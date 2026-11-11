#include "gamepad.h"

#include <climits>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <string>

#include <algorithm>
#include <vector>

#include "actions.h"
#include "animation.h"
#include "character_editor.h"
#include "color.h"
#include "combat.h"
#include "config.h"
#include "critter.h"
#include "display_monitor.h"
#include "game.h"
#include "game_config.h"
#include "game_dialog.h"
#include "game_mouse.h"
#include "input.h"
#include "interface.h"
#include "inventory.h"
#include "item.h"
#include "loadsave.h"
#include "map.h"
#include "mouse.h"
#include "object.h"
#include "party_member.h"
#include "proto.h"
#include "proto_instance.h"
#include "skill.h"
#include "skill_defs.h"
#include "svga.h"
#include "text_font.h"
#include "tile.h"
#include "window_manager.h"
#include "worldmap.h"

namespace fallout {

static const double kPi = 3.14159265358979323846;

// -----------------------------------------------------------------------------
// Impostazioni
// -----------------------------------------------------------------------------

struct MobileSettings {
    bool loaded = false;
    bool touchDirect = true; // tocco: il cursore va dove tocchi
    bool touchSnap = true; // tocco: aggancia gli oggetti vicini
    int cursorSpeed = 100; // velocità cursore del controller, in %
    int deadzone = 20; // zona morta degli stick, in %
    bool cameraFollow = true; // la visuale segue il personaggio
    bool stickMovement = true; // stick sinistro = muovi il personaggio
    bool hexMovement = true; // ...scegliendo l'esagono di arrivo (A per andarci)
    bool buttonHints = true; // barra con i tasti da premere
};

static MobileSettings gMobile;

static void hintsAfterScroll();
extern bool gHintVisible;
extern std::string gHintKey;
static bool hexModeActive();
static bool gHexShown = false; // esplorazione: esagono di arrivo visibile

static void mobileSettingsLoad()
{
    if (gMobile.loaded || !gGameConfigInitialized) {
        return;
    }

    gMobile.loaded = true;

    int value;
    if (configGetInt(&gGameConfig, "mobile", "touch_mode", &value)) gMobile.touchDirect = value != 0;
    if (configGetInt(&gGameConfig, "mobile", "touch_snap", &value)) gMobile.touchSnap = value != 0;
    if (configGetInt(&gGameConfig, "mobile", "gamepad_cursor_speed", &value)) gMobile.cursorSpeed = std::clamp(value, 25, 400);
    if (configGetInt(&gGameConfig, "mobile", "gamepad_deadzone", &value)) gMobile.deadzone = std::clamp(value, 5, 60);
    if (configGetInt(&gGameConfig, "mobile", "camera_follow", &value)) gMobile.cameraFollow = value != 0;
    if (configGetInt(&gGameConfig, "mobile", "stick_movement", &value)) gMobile.stickMovement = value != 0;
    if (configGetInt(&gGameConfig, "mobile", "hex_movement", &value)) gMobile.hexMovement = value != 0;
    if (configGetInt(&gGameConfig, "mobile", "button_hints", &value)) gMobile.buttonHints = value != 0;
}

bool touchDirectModeEnabled()
{
    mobileSettingsLoad();
    return gMobile.touchDirect;
}

bool touchSnapEnabled()
{
    mobileSettingsLoad();
    return gMobile.touchSnap;
}

// -----------------------------------------------------------------------------
// Stato del controller
// -----------------------------------------------------------------------------

enum Action {
    ACTION_NONE,
    ACTION_KEY, // tasto tenuto finché il pulsante è premuto
    ACTION_KEY_TAP, // pressione + rilascio immediati
    ACTION_MOUSE_LEFT,
    ACTION_MOUSE_RIGHT,
    ACTION_TARGET_PREV,
    ACTION_TARGET_NEXT,
    ACTION_CANCEL_MODE,
    ACTION_DIALOG_PREV,
    ACTION_DIALOG_NEXT,
    ACTION_PAD_USE, // A senza puntatore: usa l'oggetto evidenziato
    ACTION_PAD_LOOK, // X senza puntatore: esamina l'oggetto evidenziato
    ACTION_NAV_UP, // menu: salta al pulsante sopra / sotto / a sinistra / a destra
    ACTION_NAV_DOWN,
    ACTION_NAV_LEFT,
    ACTION_NAV_RIGHT,
    ACTION_WHEEL_UP, // menu: scorri la lista
    ACTION_WHEEL_DOWN,
};

struct Binding {
    Action action = ACTION_NONE;
    int scancode = 0;
};

enum Context {
    CONTEXT_MAP,
    CONTEXT_COMBAT,
    CONTEXT_DIALOG,
    CONTEXT_WINDOW,
};

static SDL_GameController* gController = nullptr;
static SDL_JoystickID gControllerId = -1;
static bool gControllerJustConnected = false;

static Sint16 gAxis[SDL_CONTROLLER_AXIS_MAX];
static Binding gActiveBinding[SDL_CONTROLLER_BUTTON_MAX];

static bool gMouseLeftHeld = false;

// Tocco di A su un oggetto dell'inventario: il trascinamento verso la sua
// destinazione naturale lo fa il controller (vedi inventoryQuickMoveTarget).
static Uint32 gLeftPressedAt = 0;
static bool gLeftMovedSincePress = false;
static int gLeftDownPolls = 0; // letture dell'input con il tasto giù
static bool gQuickDropPending = false;
static int gQuickDropX = 0;
static int gQuickDropY = 0;
static Uint32 gQuickDropUntil = 0; // tasto tenuto giù sulla destinazione fino a qui
static bool gMouseRightHeld = false;
static int gMouseRightPulse = 0;
static int gMouseLeftPulse = 0;

// Spostamento del cursore richiesto da un aggancio (dialogo, bersagli).
static bool gWarpPending = false;
static int gWarpX = 0;
static int gWarpY = 0;

// Azioni di gioco richieste dagli eventi e svolte in gamepadGameTick.
static int gPendingTargetStep = 0;
static bool gPendingCancelMode = false;

// Pulsante Select usato come modificatore.
static bool gSelectHeld = false;

static double gCursorRemainderX = 0.0;
static double gCursorRemainderY = 0.0;
static Uint32 gLastMouseTick = 0;
static Uint32 gLastWheelTick = 0;

static bool gStickWasMoving = false;
static int gStickLastTarget = -1;
static Uint32 gStickLastIssue = 0;
static double gStickLastAngle = 0.0;
static bool gStickRunning = false;

static Object* gTargetCurrent = nullptr;

// Modalità senza puntatore (controller sulla mappa).
static bool gPadMode = false; // ultimo input dal controller
static Uint32 gLastPadInput = 0;
static Object* gFocus = nullptr; // oggetto evidenziato
static bool gFocusManual = false; // scelto con LB/RB: resta finché non ti muovi
static bool gFocusOutlined = false;
static bool gWeHidCursor = false;
static bool gWeHidMapCursor = false;
static Uint32 gFocusNameDue = 0; // quando scrivere il nome dell'oggetto evidenziato // cursore "3D" della mappa (freccia + icona azione)
static bool gUseHolding = false; // A tenuto premuto
static Uint32 gUseHeldSince = 0;
static bool gMenuHold = false; // menu azioni del gioco aperto con A tenuto
static int gMenuStep = 0; // spostamenti richiesti nel menu azioni
static bool gPendingUse = false;
static bool gPendingLook = false;
static double gFacingX = 0.0; // direzione in cui "guarda" il personaggio
static double gFacingY = 1.0;
static Uint32 gLastScrollTick = 0;

// Combattimento: esagono scelto con lo stick.
static int gCombatHex = -1;
static int gCombatHexOrigin = -1;
static Uint32 gCombatHexNext = 0;
static int gCombatHexLastDir = -1;
static bool gCombatStickActive = false;

// Navigazione nei menu.
static int gNavDirX = 0; // direzione tenuta premuta (croce)
static int gNavDirY = 0;
static int gNavPendingX = 0; // salto da fare al prossimo frame
static int gNavPendingY = 0;
static Uint32 gNavNextRepeat = 0;
static int gNavWin = -1; // pulsante selezionato
static int gNavBtn = -1;
static Rect gNavRect; // dov'era il pulsante scelto (gli id vengono riusati)
static int gWheelPending = 0;
static int gLastContext = -1;
static Uint32 gNavAutoSelectAt = 0;
static int gNavStickDirX = 0;
static int gNavStickDirY = 0;
static Uint32 gNavStickNext = 0;

static Uint32 gLastGameTick = 0;

// Siamo nel ciclo della mappa locale (esplorazione o combattimento)?
// gamepadGameTick viene chiamato a ogni giro di quel ciclo: se non arriva da
// un po' vuol dire che è aperto un menu (inventario, Pip-Boy, menu principale).
static bool inGameLoop()
{
    return gLastGameTick != 0 && SDL_GetTicks() - gLastGameTick < 200;
}

static bool mapIsActive()
{
    return gDude != nullptr && gameMouseIsEnabled() && !_gdialogActive() && inGameLoop();
}

static Context currentContext()
{
    if (_gdialogActive()) {
        return CONTEXT_DIALOG;
    }

    if (mapIsActive()) {
        return isInCombat() ? CONTEXT_COMBAT : CONTEXT_MAP;
    }

    return CONTEXT_WINDOW;
}

static void controllerOpen(int deviceIndex)
{
    if (gController != nullptr) {
        return;
    }

    if (!SDL_IsGameController(deviceIndex)) {
        return;
    }

    gController = SDL_GameControllerOpen(deviceIndex);
    if (gController != nullptr) {
        gControllerId = SDL_JoystickInstanceID(SDL_GameControllerGetJoystick(gController));
        gControllerJustConnected = true;
        for (int i = 0; i < SDL_CONTROLLER_AXIS_MAX; i++) {
            gAxis[i] = 0;
        }
    }
}

static void releaseAll()
{
    for (int i = 0; i < SDL_CONTROLLER_BUTTON_MAX; i++) {
        Binding* binding = &(gActiveBinding[i]);
        if (binding->action == ACTION_KEY) {
            inputInjectKey(binding->scancode, false);
        }
        binding->action = ACTION_NONE;
    }

    for (int i = 0; i < SDL_CONTROLLER_AXIS_MAX; i++) {
        gAxis[i] = 0;
    }

    gMouseLeftHeld = false;
    gMouseRightHeld = false;
    gSelectHeld = false;
}

static void controllerClose(SDL_JoystickID id)
{
    if (gController != nullptr && id == gControllerId) {
        releaseAll();
        SDL_GameControllerClose(gController);
        gController = nullptr;
        gControllerId = -1;

        // Se c'è un altro controller collegato usa quello.
        for (int i = 0; i < SDL_NumJoysticks(); i++) {
            controllerOpen(i);
            if (gController != nullptr) {
                break;
            }
        }
    }
}

static Binding key(int scancode)
{
    Binding binding;
    binding.action = ACTION_KEY;
    binding.scancode = scancode;
    return binding;
}

static Binding keyTap(int scancode)
{
    Binding binding;
    binding.action = ACTION_KEY_TAP;
    binding.scancode = scancode;
    return binding;
}

static Binding act(Action action)
{
    Binding binding;
    binding.action = action;
    return binding;
}

static int topMenuWindow()
{
    return windowManagerGetTopVisibleWindow(gIsoWindow, gInterfaceBarWindow);
}

// Fallout 2: la scheda personaggio scorre caratteristiche e abilità con le
// frecce. Fallout 1 solo sinistra/destra (togli/aggiungi punti): su e giù
// scorrono le righe con il cursore (vedi navTick).
static const bool kEditorVerticalArrows = true;

static bool menuUsesArrowKeys()
{
    int top = topMenuWindow();
    return top != -1 && ((kEditorVerticalArrows && top == characterEditorGetWindow()) || top == loadSaveGetWindow());
}

static bool menuUsesSideArrowKeys()
{
    int top = topMenuWindow();
    return top != -1 && top == characterEditorGetWindow();
}

static bool menuIsWorldmap()
{
    int top = topMenuWindow();
    return top != -1 && top == worldmapGetWindow();
}

// Tabella dei comandi. Vedi CONTROLLI.md per lo schema completo.
static Binding bindingFor(int button, Context context)
{
    // Livello "Select tenuto premuto".
    if (gSelectHeld && (context == CONTEXT_MAP || context == CONTEXT_COMBAT)) {
        switch (button) {
        case SDL_CONTROLLER_BUTTON_A:
            return keyTap(SDL_SCANCODE_F6); // salvataggio rapido
        case SDL_CONTROLLER_BUTTON_Y:
            return keyTap(SDL_SCANCODE_F7); // caricamento rapido
        case SDL_CONTROLLER_BUTTON_DPAD_UP:
            return keyTap(SDL_SCANCODE_Z); // riposa / orologio Pip-Boy
        case SDL_CONTROLLER_BUTTON_RIGHTSHOULDER:
            return keyTap(SDL_SCANCODE_RETURN); // termina il combattimento
        }
        return Binding();
    }

    switch (context) {
    case CONTEXT_MAP:
    case CONTEXT_COMBAT:
        switch (button) {
        case SDL_CONTROLLER_BUTTON_A:
            return act(context == CONTEXT_MAP ? ACTION_PAD_USE : ACTION_MOUSE_LEFT);
        case SDL_CONTROLLER_BUTTON_B:
            return act(ACTION_CANCEL_MODE);
        case SDL_CONTROLLER_BUTTON_X:
            return act(context == CONTEXT_MAP ? ACTION_PAD_LOOK : ACTION_MOUSE_RIGHT);
        case SDL_CONTROLLER_BUTTON_Y:
            return keyTap(SDL_SCANCODE_I);
        case SDL_CONTROLLER_BUTTON_LEFTSHOULDER:
            return act(ACTION_TARGET_PREV);
        case SDL_CONTROLLER_BUTTON_RIGHTSHOULDER:
            return act(ACTION_TARGET_NEXT);
        case SDL_CONTROLLER_BUTTON_DPAD_UP:
            return keyTap(SDL_SCANCODE_P);
        case SDL_CONTROLLER_BUTTON_DPAD_DOWN:
            return keyTap(SDL_SCANCODE_C);
        case SDL_CONTROLLER_BUTTON_DPAD_LEFT:
            return keyTap(SDL_SCANCODE_S);
        case SDL_CONTROLLER_BUTTON_DPAD_RIGHT:
            return keyTap(SDL_SCANCODE_TAB);
        case SDL_CONTROLLER_BUTTON_LEFTSTICK:
            return keyTap(SDL_SCANCODE_HOME);
        case SDL_CONTROLLER_BUTTON_RIGHTSTICK:
            return keyTap(SDL_SCANCODE_N);
        case SDL_CONTROLLER_BUTTON_START:
            return keyTap(SDL_SCANCODE_ESCAPE);
        }
        break;
    case CONTEXT_DIALOG:
    case CONTEXT_WINDOW:
        // Scheda personaggio e salvataggi hanno già una selezione da
        // tastiera: la croce manda le frecce (su/giù scegli, sinistra/destra
        // togli/aggiungi punti). I pulsanti si raggiungono con lo stick.
        if (menuUsesSideArrowKeys() && !menuUsesArrowKeys()) {
            switch (button) {
            case SDL_CONTROLLER_BUTTON_DPAD_LEFT:
                return key(SDL_SCANCODE_LEFT);
            case SDL_CONTROLLER_BUTTON_DPAD_RIGHT:
                return key(SDL_SCANCODE_RIGHT);
            }
        }
        if (menuUsesArrowKeys()) {
            switch (button) {
            case SDL_CONTROLLER_BUTTON_DPAD_UP:
                return key(SDL_SCANCODE_UP);
            case SDL_CONTROLLER_BUTTON_DPAD_DOWN:
                return key(SDL_SCANCODE_DOWN);
            case SDL_CONTROLLER_BUTTON_DPAD_LEFT:
                return key(SDL_SCANCODE_LEFT);
            case SDL_CONTROLLER_BUTTON_DPAD_RIGHT:
                return key(SDL_SCANCODE_RIGHT);
            }
        }
        // Menu, finestre e dialoghi: la croce (e lo stick sinistro) saltano
        // da un pulsante all'altro, A lo preme.
        switch (button) {
        case SDL_CONTROLLER_BUTTON_A:
            return act(ACTION_MOUSE_LEFT);
        case SDL_CONTROLLER_BUTTON_X:
            return act(ACTION_MOUSE_RIGHT);
        case SDL_CONTROLLER_BUTTON_B:
        case SDL_CONTROLLER_BUTTON_START:
            return keyTap(SDL_SCANCODE_ESCAPE);
        case SDL_CONTROLLER_BUTTON_Y:
            return keyTap(SDL_SCANCODE_RETURN);
        case SDL_CONTROLLER_BUTTON_DPAD_UP:
            return act(ACTION_NAV_UP);
        case SDL_CONTROLLER_BUTTON_DPAD_DOWN:
            return act(ACTION_NAV_DOWN);
        case SDL_CONTROLLER_BUTTON_DPAD_LEFT:
            return act(ACTION_NAV_LEFT);
        case SDL_CONTROLLER_BUTTON_DPAD_RIGHT:
            return act(ACTION_NAV_RIGHT);
        case SDL_CONTROLLER_BUTTON_LEFTSHOULDER:
            return act(ACTION_WHEEL_UP);
        case SDL_CONTROLLER_BUTTON_RIGHTSHOULDER:
            return act(ACTION_WHEEL_DOWN);
        }
        break;
    }

    return Binding();
}

// I grilletti sono assi: li trattiamo come pulsanti virtuali.
#define VIRTUAL_BUTTON_LEFT_TRIGGER (SDL_CONTROLLER_BUTTON_MAX - 2)
#define VIRTUAL_BUTTON_RIGHT_TRIGGER (SDL_CONTROLLER_BUTTON_MAX - 1)

static Binding triggerBindingFor(bool right, Context context)
{
    if (context == CONTEXT_MAP || context == CONTEXT_COMBAT) {
        if (!right) {
            return keyTap(SDL_SCANCODE_B); // cambia mano
        }
        // Fuori dal combattimento lo inizia, durante il combattimento
        // termina il turno.
        return keyTap(context == CONTEXT_COMBAT ? SDL_SCANCODE_SPACE : SDL_SCANCODE_A);
    }

    if (context == CONTEXT_WINDOW || context == CONTEXT_DIALOG) {
        return right ? key(SDL_SCANCODE_PAGEDOWN) : key(SDL_SCANCODE_PAGEUP);
    }

    return Binding();
}

static void dialogStep(int step);
static bool mapIsActive();

static bool gPendingReload = false;
static bool combatWeaponNeedsReload();

static void bindingPress(int slot, Binding binding)
{
    gActiveBinding[slot] = binding;

    switch (binding.action) {
    case ACTION_KEY:
        inputInjectKey(binding.scancode, true);
        break;
    case ACTION_KEY_TAP:
        inputInjectKey(binding.scancode, true);
        inputInjectKey(binding.scancode, false);
        break;
    case ACTION_MOUSE_LEFT:
        if (gPadMode && currentContext() == CONTEXT_COMBAT) {
            // Con il controller in combattimento A esegue subito: il
            // bersaglio (LB/RB) o l'esagono (stick) li hai già scelti.
            if (gameMouseGetMode() == GAME_MOUSE_MODE_MOVE) {
                gCombatHex = -1;
            } else if (combatWeaponNeedsReload()) {
                // Arma scarica e munizioni in tasca: A ricarica.
                gPendingReload = true;
                gActiveBinding[slot].action = ACTION_NONE;
                break;
            }
        } else if (mapIsActive()) {
            int mouseX;
            int mouseY;
            mouseGetPosition(&mouseX, &mouseY);
            if (gWarpPending) {
                mouseX = gWarpX;
                mouseY = gWarpY;
            }
            if (!gamepadSmartClick(mouseX, mouseY)) {
                gActiveBinding[slot].action = ACTION_NONE;
                break;
            }
        }
        gMouseLeftHeld = true;
        gMouseLeftPulse = 2;
        gLeftPressedAt = SDL_GetTicks();
        gLeftMovedSincePress = false;
        gLeftDownPolls = 0;
        break;
    case ACTION_MOUSE_RIGHT:
        gMouseRightHeld = true;
        gMouseRightPulse = 2;
        break;
    case ACTION_TARGET_PREV:
        gPendingTargetStep = -1;
        break;
    case ACTION_TARGET_NEXT:
        gPendingTargetStep = 1;
        break;
    case ACTION_CANCEL_MODE:
        gPendingCancelMode = true;
        break;
    case ACTION_PAD_USE:
        gUseHolding = true;
        gUseHeldSince = SDL_GetTicks();
        break;
    case ACTION_PAD_LOOK:
        gPendingLook = true;
        break;
    case ACTION_NAV_UP:
    case ACTION_NAV_DOWN:
    case ACTION_NAV_LEFT:
    case ACTION_NAV_RIGHT:
        gNavDirX = binding.action == ACTION_NAV_LEFT ? -1 : (binding.action == ACTION_NAV_RIGHT ? 1 : 0);
        gNavDirY = binding.action == ACTION_NAV_UP ? -1 : (binding.action == ACTION_NAV_DOWN ? 1 : 0);
        gNavPendingX = gNavDirX;
        gNavPendingY = gNavDirY;
        gNavNextRepeat = SDL_GetTicks() + 380;
        break;
    case ACTION_WHEEL_UP:
        gWheelPending += 1;
        inputInjectKey(SDL_SCANCODE_PAGEUP, true);
        inputInjectKey(SDL_SCANCODE_PAGEUP, false);
        break;
    case ACTION_WHEEL_DOWN:
        gWheelPending -= 1;
        inputInjectKey(SDL_SCANCODE_PAGEDOWN, true);
        inputInjectKey(SDL_SCANCODE_PAGEDOWN, false);
        break;
    case ACTION_DIALOG_PREV:
        dialogStep(-1);
        break;
    case ACTION_DIALOG_NEXT:
        dialogStep(1);
        break;
    default:
        break;
    }
}

static void bindingRelease(int slot)
{
    Binding* binding = &(gActiveBinding[slot]);
    switch (binding->action) {
    case ACTION_KEY:
        inputInjectKey(binding->scancode, false);
        break;
    case ACTION_MOUSE_LEFT:
        gMouseLeftHeld = false;
#ifdef FALLOUT_AUTOTEST
        {
            int tx = -1, ty = -1, mx, my;
            mouseGetPosition(&mx, &my);
            bool ok = inventoryQuickMoveTarget(topMenuWindow(), &tx, &ty);
            printf("[pad] rilascio A: mouse %d,%d tipo %d top %d moved %d dt %u ctx %d -> %d (%d,%d)\n", mx, my, inventoryQuickMoveWindowType(), topMenuWindow(), gLeftMovedSincePress, SDL_GetTicks() - gLeftPressedAt, currentContext(), ok, tx, ty);
        }
#endif
        if (gPadMode && !gLeftMovedSincePress && SDL_GetTicks() - gLeftPressedAt < 400
            && (currentContext() == CONTEXT_WINDOW || currentContext() == CONTEXT_DIALOG)
            && inventoryQuickMoveTarget(topMenuWindow(), &gQuickDropX, &gQuickDropY)) {
            gQuickDropPending = true;
        }
        break;
    case ACTION_MOUSE_RIGHT:
        gMouseRightHeld = false;
        break;
    case ACTION_NAV_UP:
    case ACTION_NAV_DOWN:
    case ACTION_NAV_LEFT:
    case ACTION_NAV_RIGHT:
        gNavDirX = 0;
        gNavDirY = 0;
        break;
    case ACTION_PAD_USE:
        if (gMenuHold) {
            // Rilascio = conferma la voce scelta nel menu azioni.
            gMouseLeftHeld = false;
            gMenuHold = false;
        } else if (gUseHolding) {
            gPendingUse = true;
        }
        gUseHolding = false;
        break;
    default:
        break;
    }
    binding->action = ACTION_NONE;
}

static bool gSelectUsedAsModifier = false;
static bool gTriggerDown[2] = { false, false };

// RT in combattimento: tocco = fine turno, tenuto premuto = fine combattimento.
static Uint32 gEndTurnHeldSince = 0;
static bool gEndCombatSent = false;
static const Uint32 kEndCombatHoldMs = 600;

void gamepadHandleEvent(SDL_Event* event)
{
    switch (event->type) {
    case SDL_CONTROLLERDEVICEADDED:
        controllerOpen(event->cdevice.which);
        break;
    case SDL_CONTROLLERDEVICEREMOVED:
        controllerClose(event->cdevice.which);
        break;
    case SDL_CONTROLLERBUTTONDOWN:
        gPadMode = true;
        gLastPadInput = SDL_GetTicks();
        if (gMenuHold && (event->cbutton.button == SDL_CONTROLLER_BUTTON_DPAD_UP || event->cbutton.button == SDL_CONTROLLER_BUTTON_DPAD_DOWN)) {
            gMenuStep += event->cbutton.button == SDL_CONTROLLER_BUTTON_DPAD_UP ? -1 : 1;
            break;
        }
#ifdef FALLOUT_AUTOTEST
        printf("[pad] pulsante %d giù, contesto %d\n", event->cbutton.button, currentContext());
#endif
        if (event->cbutton.which != gControllerId) {
            break;
        }
        if (event->cbutton.button == SDL_CONTROLLER_BUTTON_BACK) {
            gSelectHeld = true;
            gSelectUsedAsModifier = false;
            break;
        }
        if (event->cbutton.button < VIRTUAL_BUTTON_LEFT_TRIGGER) {
            Binding binding = bindingFor(event->cbutton.button, currentContext());
            if (gSelectHeld) {
                gSelectUsedAsModifier = true;
            }
            bindingPress(event->cbutton.button, binding);
        }
        break;
    case SDL_CONTROLLERBUTTONUP:
        if (event->cbutton.which != gControllerId) {
            break;
        }
        if (event->cbutton.button == SDL_CONTROLLER_BUTTON_BACK) {
            gSelectHeld = false;
            break;
        }
        if (event->cbutton.button < VIRTUAL_BUTTON_LEFT_TRIGGER) {
            bindingRelease(event->cbutton.button);
        }
        break;
    case SDL_CONTROLLERAXISMOTION:
#ifdef FALLOUT_AUTOTEST
        printf("[pad] asse %d = %d (id %d, atteso %d)\n", event->caxis.axis, event->caxis.value, event->caxis.which, gControllerId);
#endif
        if (event->caxis.which != gControllerId) {
            break;
        }
        gAxis[event->caxis.axis] = event->caxis.value;
        if (abs(event->caxis.value) > 12000) {
            gPadMode = true;
            gLastPadInput = SDL_GetTicks();
        }

        if (event->caxis.axis == SDL_CONTROLLER_AXIS_TRIGGERLEFT || event->caxis.axis == SDL_CONTROLLER_AXIS_TRIGGERRIGHT) {
            bool right = event->caxis.axis == SDL_CONTROLLER_AXIS_TRIGGERRIGHT;
            int slot = right ? VIRTUAL_BUTTON_RIGHT_TRIGGER : VIRTUAL_BUTTON_LEFT_TRIGGER;
            // Isteresi: premuto oltre il 50%, rilasciato sotto il 25%.
            if (!gTriggerDown[right] && event->caxis.value > 16000) {
                gTriggerDown[right] = true;
                Binding binding;
                if (gSelectHeld && right && (currentContext() == CONTEXT_COMBAT)) {
                    binding = keyTap(SDL_SCANCODE_RETURN); // termina combattimento
                    gSelectUsedAsModifier = true;
                } else if (right && currentContext() == CONTEXT_COMBAT) {
                    // Decide al rilascio (o dopo un attimo se resta premuto).
                    gEndTurnHeldSince = SDL_GetTicks();
                    gEndCombatSent = false;
                } else {
                    binding = triggerBindingFor(right, currentContext());
                }
                bindingPress(slot, binding);
            } else if (gTriggerDown[right] && event->caxis.value < 8000) {
                gTriggerDown[right] = false;
                if (right && gEndTurnHeldSince != 0) {
                    if (!gEndCombatSent && currentContext() == CONTEXT_COMBAT) {
                        inputInjectKey(SDL_SCANCODE_SPACE, true);
                        inputInjectKey(SDL_SCANCODE_SPACE, false);
                    }
                    gEndTurnHeldSince = 0;
                    gEndCombatSent = false;
                }
                bindingRelease(slot);
            }
        }
        break;
    }
}

// -----------------------------------------------------------------------------
// Cursore
// -----------------------------------------------------------------------------

static double axisValue(int axis)
{
    double value = gAxis[axis] / 32767.0;
    return std::clamp(value, -1.0, 1.0);
}

// Stick con zona morta radiale e curva di risposta. Restituisce l'intensità
// (0..1) e la direzione normalizzata.
static double stickRead(int axisX, int axisY, double* nx, double* ny)
{
    double x = axisValue(axisX);
    double y = axisValue(axisY);
    double magnitude = sqrt(x * x + y * y);
    double deadzone = gMobile.deadzone / 100.0;

    if (magnitude < deadzone) {
        *nx = 0.0;
        *ny = 0.0;
        return 0.0;
    }

    *nx = x / magnitude;
    *ny = y / magnitude;
    return std::min(1.0, (magnitude - deadzone) / (1.0 - deadzone));
}

static void dialogStep(int step)
{
    int xs[DIALOG_TARGETS_MAX];
    int ys[DIALOG_TARGETS_MAX];
    int count = gameDialogGetOptionTargets(xs, ys, DIALOG_TARGETS_MAX);
    if (count <= 0) {
        // Nessuna risposta visibile: scorri il testo.
        inputInjectKey(step < 0 ? SDL_SCANCODE_UP : SDL_SCANCODE_DOWN, true);
        inputInjectKey(step < 0 ? SDL_SCANCODE_UP : SDL_SCANCODE_DOWN, false);
        return;
    }

    int mouseX;
    int mouseY;
    mouseGetPosition(&mouseX, &mouseY);
    if (gWarpPending) {
        mouseY = gWarpY;
    }

    // Risposta su cui si trova ora il cursore (la più vicina in verticale).
    int current = -1;
    int best = INT_MAX;
    for (int i = 0; i < count; i++) {
        int distance = abs(ys[i] - mouseY);
        if (distance < best && mouseX >= xs[i] - 200 && mouseX <= xs[i] + 400) {
            best = distance;
            current = i;
        }
    }

    int next;
    if (current == -1 || best > 30) {
        next = step > 0 ? 0 : count - 1;
    } else {
        next = (current + step + count) % count;
    }

    gWarpPending = true;
    gWarpX = xs[next];
    gWarpY = ys[next];
}

// -----------------------------------------------------------------------------
// Menu: navigazione a salti tra i pulsanti
// -----------------------------------------------------------------------------

static int navFind(const std::vector<NavTarget>& targets, int win, int btn)
{
    for (size_t i = 0; i < targets.size(); i++) {
        if (targets[i].win == win && targets[i].btn == btn) {
            return (int)i;
        }
    }
    return -1;
}

static void navCenter(const NavTarget& target, int* x, int* y)
{
    *x = (target.rect.left + target.rect.right) / 2;
    *y = (target.rect.top + target.rect.bottom) / 2;
}

static int navNearest(const std::vector<NavTarget>& targets, int x, int y)
{
    int best = -1;
    long long bestDistance = LLONG_MAX;
    for (size_t i = 0; i < targets.size(); i++) {
        const Rect& r = targets[i].rect;
        // Distanza dal rettangolo (0 se il punto è dentro).
        int ddx = x < r.left ? r.left - x : (x > r.right ? x - r.right : 0);
        int ddy = y < r.top ? r.top - y : (y > r.bottom ? y - r.bottom : 0);
        long long distance = (long long)ddx * ddx + (long long)ddy * ddy;
        if (distance < bestDistance) {
            bestDistance = distance;
            best = (int)i;
        }
    }
    return best;
}

// Pulsante iniziale: quello sotto il cursore se c'è, altrimenti il primo in
// alto a sinistra (la lettura naturale di un menu).
static int navDefault(const std::vector<NavTarget>& targets, int mouseX, int mouseY)
{
    // Nei dialoghi si parte dalla prima risposta.
    if (_gdialogActive()) {
        int xs[DIALOG_TARGETS_MAX];
        int ys[DIALOG_TARGETS_MAX];
        if (gameDialogGetOptionTargets(xs, ys, DIALOG_TARGETS_MAX) > 0) {
            for (size_t i = 0; i < targets.size(); i++) {
                const Rect& r = targets[i].rect;
                if (ys[0] >= r.top && ys[0] <= r.bottom && xs[0] >= r.left - 60 && xs[0] <= r.right) {
                    return (int)i;
                }
            }
        }
    }

    // Inventario, bottino, baratto: si parte dalla prima casella della tua
    // lista.
    int homeX;
    int homeY;
    if (inventoryQuantityWindow() == -1 && inventoryQuickMoveHome(&homeX, &homeY)) {
        for (size_t i = 0; i < targets.size(); i++) {
            const Rect& r = targets[i].rect;
            if (homeX >= r.left && homeX <= r.right && homeY >= r.top && homeY <= r.bottom) {
                return (int)i;
            }
        }
    }

    // "Sposta oggetti": si parte da FATTO (in basso a sinistra), così dopo il
    // tocco sull'oggetto basta un altro A per confermare.
    int quantityWindow = inventoryQuantityWindow();
    if (quantityWindow != -1) {
        int found = -1;
        for (size_t i = 0; i < targets.size(); i++) {
            if (targets[i].win != quantityWindow) {
                continue;
            }
            if (found == -1 || targets[i].rect.top > targets[found].rect.top + 4
                || (abs(targets[i].rect.top - targets[found].rect.top) <= 4 && targets[i].rect.left < targets[found].rect.left)) {
                found = (int)i;
            }
        }
        if (found != -1) {
            return found;
        }
    }

    for (size_t i = 0; i < targets.size(); i++) {
        const Rect& r = targets[i].rect;
        if (mouseX >= r.left && mouseX <= r.right && mouseY >= r.top && mouseY <= r.bottom) {
            return (int)i;
        }
    }

    int best = -1;
    long long bestScore = LLONG_MAX;
    for (size_t i = 0; i < targets.size(); i++) {
        const Rect& r = targets[i].rect;
        long long score = (long long)r.top * 4 + r.left; // prima le righe in alto
        if (score < bestScore) {
            bestScore = score;
            best = (int)i;
        }
    }
    return best;
}

// Il pulsante più vicino nella direzione indicata: conta soprattutto lo
// spostamento lungo la direzione, poco quello di lato.
static int navStep(const std::vector<NavTarget>& targets, int current, int dirX, int dirY)
{
    int cx;
    int cy;
    navCenter(targets[current], &cx, &cy);
    const Rect& cr = targets[current].rect;

    // Prima passata: solo i pulsanti il cui centro sta davvero oltre il bordo
    // di quello attuale (da una riga larga non si "salta" a un'area sopra o
    // sotto che è solo un po' spostata). Seconda passata: la regola larga.
    for (int pass = 0; pass < 2; pass++) {
        int best = -1;
        double bestScore = 1e18;
        for (size_t i = 0; i < targets.size(); i++) {
            if ((int)i == current) {
                continue;
            }
            const Rect& r = targets[i].rect;
            int x;
            int y;
            navCenter(targets[i], &x, &y);

            double along;
            double side;
            if (dirX != 0) {
                if (pass == 0) {
                    if (dirX > 0 && x <= cr.right) continue;
                    if (dirX < 0 && x >= cr.left) continue;
                } else {
                    if (dirX > 0 && r.left <= cr.left + 2) continue;
                    if (dirX < 0 && r.right >= cr.right - 2) continue;
                }
                along = fabs((double)(x - cx));
                // Sovrapposizione verticale: stessa riga = nessuna penalità.
                bool overlap = r.top <= cr.bottom && r.bottom >= cr.top;
                side = overlap ? 0.0 : fabs((double)(y - cy));
            } else {
                if (pass == 0) {
                    if (dirY > 0 && y <= cr.bottom) continue;
                    if (dirY < 0 && y >= cr.top) continue;
                } else {
                    if (dirY > 0 && r.top <= cr.top + 2) continue;
                    if (dirY < 0 && r.bottom >= cr.bottom - 2) continue;
                }
                along = fabs((double)(y - cy));
                bool overlap = r.left <= cr.right && r.right >= cr.left;
                side = overlap ? 0.0 : fabs((double)(x - cx));
            }
            double score = along + side * 3.0;
            if (score < bestScore) {
                bestScore = score;
                best = (int)i;
            }
        }
        if (best != -1) {
            return best;
        }
    }
    return -1;
}

// Ogni frame nei menu: seleziona un pulsante e sposta lì il cursore.
static void navTick(Context context, Uint32 now, int* dx, int* dy)
{
    bool inMenu = context == CONTEXT_WINDOW || context == CONTEXT_DIALOG;
    if (context != gLastContext) {
        gLastContext = context;
        gNavWin = -1;
        gNavBtn = -1;
        gNavAutoSelectAt = inMenu ? now + 250 : 0;
    }
    if (!inMenu || !gPadMode) {
        return;
    }

    // Croce tenuta premuta: ripete.
    if ((gNavDirX != 0 || gNavDirY != 0) && now >= gNavNextRepeat) {
        gNavPendingX = gNavDirX;
        gNavPendingY = gNavDirY;
        gNavNextRepeat = now + 110;
    }

    // Stick sinistro come la croce (nella mappa del mondo è un cursore
    // libero, per viaggiare verso qualsiasi punto).
    double nx;
    double ny;
    bool worldmap = menuIsWorldmap();
    if (worldmap && stickRead(SDL_CONTROLLER_AXIS_LEFTX, SDL_CONTROLLER_AXIS_LEFTY, &nx, &ny) > 0.0) {
        gNavWin = -1;
        gNavBtn = -1;
    } else if (!worldmap && stickRead(SDL_CONTROLLER_AXIS_LEFTX, SDL_CONTROLLER_AXIS_LEFTY, &nx, &ny) > 0.55) {
        int sx = fabs(nx) >= fabs(ny) ? (nx > 0 ? 1 : -1) : 0;
        int sy = fabs(nx) >= fabs(ny) ? 0 : (ny > 0 ? 1 : -1);
        if (sx != gNavStickDirX || sy != gNavStickDirY) {
            gNavPendingX = sx;
            gNavPendingY = sy;
            gNavStickNext = now + 350;
        } else if (now >= gNavStickNext) {
            gNavPendingX = sx;
            gNavPendingY = sy;
            gNavStickNext = now + 130;
        }
        gNavStickDirX = sx;
        gNavStickDirY = sy;
    } else {
        gNavStickDirX = 0;
        gNavStickDirY = 0;
    }

    bool wantJump = gNavPendingX != 0 || gNavPendingY != 0;
    if (wantJump) {
        gLeftMovedSincePress = true;
    }
    bool autoSelect = gNavAutoSelectAt != 0 && now >= gNavAutoSelectAt;
    // Controllo periodico: il cursore resta agganciato al pulsante scelto
    // (il gioco a volte lo sposta quando apre una finestra), e se il pulsante
    // sparisce se ne sceglie un altro.
    static Uint32 nextCheck = 0;
    bool quickDrop = gQuickDropPending || gQuickDropUntil != 0;
    bool check = gNavWin != -1 && now >= nextCheck && !gMouseLeftHeld && !quickDrop;
    if (quickDrop) {
        gNavPendingX = 0;
        gNavPendingY = 0;
        return;
    }
    if (!wantJump && !autoSelect && !check) {
        return;
    }
    nextCheck = now + 150;

    std::vector<NavTarget> targets(256);
    int count = (gNavFullWindowAllowed = gameDialogOptionsWindow(), windowManagerGetNavTargets)(targets.data(), (int)targets.size(), gIsoWindow, gInterfaceBarWindow);
    targets.resize(count);
    if (count == 0) {
        gNavPendingX = 0;
        gNavPendingY = 0;
        return;
    }

    int mouseX;
    int mouseY;
    mouseGetPosition(&mouseX, &mouseY);

    int current = navFind(targets, gNavWin, gNavBtn);
    if (current != -1) {
        // Finestre e pulsanti chiusi lasciano liberi i loro id: se il
        // pulsante "ritrovato" sta altrove è un altro pulsante.
        const Rect& r = targets[current].rect;
        if (r.left != gNavRect.left || r.top != gNavRect.top || r.right != gNavRect.right || r.bottom != gNavRect.bottom) {
            current = -1;
        }
    }
    int next = -1;

    // Aree alte (liste di righe, come le abilità o le note del Pip-Boy): su e
    // giù scorrono le righe dentro l'area, si esce solo dai bordi.
    if (wantJump && current != -1 && gNavPendingY != 0) {
        const Rect& r = targets[current].rect;
        int rowStep = 11 * screenGetHeight() / 480;
        if (screenGetHeight() > 480) {
            rowStep = 11; // l'interfaccia resta a 480 righe anche su schermi più alti
        }
        if (r.bottom - r.top >= 60) {
            int y = mouseY + gNavPendingY * rowStep;
            if (y >= r.top + 3 && y <= r.bottom - 3) {
                *dy += y - mouseY;
                gNavPendingX = 0;
                gNavPendingY = 0;
                return;
            }
        }
    }

    if (wantJump) {
        if (current == -1) {
            next = navDefault(targets, mouseX, mouseY);
        } else {
            next = navStep(targets, current, gNavPendingX, gNavPendingY);
        }
    } else if (current == -1) {
        // Appena aperta una finestra, o il pulsante scelto non c'è più.
        next = navDefault(targets, mouseX, mouseY);
    } else {
        const Rect& r = targets[current].rect;
        if (mouseX < r.left || mouseX > r.right || mouseY < r.top || mouseY > r.bottom) {
            next = current;
        }
    }
    int lastJumpY = gNavPendingY;
#ifdef FALLOUT_AUTOTEST
    if (wantJump) {
        printf("[nav] salto (%d,%d) da %d a %d su %d pulsanti\n", gNavPendingX, gNavPendingY, current, next, count);
    }
#endif
    gNavPendingX = 0;
    gNavPendingY = 0;
    gNavAutoSelectAt = 0;

    if (next != -1) {
        bool enteringVertically = next != current && current != -1 && lastJumpY != 0;
        gNavWin = targets[next].win;
        gNavBtn = targets[next].btn;
        gNavRect = targets[next].rect;
        int x;
        int y;
        navCenter(targets[next], &x, &y);
        const Rect& nr = targets[next].rect;
        if (enteringVertically && nr.bottom - nr.top >= 60) {
            // Si entra in una lista dall'alto o dal basso: prima/ultima riga.
            y = lastJumpY > 0 ? nr.top + 6 : nr.bottom - 6;
        }
        *dx += x - mouseX;
        *dy += y - mouseY;
        gCursorRemainderX = 0.0;
        gCursorRemainderY = 0.0;
    }
}

#ifdef FALLOUT_AUTOTEST
static Object* activeHandItem();

// Banco di prova: svuota l'arma in mano (per provare la ricarica).
void gamepadDebugEmptyWeapon()
{
    Object* weapon = activeHandItem();
    if (weapon != nullptr) {
        ammoSetQuantity(weapon, 0);
        printf("[pad] arma svuotata\n");
    }
}

void gamepadDebugState()
{
    int mx, my;
    mouseGetPosition(&mx, &my);
    printf("[pad] stato: pad %d ctx %d modo %d mouse %d,%d hex %d target %p focus %p menuHold %d uiOff %d hint %d '%s'\n",
        gPadMode, currentContext(), gameMouseGetMode(), mx, my, gCombatHex, (void*)gTargetCurrent, (void*)gFocus,
        gMenuHold, gameUiIsDisabled(), gHintVisible, gHintKey.c_str());
}

// Banco di prova: porta l'esagono sull'uscita dalla mappa più vicina.
void gamepadDebugGotoExit()
{
    int best = -1;
    int bestDistance = INT_MAX;
    for (Object* object = objectFindFirstAtElevation(gElevation); object != nullptr; object = objectFindNextAtElevation()) {
        if (object->pid >= 0x5000010 && object->pid <= 0x5000017) {
            int distance = tileDistanceBetween(gDude->tile, object->tile);
            if (distance < bestDistance && _make_path(gDude, gDude->tile, object->tile, nullptr, 0) > 0) {
                bestDistance = distance;
                best = object->tile;
            }
        }
    }
    printf("[pad] uscita piu' vicina: casella %d a %d passi\n", best, bestDistance);
    if (best != -1) {
        gCombatHex = best;
        gCombatHexOrigin = gDude->tile;
        _tile_scroll_to(best, 2);
    }
}

void gamepadDebugDumpNav(const char* name)
{
    std::vector<NavTarget> targets(256);
    int count = (gNavFullWindowAllowed = gameDialogOptionsWindow(), windowManagerGetNavTargets)(targets.data(), (int)targets.size(), gIsoWindow, gInterfaceBarWindow);
    const char* dir = getenv("FALLOUT_SHOTS");
    std::string path = std::string(dir != nullptr ? dir : ".") + "/" + name + ".nav";
    FILE* stream = fopen(path.c_str(), "wt");
    for (int i = 0; i < count; i++) {
        fprintf(stream, "%d %d %d %d %d %d %d\n", targets[i].rect.left, targets[i].rect.top, targets[i].rect.right, targets[i].rect.bottom, targets[i].win, targets[i].btn,
            targets[i].win == gNavWin && targets[i].btn == gNavBtn);
    }
    fclose(stream);
    printf("[pad] %d pulsanti, contesto %d\n", count, currentContext());
}
#endif

void gamepadGetMouseInput(int* dx, int* dy, int* buttons, int* wheelX, int* wheelY)
{
    *dx = 0;
    *dy = 0;
    *buttons = 0;
    *wheelX = 0;
    *wheelY = 0;

    mobileSettingsLoad();

    Uint32 now = SDL_GetTicks();
    double elapsed = gLastMouseTick == 0 ? 0.016 : (now - gLastMouseTick) / 1000.0;
    elapsed = std::clamp(elapsed, 0.0, 0.05);
    gLastMouseTick = now;

    if (gWarpPending) {
        int mouseX;
        int mouseY;
        mouseGetPosition(&mouseX, &mouseY);
        *dx += gWarpX - mouseX;
        *dy += gWarpY - mouseY;
        gWarpPending = false;
        gCursorRemainderX = 0.0;
        gCursorRemainderY = 0.0;
    }

    if (gController == nullptr) {
        return;
    }

    Context context = currentContext();
    bool pointerless = context == CONTEXT_MAP && gPadMode;

    // Prima volta che apri inventario o bottino col controller: una riga
    // nella console (resta visibile sotto la finestra) spiega i tasti.
    static int lastInventoryType = -1;
    static bool tipShown[8] = {};
    int inventoryType = inventoryQuickMoveWindowType();
    if (inventoryType != lastInventoryType) {
        lastInventoryType = inventoryType;
        // Finestra inventario appena aperta (o chiusa): la selezione riparte
        // dal suo punto naturale.
        gNavWin = -1;
        gNavBtn = -1;
        gNavAutoSelectAt = now + 120;
        if (gPadMode && inventoryType >= 0 && inventoryType < 8 && !tipShown[inventoryType] && !_gdialogActive()) {
            const char* tip = nullptr;
            if (inventoryType == 0) {
                tip = "A: impugna o indossa (o rimetti via). X: azioni sull'oggetto.";
            } else if (inventoryType == 2) {
                tip = "A: prendi o lascia l'oggetto. B: chiudi.";
            }
            if (tip != nullptr) {
                tipShown[inventoryType] = true;
                char buffer[128];
                snprintf(buffer, sizeof(buffer), "%s", tip);
                displayMonitorAddMessage(buffer);
            }
        }
    }

    navTick(context, now, dx, dy);

    // Senza puntatore il cursore resta nascosto sulla mappa; ricompare nei
    // menu, in combattimento e quando si apre il menu azioni.
    bool wantHidden = pointerless && !gMenuHold;
    if (wantHidden != gWeHidCursor) {
        mouseSetCursorInvisible(wantHidden);
        gWeHidCursor = wantHidden;
    }
    // Nasconde subito anche il cursore "3D" della mappa: altrimenti il gioco
    // farebbe in tempo a scrivere il nome di quello che c'era sotto.
    if (wantHidden && gameMouseObjectsIsVisible() && !(hexModeActive() && gHexShown)) {
        gameMouseObjectsHide();
        gWeHidMapCursor = true;
    }

    // A tenuto premuto su un oggetto: apre il menu azioni del gioco.
    if (gUseHolding && !gMenuHold && pointerless && gFocus != nullptr && now - gUseHeldSince >= 350) {
        gMenuHold = true;
        gMenuStep = 0;
        if (gWeHidMapCursor) {
            gameMouseObjectsShow();
            gWeHidMapCursor = false;
        }
        mouseSetCursorInvisible(false);
        gWeHidCursor = false;
        gMouseLeftHeld = true;
    }

    if (gMenuHold) {
        // Nel menu azioni: croce o stick su/giù scorrono le voci (il gioco
        // cambia voce quando il cursore si sposta di più di 10 punti).
        static Uint32 lastStickStep = 0;
        double sx;
        double sy;
        if (stickRead(SDL_CONTROLLER_AXIS_LEFTX, SDL_CONTROLLER_AXIS_LEFTY, &sx, &sy) > 0.5 && fabs(sy) > 0.7 && now - lastStickStep > 220) {
            gMenuStep += sy > 0 ? 1 : -1;
            lastStickStep = now;
        }
        if (gMenuStep != 0) {
            *dy += gMenuStep > 0 ? 14 : -14;
            gMenuStep += gMenuStep > 0 ? -1 : 1;
        }
        *buttons |= MOUSE_STATE_LEFT_BUTTON_DOWN;
        return;
    }

    if (pointerless) {
        // Niente cursore da muovere: gli stick muovono personaggio e visuale.
        if (gMouseLeftHeld || gMouseLeftPulse > 0) {
            *buttons |= MOUSE_STATE_LEFT_BUTTON_DOWN;
        }
        if (gMouseLeftPulse > 0) gMouseLeftPulse--;
        return;
    }

    // Stick che muove il cursore: sulla mappa fuori dal combattimento lo
    // stick sinistro muove il personaggio, quindi il cursore è sul destro.
    bool leftMovesDude = context == CONTEXT_MAP && gMobile.stickMovement;

    double cx = 0.0;
    double cy = 0.0;
    double cursorMagnitude = 0.0;

    if (gWheelPending != 0) {
        *wheelY = gWheelPending > 0 ? 1 : -1;
        gWheelPending += gWheelPending > 0 ? -1 : 1;
    }

    // Stick sinistro: personaggio (mappa), esagoni (combattimento), salti tra
    // i pulsanti (menu). Muove il cursore solo se il movimento con lo stick è
    // disattivato nelle impostazioni.
    double nx;
    double ny;
    double left = stickRead(SDL_CONTROLLER_AXIS_LEFTX, SDL_CONTROLLER_AXIS_LEFTY, &nx, &ny);
    bool worldmap = context == CONTEXT_WINDOW && menuIsWorldmap();
    bool leftIsCursor = (context == CONTEXT_MAP && !gMobile.stickMovement) || worldmap;
    (void)leftMovesDude;
    if (leftIsCursor && left > 0.0) {
        cx = nx;
        cy = ny;
        cursorMagnitude = left;
    }

    double rx;
    double ry;
    double right = stickRead(SDL_CONTROLLER_AXIS_RIGHTX, SDL_CONTROLLER_AXIS_RIGHTY, &rx, &ry);
    if (right > 0.0) {
        if (context == CONTEXT_COMBAT && gPadMode) {
            // In combattimento lo stick destro sposta la visuale.
        } else if (right > cursorMagnitude) {
            // Nei menu lo stick destro è un cursore libero di riserva, per i
            // punti che non sono pulsanti (es. la mappa del mondo).
            if (context == CONTEXT_WINDOW || context == CONTEXT_DIALOG) {
                gNavWin = -1;
                gNavBtn = -1;
            }
            cx = rx;
            cy = ry;
            cursorMagnitude = right;
        }
    }

    if (cursorMagnitude > 0.0) {
        // Curva quadratica: preciso con poca spinta, veloce a fondo corsa.
        // La velocità è riferita a uno schermo alto 480 punti.
        double scale = screenGetHeight() / 480.0;
        double speed = 900.0 * scale * (gMobile.cursorSpeed / 100.0) * cursorMagnitude * cursorMagnitude;
        speed = std::max(speed, 40.0 * scale);
        gCursorRemainderX += cx * speed * elapsed;
        gCursorRemainderY += cy * speed * elapsed;
        int moveX = (int)gCursorRemainderX;
        int moveY = (int)gCursorRemainderY;
        gCursorRemainderX -= moveX;
        gCursorRemainderY -= moveY;
        *dx += moveX;
        *dy += moveY;
    }

    // Tocco di A nell'inventario: il tasto resta giù qualche lettura
    // sull'oggetto (il gioco lo "prende"), poi il cursore salta a destinazione
    // e lì il tasto viene rilasciato.
    // (A tempo, non a letture: il gioco legge l'input più volte per frame.)
    if (gQuickDropUntil != 0 && now >= gQuickDropUntil) {
        gQuickDropUntil = 0;
    }
    if (gQuickDropPending && gLeftDownPolls >= 3 && now - gLeftPressedAt >= 130) {
        gQuickDropPending = false;
        gQuickDropUntil = now + 130;
#ifdef FALLOUT_AUTOTEST
        printf("[pad] trascinamento automatico verso %d,%d\n", gQuickDropX, gQuickDropY);
#endif
        int mouseX;
        int mouseY;
        mouseGetPosition(&mouseX, &mouseY);
        *dx = gQuickDropX - mouseX;
        *dy = gQuickDropY - mouseY;
    }

    // Un clic deve durare almeno un frame anche se il pulsante viene
    // rilasciato prima che il gioco legga l'input.
    if (gMouseLeftHeld || gMouseLeftPulse > 0 || gQuickDropPending || gQuickDropUntil != 0) {
        *buttons |= MOUSE_STATE_LEFT_BUTTON_DOWN;
        gLeftDownPolls++;
    }
    if (gMouseRightHeld || gMouseRightPulse > 0) {
        *buttons |= MOUSE_STATE_RIGHT_BUTTON_DOWN;
    }
    if (gMouseLeftPulse > 0) gMouseLeftPulse--;
    if (gMouseRightPulse > 0) gMouseRightPulse--;
}

// -----------------------------------------------------------------------------
// Oggetti interattivi (aggancio bersagli e tocco)
// -----------------------------------------------------------------------------

struct Candidate {
    Object* object;
    int x;
    int y;
    Rect rect;
};

static bool gIncludeDude = false; // abilità su se stessi (pronto soccorso)

static bool isInteresting(Object* object, bool combatOnly)
{
    if (object == nullptr) {
        return false;
    }

    if (object == gDude) {
        return gIncludeDude && !combatOnly;
    }

    if ((object->flags & OBJECT_HIDDEN) != 0) {
        return false;
    }

    int type = PID_TYPE(object->pid);

    if (type == OBJ_TYPE_CRITTER) {
        if (combatOnly) {
            return !critterIsDead(object) && !objectIsPartyMember(object);
        }
        // Anche i corpi: si possono perquisire.
        return true;
    }

    if (combatOnly) {
        return false;
    }

    if (type == OBJ_TYPE_ITEM) {
        return true;
    }

    if (type == OBJ_TYPE_SCENERY) {
        Proto* proto;
        if (protoGetProto(object->pid, &proto) == -1) {
            return false;
        }
        if (proto->scenery.type != SCENERY_TYPE_GENERIC) {
            return true; // porte, scale, ascensori
        }
        // Solo gli oggetti che si possono usare (computer, interruttori...):
        // non i muri o i mobili decorativi che hanno uno script.
        return _obj_action_can_use(object);
    }

    return false;
}

static bool isoWindowRect(Rect* rect)
{
    if (windowGetRect(gIsoWindow, rect) == -1) {
        return false;
    }
    return true;
}

// Parte della mappa davvero visibile: con IFACE_BAR_MODE=1 la vista continua
// dietro il pannello, che ne copre il fondo.
static bool isoVisibleRect(Rect* out)
{
    Rect iso;
    if (!isoWindowRect(&iso)) {
        return false;
    }
    Rect bar;
    if (gInterfaceBarWindow != -1 && windowGetRect(gInterfaceBarWindow, &bar) != -1) {
        if (bar.top > iso.top && bar.top <= iso.bottom) {
            iso.bottom = bar.top - 1;
        }
    }
    *out = iso;
    return true;
}

static void collectCandidates(std::vector<Candidate>& out, bool combatOnly)
{
    out.clear();

    Rect view;
    if (!isoVisibleRect(&view)) {
        return;
    }

    for (Object* object = objectFindFirstAtElevation(gElevation); object != nullptr; object = objectFindNextAtElevation()) {
        if (!isInteresting(object, combatOnly)) {
            continue;
        }

        Rect rect;
        objectGetRect(object, &rect);
        if (rect.right <= rect.left || rect.bottom <= rect.top) {
            continue;
        }

        Candidate candidate;
        candidate.object = object;
        candidate.rect = rect;
        candidate.x = (rect.left + rect.right) / 2;
        // Un po' sotto il centro: le figure sono alte e il punto "pieno"
        // dello sprite è sul busto.
        candidate.y = rect.top + (rect.bottom - rect.top) * 3 / 5;

        if (candidate.x < view.left + 4 || candidate.x > view.right - 4
            || candidate.y < view.top + 4 || candidate.y > view.bottom - 4) {
            continue;
        }

        out.push_back(candidate);
    }
}

bool gamepadSnapPoint(int* x, int* y)
{
    if (!mapIsActive()) {
        return false;
    }

    int mode = gameMouseGetMode();
    if (mode == GAME_MOUSE_MODE_MOVE) {
        return false;
    }

    std::vector<Candidate> candidates;
    collectCandidates(candidates, mode == GAME_MOUSE_MODE_CROSSHAIR);

    const int margin = 14 * screenGetHeight() / 480;
    int best = INT_MAX;
    const Candidate* found = nullptr;
    for (const Candidate& candidate : candidates) {
        if (*x < candidate.rect.left - margin || *x > candidate.rect.right + margin
            || *y < candidate.rect.top - margin || *y > candidate.rect.bottom + margin) {
            continue;
        }
        int ddx = *x - candidate.x;
        int ddy = *y - candidate.y;
        int distance = ddx * ddx + ddy * ddy;
        if (distance < best) {
            best = distance;
            found = &candidate;
        }
    }

    if (found == nullptr) {
        return false;
    }

    *x = found->x;
    *y = found->y;
    return true;
}

// Oggetto interattivo sotto il punto. Il rettangolo dello sprite è più largo
// della figura, quindi si usa una versione ristretta.
static Object* objectAtPoint(int x, int y, bool combatOnly)
{
    std::vector<Candidate> candidates;
    collectCandidates(candidates, combatOnly);

    Object* found = nullptr;
    int best = INT_MAX;
    for (const Candidate& candidate : candidates) {
        const Rect& rect = candidate.rect;
        int width = rect.right - rect.left;
        int height = rect.bottom - rect.top;
        if (x < rect.left + width * 15 / 100 || x > rect.right - width * 15 / 100
            || y < rect.top + height / 10 || y > rect.bottom) {
            continue;
        }
        int ddx = x - candidate.x;
        int ddy = y - candidate.y;
        if (ddx * ddx + ddy * ddy < best) {
            best = ddx * ddx + ddy * ddy;
            found = candidate.object;
        }
    }
    return found;
}

// Clic intelligente: sceglie da solo il cursore giusto.
//  - Esplorazione: su un oggetto usa/parla/raccogli, sul pavimento cammina.
//  - Combattimento: il primo tocco su un nemico mette il mirino (e mostra la
//    probabilità di colpire), il secondo attacca. Lo stesso per tornare a
//    muoversi: niente punti azione sprecati per errore.
// Restituisce false se il clic va trattenuto (serve una conferma).
bool gamepadSmartClick(int x, int y)
{
    if (!mapIsActive()) {
        return true;
    }

    Rect view;
    if (!isoVisibleRect(&view) || x < view.left || x > view.right || y < view.top || y > view.bottom) {
        return true; // barra dell'interfaccia
    }

    int mode = gameMouseGetMode();

    if (!isInCombat()) {
        if (mode == GAME_MOUSE_MODE_MOVE) {
            if (objectAtPoint(x, y, false) != nullptr) {
                gameMouseSetMode(GAME_MOUSE_MODE_ARROW);
            }
        } else if (mode == GAME_MOUSE_MODE_ARROW) {
            if (objectAtPoint(x, y, false) == nullptr) {
                gameMouseSetMode(GAME_MOUSE_MODE_MOVE);
            }
        }
        return true;
    }

    if (mode == GAME_MOUSE_MODE_MOVE && objectAtPoint(x, y, true) != nullptr) {
        gameMouseSetMode(GAME_MOUSE_MODE_CROSSHAIR);
        return false;
    }

    if (mode == GAME_MOUSE_MODE_CROSSHAIR && objectAtPoint(x, y, true) == nullptr) {
        gameMouseSetMode(GAME_MOUSE_MODE_MOVE);
        return false;
    }

    return true;
}

// Punto dell'oggetto su cui mettere il cursore: un pixel pieno dello sprite
// vicino al centro (il gioco riconosce l'oggetto solo sui pixel pieni).
static void objectAimPoint(Object* object, int* outX, int* outY)
{
    Rect rect;
    objectGetRect(object, &rect);
    int x = (rect.left + rect.right) / 2;
    int y = rect.top + (rect.bottom - rect.top) * 3 / 5;

    if (_obj_intersects_with(object, x, y) == 0) {
        int bestDistance = INT_MAX;
        int bestX = x;
        int bestY = y;
        for (int sy = rect.top; sy <= rect.bottom; sy += 2) {
            for (int sx = rect.left; sx <= rect.right; sx += 2) {
                int ddx = sx - x;
                int ddy = sy - y;
                int distance = ddx * ddx + ddy * ddy;
                if (distance < bestDistance && _obj_intersects_with(object, sx, sy) != 0) {
                    bestDistance = distance;
                    bestX = sx;
                    bestY = sy;
                }
            }
        }
        x = bestX;
        y = bestY;
    }

    *outX = x;
    *outY = y;
}

static void cycleTarget(int step, bool combat)
{
    std::vector<Candidate> candidates;
    collectCandidates(candidates, combat);
#ifdef FALLOUT_AUTOTEST
    printf("[pad] bersagli: %zu\n", candidates.size());
#endif
    if (candidates.empty()) {
        gTargetCurrent = nullptr;
        return;
    }

    int dudeX = 0;
    int dudeY = 0;
    tileToScreenXY(gDude->tile, &dudeX, &dudeY, gDude->elevation);
    dudeX += 16;
    dudeY += 8;

    if (combat) {
        // In combattimento prima chi ce l'ha con te, poi dal più vicino al
        // più lontano: il primo RB non finisce mai su un passante.
        auto hostile = [](Object* critter) {
            return (critter->data.critter.combat.maneuver & CRITTER_MANEUVER_ENGAGING) != 0
                || critter->data.critter.combat.whoHitMe == gDude;
        };
        std::sort(candidates.begin(), candidates.end(), [&hostile](const Candidate& a, const Candidate& b) {
            bool ha = hostile(a.object);
            bool hb = hostile(b.object);
            if (ha != hb) {
                return ha;
            }
            return tileDistanceBetween(gDude->tile, a.object->tile) < tileDistanceBetween(gDude->tile, b.object->tile);
        });
    } else if (hexModeActive()) {
        // Esplorazione a esagoni: dal più vicino a te al più lontano.
        std::sort(candidates.begin(), candidates.end(), [](const Candidate& a, const Candidate& b) {
            return tileDistanceBetween(gDude->tile, a.object->tile) < tileDistanceBetween(gDude->tile, b.object->tile);
        });
    } else {
        // In esplorazione in senso orario attorno al personaggio, così LB/RB
        // si comportano come "a sinistra / a destra".
        std::sort(candidates.begin(), candidates.end(), [dudeX, dudeY](const Candidate& a, const Candidate& b) {
            double angleA = atan2((double)(a.y - dudeY), (double)(a.x - dudeX));
            double angleB = atan2((double)(b.y - dudeY), (double)(b.x - dudeX));
            return angleA < angleB;
        });
    }

    int index = -1;
    for (size_t i = 0; i < candidates.size(); i++) {
        if (candidates[i].object == gTargetCurrent) {
            index = (int)i;
            break;
        }
    }

    if (index == -1) {
        if (combat || (hexModeActive() && gCombatHex == -1)) {
            index = 0;
        } else {
            // Primo aggancio: l'oggetto più vicino al cursore.
            int mouseX;
            int mouseY;
            mouseGetPosition(&mouseX, &mouseY);
            int best = INT_MAX;
            for (size_t i = 0; i < candidates.size(); i++) {
                int ddx = candidates[i].x - mouseX;
                int ddy = candidates[i].y - mouseY;
                if (ddx * ddx + ddy * ddy < best) {
                    best = ddx * ddx + ddy * ddy;
                    index = (int)i;
                }
            }
        }
    } else {
        index = (index + step + (int)candidates.size()) % (int)candidates.size();
    }

    gTargetCurrent = candidates[index].object;
    gWarpPending = true;
    objectAimPoint(gTargetCurrent, &gWarpX, &gWarpY);

    // Cursore giusto per l'oggetto: mirino sui nemici in combattimento,
    // freccia "usa" sugli oggetti in esplorazione.
    int wanted = combat ? GAME_MOUSE_MODE_CROSSHAIR : GAME_MOUSE_MODE_ARROW;
    if (gameMouseGetMode() == GAME_MOUSE_MODE_MOVE || (combat && gameMouseGetMode() == GAME_MOUSE_MODE_ARROW)) {
        gameMouseSetMode(wanted);
    }
}

// -----------------------------------------------------------------------------
// Modalità senza puntatore: oggetto evidenziato
// -----------------------------------------------------------------------------

// Si può parlare davvero solo con chi ha un dialogo nel suo script: per il
// gioco ogni creatura "può parlare", anche un ratto.
static bool critterCanTalk(Object* critter)
{
    if (!_obj_action_can_talk_to(critter) || critter->sid == -1) {
        return false;
    }
    Script* script;
    if (scriptGetScript(critter->sid, &script) == -1) {
        return false;
    }
    return script->procs[SCRIPT_PROC_TALK] != SCRIPT_PROC_NO_PROC;
}

// Persone (uomini, donne, bambini, mutanti, ghoul): senza dialogo A le
// esamina e basta, così in città non parte mai un combattimento per sbaglio.
static bool critterIsPerson(Object* critter)
{
    int killType = critterGetKillType(critter);
    return killType >= KILL_TYPE_MAN && killType <= KILL_TYPE_GHOUL;
}

// A su una creatura con cui non si parla: parte il combattimento con lei già
// nel mirino (al primo turno utile), poi A spara.
static Object* gPendingAttackTarget = nullptr;
static void focusLook();
static Uint32 gPendingAttackUntil = 0;

static bool isSkillMode(int mode)
{
    return mode >= FIRST_GAME_MOUSE_MODE_SKILL && mode < GAME_MOUSE_MODE_COUNT;
}

static int skillForMode(int mode)
{
    switch (mode) {
    case GAME_MOUSE_MODE_USE_FIRST_AID:
        return SKILL_FIRST_AID;
    case GAME_MOUSE_MODE_USE_DOCTOR:
        return SKILL_DOCTOR;
    case GAME_MOUSE_MODE_USE_LOCKPICK:
        return SKILL_LOCKPICK;
    case GAME_MOUSE_MODE_USE_STEAL:
        return SKILL_STEAL;
    case GAME_MOUSE_MODE_USE_TRAPS:
        return SKILL_TRAPS;
    case GAME_MOUSE_MODE_USE_SCIENCE:
        return SKILL_SCIENCE;
    case GAME_MOUSE_MODE_USE_REPAIR:
        return SKILL_REPAIR;
    }
    return -1;
}

static void focusSetOutline(Object* object, bool on)
{
    if (object == nullptr) {
        return;
    }

    Rect rect;
    int rc = on ? objectSetOutline(object, OUTLINE_TYPE_ITEM, &rect) : objectClearOutline(object, &rect);
    if (rc == 0) {
        tileWindowRefreshRect(&rect, object->elevation);
    }
}

// Toglie l'evidenziazione. Se l'oggetto non è più sulla mappa (raccolto,
// distrutto, cambio mappa) non lo tocca: il puntatore potrebbe non valere più.
static void focusClear(bool objectStillValid)
{
    if (gFocus != nullptr && gFocusOutlined && objectStillValid) {
        focusSetOutline(gFocus, false);
    }
    gFocus = nullptr;
    gFocusOutlined = false;
    gFocusManual = false;
    gFocusNameDue = 0;
    gTargetCurrent = nullptr;
}

static void focusSet(Object* object)
{
    if (object == gFocus) {
        return;
    }
#ifdef FALLOUT_AUTOTEST
    if (object != nullptr && PID_TYPE(object->pid) == OBJ_TYPE_SCENERY) {
        Proto* proto;
        protoGetProto(object->pid, &proto);
        printf("[pad] focus -> scenery pid %x tipo %d sid %d uso %d\n", object->pid, proto->scenery.type, object->sid, _obj_action_can_use(object));
    } else {
        printf("[pad] focus -> %p (dude %p) pid %x\n", (void*)object, (void*)gDude, object ? object->pid : 0);
    }
#endif
    focusClear(true);
    gFocus = object;
    if (gFocus != nullptr && gFocus != gDude) {
        focusSetOutline(gFocus, true);
        gFocusOutlined = true;
        gFocusNameDue = SDL_GetTicks() + 400;
    }
}

static double angleBetween(double ax, double ay, double bx, double by)
{
    double la = sqrt(ax * ax + ay * ay);
    double lb = sqrt(bx * bx + by * by);
    if (la < 0.001 || lb < 0.001) {
        return 0.0;
    }
    double c = (ax * bx + ay * by) / (la * lb);
    return acos(std::clamp(c, -1.0, 1.0));
}

// Sceglie l'oggetto da evidenziare: vicino e nella direzione in cui ti muovi.
static void focusUpdate()
{
    gIncludeDude = isSkillMode(gameMouseGetMode());

    std::vector<Candidate> candidates;
    collectCandidates(candidates, false);

    bool currentValid = false;
    for (const Candidate& candidate : candidates) {
        if (candidate.object == gFocus) {
            currentValid = true;
            break;
        }
    }

    if (gFocus != nullptr && !currentValid) {
        // È sparito dalla mappa: niente da ripulire.
        gFocusOutlined = false;
        focusClear(false);
    }

    if (gFocusManual && currentValid) {
        return;
    }

    int dudeX;
    int dudeY;
    tileToScreenXY(gDude->tile, &dudeX, &dudeY, gDude->elevation);
    dudeX += 16;
    dudeY += 8;

    Object* best = nullptr;
    double bestScore = 1e9;
    double currentScore = 1e9;
    for (const Candidate& candidate : candidates) {
        int distance = candidate.object == gDude ? 0 : tileDistanceBetween(gDude->tile, candidate.object->tile);
        if (distance > 8) {
            continue;
        }
        double angle = candidate.object == gDude ? 0.0 : angleBetween(gFacingX, gFacingY, candidate.x - dudeX, candidate.y - dudeY);
        double score = distance + angle * 1.5;
        if (PID_TYPE(candidate.object->pid) == OBJ_TYPE_CRITTER && !critterIsDead(candidate.object)) {
            score -= 2.0; // le persone sono la cosa con cui interagisci più spesso
        }
        if (candidate.object == gDude) {
            score = 3.0; // in modalità abilità si può scegliere anche se stessi
        }
        if (candidate.object == gFocus) {
            currentScore = score;
        }
        if (score < bestScore) {
            bestScore = score;
            best = candidate.object;
        }
    }

    // Isteresi: non saltare avanti e indietro tra due oggetti vicini.
    if (gFocus != nullptr && currentScore < 1e8 && bestScore > currentScore - 1.5) {
        return;
    }

    focusSet(best);
}

// Tiene il cursore (nascosto) sull'oggetto evidenziato, così le funzioni del
// gioco che guardano "cosa c'è sotto il cursore" vedono l'oggetto giusto.
static void focusParkCursor()
{
    int x = screenGetWidth() / 2;
    int y = screenGetHeight() - 20; // sulla barra dell'interfaccia
    if (gFocus != nullptr) {
        objectAimPoint(gFocus, &x, &y);
    }

    int mouseX;
    int mouseY;
    mouseGetPosition(&mouseX, &mouseY);
    if (abs(mouseX - x) > 2 || abs(mouseY - y) > 2) {
        gWarpPending = true;
        gWarpX = x;
        gWarpY = y;
    }
}

// A: l'azione principale sull'oggetto evidenziato, come un clic con il
// cursore "usa" del gioco originale.
static void focusUse()
{
    Object* target = gFocus;
    if (target == nullptr) {
        return;
    }

    int mode = gameMouseGetMode();
    if (isSkillMode(mode)) {
        int skill = skillForMode(mode);
        focusClear(true);
        if (actionUseSkill(gDude, target, skill) != -1) {
            gameMouseSetCursor(MOUSE_CURSOR_NONE);
            gameMouseSetMode(GAME_MOUSE_MODE_ARROW);
        }
        return;
    }

    if (mode == GAME_MOUSE_MODE_USE_CROSSHAIR) {
        Object* item;
        focusClear(true);
        if (interfaceGetActiveItem(&item) != -1) {
            _action_use_an_item_on_object(gDude, target, item);
        }
        gameMouseSetCursor(MOUSE_CURSOR_NONE);
        gameMouseSetMode(GAME_MOUSE_MODE_ARROW);
        return;
    }

    switch (PID_TYPE(target->pid)) {
    case OBJ_TYPE_ITEM:
        focusClear(true);
        actionPickUp(gDude, target);
        break;
    case OBJ_TYPE_CRITTER:
        if (target == gDude) {
            break;
        }
        if (critterCanTalk(target)) {
            actionTalk(gDude, target);
        } else if (!critterIsDead(target) && critterIsPerson(target)) {
            focusLook();
        } else if (!critterIsDead(target)) {
            gPendingAttackTarget = target;
            gPendingAttackUntil = SDL_GetTicks() + 4000;
            inputInjectKey(SDL_SCANCODE_A, true); // inizia il combattimento
            inputInjectKey(SDL_SCANCODE_A, false);
        } else {
            _action_loot_container(gDude, target);
        }
        break;
    case OBJ_TYPE_SCENERY:
        if (_obj_action_can_use(target)) {
            _action_use_an_object(gDude, target);
        } else if (_obj_examine(gDude, target) == -1) {
            _obj_look_at(gDude, target);
        }
        break;
    }
}

static void focusLook()
{
    if (gFocus != nullptr && _obj_examine(gDude, gFocus) == -1) {
        _obj_look_at(gDude, gFocus);
    }
}

// Stick destro: sposta la visuale.
static void cameraStickTick()
{
    double nx;
    double ny;
    double magnitude = stickRead(SDL_CONTROLLER_AXIS_RIGHTX, SDL_CONTROLLER_AXIS_RIGHTY, &nx, &ny);
    if (magnitude <= 0.0) {
        return;
    }
    Uint32 now = SDL_GetTicks();
    Uint32 interval = (Uint32)(140 - 100 * magnitude);
    if (now - gLastScrollTick < interval) {
        return;
    }
    gLastScrollTick = now;
    int dx = fabs(nx) > 0.38 ? (nx > 0 ? 1 : -1) : 0;
    int dy = fabs(ny) > 0.38 ? (ny > 0 ? 1 : -1) : 0;
    mapScroll(dx, dy);
    hintsAfterScroll();
}

// -----------------------------------------------------------------------------
// Combattimento: esagono di destinazione scelto con lo stick
// -----------------------------------------------------------------------------

static void hexCenter(int tile, int* x, int* y)
{
    tileToScreenXY(tile, x, y, gDude->elevation);
    *x += 16;
    *y += 8;
}

// Sposta l'esagono scelto di un passo nella direzione dello stick. Vale in
// combattimento e, con hex_movement, anche in esplorazione (lì più veloce).
// Restituisce true se l'esagono si è spostato.
static bool hexStep(bool explore)
{
    double nx;
    double ny;
    double magnitude = stickRead(SDL_CONTROLLER_AXIS_LEFTX, SDL_CONTROLLER_AXIS_LEFTY, &nx, &ny);
    Uint32 now = SDL_GetTicks();

    if (magnitude < 0.5) {
        gCombatStickActive = false;
        return false;
    }

    if (gCombatStickActive && now < gCombatHexNext) {
        return false;
    }
    Uint32 repeat = explore ? (Uint32)(170 - 100 * magnitude) : 170;
    gCombatHexNext = now + (gCombatStickActive ? repeat : (explore ? 240 : 300));
    gCombatStickActive = true;

    // Si parte dal personaggio se si è mosso o se non c'è una scelta.
    if (gCombatHex == -1 || gCombatHexOrigin != gDude->tile) {
        gCombatHex = gDude->tile;
        gCombatHexOrigin = gDude->tile;
    }

    // Tra i 6 lati dell'esagono quello più vicino alla direzione dello stick
    // (calcolato sullo schermo, così vale per qualsiasi orientamento).
    int cx;
    int cy;
    hexCenter(gCombatHex, &cx, &cy);
    int bestRotation = -1;
    double bestDot = -2.0;
    double secondDot = -2.0;
    int secondRotation = -1;
    for (int rotation = 0; rotation < 6; rotation++) {
        int neighbor = tileGetTileInDirection(gCombatHex, rotation, 1);
        if (neighbor == -1) {
            continue;
        }
        int x;
        int y;
        hexCenter(neighbor, &x, &y);
        double vx = x - cx;
        double vy = y - cy;
        double length = sqrt(vx * vx + vy * vy);
        if (length < 1.0) {
            continue;
        }
        double dot = (vx * nx + vy * ny) / length;
        if (dot > bestDot) {
            secondDot = bestDot;
            secondRotation = bestRotation;
            bestDot = dot;
            bestRotation = rotation;
        } else if (dot > secondDot) {
            secondDot = dot;
            secondRotation = rotation;
        }
    }
    if (bestRotation == -1) {
        return false;
    }
    // Su e giù cadono a metà tra due lati: si alterna per andare dritti.
    if (secondRotation != -1 && bestDot - secondDot < 0.08 && bestRotation == gCombatHexLastDir) {
        bestRotation = secondRotation;
    }
    gCombatHexLastDir = bestRotation;

    int next = tileGetTileInDirection(gCombatHex, bestRotation, 1);
    if (next == -1) {
        return false;
    }
    gCombatHex = next;
    return true;
}

static void combatStickTick()
{
    if (!hexStep(false)) {
        return;
    }
    gameMouseSetMode(GAME_MOUSE_MODE_MOVE);
    gWarpPending = true;
    hexCenter(gCombatHex, &gWarpX, &gWarpY);
}

// -----------------------------------------------------------------------------
// Movimento diretto con lo stick
// -----------------------------------------------------------------------------

static int stickTargetTile(double nx, double ny)
{
    int dudeX;
    int dudeY;
    if (tileToScreenXY(gDude->tile, &dudeX, &dudeY, gDude->elevation) == -1) {
        return -1;
    }
    dudeX += 16;
    dudeY += 8;

    // Prova a 6, 5, 4, 3, 2 esagoni di distanza (tratti lunghi = meno ripartenze); la griglia isometrica è
    // schiacciata in verticale, quindi la componente y vale meno.
    static const int distances[] = { 192, 160, 128, 96, 64, 40 };
    for (int distance : distances) {
        int x = dudeX + (int)(nx * distance);
        int y = dudeY + (int)(ny * distance * 0.75);
        int tile = tileFromScreenXY(x, y, gDude->elevation);
        if (tile == -1 || tile == gDude->tile) {
            continue;
        }
        if (_obj_blocking_at(gDude, tile, gDude->elevation) != nullptr) {
            continue;
        }
        return tile;
    }
    return -1;
}

static void issueMove(int tile, bool run)
{
#ifdef FALLOUT_AUTOTEST
    printf("[pad] muovi verso %d da %d (corsa %d)\n", tile, gDude->tile, run);
#endif
    reg_anim_clear(gDude);
    if (reg_anim_begin(ANIMATION_REQUEST_RESERVED) == -1) {
        return;
    }
    if (run) {
        animationRegisterRunToTile(gDude, tile, gDude->elevation, -1, 0);
    } else {
        animationRegisterMoveToTile(gDude, tile, gDude->elevation, -1, 0);
    }
    reg_anim_end();
}

// Visuale che segue il personaggio con passi piccoli e continui (come lo
// scorrimento ai bordi del gioco) invece di un salto di un quarto di schermo:
// niente scatti quando si passa da una zona all'altra della mappa.
static Uint32 gFollowUntil = 0;

// Scorre la visuale di un passo se il punto (x, y) esce dalla zona centrale
// (larga 2/deadDiv della vista).
static void followPoint(int tile, int deadDiv)
{
    Rect view;
    if (!isoVisibleRect(&view)) {
        return;
    }

    int x;
    int y;
    if (tileToScreenXY(tile, &x, &y, gDude->elevation) == -1) {
        return;
    }
    x += 16;
    y += 8;

    int width = view.right - view.left;
    int height = view.bottom - view.top;
    int dx = x - (view.left + width / 2);
    int dy = y - (view.top + height / 2);
    int deadX = width / deadDiv;
    int deadY = height / deadDiv;

    int stepX = dx > deadX ? 1 : (dx < -deadX ? -1 : 0);
    int stepY = dy > deadY ? 1 : (dy < -deadY ? -1 : 0);
    if (stepX == 0 && stepY == 0) {
        return;
    }

    // Punto uscito del tutto dalla vista (cambio piano, teletrasporto):
    // lì conviene ricentrare subito.
    if (abs(dx) > width / 2 || abs(dy) > height / 2) {
        _tile_scroll_to(tile, 2);
        return;
    }

    bool wasVisible = gameMouseObjectsIsVisible();
    mapScroll(stepX, stepY);
    hintsAfterScroll();
    if (wasVisible && !gameMouseObjectsIsVisible()) {
        gameMouseObjectsShow();
    }
}

static void followCamera()
{
    if (gMobile.cameraFollow) {
        followPoint(gDude->tile, 7);
    }
}

static void stickMovementTick()
{
    double nx;
    double ny;
    double magnitude = stickRead(SDL_CONTROLLER_AXIS_LEFTX, SDL_CONTROLLER_AXIS_LEFTY, &nx, &ny);
    Uint32 now = SDL_GetTicks();

    if (magnitude <= 0.0) {
        if (gStickWasMoving) {
            gStickWasMoving = false;
            gStickLastTarget = -1;
            // Fermati sull'esagono successivo, senza scatti.
            if (animationIsBusy(gDude)) {
                int next = tileGetTileInDirection(gDude->tile, gDude->rotation, 1);
                if (next != -1 && _obj_blocking_at(gDude, next, gDude->elevation) == nullptr) {
                    issueMove(next, false);
                } else {
                    reg_anim_clear(gDude);
                }
            }
        }
        return;
    }

    if (!gPadMode) {
        gameMouseSetMode(GAME_MOUSE_MODE_MOVE);
    }
    gFacingX = nx;
    gFacingY = ny;
    gFocusManual = false;

    bool run = magnitude > 0.8;
    double angle = atan2(ny, nx);
    double angleDelta = fabs(angle - gStickLastAngle);
    if (angleDelta > kPi) {
        angleDelta = 2 * kPi - angleDelta;
    }

    bool directionChanged = angleDelta > 0.6; // ~35 gradi
    bool nearTarget = gStickLastTarget == -1 || tileDistanceBetween(gDude->tile, gStickLastTarget) <= 3;
    bool idle = !animationIsBusy(gDude);
    bool gaitChanged = run != gStickRunning;

    if ((nearTarget || directionChanged || idle || gaitChanged) && now - gStickLastIssue >= 120) {
        int tile = stickTargetTile(nx, ny);
        if (tile != -1 && (tile != gStickLastTarget || idle)) {
            issueMove(tile, run);
            gStickLastTarget = tile;
            gStickLastIssue = now;
            gStickLastAngle = angle;
            gStickRunning = run;
        }
    }

    gStickWasMoving = true;
    gFollowUntil = now + 1500;
}

// -----------------------------------------------------------------------------
// Esplorazione a esagoni (hex_movement): lo stick sposta un esagono come in
// combattimento, A ci porta il personaggio. Se sull'esagono c'è una persona o
// un oggetto, viene evidenziato e A ci interagisce.
// -----------------------------------------------------------------------------

static Object* objectOnHex(const std::vector<Candidate>& candidates, int hex)
{
    Object* best = nullptr;
    int bestRank = 99;
    for (const Candidate& candidate : candidates) {
        Object* object = candidate.object;
        if (object->tile != hex) {
            continue;
        }
        if (object == gDude && !gIncludeDude) {
            continue;
        }
        int rank = 3;
        if (PID_TYPE(object->pid) == OBJ_TYPE_CRITTER) {
            rank = critterIsDead(object) ? 1 : 0;
        } else if (PID_TYPE(object->pid) == OBJ_TYPE_ITEM) {
            rank = 2;
        }
        if (rank < bestRank) {
            bestRank = rank;
            best = object;
        }
    }
    return best;
}

static bool hexModeActive()
{
    return gMobile.stickMovement && gMobile.hexMovement;
}

static void exploreHexTick()
{
    gIncludeDude = isSkillMode(gameMouseGetMode());

    std::vector<Candidate> candidates;
    collectCandidates(candidates, false);

    if (gFocus != nullptr) {
        bool valid = false;
        for (const Candidate& candidate : candidates) {
            if (candidate.object == gFocus) {
                valid = true;
                break;
            }
        }
        if (!valid) {
            gFocusOutlined = false;
            focusClear(false);
        }
    }

    bool moved = !gameUiIsDisabled() && hexStep(true);
    if (moved) {
        gFocusManual = false;
        followPoint(gCombatHex, 3);
    } else if (SDL_GetTicks() < gFollowUntil) {
        if (animationIsBusy(gDude)) {
            gFollowUntil = SDL_GetTicks() + 300;
        }
        followCamera();
    }

    // Arrivato: l'esagono sparisce (si riparte da te alla prossima mossa).
    if (gCombatHex != -1 && gCombatHex == gDude->tile && !gIncludeDude && !moved) {
        gCombatHex = -1;
    }

    if (!gFocusManual) {
        focusSet(gCombatHex != -1 ? objectOnHex(candidates, gCombatHex) : nullptr);
    }

    gHexShown = gCombatHex != -1 && gFocus == nullptr && !gMenuHold;
    if (gHexShown) {
        if (gameMouseGetMode() != GAME_MOUSE_MODE_MOVE) {
            gameMouseSetMode(GAME_MOUSE_MODE_MOVE);
        }
        if (!gameMouseObjectsIsVisible()) {
            gameMouseObjectsShow();
        }
        int x;
        int y;
        hexCenter(gCombatHex, &x, &y);
        int mouseX;
        int mouseY;
        mouseGetPosition(&mouseX, &mouseY);
        if (abs(mouseX - x) > 1 || abs(mouseY - y) > 1) {
            gWarpPending = true;
            gWarpX = x;
            gWarpY = y;
        }
    } else {
        if (!gMenuHold && gameMouseObjectsIsVisible()) {
            gameMouseObjectsHide();
            gWeHidMapCursor = true;
        }
        if (gameMouseGetMode() == GAME_MOUSE_MODE_MOVE || gameMouseGetMode() == GAME_MOUSE_MODE_CROSSHAIR) {
            gameMouseSetMode(GAME_MOUSE_MODE_ARROW);
        }
        if (!gMenuHold) {
            focusParkCursor();
        }
    }
}

// A senza niente di evidenziato: cammina fino all'esagono (corre se è lontano).
static bool exploreHexWalk()
{
    if (gCombatHex == -1 || gCombatHex == gDude->tile) {
        return false;
    }
    issueMove(gCombatHex, tileDistanceBetween(gDude->tile, gCombatHex) > 4);
    gCombatHexOrigin = -1; // la prossima mossa dello stick riparte da te
    gFollowUntil = SDL_GetTicks() + 1500;
    return true;
}

// Toglie l'evidenziazione controllando prima che l'oggetto sia ancora sulla
// mappa.
static void focusUpdateValidityAndClear()
{
    std::vector<Candidate> candidates;
    gIncludeDude = true;
    collectCandidates(candidates, false);
    bool valid = false;
    for (const Candidate& candidate : candidates) {
        if (candidate.object == gFocus) {
            valid = true;
            break;
        }
    }
    focusClear(valid);
}

// -----------------------------------------------------------------------------
// Barra dei comandi: sopra il pannello mostra i tasti utili in quel momento
// ("(A) Parla con Seth  (X) Esamina  (Y) Inventario"). Disegnata nella vista
// della mappa insieme ai testi fluttuanti, con i font e i colori del gioco.
// -----------------------------------------------------------------------------

struct HintItem {
    const char* button;
    std::string text;
};

static const int kHintHeight = 25;
static const int kHintPillHeight = 17;
std::string gHintKey;
static std::vector<unsigned char> gHintImage;
static int gHintWidth = 0;
bool gHintVisible = false;
static Rect gHintRect; // coordinate della finestra della mappa

static unsigned char hintColor(int r, int g, int b)
{
    return _colorTable[((r >> 3) << 10) | ((g >> 3) << 5) | (b >> 3)];
}

static std::string hintName(Object* object)
{
    char* name = objectGetName(object);
    return name != nullptr ? name : "";
}

// Il verbo segue quello che fa davvero A (vedi focusUse).
static std::string hintVerb(Object* object)
{
    std::string name = hintName(object);
    switch (PID_TYPE(object->pid)) {
    case OBJ_TYPE_ITEM:
        if (itemGetType(object) == ITEM_TYPE_CONTAINER) {
            return "Apri " + name;
        }
        return "Raccogli " + name;
    case OBJ_TYPE_CRITTER:
        if (critterIsDead(object)) {
            return "Perquisisci " + name;
        }
        if (critterCanTalk(object)) {
            return "Parla con " + name;
        }
        if (critterIsPerson(object)) {
            return "Esamina " + name;
        }
        return "Attacca " + name;
    case OBJ_TYPE_SCENERY: {
        Proto* proto;
        int type = SCENERY_TYPE_GENERIC;
        if (protoGetProto(object->pid, &proto) != -1) {
            type = proto->scenery.type;
        }
        switch (type) {
        case SCENERY_TYPE_DOOR:
            return (objectIsOpen(object) ? "Chiudi " : "Apri ") + name;
        case SCENERY_TYPE_LADDER_UP:
            return "Sali";
        case SCENERY_TYPE_LADDER_DOWN:
            return "Scendi";
        default:
            if (_obj_action_can_use(object)) {
                return "Usa " + name;
            }
            return "Esamina " + name;
        }
    }
    }
    return name;
}

// Arma della mano attiva (quella che A usa in combattimento).
static Object* activeHandItem()
{
    return interfaceGetCurrentHand() == HAND_LEFT ? critterGetItem1(gDude) : critterGetItem2(gDude);
}

// Hai in tasca munizioni adatte a quest'arma?
static bool hasAmmoFor(Object* weapon)
{
    if (weapon == nullptr) {
        return false;
    }
    int index = -1;
    Object* ammo;
    while ((ammo = _inven_find_type(gDude, ITEM_TYPE_AMMO, &index)) != nullptr) {
        if (weaponCanBeReloadedWith(weapon, ammo)) {
            return true;
        }
    }
    return false;
}

// In combattimento, col mirino su un bersaglio, l'arma è scarica ma si può
// ricaricare: A ricarica invece di fare "clic a vuoto".
static bool combatWeaponNeedsReload()
{
    if (!isInCombat() || gTargetCurrent == nullptr || gameMouseGetMode() != GAME_MOUSE_MODE_CROSSHAIR) {
        return false;
    }
    int hitMode;
    bool aiming;
    if (interfaceGetCurrentHitMode(&hitMode, &aiming) == -1) {
        return false;
    }
    return _combat_check_bad_shot(gDude, gTargetCurrent, hitMode, aiming) == COMBAT_BAD_SHOT_NO_AMMO
        && hasAmmoFor(activeHandItem());
}

// Casella scelta in esplorazione: ci si arriva? È un'uscita dalla mappa?
// (Il calcolo del percorso costa: si rifà solo quando cambia qualcosa.)
static void hexInfo(int hex, bool* reachable, bool* exitGrid)
{
    static int cachedFrom = -1;
    static int cachedHex = -1;
    static int cachedElevation = -1;
    static bool cachedReachable = true;
    static bool cachedExit = false;

    if (hex != cachedHex || gDude->tile != cachedFrom || gElevation != cachedElevation) {
        cachedHex = hex;
        cachedFrom = gDude->tile;
        cachedElevation = gElevation;
        cachedReachable = _make_path(gDude, gDude->tile, hex, nullptr, 0) > 0;
        cachedExit = false;
        for (Object* object = objectFindFirstAtElevation(gElevation); object != nullptr; object = objectFindNextAtElevation()) {
            if (object->tile == hex && object->pid >= 0x5000010 && object->pid <= 0x5000017) {
                cachedExit = true;
                break;
            }
        }
    }

    *reachable = cachedReachable;
    *exitGrid = cachedExit;
}

static void hintsCollect(std::vector<HintItem>& items, bool isInCombatMode)
{
    if (!gMobile.buttonHints || !gPadMode || gMenuHold || gameUiIsDisabled()) {
        return;
    }

    Context context = currentContext();
    if (context != CONTEXT_MAP && context != CONTEXT_COMBAT) {
        return;
    }

    int mode = gameMouseGetMode();
    Object* focus = (gFocus != nullptr && (gFocus != gDude || gIncludeDude)) ? gFocus : nullptr;

    if (isSkillMode(mode) || mode == GAME_MOUSE_MODE_USE_CROSSHAIR) {
        std::string text;
        if (isSkillMode(mode)) {
            char* skillName = skillGetName(skillForMode(mode));
            text = std::string("Usa ") + (skillName != nullptr ? skillName : "");
        } else {
            text = "Usa l'oggetto";
        }
        if (focus != nullptr) {
            text += focus == gDude ? " su di te" : " su " + hintName(focus);
            items.push_back({ "A", text });
        }
        items.push_back({ "RB", "Scegli" });
        items.push_back({ "B", "Annulla" });
        return;
    }

    if (isInCombatMode) {
        if (gTargetCurrent != nullptr) {
            bool found = false;
            for (Object* object = objectFindFirstAtElevation(gElevation); object != nullptr; object = objectFindNextAtElevation()) {
                if (object == gTargetCurrent) {
                    found = true;
                    break;
                }
            }
            if (!found || critterIsDead(gTargetCurrent)) {
                gTargetCurrent = nullptr;
            }
        }

        // Arma nella mano attiva (quella che spara/colpisce con A) e nell'altra.
        bool leftActive = interfaceGetCurrentHand() == HAND_LEFT;
        Object* weapon = leftActive ? critterGetItem1(gDude) : critterGetItem2(gDude);
        Object* other = leftActive ? critterGetItem2(gDude) : critterGetItem1(gDude);
        auto isWeapon = [](Object* item) {
            return item != nullptr && itemGetType(item) == ITEM_TYPE_WEAPON;
        };

        if (mode == GAME_MOUSE_MODE_CROSSHAIR && gTargetCurrent != nullptr) {
            int hitMode;
            bool aiming;
            interfaceGetCurrentHitMode(&hitMode, &aiming);
            bool ranged = isWeapon(weapon) && weaponGetRange(gDude, hitMode) > 1;
            std::string name = hintName(gTargetCurrent);
            std::string text;
            switch (_combat_check_bad_shot(gDude, gTargetCurrent, hitMode, aiming)) {
            case COMBAT_BAD_SHOT_OUT_OF_RANGE:
                // (niente lettere accentate: il font del gioco non le ha)
                text = isWeapon(weapon) ? name + " e' fuori portata" : "Troppo lontano per le mani nude";
                break;
            case COMBAT_BAD_SHOT_NO_AMMO:
                if (hasAmmoFor(weapon)) {
                    int reloadMode = leftActive ? HIT_MODE_LEFT_WEAPON_RELOAD : HIT_MODE_RIGHT_WEAPON_RELOAD;
                    text = "Ricarica (" + std::to_string(itemGetActionPointCost(gDude, reloadMode, false)) + " PA)";
                } else {
                    text = "Arma scarica: niente munizioni";
                }
                break;
            case COMBAT_BAD_SHOT_NOT_ENOUGH_AP:
                text = "PA insufficienti: chiudi il turno";
                break;
            case COMBAT_BAD_SHOT_AIM_BLOCKED:
                text = "Tiro bloccato verso " + name;
                break;
            case COMBAT_BAD_SHOT_ARM_CRIPPLED:
            case COMBAT_BAD_SHOT_BOTH_ARMS_CRIPPLED:
                text = "Braccio ferito: non puoi usare quest'arma";
                break;
            default:
                text = (ranged ? "Spara a " : "Colpisci ") + name
                    + " (" + std::to_string(itemGetActionPointCost(gDude, hitMode, aiming)) + " PA)";
                break;
            }
            items.push_back({ "A", text });
        } else if (gCombatHex != -1 && gCombatHex != gDude->tile) {
            items.push_back({ "A", "Vai qui" });
        }
        if (!isWeapon(weapon) && isWeapon(other)) {
            items.push_back({ "LT", "Usa " + hintName(other) });
        }
        items.push_back({ "RB", "Bersaglio" });
        items.push_back({ "RT", "Fine turno" });
        return;
    }

    if (focus == nullptr) {
        if (hexModeActive() && gCombatHex != -1 && gCombatHex != gDude->tile) {
            bool reachable;
            bool exitGrid;
            hexInfo(gCombatHex, &reachable, &exitGrid);
            if (!reachable) {
                items.push_back({ "A", "Da qui non ci arrivi" });
            } else if (exitGrid) {
                items.push_back({ "A", "Esci dalla zona" });
            } else {
                items.push_back({ "A", tileDistanceBetween(gDude->tile, gCombatHex) > 4 ? "Corri qui" : "Vai qui" });
            }
            items.push_back({ "RB", "Oggetti vicini" });
            items.push_back({ "B", "Annulla" });
        }
        return;
    }

    items.push_back({ "A", hintVerb(focus) });
    items.push_back({ "X", "Esamina" });
    items.push_back({ "Y", "Inventario" });
}

static int hintPillWidth(const char* button)
{
    int oldFont = fontGetCurrent();
    fontSetCurrent(strlen(button) > 1 ? 100 : 101);
    int width = std::max(kHintPillHeight, fontGetStringWidth(button) + 10);
    fontSetCurrent(oldFont);
    return width;
}

// Pulsantino metallico come quelli del pannello, con la lettera in verde.
static void hintDrawPill(unsigned char* dest, int pitch, const char* button)
{
    int width = hintPillWidth(button);
    int height = kHintPillHeight;
    double radius = height / 2.0;
    unsigned char black = hintColor(0, 0, 0);
    unsigned char ring = hintColor(150, 130, 90);
    unsigned char ringDark = hintColor(92, 80, 56);
    unsigned char inner = hintColor(28, 26, 20);

    for (int y = 0; y < height; y++) {
        for (int x = 0; x < width; x++) {
            double dx = std::max(0.0, fabs(x + 0.5 - width / 2.0) - (width / 2.0 - radius));
            double dy = fabs(y + 0.5 - height / 2.0);
            double d = sqrt(dx * dx + dy * dy);
            unsigned char* pixel = dest + y * pitch + x;
            if (d > radius) {
                continue;
            } else if (d > radius - 1.2) {
                *pixel = black;
            } else if (d > radius - 2.2) {
                *pixel = ring;
            } else if (d > radius - 3.2) {
                *pixel = ringDark;
            } else {
                *pixel = inner;
            }
        }
    }

    int oldFont = fontGetCurrent();
    fontSetCurrent(strlen(button) > 1 ? 100 : 101);
    int textWidth = fontGetStringWidth(button);
    int textHeight = fontGetLineHeight();
    fontDrawText(dest + ((height - textHeight) / 2) * pitch + (width - textWidth) / 2 + 1,
        button, textWidth + 2, pitch, _colorTable[992]);
    fontSetCurrent(oldFont);
}

static void hintsBuild(const std::vector<HintItem>& items, int maxWidth)
{
    int oldFont = fontGetCurrent();
    fontSetCurrent(101);

    // Testi troppo lunghi (nomi degli oggetti): si accorciano con "...".
    std::vector<std::string> texts;
    for (const HintItem& item : items) {
        texts.push_back(item.text);
    }

    auto totalWidth = [&]() {
        int width = 16;
        for (size_t i = 0; i < items.size(); i++) {
            width += hintPillWidth(items[i].button) + 4 + fontGetStringWidth(texts[i].c_str());
            if (i + 1 < items.size()) {
                width += 12;
            }
        }
        return width;
    };

    while (totalWidth() > maxWidth && !texts.empty() && texts[0].size() > 4) {
        std::string& text = texts[0];
        if (text.size() >= 3 && text.compare(text.size() - 3, 3, "...") == 0) {
            text.erase(text.size() - 4, 1);
        } else {
            text.erase(text.size() - 1);
            text += "...";
        }
    }

    gHintWidth = totalWidth();
    gHintImage.assign(gHintWidth * kHintHeight, hintColor(18, 20, 14));

    // Cornice: nero fuori, bronzo dentro, ombra in basso a destra.
    unsigned char black = hintColor(0, 0, 0);
    unsigned char bronze = hintColor(120, 104, 72);
    unsigned char shade = hintColor(60, 52, 36);
    for (int x = 0; x < gHintWidth; x++) {
        gHintImage[x] = black;
        gHintImage[(kHintHeight - 1) * gHintWidth + x] = black;
        if (x > 0 && x < gHintWidth - 1) {
            gHintImage[gHintWidth + x] = bronze;
            gHintImage[(kHintHeight - 2) * gHintWidth + x] = shade;
        }
    }
    for (int y = 0; y < kHintHeight; y++) {
        gHintImage[y * gHintWidth] = black;
        gHintImage[y * gHintWidth + gHintWidth - 1] = black;
        if (y > 0 && y < kHintHeight - 1) {
            gHintImage[y * gHintWidth + 1] = bronze;
            gHintImage[y * gHintWidth + gHintWidth - 2] = shade;
        }
    }

    int x = 8;
    int pillTop = (kHintHeight - kHintPillHeight) / 2;
    int textTop = (kHintHeight - fontGetLineHeight()) / 2;
    for (size_t i = 0; i < items.size(); i++) {
        hintDrawPill(gHintImage.data() + pillTop * gHintWidth + x, gHintWidth, items[i].button);
        x += hintPillWidth(items[i].button) + 4;
        fontSetCurrent(101);
        int textWidth = fontGetStringWidth(texts[i].c_str());
        fontDrawText(gHintImage.data() + textTop * gHintWidth + x, texts[i].c_str(), textWidth + 2, gHintWidth, _colorTable[992] | FONT_SHADOW);
        x += textWidth + 12;
    }

    fontSetCurrent(oldFont);
}

static void hintsRefresh(Rect rect)
{
    Rect iso;
    if (!isoWindowRect(&iso)) {
        return;
    }
    tileWindowRefreshRect(&rect, gElevation);
}

// Lo scorrimento della mappa sposta i pixel già disegnati, barra compresa:
// si ridisegna la zona attorno alla barra per non lasciarne una copia.
static void hintsAfterScroll()
{
    if (!gHintVisible) {
        return;
    }
    Rect area = gHintRect;
    area.left -= 80;
    area.top -= 60;
    area.right += 80;
    area.bottom += 60;
    tileWindowRefreshRect(&area, gElevation);
}

static void hintsTick(bool isInCombatMode)
{
    // Anche il gioco sposta la visuale per conto suo (inizio combattimento,
    // script): qualunque scorrimento trascina con sé i pixel della barra.
    static int lastCenter = -1;
    if (gCenterTile != lastCenter) {
        lastCenter = gCenterTile;
        hintsAfterScroll();
    }

    std::vector<HintItem> items;
    hintsCollect(items, isInCombatMode);

    // Se la barra in basso coprirebbe quello che stai guardando (bersaglio,
    // oggetto, esagono), va in alto.
    bool top = false;
    Rect visible;
    if (!items.empty() && isoVisibleRect(&visible)) {
        int x = -1;
        int y = -1;
        Object* watched = gTargetCurrent != nullptr ? gTargetCurrent : gFocus;
        if (watched != nullptr && watched != gDude) {
            objectAimPoint(watched, &x, &y);
        } else if (gCombatHex != -1) {
            hexCenter(gCombatHex, &x, &y);
        }
        int barTop = visible.bottom - visible.top + 1 - kHintHeight - 3;
        top = y != -1 && y - visible.top > barTop - 40;
    }

    std::string key = top ? "T|" : "B|";
    for (const HintItem& item : items) {
        key += item.button;
        key += '|';
        key += item.text;
        key += '|';
    }

    if (key == gHintKey) {
        return;
    }
    gHintKey = key;

    Rect old = gHintRect;
    bool wasVisible = gHintVisible;

    Rect iso;
    if (items.empty() || !isoVisibleRect(&iso)) {
        gHintVisible = false;
    } else {
        int isoWidth = iso.right - iso.left + 1;
        int isoHeight = iso.bottom - iso.top + 1;
        hintsBuild(items, isoWidth - 16);
        gHintRect.left = (isoWidth - gHintWidth) / 2;
        gHintRect.top = top ? 3 : isoHeight - kHintHeight - 3;
        gHintRect.right = gHintRect.left + gHintWidth - 1;
        gHintRect.bottom = gHintRect.top + kHintHeight - 1;
        gHintVisible = true;
    }

    if (wasVisible) {
        hintsRefresh(old);
    }
    if (gHintVisible) {
        hintsRefresh(gHintRect);
    }
}

void gamepadHintsRender(Rect* rect, unsigned char* buffer, int pitch)
{
    if (!gHintVisible || !inGameLoop()) {
        return;
    }

    Rect area = *rect;
    Rect bar = gHintRect;
    Rect clip;
    clip.left = std::max(area.left, bar.left);
    clip.top = std::max(area.top, bar.top);
    clip.right = std::min(area.right, bar.right);
    clip.bottom = std::min(area.bottom, bar.bottom);
    if (clip.left > clip.right || clip.top > clip.bottom) {
        return;
    }

    for (int y = clip.top; y <= clip.bottom; y++) {
        const unsigned char* src = gHintImage.data() + (y - bar.top) * gHintWidth + (clip.left - bar.left);
        memcpy(buffer + y * pitch + clip.left, src, clip.right - clip.left + 1);
    }
}

bool gamepadIsPadMode()
{
    return gController != nullptr && gPadMode;
}

void gamepadPointerUsed()
{
    if (gPadMode) {
        gPadMode = false;
    }
}

void gamepadGameTick(bool isInCombatMode)
{
    mobileSettingsLoad();
    gLastGameTick = SDL_GetTicks();

    if (gControllerJustConnected && gDude != nullptr) {
        gControllerJustConnected = false;
        char message[] = "Controller collegato.";
        displayMonitorAddMessage(message);
    }

    if (gController == nullptr || !mapIsActive()) {
        gPendingTargetStep = 0;
        gPendingCancelMode = false;
        gPendingUse = false;
        gPendingLook = false;
        return;
    }

    if (gEndTurnHeldSince != 0 && !gEndCombatSent && SDL_GetTicks() - gEndTurnHeldSince >= kEndCombatHoldMs) {
        gEndCombatSent = true;
        if (isInCombatMode) {
            inputInjectKey(SDL_SCANCODE_RETURN, true);
            inputInjectKey(SDL_SCANCODE_RETURN, false);
        }
    }

    // Fine combattimento: si torna all'esplorazione col controller, senza
    // esagono rosso né mirino rimasti appesi.
    static bool wasInCombat = false;
    if (wasInCombat && !isInCombatMode) {
        gCombatHex = -1;
        gCombatStickActive = false;
        gTargetCurrent = nullptr;
        gWarpPending = false;
        if (gLastPadInput != 0 && SDL_GetTicks() - gLastPadInput < 60000) {
            gPadMode = true;
        }
    }
    if (!wasInCombat && isInCombatMode && gPadMode) {
        // Inizio combattimento: via l'esagono e la selezione dell'esplorazione;
        // il cursore riparte da te in modalità movimento (poi, al tuo turno,
        // il mirino va da solo sul nemico più vicino).
        gCombatHex = -1;
        gCombatHexOrigin = -1;
        gCombatStickActive = false;
        gTargetCurrent = nullptr;
        // Il personaggio deve essere in vista (poteva essere in corsa verso
        // un esagono lontano, con la visuale ancora là).
        Rect view;
        int dudeX;
        int dudeY;
        hexCenter(gDude->tile, &dudeX, &dudeY);
        if (isoVisibleRect(&view)
            && (dudeX < view.left + 60 || dudeX > view.right - 60 || dudeY < view.top + 60 || dudeY > view.bottom - 50)) {
            _tile_scroll_to(gDude->tile, 2);
        }
        if (gPendingAttackTarget == nullptr) {
            gameMouseSetMode(GAME_MOUSE_MODE_MOVE);
            gWarpPending = true;
            hexCenter(gDude->tile, &gWarpX, &gWarpY);
        }
    }
    wasInCombat = isInCombatMode;

    static int lastMap = -1;
    static int lastElevation = -1;
    if (mapGetCurrentMap() != lastMap || gElevation != lastElevation) {
        lastMap = mapGetCurrentMap();
        lastElevation = gElevation;
        gCombatHex = -1;
        gCombatHexOrigin = -1;
        gTargetCurrent = nullptr;
        gPendingAttackTarget = nullptr;
        gFocusOutlined = false;
        focusClear(false);
    }

    bool pointerless = gPadMode && !isInCombatMode;

    // A con l'arma scarica: ricarica (vedi la barra dei comandi).
    if (gPendingReload) {
        gPendingReload = false;
        if (isInCombatMode && !gameUiIsDisabled()) {
            interfaceReloadActiveWeapon();
        }
    }

    if (gPendingCancelMode) {
        gPendingCancelMode = false;
        gTargetCurrent = nullptr;
        gameMouseSetCursor(MOUSE_CURSOR_NONE);
        gameMouseSetMode(pointerless ? GAME_MOUSE_MODE_ARROW : GAME_MOUSE_MODE_MOVE);
        gCombatHex = -1;
        if (pointerless && hexModeActive()) {
            focusSet(nullptr);
        }
    }

    if (!pointerless) {
        // In combattimento il gioco gestisce i contorni dei personaggi.
        if (gFocus != nullptr) {
            focusUpdateValidityAndClear();
        }
        if (gWeHidMapCursor) {
            gameMouseObjectsShow();
            gWeHidMapCursor = false;
        }
    } else if (hexModeActive()) {
        exploreHexTick();
        if (gFocusNameDue != 0 && SDL_GetTicks() >= gFocusNameDue) {
            gFocusNameDue = 0;
            if (gFocus != nullptr && gFocus != gDude) {
                _obj_look_at(gDude, gFocus);
            }
        }
        cameraStickTick();
    } else {
        if (!gMenuHold && gameMouseObjectsIsVisible()) {
            gameMouseObjectsHide();
            gWeHidMapCursor = true;
        }
        // Senza puntatore niente cursore "movimento" con l'esagono rosso.
        if (gameMouseGetMode() == GAME_MOUSE_MODE_MOVE || gameMouseGetMode() == GAME_MOUSE_MODE_CROSSHAIR) {
            gameMouseSetMode(GAME_MOUSE_MODE_ARROW);
        }
        if (!gMenuHold) {
            focusUpdate();
            focusParkCursor();
        }
        // Nome nella console ("You see: ..."), solo quando l'evidenziazione
        // resta ferma un attimo: niente elenco di nomi mentre cammini.
        if (gFocusNameDue != 0 && SDL_GetTicks() >= gFocusNameDue) {
            gFocusNameDue = 0;
            if (gFocus != nullptr && gFocus != gDude) {
                _obj_look_at(gDude, gFocus);
            }
        }
        cameraStickTick();
    }

    // Inizio del tuo turno: il mirino va da solo sul nemico più vicino tra
    // quelli che ce l'hanno con te (mai su chi non ti sta attaccando).
    static bool autoTargetDone = false;
    if (!isInCombatMode || gameUiIsDisabled()) {
        autoTargetDone = false;
    } else if (!autoTargetDone && gPadMode) {
        autoTargetDone = true;
        std::vector<Candidate> candidates;
        collectCandidates(candidates, true);
        // Il bersaglio del turno prima resta, se è ancora in piedi e in vista
        // (il mirino lo segue dove si è spostato).
        bool keep = false;
        for (const Candidate& candidate : candidates) {
            if (candidate.object == gTargetCurrent) {
                keep = true;
                break;
            }
        }
        if (!keep) {
            gTargetCurrent = nullptr;
        }
        if (keep && gPendingAttackTarget == nullptr) {
            gCombatHex = -1;
            gWarpPending = true;
            objectAimPoint(gTargetCurrent, &gWarpX, &gWarpY);
            gameMouseSetMode(GAME_MOUSE_MODE_CROSSHAIR);
        } else if (gPendingAttackTarget == nullptr && gCombatHex == -1) {
            Object* nearest = nullptr;
            int nearestDistance = INT_MAX;
            for (const Candidate& candidate : candidates) {
                Object* critter = candidate.object;
                bool hostile = (critter->data.critter.combat.maneuver & CRITTER_MANEUVER_ENGAGING) != 0
                    || critter->data.critter.combat.whoHitMe == gDude;
                int distance = tileDistanceBetween(gDude->tile, critter->tile);
                if (hostile && distance < nearestDistance) {
                    nearestDistance = distance;
                    nearest = critter;
                }
            }
            if (nearest != nullptr) {
                gTargetCurrent = nearest;
                gWarpPending = true;
                objectAimPoint(nearest, &gWarpX, &gWarpY);
                gameMouseSetMode(GAME_MOUSE_MODE_CROSSHAIR);
            }
        }
    }

    if (gPendingAttackTarget != nullptr) {
        if (SDL_GetTicks() > gPendingAttackUntil) {
            gPendingAttackTarget = nullptr;
        } else if (isInCombatMode && !gameUiIsDisabled()) {
            std::vector<Candidate> candidates;
            collectCandidates(candidates, true);
            for (const Candidate& candidate : candidates) {
                if (candidate.object == gPendingAttackTarget) {
                    gTargetCurrent = candidate.object;
                    gCombatHex = -1;
                    gWarpPending = true;
                    objectAimPoint(gTargetCurrent, &gWarpX, &gWarpY);
                    gameMouseSetMode(GAME_MOUSE_MODE_CROSSHAIR);
                    break;
                }
            }
            gPendingAttackTarget = nullptr;
        }
    }

    if (gPendingTargetStep != 0) {
        if (pointerless) {
            gTargetCurrent = gFocus;
        }
        cycleTarget(gPendingTargetStep, isInCombatMode);
        if (pointerless) {
            focusSet(gTargetCurrent);
            gFocusManual = gFocus != nullptr;
            if (gFocus != nullptr && hexModeActive()) {
                // L'esagono salta sull'oggetto scelto: lo stick riparte da lì.
                gCombatHex = gFocus->tile;
                gCombatHexOrigin = gDude->tile;
            }
        }
        gPendingTargetStep = 0;
    }

    if (gPendingUse) {
        gPendingUse = false;
        if (pointerless) {
            if (gFocus == nullptr && hexModeActive()) {
                exploreHexWalk();
            } else {
                focusUse();
            }
        }
    }

    if (gPendingLook) {
        gPendingLook = false;
        if (pointerless) {
            focusLook();
        }
    }

    if (isInCombatMode && gPadMode) {
        combatStickTick();
        cameraStickTick();
    }

    if (!isInCombatMode && gMobile.stickMovement && !hexModeActive() && !gameUiIsDisabled()) {
        stickMovementTick();
        if (SDL_GetTicks() < gFollowUntil) {
            if (animationIsBusy(gDude)) {
                gFollowUntil = SDL_GetTicks() + 300;
            }
            followCamera();
        }
    } else {
        gStickWasMoving = false;
        gStickLastTarget = -1;
    }

    hintsTick(isInCombatMode);
}

} // namespace fallout
