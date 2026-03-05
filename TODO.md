# HYDROGEN TODO

## Status: 13 PureScript errors, 41 tasks remaining

---

## PureScript Build Errors (13)

These must be fixed before the build compiles:

| ID | File | Error |
|----|------|-------|
| ps-err-1 | Hydrogen.Chart.PieChart | MissingFFIModule |
| ps-err-2 | Hydrogen.GPU.WebGPU.Device | MissingFFIModule (replace with Schema types) |
| ps-err-3 | Hydrogen.HTML.Renderer | MissingFFIModule |
| ps-err-4 | Hydrogen.Head.Meta | MissingFFIModule |
| ps-err-5 | Hydrogen.Motion.Gesture | UnknownImport: PointerEvent |
| ps-err-6 | Hydrogen.Offline.ServiceWorker | MissingFFIModule |
| ps-err-7 | Hydrogen.Playwright | MissingFFIModule |
| ps-err-8 | Hydrogen.Target.DOM | MissingFFIModule |
| ps-err-9 | Hydrogen.UI.Drag.DocumentEvents | MissingFFIModule |
| ps-err-10 | Hydrogen.UI.FocusTrap | MissingFFIModule |
| ps-err-11 | Hydrogen.Util.Keyboard | UnknownName: >>> operator |
| ps-err-12 | Hydrogen.Util.LocalStorage | UnknownImport: sessionCookieOptions |
| ps-err-13 | Hydrogen.Util.MediaQuery | UnknownImportDataConstructor: PortraitOrientation |

---

## 12 Button Types with Graded Co-Effects

From `Hydrogen.Schema.Reactive.ButtonSemantics.ButtonPurpose`:

| ID | ButtonPurpose | Description | Co-Effect |
|----|---------------|-------------|-----------|
| btn-1 | ActionButton | General action ("Save", "Continue", "Apply") | CanClick |
| btn-2 | FormSubmit | Form submission (HTML submit) | CanClick, NeedsForm |
| btn-3 | FormReset | Form reset (HTML reset) | CanClick, NeedsForm |
| btn-4 | NavigationButton | Navigation trigger (changes route) | CanClick, NeedsRouter |
| btn-5 | MediaControl | Play/Pause/Stop/Skip (19 MediaActions) | CanClick, NeedsMedia |
| btn-6 | ToggleControl | On/Off toggle (Pressed/Unpressed/Mixed) | CanClick, HasState |
| btn-7 | MenuTrigger | Opens dropdown/menu | CanClick, HasPopup |
| btn-8 | DialogTrigger | Opens modal/dialog | CanClick, HasPopup |
| btn-9 | DisclosureTrigger | Expands/collapses (accordion) | CanClick, HasState |
| btn-10 | DangerAction | Destructive, requires confirmation | CanClick, NeedsConfirm |
| btn-11 | IconAction | Icon-only (edit/delete/copy/share) | CanClick |
| btn-12 | FloatingAction | FAB - floating action button | CanClick |

### MediaControl Actions (19)

PlayAction, PauseAction, StopAction, SkipForwardAction, SkipBackwardAction,
FastForwardAction, RewindAction, NextTrackAction, PreviousTrackAction,
MuteAction, UnmuteAction, VolumeUpAction, VolumeDownAction, FullscreenAction,
ExitFullscreenAction, PictureInPictureAction, ClosedCaptionsAction,
SettingsAction, RecordAction, LiveAction

---

## Lean4 Proofs: Diffusion Sigma Schedule

Real formulas from `Hydrogen.GPU.Diffusion`:

| ID | Invariant | Formula |
|----|-----------|---------|
| lean-sigma-1 | Karras monotonicity | σ(i) = (σ_max^(1/ρ) + t*(σ_min^(1/ρ) - σ_max^(1/ρ)))^ρ |
| lean-sigma-2 | Exponential monotonicity | σ(i) = σ_max * (σ_min/σ_max)^t |
| lean-sigma-3 | Beta57 monotonicity | res4lyf schedule formula |
| lean-sigma-4 | Bounds | ∀i. sigmaMin ≤ σ(i) ≤ sigmaMax |
| lean-sigma-5 | Termination | σ(n-1) = sigmaMin |
| lean-sigma-6 | Denoise step | sigmaNext < sigma |

Default values (from Config.purs):
- sigmaMin: 0.0292
- sigmaMax: 14.6146
- rho: 7.0
- steps: 25

---

## Lean4 Proofs: Co-Effect Algebra

| ID | Invariant | Description |
|----|-----------|-------------|
| lean-coeff-1 | ResourceGrade AddCommMonoid | 0+r=r, r+0=r, (r+s)+t=r+(s+t), r+s=s+r |
| lean-coeff-2 | Handle lifetime | no use-after-free, no double-free |
| lean-coeff-3 | Memory conservation | freed ≤ allocated |

---

## Graded Monad Integration

Using Orchard's effect-monad library (`haskell/effect-monad/`):

| ID | Task |
|----|------|
| graded-1 | Wire effect-monad to Hydrogen.Effect.Grade |
| graded-2 | Implement GPU co-effect tracking in Schema.GPU.Effect |
| graded-3 | Implement graded bind: GPU r α → (α → GPU s β) → GPU (r+s) β |

---

## FFI Removal (Zero JS)

Files that still have `foreign import`:

| ID | File | Action |
|----|------|--------|
| ffi-remove-1 | Hydrogen.Effect.Grade | Replace with pure PureScript |
| ffi-remove-2 | Hydrogen.UI.AriaHider | Replace with pure PureScript |
| ffi-remove-3 | Hydrogen.UI.Dialog | Replace with pure PureScript |

JS reference files are in `DEPRECATED_JS_REFERENCE/` - do NOT use these.

---

## Completed Work

### Schema.GPU Modules (Pure PureScript, 0 warnings)
- Schema.GPU.Limits (6 submodules)
- Schema.GPU.Buffer
- Schema.GPU.Texture + Texture.Format
- Schema.GPU.Sampler
- Schema.GPU.Handle
- Schema.GPU.Command
- Schema.GPU.Effect (CoEffectMemory, CoEffectBandwidth)
- Schema.GPU.purs (rollup)
- Schema.GPU.Extended.purs

### Lean4 Setup
- Toolchain: v4.28.0
- Mathlib: v4.28.0
- Foundry/GPU.lean (WIP - has compilation errors)

### Haskell
- effect-monad (Orchard's graded monad library) already in `haskell/effect-monad/`

---

## Architecture

```
PureScript (Hydrogen)     Lean4 (Proofs)           Haskell (Backend)
─────────────────────     ──────────────           ─────────────────
Schema.GPU.*              Foundry.GPU              effect-monad
  ├─ Bounded types          ├─ Sigma proofs          ├─ Effect class
  ├─ Co-effect ADTs         ├─ Monoid proofs         ├─ Coeffect class
  └─ Pure data              └─ Lifetime proofs       └─ Graded bind

                    ↓ verified ↓
                    
              Rust Runtime (WASM)
              ───────────────────
              Interprets Schema → GPU commands
```

---

## The Rule

**ZERO JS FFI in UI components.**

Everything is pure Element composition. FFI only at true system boundaries.
