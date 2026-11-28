import Definitions.Def_JSA2020_Components
import Definitions.Def_LinuxRV_TransitionTable

/-! Sub-model compositions, unified seven-automaton synchronous product, 18-state canonical
kernel-state model, SEFM 2019 monitor enumerations, and published kernel trace excerpts
(JSA 2020 Figures 28–29 and Figure 32). -/

namespace JSA2020

open RamadgeWonham.Shared CassandrasLafortune

/-! ### Wakeup and need-resched sub-model (`G06`, `S17`, `S02`) -/

abbrev WakeupControls := PreemptState × IRQState

/-- Phase of `S02` determined by the two control automata `G06` and `S17`. -/
def wakeupPhaseOf : WakeupControls → Phase
  | (.enabled, .noIRQ) => .enabled
  | (.enabled, _) | (_, .noIRQ) => .oneDisabled
  | (_, _) => .disabled

/-- Number of disabled wakeup controls: preemption off and/or IRQs masked/handling. -/
def wakeupDisabledCount (q : WakeupControls) : Nat :=
  (if q.1 ≠ .enabled then 1 else 0) + (if q.2 ≠ .noIRQ then 1 else 0)

theorem wakeupPhaseOf_eq_disabledCount (q : WakeupControls) :
    wakeupPhaseOf q = match wakeupDisabledCount q with
      | 0 => .enabled
      | 1 => .oneDisabled
      | _ => .disabled := by
  rcases q with ⟨p, i⟩
  cases p <;> cases i <;> rfl

def withWakeupPhase (q : WakeupControls) : WakeupControls × Phase :=
  (q, wakeupPhaseOf q)

/-- Consistency invariant: the S02 phase equals the number of disabled controls. -/
def wakeupConsistent (q : WakeupControls × Phase) : Prop :=
  q.2 = wakeupPhaseOf q.1

def wakeupLift (q : WakeupControls) : WakeupControls × Phase := withWakeupPhase q

def wakeupProj (q : WakeupControls × Phase) : WakeupControls := q.1

theorem wakeupProj_lift (q : WakeupControls) : wakeupProj (wakeupLift q) = q := rfl

theorem wakeupLift_proj_of_consistent {q : WakeupControls × Phase}
    (h : wakeupConsistent q) : wakeupLift (wakeupProj q) = q := by
  rcases q with ⟨c, s⟩
  simp only [wakeupLift, wakeupProj, withWakeupPhase, wakeupConsistent] at h ⊢
  exact congrArg (Prod.mk c) h.symm

theorem wakeupConsistent_lift (q : WakeupControls) : wakeupConsistent (wakeupLift q) := rfl

/-- Guard for wakeup/need-resched notifications: preemption off and IRQs off/handling. -/
def wakeupGuard (q : WakeupControls) : Prop :=
  q.1 ≠ .enabled ∧ q.2 ≠ .noIRQ

instance wakeupGuardDecidable (q : WakeupControls) : Decidable (wakeupGuard q) :=
  inferInstanceAs (Decidable (_ ∧ _))

def wakeupControlStep (e : WakeupSpecEvent) (q : WakeupControls) : Option WakeupControls :=
  match e with
  | .preempt a => (g06.δ a q.1).map fun p => (p, q.2)
  | .irq a => (s17.δ a q.2).map fun i => (q.1, i)
  | .notify _ => some q

/-- Synchronous product of `G06`, `S17`, and `S02` (ISORC Figs. 10–12 / JSA Figs. 17–19). -/
def wakeupProduct : Generator WakeupSpecEvent where
  Q := WakeupControls × Phase
  q0 := ((g06.q0, s17.q0), s02.q0)
  Qm := {q | q.1.1 ∈ g06.Qm ∧ q.1.2 ∈ s17.Qm ∧ q.2 ∈ s02.Qm}
  δ e q := do
    let controls ← wakeupControlStep e q.1
    let phase ← s02.δ e q.2
    pure (controls, phase)

/-- Direct 9-state wakeup specification checking `G06` and `S17` directly on notifications. -/
def wakeupGuarded : Generator WakeupSpecEvent where
  Q := WakeupControls
  q0 := (g06.q0, s17.q0)
  Qm := {q | q.1 ∈ g06.Qm ∧ q.2 ∈ s17.Qm}
  δ e q := match e with
    | .notify _ => if q.1 ≠ .enabled ∧ q.2 ≠ .noIRQ then some q else none
    | .preempt _ | .irq _ => wakeupControlStep e q

/-- Reachability in the full wakeup product. -/
def wakeupReachable (q : WakeupControls × Phase) : Prop :=
  ∃ w, wakeupProduct.run w = some q

/-- Executable trace in the full wakeup product. -/
def wakeupExec (w : List WakeupSpecEvent) : Prop :=
  w ∈ wakeupProduct.L

instance (w : List WakeupSpecEvent) : Decidable (wakeupExec w) :=
  inferInstanceAs (Decidable ((wakeupProduct.run w).isSome = true))

/-- Executable trace in the guarded wakeup monitor. -/
def wakeupGuardedExec (w : List WakeupSpecEvent) : Prop :=
  w ∈ wakeupGuarded.L

instance (w : List WakeupSpecEvent) : Decidable (wakeupGuardedExec w) :=
  inferInstanceAs (Decidable ((wakeupGuarded.run w).isSome = true))

/-- The nine consistent wakeup product states. -/
def wakeupReachableList : List (WakeupControls × Phase) :=
  [ ((PreemptState.enabled, IRQState.noIRQ), Phase.enabled)
  , ((PreemptState.enabled, IRQState.masked), Phase.oneDisabled)
  , ((PreemptState.enabled, IRQState.handling), Phase.oneDisabled)
  , ((PreemptState.disabled, IRQState.noIRQ), Phase.oneDisabled)
  , ((PreemptState.disabled, IRQState.masked), Phase.disabled)
  , ((PreemptState.disabled, IRQState.handling), Phase.disabled)
  , ((PreemptState.scheduling, IRQState.noIRQ), Phase.oneDisabled)
  , ((PreemptState.scheduling, IRQState.masked), Phase.disabled)
  , ((PreemptState.scheduling, IRQState.handling), Phase.disabled) ]

theorem wakeupReachableList_length : wakeupReachableList.length = 9 := rfl

/-- Reduced wakeup product without `S17`: `G06 || S02` over the same 10-event alphabet. -/
def wakeupWithoutS17 : Generator WakeupSpecEvent where
  Q := PreemptState × Phase
  q0 := (.enabled, .enabled)
  Qm := {(.enabled, .enabled)}
  δ e q := do
    let p ← match e with
      | .preempt a => g06.δ a q.1
      | .irq _ | .notify _ => some q.1
    let phase ← s02.δ e q.2
    pure (p, phase)

/-- Reduced wakeup product without `G06`: `S17 || S02` over the same 10-event alphabet. -/
def wakeupWithoutG06 : Generator WakeupSpecEvent where
  Q := IRQState × Phase
  q0 := (.noIRQ, .enabled)
  Qm := {(.noIRQ, .enabled)}
  δ e q := do
    let i ← match e with
      | .irq a => s17.δ a q.1
      | .preempt _ | .notify _ => some q.1
    let phase ← s02.δ e q.2
    pure (i, phase)

def wakeupExecWithoutS17 (w : List WakeupSpecEvent) : Prop := w ∈ wakeupWithoutS17.L

instance (w : List WakeupSpecEvent) : Decidable (wakeupExecWithoutS17 w) :=
  inferInstanceAs (Decidable ((wakeupWithoutS17.run w).isSome = true))

def wakeupExecWithoutG06 (w : List WakeupSpecEvent) : Prop := w ∈ wakeupWithoutG06.L

instance (w : List WakeupSpecEvent) : Decidable (wakeupExecWithoutG06 w) :=
  inferInstanceAs (Decidable ((wakeupWithoutG06.run w).isSome = true))

/-! ### Context-switch sub-models (`S07`, `S08`, and composition with `G06`, `S17`) -/

abbrev SwitchTraceEvent := CassandrasLafortune.Event SwitchControlEvent SchedulerEvent SwitchEvent

/-- Binary parallel composition of `S07` and `S08` (JSA Figs. 21–22). -/
def switchProduct : Generator SwitchTraceEvent :=
  parallel s07 s08

/-- Phase of `S07` determined by `G06` (`scheduling`) and `S17` (`masked`). -/
def switchPhaseOf : WakeupControls → Phase
  | (.scheduling, .masked) => .disabled
  | (.scheduling, _) | (_, .masked) => .oneDisabled
  | (_, _) => .enabled

abbrev SwitchFullState := PreemptState × IRQState × Phase × SchedContext

/-- Synchronous composition of `G06`, `S17`, `S07`, and `S08` over `SyncEvent`.
Adding `G06` and `S17` enforces strict pairing of `preempt_disable_sched` and
`local_irq_disable` without external history assumptions. -/
def switchWithControls : Generator SyncEvent where
  Q := SwitchFullState
  q0 := (g06.q0, s17.q0, s07.q0, s08.q0)
  Qm := {q | q.1 ∈ g06.Qm ∧ q.2.1 ∈ s17.Qm ∧ q.2.2.1 ∈ s07.Qm ∧ q.2.2.2 ∈ s08.Qm}
  δ e q := do
    let p ← localStep g06 q.1 (g06View e)
    let i ← localStep s17 q.2.1 (s17View e)
    let ph ← localStep s07 q.2.2.1 (s07View e)
    let c ← localStep s08 q.2.2.2 (s08View e)
    pure (p, i, ph, c)

/-! ### IRQ-locking sub-model (`S12`, `S22`) -/

abbrev IRQLockTraceEvent := CassandrasLafortune.Event S12SchedulingEvent Empty IRQSharedEvent

/-- Binary parallel composition of `S12` and `S22` (JSA Figs. 33–34). -/
def irqLockProduct : Generator IRQLockTraceEvent :=
  parallel s12 s22

/-- Whether an `S17` state corresponds to hardware IRQ handling (`S12 = true`). -/
def irqActive : IRQState → Bool
  | .handling => true
  | .noIRQ | .masked => false

/-- Whether an `S17` state has IRQs software-masked or being handled (`S22 = true`). -/
def irqMaskedOrActive : IRQState → Bool
  | .noIRQ => false
  | .masked | .handling => true

/-! ### Unified seven-automaton synchronous model and 18-state canonical model -/

/-- Product state of `(G06, S17, S02, S07, S08, S12, S22)` (`3 × 3 × 3 × 3 × 2 × 2 × 2 = 648`). -/
abbrev SyncModelState :=
  PreemptState × IRQState × Phase × Phase × SchedContext × Bool × Bool

/-- Synchronous parallel composition of all seven published automata (`G06`, `S17`, `S02`,
`S07`, `S08`, `S12`, `S22`) over the 32-event alphabet `SyncEvent`. -/
def publishedSyncModel : Generator SyncEvent where
  Q := SyncModelState
  q0 := (g06.q0, s17.q0, s02.q0, s07.q0, s08.q0, s12.q0, s22.q0)
  Qm := {q | q.1 ∈ g06.Qm ∧ q.2.1 ∈ s17.Qm ∧ q.2.2.1 ∈ s02.Qm ∧ q.2.2.2.1 ∈ s07.Qm ∧
    q.2.2.2.2.1 ∈ s08.Qm ∧ q.2.2.2.2.2.1 ∈ s12.Qm ∧ q.2.2.2.2.2.2 ∈ s22.Qm}
  δ e q := do
    let p ← localStep g06 q.1 (g06View e)
    let i ← localStep s17 q.2.1 (s17View e)
    let p02 ← localStep s02 q.2.2.1 (s02View e)
    let p07 ← localStep s07 q.2.2.2.1 (s07View e)
    let c ← localStep s08 q.2.2.2.2.1 (s08View e)
    let a12 ← localStep s12 q.2.2.2.2.2.1 (s12View e)
    let m22 ← localStep s22 q.2.2.2.2.2.2 (s22View e)
    pure (p, i, p02, p07, c, a12, m22)

/-- True when at least one component participating in `e` has no transition from its coordinate. -/
def componentBlocked (q : SyncModelState) (e : SyncEvent) : Prop :=
  (∃ a, g06View e = some a ∧ g06.δ a q.1 = none) ∨
  (∃ a, s17View e = some a ∧ s17.δ a q.2.1 = none) ∨
  (∃ a, s02View e = some a ∧ s02.δ a q.2.2.1 = none) ∨
  (∃ a, s07View e = some a ∧ s07.δ a q.2.2.2.1 = none) ∨
  (∃ a, s08View e = some a ∧ s08.δ a q.2.2.2.2.1 = none) ∨
  (∃ a, s12View e = some a ∧ s12.δ a q.2.2.2.2.2.1 = none) ∨
  (∃ a, s22View e = some a ∧ s22.δ a q.2.2.2.2.2.2 = none)

/-- Independent control and context coordinates (`3 × 3 × 2 = 18` states). -/
abbrev CoreState := PreemptState × IRQState × SchedContext

/-- Unique embedding of the 18 reachable core states into the 648-state product. -/
def embedCore (s : CoreState) : SyncModelState :=
  let (p, i, c) := s
  (p, i, wakeupPhaseOf (p, i), switchPhaseOf (p, i), c, irqActive i, irqMaskedOrActive i)

/-- Direct 18-state canonical model capturing all four synchronization laws over `CoreState`. -/
def canonicalSyncModel : Generator SyncEvent where
  Q := CoreState
  q0 := (.enabled, .noIRQ, .thread)
  Qm := {(.enabled, .noIRQ, .thread)}
  δ e s :=
    let (p, i, c) := s
    match e with
    | .preempt .disable =>
        if p = .enabled then some (.disabled, i, c) else none
    | .preempt .enable =>
        if p = .disabled then some (.enabled, i, c) else none
    | .preempt .disableSched =>
        if p = .enabled then some (.scheduling, i, c) else none
    | .preempt .enableSched =>
        if p = .scheduling ∧ i ≠ .handling then some (.enabled, i, c) else none
    | .irq .localDisable =>
        if i = .noIRQ then some (p, .masked, c) else none
    | .irq .localEnable =>
        if i = .masked then some (p, .noIRQ, c) else none
    | .irq .hwDisable =>
        if i = .noIRQ then some (p, .handling, c) else none
    | .irq .hwEnable =>
        if i = .handling then some (p, .noIRQ, c) else none
    | .notify _ =>
        if p ≠ .enabled ∧ i ≠ .noIRQ then some (p, i, c) else none
    | .scheduler .scheduleEntry =>
        if c = .thread ∧ i ≠ .handling then some (p, i, .scheduler) else none
    | .scheduler .scheduleExit =>
        if c = .scheduler ∧ i ≠ .handling then some (p, i, .thread) else none
    | .switch _ =>
        if p = .scheduling ∧ i = .masked ∧ c = .scheduler then some (p, i, c) else none
    | .taskState _ =>
        if i ≠ .handling then some (p, i, c) else none
    | .lock _ _ =>
        if i = .noIRQ then some (p, i, c) else none

/-! ### Finite enumerations for the SEFM 2019 table-driven monitor -/

/-- Bijection between the 18 reachable core states and `Fin 18`. -/
def coreStateEnum : CoreState ≃ Fin 18 where
  toFun
    | (.enabled, .noIRQ, .thread) => 0
    | (.enabled, .noIRQ, .scheduler) => 1
    | (.enabled, .masked, .thread) => 2
    | (.enabled, .masked, .scheduler) => 3
    | (.enabled, .handling, .thread) => 4
    | (.enabled, .handling, .scheduler) => 5
    | (.disabled, .noIRQ, .thread) => 6
    | (.disabled, .noIRQ, .scheduler) => 7
    | (.disabled, .masked, .thread) => 8
    | (.disabled, .masked, .scheduler) => 9
    | (.disabled, .handling, .thread) => 10
    | (.disabled, .handling, .scheduler) => 11
    | (.scheduling, .noIRQ, .thread) => 12
    | (.scheduling, .noIRQ, .scheduler) => 13
    | (.scheduling, .masked, .thread) => 14
    | (.scheduling, .masked, .scheduler) => 15
    | (.scheduling, .handling, .thread) => 16
    | (.scheduling, .handling, .scheduler) => 17
  invFun k := match k.val with
    | 0 => (.enabled, .noIRQ, .thread)
    | 1 => (.enabled, .noIRQ, .scheduler)
    | 2 => (.enabled, .masked, .thread)
    | 3 => (.enabled, .masked, .scheduler)
    | 4 => (.enabled, .handling, .thread)
    | 5 => (.enabled, .handling, .scheduler)
    | 6 => (.disabled, .noIRQ, .thread)
    | 7 => (.disabled, .noIRQ, .scheduler)
    | 8 => (.disabled, .masked, .thread)
    | 9 => (.disabled, .masked, .scheduler)
    | 10 => (.disabled, .handling, .thread)
    | 11 => (.disabled, .handling, .scheduler)
    | 12 => (.scheduling, .noIRQ, .thread)
    | 13 => (.scheduling, .noIRQ, .scheduler)
    | 14 => (.scheduling, .masked, .thread)
    | 15 => (.scheduling, .masked, .scheduler)
    | 16 => (.scheduling, .handling, .thread)
    | _ => (.scheduling, .handling, .scheduler)
  left_inv
    | (p, i, c) => by cases p <;> cases i <;> cases c <;> rfl
  right_inv := by
    rintro ⟨k, hk⟩
    match k, hk with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _
    | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _
    | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ => rfl
    | k + 18, hk => omega

/-- Bijection between the 32 unified synchronization events and `Fin 32`. -/
def syncEventEnum : SyncEvent ≃ Fin 32 where
  toFun
    | .preempt .disable => 0
    | .preempt .enable => 1
    | .preempt .disableSched => 2
    | .preempt .enableSched => 3
    | .irq .localDisable => 4
    | .irq .localEnable => 5
    | .irq .hwDisable => 6
    | .irq .hwEnable => 7
    | .notify .waking => 8
    | .notify .needResched => 9
    | .scheduler .scheduleEntry => 10
    | .scheduler .scheduleExit => 11
    | .switch .switchIn => 12
    | .switch .switchInOther => 13
    | .switch .switchSuspend => 14
    | .switch .switchPreempt => 15
    | .switch .switchOutOther => 16
    | .switch .switchBlocking => 17
    | .taskState .setRunnable => 18
    | .taskState .setSleepable => 19
    | .lock .mutex .lock => 20
    | .lock .mutex .blocked => 21
    | .lock .mutex .acquired => 22
    | .lock .mutex .abandon => 23
    | .lock .read .lock => 24
    | .lock .read .blocked => 25
    | .lock .read .acquired => 26
    | .lock .read .abandon => 27
    | .lock .write .lock => 28
    | .lock .write .blocked => 29
    | .lock .write .acquired => 30
    | .lock .write .abandon => 31
  invFun k := match k.val with
    | 0 => .preempt .disable
    | 1 => .preempt .enable
    | 2 => .preempt .disableSched
    | 3 => .preempt .enableSched
    | 4 => .irq .localDisable
    | 5 => .irq .localEnable
    | 6 => .irq .hwDisable
    | 7 => .irq .hwEnable
    | 8 => .notify .waking
    | 9 => .notify .needResched
    | 10 => .scheduler .scheduleEntry
    | 11 => .scheduler .scheduleExit
    | 12 => .switch .switchIn
    | 13 => .switch .switchInOther
    | 14 => .switch .switchSuspend
    | 15 => .switch .switchPreempt
    | 16 => .switch .switchOutOther
    | 17 => .switch .switchBlocking
    | 18 => .taskState .setRunnable
    | 19 => .taskState .setSleepable
    | 20 => .lock .mutex .lock
    | 21 => .lock .mutex .blocked
    | 22 => .lock .mutex .acquired
    | 23 => .lock .mutex .abandon
    | 24 => .lock .read .lock
    | 25 => .lock .read .blocked
    | 26 => .lock .read .acquired
    | 27 => .lock .read .abandon
    | 28 => .lock .write .lock
    | 29 => .lock .write .blocked
    | 30 => .lock .write .acquired
    | _ => .lock .write .abandon
  left_inv e := by
    cases e with
    | preempt a => cases a <;> rfl
    | irq a => cases a <;> rfl
    | notify a => cases a <;> rfl
    | scheduler a => cases a <;> rfl
    | switch a => cases a <;> rfl
    | taskState a => cases a <;> rfl
    | lock k a => cases k <;> cases a <;> rfl
  right_inv := by
    rintro ⟨k, hk⟩
    match k, hk with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
    | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _
    | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _
    | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _ => rfl
    | k + 32, hk => omega

/-- The SEFM 2019 table-driven monitor compiled from the 18-state canonical model. -/
def syncMonitor (trace : List SyncEvent) : Except (Nat × Fin 18 × Fin 32) (Fin 18) :=
  LinuxRV.monitor canonicalSyncModel coreStateEnum syncEventEnum trace

/-! ### Published kernel trace excerpts (JSA 2020 §§5.2.2–5.2.3) -/

/-- JSA 2020, Figure 29 (§5.2.2): three recorded events reproducing the `sched_waking`
rejection reported in Figure 28 after returning to the initial state. -/
def figure29Trace : List SyncEvent :=
  [ .preempt .disable
  , .preempt .enable
  , .notify .waking ]

/-- JSA 2020, Figure 32 (§5.2.3): timer-IRQ watchdog trace excerpt from Linux `4.19-rt`,
including its leading `preempt_disable` and final invalid `mutex_lock` in IRQ context. -/
def figure32Trace : List SyncEvent :=
  [ .preempt .disable
  , .irq .localEnable
  , .irq .hwDisable
  , .lock .mutex .lock ]

/-- Full trace from `q0` reaching the software-masked starting state of Figure 32 before
replaying `figure32Trace`. -/
def figure32RootedTrace : List SyncEvent :=
  .irq .localDisable :: figure32Trace

end JSA2020
