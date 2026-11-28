import LinuxRV.Switch

/-!
The wakeup and need-resched conditions from de Oliveira, de Oliveira and Cucinotta.
ISORC 2019 Figures 10–12 and JSA 2020 Figures 17–19 give the same three automata.
The hardware IRQ labels describe entry to and return from an IRQ handler in the paper.
-/

namespace LinuxRV.Wakeup

open CassandrasLafortune RamadgeWonham.Shared

inductive PreemptEvent where
  | disable | enable | disableSched | enableSched
  deriving DecidableEq

inductive IRQEvent where
  | localDisable | localEnable | hwDisable | hwEnable
  deriving DecidableEq

inductive Notification where
  | waking | needResched
  deriving DecidableEq

inductive Event where
  | preempt (e : PreemptEvent)
  | irq (e : IRQEvent)
  | notify (e : Notification)
  deriving DecidableEq

inductive PreemptState where
  | enabled | disabled | scheduling
  deriving DecidableEq

inductive IRQState where
  | noIRQ | masked | handling
  deriving DecidableEq

/-- G06 distinguishes disabling preemption in a thread from doing so for a scheduler call. -/
def g06 : Generator PreemptEvent where
  Q := PreemptState
  q0 := .enabled
  Qm := {.enabled}
  δ e p := match p, e with
    | .enabled, .disable => some .disabled
    | .disabled, .enable => some .enabled
    | .enabled, .disableSched => some .scheduling
    | .scheduling, .enableSched => some .enabled
    | _, _ => none

/-- S17 permits either software masking or hardware IRQ handling from `noIRQ`. -/
def s17 : Generator IRQEvent where
  Q := IRQState
  q0 := .noIRQ
  Qm := {.noIRQ}
  δ e i := match i, e with
    | .noIRQ, .localDisable => some .masked
    | .masked, .localEnable => some .noIRQ
    | .noIRQ, .hwDisable => some .handling
    | .handling, .hwEnable => some .noIRQ
    | _, _ => none

abbrev Phase := Switch.Phase

private def disablePhase : Phase → Option Phase
  | .enabled => some .oneDisabled
  | .oneDisabled => some .disabled
  | .disabled => none

private def enablePhase : Phase → Option Phase
  | .enabled => none
  | .oneDisabled => some .enabled
  | .disabled => some .oneDisabled

/-- S02 counts disables without distinguishing their sources. Both notifications loop at 2. -/
def s02 : Generator Event where
  Q := Phase
  q0 := .enabled
  Qm := {.enabled}
  δ e q := match e with
    | .preempt .disable | .preempt .disableSched | .irq .localDisable | .irq .hwDisable =>
        disablePhase q
    | .preempt .enable | .preempt .enableSched | .irq .localEnable | .irq .hwEnable =>
        enablePhase q
    | .notify _ => if q = .disabled then some q else none

abbrev Controls := PreemptState × IRQState

private def controlStep (e : Event) (q : Controls) : Option Controls :=
  match e with
  | .preempt a => (g06.δ a q.1).map fun p => (p, q.2)
  | .irq a => (s17.δ a q.2).map fun i => (q.1, i)
  | .notify _ => some q

/-- The synchronous product of S02, G06 and S17. Only S02 consumes notifications. -/
def published : Generator Event where
  Q := Controls × Phase
  q0 := ((g06.q0, s17.q0), s02.q0)
  Qm := {q | q.1.1 ∈ g06.Qm ∧ q.1.2 ∈ s17.Qm ∧ q.2 ∈ s02.Qm}
  δ e q := do
    let controls ← controlStep e q.1
    let phase ← s02.δ e q.2
    pure (controls, phase)

/-- Direct formulation of the requirement in terms of the two control states. -/
def guarded : Generator Event where
  Q := Controls
  q0 := (g06.q0, s17.q0)
  Qm := {q | q.1 ∈ g06.Qm ∧ q.2 ∈ s17.Qm}
  δ e q := match e with
    | .notify _ => if q.1 ≠ .enabled ∧ q.2 ≠ .noIRQ then some q else none
    | .preempt _ | .irq _ => controlStep e q

/-- The phase of S02 counts the number of disabled controls. -/
def phaseOf (q : Controls) : Phase :=
  match q with
  | (.enabled, .noIRQ) => .enabled
  | (.enabled, _) | (_, .noIRQ) => .oneDisabled
  | (_, _) => .disabled

def withPhase (q : Controls) : Controls × Phase := (q, phaseOf q)

private theorem step_agrees (q : Controls) (e : Event) :
    published.δ e (withPhase q) = (guarded.δ e q).map withPhase := by
  obtain ⟨p, i⟩ := q
  cases e <;> rename_i a <;> cases a <;> cases p <;> cases i <;> rfl

/-- The whole run agrees, including undefined runs, and S02 tracks the two control states. -/
theorem run_agrees (w : List Event) :
    published.run w = (guarded.run w).map withPhase := by
  suffices h : ∀ q : Controls,
      published.runFrom (withPhase q) w = (guarded.runFrom q w).map withPhase from
    h guarded.q0
  induction w with
  | nil => exact fun _ => rfl
  | cons e w ih =>
    intro q
    erw [runFrom_cons published, runFrom_cons guarded, step_agrees]
    cases guarded.δ e q with
    | none => rfl
    | some r => exact ih r

/-- A reachable product state has exactly the phase determined by its controls. -/
theorem reached_iff (w : List Event) (q : Controls) (s : Phase) :
    published.run w = some (q, s) ↔ guarded.run w = some q ∧ phaseOf q = s := by
  rw [run_agrees]
  suffices aux : ∀ r : Option Controls,
      r.map withPhase = some (q, s) ↔ r = some q ∧ phaseOf q = s from
    aux (guarded.run w)
  intro r
  cases r <;> simp [withPhase]
  intro h
  rw [h]

/-- Either notification is allowed exactly when both controls are disabled. -/
theorem notification_iff (w : List Event) (q : Controls) (s : Phase) (a : Notification)
    (h : published.run w = some (q, s)) :
    w ++ [.notify a] ∈ published.L ↔ q.1 ≠ .enabled ∧ q.2 ≠ .noIRQ := by
  have hq := ((reached_iff w q s).mp h).1
  change (published.run (w ++ [.notify a])).isSome = true ↔ _
  erw [run_agrees, run_append_event guarded, hq]
  by_cases hg : q.1 ≠ .enabled ∧ q.2 ≠ .noIRQ <;> simp [guarded, hg, Option.isSome]

private def preemptPrefix : PreemptState → List Event
  | .enabled => []
  | .disabled => [.preempt .disable]
  | .scheduling => [.preempt .disableSched]

private def irqPrefix : IRQState → List Event
  | .noIRQ => []
  | .masked => [.irq .localDisable]
  | .handling => [.irq .hwDisable]

/-- Each of the nine control pairs is reachable, with a unique S02 phase. -/
theorem reachable_iff (q : Controls) (s : Phase) :
    (∃ w, published.run w = some (q, s)) ↔ phaseOf q = s := by
  constructor
  · rintro ⟨w, h⟩
    exact ((reached_iff w q s).mp h).2
  · rintro rfl
    obtain ⟨p, i⟩ := q
    exact ⟨preemptPrefix p ++ irqPrefix i, by cases p <;> cases i <;> rfl⟩

/-- Without S17, S02 allows both IRQ disables followed by a notification.
G06 has no participating letters in this trace. -/
theorem missing_s17 (a : Notification) :
    s02.run [.irq .localDisable, .irq .hwDisable, .notify a] = some .disabled ∧
    s17.run [.localDisable, .hwDisable] = none :=
  ⟨rfl, rfl⟩

/-- Without G06, S02 allows two preemption disables followed by a notification.
S17 has no participating letters in this trace. -/
theorem missing_g06 (a : Notification) :
    s02.run [.preempt .disable, .preempt .disableSched, .notify a] = some .disabled ∧
    g06.run [.disable, .disableSched] = none :=
  ⟨rfl, rfl⟩

/-- The three recorded events in JSA Figure 29. Figure 28 reports `sched_waking` rejected
after the disable/enable pair returns the monitor to its initial state. -/
def figure29 : List Event := [.preempt .disable, .preempt .enable, .notify .waking]

theorem figure29_replay :
    published.run (figure29.take 2) = some published.q0 ∧ published.run figure29 = none :=
  ⟨rfl, rfl⟩

end LinuxRV.Wakeup
