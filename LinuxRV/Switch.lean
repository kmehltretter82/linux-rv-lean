import LinuxRV.Parallel

/-! Switch specifications S07 and S08 from de Oliveira et al. (2020), Figures 21–22.
The final theorem interprets S07's merged state under a well-formed control history. -/

namespace LinuxRV.Switch

open CassandrasLafortune RamadgeWonham.Shared

inductive Control where
  | localIrqDisable | localIrqEnable | preemptDisableSched | preemptEnableSched
  deriving DecidableEq

inductive SchedulerEvent where
  | scheduleEntry | scheduleExit
  deriving DecidableEq

inductive SwitchEvent where
  | switchIn | switchInOther | switchSuspend | switchPreempt | switchOutOther | switchBlocking
  deriving DecidableEq

abbrev TraceEvent := Event Control SchedulerEvent SwitchEvent

inductive Phase where
  | enabled | oneDisabled | disabled
  deriving DecidableEq

inductive Context where
  | thread | scheduler
  deriving DecidableEq

/-- Figure 21. Both disable labels use the same two arrows, as do both enable labels. -/
def s07 : Generator (Control ⊕ SwitchEvent) where
  Q := Phase
  q0 := .enabled
  Qm := {.enabled}
  δ a p := match a, p with
    | .inl .localIrqDisable, .enabled | .inl .preemptDisableSched, .enabled => some .oneDisabled
    | .inl .localIrqDisable, .oneDisabled | .inl .preemptDisableSched, .oneDisabled => some .disabled
    | .inl .localIrqEnable, .disabled | .inl .preemptEnableSched, .disabled => some .oneDisabled
    | .inl .localIrqEnable, .oneDisabled | .inl .preemptEnableSched, .oneDisabled => some .enabled
    | .inr _, .disabled => some .disabled
    | _, _ => none

/-- Figure 22. The six switch labels are self-loops inside the scheduler. -/
def s08 : Generator (SchedulerEvent ⊕ SwitchEvent) where
  Q := Context
  q0 := .thread
  Qm := {.thread}
  δ a p := match a, p with
    | .inl .scheduleEntry, .thread => some .scheduler
    | .inl .scheduleExit, .scheduler => some .thread
    | .inr _, .scheduler => some .scheduler
    | _, _ => none

/-- A switch is legal in the composition precisely in the two diagrams' switch states. -/
theorem switch_iff (w : List TraceEvent) (k : SwitchEvent) (p : Phase) (c : Context)
    (h : (parallel s07 s08).run w = some (p, c)) :
    w ++ [.shared k] ∈ (parallel s07 s08).L ↔ p = .disabled ∧ c = .scheduler := by
  change ((parallel s07 s08).run (w ++ [.shared k])).isSome = true ↔ _
  rw [run_append_event, h]
  cases p <;> cases c <;> simp [parallel, localStep, Event.left, Event.right, s07, s08]

/-- Individual status of the IRQ mask and scheduler preemption control. -/
inductive Flags where
  | clear | irqOnly | preemptOnly | both
  deriving DecidableEq

def Flags.phase : Flags → Phase
  | .clear => .enabled
  | .irqOnly | .preemptOnly => .oneDisabled
  | .both => .disabled

/-- Well-formed control histories alternate disable and enable for each control separately.
Switch labels have no effect on this book-keeping. -/
def flagHistory : Generator (Control ⊕ SwitchEvent) where
  Q := Flags
  q0 := .clear
  Qm := Set.univ
  δ a f := match a, f with
    | .inl .localIrqDisable, .clear => some .irqOnly
    | .inl .localIrqDisable, .preemptOnly => some .both
    | .inl .localIrqEnable, .irqOnly => some .clear
    | .inl .localIrqEnable, .both => some .preemptOnly
    | .inl .preemptDisableSched, .clear => some .preemptOnly
    | .inl .preemptDisableSched, .irqOnly => some .both
    | .inl .preemptEnableSched, .preemptOnly => some .clear
    | .inl .preemptEnableSched, .both => some .irqOnly
    | .inr _, f => some f
    | _, _ => none

private theorem step_agrees (a : Control ⊕ SwitchEvent) (f g : Flags) (p : Phase)
    (hf : flagHistory.δ a f = some g) (hp : s07.δ a f.phase = some p) :
    p = g.phase := by
  cases a with
  | inl a => cases a <;> cases f <;> simp_all [flagHistory, s07, Flags.phase] <;> subst_vars <;> rfl
  | inr k =>
    cases f <;> simp_all [flagHistory, s07, Flags.phase]
    subst_vars
    rfl

private theorem run_agrees (w : List (Control ⊕ SwitchEvent)) (f g : Flags) (p : Phase)
    (hf : flagHistory.runFrom f w = some g) (hp : s07.runFrom f.phase w = some p) :
    p = g.phase := by
  induction w generalizing f with
  | nil =>
    change some f = some g at hf
    change some f.phase = some p at hp
    obtain rfl := Option.some.inj hf
    exact (Option.some.inj hp).symm
  | cons a w ih =>
    rw [runFrom_cons flagHistory f a w] at hf
    rw [runFrom_cons s07 f.phase a w] at hp
    cases h : flagHistory.δ a f with
    | none => simp [h] at hf
    | some f' =>
      cases j : s07.δ a f.phase with
      | none => simp [j] at hp
      | some p' =>
        rw [h] at hf
        rw [j] at hp
        change s07.runFrom p' w = some p at hp
        rw [step_agrees a f f' p' h j] at hp
        exact ih f' hf hp

/-- For well-formed control histories a legal switch requires both controls disabled and
scheduler context, and those conditions suffice after any legal prefix. -/
theorem switch_iff_controls (w : List TraceEvent) (k : SwitchEvent) (p : Phase)
    (c : Context) (f : Flags) (h : (parallel s07 s08).run w = some (p, c))
    (hf : flagHistory.run (w.filterMap Event.left) = some f) :
    w ++ [.shared k] ∈ (parallel s07 s08).L ↔ f = .both ∧ c = .scheduler := by
  have hs := ((parallel_run_iff s07 s08 w p c).mp h).1
  have eq := run_agrees (w.filterMap Event.left) .clear f p hf hs
  rw [switch_iff w k p c h, eq]
  cases f <;> simp [Flags.phase]

end LinuxRV.Switch
