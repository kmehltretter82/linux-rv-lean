import LinuxRV.IRQRevision

/-! Formal analysis of the `irqexit` monitor from `LinuxRV.IRQRevision`:

1. **Exhaustive fault classification (`step_none_iff`, `dispatch_rejected_iff`):**
   Every `IRQExit.step` rejection falls into exactly one of three disjoint classes:
   stateless local guard failure (`hard`, `!irqOff`, or v2 `ownerCurrent`),
   scheduler `on_cpu` switch-pairing failure, or `(entry, exit)` nesting failure.
2. **Exact 1-bit reduction (`irqexit_reduces_to_one_bit_nesting`) and redundancy
   (`irqexit_never_rejects_under_kernel_invariants`):**
   Under valid stateless local guards and valid per-task `on_cpu` alternation,
   the 3-state, 4-event `irqexit` monitor (`v2` or `v3`) has the exact same
   rejection verdict, rejection count, and projected state as a 1-bit `(entry, exit)`
   nesting checker with no `sched_switch` hook and no `suspended` state.
   When `(entry, exit)` nesting also holds, `irqexit` never rejects any finite trace.
3. **Separating bug witnesses:**
   Concrete traces passing every stateless local guard (`LocalGuardsOk`) that
   `irqexit` still rejects—direct re-entrant `preempt_schedule_irq()`, re-entry
   across `switchOut`/`switchIn`, unmatched `exit`, and `on_cpu` pairing corruption
   while suspended (showing `OnCpuValid` is strictly needed for the 1-bit reduction).
4. **Observational impossibility (`every_trace_has_safe_and_faulty_realizations`,
   `no_complete_monitor_over_irqexit_alphabet`):**
   Over an abstract kernel model containing unobservable early-hardirq and
   return-tail steps, every observable `irqexit` trace has both safe and faulty
   realizations with identical projections, so no monitor over the `irqexit`
   alphabet can decide either fault class. -/
namespace LinuxRV.IRQExitAnalysis

open LinuxRV.IRQRevision.IRQExit

/-! ### Part 1: Exhaustive 3-way classification of `IRQExit` rejections -/

/-- Structural `(entry, exit)` nesting violations on CPU:
unmatched `exit` in `idle` or re-entrant `entry` in `rescheduling`. -/
def IsNestingFault (s : State) (e : Event) : Prop :=
  (s = .idle ∧ e = .exit) ∨ (s = .rescheduling ∧ e = .entry)

/-- Structural scheduler `on_cpu` / switch-pairing violations:
`switchIn` while already running in `rescheduling`, or any non-`switchIn`
event while `suspended` (off-CPU). -/
def IsOnCpuFault (s : State) (e : Event) : Prop :=
  (s = .rescheduling ∧ e = .switchIn) ∨ (s = .suspended ∧ e ≠ .switchIn)

/-- The 6 structurally defined `(state, event)` edges of `irqexit`. -/
def IsDefinedEdge (s : State) (e : Event) : Prop :=
  ¬ IsNestingFault s e ∧ ¬ IsOnCpuFault s e

/-- Edges that check `v.ownerCurrent` in RFC v2. -/
def NeedsOwner (s : State) (e : Event) : Prop :=
  (s = .idle ∧ e = .entry) ∨
  (s = .rescheduling ∧ e = .exit) ∨
  (s = .rescheduling ∧ e = .switchOut)

/-- Stateless local guard failure on a structurally defined edge. -/
def IsGuardFault (rev : Revision) (s : State) (e : Event) (v : Env) : Prop :=
  IsDefinedEdge s e ∧
  (v.hard = true ∨ v.irqOff = false ∨ (rev = .v2 ∧ NeedsOwner s e ∧ v.ownerCurrent = false))

/-- The three fault classes are pairwise disjoint. -/
theorem fault_classes_disjoint (rev : Revision) (s : State) (e : Event) (v : Env) :
    ¬ (IsNestingFault s e ∧ IsOnCpuFault s e) ∧
    ¬ (IsGuardFault rev s e v ∧ IsNestingFault s e) ∧
    ¬ (IsGuardFault rev s e v ∧ IsOnCpuFault s e) := by
  refine ⟨?_, ?_, ?_⟩
  · cases s <;> cases e <;> simp [IsNestingFault, IsOnCpuFault]
  · rintro ⟨⟨⟨hn, _⟩, _⟩, h⟩; exact hn h
  · rintro ⟨⟨⟨_, ho⟩, _⟩, h⟩; exact ho h

/-- Exact characterization of `IRQExit.step rev s e v = none` into the three
disjoint fault classes. -/
theorem step_none_iff (rev : Revision) (s : State) (e : Event) (v : Env) :
    step rev s e v = none ↔
      IsGuardFault rev s e v ∨ IsOnCpuFault s e ∨ IsNestingFault s e := by
  cases rev <;> cases s <;> cases e <;> cases v with
  | mk hard irqOff owner =>
    cases hard <;> cases irqOff <;> cases owner <;>
      simp [step, IsGuardFault, IsDefinedEdge, IsOnCpuFault, IsNestingFault, NeedsOwner]

/-- Exact characterization of when a single `IRQExit.dispatch` call reports a rejection. -/
theorem dispatch_rejected_iff (rev : Revision) (m : Option State) (e : Event) (v : Env) :
    (dispatch rev m e v).rejected = true ↔
      match m with
      | none =>
          (e = .entry ∧ IsGuardFault rev .idle .entry v) ∨
          (e = .exit ∧ rev = .v2 ∧ (v.hard = true ∨ v.irqOff = false ∨ v.ownerCurrent = false))
      | some s =>
          IsGuardFault rev s e v ∨ IsOnCpuFault s e ∨ IsNestingFault s e := by
  cases m with
  | none =>
    cases rev <;> cases e <;> cases v with
    | mk hard irqOff owner =>
      cases hard <;> cases irqOff <;> cases owner <;>
        simp [dispatch, process, step, IsGuardFault, IsDefinedEdge,
              IsOnCpuFault, IsNestingFault, NeedsOwner]
  | some s =>
    simp only [dispatch, process]
    rw [← step_none_iff]
    cases step rev s e v <;> simp

/-! ### Part 2: Exact 1-bit nesting reduction and redundancy under kernel invariants -/

/-- Valid stateless local guards for event `e`: not in hardirq context, local IRQs
disabled, and `ownerCurrent` holds on every event other than `switchIn` (consistent
with `IRQExit.run_eq`, where `switchIn` fires for `next` while `current` is `prev`). -/
def LocalGuardsOk (e : Event) (v : Env) : Prop :=
  v.hard = false ∧ v.irqOff = true ∧ (e ≠ .switchIn → v.ownerCurrent = true)

/-- Per-task `on_cpu` transition for a single event. -/
def onCpuStep (onCpu : Bool) : Event → Option Bool
  | .entry     => if onCpu then some true else none
  | .exit      => if onCpu then some true else none
  | .switchOut => if onCpu then some false else none
  | .switchIn  => if !onCpu then some true else none

/-- Valid per-task `on_cpu` alternation: a task executes `entry`, `exit`, and
`switchOut` only while on CPU (`true`), and `switchIn` only while off CPU (`false`). -/
def OnCpuValid (onCpu : Bool) : List Event → Prop
  | [] => True
  | e :: rest =>
    match onCpuStep onCpu e with
    | some onCpu' => OnCpuValid onCpu' rest
    | none => False

/-- Final `on_cpu` boolean after executing a sequence of events. -/
def onCpuAfter (onCpu : Bool) : List Event → Bool
  | [] => onCpu
  | e :: rest =>
    match onCpuStep onCpu e with
    | some onCpu' => onCpuAfter onCpu' rest
    | none => onCpu

/-- The 2-event alphabet obtained by erasing `sched_switch` (`switchOut`, `switchIn`). -/
inductive NestingEvent where
  | entry | exit
  deriving DecidableEq, Repr

/-- Projection of an `irqexit` trace onto `(entry, exit)` events only, dropping
all switch events and all environment guards. -/
def projectEntryExit : List (Event × Env) → List NestingEvent
  | [] => []
  | (e, _) :: rest =>
    match e with
    | .entry => .entry :: projectEntryExit rest
    | .exit  => .exit  :: projectEntryExit rest
    | .switchOut | .switchIn => projectEntryExit rest

/-- A 1-bit `(entry, exit)` nesting monitor with no `sched_switch` hook and no
`suspended` state. `none` = unsynchronized; `some false` = idle;
`some true` = inside `preempt_schedule_irq`. -/
def nestingDispatch (n : Option Bool) (e : NestingEvent) : Option Bool × Bool :=
  match n, e with
  | none, .entry       => (some true, false)
  | none, .exit        => (some false, false)
  | some false, .entry => (some true, false)
  | some false, .exit  => (none, true)
  | some true, .entry  => (none, true)
  | some true, .exit   => (some false, false)

/-- Trace execution of the 1-bit nesting monitor. -/
def nestingRun (n : Option Bool) : List NestingEvent → List Bool × Option Bool
  | [] => ([], n)
  | e :: rest =>
    let res := nestingDispatch n e
    let tail := nestingRun res.1 rest
    (res.2 :: tail.1, tail.2)

/-- State correspondence embedding the 1-bit nesting state plus `onCpu` into
`Option IRQExit.State`: `some true` splits into `rescheduling` (on CPU) or
`suspended` (off CPU). -/
def embedState (onCpu : Bool) : Option Bool → Option State
  | none       => none
  | some false => some .idle
  | some true  => some (if onCpu then .rescheduling else .suspended)

/-- Single-step simulation on `switchOut` and `switchIn`: under valid local guards
and `on_cpu` alternation, switch events never reject and leave the 1-bit nesting
state unchanged. -/
theorem dispatch_switch_preserves_embed
    (rev : Revision) (onCpu onCpu' : Bool) (n : Option Bool) (e : Event) (v : Env)
    (hSwitch : e = .switchOut ∨ e = .switchIn)
    (hGuards : LocalGuardsOk e v)
    (hStep : onCpuStep onCpu e = some onCpu') :
    dispatch rev (embedState onCpu n) e v = ⟨embedState onCpu' n, false⟩ := by
  rcases hGuards with ⟨hHard, hIrqOff, hOwn⟩
  rcases hSwitch with rfl | rfl
  · have hOwn' : v.ownerCurrent = true := hOwn (by decide)
    cases onCpu with
    | false => simp [onCpuStep] at hStep
    | true =>
      simp only [onCpuStep, ↓reduceIte, Option.some.injEq] at hStep
      subst hStep
      cases rev <;> cases n with
      | none => simp [embedState, dispatch]
      | some b =>
        cases b <;>
          simp [embedState, dispatch, process, step, hHard, hIrqOff, hOwn']
  · cases onCpu with
    | true => simp [onCpuStep] at hStep
    | false =>
      simp only [onCpuStep, Bool.not_false, ↓reduceIte, Option.some.injEq] at hStep
      subst hStep
      cases rev <;> cases n with
      | none => simp [embedState, dispatch]
      | some b =>
        cases b <;>
          simp [embedState, dispatch, process, step, hHard, hIrqOff]

/-- Single-step simulation on `entry` and `exit`: under valid local guards and
`on_cpu` alternation, `IRQExit.dispatch` produces the exact same rejection flag
and embedded successor state as `nestingDispatch`. -/
theorem dispatch_entry_exit_eq_nesting
    (rev : Revision) (onCpu onCpu' : Bool) (n : Option Bool) (e : Event) (v : Env)
    (ne : NestingEvent)
    (hMap : (e = .entry ∧ ne = .entry) ∨ (e = .exit ∧ ne = .exit))
    (hGuards : LocalGuardsOk e v)
    (hStep : onCpuStep onCpu e = some onCpu') :
    dispatch rev (embedState onCpu n) e v =
      ⟨embedState onCpu' (nestingDispatch n ne).1, (nestingDispatch n ne).2⟩ := by
  rcases hGuards with ⟨hHard, hIrqOff, hOwn⟩
  rcases hMap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hOwn' : v.ownerCurrent = true := hOwn (by decide)
    cases onCpu with
    | false => simp [onCpuStep] at hStep
    | true =>
      simp only [onCpuStep, ↓reduceIte, Option.some.injEq] at hStep
      subst hStep
      cases rev <;> cases n with
      | none =>
        simp [embedState, nestingDispatch, dispatch, process, step, hHard, hIrqOff, hOwn']
      | some b =>
        cases b <;>
          simp [embedState, nestingDispatch, dispatch, process, step, hHard, hIrqOff, hOwn']
  · have hOwn' : v.ownerCurrent = true := hOwn (by decide)
    cases onCpu with
    | false => simp [onCpuStep] at hStep
    | true =>
      simp only [onCpuStep, ↓reduceIte, Option.some.injEq] at hStep
      subst hStep
      cases rev <;> cases n with
      | none =>
        simp [embedState, nestingDispatch, dispatch, hHard, hIrqOff, hOwn']
      | some b =>
        cases b <;>
          simp [embedState, nestingDispatch, dispatch, process, step, hHard, hIrqOff, hOwn']

/-- Generalized trace-level 1-bit reduction from any embedded starting state. -/
theorem run_eq_nesting_under_onCpu
    (rev : Revision) (onCpu : Bool) (n : Option Bool) (w : List (Event × Env))
    (hGuards : ∀ p ∈ w, LocalGuardsOk p.1 p.2)
    (hOnCpu : OnCpuValid onCpu (w.map Prod.fst)) :
    (run rev (embedState onCpu n) w).1.any id =
      (nestingRun n (projectEntryExit w)).1.any id ∧
    (run rev (embedState onCpu n) w).1.count true =
      (nestingRun n (projectEntryExit w)).1.count true ∧
    (run rev (embedState onCpu n) w).2 =
      embedState (onCpuAfter onCpu (w.map Prod.fst))
        (nestingRun n (projectEntryExit w)).2 := by
  induction w generalizing onCpu n with
  | nil =>
    simp [run, nestingRun, projectEntryExit, onCpuAfter]
  | cons p rest ih =>
    rcases p with ⟨e, v⟩
    have hv : LocalGuardsOk e v := hGuards (e, v) (by simp)
    have hRestGuards : ∀ q ∈ rest, LocalGuardsOk q.1 q.2 := by
      intro q hq
      exact hGuards q (by simp [hq])
    simp only [List.map_cons, OnCpuValid, onCpuAfter] at hOnCpu ⊢
    cases hStep : onCpuStep onCpu e with
    | none =>
      simp [hStep] at hOnCpu
    | some onCpu' =>
      simp only [hStep] at hOnCpu ⊢
      cases e with
      | switchOut =>
        have hd := dispatch_switch_preserves_embed rev onCpu onCpu' n .switchOut v
          (Or.inl rfl) hv hStep
        have hTail := ih onCpu' n hRestGuards hOnCpu
        simp only [run, projectEntryExit, hd]
        refine ⟨?_, ?_, hTail.2.2⟩
        · simpa using hTail.1
        · simpa [List.count_cons] using hTail.2.1
      | switchIn =>
        have hd := dispatch_switch_preserves_embed rev onCpu onCpu' n .switchIn v
          (Or.inr rfl) hv hStep
        have hTail := ih onCpu' n hRestGuards hOnCpu
        simp only [run, projectEntryExit, hd]
        refine ⟨?_, ?_, hTail.2.2⟩
        · simpa using hTail.1
        · simpa [List.count_cons] using hTail.2.1
      | entry =>
        have hd := dispatch_entry_exit_eq_nesting rev onCpu onCpu' n .entry v .entry
          (Or.inl ⟨rfl, rfl⟩) hv hStep
        have hTail := ih onCpu' (nestingDispatch n .entry).1 hRestGuards hOnCpu
        simp only [run, projectEntryExit, nestingRun, hd]
        refine ⟨?_, ?_, hTail.2.2⟩
        · simp [hTail.1]
        · simp [List.count_cons, hTail.2.1]
      | exit =>
        have hd := dispatch_entry_exit_eq_nesting rev onCpu onCpu' n .exit v .exit
          (Or.inr ⟨rfl, rfl⟩) hv hStep
        have hTail := ih onCpu' (nestingDispatch n .exit).1 hRestGuards hOnCpu
        simp only [run, projectEntryExit, nestingRun, hd]
        refine ⟨?_, ?_, hTail.2.2⟩
        · simp [hTail.1]
        · simp [List.count_cons, hTail.2.1]

/-- **1-Bit Reduction Theorem (unstarted monitor):**
Starting from `none`, under valid stateless local guards and valid per-task
`on_cpu` alternation, `IRQExit.run` (`v2` or `v3`) rejects iff the 1-bit
`(entry, exit)` nesting monitor rejects, produces the exact same number of
rejections, and ends in the exact embedded state. Thus the `sched_switch` hook
and `suspended` state add zero detection power under well-formed switching. -/
theorem irqexit_reduces_to_one_bit_nesting
    (rev : Revision) (onCpu : Bool) (w : List (Event × Env))
    (hGuards : ∀ p ∈ w, LocalGuardsOk p.1 p.2)
    (hOnCpu : OnCpuValid onCpu (w.map Prod.fst)) :
    (run rev none w).1.any id = (nestingRun none (projectEntryExit w)).1.any id ∧
    (run rev none w).1.count true = (nestingRun none (projectEntryExit w)).1.count true ∧
    (run rev none w).2 =
      embedState (onCpuAfter onCpu (w.map Prod.fst))
        (nestingRun none (projectEntryExit w)).2 := by
  simpa [embedState] using run_eq_nesting_under_onCpu rev onCpu none w hGuards hOnCpu

/-- Well-nested `(entry, exit)` sequences starting from `inside : Bool`
(`false` = outside `preempt_schedule_irq`, `true` = mid-call). -/
def NestingValid (inside : Bool) : List NestingEvent → Prop
  | [] => True
  | .entry :: rest => inside = false ∧ NestingValid true rest
  | .exit  :: rest => inside = true  ∧ NestingValid false rest

theorem nestingRun_some_no_rejection (inside : Bool) (xs : List NestingEvent)
    (h : NestingValid inside xs) :
    (nestingRun (some inside) xs).1.any id = false := by
  induction xs generalizing inside with
  | nil => rfl
  | cons e rest ih =>
    cases e with
    | entry =>
      rcases h with ⟨rfl, hrest⟩
      simpa [nestingRun, nestingDispatch] using ih true hrest
    | exit =>
      rcases h with ⟨rfl, hrest⟩
      simpa [nestingRun, nestingDispatch] using ih false hrest

theorem nestingRun_none_no_rejection (inside : Bool) (xs : List NestingEvent)
    (h : NestingValid inside xs) :
    (nestingRun none xs).1.any id = false := by
  cases xs with
  | nil => rfl
  | cons e rest =>
    cases e with
    | entry =>
      rcases h with ⟨_, hrest⟩
      simpa [nestingRun, nestingDispatch] using nestingRun_some_no_rejection true rest hrest
    | exit =>
      rcases h with ⟨_, hrest⟩
      simpa [nestingRun, nestingDispatch] using nestingRun_some_no_rejection false rest hrest

/-- **Redundancy Corollary:**
When local stateless guards hold, per-task `on_cpu` switching alternates, and
`preempt_schedule_irq()` entry/exit calls alternate (whether monitoring attaches
idle or mid-call), `irqexit` (`v2` or `v3`) never rejects any event on any finite trace. -/
theorem irqexit_never_rejects_under_kernel_invariants
    (rev : Revision) (onCpu inside : Bool) (w : List (Event × Env))
    (hGuards : ∀ p ∈ w, LocalGuardsOk p.1 p.2)
    (hOnCpu : OnCpuValid onCpu (w.map Prod.fst))
    (hNesting : NestingValid inside (projectEntryExit w)) :
    (run rev none w).1.any id = false ∧
    ∀ r ∈ (run rev none w).1, r = false := by
  have hRed := (irqexit_reduces_to_one_bit_nesting rev onCpu w hGuards hOnCpu).1
  have hNone := nestingRun_none_no_rejection inside (projectEntryExit w) hNesting
  have hAny : (run rev none w).1.any id = false := by rw [hRed, hNone]
  refine ⟨hAny, ?_⟩
  intro r hr
  cases r with
  | false => rfl
  | true =>
    have hTrue : (run rev none w).1.any id = true :=
      List.any_eq_true.mpr ⟨true, hr, rfl⟩
    rw [hAny] at hTrue
    cases hTrue

/-! ### Part 3: Separating bug witnesses — what `irqexit` catches beyond stateless checks -/

/-- A clean environment passing every stateless local check (`!hard`, `irqOff`, `ownerCurrent`). -/
def okEnv : Env := ⟨false, true, true⟩

/-- **Witness A (Direct re-entrancy):**
Two consecutive `entry` events both pass every stateless local check (`LocalGuardsOk`)
and maintain valid `on_cpu` state, yet `irqexit` (`v2` and `v3`) catches the second `entry`. -/
theorem witness_reentrant_entry_direct (rev : Revision) :
    let w : List (Event × Env) := [(.entry, okEnv), (.entry, okEnv)]
    (∀ p ∈ w, LocalGuardsOk p.1 p.2) ∧
    OnCpuValid true (w.map Prod.fst) ∧
    run rev none w = ([false, true], none) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [LocalGuardsOk, okEnv]
  · simp [OnCpuValid, onCpuStep]
  · cases rev <;> decide

/-- **Witness B (Cross-switch re-entrancy):**
A task enters `preempt_schedule_irq()`, switches out, switches back in, and re-enters
before returning from the first call. Every event passes all stateless local checks
and valid `on_cpu` alternation; `irqexit` (`v2` and `v3`) rejects the second `entry`
(equivalently to the 1-bit nesting projection `[.entry, .entry]`). -/
theorem witness_reentrant_entry_across_switch (rev : Revision) :
    let w : List (Event × Env) :=
      [(.entry, okEnv), (.switchOut, okEnv), (.switchIn, okEnv), (.entry, okEnv)]
    (∀ p ∈ w, LocalGuardsOk p.1 p.2) ∧
    OnCpuValid true (w.map Prod.fst) ∧
    run rev none w = ([false, false, false, true], none) ∧
    nestingRun none (projectEntryExit w) = ([false, true], none) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp [LocalGuardsOk, okEnv]
  · simp [OnCpuValid, onCpuStep]
  · cases rev <;> decide
  · decide

/-- **Witness C (Unmatched `exit` after synchronization):**
After synchronizing on `entry`–`exit`, a stray second `exit` passes every stateless
local check and valid `on_cpu` state, yet `irqexit` (`v2` and `v3`) rejects it. -/
theorem witness_unmatched_exit (rev : Revision) :
    let w : List (Event × Env) := [(.entry, okEnv), (.exit, okEnv), (.exit, okEnv)]
    (∀ p ∈ w, LocalGuardsOk p.1 p.2) ∧
    OnCpuValid true (w.map Prod.fst) ∧
    run rev none w = ([false, false, true], none) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [LocalGuardsOk, okEnv]
  · simp [OnCpuValid, onCpuStep]
  · cases rev <;> decide

/-- **Witness D (`on_cpu` pairing corruption while suspended — necessity of `OnCpuValid`):**
A task enters `preempt_schedule_irq()`, switches out, and then executes `exit` without
a matching `switchIn`. Every local stateless guard passes and the `(entry, exit)`
projection is well-nested (so the 1-bit nesting checker accepts it), whereas `irqexit`
(`v2` and `v3`) rejects the `exit` from `suspended`. -/
theorem witness_on_cpu_fault_while_suspended (rev : Revision) :
    let w : List (Event × Env) := [(.entry, okEnv), (.switchOut, okEnv), (.exit, okEnv)]
    (∀ p ∈ w, LocalGuardsOk p.1 p.2) ∧
    ¬ OnCpuValid true (w.map Prod.fst) ∧
    NestingValid false (projectEntryExit w) ∧
    nestingRun none (projectEntryExit w) = ([false, false], some false) ∧
    run rev none w = ([false, false, true], none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [LocalGuardsOk, okEnv]
  · simp [OnCpuValid, onCpuStep]
  · simp [projectEntryExit, NestingValid]
  · decide
  · cases rev <;> decide

/-- Conversely, while in `idle`, `irqexit` has self-loops on both `switchOut` and
`switchIn`, so it does not check general scheduler `on_cpu` alternation outside
`preempt_schedule_irq()`. -/
theorem idle_accepts_double_switchOut (rev : Revision) :
    let w : List (Event × Env) :=
      [(.entry, okEnv), (.exit, okEnv), (.switchOut, okEnv), (.switchOut, okEnv)]
    ¬ OnCpuValid true (w.map Prod.fst) ∧
    run rev none w = ([false, false, false, false], some .idle) := by
  refine ⟨?_, ?_⟩
  · simp [OnCpuValid, onCpuStep]
  · cases rev <;> decide

/-! ### Part 4: Observational impossibility over the `irqexit` alphabet -/

/-- Abstract kernel execution steps extending `irqexit`-observable events with
unobservable steps in the early-hardirq window (such as the ARM64 ftrace-recursion
interval) and the post-`preempt_schedule_irq` return tail. -/
inductive KernelStep where
  | obs (e : Event) (v : Env)
  | earlyHardirqSafe
  | earlyHardirqFault
  | returnTailSafe
  | returnTailFault
  deriving DecidableEq, Repr

/-- Observation projection onto the `irqexit` monitor alphabet: keeps only
`obs` events and erases all early-hardirq and return-tail steps. -/
def observe : List KernelStep → List (Event × Env)
  | [] => []
  | .obs e v :: rest => (e, v) :: observe rest
  | .earlyHardirqSafe :: rest => observe rest
  | .earlyHardirqFault :: rest => observe rest
  | .returnTailSafe :: rest => observe rest
  | .returnTailFault :: rest => observe rest

theorem observe_append (k₁ k₂ : List KernelStep) :
    observe (k₁ ++ k₂) = observe k₁ ++ observe k₂ := by
  induction k₁ with
  | nil => rfl
  | cons s rest ih =>
    cases s <;> simp [observe, ih]

/-- Lift a raw `irqexit` event stream into observable `KernelStep`s. -/
def liftObs (w : List (Event × Env)) : List KernelStep :=
  w.map (fun p => KernelStep.obs p.1 p.2)

theorem observe_liftObs (w : List (Event × Env)) :
    observe (liftObs w) = w := by
  induction w with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨e, v⟩
    simp only [liftObs, List.map_cons, observe]
    exact congrArg ((e, v) :: ·) ih

/-- Safety predicate: no unobservable early-hardirq fault and no return-tail fault. -/
def ExecutionSafe (k : List KernelStep) : Prop :=
  KernelStep.earlyHardirqFault ∉ k ∧ KernelStep.returnTailFault ∉ k

theorem liftObs_safe (w : List (Event × Env)) : ExecutionSafe (liftObs w) := by
  constructor <;> simp [liftObs]

/-- **Universal Monitor Blindness:**
Any two kernel executions with the same `irqexit` observation induce the exact
same verdict from *every* function/monitor `M` over the `irqexit` alphabet. -/
theorem universal_monitor_blindness {α : Type}
    (M : List (Event × Env) → α)
    (k₁ k₂ : List KernelStep)
    (hObs : observe k₁ = observe k₂) :
    M (observe k₁) = M (observe k₂) :=
  congrArg M hObs

/-- **Universal Realizability Theorem:**
Every finite trace `w` in the `irqexit` alphabet is the exact observation of a safe
execution, an early-hardirq faulty execution, and a return-tail faulty execution.
Consequently, no observation over `Event × Env` can ever certify the absence of
either unobservable fault class. -/
theorem every_trace_has_safe_and_faulty_realizations (w : List (Event × Env)) :
    ∃ kSafe kEarlyFault kTailFault : List KernelStep,
      observe kSafe = w ∧
      observe kEarlyFault = w ∧
      observe kTailFault = w ∧
      ExecutionSafe kSafe ∧
      KernelStep.earlyHardirqFault ∈ kEarlyFault ∧
      KernelStep.returnTailFault ∈ kTailFault := by
  refine ⟨.earlyHardirqSafe :: liftObs w ++ [.returnTailSafe],
          .earlyHardirqFault :: liftObs w ++ [.returnTailSafe],
          .earlyHardirqSafe :: liftObs w ++ [.returnTailFault],
          ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [observe, observe_append, observe_liftObs]
  · simp [observe, observe_append, observe_liftObs]
  · simp [observe, observe_append, observe_liftObs]
  · have ⟨h1, h2⟩ := liftObs_safe w
    constructor
    · simp [h1]
    · simp [h2]
  · simp
  · simp

/-- Concrete clean execution with one legal `entry`–`exit` cycle. -/
def cleanKernelTrace : List KernelStep :=
  [.earlyHardirqSafe, .obs .entry okEnv, .obs .exit okEnv, .returnTailSafe]

/-- Concrete early-hardirq fault execution with the exact same `irqexit` observation. -/
def earlyFaultKernelTrace : List KernelStep :=
  [.earlyHardirqFault, .obs .entry okEnv, .obs .exit okEnv, .returnTailSafe]

/-- Concrete return-tail fault execution with the exact same `irqexit` observation. -/
def tailFaultKernelTrace : List KernelStep :=
  [.earlyHardirqSafe, .obs .entry okEnv, .obs .exit okEnv, .returnTailFault]

/-- Concrete indistinguishability for both early-hardirq and return-tail faults:
`IRQExit.run` (`v2` and `v3`) accepts all three traces with zero rejections, and
every monitor over `Event × Env` returns the identical verdict on all three. -/
theorem concrete_observational_blindness (rev : Revision) :
    ExecutionSafe cleanKernelTrace ∧
    ¬ ExecutionSafe earlyFaultKernelTrace ∧
    ¬ ExecutionSafe tailFaultKernelTrace ∧
    observe cleanKernelTrace = observe earlyFaultKernelTrace ∧
    observe cleanKernelTrace = observe tailFaultKernelTrace ∧
    (run rev none (observe cleanKernelTrace)).1.any id = false ∧
    (run rev none (observe earlyFaultKernelTrace)).1.any id = false ∧
    (run rev none (observe tailFaultKernelTrace)).1.any id = false := by
  refine ⟨?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · simp [ExecutionSafe, cleanKernelTrace]
  · simp [ExecutionSafe, earlyFaultKernelTrace]
  · simp [ExecutionSafe, tailFaultKernelTrace]
  · cases rev <;> decide
  · cases rev <;> decide
  · cases rev <;> decide

/-- **Impossibility Theorem:**
No monitor `M : List (Event × Env) → Bool` over the `irqexit` alphabet can be both
sound and complete for early-hardirq safety, for return-tail safety, or for joint
execution safety. -/
theorem no_complete_monitor_over_irqexit_alphabet :
    (¬ ∃ M : List (Event × Env) → Bool,
        ∀ k : List KernelStep, M (observe k) = true ↔ KernelStep.earlyHardirqFault ∉ k) ∧
    (¬ ∃ M : List (Event × Env) → Bool,
        ∀ k : List KernelStep, M (observe k) = true ↔ KernelStep.returnTailFault ∉ k) ∧
    (¬ ∃ M : List (Event × Env) → Bool,
        ∀ k : List KernelStep, M (observe k) = true ↔ ExecutionSafe k) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨M, hM⟩
    have hClean : M (observe cleanKernelTrace) = true :=
      (hM cleanKernelTrace).mpr (by simp [cleanKernelTrace])
    have hFault : M (observe earlyFaultKernelTrace) ≠ true := by
      intro h
      exact ((hM earlyFaultKernelTrace).mp h) (by simp [earlyFaultKernelTrace])
    exact hFault (by simpa [cleanKernelTrace, earlyFaultKernelTrace, observe] using hClean)
  · rintro ⟨M, hM⟩
    have hClean : M (observe cleanKernelTrace) = true :=
      (hM cleanKernelTrace).mpr (by simp [cleanKernelTrace])
    have hFault : M (observe tailFaultKernelTrace) ≠ true := by
      intro h
      exact ((hM tailFaultKernelTrace).mp h) (by simp [tailFaultKernelTrace])
    exact hFault (by simpa [cleanKernelTrace, tailFaultKernelTrace, observe] using hClean)
  · rintro ⟨M, hM⟩
    have hClean : M (observe cleanKernelTrace) = true :=
      (hM cleanKernelTrace).mpr (by simp [ExecutionSafe, cleanKernelTrace])
    have hFault : M (observe earlyFaultKernelTrace) ≠ true := by
      intro h
      have hs := (hM earlyFaultKernelTrace).mp h
      exact hs.1 (by simp [earlyFaultKernelTrace])
    exact hFault (by simpa [cleanKernelTrace, earlyFaultKernelTrace, observe] using hClean)

end LinuxRV.IRQExitAnalysis
