import Mathlib.Data.List.Basic

/-! Models of the IRQ RFC v2 tables and the v3 proposal, based on commit
f3f79cfdf9cd387def9aa93102c4ce2cc8ec7726. The tables describe the enabled,
sequential monitor; they do not model tracepoint delivery or kernel concurrency. -/
namespace LinuxRV.IRQRevision

namespace IRQState
inductive State where
  | idle | hardirq | softirq | hardFromSoft | softFromHard | hardFromSoftFromHard
  deriving DecidableEq, Repr
inductive Event where
  | hardEntry | hardExit | softEntry | softExit | softEntryFromHard | softExitToHard
  | softSuspend | softResume
  deriving DecidableEq, Repr
structure Env where
  hard : Bool
  serving : Bool
  deriving DecidableEq, Repr

def step (s : State) (e : Event) (v : Env) : Option State :=
  match s, e with
  | .idle, .hardEntry => if v.hard && !v.serving then some .hardirq else none
  | .idle, .softEntry => if !v.hard && v.serving then some .softirq else none
  | .idle, .softResume => if !v.hard then some .softirq else none
  | .hardirq, .hardExit => if v.hard && !v.serving then some .idle else none
  | .hardirq, .softEntryFromHard => if !v.hard && v.serving then some .softFromHard else none
  | .softirq, .softExit => if !v.hard && v.serving then some .idle else none
  | .softirq, .softSuspend => if !v.hard then some .idle else none
  | .softirq, .hardEntry => if v.hard && v.serving then some .hardFromSoft else none
  | .hardFromSoft, .hardExit => if v.hard && v.serving then some .softirq else none
  | .softFromHard, .softExitToHard => if !v.hard && v.serving then some .hardirq else none
  | .softFromHard, .hardEntry => if v.hard && v.serving then some .hardFromSoftFromHard else none
  | .hardFromSoftFromHard, .hardExit => if v.hard && v.serving then some .softFromHard else none
  | _, _ => none

inductive Mode where | ordinary | start | startRun
  deriving DecidableEq, Repr
/-- A nested hardirq is suppressed only after the live hardirq check. -/
def hardDispatch (entry : Bool) (depth : Nat) (v : Env) : Option (Mode × Event) :=
  let e := if entry then Event.hardEntry else Event.hardExit
  if !v.hard then some (.startRun, e)
  else if depth > 1 then none
  else if v.serving then some (.ordinary, e)
  else if entry then some (.startRun, e) else some (.start, e)

def softDispatch (entry fromHard : Bool) (v : Env) : Mode × Event :=
  if entry then
    if fromHard then (.ordinary, .softEntryFromHard) else (.startRun, .softEntry)
  else if fromHard then (.ordinary, .softExitToHard)
  else if v.serving then (.start, .softExit) else (.startRun, .softExit)

def rtSwitch (prevServing nextServing : Bool) : List (Mode × Event) :=
  (if prevServing then [(.start, .softSuspend)] else []) ++
  (if nextServing then [(.startRun, .softResume)] else [])
/-- The handler preserves the live-state check before suppressing nested IRQs. -/
theorem nested_suppression :
    hardDispatch true 2 ⟨true, false⟩ = none ∧
    hardDispatch true 2 ⟨false, false⟩ = some (.startRun, .hardEntry) := by decide

/-- One modeled IRQ-exit softirq interval and nested hardirq. -/
theorem irq_softirq_path :
    step .idle .hardEntry ⟨true, false⟩ = some .hardirq ∧
    step .hardirq .softEntryFromHard ⟨false, true⟩ = some .softFromHard ∧
    step .softFromHard .hardEntry ⟨true, true⟩ = some .hardFromSoftFromHard ∧
    step .hardFromSoftFromHard .hardExit ⟨true, true⟩ = some .softFromHard ∧
    step .softFromHard .softExitToHard ⟨false, true⟩ = some .hardirq ∧
    step .hardirq .hardExit ⟨true, false⟩ = some .idle := by decide

/-- On RT, outgoing softirq suspension precedes incoming resumption. -/
theorem rt_switch_both :
    rtSwitch true true = [(.start, .softSuspend), (.startRun, .softResume)] := by decide
end IRQState

namespace IRQExit
inductive State where | idle | rescheduling | suspended
  deriving DecidableEq, Repr
inductive Event where | entry | exit | switchOut | switchIn
  deriving DecidableEq, Repr
structure Env where
  hard : Bool
  irqOff : Bool
  ownerCurrent : Bool
  deriving DecidableEq, Repr
inductive Revision where | v2 | v3
  deriving DecidableEq, Repr

def step (rev : Revision) (s : State) (e : Event) (v : Env) : Option State :=
  let common := !v.hard && v.irqOff
  let owner := rev == .v3 || v.ownerCurrent
  match s, e with
  | .idle, .entry => if common && owner then some .rescheduling else none
  | .idle, .switchIn | .idle, .switchOut => if common then some .idle else none
  | .rescheduling, .exit => if common && owner then some .idle else none
  | .rescheduling, .switchOut => if common && owner then some .suspended else none
  | .suspended, .switchIn => if common then some .rescheduling else none
  | _, _ => none

/-- `none` means not started. A rejected event resets monitoring. -/
structure Monitor where
  state : Option State
  rejected : Bool
  deriving DecidableEq, Repr

def process (rev : Revision) (s : State) (e : Event) (v : Env) : Monitor :=
  match step rev s e v with
  | some s' => ⟨some s', false⟩
  | none => ⟨none, true⟩

/-- Models one call to the v2 or proposed v3 irqexit handler for the target task.
Ordinary switch events are ignored until the task's monitor starts. -/
def dispatch (rev : Revision) (m : Option State) (e : Event) (v : Env) : Monitor :=
  match m, e with
  | none, .entry => process rev .idle e v
  | none, .exit =>
      if rev == .v2 && (!v.ownerCurrent || v.hard || !v.irqOff)
      then process rev .idle e v else ⟨some .idle, false⟩
  | none, _ => ⟨none, false⟩
  | some s, _ => process rev s e v

/-- Dropping the owner guard is semantics-preserving when that guard is true. -/
theorem step_eq_when_owner (s : State) (e : Event) (v : Env)
    (h : v.ownerCurrent = true) : step .v2 s e v = step .v3 s e v := by
  cases v with
  | mk hard irqOff owner =>
    cases owner <;> cases hard <;> cases irqOff <;> cases s <;> cases e <;> simp_all [step]

/-- With current ownership on entry, exit and switch-out, and valid exit context, the
proposed dispatch produces exactly the same result, including initial sync. -/
theorem dispatch_eq (m : Option State) (e : Event) (v : Env)
    (owner : e ≠ .switchIn → v.ownerCurrent = true)
    (exitContext : e = .exit → v.hard = false ∧ v.irqOff = true) :
    dispatch .v2 m e v = dispatch .v3 m e v := by
  cases m with
  | none =>
    cases v with
    | mk hard irqOff own =>
      cases own <;> cases hard <;> cases irqOff <;> cases e <;>
        simp_all [dispatch, process, step]
  | some s =>
    cases v with
    | mk hard irqOff own =>
      cases own <;> cases hard <;> cases irqOff <;> cases s <;> cases e <;>
        simp_all [dispatch, process, step]

/-- A single task's event stream, including the rejection flag for each event. -/
def run (rev : Revision) (m : Option State) : List (Event × Env) → List Bool × Option State
  | [] => ([], m)
  | (e, v) :: rest =>
    let result := dispatch rev m e v
    let tail := run rev result.state rest
    (result.rejected :: tail.1, tail.2)

/-- Under the stated per-event assumptions, all rejection reports and the
final monitor state agree on every finite single-task trace. -/
theorem run_eq (w : List (Event × Env)) (m : Option State)
    (h : ∀ p ∈ w, (p.1 ≠ .switchIn → p.2.ownerCurrent = true) ∧
      (p.1 = .exit → p.2.hard = false ∧ p.2.irqOff = true)) :
    run .v2 m w = run .v3 m w := by
  induction w generalizing m with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨e, v⟩ := p
    have hv := h (e, v) (by simp)
    have hr : ∀ p ∈ rest, (p.1 ≠ .switchIn → p.2.ownerCurrent = true) ∧
        (p.1 = .exit → p.2.hard = false ∧ p.2.irqOff = true) := by
      intro p hp
      exact h p (by simp [hp])
    simp only [run]
    rw [dispatch_eq m e v hv.1 hv.2]
    rw [ih _ hr]

/-- A first exit with bad context is rejected in v2 but skipped in the proposal. -/
theorem first_exit_difference :
    dispatch .v2 none .exit ⟨true, true, true⟩ = ⟨none, true⟩ ∧
    dispatch .v3 none .exit ⟨true, true, true⟩ = ⟨some .idle, false⟩ := by decide

/-- Once started, exit from idle is rejected in both versions. -/
theorem unmatched_exit (rev : Revision) (v : Env) :
    dispatch rev (some .idle) .exit v = ⟨none, true⟩ := by
  rfl

/-- Without the ownership assumption, removing the guard also changes
switch-out while rescheduling, even after the monitor has started. -/
theorem switch_out_difference :
    dispatch .v2 (some .rescheduling) .switchOut ⟨false, true, false⟩ = ⟨none, true⟩ ∧
    dispatch .v3 (some .rescheduling) .switchOut ⟨false, true, false⟩ = ⟨some .suspended, false⟩ := by decide
end IRQExit
end LinuxRV.IRQRevision
