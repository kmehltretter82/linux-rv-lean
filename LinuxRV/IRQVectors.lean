import LinuxRV.IRQRevision

/-! Executable, internal test vectors for the v2 irqstate handlers and the
proposed v3 irqexit handlers. A case starts with monitoring not yet synchronized.
The tests model one CPU or one target task, sequentially, while RV is enabled. -/
namespace LinuxRV.IRQVectors
open IRQRevision
namespace S
open IRQState

inductive Call where
  | hard (entry : Bool) (depth : Nat) (env : Env)
  | soft (entry fromHard : Bool) (env : Env)
  | resume (env : Env)
  | suspend (env : Env)
  deriving Repr

def event (c : Call) : Option (Mode × Event × Env) :=
  match c with
  | .hard entry depth v => (hardDispatch entry depth v).map fun (mode, e) => (mode, e, v)
  | .soft entry fromHard v => let (mode, e) := softDispatch entry fromHard v; some (mode, e, v)
  | .resume v => some (.startRun, .softResume, v)
  | .suspend v => some (.start, .softSuspend, v)

/-- Models the enabled DA startup/reset interface for a single handler event. -/
def exec (m : Option State) (c : Call) : Option State × Bool :=
  match event c with
  | none => (m, false)
  | some (mode, e, v) =>
    match m, mode with
    | none, .ordinary => (none, false)
    | none, .start => (some .idle, false)
    | _, _ =>
      match step (m.getD .idle) e v with
      | some s => (some s, false)
      | none => (none, true)

def execute (m : Option State) : List Call → List Bool × Option State
  | [] => ([], m)
  | c :: cs => let (next, failed) := exec m c
               let (results, final) := execute next cs
               (failed :: results, final)

def h0 : Env := ⟨true, false⟩
def h1 : Env := ⟨true, true⟩
def soft : Env := ⟨false, true⟩
def clear : Env := ⟨false, false⟩
def he : Call := .hard true 1 h0
def hx : Call := .hard false 1 h0
def se : Call := .soft true false soft
def sx : Call := .soft false false soft
def fhe : Call := .hard true 1 h1
def fhx : Call := .hard false 1 h1
def fe : Call := .soft true true soft
def fx : Call := .soft false true soft

/-- A sequence covers all twelve irqstate edges, in the order visited. -/
def positive : List Call := [he, hx, se, fhe, fhx, sx, he, fe, fhe, fhx, fx, hx,
  se, .suspend soft, .resume soft, sx]

def expectedStates : List State := [.hardirq, .idle, .softirq, .hardFromSoft, .softirq,
  .idle, .hardirq, .softFromHard, .hardFromSoftFromHard, .softFromHard, .hardirq,
  .idle, .softirq, .idle, .softirq, .idle]

def states (m : Option State) : List Call → List (Option State × Bool)
  | [] => []
  | c :: cs => let r := exec m c; r :: states r.1 cs

theorem positive_result : states none positive = expectedStates.map (fun s => (some s, false)) := by decide

def edges : List (State × Event × State) := [
  (.idle, .hardEntry, .hardirq), (.hardirq, .hardExit, .idle),
  (.idle, .softEntry, .softirq), (.softirq, .softExit, .idle),
  (.idle, .softResume, .softirq), (.softirq, .softSuspend, .idle),
  (.softirq, .hardEntry, .hardFromSoft), (.hardFromSoft, .hardExit, .softirq),
  (.hardirq, .softEntryFromHard, .softFromHard), (.softFromHard, .softExitToHard, .hardirq),
  (.softFromHard, .hardEntry, .hardFromSoftFromHard),
  (.hardFromSoftFromHard, .hardExit, .softFromHard)]

def visited (m : Option State) : List Call → List (State × Event × State)
  | [] => []
  | c :: cs =>
    let r := exec m c
    let edge := match event c, r with
      | some (mode, e, _), (some dst, false) =>
        if m.isSome || mode == .startRun then [(m.getD .idle, e, dst)] else []
      | _, _ => []
    edge ++ visited r.1 cs

theorem covers_all_edges : edges.all (fun e => decide (e ∈ visited none positive)) = true := by decide

/-- Each row holds a legal setup, a call that violates one guard atom, and the
expected rejection. Cases for both atoms are included for conjunction guards. -/
def negative : List (List Call × Call) := [
  ([], .hard true 1 clear), ([hx], .hard true 1 h1),
  ([], .soft true false h1), ([], .soft true false clear),
  ([], .resume h0),
  ([he], .hard false 1 clear), ([he], .hard false 1 h1),
  ([he], .soft true true h1), ([he], .soft true true clear),
  ([se], .soft false false h1), ([se], .soft false false clear),
  ([se], .suspend h0),
  ([se], .hard true 1 soft), ([se], .hard true 1 h0),
  ([se, fhe], .hard false 1 soft), ([se, fhe], .hard false 1 h0),
  ([he, fe], .soft false true h1), ([he, fe], .soft false true clear),
  ([he, fe], .hard true 1 soft), ([he, fe], .hard true 1 h0),
  ([he, fe, fhe], .hard false 1 soft), ([he, fe, fhe], .hard false 1 h0)]

def negativeOK (test : List Call × Call) : Bool :=
  let (results, state) := execute none test.1
  results.all (!·) && (exec state test.2).2

theorem negative_results : negative.all negativeOK = true := by decide

/-- The coverage obligations name both falsified atoms of each conjunction;
resume and suspend each have only the hardirq atom. -/
def guardObligations : List (State × Event × Env) := [
  (.idle, .hardEntry, clear), (.idle, .hardEntry, h1),
  (.idle, .softEntry, h1), (.idle, .softEntry, clear), (.idle, .softResume, h0),
  (.hardirq, .hardExit, clear), (.hardirq, .hardExit, h1),
  (.hardirq, .softEntryFromHard, h1), (.hardirq, .softEntryFromHard, clear),
  (.softirq, .softExit, h1), (.softirq, .softExit, clear), (.softirq, .softSuspend, h0),
  (.softirq, .hardEntry, soft), (.softirq, .hardEntry, h0),
  (.hardFromSoft, .hardExit, soft), (.hardFromSoft, .hardExit, h0),
  (.softFromHard, .softExitToHard, h1), (.softFromHard, .softExitToHard, clear),
  (.softFromHard, .hardEntry, soft), (.softFromHard, .hardEntry, h0),
  (.hardFromSoftFromHard, .hardExit, soft), (.hardFromSoftFromHard, .hardExit, h0)]

def negativeObservations : List (State × Event × Env) := negative.filterMap fun (setup, call) =>
  let (_, state) := execute none setup
  match state, event call with
  | some src, some (_, ev, env) => some (src, ev, env)
  | none, some (.startRun, ev, env) => some (.idle, ev, env)
  | _, _ => none

theorem covers_guard_negations :
    guardObligations.all (fun x => decide (x ∈ negativeObservations)) = true := by decide

/-- Both task flags set: one RT sched_switch suspends then resumes. -/
theorem rt_both_calls :
    exec (some .softirq) (.suspend soft) = (some .idle, false) ∧
    exec (some .idle) (.resume soft) = (some .softirq, false) := by decide

theorem nested_and_mid_interval :
  exec (some .hardirq) (.hard true 2 h0) = (some .hardirq, false) ∧
  exec none (.soft false false soft) = (some .idle, false) ∧
  exec none (.hard false 1 h0) = (some .idle, false) := by decide
end S

namespace X
open IRQExit
abbrev Sample := Event × Env
def ok : Env := ⟨false, true, true⟩
def badHard : Env := ⟨true, true, true⟩
def badIrq : Env := ⟨false, false, true⟩
/-- Switch events stand for the relevant task's side of a sched_switch call. -/
def positive : List Sample := [(.entry, ok), (.switchOut, ok), (.switchIn, ok),
  (.exit, ok), (.switchOut, ok), (.switchIn, ok)]
theorem positive_result :
    run .v3 none positive = ([false, false, false, false, false, false], some .idle) := by decide

def edges : List (State × Event × State) := [
  (.idle, .entry, .rescheduling), (.rescheduling, .exit, .idle),
  (.rescheduling, .switchOut, .suspended), (.suspended, .switchIn, .rescheduling),
  (.idle, .switchIn, .idle), (.idle, .switchOut, .idle)]

def visited (m : Option State) : List Sample → List (State × Event × State)
  | [] => []
  | (e, v) :: cs =>
    let r := dispatch .v3 m e v
    let edge := match r.state with
      | some dst => if !r.rejected && (m.isSome || e == .entry)
        then [(m.getD .idle, e, dst)] else []
      | none => []
    edge ++ visited r.state cs

theorem covers_all_edges : edges.all (fun e => decide (e ∈ visited none positive)) = true := by decide

def negative : List (List Sample × Sample) := [
  ([], (.entry, badHard)), ([], (.entry, badIrq)),
  ([ (.entry, ok) ], (.exit, badHard)), ([ (.entry, ok) ], (.exit, badIrq)),
  ([ (.entry, ok) ], (.switchOut, badHard)), ([ (.entry, ok) ], (.switchOut, badIrq)),
  ([ (.entry, ok), (.switchOut, ok) ], (.switchIn, badHard)),
  ([ (.entry, ok), (.switchOut, ok) ], (.switchIn, badIrq)),
  ([ (.entry, ok), (.exit, ok) ], (.switchOut, badHard)),
  ([ (.entry, ok), (.exit, ok) ], (.switchOut, badIrq)),
  ([ (.entry, ok), (.exit, ok) ], (.switchIn, badHard)),
  ([ (.entry, ok), (.exit, ok) ], (.switchIn, badIrq))]

def negativeOK (test : List Sample × Sample) : Bool :=
  let (results, state) := run .v3 none test.1
  results.all (!·) && (dispatch .v3 state test.2.1 test.2.2).rejected

theorem negative_results : negative.all negativeOK = true := by decide

def guardObligations : List (State × Event × Env) := [
  (.idle, .entry, badHard), (.idle, .entry, badIrq),
  (.rescheduling, .exit, badHard), (.rescheduling, .exit, badIrq),
  (.rescheduling, .switchOut, badHard), (.rescheduling, .switchOut, badIrq),
  (.suspended, .switchIn, badHard), (.suspended, .switchIn, badIrq),
  (.idle, .switchOut, badHard), (.idle, .switchOut, badIrq),
  (.idle, .switchIn, badHard), (.idle, .switchIn, badIrq)]

def negativeObservations : List (State × Event × Env) := negative.map fun (setup, sample) =>
  let (_, state) := run .v3 none setup
  (state.getD .idle, sample.1, sample.2)

theorem covers_guard_negations :
    guardObligations.all (fun x => decide (x ∈ negativeObservations)) = true := by decide

theorem mid_interval : dispatch .v3 none .exit ok = ⟨some .idle, false⟩ := by decide
end X
end LinuxRV.IRQVectors
