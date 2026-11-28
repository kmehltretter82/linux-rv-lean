import LinuxRV.IRQVectors

/-! Observability limits of the v2 `irqstate` monitor (`LinuxRV.IRQRevision.IRQState`).

`LinuxRV.IRQExitAnalysis` proves that no monitor over the `irqexit` alphabet can decide
faults in steps that alphabet does not observe. This file proves the corresponding result
for `irqstate`, and its kernel side is not abstract. It is a one-CPU, non-RT microstep
model of the v2 interrupt and softirq paths at `f3f79cfdf9cd387def9aa93102c4ce2cc8ec7726`.
The model is transcribed from `kernel/softirq.c` and `include/linux/hardirq.h`, not from
the `.dot` files. It also includes the fault variants of the 2026-11-28 lab commit
`0f0350cd148d2` (`rvexp_fault=e1a|e2|e4`) and the x86 `DEFINE_IDTENTRY_SYSVEC_SIMPLE` misuse
(E1b, lab commit `55c6ff34`). Faults are computed by the microstep semantics at the
kernel's own checkpoints. They are never read off an episode's name.

1. **Design gate (`exact_monitor_exists_iff`, `no_exact_monitor_of_collision`).**
   For any observation interface `view`, a monitor that decides a fault exactly exists
   iff the fault is constant on executions with equal views. One collision between a
   faulty and a fault-free execution rules out every monitor over that interface,
   whatever its automaton.
2. **No false alarms (`irqstate_accepts_valid`).** On every finite sequence of valid
   episodes, including inline and task-context softirqs with any number of nested
   hardirqs, the modeled v2 handlers (`IRQVectors.S.execute`) never react. This holds
   whether monitoring starts unsynchronized or in `idle`.
3. **Temporal kind, detected: E1a (`irqstate_detects_e1a`).** `irq_enter_rcu()` paired
   with `__irq_exit_raw()` leaves hardirq accounting open. The monitor stays silent through
   the faulty episode and reacts at the first boundary event of any later observable
   episode, as the lab's `hardirq_entry` on `in_hardirq` did 1.9 ms after the fault.
4. **State kind, invisible to `irqstate`: E2 (`e2_invisible_to_irqstate`,
   `lockdep_cross_check_exact`).** Ending lockdep's hardirq context at the start of
   `__irq_exit_rcu()` (the modern form of `f1a83e652bed`) leaves every sampled
   `(event, depth, hardirq_count, serving)` unchanged. Adding lockdep's
   `hardirq_context` to the two hardirq boundary events, and checking it against the
   depth, decides the fault exactly.
5. **Observation-gap kind, invisible to every interface at these tracepoints: E4 and E1b
   (`e4_invisible_to_every_record_view`, `e1b_invisible_to_every_record_view`).** The
   pre-`feb5c9a2447a` exit order and a fully raw vector whose handler raised a softirq
   produce tracepoint records identical, field for field, to fault-free executions. This
   includes lockdep. No per-record interface derived from these four tracepoints, and no
   automaton, can separate them. Only moving or adding tracepoints can.
6. **Universal twin (`every_e1a_free_execution_has_valid_twin`,
   `irqstate_silent_without_e1a`).** Every execution without E1a has a fault-free valid
   twin with the same `irqstate` observation. Without E2 it also has the same full
   records. Hence v2 `irqstate` is silent on all E2, E4 and E1b executions, matching
   the lab's `e2-mon`, `e4-mon` and `x86-e1b-mon` cells.

Model limits: one CPU, sequential, non-RT, monitor enabled and probes attached, complete
ordered delivery. NMIs, nested hardirqs inside hardirqs (handler depth > 1), softirq
raises by nested hardirqs, `ksoftirqd` wakeups and RT `sched_switch` events are outside
the model, so E3 is too. Each episode starts in quiescent task context `k0`. Valid, E2 and
E4 episodes provably return to `k0` (`restoring_runs_thread`), so for executions made of
them, per-episode semantics coincides with threading the kernel state through. E1a and
raised E1b episodes leave `acctOpen` or `pending` set. The model reports the fault at the
interrupt return and does not model later consequences. -/
namespace LinuxRV.IRQStateObservability

open LinuxRV.IRQRevision
open LinuxRV.IRQVectors

/-! ### Part 1: Observation design gate (generic) -/

/-- Two executions with the same observation get the same verdict from every monitor. -/
theorem same_verdict_of_same_view {X O α : Type} (view : X → O) (M : O → α) {x y : X}
    (h : view x = view y) : M (view x) = M (view y) :=
  congrArg M h

/-- A single collision between a fault-free and a faulty execution rules out every
sound and complete monitor over that observation interface. -/
theorem no_exact_monitor_of_collision {X O : Type} (view : X → O) (Bad : X → Prop)
    {good bad : X} (hv : view good = view bad) (hg : ¬ Bad good) (hb : Bad bad) :
    ¬ ∃ M : O → Bool, ∀ x, M (view x) = true ↔ Bad x := by
  rintro ⟨M, hM⟩
  have h := (hM bad).mpr hb
  rw [← hv] at h
  exact hg ((hM good).mp h)

/-- **Design gate.** A monitor that decides `Bad` exactly from `view` exists iff `Bad` is
constant on every set of executions with the same view. -/
theorem exact_monitor_exists_iff {X O : Type} (view : X → O) (Bad : X → Prop) :
    (∃ M : O → Prop, ∀ x, M (view x) ↔ Bad x) ↔
      ∀ x y, view x = view y → (Bad x ↔ Bad y) := by
  constructor
  · rintro ⟨M, hM⟩ x y h
    rw [← hM x, ← hM y, h]
  · intro h
    refine ⟨fun o => ∃ y, view y = o ∧ Bad y, fun x => ⟨?_, fun hx => ⟨x, rfl, hx⟩⟩⟩
    rintro ⟨y, hy, hBad⟩
    exact (h y x hy).mp hBad

/-! ### Part 2: Source-derived kernel microstep model (non-RT, one CPU) -/

/-- Per-CPU context record. `hardDepth` is `hardirq_count() >> HARDIRQ_SHIFT`, `serving` is
`in_serving_softirq()`, and `ldHard` is lockdep's per-CPU `hardirq_context`. `ldSaved` is
the `in_hardirq` local of `handle_softirqs()`, set by `lockdep_softirq_start()`. `pending`
means `local_softirq_pending() != 0`, and `acctOpen` means `account_hardirq_enter()` ran
without the matching `account_hardirq_exit()`. -/
structure KState where
  hardDepth : Nat
  serving : Bool
  ldHard : Nat
  ldSaved : Bool
  pending : Bool
  acctOpen : Bool
  deriving DecidableEq, Repr

/-- Quiescent task context: no hardirq, no softirq, nothing pending. -/
def k0 : KState := ⟨0, false, 0, false, false, false⟩

/-- The four v2 context tracepoints: `hardirq_context_entry` (`softirq.c:970`),
`hardirq_context_exit` (`:1049`), `softirq_context_entry` (`:880`) and
`softirq_context_exit` (`:934`). -/
inductive TpEvent where
  | hardEntry
  | hardExit
  | softEntry (fromHard : Bool)
  | softExit (fromHard : Bool)
  deriving DecidableEq, Repr

/-- Everything sampled at a tracepoint: the event and its arguments, the live
`hardirq_count()` and `in_serving_softirq()` read by the handler, and lockdep's
`hardirq_context` as an extended handler could read it. -/
structure TpRecord where
  ev : TpEvent
  depth : Nat
  hard : Bool
  serving : Bool
  ldHard : Nat
  deriving DecidableEq, Repr

/-- Kernel faults, reported at the kernel's own checkpoints. -/
inductive Fault where
  /-- `tick_irq_exit()` reached with `HARDIRQ_OFFSET` dropped (`feb5c9a2447a` invariant). -/
  | tickOutsideHardirq
  /-- `tick_irq_exit()` reached with lockdep outside hardirq context (`f1a83e652bed`). -/
  | tickOutsideLockdepHardirq
  /-- Return to task context from an interrupt with softirq work left unserved. -/
  | softirqLeftPending
  /-- Return to task context with hardirq time accounting left open. -/
  | hardirqAccountingOpen
  deriving DecidableEq, Repr

/-- Primitive kernel actions. -/
inductive Micro where
  /-- `preempt_count_add(HARDIRQ_OFFSET)` (`hardirq.h:48`). -/
  | pcAddHard
  /-- `preempt_count_sub(HARDIRQ_OFFSET)` (`softirq.c:1078`, `hardirq.h:77`). -/
  | pcSubHard
  /-- `lockdep_hardirq_enter()` (`hardirq.h:49`). -/
  | ldHardEnter
  /-- `lockdep_hardirq_exit()` (`softirq.c:1090`, `hardirq.h:76`). -/
  | ldHardExit
  /-- `account_hardirq_enter()` (`softirq.c:969`). -/
  | acctEnter
  /-- `account_hardirq_exit()` (`softirq.c:1020`). -/
  | acctExit
  /-- The handler raises a softirq (`__raise_softirq_irqoff()`, `softirq.c:1135`). -/
  | raise
  /-- `softirq_handle_begin()` from IRQ exit swaps `HARDIRQ_OFFSET` for `SOFTIRQ_OFFSET`
  (`softirq.c:537`). -/
  | swapToSoft
  /-- `softirq_handle_end()` from IRQ exit swaps back (`softirq.c:553`). -/
  | swapToHard
  /-- `softirq_handle_begin()` outside hardirq: `__local_bh_disable_ip(SOFTIRQ_OFFSET)`
  (`softirq.c:526`). -/
  | bhServeBegin
  /-- `softirq_handle_end()` outside hardirq: `__local_bh_enable(SOFTIRQ_OFFSET)`
  (`softirq.c:547`). -/
  | bhServeEnd
  /-- `lockdep_softirq_start()` (`softirq.c:832–843`). -/
  | ldSoftStart
  /-- `lockdep_softirq_end()` (`softirq.c:846–852`). -/
  | ldSoftEnd
  /-- `set_softirq_pending(0)` and the handler loop (`softirq.c:884–918`). -/
  | servePending
  /-- `tick_irq_exit()` (`softirq.c:1044`): checkpoint for both context invariants. -/
  | tickIrqExit
  /-- Return from the interrupt (arch entry code): checkpoint for work left behind on
  return to task context. -/
  | irqReturn
  /-- A context tracepoint fires and the handler samples the context. -/
  | tp (ev : TpEvent)
  deriving DecidableEq, Repr

def sample (k : KState) (ev : TpEvent) : TpRecord :=
  ⟨ev, k.hardDepth, k.hardDepth != 0, k.serving, k.ldHard⟩

def stepMicro (k : KState) : Micro → KState × Option TpRecord × List Fault
  | .pcAddHard => ({ k with hardDepth := k.hardDepth + 1 }, none, [])
  | .pcSubHard => ({ k with hardDepth := k.hardDepth - 1 }, none, [])
  | .ldHardEnter => ({ k with ldHard := k.ldHard + 1 }, none, [])
  | .ldHardExit => ({ k with ldHard := k.ldHard - 1 }, none, [])
  | .acctEnter => ({ k with acctOpen := true }, none, [])
  | .acctExit => ({ k with acctOpen := false }, none, [])
  | .raise => ({ k with pending := true }, none, [])
  | .swapToSoft => ({ k with hardDepth := k.hardDepth - 1, serving := true }, none, [])
  | .swapToHard => ({ k with hardDepth := k.hardDepth + 1, serving := false }, none, [])
  | .bhServeBegin => ({ k with serving := true }, none, [])
  | .bhServeEnd => ({ k with serving := false }, none, [])
  | .ldSoftStart =>
      if k.ldHard != 0 then ({ k with ldHard := k.ldHard - 1, ldSaved := true }, none, [])
      else ({ k with ldSaved := false }, none, [])
  | .ldSoftEnd =>
      if k.ldSaved then ({ k with ldHard := k.ldHard + 1, ldSaved := false }, none, [])
      else (k, none, [])
  | .servePending => ({ k with pending := false }, none, [])
  | .tickIrqExit =>
      (k, none,
        (if k.hardDepth == 0 then [.tickOutsideHardirq] else []) ++
        (if k.ldHard == 0 then [.tickOutsideLockdepHardirq] else []))
  | .irqReturn =>
      if k.hardDepth == 0 && !k.serving then
        (k, none,
          (if k.acctOpen then [.hardirqAccountingOpen] else []) ++
          (if k.pending then [.softirqLeftPending] else []))
      else (k, none, [])
  | .tp ev => (k, some (sample k ev), [])

def runMicro (k : KState) : List Micro → KState × List TpRecord × List Fault
  | [] => (k, [], [])
  | μ :: rest =>
    let r := stepMicro k μ
    let t := runMicro r.1 rest
    (t.1, r.2.1.toList ++ t.2.1, r.2.2 ++ t.2.2)

theorem runMicro_append (k : KState) (p q : List Micro) :
    runMicro k (p ++ q) =
      ((runMicro (runMicro k p).1 q).1,
       (runMicro k p).2.1 ++ (runMicro (runMicro k p).1 q).2.1,
       (runMicro k p).2.2 ++ (runMicro (runMicro k p).1 q).2.2) := by
  induction p generalizing k with
  | nil => simp [runMicro]
  | cons μ rest ih => simp [runMicro, ih, List.append_assoc]

/-! #### Kernel paths -/

/-- `irq_enter_rcu()` (`softirq.c:954–971`) through `__irq_enter_raw()`. -/
def enterRcu : List Micro := [.pcAddHard, .ldHardEnter, .acctEnter, .tp .hardEntry]

/-- The end of `__irq_exit_rcu()` and `irq_exit_rcu()` (`softirq.c:1044–1091`). -/
def exitRcuTail : List Micro := [.tickIrqExit, .tp .hardExit, .pcSubHard, .ldHardExit, .irqReturn]

/-- A hardirq that arrives while softirqs run. `irq_count() != HARDIRQ_OFFSET`, so its exit
serves no softirq (`softirq.c:1026`). The modeled handler raises none. -/
def nestedMicro : List Micro := enterRcu ++ [.acctExit] ++ exitRcuTail

def nestedPath (n : Nat) : List Micro := (List.replicate n nestedMicro).flatten

/-- `handle_softirqs()` entered from IRQ exit, up to the IRQ-enabled handler loop. -/
def inlineSoftirqPre : List Micro :=
  [.swapToSoft, .ldSoftStart, .tp (.softEntry true), .servePending]

def inlineSoftirqPost : List Micro := [.tp (.softExit true), .ldSoftEnd, .swapToHard]

/-- `handle_softirqs()` from task context (`__local_bh_enable_ip()` → `do_softirq()`, or
`ksoftirqd`). -/
def taskSoftirqPre : List Micro :=
  [.bhServeBegin, .ldSoftStart, .tp (.softEntry false), .servePending]

def taskSoftirqPost : List Micro := [.tp (.softExit false), .ldSoftEnd, .bhServeEnd]

/-- Kernel episodes on one CPU, each starting in quiescent task context. -/
inductive Episode where
  /-- `irq_enter_rcu()` … `irq_exit_rcu()`. `some n`: the handler raised a softirq, so the
  exit serves it inline while `n` nested hardirqs arrive. -/
  | irq (softirq : Option Nat)
  /-- A task-context softirq run with `n` nested hardirqs. -/
  | taskSoftirq (nested : Nat)
  /-- A fully raw vector, `__irq_enter_raw()` … `__irq_exit_raw()` (x86
  `DEFINE_IDTENTRY_SYSVEC_SIMPLE`, `idtentry.h:290`). Fault-free only if the handler raises
  no softirq. Raised, this is E1b. -/
  | rawIRQ (raised : Bool)
  /-- E1a: `irq_enter_rcu()` paired with `__irq_exit_raw()`. -/
  | e1aHalfRaw (raised : Bool)
  /-- E2: `lockdep_hardirq_exit()` moved to the start of `__irq_exit_rcu()`. -/
  | e2LockdepEarly (softirq : Option Nat)
  /-- E4: `rvexp_irq_exit_old()`, the exit order before `feb5c9a2447a`. -/
  | e4OldOrder (softirq : Option Nat)
  deriving DecidableEq, Repr

/-- Microstep expansion of each episode. -/
def path : Episode → List Micro
  | .irq none => enterRcu ++ [.acctExit] ++ exitRcuTail
  | .irq (some n) =>
      (enterRcu ++ [.raise, .acctExit] ++ inlineSoftirqPre) ++ nestedPath n ++
        (inlineSoftirqPost ++ exitRcuTail)
  | .taskSoftirq n => ([.raise] ++ taskSoftirqPre) ++ nestedPath n ++ taskSoftirqPost
  | .rawIRQ b =>
      [.pcAddHard, .ldHardEnter] ++ (if b then [.raise] else []) ++
        [.ldHardExit, .pcSubHard, .irqReturn]
  | .e1aHalfRaw b =>
      enterRcu ++ (if b then [.raise] else []) ++ [.ldHardExit, .pcSubHard, .irqReturn]
  | .e2LockdepEarly none =>
      enterRcu ++ [.ldHardExit, .acctExit, .tickIrqExit, .tp .hardExit, .pcSubHard, .irqReturn]
  | .e2LockdepEarly (some n) =>
      (enterRcu ++ [.raise, .ldHardExit, .acctExit] ++ inlineSoftirqPre) ++ nestedPath n ++
        (inlineSoftirqPost ++ [.tickIrqExit, .tp .hardExit, .pcSubHard, .irqReturn])
  | .e4OldOrder none =>
      enterRcu ++ [.acctExit, .tp .hardExit, .pcSubHard, .tickIrqExit, .ldHardExit, .irqReturn]
  | .e4OldOrder (some n) =>
      (enterRcu ++ [.raise, .acctExit, .tp .hardExit, .pcSubHard] ++ taskSoftirqPre) ++
        nestedPath n ++ (taskSoftirqPost ++ [.tickIrqExit, .ldHardExit, .irqReturn])

def runEp (ep : Episode) : KState × List TpRecord × List Fault := runMicro k0 (path ep)

/-- Tracepoint records of an execution. -/
def trace (x : List Episode) : List TpRecord := x.flatMap fun ep => (runEp ep).2.1

/-- Kernel faults of an execution. -/
def faults (x : List Episode) : List Fault := x.flatMap fun ep => (runEp ep).2.2

def Episode.Valid : Episode → Prop
  | .irq _ | .taskSoftirq _ => True
  | .rawIRQ b => b = false
  | _ => False

def Episode.IsE1a : Episode → Prop
  | .e1aHalfRaw _ => True
  | _ => False

def Episode.IsE2 : Episode → Prop
  | .e2LockdepEarly _ => True
  | _ => False

/-! #### Closed forms -/

/-- Kernel state during a softirq's handler loop, after `set_softirq_pending(0)`. -/
def softBody (saved : Bool) : KState := ⟨0, true, 0, saved, false, false⟩

def hE (serving : Bool) : TpRecord := ⟨.hardEntry, 1, true, serving, 1⟩
def hX (serving : Bool) (ld : Nat) : TpRecord := ⟨.hardExit, 1, true, serving, ld⟩
def sE (fromHard : Bool) : TpRecord := ⟨.softEntry fromHard, 0, false, true, 0⟩
def sX (fromHard : Bool) : TpRecord := ⟨.softExit fromHard, 0, false, true, 0⟩

def nestedRecs : List TpRecord := [hE true, hX true 1]
def nestedTrace (n : Nat) : List TpRecord := (List.replicate n nestedRecs).flatten

theorem nestedPath_succ (n : Nat) : nestedPath (n + 1) = nestedMicro ++ nestedPath n := by
  simp [nestedPath, List.replicate_succ]

theorem nestedTrace_succ (n : Nat) : nestedTrace (n + 1) = nestedRecs ++ nestedTrace n := by
  simp [nestedTrace, List.replicate_succ]

theorem runMicro_nestedMicro (b : Bool) :
    runMicro (softBody b) nestedMicro = (softBody b, nestedRecs, []) := by
  cases b <;> decide

/-- Nested hardirqs during a softirq leave the softirq context unchanged and are fault-free. -/
theorem runMicro_nestedPath (b : Bool) (n : Nat) :
    runMicro (softBody b) (nestedPath n) = (softBody b, nestedTrace n, []) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nestedPath_succ, runMicro_append, runMicro_nestedMicro]
    simp only [ih, nestedTrace_succ, List.append_nil]

theorem runEp_irq_none : runEp (.irq none) = (k0, [hE false, hX false 1], []) := by decide

theorem runEp_irq_some (n : Nat) :
    runEp (.irq (some n)) =
      (k0, [hE false, sE true] ++ nestedTrace n ++ [sX true, hX false 1], []) := by
  have hA : runMicro k0 (enterRcu ++ [.raise, .acctExit] ++ inlineSoftirqPre) =
      (softBody true, [hE false, sE true], []) := by decide
  have hB : runMicro (softBody true) (inlineSoftirqPost ++ exitRcuTail) =
      (k0, [sX true, hX false 1], []) := by decide
  simp only [runEp, path, runMicro_append, hA, runMicro_nestedPath, hB, List.append_nil]

theorem runEp_taskSoftirq (n : Nat) :
    runEp (.taskSoftirq n) = (k0, [sE false] ++ nestedTrace n ++ [sX false], []) := by
  have hA : runMicro k0 ([.raise] ++ taskSoftirqPre) = (softBody false, [sE false], []) := by
    decide
  have hB : runMicro (softBody false) taskSoftirqPost = (k0, [sX false], []) := by decide
  simp only [runEp, path, runMicro_append, hA, runMicro_nestedPath, hB, List.append_nil]

theorem runEp_rawIRQ (b : Bool) :
    runEp (.rawIRQ b) =
      (⟨0, false, 0, false, b, false⟩, [], if b then [.softirqLeftPending] else []) := by
  cases b <;> decide

theorem runEp_e1a (b : Bool) :
    runEp (.e1aHalfRaw b) =
      (⟨0, false, 0, false, b, true⟩, [hE false],
        [.hardirqAccountingOpen] ++ (if b then [.softirqLeftPending] else [])) := by
  cases b <;> decide

theorem runEp_e2_none :
    runEp (.e2LockdepEarly none) = (k0, [hE false, hX false 0], [.tickOutsideLockdepHardirq]) := by
  decide

theorem runEp_e2_some (n : Nat) :
    runEp (.e2LockdepEarly (some n)) =
      (k0, [hE false, sE true] ++ nestedTrace n ++ [sX true, hX false 0],
        [.tickOutsideLockdepHardirq]) := by
  have hA : runMicro k0 (enterRcu ++ [.raise, .ldHardExit, .acctExit] ++ inlineSoftirqPre) =
      (softBody false, [hE false, sE true], []) := by decide
  have hB : runMicro (softBody false)
      (inlineSoftirqPost ++ [.tickIrqExit, .tp .hardExit, .pcSubHard, .irqReturn]) =
      (k0, [sX true, hX false 0], [.tickOutsideLockdepHardirq]) := by decide
  simp only [runEp, path, runMicro_append, hA, runMicro_nestedPath, hB, List.append_nil,
    List.nil_append]

theorem runEp_e4_none :
    runEp (.e4OldOrder none) = (k0, [hE false, hX false 1], [.tickOutsideHardirq]) := by
  decide

theorem runEp_e4_some (n : Nat) :
    runEp (.e4OldOrder (some n)) =
      (k0, [hE false, hX false 1, sE false] ++ nestedTrace n ++ [sX false],
        [.tickOutsideHardirq]) := by
  have hA : runMicro k0
      (enterRcu ++ [.raise, .acctExit, .tp .hardExit, .pcSubHard] ++ taskSoftirqPre) =
      (softBody true, [hE false, hX false 1, sE false], []) := by decide
  have hB : runMicro (softBody true)
      (taskSoftirqPost ++ [.tickIrqExit, .ldHardExit, .irqReturn]) =
      (k0, [sX false], [.tickOutsideHardirq]) := by decide
  simp only [runEp, path, runMicro_append, hA, runMicro_nestedPath, hB, List.append_nil,
    List.nil_append]

/-- Exactly the valid episodes are fault-free. -/
theorem faults_nil_iff_valid (ep : Episode) : (runEp ep).2.2 = [] ↔ ep.Valid := by
  cases ep with
  | irq s => cases s <;> simp [runEp_irq_none, runEp_irq_some, Episode.Valid]
  | taskSoftirq n => simp [runEp_taskSoftirq, Episode.Valid]
  | rawIRQ b => cases b <;> simp [runEp_rawIRQ, Episode.Valid]
  | e1aHalfRaw b => cases b <;> simp [runEp_e1a, Episode.Valid]
  | e2LockdepEarly s => cases s <;> simp [runEp_e2_none, runEp_e2_some, Episode.Valid]
  | e4OldOrder s => cases s <;> simp [runEp_e4_none, runEp_e4_some, Episode.Valid]

/-- Episodes that return the CPU to quiescent task context. -/
def Episode.Restores : Episode → Prop
  | .rawIRQ b => b = false
  | .e1aHalfRaw _ => False
  | _ => True

theorem runEp_restores (ep : Episode) (h : ep.Restores) : (runEp ep).1 = k0 := by
  cases ep with
  | irq s => cases s <;> simp [runEp_irq_none, runEp_irq_some]
  | taskSoftirq n => simp [runEp_taskSoftirq]
  | rawIRQ b =>
    simp only [Episode.Restores] at h
    subst h
    rfl
  | e1aHalfRaw b => exact absurd h id
  | e2LockdepEarly s => cases s <;> simp [runEp_e2_none, runEp_e2_some]
  | e4OldOrder s => cases s <;> simp [runEp_e4_none, runEp_e4_some]

/-- For executions of restoring episodes, per-episode semantics from `k0` coincides with
running the concatenated microsteps with the kernel state threaded through. -/
theorem restoring_runs_thread (x : List Episode) (h : ∀ ep ∈ x, ep.Restores) :
    runMicro k0 (x.flatMap path) = (k0, trace x, faults x) := by
  induction x with
  | nil => rfl
  | cons ep rest ih =>
    have hep := runEp_restores ep (h ep (by simp))
    have hrest := ih (fun e he => h e (by simp [he]))
    simp only [List.flatMap_cons, runMicro_append]
    have hr : runMicro k0 (path ep) = runEp ep := rfl
    rw [hr, hep, hrest]
    simp [trace, faults]

/-! ### Part 3: The `irqstate` interface and the v2 handlers -/

/-- What the v2 `irqstate` handlers can read at a tracepoint: the event, its depth
argument, `hardirq_count()` and `in_serving_softirq()` (`irqstate.c` `ha_get_env`). -/
structure StdObs where
  ev : TpEvent
  depth : Nat
  hard : Bool
  serving : Bool
  deriving DecidableEq, Repr

def stdView (r : TpRecord) : StdObs := ⟨r.ev, r.depth, r.hard, r.serving⟩

def stdTrace (x : List Episode) : List StdObs := (trace x).map stdView

/-- The v2 handler call for an observation (`handle_hardirq_entry`/`_exit`,
`handle_softirq_entry`/`_exit`). -/
def callOf (o : StdObs) : S.Call :=
  match o.ev with
  | .hardEntry => .hard true o.depth ⟨o.hard, o.serving⟩
  | .hardExit => .hard false o.depth ⟨o.hard, o.serving⟩
  | .softEntry fh => .soft true fh ⟨o.hard, o.serving⟩
  | .softExit fh => .soft false fh ⟨o.hard, o.serving⟩

/-- Verdict of the modeled v2 `irqstate` handlers (`IRQVectors.S.execute`). -/
def irqstate (m : Option IRQState.State) (os : List StdObs) :
    List Bool × Option IRQState.State :=
  S.execute m (os.map callOf)

theorem execute_append (m : Option IRQState.State) (a b : List S.Call) :
    S.execute m (a ++ b) =
      ((S.execute m a).1 ++ (S.execute (S.execute m a).2 b).1,
       (S.execute (S.execute m a).2 b).2) := by
  induction a generalizing m with
  | nil => simp [S.execute]
  | cons c cs ih => simp [S.execute, ih]

theorem irqstate_append (m : Option IRQState.State) (a b : List StdObs) :
    irqstate m (a ++ b) =
      ((irqstate m a).1 ++ (irqstate (irqstate m a).2 b).1,
       (irqstate (irqstate m a).2 b).2) := by
  simp [irqstate, execute_append]

/-- Unsynchronized or synchronized in `idle`. -/
def Quiet (m : Option IRQState.State) : Prop := m = none ∨ m = some .idle

theorem irqstate_nested (st : IRQState.State) (hst : st = .softFromHard ∨ st = .softirq)
    (n : Nat) :
    (irqstate (some st) ((nestedTrace n).map stdView)).1.any id = false ∧
    (irqstate (some st) ((nestedTrace n).map stdView)).2 = some st := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have h1 : irqstate (some st) (nestedRecs.map stdView) = ([false, false], some st) := by
      rcases hst with rfl | rfl <;> decide
    rw [nestedTrace_succ, List.map_append, irqstate_append, h1]
    simp only [ih.2, List.any_append, ih.1]
    decide

/-- One valid episode from a quiet monitor causes no reaction and leaves it quiet. -/
theorem irqstate_valid_episode (ep : Episode) (hv : ep.Valid) (m : Option IRQState.State)
    (hm : Quiet m) :
    (irqstate m ((runEp ep).2.1.map stdView)).1.any id = false ∧
    Quiet (irqstate m ((runEp ep).2.1.map stdView)).2 := by
  cases ep with
  | irq s =>
    cases s with
    | none =>
      rw [runEp_irq_none]
      rcases hm with rfl | rfl <;> exact ⟨by decide, Or.inr (by decide)⟩
    | some n =>
      rw [runEp_irq_some]
      have hA : irqstate m ([hE false, sE true].map stdView) =
          ([false, false], some .softFromHard) := by
        rcases hm with rfl | rfl <;> decide
      have hB : irqstate (some .softFromHard) ([sX true, hX false 1].map stdView) =
          ([false, false], some .idle) := by decide
      have hN := irqstate_nested .softFromHard (Or.inl rfl) n
      simp only [List.map_append, irqstate_append, hA, hN.2, hB, List.any_append, hN.1]
      exact ⟨by decide, Or.inr rfl⟩
  | taskSoftirq n =>
    rw [runEp_taskSoftirq]
    have hA : irqstate m ([sE false].map stdView) = ([false], some .softirq) := by
      rcases hm with rfl | rfl <;> decide
    have hB : irqstate (some .softirq) ([sX false].map stdView) = ([false], some .idle) := by
      decide
    have hN := irqstate_nested .softirq (Or.inr rfl) n
    simp only [List.map_append, irqstate_append, hA, hN.2, hB, List.any_append, hN.1]
    exact ⟨by decide, Or.inr rfl⟩
  | rawIRQ b =>
    simp only [Episode.Valid] at hv
    subst hv
    rw [runEp_rawIRQ]
    exact ⟨rfl, hm⟩
  | e1aHalfRaw _ => exact absurd hv id
  | e2LockdepEarly _ => exact absurd hv id
  | e4OldOrder _ => exact absurd hv id

theorem stdTrace_cons (ep : Episode) (x : List Episode) :
    stdTrace (ep :: x) = (runEp ep).2.1.map stdView ++ stdTrace x := by
  simp [stdTrace, trace]

theorem irqstate_valid_quiet (x : List Episode) (hv : ∀ ep ∈ x, ep.Valid)
    (m : Option IRQState.State) (hm : Quiet m) :
    (irqstate m (stdTrace x)).1.any id = false ∧ Quiet (irqstate m (stdTrace x)).2 := by
  induction x generalizing m with
  | nil => exact ⟨rfl, hm⟩
  | cons ep rest ih =>
    have h1 := irqstate_valid_episode ep (hv ep (by simp)) m hm
    have h2 := ih (fun e he => hv e (by simp [he])) _ h1.2
    rw [stdTrace_cons, irqstate_append]
    simp only [List.any_append, h1.1, h2.1, Bool.false_or]
    exact ⟨trivial, h2.2⟩

/-- **No false alarms.** On every valid execution, the v2 `irqstate` handlers never react,
whether monitoring starts unsynchronized or in `idle`. -/
theorem irqstate_accepts_valid (x : List Episode) (hv : ∀ ep ∈ x, ep.Valid) :
    (irqstate none (stdTrace x)).1.any id = false ∧
    (irqstate (some .idle) (stdTrace x)).1.any id = false :=
  ⟨(irqstate_valid_quiet x hv none (Or.inl rfl)).1,
   (irqstate_valid_quiet x hv (some .idle) (Or.inr rfl)).1⟩

/-! ### Part 4: Temporal kind (E1a), detected -/

/-- Every observable episode starts with a task-context `hardirq_entry` or
`softirq_entry`. -/
theorem trace_head (x : List Episode) :
    trace x = [] ∨ ∃ r rest, (r = hE false ∨ r = sE false) ∧ trace x = r :: rest := by
  induction x with
  | nil => exact Or.inl rfl
  | cons ep rest ih =>
    have hcons : trace (ep :: rest) = (runEp ep).2.1 ++ trace rest := by simp [trace]
    rw [hcons]
    cases ep with
    | irq s =>
      cases s with
      | none => exact Or.inr ⟨_, _, Or.inl rfl, by rw [runEp_irq_none]; rfl⟩
      | some n => exact Or.inr ⟨_, _, Or.inl rfl, by rw [runEp_irq_some]; rfl⟩
    | taskSoftirq n => exact Or.inr ⟨_, _, Or.inr rfl, by rw [runEp_taskSoftirq]; rfl⟩
    | rawIRQ b => rw [runEp_rawIRQ]; simpa using ih
    | e1aHalfRaw b => exact Or.inr ⟨_, _, Or.inl rfl, by rw [runEp_e1a]; rfl⟩
    | e2LockdepEarly s =>
      cases s with
      | none => exact Or.inr ⟨_, _, Or.inl rfl, by rw [runEp_e2_none]; rfl⟩
      | some n => exact Or.inr ⟨_, _, Or.inl rfl, by rw [runEp_e2_some]; rfl⟩
    | e4OldOrder s =>
      cases s with
      | none => exact Or.inr ⟨_, _, Or.inl rfl, by rw [runEp_e4_none]; rfl⟩
      | some n => exact Or.inr ⟨_, _, Or.inl rfl, by rw [runEp_e4_some]; rfl⟩

/-- **E1a is detected at the next observable boundary.** After any valid prefix, an
`irq_enter_rcu()`/`__irq_exit_raw()` episode is a kernel fault (open hardirq accounting).
`irqstate` stays silent through the prefix and the faulty episode and is left in
`in_hardirq`. It rejects the very first boundary event of any later observable episode,
a task-context `hardirq_entry` or `softirq_entry`. If nothing observable follows, the
fault goes unreported. -/
theorem irqstate_detects_e1a (p x : List Episode) (hp : ∀ ep ∈ p, ep.Valid) (b : Bool)
    (hx : trace x ≠ []) :
    Fault.hardirqAccountingOpen ∈ faults [.e1aHalfRaw b] ∧
    (irqstate none (stdTrace (p ++ [.e1aHalfRaw b]))).1.any id = false ∧
    (irqstate none (stdTrace (p ++ [.e1aHalfRaw b]))).2 = some .hardirq ∧
    (irqstate (some .hardirq) (stdTrace x)).1.head? = some true ∧
    (irqstate none (stdTrace (p ++ [.e1aHalfRaw b] ++ x))).1.any id = true := by
  have hP := irqstate_valid_quiet p hp none (Or.inl rfl)
  have hE1a : ∀ m, Quiet m → irqstate m ((runEp (.e1aHalfRaw b)).2.1.map stdView) =
      ([false], some .hardirq) := by
    intro m hm
    rw [runEp_e1a]
    dsimp only
    rcases hm with rfl | rfl <;> decide
  have hpre : irqstate none (stdTrace (p ++ [.e1aHalfRaw b])) =
      ((irqstate none (stdTrace p)).1 ++ [false], some .hardirq) := by
    have hs : stdTrace (p ++ [.e1aHalfRaw b]) =
        stdTrace p ++ (runEp (.e1aHalfRaw b)).2.1.map stdView := by
      simp [stdTrace, trace, List.flatMap_append]
    rw [hs, irqstate_append, hE1a _ hP.2]
  have hhead : (irqstate (some .hardirq) (stdTrace x)).1.head? = some true := by
    rcases trace_head x with h | ⟨r, rest, hr, h⟩
    · exact absurd h hx
    · have hstd : stdTrace x = [stdView r] ++ rest.map stdView := by simp [stdTrace, h]
      have hrej : (irqstate (some .hardirq) [stdView r]).1 = [true] := by
        rcases hr with rfl | rfl <;> decide
      rw [hstd, irqstate_append, hrej]
      rfl
  refine ⟨?_, ?_, ?_, hhead, ?_⟩
  · simp [faults, runEp_e1a]
  · rw [hpre]
    simp [List.any_append, hP.1]
  · rw [hpre]
  · have hs : stdTrace (p ++ [.e1aHalfRaw b] ++ x) =
        stdTrace (p ++ [.e1aHalfRaw b]) ++ stdTrace x := by
      simp [stdTrace, trace, List.flatMap_append]
    rw [hs, irqstate_append, hpre]
    have hany : (irqstate (some .hardirq) (stdTrace x)).1.any id = true := by
      cases hl : (irqstate (some .hardirq) (stdTrace x)).1 with
      | nil => rw [hl] at hhead; cases hhead
      | cons c cs =>
        rw [hl] at hhead
        simp only [List.head?_cons, Option.some.injEq] at hhead
        simp [hhead]
    simp [List.any_append, hany]

/-! ### Part 5: State kind (E2), invisible to `irqstate`, decided by a lockdep sample -/

/-- E2's records differ from the valid twin's only in lockdep's `hardirq_context`. -/
theorem e2_invisible_to_irqstate (s : Option Nat) :
    stdTrace [.e2LockdepEarly s] = stdTrace [.irq s] ∧
    Fault.tickOutsideLockdepHardirq ∈ faults [.e2LockdepEarly s] ∧
    faults [.irq s] = [] := by
  cases s with
  | none =>
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [stdTrace, trace, faults, runEp_e2_none, runEp_irq_none, hX, stdView]
  | some n =>
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [stdTrace, trace, faults, runEp_e2_some, runEp_irq_some, hX, stdView]

/-- No monitor over the `irqstate` interface decides the E2 lockdep fault. -/
theorem no_irqstate_monitor_for_e2 :
    ¬ ∃ M : List StdObs → Bool,
      ∀ x, M (stdTrace x) = true ↔ Fault.tickOutsideLockdepHardirq ∈ faults x := by
  have h := e2_invisible_to_irqstate none
  exact no_exact_monitor_of_collision stdTrace (fun x => _ ∈ faults x) h.1.symm
    (by rw [h.2.2]; simp) h.2.1

/-- The extended interface adds lockdep's `hardirq_context` to the two hardirq boundary
events (the lab's `lockdep_check`). -/
def ExtObs := StdObs × Option Nat

def extView (r : TpRecord) : ExtObs :=
  (stdView r, match r.ev with
    | .hardEntry | .hardExit => some r.ldHard
    | _ => none)

/-- The boundary cross-check `lockdep_hardirq_context() == hardirq_count() >> HARDIRQ_SHIFT`
at `hardirq_context_entry` and `hardirq_context_exit`. -/
def ldCrossCheck (os : List ExtObs) : Bool :=
  os.any fun o => match o.2 with
    | some ld => ld != o.1.depth
    | none => false

def ldMismatch (r : TpRecord) : Bool :=
  match r.ev with
  | .hardEntry | .hardExit => r.ldHard != r.depth
  | _ => false

theorem ldCrossCheck_map (rs : List TpRecord) : ldCrossCheck (rs.map extView) = rs.any ldMismatch := by
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.map_cons, ldCrossCheck, List.any_cons] at ih ⊢
    rw [ih]
    congr 1
    rcases r with ⟨ev, d, h, s, l⟩
    cases ev <;> rfl

theorem nestedTrace_no_mismatch (n : Nat) : (nestedTrace n).any ldMismatch = false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nestedTrace_succ, List.any_append, ih]; decide

theorem episode_ldMismatch (ep : Episode) :
    (runEp ep).2.1.any ldMismatch = true ↔ Fault.tickOutsideLockdepHardirq ∈ (runEp ep).2.2 := by
  cases ep with
  | irq s =>
    cases s with
    | none => rw [runEp_irq_none]; decide
    | some n =>
      rw [runEp_irq_some]
      simp only [List.any_append, nestedTrace_no_mismatch]
      decide
  | taskSoftirq n =>
    rw [runEp_taskSoftirq]
    simp only [List.any_append, nestedTrace_no_mismatch]
    decide
  | rawIRQ b => rw [runEp_rawIRQ]; cases b <;> decide
  | e1aHalfRaw b => rw [runEp_e1a]; cases b <;> decide
  | e2LockdepEarly s =>
    cases s with
    | none => rw [runEp_e2_none]; decide
    | some n =>
      rw [runEp_e2_some]
      simp only [List.any_append, nestedTrace_no_mismatch]
      decide
  | e4OldOrder s =>
    cases s with
    | none => rw [runEp_e4_none]; decide
    | some n =>
      rw [runEp_e4_some]
      simp only [List.any_append, nestedTrace_no_mismatch]
      decide

/-- **The extended interface decides E2 exactly.** On every execution in the model, the
boundary lockdep cross-check reacts iff some `tick_irq_exit()` ran outside lockdep's
hardirq context. In particular it never reacts on valid, E1a, E1b or E4 episodes. -/
theorem lockdep_cross_check_exact (x : List Episode) :
    ldCrossCheck ((trace x).map extView) = true ↔ Fault.tickOutsideLockdepHardirq ∈ faults x := by
  rw [ldCrossCheck_map]
  simp only [trace, faults, List.any_flatMap, List.mem_flatMap]
  rw [List.any_eq_true]
  constructor
  · rintro ⟨ep, hep, h⟩
    exact ⟨ep, hep, (episode_ldMismatch ep).mp h⟩
  · rintro ⟨ep, hep, h⟩
    exact ⟨ep, hep, (episode_ldMismatch ep).mpr h⟩

/-! ### Part 6: Observation-gap kind (E4, E1b), invisible to every interface -/

/-- **E4 is invisible to every interface built from these tracepoints.** The
pre-`feb5c9a2447a` order produces exactly the records of a fault-free interrupt without
softirq, followed by a fault-free task-context softirq run. That includes the depth,
`hardirq_count()`, `in_serving_softirq()` and lockdep samples. -/
theorem e4_has_identical_valid_twin (n : Nat) :
    trace [.e4OldOrder none] = trace [.irq none] ∧
    trace [.e4OldOrder (some n)] = trace [.irq none, .taskSoftirq n] ∧
    Fault.tickOutsideHardirq ∈ faults [.e4OldOrder none] ∧
    Fault.tickOutsideHardirq ∈ faults [.e4OldOrder (some n)] ∧
    faults [.irq none, .taskSoftirq n] = [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [trace, faults, runEp_e4_none, runEp_e4_some, runEp_irq_none, runEp_taskSoftirq]

theorem e4_invisible_to_every_record_view {O : Type} (f : TpRecord → O) :
    ¬ ∃ M : List O → Bool,
      ∀ x, M ((trace x).map f) = true ↔ Fault.tickOutsideHardirq ∈ faults x := by
  have h := e4_has_identical_valid_twin 0
  refine no_exact_monitor_of_collision (fun x => (trace x).map f) (fun x => _ ∈ faults x)
    (good := [.irq none]) (bad := [.e4OldOrder none]) (by simp only [h.1]) ?_ h.2.2.1
  simp [faults, runEp_irq_none]

/-- **E1b is invisible to every interface built from these tracepoints.** A fully raw
vector emits no boundary event. Whether or not its handler raised a softirq that the raw
exit then left unserved, its records equal those of an empty `_SIMPLE` vector and those
of no interrupt at all. -/
theorem e1b_has_identical_valid_twin :
    trace [.rawIRQ true] = trace [.rawIRQ false] ∧
    trace [.rawIRQ true] = trace [] ∧
    Fault.softirqLeftPending ∈ faults [.rawIRQ true] ∧
    faults [.rawIRQ false] = [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [trace, faults, runEp_rawIRQ]

theorem e1b_invisible_to_every_record_view {O : Type} (f : TpRecord → O) :
    ¬ ∃ M : List O → Bool,
      ∀ x, M ((trace x).map f) = true ↔ Fault.softirqLeftPending ∈ faults x := by
  have h := e1b_has_identical_valid_twin
  refine no_exact_monitor_of_collision (fun x => (trace x).map f) (fun x => _ ∈ faults x)
    (good := [.rawIRQ false]) (bad := [.rawIRQ true]) (by simp only [h.1]) ?_ h.2.2.1
  rw [h.2.2.2]
  simp

/-! ### Part 7: Universal twin and silence of v2 `irqstate` -/

/-- Fault-free twin of an episode: repair E2, E4 and E1b, and keep everything else. -/
def twin : Episode → List Episode
  | .e2LockdepEarly s => [.irq s]
  | .e4OldOrder none => [.irq none]
  | .e4OldOrder (some n) => [.irq none, .taskSoftirq n]
  | .rawIRQ _ => [.rawIRQ false]
  | ep => [ep]

theorem twin_valid (ep : Episode) (h : ¬ ep.IsE1a) : ∀ e ∈ twin ep, e.Valid := by
  cases ep with
  | irq s => simp [twin, Episode.Valid]
  | taskSoftirq n => simp [twin, Episode.Valid]
  | rawIRQ b => simp [twin, Episode.Valid]
  | e1aHalfRaw b => exact absurd trivial h
  | e2LockdepEarly s => simp [twin, Episode.Valid]
  | e4OldOrder s => cases s <;> simp [twin, Episode.Valid]

theorem twin_std (ep : Episode) (h : ¬ ep.IsE1a) :
    stdTrace (twin ep) = (runEp ep).2.1.map stdView := by
  cases ep with
  | irq s => simp [twin, stdTrace, trace]
  | taskSoftirq n => simp [twin, stdTrace, trace]
  | rawIRQ b => simp [twin, stdTrace, trace, runEp_rawIRQ]
  | e1aHalfRaw b => exact absurd trivial h
  | e2LockdepEarly s =>
    have := (e2_invisible_to_irqstate s).1
    simp only [stdTrace, trace, List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
    simp [twin, stdTrace, trace, this]
  | e4OldOrder s =>
    cases s with
    | none => simp [twin, stdTrace, trace, runEp_e4_none, runEp_irq_none]
    | some n => simp [twin, stdTrace, trace, runEp_e4_some, runEp_irq_none, runEp_taskSoftirq]

theorem twin_full (ep : Episode) (h1 : ¬ ep.IsE1a) (h2 : ¬ ep.IsE2) :
    trace (twin ep) = (runEp ep).2.1 := by
  cases ep with
  | irq s => simp [twin, trace]
  | taskSoftirq n => simp [twin, trace]
  | rawIRQ b => simp [twin, trace, runEp_rawIRQ]
  | e1aHalfRaw b => exact absurd trivial h1
  | e2LockdepEarly s => exact absurd trivial h2
  | e4OldOrder s =>
    cases s with
    | none => simp [twin, trace, runEp_e4_none, runEp_irq_none]
    | some n => simp [twin, trace, runEp_e4_some, runEp_irq_none, runEp_taskSoftirq]

theorem trace_flatMap (x : List Episode) (g : Episode → List Episode) :
    trace (x.flatMap g) = x.flatMap fun ep => trace (g ep) := by
  induction x with
  | nil => rfl
  | cons ep rest ih => simp [trace, List.flatMap_append] at ih ⊢; rw [ih]

/-- **Universal twin.** Every execution without E1a has a valid, fault-free twin with the
same `irqstate` observation. If it also has no E2, the twin has the same full records,
so every per-record interface agrees on both. -/
theorem every_e1a_free_execution_has_valid_twin (x : List Episode)
    (h : ∀ ep ∈ x, ¬ ep.IsE1a) :
    (∀ e ∈ x.flatMap twin, e.Valid) ∧
    faults (x.flatMap twin) = [] ∧
    stdTrace (x.flatMap twin) = stdTrace x ∧
    ((∀ ep ∈ x, ¬ ep.IsE2) → trace (x.flatMap twin) = trace x) := by
  have hvalid : ∀ e ∈ x.flatMap twin, e.Valid := by
    intro e he
    rcases List.mem_flatMap.mp he with ⟨ep, hep, he'⟩
    exact twin_valid ep (h ep hep) e he'
  refine ⟨hvalid, ?_, ?_, ?_⟩
  · simp only [faults, List.flatMap_eq_nil_iff]
    intro e he
    exact (faults_nil_iff_valid e).mpr (hvalid e he)
  · have hstd : ∀ ep ∈ x, (trace (twin ep)).map stdView = (runEp ep).2.1.map stdView :=
      fun ep hep => twin_std ep (h ep hep)
    calc stdTrace (x.flatMap twin)
        = x.flatMap (fun ep => (trace (twin ep)).map stdView) := by
          rw [stdTrace, trace_flatMap, List.map_flatMap]
      _ = x.flatMap (fun ep => (runEp ep).2.1.map stdView) := List.flatMap_congr hstd
      _ = stdTrace x := by rw [stdTrace, trace, List.map_flatMap]
  · intro h2
    rw [trace_flatMap]
    apply List.flatMap_congr
    intro ep hep
    exact twin_full ep (h ep hep) (h2 ep hep)

/-- **v2 `irqstate` is silent on every execution without E1a**, including all E2, E4 and
E1b faults, whether monitoring starts unsynchronized or in `idle`. -/
theorem irqstate_silent_without_e1a (x : List Episode) (h : ∀ ep ∈ x, ¬ ep.IsE1a) :
    (irqstate none (stdTrace x)).1.any id = false ∧
    (irqstate (some .idle) (stdTrace x)).1.any id = false := by
  have ⟨hv, _, hstd, _⟩ := every_e1a_free_execution_has_valid_twin x h
  rw [← hstd]
  exact irqstate_accepts_valid _ hv

/-- Neither interface certifies the absence of the E4 or E1b faults: on every execution
without E1a and E2, the full records, and hence the `irqstate` verdict and the extended
cross-check, coincide with those of a fault-free valid execution. -/
theorem no_record_view_certifies_absence (x : List Episode)
    (h : ∀ ep ∈ x, ¬ ep.IsE1a ∧ ¬ ep.IsE2) {O α : Type} (f : TpRecord → O)
    (M : List O → α) :
    ∃ y : List Episode, (∀ e ∈ y, e.Valid) ∧ faults y = [] ∧
      M ((trace y).map f) = M ((trace x).map f) := by
  have ⟨hv, hf, _, hfull⟩ := every_e1a_free_execution_has_valid_twin x (fun ep hep => (h ep hep).1)
  exact ⟨x.flatMap twin, hv, hf, by rw [hfull (fun ep hep => (h ep hep).2)]⟩

end LinuxRV.IRQStateObservability
