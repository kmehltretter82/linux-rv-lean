import Definitions.Def_RamadgeWonham_Shared_Generator
import Mathlib.Data.Real.Basic

/-! Automata and timed interference-free latency model from:
- D. B. de Oliveira, D. Casini, R. S. de Oliveira, and T. Cucinotta,
  *Demystifying the Real-Time Linux Scheduling Latency*, ECRTS 2020
  (LIPIcs Vol. 165, Art. 9, pp. 9:1–9:23), §§3–4, Figures 19–22, Table 1.
- D. B. de Oliveira, *Automata-based Formal Analysis and Verification of the
  Real-Time Linux Kernel* (PhD thesis, 2020), Chapter 6 (§§6.1–6.2,
  Figures 75–78, Table 9, Lemmas 1–6).

This module transcribes the published sufficiency specifications `R12`, `R13`,
and the 7-state, 14-event `R14` automaton (ECRTS Fig. 21 / Thesis Fig. 77),
defines the phase rank and five-case classification (`i-a`, `i-b`, `i-c`,
`ii-a`, `ii-b`) of rescheduling cycles, and defines timed interference-free
runs constrained by the Table 1 / Table 9 contiguous-interval parameters
(`D_PSD`, `D_PAIE`, `D_POID`, `D_ST`). -/

namespace ECRTS2020

open RamadgeWonham.Shared

/-! ### Rule R12 (ECRTS Fig. 19 / Thesis Fig. 75): disabling preemption to schedule calls the scheduler -/

inductive R12Event where
  | preemptDisableSched
  | preemptEnableSched
  | scheduleEntry
  deriving DecidableEq

inductive R12State where
  | thread
  | pd
  | sched
  deriving DecidableEq

/-- `R12` (ECRTS Fig. 19 / Thesis Fig. 75): disabling preemption to schedule always causes
a call to the scheduler before preemption is re-enabled. -/
def r12 : Generator R12Event where
  Q := R12State
  q0 := .thread
  Qm := {.thread}
  δ e q := match q, e with
    | .thread, .preemptDisableSched => some .pd
    | .pd, .scheduleEntry => some .sched
    | .sched, .scheduleEntry => some .sched
    | .sched, .preemptEnableSched => some .thread
    | _, _ => none

/-! ### Rule R13 (ECRTS Fig. 20 / Thesis Fig. 76): calling the scheduler causes a context switch -/

inductive R13Event where
  | scheduleEntry
  | scheduleExit
  | switchSuspend
  | switchPreempt
  | switchBlocking
  | switchOutOther
  deriving DecidableEq

inductive R13State where
  | thread
  | bSwitch
  | aSwitch
  deriving DecidableEq

/-- `R13` (ECRTS Fig. 20 / Thesis Fig. 76): calling the scheduler always results in a context
switch before `schedule_exit`. -/
def r13 : Generator R13Event where
  Q := R13State
  q0 := .thread
  Qm := {.thread}
  δ e q := match q, e with
    | .thread, .scheduleEntry => some .bSwitch
    | .bSwitch, .switchSuspend | .bSwitch, .switchPreempt
    | .bSwitch, .switchBlocking | .bSwitch, .switchOutOther => some .aSwitch
    | .aSwitch, .scheduleExit => some .thread
    | _, _ => none

/-! ### Rule R14 (ECRTS Fig. 21 / Thesis Fig. 77): setting `need_resched` causes a context switch -/

/-- The 14 event labels appearing in Figure 21 (`R14`) of ECRTS 2020 / Figure 77 of Thesis Ch. 6. -/
inductive R14Event where
  | needResched
  | preemptDisable
  | preemptEnable
  | preemptDisableSched
  | preemptEnableSched
  | localIrqDisable
  | localIrqEnable
  | hwIrqDisable
  | hwIrqEnable
  | scheduleEntry
  | scheduleExit
  | switchIn
  | switchInOther
  | nonAtomic
  deriving DecidableEq

/-- The 7 states of Figure 21 (`R14`): `thread` (initial and marked), `pd_id`, `pd_ie`,
`pe_id`, `ie_resched`, `pe_ie`, and `sched`. -/
inductive R14State where
  | thread
  | pdId
  | pdIe
  | peId
  | ieResched
  | peIe
  | sched
  deriving DecidableEq

/-- `R14` (ECRTS Fig. 21 / Thesis Fig. 77): transcribed directly from the labeled arrows
of Figure 21. Setting `sched_need_resched` leaves `thread` for `pd_id` and must traverse
a context switch (`sched_switch_in` or `sched_switch_in_o`) to return to `thread`. -/
def r14 : Generator R14Event where
  Q := R14State
  q0 := .thread
  Qm := {.thread}
  δ e q := match q, e with
    | .thread, .needResched => some .pdId
    | .thread, _ => some .thread
    | .pdId, .switchIn | .pdId, .switchInOther => some .thread
    | .pdId, .localIrqEnable | .pdId, .hwIrqEnable => some .pdIe
    | .pdId, .preemptEnable => some .peId
    | .pdIe, .localIrqDisable | .pdIe, .hwIrqDisable => some .pdId
    | .pdIe, .scheduleEntry => some .sched
    | .pdIe, .scheduleExit => some .ieResched
    | .pdIe, .preemptEnable | .pdIe, .preemptEnableSched => some .peIe
    | .peId, .preemptDisable => some .pdId
    | .peId, .localIrqEnable | .peId, .hwIrqEnable => some .peIe
    | .peId, .preemptDisableSched => some .sched
    | .ieResched, .hwIrqDisable | .ieResched, .hwIrqEnable => some .ieResched
    | .ieResched, .preemptEnableSched => some .peIe
    | .ieResched, .scheduleEntry => some .sched
    | .peIe, .hwIrqDisable | .peIe, .hwIrqEnable => some .peIe
    | .peIe, .preemptDisableSched => some .sched
    | .sched, .localIrqDisable | .sched, .localIrqEnable
    | .sched, .hwIrqDisable | .sched, .hwIrqEnable
    | .sched, .scheduleEntry => some .sched
    | .sched, .switchIn | .sched, .switchInOther => some .thread
    | _, _ => none

/-! ### Phase structure and five-case classification of rescheduling cycles -/

/-- Monotonic phase rank of non-`thread` states in Figure 21:
`0` = preemption or IRQs disabled (`pd_id`, `pd_ie`, `pe_id`);
`1` = `ie_resched` (post-`schedule_exit` tail of a prior scheduler call);
`2` = `pe_ie` (both preemption and IRQs enabled);
`3` = `sched` (scheduler flow leading to the context switch);
`4` = `thread` (completed cycle). -/
def R14State.phaseRank : R14State → Nat
  | .pdId | .pdIe | .peId => 0
  | .ieResched => 1
  | .peIe => 2
  | .sched => 3
  | .thread => 4

/-- States in which preemption or IRQs are disabled (`pd_id`, `pd_ie`, `pe_id`). -/
def R14State.isDisabled : R14State → Bool
  | .pdId | .pdIe | .peId => true
  | _ => false

/-- States preceding `pe_ie` during a prior scheduler tail (`pd_id`, `pd_ie`, `pe_id`, `ie_resched`). -/
def R14State.isPrePeIe : R14State → Bool
  | .pdId | .pdIe | .peId | .ieResched => true
  | _ => false

/-- States visited in cases `(i-a)` and `(i-b)`, where neither `ie_resched` nor `pe_ie` is entered. -/
def R14State.isNoPeIe : R14State → Bool
  | .pdId | .pdIe | .peId | .sched => true
  | _ => false

/-- The five mutually-exclusive scheduling-latency cases of ECRTS 2020 §4.2 / Thesis §6.2.2
(colored regions in Figure 21 / Figure 77). -/
inductive LatencyCase where
  | ia   -- black: RHP_i between EV1 and EV2 (`pd_ie --schedule_entry--> sched`)
  | ib   -- pink:  RHP_i between EV2 and EV3 (`pd_id --switchIn/switchInOther--> thread`)
  | ic   -- brown: RHP_i between EV3 and EV7 (`pd_ie --schedule_exit--> ie_resched` or `--preempt_enable_sched--> pe_ie`)
  | iia  -- green: outside scheduler, IRQ wakeup (`pe_id --preempt_disable_sched--> sched`)
  | iib  -- blue:  outside scheduler, postponed until `pe_ie` (`pd_ie --preempt_enable--> pe_ie` or `pe_id --irq_enable--> pe_ie`)
  deriving DecidableEq

/-- Portal classification of the unique exit transition leaving the disabled cluster
`{pd_id, pd_ie, pe_id}` in Figure 21. -/
def classifyPortal : R14State → R14Event → Option LatencyCase
  | .pdId, .switchIn | .pdId, .switchInOther => some .ib
  | .pdIe, .scheduleEntry => some .ia
  | .pdIe, .scheduleExit => some .ic
  | .pdIe, .preemptEnableSched => some .ic
  | .peId, .preemptDisableSched => some .iia
  | .pdIe, .preemptEnable => some .iib
  | .peId, .localIrqEnable | .peId, .hwIrqEnable => some .iib
  | _, _ => none

/-- Classify a Figure 21 event sequence starting from state `s` by the first exit portal
it takes out of `{pd_id, pd_ie, pe_id}`. -/
def classifyPath (s : R14State) : List R14Event → Option LatencyCase
  | [] => none
  | e :: rest =>
    match classifyPortal s e with
    | some c => some c
    | none =>
      match r14.δ e s with
      | some s' => classifyPath s' rest
      | none => none

/-- `validUntilThread s w` holds when `w` is a non-empty valid `r14` trace starting at
`s ≠ .thread`, staying strictly outside `.thread` at every intermediate state, and
returning to `.thread` on its final event. -/
def validUntilThread (s : R14State) : List R14Event → Prop
  | [] => False
  | [e] => s ≠ .thread ∧ r14.δ e s = some .thread
  | e :: e' :: rest =>
    s ≠ .thread ∧
    match r14.δ e s with
    | some s' => s' ≠ .thread ∧ validUntilThread s' (e' :: rest)
    | none => False

/-! ### Timed interference-free runs and Table 1 / Table 9 parameters -/

/-- The four non-negative interference-free interval parameters of ECRTS 2020 Table 1 /
Thesis Table 9. -/
structure LatencyParams where
  /-- Longest interference-free interval in which preemption is disabled to schedule (`D_PSD`). -/
  D_PSD : ℝ
  /-- Longest interference-free interval spent in state `pe_ie` (`D_PAIE`). -/
  D_PAIE : ℝ
  /-- Longest interference-free interval in which preemption is disabled to postpone
  the scheduler or IRQs are disabled (`D_POID`). -/
  D_POID : ℝ
  /-- Longest interference-free interval between consecutive occurrences of EV3 and EV7 (`D_ST`). -/
  D_ST : ℝ
  D_PSD_nonneg : 0 ≤ D_PSD
  D_PAIE_nonneg : 0 ≤ D_PAIE
  D_POID_nonneg : 0 ≤ D_POID
  D_ST_nonneg : 0 ≤ D_ST

/-- The overall interference-free scheduling-latency upper bound of ECRTS 2020 Lemma 7 (Eq. 6) /
Thesis Lemma 6 (Eq. 23). -/
noncomputable def interferenceFreeBound (p : LatencyParams) : ℝ :=
  max p.D_ST p.D_POID + p.D_PAIE + p.D_PSD

/-- Pair each timed step `(dt, e)` with the `r14` state in which the interference-free
dwell duration `dt` elapses before event `e` occurs. -/
def visitedStatesAux (s : R14State) : List (ℝ × R14Event) → List (R14State × ℝ)
  | [] => []
  | (dt, e) :: rest =>
    (s, dt) ::
      match r14.δ e s with
      | some s' => visitedStatesAux s' rest
      | none => []

/-- A timed interference-free scheduling-latency run from `RHP_i` to `EV7`:
- `preDelay`: interference-free delay between `RHP_i` and `sched_need_resched`;
- `steps`: timed Figure 21 cycle from `pd_id` (immediately after `sched_need_resched`)
  to its first return to `thread` (at EV4, `sched_switch_in` / `sched_switch_in_o`);
- `postSwitch`: interference-free scheduler tail duration from EV4 to EV7. -/
structure TimedLatencyRun where
  preDelay : ℝ
  steps : List (ℝ × R14Event)
  postSwitch : ℝ
  preDelay_nonneg : 0 ≤ preDelay
  postSwitch_nonneg : 0 ≤ postSwitch
  dwells_nonneg : ∀ x ∈ steps, 0 ≤ x.1
  valid_cycle : validUntilThread .pdId (steps.map Prod.snd)

/-- The sequence of `(state, dwell)` pairs visited along `r.steps` starting from `pd_id`. -/
def TimedLatencyRun.visited (r : TimedLatencyRun) : List (R14State × ℝ) :=
  visitedStatesAux .pdId r.steps

/-- Total interference-free latency `L^IF` accumulated during `r`. -/
def TimedLatencyRun.totalIF (r : TimedLatencyRun) : ℝ :=
  r.preDelay + (r.steps.map Prod.fst).sum + r.postSwitch

/-- The Figure 21 case determined by `r`'s exit portal from `{pd_id, pd_ie, pe_id}`. -/
def TimedLatencyRun.latencyCase (r : TimedLatencyRun) : Option LatencyCase :=
  classifyPath .pdId (r.steps.map Prod.snd)

/-- Local contiguous-interval bound: every contiguous sublist `mid` of `visited` whose states
all satisfy `P`—augmented with `preExtra` if `mid` starts at the beginning of `visited` and
with `postExtra` if `mid` extends to the end—has total dwell duration at most `bound`. -/
def ContiguousDwellBound (P : R14State → Bool) (visited : List (R14State × ℝ))
    (preExtra postExtra bound : ℝ) : Prop :=
  ∀ l mid u, visited = l ++ mid ++ u →
    (∀ x ∈ mid, P x.1 = true) →
    (if l = [] then preExtra else 0) + (mid.map Prod.snd).sum +
      (if u = [] then postExtra else 0) ≤ bound

/-- A `TimedLatencyRun` respects the Table 1 / Table 9 interval bounds `p`: each maximal
contiguous interval of the relevant kernel condition is bounded by its Table 1 parameter. -/
def RespectsParams (p : LatencyParams) (r : TimedLatencyRun) : Prop :=
  ContiguousDwellBound (fun s => s == .peIe) r.visited 0 0 p.D_PAIE ∧
  ContiguousDwellBound (fun s => s == .sched) r.visited 0 r.postSwitch p.D_PSD ∧
  match r.latencyCase with
  | some .ia | some .ib =>
      ContiguousDwellBound R14State.isNoPeIe r.visited r.preDelay r.postSwitch p.D_PSD
  | some .ic =>
      ContiguousDwellBound R14State.isPrePeIe r.visited r.preDelay 0 p.D_ST
  | some .iia | some .iib =>
      ContiguousDwellBound R14State.isDisabled r.visited r.preDelay 0 p.D_POID
  | none => True

end ECRTS2020
