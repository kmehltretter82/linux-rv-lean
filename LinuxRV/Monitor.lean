import Definitions.Def_LinuxRV_TransitionTable

/-! Correctness of the SEFM 2019 table-driven automaton monitor (Figures 4–6, 8),
together with the Wake-up In Preemptive (WIP) worked example. -/

namespace LinuxRV

open RamadgeWonham.Shared

private theorem fold_none {α : Type} (G : Generator α) (w : List α) :
    w.foldl (fun o e ↦ o.bind (G.δ e)) none = none := by
  induction w with
  | nil => rfl
  | cons _ w ih => exact ih

private theorem runFrom_cons {α : Type} (G : Generator α) (q : G.Q) (a : α) (w : List α) :
    G.runFrom q (a :: w) = (G.δ a q).bind (fun r ↦ G.runFrom r w) := by
  unfold Generator.runFrom
  simp only [List.foldl_cons, Option.bind_some]
  cases G.δ a q with
  | none => exact fold_none G w
  | some _ => rfl

/-- Each cell of the compiled transition matrix stores the encoded source successor or -1. -/
theorem compileTable_cell {α : Type} {n m : Nat} (G : Generator α)
    (states : G.Q ≃ Fin n) (events : α ≃ Fin m) (q : G.Q) (e : α) :
    (compileTable G states events)[states q][events e] = encodeNext states (G.δ e q) := by
  simp [compileTable]

private theorem decodeCell_encodeNext {σ : Type} {n : Nat}
    (states : σ ≃ Fin n) (o : Option σ) :
    decodeCell (encodeNext states o) = o.map states := by
  cases o with
  | none => simp [encodeNext, decodeCell]
  | some q => simp [encodeNext, decodeCell, (states q).isLt]

private theorem scan_ok_iff {α : Type} {n m : Nat} (G : Generator α)
    (states : G.Q ≃ Fin n) (events : α ≃ Fin m)
    (trace : List α) (p q : G.Q) (offset : Nat) :
    scan (compileTable G states events) (states p) offset (trace.map events) = .ok (states q) ↔
      G.runFrom p trace = some q := by
  induction trace generalizing p offset with
  | nil =>
    simp only [List.map_nil, scan, Generator.runFrom, List.foldl_nil, Except.ok.injEq,
      Option.some.injEq, states.injective.eq_iff]
  | cons a rest ih =>
    simp only [List.map_cons, scan, compileTable_cell, decodeCell_encodeNext, runFrom_cons]
    cases h : G.δ a p with
    | none => simp
    | some p' => exact ih p' (offset + 1)

private theorem scan_error_iff {α : Type} {n m : Nat} (G : Generator α)
    (states : G.Q ≃ Fin n) (events : α ≃ Fin m)
    (trace : List α) (p q : G.Q) (e : α) (offset i : Nat) :
    scan (compileTable G states events) (states p) offset (trace.map events) =
        .error (i, states q, events e) ↔
      ∃ pre post, trace = pre ++ e :: post ∧ offset + pre.length = i ∧
        G.runFrom p pre = some q ∧ G.δ e q = none := by
  induction trace generalizing p offset with
  | nil =>
    simp [scan]
  | cons a rest ih =>
    simp only [List.map_cons, scan, compileTable_cell, decodeCell_encodeNext]
    cases h : G.δ a p with
    | none =>
      simp only [Option.map_none, Except.error.injEq, Prod.mk.injEq,
        states.injective.eq_iff, events.injective.eq_iff]
      constructor
      · rintro ⟨rfl, rfl, rfl⟩
        exact ⟨[], rest, rfl, Nat.add_zero offset, rfl, h⟩
      · rintro ⟨_ | ⟨b, pre⟩, post, htr, hlen, hrun, _⟩
        · simp only [List.nil_append, List.cons.injEq] at htr
          simp only [Generator.runFrom, List.foldl_nil, Option.some.injEq] at hrun
          simp only [List.length_nil, Nat.add_zero] at hlen
          exact ⟨hlen, hrun, htr.1⟩
        · simp only [List.cons_append, List.cons.injEq] at htr
          obtain ⟨rfl, _⟩ := htr
          rw [runFrom_cons, h] at hrun
          cases hrun
    | some p' =>
      simp only [Option.map_some, ih p' (offset + 1)]
      constructor
      · rintro ⟨pre, post, rfl, hlen, hrun, hnone⟩
        refine ⟨a :: pre, post, rfl, ?_, ?_, hnone⟩
        · simp only [List.length_cons]
          omega
        · rw [runFrom_cons, h]
          exact hrun
      · rintro ⟨_ | ⟨b, pre⟩, post, htr, hlen, hrun, hnone⟩
        · simp only [List.nil_append, List.cons.injEq] at htr
          simp only [Generator.runFrom, List.foldl_nil, Option.some.injEq] at hrun
          obtain ⟨rfl, _⟩ := htr
          subst hrun
          rw [h] at hnone
          cases hnone
        · simp only [List.cons_append, List.cons.injEq] at htr
          obtain ⟨rfl, rfl⟩ := htr
          refine ⟨pre, post, rfl, ?_, ?_, hnone⟩
          · simp only [List.length_cons] at hlen
            omega
          · rw [runFrom_cons, h] at hrun
            exact hrun

/-- The table-driven monitor reaches the encoded source state on every legal trace and
identifies the zero-based position, state, and event of the first undefined transition. -/
theorem monitor_correct {α : Type} {n m : Nat} (G : Generator α)
    (states : G.Q ≃ Fin n) (events : α ≃ Fin m) (trace : List α) :
    (∀ q, monitor G states events trace = .ok (states q) ↔ G.run trace = some q) ∧
    (∀ i q e, monitor G states events trace = .error (i, states q, events e) ↔
      ∃ pre post, trace = pre ++ e :: post ∧ pre.length = i ∧
        G.run pre = some q ∧ G.δ e q = none) := by
  refine ⟨fun q ↦ scan_ok_iff G states events trace G.q0 q 0, fun i q e ↦ ?_⟩
  simpa [monitor, Generator.run, Nat.zero_add] using
    scan_error_iff G states events trace G.q0 q e 0 i

namespace WIP

/-! Wake-up In Preemptive (WIP) example from SEFM 2019, Figures 4–5 and 8. -/

inductive State where
  | preemptive | nonPreemptive
  deriving DecidableEq

inductive Event where
  | preemptDisable | preemptEnable | schedWaking
  deriving DecidableEq

/-- SEFM 2019, Figure 4: `sched_waking` is only allowed while preemption is disabled. -/
def model : Generator Event where
  Q := State
  q0 := .preemptive
  Qm := {.preemptive}
  δ e q := match q, e with
    | .preemptive, .preemptDisable => some .nonPreemptive
    | .nonPreemptive, .preemptEnable => some .preemptive
    | .nonPreemptive, .schedWaking => some .nonPreemptive
    | _, _ => none

def stateEnum : State ≃ Fin 2 where
  toFun | .preemptive => 0 | .nonPreemptive => 1
  invFun | ⟨0, _⟩ => .preemptive | ⟨1, _⟩ => .nonPreemptive
  left_inv q := by cases q <;> rfl
  right_inv | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl

def eventEnum : Event ≃ Fin 3 where
  toFun | .preemptDisable => 0 | .preemptEnable => 1 | .schedWaking => 2
  invFun | ⟨0, _⟩ => .preemptDisable | ⟨1, _⟩ => .preemptEnable | ⟨2, _⟩ => .schedWaking
  left_inv e := by cases e <;> rfl
  right_inv | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl

/-- The compiled matrix matches Figure 5's `function` array entry for entry. -/
theorem wip_table :
    compileTable model stateEnum eventEnum = #v[#v[1, -1, -1], #v[-1, 0, 1]] := by
  decide

/-- Disabling preemption makes `sched_waking` a legal self-loop before re-enabling preemption. -/
theorem wip_legal_trace :
    monitor model stateEnum eventEnum [.preemptDisable, .schedWaking, .preemptEnable] =
      .ok (stateEnum .preemptive) := by
  rfl

/-- Re-enabling preemption makes a subsequent `sched_waking` fail at index 3 (Figure 8). -/
theorem wip_illegal_trace :
    monitor model stateEnum eventEnum
        [.preemptDisable, .schedWaking, .preemptEnable, .schedWaking] =
      .error (3, stateEnum .preemptive, eventEnum .schedWaking) := by
  rfl

end WIP

end LinuxRV
