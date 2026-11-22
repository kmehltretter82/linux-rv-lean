import Definitions.Def_CassandrasLafortune_Parallel

namespace CassandrasLafortune

open RamadgeWonham.Shared

variable {α A B C : Type}

private theorem fold_none (G : Generator α) (w : List α) :
    w.foldl (fun o e ↦ o.bind (G.δ e)) none = none := by
  induction w with
  | nil => rfl
  | cons e w ih => exact ih

/-- Execute the first event, then continue from its successor if it exists. -/
theorem runFrom_cons (G : Generator α) (q : G.Q) (a : α) (w : List α) :
    G.runFrom q (a :: w) = (G.δ a q).bind (fun r ↦ G.runFrom r w) := by
  unfold Generator.runFrom
  simp only [List.foldl_cons, Option.bind_some]
  cases h : G.δ a q with
  | none => exact fold_none G w
  | some r => rfl

private theorem projected_cons {ε : Type} (G : Generator α) (f : ε → Option α)
    (q : G.Q) (e : ε) (w : List ε) :
    G.runFrom q ((e :: w).filterMap f) =
      (localStep G q (f e)).bind (fun r ↦ G.runFrom r (w.filterMap f)) := by
  cases h : f e <;> simp [h, localStep, runFrom_cons]

/-- Extending a trace by one event takes one step from the state reached by the prefix. -/
theorem run_append_event (G : Generator α) (w : List α) (a : α) :
    G.run (w ++ [a]) = (G.run w).bind (G.δ a) := by
  simp [Generator.run, Generator.runFrom, List.foldl_append]

/-- The product reaches a pair exactly when both projections reach the respective components. -/
theorem parallel_run_iff (G : Generator (A ⊕ C)) (H : Generator (B ⊕ C))
    (w : List (Event A B C)) (q : G.Q) (r : H.Q) :
    (parallel G H).run w = some (q, r) ↔
      G.run (w.filterMap Event.left) = some q ∧ H.run (w.filterMap Event.right) = some r := by
  suffices aux : ∀ (p : G.Q) (s : H.Q),
      (parallel G H).runFrom (p, s) w = some (q, r) ↔
        G.runFrom p (w.filterMap Event.left) = some q ∧
        H.runFrom s (w.filterMap Event.right) = some r from aux G.q0 H.q0
  induction w with
  | nil =>
    intro p s
    change some (p, s) = some (q, r) ↔ some p = some q ∧ some s = some r
    simp
  | cons e w ih =>
    intro p s
    rw [runFrom_cons (parallel G H) (p, s) e w, projected_cons G, projected_cons H]
    change ((do
      let p' ← localStep G p e.left
      let s' ← localStep H s e.right
      pure (p', s')) : Option (G.Q × H.Q)).bind _ = _ ↔ _
    cases localStep G p e.left <;> cases localStep H s e.right <;>
      first | exact ih _ _ | simp [Option.bind]

/-- Generated-language and marked-language characterizations for the same operational product. -/
theorem parallel_languages (G : Generator (A ⊕ C)) (H : Generator (B ⊕ C))
    (w : List (Event A B C)) :
    (w ∈ (parallel G H).L ↔ w.filterMap Event.left ∈ G.L ∧ w.filterMap Event.right ∈ H.L) ∧
    (w ∈ (parallel G H).Lm ↔ w.filterMap Event.left ∈ G.Lm ∧ w.filterMap Event.right ∈ H.Lm) := by
  constructor
  · simp only [Generator.L, Set.mem_ofPred_eq, Option.isSome_iff_exists]
    constructor
    · rintro ⟨⟨q, r⟩, h⟩
      obtain ⟨hq, hr⟩ := (parallel_run_iff G H w q r).mp h
      exact ⟨⟨q, hq⟩, ⟨r, hr⟩⟩
    · rintro ⟨⟨q, hq⟩, ⟨r, hr⟩⟩
      exact ⟨(q, r), (parallel_run_iff G H w q r).mpr ⟨hq, hr⟩⟩
  · constructor
    · rintro ⟨⟨q, r⟩, h, hq, hr⟩
      obtain ⟨l, k⟩ := (parallel_run_iff G H w q r).mp h
      exact ⟨⟨q, l, hq⟩, ⟨r, k, hr⟩⟩
    · rintro ⟨⟨q, hq, mq⟩, ⟨r, hr, mr⟩⟩
      exact ⟨(q, r), (parallel_run_iff G H w q r).mpr ⟨hq, hr⟩, mq, mr⟩

/-- After a legal prefix, the next event fails exactly when a participant has no transition. -/
theorem first_failure_iff (G : Generator (A ⊕ C)) (H : Generator (B ⊕ C))
    (pre : List (Event A B C)) (e : Event A B C) (q : G.Q) (r : H.Q)
    (hpre : (parallel G H).run pre = some (q, r)) :
    (parallel G H).run (pre ++ [e]) = none ↔
      (∃ a, e.left = some a ∧ G.δ a q = none) ∨ (∃ b, e.right = some b ∧ H.δ b r = none) := by
  rw [run_append_event, hpre]
  cases e with
  | leftOnly a =>
    cases h : G.δ (.inl a) q <;> simp [parallel, localStep, Event.left, Event.right, h]
  | rightOnly b =>
    cases h : H.δ (.inl b) r <;> simp [parallel, localStep, Event.left, Event.right, h]
  | shared c =>
    cases hg : G.δ (.inr c) q <;> cases hh : H.δ (.inr c) r <;>
      simp [parallel, localStep, Event.left, Event.right, hg, hh]

end CassandrasLafortune
