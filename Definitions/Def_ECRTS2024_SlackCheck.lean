import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-! Schedule model, supply linear bound function, and `O(1)` slack recurrence from:
- M. Castrovilli and E. Bini, *SlackCheck: A Linux Kernel Module to Verify Temporal
  Properties of a Task Schedule*, ECRTS 2024 (LIPIcs Vol. 298, Art. 2, pp. 2:1–2:24),
  §§2–3, Equations (1)–(15), Definition 1, Theorem 2, and Figures 1–2.

This module defines:
1. Non-Zeno alternating `sched-in` / `sched-out` schedules `TaskSchedule`, the binary
   schedule indicator `scheduleFn` (Eq. 1), and the exact piecewise-linear cumulative
   service function `cumService` / `sched` (Eq. 2).
2. The supply linear bound function `slbf` (Eq. 5) and continuous-interval compliance
   `CompliesWithSLBF` (Eq. 6), together with the discrete `(out_k, in_h)` condition
   `CompliesOnOutIn` (Eq. 11) and the periodic server supply bound `periodicSbf` (Eq. 4).
3. The `O(1)` slack recurrence `slackOut` / `slackIn` (Definition 1, Eqs. 7–9) and
   the Figure 2 worked example (`α = 2/3`, `Δ = 4`, violation detected at `in_3 = 15`). -/

namespace ECRTS2024.SlackCheck

/-! ### Schedule model (§2, Eqs. 1–2) -/

/-- An unbounded, non-Zeno alternating schedule of `sched-out` (`outTime`) and `sched-in`
(`inTime`) instants for a monitored task `τ` (ECRTS 2024, §2, p. 2:4):
- `out₀ = 0` and `in₀ ≥ out₀` (`in₀ = out₀` if `τ` is scheduled at time `0`);
- `in_k < out_{k+1} < in_{k+1}` for all `k ∈ ℕ`;
- `lim_{k → ∞} in_k = ∞` (non-Zeno: for every `T : ℝ`, `∃ k, T ≤ in_k`). -/
structure TaskSchedule where
  inTime : ℕ → ℝ
  outTime : ℕ → ℝ
  out_zero : outTime 0 = 0
  in_zero_ge : outTime 0 ≤ inTime 0
  alternating : ∀ k : ℕ, inTime k < outTime (k + 1) ∧ outTime (k + 1) < inTime (k + 1)
  nonZeno : ∀ T : ℝ, ∃ k : ℕ, T ≤ inTime k

/-- Every real time `t` is strictly exceeded by some `out_{k+1}` (immediate from `nonZeno`
and `in_k < out_{k+1}`). -/
theorem TaskSchedule.exists_lt_out_succ (sch : TaskSchedule) (t : ℝ) :
    ∃ k : ℕ, t < sch.outTime (k + 1) := by
  obtain ⟨k, hk⟩ := sch.nonZeno t
  exact ⟨k, lt_of_le_of_lt hk (sch.alternating k).1⟩

/-- The unique interval index `k` such that `out_k ≤ t < out_{k+1}` (for `t ≥ 0`). -/
noncomputable def TaskSchedule.slotOf (sch : TaskSchedule) (t : ℝ) : ℕ :=
  letI := Classical.propDecidable
  Nat.find (sch.exists_lt_out_succ t)

/-- Binary schedule indicator `s(t) ∈ {0, 1}` (Eq. 1): `1` when `in_k ≤ t < out_{k+1}`
for some `k ∈ ℕ`, and `0` otherwise. -/
noncomputable def scheduleFn (sch : TaskSchedule) (t : ℝ) : ℝ :=
  letI := Classical.propDecidable
  if ∃ k : ℕ, sch.inTime k ≤ t ∧ t < sch.outTime (k + 1) then 1 else 0

/-- Cumulative active execution time received during `[0, out_k]` (equivalently `[0, in_k]`):
`∑_{ℓ=0}^{k-1} (out_{ℓ+1} - in_ℓ)`. -/
def activeSum (sch : TaskSchedule) (k : ℕ) : ℝ :=
  (Finset.range k).sum (fun ℓ => sch.outTime (ℓ + 1) - sch.inTime ℓ)

/-- Exact piecewise-linear cumulative CPU service `∫_0^t s(u) du` for `t ≥ 0` (and `0` for `t < 0`):
on `[out_k, in_k)` the task is idle so service stays at `activeSum sch k`; on `[in_k, out_{k+1})`
the task runs so service grows at rate `1` as `activeSum sch k + (t - in_k)`. -/
noncomputable def cumService (sch : TaskSchedule) (t : ℝ) : ℝ :=
  if 0 ≤ t then
    let k := sch.slotOf t
    activeSum sch k + max 0 (t - sch.inTime k)
  else 0

/-- Cumulative CPU service `sched(a, b) = ∫_a^b s(t) dt` over `[a, b]` (Eq. 2). -/
noncomputable def sched (sch : TaskSchedule) (a b : ℝ) : ℝ :=
  cumService sch b - cumService sch a

/-! ### Supply linear bound function and temporal constraints (§2, Eqs. 4–6 & 11) -/

/-- Supply linear bound function `slbf(t) = max(0, α (t - Δ))` for bandwidth `α` and delay `Δ` (Eq. 5). -/
noncomputable def slbf (α Δ t : ℝ) : ℝ :=
  max 0 (α * (t - Δ))

/-- Continuous-time temporal constraint (Eq. 6): for every `0 ≤ t₀ ≤ t₁`,
`sched(t₀, t₁) ≥ slbf(t₁ - t₀)`. -/
def CompliesWithSLBF (sch : TaskSchedule) (α Δ : ℝ) : Prop :=
  ∀ t₀ t₁ : ℝ, 0 ≤ t₀ → t₀ ≤ t₁ → slbf α Δ (t₁ - t₀) ≤ sched sch t₀ t₁

/-- Discrete `(out_k, in_h)` reduction (Eq. 11): for all `k ≤ h`,
`sched(out_k, in_h) ≥ slbf(in_h - out_k)`. -/
def CompliesOnOutIn (sch : TaskSchedule) (α Δ : ℝ) : Prop :=
  ∀ k h : ℕ, k ≤ h → slbf α Δ (sch.inTime h - sch.outTime k) ≤ sched sch (sch.outTime k) (sch.inTime h)

/-- Periodic-server supply bound function (Eq. 4, Fig. 1) for budget `Q` and period `P`:
`sbf(t) = max(0, t - P + Q - (k + 1)(P - Q), k · Q)` where `k = ⌊(t - P + Q) / P⌋`. -/
noncomputable def periodicSbf (Q P t : ℝ) : ℝ :=
  let k : ℤ := Int.floor ((t - P + Q) / P)
  max 0 (max (t - P + Q - ((k : ℝ) + 1) * (P - Q)) ((k : ℝ) * Q))

/-! ### SlackCheck `O(1)` slack recurrence (§3.1, Definition 1, Eqs. 7–10) -/

/-- `slack(out_k)` defined recursively by Eqs. (7) and (9):
`slack(out₀) = Δ` and `slack(out_{k+1}) = min(Δ, slack(in_k) + ((1 - α) / α) · (out_{k+1} - in_k))`. -/
noncomputable def slackOut (sch : TaskSchedule) (α Δ : ℝ) : ℕ → ℝ
  | 0 => Δ
  | k + 1 =>
    let prevIn := slackOut sch α Δ k - (sch.inTime k - sch.outTime k)
    min Δ (prevIn + ((1 - α) / α) * (sch.outTime (k + 1) - sch.inTime k))

/-- `slack(in_k) = slack(out_k) - (in_k - out_k)` (Eq. 8). -/
noncomputable def slackIn (sch : TaskSchedule) (α Δ : ℝ) (k : ℕ) : ℝ :=
  slackOut sch α Δ k - (sch.inTime k - sch.outTime k)

/-- Runtime monitoring condition checked at every `sched-in` instant (Eq. 10). -/
def AllSlackNonneg (sch : TaskSchedule) (α Δ : ℝ) : Prop :=
  ∀ h : ℕ, 0 ≤ slackIn sch α Δ h

/-! ### Worked example of Figure 2 (p. 2:7, `α = 2/3`, `Δ = 4`) -/

/-- `out_k` instants extending Figure 2 (`out₀ = 0, out₁ = 7, out₂ = 11, out₃ = 13, out₄ = 16`,
continuing periodically with step `3` thereafter). -/
def fig2Out : ℕ → ℝ
  | 0 => 0
  | 1 => 7
  | 2 => 11
  | 3 => 13
  | k + 4 => 16 + 3 * (k : ℝ)

/-- `in_k` instants extending Figure 2 (`in₀ = 1, in₁ = 10, in₂ = 12, in₃ = 15`,
continuing periodically with step `3` thereafter). -/
def fig2In : ℕ → ℝ
  | 0 => 1
  | 1 => 10
  | 2 => 12
  | 3 => 15
  | k + 4 => 18 + 3 * (k : ℝ)

/-- Concrete `TaskSchedule` realizing Figure 2 of Castrovilli & Bini (ECRTS 2024, p. 2:7). -/
def fig2Schedule : TaskSchedule where
  inTime := fig2In
  outTime := fig2Out
  out_zero := rfl
  in_zero_ge := by norm_num [fig2Out, fig2In]
  alternating := by
    intro k
    match k with
    | 0 | 1 | 2 | 3 => norm_num [fig2Out, fig2In]
    | k + 4 =>
      simp only [fig2Out, fig2In]
      push_cast
      constructor <;> linarith
  nonZeno := by
    intro T
    obtain ⟨n, hn⟩ := exists_nat_gt T
    refine ⟨n + 4, ?_⟩
    simp only [fig2In]
    linarith

end ECRTS2024.SlackCheck
