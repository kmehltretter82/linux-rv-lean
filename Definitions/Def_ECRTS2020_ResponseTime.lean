import Definitions.Def_ECRTS2020_LatencyAutomaton
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Response-time fixed-point model, execution-window soundness definitions, sporadic
interrupt characterizations, and ECRTS 2020 Figure 24 parameters from:
- D. B. de Oliveira, D. Casini, R. S. de Oliveira, and T. Cucinotta,
  *Demystifying the Real-Time Linux Scheduling Latency*, ECRTS 2020
  (LIPIcs Vol. 165, Art. 9, pp. 9:1–9:23), §§4–5, Equations (1) and (7), Theorem 8, Figure 24.
- D. B. de Oliveira, *Automata-based Formal Analysis and Verification of the
  Real-Time Linux Kernel* (PhD thesis, 2020), Chapter 6 (§§6.2–6.3, Equations (18) and (24),
  Theorem 1). -/

namespace ECRTS2020

/-! ### Interference bound regularity and response-time operator -/

/-- Left-continuity of a function `I : ℝ → ℝ` at every positive real `t > 0`.
For monotone nondecreasing `I`, `I t - ε < I s` for `s ≤ t` is equivalent to `|I t - I s| < ε`.
This is the exact regularity property satisfied by constant, sliding-window, and
sporadic ceiling demand functions `t ↦ ⌈t / T⌉ · C`. -/
def LeftContinuousOnPos (I : ℝ → ℝ) : Prop :=
  ∀ t > 0, ∀ ε > 0, ∃ δ > 0, ∀ s, t - δ < s → s ≤ t → I t - ε < I s

/-- Regularity hypotheses on an interrupt-interference bound function `I : ℝ → ℝ`:
nonnegative on `[0, ∞)`, monotone nondecreasing on `[0, ∞)`, and left-continuous on `(0, ∞)`. -/
structure ValidInterferenceBound (I : ℝ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ t → 0 ≤ I t
  mono : ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ → I t₁ ≤ I t₂
  leftCont : LeftContinuousOnPos I

/-- The response-time recursion operator `f(t) = B + I_NMI(t) + I_IRQ(t)` of ECRTS 2020
Equations (1) and (7) / Thesis Equations (18) and (24). -/
def rtaStep (B : ℝ) (I_NMI I_IRQ : ℝ → ℝ) (t : ℝ) : ℝ :=
  B + I_NMI t + I_IRQ t

/-- Kleene fixed-point iteration starting from `L₀ = B`: `L_{n+1} = B + I_NMI(L_n) + I_IRQ(L_n)`. -/
def rtaIter (B : ℝ) (I_NMI I_IRQ : ℝ → ℝ) : ℕ → ℝ
  | 0 => B
  | n + 1 => rtaStep B I_NMI I_IRQ (rtaIter B I_NMI I_IRQ n)

/-- `L` is the least positive fixed point of `f : ℝ → ℝ`. -/
def IsLeastPosFixedPoint (f : ℝ → ℝ) (L : ℝ) : Prop :=
  0 < L ∧ f L = L ∧ ∀ x, 0 < x → f x = x → L ≤ x

/-! ### Execution-window work decomposition (ECRTS 2020 Definition 1 & Property 1) -/

/-- Work decomposition of a scheduling-latency interval `[A, F]` of duration `L_actual = F - A`
for a highest-priority ready thread `τ_i` that is not preempted by higher-priority threads
(Property 1):
- `cover`: no idle time elapses before completion `F` (every instant before `F` is spent
  in interference-free scheduling/blocking work, NMI handling, or IRQ handling);
- `strict_before_finish`: `F` is the earliest instant at which the thread completes its
  total interference-free work `L_IF` (so strictly less than `L_IF` is completed before `L_actual`);
- `nmi_bounded` and `irq_bounded`: cumulative NMI and IRQ work over `[A, A + t]` are bounded
  by `I_NMI t` and `I_IRQ t`, respectively. -/
structure ExecutionWindow (I_NMI I_IRQ : ℝ → ℝ) where
  L_actual : ℝ
  L_IF : ℝ
  W_IF : ℝ → ℝ
  W_NMI : ℝ → ℝ
  W_IRQ : ℝ → ℝ
  L_actual_nonneg : 0 ≤ L_actual
  cover : ∀ t, 0 ≤ t → t < L_actual → t ≤ W_IF t + W_NMI t + W_IRQ t
  strict_before_finish : ∀ t, 0 ≤ t → t < L_actual → W_IF t < L_IF
  nmi_bounded : ∀ t, 0 ≤ t → t < L_actual → W_NMI t ≤ I_NMI t
  irq_bounded : ∀ t, 0 ≤ t → t < L_actual → W_IRQ t ≤ I_IRQ t

/-! ### Sporadic interrupt model (ECRTS 2020 §5 / Thesis §6.3) -/

/-- A sporadic interrupt source parameterized by worst-case execution time `wcet ≥ 0`
and minimum inter-arrival time `miat > 0`. -/
structure SporadicSource where
  wcet : ℝ
  miat : ℝ
  wcet_nonneg : 0 ≤ wcet
  miat_pos : 0 < miat

/-- Sporadic interference demand `⌈t / T⌉ · C` in a window of length `t`. -/
noncomputable def sporadicDemand (src : SporadicSource) (t : ℝ) : ℝ :=
  (Nat.ceil (t / src.miat) : ℝ) * src.wcet

/-- Total sporadic interference across a finite list of interrupt sources. -/
noncomputable def totalSporadicInterference (srcs : List SporadicSource) (t : ℝ) : ℝ :=
  (srcs.map (fun s => sporadicDemand s t)).sum

/-- Total utilization `∑ C_j / T_j` of a finite list of sporadic interrupt sources. -/
noncomputable def totalUtilization (srcs : List SporadicSource) : ℝ :=
  (srcs.map (fun s => s.wcet / s.miat)).sum

/-- Sum of worst-case execution times `∑ C_j` across a finite list of sporadic sources. -/
def totalWcet (srcs : List SporadicSource) : ℝ :=
  (srcs.map SporadicSource.wcet).sum

/-! ### ECRTS 2020 Figure 24 (p. 9:18) numerical workload (in nanoseconds) -/

/-- Observed interference-free parameters from ECRTS 2020 Figure 24 (`perf rtsl` output, ns):
`D_POID = 22510`, `D_ST = 19312`, `D_PAIE = 0` (neglected `< 1 μs`), `D_PSD = 19702`. -/
def fig24Params : LatencyParams where
  D_PSD := 19702
  D_PAIE := 0
  D_POID := 22510
  D_ST := 19312
  D_PSD_nonneg := by norm_num
  D_PAIE_nonneg := by norm_num
  D_POID_nonneg := by norm_num
  D_ST_nonneg := by norm_num

/-- The four sporadic IRQ entries `(oWCET, oMIAT)` in nanoseconds from ECRTS 2020 Figure 24
(IRQs 33, 35, 236, 246), where IRQs 35 and 236 have `oWCET > oMIAT` and the sporadic
recursion reports `"Did not converge."`. -/
def fig24IrqSources : List SporadicSource :=
  [ ⟨16914, 257130, by norm_num, by norm_num⟩
  , ⟨12913, 1843, by norm_num, by norm_num⟩
  , ⟨20728, 1558, by norm_num, by norm_num⟩
  , ⟨3299, 1910321, by norm_num, by norm_num⟩ ]

end ECRTS2020
