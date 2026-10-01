import Superposition.convex_exists_subgradient
import Superposition.convex_locally_lipschitz
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Convex.Continuous
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem convex_prox_map {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ConvexOn ℝ Set.univ F) :
    ∃ P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      (∀ z w, F (P z) + inner ℝ (z - P z) (w - P z) ≤ F w) ∧
      LipschitzWith 1 P ∧
      (∀ x q, (∀ w, F x + inner ℝ q (w - x) ≤ F w) → P (x + q) = x) := by
  -- key estimate
  have K : ∀ z z' x x' : EuclideanSpace ℝ (Fin n),
      (∀ w, F x + inner ℝ (z - x) (w - x) ≤ F w) →
      (∀ w, F x' + inner ℝ (z' - x') (w - x') ≤ F w) → ‖x - x'‖ ≤ ‖z - z'‖ := by
    intro z z' x x' hx hx'
    have h1 := hx x'
    have h2 := hx' x
    have e : inner ℝ (z - x) (x' - x) + inner ℝ (z' - x') (x - x') =
        ‖x - x'‖ ^ 2 - inner ℝ (z - z') (x - x') := by
      have hx'x : x' - x = -(x - x') := by abel
      rw [hx'x, inner_neg_right, ← real_inner_self_eq_norm_sq]
      have : z - x = (z - z') + (z' - x') - (x - x') := by abel
      rw [this, inner_sub_left, inner_add_left]
      ring
    have hcs := real_inner_le_norm (z - z') (x - x')
    have hle : ‖x - x'‖ ^ 2 ≤ ‖z - z'‖ * ‖x - x'‖ := by linarith
    rcases (norm_nonneg (x - x')).eq_or_lt with h0 | hpos
    · rw [← h0]; exact norm_nonneg _
    · nlinarith
  have hcont : Continuous F := hF.locallyLipschitz.continuous
  -- existence of the proximal point
  have hex : ∀ z : EuclideanSpace ℝ (Fin n), ∃ x : EuclideanSpace ℝ (Fin n),
      ∀ w, F x + inner ℝ (z - x) (w - x) ≤ F w := by
    intro z
    let G : EuclideanSpace ℝ (Fin n) → ℝ := fun y => F y + (1 / 2 : ℝ) * ‖y - z‖ ^ 2
    have hG : Continuous G := by fun_prop
    obtain ⟨q₀, hq₀⟩ := convex_exists_subgradient F hF z
    obtain ⟨x, -, hxmin⟩ := (isCompact_closedBall z (2 * ‖q₀‖)).exists_isMinOn
      ⟨z, mem_closedBall_self (by positivity)⟩ hG.continuousOn
    have hGz : G x ≤ G z := hxmin (mem_closedBall_self (by positivity))
    have hglob : ∀ y, G x ≤ G y := by
      intro y
      by_cases hy : y ∈ closedBall z (2 * ‖q₀‖)
      · exact hxmin hy
      · rw [mem_closedBall, dist_eq_norm, not_le] at hy
        have h1 := hq₀ y
        have h2 := neg_le_of_abs_le (abs_real_inner_le_norm q₀ (y - z))
        have h3 : 0 ≤ ‖y - z‖ * (‖y - z‖ - 2 * ‖q₀‖) :=
          mul_nonneg (norm_nonneg _) (by linarith)
        have : G z ≤ G y := by
          simp only [G, sub_self, norm_zero]
          nlinarith
        linarith
    refine ⟨x, fun w => ?_⟩
    -- first-order condition
    have step : ∀ t : ℝ, 0 < t → t ≤ 1 →
        0 ≤ F w - F x - inner ℝ (z - x) (w - x) + t / 2 * ‖w - x‖ ^ 2 := by
      intro t ht ht1
      have hy : x + t • (w - x) = (1 - t) • x + t • w := by
        rw [smul_sub, sub_smul, one_smul]; abel
      have hconv := hF.2 (Set.mem_univ x) (Set.mem_univ w) (by linarith : 0 ≤ 1 - t) ht.le
        (by ring)
      rw [← hy, smul_eq_mul, smul_eq_mul] at hconv
      have hmin := hglob (x + t • (w - x))
      have enorm : ‖x + t • (w - x) - z‖ ^ 2 =
          ‖x - z‖ ^ 2 + 2 * t * inner ℝ (x - z) (w - x) + t ^ 2 * ‖w - x‖ ^ 2 := by
        have : x + t • (w - x) - z = (x - z) + t • (w - x) := by abel
        rw [this, norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow,
          Real.norm_eq_abs, sq_abs]
        ring
      simp only [G] at hmin
      rw [enorm] at hmin
      have einner : inner ℝ (z - x) (w - x) = - inner ℝ (x - z) (w - x) := by
        rw [← inner_neg_left, neg_sub]
      rw [einner]
      have key : 0 ≤ t * (F w - F x + inner ℝ (x - z) (w - x) + t / 2 * ‖w - x‖ ^ 2) := by
        nlinarith
      have := (mul_nonneg_iff_of_pos_left ht).mp key
      linarith
    by_contra hcon
    rw [not_le] at hcon
    set A := F w - F x - inner ℝ (z - x) (w - x) with hA
    have hAneg : A < 0 := by rw [hA]; linarith
    set M := ‖w - x‖ ^ 2 with hM
    have hM0 : 0 ≤ M := by positivity
    set t := min 1 (-A / (M + 1)) with ht
    have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) (by linarith))
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht2 : t ≤ -A / (M + 1) := min_le_right _ _
    have h := step t ht0 ht1
    have : t * (M + 1) ≤ -A := (le_div_iff₀ (by linarith)).mp ht2
    nlinarith
  choose P hP using hex
  refine ⟨P, hP, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun z z' => ?_
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact K z z' (P z) (P z') (hP z) (hP z')
  · intro x q hq
    have h := K (x + q) (x + q) (P (x + q)) x (hP (x + q)) (by simpa using hq)
    rw [sub_self, norm_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
