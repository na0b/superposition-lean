import Superposition.Preamble
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
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem convex_locally_lipschitz {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ConvexOn ℝ Set.univ F) (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      (∀ y ∈ closedBall x₀ R, ∀ y' ∈ closedBall x₀ R, |F y - F y'| ≤ Λ * ‖y - y'‖) ∧
      (∀ y ∈ closedBall x₀ R, ∀ q : EuclideanSpace ℝ (Fin n),
        (∀ w, F y + inner ℝ q (w - y) ≤ F w) → ‖q‖ ≤ Λ) := by
  obtain ⟨K, hK⟩ := (hF.locallyLipschitz.locallyLipschitzOn (s := closedBall x₀ (R + 1))
    ).exists_lipschitzOnWith_of_compact (isCompact_closedBall x₀ (R + 1))
  have hsub : closedBall x₀ R ⊆ closedBall x₀ (R + 1) := closedBall_subset_closedBall (by linarith)
  have hL : ∀ y ∈ closedBall x₀ (R + 1), ∀ y' ∈ closedBall x₀ (R + 1),
      |F y - F y'| ≤ (K : ℝ) * ‖y - y'‖ := by
    intro y hy y' hy'
    have := hK.dist_le_mul y hy y' hy'
    rwa [Real.dist_eq, dist_eq_norm] at this
  refine ⟨K, K.2, fun y hy y' hy' => hL y (hsub hy) y' (hsub hy'), ?_⟩
  intro y hy q hq
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  set w := y + ‖q‖⁻¹ • q with hw
  have hwy : w - y = ‖q‖⁻¹ • q := by rw [hw]; abel
  have hnorm : ‖w - y‖ = 1 := by
    rw [hwy, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hwmem : w ∈ closedBall x₀ (R + 1) := by
    rw [mem_closedBall] at hy ⊢
    calc dist w x₀ ≤ dist w y + dist y x₀ := dist_triangle _ _ _
      _ ≤ 1 + R := by rw [dist_eq_norm, hnorm]; linarith
      _ = R + 1 := by ring
  have hinner : inner ℝ q (w - y) = ‖q‖ := by
    rw [hwy, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have h1 := hq w
  have h2 := hL w hwmem y (hsub hy)
  rw [hnorm, mul_one] at h2
  have := (abs_le.mp h2).2
  linarith
