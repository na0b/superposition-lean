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
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem quadratic_upper_bound_conditions {n : ℕ} (γ : EuclideanSpace ℝ (Fin n))
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.IsHermitian)
    (hloc : ∀ κ > 0, ∃ η > 0, ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ < η →
      inner ℝ γ h + (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin G h) h ≤ κ * ‖h‖ ^ 2) :
    γ = 0 ∧ (-G).PosSemidef := by
  let qG : EuclideanSpace ℝ (Fin n) → ℝ := fun h => inner ℝ (Matrix.toEuclideanLin G h) h
  have hqG : ∀ (t : ℝ) h, qG (t • h) = t ^ 2 * qG h := by
    intro t h
    simp only [qG, map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  -- γ = 0
  have hγ0 : γ = 0 := by
    obtain ⟨η, hη, hηP⟩ := hloc 1 one_pos
    by_contra hne
    have hγpos : 0 < ‖γ‖ := norm_pos_iff.mpr hne
    set Y := 1 - 1 / 2 * qG γ / ‖γ‖ ^ 2 with hY
    set t := min (η / (2 * ‖γ‖)) (1 / (2 * (|Y| + 1))) with ht
    have ht0 : 0 < t := lt_min (by positivity) (by positivity)
    have hth : ‖t • γ‖ < η := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have : t ≤ η / (2 * ‖γ‖) := min_le_left _ _
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith
    have h1 := hηP (t • γ) hth
    have h1' : t * ‖γ‖ ^ 2 + 1 / 2 * (t ^ 2 * qG γ) ≤ 1 * (t ^ 2 * ‖γ‖ ^ 2) := by
      have e1 := hqG t γ
      simp only [qG] at e1
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, e1, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht0, mul_pow] at h1
      exact h1
    -- divide by t ‖γ‖²
    have h2 : 1 ≤ t * Y := by
      have hg2 : 0 < ‖γ‖ ^ 2 := by positivity
      have : t * ‖γ‖ ^ 2 * 1 ≤ t * ‖γ‖ ^ 2 * (t * Y) := by
        rw [hY]
        have : t * ‖γ‖ ^ 2 * (t * (1 - 1 / 2 * qG γ / ‖γ‖ ^ 2))
            = t ^ 2 * ‖γ‖ ^ 2 - 1 / 2 * (t ^ 2 * qG γ) := by field_simp
        rw [this]; linarith
      exact le_of_mul_le_mul_left this (by positivity)
    have h3 : t * Y ≤ t * |Y| := mul_le_mul_of_nonneg_left (le_abs_self Y) ht0.le
    have h4 : t * (2 * (|Y| + 1)) ≤ 1 := by
      have : t ≤ 1 / (2 * (|Y| + 1)) := min_le_right _ _
      rwa [le_div_iff₀ (by positivity)] at this
    nlinarith [abs_nonneg Y]
  -- the quadratic form is nonpositive
  have hqneg : ∀ e, qG e ≤ 0 := by
    intro e
    have h4 : ∀ κ > 0, qG e ≤ 2 * κ * ‖e‖ ^ 2 := by
      intro κ hκ
      obtain ⟨η, hη, hηP⟩ := hloc κ hκ
      set t := η / (2 * (‖e‖ + 1)) with ht
      have ht0 : 0 < t := by positivity
      have hth : ‖t • e‖ < η := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
        have : t * (2 * (‖e‖ + 1)) = η := by rw [ht]; field_simp
        nlinarith [norm_nonneg e]
      have h1 := hηP (t • e) hth
      have e1 := hqG t e
      simp only [qG] at e1
      rw [hγ0, inner_zero_left, zero_add, e1, norm_smul, Real.norm_eq_abs, abs_of_pos ht0,
        mul_pow] at h1
      have ht2 : 0 < t ^ 2 := by positivity
      have : t ^ 2 * qG e ≤ t ^ 2 * (2 * κ * ‖e‖ ^ 2) := by linarith
      exact le_of_mul_le_mul_left this ht2
    by_contra hpos
    rw [not_le] at hpos
    have h5 := h4 (qG e / (4 * (‖e‖ ^ 2 + 1))) (by positivity)
    have h6 : 2 * (qG e / (4 * (‖e‖ ^ 2 + 1))) * ‖e‖ ^ 2 < qG e := by
      rw [show 2 * (qG e / (4 * (‖e‖ ^ 2 + 1))) * ‖e‖ ^ 2
          = qG e * (‖e‖ ^ 2 / (2 * (‖e‖ ^ 2 + 1))) by field_simp; ring]
      have : ‖e‖ ^ 2 / (2 * (‖e‖ ^ 2 + 1)) < 1 := by
        rw [div_lt_one (by positivity)]; nlinarith [sq_nonneg ‖e‖]
      nlinarith
    linarith
  refine ⟨hγ0, Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hG.neg, fun x => ?_⟩⟩
  have e : star x ⬝ᵥ ((-G) *ᵥ x) = -(qG (WithLp.toLp 2 x)) := by
    simp [qG, Matrix.toLpLin_apply, PiLp.inner_apply, dotProduct, Matrix.neg_mulVec]
  rw [e]
  linarith [hqneg (WithLp.toLp 2 x)]
