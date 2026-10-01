import Superposition.EuclidHessian
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
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem c2_local_max_to_strict_quadratic {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (hψ : ContDiffOn ℝ 2 ψ Ω)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ Ω)
    (hmax : IsLocalMax (fun x => w x - ψ x) x₀) (η : ℝ) (hη : 0 < η) :
    (EuclidHessian ψ x₀).IsHermitian ∧
    ∃ r > 0, closedBall x₀ r ⊆ Ω ∧ ∀ y ∈ closedBall x₀ r,
      w y - (ψ x₀ + inner ℝ (gradient ψ x₀) (y - x₀) + (1 / 2 : ℝ) *
        inner ℝ (Matrix.toEuclideanLin (EuclidHessian ψ x₀ + (2 * η) • (1 : Matrix (Fin n) (Fin n) ℝ))
          (y - x₀)) (y - x₀))
        ≤ w x₀ - ψ x₀ - η / 2 * ‖y - x₀‖ ^ 2 := by
  -- regularity
  have hψat : ∀ z ∈ Ω, ContDiffAt ℝ 2 ψ z := fun z hz => hψ.contDiffAt (hΩ.mem_nhds hz)
  have hD1 : ContDiffOn ℝ 1 (fderiv ℝ ψ) Ω := hψ.fderiv_of_isOpen hΩ (by norm_num)
  have hD2c : ContinuousOn (fderiv ℝ (fderiv ℝ ψ)) Ω :=
    (hD1.fderiv_of_isOpen hΩ (by norm_num) : ContDiffOn ℝ 0 _ Ω).continuousOn
  have hψd : ∀ z ∈ Ω, HasFDerivAt ψ (fderiv ℝ ψ z) z := fun z hz =>
    ((hψat z hz).differentiableAt (by norm_num)).hasFDerivAt
  have hD1d : ∀ z ∈ Ω, HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) z) z := fun z hz =>
    ((hD1.contDiffAt (hΩ.mem_nhds hz)).differentiableAt one_ne_zero).hasFDerivAt
  set D2 := fderiv ℝ (fderiv ℝ ψ) x₀ with hD2def
  have hsym : ∀ u v, D2 u v = D2 v u :=
    (hψat x₀ hx₀).isSymmSndFDerivAt (by simp)
  have hHerm : (EuclidHessian ψ x₀).IsHermitian := by
    ext i j
    simp [EuclidHessian, hD2def.symm, hsym]
  refine ⟨hHerm, ?_⟩
  -- quadratic-form identity
  have hquad : ∀ h : EuclideanSpace ℝ (Fin n),
      inner ℝ (Matrix.toEuclideanLin (EuclidHessian ψ x₀) h) h = D2 h h := by
    intro h
    have hH : ∀ i j, EuclidHessian ψ x₀ i j =
        D2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := fun i j => rfl
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr h]
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
      EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, ← hH, smul_eq_mul]
    simp [Matrix.toLpLin_apply, PiLp.inner_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hgrad : ∀ h, inner ℝ (gradient ψ x₀) h = fderiv ℝ ψ x₀ h := by
    intro h
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  -- radii
  obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  obtain ⟨ρ', hρ', hρ'max⟩ := Metric.eventually_nhds_iff.mp hmax
  have hcont : ContinuousAt (fderiv ℝ (fderiv ℝ ψ)) x₀ := hD2c.continuousAt (hΩ.mem_nhds hx₀)
  have hev : ∀ᶠ y in 𝓝 x₀, ‖fderiv ℝ (fderiv ℝ ψ) y - D2‖ < η / 2 := by
    have hc : ContinuousAt (fun y => ‖fderiv ℝ (fderiv ℝ ψ) y - D2‖) x₀ :=
      ContinuousAt.norm (f := fun y => fderiv ℝ (fderiv ℝ ψ) y - D2) (hcont.sub continuousAt_const)
    have := hc.eventually_lt continuousAt_const (show ‖fderiv ℝ (fderiv ℝ ψ) x₀ - D2‖ < η / 2 by
      rw [hD2def, sub_self, ContinuousLinearMap.opNorm_zero]; exact half_pos hη)
    exact this
  obtain ⟨ρ'', hρ'', hρ''c⟩ := Metric.eventually_nhds_iff.mp hev
  set R := min ρ (min ρ' ρ'') with hR
  have hR0 : 0 < R := lt_min hρ (lt_min hρ' hρ'')
  have hRρ : R ≤ ρ := min_le_left _ _
  have hRρ' : R ≤ ρ' := (min_le_right _ _).trans (min_le_left _ _)
  have hRρ'' : R ≤ ρ'' := (min_le_right _ _).trans (min_le_right _ _)
  have hBΩ : ball x₀ R ⊆ Ω := (ball_subset_ball hRρ).trans hρΩ
  -- first MVT: derivative estimate
  have hstep1 : ∀ z ∈ ball x₀ R,
      ‖fderiv ℝ ψ z - fderiv ℝ ψ x₀ - D2 (z - x₀)‖ ≤ η / 2 * ‖z - x₀‖ := by
    intro z hz
    have key := (convex_ball x₀ R).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun y => fderiv ℝ ψ y - D2 y)
      (f' := fun y => fderiv ℝ (fderiv ℝ ψ) y - D2)
      (fun y hy => ((hD1d y (hBΩ hy)).sub D2.hasFDerivAt).hasFDerivWithinAt)
      (fun y hy => by
        have : dist y x₀ < ρ'' := lt_of_lt_of_le (mem_ball.mp hy) hRρ''
        exact (hρ''c this).le)
      (mem_ball_self hR0) hz
    have e : fderiv ℝ ψ z - D2 z - (fderiv ℝ ψ x₀ - D2 x₀) =
        fderiv ℝ ψ z - fderiv ℝ ψ x₀ - D2 (z - x₀) := by
      rw [map_sub]; abel
    simpa [e] using key
  -- second MVT: Taylor estimate
  have hstep2 : ∀ y ∈ closedBall x₀ (R / 2),
      |ψ y - ψ x₀ - fderiv ℝ ψ x₀ (y - x₀) - (1 / 2 : ℝ) * D2 (y - x₀) (y - x₀)|
        ≤ η / 2 * ‖y - x₀‖ ^ 2 := by
    intro y hy
    set s := closedBall x₀ ‖y - x₀‖ with hs
    have hsB : s ⊆ ball x₀ R := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz hy
      rw [mem_ball, dist_eq_norm]
      linarith
    let φ : EuclideanSpace ℝ (Fin n) → ℝ := fun z =>
      ψ z - ψ x₀ - fderiv ℝ ψ x₀ (z - x₀) - (1 / 2 : ℝ) * D2 (z - x₀) (z - x₀)
    have hφd : ∀ z ∈ s, HasFDerivWithinAt φ
        (fderiv ℝ ψ z - fderiv ℝ ψ x₀ - D2 (z - x₀)) s z := by
      intro z hz
      have hl : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => z - x₀)
          (ContinuousLinearMap.id ℝ _) z := (hasFDerivAt_id z).sub_const x₀
      have hq := (D2.hasFDerivAt.comp z hl).clm_apply hl
      have hall := (((hψd z (hBΩ (hsB hz))).sub_const (ψ x₀)).sub
        ((fderiv ℝ ψ x₀).hasFDerivAt.comp z hl)).sub (hq.const_mul (1 / 2 : ℝ))
      refine (hall.congr_fderiv ?_).hasFDerivWithinAt
      refine ContinuousLinearMap.ext fun k => ?_
      simp only [_root_.sub_apply, _root_.add_apply, _root_.smul_apply, smul_eq_mul,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.flip_apply, Function.comp_apply]
      rw [hsym (z - x₀) k]
      ring
    have hbound : ∀ z ∈ s, ‖fderiv ℝ ψ z - fderiv ℝ ψ x₀ - D2 (z - x₀)‖ ≤ η / 2 * ‖y - x₀‖ := by
      intro z hz
      refine (hstep1 z (hsB hz)).trans ?_
      have : ‖z - x₀‖ ≤ ‖y - x₀‖ := by rw [hs, mem_closedBall, dist_eq_norm] at hz; exact hz
      gcongr
    have key := (convex_closedBall x₀ ‖y - x₀‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hφd hbound (mem_closedBall_self (norm_nonneg _)) (mem_closedBall.mpr (dist_eq_norm y x₀).le)
    have h0 : φ x₀ = 0 := by simp [φ]
    rw [h0, sub_zero, Real.norm_eq_abs] at key
    calc _ = |φ y| := rfl
      _ ≤ _ := key
      _ = _ := by ring
  -- conclusion
  refine ⟨R / 2, by linarith, ?_, ?_⟩
  · intro z hz
    apply hBΩ
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  · intro y hy
    have hmy : w y - ψ y ≤ w x₀ - ψ x₀ := by
      apply hρ'max
      rw [mem_closedBall] at hy
      linarith
    have hT := (abs_le.mp (hstep2 y hy)).2
    have hQ : inner ℝ (Matrix.toEuclideanLin (EuclidHessian ψ x₀ + (2 * η) • (1 : Matrix (Fin n) (Fin n) ℝ))
          (y - x₀)) (y - x₀) = D2 (y - x₀) (y - x₀) + 2 * η * ‖y - x₀‖ ^ 2 := by
      rw [map_add, LinearMap.add_apply, inner_add_left, hquad]
      simp [inner_smul_left]
    rw [hQ, hgrad]
    nlinarith
