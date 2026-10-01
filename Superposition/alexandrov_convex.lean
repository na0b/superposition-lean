import Superposition.convex_prox_map
import Superposition.lipschitz_image_null
import Superposition.convex_second_order_of_subgradient_expansion
import Superposition.convex_locally_lipschitz
import Superposition.convex_exists_subgradient
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
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Convex.Continuous
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem alexandrov_convex {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ConvexOn ℝ Set.univ F) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ a : EuclideanSpace ℝ (Fin n), ∃ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian ∧
        (fun y => F y - F x - inner ℝ a (y - x)
          - (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin A (y - x)) (y - x))
          =o[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
  obtain ⟨P, hP1, hPlip, hP3⟩ := convex_prox_map F hF
  have hFc : Continuous F := hF.locallyLipschitz.continuous
  -- Step 1: exceptional set
  let N2 : Set (EuclideanSpace ℝ (Fin n)) := {z | ¬ DifferentiableAt ℝ P z}
  let S : Set (EuclideanSpace ℝ (Fin n)) :=
    {z | DifferentiableAt ℝ P z ∧ (fderiv ℝ P z).det = 0}
  have hN2 : volume N2 = 0 := by
    have := hPlip.ae_differentiableAt (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    rwa [ae_iff] at this
  have hPN2 : volume (P '' N2) = 0 := lipschitz_image_null P N2 1 hPlip.lipschitzOnWith hN2
  have hPS : volume (P '' S) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume (s := S) (f' := fun z => fderiv ℝ P z)
      (fun z hz => hz.1.hasFDerivAt.hasFDerivWithinAt) (fun z hz => hz.2)
  -- Steps 2-6 at a good point
  have key : ∀ x, x ∉ P '' N2 → x ∉ P '' S →
      ∃ a : EuclideanSpace ℝ (Fin n), ∃ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian ∧
        (fun y => F y - F x - inner ℝ a (y - x)
          - (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin A (y - x)) (y - x))
          =o[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
    intro x hxN2 hxS
    -- Step 2: a good preimage
    obtain ⟨a, ha⟩ := convex_exists_subgradient F hF x
    have hPz : P (x + a) = x := hP3 x a ha
    have hdiff : DifferentiableAt ℝ P (x + a) := by
      by_contra h
      exact hxN2 ⟨x + a, h, hPz⟩
    set D := fderiv ℝ P (x + a) with hDdef
    have hD : HasFDerivAt P D (x + a) := hdiff.hasFDerivAt
    have hdet : D.det ≠ 0 := by
      intro h
      exact hxS ⟨x + a, ⟨hdiff, h⟩, hPz⟩
    have hu : IsUnit (D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :=
      (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    let Bl : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := ↑(hu.unit⁻¹)
    have hBD : ∀ v, Bl (D v) = v := fun v => by
      change ((↑hu.unit⁻¹ : Module.End ℝ (EuclideanSpace ℝ (Fin n))) *
        (hu.unit : Module.End ℝ (EuclideanSpace ℝ (Fin n)))) v = v
      rw [hu.unit.inv_mul]; rfl
    have hDB : ∀ w, D (Bl w) = w := fun w => by
      change ((hu.unit : Module.End ℝ (EuclideanSpace ℝ (Fin n))) *
        (↑hu.unit⁻¹ : Module.End ℝ (EuclideanSpace ℝ (Fin n)))) w = w
      rw [hu.unit.mul_inv]; rfl
    let B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      LinearMap.toContinuousLinearMap Bl
    have hB : ∀ w, B w = Bl w := fun w => rfl
    set m : ℝ := 1 / (‖B‖ + 1) with hm
    have hm0 : 0 < m := by positivity
    have hDlow : ∀ v, m * ‖v‖ ≤ ‖D v‖ := by
      intro v
      have h1 : ‖v‖ ≤ ‖B‖ * ‖D v‖ := by
        calc ‖v‖ = ‖B (D v)‖ := by rw [hB, hBD]
          _ ≤ ‖B‖ * ‖D v‖ := B.le_opNorm _
      have h2 : ‖v‖ ≤ (‖B‖ + 1) * ‖D v‖ := by nlinarith [norm_nonneg (D v)]
      rw [hm, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      linarith
    have hBup : ∀ w, ‖B w‖ ≤ ‖w‖ / m := by
      intro w
      rw [hm, div_div_eq_mul_div, div_one]
      calc ‖B w‖ ≤ ‖B‖ * ‖w‖ := B.le_opNorm _
        _ ≤ ‖w‖ * (‖B‖ + 1) := by nlinarith [norm_nonneg w]
    -- Step 3: the subdifferential at x is {a}
    have hsub3 : ∀ a', (∀ w, F x + inner ℝ a' (w - x) ≤ F w) → a' = a := by
      intro a' ha'
      set v := a' - a with hv
      have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → P ((x + a) + t • v) = x := by
        intro t ht0 ht1
        have hsub : ∀ w, F x + inner ℝ (a + t • v) (w - x) ≤ F w := by
          intro w
          have h1 := ha w
          have h2 := ha' w
          rw [inner_add_left, real_inner_smul_left, hv, inner_sub_left]
          nlinarith
        rw [add_assoc]
        exact hP3 x _ hsub
      have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hD)
      rw [Asymptotics.isLittleO_iff] at hlo
      obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.mp (hlo (half_pos hm0))
      set t : ℝ := min 1 (δ / (2 * (‖v‖ + 1))) with ht
      have ht0 : 0 < t := lt_min one_pos (by positivity)
      have ht1 : t ≤ 1 := min_le_left _ _
      have ht2 : t ≤ δ / (2 * (‖v‖ + 1)) := min_le_right _ _
      have htv : dist (t • v) 0 < δ := by
        rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
        have : t * (2 * (‖v‖ + 1)) ≤ δ := (le_div_iff₀ (by positivity)).mp ht2
        nlinarith [norm_nonneg v]
      have hb := hδP htv
      rw [hseg t ht0.le ht1, hPz, sub_self, zero_sub, norm_neg, map_smul, norm_smul, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht0] at hb
      have hb2 : ‖D v‖ ≤ m / 2 * ‖v‖ := by
        have := hb
        nlinarith
      have hl := hDlow v
      have hv0 : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
      rw [norm_eq_zero, hv, sub_eq_zero] at hv0
      exact hv0
    -- Step 4: subgradients near x are close to a
    have hstep4 : ∀ σ > 0, ∃ τ > 0, ∀ y q : EuclideanSpace ℝ (Fin n), ‖y - x‖ < τ →
        (∀ w, F y + inner ℝ q (w - y) ≤ F w) → ‖q - a‖ < σ := by
      obtain ⟨Λ, -, -, hΛ⟩ := convex_locally_lipschitz F hF x 1
      by_contra hcon
      push Not at hcon
      obtain ⟨σ, hσ, hbad⟩ := hcon
      have hbad' : ∀ k : ℕ, ∃ y q : EuclideanSpace ℝ (Fin n), ‖y - x‖ < 1 / ((k : ℝ) + 1) ∧
          (∀ w, F y + inner ℝ q (w - y) ≤ F w) ∧ σ ≤ ‖q - a‖ := by
        intro k
        obtain ⟨y, q, h1, h2, h3⟩ := hbad (1 / ((k : ℝ) + 1)) (by positivity)
        exact ⟨y, q, h1, h2, h3⟩
      choose ys qs hys hqs hσs using hbad'
      have hqsb : ∀ k, qs k ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) Λ := by
        intro k
        rw [mem_closedBall, dist_zero_right]
        refine hΛ (ys k) ?_ (qs k) (hqs k)
        rw [mem_closedBall, dist_eq_norm]
        refine (hys k).le.trans ?_
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      obtain ⟨qstar, -, φ, hφ, hlim⟩ := (isCompact_closedBall _ _).tendsto_subseq hqsb
      have hylim : Tendsto ys atTop (𝓝 x) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        exact squeeze_zero (fun k => norm_nonneg _) (fun k => (hys k).le)
          tendsto_one_div_add_atTop_nhds_zero_nat
      have hylim' : Tendsto (ys ∘ φ) atTop (𝓝 x) := hylim.comp hφ.tendsto_atTop
      have hstar : ∀ w, F x + inner ℝ qstar (w - x) ≤ F w := by
        intro w
        have hT : Tendsto (fun k => F ((ys ∘ φ) k) + inner ℝ ((qs ∘ φ) k) (w - (ys ∘ φ) k))
            atTop (𝓝 (F x + inner ℝ qstar (w - x))) :=
          ((hFc.tendsto x).comp hylim').add (hlim.inner (tendsto_const_nhds.sub hylim'))
        exact le_of_tendsto' hT fun k => hqs (φ k) w
      have hqa : qstar = a := hsub3 qstar hstar
      have hT2 : Tendsto (fun k => ‖(qs ∘ φ) k - a‖) atTop (𝓝 ‖qstar - a‖) :=
        (hlim.sub_const a).norm
      have := ge_of_tendsto' hT2 fun k => hσs (φ k)
      rw [hqa, sub_self, norm_zero] at this
      linarith
    -- Step 5: first-order expansion of subgradients
    let A₀ : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.toEuclideanLin.symm ((B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
        - LinearMap.id)
    have hA₀ : ∀ h, Matrix.toEuclideanLin A₀ h = B h - h := by
      intro h
      simp [A₀]
    have hexp : ∀ κ > 0, ∃ τ > 0, ∀ y q : EuclideanSpace ℝ (Fin n), ‖y - x‖ < τ →
        (∀ w, F y + inner ℝ q (w - y) ≤ F w) →
        ‖q - a - Matrix.toEuclideanLin A₀ (y - x)‖ ≤ κ * ‖y - x‖ := by
      intro κ hκ
      set θ : ℝ := min (m / 2) (κ * m ^ 2 / 2) with hθ
      have hθ0 : 0 < θ := lt_min (half_pos hm0) (by positivity)
      have hθ1 : θ ≤ m / 2 := min_le_left _ _
      have hθ2 : θ ≤ κ * m ^ 2 / 2 := min_le_right _ _
      have hlo := hasFDerivAt_iff_isLittleO.mp hD
      rw [Asymptotics.isLittleO_iff] at hlo
      obtain ⟨τθ, hτθ, hτθP⟩ := Metric.eventually_nhds_iff.mp (hlo hθ0)
      obtain ⟨τ4, hτ4, hτ4P⟩ := hstep4 (τθ / 2) (half_pos hτθ)
      refine ⟨min τ4 (τθ / 2), lt_min hτ4 (half_pos hτθ), fun y q hy hq => ?_⟩
      have hy4 : ‖y - x‖ < τ4 := lt_of_lt_of_le hy (min_le_left _ _)
      have hyθ : ‖y - x‖ < τθ / 2 := lt_of_lt_of_le hy (min_le_right _ _)
      have hqa := hτ4P y q hy4 hq
      have hPy : P (y + q) = y := hP3 y q hq
      set d := y + q - (x + a) with hd
      have hd' : d = (y - x) + (q - a) := by rw [hd]; abel
      have hdn : ‖d‖ < τθ := by
        rw [hd']
        calc ‖(y - x) + (q - a)‖ ≤ ‖y - x‖ + ‖q - a‖ := norm_add_le _ _
          _ < τθ / 2 + τθ / 2 := add_lt_add hyθ hqa
          _ = τθ := by ring
      have hdist : dist (y + q) (x + a) < τθ := by rw [dist_eq_norm]; exact hdn
      have he := hτθP hdist
      rw [hPy, hPz] at he
      set e := y - x - D d with he_def
      have heb : ‖e‖ ≤ θ * ‖d‖ := he
      -- ‖d‖ ≤ (2/m) ‖y - x‖
      have hDd : D d = (y - x) - e := by rw [he_def]; abel
      have h1 : m * ‖d‖ ≤ 2 * ‖y - x‖ := by
        have := hDlow d
        rw [hDd] at this
        have h3 : ‖(y - x) - e‖ ≤ ‖y - x‖ + ‖e‖ := norm_sub_le _ _
        nlinarith [norm_nonneg d]
      -- d = B (y - x) - B e
      have hdB : d = B (y - x) - B e := by
        rw [← map_sub, ← hDd, hB, hBD]
      have hgoal : q - a - Matrix.toEuclideanLin A₀ (y - x) = -(B e) := by
        rw [hA₀]
        have : q - a = d - (y - x) := by rw [hd']; abel
        rw [this, hdB]; abel
      rw [hgoal, norm_neg]
      have h4 : ‖B e‖ * m ≤ ‖e‖ := by
        have := hBup e
        rwa [le_div_iff₀ hm0] at this
      have h5 : ‖e‖ ≤ κ * m ^ 2 / 2 * ‖d‖ :=
        heb.trans (mul_le_mul_of_nonneg_right hθ2 (norm_nonneg _))
      have h6 : ‖B e‖ * m ≤ κ * m * ‖y - x‖ := by
        have : κ * m ^ 2 / 2 * ‖d‖ = κ * m / 2 * (m * ‖d‖) := by ring
        have h7 : κ * m / 2 * (m * ‖d‖) ≤ κ * m / 2 * (2 * ‖y - x‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        linarith
      have h8 : ‖B e‖ * m ≤ (κ * ‖y - x‖) * m := by linarith
      exact le_of_mul_le_mul_right h8 hm0
    -- Step 6: conclusion
    obtain ⟨hherm, hlo⟩ := convex_second_order_of_subgradient_expansion F hF x a A₀ hexp
    exact ⟨a, _, hherm, hlo⟩
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (measure_union_null hPN2 hPS)
  by_contra hcon
  rw [mem_union, not_or] at hcon
  exact hx (key x hcon.1 hcon.2)
