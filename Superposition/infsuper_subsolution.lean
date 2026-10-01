import Superposition.IsOpenDomain
import Superposition.c2_local_max_to_strict_quadratic
import Superposition.disjoint_sum_quadratic_strict
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

theorem infsuper_subsolution {n m : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (V : Set (EuclideanSpace ℝ (Fin m)))
    (hU : IsOpenDomain U) (hV : IsOpenDomain V)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin m) → ℝ)
    (hu : IsViscositySubsolution U InfLaplaceOperator f u)
    (hv : IsViscositySubsolution V InfLaplaceOperator g v) :
    IsViscositySubsolution {z : EuclideanSpace ℝ (Fin (n + m)) | EuclidFst z ∈ U ∧ EuclidSnd (n := n) z ∈ V}
      InfLaplaceOperator (fun z => f (EuclidFst z) + g (EuclidSnd (n := n) z))
      (fun z => u (EuclidFst z) + v (EuclidSnd (n := n) z)) := by
  have cfst : Continuous (fun z : EuclideanSpace ℝ (Fin (n + m)) => EuclidFst z) := by
    unfold EuclidFst; fun_prop
  have csnd : Continuous (fun z : EuclideanSpace ℝ (Fin (n + m)) => EuclidSnd (n := n) z) := by
    unfold EuclidSnd; fun_prop
  set Ω := {z : EuclideanSpace ℝ (Fin (n + m)) | EuclidFst z ∈ U ∧ EuclidSnd (n := n) z ∈ V}
    with hΩdef
  have hΩo : IsOpen Ω := (hU.1.preimage cfst).inter (hV.1.preimage csnd)
  have huΩ : UpperSemicontinuousOn (fun z => u (EuclidFst z)) Ω := by
    intro z hz y hy
    exact (cfst.continuousWithinAt.tendsto_nhdsWithin (fun w hw => hw.1)).eventually
      (hu.1 _ hz.1 y hy)
  have hvΩ : UpperSemicontinuousOn (fun z => v (EuclidSnd (n := n) z)) Ω := by
    intro z hz y hy
    exact (csnd.continuousWithinAt.tendsto_nhdsWithin (fun w hw => hw.2)).eventually
      (hv.1 _ hz.2 y hy)
  refine ⟨huΩ.add hvΩ, ?_⟩
  intro z₀ hz₀ ψ hψ hmax
  have hL : ∀ (c : EuclideanSpace ℝ (Fin (n + m))) (H : Matrix (Fin (n + m)) (Fin (n + m)) ℝ)
      (s : ℝ), InfLaplaceOperator c (H + s • (1 : Matrix (Fin (n + m)) (Fin (n + m)) ℝ))
        = InfLaplaceOperator c H - s * ‖c‖ ^ 2 := by
    intro c H s
    have e : inner ℝ (Matrix.toEuclideanLin (s • (1 : Matrix (Fin (n + m)) (Fin (n + m)) ℝ)) c) c
        = s * ‖c‖ ^ 2 := by
      simp [inner_smul_left]
    simp only [InfLaplaceOperator, map_add, LinearMap.add_apply, inner_add_left, e]
    ring
  have hbound : ∀ η : ℝ, 0 < η →
      InfLaplaceOperator (gradient ψ z₀) (EuclidHessian ψ z₀)
        ≤ f (EuclidFst z₀) + g (EuclidSnd (n := n) z₀) + 2 * η * ‖gradient ψ z₀‖ ^ 2 := by
    intro η hη
    obtain ⟨hH, r, hr, hball, hq⟩ :=
      c2_local_max_to_strict_quadratic Ω hΩo ψ hψ
        (fun z => u (EuclidFst z) + v (EuclidSnd (n := n) z)) z₀ hz₀ hmax η hη
    have hPH : (EuclidHessian ψ z₀ + (2 * η) •
        (1 : Matrix (Fin (n + m)) (Fin (n + m)) ℝ)).IsHermitian := by
      refine hH.add ?_
      simp [Matrix.IsHermitian]
    have := disjoint_sum_quadratic_strict U V f g hf hg u v hu hv z₀ r hr hball
      (ψ z₀) (gradient ψ z₀) _ hPH (by
        intro y hy hne
        have h1 := hq y hy
        have h2 : 0 < η / 2 * ‖y - z₀‖ ^ 2 := by
          have : 0 < ‖y - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
          positivity
        linarith)
    rw [hL] at this
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hc := sq_nonneg ‖gradient ψ z₀‖
  have hη : 0 < ε / (2 * ‖gradient ψ z₀‖ ^ 2 + 1) := by positivity
  have hb := hbound _ hη
  have : 2 * (ε / (2 * ‖gradient ψ z₀‖ ^ 2 + 1)) * ‖gradient ψ z₀‖ ^ 2 ≤ ε := by
    rw [mul_comm 2, mul_assoc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith
