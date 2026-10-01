import Superposition.IsOpenDomain
import Superposition.IsDegenerateElliptic
import Superposition.IsSubadditiveOperator
import Superposition.IsViscositySubsolution
import Superposition.c2_local_max_to_strict_quadratic
import Superposition.sum_subsolution_quadratic_strict
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

theorem superposition_common_subsolution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpenDomain Ω) (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω)
    (L : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ → ℝ)
    (hLc : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × Matrix (Fin n) (Fin n) ℝ => L p.1 p.2)
      (Set.univ ×ˢ {X | X.IsHermitian}))
    (hLe : IsDegenerateElliptic L) (hLs : IsSubadditiveOperator L)
    (u v : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : IsViscositySubsolution Ω L f u) (hv : IsViscositySubsolution Ω L g v) :
    IsViscositySubsolution Ω L (fun x => f x + g x) (fun x => u x + v x) := by
  have hΩo : IsOpen Ω := hΩ.1
  refine ⟨hu.1.add hv.1, ?_⟩
  intro x₀ hx₀ ψ hψ hmax
  have hbound : ∀ η : ℝ, 0 < η →
      L (gradient ψ x₀) (EuclidHessian ψ x₀ + (2 * η) • (1 : Matrix (Fin n) (Fin n) ℝ))
        ≤ f x₀ + g x₀ := by
    intro η hη
    obtain ⟨hH, r, hr, hball, hq⟩ :=
      c2_local_max_to_strict_quadratic Ω hΩo ψ hψ (fun x => u x + v x) x₀ hx₀ hmax η hη
    have hPH : (EuclidHessian ψ x₀ + (2 * η) • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
      refine hH.add ?_
      simp [Matrix.IsHermitian]
    refine sum_subsolution_quadratic_strict Ω f g hf hg L hLc hLe hLs u v hu hv x₀ r hr hball
      (ψ x₀) (gradient ψ x₀) _ hPH ?_
    intro y hy hne
    have h1 := hq y hy
    have h2 : 0 < η / 2 * ‖y - x₀‖ ^ 2 := by
      have : 0 < ‖y - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      positivity
    linarith
  -- limit η → 0⁺
  have hA := (show (EuclidHessian ψ x₀).IsHermitian from
    (c2_local_max_to_strict_quadratic Ω hΩo ψ hψ (fun x => u x + v x) x₀ hx₀ hmax 1 one_pos).1)
  have hT : Tendsto (fun δ : ℝ => (gradient ψ x₀,
        EuclidHessian ψ x₀ + (2 * δ) • (1 : Matrix (Fin n) (Fin n) ℝ)))
      (𝓝[>] 0) (𝓝[Set.univ ×ˢ {X | X.IsHermitian}] (gradient ψ x₀, EuclidHessian ψ x₀)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun δ : ℝ => (gradient ψ x₀,
          EuclidHessian ψ x₀ + (2 * δ) • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
        fun_prop
      have := hc.tendsto 0
      simp only [mul_zero, zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · refine Filter.Eventually.of_forall fun δ => ⟨trivial, ?_⟩
      refine hA.add ?_
      simp [Matrix.IsHermitian]
  have hL := (hLc (gradient ψ x₀, EuclidHessian ψ x₀) ⟨trivial, hA⟩).tendsto.comp hT
  exact le_of_tendsto hL (eventually_nhdsWithin_of_forall fun δ hδ => hbound δ hδ)
