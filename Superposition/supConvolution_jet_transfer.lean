import Superposition.supConvolution_properties
import Superposition.quadratic_test_subsolution
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

theorem supConvolution_jet_transfer {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (L : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ → ℝ)
    (hLc : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × Matrix (Fin n) (Fin n) ℝ => L p.1 p.2)
      (Set.univ ×ˢ {X | X.IsHermitian}))
    (f u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : IsViscositySubsolution Ω L f u)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (ε : ℝ) (hε : 0 < ε) (x xh : EuclideanSpace ℝ (Fin n)) (hxh : xh ∈ interior K)
    (hattain : SupConvolution u K ε x = u xh - ‖x - xh‖ ^ 2 / (2 * ε))
    (a : EuclideanSpace ℝ (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hjet : ∀ δ > 0, ∀ᶠ z in 𝓝 x, SupConvolution u K ε z ≤ SupConvolution u K ε x
      + inner ℝ a (z - x) + (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin A (z - x)) (z - x)
      + δ * ‖z - x‖ ^ 2) :
    L a A ≤ f xh := by
  have hKne : K.Nonempty := ⟨xh, interior_subset hxh⟩
  have huK : UpperSemicontinuousOn u K := hu.1.mono hKΩ
  have hi := (supConvolution_properties u K hK hKne huK ε hε).1
  have hxhΩ : xh ∈ Ω := hKΩ (interior_subset hxh)
  have hbound : ∀ δ : ℝ, 0 < δ → L a (A + (2 * δ) • (1 : Matrix (Fin n) (Fin n) ℝ)) ≤ f xh := by
    intro δ hδ
    obtain ⟨ρ₁, hρ₁, hρ₁j⟩ := Metric.eventually_nhds_iff.mp (hjet δ hδ)
    obtain ⟨ρ₂, hρ₂, hρ₂K⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxh)
    have hHerm : (A + (2 * δ) • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
      refine hA.add ?_
      simp [Matrix.IsHermitian]
    refine quadratic_test_subsolution Ω L f u hu xh hxhΩ (u xh) a _ hHerm ?_
    refine Metric.eventually_nhds_iff.mpr ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun y hy => ?_⟩
    have hy₁ : dist y xh < ρ₁ := lt_of_lt_of_le hy (min_le_left _ _)
    have hy₂ : y ∈ K := hρ₂K (lt_of_lt_of_le hy (min_le_right _ _))
    set z := y + (x - xh) with hz
    have hzx : z - x = y - xh := by rw [hz]; abel
    have hzy : x - z = xh - y := by rw [hz]; abel
    have h1 := hi z y hy₂
    have hzd : dist z x < ρ₁ := by rw [dist_eq_norm, hzx, ← dist_eq_norm]; exact hy₁
    have h2 := hρ₁j hzd
    have hzy' : ‖z - y‖ = ‖x - xh‖ := by rw [hz]; congr 1; abel
    rw [hzy'] at h1
    rw [hzx, hattain] at h2
    have hQ : inner ℝ (Matrix.toEuclideanLin (A + (2 * δ) • (1 : Matrix (Fin n) (Fin n) ℝ))
          (y - xh)) (y - xh) = inner ℝ (Matrix.toEuclideanLin A (y - xh)) (y - xh)
            + 2 * δ * ‖y - xh‖ ^ 2 := by
      rw [map_add, LinearMap.add_apply, inner_add_left]
      simp [inner_smul_left]
    simp only [hQ, sub_self, inner_zero_right, map_zero, mul_zero, add_zero]
    linarith
  -- limit δ → 0⁺
  have hT : Tendsto (fun δ : ℝ => (a, A + (2 * δ) • (1 : Matrix (Fin n) (Fin n) ℝ)))
      (𝓝[>] 0) (𝓝[Set.univ ×ˢ {X | X.IsHermitian}] (a, A)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun δ : ℝ => (a, A + (2 * δ) • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
        fun_prop
      have := hc.tendsto 0
      simp only [mul_zero, zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · refine Filter.Eventually.of_forall fun δ => ⟨trivial, ?_⟩
      refine hA.add ?_
      simp [Matrix.IsHermitian]
  have hL := (hLc (a, A) ⟨trivial, hA⟩).tendsto.comp hT
  exact le_of_tendsto hL (eventually_nhdsWithin_of_forall fun δ hδ => hbound δ hδ)
