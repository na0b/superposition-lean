import Superposition.SupConvolution
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

theorem supConvolution_properties {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKne : K.Nonempty)
    (hu : UpperSemicontinuousOn u K) (ε : ℝ) (hε : 0 < ε) :
    (∀ x, ∀ y ∈ K, u y - ‖x - y‖ ^ 2 / (2 * ε) ≤ SupConvolution u K ε x) ∧
    (∀ x, ∃ xh ∈ K, SupConvolution u K ε x = u xh - ‖x - xh‖ ^ 2 / (2 * ε)) ∧
    ConvexOn ℝ Set.univ (fun x => SupConvolution u K ε x + ‖x‖ ^ 2 / (2 * ε)) := by
  have _ := hε
  have hmaxer : ∀ x : EuclideanSpace ℝ (Fin n), ∃ xh ∈ K,
      IsMaxOn (fun y => u y - ‖x - y‖ ^ 2 / (2 * ε)) K xh := by
    intro x
    have hc : Continuous (fun y : EuclideanSpace ℝ (Fin n) => -(‖x - y‖ ^ 2 / (2 * ε))) := by
      fun_prop
    have husc : UpperSemicontinuousOn (fun y => u y - ‖x - y‖ ^ 2 / (2 * ε)) K := by
      have := hu.add (hc.upperSemicontinuous.upperSemicontinuousOn K)
      simpa [sub_eq_add_neg] using this
    exact husc.exists_isMaxOn hKne hK
  have hgreat : ∀ x : EuclideanSpace ℝ (Fin n), ∃ xh ∈ K,
      IsGreatest ((fun y => u y - ‖x - y‖ ^ 2 / (2 * ε)) '' K)
        (u xh - ‖x - xh‖ ^ 2 / (2 * ε)) := by
    intro x
    obtain ⟨xh, hxh, hmax⟩ := hmaxer x
    exact ⟨xh, hxh, mem_image_of_mem _ hxh, forall_mem_image.2 fun y hy => hmax hy⟩
  have hii : ∀ x, ∃ xh ∈ K, SupConvolution u K ε x = u xh - ‖x - xh‖ ^ 2 / (2 * ε) := by
    intro x
    obtain ⟨xh, hxh, hg⟩ := hgreat x
    exact ⟨xh, hxh, hg.csSup_eq⟩
  have hi : ∀ x, ∀ y ∈ K, u y - ‖x - y‖ ^ 2 / (2 * ε) ≤ SupConvolution u K ε x := by
    intro x y hy
    obtain ⟨xh, _, hg⟩ := hgreat x
    exact le_csSup hg.bddAbove (mem_image_of_mem _ hy)
  refine ⟨hi, hii, convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  obtain ⟨z, hz, hzeq⟩ := hii (a • x + b • y)
  have e : ∀ p : EuclideanSpace ℝ (Fin n),
      ‖p - z‖ ^ 2 = ‖p‖ ^ 2 - 2 * inner ℝ p z + ‖z‖ ^ 2 := fun p => norm_sub_sq_real p z
  have hx := hi x z hz
  have hy := hi y z hz
  have hin : inner ℝ (a • x + b • y) z = a * inner ℝ x z + b * inner ℝ y z := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  simp only [smul_eq_mul]
  rw [hzeq, e, hin]
  rw [e] at hx hy
  have hx' := mul_le_mul_of_nonneg_left hx ha
  have hy' := mul_le_mul_of_nonneg_left hy hb
  obtain rfl : b = 1 - a := by linarith
  simp only [div_eq_mul_inv] at *
  nlinarith [hx', hy']
