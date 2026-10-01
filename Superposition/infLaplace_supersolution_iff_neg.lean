import Superposition.InfLaplaceOperator
import Superposition.IsViscositySubsolution
import Superposition.IsViscositySupersolution
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
import Mathlib.Analysis.Calculus.ContDiff.Operations
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem infLaplace_supersolution_iff_neg {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f u : EuclideanSpace ℝ (Fin n) → ℝ) :
    IsViscositySupersolution Ω InfLaplaceOperator f u ↔
      IsViscositySubsolution Ω InfLaplaceOperator (fun x => -f x) (fun x => -u x) := by
  -- derivative identities
  have hfd : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      fderiv ℝ (fun y => -ψ y) = fun y => -fderiv ℝ ψ y := fun ψ => funext fun y => fderiv_neg
  have hgrad : ∀ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) x,
      gradient (fun y => -ψ y) x = -gradient ψ x := by
    intro ψ x
    simp only [gradient, hfd, map_neg]
  have hhess : ∀ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) x,
      EuclidHessian (fun y => -ψ y) x = -EuclidHessian ψ x := by
    intro ψ x
    ext i j
    simp only [EuclidHessian, hfd, Matrix.of_apply, Matrix.neg_apply]
    rw [show fderiv ℝ (fun y => -fderiv ℝ ψ y) x = -fderiv ℝ (fderiv ℝ ψ) x from fderiv_neg]
    rfl
  have hL : ∀ (ξ : EuclideanSpace ℝ (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ), InfLaplaceOperator (-ξ) (-X) = -InfLaplaceOperator ξ X := by
    intro ξ X
    simp [InfLaplaceOperator, map_neg, inner_neg_right]
  have hLneg : ∀ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) x,
      InfLaplaceOperator (gradient (fun y => -ψ y) x) (EuclidHessian (fun y => -ψ y) x)
        = -InfLaplaceOperator (gradient ψ x) (EuclidHessian ψ x) := by
    intro ψ x; rw [hgrad, hhess, hL]
  constructor
  · rintro ⟨hl, hs⟩
    refine ⟨fun x hx y hy => ?_, fun x₀ hx₀ ψ hψ hmax => ?_⟩
    · filter_upwards [hl x hx (-y) (by linarith)] with x' hx'
      linarith
    · have hmin : IsLocalMin (fun x => u x - (fun y => -ψ y) x) x₀ := by
        have := hmax.neg
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        simp only; ring
      have := hs x₀ hx₀ (fun y => -ψ y) (ContDiffOn.neg hψ) hmin
      rw [hLneg] at this
      linarith
  · rintro ⟨hl, hs⟩
    refine ⟨fun x hx y hy => ?_, fun x₀ hx₀ ψ hψ hmin => ?_⟩
    · filter_upwards [hl x hx (-y) (by linarith)] with x' hx'
      linarith
    · have hmax : IsLocalMax (fun x => -u x - (fun y => -ψ y) x) x₀ := by
        have := hmin.neg
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        simp only; ring
      have := hs x₀ hx₀ (fun y => -ψ y) (ContDiffOn.neg hψ) hmax
      rw [hLneg] at this
      linarith
