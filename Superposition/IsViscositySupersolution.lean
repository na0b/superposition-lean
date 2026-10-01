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
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

def IsViscositySupersolution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (L : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ → ℝ)
    (f u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  LowerSemicontinuousOn u Ω ∧
  ∀ x₀ ∈ Ω, ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ 2 ψ Ω →
    IsLocalMin (fun x => u x - ψ x) x₀ → f x₀ ≤ L (gradient ψ x₀) (EuclidHessian ψ x₀)
