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

def IsDegenerateElliptic {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ → ℝ) : Prop :=
  ∀ ξ X Y, X.IsHermitian → Y.IsHermitian → (X - Y).PosSemidef → L ξ X ≤ L ξ Y
