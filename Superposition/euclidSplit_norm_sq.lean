import Superposition.EuclidFst
import Superposition.EuclidSnd
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

theorem euclidSplit_norm_sq {n m : ℕ} (z : EuclideanSpace ℝ (Fin (n + m))) :
    ‖z‖ ^ 2 = ‖EuclidFst z‖ ^ 2 + ‖EuclidSnd (n := n) z‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, EuclidFst, EuclidSnd]
  rw [Fin.sum_univ_add]
