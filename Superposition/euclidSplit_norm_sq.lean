module

public import Superposition.EuclidFst
public import Superposition.EuclidSnd
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Topology.EMetricSpace.Lipschitz

@[expose] public section
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem euclidSplit_norm_sq {n m : ℕ} (z : EuclideanSpace ℝ (Fin (n + m))) :
    ‖z‖ ^ 2 = ‖EuclidFst z‖ ^ 2 + ‖EuclidSnd (n := n) z‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, EuclidFst, EuclidSnd]
  rw [Fin.sum_univ_add]
