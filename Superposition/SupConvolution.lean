module

public import Superposition.Preamble
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

noncomputable def SupConvolution {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun y => u y - ‖x - y‖ ^ 2 / (2 * ε)) '' K)
