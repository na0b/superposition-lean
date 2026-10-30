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
public import Mathlib.Geometry.Euclidean.Volume.Measure

@[expose] public section
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem lipschitz_image_null {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (s : Set (EuclideanSpace ℝ (Fin n))) (K : NNReal) (hf : LipschitzOnWith K f s)
    (hs : volume s = 0) : volume (f '' s) = 0 := by
  have hvol := Measure.isAddLeftInvariant_eq_smul
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (μH[n] : Measure (EuclideanSpace ℝ (Fin n)))
  have hc := Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n
  set c := Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (μH[n] : Measure (EuclideanSpace ℝ (Fin n))) with hcdef
  have hH : (μH[n] : Measure (EuclideanSpace ℝ (Fin n))) s = 0 := by
    rw [hvol, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at hs
    rcases hs with h | h
    · exact absurd (by exact_mod_cast h) hc
    · exact h
  have hH' : (μH[n] : Measure (EuclideanSpace ℝ (Fin n))) (f '' s) = 0 := by
    have := hf.hausdorffMeasure_image_le (d := n) (Nat.cast_nonneg n)
    rw [hH, mul_zero] at this
    exact le_antisymm this (zero_le)
  rw [hvol, Measure.smul_apply, hH', smul_zero]
