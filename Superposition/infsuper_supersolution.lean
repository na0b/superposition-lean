import Superposition.IsOpenDomain
import Superposition.infsuper_subsolution
import Superposition.infLaplace_supersolution_iff_neg
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

theorem infsuper_supersolution {n m : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (V : Set (EuclideanSpace ℝ (Fin m)))
    (hU : IsOpenDomain U) (hV : IsOpenDomain V)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin m) → ℝ)
    (hu : IsViscositySupersolution U InfLaplaceOperator f u)
    (hv : IsViscositySupersolution V InfLaplaceOperator g v) :
    IsViscositySupersolution {z : EuclideanSpace ℝ (Fin (n + m)) | EuclidFst z ∈ U ∧ EuclidSnd (n := n) z ∈ V}
      InfLaplaceOperator (fun z => f (EuclidFst z) + g (EuclidSnd (n := n) z))
      (fun z => u (EuclidFst z) + v (EuclidSnd (n := n) z)) := by
  rw [infLaplace_supersolution_iff_neg]
  have hu' := (infLaplace_supersolution_iff_neg U f u).1 hu
  have hv' := (infLaplace_supersolution_iff_neg V g v).1 hv
  have h := infsuper_subsolution U V hU hV (fun x => -f x) (fun y => -g y) hf.neg hg.neg
    (fun x => -u x) (fun y => -v y) hu' hv'
  convert h using 2 <;> ring
