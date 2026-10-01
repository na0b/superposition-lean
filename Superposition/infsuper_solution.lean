import Superposition.IsViscositySolution
import Superposition.infsuper_subsolution
import Superposition.infsuper_supersolution
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

theorem infsuper_solution {n m : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (V : Set (EuclideanSpace ℝ (Fin m)))
    (hU : IsOpenDomain U) (hV : IsOpenDomain V)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin m) → ℝ)
    (hu : IsViscositySolution U InfLaplaceOperator f u)
    (hv : IsViscositySolution V InfLaplaceOperator g v) :
    IsViscositySolution {z : EuclideanSpace ℝ (Fin (n + m)) | EuclidFst z ∈ U ∧ EuclidSnd (n := n) z ∈ V}
      InfLaplaceOperator (fun z => f (EuclidFst z) + g (EuclidSnd (n := n) z))
      (fun z => u (EuclidFst z) + v (EuclidSnd (n := n) z)) :=
  ⟨infsuper_subsolution U V hU hV f g hf hg u v hu.1 hv.1,
   infsuper_supersolution U V hU hV f g hf hg u v hu.2 hv.2⟩
