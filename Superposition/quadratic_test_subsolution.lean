import Superposition.IsViscositySubsolution
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
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Calculus
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem quadratic_test_subsolution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (L : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ → ℝ)
    (f u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : IsViscositySubsolution Ω L f u)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Ω) (c : ℝ) (a : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hmax : IsLocalMax (fun y => u y - (c + inner ℝ a (y - z)
      + (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin A (y - z)) (y - z))) z) :
    L a A ≤ f z := by
  let B : (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)
  have hB : ∀ v, B v = Matrix.toEuclideanLin A v := fun v => rfl
  have hsym : (Matrix.toEuclideanLin A).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  set P : (EuclideanSpace ℝ (Fin n)) → ℝ := fun y => c + inner ℝ a (y - z)
      + (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin A (y - z)) (y - z) with hP
  -- derivative of P
  let D : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := fun y => innerSL ℝ a + innerSL ℝ (B (y - z))
  have hD : ∀ y, HasFDerivAt P (D y) y := by
    intro y
    have h1 : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin n)) => y - z) (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y :=
      (hasFDerivAt_id y).sub_const z
    have h2 : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin n)) => B (y - z)) (B.comp (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) y :=
      B.hasFDerivAt.comp y h1
    have h3 := h2.inner ℝ h1
    have h4 := ((hasFDerivAt_const c y).add
      ((innerSL ℝ a).hasFDerivAt.comp y h1)).add (h3.const_mul (1 / 2 : ℝ))
    refine h4.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
    simp only [D, _root_.add_apply, innerSL_apply_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, zero_add, ContinuousLinearMap.prod_apply,
      _root_.smul_apply, smul_eq_mul, fderivInnerCLM_apply, hB]
    rw [hsym h (y - z), real_inner_comm (Matrix.toEuclideanLin A (y - z)) h]
    ring
  have hfd : fderiv ℝ P = D := funext fun y => (hD y).fderiv
  have hdiff : ContDiff ℝ 2 P := by
    have hl : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => y - z) := contDiff_id.sub contDiff_const
    exact (contDiff_const.add (contDiff_const.inner ℝ hl)).add
      (contDiff_const.mul ((B.contDiff.comp hl).inner ℝ hl))
  have hgrad : gradient P z = a := by
    rw [gradient, hfd]
    simp [D]
    exact (InnerProductSpace.toDual ℝ _).symm_apply_apply a
  have hD2 : HasFDerivAt D ((innerSL ℝ).comp B) z := by
    have h1 : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin n)) => y - z) (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) z :=
      (hasFDerivAt_id z).sub_const z
    have := (((innerSL ℝ).comp B).hasFDerivAt.comp z h1).const_add (innerSL ℝ a)
    simpa [D] using this
  have hhess : EuclidHessian P z = A := by
    ext i j
    simp only [EuclidHessian, Matrix.of_apply, hfd, hD2.fderiv, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, hB]
    simp [Matrix.toLpLin_apply, EuclideanSpace.inner_single_right]
    simpa using hA.apply i j
  have := hu.2 z hz P hdiff.contDiffOn hmax
  rwa [hgrad, hhess] at this
