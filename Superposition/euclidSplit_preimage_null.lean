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
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem euclidSplit_preimage_null {n m : ℕ} :
    (∀ N : Set (EuclideanSpace ℝ (Fin n)), volume N = 0 →
      volume {z : EuclideanSpace ℝ (Fin (n + m)) | EuclidFst z ∈ N} = 0) ∧
    (∀ N : Set (EuclideanSpace ℝ (Fin m)), volume N = 0 →
      volume {z : EuclideanSpace ℝ (Fin (n + m)) | EuclidSnd (n := n) z ∈ N} = 0) := by
  constructor
  · intro N hN
    let L : EuclideanSpace ℝ (Fin (n + m)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      { toFun := EuclidFst
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hs : Function.Surjective L := by
      intro x
      refine ⟨WithLp.toLp 2 (Fin.append (fun i => x i) (fun _ : Fin m => (0 : ℝ))), ?_⟩
      ext i
      show (EuclidFst _) i = _
      simp [EuclidFst, Fin.append_left]
    have hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        y ∈ (toMeasurable volume N)ᶜ := by
      rw [ae_iff]; simpa [measure_toMeasurable] using hN
    have := (ae_comp_linearMap_mem_iff L volume volume hs
      (measurableSet_toMeasurable _ _).compl).2 hae
    rw [ae_iff] at this
    refine measure_mono_null (fun z hz => ?_) this
    simp only [Set.mem_compl_iff, not_not]
    exact subset_toMeasurable _ _ hz
  · intro N hN
    let L : EuclideanSpace ℝ (Fin (n + m)) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
      { toFun := EuclidSnd (n := n)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hs : Function.Surjective L := by
      intro y
      refine ⟨WithLp.toLp 2 (Fin.append (fun _ : Fin n => (0 : ℝ)) (fun j => y j)), ?_⟩
      ext j
      show (EuclidSnd (n := n) _) j = _
      simp [EuclidSnd, Fin.append_right]
    have hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
        y ∈ (toMeasurable volume N)ᶜ := by
      rw [ae_iff]; simpa [measure_toMeasurable] using hN
    have := (ae_comp_linearMap_mem_iff L volume volume hs
      (measurableSet_toMeasurable _ _).compl).2 hae
    rw [ae_iff] at this
    refine measure_mono_null (fun z hz => ?_) this
    simp only [Set.mem_compl_iff, not_not]
    exact subset_toMeasurable _ _ hz
