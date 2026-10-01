import Superposition.Preamble
theorem slice_right_admissible {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (U : Set X) (V : Set Y) (O : Set (WithLp 1 (X × Y))) (xh : X)
    (hO : IsOpen O) (hOb : Bornology.IsBounded O) (hOc : IsCompact (closure O))
    (hOW : closure O ⊆ {z | z.fst ∈ U ∧ z.snd ∈ V}) :
    IsOpen {y : Y | WithLp.toLp 1 (xh, y) ∈ O} ∧
    Bornology.IsBounded {y : Y | WithLp.toLp 1 (xh, y) ∈ O} ∧
    IsCompact (closure {y : Y | WithLp.toLp 1 (xh, y) ∈ O}) ∧
    closure {y : Y | WithLp.toLp 1 (xh, y) ∈ O} ⊆ V ∧
    closure {y : Y | WithLp.toLp 1 (xh, y) ∈ O} ⊆
      {y : Y | WithLp.toLp 1 (xh, y) ∈ closure O} ∧
    frontier {y : Y | WithLp.toLp 1 (xh, y) ∈ O} ⊆
      {y : Y | WithLp.toLp 1 (xh, y) ∈ frontier O} := by
  set ι : Y → WithLp 1 (X × Y) := fun y => WithLp.toLp 1 (xh, y) with hι
  have hιc : Continuous ι :=
    (WithLp.prod_continuous_toLp 1 X Y).comp (continuous_const.prodMk continuous_id)
  have hdist : ∀ y y' : Y, dist (ι y) (ι y') = dist y y' := by
    intro y y'
    have := WithLp.prod_dist_eq_add (p := 1) (by norm_num) (ι y) (ι y')
    simpa [hι] using this
  have hS : {y : Y | WithLp.toLp 1 (xh, y) ∈ O} = ι ⁻¹' O := rfl
  have hemb : Topology.IsClosedEmbedding ι :=
    Function.LeftInverse.isClosedEmbedding (f := WithLp.snd) (fun y => rfl)
      (WithLp.continuous_snd 1 X Y) hιc
  rw [hS]
  have hcl : closure (ι ⁻¹' O) ⊆ ι ⁻¹' closure O := hιc.closure_preimage_subset O
  refine ⟨hO.preimage hιc, ?_, ?_, ?_, hcl, hιc.frontier_preimage_subset O⟩
  · obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hOb
    refine Metric.isBounded_iff.2 ⟨C, fun y hy y' hy' => ?_⟩
    rw [← hdist]; exact hC hy hy'
  · exact (hemb.isCompact_preimage hOc).of_isClosed_subset isClosed_closure hcl
  · intro y hy
    exact (hOW (hcl hy)).2
