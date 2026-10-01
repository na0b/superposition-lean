import Superposition.Preamble
theorem slice_left_admissible {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (U : Set X) (V : Set Y) (O : Set (WithLp 1 (X × Y))) (y0 : Y) (xh : X)
    (hO : IsOpen O) (hOb : Bornology.IsBounded O) (hOc : IsCompact (closure O))
    (hOW : closure O ⊆ {z | z.fst ∈ U ∧ z.snd ∈ V}) :
    IsOpen ({x : X | WithLp.toLp 1 (x, y0) ∈ O} \ {xh}) ∧
    Bornology.IsBounded ({x : X | WithLp.toLp 1 (x, y0) ∈ O} \ {xh}) ∧
    IsCompact (closure ({x : X | WithLp.toLp 1 (x, y0) ∈ O} \ {xh})) ∧
    closure ({x : X | WithLp.toLp 1 (x, y0) ∈ O} \ {xh}) ⊆ U ∧
    closure ({x : X | WithLp.toLp 1 (x, y0) ∈ O} \ {xh}) ⊆
      {x : X | WithLp.toLp 1 (x, y0) ∈ closure O} ∧
    frontier ({x : X | WithLp.toLp 1 (x, y0) ∈ O} \ {xh}) ⊆
      {x : X | WithLp.toLp 1 (x, y0) ∈ frontier O} ∪ {xh} := by
  set ι : X → WithLp 1 (X × Y) := fun x => WithLp.toLp 1 (x, y0) with hι
  have hιc : Continuous ι :=
    (WithLp.prod_continuous_toLp 1 X Y).comp (continuous_id.prodMk continuous_const)
  have hdist : ∀ x x' : X, dist (ι x) (ι x') = dist x x' := by
    intro x x'
    have := WithLp.prod_dist_eq_add (p := 1) (by norm_num) (ι x) (ι x')
    simpa [hι] using this
  have hA : {x : X | WithLp.toLp 1 (x, y0) ∈ O} = ι ⁻¹' O := rfl
  have hemb : Topology.IsClosedEmbedding ι :=
    Function.LeftInverse.isClosedEmbedding (f := WithLp.fst) (fun x => rfl)
      (WithLp.continuous_fst 1 X Y) hιc
  rw [hA]
  have hAo : IsOpen (ι ⁻¹' O) := hO.preimage hιc
  have hSo : IsOpen (ι ⁻¹' O \ {xh}) := hAo.sdiff isClosed_singleton
  have hcl : closure (ι ⁻¹' O \ {xh}) ⊆ ι ⁻¹' closure O :=
    (closure_mono Set.sdiff_subset).trans (hιc.closure_preimage_subset O)
  refine ⟨hSo, ?_, ?_, ?_, hcl, ?_⟩
  · obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hOb
    refine Metric.isBounded_iff.2 ⟨C, fun x hx x' hx' => ?_⟩
    rw [← hdist]; exact hC hx.1 hx'.1
  · exact (hemb.isCompact_preimage hOc).of_isClosed_subset isClosed_closure hcl
  · intro x hx
    exact (hOW (hcl hx)).1
  · intro x hx
    rw [hSo.frontier_eq] at hx
    obtain ⟨hxc, hxn⟩ := hx
    by_cases hxe : x = xh
    · exact Or.inr hxe
    · left
      have hxA : x ∉ ι ⁻¹' O := fun h => hxn ⟨h, hxe⟩
      have hxcA : x ∈ closure (ι ⁻¹' O) := closure_mono Set.sdiff_subset hxc
      have : x ∈ frontier (ι ⁻¹' O) := by
        rw [hAo.frontier_eq]; exact ⟨hxcA, hxA⟩
      exact hιc.frontier_preimage_subset O this
