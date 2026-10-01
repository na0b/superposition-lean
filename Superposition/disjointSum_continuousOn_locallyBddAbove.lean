import Superposition.Preamble
theorem disjointSum_continuousOn_locallyBddAbove {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (U : Set X) (V : Set Y) (u : X → ℝ) (v : Y → ℝ)
    (hu : ContinuousOn u U) (hv : ContinuousOn v V)
    (hbu : ∀ x ∈ U, ∃ t ∈ nhds x, BddAbove (u '' (t ∩ U)))
    (hbv : ∀ y ∈ V, ∃ t ∈ nhds y, BddAbove (v '' (t ∩ V))) :
    ContinuousOn (fun z : WithLp 1 (X × Y) => u z.fst + v z.snd)
      {z : WithLp 1 (X × Y) | z.fst ∈ U ∧ z.snd ∈ V} ∧
    ∀ z ∈ {z : WithLp 1 (X × Y) | z.fst ∈ U ∧ z.snd ∈ V},
      ∃ t ∈ nhds z, BddAbove ((fun z : WithLp 1 (X × Y) => u z.fst + v z.snd) ''
        (t ∩ {z : WithLp 1 (X × Y) | z.fst ∈ U ∧ z.snd ∈ V})) := by
  have hf := WithLp.continuous_fst 1 X Y
  have hs := WithLp.continuous_snd 1 X Y
  refine ⟨?_, ?_⟩
  · refine ContinuousOn.add ?_ ?_
    · exact hu.comp hf.continuousOn (fun z hz => hz.1)
    · exact hv.comp hs.continuousOn (fun z hz => hz.2)
  · rintro z ⟨hzU, hzV⟩
    obtain ⟨s, hs', ⟨A, hA⟩⟩ := hbu _ hzU
    obtain ⟨t, ht', ⟨B, hB⟩⟩ := hbv _ hzV
    refine ⟨WithLp.fst ⁻¹' s ∩ WithLp.snd ⁻¹' t,
      Filter.inter_mem (hf.continuousAt.preimage_mem_nhds hs')
        (hs.continuousAt.preimage_mem_nhds ht'), ⟨A + B, ?_⟩⟩
    rintro _ ⟨p, ⟨⟨hp1, hp2⟩, hpU, hpV⟩, rfl⟩
    exact add_le_add (hA ⟨p.fst, ⟨hp1, hpU⟩, rfl⟩) (hB ⟨p.snd, ⟨hp2, hpV⟩, rfl⟩)
