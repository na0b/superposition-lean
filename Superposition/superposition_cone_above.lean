import Superposition.IsGeodesicSpace
import Superposition.IsOpenDomain
import Superposition.ConeComparisonAbove
import Superposition.slice_right_admissible
import Superposition.slice_left_admissible
import Superposition.disjointSum_continuousOn_locallyBddAbove

set_option linter.unusedVariables false in
/-- Paper, Theorem "Superposition for comparison with cones" (comparison from above), with the
product `X × Y` carrying the ℓ¹ metric `d₁ = d_X + d_Y` via `WithLp 1`.

The hypotheses `hX`, `hY` (geodesic), `hU`, `hV` (domains) and `hUX`, `hVY` (proper subsets)
are kept so that the statement matches the paper; the proof does not use them. -/
theorem superposition_cone_above {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [ProperSpace X] [ProperSpace Y] (hX : IsGeodesicSpace X) (hY : IsGeodesicSpace Y)
    (U : Set X) (V : Set Y) (hU : IsOpenDomain U) (hV : IsOpenDomain V)
    (hUX : U ≠ Set.univ) (hVY : V ≠ Set.univ)
    (u : X → ℝ) (v : Y → ℝ) (hu : ContinuousOn u U) (hv : ContinuousOn v V)
    (hcu : ConeComparisonAbove U u) (hcv : ConeComparisonAbove V v) :
    ContinuousOn (fun z : WithLp 1 (X × Y) => u z.fst + v z.snd)
      {z : WithLp 1 (X × Y) | z.fst ∈ U ∧ z.snd ∈ V} ∧
    ConeComparisonAbove {z : WithLp 1 (X × Y) | z.fst ∈ U ∧ z.snd ∈ V}
      (fun z : WithLp 1 (X × Y) => u z.fst + v z.snd) := by
  obtain ⟨hcont, hbdd⟩ :=
    disjointSum_continuousOn_locallyBddAbove U V u v hu hv hcu.1 hcv.1
  refine ⟨hcont, hbdd, ?_⟩
  intro zh c κ O hzh hzhO hκ hO hOb hOc hOW hfr z0 hz0
  have hdist : ∀ a b : WithLp 1 (X × Y), dist a b = dist a.fst b.fst + dist a.snd b.snd :=
    fun a b => by simpa using WithLp.prod_dist_eq_add (p := 1) (by norm_num) a b
  have hmk : ∀ z : WithLp 1 (X × Y), WithLp.toLp 1 (z.fst, z.snd) = z := fun z => rfl
  by_contra hlt
  push Not at hlt
  have hz0O : z0 ∈ O := by
    by_contra h
    have hfz := hfr z0 ⟨hz0, by rw [hO.interior_eq]; exact h⟩
    linarith
  -- Y-slice at `zh.fst`
  obtain ⟨hSo, hSb, hSc, hSV, -, hSfr⟩ :=
    slice_right_admissible U V O zh.fst hO hOb hOc hOW
  have hYslice : ∀ y ∈ closure {y : Y | WithLp.toLp 1 (zh.fst, y) ∈ O},
      v y ≤ (c - u zh.fst) + κ * dist zh.snd y := by
    refine hcv.2 zh.snd (c - u zh.fst) κ _ hzh.2 ?_ hκ hSo hSb hSc hSV ?_
    · intro h
      exact hzhO (by simpa [hmk] using h)
    · intro y hy
      have h1 := hfr _ (hSfr hy)
      rw [hdist] at h1
      simp only [WithLp.toLp_fst, WithLp.toLp_snd, dist_self, zero_add] at h1
      linarith
  have hx0 : z0.fst ≠ zh.fst := by
    intro h
    have hy0 : z0.snd ∈ closure {y : Y | WithLp.toLp 1 (zh.fst, y) ∈ O} := by
      apply subset_closure
      show WithLp.toLp 1 (zh.fst, z0.snd) ∈ O
      rw [← h, hmk]; exact hz0O
    have h1 := hYslice _ hy0
    rw [hdist, h, dist_self] at hlt
    linarith
  -- X-slice at `z0.snd`, with the vertex `zh.fst` removed
  obtain ⟨hTo, hTb, hTc, hTU, hTcl, hTfr⟩ :=
    slice_left_admissible U V O z0.snd zh.fst hO hOb hOc hOW
  have hXslice := hcu.2 zh.fst (c + κ * dist zh.snd z0.snd - v z0.snd) κ _ hzh.1
    (fun h => h.2 rfl) hκ hTo hTb hTc hTU ?_ z0.fst
    (subset_closure ⟨by show WithLp.toLp 1 (z0.fst, z0.snd) ∈ O; rw [hmk]; exact hz0O, hx0⟩)
  · rw [hdist] at hlt
    linarith
  · intro x hx
    rcases hTfr hx with hxf | hxe
    · have h1 := hfr _ hxf
      rw [hdist] at h1
      simp only [WithLp.toLp_fst, WithLp.toLp_snd] at h1
      linarith
    · have hxe' : x = zh.fst := hxe
      subst hxe'
      rw [dist_self, mul_zero, add_zero]
      by_cases hin : WithLp.toLp 1 (zh.fst, z0.snd) ∈ O
      · have h1 := hYslice z0.snd (subset_closure hin)
        linarith
      · have hcl : WithLp.toLp 1 (zh.fst, z0.snd) ∈ closure O := hTcl (frontier_subset_closure hx)
        have h1 := hfr _ ⟨hcl, by rw [hO.interior_eq]; exact hin⟩
        rw [hdist] at h1
        simp only [WithLp.toLp_fst, WithLp.toLp_snd, dist_self] at h1
        linarith
