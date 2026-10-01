import Superposition.ConeComparisonBelow
import Superposition.superposition_cone_above
theorem superposition_cone_below {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [ProperSpace X] [ProperSpace Y] (hX : IsGeodesicSpace X) (hY : IsGeodesicSpace Y)
    (U : Set X) (V : Set Y) (hU : IsOpenDomain U) (hV : IsOpenDomain V)
    (hUX : U ≠ Set.univ) (hVY : V ≠ Set.univ)
    (u : X → ℝ) (v : Y → ℝ) (hu : ContinuousOn u U) (hv : ContinuousOn v V)
    (hcu : ConeComparisonBelow U u) (hcv : ConeComparisonBelow V v) :
    ContinuousOn (fun z : WithLp 1 (X × Y) => u z.fst + v z.snd)
      {z : WithLp 1 (X × Y) | z.fst ∈ U ∧ z.snd ∈ V} ∧
    ConeComparisonBelow {z : WithLp 1 (X × Y) | z.fst ∈ U ∧ z.snd ∈ V}
      (fun z : WithLp 1 (X × Y) => u z.fst + v z.snd) := by
  obtain ⟨hc, hcc⟩ := superposition_cone_above hX hY U V hU hV hUX hVY
    (fun x => -u x) (fun y => -v y) hu.neg hv.neg hcu hcv
  refine ⟨?_, ?_⟩
  · refine hc.neg.congr ?_
    intro z _
    simp only [Pi.neg_apply]
    ring
  · unfold ConeComparisonBelow
    have heq : (fun z : WithLp 1 (X × Y) => -(u z.fst + v z.snd)) =
        (fun z : WithLp 1 (X × Y) => -u z.fst + -v z.snd) := by
      funext z; ring
    rw [heq]; exact hcc
