import Superposition.ConeComparisonBoth
import Superposition.superposition_cone_below
theorem superposition_cone_both {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [ProperSpace X] [ProperSpace Y] (hX : IsGeodesicSpace X) (hY : IsGeodesicSpace Y)
    (U : Set X) (V : Set Y) (hU : IsOpenDomain U) (hV : IsOpenDomain V)
    (hUX : U ≠ Set.univ) (hVY : V ≠ Set.univ)
    (u : X → ℝ) (v : Y → ℝ) (hu : ContinuousOn u U) (hv : ContinuousOn v V)
    (hcu : ConeComparisonBoth U u) (hcv : ConeComparisonBoth V v) :
    ContinuousOn (fun z : WithLp 1 (X × Y) => u z.fst + v z.snd)
      {z : WithLp 1 (X × Y) | z.fst ∈ U ∧ z.snd ∈ V} ∧
    ConeComparisonBoth {z : WithLp 1 (X × Y) | z.fst ∈ U ∧ z.snd ∈ V}
      (fun z : WithLp 1 (X × Y) => u z.fst + v z.snd) := by
  obtain ⟨hc, ha⟩ := superposition_cone_above hX hY U V hU hV hUX hVY u v hu hv hcu.1 hcv.1
  obtain ⟨-, hb⟩ := superposition_cone_below hX hY U V hU hV hUX hVY u v hu hv hcu.2 hcv.2
  exact ⟨hc, ha, hb⟩
