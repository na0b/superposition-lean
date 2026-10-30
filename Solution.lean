module

public import Superposition

/-!
# Proofs of the Challenge statements

Each theorem below has exactly the statement of its counterpart in `Challenge.lean` and is proved
by the corresponding result of the `Superposition` development. Comparator checks that the
statements agree and that only `propext`, `Classical.choice` and `Quot.sound` are used.
-/

@[expose] public section

namespace Superposition

section infsuper_subsolution
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem infsuper_subsolution {n m : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (V : Set (EuclideanSpace ℝ (Fin m)))
    (hU : IsOpenDomain U) (hV : IsOpenDomain V)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin m) → ℝ)
    (hu : IsViscositySubsolution U InfLaplaceOperator f u)
    (hv : IsViscositySubsolution V InfLaplaceOperator g v) :
    IsViscositySubsolution {z : EuclideanSpace ℝ (Fin (n + m)) | EuclidFst z ∈ U ∧ EuclidSnd (n := n) z ∈ V}
      InfLaplaceOperator (fun z => f (EuclidFst z) + g (EuclidSnd (n := n) z))
      (fun z => u (EuclidFst z) + v (EuclidSnd (n := n) z)) := by
  exact _root_.infsuper_subsolution U V hU hV f g hf hg u v hu hv

end infsuper_subsolution

section infsuper_supersolution
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
  exact _root_.infsuper_supersolution U V hU hV f g hf hg u v hu hv

end infsuper_supersolution

section infsuper_solution
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
      (fun z => u (EuclidFst z) + v (EuclidSnd (n := n) z)) := by
  exact _root_.infsuper_solution U V hU hV f g hf hg u v hu hv

end infsuper_solution

section superposition_common_subsolution
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem superposition_common_subsolution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpenDomain Ω) (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω)
    (L : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ → ℝ)
    (hLc : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × Matrix (Fin n) (Fin n) ℝ => L p.1 p.2)
      (Set.univ ×ˢ {X | X.IsHermitian}))
    (hLe : IsDegenerateElliptic L) (hLs : IsSubadditiveOperator L)
    (u v : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : IsViscositySubsolution Ω L f u) (hv : IsViscositySubsolution Ω L g v) :
    IsViscositySubsolution Ω L (fun x => f x + g x) (fun x => u x + v x) := by
  exact _root_.superposition_common_subsolution Ω hΩ f g hf hg L hLc hLe hLs u v hu hv

end superposition_common_subsolution

section superposition_cone_above

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
  exact _root_.superposition_cone_above hX hY U V hU hV hUX hVY u v hu hv hcu hcv

end superposition_cone_above

section superposition_cone_below

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
  exact _root_.superposition_cone_below hX hY U V hU hV hUX hVY u v hu hv hcu hcv

end superposition_cone_below

section superposition_cone_both

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
  exact _root_.superposition_cone_both hX hY U V hU hV hUX hVY u v hu hv hcu hcv

end superposition_cone_both

end Superposition
