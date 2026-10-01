import Superposition.ConeComparisonAbove
/-- Comparison with cones from below: `-u` satisfies comparison with cones from above. -/
def ConeComparisonBelow {X : Type*} [MetricSpace X] (Ω : Set X) (u : X → ℝ) : Prop :=
  ConeComparisonAbove Ω (fun x => -u x)
