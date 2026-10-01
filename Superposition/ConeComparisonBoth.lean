import Superposition.ConeComparisonBelow
/-- Comparison with cones (from both sides). -/
def ConeComparisonBoth {X : Type*} [MetricSpace X] (Ω : Set X) (u : X → ℝ) : Prop :=
  ConeComparisonAbove Ω u ∧ ConeComparisonBelow Ω u
