import Superposition.Preamble
/-- A metric space is geodesic if any two points `x, y` are joined by a geodesic, i.e. a
curve `γ` with `γ 0 = x`, `γ (d(x,y)) = y` that is an isometry on `[0, d(x,y)]`. -/
def IsGeodesicSpace (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ : ℝ → X, γ 0 = x ∧ γ (dist x y) = y ∧
    ∀ s ∈ Set.Icc (0 : ℝ) (dist x y), ∀ t ∈ Set.Icc (0 : ℝ) (dist x y),
      dist (γ s) (γ t) = |s - t|
