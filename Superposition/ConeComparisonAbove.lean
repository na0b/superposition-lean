import Superposition.Preamble
/-- Comparison with cones from above (paper Def. `def cpc`). The function `u` is modelled as a
total function on `X`; only its values on `Ω` enter. -/
def ConeComparisonAbove {X : Type*} [MetricSpace X] (Ω : Set X) (u : X → ℝ) : Prop :=
  (∀ x ∈ Ω, ∃ t ∈ nhds x, BddAbove (u '' (t ∩ Ω))) ∧
  ∀ (xh : X) (c κ : ℝ) (O : Set X), xh ∈ Ω → xh ∉ O → 0 ≤ κ →
    IsOpen O → Bornology.IsBounded O → IsCompact (closure O) → closure O ⊆ Ω →
    (∀ x ∈ frontier O, u x ≤ c + κ * dist xh x) →
    ∀ x ∈ closure O, u x ≤ c + κ * dist xh x
