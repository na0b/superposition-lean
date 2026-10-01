import Superposition.Preamble
import Mathlib.Analysis.InnerProductSpace.PiL2
open Filter
open scoped Topology

theorem jet_twosided_to_upper {k : ℕ} (w : EuclideanSpace ℝ (Fin k) → ℝ)
    (y a0 : EuclideanSpace ℝ (Fin k)) (A0 : Matrix (Fin k) (Fin k) ℝ) :
    (∀ κ > 0, ∀ᶠ x in 𝓝 y, |w x - w y - inner ℝ a0 (x - y)
      - (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin A0 (x - y)) (x - y)| ≤ κ * ‖x - y‖ ^ 2) →
    ∀ κ > 0, ∀ᶠ x in 𝓝 y, w x ≤ w y + inner ℝ a0 (x - y)
      + (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin A0 (x - y)) (x - y) + κ * ‖x - y‖ ^ 2 := by
  intro hj κ hκ
  filter_upwards [hj κ hκ] with x hx
  linarith [(abs_le.mp hx).2]
