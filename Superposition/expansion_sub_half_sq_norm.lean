import Superposition.Preamble
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.EMetricSpace.Lipschitz
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem expansion_sub_half_sq_norm {n : ℕ} (w : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ)
    (hε : 0 < ε) (y a0 : EuclideanSpace ℝ (Fin n)) (A0 : Matrix (Fin n) (Fin n) ℝ)
    (hlo : (fun z => (w z + ‖z‖ ^ 2 / (2 * ε)) - (w y + ‖y‖ ^ 2 / (2 * ε)) - inner ℝ a0 (z - y)
        - (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin A0 (z - y)) (z - y))
        =o[𝓝 y] (fun z => ‖z - y‖ ^ 2)) :
    ∀ κ > 0, ∀ᶠ z in 𝓝 y, |w z - w y - inner ℝ (a0 - (1 / ε) • y) (z - y)
      - (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin
          (A0 - (1 / ε) • (1 : Matrix (Fin n) (Fin n) ℝ)) (z - y)) (z - y)|
        ≤ κ * ‖z - y‖ ^ 2 := by
  have hId : ∀ h : EuclideanSpace ℝ (Fin n), ∀ s : ℝ,
      Matrix.toEuclideanLin (s • (1 : Matrix (Fin n) (Fin n) ℝ)) h = s • h := by
    intro h s
    rw [map_smul]
    simp
  intro κ hκ
  rw [Asymptotics.isLittleO_iff] at hlo
  filter_upwards [hlo hκ] with z hz
  rw [Real.norm_eq_abs, norm_pow, norm_norm] at hz
  convert hz using 2
  have ez : ‖z‖ ^ 2 = ‖y‖ ^ 2 + 2 * inner ℝ y (z - y) + ‖z - y‖ ^ 2 := by
    have : z = y + (z - y) := by abel
    conv_lhs => rw [this]
    rw [norm_add_sq_real]
  have hA0 : ∀ h, Matrix.toEuclideanLin (A0 - (1 / ε) • (1 : Matrix (Fin n) (Fin n) ℝ)) h
      = Matrix.toEuclideanLin A0 h - (1 / ε) • h := by
    intro h; rw [map_sub, LinearMap.sub_apply, hId]
  rw [hA0, inner_sub_left, inner_sub_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, ez]
  field_simp
  ring
