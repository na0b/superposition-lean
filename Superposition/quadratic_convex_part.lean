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
import Mathlib.Analysis.Matrix.Hermitian
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem quadratic_convex_part {n : ℕ} (x₀ c : EuclideanSpace ℝ (Fin n)) (q₀ lam : ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsHermitian)
    (hlam : ∀ h : EuclideanSpace ℝ (Fin n),
      inner ℝ (Matrix.toEuclideanLin P h) h ≤ lam * ‖h‖ ^ 2) :
    ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) => lam / 2 * ‖x‖ ^ 2
      - (q₀ + inner ℝ c (x - x₀)
        + (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin P (x - x₀)) (x - x₀))) := by
  have hPsym : (Matrix.toEuclideanLin P).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hP
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  set P' := Matrix.toEuclideanLin P
  let κf : EuclideanSpace ℝ (Fin n) → ℝ := fun x => lam / 2 * ‖x‖ ^ 2
      - (q₀ + inner ℝ c (x - x₀) + (1 / 2 : ℝ) * inner ℝ (P' (x - x₀)) (x - x₀))
  change κf (a • x + b • y) ≤ a • κf x + b • κf y
  set d := x - y with hd
  have hexp : ∀ t : ℝ, κf (y + t • d) = κf y
      + t * (lam * inner ℝ y d - inner ℝ c d - inner ℝ (P' (y - x₀)) d)
      + t ^ 2 * (lam / 2 * ‖d‖ ^ 2 - 1 / 2 * inner ℝ (P' d) d) := by
    intro t
    simp only [κf]
    have e1 : y + t • d - x₀ = (y - x₀) + t • d := by abel
    have hs : inner ℝ (P' d) (y - x₀) = inner ℝ (P' (y - x₀)) d := by
      rw [hPsym, real_inner_comm]
    rw [e1, norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [hs]
    ring
  have hK2 : 0 ≤ lam / 2 * ‖d‖ ^ 2 - 1 / 2 * inner ℝ (P' d) d := by
    have := hlam d; linarith
  have ex : x = y + (1 : ℝ) • d := by rw [one_smul, hd]; abel
  have exy : a • x + b • y = y + a • d := by
    rw [hd, smul_sub]
    have : b = 1 - a := by linarith
    rw [this, sub_smul, one_smul]; abel
  rw [exy, hexp, smul_eq_mul, smul_eq_mul]
  conv_rhs => rw [ex, hexp]
  have hb' : b = 1 - a := by linarith
  rw [hb']
  have ha1 : a ^ 2 ≤ a := by nlinarith
  have := mul_le_mul_of_nonneg_right ha1 hK2
  linarith
