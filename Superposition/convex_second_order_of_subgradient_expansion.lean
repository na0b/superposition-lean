import Superposition.convex_exists_subgradient
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

theorem convex_second_order_of_subgradient_expansion {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ConvexOn ℝ Set.univ F)
    (x a : EuclideanSpace ℝ (Fin n)) (A₀ : Matrix (Fin n) (Fin n) ℝ)
    (hexp : ∀ κ > 0, ∃ τ > 0, ∀ y q : EuclideanSpace ℝ (Fin n), ‖y - x‖ < τ →
      (∀ w, F y + inner ℝ q (w - y) ≤ F w) →
      ‖q - a - Matrix.toEuclideanLin A₀ (y - x)‖ ≤ κ * ‖y - x‖) :
    ((1 / 2 : ℝ) • (A₀ + A₀ᵀ)).IsHermitian ∧
    (fun y => F y - F x - inner ℝ a (y - x)
      - (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin ((1 / 2 : ℝ) • (A₀ + A₀ᵀ)) (y - x)) (y - x))
      =o[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
  refine ⟨?_, ?_⟩
  · ext i j
    simp [add_comm]
    ring
  have hquad : ∀ h : EuclideanSpace ℝ (Fin n),
      inner ℝ (Matrix.toEuclideanLin ((1 / 2 : ℝ) • (A₀ + A₀ᵀ)) h) h
        = inner ℝ (Matrix.toEuclideanLin A₀ h) h := by
    intro h
    simp only [Matrix.toLpLin_apply, PiLp.inner_apply, Matrix.mulVec, dotProduct,
      Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul, RCLike.inner_apply,
      conj_trivial, add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
    conv_lhs => arg 2; rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [Asymptotics.isLittleO_iff]
  intro κ hκ
  obtain ⟨τ, hτ, hτq⟩ := hexp κ hκ
  refine Metric.eventually_nhds_iff.mpr ⟨τ, hτ, fun y hy => ?_⟩
  rw [dist_eq_norm] at hy
  set h := y - x with hh
  have hq := fun z => convex_exists_subgradient F hF z
  choose Q hQ using hq
  set c := inner ℝ a h with hc
  set B := inner ℝ (Matrix.toEuclideanLin A₀ h) h with hB
  set e := κ * ‖h‖ ^ 2 with he
  rw [hquad, Real.norm_eq_abs, norm_pow, norm_norm]
  change |F y - F x - c - 1 / 2 * B| ≤ κ * ‖h‖ ^ 2
  -- estimate for each partition size N
  have hN : ∀ N : ℕ, 0 < N →
      |F y - F x - c - 1 / 2 * B| ≤ e + |B| / (2 * N) := by
    intro N hN0
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
    let yk : ℕ → EuclideanSpace ℝ (Fin n) := fun k => x + ((k : ℝ) / N) • h
    -- per-point estimate on subgradient pairings
    have hpt : ∀ k : ℕ, k ≤ N →
        |inner ℝ (Q (yk k)) h - c - (k : ℝ) / N * B| ≤ e := by
      intro k hk
      have htk0 : 0 ≤ (k : ℝ) / N := by positivity
      have htk1 : (k : ℝ) / N ≤ 1 := by
        rw [div_le_one hNr]; exact_mod_cast hk
      have hyk : yk k - x = ((k : ℝ) / N) • h := by simp [yk]
      have hnorm : ‖yk k - x‖ ≤ ‖h‖ := by
        rw [hyk, norm_smul, Real.norm_eq_abs, abs_of_nonneg htk0]
        exact mul_le_of_le_one_left (norm_nonneg _) htk1
      have hb := hτq (yk k) (Q (yk k)) (lt_of_le_of_lt hnorm hy) (hQ (yk k))
      rw [hyk, map_smul] at hb
      have hb' : ‖Q (yk k) - a - ((k : ℝ) / N) • Matrix.toEuclideanLin A₀ h‖ ≤ κ * ‖h‖ := by
        refine hb.trans ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htk0]
        have := mul_le_of_le_one_left (norm_nonneg h) htk1
        nlinarith
      have hcs := abs_real_inner_le_norm (Q (yk k) - a - ((k : ℝ) / N) • Matrix.toEuclideanLin A₀ h) h
      rw [inner_sub_left, inner_sub_left, real_inner_smul_left] at hcs
      calc _ = |inner ℝ (Q (yk k)) h - inner ℝ a h - (k : ℝ) / N * B| := rfl
        _ ≤ _ := hcs
        _ ≤ κ * ‖h‖ * ‖h‖ := mul_le_mul_of_nonneg_right hb' (norm_nonneg _)
        _ = e := by rw [he]; ring
    -- increments
    have hinc : ∀ k : ℕ, k < N →
        (1 / N : ℝ) * (c + (k : ℝ) / N * B - e) ≤ F (yk (k + 1)) - F (yk k) ∧
        F (yk (k + 1)) - F (yk k) ≤ (1 / N : ℝ) * (c + ((k : ℝ) + 1) / N * B + e) := by
      intro k hk
      have hd : yk (k + 1) - yk k = (1 / N : ℝ) • h := by
        simp only [yk]
        rw [add_sub_add_left_eq_sub, ← sub_smul]
        congr 1
        push_cast
        field_simp
        ring
      have hd' : yk k - yk (k + 1) = -((1 / N : ℝ) • h) := by
        rw [← hd, neg_sub]
      have h1 := hQ (yk k) (yk (k + 1))
      have h2 := hQ (yk (k + 1)) (yk k)
      rw [hd, real_inner_smul_right] at h1
      rw [hd', inner_neg_right, real_inner_smul_right] at h2
      have p1 := abs_le.mp (hpt k hk.le)
      have p2 := abs_le.mp (hpt (k + 1) hk)
      push_cast at p2
      have hN1 : (0 : ℝ) ≤ 1 / N := by positivity
      constructor
      · have := mul_le_mul_of_nonneg_left p1.1 hN1
        nlinarith
      · have := mul_le_mul_of_nonneg_left p2.2 hN1
        nlinarith
    -- cumulative bounds by induction
    have hcum : ∀ m : ℕ, m ≤ N →
        (m : ℝ) / N * (c - e) + B * ((m : ℝ) * ((m : ℝ) - 1)) / (2 * (N : ℝ) ^ 2)
          ≤ F (yk m) - F x ∧
        F (yk m) - F x ≤
          (m : ℝ) / N * (c + e) + B * ((m : ℝ) * ((m : ℝ) + 1)) / (2 * (N : ℝ) ^ 2) := by
      intro m
      induction m with
      | zero => intro _; simp [yk]
      | succ m ih =>
        intro hm
        obtain ⟨l, u⟩ := ih (Nat.le_of_succ_le hm)
        obtain ⟨il, iu⟩ := hinc m (Nat.lt_of_succ_le hm)
        push_cast
        constructor
        · have : (m : ℝ) / N * (c - e) + B * ((m : ℝ) * ((m : ℝ) - 1)) / (2 * (N : ℝ) ^ 2)
              + (1 / N : ℝ) * (c + (m : ℝ) / N * B - e)
              = ((m : ℝ) + 1) / N * (c - e) + B * (((m : ℝ) + 1) * ((m : ℝ) + 1 - 1)) / (2 * (N : ℝ) ^ 2) := by
            field_simp; ring
          linarith
        · have : (m : ℝ) / N * (c + e) + B * ((m : ℝ) * ((m : ℝ) + 1)) / (2 * (N : ℝ) ^ 2)
              + (1 / N : ℝ) * (c + ((m : ℝ) + 1) / N * B + e)
              = ((m : ℝ) + 1) / N * (c + e) + B * (((m : ℝ) + 1) * ((m : ℝ) + 1 + 1)) / (2 * (N : ℝ) ^ 2) := by
            field_simp; ring
          linarith
    obtain ⟨l, u⟩ := hcum N le_rfl
    have hyN : yk N = y := by
      simp only [yk, div_self hNr.ne', one_smul, hh]; abel
    rw [hyN] at l u
    have el : (N : ℝ) / N * (c - e) + B * ((N : ℝ) * ((N : ℝ) - 1)) / (2 * (N : ℝ) ^ 2)
        = c - e + 1 / 2 * B - B / (2 * N) := by field_simp; ring
    have eu : (N : ℝ) / N * (c + e) + B * ((N : ℝ) * ((N : ℝ) + 1)) / (2 * (N : ℝ) ^ 2)
        = c + e + 1 / 2 * B + B / (2 * N) := by field_simp; ring
    rw [el] at l
    rw [eu] at u
    have hB1 : B / (2 * N) ≤ |B| / (2 * N) := div_le_div_of_nonneg_right (le_abs_self B) (by positivity)
    have hB2 : -B / (2 * N) ≤ |B| / (2 * N) := div_le_div_of_nonneg_right (neg_le_abs B) (by positivity)
    rw [neg_div] at hB2
    rw [abs_le]
    constructor <;> linarith
  -- let N → ∞
  have he' : e = κ * ‖h‖ ^ 2 := he
  rw [← he']
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨N, hN'⟩ := exists_nat_gt (|B| / ε)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (abs_nonneg B) hε.le) hN'
  have := hN N (by exact_mod_cast hNpos)
  have hsmall : |B| / (2 * N) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN'
    nlinarith [abs_nonneg B]
  linarith
