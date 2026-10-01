import Superposition.convex_locally_lipschitz
import Superposition.convex_exists_subgradient
import Superposition.lipschitz_image_null
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
import Mathlib.Analysis.Convex.Continuous
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem jensen_positive_measure {n : ℕ} (W : EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hconv : ConvexOn ℝ Set.univ (fun x => W x + C / 2 * ‖x‖ ^ 2))
    (x₀ xs : EuclideanSpace ℝ (Fin n)) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hxs : xs ∈ closedBall x₀ r)
    (hsphere : ∀ y, ‖y - x₀‖ = r → W y + 2 * δ * r < W xs) :
    0 < volume {x | x ∈ ball x₀ r ∧ ∃ p : EuclideanSpace ℝ (Fin n), ‖p‖ ≤ δ ∧
      ∀ y ∈ closedBall x₀ r, W y + inner ℝ p y ≤ W x + inner ℝ p x} := by
  set K := {x | x ∈ ball x₀ r ∧ ∃ p : EuclideanSpace ℝ (Fin n), ‖p‖ ≤ δ ∧
      ∀ y ∈ closedBall x₀ r, W y + inner ℝ p y ≤ W x + inner ℝ p x} with hKdef
  -- Step 1: continuity
  have hΦc : Continuous (fun x => W x + C / 2 * ‖x‖ ^ 2) := hconv.locallyLipschitz.continuous
  have hWc : Continuous W := by
    have := hΦc.sub ((continuous_const.mul (continuous_norm.pow 2)) :
      Continuous (fun x : EuclideanSpace ℝ (Fin n) => C / 2 * ‖x‖ ^ 2))
    convert this using 1
    funext x
    simp
  -- subgradients of Φ and the map g
  have hsub := fun x => convex_exists_subgradient (fun x => W x + C / 2 * ‖x‖ ^ 2) hconv x
  choose Q hQ using hsub
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => C • x - Q x
  -- Step 3: uniqueness of the witness
  have huniq : ∀ x ∈ ball x₀ r, ∀ p : EuclideanSpace ℝ (Fin n),
      (∀ y ∈ closedBall x₀ r, W y + inner ℝ p y ≤ W x + inner ℝ p x) → p = g x := by
    intro x hx p hp
    set v := Q x - (C • x - p) with hv
    have hxr : ‖x - x₀‖ < r := by rw [mem_ball, dist_eq_norm] at hx; exact hx
    set t : ℝ := min (1 / (2 * (C + 1))) ((r - ‖x - x₀‖) / (‖v‖ + 1)) with ht
    have ht0 : 0 < t := lt_min (by positivity) (div_pos (by linarith) (by positivity))
    have ht1 : t ≤ 1 / (2 * (C + 1)) := min_le_left _ _
    have ht2 : t ≤ (r - ‖x - x₀‖) / (‖v‖ + 1) := min_le_right _ _
    have hyB : x + t • v ∈ closedBall x₀ r := by
      rw [mem_closedBall, dist_eq_norm]
      have e : x + t • v - x₀ = (x - x₀) + t • v := by abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have h1 : t * (‖v‖ + 1) ≤ r - ‖x - x₀‖ := (le_div_iff₀ (by positivity)).mp ht2
      nlinarith [norm_nonneg v]
    have hup := hp _ hyB
    have hlow := hQ x (x + t • v)
    simp only [add_sub_cancel_left] at hlow
    have hn : ‖x + t • v‖ ^ 2 = ‖x‖ ^ 2 + 2 * (t * inner ℝ x v) + t ^ 2 * ‖v‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [hn, real_inner_smul_right] at hlow
    rw [inner_add_right, real_inner_smul_right] at hup
    have hvv : ‖v‖ ^ 2 = inner ℝ (Q x) v - C * inner ℝ x v + inner ℝ p v := by
      rw [← real_inner_self_eq_norm_sq]
      conv_lhs => rw [hv]
      rw [inner_sub_left, inner_sub_left, real_inner_smul_left]
      ring
    have hCt : C * t ≤ 1 / 2 := by
      have : t * (2 * (C + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp ht1
      nlinarith
    have htv := congrArg (fun z => t * z) hvv
    have key : t * (‖v‖ ^ 2 - C / 2 * t * ‖v‖ ^ 2) ≤ 0 := by
      have : t * (‖v‖ ^ 2 - C / 2 * t * ‖v‖ ^ 2) = t * ‖v‖ ^ 2 - C / 2 * (t ^ 2 * ‖v‖ ^ 2) := by ring
      rw [this]
      nlinarith
    have k2 : ‖v‖ ^ 2 - C / 2 * t * ‖v‖ ^ 2 ≤ 0 := by
      by_contra hk
      push Not at hk
      linarith [mul_pos ht0 hk]
    have k3 := mul_le_mul_of_nonneg_right hCt (sq_nonneg ‖v‖)
    have hv0 : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
    have : v = 0 := by
      have := pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp (le_antisymm hv0 (sq_nonneg _))
      exact norm_eq_zero.mp this
    rw [hv] at this
    simp only [g]
    rw [sub_eq_zero] at this
    rw [this]; abel
  -- Step 2: every small p is attained
  have hattain : ∀ p : EuclideanSpace ℝ (Fin n), ‖p‖ ≤ δ → ∃ x ∈ K, g x = p := by
    intro p hp
    have hcont : ContinuousOn (fun x => W x + inner ℝ p x) (closedBall x₀ r) :=
      (hWc.add (continuous_const.inner continuous_id)).continuousOn
    obtain ⟨xp, hxpB, hxpmax⟩ := (isCompact_closedBall x₀ r).exists_isMaxOn
      ⟨x₀, mem_closedBall_self hr.le⟩ hcont
    have hmax : ∀ y ∈ closedBall x₀ r, W y + inner ℝ p y ≤ W xp + inner ℝ p xp :=
      fun y hy => hxpmax hy
    have hxpin : xp ∈ ball x₀ r := by
      rw [mem_ball, dist_eq_norm]
      rw [mem_closedBall, dist_eq_norm] at hxpB
      rcases hxpB.lt_or_eq with h | h
      · exact h
      · exfalso
        have h1 := hsphere xp h
        have h2 := hmax xs hxs
        rw [mem_closedBall, dist_eq_norm] at hxs
        have c1 : |inner ℝ p (xp - x₀)| ≤ δ * r := by
          refine (abs_real_inner_le_norm _ _).trans ?_
          rw [h]; exact mul_le_mul_of_nonneg_right hp hr.le
        have c2 : |inner ℝ p (xs - x₀)| ≤ δ * r :=
          (abs_real_inner_le_norm _ _).trans (mul_le_mul hp hxs (norm_nonneg _) hδ.le)
        rw [inner_sub_right] at c1 c2
        have := (abs_le.mp c1).2
        have := (abs_le.mp c2).1
        linarith
    refine ⟨xp, ⟨hxpin, p, hp, hmax⟩, (huniq xp hxpin p hmax).symm⟩
  -- (U): upper quadratic bound at points of K
  have hU : ∀ x ∈ K, ∀ y ∈ closedBall x₀ r,
      W y + C / 2 * ‖y‖ ^ 2 ≤ W x + C / 2 * ‖x‖ ^ 2 + inner ℝ (Q x) (y - x)
        + C / 2 * ‖y - x‖ ^ 2 := by
    intro x hx y hy
    obtain ⟨hxb, p, -, hwit⟩ := hx
    have hpg := huniq x hxb p hwit
    have h1 := hwit y hy
    rw [hpg] at h1
    have e1 : inner ℝ (g x) y - inner ℝ (g x) x = C * inner ℝ x (y - x) - inner ℝ (Q x) (y - x) := by
      rw [← inner_sub_right]
      simp only [g]
      rw [inner_sub_left, real_inner_smul_left]
    have e2 : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ 2 := by
      have : y = x + (y - x) := by abel
      conv_lhs => rw [this]
      rw [norm_add_sq_real]
    rw [e2]
    nlinarith
  -- Step 4: local Lipschitz bound for g on K
  have hlip4 : ∀ θ > 0, ∀ x1 ∈ K, ∀ x2 ∈ K, ‖x1 - x₀‖ ≤ r - θ → ‖x2 - x₀‖ ≤ r - θ →
      ‖x1 - x2‖ ≤ θ / 2 → ‖g x1 - g x2‖ ≤ 3 * C * ‖x1 - x2‖ := by
    intro θ hθ x1 hx1 x2 hx2 h1 h2 hd
    set d := ‖x1 - x2‖ with hddef
    set Δ := Q x2 - Q x1 with hΔ
    have hg : g x1 - g x2 = C • (x1 - x2) + Δ := by
      simp only [g, hΔ, smul_sub]; abel
    have hΔb : ‖Δ‖ ≤ 2 * C * d := by
      rcases eq_or_ne Δ 0 with h0 | h0
      · rw [h0, norm_zero]; positivity
      have hΔpos : 0 < ‖Δ‖ := norm_pos_iff.mpr h0
      have hdpos : 0 < d := by
        rcases (norm_nonneg (x1 - x2)).eq_or_lt with h | h
        · exfalso
          have : x1 = x2 := sub_eq_zero.mp (norm_eq_zero.mp h.symm)
          exact h0 (by rw [hΔ, this, sub_self])
        · exact h
      set t := 2 * d with htdef
      set u := (t / ‖Δ‖) • Δ with hu
      have hun : ‖u‖ = t := by
        rw [hu, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        field_simp
      have hyB : x1 + u ∈ closedBall x₀ r := by
        rw [mem_closedBall, dist_eq_norm]
        have : x1 + u - x₀ = (x1 - x₀) + u := by abel
        rw [this]
        refine (norm_add_le _ _).trans ?_
        rw [hun]; linarith
      have L2 := hQ x2 (x1 + u)
      have U1 := hU x1 hx1 (x1 + u) hyB
      have L1 := hQ x1 x2
      have e1 : x1 + u - x2 = u + (x1 - x2) := by abel
      have e2 : x1 + u - x1 = u := by abel
      have e3 : x2 - x1 = -(x1 - x2) := by abel
      rw [e1, inner_add_right] at L2
      rw [e2, hun] at U1
      rw [e3, inner_neg_right] at L1
      have hΔu : inner ℝ (Q x2) u - inner ℝ (Q x1) u = t * ‖Δ‖ := by
        rw [← inner_sub_left, ← hΔ, hu, real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      have hΔx : -(‖Δ‖ * d) ≤ inner ℝ (Q x2) (x1 - x2) - inner ℝ (Q x1) (x1 - x2) := by
        rw [← inner_sub_left, ← hΔ]
        exact neg_le_of_abs_le (abs_real_inner_le_norm _ _)
      have key : d * ‖Δ‖ ≤ d * (2 * C * d) := by
        rw [htdef] at hΔu U1
        nlinarith
      exact le_of_mul_le_mul_left key hdpos
    rw [hg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
    linarith
  -- Step 5: conclusion
  rw [pos_iff_ne_zero]
  intro hK0
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq (EuclideanSpace ℝ (Fin n))
  let T : ℕ → ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun m j =>
    K ∩ closedBall x₀ (r - 1 / ((m : ℝ) + 1)) ∩ closedBall (c j) (1 / (4 * ((m : ℝ) + 1)))
  have hTK : ∀ m j, T m j ⊆ K := fun m j x hx => hx.1.1
  have hTlip : ∀ m j, LipschitzOnWith (⟨3 * C, by positivity⟩ : NNReal) g (T m j) := by
    intro m j
    refine LipschitzOnWith.of_dist_le_mul fun x1 hx1 x2 hx2 => ?_
    rw [dist_eq_norm, dist_eq_norm]
    change ‖g x1 - g x2‖ ≤ 3 * C * ‖x1 - x2‖
    have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    refine hlip4 (1 / ((m : ℝ) + 1)) hm x1 hx1.1.1 x2 hx2.1.1 ?_ ?_ ?_
    · have := hx1.1.2; rwa [mem_closedBall, dist_eq_norm] at this
    · have := hx2.1.2; rwa [mem_closedBall, dist_eq_norm] at this
    · have a1 := hx1.2; have a2 := hx2.2
      rw [mem_closedBall, dist_eq_norm] at a1 a2
      have : x1 - x2 = (x1 - c j) - (x2 - c j) := by abel
      rw [this]
      refine (norm_sub_le _ _).trans ?_
      have e : 1 / ((m : ℝ) + 1) / 2 = 1 / (4 * ((m : ℝ) + 1)) + 1 / (4 * ((m : ℝ) + 1)) := by
        field_simp; ring
      rw [e]; linarith
  have hcover : K ⊆ ⋃ m, ⋃ j, T m j := by
    intro x hx
    have hxr : dist x x₀ < r := hx.1
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hxr)
    have hpos : (0 : ℝ) < 1 / (4 * ((m : ℝ) + 1)) := by positivity
    obtain ⟨j, hj⟩ := hc.exists_dist_lt x hpos
    refine mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨j, ⟨hx, ?_⟩, ?_⟩⟩
    · rw [mem_closedBall]; linarith
    · rw [mem_closedBall]; exact hj.le
  have hgK : volume (g '' K) = 0 := by
    have hsub : g '' K ⊆ ⋃ m, ⋃ j, g '' T m j := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨m, hm⟩ := mem_iUnion.mp (hcover hx)
      obtain ⟨j, hj⟩ := mem_iUnion.mp hm
      exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨j, x, hj, rfl⟩⟩
    refine measure_mono_null hsub (measure_iUnion_null fun m => measure_iUnion_null fun j => ?_)
    exact lipschitz_image_null g (T m j) _ (hTlip m j) (measure_mono_null (hTK m j) hK0)
  have hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) δ ⊆ g '' K := by
    intro p hp
    rw [mem_closedBall, dist_zero_right] at hp
    obtain ⟨x, hxK, hgx⟩ := hattain p hp
    exact ⟨x, hxK, hgx⟩
  have := measure_mono_null hball hgK
  exact (measure_closedBall_pos volume (0 : EuclideanSpace ℝ (Fin n)) hδ).ne' this
