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
import Mathlib.Analysis.Convex.Cone.Extension
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem convex_exists_subgradient {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ConvexOn ℝ Set.univ F) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ q : EuclideanSpace ℝ (Fin n), ∀ y, F x + inner ℝ q (y - x) ≤ F y := by
  have conv : ∀ u v : EuclideanSpace ℝ (Fin n), ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      F (a • u + b • v) ≤ a * F u + b * F v := fun u v a b ha hb hab => by
    simpa [smul_eq_mul] using hF.2 (Set.mem_univ u) (Set.mem_univ v) ha hb hab
  -- difference quotient
  let q : EuclideanSpace ℝ (Fin n) → ℝ → ℝ := fun h t => (F (x + t • h) - F x) / t
  have mono : ∀ h s t, 0 < s → s ≤ t → q h s ≤ q h t := by
    intro h s t hs hst
    have ht : 0 < t := lt_of_lt_of_le hs hst
    set r := s / t with hr
    have hr0 : 0 ≤ r := div_nonneg hs.le ht.le
    have hr1 : r ≤ 1 := (div_le_one ht).mpr hst
    have htr : t * r = s := by rw [hr]; field_simp
    have e : x + s • h = (1 - r) • x + r • (x + t • h) := by
      rw [smul_add, smul_smul, ← htr, mul_comm t r, ← add_assoc, ← add_smul]
      simp
    have key := conv x (x + t • h) (1 - r) r (by linarith) hr0 (by ring)
    rw [← e] at key
    have key2 : t * F (x + s • h) ≤ (t - s) * F x + s * F (x + t • h) := by
      have := mul_le_mul_of_nonneg_left key ht.le
      calc t * F (x + s • h) ≤ t * ((1 - r) * F x + r * F (x + t • h)) := this
        _ = (t - t * r) * F x + (t * r) * F (x + t • h) := by ring
        _ = _ := by rw [htr]
    simp only [q]
    rw [div_le_div_iff₀ hs ht]
    nlinarith
  have lower : ∀ h t, 0 < t → F x - F (x - h) ≤ q h t := by
    intro h t ht
    have h1 : (1 + t) ≠ 0 := by linarith
    have e : x = (t / (1 + t)) • (x - h) + (1 / (1 + t)) • (x + t • h) := by
      ext i
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp
      ring
    have key := conv (x - h) (x + t • h) (t / (1 + t)) (1 / (1 + t))
      (div_nonneg ht.le (by linarith)) (div_nonneg zero_le_one (by linarith))
      (by field_simp; ring)
    rw [← e] at key
    have key2 : (1 + t) * F x ≤ t * F (x - h) + F (x + t • h) := by
      have := mul_le_mul_of_nonneg_left key (by linarith : (0:ℝ) ≤ 1 + t)
      calc (1 + t) * F x ≤ (1 + t) * (t / (1 + t) * F (x - h) + 1 / (1 + t) * F (x + t • h)) := this
        _ = _ := by field_simp
    simp only [q]
    rw [le_div_iff₀ ht]
    nlinarith
  have : Nonempty (Ioi (0:ℝ)) := ⟨⟨1, by norm_num⟩⟩
  let N : EuclideanSpace ℝ (Fin n) → ℝ := fun h => ⨅ t : Ioi (0:ℝ), q h t
  have bdd : ∀ h, BddBelow (Set.range fun t : Ioi (0:ℝ) => q h t) := fun h =>
    ⟨F x - F (x - h), by rintro _ ⟨t, rfl⟩; exact lower h t t.2⟩
  have N_le : ∀ h t, 0 < t → N h ≤ q h t := fun h t ht => ciInf_le (bdd h) ⟨t, ht⟩
  have le_N : ∀ h c, (∀ t, 0 < t → c ≤ q h t) → c ≤ N h := fun h c hc =>
    le_ciInf fun t => hc t t.2
  have qsmul : ∀ h c t, 0 < c → 0 < t → q (c • h) t = c * q h (t * c) := by
    intro h c t hc ht
    simp only [q, smul_smul]
    field_simp
  have N_hom : ∀ c : ℝ, 0 < c → ∀ h, N (c • h) = c * N h := by
    intro c hc h
    apply le_antisymm
    · have : N (c • h) / c ≤ N h := le_N h _ fun t ht => by
        rw [div_le_iff₀ hc]
        have := N_le (c • h) (t / c) (div_pos ht hc)
        rw [qsmul h c _ hc (div_pos ht hc), div_mul_cancel₀ t hc.ne'] at this
        linarith
      rw [div_le_iff₀ hc] at this
      linarith
    · refine le_N _ _ fun t ht => ?_
      rw [qsmul h c t hc ht]
      exact mul_le_mul_of_nonneg_left (N_le h _ (mul_pos ht hc)) hc.le
  have qadd : ∀ h k r, 0 < r → q (h + k) r ≤ q h (2 * r) + q k (2 * r) := by
    intro h k r hr
    have e : x + r • (h + k) = (1 / 2 : ℝ) • (x + (2 * r) • h) + (1 / 2 : ℝ) • (x + (2 * r) • k) := by
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    have key := conv (x + (2 * r) • h) (x + (2 * r) • k) (1 / 2) (1 / 2) (by norm_num) (by norm_num)
      (by norm_num)
    rw [← e] at key
    simp only [q]
    rw [← add_div, div_le_div_iff₀ hr (by linarith)]
    nlinarith
  have N_add : ∀ h k, N (h + k) ≤ N h + N k := by
    intro h k
    have hst : ∀ s t, 0 < s → 0 < t → N (h + k) ≤ q h s + q k t := by
      intro s t hs ht
      set r := min s t / 2 with hr
      have hr0 : 0 < r := by rw [hr]; exact half_pos (lt_min hs ht)
      have h2s : 2 * r ≤ s := by rw [hr]; linarith [min_le_left s t]
      have h2t : 2 * r ≤ t := by rw [hr]; linarith [min_le_right s t]
      calc N (h + k) ≤ q (h + k) r := N_le _ r hr0
        _ ≤ q h (2 * r) + q k (2 * r) := qadd h k r hr0
        _ ≤ q h s + q k t := add_le_add (mono h _ _ (by linarith) h2s) (mono k _ _ (by linarith) h2t)
    have : N (h + k) - N h ≤ N k := le_N k _ fun t ht => by
      have : N (h + k) - q k t ≤ N h := le_N h _ fun s hs => by linarith [hst s t hs ht]
      linarith
    linarith
  have N0 : N 0 = 0 := by
    have : ∀ t, q 0 t = 0 := fun t => by simp [q]
    simp only [N, this, ciInf_const]
  let f0 : EuclideanSpace ℝ (Fin n) →ₗ.[ℝ] ℝ := ⟨⊥, 0⟩
  obtain ⟨g, -, hg⟩ := exists_extension_of_le_sublinear f0 N N_hom N_add (by
    rintro ⟨v, hv⟩
    rw [Submodule.mem_bot] at hv
    subst hv
    simp [f0, N0])
  refine ⟨(InnerProductSpace.toDual ℝ _).symm (LinearMap.toContinuousLinearMap g), fun y => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
  have h1 := (hg (y - x)).trans (N_le (y - x) 1 one_pos)
  simp only [q, one_smul, div_one, add_sub_cancel] at h1
  linarith
