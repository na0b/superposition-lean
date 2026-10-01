import Superposition.EuclidFst
import Superposition.EuclidSnd
import Superposition.SupConvolution
import Superposition.supConvolution_properties
import Superposition.euclidSplit_norm_sq
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
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

theorem disjoint_supConvolution_concentration {n m : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin m) → ℝ)
    (Qf : EuclideanSpace ℝ (Fin (n + m)) → ℝ) (z₀ : EuclideanSpace ℝ (Fin (n + m)))
    (r : ℝ) (hr : 0 < r)
    (huK : UpperSemicontinuousOn u (closedBall (EuclidFst z₀) r))
    (hvK : UpperSemicontinuousOn v (closedBall (EuclidSnd (n := n) z₀) r))
    (hQc : Continuous Qf)
    (hstrict : ∀ z ∈ closedBall z₀ r, z ≠ z₀ →
      u (EuclidFst z) + v (EuclidSnd (n := n) z) - Qf z
        < u (EuclidFst z₀) + v (EuclidSnd (n := n) z₀) - Qf z₀) :
    ∀ ρ > 0, ∃ β > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → ∀ z ∈ closedBall z₀ r, ρ ≤ ‖z - z₀‖ →
      SupConvolution u (closedBall (EuclidFst z₀) r) ε (EuclidFst z)
        + SupConvolution v (closedBall (EuclidSnd (n := n) z₀) r) ε (EuclidSnd (n := n) z) - Qf z
        ≤ u (EuclidFst z₀) + v (EuclidSnd (n := n) z₀) - Qf z₀ - β := by
  -- block map facts
  have fst_sub : ∀ a b : EuclideanSpace ℝ (Fin (n + m)),
      EuclidFst (a - b) = EuclidFst a - EuclidFst b := by
    intro a b; ext i; simp [EuclidFst]
  have snd_sub : ∀ a b : EuclideanSpace ℝ (Fin (n + m)),
      EuclidSnd (n := n) (a - b) = EuclidSnd (n := n) a - EuclidSnd (n := n) b := by
    intro a b; ext i; simp [EuclidSnd]
  have fst_le : ∀ h : EuclideanSpace ℝ (Fin (n + m)), ‖EuclidFst h‖ ≤ ‖h‖ := by
    intro h
    have := euclidSplit_norm_sq h
    have h2 := sq_nonneg ‖EuclidSnd (n := n) h‖
    nlinarith [norm_nonneg h, norm_nonneg (EuclidFst h)]
  have snd_le : ∀ h : EuclideanSpace ℝ (Fin (n + m)), ‖EuclidSnd (n := n) h‖ ≤ ‖h‖ := by
    intro h
    have := euclidSplit_norm_sq h
    have h2 := sq_nonneg ‖EuclidFst h‖
    nlinarith [norm_nonneg h, norm_nonneg (EuclidSnd (n := n) h)]
  have fst_lip : LipschitzWith 1 (fun z : EuclideanSpace ℝ (Fin (n + m)) => EuclidFst z) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm, ← fst_sub, NNReal.coe_one, one_mul]; exact fst_le _
  have snd_lip : LipschitzWith 1
      (fun z : EuclideanSpace ℝ (Fin (n + m)) => EuclidSnd (n := n) z) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm, ← snd_sub, NNReal.coe_one, one_mul]; exact snd_le _
  have concat : ∀ (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)),
      ∃ ζ : EuclideanSpace ℝ (Fin (n + m)), EuclidFst ζ = x ∧ EuclidSnd (n := n) ζ = y := by
    intro x y
    refine ⟨WithLp.toLp 2 (Fin.append (x : Fin n → ℝ) (y : Fin m → ℝ)), ?_, ?_⟩
    · ext i; simp [EuclidFst]
    · ext j; simp [EuclidSnd]
  set K1 := closedBall (EuclidFst z₀) r with hK1
  set K2 := closedBall (EuclidSnd (n := n) z₀) r with hK2
  set B := closedBall z₀ r with hB
  have hK1c : IsCompact K1 := isCompact_closedBall _ r
  have hK2c : IsCompact K2 := isCompact_closedBall _ r
  have hBc : IsCompact B := isCompact_closedBall _ r
  have hK1ne : K1.Nonempty := ⟨_, mem_closedBall_self hr.le⟩
  have hK2ne : K2.Nonempty := ⟨_, mem_closedBall_self hr.le⟩
  have hmap1 : MapsTo (fun z => EuclidFst z) B K1 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz ⊢
    rw [← fst_sub]; exact (fst_le _).trans hz
  have hmap2 : MapsTo (fun z => EuclidSnd (n := n) z) B K2 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz ⊢
    rw [← snd_sub]; exact (snd_le _).trans hz
  set m0 := u (EuclidFst z₀) + v (EuclidSnd (n := n) z₀) - Qf z₀ with hm0
  obtain ⟨zu, -, hzu⟩ := huK.exists_isMaxOn hK1ne hK1c
  obtain ⟨zv, -, hzv⟩ := hvK.exists_isMaxOn hK2ne hK2c
  obtain ⟨MQ, hMQ⟩ := hBc.exists_bound_of_continuousOn hQc.continuousOn
  have SPu := fun ε (hε : 0 < ε) => supConvolution_properties u K1 hK1c hK1ne huK ε hε
  have SPv := fun ε (hε : 0 < ε) => supConvolution_properties v K2 hK2c hK2ne hvK ε hε
  -- USC of the composed functions on B
  have huB : UpperSemicontinuousOn (fun z => u (EuclidFst z)) B := by
    intro z hz y hy
    exact (fst_lip.continuous.continuousWithinAt.tendsto_nhdsWithin hmap1).eventually
      (huK _ (hmap1 hz) y hy)
  have hvB : UpperSemicontinuousOn (fun z => v (EuclidSnd (n := n) z)) B := by
    intro z hz y hy
    exact (snd_lip.continuous.continuousWithinAt.tendsto_nhdsWithin hmap2).eventually
      (hvK _ (hmap2 hz) y hy)
  intro ρ hρ
  set Aρ := B ∩ {y | ρ ≤ ‖y - z₀‖} with hAρ
  have hAc : IsCompact Aρ := hBc.inter_right
    (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
  rcases Aρ.eq_empty_or_nonempty with hAe | hAne
  · refine ⟨1, one_pos, 1, one_pos, fun ε _ _ y hy hyρ => ?_⟩
    exfalso
    have : y ∈ Aρ := ⟨hy, hyρ⟩
    rw [hAe] at this; exact this
  have hwQ : UpperSemicontinuousOn
      (fun y => u (EuclidFst y) + v (EuclidSnd (n := n) y) - Qf y) Aρ := by
    have := (huB.add hvB).add (hQc.neg.upperSemicontinuous.upperSemicontinuousOn B)
    simpa [sub_eq_add_neg] using this.mono inter_subset_left
  obtain ⟨yρ, hyρA, hyρmax⟩ := hwQ.exists_isMaxOn hAne hAc
  set mρ := u (EuclidFst yρ) + v (EuclidSnd (n := n) yρ) - Qf yρ with hmρ
  have hmρlt : mρ < m0 := by
    refine hstrict yρ hyρA.1 ?_
    intro h
    have := hyρA.2
    simp only [mem_ofPred_eq, h, sub_self, norm_zero] at this
    linarith
  set β := (m0 - mρ) / 2 with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hAmax : ∀ y ∈ Aρ, u (EuclidFst y) + v (EuclidSnd (n := n) y) - Qf y ≤ mρ :=
    fun y hy => hyρmax hy
  -- local control around each point of Aρ
  have hloc : ∀ ys ∈ Aρ, ∃ η > 0,
      (∀ x ∈ K1, dist x (EuclidFst ys) < η → u x < u (EuclidFst ys) + β / 3) ∧
      (∀ x ∈ K2, dist x (EuclidSnd (n := n) ys) < η → v x < v (EuclidSnd (n := n) ys) + β / 3) ∧
      (∀ z, dist z ys < η → Qf ys - β / 3 < Qf z) := by
    intro ys hys
    have h1 := huK _ (hmap1 hys.1) (u (EuclidFst ys) + β / 3) (by linarith)
    have h2 := hvK _ (hmap2 hys.1) (v (EuclidSnd (n := n) ys) + β / 3) (by linarith)
    obtain ⟨η1, hη1, h1'⟩ := (Metric.nhdsWithin_basis_ball.eventually_iff).mp h1
    obtain ⟨η2, hη2, h2'⟩ := (Metric.nhdsWithin_basis_ball.eventually_iff).mp h2
    have h3 : ∀ᶠ z in 𝓝 ys, Qf ys - β / 3 < Qf z :=
      hQc.continuousAt.eventually (lt_mem_nhds (by linarith))
    obtain ⟨η3, hη3, h3'⟩ := Metric.eventually_nhds_iff.mp h3
    refine ⟨min η1 (min η2 η3), lt_min hη1 (lt_min hη2 hη3), ?_, ?_, ?_⟩
    · intro z hz hd
      exact h1' ⟨lt_of_lt_of_le hd (min_le_left _ _), hz⟩
    · intro z hz hd
      exact h2' ⟨lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_left _ _)), hz⟩
    · intro z hd
      exact h3' (lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_right _ _)))
  choose! η hηpos hηu hηv hηQ using hloc
  obtain ⟨lam, hlam, hleb⟩ := lebesgue_number_lemma_of_metric
    (c := fun i : Aρ => ball (i : EuclideanSpace ℝ (Fin (n + m))) (η i))
    hAc (fun i => isOpen_ball)
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (hηpos y hy)⟩)
  set C0 := u zu + v zv + MQ - m0 + β with hC0
  refine ⟨β, hβ0, lam ^ 2 / (2 * (|C0| + 1)), by positivity, fun ε hε hεlt y hy hyρ => ?_⟩
  have hyA : y ∈ Aρ := ⟨hy, hyρ⟩
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨yh, hyhK, hyh⟩ := (SPu ε hε).2.1 (EuclidFst y)
  obtain ⟨yh', hyh'K, hyh'⟩ := (SPv ε hε).2.1 (EuclidSnd (n := n) y)
  rw [hyh, hyh'] at hcon
  have hQy := hMQ y hy
  rw [Real.norm_eq_abs] at hQy
  have hQy' := neg_abs_le (Qf y)
  have hMu := hzu hyhK
  have hMv := hzv hyh'K
  simp only [mem_ofPred_eq] at hMu hMv
  have hsq : ‖EuclidFst y - yh‖ ^ 2 / (2 * ε) + ‖EuclidSnd (n := n) y - yh'‖ ^ 2 / (2 * ε)
      < |C0| := by
    have := le_abs_self C0
    rw [hC0] at this ⊢; linarith
  obtain ⟨ζ, hζ1, hζ2⟩ := concat yh yh'
  have hζ : ‖ζ - y‖ ^ 2 < lam ^ 2 := by
    rw [euclidSplit_norm_sq, fst_sub, snd_sub, hζ1, hζ2, norm_sub_rev yh, norm_sub_rev yh',
      ← add_div] at *
    rw [div_lt_iff₀ (by positivity)] at hsq
    have h2 : ε * (2 * (|C0| + 1)) < lam ^ 2 := (lt_div_iff₀ (by positivity)).mp hεlt
    nlinarith [abs_nonneg C0]
  have hdζ : dist ζ y < lam := by
    rw [dist_eq_norm]; exact lt_of_pow_lt_pow_left₀ 2 hlam.le hζ
  obtain ⟨i, hi⟩ := hleb y hyA
  have hiA : (i : EuclideanSpace ℝ (Fin (n + m))) ∈ Aρ := i.2
  have hζi := hi hdζ
  have hyi := hi (mem_ball_self hlam)
  rw [mem_ball, dist_eq_norm] at hζi
  have d1 : dist yh (EuclidFst (i : EuclideanSpace ℝ (Fin (n + m)))) < η i := by
    rw [dist_eq_norm, ← hζ1, ← fst_sub]; exact lt_of_le_of_lt (fst_le _) hζi
  have d2 : dist yh' (EuclidSnd (n := n) (i : EuclideanSpace ℝ (Fin (n + m)))) < η i := by
    rw [dist_eq_norm, ← hζ2, ← snd_sub]; exact lt_of_le_of_lt (snd_le _) hζi
  have b1 := hηu i hiA yh hyhK d1
  have b2 := hηv i hiA yh' hyh'K d2
  have b3 := hηQ i hiA y hyi
  have b4 := hAmax i hiA
  have h0 : 0 ≤ ‖EuclidFst y - yh‖ ^ 2 / (2 * ε) := by positivity
  have h0' : 0 ≤ ‖EuclidSnd (n := n) y - yh'‖ ^ 2 / (2 * ε) := by positivity
  rw [hβ] at hcon b1 b2 b3
  linarith
