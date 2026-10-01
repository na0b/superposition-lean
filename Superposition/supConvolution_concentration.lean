import Superposition.supConvolution_properties
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

theorem supConvolution_concentration {n : ℕ} (u v Qf : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (huK : UpperSemicontinuousOn u (closedBall x₀ r))
    (hvK : UpperSemicontinuousOn v (closedBall x₀ r)) (hQc : Continuous Qf)
    (hstrict : ∀ y ∈ closedBall x₀ r, y ≠ x₀ → u y + v y - Qf y < u x₀ + v x₀ - Qf x₀) :
    ∀ ρ > 0, ∃ β > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → ∀ y ∈ closedBall x₀ r, ρ ≤ ‖y - x₀‖ →
      SupConvolution u (closedBall x₀ r) ε y + SupConvolution v (closedBall x₀ r) ε y - Qf y
        ≤ u x₀ + v x₀ - Qf x₀ - β := by
  set K := closedBall x₀ r with hKdef
  have hKc : IsCompact K := isCompact_closedBall x₀ r
  have hx₀K : x₀ ∈ K := mem_closedBall_self hr.le
  have hKne : K.Nonempty := ⟨x₀, hx₀K⟩
  set m0 := u x₀ + v x₀ - Qf x₀ with hm0
  obtain ⟨zu, -, hzu⟩ := huK.exists_isMaxOn hKne hKc
  obtain ⟨zv, -, hzv⟩ := hvK.exists_isMaxOn hKne hKc
  set Mu := u zu
  set Mv := v zv
  have hMu : ∀ z ∈ K, u z ≤ Mu := fun z hz => hzu hz
  have hMv : ∀ z ∈ K, v z ≤ Mv := fun z hz => hzv hz
  obtain ⟨MQ, hMQ⟩ := hKc.exists_bound_of_continuousOn hQc.continuousOn
  have SPu := fun ε (hε : 0 < ε) => supConvolution_properties u K hKc hKne huK ε hε
  have SPv := fun ε (hε : 0 < ε) => supConvolution_properties v K hKc hKne hvK ε hε
  intro ρ hρ
  set Aρ := K ∩ {y | ρ ≤ ‖y - x₀‖} with hAρ
  have hAc : IsCompact Aρ := hKc.inter_right
    (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
  rcases Aρ.eq_empty_or_nonempty with hAe | hAne
  · refine ⟨1, one_pos, 1, one_pos, fun ε _ _ y hy hyρ => ?_⟩
    exfalso
    have : y ∈ Aρ := ⟨hy, hyρ⟩
    rw [hAe] at this; exact this
  have hwQ : UpperSemicontinuousOn (fun y => u y + v y - Qf y) Aρ := by
    have := (huK.add hvK).add (hQc.neg.upperSemicontinuous.upperSemicontinuousOn K)
    simpa [sub_eq_add_neg] using this.mono inter_subset_left
  obtain ⟨yρ, hyρA, hyρmax⟩ := hwQ.exists_isMaxOn hAne hAc
  set mρ := u yρ + v yρ - Qf yρ with hmρ
  have hmρlt : mρ < m0 := by
    refine hstrict yρ hyρA.1 ?_
    intro h
    have := hyρA.2
    simp only [mem_ofPred_eq, h, sub_self, norm_zero] at this
    linarith
  set β := (m0 - mρ) / 2 with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hAmax : ∀ y ∈ Aρ, u y + v y - Qf y ≤ mρ := fun y hy => hyρmax hy
  -- local control around each point of Aρ
  have hloc : ∀ ys ∈ Aρ, ∃ η > 0, (∀ z ∈ K, dist z ys < η → u z < u ys + β / 3) ∧
      (∀ z ∈ K, dist z ys < η → v z < v ys + β / 3) ∧
      (∀ z, dist z ys < η → Qf ys - β / 3 < Qf z) := by
    intro ys hys
    have h1 := huK ys hys.1 (u ys + β / 3) (by linarith)
    have h2 := hvK ys hys.1 (v ys + β / 3) (by linarith)
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
  obtain ⟨lam, hlam, hleb⟩ := lebesgue_number_lemma_of_metric (c := fun i : Aρ => ball (i : EuclideanSpace ℝ (Fin n)) (η i))
    hAc (fun i => isOpen_ball)
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (hηpos y hy)⟩)
  set C0 := Mu + Mv + MQ - m0 + β with hC0
  refine ⟨β, hβ0, lam ^ 2 / (2 * (|C0| + 1)), by positivity, fun ε hε hεlt y hy hyρ => ?_⟩
  have hyA : y ∈ Aρ := ⟨hy, hyρ⟩
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨yh, hyhK, hyh⟩ := (SPu ε hε).2.1 y
  obtain ⟨yh', hyh'K, hyh'⟩ := (SPv ε hε).2.1 y
  rw [hyh, hyh'] at hcon
  have hQy := hMQ y hy
  rw [Real.norm_eq_abs] at hQy
  have hQy' := neg_abs_le (Qf y)
  have hsq : ‖y - yh‖ ^ 2 / (2 * ε) + ‖y - yh'‖ ^ 2 / (2 * ε) < C0 := by
    have := hMu yh hyhK; have := hMv yh' hyh'K
    rw [hC0]; linarith
  have hsq1 : ‖y - yh‖ ^ 2 < lam ^ 2 := by
    have h0 : 0 ≤ ‖y - yh'‖ ^ 2 / (2 * ε) := by positivity
    have h1 : ‖y - yh‖ ^ 2 / (2 * ε) < |C0| := by
      have := le_abs_self C0; linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    have h2 : ε * (2 * (|C0| + 1)) < lam ^ 2 := (lt_div_iff₀ (by positivity)).mp hεlt
    nlinarith [abs_nonneg C0]
  have hsq2 : ‖y - yh'‖ ^ 2 < lam ^ 2 := by
    have h0 : 0 ≤ ‖y - yh‖ ^ 2 / (2 * ε) := by positivity
    have h1 : ‖y - yh'‖ ^ 2 / (2 * ε) < |C0| := by
      have := le_abs_self C0; linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    have h2 : ε * (2 * (|C0| + 1)) < lam ^ 2 := (lt_div_iff₀ (by positivity)).mp hεlt
    nlinarith [abs_nonneg C0]
  have hd1 : dist yh y < lam := by
    rw [dist_comm, dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hlam.le hsq1
  have hd2 : dist yh' y < lam := by
    rw [dist_comm, dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hlam.le hsq2
  obtain ⟨i, hi⟩ := hleb y hyA
  have hiA : (i : EuclideanSpace ℝ (Fin n)) ∈ Aρ := i.2
  have b1 := hηu i hiA yh hyhK (hi hd1)
  have b2 := hηv i hiA yh' hyh'K (hi hd2)
  have b3 := hηQ i hiA y (hi (mem_ball_self hlam))
  have b4 := hAmax i hiA
  have h0 : 0 ≤ ‖y - yh‖ ^ 2 / (2 * ε) := by positivity
  have h0' : 0 ≤ ‖y - yh'‖ ^ 2 / (2 * ε) := by positivity
  rw [hβ] at hcon b1 b2 b3
  linarith
