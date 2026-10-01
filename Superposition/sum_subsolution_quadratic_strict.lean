import Superposition.IsDegenerateElliptic
import Superposition.IsSubadditiveOperator
import Superposition.IsViscositySubsolution
import Superposition.supConvolution_properties
import Superposition.supConvolution_jet_transfer
import Superposition.alexandrov_convex
import Superposition.jensen_positive_measure
import Superposition.supConvolution_concentration
import Superposition.quadratic_upper_bound_conditions
import Superposition.quadratic_convex_part
import Superposition.expansion_sub_half_sq_norm
import Superposition.jet_twosided_to_upper
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

theorem sum_subsolution_quadratic_strict {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω)
    (L : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ → ℝ)
    (hLc : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × Matrix (Fin n) (Fin n) ℝ => L p.1 p.2)
      (Set.univ ×ˢ {X | X.IsHermitian}))
    (hLe : IsDegenerateElliptic L) (hLs : IsSubadditiveOperator L)
    (u v : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : IsViscositySubsolution Ω L f u) (hv : IsViscositySubsolution Ω L g v)
    (x₀ : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) (hball : closedBall x₀ r ⊆ Ω)
    (q₀ : ℝ) (c : EuclideanSpace ℝ (Fin n)) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.IsHermitian)
    (hmax : ∀ y ∈ closedBall x₀ r, y ≠ x₀ →
      u y + v y - (q₀ + inner ℝ c (y - x₀)
        + (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin P (y - x₀)) (y - x₀))
        < u x₀ + v x₀ - q₀) :
    L c P ≤ f x₀ + g x₀ := by
  -- Setup
  have hKc : IsCompact (closedBall x₀ r) := isCompact_closedBall x₀ r
  have hx₀K : x₀ ∈ closedBall x₀ r := mem_closedBall_self hr.le
  have hKne : (closedBall x₀ r).Nonempty := ⟨x₀, hx₀K⟩
  have huK : UpperSemicontinuousOn u (closedBall x₀ r) := hu.1.mono hball
  have hvK : UpperSemicontinuousOn v (closedBall x₀ r) := hv.1.mono hball
  have hPsym : (Matrix.toEuclideanLin P).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hP
  obtain ⟨PL, hPL⟩ : ∃ PL : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ h, PL h = Matrix.toEuclideanLin P h :=
    ⟨LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin P), fun h => rfl⟩
  obtain ⟨Qf, hQf⟩ : ∃ Qf : EuclideanSpace ℝ (Fin n) → ℝ, ∀ y, Qf y =
      q₀ + inner ℝ c (y - x₀) + (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin P (y - x₀)) (y - x₀) :=
    ⟨_, fun y => rfl⟩
  have hQc : Continuous Qf := by
    have h1 : Continuous (fun y : EuclideanSpace ℝ (Fin n) => y - x₀) :=
      continuous_id.sub continuous_const
    have : Qf = fun y => q₀ + inner ℝ c (y - x₀) + (1 / 2 : ℝ) * inner ℝ (PL (y - x₀)) (y - x₀) := by
      funext y; rw [hQf, hPL]
    rw [this]
    exact (continuous_const.add (continuous_const.inner h1)).add
      (continuous_const.mul ((PL.continuous.comp h1).inner h1))
  have hQx₀ : Qf x₀ = q₀ := by rw [hQf]; simp
  have hstrict : ∀ y ∈ closedBall x₀ r, y ≠ x₀ → u y + v y - Qf y < u x₀ + v x₀ - Qf x₀ := by
    intro y hy hne; rw [hQf, hQx₀]; exact hmax y hy hne
  obtain ⟨zu, -, hzu⟩ := huK.exists_isMaxOn hKne hKc
  obtain ⟨zv, -, hzv⟩ := hvK.exists_isMaxOn hKne hKc
  obtain ⟨MQ, hMQ⟩ := hKc.exists_bound_of_continuousOn hQc.continuousOn
  -- the σ-argument
  refine le_of_forall_pos_le_add fun σ hσ => ?_
  -- continuity choices
  have hLcont : ContinuousAt (fun ξ => L ξ P) c := by
    have h := hLc (c, P) ⟨trivial, hP⟩
    have h2 : ContinuousWithinAt (fun ξ : EuclideanSpace ℝ (Fin n) => (ξ, P)) univ c :=
      (continuous_id.prodMk continuous_const).continuousWithinAt
    exact (continuousWithinAt_univ _ _).mp
      (ContinuousWithinAt.comp (g := fun p : EuclideanSpace ℝ (Fin n) × Matrix (Fin n) (Fin n) ℝ =>
        L p.1 p.2) (f := fun ξ => (ξ, P)) h h2
        (fun ξ _ => show (ξ, P) ∈ univ ×ˢ {X : Matrix (Fin n) (Fin n) ℝ | X.IsHermitian} from
          ⟨trivial, hP⟩))
  obtain ⟨ρL, hρL, hρLP⟩ := Metric.eventually_nhds_iff.mp
    (hLcont.eventually (lt_mem_nhds (show L c P - σ / 3 < L c P by linarith)))
  have hx₀Ω : x₀ ∈ Ω := hball hx₀K
  obtain ⟨ρf, hρf, hρfP⟩ := (Metric.nhdsWithin_basis_ball.eventually_iff).mp
    ((hf x₀ hx₀Ω).eventually (gt_mem_nhds (show f x₀ < f x₀ + σ / 3 by linarith)))
  obtain ⟨ρg, hρg, hρgP⟩ := (Metric.nhdsWithin_basis_ball.eventually_iff).mp
    ((hg x₀ hx₀Ω).eventually (gt_mem_nhds (show g x₀ < g x₀ + σ / 3 by linarith)))
  obtain ⟨ρ, hρ0, hρr, hρL', hρf', hρg'⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r / 2 ∧
      ρ * (‖PL‖ + 2) ≤ ρL ∧ ρ ≤ ρf / 2 ∧ ρ ≤ ρg / 2 := by
    refine ⟨min (r / 2) (min (ρL / (‖PL‖ + 2)) (min (ρf / 2) (ρg / 2))),
      lt_min (half_pos hr) (lt_min (by positivity) (lt_min (half_pos hρf) (half_pos hρg))),
      min_le_left _ _, ?_, (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
    exact (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨β, hβ, ε₀, hε₀, hA⟩ := supConvolution_concentration u v Qf x₀ r hr huK hvK hQc hstrict ρ hρ0
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = u zu + v zv + MQ - (u x₀ + v x₀ - Qf x₀) + β := ⟨_, rfl⟩
  obtain ⟨ε, hε, hεε₀, hερ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < ε₀ ∧ ε * (4 * (|C0| + 1)) ≤ ρ ^ 2 := by
    refine ⟨min (ε₀ / 2) (ρ ^ 2 / (4 * (|C0| + 1))), lt_min (half_pos hε₀) (by positivity),
      lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε₀), ?_⟩
    exact (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  obtain ⟨δ, hδ, hδρ, hδβ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < ρ ∧ δ * r ≤ β / 4 := by
    refine ⟨min (ρ / 2) (β / (4 * r)), lt_min (half_pos hρ0) (by positivity),
      lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ0), ?_⟩
    have : min (ρ / 2) (β / (4 * r)) ≤ β / (4 * r) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  -- the function W
  obtain ⟨SUi, SUii, SUiii⟩ := supConvolution_properties u _ hKc hKne huK ε hε
  obtain ⟨SVi, SVii, SViii⟩ := supConvolution_properties v _ hKc hKne hvK ε hε
  obtain ⟨W, hWdef⟩ : ∃ W : EuclideanSpace ℝ (Fin n) → ℝ, ∀ x, W x =
      SupConvolution u (closedBall x₀ r) ε x + SupConvolution v (closedBall x₀ r) ε x - Qf x :=
    ⟨_, fun x => rfl⟩
  have hW2 : u x₀ + v x₀ - Qf x₀ ≤ W x₀ := by
    have h1 := SUi x₀ x₀ hx₀K
    have h2 := SVi x₀ x₀ hx₀K
    simp only [sub_self, norm_zero] at h1 h2
    rw [hWdef]
    have : (0 : ℝ) ^ 2 / (2 * ε) = 0 := by simp
    rw [this] at h1 h2
    linarith
  have hAW : ∀ y ∈ closedBall x₀ r, ρ ≤ ‖y - x₀‖ → W y ≤ u x₀ + v x₀ - Qf x₀ - β := by
    intro y hy hyρ; rw [hWdef]; exact hA ε hε hεε₀ y hy hyρ
  -- semiconvexity
  have hPbound : ∀ d, inner ℝ (Matrix.toEuclideanLin P d) d ≤ ‖PL‖ * ‖d‖ ^ 2 := by
    intro d
    calc inner ℝ (Matrix.toEuclideanLin P d) d ≤ ‖Matrix.toEuclideanLin P d‖ * ‖d‖ :=
          real_inner_le_norm _ _
      _ ≤ (‖PL‖ * ‖d‖) * ‖d‖ := by
          gcongr; rw [← hPL]; exact PL.le_opNorm d
      _ = ‖PL‖ * ‖d‖ ^ 2 := by ring
  have hconvW : ConvexOn ℝ univ (fun x => W x + (2 / ε + ‖PL‖) / 2 * ‖x‖ ^ 2) := by
    have := (SUiii.add SViii).add (quadratic_convex_part x₀ c q₀ ‖PL‖ P hP hPbound)
    have heq : (fun x => W x + (2 / ε + ‖PL‖) / 2 * ‖x‖ ^ 2) =
        (fun x => SupConvolution u (closedBall x₀ r) ε x + ‖x‖ ^ 2 / (2 * ε)) +
        (fun x => SupConvolution v (closedBall x₀ r) ε x + ‖x‖ ^ 2 / (2 * ε)) +
        (fun x => ‖PL‖ / 2 * ‖x‖ ^ 2 - (q₀ + inner ℝ c (x - x₀)
          + (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin P (x - x₀)) (x - x₀))) := by
      funext x
      simp only [Pi.add_apply]
      rw [hWdef, hQf]
      field_simp
      ring
    rw [heq]; exact this
  -- Jensen
  have hsphere : ∀ y, ‖y - x₀‖ = r → W y + 2 * δ * r < W x₀ := by
    intro y hy
    have hyK : y ∈ closedBall x₀ r := by rw [mem_closedBall, dist_eq_norm, hy]
    have := hAW y hyK (by rw [hy]; linarith)
    linarith
  have hJ := jensen_positive_measure W (2 / ε + ‖PL‖) (by positivity) hconvW x₀ x₀ r δ hr hδ
    hx₀K hsphere
  -- Alexandrov
  obtain ⟨y, ⟨hyball, p, hp, hpmax⟩, ⟨au, Au, hAuH, hlu⟩, ⟨bv, Bv, hBvH, hlv⟩⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hJ.ne'
      (ae_restrict_of_ae ((alexandrov_convex _ SUiii).and (alexandrov_convex _ SViii)))
  -- location of y
  have hyK : y ∈ closedBall x₀ r := ball_subset_closedBall hyball
  have hWy : u x₀ + v x₀ - Qf x₀ - β < W y := by
    have h1 := hpmax x₀ hx₀K
    have h2 : inner ℝ p y - inner ℝ p x₀ ≤ δ * r := by
      rw [← inner_sub_right]
      refine (real_inner_le_norm _ _).trans ?_
      have : ‖y - x₀‖ ≤ r := by
        have := mem_closedBall.mp hyK; rwa [dist_eq_norm] at this
      exact mul_le_mul hp this (norm_nonneg _) hδ.le
    linarith
  have hyρ : ‖y - x₀‖ < ρ := by
    by_contra hc
    rw [not_lt] at hc
    have := hAW y hyK hc
    linarith
  obtain ⟨yh, hyhK, hyh⟩ := SUii y
  obtain ⟨yh', hyh'K, hyh'⟩ := SVii y
  have hdist : ‖y - yh‖ ^ 2 / (2 * ε) + ‖y - yh'‖ ^ 2 / (2 * ε) ≤ |C0| := by
    have e := hWdef y
    rw [hyh, hyh'] at e
    have hQy := hMQ y hyK
    rw [Real.norm_eq_abs] at hQy
    have := neg_abs_le (Qf y)
    have := hzu hyhK; have := hzv hyh'K
    have := le_abs_self C0
    simp only [mem_ofPred_eq] at *
    linarith
  have hsqρ : ∀ z, ‖y - z‖ ^ 2 / (2 * ε) ≤ |C0| → ‖y - z‖ < ρ := by
    intro z hz
    rw [div_le_iff₀ (by positivity)] at hz
    have : ‖y - z‖ ^ 2 < ρ ^ 2 := by nlinarith [abs_nonneg C0]
    exact lt_of_pow_lt_pow_left₀ 2 hρ0.le this
  have hyh1 : ‖y - yh‖ < ρ := hsqρ yh (by
    have : 0 ≤ ‖y - yh'‖ ^ 2 / (2 * ε) := by positivity
    linarith)
  have hyh2 : ‖y - yh'‖ < ρ := hsqρ yh' (by
    have : 0 ≤ ‖y - yh‖ ^ 2 / (2 * ε) := by positivity
    linarith)
  have hclose : ∀ z, ‖y - z‖ < ρ → dist z x₀ < 2 * ρ := by
    intro z hz
    rw [dist_eq_norm]
    have : z - x₀ = (y - x₀) - (y - z) := by abel
    rw [this]
    calc ‖(y - x₀) - (y - z)‖ ≤ ‖y - x₀‖ + ‖y - z‖ := norm_sub_le _ _
      _ < ρ + ρ := add_lt_add hyρ hz
      _ = 2 * ρ := by ring
  have hint : ∀ z, ‖y - z‖ < ρ → z ∈ interior (closedBall x₀ r) := by
    intro z hz
    refine ball_subset_interior_closedBall ?_
    rw [mem_ball]; have := hclose z hz; linarith
  -- jets of the sup-convolutions at y
  have jetu := expansion_sub_half_sq_norm _ ε hε y au Au hlu
  have jetv := expansion_sub_half_sq_norm _ ε hε y bv Bv hlv
  obtain ⟨a, ha⟩ : ∃ a : EuclideanSpace ℝ (Fin n), a = au - (1 / ε) • y := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : EuclideanSpace ℝ (Fin n), b = bv - (1 / ε) • y := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Fin n) (Fin n) ℝ,
      A = Au - (1 / ε) • (1 : Matrix (Fin n) (Fin n) ℝ) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : Matrix (Fin n) (Fin n) ℝ,
      B = Bv - (1 / ε) • (1 : Matrix (Fin n) (Fin n) ℝ) := ⟨_, rfl⟩
  rw [← ha, ← hAdef] at jetu
  rw [← hb, ← hBdef] at jetv
  have hIH : ((1 / ε) • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
    simp [Matrix.IsHermitian]
  have hAH : A.IsHermitian := by rw [hAdef]; exact hAuH.sub hIH
  have hBH : B.IsHermitian := by rw [hBdef]; exact hBvH.sub hIH
  -- jet transfer
  have hLu : L a A ≤ f yh := supConvolution_jet_transfer Ω L hLc f u hu _ hKc hball ε hε y yh
    (hint yh hyh1) hyh a A hAH (jet_twosided_to_upper _ _ a A jetu)
  have hLv : L b B ≤ g yh' := supConvolution_jet_transfer Ω L hLc g v hv _ hKc hball ε hε y yh'
    (hint yh' hyh2) hyh' b B hBH (jet_twosided_to_upper _ _ b B jetv)
  -- first- and second-order conditions at y
  obtain ⟨γ, hγ⟩ : ∃ γ : EuclideanSpace ℝ (Fin n),
      γ = a + b - c - Matrix.toEuclideanLin P (y - x₀) + p := ⟨_, rfl⟩
  have hGH : (A + B - P).IsHermitian := (hAH.add hBH).sub hP
  have hyr : ‖y - x₀‖ < r := by
    have := mem_ball.mp hyball; rwa [dist_eq_norm] at this
  have hloc2 : ∀ κ > 0, ∃ η > 0, ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ < η →
      inner ℝ γ h + (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin (A + B - P) h) h
        ≤ κ * ‖h‖ ^ 2 := by
    intro κ hκ
    obtain ⟨η1, hη1, hη1P⟩ := Metric.eventually_nhds_iff.mp
      ((jetu (κ / 2) (half_pos hκ)).and (jetv (κ / 2) (half_pos hκ)))
    refine ⟨min η1 (r - ‖y - x₀‖), lt_min hη1 (by linarith), fun h hh => ?_⟩
    have hh1 : ‖h‖ < η1 := lt_of_lt_of_le hh (min_le_left _ _)
    have hh2 : ‖h‖ < r - ‖y - x₀‖ := lt_of_lt_of_le hh (min_le_right _ _)
    have hzy : dist (y + h) y < η1 := by rw [dist_eq_norm, add_sub_cancel_left]; exact hh1
    obtain ⟨j1, j2⟩ := hη1P hzy
    rw [add_sub_cancel_left] at j1 j2
    have j1' := (abs_le.mp j1).1
    have j2' := (abs_le.mp j2).1
    have hzK : y + h ∈ closedBall x₀ r := by
      rw [mem_closedBall, dist_eq_norm]
      have : y + h - x₀ = (y - x₀) + h := by abel
      rw [this]
      linarith [norm_add_le (y - x₀) h]
    have hW := hpmax (y + h) hzK
    have hQd : Qf (y + h) - Qf y = inner ℝ c h + inner ℝ (Matrix.toEuclideanLin P (y - x₀)) h
        + 1 / 2 * inner ℝ (Matrix.toEuclideanLin P h) h := by
      rw [hQf, hQf]
      have e1 : y + h - x₀ = (y - x₀) + h := by abel
      have hs : inner ℝ (Matrix.toEuclideanLin P h) (y - x₀)
          = inner ℝ (Matrix.toEuclideanLin P (y - x₀)) h := by
        rw [hPsym, real_inner_comm]
      rw [e1]
      simp only [map_add, inner_add_left, inner_add_right]
      rw [hs]
      ring
    have hγh : inner ℝ γ h = inner ℝ a h + inner ℝ b h - inner ℝ c h
        - inner ℝ (Matrix.toEuclideanLin P (y - x₀)) h + inner ℝ p h := by
      rw [hγ]; simp only [inner_add_left, inner_sub_left]
    have hG : inner ℝ (Matrix.toEuclideanLin (A + B - P) h) h
        = inner ℝ (Matrix.toEuclideanLin A h) h + inner ℝ (Matrix.toEuclideanLin B h) h
          - inner ℝ (Matrix.toEuclideanLin P h) h := by
      rw [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, inner_sub_left,
        inner_add_left]
    have hph : inner ℝ p (y + h) = inner ℝ p y + inner ℝ p h := inner_add_right _ _ _
    rw [hWdef, hWdef, hph] at hW
    rw [hγh, hG]
    linarith
  obtain ⟨hγ0, hnegG⟩ := quadratic_upper_bound_conditions γ (A + B - P) hGH hloc2
  have hPSD : (P - (A + B)).PosSemidef := by
    have : P - (A + B) = -(A + B - P) := by abel
    rw [this]; exact hnegG
  -- the chain
  have hξ : a + b = c + Matrix.toEuclideanLin P (y - x₀) - p := by
    rw [hγ] at hγ0
    rw [← sub_eq_zero, ← hγ0]; abel
  have hchain : L (a + b) P ≤ f yh + g yh' := by
    have h1 := hLe (a + b) P (A + B) hP (hAH.add hBH) hPSD
    have h2 := hLs a b A B hAH hBH
    linarith
  have hξc : dist (a + b) c < ρL := by
    rw [hξ, dist_eq_norm]
    have e : c + Matrix.toEuclideanLin P (y - x₀) - p - c = PL (y - x₀) - p := by rw [hPL]; abel
    rw [e]
    have h1 : ‖PL (y - x₀) - p‖ ≤ ‖PL‖ * ‖y - x₀‖ + ‖p‖ := by
      have h1a := PL.le_opNorm (y - x₀)
      have h1b := norm_sub_le (PL (y - x₀)) p
      linarith
    have hlam0 : 0 ≤ ‖PL‖ := norm_nonneg PL
    have h2 : ‖PL‖ * ‖y - x₀‖ ≤ ‖PL‖ * ρ :=
      mul_le_mul_of_nonneg_left hyρ.le hlam0
    nlinarith
  have hLξ := hρLP hξc
  have hfy : f yh < f x₀ + σ / 3 := hρfP ⟨by
    rw [mem_ball]; have := hclose yh hyh1; linarith, hball hyhK⟩
  have hgy : g yh' < g x₀ + σ / 3 := hρgP ⟨by
    rw [mem_ball]; have := hclose yh' hyh2; linarith, hball hyh'K⟩
  linarith
