import Superposition.InfLaplaceOperator
import Superposition.IsViscositySubsolution
import Superposition.SupConvolution
import Superposition.supConvolution_properties
import Superposition.supConvolution_jet_transfer
import Superposition.alexandrov_convex
import Superposition.jensen_positive_measure
import Superposition.quadratic_convex_part
import Superposition.quadratic_upper_bound_conditions
import Superposition.expansion_sub_half_sq_norm
import Superposition.jet_twosided_to_upper
import Superposition.disjoint_supConvolution_concentration
import Superposition.euclidSplit_norm_sq
import Superposition.euclidSplit_preimage_null
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

theorem disjoint_sum_quadratic_strict {n m : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (V : Set (EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin m) → ℝ)
    (hu : IsViscositySubsolution U InfLaplaceOperator f u)
    (hv : IsViscositySubsolution V InfLaplaceOperator g v)
    (z₀ : EuclideanSpace ℝ (Fin (n + m))) (r : ℝ) (hr : 0 < r)
    (hball : closedBall z₀ r ⊆ {z | EuclidFst z ∈ U ∧ EuclidSnd (n := n) z ∈ V})
    (q₀ : ℝ) (c : EuclideanSpace ℝ (Fin (n + m))) (P : Matrix (Fin (n + m)) (Fin (n + m)) ℝ)
    (hP : P.IsHermitian)
    (hstrict : ∀ z ∈ closedBall z₀ r, z ≠ z₀ →
      u (EuclidFst z) + v (EuclidSnd (n := n) z) - (q₀ + inner ℝ c (z - z₀)
        + (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin P (z - z₀)) (z - z₀))
        < u (EuclidFst z₀) + v (EuclidSnd (n := n) z₀) - q₀) :
    InfLaplaceOperator c P ≤ f (EuclidFst z₀) + g (EuclidSnd (n := n) z₀) := by
  -- block calculus
  have fst_add : ∀ a b : EuclideanSpace ℝ (Fin (n + m)),
      EuclidFst (a + b) = EuclidFst a + EuclidFst b := by
    intro a b; ext i; simp [EuclidFst]
  have snd_add : ∀ a b : EuclideanSpace ℝ (Fin (n + m)),
      EuclidSnd (n := n) (a + b) = EuclidSnd (n := n) a + EuclidSnd (n := n) b := by
    intro a b; ext i; simp [EuclidSnd]
  have fst_sub : ∀ a b : EuclideanSpace ℝ (Fin (n + m)),
      EuclidFst (a - b) = EuclidFst a - EuclidFst b := by
    intro a b; ext i; simp [EuclidFst]
  have snd_sub : ∀ a b : EuclideanSpace ℝ (Fin (n + m)),
      EuclidSnd (n := n) (a - b) = EuclidSnd (n := n) a - EuclidSnd (n := n) b := by
    intro a b; ext i; simp [EuclidSnd]
  have fst_smul : ∀ (t : ℝ) (a : EuclideanSpace ℝ (Fin (n + m))),
      EuclidFst (t • a) = t • EuclidFst a := by
    intro t a; ext i; simp [EuclidFst]
  have snd_smul : ∀ (t : ℝ) (a : EuclideanSpace ℝ (Fin (n + m))),
      EuclidSnd (n := n) (t • a) = t • EuclidSnd (n := n) a := by
    intro t a; ext i; simp [EuclidSnd]
  have inner_split : ∀ a b : EuclideanSpace ℝ (Fin (n + m)),
      inner ℝ a b = inner ℝ (EuclidFst a) (EuclidFst b)
        + inner ℝ (EuclidSnd (n := n) a) (EuclidSnd (n := n) b) := by
    intro a b
    simp [PiLp.inner_apply, EuclidFst, EuclidSnd, Fin.sum_univ_add]
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
  have concat : ∀ (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)),
      ∃ ζ : EuclideanSpace ℝ (Fin (n + m)), EuclidFst ζ = x ∧ EuclidSnd (n := n) ζ = y := by
    intro x y
    refine ⟨WithLp.toLp 2 (Fin.append (x : Fin n → ℝ) (y : Fin m → ℝ)), ?_, ?_⟩
    · ext i; simp [EuclidFst]
    · ext j; simp [EuclidSnd]
  have hLc : ∀ k : ℕ, Continuous (fun p : EuclideanSpace ℝ (Fin k) × Matrix (Fin k) (Fin k) ℝ =>
      InfLaplaceOperator p.1 p.2) := by
    intro k
    have : (fun p : EuclideanSpace ℝ (Fin k) × Matrix (Fin k) (Fin k) ℝ =>
        InfLaplaceOperator p.1 p.2) = fun p => -∑ i, (p.2 *ᵥ p.1.ofLp) i * p.1 i := by
      funext p
      simp [InfLaplaceOperator, Matrix.toLpLin_apply, PiLp.inner_apply, mul_comm]
    rw [this]
    fun_prop
  -- Setup
  have hKc : IsCompact (closedBall z₀ r) := isCompact_closedBall z₀ r
  have hz₀K : z₀ ∈ closedBall z₀ r := mem_closedBall_self hr.le
  have hK1c : IsCompact (closedBall (EuclidFst z₀) r) := isCompact_closedBall _ r
  have hK2c : IsCompact (closedBall (EuclidSnd (n := n) z₀) r) := isCompact_closedBall _ r
  have hx₀K1 : EuclidFst z₀ ∈ closedBall (EuclidFst z₀) r := mem_closedBall_self hr.le
  have hy₀K2 : EuclidSnd (n := n) z₀ ∈ closedBall (EuclidSnd (n := n) z₀) r :=
    mem_closedBall_self hr.le
  have hK1U : closedBall (EuclidFst z₀) r ⊆ U := by
    intro x hx
    obtain ⟨ζ, h1, h2⟩ := concat x (EuclidSnd (n := n) z₀)
    have hζ : ζ ∈ closedBall z₀ r := by
      rw [mem_closedBall, dist_eq_norm]
      rw [mem_closedBall, dist_eq_norm] at hx
      have e := euclidSplit_norm_sq (ζ - z₀)
      rw [fst_sub, snd_sub, h1, h2, sub_self, norm_zero] at e
      have : ‖ζ - z₀‖ ^ 2 ≤ r ^ 2 := by
        rw [e]; nlinarith [norm_nonneg (x - EuclidFst z₀)]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr.le two_ne_zero).mp this
    have := (hball hζ).1
    rwa [h1] at this
  have hK2V : closedBall (EuclidSnd (n := n) z₀) r ⊆ V := by
    intro y hy
    obtain ⟨ζ, h1, h2⟩ := concat (EuclidFst z₀) y
    have hζ : ζ ∈ closedBall z₀ r := by
      rw [mem_closedBall, dist_eq_norm]
      rw [mem_closedBall, dist_eq_norm] at hy
      have e := euclidSplit_norm_sq (ζ - z₀)
      rw [fst_sub, snd_sub, h1, h2, sub_self, norm_zero] at e
      have : ‖ζ - z₀‖ ^ 2 ≤ r ^ 2 := by
        rw [e]; nlinarith [norm_nonneg (y - EuclidSnd (n := n) z₀)]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr.le two_ne_zero).mp this
    have := (hball hζ).2
    rwa [h2] at this
  have hK1ne : (closedBall (EuclidFst z₀) r).Nonempty := ⟨_, hx₀K1⟩
  have hK2ne : (closedBall (EuclidSnd (n := n) z₀) r).Nonempty := ⟨_, hy₀K2⟩
  have huK : UpperSemicontinuousOn u (closedBall (EuclidFst z₀) r) := hu.1.mono hK1U
  have hvK : UpperSemicontinuousOn v (closedBall (EuclidSnd (n := n) z₀) r) := hv.1.mono hK2V
  have hPsym : (Matrix.toEuclideanLin P).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hP
  obtain ⟨PL, hPL⟩ : ∃ PL : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] EuclideanSpace ℝ (Fin (n + m)),
      ∀ h, PL h = Matrix.toEuclideanLin P h :=
    ⟨LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin P), fun h => rfl⟩
  obtain ⟨Qf, hQf⟩ : ∃ Qf : EuclideanSpace ℝ (Fin (n + m)) → ℝ, ∀ y, Qf y =
      q₀ + inner ℝ c (y - z₀) + (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin P (y - z₀)) (y - z₀) :=
    ⟨_, fun y => rfl⟩
  have hQc : Continuous Qf := by
    have h1 : Continuous (fun y : EuclideanSpace ℝ (Fin (n + m)) => y - z₀) :=
      continuous_id.sub continuous_const
    have : Qf = fun y => q₀ + inner ℝ c (y - z₀) + (1 / 2 : ℝ) * inner ℝ (PL (y - z₀)) (y - z₀) := by
      funext y; rw [hQf, hPL]
    rw [this]
    exact (continuous_const.add (continuous_const.inner h1)).add
      (continuous_const.mul ((PL.continuous.comp h1).inner h1))
  have hQz₀ : Qf z₀ = q₀ := by rw [hQf]; simp
  have hstrict' : ∀ z ∈ closedBall z₀ r, z ≠ z₀ →
      u (EuclidFst z) + v (EuclidSnd (n := n) z) - Qf z
        < u (EuclidFst z₀) + v (EuclidSnd (n := n) z₀) - Qf z₀ := by
    intro z hz hne; rw [hQf, hQz₀]; exact hstrict z hz hne
  obtain ⟨zu, -, hzu⟩ := huK.exists_isMaxOn hK1ne hK1c
  obtain ⟨zv, -, hzv⟩ := hvK.exists_isMaxOn hK2ne hK2c
  obtain ⟨MQ, hMQ⟩ := hKc.exists_bound_of_continuousOn hQc.continuousOn
  -- the σ-argument
  refine le_of_forall_pos_le_add fun σ hσ => ?_
  have hLcont : Continuous (fun ξ : EuclideanSpace ℝ (Fin (n + m)) => InfLaplaceOperator ξ P) := by
    have h := (hLc (n + m)).comp
      ((continuous_id (X := EuclideanSpace ℝ (Fin (n + m)))).prodMk
        (continuous_const (y := P)))
    exact h
  have hev : ∀ᶠ ξ in 𝓝 c, InfLaplaceOperator c P - σ / 3 < InfLaplaceOperator ξ P :=
    hLcont.continuousAt.eventually (lt_mem_nhds (by linarith))
  obtain ⟨ρL, hρL, hρLP⟩ := Metric.eventually_nhds_iff.mp hev
  have hx₀U : EuclidFst z₀ ∈ U := hK1U hx₀K1
  have hy₀V : EuclidSnd (n := n) z₀ ∈ V := hK2V hy₀K2
  obtain ⟨ρf, hρf, hρfP⟩ := (Metric.nhdsWithin_basis_ball.eventually_iff).mp
    ((hf _ hx₀U).eventually (gt_mem_nhds
      (show f (EuclidFst z₀) < f (EuclidFst z₀) + σ / 3 by linarith)))
  obtain ⟨ρg, hρg, hρgP⟩ := (Metric.nhdsWithin_basis_ball.eventually_iff).mp
    ((hg _ hy₀V).eventually (gt_mem_nhds
      (show g (EuclidSnd (n := n) z₀) < g (EuclidSnd (n := n) z₀) + σ / 3 by linarith)))
  obtain ⟨ρ, hρ0, hρr, hρL', hρf', hρg'⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r / 2 ∧
      ρ * (‖PL‖ + 2) ≤ ρL ∧ ρ ≤ ρf / 2 ∧ ρ ≤ ρg / 2 := by
    refine ⟨min (r / 2) (min (ρL / (‖PL‖ + 2)) (min (ρf / 2) (ρg / 2))),
      lt_min (half_pos hr) (lt_min (by positivity) (lt_min (half_pos hρf) (half_pos hρg))),
      min_le_left _ _, ?_, (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
    exact (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨β, hβ, ε₀, hε₀, hA⟩ := disjoint_supConvolution_concentration u v Qf z₀ r hr huK hvK hQc
    hstrict' ρ hρ0
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = u zu + v zv + MQ
      - (u (EuclidFst z₀) + v (EuclidSnd (n := n) z₀) - Qf z₀) + β := ⟨_, rfl⟩
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
  obtain ⟨SUi, SUii, SUiii⟩ := supConvolution_properties u _ hK1c hK1ne huK ε hε
  obtain ⟨SVi, SVii, SViii⟩ := supConvolution_properties v _ hK2c hK2ne hvK ε hε
  obtain ⟨W, hWdef⟩ : ∃ W : EuclideanSpace ℝ (Fin (n + m)) → ℝ, ∀ z, W z =
      SupConvolution u (closedBall (EuclidFst z₀) r) ε (EuclidFst z)
        + SupConvolution v (closedBall (EuclidSnd (n := n) z₀) r) ε (EuclidSnd (n := n) z) - Qf z :=
    ⟨_, fun z => rfl⟩
  have hW2 : u (EuclidFst z₀) + v (EuclidSnd (n := n) z₀) - Qf z₀ ≤ W z₀ := by
    have h1 := SUi (EuclidFst z₀) (EuclidFst z₀) hx₀K1
    have h2 := SVi (EuclidSnd (n := n) z₀) (EuclidSnd (n := n) z₀) hy₀K2
    simp only [sub_self, norm_zero] at h1 h2
    rw [hWdef]
    have : (0 : ℝ) ^ 2 / (2 * ε) = 0 := by simp
    rw [this] at h1 h2
    linarith
  have hAW : ∀ z ∈ closedBall z₀ r, ρ ≤ ‖z - z₀‖ →
      W z ≤ u (EuclidFst z₀) + v (EuclidSnd (n := n) z₀) - Qf z₀ - β := by
    intro z hz hzρ; rw [hWdef]; exact hA ε hε hεε₀ z hz hzρ
  -- semiconvexity
  have hPbound : ∀ d, inner ℝ (Matrix.toEuclideanLin P d) d ≤ ‖PL‖ * ‖d‖ ^ 2 := by
    intro d
    have h1 := real_inner_le_norm (Matrix.toEuclideanLin P d) d
    have h2 := PL.le_opNorm d
    rw [hPL] at h2
    have hd := norm_nonneg d
    nlinarith
  let fstL : EuclideanSpace ℝ (Fin (n + m)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toFun := fun z => EuclidFst z, map_add' := fst_add, map_smul' := fst_smul }
  let sndL : EuclideanSpace ℝ (Fin (n + m)) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    { toFun := fun z => EuclidSnd (n := n) z, map_add' := snd_add, map_smul' := snd_smul }
  have hcu := SUiii.comp_linearMap fstL
  have hcv := SViii.comp_linearMap sndL
  simp only [preimage_univ] at hcu hcv
  have hconvW : ConvexOn ℝ univ (fun z => W z + (1 / ε + ‖PL‖) / 2 * ‖z‖ ^ 2) := by
    have := (hcu.add hcv).add (quadratic_convex_part z₀ c q₀ ‖PL‖ P hP hPbound)
    have heq : (fun z => W z + (1 / ε + ‖PL‖) / 2 * ‖z‖ ^ 2) =
        ((fun x => SupConvolution u (closedBall (EuclidFst z₀) r) ε x + ‖x‖ ^ 2 / (2 * ε)) ∘ fstL) +
        ((fun y => SupConvolution v (closedBall (EuclidSnd (n := n) z₀) r) ε y
          + ‖y‖ ^ 2 / (2 * ε)) ∘ sndL) +
        (fun x => ‖PL‖ / 2 * ‖x‖ ^ 2 - (q₀ + inner ℝ c (x - z₀)
          + (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin P (x - z₀)) (x - z₀))) := by
      funext z
      simp only [Pi.add_apply, Function.comp_apply, fstL, sndL, LinearMap.coe_mk, AddHom.coe_mk]
      rw [hWdef, hQf, euclidSplit_norm_sq z]
      field_simp
      ring
    rw [heq]; exact this
  -- Jensen
  have hsphere : ∀ z, ‖z - z₀‖ = r → W z + 2 * δ * r < W z₀ := by
    intro z hz
    have hzK : z ∈ closedBall z₀ r := by rw [mem_closedBall, dist_eq_norm, hz]
    have := hAW z hzK (by rw [hz]; linarith)
    linarith
  have hJ := jensen_positive_measure W (1 / ε + ‖PL‖) (by positivity) hconvW z₀ z₀ r δ hr hδ
    hz₀K hsphere
  -- Alexandrov (pulled back to the product)
  have hAu := alexandrov_convex _ SUiii
  have hAv := alexandrov_convex _ SViii
  have hAu' := ae_iff.mpr ((euclidSplit_preimage_null (n := n) (m := m)).1 _ (ae_iff.mp hAu))
  have hAv' := ae_iff.mpr ((euclidSplit_preimage_null (n := n) (m := m)).2 _ (ae_iff.mp hAv))
  obtain ⟨z, ⟨hzball, p, hp, hpmax⟩, ⟨au, Au, hAuH, hlu⟩, ⟨bv, Bv, hBvH, hlv⟩⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hJ.ne' (ae_restrict_of_ae (hAu'.and hAv'))
  -- location of z
  have hzK : z ∈ closedBall z₀ r := ball_subset_closedBall hzball
  have hWz : u (EuclidFst z₀) + v (EuclidSnd (n := n) z₀) - Qf z₀ - β < W z := by
    have h1 := hpmax z₀ hz₀K
    have h2 : inner ℝ p z - inner ℝ p z₀ ≤ δ * r := by
      rw [← inner_sub_right]
      refine (real_inner_le_norm _ _).trans ?_
      have : ‖z - z₀‖ ≤ r := by
        have := mem_closedBall.mp hzK; rwa [dist_eq_norm] at this
      exact mul_le_mul hp this (norm_nonneg _) hδ.le
    linarith
  have hzρ : ‖z - z₀‖ < ρ := by
    by_contra hc
    rw [not_lt] at hc
    have := hAW z hzK hc
    linarith
  obtain ⟨xh, hxhK, hxh⟩ := SUii (EuclidFst z)
  obtain ⟨yh, hyhK, hyh⟩ := SVii (EuclidSnd (n := n) z)
  have hdist : ‖EuclidFst z - xh‖ ^ 2 / (2 * ε) + ‖EuclidSnd (n := n) z - yh‖ ^ 2 / (2 * ε)
      ≤ |C0| := by
    have e := hWdef z
    rw [hxh, hyh] at e
    have hQy := hMQ z hzK
    rw [Real.norm_eq_abs] at hQy
    have := neg_abs_le (Qf z)
    have := hzu hxhK; have := hzv hyhK
    have := le_abs_self C0
    simp only [mem_ofPred_eq] at *
    linarith
  have hsqρ : ∀ {k : ℕ} (w w' : EuclideanSpace ℝ (Fin k)),
      ‖w - w'‖ ^ 2 / (2 * ε) ≤ |C0| → ‖w - w'‖ < ρ := by
    intro k w w' hz
    rw [div_le_iff₀ (by positivity)] at hz
    have : ‖w - w'‖ ^ 2 < ρ ^ 2 := by nlinarith [abs_nonneg C0]
    exact lt_of_pow_lt_pow_left₀ 2 hρ0.le this
  have hxh1 : ‖EuclidFst z - xh‖ < ρ := hsqρ _ _ (by
    have : 0 ≤ ‖EuclidSnd (n := n) z - yh‖ ^ 2 / (2 * ε) := by positivity
    linarith)
  have hyh1 : ‖EuclidSnd (n := n) z - yh‖ < ρ := hsqρ _ _ (by
    have : 0 ≤ ‖EuclidFst z - xh‖ ^ 2 / (2 * ε) := by positivity
    linarith)
  have hfz : ‖EuclidFst z - EuclidFst z₀‖ < ρ := by
    rw [← fst_sub]; exact lt_of_le_of_lt (fst_le _) hzρ
  have hsz : ‖EuclidSnd (n := n) z - EuclidSnd (n := n) z₀‖ < ρ := by
    rw [← snd_sub]; exact lt_of_le_of_lt (snd_le _) hzρ
  have hclose : ∀ {k : ℕ} (w w' w0 : EuclideanSpace ℝ (Fin k)), ‖w - w'‖ < ρ → ‖w - w0‖ < ρ →
      dist w' w0 < 2 * ρ := by
    intro k w w' w0 h1 h2
    rw [dist_eq_norm]
    have : w' - w0 = (w - w0) - (w - w') := by abel
    rw [this]
    calc ‖(w - w0) - (w - w')‖ ≤ ‖w - w0‖ + ‖w - w'‖ := norm_sub_le _ _
      _ < ρ + ρ := add_lt_add h2 h1
      _ = 2 * ρ := by ring
  have hxint : xh ∈ interior (closedBall (EuclidFst z₀) r) := by
    refine ball_subset_interior_closedBall ?_
    rw [mem_ball]; have := hclose _ _ _ hxh1 hfz; linarith
  have hyint : yh ∈ interior (closedBall (EuclidSnd (n := n) z₀) r) := by
    refine ball_subset_interior_closedBall ?_
    rw [mem_ball]; have := hclose _ _ _ hyh1 hsz; linarith
  -- jets of the sup-convolutions
  have jetu := expansion_sub_half_sq_norm _ ε hε (EuclidFst z) au Au hlu
  have jetv := expansion_sub_half_sq_norm _ ε hε (EuclidSnd (n := n) z) bv Bv hlv
  obtain ⟨a, ha⟩ : ∃ a : EuclideanSpace ℝ (Fin n), a = au - (1 / ε) • EuclidFst z := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : EuclideanSpace ℝ (Fin m), b = bv - (1 / ε) • EuclidSnd (n := n) z :=
    ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Fin n) (Fin n) ℝ,
      A = Au - (1 / ε) • (1 : Matrix (Fin n) (Fin n) ℝ) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : Matrix (Fin m) (Fin m) ℝ,
      B = Bv - (1 / ε) • (1 : Matrix (Fin m) (Fin m) ℝ) := ⟨_, rfl⟩
  rw [← ha, ← hAdef] at jetu
  rw [← hb, ← hBdef] at jetv
  have hAH : A.IsHermitian := by
    rw [hAdef]; exact hAuH.sub (by simp [Matrix.IsHermitian])
  have hBH : B.IsHermitian := by
    rw [hBdef]; exact hBvH.sub (by simp [Matrix.IsHermitian])
  -- jet transfer
  have hLu : InfLaplaceOperator a A ≤ f xh :=
    supConvolution_jet_transfer U InfLaplaceOperator (hLc n).continuousOn f u hu _ hK1c hK1U ε hε
      (EuclidFst z) xh hxint hxh a A hAH (jet_twosided_to_upper _ _ a A jetu)
  have hLv : InfLaplaceOperator b B ≤ g yh :=
    supConvolution_jet_transfer V InfLaplaceOperator (hLc m).continuousOn g v hv _ hK2c hK2V ε hε
      (EuclidSnd (n := n) z) yh hyint hyh b B hBH (jet_twosided_to_upper _ _ b B jetv)
  -- first- and second-order conditions (block form)
  obtain ⟨ξ, hξ1, hξ2⟩ := concat a b
  obtain ⟨γ, hγ⟩ : ∃ γ : EuclideanSpace ℝ (Fin (n + m)),
      γ = ξ - c - Matrix.toEuclideanLin P (z - z₀) + p := ⟨_, rfl⟩
  obtain ⟨qf, hqf⟩ : ∃ qf : EuclideanSpace ℝ (Fin (n + m)) → ℝ, ∀ h, qf h =
      inner ℝ (Matrix.toEuclideanLin A (EuclidFst h)) (EuclidFst h)
      + inner ℝ (Matrix.toEuclideanLin B (EuclidSnd (n := n) h)) (EuclidSnd (n := n) h)
      - inner ℝ (Matrix.toEuclideanLin P h) h := ⟨_, fun h => rfl⟩
  have hzr : ‖z - z₀‖ < r := by
    have := mem_ball.mp hzball; rwa [dist_eq_norm] at this
  have hloc2 : ∀ κ > 0, ∃ η > 0, ∀ h : EuclideanSpace ℝ (Fin (n + m)), ‖h‖ < η →
      inner ℝ γ h + (1 / 2 : ℝ) * qf h ≤ κ * ‖h‖ ^ 2 := by
    intro κ hκ
    obtain ⟨η1, hη1, hη1P⟩ := Metric.eventually_nhds_iff.mp (jetu (κ / 2) (half_pos hκ))
    obtain ⟨η2, hη2, hη2P⟩ := Metric.eventually_nhds_iff.mp (jetv (κ / 2) (half_pos hκ))
    refine ⟨min (min η1 η2) (r - ‖z - z₀‖), lt_min (lt_min hη1 hη2) (by linarith),
      fun h hh => ?_⟩
    have hh1 : ‖h‖ < η1 := lt_of_lt_of_le hh ((min_le_left _ _).trans (min_le_left _ _))
    have hh2 : ‖h‖ < η2 := lt_of_lt_of_le hh ((min_le_left _ _).trans (min_le_right _ _))
    have hh3 : ‖h‖ < r - ‖z - z₀‖ := lt_of_lt_of_le hh (min_le_right _ _)
    have d1 : dist (EuclidFst z + EuclidFst h) (EuclidFst z) < η1 := by
      rw [dist_eq_norm, add_sub_cancel_left]; exact lt_of_le_of_lt (fst_le h) hh1
    have d2 : dist (EuclidSnd (n := n) z + EuclidSnd (n := n) h) (EuclidSnd (n := n) z) < η2 := by
      rw [dist_eq_norm, add_sub_cancel_left]; exact lt_of_le_of_lt (snd_le h) hh2
    have j1 := hη1P d1
    have j2 := hη2P d2
    rw [add_sub_cancel_left] at j1 j2
    have j1' := (abs_le.mp j1).1
    have j2' := (abs_le.mp j2).1
    have hzK' : z + h ∈ closedBall z₀ r := by
      rw [mem_closedBall, dist_eq_norm]
      have : z + h - z₀ = (z - z₀) + h := by abel
      rw [this]
      linarith [norm_add_le (z - z₀) h]
    have hW := hpmax (z + h) hzK'
    have hQd : Qf (z + h) - Qf z = inner ℝ c h + inner ℝ (Matrix.toEuclideanLin P (z - z₀)) h
        + 1 / 2 * inner ℝ (Matrix.toEuclideanLin P h) h := by
      rw [hQf, hQf]
      have e1 : z + h - z₀ = (z - z₀) + h := by abel
      have hs : inner ℝ (Matrix.toEuclideanLin P h) (z - z₀)
          = inner ℝ (Matrix.toEuclideanLin P (z - z₀)) h := by
        rw [hPsym, real_inner_comm]
      rw [e1]
      simp only [map_add, inner_add_left, inner_add_right]
      rw [hs]
      ring
    have hγh : inner ℝ γ h = inner ℝ a (EuclidFst h) + inner ℝ b (EuclidSnd (n := n) h)
        - inner ℝ c h - inner ℝ (Matrix.toEuclideanLin P (z - z₀)) h + inner ℝ p h := by
      rw [hγ]
      simp only [inner_add_left, inner_sub_left]
      rw [inner_split ξ h, hξ1, hξ2]
    have hph : inner ℝ p (z + h) = inner ℝ p z + inner ℝ p h := inner_add_right _ _ _
    have hnorm := euclidSplit_norm_sq h
    rw [hWdef, hWdef, hph, fst_add, snd_add] at hW
    have hk : κ * ‖h‖ ^ 2 = κ * ‖EuclidFst h‖ ^ 2 + κ * ‖EuclidSnd (n := n) h‖ ^ 2 := by
      rw [hnorm]; ring
    rw [hγh, hqf, hk]
    have k1 := mul_nonneg hκ.le (sq_nonneg ‖EuclidFst h‖)
    have k2 := mul_nonneg hκ.le (sq_nonneg ‖EuclidSnd (n := n) h‖)
    linarith only [j1', j2', hW, hQd, k1, k2]
  -- the block-diagonal matrix diag(A, B)
  let D : Matrix (Fin (n + m)) (Fin (n + m)) ℝ :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)
  have hDH : D.IsHermitian := by
    have : (Matrix.fromBlocks A 0 0 B).IsHermitian :=
      Matrix.IsHermitian.fromBlocks hAH (by simp) hBH
    exact this.submatrix _
  have hDq : ∀ h : EuclideanSpace ℝ (Fin (n + m)), inner ℝ (Matrix.toEuclideanLin D h) h
      = inner ℝ (Matrix.toEuclideanLin A (EuclidFst h)) (EuclidFst h)
        + inner ℝ (Matrix.toEuclideanLin B (EuclidSnd (n := n) h)) (EuclidSnd (n := n) h) := by
    intro h
    simp [D, Matrix.toLpLin_apply, PiLp.inner_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_add,
      EuclidFst, EuclidSnd, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hqD : ∀ h, qf h = inner ℝ (Matrix.toEuclideanLin (D - P) h) h := by
    intro h
    rw [hqf, map_sub, LinearMap.sub_apply, inner_sub_left, hDq]
  have hloc2' : ∀ κ > 0, ∃ η > 0, ∀ h : EuclideanSpace ℝ (Fin (n + m)), ‖h‖ < η →
      inner ℝ γ h + (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin (D - P) h) h ≤ κ * ‖h‖ ^ 2 := by
    intro κ hκ
    obtain ⟨η, hη, hηP⟩ := hloc2 κ hκ
    exact ⟨η, hη, fun h hh => by rw [← hqD]; exact hηP h hh⟩
  obtain ⟨hγ0, hPSD⟩ := quadratic_upper_bound_conditions γ (D - P) (hDH.sub hP) hloc2'
  have h5 : qf ξ ≤ 0 := by
    have h0 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hPSD).2 ξ.ofLp
    have e : star ξ.ofLp ⬝ᵥ ((-(D - P)) *ᵥ ξ.ofLp)
        = inner ℝ (Matrix.toEuclideanLin (-(D - P)) ξ) ξ := by
      simp [Matrix.toLpLin_apply, PiLp.inner_apply, dotProduct, Matrix.sub_mulVec]
    rw [e, map_neg, LinearMap.neg_apply, inner_neg_left, ← hqD] at h0
    linarith
  rw [hqf, hξ1, hξ2] at h5
  -- the chain
  have hξeq : ξ = c + Matrix.toEuclideanLin P (z - z₀) - p := by
    rw [hγ] at hγ0
    rw [← sub_eq_zero, ← hγ0]; abel
  have hchain : InfLaplaceOperator ξ P ≤ f xh + g yh := by
    simp only [InfLaplaceOperator] at hLu hLv ⊢
    linarith
  have hξc : dist ξ c < ρL := by
    rw [hξeq, dist_eq_norm]
    have e : c + Matrix.toEuclideanLin P (z - z₀) - p - c = PL (z - z₀) - p := by rw [hPL]; abel
    rw [e]
    have h1 : ‖PL (z - z₀) - p‖ ≤ ‖PL‖ * ‖z - z₀‖ + ‖p‖ := by
      have h1a := PL.le_opNorm (z - z₀)
      have h1b := norm_sub_le (PL (z - z₀)) p
      linarith
    have hlam0 : 0 ≤ ‖PL‖ := norm_nonneg PL
    have h2 : ‖PL‖ * ‖z - z₀‖ ≤ ‖PL‖ * ρ := mul_le_mul_of_nonneg_left hzρ.le hlam0
    linarith only [h1, h2, hp, hδρ, hρL', hρ0]
  have hLξ := hρLP hξc
  have hfy : f xh < f (EuclidFst z₀) + σ / 3 := hρfP ⟨by
    rw [mem_ball]; have := hclose _ _ _ hxh1 hfz; linarith, hK1U hxhK⟩
  have hgy : g yh < g (EuclidSnd (n := n) z₀) + σ / 3 := hρgP ⟨by
    rw [mem_ball]; have := hclose _ _ _ hyh1 hsz; linarith, hK2V hyhK⟩
  linarith
