module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Definitions used in the statements of the main results

Generated together with `Challenge.lean` and kept textually identical to its definitions section
(same Mathlib imports, same declarations in the same order), so that both elaborate to the same
terms, including the names of auxiliary proofs, as Comparator requires.
-/

@[expose] public section

section IsOpenDomain

/-- A domain: a nonempty, open, connected subset (`IsConnected` includes nonemptiness). -/
def IsOpenDomain {X : Type*} [TopologicalSpace X] (Ω : Set X) : Prop :=
  IsOpen Ω ∧ IsConnected Ω

end IsOpenDomain

section EuclidHessian
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

/-- The Hessian matrix `∇²ψ(x) = (∂ᵢ∂ⱼψ(x))ᵢⱼ` of `ψ : ℝⁿ → ℝ`, as the second Fréchet
derivative evaluated on the standard basis. -/
noncomputable def EuclidHessian {n : ℕ} (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => fderiv ℝ (fderiv ℝ ψ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

end EuclidHessian

section InfLaplaceOperator
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

/-- The operator of the infinity Laplace equation `-Δ∞u = f`: `F(ξ, X) = -⟨X ξ, ξ⟩`, so that
`F(∇u, ∇²u) = -⟨∇²u ∇u, ∇u⟩ = -Δ∞u` (paper, §1). -/
noncomputable def InfLaplaceOperator {n : ℕ} (ξ : EuclideanSpace ℝ (Fin n))
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -(inner ℝ (Matrix.toEuclideanLin X ξ) ξ)

end InfLaplaceOperator

section IsViscositySubsolution
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

/-- `u` is a viscosity subsolution of `L(∇u, ∇²u) = f` in `Ω` (paper, Definition *Viscosity
solutions*): `u` is upper semicontinuous on `Ω`, and whenever `ψ` is `C²` on `Ω` and `u - ψ` has a
local maximum at `x₀ ∈ Ω`, `L(∇ψ(x₀), ∇²ψ(x₀)) ≤ f(x₀)`. Functions are total on `ℝⁿ`; only their
values on `Ω` enter. -/
def IsViscositySubsolution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (L : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ → ℝ)
    (f u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  UpperSemicontinuousOn u Ω ∧
  ∀ x₀ ∈ Ω, ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ 2 ψ Ω →
    IsLocalMax (fun x => u x - ψ x) x₀ → L (gradient ψ x₀) (EuclidHessian ψ x₀) ≤ f x₀

end IsViscositySubsolution

section IsViscositySupersolution
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

/-- `u` is a viscosity supersolution of `L(∇u, ∇²u) = f` in `Ω`: `u` is lower semicontinuous on `Ω`,
and whenever `ψ` is `C²` on `Ω` and `u - ψ` has a local minimum at `x₀ ∈ Ω`,
`f(x₀) ≤ L(∇ψ(x₀), ∇²ψ(x₀))`. -/
def IsViscositySupersolution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (L : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ → ℝ)
    (f u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  LowerSemicontinuousOn u Ω ∧
  ∀ x₀ ∈ Ω, ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ 2 ψ Ω →
    IsLocalMin (fun x => u x - ψ x) x₀ → f x₀ ≤ L (gradient ψ x₀) (EuclidHessian ψ x₀)

end IsViscositySupersolution

section IsViscositySolution
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

/-- `u` is a viscosity solution: both a subsolution and a supersolution. -/
def IsViscositySolution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (L : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ → ℝ)
    (f u : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  IsViscositySubsolution Ω L f u ∧ IsViscositySupersolution Ω L f u

end IsViscositySolution

section EuclidFst
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

/-- The first `n` coordinates `x` of a point `z = (x, y) ∈ ℝⁿ⁺ᵐ = ℝⁿ × ℝᵐ`. -/
noncomputable def EuclidFst {n m : ℕ} (z : EuclideanSpace ℝ (Fin (n + m))) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i : Fin n => z (Fin.castAdd m i))

end EuclidFst

section EuclidSnd
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

/-- The last `m` coordinates `y` of a point `z = (x, y) ∈ ℝⁿ⁺ᵐ = ℝⁿ × ℝᵐ`. -/
noncomputable def EuclidSnd {n m : ℕ} (z : EuclideanSpace ℝ (Fin (n + m))) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun j : Fin m => z (Fin.natAdd n j))

end EuclidSnd

section IsDegenerateElliptic
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

/-- Degenerate ellipticity (paper, (ellip)): `L(ξ, X) ≤ L(ξ, Y)` for symmetric `X, Y` with
`X - Y` positive semidefinite. -/
def IsDegenerateElliptic {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ → ℝ) : Prop :=
  ∀ ξ X Y, X.IsHermitian → Y.IsHermitian → (X - Y).PosSemidef → L ξ X ≤ L ξ Y

end IsDegenerateElliptic

section IsSubadditiveOperator
open Matrix Metric MeasureTheory Filter Asymptotics Set
open scoped Topology

/-- Sub-additivity (paper, (sub-add)): `L(ξ + η, X + Y) ≤ L(ξ, X) + L(η, Y)` for symmetric `X, Y`. -/
def IsSubadditiveOperator {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ → ℝ) : Prop :=
  ∀ ξ η X Y, X.IsHermitian → Y.IsHermitian → L (ξ + η) (X + Y) ≤ L ξ X + L η Y

end IsSubadditiveOperator

section IsGeodesicSpace

/-- A metric space is geodesic if any two points `x, y` are joined by a curve `γ` with `γ(0) = x`,
`γ(d(x,y)) = y`, which is an isometry on `[0, d(x,y)]`. -/
def IsGeodesicSpace (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ : ℝ → X, γ 0 = x ∧ γ (dist x y) = y ∧
    ∀ s ∈ Set.Icc (0 : ℝ) (dist x y), ∀ t ∈ Set.Icc (0 : ℝ) (dist x y),
      dist (γ s) (γ t) = |s - t|

end IsGeodesicSpace

section ConeComparisonAbove

/-- Comparison with cones from above (paper, Definition *Comparison with cones*): `u` is locally
bounded above on `Ω`, and for every `x̂ ∈ Ω`, `c ∈ ℝ`, `κ ≥ 0` and bounded open `𝒪 ⊂⊂ Ω` with
`x̂ ∉ 𝒪`, if `u ≤ c + κ d(x̂, ·)` on `∂𝒪` then `u ≤ c + κ d(x̂, ·)` on `closure 𝒪`. Here `𝒪 ⊂⊂ Ω`
is expressed as: `𝒪` open and bounded, with compact closure contained in `Ω`. -/
def ConeComparisonAbove {X : Type*} [MetricSpace X] (Ω : Set X) (u : X → ℝ) : Prop :=
  (∀ x ∈ Ω, ∃ t ∈ nhds x, BddAbove (u '' (t ∩ Ω))) ∧
  ∀ (xh : X) (c κ : ℝ) (O : Set X), xh ∈ Ω → xh ∉ O → 0 ≤ κ →
    IsOpen O → Bornology.IsBounded O → IsCompact (closure O) → closure O ⊆ Ω →
    (∀ x ∈ frontier O, u x ≤ c + κ * dist xh x) →
    ∀ x ∈ closure O, u x ≤ c + κ * dist xh x

end ConeComparisonAbove

section ConeComparisonBelow

/-- Comparison with cones from below: `-u` satisfies comparison with cones from above. -/
def ConeComparisonBelow {X : Type*} [MetricSpace X] (Ω : Set X) (u : X → ℝ) : Prop :=
  ConeComparisonAbove Ω (fun x => -u x)

end ConeComparisonBelow

section ConeComparisonBoth

/-- Comparison with cones from both sides. -/
def ConeComparisonBoth {X : Type*} [MetricSpace X] (Ω : Set X) (u : X → ℝ) : Prop :=
  ConeComparisonAbove Ω u ∧ ConeComparisonBelow Ω u

end ConeComparisonBoth
