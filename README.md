# Superposition in disjoint variables for the infinity Laplacian, in Lean 4

This repository contains a complete Lean 4 formalization, built on [Mathlib](https://github.com/leanprover-community/mathlib4), of the main results of

> Qing Liu, Juan J. Manfredi and Xiaodan Zhou,
> *Superposition property in disjoint variables for the infinity Laplace equation*,
> RIMS Kôkyûroku Bessatsu **B99** (2026), 19–34.
> [arXiv:2508.17106](https://arxiv.org/abs/2508.17106)

All three main theorems of the paper are stated and proved. The development contains no `sorry`, and each main theorem depends only on the three standard axioms of Lean (`propext`, `Classical.choice`, `Quot.sound`).

## Results

| Paper | Lean declaration | File |
|---|---|---|
| Theorem *Superposition in disjoint variables for the infinity Laplacian* (subsolutions) | `infsuper_subsolution` | [`Superposition/infsuper_subsolution.lean`](Superposition/infsuper_subsolution.lean) |
| ″ (supersolutions) | `infsuper_supersolution` | [`Superposition/infsuper_supersolution.lean`](Superposition/infsuper_supersolution.lean) |
| ″ (solutions) | `infsuper_solution` | [`Superposition/infsuper_solution.lean`](Superposition/infsuper_solution.lean) |
| Theorem *Subsolutions of sub-additive equations* | `superposition_common_subsolution` | [`Superposition/superposition_common_subsolution.lean`](Superposition/superposition_common_subsolution.lean) |
| Theorem *Superposition for comparison with cones* (from above) | `superposition_cone_above` | [`Superposition/superposition_cone_above.lean`](Superposition/superposition_cone_above.lean) |
| ″ (from below) | `superposition_cone_below` | [`Superposition/superposition_cone_below.lean`](Superposition/superposition_cone_below.lean) |
| ″ (from both sides) | `superposition_cone_both` | [`Superposition/superposition_cone_both.lean`](Superposition/superposition_cone_both.lean) |

Proposition *Superposition for Laplacian*, Proposition *Subsolutions of convex equations* and the remarks of the paper are not formalized.

For instance, the main theorem reads as follows. Here `EuclidFst` and `EuclidSnd` split a point of ℝ<sup>n+m</sup> into its first `n` and last `m` coordinates, and `InfLaplaceOperator ξ X = -⟪X ξ, ξ⟫`.

```lean
theorem infsuper_solution {n m : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (V : Set (EuclideanSpace ℝ (Fin m)))
    (hU : IsOpenDomain U) (hV : IsOpenDomain V)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin m) → ℝ)
    (hu : IsViscositySolution U InfLaplaceOperator f u)
    (hv : IsViscositySolution V InfLaplaceOperator g v) :
    IsViscositySolution {z : EuclideanSpace ℝ (Fin (n + m)) | EuclidFst z ∈ U ∧ EuclidSnd (n := n) z ∈ V}
      InfLaplaceOperator (fun z => f (EuclidFst z) + g (EuclidSnd (n := n) z))
      (fun z => u (EuclidFst z) + v (EuclidSnd (n := n) z))
```

## How the definitions model the paper

- **Viscosity solutions** (paper, Definition *Viscosity solutions*). `IsViscositySubsolution Ω L f u` asks that `u` be upper semicontinuous on `Ω` and that `L (∇ψ x₀) (∇²ψ x₀) ≤ f x₀` whenever `ψ` is C² on `Ω` and `u - ψ` has a local maximum at `x₀ ∈ Ω`. Supersolutions are defined symmetrically, and a solution is both. Functions are total on the ambient space; only their values on `Ω` enter.
- **Elliptic and sub-additive operators** are the paper's conditions (ellip) and (sub-add), imposed on symmetric matrices.
- **Comparison with cones** (paper, Definition *Comparison with cones*) is `ConeComparisonAbove`, `ConeComparisonBelow` and `ConeComparisonBoth`. The condition 𝒪 ⊂⊂ Ω is expressed as: `𝒪` is open and bounded, its closure is compact, and its closure lies in `Ω`.
- **The product metric.** The paper equips X × Y with d<sub>1</sub> = d<sub>X</sub> + d<sub>Y</sub>. Mathlib's default metric on a product is the maximum metric, so the formalization uses `WithLp 1 (X × Y)`, which carries exactly d<sub>1</sub>.

## How the proofs relate to the paper

The paper proves the Euclidean results with the Theorem on Sums of Crandall, Ishii and Lions. Mathlib does not contain that theorem, so we formalize the ingredients of its standard proof and use them directly:

- sup-convolution and its basic properties (`SupConvolution`, `supConvolution_properties`, `supConvolution_jet_transfer`);
- Alexandrov's theorem on the twice differentiability almost everywhere of convex functions (`alexandrov_convex`);
- Jensen's lemma (`jensen_positive_measure`);
- the fact that Lipschitz maps send null sets to null sets (`lipschitz_image_null`).

The argument is then the Crandall–Ishii–Lions argument, specialized to disjoint variables. The supersolution case is reduced to the subsolution case through u ↦ −u. The metric-space theorem follows the slicing argument of the paper closely.

The formalization also shows that the proof of `superposition_cone_above` uses neither that X and Y are geodesic, nor that U and V are open and connected, nor that U ≠ X and V ≠ Y. These hypotheses are kept so that the statement matches the paper. Moreover, the point z₀ in the paper's proof need not be a maximizer of w − φ; it suffices that w(z₀) > φ(z₀).

## Blueprint

The directory [`blueprint/`](blueprint) contains a natural-language statement and a detailed proof for every Lean declaration, cross-referenced to the paper and to each other. They are collected, in dependency order, in [`blueprint/blueprint.pdf`](blueprint/blueprint.pdf). To rebuild it, run `pdflatex blueprint.tex` three times in that directory.

## Building and checking

Install Lean with [elan](https://github.com/leanprover/elan), then:

```sh
git clone <repository URL> superposition-lean
cd superposition-lean
lake exe cache get        # download prebuilt Mathlib
lake build
lake env lean Axioms.lean # print the axioms used by each main theorem
```

The project is pinned to Lean `v4.33.0` and Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. Continuous integration rebuilds the project and checks the axioms on every push.

## Layout

```
Superposition.lean         root module, imports the main theorems
Superposition/             one file per definition, lemma or theorem
Axioms.lean                #print axioms for the main theorems
blueprint/blueprint.tex    natural-language companion (inputs blueprint/nodes/*.tex)
```

## How this formalization was produced

The formalization was produced with Trellis, an AI-assisted formalization pipeline that uses Claude (Anthropic). Each node was reviewed automatically for soundness of its natural-language proof, for faithfulness to the paper, and for agreement between its Lean statement and its natural-language statement. The Lean kernel checks every proof.

<!-- TODO before release: replace this comment with a sentence confirming that the authors have read the Lean statements of the definitions and main theorems. -->

## Citation

Please cite the paper; see [`CITATION.cff`](CITATION.cff).

## License

Apache License 2.0, the license used by Mathlib. See [`LICENSE`](LICENSE).
