import Polyfold
/-! Blind formalization of V15_34 (the Springer 2021 book, Part II, §15.3, Corollary 15.3.10 (3),
pp. 699–700; 2017: Corollary 15.1 (3)): regular perturbations are cobordant.

Text: there is a structurable regular perturbation `(Ñ, Ũ, Λ̃)` of `f̃` on `[0, 1] × X` with
`Λ̃ = Λⁱ` over `{i} × X`; `Θ̃ = Λ̃ ∘ f̃` is a compact cobordism between `Θ₀` and `Θ₁` (proof:
Theorem 15.3.9 on `[0, 1] × X`).

Choices:
- Setting: the standing hypotheses of Corollary 15.3.10 (as in my `V15_33.lean`): universe 0,
  `A : SEP.{0}`, `d_X ≡ 0` (`degIndex = 0` at every object), `|X|` paracompact
  (`HasParacompactOrbitSpace`), `f` an sc-Fredholm section functor with `|S_f|` compact.
  Doubt as in V15_33: no bump-function / partition-of-unity hypothesis is quoted, none added.
- `Λ⁰`, `Λ¹`, `Θᵢ = Λⁱ ∘ f`: read from the corollary's context (part (2), not quoted in my
  statement file) as two structurable regular perturbations `(Nᵢ, Uᵢ, Λⁱ)` of `f` (part (1));
  "structurable regular perturbation" is the project's `IsRegularPerturbation` (`#print`ed:
  `(N, U)` controls compactness, `Λ` structurable, `dom-supp Λ ⊆ U`, `N(Λ) < 1`, `T(f,Λ)` onto on
  the support), the notion my V15_33 spells out.  The two pairs `(Nᵢ, Uᵢ)` may differ.
- `[0, 1] × X` and `f̃`: the project's `A.cubeSEP 1` (the pull-back `W̃ → [0, 1] × X` of `W` along
  the projection; objects `(Fin 1 → [0, 1]) × Obj`, points of `W̃` are triples `((q, x), w)` with
  `w ∈ W_x`, read by `SEP.cubeVal`) and `f̃ = cubeLiftSec f`, `(q, y) ↦ ((q, y), f(y))`.
  "structurable regular perturbation of `f̃`": `IsRegularPerturbation (A.cubeSEP 1) f̃ Ñ Ũ Λ̃`.
- "`Λ̃ = Λⁱ` over `{i} × X`": for every `w̃ = ((q, x), w)` with `q = i`, `Λ̃(w̃) = Λⁱ(w)`.
- "`Θ̃` is a compact cobordism between `Θ₀` and `Θ₁`": `Θ̃ = z ↦ Λ̃(f̃(z))` is a branched
  ep⁺-subgroupoid of `[0, 1] × X`, compact and tame, whose boundary `∂Θ̃` (the project's
  `boundaryTheta`, Definition 9.2.16) is `Θ₀ ⊔ Θ₁`: `∂Θ̃(i, x) = Θᵢ(x)` for `i ∈ {0, 1}` (off
  `{0, 1} × X = ∂([0, 1] × X)` the boundary functor vanishes by definition).  Orientations are not
  part of this item.
- Nothing looks doubtful to me (apart from the doubt above).
-/
namespace RoundTrip.V15_34
open Polyfold Polyfold.SBLocalization

/-- The point `i ∈ [0, 1]` as an element of `[0, 1]¹`. -/
def tPt (i : unitInterval) : Fin 1 → unitInterval := fun _ => i

/-- `Θ = Λ ∘ g` as a functor to `ℚ`. -/
def comp {A : SEP.{0}} (Λ : A.W → ℚ≥0) (g : A.Obj → A.W) : A.Obj → ℚ :=
  fun z => ((Λ (g z) : ℚ≥0) : ℚ)

/-- Corollary 15.3.10 (3). -/
def B : Prop :=
  ∀ (A : SEP.{0}), (∀ x : A.Obj, A.X.PObj.degIndex x = 0) → A.X.HasParacompactOrbitSpace →
    ∀ (f : A.Obj → A.W), A.E.IsScFredholmSectionFunctor f → A.E.HasCompactSolutionSetEp f →
    ∀ (N₀ N₁ : A.B.One → ℝ) (U₀ U₁ : Set A.Obj) (Λ₀ Λ₁ : A.W → ℚ≥0),
      IsRegularPerturbation A f N₀ U₀ Λ₀ → IsRegularPerturbation A f N₁ U₁ Λ₁ →
      ∃ (Nt : (A.cubeSEP 1).B.One → ℝ) (Ut : Set (A.cubeSEP 1).Obj)
        (Λt : (A.cubeSEP 1).W → ℚ≥0),
        IsRegularPerturbation (A.cubeSEP 1) (cubeLiftSec f) Nt Ut Λt ∧
        -- `Λ̃ = Λ⁰` over `{0} × X` and `Λ̃ = Λ¹` over `{1} × X`
        (∀ w : (A.cubeSEP 1).W, (SEP.cubeVal w).1.1 = tPt 0 → Λt w = Λ₀ (SEP.cubeVal w).2) ∧
        (∀ w : (A.cubeSEP 1).W, (SEP.cubeVal w).1.1 = tPt 1 → Λt w = Λ₁ (SEP.cubeVal w).2) ∧
        -- `Θ̃` is a compact (tame, branched) cobordism between `Θ₀` and `Θ₁`
        (A.cubeSEP 1).X.IsBranchedEpSubgroupoid (comp Λt (cubeLiftSec f)) ∧
        (A.cubeSEP 1).X.IsCompactBranched (comp Λt (cubeLiftSec f)) ∧
        (A.cubeSEP 1).X.IsTameBranched (comp Λt (cubeLiftSec f)) ∧
        (∀ x : A.Obj,
          (A.cubeSEP 1).X.boundaryTheta (comp Λt (cubeLiftSec f)) (tPt 0, x) = comp Λ₀ f x ∧
          (A.cubeSEP 1).X.boundaryTheta (comp Λt (cubeLiftSec f)) (tPt 1, x) = comp Λ₁ f x)

end RoundTrip.V15_34
