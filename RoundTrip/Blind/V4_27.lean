import Polyfold
/-! Blind formalization of V4_27 (the text's §4.1, proof of Theorem 4.2, (i) ⇒ (ii), p. 156).

Text: "The identity of `U` is a tame retraction, `U = U_∞` and `1_0^1 : U → U^1` is sc-smooth; so
`X_0 = X_∞`, `1_0^1` is sc-smooth and the statement (ii) follows."  The claim is the implication
(i) ⇒ (ii) of Theorem 4.2; the sentences quoted are its proof.  The statement of Theorem 4.2 is
taken from `RoundTrip/Blind/V4_5.lean` (same setting): for a tame M-polyfold `X`, (i) `X` has a
compatible smooth manifold structure with boundary with corners; (ii) `X_0 = X_∞`,
`1_0^1 : X → X^1` is sc-smooth, and every `x` lies in a tame chart `(V, ψ, (O, C, E))` with
`ψ(x) = 0` whose tangent space `T_0O` is finite-dimensional and in good position to `C`.

Choices:
- Setting: `X : Type` (universe 0, as asked), Hausdorff paracompact, `P : MPolyfold X`.  Theorem
  4.2 is stated for tame `X`, so `P.IsTame` (Definition 2.37, checked with `#print`: an equivalent
  atlas all of whose charts are modelled on tame retracts — a property of the given structure) is
  a hypothesis.  B is `P.IsTame → (i) → (ii)`.
- (i): the project's `P.HasCornerStructure` (Definition 4.1, checked: an atlas equivalent to that
  of `P` all of whose charts are corner charts, modelled on `(U, C, V)` with `U` relatively open in
  a partial quadrant `C` of a finite-dimensional `V` with the constant sc-structure and the
  identity retraction).
- `X_0 = X_∞`: `P.smoothSet = Set.univ` (checked: `⋂ m, X_m`, `X_m` the points mapped to level `m`
  by some compatible chart).  `1_0^1 : X → X^1`: `P.toLevelOne x₀` into the M-polyfold
  `P.shift` (checked: `x ↦ x` on `X_1`, junk `x₀` off `X_1`; `P.shift` is `X_1` with the level-1
  atlas, its paracompactness a project instance found by instance search).  Since `X_0 = X_∞` is
  asserted alongside, the junk never matters; B asks the sc-smoothness for every `x₀`.
- "tame chart `(V, ψ, (O, C, E))`": `P.IsChart ψ` (checked: compatible with every chart of the
  atlas) whose model is a tame retract (`IsTameRetract`, checked), `x` in its domain, `ψ(x) = 0`.
- `T_0O`: `Dr(0)E` = range of `scDeriv R.U R.toFun 0` for a retraction `R` onto `O` (Definition
  2.17; the fibre over `0` of `Tr(TU)`).  As a conclusion it is asserted for EVERY retraction `R`
  onto `O` (the text's `T_0O` does not depend on `R`).  "finite-dimensional" is
  `FiniteDimensional ℝ T_0O`.
- "in good position" (Definition 3.21): my own `IsGoodPositionB` — `N ∩ C` has nonempty interior
  in `N` and `N` has a good complement `Y` which is an sc-complement (`E.IsScSplitting N Y`) with
  an `ε > 0` such that `|y|₀ ≤ ε|n|₀` implies `n ∈ C ↔ n + y ∈ C`.  (The project's
  `IsInGoodPosition` only asks an algebraic complement; I wanted the text's sc-complement.)
- Nothing looks false to me.
-/
namespace RoundTrip.V4_27
open Polyfold

/-- `T_0O = Dr(0)E`, the range of the derivative of a retraction at `0`. -/
noncomputable def tangentAtZero {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) :
    Submodule ℝ (E.lvl 0) :=
  LinearMap.range (scDeriv R.U R.toFun 0 : E.lvl 0 →ₗ[ℝ] E.lvl 0)

/-- Definition 3.21 with an sc-complement: `N ∩ C` has nonempty interior in `N`, and `N` has an
sc-complement `Y` with `n ∈ C ↔ n + y ∈ C` whenever `|y|₀ ≤ ε|n|₀`. -/
def IsGoodPositionB (E : ScBanach) (C : Set (E.lvl 0)) (N : Submodule ℝ (E.lvl 0)) : Prop :=
  (interior ((Subtype.val : N → E.lvl 0) ⁻¹' C)).Nonempty ∧
    ∃ Y : Submodule ℝ (E.lvl 0), E.IsScSplitting N Y ∧
      ∃ ε > (0 : ℝ), ∀ n ∈ N, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + y ∈ C)

/-- Theorem 4.2, (i) ⇒ (ii): a tame M-polyfold with a compatible structure of a smooth manifold
with boundary with corners has `X_0 = X_∞`, sc-smooth `1_0^1 : X → X^1`, and every point is the
centre of a tame chart whose tangent space at `0` is finite-dimensional and in good position. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
    P.IsTame → P.HasCornerStructure →
      P.smoothSet = Set.univ ∧
      (∀ x₀ : P.Level 1, P.IsScSmoothMap P.shift (P.toLevelOne x₀)) ∧
      ∀ x : X, ∃ ψ : MChart X,
        P.IsChart ψ ∧ IsTameRetract ψ.model.E ψ.model.C ψ.model.O ∧
        x ∈ ψ.source ∧ ψ.toPartialEquiv x = 0 ∧
        ∀ R : ScRetraction ψ.model.E ψ.model.C, R.retract = ψ.model.O →
          FiniteDimensional ℝ (tangentAtZero R) ∧
          IsGoodPositionB ψ.model.E ψ.model.C (tangentAtZero R)

end RoundTrip.V4_27
