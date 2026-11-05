import Polyfold
/-! Blind formalization of V3_18 (the text's §3.1, Lemma 3.16, p. 72). Choices:
- Setting: a strong local bundle `K = R(U ◁ F) → O`: `E F : ScBanach` (levels in `Type`, forced by
  `ScBanach`), `C U ⊆ E₀` with `U` relatively open in the partial quadrant `C`
  (`IsRelOpenInQuadrant`), `R : E₀ × F₀ → E₀ × F₀` a strong bundle retraction on `U ◁ F`
  (`IsStrongBundleRetraction`, Definition 2.47; trusted), `R(u, h) = (r(u), ρ(u)h)` with
  `r(u) = (R(u, 0))₁`, `O = r(U)`, `K = R(U × F)`.  Tameness of `R` is not assumed (the quote does not
  ask for it; if the text presupposes it, `B` is stronger).
- `s : O → K` an sc⁺-section: the project's `IsScPlusSection C O K s` (Definition 2.49: `s` takes
  values in `E₀ × F₁`, `(s x)₁ = x` on `O`, sc-smooth as a map into the retract `K[1]`; trusted).
- `s̃(u) = s(r(u))` is read as the text's abuse of notation for principal parts: `s̃(u) = (u, ŝ(r(u)))`
  where `ŝ(p) = (s p)₂ ∈ F₁` (a section of `U ◁ F → U` must lie over `u`).  "`s̃` is an
  sc⁺-section of `U ◁ F → U`": `IsScPlusSection C U (U × F) s̃` (the trivial local strong bundle,
  `R = id`, base `U`).
- (1) `s̃ = s` on `O`.  (2) `R(r(u), s̃(u)) = s(r(u))` for `u ∈ U`, with `s̃(u)` standing for its
  principal part `ŝ(r(u)) ∈ F₁ ⊆ F₀` and both sides in `E₀ × F₀` (the `F₁`-component of `s(r(u))`
  included into `F₀`).  "Extends" is (1).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_18
open Polyfold

/-- Lemma 3.16: for an sc⁺-section `s : O → K` of `K = R(U ◁ F) → O`, `s̃(u) = (u, ŝ(r(u)))` is an
sc⁺-section of `U ◁ F → U` with `s̃ = s` on `O` and `R(r(u), s̃(u)) = s(r(u))`. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0),
    IsRelOpenInQuadrant E C U → IsStrongBundleRetraction U R →
    ∀ s : E.lvl 0 → E.lvl 0 × F.lvl 1,
      IsScPlusSection C ((fun u => (R (u, 0)).1) '' U) (R '' (U ×ˢ Set.univ)) s →
      let r : E.lvl 0 → E.lvl 0 := fun u => (R (u, 0)).1
      let st : E.lvl 0 → E.lvl 0 × F.lvl 1 := fun u => (u, (s (r u)).2)
      IsScPlusSection C U (U ×ˢ Set.univ) st ∧
      (∀ u ∈ r '' U, st u = s u) ∧
      (∀ u ∈ U, R (r u, F.toBase 1 (st u).2) = ((s (r u)).1, F.toBase 1 (s (r u)).2))

end RoundTrip.V3_18
