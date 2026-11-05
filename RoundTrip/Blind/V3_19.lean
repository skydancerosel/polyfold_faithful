import Polyfold
/-! Blind formalization of V3_19 (the text's §3.1, Lemma 3.17, p. 72). Choices:
- Setting: the local situation of Definition 3.4, a *tame* strong local bundle
  `K = R(U ◁ F) → O` with `0 ∈ O`: `E F : ScBanach`, `C U ⊆ E₀` with `U` relatively open in the
  partial quadrant `C`, `R` a strong bundle retraction on `U ◁ F` (`IsStrongBundleRetraction`,
  Definition 2.47; trusted), `R(u, h) = (r(u), ρ(u)h)`, `r(u) = (R(u, 0))₁`, `O = r(U)`,
  `K = R(U × F)`, `0 ∈ U`, `r(0) = 0`.  Tameness (`ScRetraction.IsTame` of the base retraction) is a
  hypothesis because the text defines fillers (Definition 3.4) only for tame strong local bundles;
  the lemma itself presumably does not use it.
- "sc-smooth section `f : O → K`": the project's `IsScSmoothSection C O K f` (Definition 2.49:
  `(f x)₁ = x` on `O`, sc-smooth into the retract `K`; trusted), principal part `f̂ = (f ·)₂`.
- "`f` has the filler `g`": Definition 3.4 as written in my blind file V3_13 (`IsFillingB`, copied
  below): `g` an sc-smooth section germ of `U ◁ F → U` at `0` (Definition 3.2 germ), with
  conditions (1)–(3) near `0` for the principal parts.
- "`s : O → K` an sc⁺-section": the project's `IsScPlusSection C O K s` (Definition 2.49; values in
  `E₀ × F₁`; trusted), principal part `ŝ = (s ·)₂ ∈ F₁`.
- `f + s` is the fibrewise sum, principal part `f̂ + ŝ` (with `F₁ ⊆ F₀`); `s̃` is the extension of
  Lemma 3.16, `s̃(u) = (u, ŝ(r(u)))`, so `g + s̃` has principal part `u ↦ g(u) + ŝ(r(u))`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_19
open Polyfold Filter Topology

/-- **Definitions 3.4/3.6**: `g` is a filling (filled version) of the principal part `f̂` of a
section of `K = R(U ◁ F) → O`, `O = r(U)`, all near `0`. -/
def IsFillingB {E F : ScBanach} (C U : Set (E.lvl 0))
    (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0) (fhat g : E.lvl 0 → F.lvl 0) : Prop :=
  -- `g` is an sc-smooth section germ of `U ◁ F → U`, and condition (3)
  (∃ G : ScNbhdGerm E C, (∀ x ∈ G.U 0, x ∈ U) ∧ IsScSmoothGerm G g ∧
    ∃ Dk : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0,
      IsSc1GermWith G (fun y => g y - (R ((R (y, 0)).1, g y)).2) Dk ∧
    ∃ Dr : E.lvl 1 → E.lvl 0 →L[ℝ] E.lvl 0, IsSc1With U (fun u => (R (u, 0)).1) Dr ∧
      Set.BijOn (Dk 0) {v | Dr 0 v = 0} {h | (R (0, h)).2 = 0} ∧
      ∃ c : ℝ, ∀ v, Dr 0 v = 0 → ‖v‖ ≤ c * ‖Dk 0 v‖) ∧
  -- (1) `f̂ = g` on `O` near `0`
  (∀ᶠ x in 𝓝 (0 : E.lvl 0), x ∈ (fun u => (R (u, 0)).1) '' U → fhat x = g x) ∧
  -- (2) `g(y) = ρ(r(y))g(y)`, `y ∈ U` near `0`, forces `y ∈ O`
  (∀ᶠ y in 𝓝 (0 : E.lvl 0), y ∈ U → g y = (R ((R (y, 0)).1, g y)).2 →
    y ∈ (fun u => (R (u, 0)).1) '' U)

/-- Lemma 3.17: if the sc-smooth section `f` of the tame strong local bundle `K → O` has the filler
`g` and `s` is an sc⁺-section, then `f + s` has the filler `g + s̃`, `s̃(u) = (u, ŝ(r(u)))`. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0)
    (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R),
    (IsStrongBundleRetraction.baseRetraction hU hR).IsTame →
    (0 : E.lvl 0) ∈ U → (R (0, 0)).1 = 0 →
    ∀ (f : E.lvl 0 → E.lvl 0 × F.lvl 0) (s : E.lvl 0 → E.lvl 0 × F.lvl 1)
      (g : E.lvl 0 → F.lvl 0),
      IsScSmoothSection C ((fun u => (R (u, 0)).1) '' U) (R '' (U ×ˢ Set.univ)) f →
      IsScPlusSection C ((fun u => (R (u, 0)).1) '' U) (R '' (U ×ˢ Set.univ)) s →
      IsFillingB C U R (fun x => (f x).2) g →
      IsFillingB C U R (fun x => (f x).2 + F.toBase 1 (s x).2)
        (fun u => g u + F.toBase 1 (s ((R (u, 0)).1)).2)

end RoundTrip.V3_19
