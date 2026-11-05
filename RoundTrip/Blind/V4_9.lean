import Polyfold
/-! Blind formalization of V4_9 (the text's §4.1, Definition 4.4, p. 148).

Text: an sc-smooth retraction `r : U → U` is an sc⁺-retraction if `r(U_m) ⊆ U_{m+1}` for all `m`
and `r : U → U¹` is sc-smooth; on an open `V ⊆ X` (of an M-polyfold `X`), an sc-smooth retraction
`r : V → V` is an sc⁺-retraction if `r : V → V¹` is sc-smooth.

Choices:
- This item is a definition (two of them).  B says that the project's notions are the text's:
  `R.IsScPlus ↔ IsScPlusRetractionB R` and
  `P.IsScPlusRetractionOn r V ↔ IsScPlusRetractionOnB P r V`.
- Setting, first sentence: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C ⊆ E₀`, and an
  sc-smooth retraction `R : ScRetraction E C` (the project's Definition 2.1 structure, audited in
  V2_1: `U` relatively open in the partial quadrant `C`, `r` sc-smooth on `U`, `r(U) ⊆ U`,
  `r ∘ r = r` on `U`).
- "`r(U_m) ⊆ U_{m+1}`": for `x ∈ U ∩ E_m` (given as a level-`m` point `x` with `ι_m x ∈ U`),
  `r(x)` lifts to `E_{m+1}` (it lies in `U` already, `r(U) ⊆ U`).  The text lists it although it
  follows from the second condition; I kept it.
- "`r : U → U¹` is sc-smooth": `r` takes values in `E₁ = (E¹)₀`, and its lift `g : E₀ → E₁`
  (`ι₁ ∘ g = r` on `U`, values off `U` irrelevant) is sc-smooth on `U` as a map into the shifted
  space `E¹` (`IsScSmooth` with target `E.shift`, Definition 1.15).  I quantify existentially over
  the lift; on `U` it is unique since `ι₁` is injective.  (`U¹` sits in `E¹`, so sc-smooth into
  `U¹` is sc-smooth into `E¹` with values in `U₁`; the values lie in `U` by `r(U) ⊆ U`.)
- Second sentence: `X : Type`, Hausdorff paracompact, `P : MPolyfold X`, `r : X → X` and `V ⊆ X`.
  "sc-smooth retraction `r : V → V` on the open `V`": `V` open, `r` sc-smooth on `V`
  (`P.IsScSmoothOn P r V`, Definition 2.14), `r(V) ⊆ V`, `r ∘ r = r` on `V` (as in Definition
  2.20).  "`r : V → V¹` is sc-smooth": `r(V) ⊆ X₁` (`P.levelSet 1`) and every lift
  `g : X → X₁` of `r` on `V` (`P.levelVal 1 ∘ g = r` on `V`) is sc-smooth on `V` as a map into the
  M-polyfold `X¹` (`P.shift`, the level `X₁` with the charts `(V₁, φ, (O₁, C₁, E¹))`; its
  paracompactness is a project instance found by instance search).  I used "every lift" (rather
  than "some lift") because a function `X → X₁` need not exist when `V = ∅`; for `V ≠ ∅` lifts
  exist and all agree on `V`.  The text does not ask `r(V_m) ⊆ V_{m+1}` here and neither do I.
- Project definitions used: `ScRetraction`, `IsScSmooth`, `ScBanach.shift`, `MPolyfold`,
  `IsScSmoothOn`, `levelSet`, `Level`, `levelVal`, `MPolyfold.shift` (all checked with `#print` or
  their vocab docstrings).  Compared with: `ScRetraction.IsScPlus` (checked: `r(U) ⊆ E₁` and
  `E.liftOne ∘ r` sc-smooth into `E¹`, `liftOne` a junk-valued inverse of `ι₁`) and
  `MPolyfold.IsScPlusRetractionOn` (checked: sc-smooth on `V`, maps `V` to `V`, idempotent,
  `r(V) ⊆ X₁`, and `toLevelOne x₀ ∘ r` sc-smooth on `V` for every junk `x₀`).
- Nothing looks false to me.
-/
namespace RoundTrip.V4_9
open Polyfold

/-- **Definition 4.4** (first sentence): the sc-smooth retraction `r : U → U` is an
**sc⁺-retraction**: `r(U_m) ⊆ U_{m+1}` for every `m`, and `r : U → U¹` is sc-smooth, i.e. a lift
`g : E₀ → E₁` of `r` on `U` is sc-smooth on `U` as a map into `E¹`. -/
def IsScPlusRetractionB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) : Prop :=
  -- `r(U_m) ⊆ U_{m+1}`
  (∀ (m : ℕ) (x : E.lvl m), E.toBase m x ∈ R.U →
      ∃ y : E.lvl (m + 1), E.toBase (m + 1) y = R.toFun (E.toBase m x)) ∧
  -- `r : U → U¹` is sc-smooth
  ∃ g : E.lvl 0 → E.shift.lvl 0,
    (∀ x ∈ R.U, E.toBase 1 (g x) = R.toFun x) ∧ IsScSmooth (E := E) (F := E.shift) R.U g

/-- **Definition 4.4** (second sentence): an sc-smooth retraction `r : V → V` on an open subset
`V` of the M-polyfold `X` is an **sc⁺-retraction** if `r : V → V¹` is sc-smooth. -/
def IsScPlusRetractionOnB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (r : X → X) (V : Set X) : Prop :=
  -- `r : V → V` is an sc-smooth retraction on the open set `V`
  IsOpen V ∧ P.IsScSmoothOn P r V ∧ Set.MapsTo r V V ∧ (∀ x ∈ V, r (r x) = r x) ∧
  -- `r : V → V¹` is sc-smooth
  (∀ x ∈ V, r x ∈ P.levelSet 1) ∧
  ∀ g : X → P.Level 1, (∀ x ∈ V, P.levelVal 1 (g x) = r x) → P.IsScSmoothOn P.shift g V

/-- Definition 4.4: the project's sc⁺-retractions (on relatively open subsets of partial
quadrants, and on open subsets of M-polyfolds) are the text's. -/
def B : Prop :=
  (∀ (E : ScBanach) (C : Set (E.lvl 0)) (R : ScRetraction E C),
    R.IsScPlus ↔ IsScPlusRetractionB R) ∧
  (∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (r : X → X) (V : Set X),
    P.IsScPlusRetractionOn r V ↔ IsScPlusRetractionOnB P r V)

end RoundTrip.V4_9
