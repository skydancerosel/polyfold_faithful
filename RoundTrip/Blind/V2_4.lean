import Polyfold
/-! Blind formalization of V2_4 (the text's §2.1, Definition 2.5, p. 19, and Definition 2.17).

Text: the tangent of `(O, C, E)` is `T(O, C, E) = (TO, TC, TE)` with `TC = C¹ ⊕ E`,
`TE = E¹ ⊕ E` and `TO := Tr(TU)` for any retraction `r` onto `O`; explicitly
`TO = {(r(x), Dr(x)h) : x ∈ U₁, h ∈ E}`.  Definition 2.17: for `x ∈ O₁`, `T_xO = p⁻¹(x)`, the
image of the projection `Dr(x)`.

Choices:
- This item is a definition plus properties.  Setting: `E : ScBanach` (levels in `Type`, forced by
  `ScBanach`), `C O ⊆ E₀` with `(O, C, E)` an sc-smooth retract (presupposed by "the tangent of
  `(O, C, E)`"): the project's `IsScRetract E C O` (checked with `#print`: `O = R.retract` for
  some `R : ScRetraction E C`).  "Retraction `r` onto `O`": `R : ScRetraction E C` with
  `R.retract = O` (checked: `R.retract = R.toFun '' R.U`; `ScRetraction` is Definition 2.1, see
  my `RoundTrip/Blind/V2_1.lean`).
- My definitions: `TEB E = E¹ ⊕ E` is `E.shift.prod E` (levels `E_{m+1} × E_m`; the project's
  `ScBanach.tangent` is this, reducibly).  `TCB E C = C¹ ⊕ E` is the set of `(x, h) ∈ E₁ × E₀`
  with `x ∈ C`.  `TOB R` is the explicit set `{(r(x), Dr(x)h) : x ∈ U₁, h ∈ E₀}` (`r(x)` enters
  as the level-1 point `p.1` with `ι₁ p.1 = r(ι₁ x₁)`).  `TxOB R x₁ = p⁻¹(x) = {h | (x, h) ∈ TO}`.
- `Dr(x)` is `scDeriv R.U R.toFun x₁` (the project's chosen derivative family of the `sc¹` map
  `r`; unique for `x ∈ U₁`, `U₁` being of unique differentiability and `E₁` dense in `E₀`), and
  `Tr(TU)` is the project's `R.tangent` (checked: the image of `TU = E.tangentSet R.U` under
  `tangentMap R.U R.toFun`, `Tr(x, h) = (r(x), Dr(x)h)`).
- "`TO := Tr(TU)` for any retraction `r`": B asserts that the project's `retractTangent E C O`
  (Definition 2.5, computed with a chosen retraction) equals `TOB R` for EVERY retraction `R` onto
  `O`, and that `Tr(TU) = TOB R` (the "explicitly").  "`T(O, C, E) = (TO, TC, TE)`": the project's
  `LocalModel.tangent` of `(O, C, E)` has `E`-component `TEB E`, `C`-component `TCB E C` and
  `O`-component `TOB R` for every `R` onto `O` (stated using that the level types of
  `(LocalModel.mk E C O hO).tangent.E` and `TEB E` agree definitionally).
- Definition 2.17: for `x ∈ O₁` (given by its level-1 lift `x₁`), the project's
  `tangentSpace E C O x₁` is `p⁻¹(x)` (`TxOB R x₁`), and `p⁻¹(x)` is the image `Dr(x)(E₀)`, for
  EVERY retraction `R` onto `O`.  That `Dr(x)` is a projection is item V2_1.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_4
open Polyfold

/-- `TE = E¹ ⊕ E`. -/
noncomputable abbrev TEB (E : ScBanach) : ScBanach := E.shift.prod E

/-- `TC = C¹ ⊕ E ⊆ (TE)₀ = E₁ × E₀`. -/
def TCB (E : ScBanach) (C : Set (E.lvl 0)) : Set ((TEB E).lvl 0) :=
  {p | E.toBase 1 p.1 ∈ C}

/-- `TO = {(r(x), Dr(x)h) : x ∈ U₁, h ∈ E}`, computed with the retraction `R`. -/
def TOB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) : Set ((TEB E).lvl 0) :=
  {p | ∃ x₁ : E.lvl 1, E.toBase 1 x₁ ∈ R.U ∧ ∃ h : E.lvl 0,
    E.toBase 1 p.1 = R.toFun (E.toBase 1 x₁) ∧ p.2 = scDeriv R.U R.toFun x₁ h}

/-- `T_xO = p⁻¹(x) = {h | (x, h) ∈ TO}` (Definition 2.17), `x` given by its level-1 point `x₁`. -/
def TxOB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) (x₁ : E.lvl 1) :
    Set (E.lvl 0) :=
  {h | (x₁, h) ∈ TOB R}

/-- Definition 2.5 (`T(O, C, E) = (TO, TC, TE)`, `TO = Tr(TU)` for any retraction `r` onto `O`,
explicitly) and Definition 2.17 (`T_xO = p⁻¹(x) = Dr(x)E`). -/
def B : Prop :=
  ∀ (E : ScBanach) (C O : Set (E.lvl 0)) (hO : IsScRetract E C O),
    -- `TO := Tr(TU)` for any retraction `r` onto `O`, explicitly `{(r(x), Dr(x)h)}`
    (∀ R : ScRetraction E C, R.retract = O →
      retractTangent E C O = TOB R ∧ R.tangent = TOB R) ∧
    -- `T(O, C, E) = (TO, TC, TE)`
    ((LocalModel.mk E C O hO).tangent.E = TEB E ∧
      (LocalModel.mk E C O hO).tangent.C = TCB E C ∧
      ∀ R : ScRetraction E C, R.retract = O → (LocalModel.mk E C O hO).tangent.O = TOB R) ∧
    -- Definition 2.17: `T_xO = p⁻¹(x)`, the image of `Dr(x)`
    (∀ x₁ : E.lvl 1, E.toBase 1 x₁ ∈ O → ∀ R : ScRetraction E C, R.retract = O →
      tangentSpace E C O x₁ = TxOB R x₁ ∧
      TxOB R x₁ = Set.range (scDeriv R.U R.toFun x₁))

end RoundTrip.V2_4
