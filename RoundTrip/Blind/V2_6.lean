import Polyfold
/-! Blind formalization of V2_6 (the text's §2.1, Definition 2.7, pp. 20–21).

Text: `f : O → O'` is *sc-smooth* if `f ∘ r : U → E'` is sc-smooth for a retraction `r` onto `O`;
`Tf := T(f ∘ r)|_{TO}`, which maps `TO` into `TO'` and does not depend on `r`.  For `o ∈ O₁`,
`Tf(o) : T_oO → T_{f(o)}O'` is the linearization.

Choices:
- This item is a definition plus properties.  Setting: `E E' : ScBanach` (levels in `Type`, forced
  by `ScBanach`), sc-smooth retracts `(O, C, E)`, `(O', C', E')` (the project's `IsScRetract`,
  checked with `#print`: `O = R.retract` for some `R : ScRetraction E C`; see my
  `RoundTrip/Blind/V2_2.lean`).  `f : O → O'` is a total map `f : E₀ → E'₀` with `f(O) ⊆ O'`;
  only its values on `O` matter.  "Retraction `r` onto `O`": `R : ScRetraction E C` with
  `R.retract = O` (Definition 2.1, see `RoundTrip/Blind/V2_1.lean`).
- Definition: "`f ∘ r` is sc-smooth for a retraction `r` onto `O`" is read existentially (for SOME
  retraction): `IsScSmoothRetractMapB`, with `IsScSmooth R.U (f ∘ R.toFun)` (Definition 1.15, as a
  map `U → E'`).  B asserts that the project's `IsScSmoothRetractMap` (checked with `#print`:
  `f(O) ⊆ O'` and `f ∘ R` sc-smooth for EVERY `R` onto `O`) is equivalent to it, for retracts.
- `T(f ∘ r)` is the project's `tangentMap R.U (f ∘ R.toFun)` (Definition 1.14:
  `(x, h) ↦ ((f ∘ r)(x), D(f ∘ r)(x)h)` with the chosen derivative family `scDeriv`, canonical on
  `TU`).  `TO` is my explicit `TOB R = {(r(x), Dr(x)h) : x ∈ U₁, h ∈ E}` of Definition 2.5 (see
  `RoundTrip/Blind/V2_4.lean`, which also relates it to the project's `retractTangent`), and
  `T_oO = p⁻¹(o) = {h | (o, h) ∈ TO}` is `TxOB R o₁` (Definition 2.17).  The text's `TO` does not
  depend on `r` (Proposition 2.4), so it is used with whichever retraction is at hand.
- The properties (under "`f` sc-smooth"): (i) `T(f ∘ r) = T(f ∘ r')` on `TO` for ANY two
  retractions `r`, `r'` onto `O`; (ii) `T(f ∘ r)` maps `TO` into `TO'` (for any retractions onto
  `O`, `O'`); (iii) the project's `retractTangentMap E C O f` (its `Tf`, Definition 2.7) agrees
  with `T(f ∘ r)` on `TO`; (iv) "for `o ∈ O₁`, `Tf(o) : T_oO → T_{f(o)}O'` is the linearization":
  for `o ∈ O₁` (level-1 point `o₁`, and `fo₁` the level-1 point over `f(o)`), there is a bounded
  linear `L : E₀ → E'₀` with `Tf(o, h) = (f(o), L h)` and `L h ∈ T_{f(o)}O'` for every
  `h ∈ T_oO`, i.e. `Tf` maps the fibre over `o` linearly into the fibre over `f(o)`.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_6
open Polyfold

/-- `TE = E¹ ⊕ E`. -/
noncomputable abbrev TEB (E : ScBanach) : ScBanach := E.shift.prod E

/-- `TO = {(r(x), Dr(x)h) : x ∈ U₁, h ∈ E}`, computed with the retraction `R` (Definition 2.5). -/
def TOB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) : Set ((TEB E).lvl 0) :=
  {p | ∃ x₁ : E.lvl 1, E.toBase 1 x₁ ∈ R.U ∧ ∃ h : E.lvl 0,
    E.toBase 1 p.1 = R.toFun (E.toBase 1 x₁) ∧ p.2 = scDeriv R.U R.toFun x₁ h}

/-- `T_xO = p⁻¹(x) = {h | (x, h) ∈ TO}` (Definition 2.17), `x` given by its level-1 point `x₁`. -/
def TxOB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) (x₁ : E.lvl 1) :
    Set (E.lvl 0) :=
  {h | (x₁, h) ∈ TOB R}

/-- **Definition 2.7**: `f : O → O'` is sc-smooth between the retracts `(O, C, E)` and
`(O', C', E')`: `f(O) ⊆ O'` and `f ∘ r : U → E'` is sc-smooth for a retraction `r` onto `O`. -/
def IsScSmoothRetractMapB (E : ScBanach) (C O : Set (E.lvl 0)) (E' : ScBanach)
    (O' : Set (E'.lvl 0)) (f : E.lvl 0 → E'.lvl 0) : Prop :=
  Set.MapsTo f O O' ∧ ∃ R : ScRetraction E C, R.retract = O ∧ IsScSmooth R.U (f ∘ R.toFun)

/-- Definition 2.7: sc-smooth maps between retracts; `Tf = T(f ∘ r)|_{TO}` maps `TO` into `TO'`,
does not depend on `r`, and is linear from `T_oO` to `T_{f(o)}O'` on each fibre. -/
def B : Prop :=
  ∀ (E E' : ScBanach) (C O : Set (E.lvl 0)) (C' O' : Set (E'.lvl 0)) (f : E.lvl 0 → E'.lvl 0),
    IsScRetract E C O → IsScRetract E' C' O' →
      -- the definition
      (IsScSmoothRetractMap E C O E' C' O' f ↔ IsScSmoothRetractMapB E C O E' O' f) ∧
      (IsScSmoothRetractMapB E C O E' O' f →
        -- `T(f ∘ r)|_{TO}` does not depend on `r`
        (∀ R R' : ScRetraction E C, R.retract = O → R'.retract = O →
          Set.EqOn (tangentMap R.U (f ∘ R.toFun)) (tangentMap R'.U (f ∘ R'.toFun)) (TOB R)) ∧
        -- `Tf` maps `TO` into `TO'`
        (∀ (R : ScRetraction E C) (R' : ScRetraction E' C'), R.retract = O → R'.retract = O' →
          Set.MapsTo (tangentMap R.U (f ∘ R.toFun)) (TOB R) (TOB R')) ∧
        -- the project's `Tf` is `T(f ∘ r)` on `TO`
        (∀ R : ScRetraction E C, R.retract = O →
          Set.EqOn (retractTangentMap E C O f) (tangentMap R.U (f ∘ R.toFun)) (TOB R)) ∧
        -- `Tf(o) : T_oO → T_{f(o)}O'` is linear, `o ∈ O₁`
        (∀ (R : ScRetraction E C) (R' : ScRetraction E' C'), R.retract = O → R'.retract = O' →
          ∀ (o₁ : E.lvl 1) (fo₁ : E'.lvl 1), E.toBase 1 o₁ ∈ O →
            E'.toBase 1 fo₁ = f (E.toBase 1 o₁) →
            ∃ L : E.lvl 0 →L[ℝ] E'.lvl 0, ∀ h ∈ TxOB R o₁,
              tangentMap R.U (f ∘ R.toFun) (o₁, h) = (fo₁, L h) ∧ L h ∈ TxOB R' fo₁))

end RoundTrip.V2_6
