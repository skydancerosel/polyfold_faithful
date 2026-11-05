import Polyfold
/-! Blind formalization of V2_8 (the text's §2.1, after Theorem 2.8 and Definition 2.9,
pp. 21–22).

Text: `T` is a functor `𝓡 → 𝓡`: `(TO, TC, TE)` is again a retract,
`Tf : (TO, TC, TE) → (TO', TC', TE')`, `Tf(x, h) = (f(x), Df(x)h)`, and `T(g ∘ f) = Tg ∘ Tf`.
If `r` is a retraction, `Tr : TU → TU` is a (bundle) retraction.

Choices:
- Setting: `E E' E'' : ScBanach` (levels in `Type`, forced by `ScBanach`).  `𝓡` is the category of
  sc-smooth retracts `(O, C, E)` (the project's `IsScRetract`, checked with `#print`:
  `O = R.retract` for some `R : ScRetraction E C`; see `RoundTrip/Blind/V2_2.lean`) and sc-smooth
  maps between
  them (Definition 2.7).  Maps are total functions `E₀ → E'₀`; only their values on `O` matter.
  "Retraction onto `O`": `R : ScRetraction E C` with `R.retract = O` (Definition 2.1, see
  `RoundTrip/Blind/V2_1.lean`; checked with `#print`).
- Prelude: `TEB E = E¹ ⊕ E` (`E.shift.prod E`), `TCB E C = C¹ ⊕ E`, `TUB E U = U¹ ⊕ E` (pairs
  `(x, h) ∈ E₁ × E₀` with `x ∈ C`, resp. `x ∈ U`), `TOB R = {(r(x), Dr(x)h) : x ∈ U₁, h ∈ E}`
  (Definition 2.5, as in `RoundTrip/Blind/V2_4.lean`; `Dr` is the project's `scDeriv`, unique on
  `U₁`).  `IsScRetractionB` is Definition 2.1 (as in V2_1) and `IsScSmoothRetractMapB` is
  Definition 2.7 read existentially (`f(O) ⊆ O'` and `f ∘ r` sc-smooth for SOME retraction `r`
  onto `O`, as in `RoundTrip/Blind/V2_6.lean`).
- `Tf` for `f : O → O'` is `T(f ∘ r)` restricted to `TO` (Definition 2.7), with `T(·)` the
  project's `tangentMap` (Definition 1.14, chosen derivative family, canonical on `TU`).  Since the
  text's `TO` and `Tf` do not depend on `r` (Propositions 2.4, 2.6), every claim is asserted for
  EVERY retraction onto each retract involved.
- Hypotheses on `f`, `g` ("sc-smooth") use the existential reading; the conclusion "`Tf` is a
  morphism `(TO, TC, TE) → (TO', TC', TE')`" is asserted in the strong form: `Tf(TO) ⊆ TO'` and
  `Tf ∘ ρ` is sc-smooth for EVERY retraction `ρ` onto `TO` (inside `(TC, TE)`).
- "`T` is a functor": objects go to retracts, morphisms to morphisms, composition is preserved
  (Theorem 2.8, as in `RoundTrip/Blind/V2_7.lean`), and — part of being a functor, though not
  spelled out in the quoted sentence — `T(1_O) = 1_{TO}` on `TO`.
- "`Tf(x, h) = (f(x), Df(x)h)`": for `(x, h) ∈ TO`, the first component of `Tf(x, h)` lies over
  `f(x)` and the second is `D(f ∘ r)(x)h` (the text's `Df(x)` for a map on a retract is
  `D(f ∘ r)(x)`).
- "`Tr : TU → TU` is a (bundle) retraction": `Tr` is an sc-smooth retraction on `TU`, relatively
  open in the partial quadrant `TC` of `TE` (`IsScRetractionB`), and it is a bundle map of the
  trivial bundle `TU = U¹ × E → U¹`: it covers `r` (first component over `r(x)`) and is linear on
  each fibre (`Tr(x, h) = (r(x), L_x h)`, `L_x` bounded linear).  This is my reading of
  "(bundle)".
- Nothing looks false to me.
-/
namespace RoundTrip.V2_8
open Polyfold

/-- `TE = E¹ ⊕ E`. -/
noncomputable abbrev TEB (E : ScBanach) : ScBanach := E.shift.prod E

/-- `TC = C¹ ⊕ E ⊆ (TE)₀ = E₁ × E₀`. -/
def TCB (E : ScBanach) (C : Set (E.lvl 0)) : Set ((TEB E).lvl 0) :=
  {p | E.toBase 1 p.1 ∈ C}

/-- `TU = U¹ ⊕ E ⊆ (TE)₀ = E₁ × E₀`. -/
def TUB (E : ScBanach) (U : Set (E.lvl 0)) : Set ((TEB E).lvl 0) :=
  {p | E.toBase 1 p.1 ∈ U}

/-- `TO = {(r(x), Dr(x)h) : x ∈ U₁, h ∈ E}`, computed with the retraction `R` (Definition 2.5). -/
def TOB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) : Set ((TEB E).lvl 0) :=
  {p | ∃ x₁ : E.lvl 1, E.toBase 1 x₁ ∈ R.U ∧ ∃ h : E.lvl 0,
    E.toBase 1 p.1 = R.toFun (E.toBase 1 x₁) ∧ p.2 = scDeriv R.U R.toFun x₁ h}

/-- **Definition 2.1**: `r : U → U` is an sc-smooth retraction on the relatively open subset `U`
of the partial quadrant `C ⊆ E`. -/
def IsScRetractionB (E : ScBanach) (C U : Set (E.lvl 0)) (r : E.lvl 0 → E.lvl 0) : Prop :=
  IsRelOpenInQuadrant E C U ∧ Set.MapsTo r U U ∧ IsScSmooth U r ∧ ∀ x ∈ U, r (r x) = r x

/-- **Definition 2.7**: `f : O → O'` is sc-smooth between the retracts `(O, C, E)` and
`(O', C', E')`: `f(O) ⊆ O'` and `f ∘ r` is sc-smooth for a retraction `r` onto `O`. -/
def IsScSmoothRetractMapB (E : ScBanach) (C O : Set (E.lvl 0)) (E' : ScBanach)
    (O' : Set (E'.lvl 0)) (f : E.lvl 0 → E'.lvl 0) : Prop :=
  Set.MapsTo f O O' ∧ ∃ R : ScRetraction E C, R.retract = O ∧ IsScSmooth R.U (f ∘ R.toFun)

/-- The tangent functor on retracts: `T(O, C, E)` is a retract, `Tf` is sc-smooth between tangent
retracts with `Tf(x, h) = (f(x), Df(x)h)`, `T(g ∘ f) = Tg ∘ Tf`, `T(1) = 1`; and `Tr` is a bundle
retraction. -/
def B : Prop :=
  -- `(TO, TC, TE)` is a retract
  (∀ (E : ScBanach) (C O : Set (E.lvl 0)), IsScRetract E C O →
    ∀ R : ScRetraction E C, R.retract = O → IsScRetract (TEB E) (TCB E C) (TOB R)) ∧
  -- `Tf : (TO, TC, TE) → (TO', TC', TE')` is a morphism, and `Tf(x, h) = (f(x), Df(x)h)`
  (∀ (E E' : ScBanach) (C O : Set (E.lvl 0)) (C' O' : Set (E'.lvl 0)) (f : E.lvl 0 → E'.lvl 0),
    IsScRetract E C O → IsScRetract E' C' O' → IsScSmoothRetractMapB E C O E' O' f →
    ∀ (R : ScRetraction E C) (R' : ScRetraction E' C'), R.retract = O → R'.retract = O' →
      (Set.MapsTo (tangentMap R.U (f ∘ R.toFun)) (TOB R) (TOB R') ∧
        ∀ ρ : ScRetraction (TEB E) (TCB E C), ρ.retract = TOB R →
          IsScSmooth ρ.U (tangentMap R.U (f ∘ R.toFun) ∘ ρ.toFun)) ∧
      (∀ p ∈ TOB R,
        E'.toBase 1 (tangentMap R.U (f ∘ R.toFun) p).1 = f (E.toBase 1 p.1) ∧
        (tangentMap R.U (f ∘ R.toFun) p).2 = scDeriv R.U (f ∘ R.toFun) p.1 p.2)) ∧
  -- `T(g ∘ f) = Tg ∘ Tf`
  (∀ (E E' E'' : ScBanach) (C O : Set (E.lvl 0)) (C' O' : Set (E'.lvl 0))
    (C'' O'' : Set (E''.lvl 0)) (f : E.lvl 0 → E'.lvl 0) (g : E'.lvl 0 → E''.lvl 0),
    IsScRetract E C O → IsScRetract E' C' O' → IsScRetract E'' C'' O'' →
    IsScSmoothRetractMapB E C O E' O' f → IsScSmoothRetractMapB E' C' O' E'' O'' g →
    ∀ (R : ScRetraction E C) (R' : ScRetraction E' C'), R.retract = O → R'.retract = O' →
      Set.EqOn (tangentMap R.U ((g ∘ f) ∘ R.toFun))
        (tangentMap R'.U (g ∘ R'.toFun) ∘ tangentMap R.U (f ∘ R.toFun)) (TOB R)) ∧
  -- `T(1_O) = 1_{TO}`
  (∀ (E : ScBanach) (C O : Set (E.lvl 0)), IsScRetract E C O →
    ∀ R : ScRetraction E C, R.retract = O →
      Set.EqOn (tangentMap R.U (id ∘ R.toFun)) id (TOB R)) ∧
  -- `Tr : TU → TU` is a (bundle) retraction
  (∀ (E : ScBanach) (C : Set (E.lvl 0)) (R : ScRetraction E C),
    IsScRetractionB (TEB E) (TCB E C) (TUB E R.U) (tangentMap R.U R.toFun) ∧
    ∀ p ∈ TUB E R.U,
      E.toBase 1 (tangentMap R.U R.toFun p).1 = R.toFun (E.toBase 1 p.1) ∧
      ∃ L : E.lvl 0 →L[ℝ] E.lvl 0, ∀ h : E.lvl 0,
        tangentMap R.U R.toFun (p.1, h) = ((tangentMap R.U R.toFun p).1, L h))

end RoundTrip.V2_8
