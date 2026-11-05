import Polyfold
/-! Blind formalization of V2_35 (the text's §2.3, Proposition 2.30, p. 35).

Text: if `f : (O, x) → (O', f(x))` is a germ of sc-diffeomorphism between retracts, `x ∈ O_∞`,
then `Tf(x)T^R_xO = T^R_yO'` and `Tf(x)C_xO = C_yO'`, `y = f(x)`.

Choices:
- Setting: `E, E' : ScBanach` (levels in `Type`, forced by `ScBanach`), `(O, C, E)` and
  `(O', C', E')` sc-smooth retracts (`IsScRetract`, checked with `#print`).  "`x ∈ O_∞`":
  `x ∈ O ∩ E_∞`; `x₁ ∈ E₁`, `y₁ ∈ E'₁` are the level-1 lifts of `x` and `y = f(x)` (the project
  indexes tangent data by level-1 points; `y` is smooth since `f` is sc-smooth, and the lift is
  unique, so I quantify over it).
- "Germ of sc-diffeomorphism `f : (O, x) → (O', f(x))`" (my `IsGermDiffeoB`): open sets
  `V ∋ x` of `E₀` and `V' ∋ f(x)` of `E'₀` (so `O ∩ V`, `O' ∩ V'` are open neighbourhoods of `x`,
  `f(x)` in `O`, `O'`), `f` sc-smooth between the retracts `(O ∩ V, C, E)` and `(O' ∩ V', C', E')`
  with an sc-smooth inverse `g` (inverse on `O ∩ V` and `O' ∩ V'`).  "sc-smooth between
  retracts" is the project's `IsScSmoothRetractMap` (Definition 2.7, checked with `#print`:
  `f(O) ⊆ O'` and `f ∘ r` sc-smooth on `U` for every retraction `r : U → U` onto `O`; not vacuous
  here since `O ∩ V` is a retract by Proposition 2.10).  `f`, `g` are total functions; only their
  values on `O ∩ V`, `O' ∩ V'` matter.
- `Tf(x) : T_xO → T_yO'` (Definition 2.7) is `D(f ∘ r)(x)` for a retraction `r` onto `O ∩ V` (the
  domain of the representative `f`), i.e. `scDeriv RV.U (f ∘ RV.toFun) x₁`; on `T_xO` it does not
  depend on `r`, so the claims are made for EVERY retraction `RV` onto `O ∩ V`.
- `T^R_xO = T_xO ∩ E_x` and `C_xO = T_xO ∩ C_x` (Definition 2.27) are the project's
  `reducedTangentSpaceWith R T x₁` and `partialConeWith R T x₁` (checked with `#print`:
  `range Dr(x) ∩ {v | (Tv)_i = 0 for i ∈ I(x)}` and `range Dr(x) ∩ {v | (Tv)_i ≥ 0 for
  i ∈ I(x)}`, `I(x) = {i | (Tx)_i = 0}`), computed with a retraction `R` onto `O` (resp. `R'` onto
  `O'`) and a presentation `T : E ≅ ℝⁿ ⊕ W` of `C` (resp. `T'` of `C'`).  They depend on neither
  choice, so the claims are made for EVERY `R, R', T, T'`.
- "`Tf(x)A = B`" is the set equality `Tf(x) '' A = B`.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_35
open Polyfold

/-- A germ of sc-diffeomorphisms `f : (O, x) → (O', f(x))` between the retracts `(O, C, E)` and
`(O', C', E')`, represented on the open neighbourhoods `O ∩ V` of `x` and `O' ∩ V'` of `f(x)`,
with sc-smooth inverse `g`. -/
def IsGermDiffeoB {E E' : ScBanach} (C O : Set (E.lvl 0)) (C' O' : Set (E'.lvl 0))
    (x : E.lvl 0) (f : E.lvl 0 → E'.lvl 0) (g : E'.lvl 0 → E.lvl 0)
    (V : Set (E.lvl 0)) (V' : Set (E'.lvl 0)) : Prop :=
  IsOpen V ∧ IsOpen V' ∧ x ∈ V ∧ f x ∈ V' ∧
    IsScSmoothRetractMap E C (O ∩ V) E' C' (O' ∩ V') f ∧
    IsScSmoothRetractMap E' C' (O' ∩ V') E C (O ∩ V) g ∧
    (∀ z ∈ O ∩ V, g (f z) = z) ∧ (∀ z ∈ O' ∩ V', f (g z) = z)

/-- Proposition 2.30: the linearization at a smooth point of a germ of sc-diffeomorphisms
between retracts maps `T^R_xO` onto `T^R_yO'` and `C_xO` onto `C_yO'`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C O : Set (E.lvl 0)), IsScRetract E C O →
  ∀ (E' : ScBanach) (C' O' : Set (E'.lvl 0)), IsScRetract E' C' O' →
  ∀ x ∈ O, x ∈ E.smooth →
  ∀ (f : E.lvl 0 → E'.lvl 0) (g : E'.lvl 0 → E.lvl 0) (V : Set (E.lvl 0)) (V' : Set (E'.lvl 0)),
    IsGermDiffeoB C O C' O' x f g V V' →
  ∀ (x₁ : E.lvl 1), E.toBase 1 x₁ = x →
  ∀ (y₁ : E'.lvl 1), E'.toBase 1 y₁ = f x →
  ∀ (R : ScRetraction E C), R.retract = O →
  ∀ (R' : ScRetraction E' C'), R'.retract = O' →
  ∀ (RV : ScRetraction E C), RV.retract = O ∩ V →
  ∀ (n : ℕ) (W : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)),
    C = T.lvl 0 ⁻¹' quadrant n W 0 →
  ∀ (n' : ℕ) (W' : ScBanach) (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W')),
    C' = T'.lvl 0 ⁻¹' quadrant n' W' 0 →
      -- `Tf(x) T^R_xO = T^R_yO'`
      (scDeriv RV.U (f ∘ RV.toFun) x₁ '' (↑(reducedTangentSpaceWith R T x₁) : Set (E.lvl 0)) =
        (↑(reducedTangentSpaceWith R' T' y₁) : Set (E'.lvl 0))) ∧
      -- `Tf(x) C_xO = C_yO'`
      (scDeriv RV.U (f ∘ RV.toFun) x₁ '' partialConeWith R T x₁ = partialConeWith R' T' y₁)

end RoundTrip.V2_35
