import Polyfold
/-! Blind formalization of V2_21 (the text's §2.2, after Proposition 2.19, p. 27).

Text: `Tφ : TV → TO` is a homeomorphism; `Tφ' ∘ (Tφ)⁻¹ = T(φ' ∘ φ⁻¹)` (formula (5)) is
sc-smooth; the charts `(TV, Tφ, (TO, TC, TE))` form an atlas, `TX` is an M-polyfold, and
`p : TX → X_1` is an sc-smooth M-polyfold bundle.

Choices:
- Setting: `X : Type` (spaces in `Type`; the project's `MPolyfold` is universe-polymorphic, this
  is `u = 0`; `TX` lives in `Type 1`) with `[TopologicalSpace X] [T2Space X] [ParacompactSpace X]`,
  `P : MPolyfold X` (Definition 2.13).  Charts of `X`: `MChart X` with `P.IsChart φ` (maximal
  atlas, checked with `#print`); `V = φ.source`, `(O, C, E) = φ.model`.
- `TX` is the project's `P.TangentSpace`, `TV`, `Tφ` (`TVB`, `TφB`), the family `𝓑` (`TfamB`) and
  the topology `τB P = generateFrom 𝓑` on `TX` are as in my `RoundTrip/Blind/V2_19.lean` and
  `V2_20.lean` (`Tφ[(x, φ, h)] = (φ(x), h)` with a chosen representative in the chart `φ`, junk
  `0` off `TV`).  I do not use the project's topology instance on `TX`.
- `(TO, TC, TE)` (Definition 2.5): `TE = E¹ ⊕ E` (`TEB`), `TC = C¹ ⊕ E` (`TCB`), `TO = TOB R`
  for a retraction `R` onto `O` (`{(r(x), Dr(x)h)}`, as in `RoundTrip/Blind/V2_4.lean`); as `TO`
  does not depend on `R`, claims are made for EVERY retraction onto `O`.
- "`Tφ` is a homeomorphism" and "the charts `(TV, Tφ, (TO, TC, TE))`": each is a chart on `TX`
  in the sense of Definition 2.11 (`IsChartB`, as in `RoundTrip/Blind/V2_16.lean`): `TV` open,
  `(TO, TC, TE)` an sc-smooth retract (`IsScRetract`), and `Tφ` restricts to a homeomorphism
  `TV ≃ TO`.
- Formula (5): for charts `φ, φ'` of `X`, `A = φ(V ∩ V')`, `A' = φ'(V ∩ V')` and retractions `R`,
  `R'` onto them: `Tφ(TV ∩ TV') = TA` (the domain of `T(φ' ∘ φ⁻¹)`), and on `TV ∩ TV'`,
  `Tφ' = T(φ' ∘ φ⁻¹) ∘ Tφ`, where `T(φ' ∘ φ⁻¹) := T((φ' ∘ φ⁻¹) ∘ r)` (Definition 2.7; the
  project's `tangentMap` of Definition 1.14, `(a, h) ↦ (g(a), Dg(a)h)`).  "is sc-smooth": this map
  is sc-smooth from `(TA, TC, TE)` to `(TA', TC', TE')` (Definition 2.7, existential reading
  `IsScSmoothRetractMapB`).
- "form an atlas" (Definition 2.12): the tangent charts are pairwise compatible (`CompatibleB`,
  Definition 2.11, as in V2_16) and cover `TX`.  "`TX` is an M-polyfold" (Definition 2.13): in
  addition `τB P` is Hausdorff and paracompact (also Proposition 2.19, V2_20).
- "`p : TX → X_1` is an sc-smooth M-polyfold bundle" (my reading, the text gives no further
  definition here): `X^1` carries the level-1 charts `(V_1, φ_1, (O_1, C_1, E^1))` of
  `RoundTrip/Blind/V2_16.lean` (`E^1` = `E.shiftAdd 1`, `φ_1(x)` = `φ(x)` seen in `E_1`); over
  each chart, `Tφ` covers `φ_1` (first component of `Tφ α` is `φ_1(p α)`, and `TV = p⁻¹(V_1)` by
  definition), so the representative `φ_1 ∘ p ∘ (Tφ)⁻¹` of `p` is the projection `(a, h) ↦ a`,
  which is sc-smooth from `(TO, TC, TE)` to `(O_1, C_1, E^1)`.  This gives `p` sc-smooth in the
  sense of Definition 2.14 (with the generating atlases), and the bundle structure: fibres
  `T_xX` are vector spaces (V2_19) and, by formula (5), the transition maps are
  `(a, h) ↦ ((φ' ∘ φ⁻¹)(a), D(φ' ∘ φ⁻¹)(a)h)`, linear in `h`.  `p` is the project's
  `P.tangentProj` (V2_19 asserts `p[(x, φ, h)] = x`).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_21
open Polyfold

/-- `TE = E¹ ⊕ E`. -/
noncomputable abbrev TEB (E : ScBanach) : ScBanach := E.shift.prod E

/-- `TC = C¹ ⊕ E ⊆ (TE)₀ = E₁ × E₀`. -/
def TCB (E : ScBanach) (C : Set (E.lvl 0)) : Set ((TEB E).lvl 0) :=
  {p | E.toBase 1 p.1 ∈ C}

/-- `TO = {(r(x), Dr(x)h) : x ∈ U₁, h ∈ E}`, computed with the retraction `R` (Definition 2.5). -/
def TOB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) : Set ((TEB E).lvl 0) :=
  {p | ∃ x₁ : E.lvl 1, E.toBase 1 x₁ ∈ R.U ∧ ∃ h : E.lvl 0,
    E.toBase 1 p.1 = R.toFun (E.toBase 1 x₁) ∧ p.2 = scDeriv R.U R.toFun x₁ h}

/-- **Definition 2.7**: `f : O → O'` is sc-smooth between the retracts `(O, C, E)` and
`(O', C', E')`: `f(O) ⊆ O'` and `f ∘ r` is sc-smooth for a retraction `r` onto `O`. -/
def IsScSmoothRetractMapB (E : ScBanach) (C O : Set (E.lvl 0)) (E' : ScBanach)
    (O' : Set (E'.lvl 0)) (f : E.lvl 0 → E'.lvl 0) : Prop :=
  Set.MapsTo f O O' ∧ ∃ R : ScRetraction E C, R.retract = O ∧ IsScSmooth R.U (f ∘ R.toFun)

section
universe u
variable {Y : Type u}

/-- **Definition 2.11**: `(V, φ, (O, C, E))` is a chart on the space `Y`: `V` open, `(O, C, E)`
an sc-smooth retract, `φ : V → O` a homeomorphism. -/
def IsChartB [TopologicalSpace Y] (V : Set Y) (E : ScBanach) (C O : Set (E.lvl 0))
    (φ : Y → E.lvl 0) : Prop :=
  IsOpen V ∧ IsScRetract E C O ∧ ∃ e : V ≃ₜ O, ∀ y : V, (e y : E.lvl 0) = φ y

open Classical in
/-- The transition map `ψ ∘ φ⁻¹`, as a total map (junk `0` off `φ(V)`). -/
noncomputable def transB (V : Set Y) {E E' : ScBanach} (φ : Y → E.lvl 0) (ψ : Y → E'.lvl 0) :
    E.lvl 0 → E'.lvl 0 :=
  fun z => if h : ∃ y ∈ V, φ y = z then ψ h.choose else 0

/-- **Definition 2.11**: the charts `(V, φ, (O, C, E))` and `(V', ψ, (O', C', E'))` are
sc-smoothly compatible. -/
def CompatibleB (V : Set Y) (E : ScBanach) (C : Set (E.lvl 0)) (φ : Y → E.lvl 0)
    (V' : Set Y) (E' : ScBanach) (C' : Set (E'.lvl 0)) (ψ : Y → E'.lvl 0) : Prop :=
  IsScSmoothRetractMapB E C (φ '' (V ∩ V')) E' (ψ '' (V ∩ V')) (transB V φ ψ) ∧
  IsScSmoothRetractMapB E' C' (ψ '' (V ∩ V')) E (φ '' (V ∩ V')) (transB V' ψ φ)

end

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- `TV`: the classes `[(x, ψ, h)]` with `x ∈ V`, `V` the domain of `φ`. -/
def TVB (P : MPolyfold X) (φ : MChart X) : Set P.TangentSpace :=
  {α | ∃ p : P.TangentPre, MPolyfold.TangentSpace.mk p = α ∧ p.x ∈ φ.source}

/-- The vector `(φ(x), h) ∈ TE₀` of a tuple `(x, φ, h)`, `φ(x)` seen in `E_1`. -/
noncomputable def vecB {P : MPolyfold X} (p : P.TangentPre) : (TEB p.φ.model.E).lvl 0 :=
  (Function.invFun (p.φ.model.E.toBase 1) (p.φ.toPartialEquiv p.x), p.h)

open Classical in
/-- `Tφ : TV → TO`, `[(x, φ, h)] ↦ (φ(x), h)`, computed with a chosen representative in the
chart `φ` (junk `0` when there is none). -/
noncomputable def TφB (P : MPolyfold X) (φ : MChart X) (α : P.TangentSpace) :
    (TEB φ.model.E).lvl 0 :=
  if h : ∃ p : P.TangentPre, p.φ = φ ∧ MPolyfold.TangentSpace.mk p = α then
    cast (congrArg (fun c : MChart X => (TEB c.model.E).lvl 0) h.choose_spec.1) (vecB h.choose)
  else 0

/-- The family `𝓑` of the sets `(Tφ)⁻¹(W)`, `φ` a chart of `X`, `W` open. -/
def TfamB (P : MPolyfold X) : Set (Set P.TangentSpace) :=
  {s | ∃ φ : MChart X, P.IsChart φ ∧ ∃ W : Set ((TEB φ.model.E).lvl 0), IsOpen W ∧
    s = {α | α ∈ TVB P φ ∧ TφB P φ α ∈ W}}

/-- The topology on `TX` generated by `𝓑`. -/
@[instance_reducible] def τB (P : MPolyfold X) : TopologicalSpace P.TangentSpace :=
  TopologicalSpace.generateFrom (TfamB P)

/-- The transition `φ' ∘ φ⁻¹` of two charts of `X`, as a total map. -/
def chartTransB (φ φ' : MChart X) : φ.model.E.lvl 0 → φ'.model.E.lvl 0 :=
  (φ'.toPartialEquiv : X → φ'.model.E.lvl 0) ∘ φ.symm

end

/-- `TX` is an M-polyfold with the charts `(TV, Tφ, (TO, TC, TE))`, whose transitions are the
tangent maps `T(φ' ∘ φ⁻¹)`, and `p : TX → X^1` is an sc-smooth bundle. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
    -- `(TV, Tφ, (TO, TC, TE))` is a chart on `TX`: `Tφ : TV → TO` is a homeomorphism
    (∀ φ : MChart X, P.IsChart φ → ∀ R : ScRetraction φ.model.E φ.model.C,
      R.retract = φ.model.O →
        @IsChartB _ (τB P) (TVB P φ) (TEB φ.model.E) (TCB φ.model.E φ.model.C) (TOB R)
          (TφB P φ)) ∧
    -- formula (5): `Tφ' ∘ (Tφ)⁻¹ = T(φ' ∘ φ⁻¹)` on `Tφ(TV ∩ TV') = T(φ(V ∩ V'))`, sc-smooth
    (∀ φ φ' : MChart X, P.IsChart φ → P.IsChart φ' →
      ∀ R : ScRetraction φ.model.E φ.model.C,
        R.retract = φ.toPartialEquiv '' (φ.source ∩ φ'.source) →
      ∀ R' : ScRetraction φ'.model.E φ'.model.C,
        R'.retract = φ'.toPartialEquiv '' (φ.source ∩ φ'.source) →
        TφB P φ '' (TVB P φ ∩ TVB P φ') = TOB R ∧
        (∀ α ∈ TVB P φ ∩ TVB P φ',
          TφB P φ' α = tangentMap R.U (chartTransB φ φ' ∘ R.toFun) (TφB P φ α)) ∧
        IsScSmoothRetractMapB (TEB φ.model.E) (TCB φ.model.E φ.model.C) (TOB R)
          (TEB φ'.model.E) (TOB R') (tangentMap R.U (chartTransB φ φ' ∘ R.toFun))) ∧
    -- the tangent charts form an atlas: pairwise compatible, covering `TX`
    (∀ φ φ' : MChart X, P.IsChart φ → P.IsChart φ' →
      CompatibleB (TVB P φ) (TEB φ.model.E) (TCB φ.model.E φ.model.C) (TφB P φ)
        (TVB P φ') (TEB φ'.model.E) (TCB φ'.model.E φ'.model.C) (TφB P φ')) ∧
    (∀ α : P.TangentSpace, ∃ φ : MChart X, P.IsChart φ ∧ α ∈ TVB P φ) ∧
    -- `TX` is an M-polyfold: Hausdorff and paracompact
    (@T2Space _ (τB P) ∧ @ParacompactSpace _ (τB P)) ∧
    -- `p : TX → X^1` is an sc-smooth bundle: `Tφ` covers `φ_1`, and `p` is the projection
    -- `(a, h) ↦ a`, sc-smooth `(TO, TC, TE) → (O_1, C_1, E^1)`, in these charts
    (∀ φ : MChart X, P.IsChart φ → ∀ R : ScRetraction φ.model.E φ.model.C,
      R.retract = φ.model.O →
        (∀ α ∈ TVB P φ, φ.model.E.toBase 1 (TφB P φ α).1 =
          φ.toPartialEquiv (P.levelVal 1 (P.tangentProj α))) ∧
        IsScSmoothRetractMapB (TEB φ.model.E) (TCB φ.model.E φ.model.C) (TOB R)
          (φ.model.E.shiftAdd 1) (φ.model.E.lvlSet φ.model.O 1)
          (fun a : (TEB φ.model.E).lvl 0 => (a.1 : (φ.model.E.shiftAdd 1).lvl 0)))

end RoundTrip.V2_21
