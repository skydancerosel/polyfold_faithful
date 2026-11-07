import Polyfold
/-! Blind formalization of V7_5 (the text's Part II, §7.1, Definition 7.4 and the paragraph before
it, p. 227 of the 2017 book).

Text: since `s, t` are local sc-diffeomorphisms, every morphism `φ : x → y` of an ep-groupoid has
an extension to a local sc-diffeomorphism `φ̂` with `φ̂(x) = y`: there are open `𝐔(φ) ⊆ 𝐗`,
`U(x), U(y) ⊆ X` with `s : 𝐔(φ) → U(x)` and `t : 𝐔(φ) → U(y)` sc-diffeomorphisms, and
`φ̂ = t ∘ (s|𝐔(φ))⁻¹ : U(x) → U(y)`.  For `φ ∈ 𝐗_∞` there is an associated sc-isomorphism
`Tφ : T_{s(φ)}X → T_{t(φ)}X`, `Tφ := Tφ̂(x)`; `Tφ` can be defined for `φ` on level `≥ 1` and is
then a bounded linear isomorphism on level `0`; only for smooth `φ` is it an sc-operator.
Definition 7.4 names `φ̂` and `Tφ`.

Choices:
- Setting: `Obj Mor : Type` (universe 0), Hausdorff paracompact, `X : EpGroupoid Obj Mor`
  (characterized as the text's ep-groupoid in `RoundTrip/Blind/V7_3.lean`).
- A "sheet at `φ`" (`IsSheetAtB X φ W Ux Uy σ τ`): open `W = 𝐔(φ) ∋ φ`, open `Ux = U(x)`,
  `Uy = U(y)`, with `s : W → Ux` an sc-diffeomorphism with inverse `σ = (s|W)⁻¹` and `t : W → Uy`
  one with inverse `τ` (the project's `MPolyfold.IsScDiffeoOn`, checked with `#print`; see
  `RoundTrip/Blind/V2_28.lean`).  `σ`, `τ` are total maps whose values off `Ux`, `Uy` are
  irrelevant.  `φ̂ = t ∘ σ`.
- B (1) every `φ` has a sheet; (2) for every sheet, `x ∈ U(x)`, `φ̂(x) = y` and `φ̂ : U(x) → U(y)`
  is an sc-diffeomorphism (inverse `s ∘ τ`); the text's `φ̂` depends on the choice of `𝐔(φ)`, so
  this is asserted for every choice.  (3) The project's `EpGroupoid.hat φ` is such a `φ̂`: some
  sheet at `φ` exists on whose `U(x)` it agrees with `t ∘ σ` (I do not assume that the project's
  chosen `sheetAt φ` contains `φ`; (3) asserts what is needed).
- `Tφ`: the project's `EpGroupoid.tangentMor φ : TX → TX` (a total map; only its values on the
  fibre `T_xX` are claimed).  Fibres `T_xX = p⁻¹(x)` of the project's tangent bundle
  `MPolyfold.TangentSpace` (Definition 2.18) are written `fibreB P x`.  (4), literally
  `Tφ = Tφ̂(x)`: for `φ ∈ 𝐗₁` and every sheet, `U(x)` with the M-polyfold structure of an open
  subset (the project's `MPolyfold.restrictOpen`; its instance arguments `Nonempty ↥U(x)`,
  `ParacompactSpace ↥U(x)` are universally quantified, both true) makes `φ̂ : U(x) → X` and the
  inclusion `j : U(x) → X` sc-smooth, and `Tφ (Tj v) = Tφ̂ v` for every `v ∈ T_xU(x)`, where `Tj`
  maps `T_xU(x)` onto `T_xX` (the identification `T_xU(x) = T_xX` the text uses tacitly).
  `MPolyfold.tangentMap` is the project's tangent map of an sc-smooth map (Definition 2.18).
- (5) `Tφ` is a bijection `T_xX → T_yX` for `φ ∈ 𝐗₁`.  (6) "bounded linear isomorphism on level
  `0`", read in charts (the project's tangent spaces have no linear structure of their own): for
  charts `φ₁` of `X` around `x` and `ψ₁` around `y` (the project's `IsChart`, the charts of the
  structure), with `p`, `q` the level-1 lifts of `φ₁(x)`, `ψ₁(y)` (`MPolyfold.levelLift`), the
  chart representation `h ↦ Tψ₁(Tφ(Tφ₁⁻¹(p, h)))` on `T_pO` (`tangentSpace E C O p`) is
  `h ↦ (q, A h)` for a continuous linear `A : E₀ → E'₀` mapping `T_pO` bijectively onto `T_qO'`
  with a continuous linear inverse `A'` there (the project's `tangentChartMap`,
  `tangentChartInv`; the junk argument `w₀` of `tangentChartInv` is used only off `TO`, and is
  universally quantified).  `ChartIsoB … sc` packs this; its flag `sc` (`False` in (6), `True`
  in (7)) switches on the sc-part.  (7) for `φ ∈ 𝐗_∞` the same holds with `A`, `A'` sc-operators
  (`IsScOperator`: level-preserving with continuous level maps), i.e. `Tφ` is an
  sc-isomorphism `T_pO → T_qO'` (restrictions of sc-operators of the ambient spaces; at smooth
  points `T_pO` is sc-complemented, so this is the same as an sc-isomorphism of `T_pO`).
- Not formalized: "only in the case that `φ` is smooth is `Tφ` an sc-operator" (I read it as a
  remark that the sc-property is guaranteed only for smooth `φ`, not as a converse), and "more
  generally `Tφ̂ : TU(s φ) → TU(t φ)`" (the tangent map of the sc-diffeomorphism in (2)).
- Nothing looks false to me.
-/
namespace RoundTrip.V7_5
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- A sheet at `φ`: open `W ∋ φ`, `Ux`, `Uy` with `s : W → Ux` (inverse `σ`) and `t : W → Uy`
(inverse `τ`) sc-diffeomorphisms. -/
def IsSheetAtB (X : EpGroupoid Obj Mor) (φ : Mor) (W : Set Mor) (Ux Uy : Set Obj)
    (σ τ : Obj → Mor) : Prop :=
  IsOpen W ∧ IsOpen Ux ∧ IsOpen Uy ∧ φ ∈ W ∧
  X.PMor.IsScDiffeoOn X.PObj X.src σ W Ux ∧ X.PMor.IsScDiffeoOn X.PObj X.tgt τ W Uy

/-- The fibre `T_xX = p⁻¹(x)` of the tangent bundle. -/
def fibreB {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
    (x : Z) : Set P.TangentSpace :=
  {w | P.levelVal 1 (P.tangentProj w) = x}

/-- The fibre `T_xU = p⁻¹(x)` of the tangent bundle of an open subset `U ∋ x` (as an
M-polyfold on the subtype). -/
def subFibreB {Z : Type} [TopologicalSpace Z] {U : Set Z} [T2Space ↥U] [ParacompactSpace ↥U]
    (P : MPolyfold ↥U) (x : Z) : Set P.TangentSpace :=
  {v | (P.levelVal 1 (P.tangentProj v) : Z) = x}

/-- `Tφ = Tφ̂(x)` on `T_xX`: with `U(x)` the open-subset M-polyfold, `φ̂ = t ∘ σ` and the
inclusion `j` are sc-smooth on `U(x)`, `Tj` maps `T_xU(x)` onto `T_xX`, and `Tφ ∘ Tj = Tφ̂` on
`T_xU(x)`. -/
def TangentIsHatB (X : EpGroupoid Obj Mor) (φ : Mor) (Ux : Set Obj) (hUx : IsOpen Ux)
    (σ : Obj → Mor) [Nonempty ↥Ux] [ParacompactSpace ↥Ux] : Prop :=
  ∃ (hj : (X.PObj.restrictOpen hUx).IsScSmoothMap X.PObj (fun z : ↥Ux => z.1))
    (hφ : (X.PObj.restrictOpen hUx).IsScSmoothMap X.PObj (fun z : ↥Ux => X.tgt (σ z.1))),
    Set.SurjOn (MPolyfold.tangentMap hj) (subFibreB (X.PObj.restrictOpen hUx) (X.src φ))
      (fibreB X.PObj (X.src φ)) ∧
    ∀ v ∈ subFibreB (X.PObj.restrictOpen hUx) (X.src φ),
      X.tangentMor φ (MPolyfold.tangentMap hj v) = MPolyfold.tangentMap hφ v

/-- In the charts `φ₁` around `x` and `ψ₁` around `y`, `Tφ` is `h ↦ (q, A h)` on `T_pO` for a
continuous linear `A` mapping `T_pO` bijectively onto `T_qO'`, with continuous linear inverse `A'`
on `T_qO'`; if `sc` holds, `A` and `A'` are moreover sc-operators. -/
def ChartIsoB (X : EpGroupoid Obj Mor) (φ : Mor) {φ₁ ψ₁ : MChart Obj} (h₁ : X.PObj.IsChart φ₁)
    (h₂ : X.PObj.IsChart ψ₁) (w₀ : X.PObj.TangentSpace) (sc : Prop) : Prop :=
  ∃ (A : φ₁.model.E.lvl 0 →L[ℝ] ψ₁.model.E.lvl 0) (A' : ψ₁.model.E.lvl 0 →L[ℝ] φ₁.model.E.lvl 0),
    (sc → IsScOperator A ∧ IsScOperator A') ∧
    (∀ h ∈ tangentSpace φ₁.model.E φ₁.model.C φ₁.model.O (MPolyfold.levelLift φ₁ 1 (X.src φ)),
      MPolyfold.tangentChartMap h₂
          (X.tangentMor φ
            (MPolyfold.tangentChartInv h₁ w₀
              ((MPolyfold.levelLift φ₁ 1 (X.src φ), h) : φ₁.model.E.tangent.lvl 0))) =
        ((MPolyfold.levelLift ψ₁ 1 (X.tgt φ), A h) : ψ₁.model.E.tangent.lvl 0)) ∧
    Set.MapsTo A
      (tangentSpace φ₁.model.E φ₁.model.C φ₁.model.O (MPolyfold.levelLift φ₁ 1 (X.src φ)))
      (tangentSpace ψ₁.model.E ψ₁.model.C ψ₁.model.O (MPolyfold.levelLift ψ₁ 1 (X.tgt φ))) ∧
    Set.MapsTo A'
      (tangentSpace ψ₁.model.E ψ₁.model.C ψ₁.model.O (MPolyfold.levelLift ψ₁ 1 (X.tgt φ)))
      (tangentSpace φ₁.model.E φ₁.model.C φ₁.model.O (MPolyfold.levelLift φ₁ 1 (X.src φ))) ∧
    Set.LeftInvOn A' A
      (tangentSpace φ₁.model.E φ₁.model.C φ₁.model.O (MPolyfold.levelLift φ₁ 1 (X.src φ))) ∧
    Set.LeftInvOn A A'
      (tangentSpace ψ₁.model.E ψ₁.model.C ψ₁.model.O (MPolyfold.levelLift ψ₁ 1 (X.tgt φ)))

end

/-- Definition 7.4: every morphism has sheets and the sc-diffeomorphism `φ̂ = t ∘ (s|𝐔(φ))⁻¹`
with `φ̂(x) = y`; the project's `hat` is such a `φ̂`; for `φ ∈ 𝐗₁` the project's `tangentMor` is
`Tφ̂(x)`, a bijection `T_xX → T_yX`, in charts a bounded linear isomorphism, an sc-isomorphism for
`φ ∈ 𝐗_∞`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    -- (1) sheets exist at every morphism
    (∀ φ : Mor, ∃ (W : Set Mor) (Ux Uy : Set Obj) (σ τ : Obj → Mor),
      IsSheetAtB X φ W Ux Uy σ τ) ∧
    -- (2) `φ̂ = t ∘ (s|𝐔(φ))⁻¹ : U(x) → U(y)` is an sc-diffeomorphism with `φ̂(x) = y`
    (∀ (φ : Mor) (W : Set Mor) (Ux Uy : Set Obj) (σ τ : Obj → Mor),
      IsSheetAtB X φ W Ux Uy σ τ →
        X.src φ ∈ Ux ∧ X.tgt φ ∈ Uy ∧ X.tgt (σ (X.src φ)) = X.tgt φ ∧
        X.PObj.IsScDiffeoOn X.PObj (fun z => X.tgt (σ z)) (fun z => X.src (τ z)) Ux Uy) ∧
    -- (3) the project's `hat φ` is `t ∘ (s|𝐔(φ))⁻¹` on `U(x)` for a sheet at `φ`
    (∀ φ : Mor, ∃ (W : Set Mor) (Ux Uy : Set Obj) (σ τ : Obj → Mor),
      IsSheetAtB X φ W Ux Uy σ τ ∧ Set.EqOn (X.hat φ) (fun z => X.tgt (σ z)) Ux) ∧
    -- (4) `Tφ = Tφ̂(x)` for `φ` on level `≥ 1`, for every sheet
    (∀ φ : Mor, φ ∈ X.PMor.levelSet 1 →
      ∀ (W : Set Mor) (Ux Uy : Set Obj) (σ τ : Obj → Mor) (hS : IsSheetAtB X φ W Ux Uy σ τ)
        (_ : Nonempty ↥Ux) (_ : ParacompactSpace ↥Ux),
        TangentIsHatB X φ Ux hS.2.1 σ) ∧
    -- (5) `Tφ : T_xX → T_yX` is a bijection
    (∀ φ : Mor, φ ∈ X.PMor.levelSet 1 →
      Set.BijOn (X.tangentMor φ) (fibreB X.PObj (X.src φ)) (fibreB X.PObj (X.tgt φ))) ∧
    -- (6) in charts, a bounded linear isomorphism on level `0`, for `φ` on level `≥ 1`
    (∀ φ : Mor, φ ∈ X.PMor.levelSet 1 →
      ∀ (φ₁ ψ₁ : MChart Obj) (h₁ : X.PObj.IsChart φ₁) (h₂ : X.PObj.IsChart ψ₁),
        X.src φ ∈ φ₁.source → X.tgt φ ∈ ψ₁.source →
        ∀ w₀ : X.PObj.TangentSpace, ChartIsoB X φ h₁ h₂ w₀ False) ∧
    -- (7) for smooth `φ`, an sc-isomorphism
    (∀ φ : Mor, φ ∈ X.PMor.smoothSet →
      ∀ (φ₁ ψ₁ : MChart Obj) (h₁ : X.PObj.IsChart φ₁) (h₂ : X.PObj.IsChart ψ₁),
        X.src φ ∈ φ₁.source → X.tgt φ ∈ ψ₁.source →
        ∀ w₀ : X.PObj.TangentSpace, ChartIsoB X φ h₁ h₂ w₀ True)

end RoundTrip.V7_5
