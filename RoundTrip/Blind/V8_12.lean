import Polyfold
/-! Blind formalization of V8_12 (the text's Part II, §8.1, Remark 8.1.10 (2017: 8.1), pp. 364 ff.;
2017 pp. 264–265).

Text: (i) a morphism `φ : x → y`, `x ∈ X₁`, has a well-defined linear isomorphism
`Tφ : T_xX → T_yX` (printed `T_yY`), the tangent map of `t ∘ (s|𝐔(φ))⁻¹` at `x`; (ii) `(Tφ, h)` is a
morphism from `h` to `Tφ(h)`, and `(Tψ, h) ∘ (Tφ, l) = (Tψ ∘ Tφ, l) = (T(ψ ∘ φ), l)` for
`h = Tφ(l)`; (iii) `G : (φ, h) ↦ (Tφ, Ts(h))` is compatible with the functorial structures, and
`G : T𝐗 → {(Tφ, a) | φ ∈ 𝐗₁, a ∈ T_{s(φ)}X}` is a bijection; (iv) the right-hand side can be
given an M-polyfold structure making `G` an sc-diffeomorphism; (v) the pairs `(Tφ, a)` can be
identified with the triples `(a, Tφ, b)`, `b = Tφ(a)`; (vi) `Tt(φ) ∘ Ts(φ)⁻¹ : T_xX → T_yX` is the
linearization of `t ∘ (s|𝐔(φ))⁻¹` at `x`, hence `= Tφ`, and `t_T ∘ (s_T|…)⁻¹ = Tφ` is a linear
isomorphism.

Choices:
- Setting: `Obj Mor : Type` (universe 0), Hausdorff paracompact, `X : EpGroupoid Obj Mor` (the
  text's ep-groupoid: `RoundTrip/Blind/V7_3.lean`); tangent spaces (Part I's `TangentSpace`,
  `tangentPolyfold`, `tangentMap`) in `Type 1`; `baseB` = the projection `p` seen in the base,
  `fibreB P x = T_xX`.  `s`, `t`, `ι` sc-smooth is asserted (∃ of the proofs).
- `Tφ` (i): the project's `EpGroupoid.tangentMor φ : TX → TX` (only its values on `T_xX`
  matter).  B (0) anchors it to the text's definition exactly as `RoundTrip/Blind/V7_5.lean` (4)
  does: for every sheet `(𝐔(φ), U(x), U(y))` at `φ ∈ 𝐗₁` (`IsSheetAtB`, copied), on `U(x)` with
  the open-subset M-polyfold structure, `Tφ ∘ Tj = T(t ∘ σ)` on `T_xU(x)` (`TangentIsHatB`,
  copied, `σ = (s|𝐔(φ))⁻¹`, `j` the inclusion).  "Linear isomorphism `T_xX → T_yX`": a bijection
  of the fibres, linear in charts (`ChartIsoB … False`, copied from `V7_5`).  The misprint
  `T_yY` is read `T_yX`.
- To compare maps `T_xX → T_yX` as objects, `TφB φ` is `Tφ` on `T_{s φ}X` and the identity
  elsewhere; a pair `(Tφ, a)` with `a ∈ T_{s φ}X` is encoded as `(TφB φ, a)`, which determines
  `x = p(a)`, the map `Tφ` on `T_xX`, and `y`.  The pairs `(L, a)` form a category with source `a`,
  target `L a`, `(L₂, b) ∘ (L₁, a) = (L₂ ∘ L₁ on T_{p(a)}X, a)` (`pairCompB`, (ii)), units `(id, a)`
  and inverses `(L⁻¹ on T_{p(L a)}X, L a)`.
- (ii) is asserted as `T(ψ ∘ φ) = Tψ ∘ Tφ` on `T_{s φ}X` for composable `ψ, φ ∈ 𝐗₁`.
- (iii) "compatible with the functorial structures": `G` (`GB`) intertwines `s_T`, `t_T`,
  composition (`tCompB`, as in `RoundTrip/Blind/V8_3.lean`), units (characterized by `IsTUnitB`)
  and inverses (`ι_T = Tι`) of `T𝐗` with those of the pair category.
- (iii) the bijection is formalized LITERALLY, with `Tφ` the linear map:
  `Set.BijOn GB univ S`, `S = {(TφB φ, a) | φ ∈ 𝐗₁, p(a) = s(φ)}`.  As I read it this does NOT
  hold in general: for an ep-groupoid with ineffective isotropy (e.g. `X` a point, `𝐗` a group of
  order 2 acting trivially) two morphisms have the same `Tφ`, and `G` is not injective.  It holds
  if `Tφ` in `(Tφ, a)` is read as a label for `φ` (pairs `(φ, a)`), where it is the fibrewise
  bijectivity of `Ts`; I formalize the literal reading as instructed.
- (iv): there are a topology, Hausdorffness, paracompactness and an M-polyfold structure on the
  subtype `S` and a map `G' : T𝐗 → S` lifting `G` that is an sc-diffeomorphism
  (`MPolyfold.IsScDiffeoOn` on `univ`, `univ`); all instances given explicitly (`@`).  Under (iii)
  this is transport of structure.
- (v) is a relabelling `(L, a) ↦ (a, L, L a)`, not formalized.
- (vi): `Tφ(Ts h) = Tt h` for every `h ∈ T_φ𝐗`, plus the presupposition that `Ts : T_φ𝐗 → T_{sφ}X`
  is a bijection (so `Tt(φ) ∘ Ts(φ)⁻¹ = Tφ` on `T_xX`); "linear isomorphism" is (i).  The text's
  `(s_T|T_xX)⁻¹` is read `(s_T|T_φ𝐗)⁻¹`.
-/
namespace RoundTrip.V8_12
open Polyfold

universe u

/-- The base point `p(w) ∈ Z₁ ⊆ Z` of a tangent vector `w ∈ TZ`. -/
def baseB {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
    (w : P.TangentSpace) : Z :=
  P.levelVal 1 (P.tangentProj w)

/-- The tangent space `T_zZ = p⁻¹(z)`. -/
def fibreB {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
    (z : Z) : Set P.TangentSpace :=
  {w | baseB P w = z}

/-- The fibre `T_xU = p⁻¹(x)` of the tangent bundle of an open subset `U ∋ x` (as an
M-polyfold on the subtype), as in `RoundTrip/Blind/V7_5.lean`. -/
def subFibreB {Z : Type} [TopologicalSpace Z] {U : Set Z} [T2Space ↥U] [ParacompactSpace ↥U]
    (P : MPolyfold ↥U) (x : Z) : Set P.TangentSpace :=
  {v | (P.levelVal 1 (P.tangentProj v) : Z) = x}

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- A sheet at `φ`: open `W ∋ φ`, `Ux`, `Uy` with `s : W → Ux` (inverse `σ`) and `t : W → Uy`
(inverse `τ`) sc-diffeomorphisms (as in `RoundTrip/Blind/V7_5.lean`). -/
def IsSheetAtB (X : EpGroupoid Obj Mor) (φ : Mor) (W : Set Mor) (Ux Uy : Set Obj)
    (σ τ : Obj → Mor) : Prop :=
  IsOpen W ∧ IsOpen Ux ∧ IsOpen Uy ∧ φ ∈ W ∧
  X.PMor.IsScDiffeoOn X.PObj X.src σ W Ux ∧ X.PMor.IsScDiffeoOn X.PObj X.tgt τ W Uy

/-- `Tφ = T(t ∘ (s|𝐔(φ))⁻¹)(x)` on `T_xX` (as in `RoundTrip/Blind/V7_5.lean`). -/
def TangentIsHatB (X : EpGroupoid Obj Mor) (φ : Mor) (Ux : Set Obj) (hUx : IsOpen Ux)
    (σ : Obj → Mor) [Nonempty ↥Ux] [ParacompactSpace ↥Ux] : Prop :=
  ∃ (hj : (X.PObj.restrictOpen hUx).IsScSmoothMap X.PObj (fun z : ↥Ux => z.1))
    (hφ : (X.PObj.restrictOpen hUx).IsScSmoothMap X.PObj (fun z : ↥Ux => X.tgt (σ z.1))),
    Set.SurjOn (MPolyfold.tangentMap hj) (subFibreB (X.PObj.restrictOpen hUx) (X.src φ))
      (fibreB X.PObj (X.src φ)) ∧
    ∀ v ∈ subFibreB (X.PObj.restrictOpen hUx) (X.src φ),
      X.tangentMor φ (MPolyfold.tangentMap hj v) = MPolyfold.tangentMap hφ v

/-- In the charts `φ₁` around `x` and `ψ₁` around `y`, `Tφ` is `h ↦ (q, A h)` on `T_pO` for a
continuous linear `A` mapping `T_pO` bijectively onto `T_qO'` with continuous linear inverse `A'`
there (as in `RoundTrip/Blind/V7_5.lean`). -/
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

open Classical in
/-- (8.5): `k ∘ h = Ts(ψ ∘ φ)⁻¹(Ts(φ)(h))`, a vector over `p(k) ∘ p(h)` with `Ts` equal to
`Ts h` (chosen; junk `h` if there is none). -/
noncomputable def tCompB (X : EpGroupoid Obj Mor) (hs : X.PMor.IsScSmoothMap X.PObj X.src)
    (k h : X.PMor.TangentSpace) : X.PMor.TangentSpace :=
  if hex : ∃ v, baseB X.PMor v = X.comp (baseB X.PMor k) (baseB X.PMor h) ∧
      MPolyfold.tangentMap hs v = MPolyfold.tangentMap hs h then hex.choose else h

/-- (8.8): `v` is `1_a = (1_x, Ts(1_x)⁻¹ a)`, `x = p(a)`. -/
def IsTUnitB (X : EpGroupoid Obj Mor) (hs : X.PMor.IsScSmoothMap X.PObj X.src)
    (a : X.PObj.TangentSpace) (v : X.PMor.TangentSpace) : Prop :=
  baseB X.PMor v = X.unit (baseB X.PObj a) ∧ MPolyfold.tangentMap hs v = a

open Classical in
/-- `Tφ : T_{s φ}X → T_{t φ}X` as a map of `TX`: `Tφ` on `T_{s φ}X`, the identity elsewhere. -/
noncomputable def TφB (X : EpGroupoid Obj Mor) (φ : Mor) :
    X.PObj.TangentSpace → X.PObj.TangentSpace :=
  fun c => if baseB X.PObj c = X.src φ then X.tangentMor φ c else c

open Classical in
/-- The composition of pairs `(L₂, b) ∘ (L₁, a) = (L₂ ∘ L₁ on T_{p(a)}X, a)`. -/
noncomputable def pairCompB (X : EpGroupoid Obj Mor)
    (P₂ P₁ : (X.PObj.TangentSpace → X.PObj.TangentSpace) × X.PObj.TangentSpace) :
    (X.PObj.TangentSpace → X.PObj.TangentSpace) × X.PObj.TangentSpace :=
  (fun c => if baseB X.PObj c = baseB X.PObj P₁.2 then P₂.1 (P₁.1 c) else c, P₁.2)

/-- `G(φ, h) = (Tφ, Ts(h))`. -/
noncomputable def GB (X : EpGroupoid Obj Mor) (hs : X.PMor.IsScSmoothMap X.PObj X.src)
    (k : X.PMor.TangentSpace) :
    (X.PObj.TangentSpace → X.PObj.TangentSpace) × X.PObj.TangentSpace :=
  (TφB X (baseB X.PMor k), MPolyfold.tangentMap hs k)

/-- The set `{(Tφ, a) | φ ∈ 𝐗₁, a ∈ T_{s(φ)}X}`. -/
def SB (X : EpGroupoid Obj Mor) :
    Set ((X.PObj.TangentSpace → X.PObj.TangentSpace) × X.PObj.TangentSpace) :=
  {P | ∃ φ ∈ X.PMor.levelSet 1, P.1 = TφB X φ ∧ baseB X.PObj P.2 = X.src φ}

end

/-- Remark 8.1.10: `Tφ` is a well-defined linear isomorphism with `T(ψ ∘ φ) = Tψ ∘ Tφ` and
`Tφ = Tt(φ) ∘ Ts(φ)⁻¹`; `G(φ, h) = (Tφ, Ts h)` is compatible with the structure maps, a
bijection onto the pairs `(Tφ, a)` (literal reading), and an sc-diffeomorphism for some
M-polyfold structure on them. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ∃ (hs : X.PMor.IsScSmoothMap X.PObj X.src) (ht : X.PMor.IsScSmoothMap X.PObj X.tgt)
      (hι : X.PMor.IsScSmoothMap X.PMor X.inv),
      -- (0) `Tφ` is the tangent of `t ∘ (s|𝐔(φ))⁻¹` at `x`, for every sheet
      (∀ φ ∈ X.PMor.levelSet 1,
        ∀ (W : Set Mor) (Ux Uy : Set Obj) (σ τ : Obj → Mor) (hS : IsSheetAtB X φ W Ux Uy σ τ)
          (_ : Nonempty ↥Ux) (_ : ParacompactSpace ↥Ux),
          TangentIsHatB X φ Ux hS.2.1 σ) ∧
      -- (i) `Tφ : T_xX → T_yX` is a linear isomorphism
      (∀ φ ∈ X.PMor.levelSet 1,
        Set.BijOn (X.tangentMor φ) (fibreB X.PObj (X.src φ)) (fibreB X.PObj (X.tgt φ)) ∧
        ∀ (φ₁ ψ₁ : MChart Obj) (h₁ : X.PObj.IsChart φ₁) (h₂ : X.PObj.IsChart ψ₁),
          X.src φ ∈ φ₁.source → X.tgt φ ∈ ψ₁.source →
          ∀ w₀ : X.PObj.TangentSpace, ChartIsoB X φ h₁ h₂ w₀ False) ∧
      -- (ii) `T(ψ ∘ φ) = Tψ ∘ Tφ` on `T_xX`
      (∀ φ ∈ X.PMor.levelSet 1, ∀ ψ ∈ X.PMor.levelSet 1, X.src ψ = X.tgt φ →
        ∀ c ∈ fibreB X.PObj (X.src φ),
          X.tangentMor (X.comp ψ φ) c = X.tangentMor ψ (X.tangentMor φ c)) ∧
      -- (vi) `Ts : T_φ𝐗 → T_xX` is a bijection and `Tt(φ) ∘ Ts(φ)⁻¹ = Tφ`
      (∀ φ ∈ X.PMor.levelSet 1,
        Set.BijOn (MPolyfold.tangentMap hs) (fibreB X.PMor φ) (fibreB X.PObj (X.src φ))) ∧
      (∀ h : X.PMor.TangentSpace,
        X.tangentMor (baseB X.PMor h) (MPolyfold.tangentMap hs h) = MPolyfold.tangentMap ht h) ∧
      -- (iii) `G` is compatible with sources, targets, composition, units and inverses
      (∀ k : X.PMor.TangentSpace, (GB X hs k).2 = MPolyfold.tangentMap hs k) ∧
      (∀ k : X.PMor.TangentSpace, (GB X hs k).1 (GB X hs k).2 = MPolyfold.tangentMap ht k) ∧
      (∀ l k : X.PMor.TangentSpace, MPolyfold.tangentMap hs l = MPolyfold.tangentMap ht k →
        GB X hs (tCompB X hs l k) = pairCompB X (GB X hs l) (GB X hs k)) ∧
      (∀ (q : X.PObj.TangentSpace) (v : X.PMor.TangentSpace), IsTUnitB X hs q v →
        GB X hs v = (id, q)) ∧
      (∀ k : X.PMor.TangentSpace,
        (GB X hs (MPolyfold.tangentMap hι k)).2 = (GB X hs k).1 (GB X hs k).2 ∧
        (∀ c ∈ fibreB X.PObj (X.src (baseB X.PMor k)),
          (GB X hs (MPolyfold.tangentMap hι k)).1 ((GB X hs k).1 c) = c) ∧
        (∀ d ∈ fibreB X.PObj (X.tgt (baseB X.PMor k)),
          (GB X hs k).1 ((GB X hs (MPolyfold.tangentMap hι k)).1 d) = d)) ∧
      -- (iii) `G : T𝐗 → {(Tφ, a)}` is a bijection (literal reading; see the header)
      Set.BijOn (GB X hs) Set.univ (SB X) ∧
      -- (iv) `{(Tφ, a)}` has an M-polyfold structure making `G` an sc-diffeomorphism
      (∃ (τ : TopologicalSpace ↥(SB X)) (i₂ : @T2Space ↥(SB X) τ)
        (i₃ : @ParacompactSpace ↥(SB X) τ) (R : @MPolyfold ↥(SB X) τ i₂ i₃)
        (G' : X.PMor.TangentSpace → ↥(SB X)) (H : ↥(SB X) → X.PMor.TangentSpace),
        (∀ k : X.PMor.TangentSpace, (G' k).1 = GB X hs k) ∧
        @MPolyfold.IsScDiffeoOn X.PMor.TangentSpace _ _ _ X.PMor.tangentPolyfold ↥(SB X) τ i₂ i₃
          R G' H Set.univ Set.univ)

end RoundTrip.V8_12
