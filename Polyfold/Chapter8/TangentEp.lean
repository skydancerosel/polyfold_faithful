import Polyfold.Chapter8.Basic
import Polyfold.Chapter8.TangentLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 8, §8.1, pp. 257–268: **Theorem 8.1.1 (2017: 8.1)** (without its tameness sentence), **Lemmas
8.1–8.7**, **Remark 8.1.10 (2017: 8.1)**, **Theorem 8.1.11 (2017: 8.2)**, **Theorem 8.1.12 (2017: 8.3)** and **Proposition 8.1.14 (2017: 8.1)**.  There is no
2014 preprint of Part II; numbers and pages are the 2017 text's.  Part I's tangent bundle `TX` and
tangent map `Tf` are `MPolyfold.TangentSpace` and `MPolyfold.tangentMap`; the structure maps
(8.3)–(8.9) are `EpGroupoid.tSrc`, `tTgt`, `tComp`, `tUnit`, `tInv` (`Chapter8/Basic.lean`); the
tangents of maps sc-smooth on open sets are `MPolyfold.tangentMapOn` (`Chapter8/TangentLocal.lean`).

# The tangent of an ep-groupoid

## The text, paraphrased

(pp. 257–258) The tangent of the ep-groupoid `(X, 𝐗)` is `T(X, 𝐗) = (TX, T𝐗)` (8.1).  A vector
`(φ, h) ∈ T_φ𝐗` is a morphism `Ts(φ)(h) → Tt(φ)(h)` (8.2), so `s_T = Ts`, `t_T = Tt` (8.3); for
`Ts(ψ)(k) = Tt(φ)(h)` (8.4), `(ψ, k) ∘ (φ, h) = (ψ ∘ φ, Ts(ψ ∘ φ)⁻¹(Ts(φ)(h)))` (8.5), in short
(8.6) with the projection `p : T𝐗 → 𝐗¹`; the unit of `a ∈ T_xX` is `1_a = (1_x, Ts(1_x)⁻¹(a))`
(8.7), (8.8); the inverse is `ι_T(φ, k) = (φ⁻¹, Tι(φ)(k))` (8.9).  (**Theorem 8.1.1 (2017: 8.1)**) `T(X, 𝐗)` is
an ep-groupoid; if `X` is tame so is `TX`; the projections form an sc-smooth functor
`(p, p) : T(X, 𝐗) → (X, 𝐗)¹`.  With `T(𝐗 ₛ×ₜ 𝐗) = T𝐗 _{Ts}×_{Tt} T𝐗`: (**Lemma 8.1.2 (2017: 8.1)**)
`(ψ, k) ∘ (φ, h) = Tm(ψ, φ)(k, h)`; the proof varies `φ'` near `φ` and `ψ' = F(φ') =
(s|U(ψ))⁻¹(t(φ'))`, and differentiates `s(m(F(φ'), φ')) = s(φ')`.  (**Lemma 8.2**)
`s_T(Ψ ∘ Φ) = s_T(Φ)`, `t_T(Ψ ∘ Φ) = t_T(Ψ)`, the second by differentiating
`α ∘ s = t ∘ (s|U(ψ))⁻¹ ∘ t` near `φ`, `α = t ∘ (s|U(ψ ∘ φ))⁻¹`.  (**Lemma 8.1.4 (2017: 8.3)**) Associativity.
(**Lemma 8.1.5 (2017: 8.4)**) `1_q` is a morphism `q → q` (`t ∘ (s|U(1_x))⁻¹ = id` near `x`) and a two-sided
identity.  (**Lemma 8.1.6 (2017: 8.5)**) `ι_T` is a two-sided inverse (chain rule for `s ∘ ι = t`,
`t ∘ ι = s`).  (**Lemma 8.1.7 (2017: 8.6)**) `s_T`, `t_T` are surjective local sc-diffeomorphisms "by
construction", `u_T`, `ι_T` are sc-smooth, and the multiplication is `Tm`, sc-smooth.
(**Lemma 8.1.8 (2017: 8.7)**) Properness: for `V(x)` as in (3), `t_T : s_T⁻¹(cl TV) → TX` is proper, by a
sequence argument (`φ_k → φ` in `𝐗` by properness of `X`, then in `𝐗¹`, then `(φ_k, h_k)`
converges since `Ts : TU(φ) → TU(x)` is an sc-diffeomorphism).  (**Remark 8.1.10 (2017: 8.1)**) `Tφ`
(Definition 7.1.4 (2017: 7.4)) is `t_T ∘ (s_T|T_xX)⁻¹`; `G : (φ, h) ↦ (Tφ, Ts(h))` identifies `T𝐗` with pairs
`(Tφ, a)`, `a ∈ T_{s(φ)}X`, composed by `(Tψ, h) ∘ (Tφ, l) = (T(ψ ∘ φ), l)`.  (**Theorem 8.1.11 (2017: 8.2)**)
The tangent `(TΦ, T𝚽)` of an sc-smooth functor is an sc-smooth functor `T(X, 𝐗) → T(Y, 𝐘)`
(differentiate `Φ(m(ψ, φ)) = m(Φ ψ, Φ φ)`, `s ∘ 𝚽 = Φ ∘ s`, `t ∘ 𝚽 = Φ ∘ t`).
(**Theorem 8.1.12 (2017: 8.3)**) `T : EP → EP` is a functor, preserving tameness.  (**Proposition 8.1.14 (2017: 8.1)**) For a
natural transformation `τ : Φ → Ψ`, `Tτ : TΦ → TΨ` is a natural transformation (differentiate
`Φ = s ∘ τ`, `Ψ = t ∘ τ` and the naturality square at `α₀ ∈ 𝐗¹`).

## What is formalized (namespace `Polyfold.EpGroupoid` unless noted)

* **Chain rule forms** (namespace `Polyfold.MPolyfold`): `tangentMap_congr_fun`,
  `tangentMap_tangentMap_of_eq`, `tangentMap_tangentMap_of_eq_id`, `tangentMap_tangentMap_comm`,
  `tangentMap_tangentMapOn`, `tangentMapOn_tangentMap`, `tangentMap_tangentMapOn_of_eqOn`.
* **Base points and fibre injectivity**: `levelVal_tangentProj_tSrc`, `levelVal_tangentProj_tTgt`,
  `tBase_tUnit`, `tBase_tInv`, `tBase_tangentMap`, `continuous_tBase`, `continuous_tSrc`,
  `continuous_tTgt`; **`tangent_ext`** (same base point and same `Ts` ⇒ equal),
  `tangent_ext_tgt`, `exists_tSrc_eq`, `exists_tSrc_eq'` (fibre surjectivity of `Ts`).
* **(8.5)**: `src_tBase_eq`, **`tComp_spec`** (`k ∘ h` lies over `p k ∘ p h`, `Ts(k ∘ h) = Ts h`),
  `tBase_tComp`, `tSrc_tComp`, `tComp_eq` (uniqueness).
* **Lemma 8.1.2 (2017: 8.1)** on a sheet `s : W → V` with inverse `σ`: `tangentMapOn_srcInv_tSrc`,
  `mem_tangentPreimage_tgt`, **`tComp_eq_tangentMapOn`** (`k ∘ h = Tg(h)`,
  `g(φ') = m(σ(t φ'), φ')`), `tTgt_tangentMapOn`; `lemma_8_1_2`.
* **Lemmas 8.1.3–8.1.6 (2017: 8.2–8.5)**: `lemma_8_1_3`, `lemma_8_1_4`; `tSrc_tUnit`, `tTgt_tUnit`, `tUnit_eq`,
  `tComp_tUnit`, `tUnit_tComp`, `lemma_8_1_5`; `tSrc_tInv`, `tTgt_tInv`, `tComp_tInv`, `tInv_tComp`,
  `lemma_8_1_6`; the groupoid `tangentGroupoidStr`.
* **Lemma 8.1.7 (2017: 8.6)**: `isLocalScDiffeo_tSrc`, `isLocalScDiffeo_tTgt`, `surjective_tSrc`,
  `surjective_tTgt`, `isScSmoothMap_tUnit`, `isScSmoothMap_tInv`, `isScSmoothCompSheet_tangent`
  (condition (4), sheet form), `isScSmoothComp_tangent` (literally), `lemma_8_1_7`.
* **Lemma 8.1.8 (2017: 8.7)**: `lemma_8_1_8`.
* **Theorem 8.1.1 (2017: 8.1)**: the ep-groupoid **`tangentEpGroupoid : EpGroupoid TX T𝐗`**, the functor
  **`tangentProjFunctor : EpFunctor X.tangentEpGroupoid X.liftOne`** (`(p, p)`, with Chapter 7's
  `X¹ = liftOne`), `theorem_8_1_1`.
* **Remark 8.1.10 (2017: 8.1)**: `tangentMor_tSrc` (`Tφ(Ts h) = Tt h`, Chapter 7's `tangentMor`),
  `tangentMor_comp` (`T(ψ ∘ φ) = Tψ ∘ Tφ`), `remarkG` (`G`), `remark_8_1_10`.
* **Theorem 8.1.11 (2017: 8.2)**: `EpFunctor.tangent`, `EpFunctor.theorem_8_1_11`.
* **Theorem 8.1.12 (2017: 8.3)**: `EP.tangent`, **`tangentFunctor : EP ⥤ EP`**, `theorem_8_1_12`.
* **Proposition 8.1.14 (2017: 8.1)**: `EpNatTrans.tangent`, `proposition_8_1_14`.

## What the text leaves implicit, and the choices made

* **Fibre injectivity in place of differentiating identities.**  `s` is a local
  sc-diffeomorphism, so `Ts` is injective on every fibre `T_φ𝐗` and maps it onto `T_{s φ}X`
  (`IsLocalScDiffeo.bijOn_tangentFiber`).  Two vectors of `T𝐗` are therefore equal as soon as
  they have the same base point and the same `Ts` (`tangent_ext`).  This gives associativity, the
  unit and inverse laws, the functoriality in Theorem 8.1.11 (2017: 8.2) and the naturality in Proposition 8.1.14 (2017: 8.1)
  without differentiating the identities as the text does: the base points are computed in `𝐗`
  and the values of `Ts` by Part I's chain rule (`s ∘ u = id`, `s ∘ ι = t`, `s ∘ 𝚽 = Φ ∘ s`,
  `s ∘ τ = Φ`).  The only genuine differentiation is `t_T(Ψ ∘ Φ) = t_T(Ψ)` (Lemma 8.1.3 (2017: 8.2)), done as in
  the text with maps defined on open sets (`tangentMapOn`): `k ∘ h = Tg(h)` on a sheet and
  `t ∘ g = t ∘ σ ∘ t` on `t⁻¹(V)` (the text's `α ∘ s = t ∘ (s|U(ψ))⁻¹ ∘ t`).  The units are
  `u_T = Tu`, and `Tt(1_q) = q` is the chain rule for `t ∘ u = id` rather than the text's
  `t ∘ (s|U(1_x))⁻¹ = id` near `x`; with `tangent_ext` this is (8.8) (`tUnit_eq`).
* **The sheet form of condition (4)** in place of `T(𝐗 ₛ×ₜ 𝐗) = T𝐗 _{Ts}×_{Tt} T𝐗`.  The
  identification of the tangent of the fibred product with the fibred product of tangents is not
  proved here.  Lemma 8.1.2 (2017: 8.1) is stated in the form the text's proof uses: for a sheet `s : W → V` with
  inverse `σ = (s|U(ψ))⁻¹`, `g(φ') = m(σ(t φ'), φ')` (the text's `m(F(φ'), φ')`) is sc-smooth on
  `t⁻¹(V)` (Chapter 7's `isScSmoothCompSheet`) and `k ∘ h = Tg(h)`.  Lemma 8.1.7 (2017: 8.6)'s (4) is proved in
  Chapter 7's sheet form (`isScSmoothComp_iff_sheet`): near a point, `Ψ ↦ σ_T(t_T Ψ) ∘ Ψ` is `Tg`
  for a sheet of `s`, sc-smooth by `tangentMapOn_isScSmoothOn`.
* **Lemma 8.1.8 (2017: 8.7).**  The text's step "`φ_k → φ` in `𝐗¹`" is not needed: convergence in `𝐗` already
  puts `φ_k` in `U(φ)`, and on `TU(φ) = p⁻¹(U(φ))` the inverse of `Tt` is continuous
  (`IsScDiffeoOn.tangentMap`), so `(φ_k, h_k) = (Tt|TU(φ))⁻¹(t_T(φ_k, h_k))` converges.  `TV` is
  `p⁻¹(V)` and properness is checked by the sequential criterion (`TX`, `T𝐗` are metrizable).
* **Remark 8.1.10 (2017: 8.1).**  `Tφ` is Chapter 7's `tangentMor` (Definition 7.1.4 (2017: 7.4), `Tt ∘ (Ts|T_φ𝐗)⁻¹`); its
  functoriality `T(ψ ∘ φ) = Tψ ∘ Tφ` is `tangentMor_comp`.  In `G(φ, h) = (Tφ, Ts(h))` the first
  entry is read as `Tφ` labelled by `φ` (as a bare map, distinct morphisms with the same `Tφ`,
  e.g. isotropy acting trivially, would make `G` non-injective); `G = remarkG` then is a bijection
  onto `{(φ, a) | φ ∈ 𝐗₁, a ∈ T_{s φ}X}`.  The M-polyfold structure transported along `G` is not
  formalized.  Linearity of `Tφ` is out of scope: Part I's `T_xX` carries no linear structure
  (gap G.7).
* **Universes.**  Part I's `TangentSpace` of `X : Type u` lives in `Type (max u 1)`, so the tangent
  functor is `EP.{max u 1} ⥤ EP.{max u 1}` (Lean identifies `max (max u 1) 1` with `max u 1`).
  This is an artifact of the formalization.
* **Tameness** ("if `X` is tame, then `TX` is tame", Theorem 8.1.1 (2017: 8.1), Theorem 8.1.12 (2017: 8.3), Lemma 8.1.9 (2017: 8.8)) is not
  formalized here; it is proved in `TangentTame.lean` (`lemma_8_1_9`, `theorem_8_1_12_tame`).
* **Possible misprints**, as we read them: (8.5) writes `T_{φ∘ψ}𝐗` for `T_{ψ∘φ}𝐗`; Lemma 8.1.2 (2017: 8.1)'s proof
  writes `s|U(φ ∘ ψ)` for `s|U(ψ ∘ φ)`; Lemma 8.1.3 (2017: 8.2)'s proof has "`= =`", "`t : U(ψ ∘ φ) → U(y)` and
  `: U(ψ ∘ φ) → U(x)`" without `s`, and `T t)φ)(h)`; Lemma 8.1.8 (2017: 8.7)'s proof writes
  `t(φ_k, h_k) = Ts(φ_k)(h_k)` for `Tt(φ_k)(h_k)`; Remark 8.1.10 (2017: 8.1) writes `T_yY` for `T_yX`.
-/

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v w

/-! ### The chain rule in the forms used below -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

/-- Part I's `Tf` depends only on the map `f`. -/
theorem tangentMap_congr_fun {f g : X → Y} (hf : P.IsScSmoothMap Q f) (hg : P.IsScSmoothMap Q g)
    (h : f = g) : tangentMap hf = tangentMap hg := by
  subst h
  rfl

/-- The chain rule in the form `Tg(Tf α) = Th α` for `g ∘ f = h`. -/
theorem tangentMap_tangentMap_of_eq {f : X → Y} {g : Y → Z} {h : X → Z}
    (hg : Q.IsScSmoothMap S g) (hf : P.IsScSmoothMap Q f) (hh : P.IsScSmoothMap S h)
    (heq : g ∘ f = h) (α : P.TangentSpace) :
    tangentMap hg (tangentMap hf α) = tangentMap hh α := by
  rw [← Function.comp_apply (f := tangentMap hg), ← tangentMap_comp,
    tangentMap_congr_fun _ hh heq]

/-- The chain rule in the form `Tg(Tf α) = α` for `g ∘ f = id`. -/
theorem tangentMap_tangentMap_of_eq_id {f : X → Y} {g : Y → X} (hg : Q.IsScSmoothMap P g)
    (hf : P.IsScSmoothMap Q f) (heq : g ∘ f = id) (α : P.TangentSpace) :
    tangentMap hg (tangentMap hf α) = α := by
  rw [tangentMap_tangentMap_of_eq hg hf isScSmoothMap_id heq, tangentMap_id, id]

/-- The chain rule for a commuting square `g₁ ∘ f₁ = g₂ ∘ f₂`. -/
theorem tangentMap_tangentMap_comm {Y' : Type*} [TopologicalSpace Y'] [T2Space Y']
    [ParacompactSpace Y'] {Q' : MPolyfold Y'} {f₁ : X → Y} {g₁ : Y → Z} {f₂ : X → Y'}
    {g₂ : Y' → Z} (hg₁ : Q.IsScSmoothMap S g₁) (hf₁ : P.IsScSmoothMap Q f₁)
    (hg₂ : Q'.IsScSmoothMap S g₂) (hf₂ : P.IsScSmoothMap Q' f₂) (h : g₁ ∘ f₁ = g₂ ∘ f₂)
    (α : P.TangentSpace) :
    tangentMap hg₁ (tangentMap hf₁ α) = tangentMap hg₂ (tangentMap hf₂ α) := by
  rw [tangentMap_tangentMap_of_eq hg₁ hf₁ (hg₂.comp hf₂) h, tangentMap_comp]
  rfl

/-- The chain rule `TF ∘ Tf = T(F ∘ f)` on `p⁻¹(U)`, for `f` sc-smooth on `U` and `F` globally
sc-smooth. -/
theorem tangentMap_tangentMapOn {f : X → Y} {F : Y → Z} {U : Set X} (hF : Q.IsScSmoothMap S F)
    (hf : P.IsScSmoothOn Q f U) {α : P.TangentSpace} (hα : α ∈ P.tangentPreimage U) :
    tangentMap hF (tangentMapOn hf α) =
      tangentMapOn (IsScSmoothOn.comp hF hf (mapsTo_univ _ _)) α := by
  have h1 := tangentMapOn_comp hF hf (mapsTo_univ _ _) hα
  rw [tangentMapOn_univ hF] at h1
  exact h1.symm

/-- The chain rule `Tf ∘ TF = T(f ∘ F)` on `p⁻¹(U)`, for `F` globally sc-smooth mapping the open
`U` into `V` and `f` sc-smooth on `V`. -/
theorem tangentMapOn_tangentMap {f : Y → Z} {F : X → Y} {U : Set X} {V : Set Y}
    (hf : Q.IsScSmoothOn S f V) (hF : P.IsScSmoothMap Q F) (hU : IsOpen U) (hFU : MapsTo F U V)
    {α : P.TangentSpace} (hα : α ∈ P.tangentPreimage U) :
    tangentMapOn hf (tangentMap hF α) =
      tangentMapOn (hf.comp (hF.mono hU (subset_univ _)) hFU) α := by
  have h1 := tangentMapOn_comp hf (hF.mono hU (subset_univ _)) hFU hα
  rw [h1, Function.comp_apply, tangentMapOn_eq_tangentMap hF _ hα]

/-- `TF ∘ Tf = TG` on `p⁻¹(U)` if `F ∘ f = G` on `U` (`F`, `G` globally sc-smooth). -/
theorem tangentMap_tangentMapOn_of_eqOn {f : X → Y} {F : Y → Z} {G : X → Z} {U : Set X}
    (hf : P.IsScSmoothOn Q f U) (hF : Q.IsScSmoothMap S F) (hG : P.IsScSmoothMap S G)
    (hFG : EqOn (F ∘ f) G U) {α : P.TangentSpace} (hα : α ∈ P.tangentPreimage U) :
    tangentMap hF (tangentMapOn hf α) = tangentMap hG α := by
  rw [tangentMap_tangentMapOn hF hf hα,
    tangentMapOn_congr (IsScSmoothOn.comp hF hf (mapsTo_univ _ _))
      (hG.mono hf.isOpen (subset_univ _)) hf.isOpen subset_rfl subset_rfl hFG hα,
    tangentMapOn_eq_tangentMap hG _ hα]

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### Base points and fibre injectivity -/

/-- The base point `p(Ts(h)) = s(p(h))`. -/
theorem levelVal_tangentProj_tSrc (v : X.PMor.TangentSpace) :
    X.PObj.levelVal 1 (X.PObj.tangentProj (X.tSrc v)) = X.src (X.tBase v) :=
  MPolyfold.levelVal_tangentProj_tangentMap _ v

/-- The base point `p(Tt(h)) = t(p(h))`. -/
theorem levelVal_tangentProj_tTgt (v : X.PMor.TangentSpace) :
    X.PObj.levelVal 1 (X.PObj.tangentProj (X.tTgt v)) = X.tgt (X.tBase v) :=
  MPolyfold.levelVal_tangentProj_tangentMap _ v

/-- `p(u_T(a)) = 1_{p(a)}`. -/
theorem tBase_tUnit (a : X.PObj.TangentSpace) :
    X.tBase (X.tUnit a) = X.unit (X.PObj.levelVal 1 (X.PObj.tangentProj a)) :=
  MPolyfold.levelVal_tangentProj_tangentMap _ a

/-- `p(ι_T(h)) = p(h)⁻¹`. -/
theorem tBase_tInv (v : X.PMor.TangentSpace) : X.tBase (X.tInv v) = X.inv (X.tBase v) :=
  MPolyfold.levelVal_tangentProj_tangentMap _ v

/-- The base point of `Tf(α)` for an sc-smooth map `f` into the morphisms. -/
theorem tBase_tangentMap {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    {P : MPolyfold Z} {f : Z → Mor} (hf : P.IsScSmoothMap X.PMor f) (α : P.TangentSpace) :
    X.tBase (MPolyfold.tangentMap hf α) = f (P.levelVal 1 (P.tangentProj α)) :=
  MPolyfold.levelVal_tangentProj_tangentMap hf α

theorem tBase_mem_levelSet (v : X.PMor.TangentSpace) : X.tBase v ∈ X.PMor.levelSet 1 :=
  MPolyfold.levelVal_mem _

theorem continuous_tBase : Continuous X.tBase := MPolyfold.continuous_levelVal_tangentProj

theorem continuous_tSrc : Continuous X.tSrc := MPolyfold.continuous_tangentMap _

theorem continuous_tTgt : Continuous X.tTgt := MPolyfold.continuous_tangentMap _

/-- **Fibre injectivity of `Ts`**: two tangent vectors of `𝐗` with the same base point and the
same image under `Ts` are equal (`s` is a local sc-diffeomorphism). -/
theorem tangent_ext {v w : X.PMor.TangentSpace} (hb : X.tBase v = X.tBase w)
    (hs : X.tSrc v = X.tSrc w) : v = w := by
  have hp : X.PMor.tangentProj v = X.PMor.tangentProj w := MPolyfold.level_ext hb
  exact X.isLocalScDiffeo_src.injOn_tangentFiber (X.PMor.tangentProj v) rfl hp.symm hs

/-- **Fibre injectivity of `Tt`**. -/
theorem tangent_ext_tgt {v w : X.PMor.TangentSpace} (hb : X.tBase v = X.tBase w)
    (ht : X.tTgt v = X.tTgt w) : v = w := by
  have hp : X.PMor.tangentProj v = X.PMor.tangentProj w := MPolyfold.level_ext hb
  exact X.isLocalScDiffeo_tgt.injOn_tangentFiber (X.PMor.tangentProj v) rfl hp.symm ht

/-- **Fibre surjectivity of `Ts`**: for `φ ∈ 𝐗₁` every `a ∈ T_{s φ}X` is `Ts(h)` for some
`h ∈ T_φ𝐗`. -/
theorem exists_tSrc_eq {φ : X.PMor.Level 1} {a : X.PObj.TangentSpace}
    (ha : X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src (X.PMor.levelVal 1 φ)) :
    ∃ v, X.PMor.tangentProj v = φ ∧ X.tSrc v = a := by
  obtain ⟨v, hv, hva⟩ := X.isLocalScDiffeo_src.tangentFiber_subset_image φ
    (X.PObj.tangentProj a) ha.symm (show a ∈ X.PObj.tangentFiber _ from rfl)
  exact ⟨v, hv, hva⟩

/-- Fibre surjectivity of `Ts`, with the base point a morphism on level `1`. -/
theorem exists_tSrc_eq' {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) {a : X.PObj.TangentSpace}
    (ha : X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src φ) :
    ∃ v, X.tBase v = φ ∧ X.tSrc v = a := by
  obtain ⟨v, hv, hva⟩ := X.exists_tSrc_eq (φ := X.PMor.levelMk 1 φ hφ) ha
  exact ⟨v, by rw [tBase, hv, MPolyfold.levelVal_levelMk], hva⟩

/-! ### The composition (8.5) -/

/-- Composable tangent vectors have composable base points. -/
theorem src_tBase_eq {k h : X.PMor.TangentSpace} (hkh : X.tSrc k = X.tTgt h) :
    X.src (X.tBase k) = X.tgt (X.tBase h) := by
  rw [← levelVal_tangentProj_tSrc, hkh, levelVal_tangentProj_tTgt]

/-- **(8.5)**: for `Ts(k) = Tt(h)`, `k ∘ h` lies over `p(k) ∘ p(h)` and `Ts(k ∘ h) = Ts(h)`. -/
theorem tComp_spec {k h : X.PMor.TangentSpace} (hkh : X.tSrc k = X.tTgt h) :
    X.tBase (X.tComp k h) = X.comp (X.tBase k) (X.tBase h) ∧
      X.tSrc (X.tComp k h) = X.tSrc h := by
  have hc := X.src_tBase_eq hkh
  have hex : ∃ v, X.tBase v = X.comp (X.tBase k) (X.tBase h) ∧ X.tSrc v = X.tSrc h :=
    X.exists_tSrc_eq' (X.comp_mem_levelSet (X.tBase_mem_levelSet k) hc)
      (by rw [levelVal_tangentProj_tSrc, X.src_comp _ _ hc])
  rw [tComp, dif_pos hex]
  exact hex.choose_spec

theorem tBase_tComp {k h : X.PMor.TangentSpace} (hkh : X.tSrc k = X.tTgt h) :
    X.tBase (X.tComp k h) = X.comp (X.tBase k) (X.tBase h) := (X.tComp_spec hkh).1

theorem tSrc_tComp {k h : X.PMor.TangentSpace} (hkh : X.tSrc k = X.tTgt h) :
    X.tSrc (X.tComp k h) = X.tSrc h := (X.tComp_spec hkh).2

/-- `k ∘ h` is the unique vector over `p(k) ∘ p(h)` with `Ts(k ∘ h) = Ts(h)`. -/
theorem tComp_eq {k h v : X.PMor.TangentSpace} (hkh : X.tSrc k = X.tTgt h)
    (hb : X.tBase v = X.comp (X.tBase k) (X.tBase h)) (hs : X.tSrc v = X.tSrc h) :
    X.tComp k h = v :=
  X.tangent_ext ((X.tBase_tComp hkh).trans hb.symm) ((X.tSrc_tComp hkh).trans hs.symm)

/-! ### Lemma 8.1.2 (2017: 8.1) on a sheet of `s` -/

section Sheet

variable {X} {σ : Obj → Mor} {W : Set Mor} {V : Set Obj}

/-- On a sheet `s : W → V` with inverse `σ`, `T(s|W)⁻¹(Ts k) = k` for `k` over `W`. -/
theorem tangentMapOn_srcInv_tSrc (hd : X.PMor.IsScDiffeoOn X.PObj X.src σ W V)
    {k : X.PMor.TangentSpace} (hk : X.tBase k ∈ W) :
    MPolyfold.tangentMapOn hd.isScSmoothOn_inv (X.tSrc k) = k :=
  (hd.tangentMap X.isScSmoothMap_src).left_inv k hk

/-- A vector `h` composable with a vector over `W` lies over `t⁻¹(V)`. -/
theorem mem_tangentPreimage_tgt (hd : X.PMor.IsScDiffeoOn X.PObj X.src σ W V)
    {k h : X.PMor.TangentSpace} (hkh : X.tSrc k = X.tTgt h) (hk : X.tBase k ∈ W) :
    h ∈ X.PMor.tangentPreimage (X.tgt ⁻¹' V) := by
  change X.tgt (X.tBase h) ∈ V
  rw [← X.src_tBase_eq hkh]
  exact hd.mapsTo hk

/-- **The composition on a sheet**: for a sheet `s : W → V` with inverse `σ` and
`g(φ') = m(σ(t φ'), φ')` (sc-smooth on `t⁻¹(V)` by condition (4)), `k ∘ h = Tg(h)` for
composable `k, h` with `k` over `W`. -/
theorem tComp_eq_tangentMapOn (hd : X.PMor.IsScDiffeoOn X.PObj X.src σ W V)
    {k h : X.PMor.TangentSpace} (hkh : X.tSrc k = X.tTgt h) (hk : X.tBase k ∈ W) :
    X.tComp k h = MPolyfold.tangentMapOn (X.isScSmoothCompSheet σ W V hd) h := by
  have hh := mem_tangentPreimage_tgt hd hkh hk
  have hg := X.isScSmoothCompSheet σ W V hd
  refine X.tComp_eq hkh ?_ ?_
  · change X.PMor.levelVal 1 (X.PMor.tangentProj (MPolyfold.tangentMapOn hg h)) = _
    rw [MPolyfold.levelVal_tangentProj_tangentMapOn hg hh]
    change X.comp (σ (X.tgt (X.tBase h))) (X.tBase h) = _
    rw [← X.src_tBase_eq hkh, hd.left_inv _ hk]
  · refine MPolyfold.tangentMap_tangentMapOn_of_eqOn hg X.isScSmoothMap_src X.isScSmoothMap_src
      (fun ψ hψ => ?_) hh
    exact X.src_comp _ _ (hd.right_inv _ hψ)

/-- The target of `k ∘ h` on a sheet: `Tt(Tg(h)) = Tt(k)`, from `t ∘ g = t ∘ σ ∘ t` on
`t⁻¹(V)` (the text's `α ∘ s = t ∘ (s|U(ψ))⁻¹ ∘ t`). -/
theorem tTgt_tangentMapOn (hd : X.PMor.IsScDiffeoOn X.PObj X.src σ W V)
    {k h : X.PMor.TangentSpace} (hkh : X.tSrc k = X.tTgt h) (hk : X.tBase k ∈ W) :
    X.tTgt (MPolyfold.tangentMapOn (X.isScSmoothCompSheet σ W V hd) h) = X.tTgt k := by
  have hh := mem_tangentPreimage_tgt hd hkh hk
  have hg := X.isScSmoothCompSheet σ W V hd
  have hU : IsOpen (X.tgt ⁻¹' V) := hd.isScSmoothOn_inv.isOpen.preimage X.continuous_tgt
  have hσt := hd.isScSmoothOn_inv.comp (X.isScSmoothMap_tgt.mono hU (subset_univ _))
    (mapsTo_preimage _ _)
  -- `T(σ ∘ t)(h) = Tσ(Tt h) = Tσ(Ts k) = k`
  have h1 : MPolyfold.tangentMapOn hσt h = k := by
    rw [← MPolyfold.tangentMapOn_tangentMap hd.isScSmoothOn_inv X.isScSmoothMap_tgt hU
      (mapsTo_preimage _ _) hh]
    change MPolyfold.tangentMapOn hd.isScSmoothOn_inv (X.tTgt h) = k
    rw [← hkh, tangentMapOn_srcInv_tSrc hd hk]
  -- `T(t ∘ g)(h) = T(t ∘ σ ∘ t)(h) = Tt(k)`
  change MPolyfold.tangentMap X.isScSmoothMap_tgt (MPolyfold.tangentMapOn hg h) = _
  rw [MPolyfold.tangentMap_tangentMapOn X.isScSmoothMap_tgt hg hh,
    MPolyfold.tangentMapOn_congr
      (MPolyfold.IsScSmoothOn.comp X.isScSmoothMap_tgt hg (mapsTo_univ _ _))
      (MPolyfold.IsScSmoothOn.comp X.isScSmoothMap_tgt hσt (mapsTo_univ _ _)) hU subset_rfl
      subset_rfl (fun ψ hψ => X.tgt_comp _ _ (hd.right_inv _ hψ)) hh,
    ← MPolyfold.tangentMap_tangentMapOn X.isScSmoothMap_tgt hσt hh, h1]
  rfl

variable (X) in
/-- **Lemma 8.1.2 (2017: 8.1)** (in the sheet form of the text's proof): let `s : W → V` be a sheet of `s` with
inverse `σ = (s|U(ψ))⁻¹` and `g(φ') = m(σ(t φ'), φ')` (the text's `m(F(φ'), φ')`,
`F = (s|U(ψ))⁻¹ ∘ t`; sc-smooth on `t⁻¹(V)` by condition (4)).  For composable `k, h`
(`Ts(k) = Tt(h)`) with `k` over `W`: `k = T(s|U(ψ))⁻¹(Tt(h))`, the composition (8.5) is the
tangent `k ∘ h = Tg(h)` (the text's `T m(ψ, φ)(k, h)`), and it lies over `ψ ∘ φ` with
`Ts(k ∘ h) = Ts(h)`, i.e. `k ∘ h = (ψ ∘ φ, (Ts(ψ ∘ φ))⁻¹ Ts(φ)(h))`. -/
theorem lemma_8_1_2 (hd : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) {k h : X.PMor.TangentSpace}
    (hkh : X.tSrc k = X.tTgt h) (hk : X.tBase k ∈ W) :
    MPolyfold.tangentMapOn hd.isScSmoothOn_inv (X.tTgt h) = k ∧
      X.tComp k h = MPolyfold.tangentMapOn (X.isScSmoothCompSheet σ W V hd) h ∧
      X.tBase (X.tComp k h) = X.comp (X.tBase k) (X.tBase h) ∧
      X.tSrc (X.tComp k h) = X.tSrc h :=
  ⟨by rw [← hkh]; exact tangentMapOn_srcInv_tSrc hd hk, tComp_eq_tangentMapOn hd hkh hk,
    X.tComp_spec hkh⟩

end Sheet

/-! ### Lemmas 8.1.3 and 8.1.4 (2017: 8.2 and 8.3) -/

/-- **Lemma 8.1.3 (2017: 8.2)**: `s_T(Ψ ∘ Φ) = s_T(Φ)` and `t_T(Ψ ∘ Φ) = t_T(Ψ)`. -/
theorem lemma_8_1_3 {k h : X.PMor.TangentSpace} (hkh : X.tSrc k = X.tTgt h) :
    X.tSrc (X.tComp k h) = X.tSrc h ∧ X.tTgt (X.tComp k h) = X.tTgt k := by
  refine ⟨X.tSrc_tComp hkh, ?_⟩
  obtain ⟨W, V, σ, hk, hd⟩ := X.isLocalScDiffeo_src (X.tBase k)
  rw [tComp_eq_tangentMapOn hd hkh hk, tTgt_tangentMapOn hd hkh hk]

/-- **Lemma 8.1.4 (2017: 8.3)**: the composition of `T𝐗` is associative. -/
theorem lemma_8_1_4 {l k h : X.PMor.TangentSpace} (hlk : X.tSrc l = X.tTgt k)
    (hkh : X.tSrc k = X.tTgt h) : X.tComp (X.tComp l k) h = X.tComp l (X.tComp k h) := by
  have h1 : X.tSrc (X.tComp l k) = X.tTgt h := by rw [X.tSrc_tComp hlk, hkh]
  have h2 : X.tSrc l = X.tTgt (X.tComp k h) := by rw [(X.lemma_8_1_3 hkh).2, hlk]
  refine X.tangent_ext ?_ ?_
  · rw [X.tBase_tComp h1, X.tBase_tComp h2, X.tBase_tComp hlk, X.tBase_tComp hkh,
      X.comp_assoc _ _ _ (X.src_tBase_eq hlk) (X.src_tBase_eq hkh)]
  · rw [X.tSrc_tComp h1, X.tSrc_tComp h2, X.tSrc_tComp hkh]

/-! ### Units and inverses (Lemmas 8.1.5, 8.1.6 (2017: 8.4, 8.5)) -/

/-- `Ts ∘ Tu = id` (chain rule for `s ∘ u = id`). -/
theorem tSrc_tUnit (a : X.PObj.TangentSpace) : X.tSrc (X.tUnit a) = a :=
  MPolyfold.tangentMap_tangentMap_of_eq_id X.isScSmoothMap_src X.isScSmoothMap_unit
    (funext X.src_unit) a

/-- `Tt ∘ Tu = id` (chain rule for `t ∘ u = id`). -/
theorem tTgt_tUnit (a : X.PObj.TangentSpace) : X.tTgt (X.tUnit a) = a :=
  MPolyfold.tangentMap_tangentMap_of_eq_id X.isScSmoothMap_tgt X.isScSmoothMap_unit
    (funext X.tgt_unit) a

/-- **(8.8)**: `u_T(a) = (1_x, Ts(1_x)⁻¹(a))`, the unique vector over `1_x` with `Ts = a`. -/
theorem tUnit_eq {a : X.PObj.TangentSpace} {v : X.PMor.TangentSpace}
    (hb : X.tBase v = X.unit (X.PObj.levelVal 1 (X.PObj.tangentProj a))) (hs : X.tSrc v = a) :
    X.tUnit a = v :=
  X.tangent_ext ((X.tBase_tUnit a).trans hb.symm) ((X.tSrc_tUnit a).trans hs.symm)

/-- `Ts ∘ Tι = Tt` (chain rule for `s ∘ ι = t`). -/
theorem tSrc_tInv (v : X.PMor.TangentSpace) : X.tSrc (X.tInv v) = X.tTgt v :=
  MPolyfold.tangentMap_tangentMap_of_eq X.isScSmoothMap_src X.isScSmoothMap_inv
    X.isScSmoothMap_tgt (funext X.src_inv) v

/-- `Tt ∘ Tι = Ts` (chain rule for `t ∘ ι = s`). -/
theorem tTgt_tInv (v : X.PMor.TangentSpace) : X.tTgt (X.tInv v) = X.tSrc v :=
  MPolyfold.tangentMap_tangentMap_of_eq X.isScSmoothMap_tgt X.isScSmoothMap_inv
    X.isScSmoothMap_src (funext X.tgt_inv) v

theorem tComp_tUnit (k : X.PMor.TangentSpace) : X.tComp k (X.tUnit (X.tSrc k)) = k :=
  X.tComp_eq (X.tTgt_tUnit _).symm
    (by rw [tBase_tUnit, levelVal_tangentProj_tSrc, X.comp_unit]) (X.tSrc_tUnit _).symm

theorem tUnit_tComp (h : X.PMor.TangentSpace) : X.tComp (X.tUnit (X.tTgt h)) h = h :=
  X.tComp_eq (X.tSrc_tUnit _) (by rw [tBase_tUnit, levelVal_tangentProj_tTgt, X.unit_comp]) rfl

theorem tComp_tInv (v : X.PMor.TangentSpace) : X.tComp v (X.tInv v) = X.tUnit (X.tTgt v) :=
  X.tComp_eq (X.tTgt_tInv v).symm
    (by rw [tBase_tUnit, tBase_tInv, levelVal_tangentProj_tTgt, X.comp_inv])
    (by rw [tSrc_tUnit, tSrc_tInv])

theorem tInv_tComp (v : X.PMor.TangentSpace) : X.tComp (X.tInv v) v = X.tUnit (X.tSrc v) :=
  X.tComp_eq (X.tSrc_tInv v)
    (by rw [tBase_tUnit, tBase_tInv, levelVal_tangentProj_tSrc, X.inv_comp]) (X.tSrc_tUnit _)

/-- **Lemma 8.1.5 (2017: 8.4)** (with (8.7), (8.8)): the unit `1_q = u_T(q)` of `q ∈ T_xX` lies over `1_x`
with `Ts(1_q) = q`, i.e. `1_q = (1_x, Ts(1_x)⁻¹ q)`; it is a morphism `q → q` and a two-sided
identity. -/
theorem lemma_8_1_5 (q : X.PObj.TangentSpace) :
    X.tBase (X.tUnit q) = X.unit (X.PObj.levelVal 1 (X.PObj.tangentProj q)) ∧
      X.tSrc (X.tUnit q) = q ∧ X.tTgt (X.tUnit q) = q ∧
      (∀ k, X.tSrc k = q → X.tComp k (X.tUnit q) = k) ∧
      (∀ k, X.tTgt k = q → X.tComp (X.tUnit q) k = k) := by
  refine ⟨X.tBase_tUnit q, X.tSrc_tUnit q, X.tTgt_tUnit q, fun k hk => ?_, fun k hk => ?_⟩
  · subst hk
    exact X.tComp_tUnit k
  · subst hk
    exact X.tUnit_tComp k

/-- **Lemma 8.1.6 (2017: 8.5)** (with (8.9)): `ι_T(φ, k) = (φ⁻¹, Tι(φ)(k))` is a morphism
`t_T(φ, k) → s_T(φ, k)` and a two-sided inverse. -/
theorem lemma_8_1_6 (v : X.PMor.TangentSpace) :
    X.tBase (X.tInv v) = X.inv (X.tBase v) ∧ X.tSrc (X.tInv v) = X.tTgt v ∧
      X.tTgt (X.tInv v) = X.tSrc v ∧ X.tComp (X.tInv v) v = X.tUnit (X.tSrc v) ∧
      X.tComp v (X.tInv v) = X.tUnit (X.tTgt v) :=
  ⟨X.tBase_tInv v, X.tSrc_tInv v, X.tTgt_tInv v, X.tInv_tComp v, X.tComp_tInv v⟩

/-- The groupoid `(TX, T𝐗)` with the structure maps (8.3)–(8.9) (Lemmas 8.1.3–8.1.6 (2017: 8.2–8.5)). -/
def tangentGroupoidStr : GroupoidStr X.PObj.TangentSpace X.PMor.TangentSpace where
  src := X.tSrc
  tgt := X.tTgt
  comp := X.tComp
  unit := X.tUnit
  inv := X.tInv
  src_comp _ _ h := (X.lemma_8_1_3 h).1
  tgt_comp _ _ h := (X.lemma_8_1_3 h).2
  comp_assoc _ _ _ h h' := X.lemma_8_1_4 h h'
  src_unit := X.tSrc_tUnit
  tgt_unit := X.tTgt_tUnit
  comp_unit := X.tComp_tUnit
  unit_comp := X.tUnit_tComp
  src_inv := X.tSrc_tInv
  tgt_inv := X.tTgt_tInv
  comp_inv := X.tComp_tInv
  inv_comp := X.tInv_tComp

/-! ### Lemma 8.1.7 (2017: 8.6): the differential geometric properties -/

theorem isLocalScDiffeo_tSrc :
    X.PMor.tangentPolyfold.IsLocalScDiffeo X.PObj.tangentPolyfold X.tSrc :=
  X.isLocalScDiffeo_src.tangentMap

theorem isLocalScDiffeo_tTgt :
    X.PMor.tangentPolyfold.IsLocalScDiffeo X.PObj.tangentPolyfold X.tTgt :=
  X.isLocalScDiffeo_tgt.tangentMap

theorem surjective_tSrc : Surjective X.tSrc :=
  X.isLocalScDiffeo_src.surjective_tangentMap fun x => ⟨X.unit x, X.src_unit x⟩

theorem surjective_tTgt : Surjective X.tTgt :=
  X.isLocalScDiffeo_tgt.surjective_tangentMap fun x => ⟨X.unit x, X.tgt_unit x⟩

theorem isScSmoothMap_tUnit :
    X.PObj.tangentPolyfold.IsScSmoothMap X.PMor.tangentPolyfold X.tUnit :=
  MPolyfold.tangentMap_isScSmooth X.isScSmoothMap_unit

theorem isScSmoothMap_tInv :
    X.PMor.tangentPolyfold.IsScSmoothMap X.PMor.tangentPolyfold X.tInv :=
  MPolyfold.tangentMap_isScSmooth X.isScSmoothMap_inv

/-- **Condition (4) for `T(X, 𝐗)`, sheet form**: for a sheet `s_T : W_T → V_T` with inverse
`σ_T`, `Ψ ↦ σ_T(t_T Ψ) ∘ Ψ` is sc-smooth on `t_T⁻¹(V_T)`: near `Ψ₀` it is `Tg` for a sheet of
`s` around the base point of `σ_T(t_T Ψ₀)` (`tComp_eq_tangentMapOn`). -/
theorem isScSmoothCompSheet_tangent :
    IsScSmoothCompSheet X.PObj.tangentPolyfold X.PMor.tangentPolyfold X.tSrc X.tTgt X.tComp := by
  intro σT WT VT hdT
  have hU : IsOpen (X.tTgt ⁻¹' VT) := hdT.isScSmoothOn_inv.isOpen.preimage X.continuous_tTgt
  refine MPolyfold.IsScSmoothOn.of_locally hU fun Ψ₀ hΨ₀ => ?_
  obtain ⟨W, V, σ, hk₀, hd⟩ := X.isLocalScDiffeo_src (X.tBase (σT (X.tTgt Ψ₀)))
  have hcN : ContinuousOn (fun Ψ => X.tBase (σT (X.tTgt Ψ))) (X.tTgt ⁻¹' VT) :=
    X.continuous_tBase.comp_continuousOn (hdT.isScSmoothOn_inv.continuousOn.comp
      X.continuous_tTgt.continuousOn (mapsTo_preimage _ _))
  have hN := hcN.isOpen_inter_preimage hU hd.isScSmoothOn.isOpen
  refine ⟨_, hN, ⟨hΨ₀, hk₀⟩, inter_subset_left, ?_⟩
  have hkh : ∀ Ψ ∈ X.tTgt ⁻¹' VT, X.tSrc (σT (X.tTgt Ψ)) = X.tTgt Ψ :=
    fun Ψ hΨ => hdT.right_inv _ hΨ
  have hg := X.isScSmoothCompSheet σ W V hd
  exact ((MPolyfold.tangentMapOn_isScSmoothOn hg).mono hN
    fun Ψ hΨ => mem_tangentPreimage_tgt hd (hkh Ψ hΨ.1) hΨ.2).congr
    fun Ψ hΨ => (tComp_eq_tangentMapOn hd (hkh Ψ hΨ.1) hΨ.2).symm

/-- **Condition (4) for `T(X, 𝐗)`**, literally, on the M-polyfold `T𝐗 ₛ×ₜ T𝐗`. -/
theorem isScSmoothComp_tangent :
    IsScSmoothComp X.PObj.tangentPolyfold X.PMor.tangentPolyfold X.tSrc X.tTgt X.tComp
      X.isLocalScDiffeo_tSrc X.isLocalScDiffeo_tTgt.isScSmoothMap :=
  (isScSmoothComp_iff_sheet _ _).2 X.isScSmoothCompSheet_tangent

/-- **Lemma 8.1.7 (2017: 8.6)**: `s_T` and `t_T` are surjective local sc-diffeomorphisms, `u_T` and `ι_T` are
sc-smooth, and the multiplication is sc-smooth on `T𝐗 ₛ×ₜ T𝐗` (condition (4), literally and in
the sheet form). -/
theorem lemma_8_1_7 :
    X.PMor.tangentPolyfold.IsLocalScDiffeo X.PObj.tangentPolyfold X.tSrc ∧ Surjective X.tSrc ∧
      X.PMor.tangentPolyfold.IsLocalScDiffeo X.PObj.tangentPolyfold X.tTgt ∧
      Surjective X.tTgt ∧
      X.PObj.tangentPolyfold.IsScSmoothMap X.PMor.tangentPolyfold X.tUnit ∧
      X.PMor.tangentPolyfold.IsScSmoothMap X.PMor.tangentPolyfold X.tInv ∧
      IsScSmoothComp X.PObj.tangentPolyfold X.PMor.tangentPolyfold X.tSrc X.tTgt X.tComp
        X.isLocalScDiffeo_tSrc X.isLocalScDiffeo_tTgt.isScSmoothMap ∧
      IsScSmoothCompSheet X.PObj.tangentPolyfold X.PMor.tangentPolyfold X.tSrc X.tTgt X.tComp :=
  ⟨X.isLocalScDiffeo_tSrc, X.surjective_tSrc, X.isLocalScDiffeo_tTgt, X.surjective_tTgt,
    X.isScSmoothMap_tUnit, X.isScSmoothMap_tInv, X.isScSmoothComp_tangent,
    X.isScSmoothCompSheet_tangent⟩

/-! ### Lemma 8.1.8 (2017: 8.7): properness -/

/-- **Lemma 8.1.8 (2017: 8.7)**: `T(X, 𝐗)` has the properness property (3): for `a ∈ T_xX` and `V(x)` as in
(3) for `X`, `t_T : s_T⁻¹(cl TV) → TX` is proper, `TV = p⁻¹(V)`.  For `(Φ_k)` with
`s_T(Φ_k) ∈ cl TV` and `t_T(Φ_k) → b`, a subsequence of the base points converges in `𝐗` to some
`φ` (properness of `X`), and `Φ_k = (Tt|TU(φ))⁻¹(t_T(Φ_k)) → (Tt|TU(φ))⁻¹(b)`. -/
theorem lemma_8_1_8 (a : X.PObj.TangentSpace) : ∃ V' : Set X.PObj.TangentSpace, IsOpen V' ∧
    a ∈ V' ∧ IsProperMap ((X.tSrc ⁻¹' closure V').domRestrict X.tTgt) := by
  obtain ⟨V, hVo, hxV, hV⟩ := X.exists_isProperMap (X.PObj.levelVal 1 (X.PObj.tangentProj a))
  have hpc := MPolyfold.continuous_levelVal_tangentProj (P := X.PObj)
  refine ⟨X.PObj.tangentPreimage V, MPolyfold.isOpen_tangentPreimage hVo, hxV, ?_⟩
  rw [MPolyfold.isProperMap_domRestrict_iff_of_isClosed X.PMor.tangentPolyfold
    X.PObj.tangentPolyfold X.continuous_tSrc X.continuous_tTgt isClosed_closure]
  intro Φ b hΦ hb
  -- the base points: `s(φ_k) ∈ cl V` and `t(φ_k) → p(b)`
  have hΦ' : ∀ n, X.src (X.tBase (Φ n)) ∈ closure V := fun n => by
    rw [← levelVal_tangentProj_tSrc]
    exact hpc.closure_preimage_subset V (hΦ n)
  have hb' : Tendsto (X.tgt ∘ fun n => X.tBase (Φ n)) atTop
      (𝓝 (X.PObj.levelVal 1 (X.PObj.tangentProj b))) :=
    ((hpc.tendsto b).comp hb).congr fun n => X.levelVal_tangentProj_tTgt (Φ n)
  -- properness of `X`: `φ_k → φ₀` in `𝐗` along a subsequence
  obtain ⟨φ₀, -, hφ₀t, ψ, hψ, hlim⟩ :=
    MPolyfold.exists_tendsto_subseq_of_isProperMap_domRestrict X.PMor hV hΦ' hb'
  -- `t : W → V''` near `φ₀`, and `Tt : p⁻¹(W) → p⁻¹(V'')` with continuous inverse
  obtain ⟨W, V'', τ, hφ₀W, hd⟩ := X.isLocalScDiffeo_tgt φ₀
  have hD := hd.tangentMap X.isScSmoothMap_tgt
  have hbV : b ∈ X.PObj.tangentPreimage V'' := by
    change X.PObj.levelVal 1 (X.PObj.tangentProj b) ∈ V''
    rw [← hφ₀t]
    exact hd.mapsTo hφ₀W
  have hcont : ContinuousAt (MPolyfold.tangentMapOn hd.isScSmoothOn_inv) b :=
    hD.isScSmoothOn_inv.continuousOn.continuousAt (hD.isScSmoothOn_inv.isOpen.mem_nhds hbV)
  refine ⟨MPolyfold.tangentMapOn hd.isScSmoothOn_inv b, ψ, hψ, ?_⟩
  have h1 : Tendsto (MPolyfold.tangentMapOn hd.isScSmoothOn_inv ∘ X.tTgt ∘ Φ ∘ ψ) atTop
      (𝓝 (MPolyfold.tangentMapOn hd.isScSmoothOn_inv b)) :=
    hcont.tendsto.comp (hb.comp hψ.tendsto_atTop)
  refine h1.congr' ?_
  filter_upwards [hlim (hd.isScSmoothOn.isOpen.mem_nhds hφ₀W)] with n hn
  exact hD.left_inv _ hn

/-! ### Theorem 8.1.1 (2017: 8.1) -/

/-- **Theorem 8.1.1 (2017: 8.1), the structure**: the tangent `T(X, 𝐗) = (TX, T𝐗)`, an ep-groupoid with the
object M-polyfold `TX`, the morphism M-polyfold `T𝐗` and the structure maps (8.3)–(8.9). -/
def tangentEpGroupoid : EpGroupoid X.PObj.TangentSpace X.PMor.TangentSpace where
  toGroupoidStr := X.tangentGroupoidStr
  PObj := X.PObj.tangentPolyfold
  PMor := X.PMor.tangentPolyfold
  isLocalScDiffeo_src := X.isLocalScDiffeo_tSrc
  isLocalScDiffeo_tgt := X.isLocalScDiffeo_tTgt
  isScSmoothMap_unit := X.isScSmoothMap_tUnit
  isScSmoothMap_inv := X.isScSmoothMap_tInv
  exists_isProperMap := X.lemma_8_1_8
  isScSmoothComp := X.isScSmoothComp_tangent

/-- The projections `(p, p) : T(X, 𝐗) → (X, 𝐗)¹`, a functor sc-smooth on objects and morphisms
(Theorem 8.1.1 (2017: 8.1), last sentence; `(X, 𝐗)¹` is Chapter 7's `liftOne`). -/
def tangentProjFunctor : EpFunctor X.tangentEpGroupoid X.liftOne where
  obj := X.PObj.tangentProj
  mor := X.PMor.tangentProj
  src_mor v := MPolyfold.level_ext (X.levelVal_tangentProj_tSrc v).symm
  tgt_mor v := MPolyfold.level_ext (X.levelVal_tangentProj_tTgt v).symm
  mor_comp k h hkh := MPolyfold.level_ext <| by
    have hkh' : X.tSrc k = X.tTgt h := hkh
    have hc : X.liftOne.src (X.PMor.tangentProj k) = X.liftOne.tgt (X.PMor.tangentProj h) :=
      MPolyfold.level_ext (X.src_tBase_eq hkh')
    rw [X.liftOne_comp_val hc]
    exact X.tBase_tComp hkh'
  mor_unit a := MPolyfold.level_ext (X.tBase_tUnit a)
  isScSmoothMap_obj := X.PObj.tangentProj_isScSmooth
  isScSmoothMap_mor := X.PMor.tangentProj_isScSmooth

/-- **Theorem 8.1.1 (2017: 8.1)** (without its tameness sentence, Lemma 8.8): `T(X, 𝐗) = (TX, T𝐗)` is an
ep-groupoid (`tangentEpGroupoid`) with the M-polyfolds `TX`, `T𝐗` and the structure maps
`s_T = Ts`, `t_T = Tt` (8.3), the composition (8.5)–(8.6) (over `p(k) ∘ p(h)` with
`Ts(k ∘ h) = Ts(h)`), `u_T = Tu` (8.8) and `ι_T = Tι` (8.9); and the projections
`(p, p) : T(X, 𝐗) → (X, 𝐗)¹` form an sc-smooth functor (`tangentProjFunctor`). -/
theorem theorem_8_1_1 :
    X.tangentEpGroupoid.PObj = X.PObj.tangentPolyfold ∧
      X.tangentEpGroupoid.PMor = X.PMor.tangentPolyfold ∧
      X.tangentEpGroupoid.src = MPolyfold.tangentMap X.isScSmoothMap_src ∧
      X.tangentEpGroupoid.tgt = MPolyfold.tangentMap X.isScSmoothMap_tgt ∧
      X.tangentEpGroupoid.comp = X.tComp ∧
      X.tangentEpGroupoid.unit = MPolyfold.tangentMap X.isScSmoothMap_unit ∧
      X.tangentEpGroupoid.inv = MPolyfold.tangentMap X.isScSmoothMap_inv ∧
      (∀ k h, X.tangentEpGroupoid.src k = X.tangentEpGroupoid.tgt h →
        X.tBase (X.tangentEpGroupoid.comp k h) = X.comp (X.tBase k) (X.tBase h) ∧
          X.tangentEpGroupoid.src (X.tangentEpGroupoid.comp k h) =
            X.tangentEpGroupoid.src h) ∧
      X.tangentProjFunctor.obj = X.PObj.tangentProj ∧
      X.tangentProjFunctor.mor = X.PMor.tangentProj :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ h => X.tComp_spec h, rfl, rfl⟩

/-! ### Remark 8.1.10 (2017: 8.1): `Tφ = t_T ∘ (s_T|T_xX)⁻¹` -/

/-- `Tt ∘ (Ts|T_φ𝐗)⁻¹ = Tφ` (Chapter 7's `tangentMor`, Definition 7.1.4 (2017: 7.4)): for `h ∈ T_φ𝐗`,
`Tφ(Ts(h)) = Tt(h)`. -/
theorem tangentMor_tSrc (v : X.PMor.TangentSpace) :
    X.tangentMor (X.tBase v) (X.tSrc v) = X.tTgt v := by
  have hex : ∃ w : X.PMor.TangentSpace, X.PMor.levelVal 1 (X.PMor.tangentProj w) = X.tBase v ∧
      MPolyfold.tangentMap X.isScSmoothMap_src w = X.tSrc v := ⟨v, rfl, rfl⟩
  rw [tangentMor, dif_pos hex]
  exact congrArg (MPolyfold.tangentMap X.isScSmoothMap_tgt)
    (X.tangent_ext hex.choose_spec.1 hex.choose_spec.2)

/-- **Functoriality of `Tφ`**: `T(ψ ∘ φ) = Tψ ∘ Tφ` on `T_{s φ}X` for composable `ψ, φ ∈ 𝐗₁`. -/
theorem tangentMor_comp {φ ψ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) (hψφ : X.src ψ = X.tgt φ)
    {a : X.PObj.TangentSpace} (ha : X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src φ) :
    X.tangentMor (X.comp ψ φ) a = X.tangentMor ψ (X.tangentMor φ a) := by
  obtain ⟨h, rfl, rfl⟩ := X.exists_tSrc_eq' hφ ha
  have hψ1 : ψ ∈ X.PMor.levelSet 1 := by
    rw [← X.mem_levelSet_src_iff, hψφ, X.mem_levelSet_tgt_iff]
    exact hφ
  obtain ⟨k, rfl, hkh⟩ := X.exists_tSrc_eq' hψ1 (a := X.tTgt h)
    (by rw [levelVal_tangentProj_tTgt, hψφ])
  rw [X.tangentMor_tSrc h, ← hkh, X.tangentMor_tSrc k, ← X.tBase_tComp hkh,
    ← X.tSrc_tComp hkh, X.tangentMor_tSrc, (X.lemma_8_1_3 hkh).2]

/-- The map `G : (φ, h) ↦ (Tφ, Ts(h))` of Remark 8.1.10 (2017: 8.1), with `Tφ` recorded by its label
`φ ∈ 𝐗₁`. -/
def remarkG (v : X.PMor.TangentSpace) : Mor × X.PObj.TangentSpace := (X.tBase v, X.tSrc v)

/-- **Remark 8.1.10 (2017: 8.1)**: (1) `t_T ∘ (s_T|T_φ𝐗)⁻¹ = Tφ : T_xX → T_yX` (Definition 7.1.4 (2017: 7.4)'s `Tφ`);
(2) `T(ψ ∘ φ) = Tψ ∘ Tφ` on `T_{s φ}X`; (3) `G : (φ, h) ↦ (Tφ, Ts(h))` is a bijection of `T𝐗`
onto the pairs `(Tφ, a)`, `φ ∈ 𝐗₁`, `a ∈ T_{s φ}X` (with `Tφ` labelled by `φ`); (4) `G` is
compatible with the compositions: `(ψ, k) ∘ (φ, h)` is defined iff `Ts(k) = Tφ(Ts(h))`, and then
`G(k ∘ h) = (T(ψ ∘ φ), Ts(h))` with `T(ψ ∘ φ) = Tψ ∘ Tφ`. -/
theorem remark_8_1_10 :
    (∀ v, X.tangentMor (X.tBase v) (X.tSrc v) = X.tTgt v) ∧
      (∀ φ ψ, φ ∈ X.PMor.levelSet 1 → X.src ψ = X.tgt φ → ∀ a,
        X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src φ →
          X.tangentMor (X.comp ψ φ) a = X.tangentMor ψ (X.tangentMor φ a)) ∧
      Injective X.remarkG ∧
      range X.remarkG = {p | p.1 ∈ X.PMor.levelSet 1 ∧
        X.PObj.levelVal 1 (X.PObj.tangentProj p.2) = X.src p.1} ∧
      (∀ k h, (X.tSrc k = X.tTgt h ↔ X.tSrc k = X.tangentMor (X.tBase h) (X.tSrc h))) ∧
      (∀ k h, X.tSrc k = X.tTgt h →
        X.remarkG (X.tComp k h) = (X.comp (X.tBase k) (X.tBase h), X.tSrc h) ∧
          ∀ a, X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src (X.tBase h) →
            X.tangentMor (X.comp (X.tBase k) (X.tBase h)) a =
              X.tangentMor (X.tBase k) (X.tangentMor (X.tBase h) a)) := by
  refine ⟨X.tangentMor_tSrc, fun φ ψ hφ hψφ a ha => X.tangentMor_comp hφ hψφ ha,
    fun v w hvw => X.tangent_ext (congrArg Prod.fst hvw) (congrArg Prod.snd hvw), ?_,
    fun k h => by rw [X.tangentMor_tSrc], fun k h hkh => ⟨?_, fun a ha =>
      X.tangentMor_comp (X.tBase_mem_levelSet h) (X.src_tBase_eq hkh) ha⟩⟩
  · ext ⟨φ, a⟩
    constructor
    · rintro ⟨v, hv⟩
      simp only [remarkG, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact ⟨X.tBase_mem_levelSet v, X.levelVal_tangentProj_tSrc v⟩
    · rintro ⟨hφ, ha⟩
      obtain ⟨v, hv, hva⟩ := X.exists_tSrc_eq' hφ ha
      exact ⟨v, by rw [remarkG, hv, hva]⟩
  · rw [remarkG, X.tBase_tComp hkh, X.tSrc_tComp hkh]

end EpGroupoid

/-! ### Theorem 8.1.11 (2017: 8.2): the tangent of an sc-smooth functor -/

namespace EpFunctor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- **Theorem 8.1.11 (2017: 8.2), the functor**: the tangent `(TΦ, T𝚽) : T(X, 𝐗) → T(Y, 𝐘)` of an sc-smooth
functor, `TΦ` and `T𝚽` Part I's tangent maps. -/
def tangent (Φ : EpFunctor X Y) : EpFunctor X.tangentEpGroupoid Y.tangentEpGroupoid where
  obj := MPolyfold.tangentMap Φ.isScSmoothMap_obj
  mor := MPolyfold.tangentMap Φ.isScSmoothMap_mor
  src_mor v := MPolyfold.tangentMap_tangentMap_comm Y.isScSmoothMap_src Φ.isScSmoothMap_mor
    Φ.isScSmoothMap_obj X.isScSmoothMap_src (funext Φ.src_mor) v
  tgt_mor v := MPolyfold.tangentMap_tangentMap_comm Y.isScSmoothMap_tgt Φ.isScSmoothMap_mor
    Φ.isScSmoothMap_obj X.isScSmoothMap_tgt (funext Φ.tgt_mor) v
  mor_comp k h hkh := by
    have hkh' : X.tSrc k = X.tTgt h := hkh
    have hs : ∀ v, Y.tSrc (MPolyfold.tangentMap Φ.isScSmoothMap_mor v) =
        MPolyfold.tangentMap Φ.isScSmoothMap_obj (X.tSrc v) := fun v =>
      MPolyfold.tangentMap_tangentMap_comm Y.isScSmoothMap_src Φ.isScSmoothMap_mor
        Φ.isScSmoothMap_obj X.isScSmoothMap_src (funext Φ.src_mor) v
    have ht : ∀ v, Y.tTgt (MPolyfold.tangentMap Φ.isScSmoothMap_mor v) =
        MPolyfold.tangentMap Φ.isScSmoothMap_obj (X.tTgt v) := fun v =>
      MPolyfold.tangentMap_tangentMap_comm Y.isScSmoothMap_tgt Φ.isScSmoothMap_mor
        Φ.isScSmoothMap_obj X.isScSmoothMap_tgt (funext Φ.tgt_mor) v
    have hY : Y.tSrc (MPolyfold.tangentMap Φ.isScSmoothMap_mor k) =
        Y.tTgt (MPolyfold.tangentMap Φ.isScSmoothMap_mor h) := by rw [hs, ht, hkh']
    refine (Y.tComp_eq hY ?_ ?_).symm
    · rw [Y.tBase_tangentMap, Y.tBase_tangentMap, Y.tBase_tangentMap]
      change Φ.mor (X.tBase (X.tComp k h)) = Y.comp (Φ.mor (X.tBase k)) (Φ.mor (X.tBase h))
      rw [X.tBase_tComp hkh', Φ.mor_comp _ _ (X.src_tBase_eq hkh')]
    · change Y.tSrc (MPolyfold.tangentMap Φ.isScSmoothMap_mor (X.tComp k h)) = _
      rw [hs, hs, X.tSrc_tComp hkh']
  mor_unit a := MPolyfold.tangentMap_tangentMap_comm Φ.isScSmoothMap_mor X.isScSmoothMap_unit
    Y.isScSmoothMap_unit Φ.isScSmoothMap_obj (funext Φ.mor_unit) a
  isScSmoothMap_obj := MPolyfold.tangentMap_isScSmooth Φ.isScSmoothMap_obj
  isScSmoothMap_mor := MPolyfold.tangentMap_isScSmooth Φ.isScSmoothMap_mor

/-- **Theorem 8.1.11 (2017: 8.2)**: the tangent `(TΦ, T𝚽)` of an sc-smooth functor `(Φ, 𝚽) : (X, 𝐗) → (Y, 𝐘)`
is an sc-smooth functor `T(X, 𝐗) → T(Y, 𝐘)` (`EpFunctor.tangent`): `TΦ`, `T𝚽` are sc-smooth,
`T𝚽` is compatible with sources, targets, units and the composition (8.5). -/
theorem theorem_8_1_11 (Φ : EpFunctor X Y) :
    Φ.tangent.obj = MPolyfold.tangentMap Φ.isScSmoothMap_obj ∧
      Φ.tangent.mor = MPolyfold.tangentMap Φ.isScSmoothMap_mor ∧
      X.PObj.tangentPolyfold.IsScSmoothMap Y.PObj.tangentPolyfold Φ.tangent.obj ∧
      X.PMor.tangentPolyfold.IsScSmoothMap Y.PMor.tangentPolyfold Φ.tangent.mor ∧
      (∀ v, Y.tSrc (Φ.tangent.mor v) = Φ.tangent.obj (X.tSrc v)) ∧
      (∀ v, Y.tTgt (Φ.tangent.mor v) = Φ.tangent.obj (X.tTgt v)) ∧
      (∀ k h, X.tSrc k = X.tTgt h →
        Φ.tangent.mor (X.tComp k h) = Y.tComp (Φ.tangent.mor k) (Φ.tangent.mor h)) ∧
      (∀ a, Φ.tangent.mor (X.tUnit a) = Y.tUnit (Φ.tangent.obj a)) :=
  ⟨rfl, rfl, Φ.tangent.isScSmoothMap_obj, Φ.tangent.isScSmoothMap_mor, Φ.tangent.src_mor,
    Φ.tangent.tgt_mor, Φ.tangent.mor_comp, Φ.tangent.mor_unit⟩

end EpFunctor

/-! ### Theorem 8.1.12 (2017: 8.3): the tangent functor `T : EP → EP` -/

/-- The tangent `TX` of a bundled ep-groupoid (in `EP.{max u 1}`, Part I's `TangentSpace` of a
type in `Type (max u 1)` being again in `Type (max u 1)`). -/
def EP.tangent (A : EP.{max u 1}) : EP.{max u 1} where
  Obj := A.X.PObj.TangentSpace
  Mor := A.X.PMor.TangentSpace
  X := A.X.tangentEpGroupoid

/-- **Theorem 8.1.12 (2017: 8.3), the functor** `T : EP → EP`, `X ↦ TX`, `Φ ↦ TΦ`. -/
def tangentFunctor : EP.{max u 1} ⥤ EP.{max u 1} where
  obj A := A.tangent
  map Φ := EpFunctor.tangent Φ
  map_id _ := EpFunctor.ext MPolyfold.tangentMap_id MPolyfold.tangentMap_id
  map_comp Φ Ψ :=
    EpFunctor.ext (MPolyfold.tangentMap_comp Ψ.isScSmoothMap_obj Φ.isScSmoothMap_obj)
      (MPolyfold.tangentMap_comp Ψ.isScSmoothMap_mor Φ.isScSmoothMap_mor)

/-- **Theorem 8.1.12 (2017: 8.3) (functoriality of `T` on ep-groupoids)**: `T : EP → EP` (`tangentFunctor`) is
a functor associating with an ep-groupoid `X` its tangent `TX` and with an sc-smooth functor `Φ`
its tangent `TΦ`, which preserves the composition and the other structure maps (Theorem 8.1.11 (2017: 8.2)).
(Tameness, Lemma 8.1.9 (2017: 8.8), is not formalized here.) -/
theorem theorem_8_1_12 :
    (∀ A : EP.{max u 1}, (tangentFunctor.obj A).X = A.X.tangentEpGroupoid) ∧
      (∀ {A B : EP.{max u 1}} (Φ : A ⟶ B), (tangentFunctor.map Φ : EpFunctor _ _) =
        EpFunctor.tangent (X := A.X) (Y := B.X) Φ) ∧
      (∀ A : EP.{max u 1}, tangentFunctor.map (𝟙 A) = 𝟙 (tangentFunctor.obj A)) ∧
      (∀ {A B C : EP.{max u 1}} (Φ : A ⟶ B) (Ψ : B ⟶ C),
        tangentFunctor.map (Φ ≫ Ψ) = tangentFunctor.map Φ ≫ tangentFunctor.map Ψ) :=
  ⟨fun _ => rfl, fun _ => rfl, tangentFunctor.map_id, tangentFunctor.map_comp⟩

/-! ### Proposition 8.1.14 (2017: 8.1): tangents of natural transformations -/

namespace EpNatTrans

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Φ Ψ : EpFunctor X Y}

/-- The tangent `Tτ : TX → T𝐘` of a natural transformation `τ : Φ → Ψ`, a natural
transformation `TΦ → TΨ` (Proposition 8.1.14 (2017: 8.1)).  Naturality: both sides of the square lie over
`τ(t α) ∘ Φ(α) = Ψ(α) ∘ τ(s α)` and have the same `Ts`, namely `TΦ(s_T p)`. -/
def tangent (τ : EpNatTrans Φ Ψ) : EpNatTrans Φ.tangent Ψ.tangent where
  app := MPolyfold.tangentMap τ.isScSmoothMap_app
  isScSmoothMap_app := MPolyfold.tangentMap_isScSmooth τ.isScSmoothMap_app
  src_app a := MPolyfold.tangentMap_tangentMap_of_eq Y.isScSmoothMap_src τ.isScSmoothMap_app
    Φ.isScSmoothMap_obj (funext τ.src_app) a
  tgt_app a := MPolyfold.tangentMap_tangentMap_of_eq Y.isScSmoothMap_tgt τ.isScSmoothMap_app
    Ψ.isScSmoothMap_obj (funext τ.tgt_app) a
  naturality v := by
    have hsτ : ∀ a, Y.tSrc (MPolyfold.tangentMap τ.isScSmoothMap_app a) =
        MPolyfold.tangentMap Φ.isScSmoothMap_obj a := fun a =>
      MPolyfold.tangentMap_tangentMap_of_eq Y.isScSmoothMap_src τ.isScSmoothMap_app
        Φ.isScSmoothMap_obj (funext τ.src_app) a
    have htτ : ∀ a, Y.tTgt (MPolyfold.tangentMap τ.isScSmoothMap_app a) =
        MPolyfold.tangentMap Ψ.isScSmoothMap_obj a := fun a =>
      MPolyfold.tangentMap_tangentMap_of_eq Y.isScSmoothMap_tgt τ.isScSmoothMap_app
        Ψ.isScSmoothMap_obj (funext τ.tgt_app) a
    have h1 : Y.tSrc (MPolyfold.tangentMap τ.isScSmoothMap_app (X.tTgt v)) =
        Y.tTgt (Φ.tangent.mor v) := by
      rw [hsτ]
      exact (Φ.tangent.tgt_mor v).symm
    have h2 : Y.tSrc (Ψ.tangent.mor v) =
        Y.tTgt (MPolyfold.tangentMap τ.isScSmoothMap_app (X.tSrc v)) := by
      rw [htτ]
      exact Ψ.tangent.src_mor v
    change Y.tComp (MPolyfold.tangentMap τ.isScSmoothMap_app (X.tTgt v)) (Φ.tangent.mor v) =
      Y.tComp (Ψ.tangent.mor v) (MPolyfold.tangentMap τ.isScSmoothMap_app (X.tSrc v))
    refine Y.tangent_ext ?_ ?_
    · rw [Y.tBase_tComp h1, Y.tBase_tComp h2]
      change Y.comp (Y.tBase (MPolyfold.tangentMap τ.isScSmoothMap_app (X.tTgt v)))
          (Y.tBase (MPolyfold.tangentMap Φ.isScSmoothMap_mor v)) =
        Y.comp (Y.tBase (MPolyfold.tangentMap Ψ.isScSmoothMap_mor v))
          (Y.tBase (MPolyfold.tangentMap τ.isScSmoothMap_app (X.tSrc v)))
      rw [Y.tBase_tangentMap, Y.tBase_tangentMap, Y.tBase_tangentMap, Y.tBase_tangentMap,
        X.levelVal_tangentProj_tTgt, X.levelVal_tangentProj_tSrc]
      exact τ.naturality _
    · rw [Y.tSrc_tComp h1, Y.tSrc_tComp h2, hsτ]
      exact Φ.tangent.src_mor v

end EpNatTrans

/-- **Proposition 8.1.14 (2017: 8.1)**: if `τ : Φ → Ψ` is a natural transformation between sc-smooth functors
`Φ, Ψ : (X, 𝐗) → (Y, 𝐘)`, its tangent `Tτ : TX → T𝐘` is a natural transformation
`Tτ : TΦ → TΨ` (`EpNatTrans.tangent`); in particular `Φ ≃ Ψ` implies `TΦ ≃ TΨ`. -/
theorem proposition_8_1_14 {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Φ Ψ : EpFunctor X Y}
    (τ : EpNatTrans Φ Ψ) :
    ∃ Tτ : EpNatTrans Φ.tangent Ψ.tangent, Tτ.app = MPolyfold.tangentMap τ.isScSmoothMap_app ∧
      (Φ.NaturallyEquivalent Ψ → Φ.tangent.NaturallyEquivalent Ψ.tangent) :=
  ⟨τ.tangent, rfl, fun ⟨σ⟩ => ⟨σ.tangent⟩⟩

end Polyfold
