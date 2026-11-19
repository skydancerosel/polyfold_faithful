import Polyfold.Chapter2.TangentMap
import Polyfold.Chapter5.RestrictOpen
import Polyfold.Chapter7.LocalDiffeo
import Polyfold.Chapter2.TangentMapLocal
import Polyfold.Chapter5.SubtypeValSmooth

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II, Chapter 8,
§8.1, pp. 257–263: the tangent maps behind the structure maps (8.3), (8.5), (8.8) of the tangent
ep-groupoid and the proofs of Lemmas 8.1.2, 8.1.3, 8.1.5, 8.1.7 and 8.1.8 (2017: 8.1, 8.2, 8.4, 8.6 and 8.7) *(Part II has no 2014 preprint;
numbers and pages are those of the 2017 text)*.  Part I's tangent bundle `TX` and tangent map `Tf`
are `MPolyfold.TangentSpace` and `MPolyfold.tangentMap` (Part I, §2.2 [§2.1 of the 2017 text]).

# Tangents of maps sc-smooth on open sets, and of local sc-diffeomorphisms

## The text, paraphrased

(8.3) The source and target of the morphism `(φ, h) ∈ T_φ𝐗` are `Ts(φ)(h)` and `Tt(φ)(h)`.
(8.5) The product of `(ψ, k)` and `(φ, h)` is `(ψ ∘ φ, (Ts(ψ ∘ φ))⁻¹(Ts(φ)(h)))`, using that `s`
is a local sc-diffeomorphism; (8.8) the unit at `a ∈ T_xX` is `(1_x, Ts(1_x)⁻¹(a))`.  In the proofs
of Lemmas 8.1.2, 8.1.3 and 8.1.5 (2017: 8.1, 8.2 and 8.4) the text differentiates maps defined on open sets only, such as the
local inverse `(s|U(ψ))⁻¹` and `α = t ∘ (s|U(ψ ∘ φ))⁻¹`, applies the chain rule to them, and uses
that `t ∘ (s|U(1_x))⁻¹` is the identity near `x`, so that its tangent is the identity.  (Lemma 8.1.7 (2017: 8.6))
The source and target maps of the tangent are local sc-diffeomorphisms "by construction".
(Lemma 8.1.8 (2017: 8.7)) For open `U(φ)`, `U(x)` with `s : U(φ) → U(x)` an sc-diffeomorphism, the text uses that
`Ts : TU(φ) → TU(x)` is an sc-diffeomorphism, `TU` being the part of the tangent bundle over `U`.

## What is formalized (namespace `Polyfold.MPolyfold`)

* **`TU = p⁻¹(U)`**: `tangentPreimage P U` (`isOpen_tangentPreimage`, `tangentPreimage_univ`,
  `tangentPreimage_mono`, `tangentPreimage_inter`, `tangentChartSet_eq_tangentPreimage`,
  `tangentFiber_subset_tangentPreimage`), `tangentChartMap_image_tangentPreimage`
  (`Tφ(p⁻¹(s)) = T(φ(s))`); `exists_mem_levelSet_one` and `nonempty_tangentSpace` (an M-polyfold
  with a point has a point on level `1`, so `TX` is nonempty).
* **The image vector of a map sc-smooth on an open set** (Part I's construction with
  `U ∩ V ∩ f⁻¹(V')` in place of `V ∩ f⁻¹(V')`): `TangentPre.fdomOn`, `TangentPre.ftransportOn`,
  `ftransportOn_fst`, `ftransportOn_mem`, `ftransportOn_transport`, `ftransportOn_eq_of_transport`,
  `TangentPre.Rel.ftransportOn`, `ftransportOn_congr` (locality), `fimageOnWith`,
  `mk_fimageOnWith_eq`, `mk_fimageOnWith_eq_of_rel`, `fimageOn`.
* **`tangentMapOn hf : TX → TY`** for `hf : P.IsScSmoothOn Q f U` (`Tf` on `p⁻¹(U)`, junk off it):
  `tangentMapOn_mk`; projection `levelVal_tangentProj_tangentMapOn` (`p ∘ Tf = f ∘ p` on
  `p⁻¹(U)`), `tangentMapOn_mapsTo`, `tangentMapOn_mapsTo_fiber`; formula (5)
  `tangentChartMap_tangentMapOn`; locality `tangentMapOn_congr`, `tangentMapOn_mono`,
  `tangentMap_eqOn_of_eqOn`; comparison with Part I `tangentMapOn_eq_tangentMap`,
  `tangentMapOn_univ`; `tangentMapOn_id`, `tangentMapOn_eqOn_id`; the chain rule
  `tangentMapOn_comp`; `continuousOn_tangentMapOn` and `tangentMapOn_isScSmoothOn` (`Tf` is
  sc-smooth on `p⁻¹(U)` for the M-polyfold structures `tangentPolyfold`).
* **Sc-diffeomorphisms between open sets**: `IsScDiffeoOn.congr_left`, `IsScDiffeoOn.congr_right`,
  **`IsScDiffeoOn.tangent`** (`Tf : p⁻¹(U) → p⁻¹(V)` is an sc-diffeomorphism with inverse `Tg`:
  Lemma 8.1.8 (2017: 8.7)'s `Ts : TU(φ) → TU(x)`), `IsScDiffeoOn.tangentMap` (the same with Part I's `Tf` for a
  globally sc-smooth `f`), `IsScDiffeoOn.injOn_tangent`, `IsScDiffeoOn.image_tangent`,
  `IsScDiffeoOn.isOpen_image_tangent`, `IsScDiffeoOn.bijOn_tangentFiber`.
* **Local sc-diffeomorphisms**: **`IsLocalScDiffeo.tangentMap`** (`Tf : TX → TY` is a local
  sc-diffeomorphism: Lemma 8.1.7 (2017: 8.6)), `IsLocalScDiffeo.isLocalHomeomorph_tangentMap`,
  `IsLocalScDiffeo.isOpenMap_tangentMap`, `IsLocalScDiffeo.surjective_tangentMap` (for surjective
  `f`); **fibrewise bijectivity** `IsLocalScDiffeo.bijOn_tangentFiber` (`Tf : T_xX → T_{f(x)}Y` is a
  bijection, so that `(Ts(φ))⁻¹` in (8.5), (8.8) makes sense), `IsLocalScDiffeo.injOn_tangentFiber`,
  `IsLocalScDiffeo.tangentFiber_subset_image`.
* **`TU` for Part I's open sub-M-polyfold `restrictOpen`**: `isScSmoothMap_subtypeVal`,
  `openRetraction` with `isScSmoothOn_openRetraction`, `isScDiffeoOn_subtypeVal`,
  `isLocalScDiffeo_subtypeVal`, and `isScDiffeoOn_tangentMap_subtypeVal` (`Tι : TU → TX` is an
  sc-diffeomorphism onto `p⁻¹(U)`), `injective_tangentMap_subtypeVal`,
  `range_tangentMap_subtypeVal`, `isOpenEmbedding_tangentMap_subtypeVal`,
  `levelVal_tangentProj_tangentMap_subtypeVal`.

## What the text leaves implicit, and the choices made

* `TU` for an open `U ⊆ X` is read as the open subset `p⁻¹(U)` of `TX`, with the structure of an
  open subset; that it is also the tangent bundle of the M-polyfold `U` is
  `isScDiffeoOn_tangentMap_subtypeVal` (for `U ≠ ∅`, as Part I's `restrictOpen` needs a junk
  point).
* The tangent of a map defined on an open set only (`(s|U(ψ))⁻¹`, `α` in Lemma 8.1.3 (2017: 8.2)) is never
  defined in the text.  It is built here directly from the charts, as Part I builds `Tf`, and not
  through `restrictOpen`, which would need `U ≠ ∅` and maps between subtypes.  Off `p⁻¹(U)` it
  takes a junk value in `TY`, which is nonempty since `Y ∋ f(x)` is and a nonempty M-polyfold has
  points on level `1` (`exists_mem_levelSet_one`: `E₁` is dense in `E₀` and a partial quadrant is
  convex with nonempty interior, so every retract `O ≠ ∅` meets `E₁`).  The text does not need
  this; it only avoids a hypothesis `[Nonempty TY]`.
* The text's `Ts(φ)(h)` is Part I's `tangentMap hs` applied to the class of `h`; `φ` is its
  projection `p`.  `Ts(φ)⁻¹` is the inverse of the bijection of fibres of
  `IsLocalScDiffeo.bijOn_tangentFiber`; on a sheet `U(φ)` it is the tangent map of the local inverse
  restricted to the fibre (`IsScDiffeoOn.bijOn_tangentFiber`).  The linear structure of the fibres
  is not part of Part I's `TangentSpace` (point G.7), so linearity is not stated.
* Lemma 8.1.7 (2017: 8.6)'s "by construction" is `IsLocalScDiffeo.tangentMap`: a sheet of `Tf` around `v` is
  `p⁻¹(U)` for a sheet `U` of `f` around `p(v)`, with inverse the tangent of the local inverse.
  Surjectivity of `Tf` uses that of `f` (`IsLocalScDiffeo.surjective_tangentMap`).

Local tangent maps (`MPolyfold.tangentMapOn`, `MPolyfold.tangentMapOn_id`,
`MPolyfold.tangentMapOn_mk`, `MPolyfold.tangentPreimage`, …): `Chapter2/TangentMapLocal.lean`.

Smoothness of the subtype inclusion (`MPolyfold.isScSmoothMap_subtypeVal`):
`Chapter5/SubtypeValSmooth.lean`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

/-! ### `p⁻¹(U) ⊆ TX` -/

section Preimage

lemma mk_mem_tangentPreimage {U : Set X} {p : P.TangentPre} :
    TangentSpace.mk p ∈ P.tangentPreimage U ↔ p.x ∈ U := Iff.rfl

lemma isOpen_tangentPreimage {U : Set X} (hU : IsOpen U) : IsOpen (P.tangentPreimage U) :=
  hU.preimage continuous_levelVal_tangentProj

@[simp] lemma tangentPreimage_univ : P.tangentPreimage univ = univ := rfl

lemma tangentPreimage_mono {U U' : Set X} (h : U ⊆ U') :
    P.tangentPreimage U ⊆ P.tangentPreimage U' := fun _ hα => h hα

lemma tangentPreimage_inter (U U' : Set X) :
    P.tangentPreimage (U ∩ U') = P.tangentPreimage U ∩ P.tangentPreimage U' := rfl

lemma tangentChartSet_eq_tangentPreimage (φ : MChart X) :
    tangentChartSet (P := P) φ = P.tangentPreimage φ.source := rfl

end Preimage

/-! ### Level-one points and vectors exist -/

/-! ### The image vector of a map sc-smooth on an open set -/

namespace TangentPre

variable {f : X → Y} {U : Set X}

section FImage

variable (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U) {ψ : MChart Y}
  (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source)

lemma fimageOnWith_x : (fimageOnWith hf p hxU hψ hx).x = f p.x := rfl

end FImage

end TangentPre

/-! ### The tangent map `Tf : TU → TY` of a map sc-smooth on an open set `U` -/

section TangentMapOn

variable {f : X → Y} {U : Set X}

/-- Shrinking the open set does not change `Tf`. -/
theorem tangentMapOn_mono (hf : P.IsScSmoothOn Q f U) {U' : Set X} (hU' : IsOpen U')
    (hsub : U' ⊆ U) :
    EqOn (tangentMapOn (hf.mono hU' hsub)) (tangentMapOn hf) (P.tangentPreimage U') :=
  tangentMapOn_congr _ _ hU' subset_rfl hsub (eqOn_refl _ _)

/-- **Locality of Part I's `Tf`**: sc-smooth maps agreeing on an open `W` have the same tangent
map on `p⁻¹(W)`. -/
theorem tangentMap_eqOn_of_eqOn {g : X → Y} (hf : P.IsScSmoothMap Q f) (hg : P.IsScSmoothMap Q g)
    {W : Set X} (hW : IsOpen W) (hfg : EqOn f g W) :
    EqOn (tangentMap hf) (tangentMap hg) (P.tangentPreimage W) := fun α hα => by
  rw [← tangentMapOn_eq_tangentMap hf (hf.mono hW (subset_univ _)) hα,
    ← tangentMapOn_eq_tangentMap hg (hg.mono hW (subset_univ _)) hα]
  exact tangentMapOn_congr _ _ hW subset_rfl subset_rfl hfg hα

end TangentMapOn

/-! ### `Tf` is continuous and sc-smooth on `p⁻¹(U)` -/

section Smooth

variable {f : X → Y} {U : Set X}

/-- `Tφ(p⁻¹(s)) = T(φ(s))` for an open subset `s` of the domain of a chart `φ`. -/
theorem tangentChartMap_image_tangentPreimage {φ : MChart X} (hφ : P.IsChart φ) {s : Set X}
    (hs : s ⊆ φ.source) (hso : IsOpen s) :
    tangentChartMap hφ '' P.tangentPreimage s = retractTangent φ.model.E φ.model.C (φ '' s) := by
  ext a
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    have hγφ : γ ∈ tangentChartSet φ := hs hγ
    refine (TangentPre.mem_retractTangent_image_iff hs hso ?_).2 (tangentChartMap_mem hφ hγφ)
    rw [tangentChartMap_fst hφ hγφ, P.toBase_levelLift hφ hγφ (levelVal_mem _)]
    exact ⟨_, hγ, rfl⟩
  · intro ha
    have haO : a ∈ retractTangent φ.model.E φ.model.C φ.model.O :=
      (TangentPre.mem_retractTangent_image_iff hs hso
        (retractTangent_fst_mem (φ.isScRetract_image hs hso) ha)).1 ha
    refine ⟨TangentSpace.mk (TangentPre.ofVec hφ haO), ?_, tangentChartMap_mk_ofVec hφ haO⟩
    change φ.symm (φ.model.E.toBase 1 a.1) ∈ s
    obtain ⟨y, hy, hyeq⟩ := retractTangent_fst_mem (φ.isScRetract_image hs hso) ha
    rw [← hyeq, φ.symm_apply_apply (hs hy)]
    exact hy

/-- `Tf` is continuous on `p⁻¹(U)`: near `[(x, φ, h)]` it is `(Tψ)⁻¹ ∘ T(ψ ∘ f ∘ φ⁻¹) ∘ Tφ`. -/
theorem continuousOn_tangentMapOn (hf : P.IsScSmoothOn Q f U) :
    ContinuousOn (tangentMapOn hf) (P.tangentPreimage U) := by
  intro α hα
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  have hxU : p.x ∈ U := hα
  set φ := p.φ with hφdef
  have hφ : P.IsChart φ := p.isChart
  obtain ⟨ψ, hψ, hx⟩ := Q.exists_isChart_mem_source (f p.x)
  set s := TangentPre.fdomOn U φ f ψ with hs
  have hso : IsOpen s := TangentPre.isOpen_fdomOn hf φ ψ
  have hsφ : s ⊆ φ.source := TangentPre.fdomOn_subset _ _ _ _
  have hVo : IsOpen (P.tangentPreimage s) := isOpen_tangentPreimage hso
  have hαV : TangentSpace.mk p ∈ P.tangentPreimage s := ⟨⟨hxU, p.mem_source⟩, hx⟩
  set β₀ := tangentMapOn hf (TangentSpace.mk p) with hβ₀
  set T := retractTangentMap φ.model.E φ.model.C (φ '' s) (ψ ∘ f ∘ φ.symm) with hT
  have hsm := TangentPre.isScSmoothRetractMap_coordOn hf hφ hψ subset_rfl hso
  have hφs : IsScRetract φ.model.E φ.model.C (φ '' s) := φ.isScRetract_image hsφ hso
  -- on `p⁻¹(s)`, `Tf = (Tψ)⁻¹ ∘ T(ψ ∘ f ∘ φ⁻¹) ∘ Tφ`
  have heq : EqOn (tangentMapOn hf) (tangentChartInv hψ β₀ ∘ T ∘ tangentChartMap hφ)
      (P.tangentPreimage s) := by
    intro γ hγ
    have hγψ : tangentMapOn hf γ ∈ tangentChartSet ψ := by
      change Q.levelVal 1 (Q.tangentProj (tangentMapOn hf γ)) ∈ ψ.source
      rw [levelVal_tangentProj_tangentMapOn hf hγ.1.1]
      exact hγ.2
    simp only [Function.comp_apply, hT]
    rw [← tangentChartMap_tangentMapOn hf hφ hψ hγ]
    exact ((tangentChart hψ β₀).symm_apply_apply hγψ).symm
  have h1 : ContinuousOn (tangentChartMap hφ) (tangentChartSet φ) :=
    (tangentChart hφ (TangentSpace.mk p)).continuousOn_toFun
  have h2 : ContinuousOn T (retractTangent φ.model.E φ.model.C (φ '' s)) :=
    (hsm.tangent hφs ψ.model.isScRetract).continuousOn hφs.tangentSet
  have h3 : ContinuousOn (tangentChartInv hψ β₀) (retractTangent ψ.model.E ψ.model.C ψ.model.O) :=
    (tangentChart hψ β₀).continuousOn_invFun
  have hm1 : MapsTo (tangentChartMap hφ) (P.tangentPreimage s)
      (retractTangent φ.model.E φ.model.C (φ '' s)) := fun γ hγ => by
    rw [← tangentChartMap_image_tangentPreimage hφ hsφ hso]
    exact mem_image_of_mem _ hγ
  have hm2 : MapsTo T (retractTangent φ.model.E φ.model.C (φ '' s))
      (retractTangent ψ.model.E ψ.model.C ψ.model.O) :=
    hsm.tangentMap_mapsTo hφs ψ.model.isScRetract
  have hcont : ContinuousOn (tangentChartInv hψ β₀ ∘ T ∘ tangentChartMap hφ)
      (P.tangentPreimage s) :=
    h3.comp (h2.comp (h1.mono fun γ hγ => hsφ hγ) hm1) (hm2.comp hm1)
  exact ((hcont.congr heq).continuousAt (hVo.mem_nhds hαV)).continuousWithinAt

/-- **`Tf : p⁻¹(U) → TY` is sc-smooth**: in the charts `Tφ`, `Tψ` it is `T(ψ ∘ f ∘ φ⁻¹)`. -/
theorem tangentMapOn_isScSmoothOn (hf : P.IsScSmoothOn Q f U) :
    P.tangentPolyfold.IsScSmoothOn Q.tangentPolyfold (tangentMapOn hf) (P.tangentPreimage U) := by
  refine IsScSmoothOn.of_exists_charts (isOpen_tangentPreimage hf.isOpen)
    (continuousOn_tangentMapOn hf) fun α hα => ?_
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  have hxU : p.x ∈ U := hα
  set φ := p.φ with hφdef
  have hφ : P.IsChart φ := p.isChart
  obtain ⟨ψ, hψ, hx⟩ := Q.exists_isChart_mem_source (f p.x)
  set s := TangentPre.fdomOn U φ f ψ with hs
  have hso : IsOpen s := TangentPre.isOpen_fdomOn hf φ ψ
  have hsφ : s ⊆ φ.source := TangentPre.fdomOn_subset _ _ _ _
  have hTs : retractTangent φ.model.E φ.model.C (φ '' s) =
      tangentChart hφ (TangentSpace.mk p) '' P.tangentPreimage s :=
    (tangentChartMap_image_tangentPreimage hφ hsφ hso).symm
  refine ⟨tangentChart hφ (TangentSpace.mk p),
    tangentChart hψ (tangentMapOn hf (TangentSpace.mk p)), P.tangentPreimage s,
    P.tangentPolyfold_isChart hφ _, Q.tangentPolyfold_isChart hψ _, isOpen_tangentPreimage hso,
    ⟨⟨hxU, p.mem_source⟩, hx⟩, fun γ hγ => ⟨hγ.1.1, hγ.1.2⟩, ?_, ?_⟩
  · intro γ hγ
    change Q.levelVal 1 (Q.tangentProj (tangentMapOn hf γ)) ∈ ψ.source
    rw [levelVal_tangentProj_tangentMapOn hf hγ.1.1]
    exact hγ.2
  · rw [← hTs]
    refine ((TangentPre.isScSmoothRetractMap_coordOn hf hφ hψ subset_rfl hso).tangent
      (φ.isScRetract_image hsφ hso) ψ.model.isScRetract).congr fun a ha => ?_
    have haO : a ∈ retractTangent φ.model.E φ.model.C φ.model.O :=
      (TangentPre.mem_retractTangent_image_iff hsφ hso
        (retractTangent_fst_mem (φ.isScRetract_image hsφ hso) ha)).1 ha
    change _ = tangentChartMap hψ (tangentMapOn hf (tangentChartInv hφ _ a))
    rw [tangentChartInv_of_mem hφ _ haO]
    have hγ : TangentSpace.mk (TangentPre.ofVec hφ haO) ∈ P.tangentPreimage s := by
      change φ.symm (φ.model.E.toBase 1 a.1) ∈ s
      obtain ⟨y, hy, hyeq⟩ := retractTangent_fst_mem (φ.isScRetract_image hsφ hso) ha
      rw [← hyeq, φ.symm_apply_apply (hsφ hy)]
      exact hy
    rw [tangentChartMap_tangentMapOn hf hφ hψ hγ, tangentChartMap_mk_ofVec hφ haO]

end Smooth

/-! ### Sc-diffeomorphisms between open sets and local sc-diffeomorphisms -/

section Diffeo

variable {f f' : X → Y} {g g' : Y → X} {U : Set X} {V : Set Y}

/-- Only the values of `f` on `U` matter for an sc-diffeomorphism `f : U → V`. -/
theorem IsScDiffeoOn.congr_left (h : P.IsScDiffeoOn Q f g U V) (hff' : EqOn f f' U) :
    P.IsScDiffeoOn Q f' g U V where
  isScSmoothOn := h.isScSmoothOn.congr hff'
  isScSmoothOn_inv := h.isScSmoothOn_inv
  mapsTo x hx := hff' hx ▸ h.mapsTo hx
  mapsTo_inv := h.mapsTo_inv
  left_inv x hx := by rw [← hff' hx]; exact h.left_inv x hx
  right_inv y hy := by rw [← hff' (h.mapsTo_inv hy)]; exact h.right_inv y hy

/-- Only the values of the inverse `g` on `V` matter. -/
theorem IsScDiffeoOn.congr_right (h : P.IsScDiffeoOn Q f g U V) (hgg' : EqOn g g' V) :
    P.IsScDiffeoOn Q f g' U V :=
  (h.symm.congr_left hgg').symm

/-- **The tangent of an sc-diffeomorphism between open sets**: if `f : U → V` is an
sc-diffeomorphism with inverse `g`, then `Tf : p⁻¹(U) → p⁻¹(V)` is an sc-diffeomorphism with
inverse `Tg` (the text's "`Ts : TU(φ) → TU(x)` is an sc-diffeomorphism"). -/
theorem IsScDiffeoOn.tangent (h : P.IsScDiffeoOn Q f g U V) :
    P.tangentPolyfold.IsScDiffeoOn Q.tangentPolyfold (tangentMapOn h.isScSmoothOn)
      (tangentMapOn h.isScSmoothOn_inv) (P.tangentPreimage U) (Q.tangentPreimage V) where
  isScSmoothOn := tangentMapOn_isScSmoothOn h.isScSmoothOn
  isScSmoothOn_inv := tangentMapOn_isScSmoothOn h.isScSmoothOn_inv
  mapsTo := tangentMapOn_mapsTo h.isScSmoothOn h.mapsTo
  mapsTo_inv := tangentMapOn_mapsTo h.isScSmoothOn_inv h.mapsTo_inv
  left_inv α hα := by
    have h1 := tangentMapOn_comp h.isScSmoothOn_inv h.isScSmoothOn h.mapsTo hα
    rw [Function.comp_apply] at h1
    rw [← h1]
    exact tangentMapOn_eqOn_id _ (fun x hx => h.left_inv x hx) hα
  right_inv β hβ := by
    have h1 := tangentMapOn_comp h.isScSmoothOn h.isScSmoothOn_inv h.mapsTo_inv hβ
    rw [Function.comp_apply] at h1
    rw [← h1]
    exact tangentMapOn_eqOn_id _ (fun y hy => h.right_inv y hy) hβ

/-- The same with Part I's `Tf` for a globally sc-smooth `f` (the text's `Ts : TU(φ) → TU(x)` for
the source map `s` of an ep-groupoid). -/
theorem IsScDiffeoOn.tangentMap (h : P.IsScDiffeoOn Q f g U V) (hf : P.IsScSmoothMap Q f) :
    P.tangentPolyfold.IsScDiffeoOn Q.tangentPolyfold (MPolyfold.tangentMap hf)
      (tangentMapOn h.isScSmoothOn_inv) (P.tangentPreimage U) (Q.tangentPreimage V) :=
  h.tangent.congr_left (tangentMapOn_eq_tangentMap hf h.isScSmoothOn)

/-- `Tf` is injective on `p⁻¹(U)`. -/
theorem IsScDiffeoOn.injOn_tangent (h : P.IsScDiffeoOn Q f g U V) :
    InjOn (tangentMapOn h.isScSmoothOn) (P.tangentPreimage U) :=
  h.tangent.injOn

/-- `Tf(p⁻¹(U)) = p⁻¹(V)`. -/
theorem IsScDiffeoOn.image_tangent (h : P.IsScDiffeoOn Q f g U V) :
    tangentMapOn h.isScSmoothOn '' P.tangentPreimage U = Q.tangentPreimage V :=
  h.tangent.image_eq

/-- `Tf` maps open subsets of `p⁻¹(U)` to open subsets of `TY`. -/
theorem IsScDiffeoOn.isOpen_image_tangent (h : P.IsScDiffeoOn Q f g U V)
    {A : Set P.TangentSpace} (hA : IsOpen A) (hAU : A ⊆ P.tangentPreimage U) :
    IsOpen (tangentMapOn h.isScSmoothOn '' A) :=
  h.tangent.toOpenPartialHomeomorph.isOpen_image_of_subset_source hA hAU

/-- **Fibrewise bijectivity**: for `x ∈ U ∩ X₁`, `Tf : T_xX → T_{f(x)}Y` is a bijection. -/
theorem IsScDiffeoOn.bijOn_tangentFiber (h : P.IsScDiffeoOn Q f g U V) (x : P.Level 1)
    (hx : P.levelVal 1 x ∈ U) (y : Q.Level 1) (hxy : f (P.levelVal 1 x) = Q.levelVal 1 y) :
    BijOn (tangentMapOn h.isScSmoothOn) (P.tangentFiber x) (Q.tangentFiber y) := by
  have hT := h.tangent
  have hxsub : P.tangentFiber x ⊆ P.tangentPreimage U := tangentFiber_subset_tangentPreimage hx
  have hyV : Q.levelVal 1 y ∈ V := hxy ▸ h.mapsTo hx
  have hysub : Q.tangentFiber y ⊆ Q.tangentPreimage V := tangentFiber_subset_tangentPreimage hyV
  refine ⟨tangentMapOn_mapsTo_fiber h.isScSmoothOn x hx y hxy, hT.injOn.mono hxsub, ?_⟩
  intro β hβ
  refine ⟨tangentMapOn h.isScSmoothOn_inv β, ?_, hT.right_inv β (hysub hβ)⟩
  have hβy : Q.tangentProj β = y := hβ
  change P.tangentProj (tangentMapOn h.isScSmoothOn_inv β) = x
  apply level_ext
  rw [levelVal_tangentProj_tangentMapOn h.isScSmoothOn_inv (hysub hβ), hβy, ← hxy,
    h.left_inv _ hx]

/-- **The tangent of a local sc-diffeomorphism is a local sc-diffeomorphism** `TX → TY`: on
`p⁻¹(U)`, for a sheet `f : U → V` with inverse `g`, it is the sc-diffeomorphism `Tf` with inverse
`Tg`. -/
theorem IsLocalScDiffeo.tangentMap (hf : P.IsLocalScDiffeo Q f) :
    P.tangentPolyfold.IsLocalScDiffeo Q.tangentPolyfold (MPolyfold.tangentMap hf.isScSmoothMap) :=
  fun α => by
    obtain ⟨U, V, g, hx, hd⟩ := hf (P.levelVal 1 (P.tangentProj α))
    exact ⟨P.tangentPreimage U, Q.tangentPreimage V, tangentMapOn hd.isScSmoothOn_inv, hx,
      hd.tangentMap hf.isScSmoothMap⟩

/-- The tangent map of a local sc-diffeomorphism is a local homeomorphism. -/
theorem IsLocalScDiffeo.isLocalHomeomorph_tangentMap (hf : P.IsLocalScDiffeo Q f) :
    IsLocalHomeomorph (MPolyfold.tangentMap hf.isScSmoothMap) :=
  hf.tangentMap.isLocalHomeomorph

/-- The tangent map of a local sc-diffeomorphism is an open map. -/
theorem IsLocalScDiffeo.isOpenMap_tangentMap (hf : P.IsLocalScDiffeo Q f) :
    IsOpenMap (MPolyfold.tangentMap hf.isScSmoothMap) :=
  hf.tangentMap.isOpenMap

/-- The tangent map of a surjective local sc-diffeomorphism is surjective. -/
theorem IsLocalScDiffeo.surjective_tangentMap (hf : P.IsLocalScDiffeo Q f)
    (hsurj : Surjective f) : Surjective (MPolyfold.tangentMap hf.isScSmoothMap) := fun β => by
  obtain ⟨x, hx⟩ := hsurj (Q.levelVal 1 (Q.tangentProj β))
  obtain ⟨U, V, g, hxU, hd⟩ := hf x
  have hβ : β ∈ Q.tangentPreimage V := by
    change Q.levelVal 1 (Q.tangentProj β) ∈ V
    rw [← hx]
    exact hd.mapsTo hxU
  have hT := hd.tangent
  refine ⟨tangentMapOn hd.isScSmoothOn_inv β, ?_⟩
  rw [← tangentMapOn_eq_tangentMap hf.isScSmoothMap hd.isScSmoothOn (hT.mapsTo_inv hβ)]
  exact hT.right_inv β hβ

/-- **Fibrewise bijectivity**: for a local sc-diffeomorphism `f` and `x ∈ X₁`,
`Tf : T_xX → T_{f(x)}Y` is a bijection. -/
theorem IsLocalScDiffeo.bijOn_tangentFiber (hf : P.IsLocalScDiffeo Q f) (x : P.Level 1)
    (y : Q.Level 1) (hxy : f (P.levelVal 1 x) = Q.levelVal 1 y) :
    BijOn (MPolyfold.tangentMap hf.isScSmoothMap) (P.tangentFiber x) (Q.tangentFiber y) := by
  obtain ⟨U, V, g, hxU, hd⟩ := hf (P.levelVal 1 x)
  exact (hd.bijOn_tangentFiber x hxU y hxy).congr
    ((tangentMapOn_eq_tangentMap hf.isScSmoothMap hd.isScSmoothOn).mono
      (tangentFiber_subset_tangentPreimage hxU))

/-- `Tf` is injective on `T_xX`. -/
theorem IsLocalScDiffeo.injOn_tangentFiber (hf : P.IsLocalScDiffeo Q f) (x : P.Level 1) :
    InjOn (MPolyfold.tangentMap hf.isScSmoothMap) (P.tangentFiber x) :=
  (hf.bijOn_tangentFiber x (Q.levelMk 1 _ (hf.isScSmoothMap.mapsTo_levelSet 1 (levelVal_mem x)))
    rfl).injOn

/-- Every vector of `T_{f(x)}Y` is the image of a vector of `T_xX`. -/
theorem IsLocalScDiffeo.tangentFiber_subset_image (hf : P.IsLocalScDiffeo Q f) (x : P.Level 1)
    (y : Q.Level 1) (hxy : f (P.levelVal 1 x) = Q.levelVal 1 y) :
    Q.tangentFiber y ⊆ MPolyfold.tangentMap hf.isScSmoothMap '' P.tangentFiber x :=
  (hf.bijOn_tangentFiber x y hxy).surjOn

end Diffeo

/-! ### The tangent of an open subset: `TU = p⁻¹(U)` -/

section OpenSubset

variable {U : Set X} (hU : IsOpen U) [Nonempty U] [ParacompactSpace U]

open scoped Classical in
variable (U) in
/-- The map `X → U`, `x ↦ x` on `U` (a junk point of `U` off `U`). -/
def openRetraction : X → U := fun x => if h : x ∈ U then ⟨x, h⟩ else Classical.arbitrary U

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [ParacompactSpace U] in
lemma openRetraction_of_mem {x : X} (hx : x ∈ U) : openRetraction U x = ⟨x, hx⟩ := dif_pos hx

omit [T2Space X] [ParacompactSpace X] [ParacompactSpace U] in
lemma continuousOn_openRetraction : ContinuousOn (openRetraction U) U := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : U.domRestrict (openRetraction U) = id := funext fun x => openRetraction_of_mem x.2
  rw [this]
  exact continuous_id

include hU in
/-- `x ↦ x`, `X ⊇ U → U`, is sc-smooth on `U`. -/
theorem isScSmoothOn_openRetraction :
    P.IsScSmoothOn (P.restrictOpen hU) (openRetraction U) U := by
  refine IsScSmoothOn.of_exists_charts hU continuousOn_openRetraction fun x hx => ?_
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  set φ' := φ.restrict (s := φ.source ∩ U) inter_subset_left (φ.isOpen_source.inter hU) with hφ'
  have hφ'c : P.IsChart φ' := MPolyfold.IsChart.restrict P hφ _ _
  set φ'' := φ'.restrictTo (V := U) inter_subset_right with hφ''
  have hφ''c : (P.restrictOpen hU).IsChart φ'' := isChart_restrictTo hU hφ'c inter_subset_right
  refine ⟨φ', φ'', φ'.source, hφ'c, hφ''c, φ'.isOpen_source, ⟨hxφ, hx⟩,
    fun y hy => ⟨hy.2, hy⟩, fun y hy => ?_, ?_⟩
  · change (openRetraction U y).1 ∈ φ'.source
    rw [openRetraction_of_mem hy.2]
    exact hy
  · refine ((isScSmoothRetractMap_id _).mono_target
      fun z hz => φ'.image_subset_model subset_rfl hz).congr ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, id, φ'.symm_apply_apply hy, openRetraction_of_mem hy.2]
    rfl

include hU in
/-- The inclusion `U → X` is an sc-diffeomorphism onto the open set `U`. -/
theorem isScDiffeoOn_subtypeVal :
    (P.restrictOpen hU).IsScDiffeoOn P Subtype.val (openRetraction U) univ U where
  isScSmoothOn := isScSmoothMap_subtypeVal hU
  isScSmoothOn_inv := isScSmoothOn_openRetraction hU
  mapsTo v _ := v.2
  mapsTo_inv _ _ := mem_univ _
  left_inv v _ := openRetraction_of_mem v.2
  right_inv x hx := by rw [openRetraction_of_mem hx]

include hU in
/-- The inclusion `U → X` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_subtypeVal :
    (P.restrictOpen hU).IsLocalScDiffeo P (Subtype.val : U → X) := fun _ =>
  ⟨univ, U, openRetraction U, mem_univ _, isScDiffeoOn_subtypeVal hU⟩

/-- **`TU = p⁻¹(U)`**: the tangent map `Tι : TU → TX` of the inclusion is an sc-diffeomorphism
of `TU` onto the open set `p⁻¹(U)`, with inverse the tangent map of `x ↦ x` on `U`. -/
theorem isScDiffeoOn_tangentMap_subtypeVal :
    (P.restrictOpen hU).tangentPolyfold.IsScDiffeoOn P.tangentPolyfold
      (tangentMap (isScSmoothMap_subtypeVal hU)) (tangentMapOn (isScSmoothOn_openRetraction hU))
      univ (P.tangentPreimage U) :=
  ((isScDiffeoOn_subtypeVal (P := P) hU).tangent).congr_left fun α _ =>
    tangentMapOn_eq_tangentMap (isScSmoothMap_subtypeVal hU) _ (mem_univ α)

/-- `Tι : TU → TX` is injective. -/
theorem injective_tangentMap_subtypeVal :
    Injective (tangentMap (isScSmoothMap_subtypeVal (P := P) hU)) := fun α β h =>
  (isScDiffeoOn_tangentMap_subtypeVal hU).injOn (mem_univ α) (mem_univ β) h

/-- The range of `Tι : TU → TX` is `p⁻¹(U)`. -/
theorem range_tangentMap_subtypeVal :
    range (tangentMap (isScSmoothMap_subtypeVal (P := P) hU)) = P.tangentPreimage U := by
  rw [← image_univ]
  exact (isScDiffeoOn_tangentMap_subtypeVal hU).image_eq

/-- `Tι : TU → TX` is an open embedding. -/
theorem isOpenEmbedding_tangentMap_subtypeVal :
    IsOpenEmbedding (tangentMap (isScSmoothMap_subtypeVal (P := P) hU)) :=
  .of_continuous_injective_isOpenMap (continuous_tangentMap _) (injective_tangentMap_subtypeVal hU)
    fun _ hA => (isScDiffeoOn_tangentMap_subtypeVal hU).toOpenPartialHomeomorph
      |>.isOpen_image_of_subset_source hA (subset_univ _)

/-- `Tι` covers `ι`: `p(Tι(v)) = p(v)`. -/
theorem levelVal_tangentProj_tangentMap_subtypeVal (α : (P.restrictOpen hU).TangentSpace) :
    P.levelVal 1 (P.tangentProj (tangentMap (isScSmoothMap_subtypeVal hU) α)) =
      ((P.restrictOpen hU).levelVal 1 ((P.restrictOpen hU).tangentProj α) : X) :=
  levelVal_tangentProj_tangentMap _ α

end OpenSubset

end MPolyfold

end Polyfold
