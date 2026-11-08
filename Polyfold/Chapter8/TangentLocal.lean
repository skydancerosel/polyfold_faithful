import Polyfold.Chapter2.TangentMap
import Polyfold.Chapter3.RestrictOpen
import Polyfold.Chapter7.LocalDiffeo

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II, Chapter 8,
§8.1, pp. 257–263: the tangent maps behind the structure maps (8.3), (8.5), (8.8) of the tangent
ep-groupoid and the proofs of Lemmas 8.1, 8.2, 8.4, 8.6 and 8.7 *(Part II has no 2014 preprint;
numbers and pages are those of the 2017 text)*.  Part I's tangent bundle `TX` and tangent map `Tf`
are `MPolyfold.TangentSpace` and `MPolyfold.tangentMap` (Part I, §2.2 [§2.1 of the 2017 text]).

# Tangents of maps sc-smooth on open sets, and of local sc-diffeomorphisms

## The text, paraphrased

(8.3) The source and target of the morphism `(φ, h) ∈ T_φ𝐗` are `Ts(φ)(h)` and `Tt(φ)(h)`.
(8.5) The product of `(ψ, k)` and `(φ, h)` is `(ψ ∘ φ, (Ts(ψ ∘ φ))⁻¹(Ts(φ)(h)))`, using that `s`
is a local sc-diffeomorphism; (8.8) the unit at `a ∈ T_xX` is `(1_x, Ts(1_x)⁻¹(a))`.  In the proofs
of Lemmas 8.1, 8.2 and 8.4 the text differentiates maps defined on open sets only, such as the
local inverse `(s|U(ψ))⁻¹` and `α = t ∘ (s|U(ψ ∘ φ))⁻¹`, applies the chain rule to them, and uses
that `t ∘ (s|U(1_x))⁻¹` is the identity near `x`, so that its tangent is the identity.  (Lemma 8.6)
The source and target maps of the tangent are local sc-diffeomorphisms "by construction".
(Lemma 8.7) For open `U(φ)`, `U(x)` with `s : U(φ) → U(x)` an sc-diffeomorphism, the text uses that
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
  Lemma 8.7's `Ts : TU(φ) → TU(x)`), `IsScDiffeoOn.tangentMap` (the same with Part I's `Tf` for a
  globally sc-smooth `f`), `IsScDiffeoOn.injOn_tangent`, `IsScDiffeoOn.image_tangent`,
  `IsScDiffeoOn.isOpen_image_tangent`, `IsScDiffeoOn.bijOn_tangentFiber`.
* **Local sc-diffeomorphisms**: **`IsLocalScDiffeo.tangentMap`** (`Tf : TX → TY` is a local
  sc-diffeomorphism: Lemma 8.6), `IsLocalScDiffeo.isLocalHomeomorph_tangentMap`,
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
* The tangent of a map defined on an open set only (`(s|U(ψ))⁻¹`, `α` in Lemma 8.2) is never
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
  is not part of Part I's `TangentSpace` (gap G.7), so linearity is not stated.
* Lemma 8.6's "by construction" is `IsLocalScDiffeo.tangentMap`: a sheet of `Tf` around `v` is
  `p⁻¹(U)` for a sheet `U` of `f` around `p(v)`, with inverse the tangent of the local inverse.
  Surjectivity of `Tf` uses that of `f` (`IsLocalScDiffeo.surjective_tangentMap`).
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

variable (P) in
/-- The part `p⁻¹(U) = {v ∈ TX | p(v) ∈ U}` of `TX` over a subset `U ⊆ X` (the text's `TU`). -/
def tangentPreimage (U : Set X) : Set P.TangentSpace :=
  {α | P.levelVal 1 (P.tangentProj α) ∈ U}

lemma mem_tangentPreimage {U : Set X} {α : P.TangentSpace} :
    α ∈ P.tangentPreimage U ↔ P.levelVal 1 (P.tangentProj α) ∈ U := Iff.rfl

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

lemma tangentFiber_subset_tangentPreimage {U : Set X} {x : P.Level 1}
    (hx : P.levelVal 1 x ∈ U) : P.tangentFiber x ⊆ P.tangentPreimage U := fun α hα => by
  change P.levelVal 1 (P.tangentProj α) ∈ U
  rw [show P.tangentProj α = x from hα]
  exact hx

end Preimage

/-! ### Level-one points and vectors exist -/

variable (P) in
/-- An M-polyfold with a point has a point on level `1` (the points of `O ∩ E₁` are dense in a
retract `O`, by the density of `E₁` in `E₀`). -/
theorem exists_mem_levelSet_one (x : X) : (P.levelSet 1).Nonempty := by
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source x
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  have hxU : φ x ∈ R.U := R.retract_subset (hR ▸ φ.mapsTo_model x hx)
  obtain ⟨W, hW, hWU⟩ := R.relOpen.relOpen
  have hC := R.relOpen.isPartialQuadrant
  rw [hWU] at hxU
  have hint : (interior φ.model.C).Nonempty := hC.interior_lvlSet_nonempty 0
  have hcl : φ x ∈ closure (interior φ.model.C) := by
    rw [hC.convex.closure_interior_eq_closure_of_nonempty_interior hint]
    exact subset_closure hxU.2
  obtain ⟨z, hzW, hzC⟩ := mem_closure_iff.1 hcl W hW hxU.1
  obtain ⟨z₁, hz₁⟩ := (φ.model.E.denseRange_incl 0).exists_mem_open
    (hW.inter _root_.isOpen_interior) ⟨z, hzW, hzC⟩
  have hz₁U : z₁ ∈ φ.model.E.lvlSet R.U 1 := by
    change φ.model.E.toBase 1 z₁ ∈ R.U
    rw [hWU]
    exact ⟨hz₁.1, interior_subset hz₁.2⟩
  have hRz : R (φ.model.E.toBase 1 z₁) ∈ φ.model.O := hR ▸ R.apply_mem_retract hz₁U
  refine ⟨φ.symm (R (φ.model.E.toBase 1 z₁)), (P.mem_levelSet_iff hφ (φ.symm_mapsTo hRz)).2 ?_⟩
  rw [φ.apply_symm_apply hRz]
  exact ⟨levelMap R 1 z₁, R.isSc1.isSc0.toBase_levelMap hz₁U⟩

variable (P) in
/-- `TX` is nonempty as soon as `X` is: the zero vector at a point of `X₁`. -/
theorem nonempty_tangentSpace (x : X) : Nonempty P.TangentSpace := by
  obtain ⟨y, hy⟩ := P.exists_mem_levelSet_one x
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  refine ⟨TangentSpace.mk ⟨y, φ, 0, hφ, hyφ, hy, mk_zero_mem_retractTangent φ.model.isScRetract ?_⟩⟩
  change φ.model.E.toBase 1 (levelLift φ 1 y) ∈ φ.model.O
  rw [P.toBase_levelLift hφ hyφ hy]
  exact φ.mapsTo_model y hyφ


/-! ### The image vector of a map sc-smooth on an open set -/

namespace TangentPre

variable {f : X → Y} {U : Set X}

/-- The domain `U ∩ V ∩ f⁻¹(V')` of the coordinate representation `ψ ∘ f ∘ φ⁻¹` of a map
considered on the open set `U`. -/
def fdomOn (U : Set X) (φ : MChart X) (f : X → Y) (ψ : MChart Y) : Set X :=
  U ∩ φ.source ∩ f ⁻¹' ψ.source

omit [T2Space X] [ParacompactSpace X] [T2Space Y] [ParacompactSpace Y] in
lemma fdomOn_univ (φ : MChart X) (f : X → Y) (ψ : MChart Y) : fdomOn univ φ f ψ = fdom φ f ψ := by
  simp only [fdomOn, fdom, univ_inter]

omit [T2Space X] [ParacompactSpace X] [T2Space Y] [ParacompactSpace Y] in
lemma fdomOn_subset (U : Set X) (φ : MChart X) (f : X → Y) (ψ : MChart Y) :
    fdomOn U φ f ψ ⊆ φ.source := fun _ hy => hy.1.2

lemma isOpen_fdomOn (hf : P.IsScSmoothOn Q f U) (φ : MChart X) (ψ : MChart Y) :
    IsOpen (fdomOn U φ f ψ) :=
  (hf.continuousOn.mono inter_subset_left).isOpen_inter_preimage (hf.isOpen.inter φ.isOpen_source)
    ψ.isOpen_source

/-- `ψ ∘ f ∘ φ⁻¹` is sc-smooth on `φ(s)` for every open `s ⊆ U ∩ V ∩ f⁻¹(V')`. -/
lemma isScSmoothRetractMap_coordOn (hf : P.IsScSmoothOn Q f U) {φ : MChart X} {ψ : MChart Y}
    (hφ : P.IsChart φ) (hψ : Q.IsChart ψ) {s : Set X} (hs : s ⊆ fdomOn U φ f ψ) (hso : IsOpen s) :
    IsScSmoothRetractMap φ.model.E φ.model.C (φ '' s) ψ.model.E ψ.model.C ψ.model.O
      (ψ ∘ f ∘ φ.symm) :=
  hf.smooth φ ψ hφ hψ s hso (fun _ hy => (hs hy).1) fun _ hy => (hs hy).2

/-- The image of `(x, φ, h)` under `f` (sc-smooth on `U ∋ x`) in the chart `ψ` of `Y`:
`T(ψ ∘ f ∘ φ⁻¹)(φ(x), h)`, the tangent map computed on `φ(U ∩ V ∩ f⁻¹(V'))`. -/
def ftransportOn (p : P.TangentPre) (U : Set X) (f : X → Y) (ψ : MChart Y) :
    ψ.model.E.tangent 0 :=
  retractTangentMap p.φ.model.E p.φ.model.C (p.φ '' fdomOn U p.φ f ψ) (ψ ∘ f ∘ p.φ.symm) p.vec

lemma vec_mem_fdomOn (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U)
    {ψ : MChart Y} (hx : f p.x ∈ ψ.source) :
    p.vec ∈ retractTangent p.φ.model.E p.φ.model.C (p.φ '' fdomOn U p.φ f ψ) :=
  p.vec_mem_image (fdomOn_subset _ _ _ _) (isOpen_fdomOn hf p.φ ψ) ⟨⟨hxU, p.mem_source⟩, hx⟩

lemma ftransportOn_mem (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U)
    {ψ : MChart Y} (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source) :
    p.ftransportOn U f ψ ∈ retractTangent ψ.model.E ψ.model.C ψ.model.O :=
  (isScSmoothRetractMap_coordOn hf p.isChart hψ subset_rfl
    (isOpen_fdomOn hf p.φ ψ)).tangentMap_mapsTo
    (p.φ.isScRetract_image (fdomOn_subset _ _ _ _) (isOpen_fdomOn hf p.φ ψ)) ψ.model.isScRetract
    (vec_mem_fdomOn hf p hxU hx)

/-- The base point of the image vector is `ψ(f(x))`. -/
lemma ftransportOn_fst (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U)
    {ψ : MChart Y} (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source) :
    (p.ftransportOn U f ψ).1 = levelLift ψ 1 (f p.x) := by
  have hso := isOpen_fdomOn hf p.φ ψ
  have hsm := isScSmoothRetractMap_coordOn hf p.isChart hψ subset_rfl hso
  obtain ⟨R, hR⟩ := p.φ.isScRetract_image (fdomOn_subset U p.φ f ψ) hso
  have hmem := vec_mem_fdomOn hf p hxU hx
  rw [ftransportOn, retractTangentMap_apply hsm R hR hmem]
  apply ψ.model.E.toBase_injective 1
  have hsc : IsSc0 p.φ.model.E ψ.model.E R.U ((ψ ∘ f ∘ p.φ.symm) ∘ R) :=
    (hsm.comp_isScSmooth R hR).isSc1.isSc0
  have h1 : p.vec.1 ∈ p.φ.model.E.lvlSet R.U 1 := by
    apply R.lvlSet_retract_subset 1
    rw [hR]
    exact retractTangent_fst_mem (p.φ.isScRetract_image (fdomOn_subset U p.φ f ψ) hso) hmem
  have h2 : p.φ p.x ∈ R.retract := by rw [hR]; exact ⟨p.x, ⟨⟨hxU, p.mem_source⟩, hx⟩, rfl⟩
  have hfx1 : f p.x ∈ Q.levelSet 1 := hf.mapsTo_levelSet 1 ⟨hxU, p.mem_level⟩
  rw [hsc.toBase_levelMap h1, Function.comp_apply, p.toBase_vec_fst,
    R.apply_eq_self_of_mem_retract h2, Function.comp_apply, Function.comp_apply,
    p.φ.symm_apply_apply p.mem_source, Q.toBase_levelLift hψ hx hfx1]

/-- Changing the chart of `Y`: `T(ψ₂ ∘ ψ₁⁻¹)` carries the image vector in `ψ₁` to the image vector
in `ψ₂`. -/
theorem ftransportOn_transport (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U)
    {ψ₁ ψ₂ : MChart Y} (hψ₁ : Q.IsChart ψ₁) (hψ₂ : Q.IsChart ψ₂) (hx₁ : f p.x ∈ ψ₁.source)
    (hx₂ : f p.x ∈ ψ₂.source) :
    retractTangentMap ψ₁.model.E ψ₁.model.C (ψ₁.overlap ψ₂) (ψ₁.transition ψ₂)
      (p.ftransportOn U f ψ₁) = p.ftransportOn U f ψ₂ := by
  set t := fdomOn U p.φ f ψ₁ ∩ fdomOn U p.φ f ψ₂ with ht
  have hs₁o : IsOpen (fdomOn U p.φ f ψ₁) := isOpen_fdomOn hf p.φ ψ₁
  have hs₂o : IsOpen (fdomOn U p.φ f ψ₂) := isOpen_fdomOn hf p.φ ψ₂
  have hto : IsOpen t := hs₁o.inter hs₂o
  have hxt : p.x ∈ t := ⟨⟨⟨hxU, p.mem_source⟩, hx₁⟩, ⟨⟨hxU, p.mem_source⟩, hx₂⟩⟩
  have hG : IsScSmoothRetractMap ψ₁.model.E ψ₁.model.C (ψ₁.overlap ψ₂) ψ₂.model.E ψ₂.model.C
      ψ₂.model.O (ψ₁.transition ψ₂) :=
    (hψ₁.compatible hψ₂ (P := Q)).1.mono_target fun _ hz =>
      ψ₂.overlap_subset ψ₁ (ψ₁.transition_mapsTo ψ₂ hz)
  have hFt : MapsTo (ψ₁ ∘ f ∘ p.φ.symm) (p.φ '' t) (ψ₁.overlap ψ₂) := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.1.2]
    exact ⟨f y, ⟨hy.1.2, hy.2.2⟩, rfl⟩
  exact (p.φ.retractTangentMap_comp_image (fdomOn_subset _ _ _ _) hs₁o (fdomOn_subset _ _ _ _) hs₂o
    inter_subset_left inter_subset_right hto (ψ₁.isScRetract_overlap ψ₂)
    (isScSmoothRetractMap_coordOn hf p.isChart hψ₁ subset_rfl hs₁o) hFt hG
    (isScSmoothRetractMap_coordOn hf p.isChart hψ₂ subset_rfl hs₂o)
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.1.2, MChart.transition,
        ψ₁.symm_apply_apply hy.1.2])
    (p.vec_mem_image (fun y hy => hy.1.1.2) hto hxt)).symm

/-- The image vector computed from the vector seen in any chart `φ'` of `X` around `x`. -/
theorem ftransportOn_eq_of_transport (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre)
    (hxU : p.x ∈ U) {φ' : MChart X} (hφ' : P.IsChart φ') (hxφ' : p.x ∈ φ'.source) {ψ : MChart Y}
    (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source) :
    p.ftransportOn U f ψ = retractTangentMap φ'.model.E φ'.model.C (φ' '' fdomOn U φ' f ψ)
      (ψ ∘ f ∘ φ'.symm) (p.transport φ') := by
  set t := (p.φ.source ∩ φ'.source) ∩ fdomOn U p.φ f ψ with ht
  have hs₁o : IsOpen (p.φ.source ∩ φ'.source) := p.φ.isOpen_source.inter φ'.isOpen_source
  have hs₂o : IsOpen (fdomOn U p.φ f ψ) := isOpen_fdomOn hf p.φ ψ
  have hto : IsOpen t := hs₁o.inter hs₂o
  have hxt : p.x ∈ t := ⟨⟨p.mem_source, hxφ'⟩, ⟨⟨hxU, p.mem_source⟩, hx⟩⟩
  have hO₁' : IsScRetract φ'.model.E φ'.model.C (φ' '' fdomOn U φ' f ψ) :=
    φ'.isScRetract_image (fdomOn_subset _ _ _ _) (isOpen_fdomOn hf φ' ψ)
  have hF : IsScSmoothRetractMap p.φ.model.E p.φ.model.C (p.φ '' (p.φ.source ∩ φ'.source))
      φ'.model.E φ'.model.C (φ'.overlap p.φ) (p.φ.transition φ') :=
    (p.isChart.compatible hφ' (P := P)).1
  have hFt : MapsTo (p.φ.transition φ') (p.φ '' t) (φ' '' fdomOn U φ' f ψ) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [p.φ.transition_apply φ' hy.1.1]
    exact ⟨y, ⟨⟨hy.2.1.1, hy.1.2⟩, hy.2.2⟩, rfl⟩
  exact p.φ.retractTangentMap_comp_image inter_subset_left hs₁o (fdomOn_subset _ _ _ _) hs₂o
    inter_subset_left inter_subset_right hto hO₁' hF hFt
    (isScSmoothRetractMap_coordOn hf hφ' hψ subset_rfl (isOpen_fdomOn hf φ' ψ))
    (isScSmoothRetractMap_coordOn hf p.isChart hψ subset_rfl hs₂o)
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.1, p.φ.transition_apply φ' hy.1.1,
        φ'.symm_apply_apply hy.1.2])
    (p.vec_mem_image (fun y hy => hy.1.1) hto hxt)

/-- Equivalent tuples have the same image vector. -/
theorem Rel.ftransportOn (hf : P.IsScSmoothOn Q f U) {p q : P.TangentPre} (h : Rel p q)
    (hxU : p.x ∈ U) {ψ : MChart Y} (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source) :
    p.ftransportOn U f ψ = q.ftransportOn U f ψ := by
  have hqU : q.x ∈ U := h.1 ▸ hxU
  have hqx : f q.x ∈ ψ.source := h.1 ▸ hx
  rw [ftransportOn_eq_of_transport hf p hxU q.isChart (h.1 ▸ q.mem_source) hψ hx, h.2,
    ftransportOn_eq_of_transport hf q hqU q.isChart q.mem_source hψ hqx, q.transport_self]

/-- **Locality**: if `f = g` on an open `W ⊆ U ∩ U'`, the image vectors of a tuple over `W` agree
(the chain rule with `G = id`, computed on `φ(W ∩ V ∩ f⁻¹(V'))`). -/
theorem ftransportOn_congr {g : X → Y} {U' W : Set X} (hf : P.IsScSmoothOn Q f U)
    (hg : P.IsScSmoothOn Q g U') (hW : IsOpen W) (hWU : W ⊆ U) (hWU' : W ⊆ U') (hfg : EqOn f g W)
    (p : P.TangentPre) (hxW : p.x ∈ W) {ψ : MChart Y} (hψ : Q.IsChart ψ)
    (hx : f p.x ∈ ψ.source) : p.ftransportOn U f ψ = p.ftransportOn U' g ψ := by
  set t := fdomOn W p.φ f ψ with ht
  have hs₁o := isOpen_fdomOn hf p.φ ψ
  have hs₂o := isOpen_fdomOn hg p.φ ψ
  have hto : IsOpen t := isOpen_fdomOn (hf.mono hW hWU) p.φ ψ
  have hts₁ : t ⊆ fdomOn U p.φ f ψ := fun y hy => ⟨⟨hWU hy.1.1, hy.1.2⟩, hy.2⟩
  have hts₂ : t ⊆ fdomOn U' p.φ g ψ := fun y hy =>
    ⟨⟨hWU' hy.1.1, hy.1.2⟩, by rw [mem_preimage, ← hfg hy.1.1]; exact hy.2⟩
  have hxt : p.x ∈ t := ⟨⟨hxW, p.mem_source⟩, hx⟩
  have hFt : MapsTo (ψ ∘ f ∘ p.φ.symm) (p.φ '' t) ψ.model.O := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.2]
    exact ψ.mapsTo_model _ hy.2
  have key := p.φ.retractTangentMap_comp_image (fdomOn_subset _ _ _ _) hs₁o
    (fdomOn_subset _ _ _ _) hs₂o hts₁ hts₂ hto ψ.model.isScRetract
    (isScSmoothRetractMap_coordOn hf p.isChart hψ subset_rfl hs₁o) hFt
    (isScSmoothRetractMap_id ψ.model.O)
    (isScSmoothRetractMap_coordOn hg p.isChart hψ subset_rfl hs₂o)
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp_apply, id, p.φ.symm_apply_apply hy.1.2, hfg hy.1.1])
    (p.vec_mem_image (fun y hy => hy.1.2) hto hxt)
  rw [ftransportOn, ftransportOn, key]
  exact (retractTangentMap_id ψ.model.isScRetract (fun _ _ => rfl)
    (ftransportOn_mem hf p (hWU hxW) hψ hx)).symm

/-- The tuple `(f(x), ψ, Df(x)h)` of `Y`: the image of `(x, φ, h)` under `f`, in the chart `ψ`. -/
def fimageOnWith (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U) {ψ : MChart Y}
    (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source) : Q.TangentPre where
  x := f p.x
  φ := ψ
  h := (p.ftransportOn U f ψ).2
  isChart := hψ
  mem_source := hx
  mem_level := hf.mapsTo_levelSet 1 ⟨hxU, p.mem_level⟩
  mem_tangent := by
    have h1 : ((levelLift ψ 1 (f p.x), (p.ftransportOn U f ψ).2) : ψ.model.E.tangent 0) =
        p.ftransportOn U f ψ := Prod.ext (ftransportOn_fst hf p hxU hψ hx).symm rfl
    rw [h1]
    exact ftransportOn_mem hf p hxU hψ hx

section FImage

variable (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U) {ψ : MChart Y}
  (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source)

lemma fimageOnWith_x : (fimageOnWith hf p hxU hψ hx).x = f p.x := rfl

lemma fimageOnWith_vec : (fimageOnWith hf p hxU hψ hx).vec = p.ftransportOn U f ψ :=
  Prod.ext (ftransportOn_fst hf p hxU hψ hx).symm rfl

lemma fimageOnWith_transport (χ : MChart Y) :
    (fimageOnWith hf p hxU hψ hx).transport χ =
      retractTangentMap ψ.model.E ψ.model.C (ψ.overlap χ) (ψ.transition χ)
        (p.ftransportOn U f ψ) :=
  congrArg (retractTangentMap ψ.model.E ψ.model.C (ψ.overlap χ) (ψ.transition χ))
    (fimageOnWith_vec hf p hxU hψ hx)

lemma fimageOnWith_transport_self :
    (fimageOnWith hf p hxU hψ hx).transport ψ = p.ftransportOn U f ψ :=
  ((fimageOnWith hf p hxU hψ hx).transport_self).trans (fimageOnWith_vec hf p hxU hψ hx)

end FImage

/-- The class of the image tuple does not depend on the chart of `Y`. -/
theorem mk_fimageOnWith_eq (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U)
    {ψ₁ ψ₂ : MChart Y} (hψ₁ : Q.IsChart ψ₁) (hψ₂ : Q.IsChart ψ₂) (hx₁ : f p.x ∈ ψ₁.source)
    (hx₂ : f p.x ∈ ψ₂.source) :
    TangentSpace.mk (fimageOnWith hf p hxU hψ₁ hx₁) =
      TangentSpace.mk (fimageOnWith hf p hxU hψ₂ hx₂) := by
  refine TangentSpace.sound ⟨rfl, ?_⟩
  change (fimageOnWith hf p hxU hψ₁ hx₁).transport ψ₂ = (fimageOnWith hf p hxU hψ₂ hx₂).vec
  rw [fimageOnWith_transport, fimageOnWith_vec, ftransportOn_transport hf p hxU hψ₁ hψ₂ hx₁ hx₂]

/-- The class of the image tuple does not depend on the representative. -/
theorem mk_fimageOnWith_eq_of_rel (hf : P.IsScSmoothOn Q f U) {p q : P.TangentPre} (h : Rel p q)
    (hxU : p.x ∈ U) (hqU : q.x ∈ U) {ψ : MChart Y} (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source)
    (hqx : f q.x ∈ ψ.source) :
    TangentSpace.mk (fimageOnWith hf p hxU hψ hx) =
      TangentSpace.mk (fimageOnWith hf q hqU hψ hqx) := by
  refine TangentSpace.sound ⟨?_, ?_⟩
  · change f p.x = f q.x
    rw [h.1]
  · change (fimageOnWith hf p hxU hψ hx).transport ψ = (fimageOnWith hf q hqU hψ hqx).vec
    rw [fimageOnWith_transport_self, fimageOnWith_vec, h.ftransportOn hf hxU hψ hx]

/-- The image tuple in the chosen chart of `Y` around `f(x)`. -/
def fimageOn (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U) : Q.TangentPre :=
  fimageOnWith hf p hxU (Q.exists_isChart_mem_source (f p.x)).choose_spec.1
    (Q.exists_isChart_mem_source (f p.x)).choose_spec.2

end TangentPre

/-! ### The tangent map `Tf : TU → TY` of a map sc-smooth on an open set `U` -/

section TangentMapOn

variable {f : X → Y} {U : Set X}

open scoped Classical in
/-- **The tangent map `Tf : p⁻¹(U) → TY`** of a map `f` sc-smooth on the open set `U`,
`[(x, φ, h)] ↦ [(f(x), ψ, (T(ψ ∘ f ∘ φ⁻¹)(φ(x), h))₂)]` for `x ∈ U`; off `p⁻¹(U)` a junk value
(a point of `TY`, which is nonempty as soon as `Y` is: `nonempty_tangentSpace`). -/
def tangentMapOn (hf : P.IsScSmoothOn Q f U) : P.TangentSpace → Q.TangentSpace :=
  TangentSpace.lift (fun p => if hx : p.x ∈ U then TangentSpace.mk (p.fimageOn hf hx)
      else Classical.choice (Q.nonempty_tangentSpace (f p.x))) fun p q h => by
    by_cases hx : p.x ∈ U
    · have hqU : q.x ∈ U := h.1 ▸ hx
      have hψ := (Q.exists_isChart_mem_source (f p.x)).choose_spec
      have hqx : f q.x ∈ (Q.exists_isChart_mem_source (f p.x)).choose.source := h.1 ▸ hψ.2
      rw [dif_pos hx, dif_pos hqU, TangentPre.fimageOn, TangentPre.fimageOn]
      exact (TangentPre.mk_fimageOnWith_eq_of_rel hf h hx hqU hψ.1 hψ.2 hqx).trans
        (TangentPre.mk_fimageOnWith_eq hf q hqU _ _ _ _)
    · have hqU : q.x ∉ U := h.1 ▸ hx
      rw [dif_neg hx, dif_neg hqU]

/-- `Tf[(x, φ, h)]` computed in any chart `ψ` of `Y` around `f(x)`, for `x ∈ U`. -/
theorem tangentMapOn_mk (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U)
    {ψ : MChart Y} (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source) :
    tangentMapOn hf (TangentSpace.mk p) = TangentSpace.mk (p.fimageOnWith hf hxU hψ hx) := by
  rw [tangentMapOn, TangentSpace.lift_mk, dif_pos hxU, TangentPre.fimageOn,
    TangentPre.mk_fimageOnWith_eq hf p hxU _ hψ _ hx]

/-- `p ∘ Tf = f ∘ p` on `p⁻¹(U)`. -/
theorem levelVal_tangentProj_tangentMapOn (hf : P.IsScSmoothOn Q f U) {α : P.TangentSpace}
    (hα : α ∈ P.tangentPreimage U) :
    Q.levelVal 1 (Q.tangentProj (tangentMapOn hf α)) = f (P.levelVal 1 (P.tangentProj α)) := by
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  obtain ⟨ψ, hψ, hx⟩ := Q.exists_isChart_mem_source (f p.x)
  rw [tangentMapOn_mk hf p hα hψ hx]
  rfl

/-- `Tf` maps `p⁻¹(U)` into `p⁻¹(V)` when `f` maps `U` into `V`. -/
theorem tangentMapOn_mapsTo (hf : P.IsScSmoothOn Q f U) {V : Set Y} (hfUV : MapsTo f U V) :
    MapsTo (tangentMapOn hf) (P.tangentPreimage U) (Q.tangentPreimage V) := fun α hα => by
  change Q.levelVal 1 (Q.tangentProj (tangentMapOn hf α)) ∈ V
  rw [levelVal_tangentProj_tangentMapOn hf hα]
  exact hfUV hα

/-- `Tf` maps `T_xX` into `T_{f(x)}Y` for `x ∈ U`. -/
theorem tangentMapOn_mapsTo_fiber (hf : P.IsScSmoothOn Q f U) (x : P.Level 1)
    (hx : P.levelVal 1 x ∈ U) (y : Q.Level 1) (hxy : f (P.levelVal 1 x) = Q.levelVal 1 y) :
    MapsTo (tangentMapOn hf) (P.tangentFiber x) (Q.tangentFiber y) := fun α hα => by
  have hαx : P.tangentProj α = x := hα
  change Q.tangentProj (tangentMapOn hf α) = y
  apply level_ext
  rw [levelVal_tangentProj_tangentMapOn hf (tangentFiber_subset_tangentPreimage hx hα), hαx, hxy]

/-- `Tψ ∘ Tf = T(ψ ∘ f ∘ φ⁻¹) ∘ Tφ` on `p⁻¹(U ∩ V ∩ f⁻¹(V'))` (formula (5) for `f`). -/
theorem tangentChartMap_tangentMapOn (hf : P.IsScSmoothOn Q f U) {φ : MChart X}
    (hφ : P.IsChart φ) {ψ : MChart Y} (hψ : Q.IsChart ψ) {α : P.TangentSpace}
    (hα : α ∈ P.tangentPreimage (TangentPre.fdomOn U φ f ψ)) :
    tangentChartMap hψ (tangentMapOn hf α) =
      retractTangentMap φ.model.E φ.model.C (φ '' TangentPre.fdomOn U φ f ψ) (ψ ∘ f ∘ φ.symm)
        (tangentChartMap hφ α) := by
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  have hxU : p.x ∈ U := hα.1.1
  have hxφ : p.x ∈ φ.source := hα.1.2
  have hfα : f p.x ∈ ψ.source := hα.2
  rw [tangentMapOn_mk hf p hxU hψ hfα, tangentChartMap_mk hψ hfα,
    TangentPre.fimageOnWith_transport_self, tangentChartMap_mk hφ hxφ,
    TangentPre.ftransportOn_eq_of_transport hf p hxU hφ hxφ hψ hfα]

/-- **Locality of `Tf`**: if `f = g` on an open `W ⊆ U ∩ U'`, then `Tf = Tg` on `p⁻¹(W)`. -/
theorem tangentMapOn_congr {g : X → Y} {U' W : Set X} (hf : P.IsScSmoothOn Q f U)
    (hg : P.IsScSmoothOn Q g U') (hW : IsOpen W) (hWU : W ⊆ U) (hWU' : W ⊆ U')
    (hfg : EqOn f g W) : EqOn (tangentMapOn hf) (tangentMapOn hg) (P.tangentPreimage W) := by
  intro α hα
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  have hxW : p.x ∈ W := hα
  obtain ⟨ψ, hψ, hx⟩ := Q.exists_isChart_mem_source (f p.x)
  have hx' : g p.x ∈ ψ.source := hfg hxW ▸ hx
  rw [tangentMapOn_mk hf p (hWU hxW) hψ hx, tangentMapOn_mk hg p (hWU' hxW) hψ hx']
  refine TangentSpace.sound ⟨hfg hxW, ?_⟩
  change (p.fimageOnWith hf (hWU hxW) hψ hx).transport ψ = (p.fimageOnWith hg (hWU' hxW) hψ hx').vec
  rw [TangentPre.fimageOnWith_transport_self, TangentPre.fimageOnWith_vec]
  exact TangentPre.ftransportOn_congr hf hg hW hWU hWU' hfg p hxW hψ hx

/-- Shrinking the open set does not change `Tf`. -/
theorem tangentMapOn_mono (hf : P.IsScSmoothOn Q f U) {U' : Set X} (hU' : IsOpen U')
    (hsub : U' ⊆ U) :
    EqOn (tangentMapOn (hf.mono hU' hsub)) (tangentMapOn hf) (P.tangentPreimage U') :=
  tangentMapOn_congr _ _ hU' subset_rfl hsub (eqOn_refl _ _)

/-- For a globally sc-smooth `f`, the tangent map on `U` is Part I's `Tf` on `p⁻¹(U)`. -/
theorem tangentMapOn_eq_tangentMap (hf : P.IsScSmoothMap Q f) (hf' : P.IsScSmoothOn Q f U) :
    EqOn (tangentMapOn hf') (tangentMap hf) (P.tangentPreimage U) := by
  intro α hα
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  have hxU : p.x ∈ U := hα
  obtain ⟨ψ, hψ, hx⟩ := Q.exists_isChart_mem_source (f p.x)
  rw [tangentMapOn_mk hf' p hxU hψ hx, tangentMap_mk hf p hψ hx]
  refine TangentSpace.sound ⟨rfl, ?_⟩
  change (p.fimageOnWith hf' hxU hψ hx).transport ψ = (p.fimageWith hf hψ hx).vec
  rw [TangentPre.fimageOnWith_transport_self, TangentPre.fimageWith_vec]
  have h1 : p.ftransport f ψ = p.ftransportOn univ f ψ := by
    rw [TangentPre.ftransport, TangentPre.ftransportOn, TangentPre.fdomOn_univ]
  rw [h1]
  exact TangentPre.ftransportOn_congr hf' hf hf'.isOpen subset_rfl (subset_univ _)
    (eqOn_refl _ _) p hxU hψ hx

/-- The tangent map on `univ` is Part I's `Tf`. -/
theorem tangentMapOn_univ (hf : P.IsScSmoothMap Q f) : tangentMapOn hf = tangentMap hf :=
  funext fun _ => tangentMapOn_eq_tangentMap hf hf (mem_univ _)

/-- **Locality of Part I's `Tf`**: sc-smooth maps agreeing on an open `W` have the same tangent
map on `p⁻¹(W)`. -/
theorem tangentMap_eqOn_of_eqOn {g : X → Y} (hf : P.IsScSmoothMap Q f) (hg : P.IsScSmoothMap Q g)
    {W : Set X} (hW : IsOpen W) (hfg : EqOn f g W) :
    EqOn (tangentMap hf) (tangentMap hg) (P.tangentPreimage W) := fun α hα => by
  rw [← tangentMapOn_eq_tangentMap hf (hf.mono hW (subset_univ _)) hα,
    ← tangentMapOn_eq_tangentMap hg (hg.mono hW (subset_univ _)) hα]
  exact tangentMapOn_congr _ _ hW subset_rfl subset_rfl hfg hα

/-- **`T(id) = id`** on `p⁻¹(U)`. -/
theorem tangentMapOn_id (h : P.IsScSmoothOn P id U) :
    EqOn (tangentMapOn h) id (P.tangentPreimage U) := fun α hα => by
  rw [tangentMapOn_eq_tangentMap isScSmoothMap_id h hα, tangentMap_id]

/-- `Tf = id` on `p⁻¹(U)` for a map `f` sc-smooth on `U` with `f = id` on `U`. -/
theorem tangentMapOn_eqOn_id {f : X → X} (hf : P.IsScSmoothOn P f U) (hfid : EqOn f id U) :
    EqOn (tangentMapOn hf) id (P.tangentPreimage U) := fun α hα => by
  rw [tangentMapOn_congr hf (isScSmoothMap_id.mono hf.isOpen (subset_univ _)) hf.isOpen subset_rfl
    subset_rfl hfid hα]
  exact tangentMapOn_id _ hα

/-- **The chain rule on open sets**: `T(g ∘ f) = Tg ∘ Tf` on `p⁻¹(U)`, for `f` sc-smooth on `U`,
`g` sc-smooth on `V` and `f(U) ⊆ V`. -/
theorem tangentMapOn_comp {g : Y → Z} {V : Set Y} (hg : Q.IsScSmoothOn S g V)
    (hf : P.IsScSmoothOn Q f U) (hfUV : MapsTo f U V) :
    EqOn (tangentMapOn (hg.comp hf hfUV)) (tangentMapOn hg ∘ tangentMapOn hf)
      (P.tangentPreimage U) := by
  intro α hα
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  have hxU : p.x ∈ U := hα
  obtain ⟨ψ, hψ, hx⟩ := Q.exists_isChart_mem_source (f p.x)
  obtain ⟨χ, hχ, hgx⟩ := S.exists_isChart_mem_source (g (f p.x))
  set r := p.fimageOnWith hf hxU hψ hx with hr
  have hrV : r.x ∈ V := hfUV hxU
  have hgr : g r.x ∈ χ.source := hgx
  rw [Function.comp_apply, tangentMapOn_mk hf p hxU hψ hx, tangentMapOn_mk hg r hrV hχ hgr,
    tangentMapOn_mk (hg.comp hf hfUV) p hxU hχ hgx]
  refine TangentSpace.sound ⟨rfl, ?_⟩
  change (p.fimageOnWith (hg.comp hf hfUV) hxU hχ hgx).transport χ =
    (r.fimageOnWith hg hrV hχ hgr).vec
  rw [TangentPre.fimageOnWith_transport_self, TangentPre.fimageOnWith_vec hg r hrV hχ hgr]
  change _ = retractTangentMap ψ.model.E ψ.model.C (ψ '' TangentPre.fdomOn V ψ g χ)
    (χ ∘ g ∘ ψ.symm) r.vec
  refine Eq.trans ?_ (congrArg (retractTangentMap ψ.model.E ψ.model.C
    (ψ '' TangentPre.fdomOn V ψ g χ) (χ ∘ g ∘ ψ.symm))
    (TangentPre.fimageOnWith_vec hf p hxU hψ hx)).symm
  set t := TangentPre.fdomOn U p.φ f ψ ∩ f ⁻¹' TangentPre.fdomOn V ψ g χ with ht
  have hs₁o : IsOpen (TangentPre.fdomOn U p.φ f ψ) := TangentPre.isOpen_fdomOn hf p.φ ψ
  have hs₂o : IsOpen (TangentPre.fdomOn U p.φ (g ∘ f) χ) :=
    TangentPre.isOpen_fdomOn (hg.comp hf hfUV) p.φ χ
  have hto : IsOpen t :=
    (hf.continuousOn.mono fun y hy => hy.1.1).isOpen_inter_preimage hs₁o
      (TangentPre.isOpen_fdomOn hg ψ χ)
  have hts₂ : t ⊆ TangentPre.fdomOn U p.φ (g ∘ f) χ := fun y hy => ⟨hy.1.1, hy.2.2⟩
  have hxt : p.x ∈ t := ⟨⟨⟨hxU, p.mem_source⟩, hx⟩, ⟨⟨hrV, hx⟩, hgx⟩⟩
  have hO₁' : IsScRetract ψ.model.E ψ.model.C (ψ '' TangentPre.fdomOn V ψ g χ) :=
    ψ.isScRetract_image (TangentPre.fdomOn_subset _ _ _ _) (TangentPre.isOpen_fdomOn hg ψ χ)
  have hFt : MapsTo (ψ ∘ f ∘ p.φ.symm) (p.φ '' t) (ψ '' TangentPre.fdomOn V ψ g χ) := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.1.2]
    exact ⟨f y, hy.2, rfl⟩
  exact p.φ.retractTangentMap_comp_image (TangentPre.fdomOn_subset _ _ _ _) hs₁o
    (TangentPre.fdomOn_subset _ _ _ _) hs₂o inter_subset_left hts₂ hto hO₁'
    (TangentPre.isScSmoothRetractMap_coordOn hf p.isChart hψ subset_rfl hs₁o) hFt
    (TangentPre.isScSmoothRetractMap_coordOn hg hψ hχ subset_rfl
      (TangentPre.isOpen_fdomOn hg ψ χ))
    (TangentPre.isScSmoothRetractMap_coordOn (hg.comp hf hfUV) p.isChart hχ subset_rfl hs₂o)
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.1.2,
        ψ.symm_apply_apply hy.2.1.2])
    (p.vec_mem_image (fun y hy => hy.1.1.2) hto hxt)

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

include hU in
/-- The inclusion `U → X` of an open subset (with Part I's structure `restrictOpen`) is sc-smooth:
in the charts `φ|U` of `U` and `φ|U` of `X` it is the identity. -/
theorem isScSmoothMap_subtypeVal : (P.restrictOpen hU).IsScSmoothMap P (Subtype.val : U → X) := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ continuous_subtype_val.continuousOn
    fun v _ => ?_
  obtain ⟨φ, hφ, hv⟩ := P.exists_isChart_mem_source v.1
  set φ' := φ.restrict (s := φ.source ∩ U) inter_subset_left (φ.isOpen_source.inter hU) with hφ'
  have hφ'c : P.IsChart φ' := MPolyfold.IsChart.restrict P hφ _ _
  set φ'' := φ'.restrictTo (V := U) inter_subset_right with hφ''
  have hφ''c : (P.restrictOpen hU).IsChart φ'' := isChart_restrictTo hU hφ'c inter_subset_right
  refine ⟨φ'', φ', φ''.source, hφ''c, hφ'c, φ''.isOpen_source, ⟨hv, v.2⟩,
    fun w hw => ⟨mem_univ _, hw⟩, fun w hw => hw, ?_⟩
  refine ((isScSmoothRetractMap_id _).mono_target
    fun z hz => φ''.image_subset_model subset_rfl hz).congr ?_
  rintro _ ⟨w, hw, rfl⟩
  simp only [Function.comp_apply, id, φ''.symm_apply_apply hw]
  rfl

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
