import Polyfold.Chapter15.GeneralPositionEquivalence
import Polyfold.Chapter15.ParamOntoTransport

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.2, **Definition 15.2.1** (p. 688): transversality of `(f, Λ)` under local strong bundle
isomorphisms, strong bundle equivalences and diagrams of strong bundle equivalences, as needed for
the passage between two models of a strong polyfold bundle (§16.6, p. 739).

# Transversality is invariant under strong bundle equivalences

## The text, paraphrased

(Definition 15.2.1) `(f, Λ)` is transversal if at every `x ∈ supp(Λ ∘ f)` every operator of
`T(f, Λ)(x) = ∑ σᵢ · (f − sᵢ)'(x)` is onto `W_x`.  (§16.6) Two models of a strong polyfold bundle
differ by a generalized strong bundle isomorphism `[W ←Φ W'' →Ψ W']`, both legs strong bundle
equivalences.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `surjective_toIntr_transportChart_iff_full`: an operator read through the carried chart
  `c' ∘ Φ` at `x` is onto `W_x` iff it is onto `W'_{x'}` read through `c'` at `x' = ϕ(x)`.
* **`isOntoAtLevel_localIso_iff`**: for a local strong bundle isomorphism `L : W|U → W'|U'`,
  `f = Ψ ∘ f' ∘ ϕ` on `U` and `Λ = Λ' ∘ Φ` over `U`, `T(f, Λ)(x)` is onto iff `T(f', Λ')(ϕ x)` is.
* `isOntoAtLevel_of_mor`: `T(f, Λ)` onto at `s(φ)` gives onto at `t(φ)` (Theorem 15.1.1).
* `isOntoAtLevel_pullback_iff`, **`isTransversal_pullback_iff`**: `(Ψ^* f', Ψ^* Λ')` is transversal
  iff `(f', Λ')` is, for a strong bundle equivalence `Ψ`.
* **`SDiagram.isTransversal_iff_of_pullback_eq`**: for a diagram `W ←Φ W'' →Ψ W'` of strong
  bundle equivalences, sections with `Φ^* F = Ψ^* F'` and sc⁺-multisections with `Λ(w) = Λ'(w')`
  whenever `|D|(|w|) = |w'|`: `(F, Λ)` is transversal iff `(F', Λ')` is.

## Reading

As in Chapter 15, `T(f, Λ)(x)` is read at level-`1` points.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongRetr MPolyfold Linearization15 StrongBundle EPLocalization

variable {A A' : SEP.{u}}

/-! ### Along a local strong bundle isomorphism -/

section LocalIso

variable {U : Set A.Obj} {U' : Set A'.Obj} (L : StrongBundle.LocalIso A.B A'.B U U')
  {c' : StrongBundleChart A'.X.PObj A'.P} (hsub : c'.φ.source ⊆ U')
  {x : A.X.PObj.Level 1} {x' : A'.X.PObj.Level 1}
  (hϕ : L.ϕ (A.X.PObj.levelVal 1 x) = A'.X.PObj.levelVal 1 x')
  (hx : A.X.PObj.levelVal 1 x ∈ (L.transportChart c' hsub).φ.source)
  (hx' : A'.X.PObj.levelVal 1 x' ∈ c'.φ.source)

include hϕ in
/-- **Onto through the carried chart and through `c'`**: `Φ_x⁻¹ ∘ Lop ∘ T(c' ∘ Φ)` is onto `W_x`
iff `Φ'_{x'}⁻¹ ∘ Lop ∘ Tc'` is onto `W'_{x'}`. -/
theorem surjective_toIntr_transportChart_iff_full (Lop : c'.φ.model.E 0 →L[ℝ] c'.F 0) :
    Surjective (toIntr (L.transportChart c' hsub) hx Lop) ↔ Surjective (toIntr c' hx' Lop) := by
  set c := L.transportChart c' hsub
  set τ := tangentIso L hsub hϕ hx hx'
  constructor
  · intro H w
    obtain ⟨v, hv⟩ := exists_fiberLin_transportChart_eq L hsub hϕ hx hx' w
    obtain ⟨α, hαv⟩ := H v
    refine ⟨τ α, c'.fiberLin_injective hx' ?_⟩
    rw [fiberLin_toIntr_tangentIso L hsub hϕ hx hx' Lop α, ← hv, hαv]
  · intro H v
    obtain ⟨w, hw⟩ := exists_fiberLin_eq L hsub hϕ hx hx' v
    obtain ⟨α', hαw⟩ := H w
    refine ⟨τ.symm α', c.fiberLin_injective hx ?_⟩
    rw [← fiberLin_toIntr_tangentIso L hsub hϕ hx hx' Lop (τ.symm α'), τ.apply_symm_apply, hαw,
      hw]

end LocalIso

open scoped Classical in
/-- **`T(f, Λ)` onto at a point along a local strong bundle isomorphism** (Definition 15.2.1 at
one point): for sc-Fredholm section functors `f` of `W` and `f'` of `W'` with `f = Ψ ∘ f' ∘ ϕ`
on `U`, an sc⁺-multisection `Λ'` of `W'` and a function `Λ` with `Λ = Λ' ∘ Φ` over `U`, every
operator of `T(f, Λ)(x)` is onto at `x ∈ U` iff every operator of `T(f', Λ')(ϕ x)` is. -/
theorem isOntoAtLevel_localIso_iff {U : Set A.Obj} {U' : Set A'.Obj}
    (L : StrongBundle.LocalIso A.B A'.B U U') {f : A.Obj → A.W} {f' : A'.Obj → A'.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hf' : A'.E.IsScFredholmSectionFunctor f')
    {Λ : A.W → ℚ≥0} {Λ' : A'.W → ℚ≥0} (hΛ' : IsScPlusMultisection A' Λ')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hΛL : ∀ w, A.P w ∈ U → Λ w = Λ' (L.Φ w))
    {x : A.X.PObj.Level 1} {x' : A'.X.PObj.Level 1} (hxU : A.X.PObj.levelVal 1 x ∈ U)
    (hϕ : L.ϕ (A.X.PObj.levelVal 1 x) = A'.X.PObj.levelVal 1 x') :
    IsOntoAtLevel f Λ x ↔ IsOntoAtLevel f' Λ' x' := by
  obtain ⟨d⟩ := nonempty_localLinData hΛ' x'
  set y := A.X.PObj.levelVal 1 x with hy
  set y' := A'.X.PObj.levelVal 1 x' with hy'
  have hy'U : y' ∈ U' := hϕ ▸ L.base.mapsTo hxU
  have hso : IsOpen (d.c.φ.source ∩ U') := d.c.φ.isOpen_source.inter L.isOpen_U'
  set c' := d.c.restrict inter_subset_left hso with hc'def
  have hc' : A'.B.IsChart c' := d.isChart.restrict inter_subset_left hso
  have hsub : c'.φ.source ⊆ U' := fun z hz => hz.2
  have hx' : y' ∈ c'.φ.source := ⟨d.mem, hy'U⟩
  set O' := d.O ∩ U' with hO'def
  have hO' : IsOpen O' := d.isOpen.inter L.isOpen_U'
  have hrep' : IsLocalRepOn A' Λ' O' d.s d.σ := d.rep.mono hO' inter_subset_left
  have hsubO : c'.φ.source ⊆ O' := fun z hz => ⟨d.sub hz.1, hz.2⟩
  set c := L.transportChart c' hsub with hcdef
  have hx : y ∈ c.φ.source := ⟨hxU, by rw [mem_preimage, hϕ]; exact hx'⟩
  have hrep : IsLocalRepOn A Λ (isoSet L O') (fun i => isoSec L (d.s i)) d.σ :=
    isLocalRepOn_isoSec L hΛL hO' inter_subset_right hrep'
  have hcsub : c.φ.source ⊆ isoSet L O' := fun z hz => ⟨hz.1, hsubO hz.2⟩
  let dx' : LocalLinData A' Λ' x' := ⟨O', hO', d.k, d.s, d.σ, hrep', c', hc', hsubO, hx'⟩
  let dx : LocalLinData A Λ x :=
    ⟨isoSet L O', isOpen_isoSet L hO', d.k, fun i => isoSec L (d.s i), d.σ, hrep, c,
      L.isChart_transportChart c' hsub hc', hcsub, hx⟩
  have hsec' : IsSection A'.P f' := hf'.1.1.1
  have hbr : ∀ i, isoSec L (d.s i) y = f y ↔ d.s i y' = f' y' := fun i => by
    have e1 : isoSec L (d.s i) y = L.Ψ (d.s i y') := by rw [isoSec, hϕ]
    have e2 : f y = L.Ψ (f' y') := by rw [hfL hxU]; simp only [Function.comp_apply, hϕ]
    rw [e1, e2]
    constructor
    · intro h
      have h1 : d.s i y' ∈ A'.P ⁻¹' U' := by
        change A'.P (d.s i y') ∈ U'
        rw [(hrep'.2.1 i).1 _ (hsubO hx')]; exact hy'U
      have h2 : f' y' ∈ A'.P ⁻¹' U' := by
        change A'.P (f' y') ∈ U'
        rw [hsec' y']; exact hy'U
      rw [← L.zero.right_inv _ h1, ← L.zero.right_inv _ h2, h]
    · intro h; rw [h]
  have hl : levelLift c.φ 1 y = levelLift c'.φ 1 y' := levelLift_transportChart L hsub hϕ
  have hzU : c'.φ.model.E.toBase 1 (levelLift c'.φ 1 y') ∈ c'.U := by
    rw [A'.X.PObj.toBase_levelLift c'.isChart hx' (levelVal_mem x')]
    exact mem_U_of_mem_O c'.isRetraction (c'.r_image ▸ c'.φ.mapsTo_model _ hx')
  have hD : ∀ i, subDeriv c f (isoSec L (d.s i)) (levelLift c.φ 1 y) =
      subDeriv c' f' (d.s i) (levelLift c'.φ 1 y') := fun i => by
    rw [hl]
    exact subDeriv_transportChart L hsub hf'.1.1 hfL (hrep'.2.1 i) hc' hsubO hzU
  rw [isOntoAtLevel_iff hf dx, isOntoAtLevel_iff hf' dx']
  refine forall_congr' fun i => ?_
  change (isoSec L (d.s i) y = f y → Surjective (toIntr c hx
      (subDeriv c f (isoSec L (d.s i)) (levelLift c.φ 1 y)))) ↔
    (d.s i y' = f' y' → Surjective (toIntr c' hx' (subDeriv c' f' (d.s i) (levelLift c'.φ 1 y'))))
  rw [hbr i, hD i]
  exact imp_congr_right fun _ =>
    surjective_toIntr_transportChart_iff_full L hsub hϕ hx hx' _

/-! ### Along morphisms -/

/-- **`T(f, Λ)` onto at a point is carried along morphisms**: for an sc-Fredholm section functor
`f`, an sc⁺-multisection `Λ` and a morphism `φ : x → y` of level-`1` points, the operators of
`T(f, Λ)(y)` are onto if those of `T(f, Λ)(x)` are (Theorem 15.1.1:
`T(f, Λ)(y) = μ(φ, ·) ∘ T(f, Λ)(x) ∘ (Tφ)⁻¹`). -/
theorem isOntoAtLevel_of_mor {A : SEP.{u}} {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (φ : A.Mor) {x y : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x = A.X.src φ)
    (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ) (H : IsOntoAtLevel f Λ x) :
    IsOntoAtLevel f Λ y := by
  classical
  intro L' hL' w
  set hφ := mem_levelSet_one_of_src hx
  rw [theorem_15_1_1_functor hf hΛ φ hx hy, grfPush] at hL'
  obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hL')
  obtain ⟨w₀, rfl⟩ := muLin_surjective φ hx.symm hy.symm w
  obtain ⟨u, hu⟩ := H L hL w₀
  refine ⟨A.X.tangentMorCLE hφ hx hy u, ?_⟩
  rw [conjOp_apply, ContinuousLinearEquiv.symm_apply_apply, hu]

/-! ### Along a strong bundle equivalence -/

/-- **`T(f, Λ)` onto at a point along a strong bundle equivalence** `Ψ : W → W'` covering `ψ`:
`T(Ψ^* f', Ψ^* Λ')(x)` is onto iff `T(f', Λ')(ψ x)` is. -/
theorem isOntoAtLevel_pullback_iff {Ψ : A ⟶ A'} (hΨ : SEP.equivalences Ψ)
    {f' : A'.Obj → A'.W} (hf' : A'.E.IsScFredholmSectionFunctor f') {Λ' : A'.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection A' Λ') {x : A.X.PObj.Level 1} {x' : A'.X.PObj.Level 1}
    (hϕ : (SEP.Hom.ϕ Ψ).obj (A.X.PObj.levelVal 1 x) = A'.X.PObj.levelVal 1 x') :
    IsOntoAtLevel ((sbe hΨ).pullback f') (pullMult Ψ Λ') x ↔ IsOntoAtLevel f' Λ' x' :=
  isOntoAtLevel_localIso_iff ((sbe hΨ).locIso (A.X.PObj.levelVal 1 x))
    ((EpStrongBundle.theorem_10_4_5_fred (sbe hΨ)).2.1 hf') hf' hΛ'
    ((sbe hΨ).eqOn_locIso hf'.1.1.1 _) (fun _ _ => rfl) ((sbe hΨ).mem_locSet _) hϕ

/-- **Transversality (Definition 15.2.1) is invariant under strong bundle equivalences**: for a
strong bundle equivalence `Ψ : W → W'`, an sc-Fredholm section functor `f'` and an
sc⁺-multisection `Λ'` of `W'`, `(Ψ^* f', Ψ^* Λ')` is transversal iff `(f', Λ')` is. -/
theorem isTransversal_pullback_iff {Ψ : A ⟶ A'} (hΨ : SEP.equivalences Ψ)
    {f' : A'.Obj → A'.W} (hf' : A'.E.IsScFredholmSectionFunctor f') {Λ' : A'.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection A' Λ') :
    IsTransversal ((sbe hΨ).pullback f') (pullMult Ψ Λ') ↔ IsTransversal f' Λ' := by
  set h := sbe hΨ
  have hsec' : IsSection A'.P f' := hf'.1.1.1
  have hf := (EpStrongBundle.theorem_10_4_5_fred h).2.1 hf'
  have hΛ : IsScPlusMultisection A (pullMult Ψ Λ') := isScPlusMultisection_pullMult hΨ hΛ'
  have hlev : ∀ a : A.Obj, (SEP.Hom.ϕ Ψ).obj a ∈ A'.X.PObj.levelSet 1 ↔
      a ∈ A.X.PObj.levelSet 1 := fun a =>
    (h.locIso a).base.mem_levelSet_iff (h.mem_locSet a) 1
  have hval : ∀ a : A.Obj, pullMult Ψ Λ' (h.pullback f' a) = Λ' (f' ((SEP.Hom.ϕ Ψ).obj a)) :=
    fun a => congrArg Λ' (h.obj_pullback hsec' a)
  constructor
  · intro H y' hpos
    have hy'1 : y' ∈ A'.X.PObj.levelSet 1 := mem_levelSet_one_of_pos hf' hΛ' hpos
    set x' := A'.X.PObj.levelMk 1 y' hy'1
    have hx'v : A'.X.PObj.levelVal 1 x' = y' := A'.X.PObj.levelVal_levelMk 1 _ hy'1
    set a := h.preObj y'
    set σ := h.preMor y'
    have hsrc : A'.X.src σ = (SEP.Hom.ϕ Ψ).obj a := h.src_preMor y'
    have htgt : A'.X.tgt σ = y' := h.tgt_preMor y'
    have hσ1 : σ ∈ A'.X.PMor.levelSet 1 :=
      (A'.X.mem_levelSet_tgt_iff σ 1).1 (htgt ▸ hy'1)
    have hϕa1 : (SEP.Hom.ϕ Ψ).obj a ∈ A'.X.PObj.levelSet 1 :=
      hsrc ▸ (A'.X.mem_levelSet_src_iff σ 1).2 hσ1
    have ha1 : a ∈ A.X.PObj.levelSet 1 := (hlev a).1 hϕa1
    set x := A.X.PObj.levelMk 1 a ha1
    set x'' := A'.X.PObj.levelMk 1 ((SEP.Hom.ϕ Ψ).obj a) hϕa1
    have hx : A.X.PObj.levelVal 1 x = a := A.X.PObj.levelVal_levelMk 1 _ ha1
    have hx'' : A'.X.PObj.levelVal 1 x'' = (SEP.Hom.ϕ Ψ).obj a :=
      A'.X.PObj.levelVal_levelMk 1 _ hϕa1
    have hfun := isFunctorial_comp hf' hΛ' σ
    have hpos' : 0 < Λ' (f' ((SEP.Hom.ϕ Ψ).obj a)) := by
      have e : ((Λ' (f' (A'.X.src σ)) : ℚ≥0) : ℚ) = Λ' (f' (A'.X.tgt σ)) := hfun
      rw [hsrc, htgt] at e
      have e' : Λ' (f' ((SEP.Hom.ϕ Ψ).obj a)) = Λ' (f' y') := by exact_mod_cast e
      rw [e']; exact hpos
    have hposa : 0 < pullMult Ψ Λ' (h.pullback f' a) := by rw [hval]; exact hpos'
    obtain ⟨-, ha1', h1⟩ := H a hposa
    have h1' : IsOntoAtLevel (h.pullback f') (pullMult Ψ Λ') x := h1
    have h2 : IsOntoAtLevel f' Λ' x'' :=
      (isOntoAtLevel_pullback_iff hΨ hf' hΛ' (by rw [hx, hx''])).1 h1'
    exact ⟨hpos, hy'1, isOntoAtLevel_of_mor hf' hΛ' σ (hx''.trans hsrc.symm)
      (hx'v.trans htgt.symm) h2⟩
  · intro H a hpos
    have ha1 : a ∈ A.X.PObj.levelSet 1 := mem_levelSet_one_of_pos hf hΛ hpos
    set x := A.X.PObj.levelMk 1 a ha1
    have hx : A.X.PObj.levelVal 1 x = a := A.X.PObj.levelVal_levelMk 1 _ ha1
    have hϕa1 : (SEP.Hom.ϕ Ψ).obj a ∈ A'.X.PObj.levelSet 1 := (hlev a).2 ha1
    set x' := A'.X.PObj.levelMk 1 ((SEP.Hom.ϕ Ψ).obj a) hϕa1
    have hx' : A'.X.PObj.levelVal 1 x' = (SEP.Hom.ϕ Ψ).obj a :=
      A'.X.PObj.levelVal_levelMk 1 _ hϕa1
    have hpos' : 0 < Λ' (f' ((SEP.Hom.ϕ Ψ).obj a)) := by rw [← hval]; exact hpos
    obtain ⟨-, hx1', h1⟩ := H _ hpos'
    have h1' : IsOntoAtLevel f' Λ' x' := h1
    exact ⟨hpos, ha1, (isOntoAtLevel_pullback_iff hΨ hf' hΛ' (by rw [hx, hx'])).2 h1'⟩

/-! ### Diagrams of strong bundle equivalences -/

namespace SDiagram

/-- **Transversality is invariant under generalized strong bundle isomorphisms**: for a diagram
`D : W ←Φ W'' →Ψ W'` of strong bundle equivalences, sc-Fredholm section functors `F` of `W` and
`F'` of `W'` with `Φ^* F = Ψ^* F'`, and sc⁺-multisections `Λ` of `W` and `Λ'` of `W'` with
`Λ(w) = Λ'(w')` whenever `|D|(|w|) = |w'|`: `(F, Λ)` is transversal iff `(F', Λ')` is. -/
theorem isTransversal_iff_of_pullback_eq (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
    {F : A.Obj → A.W} {F' : A'.Obj → A'.W} (hF : A.E.IsScFredholmSectionFunctor F)
    (hF' : A'.E.IsScFredholmSectionFunctor F')
    (hpb : D.hΦ.pullback F = (sbe hΨ).pullback F') {Λ : A.W → ℚ≥0} {Λ' : A'.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) (hΛ' : IsScPlusMultisection A' Λ')
    (hΛΛ' : ∀ w w', D.orbitMap (A.E.toEpGroupoid.π w) = A'.E.toEpGroupoid.π w' → Λ w = Λ' w') :
    IsTransversal F Λ ↔ IsTransversal F' Λ' := by
  have e2 : SBLocalization.pullMult D.Ψ Λ' = SBLocalization.pullMult D.Φ Λ := funext fun v =>
    (hΛΛ' _ _ (D.orbitMap_orbitMap_Φ (D.B.E.toEpGroupoid.π v))).symm
  have h1 := isTransversal_pullback_iff D.isEquivalence_Φ hF hΛ
  have h2 := isTransversal_pullback_iff hΨ hF' hΛ'
  rw [← hpb, e2] at h2
  exact h1.symm.trans h2

end SDiagram

end SBLocalization

end Polyfold
