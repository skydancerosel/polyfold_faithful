import Polyfold.Examples.OrbifoldSquareInfBundle
import Polyfold.Chapter4.RetractionSectionFredholm
import Polyfold.Chapter3.BasicGermCriterionTransport
import Polyfold.Chapter6.Propagation
import Polyfold.Chapter14.Linearization
import Polyfold.Chapter16.CircleSectionCobordism

/-!
# The orbifold `(ℂ × H)/ℤ₅` and the section `(z, e) ↦ (z², e)`: sc-Fredholm, index `0`

Part of the infinite-dimensional worked example for Hofer–Wysocki–Zehnder, *Polyfold and Fredholm
Theory* (Springer 2021), Theorem 16.6.6, 2021 p. 739, with Definitions 3.1.16 (p. 96), 3.6.4
(p. 135) and 6.2.1 (p. 201).

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquareInf`)

* `isConjugateToBasicGerm_id`: on any sc-Banach space the principal part `v ↦ v` of a section of
  `U ◁ E` is conjugated to a basic germ.
* **`isScFredholmSectionTame_idSec`**: the section `e ↦ (e, e)` of `H ◁ H → H` is sc-Fredholm
  with tame germ data; it is regularizing because `(e, e) ∈ W[m, m+1]` means `e ∈ H_{m+1}`.
* **`isScFredholmSectionFunctor_sqInf`**, **`isScFredholmSectionTame_sqInf`**: the section
  `(z, e) ↦ ((z, z²), (e, e))` is an sc-Fredholm section functor with tame germ data.
* `isZeroAt_sqInf_iff`, `solutionSet_sqInf`: the solution set is the point `(0, 0)`.
* `constSec`, `isScPlusSection_constSec`: the constant sections of `H ◁ H` through smooth points
  are sc⁺-sections.
* **`isIndexAt_sqInf`**: the Fredholm index is `0` at every smooth point.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.OrbifoldSquareInf

open TrivialBundle EpGroupoid.Examples StrongBundle WeightedEllTwo OrbifoldSquare SBLocalization
  StrongRetr

/-! ### The identity principal part -/

/-- **The principal part `v ↦ v` is conjugated to a basic germ** (Definition 3.1.11): the case
`N = 0`, `Y = E` of the last step of Lemma 4.1.11. -/
theorem isConjugateToBasicGerm_id {E : ScBanach} {C U : Set (E 0)}
    (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U) :
    IsConjugateToBasicGerm (E := E) (F := E) U (fun v => v) := by
  have hpN : ∀ n : (⊥ : Submodule ℝ (E 0)),
      (0 : E 0 →L[ℝ] (⊥ : Submodule ℝ (E 0))) n = n := fun n => Subsingleton.elim _ _
  have hpY : ∀ y ∈ (⊤ : Submodule ℝ (E 0)),
      (0 : E 0 →L[ℝ] (⊥ : Submodule ℝ (E 0))) y = 0 := fun _ _ => rfl
  have hq := isConjugateToBasicGerm_qOp (N := ⊥) (Y := ⊤) bot_le E.isScSubspace_top
    isCompl_bot_top (0 : E 0 →L[ℝ] (⊥ : Submodule ℝ (E 0))) hpN hpY hU h0
  have himg : (ScIso.refl E) 0 '' U = U :=
    Set.ext fun v => ⟨by rintro ⟨u, hu, rfl⟩; exact hu, fun hv => ⟨v, hv, rfl⟩⟩
  refine IsConjugateToBasicGerm.of_scIso hU (ScIso.refl E) E.topIso (himg.symm ▸ hU) ?_
  rw [himg]
  refine hq.congr fun u _ => Subtype.ext ?_
  rw [qOp_zero_val]
  change u - 0 = u
  rw [sub_zero]

/-! ### The identity section of `H ◁ H` -/

theorem mem_smoothSet_PH_iff {x : HObj} : x ∈ PH.smoothSet ↔ (x : H 0) ∈ H.smooth :=
  LocalBundle.mem_smoothSet_iff relOpen_H h0

/-- **`e ↦ (e, e)` is an sc-Fredholm section of `H ◁ H → H` with tame germ data**
(Definitions 3.1.16, 3.6.4). -/
theorem isScFredholmSectionTame_secId :
    BH.IsScFredholmSectionTame (LocalBundle.sec (E := H) (U := (univ : Set (H 0))) (F := H) id) := by
  classical
  set idSec : HObj → HObj × H 0 :=
    LocalBundle.sec (E := H) (U := (univ : Set (H 0))) (F := H) id with hidSec
  have hdom := relOpen_H.isScDomain
  have hksm : IsScSmooth (E := H) (F := H) (univ : Set (H 0)) id := isScSmooth_id hdom
  have germ : ∀ x ∈ PH.smoothSet, BH.IsScFredholmGermTame idSec x := by
    intro x hx
    have hxs := hx
    rw [mem_smoothSet_PH_iff] at hx
    set e : H 0 := (x : H 0) with hedef
    obtain ⟨n, W, T, hT⟩ := relOpen_H.isPartialQuadrant
    set c := LocalBundle.centred (F := H) relOpen_H h0 hT hx with hcdef
    have hch : BH.IsChart c := LocalBundle.isChart_centred relOpen_H h0 hT hx
    have h0c : (0 : H 0) ∈ c.U := LocalBundle.zero_mem_centred_U relOpen_H h0 hT hx (mem_univ _)
    have hdomc := c.relOpen.isScDomain
    have hprinc : ∀ v : H 0, v ∈ c.U → (c.principal idSec v : H 0) = v + e := fun v hv =>
      LocalBundle.principal_centred relOpen_H h0 hT hx id hv
    have hgsm : IsScSmooth c.U (c.principal idSec) :=
      (isScSmooth_add_const hx hdomc).congr hdomc fun v hv => (hprinc v hv).symm
    have he1 : e ∈ range (H.toBase 1) := (H.mem_smooth_iff.1 hx) 1
    let s : H 0 → H 1 := fun _ => H.liftOne e
    have hs : IsScSmooth (E := H) (F := H.shift) c.U s :=
      isScSmooth_const_of_smooth hdomc (by rw [H.toBase_liftOne he1]; exact hx)
    have hQc := c.relOpen.isPartialQuadrant.isQuadrantLike
    have htame : BH.IsTameChart c := isTameChart_of_eqOn_id hch fun u _ =>
      congrArg Prod.fst (LocalBundle.centred_R_apply relOpen_H h0 hT hx (u, 0))
    refine ⟨hxs, c, htame, LocalBundle.mem_centred_source relOpen_H h0 hT hx rfl,
      LocalBundle.centred_apply_self relOpen_H h0 hT hx rfl, h0c, c.principal idSec, s,
      (isFilling2021_of_R_eq_self c.relOpen c.isRetraction
        (LocalBundle.centred_R_apply relOpen_H h0 hT hx) h0c hgsm).isFillingGerm,
      ⟨ScNbhdGerm.ofSet c.relOpen.relOpen h0c, fun _ hv => hv,
        IsScSmooth.isScSmoothGerm hQc c.relOpen.relOpen h0c hs⟩, ?_, ?_⟩
    · exact (H.toBase_liftOne he1).trans ((hprinc 0 h0c).trans (zero_add e)).symm
    · refine (isConjugateToBasicGerm_id c.relOpen h0c).congr fun v hv => ?_
      refine eq_sub_of_add_eq ?_
      exact (congrArg (fun t : H 0 => (show H 0 from v) + t) (H.toBase_liftOne he1)).trans
        (hprinc v hv).symm
  refine { isScSmooth := LocalBundle.isScSmoothSection_sec relOpen_H h0 hksm
           regularizing := ?_
           germ := fun x hx => (germ x hx).isScFredholmGerm
           germTame := germ }
  intro m x _ hfx
  exact (LocalBundle.mem_levelSet_iff relOpen_H h0).2
    ((LocalBundle.mem_doubleLevel_iff relOpen_H h0).1 hfx).2

theorem isScFredholmSectionTame_idSec : AH.B.IsScFredholmSectionTame idSec :=
  isScFredholmSectionTame_secId

/-- `e ↦ (e, e)` is an sc-Fredholm section functor over the trivial ep-groupoid of `H`. -/
theorem isScFredholmSectionFunctor_idSec : AH.E.IsScFredholmSectionFunctor idSec :=
  ⟨⟨isScFredholmSectionTame_idSec.isScSmooth, fun _ => rfl⟩,
    isScFredholmSectionTame_idSec.toIsScFredholmSection⟩

/-! ### The section `(z, e) ↦ ((z, z²), (e, e))` -/

/-- `z ↦ (z, z²)` has tame germ data. -/
theorem isScFredholmSectionTame_sqSection' : A5.B.IsScFredholmSectionTame sqSection :=
  isScFredholmSectionTame_graphSection contDiff_sq

/-- **`f` is an sc-Fredholm section functor** of `(ℂ × ℂ) × (H ◁ H)` over `(ℤ/5 ⋉ ℂ) × H`. -/
theorem isScFredholmSectionFunctor_sqInf : Ainf.E.IsScFredholmSectionFunctor sqInf :=
  (isScFredholmSectionFunctor_prodMap isScFredholmSectionFunctor_sqSection
    isScFredholmSectionTame_sqSection' isScFredholmSectionFunctor_idSec
    isScFredholmSectionTame_idSec).1

/-- **`f` has tame germ data** (Definition 3.6.4). -/
theorem isScFredholmSectionTame_sqInf : Ainf.B.IsScFredholmSectionTame sqInf :=
  (isScFredholmSectionFunctor_prodMap isScFredholmSectionFunctor_sqSection
    isScFredholmSectionTame_sqSection' isScFredholmSectionFunctor_idSec
    isScFredholmSectionTame_idSec).2

/-- `(e, e) = 0` iff `e = 0`. -/
theorem isZeroAt_idSec_iff {x : AH.Obj} : IsZeroAt AH.P idSec x ↔ x = h0 := by
  constructor
  · intro h
    have h2 : (show HObj from x).1 = 0 := congrArg Prod.snd h
    exact Subtype.ext h2
  · rintro rfl
    rfl

/-- **`f(z, e) = 0` iff `(z, e) = (0, 0)`.** -/
theorem isZeroAt_sqInf_iff {x : Ainf.Obj} :
    IsZeroAt Ainf.P sqInf x ↔ x = ((0 : Fin 2 → ℝ), h0) := by
  have h : x ∈ solutionSet Ainf.P sqInf ↔ x = ((0 : Fin 2 → ℝ), h0) := by
    refine (Set.ext_iff.1 (solutionSet_prodMap (A := A5) (A' := AH) sqSection idSec) x).trans ?_
    constructor
    · rintro ⟨h1, h2⟩
      exact Prod.ext (isZeroAt_sqSection_iff.1 h1) (isZeroAt_idSec_iff.1 h2)
    · rintro rfl
      exact ⟨isZeroAt_sqSection_iff.2 rfl, isZeroAt_idSec_iff.2 rfl⟩
  exact h

/-- **The solution set is the point `(0, 0)`.** -/
theorem solutionSet_sqInf : solutionSet Ainf.P sqInf = {((0 : Fin 2 → ℝ), h0)} := by
  ext x
  exact isZeroAt_sqInf_iff

/-! ### Constant sections of `H ◁ H` -/

/-- The constant section `e ↦ (e, b)` of `H ◁ H → H`. -/
def constSec (b : H 0) : HObj → HObj × H 0 :=
  LocalBundle.sec (E := H) (U := (univ : Set (H 0))) (F := H) fun _ => b

theorem constSec_apply (b : H 0) (x : HObj) : constSec b x = (x, b) := rfl

/-- **The constant section through a smooth point is an sc⁺-section** (Definition 2.6.6). -/
theorem isScPlusSection_constSec {b : H 0} (hb : b ∈ H.smooth) :
    BH.IsScPlusSection (constSec b) := by
  classical
  refine ⟨LocalBundle.isSection_sec _, ?_⟩
  intro c hc
  obtain rfl : c = LocalBundle.chart relOpen_H h0 := mem_singleton_iff.1 hc
  have hb1 : b ∈ range (H.toBase 1) := (H.mem_smooth_iff.1 hb) 1
  refine ⟨fun x _ => hb1, ?_⟩
  have hdom := relOpen_H.isScDomain
  have hrep : ∀ v : H 0, StrongBundle.localRepOne (LocalBundle.chart (F := H) relOpen_H h0)
      (constSec b) v = (v, Function.invFun (H.toBase 1) b) := by
    intro v
    have h1 : ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm v : H 0) = v :=
      (LocalBundle.baseChart relOpen_H h0).toPartialEquiv.right_inv (mem_univ v)
    exact Prod.ext h1 rfl
  refine (isScSmoothRetractMap_iff_exists relOpen_H.isScRetract).2
    ⟨fun v _ => ?_, ScRetraction.id relOpen_H, image_id _, ?_⟩
  · change (_, _) ∈ (LocalBundle.chart (F := H) relOpen_H h0).R ''
      ((LocalBundle.chart (F := H) relOpen_H h0).U ×ˢ univ)
    exact ⟨_, ⟨mem_univ _, mem_univ _⟩, rfl⟩
  · have hc2 : IsScSmooth (E := H) (F := H.shift) (univ : Set (H 0))
        (fun _ => Function.invFun (H.toBase 1) b) :=
      isScSmooth_const_of_smooth hdom (by rw [Function.invFun_eq hb1]; exact hb)
    exact (IsScSmooth.scPair hdom (isScSmooth_id hdom) hc2).congr hdom
      fun v _ => (hrep v).symm

/-! ### The index -/

/-- A bijective continuous linear map has Fredholm index `0`. -/
theorem fredholmIndex_eq_zero_of_bijective {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (hL : Bijective L) :
    fredholmIndex L = 0 :=
  linIndex_equiv (LinearEquiv.ofBijective (L : E →ₗ[ℝ] F) hL)

set_option maxHeartbeats 800000 in
-- the product chart is unfolded
/-- **The Fredholm index of `f` is `0`** at every smooth point (Definition 6.2.1): for the
sc⁺-section `s(z, e) = ((z, (z − z₀) − z²), (e, −e₀))`, `(f + s)(z, e) = ((z, z − z₀), (e, e − e₀))`
vanishes at `(z₀, e₀)` and its linearization there, in the product of the chart of `ℂ` centred at
`z₀` and the chart of `H`, is the identity. -/
theorem isIndexAt_sqInf_mk (z₀ : Fin 2 → ℝ) (y : HObj)
    (hx : ((z₀, y) : Ainf.Obj) ∈ Ainf.X.PObj.smoothSet) :
    Ainf.B.IsIndexAt sqInf ((z₀, y) : Ainf.Obj) 0 := by
  classical
  have : ParacompactSpace ((Fin 2 → ℝ) × HObj) := SEP.instParacompactObjProd A5 AH
  have : ParacompactSpace ((Fin 2 → ℝ) × AH.Obj) := SEP.instParacompactObjProd A5 AH
  have : ParacompactSpace (((Fin 2 → ℝ) × (Fin 2 → ℝ)) × (HObj × H 0)) :=
    SEP.instParacompactWProd A5 AH
  have : ParacompactSpace (((Fin 2 → ℝ) × (Fin 2 → ℝ)) × AH.W) :=
    SEP.instParacompactWProd A5 AH
  have hf := isScFredholmSectionFunctor_sqInf.2
  have hy : (y : HObj) ∈ PH.smoothSet := (MPolyfold.mem_smoothSet_prod.1 hx).2
  set e : H 0 := (show HObj from y).1 with hedef
  have he : e ∈ H.smooth := mem_smoothSet_PH_iff.1 hy
  obtain ⟨e₁, he₁⟩ := (H.mem_smooth_iff.1 he) 1
  -- the sc⁺-section
  let ψ : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun z => (z - z₀) - OrbifoldSquare.sq z
  have hψ : ContDiff ℝ ∞ ψ := (contDiff_id.sub contDiff_const).sub contDiff_sq
  let S : Ainf.Obj → Ainf.W := Prod.map (graphSection ψ) (constSec (-e))
  have hS : Ainf.B.IsScPlusSection S :=
    StrongBundle.IsScPlusSection.prod (isScPlusSection_graphSection hψ)
      (isScPlusSection_constSec (H.smooth.neg_mem he))
  have hFs := hf.isScSmooth.sectionAdd hS
  -- the chart
  let c : StrongBundleChart Ainf.X.PObj Ainf.P :=
    (chart (k := 2) z₀).prod (LocalBundle.chart (F := H) relOpen_H h0)
  have hc : Ainf.B.IsChart c :=
    StrongBundle.IsChart.prod (isChart_chart (k := 2) z₀)
      (LocalBundle.isChart_chart (F := H) relOpen_H h0)
  have hsrc : ((z₀, y) : Ainf.Obj) ∈ c.φ.source := ⟨mem_univ _, mem_univ _⟩
  have hφ : c.φ ((z₀, y) : Ainf.Obj) = ((0 : Fin 2 → ℝ), e) :=
    Prod.ext (sub_self (show Fin 2 → ℝ from z₀)) rfl
  have hprin : ∀ u : (Fin 2 → ℝ) × H 0,
      c.principal (sectionAdd Ainf.P sqInf S) u = (u.1, u.2 - e) := by
    intro u
    rw [c.principal_sectionAdd hf.isScSmooth.1 hS.1 (show u ∈ c.φ.model.O from
      ⟨mem_univ _, mem_univ _⟩)]
    have h1 : ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm u.2 : H 0) = u.2 :=
      (LocalBundle.baseChart relOpen_H h0).toPartialEquiv.right_inv (mem_univ _)
    refine Prod.ext ?_ ?_
    · change OrbifoldSquare.sq (u.1 + z₀) + ((u.1 + z₀ - z₀) - OrbifoldSquare.sq (u.1 + z₀)) = u.1
      abel
    · change ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm u.2 : H 0) + -e = u.2 - e
      rw [h1, sub_eq_add_neg]
  have h0z : IsZeroAt Ainf.P (sectionAdd Ainf.P sqInf S) ((z₀, y) : Ainf.Obj) := by
    refine (c.isZeroAt_iff hFs.1 hsrc).2 ?_
    refine (congrArg (c.principal (sectionAdd Ainf.P sqInf S)) hφ).trans ?_
    exact (hprin _).trans (Prod.ext rfl (sub_self e))
  -- the chart point
  let p₀ : ChartPoint Ainf.B ((z₀, y) : Ainf.Obj) :=
    { c := c
      isChart := hc
      mem_source := hsrc
      z := ((0 : Fin 2 → ℝ), e₁)
      toBase_z := by
        rw [hφ]
        exact Prod.ext rfl he₁ }
  have hzU : p₀.z ∈ c.φ.model.E.lvlSet c.U 1 := by
    change c.φ.model.E.toBase 1 p₀.z ∈ c.U
    exact ⟨mem_univ _, mem_univ _⟩
  have hr : r c.R = id := funext fun u => rfl
  have hDr : scDeriv c.U (r c.R) p₀.z = ContinuousLinearMap.id ℝ _ := by
    rw [hr]
    exact scDeriv_eq_of_hasFDerivAt c.relOpen (isScSmooth_id c.relOpen.isScDomain 1).isSc1 hzU
      (hasFDerivAt_id _)
  have hcomp : (c.principal (sectionAdd Ainf.P sqInf S) ∘ r c.R) =
      fun u : (Fin 2 → ℝ) × H 0 => u - ((0 : Fin 2 → ℝ), e) := by
    rw [hr]
    funext u
    exact (hprin u).trans (Prod.ext (sub_zero _).symm rfl)
  have hDg : scDeriv c.U (c.principal (sectionAdd Ainf.P sqInf S) ∘ r c.R) p₀.z =
      ContinuousLinearMap.id ℝ _ := by
    refine scDeriv_eq_of_hasFDerivAt c.relOpen
      ((isScSmooth_principal_comp_r (A := Ainf) hFs hc) 1).isSc1 hzU ?_
    rw [hcomp]
    exact (hasFDerivAt_id _).sub_const _
  have hL : ∀ v : ↥p₀.T, ((p₀.stabT hf hS h0z v : ↥p₀.K) : c.F 0) = (v : c.φ.model.E 0) := by
    intro v
    rw [ChartPoint.coe_stabT, linAt_apply]
    exact congrArg (fun D : c.φ.model.E 0 →L[ℝ] c.F 0 => D (v : c.φ.model.E 0)) hDg
  have hbij : Bijective (p₀.stabT hf hS h0z) := by
    constructor
    · intro v w hvw
      have h := congrArg (fun t : ↥p₀.K => (t : c.F 0)) hvw
      simp only [hL] at h
      exact Subtype.ext h
    · intro w
      have hwT : (w : c.F 0) ∈ p₀.T :=
        ⟨(w : c.F 0), congrArg (fun D : c.φ.model.E 0 →L[ℝ] c.φ.model.E 0 => D (w : c.F 0)) hDr⟩
      exact ⟨⟨(w : c.F 0), hwT⟩, Subtype.ext (hL _)⟩
  have h := (p₀.isFredholm_isIndexAt_of_mem_linSet hf (p₀.stabT_mem_linSet hf hS h0z hx)).2
  rwa [fredholmIndex_eq_zero_of_bijective _ hbij] at h

/-- **The Fredholm index of `f` is `0`** at every smooth point (Definition 6.2.1). -/
theorem isIndexAt_sqInf (x : Ainf.Obj) (hx : x ∈ Ainf.X.PObj.smoothSet) :
    Ainf.B.IsIndexAt sqInf x 0 :=
  isIndexAt_sqInf_mk x.1 x.2 hx

end Polyfold.Examples.OrbifoldSquareInf
