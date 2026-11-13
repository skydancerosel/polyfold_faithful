import Polyfold.Chapter12.ChartPullTwoBundles
import Polyfold.Chapter12.OrientationOrbit

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, **Theorem 12.5.7** (2017: Theorem 12.12), the step for one strong bundle
equivalence: orientations of `DET(f', ϕ(a))` and of `DET(f, a)` for `f = Φ^* f'`, and the
naturality of this identification under morphisms.

## The text, paraphrased

(Proof of Theorem 12.5.7, pp. 596–597) A representative of the generalized strong bundle
isomorphism is a diagram `W ← V → W'` of strong bundle equivalences; the pull-back of `f` to `V`
and the push-forward to `W'` give bijections of the fibres of the orientation bundles,
`σ⁻¹(F(a)) → σ''⁻¹(a) → σ'⁻¹(F'(a))`, and the diagrams of morphisms relating two choices "have
canonical lifts to maps between the bundle fibers".

## What is formalized

For a strong bundle equivalence `Φ : W → W'` covering `ϕ : X → X'` (Definition 10.4.1,
`EpStrongBundle.IsStrongBundleEquivalence`), an sc-Fredholm section functor `f'` of `W'` and
`f = Φ^* f'`:

* `locIso a`: the local strong bundle isomorphism `W|U(a) → W'|U'(a)` of Definition 10.4.1 (2)
  at `a`, with base map `ϕ` and bundle map `Φ` (`locIso_ϕ`, `locIso_Φ`), along which
  `f = Ψ ∘ f' ∘ ϕ` (`eqOn_loc`).
* `eT a`, `eK a`: the maps `T_{ϕ(a)}X' → T_aX`, `W'_{ϕ(a)} → W_a` of `Φ⁻¹`, read in the chosen
  chart points; `orEqv a : Or^{f'}_{ϕ(a)} ≃ Or^f_a`, the conjugation by them (`orEqv_apply`).
* `germAgree₄_mor`: for a morphism `α : a → b`, `Φ ∘ Φ̂_α` and `Φ̂'_{ϕ(α)} ∘ Φ` (in the inverse
  direction of the text's `Φ̂`, as in `EpStrongBundle.morIso`) agree near `b`: `ϕ` maps the sheet
  of `α` into the sheet of `ϕ(α)` near `α`, and `Φ(μ(γ, w)) = μ'(ϕ(γ), Φ(w))`.
* `morTx_eT`, `morKx_eK`: `Tα ∘ eT a = eT b ∘ T(ϕ(α))` and the fibre form.
* `orMor_orEqv`: **naturality**, `α_* (orEqv a o) = orEqv b (ϕ(α)_* o)`.

## Hypotheses

Part I's `Lin(f, x) ≠ ∅` needs sc⁺-sections through smooth fibre points, here for both bundles
(`hsec`, `hsec'`; they follow from bump functions,
`MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough`), as in `OrientationBundleEp`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

open StrongRetr

universe u

section Equiv

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type u} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'}

namespace EpStrongBundle.IsStrongBundleEquivalence

variable {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (h : E.IsStrongBundleEquivalence E' ϕ Φ)

/-! ### The local strong bundle isomorphisms of the equivalence -/

/-- The open set `U(a) ∋ a` of Definition 10.4.1 (2). -/
def locSet (a : Obj) : Set Obj := (h.isLocalStrongBundleIso_obj a).choose

/-- The open set `U'(a) = ϕ(U(a))`. -/
def locSet' (a : Obj) : Set Obj' := (h.isLocalStrongBundleIso_obj a).choose_spec.choose

theorem mem_locSet (a : Obj) : a ∈ h.locSet a :=
  (h.isLocalStrongBundleIso_obj a).choose_spec.choose_spec.1

theorem isStrongBundleIsoOn_loc (a : Obj) :
    B.IsStrongBundleIsoOn B' h.isStrongBundleFunctor.isStrongBundleMap_obj (h.locSet a)
      (h.locSet' a) :=
  (h.isLocalStrongBundleIso_obj a).choose_spec.choose_spec.2

/-- **The local strong bundle isomorphism `Φ : W|U(a) → W'|U'(a)`** of Definition 10.4.1 (2). -/
def locIso (a : Obj) : StrongBundle.LocalIso B B' (h.locSet a) (h.locSet' a) :=
  (h.isStrongBundleIsoOn_loc a).toLocalIso

@[simp] lemma locIso_ϕ (a : Obj) : (h.locIso a).ϕ = ϕ.obj := rfl

@[simp] lemma locIso_Φ (a : Obj) : (h.locIso a).Φ = Φ.obj := rfl

theorem isOpen_locSet' (a : Obj) : IsOpen (h.locSet' a) := (h.locIso a).isOpen_U'

theorem isOpen_locSet (a : Obj) : IsOpen (h.locSet a) := (h.locIso a).isOpen_U

theorem obj_mem_locSet' (a : Obj) : ϕ.obj a ∈ h.locSet' a :=
  (h.locIso a).base.mapsTo (h.mem_locSet a)

include h in
/-- `a` is smooth iff `ϕ(a)` is. -/
theorem smooth_obj {a : Obj} (hs : a ∈ X.PObj.smoothSet) : ϕ.obj a ∈ X'.PObj.smoothSet :=
  ((h.locIso a).mem_smoothSet_iff (h.mem_locSet a)).1 hs

include h in
theorem smooth_of_obj {a : Obj} (hs : ϕ.obj a ∈ X'.PObj.smoothSet) : a ∈ X.PObj.smoothSet :=
  ((h.locIso a).mem_smoothSet_iff (h.mem_locSet a)).2 hs

/-- Near `a`, the pull-back is `Ψ ∘ f' ∘ ϕ`. -/
theorem eqOn_locIso {f' : Obj' → W'} (hf' : IsSection P' f') (a : Obj) :
    EqOn (h.pullback f') ((h.locIso a).Ψ ∘ f' ∘ (h.locIso a).ϕ) (h.locSet a) :=
  (h.eqOn_pullback hf' (h.locIso a).base (h.locIso a).zero).symm

/-- The chart point at `ϕ(a)` inside `U'(a)` (the chosen chart restricted). -/
abbrev locPt (a : Obj) (hs : a ∈ X.PObj.smoothSet) : ChartPoint B' (ϕ.obj a) :=
  restrPt B' (ϕ.obj a) (h.isOpen_locSet' a) (h.obj_mem_locSet' a) (h.smooth_obj hs)

/-! ### The maps `T_{ϕ(a)}X' → T_aX` and `W'_{ϕ(a)} → W_a` -/

/-- **`T_{ϕ(a)}X' → T_aX`**, the derivative of `ϕ⁻¹` near `ϕ(a)`, read in the chosen chart
points. -/
def eT (a : Obj) (hs : a ∈ X.PObj.smoothSet) :
    ↥(orPt B' (ϕ.obj a) (h.smooth_obj hs)).T ≃L[ℝ] ↥(orPt B a hs).T :=
  (h.locIso a).mmorT (orPt B' _ _) (orPt B a hs) (h.locPt a hs) (restrPt_sub _ _ _ _)
    (h.mem_locSet a) rfl

/-- **`W'_{ϕ(a)} → W_a`**, the inverse of `Φ` on the fibre, read in the chosen chart points. -/
def eK (a : Obj) (hs : a ∈ X.PObj.smoothSet) :
    ↥(orPt B' (ϕ.obj a) (h.smooth_obj hs)).K ≃L[ℝ] ↥(orPt B a hs).K :=
  (h.locIso a).mmorK (orPt B' _ _) (orPt B a hs) (h.locPt a hs) (restrPt_sub _ _ _ _)
    (h.mem_locSet a) rfl

theorem eT_eq {a : Obj} (hs : a ∈ X.PObj.smoothSet) (p : ChartPoint B' (ϕ.obj a))
    (hp : p.c.φ.source ⊆ h.locSet' a) (v) :
    h.eT a hs v = (h.locIso a).mmorT (orPt B' _ _) (orPt B a hs) p hp (h.mem_locSet a) rfl v :=
  (h.locIso a).mmorT_eq _ _ _ _ _ _ v

theorem eK_eq {a : Obj} (hs : a ∈ X.PObj.smoothSet) (p : ChartPoint B' (ϕ.obj a))
    (hp : p.c.φ.source ⊆ h.locSet' a) (k) :
    h.eK a hs k = (h.locIso a).mmorK (orPt B' _ _) (orPt B a hs) p hp (h.mem_locSet a) rfl k :=
  (h.locIso a).mmorK_eq _ _ _ _ _ _ k

/-! ### The identification of orientations -/

section Or

variable {f : Obj → W} {f' : Obj' → W'} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hpb : f = h.pullback f')
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)

include hpb in
/-- Near `a`, `f = Ψ ∘ f' ∘ ϕ`. -/
theorem eqOn_loc (hf' : IsSection P' f') (a : Obj) :
    EqOn f ((h.locIso a).Ψ ∘ f' ∘ (h.locIso a).ϕ) (h.locSet a) :=
  hpb ▸ h.eqOn_locIso hf' a

include hF hF' hpb hsec hsec' in
/-- `Lin(f, a)` read in a carried chart point is `Lin(f', ϕ(a))`. -/
theorem linSet_loc {a : Obj} (hs : a ∈ X.PObj.smoothSet) (p : ChartPoint B' (ϕ.obj a))
    (hp : p.c.φ.source ⊆ h.locSet' a) :
    ((h.locIso a).mpullPt p hp (h.mem_locSet a) rfl).linSet f = p.linSet f' :=
  StrongBundle.LocalIso.linSet_mpullPt hF.2 hF'.2 (h.eqOn_loc hpb hF'.2.isScSmooth.1 a) hsec
    hsec' hs (h.smooth_obj hs)

include hF hF' hpb hsec hsec' in
theorem eT_mem {a : Obj} (hs : a ∈ X.PObj.smoothSet) :
    ∀ S ∈ (orPt B a hs).linSet f, (((h.eK a hs).symm : ↥(orPt B a hs).K →L[ℝ] _) ∘L S ∘L
      (h.eT a hs : ↥(orPt B' (ϕ.obj a) (h.smooth_obj hs)).T →L[ℝ] _)) ∈
        (orPt B' (ϕ.obj a) (h.smooth_obj hs)).linSet f' :=
  StrongBundle.LocalIso.mmorT_mem hF.2 hF'.2 (h.linSet_loc hF hF' hpb hsec hsec' hs _ _)
    (h.smooth_obj hs) hs

/-- **`Or^{f'}_{ϕ(a)} ≃ Or^f_a`**: an orientation of `DET(f', ϕ(a))` carried to one of
`DET(f, a)` along `Φ⁻¹` (through `U(a)`). -/
def orEqv (a : Obj) (hs : a ∈ X.PObj.smoothSet) :
    Orx f' hF'.2 (ϕ.obj a) (h.smooth_obj hs) ≃ Orx f hF.2 a hs :=
  (h.locIso a).morVia hF.2 hF'.2 (orPt B' _ _) (orPt B a hs) (h.locPt a hs)
    (restrPt_sub _ _ _ _) (h.mem_locSet a) rfl (h.linSet_loc hF hF' hpb hsec hsec' hs _ _)
    (h.smooth_obj hs) hs

/-- `orEqv` is the conjugation by `eT` and `eK`. -/
theorem orEqv_apply (a : Obj) (hs : a ∈ X.PObj.smoothSet)
    (o : Orx f' hF'.2 (ϕ.obj a) (h.smooth_obj hs)) :
    h.orEqv hF hF' hpb hsec hsec' a hs o =
      o.conj (hC' := (orPt B a hs).isFredholm_of_mem_linSet hF.2) (h.eT a hs) (h.eK a hs)
        (h.eT_mem hF hF' hpb hsec hsec' hs) :=
  StrongBundle.LocalIso.morVia_apply _ _ _ _ _ _ _ _ _ _ _ _ o

end Or

/-! ### Naturality under morphisms -/

section Natural

variable {α : Mor} {a b : Obj}

omit [ParacompactSpace (pullbackSpace P X.src)] [ParacompactSpace (pullbackSpace P' X'.src)] in
theorem src_mor_eq (ha : X.src α = a) : X'.src (ϕ.mor α) = ϕ.obj a :=
  (ϕ.src_mor α).trans (congrArg ϕ.obj ha)

omit [ParacompactSpace (pullbackSpace P X.src)] [ParacompactSpace (pullbackSpace P' X'.src)] in
theorem tgt_mor_eq (hb : X.tgt α = b) : X'.tgt (ϕ.mor α) = ϕ.obj b :=
  (ϕ.tgt_mor α).trans (congrArg ϕ.obj hb)

omit [ParacompactSpace (pullbackSpace P X.src)] [ParacompactSpace (pullbackSpace P' X'.src)] in
theorem continuous_mor (ϕ : EpFunctor X X') : Continuous ϕ.mor :=
  continuousOn_univ.1 ϕ.isScSmoothMap_mor.continuousOn

include h in
/-- **The local isomorphisms of `α` and of `ϕ(α)` correspond under `Φ`**: the composites
`Φ ∘ Φ̂_α` and `Φ̂'_{ϕ(α)} ∘ Φ` (inverse direction, `EpStrongBundle.morIso`) have the same germ
at `b = t(α)`. -/
theorem germAgree₄_mor (hb : X.tgt α = b) :
    StrongBundle.LocalIso.GermAgree₄ (h.locIso a) (E.morIso α) (E'.morIso (ϕ.mor α))
      (h.locIso b) b := by
  set S := X.sheetAt α with hS
  set S' := X'.sheetAt (ϕ.mor α) with hS'
  have hτc : ContinuousOn S.tgtInv S.tgtSet := S.isScDiffeoOn_tgt.isScSmoothOn_inv.continuousOn
  have hO₁ : IsOpen (S.tgtSet ∩ S.tgtInv ⁻¹' (ϕ.mor ⁻¹' S'.carrier)) :=
    hτc.isOpen_inter_preimage S.isScDiffeoOn_tgt.isOpen_target
      (S'.isScDiffeoOn_tgt.isOpen_source.preimage (continuous_mor ϕ))
  set N := (S.tgtSet ∩ S.tgtInv ⁻¹' (ϕ.mor ⁻¹' S'.carrier)) ∩ h.locSet b with hN
  have key : ∀ y ∈ N, S'.tgtInv (ϕ.obj y) = ϕ.mor (S.tgtInv y) ∧ ϕ.obj y ∈ S'.tgtSet := by
    rintro y ⟨⟨hyT, hyC⟩, -⟩
    have hm' : ϕ.mor (S.tgtInv y) ∈ S'.carrier := hyC
    have ht : X'.tgt (ϕ.mor (S.tgtInv y)) = ϕ.obj y := by
      rw [ϕ.tgt_mor]; exact congrArg ϕ.obj (S.isScDiffeoOn_tgt.right_inv y hyT)
    refine ⟨?_, ht ▸ S'.isScDiffeoOn_tgt.mapsTo hm'⟩
    rw [← ht]; exact S'.isScDiffeoOn_tgt.left_inv _ hm'
  refine ⟨⟨N, hO₁.inter (h.isOpen_locSet b), ?_, fun y hy => hy.1.1, fun y hy => hy.2,
    fun y hy => ?_, fun w hw => ?_⟩⟩
  · have hbT : b ∈ S.tgtSet := mem_tgtSet hb
    refine ⟨⟨hbT, ?_⟩, h.mem_locSet b⟩
    change ϕ.mor (S.tgtInv b) ∈ S'.carrier
    rw [← hb, tgtInv_tgt]; exact X'.mem_sheetAt _
  · obtain ⟨h1, -⟩ := key y hy
    change ϕ.obj (X.src (S.tgtInv y)) = X'.src (S'.tgtInv (ϕ.obj y))
    rw [h1, ϕ.src_mor]
  · obtain ⟨h1, h2⟩ := key (P w) hw
    have hw1 : P w = X.src (morInvSec X α (P w)) := (src_morInvSec α hw.1.1).symm
    have hcov : P' (Φ.obj w) = ϕ.obj (P w) := h.covers w
    have hw2 : P' (Φ.obj w) = X'.src (morInvSec X' (ϕ.mor α) (P' (Φ.obj w))) :=
      (src_morInvSec (ϕ.mor α) (hcov ▸ h2)).symm
    change Φ.obj (E.sectionAct (morInvSec X α) w) =
      E'.sectionAct (morInvSec X' (ϕ.mor α)) (Φ.obj w)
    rw [E.sectionAct_of_eq _ hw1, h.isStrongBundleFunctor.isMap.map_μ, E'.sectionAct_of_eq _ hw2]
    refine E'.μ_mk_congr ?_ rfl _ _
    change ϕ.mor (X.inv (S.tgtInv (P w))) = X'.inv (S'.tgtInv (P' (Φ.obj w)))
    rw [hcov, h1]
    exact ϕ.toGroupoidFunctor.mor_inv _

/-- The chart point at `ϕ(a)` used to compare `Tα` and `T(ϕ(α))`: inside `U'(a)`, inside
`ϕ(U(a) ∩ s(sheet α))`, inside `s(sheet ϕ(α))` and inside the preimage of `U'(b)`. -/
def natSet (α : Mor) (a b : Obj) : Set Obj' :=
  (h.locSet' a ∩ (h.locIso a).g ⁻¹' (X.sheetAt α).srcSet) ∩
    ((X'.sheetAt (ϕ.mor α)).srcSet ∩ (E'.morIso (ϕ.mor α)).g ⁻¹' h.locSet' b)

theorem isOpen_natSet (α : Mor) (a b : Obj) : IsOpen (h.natSet α a b) :=
  ((h.locIso a).base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage (h.isOpen_locSet' a)
    (isOpen_srcSet α)).inter
    ((E'.morIso (ϕ.mor α)).base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage
      (isOpen_srcSet _) (h.isOpen_locSet' b))

theorem mem_natSet (ha : X.src α = a) (hb : X.tgt α = b) : ϕ.obj a ∈ h.natSet α a b := by
  have ha' := src_mor_eq (ϕ := ϕ) ha
  have hb' := tgt_mor_eq (ϕ := ϕ) hb
  refine ⟨⟨h.obj_mem_locSet' a, ?_⟩, mem_srcSet ha', ?_⟩
  · change (h.locIso a).g ((h.locIso a).ϕ a) ∈ (X.sheetAt α).srcSet
    rw [(h.locIso a).base.left_inv a (h.mem_locSet a)]; exact mem_srcSet ha
  · change (E'.morIso (ϕ.mor α)).g (ϕ.obj a) ∈ h.locSet' b
    rw [← E'.morIso_ϕ_eq ha' hb', (E'.morIso (ϕ.mor α)).base.left_inv _ (mem_tgtSet hb')]
    exact h.obj_mem_locSet' b

/-- **`Tα ∘ eT a = eT b ∘ T(ϕ(α))`** (read in the chosen chart points). -/
theorem morTx_eT {ha : X.src α = a} {hb : X.tgt α = b} (hs : a ∈ X.PObj.smoothSet)
    (hsb : b ∈ X.PObj.smoothSet)
    (v : ↥(orPt B' (ϕ.obj a) (h.smooth_obj hs)).T) :
    E.morTx α ha hb hs hsb (h.eT a hs v) =
      h.eT b hsb (E'.morTx (ϕ.mor α) (src_mor_eq ha) (tgt_mor_eq hb) (h.smooth_obj hs)
        (h.smooth_obj hsb) v) := by
  have ha' := src_mor_eq (ϕ := ϕ) ha
  have hb' := tgt_mor_eq (ϕ := ϕ) hb
  set p := restrPt B' (ϕ.obj a) (h.isOpen_natSet α a b) (h.mem_natSet ha hb) (h.smooth_obj hs)
    with hp
  have hpV : p.c.φ.source ⊆ h.natSet α a b := restrPt_sub _ _ _ _
  have hpa : p.c.φ.source ⊆ h.locSet' a := fun y hy => (hpV hy).1.1
  have hpm : p.c.φ.source ⊆ (X'.sheetAt (ϕ.mor α)).srcSet := fun y hy => (hpV hy).2.1
  set r := (h.locIso a).mpullPt p hpa (h.mem_locSet a) rfl with hr
  have hrs : r.c.φ.source ⊆ (X.sheetAt α).srcSet := by
    rintro y ⟨hyU, hyp⟩
    have := (hpV hyp).1.2
    change (h.locIso a).g ((h.locIso a).ϕ y) ∈ (X.sheetAt α).srcSet at this
    rwa [(h.locIso a).base.left_inv y hyU] at this
  set q := (E'.morIso (ϕ.mor α)).pullPt p hpm (mem_tgtSet hb') (E'.morIso_ϕ_eq ha' hb') with hq
  have hqs : q.c.φ.source ⊆ h.locSet' b := by
    rintro y ⟨hyU, hyp⟩
    have := (hpV hyp).2.2
    change (E'.morIso (ϕ.mor α)).g ((E'.morIso (ϕ.mor α)).ϕ y) ∈ h.locSet' b at this
    rwa [(E'.morIso (ϕ.mor α)).base.left_inv y hyU] at this
  set A := (E.morIso α).pullPt r hrs (mem_tgtSet hb) (E.morIso_ϕ_eq ha hb) with hA
  set Bq := (h.locIso b).mpullPt q hqs (h.mem_locSet b) rfl with hBq
  set t := (orPt B' (ϕ.obj a) (h.smooth_obj hs)).transferT p v
  have e1 : E.morTx α ha hb hs hsb (h.eT a hs v) = A.transferT (orPt B b hsb) t := by
    rw [h.eT_eq hs p hpa, E.morTx_eq α ha hb hs hsb r hrs]
    exact congrArg (A.transferT (orPt B b hsb))
      ((r.transferT_trans_apply (orPt B a hs) r t).trans (r.transferT_self_apply t))
  have e2 : h.eT b hsb (E'.morTx (ϕ.mor α) (src_mor_eq ha) (tgt_mor_eq hb) (h.smooth_obj hs)
      (h.smooth_obj hsb) v) = Bq.transferT (orPt B b hsb) t := by
    rw [E'.morTx_eq (ϕ.mor α) ha' hb' (h.smooth_obj hs) (h.smooth_obj hsb) p hpm,
      h.eT_eq hsb q hqs]
    exact congrArg (Bq.transferT (orPt B b hsb))
      ((q.transferT_trans_apply (orPt B' (ϕ.obj b) (h.smooth_obj hsb)) q t).trans
        (q.transferT_self_apply t))
  have h4 := StrongBundle.LocalIso.transferT_mpullPt₄ (L := h.locIso a) (L₂ := E.morIso α)
    (M := E'.morIso (ϕ.mor α)) (M₂ := h.locIso b) p hpa (h.mem_locSet a) rfl hrs (mem_tgtSet hb)
    (E.morIso_ϕ_eq ha hb) hpm (mem_tgtSet hb') (E'.morIso_ϕ_eq ha' hb') hqs (h.mem_locSet b) rfl
    (h.germAgree₄_mor (a := a) hb) t
  have e3 : A.transferT (orPt B b hsb) t = Bq.transferT (orPt B b hsb) t :=
    (congrArg (A.transferT (orPt B b hsb)) (Subtype.ext h4).symm).trans
      (ChartPoint.transferT_trans_apply Bq A (orPt B b hsb) t)
  exact e1.trans (e3.trans e2.symm)

/-- **`μ(α, ·) ∘ eK a = eK b ∘ μ'(ϕ(α), ·)`** (read in the chosen chart points). -/
theorem morKx_eK {ha : X.src α = a} {hb : X.tgt α = b} (hs : a ∈ X.PObj.smoothSet)
    (hsb : b ∈ X.PObj.smoothSet)
    (k : ↥(orPt B' (ϕ.obj a) (h.smooth_obj hs)).K) :
    E.morKx α ha hb hs hsb (h.eK a hs k) =
      h.eK b hsb (E'.morKx (ϕ.mor α) (src_mor_eq ha) (tgt_mor_eq hb) (h.smooth_obj hs)
        (h.smooth_obj hsb) k) := by
  have ha' := src_mor_eq (ϕ := ϕ) ha
  have hb' := tgt_mor_eq (ϕ := ϕ) hb
  set p := restrPt B' (ϕ.obj a) (h.isOpen_natSet α a b) (h.mem_natSet ha hb) (h.smooth_obj hs)
    with hp
  have hpV : p.c.φ.source ⊆ h.natSet α a b := restrPt_sub _ _ _ _
  have hpa : p.c.φ.source ⊆ h.locSet' a := fun y hy => (hpV hy).1.1
  have hpm : p.c.φ.source ⊆ (X'.sheetAt (ϕ.mor α)).srcSet := fun y hy => (hpV hy).2.1
  set r := (h.locIso a).mpullPt p hpa (h.mem_locSet a) rfl with hr
  have hrs : r.c.φ.source ⊆ (X.sheetAt α).srcSet := by
    rintro y ⟨hyU, hyp⟩
    have := (hpV hyp).1.2
    change (h.locIso a).g ((h.locIso a).ϕ y) ∈ (X.sheetAt α).srcSet at this
    rwa [(h.locIso a).base.left_inv y hyU] at this
  set q := (E'.morIso (ϕ.mor α)).pullPt p hpm (mem_tgtSet hb') (E'.morIso_ϕ_eq ha' hb') with hq
  have hqs : q.c.φ.source ⊆ h.locSet' b := by
    rintro y ⟨hyU, hyp⟩
    have := (hpV hyp).2.2
    change (E'.morIso (ϕ.mor α)).g ((E'.morIso (ϕ.mor α)).ϕ y) ∈ h.locSet' b at this
    rwa [(E'.morIso (ϕ.mor α)).base.left_inv y hyU] at this
  set A := (E.morIso α).pullPt r hrs (mem_tgtSet hb) (E.morIso_ϕ_eq ha hb) with hA
  set Bq := (h.locIso b).mpullPt q hqs (h.mem_locSet b) rfl with hBq
  set t := (orPt B' (ϕ.obj a) (h.smooth_obj hs)).transferK p k
  have e1 : E.morKx α ha hb hs hsb (h.eK a hs k) = A.transferK (orPt B b hsb) t := by
    rw [h.eK_eq hs p hpa, E.morKx_eq α ha hb hs hsb r hrs]
    exact congrArg (A.transferK (orPt B b hsb))
      ((r.transferK_trans_apply (orPt B a hs) r t).trans (r.transferK_self_apply t))
  have e2 : h.eK b hsb (E'.morKx (ϕ.mor α) (src_mor_eq ha) (tgt_mor_eq hb) (h.smooth_obj hs)
      (h.smooth_obj hsb) k) = Bq.transferK (orPt B b hsb) t := by
    rw [E'.morKx_eq (ϕ.mor α) ha' hb' (h.smooth_obj hs) (h.smooth_obj hsb) p hpm,
      h.eK_eq hsb q hqs]
    exact congrArg (Bq.transferK (orPt B b hsb))
      ((q.transferK_trans_apply (orPt B' (ϕ.obj b) (h.smooth_obj hsb)) q t).trans
        (q.transferK_self_apply t))
  have h4 := StrongBundle.LocalIso.transferK_mpullPt₄ (L := h.locIso a) (L₂ := E.morIso α)
    (M := E'.morIso (ϕ.mor α)) (M₂ := h.locIso b) p hpa (h.mem_locSet a) rfl hrs (mem_tgtSet hb)
    (E.morIso_ϕ_eq ha hb) hpm (mem_tgtSet hb') (E'.morIso_ϕ_eq ha' hb') hqs (h.mem_locSet b) rfl
    (h.germAgree₄_mor (a := a) hb) t
  have e3 : A.transferK (orPt B b hsb) t = Bq.transferK (orPt B b hsb) t :=
    (congrArg (A.transferK (orPt B b hsb)) (Subtype.ext h4).symm).trans
      (ChartPoint.transferK_trans_apply Bq A (orPt B b hsb) t)
  exact e1.trans (e3.trans e2.symm)

end Natural

/-! ### Naturality of the identification of orientations -/

section OrNatural

variable {f : Obj → W} {f' : Obj' → W'} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hpb : f = h.pullback f')
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)

/-- **Naturality of `orEqv`** (the "canonical lifts" in the proof of Theorem 12.5.7, p. 597):
for a morphism `α : a → b` between smooth objects, `α_* ∘ orEqv a = orEqv b ∘ ϕ(α)_*`. -/
theorem orMor_orEqv {α : Mor} {a b : Obj} (ha : X.src α = a) (hb : X.tgt α = b)
    (hs : a ∈ X.PObj.smoothSet) (hsb : b ∈ X.PObj.smoothSet)
    (o : Orx f' hF'.2 (ϕ.obj a) (h.smooth_obj hs)) :
    E.orMor hF hsec α ha hb hs hsb (h.orEqv hF hF' hpb hsec hsec' a hs o) =
      h.orEqv hF hF' hpb hsec hsec' b hsb (E'.orMor hF' hsec' (ϕ.mor α) (src_mor_eq ha)
        (tgt_mor_eq hb) (h.smooth_obj hs) (h.smooth_obj hsb) o) := by
  have m1 := h.eT_mem hF hF' hpb hsec hsec' hs
  have m2 := E.morTx_mem hF hsec α ha hb hs hsb
  have m3 := E'.morTx_mem hF' hsec' (ϕ.mor α) (src_mor_eq ha) (tgt_mor_eq hb) (h.smooth_obj hs)
    (h.smooth_obj hsb)
  have m4 := h.eT_mem hF hF' hpb hsec hsec' hsb
  have eL : E.orMor hF hsec α ha hb hs hsb (h.orEqv hF hF' hpb hsec hsec' a hs o) =
      o.conj (hC' := (orPt B b hsb).isFredholm_of_mem_linSet hF.2)
        ((h.eT a hs).trans (E.morTx α ha hb hs hsb)) ((h.eK a hs).trans (E.morKx α ha hb hs hsb))
        (conj_mem_trans _ _ _ _ m1 m2) := by
    refine (E.orMor_apply hF hsec α ha hb hs hsb (h.orEqv hF hF' hpb hsec hsec' a hs o)).trans ?_
    rw [h.orEqv_apply]
    exact (LineOrientation.conj_trans
      (hC' := (orPt B a hs).isFredholm_of_mem_linSet hF.2)
      (hC'' := (orPt B b hsb).isFredholm_of_mem_linSet hF.2) (h.eT a hs) (h.eK a hs)
      (E.morTx α ha hb hs hsb) (E.morKx α ha hb hs hsb) m1 m2 (conj_mem_trans _ _ _ _ m1 m2) o)
  have eR : h.orEqv hF hF' hpb hsec hsec' b hsb (E'.orMor hF' hsec' (ϕ.mor α) (src_mor_eq ha)
        (tgt_mor_eq hb) (h.smooth_obj hs) (h.smooth_obj hsb) o) =
      o.conj (hC' := (orPt B b hsb).isFredholm_of_mem_linSet hF.2)
        ((E'.morTx (ϕ.mor α) (src_mor_eq ha) (tgt_mor_eq hb) (h.smooth_obj hs)
          (h.smooth_obj hsb)).trans (h.eT b hsb))
        ((E'.morKx (ϕ.mor α) (src_mor_eq ha) (tgt_mor_eq hb) (h.smooth_obj hs)
          (h.smooth_obj hsb)).trans (h.eK b hsb))
        (conj_mem_trans _ _ _ _ m3 m4) := by
    refine (h.orEqv_apply hF hF' hpb hsec hsec' b hsb (E'.orMor hF' hsec' (ϕ.mor α)
      (src_mor_eq ha) (tgt_mor_eq hb) (h.smooth_obj hs) (h.smooth_obj hsb) o)).trans ?_
    rw [E'.orMor_apply]
    exact (LineOrientation.conj_trans
      (hC' := (orPt B' (ϕ.obj b) (h.smooth_obj hsb)).isFredholm_of_mem_linSet hF'.2)
      (hC'' := (orPt B b hsb).isFredholm_of_mem_linSet hF.2)
      (E'.morTx (ϕ.mor α) (src_mor_eq ha) (tgt_mor_eq hb) (h.smooth_obj hs) (h.smooth_obj hsb))
      (E'.morKx (ϕ.mor α) (src_mor_eq ha) (tgt_mor_eq hb) (h.smooth_obj hs) (h.smooth_obj hsb))
      (h.eT b hsb) (h.eK b hsb) m3 m4 (conj_mem_trans _ _ _ _ m3 m4) o)
  have hA : ∀ v, ((h.eT a hs).trans (E.morTx α ha hb hs hsb)) v =
      ((E'.morTx (ϕ.mor α) (src_mor_eq ha) (tgt_mor_eq hb) (h.smooth_obj hs)
        (h.smooth_obj hsb)).trans (h.eT b hsb)) v := fun v => by
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply]
    exact h.morTx_eT (ha := ha) (hb := hb) hs hsb v
  have hΓ : ∀ k, ((h.eK a hs).trans (E.morKx α ha hb hs hsb)) k =
      ((E'.morKx (ϕ.mor α) (src_mor_eq ha) (tgt_mor_eq hb) (h.smooth_obj hs)
        (h.smooth_obj hsb)).trans (h.eK b hsb)) k := fun k => by
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply]
    exact h.morKx_eK (ha := ha) (hb := hb) hs hsb k
  exact eL.trans ((LineOrientation.conj_congr hA hΓ _ _ o).trans eR.symm)

end OrNatural

end EpStrongBundle.IsStrongBundleEquivalence

end Equiv

end Polyfold
