import Polyfold.Chapter12.P3W5OR_Theorem1253
import Polyfold.Chapter12.P3F_EquivalenceOr

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 594–597: tools for Proposition 12.5.6 and Theorem 12.5.7 (2017: Proposition 12.4,
Theorem 12.12).

# The orientation map of a local isomorphism depends only on its germ

* `LocalIso.GermEq L₁ L₃ b`: two local strong bundle isomorphisms `Y|U₁ → Y'|U₁'` and
  `Y|U₃ → Y'|U₃'` with the same base and bundle maps near `b`.
* `LocalIso.morVia_germ`: then they act in the same way on orientations at `b` (the carried chart
  points have the identity as transition at `b`: `baseDeriv_mpullPt_germ`,
  `fiberMap_mpullPt_germ`).
* `EpStrongBundle.germEq_morIso_sheet`: for `y'` in the target of the sheet of `φ`, the isomorphism
  of `φ` and that of the morphism `σ' = (t|sheet)⁻¹(y')` agree near `y'` (`t` is injective on a
  sheet).  `EpStrongBundle.pullOrx_morIso_eq_orMor`: hence the section carried by the
  isomorphism of `φ` is, at every `y'`, the action `σ'_*` of the morphism of the sheet ending
  at `y'`.
* `IsStrongBundleEquivalence.orEqv_eq_orxVia`: for an equivalence, `orEqv b` is the orientation
  map of the local isomorphism at any `a` with `b ∈ U(a)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

open StrongRetr

universe u v u' v'

section GermLocal

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'}

namespace StrongBundle.LocalIso

variable {U₁ U₃ : Set X} {U₁' U₃' : Set X'}

/-- **Two local isomorphisms with the same germ at `b`**: on an open `N ∋ b` inside both domains
the base maps and the bundle maps agree. -/
structure GermEq (L₁ : LocalIso B B' U₁ U₁') (L₃ : LocalIso B B' U₃ U₃') (b : X) : Prop where
  exists_nhds : ∃ N : Set X, IsOpen N ∧ b ∈ N ∧ N ⊆ U₁ ∧ N ⊆ U₃ ∧
    (∀ y ∈ N, L₁.ϕ y = L₃.ϕ y) ∧ ∀ w, P w ∈ N → L₁.Φ w = L₃.Φ w

variable {L₁ : LocalIso B B' U₁ U₁'} {L₃ : LocalIso B B' U₃ U₃'} {x : X'} {b : X}

/-- **Carried chart points of two isomorphisms with the same germ**: the base derivative between
them is `Dr(z)`, as from a chart point to itself. -/
theorem baseDeriv_mpullPt_germ (p : ChartPoint B' x) (h₁ : p.c.φ.source ⊆ U₁') (hb₁ : b ∈ U₁)
    (hϕ₁ : L₁.ϕ b = x) (h₃ : p.c.φ.source ⊆ U₃') (hb₃ : b ∈ U₃) (hϕ₃ : L₃.ϕ b = x)
    (hG : GermEq L₁ L₃ b) (v : p.c.φ.model.E 0) :
    (L₃.mpullPt p h₃ hb₃ hϕ₃).baseDeriv (L₁.mpullPt p h₁ hb₁ hϕ₁) v = p.baseDeriv p v := by
  obtain ⟨N, hNo, hbN, -, -, hNϕ, -⟩ := hG.exists_nhds
  set a₃ := L₃.mpullPt p h₃ hb₃ hϕ₃ with ha₃
  set a₁ := L₁.mpullPt p h₁ hb₁ hϕ₁ with ha₁
  obtain ⟨G, hGo, hG⟩ := a₃.c.φ.exists_isOpen_image_eq (s := N ∩ a₃.c.φ.source)
    inter_subset_right (hNo.inter a₃.c.φ.isOpen_source)
  set R' := (a₃.baseRet a₁).restrict hGo with hR'
  have hV₁ : R'.U ⊆ (a₃.baseRet a₁).U := inter_subset_left
  have hV₂ : R'.U ⊆ p.c.U := fun u hu => (a₃.baseRet_U_subset a₁) hu.1
  have hzG : r p.c.R (p.c.φ.model.E.toBase 1 p.z) ∈ G := by
    rw [p.r_toBase_z]
    have : a₃.c.φ b ∈ a₃.c.φ '' (N ∩ a₃.c.φ.source) := ⟨b, ⟨hbN, a₃.mem_source⟩, rfl⟩
    rw [hG] at this
    have h' : a₃.c.φ b = p.c.φ.model.E.toBase 1 p.z := a₃.toBase_z.symm
    rw [h'] at this
    exact this.2
  have hzV : p.z ∈ p.c.φ.model.E.lvlSet R'.U 1 := ⟨a₃.z_mem_baseRet a₁, hzG⟩
  have hr1 : IsSc1 p.c.U (r p.c.R) := (r_isScSmooth p.c.relOpen p.c.isRetraction).isSc1
  have hOO : a₃.c.φ.model.O = p.c.φ.model.O := L₃.transportChart_model_O p.c h₃
  have heq : EqOn (a₃.c.φ.transition a₁.c.φ ∘ a₃.baseRet a₁) (r p.c.R) R'.U := by
    intro u hu
    obtain ⟨y, hy, hy', hyu⟩ := a₃.exists_eq_of_mem_baseRet a₁ (hV₁ hu)
    have hrG : r p.c.R u ∈ a₃.c.φ.model.O ∩ G := ⟨hOO ▸ p.c.r_mem_O (hV₂ hu), hu.2⟩
    rw [← hG] at hrG
    obtain ⟨y₂, ⟨hy₂N, hy₂s⟩, hy₂u⟩ := hrG
    have hyy : y₂ = y := by
      have e : a₃.c.φ y₂ = a₃.c.φ y := hy₂u.trans hyu
      rw [← a₃.c.φ.symm_apply_apply hy₂s, ← a₃.c.φ.symm_apply_apply hy, e]
    subst hyy
    have hyu' : r p.c.R u = p.c.φ (L₃.ϕ y₂) := hyu
    change p.c.φ (L₁.ϕ (L₃.g (p.c.φ.symm (r p.c.R u)))) = r p.c.R u
    rw [hyu', p.c.φ.symm_apply_apply hy.2, L₃.base.left_inv y₂ hy.1, hNϕ y₂ hy₂N]
  have := scDeriv_eq_of_eqOn_relOpen R'.relOpen (a₃.isSc1_transition a₁) hr1 hV₁ hV₂ heq hzV
  rw [p.baseDeriv_self]
  exact congrArg (fun T : p.c.φ.model.E 0 →L[ℝ] p.c.φ.model.E 0 => T v) this

/-- **Carried chart points of two isomorphisms with the same germ**: the fibre transition between
them is the identity on `K_z`. -/
theorem fiberMap_mpullPt_germ (p : ChartPoint B' x) (h₁ : p.c.φ.source ⊆ U₁') (hb₁ : b ∈ U₁)
    (hϕ₁ : L₁.ϕ b = x) (h₃ : p.c.φ.source ⊆ U₃') (hb₃ : b ∈ U₃) (hϕ₃ : L₃.ϕ b = x)
    (hG : GermEq L₁ L₃ b) (k : p.c.F 0) :
    (L₃.mpullPt p h₃ hb₃ hϕ₃).fiberMap (L₁.mpullPt p h₁ hb₁ hϕ₁) k = p.fiberMap p k := by
  obtain ⟨N, -, hbN, -, -, -, hNΦ⟩ := hG.exists_nhds
  set w : p.c.φ.model.E 0 × p.c.F 0 :=
    (p.c.φ.model.E.toBase 1 p.z, ρ p.c.R (p.c.φ.model.E.toBase 1 p.z) k) with hw
  have hwK : w ∈ p.c.toPartialEquiv.target := by
    rw [p.c.target_eq]; exact p.c.mem_K_ρ p.toBase_z_mem_O k
  have hsrc := p.c.toPartialEquiv.map_target hwK
  have hPx : P' (p.c.toPartialEquiv.symm w) = x := by
    have h1 := p.c.covers _ hsrc
    rw [p.c.toPartialEquiv.right_inv hwK] at h1
    have h2 : p.c.φ.model.E.toBase 1 p.z = p.c.φ (P' (p.c.toPartialEquiv.symm w)) := h1
    rw [p.c.source_eq] at hsrc
    rw [p.toBase_z] at h2
    rw [← p.c.φ.symm_apply_apply hsrc, ← h2, p.c.φ.symm_apply_apply p.mem_source]
  have hU₃' : P' (p.c.toPartialEquiv.symm w) ∈ U₃' := by rw [hPx]; exact h₃ p.mem_source
  have hPb : P (L₃.Ψ (p.c.toPartialEquiv.symm w)) ∈ N := by
    rw [L₃.covers_inv _ hU₃', hPx, ← hϕ₃, L₃.base.left_inv _ hb₃]; exact hbN
  change (p.c (L₁.Φ (L₃.Ψ (p.c.toPartialEquiv.symm w)))).2 =
    (p.c (p.c.toPartialEquiv.symm w)).2
  rw [hNΦ _ hPb, L₃.zero.right_inv _ hU₃']

/-- The identification of `T_bX` between the two carried chart points is the identity. -/
theorem transferT_mpullPt_germ (p : ChartPoint B' x) (h₁ : p.c.φ.source ⊆ U₁') (hb₁ : b ∈ U₁)
    (hϕ₁ : L₁.ϕ b = x) (h₃ : p.c.φ.source ⊆ U₃') (hb₃ : b ∈ U₃) (hϕ₃ : L₃.ϕ b = x)
    (hG : GermEq L₁ L₃ b) (v : ↥p.T) :
    (Subtype.val ((L₃.mpullPt p h₃ hb₃ hϕ₃).transferT (L₁.mpullPt p h₁ hb₁ hϕ₁) v) :
      p.c.φ.model.E 0) = v :=
  (baseDeriv_mpullPt_germ p h₁ hb₁ hϕ₁ h₃ hb₃ hϕ₃ hG v).trans
    (congrArg Subtype.val (p.transferT_self_apply v))

/-- The identification of `Y_b` between the two carried chart points is the identity. -/
theorem transferK_mpullPt_germ (p : ChartPoint B' x) (h₁ : p.c.φ.source ⊆ U₁') (hb₁ : b ∈ U₁)
    (hϕ₁ : L₁.ϕ b = x) (h₃ : p.c.φ.source ⊆ U₃') (hb₃ : b ∈ U₃) (hϕ₃ : L₃.ϕ b = x)
    (hG : GermEq L₁ L₃ b) (k : ↥p.K) :
    (Subtype.val ((L₃.mpullPt p h₃ hb₃ hϕ₃).transferK (L₁.mpullPt p h₁ hb₁ hϕ₁) k) :
      p.c.F 0) = k :=
  (fiberMap_mpullPt_germ p h₁ hb₁ hϕ₁ h₃ hb₃ hϕ₃ hG k).trans
    (congrArg Subtype.val (p.transferK_self_apply k))

/-- **`mmorT` depends only on the germ.** -/
theorem mmorT_germ (q' : ChartPoint B' x) (q : ChartPoint B b) (p : ChartPoint B' x)
    (h₁ : p.c.φ.source ⊆ U₁') (hb₁ : b ∈ U₁) (hϕ₁ : L₁.ϕ b = x) (h₃ : p.c.φ.source ⊆ U₃')
    (hb₃ : b ∈ U₃) (hϕ₃ : L₃.ϕ b = x) (hG : GermEq L₁ L₃ b) (v : ↥q'.T) :
    L₁.mmorT q' q p h₁ hb₁ hϕ₁ v = L₃.mmorT q' q p h₃ hb₃ hϕ₃ v := by
  rw [mmorT_apply, mmorT_apply]
  set w : ↥(L₃.mpullPt p h₃ hb₃ hϕ₃).T := q'.transferT p v
  have h1 := ((L₃.mpullPt p h₃ hb₃ hϕ₃).transferT_trans_apply (L₁.mpullPt p h₁ hb₁ hϕ₁) q w).symm
  have h2 : (L₃.mpullPt p h₃ hb₃ hϕ₃).transferT (L₁.mpullPt p h₁ hb₁ hϕ₁) w =
      (w : ↥(L₁.mpullPt p h₁ hb₁ hϕ₁).T) :=
    Subtype.ext (transferT_mpullPt_germ p h₁ hb₁ hϕ₁ h₃ hb₃ hϕ₃ hG w)
  exact (h1.trans (congrArg ((L₁.mpullPt p h₁ hb₁ hϕ₁).transferT q) h2)).symm

/-- **`mmorK` depends only on the germ.** -/
theorem mmorK_germ (q' : ChartPoint B' x) (q : ChartPoint B b) (p : ChartPoint B' x)
    (h₁ : p.c.φ.source ⊆ U₁') (hb₁ : b ∈ U₁) (hϕ₁ : L₁.ϕ b = x) (h₃ : p.c.φ.source ⊆ U₃')
    (hb₃ : b ∈ U₃) (hϕ₃ : L₃.ϕ b = x) (hG : GermEq L₁ L₃ b) (k : ↥q'.K) :
    L₁.mmorK q' q p h₁ hb₁ hϕ₁ k = L₃.mmorK q' q p h₃ hb₃ hϕ₃ k := by
  rw [mmorK_apply, mmorK_apply]
  set w : ↥(L₃.mpullPt p h₃ hb₃ hϕ₃).K := q'.transferK p k
  have h1 := ((L₃.mpullPt p h₃ hb₃ hϕ₃).transferK_trans_apply (L₁.mpullPt p h₁ hb₁ hϕ₁) q w).symm
  have h2 : (L₃.mpullPt p h₃ hb₃ hϕ₃).transferK (L₁.mpullPt p h₁ hb₁ hϕ₁) w =
      (w : ↥(L₁.mpullPt p h₁ hb₁ hϕ₁).K) :=
    Subtype.ext (transferK_mpullPt_germ p h₁ hb₁ hϕ₁ h₃ hb₃ hϕ₃ hG w)
  exact (h1.trans (congrArg ((L₁.mpullPt p h₁ hb₁ hϕ₁).transferK q) h2)).symm

/-- **The orientation map depends only on the germ**: two local isomorphisms with the same germ
at `b` give the same `morVia` at `b`. -/
theorem morVia_germ (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (q' : ChartPoint B' x) (q : ChartPoint B b) (p : ChartPoint B' x)
    (h₁ : p.c.φ.source ⊆ U₁') (hb₁ : b ∈ U₁) (hϕ₁ : L₁.ϕ b = x) (h₃ : p.c.φ.source ⊆ U₃')
    (hb₃ : b ∈ U₃) (hϕ₃ : L₃.ϕ b = x) (hG : GermEq L₁ L₃ b)
    (hl₁ : (L₁.mpullPt p h₁ hb₁ hϕ₁).linSet f = p.linSet f')
    (hl₃ : (L₃.mpullPt p h₃ hb₃ hϕ₃).linSet f = p.linSet f') (hxs : x ∈ PX'.smoothSet)
    (hbs : b ∈ PX.smoothSet) :
    L₁.morVia hf hf' q' q p h₁ hb₁ hϕ₁ hl₁ hxs hbs =
      L₃.morVia hf hf' q' q p h₃ hb₃ hϕ₃ hl₃ hxs hbs :=
  Equiv.ext fun o => by
    rw [morVia_apply, morVia_apply]
    exact LineOrientation.conj_congr (mmorT_germ q' q p h₁ hb₁ hϕ₁ h₃ hb₃ hϕ₃ hG)
      (mmorK_germ q' q p h₁ hb₁ hϕ₁ h₃ hb₃ hϕ₃ hG) _ _ o

end StrongBundle.LocalIso

end GermLocal

section Mor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

/-- **Two sheets through a morphism `σ` have the same local inverse of `t` near `t(σ)`** (`t` is
injective on a sheet). -/
theorem EpGroupoid.Sheet.tgtInv_eq_near_or (S S' : X.Sheet) {σ : Mor} (hσ : σ ∈ S.carrier)
    (hσ' : σ ∈ S'.carrier) :
    ∃ N : Set Obj, IsOpen N ∧ X.tgt σ ∈ N ∧ N ⊆ S.tgtSet ∧ N ⊆ S'.tgtSet ∧
      ∀ y ∈ N, S'.tgtInv y = S.tgtInv y := by
  have ht := S.isScDiffeoOn_tgt
  have ht' := S'.isScDiffeoOn_tgt
  refine ⟨S.tgtSet ∩ S.tgtInv ⁻¹' S'.carrier ∩ S'.tgtSet,
    (ht.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage ht.isScSmoothOn_inv.isOpen
      ht'.isScSmoothOn.isOpen).inter ht'.isScSmoothOn_inv.isOpen,
    ⟨⟨ht.mapsTo hσ, ?_⟩, ht'.mapsTo hσ'⟩, fun y hy => hy.1.1, fun y hy => hy.2, fun y hy => ?_⟩
  · rw [mem_preimage, ht.left_inv σ hσ]; exact hσ'
  · calc S'.tgtInv y = S'.tgtInv (X.tgt (S.tgtInv y)) := by rw [ht.right_inv y hy.1.1]
      _ = S.tgtInv y := ht'.left_inv _ hy.1.2

namespace EpStrongBundle

variable [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B) {f : Obj → W}
  (hF : E.IsScFredholmSectionFunctor f) (hsec : B.HasScPlusSectionsThrough)

/-- **The isomorphism of `φ` and that of the morphism of its sheet ending at `y'` have the same
germ at `y'`.** -/
theorem germEq_morIso_sheet (φ : Mor) {y' : Obj} (hy' : y' ∈ (X.sheetAt φ).tgtSet) :
    StrongBundle.LocalIso.GermEq (E.morIso φ) (E.morIso ((X.sheetAt φ).tgtInv y')) y' := by
  set S := X.sheetAt φ
  set σ' := S.tgtInv y'
  have ht := S.isScDiffeoOn_tgt
  have hσ : σ' ∈ S.carrier := ht.mapsTo_inv hy'
  have htσ : X.tgt σ' = y' := ht.right_inv y' hy'
  obtain ⟨N, hNo, hyN, hNS, hNS', hτ⟩ :=
    EpGroupoid.Sheet.tgtInv_eq_near_or S (X.sheetAt σ') hσ (X.mem_sheetAt σ')
  rw [htσ] at hyN
  refine ⟨⟨N, hNo, hyN, hNS, hNS', fun y hy => ?_, fun w hw => ?_⟩⟩
  · rw [morIso_ϕ, morIso_ϕ, hτ y hy]
  · have h1 : P w = X.src (morInvSec X φ (P w)) := (src_morInvSec φ (hNS hw)).symm
    have h3 : P w = X.src (morInvSec X σ' (P w)) := (src_morInvSec σ' (hNS' hw)).symm
    have heq : morInvSec X φ (P w) = morInvSec X σ' (P w) :=
      congrArg X.inv (hτ _ hw).symm
    rw [morIso_Φ, morIso_Φ, E.sectionAct_of_eq _ h1, E.sectionAct_of_eq _ h3]
    exact E.μ_congr (Prod.ext heq rfl)

/-- **The carried section is the action of the morphisms of the sheet**: for `y'` in the target
of the sheet of `φ`, the section carried by the isomorphism of `φ` has at `y'` the value
`σ'_* o_{s(σ')}` for the morphism `σ' = (t|sheet)⁻¹(y')` of the sheet. -/
theorem pullOrx_morIso_eq_orMor (φ : Mor) {y' : Obj} (hy' : y' ∈ (X.sheetAt φ).tgtSet)
    (hs : (E.morIso φ).ϕ y' ∈ X.PObj.smoothSet) (hs' : y' ∈ X.PObj.smoothSet)
    (o : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy) :
    (E.morIso φ).pullOrx hF.2 hF.2 (E.eqOn_morIso_of_functor hF φ) hsec hsec o y' hs' =
      E.orMor hF hsec ((X.sheetAt φ).tgtInv y') rfl
        ((X.sheetAt φ).isScDiffeoOn_tgt.right_inv y' hy') hs hs' (o _ hs) := by
  set σ' := (X.sheetAt φ).tgtInv y'
  have htσ : X.tgt σ' = y' := (X.sheetAt φ).isScDiffeoOn_tgt.right_inv y' hy'
  have hx₁ : (E.morIso φ).ϕ y' ∈ (X.sheetAt φ).srcSet := (E.morIso φ).base.mapsTo hy'
  have hx₃ : (E.morIso φ).ϕ y' ∈ (X.sheetAt σ').srcSet := mem_srcSet rfl
  have hV : IsOpen ((X.sheetAt φ).srcSet ∩ (X.sheetAt σ').srcSet) :=
    (isOpen_srcSet φ).inter (isOpen_srcSet σ')
  set p := restrPt B _ hV ⟨hx₁, hx₃⟩ hs
  have hp₁ : p.c.φ.source ⊆ (X.sheetAt φ).srcSet := fun _ hw => (restrPt_sub _ _ _ _ hw).1
  have hp₃ : p.c.φ.source ⊆ (X.sheetAt σ').srcSet := fun _ hw => (restrPt_sub _ _ _ _ hw).2
  rw [StrongBundle.LocalIso.pullOrx, dif_pos hy',
    StrongBundle.LocalIso.orxVia_eq_morVia _ _ _ _ _ _ _ _ p hp₁,
    StrongBundle.LocalIso.morVia_germ _ _ _ _ p hp₁ hy' rfl hp₃ (mem_tgtSet htσ)
      (E.morIso_ϕ_eq rfl htσ) (E.germEq_morIso_sheet φ hy') _
      (StrongBundle.LocalIso.linSet_mpullPt hF.2 hF.2 (E.eqOn_morIso_of_functor hF σ') hsec hsec
        hs' hs),
    StrongBundle.LocalIso.morVia_eq _ _ _ _ _ hp₃ (restrPt_sub _ _ _ _) (mem_tgtSet htσ)
      (E.morIso_ϕ_eq rfl htσ) _
      (StrongBundle.LocalIso.linSet_mpullPt hF.2 hF.2 (E.eqOn_morIso_of_functor hF σ') hsec hsec
        hs' hs)]
  rfl

end EpStrongBundle

end Mor

section EquivGerm

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

/-- The local isomorphisms of an equivalence at `a` and at `b ∈ U(a)` have the same germ at `b`
(both are `ϕ` and `Φ`). -/
theorem germEq_locIso {a b : Obj} (hb : b ∈ h.locSet a) :
    StrongBundle.LocalIso.GermEq (h.locIso a) (h.locIso b) b :=
  ⟨⟨h.locSet a ∩ h.locSet b, (h.isOpen_locSet a).inter (h.isOpen_locSet b),
    ⟨hb, h.mem_locSet b⟩, inter_subset_left, inter_subset_right, fun _ _ => rfl,
    fun _ _ => rfl⟩⟩

variable {f : Obj → W} {f' : Obj' → W'} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hpb : f = h.pullback f')
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)

/-- **`orEqv b` is the orientation map of the local isomorphism at any `a` with `b ∈ U(a)`.** -/
theorem orEqv_eq_orxVia {a b : Obj} (hb : b ∈ h.locSet a) (hs : b ∈ X.PObj.smoothSet) :
    h.orEqv hF hF' hpb hsec hsec' b hs =
      (h.locIso a).orxVia hF.2 hF'.2 (h.eqOn_loc hpb hF'.2.isScSmooth.1 a) hsec hsec' hb hs := by
  have hx₁ : ϕ.obj b ∈ h.locSet' a := (h.locIso a).base.mapsTo hb
  have hx₃ : ϕ.obj b ∈ h.locSet' b := h.obj_mem_locSet' b
  set p := restrPt B' _ ((h.isOpen_locSet' a).inter (h.isOpen_locSet' b)) ⟨hx₁, hx₃⟩
    (h.smooth_obj hs)
  have hp₁ : p.c.φ.source ⊆ h.locSet' a := fun _ hw => (restrPt_sub _ _ _ _ hw).1
  have hp₃ : p.c.φ.source ⊆ h.locSet' b := fun _ hw => (restrPt_sub _ _ _ _ hw).2
  have hl₃ := h.linSet_loc hF hF' hpb hsec hsec' hs p hp₃
  have hl₁ : ((h.locIso a).mpullPt p hp₁ hb rfl).linSet f = p.linSet f' :=
    StrongBundle.LocalIso.linSet_mpullPt hF.2 hF'.2 (h.eqOn_loc hpb hF'.2.isScSmooth.1 a) hsec
      hsec' hs (h.smooth_obj hs)
  have e1 : h.orEqv hF hF' hpb hsec hsec' b hs =
      (h.locIso b).morVia hF.2 hF'.2 (orPt B' (ϕ.obj b) (h.smooth_obj hs)) (orPt B b hs) p hp₃
        (h.mem_locSet b) rfl hl₃ (h.smooth_obj hs) hs :=
    ((h.locIso b).morVia_eq hF.2 hF'.2 (orPt B' (ϕ.obj b) (h.smooth_obj hs)) (orPt B b hs) hp₃
      (restrPt_sub _ _ _ _) (h.mem_locSet b) rfl hl₃
      (h.linSet_loc hF hF' hpb hsec hsec' hs _ _) (h.smooth_obj hs) hs).symm
  have e2 := StrongBundle.LocalIso.morVia_germ hF.2 hF'.2
    (orPt B' (ϕ.obj b) (h.smooth_obj hs)) (orPt B b hs) p hp₁ hb rfl hp₃ (h.mem_locSet b) rfl
      (h.germEq_locIso hb) hl₁ hl₃ (h.smooth_obj hs) hs
  have e3 := (h.locIso a).orxVia_eq_morVia hF.2 hF'.2 (h.eqOn_loc hpb hF'.2.isScSmooth.1 a)
    hsec hsec' hb hs p hp₁
  exact e1.trans (e2.symm.trans e3.symm)

end EpStrongBundle.IsStrongBundleEquivalence

end EquivGerm

end Polyfold
