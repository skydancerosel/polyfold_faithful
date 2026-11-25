import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V13_51

set_option maxSynthPendingDepth 3

/-! Round trip for V13_51 (2021 Theorem 13.4.1, pp. 621–622; 2017: Theorem 13.3: the pull-back
along a strong bundle equivalence is structurable, with a canonical structure).

`A` is the conjunction of the types of the 21 listed theorems at universe `0` (the definitions
of the list are vocabulary).  The main conjuncts are `theorem_13_4_1` (`Φ^*Λ'` structurable) and
`theorem_13_4_1_structured` (a map of structured sc⁺-multisections with `forget` compatible,
`[T'] ↦ [pullTuple T' P]` for every adapted good system `P`, `I_x = I'_{F(x)}`,
`τ_{x,y}(φ) = τ'_{F(x),F(y)}(F(φ))`); the others are the steps of the proof, stated for general
pull-back data `PullMap` (equivalences and proper coverings).

* `A_to_B`: (a) is `theorem_13_4_1` (`pullMult F Λ' = Λ' ∘ F.Φ.obj` by definition); (b) is the
  `Λ` conjunct of `theorem_13_4_1_structured`; (c) is `pullTuple_equiv` at
  `PullMap.ofEquivalence hF`.
* `B_to_A`: `theorem_13_4_1` from (a).  `theorem_13_4_1_structured` from (b), (c): the map is
  `Quotient.lift` of `T' ↦ [pullTuple T' P]` (well defined by (c)), with `forget` from (b); the
  existence of an adapted good system `P` does not follow from `B` and comes from the copied
  `exists_pullData_rt`.  The 19 helper conjuncts do not follow from `B` (they concern general
  `PullMap`s); they are re-proved outright by copying the project's proofs (suffix `_rt`).

**Harness note.**  The statements mention `PullMap.pullTuple`, `pullDecoration`, `pullTau`,
`pullStructured`, whose proof fields are proved with banned theorems (`isScPlusMultisection_pull`,
`isScPlusSectionOn_pullSec`, `pullSec_eq_iff`, `eq_of_obj_eq`, `obj_fibAct`, `mor_biact`,
`biact_compHom`, `ofPerm_compHom`, `pullTuple_equiv`, `exists_pullData` through `somePullData`),
so `#rt_check_soft` is used. -/

/-! ### Copies of the project's proofs (suffix `_rt`) -/

open Set Function Topology Filter CategoryTheory
open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

theorem isOpen_setOf_eq_of_src_rt {α : Type*} [TopologicalSpace α] {O : Set α} (hO : IsOpen O)
    {a b : α → Mor} (ha : ContinuousOn a O) (hb : ContinuousOn b O)
    (hab : ∀ p ∈ O, X.src (a p) = X.src (b p)) : IsOpen {p | p ∈ O ∧ a p = b p} := by
  refine isOpen_iff_mem_nhds.2 fun p ⟨hp, he⟩ => ?_
  obtain ⟨V, hV, hpV, hinj⟩ := X.isLocalScDiffeo_src.isLocallyInjective (a p)
  have h1 : a ⁻¹' V ∈ 𝓝 p := (ha.continuousAt (hO.mem_nhds hp)).preimage_mem_nhds
    (hV.mem_nhds hpV)
  have h2 : b ⁻¹' V ∈ 𝓝 p := (hb.continuousAt (hO.mem_nhds hp)).preimage_mem_nhds
    (hV.mem_nhds (he ▸ hpV))
  filter_upwards [hO.mem_nhds hp, h1, h2] with q hq hq1 hq2
  exact ⟨hq, hinj hq1 hq2 (hab q hq)⟩

end EpGroupoid

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A C : SEP.{u}}

namespace PullMap

variable (M : PullMap C A)

theorem covers_rt (w : C.W) : A.P (M.Φ w) = M.ϕ.obj (C.P w) :=
  M.isMap.isStrongBundleMap.covers w


theorem eq_of_obj_eq_rt {w w₁ : C.W} (hP : C.P w = C.P w₁) (he : M.Φ w = M.Φ w₁) : w = w₁ := by
  have := (M.fiberEquiv (C.P w₁)).injective (a₁ := ⟨w, hP⟩) (a₂ := ⟨w₁, rfl⟩) (Subtype.ext he)
  exact congrArg Subtype.val this


theorem obj_fibAct_rt {ψ : C.Mor} {v : C.W} (h : C.P v = C.X.src ψ) :
    M.Φ (fibAct ψ v) = fibAct (M.ϕ.mor ψ) (M.Φ v) := by
  have h' : A.P (M.Φ v) = A.X.src (M.ϕ.mor ψ) := by
    rw [M.covers_rt, h, M.ϕ.src_mor]
  rw [fibAct_of h, fibAct_of h', M.isMap.map_μ ψ v h]




theorem pullSec_eq_iff_rt {s' : A.Obj → A.W} {z : C.Obj} (h : A.P (s' (M.ϕ.obj z)) = M.ϕ.obj z)
    {w : C.W} (hw : C.P w = z) : M.pullSec s' z = w ↔ s' (M.ϕ.obj z) = M.Φ w := by
  constructor
  · rintro rfl; exact (M.obj_pullSec h).symm
  · intro e
    exact M.eq_of_obj_eq_rt ((M.P_pullSec s' z).trans hw.symm) ((M.obj_pullSec h).trans e)



theorem isScPlusSectionOn_pullSec_rt {s' : A.Obj → A.W} {U' : Set A.Obj}
    (hs' : IsScPlusSectionOn A s' U') {U : Set C.Obj} (hU : IsOpen U)
    (hUU' : MapsTo M.ϕ.obj U U') : IsScPlusSectionOn C (M.pullSec s') U := by
  refine IsScPlusSectionOn.of_locally hU fun y hy => ?_
  obtain ⟨U₀, U₀', hyU₀, hi⟩ := M.isLocalIso y
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
  obtain ⟨G', hG'val, hG'sm⟩ := hs'.2
  have hFs := M.isMap.isStrongBundleMap
  set O : Set C.Obj := U₀ ∩ U with hOdef
  have hO : IsOpen O := hg.isOpen_source.inter hU
  have hmem : ∀ z ∈ O, A.P (A.B.oneVal (G' (M.ϕ.obj z))) ∈ U₀' := fun z hz => by
    rw [hG'val _ (hUU' hz.2), hs'.1 _ (hUU' hz.2)]; exact hg.mapsTo hz.1
  have hval : ∀ z ∈ O, C.B.oneVal (Ψ₁ (G' (M.ϕ.obj z))) = M.pullSec s' z := fun z hz => by
    have hP : C.P (C.B.oneVal (Ψ₁ (G' (M.ϕ.obj z)))) = z := by
      rw [StrongBundle.IsStrongBundleIsoOn.P_inv_one (h := hFs) hg hΨ₁ (hmem z hz),
        hG'val _ (hUU' hz.2), hs'.1 _ (hUU' hz.2), hg.left_inv z hz.1]
    have hΦ : M.Φ (C.B.oneVal (Ψ₁ (G' (M.ϕ.obj z)))) = s' (M.ϕ.obj z) := by
      have e := congrArg A.B.oneVal (hΨ₁.right_inv _ (hmem z hz))
      rw [oneVal_oneRestrict] at e
      exact e.trans (hG'val _ (hUU' hz.2))
    exact ((M.pullSec_eq_iff_rt (hs'.1 _ (hUU' hz.2)) hP).2 hΦ.symm).symm
  refine ⟨O, hO, ⟨hyU₀, hy⟩, inter_subset_right, fun z _ => M.P_pullSec s' z,
    Ψ₁ ∘ G' ∘ M.ϕ.obj, fun z hz => hval z hz, ?_⟩
  exact MPolyfold.IsScSmoothOn.comp hΨ₁.isScSmoothOn_inv
    (MPolyfold.IsScSmoothOn.comp hG'sm (hg.isScSmoothOn.mono hO inter_subset_left)
      fun z hz => hUU' hz.2) fun z hz => hmem z hz




theorem isWFunctor_pull_rt {Λ' : A.W → ℚ≥0} (h : IsWFunctor A Λ') : IsWFunctor C (M.pull Λ') := by
  rintro ⟨⟨γ, w⟩, hq⟩
  change Λ' (M.Φ (C.E.μ ⟨(γ, w), hq⟩)) = Λ' (M.Φ w)
  rw [M.isMap.map_μ γ w hq]
  exact h _


theorem pull_ofEquivalence_rt {F : C ⟶ A} (hF : SEP.equivalences F) (Λ' : A.W → ℚ≥0) :
    (ofEquivalence hF).pull Λ' = pullMult F Λ' := rfl



theorem exists_isLocalRepOn_pull_rt {Λ' : A.W → ℚ≥0} {O' : Set A.Obj} (hO' : IsOpen O') {k : ℕ}
    {s' : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ' O' s' σ) :
    IsLocalRepOn C (M.pull Λ') (M.ϕ.obj ⁻¹' O') (fun i => M.pullSec (s' i)) σ := by
  have hO : IsOpen (M.ϕ.obj ⁻¹' O') := hO'.preimage M.ϕ.continuous_obj'
  refine ⟨h.1, fun i => M.isScPlusSectionOn_pullSec_rt (h.2.1 i) hO fun z hz => hz, h.2.2.1,
    fun w hw => ?_⟩
  have hw' : A.P (M.Φ w) ∈ O' := by rw [M.covers_rt]; exact hw
  rw [pull_apply, h.2.2.2 _ hw', M.covers_rt]
  refine Finset.sum_congr rfl fun i _ => if_congr ?_ rfl rfl
  have e := M.pullSec_eq_iff_rt (s' := s' i) ((h.2.1 i).1 _ hw) (w := w) rfl
  exact ⟨fun h1 => (e.2 h1.symm).symm, fun h1 => (e.1 h1.symm).symm⟩


theorem isScPlusMultisection_pull_rt {Λ' : A.W → ℚ≥0} (h : IsScPlusMultisection A Λ') :
    IsScPlusMultisection C (M.pull Λ') := by
  refine ⟨M.isWFunctor_pull_rt h.1, fun x => ?_⟩
  obtain ⟨R, k, s', σ, hr⟩ := h.2 (M.ϕ.obj x)
  exact hasLocalSectionStructure_of_isLocalRepOn (R.isOpen_U.preimage M.ϕ.continuous_obj')
    R.mem_U (M.exists_isLocalRepOn_pull_rt R.isOpen_U hr)


variable {M}

variable (M)


theorem exists_isPullNbhd_rt {x : C.Obj} (N' : A.X.NatNbhd (M.ϕ.obj x)) {V : Set C.Obj}
    (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ N : C.X.NatNbhd x, M.IsPullNbhd N N' ∧ C.X.IsProperSubset (closure N.U) ∧ N.U ⊆ V := by
  obtain ⟨U₀, U₀', g₀, hxU₀, hd⟩ := M.isLocalScDiffeo_obj x
  set O : Set C.Obj := V ∩ U₀ ∩ M.ϕ.obj ⁻¹' N'.U with hOdef
  have hO : IsOpen O :=
    (hV.inter hd.isOpen_source).inter (N'.isOpen_U.preimage M.ϕ.continuous_obj')
  have hxO : x ∈ O := ⟨⟨hxV, hxU₀⟩, N'.mem_U⟩
  obtain ⟨N₀, hN₀O, hprop⟩ := C.X.exists_natNbhd_isProperSubset x hO hxO
  set E : Set C.Obj := N₀.U ∩ ⋂ g, {y | y ∈ N₀.U ∧
    M.ϕ.mor (N₀.rep.Γ g y) = N'.rep.Γ (M.ϕ.isotropyHom x g) (M.ϕ.obj y)} with hEdef
  have hE : IsOpen E := by
    refine N₀.isOpen_U.inter (isOpen_iInter_of_finite fun g => ?_)
    refine A.X.isOpen_setOf_eq_of_src_rt N₀.isOpen_U
      (M.ϕ.continuous_mor.comp_continuousOn
        ((N₀.rep.isScSmoothOn_Γ g).continuousOn.mono N₀.U_subset))
      ((N'.rep.isScSmoothOn_Γ _).continuousOn.comp M.ϕ.continuous_obj'.continuousOn
        fun y hy => N'.U_subset (hN₀O hy).2) fun y hy => ?_
    rw [M.ϕ.src_mor, N₀.src_Γ g hy, N'.src_Γ _ (hN₀O hy).2]
  have hxE : x ∈ E := ⟨N₀.mem_U, mem_iInter.2 fun g => ⟨N₀.mem_U, by
    rw [N₀.rep.Γ_self, N'.rep.Γ_self]; rfl⟩⟩
  obtain ⟨N, hrep, hsub⟩ := N₀.exists_restrict_subset hE hxE
  have hNO : ∀ y ∈ N.U, y ∈ O := fun y hy => hN₀O (hsub hy).1
  refine ⟨N, ⟨fun a ha b hb e => ?_, fun y hy => (hNO y hy).2, fun g y hy => ?_⟩,
    isProperMap_domRestrict_of_subset_of_isClosed C.X.continuous_src hprop
      (closure_mono fun y hy => (hsub hy).1) isClosed_closure,
    fun y hy => (hNO y hy).1.1⟩
  · rw [← hd.left_inv a (hNO a ha).1.2, e, hd.left_inv b (hNO b hb).1.2]
  · rw [hrep]
    exact (mem_iInter.1 (hsub hy).2.2 g).2



theorem isDiffeoComponent_of_isPull_rt (𝒰' : A.X.GoodSystem) {x x' : C.Obj} {N : C.X.NatNbhd x}
    {N₁ : C.X.NatNbhd x'} (h : M.IsPullNbhd N (𝒰'.nbhd (M.ϕ.obj x)))
    (h₁ : M.IsPullNbhd N₁ (𝒰'.nbhd (M.ϕ.obj x'))) {φ : C.Mor}
    (hφ : φ ∈ C.X.morBetween N.U N₁.U) :
    C.X.IsDiffeoComponent (connectedComponentIn (C.X.morBetween N.U N₁.U) φ) := by
  have hmaps := M.mapsTo_connectedComponentIn h.mapsTo h₁.mapsTo hφ
  have hφ' : M.ϕ.mor φ ∈ 𝒰'.mor (M.ϕ.obj x) (M.ϕ.obj x') :=
    M.mem_morBetween h.mapsTo h₁.mapsTo hφ
  have hsub : ∀ {ψ}, ψ ∈ connectedComponentIn (C.X.morBetween N.U N₁.U) φ →
      ψ ∈ C.X.morBetween N.U N₁.U := fun hψ => connectedComponentIn_subset _ _ hψ
  refine (isDiffeoComponent_iff_injOn (isOpen_connectedComponentIn_mor C.X
    (isOpen_morBetween N.isOpen_U N₁.isOpen_U) φ)).2
    ⟨fun ψ₁ hψ₁ ψ₂ hψ₂ e => ?_, fun ψ₁ hψ₁ ψ₂ hψ₂ e => ?_⟩
  · have e' : M.ϕ.mor ψ₁ = M.ϕ.mor ψ₂ := 𝒰'.injOn_src_comp hφ' (hmaps hψ₁) (hmaps hψ₂)
      (by rw [M.ϕ.src_mor, M.ϕ.src_mor, e])
    have et : C.X.tgt ψ₁ = C.X.tgt ψ₂ := h₁.injOn (hsub hψ₁).2 (hsub hψ₂).2
      (by rw [← M.ϕ.tgt_mor, ← M.ϕ.tgt_mor, e'])
    exact M.mor_injective _ _ e et e'
  · have e' : M.ϕ.mor ψ₁ = M.ϕ.mor ψ₂ := 𝒰'.injOn_tgt_comp hφ' (hmaps hψ₁) (hmaps hψ₂)
      (by rw [M.ϕ.tgt_mor, M.ϕ.tgt_mor, e])
    have es : C.X.src ψ₁ = C.X.src ψ₂ := h.injOn (hsub hψ₁).1 (hsub hψ₂).1
      (by rw [← M.ϕ.src_mor, ← M.ϕ.src_mor, e'])
    exact M.mor_injective _ _ es e e'

variable {M} in

theorem IsPullNbhd.mor_biact_rt {x x' : C.Obj} {N : C.X.NatNbhd x} {N₁ : C.X.NatNbhd x'}
    {N' : A.X.NatNbhd (M.ϕ.obj x)} {N₁' : A.X.NatNbhd (M.ϕ.obj x')} (h : M.IsPullNbhd N N')
    (h₁ : M.IsPullNbhd N₁ N₁') {φ : C.Mor} (hφ : φ ∈ C.X.morBetween N.U N₁.U)
    (g' : C.X.Isotropy x') (g : C.X.Isotropy x) :
    M.ϕ.mor (biact N N₁ g' φ g) =
      biact N' N₁' (M.ϕ.isotropyHom x' g') (M.ϕ.mor φ) (M.ϕ.isotropyHom x g) := by
  have hy : N.rep.Φ g⁻¹ (C.X.src φ) ∈ N.U := N.Φ_mem g⁻¹ hφ.1
  have h1 : C.X.src φ = C.X.tgt (N.rep.Γ g (N.rep.Φ g⁻¹ (C.X.src φ))) := by
    rw [N.tgt_Γ g hy, N.Φ_Φ_inv g hφ.1]
  have h2 : C.X.src (N₁.rep.Γ g' (C.X.tgt φ)) =
      C.X.tgt (C.X.comp φ (N.rep.Γ g (N.rep.Φ g⁻¹ (C.X.src φ)))) := by
    rw [N₁.src_Γ g' hφ.2, C.X.tgt_comp _ _ h1]
  unfold biact
  rw [M.ϕ.mor_comp _ _ h2, M.ϕ.mor_comp _ _ h1, h₁.Γ_eq g' _ hφ.2, h.Γ_eq g _ hy,
    h.Φ_eq g⁻¹ hφ.1, map_inv, M.ϕ.tgt_mor, M.ϕ.src_mor]



theorem exists_pullData_rt (𝒰' : A.X.GoodSystem) (V : C.Obj → Set C.Obj) (hV : ∀ x, IsOpen (V x))
    (hxV : ∀ x, x ∈ V x) : ∃ P : M.PullData 𝒰', ∀ x, P.𝒰.U x ⊆ V x := by
  choose N hN hprop hsub using fun x => M.exists_isPullNbhd_rt (𝒰'.nbhd (M.ϕ.obj x)) (hV x) (hxV x)
  exact ⟨⟨⟨N, hprop, fun x x' φ hφ => M.isDiffeoComponent_of_isPull_rt 𝒰' (hN x) (hN x') hφ⟩, hN⟩,
    hsub⟩



theorem biact_compHom_rt {α β : Type u} {G G' H H' : Type*} [Group G] [Group G'] [Group H]
    [Group H'] [MulAction H α] [MulAction H' β] (f : G →* H) (f' : G' →* H') (g' : G')
    (τ : IndexCorr α β) (g : G) :
    @IndexCorr.biact α β G G' _ _ (MulAction.compHom α f) (MulAction.compHom β f') g' τ g =
      IndexCorr.biact (f' g') τ (f g) := by
  unfold IndexCorr.biact
  congr 1
  · ext i
    change f g⁻¹ • i = (f g)⁻¹ • i
    rw [map_inv]
  · ext i
    rfl


theorem ofPerm_compHom_rt {α : Type u} [Fintype α] {G H : Type*} [Group G] [Group H]
    [MulAction H α] (f : G →* H) (g : G) :
    @IndexCorr.ofPerm α G _ _ (MulAction.compHom α f) g = IndexCorr.ofPerm (f g) :=
  congrArg IndexCorr.ofEquiv (Equiv.ext fun _ => rfl)



theorem isStructurable_pull_rt {Λ' : A.W → ℚ≥0} (h : IsStructurable A Λ') :
    IsStructurable C (M.pull Λ') := by
  obtain ⟨hΛ', D', ⟨t'⟩⟩ := h
  obtain ⟨P, -⟩ := M.exists_pullData_rt D'.𝒰 (fun _ => univ) (fun _ => isOpen_univ) fun _ => mem_univ _
  exact ⟨M.isScPlusMultisection_pull_rt hΛ', pullDecoration D' P,
    ⟨pullTau t' P⟩⟩

variable {M}


theorem pullTuple_equiv_rt {T₁ T₂ : StructuredTuple A} (h : T₁.Equiv T₂) (P₁ : M.PullData T₁.dec.𝒰)
    (P₂ : M.PullData T₂.dec.𝒰) : (pullTuple T₁ P₁).Equiv (pullTuple T₂ P₂) := by
  obtain ⟨hΛ, 𝒰'', hsub, hI, hτ⟩ := h
  obtain ⟨𝒲, h𝒲⟩ := P₁.𝒰.exists_subset_inter
    (fun x => P₂.𝒰.U x ∩ M.ϕ.obj ⁻¹' 𝒰''.U (M.ϕ.obj x))
    (fun x => (P₂.𝒰.isOpen_U x).inter ((𝒰''.isOpen_U _).preimage M.ϕ.continuous_obj'))
    fun x => ⟨P₂.𝒰.mem_U x, 𝒰''.mem_U _⟩
  refine ⟨congrArg M.pull hΛ, 𝒲, fun x y hy => ⟨(h𝒲 x hy).1, (h𝒲 x hy).2.1⟩,
    fun x => hI (M.ϕ.obj x), fun x x' φ hφ => ?_⟩
  exact hτ _ _ (M.ϕ.mor φ) ⟨by rw [M.ϕ.src_mor]; exact (h𝒲 x hφ.1).2.2,
    by rw [M.ϕ.tgt_mor]; exact (h𝒲 x' hφ.2).2.2⟩

variable (M)


theorem pullStructured_mk_rt (T' : StructuredTuple A) (P : M.PullData T'.dec.𝒰) :
    M.pullStructured (Quotient.mk _ T') = Quotient.mk _ (pullTuple T' P) :=
  Quotient.sound (pullTuple_equiv_rt (StructuredTuple.equivalence.refl T') _ _)


theorem forget_pullStructured_rt (L : StructuredMultisection A) :
    (M.pullStructured L).forget = M.pull L.forget :=
  Quotient.inductionOn L fun _ => rfl


end PullMap

end SBLocalization

end Polyfold

end

namespace RoundTrip.V13_51
open Polyfold Polyfold.SBLocalization CategoryTheory

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.isOpen_setOf_eq_of_src.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.covers.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.eq_of_obj_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.obj_fibAct.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.pullSec_eq_iff.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.isScPlusSectionOn_pullSec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.isWFunctor_pull.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.pull_ofEquivalence.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.isScPlusMultisection_pull.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.exists_isPullNbhd.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.isDiffeoComponent_of_isPull.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.IsPullNbhd.mor_biact.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.exists_pullData.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.biact_compHom.{0, 0, 0, 0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.ofPerm_compHom.{0, 0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.isStructurable_pull.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.pullTuple_equiv.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.pullStructured_mk.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PullMap.forget_pullStructured.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_13_4_1.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_13_4_1_structured.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.isOpen_setOf_eq_of_src.{0, 0},
    @Polyfold.SBLocalization.PullMap.covers.{0},
    @Polyfold.SBLocalization.PullMap.eq_of_obj_eq.{0},
    @Polyfold.SBLocalization.PullMap.obj_fibAct.{0},
    @Polyfold.SBLocalization.PullMap.pullSec_eq_iff.{0},
    @Polyfold.SBLocalization.PullMap.isScPlusSectionOn_pullSec.{0},
    @Polyfold.SBLocalization.PullMap.isWFunctor_pull.{0},
    @Polyfold.SBLocalization.PullMap.pull_ofEquivalence.{0},
    @Polyfold.SBLocalization.PullMap.isScPlusMultisection_pull.{0},
    @Polyfold.SBLocalization.PullMap.exists_isPullNbhd.{0},
    @Polyfold.SBLocalization.PullMap.isDiffeoComponent_of_isPull.{0},
    @Polyfold.SBLocalization.PullMap.IsPullNbhd.mor_biact.{0},
    @Polyfold.SBLocalization.PullMap.exists_pullData.{0},
    @Polyfold.SBLocalization.PullMap.biact_compHom.{0, 0, 0, 0, 0},
    @Polyfold.SBLocalization.PullMap.ofPerm_compHom.{0, 0, 0},
    @Polyfold.SBLocalization.PullMap.isStructurable_pull.{0},
    @Polyfold.SBLocalization.PullMap.pullTuple_equiv.{0},
    @Polyfold.SBLocalization.PullMap.pullStructured_mk.{0},
    @Polyfold.SBLocalization.PullMap.forget_pullStructured.{0},
    @Polyfold.SBLocalization.theorem_13_4_1.{0},
    @Polyfold.SBLocalization.theorem_13_4_1_structured.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hequiv, -, -, h1, hst⟩
  intro C A F hF
  refine ⟨fun Λ' h => h1 hF h, fun T' P => ?_, fun T₁ T₂ h P₁ P₂ => hequiv h P₁ P₂⟩
  obtain ⟨pull, -, hP⟩ := hst hF
  exact (hP T' P).2.1

theorem B_to_A : B → A := by
  intro hB
  refine ⟨@EpGroupoid.isOpen_setOf_eq_of_src_rt.{0, 0}, @PullMap.covers_rt.{0},
    @PullMap.eq_of_obj_eq_rt.{0}, @PullMap.obj_fibAct_rt.{0}, @PullMap.pullSec_eq_iff_rt.{0},
    @PullMap.isScPlusSectionOn_pullSec_rt.{0}, @PullMap.isWFunctor_pull_rt.{0},
    @PullMap.pull_ofEquivalence_rt.{0}, @PullMap.isScPlusMultisection_pull_rt.{0},
    @PullMap.exists_isPullNbhd_rt.{0}, @PullMap.isDiffeoComponent_of_isPull_rt.{0},
    @PullMap.IsPullNbhd.mor_biact_rt.{0}, @PullMap.exists_pullData_rt.{0},
    @PullMap.biact_compHom_rt.{0, 0, 0, 0, 0}, @PullMap.ofPerm_compHom_rt.{0, 0, 0},
    @PullMap.isStructurable_pull_rt.{0}, @PullMap.pullTuple_equiv_rt.{0},
    @PullMap.pullStructured_mk_rt.{0}, @PullMap.forget_pullStructured_rt.{0}, ?_, ?_⟩
  · intro A C F hF Λ' h
    exact (hB C A F hF).1 Λ' h
  · intro A C F hF
    obtain ⟨-, hΛ, hwd⟩ := hB C A F hF
    -- an adapted good system for every good system (copied existence)
    have hP : ∀ 𝒰' : A.X.GoodSystem, Nonempty ((PullMap.ofEquivalence hF).PullData 𝒰') := by
      intro 𝒰'
      obtain ⟨P, -⟩ := (PullMap.ofEquivalence hF).exists_pullData_rt 𝒰' (fun _ => Set.univ)
        (fun _ => isOpen_univ) (fun _ => Set.mem_univ _)
      exact ⟨P⟩
    let pull : StructuredMultisection A → StructuredMultisection C :=
      Quotient.lift (fun T' : StructuredTuple A =>
          (Quotient.mk _ (PullMap.pullTuple T' (hP T'.dec.𝒰).some) : StructuredMultisection C))
        fun T₁ T₂ h => Quotient.sound (hwd T₁ T₂ h _ _)
    have hforget : ∀ L, (pull L).forget = pullMult F L.forget := fun L =>
      Quotient.inductionOn L fun T' => hΛ T' (hP T'.dec.𝒰).some
    have hmk : ∀ (T' : StructuredTuple A) (P : (PullMap.ofEquivalence hF).PullData T'.dec.𝒰),
        pull (Quotient.mk _ T') = Quotient.mk _ (PullMap.pullTuple T' P) := fun T' P =>
      Quotient.sound (s := StructuredTuple.setoid C)
        (hwd T' T' (StructuredTuple.equivalence.refl T') _ P)
    exact ⟨pull, hforget, fun T' P => ⟨hmk T' P, hΛ T' P, fun _ => rfl, fun _ _ _ => rfl⟩⟩

#rt_check_soft RoundTrip.V13_51.A_to_B [Polyfold.EpGroupoid.isOpen_setOf_eq_of_src, Polyfold.SBLocalization.PullMap.covers, Polyfold.SBLocalization.PullMap.eq_of_obj_eq, Polyfold.SBLocalization.PullMap.obj_fibAct, Polyfold.SBLocalization.PullMap.pullSec_eq_iff, Polyfold.SBLocalization.PullMap.isScPlusSectionOn_pullSec, Polyfold.SBLocalization.PullMap.isWFunctor_pull, Polyfold.SBLocalization.PullMap.pull_ofEquivalence, Polyfold.SBLocalization.PullMap.isScPlusMultisection_pull, Polyfold.SBLocalization.PullMap.exists_isPullNbhd, Polyfold.SBLocalization.PullMap.isDiffeoComponent_of_isPull, Polyfold.SBLocalization.PullMap.IsPullNbhd.mor_biact, Polyfold.SBLocalization.PullMap.exists_pullData, Polyfold.SBLocalization.PullMap.biact_compHom, Polyfold.SBLocalization.PullMap.ofPerm_compHom, Polyfold.SBLocalization.PullMap.isStructurable_pull, Polyfold.SBLocalization.PullMap.pullTuple_equiv, Polyfold.SBLocalization.PullMap.pullStructured_mk, Polyfold.SBLocalization.PullMap.forget_pullStructured, Polyfold.SBLocalization.theorem_13_4_1, Polyfold.SBLocalization.theorem_13_4_1_structured]
#rt_check_soft RoundTrip.V13_51.B_to_A [Polyfold.EpGroupoid.isOpen_setOf_eq_of_src, Polyfold.SBLocalization.PullMap.covers, Polyfold.SBLocalization.PullMap.eq_of_obj_eq, Polyfold.SBLocalization.PullMap.obj_fibAct, Polyfold.SBLocalization.PullMap.pullSec_eq_iff, Polyfold.SBLocalization.PullMap.isScPlusSectionOn_pullSec, Polyfold.SBLocalization.PullMap.isWFunctor_pull, Polyfold.SBLocalization.PullMap.pull_ofEquivalence, Polyfold.SBLocalization.PullMap.isScPlusMultisection_pull, Polyfold.SBLocalization.PullMap.exists_isPullNbhd, Polyfold.SBLocalization.PullMap.isDiffeoComponent_of_isPull, Polyfold.SBLocalization.PullMap.IsPullNbhd.mor_biact, Polyfold.SBLocalization.PullMap.exists_pullData, Polyfold.SBLocalization.PullMap.biact_compHom, Polyfold.SBLocalization.PullMap.ofPerm_compHom, Polyfold.SBLocalization.PullMap.isStructurable_pull, Polyfold.SBLocalization.PullMap.pullTuple_equiv, Polyfold.SBLocalization.PullMap.pullStructured_mk, Polyfold.SBLocalization.PullMap.forget_pullStructured, Polyfold.SBLocalization.theorem_13_4_1, Polyfold.SBLocalization.theorem_13_4_1_structured]
#rt_overlap RoundTrip.V13_51.B_to_A [Polyfold.EpGroupoid.isOpen_setOf_eq_of_src, Polyfold.SBLocalization.PullMap.covers, Polyfold.SBLocalization.PullMap.eq_of_obj_eq, Polyfold.SBLocalization.PullMap.obj_fibAct, Polyfold.SBLocalization.PullMap.pullSec_eq_iff, Polyfold.SBLocalization.PullMap.isScPlusSectionOn_pullSec, Polyfold.SBLocalization.PullMap.isWFunctor_pull, Polyfold.SBLocalization.PullMap.pull_ofEquivalence, Polyfold.SBLocalization.PullMap.isScPlusMultisection_pull, Polyfold.SBLocalization.PullMap.exists_isPullNbhd, Polyfold.SBLocalization.PullMap.isDiffeoComponent_of_isPull, Polyfold.SBLocalization.PullMap.IsPullNbhd.mor_biact, Polyfold.SBLocalization.PullMap.exists_pullData, Polyfold.SBLocalization.PullMap.biact_compHom, Polyfold.SBLocalization.PullMap.ofPerm_compHom, Polyfold.SBLocalization.PullMap.isStructurable_pull, Polyfold.SBLocalization.PullMap.pullTuple_equiv, Polyfold.SBLocalization.PullMap.pullStructured_mk, Polyfold.SBLocalization.PullMap.forget_pullStructured, Polyfold.SBLocalization.theorem_13_4_1, Polyfold.SBLocalization.theorem_13_4_1_structured]

end RoundTrip.V13_51
