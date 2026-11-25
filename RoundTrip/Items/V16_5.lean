import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_5

set_option maxSynthPendingDepth 3

/-! Round trip for V16_5 (2021 Proposition 16.1.4, p. 708; 2017: Proposition 16.2: sc-smooth bump
functions and sc-smooth partitions of unity are invariant under equivalence of polyfold
structures).

The item lists the definition `EpGroupoid.HasOrbitScPartitionsOfUnity` (vocabulary) and nine
theorems; `A` is the conjunction of their types, all universes at `0`: the main statement
`PolyfoldStructure.proposition_16_1_4` (both parts), its halves `proposition_16_1_4_one`,
`proposition_16_1_4_two`, and the proof steps on ep-groupoid equivalences `F : A → X`
(`admitsBumpFunctions_iff`, `hasScPartitionsOfUnity_iff`, `isScSmoothMap_comp_π_of_comp_obj`),
on one ep-groupoid (`hasScPartitionsOfUnity_iff_orbit`, `hasBumpAt_tgt`), and on M-polyfolds
(`IsScDiffeoOn.hasBumpAt`).

**The two bump notions differ.**  `A`'s bump half is about the *object M-polyfold* in the
pointwise reading (`MPolyfold.AdmitsBumpFunctions`: for each `x` and open `U ∋ x` an sc-smooth `f`
with `f(x) ≠ 0`, `supp f ⊆ U`).  `B`'s is about the *ep-groupoid* notion of Definition 12.3.1 as
printed (`EpGroupoid.AdmitsBumpFunctions`: saturated `U`, invariant `f`, `f` not identically
zero), which by `EpGroupoid.theorem_12_3_2_1_weak` (a non-item project lemma) is the *weak*
reading on the object M-polyfold (`MPolyfold.AdmitsBumpFunctionsWeak`: `f ≢ 0`).  Whether the weak
reading implies the pointwise one is open in the project (`BumpWeakPointwise.lean`), so neither
bump half follows from the other: each is proved here outright.  The partition halves are the same
statement (Definition 7.5.5, `EpGroupoid.HasScPartitionsOfUnity`) on both sides.

* `A_to_B`: partitions from `A` (`proposition_16_1_4_two`).  Bumps: proved outright, by the
  project's argument redone for the weak reading (`weakBumpAt` below: a weak bump point is carried
  back along an sc-diffeomorphism of open sets; then the local sc-diffeomorphisms `F` and `ψ̂`; then
  `EPLoc.iff_of_isGeneralizedIso`) and `theorem_12_3_2_1_weak`.
* `B_to_A`: `proposition_16_1_4_two` and the partition half of `proposition_16_1_4` from `B`.
  Everything else (the pointwise bump half and the proof-step lemmas on arbitrary ep-groupoid
  equivalences, which `B`, a statement about polyfold structures, does not reach) is re-proved
  outright by copies of the project's proofs (from non-item lemmas). -/

namespace RoundTrip.V16_5
open Polyfold Set Function Topology Filter

/-- The project's statement (all universes `0`). -/
def A : Prop :=
  (type_of% @Polyfold.PolyfoldStructure.proposition_16_1_4.{0}) ∧
  (type_of% @Polyfold.PolyfoldStructure.proposition_16_1_4_two.{0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.hasScPartitionsOfUnity_iff.{0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.isScSmoothMap_comp_π_of_comp_obj.{0, 0}) ∧
  (type_of% @Polyfold.EpGroupoid.hasScPartitionsOfUnity_iff_orbit.{0}) ∧
  (type_of% @Polyfold.PolyfoldStructure.proposition_16_1_4_one.{0}) ∧
  (type_of% @Polyfold.EpFunctor.IsEquivalence.admitsBumpFunctions_iff.{0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.IsScDiffeoOn.hasBumpAt.{0, 0}) ∧
  (type_of% @Polyfold.EpGroupoid.hasBumpAt_tgt.{0})

theorem A_holds : A :=
  ⟨@Polyfold.PolyfoldStructure.proposition_16_1_4.{0},
    @Polyfold.PolyfoldStructure.proposition_16_1_4_two.{0},
    @Polyfold.EpFunctor.IsEquivalence.hasScPartitionsOfUnity_iff.{0},
    @Polyfold.EpFunctor.IsEquivalence.isScSmoothMap_comp_π_of_comp_obj.{0, 0},
    @Polyfold.EpGroupoid.hasScPartitionsOfUnity_iff_orbit.{0},
    @Polyfold.PolyfoldStructure.proposition_16_1_4_one.{0},
    @Polyfold.EpFunctor.IsEquivalence.admitsBumpFunctions_iff.{0, 0},
    @Polyfold.MPolyfold.IsScDiffeoOn.hasBumpAt.{0, 0},
    @Polyfold.EpGroupoid.hasBumpAt_tgt.{0}⟩

universe u v

/-! ### Bump points: the pointwise reading (copies of the project's proofs) and the weak reading -/

section Bump

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- A **weak bump point**: every open `U ∋ x` carries an sc-smooth `f ≢ 0` with `supp f ⊆ U`. -/
def WeakBumpAt (P : MPolyfold X) (x : X) : Prop :=
  ∀ U : Set X, IsOpen U → x ∈ U →
    ∃ f : X → ℝ, P.IsScSmoothMap realPolyfold f ∧ f ≠ 0 ∧ tsupport f ⊆ U

/-- The common construction: from a function `g` on `Y` supported in `φ(N)`, `N` a small
neighbourhood of `x` in `V`, the function `1_V · (g ∘ φ)` on `X`. -/
theorem pullback_bump {φ : X → Y} {ψ : Y → X} {V : Set X} {W : Set Y}
    (hd : P.IsScDiffeoOn Q φ ψ V W) {x : X} (hx : x ∈ V) {U : Set X} (hU : IsOpen U)
    (hxU : x ∈ U) :
    ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ N ⊆ V ∧ IsOpen (φ '' N) ∧
      ∀ g : Y → ℝ, Q.IsScSmoothMap realPolyfold g → tsupport g ⊆ φ '' N →
        P.IsScSmoothMap realPolyfold (V.indicator (g ∘ φ)) ∧
          tsupport (V.indicator (g ∘ φ)) ⊆ U := by
  obtain ⟨t, ht, htc, htsub⟩ :=
    exists_mem_nhds_isClosed_subset ((hU.inter hd.isOpen_source).mem_nhds ⟨hxU, hx⟩)
  set N := interior t with hNdef
  have hxN : x ∈ N := mem_interior_iff_mem_nhds.2 ht
  have hNcl : closure N ⊆ U ∩ V := (closure_minimal interior_subset htc).trans htsub
  have hNV : N ⊆ V := subset_closure.trans (hNcl.trans inter_subset_right)
  have hdN := hd.restrict _root_.isOpen_interior hNV
  have hφN : IsOpen (φ '' N) := by rw [hdN.image_eq]; exact hdN.isOpen_target
  refine ⟨N, isOpen_interior, hxN, hNV, hφN, fun g hg hgsupp => ?_⟩
  set f : X → ℝ := V.indicator (g ∘ φ) with hfdef
  have hsupp : support f ⊆ N := by
    intro y hy
    have hyV : y ∈ V := by
      by_contra hyV; exact hy (indicator_of_notMem hyV _)
    have hgy : g (φ y) ≠ 0 := by
      have := mem_support.1 hy; rwa [hfdef, indicator_of_mem hyV] at this
    obtain ⟨n, hn, hny⟩ := hgsupp (subset_tsupport g (mem_support.2 hgy))
    rwa [hd.injOn (hNV hn) hyV hny] at hn
  have htsupp : tsupport f ⊆ U ∩ V := (closure_mono hsupp).trans hNcl
  refine ⟨MPolyfold.isScSmoothMap_real_of_locally fun y => ?_, htsupp.trans inter_subset_left⟩
  by_cases hy : y ∈ V
  · refine ⟨V, hd.isOpen_source, hy, ?_⟩
    refine (MPolyfold.IsScSmoothOn.comp hg hd.isScSmoothOn (mapsTo_univ _ _)).congr fun z hz => ?_
    simp only [hfdef, indicator_of_mem hz]
  · have hyt : y ∉ tsupport f := fun h => hy (htsupp h).2
    refine ⟨(tsupport f)ᶜ, (isClosed_tsupport f).isOpen_compl, hyt, ?_⟩
    refine ((isScSmoothMap_real_const (PX := P) 0).mono (isClosed_tsupport f).isOpen_compl
      (subset_univ _)).congr fun z hz => ?_
    exact (image_eq_zero_of_notMem_tsupport hz).symm

/-- Copy of `IsScDiffeoOn.hasBumpAt` (pointwise reading). -/
theorem hasBumpAt' {φ : X → Y} {ψ : Y → X} {V : Set X} {W : Set Y}
    (hd : P.IsScDiffeoOn Q φ ψ V W) {x : X} (hx : x ∈ V) (hb : Q.HasBumpAt (φ x)) :
    P.HasBumpAt x := by
  intro U hU hxU
  obtain ⟨N, -, hxN, -, hφN, hN⟩ := pullback_bump hd hx hU hxU
  obtain ⟨g, hg, hgx, hgsupp⟩ := hb (φ '' N) hφN ⟨x, hxN, rfl⟩
  obtain ⟨h1, h2⟩ := hN g hg hgsupp
  refine ⟨_, h1, ?_, h2⟩
  simp only [indicator_of_mem hx, Function.comp_apply]
  exact hgx

/-- **A weak bump point is carried back along an sc-diffeomorphism of open sets.** -/
theorem weakBumpAt {φ : X → Y} {ψ : Y → X} {V : Set X} {W : Set Y}
    (hd : P.IsScDiffeoOn Q φ ψ V W) {x : X} (hx : x ∈ V) (hb : WeakBumpAt Q (φ x)) :
    WeakBumpAt P x := by
  intro U hU hxU
  obtain ⟨N, -, hxN, hNV, hφN, hN⟩ := pullback_bump hd hx hU hxU
  obtain ⟨g, hg, hgne, hgsupp⟩ := hb (φ '' N) hφN ⟨x, hxN, rfl⟩
  obtain ⟨h1, h2⟩ := hN g hg hgsupp
  refine ⟨_, h1, fun h0 => ?_, h2⟩
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hgne
  obtain ⟨n, hn, rfl⟩ := hgsupp (subset_tsupport g (mem_support.2 hw))
  have := congrFun h0 n
  simp only [indicator_of_mem (hNV hn), Function.comp_apply, Pi.zero_apply] at this
  exact hw this

end Bump

section Equivalence

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {A : EpGroupoid Obj Mor} {X : EpGroupoid Obj' Mor'} {F : EpFunctor A X}

/-- Copy of `EpGroupoid.hasBumpAt_tgt`. -/
theorem hasBumpAt_tgt' (X : EpGroupoid Obj' Mor') (ψ : Mor')
    (h : X.PObj.HasBumpAt (X.src ψ)) : X.PObj.HasBumpAt (X.tgt ψ) := by
  obtain ⟨U, Vs, Vt, gs, gt, hψU, hs, ht, hhat, hval⟩ :=
    X.isLocalScDiffeo_src.exists_isScDiffeoOn_hat X.isLocalScDiffeo_tgt ψ
  have hmem : X.tgt ψ ∈ Vt := ht.mapsTo hψU
  refine hasBumpAt' hhat.symm hmem ?_
  have e : (X.src ∘ gt) (X.tgt ψ) = X.src ψ := by
    simp only [Function.comp_apply, ht.left_inv ψ hψU]
  rwa [e]

/-- Weak bump points are invariant under isomorphism. -/
theorem weakBumpAt_tgt (X : EpGroupoid Obj' Mor') (ψ : Mor')
    (h : WeakBumpAt X.PObj (X.src ψ)) : WeakBumpAt X.PObj (X.tgt ψ) := by
  obtain ⟨U, Vs, Vt, gs, gt, hψU, hs, ht, hhat, hval⟩ :=
    X.isLocalScDiffeo_src.exists_isScDiffeoOn_hat X.isLocalScDiffeo_tgt ψ
  have hmem : X.tgt ψ ∈ Vt := ht.mapsTo hψU
  refine weakBumpAt hhat.symm hmem ?_
  have e : (X.src ∘ gt) (X.tgt ψ) = X.src ψ := by
    simp only [Function.comp_apply, ht.left_inv ψ hψU]
  rwa [e]

/-- Copy of `EpFunctor.IsEquivalence.admitsBumpFunctions_iff` (pointwise reading). -/
theorem admitsBumpFunctions_iff' (hF : F.IsEquivalence) :
    A.PObj.AdmitsBumpFunctions ↔ X.PObj.AdmitsBumpFunctions := by
  rw [MPolyfold.admitsBumpFunctions_iff_forall_hasBumpAt,
    MPolyfold.admitsBumpFunctions_iff_forall_hasBumpAt]
  refine ⟨fun h x => ?_, fun h a => ?_⟩
  · obtain ⟨a, ψ, hs, ht⟩ := hF.exists_iso x
    have h1 : X.PObj.HasBumpAt (F.obj a) := by
      obtain ⟨U, V, g, haU, hd⟩ := hF.isLocalScDiffeo_obj a
      refine hasBumpAt' hd.symm (hd.mapsTo haU) ?_
      rw [hd.left_inv a haU]
      exact h a
    rw [← hs] at h1
    have h2 := hasBumpAt_tgt' X ψ h1
    rwa [ht] at h2
  · obtain ⟨U, V, g, haU, hd⟩ := hF.isLocalScDiffeo_obj a
    exact hasBumpAt' hd haU (h _)

/-- **Weak reading**: an equivalence `F : A → X` transfers the weak reading of bump functions on
the object M-polyfolds, in both directions. -/
theorem admitsBumpFunctionsWeak_iff (hF : F.IsEquivalence) :
    A.PObj.AdmitsBumpFunctionsWeak ↔ X.PObj.AdmitsBumpFunctionsWeak := by
  change (∀ a, WeakBumpAt A.PObj a) ↔ ∀ x, WeakBumpAt X.PObj x
  refine ⟨fun h x => ?_, fun h a => ?_⟩
  · obtain ⟨a, ψ, hs, ht⟩ := hF.exists_iso x
    have h1 : WeakBumpAt X.PObj (F.obj a) := by
      obtain ⟨U, V, g, haU, hd⟩ := hF.isLocalScDiffeo_obj a
      refine weakBumpAt hd.symm (hd.mapsTo haU) ?_
      rw [hd.left_inv a haU]
      exact h a
    rw [← hs] at h1
    have h2 := weakBumpAt_tgt X ψ h1
    rwa [ht] at h2
  · obtain ⟨U, V, g, haU, hd⟩ := hF.isLocalScDiffeo_obj a
    exact weakBumpAt hd haU (h _)

/-- Copy of `EpFunctor.IsEquivalence.isScSmoothMap_comp_π_of_comp_obj`. -/
theorem isScSmoothMap_comp_π_of_comp_obj' (hF : F.IsEquivalence) {g : X.OrbitSpace → ℝ}
    (hg : A.PObj.IsScSmoothMap realPolyfold (g ∘ X.π ∘ F.obj)) :
    X.PObj.IsScSmoothMap realPolyfold (g ∘ X.π) := by
  refine MPolyfold.isScSmoothMap_real_of_locally fun y => ?_
  obtain ⟨a, ψ, hs, ht⟩ := hF.exists_iso y
  obtain ⟨U, V, k, haU, hd⟩ := hF.isLocalScDiffeo_obj a
  have hV : X.PObj.IsScSmoothOn realPolyfold (g ∘ X.π) V := by
    refine (MPolyfold.IsScSmoothOn.comp hg hd.isScSmoothOn_inv (mapsTo_univ _ _)).congr
      fun v hv => ?_
    simp only [Function.comp_apply, hd.right_inv v hv]
  obtain ⟨W, Vs, Vt, gs, gt, hψW, hsd, htd, hhat, -⟩ :=
    X.isLocalScDiffeo_src.exists_isScDiffeoOn_hat X.isLocalScDiffeo_tgt ψ
  have hinv := hhat.symm
  set O := Vt ∩ (X.src ∘ gt) ⁻¹' V with hO
  have hOo : IsOpen O :=
    hinv.isScSmoothOn.continuousOn.isOpen_inter_preimage hinv.isOpen_source hd.isOpen_target
  have hyO : y ∈ O := by
    refine ⟨ht ▸ htd.mapsTo hψW, ?_⟩
    rw [← ht, mem_preimage, Function.comp_apply, htd.left_inv ψ hψW, hs]
    exact hd.mapsTo haU
  refine ⟨O, hOo, hyO, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp hV (hinv.isScSmoothOn.mono hOo inter_subset_left)
    fun z hz => hz.2).congr fun z hz => ?_
  simp only [Function.comp_apply]
  rw [X.π_src_eq_π_tgt, htd.right_inv z hz.1]

end Equivalence

/-! ### Partitions of unity (copies of the project's proofs) -/

section Partitions

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- Copy of `EpGroupoid.hasScPartitionsOfUnity_iff_orbit`. -/
theorem hasScPartitionsOfUnity_iff_orbit' :
    X.HasScPartitionsOfUnity ↔ X.HasOrbitScPartitionsOfUnity := by
  constructor
  · intro h ι O hO hcov
    have hcovU : ⋃ i, X.π ⁻¹' O i = univ := by rw [← preimage_iUnion, hcov, preimage_univ]
    obtain ⟨β, hsub, hsm, hfin, hinv⟩ := h ι (fun i => X.π ⁻¹' O i)
      (fun i => (hO i).preimage X.continuous_π)
      (fun i => by
        change X.π ⁻¹' (X.π '' (X.π ⁻¹' O i)) = X.π ⁻¹' O i
        rw [image_preimage_eq _ X.surjective_π]) hcovU
    let σf : ι → C(X.OrbitSpace, ℝ) := fun i => EpGroupoid.orbitDescend (β i) (hinv i)
    have hsupp : ∀ i, X.π ⁻¹' support (σf i) = support (β i) := fun i => rfl
    refine ⟨{ toFun := σf
              locallyFinite' := fun q => ?_
              nonneg' := fun i q => ?_
              sum_eq_one' := fun q _ => ?_
              sum_le_one' := fun q => ?_ }, fun i => ?_, fun i => hsm i⟩
    · obtain ⟨x, rfl⟩ := X.surjective_π q
      obtain ⟨W, hWo, -, hxW, hWfin⟩ := hfin x
      refine ⟨X.π '' W, (X.proposition_7_1_8 W hWo).mem_nhds ⟨x, hxW, rfl⟩,
        hWfin.subset fun i hi => ?_⟩
      obtain ⟨_, hs, ⟨w, hwW, rfl⟩⟩ := hi
      exact ⟨w, hwW, subset_tsupport _ hs⟩
    · obtain ⟨x, rfl⟩ := X.surjective_π q
      exact β.nonneg i x
    · obtain ⟨x, rfl⟩ := X.surjective_π q
      exact β.sum_eq_one (mem_univ x)
    · obtain ⟨x, rfl⟩ := X.surjective_π q
      exact β.sum_le_one x
    · intro q hq
      obtain ⟨x, rfl⟩ := X.surjective_π q
      have hx : x ∈ X.π ⁻¹' closure (support (σf i)) := hq
      rw [EpGroupoid.preimage_closure_π, hsupp] at hx
      exact hsub i hx
  · intro h ι U hUo hUs hcov
    have hcovO : ⋃ i, X.π '' U i = univ := by
      rw [← image_iUnion, hcov, image_univ_of_surjective X.surjective_π]
    obtain ⟨σ, hσ, hsm⟩ := h ι (fun i => X.π '' U i) (fun i => X.proposition_7_1_8 _ (hUo i))
      hcovO
    exact ⟨X.orbitPullback σ, X.orbitPullback_isSubordinate hσ hUs, hsm,
      X.exists_isSaturated_nhds_finite_orbitPullback σ, X.orbitPullback_src σ⟩

end Partitions

/-- Copy of `EpFunctor.IsEquivalence.hasScPartitionsOfUnity_iff`. -/
theorem hasScPartitionsOfUnity_iff' {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj]
    [T2Space Obj] [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor]
    [ParacompactSpace Mor] [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {A : EpGroupoid Obj Mor}
    {X : EpGroupoid Obj' Mor'} {F : EpFunctor A X} (hF : F.IsEquivalence) :
    A.HasScPartitionsOfUnity ↔ X.HasScPartitionsOfUnity := by
  rw [hasScPartitionsOfUnity_iff_orbit', hasScPartitionsOfUnity_iff_orbit']
  set e : A.OrbitSpace ≃ₜ X.OrbitSpace := hF.isHomeomorph_orbitMap.homeomorph _ with he
  have heπ : ∀ a, e (A.π a) = X.π (F.obj a) := fun a => GroupoidFunctor.orbitMap_π _ a
  have hsm : ∀ g : X.OrbitSpace → ℝ, A.PObj.IsScSmoothMap realPolyfold (g ∘ e ∘ A.π) ↔
      X.PObj.IsScSmoothMap realPolyfold (g ∘ X.π) := fun g => by
    have h1 : g ∘ e ∘ A.π = g ∘ X.π ∘ F.obj := funext fun a => by
      simp only [Function.comp_apply, heπ]
    rw [h1]
    exact ⟨isScSmoothMap_comp_π_of_comp_obj' hF, fun h =>
      MPolyfold.IsScSmoothMap.comp (g := g ∘ X.π) h F.isScSmoothMap_obj⟩
  constructor
  · intro h ι O hO hcov
    have hcov' : ⋃ i, e ⁻¹' O i = univ := by rw [← preimage_iUnion, hcov, preimage_univ]
    obtain ⟨σ', hσ', hsm'⟩ := h ι (fun i => e ⁻¹' O i) (fun i => (hO i).preimage e.continuous)
      hcov'
    refine ⟨PartitionOfUnity.comap ⟨⇑e.symm, e.symm.continuous⟩ σ', fun i => ?_, fun i => ?_⟩
    · refine (tsupport_comp_subset_preimage (σ' i) e.symm.continuous).trans fun q hq => ?_
      have := hσ' i hq
      rwa [mem_preimage, Homeomorph.apply_symm_apply] at this
    · refine (hsm _).1 ?_
      have e1 : (⇑(PartitionOfUnity.comap ⟨⇑e.symm, e.symm.continuous⟩ σ' i) ∘ ⇑e ∘ A.π) =
          σ' i ∘ A.π := funext fun a => by
        simp only [Function.comp_apply, PartitionOfUnity.comap_apply,
          ContinuousMap.coe_mk, Homeomorph.symm_apply_apply]
      rw [e1]
      exact hsm' i
  · intro h ι O hO hcov
    have hcov' : ⋃ i, e.symm ⁻¹' O i = univ := by rw [← preimage_iUnion, hcov, preimage_univ]
    obtain ⟨σ, hσ, hsmX⟩ := h ι (fun i => e.symm ⁻¹' O i)
      (fun i => (hO i).preimage e.symm.continuous) hcov'
    refine ⟨PartitionOfUnity.comap ⟨⇑e, e.continuous⟩ σ, fun i => ?_, fun i => ?_⟩
    · refine (tsupport_comp_subset_preimage (σ i) e.continuous).trans fun q hq => ?_
      have := hσ i hq
      rwa [mem_preimage, Homeomorph.symm_apply_apply] at this
    · exact (hsm (σ i)).2 (hsmX i)

/-! ### Polyfold structures -/

section Structures

variable {Z : Type} [TopologicalSpace Z]

/-- Pointwise bump half, re-proved (copy of `proposition_16_1_4_one`). -/
theorem bump_pointwise {p q : PolyfoldStructure Z} (h : p.Equiv q) :
    p.X.X.PObj.AdmitsBumpFunctions ↔ q.X.X.PObj.AdmitsBumpFunctions := by
  obtain ⟨f, hf, -⟩ := h
  exact EPLocalization.EPLoc.iff_of_isGeneralizedIso (fun B => B.X.PObj.AdmitsBumpFunctions)
    (fun _ hF => admitsBumpFunctions_iff' hF) hf

/-- The bump half of `B` (Definition 12.3.1 as printed), proved outright through the weak reading. -/
theorem bump_ep {p q : PolyfoldStructure Z} (h : p.Equiv q) :
    p.X.X.AdmitsBumpFunctions ↔ q.X.X.AdmitsBumpFunctions := by
  rw [EpGroupoid.theorem_12_3_2_1_weak, EpGroupoid.theorem_12_3_2_1_weak]
  obtain ⟨f, hf, -⟩ := h
  exact EPLocalization.EPLoc.iff_of_isGeneralizedIso (fun B => B.X.PObj.AdmitsBumpFunctionsWeak)
    (fun _ hF => admitsBumpFunctionsWeak_iff hF) hf

end Structures

theorem A_to_B : A → B := fun hA _ _ _ _ h => ⟨bump_ep h, hA.2.1 h⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨@fun Z _ p q h => ⟨bump_pointwise h, (hB Z p q h).2⟩, @fun Z _ p q h => (hB Z p q h).2,
    @hasScPartitionsOfUnity_iff'.{0}, @isScSmoothMap_comp_π_of_comp_obj'.{0, 0},
    @hasScPartitionsOfUnity_iff_orbit'.{0}, @fun _ _ _ _ h => bump_pointwise h,
    @admitsBumpFunctions_iff'.{0, 0}, @hasBumpAt'.{0, 0}, @hasBumpAt_tgt'.{0}⟩

/-! ### The main conjunct alone -/

/-- The main conjunct: `proposition_16_1_4`. -/
def Amain : Prop := type_of% @Polyfold.PolyfoldStructure.proposition_16_1_4.{0}

theorem Amain_to_B : Amain → B := fun hA _ _ _ _ h => ⟨bump_ep h, (hA h).2⟩

theorem B_to_Amain : B → Amain := @fun hB Z _ p q h => ⟨bump_pointwise h, (hB Z p q h).2⟩

#rt_check RoundTrip.V16_5.A_to_B [Polyfold.PolyfoldStructure.proposition_16_1_4,
  Polyfold.PolyfoldStructure.proposition_16_1_4_two,
  Polyfold.EpFunctor.IsEquivalence.hasScPartitionsOfUnity_iff,
  Polyfold.EpFunctor.IsEquivalence.isScSmoothMap_comp_π_of_comp_obj,
  Polyfold.EpGroupoid.hasScPartitionsOfUnity_iff_orbit,
  Polyfold.PolyfoldStructure.proposition_16_1_4_one,
  Polyfold.EpFunctor.IsEquivalence.admitsBumpFunctions_iff,
  Polyfold.MPolyfold.IsScDiffeoOn.hasBumpAt, Polyfold.EpGroupoid.hasBumpAt_tgt]
#rt_check RoundTrip.V16_5.B_to_A [Polyfold.PolyfoldStructure.proposition_16_1_4,
  Polyfold.PolyfoldStructure.proposition_16_1_4_two,
  Polyfold.EpFunctor.IsEquivalence.hasScPartitionsOfUnity_iff,
  Polyfold.EpFunctor.IsEquivalence.isScSmoothMap_comp_π_of_comp_obj,
  Polyfold.EpGroupoid.hasScPartitionsOfUnity_iff_orbit,
  Polyfold.PolyfoldStructure.proposition_16_1_4_one,
  Polyfold.EpFunctor.IsEquivalence.admitsBumpFunctions_iff,
  Polyfold.MPolyfold.IsScDiffeoOn.hasBumpAt, Polyfold.EpGroupoid.hasBumpAt_tgt]
#rt_check RoundTrip.V16_5.Amain_to_B [Polyfold.PolyfoldStructure.proposition_16_1_4,
  Polyfold.PolyfoldStructure.proposition_16_1_4_two,
  Polyfold.EpFunctor.IsEquivalence.hasScPartitionsOfUnity_iff,
  Polyfold.EpFunctor.IsEquivalence.isScSmoothMap_comp_π_of_comp_obj,
  Polyfold.EpGroupoid.hasScPartitionsOfUnity_iff_orbit,
  Polyfold.PolyfoldStructure.proposition_16_1_4_one,
  Polyfold.EpFunctor.IsEquivalence.admitsBumpFunctions_iff,
  Polyfold.MPolyfold.IsScDiffeoOn.hasBumpAt, Polyfold.EpGroupoid.hasBumpAt_tgt]
#rt_check RoundTrip.V16_5.B_to_Amain [Polyfold.PolyfoldStructure.proposition_16_1_4,
  Polyfold.PolyfoldStructure.proposition_16_1_4_two,
  Polyfold.EpFunctor.IsEquivalence.hasScPartitionsOfUnity_iff,
  Polyfold.EpFunctor.IsEquivalence.isScSmoothMap_comp_π_of_comp_obj,
  Polyfold.EpGroupoid.hasScPartitionsOfUnity_iff_orbit,
  Polyfold.PolyfoldStructure.proposition_16_1_4_one,
  Polyfold.EpFunctor.IsEquivalence.admitsBumpFunctions_iff,
  Polyfold.MPolyfold.IsScDiffeoOn.hasBumpAt, Polyfold.EpGroupoid.hasBumpAt_tgt]
#rt_overlap RoundTrip.V16_5.B_to_A [Polyfold.PolyfoldStructure.proposition_16_1_4,
  Polyfold.PolyfoldStructure.proposition_16_1_4_two,
  Polyfold.EpFunctor.IsEquivalence.hasScPartitionsOfUnity_iff,
  Polyfold.EpFunctor.IsEquivalence.isScSmoothMap_comp_π_of_comp_obj,
  Polyfold.EpGroupoid.hasScPartitionsOfUnity_iff_orbit,
  Polyfold.PolyfoldStructure.proposition_16_1_4_one,
  Polyfold.EpFunctor.IsEquivalence.admitsBumpFunctions_iff,
  Polyfold.MPolyfold.IsScDiffeoOn.hasBumpAt, Polyfold.EpGroupoid.hasBumpAt_tgt]

end RoundTrip.V16_5
