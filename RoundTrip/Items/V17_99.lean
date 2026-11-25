import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_99

set_option maxSynthPendingDepth 3

/-! Round trip for V17_99 (2021 Proposition 17.5.5, p. 814: the manifold / orbifold structure on
`|supp(Θ)|`).  Universe `0`.

**Harness.**  The statement of `proposition_17_5_5_one` contains the item theorem
`paracompactSpace_orbitSuppC` as the instance on `|supp Θ|` (needed for `MPolyfold.transport`), so
every term whose type mentions `A` reaches it.  `One'` restates that conjunct with the copy
`paraC'` (preferred by instance search), `A'` is `A` with `One'`; `A = A'` by `rfl` (proof
irrelevance), and the directions are proved for `A'` and transported point-free.

`A ⇒ B` is proved only for polyfold constructions with a covering family
(`A_to_B_of_nonempty`); `B ⇒ A` is proved (`B_to_A`), with the ep-groupoid conjuncts
(`restrictSupp_orbifold`, `isScSmoothOn_orbitSuppMap`, `exists_isSuppStructure`) and the
second half of `proposition_17_5_5_two` re-proved outright from non-item lemmas. -/

namespace RoundTrip.V17_99
open Set Polyfold CategoryTheory
open Polyfold.GCT.PolyfoldConstruction
open Polyfold.EpGroupoid Polyfold.MPolyfold Polyfold.EPLocalization Polyfold.EPLocalization.EPLoc

/-- The project's statement, universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_one.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_two.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.suppHomeomorph_orbitSuppMap.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.paracompactSpace_orbitSuppC.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.exists_isSuppStructure.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.isScSmoothOn_orbitSuppMap.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.restrictSupp_orbifold.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_one.{0},
    @Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_two.{0},
    @Polyfold.GCT.PolyfoldConstruction.suppHomeomorph_orbitSuppMap.{0},
    @Polyfold.GCT.PolyfoldConstruction.paracompactSpace_orbitSuppC.{0},
    @Polyfold.EpGroupoid.exists_isSuppStructure.{0},
    @Polyfold.EPLocalization.EPLoc.isScSmoothOn_orbitSuppMap.{0},
    @Polyfold.EPLocalization.EPLoc.restrictSupp_orbifold.{0}⟩

/-- Copy of the instance `paracompactSpace_orbitSuppC` (an item theorem that occurs inside the
statement of `proposition_17_5_5_one`); preferred by instance search below. -/
instance (priority := high) paraC' {C : GCT.{0}} (Θ : C.Obj → ℚ) :
    ParacompactSpace (C.toGroupoidStr.orbitSupp Θ) :=
  paracompactSpace_of_metrizableSpace _

/-- `proposition_17_5_5_one` restated with the copy `paraC'` of the instance. -/
def One' : Prop :=
  ∀ {C : GCT.{0}} {S : C.PolyfoldConstruction} {Θ : C.Obj → ℚ} (hΘ : S.IsBranchedSubcategory Θ),
    C.IsManifoldTypeBranched Θ →
    (∀ c : S.CoveringFamily, ∃ PZ : MPolyfold ((S.modelEP c.Ψ).X.orbitSupp (S.modelPull c.Ψ Θ)),
      (S.modelEP c.Ψ).X.IsSuppStructure _ PZ) ∧
    ∀ (c c' : S.CoveringFamily)
      (PZ : MPolyfold ((S.modelEP c.Ψ).X.orbitSupp (S.modelPull c.Ψ Θ)))
      (PZ' : MPolyfold ((S.modelEP c'.Ψ).X.orbitSupp (S.modelPull c'.Ψ Θ))),
      (S.modelEP c.Ψ).X.IsSuppStructure _ PZ → (S.modelEP c'.Ψ).X.IsSuppStructure _ PZ' →
      (PZ.transport (S.suppHomeomorph c hΘ.isFunctorial)).IsScDiffeoOn
        (PZ'.transport (S.suppHomeomorph c' hΘ.isFunctorial)) id id univ univ

def A' : Prop :=
  One' ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_two.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.suppHomeomorph_orbitSuppMap.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.paracompactSpace_orbitSuppC.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.exists_isSuppStructure.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.isScSmoothOn_orbitSuppMap.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.restrictSupp_orbifold.{0})

theorem A_eq_A' : A = A' := rfl

/-- The main conjuncts: `proposition_17_5_5_one ∧ proposition_17_5_5_two` (parts (1), (2)). -/
def Main' : Prop :=
  One' ∧ (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_two.{0})

def Main : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_one.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_two.{0})

theorem Main_eq_Main' : Main = Main' := rfl

/-- `Main ⇒ B` when `S` has a covering family.  (`B`'s manifold part asks for an M-polyfold
structure on `|supp Θ|` even when `S` has no covering family; `A` says nothing then.) -/
theorem main'_to_B_of_nonempty (h : Main') {C : GCT.{0}} (S : C.PolyfoldConstruction)
    [hne : Nonempty S.CoveringFamily] (Θ : C.Obj → ℚ) (hΘ : S.IsBranchedSubcategory Θ) :
    ImageSupp S Θ ∧ ManifoldPart S Θ ∧ OrbifoldPart S Θ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun c => image_modelOrbitMap_orbitSupp c.isCoveringFamily hΘ.isFunctorial, ?_, ?_⟩
  · intro hm _ _
    obtain ⟨c₀⟩ := hne
    have H := h1 hΘ hm
    obtain ⟨PZ₀, hPZ₀⟩ := H.1 c₀
    refine ⟨PZ₀.transport (S.suppHomeomorph c₀ hΘ.isFunctorial), fun c _ _ => ⟨H.1 c, ?_⟩⟩
    intro PZc hPZc e g he hg
    have D := H.2 c c₀ PZc PZ₀ hPZc hPZ₀
    have t := PZc.isScDiffeoOn_transport (S.suppHomeomorph c hΘ.isFunctorial)
    have K := D.comp t
    have he' : e = S.suppHomeomorph c hΘ.isFunctorial :=
      funext fun x => Subtype.ext ((he x).trans (suppHomeomorph_val c hΘ.isFunctorial x).symm)
    have hg' : g = (S.suppHomeomorph c hΘ.isFunctorial).symm := by
      funext y
      apply (S.suppHomeomorph c hΘ.isFunctorial).injective
      rw [Homeomorph.apply_symm_apply]
      exact Subtype.ext ((suppHomeomorph_val c hΘ.isFunctorial (g y)).trans (hg y))
    subst he' hg'
    exact K
  · intro ho
    have H := h2 hΘ ho
    refine ⟨fun c => ?_, fun c hA => ?_, fun c c' hA hA' => ?_⟩
    · obtain ⟨hA, hsub, -⟩ := H.1 c
      exact ⟨hA, hsub⟩
    · obtain ⟨hA₁, -, e, he⟩ := H.1 c
      refine ⟨e, fun x => ?_⟩
      exact (he x).trans ((S.modelFunctor c.Ψ).orbitMap_π _).symm
    · obtain ⟨A₀, F, Φ, ΘA, hF, hΦ, hΘA, hoA, hmF, hmΦ, horb⟩ := H.2 c c'
      have hSA := isEpSubgroupoid_supp_of_isOrbifoldType hΘA hoA
      have := A₀.X.PObj.paracompactSpace_subtype (EpGroupoid.supp ΘA)
      have := (S.modelEP c.Ψ).X.PObj.paracompactSpace_subtype (EpGroupoid.supp (S.modelPull c.Ψ Θ))
      have := (S.modelEP c'.Ψ).X.PObj.paracompactSpace_subtype
        (EpGroupoid.supp (S.modelPull c'.Ψ Θ))
      let d : Diagram ((S.modelEP c.Ψ).sub hA) ((S.modelEP c'.Ψ).sub hA') :=
        { A := A₀.sub hSA
          F := F.restrictSub hSA hA hmF
          isEquivalence_F := hF.restrictSub hSA hA hmF
          Φ := Φ.restrictSub hSA hA' hmΦ }
      refine ⟨homMk d, (theorem_10_3_10 d).1.2 (hΦ.restrictSub hSA hA' hmΦ), fun x y hxy => ?_⟩
      obtain ⟨b, ψ, hs, ht⟩ := hF.exists_iso x.1
      have hb : b ∈ EpGroupoid.supp ΘA := by
        refine (hmF b).2 ?_
        rw [← hs]
        exact src_mem_of_tgt_mem_of_isSaturated hA.isSaturated (by rw [ht]; exact x.2)
      have h1 : d.F.orbitMap ((A₀.sub hSA).X.π ⟨b, hb⟩) = ((S.modelEP c.Ψ).sub hA).X.π x := by
        refine (d.F.orbitMap_π _).trans ?_
        refine (GroupoidStr.π_eq_π_iff _).2 ⟨⟨ψ, ?_, ?_⟩, Subtype.ext hs, Subtype.ext ht⟩
        · rw [hs]; exact (hmF b).1 hb
        · rw [ht]; exact x.2
      have h2' := Diagram.orbitMap_eq_of h1
      rw [orbitMap_homMk, h2'] at hxy
      replace hxy := ((d.Φ.orbitMap_π _).symm.trans hxy :)
      obtain ⟨φ', hs', ht'⟩ := (GroupoidStr.π_eq_π_iff _).1 hxy
      have h3 : (S.modelEP c'.Ψ).X.π (Φ.obj b) = (S.modelEP c'.Ψ).X.π y.1 :=
        (GroupoidStr.π_eq_π_iff _).2 ⟨φ'.1, congrArg Subtype.val hs', congrArg Subtype.val ht'⟩
      have h4 : (S.modelEP c.Ψ).X.π (F.obj b) = (S.modelEP c.Ψ).X.π x.1 :=
        (GroupoidStr.π_eq_π_iff _).2 ⟨ψ, hs, ht⟩
      rw [← h3, ← h4, (S.modelFunctor c'.Ψ).orbitMap_π, (S.modelFunctor c.Ψ).orbitMap_π]
      exact (horb b).symm

/-! ### Copies (the project's proofs, from non-item lemmas) of the ep-groupoid conjuncts -/

theorem restrictSupp_orbifold' {X Y : EP.{0}} {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {Θ' : Y.Obj → ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (ho' : IsOrbifoldType Θ')
    {Θ : X.Obj → ℚ} (hpull : pullTheta f Θ' = Θ) :
    ∃ (A : EP.{0}) (F : EpFunctor A.X X.X) (Φ : EpFunctor A.X Y.X) (ΘA : A.Obj → ℚ),
      F.IsEquivalence ∧ Φ.IsEquivalence ∧ A.X.IsBranchedEpSubgroupoid ΘA ∧ IsOrbifoldType ΘA ∧
      (∀ b, b ∈ EpGroupoid.supp ΘA ↔ F.obj b ∈ EpGroupoid.supp Θ) ∧
      (∀ b, b ∈ EpGroupoid.supp ΘA ↔ Φ.obj b ∈ EpGroupoid.supp Θ') ∧
      ∀ b, orbitMap f (X.X.π (F.obj b)) = Y.X.π (Φ.obj b) := by
  subst hpull
  set d := rep f
  have hF := d.isEquivalence_F
  have hΦ := isEquivalence_rep_Φ hf
  set ΘA := d.Φ.pullbackTheta Θ'
  have hΘA := EpFunctor.isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ'
  refine ⟨d.A, d.F, d.Φ, ΘA, hF, hΦ, hΘA, fun x => ho' (d.Φ.obj x), fun b => ?_,
    fun _ => Iff.rfl, fun b => ?_⟩
  · change 0 < ΘA b ↔ 0 < d.F.pushforwardTheta ΘA (d.F.obj b)
    rw [EpFunctor.pushforwardTheta_obj hF.full hΘA.isFunctorial]
  · rw [orbitMap_eq_rep]
    exact ((rep f).orbitMap_orbitMap_F (d.A.X.π b))

theorem isScSmoothOn_orbitSuppMap' {X Y : EP.{0}} {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {Θ' : Y.Obj → ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (ho' : IsOrbifoldType Θ')
    {Θ : X.Obj → ℚ} (hpull : pullTheta f Θ' = Θ)
    [ParacompactSpace (X.X.orbitSupp Θ)] [ParacompactSpace (Y.X.orbitSupp Θ')]
    {PZ : MPolyfold (X.X.orbitSupp Θ)} {PZ' : MPolyfold (Y.X.orbitSupp Θ')}
    (hPZ : X.X.IsSuppStructure Θ PZ) (hPZ' : Y.X.IsSuppStructure Θ' PZ') :
    PZ.IsScSmoothOn PZ' (orbitSuppMap hf hΘ'.isFunctorial hpull) univ := by
  classical
  obtain ⟨hA, -, hloc⟩ := hPZ
  obtain ⟨hA', -, hloc'⟩ := hPZ'
  have := X.X.PObj.paracompactSpace_subtype (EpGroupoid.supp Θ)
  have := Y.X.PObj.paracompactSpace_subtype (EpGroupoid.supp Θ')
  obtain ⟨A, F, Φ, ΘA, hF, hΦ, hΘA, hoA, hmemF, hmemΦ, horb⟩ :=
    restrictSupp_orbifold' hf hΘ' ho' hpull
  have hSA := isEpSubgroupoid_supp_of_isOrbifoldType hΘA hoA
  have := A.X.PObj.paracompactSpace_subtype (EpGroupoid.supp ΘA)
  set Fs := F.restrictSub hSA hA hmemF
  set Φs := Φ.restrictSub hSA hA' hmemΦ
  have hFs := (hF.restrictSub hSA hA hmemF).isLocalScDiffeo_obj
  have hΦs := Φs.isScSmoothMap_obj
  have key : ∀ b : EpGroupoid.supp ΘA,
      orbitSuppMap hf hΘ'.isFunctorial hpull (X.X.orbitSuppProj Θ (Fs.obj b)) =
      Y.X.orbitSuppProj Θ' (Φs.obj b) := fun b => Subtype.ext (horb b.1)
  refine IsScSmoothOn.of_locally isOpen_univ fun q _ => ?_
  obtain ⟨b, rfl⟩ : ∃ b : EpGroupoid.supp ΘA, X.X.orbitSuppProj Θ (Fs.obj b) = q := by
    obtain ⟨_, x, hx, rfl⟩ := q
    obtain ⟨y, ψ, hs, ht⟩ := hF.exists_iso x
    have hψs : X.X.src ψ ∈ EpGroupoid.supp Θ :=
      src_mem_of_tgt_mem_of_isSaturated hA.isSaturated (by rw [ht]; exact hx)
    have hy : y ∈ EpGroupoid.supp ΘA := (hmemF y).2 (hs ▸ hψs)
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change X.X.π (F.obj y) = X.X.π x
    exact (GroupoidStr.π_eq_π_iff _).2 ⟨ψ, hs, ht⟩
  obtain ⟨U₁, V₁, g₁, hU₁, hd₁⟩ := hloc (Fs.obj b)
  obtain ⟨U₂, V₂, g₂, hU₂, hd₂⟩ := hFs b
  set V := V₁ ∩ g₁ ⁻¹' V₂
  have hV : IsOpen V := hd₁.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage
    hd₁.isScSmoothOn_inv.isOpen hd₂.isScSmoothOn_inv.isOpen
  have hqV : X.X.orbitSuppProj Θ (Fs.obj b) ∈ V := by
    refine ⟨hd₁.mapsTo hU₁, ?_⟩
    change g₁ _ ∈ V₂
    rw [hd₁.left_inv _ hU₁]
    exact hd₂.mapsTo hU₂
  refine ⟨V, hV, hqV, subset_univ _, ?_⟩
  have hg₁ : PZ.IsScSmoothOn (subEpGroupoid hA).PObj g₁ V :=
    hd₁.isScSmoothOn_inv.mono hV inter_subset_left
  have hg₂ := IsScSmoothOn.comp hd₂.isScSmoothOn_inv hg₁ fun z hz => hz.2
  have hΦg := IsScSmoothOn.comp hΦs hg₂ (mapsTo_univ _ _)
  have hG := IsScSmoothOn.comp (hloc'.isScSmoothMap) hΦg (mapsTo_univ _ _)
  refine hG.congr fun z hz => ?_
  have h2 : X.X.orbitSuppProj Θ (g₁ z) = z := hd₁.right_inv z hz.1
  have h3 : Fs.obj (g₂ (g₁ z)) = g₁ z := hd₂.right_inv _ hz.2
  change Y.X.orbitSuppProj Θ' (Φs.obj (g₂ (g₁ z))) = orbitSuppMap hf hΘ'.isFunctorial hpull z
  rw [← key, h3, h2]

theorem B_to_A' : B → A' := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `proposition_17_5_5_one` from `B`'s manifold part
    intro C S Θ hΘ hm
    obtain ⟨PZ₀, hPZ₀⟩ := (hB C S Θ hΘ).2.1 hm
    refine ⟨fun c => (hPZ₀ c).1, fun c c' PZ PZ' hPZ hPZ' => ?_⟩
    have hc := (hPZ₀ c).2 PZ hPZ (S.suppHomeomorph c hΘ.isFunctorial)
      (S.suppHomeomorph c hΘ.isFunctorial).symm (fun x => suppHomeomorph_val c _ x)
      (fun y => by rw [← suppHomeomorph_val c hΘ.isFunctorial, Homeomorph.apply_symm_apply])
    have hc' := (hPZ₀ c').2 PZ' hPZ' (S.suppHomeomorph c' hΘ.isFunctorial)
      (S.suppHomeomorph c' hΘ.isFunctorial).symm (fun x => suppHomeomorph_val c' _ x)
      (fun y => by rw [← suppHomeomorph_val c' hΘ.isFunctorial, Homeomorph.apply_symm_apply])
    have t := PZ.isScDiffeoOn_transport (S.suppHomeomorph c hΘ.isFunctorial)
    have t' := PZ'.isScDiffeoOn_transport (S.suppHomeomorph c' hΘ.isFunctorial)
    have K := (t'.comp hc'.symm).comp (hc.comp t.symm)
    refine (K.congr_left fun z _ => ?_).congr_right fun z _ => ?_
    · change (S.suppHomeomorph c' hΘ.isFunctorial) ((S.suppHomeomorph c' hΘ.isFunctorial).symm
        ((S.suppHomeomorph c hΘ.isFunctorial) ((S.suppHomeomorph c hΘ.isFunctorial).symm z))) = z
      rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
    · change (S.suppHomeomorph c hΘ.isFunctorial) ((S.suppHomeomorph c hΘ.isFunctorial).symm
        ((S.suppHomeomorph c' hΘ.isFunctorial) ((S.suppHomeomorph c' hΘ.isFunctorial).symm z))) = z
      rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  · -- `proposition_17_5_5_two`: part 1 from `B`, part 2 re-proved
    intro C S Θ hΘ ho
    refine ⟨fun c => ?_, fun c c' => ?_⟩
    · obtain ⟨hA, hsub⟩ := (hB C S Θ hΘ).2.2 ho |>.1 c
      obtain ⟨e, he⟩ := ((hB C S Θ hΘ).2.2 ho).2.1 c hA
      exact ⟨hA, hsub, e, fun x => (he x).trans ((S.modelFunctor c.Ψ).orbitMap_π _)⟩
    · obtain ⟨A, F, Φ, ΘA, hF, hΦ, hΘA, hoA, hmF, hmΦ, horb⟩ :=
        restrictSupp_orbifold' (S.isGeneralizedIso_comparison c c')
          (proposition_17_5_2_two (Ψ := c'.Ψ) hΘ)
          ((isOrbifoldType_modelPull_iff c' hΘ.isFunctorial).2 ho)
          (pullTheta_comparison_modelPull c c' hΘ.isFunctorial)
      refine ⟨A, F, Φ, ΘA, hF, hΦ, hΘA, hoA, hmF, hmΦ, fun b => ?_⟩
      have h := congrFun (S.orbitMap_comparison c c') ((S.modelEP c.Ψ).X.π (F.obj b))
      exact h.symm.trans (congrArg (S.modelFunctor c'.Ψ).orbitMap (horb b))
  · intro C S Θ c c' hΘ q
    exact Subtype.ext (congrFun (S.orbitMap_comparison c c') q.1)
  · intro C Θ
    exact paracompactSpace_of_metrizableSpace _
  · intro Obj Mor _ _ _ _ _ _ X Θ hΘ hm
    have := hΘ.paracompactSpace_orbitSupp
    obtain ⟨hA, hsub, PZ, hPZ⟩ := X.proposition_9_1_9_one hΘ hm
    exact ⟨PZ, hA, hsub, hPZ⟩
  · intro X Y f hf Θ' hΘ' ho' Θ hpull _ _ PZ PZ' hPZ hPZ'
    exact isScSmoothOn_orbitSuppMap' hf hΘ' ho' hpull hPZ hPZ'
  · intro X Y f hf Θ' hΘ' ho' Θ hpull
    exact restrictSupp_orbifold' hf hΘ' ho' hpull

theorem B_to_A : B → A := B_to_A'

theorem A'_to_B_of_nonempty (h : A') {C : GCT.{0}} (S : C.PolyfoldConstruction)
    [Nonempty S.CoveringFamily] (Θ : C.Obj → ℚ) (hΘ : S.IsBranchedSubcategory Θ) :
    ImageSupp S Θ ∧ ManifoldPart S Θ ∧ OrbifoldPart S Θ :=
  main'_to_B_of_nonempty ⟨h.1, h.2.1⟩ S Θ hΘ

theorem main_to_B_of_nonempty : Main → ∀ {C : GCT.{0}} (S : C.PolyfoldConstruction)
    [Nonempty S.CoveringFamily] (Θ : C.Obj → ℚ), S.IsBranchedSubcategory Θ →
    ImageSupp S Θ ∧ ManifoldPart S Θ ∧ OrbifoldPart S Θ := main'_to_B_of_nonempty

/-- `A ⇒ B` for polyfold structures that have a covering family (the full `A_to_B` is not
proved: see the JSON). -/
theorem A_to_B_of_nonempty : A → ∀ {C : GCT.{0}} (S : C.PolyfoldConstruction)
    [Nonempty S.CoveringFamily] (Θ : C.Obj → ℚ), S.IsBranchedSubcategory Θ →
    ImageSupp S Θ ∧ ManifoldPart S Θ ∧ OrbifoldPart S Θ := A'_to_B_of_nonempty

theorem B_to_main' : B → Main' := fun hB => ⟨(B_to_A' hB).1, (B_to_A' hB).2.1⟩
theorem B_to_main : B → Main := B_to_main'

#rt_check RoundTrip.V17_99.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_one, Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_two, Polyfold.GCT.PolyfoldConstruction.suppHomeomorph_orbitSuppMap, Polyfold.GCT.PolyfoldConstruction.paracompactSpace_orbitSuppC, Polyfold.EpGroupoid.exists_isSuppStructure, Polyfold.EPLocalization.EPLoc.isScSmoothOn_orbitSuppMap, Polyfold.EPLocalization.EPLoc.restrictSupp_orbifold]
#rt_check RoundTrip.V17_99.A_to_B_of_nonempty [Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_one, Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_two, Polyfold.GCT.PolyfoldConstruction.suppHomeomorph_orbitSuppMap, Polyfold.GCT.PolyfoldConstruction.paracompactSpace_orbitSuppC, Polyfold.EpGroupoid.exists_isSuppStructure, Polyfold.EPLocalization.EPLoc.isScSmoothOn_orbitSuppMap, Polyfold.EPLocalization.EPLoc.restrictSupp_orbifold]
#rt_check RoundTrip.V17_99.main_to_B_of_nonempty [Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_one, Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_two, Polyfold.GCT.PolyfoldConstruction.suppHomeomorph_orbitSuppMap, Polyfold.GCT.PolyfoldConstruction.paracompactSpace_orbitSuppC, Polyfold.EpGroupoid.exists_isSuppStructure, Polyfold.EPLocalization.EPLoc.isScSmoothOn_orbitSuppMap, Polyfold.EPLocalization.EPLoc.restrictSupp_orbifold]
#rt_check RoundTrip.V17_99.B_to_main [Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_one, Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_two, Polyfold.GCT.PolyfoldConstruction.suppHomeomorph_orbitSuppMap, Polyfold.GCT.PolyfoldConstruction.paracompactSpace_orbitSuppC, Polyfold.EpGroupoid.exists_isSuppStructure, Polyfold.EPLocalization.EPLoc.isScSmoothOn_orbitSuppMap, Polyfold.EPLocalization.EPLoc.restrictSupp_orbifold]
#rt_overlap RoundTrip.V17_99.B_to_A [Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_one, Polyfold.GCT.PolyfoldConstruction.proposition_17_5_5_two, Polyfold.GCT.PolyfoldConstruction.suppHomeomorph_orbitSuppMap, Polyfold.GCT.PolyfoldConstruction.paracompactSpace_orbitSuppC, Polyfold.EpGroupoid.exists_isSuppStructure, Polyfold.EPLocalization.EPLoc.isScSmoothOn_orbitSuppMap, Polyfold.EPLocalization.EPLoc.restrictSupp_orbifold]

end RoundTrip.V17_99
