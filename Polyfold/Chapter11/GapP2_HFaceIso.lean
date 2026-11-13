import Polyfold.Chapter11.GapP2_HFaces

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.1: **Proposition 11.1.6** (2021 pp. 524–525; 2017: Proposition 11.2,
p. 378), the generalized isomorphisms `[d]_F : F → [d]_*F` of (11.1), and **Proposition 11.1.8**
(2021 p. 526; 2017: Proposition 11.3, p. 380).

# The generalized isomorphisms between faces

## The text, paraphrased

(Proposition 11.1.6, last claim, and its proof, p. 525) For a generalized isomorphism `[d]`
represented by `X ←Φ A →Ψ Y` and a face `F` of `X`, `B = Φ⁻¹(F)` is a face of `A` and the
saturation `C` of `Ψ(B)` is a face of `Y`; the restrictions form the diagram (11.1)
`F ←Φ|B B →Ψ|B C`, whose class `[d]_F` is a generalized isomorphism `F → C` by Theorem 10.3.10:
the restricted functors are essentially surjective, full and faithful and local
sc-diffeomorphisms, hence equivalences by Lemma 10.1.2.  (Proposition 11.1.8) If `|f| = |g|`
then `f_* = g_*`, and the generalized isomorphisms `F → f_*F` and `F → g_*F` of (11.1) induce the
same map `|F| → |f_*F|`.

## What is formalized

* Restriction to ep-subgroupoids `A = G⁻¹(B)`: `EpFunctor.restrictSub` (with
  `restrictSub_comp`, `orbitMap_subEpFunctor_restrictSub`), `EpNatTrans.restrictSub`,
  `EpFunctor.IsEquivalence.restrictSub` (the text's argument: full, faithful, essentially
  surjective since `B` is saturated, a local sc-diffeomorphism on objects; Lemma 10.1.2);
  `MPolyfold.isLocalScDiffeo_subPolyfold_of_iff`.
* `EpFunctor.IsEquivalence.isEpFaceStructured_iff`; `EPLocalization.faceEP` (the face as an
  object of `EP`); `Diagram.restrictFace` (the diagram (11.1)), `isEquivalence_restrictFace_Φ`,
  `IsRefinement.restrictFace`, `Equiv.restrictFace` (equivalent diagrams have equivalent
  restrictions), `orbitMap_restrictFace` (`|d_F|` is the restriction of `|d|`).
* `EPLoc.faceIso f θ' h` (`[d]_F`, for `θ' = f_*θ`), `homMk_restrictFace_eq_faceIso` (it is the
  class of the restriction (11.1) of every representative: a natural class),
  `isGeneralizedIso_faceIso`, `orbitMap_faceIso`; **Proposition 11.1.6, last claim**:
  `proposition_11_1_6_faceIso`.  **Proposition 11.1.8**: `proposition_11_1_8_faceIso`.

## Choices

* The target face is passed as a set `θ'` with a proof of `θ' = f_*θ`, so that `[f]_F` and
  `[g]_F` have the same type when `f_* = g_*` and Proposition 11.1.8 is an equality of maps.
* The text's `C = saturation(Ψ(B))` is `Y_{|Ψ|(θ_A)}` (Remark 11.1.5,
  `saturation_image_faceObj`); the restriction to it uses `B = Ψ⁻¹(C)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

open scoped Polyfold.EpGroupoid

noncomputable section

namespace Polyfold

universe u v w

/-! ### Local sc-diffeomorphisms restricted to sub-M-polyfolds -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- An sc-smooth map restricted to a sub-M-polyfold `B` of its domain. -/
theorem isScSmoothOn_comp_subVal {B : Set X} (hB : P.IsSubMPolyfold B) [ParacompactSpace B]
    {g : X → Y} {U : Set X} (hg : P.IsScSmoothOn Q g U) :
    (subPolyfold hB).IsScSmoothOn Q (fun b : B => g b) (Subtype.val ⁻¹' U) :=
  IsScSmoothOn.comp hg ((subPolyfold_inclusion_isScSmooth hB).mono
    (hg.isOpen.preimage continuous_subtype_val) (subset_univ _)) fun _ h => h

/-- **A local sc-diffeomorphism restricts** to a local sc-diffeomorphism `B → A` between
sub-M-polyfolds when `B = f⁻¹(A)` (the argument of Chapter 7's `SubGroupoid.lean`). -/
theorem isLocalScDiffeo_subPolyfold_of_iff {f : X → Y} (hf : P.IsLocalScDiffeo Q f)
    {A : Set Y} {B : Set X} (hA : Q.IsSubMPolyfold A) (hB : P.IsSubMPolyfold B)
    [ParacompactSpace A] [ParacompactSpace B] (hBA : ∀ x, x ∈ B ↔ f x ∈ A) {f' : B → A}
    (hf' : ∀ b, (f' b : Y) = f b) :
    (subPolyfold hB).IsLocalScDiffeo (subPolyfold hA) f' := by
  classical
  intro b
  obtain ⟨W, V, g, hbW, hd⟩ := hf b.1
  have hgB : ∀ a : A, a.1 ∈ V → g a.1 ∈ B := fun a ha =>
    (hBA _).2 (by rw [hd.right_inv _ ha]; exact a.2)
  let g' : A → B := fun a => if h : g a.1 ∈ B then ⟨g a.1, h⟩ else b
  have hg' : ∀ a : A, a.1 ∈ V → (g' a : X) = g a.1 := fun a ha => by
    simp only [g', dif_pos (hgB a ha)]
  have hf'V : ∀ c : B, c.1 ∈ W → (f' c : Y) ∈ V := fun c hc => by
    rw [hf']; exact hd.mapsTo hc
  refine ⟨Subtype.val ⁻¹' W, Subtype.val ⁻¹' V, g', hbW, ?_⟩
  exact
    { isScSmoothOn := isScSmoothOn_sub_of_val hA
        ((isScSmoothOn_comp_subVal hB hd.isScSmoothOn).congr fun c _ => (hf' c).symm)
      isScSmoothOn_inv := isScSmoothOn_sub_of_val hB
        ((isScSmoothOn_comp_subVal hA hd.isScSmoothOn_inv).congr fun a ha => (hg' a ha).symm)
      mapsTo := fun c hc => hf'V c hc
      mapsTo_inv := fun a ha => by
        change (g' a : X) ∈ W
        rw [hg' a ha]; exact hd.mapsTo_inv ha
      left_inv := fun c hc => Subtype.ext (by rw [hg' _ (hf'V c hc), hf', hd.left_inv _ hc])
      right_inv := fun a ha => Subtype.ext (by rw [hf', hg' a ha, hd.right_inv _ ha]) }

end MPolyfold

/-! ### Restriction of functors and natural transformations to ep-subgroupoids -/

section Restrict

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {Obj'' Mor'' : Type w} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Z : EpGroupoid Obj'' Mor''}
  {A : Set Obj} {B : Set Obj'} {C : Set Obj''}
  (hA : X.IsEpSubgroupoid A) (hB : Y.IsEpSubgroupoid B) (hC : Z.IsEpSubgroupoid C)
  [ParacompactSpace A] [ParacompactSpace B] [ParacompactSpace C]

open EpGroupoid

namespace EpFunctor

omit [ParacompactSpace A] [ParacompactSpace B] in
theorem mem_morOn_mor (G : EpFunctor X Y) (hAB : ∀ x, x ∈ A ↔ G.obj x ∈ B) (φ : X.morOn A) :
    G.mor φ ∈ Y.morOn B :=
  ⟨by rw [G.src_mor]; exact (hAB _).1 φ.2.1, by rw [G.tgt_mor]; exact (hAB _).1 φ.2.2⟩

/-- **The restriction of `G : X → Y` to the ep-subgroupoids `A = G⁻¹(B)` and `B`** (the
functors `Φ|B`, `Ψ|B` of (11.1)). -/
def restrictSub (G : EpFunctor X Y) (hAB : ∀ x, x ∈ A ↔ G.obj x ∈ B) :
    EpFunctor (subEpGroupoid hA) (subEpGroupoid hB) where
  obj a := ⟨G.obj a, (hAB a).1 a.2⟩
  mor φ := ⟨G.mor φ, G.mem_morOn_mor hAB φ⟩
  src_mor φ := Subtype.ext (G.src_mor φ.1)
  tgt_mor φ := Subtype.ext (G.tgt_mor φ.1)
  mor_comp φ ψ h := by
    have h' : X.src φ.1 = X.tgt ψ.1 := congrArg Subtype.val h
    have hY : (subEpGroupoid hB).src ⟨G.mor φ, G.mem_morOn_mor hAB φ⟩ =
        (subEpGroupoid hB).tgt ⟨G.mor ψ, G.mem_morOn_mor hAB ψ⟩ :=
      Subtype.ext (show Y.src (G.mor φ.1) = Y.tgt (G.mor ψ.1) by
        rw [G.src_mor, G.tgt_mor, h'])
    refine Subtype.ext ?_
    change G.mor ((subEpGroupoid hA).comp φ ψ : Mor) = ((subEpGroupoid hB).comp _ _ : Mor')
    rw [subEpGroupoid_comp_val hA h, subEpGroupoid_comp_val hB hY, G.mor_comp _ _ h']
  mor_unit x := Subtype.ext (G.mor_unit x.1)
  isScSmoothMap_obj := MPolyfold.isScSmoothOn_sub_of_val hB.isSubMPolyfold
    (MPolyfold.isScSmoothOn_comp_subVal hA.isSubMPolyfold G.isScSmoothMap_obj)
  isScSmoothMap_mor := MPolyfold.isScSmoothOn_sub_of_val (Y.isSubMPolyfold_morOn hB)
    (MPolyfold.isScSmoothOn_comp_subVal (X.isSubMPolyfold_morOn hA) G.isScSmoothMap_mor)

@[simp] theorem restrictSub_obj_val (G : EpFunctor X Y) (hAB : ∀ x, x ∈ A ↔ G.obj x ∈ B)
    (a : A) : ((G.restrictSub hA hB hAB).obj a : Obj') = G.obj a := rfl

/-- Restriction commutes with composition. -/
theorem restrictSub_comp (G : EpFunctor Y Z) (H : EpFunctor X Y)
    (hBC : ∀ y, y ∈ B ↔ G.obj y ∈ C) (hAB : ∀ x, x ∈ A ↔ H.obj x ∈ B)
    (hAC : ∀ x, x ∈ A ↔ (G.comp H).obj x ∈ C) :
    (G.comp H).restrictSub hA hC hAC = (G.restrictSub hB hC hBC).comp (H.restrictSub hA hB hAB) :=
  EpFunctor.ext rfl rfl

/-- `|G| ∘ |i_A| = |i_B| ∘ |G|B|`. -/
theorem orbitMap_subEpFunctor_restrictSub (G : EpFunctor X Y) (hAB : ∀ x, x ∈ A ↔ G.obj x ∈ B)
    (q : (subEpGroupoid hA).OrbitSpace) :
    (subEpFunctor hB).orbitMap ((G.restrictSub hA hB hAB).orbitMap q) =
      G.orbitMap ((subEpFunctor hA).orbitMap q) := by
  induction q using Quotient.inductionOn with | h x => rfl

/-- **The restriction of an equivalence is an equivalence** (proof of Proposition 11.1.6,
p. 525): full and faithful as `G` is, essentially surjective since `B` is saturated, and a
local sc-diffeomorphism on objects; Lemma 10.1.2. -/
theorem IsEquivalence.restrictSub {G : EpFunctor X Y} (hG : G.IsEquivalence)
    (hAB : ∀ x, x ∈ A ↔ G.obj x ∈ B) : (G.restrictSub hA hB hAB).IsEquivalence := by
  refine lemma_10_1_2 _ ?_ ?_
  · refine { faithful := ?_, full := ?_, essSurj := ?_ }
    · refine (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs ht he => Subtype.ext ?_
      exact hG.mor_injective (congrArg Subtype.val hs) (congrArg Subtype.val ht)
        (congrArg Subtype.val he)
    · refine (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => ?_
      obtain ⟨φ, h₁, h₂, h₃⟩ := hG.exists_mor_eq (congrArg Subtype.val hs)
        (congrArg Subtype.val ht)
      have hφ : φ ∈ X.morOn A := ⟨by rw [h₁]; exact x.2, by rw [h₂]; exact x'.2⟩
      exact ⟨⟨φ, hφ⟩, Subtype.ext h₁, Subtype.ext h₂, Subtype.ext h₃⟩
    · refine (GroupoidFunctor.essSurj_iff _).2 fun y => ?_
      obtain ⟨x, ψ, hs, ht⟩ := hG.exists_iso y.1
      have hψt : Y.tgt ψ ∈ B := by rw [ht]; exact y.2
      have hψs : Y.src ψ ∈ B := src_mem_of_tgt_mem_of_isSaturated hB.isSaturated hψt
      have hx : x ∈ A := (hAB x).2 (hs ▸ hψs)
      exact ⟨⟨x, hx⟩, ⟨ψ, hψs, hψt⟩, Subtype.ext hs, Subtype.ext ht⟩
  · exact MPolyfold.isLocalScDiffeo_subPolyfold_of_iff hG.isLocalScDiffeo_obj hB.isSubMPolyfold
      hA.isSubMPolyfold hAB fun _ => rfl

end EpFunctor

/-- **The restriction of a natural transformation** `τ : G → G'` to `A = G⁻¹(B) = G'⁻¹(B)`. -/
def EpNatTrans.restrictSub {G G' : EpFunctor X Y} (τ : EpNatTrans G G')
    (hAB : ∀ x, x ∈ A ↔ G.obj x ∈ B) (hAB' : ∀ x, x ∈ A ↔ G'.obj x ∈ B) :
    EpNatTrans (G.restrictSub hA hB hAB) (G'.restrictSub hA hB hAB') where
  app a := ⟨τ.app a, by rw [τ.src_app]; exact (hAB _).1 a.2,
    by rw [τ.tgt_app]; exact (hAB' _).1 a.2⟩
  isScSmoothMap_app := MPolyfold.isScSmoothOn_sub_of_val (Y.isSubMPolyfold_morOn hB)
    (MPolyfold.isScSmoothOn_comp_subVal hA.isSubMPolyfold τ.isScSmoothMap_app)
  src_app a := Subtype.ext (τ.src_app a)
  tgt_app a := Subtype.ext (τ.tgt_app a)
  naturality h := by
    have h₁ : Y.src (τ.app (X.tgt h.1)) = Y.tgt (G.mor h.1) := by
      rw [τ.src_app, G.tgt_mor]
    have h₂ : Y.src (G'.mor h.1) = Y.tgt (τ.app (X.src h.1)) := by
      rw [τ.tgt_app, G'.src_mor]
    refine Subtype.ext ?_
    rw [subEpGroupoid_comp_val hB, subEpGroupoid_comp_val hB]
    all_goals first | exact τ.naturality h.1 | exact Subtype.ext h₁ | exact Subtype.ext h₂

end Restrict

/-! ### Face structure along equivalences -/

namespace EpFunctor.IsEquivalence

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {F : EpFunctor X Y}

/-- An equivalence preserves and reflects being face structured (Remark 11.1.5). -/
theorem isEpFaceStructured_iff (hF : F.IsEquivalence) :
    X.IsEpFaceStructured ↔ Y.IsEpFaceStructured := by
  rw [EpGroupoid.isEpFaceStructured_iff, EpGroupoid.isEpFaceStructured_iff, hF.isTame_iff,
    TameBoundary.isFaceStructuredOpen_univ_iff hF.isHomeomorph_orbitMap hF.degIndexOrbit_orbitMap]

end EpFunctor.IsEquivalence

/-! ### The diagram (11.1) -/

namespace EPLocalization

open EpGroupoid

/-- **The face `X_θ` of a face structured ep-groupoid as an object of `EP`** (Proposition
11.1.6). -/
def faceEP (X : EP.{u}) (hX : X.X.IsEpFaceStructured) {θ : Set X.X.OrbitSpace}
    (hθ : X.X.IsOrbitFace θ) : EP.{u} :=
  ⟨X.X.faceObj θ, X.X.morOn (X.X.faceObj θ), X.X.faceEpGroupoid hX hθ⟩

namespace Diagram

variable {X Y : EP.{u}} (d : Diagram X Y) (hX : X.X.IsEpFaceStructured)
  {θ : Set X.X.OrbitSpace} (hθ : X.X.IsOrbitFace θ) (hY : Y.X.IsEpFaceStructured)
  {θ' : Set Y.X.OrbitSpace} (hθ' : Y.X.IsOrbitFace θ')

include hX in
theorem isEpFaceStructured_A : d.A.X.IsEpFaceStructured :=
  d.isEquivalence_F.isEpFaceStructured_iff.2 hX

include hθ in
/-- `θ_A = |F|⁻¹(θ)` is a face of `|A|` (Remark 11.1.5). -/
theorem isOrbitFace_A : d.A.X.IsOrbitFace (d.F.orbitMap ⁻¹' θ) :=
  d.isEquivalence_F.bijOn_faces.2.2 hθ

include hX hθ in
theorem isEpSubgroupoid_A : d.A.X.IsEpSubgroupoid (d.A.X.faceObj (d.F.orbitMap ⁻¹' θ)) :=
  isEpSubgroupoid_faceObj (d.isEpFaceStructured_A hX) (d.isOrbitFace_A hθ)

theorem mem_faceObj_A_iff (a : d.A.Obj) :
    a ∈ d.A.X.faceObj (d.F.orbitMap ⁻¹' θ) ↔ d.F.obj a ∈ X.X.faceObj θ := by
  change d.F.orbitMap (d.A.X.π a) ∈ θ ↔ X.X.π (d.F.obj a) ∈ θ
  rw [GroupoidFunctor.orbitMap_π]

theorem mem_faceObj_A_iff' (hd : ∀ p, p ∈ θ ↔ d.orbitMap p ∈ θ')
    (a : d.A.Obj) :
    a ∈ d.A.X.faceObj (d.F.orbitMap ⁻¹' θ) ↔ d.Φ.obj a ∈ Y.X.faceObj θ' := by
  change d.F.orbitMap (d.A.X.π a) ∈ θ ↔ Y.X.π (d.Φ.obj a) ∈ θ'
  rw [← GroupoidFunctor.orbitMap_π, ← orbitMap_orbitMap_F]
  exact hd _

/-- **The diagram (11.1)** `X_θ ← A_{θ_A} → Y_{θ'}` of the restrictions, for `θ_A = |F|⁻¹(θ)`
and a face `θ'` of `|Y|` with `θ = |d|⁻¹(θ')`. -/
def restrictFace (hd : ∀ p, p ∈ θ ↔ d.orbitMap p ∈ θ') :
    Diagram (faceEP X hX hθ) (faceEP Y hY hθ') where
  A := faceEP d.A (d.isEpFaceStructured_A hX) (d.isOrbitFace_A hθ)
  F := d.F.restrictSub (d.isEpSubgroupoid_A hX hθ)
    (isEpSubgroupoid_faceObj hX hθ) (d.mem_faceObj_A_iff)
  isEquivalence_F := d.isEquivalence_F.restrictSub _ _ _
  Φ := d.Φ.restrictSub (d.isEpSubgroupoid_A hX hθ)
    (isEpSubgroupoid_faceObj hY hθ') (d.mem_faceObj_A_iff' hd)

variable {d hX hθ hY hθ'}

/-- If `Φ` is an equivalence, so is its restriction: `[d_F]` is a generalized isomorphism
(Theorem 10.3.10). -/
theorem isEquivalence_restrictFace_Φ {hd : ∀ p, p ∈ θ ↔ d.orbitMap p ∈ θ'}
    (hΦ : d.Φ.IsEquivalence) : (d.restrictFace hX hθ hY hθ' hd).Φ.IsEquivalence :=
  EpFunctor.IsEquivalence.restrictSub (d.isEpSubgroupoid_A hX hθ)
    (isEpSubgroupoid_faceObj hY hθ') hΦ (d.mem_faceObj_A_iff' hd)

/-- **`|d_F|` is the restriction of `|d|`**: `|i_Y| ∘ |d_F| = |d| ∘ |i_X|`. -/
theorem orbitMap_restrictFace {hd : ∀ p, p ∈ θ ↔ d.orbitMap p ∈ θ'}
    (q : (faceEP X hX hθ).X.OrbitSpace) :
    (subEpFunctor (isEpSubgroupoid_faceObj hY hθ')).orbitMap
        ((d.restrictFace hX hθ hY hθ' hd).orbitMap q) =
      d.orbitMap ((subEpFunctor (isEpSubgroupoid_faceObj hX hθ)).orbitMap q) := by
  obtain ⟨r, rfl⟩ :=
    (d.restrictFace hX hθ hY hθ' hd).isEquivalence_F.isHomeomorph_orbitMap.surjective q
  rw [orbitMap_orbitMap_F]
  have h1 := EpFunctor.orbitMap_subEpFunctor_restrictSub
    (d.isEpSubgroupoid_A hX hθ) (isEpSubgroupoid_faceObj hY hθ') d.Φ
    (d.mem_faceObj_A_iff' hd) r
  have h2 := EpFunctor.orbitMap_subEpFunctor_restrictSub
    (d.isEpSubgroupoid_A hX hθ) (isEpSubgroupoid_faceObj hX hθ) d.F
    d.mem_faceObj_A_iff r
  refine h1.trans ?_
  rw [show (subEpFunctor (isEpSubgroupoid_faceObj hX hθ)).orbitMap
    ((d.restrictFace hX hθ hY hθ' hd).F.orbitMap r) = _ from h2, orbitMap_orbitMap_F]

/-- **Refinements restrict to refinements**: if `H : d' → d`, then `H|` refines the restriction
of `d` by the restriction of `d'`. -/
theorem IsRefinement.restrictFace {d d' : Diagram X Y}
    {hd : ∀ p, p ∈ θ ↔ d.orbitMap p ∈ θ'}
    {hd' : ∀ p, p ∈ θ ↔ d'.orbitMap p ∈ θ'} (h : d'.IsRefinement d) :
    (d'.restrictFace hX hθ hY hθ' hd').IsRefinement (d.restrictFace hX hθ hY hθ' hd) := by
  obtain ⟨H, hH, ⟨τ⟩, ⟨σ⟩⟩ := h
  have eF : d'.F.orbitMap = d.F.orbitMap ∘ H.orbitMap := by
    rw [← EpFunctor.orbitMap_comp]
    exact (EpFunctor.NaturallyEquivalent.orbitMap_eq ⟨τ⟩).symm
  have hAB : ∀ a, a ∈ d'.A.X.faceObj (d'.F.orbitMap ⁻¹' θ) ↔
      H.obj a ∈ d.A.X.faceObj (d.F.orbitMap ⁻¹' θ) := fun a => by
    change d'.F.orbitMap (d'.A.X.π a) ∈ θ ↔ d.F.orbitMap (d.A.X.π (H.obj a)) ∈ θ
    rw [eF, ← GroupoidFunctor.orbitMap_π]
    rfl
  have hA' := d'.isEpSubgroupoid_A hX hθ
  have hA := d.isEpSubgroupoid_A hX hθ
  refine ⟨H.restrictSub hA' hA hAB, hH.restrictSub _ _ _, ⟨?_⟩, ⟨?_⟩⟩
  · have hAC : ∀ a, a ∈ d'.A.X.faceObj (d'.F.orbitMap ⁻¹' θ) ↔
        (d.F.comp H).obj a ∈ X.X.faceObj θ := fun a =>
      (hAB a).trans (d.mem_faceObj_A_iff _)
    have e := EpFunctor.restrictSub_comp hA' hA (isEpSubgroupoid_faceObj hX hθ) d.F H
      d.mem_faceObj_A_iff hAB hAC
    have τ' := τ.restrictSub hA' (isEpSubgroupoid_faceObj hX hθ) hAC d'.mem_faceObj_A_iff
    rw [e] at τ'
    exact τ'
  · have hAC : ∀ a, a ∈ d'.A.X.faceObj (d'.F.orbitMap ⁻¹' θ) ↔
        (d.Φ.comp H).obj a ∈ Y.X.faceObj θ' := fun a =>
      (hAB a).trans (d.mem_faceObj_A_iff' hd _)
    have e := EpFunctor.restrictSub_comp hA' hA (isEpSubgroupoid_faceObj hY hθ') d.Φ H
      (d.mem_faceObj_A_iff' hd) hAB hAC
    have σ' := σ.restrictSub hA' (isEpSubgroupoid_faceObj hY hθ') hAC (d'.mem_faceObj_A_iff' hd')
    rw [e] at σ'
    exact σ'

/-- **Equivalent diagrams have equivalent restrictions** (the class `[d]_F` is natural). -/
theorem Equiv.restrictFace {d d' : Diagram X Y}
    {hd : ∀ p, p ∈ θ ↔ d.orbitMap p ∈ θ'}
    {hd' : ∀ p, p ∈ θ ↔ d'.orbitMap p ∈ θ'} (h : Equiv d d') :
    Equiv (d.restrictFace hX hθ hY hθ' hd) (d'.restrictFace hX hθ hY hθ' hd') := by
  obtain ⟨d'', h₁, h₂⟩ := h
  have e₁ : d''.orbitMap = d.orbitMap := (lemma_10_3_6 h₁).symm
  have hd'' : ∀ p, p ∈ θ ↔ d''.orbitMap p ∈ θ' := by rw [e₁]; exact hd
  exact ⟨d''.restrictFace hX hθ hY hθ' hd'', h₁.restrictFace, h₂.restrictFace⟩

end Diagram

/-! ### `[d]_F` on classes: Proposition 11.1.6, last claim, and Proposition 11.1.8 -/

namespace EPLoc

variable {X Y : EP.{u}} {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
  (hX : X.X.IsEpFaceStructured) {θ : Set X.X.OrbitSpace} (hθ : X.X.IsOrbitFace θ)
  {θ' : Set Y.X.OrbitSpace} (hθ' : faceMap f θ = θ')

include hf hX in
/-- `Y` is face structured (Remark 11.1.7). -/
theorem isEpFaceStructured_target : Y.X.IsEpFaceStructured := (remark_11_1_7 hf).1 hX

include hf hθ hθ' in
/-- `θ' = [d]_*θ` is a face of `|Y|`. -/
theorem isOrbitFace_target : Y.X.IsOrbitFace θ' := hθ' ▸ isOrbitFace_faceMap hf hθ

include hf hθ' in
/-- For a representative `d` of `f`: `θ = |d|⁻¹(θ')`. -/
theorem mem_iff_orbitMap_mem {d : Diagram X Y} (hd : homMk d = f) (p : X.X.OrbitSpace) :
    p ∈ θ ↔ d.orbitMap p ∈ θ' := by
  subst hd hθ'
  exact ((isHomeomorph_orbitMap hf).injective.mem_set_image).symm

/-- **The generalized isomorphism `[d]_F : X_θ → Y_{θ'}`** of (11.1), `θ' = [d]_*θ`: the class of
the restriction of a representative of `f` (any representative gives the same class,
`homMk_restrictFace_eq_faceIso`). -/
def faceIso : of (faceEP X hX hθ) ⟶
    of (faceEP Y (isEpFaceStructured_target hf hX) (isOrbitFace_target hf hθ hθ')) :=
  homMk ((Quotient.out f).restrictFace hX hθ _ _
    (mem_iff_orbitMap_mem hf hθ' (Quotient.out_eq f)))

/-- **`[d]_F` is a natural class**: it is the class of the diagram (11.1) of every
representative `d` of `f`. -/
theorem homMk_restrictFace_eq_faceIso {d : Diagram X Y} (hd : homMk d = f) :
    homMk (d.restrictFace hX hθ (isEpFaceStructured_target hf hX) (isOrbitFace_target hf hθ hθ')
      (mem_iff_orbitMap_mem hf hθ' hd)) = faceIso hf hX hθ hθ' :=
  homMk_eq_homMk_iff.2 (Diagram.Equiv.restrictFace
    (homMk_eq_homMk_iff.1 (hd.trans (Quotient.out_eq f).symm)))

/-- **`[d]_F` is a generalized isomorphism** (Theorem 10.3.10: the restricted functors are
equivalences). -/
theorem isGeneralizedIso_faceIso : IsGeneralizedIso (faceIso hf hX hθ hθ') := by
  have hΦ : (Quotient.out f).Φ.IsEquivalence :=
    (theorem_10_3_10 (Quotient.out f)).1.1 (by
      rw [show homMk (Quotient.out f) = f from Quotient.out_eq f]
      exact hf)
  exact (theorem_10_3_10 _).1.2 (Diagram.isEquivalence_restrictFace_Φ hΦ)

/-- **`|[d]_F|` is the restriction of `|[d]|`**: `|i_Y| ∘ |[d]_F| = |[d]| ∘ |i_X|`. -/
theorem orbitMap_faceIso (q : (faceEP X hX hθ).X.OrbitSpace) :
    (EpGroupoid.subEpFunctor (EpGroupoid.isEpSubgroupoid_faceObj
        (isEpFaceStructured_target hf hX) (isOrbitFace_target hf hθ hθ'))).orbitMap
        (orbitMap (faceIso hf hX hθ hθ') q) =
      orbitMap f
        ((EpGroupoid.subEpFunctor (EpGroupoid.isEpSubgroupoid_faceObj hX hθ)).orbitMap q) := by
  rw [faceIso, orbitMap_homMk, Diagram.orbitMap_restrictFace]
  conv_rhs => rw [← Quotient.out_eq f]
  rfl

/-- `|i_X| : |X_θ| → |X|` is injective (the face is a full subcategory). -/
theorem injective_orbitMap_subEpFunctor_face :
    Injective (EpGroupoid.subEpFunctor (EpGroupoid.isEpSubgroupoid_faceObj hX hθ)).orbitMap :=
  GroupoidFunctor.injective_orbitMap_of_full _ inferInstance

omit hf hθ' in
/-- The object set of the target face is `saturation(Ψ(B))`, `B = Φ⁻¹(X_θ)`, for every
representative `X ←Φ A →Ψ Y` of `f` (the face `C` of the text's proof). -/
theorem faceObj_target_eq {d : Diagram X Y} (hd : homMk d = f) (hθ' : faceMap f θ = θ') :
    Y.X.faceObj θ' = Y.X.saturation (d.Φ.obj '' d.A.X.faceObj (d.F.orbitMap ⁻¹' θ)) := by
  rw [EpFunctor.saturation_image_faceObj, ← hθ', ← hd, faceMap_homMk]

/-- **2021 Proposition 11.1.6, p. 524 (2017: Proposition 11.2, p. 378)**, the last claim: for a
generalized isomorphism `[d] : X → Y` of tame ep-groupoids with `X` face structured and a face
`X_θ`, `[d]` induces the generalized isomorphism `[d]_F : X_θ → Y_{[d]_*θ}`; it is the class of
the diagram (11.1) of restrictions `X_θ ← A_{|Φ|⁻¹θ} → Y_{[d]_*θ}` for every representative
`X ←Φ A →Ψ Y` (a natural class), the target face is `saturation(Ψ(Φ⁻¹(X_θ)))`, and
`|[d]_F|` is the restriction of `|[d]|`. -/
theorem proposition_11_1_6_faceIso :
    IsGeneralizedIso (faceIso hf hX hθ hθ') ∧
      (∀ (d : Diagram X Y) (hd : homMk d = f),
        homMk (d.restrictFace hX hθ (isEpFaceStructured_target hf hX)
          (isOrbitFace_target hf hθ hθ') (mem_iff_orbitMap_mem hf hθ' hd)) =
            faceIso hf hX hθ hθ' ∧
        Y.X.faceObj θ' = Y.X.saturation (d.Φ.obj '' d.A.X.faceObj (d.F.orbitMap ⁻¹' θ))) ∧
      ∀ q, (EpGroupoid.subEpFunctor (EpGroupoid.isEpSubgroupoid_faceObj
          (isEpFaceStructured_target hf hX) (isOrbitFace_target hf hθ hθ'))).orbitMap
          (orbitMap (faceIso hf hX hθ hθ') q) =
        orbitMap f
          ((EpGroupoid.subEpFunctor (EpGroupoid.isEpSubgroupoid_faceObj hX hθ)).orbitMap q) :=
  ⟨isGeneralizedIso_faceIso hf hX hθ hθ', fun _ hd =>
    ⟨homMk_restrictFace_eq_faceIso hf hX hθ hθ' hd, faceObj_target_eq hd hθ'⟩,
    orbitMap_faceIso hf hX hθ hθ'⟩

omit hθ' in
/-- **2021 Proposition 11.1.8, p. 526 (2017: Proposition 11.3, p. 380)**: if `f, g : X → Y` are
generalized isomorphisms, `X` is tame and face structured (then so is `Y`, Remark 11.1.7) and
`|f| = |g|`, then `f_* = g_*`, and for every face `X_θ` the generalized isomorphisms
`[f]_F, [g]_F : X_θ → Y_{f_*θ}` of (11.1) induce the same map of orbit spaces. -/
theorem proposition_11_1_8_faceIso {g : of X ⟶ of Y} (hg : IsGeneralizedIso g)
    (h : orbitMap f = orbitMap g) :
    faceMap f = faceMap g ∧
      orbitMap (faceIso hf hX hθ rfl) =
        orbitMap (faceIso hg hX hθ (show faceMap g θ = faceMap f θ by simp only [faceMap, h])) := by
  refine ⟨by funext θ; simp only [faceMap, h], funext fun q => ?_⟩
  refine injective_orbitMap_subEpFunctor_face (isEpFaceStructured_target hf hX)
    (isOrbitFace_target hf hθ rfl) ?_
  have h1 := orbitMap_faceIso hf hX hθ rfl q
  have h2 := orbitMap_faceIso hg hX hθ (show faceMap g θ = faceMap f θ by simp only [faceMap, h]) q
  exact h1.trans ((congrFun h _).trans h2.symm)

end EPLoc

end EPLocalization

end Polyfold
