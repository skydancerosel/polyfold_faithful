import Polyfold.Chapter17.TameBoundaryTransition
import Polyfold.Chapter17.SubpolyfoldStructure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.4 (pp. 800–801): **the natural M-polyfold structure on `M(Ψ_θ, Ψ'_{θ'})`**,
Definition 17.4.14, Lemma 17.4.15 and Theorem 17.4.16.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `GoodNbhd.faceSubPolyfold`: a face `θ` of a good neighbourhood with its structure as a
  sub-M-polyfold of `O` (Theorem 2.5.17).
* `inv_mem_transFaceSet_iff`, `exists_isOpen_inter_eq_tgt` (`M(Ψ, Ψ')*_{θ,θ'} = 𝒪' ∩ t⁻¹(θ')`),
  `mul_mem_transFaceSet`.
* **Definition 17.4.14**: `FTr` (`M(Ψ_θ, Ψ'_{θ'})` with its topology), `ftrHomeomorph`
  ((17.74) as a homeomorphism onto `M(Ψ, Ψ')*_{θ,θ'}`), `ftrPolyfold` (the natural M-polyfold
  structure), `ftr_isScDiffeoOn_homeomorph` ((17.74) is an sc-diffeomorphism).
* `faceTrToTr_inv`, `faceTrToTr_unit`, `faceTrToTr_comp`: (17.74) commutes with the structure maps.
* **Lemma 17.4.15**: `ftr_isLocalScDiffeo_src`, `ftr_isLocalScDiffeo_tgt`, `ftr_isScSmoothMap_inv`,
  `ftr_isScDiffeoOn_inv`, `ftr_isScSmoothMap_unit`, `ftr_isScSmoothMap_mul`, `lemma_17_4_15`.
* **Theorem 17.4.16**: `theorem_17_4_16`.
* `MPolyfold.isLocalScDiffeo_subPolyfold_of_inter`: a local sc-diffeomorphism restricts to the
  sub-M-polyfolds `B = O ∩ f⁻¹(A)`, `A` (`O` open).

## Readings

* The target of `s` is the face `θ` with its structure as a sub-M-polyfold of `O` (the M-polyfold
  of objects of `Ψ_θ`, p. 801); "uniquely determined" in Definition 17.4.14 is the transport of
  the sub-M-polyfold structure of `M(Ψ, Ψ')*_{θ,θ'}` along (17.74).
* The hypotheses (`S.IsTame`, `S.HasUniformizers`) are met by the quadrant polyfold
  (`quadrant_tameBoundaryUniformizer_witness`), where the unit at the corner lies in
  `M(Ψ, Ψ)*_{θ,θ}` for both faces `θ`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

universe u

namespace Polyfold

open TameBoundary

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- **A local sc-diffeomorphism restricts** to a local sc-diffeomorphism `B → A` between
sub-M-polyfolds when `B = O ∩ f⁻¹(A)` for an open `O` (`isLocalScDiffeo_subPolyfold_of_iff` is the
case `O = X`). -/
theorem isLocalScDiffeo_subPolyfold_of_inter {f : X → Y} (hf : P.IsLocalScDiffeo Q f)
    {A : Set Y} {B O : Set X} (hA : Q.IsSubMPolyfold A) (hB : P.IsSubMPolyfold B)
    [ParacompactSpace A] [ParacompactSpace B] (hO : IsOpen O) (hBO : B ⊆ O)
    (hBA : ∀ x ∈ O, x ∈ B ↔ f x ∈ A) {f' : B → A} (hf' : ∀ b, (f' b : Y) = f b) :
    (subPolyfold hB).IsLocalScDiffeo (subPolyfold hA) f' := by
  classical
  intro b
  obtain ⟨W₀, V₀, g, hbW₀, hd₀⟩ := hf b.1
  have hd := hd₀.restrict (hd₀.isOpen_source.inter hO) inter_subset_left
  set W := W₀ ∩ O
  set V := V₀ ∩ g ⁻¹' W
  have hbW : b.1 ∈ W := ⟨hbW₀, hBO b.2⟩
  have hgB : ∀ a : A, a.1 ∈ V → g a.1 ∈ B := fun a ha =>
    (hBA _ (hd.mapsTo_inv ha).2).2 (by rw [hd.right_inv _ ha]; exact a.2)
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

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {hT : S.IsTame} {hS : S.HasUniformizers}

namespace GoodNbhd

variable {Ψ Ψ' Ψ'' : S.Unif} {o : Ψ.1.O} {o' : Ψ'.1.O} {o'' : Ψ''.1.O} (V : S.GoodNbhd Ψ o)
  (V' : S.GoodNbhd Ψ' o') (V'' : S.GoodNbhd Ψ'' o'')

instance instParacompactFace (θ : Set Ψ.1.O) : ParacompactSpace θ :=
  Ψ.1.P.paracompactSpace_subtype θ

instance instParacompactTr (A : Set (S.Tr Ψ Ψ')) : ParacompactSpace A :=
  (S.transPolyfold Ψ Ψ').paracompactSpace_subtype A

variable (hT) in
/-- **The face `θ` as an M-polyfold**: its structure as a sub-M-polyfold of `O` (2021 Theorem
2.5.17). -/
def faceSubPolyfold {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) : MPolyfold θ :=
  MPolyfold.subPolyfold (V.isSubMPolyfold_face hT hθ)

/-- `a ∈ M(Ψ, Ψ')*_{θ,θ'}` iff its inverse lies in `M(Ψ', Ψ)*_{θ',θ}`. -/
theorem inv_mem_transFaceSet_iff {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) (a : S.Tr Ψ Ψ') :
    S.toTr (GroupoidStr.TransitionSet.inv a) ∈ V'.transFaceSet hT V hθ' hθ ↔
      a ∈ V.transFaceSet hT V' hθ hθ' := by
  constructor
  · rintro ⟨hx', hx, hl⟩
    refine ⟨hx, hx', ?_⟩
    convert germLift_inv hl using 1
    · exact (GroupoidStr.TransitionSet.inv_inv a).symm
    all_goals rfl
  · rintro ⟨hx, hx', hl⟩
    exact ⟨hx', hx, germLift_inv hl⟩

/-- `M(Ψ, Ψ')*_{θ,θ'} = 𝒪' ∩ t⁻¹(θ')` for an open `𝒪' ⊆ M(Ψ, Ψ')`. -/
theorem exists_isOpen_inter_eq_tgt {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) :
    ∃ 𝒪 : Set (S.Tr Ψ Ψ'), IsOpen 𝒪 ∧
      V.transFaceSet hT V' hθ hθ' = 𝒪 ∩ (fun b : S.Tr Ψ Ψ' => b.tgt) ⁻¹' θ' := by
  obtain ⟨𝒪, h𝒪, he⟩ := V'.exists_isOpen_inter_eq (hT := hT) V hθ' hθ
  have hc : Continuous fun a : S.Tr Ψ Ψ' => S.toTr (GroupoidStr.TransitionSet.inv a) :=
    continuousOn_univ.1 (S.isScSmoothMap_trInv Ψ Ψ').continuousOn
  refine ⟨_, h𝒪.preimage hc, ?_⟩
  ext a
  rw [← V.inv_mem_transFaceSet_iff V' hθ hθ', he]
  rfl

variable (hT hS) in
/-- **The transition M-polyfold `M(Ψ_θ, Ψ'_{θ'})`** (2021 Definition 17.4.14, p. 800): a type
synonym of the transition set carrying the topology and the M-polyfold structure of the
sub-M-polyfold `M(Ψ, Ψ')*_{θ,θ'}` of `M(Ψ, Ψ')`, transported along (17.74). -/
def FTr {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces) : Type u :=
  V.FaceTr hT hS V' hθ hθ'

instance {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces) :
    TopologicalSpace (V.FTr hT hS V' hθ hθ') :=
  TopologicalSpace.induced (V.faceTrEquiv (hT := hT) (hS := hS) V' hθ hθ') inferInstance

variable (hT hS) in
/-- (17.74): `M(Ψ_θ, Ψ'_{θ'}) ≃ₜ M(Ψ, Ψ')*_{θ,θ'}`. -/
def ftrHomeomorph {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces) :
    V.FTr hT hS V' hθ hθ' ≃ₜ V.transFaceSet hT V' hθ hθ' :=
  Equiv.toHomeomorphOfIsInducing
    (V.faceTrEquiv (hT := hT) (hS := hS) V' hθ hθ' :
      V.FTr hT hS V' hθ hθ' ≃ V.transFaceSet hT V' hθ hθ') ⟨rfl⟩

variable (hT hS) in
@[simp]
theorem ftrHomeomorph_apply {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) (h : V.FTr hT hS V' hθ hθ') :
    (V.ftrHomeomorph hT hS V' hθ hθ' h : S.Tr Ψ Ψ') = V.faceTrToTr V' h := rfl

instance {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces) :
    T2Space (V.FTr hT hS V' hθ hθ') :=
  (V.ftrHomeomorph hT hS V' hθ hθ').isEmbedding.t2Space

instance {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces) :
    ParacompactSpace (V.FTr hT hS V' hθ hθ') :=
  (V.ftrHomeomorph hT hS V' hθ hθ').isClosedEmbedding.paracompactSpace

variable (hT hS) in
/-- **2021 Definition 17.4.14, p. 800: the natural M-polyfold structure** on `M(Ψ_θ, Ψ'_{θ'})`,
the one for which (17.74) is an sc-diffeomorphism onto the sub-M-polyfold `M(Ψ, Ψ')*_{θ,θ'}`. -/
def ftrPolyfold {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces) :
    MPolyfold (V.FTr hT hS V' hθ hθ') :=
  (MPolyfold.subPolyfold (V.isSubMPolyfold_transFaceSet V' hθ hθ')).transport
    (V.ftrHomeomorph hT hS V' hθ hθ').symm

variable (hT hS) in
theorem ftr_isLocalScDiffeo_homeomorph {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) :
    (V.ftrPolyfold hT hS V' hθ hθ').IsLocalScDiffeo
      (MPolyfold.subPolyfold (V.isSubMPolyfold_transFaceSet V' hθ hθ'))
      (V.ftrHomeomorph hT hS V' hθ hθ') :=
  MPolyfold.isLocalScDiffeo_transport_symm _ (V.ftrHomeomorph hT hS V' hθ hθ').symm

variable (hT hS) in
theorem ftr_isScSmoothMap_homeomorph_symm {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) :
    (MPolyfold.subPolyfold (V.isSubMPolyfold_transFaceSet (hT := hT) V' hθ hθ')).IsScSmoothMap
      (V.ftrPolyfold hT hS V' hθ hθ') (V.ftrHomeomorph hT hS V' hθ hθ').symm :=
  MPolyfold.isScSmoothMap_transport _ (V.ftrHomeomorph hT hS V' hθ hθ').symm

variable (hT hS) in
/-- **(17.74) is an sc-diffeomorphism** onto the sub-M-polyfold `M(Ψ, Ψ')*_{θ,θ'}` (2021
Definition 17.4.14). -/
theorem ftr_isScDiffeoOn_homeomorph {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) :
    (V.ftrPolyfold hT hS V' hθ hθ').IsScDiffeoOn
      (MPolyfold.subPolyfold (V.isSubMPolyfold_transFaceSet V' hθ hθ'))
      (V.ftrHomeomorph hT hS V' hθ hθ') (V.ftrHomeomorph hT hS V' hθ hθ').symm univ univ :=
  (MPolyfold.isScDiffeoOn_transport _ (V.ftrHomeomorph hT hS V' hθ hθ').symm).symm

variable (hT hS) in
/-- **2021 Lemma 17.4.15 (source), p. 801**: `s : M(Ψ_θ, Ψ'_{θ'}) → θ` is a local
sc-diffeomorphism (`θ` with its structure as a sub-M-polyfold of `O`). -/
theorem ftr_isLocalScDiffeo_src {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) :
    (V.ftrPolyfold hT hS V' hθ hθ').IsLocalScDiffeo (V.faceSubPolyfold hT hθ)
      fun h : V.FTr hT hS V' hθ hθ' => h.src := by
  obtain ⟨𝒪, h𝒪, he⟩ := V.exists_isOpen_inter_eq (hT := hT) V' hθ hθ'
  have hBO : V.transFaceSet hT V' hθ hθ' ⊆ 𝒪 := by rw [he]; exact inter_subset_left
  have h1 := MPolyfold.isLocalScDiffeo_subPolyfold_of_inter (S.isLocalScDiffeo_trSrc Ψ Ψ')
    (V.isSubMPolyfold_face hT hθ) (V.isSubMPolyfold_transFaceSet V' hθ hθ') h𝒪 hBO
    (fun x hx => by rw [he]; exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩)
    (f' := fun b : V.transFaceSet hT V' hθ hθ' => (⟨b.1.src, b.2.1⟩ : θ)) fun _ => rfl
  exact h1.comp (V.ftr_isLocalScDiffeo_homeomorph hT hS V' hθ hθ')

variable (hT hS) in
/-- **2021 Lemma 17.4.15 (target), p. 801**: `t : M(Ψ_θ, Ψ'_{θ'}) → θ'` is a local
sc-diffeomorphism. -/
theorem ftr_isLocalScDiffeo_tgt {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) :
    (V.ftrPolyfold hT hS V' hθ hθ').IsLocalScDiffeo (V'.faceSubPolyfold hT hθ')
      fun h : V.FTr hT hS V' hθ hθ' => h.tgt := by
  obtain ⟨𝒪, h𝒪, he⟩ := V.exists_isOpen_inter_eq_tgt (hT := hT) V' hθ hθ'
  have hBO : V.transFaceSet hT V' hθ hθ' ⊆ 𝒪 := by rw [he]; exact inter_subset_left
  have h1 := MPolyfold.isLocalScDiffeo_subPolyfold_of_inter (S.isLocalScDiffeo_trTgt Ψ Ψ')
    (V'.isSubMPolyfold_face hT hθ') (V.isSubMPolyfold_transFaceSet V' hθ hθ') h𝒪 hBO
    (fun x hx => by rw [he]; exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩)
    (f' := fun b : V.transFaceSet hT V' hθ hθ' => (⟨b.1.tgt, b.2.2.1⟩ : θ')) fun _ => rfl
  exact h1.comp (V.ftr_isLocalScDiffeo_homeomorph hT hS V' hθ hθ')

/-- `h̄ ↦ h` commutes with inversion. -/
theorem faceTrToTr_inv {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} {hθ : θ ∈ V.faces}
    {hθ' : θ' ∈ V'.faces} (h : V.FaceTr hT hS V' hθ hθ') :
    V'.faceTrToTr V (GroupoidStr.TransitionSet.inv h) =
      S.toTr (GroupoidStr.TransitionSet.inv (V.faceTrToTr V' h)) := rfl

/-- `h̄ ↦ h` carries units to units. -/
theorem faceTrToTr_unit {θ : Set Ψ.1.O} {hθ : θ ∈ V.faces} (q : θ) :
    V.faceTrToTr V (hT := hT) (hS := hS) (hθ := hθ) (hθ' := hθ)
        (GroupoidStr.TransitionSet.unit q) =
      S.toTr (GroupoidStr.TransitionSet.unit q.1) := by
  refine GroupoidStr.TransitionSet.ext rfl ?_ rfl
  change C.toGroupoidStr.unit (V.faceObj hT hS hθ q.1 q.2).α = _
  rw [faceObj_α]
  rfl

/-- `h̄ ↦ h` carries composites to composites. -/
theorem faceTrToTr_comp {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} {θ'' : Set Ψ''.1.O}
    {hθ : θ ∈ V.faces} {hθ' : θ' ∈ V'.faces} {hθ'' : θ'' ∈ V''.faces}
    (a : V'.FaceTr hT hS V'' hθ' hθ'') (b : V.FaceTr hT hS V' hθ hθ') (hab : a.src = b.tgt) :
    V.faceTrToTr V'' (GroupoidStr.TransitionSet.mul ⟨(a, b), hab⟩) =
      S.toTr (GroupoidStr.TransitionSet.mul
        (⟨(V'.faceTrToTr V'' a, V.faceTrToTr V' b), by
          change a.src.1 = b.tgt.1; rw [hab]⟩ :
          MPolyfold.fibredProduct (fun a : S.Tr Ψ' Ψ'' => a.src)
            (fun a : S.Tr Ψ Ψ' => a.tgt))) := by
  refine GroupoidStr.TransitionSet.ext rfl ?_ rfl
  change (BMor.comp a.mor b.mor).mor = _
  rw [BMor.comp_of_eq (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt hab)]
  rfl

variable (hT hS) in
/-- **2021 Lemma 17.4.15 (inversion), p. 801**: `ι : M(Ψ_θ, Ψ'_{θ'}) → M(Ψ'_{θ'}, Ψ_θ)` is
sc-smooth. -/
theorem ftr_isScSmoothMap_inv {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) :
    (V.ftrPolyfold hT hS V' hθ hθ').IsScSmoothMap (V'.ftrPolyfold hT hS V hθ' hθ)
      fun h : V.FTr hT hS V' hθ hθ' =>
        (GroupoidStr.TransitionSet.inv h : V'.FTr hT hS V hθ' hθ) := by
  have hB := V.isSubMPolyfold_transFaceSet (hT := hT) V' hθ hθ'
  have hB' := V'.isSubMPolyfold_transFaceSet (hT := hT) V hθ' hθ
  have hi : (MPolyfold.subPolyfold hB).IsScSmoothMap (MPolyfold.subPolyfold hB')
      fun b : V.transFaceSet hT V' hθ hθ' =>
        (⟨S.toTr (GroupoidStr.TransitionSet.inv b.1),
          (V.inv_mem_transFaceSet_iff V' hθ hθ' b.1).2 b.2⟩ : V'.transFaceSet hT V hθ' hθ) :=
    MPolyfold.isScSmoothOn_subPolyfold_of_val hB'
      ((S.isScSmoothMap_trInv Ψ Ψ').comp (MPolyfold.subPolyfold_inclusion_isScSmooth hB))
  refine ((V'.ftr_isScSmoothMap_homeomorph_symm hT hS V hθ' hθ).comp
    (hi.comp (V.ftr_isLocalScDiffeo_homeomorph hT hS V' hθ hθ').isScSmoothMap)).congr
      fun h _ => ?_
  refine (Homeomorph.symm_apply_eq _).2 ?_
  exact Subtype.ext (V.faceTrToTr_inv V' h).symm

variable (hT hS) in
/-- **2021 Lemma 17.4.15, p. 801**: the inversion is an sc-diffeomorphism
`M(Ψ_θ, Ψ'_{θ'}) → M(Ψ'_{θ'}, Ψ_θ)`. -/
theorem ftr_isScDiffeoOn_inv {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) :
    (V.ftrPolyfold hT hS V' hθ hθ').IsScDiffeoOn (V'.ftrPolyfold hT hS V hθ' hθ)
      (fun h : V.FTr hT hS V' hθ hθ' =>
        (GroupoidStr.TransitionSet.inv h : V'.FTr hT hS V hθ' hθ))
      (fun h : V'.FTr hT hS V hθ' hθ =>
        (GroupoidStr.TransitionSet.inv h : V.FTr hT hS V' hθ hθ')) univ univ where
  isScSmoothOn := V.ftr_isScSmoothMap_inv hT hS V' hθ hθ'
  isScSmoothOn_inv := V'.ftr_isScSmoothMap_inv hT hS V hθ' hθ
  mapsTo := mapsTo_univ _ _
  mapsTo_inv := mapsTo_univ _ _
  left_inv h _ := GroupoidStr.TransitionSet.inv_inv h
  right_inv h _ := GroupoidStr.TransitionSet.inv_inv h

variable (hT hS) in
/-- **2021 Lemma 17.4.15 (unit), p. 801**: the unit map `θ → M(Ψ_θ, Ψ_θ)` is sc-smooth. -/
theorem ftr_isScSmoothMap_unit {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    (V.faceSubPolyfold hT hθ).IsScSmoothMap (V.ftrPolyfold hT hS V hθ hθ)
      fun q : θ => (GroupoidStr.TransitionSet.unit q : V.FTr hT hS V hθ hθ) := by
  have hB := V.isSubMPolyfold_transFaceSet (hT := hT) V hθ hθ
  have hu : (V.faceSubPolyfold hT hθ).IsScSmoothMap (MPolyfold.subPolyfold hB)
      fun q : θ => (⟨S.toTr (GroupoidStr.TransitionSet.unit q.1),
        q.2, q.2, germLift_unit (V.bMap_faceGerm hθ _ q.2)⟩ : V.transFaceSet hT V hθ hθ) :=
    MPolyfold.isScSmoothOn_subPolyfold_of_val hB
      ((S.isScSmoothMap_trUnit Ψ).comp
        (MPolyfold.subPolyfold_inclusion_isScSmooth (V.isSubMPolyfold_face hT hθ)))
  refine ((V.ftr_isScSmoothMap_homeomorph_symm hT hS V hθ hθ).comp hu).congr fun q _ => ?_
  refine (Homeomorph.symm_apply_eq _).2 ?_
  exact Subtype.ext (V.faceTrToTr_unit q).symm

/-- Composites of elements of `M(Ψ, Ψ')*_{θ,θ'}` and `M(Ψ', Ψ'')*_{θ',θ''}` lie in
`M(Ψ, Ψ'')*_{θ,θ''}`. -/
theorem mul_mem_transFaceSet {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} {θ'' : Set Ψ''.1.O}
    (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces) (hθ'' : θ'' ∈ V''.faces)
    (x : MPolyfold.fibredProduct (fun a : S.Tr Ψ' Ψ'' => a.src) (fun a : S.Tr Ψ Ψ' => a.tgt))
    (ha : x.1.1 ∈ V'.transFaceSet hT V'' hθ' hθ'') (hb : x.1.2 ∈ V.transFaceSet hT V' hθ hθ') :
    S.toTr (GroupoidStr.TransitionSet.mul x) ∈ V.transFaceSet hT V'' hθ hθ'' := by
  obtain ⟨hx₁, hx₁', hl₁⟩ := ha
  obtain ⟨hx₂, hx₂', hl₂⟩ := hb
  refine ⟨hx₂, hx₁', ?_⟩
  have hp : V'.faceGerm hT hθ' x.1.2.tgt hx₂' = V'.faceGerm hT hθ' x.1.1.src hx₁ :=
    V'.faceGerm_congr_pt hθ' x.2.symm _ _
  rw [hp] at hl₂
  exact germLift_comp (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt x.2) x.2 hl₂ hl₁

variable (hT hS) in
/-- **2021 Lemma 17.4.15 (multiplication), p. 801**: the multiplication
`M(Ψ'_{θ'}, Ψ''_{θ''}) ₛ×ₜ M(Ψ_θ, Ψ'_{θ'}) → M(Ψ_θ, Ψ''_{θ''})` is sc-smooth: it is the
multiplication of `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` composed with the inclusion of the fibred products. -/
theorem ftr_isScSmoothMap_mul {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} {θ'' : Set Ψ''.1.O}
    (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces) (hθ'' : θ'' ∈ V''.faces) :
    MPolyfold.IsScSmoothOnFibredProduct (V'.ftrPolyfold hT hS V'' hθ' hθ'')
      (V.ftrPolyfold hT hS V' hθ hθ') (V.ftrPolyfold hT hS V'' hθ hθ'')
      (V'.ftr_isLocalScDiffeo_src hT hS V'' hθ' hθ'')
      (V.ftr_isLocalScDiffeo_tgt hT hS V' hθ hθ').isScSmoothMap
      fun x => (GroupoidStr.TransitionSet.mul x : V.FTr hT hS V'' hθ hθ'') := by
  let P₁ := V'.ftrPolyfold hT hS V'' hθ' hθ''
  let P₂ := V.ftrPolyfold hT hS V' hθ hθ'
  let _ := MPolyfold.paracompactSpace_prod P₁ P₂
  let _ := (P₁.prod P₂).paracompactSpace_subtype
    (MPolyfold.fibredProduct (fun a : V'.FTr hT hS V'' hθ' hθ'' => a.src)
      (fun a : V.FTr hT hS V' hθ hθ' => a.tgt))
  let _ := MPolyfold.paracompactSpace_prod (S.transPolyfold Ψ' Ψ'') (S.transPolyfold Ψ Ψ')
  let _ := ((S.transPolyfold Ψ' Ψ'').prod (S.transPolyfold Ψ Ψ')).paracompactSpace_subtype
    (MPolyfold.fibredProduct (fun a : S.Tr Ψ' Ψ'' => a.src) (fun a : S.Tr Ψ Ψ' => a.tgt))
  have hF := MPolyfold.isSubMPolyfold_fibredProduct (S.isLocalScDiffeo_trSrc Ψ' Ψ'')
    (S.isLocalScDiffeo_trTgt Ψ Ψ').isScSmoothMap
  have hF' := MPolyfold.isSubMPolyfold_fibredProduct
    (V'.ftr_isLocalScDiffeo_src hT hS V'' hθ' hθ'')
    (V.ftr_isLocalScDiffeo_tgt hT hS V' hθ hθ').isScSmoothMap
  have hm : (MPolyfold.subPolyfold hF).IsScSmoothMap (S.transPolyfold Ψ Ψ'')
      fun x => S.toTr (GroupoidStr.TransitionSet.mul x) := S.isScSmoothMap_trMul Ψ Ψ' Ψ''
  have hB₁ := V'.isSubMPolyfold_transFaceSet (hT := hT) V'' hθ' hθ''
  have hB₂ := V.isSubMPolyfold_transFaceSet (hT := hT) V' hθ hθ'
  have hB₃ := V.isSubMPolyfold_transFaceSet (hT := hT) V'' hθ hθ''
  let e₁ := V'.ftrHomeomorph hT hS V'' hθ' hθ''
  let e₂ := V.ftrHomeomorph hT hS V' hθ hθ'
  let j : MPolyfold.fibredProduct (fun a : V'.FTr hT hS V'' hθ' hθ'' => a.src)
      (fun a : V.FTr hT hS V' hθ hθ' => a.tgt) →
      MPolyfold.fibredProduct (fun a : S.Tr Ψ' Ψ'' => a.src) (fun a : S.Tr Ψ Ψ' => a.tgt) :=
    fun x => ⟨((e₁ x.1.1).1, (e₂ x.1.2).1), congrArg Subtype.val x.2⟩
  have hi := MPolyfold.subPolyfold_inclusion_isScSmooth hF'
  have h1 : (MPolyfold.subPolyfold hF').IsScSmoothMap (S.transPolyfold Ψ' Ψ'')
      fun x => (e₁ x.1.1).1 :=
    (MPolyfold.subPolyfold_inclusion_isScSmooth hB₁).comp
      ((V'.ftr_isLocalScDiffeo_homeomorph hT hS V'' hθ' hθ'').isScSmoothMap.comp
        ((MPolyfold.isScSmoothMap_fst P₁ P₂).comp hi))
  have h2 : (MPolyfold.subPolyfold hF').IsScSmoothMap (S.transPolyfold Ψ Ψ')
      fun x => (e₂ x.1.2).1 :=
    (MPolyfold.subPolyfold_inclusion_isScSmooth hB₂).comp
      ((V.ftr_isLocalScDiffeo_homeomorph hT hS V' hθ hθ').isScSmoothMap.comp
        ((MPolyfold.isScSmoothMap_snd P₁ P₂).comp hi))
  have hj : (MPolyfold.subPolyfold hF').IsScSmoothMap (MPolyfold.subPolyfold hF) j :=
    MPolyfold.isScSmoothOn_subPolyfold_of_val hF (MPolyfold.IsScSmoothOn.prodMk h1 h2)
  let mB : MPolyfold.fibredProduct (fun a : V'.FTr hT hS V'' hθ' hθ'' => a.src)
      (fun a : V.FTr hT hS V' hθ hθ' => a.tgt) → V.transFaceSet hT V'' hθ hθ'' :=
    fun x => ⟨S.toTr (GroupoidStr.TransitionSet.mul (j x)),
      V.mul_mem_transFaceSet V' V'' hθ hθ' hθ'' (j x) (e₁ x.1.1).2 (e₂ x.1.2).2⟩
  have hmB : (MPolyfold.subPolyfold hF').IsScSmoothMap (MPolyfold.subPolyfold hB₃) mB :=
    MPolyfold.isScSmoothOn_subPolyfold_of_val hB₃ (hm.comp hj)
  change (MPolyfold.subPolyfold hF').IsScSmoothMap (V.ftrPolyfold hT hS V'' hθ hθ'') _
  refine ((V.ftr_isScSmoothMap_homeomorph_symm hT hS V'' hθ hθ'').comp hmB).congr
    fun x _ => ?_
  refine (Homeomorph.symm_apply_eq _).2 ?_
  refine Subtype.ext ?_
  change _ = V.faceTrToTr V'' (GroupoidStr.TransitionSet.mul ⟨(x.1.1, x.1.2), x.2⟩)
  rw [V.faceTrToTr_comp V' V'' x.1.1 x.1.2 x.2]
  rfl

variable (hT hS) in
/-- **2021 Lemma 17.4.15, p. 801**: for the natural M-polyfold structures, `s` and `t` are local
sc-diffeomorphisms onto the faces `θ`, `θ'`, the inversion is an sc-diffeomorphism and the unit
and the multiplication are sc-smooth. -/
theorem lemma_17_4_15 {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} {θ'' : Set Ψ''.1.O}
    (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces) (hθ'' : θ'' ∈ V''.faces) :
    (V.ftrPolyfold hT hS V' hθ hθ').IsLocalScDiffeo (V.faceSubPolyfold hT hθ)
        (fun h : V.FTr hT hS V' hθ hθ' => h.src) ∧
    (V.ftrPolyfold hT hS V' hθ hθ').IsLocalScDiffeo (V'.faceSubPolyfold hT hθ')
        (fun h : V.FTr hT hS V' hθ hθ' => h.tgt) ∧
    (V.ftrPolyfold hT hS V' hθ hθ').IsScDiffeoOn (V'.ftrPolyfold hT hS V hθ' hθ)
      (fun h : V.FTr hT hS V' hθ hθ' =>
        (GroupoidStr.TransitionSet.inv h : V'.FTr hT hS V hθ' hθ))
      (fun h : V'.FTr hT hS V hθ' hθ =>
        (GroupoidStr.TransitionSet.inv h : V.FTr hT hS V' hθ hθ')) univ univ ∧
    (V.faceSubPolyfold hT hθ).IsScSmoothMap (V.ftrPolyfold hT hS V hθ hθ)
      (fun q : θ => (GroupoidStr.TransitionSet.unit q : V.FTr hT hS V hθ hθ)) ∧
    MPolyfold.IsScSmoothOnFibredProduct (V'.ftrPolyfold hT hS V'' hθ' hθ'')
      (V.ftrPolyfold hT hS V' hθ hθ') (V.ftrPolyfold hT hS V'' hθ hθ'')
      (V'.ftr_isLocalScDiffeo_src hT hS V'' hθ' hθ'')
      (V.ftr_isLocalScDiffeo_tgt hT hS V' hθ hθ').isScSmoothMap
      (fun x => (GroupoidStr.TransitionSet.mul x : V.FTr hT hS V'' hθ hθ'')) :=
  ⟨V.ftr_isLocalScDiffeo_src hT hS V' hθ hθ', V.ftr_isLocalScDiffeo_tgt hT hS V' hθ hθ',
    V.ftr_isScDiffeoOn_inv hT hS V' hθ hθ', V.ftr_isScSmoothMap_unit hT hS hθ,
    V.ftr_isScSmoothMap_mul hT hS V' V'' hθ hθ' hθ''⟩

end GoodNbhd

variable (hT hS) in
/-- **2021 Theorem 17.4.16, p. 801**: for the natural M-polyfold structures on all
`M(Ψ_θ, Ψ'_{θ'})` (any `Ψ, Ψ'`, good neighbourhoods and faces), all structure maps are sc-smooth and
the source and target maps are local sc-diffeomorphisms. -/
theorem theorem_17_4_16 :
    ∀ {Ψ Ψ' Ψ'' : S.Unif} {o : Ψ.1.O} {o' : Ψ'.1.O} {o'' : Ψ''.1.O} (V : S.GoodNbhd Ψ o)
      (V' : S.GoodNbhd Ψ' o') (V'' : S.GoodNbhd Ψ'' o'') {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O}
      {θ'' : Set Ψ''.1.O} (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces) (hθ'' : θ'' ∈ V''.faces),
    (V.ftrPolyfold hT hS V' hθ hθ').IsLocalScDiffeo (V.faceSubPolyfold hT hθ)
        (fun h : V.FTr hT hS V' hθ hθ' => h.src) ∧
    (V.ftrPolyfold hT hS V' hθ hθ').IsLocalScDiffeo (V'.faceSubPolyfold hT hθ')
        (fun h : V.FTr hT hS V' hθ hθ' => h.tgt) ∧
    (V.ftrPolyfold hT hS V' hθ hθ').IsScSmoothMap (V'.ftrPolyfold hT hS V hθ' hθ)
      (fun h : V.FTr hT hS V' hθ hθ' =>
        (GroupoidStr.TransitionSet.inv h : V'.FTr hT hS V hθ' hθ)) ∧
    (V.faceSubPolyfold hT hθ).IsScSmoothMap (V.ftrPolyfold hT hS V hθ hθ)
      (fun q : θ => (GroupoidStr.TransitionSet.unit q : V.FTr hT hS V hθ hθ)) ∧
    MPolyfold.IsScSmoothOnFibredProduct (V'.ftrPolyfold hT hS V'' hθ' hθ'')
      (V.ftrPolyfold hT hS V' hθ hθ') (V.ftrPolyfold hT hS V'' hθ hθ'')
      (V'.ftr_isLocalScDiffeo_src hT hS V'' hθ' hθ'')
      (V.ftr_isLocalScDiffeo_tgt hT hS V' hθ hθ').isScSmoothMap
      (fun x => (GroupoidStr.TransitionSet.mul x : V.FTr hT hS V'' hθ hθ'')) :=
  fun V V' V'' _ _ _ hθ hθ' hθ'' =>
    ⟨V.ftr_isLocalScDiffeo_src hT hS V' hθ hθ', V.ftr_isLocalScDiffeo_tgt hT hS V' hθ hθ',
      V.ftr_isScSmoothMap_inv hT hS V' hθ hθ', V.ftr_isScSmoothMap_unit hT hS hθ,
      V.ftr_isScSmoothMap_mul hT hS V' V'' hθ hθ' hθ''⟩

end GCT.PolyfoldConstruction

end Polyfold
