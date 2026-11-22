import Polyfold.Chapter17.TameBoundaryPolyfold
import Polyfold.Chapter2.TameFaces
import Polyfold.Chapter7.LocalDiffeo

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.4 (pp. 798–811): the tameness assertions of **Lemma 17.4.13** in the form of
**Definition 2.5.18** (the induced structure on `M(Ψ, Ψ')*_{θ,θ'}` is tame), hence the tameness
of the M-polyfolds `θ`, `M(Ψ_θ, Ψ'_{θ'})` of **Theorem 17.4.26** ("the tame M-polyfolds above",
p. 811): the tame boundary `bC` is a tame polyfold.  Numbers and pages are the 2021 text's.

## The text, paraphrased

(p. 798, Lemma 17.4.13) `M(Ψ, Ψ')*_{θ,θ'}` is a tame sub-M-polyfold of `M(Ψ, Ψ')`; (proof,
pp. 799–800) near `h₀` the retraction `R = (s|W(h₀))⁻¹ ∘ r ∘ s` onto `M(Ψ, Ψ')*_{θ,θ'}` is built
from the tame retraction `r` onto the face `θ` of the tame `V(ō)`.  (p. 801) `M(Ψ_θ, Ψ'_{θ'})`
carries the structure making (17.74) an sc-diffeomorphism.  (pp. 809–811) The faces `θ`,
`M(Ψ_θ, Ψ'_{θ'})` are "the tame M-polyfolds above".

## What is formalized

* General facts on Definition 2.5.18 (namespace `MPolyfold`):
  `HasTameInducedStructure.inter_isOpen_of_isSubMPolyfold` (open pieces),
  `hasTameInducedStructure_of_local` (tameness of the induced structure is local),
  `HasTameInducedStructure.image_of_isScDiffeoOn_of_isSubMPolyfold` (images under
  sc-diffeomorphisms), `hasTameInducedStructure_of_isFaceIn` (a face of a face-structured open
  subset of a tame M-polyfold has a tame induced structure: Theorem 2.5.17 on the open set).
* `GoodNbhd.hasTameInducedStructure_face`, `GoodNbhd.isTame_faceSubPolyfold`: the faces `θ` of
  `U(ō)`, with their structure as sub-M-polyfolds of `O`, are tame.
* **`GoodNbhd.hasTameInducedStructure_transFaceSet`**: the induced structure on
  `M(Ψ, Ψ')*_{θ,θ'}` is tame (Definition 2.5.18): near every element, `s` carries it onto an open
  piece of the face `θ` (the sheets of `exists_sheet_transFaceSet`, the map `R` of (17.73)).
  **`GoodNbhd.lemma_17_4_13`**: Lemma 17.4.13 as we read it, this tameness together with the
  assertions of `lemma_17_4_13_subMPolyfold` (`TameBoundaryTransition.lean`).
* `GoodNbhd.isTame_ftrPolyfold`: `M(Ψ_θ, Ψ'_{θ'})` (Definition 17.4.14) is a tame M-polyfold.
* **`bdryConstruction_isTame`**, **`theorem_17_4_26_tame`**: the polyfold structure
  `(F_bC, M)` of Theorem 17.4.26 is tame (every `Ψ_θ ∈ F_bC` has a tame object M-polyfold, and
  every transition M-polyfold `M(L, L')` is tame).

## Readings

* We read the faces in Lemma 17.4.13 in the sense of Definition 2.5.18, the sense the book gives
  faces in Proposition 2.5.15 – Theorem 2.5.17: the tameness asserted is that of the induced
  structure, which is what the construction of `M(Ψ_θ, Ψ'_{θ'})` and of `bC` uses.  With the
  pointer to Definition 2.5.19 taken literally ((2) for `d_{M(Ψ,Ψ')}`), no face qualifies
  (`lemma_17_4_13_literal`, `TameBoundaryTransition.lean`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

universe u

namespace Polyfold

open TameBoundary

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **An open piece of a sub-M-polyfold with a tame induced structure has a tame induced
structure** (2021 Definition 2.5.18): the inclusion `N ∩ V → N` is an sc-diffeomorphism onto an
open subset of `N`. -/
theorem HasTameInducedStructure.inter_isOpen_of_isSubMPolyfold {N V : Set X}
    (ht : P.HasTameInducedStructure N) (hV : IsOpen V) : P.HasTameInducedStructure (N ∩ V) := by
  classical
  obtain ⟨hY, htame⟩ := ht
  have hY' : P.IsSubMPolyfold (N ∩ V) := hY.inter_isOpen hV
  let _ := P.paracompactSpace_subtype N
  let _ := P.paracompactSpace_subtype (N ∩ V)
  refine ⟨hY', isTame_of_forall_exists_chart _ fun x => ?_⟩
  let j : ↥(N ∩ V) → ↥N := fun y => ⟨y.1, y.2.1⟩
  let g : ↥N → ↥(N ∩ V) := fun y => if h : y.1 ∈ V then ⟨y.1, y.2, h⟩ else x
  let W : Set ↥N := {y | y.1 ∈ V}
  have hW : IsOpen W := hV.preimage continuous_subtype_val
  have hg : ∀ y ∈ W, ((g y : ↥(N ∩ V)) : X) = y.1 := fun y hy => by
    simp only [g, dif_pos (show y.1 ∈ V from hy)]
  have hj : (subPolyfold hY').IsScSmoothOn (subPolyfold hY) j univ :=
    isScSmoothOn_subPolyfold_of_val hY (f := j) (subPolyfold_inclusion_isScSmooth hY')
  have hgs : (subPolyfold hY).IsScSmoothOn (subPolyfold hY') g W :=
    isScSmoothOn_subPolyfold_of_val hY' (f := g)
      (((subPolyfold_inclusion_isScSmooth hY).mono hW (subset_univ W)).congr
        fun y hy => (hg y hy).symm)
  have hd : (subPolyfold hY').IsScDiffeoOn (subPolyfold hY) j g univ W :=
    { isScSmoothOn := hj
      isScSmoothOn_inv := hgs
      mapsTo := fun y _ => y.2.2
      mapsTo_inv := fun _ _ => mem_univ _
      left_inv := fun y _ => Subtype.ext (hg (j y) y.2.2)
      right_inv := fun y hy => Subtype.ext (hg y hy) }
  exact hd.exists_tame_chart htame (mem_univ x)

/-- **Tameness of the induced structure is local** (2021 Definition 2.5.18): a sub-M-polyfold `Y`
such that every point has an open neighbourhood `W` with `Y ∩ W` of tame induced structure has a
tame induced structure (the tame charts of `Y ∩ W` are charts of `Y`). -/
theorem hasTameInducedStructure_of_local {Y : Set X} (hY : P.IsSubMPolyfold Y)
    (h : ∀ y ∈ Y, ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ P.HasTameInducedStructure (Y ∩ W)) :
    P.HasTameInducedStructure Y := by
  classical
  let _ := P.paracompactSpace_subtype Y
  refine ⟨hY, isTame_of_forall_exists_chart _ fun x => ?_⟩
  obtain ⟨W, hWo, hxW, hY', htame⟩ := h x.1 x.2
  let _ := P.paracompactSpace_subtype (Y ∩ W)
  let x' : ↥(Y ∩ W) := ⟨x.1, x.2, hxW⟩
  let j : ↥(Y ∩ W) → ↥Y := fun y => ⟨y.1, y.2.1⟩
  let g : ↥Y → ↥(Y ∩ W) := fun y => if h : y.1 ∈ W then ⟨y.1, y.2, h⟩ else x'
  let W' : Set ↥Y := {y | y.1 ∈ W}
  have hW : IsOpen W' := hWo.preimage continuous_subtype_val
  have hg : ∀ y ∈ W', ((g y : ↥(Y ∩ W)) : X) = y.1 := fun y hy => by
    simp only [g, dif_pos (show y.1 ∈ W from hy)]
  have hj : (subPolyfold hY').IsScSmoothOn (subPolyfold hY) j univ :=
    isScSmoothOn_subPolyfold_of_val hY (f := j) (subPolyfold_inclusion_isScSmooth hY')
  have hgs : (subPolyfold hY).IsScSmoothOn (subPolyfold hY') g W' :=
    isScSmoothOn_subPolyfold_of_val hY' (f := g)
      (((subPolyfold_inclusion_isScSmooth hY).mono hW (subset_univ W')).congr
        fun y hy => (hg y hy).symm)
  have hd : (subPolyfold hY').IsScDiffeoOn (subPolyfold hY) j g univ W' :=
    { isScSmoothOn := hj
      isScSmoothOn_inv := hgs
      mapsTo := fun y _ => y.2.2
      mapsTo_inv := fun _ _ => mem_univ _
      left_inv := fun y _ => Subtype.ext (hg (j y) y.2.2)
      right_inv := fun y hy => Subtype.ext (hg y hy) }
  exact hd.symm.exists_tame_chart htame (show x.1 ∈ W from hxW)

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- **The image of a set with a tame induced structure under an sc-diffeomorphism has a tame
induced structure** (2021 Definition 2.5.18), when the image is a sub-M-polyfold: `f` and `g`
restrict to an sc-diffeomorphism `f(N) → N`, and tame charts are carried along. -/
theorem HasTameInducedStructure.image_of_isScDiffeoOn_of_isSubMPolyfold {N : Set X}
    (ht : P.HasTameInducedStructure N) {f : X → Y} {g : Y → X} {U : Set X} {U' : Set Y}
    (hf : P.IsScDiffeoOn Q f g U U') (hNU : N ⊆ U) (hY' : Q.IsSubMPolyfold (f '' N)) :
    Q.HasTameInducedStructure (f '' N) := by
  classical
  obtain ⟨hY, htame⟩ := ht
  let _ := P.paracompactSpace_subtype N
  let _ := Q.paracompactSpace_subtype (f '' N)
  refine ⟨hY', isTame_of_forall_exists_chart _ fun x => ?_⟩
  have hgN : ∀ z ∈ f '' N, g z ∈ N := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hf.left_inv y (hNU hy)]; exact hy
  let k : ↥(f '' N) → ↥N := fun z => ⟨g z.1, hgN z.1 z.2⟩
  let j : ↥N → ↥(f '' N) := fun y => ⟨f y.1, mem_image_of_mem f y.2⟩
  have hk : (subPolyfold hY').IsScSmoothOn (subPolyfold hY) k univ :=
    isScSmoothOn_subPolyfold_of_val hY (f := k)
      (hf.isScSmoothOn_inv.comp (subPolyfold_inclusion_isScSmooth hY')
        fun z _ => image_subset_iff.2 (fun y hy => hf.mapsTo (hNU hy)) z.2)
  have hj : (subPolyfold hY).IsScSmoothOn (subPolyfold hY') j univ :=
    isScSmoothOn_subPolyfold_of_val hY' (f := j)
      (hf.isScSmoothOn.comp (subPolyfold_inclusion_isScSmooth hY) fun y _ => hNU y.2)
  have hd : (subPolyfold hY').IsScDiffeoOn (subPolyfold hY) k j univ univ :=
    { isScSmoothOn := hk
      isScSmoothOn_inv := hj
      mapsTo := fun _ _ => mem_univ _
      mapsTo_inv := fun _ _ => mem_univ _
      left_inv := fun z _ => Subtype.ext (by
        obtain ⟨_, y, hy, rfl⟩ := z
        exact congrArg f (hf.left_inv y (hNU hy)))
      right_inv := fun y _ => Subtype.ext (hf.left_inv y.1 (hNU y.2)) }
  exact hd.exists_tame_chart htame (mem_univ x)

/-- **A face of a face-structured open subset of a tame M-polyfold has a tame induced
structure** (2021 Definition 2.5.18; Theorem 2.5.17 applied to the tame, face-structured
M-polyfold `V`, Proposition 2.5.15). -/
theorem hasTameInducedStructure_of_isFaceIn (hP : P.IsTame) {V θ : Set X}
    (hV : IsFaceStructuredOpen P.degIndex V) (hθ : IsFaceIn P.degIndex V θ) :
    P.HasTameInducedStructure θ := by
  have hVo : IsOpen V := hV.1
  obtain ⟨p, hpV, -⟩ := id hθ
  have : Nonempty V := ⟨⟨p, hpV⟩⟩
  let _ : ParacompactSpace V := P.paracompactSpace_subtype V
  have hfs : (P.restrictOpen hVo).IsFaceStructured :=
    (isFaceStructured_iff_univ _).2 (isFaceStructuredOpen_restrictOpen P hVo hV)
  have h' : IsFaceIn P.degIndex (Subtype.val '' (univ : Set V)) θ := by
    rw [image_univ, Subtype.range_coe]; exact hθ
  obtain ⟨γ, hγ, hγe⟩ := (isDHomeoOn_subtypeVal P hVo).exists_isFaceIn_of_image subset_rfl h'
  have hF : (P.restrictOpen hVo).IsFace γ := (isFace_iff_isFaceIn_univ _).2 hγ
  have : ParacompactSpace γ := paracompactSpace_of_isClosed (IsFace.isClosed _ hF)
  have htame := (theorem_2_5_17_isTame_face _ (isTame_restrictOpen P hVo hP) hfs hF).1
  have ht : (P.restrictOpen hVo).HasTameInducedStructure γ := ⟨_, htame⟩
  rw [← hγe]
  refine ht.image_of_isScDiffeoOn_of_isSubMPolyfold (isScDiffeoOn_subtypeVal hVo)
    (subset_univ _) ?_
  rw [hγe]
  exact P.isSubMPolyfold_of_isFaceIn hP hV hθ

end MPolyfold

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {hT : S.IsTame} {hS : S.HasUniformizers}

namespace GoodNbhd

variable {Ψ Ψ' : S.Unif} {o : Ψ.1.O} {o' : Ψ'.1.O} (V : S.GoodNbhd Ψ o) (V' : S.GoodNbhd Ψ' o')

/-- **The faces `θ` of `U(ō)` have a tame induced structure** (2021 Definition 2.5.18): `θ` is a
face of the face-structured open set `V(ō)` of the tame `O` (Theorem 2.5.17). -/
theorem hasTameInducedStructure_face (hT : S.IsTame) {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    Ψ.1.P.HasTameInducedStructure θ :=
  MPolyfold.hasTameInducedStructure_of_isFaceIn (S.isTame_unif hT Ψ) V.isFaceStructuredOpen hθ

variable (hT) in
/-- **The face `θ` with its structure as a sub-M-polyfold of `O` is a tame M-polyfold** (the
object M-polyfold of `Ψ_θ`, Lemma 17.4.6). -/
theorem isTame_faceSubPolyfold {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    (V.faceSubPolyfold hT hθ).IsTame := by
  obtain ⟨_, h⟩ := V.hasTameInducedStructure_face hT hθ
  exact h

/-- **The induced structure on `M(Ψ, Ψ')*_{θ,θ'}` is tame** (Lemma 17.4.13 with
Definition 2.5.18): near every element `a`, `s` is an sc-diffeomorphism `U → N` carrying
`U ∩ M(Ψ, Ψ')*_{θ,θ'}` onto `N ∩ θ` (the map `R` of (17.73)), and `N ∩ θ` has a tame induced
structure. -/
theorem hasTameInducedStructure_transFaceSet {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O}
    (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces) :
    (S.transPolyfold Ψ Ψ').HasTameInducedStructure (V.transFaceSet hT V' hθ hθ') := by
  refine MPolyfold.hasTameInducedStructure_of_local (V.isSubMPolyfold_transFaceSet V' hθ hθ')
    fun a ha => ?_
  obtain ⟨U, N, g, haU, hd, himg⟩ := V.exists_sheet_transFaceSet V' hθ hθ' ha
  refine ⟨U, hd.isScSmoothOn.isOpen, haU, ?_⟩
  have he : V.transFaceSet hT V' hθ hθ' ∩ U = g '' (N ∩ θ) := by
    rw [← himg]
    ext b
    constructor
    · rintro ⟨hb, hbU⟩
      exact ⟨b.src, ⟨b, ⟨hbU, hb⟩, rfl⟩, hd.left_inv b hbU⟩
    · rintro ⟨_, ⟨b, ⟨hbU, hb⟩, rfl⟩, rfl⟩
      change g b.src ∈ _
      rw [hd.left_inv b hbU]
      exact ⟨hb, hbU⟩
  rw [he]
  have hNθ : Ψ.1.P.HasTameInducedStructure (N ∩ θ) := by
    rw [inter_comm]
    exact (V.hasTameInducedStructure_face hT hθ).inter_isOpen_of_isSubMPolyfold
      hd.isScSmoothOn_inv.isOpen
  refine hNθ.image_of_isScDiffeoOn_of_isSubMPolyfold hd.symm inter_subset_left ?_
  rw [← he]
  exact (V.isSubMPolyfold_transFaceSet V' hθ hθ').inter_isOpen hd.isScSmoothOn.isOpen

/-- **2021 Lemma 17.4.13, p. 798**, as we read it, with the faces in the sense of Definition
2.5.18 (Proposition 2.5.15 – Theorem 2.5.17): the induced structure on `M(Ψ, Ψ')*_{θ,θ'}` is tame
(Definition 2.5.18), as is that of the face `θ`; `M(Ψ, Ψ')*_{θ,θ'}` is a sub-M-polyfold of
`M(Ψ, Ψ')`, the open part `𝒪 ∩ s⁻¹(θ)` of the preimage of `θ`; near every element `s` is an
sc-diffeomorphism `U → N` carrying `U ∩ M(Ψ, Ψ')*_{θ,θ'}` onto `N ∩ θ` (the retraction
`R = (s|W(h₀))⁻¹ ∘ r ∘ s` of (17.73)); `d_{M(Ψ, Ψ')} = d_O ∘ s ≥ 1` on it; and (17.71)
`(x, Φ, x') ↦ (x, φ, x')` is a bijection `M(Ψ_θ, Ψ'_{θ'}) → M(Ψ, Ψ')*_{θ,θ'}`.  With the pointer to
Definition 2.5.19 taken literally, no face qualifies (`lemma_17_4_13_literal`). -/
theorem lemma_17_4_13 {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) :
    (S.transPolyfold Ψ Ψ').HasTameInducedStructure (V.transFaceSet hT V' hθ hθ') ∧
    Ψ.1.P.HasTameInducedStructure θ ∧
    (S.transPolyfold Ψ Ψ').IsSubMPolyfold (V.transFaceSet hT V' hθ hθ') ∧
    (∃ 𝒪 : Set (S.Tr Ψ Ψ'), IsOpen 𝒪 ∧
      V.transFaceSet hT V' hθ hθ' = 𝒪 ∩ (fun b : S.Tr Ψ Ψ' => b.src) ⁻¹' θ) ∧
    (∀ a ∈ V.transFaceSet hT V' hθ hθ', ∃ (U : Set (S.Tr Ψ Ψ')) (N : Set Ψ.1.O)
      (g : Ψ.1.O → S.Tr Ψ Ψ'), a ∈ U ∧
      (S.transPolyfold Ψ Ψ').IsScDiffeoOn Ψ.1.P (fun b : S.Tr Ψ Ψ' => b.src) g U N ∧
      (fun b : S.Tr Ψ Ψ' => b.src) '' (U ∩ V.transFaceSet hT V' hθ hθ') = N ∩ θ) ∧
    (∀ a ∈ V.transFaceSet hT V' hθ hθ',
      (S.transPolyfold Ψ Ψ').degIndex a = Ψ.1.P.degIndex a.src ∧
        1 ≤ (S.transPolyfold Ψ Ψ').degIndex a) ∧
    Injective (V.faceTrToTr V' (hT := hT) (hS := hS) (hθ := hθ) (hθ' := hθ')) ∧
    range (V.faceTrToTr V' (hT := hT) (hS := hS) (hθ := hθ) (hθ' := hθ')) =
      V.transFaceSet hT V' hθ hθ' :=
  ⟨V.hasTameInducedStructure_transFaceSet V' hθ hθ', V.hasTameInducedStructure_face hT hθ,
    V.lemma_17_4_13_subMPolyfold V' hθ hθ'⟩

variable (hT hS) in
/-- **`M(Ψ_θ, Ψ'_{θ'})` is a tame M-polyfold** (Definition 17.4.14: the structure making (17.74)
an sc-diffeomorphism onto `M(Ψ, Ψ')*_{θ,θ'}`, whose induced structure is tame). -/
theorem isTame_ftrPolyfold {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) : (V.ftrPolyfold hT hS V' hθ hθ').IsTame := by
  obtain ⟨_, h⟩ := V.hasTameInducedStructure_transFaceSet V' hθ hθ'
  exact (V.ftr_isLocalScDiffeo_homeomorph hT hS V' hθ hθ').isTame h

end GoodNbhd

section Construction

variable (hc : S.HatContinuous) (hcent : S.IsCentred)

variable (hT hS) in
/-- **The tame boundary `bC` is a tame polyfold**: every `Ψ_θ ∈ F_bC` has the tame object
M-polyfold `θ` (Definition 17.1.5's tameness for `(F_bC, M)` of Theorem 17.4.26). -/
theorem bdryConstruction_isTame : (S.bdryConstruction hT hS hc hcent).IsTame := by
  rintro ᾱ L ⟨d, -, -, rfl⟩
  exact d.V.isTame_faceSubPolyfold hT d.hθ

variable (hT hS) in
/-- **Theorem 17.4.26 with tameness** (2021 p. 809; "the tame M-polyfolds above", p. 811): the
polyfold structure `(F_bC, M)` on the tame boundary `bC` is tame, and every transition
M-polyfold `M(L, L')` of it is tame. -/
theorem theorem_17_4_26_tame :
    (S.bdryConstruction hT hS hc hcent).IsTame ∧
      ∀ L L' : (S.bdryConstruction hT hS hc hcent).Unif,
        ((S.bdryConstruction hT hS hc hcent).transPolyfold L L').IsTame := by
  refine ⟨bdryConstruction_isTame hT hS hc hcent, fun L L' => ?_⟩
  exact ((S.bdryConstruction hT hS hc hcent).isLocalScDiffeo_trSrc L L').isTame
    ((S.bdryConstruction hT hS hc hcent).isTame_unif (bdryConstruction_isTame hT hS hc hcent) L)

end Construction

section SwapWitness

variable (W : ScBanach)

/-- **Witness with a non-trivial group** (`swapConstruction`, `ℤ/2 ⋉ ([0,∞)² ⊕ W)`, the group
swapping the two faces at the corner, `swap_tameBoundary_witness`): the standing hypotheses of
§17.4 hold and the polyfold structure of Theorem 17.4.26 on `bC` is tame. -/
theorem swap_theorem_17_4_26_tame :
    ∃ (hT : (swapConstruction W).IsTame) (hS : (swapConstruction W).HasUniformizers)
      (hc : (swapConstruction W).HatContinuous) (hcent : (swapConstruction W).IsCentred),
      ((swapConstruction W).bdryConstruction hT hS hc hcent).IsTame ∧
        ∀ L L' : ((swapConstruction W).bdryConstruction hT hS hc hcent).Unif,
          (((swapConstruction W).bdryConstruction hT hS hc hcent).transPolyfold L L').IsTame :=
  ⟨swapConstruction_isTame W, swapConstruction_hasUniformizers W,
    swapConstruction_hatContinuous W, swapConstruction_isCentred W,
    theorem_17_4_26_tame _ _ _ _⟩

end SwapWitness

end GCT.PolyfoldConstruction

end Polyfold
