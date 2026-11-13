import Polyfold.Chapter10.WeakFibredProduct

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 10,
§10.2, **Theorem 10.2.2, p. 478 (2017: Theorem 10.2, p. 343)**, last sentence of the statement:
the M-polyfold structures of the object set `L` and the morphism set `𝐋` of the weak fibred
product `X ×_Y Z` are the ones induced on `L ⊂ X × 𝐘 × Z` and `𝐋 ⊂ 𝐗 × 𝐘 × 𝐙` as
sub-M-polyfolds.

The formal structures `WeakFibredProduct.PObj`, `PMor` are iterated: `L = X _F×ₛ (𝐘 ₜ×_G Z)`
is a sub-M-polyfold of `X × (𝐘 ₜ×_G Z)`, itself carrying the sub-M-polyfold structure of
`𝐘 × Z` (Proposition 2.5.20).  Here we prove that the triple-product sets are sub-M-polyfolds
of the triple products and that the two structures agree: the identification of the iterated
subtype with the triple-product subtype is an sc-diffeomorphism.

## What is formalized

* Generic Part I facts (namespace `Polyfold.MPolyfold`):
  `isSubMPolyfold_univ_prod` (`X × A ⊂ X × N` for a sub-M-polyfold `A ⊂ N`),
  `isScDiffeoOn_prodSubtype` (the subtype `X × A` of `X × N` is `X × A` with the product of the
  sub-M-polyfold structure), and `isSubMPolyfold_image_of_isScDiffeoOn` (a sub-M-polyfold of an
  M-polyfold sc-diffeomorphic to a sub-M-polyfold `S ⊂ M` is a sub-M-polyfold of `M`; the
  transitivity of sub-M-polyfolds).
* Theorem 10.2.2 (namespace `Polyfold.WeakFibredProduct`): `objSetTriple`, `morSetTriple` (the
  sets `L ⊂ X × 𝐘 × Z`, `𝐋 ⊂ 𝐗 × 𝐘 × 𝐙`), `isSubMPolyfold_objSetTriple`,
  `isSubMPolyfold_morSetTriple`, and **`theorem_10_2_2_triple`**: both are sub-M-polyfolds and
  `(x, ϕ, z) ↦ (x, ϕ, z)`, `(h, ϕ, k) ↦ (h, ϕ, k)` are sc-diffeomorphisms of `PObj`, `PMor`
  onto the induced structures.

No hypothesis is added beyond the admissibility used for `PObj`, `PMor` (which an equivalence `F`
or `G` gives, `Admissible.of_isEquivalence_left`, `of_isEquivalence_right`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v w

namespace MPolyfold

section Generic

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ParacompactSpace M] {P : MPolyfold M}
  {N : Type*} [TopologicalSpace N] [T2Space N] [ParacompactSpace N] {Q : MPolyfold N}

/-- A map into a sub-M-polyfold which is sc-smooth into the ambient M-polyfold is sc-smooth into
the sub-M-polyfold (a copy of the private lemma of `Chapter10/WeakFibredProduct.lean`). -/
private theorem isScSmoothOn_subPolyfold_of_val' {A : Set N} (hA : Q.IsSubMPolyfold A)
    [ParacompactSpace A] {f : M → A} {U : Set M}
    (hf : P.IsScSmoothOn Q (fun x => (f x : N)) U) :
    P.IsScSmoothOn (subPolyfold hA) f U := by
  refine IsScSmoothOn.of_locally hf.isOpen fun x hx => ?_
  set d := hA.data (f x).2
  have hU' : IsOpen (U ∩ (fun x => (f x : N)) ⁻¹' d.V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen d.isOpen
  refine ⟨_, hU', ⟨hx, hA.mem_data_V (f x).2⟩, inter_subset_left, ?_⟩
  refine (IsScSmoothOn.comp (subPolyfold_retraction_isScSmooth hA d (f x))
    (hf.mono hU' inter_subset_left) fun y hy => hy.2).congr fun y hy => Subtype.ext ?_
  simp only [Function.comp_apply]
  rw [d.retractInto_val (f x) hy.2]
  exact d.apply_eq_self ⟨(f y).2, hy.2⟩

/-- **`X × A` is a sub-M-polyfold of `X × N`** for a sub-M-polyfold `A ⊂ N`, with the
retraction `id × r`. -/
theorem isSubMPolyfold_univ_prod [ParacompactSpace (M × N)] {A : Set N}
    (hA : Q.IsSubMPolyfold A) : (P.prod Q).IsSubMPolyfold (univ ×ˢ A) := by
  rintro ⟨x, a⟩ ⟨-, ha⟩
  set d := hA.data ha
  refine ⟨univ ×ˢ d.V, isOpen_univ.prod d.isOpen, ⟨mem_univ x, hA.mem_data_V ha⟩,
    fun p => (p.1, d.r p.2), fun p hp => ⟨mem_univ _, d.mapsTo hp.2⟩, ?_, fun p hp => ?_, ?_⟩
  · exact IsScSmoothOn.prodMk
      (IsScSmoothOn.mono (isScSmoothMap_fst P Q) (isOpen_univ.prod d.isOpen) (subset_univ _))
      (d.isScSmoothOn.comp
        (IsScSmoothOn.mono (isScSmoothMap_snd P Q) (isOpen_univ.prod d.isOpen) (subset_univ _))
        fun p hp => hp.2)
  · exact Prod.ext rfl (d.idem _ hp.2)
  · ext ⟨y, b⟩
    constructor
    · rintro ⟨⟨y', b'⟩, hp, he⟩
      cases he
      exact ⟨⟨mem_univ _, d.apply_mem hp.2⟩, mem_univ _, d.mapsTo hp.2⟩
    · rintro ⟨⟨-, hb⟩, -, hbV⟩
      exact ⟨(y, b), ⟨mem_univ _, hbV⟩, Prod.ext rfl (d.apply_eq_self ⟨hb, hbV⟩)⟩

/-- `X × A → (X × N) ⊇ univ ×ˢ A`, `(x, a) ↦ (x, a)`. -/
def prodSubtypeMk {A : Set N} (p : M × A) : (univ ×ˢ A : Set (M × N)) :=
  ⟨(p.1, p.2.1), mem_univ _, p.2.2⟩

/-- The inverse `univ ×ˢ A → X × A`. -/
def prodSubtypeInv {A : Set N} (q : (univ ×ˢ A : Set (M × N))) : M × A :=
  (q.1.1, ⟨q.1.2, q.2.2⟩)

/-- **The subtype `univ ×ˢ A` of `X × N` is `X × A`**: the identification is an
sc-diffeomorphism from `X × A` (product of `X` and the sub-M-polyfold `A`) onto the
sub-M-polyfold `univ ×ˢ A` of `X × N`. -/
theorem isScDiffeoOn_prodSubtype {A : Set N} (hA : Q.IsSubMPolyfold A) [ParacompactSpace A]
    [ParacompactSpace (M × N)] [ParacompactSpace (M × A)]
    [ParacompactSpace (univ ×ˢ A : Set (M × N))] :
    (P.prod (subPolyfold hA)).IsScDiffeoOn (subPolyfold (isSubMPolyfold_univ_prod (P := P) hA))
      prodSubtypeMk prodSubtypeInv univ univ := by
  refine ⟨?_, ?_, mapsTo_univ _ _, mapsTo_univ _ _, fun _ _ => rfl, fun _ _ => rfl⟩
  · refine isScSmoothOn_subPolyfold_of_val' _ ?_
    exact IsScSmoothOn.prodMk (isScSmoothMap_fst _ _)
      ((subPolyfold_inclusion_isScSmooth hA).comp (isScSmoothMap_snd _ _))
  · have hinc := subPolyfold_inclusion_isScSmooth (isSubMPolyfold_univ_prod (P := P) hA)
    refine IsScSmoothOn.prodMk ((isScSmoothMap_fst _ _).comp hinc) ?_
    refine isScSmoothOn_subPolyfold_of_val' hA ?_
    exact (isScSmoothMap_snd _ _).comp hinc

/-- **Transitivity of sub-M-polyfolds**: if `j : M₁ → S` is an sc-diffeomorphism onto a
sub-M-polyfold `S ⊂ M` and `B ⊂ M₁` is a sub-M-polyfold, then `j(B)` is a sub-M-polyfold of
`M`.  Near `j(b)` the retraction is `j ∘ r_B ∘ j⁻¹ ∘ (i⁻¹ ∘ r_S)`. -/
theorem isSubMPolyfold_image_of_isScDiffeoOn {M₁ : Type*} [TopologicalSpace M₁] [T2Space M₁]
    [ParacompactSpace M₁] {P₁ : MPolyfold M₁} {S : Set M} (hS : P.IsSubMPolyfold S)
    [ParacompactSpace S] {j : M₁ → S} {g : S → M₁}
    (hj : P₁.IsScDiffeoOn (subPolyfold hS) j g univ univ) {B : Set M₁}
    (hB : P₁.IsSubMPolyfold B) : P.IsSubMPolyfold ((fun x => (j x : M)) '' B) := by
  rintro _ ⟨b, hb, rfl⟩
  set J : M₁ → M := fun x => (j x : M) with hJ
  have hJs : P₁.IsScSmoothOn P J univ :=
    (subPolyfold_inclusion_isScSmooth hS).comp hj.isScSmoothOn
  set dS := hS.data (j b).2
  set dB := hB.data hb
  set ρ : M → M₁ := g ∘ dS.retractInto (j b)
  have hρs : P.IsScSmoothOn P₁ ρ dS.V :=
    hj.isScSmoothOn_inv.comp (subPolyfold_retraction_isScSmooth hS dS (j b)) (mapsTo_univ _ _)
  -- `ρ ∘ J = id` near `b`
  have hK : ∀ x, J x ∈ dS.V → ρ (J x) = x := fun x hx => by
    have : dS.retractInto (j b) (J x) = j x :=
      Subtype.ext ((dS.retractInto_val (j b) hx).trans (dS.apply_eq_self ⟨(j x).2, hx⟩))
    change g (dS.retractInto (j b) (J x)) = x
    rw [this, hj.left_inv x (mem_univ _)]
  set W := dB.V ∩ J ⁻¹' dS.V with hW
  have hWo : IsOpen W := hJs.continuousOn.isOpen_inter_preimage isOpen_univ dS.isOpen |>.inter
    dB.isOpen |> fun h => by simpa [hW, inter_comm] using h
  set VB := W ∩ dB.r ⁻¹' W with hVB
  have hVBo : IsOpen VB := (dB.continuousOn.mono inter_subset_left).isOpen_inter_preimage hWo hWo
  set V := dS.V ∩ ρ ⁻¹' VB with hV
  have hVo : IsOpen V := hρs.continuousOn.isOpen_inter_preimage dS.isOpen hVBo
  have hbS : J b ∈ dS.V := hS.mem_data_V (j b).2
  have hbB : b ∈ dB.V := hB.mem_data_V hb
  have hrb : dB.r b = b := dB.apply_eq_self ⟨hb, hbB⟩
  -- the retraction maps `VB` into `VB`
  have hVBr : ∀ y ∈ VB, dB.r y ∈ VB := fun y hy => ⟨hy.2, by
    rw [mem_preimage, dB.idem y hy.1.1]; exact hy.2⟩
  have hmaps : ∀ x ∈ V, J (dB.r (ρ x)) ∈ V := fun x hx => by
    have hz := hVBr _ hx.2
    refine ⟨hz.1.2, ?_⟩
    rw [mem_preimage, hK _ hz.1.2]
    exact hz
  refine ⟨V, hVo, ⟨hbS, ?_⟩, fun x => J (dB.r (ρ x)), hmaps, ?_, fun x hx => ?_, ?_⟩
  · rw [mem_preimage, hK b hbS]
    exact ⟨⟨hbB, hbS⟩, by rw [mem_preimage, hrb]; exact ⟨hbB, hbS⟩⟩
  · have h1 : P₁.IsScSmoothOn P (J ∘ dB.r) VB :=
      hJs.comp (dB.isScSmoothOn.mono hVBo fun y hy => hy.1.1) (mapsTo_univ _ _)
    exact h1.comp (hρs.mono hVo inter_subset_left) fun x hx => hx.2
  · have hz := hVBr _ hx.2
    change J (dB.r (ρ (J (dB.r (ρ x))))) = J (dB.r (ρ x))
    rw [hK _ hz.1.2, dB.idem _ hx.2.1.1]
  · ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨_, dB.apply_mem (hx.2.1.1), rfl⟩, hmaps x hx⟩
    · rintro ⟨⟨b', hb', rfl⟩, hw⟩
      have hb'V : ρ (J b') = b' := hK b' hw.1
      have hb'B : b' ∈ dB.V := by
        have := hw.2
        rw [mem_preimage, hb'V] at this
        exact this.1.1
      refine ⟨J b', hw, ?_⟩
      change J (dB.r (ρ (J b'))) = J b'
      rw [hb'V, dB.apply_eq_self ⟨hb', hb'B⟩]

end Generic

end MPolyfold

/-! ### Theorem 10.2.2: the structures induced from the triple products -/

section WFP

variable {ObjX MorX : Type u} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY MorY : Type v} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjZ MorZ : Type w} [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
  [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
  {X : EpGroupoid ObjX MorX} {Y : EpGroupoid ObjY MorY} {Z : EpGroupoid ObjZ MorZ}
  (F : EpFunctor X Y) (G : EpFunctor Z Y)

namespace WeakFibredProduct

/-- The object set `L = {(x, ϕ, z) | ϕ : F(x) → G(z)}` as a subset of `X × 𝐘 × Z`. -/
def objSetTriple : Set (ObjX × (MorY × ObjZ)) :=
  {p | Y.src p.2.1 = F.obj p.1 ∧ Y.tgt p.2.1 = G.obj p.2.2}

/-- The morphism set `𝐋 = {(h, ϕ, k) | ϕ : F(s(h)) → G(s(k))}` as a subset of `𝐗 × 𝐘 × 𝐙`. -/
def morSetTriple : Set (MorX × (MorY × MorZ)) :=
  {p | Y.src p.2.1 = F.obj (X.src p.1) ∧ Y.tgt p.2.1 = G.obj (Z.src p.2.2)}

variable {F G}

/-- The triple-product form of the objects. -/
def Obj.toTriple (p : Obj F G) : objSetTriple F G := ⟨(p.x, (p.φ, p.z)), p.src_φ, p.tgt_φ⟩

/-- The objects from the triple-product form. -/
def Obj.ofTriple (q : objSetTriple F G) : Obj F G := Obj.mk F G q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2

/-- The triple-product form of the morphisms. -/
def Mor.toTriple (m : Mor F G) : morSetTriple F G := ⟨(m.h, (m.φ, m.k)), m.src_φ, m.tgt_φ⟩

/-- The morphisms from the triple-product form. -/
def Mor.ofTriple (q : morSetTriple F G) : Mor F G := Mor.mk F G q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2

variable (F G)

theorem objSetTriple_eq :
    objSetTriple F G = (fun q : ObjX × objRight G => (q.1, (q.2 : MorY × ObjZ))) '' objSet F G := by
  ext ⟨x, φ, z⟩
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨(x, ⟨(φ, z), h₂⟩), h₁.symm, rfl⟩
  · rintro ⟨⟨x', ⟨⟨φ', z'⟩, h₂⟩⟩, h₁, he⟩
    cases he
    exact ⟨h₁.symm, h₂⟩

theorem morSetTriple_eq :
    morSetTriple F G = (fun q : MorX × morRight G => (q.1, (q.2 : MorY × MorZ))) '' morSet F G := by
  ext ⟨x, φ, z⟩
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨(x, ⟨(φ, z), h₂⟩), h₁.symm, rfl⟩
  · rintro ⟨⟨x', ⟨⟨φ', z'⟩, h₂⟩⟩, h₁, he⟩
    cases he
    exact ⟨h₁.symm, h₂⟩

/-- **2021 Theorem 10.2.2, p. 478**: `L` is a sub-M-polyfold of `X × 𝐘 × Z`. -/
theorem isSubMPolyfold_objSetTriple (h : Admissible F G) :
    letI := MPolyfold.paracompactSpace_prod Y.PMor Z.PObj
    letI := MPolyfold.paracompactSpace_prod X.PObj (Y.PMor.prod Z.PObj)
    (X.PObj.prod (Y.PMor.prod Z.PObj)).IsSubMPolyfold (objSetTriple F G) := by
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PObj
  let _ := MPolyfold.paracompactSpace_prod X.PObj (Y.PMor.prod Z.PObj)
  let _ := MPolyfold.paracompactSpace_prod X.PObj (PA G)
  let _ := (X.PObj.prod (Y.PMor.prod Z.PObj)).paracompactSpace_subtype
    (univ ×ˢ objRight G : Set (ObjX × (MorY × ObjZ)))
  rw [objSetTriple_eq]
  exact MPolyfold.isSubMPolyfold_image_of_isScDiffeoOn _
    (MPolyfold.isScDiffeoOn_prodSubtype (P := X.PObj) (isSubMPolyfold_objRight G))
    (isSubMPolyfold_objSet F G h)

/-- **2021 Theorem 10.2.2, p. 478**: `𝐋` is a sub-M-polyfold of `𝐗 × 𝐘 × 𝐙`. -/
theorem isSubMPolyfold_morSetTriple (h : Admissible F G) :
    letI := MPolyfold.paracompactSpace_prod Y.PMor Z.PMor
    letI := MPolyfold.paracompactSpace_prod X.PMor (Y.PMor.prod Z.PMor)
    (X.PMor.prod (Y.PMor.prod Z.PMor)).IsSubMPolyfold (morSetTriple F G) := by
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PMor
  let _ := MPolyfold.paracompactSpace_prod X.PMor (Y.PMor.prod Z.PMor)
  let _ := MPolyfold.paracompactSpace_prod X.PMor (PB G)
  let _ := (X.PMor.prod (Y.PMor.prod Z.PMor)).paracompactSpace_subtype
    (univ ×ˢ morRight G : Set (MorX × (MorY × MorZ)))
  rw [morSetTriple_eq]
  exact MPolyfold.isSubMPolyfold_image_of_isScDiffeoOn _
    (MPolyfold.isScDiffeoOn_prodSubtype (P := X.PMor) (isSubMPolyfold_morRight G))
    (isSubMPolyfold_morSet F G h)

/-- **2021 Theorem 10.2.2, p. 478 (2017: Theorem 10.2, p. 343), last sentence**: the object set
`L ⊂ X × 𝐘 × Z` and the morphism set `𝐋 ⊂ 𝐗 × 𝐘 × 𝐙` are sub-M-polyfolds, and the structures
`PObj`, `PMor` of the weak fibred product are the induced ones: `(x, ϕ, z) ↦ (x, ϕ, z)` and
`(h, ϕ, k) ↦ (h, ϕ, k)` are sc-diffeomorphisms onto `L` and `𝐋` with their sub-M-polyfold
structures. -/
theorem theorem_10_2_2_triple (h : Admissible F G) :
    letI := MPolyfold.paracompactSpace_prod Y.PMor Z.PObj
    letI := MPolyfold.paracompactSpace_prod X.PObj (Y.PMor.prod Z.PObj)
    letI := MPolyfold.paracompactSpace_prod Y.PMor Z.PMor
    letI := MPolyfold.paracompactSpace_prod X.PMor (Y.PMor.prod Z.PMor)
    letI := (X.PObj.prod (Y.PMor.prod Z.PObj)).paracompactSpace_subtype (objSetTriple F G)
    letI := (X.PMor.prod (Y.PMor.prod Z.PMor)).paracompactSpace_subtype (morSetTriple F G)
    ∃ (hL : (X.PObj.prod (Y.PMor.prod Z.PObj)).IsSubMPolyfold (objSetTriple F G))
      (hL' : (X.PMor.prod (Y.PMor.prod Z.PMor)).IsSubMPolyfold (morSetTriple F G)),
      (PObj F G h).IsScDiffeoOn (MPolyfold.subPolyfold hL) Obj.toTriple Obj.ofTriple univ univ ∧
      (PMor F G h).IsScDiffeoOn (MPolyfold.subPolyfold hL') Mor.toTriple Mor.ofTriple univ
        univ := by
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PObj
  let _ := MPolyfold.paracompactSpace_prod X.PObj (Y.PMor.prod Z.PObj)
  let _ := MPolyfold.paracompactSpace_prod Y.PMor Z.PMor
  let _ := MPolyfold.paracompactSpace_prod X.PMor (Y.PMor.prod Z.PMor)
  let _ := (X.PObj.prod (Y.PMor.prod Z.PObj)).paracompactSpace_subtype (objSetTriple F G)
  let _ := (X.PMor.prod (Y.PMor.prod Z.PMor)).paracompactSpace_subtype (morSetTriple F G)
  have hL := isSubMPolyfold_objSetTriple F G h
  have hL' := isSubMPolyfold_morSetTriple F G h
  refine ⟨hL, hL', ⟨?_, ?_, mapsTo_univ _ _, mapsTo_univ _ _, fun _ _ => rfl, fun _ _ => rfl⟩,
    ⟨?_, ?_, mapsTo_univ _ _, mapsTo_univ _ _, fun _ _ => rfl, fun _ _ => rfl⟩⟩
  · refine MPolyfold.isScSmoothOn_subPolyfold_of_val' hL ?_
    exact MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_x h)
      (MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_φ h) (isScSmoothMap_z h))
  · have hinc := MPolyfold.subPolyfold_inclusion_isScSmooth hL
    have h₂ : (MPolyfold.subPolyfold hL).IsScSmoothMap (Y.PMor.prod Z.PObj)
        fun q : objSetTriple F G => q.1.2 := (MPolyfold.isScSmoothMap_snd _ _).comp hinc
    have hx : (MPolyfold.subPolyfold hL).IsScSmoothMap X.PObj fun q : objSetTriple F G => q.1.1 :=
      (MPolyfold.isScSmoothMap_fst _ _).comp hinc
    have hφ : (MPolyfold.subPolyfold hL).IsScSmoothMap Y.PMor
        fun q : objSetTriple F G => q.1.2.1 := (MPolyfold.isScSmoothMap_fst _ _).comp h₂
    have hz : (MPolyfold.subPolyfold hL).IsScSmoothMap Z.PObj
        fun q : objSetTriple F G => q.1.2.2 := (MPolyfold.isScSmoothMap_snd _ _).comp h₂
    exact isScSmoothOn_obj_of (f := Obj.ofTriple) h hx hφ hz
  · refine MPolyfold.isScSmoothOn_subPolyfold_of_val' hL' ?_
    exact MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_h h)
      (MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_mφ h) (isScSmoothMap_k h))
  · have hinc := MPolyfold.subPolyfold_inclusion_isScSmooth hL'
    have h₂ : (MPolyfold.subPolyfold hL').IsScSmoothMap (Y.PMor.prod Z.PMor)
        fun q : morSetTriple F G => q.1.2 := (MPolyfold.isScSmoothMap_snd _ _).comp hinc
    have hh : (MPolyfold.subPolyfold hL').IsScSmoothMap X.PMor fun q : morSetTriple F G => q.1.1 :=
      (MPolyfold.isScSmoothMap_fst _ _).comp hinc
    have hφ : (MPolyfold.subPolyfold hL').IsScSmoothMap Y.PMor
        fun q : morSetTriple F G => q.1.2.1 := (MPolyfold.isScSmoothMap_fst _ _).comp h₂
    have hk : (MPolyfold.subPolyfold hL').IsScSmoothMap Z.PMor
        fun q : morSetTriple F G => q.1.2.2 := (MPolyfold.isScSmoothMap_snd _ _).comp h₂
    exact isScSmoothOn_mor_of (f := Mor.ofTriple) h hh hφ hk

end WeakFibredProduct

end WFP

end Polyfold
