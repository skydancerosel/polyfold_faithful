import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_19

/-! Round trip for V10_19 (2021 Theorem 10.2.2, the claims for an equivalence `F`).

The item lists the definitions `projLeft`, `projRight`, `natTrans` (vocabulary) and nine
theorems; `A` is the conjunction of their types, universes at `0` (the example has none):
`natTrans_app`, `naturallyEquivalent` (for every admissible `F`, `G`), `isEquivalence_projRight`,
`degIndex_eq_z`, `theorem_10_2_2`, the general facts `EpFunctor.IsEquivalence.degIndex_obj`,
`isTame_of_isTame`, `hasParacompactOrbitSpace`, and the witness `theorem_10_2_2_pairToPoint`.

**The two weak fibred products.**  The project's ep-groupoid `epGroupoid F G h` lives on
`Obj F G ⊆ X × (𝐘 ₜ×_G Z)` with the *iterated* sub-M-polyfold structure (`PObj`:
`X _F×ₛ (𝐘 ₜ×_G Z)` inside `X × (𝐘 ₜ×_G Z)`, the latter inside `𝐘 × Z`).  The blind `B` builds
its own `E` on `objSetB F G ⊆ X × 𝐘 × Z`, a sub-M-polyfold *of the triple product*
(`IsWFPEpB`: the structure maps of Definition 10.2.1 and `E.PObj = subPolyfold hS`,
`E.PMor = subPolyfold hT`), and asserts its existence.

**Comparison (used by `B_to_A`, reusable for V10_20, V10_21).**  Given any such `E` (so given the
triple-product sub-M-polyfold structures `hS`, `hT`), the obvious bijections
`eo : Obj F G → objSetB F G`, `em : Mor F G → morSetB F G` form an sc-smooth functor
`toE : epGroupoid F G h → E` with sc-smooth inverse functor `toE'` (entrywise sc-smoothness in
both directions; the middle entry of the target uses `conjB = conj`), hence an equivalence
(`EpFunctor.isEquivalence_of_inverse`).  So `projRight = πZ ∘ toE`, `projLeft = πX ∘ toE`, and
equivalence, degeneracy index, tameness and paracompactness of the orbit space transfer.

* `B_to_A`: `isEquivalence_projRight`, `degIndex_eq_z`, `theorem_10_2_2` (including its natural
  equivalence, as `B`'s `τ` whiskered by `toE`) and the witness's second half follow from `B`
  through the comparison.  `natTrans_app` (`rfl`), `naturallyEquivalent` (stated for *every*
  admissible `F`, `G`, not only for an equivalence `F`, so not a consequence of `B`), the three
  general facts about equivalences and the witness's `Nonempty` are re-proved outright (the
  project's one-line proofs, from non-item lemmas).
* `A_to_B` is not proved.  It needs an `E` with `IsWFPEpB`, i.e. (i) that `objSetB F G` and
  `morSetB F G` are sub-M-polyfolds of the triple products `X × 𝐘 × Z`, `𝐗 × 𝐘 × 𝐙` (the text's
  (10.8); the project proves only the iterated fibred-product version and says "the comparison
  with a structure induced from the triple product is not needed"), and (ii) the ep-groupoid
  structure on them with *literally* `PObj = subPolyfold hS`, transported from `epGroupoid`
  along the comparison (sc-diffeomorphism, properness, condition (4) on `𝐋 ₛ×ₜ 𝐋`).  This is
  the first claim of Theorem 10.2.2 (item V10_18) in the blind's triple-product form, which `A`
  does not contain; both (i) and (ii) are believed true (for (i): a sub-M-polyfold of a
  sub-M-polyfold is one, with the composite retraction `(id × i) ∘ r_A ∘ (id × i⁻¹r_B)`), but
  they are Part I/Chapter 7 constructions not in the project. -/

set_option maxSynthPendingDepth 3

namespace RoundTrip.V10_19
open Polyfold Set Function WeakFibredProduct

/-! The project's statement (universes at `0`). -/
def A1 : Prop := type_of% @Polyfold.WeakFibredProduct.natTrans_app.{0, 0, 0}
def A2 : Prop := type_of% @Polyfold.WeakFibredProduct.naturallyEquivalent.{0, 0, 0}
def A3 : Prop := type_of% @Polyfold.WeakFibredProduct.isEquivalence_projRight.{0, 0, 0}
def A4 : Prop := type_of% @Polyfold.WeakFibredProduct.degIndex_eq_z.{0, 0, 0}
def A5 : Prop := type_of% @Polyfold.WeakFibredProduct.theorem_10_2_2.{0, 0, 0}
def A6 : Prop := type_of% @Polyfold.EpFunctor.IsEquivalence.degIndex_obj.{0, 0}
def A7 : Prop := type_of% @Polyfold.EpFunctor.IsEquivalence.isTame_of_isTame.{0, 0}
def A8 : Prop := type_of% @Polyfold.EpFunctor.IsEquivalence.hasParacompactOrbitSpace.{0, 0}
def A9 : Prop := type_of% @Polyfold.WeakFibredProduct.Examples.theorem_10_2_2_pairToPoint

/-- The project's statement. -/
def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A6 ∧ A7 ∧ A8 ∧ A9

theorem A_holds : A :=
  ⟨@Polyfold.WeakFibredProduct.natTrans_app.{0, 0, 0},
    @Polyfold.WeakFibredProduct.naturallyEquivalent.{0, 0, 0},
    @Polyfold.WeakFibredProduct.isEquivalence_projRight.{0, 0, 0},
    @Polyfold.WeakFibredProduct.degIndex_eq_z.{0, 0, 0},
    @Polyfold.WeakFibredProduct.theorem_10_2_2.{0, 0, 0},
    @Polyfold.EpFunctor.IsEquivalence.degIndex_obj.{0, 0},
    @Polyfold.EpFunctor.IsEquivalence.isTame_of_isTame.{0, 0},
    @Polyfold.EpFunctor.IsEquivalence.hasParacompactOrbitSpace.{0, 0},
    @Polyfold.WeakFibredProduct.Examples.theorem_10_2_2_pairToPoint⟩

/-! ### The comparison of the two weak fibred products -/

/-- A map into a sub-M-polyfold which is sc-smooth into the ambient M-polyfold is sc-smooth (a
copy of the private `isScSmoothOn_subPolyfold_of_val` of `WeakFibredProduct.lean`). -/
theorem subVal {M : Type*} [TopologicalSpace M] [T2Space M] [ParacompactSpace M]
    {PM : MPolyfold M} {N : Type*} [TopologicalSpace N] [T2Space N] [ParacompactSpace N]
    {PN : MPolyfold N} {A : Set N} (hA : PN.IsSubMPolyfold A) [ParacompactSpace A] {f : M → A}
    {U : Set M} (hf : PM.IsScSmoothOn PN (fun x => (f x : N)) U) :
    PM.IsScSmoothOn (MPolyfold.subPolyfold hA) f U := by
  refine MPolyfold.IsScSmoothOn.of_locally hf.isOpen fun x hx => ?_
  set d := hA.data (f x).2
  have hU' : IsOpen (U ∩ (fun x => (f x : N)) ⁻¹' d.V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen d.isOpen
  refine ⟨_, hU', ⟨hx, hA.mem_data_V (f x).2⟩, inter_subset_left, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp (MPolyfold.subPolyfold_retraction_isScSmooth hA d (f x))
    (hf.mono hU' inter_subset_left) fun y hy => hy.2).congr fun y hy => Subtype.ext ?_
  simp only [Function.comp_apply]
  rw [d.retractInto_val (f x) hy.2]
  exact d.apply_eq_self ⟨(f y).2, hy.2⟩

section Iso
variable {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjZ MorZ : Type} [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
  [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
  {X : EpGroupoid ObjX MorX} {Y : EpGroupoid ObjY MorY} {Z : EpGroupoid ObjZ MorZ}
  {F : EpFunctor X Y} {G : EpFunctor Z Y}

/-- Objects: `(x, (ϕ, z)) ↦ (x, ϕ, z)`. -/
def eo (p : WeakFibredProduct.Obj F G) : objSetB F G := ⟨(p.x, p.φ, p.z), p.src_φ, p.tgt_φ⟩

/-- Objects, inverse. -/
def eo' (q : objSetB F G) : WeakFibredProduct.Obj F G :=
  Obj.mk F G q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2

/-- Morphisms: `(h, (ϕ, k)) ↦ (h, ϕ, k)`. -/
def em (m : WeakFibredProduct.Mor F G) : morSetB F G := ⟨(m.h, m.φ, m.k), m.src_φ, m.tgt_φ⟩

/-- Morphisms, inverse. -/
def em' (q : morSetB F G) : WeakFibredProduct.Mor F G :=
  Mor.mk F G q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2

/-- The blind's `G(k) ∘ (ϕ ∘ F(h⁻¹))` is the project's `(G(k) ∘ ϕ) ∘ F(h)⁻¹`. -/
theorem conjB_eq {h : MorX} {φ : MorY} {k : MorZ} (h₁ : Y.src φ = F.obj (X.src h))
    (h₂ : Y.tgt φ = G.obj (Z.src k)) : conjB F G h φ k = conj F G h φ k := by
  unfold conjB conj
  rw [F.toGroupoidFunctor.mor_inv h]
  exact (Y.comp_assoc _ _ _ (by rw [G.src_mor, h₂]) (by rw [Y.tgt_inv, F.src_mor, h₁])).symm

variable [ParacompactSpace (MorY × ObjZ)] [ParacompactSpace (ObjX × MorY × ObjZ)]
  [ParacompactSpace (MorY × MorZ)] [ParacompactSpace (MorX × MorY × MorZ)]
  [ParacompactSpace (objSetB F G)] [ParacompactSpace (morSetB F G)]
  {E : EpGroupoid (objSetB F G) (morSetB F G)}

theorem em_src (hE : IsWFPEpB F G E) (m : WeakFibredProduct.Mor F G) :
    E.src (em m) = eo (WeakFibredProduct.src m) :=
  Subtype.ext (hE.1.1 (em m))

theorem em_tgt (hE : IsWFPEpB F G E) (m : WeakFibredProduct.Mor F G) :
    E.tgt (em m) = eo (WeakFibredProduct.tgt m) := by
  apply Subtype.ext
  rw [hE.1.2.1 (em m)]
  change (X.tgt m.h, conjB F G m.h m.φ m.k, Z.tgt m.k) = (X.tgt m.h, conj F G m.h m.φ m.k, Z.tgt m.k)
  rw [conjB_eq m.src_φ m.tgt_φ]

theorem src_em' (hE : IsWFPEpB F G E) (q : morSetB F G) :
    WeakFibredProduct.src (em' q) = eo' (E.src q) := by
  have e := hE.1.1 q
  exact Obj.ext (congrArg (·.1) e).symm (congrArg (·.2.1) e).symm (congrArg (·.2.2) e).symm

theorem tgt_em' (hE : IsWFPEpB F G E) (q : morSetB F G) :
    WeakFibredProduct.tgt (em' q) = eo' (E.tgt q) := by
  have e := hE.1.2.1 q
  refine Obj.ext (congrArg (·.1) e).symm ?_ (congrArg (·.2.2) e).symm
  change conj F G q.1.1 q.1.2.1 q.1.2.2 = (E.tgt q).1.2.1
  rw [congrArg (·.2.1) e]
  exact (conjB_eq q.2.1 q.2.2).symm

/-- The comparison functor `X ×_Y Z (project) → X ×_Y Z (blind)`. -/
def toE (hE : IsWFPEpB F G E) (h : Admissible F G) : EpFunctor (epGroupoid F G h) E where
  obj := eo
  mor := em
  src_mor m := em_src hE m
  tgt_mor m := em_tgt hE m
  mor_comp m m' hc := by
    have hc' : E.src (em m) = E.tgt (em m') := by
      rw [em_src hE, em_tgt hE]; exact congrArg eo hc
    apply Subtype.ext
    rw [hE.1.2.2.2.2 (em m) (em m') hc']
    change ((WeakFibredProduct.comp m m').h, (WeakFibredProduct.comp m m').φ,
      (WeakFibredProduct.comp m m').k) = _
    rw [h_comp hc, φ_comp hc, k_comp hc]
    rfl
  mor_unit p := Subtype.ext (hE.1.2.2.1 (eo p)).symm
  isScSmoothMap_obj := by
    obtain ⟨hS, hT, hPO, hPM⟩ := hE.2
    change (PObj F G h).IsScSmoothMap E.PObj eo
    rw [hPO]
    exact subVal hS (MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_x h)
      (MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_φ h) (isScSmoothMap_z h)))
  isScSmoothMap_mor := by
    obtain ⟨hS, hT, hPO, hPM⟩ := hE.2
    change (PMor F G h).IsScSmoothMap E.PMor em
    rw [hPM]
    exact subVal hT (MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_h h)
      (MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_mφ h) (isScSmoothMap_k h)))

/-- The inverse comparison functor. -/
def toE' (hE : IsWFPEpB F G E) (h : Admissible F G) : EpFunctor E (epGroupoid F G h) where
  obj := eo'
  mor := em'
  src_mor q := src_em' hE q
  tgt_mor q := tgt_em' hE q
  mor_comp q q' hc := by
    have hc' : WeakFibredProduct.src (em' q) = WeakFibredProduct.tgt (em' q') := by
      rw [src_em' hE, tgt_em' hE]; exact congrArg eo' hc
    have e := hE.1.2.2.2.2 q q' hc
    refine Mor.ext ?_ ?_ ?_
    · change (E.comp q q').1.1 = (WeakFibredProduct.comp (em' q) (em' q')).h
      rw [h_comp hc', congrArg (·.1) e]; rfl
    · change (E.comp q q').1.2.1 = (WeakFibredProduct.comp (em' q) (em' q')).φ
      rw [φ_comp hc', congrArg (·.2.1) e]; rfl
    · change (E.comp q q').1.2.2 = (WeakFibredProduct.comp (em' q) (em' q')).k
      rw [k_comp hc', congrArg (·.2.2) e]; rfl
  mor_unit o := by
    have e := hE.1.2.2.1 o
    exact Mor.ext (congrArg (·.1) e) (congrArg (·.2.1) e) (congrArg (·.2.2) e)
  isScSmoothMap_obj := by
    obtain ⟨hS, hT, hPO, hPM⟩ := hE.2
    change E.PObj.IsScSmoothMap (PObj F G h) eo'
    rw [hPO]
    have hi := MPolyfold.subPolyfold_inclusion_isScSmooth hS
    have hsnd := (MPolyfold.isScSmoothMap_snd X.PObj (Y.PMor.prod Z.PObj)).comp hi
    exact isScSmoothOn_obj_of h ((MPolyfold.isScSmoothMap_fst X.PObj (Y.PMor.prod Z.PObj)).comp hi)
      ((MPolyfold.isScSmoothMap_fst Y.PMor Z.PObj).comp hsnd)
      ((MPolyfold.isScSmoothMap_snd Y.PMor Z.PObj).comp hsnd)
  isScSmoothMap_mor := by
    obtain ⟨hS, hT, hPO, hPM⟩ := hE.2
    change E.PMor.IsScSmoothMap (PMor F G h) em'
    rw [hPM]
    have hi := MPolyfold.subPolyfold_inclusion_isScSmooth hT
    have hsnd := (MPolyfold.isScSmoothMap_snd X.PMor (Y.PMor.prod Z.PMor)).comp hi
    exact isScSmoothOn_mor_of h ((MPolyfold.isScSmoothMap_fst X.PMor (Y.PMor.prod Z.PMor)).comp hi)
      ((MPolyfold.isScSmoothMap_fst Y.PMor Z.PMor).comp hsnd)
      ((MPolyfold.isScSmoothMap_snd Y.PMor Z.PMor).comp hsnd)

/-- **The comparison functor is an equivalence** (it is an isomorphism of ep-groupoids). -/
theorem isEquivalence_toE (hE : IsWFPEpB F G E) (h : Admissible F G) :
    (toE hE h).IsEquivalence :=
  EpFunctor.isEquivalence_of_inverse (G := toE' hE h) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl)

/-- `πZ ∘ toE = projRight`. -/
theorem projRight_eq (hE : IsWFPEpB F G E) (h : Admissible F G) (πZ : EpFunctor E Z)
    (ho : πZ.obj = fun a => a.1.2.2) (hm : πZ.mor = fun m => m.1.2.2) :
    projRight F G h = πZ.comp (toE hE h) := by
  refine EpFunctor.ext (funext fun p => ?_) (funext fun m => ?_)
  · change p.z = πZ.obj (eo p); rw [ho]; rfl
  · change m.k = πZ.mor (em m); rw [hm]; rfl

/-- `πX ∘ toE = projLeft`. -/
theorem projLeft_eq (hE : IsWFPEpB F G E) (h : Admissible F G) (πX : EpFunctor E X)
    (ho : πX.obj = fun a => a.1.1) (hm : πX.mor = fun m => m.1.1) :
    projLeft F G h = πX.comp (toE hE h) := by
  refine EpFunctor.ext (funext fun p => ?_) (funext fun m => ?_)
  · change p.x = πX.obj (eo p); rw [ho]; rfl
  · change m.h = πX.mor (em m); rw [hm]; rfl

/-- The degeneracy index of `epGroupoid` is that of `E`. -/
theorem degIndex_eq (hE : IsWFPEpB F G E) (h : Admissible F G) (p : WeakFibredProduct.Obj F G) :
    (epGroupoid F G h).PObj.degIndex p = E.PObj.degIndex (eo p) :=
  ((isEquivalence_toE hE h).isLocalScDiffeo_obj.degIndex_eq p).symm

/-- Tameness passes from `E` to `epGroupoid`. -/
theorem isTame_of (hE : IsWFPEpB F G E) (h : Admissible F G) (hT : E.PObj.IsTame) :
    (epGroupoid F G h).IsTame :=
  (isEquivalence_toE hE h).isLocalScDiffeo_obj.isTame hT

/-- A paracompact orbit space passes from `E` to `epGroupoid`. -/
theorem paracompact_of (hE : IsWFPEpB F G E) (h : Admissible F G)
    (hP : ParacompactSpace E.OrbitSpace) : (epGroupoid F G h).HasParacompactOrbitSpace := by
  exact (IsHomeomorph.homeomorph _
    (isEquivalence_toE hE h).isHomeomorph_orbitMap).isClosedEmbedding.paracompactSpace

end Iso

/-! ### `B ⇒ A` -/

section Core
variable {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjZ MorZ : Type} [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
  [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
  {X : EpGroupoid ObjX MorX} {Y : EpGroupoid ObjY MorY} {Z : EpGroupoid ObjZ MorZ}
  {F : EpFunctor X Y} {G : EpFunctor Z Y}

/-- **`B` gives the claims of Theorem 10.2.2 for the project's `epGroupoid`.** -/
theorem core (hB : B) (hF : F.IsEquivalence) (h : Admissible F G) :
    (projRight F G h).IsEquivalence ∧
    (F.comp (projLeft F G h)).NaturallyEquivalent (G.comp (projRight F G h)) ∧
    (∀ p : WeakFibredProduct.Obj F G,
      (epGroupoid F G h).PObj.degIndex p = Z.PObj.degIndex p.z) ∧
    (Z.IsTame → (epGroupoid F G h).IsTame) ∧
    (Z.HasParacompactOrbitSpace → (epGroupoid F G h).HasParacompactOrbitSpace) := by
  obtain ⟨_, _, _, _, _, _, E, hE, πX, πZ, hXo, hXm, hZo, hZm, hπZ, hτ, hdeg, htame, hpara⟩ :=
    hB ObjX MorX ObjY MorY ObjZ MorZ X Y Z F G hF
  have hR := projRight_eq hE h πZ hZo hZm
  have hL := projLeft_eq hE h πX hXo hXm
  refine ⟨?_, ?_, fun p => (degIndex_eq hE h p).trans (hdeg (eo p)),
    fun hZ => isTame_of hE h (htame hZ), fun hZ => paracompact_of hE h (hpara hZ)⟩
  · rw [hR]; exact hπZ.comp (isEquivalence_toE hE h)
  · have := EpFunctor.NaturallyEquivalent.comp_left (toE hE h) hτ
    rw [hL, hR]
    exact this

end Core

/-! Conjuncts re-proved outright (not consequences of `B`). -/

theorem degIndex_obj' : A6 := by
  intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF x
  exact hF.isLocalScDiffeo_obj.degIndex_eq x

theorem isTame_of_isTame' : A7 := by
  intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF hY
  exact hF.isLocalScDiffeo_obj.isTame hY

theorem hasParacompactOrbitSpace' : A8 := by
  intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF hY
  let _ : ParacompactSpace Y.OrbitSpace := hY
  exact (IsHomeomorph.homeomorph _ hF.isHomeomorph_orbitMap).isClosedEmbedding.paracompactSpace

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, degIndex_obj', isTame_of_isTame', hasParacompactOrbitSpace', ?_⟩
  · -- `natTrans_app` (definitional)
    intro ObjX MorX _ _ _ _ _ _ ObjY MorY _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ X Y Z F G h p
    rfl
  · -- `naturallyEquivalent`, for every admissible `F`, `G`: the project's `natTrans`
    intro ObjX MorX _ _ _ _ _ _ ObjY MorY _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ X Y Z F G h
    exact ⟨natTrans F G h⟩
  · intro ObjX MorX _ _ _ _ _ _ ObjY MorY _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ X Y Z F G hF h
    exact (core hB hF h).1
  · intro ObjX MorX _ _ _ _ _ _ ObjY MorY _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ X Y Z F G hF h p
    exact (core hB hF h).2.2.1 p
  · intro ObjX MorX _ _ _ _ _ _ ObjY MorY _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ X Y Z F G hF
    exact core hB hF _
  · -- the witness
    refine ⟨⟨Obj.mk _ _ (0 : ℤ) () () rfl rfl⟩, ?_⟩
    exact (core hB EpGroupoid.Examples.isEquivalence_pairToPoint _).1

#rt_check RoundTrip.V10_19.B_to_A [Polyfold.WeakFibredProduct.natTrans_app,
  Polyfold.WeakFibredProduct.naturallyEquivalent,
  Polyfold.WeakFibredProduct.isEquivalence_projRight,
  Polyfold.WeakFibredProduct.degIndex_eq_z, Polyfold.WeakFibredProduct.theorem_10_2_2,
  Polyfold.EpFunctor.IsEquivalence.degIndex_obj, Polyfold.EpFunctor.IsEquivalence.isTame_of_isTame,
  Polyfold.EpFunctor.IsEquivalence.hasParacompactOrbitSpace,
  Polyfold.WeakFibredProduct.Examples.theorem_10_2_2_pairToPoint]
#rt_overlap RoundTrip.V10_19.B_to_A [Polyfold.WeakFibredProduct.natTrans_app,
  Polyfold.WeakFibredProduct.naturallyEquivalent,
  Polyfold.WeakFibredProduct.isEquivalence_projRight,
  Polyfold.WeakFibredProduct.degIndex_eq_z, Polyfold.WeakFibredProduct.theorem_10_2_2,
  Polyfold.EpFunctor.IsEquivalence.degIndex_obj, Polyfold.EpFunctor.IsEquivalence.isTame_of_isTame,
  Polyfold.EpFunctor.IsEquivalence.hasParacompactOrbitSpace,
  Polyfold.WeakFibredProduct.Examples.theorem_10_2_2_pairToPoint]

end RoundTrip.V10_19
