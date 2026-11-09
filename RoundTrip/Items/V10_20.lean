import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_20

/-! Round trip for V10_20 (2021 Theorem 10.2.2, the claims for an equivalence `G` and for two
equivalences).

The item lists four theorems; `A` is the conjunction of their types, universes at `0`:
`isEquivalence_projLeft`, `degIndex_eq_x` (for an equivalence `G` and every admissible pair),
`theorem_10_2_2_right` (`π_X` an equivalence, `F ∘ π_X ≃ G ∘ π_Z`, `d = d_X ∘ π_X`, tameness and
paracompactness of the orbit space pass from `X`) and `theorem_10_2_2_both`
(`d_X(x) = d(x, ϕ, z) = d_Z(z)`).

`B` (blind) makes (a) the claims "`π_X` is an equivalence, `d = d_X ∘ π_X`" for an equivalence
`G` and (b) `d_X = d = d_Z` for two equivalences, about some ep-groupoid `E` on
`objSetB F G ⊆ X × 𝐘 × Z` with the sub-M-polyfold structure of the triple product (`IsWFPEpB`).

The comparison `toE : epGroupoid F G h → E` (an sc-smooth functor with sc-smooth inverse functor,
hence an equivalence) is copied from the V10_19 item file (same blind vocabulary, defeq).

* `B_to_A`: `π_X = πX ∘ toE` is an equivalence and the degeneracy indices transfer (from `B`
  (a), (b)).  In `theorem_10_2_2_right` the natural equivalence (the project's `natTrans`, the
  text's `τ(x, ϕ, z) = ϕ`, a definition of item V10_19), and the transfer of tameness and of a
  paracompact orbit space along the equivalence `π_X` (the general facts
  `EpFunctor.IsEquivalence.isTame_of_isTame`, `hasParacompactOrbitSpace`, items of V10_19) are
  not in `B` (a); they are obtained from these non-item lemmas.
* `A_to_B` is not proved, for the reason of V10_19 and V10_18: an `E` with `IsWFPEpB` needs the
  triple-product sub-M-polyfold structures on `objSetB`, `morSetB` and the transport of the
  ep-groupoid structure onto them, which the project does not prove (believed true). -/

set_option maxSynthPendingDepth 3

namespace RoundTrip.V10_20
open Polyfold Set Function WeakFibredProduct

/-! The project's statement (universes at `0`). -/
def A1 : Prop := type_of% @Polyfold.WeakFibredProduct.isEquivalence_projLeft.{0, 0, 0}
def A2 : Prop := type_of% @Polyfold.WeakFibredProduct.degIndex_eq_x.{0, 0, 0}
def A3 : Prop := type_of% @Polyfold.WeakFibredProduct.theorem_10_2_2_right.{0, 0, 0}
def A4 : Prop := type_of% @Polyfold.WeakFibredProduct.theorem_10_2_2_both.{0, 0, 0}

/-- The project's statement. -/
def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4

theorem A_holds : A :=
  ⟨@Polyfold.WeakFibredProduct.isEquivalence_projLeft.{0, 0, 0},
    @Polyfold.WeakFibredProduct.degIndex_eq_x.{0, 0, 0},
    @Polyfold.WeakFibredProduct.theorem_10_2_2_right.{0, 0, 0},
    @Polyfold.WeakFibredProduct.theorem_10_2_2_both.{0, 0, 0}⟩

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

/-- **`B` (a) for the project's `epGroupoid`**: `π_X` is an equivalence, `d = d_X ∘ π_X`. -/
theorem coreLeft (hB : B) (hG : G.IsEquivalence) (h : Admissible F G) :
    (projLeft F G h).IsEquivalence ∧
    ∀ p : WeakFibredProduct.Obj F G, (epGroupoid F G h).PObj.degIndex p = X.PObj.degIndex p.x := by
  obtain ⟨_, _, _, _, _, _, E, hE, ⟨πX, hXo, hXm, hπX⟩, hdeg⟩ :=
    (hB ObjX MorX ObjY MorY ObjZ MorZ X Y Z F G).1 hG
  refine ⟨?_, fun p => (degIndex_eq hE h p).trans (hdeg (eo p))⟩
  rw [projLeft_eq hE h πX hXo hXm]
  exact hπX.comp (isEquivalence_toE hE h)

/-- **`B` (b) for the project's `epGroupoid`**: `d_X = d = d_Z`. -/
theorem coreBoth (hB : B) (hF : F.IsEquivalence) (hG : G.IsEquivalence)
    (p : WeakFibredProduct.Obj F G) :
    X.PObj.degIndex p.x = (epGroupoid F G (.of_isEquivalence_left hF)).PObj.degIndex p ∧
      (epGroupoid F G (.of_isEquivalence_left hF)).PObj.degIndex p = Z.PObj.degIndex p.z := by
  obtain ⟨_, _, _, _, _, _, E, hE, hdeg⟩ := (hB ObjX MorX ObjY MorY ObjZ MorZ X Y Z F G).2 hF hG
  rw [degIndex_eq hE (.of_isEquivalence_left hF) p]
  exact hdeg (eo p)

end Core

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ObjX MorX _ _ _ _ _ _ ObjY MorY _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ X Y Z F G hG h
    exact (coreLeft hB hG h).1
  · intro ObjX MorX _ _ _ _ _ _ ObjY MorY _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ X Y Z F G hG h p
    exact (coreLeft hB hG h).2 p
  · intro ObjX MorX _ _ _ _ _ _ ObjY MorY _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ X Y Z F G hG
    obtain ⟨hπ, hdeg⟩ := coreLeft (F := F) hB hG (Admissible.of_isEquivalence_right hG)
    exact ⟨hπ, ⟨natTrans F G _⟩, hdeg, hπ.isTame_of_isTame, hπ.hasParacompactOrbitSpace⟩
  · intro ObjX MorX _ _ _ _ _ _ ObjY MorY _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ X Y Z F G hF hG p
    exact coreBoth hB hF hG p

#rt_check RoundTrip.V10_20.B_to_A [Polyfold.WeakFibredProduct.isEquivalence_projLeft,
  Polyfold.WeakFibredProduct.degIndex_eq_x, Polyfold.WeakFibredProduct.theorem_10_2_2_right,
  Polyfold.WeakFibredProduct.theorem_10_2_2_both]
#rt_overlap RoundTrip.V10_20.B_to_A [Polyfold.WeakFibredProduct.isEquivalence_projLeft,
  Polyfold.WeakFibredProduct.degIndex_eq_x, Polyfold.WeakFibredProduct.theorem_10_2_2_right,
  Polyfold.WeakFibredProduct.theorem_10_2_2_both]

end RoundTrip.V10_20
