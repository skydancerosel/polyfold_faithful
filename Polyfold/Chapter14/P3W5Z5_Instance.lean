import Polyfold.Chapter14.P3W5Z5_LimitExists
import Polyfold.Chapter14.P3W4S3_CoverVHat

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 14,
§§14.3–14.4, pp. 656–671: the data of §14.4 built from the objects of §14.3, and
**Proposition 14.4.6 (2)**, **Proposition 14.4.10**, the coherent neighbourhood systems and
**Proposition 14.4.14** for them (2017 text: Propositions 14.4–14.7).

# The §14.4 setting from the §14.3 objects

## What is formalized

The objects of §14.3 are indexed by boundary points `x : ∂X` (a subtype), the §14.4 setting
(`ZData`, `ZSections`) by objects.  A retraction `bdryRetr_z5 x₀ : X → ∂X` (the identity on `∂X`)
and the identification `isoRetr_z5 : G_a → G_{r(a)}` (the identity for `a ∈ ∂X`) carry them over
without casts; values at objects outside `∂X` are irrelevant (`A ⊆ ∂X`).

* `ZConcrete E Q`: the data of Proposition 14.3.8 (`A`, `Ṽ_a`, `V̂_a` with the properties
  proved there) for a correspondence extension `E` (Lemma 14.3.1 on (P4), (P5)) and (P6)
  neighbourhoods `Q`; `ZConcrete.exists_` (from `CorrExtension.proposition_14_3_8`) and
  `exists_zConcrete_of_hasP4` (the whole chain from (P4) and `|X|` paracompact).
* `ZConcrete.toZData` (B2's and Z4's setting: `Ũ(a)`, `V̂_a`, `I_a`, `τ̂_{a,a'}` with
  Definition 13.3.6 (1), (2) on `V̂_a` and the local constancy of `τ̂`), `ZConcrete.toLimit` (the
  facts of §14.3 for Proposition 14.4.6 (2)), `ZConcrete.toZSections` (the boundary sections `sˣᵢ`
  of the tuple `T`), `ZConcrete.compatNbhd` (Definition 14.1.7 (4) through `τ̂ = τ⁰`).
* For these data, with no hypothesis beyond the text's: `ZConcrete.proposition_14_4_6_2`,
  `ZConcrete.proposition_14_4_10`, `ZConcrete.exists_zCoherentNbhdSystem`,
  `ZConcrete.proposition_14_4_14`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-- A pair of a correspondence is a pair at which every condition it satisfies holds. -/
theorem IndexCorr.sat_pairs_z5 {α β : Type u} {R : α → β → Prop} {τ : IndexCorr α β}
    (h : τ.Sat R) {i : α} {j : β} (hp : τ.Pairs i j) : R i j := by
  revert h hp
  refine IndexCorr.ind (fun d h hp => ?_) τ
  obtain ⟨k, rfl, rfl⟩ := hp
  exact h k

/-! ### From boundary points to objects -/

open scoped Classical in
/-- A retraction of the objects onto `∂X`: the identity on `∂X`, `x₀` elsewhere. -/
def bdryRetr_z5 (x₀ : A.X.PObj.boundary) (a : A.Obj) : A.X.PObj.boundary :=
  if h : a ∈ A.X.PObj.boundary then ⟨a, h⟩ else x₀

theorem bdryRetr_z5_of_mem (x₀ : A.X.PObj.boundary) {a : A.Obj} (h : a ∈ A.X.PObj.boundary) :
    bdryRetr_z5 x₀ a = ⟨a, h⟩ := by
  unfold bdryRetr_z5
  exact dif_pos h

theorem coe_bdryRetr_z5_of_mem (x₀ : A.X.PObj.boundary) {a : A.Obj}
    (h : a ∈ A.X.PObj.boundary) : (bdryRetr_z5 x₀ a : A.Obj) = a := by
  rw [bdryRetr_z5_of_mem x₀ h]

open scoped Classical in
/-- `G_a → G_{r(a)}`: the identity of morphisms for `a ∈ ∂X` (trivial elsewhere). -/
def isoRetr_z5 (x₀ : A.X.PObj.boundary) (a : A.Obj) :
    A.X.Isotropy a →* A.X.Isotropy (bdryRetr_z5 x₀ a : A.Obj) :=
  if h : (bdryRetr_z5 x₀ a : A.Obj) = a then
    MonoidHom.mk' (fun g => ⟨g.val, g.src_val.trans h.symm, g.tgt_val.trans h.symm⟩)
      (fun _ _ => GroupoidStr.Isotropy.ext rfl)
  else 1

theorem isoRetr_z5_val (x₀ : A.X.PObj.boundary) {a : A.Obj} (h : a ∈ A.X.PObj.boundary)
    (g : A.X.Isotropy a) : (isoRetr_z5 x₀ a g).val = g.val := by
  unfold isoRetr_z5
  rw [dif_pos (coe_bdryRetr_z5_of_mem x₀ h)]
  rfl

/-- For a family of neighbourhoods indexed by `∂X`, the natural action at `r(a)` through
`isoRetr_z5` is the natural action at `a`. -/
theorem rep_isoRetr_z5 (x₀ : A.X.PObj.boundary) (N : ∀ x : A.X.PObj.boundary, A.X.NatNbhd x)
    {a : A.Obj} (h : a ∈ A.X.PObj.boundary) (g : A.X.Isotropy a) (w : A.Obj) :
    (N (bdryRetr_z5 x₀ a)).rep.Γ (isoRetr_z5 x₀ a g) w = (N ⟨a, h⟩).rep.Γ g w ∧
    (N (bdryRetr_z5 x₀ a)).rep.Φ (isoRetr_z5 x₀ a g) w = (N ⟨a, h⟩).rep.Φ g w := by
  have key : ∀ (x : A.X.PObj.boundary), x = ⟨a, h⟩ → ∀ g' : A.X.Isotropy (x : A.Obj),
      g'.val = g.val →
      (N x).rep.Γ g' w = (N ⟨a, h⟩).rep.Γ g w ∧ (N x).rep.Φ g' w = (N ⟨a, h⟩).rep.Φ g w := by
    rintro x rfl g' hg
    have : g' = g := GroupoidStr.Isotropy.ext hg
    subst this
    exact ⟨rfl, rfl⟩
  exact key _ (bdryRetr_z5_of_mem x₀ h) _ (isoRetr_z5_val x₀ h g)

/-- Relabelling the group along `isoRetr_z5` does not change `[I ←id I →g I]`. -/
theorem ofPerm_isoRetr_z5 {α : Type u} [Fintype α] (x₀ : A.X.PObj.boundary) (a : A.Obj)
    [MulAction (A.X.Isotropy (bdryRetr_z5 x₀ a : A.Obj)) α] (g : A.X.Isotropy a) :
    @IndexCorr.ofPerm α (A.X.Isotropy a) _ _ (MulAction.compHom α (isoRetr_z5 x₀ a)) g =
      IndexCorr.ofPerm (isoRetr_z5 x₀ a g) :=
  IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩

/-! ### The data of Proposition 14.3.8 -/

variable {T : BoundaryStructuredTuple A} {P : P5Nbhds T}

/-- **The data of Proposition 14.3.8** (p. 656) for a correspondence extension `E` and (P6)
neighbourhoods `Q`: `A ⊆ ∂X`, `Ṽ_a ⊆ Ũ(a)` with `cl_{|X|}|Ṽ_a| ⊆ |Ũ(a)|`, and open invariant
`V̂_a ⊆ Ṽ_a` with `(|V̂_a|)` locally finite and `V̂_{a,a'} ⊆ Ô_{a,a'}`; `x₀ ∈ ∂X` fixes the
irrelevant values off `∂X`. -/
structure ZConcrete (E : CorrExtension T P) (Q : P5Nbhds.P6Nbhds P) where
  x₀ : A.X.PObj.boundary
  Aset : Set A.Obj
  Vt : A.Obj → Set A.Obj
  Vh : A.Obj → Set A.Obj
  A_subset : Aset ⊆ A.X.PObj.boundary
  Vt_subset : ∀ a ∈ Aset, Vt a ⊆ (Q.nbhdObj a).U
  closure_π_Vt : ∀ a ∈ Aset, closure (A.X.π '' Vt a) ⊆ A.X.π '' (Q.nbhdObj a).U
  isOpen_Vh : ∀ a ∈ Aset, IsOpen (Vh a)
  Vh_subset : ∀ a ∈ Aset, Vh a ⊆ Vt a
  mapsTo_Vh : ∀ a ∈ Aset, ∀ g, MapsTo ((Q.nbhdObj a).rep.Φ g) (Vh a) (Vh a)
  locallyFinite : LocallyFinite fun a : Aset => A.X.π '' Vh a
  cover : A.X.π '' A.X.PObj.boundary ⊆ ⋃ a ∈ Aset, A.X.π '' Vh a
  morBetween_subset : ∀ a ∈ Aset, ∀ a' ∈ Aset, A.X.morBetween (Vh a) (Vh a') ⊆ E.OhatObj a a'

namespace ZConcrete

/-- **The data exist** (Proposition 14.3.8, with Lemma 14.3.6), for `|X|` paracompact and
`∂X ≠ ∅`. -/
theorem exists_ (E : CorrExtension T P) (hpara : A.X.HasParacompactOrbitSpace)
    (Q : P5Nbhds.P6Nbhds P) (x₀ : A.X.PObj.boundary) : Nonempty (ZConcrete E Q) := by
  obtain ⟨Aset, Vt, Vh, hAB, hVt, -, hVh, -, ⟨-, hlf, hcov⟩, hO⟩ := E.proposition_14_3_8 hpara Q
  exact ⟨⟨x₀, Aset, Vt, Vh, hAB, fun a ha => (hVt a ha).2.2.1, fun a ha => (hVt a ha).2.2.2.1,
    fun a ha => (hVh a ha).1, fun a ha => (hVh a ha).2.1, fun a ha => (hVh a ha).2.2, hlf, hcov,
    hO⟩⟩

variable {E : CorrExtension T P} {Q : P5Nbhds.P6Nbhds P} (C : ZConcrete E Q)

theorem isProper (a : A.Obj) (ha : a ∈ A.X.PObj.boundary) :
    A.X.IsProperSubset (closure (Q.nbhdObj a).U) := by
  rw [Q.nbhdObj_of_mem ha]
  exact Q.isProperSubset_closure _

theorem closure_Vh_subset {a : A.Obj} (ha : a ∈ C.Aset) : closure (C.Vh a) ⊆ (Q.nbhdObj a).U :=
  (closure_mono (C.Vh_subset a ha)).trans
    ((A.X.lemma_13_1_1 (Q.nbhdObj a) (isProper a (C.A_subset ha)) (C.Vt_subset a ha)).2
      (C.closure_π_Vt a ha))

theorem Vh_subset_P {a : A.Obj} (ha : a ∈ C.Aset) :
    C.Vh a ⊆ (P.nbhd (bdryRetr_z5 C.x₀ a)).U := by
  have h := (C.Vh_subset a ha).trans (C.Vt_subset a ha)
  rw [Q.nbhdObj_of_mem (C.A_subset ha)] at h
  rw [bdryRetr_z5_of_mem C.x₀ (C.A_subset ha)]
  exact h.trans (Q.subset _)

theorem mapsTo_Vh_P {a : A.Obj} (ha : a ∈ C.Aset)
    (g : A.X.Isotropy (bdryRetr_z5 C.x₀ a : A.Obj)) :
    MapsTo ((P.nbhd (bdryRetr_z5 C.x₀ a)).rep.Φ g) (C.Vh a) (C.Vh a) := by
  have hb := C.A_subset ha
  have key : ∀ x : A.X.PObj.boundary, x = ⟨a, hb⟩ → ∀ g' : A.X.Isotropy (x : A.Obj),
      MapsTo ((P.nbhd x).rep.Φ g') (C.Vh a) (C.Vh a) := by
    rintro x rfl g'
    have := C.mapsTo_Vh a ha g'
    rwa [Q.nbhdObj_of_mem hb, Q.rep_eq] at this
  exact key _ (bdryRetr_z5_of_mem C.x₀ hb) g

theorem morBetween_subset_Ohat {a b : A.Obj} (ha : a ∈ C.Aset) (hb : b ∈ C.Aset) :
    A.X.morBetween (C.Vh a) (C.Vh b) ⊆ E.Ohat (bdryRetr_z5 C.x₀ a) (bdryRetr_z5 C.x₀ b) := by
  rw [bdryRetr_z5_of_mem C.x₀ (C.A_subset ha), bdryRetr_z5_of_mem C.x₀ (C.A_subset hb),
    ← E.OhatObj_of_mem]
  exact C.morBetween_subset a ha b hb

/-- `Ũ(a) ∩ ∂X ⊆ U⁰(r(a))`, where the boundary sections live. -/
theorem mem_bdry {a : A.Obj} (ha : a ∈ C.Aset) {y : A.Obj}
    (hy : y ∈ (Q.nbhdObj a).U ∩ A.X.PObj.boundary) :
    y ∈ T.dec.𝒰.U (bdryRetr_z5 C.x₀ a) := by
  have hb := C.A_subset ha
  rw [bdryRetr_z5_of_mem C.x₀ hb, ← P.inter_boundary]
  rw [Q.nbhdObj_of_mem hb] at hy
  exact ⟨Q.subset _ hy.1, hy.2⟩

/-- **The setting of §14.4** (B2's `ZSetup` with Z4's three facts) from the data of §14.3. -/
def toZData : A.X.ZData where
  A := C.Aset
  nbhd := Q.nbhdObj
  V := C.Vh
  V_subset a ha := (C.Vh_subset a ha).trans (C.Vt_subset a ha)
  mapsTo_V := C.mapsTo_Vh
  I a := (T.dec.S (bdryRetr_z5 C.x₀ a)).I
  fintype _ := inferInstance
  mulAction a := MulAction.compHom _ (isoRetr_z5 C.x₀ a)
  τ a a' := E.tauHat (bdryRetr_z5 C.x₀ a) (bdryRetr_z5 C.x₀ a')
  diag a ha g w hw := by
    have hb := C.A_subset ha
    have e₁ : (Q.nbhdObj a).rep.Γ g w =
        (P.nbhd (bdryRetr_z5 C.x₀ a)).rep.Γ (isoRetr_z5 C.x₀ a g) w := by
      rw [(rep_isoRetr_z5 C.x₀ P.nbhd hb g w).1, Q.nbhdObj_of_mem hb, Q.rep_eq]
    rw [e₁, E.tauHat_Γ_of_VHat (C.Vh_subset_P ha) (C.mapsTo_Vh_P ha)
      (C.morBetween_subset_Ohat ha ha) _ hw]
    exact (ofPerm_isoRetr_z5 C.x₀ a g).symm
  swap a ha a' ha' φ hs ht := E.tauHat_inv_of_VHat (C.morBetween_subset_Ohat ha ha') hs ht
  isOpen_V := C.isOpen_Vh
  closure_V_subset _ ha := C.closure_Vh_subset ha
  locallyConstant a ha a' ha' φ hs ht :=
    E.tauHat_locallyConstant (E.Ohat_subset_Ot _ _ (C.morBetween_subset_Ohat ha ha' ⟨hs, ht⟩))

/-- **The facts of §14.3 used by Proposition 14.4.6 (2)**, for these data: `M b c = Ô_{b,c}`,
(P6) properness, Proposition 14.3.8 (3). -/
def toLimit : ZLimitSetting C.toZData where
  M b c := E.Ohat (bdryRetr_z5 C.x₀ b) (bdryRetr_z5 C.x₀ c)
  isOpen_M _ _ _ _ := E.isOpen_Ohat _ _
  locallyConstant_M _ _ _ _ _ hφ := E.tauHat_locallyConstant (E.Ohat_subset_Ot _ _ hφ)
  boundary_mem_M b hb c hc φ hs ht := by
    have hb' := C.A_subset hb
    have hc' := C.A_subset hc
    change A.X.src φ ∈ (Q.nbhdObj b).U ∩ A.X.PObj.boundary at hs
    change A.X.tgt φ ∈ closure (Q.nbhdObj c).U ∩ A.X.PObj.boundary at ht
    change φ ∈ E.Ohat (bdryRetr_z5 C.x₀ b) (bdryRetr_z5 C.x₀ c)
    rw [bdryRetr_z5_of_mem C.x₀ hb', bdryRetr_z5_of_mem C.x₀ hc']
    refine E.mor_subset_Ohat _ _ ?_
    rw [← P.mor_inter_boundaryMor]
    rw [Q.nbhdObj_of_mem hb'] at hs
    rw [Q.nbhdObj_of_mem hc'] at ht
    exact ⟨⟨Q.subset _ hs.1, Q.closure_subset _ ht.1⟩, hs.2, ht.2⟩
  isProper b hb := isProper b (C.A_subset hb)
  locallyFinite := C.locallyFinite

/-- **Definition 14.1.7 (4) through `τ̂ = τ⁰`** (Proposition 14.3.4): along a morphism of `∂X`
from `Ũ(b)` to `Ũ(c)`, the boundary sections are related by every pair of `τ̂_{b,c}(φ)`. -/
theorem compat_aux {b c : A.Obj} (hb : b ∈ C.Aset) (hc : c ∈ C.Aset) {φ : A.Mor}
    (hs : A.X.src φ ∈ (Q.nbhdObj b).U ∩ A.X.PObj.boundary) (ht : A.X.tgt φ ∈ (Q.nbhdObj c).U)
    {i : (T.dec.S (bdryRetr_z5 C.x₀ b)).I} {j : (T.dec.S (bdryRetr_z5 C.x₀ c)).I}
    (hp : (E.tauHat (bdryRetr_z5 C.x₀ b) (bdryRetr_z5 C.x₀ c) φ).Pairs i j) :
    (T.dec.S (bdryRetr_z5 C.x₀ c)).s j (A.X.tgt φ) =
      fibAct φ ((T.dec.S (bdryRetr_z5 C.x₀ b)).s i (A.X.src φ)) := by
  have htb : A.X.tgt φ ∈ A.X.PObj.boundary := (tgt_mem_boundary_iff_z4 φ).2 hs.2
  have hφ : φ ∈ T.dec.𝒰.mor (bdryRetr_z5 C.x₀ b) (bdryRetr_z5 C.x₀ c) :=
    ⟨C.mem_bdry hb hs, C.mem_bdry hc ⟨ht, htb⟩⟩
  have hsat := T.tau.compat _ _ φ hφ
  rw [← E.tauHat_eq_tau hφ] at hsat
  exact IndexCorr.sat_pairs_z5 hsat hp

/-- **The boundary data of §14.4**: the sections `sˣᵢ` of the tuple `T` at `x = a ∈ A`. -/
def toZSections : ZSections A C.toZData where
  s a i y := (T.dec.S (bdryRetr_z5 C.x₀ a)).s i y
  P_s a ha i y hy := (T.dec.S _).P_s i (C.mem_bdry ha hy)
  equivariant a ha g i y hy := by
    have hb := C.A_subset ha
    have e := (T.dec.S (bdryRetr_z5 C.x₀ a)).equivariant (isoRetr_z5 C.x₀ a g) i y
      (C.mem_bdry ha hy)
    rw [(rep_isoRetr_z5 C.x₀ T.dec.𝒰.nbhd hb g y).1,
      (rep_isoRetr_z5 C.x₀ T.dec.𝒰.nbhd hb g y).2, ← P.rep_eq, ← Q.rep_eq,
      ← Q.nbhdObj_of_mem hb] at e
    exact e
  compat a ha a' ha' φ hs ht i j hp :=
    C.compat_aux ha ha' ⟨(C.Vh_subset a ha).trans (C.Vt_subset a ha) hs.1, hs.2⟩
      ((C.Vh_subset a' ha').trans (C.Vt_subset a' ha') ht) hp

theorem compatNbhd : C.toZSections.CompatNbhd := fun _ hb _ hc _ hs ht _ _ hp =>
  C.compat_aux hb hc hs ht hp

/-! ### Proposition 14.4.6 (2), Proposition 14.4.10 and Proposition 14.4.14 for these data -/

/-- **Proposition 14.4.6 (2), p. 661 (2017: Proposition 14.5 (2))**, as printed, for the data of
§14.3. -/
theorem proposition_14_4_6_2 : proposition_14_4_6_2_statement C.toZSections :=
  proposition_14_4_6_2_of_limit C.toZSections C.toLimit C.compatNbhd

/-- Proposition 14.4.6 (2) in the form used by Lemma 14.4.9 (3), for the data of §14.3. -/
theorem hasThetaLocalEq : HasThetaLocalEq C.toZSections :=
  hasThetaLocalEq_of_limit C.toZSections C.toLimit C.compatNbhd

/-- **Proposition 14.4.10, p. 664 (2017: Proposition 14.6)**, for the data of §14.3. -/
theorem proposition_14_4_10 {a : A.Obj} (ha : a ∈ C.Aset) :
    ∃ O : A.Obj → Set A.Obj, ∀ z ∈ closure (C.Vh a), IsOpen (O z) ∧ z ∈ O z ∧
      O z ⊆ (Q.nbhdObj a).U ∧
      (∀ g, O ((Q.nbhdObj a).rep.Φ g z) = (Q.nbhdObj a).rep.Φ g '' O z) ∧
      (∀ g, (Q.nbhdObj a).rep.Φ g z ≠ z → Disjoint (O z) (O ((Q.nbhdObj a).rep.Φ g z))) ∧
      (∀ i, ∀ y ∈ O z ∩ C.Vh a, C.toZData.zClass a y i ⊆ C.toZData.approxClass a z i) ∧
      (z ∈ closure (C.Vh a ∩ A.X.PObj.boundary) → ∀ i i', C.toZData.Approx a z i i' →
        ∀ y ∈ O z ∩ ((Q.nbhdObj a).U ∩ A.X.PObj.boundary),
          (T.dec.S (bdryRetr_z5 C.x₀ a)).s i y = (T.dec.S (bdryRetr_z5 C.x₀ a)).s i' y) :=
  proposition_14_4_10_of_limit C.toZSections C.toLimit C.compatNbhd ha

/-- **Coherent neighbourhood systems exist** (Definition 14.4.11) for the data of §14.3. -/
theorem exists_zCoherentNbhdSystem {a : A.Obj} (ha : a ∈ C.Aset) :
    Nonempty (ZCoherentNbhdSystem C.toZSections a) :=
  exists_zCoherentNbhdSystem_of_limit C.toZSections C.toLimit C.compatNbhd ha

/-- The boundary sections are face-wise sc⁺ on `U(a) = Ũ(a) ∩ ∂X` (Definition 14.1.3 (1)). -/
theorem isFaceScPlus {a : A.Obj} (ha : a ∈ C.Aset) (i : C.toZData.I a) :
    IsFaceScPlusSectionOn A (C.toZSections.s a i) (C.toZData.nbhd a).bdry :=
  ((T.dec.S (bdryRetr_z5 C.x₀ a)).isFaceScPlus i).mono fun _ hy => C.mem_bdry ha hy

/-- **Proposition 14.4.14, pp. 667–671 (2017: Proposition 14.7)**, for the data of §14.3: for
`a ∈ A` there are sc⁺-sections `ŝᵃᵢ` on `V̂_a`, symmetric, equal to the boundary sections `sᵃᵢ`
of `T` on `V_a = V̂_a ∩ ∂X`, and equal for `i ∼_z i'`. -/
theorem proposition_14_4_14
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) {a : A.Obj} (ha : a ∈ C.Aset) :
    ∃ sh : C.toZData.I a → A.Obj → A.W, (∀ i, IsScPlusSectionOn A (sh i) (C.Vh a)) ∧
      (∀ (g : A.X.Isotropy a) i, ∀ y ∈ C.Vh a,
        sh (g • i) ((Q.nbhdObj a).rep.Φ g y) = fibAct ((Q.nbhdObj a).rep.Γ g y) (sh i y)) ∧
      (∀ i, ∀ y ∈ C.Vh a ∩ A.X.PObj.boundary,
        sh i y = (T.dec.S (bdryRetr_z5 C.x₀ a)).s i y) ∧
      ∀ y ∈ C.Vh a, ∀ i i', C.toZData.ZRel a y i i' → sh i y = sh i' y :=
  proposition_14_4_14_of_limit C.toZSections C.toLimit hB hpu C.compatNbhd ha (C.isFaceScPlus ha)

end ZConcrete

/-- **The whole chain is satisfiable**: from (P4) for the tuple, `|X|` paracompact and a boundary
point, there are (P5), the extension of Lemma 14.3.1, (P6) and the data of Proposition 14.3.8. -/
theorem exists_zConcrete_of_hasP4 (hT : T.HasP4) (hpara : A.X.HasParacompactOrbitSpace)
    (x₀ : A.X.PObj.boundary) :
    ∃ (P : P5Nbhds T) (E : CorrExtension T P) (Q : P5Nbhds.P6Nbhds P),
      Nonempty (ZConcrete E Q) := by
  obtain ⟨E⟩ := lemma_14_3_1 hT (P5Nbhds.ofGood T)
  obtain ⟨Q⟩ := P5Nbhds.P6Nbhds.exists_ (P5Nbhds.ofGood T)
  exact ⟨_, E, Q, ZConcrete.exists_ E hpara Q x₀⟩

/-- **Nonvacuity**: for a tame `X` with paracompact orbit space and `∂X ≠ ∅` there are a tuple
(the zero structured multisection, Proposition 14.2.3 for (P4)) and data of Proposition 14.3.8,
so the results above apply. -/
theorem exists_zConcrete_of_tame (hX : A.X.IsTame) (hpara : A.X.HasParacompactOrbitSpace)
    (x₀ : A.X.PObj.boundary) :
    ∃ (T' : BoundaryStructuredTuple A) (P' : P5Nbhds T') (E : CorrExtension T' P')
      (Q : P5Nbhds.P6Nbhds P'), Nonempty (ZConcrete E Q) := by
  obtain ⟨T₀, -⟩ := isBoundaryStructurable_iff.1 (isBoundaryStructurable_zero hX hpara)
  obtain ⟨T', -, -, -, hT'⟩ := BoundaryStructuredTuple.proposition_14_2_3 hX T₀
  obtain ⟨P', E, Q, hC⟩ := exists_zConcrete_of_hasP4 hT' hpara x₀
  exact ⟨T', P', E, Q, hC⟩

end SBLocalization

end Polyfold
