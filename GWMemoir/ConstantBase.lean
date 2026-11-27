import GWMemoir.FibreInstance
import GWMemoir.Evaluation

/-!
# The base of the constant maps from the three-pointed sphere

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §3 (the polyfold structure
on `Z`, pp. 62–91), on the simplest honest piece of GW data: the full subcategory `C` of the
stable maps `S² → Q` of class `(k, δ)` with three marked points that are constant
(`gwSub (constOb om k δ)`).
Read against the 2021 book, Definitions 19.1.2–19.1.3 (uniformizers and uniformizer
constructions), the Properties (19.3), Definition 19.4.1 and Theorems 19.2.2, 19.5.3.

## What is formalized

* `constCat`: the category; every morphism is a unit (`constCat_mor_eq_unit`): an isomorphism of
  constant maps from `sphere3` is the identity of `sphere3` (`sphere3_iso_apply`, Liouville).
* `constUnif`: the uniformizer `Ψ : {1} ⋉ Q → C`, `Ψ(q) = (sphere3, u ≡ q)`, with `Q` as an
  M-polyfold of the constant scale (`manifoldMPolyfold`); its automorphism group is trivial, as for
  every constant stable map.  `constU`: the uniformizer construction `F(α) = {Ψ}` (Definition
  19.1.3).
* `constCS`: core-smoothness in the memoir's sense (pp. 27–28) for surfaces without nodes: the
  family `(q, z) ↦ φ_q(z)` of domain isomorphisms, read on `sphere3`, is sc-smooth on `V × S²`, i.e.
  smooth (constant scales).
* Proved, with no named proposition: **Proposition 3.10** (`constU_hasClassUniformizers`),
  **Theorem 3.13** (`constU_theorem_3_13`), `CSClosed` (`constU_csClosed`), `PointFinite`
  (`constU_pointFinite`), **Theorem 3.22** (`constU_theorem_3_22`) and **Theorem 1.6** (second
  countability, `constU_theorem_1_6_sc`) for every transition data, tangent-faithfulness and local
  faithfulness of the actions.
* **`memoir_polyfold_structure_const`**: `memoir_polyfold_structure` applies; the orbit space is
  metrizable, carries (ZHOU), is effective and has its polyfold class.  `constOrbitHomeomorph`:
  with the natural topology, `Z ≃ₜ Q`.

## Readings

* This category has no nodes, no gluing and no Deligne–Mumford parameters: it tests how the
  named propositions are wired to the book, not the analysis behind them.  The uniformizer is the
  inclusion of the open set `Q` itself; any open cover of `Q` would do as well.
* `O` and `G` live in the universe of `C`: `O = ULift Q`, `G = PUnit`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Set Function Filter Topology

noncomputable section

namespace GWMemoir

open Polyfold Polyfold.GroupoidalCategory

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-! ## 1. The category of constant maps -/

section Cat

variable (om : SymplecticForm E Q) (k : ℕ) (δ : ℝ)

/-- **The full subcategory of the constant stable maps from the three-pointed sphere.** -/
abbrev constCat : GroupoidalCategory.{1} := gwSub (constOb om k δ) constOb_finite

variable {om k δ}

/-- The object `(sphere3, u ≡ q)`. -/
def constObj (q : Q) : (constCat om k δ).Obj := ⟨constStableMap om q k δ, q, rfl⟩

theorem constObj_injective : Injective (constObj (om := om) (k := k) (δ := δ)) := by
  intro q q' h
  have h1 : constStableMap om q k δ = constStableMap om q' k δ := congrArg Subtype.val h
  have f : (constStableMap om q k δ).Iso (constStableMap om q' k δ) :=
    h1 ▸ StableMap.Iso.refl (constStableMap om q k δ)
  exact (eq_of_iso_const f).symm

theorem exists_constObj (a : (constCat om k δ).Obj) : ∃ q, constObj q = a := by
  obtain ⟨_, q, rfl⟩ := a
  exact ⟨q, rfl⟩

/-- **Every morphism of `constCat` is a unit**: an isomorphism `const q → const q'` forces
`q = q'` and is the identity of `sphere3`. -/
theorem constCat_mor_eq_unit (φ : (constCat om k δ).Mor) :
    φ = (constCat om k δ).toGroupoidStr.unit ((constCat om k δ).toGroupoidStr.src φ) := by
  obtain ⟨⟨α, β, f⟩, hα, hβ⟩ := φ
  obtain ⟨q, hq⟩ := hα
  obtain ⟨q', hq'⟩ := hβ
  change constStableMap om q k δ = α at hq
  change constStableMap om q' k δ = β at hq'
  subst hq hq'
  obtain rfl := eq_of_iso_const f
  have hf : f = StableMap.Iso.refl _ := StableMap.Iso.ext fun x => sphere3_iso_apply f.φ x
  subst hf
  rfl

theorem constCat_src_eq_tgt (φ : (constCat om k δ).Mor) :
    (constCat om k δ).toGroupoidStr.src φ = (constCat om k δ).toGroupoidStr.tgt φ := by
  conv_rhs => rw [constCat_mor_eq_unit φ]
  exact ((constCat om k δ).toGroupoidStr.tgt_unit _).symm

/-- **Transitions are determined by their source**: for uniformizers `Ψ, Ψ'` of `constCat`, two
elements of `M(Ψ, Ψ')` with the same source agree. -/
theorem trans_eq_of_src {Ψ Ψ' : (constCat om k δ).Uniformizer} {a b : Ψ.Trans Ψ'}
    (h : a.src = b.src) : a = b := by
  have hm : ∀ c : Ψ.Trans Ψ', c.mor = (constCat om k δ).toGroupoidStr.unit (Ψ.obj c.src) :=
    fun c => (constCat_mor_eq_unit c.mor).trans (congrArg _ c.src_mor)
  have ht : ∀ c : Ψ.Trans Ψ', Ψ'.obj c.tgt = Ψ.obj c.src := fun c =>
    c.tgt_mor.symm.trans ((constCat_src_eq_tgt c.mor).symm.trans c.src_mor)
  refine GroupoidStr.TransitionSet.ext h ?_ ?_
  · rw [hm a, hm b, h]
  · exact Ψ'.injective_obj ((ht a).trans (h ▸ (ht b).symm))

end Cat

/-! ## 2. The uniformizer and the uniformizer construction -/

section Unif

variable [T2Space Q] [ParacompactSpace Q] [SecondCountableTopology Q]

instance paracompactSpace_ulift {X : Type} [TopologicalSpace X] [ParacompactSpace X] :
    ParacompactSpace (ULift.{1} X) :=
  (Homeomorph.ulift.{1, 0} (X := X)).isClosedEmbedding.paracompactSpace

variable (E Q) in
/-- `Q` as an M-polyfold of the constant scale, on `ULift Q`. -/
abbrev qPoly : MPolyfold (ULift.{1} Q) := manifoldMPolyfold 𝓘(ℝ, E) Q Homeomorph.ulift

/-- The trivial action of `PUnit` on `ULift Q`. -/
@[instance_reducible] def trivAct : MulAction PUnit.{2} (ULift.{1} Q) where
  smul _ q := q
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

variable (om : SymplecticForm E Q) (k : ℕ) (δ : ℝ)

/-- The functor `{1} ⋉ Q → C`, `q ↦ (sphere3, u ≡ q)`, every morphism to a unit. -/
def constFunctor : @GroupoidFunctor _ _ _ _
    (@GroupoidStr.translation PUnit.{2} (ULift.{1} Q) _ trivAct)
    (constCat om k δ).toGroupoidStr :=
  letI := trivAct (Q := Q)
  { obj := fun q => constObj q.down
    mor := fun p => (constCat om k δ).toGroupoidStr.unit (constObj p.2.down)
    src_mor := fun _ => (constCat om k δ).toGroupoidStr.src_unit _
    tgt_mor := fun _ => (constCat om k δ).toGroupoidStr.tgt_unit _
    mor_comp := fun x y h => by
      have h' : x.2 = y.2 := h
      change (constCat om k δ).toGroupoidStr.unit (constObj y.2.down) =
        (constCat om k δ).toGroupoidStr.comp ((constCat om k δ).toGroupoidStr.unit
          (constObj x.2.down)) ((constCat om k δ).toGroupoidStr.unit (constObj y.2.down))
      rw [h']
      exact ((constCat om k δ).toGroupoidStr.unit_comp_of_eq
        ((constCat om k δ).toGroupoidStr.tgt_unit _)).symm
    mor_unit := fun _ => rfl }

/-- **The uniformizer of the constant maps** (2021 Definition 19.1.2): `O = Q` (constant scale),
`G = {1}`, `Ψ(q) = (sphere3, u ≡ q)`; fully faithful and injective on objects. -/
def constUnif : (constCat om k δ).Uniformizer where
  O := ULift.{1} Q
  P := qPoly E Q
  G := PUnit.{2}
  topG := ⊥
  discG := ⟨rfl⟩
  act := trivAct
  smooth_smul _ := (qPoly E Q).isScSmoothMap_id
  functor := constFunctor om k δ
  injective_obj q q' h := ULift.ext _ _ (constObj_injective h)
  full := by
    refine (GroupoidFunctor.full_iff _).2 fun q q' φ hs ht => ?_
    have hq : q = q' := ULift.ext _ _ (constObj_injective
      (hs.symm.trans ((constCat_src_eq_tgt φ).trans ht)))
    subst hq
    refine ⟨(PUnit.unit, q), rfl, rfl, ?_⟩
    change (constCat om k δ).toGroupoidStr.unit (constObj q.down) = φ
    rw [constCat_mor_eq_unit φ, hs]
    rfl
  faithful := by
    refine (GroupoidFunctor.faithful_iff _).2 fun p p' hs _ _ => ?_
    exact Prod.ext (Subsingleton.elim _ _) hs

theorem constUnif_obj (q : (constUnif om k δ).O) :
    (constUnif om k δ).obj q = constObj (ULift.down q) := rfl

/-- **The uniformizer construction** `F(α) = {Ψ}` (2021 Definition 19.1.3). -/
def constU : (constCat om k δ).UniformizerConstruction where
  F _ := {constUnif om k δ}
  isAt α Ψ h := by
    rw [mem_singleton_iff.1 h]
    obtain ⟨q, rfl⟩ := exists_constObj α
    exact ⟨ULift.up q, rfl⟩

variable {om k δ}

theorem constU_unif_eq (Ψ : (constU om k δ).Unif) : Ψ.1 = constUnif om k δ :=
  let ⟨_, _, h⟩ := Ψ
  mem_singleton_iff.1 h

variable (om k δ) in
/-- **Memoir Proposition 3.10 on the constant maps**: every class meets a uniformizer. -/
theorem constU_hasClassUniformizers : (constU om k δ).HasClassUniformizers :=
  UniformizerConstruction.HasUniformizers.hasClassUniformizers fun _ => ⟨_, rfl⟩

theorem constUnif_surjective (a : (constCat om k δ).Obj) :
    ∃ q : (constUnif om k δ).O, (constUnif om k δ).obj q = a := by
  obtain ⟨q, rfl⟩ := exists_constObj a
  exact ⟨ULift.up q, rfl⟩

end Unif

/-! ## 3. Core-smoothness and Theorem 3.13 -/

section Core

variable {om : SymplecticForm E Q} {k : ℕ} {δ : ℝ}

/-- The domain of a constant map from `sphere3` is `S²`. -/
theorem domEq {α : StableMap om 3 k δ} (h : α ∈ constOb om k δ) : α.dom.S = S2 := by
  obtain ⟨q, rfl⟩ := h
  rfl

/-- **The domain isomorphism of a morphism, read on the core `S²`** (memoir pp. 27–28): for
`φ : α → β`, the diffeomorphism `S_α → S_β` with both surfaces identified with `S²`. -/
def coreMap (φ : (constCat om k δ).Mor) (z : S2) : S2 :=
  cast (domEq φ.2.2) (φ.1.2.2.φ.φ (cast (domEq (α := φ.1.1) φ.2.1).symm z))

/-- Every domain isomorphism of `constCat` is the identity of `S²`. -/
theorem coreMap_eq (φ : (constCat om k δ).Mor) (z : S2) : coreMap φ z = z := by
  obtain ⟨⟨α, β, f⟩, hα, hβ⟩ := φ
  obtain ⟨q, hq⟩ := hα
  obtain ⟨q', hq'⟩ := hβ
  change constStableMap om q k δ = α at hq
  change constStableMap om q' k δ = β at hq'
  subst hq hq'
  exact sphere3_iso_apply f.φ z

/-- `S²` as an M-polyfold (constant scale). -/
abbrev s2Poly : MPolyfold S2 := manifoldMPolyfold 𝓘(ℝ, E2) S2 (Homeomorph.refl S2)

variable [T2Space Q] [ParacompactSpace Q] [SecondCountableTopology Q]

variable (om k δ) in
/-- **Core-smoothness** (memoir pp. 27–28, surfaces without nodes, the core being all of `S²`):
the family `(q, z) ↦ φ_q(z)` of domain isomorphisms of the germ `q ↦ Φ(q)` is sc-smooth on
`V × S²`, which for the constant scales is smoothness. -/
def constCS : CSPred (constU om k δ) := fun Ψ _ Φ V =>
  letI := MPolyfold.paracompactSpace_prod Ψ.1.P s2Poly
  (Ψ.1.P.prod s2Poly).IsScSmoothOn s2Poly (fun x => coreMap (Φ x.1).mor x.2) (V ×ˢ univ)

/-- Core-smoothness holds exactly on the open sets: the domain isomorphisms are all `id_{S²}`. -/
theorem constCS_iff {Ψ Ψ' : (constU om k δ).Unif} {Φ : Ψ.1.O → Ψ.1.Trans Ψ'.1} {V : Set Ψ.1.O} :
    constCS om k δ Ψ Ψ' Φ V ↔ IsOpen V := by
  let _ := MPolyfold.paracompactSpace_prod Ψ.1.P s2Poly
  constructor
  · intro h
    have ho : IsOpen (V ×ˢ (univ : Set S2)) := h.isOpen
    have hc : Continuous fun q : Ψ.1.O => (q, (pt 0 : S2)) := continuous_id.prodMk continuous_const
    have := ho.preimage hc
    rwa [show (fun q : Ψ.1.O => (q, (pt 0 : S2))) ⁻¹' (V ×ˢ univ) = V by ext q; simp] at this
  · intro hV
    have he : (fun x : Ψ.1.O × S2 => coreMap (Φ x.1).mor x.2) = Prod.snd :=
      funext fun x => coreMap_eq _ _
    change (Ψ.1.P.prod s2Poly).IsScSmoothOn s2Poly (fun x => coreMap (Φ x.1).mor x.2) _
    rw [he]
    exact (MPolyfold.isScSmoothMap_snd Ψ.1.P s2Poly).mono (hV.prod isOpen_univ) (subset_univ _)

/-- **`CSClosed` on the constant maps**: core-smoothness is closed under the operations on germs. -/
theorem constU_csClosed : CSClosed (constU om k δ) (constCS om k δ) where
  hat _ _ := constCS_iff.2 isOpen_univ
  transl _ _ _ _ _ h := constCS_iff.2 (constCS_iff.1 h)
  inv _ _ _ _ _ _ _ _ hd := constCS_iff.2 hd.isOpen_target
  comp _ _ _ _ _ _ _ _ _ _ h1 h1' _ _ hc := constCS_iff.2 (hc.isOpen_inter_preimage h1 h1')

/-- **Memoir Theorem 3.13 on the constant maps** (p. 70): every `h ∈ M(Ψ, Ψ')` extends to a
core-smooth transition germ, unique near `s(h)`. -/
theorem constU_theorem_3_13 : Theorem_3_13 (constU om k δ) (constCS om k δ) := by
  intro Ψ Ψ' h
  have e : Ψ' = Ψ := Subtype.ext ((constU_unif_eq Ψ').trans (constU_unif_eq Ψ).symm)
  subst e
  refine ⟨⟨univ, fun q => Ψ'.1.hat (1, q), ?_⟩, fun V₁ Φ₁ V₂ Φ₂ g₁ g₂ => ?_⟩
  · have hh : Ψ'.1.hat (1, h.src) = h := trans_eq_of_src rfl
    have := hatGerm constU_csClosed Ψ' 1 h.src
    rw [hh] at this
    exact this
  · exact ⟨V₁ ∩ V₂, g₁.1.inter g₂.1, ⟨g₁.2.1, g₂.2.1⟩, subset_rfl, fun q hq =>
      trans_eq_of_src ((g₁.2.2.2.1 q hq.1).trans (g₂.2.2.2.1 q hq.2).symm)⟩

/-- **The family `F(α) = {Ψ}` is point-finite.** -/
theorem constU_pointFinite : PointFinite (constU om k δ) := fun Ψ _ =>
  (Set.finite_singleton Ψ).subset fun Ψ' _ => mem_singleton_iff.2
    (Subtype.ext ((constU_unif_eq Ψ').trans (constU_unif_eq Ψ).symm))

end Core

/-! ## 4. Theorems 3.22 and 1.6, and the polyfold structure on `Z` -/

section Structure

variable {om : SymplecticForm E Q} {k : ℕ} {δ : ℝ}
variable [T2Space Q] [ParacompactSpace Q] [SecondCountableTopology Q] [Nonempty Q]
variable (T : (constU om k δ).TransitionData)

/-- The natural topology `T` of `Z` (Definition 19.2.1) for the transition data `T`. -/
abbrev constTop : TopologicalSpace (constCat om k δ).OrbitSpace :=
  (basicOf (constU om k δ) T).natTop (constU_hasClassUniformizers om k δ)

theorem continuous_constπ :
    Continuous[_, constTop T] fun q : (constUnif om k δ).O =>
      (constCat om k δ).π ((constUnif om k δ).obj q) :=
  (basicOf (constU om k δ) T).continuous_π_obj (constU_hasClassUniformizers om k δ)
    (α := constObj (Classical.arbitrary Q)) (mem_singleton _)

theorem surjective_constπ :
    Surjective fun q : (constUnif om k δ).O => (constCat om k δ).π ((constUnif om k δ).obj q) := by
  intro z
  obtain ⟨a, rfl⟩ := (constCat om k δ).toGroupoidStr.surjective_π z
  obtain ⟨q, hq⟩ := constUnif_surjective a
  exact ⟨q, congrArg (constCat om k δ).π hq⟩

theorem injective_constπ :
    Injective fun q : (constUnif om k δ).O => (constCat om k δ).π ((constUnif om k δ).obj q) := by
  intro o o' h
  obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 h
  have h1 := constCat_src_eq_tgt φ
  rw [hs, ht] at h1
  exact ULift.ext _ _ (constObj_injective h1)

/-- **With the natural topology, `Z ≃ₜ Q`**: `q ↦ |Ψ(q)|` is a continuous open bijection
(Theorem 19.2.2 (2)). -/
def constOrbitHomeomorph : @Homeomorph Q (constCat om k δ).OrbitSpace _ (constTop T) :=
  let _ := constTop T
  Homeomorph.ulift.symm.trans
    ((Equiv.ofBijective _ ⟨injective_constπ, surjective_constπ⟩).toHomeomorphOfContinuousOpen
      (continuous_constπ T) fun _ hV =>
        (basicOf (constU om k δ) T).theorem_19_2_2_two (constU_hasClassUniformizers om k δ)
          (α := constObj (Classical.arbitrary Q)) (mem_singleton _) hV)

/-- `Z` is metrizable: `|Ψ|` is onto (2021 Theorem 19.2.2 (3)). -/
theorem constU_metrizable : @TopologicalSpace.MetrizableSpace _ (constTop T) :=
  (basicOf (constU om k δ) T).metrizableSpace_natTop_of_surjective
    (constU_hasClassUniformizers om k δ) (α := constObj (Classical.arbitrary Q))
    (Ψ := constUnif om k δ) (mem_singleton _) surjective_constπ

/-- **Memoir Theorem 3.22 on the constant maps** (properness (v1) of Definition 19.4.1), for every
transition data: from the metrizability of `Z` (Propositions 19.4.7 and 19.4.2). -/
theorem constU_theorem_3_22 : Theorem_3_22 (constU om k δ) T :=
  ((basicOf (constU om k δ) T).proposition_19_4_2_one_iff_two
      (constU_hasClassUniformizers om k δ)).2
    (((basicOf (constU om k δ) T).proposition_19_4_7 (constU_hasClassUniformizers om k δ)).1
      (constU_metrizable T)).1

instance secondCountableTopology_ulift {X : Type} [TopologicalSpace X]
    [SecondCountableTopology X] : SecondCountableTopology (ULift.{1} X) :=
  (Homeomorph.ulift.{1, 0} (X := X)).isEmbedding.secondCountableTopology

/-- **Memoir Theorem 1.6, second countability, on the constant maps**, for every transition
data: `Z` is the continuous image of the separable `Q`, and metrizable. -/
theorem constU_theorem_1_6_sc :
    Theorem_1_6_sc (constU om k δ) T (constU_hasClassUniformizers om k δ) := by
  let _ := constTop T
  have := constU_metrizable T
  have : TopologicalSpace.SeparableSpace (constUnif om k δ).O :=
    inferInstanceAs (TopologicalSpace.SeparableSpace (ULift.{1} Q))
  have : TopologicalSpace.SeparableSpace (constCat om k δ).OrbitSpace :=
    surjective_constπ.denseRange.separableSpace (continuous_constπ T)
  let _ := TopologicalSpace.pseudoMetrizableSpaceUniformity (constCat om k δ).OrbitSpace
  have := TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated
    (constCat om k δ).OrbitSpace
  exact UniformSpace.secondCountable_of_separable _

/-- The actions are tangent-faithful at every smooth point (`G = {1}`). -/
theorem constU_tangentFaithful : ∀ (α : (constCat om k δ).Obj), ∀ Ψ ∈ (constU om k δ).F α,
    ∀ y : Ψ.P.SmoothLevel, IsTangentFaithfulAt Ψ y := by
  intro α Ψ hΨ y g _ _
  obtain rfl := mem_singleton_iff.1 hΨ
  exact Subsingleton.elim (α := PUnit.{2}) _ _

/-- The actions are locally faithful (`G = {1}`). -/
theorem constU_locallyFaithful : ∀ (α : (constCat om k δ).Obj), ∀ Ψ ∈ (constU om k δ).F α,
    IsLocallyFaithful Ψ := by
  intro α Ψ hΨ g _ _
  obtain rfl := mem_singleton_iff.1 hΨ
  exact Subsingleton.elim (α := PUnit.{2}) _ _

variable (om k δ) in
/-- The transition data of Theorem 3.13 on the constant maps (`reduction_3_13`). -/
abbrev constT : (constU om k δ).TransitionData :=
  gwTransitionData constU_theorem_3_13 constU_csClosed constU_pointFinite

variable (om k δ) in
/-- **The polyfold structure of `Z` on the constant maps from the three-pointed sphere**, with no
named proposition (memoir Theorem 1.6 through `memoir_polyfold_structure`): all its hypotheses
hold — Proposition 3.10, Theorem 3.13 for the core-smoothness `constCS`, `CSClosed`,
`PointFinite`, Theorems 3.22 and 1.6 (second countability), and the faithfulness of the
actions — and `Z` is metrizable, with (ZHOU), effective, with its polyfold class.

This category has no nodes and no gluing: the statement checks the wiring of the named
propositions to the book (Chapters 17 and 19), not the analysis of the memoir. -/
theorem memoir_polyfold_structure_const :
    ∃ (hm : @TopologicalSpace.MetrizableSpace (constCat om k δ).OrbitSpace
        ((basicOf (constU om k δ) (constT om k δ)).natTop (constU_hasClassUniformizers om k δ))),
      (basicOf (constU om k δ) (constT om k δ)).IsZhou ∧
      (BasicConstruction.toPolyfoldConstruction hm).IsZhou ∧
      (BasicConstruction.toPolyfoldConstruction hm).IsEffective ∧
        Nonempty (PolyfoldClass ((basicOf (constU om k δ) (constT om k δ)).toGCTOfMetrizable
          (constU_hasClassUniformizers om k δ) hm).toGroupoidStr.OrbitSpace) :=
  memoir_polyfold_structure (constU_hasClassUniformizers om k δ) constU_theorem_3_13
    constU_csClosed constU_pointFinite (constU_theorem_3_22 _) (constU_theorem_1_6_sc _)
    constU_tangentFaithful constU_locallyFaithful

end Structure

end GWMemoir
