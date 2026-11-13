import Polyfold.Chapter14.P3W4LX_LocalExtension
import Polyfold.Chapter14.P3W3B2_ZLoops

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.4, pp. 664–671:
**Definition 14.4.11** (coherent neighbourhood system), taken abstractly, and
**Proposition 14.4.14** (local sc⁺ symmetric section structure on `V̂_a`) (2017: Definition 14.9,
"good neighborhood system", and Proposition 14.7).

# The local extension on `V̂_a`

## The text, paraphrased

Fix `a ∈ A`.  The boundary data are sc⁺-sections `s⁰ᵃᵢ`, `i ∈ I_a`, of `W` over `U'(a) ⊆ ∂X`,
face-wise sc⁺, with `s⁰ᵃ_{g(i)}(g ∗ y) = μ(Γ(g, y), s⁰ᵃᵢ(y))` (14.45).  For `y ∈ V̂_a` there is the
relation `∼_y` on `I_a` (Definition 14.4.4), and for `z ∈ cl(V̂_a)` the relation `≈_z`
(Definition 14.4.8).  (Definition 14.4.11) A coherent neighbourhood system is a family of open
sets `Õ(z)`, `z ∈ cl(V̂_a)`, with (1) `Õ(z) ⊆ Ũ(a)`, (2) `Õ(g ∗ z) = g ∗ Õ(z)`, and
`Õ(z) ∩ Õ(g ∗ z) = ∅` if `z ≠ g ∗ z`, (3) `[i]_{∼_y} ⊆ [i]_{≈_z}` for `y ∈ Õ(z) ∩ V̂_a`, (4) for
`z ∈ cl(V_a)`, `V_a = V̂_a ∩ ∂X`: `s⁰ᵃᵢ(y) = s⁰ᵃ_{i'}(y)` if `i ≈_z i'` and `y ∈ Õ(z) ∩ U(a)`.
(Proposition 14.4.14) There is a local sc⁺ symmetric section structure `(ŝᵃᵢ)` on `V̂_a` with (1)
`ŝᵃᵢ = s⁰ᵃᵢ` on `V_a` and (2) `ŝᵃᵢ(z) = ŝᵃ_{i'}(z)` if `i ∼_z i'`, `z ∈ V̂_a`.  The proof builds, on
each `Õ([z]) = ⋃_{z' ∈ [z]} Õ(z')`, sections constant on `≈_{z'}`-classes and equivariant under
`G_a`, class by class and orbit by orbit, and glues them with a `G_a`-invariant partition of unity.

## What is formalized

* `LocalExtensionBase A a`: the data the proof uses, abstractly: `Ũ(a)` with the natural
  `G_a`-action (`N`), the open `G_a`-invariant `V̂_a ⊆ Ũ(a)`, the finite `I_a` with its
  `G_a`-action, the boundary sections `s⁰ᵃᵢ` (face-wise sc⁺ on `U(a) = Ũ(a) ∩ ∂X`, with (14.45)),
  the relations `∼_y` with Lemma 14.4.5 (`sim_smul`), and the relations `≈_z`.
* **Definition 14.4.11**: `CoherentNbhdSystem D`, with (1), (3), (4) as fields; (2) is the
  separate predicate `CoherentNbhdSystem.IsEquivariant`.  The proof of Proposition 14.4.14 below
  does not use (2).
* **Proposition 14.4.14**: `proposition_14_4_14`.  Proof: for `z ∈ cl(V_a)` take a section
  constant on each `≈_z`-class (an extension, by `exists_scPlusSection_extension_of_face`, of the
  boundary section of a chosen class representative); for the other `z ∈ cl(V̂_a)` take `0` on a
  neighbourhood missing `cl(V_a)`; glue by an sc-smooth partition of unity; average over `G_a`
  (`avgSection` of Proposition 14.1.4).  The average is `G_a`-equivariant, still extends the
  boundary data (they are equivariant), and is still compatible with `∼_y` because `∼` is
  equivariant (Lemma 14.4.5).
* `LocalExtensionBase.ofZSetup`: the base data for `∼ = ZRel` of B2's `ZSetup`, with
  `sim_smul` discharged by Lemma 14.4.5 (`zRel_smul`).
* Nonvacuity: `LocalExtensionBase.zero` and `CoherentNbhdSystem.zero` (zero sections, trivial
  relations, `Õ(z) = Ũ(a)` when `cl(V̂_a) ⊆ Ũ(a)`), and `exists_coherentNbhdSystem_zero` (for
  tame `X`, at every boundary point, with `V̂_a ∋ a`, from Lemma 14.2.1).

## Reading

* (3) of Definition 14.4.11 is printed for `z ∈ V̂_a`; Proposition 14.4.10 (3) states it for
  `z ∈ cl(V̂_a)`, and the proof of Proposition 14.4.14 uses it at points of `cl(V̂_a)`.  We read
  `z ∈ cl(V̂_a)`, presumably what is meant.
* (4) is used as printed: only for `z ∈ cl(V_a)`.  Points `z ∈ cl(V̂_a) ∖ cl(V_a)` get a
  neighbourhood missing `cl(V_a)`, on which no boundary datum has to be matched.
* `≈_z` need not be an equivalence relation for the proof: the classes of its equivalence closure
  are used, and (3), (4) pass to the closure.
* "Local sc⁺ symmetric section structure on `V̂_a`" is read as sc⁺-sections on `V̂_a` with
  `ŝ_{g(i)}(g ∗ y) = μ(Γ(g, y), ŝᵢ(y))` (Definition 13.2.5 (1)); the weights and `Λ̂_a` are
  defined from them in §14.5.
* The text's `G_a`-invariant partition of unity subordinate to the `Õ([z])` is replaced by an
  ordinary partition of unity followed by the average over `G_a`; this is why (2) is not needed.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### A congruence for glued sections -/

theorem glueSection_congr_at {ι : Type*} {ρ : PartitionOfUnity ι A.Obj}
    {σ σ' : ι → A.Obj → A.W} (hσ : ∀ i, IsSection A.P (σ i)) (hσ' : ∀ i, IsSection A.P (σ' i))
    {y : A.Obj} (h : ∀ i, y ∈ tsupport (ρ i) → σ i y = σ' i y) :
    glueSection A.P ρ σ y = glueSection A.P ρ σ' y := by
  rw [glueSection_apply hσ, glueSection_apply hσ']
  congr 1
  refine finsum_congr fun i => ?_
  by_cases hρ : ρ i y = 0
  · rw [hρ, zero_smul, zero_smul]
  · congr 1
    exact Subtype.ext (h i (subset_tsupport _ hρ))

/-! ### The data of Proposition 14.4.14 -/

/-- **The data of Proposition 14.4.14** (§14.4, pp. 664–667), for a fixed `a`: `Ũ(a)` with the
natural `G_a`-action, an open `G_a`-invariant `V̂_a ⊆ Ũ(a)`, a finite index set `I_a` with a
`G_a`-action, the boundary sections `s⁰ᵃᵢ` (Definition 14.1.3 (1) on `U(a) = Ũ(a) ∩ ∂X`, and
(14.45)), the relations `∼_y` (Definition 14.4.4) with Lemma 14.4.5, and the relations `≈_z`
(Definition 14.4.8). -/
structure LocalExtensionBase (A : SEP.{u}) (a : A.Obj) where
  /-- `Ũ(a)` with the natural `G_a`-action. -/
  N : A.X.NatNbhd a
  /-- `V̂_a`. -/
  Vh : Set A.Obj
  isOpen_Vh : IsOpen Vh
  Vh_subset : Vh ⊆ N.U
  mapsTo_Vh : ∀ g, MapsTo (N.rep.Φ g) Vh Vh
  /-- The index set `I_a`. -/
  I : Type u
  [fintype : Fintype I]
  [mulAction : MulAction (A.X.Isotropy a) I]
  /-- The boundary sections `s⁰ᵃᵢ`. -/
  s0 : I → A.Obj → A.W
  isFaceScPlus : ∀ i, IsFaceScPlusSectionOn A (s0 i) N.bdry
  /-- (14.45). -/
  equivariant : ∀ (g : A.X.Isotropy a) (i : I), ∀ y ∈ N.bdry,
    s0 (g • i) (N.rep.Φ g y) = fibAct (N.rep.Γ g y) (s0 i y)
  /-- `i ∼_y i'` (Definition 14.4.4). -/
  sim : A.Obj → I → I → Prop
  /-- Lemma 14.4.5: `i ∼_y i'` implies `g(i) ∼_{g ∗ y} g(i')`. -/
  sim_smul : ∀ (g : A.X.Isotropy a), ∀ y ∈ Vh, ∀ i i', sim y i i' →
    sim (N.rep.Φ g y) (g • i) (g • i')
  /-- `i ≈_z i'` (Definition 14.4.8). -/
  approx : A.Obj → I → I → Prop

attribute [instance] LocalExtensionBase.fintype LocalExtensionBase.mulAction

/-- **2021 Definition 14.4.11, p. 664 (2017: Definition 14.9)**, conditions (1), (3), (4): a
**coherent neighbourhood system** for `cl(V̂_a) ⊆ Ũ(a)`: open sets `Õ(z) ∋ z`, `z ∈ cl(V̂_a)`, with
(1) `Õ(z) ⊆ Ũ(a)`; (3) `[i]_{∼_y} ⊆ [i]_{≈_z}` for `y ∈ Õ(z) ∩ V̂_a` (read for `z ∈ cl(V̂_a)`, as
in Proposition 14.4.10 (3)); (4) for `z ∈ cl(V_a)`, `V_a = V̂_a ∩ ∂X`: `s⁰ᵃᵢ(y) = s⁰ᵃ_{i'}(y)` if
`i ≈_z i'` and `y ∈ Õ(z) ∩ U(a)`.  Condition (2) is `IsEquivariant`. -/
structure CoherentNbhdSystem {a : A.Obj} (D : LocalExtensionBase A a) where
  /-- `Õ(z)`. -/
  O : A.Obj → Set A.Obj
  isOpen_O : ∀ z ∈ closure D.Vh, IsOpen (O z)
  mem_O : ∀ z ∈ closure D.Vh, z ∈ O z
  /-- (1) -/
  O_subset : ∀ z ∈ closure D.Vh, O z ⊆ D.N.U
  /-- (3) -/
  sim_approx : ∀ z ∈ closure D.Vh, ∀ y ∈ O z ∩ D.Vh, ∀ i i', D.sim y i i' → D.approx z i i'
  /-- (4) -/
  approx_s0 : ∀ z ∈ closure (D.Vh ∩ A.X.PObj.boundary), ∀ y ∈ O z ∩ D.N.bdry, ∀ i i',
    D.approx z i i' → D.s0 i y = D.s0 i' y

/-- **(2) of Definition 14.4.11**: `Õ(g ∗ z) = g ∗ Õ(z)`, and `Õ(z) ∩ Õ(g ∗ z) = ∅` if
`g ∗ z ≠ z`.  (Not used by `proposition_14_4_14`.) -/
def CoherentNbhdSystem.IsEquivariant {a : A.Obj} {D : LocalExtensionBase A a}
    (C : CoherentNbhdSystem D) : Prop :=
  ∀ z ∈ closure D.Vh, ∀ g : A.X.Isotropy a,
    C.O (D.N.rep.Φ g z) = D.N.rep.Φ g '' C.O z ∧
      (D.N.rep.Φ g z ≠ z → Disjoint (C.O z) (C.O (D.N.rep.Φ g z)))

namespace CoherentNbhdSystem

variable {a : A.Obj} {D : LocalExtensionBase A a} (C : CoherentNbhdSystem D)

/-- (4) passes to the equivalence closure of `≈_z`. -/
theorem eqvGen_s0 {z : A.Obj} (hz : z ∈ closure (D.Vh ∩ A.X.PObj.boundary)) {y : A.Obj}
    (hy : y ∈ C.O z ∩ D.N.bdry) {i i' : D.I} (h : Relation.EqvGen (D.approx z) i i') :
    D.s0 i y = D.s0 i' y := by
  induction h with
  | rel i i' h => exact C.approx_s0 z hz y hy i i' h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **The local pieces**: every object `y` has an open neighbourhood `U` with sc⁺-sections
`σᵢ` of `P` that equal `s⁰ᵃᵢ` on `U ∩ V̂_a ∩ ∂X` and are constant on `∼_z`-classes at the points
`z ∈ U ∩ V̂_a`. -/
theorem exists_local_piece (C : CoherentNbhdSystem D)
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) (y : A.Obj) :
    ∃ U : Set A.Obj, IsOpen U ∧ y ∈ U ∧ ∃ σ : D.I → A.Obj → A.W,
      (∀ i, A.B.IsScPlusSection (σ i)) ∧
      (∀ z ∈ U ∩ D.Vh ∩ A.X.PObj.boundary, ∀ i, σ i z = D.s0 i z) ∧
      ∀ z ∈ U ∩ D.Vh, ∀ i i', D.sim z i i' → σ i z = σ i' z := by
  classical
  by_cases hy : y ∈ closure D.Vh
  swap
  · refine ⟨(closure D.Vh)ᶜ, isClosed_closure.isOpen_compl, hy, fun _ => fiberZero A.P,
      fun _ => isScPlusSection_fiberZero, fun z hz _ => ?_, fun _ _ _ _ _ => rfl⟩
    exact absurd (subset_closure hz.1.2) hz.1.1
  by_cases hyb : y ∈ closure (D.Vh ∩ A.X.PObj.boundary)
  · -- a section constant on the classes of `≈_y`, extending the boundary data
    obtain ⟨K, hKn, hKc, hKO⟩ := exists_mem_nhds_isClosed_subset
      ((C.isOpen_O y hy).mem_nhds (C.mem_O y hy))
    have hclK : closure (interior K) ⊆ D.N.U :=
      ((closure_minimal interior_subset hKc).trans hKO).trans (C.O_subset y hy)
    choose e he hes using fun j : D.I => exists_scPlusSection_extension_of_face hB hpu
      D.N.isOpen_U (D.isFaceScPlus j) hclK
    let r : D.I → D.I := fun i =>
      (Quotient.mk (Relation.EqvGen.setoid (D.approx y)) i).out
    have hr : ∀ i, Relation.EqvGen (D.approx y) (r i) i := fun i =>
      Quotient.mk_out (s := Relation.EqvGen.setoid (D.approx y)) i
    refine ⟨interior K, isOpen_interior, mem_interior_iff_mem_nhds.2 hKn, fun i => e (r i),
      fun i => he (r i), ?_, ?_⟩
    · rintro z ⟨⟨hzK, -⟩, hzb⟩ i
      have hzO : z ∈ C.O y := hKO (interior_subset hzK)
      change e (r i) z = D.s0 i z
      rw [hes (r i) z ⟨hzK, hzb⟩]
      exact C.eqvGen_s0 hyb ⟨hzO, C.O_subset y hy hzO, hzb⟩ (hr i)
    · rintro z ⟨hzK, hzV⟩ i i' hii'
      have h := C.sim_approx y hy z ⟨hKO (interior_subset hzK), hzV⟩ i i' hii'
      have hri : r i = r i' := by
        change (Quotient.mk (Relation.EqvGen.setoid (D.approx y)) i).out =
          (Quotient.mk (Relation.EqvGen.setoid (D.approx y)) i').out
        rw [Quotient.sound (Relation.EqvGen.rel _ _ h)]
      change e (r i) z = e (r i') z
      rw [hri]
  · -- no boundary datum near `y`: the zero sections
    refine ⟨C.O y ∩ (closure (D.Vh ∩ A.X.PObj.boundary))ᶜ,
      (C.isOpen_O y hy).inter isClosed_closure.isOpen_compl, ⟨C.mem_O y hy, hyb⟩,
      fun _ => fiberZero A.P, fun _ => isScPlusSection_fiberZero, fun z hz _ => ?_,
      fun _ _ _ _ _ => rfl⟩
    exact absurd (subset_closure (show z ∈ D.Vh ∩ A.X.PObj.boundary from ⟨hz.1.2, hz.2⟩))
      hz.1.1.2

end CoherentNbhdSystem

/-! ### Proposition 14.4.14 -/

/-- **2021 Proposition 14.4.14, pp. 667–671 (2017: Proposition 14.7)**: let every object lie in a
tame strong bundle chart and let the object M-polyfold admit sc-smooth partitions of unity.  For
the data `D` of a fixed `a ∈ A` and a coherent neighbourhood system `C` (Definition 14.4.11
(1), (3), (4)) there are sc⁺-sections `ŝᵃᵢ`, `i ∈ I_a`, on `V̂_a` with
`ŝᵃ_{g(i)}(g ∗ y) = μ(Γ(g, y), ŝᵃᵢ(y))` on `V̂_a` (a symmetric section structure), (1)
`ŝᵃᵢ = s⁰ᵃᵢ` on `V_a = V̂_a ∩ ∂X`, and (2) `ŝᵃᵢ(z) = ŝᵃ_{i'}(z)` whenever `i ∼_z i'`, `z ∈ V̂_a`. -/
theorem proposition_14_4_14
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) {a : A.Obj} {D : LocalExtensionBase A a}
    (C : CoherentNbhdSystem D) :
    ∃ sh : D.I → A.Obj → A.W, (∀ i, IsScPlusSectionOn A (sh i) D.Vh) ∧
      (∀ (g : A.X.Isotropy a) i, ∀ y ∈ D.Vh,
        sh (g • i) (D.N.rep.Φ g y) = fibAct (D.N.rep.Γ g y) (sh i y)) ∧
      (∀ i, ∀ y ∈ D.Vh ∩ A.X.PObj.boundary, sh i y = D.s0 i y) ∧
      ∀ y ∈ D.Vh, ∀ i i', D.sim y i i' → sh i y = sh i' y := by
  classical
  let _ : Fintype (A.X.Isotropy a) := Fintype.ofFinite _
  choose U hU hyU σ hσ hσs hσsim using C.exists_local_piece hB hpu
  obtain ⟨ρ, hρsub, hρsm⟩ := hpu A.Obj U hU (iUnion_eq_univ_iff.2 fun y => ⟨y, hyU y⟩)
  have hsec : ∀ k i, IsSection A.P (σ k i) := fun k i => (hσ k i).1
  -- the glued sections
  set τ : D.I → A.Obj → A.W := fun i => glueSection A.P ρ fun k => σ k i with hτdef
  have hτ : ∀ i, IsScPlusSectionOn A (τ i) D.N.U := fun i =>
    IsScPlusSectionOn.of_isScPlusSection
      (isScPlusSection_glueSection (X := A.X) hρsm fun k => hσ k i) D.N.isOpen_U
  have hτs : ∀ i, ∀ y ∈ D.Vh ∩ A.X.PObj.boundary, τ i y = D.s0 i y := by
    rintro i y ⟨hyV, hyb⟩
    exact glueSection_eq_of (fun k => hsec k i)
      ((D.isFaceScPlus i).1 y ⟨D.Vh_subset hyV, hyb⟩).1
      fun k hk => hσs k y ⟨⟨hρsub k hk, hyV⟩, hyb⟩ i
  have hτsim : ∀ y ∈ D.Vh, ∀ i i', D.sim y i i' → τ i y = τ i' y := by
    intro y hyV i i' h
    exact glueSection_congr_at (fun k => hsec k i) (fun k => hsec k i')
      fun k hk => hσsim k y ⟨hρsub k hk, hyV⟩ i i' h
  -- the average over `G_a`
  have hBU : D.Vh ∩ A.X.PObj.boundary ⊆ D.N.U := fun y hy => D.Vh_subset hy.1
  have hBinv : ∀ (g : A.X.Isotropy a), ∀ y ∈ D.Vh ∩ A.X.PObj.boundary,
      D.N.rep.Φ g y ∈ D.Vh ∩ A.X.PObj.boundary := fun g y hy =>
    ⟨D.mapsTo_Vh g hy.1, (NatNbhd.mapsTo_Φ_bdry D.N g ⟨D.Vh_subset hy.1, hy.2⟩).2⟩
  refine ⟨avgSection D.N τ, fun i => (isScPlusSectionOn_avgSection hτ i).mono D.isOpen_Vh
    D.Vh_subset, fun g i y hy => avgSection_equivariant hτ g i (D.Vh_subset hy),
    fun i y hy => ?_, fun y hy i i' h => ?_⟩
  · rw [avgSection_eq_of_equivariant hτ hBU (fun g j z hz => by
      rw [hτs _ _ (hBinv g z hz), hτs _ _ hz]
      exact D.equivariant g j z ⟨D.Vh_subset hz.1, hz.2⟩) i hy, hτs i y hy]
  · have hyU := D.Vh_subset hy
    have hterm : ∀ g, avgTerm D.N τ g i y = avgTerm D.N τ g i' y := fun g => by
      rw [avgTerm_apply (fun k => (hτ k).1) g i hyU, avgTerm_apply (fun k => (hτ k).1) g i' hyU,
        hτsim _ (D.mapsTo_Vh g hy) _ _ (D.sim_smul g y hy i i' h)]
    rw [avgSection_apply hτ i hyU, avgSection_apply hτ i' hyU]
    congr 2
    exact Finset.sum_congr rfl fun g _ => Subtype.ext (hterm g)

/-! ### The base data from B2's `ZSetup` -/

namespace LocalExtensionBase

/-- **The data of Proposition 14.4.14 from a `ZSetup`** (B2's setting of Definitions
14.4.2–14.4.4) at `a`: `∼_y` is `ZRel a y`, and Lemma 14.4.5 (`zRel_smul`) is `sim_smul`.  The
boundary sections and `≈_z` are given. -/
def ofZSetup (S : A.X.ZSetup) {a : A.Obj} (ha : a ∈ S.A) (hV : IsOpen (S.V a))
    (s0 : S.I a → A.Obj → A.W) (hs0 : ∀ i, IsFaceScPlusSectionOn A (s0 i) (S.nbhd a).bdry)
    (heq : ∀ (g : A.X.Isotropy a) (i : S.I a), ∀ y ∈ (S.nbhd a).bdry,
      s0 (g • i) ((S.nbhd a).rep.Φ g y) = fibAct ((S.nbhd a).rep.Γ g y) (s0 i y))
    (approx : A.Obj → S.I a → S.I a → Prop) : LocalExtensionBase A a where
  N := S.nbhd a
  Vh := S.V a
  isOpen_Vh := hV
  Vh_subset := S.V_subset a ha
  mapsTo_Vh := S.mapsTo_V a ha
  I := S.I a
  s0 := s0
  isFaceScPlus := hs0
  equivariant := heq
  sim := S.ZRel a
  sim_smul g _ _ _ _ h := ZSetup.zRel_smul h g
  approx := approx

/-- **Nonvacuity**: the zero boundary sections, one index, trivial relations, for any `Ũ(a)` and
any open invariant `V̂_a ⊆ Ũ(a)`. -/
def zero {a : A.Obj} (N : A.X.NatNbhd a) (Vh : Set A.Obj) (hVo : IsOpen Vh) (hVU : Vh ⊆ N.U)
    (hVinv : ∀ g, MapsTo (N.rep.Φ g) Vh Vh) : LocalExtensionBase A a where
  N := N
  Vh := Vh
  isOpen_Vh := hVo
  Vh_subset := hVU
  mapsTo_Vh := hVinv
  I := PUnit.{u + 1}
  s0 _ := fiberZero A.P
  isFaceScPlus _ := isFaceScPlusSectionOn_fiberZero (NatNbhd.bdry_subset_boundary N)
  equivariant g _ _ hy := (fibAct_fiberZero (N.src_Γ g hy.1) (N.tgt_Γ g hy.1)).symm
  sim _ _ _ := True
  sim_smul _ _ _ _ _ _ := trivial
  approx _ _ _ := True

end LocalExtensionBase

/-- **Nonvacuity of Definition 14.4.11**: if `cl(V̂_a) ⊆ Ũ(a)`, then `Õ(z) = Ũ(a)` is a coherent
neighbourhood system for the zero data; it also satisfies (2) when the action on `Ũ(a)` is
onto. -/
def CoherentNbhdSystem.zero {a : A.Obj} (N : A.X.NatNbhd a) (Vh : Set A.Obj) (hVo : IsOpen Vh)
    (hVU : Vh ⊆ N.U) (hVinv : ∀ g, MapsTo (N.rep.Φ g) Vh Vh) (hcl : closure Vh ⊆ N.U) :
    CoherentNbhdSystem (LocalExtensionBase.zero (A := A) N Vh hVo hVU hVinv) where
  O _ := N.U
  isOpen_O _ _ := N.isOpen_U
  mem_O _ hz := hcl hz
  O_subset _ _ := subset_rfl
  sim_approx _ _ _ _ _ _ _ := trivial
  approx_s0 _ _ _ _ _ _ _ := rfl

/-- **The hypotheses of `proposition_14_4_14` are satisfiable** beyond the zero data's
structure: for tame `X`, a good `V₀` at a boundary point `x` contains a good `V` with
`cl V ⊆ V₀` (Lemma 14.2.1), so `Ũ(x) = V₀`, `V̂_x = V` carry a coherent neighbourhood system. -/
theorem exists_coherentNbhdSystem_zero (hX : A.X.IsTame) {x : A.Obj}
    (hx : x ∈ A.X.PObj.boundary) (V₀ : A.X.NatNbhd x) (hV₀ : A.X.IsGoodBoundaryNbhd V₀) :
    ∃ (D : LocalExtensionBase A x), x ∈ D.Vh ∧ Nonempty (CoherentNbhdSystem D) := by
  obtain ⟨V, hle, -, hcl, -⟩ := A.X.lemma_14_2_1 hX hx V₀ hV₀
  have hVU : V.U ⊆ V₀.U := hle.subset
  have hinv : ∀ g, MapsTo (V₀.rep.Φ g) V.U V.U := fun g y hy => by
    rw [← hle.Φ_eq g hy]; exact V.mapsTo_Φ g hy
  exact ⟨LocalExtensionBase.zero V₀ V.U V.isOpen_U hVU hinv, V.mem_U,
    ⟨CoherentNbhdSystem.zero V₀ V.U V.isOpen_U hVU hinv hcl⟩⟩

end SBLocalization

end Polyfold
