import Polyfold.Chapter14.P3W4S3_ExtendCorrespondences
import Polyfold.Chapter14.P3W3B2_Cover

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.3, pp. 653–657:
the neighbourhoods (P6), **Proposition 14.3.8** and the summary (14.33)–(14.38)
(2017: §14.3, Proposition 14.4).

# The sets `V̂_a`

## The text, paraphrased

Choose open `Ũ(x) ∋ x`, `x ∈ ∂X`, with (P6): (i) the natural `G_x`-action and the properness
property, (ii) `cl_{|X|}(|Ũ(x)|) ⊆ |Ũ'(x)|`; hence `cl_X(Ũ(x)) ⊆ Ũ'(x)`.  Lemma 14.3.6 gives
`A ⊆ ∂X` and `Ṽ_a ⊆ Ũ(a)`, Lemma 14.3.7 gives `o(y)`, `Õ(y)` for `y ∈ U'(a)`, and (14.32)
`V̂_a = (⋃_{y ∈ U'(a)} Õ(y)) ∩ Ṽ_a`.  (Proposition 14.3.8) (1) `V̂_a` is open, `G_a`-invariant
and `V̂_a ⊆ Ṽ_a ⊆ Ũ(a)`; (2) `V̂_a ∩ ∂X = Ṽ_a ∩ ∂X`; (3) `(|V̂_a|)_{a ∈ A}` is a locally finite
covering of `|∂X|` by sets open in `|X|`; (4) `V̂_{a,a'} ⊆ Ô_{a,a'}`, so `τ̂_{a,a'}` restricts to
`V̂_{a,a'}`.

## What is formalized

* `EpGroupoid.proposition_14_3_8`: Proposition 14.3.8 in B2's abstract setting (a saturated `B`
  for `∂X`, `NatNbhd`s `Ũ'(a)`, `Ũ(a)` with the same representation, any open `Ô_{a,b}`
  containing `U'(a, b)`), from `lemma_14_3_7`.
* `EpGroupoid.isSaturated_boundary_p3w4`: `∂X` is saturated (so `|∂X|` is closed in `|X|`).
* `SBLocalization.P6Nbhds P` (the neighbourhoods of (P6), with the text's
  `cl_{|X|}`-condition), `P6Nbhds.closure_subset` (the "obvious ramification", from
  Lemma 13.1.1 and (P5)(i)) and the witness `P6Nbhds.exists_`.
* `SBLocalization.CorrExtension.proposition_14_3_8`: the whole of §14.3 for a representative
  with (P4), (P5), (P6) and `|X|` paracompact: `A`, `Ṽ_a` (Lemma 14.3.6), `V̂_a` with (1)–(4) for
  the `Ô_{a,a'}` of Proposition 14.3.4.
* For §14.4 (B2's `ZSetup`): `CorrExtension.tauHat_Γ_of_VHat` (the condition `diag`) and
  `CorrExtension.tauHat_inv_of_VHat` (the condition `swap`) for `τ̂` on `V̂_{a,a'}`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- `∂X` is saturated: isomorphic objects have the same degeneracy index. -/
theorem isSaturated_boundary_p3w4 : X.IsSaturated X.PObj.boundary := by
  refine Subset.antisymm (fun y hy => ?_) (subset_preimage_image _ _)
  obtain ⟨b, hb, hby⟩ := hy
  obtain ⟨φ, hs, ht⟩ := X.π_eq_π_iff.1 hby
  change 1 ≤ X.PObj.degIndex y
  rw [← ht, ← X.degIndex_tgt, X.degIndex_src, hs]
  exact hb

/-- **2021 Proposition 14.3.8, p. 656 (2017: Proposition 14.4), in the abstract setting of
Lemma 14.3.7**: `B` (for `∂X`) saturated; `Ũ'(a)`, `Ũ(a)` neighbourhoods with the same natural
action, `cl_X Ũ(b) ⊆ Ũ'(b)`, `cl_X Ũ(b)` proper (P6); `Ṽ_a ⊆ Ũ(a)` open, invariant, with
`(|Ṽ_a|)` locally finite and covering `|B|` (Lemma 14.3.6); `Ô_{a,b}` open with
`U'(a, b) ⊆ Ô_{a,b}` (Proposition 14.3.4 (1)).  Then the sets `V̂_a` of (14.32) satisfy
(1) `V̂_a` open, `G_a`-invariant, `V̂_a ⊆ Ṽ_a`; (2) `V̂_a ∩ B = Ṽ_a ∩ B`; (3) `(|V̂_a|)` is a
locally finite covering of `|B|` by open sets; (4) `V̂_{a,a'} ⊆ Ô_{a,a'}`. -/
theorem proposition_14_3_8 {A B : Set Obj} (hB : X.IsSaturated B)
    (N N' : ∀ x : Obj, X.NatNbhd x) (hrep : ∀ a ∈ A, (N a).rep = (N' a).rep)
    (hcl : ∀ b ∈ A, closure (N b).U ⊆ (N' b).U)
    (hprop : ∀ b ∈ A, X.IsProperSubset (closure (N b).U))
    {Vt : Obj → Set Obj} (hVo : ∀ a ∈ A, IsOpen (Vt a)) (hVU : ∀ a ∈ A, Vt a ⊆ (N a).U)
    (hVinv : ∀ a ∈ A, ∀ g, MapsTo ((N a).rep.Φ g) (Vt a) (Vt a))
    (hlf : LocallyFinite fun a : A => X.π '' Vt a) (hcov : X.π '' B ⊆ ⋃ a ∈ A, X.π '' Vt a)
    {O : Obj → Obj → Set Mor} (hOo : ∀ a ∈ A, ∀ b ∈ A, IsOpen (O a b))
    (hO : ∀ a ∈ A, ∀ b ∈ A, ∀ φ, X.src φ ∈ (N' a).U ∩ B → X.tgt φ ∈ (N' b).U ∩ B → φ ∈ O a b) :
    ∃ Vh : Obj → Set Obj,
      (∀ a ∈ A, IsOpen (Vh a) ∧ Vh a ⊆ Vt a ∧ ∀ g, MapsTo ((N a).rep.Φ g) (Vh a) (Vh a)) ∧
      (∀ a ∈ A, Vh a ∩ B = Vt a ∩ B) ∧
      ((∀ a ∈ A, IsOpen (X.π '' Vh a)) ∧ LocallyFinite (fun a : A => X.π '' Vh a) ∧
        X.π '' B ⊆ ⋃ a ∈ A, X.π '' Vh a) ∧
      (∀ a ∈ A, ∀ a' ∈ A, X.morBetween (Vh a) (Vh a') ⊆ O a a') := by
  classical
  have h37 := fun a (ha : a ∈ A) => X.lemma_14_3_7 (A := A) hB (N' a)
    (Ut := fun b => (N b).U) (Ut' := fun b => (N' b).U) (V := Vt) hcl hprop (hOo a ha)
    (hO a ha) hlf
  choose o Oy hOy using h37
  let Vh : Obj → Set Obj := fun a =>
    if ha : a ∈ A then (⋃ y ∈ (N' a).U ∩ B, Oy a ha y) ∩ Vt a else ∅
  have hVh : ∀ a (ha : a ∈ A), Vh a = (⋃ y ∈ (N' a).U ∩ B, Oy a ha y) ∩ Vt a :=
    fun a ha => dif_pos ha
  have hsub : ∀ a ∈ A, Vh a ⊆ Vt a := fun a ha => by
    rw [hVh a ha]
    exact inter_subset_right
  -- `Ũ(a) ⊆ Ũ'(a)`
  have hNN' : ∀ a ∈ A, (N a).U ⊆ (N' a).U := fun a ha => subset_closure.trans (hcl a ha)
  -- `B ∩ Ṽ_a ⊆ V̂_a`
  have hBV : ∀ a ∈ A, Vt a ∩ B ⊆ Vh a := fun a ha z hz => by
    rw [hVh a ha]
    have hzD : z ∈ (N' a).U ∩ B := ⟨hNN' a ha (hVU a ha hz.1), hz.2⟩
    exact ⟨mem_iUnion₂.2 ⟨z, hzD, (hOy a ha z hzD).2.1⟩, hz.1⟩
  refine ⟨Vh, fun a ha => ⟨?_, hsub a ha, fun g z hz => ?_⟩, fun a ha => ?_, ⟨fun a ha => ?_,
    hlf.subset fun a => image_mono (hsub a a.2), ?_⟩, fun a ha a' ha' φ hφ => ?_⟩
  · -- (1) open
    rw [hVh a ha]
    exact (isOpen_biUnion fun y hy => (hOy a ha y hy).1).inter (hVo a ha)
  · -- (1) invariant
    rw [hVh a ha] at hz ⊢
    obtain ⟨hzU, hzV⟩ := hz
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 hzU
    have hgy : (N' a).rep.Φ g y ∈ (N' a).U ∩ B := by
      refine ⟨(N' a).Φ_mem g hy.1, ?_⟩
      have hmem : (N' a).rep.Φ g y ∈ X.π ⁻¹' (X.π '' B) :=
        ⟨y, hy.2, ((N' a).π_Φ g ((N' a).U_subset hy.1)).symm⟩
      rwa [hB] at hmem
    refine ⟨mem_iUnion₂.2 ⟨_, hgy, ?_⟩, hVinv a ha g hzV⟩
    rw [hrep a ha, ← ((hOy a ha y hy).2.2.2.2.2.2.1 g).1]
    exact mem_image_of_mem _ hzy
  · -- (2)
    exact Subset.antisymm (fun z hz => ⟨hsub a ha hz.1, hz.2⟩)
      (fun z hz => ⟨hBV a ha hz, hz.2⟩)
  · -- (3) open
    exact X.proposition_7_1_8 _ (by
      rw [hVh a ha]
      exact (isOpen_biUnion fun y hy => (hOy a ha y hy).1).inter (hVo a ha))
  · -- (3) covering
    intro p hp
    obtain ⟨b, hb, rfl⟩ := hp
    obtain ⟨a, ha, v, hv, hvb⟩ := mem_iUnion₂.1 (hcov ⟨b, hb, rfl⟩)
    have hvB : v ∈ B := by
      have hmem : v ∈ X.π ⁻¹' (X.π '' B) := ⟨b, hb, hvb.symm⟩
      rwa [hB] at hmem
    exact mem_iUnion₂.2 ⟨a, ha, v, hBV a ha ⟨hv, hvB⟩, hvb⟩
  · -- (4)
    have hs := hφ.1
    rw [hVh a ha] at hs
    obtain ⟨hsU, -⟩ := hs
    obtain ⟨y, hy, hsy⟩ := mem_iUnion₂.1 hsU
    have ht : X.tgt φ ∈ Vt a' := hsub a' ha' hφ.2
    have hspec := hOy a ha y hy
    have ha'o : a' ∈ o a ha y :=
      hspec.2.2.2.2.2.1 a' ha' ⟨X.π (X.src φ), mem_image_of_mem _ hsy,
        X.tgt φ, ht, (X.π_src_eq_π_tgt φ).symm⟩
    exact hspec.2.2.2.2.2.2.2 a' ha'o φ hsy (hVU a' ha' ht)

end EpGroupoid

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### The neighbourhoods of (P6) -/

namespace P5Nbhds

variable {T : BoundaryStructuredTuple A}

/-- **(P6)**, p. 653: open neighbourhoods `Ũ(x)` of the `x ∈ ∂X` with (i) the natural
`G_x`-action (read as the restriction of that of `Ũ'(x)`: same representation,
`Ũ(x) ⊆ Ũ'(x)`) and the properness property, (ii) `cl_{|X|}(|Ũ(x)|) ⊆ |Ũ'(x)|`. -/
structure P6Nbhds (P : P5Nbhds T) where
  /-- `Ũ(x)`. -/
  nbhd : ∀ x : A.X.PObj.boundary, A.X.NatNbhd x
  rep_eq : ∀ x, (nbhd x).rep = (P.nbhd x).rep
  subset : ∀ x, (nbhd x).U ⊆ (P.nbhd x).U
  /-- (i) -/
  isProperSubset_closure : ∀ x, A.X.IsProperSubset (closure (nbhd x).U)
  /-- (ii) -/
  closure_π_subset : ∀ x, closure (A.X.π '' (nbhd x).U) ⊆ A.X.π '' (P.nbhd x).U

variable {P : P5Nbhds T}

/-- **The "obvious ramification" of (P6)**: `cl_X(Ũ(x)) ⊆ Ũ'(x)` (Lemma 13.1.1, using the
properness of `Ũ'(x)`, (P5)(i)). -/
theorem P6Nbhds.closure_subset (Q : P6Nbhds P) (x : A.X.PObj.boundary) :
    closure (Q.nbhd x).U ⊆ (P.nbhd x).U :=
  (A.X.lemma_13_1_1 (P.nbhd x) (P.isProperSubset_closure x) (Q.subset x)).2 (Q.closure_π_subset x)

/-- **(P6) is satisfiable** (no tameness needed): shrink `Ũ'(x)` invariantly into a closed
neighbourhood inside `Ũ'(x)` and an open set with the properness property. -/
theorem P6Nbhds.exists_ (P : P5Nbhds T) : Nonempty (P6Nbhds P) := by
  have key : ∀ x : A.X.PObj.boundary, ∃ N : A.X.NatNbhd x, N.rep = (P.nbhd x).rep ∧
      N.U ⊆ (P.nbhd x).U ∧ A.X.IsProperSubset (closure N.U) ∧
      closure (A.X.π '' N.U) ⊆ A.X.π '' (P.nbhd x).U := by
    intro x
    obtain ⟨C, hCn, hCc, hCU⟩ :=
      exists_mem_nhds_isClosed_subset ((P.nbhd x).isOpen_U.mem_nhds (P.nbhd x).mem_U)
    obtain ⟨Q, hxQ, hQo, hQp⟩ := A.X.exists_hasPropernessProperty (x : A.Obj)
    obtain ⟨N, hrep, hNU⟩ := (P.nbhd x).exists_restrict_subset (isOpen_interior.inter hQo)
      ⟨mem_interior_iff_mem_nhds.2 hCn, hxQ⟩
    have hNP : N.U ⊆ (P.nbhd x).U := fun y hy => (hNU hy).1
    have hcl : closure N.U ⊆ (P.nbhd x).U :=
      (closure_minimal (fun y hy => interior_subset (hNU hy).2.1) hCc).trans hCU
    refine ⟨N, hrep, hNP, hQp.of_subset (closure_mono fun y hy => (hNU hy).2.2) isClosed_closure,
      ?_⟩
    exact (A.X.lemma_13_1_1 (P.nbhd x) (P.isProperSubset_closure x) hNP).1 hcl
  choose N hrep hsub hprop hπ using key
  exact ⟨⟨N, hrep, hsub, hprop, hπ⟩⟩

open scoped Classical in
/-- `Ũ'(a)` for every object `a` (for `a ∉ ∂X`, the domain of some natural representation;
irrelevant). -/
def nbhdObj (P : P5Nbhds T) (a : A.Obj) : A.X.NatNbhd a :=
  if h : a ∈ A.X.PObj.boundary then P.nbhd ⟨a, h⟩ else
    NatNbhd.ofRep (A.X.theorem_7_1_13 a isOpen_univ (mem_univ a)).choose

theorem nbhdObj_of_mem (P : P5Nbhds T) {a : A.Obj} (h : a ∈ A.X.PObj.boundary) :
    P.nbhdObj a = P.nbhd ⟨a, h⟩ := by
  classical
  exact dif_pos h

open scoped Classical in
/-- `Ũ(a)` for every object `a`. -/
def P6Nbhds.nbhdObj (Q : P6Nbhds P) (a : A.Obj) : A.X.NatNbhd a :=
  if h : a ∈ A.X.PObj.boundary then Q.nbhd ⟨a, h⟩ else
    NatNbhd.ofRep (A.X.theorem_7_1_13 a isOpen_univ (mem_univ a)).choose

theorem P6Nbhds.nbhdObj_of_mem (Q : P6Nbhds P) {a : A.Obj} (h : a ∈ A.X.PObj.boundary) :
    Q.nbhdObj a = Q.nbhd ⟨a, h⟩ := by
  classical
  exact dif_pos h

end P5Nbhds

namespace CorrExtension

variable {T : BoundaryStructuredTuple A} {P : P5Nbhds T} (E : CorrExtension T P)

open scoped Classical in
/-- `Ô_{a,b}` for objects `a, b` (empty unless `a, b ∈ ∂X`). -/
def OhatObj (a b : A.Obj) : Set A.Mor :=
  if h : a ∈ A.X.PObj.boundary ∧ b ∈ A.X.PObj.boundary then E.Ohat ⟨a, h.1⟩ ⟨b, h.2⟩ else ∅

theorem OhatObj_of_mem {a b : A.Obj} (ha : a ∈ A.X.PObj.boundary) (hb : b ∈ A.X.PObj.boundary) :
    E.OhatObj a b = E.Ohat ⟨a, ha⟩ ⟨b, hb⟩ := by
  classical
  exact dif_pos ⟨ha, hb⟩

/-- **2021 Proposition 14.3.8, p. 656 (2017: Proposition 14.4), with the data of §14.3**: for a
representative `(Λ, 𝒰⁰, S⁰, τ⁰)` with (P1)–(P4), the `Ô_{x,x'}` of Proposition 14.3.4 built on
neighbourhoods `Ũ'(x)` with (P5), neighbourhoods `Ũ(x)` with (P6), and `|X|` paracompact, there
are `A ⊆ ∂X` and `Ṽ_a` as in Lemma 14.3.6 (nonempty, open, `Ṽ_a ⊆ Ũ(a)`,
`cl_{|X|}|Ṽ_a| ⊆ |Ũ(a)|`, `G_a`-invariant, `(|Ṽ_a|)` locally finite) and `V̂_a` with
(1) `V̂_a` open, `G_a`-invariant, `V̂_a ⊆ Ṽ_a`, (2) `V̂_a ∩ ∂X = Ṽ_a ∩ ∂X`, (3) `(|V̂_a|)` a locally
finite covering of `|∂X|` by sets open in `|X|`, (4) `V̂_{a,a'} ⊆ Ô_{a,a'}`. -/
theorem proposition_14_3_8 (hpara : A.X.HasParacompactOrbitSpace) (Q : P5Nbhds.P6Nbhds P) :
    ∃ (Aset : Set A.Obj) (Vt Vh : A.Obj → Set A.Obj), Aset ⊆ A.X.PObj.boundary ∧
      (∀ a ∈ Aset, (Vt a).Nonempty ∧ IsOpen (Vt a) ∧ Vt a ⊆ (Q.nbhdObj a).U ∧
        closure (A.X.π '' Vt a) ⊆ A.X.π '' (Q.nbhdObj a).U ∧
        ∀ g, MapsTo ((Q.nbhdObj a).rep.Φ g) (Vt a) (Vt a)) ∧
      LocallyFinite (fun a : Aset => A.X.π '' Vt a) ∧
      (∀ a ∈ Aset, IsOpen (Vh a) ∧ Vh a ⊆ Vt a ∧
        ∀ g, MapsTo ((Q.nbhdObj a).rep.Φ g) (Vh a) (Vh a)) ∧
      (∀ a ∈ Aset, Vh a ∩ A.X.PObj.boundary = Vt a ∩ A.X.PObj.boundary) ∧
      ((∀ a ∈ Aset, IsOpen (A.X.π '' Vh a)) ∧ LocallyFinite (fun a : Aset => A.X.π '' Vh a) ∧
        A.X.π '' A.X.PObj.boundary ⊆ ⋃ a ∈ Aset, A.X.π '' Vh a) ∧
      (∀ a ∈ Aset, ∀ a' ∈ Aset, A.X.morBetween (Vh a) (Vh a') ⊆ E.OhatObj a a') := by
  have hsat : A.X.IsSaturated A.X.PObj.boundary := isSaturated_boundary_p3w4
  obtain ⟨Aset, Vt, hAB, hVt, hlf, hcov⟩ := A.X.lemma_14_3_6 hpara
    (A.X.isClosed_π_image_of_isSaturated hsat A.X.PObj.isClosed_boundary) Q.nbhdObj
  have hrep : ∀ a ∈ Aset, (Q.nbhdObj a).rep = (P.nbhdObj a).rep := fun a ha => by
    rw [Q.nbhdObj_of_mem (hAB ha), P.nbhdObj_of_mem (hAB ha)]
    exact Q.rep_eq _
  have hcl : ∀ b ∈ Aset, closure (Q.nbhdObj b).U ⊆ (P.nbhdObj b).U := fun b hb => by
    rw [Q.nbhdObj_of_mem (hAB hb), P.nbhdObj_of_mem (hAB hb)]
    exact Q.closure_subset _
  have hprop : ∀ b ∈ Aset, A.X.IsProperSubset (closure (Q.nbhdObj b).U) := fun b hb => by
    rw [Q.nbhdObj_of_mem (hAB hb)]
    exact Q.isProperSubset_closure _
  have hOo : ∀ a ∈ Aset, ∀ b ∈ Aset, IsOpen (E.OhatObj a b) := fun a ha b hb => by
    rw [E.OhatObj_of_mem (hAB ha) (hAB hb)]
    exact E.isOpen_Ohat _ _
  have hO : ∀ a ∈ Aset, ∀ b ∈ Aset, ∀ φ, A.X.src φ ∈ (P.nbhdObj a).U ∩ A.X.PObj.boundary →
      A.X.tgt φ ∈ (P.nbhdObj b).U ∩ A.X.PObj.boundary → φ ∈ E.OhatObj a b := by
    intro a ha b hb φ hs ht
    rw [E.OhatObj_of_mem (hAB ha) (hAB hb)]
    rw [P.nbhdObj_of_mem (hAB ha)] at hs
    rw [P.nbhdObj_of_mem (hAB hb)] at ht
    refine E.mor_subset_Ohat _ _ ?_
    rw [← P.mor_inter_boundaryMor]
    exact ⟨⟨hs.1, ht.1⟩, hs.2, ht.2⟩
  obtain ⟨Vh, h1, h2, h3, h4⟩ :=
    EpGroupoid.proposition_14_3_8 hsat Q.nbhdObj P.nbhdObj hrep hcl hprop
    (fun a ha => (hVt a ha).2.1) (fun a ha => (hVt a ha).2.2.1)
    (fun a ha => (hVt a ha).2.2.2.2.2) hlf hcov hOo hO
  exact ⟨Aset, Vt, Vh, hAB, fun a ha => ⟨(hVt a ha).1, (hVt a ha).2.1, (hVt a ha).2.2.1,
    (hVt a ha).2.2.2.2.1, (hVt a ha).2.2.2.2.2⟩, hlf, h1, h2, h3, h4⟩

/-! ### The conditions `diag` and `swap` of B2's `ZSetup` for `τ̂` on the `V̂_a` -/

/-- **`diag` for `τ̂`**: if `V̂_a ⊆ Ũ'(a)` is invariant under the natural action and
`V̂_{a,a} ⊆ Ô_{a,a}`, then `τ̂_{a,a}(Γ(g, w)) = [I_a ←Id I_a →g I_a]` for `w ∈ V̂_a`. -/
theorem tauHat_Γ_of_VHat {a : A.X.PObj.boundary} {V : Set A.Obj} (hVU : V ⊆ (P.nbhd a).U)
    (hVinv : ∀ g, MapsTo ((P.nbhd a).rep.Φ g) V V) (hVO : A.X.morBetween V V ⊆ E.Ohat a a)
    (g : A.X.Isotropy a) {w : A.Obj} (hw : w ∈ V) :
    E.tauHat a a ((P.nbhd a).rep.Γ g w) = IndexCorr.ofPerm g := by
  refine E.tauHat_Γ g (hVU hw) (hVO ⟨?_, ?_⟩)
  · rw [(P.nbhd a).src_Γ g (hVU hw)]
    exact hw
  · rw [(P.nbhd a).tgt_Γ g (hVU hw)]
    exact hVinv g hw

/-- **`swap` for `τ̂`**: on `V̂_{a',a} ⊆ Ô_{a',a}`, `τ̂_{a',a}(φ) = τ̂_{a,a'}(φ⁻¹)♯`. -/
theorem tauHat_inv_of_VHat {a a' : A.X.PObj.boundary} {V V' : Set A.Obj}
    (hVO : A.X.morBetween V V' ⊆ E.Ohat a a') {φ : A.Mor} (hs : A.X.src φ ∈ V')
    (ht : A.X.tgt φ ∈ V) : E.tauHat a' a φ = (E.tauHat a a' (A.X.inv φ)).swap := by
  have hφ : A.X.inv φ ∈ E.Ohat a a' :=
    hVO ⟨by rw [A.X.src_inv]; exact ht, by rw [A.X.tgt_inv]; exact hs⟩
  have h := E.tauHat_inv hφ.1
  rw [GroupoidStr.inv_inv] at h
  exact h

end CorrExtension

end SBLocalization

end Polyfold
