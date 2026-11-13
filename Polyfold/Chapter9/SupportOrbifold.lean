import Polyfold.Chapter9.Symmetric
import Polyfold.Chapter7.SubGroupoid

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 9,
§9.1, **Proposition 9.1.9** (p. 405; 2017: Proposition 9.1, p. 294), orbifold-type, and the first
step of its proof.

# The orbifold structure on `|supp(Θ)|` for `Θ` of orbifold-type

## The text, paraphrased

(Proposition 9.1.9 (2)) For a branched ep⁺-subgroupoid `Θ` of orbifold-type (values in `{0, 1}`),
`X` induces on `Z = |supp(Θ)|` a natural orbifold structure.  *Proof* (text): near `x ∈ supp(Θ)`
all the `Mᵢ` of a local branching structure coincide (`0 < Θ(y) < Θ(x) = 1` otherwise), so
`Θ = 1_{M_x}` on `U(x)`, `M_x` a submanifold; the étale proper groupoid with objects the disjoint
union of the `M_x` and morphisms `{φ | s(φ) ∈ M_x, t(φ) ∈ M_{x'}}` maps by a functor `β` to `Z`,
`|β|` is a homeomorphism, and this equips `Z` with an orbifold structure (up to equivalence for
other choices).

## What is formalized

* `EpGroupoid.supp_inter_eq_of_isOrbifoldType` (the first step of the proof): for `Θ` of
  orbifold-type and a local branching structure `(Mᵢ)` at `x ∈ supp(Θ)`,
  `supp(Θ) ∩ U(x) = M_{i}` for every `i`.
* `EpGroupoid.isSmoothSubmanifold_supp_of_isOrbifoldType`: `supp(Θ)` is a smooth
  finite-dimensional submanifold of `X` (Definition 4.2.1).
* `EpGroupoid.isEpSubgroupoid_supp_of_isOrbifoldType`: `supp(Θ)` is an ep-subgroupoid
  (Definition 7.1.21: a saturated sub-M-polyfold), so the full subcategory on `supp(Θ)` is an
  ep-groupoid (`subEpGroupoid`, Proposition 7.1.22) whose object M-polyfold is a smooth
  submanifold of `X`.
* `EpGroupoid.orbitSuppHomeomorph`: for a saturated `A`, the natural map
  `|A| → π(A) ⊆ |X|` induced by the inclusion is a homeomorphism.
* **`EpGroupoid.proposition_9_1_9_two`**: for `Θ` of orbifold-type, the full subcategory on
  `supp(Θ)` is an ep-groupoid with object space a smooth submanifold of `X`, and its orbit space
  is homeomorphic to `Z = |supp(Θ)|` by the map induced by the inclusion.

## How it relates to the text

The text's orbifold structure is the equivalence class of the étale proper groupoid built from the
`M_x`; the full subcategory on `supp(Θ)` is a choice-free representative (its objects are covered
by the open pieces `M_x`, it is Morita equivalent to the text's groupoid; that equivalence is not
formalized).  "Smooth" is the M⁺-polyfold sense of Remark 9.1.10: the objects form a smooth
finite-dimensional submanifold of `X`.  The hypothesis that `|X|` is paracompact is not used.
-/

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

/-! ### The first step of the proof: one sheet -/

/-- **The first step of the proof of Proposition 9.1.9**: for `Θ` of orbifold-type, every sheet
`Mᵢ` of a local branching structure at `x ∈ supp(Θ)` is `supp(Θ) ∩ U(x)` (`Θ(y) = 1` forces `y`
into every `Mⱼ`, the weights being positive and summing to `Θ(x) = 1`). -/
theorem supp_inter_eq_of_isOrbifoldType (ho : IsOrbifoldType Θ) {x : Obj} (hx : x ∈ supp Θ)
    (B : X.LocalBranchingStructure Θ x) (i : B.ι) : supp Θ ∩ B.U = B.M i := by
  classical
  have hΘx : Θ x = 1 := (ho x).resolve_left (ne_of_gt hx)
  have hall : Θ x = ∑ j, B.σ j := by
    rw [B.eq_sum x B.mem_U]
    exact Finset.sum_congr (Finset.filter_true_of_mem fun j _ => B.mem_M j) fun _ _ => rfl
  ext y
  constructor
  · rintro ⟨hy, hyU⟩
    have hΘy : Θ y = 1 := (ho y).resolve_left (ne_of_gt hy)
    rw [B.eq_sum y hyU] at hΘy
    rw [hΘx] at hall
    by_contra hyi
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => y ∈ B.M j) B.σ
    have hpos : 0 < ∑ j ∈ Finset.univ.filter (fun j => y ∉ B.M j), B.σ j :=
      Finset.sum_pos (fun j _ => B.σ_pos j) ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hyi⟩⟩
    linarith
  · intro hyi
    have hyU := B.subset_U i hyi
    refine ⟨?_, hyU⟩
    change 0 < Θ y
    rw [B.eq_sum y hyU]
    exact Finset.sum_pos (fun j _ => B.σ_pos j) ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hyi⟩⟩

/-- For `Θ` of orbifold-type, a local branching structure at `x ∈ supp(Θ)` has at least one
sheet. -/
theorem nonempty_ι_of_mem_supp {x : Obj} (hx : x ∈ supp Θ) (B : X.LocalBranchingStructure Θ x) :
    Nonempty B.ι := by
  classical
  by_contra h
  rw [not_nonempty_iff] at h
  have := B.eq_sum x B.mem_U
  simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.sum_empty] at this
  exact (ne_of_gt hx) this

/-- **`supp(Θ)` is a smooth finite-dimensional submanifold of `X`** for `Θ` of orbifold-type
(Definition 4.2.1): near each point it is the sheet `M_x ∩ U(x)`. -/
theorem isSmoothSubmanifold_supp_of_isOrbifoldType (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (ho : IsOrbifoldType Θ) : X.PObj.IsSmoothSubmanifold (supp Θ) := by
  intro a ha
  obtain ⟨B⟩ := hΘ.localBranching a ha
  obtain ⟨i⟩ := nonempty_ι_of_mem_supp ha B
  obtain ⟨W, hWo, haW, hWU, r, hr, himg⟩ :=
    (B.isSmoothSubmanifold i).exists_subset B.isOpen_U (B.mem_M i) B.mem_U
  refine ⟨W, hWo, haW, r, hr, ?_⟩
  rw [himg, ← supp_inter_eq_of_isOrbifoldType ho ha B i, inter_assoc, inter_eq_right.2 hWU]

/-- `supp(Θ)` is saturated (`Θ` is a functor). -/
theorem isSaturated_supp (hΘ : X.IsFunctorial Θ) : X.IsSaturated (supp Θ) :=
  preimage_π_orbitSupp hΘ

/-- **`supp(Θ)` is an ep-subgroupoid** (Definition 7.1.21) for `Θ` of orbifold-type. -/
theorem isEpSubgroupoid_supp_of_isOrbifoldType (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (ho : IsOrbifoldType Θ) : X.IsEpSubgroupoid (supp Θ) :=
  ⟨(isSmoothSubmanifold_supp_of_isOrbifoldType hΘ ho).isSubMPolyfold,
    isSaturated_supp hΘ.isFunctorial⟩

/-! ### The orbit space of a saturated full subcategory -/

section OrbitSupp

variable (X)

/-- `|a| ∈ |A|` ↦ `|a| ∈ π(A) ⊆ |X|`: the map of orbit spaces induced by the inclusion of the full
subcategory on `A`. -/
def orbitSuppMap (A : Set Obj) : (X.fullSub A).OrbitSpace → X.π '' A :=
  Quotient.lift (fun a : A => (⟨X.π a.1, a.1, a.2, rfl⟩ : X.π '' A)) <| by
    rintro a b ⟨φ, rfl, rfl⟩
    exact Subtype.ext ((X.π_eq_π_iff).2 ⟨φ.1, rfl, rfl⟩)

variable {X}

theorem orbitSuppMap_mk (A : Set Obj) (a : A) :
    X.orbitSuppMap A (Quotient.mk _ a) = ⟨X.π a.1, a.1, a.2, rfl⟩ := rfl

theorem bijective_orbitSuppMap (A : Set Obj) :
    Bijective (X.orbitSuppMap A) := by
  refine ⟨fun p q h => ?_, ?_⟩
  · induction p using Quotient.inductionOn with | h a => ?_
    induction q using Quotient.inductionOn with | h b => ?_
    obtain ⟨φ, hs, ht⟩ := (X.π_eq_π_iff).1 (congrArg Subtype.val h)
    exact Quotient.sound ⟨⟨φ, hs ▸ a.2, ht ▸ b.2⟩, Subtype.ext hs, Subtype.ext ht⟩
  · rintro ⟨_, a, ha, rfl⟩
    exact ⟨Quotient.mk _ ⟨a, ha⟩, rfl⟩

/-- **The natural homeomorphism `|A| ≅ π(A)`** for a saturated sub-M-polyfold `A` (an
ep-subgroupoid): the orbit space of the ep-groupoid `subEpGroupoid hA` is homeomorphic to the
subspace `π(A)` of `|X|` by the map induced by the inclusion.  Openness: for `T = T' ∩ A`
saturated in `A`, `π(T) = π(T') ∩ π(A)` by saturation, and `π` is open (Proposition 7.1.8). -/
def orbitSuppHomeomorph {A : Set Obj} (hA : X.IsEpSubgroupoid A) [ParacompactSpace A] :
    (subEpGroupoid hA).OrbitSpace ≃ₜ X.π '' A := by
  refine (Equiv.ofBijective (X.orbitSuppMap A)
    (bijective_orbitSuppMap A)).toHomeomorphOfContinuousOpen ?_ ?_
  · exact continuous_quot_lift _ ((X.continuous_π.comp continuous_subtype_val).subtype_mk _)
  · intro S hS
    have hT : IsOpen (Quotient.mk (subEpGroupoid hA).orbitSetoid ⁻¹' S) :=
      hS.preimage continuous_quot_mk
    obtain ⟨T', hT'o, hT'⟩ := isOpen_induced_iff.1 hT
    have himg : (Equiv.ofBijective (X.orbitSuppMap A) (bijective_orbitSuppMap A)) '' S
        = Subtype.val ⁻¹' (X.π '' T') := by
      ext ⟨z, a, ha, rfl⟩
      constructor
      · rintro ⟨p, hp, hpz⟩
        induction p using Quotient.inductionOn with | h b => ?_
        have hb : b ∈ Subtype.val ⁻¹' T' := by rw [hT']; exact hp
        exact ⟨b.1, hb, congrArg Subtype.val hpz⟩
      · rintro ⟨y, hyT', hya⟩
        have hyA : y ∈ A := by
          have : y ∈ X.π ⁻¹' (X.π '' A) := ⟨a, ha, hya.symm⟩
          rwa [hA.isSaturated] at this
        have hmem : (⟨y, hyA⟩ : A) ∈ Quotient.mk (subEpGroupoid hA).orbitSetoid ⁻¹' S := by
          rw [← hT']; exact hyT'
        exact ⟨Quotient.mk _ ⟨y, hyA⟩, hmem, Subtype.ext hya⟩
    rw [himg]
    exact (X.proposition_7_1_8 _ hT'o).preimage continuous_subtype_val

theorem orbitSuppHomeomorph_π {A : Set Obj} (hA : X.IsEpSubgroupoid A) [ParacompactSpace A]
    (a : A) : (orbitSuppHomeomorph hA ((subEpGroupoid hA).π a) : X.OrbitSpace) = X.π a.1 := rfl

end OrbitSupp

/-! ### Proposition 9.1.9 (2) -/

/-- **2021 Proposition 9.1.9 (2)**, p. 405 (2017: Proposition 9.1 (2), p. 295): for a branched
ep⁺-subgroupoid `Θ` of orbifold-type, `X` induces on `Z = |supp(Θ)|` an orbifold structure: the
full subcategory on `supp(Θ)` is an ep-groupoid (`subEpGroupoid hA`, étale and proper), its object
space `supp(Θ)` is a smooth finite-dimensional submanifold of `X` (Remark 9.1.10: the M⁺-polyfold
sense), and the map `|supp(Θ)|_{subEpGroupoid} → Z` induced by the inclusion is a homeomorphism.
The text's groupoid (objects `⊔ M_x`) is a Morita equivalent choice. -/
theorem proposition_9_1_9_two (hΘ : X.IsBranchedEpSubgroupoid Θ) (ho : IsOrbifoldType Θ) :
    ∃ hA : X.IsEpSubgroupoid (supp Θ), X.PObj.IsSmoothSubmanifold (supp Θ) ∧
      haveI := X.PObj.paracompactSpace_subtype (supp Θ)
      ∃ e : (subEpGroupoid hA).OrbitSpace ≃ₜ X.orbitSupp Θ,
        ∀ a : supp Θ, (e ((subEpGroupoid hA).π a) : X.OrbitSpace) = X.π a.1 :=
  haveI := X.PObj.paracompactSpace_subtype (supp Θ)
  ⟨isEpSubgroupoid_supp_of_isOrbifoldType hΘ ho, isSmoothSubmanifold_supp_of_isOrbifoldType hΘ ho,
    orbitSuppHomeomorph _, fun a => orbitSuppHomeomorph_π _ a⟩

end EpGroupoid

end Polyfold
