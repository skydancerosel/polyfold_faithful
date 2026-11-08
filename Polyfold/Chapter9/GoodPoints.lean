import Polyfold.Chapter9.Symmetric

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.2 "The Tangent and Boundary of Θ", the good-point analysis:
**Definition 9.2.2** (p. 410; 2017: Definition 9.4, p. 299), **Lemma 9.2.3** (p. 410; 2017:
Lemma 9.3, p. 299), **Remark 9.2.4** (p. 411; 2017: Remark 9.4, p. 300), **Lemma 9.2.5** (p. 411;
2017: Lemma 9.4, p. 300), **Definition 9.2.6** (p. 411; 2017: Definition 9.5, p. 300) and the
first half of **Lemma 9.2.7 (1)** (p. 412; 2017: Lemma 9.5, p. 300).  Numbers and pages are the
2021 text's, the 2017 ones in parentheses.  The tangent `TΘ` (Theorem 9.2.1, Definition 9.2.12)
is in `Polyfold/Chapter9/Tangent.lean`.

# Good and bad points of a branched ep⁺-subgroupoid

## The text, paraphrased

(Definition 9.2.2) For an equidimensional branched ep⁺-subgroupoid `Θ` with a local branching
structure `(Mᵢ)_{i ∈ I}`, `(σᵢ)` on `U = U(x)`, put `M_U = ⋃ Mᵢ`.  A point `y ∈ M_U` is *good*
(for the structure) if some open `V(y) ⊆ U(x)` has `V(y) ∩ Mᵢ = V(y) ∩ Mⱼ` for all
`i, j ∈ I_y = {k | y ∈ M_k}`.  (Lemma 9.2.3) For two structures on `U(x)` (with `M_U = N_U`), a
point good for the first is good for the second.  *Proof* (text): shrink `V(y)` so that also
`Mᵢ ∩ V(y) = ∅` for `i ∉ I_y` (properness); then `Θ` is constant on `V(y) ∩ M_U`; for the second
structure `J_z ⊆ J_y` near `y` (properness), so `Θ(z) = ∑_{J_z} τⱼ ≤ ∑_{J_y} τⱼ = Θ(y)`, with
equality only if `J_z = J_y`; hence the `Nⱼ`, `j ∈ J_y`, agree near `y`.  (Remark 9.2.4) (a) Being
good is intrinsic; (b) at a good point `Θ = σ · δ_M` near `y` for one submanifold `M` properly
embedded in `V(y)` and `σ > 0`.  (Lemma 9.2.5) For a morphism `φ` with `s(φ) ∈ supp(Θ)`,
`s(φ)` is good iff `t(φ)` is.  (Definition 9.2.6) `S^g_Θ` is the set of good points of
`supp(Θ)`, `S^b_Θ = supp(Θ) ∖ S^g_Θ` the bad ones; they descend to `|X|`:
`π⁻¹(|S^g_Θ|) = S^g_Θ`, `π⁻¹(|S^b_Θ|) = S^b_Θ`.  (Lemma 9.2.7) (1) `S^g_Θ` is open and dense in
`supp(Θ)`, `S^b_Θ` closed and nowhere dense; (2) for a bad `x` and a local branching structure on
`U(x)`, every `Mᵢ` contains a sequence of good points converging to `x`.

## What is formalized

* `LocalBranchingStructure.MU` (`M_U`), `MU_eq` (`M_U = supp(Θ) ∩ U(x)`),
  `isOpen_U_diff_M`, `nbhdAt` (the open set `{z ∈ U(x) | z ∈ Mⱼ ⇒ y ∈ Mⱼ}`, the text's
  shrinking by properness), `isOpen_nbhdAt`, `le_of_mem_nbhdAt` (`Θ(z) ≤ Θ(y)` there),
  `eq_iff_of_mem_nbhdAt` (equality iff `I_y ⊆ I_z`).
* **Definition 9.2.2**: `LocalBranchingStructure.IsGoodPoint`, and its characterization
  `isGoodPoint_iff`: for `y ∈ U(x)`, `y` is good iff `y ∈ supp(Θ)` and `Θ` is constant on
  `supp(Θ)` near `y` (the content of the text's proof of Lemma 9.2.3).
* **Lemma 9.2.3**: `lemma_9_2_3`, for any two structures whose domains contain `y`.
* **Definition 9.2.6**: `EpGroupoid.goodSet` (`S^g_Θ`), `EpGroupoid.badSet` (`S^b_Θ`),
  `mem_goodSet_iff` (the intrinsic form), `preimage_π_image_goodSet`,
  `preimage_π_image_badSet` (the sets descend to `|X|`).
* **Remark 9.2.4**: `remark_9_2_4_a` (a good point is good for every structure),
  `remark_9_2_4_b`.
* **Lemma 9.2.5**: `lemma_9_2_5`, through `Sheet.apply_hat` (`Θ ∘ φ̂ = Θ` on `U(x)`).
* **Lemma 9.2.7 (1)**, the topological half: `lemma_9_2_7_1` (`S^g_Θ` open, `S^b_Θ` closed in
  `supp(Θ)`).
* `LocalBranchingStructure.restrictAt` (a structure at `x` restricts to a structure at every
  `y ∈ U(x)`: the `Mᵢ` through `y`, cut down to `nbhdAt y`), used for Definition 9.2.12.

## What the text leaves implicit, and the choices made

* Definition 9.2.2 and Lemmas 9.2.3, 9.2.5 are stated in the text for equidimensional `Θ`;
  none of the proofs here uses equidimensionality, so they are stated for every `Θ` with a local
  branching structure (for Lemma 9.2.5, every branched ep⁺-subgroupoid).
* Lemma 9.2.3 is stated in the text for two structures on the same `U(x)`; it holds for any two
  structures (at possibly different points) whose domains contain `y`, and is proved through the
  intrinsic characterization `isGoodPoint_iff`, which is the text's argument.
* `S^g_Θ` (Definition 9.2.6) is the set of `y ∈ supp(Θ)` that are good for some local branching
  structure whose domain contains `y`; by Lemma 9.2.3 they are good for every such structure
  (`remark_9_2_4_a`).  "In view of Remark 9.2.4 (c)" (p. 411): Remark 9.2.4 has only (a) and
  (b); a possible misprint for Lemma 9.2.5, which is what the descent to `|X|` uses.
* Remark 9.2.4 (b) is proved with `M = Mᵢ ∩ V(y)` for any `i ∈ I_y` and `σ = Θ(y)`.
* Lemma 9.2.5: the text's "transport local branching structures by morphisms" is replaced by
  the intrinsic characterization and `Θ ∘ φ̂ = Θ` on the sheet of `φ` (Definition 7.1.6's `φ̂`).
* In the proof of Lemma 9.2.3 the set `Q(z) = V(y) ∩ W(y)` is presumably `Q(y)`.

## Not formalized, and why

* **Lemma 9.2.7 (2)** and the density of `S^g_Θ` in Lemma 9.2.7 (1).  The proof picks points of
  `M_{i₀} ∩ D_k(x)` outside, or in the interior of, the sets `Σᵢ = Mᵢ ∩ M_{i₀} ∩ D_k(x)`, and
  concludes "clearly `x_k` is a good point".  That conclusion needs, for equidimensional
  submanifolds, that `M_{i₀} ⊆ Mᵢ` near a point forces `M_{i₀} = Mᵢ` near it (invariance of
  domain, or the local graph representation of Lemmas 9.2.10–9.2.11), and the compactness of
  `Mᵢ ∩ D_k(x)` needs the compactness of sc⁺-retracts of bounded sets; neither is in Part I.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

namespace LocalBranchingStructure

variable {x : Obj} (B : X.LocalBranchingStructure Θ x)

/-! ### The sets `M_U` and the neighbourhoods given by properness -/

/-- `M_U = ⋃ᵢ Mᵢ` (Definition 9.2.2). -/
def MU : Set Obj := ⋃ i, B.M i

/-- `M_U = supp(Θ) ∩ U(x)` (the weights are positive). -/
theorem MU_eq : B.MU = supp Θ ∩ B.U := by
  ext y
  simp only [MU, mem_iUnion, mem_inter_iff]
  constructor
  · rintro ⟨i, hi⟩
    have hyU := B.subset_U i hi
    exact ⟨(B.mem_supp_iff hyU).2 ⟨i, hi⟩, hyU⟩
  · rintro ⟨hs, hyU⟩
    exact (B.mem_supp_iff hyU).1 hs

/-- `U(x) ∖ Mⱼ` is open (`Mⱼ` is closed in `U(x)`, the inclusion being proper). -/
theorem isOpen_U_diff_M (j : B.ι) : IsOpen (B.U \ B.M j) := by
  have h := B.isOpen_U.isOpenMap_subtype_val _ (B.isClosed_M j).isOpen_compl
  convert h using 1
  ext z
  simp only [Set.mem_sdiff, mem_image, mem_compl_iff, mem_preimage, Subtype.exists,
    exists_and_right, exists_eq_right]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- The open neighbourhood `{z ∈ U(x) | z ∈ Mⱼ ⇒ y ∈ Mⱼ}` of `y ∈ U(x)`: the points of `U(x)`
off every `Mⱼ` not passing through `y` (the shrinking "by properness" in the proof of
Lemma 9.2.3). -/
def nbhdAt (y : Obj) : Set Obj := {z | z ∈ B.U ∧ ∀ j, z ∈ B.M j → y ∈ B.M j}

theorem nbhdAt_subset (y : Obj) : B.nbhdAt y ⊆ B.U := fun _ hz => hz.1

theorem mem_nbhdAt_self {y : Obj} (hy : y ∈ B.U) : y ∈ B.nbhdAt y := ⟨hy, fun _ h => h⟩

theorem isOpen_nbhdAt (y : Obj) : IsOpen (B.nbhdAt y) := by
  classical
  have h : B.nbhdAt y = B.U ∩ ⋂ j, (if y ∈ B.M j then B.U else B.U \ B.M j) := by
    ext z
    simp only [nbhdAt, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨hz, h⟩
      refine ⟨hz, fun j => ?_⟩
      split_ifs with hj
      · exact hz
      · exact ⟨hz, fun hzj => hj (h j hzj)⟩
    · rintro ⟨hz, h⟩
      refine ⟨hz, fun j hzj => ?_⟩
      by_contra hj
      have h' := h j
      rw [if_neg hj] at h'
      exact h'.2 hzj
  rw [h]
  refine B.isOpen_U.inter (isOpen_iInter_of_finite fun j => ?_)
  split_ifs
  · exact B.isOpen_U
  · exact B.isOpen_U_diff_M j

open scoped Classical in
/-- On `nbhdAt y`, `Θ(z) = ∑_{J_z} σ ≤ ∑_{J_y} σ = Θ(y)` (`J_z ⊆ J_y`). -/
theorem le_of_mem_nbhdAt {y z : Obj} (hy : y ∈ B.U) (hz : z ∈ B.nbhdAt y) : Θ z ≤ Θ y := by
  rw [B.eq_sum z hz.1, B.eq_sum y hy]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i _ _ => (B.σ_pos i).le
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hz.2 i hi

open scoped Classical in
/-- On `nbhdAt y`, `Θ(z) = Θ(y)` iff `I_y ⊆ I_z` (then `I_z = I_y`; the weights are positive). -/
theorem eq_iff_of_mem_nbhdAt {y z : Obj} (hy : y ∈ B.U) (hz : z ∈ B.nbhdAt y) :
    Θ z = Θ y ↔ ∀ i, y ∈ B.M i → z ∈ B.M i := by
  constructor
  · intro h i hyi
    by_contra hzi
    have hlt : Θ z < Θ y := by
      rw [B.eq_sum z hz.1, B.eq_sum y hy]
      refine Finset.sum_lt_sum_of_subset (i := i) (fun j hj => ?_) ?_ ?_ (B.σ_pos i)
        fun j _ _ => (B.σ_pos j).le
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact hz.2 j hj
      · simpa using hyi
      · simpa using hzi
    exact (ne_of_lt hlt) h
  · intro h
    rw [B.eq_sum z hz.1, B.eq_sum y hy]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hz.2 i, h i⟩

/-! ### Definition 9.2.2 and Lemma 9.2.3 -/

/-- **Definition 9.2.2, p. 410 (2017: Definition 9.4, p. 299) (good point)**: `y ∈ M_U` is a good
point of the local branching structure if some open `V(y) ⊆ U(x)` containing `y` has
`V(y) ∩ Mᵢ = V(y) ∩ Mⱼ` for all `i, j ∈ I_y = {k | y ∈ M_k}`. -/
def IsGoodPoint (y : Obj) : Prop :=
  y ∈ B.MU ∧ ∃ V : Set Obj, IsOpen V ∧ y ∈ V ∧ V ⊆ B.U ∧
    ∀ i j, y ∈ B.M i → y ∈ B.M j → V ∩ B.M i = V ∩ B.M j

/-- **The intrinsic form of Definition 9.2.2** (the argument of the proof of Lemma 9.2.3): for
`y ∈ U(x)`, `y` is a good point iff `y ∈ supp(Θ)` and `Θ` is constant on `supp(Θ)` near `y`. -/
theorem isGoodPoint_iff {y : Obj} (hy : y ∈ B.U) :
    B.IsGoodPoint y ↔ y ∈ supp Θ ∧ ∃ V ∈ 𝓝 y, ∀ z ∈ V, z ∈ supp Θ → Θ z = Θ y := by
  constructor
  · rintro ⟨hyM, V, hV, hyV, -, hVM⟩
    rw [B.MU_eq] at hyM
    refine ⟨hyM.1, V ∩ B.nbhdAt y, (hV.inter (B.isOpen_nbhdAt y)).mem_nhds
      ⟨hyV, B.mem_nbhdAt_self hy⟩, fun z hz hzs => ?_⟩
    obtain ⟨k, hzk⟩ := (B.mem_supp_iff hz.2.1).1 hzs
    have hyk : y ∈ B.M k := hz.2.2 k hzk
    refine (B.eq_iff_of_mem_nbhdAt hy hz.2).2 fun i hyi => ?_
    have h' : z ∈ V ∩ B.M k := ⟨hz.1, hzk⟩
    rw [hVM k i hyk hyi] at h'
    exact h'.2
  · rintro ⟨hys, V, hV, hc⟩
    obtain ⟨V₁, hV₁V, hV₁, hyV₁⟩ := mem_nhds_iff.1 hV
    refine ⟨B.MU_eq ▸ ⟨hys, hy⟩, V₁ ∩ B.nbhdAt y, hV₁.inter (B.isOpen_nbhdAt y),
      ⟨hyV₁, B.mem_nbhdAt_self hy⟩, fun z hz => (B.nbhdAt_subset y) hz.2,
      fun i j hyi hyj => ?_⟩
    have key : ∀ i j, y ∈ B.M i → y ∈ B.M j →
        V₁ ∩ B.nbhdAt y ∩ B.M i ⊆ V₁ ∩ B.nbhdAt y ∩ B.M j := by
      intro i j _ hyj z hz
      have hzs : z ∈ supp Θ := (B.mem_supp_iff hz.1.2.1).2 ⟨i, hz.2⟩
      have hΘz := hc z (hV₁V hz.1.1) hzs
      exact ⟨hz.1, (B.eq_iff_of_mem_nbhdAt hy hz.1.2).1 hΘz j hyj⟩
    exact Subset.antisymm (key i j hyi hyj) (key j i hyj hyi)

/-- **Lemma 9.2.3, p. 410 (2017: Lemma 9.3, p. 299)**: if `y` is a good point of one local
branching structure of `Θ`, it is a good point of every local branching structure whose domain
contains `y` (the text: two structures on the same `U(x)`). -/
theorem lemma_9_2_3 {x' : Obj} (B' : X.LocalBranchingStructure Θ x') {y : Obj} (hyU : y ∈ B.U)
    (hyU' : y ∈ B'.U) (h : B.IsGoodPoint y) : B'.IsGoodPoint y :=
  (B'.isGoodPoint_iff hyU').2 ((B.isGoodPoint_iff hyU).1 h)

/-! ### Restriction to a point of `U(x)` -/

open scoped Classical in
/-- **The restriction of a local branching structure at `x` to a point `y ∈ U(x)`**: the domain
`nbhdAt y`, the submanifolds `Mᵢ ∩ nbhdAt y` for the `i` with `y ∈ Mᵢ`, the same weights. -/
def restrictAt {y : Obj} (hy : y ∈ B.U) : X.LocalBranchingStructure Θ y where
  U := B.nbhdAt y
  isOpen_U := B.isOpen_nbhdAt y
  mem_U := B.mem_nbhdAt_self hy
  ι := {i // y ∈ B.M i}
  M i := B.M i.1 ∩ B.nbhdAt y
  subset_U _ := inter_subset_right
  isSmoothSubmanifold i := (B.isSmoothSubmanifold i.1).inter_isOpen (B.isOpen_nbhdAt y)
  mem_M i := ⟨i.2, B.mem_nbhdAt_self hy⟩
  isProperMap i := by
    refine (isProperMap_inclusion_iff _).2 ?_
    have h := (B.isClosed_M i.1).preimage (continuous_inclusion (B.nbhdAt_subset y))
    convert h using 1
    ext z
    exact ⟨fun h => h.1, fun h => ⟨h, z.2⟩⟩
  σ i := B.σ i.1
  σ_pos i := B.σ_pos i.1
  eq_sum z hz := by
    rw [B.eq_sum z (B.nbhdAt_subset y hz)]
    symm
    refine Finset.sum_bij (fun a _ => a.1) (fun a ha => ?_) (fun a _ b _ h => Subtype.ext h)
      (fun i hi => ?_) fun _ _ => rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ha.1
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨⟨i, hz.2 i hi⟩, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hi, hz⟩, rfl⟩

@[simp] theorem restrictAt_U {y : Obj} (hy : y ∈ B.U) : (B.restrictAt hy).U = B.nbhdAt y := rfl

@[simp] theorem restrictAt_M {y : Obj} (hy : y ∈ B.U) (i : (B.restrictAt hy).ι) :
    (B.restrictAt hy).M i = B.M i.1 ∩ B.nbhdAt y := rfl

@[simp] theorem restrictAt_σ {y : Obj} (hy : y ∈ B.U) (i : (B.restrictAt hy).ι) :
    (B.restrictAt hy).σ i = B.σ i.1 := rfl

end LocalBranchingStructure

/-! ### Definition 9.2.6 -/

variable (X) in
/-- **Definition 9.2.6, p. 411 (2017: Definition 9.5, p. 300) (good points)**: the set `S^g_Θ`
of points of `supp(Θ)` that are good (Definition 9.2.2) for some local branching structure whose
domain contains them. -/
def goodSet (Θ : Obj → ℚ) : Set Obj :=
  {y | y ∈ supp Θ ∧ ∃ (x : Obj) (B : X.LocalBranchingStructure Θ x), y ∈ B.U ∧ B.IsGoodPoint y}

variable (X) in
/-- **Definition 9.2.6 (bad points)**: `S^b_Θ = supp(Θ) ∖ S^g_Θ`. -/
def badSet (Θ : Obj → ℚ) : Set Obj := supp Θ \ X.goodSet Θ

/-- **Remark 9.2.4 (a), p. 411 (2017: Remark 9.4 (a), p. 300)**: a good point of `Θ` is a good
point of every local branching structure whose domain contains it (Lemma 9.2.3). -/
theorem remark_9_2_4_a {y : Obj} (hy : y ∈ X.goodSet Θ) {x : Obj}
    (B : X.LocalBranchingStructure Θ x) (hyU : y ∈ B.U) : B.IsGoodPoint y := by
  obtain ⟨-, x', B', hyU', hB'⟩ := hy
  exact B'.lemma_9_2_3 B hyU' hyU hB'

/-- **The intrinsic description of `S^g_Θ`**: for a branched ep⁺-subgroupoid, `y` is a good point
iff `y ∈ supp(Θ)` and `Θ` is constant on `supp(Θ)` near `y`. -/
theorem mem_goodSet_iff (hΘ : X.IsBranchedEpSubgroupoid Θ) {y : Obj} :
    y ∈ X.goodSet Θ ↔ y ∈ supp Θ ∧ ∃ V ∈ 𝓝 y, ∀ z ∈ V, z ∈ supp Θ → Θ z = Θ y := by
  constructor
  · rintro ⟨hys, x, B, hyU, hB⟩
    exact (B.isGoodPoint_iff hyU).1 hB
  · rintro ⟨hys, h⟩
    obtain ⟨B⟩ := hΘ.localBranching y hys
    exact ⟨hys, y, B, B.mem_U, (B.isGoodPoint_iff B.mem_U).2 ⟨hys, h⟩⟩

open scoped Classical in
/-- **Remark 9.2.4 (b), p. 411 (2017: Remark 9.4 (b), p. 300)**: near a good point `y`, `Θ` is
`σ · δ_M` for an open `V(y)`, a submanifold `M` through `y` properly embedded in `V(y)` and the
weight `σ = Θ(y) > 0`. -/
theorem remark_9_2_4_b (hΘ : X.IsBranchedEpSubgroupoid Θ) {y : Obj} (hy : y ∈ X.goodSet Θ) :
    ∃ V : Set Obj, IsOpen V ∧ y ∈ V ∧ ∃ (M : Set Obj) (hMV : M ⊆ V),
      X.PObj.IsSmoothSubmanifold M ∧ y ∈ M ∧ IsProperMap (inclusion hMV) ∧ 0 < Θ y ∧
        ∀ z ∈ V, Θ z = if z ∈ M then Θ y else 0 := by
  classical
  obtain ⟨B⟩ := hΘ.localBranching y hy.1
  obtain ⟨hyM, V, hV, hyV, hVU, hVM⟩ := remark_9_2_4_a hy B B.mem_U
  obtain ⟨i₀, -⟩ := mem_iUnion.1 hyM
  refine ⟨V, hV, hyV, B.M i₀ ∩ V, inter_subset_right,
    (B.isSmoothSubmanifold i₀).inter_isOpen hV, ⟨B.mem_M i₀, hyV⟩, ?_, hy.1, fun z hz => ?_⟩
  · refine (isProperMap_inclusion_iff _).2 ?_
    have h := (B.isClosed_M i₀).preimage (continuous_inclusion hVU)
    convert h using 1
    ext w
    exact ⟨fun h => h.1, fun h => ⟨h, w.2⟩⟩
  · have hall : ∀ i, (z ∈ B.M i ↔ z ∈ B.M i₀) := fun i => by
      have h := hVM i i₀ (B.mem_M i) (B.mem_M i₀)
      constructor
      · intro hzi
        have h1 : z ∈ V ∩ B.M i := ⟨hz, hzi⟩
        rw [h] at h1
        exact h1.2
      · intro hzi
        have h1 : z ∈ V ∩ B.M i₀ := ⟨hz, hzi⟩
        rw [← h] at h1
        exact h1.2
    rw [B.eq_sum z (hVU hz), B.eq_sum y B.mem_U]
    by_cases hzi : z ∈ B.M i₀
    · rw [if_pos ⟨hzi, hz⟩]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hall i, hzi, B.mem_M i]
    · rw [if_neg fun h => hzi h.1]
      refine Finset.sum_eq_zero fun i hi => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hall i] at hi
      exact (hzi hi).elim

/-! ### Lemma 9.2.5 -/

/-- `Θ ∘ φ̂ = Θ` on the domain `U(x)` of a sheet, for a functor `Θ` (`φ̂ = t ∘ (s|𝐔)⁻¹`). -/
theorem Sheet.apply_hat (hΘ : X.IsFunctorial Θ) (S : X.Sheet) {z : Obj} (hz : z ∈ S.srcSet) :
    Θ (S.hat z) = Θ z := by
  change Θ (X.tgt (S.srcInv z)) = Θ z
  rw [← hΘ (S.srcInv z), S.isScDiffeoOn_src.right_inv z hz]

/-- One direction of Lemma 9.2.5: if `t(φ)` is a good point, so is `s(φ)`. -/
theorem src_mem_goodSet_of_tgt (hΘ : X.IsBranchedEpSubgroupoid Θ) (φ : Mor)
    (h : X.tgt φ ∈ X.goodSet Θ) : X.src φ ∈ X.goodSet Θ := by
  obtain ⟨hts, V, hV, hc⟩ := (mem_goodSet_iff hΘ).1 h
  have hss : X.src φ ∈ supp Θ := by
    change 0 < Θ (X.src φ); rw [hΘ.isFunctorial φ]; exact hts
  set S := X.sheetAt φ
  have hd := X.isScDiffeoOn_hat φ
  have hcont : ContinuousAt (X.hat φ) (X.src φ) :=
    hd.isScSmoothOn.continuousOn.continuousAt
      (hd.isScSmoothOn.isOpen.mem_nhds (X.src_mem_sheetAt φ))
  have hV' : X.hat φ ⁻¹' V ∈ 𝓝 (X.src φ) :=
    hcont.preimage_mem_nhds (by rw [X.hat_src]; exact hV)
  refine (mem_goodSet_iff hΘ).2 ⟨hss, S.srcSet ∩ X.hat φ ⁻¹' V,
    inter_mem (hd.isScSmoothOn.isOpen.mem_nhds (X.src_mem_sheetAt φ)) hV',
    fun z hz hzs => ?_⟩
  have hhat : Θ (X.hat φ z) = Θ z := Sheet.apply_hat hΘ.isFunctorial S hz.1
  have hzs' : X.hat φ z ∈ supp Θ := by change 0 < Θ (X.hat φ z); rw [hhat]; exact hzs
  rw [← hhat, hc _ hz.2 hzs', hΘ.isFunctorial φ]

/-- **Lemma 9.2.5, p. 411 (2017: Lemma 9.4, p. 300)**: for a morphism `φ` with
`s(φ) ∈ supp(Θ)`, `s(φ)` is a good point iff `t(φ)` is. -/
theorem lemma_9_2_5 (hΘ : X.IsBranchedEpSubgroupoid Θ) (φ : Mor) :
    X.src φ ∈ X.goodSet Θ ↔ X.tgt φ ∈ X.goodSet Θ := by
  refine ⟨fun h => ?_, src_mem_goodSet_of_tgt hΘ φ⟩
  have h' := src_mem_goodSet_of_tgt hΘ (X.inv φ) (by rwa [X.tgt_inv])
  rwa [X.src_inv] at h'

/-- **Definition 9.2.6, the descent to `|X|`**: `π⁻¹(|S^g_Θ|) = S^g_Θ`. -/
theorem preimage_π_image_goodSet (hΘ : X.IsBranchedEpSubgroupoid Θ) :
    X.π ⁻¹' (X.π '' X.goodSet Θ) = X.goodSet Θ := by
  refine Subset.antisymm (fun y hy => ?_) (subset_preimage_image _ _)
  obtain ⟨a, ha, hay⟩ := hy
  obtain ⟨φ, rfl, rfl⟩ := (X.π_eq_π_iff).1 hay
  exact (lemma_9_2_5 hΘ φ).1 ha

/-- **Definition 9.2.6, the descent to `|X|`**: `π⁻¹(|S^b_Θ|) = S^b_Θ`. -/
theorem preimage_π_image_badSet (hΘ : X.IsBranchedEpSubgroupoid Θ) :
    X.π ⁻¹' (X.π '' X.badSet Θ) = X.badSet Θ := by
  refine Subset.antisymm (fun y hy => ?_) (subset_preimage_image _ _)
  obtain ⟨a, ha, hay⟩ := hy
  obtain ⟨φ, rfl, rfl⟩ := (X.π_eq_π_iff).1 hay
  refine ⟨?_, fun hg => ha.2 ((lemma_9_2_5 hΘ φ).2 hg)⟩
  change 0 < Θ (X.tgt φ)
  rw [← hΘ.isFunctorial φ]
  exact ha.1

/-! ### Lemma 9.2.7 (1), the topological half -/

/-- **Lemma 9.2.7 (1), p. 412 (2017: Lemma 9.5 (1), p. 300), first half**: `S^g_Θ` is open and
`S^b_Θ` is closed in `supp(Θ)` (with the topology induced from `X`).  The density of `S^g_Θ`
rests on Lemma 9.2.7 (2), which is not formalized (see the module docstring). -/
theorem lemma_9_2_7_1 (hΘ : X.IsBranchedEpSubgroupoid Θ) :
    IsOpen ((↑) ⁻¹' X.goodSet Θ : Set (supp Θ)) ∧
      IsClosed ((↑) ⁻¹' X.badSet Θ : Set (supp Θ)) := by
  have hopen : IsOpen ((↑) ⁻¹' X.goodSet Θ : Set (supp Θ)) := by
    refine isOpen_iff_mem_nhds.2 fun y hy => ?_
    obtain ⟨-, V, hV, hc⟩ := (mem_goodSet_iff hΘ).1 hy
    obtain ⟨O, hOV, hO, hyO⟩ := mem_nhds_iff.1 hV
    refine Filter.mem_of_superset
      (continuous_subtype_val.continuousAt.preimage_mem_nhds (hO.mem_nhds hyO)) fun z hz => ?_
    refine (mem_goodSet_iff hΘ).2 ⟨z.2, O, hO.mem_nhds hz, fun w hw hws => ?_⟩
    rw [hc w (hOV hw) hws, hc z.1 (hOV hz) z.2]
  refine ⟨hopen, ?_⟩
  have h : ((↑) ⁻¹' X.badSet Θ : Set (supp Θ)) = ((↑) ⁻¹' X.goodSet Θ)ᶜ := by
    ext z
    simp only [badSet, mem_preimage, Set.mem_sdiff, mem_compl_iff]
    exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩
  rw [h]
  exact hopen.isClosed_compl

end EpGroupoid

end Polyfold
