import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_46

/-! Round trip for V9_46 (Lemma 9.4.8, 2021 p. 432; 2017: Lemma 9.15): the points with at least
two `∼_y`-classes form a null set.

`A` is the conjunction of the types of the two listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `MPolyfold.SheetGeometry.lemma_9_4_8` and
`MPolyfold.SheetGeometry.isNullIn_diff_MStar`.  `IsNullIn` and `MStar` are definitions
(vocabulary).

* `A → B` is proved.  `A` is stated for an abstract `SheetGeometry` (essential points and null
  sets of the sheets as data, Lemmas 9.4.4 and 9.4.6 as fields) on an M-polyfold; `B` for sheets
  that are immersed `n`-manifolds with corners `jᵢ : Nᵢ → F`, essential points and null sets from
  `essentialSet` / `IsMeasureZero` in `Nᵢ`.  The proof builds from `B`'s structure `L` a
  `SheetGeometry` `tG L` on the discrete M-polyfold `Tag F ι = F ⊕ (ι × ι)`: sheet `i` is
  `Mᵢ ∪ {tags (p, q) with p = i or q = i}`.  The tags make the pair `{a, b}` readable off
  `M̃_a ∩ M̃_b` (for `a ≠ b` its tags are `(a, b), (b, a)`), so the essential points can be
  defined from the set `K` alone (`tEss`: `z` is essential if `z ∈ K^e` for the reference sheet
  of one of the tags of `K`), which makes Lemma 9.4.4 (`ess_comm`) hold by `inter_comm`; the
  null sets are `B`'s, plus "contains no tag of the sheet" (which gives `not_isNull_self`);
  Lemma 9.4.6 (`isNull_diff_ess`) is the project's `lemma_9_4_6` in `Nₐ`; `submanifoldTangent_eq`
  holds because in a discrete M-polyfold `T_zN` only depends on `N ∩ {z}`.  The links of `tG L`
  at a point of `F` are `B`'s links and their reverses, so its classes are `B`'s (`two_le`), and
  `lemma_9_4_8` for `tG L` is `B`.
* `B → A`: not proved.  `A` holds for every `SheetGeometry` (any M-polyfold, any data
  satisfying the fields); `B` is one concrete model and says nothing about abstract data.  (`A`
  has a short direct proof from the fields; it is not given here, as it would not use `B`.)
-/

namespace RoundTrip.V9_46
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.SheetGeometry.lemma_9_4_8.{0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.SheetGeometry.isNullIn_diff_MStar.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.SheetGeometry.lemma_9_4_8.{0, 0},
    @Polyfold.MPolyfold.SheetGeometry.isNullIn_diff_MStar.{0, 0}⟩

/-! ### The tagged discrete ambient -/

/-- `F` with one tag point for every ordered pair of indices, as a discrete space. -/
def Tag (F ι : Type) : Type := F ⊕ (ι × ι)

namespace Tag
variable {F ι : Type}

instance : TopologicalSpace (Tag F ι) := ⊥
instance : DiscreteTopology (Tag F ι) := ⟨rfl⟩

/-- A point of `F`. -/
def pt (z : F) : Tag F ι := Sum.inl z
/-- The tag of a pair of indices. -/
def tag (p : ι × ι) : Tag F ι := Sum.inr p

theorem pt_injective : Function.Injective (pt : F → Tag F ι) := Sum.inl_injective
theorem tag_injective : Function.Injective (tag : ι × ι → Tag F ι) := Sum.inr_injective
theorem pt_ne_tag {z : F} {p : ι × ι} : (pt z : Tag F ι) ≠ tag p := Sum.inl_ne_inr
theorem tag_ne_pt {z : F} {p : ι × ι} : (tag p : Tag F ι) ≠ pt z := Sum.inr_ne_inl

end Tag

open Tag

section
variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {x : F}
  (L : LocalStrB n F x)

/-- The tagged sheet `M̃ᵢ = Mᵢ ∪ {tags (p, q) | p = i ∨ q = i}`. -/
def tM (i : L.ι) : Set (Tag F L.ι) :=
  pt '' (L.S i).M ∪ tag '' {p : L.ι × L.ι | p.1 = i ∨ p.2 = i}

variable {L}

theorem mem_tM_pt {z : F} {i : L.ι} : (pt z : Tag F L.ι) ∈ tM L i ↔ z ∈ (L.S i).M := by
  constructor
  · rintro (⟨w, hw, he⟩ | ⟨p, -, he⟩)
    · rwa [pt_injective he] at hw
    · exact absurd he tag_ne_pt
  · intro h
    exact Or.inl ⟨z, h, rfl⟩

theorem mem_tM_tag {p : L.ι × L.ι} {i : L.ι} :
    (tag p : Tag F L.ι) ∈ tM L i ↔ p.1 = i ∨ p.2 = i := by
  constructor
  · rintro (⟨w, -, he⟩ | ⟨q, hq, he⟩)
    · exact absurd he pt_ne_tag
    · rwa [tag_injective he] at hq
  · intro h
    exact Or.inr ⟨p, h, rfl⟩

theorem preimage_pt_tM_inter (a b : L.ι) :
    (pt : F → Tag F L.ι) ⁻¹' (tM L a ∩ tM L b) = L.K a b := by
  ext z
  exact and_congr mem_tM_pt mem_tM_pt

variable (L)

/-- The essential points of `K` in the tagged geometry: the tags of `K`, and the points `z ∈ F` of
`K` essential (in `B`'s sense) for the reference sheet of one of the tags of `K`; all of `K` if
`K` is a sheet. -/
def tEss (K : Set (Tag F L.ι)) : Set (Tag F L.ι) :=
  {p | p ∈ K ∧ (K ∈ range (tM L) ∨ ∀ z : F, p = pt z →
    ∃ i i' : L.ι, (tag (i, i') : Tag F L.ι) ∈ K ∧ z ∈ (L.S i).ess (pt ⁻¹' K))}

/-- The null sets in the tagged geometry: `B`'s null sets in the sheet `i` marked by the tag
`(i, i)`, containing no tag of the sheet. -/
def tNull (N A : Set (Tag F L.ι)) : Prop :=
  (∀ i : L.ι, (tag (i, i) : Tag F L.ι) ∈ N → (L.S i).IsNull (pt ⁻¹' A)) ∧
    ∀ p : L.ι × L.ι, (tag p : Tag F L.ι) ∈ A → (tag p : Tag F L.ι) ∉ N

theorem tag_mem_tEss {K : Set (Tag F L.ι)} {p : L.ι × L.ι} (h : (tag p : Tag F L.ι) ∈ K) :
    (tag p : Tag F L.ι) ∈ tEss L K :=
  ⟨h, Or.inr fun _ he => absurd he tag_ne_pt⟩

/-- **The tagged `SheetGeometry`** of `B`'s structure `L`, on the discrete M-polyfold. -/
def tG : (discretePolyfold (Tag F L.ι)).SheetGeometry (range (tM L)) where
  ess _ K := tEss L K
  ess_subset _ _ _ h := h.1
  ess_self N hN := Subset.antisymm (fun _ h => h.1) fun _ hp => ⟨hp, Or.inl hN⟩
  ess_comm N _ N' _ := by rw [inter_comm]
  submanifoldTangent_eq N _ N' _ z hz := by
    have hz' := hz.1
    have h : N ∩ {z} = N' ∩ {z} := by
      rw [inter_eq_right.2 (singleton_subset_iff.2 hz'.1),
        inter_eq_right.2 (singleton_subset_iff.2 hz'.2)]
    exact Subset.antisymm
      (MPolyfold.submanifoldTangent_subset_of_inter_eq (V := {z}) (isOpen_discrete _)
        (mem_singleton z) h)
      (MPolyfold.submanifoldTangent_subset_of_inter_eq (V := {z}) (isOpen_discrete _)
        (mem_singleton z) h.symm)
  IsNull := tNull L
  isNull_empty _ := ⟨fun i _ => by
      change IsMeasureZero _ _
      rw [preimage_empty, preimage_empty]
      exact isMeasureZero_empty, fun _ hp => hp.elim⟩
  isNull_mono h hA :=
    ⟨fun i hi => IsMeasureZero.mono (h.1 i hi) (preimage_mono (preimage_mono hA)),
      fun p hp => h.2 p (hA hp)⟩
  isNull_union h h' := ⟨fun i hi => by
      change IsMeasureZero _ _
      rw [preimage_union, preimage_union]
      exact (h.1 i hi).union (h'.1 i hi), fun p hp => hp.elim (h.2 p) (h'.2 p)⟩
  not_isNull_self N hN _ h := by
    obtain ⟨i, rfl⟩ := hN
    have hmem : (tag (i, i) : Tag F L.ι) ∈ tM L i := mem_tM_tag.2 (Or.inl rfl)
    exact h.2 (i, i) hmem hmem
  isNull_diff_ess N hN N' hN' := by
    obtain ⟨a, rfl⟩ := hN
    obtain ⟨b, rfl⟩ := hN'
    refine ⟨fun i hi => ?_, fun p hp => (hp.2 (tag_mem_tEss L hp.1)).elim⟩
    have hia : i = a := by
      rcases mem_tM_tag.1 hi with h | h <;> exact h
    subst hia
    refine IsMeasureZero.mono (lemma_9_4_6 (I := Q n) ((L.S i).j ⁻¹' L.K i b)) ?_
    rintro w ⟨hwK, hwe⟩
    have hK : (L.S i).j w ∈ L.K i b := by
      rw [← preimage_pt_tM_inter]
      exact hwK
    refine ⟨hK, fun hess => hwe ⟨hwK, Or.inr fun z hz => ?_⟩⟩
    refine ⟨i, b, ⟨mem_tM_tag.2 (Or.inl rfl), mem_tM_tag.2 (Or.inr rfl)⟩, ?_⟩
    rw [← pt_injective hz, preimage_pt_tM_inter]
    exact ⟨w, hess, rfl⟩

/-- A link of the tagged geometry at a point of `F` is a link of `B` or the reverse of one. -/
theorem eqvGen_of_isLink {z : F} {a b : {i // (pt z : Tag F L.ι) ∈ tM L i}}
    (h : (tG L).IsLink (tM L) (pt z) a b) :
    Relation.EqvGen (L.YEquivB z) ⟨a.1, mem_tM_pt.1 a.2⟩ ⟨b.1, mem_tM_pt.1 b.2⟩ := by
  by_cases hab : a.1 = b.1
  · have : (⟨a.1, mem_tM_pt.1 a.2⟩ : {i // z ∈ (L.S i).M}) = ⟨b.1, mem_tM_pt.1 b.2⟩ :=
      Subtype.ext hab
    rw [this]
    exact Relation.EqvGen.refl _
  obtain ⟨-, hK | hK⟩ := h
  · exfalso
    obtain ⟨c, hc⟩ := hK
    have hcc : (tag (c, c) : Tag F L.ι) ∈ tM L c := mem_tM_tag.2 (Or.inl rfl)
    change tM L c = tM L a.1 ∩ tM L b.1 at hc
    rw [hc] at hcc
    have h1 := mem_tM_tag.1 hcc.1
    have h2 := mem_tM_tag.1 hcc.2
    simp only [or_self] at h1 h2
    exact hab (h1.symm.trans h2)
  · obtain ⟨i, i', ⟨hia, hib⟩, hess⟩ := hK z rfl
    rw [preimage_pt_tM_inter] at hess
    have hia := mem_tM_tag.1 hia
    have hib := mem_tM_tag.1 hib
    simp only at hia hib
    rcases hia with hi | hi'
    · subst hi
      exact Relation.EqvGen.rel _ _ (Relation.ReflTransGen.single hess)
    · rcases hib with hi | hi''
      · subst hi
        refine Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Relation.ReflTransGen.single ?_))
        change z ∈ (L.S b.1).ess (L.K b.1 a.1)
        rw [LocalStrB.K, inter_comm]
        exact hess
      · exact (hab (hi'.symm.trans hi'')).elim

/-- The tagged geometry has at least as many classes at `z` as `B`. -/
theorem two_le {z : F} (h : 2 ≤ L.numClasses z) : 2 ≤ (tG L).numClasses (tM L) (pt z) := by
  let f : Quotient ((tG L).ySetoid (tM L) (pt z)) → Quot (L.YEquivB z) :=
    Quotient.lift (fun a => Quot.mk _ ⟨a.1, mem_tM_pt.1 a.2⟩) fun a b hab => by
      refine Quot.eqvGen_sound ?_
      change Relation.EqvGen _ a b at hab
      induction hab with
      | rel a b h => exact eqvGen_of_isLink L h
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  have hf : Function.Surjective f := by
    rintro ⟨i, hi⟩
    exact ⟨Quotient.mk _ ⟨i, mem_tM_pt.2 hi⟩, rfl⟩
  exact h.trans (Nat.card_le_card_of_surjective f hf)

end

theorem A_to_B : A → B := by
  intro hA n F _ _ _ x L i
  have h := (hA.1 (tG L) (tM L) (fun i => mem_range_self i) i).1 i (mem_tM_tag.2 (Or.inl rfl))
  refine IsMeasureZero.mono h ?_
  rintro w ⟨hMU, h2⟩
  obtain ⟨k, hk⟩ := mem_iUnion.1 hMU
  exact ⟨⟨mem_iUnion.2 ⟨k, mem_tM_pt.2 hk⟩, two_le L h2⟩, mem_tM_pt.2 ⟨w, rfl⟩⟩

#rt_check RoundTrip.V9_46.A_to_B [Polyfold.MPolyfold.SheetGeometry.lemma_9_4_8,
  Polyfold.MPolyfold.SheetGeometry.isNullIn_diff_MStar]
#rt_overlap RoundTrip.V9_46.A_to_B [Polyfold.MPolyfold.SheetGeometry.lemma_9_4_8,
  Polyfold.MPolyfold.SheetGeometry.isNullIn_diff_MStar]

end RoundTrip.V9_46
