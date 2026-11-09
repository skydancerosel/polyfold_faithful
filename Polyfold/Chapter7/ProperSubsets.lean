import Polyfold.Chapter7.EpGroupoid
import Polyfold.Chapter7.ProperMaps
import Polyfold.Chapter7.LocalDiffeo
import Polyfold.Chapter7.LocConnected

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II, §7.4,
pp. 251–252: **Definition 7.5.8 (2017: 7.17)** (proper subsets, the properness property), **Proposition 7.5.9 (2017: 7.13)**
(a proper subset is closed) and **Proposition 7.5.10 (2017: 7.14)** (`π(Q)` is closed for proper `Q`; if `|X|`
is paracompact, the closed subsets of `|X|` are the images `π(Q)` of proper `Q`).  There is no
2014 preprint of Part II; numbers and pages are the 2017 text's.  Definition 7.5.8 (2017: 7.17) itself is in
`EpGroupoid.lean` (`IsProperSubset`, `HasPropernessProperty`).

# Proper subsets of an ep-groupoid

## The text, paraphrased

(Definition 7.5.8 (2017: 7.17)) `Q ⊂ X` is proper if `t : s⁻¹(Q) → X` is proper; an open `U ⊂ X` has the
properness property if `cl_X(U)` is proper.  (Proposition 7.5.9 (2017: 7.13)) A proper `Q` is closed: for
`x_n → x` in `Q`, the units `1_{x_n}` lie in the compact set `(t|s⁻¹(Q))⁻¹({x_n} ∪ {x})`, a
subsequence converges to some `φ` with `s(φ) ∈ Q`, and `s(φ) = x`.  (Proposition 7.5.10 (2017: 7.14)) (1) If `Q`
is proper, `π(Q)` is closed in `|X|`: for `z ∈ cl(π(Q))` there are `φ_k : x_k → y_k` with
`x_k ∈ Q`, `y_k → y`, `π(y) = z`, a subsequence of `(φ_k)` converges to some `φ` over `Q`, and
`z = π(s(φ))`.  (2) If `|X|` is paracompact, a set `A ⊂ |X|` is closed if and only if `A = π(Q)`
for a proper `Q`.  *Proof of (2)*: choose for `z ∈ A` a representative `x_z` and a neighbourhood
`U(x_z)` with the natural action whose closure `Q_z` is proper; by Lemma 2.7.3 (2017: 2.7) the closed (hence
paracompact) `A` has a locally finite cover by closed `A_i ⊂ π(Q_{z_i})`; with
`P_i = (π|cl_X(U(x_{z_i})))⁻¹(A_i)` the set `Q = ⋃ P_i` has `π(Q) = A`, and it is proper: for
`s(φ_k) ∈ Q` and `t(φ_k) → y` only finitely many `A_i` meet a neighbourhood of `π(y)`, so for
large `k` the `s(φ_k)` lie in finitely many `P_i`, each of them proper.

## What is formalized

* `isProperSubset_iff_isCompact` (`Q` is proper iff `s⁻¹(Q) ∩ t⁻¹(K)` is compact for every
  compact `K`, the form of Proposition 7.5.9 (2017: 7.13)'s proof) and `isProperSubset_iff_exists_tendsto_subseq`
  (for closed `Q`, the sequential form of the other proofs).
* **Proposition 7.5.9 (2017: 7.13)**: `proposition_7_5_9` (`IsProperSubset.isClosed`).
* **Proposition 7.5.10 (2017: 7.14) (1)**: `proposition_7_5_10_one`; at the level of objects,
  `isClosed_saturation_of_isProperSubset` (the saturation `π⁻¹(π(Q))` is closed).
* Basic lemmas: `IsProperSubset.of_subset` (**a closed subset of a proper set is proper**),
  `isProperSubset_empty`, `IsProperSubset.union`, `isProperSubset_biUnion`,
  `isProperSubset_iUnion` (**finite unions of proper sets are proper**),
  `isProperSubset_iUnion_of_locallyFinite` (a union of proper sets whose images in `|X|` form a
  locally finite family is proper: the step "`Q` is proper" of Proposition 7.5.10 (2017: 7.14) (2)),
  `isProperSubset_of_isCompact` (compact sets are proper), `HasPropernessProperty.isProperSubset`,
  `HasPropernessProperty.mono` (**if `V(x)` has the properness property, so does every open
  `V' ⊂ V(x)`**; PLAN II.5, 4), `exists_hasPropernessProperty_subset` and
  `exists_hasPropernessProperty_isConnected_subset` (inside every neighbourhood of `x` there is
  an open, resp. open and connected, neighbourhood of `x` with the properness property).
* **Proposition 7.5.10 (2017: 7.14) (2)**: `proposition_7_5_10_two` (`[ParacompactSpace X.OrbitSpace]`: `A` is
  closed iff `A = π(Q)` for a proper `Q`).

## Reading

* Properness is Mathlib's `IsProperMap` of `(s ⁻¹' Q).domRestrict t` (PLAN P3).  Both `X` and
  `𝐗` are metrizable (Theorem 2.3.10 (2017: 2.2) [2.16]), so this is "preimages of compact sets are compact"
  (`ProperMaps.lean`), which for the subtype `s⁻¹(Q)` is the compactness of `s⁻¹(Q) ∩ t⁻¹(K)`.
* Proposition 7.5.10 (2017: 7.14) (1) is proved through the closed-map property of proper maps rather than the
  text's sequences: `π⁻¹(π(Q)) = t(s⁻¹(Q))` is the image of the closed `s⁻¹(Q)` (Proposition
  7.13) under the proper `t : s⁻¹(Q) → X`, and `|X|` carries the quotient topology.
* **Proposition 7.5.10 (2017: 7.14) (2) needs no regularity of `|X|`.**  The text's proof takes a locally finite
  *closed* refinement from Lemma 2.7.3 (2017: 2.7) [2.56], which assumes a regular Hausdorff space (true for
  `|X|` by Theorem 7.3.1 (2017: 7.2), p. 324 (2017 p. 244), which a later wave of this project formalizes).  We take instead
  an *open* locally finite precise refinement `(v_z)` of the cover `(π(V(x_z)))_z` of the closed
  `A` (Mathlib's `precise_refinement_set`, paracompactness alone) and use the closures:
  `P_z = cl_X(V(x_z)) ∩ π⁻¹(cl(v_z) ∩ A)` is a closed subset of the proper `cl_X(V(x_z))`,
  `π(P_z) ⊂ cl(v_z)`, and the closures of a locally finite family are locally finite.  So (2) is
  proved as stated, with `[ParacompactSpace X.OrbitSpace]` only (Definition 7.5.1 (2017: 7.15): paracompact
  without Hausdorff), and no version "`_of_regularSpace`" is needed.  PLAN II.6, 7's shrinking in
  the normal `|X|` is not needed either.
* In (2) the text's "neighborhood `U(x_z)` for which we have the natural `G_{x_z}`-action" is used
  only through the properness of `cl_X(U(x_z))`; any neighbourhood with the properness property
  (Definition 7.1.3 (2017: 7.3) (3)) is taken.  The text's sequence argument for the properness of `Q` is
  replaced by compact sets: a compact `K` has compact `π(K)`, which meets only finitely many
  `cl(v_z)`.
* The representatives `x_z` are `Quotient.out`.  The text's "`Q_z` is proper and therefore
  `π(Q_z)` is closed" and "`A` is paracompact" are not needed by this route.
* Possible misprints (notation only): the proof of (2) writes `cl_X(U_{x_{z_i}})` for
  `cl_X(U(x_{z_i}))`; the proof of (1) concludes "`x = s(φ) ∈ Q`" with `x` a new name for the
  point `s(φ)` (the `x_k` are the earlier points of `Q`).
* "For all" hypotheses: none is added.  `[ParacompactSpace X.OrbitSpace]` is the text's
  hypothesis and is satisfiable (`EpGroupoid.hasParacompactOrbitSpace_trivial`).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### The orbit map: saturations, openness, closed images -/

/-- The saturation `π⁻¹(π(Q))` is `t(s⁻¹(Q))`. -/
private theorem preimage_π_image_eq (Q : Set Obj) :
    X.π ⁻¹' (X.π '' Q) = X.tgt '' (X.src ⁻¹' Q) := by
  ext y
  constructor
  · rintro ⟨q, hq, hqy⟩
    obtain ⟨φ, rfl, rfl⟩ := (X.π_eq_π_iff).1 hqy
    exact ⟨φ, hq, rfl⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨X.src φ, hφ, X.π_src_eq_π_tgt φ⟩

/-- A set of `|X|` is closed iff its preimage under `π` is (the quotient topology). -/
private theorem isClosed_iff_preimage_π {A : Set X.OrbitSpace} :
    IsClosed A ↔ IsClosed (X.π ⁻¹' A) :=
  isClosed_coinduced

/-- `π` is open (the argument of Proposition 7.1.8 (2017: 7.1): `π⁻¹(π(U)) = t(s⁻¹(U))` and `t` is open). -/
private theorem isOpen_image_π {U : Set Obj} (hU : IsOpen U) : IsOpen (X.π '' U) := by
  change IsOpen (X.π ⁻¹' (X.π '' U))
  rw [preimage_π_image_eq]
  exact X.isLocalScDiffeo_tgt.isOpenMap _ (hU.preimage X.continuous_src)

/-! ### Proper subsets, by compact sets and by sequences -/

/-- **Proper subsets by compact sets**: `Q` is proper iff `s⁻¹(Q) ∩ t⁻¹(K)` is compact for every
compact `K ⊆ X` (the form of the proof of Proposition 7.5.9 (2017: 7.13)). -/
theorem isProperSubset_iff_isCompact {Q : Set Obj} :
    X.IsProperSubset Q ↔ ∀ K, IsCompact K → IsCompact (X.src ⁻¹' Q ∩ X.tgt ⁻¹' K) := by
  unfold IsProperSubset
  rw [MPolyfold.isProperMap_domRestrict_iff_isCompact_preimage X.PObj]
  have he : ∀ K : Set Obj, IsCompact ((X.src ⁻¹' Q).domRestrict X.tgt ⁻¹' K) ↔
      IsCompact (X.src ⁻¹' Q ∩ X.tgt ⁻¹' K) := fun K => by
    rw [IsEmbedding.subtypeVal.isCompact_iff, ← Subtype.image_preimage_coe]
    rfl
  simp only [he]
  exact ⟨fun h => h.2, fun h => ⟨X.continuous_tgt.comp continuous_subtype_val, h⟩⟩

/-- **Proper subsets by sequences**, in the words of the text: a closed `Q` is proper iff every
sequence `(φ_k)` with `s(φ_k) ∈ Q` and `t(φ_k)` convergent has a convergent subsequence. -/
theorem isProperSubset_iff_exists_tendsto_subseq {Q : Set Obj} (hQ : IsClosed Q) :
    X.IsProperSubset Q ↔ ∀ ⦃φ : ℕ → Mor⦄ ⦃y : Obj⦄, (∀ n, X.src (φ n) ∈ Q) →
      Tendsto (X.tgt ∘ φ) atTop (𝓝 y) →
        ∃ φ₀, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (φ ∘ ψ) atTop (𝓝 φ₀) :=
  MPolyfold.isProperMap_domRestrict_iff_of_isClosed X.PMor X.PObj X.continuous_src
    X.continuous_tgt hQ

/-! ### Proposition 7.5.9 (2017: 7.13) -/

/-- **Proposition 7.5.9 (2017: 7.13)**: a proper subset `Q ⊆ X` is closed. -/
theorem proposition_7_5_9 {Q : Set Obj} (hQ : X.IsProperSubset Q) : IsClosed Q := by
  have := X.PMor.metrizableSpace
  have := X.PObj.metrizableSpace
  exact isClosed_of_isProperMap_domRestrict X.continuous_src hQ X.src_unit X.tgt_unit

variable {X} in
/-- A proper subset is closed (Proposition 7.5.9 (2017: 7.13)). -/
theorem IsProperSubset.isClosed {Q : Set Obj} (hQ : X.IsProperSubset Q) : IsClosed Q :=
  X.proposition_7_5_9 hQ

/-! ### Proposition 7.5.10 (2017: 7.14) (1) -/

/-- The saturation `π⁻¹(π(Q)) = t(s⁻¹(Q))` of a proper `Q` is closed. -/
theorem isClosed_saturation_of_isProperSubset {Q : Set Obj} (hQ : X.IsProperSubset Q) :
    IsClosed (X.saturation Q) := by
  change IsClosed (X.π ⁻¹' (X.π '' Q))
  rw [preimage_π_image_eq]
  exact isClosed_image_preimage_of_isProperMap_domRestrict hQ subset_rfl
    (hQ.isClosed.preimage X.continuous_src)

/-- **Proposition 7.5.10 (2017: 7.14) (1)**: if `Q ⊆ X` is proper, then `π(Q)` is closed in `|X|`. -/
theorem proposition_7_5_10_one {Q : Set Obj} (hQ : X.IsProperSubset Q) : IsClosed (X.π '' Q) :=
  (isClosed_iff_preimage_π X).2 (X.isClosed_saturation_of_isProperSubset hQ)

/-! ### Closed subsets and unions of proper sets -/

variable {X}

/-- **A closed subset of a proper set is proper.** -/
theorem IsProperSubset.of_subset {Q Q' : Set Obj} (hQ : X.IsProperSubset Q) (hQ'Q : Q' ⊆ Q)
    (hQ' : IsClosed Q') : X.IsProperSubset Q' :=
  isProperMap_domRestrict_of_subset_of_isClosed X.continuous_src hQ hQ'Q hQ'

variable (X) in
/-- The empty set is proper. -/
theorem isProperSubset_empty : X.IsProperSubset ∅ :=
  (X.isProperSubset_iff_isCompact).2 fun K _ => by
    rw [preimage_empty, empty_inter]
    exact isCompact_empty

/-- **The union of two proper sets is proper.** -/
theorem IsProperSubset.union {Q Q' : Set Obj} (hQ : X.IsProperSubset Q)
    (hQ' : X.IsProperSubset Q') : X.IsProperSubset (Q ∪ Q') := by
  rw [isProperSubset_iff_isCompact] at hQ hQ' ⊢
  intro K hK
  rw [preimage_union, union_inter_distrib_right]
  exact (hQ K hK).union (hQ' K hK)

/-- **A finite union of proper sets is proper** (indexed by a finite set). -/
theorem isProperSubset_biUnion {ι : Type*} {S : Set ι} (hS : S.Finite) {Q : ι → Set Obj}
    (hQ : ∀ i ∈ S, X.IsProperSubset (Q i)) : X.IsProperSubset (⋃ i ∈ S, Q i) := by
  rw [isProperSubset_iff_isCompact]
  intro K hK
  rw [preimage_iUnion₂, iUnion₂_inter]
  exact hS.isCompact_biUnion fun i hi => (X.isProperSubset_iff_isCompact).1 (hQ i hi) K hK

/-- **A finite union of proper sets is proper** (indexed by a finite type). -/
theorem isProperSubset_iUnion {ι : Type*} [Finite ι] {Q : ι → Set Obj}
    (hQ : ∀ i, X.IsProperSubset (Q i)) : X.IsProperSubset (⋃ i, Q i) := by
  rw [isProperSubset_iff_isCompact]
  intro K hK
  rw [preimage_iUnion, iUnion_inter]
  exact isCompact_iUnion fun i => (X.isProperSubset_iff_isCompact).1 (hQ i) K hK

/-- **A locally finite union of proper sets is proper**: if every `Q_i` is proper and the images
`π(Q_i)` form a locally finite family in `|X|`, then `⋃ Q_i` is proper.  (A compact `K` has
compact `π(K)`, which meets only finitely many `π(Q_i)`; this is the step "`Q` is proper" of the
proof of Proposition 7.5.10 (2017: 7.14) (2).) -/
theorem isProperSubset_iUnion_of_locallyFinite {ι : Type*} {Q : ι → Set Obj}
    (hQ : ∀ i, X.IsProperSubset (Q i)) (hlf : LocallyFinite fun i => X.π '' Q i) :
    X.IsProperSubset (⋃ i, Q i) := by
  rw [isProperSubset_iff_isCompact]
  intro K hK
  have hfin := hlf.finite_nonempty_inter_compact (hK.image X.continuous_π)
  have heq : X.src ⁻¹' (⋃ i, Q i) ∩ X.tgt ⁻¹' K =
      ⋃ i ∈ {i | (X.π '' Q i ∩ X.π '' K).Nonempty}, X.src ⁻¹' Q i ∩ X.tgt ⁻¹' K := by
    ext φ
    simp only [mem_inter_iff, mem_preimage, mem_iUnion, mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨⟨i, hi⟩, hK'⟩
      exact ⟨i, ⟨X.π (X.src φ), mem_image_of_mem _ hi,
        X.π_src_eq_π_tgt φ ▸ mem_image_of_mem _ hK'⟩, hi, hK'⟩
    · rintro ⟨i, -, hi, hK'⟩
      exact ⟨⟨i, hi⟩, hK'⟩
  rw [heq]
  exact hfin.isCompact_biUnion fun i _ => (X.isProperSubset_iff_isCompact).1 (hQ i) K hK

variable (X) in
/-- **Compact sets are proper**: a compact `K` is covered by finitely many neighbourhoods `V(x)`
with the properness property (Definition 7.1.3 (2017: 7.3) (3)), and `K = ⋃ (K ∩ cl V(x))`. -/
theorem isProperSubset_of_isCompact {K : Set Obj} (hK : IsCompact K) : X.IsProperSubset K := by
  choose V hxV hV using X.exists_hasPropernessProperty
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V (fun x => (hV x).1)
    fun x _ => mem_iUnion.2 ⟨x, hxV x⟩
  have heq : K = ⋃ x ∈ t, K ∩ closure (V x) := by
    refine Subset.antisymm (fun y hy => ?_) (iUnion₂_subset fun _ _ => inter_subset_left)
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (ht hy)
    exact mem_iUnion₂.2 ⟨x, hx, hy, subset_closure hyx⟩
  rw [heq]
  exact isProperSubset_biUnion t.finite_toSet fun x _ =>
    (hV x).2.of_subset inter_subset_right (hK.isClosed.inter isClosed_closure)

/-! ### The properness property -/

/-- An open set with the properness property has a proper closure (Definition 7.5.8 (2017: 7.17)). -/
theorem HasPropernessProperty.isProperSubset {U : Set Obj} (hU : X.HasPropernessProperty U) :
    X.IsProperSubset (closure U) :=
  hU.2

/-- **If `V(x)` has the properness property, so does every open `V' ⊆ V(x)`** (PLAN II.5, 4): the
closure of `V'` is a closed subset of the proper `cl_X(V(x))`. -/
theorem HasPropernessProperty.mono {V V' : Set Obj} (hV : X.HasPropernessProperty V)
    (hV' : IsOpen V') (hV'V : V' ⊆ V) : X.HasPropernessProperty V' :=
  ⟨hV', hV.2.of_subset (closure_mono hV'V) isClosed_closure⟩

variable (X) in
/-- Every neighbourhood `W` of `x` contains an open neighbourhood of `x` with the properness
property. -/
theorem exists_hasPropernessProperty_subset {x : Obj} {W : Set Obj} (hW : W ∈ 𝓝 x) :
    ∃ V, x ∈ V ∧ V ⊆ W ∧ X.HasPropernessProperty V := by
  obtain ⟨V, hxV, hV⟩ := X.exists_hasPropernessProperty x
  obtain ⟨W', hW'W, hW'o, hxW'⟩ := mem_nhds_iff.1 hW
  exact ⟨V ∩ W', ⟨hxV, hxW'⟩, inter_subset_right.trans hW'W,
    hV.mono (hV.1.inter hW'o) inter_subset_left⟩

variable (X) in
/-- Every neighbourhood `W` of `x` contains an open **connected** neighbourhood of `x` with the
properness property (M-polyfolds are locally connected, `LocConnected.lean`). -/
theorem exists_hasPropernessProperty_isConnected_subset {x : Obj} {W : Set Obj} (hW : W ∈ 𝓝 x) :
    ∃ V, x ∈ V ∧ V ⊆ W ∧ IsConnected V ∧ X.HasPropernessProperty V := by
  obtain ⟨V, hxV, hVW, hV⟩ := X.exists_hasPropernessProperty_subset hW
  obtain ⟨V', hV'o, hxV', hV'V, hV'c⟩ :=
    X.PObj.exists_isOpen_isConnected_subset (hV.1.mem_nhds hxV)
  exact ⟨V', hxV', hV'V.trans hVW, hV'c, hV.mono hV'o hV'V⟩

/-! ### Proposition 7.5.10 (2017: 7.14) (2) -/

variable (X)

/-- **Proposition 7.5.10 (2017: 7.14) (2)**: if `|X|` is paracompact, a subset `A ⊆ |X|` is closed if and only if
`A = π(Q)` for a proper subset `Q ⊆ X`.  (No regularity of `|X|` is needed; see the module
docstring.) -/
theorem proposition_7_5_10_two [ParacompactSpace X.OrbitSpace] (A : Set X.OrbitSpace) :
    IsClosed A ↔ ∃ Q : Set Obj, X.IsProperSubset Q ∧ X.π '' Q = A := by
  refine ⟨fun hA => ?_, ?_⟩
  swap
  · rintro ⟨Q, hQ, rfl⟩
    exact X.proposition_7_5_10_one hQ
  -- For every `z ∈ |X|` a representative `x_z` and an open `V(x_z) ∋ x_z` with the properness
  -- property; the sets `π(V(x_z))` cover `|X|`.
  choose V hxV hV using fun z : X.OrbitSpace => X.exists_hasPropernessProperty z.out
  have hzV : ∀ z, z ∈ X.π '' V z := fun z => ⟨z.out, hxV z, Quotient.out_eq z⟩
  obtain ⟨v, -, hAv, hvlf, hvV⟩ := precise_refinement_set hA (fun z => X.π '' V z)
    (fun z => isOpen_image_π X (hV z).1) fun z _ => mem_iUnion.2 ⟨z, hzV z⟩
  -- `P_z = cl(V(x_z)) ∩ π⁻¹(cl(v_z) ∩ A)` and `Q = ⋃ P_z`.
  set P : X.OrbitSpace → Set Obj := fun z => closure (V z) ∩ X.π ⁻¹' (closure (v z) ∩ A) with hP
  have hPproper : ∀ z, X.IsProperSubset (P z) := fun z =>
    (hV z).2.of_subset inter_subset_left
      (isClosed_closure.inter ((isClosed_closure.inter hA).preimage X.continuous_π))
  have hPlf : LocallyFinite fun z => X.π '' P z :=
    hvlf.closure.subset fun z => (image_mono inter_subset_right).trans
      ((image_preimage_subset _ _).trans inter_subset_left)
  refine ⟨⋃ z, P z, isProperSubset_iUnion_of_locallyFinite hPproper hPlf, ?_⟩
  refine Subset.antisymm ?_ fun a ha => ?_
  · rw [image_iUnion]
    exact iUnion_subset fun z => (image_mono inter_subset_right).trans
      ((image_preimage_subset _ _).trans inter_subset_right)
  · obtain ⟨z, hz⟩ := mem_iUnion.1 (hAv ha)
    obtain ⟨y, hy, rfl⟩ := hvV z hz
    exact ⟨y, mem_iUnion.2 ⟨z, subset_closure hy, subset_closure hz, ha⟩, rfl⟩

end EpGroupoid

end Polyfold
