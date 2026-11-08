import Polyfold.Chapter9.Propositions
import Polyfold.Chapter9.GoodPoints

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.6 "Appendix", §9.6.1 "Proof of Proposition 9.1.12" (pp. 452–457; the whole
subsection is new in the 2021 edition): **Lemma 9.6.1** (p. 453), the local top dimension `dim_Θ`
(p. 454), **Lemma 9.6.2** (p. 454), **Definition 9.6.3** (p. 455), **Lemma 9.6.4** (p. 455), the
agreement of `Θ_k` at top-good points (p. 456) and, from them, **Proposition 9.1.12** (p. 408),
whose statement is `EpGroupoid.Proposition_9_1_12` in `Polyfold/Chapter9/Propositions.lean`.
**Proposition 9.6.5** (p. 456) is not formalized: its role is taken by the explicit hypothesis
`MPolyfold.TopMultiplicity`, which has witnesses in this file.

# The dimensional decomposition does not depend on the local branching structure

## The text, paraphrased

Near `x` a branched ep⁺-subgroupoid is `Θ(y) = ∑_{i : y ∈ Mᵢ} σᵢ` on `U(x)`; splitting the index set
`I = I_0 ⊔ ⋯ ⊔ I_k` by the dimension of `Mᵢ` gives `Θ = Θ_0 + ⋯ + Θ_k` on `U(x)`, and
Proposition 9.1.12 says that near `x` this splitting does not depend on the structure.

(Lemma 9.6.1, p. 453) Two structures on `U(x)` have the same top dimension.  Proof: if the first
has top dimension `k` and the second `ℓ < k`, remove from the union `M_U^k` of the `k`-dimensional
`Mᵢ` the other sets of both structures; the removed part has `k`-dimensional measure zero, and at a
remaining point the first structure gives `Θ > 0`, the second `Θ = 0`.

(p. 454) Hence `dim_Θ(x)`, `−∞` off `supp(Θ)` and the top dimension of a local structure on
`supp(Θ)`, is well defined.  The top-dimensional part of a structure is again a branching structure,
with functor `Θ_k`; once `Θ_k` is shown not to depend on the structure, one removes the
top-dimensional manifolds from both structures and repeats the argument in lower dimensions.

(Lemma 9.6.2, p. 454) The union `M_U^k` does not depend on the structure.  Proof: a point of
`M' ∖ M''`, moved slightly off the lower-dimensional sets of both structures, has `Θ > 0` by the
first structure and `Θ = 0` by the second.

(Definition 9.6.3, p. 455) `y ∈ M_U` is *top-good* if some open `V ∋ y` has `V ∩ Mᵢ = V ∩ Mⱼ` for
all `i, j ∈ I_y^k` (the top-dimensional indices with `y ∈ Mᵢ`); the *top-bad* points are those of
`M_U^k` that are not top-good.

(Lemma 9.6.4, p. 455) Top-good and top-bad points do not depend on the structure.  Proof: near a
top-good `z`, `Θ = σ · δ_M + Θ_0 + ⋯ + Θ_{k−1}` with `M = V ∩ Mⱼ` and `σ` the sum of the top
weights through `z`; a point of `M` near `z` off the lower-dimensional sets has `Θ = σ`; as in the
discussion of good points, `z` is then top-good for the second structure.

(pp. 456–457) `Θ_k` agrees at top-good points.  At a top-bad `x`, call `i ∼ i'` in `I_k` if
`T_xMᵢ = T_xMᵢ'`; (Proposition 9.6.5) each class `Ξ` splits into nonempty disjoint `I¹, …, I^p`
with sequences of top-good points converging to `x` that lie on `Mᵢ` exactly for `i ∈ I^e`; then
`Θ_k(x) = ∑_Ξ ∑_e Θ_k(x^e)`, and the right side is said not to depend on the structure.

## What is formalized

* **In place of "measure zero"** (Lemmas 9.6.1, 9.6.2, 9.6.4): a purely topological argument; no
  Lebesgue measure and no Baire category is needed.  `MPolyfold.HasDimAt.le_of_inter_subset`: if
  `A ∩ W ⊆ N` for an open `W ∋ a`, then `dim_a A ≤ dim_a N` (inclusion of tangent spaces in a chart,
  finite-dimensionality from Remark 4.14).  `MPolyfold.exists_mem_forall_notMem` (covering lemma):
  a nonempty open piece of a `k`-dimensional submanifold is not covered by finitely many
  submanifolds of smaller dimension that are closed in an open `O`; by induction on the family,
  since removing one closed set of smaller dimension leaves a nonempty open piece.
* `LocalBranchingStructure.topDim` (top dimension), `topUnion` (`M_U^k`), `IsGeneric`,
  `exists_isGeneric` ("moving `z` slightly"), `eq_dimPart_add`, `eq_dimPart_topDim`.
* **Lemma 9.6.1**: `lemma_9_6_1`; `dim_Θ` (p. 454): `EpGroupoid.localTopDim`, `localTopDim_eq`,
  `localTopDim_eq_bot`.
* **Lemma 9.6.2**: `lemma_9_6_2`, `mem_topUnion_iff_of_mem`.
* **Definition 9.6.3**: `IsTopGoodPoint`, `IsTopBadPoint`.
* `Θ_k` agrees at points top-good for both structures (p. 456):
  `dimPart_topDim_eq_of_isTopGoodPoint`, with no further hypothesis.
* `MPolyfold.TopMultiplicity P k` (see below), with witnesses `topMultiplicity_zero` (every
  M-polyfold, `k = 0`) and `topMultiplicity_rn_of_le` (`ℝⁿ`, `k ≥ n`, through
  `rnPolyfold_mem_nhds_of_hasDimAt`: an `n`-dimensional submanifold of `ℝⁿ` is a neighbourhood of
  each of its points, by the inverse function theorem).  Under it:
  `dimPart_topDim_eq_of_topMultiplicity` (the top parts agree on `U ∩ U'`), **Lemma 9.6.4**
  `lemma_9_6_4`, `isTopBadPoint_iff`.
* **Proposition 9.1.12**: `dimPartsAgreeNear_of_topMultiplicity` and
  `EpGroupoid.proposition_9_1_12_of_topMultiplicity`, by the descending induction of p. 454
  (`subOn` removes the top-dimensional manifolds); unconditionally `proposition_9_1_12_rn_zero`,
  `proposition_9_1_12_rn_one` for the trivial ep-groupoids of `ℝ⁰`, `ℝ¹`.  `exists_mixed_rn_one`:
  on `ℝ¹` there is a branched ep⁺-subgroupoid (`1 + δ_0`) with a structure of submanifolds of
  dimensions `0` and `1`, so the `ℝ¹` case goes beyond the equidimensional case
  `dimPartsAgreeNear_of_isOfDim` of `Propositions.lean`.

## What the text leaves implicit, and the choices made

* As in `Proposition_9_1_12`, each structure comes with a labelling `dim` of its submanifolds by
  (constant) dimensions.  The two structures may have different domains `U`, `U'`; the statements
  are on `U ∩ U'` (Lemma 9.6.2 as `M_U^k ∩ U' = M'^k_U ∩ U`).  The `G_x`-invariance of `V(x)` is
  `DimPartsAgreeNear.exists_naturalRep` (`Propositions.lean`).
* Lemmas 9.6.1, 9.6.2, Definition 9.6.3 and the agreement at top-good points use only the two
  local structures: no morphisms, and neither `x ∈ supp(Θ)` nor that `Θ` be a branched
  ep⁺-subgroupoid.  As printed, points of `M_U` off `M_U^k` are (vacuously) top-good.

## The proof as we read it, and `TopMultiplicity`

* Lemma 9.6.4, last step ("as in the discussion of good points"): the argument of Lemma 9.2.3 gives,
  for the second structure, `Θ'_k(z) ≤ Θ'_k(y)` near `y`, with equality only if every top `Nⱼ`
  through `y` contains `z`.  To conclude it needs `Θ'_k(y) = σ`, i.e. that the total top weight
  at `y` is determined by the values of `Θ` at nearby points off the lower-dimensional sets.  As
  we read it, the text gives no argument for this step.
* p. 457: the classes `Ξ`, the sets `I^e` and the points `x^e` come from the first structure.
  Agreement at top-good points gives `∑_Ξ ∑_e Θ_k(x^e) = ∑_Ξ ∑_e Θ'_k(x^e)`, but that the latter
  equals `Θ'_k(x)` is the formula for the second structure with the points of the first one, which
  is not shown; so the claimed independence of the right side does not hold as we read it without
  a further argument.
* Both steps are exactly `MPolyfold.TopMultiplicity`: if two finite weighted families of
  `k`-dimensional submanifolds through `x`, closed in an open `O ∋ x`, have the same counting
  function on `O` off finitely many closed submanifolds of dimension `< k`, then their total
  weights agree.  We take it as an explicit hypothesis, proved for `k = 0` and in `ℝⁿ` for `k ≥ n`.

## Not formalized, and why

* **Proposition 9.6.5** and the formula on p. 457: they need the graph representation of
  Proposition 9.2.8 (the `T_xMᵢ` as linear subspaces of `T_xX`, sequences of top-good points);
  `TangentSlices.lean` is not imported here.  Replaced by `TopMultiplicity`.
* **`TopMultiplicity` in `ℝⁿ` for `0 < k < n`** and in general M-polyfolds.  In `ℝⁿ` we expect it
  from the density of `k`-dimensional measure of `Mᵢ ∩ B_r(x)` per class of tangent planes
  (essentially the classes of Proposition 9.6.5); not formalized, so Proposition 9.1.12 is proved
  unconditionally only for `ℝ⁰` and `ℝ¹`.
* The global part of Proposition 9.1.11 (gluing the `Θ_k`), as in `Propositions.lean`.

## Possible misprints

Those of §9.6.1 are listed in the module docstring of `Polyfold/Chapter9/Propositions.lean`
(`Ξ = I¹ ⊔ ⋯ ⊔ I^p` in Proposition 9.6.5 (1); the points `x_e^k` on p. 457; "proof of
Proposition 9.6.5" for "proof of Proposition 9.1.12"; `z` and `y` in the proof of Lemma 9.6.4).
-/

set_option maxSynthPendingDepth 3

open Set Module Submodule Filter Topology

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-! ### In place of "measure zero": the covering lemma -/

/-- **Dimension is monotone under local inclusion** (in place of the "measure zero" arguments of
§9.6.1, pp. 453–455): if `A ∩ W ⊆ N` for an open `W ∋ a`, `A` has dimension `k` and `N` dimension
`l` at `a`, then `k ≤ l`.  In a chart the tangent space of `A` at `a` lies in that of `N`, which is
finite-dimensional (Remark 4.14). -/
theorem HasDimAt.le_of_inter_subset {A N W : Set X} (hA : P.IsSmoothSubmanifold A)
    (hW : IsOpen W) {a : X} (haW : a ∈ W) (hAN : A ∩ W ⊆ N) {k l : ℕ}
    (hk : P.HasDimAt A a k) (hl : P.HasDimAt N a l) : k ≤ l := by
  obtain ⟨haN, d, φ, z, ha, hφ, haφ, hz, hfin⟩ := hl
  have hGN : IsOpen (d.toSubData.shrink φ) := d.toSubData.isOpen_shrink φ
  have haGN : a ∈ d.toSubData.shrink φ := d.toSubData.mem_shrink φ haN ha haφ
  have hA'' : P.IsSmoothSubmanifold (A ∩ (W ∩ d.toSubData.shrink φ)) :=
    hA.inter_isOpen (hW.inter hGN)
  have haA'' : a ∈ A ∩ (W ∩ d.toSubData.shrink φ) := ⟨hk.1, haW, haGN⟩
  set dA := hA''.data haA''
  have hG : IsOpen (dA.toSubData.shrink φ) := dA.toSubData.isOpen_shrink φ
  have haG : a ∈ dA.toSubData.shrink φ :=
    dA.toSubData.mem_shrink φ haA'' (hA''.mem_data_V haA'') haφ
  have hQ := dA.toSubData.isScRetract_image φ hφ
  have hset : dA.toSubData.shrink φ ∩ (A ∩ (W ∩ d.toSubData.shrink φ)) =
      (dA.toSubData.shrink φ ∩ (W ∩ d.toSubData.shrink φ)) ∩ A := by
    ext; simp only [mem_inter_iff]; tauto
  have hk' : finrank ℝ (span ℝ (tangentSpace φ.model.E φ.model.C
      (φ '' (dA.toSubData.shrink φ ∩ (A ∩ (W ∩ d.toSubData.shrink φ)))) z)) = k := by
    rw [hset] at hQ ⊢
    exact hk.finrank_eq' hφ (hG.inter (hW.inter hGN))
      (fun x hx => dA.toSubData.shrink_subset_source φ hx.1) hQ ⟨haG, haW, haGN⟩ hz
  obtain ⟨R, hR⟩ := d.toSubData.isScRetract_image φ hφ
  have hsub : φ '' (dA.toSubData.shrink φ ∩ (A ∩ (W ∩ d.toSubData.shrink φ))) ⊆ R.retract := by
    rw [hR]
    refine image_mono ?_
    rintro y ⟨-, hyA, hyW, hyGN⟩
    exact ⟨hyGN, hAN ⟨hyA, hyW⟩⟩
  have hzQ : z ∈ φ.model.E.lvlSet
      (φ '' (dA.toSubData.shrink φ ∩ (A ∩ (W ∩ d.toSubData.shrink φ)))) 1 := by
    rw [ScBanach.mem_lvlSet, hz]; exact ⟨a, ⟨haG, haA''⟩, rfl⟩
  have hT := tangentSpace_subset_of_subset R hQ hsub hzQ
  rw [hR] at hT
  obtain ⟨-, -, -, Nsub, hNsub, hNfin⟩ := d.remark_4_14 hφ haN ha haφ hz
  have hspan : span ℝ (tangentSpace φ.model.E φ.model.C
      (φ '' (d.toSubData.shrink φ ∩ N)) z) = Nsub := by
    rw [← hNsub, span_eq]
  rw [hspan] at hfin
  rw [← hk', ← hfin]
  exact Submodule.finrank_mono (span_le.2 (hT.trans hNsub.symm.subset))

/-- **Covering lemma** (in place of "measure zero" and "moving `z` slightly", Lemmas 9.6.1, 9.6.2,
9.6.4, pp. 453–455): a nonempty open piece `A ∩ W` (`W ⊆ O` open) of a `k`-dimensional submanifold
`A` is not covered by finitely many submanifolds `N_j` of dimension `< k` that are closed in `O`.
Purely topological: by induction on the family, removing one `N_j` leaves a nonempty open piece,
since `A ∩ W ⊆ N_j` would force `k ≤ dim N_j` (`HasDimAt.le_of_inter_subset`). -/
theorem exists_mem_forall_notMem {A : Set X} {k : ℕ} (hA : P.IsSubmanifoldOfDim A k)
    {ι : Type*} (s : Finset ι) (N : ι → Set X) (d : ι → ℕ)
    (hN : ∀ j ∈ s, P.IsSubmanifoldOfDim (N j) (d j)) (hd : ∀ j ∈ s, d j < k)
    {O : Set X} (hNO : ∀ j ∈ s, IsOpen (O \ N j)) {W : Set X} (hW : IsOpen W) (hWO : W ⊆ O)
    {a : X} (ha : a ∈ A) (haW : a ∈ W) : ∃ y ∈ A ∩ W, ∀ j ∈ s, y ∉ N j := by
  classical
  induction s using Finset.induction_on generalizing W a with
  | empty => exact ⟨a, ⟨ha, haW⟩, by simp⟩
  | insert j s hj ih =>
    by_cases h : A ∩ W ⊆ N j
    · exfalso
      have haN : a ∈ N j := h ⟨ha, haW⟩
      have := (hA.2 a ha).le_of_inter_subset hA.1 hW haW h
        ((hN j (Finset.mem_insert_self j s)).2 a haN)
      exact absurd (hd j (Finset.mem_insert_self j s)) (not_lt.2 this)
    · obtain ⟨a', ⟨ha'A, ha'W⟩, ha'N⟩ := not_subset.1 h
      obtain ⟨y, ⟨hyA, hyW, hyO⟩, hy⟩ := ih (fun i hi => hN i (Finset.mem_insert_of_mem hi))
        (fun i hi => hd i (Finset.mem_insert_of_mem hi))
        (fun i hi => hNO i (Finset.mem_insert_of_mem hi))
        (hW.inter (hNO j (Finset.mem_insert_self j s))) (inter_subset_left.trans hWO) ha'A
        ⟨ha'W, hWO ha'W, ha'N⟩
      refine ⟨y, ⟨hyA, hyW⟩, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hyO.2
      · exact hy i hi

/-! ### The hypothesis replacing Proposition 9.6.5 -/

open scoped Classical in
/-- **Top multiplicity in dimension `k`** (the hypothesis replacing Proposition 9.6.5, p. 456, and
the formula on p. 457; new in the 2021 edition): for every `x`, open `O ∋ x`, finite families
`(Mᵢ, σᵢ)`, `(Nⱼ, τⱼ)` of `k`-dimensional submanifolds through `x`, closed in `O`, with positive
weights, and a finite family `(L_l)` of submanifolds of dimension `< k` closed in `O`: if
`∑_{i : y ∈ Mᵢ} σᵢ = ∑_{j : y ∈ Nⱼ} τⱼ` at every `y ∈ O` off the `L_l`, then `∑ σᵢ = ∑ τⱼ`.  The
total top weight at `x` is determined by the counting function near `x` off the lower-dimensional
sets; this is what the text obtains from Proposition 9.6.5 and uses in the proof of Lemma 9.6.4.
Satisfiable: `topMultiplicity_zero`, `topMultiplicity_rn_of_le`. -/
def TopMultiplicity (P : MPolyfold X) (k : ℕ) : Prop :=
  ∀ (x : X) (O : Set X), IsOpen O → x ∈ O →
    ∀ (ι κ ν : Type u) [Fintype ι] [Fintype κ] [Fintype ν] (M : ι → Set X) (σ : ι → ℚ)
      (N : κ → Set X) (τ : κ → ℚ) (L : ν → Set X) (dL : ν → ℕ),
      (∀ i, P.IsSubmanifoldOfDim (M i) k ∧ x ∈ M i ∧ IsOpen (O \ M i) ∧ 0 < σ i) →
      (∀ j, P.IsSubmanifoldOfDim (N j) k ∧ x ∈ N j ∧ IsOpen (O \ N j) ∧ 0 < τ j) →
      (∀ l, P.IsSubmanifoldOfDim (L l) (dL l) ∧ dL l < k ∧ IsOpen (O \ L l)) →
      (∀ y ∈ O, (∀ l, y ∉ L l) → ∑ i with y ∈ M i, σ i = ∑ j with y ∈ N j, τ j) →
      ∑ i, σ i = ∑ j, τ j

open scoped Classical in
/-- **`TopMultiplicity` holds in dimension `0` in every M-polyfold**: there are no submanifolds of
negative dimension, so the counting functions agree at `x` itself, which lies on every `Mᵢ` and
every `Nⱼ`. -/
theorem topMultiplicity_zero (P : MPolyfold X) : P.TopMultiplicity 0 := by
  intro x O _ hxO ι κ ν _ _ _ M σ N τ L dL hM hN hL hagree
  have h := hagree x hxO fun l => absurd (hL l).2.1 (Nat.not_lt_zero _)
  rwa [Finset.filter_true_of_mem fun i _ => (hM i).2.1,
    Finset.filter_true_of_mem fun j _ => (hN j).2.1] at h

end MPolyfold

/-- A filtered sum over a subtype as a filtered sum over the underlying type. -/
theorem sum_subtype_filter {ι : Type*} [Fintype ι] (p q : ι → Prop) [Fintype {i // p i}]
    [DecidablePred fun i : {i // p i} => q i.1] [DecidablePred fun i => p i ∧ q i] (f : ι → ℚ) :
    ∑ i : {i // p i} with q i.1, f i.1 = ∑ i with p i ∧ q i, f i := by
  refine Finset.sum_bij (fun a _ => a.1) (fun a ha => ?_) (fun a _ b _ h => Subtype.ext h)
    (fun i hi => ?_) (fun _ _ => rfl)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨a.2, ha⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨⟨i, hi.1⟩, by simpa using hi.2, rfl⟩

/-- A sum over a finset of a subtype as a sum over the underlying type. -/
theorem sum_subtype_eq {ι : Type*} {p : ι → Prop} (s : Finset {i // p i}) (t : Finset ι)
    (h : ∀ i, i ∈ t ↔ ∃ hi : p i, (⟨i, hi⟩ : {i // p i}) ∈ s) (f : ι → ℚ) :
    ∑ i ∈ s, f i.1 = ∑ i ∈ t, f i := by
  refine Finset.sum_bij (fun a _ => a.1) (fun a ha => (h a.1).2 ⟨a.2, ha⟩)
    (fun a _ b _ h => Subtype.ext h) (fun i hi => ?_) (fun _ _ => rfl)
  obtain ⟨hp, hs⟩ := (h i).1 hi
  exact ⟨⟨i, hp⟩, hs, rfl⟩

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

namespace LocalBranchingStructure

variable {x : Obj}

/-! ### Top dimension, `M_U^k`, top-good points -/

section One

variable (B : X.LocalBranchingStructure Θ x)

open scoped Classical in
/-- **The top dimension** of a local branching structure labelled by `dim` (Lemma 9.6.1, p. 453):
`max_i dim i` (`0` for the empty structure). -/
def topDim (dim : B.ι → ℕ) : ℕ := Finset.univ.sup dim

open scoped Classical in
/-- Every label is at most the top dimension. -/
theorem dim_le_topDim (dim : B.ι → ℕ) (i : B.ι) : dim i ≤ B.topDim dim :=
  Finset.le_sup (Finset.mem_univ i)

open scoped Classical in
/-- For a nonempty structure the top dimension is attained. -/
theorem exists_dim_eq_topDim (dim : B.ι → ℕ) [Nonempty B.ι] : ∃ i, dim i = B.topDim dim := by
  obtain ⟨i, -, h⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty dim
  exact ⟨i, h.symm⟩

open scoped Classical in
/-- Each `Mᵢ` is closed in every open `O ⊆ U(x)` (properness, Definition 9.1.2 (3)). -/
theorem isOpen_diff_M {O : Set Obj} (hO : IsOpen O) (hOU : O ⊆ B.U) (i : B.ι) :
    IsOpen (O \ B.M i) := by
  have h : O \ B.M i = O ∩ (B.U \ B.M i) := by
    ext y
    simp only [Set.mem_sdiff, mem_inter_iff]
    exact ⟨fun h => ⟨h.1, hOU h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [h]
  exact hO.inter (B.isOpen_U_diff_M i)

open scoped Classical in
/-- **`M_U^k`** (pp. 453–454): the union of the `Mᵢ` labelled `k`; with `k` the top dimension it is
the set of Lemma 9.6.2. -/
def topUnion (dim : B.ι → ℕ) (k : ℕ) : Set Obj := ⋃ (i) (_ : dim i = k), B.M i

open scoped Classical in
/-- Membership in `M_U^k`. -/
theorem mem_topUnion {dim : B.ι → ℕ} {k : ℕ} {y : Obj} :
    y ∈ B.topUnion dim k ↔ ∃ i, dim i = k ∧ y ∈ B.M i := by
  simp [topUnion]

open scoped Classical in
/-- `Θ_k` vanishes off `M_U^k`. -/
theorem dimPart_eq_zero_of_notMem_topUnion {dim : B.ι → ℕ} {k : ℕ} {y : Obj}
    (hy : y ∉ B.topUnion dim k) : B.dimPart dim k y = 0 := by
  unfold dimPart
  refine Finset.sum_eq_zero fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact (hy (B.mem_topUnion.2 ⟨i, hi⟩)).elim

open scoped Classical in
/-- `Θ = Θ_k + ∑_{dim i ≠ k, y ∈ Mᵢ} σᵢ` on `U(x)`. -/
theorem eq_dimPart_add {dim : B.ι → ℕ} (k : ℕ) {y : Obj} (hy : y ∈ B.U) :
    Θ y = B.dimPart dim k y + ∑ i with dim i ≠ k ∧ y ∈ B.M i, B.σ i := by
  rw [B.eq_sum y hy]
  unfold dimPart
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun i => y ∈ B.M i)
    (fun i => dim i = k), Finset.filter_filter, Finset.filter_filter]
  congr 1
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact and_comm
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact and_comm

open scoped Classical in
/-- At a point of `U(x)` off the lower-dimensional `Mᵢ`, `Θ = Θ_k` for the top dimension `k`. -/
theorem eq_dimPart_topDim {dim : B.ι → ℕ} {y : Obj} (hy : y ∈ B.U)
    (hgen : ∀ i, dim i < B.topDim dim → y ∉ B.M i) : Θ y = B.dimPart dim (B.topDim dim) y := by
  rw [B.eq_sum y hy]
  unfold dimPart
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨le_antisymm (B.dim_le_topDim dim i) (not_lt.1 fun hlt => hgen i hlt h), h⟩,
    fun h => h.2⟩

open scoped Classical in
/-- **Definition 9.6.3, p. 455 (new in the 2021 edition) (top-good point)**: `y ∈ M_U` is top-good
if some open `V ∋ y` inside `U(x)` has `V ∩ Mᵢ = V ∩ Mⱼ` for all top-dimensional `i, j` with
`y ∈ Mᵢ, Mⱼ`. -/
def IsTopGoodPoint (dim : B.ι → ℕ) (y : Obj) : Prop :=
  y ∈ B.MU ∧ ∃ V : Set Obj, IsOpen V ∧ y ∈ V ∧ V ⊆ B.U ∧
    ∀ i j, dim i = B.topDim dim → dim j = B.topDim dim → y ∈ B.M i → y ∈ B.M j →
      V ∩ B.M i = V ∩ B.M j

open scoped Classical in
/-- **Definition 9.6.3, p. 455 (new in the 2021 edition) (top-bad point)**: a point of `M_U^k`,
`k` the top dimension, that is not top-good. -/
def IsTopBadPoint (dim : B.ι → ℕ) (y : Obj) : Prop :=
  y ∈ B.topUnion dim (B.topDim dim) ∧ ¬ B.IsTopGoodPoint dim y

end One

/-! ### Lemmas 9.6.1 and 9.6.2 -/

section Two

variable (B B' : X.LocalBranchingStructure Θ x) {dim : B.ι → ℕ} {dim' : B'.ι → ℕ}

open scoped Classical in
/-- A point is **generic** below `k` for two structures if it lies on no `Mᵢ`, `M'ⱼ` of dimension
`< k`. -/
def IsGeneric (dim : B.ι → ℕ) (dim' : B'.ι → ℕ) (k : ℕ) (y : Obj) : Prop :=
  (∀ i, dim i < k → y ∉ B.M i) ∧ ∀ j, dim' j < k → y ∉ B'.M j

variable {B B'}

open scoped Classical in
/-- **"Moving the point slightly"** (Lemmas 9.6.2, 9.6.4): every nonempty open piece of a
`k`-dimensional submanifold inside `U ∩ U'` contains a point generic below `k`. -/
theorem exists_isGeneric (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) {A : Set Obj} {k : ℕ}
    (hA : X.PObj.IsSubmanifoldOfDim A k) {W : Set Obj} (hW : IsOpen W) (hWU : W ⊆ B.U ∩ B'.U)
    {a : Obj} (ha : a ∈ A) (haW : a ∈ W) : ∃ y ∈ A ∩ W, IsGeneric B B' dim dim' k y := by
  have hO : IsOpen (B.U ∩ B'.U) := B.isOpen_U.inter B'.isOpen_U
  obtain ⟨y, hy, hgen⟩ := MPolyfold.exists_mem_forall_notMem hA
    (Finset.univ.filter fun l : B.ι ⊕ B'.ι => Sum.elim dim dim' l < k) (Sum.elim B.M B'.M)
    (Sum.elim dim dim') (fun l _ => by cases l with
      | inl i => exact hdim i
      | inr j => exact hdim' j)
    (fun l hl => (Finset.mem_filter.1 hl).2)
    (fun l _ => by cases l with
      | inl i => exact B.isOpen_diff_M hO inter_subset_left i
      | inr j => exact B'.isOpen_diff_M hO inter_subset_right j) hW hWU ha haW
  exact ⟨y, hy, fun i hi => hgen (Sum.inl i) (by simpa using hi),
    fun j hj => hgen (Sum.inr j) (by simpa using hj)⟩

open scoped Classical in
/-- Every label of the first structure is at most the top dimension of the second (the proof of
Lemma 9.6.1): a generic point of `Mᵢ` would have `Θ > 0` by the first structure and `Θ = 0` by the
second. -/
theorem dim_le_topDim_of (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) (i : B.ι) :
    dim i ≤ B'.topDim dim' := by
  by_contra h
  replace h := not_le.1 h
  obtain ⟨y, ⟨hyM, hyU, hyU'⟩, hy⟩ := MPolyfold.exists_mem_forall_notMem (hdim i)
    Finset.univ B'.M dim' (fun j _ => hdim' j)
    (fun j _ => (B'.dim_le_topDim dim' j).trans_lt h)
    (fun j _ => B'.isOpen_diff_M (B.isOpen_U.inter B'.isOpen_U) inter_subset_right j)
    (B.isOpen_U.inter B'.isOpen_U) subset_rfl (B.mem_M i) ⟨B.mem_U, B'.mem_U⟩
  have h1 : y ∈ supp Θ := (B.mem_supp_iff hyU).2 ⟨i, hyM⟩
  obtain ⟨j, hj⟩ := (B'.mem_supp_iff hyU').1 h1
  exact hy j (Finset.mem_univ j) hj

open scoped Classical in
/-- **Lemma 9.6.1, p. 453 (new in the 2021 edition) (top dimensions agree)**: two local branching
structures of `Θ` at `x` have the same top dimension. -/
theorem lemma_9_6_1 (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) :
    B.topDim dim = B'.topDim dim' :=
  le_antisymm (Finset.sup_le fun i _ => dim_le_topDim_of hdim hdim' i)
    (Finset.sup_le fun j _ => dim_le_topDim_of hdim' hdim j)

open scoped Classical in
/-- One inclusion of Lemma 9.6.2: `M_U^k ∩ U' ⊆ M'^k_U`. -/
theorem topUnion_inter_subset (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) :
    B.topUnion dim (B.topDim dim) ∩ B'.U ⊆ B'.topUnion dim' (B'.topDim dim') := by
  rintro z ⟨hz, hzU'⟩
  obtain ⟨i, hi, hzi⟩ := B.mem_topUnion.1 hz
  by_contra hz'
  have hK : B'.topDim dim' = B.topDim dim := (lemma_9_6_1 hdim hdim').symm
  set K := B.topDim dim
  have hO : IsOpen (B.U ∩ B'.U) := B.isOpen_U.inter B'.isOpen_U
  set W := (B.U ∩ B'.U) ∩ ⋂ j ∈ Finset.univ.filter (fun j => dim' j = K),
    ((B.U ∩ B'.U) \ B'.M j) with hWdef
  have hW : IsOpen W :=
    hO.inter (isOpen_biInter_finset fun j _ => B'.isOpen_diff_M hO inter_subset_right j)
  have hzW : z ∈ W := by
    refine ⟨⟨B.subset_U i hzi, hzU'⟩, mem_iInter₂.2 fun j hj => ⟨⟨B.subset_U i hzi, hzU'⟩,
      fun hzj => hz' (B'.mem_topUnion.2 ⟨j, ?_, hzj⟩)⟩⟩
    rw [hK]; exact (Finset.mem_filter.1 hj).2
  obtain ⟨y, ⟨hyM, hyW⟩, hgen⟩ := exists_isGeneric hdim hdim' (hdim i) hW inter_subset_left hzi hzW
  have h1 : y ∈ supp Θ := (B.mem_supp_iff hyW.1.1).2 ⟨i, hyM⟩
  obtain ⟨j, hj⟩ := (B'.mem_supp_iff hyW.1.2).1 h1
  rcases lt_trichotomy (dim' j) K with hlt | heq | hgt
  · exact hgen.2 j (hi ▸ hlt) hj
  · exact (mem_iInter₂.1 hyW.2 j (by simp [heq])).2 hj
  · have := B'.dim_le_topDim dim' j
    rw [hK] at this
    omega

open scoped Classical in
/-- **Lemma 9.6.2, p. 454 (new in the 2021 edition) (`M_U^k` is intrinsic)**: for two local
branching structures at `x`, with top dimension `k`, `M_U^k ∩ U' = M'^k_U ∩ U`; on a common domain
`U = U'` the two sets `M_U^k` are equal. -/
theorem lemma_9_6_2 (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) :
    B.topUnion dim (B.topDim dim) ∩ B'.U = B'.topUnion dim' (B'.topDim dim') ∩ B.U := by
  have hsub : ∀ {B B' : X.LocalBranchingStructure Θ x} {dim : B.ι → ℕ} {dim' : B'.ι → ℕ},
      (∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) →
      (∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) →
      B.topUnion dim (B.topDim dim) ∩ B'.U ⊆ B'.topUnion dim' (B'.topDim dim') ∩ B.U := by
    intro B B' dim dim' hdim hdim' z hz
    obtain ⟨i, -, hzi⟩ := B.mem_topUnion.1 hz.1
    exact ⟨topUnion_inter_subset hdim hdim' hz, B.subset_U i hzi⟩
  exact Subset.antisymm (hsub hdim hdim') (hsub hdim' hdim)

open scoped Classical in
/-- Lemma 9.6.2 pointwise on `U ∩ U'`. -/
theorem mem_topUnion_iff_of_mem (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) {y : Obj} (hyU : y ∈ B.U)
    (hyU' : y ∈ B'.U) :
    y ∈ B.topUnion dim (B.topDim dim) ↔ y ∈ B'.topUnion dim' (B'.topDim dim') := by
  have h := lemma_9_6_2 hdim hdim'
  constructor
  · intro hy
    have : y ∈ B.topUnion dim (B.topDim dim) ∩ B'.U := ⟨hy, hyU'⟩
    rw [h] at this
    exact this.1
  · intro hy
    have : y ∈ B'.topUnion dim' (B'.topDim dim') ∩ B.U := ⟨hy, hyU⟩
    rw [← h] at this
    exact this.1

open scoped Classical in
/-- At a generic point of `U ∩ U'` the two top-dimensional parts agree (both equal `Θ`). -/
theorem dimPart_topDim_eq_of_isGeneric (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) {y : Obj} (hyU : y ∈ B.U)
    (hyU' : y ∈ B'.U) (hgen : IsGeneric B B' dim dim' (B.topDim dim) y) :
    B.dimPart dim (B.topDim dim) y = B'.dimPart dim' (B'.topDim dim') y := by
  have hK : B'.topDim dim' = B.topDim dim := (lemma_9_6_1 hdim hdim').symm
  rw [← B.eq_dimPart_topDim hyU hgen.1, ← B'.eq_dimPart_topDim hyU' (hK ▸ hgen.2)]

open scoped Classical in
/-- **`Θ_k` agrees at top-good points** (p. 456, new in the 2021 edition): at a point of `U ∩ U'`
top-good for both structures the top-dimensional parts agree.  No further hypothesis is needed:
near the point `Θ_k` is constant on `M_U^k` for both structures, and agrees at a generic point. -/
theorem dimPart_topDim_eq_of_isTopGoodPoint
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) {y : Obj} (hyU : y ∈ B.U)
    (hyU' : y ∈ B'.U) (h : B.IsTopGoodPoint dim y) (h' : B'.IsTopGoodPoint dim' y) :
    B.dimPart dim (B.topDim dim) y = B'.dimPart dim' (B'.topDim dim') y := by
  have hK : B'.topDim dim' = B.topDim dim := (lemma_9_6_1 hdim hdim').symm
  have h962 := lemma_9_6_2 hdim hdim'
  by_cases hyT : y ∈ B.topUnion dim (B.topDim dim)
  · obtain ⟨i₀, hi₀, hyi₀⟩ := B.mem_topUnion.1 hyT
    obtain ⟨-, V, hV, hyV, -, hVeq⟩ := h
    obtain ⟨-, V', hV', hyV', -, hV'eq⟩ := h'
    set W := V ∩ V' ∩ (B.nbhdAt y ∩ B'.nbhdAt y)
    have hW : IsOpen W := (hV.inter hV').inter ((B.isOpen_nbhdAt y).inter (B'.isOpen_nbhdAt y))
    have hWU : W ⊆ B.U ∩ B'.U := fun z hz => ⟨hz.2.1.1, hz.2.2.1⟩
    have hyW : y ∈ W := ⟨⟨hyV, hyV'⟩, B.mem_nbhdAt_self hyU, B'.mem_nbhdAt_self hyU'⟩
    obtain ⟨z, ⟨hzi₀, hzW⟩, hgen⟩ := exists_isGeneric hdim hdim' (hdim i₀) hW hWU hyi₀ hyW
    have c1 : ∀ i, dim i = B.topDim dim → (z ∈ B.M i ↔ y ∈ B.M i) := fun i hi =>
      ⟨hzW.2.1.2 i, fun hyi => by
        have : z ∈ V ∩ B.M i₀ := ⟨hzW.1.1, hzi₀⟩
        rw [← hVeq i i₀ hi hi₀ hyi hyi₀] at this
        exact this.2⟩
    have hzT' : z ∈ B'.topUnion dim' (B'.topDim dim') := by
      have : z ∈ B.topUnion dim (B.topDim dim) ∩ B'.U :=
        ⟨B.mem_topUnion.2 ⟨i₀, hi₀, hzi₀⟩, (hWU hzW).2⟩
      rw [h962] at this
      exact this.1
    obtain ⟨j₀, hj₀, hzj₀⟩ := B'.mem_topUnion.1 hzT'
    have hyj₀ : y ∈ B'.M j₀ := hzW.2.2.2 j₀ hzj₀
    have c2 : ∀ j, dim' j = B'.topDim dim' → (z ∈ B'.M j ↔ y ∈ B'.M j) := fun j hj =>
      ⟨hzW.2.2.2 j, fun hyj => by
        have : z ∈ V' ∩ B'.M j₀ := ⟨hzW.1.2, hzj₀⟩
        rw [← hV'eq j j₀ hj hj₀ hyj hyj₀] at this
        exact this.2⟩
    have e1 : B.dimPart dim (B.topDim dim) y = B.dimPart dim (B.topDim dim) z := by
      unfold dimPart
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨h.1, (c1 i h.1).2 h.2⟩, fun h => ⟨h.1, (c1 i h.1).1 h.2⟩⟩
    have e2 : B'.dimPart dim' (B'.topDim dim') y = B'.dimPart dim' (B'.topDim dim') z := by
      unfold dimPart
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨h.1, (c2 j h.1).2 h.2⟩, fun h => ⟨h.1, (c2 j h.1).1 h.2⟩⟩
    rw [e1, e2, dimPart_topDim_eq_of_isGeneric hdim hdim' (hWU hzW).1 (hWU hzW).2 (hi₀ ▸ hgen)]
  · have hyT' : y ∉ B'.topUnion dim' (B'.topDim dim') := fun hy' => by
      have : y ∈ B'.topUnion dim' (B'.topDim dim') ∩ B.U := ⟨hy', hyU⟩
      rw [← h962] at this
      exact hyT this.1
    rw [B.dimPart_eq_zero_of_notMem_topUnion hyT, B'.dimPart_eq_zero_of_notMem_topUnion hyT']

end Two

end LocalBranchingStructure

/-! ### The local top dimension `dim_Θ` -/

open scoped Classical in
variable (X Θ) in
/-- **The local top dimension `dim_Θ`** (p. 454, new in the 2021 edition): `⊥` (the text's `−∞`)
off `supp(Θ)` or if there is no local branching structure at `x` with dimension labels, and
otherwise the top dimension of one such structure (well defined by Lemma 9.6.1,
`localTopDim_eq`). -/
def localTopDim (x : Obj) : WithBot ℕ :=
  if h : x ∈ supp Θ ∧ ∃ (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ),
      ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i) then
    (h.2.choose.topDim h.2.choose_spec.choose : WithBot ℕ)
  else ⊥

/-- **`dim_Θ` does not depend on the choices** (p. 454, from Lemma 9.6.1): on `supp(Θ)` it is the
top dimension of every local branching structure at `x` with dimension labels. -/
theorem localTopDim_eq {x : Obj} (B : X.LocalBranchingStructure Θ x) {dim : B.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) (hx : x ∈ supp Θ) :
    X.localTopDim Θ x = B.topDim dim := by
  have h : x ∈ supp Θ ∧ ∃ (C : X.LocalBranchingStructure Θ x) (dimC : C.ι → ℕ),
      ∀ i, X.PObj.IsSubmanifoldOfDim (C.M i) (dimC i) := ⟨hx, B, dim, hdim⟩
  rw [localTopDim, dif_pos h]
  exact congrArg _ (LocalBranchingStructure.lemma_9_6_1 h.2.choose_spec.choose_spec hdim)

/-- `dim_Θ = −∞` off `supp(Θ)` (p. 454). -/
theorem localTopDim_eq_bot {x : Obj} (hx : x ∉ supp Θ) : X.localTopDim Θ x = ⊥ := by
  rw [localTopDim, dif_neg fun h => hx h.1]

end EpGroupoid

/-! ### Lemma 9.6.4 and Proposition 9.1.12 under `TopMultiplicity` -/

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

namespace LocalBranchingStructure

variable {x : Obj}

section Three

variable {B B' : X.LocalBranchingStructure Θ x} {dim : B.ι → ℕ} {dim' : B'.ι → ℕ}

open scoped Classical in
/-- **The top-dimensional parts agree on `U ∩ U'`** (the aim stated on p. 454), under
`TopMultiplicity` in the top dimension: apply it at `y` to the top `Mᵢ`, `M'ⱼ` through `y`, with the
lower-dimensional sets of both structures as `L`. -/
theorem dimPart_topDim_eq_of_topMultiplicity (hT : X.PObj.TopMultiplicity (B.topDim dim))
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) {y : Obj} (hyU : y ∈ B.U)
    (hyU' : y ∈ B'.U) :
    B.dimPart dim (B.topDim dim) y = B'.dimPart dim' (B'.topDim dim') y := by
  have hK : B'.topDim dim' = B.topDim dim := (lemma_9_6_1 hdim hdim').symm
  rw [hK]
  set K := B.topDim dim
  set O := (B.U ∩ B'.U) ∩ (B.nbhdAt y ∩ B'.nbhdAt y)
  have hO : IsOpen O := (B.isOpen_U.inter B'.isOpen_U).inter
    ((B.isOpen_nbhdAt y).inter (B'.isOpen_nbhdAt y))
  have hyO : y ∈ O := ⟨⟨hyU, hyU'⟩, B.mem_nbhdAt_self hyU, B'.mem_nbhdAt_self hyU'⟩
  have key := hT y O hO hyO {i // dim i = K ∧ y ∈ B.M i} {j // dim' j = K ∧ y ∈ B'.M j}
    {l : B.ι ⊕ B'.ι // Sum.elim dim dim' l < K} (fun i => B.M i.1) (fun i => B.σ i.1)
    (fun j => B'.M j.1) (fun j => B'.σ j.1) (fun l => Sum.elim B.M B'.M l.1)
    (fun l => Sum.elim dim dim' l.1)
    (fun i => ⟨(congrArg _ i.2.1).mp (hdim i.1), i.2.2, B.isOpen_diff_M hO (fun z hz => hz.1.1) i.1,
      B.σ_pos i.1⟩)
    (fun j => ⟨(congrArg _ j.2.1).mp (hdim' j.1), j.2.2,
      B'.isOpen_diff_M hO (fun z hz => hz.1.2) j.1, B'.σ_pos j.1⟩)
    (fun l => by
      obtain ⟨l | l, hl⟩ := l
      · exact ⟨hdim l, hl, B.isOpen_diff_M hO (fun z hz => hz.1.1) l⟩
      · exact ⟨hdim' l, hl, B'.isOpen_diff_M hO (fun z hz => hz.1.2) l⟩)
    (fun z hzO hzL => by
      have hgen1 : ∀ i, dim i < K → z ∉ B.M i := fun i hi hz => hzL ⟨Sum.inl i, hi⟩ hz
      have hgen2 : ∀ j, dim' j < K → z ∉ B'.M j := fun j hj hz => hzL ⟨Sum.inr j, hj⟩ hz
      refine (sum_subtype_filter (fun i => dim i = K ∧ y ∈ B.M i) (fun i => z ∈ B.M i)
        B.σ).trans (Eq.trans ?_ (sum_subtype_filter (fun j => dim' j = K ∧ y ∈ B'.M j)
        (fun j => z ∈ B'.M j) B'.σ).symm)
      have e1 : ∑ i with (dim i = K ∧ y ∈ B.M i) ∧ z ∈ B.M i, B.σ i = Θ z := by
        rw [B.eq_dimPart_topDim hzO.1.1 hgen1]
        unfold dimPart
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hzO.2.1.2 i h.2⟩, h.2⟩⟩
      have e2 : ∑ j with (dim' j = K ∧ y ∈ B'.M j) ∧ z ∈ B'.M j, B'.σ j = Θ z := by
        rw [B'.eq_dimPart_topDim hzO.1.2 (hK ▸ hgen2), hK]
        unfold dimPart
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hzO.2.2.2 j h.2⟩, h.2⟩⟩
      rw [e1, e2])
  unfold dimPart
  rw [Finset.sum_subtype (Finset.univ.filter fun i => dim i = K ∧ y ∈ B.M i)
      (p := fun i => dim i = K ∧ y ∈ B.M i) (by simp),
    Finset.sum_subtype (Finset.univ.filter fun j => dim' j = K ∧ y ∈ B'.M j)
      (p := fun j => dim' j = K ∧ y ∈ B'.M j) (by simp)]
  exact key

open scoped Classical in
/-- One direction of Lemma 9.6.4, under `TopMultiplicity` in the top dimension: a point top-good
for the first structure is top-good for the second.  Near `y` the top part `Θ'_k` is constant on
`M_U^k`, so by `eq_iff_of_mem_nbhdAt` every top `M'ⱼ` through `y` contains every nearby point of
`M_U^k`. -/
theorem isTopGoodPoint_of_topMultiplicity (hT : X.PObj.TopMultiplicity (B.topDim dim))
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) {y : Obj} (hyU : y ∈ B.U)
    (hyU' : y ∈ B'.U) (h : B.IsTopGoodPoint dim y) : B'.IsTopGoodPoint dim' y := by
  have hK : B'.topDim dim' = B.topDim dim := (lemma_9_6_1 hdim hdim').symm
  have h962 := lemma_9_6_2 hdim hdim'
  have hyM' : y ∈ B'.MU := by
    have := h.1
    rw [B.MU_eq] at this
    rw [B'.MU_eq]
    exact ⟨this.1, hyU'⟩
  refine ⟨hyM', ?_⟩
  by_cases hyT : y ∈ B'.topUnion dim' (B'.topDim dim')
  · obtain ⟨-, V, hV, hyV, hVU, hVeq⟩ := h
    set W := V ∩ (B.nbhdAt y ∩ B'.nbhdAt y)
    have hW : IsOpen W := hV.inter ((B.isOpen_nbhdAt y).inter (B'.isOpen_nbhdAt y))
    have hyW : y ∈ W := ⟨hyV, B.mem_nbhdAt_self hyU, B'.mem_nbhdAt_self hyU'⟩
    have key : ∀ j j', dim' j = B'.topDim dim' → dim' j' = B'.topDim dim' → y ∈ B'.M j →
        y ∈ B'.M j' → W ∩ B'.M j ⊆ W ∩ B'.M j' := by
      intro j j' hj hj' hyj hyj' z ⟨hzW, hzj⟩
      refine ⟨hzW, ?_⟩
      have hzU : z ∈ B.U := hzW.2.1.1
      have hzU' : z ∈ B'.U := hzW.2.2.1
      -- `z` lies on a top-dimensional `Mᵢ` through `y`
      have hzT : z ∈ B.topUnion dim (B.topDim dim) := by
        have : z ∈ B'.topUnion dim' (B'.topDim dim') ∩ B.U :=
          ⟨B'.mem_topUnion.2 ⟨j, hj, hzj⟩, hzU⟩
        rw [← h962] at this
        exact this.1
      obtain ⟨i, hi, hzi⟩ := B.mem_topUnion.1 hzT
      have hyi : y ∈ B.M i := hzW.2.1.2 i hzi
      have c1 : ∀ i', dim i' = B.topDim dim → (z ∈ B.M i' ↔ y ∈ B.M i') := fun i' hi' =>
        ⟨hzW.2.1.2 i', fun hyi' => by
          have : z ∈ V ∩ B.M i := ⟨hzW.1, hzi⟩
          rw [← hVeq i' i hi' hi hyi' hyi] at this
          exact this.2⟩
      have e1 : B.dimPart dim (B.topDim dim) z = B.dimPart dim (B.topDim dim) y := by
        unfold dimPart
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext i'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => ⟨h.1, (c1 i' h.1).1 h.2⟩, fun h => ⟨h.1, (c1 i' h.1).2 h.2⟩⟩
      have e2 : B'.dimPart dim' (B'.topDim dim') z = B'.dimPart dim' (B'.topDim dim') y := by
        rw [← dimPart_topDim_eq_of_topMultiplicity hT hdim hdim' hzU hzU',
          ← dimPart_topDim_eq_of_topMultiplicity hT hdim hdim' hyU hyU', e1]
      have hzN : z ∈ (B'.dimPartStructure dim' (B'.topDim dim')).nbhdAt y :=
        ⟨hzU', fun j hzj => hzW.2.2.2 j.1 hzj⟩
      exact ((B'.dimPartStructure dim' (B'.topDim dim')).eq_iff_of_mem_nbhdAt hyU' hzN).1 e2
        ⟨j', hj'⟩ hyj'
    exact ⟨W, hW, hyW, fun z hz => hz.2.2.1, fun j j' hj hj' hyj hyj' =>
      Subset.antisymm (key j j' hj hj' hyj hyj') (key j' j hj' hj hyj' hyj)⟩
  · exact ⟨B'.U, B'.isOpen_U, hyU', subset_rfl, fun j j' hj _ hyj _ =>
      (hyT (B'.mem_topUnion.2 ⟨j, hj, hyj⟩)).elim⟩

open scoped Classical in
/-- **Lemma 9.6.4, p. 455 (new in the 2021 edition) (top-good points are intrinsic)**, under
`TopMultiplicity` in the top dimension: a point of `U ∩ U'` is top-good for one local branching
structure iff it is for the other.  See the module docstring for why the hypothesis is used. -/
theorem lemma_9_6_4 (hT : X.PObj.TopMultiplicity (B.topDim dim))
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) {y : Obj} (hyU : y ∈ B.U)
    (hyU' : y ∈ B'.U) : B.IsTopGoodPoint dim y ↔ B'.IsTopGoodPoint dim' y := by
  have hT' : X.PObj.TopMultiplicity (B'.topDim dim') := by
    rw [← lemma_9_6_1 hdim hdim']; exact hT
  exact ⟨isTopGoodPoint_of_topMultiplicity hT hdim hdim' hyU hyU',
    isTopGoodPoint_of_topMultiplicity hT' hdim' hdim hyU' hyU⟩

open scoped Classical in
/-- **Lemma 9.6.4, p. 455, for top-bad points**, under `TopMultiplicity` in the top dimension: by
Lemma 9.6.2 and `lemma_9_6_4`. -/
theorem isTopBadPoint_iff (hT : X.PObj.TopMultiplicity (B.topDim dim))
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) {y : Obj} (hyU : y ∈ B.U)
    (hyU' : y ∈ B'.U) : B.IsTopBadPoint dim y ↔ B'.IsTopBadPoint dim' y := by
  unfold IsTopBadPoint
  rw [mem_topUnion_iff_of_mem hdim hdim' hyU hyU', lemma_9_6_4 hT hdim hdim' hyU hyU']

end Three

section Four

open scoped Classical in
/-- **A sub-family on an open set** (for "removing these manifolds", p. 454): the `Mᵢ ∩ V` with
`p i`, for an open `x ∈ V ⊆ U(x)`, are a local branching structure at `x` of every `Θ'` equal to
`∑_{p i, y ∈ Mᵢ} σᵢ` on `V`. -/
def subOn (B : X.LocalBranchingStructure Θ x) (p : B.ι → Prop) [DecidablePred p] {V : Set Obj}
    (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ B.U) (Θ' : Obj → ℚ)
    (h : ∀ y ∈ V, Θ' y = ∑ i with p i ∧ y ∈ B.M i, B.σ i) : X.LocalBranchingStructure Θ' x where
  U := V
  isOpen_U := hV
  mem_U := hxV
  ι := {i // p i}
  M i := B.M i.1 ∩ V
  subset_U _ := inter_subset_right
  isSmoothSubmanifold i := (B.isSmoothSubmanifold i.1).inter_isOpen hV
  mem_M i := ⟨B.mem_M i.1, hxV⟩
  isProperMap i := by
    refine (isProperMap_inclusion_iff _).2 ?_
    have h := (B.isClosed_M i.1).preimage (continuous_inclusion hVU)
    convert h using 1
    ext y
    exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
  σ i := B.σ i.1
  σ_pos i := B.σ_pos i.1
  eq_sum y hy := by
    rw [h y hy]
    refine (sum_subtype_eq _ _ (fun i => ?_) B.σ).symm
    simp [hy]

open scoped Classical in
/-- The `k`-dimensional part of `subOn` on `V`. -/
theorem subOn_dimPart (B : X.LocalBranchingStructure Θ x) (p : B.ι → Prop) [DecidablePred p]
    {V : Set Obj} (hV : IsOpen V) (hxV : x ∈ V) (hVU : V ⊆ B.U) (Θ' : Obj → ℚ)
    (h : ∀ y ∈ V, Θ' y = ∑ i with p i ∧ y ∈ B.M i, B.σ i) (dim : B.ι → ℕ) (k : ℕ) {y : Obj}
    (hy : y ∈ V) :
    (B.subOn p hV hxV hVU Θ' h).dimPart (fun i => dim i.1) k y =
      ∑ i with p i ∧ (dim i = k ∧ y ∈ B.M i), B.σ i := by
  unfold dimPart
  refine Finset.sum_bij (fun a _ => a.1) (fun a ha => ?_) (fun a _ b _ h => Subtype.ext h)
    (fun i hi => ?_) (fun _ _ => rfl)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    change dim a.1 = k ∧ y ∈ B.M a.1 ∩ V at ha
    exact ⟨a.2, ha.1, ha.2.1⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨⟨i, hi.1⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi.2.1, hi.2.2, hy⟩, rfl⟩

open scoped Classical in
/-- For `k ≠ K`, `Θ_k` only involves the `Mᵢ` not labelled `K`. -/
theorem dimPart_eq_sum_ne (B : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ) {K k : ℕ}
    (hk : k ≠ K) (y : Obj) :
    B.dimPart dim k y = ∑ i with dim i ≠ K ∧ (dim i = k ∧ y ∈ B.M i), B.σ i := by
  unfold dimPart
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h.1 ▸ hk, h⟩, fun h => h.2⟩

open scoped Classical in
/-- The descending induction of p. 454, by strong induction on the number of submanifolds of both
structures: the top parts agree on `U ∩ U'` (`dimPart_topDim_eq_of_topMultiplicity`), and the
remaining manifolds form two structures (`subOn`) of the same function there. -/
theorem dimPartsAgreeNear_of_topMultiplicity_aux (hT : ∀ k, X.PObj.TopMultiplicity k) (n : ℕ) :
    ∀ (Θ : Obj → ℚ) (B B' : X.LocalBranchingStructure Θ x) (dim : B.ι → ℕ) (dim' : B'.ι → ℕ),
      (∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) →
      (∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) →
      Fintype.card B.ι + Fintype.card B'.ι = n → DimPartsAgreeNear B B' dim dim' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Θ B B' dim dim' hdim hdim' hn
  have hO : IsOpen (B.U ∩ B'.U) := B.isOpen_U.inter B'.isOpen_U
  have hxO : x ∈ B.U ∩ B'.U := ⟨B.mem_U, B'.mem_U⟩
  -- the cases with an empty index set
  have hΘx : ∀ (C : X.LocalBranchingStructure Θ x), IsEmpty C.ι → Θ x = 0 := fun C hC => by
    rw [C.eq_sum x C.mem_U]
    exact Finset.sum_eq_zero fun i _ => hC.elim i
  have hΘx' : ∀ (C : X.LocalBranchingStructure Θ x), Nonempty C.ι → 0 < Θ x := fun C hC => by
    obtain ⟨i⟩ := hC
    exact (C.mem_supp_iff C.mem_U).2 ⟨i, C.mem_M i⟩
  rcases isEmpty_or_nonempty B.ι with hB | hB <;> rcases isEmpty_or_nonempty B'.ι with hB' | hB'
  · refine ⟨B.U ∩ B'.U, hO, hxO, subset_rfl, fun k y _ => ?_⟩
    unfold dimPart
    rw [Finset.sum_eq_zero fun i _ => hB.elim i, Finset.sum_eq_zero fun j _ => hB'.elim j]
  · exact absurd (hΘx' B' hB') (by rw [hΘx B hB]; exact lt_irrefl 0)
  · exact absurd (hΘx' B hB) (by rw [hΘx B' hB']; exact lt_irrefl 0)
  · -- both nonempty: the top-dimensional parts agree on `U ∩ U'`, then induct on the rest
    have hK : B'.topDim dim' = B.topDim dim := (lemma_9_6_1 hdim hdim').symm
    set K := B.topDim dim with hKdef
    have htop : ∀ y ∈ B.U ∩ B'.U, B.dimPart dim K y = B'.dimPart dim' K y := fun y hy => by
      have := dimPart_topDim_eq_of_topMultiplicity (hT K) hdim hdim' hy.1 hy.2
      rwa [hK] at this
    set Θ' : Obj → ℚ := fun y => ∑ i with dim i ≠ K ∧ y ∈ B.M i, B.σ i with hΘ'
    have hBL : ∀ y ∈ B.U ∩ B'.U, Θ' y = ∑ i with dim i ≠ K ∧ y ∈ B.M i, B.σ i :=
      fun y _ => rfl
    have hB'L : ∀ y ∈ B.U ∩ B'.U, Θ' y = ∑ j with dim' j ≠ K ∧ y ∈ B'.M j, B'.σ j := by
      intro y hy
      have h1 := B.eq_dimPart_add (dim := dim) K hy.1
      have h2 := B'.eq_dimPart_add (dim := dim') K hy.2
      rw [htop y hy] at h1
      change ∑ i with dim i ≠ K ∧ y ∈ B.M i, B.σ i = _
      linarith
    set BL := B.subOn (fun i => dim i ≠ K) hO hxO inter_subset_left Θ' hBL
    set B'L := B'.subOn (fun j => dim' j ≠ K) hO hxO inter_subset_right Θ' hB'L
    obtain ⟨i₀, hi₀⟩ := B.exists_dim_eq_topDim dim
    have hcard : Fintype.card BL.ι + Fintype.card B'L.ι < n := by
      have h1 : Fintype.card {i // dim i ≠ K} < Fintype.card B.ι :=
        Fintype.card_subtype_lt (x := i₀) (by simp [hi₀, hKdef])
      have h2 : Fintype.card {j // dim' j ≠ K} ≤ Fintype.card B'.ι :=
        Fintype.card_subtype_le _
      have h1' : Fintype.card BL.ι < Fintype.card B.ι := h1
      have h2' : Fintype.card B'L.ι ≤ Fintype.card B'.ι := h2
      omega
    obtain ⟨V, hV, hxV, hVU, hVk⟩ := ih _ hcard Θ' BL B'L (fun i => dim i.1) (fun j => dim' j.1)
      (fun i => (hdim i.1).inter_isOpen hO) (fun j => (hdim' j.1).inter_isOpen hO) rfl
    have hVO : V ⊆ B.U ∩ B'.U := fun y hy => (hVU hy).1
    refine ⟨V, hV, hxV, hVO, fun k y hy => ?_⟩
    by_cases hk : k = K
    · subst hk; exact htop y (hVO hy)
    · have := hVk k y hy
      rw [subOn_dimPart B _ hO hxO inter_subset_left Θ' hBL dim k (hVO hy),
        subOn_dimPart B' _ hO hxO inter_subset_right Θ' hB'L dim' k (hVO hy)] at this
      rw [B.dimPart_eq_sum_ne dim hk, B'.dimPart_eq_sum_ne dim' hk]
      exact this

open scoped Classical in
/-- **Proposition 9.1.12 locally**, under `TopMultiplicity` in every dimension: the dimensional
decompositions of any two local branching structures (with dimension labels) of any `Θ` at `x`
agree on an open `V ∋ x` inside both domains. -/
theorem dimPartsAgreeNear_of_topMultiplicity (hT : ∀ k, X.PObj.TopMultiplicity k)
    (B B' : X.LocalBranchingStructure Θ x) {dim : B.ι → ℕ} {dim' : B'.ι → ℕ}
    (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) :
    DimPartsAgreeNear B B' dim dim' :=
  dimPartsAgreeNear_of_topMultiplicity_aux hT _ Θ B B' dim dim' hdim hdim' rfl

end Four

end LocalBranchingStructure

/-- **Proposition 9.1.12, p. 408 (new in the 2021 edition; proof in §9.6.1, pp. 452–457)**, for an
ep-groupoid whose object M-polyfold satisfies `TopMultiplicity` in every dimension. -/
theorem proposition_9_1_12_of_topMultiplicity (hT : ∀ k, X.PObj.TopMultiplicity k) :
    X.Proposition_9_1_12 := fun _ _ _ B B' _ _ hdim hdim' =>
  LocalBranchingStructure.dimPartsAgreeNear_of_topMultiplicity hT B B' hdim hdim'

end EpGroupoid

/-! ### Witnesses: `ℝⁿ` -/

section Rn

/-- The model of the standard chart of `ℝⁿ` is finite-dimensional at level `0`. -/
theorem rnChart_model_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ ((rnChart n 0).model.E 0) :=
  (inferInstance : FiniteDimensional ℝ (Fin n → ℝ))

/-- The model of the standard chart of `ℝⁿ` has dimension `n` at level `0`. -/
theorem rnChart_model_finrank (n : ℕ) : finrank ℝ ((rnChart n 0).model.E 0) = n :=
  (by simp : finrank ℝ (Fin n → ℝ) = n)

/-- A submanifold of `ℝⁿ` has dimension at most `n`. -/
theorem rnPolyfold_hasDimAt_le {n : ℕ} {A : Set (Fin n → ℝ)} {a : Fin n → ℝ} {k : ℕ}
    (h : (rnPolyfold n).HasDimAt A a k) : k ≤ n := by
  obtain ⟨-, d, -, -, ha, -⟩ := id h
  let z : (rnChart n 0).model.E 1 := (a : Fin n → ℝ)
  have hk := h.finrank_eq d (isChart_rnChart 0) (z' := z) ha (mem_univ a) (by
    change (ScBanach.const (Fin n → ℝ)).toBase 1 a = a - 0
    rw [ScBanach.const_toBase, sub_zero])
  rw [← hk]
  have := rnChart_model_finiteDimensional n
  exact (Submodule.finrank_le _).trans (rnChart_model_finrank n).le

/-- **An `n`-dimensional submanifold of `ℝⁿ` is a neighbourhood of each of its points**: the
retraction of a chart has surjective, hence identity, derivative at the point, so by the inverse
function theorem its image is a neighbourhood. -/
theorem rnPolyfold_mem_nhds_of_hasDimAt {n : ℕ} {A : Set (Fin n → ℝ)} {a : Fin n → ℝ}
    (h : (rnPolyfold n).HasDimAt A a n) : A ∈ 𝓝 a := by
  obtain ⟨haA, d, -, -, ha, -⟩ := id h
  have hφ : (rnPolyfold n).IsChart (rnChart n 0) := isChart_rnChart 0
  obtain ⟨t, ht⟩ := d.toSubData.isScRetract_image (rnChart n 0) hφ
  let z : (rnChart n 0).model.E 1 := (a : Fin n → ℝ)
  have hz : (rnChart n 0).model.E.toBase 1 z = (rnChart n 0) a := by
    change (ScBanach.const (Fin n → ℝ)).toBase 1 a = a - 0
    rw [ScBanach.const_toBase, sub_zero]
  have hk := h.finrank_eq d hφ ha (mem_univ a) hz
  have haW : a ∈ d.toSubData.shrink (rnChart n 0) :=
    d.toSubData.mem_shrink (rnChart n 0) haA ha (mem_univ a)
  have hat : a ∈ t.retract := by
    rw [ht]; exact ⟨a, ⟨haW, haA⟩, by rw [rnChart_apply, sub_zero]⟩
  have hzt : z ∈ (rnChart n 0).model.E.lvlSet t.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, rnChart_apply, sub_zero]; exact hat
  rw [← ht, tangentSpace_eq_coe_submodule t hzt, span_eq] at hk
  have := rnChart_model_finiteDimensional n
  have htop : LinearMap.range (scDeriv t.U t z :
      (rnChart n 0).model.E 0 →ₗ[ℝ] (rnChart n 0).model.E 0) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hk, rnChart_model_finrank])
  have hid : ∀ v, scDeriv t.U t z v = v := by
    intro v
    obtain ⟨w, hw⟩ := LinearMap.range_eq_top.1 htop v
    have hc := congrArg (fun L => L w) (t.scDeriv_comp_self hzt)
    simp only [ContinuousLinearMap.comp_apply] at hc
    change scDeriv t.U t z w = v at hw
    rw [← hw]
    exact hc
  obtain ⟨Ot, hOt, hUt⟩ := t.relOpen.relOpen
  have hUo : IsOpen (t.U : Set (Fin n → ℝ)) := by
    rw [hUt]
    change IsOpen (Ot ∩ univ)
    rw [inter_univ]; exact hOt
  have haU : a ∈ t.U := t.retract_subset hat
  let g : (Fin n → ℝ) → Fin n → ℝ := t
  have hC1 : ContDiffOn ℝ 1 g t.U :=
    (isSc1_iff_contDiffOn_const (V := Fin n → ℝ) (W := Fin n → ℝ) t.isScDomain t).1 t.isSc1
  have hd : HasFDerivWithinAt g (scDeriv (E := rnSc n) (F := rnSc n) t.U t a) t.U a :=
    hasFDerivWithinAt_scDeriv_const' (V := Fin n → ℝ) (F := rnSc n) (U := t.U) (f := t)
      t.isSc1 haU
  have hfd : fderiv ℝ g a = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    rw [(hd.hasFDerivAt (hUo.mem_nhds haU)).fderiv]
    ext1 v
    exact hid v
  have hstrict : HasStrictFDerivAt g (fderiv ℝ g a) a :=
    (hC1.contDiffAt (hUo.mem_nhds haU)).hasStrictFDerivAt one_ne_zero
  rw [hfd] at hstrict
  have hstrict' : HasStrictFDerivAt g
      ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] Fin n → ℝ) a := by
    rw [ContinuousLinearEquiv.coe_refl]; exact hstrict
  have hmap := hstrict'.map_nhds_eq_of_equiv
  have hta : g a = a := t.apply_eq_self_of_mem_retract hat
  have himg : g '' t.U ∈ 𝓝 a := by
    rw [← hta, ← hmap]; exact image_mem_map (hUo.mem_nhds haU)
  refine mem_of_superset himg ?_
  rintro _ ⟨u, hu, rfl⟩
  have hu' := t.apply_mem_retract hu
  rw [ht] at hu'
  obtain ⟨b, ⟨-, hbA⟩, hb⟩ := hu'
  rw [rnChart_apply, sub_zero] at hb
  change t u ∈ A
  rw [← hb]; exact hbA

open scoped ContDiff in
/-- `ℝⁿ` is an `n`-dimensional submanifold of itself. -/
theorem rnPolyfold_isSubmanifoldOfDim_univ (n : ℕ) :
    (rnPolyfold n).IsSubmanifoldOfDim univ n := by
  have hr : range (id : (Fin n → ℝ) → Fin n → ℝ) = univ := range_id
  refine ⟨hr ▸ rnPolyfold_isSmoothSubmanifold_range contDiff_id (fun _ => rfl), fun a _ => ?_⟩
  have h := rnPolyfold_hasDimAt_range (s := id) contDiff_id (fun _ => rfl) (hr ▸ mem_univ a)
  rw [hr, fderiv_id, ContinuousLinearMap.coe_id, LinearMap.range_id, finrank_top] at h
  simpa using h

open scoped Classical in
/-- **Witness for `TopMultiplicity`**: `ℝⁿ` satisfies it in every dimension `k ≥ n`.  For `k > n`
there are no `k`-dimensional submanifolds; for `k = n` all `Mᵢ`, `Nⱼ` are neighbourhoods of `x`,
and the covering lemma gives a point near `x` off the `L_l` lying on all of them. -/
theorem topMultiplicity_rn_of_le {n k : ℕ} (hnk : n ≤ k) : (rnPolyfold n).TopMultiplicity k := by
  intro x O hO hxO ι κ ν _ _ _ M σ N τ L dL hM hN hL hagree
  rcases hnk.lt_or_eq with hlt | rfl
  · have hι : IsEmpty ι := ⟨fun i =>
      absurd (rnPolyfold_hasDimAt_le ((hM i).1.2 x (hM i).2.1)) (not_le.2 hlt)⟩
    have hκ : IsEmpty κ := ⟨fun j =>
      absurd (rnPolyfold_hasDimAt_le ((hN j).1.2 x (hN j).2.1)) (not_le.2 hlt)⟩
    simp [Finset.univ_eq_empty]
  · have hMn : ∀ i, M i ∈ 𝓝 x := fun i =>
      rnPolyfold_mem_nhds_of_hasDimAt ((hM i).1.2 x (hM i).2.1)
    have hNn : ∀ j, N j ∈ 𝓝 x := fun j =>
      rnPolyfold_mem_nhds_of_hasDimAt ((hN j).1.2 x (hN j).2.1)
    set W := O ∩ ((⋂ i, interior (M i)) ∩ ⋂ j, interior (N j))
    have hW : IsOpen W := hO.inter ((isOpen_iInter_of_finite fun _ => isOpen_interior).inter
      (isOpen_iInter_of_finite fun _ => isOpen_interior))
    have hxW : x ∈ W := ⟨hxO, mem_iInter.2 fun i => mem_interior_iff_mem_nhds.2 (hMn i),
      mem_iInter.2 fun j => mem_interior_iff_mem_nhds.2 (hNn j)⟩
    obtain ⟨y, ⟨-, hyW⟩, hy⟩ := MPolyfold.exists_mem_forall_notMem
      (rnPolyfold_isSubmanifoldOfDim_univ _) Finset.univ L dL (fun l _ => (hL l).1)
      (fun l _ => (hL l).2.1) (fun l _ => (hL l).2.2) hW inter_subset_left (mem_univ x) hxW
    have h := hagree y hyW.1 fun l => hy l (Finset.mem_univ l)
    rwa [Finset.filter_true_of_mem fun i _ => interior_subset (mem_iInter.1 hyW.2.1 i),
      Finset.filter_true_of_mem fun j _ => interior_subset (mem_iInter.1 hyW.2.2 j)] at h

/-- `ℝ⁰` satisfies `TopMultiplicity` in every dimension. -/
theorem topMultiplicity_rn_zero (k : ℕ) : (rnPolyfold 0).TopMultiplicity k :=
  topMultiplicity_rn_of_le (Nat.zero_le k)

/-- `ℝ¹` satisfies `TopMultiplicity` in every dimension. -/
theorem topMultiplicity_rn_one (k : ℕ) : (rnPolyfold 1).TopMultiplicity k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact MPolyfold.topMultiplicity_zero _
  · exact topMultiplicity_rn_of_le hk

/-- **Proposition 9.1.12, p. 408, for the trivial ep-groupoid of `ℝ⁰`**, unconditionally. -/
theorem proposition_9_1_12_rn_zero : (EpGroupoid.trivial (rnPolyfold 0)).Proposition_9_1_12 :=
  EpGroupoid.proposition_9_1_12_of_topMultiplicity topMultiplicity_rn_zero

/-- **Proposition 9.1.12, p. 408, for the trivial ep-groupoid of `ℝ¹`**, unconditionally.  By
`exists_mixed_rn_one` this covers structures with submanifolds of different dimensions. -/
theorem proposition_9_1_12_rn_one : (EpGroupoid.trivial (rnPolyfold 1)).Proposition_9_1_12 :=
  EpGroupoid.proposition_9_1_12_of_topMultiplicity topMultiplicity_rn_one

open scoped Classical in
/-- **A branched ep⁺-subgroupoid with a mixed-dimensional structure** (witness for the hypotheses
of Proposition 9.1.12 beyond the equidimensional case): on `ℝ¹`, `Θ = 1 + δ_0` (weights `1` on
`ℝ` and on `{0}`) has at `0` a local branching structure with dimension labels in which both
dimensions `0` and `1` occur. -/
theorem exists_mixed_rn_one : ∃ (Θ : (Fin 1 → ℝ) → ℚ)
    (B : (EpGroupoid.trivial (rnPolyfold 1)).LocalBranchingStructure Θ 0) (dim : B.ι → ℕ),
    (EpGroupoid.trivial (rnPolyfold 1)).IsBranchedEpSubgroupoid Θ ∧
      (∀ i, (rnPolyfold 1).IsSubmanifoldOfDim (B.M i) (dim i)) ∧ (∃ i, dim i = 0) ∧
        ∃ i, dim i = 1 := by
  set M : Fin 2 → Set (Fin 1 → ℝ) := ![univ, {0}]
  have hMd : ∀ i, (rnPolyfold 1).IsSubmanifoldOfDim (M i) (![1, 0] i) := by
    intro i
    fin_cases i
    · exact rnPolyfold_isSubmanifoldOfDim_univ 1
    · exact EpGroupoid.rnPolyfold_isSubmanifoldOfDim_singleton 0
  have hc : ∀ i, IsClosed (M i) := by
    intro i
    fin_cases i
    · exact isClosed_univ
    · exact isClosed_singleton
  set B := EpGroupoid.localBranchingStructure_sum_rn M 1 (fun _ => one_pos) (fun i => (hMd i).1)
    hc 0
  refine ⟨_, B, fun i => ![1, 0] i.1,
    EpGroupoid.isBranchedEpSubgroupoid_sum_rn M 1 (fun _ => one_pos) (fun i => (hMd i).1) hc,
    fun i => (hMd i.1).inter_isOpen B.isOpen_U, ⟨⟨1, rfl⟩, rfl⟩, ⟨⟨0, mem_univ _⟩, rfl⟩⟩

end Rn

end Polyfold
