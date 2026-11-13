import Polyfold.Chapter9.Measure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §9.5,
**Theorems 9.5.15 and 9.5.16** (canonical boundary measures, p. 449; 2017: Theorems 9.5, 9.6,
p. 327), and the same step of **Theorems 9.5.4 and 9.5.5** (p. 438): the passage from the local
formulas to the measure (gap G.109).

# Signed measures from local formulas

## The text, paraphrased

(pp. 438, 449) There is a linear map `ω ↦ μ_ω` into the signed measures on `(∂S, L(∂S))`
"uniquely characterized" by: for `x ∈ supp(∂Θ)`, a suitable `U(x)` and an oriented branching
structure on it, `μ_ω(K)` is the weighted sum of the integrals of `ω` over the preimages `Kᵢ`,
for every measurable `K ⊆ |M_U^∂|`.  (p. 446, proof of Theorems 9.5.4, 9.5.5) By compactness
finitely many `|U(x)|` cover; the local expressions are compatible on overlaps (Lemmas 9.5.7,
9.5.9–9.5.11), and this "defines our desired signed measure".

## What is formalized

The step from the compatible local expressions to the measure, and the uniqueness:

* `SignedMeasure.eq_sum_range_inter`: finite additivity over a measurable partition.
* `existsUnique_signedMeasure_of_local`: for measurable `W₀, …, W_{N-1}` covering `T` and signed
  measures `μ₀, …, μ_{N-1}` agreeing on the measurable subsets of the overlaps, there is exactly
  one signed measure `ν` with `ν(K) = μₖ(K)` for the measurable `K ⊆ Wₖ`.
* `existsUnique_linearMap_signedMeasure_of_local`: the same for linear families `ω ↦ μₖ(ω)`:
  exactly one linear `Φ` with `Φ(ω)(K) = μₖ(ω)(K)`.
* `existsUnique_linearMap_signedMeasure_of_openCover`: on a compact space `T` with a σ-algebra
  containing the Borel sets, for local linear expressions `μ_j` on the members of an open cover
  `(O_j)` that agree on overlaps: exactly one linear `Φ` with `Φ(ω)(K) = μ_j(ω)(K)` for every
  measurable `K ⊆ O_j`.
* `EpGroupoid.isClosed_orbitSupp_boundaryTheta`, `isCompact_orbitSupp_boundaryTheta`: `∂S` is
  closed in `S`, so `∂Θ` is compact when `Θ` is.
* `EpGroupoid.theorem_9_5_15_of_overlap`: the form for `(∂S, L(∂S))`: `Θ` tame and compact, for every
  `x ∈ supp(∂Θ)` and every tame branching structure `B` at `x` a linear local expression
  `loc x B` (the right-hand side of the characterizing identity, as a signed measure), any two
  agreeing on the measurable subsets of `∂S ∩ |U(x)| ∩ |U(x')|`: there is exactly one linear
  `Φ : V → M(∂S, L(∂S))` with `Φ(ω)(K) = loc x B ω K` for all measurable `K ⊆ ∂S ∩ |U(x)|`.
  With `V = Ωⁿ⁻¹_∞(X)` and the weights `1/♯G_x` or `1/♯G_x^{eff}` these are the statements of
  Theorems 9.5.15 and 9.5.16, given the local expressions and their agreement on overlaps.

## Not formalized

The local expressions themselves (the integrals of `ω` over measurable subsets of `∂Mᵢ` with the
boundary orientation) and their agreement on overlaps, the boundary versions of Lemmas 9.5.7 and
9.5.9–9.5.11.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Finite additivity and the gluing of signed measures -/

section Glue

variable {T : Type*}

/-- The pieces `Dₙ = Wₙ ∖ ⋃_{j<n} W_j` of a cover. -/
def firstPiece (W : ℕ → Set T) (n : ℕ) : Set T := W n \ ⋃ j, ⋃ (_ : j < n), W j

theorem firstPiece_subset (W : ℕ → Set T) (n : ℕ) : firstPiece W n ⊆ W n := sdiff_subset

theorem measurableSet_firstPiece [MeasurableSpace T] {W : ℕ → Set T} (hW : ∀ n, MeasurableSet (W n)) (n : ℕ) :
    MeasurableSet (firstPiece W n) :=
  (hW n).diff (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hW j)

theorem pairwise_disjoint_firstPiece (W : ℕ → Set T) :
    Pairwise (Function.onFun Disjoint (firstPiece W)) := by
  have key : ∀ m n, m < n → Disjoint (firstPiece W m) (firstPiece W n) := fun m n hmn =>
    disjoint_left.2 fun x hxm hxn =>
      hxn.2 (mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨hmn, hxm.1⟩⟩)
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact key m n h
  · exact (key n m h).symm

theorem subset_iUnion_firstPiece {W : ℕ → Set T} {N : ℕ} {K : Set T}
    (hK : K ⊆ ⋃ n, ⋃ (_ : n < N), W n) : K ⊆ ⋃ n, ⋃ (_ : n < N), firstPiece W n := by
  classical
  intro x hx
  have hex : ∃ n, n < N ∧ x ∈ W n := by
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hK hx)
    obtain ⟨hnN, hxn⟩ := mem_iUnion.1 hn
    exact ⟨n, hnN, hxn⟩
  have hmin : ∀ j, j < Nat.find hex → ¬ (j < N ∧ x ∈ W j) := fun j hj => Nat.find_min hex hj
  obtain ⟨hN, hxW⟩ := Nat.find_spec hex
  refine mem_iUnion.2 ⟨Nat.find hex, mem_iUnion.2 ⟨hN, hxW, fun hmem => ?_⟩⟩
  obtain ⟨j, hj⟩ := mem_iUnion.1 hmem
  obtain ⟨hjlt, hxj⟩ := mem_iUnion.1 hj
  exact hmin j hjlt ⟨hjlt.trans hN, hxj⟩

variable [MeasurableSpace T]

/-- **Finite additivity over a partition**: for pairwise disjoint measurable `D₀, D₁, …` and a
measurable `K ⊆ D₀ ∪ … ∪ D_{N-1}`, `v(K) = ∑_{n<N} v(K ∩ Dₙ)`. -/
theorem SignedMeasure.eq_sum_range_inter (v : SignedMeasure T) {D : ℕ → Set T}
    (hD : ∀ n, MeasurableSet (D n)) (hdisj : Pairwise (Function.onFun Disjoint D)) {N : ℕ}
    {K : Set T} (hK : MeasurableSet K) (hcov : K ⊆ ⋃ n, ⋃ (_ : n < N), D n) :
    v K = ∑ n ∈ Finset.range N, v (K ∩ D n) := by
  classical
  set f : ℕ → Set T := fun n => if n < N then K ∩ D n else ∅ with hf
  have hfm : ∀ n, MeasurableSet (f n) := fun n => by
    simp only [hf]; split_ifs
    · exact hK.inter (hD n)
    · exact MeasurableSet.empty
  have hfd : Pairwise (Function.onFun Disjoint f) := fun m n hmn => by
    simp only [Function.onFun, hf]
    split_ifs
    · exact (hdisj hmn).mono inter_subset_right inter_subset_right
    · exact disjoint_bot_right
    · exact disjoint_bot_left
    · exact disjoint_bot_left
  have hfU : ⋃ n, f n = K := by
    apply Subset.antisymm
    · refine iUnion_subset fun n => ?_
      simp only [hf]; split_ifs
      · exact inter_subset_left
      · exact empty_subset _
    · intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov hx)
      obtain ⟨hnN, hxn⟩ := mem_iUnion.1 hn
      exact mem_iUnion.2 ⟨n, by simp only [hf, if_pos hnN]; exact ⟨hx, hxn⟩⟩
  have h1 := v.of_disjoint_iUnion hfm hfd
  rw [hfU, tsum_eq_sum (s := Finset.range N) (fun n hn => by
    have : ¬ n < N := fun h => hn (Finset.mem_range.2 h)
    simp only [hf, if_neg this, VectorMeasure.empty])] at h1
  rw [h1]
  exact Finset.sum_congr rfl fun n hn => by
    simp only [hf, if_pos (Finset.mem_range.1 hn)]

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The glued linear family: `∑_{n<N} μₙ(ω)|_{Dₙ}`. -/
def glueLinear (W : ℕ → Set T) (N : ℕ) (μ : ℕ → V →ₗ[ℝ] SignedMeasure T) :
    V →ₗ[ℝ] SignedMeasure T :=
  ∑ n ∈ Finset.range N, (VectorMeasure.restrictₗ (firstPiece W n)).comp (μ n)

theorem glueLinear_apply {W : ℕ → Set T} (hW : ∀ n, MeasurableSet (W n)) (N : ℕ)
    (μ : ℕ → V →ₗ[ℝ] SignedMeasure T) (ω : V) {K : Set T} (hK : MeasurableSet K) :
    glueLinear W N μ ω K = ∑ n ∈ Finset.range N, μ n ω (K ∩ firstPiece W n) := by
  have hsum : ∀ (s : Finset ℕ) (v : ℕ → SignedMeasure T),
      (∑ n ∈ s, v n) K = ∑ n ∈ s, v n K := fun s v => by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]
  simp only [glueLinear, LinearMap.sum_apply, LinearMap.comp_apply, VectorMeasure.restrictₗ_apply]
  rw [hsum]
  exact Finset.sum_congr rfl fun n _ =>
    VectorMeasure.restrict_apply _ (measurableSet_firstPiece hW n) hK

/-- **Linear families of signed measures from local expressions**: for measurable
`W₀, …, W_{N-1}` covering `T` and linear `μₖ : V → M(T)` agreeing on the measurable subsets of the
overlaps `Wₖ ∩ W_l`, there is exactly one linear `Φ : V → M(T)` with `Φ(ω)(K) = μₖ(ω)(K)` for all
measurable `K ⊆ Wₖ`, `k < N`. -/
theorem existsUnique_linearMap_signedMeasure_of_local {W : ℕ → Set T} {N : ℕ}
    (hW : ∀ n, MeasurableSet (W n)) (hcov : ⋃ n, ⋃ (_ : n < N), W n = univ)
    (μ : ℕ → V →ₗ[ℝ] SignedMeasure T)
    (hcompat : ∀ k < N, ∀ l < N, ∀ ω K, MeasurableSet K → K ⊆ W k ∩ W l →
      μ k ω K = μ l ω K) :
    ∃! Φ : V →ₗ[ℝ] SignedMeasure T, ∀ k < N, ∀ ω K, MeasurableSet K → K ⊆ W k →
      Φ ω K = μ k ω K := by
  have hpart : ∀ K : Set T, K ⊆ ⋃ n, ⋃ (_ : n < N), firstPiece W n := fun K =>
    subset_iUnion_firstPiece (hcov ▸ subset_univ K)
  have hD := measurableSet_firstPiece hW
  refine ⟨glueLinear W N μ, fun k hk ω K hK hKW => ?_, fun Ψ hΨ => ?_⟩
  · rw [glueLinear_apply hW N μ ω hK,
      SignedMeasure.eq_sum_range_inter (μ k ω) hD (pairwise_disjoint_firstPiece W) hK (hpart K)]
    refine Finset.sum_congr rfl fun n hn => ?_
    exact hcompat n (Finset.mem_range.1 hn) k hk ω _ (hK.inter (hD n))
      fun x hx => ⟨firstPiece_subset W n hx.2, hKW hx.1⟩
  · refine LinearMap.ext fun ω => VectorMeasure.ext fun K hK => ?_
    rw [glueLinear_apply hW N μ ω hK,
      SignedMeasure.eq_sum_range_inter (Ψ ω) hD (pairwise_disjoint_firstPiece W) hK (hpart K)]
    refine Finset.sum_congr rfl fun n hn => ?_
    exact hΨ n (Finset.mem_range.1 hn) ω _ (hK.inter (hD n))
      fun x hx => firstPiece_subset W n hx.2

/-- **A signed measure from local ones**: the case of one measure (`V = ℝ`, `ω = 1`) of
`existsUnique_linearMap_signedMeasure_of_local`. -/
theorem existsUnique_signedMeasure_of_local {W : ℕ → Set T} {N : ℕ}
    (hW : ∀ n, MeasurableSet (W n)) (hcov : ⋃ n, ⋃ (_ : n < N), W n = univ)
    (μ : ℕ → SignedMeasure T)
    (hcompat : ∀ k < N, ∀ l < N, ∀ K, MeasurableSet K → K ⊆ W k ∩ W l → μ k K = μ l K) :
    ∃! ν : SignedMeasure T, ∀ k < N, ∀ K, MeasurableSet K → K ⊆ W k → ν K = μ k K := by
  have hpart : ∀ K : Set T, K ⊆ ⋃ n, ⋃ (_ : n < N), firstPiece W n := fun K =>
    subset_iUnion_firstPiece (hcov ▸ subset_univ K)
  have hD := measurableSet_firstPiece hW
  obtain ⟨Φ, hΦ, -⟩ := existsUnique_linearMap_signedMeasure_of_local hW hcov
    (fun n => LinearMap.toSpanSingleton ℝ (SignedMeasure T) (μ n))
    (fun k hk l hl ω K hK hKW => by
      simp only [LinearMap.toSpanSingleton_apply, smul_apply]
      rw [hcompat k hk l hl K hK hKW])
  refine ⟨Φ 1, fun k hk K hK hKW => ?_, fun ν hν => VectorMeasure.ext fun K hK => ?_⟩
  · rw [hΦ k hk 1 K hK hKW]
    simp
  · rw [SignedMeasure.eq_sum_range_inter ν hD (pairwise_disjoint_firstPiece W) hK (hpart K),
      SignedMeasure.eq_sum_range_inter (Φ 1) hD (pairwise_disjoint_firstPiece W) hK (hpart K)]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_range.1 hn
    have hsub : K ∩ firstPiece W n ⊆ W n := fun x hx => firstPiece_subset W n hx.2
    rw [hν n hn' _ (hK.inter (hD n)) hsub, hΦ n hn' 1 _ (hK.inter (hD n)) hsub]
    simp

end Glue

/-! ### Compact spaces and open covers -/

section OpenCover

variable {T : Type*} [TopologicalSpace T] [CompactSpace T] [m : MeasurableSpace T]
  {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The measure from local expressions on an open cover of a compact space**: let the σ-algebra
of `T` contain the Borel sets, `(O_j)` be an open cover and `μ_j : V → M(T)` linear, with
`μ_j(ω)(K) = μ_l(ω)(K)` for the measurable `K ⊆ O_j ∩ O_l`.  Then there is exactly one linear
`Φ : V → M(T)` with `Φ(ω)(K) = μ_j(ω)(K)` for every `j` and every measurable `K ⊆ O_j`. -/
theorem existsUnique_linearMap_signedMeasure_of_openCover (hm : borel T ≤ m) {J : Type*}
    (O : J → Set T) (hO : ∀ j, IsOpen (O j)) (hcov : ⋃ j, O j = univ)
    (μ : J → V →ₗ[ℝ] SignedMeasure T)
    (hcompat : ∀ j l ω K, MeasurableSet K → K ⊆ O j ∩ O l → μ j ω K = μ l ω K) :
    ∃! Φ : V →ₗ[ℝ] SignedMeasure T, ∀ j ω K, MeasurableSet K → K ⊆ O j → Φ ω K = μ j ω K := by
  classical
  have hOm : ∀ j, MeasurableSet (O j) := fun j =>
    hm _ (MeasurableSpace.measurableSet_generateFrom (hO j))
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO hcov.ge
  rcases isEmpty_or_nonempty J with hJ | ⟨⟨j₀⟩⟩
  · -- `T` is empty
    have hT : ∀ K : Set T, K = ∅ := fun K => by
      rw [← subset_empty_iff, ← iUnion_of_empty O, hcov]; exact subset_univ K
    refine ⟨0, fun j => (hJ.false j).elim, fun Ψ _ => LinearMap.ext fun ω =>
      VectorMeasure.ext fun K _ => ?_⟩
    rw [hT K]; simp
  -- enumerate the finite subcover
  set e := s.equivFin
  set idx : ℕ → J := fun n => if h : n < s.card then (e.symm ⟨n, h⟩ : J) else j₀ with hidx
  set W : ℕ → Set T := fun n => O (idx n) with hWdef
  have hcovW : ⋃ n, ⋃ (_ : n < s.card), W n = univ := by
    refine eq_univ_of_univ_subset fun x _ => ?_
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hs (mem_univ x))
    obtain ⟨hjs, hxj⟩ := mem_iUnion.1 hj
    refine mem_iUnion.2 ⟨(e ⟨j, hjs⟩ : ℕ), mem_iUnion.2 ⟨(e ⟨j, hjs⟩).2, ?_⟩⟩
    simp only [hWdef, hidx, dif_pos (e ⟨j, hjs⟩).2, Fin.eta, Equiv.symm_apply_apply]
    exact hxj
  obtain ⟨Φ, hΦ, hΦu⟩ := existsUnique_linearMap_signedMeasure_of_local (W := W)
    (fun n => hOm (idx n)) hcovW (fun n => μ (idx n))
    (fun k _ l _ ω K hK hKW => hcompat (idx k) (idx l) ω K hK hKW)
  have hpart : ∀ K : Set T, K ⊆ ⋃ n, ⋃ (_ : n < s.card), firstPiece W n := fun K =>
    subset_iUnion_firstPiece (hcovW ▸ subset_univ K)
  have hD := measurableSet_firstPiece fun n => hOm (idx n)
  have hall : ∀ j ω K, MeasurableSet K → K ⊆ O j → Φ ω K = μ j ω K := fun j ω K hK hKj => by
    rw [SignedMeasure.eq_sum_range_inter (Φ ω) hD (pairwise_disjoint_firstPiece W) hK (hpart K),
      SignedMeasure.eq_sum_range_inter (μ j ω) hD (pairwise_disjoint_firstPiece W) hK (hpart K)]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hsub : K ∩ firstPiece W n ⊆ W n := fun x hx => firstPiece_subset W n hx.2
    rw [hΦ n (Finset.mem_range.1 hn) ω _ (hK.inter (hD n)) hsub]
    exact hcompat (idx n) j ω _ (hK.inter (hD n)) fun x hx => ⟨hsub hx, hKj hx.1⟩
  exact ⟨Φ, hall, fun Ψ hΨ => hΦu Ψ fun k _ ω K hK hKW => hΨ (idx k) ω K hK hKW⟩

end OpenCover

/-! ### Theorems 9.5.15 and 9.5.16 from the local expressions -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {S' : Set (Set Obj)} (G' : SheetNullSets S') {Θ : Obj → ℚ}
  {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A sheet of a local branching structure is closed in `U(x)` (the inclusion is proper). -/
theorem LocalBranchingStructure.exists_isClosed_eq_inter {x : Obj}
    (B : X.LocalBranchingStructure Θ x) (i : B.ι) : ∃ t, IsClosed t ∧ B.M i = t ∩ B.U := by
  have hcl : IsClosed (range (Set.inclusion (B.subset_U i))) :=
    (B.isProperMap i).isClosedMap.isClosed_range
  obtain ⟨t, ht, hteq⟩ := isClosed_induced_iff.1 hcl
  refine ⟨t, ht, ?_⟩
  ext y
  constructor
  · intro hy
    have : (⟨y, B.subset_U i hy⟩ : B.U) ∈ Subtype.val ⁻¹' t := hteq ▸ ⟨⟨y, hy⟩, rfl⟩
    exact ⟨this, B.subset_U i hy⟩
  · rintro ⟨hyt, hyU⟩
    have : (⟨y, hyU⟩ : B.U) ∈ range (Set.inclusion (B.subset_U i)) := hteq ▸ hyt
    obtain ⟨⟨z, hz⟩, hzy⟩ := this
    have : z = y := congrArg Subtype.val hzy
    exact this ▸ hz

/-- `∂M` is closed in `M`. -/
theorem exists_isClosed_submanifoldBoundary_eq {A : Set Obj}
    (hA : X.PObj.IsSmoothSubmanifold A) :
    ∃ t, IsClosed t ∧ X.PObj.submanifoldBoundary A = t ∩ A := by
  let _ := X.PObj.paracompactSpace_subtype A
  obtain ⟨t, ht, hteq⟩ := isClosed_induced_iff.1
    (MPolyfold.subPolyfold hA.isSubMPolyfold).isClosed_boundary
  refine ⟨t, ht, ?_⟩
  ext y
  constructor
  · intro hy
    have hyA : y ∈ A := by obtain ⟨-, hy', -⟩ := hy; exact hy'
    have h1 := (MPolyfold.mem_submanifoldBoundary_iff_mem_boundary hA ⟨y, hyA⟩).1 hy
    rw [← hteq] at h1
    exact ⟨h1, hyA⟩
  · rintro ⟨hyt, hyA⟩
    refine (MPolyfold.mem_submanifoldBoundary_iff_mem_boundary hA ⟨y, hyA⟩).2 ?_
    rw [← hteq]
    exact hyt

/-- **`∂S` is closed** when `S` is: near a point of `supp(Θ)` the complement of `supp(∂Θ)` in
`U(x)` is the open set `U(x) ∖ ⋃ᵢ ∂Mᵢ`, and `supp(∂Θ)` is saturated. -/
theorem isClosed_orbitSupp_boundaryTheta (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) (hcl : IsClosed (X.orbitSupp Θ)) :
    IsClosed (X.orbitSupp (X.boundaryTheta Θ)) := by
  classical
  have hfun := X.isFunctorial_boundaryTheta hΘ hind
  have hsupp : ∀ {a b : Obj}, X.π a = X.π b → a ∈ supp (X.boundaryTheta Θ) →
      b ∈ supp (X.boundaryTheta Θ) := fun {a b} hab ha => by
    obtain ⟨φ, rfl, rfl⟩ := X.π_eq_π_iff.1 hab
    change 0 < X.boundaryTheta Θ (X.tgt φ)
    rw [← hfun φ]
    exact ha
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro q hq
  obtain ⟨y, rfl⟩ := X.surjective_π q
  by_cases hy : X.π y ∈ X.orbitSupp Θ
  · obtain ⟨z, hz, hzy⟩ := hy
    have hyS : y ∈ supp Θ := by
      obtain ⟨φ, rfl, rfl⟩ := X.π_eq_π_iff.1 hzy
      change 0 < Θ (X.tgt φ)
      rw [← hΘ.isFunctorial φ]
      exact hz
    obtain ⟨B⟩ := hΘ.localBranching y hyS
    choose t ht hMt using B.exists_isClosed_eq_inter
    choose t' ht' hbt using fun i => exists_isClosed_submanifoldBoundary_eq (B.isSmoothSubmanifold i)
    have hmem : ∀ {w : Obj}, w ∈ B.U → ∀ i,
        (w ∈ X.PObj.submanifoldBoundary (B.M i) ↔ w ∈ t' i ∩ t i) := fun {w} hw i => by
      rw [hbt i, hMt i]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hw⟩⟩
    set W : Set Obj := B.U ∩ ⋂ i, (t' i ∩ t i)ᶜ with hW
    have hWo : IsOpen W := B.isOpen_U.inter
      (isOpen_iInter_of_finite fun i => ((ht' i).inter (ht i)).isOpen_compl)
    have hnot : ∀ {w : Obj}, w ∈ W → w ∉ supp (X.boundaryTheta Θ) := fun {w} hw hws => by
      have h1 : 0 < X.boundaryTheta Θ w := hws
      rw [X.boundaryTheta_eq hind B hw.1] at h1
      obtain ⟨i, hi⟩ := exists_mem_of_sum_pos h1
      exact mem_iInter.1 hw.2 i ((hmem hw.1 i).1 hi)
    have hyW : y ∈ W := by
      refine ⟨B.mem_U, mem_iInter.2 fun i hi => ?_⟩
      apply hq
      refine ⟨y, ?_, rfl⟩
      change 0 < X.boundaryTheta Θ y
      rw [X.boundaryTheta_eq hind B B.mem_U]
      exact Finset.sum_pos' (fun j _ => (B.σ_pos j).le)
        ⟨i, by simp [(hmem B.mem_U i).2 hi], B.σ_pos i⟩
    refine mem_of_superset ((X.proposition_7_1_8 _ hWo).mem_nhds ⟨y, hyW, rfl⟩) ?_
    rintro _ ⟨w, hw, rfl⟩ ⟨z, hz, hzw⟩
    exact hnot hw (hsupp hzw hz)
  · exact mem_of_superset (hcl.isOpen_compl.mem_nhds hy)
      (compl_subset_compl.2 orbitSupp_boundaryTheta_subset)

/-- **`∂Θ` is compact when `Θ` is** (`∂S ⊆ S` closed). -/
theorem isCompact_orbitSupp_boundaryTheta (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) (hS : X.IsCompactBranched Θ) :
    IsCompact (X.orbitSupp (X.boundaryTheta Θ)) :=
  hS.of_isClosed_subset (isClosed_orbitSupp_boundaryTheta hΘ hind hS.isClosed)
    orbitSupp_boundaryTheta_subset

/-- **Theorems 9.5.15 and 9.5.16 (2021 p. 449), from the local expressions**: let `Θ` be a tame,
compact branched ep⁺-subgroupoid (with the independence of Theorem 9.2.1, through which `∂Θ` is
defined), and let `loc x B : V → M(∂S, L(∂S))` be linear for every
`x ∈ supp(∂Θ)` and every tame branching structure `B` of `Θ` at `x` (the right-hand side of the
characterizing identity; `V` the space of forms), any two agreeing on the measurable subsets of
`∂S ∩ |U(x)| ∩ |U(x')|`.  Then there is exactly one linear map `Φ : V → M(∂S, L(∂S))` with
`Φ(ω)(K) = loc x B ω K` for all `x`, `B` and all `K ∈ L(∂S)` with `K ⊆ |U(x)|`. -/
theorem theorem_9_5_15_of_overlap
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hind : X.HasIndependentTangentSums Θ)
    (htame : X.IsTameBranched Θ) (hS : X.IsCompactBranched Θ)
    (loc : ∀ x, x ∈ supp (X.boundaryTheta Θ) → X.TameBranchingStructure Θ x →
      V →ₗ[ℝ] @SignedMeasure _ (X.lebesgueSigmaBoundary G' Θ))
    (hcompat : ∀ x hx B x' hx' B' ω (K : Set (X.orbitSupp (X.boundaryTheta Θ))),
      MeasurableSet[X.lebesgueSigmaBoundary G' Θ] K →
      Subtype.val '' K ⊆ X.π '' B.U ∩ X.π '' B'.U → loc x hx B ω K = loc x' hx' B' ω K) :
    ∃! Φ : V →ₗ[ℝ] @SignedMeasure _ (X.lebesgueSigmaBoundary G' Θ),
      ∀ x hx B ω (K : Set (X.orbitSupp (X.boundaryTheta Θ))),
        MeasurableSet[X.lebesgueSigmaBoundary G' Θ] K → Subtype.val '' K ⊆ X.π '' B.U →
          Φ ω K = loc x hx B ω K := by
  let _ := X.lebesgueSigmaBoundary G' Θ
  have : CompactSpace (X.orbitSupp (X.boundaryTheta Θ)) :=
    isCompact_iff_compactSpace.1 (isCompact_orbitSupp_boundaryTheta hΘ hind hS)
  have hne : ∀ x ∈ supp (X.boundaryTheta Θ), Nonempty (X.TameBranchingStructure Θ x) :=
    fun x hx => htame x (by
      by_contra h
      have h0 := X.boundaryTheta_eq_zero_of_not_mem_supp (Θ := Θ) h
      have h1 : 0 < X.boundaryTheta Θ x := hx
      rw [h0] at h1
      exact lt_irrefl _ h1)
  set J := Σ x : {x // x ∈ supp (X.boundaryTheta Θ)}, X.TameBranchingStructure Θ x.1
  set O : J → Set (X.orbitSupp (X.boundaryTheta Θ)) :=
    fun j => Subtype.val ⁻¹' (X.π '' j.2.U) with hOdef
  have hsub : ∀ (j : J) (K : Set (X.orbitSupp (X.boundaryTheta Θ))),
      K ⊆ O j ↔ Subtype.val '' K ⊆ X.π '' j.2.U := fun j K => image_subset_iff.symm
  have hO : ∀ j, IsOpen (O j) := fun j =>
    (X.proposition_7_1_8 _ j.2.isOpen_U).preimage continuous_subtype_val
  have hcov : ⋃ j, O j = univ := by
    refine eq_univ_of_univ_subset fun q _ => ?_
    obtain ⟨y, hy, hq⟩ := q.2
    obtain ⟨B⟩ := hne y hy
    exact mem_iUnion.2 ⟨⟨⟨y, hy⟩, B⟩, y, B.mem_U, hq⟩
  obtain ⟨Φ, hΦ, hΦu⟩ := existsUnique_linearMap_signedMeasure_of_openCover
    (borel_le_borelNullSigma _) O hO hcov (fun j => loc j.1.1 j.1.2 j.2)
    (fun j l ω K hK hKO => hcompat j.1.1 j.1.2 j.2 l.1.1 l.1.2 l.2 ω K hK (by
      rw [subset_inter_iff] at hKO ⊢
      exact ⟨(hsub j K).1 hKO.1, (hsub l K).1 hKO.2⟩))
  refine ⟨Φ, fun x hx B ω K hK hKU => hΦ ⟨⟨x, hx⟩, B⟩ ω K hK ((hsub ⟨⟨x, hx⟩, B⟩ K).2 hKU),
    fun Ψ hΨ => hΦu Ψ fun j ω K hK hKO => hΨ j.1.1 j.1.2 j.2 ω K hK ((hsub j K).1 hKO)⟩

end EpGroupoid

end Polyfold
