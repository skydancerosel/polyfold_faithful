import Polyfold.Chapter7.Basic
import Polyfold.Chapter4.Submanifolds
import Polyfold.Chapter6.PathCategory
import Polyfold.Chapter5.StrongBundleShift
import Polyfold.Chapter3.NonVacuity

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 9, "Branched Ep⁺-Subgroupoids", §9.1 "Basic Definitions" (pp. 291–294): **Definitions
9.1–9.3** and **Lemma 9.1**.  Numbers and pages are the 2017 text's.

# Branched ep⁺-subgroupoids

## The text, paraphrased

(p. 291, Remark 9.1) A finite-dimensional submanifold of an M-polyfold (Chapter 4) is locally an
sc⁺-retract; it inherits an M⁺-polyfold structure, called a (smooth) manifold; the dimension of
`T_m M` is locally constant, the local dimension of `M`.

(Definition 9.1, p. 292) A branched ep⁺-subgroupoid of the ep-groupoid `X` is a functor
`Θ : X → ℚ⁺` with (1) `supp(Θ) = {x | Θ(x) > 0} ⊆ X_∞`, and for every `x ∈ supp(Θ)`:
(2) an open `U(x)` and a finite family of submanifolds `Mᵢ ⊆ U(x)`, `i ∈ I`, with `x ∈ Mᵢ` and
the inclusions `Mᵢ → U(x)` proper; (3) weights `σᵢ ∈ ℚ`, `σᵢ > 0`; (4) `Θ(y) = ∑_{i : y ∈ Mᵢ} σᵢ`
for `y ∈ U(x)` (a local branching structure).  `Θ` is `n`-dimensional if all the `Mᵢ` are
`n`-dimensional, locally equidimensional if for small branching structures they have one
dimension.  (Remark 9.2, p. 292) Local branching structures are not unique (two graphs in `ℝ²`).

(Lemma 9.1, p. 293) `|supp(Θ)|` is locally closed in `|X|`.  *Proof* (text): take `U(x)` with
the natural `G_x`-action and the properness property carrying a local branching structure; for
`w ∈ |U(x)| ∩ cl |supp(Θ)|` with representative `y`, a sequence in `⋃ Mᵢ` converges to `y`
(`⋃ Mᵢ` is `G_x`-invariant), and the properness of `Mᵢ → U(x)` gives `y ∈ Mᵢ`.

(Definition 9.2, p. 293) `Θ` is closed (compact) if `|supp(Θ)|` is closed in (a compact subset
of) `|X|`.  (pp. 293–294) Restricting to `V ⊆ U(x)` gives `Nᵢ = Mᵢ ∩ V` (possibly empty);
averaging over `G_x` gives a symmetric representation (Lemma 9.2).  (Definition 9.3, p. 294)
`Θ` is of manifold-type if it takes only the values `0`, `1` and between objects of `supp(Θ)`
there is at most one morphism; of orbifold-type if it takes only the values `0`, `1`.

## What is formalized

* `EpGroupoid.IsFunctorial`, `EpGroupoid.supp`, `EpGroupoid.LocalBranchingStructure`,
  `EpGroupoid.IsBranchedEpSubgroupoid` (**Definition 9.1**).
* `EpGroupoid.orbitSupp` (`|supp(Θ)|`), `IsClosedBranched`, `IsCompactBranched`
  (**Definition 9.2**); `IsManifoldType`, `IsOrbifoldType` (**Definition 9.3**).
* `EpGroupoid.lemma_9_1` (**Lemma 9.1**), with `isLocallyClosed_supp` (`supp(Θ)` is locally
  closed in `X`) and `preimage_π_orbitSupp` (`supp(Θ)` is saturated).
* Witnesses: `isBranchedEpSubgroupoid_zero` (`Θ = 0`, any ep-groupoid);
  `isBranchedEpSubgroupoid_indicator` (the indicator of a point `p` of `ℝⁿ` in the trivial
  ep-groupoid of `ℝⁿ`, a nonempty support), which is compact (`isCompactBranched_indicator`) and
  of manifold-type (`isManifoldType_indicator`); `rnPolyfold_isSmoothSubmanifold_singleton`
  (a point of `ℝⁿ` is a submanifold in the sense of Definition 4.13 [4.4]).

## What the text leaves implicit, and the choices made

* `ℚ⁺` is read as `ℚ_{≥0}` (`Θ = 0` off the support): `Θ : X → ℚ` with the field `nonneg`.  A
  functor to `ℚ` (only identity morphisms) is a function with `Θ(s φ) = Θ(t φ)`.
* The submanifolds are Part I's smooth finite-dimensional submanifolds (Definition 4.13 [4.4],
  `MPolyfold.IsSmoothSubmanifold`) of `X` contained in the open `U(x)`; "the inclusion
  `Mᵢ → U(x)` is proper" is `IsProperMap (Set.inclusion _)`.  The index set is a `Fintype` in
  the universe of the objects; `x ∈ Mᵢ` for every `i`, as in (2).
* "`n`-dimensional" and "locally equidimensional" (and the local dimension of Remark 9.1) are
  not formalized: Part I has no dimension of a submanifold as the rank of its tangent spaces (the
  tangent fibres are sets in `TangentSpace`, without a vector space structure).
* Definitions 9.2 and 9.3 are conditions on any `Θ : X → ℚ`, to be applied to branched
  ep⁺-subgroupoids.  "At most one morphism between `x, y ∈ supp(Θ)`" is: two morphisms with the
  same source and target in `supp(Θ)` are equal.
* The proof of Lemma 9.1 replaces the natural representation and the sequence argument by:
  `supp(Θ) ∩ U(x) = ⋃ Mᵢ` (positive weights) is closed in `U(x)` (proper maps are closed), so
  `supp(Θ)` is locally closed in `X`; it is saturated (`Θ` a functor) and `π` is open
  (Proposition 7.1), so `π⁻¹` of the coborder of `|supp(Θ)|` is the coborder of `supp(Θ)`.
* In Definition 9.1 (4), "the data in (ii) and (iii)" refers to (2) and (3) (possible
  misprint); "see the next 9.1" on p. 291 refers to Remark 9.1.
* Not formalized here: Remark 9.2 (b) (graphs as submanifolds), the restriction remark and
  Lemma 9.2 (the symmetric representation; it needs that `g ∗ Mᵢ` and `Mᵢ ∩ V` are submanifolds,
  i.e. images of submanifolds under sc-diffeomorphisms and open pieces of submanifolds, which
  Part I does not state), Proposition 9.1 and Remark 9.3.
-/

open Set

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### Definition 9.1 -/

/-- A function `Θ : X → ℚ` on the objects is a **functor** to `ℚ` (a category with only identity
morphisms) if `Θ(s φ) = Θ(t φ)` for every morphism `φ`. -/
def IsFunctorial (Θ : Obj → ℚ) : Prop := ∀ φ : Mor, Θ (X.src φ) = Θ (X.tgt φ)

/-- The **support** `supp(Θ) = {x ∈ X | Θ(x) > 0}`. -/
def supp (Θ : Obj → ℚ) : Set Obj := {x | 0 < Θ x}

open scoped Classical in
/-- **Definition 9.1 (2)–(4) (local branching structure at `x`)**: an open neighbourhood
`U = U(x)`, a finite family `(Mᵢ)_{i ∈ I}` of smooth finite-dimensional submanifolds of `X`
(Definition 4.13 [4.4]) contained in `U` and passing through `x`, with the inclusions `Mᵢ → U`
proper, and weights `σᵢ ∈ ℚ`, `σᵢ > 0`, with `Θ(y) = ∑_{i ∈ I, y ∈ Mᵢ} σᵢ` for `y ∈ U`. -/
structure LocalBranchingStructure (Θ : Obj → ℚ) (x : Obj) where
  /-- The open neighbourhood `U(x)`. -/
  U : Set Obj
  isOpen_U : IsOpen U
  mem_U : x ∈ U
  /-- The finite index set `I`. -/
  ι : Type u
  [fintype : Fintype ι]
  /-- The submanifolds `Mᵢ`. -/
  M : ι → Set Obj
  subset_U : ∀ i, M i ⊆ U
  isSmoothSubmanifold : ∀ i, X.PObj.IsSmoothSubmanifold (M i)
  mem_M : ∀ i, x ∈ M i
  isProperMap : ∀ i, IsProperMap (Set.inclusion (subset_U i))
  /-- The weights `σᵢ`. -/
  σ : ι → ℚ
  σ_pos : ∀ i, 0 < σ i
  eq_sum : ∀ y ∈ U, Θ y = ∑ i with y ∈ M i, σ i

attribute [instance] LocalBranchingStructure.fintype

/-- **Definition 9.1 (branched ep⁺-subgroupoid)**: a functor `Θ : X → ℚ⁺` (`ℚ⁺ = ℚ_{≥ 0}`) with
(1) `supp(Θ) ⊆ X_∞`, and (2)–(4) a local branching structure at every point of `supp(Θ)`. -/
structure IsBranchedEpSubgroupoid (Θ : Obj → ℚ) : Prop where
  nonneg : ∀ x, 0 ≤ Θ x
  isFunctorial : X.IsFunctorial Θ
  support_subset : supp Θ ⊆ X.PObj.smoothSet
  localBranching : ∀ x ∈ supp Θ, Nonempty (X.LocalBranchingStructure Θ x)

/-! ### Definitions 9.2 and 9.3 -/

/-- The orbit space `|supp(Θ)| = π(supp(Θ)) ⊆ |X|` of the support. -/
def orbitSupp (Θ : Obj → ℚ) : Set X.OrbitSpace := X.π '' supp Θ

/-- **Definition 9.2 (1)**: the branched ep⁺-subgroupoid `Θ` is **closed** if `|supp(Θ)|` is
closed in `|X|`. -/
def IsClosedBranched (Θ : Obj → ℚ) : Prop := IsClosed (X.orbitSupp Θ)

/-- **Definition 9.2 (2)**: the branched ep⁺-subgroupoid `Θ` is **compact** if `|supp(Θ)|` is a
compact subset of `|X|`. -/
def IsCompactBranched (Θ : Obj → ℚ) : Prop := IsCompact (X.orbitSupp Θ)

/-- **Definition 9.3 (2)**: `Θ` is of **orbifold-type** if it only takes the values `0` and `1`. -/
def IsOrbifoldType (Θ : Obj → ℚ) : Prop := ∀ x, Θ x = 0 ∨ Θ x = 1

/-- **Definition 9.3 (1)**: `Θ` is of **manifold-type** if it only takes the values `0` and `1`
and between two objects of `supp(Θ)` there is at most one morphism. -/
def IsManifoldType (Θ : Obj → ℚ) : Prop :=
  IsOrbifoldType Θ ∧ ∀ φ ψ : Mor, X.src φ ∈ supp Θ → X.tgt φ ∈ supp Θ →
    X.src φ = X.src ψ → X.tgt φ = X.tgt ψ → φ = ψ

/-! ### Lemma 9.1 -/

variable {X} {Θ : Obj → ℚ}

/-- For a functor `Θ`, the support is saturated: `π⁻¹(|supp(Θ)|) = supp(Θ)`. -/
theorem preimage_π_orbitSupp (hΘ : X.IsFunctorial Θ) : X.π ⁻¹' X.orbitSupp Θ = supp Θ := by
  ext y
  constructor
  · rintro ⟨a, ha, hay⟩
    obtain ⟨φ, rfl, rfl⟩ := (X.π_eq_π_iff).1 hay
    change 0 < Θ (X.tgt φ)
    rw [← hΘ φ]
    exact ha
  · intro hy
    exact ⟨y, hy, rfl⟩

namespace LocalBranchingStructure

variable {x : Obj} (B : X.LocalBranchingStructure Θ x)
include B

/-- On `U(x)`, the support of `Θ` is the union of the submanifolds `Mᵢ` (the weights are
positive). -/
theorem mem_supp_iff {y : Obj} (hy : y ∈ B.U) : y ∈ supp Θ ↔ ∃ i, y ∈ B.M i := by
  change 0 < Θ y ↔ _
  rw [B.eq_sum y hy]
  constructor
  · intro h
    by_contra hne
    simp only [not_exists] at hne
    simp [hne] at h
  · rintro ⟨i, hi⟩
    exact Finset.sum_pos' (fun j _ => (B.σ_pos j).le) ⟨i, by simp [hi], B.σ_pos i⟩

/-- `supp(Θ) ∩ U(x)` is closed in `U(x)`: it is the finite union of the `Mᵢ`, closed in `U(x)`
since the inclusions `Mᵢ → U(x)` are proper. -/
theorem isClosed_preimage_val_supp : IsClosed ((↑) ⁻¹' supp Θ : Set B.U) := by
  have h : ((↑) ⁻¹' supp Θ : Set B.U) = ⋃ i, range (inclusion (B.subset_U i)) := by
    ext ⟨y, hy⟩
    simp only [mem_preimage, mem_iUnion, mem_range, B.mem_supp_iff hy]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, ⟨y, hi⟩, rfl⟩
    · rintro ⟨i, ⟨z, hz⟩, hzy⟩
      have h' : z = y := congrArg Subtype.val hzy
      exact ⟨i, h' ▸ hz⟩
  rw [h]
  exact isClosed_iUnion_of_finite fun i => (B.isProperMap i).isClosedMap.isClosed_range

end LocalBranchingStructure

/-- The support of a branched ep⁺-subgroupoid is locally closed in `X`. -/
theorem isLocallyClosed_supp (hΘ : X.IsBranchedEpSubgroupoid Θ) : IsLocallyClosed (supp Θ) := by
  refine ((isLocallyClosed_tfae (supp Θ)).out 0 2).2 fun x hx => ?_
  obtain ⟨B⟩ := hΘ.localBranching x hx
  exact ⟨B.U, B.isOpen_U.mem_nhds B.mem_U, B.isClosed_preimage_val_supp⟩

/-- **Lemma 9.1**: for a branched ep⁺-subgroupoid `Θ`, `|supp(Θ)|` is locally closed in `|X|`.
(Proof: `supp(Θ)` is locally closed in `X` and saturated, and `π` is open, Proposition 7.1.) -/
theorem lemma_9_1 (hΘ : X.IsBranchedEpSubgroupoid Θ) : IsLocallyClosed (X.orbitSupp Θ) := by
  rw [isLocallyClosed_iff_isOpen_coborder]
  refine isQuotientMap_quotient_mk'.isOpen_preimage.1 ?_
  change IsOpen (X.π ⁻¹' coborder (X.orbitSupp Θ))
  rw [← coborder_preimage X.proposition_7_1 X.continuous_π, preimage_π_orbitSupp hΘ.isFunctorial]
  exact (isLocallyClosed_supp hΘ).isOpen_coborder

variable (X)

/-! ### Witnesses for Definition 9.1 -/

/-- The zero functor `Θ = 0` is a branched ep⁺-subgroupoid of every ep-groupoid (empty support). -/
theorem isBranchedEpSubgroupoid_zero : X.IsBranchedEpSubgroupoid 0 where
  nonneg _ := le_rfl
  isFunctorial _ := rfl
  support_subset _ hx := (lt_irrefl (0 : ℚ) hx).elim
  localBranching _ hx := (lt_irrefl (0 : ℚ) hx).elim

end EpGroupoid

/-- A point of `ℝⁿ` is a smooth finite-dimensional submanifold of the M-polyfold `ℝⁿ`
(Definition 4.13 [4.4]): the constant map `s = p` is an sc⁺-retraction of `V = ℝⁿ` onto `{p}`. -/
theorem rnPolyfold_isSmoothSubmanifold_singleton (n : ℕ) (p : Fin n → ℝ) :
    (rnPolyfold n).IsSmoothSubmanifold {p} := by
  have hp : p ∈ (rnPolyfold n).smoothSet := by
    rw [TrivialBundle.rnPolyfold_smoothSet]; exact mem_univ p
  have hp1 : p ∈ (rnPolyfold n).levelSet 1 :=
    MPolyfold.smoothSet_subset_levelSet (P := rnPolyfold n) 1 hp
  intro a _
  refine ⟨univ, isOpen_univ, mem_univ a, fun _ => p,
    ⟨isScSmoothMap_const_of_mem_smoothSet hp, fun _ _ => mem_univ _, fun _ _ => rfl,
      fun _ _ => hp1, fun x₀ => ?_⟩, ?_⟩
  · refine isScSmoothMap_const_of_mem_smoothSet
      ((MPolyfold.mem_shift_smoothSet_iff ((rnPolyfold n).toLevelOne x₀ p)).2 ?_)
    rw [MPolyfold.levelVal_toLevelOne x₀ hp1]
    exact hp
  · ext y
    simp [eq_comm]

namespace EpGroupoid

/-- The local branching structure of the indicator of a point `p` of `ℝⁿ` in the trivial
ep-groupoid of `ℝⁿ`: `U = ℝⁿ`, one submanifold `M = {p}` with weight `1`. -/
def localBranchingStructure_indicator (n : ℕ) (p : Fin n → ℝ) :
    (trivial (rnPolyfold n)).LocalBranchingStructure (({p} : Set (Fin n → ℝ)).indicator 1) p where
  U := univ
  isOpen_U := isOpen_univ
  mem_U := mem_univ p
  ι := Unit
  M _ := {p}
  subset_U _ := subset_univ _
  isSmoothSubmanifold _ := rnPolyfold_isSmoothSubmanifold_singleton n p
  mem_M _ := rfl
  isProperMap _ := (continuous_inclusion _).isProperMap
  σ _ := 1
  σ_pos _ := one_pos
  eq_sum y _ := by
    by_cases hy : y = p
    · subst hy; simp
    · simp [hy]

/-- **Satisfiability of Definition 9.1 with nonempty support**: the indicator of a point `p` of
`ℝⁿ` is a branched ep⁺-subgroupoid of the trivial ep-groupoid of `ℝⁿ`. -/
theorem isBranchedEpSubgroupoid_indicator (n : ℕ) (p : Fin n → ℝ) :
    (trivial (rnPolyfold n)).IsBranchedEpSubgroupoid (({p} : Set (Fin n → ℝ)).indicator 1) where
  nonneg y := by
    by_cases hy : y = p
    · subst hy; simp
    · simp [hy]
  isFunctorial _ := rfl
  support_subset y _ := by
    change y ∈ (rnPolyfold n).smoothSet
    rw [TrivialBundle.rnPolyfold_smoothSet]; exact mem_univ y
  localBranching y hy := by
    have hyp : y = p := by
      by_contra h
      have : ¬ (0 < (({p} : Set (Fin n → ℝ)).indicator 1 y : ℚ)) := by simp [h]
      exact this hy
    subst hyp
    exact ⟨localBranchingStructure_indicator n y⟩

/-- `supp` of the indicator of `p` is `{p}`. -/
theorem supp_indicator_singleton (n : ℕ) (p : Fin n → ℝ) :
    supp (({p} : Set (Fin n → ℝ)).indicator (1 : (Fin n → ℝ) → ℚ)) = {p} := by
  ext y
  by_cases hy : y = p
  · subst hy; simp [supp]
  · simp [supp, hy]

/-- The indicator of a point of `ℝⁿ` is compact (Definition 9.2): `|supp| = {π(p)}`. -/
theorem isCompactBranched_indicator (n : ℕ) (p : Fin n → ℝ) :
    (trivial (rnPolyfold n)).IsCompactBranched (({p} : Set (Fin n → ℝ)).indicator 1) := by
  unfold IsCompactBranched orbitSupp
  rw [supp_indicator_singleton]
  exact isCompact_singleton.image (trivial (rnPolyfold n)).continuous_π

/-- The indicator of a point of `ℝⁿ` is of manifold-type (Definition 9.3): it takes the values
`0`, `1`, and the morphisms of the trivial ep-groupoid are identities. -/
theorem isManifoldType_indicator (n : ℕ) (p : Fin n → ℝ) :
    (trivial (rnPolyfold n)).IsManifoldType (({p} : Set (Fin n → ℝ)).indicator 1) := by
  refine ⟨fun y => ?_, fun φ ψ _ _ h _ => h⟩
  by_cases hy : y = p
  · subst hy; simp
  · simp [hy]

end EpGroupoid

end Polyfold
