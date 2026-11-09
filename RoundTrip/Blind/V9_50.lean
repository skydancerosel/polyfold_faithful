import Polyfold
/-! Blind formalization of V9_50 (the Springer 2021 book, Part II, §9.5, Lemma 9.5.2, p. 437;
2017: Lemma 9.16, p. 322): measure zero in `S = |supp(Θ)|` does not depend on the choice of the
local branching structures.

Text: the notion of a set of measure zero in `S` (Definition 9.5.1: `K ⊆ S` has measure zero if
for every `x ∈ supp(Θ)` and a choice of local branching structure `(Mᵢ)`, `(σᵢ)` on a suitable
`U(x)`, the preimages `Kᵢ` of `K` under the canonical maps `Mᵢ → |M_U| ⊆ S` have measure zero in
`Mᵢ`) does not depend on the choice of the local branching structures.  Cited, no proof.

Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files), the project's ep-groupoid
  `X : EpGroupoid Obj Mor`, `Θ : Obj → ℚ` with the standing assumptions of §9.5 as I read them:
  `Θ` a branched ep⁺-subgroupoid (project's `IsBranchedEpSubgroupoid`, compared with the text in
  `RoundTrip/Blind/V9_1.lean`), `n`-dimensional (project's `IsNDimensional`, compared in
  `RoundTrip/Blind/V9_2.lean`; §9.5 integrates `n`-forms and Definition 9.5.1 measures the
  `n`-dimensional sheets), and tame (my `IsTameB`, Definition 9.3.6).  A tameness hypothesis on
  `X` itself is not added (not needed for the notion, and I do not know that the text has it).
- "a local branching structure on a suitable `U(x)`": a project `LocalBranchingStructure Θ x`
  (`#print`ed: open `U ∋ x`, finite family of smooth finite-dimensional submanifolds `Mᵢ ⊆ U`
  through `x` with proper inclusions, weights `σᵢ > 0`, `Θ(y) = ∑_{y ∈ Mᵢ} σᵢ` on `U`) whose
  `U(x)` carries the natural `G_x`-action, is connected (the text's `U(x)` of Theorem 7.1.13 is
  connected, as recorded in `RoundTrip/Blind/V7_37.lean`), has the properness property, and whose
  `Mᵢ` have tame induced structures: my `IsSuitableB`, i.e. the data of Definition 9.3.6 as in
  `RoundTrip/Blind/V9_34.lean` (its `IsNatAction` copied, plus connectedness).
- "the preimages `Kᵢ` under `Mᵢ → |M_U| ⊆ S`": `Kᵢ = Mᵢ ∩ π⁻¹(K)`, `π : X → |X|` the project's
  orbit map; `K ⊆ S = π(supp Θ)` (project's `orbitSupp`).
- "measure zero in `Mᵢ`" (Definition 9.4.5: `ϕ(U ∩ K)` Lebesgue-null for every chart `ϕ` of the
  manifold `Mᵢ`): the project's vocabulary has no manifold charts on the sheets (its
  `SheetNullSets` is an abstract system of null sets with axioms, so it does not express the
  text's notion and I did not use it).  My `IsLocNullB P n A`: every point of `A` has an open
  `V` such that every chart `φ` of the M-polyfold maps `A ∩ V` to a set of `n`-dimensional
  Hausdorff (outer) measure zero in the level-0 Banach space `E₀` of the chart (Mathlib's
  `OuterMeasure.mkMetric (r ↦ r^n)`).  Reason: in a chart an `n`-dimensional sheet is a smooth
  embedded `n`-dimensional submanifold of `E₀` (Part I), locally bi-Lipschitz to its manifold
  charts, so on a small `V` the `n`-dimensional Hausdorff null sets are exactly the Lebesgue null
  sets of the charts of `Mᵢ`; the localisation avoids non-separable pieces, where a Hausdorff
  measure would see uncountably many components at once.  The statement "`Kᵢ` has measure zero in
  `Mᵢ`" is `IsLocNullB X.PObj n (Mᵢ ∩ π⁻¹(K))`.
- "does not depend on the choice": the definition fixes one suitable structure per point; I state
  that if one choice (some suitable structure at every `x ∈ supp Θ`) has null preimages, then
  every suitable structure at every `x ∈ supp Θ` has (this is equivalent to "any two choices give
  the same notion", suitable structures existing at every point since `Θ` is tame).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_50
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The natural `G_x`-action on the open neighbourhood `U` of `x` (the data `Φ`, `Γ` of
Theorem 7.1), as in `RoundTrip/Blind/V7_21.lean` and `RoundTrip/Blind/V9_34.lean`. -/
structure IsNatAction (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj)
    (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor) : Prop where
  isOpen : IsOpen U
  mem : x ∈ U
  diffeo : ∀ g, ∃ ψ : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj (Φ g) ψ U U
  hom : ∀ g h, ∀ y ∈ U, Φ (g * h) y = Φ g (Φ h y)
  smooth : ∀ g, X.PObj.IsScSmoothOn X.PMor (Γ g) U
  Γ_x : ∀ g, Γ g x = g.val
  src_tgt : ∀ g, ∀ y ∈ U, X.src (Γ g y) = y ∧ X.tgt (Γ g y) = Φ g y
  unique : ∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃! g, Γ g (X.src h) = h

/-- A local branching structure on a **suitable** `U(x)` (the data of Definition 9.3.6): `U(x)`
connected, with the natural `G_x`-action and the properness property, the `Mᵢ` with tame induced
structures. -/
def IsSuitableB (X : EpGroupoid Obj Mor) {Θ : Obj → ℚ} {x : Obj}
    (B : X.LocalBranchingStructure Θ x) : Prop :=
  (∃ (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor), IsNatAction X x B.U Φ Γ) ∧
  IsConnected B.U ∧ X.HasPropernessProperty B.U ∧ ∀ i, X.PObj.HasTameInducedStructure (B.M i)

/-- **Definition 9.3.6**: `Θ` is tame. -/
def IsTameB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) : Prop :=
  ∀ x ∈ EpGroupoid.supp Θ, ∃ B : X.LocalBranchingStructure Θ x, IsSuitableB X B

end

section
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]

/-- `A` has `d`-dimensional measure zero, read in the charts of the M-polyfold: every point of
`A` has an open `V` such that every chart `φ` maps `A ∩ V` to a set of `d`-dimensional Hausdorff
measure zero in `E₀`. -/
def IsLocNullB (P : MPolyfold Z) (d : ℕ) (A : Set Z) : Prop :=
  ∀ z ∈ A, ∃ V : Set Z, IsOpen V ∧ z ∈ V ∧ ∀ φ : MChart Z, P.IsChart φ →
    MeasureTheory.OuterMeasure.mkMetric (fun r : ENNReal => r ^ (d : ℝ))
      (φ.toPartialEquiv '' (A ∩ V ∩ φ.toPartialEquiv.source)) = 0

end

/-- The preimages `Kᵢ = Mᵢ ∩ π⁻¹(K)` of `K ⊆ |X|` have measure zero in the `n`-dimensional
sheets `Mᵢ` of `B`. -/
def NullPreimagesB {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor) (n : ℕ)
    {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x) (K : Set X.OrbitSpace) : Prop :=
  ∀ i, IsLocNullB X.PObj n (B.M i ∩ X.π ⁻¹' K)

/-- **Lemma 9.5.2**: if `K ⊆ S` has null preimages for one choice of suitable local branching
structures at the points of `supp(Θ)`, it has them for every suitable structure at every point. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (n : ℕ),
    X.IsBranchedEpSubgroupoid Θ → IsTameB X Θ → X.IsNDimensional Θ n →
    ∀ K : Set X.OrbitSpace, K ⊆ X.orbitSupp Θ →
      (∀ x ∈ EpGroupoid.supp Θ, ∃ B : X.LocalBranchingStructure Θ x,
        IsSuitableB X B ∧ NullPreimagesB X n B K) →
      ∀ x ∈ EpGroupoid.supp Θ, ∀ B : X.LocalBranchingStructure Θ x,
        IsSuitableB X B → NullPreimagesB X n B K

end RoundTrip.V9_50
