import Polyfold
/-! Blind formalization of V9_52 (the Springer 2021 book, Part II, §9.5, Definition 9.5.14,
p. 448, with the paragraph before it; 2017: Definition 9.17, p. 327): measure zero in
`∂S = |supp(∂Θ)|` and the σ-algebra `L(∂S)`.

Text: for `K ⊆ |∂M_U|` the preimages lie in the `∂Mᵢ`, where `(n-1)`-dimensional measure zero
makes sense in the faces; this gives a well-defined notion of measure zero in
`∂S = |supp(∂Θ)|`, and `L(∂S)` is the smallest σ-algebra containing `B(∂S)` and the subsets of
measure zero.

Choices:
- Setting as in my `RoundTrip/Blind/V9_50.lean` (prelude copied): the project's ep-groupoid `X`,
  `Θ` a branched (project's `IsBranchedEpSubgroupoid`), `n`-dimensional (project's
  `IsNDimensional`), tame (my `IsTameB`) ep⁺-subgroupoid; suitable local branching structures
  (`IsSuitableB`: the data of Definition 9.3.6 on a connected `U(x)`).
- `∂Θ`: the project's `X.boundaryTheta Θ` (Definition 9.2.16; compared with the text in
  `RoundTrip/Blind/V9_27.lean`); `∂S = π(supp ∂Θ)` (project's `orbitSupp`).  `∂Mᵢ`: the project's
  `MPolyfold.submanifoldBoundary` (`#print`ed in `RoundTrip/Blind/V9_26.lean`: the `y ∈ Mᵢ` with
  `d_{Mᵢ}(y) ≥ 1`).  `|∂M_U| = π(⋃ᵢ ∂Mᵢ)`.
- "the preimages lie in the `∂Mᵢ`" (part (a) of B): for a suitable structure at `x ∈ supp Θ`,
  `K ⊆ |∂M_U|` and `y ∈ M_U = ⋃ Mᵢ` with `π(y) ∈ K`, `y` lies in some `∂Mᵢ`.  (Read with the
  union; `y ∈ Mᵢ ∩ π⁻¹(K)` need not lie in that same `∂Mᵢ`.)  The preimages used for the measure
  are then `Kᵢ = ∂Mᵢ ∩ π⁻¹(K)`.
- "`(n-1)`-dimensional measure zero in the faces": `∂Mᵢ` is the union of the faces of the
  `n`-manifold with corners `Mᵢ`, `(n-1)`-dimensional manifolds with corners; measure zero in every
  face is, as in V9_50, locally `(n-1)`-dimensional Hausdorff-null in the charts of the object
  M-polyfold (`IsLocNullB X.PObj (n - 1)`; the lower strata are `(n-1)`-null anyway).  For `n = 0`
  (`n - 1 = 0` in `ℕ`) the `∂Mᵢ` are empty and nothing is claimed.
- "a well-defined notion of measure zero in `∂S`" (part (b)): `K ⊆ ∂S` has measure zero if at
  every `x ∈ supp(∂Θ)` a chosen suitable structure has null `Kᵢ`; well defined: if one choice has
  null `Kᵢ`, every suitable structure at every `x ∈ supp(∂Θ)` has (as for Lemma 9.5.2 in V9_50).
- `L(∂S)` (my `LdSB`: Mathlib's `generateFrom` of `borel ↥∂S` and the null sets) is a definition
  with no claim of its own; it is recorded but not part of B.  The project's
  `lebesgueSigmaBoundary` is built on the abstract `SheetNullSets` and not used.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_52
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

/-- `Kᵢ = ∂Mᵢ ∩ π⁻¹(K)` has `(n-1)`-dimensional measure zero for every sheet `Mᵢ` of `B`. -/
def NullBdPreimagesB {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (n : ℕ) {Θ : Obj → ℚ} {x : Obj}
    (B : X.LocalBranchingStructure Θ x) (K : Set X.OrbitSpace) : Prop :=
  ∀ i, IsLocNullB X.PObj (n - 1) (X.PObj.submanifoldBoundary (B.M i) ∩ X.π ⁻¹' K)

/-- **Measure zero in `∂S`** (with one choice of suitable structures at the points of
`supp(∂Θ)`). -/
def IsNullBdB {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Θ : Obj → ℚ) (n : ℕ) (K : Set X.OrbitSpace) : Prop :=
  ∀ x ∈ EpGroupoid.supp (X.boundaryTheta Θ), ∃ B : X.LocalBranchingStructure Θ x,
    IsSuitableB X B ∧ NullBdPreimagesB X n B K

/-- **Definition 9.5.14** (recorded, not part of `B`): `L(∂S)`, generated by the Borel sets of
`∂S` and its subsets of measure zero. -/
def LdSB {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Θ : Obj → ℚ) (n : ℕ) : MeasurableSpace ↥(X.orbitSupp (X.boundaryTheta Θ)) :=
  MeasurableSpace.generateFrom
    ({A | @MeasurableSet _ (borel ↥(X.orbitSupp (X.boundaryTheta Θ))) A} ∪
      {A | IsNullBdB X Θ n (Subtype.val '' A)})

/-- **Measure zero in `∂S`**: (a) the preimages of `K ⊆ |∂M_U|` in `M_U` lie in the `∂Mᵢ`;
(b) the `(n-1)`-dimensional null condition on the `Kᵢ = ∂Mᵢ ∩ π⁻¹(K)` does not depend on the
choice of the suitable local branching structures. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (n : ℕ),
    X.IsBranchedEpSubgroupoid Θ → IsTameB X Θ → X.IsNDimensional Θ n →
    -- (a)
    (∀ x ∈ EpGroupoid.supp Θ, ∀ B : X.LocalBranchingStructure Θ x, IsSuitableB X B →
      ∀ K : Set X.OrbitSpace, K ⊆ X.π '' (⋃ i, X.PObj.submanifoldBoundary (B.M i)) →
        ∀ y ∈ ⋃ i, B.M i, X.π y ∈ K → ∃ i, y ∈ X.PObj.submanifoldBoundary (B.M i)) ∧
    -- (b)
    (∀ K : Set X.OrbitSpace, K ⊆ X.orbitSupp (X.boundaryTheta Θ) →
      IsNullBdB X Θ n K →
      ∀ x ∈ EpGroupoid.supp (X.boundaryTheta Θ), ∀ B : X.LocalBranchingStructure Θ x,
        IsSuitableB X B → NullBdPreimagesB X n B K)

end RoundTrip.V9_52
