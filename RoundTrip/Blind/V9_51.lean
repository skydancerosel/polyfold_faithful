import Polyfold
/-! Blind formalization of V9_51 (the Springer 2021 book, Part II, §9.5, Definition 9.5.3,
p. 438, and the remark after it; 2017: Definition 9.16, p. 323): the σ-algebra `L(S)`.

Text: `L(S)` is the smallest σ-algebra on `S = |supp(Θ)|` containing the Borel σ-algebra
`B(S)` and all subsets of measure zero; it is obtained from `B(S)` by adding the sets of measure
zero.

Choices:
- Setting and the notion "measure zero in `S`" as in my `RoundTrip/Blind/V9_50.lean` (prelude
  copied: `Θ` a branched, `n`-dimensional, tame ep⁺-subgroupoid of the project's ep-groupoid `X`;
  suitable local branching structures `IsSuitableB`; null sets in a sheet `IsLocNullB`, read as
  locally `n`-dimensional Hausdorff-null in the charts of the object M-polyfold).  `K ⊆ S` has
  measure zero (Definition 9.5.1, my `IsNullSB`): every `x ∈ supp Θ` has a suitable local
  branching structure whose preimages `Mᵢ ∩ π⁻¹(K)` are null in the `Mᵢ` (one choice per point;
  by Lemma 9.5.2 the choice does not matter).  I did not use the project's `lebesgueSigma` /
  `measureZeroSets`: they are built on the abstract `SheetNullSets`, which does not express
  Definition 9.4.5.
- `S`: the subspace `π(supp Θ) ⊆ |X|` (project's `orbitSupp`, with the subspace topology of the
  quotient topology of `|X|`); subsets of `S` are `Set ↥S`, a subset `A` has measure zero if its
  image in `|X|` does.  `B(S)`: Mathlib's `borel ↥S`.  `L(S)` (my `LSB`): Mathlib's
  `MeasurableSpace.generateFrom` of the Borel sets and the null sets.
- The definition itself carries no claim; B is the remark: "obtained from `B(S)` by adding the
  sets of measure zero", read as: a subset of `S` lies in `L(S)` iff it differs from a Borel set
  by a set of measure zero, `L = A ∆ N` with `A` Borel and `N` null.  (The other reading
  `L = A ∪ N` agrees with it as soon as every null set lies in a Borel null set; the symmetric
  difference form needs only that the null sets form a σ-ideal, which the remark presupposes.)
- Nothing looks false to me.
-/
namespace RoundTrip.V9_51
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

/-- **Definition 9.5.1**: `K ⊆ |X|` has measure zero (for `K ⊆ S`): one suitable local branching
structure at every `x ∈ supp(Θ)` has null preimages. -/
def IsNullSB {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Θ : Obj → ℚ) (n : ℕ) (K : Set X.OrbitSpace) : Prop :=
  ∀ x ∈ EpGroupoid.supp Θ, ∃ B : X.LocalBranchingStructure Θ x,
    IsSuitableB X B ∧ NullPreimagesB X n B K

/-- **Definition 9.5.3**: `L(S)`, the σ-algebra on `S` generated by the Borel sets and the sets of
measure zero. -/
def LSB {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Θ : Obj → ℚ) (n : ℕ) : MeasurableSpace ↥(X.orbitSupp Θ) :=
  MeasurableSpace.generateFrom
    ({A | @MeasurableSet _ (borel ↥(X.orbitSupp Θ)) A} ∪
      {A | IsNullSB X Θ n (Subtype.val '' A)})

/-- **The remark after Definition 9.5.3**: `L(S)` is obtained from `B(S)` by adding the sets of
measure zero: its members are the sets `A ∆ N`, `A` Borel, `N` of measure zero. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (n : ℕ),
    X.IsBranchedEpSubgroupoid Θ → IsTameB X Θ → X.IsNDimensional Θ n →
    ∀ L : Set ↥(X.orbitSupp Θ),
      @MeasurableSet _ (LSB X Θ n) L ↔
        ∃ A N : Set ↥(X.orbitSupp Θ), @MeasurableSet _ (borel ↥(X.orbitSupp Θ)) A ∧
          IsNullSB X Θ n (Subtype.val '' N) ∧ L = symmDiff A N

end RoundTrip.V9_51
