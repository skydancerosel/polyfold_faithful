import Polyfold
/-! Blind formalization of V9_1 (the Springer 2021 book, Part II, §9.1, Definition 9.1.2, p. 402;
2017: Definition 9.1, p. 292): branched ep⁺-subgroupoids.

Text: a branched ep⁺-subgroupoid of the ep-groupoid `X` is a functor `Θ : X → ℚ⁺` with
(1) `supp(Θ) = {Θ > 0}` contained in `X_∞` and `|supp(Θ)|` paracompact in the topology induced
from `|X|`; and, at every `x ∈ supp(Θ)`, (2) an open `U(x)` and finitely many submanifolds
`Mᵢ ⊆ U(x)` through `x` with proper inclusions, (3) weights `σᵢ ∈ ℚ`, `σᵢ > 0`, and
(4) `Θ(y) = ∑_{y ∈ Mᵢ} σᵢ` for `y ∈ U(x)`: a local branching structure.

Choices:
- This item is a definition.  B says that the project's `X.IsBranchedEpSubgroupoid Θ` is my
  `IsBranchedB X Θ`, for every ep-groupoid and every `Θ : Obj → ℚ`.
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files) with the instances the
  project's `EpGroupoid` asks for, `X : EpGroupoid Obj Mor` (Definition 7.1.3 [2017: 7.3]; the
  project's structure, as in `RoundTrip/Blind/V7_*.lean`).
- `Θ : X → ℚ⁺`: a function `Θ : Obj → ℚ` with `0 ≤ Θ` (`ℚ⁺ = ℚ ∩ [0, ∞)`, so that `Θ = 0` is
  possible off the support).  "Functor" (`ℚ⁺` a category with identity morphisms only): `Θ` is
  constant along morphisms, `Θ(s φ) = Θ(t φ)`.
- `X_∞`: the project's `X.PObj.smoothSet` (compared with `⋂ X_m` in `RoundTrip/Blind/V7_6.lean`).
- `|supp Θ| = π(supp Θ) ⊆ |X|`, `|X|` the project's `X.OrbitSpace` with its quotient topology
  (Mathlib's instance, `#synth`ed: `instTopologicalSpaceQuotient`); "paracompact in the induced
  topology": `ParacompactSpace` of the subtype.
- "submanifolds": smooth finite-dimensional submanifolds of the object M-polyfold in the sense of
  Part I (Definition 4.13 of the preprint: locally the image of an sc⁺-retraction), the project's
  `X.PObj.IsSmoothSubmanifold` (`#print`ed; compared with the text in
  `RoundTrip/Blind/V4_29.lean`).
- "finitely many": an index type `ι : Type` with `Fintype ι` (possibly empty; at a point of the
  support it is not, by (4)).  "through `x`": `x ∈ Mᵢ`.
- "proper inclusions `Mᵢ → U(x)`": I read "proper" in the classical sense, preimages of compact
  sets are compact: every compact `K ⊆ U(x)` meets `Mᵢ` in a compact set (`IsProperInclB`).  The
  project uses Mathlib's (Bourbaki) `IsProperMap` of `Set.inclusion`; the two agree here because
  `U(x)` is metrizable (compactly generated), but that is to be proved, not assumed.
- (4) is asked for every `y ∈ U(x)` (the sum over the `i` with `y ∈ Mᵢ`, a `Finset` sum).
- Nothing in the definition looks false to me.
-/
namespace RoundTrip.V9_1
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `supp(Θ) = {x | Θ(x) > 0}`. -/
def suppB (Θ : Obj → ℚ) : Set Obj := {x | 0 < Θ x}

/-- The inclusion `A → U` is proper: preimages of compact subsets of `U` are compact. -/
def IsProperInclB (A U : Set Obj) : Prop :=
  ∀ K : Set Obj, K ⊆ U → IsCompact K → IsCompact (K ∩ A)

open Classical in
/-- **Definition 9.1.2 (2)–(4)**: `(U, (Mᵢ)_{i ∈ ι}, (σᵢ)_{i ∈ ι})` is a local branching structure
of `Θ` at `x`. -/
def IsLBSB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (x : Obj) {ι : Type} [Fintype ι]
    (U : Set Obj) (M : ι → Set Obj) (σ : ι → ℚ) : Prop :=
  IsOpen U ∧ x ∈ U ∧
  (∀ i, M i ⊆ U ∧ X.PObj.IsSmoothSubmanifold (M i) ∧ x ∈ M i ∧ IsProperInclB (M i) U) ∧
  (∀ i, 0 < σ i) ∧
  ∀ y ∈ U, Θ y = ∑ i with y ∈ M i, σ i

/-- **Definition 9.1.2**: `Θ` is a branched ep⁺-subgroupoid of `X`. -/
def IsBranchedB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) : Prop :=
  -- `Θ : X → ℚ⁺` is a functor
  (∀ x, 0 ≤ Θ x) ∧ (∀ φ : Mor, Θ (X.src φ) = Θ (X.tgt φ)) ∧
  -- (1)
  suppB Θ ⊆ X.PObj.smoothSet ∧ ParacompactSpace ↥(X.π '' suppB Θ) ∧
  -- (2)–(4) at every point of the support
  ∀ x ∈ suppB Θ, ∃ (ι : Type) (_ : Fintype ι) (U : Set Obj) (M : ι → Set Obj) (σ : ι → ℚ),
    IsLBSB X Θ x U M σ

end

/-- Definition 9.1.2: the project's branched ep⁺-subgroupoids are the text's. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ),
    X.IsBranchedEpSubgroupoid Θ ↔ IsBranchedB X Θ

end RoundTrip.V9_1
