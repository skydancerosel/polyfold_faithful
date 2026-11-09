import Polyfold
/-! Blind formalization of V9_5 (the Springer 2021 book, Part II, §9.1, Lemma 9.1.5, p. 403;
2017: Lemma 9.1, p. 293): `|supp(Θ)|` is locally closed.

Text: for a branched ep⁺-subgroupoid `Θ`, `|supp(Θ)|` is locally closed in `|X|`.

Choices:
- Setting: `Obj Mor : Type` (universe 0) with the project's `X : EpGroupoid Obj Mor`, as in
  `RoundTrip/Blind/V7_*.lean`.
- "branched ep⁺-subgroupoid": my `IsBranchedB` (Definition 9.1.2, copied from my
  `RoundTrip/Blind/V9_1.lean`, where its choices are recorded: `Θ : Obj → ℚ`, `Θ ≥ 0`, constant
  along morphisms, support in `X_∞` with paracompact image in `|X|`, local branching structures
  with submanifolds of Part I's Definition 4.13 and proper inclusions read as "compact sets have
  compact preimages").
- `|supp(Θ)| = π(supp Θ)` in `|X|` = the project's `X.OrbitSpace` with Mathlib's quotient
  topology.  "Locally closed": Mathlib's `IsLocallyClosed` (the intersection of an open and a
  closed set; equivalent to "every point has a neighbourhood `V` with `V ∩ S` closed in `V`").
- Nothing looks false to me.
-/
namespace RoundTrip.V9_5
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

/-- Lemma 9.1.5: for a branched ep⁺-subgroupoid `Θ`, `|supp(Θ)|` is locally closed in `|X|`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ),
    IsBranchedB X Θ → IsLocallyClosed (X.π '' suppB Θ)

end RoundTrip.V9_5
