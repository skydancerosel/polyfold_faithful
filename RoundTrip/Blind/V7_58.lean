import Polyfold
/-! Blind formalization of V7_58 (the 2017 book's Part II, §7.4, Theorem 7.4, p. 251, proved as
Theorem 7.6, pp. 255–256).

Text: let `X` be an ep-groupoid with paracompact orbit space `|X|` whose object M-polyfold `X`
admits sc-smooth partitions of unity.  Then every open cover of `X` by saturated open subsets
`(U_λ)_{λ ∈ Λ}` has a subordinate sc-smooth partition of unity of the ep-groupoid `X` (in the
sense of Definition 7.16).

Choices:
- Setting as in `RoundTrip/Blind/V7_49.lean`: `Obj Mor : Type` (universe 0) with the instances
  of the project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (the project's ep-groupoid,
  Definition 7.3, fields read with `#print`).
- "with paracompact orbit space": the project's `X.HasParacompactOrbitSpace` (checked with
  `#print`: Mathlib's `ParacompactSpace X.OrbitSpace`; see `RoundTrip/Blind/V7_53.lean`).
- "the object M-polyfold `X` admits sc-smooth partitions of unity" (Definition 5.28): the
  project's `X.PObj.AdmitsScPartitionsOfUnity` (checked with `#print`: every open cover indexed by
  a type in `Obj`'s universe has a subordinate Mathlib `PartitionOfUnity` of sc-smooth functions
  `X → ℝ`; stated equal to the text's notion in `RoundTrip/Blind/V5_47.lean`).
- The conclusion, written with my own reading of Definition 7.16 (`HasScPUB`, copied from
  `RoundTrip/Blind/V7_56.lean`): for every family `U : Λ → Set Obj` (`Λ : Type`) of open
  saturated (`U = π⁻¹(π(U))`) sets covering `Obj` there is a Mathlib `PartitionOfUnity Λ Obj`,
  subordinate (`tsupport β_λ ⊆ U_λ`), of sc-smooth functions (`IsScSmoothMap realPolyfold`), with
  (1) every `x` having a saturated open neighbourhood meeting only finitely many `supp β_λ`, and
  (2) `β_λ(z) = β_λ(y)` for isomorphic `y, z`.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_58
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `U ⊆ X` is saturated: `U = π⁻¹(π(U))`. -/
def IsSatB (X : EpGroupoid Obj Mor) (U : Set Obj) : Prop :=
  X.π ⁻¹' (X.π '' U) = U

/-- `y` and `z` are isomorphic objects: some morphism `φ : y → z`. -/
def IsoB (X : EpGroupoid Obj Mor) (y z : Obj) : Prop :=
  ∃ φ : Mor, X.src φ = y ∧ X.tgt φ = z

/-- **Definition 7.16** (as in V7_56): every saturated open covering of the object M-polyfold has
a subordinate sc-smooth partition of unity with (1) saturated neighbourhoods meeting finitely
many supports and (2) values invariant under isomorphism. -/
def HasScPUB (X : EpGroupoid Obj Mor) : Prop :=
  ∀ (Λ : Type) (U : Λ → Set Obj), (∀ l, IsOpen (U l)) → (∀ l, IsSatB X (U l)) →
    ⋃ l, U l = Set.univ →
    ∃ β : PartitionOfUnity Λ Obj, β.IsSubordinate U ∧
      (∀ l, X.PObj.IsScSmoothMap realPolyfold (β l)) ∧
      (∀ x : Obj, ∃ W : Set Obj, IsOpen W ∧ IsSatB X W ∧ x ∈ W ∧
        {l : Λ | (W ∩ tsupport (β l)).Nonempty}.Finite) ∧
      (∀ (l : Λ) (y z : Obj), IsoB X y z → β l z = β l y)

end

/-- Theorem 7.4: paracompact orbit space and sc-smooth partitions of unity on the object
M-polyfold give sc-smooth partitions of unity of the ep-groupoid (Definition 7.16). -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor),
    X.HasParacompactOrbitSpace → X.PObj.AdmitsScPartitionsOfUnity → HasScPUB X

end RoundTrip.V7_58
