import Polyfold
/-! Blind formalization of V7_55 (the 2017 book's Part II, §7.4, Theorem 7.3 and the paragraph
before it, p. 250).

Text: for an ep-groupoid `X` with paracompact orbit space, every open cover `(O_λ)_{λ ∈ Λ}` of
`|X|` has a subordinate partition of unity `(σ_λ)_{λ ∈ Λ}`.  In particular every covering
`(U_λ)` of `X` by saturated open sets has a subordinate continuous partition of unity `(β_λ)`
with every `β_λ` taking the same values on isomorphic objects.  (The proof shows moreover that
every object has an open neighbourhood `π⁻¹(V)` meeting only finitely many supports of the
`β_λ`.)

Choices:
- Setting as in `RoundTrip/Blind/V7_49.lean`: `Obj Mor : Type` (universe 0) with the instances
  of the project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (the project's ep-groupoid,
  Definition 7.3, fields read with `#print`); `|X|` the project's `X.OrbitSpace` (the quotient by
  "isomorphic", checked) with the quotient topology, `π` the project's `X.π` (checked: `x ↦ ⟦x⟧`).
- "with paracompact orbit space": the project's `X.HasParacompactOrbitSpace` (checked with
  `#print`: Mathlib's `ParacompactSpace X.OrbitSpace`; see `RoundTrip/Blind/V7_53.lean`).
- "partition of unity subordinate to `(O_λ)`": Mathlib's `PartitionOfUnity Λ |X|` (continuous
  `σ_λ ≥ 0`, locally finite supports, `Σ_λ σ_λ = 1`) with `IsSubordinate`
  (`supp σ_λ = cl{σ_λ ≠ 0} ⊆ O_λ`).  Index types `Λ : Type`; the same index set `Λ` for the
  cover and the partition, as in the text (zero functions allowed).
- "saturated" (`IsSatB`): `U = π⁻¹(π(U))`, as defined in the text.  "isomorphic objects"
  (`IsoB`): there is a morphism `φ` with `s φ = y`, `t φ = z`.  A "covering of `X`": `⋃ U_λ = X`
  (the object space).
- B is the conjunction of (1) the partition of unity on `|X|`; (2) for every saturated open cover
  of the object space, ONE continuous partition of unity `(β_λ)` on `Obj` (Mathlib's
  `PartitionOfUnity Λ Obj`) which is subordinate, invariant under isomorphism, and such that every
  object `x` has an open `V ⊆ |X|` with `x ∈ π⁻¹(V)` and `π⁻¹(V)` meeting `supp β_λ =
  cl{β_λ ≠ 0}` (`tsupport`) for only finitely many `λ` — the parenthetical "the proof shows,
  moreover", included as a claim.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_55
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

end

/-- Theorem 7.3: subordinate partitions of unity on `|X|`, and invariant ones on `X` for saturated
open covers, with saturated neighbourhoods `π⁻¹(V)` meeting finitely many supports. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor), X.HasParacompactOrbitSpace →
    (∀ (Λ : Type) (O : Λ → Set X.OrbitSpace), (∀ l, IsOpen (O l)) → ⋃ l, O l = Set.univ →
      ∃ σ : PartitionOfUnity Λ X.OrbitSpace, σ.IsSubordinate O) ∧
    (∀ (Λ : Type) (U : Λ → Set Obj), (∀ l, IsOpen (U l)) → (∀ l, IsSatB X (U l)) →
      ⋃ l, U l = Set.univ →
      ∃ β : PartitionOfUnity Λ Obj, β.IsSubordinate U ∧
        (∀ (l : Λ) (y z : Obj), IsoB X y z → β l y = β l z) ∧
        (∀ x : Obj, ∃ V : Set X.OrbitSpace, IsOpen V ∧ X.π x ∈ V ∧
          {l : Λ | (X.π ⁻¹' V ∩ tsupport (β l)).Nonempty}.Finite))

end RoundTrip.V7_55
