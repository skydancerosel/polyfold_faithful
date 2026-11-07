import Polyfold
/-! Blind formalization of V7_56 (the 2017 book's Part II, §7.4, Definition 7.16, pp. 250–251).

Text: an ep-groupoid `X` with sc-smooth partitions of unity is one such that for every saturated
open covering `(U_λ)_{λ ∈ Λ}` of the object M-polyfold `X` there is a subordinate sc-smooth
partition of unity `(β_λ)_{λ ∈ Λ}` with (1) every `x ∈ X` has a saturated open neighbourhood
meeting only finitely many `supp(β_λ)`; (2) `β_λ(z) = β_λ(y)` for isomorphic objects `y, z`.

Choices:
- This item is a definition.  B says that the project's `X.HasScPartitionsOfUnity` is the text's
  notion `HasScPUB X` written below.
- Setting as in `RoundTrip/Blind/V7_49.lean`: `Obj Mor : Type` (universe 0) with the instances
  of the project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (the project's ep-groupoid,
  Definition 7.3, fields read with `#print`); `π` the project's `X.π : Obj → X.OrbitSpace`
  (checked: the quotient by "isomorphic").
- "saturated" (`IsSatB`): `U = π⁻¹(π(U))` (the text's definition, p. 250).  "isomorphic objects"
  (`IsoB`): some morphism `φ` with `s φ = y`, `t φ = z`.  "saturated open covering of `X`": a
  family `U : Λ → Set Obj` (`Λ : Type`) of open saturated sets with `⋃ U_λ = Obj`.
- "subordinate sc-smooth partition of unity `(β_λ)_{λ ∈ Λ}`": a Mathlib `PartitionOfUnity Λ Obj`
  (continuous `β_λ ≥ 0`, locally finite supports, `Σ β_λ = 1`), subordinate
  (`IsSubordinate`: `supp β_λ = cl{β_λ ≠ 0} ⊆ U_λ`), every `β_λ` sc-smooth as a map `X → ℝ`
  (`X.PObj.IsScSmoothMap realPolyfold`, Definition 2.14 with `ℝ` the one-chart M-polyfold; the
  reading of "sc-smooth function" used in the earlier blind files on partitions of unity,
  e.g. `RoundTrip/Blind/V5_47.lean`).  Same index set `Λ` as the cover.
- (1): `W` open, saturated, `x ∈ W`, and `{λ | W ∩ supp β_λ ≠ ∅}` finite, `supp` = `tsupport`.
  (2): for all `λ` and isomorphic `y, z`, `β_λ(z) = β_λ(y)`.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_56
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

/-- **Definition 7.16**: every saturated open covering of the object M-polyfold has a subordinate
sc-smooth partition of unity with (1) saturated neighbourhoods meeting finitely many supports and
(2) values invariant under isomorphism. -/
def HasScPUB (X : EpGroupoid Obj Mor) : Prop :=
  ∀ (Λ : Type) (U : Λ → Set Obj), (∀ l, IsOpen (U l)) → (∀ l, IsSatB X (U l)) →
    ⋃ l, U l = Set.univ →
    ∃ β : PartitionOfUnity Λ Obj, β.IsSubordinate U ∧
      (∀ l, X.PObj.IsScSmoothMap realPolyfold (β l)) ∧
      (∀ x : Obj, ∃ W : Set Obj, IsOpen W ∧ IsSatB X W ∧ x ∈ W ∧
        {l : Λ | (W ∩ tsupport (β l)).Nonempty}.Finite) ∧
      (∀ (l : Λ) (y z : Obj), IsoB X y z → β l z = β l y)

end

/-- Definition 7.16: the project's ep-groupoids with sc-smooth partitions of unity are the
text's. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor),
    X.HasScPartitionsOfUnity ↔ HasScPUB X

end RoundTrip.V7_56
