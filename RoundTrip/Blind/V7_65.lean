import Polyfold
/-! Blind formalization of V7_65 (the 2017 book's Part II, §7.5.2, Theorem 7.6 = Theorem 7.4,
p. 255).

Text: let `X` be an ep-groupoid with paracompact orbit space `|X|` whose object M-polyfold admits
sc-smooth partitions of unity.  Then for every open cover of `X` by saturated open subsets
`(U_λ)_{λ ∈ Λ}` there is a subordinate sc-smooth partition of unity of the ep-groupoid `X`.

Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files), with the instances of the
  project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (the project's Definition 7.3, fields read
  with `#print`, as in `RoundTrip/Blind/V7_49.lean`); `|X|` is `X.OrbitSpace` with Mathlib's
  quotient topology (`#synth`), `π` is `X.π`.
- "`|X|` paracompact": Mathlib's `ParacompactSpace X.OrbitSpace` (= the project's
  `HasParacompactOrbitSpace`, `#print`).
- "the object M-polyfold admits sc-smooth partitions of unity" (Definition 5.28): the project's
  `X.PObj.AdmitsScPartitionsOfUnity` (`#print`: every open cover indexed by a `Type` has a
  subordinate Mathlib `PartitionOfUnity` of sc-smooth functions; checked against the text in item
  V5_47).
- "saturated" (`IsSatB`): `π⁻¹(π(U)) = U`.  The cover: `U : Λ → Set Obj`, `Λ : Type`, open,
  saturated, `⋃ U_λ = Obj`.
- "sc-smooth partition of unity of the ep-groupoid `X`" (`IsEpScPOUB`): the notion of
  Definition 7.16 (as quoted in item V7_56: a subordinate sc-smooth partition of unity
  `(β_λ)_{λ ∈ Λ}` with (1) every point has a saturated open neighbourhood meeting only finitely
  many `supp β_λ`, (2) `β_λ(y) = β_λ(z)` for isomorphic `y, z`): every `β_λ : X → ℝ` sc-smooth
  (`X.PObj.IsScSmoothMap realPolyfold`, as in V5_47 and V7_56), `β_λ ≥ 0`, `Σ_λ β_λ = 1`
  pointwise (`finsum`; a finite sum by (1)), (1) with `supp = tsupport`, and (2) as
  `β_λ(s φ) = β_λ(t φ)` for every morphism `φ`.  (1) implies the ordinary local finiteness of the
  supports.  "Subordinate": `supp β_λ ⊆ U_λ`, same index set `Λ`.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_65
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `U ⊆ X` is saturated: `π⁻¹(π(U)) = U`. -/
def IsSatB (X : EpGroupoid Obj Mor) (U : Set Obj) : Prop :=
  X.π ⁻¹' (X.π '' U) = U

/-- An sc-smooth partition of unity of the ep-groupoid `X` (Definition 7.16): sc-smooth,
`≥ 0`, summing to `1`, saturated neighbourhoods meeting finitely many supports, and invariant
under morphisms. -/
def IsEpScPOUB (X : EpGroupoid Obj Mor) {Λ : Type} (β : Λ → Obj → ℝ) : Prop :=
  (∀ l, X.PObj.IsScSmoothMap realPolyfold (β l)) ∧
  (∀ l y, 0 ≤ β l y) ∧
  (∀ y, ∑ᶠ l, β l y = 1) ∧
  (∀ y, ∃ W : Set Obj, IsOpen W ∧ IsSatB X W ∧ y ∈ W ∧
    {l | (W ∩ tsupport (β l)).Nonempty}.Finite) ∧
  (∀ l (φ : Mor), β l (X.src φ) = β l (X.tgt φ))

end

/-- Theorem 7.6 (= 7.4): with paracompact `|X|` and sc-smooth partitions of unity on the object
M-polyfold, every saturated open cover has a subordinate sc-smooth partition of unity of `X`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ParacompactSpace X.OrbitSpace → X.PObj.AdmitsScPartitionsOfUnity →
    ∀ (Λ : Type) (U : Λ → Set Obj), (∀ l, IsOpen (U l)) → (∀ l, IsSatB X (U l)) →
      ⋃ l, U l = Set.univ →
      ∃ β : Λ → Obj → ℝ, IsEpScPOUB X β ∧ ∀ l, tsupport (β l) ⊆ U l

end RoundTrip.V7_65
