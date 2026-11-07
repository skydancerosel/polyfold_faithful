import Polyfold
/-! Blind formalization of V7_68 (the 2017 book's Part II, §7.5.2, Corollary 7.3, p. 256).

Text: let `X` be an ep-groupoid with paracompact `|X|` whose object M-polyfold admits an atlas of
charts whose local models `(O, C, E)` have `E₀` Hilbert spaces.  Then every open covering of `X`
by saturated open subsets `(U_λ)_{λ ∈ Λ}` has a subordinate sc-smooth partition of unity of the
ep-groupoid `X`.  (Proof: the assumption implies that the object M-polyfold admits sc-smooth
partitions of unity; then Theorem 7.4 applies.)

Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files), with the instances of the
  project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (Definition 7.3, fields read with `#print`, as
  in `RoundTrip/Blind/V7_49.lean`); `|X| = X.OrbitSpace` (quotient topology), paracompact in
  Mathlib's sense.
- "admits an atlas consisting of charts whose local models have `E₀` Hilbert"
  (`HasHilbertAtlasB`): there is an atlas `A` (the project's `MAtlas`, `#print`: pairwise
  compatible charts covering `X`) EQUIVALENT to the given structure `X.PObj.atlas` (the project's
  `MAtlas.Equiv`, `#print`: the union is again an atlas; the same reading the project uses for
  "tame", `MPolyfold.IsTame`), every chart `φ ∈ A` having a local model `φ.model = (O, C, E)`
  with `E₀ = φ.model.E.lvl 0` a Hilbert space.  This is an existential property of the given
  structure, not a condition on all charts.
- "`E₀` is a Hilbert space" (`IsHilbertNormB`): the given (complete) norm of `E₀` satisfies the
  parallelogram identity, i.e. comes from an inner product (Jordan–von Neumann; Mathlib's
  `InnerProductSpace.ofNorm` takes exactly this).  I read it literally (the norm IS a Hilbert
  norm).  The weaker reading "`E₀` is isomorphic to a Hilbert space" (an equivalent Hilbert norm)
  would give a stronger B; I believe it is also true, since sc-smoothness is unchanged under
  equivalent norms.
- Conclusion as in `RoundTrip/Blind/V7_65.lean` (`IsSatB`, `IsEpScPOUB` = Definition 7.16).
- B is the conjunction of the proof's stated intermediate claim (the object M-polyfold admits
  sc-smooth partitions of unity: the project's `AdmitsScPartitionsOfUnity`, Definition 5.28,
  item V5_47) and the corollary.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_68
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `U ⊆ X` is saturated: `π⁻¹(π(U)) = U`. -/
def IsSatB (X : EpGroupoid Obj Mor) (U : Set Obj) : Prop :=
  X.π ⁻¹' (X.π '' U) = U

/-- An sc-smooth partition of unity of the ep-groupoid `X` (Definition 7.16), as in
`RoundTrip/Blind/V7_65.lean`. -/
def IsEpScPOUB (X : EpGroupoid Obj Mor) {Λ : Type} (β : Λ → Obj → ℝ) : Prop :=
  (∀ l, X.PObj.IsScSmoothMap realPolyfold (β l)) ∧
  (∀ l y, 0 ≤ β l y) ∧
  (∀ y, ∑ᶠ l, β l y = 1) ∧
  (∀ y, ∃ W : Set Obj, IsOpen W ∧ IsSatB X W ∧ y ∈ W ∧
    {l | (W ∩ tsupport (β l)).Nonempty}.Finite) ∧
  (∀ l (φ : Mor), β l (X.src φ) = β l (X.tgt φ))

end

/-- The norm of `E` is a Hilbert norm: the parallelogram identity. -/
def IsHilbertNormB (E : Type) [NormedAddCommGroup E] : Prop :=
  ∀ a b : E, ‖a + b‖ * ‖a + b‖ + ‖a - b‖ * ‖a - b‖ = 2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖)

/-- The M-polyfold admits an (equivalent) atlas of charts whose local models have Hilbert `E₀`. -/
def HasHilbertAtlasB {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (P : MPolyfold Z) : Prop :=
  ∃ A : MAtlas Z, A.Equiv P.atlas ∧ ∀ φ ∈ A.charts, IsHilbertNormB (φ.model.E.lvl 0)

/-- Corollary 7.3: with paracompact `|X|` and an sc-Hilbert atlas of the object M-polyfold, the
object M-polyfold admits sc-smooth partitions of unity, and every saturated open cover has a
subordinate sc-smooth partition of unity of `X`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ParacompactSpace X.OrbitSpace → HasHilbertAtlasB X.PObj →
    X.PObj.AdmitsScPartitionsOfUnity ∧
    ∀ (Λ : Type) (U : Λ → Set Obj), (∀ l, IsOpen (U l)) → (∀ l, IsSatB X (U l)) →
      ⋃ l, U l = Set.univ →
      ∃ β : Λ → Obj → ℝ, IsEpScPOUB X β ∧ ∀ l, tsupport (β l) ⊆ U l

end RoundTrip.V7_68
