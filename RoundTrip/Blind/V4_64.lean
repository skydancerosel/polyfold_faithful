import Polyfold
/-! Blind formalization of V4_64 (the text's §4.3, proof of Theorem 4.23, p. 165).

Text: "We cover the set `{z ∈ A : |p(z)| ≤ ε}` with the finitely many such neighborhoods
`U(z_1), …, U(z_k)`."

Choices:
- Setting: the hypotheses of Theorem 4.23, copied from the blind file V4_54: `X : Type`
  (universe 0), Hausdorff, paracompact, `PX` tame (`IsTame`, Definition 2.37); `Z = ℝᵐ × X` with
  the product charts, the project's `(rnPolyfold m).prod PX` (paracompactness of `ℝᵐ × X` an
  instance hypothesis); `A ⊆ Z` a smooth submanifold with tame induced structure
  (`IsTameSubmanifold`, Definition 4.17, `A` paracompact) with compact closure (in `Z`); `ε > 0`;
  (1) `p⁻¹(λ) = {z ∈ A | z.1 = λ}` compact and nonempty for `|λ| ≤ ε` (`|·|` the Euclidean norm
  `eucNorm`); (2) `A` in general position at every point (the project's `IsGeneralPositionAt`).
- The claim: in the proof, every `z ∈ K = {z ∈ A : |p(z)| ≤ ε}` has been given an open
  neighbourhood `U(z)` (from Theorem 4.22 and the local step, item V4_63), and the text says
  finitely many of them, `U(z_1), …, U(z_k)` with `z_i ∈ K`, cover `K`.  Since the choice of
  `U(z)` is arbitrary (and can be made arbitrarily small: the conclusions of Theorem 4.22 and of
  the local step survive shrinking to small chart neighbourhoods), I read this as: for EVERY
  assignment `z ↦ U(z)` of open neighbourhoods `U(z) ∋ z` to the points of `K`, finitely many
  `z_1, …, z_k ∈ K` have `K ⊆ U(z_1) ∪ … ∪ U(z_k)`.  This is the compactness of `K` (which the
  text tacitly uses).  An alternative, existential reading ("some finite family of such
  neighbourhoods covers `K`") would require restating the properties of the `U(z)`; I did not
  take it.
- I believe the claim is FALSE under the stated hypotheses (formalized literally anyway): `K`
  need not be compact.  Example: `X = ℝ` (no boundary; tame), `m = 1`, `ε = 1`,
  `A = ((−2, 2) × {0}) ∪ ((0, 2) × {1}) ⊆ ℝ²`: a smooth 1-dimensional submanifold without boundary
  (tame, in general position), `closure A` is compact, every fibre `p⁻¹(λ)`, `|λ| ≤ 1`, is a
  nonempty finite set; but `K ⊇ (0, 1] × {1}` accumulates at `(0, 1) ∉ A`, so with
  `U((λ, 1))` the ball of radius `λ/2` no finite subfamily covers `K`.  (A countable subfamily
  always suffices, as `A` is second countable.)
- Nothing else looks doubtful.
-/
namespace RoundTrip.V4_64
open Polyfold

/-- The Euclidean norm `|λ|` on `ℝᵐ`. -/
noncomputable def eucNorm {m : ℕ} (l : Fin m → ℝ) : ℝ := Real.sqrt (∑ i, l i ^ 2)

/-- In the proof of Theorem 4.23: any choice of open neighbourhoods `U(z)` of the points of
`K = {z ∈ A : |p(z)| ≤ ε}` has a finite subfamily `U(z_1), …, U(z_k)`, `z_i ∈ K`, covering `K`. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    (m : ℕ) [ParacompactSpace ((Fin m → ℝ) × X)] (A : Set ((Fin m → ℝ) × X)) (ε : ℝ),
    PX.IsTame →
    (∃ _ : ParacompactSpace A, ((rnPolyfold m).prod PX).IsTameSubmanifold A) →
    IsCompact (closure A) →
    0 < ε →
    -- (1)
    (∀ l : Fin m → ℝ, eucNorm l ≤ ε →
      IsCompact {z | z ∈ A ∧ z.1 = l} ∧ {z | z ∈ A ∧ z.1 = l}.Nonempty) →
    -- (2) general position of `A` at every point
    (∀ z ∈ A, ((rnPolyfold m).prod PX).IsGeneralPositionAt A z) →
    ∀ U : (Fin m → ℝ) × X → Set ((Fin m → ℝ) × X),
      (∀ z ∈ A, eucNorm z.1 ≤ ε → IsOpen (U z) ∧ z ∈ U z) →
      ∃ S : Finset ((Fin m → ℝ) × X), (∀ z ∈ S, z ∈ A ∧ eucNorm z.1 ≤ ε) ∧
        {z | z ∈ A ∧ eucNorm z.1 ≤ ε} ⊆ ⋃ z ∈ S, U z

end RoundTrip.V4_64
