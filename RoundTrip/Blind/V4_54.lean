import Polyfold
/-! Blind formalization of V4_54 (the text's §4.3, Theorem 4.23, p. 165).

Text: let `A ⊆ Z` be a smooth submanifold with tame induced structure and compact closure,
`p = P|_A`, `ε > 0` with (1) `p⁻¹(λ)` compact and non-empty for `|λ| ≤ ε`, (2) "for `z ∈ A` there
exists a sc-complement `T_zA` in `T_zZ` contained in `T^R_zZ`".  Then there is
`Σ ⊆ {|λ| < ε}` of full measure of regular values of `p` such that for `λ ∈ Σ`, `A_λ` is a smooth
compact manifold with boundary with corners in general position.

Choices:
- Setting (from the text's §4.3 set-up, item V4.53): `X` a tame M-polyfold (`PX.IsTame`,
  Definition 2.37, an equivalent atlas of tame charts — a property of the given structure),
  `X : Type` (universe 0, as asked); `Z = ℝᵐ × X` with the product charts, the project's
  `(rnPolyfold m).prod PX` (`ℝᵐ` with its single chart `id`; Lemma 4.D product charts);
  `P : Z → ℝᵐ`, `P(λ, x) = λ`.  The product needs `ℝᵐ × X` paracompact as an instance; it is a
  hypothesis of B (true: `X` is metrizable by Theorem 2.16).
- "smooth submanifold with tame induced structure": `Z.IsTameSubmanifold A` (Definition 4.17,
  checked with `#print`: `A` is a smooth finite-dimensional submanifold, Definition 4.13, and the
  induced M-polyfold `subPolyfold` is tame), with `A` paracompact as an instance (hypothesis).
  "compact closure": `IsCompact (closure A)` in `Z`.
- (1): `p⁻¹(λ) = {z ∈ A | z.1 = λ}` is compact (in `Z`) and nonempty for every `λ` with
  `|λ| ≤ ε`.  `|λ|` is the Euclidean norm `√(Σ λᵢ²)` (`eucNorm`), my reading of `|·|` on `ℝᵐ`
  (Mathlib's default norm on `Fin m → ℝ` is the sup norm, which I did not use).
- (2) is garbled in the text ("a sc-complement `T_zA`"); I read it as Definition 4.21: `A` is in
  general position at every `z ∈ A` (`T_zA` has in `T_zZ` an sc-complement contained in
  `T^R_zZ`), the project's `Z.IsGeneralPositionAt A z` (checked: in some chart, some data of
  Definition 4.13, some presentation, at the level-`1` lift: an sc-subspace `B ⊆ T_zO ∩ E_z` with
  `(T_zO)_m = (T_zA)_m ⊕ B_m` on every level).
- "of full measure": `Σ ⊆ {|λ| < ε}` and `{|λ| < ε} \ Σ` is Lebesgue-null (`volume` on
  `Fin m → ℝ`).
- "regular values of `p`": I read this literally, in the plain sense: at every `z ∈ A` with
  `p(z) = λ`, `Tp(z) : T_zA → ℝᵐ` is onto (`IsRegularPointB`: in a product chart
  `(r ↦ r − a) × φ` of `Z`, with some data of Definition 4.13 of `A`, the first components of the
  vectors of the tangent space `T_y(ψ(W ∩ A))` at the level-`1` lift `y` exhaust `ℝᵐ`; built
  like the project's `IsStratRegularPoint`, but WITHOUT its restriction to the stratum subspace
  `E_z`).  The text's proof uses the stronger stratified notion (regular values of all `p_σ`); the
  statement only says "regular values of `p`".
- "`A_λ` is a smooth compact manifold with boundary with corners in general position": with
  `A_λ = {x | (λ, x) ∈ A} ⊆ X` (the project's `fibreSet`, checked): `A_λ` is a smooth
  finite-dimensional submanifold of `X` (Definition 4.13), compact, its induced structure (as a
  sub-M-polyfold, `subPolyfold`, paracompactness asserted) has a compatible corner structure
  (`HasCornerStructure`, Definition 4.1), and `A_λ` is in general position (Definition 4.21) at each
  of its points.
- Nothing looks false to me apart from the garbled hypothesis (2).
-/
namespace RoundTrip.V4_54
open Polyfold MeasureTheory

/-- The Euclidean norm `|λ|` on `ℝᵐ`. -/
noncomputable def eucNorm {m : ℕ} (l : Fin m → ℝ) : ℝ := Real.sqrt (∑ i, l i ^ 2)

/-- `z ∈ A` is a regular point of `p = P|_A : A → ℝᵐ` (plain sense): `Tp(z) : T_zA → ℝᵐ` is onto,
read in a product chart `(r ↦ r − a) × φ` of `ℝᵐ × X` with data of Definition 4.13 of `A`. -/
def IsRegularPointB {m : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) [ParacompactSpace ((Fin m → ℝ) × X)] (A : Set ((Fin m → ℝ) × X))
    (z : (Fin m → ℝ) × X) : Prop :=
  z ∈ A ∧
    ∃ (d : ((rnPolyfold m).prod PX).SubmanifoldData A) (a : Fin m → ℝ) (φ : MChart X)
      (y : ((rnSc m).prod φ.model.E).lvl 1),
      z ∈ d.V ∧ PX.IsChart φ ∧ z.2 ∈ φ.source ∧
        ((rnSc m).prod φ.model.E).toBase 1 y = ((rnChart m a).prod φ).toPartialEquiv z ∧
        ∀ μ : Fin m → ℝ,
          ∃ v ∈ tangentSpace ((rnSc m).prod φ.model.E) (Set.univ ×ˢ φ.model.C)
              (((rnChart m a).prod φ).toPartialEquiv ''
                (d.toSubData.shrink ((rnChart m a).prod φ) ∩ A)) y,
            v.1 = μ

/-- Theorem 4.23: under (1)–(2), almost every `λ` with `|λ| < ε` is a regular value of `p` whose
fibre `A_λ` is a compact smooth manifold with boundary with corners in general position. -/
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
      ∃ Sig : Set (Fin m → ℝ), Sig ⊆ {l | eucNorm l < ε} ∧
        volume ({l | eucNorm l < ε} \ Sig) = 0 ∧
        ∀ l ∈ Sig,
          -- `λ` is a regular value of `p`
          (∀ z ∈ A, z.1 = l → IsRegularPointB PX A z) ∧
          -- `A_λ` is a smooth compact manifold with boundary with corners in general position
          PX.IsSmoothSubmanifold (fibreSet A l) ∧ IsCompact (fibreSet A l) ∧
          (∃ (hS : PX.IsSubMPolyfold (fibreSet A l)) (_ : ParacompactSpace (fibreSet A l)),
            (PX.subPolyfold hS).HasCornerStructure) ∧
          ∀ x ∈ fibreSet A l, PX.IsGeneralPositionAt (fibreSet A l) x

end RoundTrip.V4_54
