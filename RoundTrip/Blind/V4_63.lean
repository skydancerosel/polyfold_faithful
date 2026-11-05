import Polyfold
/-! Blind formalization of V4_63 (the text's §4.3, proof of Theorem 4.23, pp. 165–166).

Text: "Near `z`, Theorem 4.22 gives `U(z)`; the regular values of the `p_σ` have full measure,
and over them `A_λ ∩ U(z)` is a smooth submanifold in general position."

Choices:
- Setting: the hypotheses of Theorem 4.23, copied from the blind file V4_54: `X : Type`
  (universe 0), Hausdorff, paracompact, `PX` tame (`IsTame`, Definition 2.37); `Z = ℝᵐ × X` with
  the product charts, the project's `(rnPolyfold m).prod PX` (paracompactness of `ℝᵐ × X` an
  instance hypothesis); `A ⊆ Z` a smooth submanifold with tame induced structure
  (`IsTameSubmanifold`, Definition 4.17, `A` paracompact) with compact closure; `ε > 0`;
  (1) `p⁻¹(λ)` compact and nonempty for `|λ| ≤ ε` (`|·|` the Euclidean norm `eucNorm`);
  (2) `A` in general position at every point (the project's `IsGeneralPositionAt`, Definition
  4.21).
- "Near `z`" (`z ∈ A`; the proof uses points with `|p(z)| ≤ ε`, but nothing in the local step
  depends on it, so B states it for every `z ∈ A`), "Theorem 4.22 gives `U(z)`": an open
  `U ∋ z` with exactly `d = d_Z(z)` local faces `F_1, …, F_d` (as in my V4_50/V4_57:
  `IsLocalFacesB`, the faces of `U` — `IsFaceOfOpen`, closures in `U` of components of
  `{d_Z = 1} ∩ U` — are exactly an injective family `F`, all through `z`).  B asserts the
  existence of such `U`, `F` with the claims below; I do not restate the other conclusions of
  Theorem 4.22 for `U`.
- "the regular values of the `p_σ`": `p_σ = P|_{A ∩ F_σ°}`, `F_σ° = {y ∈ U | y ∈ F_i ⟺ i ∈ σ}`
  (`openStratum`), `σ ⊆ {1, …, d}`; `λ` is a regular value of `p_σ` if `Tp_σ(z')` maps
  `T_{z'}(A ∩ F_σ°)` onto `ℝᵐ` at every `z' ∈ A ∩ F_σ°` over `λ` (`regValues`, read in a product
  chart `(r ↦ r − a) × φ` with data of Definition 4.13 for `A ∩ F_σ°`, as in my V4_57).  "The
  regular values of the `p_σ`" = the common regular values `Σ(z) = ⋂_σ Σ_σ`; "have full
  measure": the complement in `ℝᵐ` is Lebesgue-null.
- "over them `A_λ ∩ U(z)` is a smooth submanifold in general position": for every common regular
  value `λ`, the set `{x | (λ, x) ∈ A ∩ U}` (the project's `fibreSet` of `A ∩ U`) is a smooth
  finite-dimensional submanifold of `X` (`IsSmoothSubmanifold`, Definition 4.13) and is in general
  position (`IsGeneralPositionAt`, Definition 4.21) at each of its points.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_63
open Polyfold MeasureTheory

/-- The Euclidean norm `|λ|` on `ℝᵐ`. -/
noncomputable def eucNorm {m : ℕ} (l : Fin m → ℝ) : ℝ := Real.sqrt (∑ i, l i ^ 2)

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- `G` is a face of the open subset `U` of `X`: the closure in `U` of a connected component of
`{y ∈ U | d_X(y) = 1}`. -/
def IsFaceOfOpen (P : MPolyfold X) (U G : Set X) : Prop :=
  ∃ x ∈ U, P.degIndex x = 1 ∧
    G = U ∩ closure (connectedComponentIn (U ∩ {y | P.degIndex y = 1}) x)

/-- Theorem 4.22 (1): the faces of `U` are exactly `F_1, …, F_d`, and all contain `z`. -/
def IsLocalFacesB (P : MPolyfold X) (U : Set X) (z : X) {d : ℕ} (F : Fin d → Set X) : Prop :=
  (∀ i, IsFaceOfOpen P U (F i) ∧ z ∈ F i) ∧ Function.Injective F ∧
    ∀ G : Set X, IsFaceOfOpen P U G → ∃ i, G = F i

/-- The open stratum `F_σ° = {y ∈ U | y ∈ F_i ⟺ i ∈ σ}`. -/
def openStratum {d : ℕ} (U : Set X) (F : Fin d → Set X) (σ : Finset (Fin d)) : Set X :=
  {y | y ∈ U ∧ ∀ i, y ∈ F i ↔ i ∈ σ}

end

/-- `p_S = P|_S : S → ℝᵐ` is regular at `z' ∈ S` (`S ⊆ ℝᵐ × X` a submanifold): in some product
chart `ψ = (r ↦ r − a) × φ`, with data `(V, s)` of Definition 4.13 for `S` at `z'` and the lift
`y` of `ψ(z')`, `v ↦ v.1` maps `T_y(ψ(S ∩ V))` onto `ℝᵐ`. -/
def IsRegularPointOnB {m : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) [ParacompactSpace ((Fin m → ℝ) × X)] (S : Set ((Fin m → ℝ) × X))
    (z' : (Fin m → ℝ) × X) : Prop :=
  ∃ (V : Set ((Fin m → ℝ) × X)) (s : (Fin m → ℝ) × X → (Fin m → ℝ) × X) (a : Fin m → ℝ)
    (φ : MChart X) (y : ((rnSc m).prod φ.model.E).lvl 1),
    ((rnPolyfold m).prod PX).IsScPlusRetractionOn s V ∧ s '' V = S ∩ V ∧ z' ∈ V ∧
    PX.IsChart φ ∧ V ⊆ ((rnChart m a).prod φ).toPartialEquiv.source ∧
    ((rnSc m).prod φ.model.E).toBase 1 y = ((rnChart m a).prod φ).toPartialEquiv z' ∧
    ∀ μ : Fin m → ℝ,
      ∃ v ∈ tangentSpace ((rnSc m).prod φ.model.E) (Set.univ ×ˢ φ.model.C)
          (((rnChart m a).prod φ).toPartialEquiv '' (S ∩ V)) y, v.1 = μ

/-- The regular values of `p_S = P|_S : S → ℝᵐ`. -/
def regValues {m : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) [ParacompactSpace ((Fin m → ℝ) × X)] (S : Set ((Fin m → ℝ) × X)) :
    Set (Fin m → ℝ) :=
  {l | ∀ z' ∈ S, z'.1 = l → IsRegularPointOnB PX S z'}

/-- The local step of Theorem 4.23: near every `z ∈ A`, in the neighbourhood `U(z)` of Theorem
4.22, the common regular values of the `p_σ` have full measure, and over each of them
`A_λ ∩ U(z)` is a smooth submanifold of `X` in general position. -/
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
    ∀ z ∈ A, ∃ (U : Set ((Fin m → ℝ) × X))
      (F : Fin (((rnPolyfold m).prod PX).degIndex z) → Set ((Fin m → ℝ) × X)),
      IsOpen U ∧ z ∈ U ∧ IsLocalFacesB ((rnPolyfold m).prod PX) U z F ∧
      -- the common regular values of the `p_σ` have full measure
      volume (⋂ σ : Finset (Fin (((rnPolyfold m).prod PX).degIndex z)),
        regValues PX (A ∩ openStratum U F σ))ᶜ = 0 ∧
      -- over them, `A_λ ∩ U(z)` is a smooth submanifold in general position
      ∀ l ∈ ⋂ σ : Finset (Fin (((rnPolyfold m).prod PX).degIndex z)),
          regValues PX (A ∩ openStratum U F σ),
        PX.IsSmoothSubmanifold (fibreSet (A ∩ U) l) ∧
        ∀ x ∈ fibreSet (A ∩ U) l, PX.IsGeneralPositionAt (fibreSet (A ∩ U) l) x

end RoundTrip.V4_63
