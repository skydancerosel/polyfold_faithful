import Polyfold
/-! Blind formalization of V4_57 (the text's §4.3, proof of Theorem 4.23, pp. 165–166).

Text: "By Theorem 4.23, the intersection `A ∩ F_σ°` is a smooth manifold without boundary having
dimension `dim(A) − #σ`"; Sard gives sets `Σ_σ` of full measure of regular values of `p_σ`, and
`Σ = ⋂_σ Σ_σ`.

Choices:
- "By Theorem 4.23" is a misprint for Theorem 4.22 (the theorem being proved is 4.23; the faces
  `F_σ` and the neighbourhood `U(z)` come from Theorem 4.22).  Formalized as the text means it.
- Setting: the hypotheses of Theorem 4.23, copied from the blind file V4_54: `X : Type`
  (universe 0), Hausdorff, paracompact, `PX` tame (`IsTame`, Definition 2.37); `Z = ℝᵐ × X` with
  the product charts, the project's `(rnPolyfold m).prod PX` (paracompactness of `ℝᵐ × X` an
  instance hypothesis); `A ⊆ Z` a smooth submanifold with tame induced structure
  (`IsTameSubmanifold`, Definition 4.17, `A` paracompact) with compact closure; `ε > 0`;
  (1) `p⁻¹(λ)` compact and nonempty for `|λ| ≤ ε` (`|·|` the Euclidean norm `eucNorm`);
  (2) `A` in general position at every point (the project's `IsGeneralPositionAt`, Definition
  4.21).
- The local objects of the proof: for `z ∈ A`, Theorem 4.22 (applicable by (2)) gives an open
  `U = U(z) ∋ z` with exactly `d = d_Z(z)` local faces `F_1, …, F_d`.  As in my V4_50: the faces
  of `U` (`IsFaceOfOpen`: closures in `U` of connected components of `{y ∈ U | d_Z(y) = 1}`,
  `d_Z` the project's `degIndex` of `Z`) are exactly an injective family `F : Fin d → Set Z`, all
  containing `z` (`IsLocalFacesB`).  B asserts the existence of such `U`, `F` (the `U(z)` of
  Theorem 4.22) for which the claims hold.  `F_σ° = {y ∈ U | y ∈ F_i ⟺ i ∈ σ}` (`openStratum`:
  the points of `F_σ = ⋂_{i ∈ σ} F_i` lying on no other local face), `σ ⊆ {1, …, d}`.
- "`A ∩ F_σ°` is a smooth manifold without boundary": `A ∩ F_σ°` is a smooth finite-dimensional
  submanifold of `Z` (the project's `IsSmoothSubmanifold`, Definition 4.13), and its induced
  M-polyfold structure (`subPolyfold`, paracompactness asserted) has no boundary
  (`IsWithoutBoundary`: degeneracy index `0` everywhere, Definition 2.25).
- "having dimension `dim(A) − #σ`", pointwise: at every `z' ∈ A ∩ F_σ°` there is `k` with
  `dim T_{z'}A = k + #σ` and `dim T_{z'}(A ∩ F_σ°) = k` (`HasTanDimB`: the tangent space
  `T_w(φ(S ∩ V))` (`tangentSpace`, Definition 2.17) has rank `k` for EVERY data `(V, s)` of
  Definition 4.13 at the point, chart `φ ⊇ V` of the structure and level-`1` lift `w`).
- "regular values of `p_σ`", `p_σ = P|_{A ∩ F_σ°} : A ∩ F_σ° → ℝᵐ`: `λ` such that at every
  `z' ∈ A ∩ F_σ°` with `p(z') = λ` the derivative `Tp_σ(z')` maps `T_{z'}(A ∩ F_σ°)` onto `ℝᵐ`
  (`regValues`).  `Tp_σ(z')` is read in a product chart `(r ↦ r − a) × φ` of `Z`, with data
  `(V, s)` of Definition 4.13 for `A ∩ F_σ°` at `z'` and the level-`1` lift `y` of the image of
  `z'`: every `μ ∈ ℝᵐ` is `v.1` for some `v ∈ T_y(ψ((A ∩ F_σ°) ∩ V))` (the derivative of `P` in
  this chart is `v ↦ v.1`); "for some" such chart and data, the convention of Definitions 4.16,
  4.21.
- "Sard gives sets `Σ_σ` of full measure of regular values": the set of regular values of `p_σ`
  has full measure in `ℝᵐ` (its complement is Lebesgue-null, `volume` on `Fin m → ℝ`); a full
  measure set of regular values exists iff this holds.  "`Σ = ⋂_σ Σ_σ`": B also asserts that the
  set of common regular values of all `p_σ`, `σ ⊆ {1, …, d}`, has full measure.
- Nothing looks false to me apart from the misprinted theorem number.
-/
namespace RoundTrip.V4_57
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

/-- The submanifold `S` has dimension `k` at `y`: in every chart, `dim T_yS = k`. -/
def HasTanDimB (P : MPolyfold X) (S : Set X) (y : X) (k : ℕ) : Prop :=
  ∀ (V : Set X) (s : X → X) (φ : MChart X) (w : φ.model.E.lvl 1)
    (N : Submodule ℝ (φ.model.E.lvl 0)),
    P.IsScPlusRetractionOn s V → s '' V = S ∩ V → y ∈ V →
    P.IsChart φ → V ⊆ φ.toPartialEquiv.source →
    φ.model.E.toBase 1 w = φ.toPartialEquiv y →
    (N : Set (φ.model.E.lvl 0)) =
      tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (S ∩ V)) w →
    Module.rank ℝ N = k

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

/-- In the proof of Theorem 4.23: near every `z ∈ A`, in the neighbourhood `U(z)` of Theorem 4.22
with its local faces, each stratum `A ∩ F_σ°` is a manifold without boundary of dimension
`dim A − #σ`, the regular values of `p_σ` have full measure (Sard), and so do the common regular
values `Σ = ⋂_σ Σ_σ`. -/
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
      (∀ σ : Finset (Fin (((rnPolyfold m).prod PX).degIndex z)),
        -- `A ∩ F_σ°` is a smooth manifold without boundary
        ((rnPolyfold m).prod PX).IsSmoothSubmanifold (A ∩ openStratum U F σ) ∧
        (∃ (hS : ((rnPolyfold m).prod PX).IsSubMPolyfold (A ∩ openStratum U F σ))
          (_ : ParacompactSpace ↥(A ∩ openStratum U F σ)),
          (((rnPolyfold m).prod PX).subPolyfold hS).IsWithoutBoundary) ∧
        -- of dimension `dim(A) − #σ`
        (∀ z' ∈ A ∩ openStratum U F σ, ∃ k : ℕ,
          HasTanDimB ((rnPolyfold m).prod PX) A z' (k + σ.card) ∧
          HasTanDimB ((rnPolyfold m).prod PX) (A ∩ openStratum U F σ) z' k) ∧
        -- Sard: the regular values `Σ_σ` of `p_σ` have full measure
        volume (regValues PX (A ∩ openStratum U F σ))ᶜ = 0) ∧
      -- `Σ = ⋂_σ Σ_σ` has full measure
      volume (⋂ σ : Finset (Fin (((rnPolyfold m).prod PX).degIndex z)),
        regValues PX (A ∩ openStratum U F σ))ᶜ = 0

end RoundTrip.V4_57
