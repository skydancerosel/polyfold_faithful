import Polyfold
/-! Blind formalization of V4_53 (the text's §4.3, p. 164, and the proof of Theorem 4.23, p. 166).

Text: "`Z = ℝᵐ ⊕ X` with the product charts is tame; `P(λ, x) = λ`; the proof uses regular values
of the maps `p_σ : A ∩ F_σ° → ℝᵐ`."

Choices:
- The item mixes one claim and two definitions.  B is the conjunction of (i) the claim "`Z` is
  tame" and (ii) the statement that the project's `IsStratRegularPoint` is the text's notion
  "`z` is a regular point of `p_σ`, `σ` the set of local faces through `z`" (written here as
  `IsStratRegularPointB`), in the text's setting.  `P(λ, x) = λ` is the definition `projP` below
  (the text asserts nothing about it).
- Setting: `X : Type` (universe 0, as in the other blind files of this chapter), Hausdorff,
  paracompact, `PX : MPolyfold X` tame (`PX.IsTame`, Definition 2.37: an equivalent atlas of
  charts on tame retracts — a property of the given structure).  `ℝᵐ = Fin m → ℝ` is the project's
  `rnPolyfold m` (one chart `id`; constant sc-structure).  "`Z = ℝᵐ ⊕ X` with the product charts":
  the project's `(rnPolyfold m).prod PX` (Exposition Lemma 4.D: the atlas of product charts).  It
  needs `ℝᵐ × X` paracompact as an instance; this is a hypothesis of B (true: `X` is metrizable).
- (i): `((rnPolyfold m).prod PX).IsTame` for every tame `X` and every `m`.
- (ii), the notion of regular value used by the proof.  In a neighbourhood `U(z)` of Theorem 4.22
  every point `z'` of `A ∩ U(z)` lies in exactly one open stratum `F_σ°`, `σ = σ(z')` the local
  faces through `z'`, and `λ` is a regular value of all `p_σ` iff `Tp_σ(z') : T_{z'}(A ∩ F_σ°) →
  ℝᵐ` is onto at every `z'` over `λ`.  The tangent space of the stratum is
  `T_{z'}A ∩ T^R_{z'}Z` (Definition 2.38: the reduced tangent space is the tangent space of the
  stratum), and `T^R_{z'}Z = ℝᵐ × T^R_{z'₂}X`.  In a chart: a product chart
  `ψ = (r ↦ r − a) × φ` of `Z` (`rnChart m a`, `φ` a chart of `X`), data `(V, s)` of Definition
  4.13 for `A` at `z'` with `V` inside the domain of `ψ` (the project's `IsScPlusRetractionOn`,
  `s(V) = A ∩ V`), a presentation `T` of the partial quadrant of `φ`, and the level-`1` lift `y` of
  `ψ(z')`; `T_{z'}A = T_y(ψ(A ∩ V))` (`tangentSpace`, Definition 2.17) and
  `T^R = T_yO ∩ (ℝᵐ × E_{y₂})` with `E_{y₂}` the vectors whose coordinates vanish where those of
  `y₂` do (`minimalSubspaceWith`).  The derivative of `P` in this chart is `v ↦ v.1`.  So
  `IsStratRegularPointB`: `z' ∈ A` and, for some such data, chart, presentation and lift, every
  `μ ∈ ℝᵐ` is `v.1` for some `v ∈ T_y(ψ(A ∩ V))` with `v.2 ∈ E_{y₂}`.  "For some" is the chart
  convention of Definitions 4.16 and 4.21 (the condition does not depend on the choices).
  I do not restrict to charts of `X` modelled on tame retracts (Definition 2.38 is phrased with
  tame charts); this follows the chart convention of the other blind files for Definition 4.21.
- (ii) is stated for `X` tame and `A` a smooth finite-dimensional submanifold of `Z` (the
  project's `IsSmoothSubmanifold`, Definition 4.13) and every point `z ∈ Z`.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_53
open Polyfold

/-- The projection `P : ℝᵐ × X → ℝᵐ`, `P(λ, x) = λ`. -/
def projP {m : ℕ} {X : Type} : (Fin m → ℝ) × X → (Fin m → ℝ) := Prod.fst

/-- `z ∈ A` is a regular point of `p_σ : A ∩ F_σ° → ℝᵐ` (`σ` the local faces through `z`): in a
product chart `ψ = (r ↦ r − a) × φ` of `ℝᵐ × X`, with data `(V, s)` of Definition 4.13 for `A`, a
presentation `T` of the partial quadrant of `φ` and the level-`1` lift `y` of `ψ(z)`, the
derivative `v ↦ v.1` of `P` maps `T_zA ∩ T^R_zZ = T_y(ψ(A ∩ V)) ∩ (ℝᵐ × E_{y₂})` onto `ℝᵐ`. -/
def IsStratRegularPointB {m : ℕ} {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] (PX : MPolyfold X) [ParacompactSpace ((Fin m → ℝ) × X)]
    (A : Set ((Fin m → ℝ) × X)) (z : (Fin m → ℝ) × X) : Prop :=
  z ∈ A ∧
    ∃ (V : Set ((Fin m → ℝ) × X)) (s : (Fin m → ℝ) × X → (Fin m → ℝ) × X) (a : Fin m → ℝ)
      (φ : MChart X) (n : ℕ) (Wq : ScBanach)
      (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
      (y : ((rnSc m).prod φ.model.E).lvl 1),
      ((rnPolyfold m).prod PX).IsScPlusRetractionOn s V ∧ s '' V = A ∩ V ∧ z ∈ V ∧
      PX.IsChart φ ∧ V ⊆ ((rnChart m a).prod φ).toPartialEquiv.source ∧
      φ.model.C = T.lvl 0 ⁻¹' quadrant n Wq 0 ∧
      ((rnSc m).prod φ.model.E).toBase 1 y = ((rnChart m a).prod φ).toPartialEquiv z ∧
      ∀ μ : Fin m → ℝ,
        ∃ v ∈ tangentSpace ((rnSc m).prod φ.model.E) (Set.univ ×ˢ φ.model.C)
            (((rnChart m a).prod φ).toPartialEquiv '' (A ∩ V)) y,
          v.2 ∈ minimalSubspaceWith T (φ.model.E.toBase 1 y.2) ∧ v.1 = μ

/-- `ℝᵐ × X` with the product charts is tame, and the project's stratified regular points are the
regular points of the maps `p_σ` of the proof of Theorem 4.23. -/
def B : Prop :=
  (∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    (m : ℕ) [ParacompactSpace ((Fin m → ℝ) × X)],
      PX.IsTame → ((rnPolyfold m).prod PX).IsTame) ∧
  (∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    (m : ℕ) [ParacompactSpace ((Fin m → ℝ) × X)] (A : Set ((Fin m → ℝ) × X))
    (z : (Fin m → ℝ) × X),
      PX.IsTame → ((rnPolyfold m).prod PX).IsSmoothSubmanifold A →
        (IsStratRegularPoint PX A z ↔ IsStratRegularPointB PX A z))

end RoundTrip.V4_53
