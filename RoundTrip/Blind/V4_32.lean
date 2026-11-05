import Polyfold
/-! Blind formalization of V4_32 (the text's §4.2, Remark 4.14, p. 157).

Text: near points `a ∈ A` with `d_X(a) = 0`, `A` is a smooth finite-dimensional manifold in the
classical sense; the same where `T_aA` is in good position.

Choices:
- Setting: `X : Type` (universe 0), Hausdorff paracompact, `P : MPolyfold X`, `A ⊆ X` a smooth
  finite-dimensional submanifold (Definition 4.13; my own `IsSmoothSubmanifoldB`, copied from my
  V4_29, with the sc⁺-retractions `IsScPlusRetractionOnB` of my V4_9).  No tameness: the remark
  does not assume it.
- `d_X(a)`: the project's `P.degIndex a` (Definition 2.22, checked with `#print`: the minimum over
  the charts `φ` around `a` of `d_C(φ(a))`).
- "Near `a`, `A` is a smooth finite-dimensional manifold in the classical sense": there is an open
  `W ∋ a` in `X` such that `A ∩ W` with the structure induced from `X` (sub-M-polyfold,
  `IsSubMPolyfold`, Definition 2.20; induced structure `subPolyfold`, Proposition 2.21; `A ∩ W`
  paracompact, asserted (∃) as the project needs it as an instance) has a compatible smooth
  manifold structure with boundary with corners (the project's `HasCornerStructure`, Definition
  4.1, checked: an equivalent atlas of corner charts onto relatively open subsets of partial
  quadrants of finite-dimensional spaces with the constant sc-structure; by the remark after
  Definition 4.1 such an atlas is a classical `C^∞` atlas).  For `d_X(a) = 0` I read "classical
  manifold" as a manifold WITHOUT boundary and add that the induced structure has `d ≡ 0`
  (`IsWithoutBoundary`, Definition 2.25); with corner charts this means the charts take values in
  the interiors of the quadrants.  For "the same where `T_aA` is in good position" the manifold may
  have boundary and corners (only `HasCornerStructure`).
- "`T_aA` is in good position" (AMBIGUOUS; the remark precedes Definition 4.16 and follows
  Proposition 4.9): I read it in a chart, in the sense of Definition 3.21 as used in Proposition
  4.9 — my `IsGoodPositionInChartB`: for SOME data `(V, s)` of Definition 4.13 at `a`, SOME chart
  `φ` of the structure with `V` in its domain, SOME presentation `T` of its partial quadrant `C`,
  and the level-`1` point `z` over `φ(a)`, the tangent space `T_z(φ(A ∩ V))` (the project's
  `tangentSpace`, Definition 2.17) is in good position (Definition 3.21, my `IsGoodPositionB`
  copied from my V4_20: `N ∩ C_z` has nonempty interior in `N`, and `N` has an sc-complement `Y`
  with `n ∈ C_z ↔ n + y ∈ C_z` when `|y|₀ ≤ ε|n|₀`) to the partial quadrant `C_z` of
  Definition 2.33 (the project's `partialQuadrantAtWith T z`, checked: the half-spaces of the
  coordinates vanishing at `z`; `C_0 = C`, and `C_z` agrees with `C` near `z`).  The alternative
  reading is Definition 4.16 (`T_aA` in good position to the partial cone `C_aX` inside `T_aX`, the
  project's `IsGoodPositionAt`), which is the notion of Theorem 4.18 (where `X` is tame); I did not
  use it.
- Nothing looks false to me under these readings.
-/
namespace RoundTrip.V4_32
open Polyfold

/-- Definition 4.4 (second sentence): an sc-smooth retraction `r : V → V` on an open subset `V` of
the M-polyfold `X` is an **sc⁺-retraction** if `r : V → V¹` is sc-smooth. -/
def IsScPlusRetractionOnB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (r : X → X) (V : Set X) : Prop :=
  IsOpen V ∧ P.IsScSmoothOn P r V ∧ Set.MapsTo r V V ∧ (∀ x ∈ V, r (r x) = r x) ∧
  (∀ x ∈ V, r x ∈ P.levelSet 1) ∧
  ∀ g : X → P.Level 1, (∀ x ∈ V, P.levelVal 1 (g x) = r x) → P.IsScSmoothOn P.shift g V

/-- Definition 4.13: `A` is a smooth finite-dimensional submanifold of `X`. -/
def IsSmoothSubmanifoldB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (A : Set X) : Prop :=
  ∀ a ∈ A, ∃ (V : Set X) (s : X → X), IsOpen V ∧ a ∈ V ∧ IsScPlusRetractionOnB P s V ∧
    s '' V = A ∩ V

/-- Definition 3.21 with an sc-complement: `N ∩ C` has nonempty interior in `N`, and `N` has an
sc-complement `Y` with `n ∈ C ↔ n + y ∈ C` whenever `|y|₀ ≤ ε|n|₀`. -/
def IsGoodPositionB (E : ScBanach) (C : Set (E.lvl 0)) (N : Submodule ℝ (E.lvl 0)) : Prop :=
  (interior ((Subtype.val : N → E.lvl 0) ⁻¹' C)).Nonempty ∧
    ∃ Y : Submodule ℝ (E.lvl 0), E.IsScSplitting N Y ∧
      ∃ ε > (0 : ℝ), ∀ n ∈ N, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + y ∈ C)

/-- `T_aA` is in good position, read in a chart: for some data `(V, s)` of Definition 4.13 at
`a`, some chart `φ ⊇ V`, some presentation `T` of its partial quadrant and the level-`1` point `z`
over `φ(a)`, `T_z(φ(A ∩ V))` is in good position to the partial quadrant `C_z`. -/
def IsGoodPositionInChartB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (A : Set X) (a : X) : Prop :=
  ∃ (V : Set X) (s : X → X) (φ : MChart X) (n : ℕ) (Wq : ScBanach)
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (z : φ.model.E.lvl 1)
    (N : Submodule ℝ (φ.model.E.lvl 0)),
    IsScPlusRetractionOnB P s V ∧ s '' V = A ∩ V ∧ a ∈ A ∩ V ∧
    P.IsChart φ ∧ V ⊆ φ.toPartialEquiv.source ∧
    φ.model.C = T.lvl 0 ⁻¹' quadrant n Wq 0 ∧
    φ.model.E.toBase 1 z = φ.toPartialEquiv a ∧
    (N : Set (φ.model.E.lvl 0)) =
      tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (A ∩ V)) z ∧
    IsGoodPositionB φ.model.E (partialQuadrantAtWith T (φ.model.E.toBase 1 z)) N

/-- Remark 4.14: near a point of `A` with `d_X = 0`, `A` (with the induced structure) is a
classical smooth manifold without boundary; near a point where `T_aA` is in good position it is a
classical smooth manifold with boundary with corners. -/
def B : Prop :=
  (∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X), IsSmoothSubmanifoldB P A → ∀ a ∈ A, P.degIndex a = 0 →
      ∃ W : Set X, IsOpen W ∧ a ∈ W ∧
        ∃ (hW : P.IsSubMPolyfold (A ∩ W)) (_ : ParacompactSpace ↑(A ∩ W)),
          (P.subPolyfold hW).HasCornerStructure ∧ (P.subPolyfold hW).IsWithoutBoundary) ∧
  (∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X), IsSmoothSubmanifoldB P A → ∀ a ∈ A, IsGoodPositionInChartB P A a →
      ∃ W : Set X, IsOpen W ∧ a ∈ W ∧
        ∃ (hW : P.IsSubMPolyfold (A ∩ W)) (_ : ParacompactSpace ↑(A ∩ W)),
          (P.subPolyfold hW).HasCornerStructure)

end RoundTrip.V4_32
