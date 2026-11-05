import Polyfold
/-! Blind formalization of V4_43 (the text's §4.2, Remark 4.20, p. 161).

Text: if `A` is in good position at `a`, there is an open `V(a) ⊆ X` such that `A` is in good
position at every `b ∈ V(a) ∩ A` (Proposition 4.9 and Lemma 3.55: "the tangent spaces of `A`
move only slowly").

Choices:
- Setting (that of Definition 4.16): `X : Type` (universe 0, as in the other blind files of this
  chapter), Hausdorff paracompact, `P : MPolyfold X` tame (the project's `IsTame`, docstring =
  Definition 2.37), `A ⊆ X` a smooth finite-dimensional submanifold (my own
  `IsSmoothSubmanifoldB`, Definition 4.13, copied from V4_33), `a ∈ A`.
- "in good position at `a`": Definition 4.16 in my own chart form `IsGoodPositionAtB`, copied
  verbatim from my V4_38 (which states that it agrees with the project's `IsGoodPositionAt`):
  for some data `(V, s)` of Definition 4.13 at the point, some chart `φ ⊇ V` of the structure,
  some presentation `T` of its partial quadrant and the level-1 lift `z` of `φ(a)`, the tangent
  space `T_z(φ(A ∩ V))` is in good position (Definition 3.21 inside `T_zO`, with an sc-complement
  in `T_zO`) to the partial cone `T_zO ∩ C_z`.  The same notion is used in the hypothesis (at
  `a`) and in the conclusion (at every `b`); the chart may vary with `b`.
- "an open `V(a) ⊆ X`": an open set containing `a` (the notation `V(a)`).
- Nothing looks false to me.
-/
namespace RoundTrip.V4_43
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

/-- Definition 3.21 inside the sc-subspace `M ⊆ E` (with the levels `M_m = M ∩ E_m`): `Y ⊆ M` is
a good complement of `N` in `M` with respect to `K`: an sc-complement of `N` in `M` with an
`ε > 0` such that `n ∈ K ↔ n + y ∈ K` whenever `|y|₀ ≤ ε|n|₀`. -/
def IsGoodComplementInB (E : ScBanach) (M : Submodule ℝ (E.lvl 0)) (K : Set (E.lvl 0))
    (N Y : Submodule ℝ (E.lvl 0)) : Prop :=
  Y ≤ M ∧ E.IsScSubspace Y ∧
    (∀ m : ℕ, E.levelSub N m ⊓ E.levelSub Y m = ⊥ ∧
      E.levelSub N m ⊔ E.levelSub Y m = E.levelSub M m) ∧
    ∃ ε > (0 : ℝ), ∀ n ∈ N, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖n‖ → (n ∈ K ↔ n + y ∈ K)

/-- Definition 3.21 inside `M`: `N ⊆ M` is in good position to the partial quadrant `K ⊆ M`:
`N ∩ K` has nonempty interior in `N` and `N` has a good complement in `M`. -/
def IsGoodPositionInB (E : ScBanach) (M : Submodule ℝ (E.lvl 0)) (K : Set (E.lvl 0))
    (N : Submodule ℝ (E.lvl 0)) : Prop :=
  N ≤ M ∧ (interior ((Subtype.val : N → E.lvl 0) ⁻¹' K)).Nonempty ∧
    ∃ Y : Submodule ℝ (E.lvl 0), IsGoodComplementInB E M K N Y

/-- **Definition 4.16**, in a chart: `T_aA = T_z(φ(A ∩ V))` is in good position to the partial
cone `C_zO = T_zO ∩ C_z` inside `T_aX = T_zO`, for some data `(V, s)` of Definition 4.13 at `a`,
some chart `φ ⊇ V`, some presentation `T` of its partial quadrant and the lift `z` of `φ(a)`. -/
def IsGoodPositionAtB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (A : Set X) (a : X) : Prop :=
  ∃ (V : Set X) (s : X → X) (φ : MChart X) (n : ℕ) (Wq : ScBanach)
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (z : φ.model.E.lvl 1)
    (N M : Submodule ℝ (φ.model.E.lvl 0)),
    IsScPlusRetractionOnB P s V ∧ s '' V = A ∩ V ∧ a ∈ V ∧
    P.IsChart φ ∧ V ⊆ φ.toPartialEquiv.source ∧
    φ.model.C = T.lvl 0 ⁻¹' quadrant n Wq 0 ∧
    φ.model.E.toBase 1 z = φ.toPartialEquiv a ∧
    (N : Set (φ.model.E.lvl 0)) =
      tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (A ∩ V)) z ∧
    (M : Set (φ.model.E.lvl 0)) = tangentSpace φ.model.E φ.model.C φ.model.O z ∧
    IsGoodPositionInB φ.model.E M
      ((M : Set (φ.model.E.lvl 0)) ∩ partialQuadrantAtWith T (φ.model.E.toBase 1 z)) N

/-- Remark 4.20: good position is an open condition along `A`. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X) (a : X), P.IsTame → IsSmoothSubmanifoldB P A → a ∈ A →
      IsGoodPositionAtB P A a →
        ∃ U : Set X, IsOpen U ∧ a ∈ U ∧ ∀ b ∈ U ∩ A, IsGoodPositionAtB P A b

end RoundTrip.V4_43
