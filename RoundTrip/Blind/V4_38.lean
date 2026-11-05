import Polyfold
/-! Blind formalization of V4_38 (the text's §4.2, Definition 4.16, p. 159).

Text: a smooth finite-dimensional submanifold `A` of a tame `X` is in good position at `a` if
`T_aA` is in good position to the partial quadrant `C_aX` in `T_aX`.

Choices:
- This item is a definition.  B says that the project's notion is the text's, in the text's
  setting: for `X` tame, `A` a smooth finite-dimensional submanifold and `a ∈ A`,
  `P.IsGoodPositionAt A a ↔ IsGoodPositionAtB P A a`.  The text asserts no further property here
  (chart independence is item V4_39).
- Setting: `X : Type` (universe 0, as in the other blind files of this chapter), Hausdorff
  paracompact, `P : MPolyfold X` tame (the project's `IsTame`, docstring = Definition 2.37: an
  equivalent atlas of charts modelled on tame retracts; a property of the given structure).
  `A`: my own `IsSmoothSubmanifoldB` (Definition 4.13), copied from V4_33 (sc⁺-retractions
  `IsScPlusRetractionOnB` as in V4_9).
- `T_aX` has no linear structure by itself, so (as in the text's use of the definition) it is read
  in a chart.  `IsGoodPositionAtB P A a`: there are data `(V, s)` of Definition 4.13 at `a`, a
  chart `φ` of the structure (`P.IsChart φ`) with `V` in its domain, a presentation
  `T : E ≅ ℝⁿ ⊕ W` of its partial quadrant `C` (`C = T⁻¹([0,∞)ⁿ ⊕ W)`) and the level-`1` point
  `z` over `φ(a)` such that, with
  * `T_aX ↦ M = T_zO` (`tangentSpace` of the chart's model `O`, Definition 2.17: the fibre over
    `z` of `TO`),
  * `T_aA ↦ N = T_z(φ(A ∩ V))` (`tangentSpace` of the retract `φ(A ∩ V)`, the model of the
    sub-chart `φ|A∩V` of the induced structure; the tangent map of the inclusion `A ↪ X` is the
    identity in these charts),
  * `C_aX ↦ C_zO = T_zO ∩ C_z`, the partial cone (Definition 2.27), `C_z` the partial quadrant of
    `z` (Definition 2.33, the project's `partialQuadrantAtWith T`: the half-spaces of the
    coordinates vanishing at `z`),
  `N` is in good position to `C_zO` inside the sc-space `T_zO` (Definition 3.21 read in `T_zO`,
  my `IsGoodPositionInB`): `N ⊆ T_zO`, `N ∩ C_zO` has nonempty interior in `N`, and `N` has in
  `T_zO` an sc-complement `Y` (an sc-subspace with `(T_zO)_m = N_m ⊕ Y_m` on every level) and an
  `ε > 0` with `n ∈ C_zO ↔ n + y ∈ C_zO` whenever `n ∈ N`, `y ∈ Y`, `|y|₀ ≤ ε|n|₀`.
  The complement is an sc-complement, as in Definition 3.21 (not merely algebraic).
- "for some data/chart/presentation": the existential form.  Since `T_aA`, `T_aX` and `C_aX` are
  carried isomorphically between charts (tangent maps of transitions), the condition holds in one
  chart iff in all; I chose the existential form as the literal chart transcription and did not
  build chart independence into the definition.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_38
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

/-- Definition 4.16: the project's "in good position at `a`" is the text's, for a smooth
finite-dimensional submanifold `A` of a tame `X` and `a ∈ A`. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X) (a : X), P.IsTame → IsSmoothSubmanifoldB P A → a ∈ A →
      (P.IsGoodPositionAt A a ↔ IsGoodPositionAtB P A a)

end RoundTrip.V4_38
