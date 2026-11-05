import Polyfold
/-! Blind formalization of V4_44 (the text's §4.2, Definition 4.21, p. 161).

Text: `A` is in general position at `a` if `T_aA` has in `T_aX` an sc-complement contained in
`T^R_aX` (Definition 2.38).

Choices:
- This item is a definition.  B says that the project's notion is the text's, in the text's
  setting: for `X` tame, `A` a smooth finite-dimensional submanifold and `a ∈ A`,
  `P.IsGeneralPositionAt A a ↔ IsGeneralPositionAtB P A a`.  The text asserts no further property
  here (chart independence is item V4_45).
- Setting: `X : Type` (universe 0, as in the other blind files of this chapter), Hausdorff
  paracompact, `P : MPolyfold X`.  I assume `X` tame (project's `IsTame`, docstring =
  Definition 2.37): the item does not say it, but §4.2 works with tame `X` (Definition 4.16 says
  "of a tame `X`", Theorem 4.22 "of the tame `X`"), and the reduced tangent space `T^R_aX` of
  Definition 2.38 is the notion for tame M-polyfolds.  `A`: my own `IsSmoothSubmanifoldB`
  (Definition 4.13), copied from V4_33.
- In a chart, as for Definition 4.16 (my V4_38): `IsGeneralPositionAtB P A a` asks for some data
  `(V, s)` of Definition 4.13 at `a`, a chart `φ` of the structure with `V` in its domain, a
  presentation `T : E ≅ ℝⁿ ⊕ W` of its partial quadrant `C` and the level-1 lift `z` of `φ(a)`,
  with
  * `T_aX ↦ M = T_zO` (`tangentSpace` of the chart's model, Definition 2.17),
  * `T_aA ↦ N = T_z(φ(A ∩ V))` (`tangentSpace` of the image of `A`, the model of the sub-chart),
  * `T^R_aX ↦ T_zO ∩ E_z` (Definitions 2.27, 2.38), `E_z` the vectors whose coordinates vanish
    wherever those of `z` vanish (the project's `minimalSubspaceWith T`, docstring checked),
  and an sc-subspace `B'` of `E` contained in `T_zO ∩ E_z` with `(T_zO)_m = N_m ⊕ B'_m` on every
  level `m` (an sc-complement of `N` inside the sc-space `T_zO`, whose levels are `T_zO ∩ E_m`).
- "for some data/chart/presentation": the existential form, the literal chart transcription;
  chart independence (V4_45) is not built in.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_44
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

/-- `N` has in `M` (levels `M_m = M ∩ E_m`) an sc-complement contained in `K`: an sc-subspace
`B' ⊆ K` with `M_m = N_m ⊕ B'_m` on every level. -/
def HasScComplementInWithinB (E : ScBanach) (N M K : Submodule ℝ (E.lvl 0)) : Prop :=
  ∃ B' : Submodule ℝ (E.lvl 0), E.IsScSubspace B' ∧ B' ≤ K ∧
    ∀ m : ℕ, E.levelSub N m ⊓ E.levelSub B' m = ⊥ ∧
      E.levelSub N m ⊔ E.levelSub B' m = E.levelSub M m

/-- **Definition 4.21**, in a chart: `T_aA = T_z(φ(A ∩ V))` has in `T_aX = T_zO` an sc-complement
contained in `T^R_aX = T_zO ∩ E_z`, for some data `(V, s)` of Definition 4.13 at `a`, some chart
`φ ⊇ V`, some presentation `T` of its partial quadrant and the lift `z` of `φ(a)`. -/
def IsGeneralPositionAtB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
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
    HasScComplementInWithinB φ.model.E N M (M ⊓ minimalSubspaceWith T (φ.model.E.toBase 1 z))

/-- Definition 4.21: the project's "in general position at `a`" is the text's, for a smooth
finite-dimensional submanifold `A` of a tame `X` and `a ∈ A`. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X) (a : X), P.IsTame → IsSmoothSubmanifoldB P A → a ∈ A →
      (P.IsGeneralPositionAt A a ↔ IsGeneralPositionAtB P A a)

end RoundTrip.V4_44
