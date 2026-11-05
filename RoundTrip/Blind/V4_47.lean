import Polyfold
/-! Blind formalization of V4_47 (the text's §4.2, proof of Theorem 4.22 (3), p. 164).

Text: `T_aO = T_aA + (W ∩ T_aO) = T_aA + T^R_aO`, "implying that `T_aA` has in `T_aO` a
sc-complement which is contained in `T^R_aO`".

Choices:
- Context (proof of Theorem 4.22): `X` tame, `A` a smooth finite-dimensional submanifold, a tame
  chart `φ` with model `(O, C, E)`, `E = ℝⁿ ⊕ W`, `C = [0,∞)ⁿ ⊕ W`, and points `a ∈ A` (in the
  neighbourhood `U` of the theorem) at which the preceding step (item V4_49) has shown
  `T_aA + W = E`.  The step formalized here is: from `T_aA + W = E` deduce the two equalities and
  the sc-complement.  B takes `T_aA + W = E` as its hypothesis instead of the centring
  `φ(x) = 0`, general position at `x` and `a ∈ U`, which the text uses only to obtain it.
- Setting: `X : Type` (universe 0, as in the other blind files of this chapter), Hausdorff
  paracompact, `P : MPolyfold X`, `P.IsTame` (project's `IsTame`, docstring = Definition 2.37).
  `A`: my own `IsSmoothSubmanifoldB` (Definition 4.13, copied from V4_33), with data `(V, s)`
  (`IsScPlusRetractionOnB`, `s(V) = A ∩ V`).  The chart: `P.IsChart φ`, model a tame retract
  (`IsTameRetract`, Definition 2.34), `V` in its domain, a presentation `T : E ≅ ℝⁿ ⊕ W'` of `C`
  (`C = T⁻¹([0,∞)ⁿ ⊕ W')`).  The text identifies `E` with `ℝⁿ ⊕ W`; its `W ⊆ E` is
  `T⁻¹({0} ⊕ W')`, the vectors all of whose half-line coordinates vanish: the project's
  `minimalSubspaceWith T 0` (docstring: vectors whose coordinates vanish where those of `0` do,
  i.e. all of them).
- `a ∈ A ∩ V`, `z` the level-1 lift of `φ(a)`; `T_aO`: `M = T_zO` (`tangentSpace` of the chart's
  model, Definition 2.17); `T_aA`: `N = T_z(φ(A ∩ V))` (`tangentSpace` of the image of `A`);
  `T^R_aO = T_zO ∩ E_z` (Definitions 2.27, 2.38; `E_z = minimalSubspaceWith T z`).
- Hypothesis "`T_aA + W = E`": `N ⊔ W = ⊤` in `E₀`.
- Conclusions: (1) `T_aO = T_aA + (W ∩ T_aO)`, (2) `T_aA + (W ∩ T_aO) = T_aA + T^R_aO` (as
  submodules of `E₀`), and (3) `T_aA` has in `T_aO` an sc-complement contained in `T^R_aO`: an
  sc-subspace `B' ⊆ T_zO ∩ E_z` of `E` with `(T_zO)_m = N_m ⊕ B'_m` on every level (the chart form
  of Definition 4.21, as in my V4_44).
- Nothing looks false to me.
-/
namespace RoundTrip.V4_47
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

/-- Proof of Theorem 4.22 (3): in a tame chart, `T_aA + W = E` gives
`T_aO = T_aA + (W ∩ T_aO) = T_aA + T^R_aO`, so `T_aA` has in `T_aO` an sc-complement contained
in `T^R_aO`. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X), P.IsTame → IsSmoothSubmanifoldB P A →
    ∀ (V : Set X) (s : X → X) (φ : MChart X) (n : ℕ) (Wq : ScBanach)
      (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
      IsScPlusRetractionOnB P s V → s '' V = A ∩ V →
      P.IsChart φ → IsTameRetract φ.model.E φ.model.C φ.model.O →
      V ⊆ φ.toPartialEquiv.source → φ.model.C = T.lvl 0 ⁻¹' quadrant n Wq 0 →
    ∀ (a : X) (z : φ.model.E.lvl 1) (N M : Submodule ℝ (φ.model.E.lvl 0)),
      a ∈ A ∩ V → φ.model.E.toBase 1 z = φ.toPartialEquiv a →
      -- `N = T_aA`, `M = T_aO`
      (N : Set (φ.model.E.lvl 0)) =
        tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (A ∩ V)) z →
      (M : Set (φ.model.E.lvl 0)) = tangentSpace φ.model.E φ.model.C φ.model.O z →
      -- `T_aA + W = E`
      N ⊔ minimalSubspaceWith T 0 = ⊤ →
        -- `T_aO = T_aA + (W ∩ T_aO)`
        M = N ⊔ (minimalSubspaceWith T 0 ⊓ M) ∧
        -- `T_aA + (W ∩ T_aO) = T_aA + T^R_aO`
        N ⊔ (minimalSubspaceWith T 0 ⊓ M) =
          N ⊔ (M ⊓ minimalSubspaceWith T (φ.model.E.toBase 1 z)) ∧
        -- `T_aA` has in `T_aO` an sc-complement contained in `T^R_aO`
        HasScComplementInWithinB φ.model.E N M
          (M ⊓ minimalSubspaceWith T (φ.model.E.toBase 1 z))

end RoundTrip.V4_47
