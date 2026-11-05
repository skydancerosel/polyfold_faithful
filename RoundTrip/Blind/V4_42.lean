import Polyfold
/-! Blind formalization of V4_42 (the text's §4.2, Lemma 4.19, p. 160, in the proof of
Theorem 4.18).

Text: `N = Tφ(a)(T_aA)` is in good position to `C`, and `Y ⊕ Z` is a good complement
(`Z ⊆ C` the sc-complement of `T_0O` of Proposition 2.35).

Choices:
- Context (proof of Theorem 4.18): `X` tame, `A ⊆ X` a smooth finite-dimensional submanifold in
  good position at `a ∈ A` (Definition 4.16), `φ : V' → O ⊆ C ⊆ E` a tame chart around `a` with
  `φ(a) = 0`; `Y` the good complement of `N` in `T_0O` given by Definition 4.16 in this chart;
  `Z` an sc-complement of `T_0O` in `E` with `Z ⊆ C` (Proposition 2.35, tameness of the chart).
- Setting: `X : Type` (universe 0, as in the other blind files of this chapter), Hausdorff
  paracompact, `P : MPolyfold X`, `P.IsTame` (project's `IsTame`, docstring = Definition 2.37).
  `A`: my own `IsSmoothSubmanifoldB` (Definition 4.13, copied from V4_33), with data `(V, s)` at
  `a` (`IsScPlusRetractionOnB`, `s(V) = A ∩ V`).  The chart: `P.IsChart φ`, its model a tame
  retract (`IsTameRetract`, Definition 2.34), `V` in its domain, `φ(a) = 0`.
- `N = Tφ(a)(T_aA)`: `T_0(φ(A ∩ V))` (`tangentSpace` of the retract `φ(A ∩ V)` at the level-1
  point `0`, Definition 2.17; it is the image of `T_aA` under `Tφ(a)`, since `φ|A∩V` is a chart of
  the induced structure).  `T_0O`: `tangentSpace` of the chart's model `O` at `0`.  Both are
  given as submodules `N`, `M` whose underlying sets are these tangent spaces.
- "`A` in good position at `a`" is used only in the chart `φ` (as the text does): `N ⊆ T_0O`,
  `N ∩ C_0O` has nonempty interior in `N`, and `Y` is a good complement of `N` in `T_0O`
  (sc-complement inside `T_0O`, levelwise `(T_0O)_m = N_m ⊕ Y_m`, with an `ε`) with respect to
  the partial cone `C_0O = T_0O ∩ C_0`.  For the point `0` every coordinate vanishes, so
  `C_0 = C` and `C_0O = T_0O ∩ C`; I write `T_0O ∩ C`.  I did not hypothesize
  `IsGoodPositionAt` itself: B takes the chart form at `φ` directly (no chart independence is
  needed; this is a weaker hypothesis than "in good position at `a`" plus chart independence).
- `Z`: `E = T_0O ⊕ Z` an sc-splitting (`E.IsScSplitting`, Definition 1.5) and `Z ⊆ C` (as sets;
  for a subspace this forces `Z ⊆ {0} ⊕ W`).
- Conclusions (Definition 3.21 in `E`, with an sc-complement): "`N` is in good position to `C`"
  — my `IsGoodPositionB` (copied from V4_27): `N ∩ C` has nonempty interior in `N` and `N` has a
  good sc-complement; "`Y ⊕ Z` is a good complement": `E = N ⊕ (Y + Z)` is an sc-splitting and
  for some `ε > 0`, `n ∈ C ↔ n + p ∈ C` whenever `n ∈ N`, `p ∈ Y + Z`, `|p|₀ ≤ ε|n|₀`.
  `Y ⊕ Z` is the submodule `Y ⊔ Z` (the sum is direct as `Y ⊆ T_0O`).
- Nothing looks false to me (a vector of `Z ⊆ {0} ⊕ W` does not change membership in `C`, and the
  projection of `Y ⊕ Z` onto `Y` is bounded).
-/
namespace RoundTrip.V4_42
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

/-- Definition 3.21 inside the sc-subspace `M ⊆ E` (levels `M_m = M ∩ E_m`): `Y ⊆ M` is a good
complement of `N` in `M` with respect to `K`. -/
def IsGoodComplementInB (E : ScBanach) (M : Submodule ℝ (E.lvl 0)) (K : Set (E.lvl 0))
    (N Y : Submodule ℝ (E.lvl 0)) : Prop :=
  Y ≤ M ∧ E.IsScSubspace Y ∧
    (∀ m : ℕ, E.levelSub N m ⊓ E.levelSub Y m = ⊥ ∧
      E.levelSub N m ⊔ E.levelSub Y m = E.levelSub M m) ∧
    ∃ ε > (0 : ℝ), ∀ n ∈ N, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖n‖ → (n ∈ K ↔ n + y ∈ K)

/-- Definition 3.21 (the complement): `P'` is a good complement of `N` in `E` with respect to
`C`: `E = N ⊕ P'` is an sc-splitting and `n ∈ C ↔ n + p ∈ C` whenever `|p|₀ ≤ ε|n|₀`. -/
def IsGoodComplementB (E : ScBanach) (C : Set (E.lvl 0)) (N P' : Submodule ℝ (E.lvl 0)) :
    Prop :=
  E.IsScSplitting N P' ∧
    ∃ ε > (0 : ℝ), ∀ n ∈ N, ∀ p ∈ P', ‖p‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + p ∈ C)

/-- Definition 3.21 with an sc-complement: `N ∩ C` has nonempty interior in `N`, and `N` has an
sc-complement `Y` with `n ∈ C ↔ n + y ∈ C` whenever `|y|₀ ≤ ε|n|₀`. -/
def IsGoodPositionB (E : ScBanach) (C : Set (E.lvl 0)) (N : Submodule ℝ (E.lvl 0)) : Prop :=
  (interior ((Subtype.val : N → E.lvl 0) ⁻¹' C)).Nonempty ∧
    ∃ Y : Submodule ℝ (E.lvl 0), E.IsScSplitting N Y ∧
      ∃ ε > (0 : ℝ), ∀ n ∈ N, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + y ∈ C)

/-- Lemma 4.19: in a tame chart centred at `a`, `N = Tφ(a)(T_aA)` is in good position to `C`,
and `Y ⊕ Z` is a good complement of `N` (`Y` the good complement of `N` in `T_0O`, `Z ⊆ C` an
sc-complement of `T_0O`). -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X), P.IsTame → IsSmoothSubmanifoldB P A →
    ∀ (a : X) (V : Set X) (s : X → X) (φ : MChart X),
      IsScPlusRetractionOnB P s V → s '' V = A ∩ V → a ∈ A ∩ V →
      P.IsChart φ → IsTameRetract φ.model.E φ.model.C φ.model.O →
      V ⊆ φ.toPartialEquiv.source → φ.toPartialEquiv a = 0 →
    ∀ (N M Y Z : Submodule ℝ (φ.model.E.lvl 0)),
      -- `N = Tφ(a)(T_aA)`, `M = T_0O`
      (N : Set (φ.model.E.lvl 0)) =
        tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (A ∩ V)) 0 →
      (M : Set (φ.model.E.lvl 0)) = tangentSpace φ.model.E φ.model.C φ.model.O 0 →
      -- good position at `a`, in `φ`: `N` in good position to `C_0O = T_0O ∩ C` in `T_0O`,
      -- with the good complement `Y`
      N ≤ M →
      (interior ((Subtype.val : N → φ.model.E.lvl 0) ⁻¹' ((M : Set _) ∩ φ.model.C))).Nonempty →
      IsGoodComplementInB φ.model.E M ((M : Set _) ∩ φ.model.C) N Y →
      -- `Z ⊆ C` an sc-complement of `T_0O`
      φ.model.E.IsScSplitting M Z → (Z : Set (φ.model.E.lvl 0)) ⊆ φ.model.C →
        IsGoodPositionB φ.model.E φ.model.C N ∧
        IsGoodComplementB φ.model.E φ.model.C N (Y ⊔ Z)

end RoundTrip.V4_42
