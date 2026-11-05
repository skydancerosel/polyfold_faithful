import Polyfold
/-! Blind formalization of V3_22 (the text's §3.2, Definition 3.25, p. 79). Choices:
- This item is a definition.  `B` states that the project's notion of Definition 3.25
  (`MPolyfold.HasTangentGermProperty`, the declaration whose docstring is "Definition 3.25") is the
  text's notion, written here as `HasTangentGermPropertyB`, for subsets of a *tame* M-polyfold (the
  text's setting "`M ⊆ X` (tame)"; `MPolyfold.IsTame`, Definition 2.37, a hypothesis of `B`).
- Setting: `X : Type` (universe 0) with an M-polyfold structure `PX`, `M : Set X`, `n : ℕ`.
- `M ⊆ X_∞`: `M ⊆ PX.smoothSet`.
- "A chart `φ : (U, x) → (O, 0)` onto a tame retract `(O, C, E)`": an M-polyfold chart `φ`
  compatible with the structure (`MPolyfold.IsChart`), `U` its domain, `x ∈ U`, `φ(x) = 0`, whose
  local model `(O, C, E)` is a tame retract (`IsTameRetract`, Definition 2.34; trusted).
- "An `n`-dimensional smooth `N ⊆ E` in good position to `C` with good complement `Y`,
  `E = N ⊕ Y`": `N, Y` subspaces of `E₀`, `N` finite-dimensional of dimension `n`, `N ⊆ E_∞`,
  `N ∩ C` with nonempty interior in `N`, and `Y` a good complement of `N` in the sense of Definition
  3.21 as written in my blind file V3_20 (`IsGoodComplementB`, copied below; for smooth `N` it says
  `E = N ⊕ Y` is an sc-splitting, plus the `ε`-property) — this also gives `E = N ⊕ Y`.
- "A relatively open `V ∋ 0` in `N ∩ C`": `V ⊆ N`, `V = O' ∩ (N ∩ C)` for an open `O' ⊆ N`.
- "A continuous `δ : V → Y`": `δ : N → E₀` (values off `V` irrelevant) with `δ(V) ⊆ Y`, continuous on
  `V`.
- (i) `φ(M ∩ U) = {v + δ(v) | v ∈ V}`.
- (ii) "`δ : O(N ∩ C, 0) → (Y, 0)` an sc^∞-germ": Definition 3.2 (project `ScNbhdGerm`,
  `IsScSmoothGerm`; trusted as Definition 3.2): an sc-smooth germ on a germ of neighbourhoods of `0`
  in the partial quadrant `N ∩ C` of `N` (constant sc-structure `ScBanach.const N`, levels inside
  `V`), as a map into `E` with values in `Y` (for the sc-subspace `Y` with its induced levels this is
  the same as an sc-smooth germ into `Y`); `δ(0) = 0`; `Dδ(0) = 0`: a derivative family `D` of the
  sc¹-germ `δ` (`IsSc1GermWith`) vanishes at `0`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_22
open Polyfold

/-- **Definition 3.21**: `P` is a good complement of the finite-dimensional `N` with respect to
`C`: an sc-complement (topological complement if `N` is not smooth) with the `ε`-property. -/
def IsGoodComplementB (E : ScBanach) (C : Set (E.lvl 0)) (N P : Submodule ℝ (E.lvl 0)) : Prop :=
  (N ≤ E.smooth → E.IsScSplitting N P) ∧
  (¬ N ≤ E.smooth → IsCompl N P ∧ IsClosed (P : Set (E.lvl 0))) ∧
  ∃ ε > (0 : ℝ), ∀ n ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + p ∈ C)

/-- **Definition 3.25**: `M ⊆ X` has the `n`-dimensional tangent germ property. -/
def HasTangentGermPropertyB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (M : Set X) (n : ℕ) : Prop :=
  M ⊆ PX.smoothSet ∧
  ∀ x ∈ M, ∃ φ : MChart X, PX.IsChart φ ∧ x ∈ φ.source ∧ φ.toPartialEquiv x = 0 ∧
    IsTameRetract φ.model.E φ.model.C φ.model.O ∧
    ∃ (N Yc : Submodule ℝ (φ.model.E.lvl 0)) (_ : FiniteDimensional ℝ N),
      Module.finrank ℝ N = n ∧ N ≤ φ.model.E.smooth ∧
      (interior ((Subtype.val : N → φ.model.E.lvl 0) ⁻¹' φ.model.C)).Nonempty ∧
      IsGoodComplementB φ.model.E φ.model.C N Yc ∧
      ∃ V : Set N, (∃ O' : Set N, IsOpen O' ∧ V = O' ∩ (Subtype.val ⁻¹' φ.model.C)) ∧
        (0 : N) ∈ V ∧
      ∃ δ : N → φ.model.E.lvl 0, (∀ v ∈ V, δ v ∈ Yc) ∧ ContinuousOn δ V ∧
        -- (i)
        φ.toPartialEquiv '' (M ∩ φ.source) = (fun v : N => (v : φ.model.E.lvl 0) + δ v) '' V ∧
        -- (ii)
        δ 0 = 0 ∧
        ∃ G : ScNbhdGerm (ScBanach.const N) ((Subtype.val : N → φ.model.E.lvl 0) ⁻¹' φ.model.C),
          (∀ v ∈ G.U 0, v ∈ V) ∧ IsScSmoothGerm (F := φ.model.E) G δ ∧
          ∃ D : (ScBanach.const N).lvl 1 → (ScBanach.const N).lvl 0 →L[ℝ] φ.model.E.lvl 0,
            IsSc1GermWith G δ D ∧ D 0 = 0

/-- Definition 3.25: in a tame M-polyfold, the project's `n`-dimensional tangent germ property is
the text's. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X),
    PX.IsTame → ∀ (M : Set X) (n : ℕ),
      (PX.HasTangentGermProperty M n ↔ HasTangentGermPropertyB PX M n)

end RoundTrip.V3_22
