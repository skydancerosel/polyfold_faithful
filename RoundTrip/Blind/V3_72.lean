import Polyfold
/-! Blind formalization of V3_72 (the text's §3.2, Theorem 3.27, p. 81, for a fixed dimension `n`).
Choices:
- Setting: `X : Type` (universe 0; nothing depends on it) with an M-polyfold structure `PX`,
  `M : Set X`, `n : ℕ`.  `X` tame (`MPolyfold.IsTame`, Definition 2.37), the setting of
  Theorem 3.27 and Definition 3.25.
- "the `n`-dimensional tangent germ property" (Definition 3.25): written out here
  (`HasTangentGermPropertyB`, data `IsGermData`) exactly as in the earlier blind file V3_22, not via
  the project's `HasTangentGermProperty`: `M ⊆ X_∞`, and at every `x ∈ M` a chart
  `φ : (U, x) → (O, 0)` of the structure (`IsChart`) onto a tame retract (`IsTameRetract`), an
  `n`-dimensional smooth `N ⊆ E` (`N ⊆ E_∞`) in good position to `C` (`N ∩ C` has nonempty interior
  in `N`) with a good complement `Y` (Definition 3.21, `IsGoodComplementB`: an sc-complement plus the
  `ε`-property), a relatively open `V ∋ 0` in `N ∩ C`, a continuous `δ : V → Y` with
  (i) `φ(M ∩ U) = {v + δ(v) | v ∈ V}` and (ii) `δ` an sc-smooth germ on some germ of neighbourhoods of
  `0` in `N ∩ C` inside `V` (Definition 3.2, project `IsScSmoothGerm`), `δ(0) = 0`, `Dδ(0) = 0`.
- Conclusion: `M` is a sub-M-polyfold (`IsSubMPolyfold`, Definition 2.20), paracompact (needed for
  the induced structure `subPolyfold`, Proposition 2.21; asserted), the induced structure is tame
  (`MPolyfold.IsTame`), and it is equivalent to an `n`-dimensional manifold with boundary with
  corners: an equivalent atlas of corner charts (`MChart.IsCornerChart`, Definition 4.1) modelled
  on `n`-dimensional spaces (`HasCornerStructureOfDim`, defined here).
- "with the charts `π ∘ φ`": for every `x ∈ M` and *every* data `(φ, N, Y, V, δ)` at `x`, the map
  `y ↦ π(φ(y))` (`π : E → N` the projection along `Y`, characterized by `φ(y) − π(φ(y)) ∈ Y`) is, on
  some open neighbourhood of `x` in `M`, a chart of the induced structure (`IsChart`) modelled on a
  relatively open subset of the partial quadrant `N ∩ C` of `N` with the constant sc-structure
  (`IsProjChartAt`).  These charts (one data exists at every point) form an `n`-dimensional corner
  atlas equivalent to the induced structure.
- Doubt (as in V3_24): Definition 3.25 gives `δ` sc-smooth only as a germ at `0`; the charts are
  claimed only on a neighbourhood of `x` ("around `x`"), not on all of `M ∩ U` (on all of `M ∩ U`
  the claim can fail: see my report on V3_73).
-/
namespace RoundTrip.V3_72
open Polyfold

/-- **Definition 3.21**: `P` is a good complement of the finite-dimensional `N` with respect to
`C`: an sc-complement (topological complement if `N` is not smooth) with the `ε`-property. -/
def IsGoodComplementB (E : ScBanach) (C : Set (E.lvl 0)) (N P : Submodule ℝ (E.lvl 0)) : Prop :=
  (N ≤ E.smooth → E.IsScSplitting N P) ∧
  (¬ N ≤ E.smooth → IsCompl N P ∧ IsClosed (P : Set (E.lvl 0))) ∧
  ∃ ε > (0 : ℝ), ∀ n ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + p ∈ C)

/-- **Definition 3.25 (2)**: `(φ, N, Y, V, δ)` are data of the `n`-dimensional tangent germ property
of `M` at `x`. -/
def IsGermData {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (M : Set X) (n : ℕ) (x : X) (φ : MChart X)
    (N Yc : Submodule ℝ (φ.model.E.lvl 0)) [FiniteDimensional ℝ N] (V : Set N)
    (δ : N → φ.model.E.lvl 0) : Prop :=
  PX.IsChart φ ∧ x ∈ φ.source ∧ φ.toPartialEquiv x = 0 ∧
  IsTameRetract φ.model.E φ.model.C φ.model.O ∧
  Module.finrank ℝ N = n ∧ N ≤ φ.model.E.smooth ∧
  (interior ((Subtype.val : N → φ.model.E.lvl 0) ⁻¹' φ.model.C)).Nonempty ∧
  IsGoodComplementB φ.model.E φ.model.C N Yc ∧
  (∃ O' : Set N, IsOpen O' ∧ V = O' ∩ (Subtype.val ⁻¹' φ.model.C)) ∧ (0 : N) ∈ V ∧
  (∀ v ∈ V, δ v ∈ Yc) ∧ ContinuousOn δ V ∧
  -- (i)
  φ.toPartialEquiv '' (M ∩ φ.source) = (fun v : N => (v : φ.model.E.lvl 0) + δ v) '' V ∧
  -- (ii)
  δ 0 = 0 ∧
  ∃ G : ScNbhdGerm (ScBanach.const N) ((Subtype.val : N → φ.model.E.lvl 0) ⁻¹' φ.model.C),
    (∀ v ∈ G.U 0, v ∈ V) ∧ IsScSmoothGerm (F := φ.model.E) G δ ∧
    ∃ D : (ScBanach.const N).lvl 1 → (ScBanach.const N).lvl 0 →L[ℝ] φ.model.E.lvl 0,
      IsSc1GermWith G δ D ∧ D 0 = 0

/-- **Definition 3.25**: `M ⊆ X` has the `n`-dimensional tangent germ property. -/
def HasTangentGermPropertyB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (M : Set X) (n : ℕ) : Prop :=
  M ⊆ PX.smoothSet ∧
  ∀ x ∈ M, ∃ (φ : MChart X) (N Yc : Submodule ℝ (φ.model.E.lvl 0)) (_ : FiniteDimensional ℝ N)
    (V : Set N) (δ : N → φ.model.E.lvl 0), IsGermData PX M n x φ N Yc V δ

/-- The M-polyfold `QZ` is equivalent to an `n`-dimensional manifold with boundary with corners: it
has an equivalent atlas of corner charts (Definition 4.1) modelled on `n`-dimensional spaces. -/
def HasCornerStructureOfDim {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (QZ : MPolyfold Z) (n : ℕ) : Prop :=
  ∃ A : MAtlas Z, A.Equiv QZ.atlas ∧
    ∀ χ ∈ A.charts, χ.IsCornerChart ∧ Module.finrank ℝ (χ.model.E.lvl 0) = n

/-- On some open neighbourhood of `x` in `M`, `y ↦ π(φ(y))` (`π : E → N` the projection along `Y`)
is a chart of the M-polyfold `QM` modelled on a relatively open subset of the partial quadrant
`N ∩ C` of `N` (constant sc-structure). -/
def IsProjChartAt {X : Type} [TopologicalSpace X] {M : Set X} [T2Space M] [ParacompactSpace M]
    (QM : MPolyfold M) (φ : MChart X) (N Yc : Submodule ℝ (φ.model.E.lvl 0))
    [FiniteDimensional ℝ N] (x : M) : Prop :=
  ∃ (Vn : Set N)
    (hV : IsRelOpenInQuadrant (ScBanach.const N)
      ((Subtype.val : N → φ.model.E.lvl 0) ⁻¹' φ.model.C) Vn)
    (e : PartialEquiv M N) (h1 : IsOpen e.source) (h2 : e.target = Vn)
    (h3 : ContinuousOn e e.source) (h4 : ContinuousOn e.symm Vn),
    x ∈ e.source ∧
    (∀ y ∈ e.source, (y : X) ∈ φ.source ∧
      φ.toPartialEquiv (y : X) - ((e y : N) : φ.model.E.lvl 0) ∈ Yc) ∧
    QM.IsChart ⟨LocalModel.ofRelOpen hV, e, h1, h2, h3, h4⟩

/-- Theorem 3.27 (dimension `n`): in a tame M-polyfold, a subset with the `n`-dimensional tangent
germ property is a sub-M-polyfold whose induced structure is tame and equivalent to an
`n`-dimensional manifold with boundary with corners, with the charts `π ∘ φ`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    (M : Set X) (n : ℕ),
    PX.IsTame → HasTangentGermPropertyB PX M n →
    ∃ (hM : PX.IsSubMPolyfold M) (_ : ParacompactSpace M),
      (PX.subPolyfold hM).IsTame ∧ HasCornerStructureOfDim (PX.subPolyfold hM) n ∧
      ∀ (x : X) (hx : x ∈ M) (φ : MChart X) (N Yc : Submodule ℝ (φ.model.E.lvl 0))
        [FiniteDimensional ℝ N] (V : Set N) (δ : N → φ.model.E.lvl 0),
        IsGermData PX M n x φ N Yc V δ →
        IsProjChartAt (PX.subPolyfold hM) φ N Yc ⟨x, hx⟩

end RoundTrip.V3_72
