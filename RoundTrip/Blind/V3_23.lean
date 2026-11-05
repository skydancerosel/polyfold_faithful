import Polyfold
/-! Blind formalization of V3_23 (the text's §3.2, Proposition 3.26, p. 80). Choices:
- Setting: `X X' : Type` (universe 0) with M-polyfold structures `PX`, `PX'`; `X` tame
  (`MPolyfold.IsTame`, Definition 2.37) as the quote says.  `X'` is *not* assumed tame (the quote
  does not say so; tameness is carried by sc-diffeomorphisms anyway), so `B` is the stronger reading.
- "An sc-diffeomorphism `ψ : X → X'`": `ψ` with inverse `ψ'`, both sc-smooth on all of `X`, `X'`
  (`MPolyfold.IsScDiffeoOn PX PX' ψ ψ' univ univ`; trusted).  `M ⊆ X`, `M' ⊆ X'` with `ψ(M) = M'`.
- "`n`-dimensional tangent germ property": the text's Definition 3.25 as written in my blind file
  V3_22 (`HasTangentGermPropertyB`, copied below with `IsGoodComplementB` from V3_20), not the
  project's `HasTangentGermProperty`: `M ⊆ X_∞`, and at every `x ∈ M` a compatible chart onto a tame
  retract with `φ(x) = 0`, an `n`-dimensional smooth `N` in good position with good (sc-)complement
  `Y`, a relatively open `V ∋ 0` in `N ∩ C` and continuous `δ : V → Y` with
  `φ(M ∩ U) = {v + δ(v)}`, `δ` an sc-smooth germ (Definition 3.2), `δ(0) = 0`, `Dδ(0) = 0`.
- The claim is the equivalence for every `n`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_23
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

/-- Proposition 3.26: the `n`-dimensional tangent germ property is invariant under
sc-diffeomorphisms `ψ : X → X'` of a tame M-polyfold `X`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {X' : Type} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] (PX' : MPolyfold X')
    (ψ : X → X') (ψ' : X' → X),
    PX.IsTame → PX.IsScDiffeoOn PX' ψ ψ' Set.univ Set.univ →
      ∀ (M : Set X) (M' : Set X'), ψ '' M = M' → ∀ n : ℕ,
        (HasTangentGermPropertyB PX' M' n ↔ HasTangentGermPropertyB PX M n)

end RoundTrip.V3_23
