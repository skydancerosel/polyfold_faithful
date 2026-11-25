import Polyfold
/-! Blind formalization of V12_32 (the text's Part II, §12.2, Theorem 12.2.11, p. 577 of the
Springer 2021 book; 2017: Theorem 12.4).

Text: with reflexive `1`-fibres and `|X|` paracompact: a reflexive auxiliary norm exists;
`h ↦ f(P(h)) N(h)` is one for every functorial continuous `f : X → (0, ∞)`; every auxiliary norm
`N'` has reflexive `N₁ ≤ N' ≤ N₂`.

Choices:
- Setting as in `RoundTrip/Blind/V12_4.lean` (universe 0, `E : EpStrongBundle X B`,
  paracompactness of `𝐗 ₛ×_P W` as an instance hypothesis).  "`|X|` paracompact":
  `X.HasParacompactOrbitSpace`.
- "reflexive `1`-fibres": the project's `EpStrongBundle.HasReflexiveFibers` (read with `#print`:
  Part I's `StrongBundle.HasReflexiveFibers` of the object bundle, Definition 5.1.4: a strong
  bundle atlas with reflexive `F₁`).
- "reflexive auxiliary norm" (Definition 12.2.10): the project's `EpStrongBundle.IsReflexiveAuxNorm`
  (fields read with `#print`: an auxiliary norm, `EpStrongBundle.IsAuxNorm`, with
  `N(w) ≤ liminf N(w_k)` in `EReal` whenever `w_k → w` in the mixed sense,
  `EpStrongBundle.MixedTendsto` = Part I's `StrongBundle.MixedTendsto`, Definition 12.2.8).
  "auxiliary norm": `EpStrongBundle.IsAuxNorm` (as in V12_4).  I trust these definitions.
- The second claim: `N` is a reflexive auxiliary norm (any one; the text's "`N`" refers to the
  reflexive auxiliary norm just obtained, and I read the claim for every such `N`).  "functorial
  continuous `f : X → (0, ∞)`": `f : Obj → ℝ` continuous on the object space, `f > 0`, and
  `f(s(φ)) = f(t(φ))` for every morphism `φ` (a functor to the trivial category `(0, ∞)`).  The
  new norm is `h ↦ f(P(h)) · N(h)` on `W_{0,1}`.
- The third claim: for every auxiliary norm `N'` there are reflexive auxiliary norms `N₁`, `N₂`
  with `N₁ ≤ N' ≤ N₂` pointwise on `W_{0,1}`.
- B is the conjunction of the three claims.  Nothing looks doubtful to me.
-/
namespace RoundTrip.V12_32
open Polyfold

/-- **Theorem 12.2.11**: existence of reflexive auxiliary norms, rescaling by positive
continuous functors, and two-sided reflexive bounds of auxiliary norms. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B),
    E.HasReflexiveFibers → X.HasParacompactOrbitSpace →
    -- a reflexive auxiliary norm exists
    (∃ N : B.One → ℝ, E.IsReflexiveAuxNorm N) ∧
    -- `h ↦ f(P(h)) N(h)` is a reflexive auxiliary norm for functorial continuous `f > 0`
    (∀ N : B.One → ℝ, E.IsReflexiveAuxNorm N →
      ∀ f : Obj → ℝ, Continuous f → (∀ x, 0 < f x) → (∀ φ : Mor, f (X.src φ) = f (X.tgt φ)) →
        E.IsReflexiveAuxNorm (fun h => f (P (B.oneVal h)) * N h)) ∧
    -- every auxiliary norm lies between two reflexive auxiliary norms
    (∀ N' : B.One → ℝ, E.IsAuxNorm N' →
      ∃ N₁ N₂ : B.One → ℝ, E.IsReflexiveAuxNorm N₁ ∧ E.IsReflexiveAuxNorm N₂ ∧
        ∀ h : B.One, N₁ h ≤ N' h ∧ N' h ≤ N₂ h)

end RoundTrip.V12_32
