import Polyfold
/-! Blind formalization of V12_34 (the text's Part II, §12.2, Theorem 12.2.13, p. 578 of the
Springer 2021 book; 2017: Theorem 12.5).

Text: with reflexive `1`-fibres and `X` tame: a reflexive auxiliary norm `N` for `W_{0,1}|∂X`
extends to a reflexive auxiliary norm `Ñ` of `W`.  (Proof: the local extension of Theorem 12.2.7,
reflexive local norms near interior points, partitions of unity as in Theorem 12.2.11.)

Choices:
- Setting as in `RoundTrip/Blind/V12_4.lean` (universe 0, `E : EpStrongBundle X B`,
  paracompactness of `𝐗 ₛ×_P W` as an instance hypothesis).  "`X` tame": `X.IsTame`;
  "reflexive `1`-fibres": `E.HasReflexiveFibers` (as in V12_32).
- ADDED hypothesis: `|X|` paracompact (`X.HasParacompactOrbitSpace`).  The quoted statement does
  not name it, but the theorem sits in the setting of Theorems 12.2.7 and 12.2.11 (both assume
  `|X|` paracompact), and its proof glues with "partitions of unity as in Theorem 12.2.11",
  which need it; I read it as presupposed.
- `∂X = X.PObj.boundary` (as in V12_9).  "reflexive auxiliary norm for `W_{0,1}|∂X`": the
  project's `EpStrongBundle.IsReflexiveAuxNormOn E ∂X N` (fields read with `#print`: the
  auxiliary norm conditions over `∂X`, `IsAuxNormOn` as in V12_9, plus
  `N(w) ≤ liminf N(w_k)` for mixed convergent `w_k → w` with all `P(w_k)`, `P(w)` in `∂X`).
- "reflexive auxiliary norm `Ñ` of `W`": `EpStrongBundle.IsReflexiveAuxNorm` (as in V12_32);
  "extends": `Ñ = N` on `W_{0,1}|∂X`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V12_34
open Polyfold

/-- **Theorem 12.2.13**: over a tame ep-groupoid (with paracompact orbit space) and with reflexive
`1`-fibres, a reflexive auxiliary norm for `W_{0,1}|∂X` extends to a reflexive auxiliary norm. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B),
    E.HasReflexiveFibers → X.IsTame → X.HasParacompactOrbitSpace →
    ∀ N : B.One → ℝ, E.IsReflexiveAuxNormOn X.PObj.boundary N →
      ∃ N' : B.One → ℝ, E.IsReflexiveAuxNorm N' ∧
        ∀ w : B.One, P (B.oneVal w) ∈ X.PObj.boundary → N' w = N w

end RoundTrip.V12_34
