import Polyfold
/-! Blind formalization of V12_9 (the text's Part II, §12.2, Theorem 12.2.7, pp. 574–576 of the
Springer 2021 book; 2017: Theorem 12.3).

Text: for a strong bundle over a tame ep-groupoid with paracompact `|X|`, an auxiliary norm for
`W|∂X` extends to an auxiliary norm of `W`.

Choices:
- Setting as in `RoundTrip/Blind/V12_4.lean` (universe 0, `E : EpStrongBundle X B`,
  paracompactness of `𝐗 ₛ×_P W` as an instance hypothesis).
- "tame ep-groupoid": `X.IsTame` (Definition 7.1.6, read with `#print`: the object M-polyfold is
  tame).  "`|X|` paracompact": `X.HasParacompactOrbitSpace` (as in V12_4).
- `∂X`: the boundary of the object M-polyfold, `X.PObj.boundary` (read with `#print`:
  `{x | 1 ≤ d(x)}`); it is saturated, so `W|∂X` is invariant under the morphisms.
- "auxiliary norm for `W|∂X`": `W|∂X` is not a strong bundle, so I read it as Definition 12.2.1
  over `∂X`: the project's `EpStrongBundle.IsAuxNormOn E ∂X N` (fields read with `#print`: `N`
  continuous on `W_{0,1}|∂X`, a complete norm on the fibres over `∂X`, `h_k → 0_y` for
  `h_k ∈ W_{0,1}|∂X`, `P(h_k) → y ∈ ∂X`, `N(h_k) → 0`, and `N(h) = N(k)` for `h = μ(φ, k)`,
  `P(k) ∈ ∂X`).  Values of `N` off `W_{0,1}|∂X` are irrelevant.
- "auxiliary norm of `W`": `EpStrongBundle.IsAuxNorm` (as in V12_4).  "extends": `Ñ = N` on
  `W_{0,1}|∂X`.
- The proof sketch (local extension `N(rq(u), A(rq(u))w) + ‖w − A(rq(u))w‖_{F₁}`, averaging over
  `G_{x₀}`, gluing) is not part of the claim.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V12_9
open Polyfold

/-- **Theorem 12.2.7**: over a tame ep-groupoid with paracompact orbit space, every auxiliary
norm for `W|∂X` extends to an auxiliary norm of `W`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B),
    X.IsTame → X.HasParacompactOrbitSpace →
    ∀ N : B.One → ℝ, E.IsAuxNormOn X.PObj.boundary N →
      ∃ N' : B.One → ℝ, E.IsAuxNorm N' ∧
        ∀ w : B.One, P (B.oneVal w) ∈ X.PObj.boundary → N' w = N w

end RoundTrip.V12_9
