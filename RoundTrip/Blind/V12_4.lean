import Polyfold
/-! Blind formalization of V12_4 (the text's Part II, §12.2, Theorem 12.2.2, p. 570 of the
Springer 2021 book; 2017: Theorem 12.1).

Text: every strong bundle over an ep-groupoid with paracompact orbit space admits an auxiliary
norm.

Choices:
- Setting as in `RoundTrip/Blind/V8_20.lean`, `V10_25.lean`: `X : EpGroupoid Obj Mor` with
  `Obj Mor : Type` (universe 0), `W : Type` Hausdorff paracompact, `P : W → Obj` with the fibre
  linear structures as instances, `B : StrongBundle X.PObj P` and `E : EpStrongBundle X B`
  (Definition 8.3.1, `μ = E.μ`); paracompactness of `𝐗 ₛ×_P W` is an instance hypothesis (true,
  and needed to form `EpStrongBundle`).
- "ep-groupoid with paracompact orbit space": the project's `EpGroupoid.HasParacompactOrbitSpace`
  (Definition 7.5.1; read with `#print`: `ParacompactSpace X.OrbitSpace`, the orbit space with
  its quotient topology; (1)–(4) of Definition 7.5.1 are the ep-groupoid axioms already in
  `EpGroupoid`).
- "auxiliary norm" (Definition 12.2.1 = 2021 Definition 8.3.5): the project's
  `EpStrongBundle.IsAuxNorm` (read with `#print`: Part I's `StrongBundle.IsAuxNorm` — `N`
  continuous on `W_{0,1}`, a complete norm on each fibre `(W_{0,1})_x`, and `P(h_k) → x`,
  `N(h_k) → 0` imply `h_k → 0_x` — plus `N(h) = N(k)` whenever `h = μ(φ, k)`).  `N` is a function
  on `W_{0,1}` (`B.One`).  I trust these definitions.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V12_4
open Polyfold

/-- **Theorem 12.2.2**: a strong bundle over an ep-groupoid with paracompact orbit space admits
an auxiliary norm. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B),
    X.HasParacompactOrbitSpace →
    ∃ N : B.One → ℝ, E.IsAuxNorm N

end RoundTrip.V12_4
