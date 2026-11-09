import Polyfold
/-! Blind formalization of V8_20 (the text's Part II, §8.3, Definition 8.3.1 = 2017 Definition
8.4, p. 375 / 2017 p. 271).

Text: a strong bundle over the ep-groupoid `X` is a pair `(P, μ)`: `P : W → X` a strong bundle over
the object M-polyfold `X`, and `μ : 𝐗 ₛ×_P W → W` a strong bundle map covering `t : 𝐗 → X`
(`P(μ(ψ, w)) = t(ψ)`) with (1) `μ` a surjective local sc-diffeomorphism, linear on the fibres;
(2) `μ(1_x, w) = w` for `w ∈ W_x`; (3) `μ(ψ ∘ γ, w) = μ(ψ, μ(γ, w))` when `s(γ) = P(w)` and
`t(γ) = s(ψ) = P(μ(γ, w))`.

Choices:
- This item is a definition.  Setting: `X : EpGroupoid Obj Mor` (`Obj Mor : Type`, universe 0,
  as in `RoundTrip/Blind/V7_3.lean`); `W : Type` Hausdorff paracompact, `P : W → Obj` with the
  fibre linear structures as instances; `B : StrongBundle X.PObj P` (Definition 2.51 of Part I,
  characterized in `RoundTrip/Blind/V2_58.lean`).
- `𝐗 ₛ×_P W = {(ψ, w) | P(w) = s(ψ)}` is the project's `pullbackSpace P X.src` (the pull-back
  `s*W` of Definition 2.53, checked in `RoundTrip/Blind/V2_60.lean`), as a strong bundle over `𝐗`
  the project's pull-back strong bundle `B.pullback hs` (Proposition 2.54) with projection
  `(ψ, w) ↦ ψ`.  This needs the sc-smoothness `hs` of `s` (true: V7_3 (d)) and paracompactness of
  `𝐗 ₛ×_P W` (true: a closed subset of the metrizable `𝐗 × W`); both are hypotheses of B, the
  construction does not depend on them (proof irrelevance), and they are satisfiable.
- "strong bundle map covering `t`": the project's `StrongBundle.IsStrongBundleMap` (fields read
  with `#print`: covers `f`, linear on the fibres, sc-smooth `[0] → [0]`, maps `[1]` into `[1]`
  sc-smoothly), i.e. the text's notion of a map that is a strong bundle map in both levels; I
  trust it.  It includes `P(μ(ψ, w)) = t(ψ)` and fibre linearity for the pull-back's fibre
  structure; I add the literal fibre linearity "`μ(ψ, ·) : W_{s ψ} → W_{t ψ}` is linear" with
  the fibre structures of `W` (∃ a linear map with these values), so as not to depend on the
  project's fibre instance of the pull-back.
- "surjective local sc-diffeomorphism": `μ` surjective and `MPolyfold.IsLocalScDiffeo` between
  the M-polyfolds `(𝐗 ₛ×_P W)[0]` and `W[0]` (the total spaces as M-polyfolds; the reading at level
  `[0]`, the literal M-polyfold sense).
- (2) and (3) are stated with the memberships `(1_x, w) ∈ 𝐗 ₛ×_P W` etc. as hypotheses (they are
  provable, so nothing is lost); in (3) the text's hypotheses `s(γ) = P(w)`, `t(γ) = s(ψ)`,
  `s(ψ) = P(μ(γ, w))` are kept literally.
- B: (a) the project's `EpStrongBundle X B` (fields read with `#print`) satisfies my
  `IsEpStrongBundleB` for its `μ`; (b) every `μ` satisfying it is the `μ` of an `EpStrongBundle`.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_20
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- **Definition 8.3.1**: `μ : 𝐗 ₛ×_P W → W` makes the strong bundle `B` a strong bundle over the
ep-groupoid `X`. -/
def IsEpStrongBundleB (X : EpGroupoid Obj Mor) (B : StrongBundle X.PObj P)
    [ParacompactSpace (pullbackSpace P X.src)] (hs : X.PMor.IsScSmoothMap X.PObj X.src)
    (μ : pullbackSpace P X.src → W) : Prop :=
  -- `μ` is a strong bundle map covering `t` (so `P(μ(ψ, w)) = t(ψ)`)
  (B.pullback hs).IsStrongBundleMap B X.tgt μ ∧
  -- (1) `μ` is a surjective local sc-diffeomorphism
  Function.Surjective μ ∧
  (B.pullback hs).toMPolyfold0.IsLocalScDiffeo B.toMPolyfold0 μ ∧
  -- (1) `μ` is linear on the fibres: `μ(ψ, ·) : W_{s ψ} → W_{t ψ}` is linear
  (∀ ψ : Mor, ∃ L : (P ⁻¹' {X.src ψ}) →ₗ[ℝ] (P ⁻¹' {X.tgt ψ}),
    ∀ w : P ⁻¹' {X.src ψ}, (L w : W) = μ ⟨(ψ, w.1), w.2⟩) ∧
  -- (2) `μ(1_x, w) = w` for `w ∈ W_x`
  (∀ (x : Obj) (w : W) (_ : P w = x) (h : P w = X.src (X.unit x)),
    μ ⟨(X.unit x, w), h⟩ = w) ∧
  -- (3) `μ(ψ ∘ γ, w) = μ(ψ, μ(γ, w))` for `s(γ) = P(w)`, `t(γ) = s(ψ) = P(μ(γ, w))`
  (∀ (ψ γ : Mor) (w : W) (h₁ : P w = X.src γ) (h₂ : X.tgt γ = X.src ψ)
    (h₃ : X.src ψ = P (μ ⟨(γ, w), h₁⟩)),
    μ ⟨(X.comp ψ γ, w), h₁.trans (X.src_comp ψ γ h₂.symm).symm⟩ =
      μ ⟨(ψ, μ ⟨(γ, w), h₁⟩), h₃.symm⟩)

end

/-- Definition 8.3.1: the project's strong bundles over ep-groupoids are the text's. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    [ParacompactSpace (pullbackSpace P X.src)] (hs : X.PMor.IsScSmoothMap X.PObj X.src),
    -- (a) every project strong bundle over `X` is one in the text's sense
    (∀ E : EpStrongBundle X B, IsEpStrongBundleB X B hs E.μ) ∧
    -- (b) every strong bundle over `X` in the text's sense is a project one
    (∀ μ : pullbackSpace P X.src → W, IsEpStrongBundleB X B hs μ →
      ∃ E : EpStrongBundle X B, E.μ = μ)

end RoundTrip.V8_20
