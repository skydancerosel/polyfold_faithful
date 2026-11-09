import Polyfold
/-! Blind formalization of V8_23 (the text's Part II, §8.3, Definition 8.3.2 = 2017 Definition 8.5
and the paragraph after it, 2017 p. 273).

Text: for strong bundles `(P : W → X, μ)` and `(P' : W' → X', μ')` over ep-groupoids, a strong
bundle map (strong bundle functor) between them is a strong bundle map `Φ : W → W'` covering an
sc-smooth functor `φ : X → X'` with `Φ(μ(γ, w)) = μ'(φ(γ), Φ(w))` for all `γ ∈ 𝐗`, `w ∈ W` with
`s(γ) = P(w)`; the relation is well defined since `φ(γ) : φ(s γ) → φ(t γ)`.

Choices:
- This item is a definition plus a well-definedness remark.  Setting as in my
  `RoundTrip/Blind/V8_20.lean`, twice: `X : EpGroupoid Obj Mor`, `X' : EpGroupoid Obj' Mor'`,
  `W W' : Type`, strong bundles `B : StrongBundle X.PObj P`, `B' : StrongBundle X'.PObj P'`, and
  strong bundles over the ep-groupoids `E : EpStrongBundle X B`, `E' : EpStrongBundle X' B'`
  (V8_20).  All spaces in `Type` (the project's `IsMap` puts `Obj, Obj'` in one universe and
  `W, W'` in one universe).  The sc-smooth functor `φ` is a project `EpFunctor X X'` (V7_9).
- "strong bundle map `Φ : W → W'` covering `φ`": the project's `StrongBundle.IsStrongBundleMap`
  covering the object map `φ.obj` (as in V8_20: covers, fibrewise linear, sc-smooth on `[0]` and
  `[1]`; I trust it).
- The identity is stated with the membership `(φ(γ), Φ(w)) ∈ 𝐗' ₛ×_{P'} W'` as a hypothesis
  `h'` (it holds, by the remark).
- B: (a) the project's `EpStrongBundle.IsMap E E' φ Φ` (fields read with `#print`) iff my
  `IsMapB`; (b) the remark: for a strong bundle map `Φ` covering `φ` and `s(γ) = P(w)`,
  `P'(Φ w) = s'(φ γ)`, so that `μ'(φ(γ), Φ(w))` is defined.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_23
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}

/-- **Definition 8.3.2**: `Φ : W → W'` is a strong bundle map between the strong bundles `E`, `E'`
over the ep-groupoids `X`, `X'`, covering the sc-smooth functor `φ`. -/
def IsMapB (E : EpStrongBundle X B) (E' : EpStrongBundle X' B') (φ : EpFunctor X X')
    (Φ : W → W') : Prop :=
  B.IsStrongBundleMap B' φ.obj Φ ∧
  ∀ (γ : Mor) (w : W) (h : P w = X.src γ) (h' : P' (Φ w) = X'.src (φ.mor γ)),
    Φ (E.μ ⟨(γ, w), h⟩) = E'.μ ⟨(φ.mor γ, Φ w), h'⟩

end

/-- Definition 8.3.2: the project's strong bundle maps between strong bundles over ep-groupoids
are the text's, and the defining relation is well defined. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    (Obj' Mor' : Type) [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] (X' : EpGroupoid Obj' Mor')
    (W' : Type) [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] (P' : W' → Obj')
    [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] (B' : StrongBundle X'.PObj P')
    (E : EpStrongBundle X B) (E' : EpStrongBundle X' B') (φ : EpFunctor X X') (Φ : W → W'),
    -- (a) the project's notion is the text's
    (E.IsMap E' φ Φ ↔ IsMapB E E' φ Φ) ∧
    -- (b) well defined: `(φ(γ), Φ(w)) ∈ 𝐗' ₛ×_{P'} W'` when `s(γ) = P(w)`
    (B.IsStrongBundleMap B' φ.obj Φ →
      ∀ (γ : Mor) (w : W), P w = X.src γ → P' (Φ w) = X'.src (φ.mor γ))

end RoundTrip.V8_23
