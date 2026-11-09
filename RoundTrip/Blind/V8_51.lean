import Polyfold
/-! Blind formalization of V8_51 (the 2021 book, Part II, §8.5, Lemma 8.5.10, p. 395).

Text: for a proper strong bundle covering functor `A : W → V` covering `F : Y → X`, the map
`B : W → F*V`, `w ↦ (P(w), A(w))`, is a strong bundle isomorphism over the ep-groupoid `Y`,
where `F*V` carries `μ_{F*V}(φ, (y, v)) = (t(φ), μ_X(F(φ), v))`; it satisfies (8.23)
`B(μ_Y(φ, w)) = μ_{F*V}(φ, B(w))`, and `A = Ā ∘ B`.

Choices:
- Setting: universe 0; `Y`, `X` ep-groupoids, `W`, `V` with their topologies, `P : W → ObjY`,
  `Q : V → ObjX` with the linear structures on the fibres, Part I strong bundles `BW`, `BV`,
  strong bundles over the ep-groupoids `EW` (`μ_Y`), `EV` (`μ_X`), `F : EpFunctor Y X`,
  `A : W → V`.  Hypothesis: `A` is a proper strong bundle covering functor in the 2021 sense
  (Definition 8.5.9), the project's `IsProperStrongBundleCovering2021 EW EV F A` (item V8_50
  checks this definition).  `Q ∘ A = F ∘ P` (part of that definition) is also taken as an
  explicit hypothesis `hQA`, only to write down `B(w) ∈ F*V`.
- `F*V = {(y, v) ∈ Y × V | F(y) = Q(v)}` is the project's `pullbackSpace Q F.obj` (read with
  `#print`: `{p | Q p.2 = F.obj p.1}`, subspace topology), with Part I's pull-back strong bundle
  structure `BV.pullback F.isScSmoothMap_obj` over the object M-polyfold of `Y` (projection
  `(y, v) ↦ y`).  The project requires `ParacompactSpace (F*V)` for that structure, and
  `ParacompactSpace (𝐘 ₛ×_P W)` for the 2021 definition; both are hypotheses (instances), true in
  the text's setting (M-polyfolds are paracompact).
- "strong bundle isomorphism over `Y`" (conjunct (a)): Part I's `IsStrongBundleIso` from `W → Y`
  to `F*V → Y` covering the identity of `Y`, for `B` and some inverse.
- (8.23) (conjunct (b)): for every morphism `φ` of `Y` and `w` with `P(w) = s(φ)`,
  `B(μ_Y(φ, w)) = (t(φ), μ_X(F(φ), A(w)))`, compared as pairs; the proof that
  `(F(φ), A(w)) ∈ 𝐗 ₛ×_Q V` is a hypothesis `hv` (it always holds).
- `A = Ā ∘ B` (conjunct (c)), `Ā : F*V → V`, `(y, v) ↦ v`.
- "over the ep-groupoid `Y`, where `F*V` carries `μ_{F*V}`" (conjunct (d)): I read this as also
  saying that `(F*V, μ_{F*V})` is a strong bundle over the ep-groupoid `Y` (2017 Definition 8.4,
  the project's `EpStrongBundle`): some `EpStrongBundle` structure on `F*V → Y` whose structure
  map is `μ_{F*V}(φ, (y, v)) = (t(φ), μ_X(F(φ), v))` (for `y = s(φ)`).  This is presupposed by
  "strong bundle isomorphism over the ep-groupoid" (and follows from (a), (b) by transport); if
  the text only defines `μ_{F*V}` here, (d) is an addition.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_51
open Polyfold

/-- Lemma 8.5.10: `w ↦ (P(w), A(w))` is a strong bundle isomorphism `W ≅ F*V` over `Y`
intertwining `μ_Y` and `μ_{F*V}` ((8.23)), with `A = Ā ∘ B`; `(F*V, μ_{F*V})` is a strong bundle
over the ep-groupoid `Y`. -/
def B : Prop :=
  ∀ (ObjY MorY : Type) [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY] (Y : EpGroupoid ObjY MorY)
    (ObjX MorX : Type) [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX] (X : EpGroupoid ObjX MorX)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → ObjY)
    [∀ y, AddCommGroup (P ⁻¹' {y})] [∀ y, Module ℝ (P ⁻¹' {y})] (BW : StrongBundle Y.PObj P)
    [ParacompactSpace (pullbackSpace P Y.src)]
    (V : Type) [TopologicalSpace V] [T2Space V] [ParacompactSpace V] (Q : V → ObjX)
    [∀ x, AddCommGroup (Q ⁻¹' {x})] [∀ x, Module ℝ (Q ⁻¹' {x})] (BV : StrongBundle X.PObj Q)
    (EW : EpStrongBundle Y BW) (EV : EpStrongBundle X BV) (F : EpFunctor Y X) (A : W → V)
    [ParacompactSpace (pullbackSpace Q F.obj)],
    EW.IsProperStrongBundleCovering2021 EV F A →
    ∀ hQA : ∀ w : W, Q (A w) = F.obj (P w),
      let Bm : W → pullbackSpace Q F.obj := fun w => ⟨(P w, A w), hQA w⟩
      -- (a) a strong bundle isomorphism `W → F*V` over the identity of `Y`
      (∃ Binv : pullbackSpace Q F.obj → W,
        BW.IsStrongBundleIso (BV.pullback F.isScSmoothMap_obj) id Bm id Binv) ∧
      -- (b) (8.23) `B(μ_Y(φ, w)) = μ_{F*V}(φ, B(w)) = (t(φ), μ_X(F(φ), A(w)))`
      (∀ (φ : MorY) (w : W) (hw : P w = Y.src φ) (hv : Q (A w) = X.src (F.mor φ)),
        (Bm (EW.μ ⟨(φ, w), hw⟩)).1 = (Y.tgt φ, EV.μ ⟨(F.mor φ, A w), hv⟩)) ∧
      -- (c) `A = Ā ∘ B`
      (∀ w : W, A w = (Bm w).1.2) ∧
      -- (d) `(F*V, μ_{F*V})` is a strong bundle over the ep-groupoid `Y`
      (∃ E' : EpStrongBundle Y (BV.pullback F.isScSmoothMap_obj),
        ∀ (φ : MorY) (q : pullbackSpace Q F.obj) (hq : pullbackProj Q F.obj q = Y.src φ)
          (hv : Q q.1.2 = X.src (F.mor φ)),
          (E'.μ ⟨(φ, q), hq⟩).1 = (Y.tgt φ, EV.μ ⟨(F.mor φ, q.1.2), hv⟩))

end RoundTrip.V8_51
