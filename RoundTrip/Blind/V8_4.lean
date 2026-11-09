import Polyfold
/-! Blind formalization of V8_4 (the text's Part II, §8.1, Lemma 8.1.2 (2017: 8.1), 2017 p. 259).

Text: with `T(𝐗 ₛ×ₜ 𝐗)` identified with `T𝐗 _{Ts}×_{Tt} T𝐗`, the multiplication (8.5) of `T𝐗`
is the tangent of the multiplication `m` of `𝐗`:
`(ψ, k) ∘ (φ, h) = Tm(ψ, φ)(k, h) = (ψ ∘ φ, (Ts(ψ ∘ φ))⁻¹ ∘ Ts(φ)(h))`, where
`k = Ts(ψ)⁻¹(Tt(φ)(h))`.  (The proof's differentiation of
`s|𝐔(φ ∘ ψ) ∘ m((s|𝐔(ψ))⁻¹(t(φ')), φ') = s(φ')` is the proof, not formalized.)

Choices:
- Setting: `Obj Mor : Type` (universe 0), Hausdorff paracompact, `X : EpGroupoid Obj Mor` (the
  text's ep-groupoid: `RoundTrip/Blind/V7_3.lean`); tangent spaces (Part I's `TangentSpace`,
  `tangentPolyfold`, `tangentMap`) in `Type 1`; `baseB` = the projection `p` seen in `X`.
- `𝐗 ₛ×ₜ 𝐗 = {(ψ, φ) | s ψ = t φ}` is the project's `MPolyfold.fibredProduct src tgt` with its
  natural M-polyfold structure, read (as in `RoundTrip/Blind/V7_3.lean`) as a sub-M-polyfold of
  `𝐗 × 𝐗` (`MPolyfold.prod`, `subPolyfold`; the paracompactness instances are asserted to
  exist).  `m(ψ, φ) = ψ ∘ φ` and the two projections `pr₁, pr₂ : 𝐗 ₛ×ₜ 𝐗 → 𝐗` are sc-smooth
  (asserted, ∃; `m` by Definition 7.3, the projections as restrictions of sc-smooth maps).
- "identified with `T𝐗 _{Ts}×_{Tt} T𝐗`": via `v ↦ (Tpr₁ v, Tpr₂ v)`, which B asserts to be a
  bijection of `T(𝐗 ₛ×ₜ 𝐗)` onto `{(k, h) | Ts k = Tt h}` (the presupposition of the
  identification; I do not assert the M-polyfold side of it).
- The composite (8.5): my `tCompB` (as in `RoundTrip/Blind/V8_3.lean`), the vector over
  `p(k) ∘ p(h)` with `Ts` equal to `Ts h`, chosen (junk `h` if none).  B asserts
  `Tm v = (Tpr₁ v) ∘ (Tpr₂ v)`, and, explicitly, that `Tm v` lies over `ψ ∘ φ` and has
  `Ts(Tm v) = Ts(Tpr₂ v)`, i.e. `Tm v = Ts(ψ ∘ φ)⁻¹(Ts(φ)(h))`.
- "keeping in mind `k = Ts(ψ)⁻¹(Tt(φ)(h))`" is the fibrewise invertibility of `Ts` (asserted in
  `RoundTrip/Blind/V8_1.lean`), not repeated.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_4
open Polyfold

universe u

/-- The base point `p(w) ∈ Z₁ ⊆ Z` of a tangent vector `w ∈ TZ`. -/
def baseB {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
    (w : P.TangentSpace) : Z :=
  P.levelVal 1 (P.tangentProj w)

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

open Classical in
/-- (8.5): `k ∘ h = Ts(ψ ∘ φ)⁻¹(Ts(φ)(h))`, a vector over `p(k) ∘ p(h)` with `Ts` equal to
`Ts h` (chosen; junk `h` if there is none). -/
noncomputable def tCompB (X : EpGroupoid Obj Mor) (hs : X.PMor.IsScSmoothMap X.PObj X.src)
    (k h : X.PMor.TangentSpace) : X.PMor.TangentSpace :=
  if hex : ∃ v, baseB X.PMor v = X.comp (baseB X.PMor k) (baseB X.PMor h) ∧
      MPolyfold.tangentMap hs v = MPolyfold.tangentMap hs h then hex.choose else h

end

/-- Lemma 8.1.2: under `T(𝐗 ₛ×ₜ 𝐗) ≅ T𝐗 _{Ts}×_{Tt} T𝐗`, `v ↦ (Tpr₁ v, Tpr₂ v)`, the tangent
`Tm` of the multiplication is the multiplication (8.5) of `T𝐗`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ∃ (hs : X.PMor.IsScSmoothMap X.PObj X.src) (ht : X.PMor.IsScSmoothMap X.PObj X.tgt)
      (_ : ParacompactSpace (Mor × Mor))
      (hA : (X.PMor.prod X.PMor).IsSubMPolyfold (MPolyfold.fibredProduct X.src X.tgt))
      (_ : ParacompactSpace ↥(MPolyfold.fibredProduct X.src X.tgt))
      (hm : ((X.PMor.prod X.PMor).subPolyfold hA).IsScSmoothMap X.PMor
        (fun p => X.comp p.1.1 p.1.2))
      (h₁ : ((X.PMor.prod X.PMor).subPolyfold hA).IsScSmoothMap X.PMor (fun p => p.1.1))
      (h₂ : ((X.PMor.prod X.PMor).subPolyfold hA).IsScSmoothMap X.PMor (fun p => p.1.2)),
      -- the identification `T(𝐗 ₛ×ₜ 𝐗) ≅ T𝐗 _{Ts}×_{Tt} T𝐗`
      Set.BijOn (fun v => (MPolyfold.tangentMap h₁ v, MPolyfold.tangentMap h₂ v)) Set.univ
        {q : X.PMor.TangentSpace × X.PMor.TangentSpace |
          MPolyfold.tangentMap hs q.1 = MPolyfold.tangentMap ht q.2} ∧
      -- `Tm(ψ, φ)(k, h) = (ψ, k) ∘ (φ, h) = (ψ ∘ φ, Ts(ψ ∘ φ)⁻¹ Ts(φ)(h))`
      ∀ v : ((X.PMor.prod X.PMor).subPolyfold hA).TangentSpace,
        MPolyfold.tangentMap hm v =
          tCompB X hs (MPolyfold.tangentMap h₁ v) (MPolyfold.tangentMap h₂ v) ∧
        baseB X.PMor (MPolyfold.tangentMap hm v) =
          X.comp (baseB X.PMor (MPolyfold.tangentMap h₁ v))
            (baseB X.PMor (MPolyfold.tangentMap h₂ v)) ∧
        MPolyfold.tangentMap hs (MPolyfold.tangentMap hm v) =
          MPolyfold.tangentMap hs (MPolyfold.tangentMap h₂ v)

end RoundTrip.V8_4
