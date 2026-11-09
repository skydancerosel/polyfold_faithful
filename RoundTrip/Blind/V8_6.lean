import Polyfold
/-! Blind formalization of V8_6 (the text's Part II, §8.1, Lemma 8.1.4 (2017: 8.3), pp. 360–362;
2017 pp. 260–261).

Text: the composition of `T𝐗` is associative: when sources and targets match,
`(σ, l) ∘ ((ψ, k) ∘ (φ, h))` and `((σ, l) ∘ (ψ, k)) ∘ (φ, h)` are both
`(σ ∘ ψ ∘ φ, (Ts(σ ∘ ψ ∘ φ))⁻¹ Ts(φ)(h))`.

Choices:
- Setting: `Obj Mor : Type` (universe 0), Hausdorff paracompact, `X : EpGroupoid Obj Mor` (the
  text's ep-groupoid: `RoundTrip/Blind/V7_3.lean`); tangent spaces (Part I's `TangentSpace`,
  `tangentMap`) in `Type 1`; `baseB` = the projection `p` seen in `X`.
- The composite (8.5) is my `tCompB` (as in `RoundTrip/Blind/V8_3.lean`): a vector over
  `p(k) ∘ p(h)` with `Ts` equal to `Ts h`, chosen (junk `h` if there is none); `s`, `t`
  sc-smooth is asserted (∃ of the proofs).
- "sources and targets match": `Ts l = Tt k` and `Ts k = Tt h`.  B asserts the two bracketings
  are equal, and that the common value lies over `σ ∘ (ψ ∘ φ)` (`= (σ ∘ ψ) ∘ φ` in `𝐗`) with
  `Ts` equal to `Ts h`, i.e. it is `(Ts(σ ∘ ψ ∘ φ))⁻¹ Ts(φ)(h)`.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_6
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

/-- Lemma 8.1.4: the composition (8.5) of `T𝐗` is associative, with common value
`(σ ∘ ψ ∘ φ, Ts(σ ∘ ψ ∘ φ)⁻¹ Ts(φ)(h))`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ∃ (hs : X.PMor.IsScSmoothMap X.PObj X.src) (ht : X.PMor.IsScSmoothMap X.PObj X.tgt),
      ∀ l k h : X.PMor.TangentSpace,
        MPolyfold.tangentMap hs l = MPolyfold.tangentMap ht k →
        MPolyfold.tangentMap hs k = MPolyfold.tangentMap ht h →
          tCompB X hs l (tCompB X hs k h) = tCompB X hs (tCompB X hs l k) h ∧
          baseB X.PMor (tCompB X hs l (tCompB X hs k h)) =
            X.comp (baseB X.PMor l) (X.comp (baseB X.PMor k) (baseB X.PMor h)) ∧
          MPolyfold.tangentMap hs (tCompB X hs l (tCompB X hs k h)) = MPolyfold.tangentMap hs h

end RoundTrip.V8_6
