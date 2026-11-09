import Polyfold
/-! Blind formalization of V8_5 (the text's Part II, §8.1, Lemma 8.1.3 (2017: 8.2), pp. 359–361;
2017 pp. 259–260).

Text: for morphisms `Φ = (φ, h)`, `Ψ = (ψ, k)` of `T𝐗` (composable: `s_T(Ψ) = t_T(Φ)`),
`s_T(Ψ ∘ Φ) = s_T(Φ)` and `t_T(Ψ ∘ Φ) = t_T(Ψ)`.  (The computation of the target with
`α = t ∘ (s|𝐔(ψ ∘ φ))⁻¹` is the proof, not formalized.)

Choices:
- Setting: `Obj Mor : Type` (universe 0), Hausdorff paracompact, `X : EpGroupoid Obj Mor` (the
  text's ep-groupoid: `RoundTrip/Blind/V7_3.lean`); tangent spaces (Part I's `TangentSpace`,
  `tangentMap`) in `Type 1`; `baseB` = the projection `p` seen in `X`.
- `s_T = Ts`, `t_T = Tt` (8.3); `s`, `t` sc-smooth is asserted (∃ of the proofs).  The composite
  (8.5) is my `tCompB` (as in `RoundTrip/Blind/V8_3.lean`): a vector over `ψ ∘ φ` with `Ts` equal
  to `Ts h`, chosen (junk `h` if there is none).  So `s_T(Ψ ∘ Φ) = s_T(Φ)` contains the existence
  of such a vector, and `t_T(Ψ ∘ Φ) = t_T(Ψ)` is the content of the lemma.
- Composable pairs only (`Ts k = Tt h`, (8.4)).
- Nothing looks false to me.
-/
namespace RoundTrip.V8_5
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

/-- Lemma 8.1.3: `s_T(Ψ ∘ Φ) = s_T(Φ)` and `t_T(Ψ ∘ Φ) = t_T(Ψ)` for composable `Ψ`, `Φ`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ∃ (hs : X.PMor.IsScSmoothMap X.PObj X.src) (ht : X.PMor.IsScSmoothMap X.PObj X.tgt),
      ∀ Ψ Φ : X.PMor.TangentSpace, MPolyfold.tangentMap hs Ψ = MPolyfold.tangentMap ht Φ →
        MPolyfold.tangentMap hs (tCompB X hs Ψ Φ) = MPolyfold.tangentMap hs Φ ∧
        MPolyfold.tangentMap ht (tCompB X hs Ψ Φ) = MPolyfold.tangentMap ht Ψ

end RoundTrip.V8_5
