import Polyfold
/-! Blind formalization of V8_7 (the text's Part II, §8.1, Lemma 8.1.5 (2017: 8.4), 2017 p. 261).

Text: for an object `q ∈ T_xX`, the 1-morphism `1_q = (1_x, Ts(1_x)⁻¹ q) ∈ T_{1_x}𝐗` is a
two-sided identity for the composition.  (Proof: `s_T(1_q) = q`, `t_T(1_q) = q` since
`t ∘ (s|𝐔(1_x))⁻¹(b) = b` near `x`; `(φ, k) ∘ 1_q = (φ, k)` if `Ts(φ)(k) = q`, and
`1_q ∘ (φ, k) = (φ, k)` if `Tt(φ)(k) = q`.)

Choices:
- Setting: `Obj Mor : Type` (universe 0), Hausdorff paracompact, `X : EpGroupoid Obj Mor` (the
  text's ep-groupoid: `RoundTrip/Blind/V7_3.lean`); tangent spaces (Part I's `TangentSpace`,
  `tangentMap`) in `Type 1`; `baseB` = the projection `p` seen in `X`, so `x = baseB q`.
- `1_q` is characterized by `IsTUnitB q v`: `v` lies over `1_x` and `Ts v = q` (that is
  `v = Ts(1_x)⁻¹ q`).  B asserts that such a `v` exists (the definition makes sense) and that
  every such `v` has `s_T v = q`, `t_T v = q` (the two-sidedness needs both; they are the
  sources/targets the composites require) and is a two-sided identity.
- The composite (8.5) is my `tCompB` (as in `RoundTrip/Blind/V8_3.lean`): a vector over
  `p(k) ∘ p(h)` with `Ts` equal to `Ts h`, chosen (junk `h` if none); `s`, `t` sc-smooth is
  asserted (∃ of the proofs).  "Two-sided identity": `k ∘ 1_q = k` for `Ts k = q`, and
  `1_q ∘ k = k` for `Tt k = q` (exactly the composable cases).
- Nothing looks false to me.
-/
namespace RoundTrip.V8_7
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

/-- `v` is `1_q = (1_x, Ts(1_x)⁻¹ q)`, `x = p(q)`. -/
def IsTUnitB (X : EpGroupoid Obj Mor) (hs : X.PMor.IsScSmoothMap X.PObj X.src)
    (q : X.PObj.TangentSpace) (v : X.PMor.TangentSpace) : Prop :=
  baseB X.PMor v = X.unit (baseB X.PObj q) ∧ MPolyfold.tangentMap hs v = q

end

/-- Lemma 8.1.5: `1_q = (1_x, Ts(1_x)⁻¹ q)` exists, has source and target `q`, and is a
two-sided identity for the composition (8.5). -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ∃ (hs : X.PMor.IsScSmoothMap X.PObj X.src) (ht : X.PMor.IsScSmoothMap X.PObj X.tgt),
      ∀ q : X.PObj.TangentSpace,
        (∃ v : X.PMor.TangentSpace, IsTUnitB X hs q v) ∧
        ∀ v : X.PMor.TangentSpace, IsTUnitB X hs q v →
          MPolyfold.tangentMap hs v = q ∧ MPolyfold.tangentMap ht v = q ∧
          (∀ k : X.PMor.TangentSpace, MPolyfold.tangentMap hs k = q → tCompB X hs k v = k) ∧
          (∀ k : X.PMor.TangentSpace, MPolyfold.tangentMap ht k = q → tCompB X hs v k = k)

end RoundTrip.V8_7
