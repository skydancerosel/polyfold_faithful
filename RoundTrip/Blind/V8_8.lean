import Polyfold
/-! Blind formalization of V8_8 (the text's Part II, §8.1, Lemma 8.1.6 (2017: 8.5), pp. 361–363;
2017 pp. 261–262).

Text: the inverse `ι_T(φ, k) = (φ⁻¹, Tι(φ)(k))` is a two-sided inverse for the composition.
(Proof: by the chain rule for `s(φ⁻¹) = t(φ)`, `t(φ⁻¹) = s(φ)`: `s_T(ι_T(φ, k)) = t_T(φ, k)`,
`t_T(ι_T(φ, k)) = s_T(φ, k)`; then `ι_T(φ, k) ∘ (φ, k) = 1_{Ts(φ)k}`, and the composition from the
right is verified the same way.)

Choices:
- Setting: `Obj Mor : Type` (universe 0), Hausdorff paracompact, `X : EpGroupoid Obj Mor` (the
  text's ep-groupoid: `RoundTrip/Blind/V7_3.lean`); tangent spaces (Part I's `TangentSpace`,
  `tangentMap`) in `Type 1`; `baseB` = the projection `p` seen in `X`.
- `ι_T = Tι` (8.9), `s_T = Ts`, `t_T = Tt`; `s`, `t`, `ι` sc-smooth is asserted (∃ of the
  proofs).  B asserts `ι_T(φ, k)` lies over `φ⁻¹` (the form `(φ⁻¹, ·)` of (8.9)) and the source
  and target identities (which make both composites composable).
- The composite (8.5) is my `tCompB` (as in `RoundTrip/Blind/V8_3.lean`), chosen (junk `h` if
  none).  The unit `1_q` is characterized by `IsTUnitB q v` (`v` over `1_{p(q)}`, `Ts v = q`);
  "`ι_T(φ, k) ∘ (φ, k) = 1_{Ts(φ)k}`" is asserted as: the composite satisfies `IsTUnitB (Ts k)`
  and equals every `v` that does.  From the right: `(φ, k) ∘ ι_T(φ, k) = 1_{Tt(φ)k}` (the unit at
  the source of `ι_T(φ, k)`, i.e. at `t_T(φ, k)`).
- Nothing looks false to me.
-/
namespace RoundTrip.V8_8
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

/-- Lemma 8.1.6: `ι_T = Tι` is a two-sided inverse for the composition (8.5). -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ∃ (hs : X.PMor.IsScSmoothMap X.PObj X.src) (ht : X.PMor.IsScSmoothMap X.PObj X.tgt)
      (hι : X.PMor.IsScSmoothMap X.PMor X.inv),
      ∀ k : X.PMor.TangentSpace,
        -- `ι_T(φ, k) = (φ⁻¹, Tι(φ)(k))`
        baseB X.PMor (MPolyfold.tangentMap hι k) = X.inv (baseB X.PMor k) ∧
        -- `s_T(ι_T(φ, k)) = t_T(φ, k)`, `t_T(ι_T(φ, k)) = s_T(φ, k)`
        MPolyfold.tangentMap hs (MPolyfold.tangentMap hι k) = MPolyfold.tangentMap ht k ∧
        MPolyfold.tangentMap ht (MPolyfold.tangentMap hι k) = MPolyfold.tangentMap hs k ∧
        -- `ι_T(φ, k) ∘ (φ, k) = 1_{Ts(φ)k}`
        IsTUnitB X hs (MPolyfold.tangentMap hs k) (tCompB X hs (MPolyfold.tangentMap hι k) k) ∧
        (∀ v : X.PMor.TangentSpace, IsTUnitB X hs (MPolyfold.tangentMap hs k) v →
          tCompB X hs (MPolyfold.tangentMap hι k) k = v) ∧
        -- `(φ, k) ∘ ι_T(φ, k) = 1_{Tt(φ)k}`
        IsTUnitB X hs (MPolyfold.tangentMap ht k) (tCompB X hs k (MPolyfold.tangentMap hι k)) ∧
        (∀ v : X.PMor.TangentSpace, IsTUnitB X hs (MPolyfold.tangentMap ht k) v →
          tCompB X hs k (MPolyfold.tangentMap hι k) = v)

end RoundTrip.V8_8
