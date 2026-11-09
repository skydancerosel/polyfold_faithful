import Polyfold
/-! Blind formalization of V8_13 (the text's Part II, §8.1, Theorem 8.1.11 (2017: 8.2),
pp. 365–367; 2017 pp. 265–266).

Text: if `(Φ, 𝚽) : (X, 𝐗) → (Y, 𝐘)` is an sc-smooth functor between ep-groupoids, then
`(TΦ, T𝚽) : T(X, 𝐗) → T(Y, 𝐘)` is an sc-smooth functor between the tangent ep-groupoids.  (Proof:
`TΦ`, `T𝚽` sc-smooth; differentiating `𝚽 ∘ m_X = m_Y ∘ (𝚽 × 𝚽)` and Lemma 8.1.2 give
`T𝚽(ψ ∘ φ)(k ∘ h) = T𝚽(ψ)(k) ∘ T𝚽(φ)(h)`; units "left to the reader"; differentiating
`s ∘ 𝚽 = Φ ∘ s`, `t ∘ 𝚽 = Φ ∘ t` gives sources and targets.)

Choices:
- Setting: `Obj Mor Obj' Mor' : Type` (universe 0), Hausdorff paracompact,
  `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'` (the text's ep-groupoids:
  `RoundTrip/Blind/V7_3.lean`); an sc-smooth functor is a project `EpFunctor X Y` (= the text's
  morphisms of `𝓔𝓟`, Definition 7.7, by `RoundTrip/Blind/V7_9.lean`), with maps `F.obj = Φ`,
  `F.mor = 𝚽` and their sc-smoothness fields.  Tangent spaces (Part I's `TangentSpace` with the
  M-polyfold structure `tangentPolyfold`, tangent maps `tangentMap`) in `Type 1`; `baseB` = the
  projection `p` seen in the base space.
- `TΦ`, `T𝚽` are the tangent maps of `F.obj`, `F.mor`.
- The tangent ep-groupoids carry the structure maps (8.3)–(8.9) (`RoundTrip/Blind/V8_1.lean`,
  `V8_3.lean`): `s_T = Ts`, `t_T = Tt` (`s`, `t` sc-smooth asserted, ∃ of the proofs), composite
  `tCompB` (a vector over `p(k) ∘ p(h)` with `Ts` equal to `Ts h`, chosen, junk `h` if none), unit
  characterized by `IsTUnitB` (over `1_{p(a)}`, `Ts = a`).
- "sc-smooth functor" (as in Definition 7.7, `RoundTrip/Blind/V7_9.lean`): `TΦ : TX → TY`,
  `T𝚽 : T𝐗 → T𝐘` sc-smooth; `s_T(T𝚽 k) = TΦ(s_T k)`, `t_T(T𝚽 k) = TΦ(t_T k)`;
  `T𝚽(l ∘ k) = T𝚽 l ∘ T𝚽 k` for composable `l`, `k`; `T𝚽(1_a) = 1_{TΦ(a)}`, asserted as: for
  every `v` with `IsTUnitB a v`, `T𝚽 v` satisfies `IsTUnitB (TΦ a)` and equals every vector that
  does.  (Inverses are then preserved automatically; not asserted.)
- Nothing looks false to me.
-/
namespace RoundTrip.V8_13
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

/-- (8.8): `v` is `1_a = (1_x, Ts(1_x)⁻¹ a)`, `x = p(a)`. -/
def IsTUnitB (X : EpGroupoid Obj Mor) (hs : X.PMor.IsScSmoothMap X.PObj X.src)
    (a : X.PObj.TangentSpace) (v : X.PMor.TangentSpace) : Prop :=
  baseB X.PMor v = X.unit (baseB X.PObj a) ∧ MPolyfold.tangentMap hs v = a

end

/-- Theorem 8.1.11: the tangent `(TΦ, T𝚽)` of an sc-smooth functor is an sc-smooth functor
between the tangent ep-groupoids. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y),
    ∃ (hsX : X.PMor.IsScSmoothMap X.PObj X.src) (htX : X.PMor.IsScSmoothMap X.PObj X.tgt)
      (hsY : Y.PMor.IsScSmoothMap Y.PObj Y.src) (htY : Y.PMor.IsScSmoothMap Y.PObj Y.tgt),
      -- `TΦ`, `T𝚽` sc-smooth
      X.PObj.tangentPolyfold.IsScSmoothMap Y.PObj.tangentPolyfold
        (MPolyfold.tangentMap F.isScSmoothMap_obj) ∧
      X.PMor.tangentPolyfold.IsScSmoothMap Y.PMor.tangentPolyfold
        (MPolyfold.tangentMap F.isScSmoothMap_mor) ∧
      -- sources and targets
      (∀ k : X.PMor.TangentSpace,
        MPolyfold.tangentMap hsY (MPolyfold.tangentMap F.isScSmoothMap_mor k) =
          MPolyfold.tangentMap F.isScSmoothMap_obj (MPolyfold.tangentMap hsX k)) ∧
      (∀ k : X.PMor.TangentSpace,
        MPolyfold.tangentMap htY (MPolyfold.tangentMap F.isScSmoothMap_mor k) =
          MPolyfold.tangentMap F.isScSmoothMap_obj (MPolyfold.tangentMap htX k)) ∧
      -- composition: `T𝚽(ψ ∘ φ)(k ∘ h) = T𝚽(ψ)(k) ∘ T𝚽(φ)(h)`
      (∀ l k : X.PMor.TangentSpace, MPolyfold.tangentMap hsX l = MPolyfold.tangentMap htX k →
        MPolyfold.tangentMap F.isScSmoothMap_mor (tCompB X hsX l k) =
          tCompB Y hsY (MPolyfold.tangentMap F.isScSmoothMap_mor l)
            (MPolyfold.tangentMap F.isScSmoothMap_mor k)) ∧
      -- units: `T𝚽(1_a) = 1_{TΦ(a)}`
      (∀ (a : X.PObj.TangentSpace) (v : X.PMor.TangentSpace), IsTUnitB X hsX a v →
        IsTUnitB Y hsY (MPolyfold.tangentMap F.isScSmoothMap_obj a)
            (MPolyfold.tangentMap F.isScSmoothMap_mor v) ∧
          ∀ w : Y.PMor.TangentSpace,
            IsTUnitB Y hsY (MPolyfold.tangentMap F.isScSmoothMap_obj a) w →
              MPolyfold.tangentMap F.isScSmoothMap_mor v = w)

end RoundTrip.V8_13
