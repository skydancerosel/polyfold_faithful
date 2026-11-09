import Polyfold
/-! Blind formalization of V8_3 (the text's Part II, §8.1, Theorem 8.1.1 (2017: 8.1), p. 359;
2017 p. 258).

Text: `T(X, 𝐗) = (TX, T𝐗)` with the structure maps (8.3)–(8.9) is an ep-groupoid; if `(X, 𝐗)` is
tame, so is `T(X, 𝐗)`; the projections `p : TX → X¹`, `𝐩 : T𝐗 → 𝐗¹` define an sc-smooth functor
`(p, 𝐩) : T(X, 𝐗) → (X, 𝐗)¹`.

Choices:
- Setting: `Obj Mor : Type` (universe 0), Hausdorff paracompact, `X : EpGroupoid Obj Mor` (the
  text's ep-groupoid: `RoundTrip/Blind/V7_3.lean`).  The tangent spaces `TX`, `T𝐗` are then in
  `Type 1`, so the ep-groupoid notion is restated universe-polymorphically.
- Tangent notions (Part I, as in `RoundTrip/Blind/V7_5.lean`): `MPolyfold.TangentSpace` with the
  M-polyfold structure `tangentPolyfold`, `tangentProj : TX → X¹`, tangent maps
  `MPolyfold.tangentMap`; `baseB` = `p` seen in `X`, `fibreB P x = T_xX`.
- The structure maps (8.3)–(8.9) (see `RoundTrip/Blind/V8_1.lean`): `s_T = Ts`, `t_T = Tt`,
  `ι_T = Tι`; the composite `k ∘ h = Ts(ψ ∘ φ)⁻¹(Ts(φ)(h))` is my `tCompB`: a vector over
  `p(k) ∘ p(h)` with the same `Ts` as `h`, chosen (junk `h` if there is none, which does not
  happen for composable pairs once `Ts` is fibrewise bijective); the unit `u_T(a)` is
  characterized by `IsTUnitB` (over `1_{p(a)}`, `Ts(u_T a) = a`).  `Ts`, `Tt`, `Tι` need `s`, `t`,
  `ι` sc-smooth: B asserts such proofs exist.
- "is an ep-groupoid": there is a groupoid `G` (the project's `GroupoidStr`, = the text's
  groupoid by `RoundTrip/Blind/V7_1.lean`) on `(TX, T𝐗)` with these structure maps (`comp`
  prescribed on composable pairs `Ts k = Tt h` only, as in Definition 7.1), which with the
  M-polyfolds `TX`, `T𝐗` satisfies Definition 7.3: `IsEpGroupoidB`, copied from
  `RoundTrip/Blind/V7_3.lean` (local sc-diffeomorphisms `s, t`; `u, ι` sc-smooth; properness with
  "proper" = continuous with compact preimages of compacts; `m` sc-smooth on the fibred product
  with its structure as a sub-M-polyfold of the product), universe-polymorphic.
- Tame: Definition 7.6, the object M-polyfold is tame (`MPolyfold.IsTame`, the text's notion by
  `RoundTrip/Blind/V2_43.lean`): `X` tame ⇒ `TX` tame.
- `(X, 𝐗)¹`: the ep-groupoid with object M-polyfold `X¹` (`MPolyfold.shift`, the level `X₁` with
  the charts `(V₁, φ, (O₁, C₁, E¹))`), morphism M-polyfold `𝐗¹`, and the restricted structure maps.
  I do not use the project's `EpGroupoid.liftOne`; "functor" is expressed through the inclusion
  `X¹ → X` (injective): `p(Ts k) = s(𝐩 k)`, `p(Tt k) = t(𝐩 k)`, `𝐩(k ∘ h) = 𝐩 k ∘ 𝐩 h` on
  composable pairs, `𝐩(1_a) = 1_{p(a)}`; "sc-smooth": `p : TX → X¹` and `𝐩 : T𝐗 → 𝐗¹` are
  sc-smooth.  These are stated for the groupoid `G` of the first part.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_3
open Polyfold

universe u

/-- The base point `p(w) ∈ Z₁ ⊆ Z` of a tangent vector `w ∈ TZ`. -/
def baseB {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
    (w : P.TangentSpace) : Z :=
  P.levelVal 1 (P.tangentProj w)

/-- A proper map: continuous, with compact preimages of compact sets. -/
def IsProperB {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α → β) : Prop :=
  Continuous f ∧ ∀ K : Set β, IsCompact K → IsCompact (f ⁻¹' K)

section
variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **Definition 7.3 (4)**: `m(φ, ψ) = φ ∘ ψ` is sc-smooth on `𝐗 ₛ×ₜ 𝐗` with its structure as a
sub-M-polyfold of `𝐗 × 𝐗` (as in `RoundTrip/Blind/V7_3.lean`). -/
def IsScSmoothMulB (G : GroupoidStr Obj Mor) (Q : MPolyfold Mor) : Prop :=
  ∃ (_ : ParacompactSpace (Mor × Mor))
    (hA : (Q.prod Q).IsSubMPolyfold (MPolyfold.fibredProduct G.src G.tgt))
    (_ : ParacompactSpace ↥(MPolyfold.fibredProduct G.src G.tgt)),
    ((Q.prod Q).subPolyfold hA).IsScSmoothMap Q (fun p => G.comp p.1.1 p.1.2)

/-- **Definition 7.3**: the groupoid `G` with the M-polyfolds `P` (objects), `Q` (morphisms) is
an ep-groupoid (as in `RoundTrip/Blind/V7_3.lean`). -/
def IsEpGroupoidB (G : GroupoidStr Obj Mor) (P : MPolyfold Obj) (Q : MPolyfold Mor) : Prop :=
  Q.IsLocalScDiffeo P G.src ∧ Q.IsLocalScDiffeo P G.tgt ∧
  P.IsScSmoothMap Q G.unit ∧ Q.IsScSmoothMap Q G.inv ∧
  (∀ x : Obj, ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧
    IsProperB ((G.src ⁻¹' closure V).domRestrict G.tgt)) ∧
  IsScSmoothMulB G Q

end

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

/-- Theorem 8.1.1: `(TX, T𝐗)` with (8.3)–(8.9) is an ep-groupoid, tame if `X` is, and
`(p, 𝐩) : T(X, 𝐗) → (X, 𝐗)¹` is an sc-smooth functor. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ∃ (hs : X.PMor.IsScSmoothMap X.PObj X.src) (ht : X.PMor.IsScSmoothMap X.PObj X.tgt)
      (hι : X.PMor.IsScSmoothMap X.PMor X.inv),
      (∃ G : GroupoidStr X.PObj.TangentSpace X.PMor.TangentSpace,
        -- the structure maps (8.3)–(8.9)
        G.src = MPolyfold.tangentMap hs ∧ G.tgt = MPolyfold.tangentMap ht ∧
        (∀ k h : X.PMor.TangentSpace, MPolyfold.tangentMap hs k = MPolyfold.tangentMap ht h →
          G.comp k h = tCompB X hs k h) ∧
        (∀ a : X.PObj.TangentSpace, IsTUnitB X hs a (G.unit a)) ∧
        G.inv = MPolyfold.tangentMap hι ∧
        -- (1) an ep-groupoid with the M-polyfolds `TX`, `T𝐗`
        IsEpGroupoidB G X.PObj.tangentPolyfold X.PMor.tangentPolyfold ∧
        -- (3) `(p, 𝐩) : T(X, 𝐗) → (X, 𝐗)¹` is a functor ...
        (∀ k : X.PMor.TangentSpace, baseB X.PObj (G.src k) = X.src (baseB X.PMor k)) ∧
        (∀ k : X.PMor.TangentSpace, baseB X.PObj (G.tgt k) = X.tgt (baseB X.PMor k)) ∧
        (∀ k h : X.PMor.TangentSpace, G.src k = G.tgt h →
          baseB X.PMor (G.comp k h) = X.comp (baseB X.PMor k) (baseB X.PMor h)) ∧
        (∀ a : X.PObj.TangentSpace, baseB X.PMor (G.unit a) = X.unit (baseB X.PObj a)) ∧
        -- ... which is sc-smooth into `X¹`, `𝐗¹`
        X.PObj.tangentPolyfold.IsScSmoothMap X.PObj.shift X.PObj.tangentProj ∧
        X.PMor.tangentPolyfold.IsScSmoothMap X.PMor.shift X.PMor.tangentProj) ∧
      -- (2) tame if `X` is tame
      (X.PObj.IsTame → X.PObj.tangentPolyfold.IsTame)

end RoundTrip.V8_3
