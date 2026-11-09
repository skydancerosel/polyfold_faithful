import Polyfold
/-! Blind formalization of V8_14 (the text's Part II, §8.1, Theorem 8.1.12 (2017: 8.3), p. 366;
2017 p. 266).

Text: the tangent gives a functor `T : 𝓔𝓟 → 𝓔𝓟`, `X ↦ TX`, `(Φ : X → Y) ↦ TΦ`.  In particular
`TΦ` preserves the composition and the other structure maps.  `T` preserves tameness: `X` tame
⇒ `TX` tame.

Choices:
- Setting: ep-groupoids on spaces in `Type` (universe 0), Hausdorff paracompact (the text's
  ep-groupoids: `RoundTrip/Blind/V7_3.lean`); morphisms of `𝓔𝓟` are the project's `EpFunctor`s
  (= Definition 7.7 by `RoundTrip/Blind/V7_9.lean`).  The tangent spaces are in `Type 1`
  (Part I's `TangentSpace`), so in Lean `T` goes from ep-groupoids in `Type` to ep-groupoids in
  `Type 1`; "endofunctor" is not expressible at a single universe level without the project's
  bundled `EP` (I do not use the project's `tangentFunctor`/`EP.tangent`).  I state the
  functor componentwise:
  (a) objects: `TX = (TX, T𝐗)` with the structure maps (8.3)–(8.9) is an ep-groupoid (as in
  `RoundTrip/Blind/V8_3.lean`: a `GroupoidStr` with `s_T = Ts`, `t_T = Tt`, `ι_T = Tι`, composite
  `tCompB` on composable pairs, unit characterized by `IsTUnitB`, satisfying my Definition 7.3
  `IsEpGroupoidB` with the M-polyfolds `tangentPolyfold`);
  (b) morphisms ("in particular"): `(TΦ, T𝚽)` is a morphism of `𝓔𝓟` between the tangents, i.e.
  sc-smooth and compatible with sources, targets, composition and units (as in
  `RoundTrip/Blind/V8_13.lean`);
  (c) functor laws: `T(id_X) = id_{TX}` and `T(Ψ ∘ Φ) = TΨ ∘ TΦ`, on objects and on morphisms (the
  identity and composite functors have the maps `id` and `G ∘ F`; their sc-smoothness, needed to
  form the tangent maps, is asserted, ∃ of the proofs);
  (d) tameness (Definition 7.6, `MPolyfold.IsTame` of the object M-polyfold).
- `s`, `t`, `ι` sc-smooth is asserted wherever their tangent maps are used (∃ of the proofs).
- Nothing looks false to me.
-/
namespace RoundTrip.V8_14
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

/-- `TX = (TX, T𝐗)` with the structure maps (8.3)–(8.9) is an ep-groupoid. -/
def TangentIsEpB (X : EpGroupoid Obj Mor) : Prop :=
  ∃ (hs : X.PMor.IsScSmoothMap X.PObj X.src) (ht : X.PMor.IsScSmoothMap X.PObj X.tgt)
    (hι : X.PMor.IsScSmoothMap X.PMor X.inv)
    (G : GroupoidStr X.PObj.TangentSpace X.PMor.TangentSpace),
    G.src = MPolyfold.tangentMap hs ∧ G.tgt = MPolyfold.tangentMap ht ∧
    (∀ k h : X.PMor.TangentSpace, MPolyfold.tangentMap hs k = MPolyfold.tangentMap ht h →
      G.comp k h = tCompB X hs k h) ∧
    (∀ a : X.PObj.TangentSpace, IsTUnitB X hs a (G.unit a)) ∧
    G.inv = MPolyfold.tangentMap hι ∧
    IsEpGroupoidB G X.PObj.tangentPolyfold X.PMor.tangentPolyfold

end

/-- `(TΦ, T𝚽)` is a morphism of `𝓔𝓟` between the tangent ep-groupoids (as in
`RoundTrip/Blind/V8_13.lean`). -/
def TangentIsMorB {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj'] [TopologicalSpace Mor']
    [T2Space Mor'] [ParacompactSpace Mor'] {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}
    (F : EpFunctor X Y) : Prop :=
  ∃ (hsX : X.PMor.IsScSmoothMap X.PObj X.src) (htX : X.PMor.IsScSmoothMap X.PObj X.tgt)
    (hsY : Y.PMor.IsScSmoothMap Y.PObj Y.src) (htY : Y.PMor.IsScSmoothMap Y.PObj Y.tgt),
    X.PObj.tangentPolyfold.IsScSmoothMap Y.PObj.tangentPolyfold
      (MPolyfold.tangentMap F.isScSmoothMap_obj) ∧
    X.PMor.tangentPolyfold.IsScSmoothMap Y.PMor.tangentPolyfold
      (MPolyfold.tangentMap F.isScSmoothMap_mor) ∧
    (∀ k : X.PMor.TangentSpace,
      MPolyfold.tangentMap hsY (MPolyfold.tangentMap F.isScSmoothMap_mor k) =
        MPolyfold.tangentMap F.isScSmoothMap_obj (MPolyfold.tangentMap hsX k)) ∧
    (∀ k : X.PMor.TangentSpace,
      MPolyfold.tangentMap htY (MPolyfold.tangentMap F.isScSmoothMap_mor k) =
        MPolyfold.tangentMap F.isScSmoothMap_obj (MPolyfold.tangentMap htX k)) ∧
    (∀ l k : X.PMor.TangentSpace, MPolyfold.tangentMap hsX l = MPolyfold.tangentMap htX k →
      MPolyfold.tangentMap F.isScSmoothMap_mor (tCompB X hsX l k) =
        tCompB Y hsY (MPolyfold.tangentMap F.isScSmoothMap_mor l)
          (MPolyfold.tangentMap F.isScSmoothMap_mor k)) ∧
    (∀ (a : X.PObj.TangentSpace) (v : X.PMor.TangentSpace), IsTUnitB X hsX a v →
      IsTUnitB Y hsY (MPolyfold.tangentMap F.isScSmoothMap_obj a)
          (MPolyfold.tangentMap F.isScSmoothMap_mor v) ∧
        ∀ w : Y.PMor.TangentSpace,
          IsTUnitB Y hsY (MPolyfold.tangentMap F.isScSmoothMap_obj a) w →
            MPolyfold.tangentMap F.isScSmoothMap_mor v = w)

/-- Theorem 8.1.12: `X ↦ TX`, `Φ ↦ TΦ` is a functor `𝓔𝓟 → 𝓔𝓟` (on objects ep-groupoids, on
morphisms morphisms of `𝓔𝓟`, preserving identities and composition), and `T` preserves
tameness. -/
def B : Prop :=
  -- (a) on objects
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    TangentIsEpB X) ∧
  -- (b) on morphisms
  (∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y),
    TangentIsMorB F) ∧
  -- (c) `T(id) = id`
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ∃ (h₀ : X.PObj.IsScSmoothMap X.PObj (id : Obj → Obj))
      (h₁ : X.PMor.IsScSmoothMap X.PMor (id : Mor → Mor)),
      MPolyfold.tangentMap h₀ = id ∧ MPolyfold.tangentMap h₁ = id) ∧
  -- (c) `T(Ψ ∘ Φ) = TΨ ∘ TΦ`
  (∀ (Obj Mor Obj' Mor' Obj'' Mor'' : Type)
    [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
    [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (Z : EpGroupoid Obj'' Mor'')
    (F : EpFunctor X Y) (G : EpFunctor Y Z),
    ∃ (h₀ : X.PObj.IsScSmoothMap Z.PObj (G.obj ∘ F.obj))
      (h₁ : X.PMor.IsScSmoothMap Z.PMor (G.mor ∘ F.mor)),
      MPolyfold.tangentMap h₀ =
          MPolyfold.tangentMap G.isScSmoothMap_obj ∘ MPolyfold.tangentMap F.isScSmoothMap_obj ∧
        MPolyfold.tangentMap h₁ =
          MPolyfold.tangentMap G.isScSmoothMap_mor ∘ MPolyfold.tangentMap F.isScSmoothMap_mor) ∧
  -- (d) `T` preserves tameness
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    X.PObj.IsTame → X.PObj.tangentPolyfold.IsTame)

end RoundTrip.V8_14
