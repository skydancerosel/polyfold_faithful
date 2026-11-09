import Polyfold
/-! Blind formalization of V8_9 (the text's Part II, §8.1, Lemma 8.1.7 (2017: 8.6), 2017 p. 262).

Text: for the category with object M-polyfold `TX` and morphism M-polyfold `T𝐗`, the source and
target maps `s_T`, `t_T` are surjective local sc-diffeomorphisms and all structure maps are
sc-smooth.  (Proof: `s_T`, `t_T` local sc-diffeomorphisms by construction; `1_q` depends
sc-smoothly on `q`; the inversion is `Tι`, an sc-diffeomorphism; the fibred product
`T𝐗 _{s_T}×_{t_T} T𝐗` is an M-polyfold and the multiplication is sc-smooth; alternatively it is
`Tm`.)

Choices:
- Setting: `Obj Mor : Type` (universe 0), Hausdorff paracompact, `X : EpGroupoid Obj Mor` (the
  text's ep-groupoid: `RoundTrip/Blind/V7_3.lean`); tangent spaces (Part I's `TangentSpace` with
  the M-polyfold structure `tangentPolyfold`, tangent maps `tangentMap`) in `Type 1`; `baseB` =
  the projection `p` seen in `X`.
- Structure maps (8.3)–(8.9): `s_T = Ts`, `t_T = Tt`, `ι_T = Tι` (`s`, `t`, `ι` sc-smooth is
  asserted, ∃ of the proofs); `m_T` = my `tCompB` (as in `RoundTrip/Blind/V8_3.lean`: a vector
  over `p(k) ∘ p(h)` with `Ts` equal to `Ts h`, chosen, junk `h` if none); `u_T` is characterized
  by `IsTUnitB` (over `1_{p(a)}`, `Ts(u_T a) = a`): B asserts such a map exists and that every such
  map is sc-smooth.
- "local sc-diffeomorphism" / "sc-smooth": the project's `MPolyfold.IsLocalScDiffeo`,
  `IsScSmoothMap` (the text's notions, `RoundTrip/Blind/V7_3.lean`).  "All structure maps":
  `s_T`, `t_T`, `u_T`, `ι_T`, `m_T`; for `m_T` the domain `T𝐗 _{s_T}×_{t_T} T𝐗` carries its
  structure as a sub-M-polyfold of `T𝐗 × T𝐗` (as in Definition 7.3 (4),
  `RoundTrip/Blind/V7_3.lean`); that it is a sub-M-polyfold is part of the claim (presupposed by
  "`m_T` is sc-smooth"); paracompactness instances are asserted to exist.
- Not formalized (proof only): "`Tι` is an sc-diffeomorphism", "`m_T = Tm`" (that is
  `RoundTrip/Blind/V8_4.lean`).
- Nothing looks false to me.
-/
namespace RoundTrip.V8_9
open Polyfold

universe u

/-- The base point `p(w) ∈ Z₁ ⊆ Z` of a tangent vector `w ∈ TZ`. -/
def baseB {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
    (w : P.TangentSpace) : Z :=
  P.levelVal 1 (P.tangentProj w)

/-- The multiplication `m` is sc-smooth on `M _s×_t M` with its structure as a sub-M-polyfold of
`M × M`. -/
def IsScSmoothMulOnB {O M : Type u} [TopologicalSpace O] [TopologicalSpace M] [T2Space M]
    [ParacompactSpace M] (s t : M → O) (m : M → M → M) (Q : MPolyfold M) : Prop :=
  ∃ (_ : ParacompactSpace (M × M))
    (hA : (Q.prod Q).IsSubMPolyfold (MPolyfold.fibredProduct s t))
    (_ : ParacompactSpace ↥(MPolyfold.fibredProduct s t)),
    ((Q.prod Q).subPolyfold hA).IsScSmoothMap Q (fun p => m p.1.1 p.1.2)

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

/-- Lemma 8.1.7: `s_T`, `t_T` are surjective local sc-diffeomorphisms `T𝐗 → TX`, and `s_T`,
`t_T`, `u_T`, `ι_T`, `m_T` are sc-smooth. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ∃ (hs : X.PMor.IsScSmoothMap X.PObj X.src) (ht : X.PMor.IsScSmoothMap X.PObj X.tgt)
      (hι : X.PMor.IsScSmoothMap X.PMor X.inv),
      -- `s_T`, `t_T` surjective local sc-diffeomorphisms
      Function.Surjective (MPolyfold.tangentMap hs) ∧
      Function.Surjective (MPolyfold.tangentMap ht) ∧
      X.PMor.tangentPolyfold.IsLocalScDiffeo X.PObj.tangentPolyfold (MPolyfold.tangentMap hs) ∧
      X.PMor.tangentPolyfold.IsLocalScDiffeo X.PObj.tangentPolyfold (MPolyfold.tangentMap ht) ∧
      -- all structure maps sc-smooth: `s_T`, `t_T`
      X.PMor.tangentPolyfold.IsScSmoothMap X.PObj.tangentPolyfold (MPolyfold.tangentMap hs) ∧
      X.PMor.tangentPolyfold.IsScSmoothMap X.PObj.tangentPolyfold (MPolyfold.tangentMap ht) ∧
      -- `u_T : q ↦ 1_q`
      (∃ uT : X.PObj.TangentSpace → X.PMor.TangentSpace, ∀ a, IsTUnitB X hs a (uT a)) ∧
      (∀ uT : X.PObj.TangentSpace → X.PMor.TangentSpace, (∀ a, IsTUnitB X hs a (uT a)) →
        X.PObj.tangentPolyfold.IsScSmoothMap X.PMor.tangentPolyfold uT) ∧
      -- `ι_T = Tι`
      X.PMor.tangentPolyfold.IsScSmoothMap X.PMor.tangentPolyfold (MPolyfold.tangentMap hι) ∧
      -- `m_T` on the M-polyfold `T𝐗 _{s_T}×_{t_T} T𝐗`
      IsScSmoothMulOnB (MPolyfold.tangentMap hs) (MPolyfold.tangentMap ht) (tCompB X hs)
        X.PMor.tangentPolyfold

end RoundTrip.V8_9
