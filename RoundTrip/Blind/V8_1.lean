import Polyfold
/-! Blind formalization of V8_1 (the text's Part II, §8.1, (8.1)–(8.9), pp. 357–359; 2017
pp. 257–258).

Text: `T(X, 𝐗) = (TX, T𝐗)` (8.1), to be made an ep-groupoid with object M-polyfold `TX` and
morphism M-polyfold `T𝐗`; `(φ, h) ∈ T_φ𝐗` is a morphism `Ts(φ)(h) → Tt(φ)(h)` (8.2), so
`s_T(φ, h) = Ts(φ)(h)`, `t_T(φ, h) = Tt(φ)(h)` (8.3); if `Ts(ψ)(k) = Tt(φ)(h)` (8.4), which implies
`s(ψ) = t(φ)`, then `(ψ, k) ∘ (φ, h) = (ψ ∘ φ, Ts(ψ ∘ φ)⁻¹(Ts(φ)(h)))` (8.5), where
`k = Ts(ψ)⁻¹(Tt(φ)(h))`; shorter `k ∘ h = Ts(p(k) ∘ p(h))⁻¹ Ts(p(h))(h)` (8.6); the unit at
`a ∈ T_xX` is `1_a = (1_x, h_a)` with `Ts(1_x)(h_a) = a = Tt(1_x)(h_a)` (8.7), so
`u_T(a) = (1_x, Ts(1_x)⁻¹(a))` (8.8); the inverse is `ι_T(φ, k) = (φ⁻¹, Tι(φ)(k))` (8.9).

Choices:
- This item is a definition (with two embedded claims: "which implies `s(ψ) = t(φ)`" and
  "`Tt(1_x)(h_a) = a`", plus the presupposition that `Ts(φ) : T_φ𝐗 → T_{s(φ)}X` is invertible).
  Setting: `Obj Mor : Type` (universe 0; the tangent spaces are then in `Type 1`, the project's
  `TangentSpace` of a type in `Type u` being in `Type (max u 1)`), Hausdorff paracompact,
  `X : EpGroupoid Obj Mor` (the text's ep-groupoid: `RoundTrip/Blind/V7_3.lean`).
- Tangent notions from Part I (project definitions, as in `RoundTrip/Blind/V7_5.lean`,
  `V2_25.lean`): `TX` is `MPolyfold.TangentSpace` with the M-polyfold structure
  `MPolyfold.tangentPolyfold`; `p : TX → X¹` is `tangentProj`; my `baseB P w` is `p(w)` seen in
  `X` (`levelVal 1`), my `fibreB P x = T_xX = p⁻¹(x)` (empty unless `x ∈ X₁`); the tangent map
  `Tf` of an sc-smooth `f` is `MPolyfold.tangentMap hf` (`[(x, φ, h)] ↦ [(f x, ψ, …)]`).  A tangent
  vector "`(φ, h) ∈ T_φ𝐗`" is an element `h` of `T𝐗` with `baseB h = φ`; `Ts(φ)(h)` is `Ts h`.
- `Ts`, `Tt`, `Tι` need `s`, `t`, `ι` sc-smooth; B asserts proofs exist (∃; by proof irrelevance
  the maps do not depend on them).
- Presupposition of `Ts(φ)⁻¹` (and of "`k = Ts(ψ)⁻¹(Tt(φ)(h))`", i.e. `k` is determined by `ψ`,
  `h`): for `φ ∈ 𝐗₁`, `Ts` maps `T_φ𝐗` bijectively onto `T_{s(φ)}X`.  Linearity of `Ts(φ)` is
  not asserted here.
- (8.5)/(8.6) read: `k ∘ h` is the vector over `ψ ∘ φ = comp (p k) (p h)` whose `Ts` is `Ts h`
  (given the presupposition, that is `Ts(ψ ∘ φ)⁻¹(Ts(φ)(h))`).  The text's "`∈ T_{φ∘ψ}𝐗`" is a
  misprint for `T_{ψ∘φ}𝐗` (`φ ∘ ψ` is not composable in general; the formula itself lies in
  `T_{ψ∘φ}𝐗`); I use `ψ ∘ φ`.  The composition is only claimed on composable pairs
  `Ts k = Tt h`.
- (8.7)/(8.8): `u_T(a)` is the vector over `1_x`, `x = p(a)`, with `Ts(u_T a) = a`; the claim
  `Tt(u_T a) = a` is asserted.  (8.9): `ι_T = Tι`.
- The project's structure: B asserts that the project's tangent ep-groupoid
  `EpGroupoid.tangentEpGroupoid` has object/morphism M-polyfolds `tangentPolyfold` of `X`, `𝐗`,
  and that its groupoid, the project's `tangentGroupoidStr`, and the named maps `tSrc`, `tTgt`,
  `tComp`, `tUnit`, `tInv`, `tBase` (vocabulary docstrings: (8.3)–(8.9)) are the maps above
  (`comp` only on composable pairs, `unit` by its characterization; no equality of structures
  is asserted, so junk values off composable pairs do not matter).
- Nothing looks false to me (apart from the misprint).
-/
namespace RoundTrip.V8_1
open Polyfold

universe u

/-- The base point `p(w) ∈ Z₁ ⊆ Z` of a tangent vector `w ∈ TZ`. -/
def baseB {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
    (w : P.TangentSpace) : Z :=
  P.levelVal 1 (P.tangentProj w)

/-- The tangent space `T_zZ = p⁻¹(z)`. -/
def fibreB {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)
    (z : Z) : Set P.TangentSpace :=
  {w | baseB P w = z}

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- (8.5)/(8.6): `c` is `k ∘ h = Ts(ψ ∘ φ)⁻¹(Ts(φ)(h))`: it lies over `ψ ∘ φ = p(k) ∘ p(h)` and
`Ts c = Ts h`. -/
def IsTCompB (X : EpGroupoid Obj Mor) (hs : X.PMor.IsScSmoothMap X.PObj X.src)
    (k h c : X.PMor.TangentSpace) : Prop :=
  baseB X.PMor c = X.comp (baseB X.PMor k) (baseB X.PMor h) ∧
    MPolyfold.tangentMap hs c = MPolyfold.tangentMap hs h

/-- (8.7)/(8.8): `v` is `1_a = (1_x, Ts(1_x)⁻¹ a)`, `x = p(a)`. -/
def IsTUnitB (X : EpGroupoid Obj Mor) (hs : X.PMor.IsScSmoothMap X.PObj X.src)
    (a : X.PObj.TangentSpace) (v : X.PMor.TangentSpace) : Prop :=
  baseB X.PMor v = X.unit (baseB X.PObj a) ∧ MPolyfold.tangentMap hs v = a

/-- The groupoid `G` on `(TX, T𝐗)` has the structure maps (8.3)–(8.9). -/
def HasTextMapsB (X : EpGroupoid Obj Mor) (hs : X.PMor.IsScSmoothMap X.PObj X.src)
    (ht : X.PMor.IsScSmoothMap X.PObj X.tgt) (hι : X.PMor.IsScSmoothMap X.PMor X.inv)
    (G : GroupoidStr X.PObj.TangentSpace X.PMor.TangentSpace) : Prop :=
  -- (8.3)
  G.src = MPolyfold.tangentMap hs ∧ G.tgt = MPolyfold.tangentMap ht ∧
  -- (8.5)/(8.6), on composable pairs (8.4)
  (∀ k h : X.PMor.TangentSpace, MPolyfold.tangentMap hs k = MPolyfold.tangentMap ht h →
    IsTCompB X hs k h (G.comp k h)) ∧
  -- (8.8)
  (∀ a : X.PObj.TangentSpace, IsTUnitB X hs a (G.unit a)) ∧
  -- (8.9)
  G.inv = MPolyfold.tangentMap hι

end

/-- (8.1)–(8.9): `Ts : T_φ𝐗 → T_{s φ}X` is invertible, composability (8.4) implies
`s(ψ) = t(φ)`, the unit satisfies `Tt(1_a) = a`, and the project's tangent ep-groupoid and its
named structure maps are `(TX, T𝐗)` with the maps (8.3)–(8.9). -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ∃ (hs : X.PMor.IsScSmoothMap X.PObj X.src) (ht : X.PMor.IsScSmoothMap X.PObj X.tgt)
      (hι : X.PMor.IsScSmoothMap X.PMor X.inv),
      -- presupposition of `Ts(φ)⁻¹`: `Ts : T_φ𝐗 → T_{s(φ)}X` is a bijection, `φ ∈ 𝐗₁`
      (∀ φ ∈ X.PMor.levelSet 1,
        Set.BijOn (MPolyfold.tangentMap hs) (fibreB X.PMor φ) (fibreB X.PObj (X.src φ))) ∧
      -- (8.4) implies `s(ψ) = t(φ)`
      (∀ k h : X.PMor.TangentSpace, MPolyfold.tangentMap hs k = MPolyfold.tangentMap ht h →
        X.src (baseB X.PMor k) = X.tgt (baseB X.PMor h)) ∧
      -- (8.7): `Tt(1_x)(h_a) = a`
      (∀ (a : X.PObj.TangentSpace) (v : X.PMor.TangentSpace), IsTUnitB X hs a v →
        MPolyfold.tangentMap ht v = a) ∧
      -- (8.1): the project's `T(X, 𝐗)` is `(TX, T𝐗)` with the M-polyfolds `TX`, `T𝐗` ...
      X.tangentEpGroupoid.PObj = X.PObj.tangentPolyfold ∧
      X.tangentEpGroupoid.PMor = X.PMor.tangentPolyfold ∧
      -- ... and the structure maps (8.3)–(8.9), as are those of `tangentGroupoidStr`
      HasTextMapsB X hs ht hι X.tangentEpGroupoid.toGroupoidStr ∧
      HasTextMapsB X hs ht hι X.tangentGroupoidStr ∧
      -- the project's named maps
      X.tBase = baseB X.PMor ∧
      X.tSrc = MPolyfold.tangentMap hs ∧ X.tTgt = MPolyfold.tangentMap ht ∧
      (∀ k h : X.PMor.TangentSpace, MPolyfold.tangentMap hs k = MPolyfold.tangentMap ht h →
        IsTCompB X hs k h (X.tComp k h)) ∧
      (∀ a : X.PObj.TangentSpace, IsTUnitB X hs a (X.tUnit a)) ∧
      X.tInv = MPolyfold.tangentMap hι

end RoundTrip.V8_1
