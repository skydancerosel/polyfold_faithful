import Polyfold
/-! Blind formalization of V10_22 (the text's Part II, §10.4, Definition 10.4.1, p. 496 of the
Springer 2021 book; 2017: Definition 10.10, p. 357).

Text: a strong bundle equivalence is a strong bundle functor `Φ` covering an equivalence `ϕ` such
that (1) `Φ : W[i] → W'[i]`, `i = 0, 1`, are equivalences and (2) `Φ` is locally a strong bundle
isomorphism on objects and morphisms.

Choices:
- This item is a definition.  Setting as in `RoundTrip/Blind/V8_24.lean`: strong bundles
  `(P : W → X, μ)`, `(P' : W' → X', μ')` over ep-groupoids (`E : EpStrongBundle X B`,
  `E' : EpStrongBundle X' B'`, characterized in `RoundTrip/Blind/V8_20.lean`), all spaces in
  `Type` (universe 0); paracompactness of `𝐖 = 𝐗 ₛ×_P W`, `𝐖'` as instance hypotheses (true;
  needed for the ep-groupoids `(W, 𝐖)`, as in V8_22, V8_24).  `ϕ : X → X'` an `EpFunctor`,
  `Φ : (W, 𝐖) → (W', 𝐖')` an `EpFunctor` between the project's `E.toEpGroupoid`,
  `E'.toEpGroupoid` (`W[0] = (W, 𝐖)`, characterized in `RoundTrip/Blind/V8_22.lean`).
- "strong bundle functor covering `ϕ`": the project's `IsStrongBundleFunctor` (checked against
  the text in `RoundTrip/Blind/V8_24.lean`).  "equivalence" (for `ϕ` and for `Φ : W[0] → W'[0]`):
  the project's `EpFunctor.IsEquivalence` (Definition 10.1.1, `RoundTrip/Blind/V10_1.lean`).
- (1) for `i = 1` (`EquivOneB`, my own; the project has no ep-groupoid `W[1]`): objects
  `W[1] = W_{0,1}` (the project's `B.One`, `B.oneSet`, with the M-polyfold `B.toMPolyfold1`,
  V2_58), morphisms `𝐖[1]` = the `(φ, w) ∈ 𝐖` with `w ∈ W_{0,1}`.  An equivalence: `Φ` maps
  `W_{0,1}` into `W'_{0,1}`; a local sc-diffeomorphism `W[1] → W'[1]` on objects; faithful and full
  on the morphisms between points of `W_{0,1}` (those are the morphisms of `𝐖[1]`); and
  `|W[1]| → |W'[1]|` a homeomorphism, `|W[1]|` my quotient of `W[1]` by "isomorphic" with
  Mathlib's quotient topology.  The sc-smoothness of `Φ` on `W[1]`, `𝐖[1]` is part of the strong
  bundle functor condition (`IsStrongBundleMap` contains the level-`[1]` sc-smoothness) and is
  not repeated.
- (2) "locally a strong bundle isomorphism on objects and morphisms": every `x ∈ X` (resp.
  `φ ∈ 𝐗`) lies in a set `U` with `Φ : W|U → W'|U'` (resp. `𝚽 : 𝐖|U → 𝐖'|U'`, over the
  pull-back bundles `𝐖 → 𝐗`, `𝐖' → 𝐗'`) a strong bundle isomorphism covering `ϕ : U → U'`: the
  project's `StrongBundle.IsStrongBundleIsoOn` (read with `#print`: `ϕ` an sc-diffeomorphism
  `U → U'`, `Φ` an sc-diffeomorphism `P⁻¹(U) → P'⁻¹(U')` on level `[0]` and on level `[1]`,
  fibre-linear by the strong bundle map; `U`, `U'` are open since `IsScSmoothOn` requires it).
  Trusted as the text's "strong bundle isomorphism over `U`".
- B: the project's `IsStrongBundleEquivalence E E' ϕ Φ` is my `IsSBEquivB E E' ϕ Φ`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_22
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]

/-- Two points of `W[1] = W_{0,1}` are isomorphic in `W[1]`: there is a morphism of `(W, 𝐖)`
between them (a morphism `(φ, w)` with `w ∈ W_{0,1}` lies in `𝐖[1]`). -/
def IsoOneB (E : EpStrongBundle X B) (a b : B.One) : Prop :=
  ∃ m : pullbackSpace P X.src, E.toEpGroupoid.src m = B.oneVal a ∧ E.toEpGroupoid.tgt m = B.oneVal b

/-- **Definition 10.4.1 (1), `i = 1`**: `Φ : W[1] → W'[1]` is an equivalence: it maps `W_{0,1}`
into `W'_{0,1}`, is a local sc-diffeomorphism `W[1] → W'[1]` on objects, is faithful and full on
`W[1]`, and induces a homeomorphism `|W[1]| → |W'[1]|`.  (Its sc-smoothness on the objects and
morphisms of level `[1]` is part of the strong bundle functor condition.) -/
def EquivOneB (E : EpStrongBundle X B) (E' : EpStrongBundle X' B')
    (Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid) : Prop :=
  ∃ hmap : Set.MapsTo Φ.obj B.oneSet B'.oneSet,
    -- local sc-diffeomorphism on objects `W[1] → W'[1]`
    B.toMPolyfold1.IsLocalScDiffeo B'.toMPolyfold1 (B.oneRestrict B' Φ.obj hmap) ∧
    -- faithful on `W[1]`
    (∀ m m' : pullbackSpace P X.src, E.toEpGroupoid.src m ∈ B.oneSet →
      E.toEpGroupoid.src m = E.toEpGroupoid.src m' → E.toEpGroupoid.tgt m = E.toEpGroupoid.tgt m' →
        Φ.mor m = Φ.mor m' → m = m') ∧
    -- full on `W[1]`
    (∀ w₁ w₂ : W, w₁ ∈ B.oneSet → w₂ ∈ B.oneSet → ∀ m' : pullbackSpace P' X'.src,
      E'.toEpGroupoid.src m' = Φ.obj w₁ → E'.toEpGroupoid.tgt m' = Φ.obj w₂ →
        ∃ m : pullbackSpace P X.src, E.toEpGroupoid.src m = w₁ ∧ E.toEpGroupoid.tgt m = w₂ ∧
          Φ.mor m = m') ∧
    -- `|Φ| : |W[1]| → |W'[1]|` is a homeomorphism (quotient topologies of `W[1]`, `W'[1]`)
    ∃ e : Quot (IsoOneB E) ≃ₜ Quot (IsoOneB E'),
      ∀ a : B.One, e (Quot.mk _ a) = Quot.mk _ (B.oneRestrict B' Φ.obj hmap a)

/-- **Definition 10.4.1**: `Φ` is a strong bundle equivalence covering `ϕ`. -/
def IsSBEquivB (E : EpStrongBundle X B) (E' : EpStrongBundle X' B') (ϕ : EpFunctor X X')
    (Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid) : Prop :=
  -- a strong bundle functor covering `ϕ`
  ∃ hF : E.IsStrongBundleFunctor E' ϕ Φ,
    -- `ϕ` is an equivalence
    ϕ.IsEquivalence ∧
    -- (1) `Φ : W[0] → W'[0]` and `Φ : W[1] → W'[1]` are equivalences
    Φ.IsEquivalence ∧ EquivOneB E E' Φ ∧
    -- (2) `Φ : W → W'` is locally a strong bundle isomorphism
    (∀ x : Obj, ∃ (U : Set Obj) (U' : Set Obj'), x ∈ U ∧
      B.IsStrongBundleIsoOn B' hF.isStrongBundleMap_obj U U') ∧
    -- (2) `𝚽 : 𝐖 → 𝐖'` is locally a strong bundle isomorphism
    (∀ φ : Mor, ∃ (U : Set Mor) (U' : Set Mor'), φ ∈ U ∧
      StrongBundle.IsStrongBundleIsoOn _ _ hF.isStrongBundleMap_mor U U')

end

/-- Definition 10.4.1: the project's strong bundle equivalences are the text's. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    [ParacompactSpace (pullbackSpace P X.src)]
    (Obj' Mor' : Type) [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] (X' : EpGroupoid Obj' Mor')
    (W' : Type) [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] (P' : W' → Obj')
    [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] (B' : StrongBundle X'.PObj P')
    [ParacompactSpace (pullbackSpace P' X'.src)]
    (E : EpStrongBundle X B) (E' : EpStrongBundle X' B') (ϕ : EpFunctor X X')
    (Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid),
    E.IsStrongBundleEquivalence E' ϕ Φ ↔ IsSBEquivB E E' ϕ Φ

end RoundTrip.V10_22
