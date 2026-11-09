import Polyfold
/-! Blind formalization of V10_23 (the text's Part II, §10.4, the pull-back and the push-forward
of section functors, (10.15)–(10.17) and (10.22), pp. 496–498 of the Springer 2021 book; 2017
pp. 357–360).

Text: `Φ*f' = Φ_x⁻¹ ∘ f' ∘ ϕ` and `Φ_*f(x') = μ'(σ, Φ(f(x)))` for `σ : ϕ(x) → x'`, independent
of the choices by (10.22); both are section functors and mutually inverse.

Choices:
- Setting as in my `RoundTrip/Blind/V10_22.lean` (strong bundles `E`, `E'` over ep-groupoids, all
  spaces in `Type`, paracompactness of `𝐖`, `𝐖'` as instance hypotheses).  `Φ` is a strong bundle
  equivalence covering `ϕ` in the text's sense, my `IsSBEquivB` of V10_22 (copied; the project's
  `IsStrongBundleEquivalence` is not used).
- "section functor": sc-smooth section functor, Definition 8.3.4 (1), my
  `IsScSmoothSectionFunctorB` (copied from `RoundTrip/Blind/V8_26.lean`), for `(P, μ)` and
  `(P', μ')`.  Both maps are read on `Γ(P', μ')`, `Γ(P, μ)`.
- `Φ_x : W_x → W'_{ϕ(x)}` is the restriction of `Φ` to the fibre; `Φ_x⁻¹` presupposes that it is
  bijective, asserted as (a).  `pullB` (my own) picks `w ∈ W_x` with `Φ(w) = f'(ϕ(x))`; by (a)
  this is `Φ_x⁻¹(f'(ϕ(x)))`.  (b) says that such `w` exist for section functors and that
  `Φ*f'` is a section functor.
- `pushB` (my own) picks `x` and `σ : ϕ(x) → x'` (with the membership `(σ, Φ(f x)) ∈ 𝐗' ₛ×_{P'} W'`)
  and takes `μ'(σ, Φ(f(x)))`.  (c) every `x'` admits a choice (presupposed by the definition);
  (d) "independent of the choices" (10.22): `Φ_*f(x') = μ'(σ, Φ(f(x)))` for every choice
  `(x, σ)`, so any two choices give the same value; and `Φ_*f` is a section functor.
- (e) "mutually inverse": `Φ*(Φ_*f) = f` on `Γ(P, μ)` and `Φ_*(Φ*f') = f'` on `Γ(P', μ')`.
- The individual displays (10.15)–(10.17) are not visible to me; the item's summary is
  formalized.  Linearity of `Φ*`, `Φ_*` is not claimed (not in the item).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_23
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

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

/-- `f` is a section of `P`. -/
def IsSectionB (P : W → Obj) (f : Obj → W) : Prop :=
  ∀ x : Obj, P (f x) = x

/-- The zero `0_x ∈ W_x` (junk value). -/
def zeroB (P : W → Obj) [∀ x, AddCommGroup (P ⁻¹' {x})] (x : Obj) : W :=
  ((0 : P ⁻¹' {x}) : W)

/-- **Definition 8.3.4 (1)** (as in `RoundTrip/Blind/V8_26.lean`): `f` is an sc-smooth section
functor of `(P, μ)`. -/
def IsScSmoothSectionFunctorB (E : EpStrongBundle X B) (f : Obj → W) : Prop :=
  IsSectionB P f ∧ X.PObj.IsScSmoothMap B.toMPolyfold0 f ∧
  ∀ (φ : Mor) (x y : Obj), X.src φ = x → X.tgt φ = y →
    ∀ h : P (f x) = X.src φ, f y = E.μ ⟨(φ, f x), h⟩

end

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

open Classical in
/-- **The pull-back** `Φ*f' = Φ_x⁻¹ ∘ f' ∘ ϕ`: `Φ*f'(x)` is a (the) `w ∈ W_x` with
`Φ(w) = f'(ϕ(x))` (junk `0_x` if there is none). -/
noncomputable def pullB {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} (ϕ : EpFunctor X X')
    (Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid) (f' : Obj' → W') : Obj → W :=
  fun x => if h : ∃ w : W, P w = x ∧ Φ.obj w = f' (ϕ.obj x) then h.choose else zeroB P x

open Classical in
/-- **The push-forward** `Φ_*f(x') = μ'(σ, Φ(f(x)))` for a chosen `x ∈ X` and `σ : ϕ(x) → x'`
(junk `0_{x'}` if there is no such choice). -/
noncomputable def pushB {E : EpStrongBundle X B} (E' : EpStrongBundle X' B') (ϕ : EpFunctor X X')
    (Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid) (f : Obj → W) : Obj' → W' :=
  fun x' => if h : ∃ q : Obj × Mor', X'.src q.2 = ϕ.obj q.1 ∧ X'.tgt q.2 = x' ∧
      P' (Φ.obj (f q.1)) = X'.src q.2 then
    E'.μ ⟨(h.choose.2, Φ.obj (f h.choose.1)), h.choose_spec.2.2⟩ else zeroB P' x'

end

/-- The pull-back and the push-forward of section functors along a strong bundle equivalence:
well defined, section functors, mutually inverse. -/
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
    IsSBEquivB E E' ϕ Φ →
      -- (a) `Φ_x : W_x → W'_{ϕ(x)}` is bijective
      (∀ w₁ w₂ : W, P w₁ = P w₂ → Φ.obj w₁ = Φ.obj w₂ → w₁ = w₂) ∧
      (∀ (x : Obj) (w' : W'), P' w' = ϕ.obj x → ∃ w : W, P w = x ∧ Φ.obj w = w') ∧
      -- (b) `Φ*f' = Φ_x⁻¹ ∘ f' ∘ ϕ` is a section functor
      (∀ f' : Obj' → W', IsScSmoothSectionFunctorB E' f' →
        (∀ x : Obj, P (pullB ϕ Φ f' x) = x ∧ Φ.obj (pullB ϕ Φ f' x) = f' (ϕ.obj x)) ∧
        IsScSmoothSectionFunctorB E (pullB ϕ Φ f')) ∧
      -- (c) every `x'` admits some `σ : ϕ(x) → x'`
      (∀ x' : Obj', ∃ (x : Obj) (σ : Mor'), X'.src σ = ϕ.obj x ∧ X'.tgt σ = x') ∧
      -- (d) `Φ_*f(x') = μ'(σ, Φ(f(x)))` for every choice (10.22), and a section functor
      (∀ f : Obj → W, IsScSmoothSectionFunctorB E f →
        (∀ (x : Obj) (x' : Obj') (σ : Mor'), X'.src σ = ϕ.obj x → X'.tgt σ = x' →
          ∀ h : P' (Φ.obj (f x)) = X'.src σ, pushB E' ϕ Φ f x' = E'.μ ⟨(σ, Φ.obj (f x)), h⟩) ∧
        IsScSmoothSectionFunctorB E' (pushB E' ϕ Φ f)) ∧
      -- (e) mutually inverse
      (∀ f : Obj → W, IsScSmoothSectionFunctorB E f → pullB ϕ Φ (pushB E' ϕ Φ f) = f) ∧
      (∀ f' : Obj' → W', IsScSmoothSectionFunctorB E' f' → pushB E' ϕ Φ (pullB ϕ Φ f') = f')

end RoundTrip.V10_23
