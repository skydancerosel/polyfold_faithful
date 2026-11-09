import Polyfold
/-! Blind formalization of V10_26 (the text's Part II, §10.4, Proposition 10.4.4, p. 499 of the
Springer 2021 book; 2017: Proposition 10.9, p. 360).

Text: for strong bundle equivalences `Φ : (P, μ) → (P', μ')` and `Ψ : (P', μ') → (P'', μ'')`,
`(Ψ ∘ Φ)^* = Φ^* ∘ Ψ^*` and `(Ψ ∘ Φ)_* = Ψ_* ∘ Φ_*`.

Choices:
- Setting as in my `RoundTrip/Blind/V10_25.lean`, with three strong bundles `P : W → X`,
  `P' : W' → X'`, `P'' : W'' → X''` over ep-groupoids (`E`, `E'`, `E''`), all spaces in `Type`;
  `Φ` covers `ϕ : X → X'`, `Ψ` covers `ψ : X' → X''`; both are strong bundle equivalences in the
  sense of the project's `IsStrongBundleEquivalence` (Definition 10.4.1; trusted, see V10_25).
- `Ψ ∘ Φ` is the project's `EpFunctor.comp` (`Ψ.comp Φ`, covering `ψ.comp ϕ`; checked to be the
  composite functor in `RoundTrip/Blind/V7_9.lean`).  That `Ψ ∘ Φ` is again a strong bundle
  equivalence is presupposed by the text but not asserted (my push-forward and pull-back do not
  need it).
- Push-forward `pushB` as in V10_25 (`(Φ_* f)(x') = μ'(σ, Φ(f(x)))` for a chosen `x` and
  `σ : ϕ(x) → x'`).  Pull-back (`pullB`, my own, from the text's definition p. 496):
  `(Φ^* f')(x) = Φ_x⁻¹(f'(ϕ(x)))`, the (unique, `Φ_x` being bijective) `w ∈ W_x` with
  `Φ(w) = f'(ϕ(x))`, chosen with `Classical.choose`; junk value `0 ∈ W_x` if there is none (never,
  for a section `f'` and a strong bundle equivalence).  The project's
  `IsStrongBundleEquivalence.pullback`/`pushforward` are not used.
- The equalities are of maps `Γ(P'', μ'') → Γ(P, μ)` and `Γ(P, μ) → Γ(P'', μ'')`, i.e. for every
  `f'' ∈ Γ(P'', μ'')` resp. `f ∈ Γ(P, μ)` (the project's `sectionFunctors`, V8_26).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_26
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} {P : W → Obj}
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}

/-- The push-forward `Φ_* f`: `(Φ_* f)(x') = μ'(σ, Φ(f(x)))` for a chosen `x ∈ X` and
`σ : ϕ(x) → x'`. -/
noncomputable def pushB (E' : EpStrongBundle X' B') (ϕ : EpFunctor X X') (Φ : W → W')
    (f : Obj → W) : Obj' → W' := fun x' => by
  classical
  exact if h : ∃ p : Obj × Mor', X'.src p.2 = ϕ.obj p.1 ∧ X'.tgt p.2 = x' ∧
      P' (Φ (f p.1)) = X'.src p.2 then
    E'.μ ⟨(h.choose.2, Φ (f h.choose.1)), h.choose_spec.2.2⟩
  else ((0 : P' ⁻¹' {x'}) : W')

/-- The pull-back `Φ^* f'`: `(Φ^* f')(x) = Φ_x⁻¹(f'(ϕ(x)))`, a chosen `w ∈ W_x` with
`Φ(w) = f'(ϕ(x))`. -/
noncomputable def pullB (P : W → Obj) [∀ x, AddCommGroup (P ⁻¹' {x})] (ϕ : EpFunctor X X')
    (Φ : W → W') (f' : Obj' → W') : Obj → W := fun x => by
  classical
  exact if h : ∃ w : W, P w = x ∧ Φ w = f' (ϕ.obj x) then h.choose else ((0 : P ⁻¹' {x}) : W)

end

/-- **Proposition 10.4.4**: `(Ψ ∘ Φ)^* = Φ^* ∘ Ψ^*` on `Γ(P'', μ'')` and
`(Ψ ∘ Φ)_* = Ψ_* ∘ Φ_*` on `Γ(P, μ)`. -/
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
    (Obj'' Mor'' : Type) [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
    [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor''] (X'' : EpGroupoid Obj'' Mor'')
    (W'' : Type) [TopologicalSpace W''] [T2Space W''] [ParacompactSpace W''] (P'' : W'' → Obj'')
    [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]
    (B'' : StrongBundle X''.PObj P'') [ParacompactSpace (pullbackSpace P'' X''.src)]
    (E : EpStrongBundle X B) (E' : EpStrongBundle X' B') (E'' : EpStrongBundle X'' B'')
    (ϕ : EpFunctor X X') (ψ : EpFunctor X' X'')
    (Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid) (Ψ : EpFunctor E'.toEpGroupoid E''.toEpGroupoid),
    E.IsStrongBundleEquivalence E' ϕ Φ → E'.IsStrongBundleEquivalence E'' ψ Ψ →
    -- `(Ψ ∘ Φ)^* = Φ^* ∘ Ψ^*`
    (∀ f'' ∈ E''.sectionFunctors,
      pullB P (ψ.comp ϕ) (Ψ.comp Φ).obj f'' = pullB P ϕ Φ.obj (pullB P' ψ Ψ.obj f'')) ∧
    -- `(Ψ ∘ Φ)_* = Ψ_* ∘ Φ_*`
    (∀ f ∈ E.sectionFunctors,
      pushB E'' (ψ.comp ϕ) (Ψ.comp Φ).obj f = pushB E'' ψ Ψ.obj (pushB E' ϕ Φ.obj f))

end RoundTrip.V10_26
