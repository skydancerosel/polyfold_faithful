import Polyfold
/-! Blind formalization of V10_25 (the text's Part II, §10.4, Proposition 10.4.3, p. 499 of the
Springer 2021 book; 2017: Proposition 10.8, p. 360).

Text: for strong bundle equivalences `Φ, Ψ : (P, μ) → (P', μ')` with `|Φ| = |Ψ|`, `Φ_* f = Ψ_* f`
for every sc-smooth section functor `f` of `(P, μ)`.

Choices:
- Setting as in `RoundTrip/Blind/V8_20.lean`, `V8_24.lean`: strong bundles `P : W → X`,
  `P' : W' → X'` over ep-groupoids, `E : EpStrongBundle X B`, `E' : EpStrongBundle X' B'`
  (`μ = E.μ`, `μ' = E'.μ`), all spaces in `Type` (universe 0; the project's strong bundle
  equivalences need one universe); paracompactness of `𝐗 ₛ×_P W`, `𝐗' ₛ×_{P'} W'` as instance
  hypotheses (true, as in V8_20).  The functors `Φ, Ψ : (W, 𝐖) → (W', 𝐖')` are project
  `EpFunctor`s between the ep-groupoids `E.toEpGroupoid`, `E'.toEpGroupoid` (V8_22), covering
  `ϕ, ψ : X → X'`.
- "strong bundle equivalence" (Definition 10.4.1, an earlier item) is the project's
  `EpStrongBundle.IsStrongBundleEquivalence` (fields read with `#print`: a strong bundle functor,
  `ϕ` and `Φ` equivalences, `|Φ| : |W[1]| → |W'[1]|` a homeomorphism, local strong bundle
  isomorphisms on objects and morphisms); I trust it, I did not re-derive it.
- `|Φ| = |Ψ|`: equality of the induced maps `|W| → |W'|` of orbit spaces of `(W, 𝐖)`, `(W', 𝐖')`
  (the project's `GroupoidFunctor.orbitMap`, "the induced map `|G| → |H|`"), i.e. `|Φ|` on
  `W = W[0]`, not the map `|W[1]| → |W'[1]|` of Definition 10.4.1 (which it restricts to).  The
  two equivalences may cover different `ϕ, ψ : X → X'`.
- "sc-smooth section functor": `f ∈ E.sectionFunctors` (the project's `Γ(P, μ)`, Definition 8.3.4,
  characterized in `RoundTrip/Blind/V8_26.lean`).
- The push-forward (`pushB`, my own, from the text's definition p. 498): `(Φ_* f)(x') =
  μ'(σ, Φ(f(x)))` for some `x ∈ X` and `σ : ϕ(x) → x'` in `𝐗'`, chosen with `Classical.choose`
  (the text shows the value does not depend on the choice); the condition `P'(Φ(f x)) = s(σ)`
  needed to apply `μ'` is part of the choice (it holds for sections and strong bundle functors).
  Junk value `0 ∈ W'_{x'}` when no `(x, σ)` exists (never, for an equivalence `ϕ`).  The project's
  `IsStrongBundleEquivalence.pushforward` is not used.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_25
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} {P : W → Obj}
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}

/-- The push-forward `Φ_* f` of a section `f` of `P` along a functor covering `ϕ` with object map
`Φ : W → W'`: `(Φ_* f)(x') = μ'(σ, Φ(f(x)))` for a chosen `x ∈ X` and `σ : ϕ(x) → x'`. -/
noncomputable def pushB (E' : EpStrongBundle X' B') (ϕ : EpFunctor X X') (Φ : W → W')
    (f : Obj → W) : Obj' → W' := fun x' => by
  classical
  exact if h : ∃ p : Obj × Mor', X'.src p.2 = ϕ.obj p.1 ∧ X'.tgt p.2 = x' ∧
      P' (Φ (f p.1)) = X'.src p.2 then
    E'.μ ⟨(h.choose.2, Φ (f h.choose.1)), h.choose_spec.2.2⟩
  else ((0 : P' ⁻¹' {x'}) : W')

end

/-- **Proposition 10.4.3**: if `|Φ| = |Ψ|`, then `Φ_* f = Ψ_* f` for every sc-smooth section
functor `f`. -/
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
    (E : EpStrongBundle X B) (E' : EpStrongBundle X' B') (ϕ ψ : EpFunctor X X')
    (Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid),
    E.IsStrongBundleEquivalence E' ϕ Φ → E.IsStrongBundleEquivalence E' ψ Ψ →
    -- `|Φ| = |Ψ| : |W| → |W'|`
    Φ.orbitMap = Ψ.orbitMap →
    ∀ f ∈ E.sectionFunctors, pushB E' ϕ Φ.obj f = pushB E' ψ Ψ.obj f

end RoundTrip.V10_25
