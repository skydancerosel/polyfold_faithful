import Polyfold
/-! Blind formalization of V10_27 (the text's Part II, §10.4, Theorem 10.4.5, pp. 500–501 of the
Springer 2021 book; 2017: Theorem 10.8, p. 362), as quoted ("without the Fred part").

Text: for a strong bundle equivalence `Φ : (P, μ) → (P', μ')`, `Φ_* : Γ(P, μ) → Γ(P', μ')` is a
bijection with inverse `Φ^*`; it depends only on `|Φ|`; it restricts to `Γ⁺` and to the
sc-Fredholm section functors.

Choices:
- Setting, push-forward `pushB` and pull-back `pullB` as in my `RoundTrip/Blind/V10_25.lean` and
  `V10_26.lean` (all spaces in `Type`; `Φ` covers `ϕ`; "strong bundle equivalence" the project's
  `IsStrongBundleEquivalence`, trusted; `Γ`, `Γ⁺`, `Fred` the project's `sectionFunctors`,
  `plusSectionFunctors`, `fredholmSectionFunctors` of Definition 8.3.4, characterized in
  `RoundTrip/Blind/V8_26.lean`).
- "bijection `Γ(P, μ) → Γ(P', μ')` with inverse `Φ^*`": (a) `Φ_*` maps `Γ(P, μ)` into
  `Γ(P', μ')`, (b) `Φ^*` maps `Γ(P', μ')` into `Γ(P, μ)`, (c) `Φ^* Φ_* f = f` on `Γ(P, μ)` and
  (d) `Φ_* Φ^* f' = f'` on `Γ(P', μ')`.
- "depends only on `|Φ|`" (e): for every strong bundle equivalence `Ψ : (P, μ) → (P', μ')`
  (covering any `ψ`) with `|Ψ| = |Φ|` (equal induced maps `|W| → |W'|`, the project's
  `GroupoidFunctor.orbitMap`), `Ψ_* = Φ_*` on `Γ(P, μ)` (then also `Ψ^* = Φ^*` on `Γ(P', μ')`, as
  inverses).
- "restricts to `Γ⁺` and to the sc-Fredholm section functors": the bijection restricts to
  bijections `Γ⁺(P, μ) → Γ⁺(P', μ')` and `Fred(P, μ) → Fred(P', μ')`, i.e. `Φ_*` maps each class
  of `P` into the corresponding class of `P'` and `Φ^*` maps back ((f), (g)).
- The title says "without the Fred part", but the quoted statement includes the restriction to
  sc-Fredholm section functors; I formalize the quoted statement, the Fredholm restriction being
  the separate conjunct (g).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_27
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

/-- **Theorem 10.4.5** (as quoted): `Φ_* : Γ(P, μ) → Γ(P', μ')` is a bijection with inverse
`Φ^*`, depends only on `|Φ|`, and restricts to `Γ⁺` and to the sc-Fredholm section functors. -/
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
    E.IsStrongBundleEquivalence E' ϕ Φ →
    -- (a) `Φ_*` maps `Γ(P, μ)` into `Γ(P', μ')`
    (∀ f ∈ E.sectionFunctors, pushB E' ϕ Φ.obj f ∈ E'.sectionFunctors) ∧
    -- (b) `Φ^*` maps `Γ(P', μ')` into `Γ(P, μ)`
    (∀ f' ∈ E'.sectionFunctors, pullB P ϕ Φ.obj f' ∈ E.sectionFunctors) ∧
    -- (c), (d) `Φ^*` is inverse to `Φ_*`
    (∀ f ∈ E.sectionFunctors, pullB P ϕ Φ.obj (pushB E' ϕ Φ.obj f) = f) ∧
    (∀ f' ∈ E'.sectionFunctors, pushB E' ϕ Φ.obj (pullB P ϕ Φ.obj f') = f') ∧
    -- (e) `Φ_*` depends only on `|Φ|`
    (∀ (ψ : EpFunctor X X') (Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid),
      E.IsStrongBundleEquivalence E' ψ Ψ → Ψ.orbitMap = Φ.orbitMap →
      ∀ f ∈ E.sectionFunctors, pushB E' ψ Ψ.obj f = pushB E' ϕ Φ.obj f) ∧
    -- (f) restriction to `Γ⁺`
    (∀ f ∈ E.plusSectionFunctors, pushB E' ϕ Φ.obj f ∈ E'.plusSectionFunctors) ∧
    (∀ f' ∈ E'.plusSectionFunctors, pullB P ϕ Φ.obj f' ∈ E.plusSectionFunctors) ∧
    -- (g) restriction to the sc-Fredholm section functors
    (∀ f ∈ E.fredholmSectionFunctors, pushB E' ϕ Φ.obj f ∈ E'.fredholmSectionFunctors) ∧
    (∀ f' ∈ E'.fredholmSectionFunctors, pullB P ϕ Φ.obj f' ∈ E.fredholmSectionFunctors)

end RoundTrip.V10_27
