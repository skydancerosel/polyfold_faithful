import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_27

/-! Round trip for V10_27 (2021 Theorem 10.4.5 = 2017 Theorem 10.8: `Φ_* : Γ(P, μ) → Γ(P', μ')`
is a bijection with inverse `Φ^*`, depends only on `|Φ|`, and restricts to `Γ⁺` and `Fred`).

`A` (universes at `0`) is the conjunction of the types of thirteen theorems: `theorem_10_4_5`
(`A1`: mutually inverse bijections `Γ ⇄ Γ'`, `Φ_* = Ψ_*` and `Φ^* = Ψ^*` when `|Φ| = |Ψ|`, both
restrict to `Γ⁺`; the `Fred` part is not formalized, as the project's docstring says), six
lemmas of its proof (`eqOn_pullback`, `isScSmoothSection_pullback`, `isScPlusSection_pullback`,
`exists_pushforward_local`, `isScSmoothSection_pushforward`, `isScPlusSection_pushforward`),
five general lemmas on M-polyfolds and strong bundles (`isScSmoothOn_to_pullback_one`,
`isScSmoothOn_of_forall_charts`, `IsStrongBundleIsoOn.restrict`, `.comp`, `.exists_comp`) and
the concrete instance `bijOn_pushforward_example`.

`B` has (a)–(f) (the same content as `A1`, for `B`'s own `pushB`/`pullB`) and (g): `Φ_*` and `Φ^*`
map sc-Fredholm section functors to sc-Fredholm section functors.

* Bridges (not item theorems): `pullB = h.pullback` on sections (`pullback_eq`), `pushB =
  h.pushforward` on functorial sections ((10.22) `pushforward_eq`).
* `A_to_B` fails at (g) only: `A` says nothing about `Fred` (the project lacks the invariance of
  `StrongBundle.IsScFredholmSection` under local strong bundle isomorphisms).  Proved here:
  `A_to_BnoFred : A → BnoFred`, with `BnoFred` = `B` without (g) (and `B → BnoFred`).
* `B_to_A`: `A1` from (a)–(f) (`theorem_10_4_5_of_B`: `Φ^* = Ψ^*` from `Φ_* = Ψ_*` and the inverse
  laws), `isScSmoothSection_pushforward` from (a), `isScPlusSection_pushforward` from (f),
  `bijOn_pushforward_example` from `theorem_10_4_5_of_B`.  The other ten conjuncts are statements
  `B` does not make (pull-backs of sections that are not functorial, local forms, general
  M-polyfold lemmas); they are re-proved outright below (the project's proofs, copied, from
  non-item lemmas). -/

namespace RoundTrip.V10_27
open Polyfold Set Function

/-! ### The project's statement (universes at `0`) -/

def A1 : Prop := type_of% @Polyfold.EpStrongBundle.theorem_10_4_5.{0}
def A2 : Prop := type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.eqOn_pullback.{0}
def A3 : Prop :=
  type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScSmoothSection_pullback.{0}
def A4 : Prop :=
  type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScPlusSection_pullback.{0}
def A5 : Prop :=
  type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.exists_pushforward_local.{0}
def A6 : Prop :=
  type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScSmoothSection_pushforward.{0}
def A7 : Prop :=
  type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScPlusSection_pushforward.{0}
def A8 : Prop := type_of% @Polyfold.StrongBundle.isScSmoothOn_to_pullback_one.{0, 0, 0, 0}
def A9 : Prop := type_of% @Polyfold.MPolyfold.isScSmoothOn_of_forall_charts.{0, 0}
def A10 : Prop := type_of% @Polyfold.StrongBundle.IsStrongBundleIsoOn.restrict.{0, 0, 0, 0}
def A11 : Prop := type_of% @Polyfold.StrongBundle.IsStrongBundleIsoOn.comp.{0, 0, 0, 0, 0, 0}
def A12 : Prop :=
  type_of% @Polyfold.StrongBundle.IsStrongBundleIsoOn.exists_comp.{0, 0, 0, 0, 0, 0}
def A13 : Prop := type_of% @Polyfold.StrongBundleEquivalenceExamples.bijOn_pushforward_example

def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A6 ∧ A7 ∧ A8 ∧ A9 ∧ A10 ∧ A11 ∧ A12 ∧ A13

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.theorem_10_4_5.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.eqOn_pullback.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScSmoothSection_pullback.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScPlusSection_pullback.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.exists_pushforward_local.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScSmoothSection_pushforward.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScPlusSection_pushforward.{0},
    @Polyfold.StrongBundle.isScSmoothOn_to_pullback_one.{0, 0, 0, 0},
    @Polyfold.MPolyfold.isScSmoothOn_of_forall_charts.{0, 0},
    @Polyfold.StrongBundle.IsStrongBundleIsoOn.restrict.{0, 0, 0, 0},
    @Polyfold.StrongBundle.IsStrongBundleIsoOn.comp.{0, 0, 0, 0, 0, 0},
    @Polyfold.StrongBundle.IsStrongBundleIsoOn.exists_comp.{0, 0, 0, 0, 0, 0},
    @Polyfold.StrongBundleEquivalenceExamples.bijOn_pushforward_example⟩

/-- `B` without its Fredholm part (g). -/
def BnoFred : Prop :=
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
    (∀ f ∈ E.sectionFunctors, pushB E' ϕ Φ.obj f ∈ E'.sectionFunctors) ∧
    (∀ f' ∈ E'.sectionFunctors, pullB P ϕ Φ.obj f' ∈ E.sectionFunctors) ∧
    (∀ f ∈ E.sectionFunctors, pullB P ϕ Φ.obj (pushB E' ϕ Φ.obj f) = f) ∧
    (∀ f' ∈ E'.sectionFunctors, pushB E' ϕ Φ.obj (pullB P ϕ Φ.obj f') = f') ∧
    (∀ (ψ : EpFunctor X X') (Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid),
      E.IsStrongBundleEquivalence E' ψ Ψ → Ψ.orbitMap = Φ.orbitMap →
      ∀ f ∈ E.sectionFunctors, pushB E' ψ Ψ.obj f = pushB E' ϕ Φ.obj f) ∧
    (∀ f ∈ E.plusSectionFunctors, pushB E' ϕ Φ.obj f ∈ E'.plusSectionFunctors) ∧
    (∀ f' ∈ E'.plusSectionFunctors, pullB P ϕ Φ.obj f' ∈ E.plusSectionFunctors)

theorem B_to_BnoFred : B → BnoFred := fun hB Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor'
    _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _ E E' ϕ Φ h => by
  obtain ⟨ha, hb, hc, hd, he, hf, hg, -, -⟩ :=
    hB Obj Mor X W P B Obj' Mor' X' W' P' B' E E' ϕ Φ h
  exact ⟨ha, hb, hc, hd, he, hf, hg⟩

/-! ### Bridges between `B`'s `pushB`/`pullB` and the project's `pushforward`/`pullback` -/

section Bridge

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
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'}

theorem pushB_eq {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (h : E.IsStrongBundleEquivalence E' ϕ Φ) {f : Obj → W} (hf : IsSection P f)
    (hfun : E.IsFunctorialSection hf) : pushB E' ϕ Φ.obj f = h.pushforward f := by
  funext x'
  have hex : ∃ p : Obj × Mor', X'.src p.2 = ϕ.obj p.1 ∧ X'.tgt p.2 = x' ∧
      P' (Φ.obj (f p.1)) = X'.src p.2 :=
    ⟨(h.preObj x', h.preMor x'), h.src_preMor x', h.tgt_preMor x',
      by rw [h.covers, hf, h.src_preMor]⟩
  unfold pushB
  rw [dif_pos hex, h.pushforward_eq hf hfun hex.choose_spec.1 hex.choose_spec.2.1]

theorem pullB_eq {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (h : E.IsStrongBundleEquivalence E' ϕ Φ) {f' : Obj' → W'} (hf' : IsSection P' f') :
    pullB P ϕ Φ.obj f' = h.pullback f' := by
  funext x
  have hex : ∃ w : W, P w = x ∧ Φ.obj w = f' (ϕ.obj x) :=
    ⟨h.pullback f' x, h.P_pullback f' x, h.obj_pullback hf' x⟩
  unfold pullB
  rw [dif_pos hex]
  exact (h.pullback_eq hf' hex.choose_spec.1 hex.choose_spec.2).symm

/-! ### `theorem_10_4_5` from `B` -/

/-- The first part of `theorem_10_4_5` from `B` (a)–(d). -/
theorem basic_of_B (hB : RoundTrip.V10_27.B) {ϕ : EpFunctor X X'}
    {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (h : E.IsStrongBundleEquivalence E' ϕ Φ) :
    MapsTo h.pushforward E.sectionFunctors E'.sectionFunctors ∧
      MapsTo h.pullback E'.sectionFunctors E.sectionFunctors ∧
      InvOn h.pullback h.pushforward E.sectionFunctors E'.sectionFunctors := by
  obtain ⟨ha, hb, hc, hd, -⟩ := hB Obj Mor X W P B Obj' Mor' X' W' P' B' E E' ϕ Φ h
  have hpush : MapsTo h.pushforward E.sectionFunctors E'.sectionFunctors := fun f hf => by
    have := ha f hf
    obtain ⟨hs, hfun⟩ := hf
    rwa [pushB_eq h hs.1 hfun] at this
  have hpull : MapsTo h.pullback E'.sectionFunctors E.sectionFunctors := fun f' hf' => by
    have := hb f' hf'
    obtain ⟨hs, -⟩ := hf'
    rwa [pullB_eq h hs.1] at this
  refine ⟨hpush, hpull, fun f hf => ?_, fun f' hf' => ?_⟩
  · have := hc f hf
    obtain ⟨hs, hfun⟩ := hf
    rwa [pushB_eq h hs.1 hfun, pullB_eq h (h.isSection_pushforward f)] at this
  · have := hd f' hf'
    obtain ⟨hs2, hfun2⟩ := hpull hf'
    obtain ⟨hs, -⟩ := hf'
    rwa [pullB_eq h hs.1, pushB_eq h hs2.1 hfun2] at this

/-- **`theorem_10_4_5` from `B`** ((a)–(f); `Φ^* = Ψ^*` from `Φ_* = Ψ_*` and the inverse laws). -/
theorem theorem_10_4_5_of_B (hB : RoundTrip.V10_27.B) {ϕ : EpFunctor X X'}
    {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (h : E.IsStrongBundleEquivalence E' ϕ Φ) :
    (MapsTo h.pushforward E.sectionFunctors E'.sectionFunctors ∧
      MapsTo h.pullback E'.sectionFunctors E.sectionFunctors ∧
      InvOn h.pullback h.pushforward E.sectionFunctors E'.sectionFunctors ∧
      BijOn h.pushforward E.sectionFunctors E'.sectionFunctors) ∧
    (∀ (ψ : EpFunctor X X') (Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid)
      (hΨ : E.IsStrongBundleEquivalence E' ψ Ψ), Φ.orbitMap = Ψ.orbitMap →
      EqOn h.pushforward hΨ.pushforward E.sectionFunctors ∧
      EqOn h.pullback hΨ.pullback E'.sectionFunctors) ∧
    MapsTo h.pushforward E.plusSectionFunctors E'.plusSectionFunctors ∧
    MapsTo h.pullback E'.plusSectionFunctors E.plusSectionFunctors := by
  obtain ⟨hpush, hpull, hinv⟩ := basic_of_B hB h
  obtain ⟨-, -, -, -, he, hf₁, hf₂, -⟩ := hB Obj Mor X W P B Obj' Mor' X' W' P' B' E E' ϕ Φ h
  -- `Φ_* = Ψ_*` for `|Φ| = |Ψ|`
  have hpeq : ∀ (ψ : EpFunctor X X') (Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid)
      (hΨ : E.IsStrongBundleEquivalence E' ψ Ψ), Φ.orbitMap = Ψ.orbitMap →
      EqOn h.pushforward hΨ.pushforward E.sectionFunctors := fun ψ Ψ hΨ hΦΨ f hf => by
    have := he ψ Ψ hΨ hΦΨ.symm f hf
    obtain ⟨hs, hfun⟩ := hf
    rw [pushB_eq hΨ hs.1 hfun, pushB_eq h hs.1 hfun] at this
    exact this.symm
  refine ⟨⟨hpush, hpull, hinv, hinv.bijOn hpush hpull⟩,
    fun ψ Ψ hΨ hΦΨ => ⟨hpeq ψ Ψ hΨ hΦΨ, fun f' hf' => ?_⟩, fun f hf => ?_, fun f' hf' => ?_⟩
  · -- `Φ^* f' = Φ^* Ψ_* Ψ^* f' = Φ^* Φ_* Ψ^* f' = Ψ^* f'`
    obtain ⟨-, hpullΨ, hinvΨ⟩ := basic_of_B hB hΨ
    have hg := hpullΨ hf'
    calc h.pullback f' = h.pullback (hΨ.pushforward (hΨ.pullback f')) := by
          rw [hinvΨ.2 hf']
      _ = h.pullback (h.pushforward (hΨ.pullback f')) := by
          rw [hpeq ψ Ψ hΨ hΦΨ hg]
      _ = hΨ.pullback f' := hinv.1 hg
  · have := hf₁ f hf
    obtain ⟨⟨hs, hfun⟩, -⟩ := hf
    rwa [pushB_eq h hs.1 hfun] at this
  · have := hf₂ f' hf'
    obtain ⟨⟨hs, -⟩, -⟩ := hf'
    rwa [pullB_eq h hs.1] at this

end Bridge

/-! ### The general lemmas, re-proved outright (the project's proofs, copied) -/

section IsoOn

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  {X'' : Type} [TopologicalSpace X''] [T2Space X''] [ParacompactSpace X''] {PX'' : MPolyfold X''}
  {Y'' : Type} [TopologicalSpace Y''] [T2Space Y''] [ParacompactSpace Y''] {P'' : Y'' → X''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]
  {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {B'' : StrongBundle PX'' P''}
  {f : X → X'} {Φ : Y → Y'} {h : B.IsStrongBundleMap B' f Φ} {U : Set X} {U' : Set X'}

open StrongBundle in
theorem restrict' (hi : B.IsStrongBundleIsoOn B' h U U') {g : X' → X}
    (hg : PX.IsScDiffeoOn PX' f g U U') {U₀ : Set X} (hU₀ : IsOpen U₀) (hsub : U₀ ⊆ U) :
    B.IsStrongBundleIsoOn B' h U₀ (U' ∩ g ⁻¹' U₀) := by
  obtain ⟨Ψ, hΨ⟩ := hi.isScDiffeoOn_zero
  obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
  refine ⟨⟨g, hg.restrict hU₀ hsub⟩, ⟨Ψ, ?_⟩, ⟨Ψ₁, ?_⟩⟩
  · have e := hΨ.restrict (hU₀.preimage B.continuous) (preimage_mono hsub)
    have hset : P' ⁻¹' U' ∩ Ψ ⁻¹' (P ⁻¹' U₀) = P' ⁻¹' (U' ∩ g ⁻¹' U₀) := by
      ext w'
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [← IsStrongBundleIsoOn.P_inv (h := h) hg hΨ h1]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [IsStrongBundleIsoOn.P_inv (h := h) hg hΨ h1]; exact h2⟩
    rwa [hset] at e
  · have hc : Continuous (P ∘ B.oneVal) := B.continuous.comp B.continuous_oneVal
    have e := hΨ₁.restrict (hU₀.preimage hc) (preimage_mono hsub)
    have hset : (P' ∘ B'.oneVal) ⁻¹' U' ∩ Ψ₁ ⁻¹' ((P ∘ B.oneVal) ⁻¹' U₀) =
        (P' ∘ B'.oneVal) ⁻¹' (U' ∩ g ⁻¹' U₀) := by
      ext w'
      simp only [mem_inter_iff, mem_preimage, Function.comp_apply]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [← IsStrongBundleIsoOn.P_inv_one (h := h) hg hΨ₁ h1]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [IsStrongBundleIsoOn.P_inv_one (h := h) hg hΨ₁ h1]; exact h2⟩
    rwa [hset] at e

theorem comp'' {f' : X' → X''} {Ψ : Y' → Y''}
    {h' : B'.IsStrongBundleMap B'' f' Ψ} {U'' : Set X''}
    (hi' : B'.IsStrongBundleIsoOn B'' h' U' U'') (hi : B.IsStrongBundleIsoOn B' h U U') :
    B.IsStrongBundleIsoOn B'' (h'.comp h) U U'' := by
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨g', hg'⟩ := hi'.isScDiffeoOn_base
  obtain ⟨Φi, hΦi⟩ := hi.isScDiffeoOn_zero
  obtain ⟨Ψi, hΨi⟩ := hi'.isScDiffeoOn_zero
  obtain ⟨Φ₁, hΦ₁⟩ := hi.isScDiffeoOn_one
  obtain ⟨Ψ₁, hΨ₁⟩ := hi'.isScDiffeoOn_one
  exact ⟨⟨_, hg'.comp hg⟩, ⟨_, hΨi.comp hΦi⟩, ⟨_, hΨ₁.comp hΦ₁⟩⟩

theorem exists_comp' {f' : X' → X''} {Ψ : Y' → Y''}
    {h' : B'.IsStrongBundleMap B'' f' Ψ} {V' : Set X'} {V'' : Set X''}
    (hi' : B'.IsStrongBundleIsoOn B'' h' V' V'') (hi : B.IsStrongBundleIsoOn B' h U U') {x : X}
    (hx : x ∈ U) (hfx : f x ∈ V') :
    ∃ (U₀ : Set X) (U₀'' : Set X''), x ∈ U₀ ∧ B.IsStrongBundleIsoOn B'' (h'.comp h) U₀ U₀'' := by
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨g', hg'⟩ := hi'.isScDiffeoOn_base
  have hU₀ : IsOpen (U ∩ f ⁻¹' V') :=
    hg.isScSmoothOn.continuousOn.isOpen_inter_preimage hg.isOpen_source hg'.isOpen_source
  have e₁ := restrict' hi hg hU₀ inter_subset_left
  have hsub : U' ∩ g ⁻¹' (U ∩ f ⁻¹' V') ⊆ V' := fun y hy => by
    have := hy.2.2
    rwa [mem_preimage, hg.right_inv y hy.1] at this
  have hopen : IsOpen (U' ∩ g ⁻¹' (U ∩ f ⁻¹' V')) :=
    (hg.restrict hU₀ inter_subset_left).isOpen_target
  exact ⟨U ∩ f ⁻¹' V', _, ⟨hx, hfx⟩, comp'' (restrict' hi' hg' hopen hsub) e₁⟩

end IsoOn

section PullbackOneOn

theorem isScSmoothOn_of_forall_charts' {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] {PY : MPolyfold Y} {f : X → Y} {U : Set X} (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ (φ : MChart X) (ψ : MChart Y), PX.IsChart φ ∧ PY.IsChart ψ ∧ x ∈ φ.source ∧
      φ.source ⊆ U ∧ MapsTo f φ.source ψ.source ∧
      IsScSmoothRetractMap φ.model.E φ.model.C φ.model.O ψ.model.E ψ.model.C ψ.model.O
        (ψ ∘ f ∘ φ.symm)) :
    PX.IsScSmoothOn PY f U := by
  have hloc : ∀ x ∈ U, ∃ φ : MChart X, x ∈ φ.source ∧ ContinuousOn f φ.source := fun x hx => by
    obtain ⟨φ, ψ, -, -, hx, -, hmaps, hsm⟩ := h x hx
    refine ⟨φ, hx, ?_⟩
    have h1 : ContinuousOn (ψ.symm ∘ (ψ ∘ f ∘ φ.symm) ∘ φ) φ.source :=
      (ψ.continuousOn_invFun.comp (hsm.continuousOn φ.model.isScRetract) hsm.mapsTo).comp
        φ.continuousOn_toFun fun z hz => φ.mapsTo_model z hz
    refine h1.congr fun z hz => ?_
    simp only [Function.comp_apply, φ.symm_apply_apply hz, ψ.symm_apply_apply (hmaps hz)]
  have hc : ContinuousOn f U := fun x hx => by
    obtain ⟨φ, hxφ, hcont⟩ := hloc x hx
    exact (hcont.continuousAt (φ.isOpen_source.mem_nhds hxφ)).continuousWithinAt
  refine MPolyfold.IsScSmoothOn.of_exists_charts hU hc fun x hx => ?_
  obtain ⟨φ, ψ, hφ, hψ, hxφ, hsub, hmaps, hsm⟩ := h x hx
  refine ⟨φ, ψ, φ.source, hφ, hψ, φ.isOpen_source, hxφ, fun z hz => ⟨hsub hz, hz⟩, hmaps, ?_⟩
  rw [φ.image_source]; exact hsm

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {f : Z → X} [ParacompactSpace (pullbackSpace P f)]
  {V : Type} [TopologicalSpace V] [T2Space V] [ParacompactSpace V] {Q : MPolyfold V}

open StrongBundle in
theorem isScSmoothOn_to_pullback_one' (B : StrongBundle PX P) (hf : PZ.IsScSmoothMap PX f)
    {ι : V → (B.pullback hf).One} {U : Set V}
    (ha : Q.IsScSmoothOn PZ (pullbackProj P f ∘ (B.pullback hf).oneVal ∘ ι) U)
    (hb : Q.IsScSmoothOn B.toMPolyfold1 (B.pullbackProj'One hf ∘ ι) U) :
    Q.IsScSmoothOn (B.pullback hf).toMPolyfold1 ι U := by
  refine isScSmoothOn_of_forall_charts' ha.isOpen fun v hv => ?_
  obtain ⟨d, hd, hq⟩ := PullbackChartData.exists_mem_atlas B hf ((B.pullback hf).oneVal (ι v))
  have hmem := B.toChart_mem_pullback_atlas hf hd ((B.pullback hf).oneVal (ι v))
  obtain ⟨φ, hφ, hvφ⟩ := Q.exists_isChart_mem_source v
  have hso : IsOpen ((U ∩ φ.source) ∩
      (pullbackProj P f ∘ (B.pullback hf).oneVal ∘ ι) ⁻¹' d.ψ.source) :=
    (ha.continuousOn.mono inter_subset_left).isOpen_inter_preimage
      (ha.isOpen.inter φ.isOpen_source) d.ψ.isOpen_source
  have hsub : (U ∩ φ.source) ∩ (pullbackProj P f ∘ (B.pullback hf).oneVal ∘ ι) ⁻¹' d.ψ.source ⊆
      φ.source := fun x hx => hx.1.2
  set φ' := φ.restrict hsub hso with hφ'def
  have hφ' : Q.IsChart φ' := MPolyfold.IsChart.restrict Q hφ hsub hso
  set y' := B.pullbackProj'One hf (ι v)
  refine ⟨φ', oneChart hmem (ι v), hφ', (B.pullback hf).isChart_oneChart hmem (ι v),
    ⟨⟨hv, hvφ⟩, hq⟩, fun x hx => hx.1.1, fun x hx => hx.2, ?_⟩
  have h1 := ha.smooth φ' d.ψ hφ' d.isChart φ'.source φ'.isOpen_source
    (fun x hx => ⟨hx.1.1, hx⟩) fun x hx => hx.2
  have h2 := hb.smooth φ' (oneChart hd y') hφ' (B.isChart_oneChart hd y') φ'.source
    φ'.isOpen_source (fun x hx => ⟨hx.1.1, hx⟩) fun x hx => d.mem_c_source hx.2
  have h3 : IsScSmoothRetractMap (d.c.φ.model.E.prod d.c.F.shift) (d.c.φ.model.C ×ˢ univ)
      (strongShiftOne d.c.K) d.c.F.shift univ univ Prod.snd :=
    (d.c.φ.model.E.prodSndOp d.c.F.shift).isScSmoothRetractMap d.c.isScRetract_one
      (mapsTo_univ _ _)
  have h4 := h3.comp h2 d.c.isScRetract_one
  rw [φ'.image_source] at h1 h4
  refine (IsScSmoothRetractMap.scPair h1 h4 ?_).congr fun _ _ => rfl
  intro z hz
  obtain ⟨x, hx, rfl⟩ : z ∈ φ' '' φ'.source := by rw [φ'.image_source]; exact hz
  change (oneChart hmem (ι v)) (ι (φ'.symm (φ' x))) ∈ strongShiftOne (d.toChart _).K
  rw [φ'.symm_apply_apply hx]
  exact (oneChart hmem (ι v)).toPartialEquiv.map_source
    (show ι x ∈ (oneChart hmem (ι v)).source from hx.2)

end PullbackOneOn

section Pullback

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
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'}
  {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}

theorem eqOn_pullback' (h : E.IsStrongBundleEquivalence E' ϕ Φ) {f' : Obj' → W'}
    (hf' : IsSection P' f') {U : Set Obj} {U' : Set Obj'}
    {g : Obj' → Obj} (hg : X.PObj.IsScDiffeoOn X'.PObj ϕ.obj g U U') {Ψ : W' → W}
    (hΨ : B.toMPolyfold0.IsScDiffeoOn B'.toMPolyfold0 Φ.obj Ψ (P ⁻¹' U) (P' ⁻¹' U')) :
    EqOn (Ψ ∘ f' ∘ ϕ.obj) (h.pullback f') U := fun z hz => by
  have hm : P' (f' (ϕ.obj z)) ∈ U' := by rw [hf' (ϕ.obj z)]; exact hg.mapsTo hz
  refine (h.pullback_eq hf' ?_ (hΨ.right_inv _ hm)).symm
  rw [StrongBundle.IsStrongBundleIsoOn.P_inv (h := h.isStrongBundleFunctor.isStrongBundleMap_obj)
    hg hΨ hm, hf' (ϕ.obj z), hg.left_inv z hz]

theorem isScSmoothSection_pullback' (h : E.IsStrongBundleEquivalence E' ϕ Φ) {f' : Obj' → W'}
    (hf' : B'.IsScSmoothSection f') : B.IsScSmoothSection (h.pullback f') := by
  refine ⟨h.isSection_pullback f', MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x _ => ?_⟩
  obtain ⟨U, U', hxU, hi⟩ := h.isLocalStrongBundleIso_obj x
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨Ψ, hΨ⟩ := hi.isScDiffeoOn_zero
  have hmaps : MapsTo (f' ∘ ϕ.obj) U (P' ⁻¹' U') := fun z hz => by
    change P' (f' (ϕ.obj z)) ∈ U'; rw [hf'.1 (ϕ.obj z)]; exact hg.mapsTo hz
  refine ⟨U, hg.isOpen_source, hxU, subset_univ _, ?_⟩
  exact (MPolyfold.IsScSmoothOn.comp hΨ.isScSmoothOn_inv
    (MPolyfold.IsScSmoothOn.comp hf'.2 hg.isScSmoothOn (mapsTo_univ _ _)) hmaps).congr
    (eqOn_pullback' h hf'.1 hg hΨ)

theorem isScPlusSection_pullback' (h : E.IsStrongBundleEquivalence E' ϕ Φ) {f' : Obj' → W'}
    (hf' : B'.IsScPlusSection f') : B.IsScPlusSection (h.pullback f') := by
  obtain ⟨hs', g', hg'f, hg'⟩ := (B'.isScPlusSection_iff f').1 hf'
  have key : ∀ x, ∃ U : Set Obj, IsOpen U ∧ x ∈ U ∧ ∃ G : Obj → B.One,
      X.PObj.IsScSmoothOn B.toMPolyfold1 G U ∧ ∀ z ∈ U, B.oneVal (G z) = h.pullback f' z := by
    intro x
    obtain ⟨U, U', hxU, hi⟩ := h.isLocalStrongBundleIso_obj x
    obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
    obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
    have hval : ∀ z, B'.oneVal (g' (ϕ.obj z)) = f' (ϕ.obj z) := fun z => congrFun hg'f _
    have hmaps : MapsTo (g' ∘ ϕ.obj) U ((P' ∘ B'.oneVal) ⁻¹' U') := fun z hz => by
      change P' (B'.oneVal (g' (ϕ.obj z))) ∈ U'
      rw [hval z, hs' (ϕ.obj z)]
      exact hg.mapsTo hz
    refine ⟨U, hg.isOpen_source, hxU, Ψ₁ ∘ g' ∘ ϕ.obj,
      MPolyfold.IsScSmoothOn.comp hΨ₁.isScSmoothOn_inv
        (MPolyfold.IsScSmoothOn.comp hg' hg.isScSmoothOn (mapsTo_univ _ _)) hmaps,
      fun z hz => ?_⟩
    have hm := hmaps hz
    refine (h.pullback_eq hs' ?_ ?_).symm
    · refine (StrongBundle.IsStrongBundleIsoOn.P_inv_one
        (h := h.isStrongBundleFunctor.isStrongBundleMap_obj) hg hΨ₁ hm).trans ?_
      change g (P' (B'.oneVal (g' (ϕ.obj z)))) = z
      rw [hval z, hs' (ϕ.obj z), hg.left_inv z hz]
    · have h2 := congrArg B'.oneVal (hΨ₁.right_inv _ hm)
      rw [StrongBundle.oneVal_oneRestrict] at h2
      exact h2.trans (hval z)
  choose U hU hxU G hG hGeq using key
  have hmem : ∀ z, h.pullback f' z ∈ B.oneSet := fun z =>
    hGeq z z (hxU z) ▸ B.oneVal_mem (G z z)
  refine (B.isScPlusSection_iff _).2 ⟨h.isSection_pullback f', fun z => B.oneMk _ (hmem z),
    funext fun z => B.oneVal_oneMk _ (hmem z), ?_⟩
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x _ =>
    ⟨U x, hU x, hxU x, subset_univ _, (hG x).congr fun z hz => ?_⟩
  apply B.oneVal_injective
  rw [hGeq x z hz, B.oneVal_oneMk]

theorem exists_pushforward_local' (h : E.IsStrongBundleEquivalence E' ϕ Φ) (x₀ : Obj') :
    ∃ (T : Set Mor') (V : Set Obj') (τ : Obj' → Mor') (U₁ : Set Obj) (U₁' : Set Obj')
      (g₁ : Obj' → Obj), X'.PMor.IsScDiffeoOn X'.PObj X'.tgt τ T V ∧
      X.PObj.IsScDiffeoOn X'.PObj ϕ.obj g₁ U₁ U₁' ∧ x₀ ∈ V ∩ τ ⁻¹' (X'.src ⁻¹' U₁') ∧
      IsOpen (V ∩ τ ⁻¹' (X'.src ⁻¹' U₁')) := by
  obtain ⟨T, V, τ, hσT, hτ⟩ := X'.isLocalScDiffeo_tgt (h.preMor x₀)
  obtain ⟨U₁, U₁', g₁, hy₀, hg₁⟩ := h.isEquivalence_base.isLocalScDiffeo_obj (h.preObj x₀)
  refine ⟨T, V, τ, U₁, U₁', g₁, hτ, hg₁, ?_, hτ.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage
    hτ.isOpen_target (hg₁.isOpen_target.preimage X'.continuous_src)⟩
  have h1 : X'.tgt (h.preMor x₀) = x₀ := h.tgt_preMor x₀
  have h2 := hτ.left_inv _ hσT
  rw [h1] at h2
  refine ⟨h1 ▸ hτ.mapsTo hσT, ?_⟩
  change X'.src (τ x₀) ∈ U₁'
  rw [h2, h.src_preMor]; exact hg₁.mapsTo hy₀

end Pullback

/-! ### The two directions -/

theorem A_to_BnoFred : A → BnoFred := by
  rintro ⟨h105, -⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
    E E' ϕ Φ h
  obtain ⟨⟨hpush, hpull, hinv, -⟩, heq, hplus, hplus'⟩ := h105 h
  refine ⟨fun f hf => ?_, fun f' hf' => ?_, fun f hf => ?_, fun f' hf' => ?_,
    fun ψ Ψ hΨ hΨΦ f hf => ?_, fun f hf => ?_, fun f' hf' => ?_⟩
  · obtain ⟨hs, hfun⟩ := hf
    rw [pushB_eq h hs.1 hfun]; exact hpush ⟨hs, hfun⟩
  · obtain ⟨hs, hfun⟩ := hf'
    rw [pullB_eq h hs.1]; exact hpull ⟨hs, hfun⟩
  · obtain ⟨hs, hfun⟩ := hf
    rw [pushB_eq h hs.1 hfun, pullB_eq h (h.isSection_pushforward f)]
    exact hinv.1 ⟨hs, hfun⟩
  · obtain ⟨hs2, hfun2⟩ := hpull hf'
    obtain ⟨hs, hfun⟩ := hf'
    rw [pullB_eq h hs.1, pushB_eq h hs2.1 hfun2]
    exact hinv.2 ⟨hs, hfun⟩
  · obtain ⟨hs, hfun⟩ := hf
    rw [pushB_eq hΨ hs.1 hfun, pushB_eq h hs.1 hfun]
    exact ((heq ψ Ψ hΨ hΨΦ.symm).1 ⟨hs, hfun⟩).symm
  · obtain ⟨⟨hs, hfun⟩, hp⟩ := hf
    rw [pushB_eq h hs.1 hfun]; exact hplus ⟨⟨hs, hfun⟩, hp⟩
  · obtain ⟨⟨hs, hfun⟩, hp⟩ := hf'
    rw [pullB_eq h hs.1]; exact hplus' ⟨⟨hs, hfun⟩, hp⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun h => theorem_10_4_5_of_B hB h, @eqOn_pullback', @isScSmoothSection_pullback',
    @isScPlusSection_pullback', @exists_pushforward_local', ?_, ?_, @isScSmoothOn_to_pullback_one',
    @isScSmoothOn_of_forall_charts', @restrict', @comp'', @exists_comp', ?_⟩
  · -- `isScSmoothSection_pushforward` from (a)
    intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
      E E' ϕ Φ h f hf hfun
    exact ((basic_of_B hB h).1 ⟨hf, hfun⟩).1
  · -- `isScPlusSection_pushforward` from (f)
    intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
      E E' ϕ Φ h f hf hfun hf₁
    exact ((theorem_10_4_5_of_B hB h).2.2.1 ⟨⟨hf, hfun⟩, hf₁⟩).2
  · -- `bijOn_pushforward_example` from (a)–(d)
    intro n k
    exact (theorem_10_4_5_of_B hB
      (StrongBundleEquivalenceExamples.isStrongBundleEquivalence_pullbackProj' n k)).1.2.2.2

#rt_check RoundTrip.V10_27.A_to_BnoFred [Polyfold.EpStrongBundle.theorem_10_4_5,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.eqOn_pullback,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScSmoothSection_pullback,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScPlusSection_pullback,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.exists_pushforward_local,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScSmoothSection_pushforward,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScPlusSection_pushforward,
  Polyfold.StrongBundle.isScSmoothOn_to_pullback_one,
  Polyfold.MPolyfold.isScSmoothOn_of_forall_charts,
  Polyfold.StrongBundle.IsStrongBundleIsoOn.restrict,
  Polyfold.StrongBundle.IsStrongBundleIsoOn.comp,
  Polyfold.StrongBundle.IsStrongBundleIsoOn.exists_comp,
  Polyfold.StrongBundleEquivalenceExamples.bijOn_pushforward_example]
#rt_check RoundTrip.V10_27.B_to_A [Polyfold.EpStrongBundle.theorem_10_4_5,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.eqOn_pullback,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScSmoothSection_pullback,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScPlusSection_pullback,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.exists_pushforward_local,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScSmoothSection_pushforward,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScPlusSection_pushforward,
  Polyfold.StrongBundle.isScSmoothOn_to_pullback_one,
  Polyfold.MPolyfold.isScSmoothOn_of_forall_charts,
  Polyfold.StrongBundle.IsStrongBundleIsoOn.restrict,
  Polyfold.StrongBundle.IsStrongBundleIsoOn.comp,
  Polyfold.StrongBundle.IsStrongBundleIsoOn.exists_comp,
  Polyfold.StrongBundleEquivalenceExamples.bijOn_pushforward_example]
#rt_overlap RoundTrip.V10_27.B_to_A [Polyfold.EpStrongBundle.theorem_10_4_5,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.eqOn_pullback,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScSmoothSection_pullback,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScPlusSection_pullback,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.exists_pushforward_local,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScSmoothSection_pushforward,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScPlusSection_pushforward,
  Polyfold.StrongBundle.isScSmoothOn_to_pullback_one,
  Polyfold.MPolyfold.isScSmoothOn_of_forall_charts,
  Polyfold.StrongBundle.IsStrongBundleIsoOn.restrict,
  Polyfold.StrongBundle.IsStrongBundleIsoOn.comp,
  Polyfold.StrongBundle.IsStrongBundleIsoOn.exists_comp,
  Polyfold.StrongBundleEquivalenceExamples.bijOn_pushforward_example]

end RoundTrip.V10_27
