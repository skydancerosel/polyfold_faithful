import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_24

/-! Round trip for V10_24 (2021 Proposition 10.4.2 = 2017 Proposition 10.7: pull-backs along
strong bundle equivalences with `|Φ| = |Ψ|` agree).

The item lists two theorems; `A` is the conjunction of their types, universes at `0`:
`proposition_10_4_2` (for sc-smooth section functors `f' ∈ Γ(P', μ')`) and its helper
`IsStrongBundleEquivalence.pullback_eq_of_orbitMap_eq` (the same for every *functorial section*
`f'`, sc-smooth or not).

`B` (blind): for strong bundle equivalences `Φ`, `Ψ` in the text's sense (`IsSBEquivB`, see
V10_22) with `Φ(w) ≅ Ψ(w)` for all `w` (`SameOrbitMapB`), the blind pull-backs `pullB` of every
sc-smooth section functor agree.

Glue (both directions): `IsSBEquivB ↔ IsStrongBundleEquivalence` (`toB`, `ofB`, as in V10_22;
here the project's `isLocalScDiffeo_one` is not banned); `SameOrbitMapB ↔ Φ.orbitMap = Ψ.orbitMap`
(`orbitMap_eq_of_forall_exists`, `exists_μ_eq_of_orbitMap_eq`); the blind sc-smooth section
functors are `E'.sectionFunctors`; and `pullB ϕ Φ f' = h.pullback f'` for sections (`pullback_eq`:
both pick the unique `w ∈ W_x` with `Φ(w) = f'(ϕ(x))`).

* `A_to_B`: from `proposition_10_4_2` and the glue.
* `B_to_A1`: `proposition_10_4_2` from `B` and the glue (`#rt_check` OK).
* `B ⇒ A` fails on the second conjunct for a genuine reason: `pullback_eq_of_orbitMap_eq` is
  stated for all functorial sections, also non-sc-smooth ones, about which `B` says nothing (a
  functorial section through a given vector of `W'_{ϕ(x)}` need not be approximable by an
  sc-smooth one).  It is the project's (more general) helper; the text's statement is the first
  conjunct. -/

set_option maxSynthPendingDepth 3

namespace RoundTrip.V10_24
open Polyfold Set Function

/-! The project's statement (universes at `0`). -/
def A1 : Prop := type_of% @Polyfold.EpStrongBundle.proposition_10_4_2.{0}
def A2 : Prop :=
  type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_eq_of_orbitMap_eq.{0}

/-- The project's statement. -/
def A : Prop := A1 ∧ A2

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.proposition_10_4_2.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_eq_of_orbitMap_eq.{0}⟩

section Glue
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
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {ϕ : EpFunctor X X'}
  {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}

/-- The project's strong bundle equivalences are the blind ones (V10_22, `→`). -/
theorem toB (h : E.IsStrongBundleEquivalence E' ϕ Φ) : IsSBEquivB E E' ϕ Φ := by
  refine ⟨h.isStrongBundleFunctor, h.isEquivalence_base, h.isEquivalence,
    ⟨h.isStrongBundleFunctor.isStrongBundleMap_obj.mapsTo_oneSet, h.isLocalScDiffeo_one, ?_, ?_,
      ?_⟩, h.isLocalStrongBundleIso_obj, h.isLocalStrongBundleIso_mor⟩
  · intro m m' _ hs ht he
    exact h.isEquivalence.mor_injective hs ht he
  · intro w₁ w₂ _ _ m' hs ht
    exact h.isEquivalence.exists_mor_eq hs ht
  · exact ⟨h.isHomeomorph_oneOrbitMap.homeomorph, fun a => rfl⟩

/-- The blind strong bundle equivalences are the project's (V10_22, `←`). -/
theorem ofB (h : IsSBEquivB E E' ϕ Φ) : E.IsStrongBundleEquivalence E' ϕ Φ := by
  obtain ⟨hF, hϕ, hΦ, ⟨hmap, -, -, -, e, he⟩, hobj, hmor⟩ := h
  refine ⟨hF, hϕ, hΦ, ?_, hobj, hmor⟩
  have : E.oneOrbitMap E' Φ hF.isStrongBundleMap_obj.mapsTo_oneSet = e := by
    funext q
    induction q using Quot.ind with
    | mk a => exact (he a).symm
  rw [this]
  exact e.isHomeomorph

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- The blind sc-smooth section functors are `Γ(P, μ)`. -/
theorem mem_sectionFunctors_iff (f : Obj → W) :
    IsScSmoothSectionFunctorB E f ↔ f ∈ E.sectionFunctors := by
  constructor
  · rintro ⟨hs, hsm, hfun⟩
    exact ⟨⟨hs, hsm⟩, fun φ => hfun φ _ _ rfl rfl (hs (X.src φ))⟩
  · rintro ⟨⟨hs, hsm⟩, hfun⟩
    refine ⟨hs, hsm, fun φ x y hx hy h => ?_⟩
    subst hx hy
    exact hfun φ

/-- The blind pull-back is the project's on sections. -/
theorem pullB_eq (h : E.IsStrongBundleEquivalence E' ϕ Φ) {f' : Obj' → W'}
    (hf' : IsSection P' f') : pullB ϕ Φ f' = h.pullback f' := by
  funext x
  have hex : ∃ w : W, P w = x ∧ Φ.obj w = f' (ϕ.obj x) :=
    ⟨h.pullback f' x, h.P_pullback f' x, h.obj_pullback hf' x⟩
  unfold pullB
  rw [dif_pos hex]
  exact (h.pullback_eq hf' hex.choose_spec.1 hex.choose_spec.2).symm

/-- `SameOrbitMapB` is `|Φ| = |Ψ|`. -/
theorem sameOrbitMap_iff {Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} :
    SameOrbitMapB Φ Ψ ↔ Φ.orbitMap = Ψ.orbitMap := by
  constructor
  · intro h
    exact EpStrongBundle.orbitMap_eq_of_forall_exists fun w => h w
  · intro h w
    exact EpStrongBundle.exists_μ_eq_of_orbitMap_eq h w

end Glue

theorem A_to_B : A → B := by
  rintro ⟨h42, -⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
    E E' ϕ ψ Φ Ψ hΦ hΨ hΦΨ f' hf'
  have hΦ' := ofB hΦ
  have hΨ' := ofB hΨ
  rw [pullB_eq hΦ' hf'.1, pullB_eq hΨ' hf'.1]
  exact h42 hΦ' hΨ' (sameOrbitMap_iff.1 hΦΨ) ((mem_sectionFunctors_iff f').1 hf')

/-- `B` gives the text's statement, the first conjunct of `A`. -/
theorem B_to_A1 : B → A1 := by
  intro hB Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
    E E' ϕ ψ Φ Ψ hΦ hΨ hΦΨ f' hf'
  have hf'B := (mem_sectionFunctors_iff f').2 hf'
  rw [← pullB_eq hΦ hf'B.1, ← pullB_eq hΨ hf'B.1]
  exact hB Obj Mor X W P B Obj' Mor' X' W' P' B' E E' ϕ ψ Φ Ψ (toB hΦ) (toB hΨ)
    (sameOrbitMap_iff.2 hΦΨ) f' hf'B

#rt_check RoundTrip.V10_24.A_to_B [Polyfold.EpStrongBundle.proposition_10_4_2,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_eq_of_orbitMap_eq]
#rt_check RoundTrip.V10_24.B_to_A1 [Polyfold.EpStrongBundle.proposition_10_4_2,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_eq_of_orbitMap_eq]
#rt_overlap RoundTrip.V10_24.B_to_A1 [Polyfold.EpStrongBundle.proposition_10_4_2,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_eq_of_orbitMap_eq]

end RoundTrip.V10_24
