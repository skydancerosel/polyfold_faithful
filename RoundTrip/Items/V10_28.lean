import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_28

/-! Round trip for V10_28 (2021 Definition 10.4.8 = 2017 Definition 10.11: natural
transformations of strong bundle functors).

The item lists the definitions `StrongBundleNatTrans`, `StrongBundleNatEquiv`,
`StrongBundleNatTrans.refl` (vocabulary) and one theorem, the witness
`StrongBundleEquivalenceExamples.strongBundleNatEquiv_example` (`Φ ≃ Φ` for the concrete
strong bundle equivalence `(-id)*W' → W'`); `A` is its type (no universe parameters).

`B` characterizes the project's `StrongBundleNatTrans`: (a) the data `(T, τ)` of every one satisfy
the text's `IsSBNatTransB` (`T(w) : Φ(w) → Ψ(w)` in `(W', 𝐖')`, naturality, `T(w)` over
`τ(P(w))`), (b) every such pair is the data of one.

* `A_to_B`: vacuous; `B` is proved outright (`B_holds`): the structure fields are exactly the
  three clauses of `IsSBNatTransB` (`app_P` is the third, reversed), so the definitions agree.
* `B_to_A`: from `B` (b) with `τ = 1_ϕ` and `T(w) = 1_{Φ(w)}` (`natEquiv_refl_of_B`), applied to
  the example; the clauses for this pair are checked directly (not with `refl`). -/

namespace RoundTrip.V10_28
open Polyfold Set Function

/-- The project's statement (the witness; no universe parameters). -/
def A : Prop := type_of% @Polyfold.StrongBundleEquivalenceExamples.strongBundleNatEquiv_example

theorem A_holds : A := @Polyfold.StrongBundleEquivalenceExamples.strongBundleNatEquiv_example

/-- **The definitions agree**: `B` holds outright. -/
theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
    E E' ϕ ψ Φ Ψ _ _
  refine ⟨fun N => ⟨fun w => ⟨N.src_T w, N.tgt_T w⟩, N.naturality, fun w => (N.app_P w).symm⟩,
    fun τ T hT => ?_⟩
  exact ⟨⟨T, fun w => (hT.1 w).1, fun w => (hT.1 w).2, hT.2.1, τ, fun w => (hT.2.2 w).symm⟩,
    rfl, rfl⟩

/-- Vacuous for the audit: `B` is proved outright. -/
theorem A_to_B : A → B := fun _ => B_holds

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
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'}

/-- From `B` (b): every strong bundle functor is naturally equivalent to itself, with
`T(w) = 1_{Φ(w)}` over `τ = 1_ϕ`. -/
theorem natEquiv_refl_of_B (hB : RoundTrip.V10_28.B) {ϕ : EpFunctor X X'}
    {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (hΦ : E.IsStrongBundleFunctor E' ϕ Φ) :
    E.StrongBundleNatEquiv E' ϕ ϕ Φ Φ := by
  obtain ⟨-, hb⟩ := hB Obj Mor X W P B Obj' Mor' X' W' P' B' E E' ϕ ϕ Φ Φ hΦ hΦ
  obtain ⟨N, -, -⟩ := hb (EpNatTrans.refl ϕ) (fun w => E'.toEpGroupoid.unit (Φ.obj w))
    ⟨fun w => ⟨E'.toEpGroupoid.src_unit _, E'.toEpGroupoid.tgt_unit _⟩, fun q => by
      beta_reduce
      rw [← Φ.tgt_mor, ← Φ.src_mor, E'.toEpGroupoid.unit_comp, E'.toEpGroupoid.comp_unit],
      fun w => by rw [EpNatTrans.refl_app, ← hΦ.isStrongBundleMap_obj.covers]; rfl⟩
  exact ⟨N⟩

end

theorem B_to_A : B → A := fun hB n k =>
  natEquiv_refl_of_B hB
    (StrongBundleEquivalenceExamples.isMap_pullbackProj' n k).isStrongBundleFunctor_liftFunctor

#rt_check RoundTrip.V10_28.A_to_B
  [Polyfold.StrongBundleEquivalenceExamples.strongBundleNatEquiv_example]
#rt_check RoundTrip.V10_28.B_to_A
  [Polyfold.StrongBundleEquivalenceExamples.strongBundleNatEquiv_example]
#rt_overlap RoundTrip.V10_28.B_to_A
  [Polyfold.StrongBundleEquivalenceExamples.strongBundleNatEquiv_example]

end RoundTrip.V10_28
