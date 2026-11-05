import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_41

/-! **Refresh 2026-11-02** (HEAD after the germ reading of Definition 3.11 and the notions built
on it).
The sc-Fredholm clauses of the project's IsGenCompactHomotopy (f and every f|X_τ,
IsScFredholmSectionTame) and of B's notion now both denote the germ reading, so they still agree
literally; the only difference remains B's tame strong bundle atlas, which the project cannot
construct from PX.IsTame. Result unchanged.
-/

namespace RoundTrip.V5_41
open Polyfold

/-- The project's statement: the only theorem among the decls is
`IsGenCompactHomotopy.isCompact_solutionSet_restrict` (the restricted problems have compact
solution sets), universes at `0`; `restrictSection` and `IsGenCompactHomotopy` are vocabulary. -/
def A : Prop :=
  type_of% @Polyfold.StrongBundle.IsGenCompactHomotopy.isCompact_solutionSet_restrict.{0, 0}

theorem A_holds : A :=
  @Polyfold.StrongBundle.IsGenCompactHomotopy.isCompact_solutionSet_restrict.{0, 0}

set_option linter.unusedSectionVars false

section Glue
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- B's solution set is the project's. -/
theorem solSet_eq (f : X → Y) : solSet P f = solutionSet P f := rfl

/-- **The ⇐ half of B** (B's notion implies the project's): B's tame strong bundle contains
`PX.IsTame`; everything else is literally the same (the paracompactness instances, the
sc-smoothness of the inclusion and `IsSection P f` are propositions). -/
theorem project_of_B (Bd : StrongBundle PX P) (f : X → Y) (t : X → ℝ)
    (h : IsGenCompactHomotopyB Bd f t) : Bd.IsGenCompactHomotopy f t := by
  obtain ⟨⟨hX, -⟩, hf, hcpt, ht, hrange, hfib⟩ := h
  refine ⟨hX, hf, hcpt, ht, hrange, fun τ hτ => ?_⟩
  obtain ⟨hsub, _, htame, hι, _, hfs, hF⟩ := hfib τ hτ
  exact ⟨hsub, htame, hF⟩

/-- **The ⇒ half of B, under B's extra hypothesis**: with a tame strong bundle, the project's
notion gives B's. -/
theorem B_of_project (Bd : StrongBundle PX P) (f : X → Y) (t : X → ℝ)
    (h : Bd.IsGenCompactHomotopy f t) (hT : IsTameStrongBundle Bd) :
    IsGenCompactHomotopyB Bd f t := by
  refine ⟨hT, h.isScFredholm, h.isCompact, h.isScSmooth_t, h.range_t, fun τ hτ => ?_⟩
  obtain ⟨hsub, htame, hF⟩ := h.fibre τ hτ
  have := PX.paracompactSpace_subtype (t ⁻¹' {τ})
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : t ⁻¹' {τ} → X))
    (MPolyfold.subPolyfold hsub) Bd
  exact ⟨hsub, inferInstance, htame, MPolyfold.subPolyfold_inclusion_isScSmooth hsub,
    inferInstance, h.isScFredholm.isScSmooth.1, hF⟩

/-- So B is equivalent to: "the project's generalized compact homotopies live on tame strong
bundles" (`B ↔ ∀ …, IsGenCompactHomotopy f t → IsTameStrongBundle Bd`). -/
theorem B_iff_tame :
    B ↔ ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      (Bd : StrongBundle PX P) (f : X → Y) (t : X → ℝ),
      Bd.IsGenCompactHomotopy f t → IsTameStrongBundle Bd := by
  constructor
  · intro hB X _ _ _ PX Y _ _ _ P _ _ Bd f t h
    exact ((hB PX P Bd f t).1 h).1
  · intro hT X _ _ _ PX Y _ _ _ P _ _ Bd f t
    exact ⟨fun h => B_of_project Bd f t h (hT PX P Bd f t h), project_of_B Bd f t⟩

end Glue

/-- `B ⇒ A`: vacuous; the compactness of the restricted solution sets is re-proved directly (the
trace of the compact `S_f` on the closed fibre `t⁻¹(τ)`); B adds nothing, since its notion has
the same compactness clause. -/
theorem B_to_A : B → A := by
  intro _ X _ _ _ PX Y _ _ _ P _ _ Bd f t h τ
  have hcont : Continuous t := continuousOn_univ.1 h.isScSmooth_t.continuousOn
  have hcl : IsClosed (t ⁻¹' {τ}) := isClosed_singleton.preimage hcont
  have heq : solutionSet (pullbackProj P (Subtype.val : t ⁻¹' {τ} → X))
      (restrictSection P (t ⁻¹' {τ}) f h.isScFredholm.isScSmooth.1) =
      Subtype.val ⁻¹' solutionSet P f := by
    ext a
    exact isZeroAt_restrictSection_iff h.isScFredholm.isScSmooth.1 a
  rw [heq]
  exact hcl.isClosedEmbedding_subtypeVal.isCompact_preimage h.isCompact

/-! `A ⇒ B` is not proved.  A says nothing about the definition, so B has to be proved outright,
and by `B_iff_tame` B amounts to: every strong bundle carrying a (project) generalized compact
homotopy is a tame strong bundle in B's sense (an EQUIVALENT strong bundle atlas whose base
retractions are all tame).  The project's Definition 5.20 only asks `PX.IsTame` (tame retracts,
not tame bundle retractions) plus tame germ data at the smooth points for `f` and the `f|X_τ`.
Mathematically the missing step is true (over a tame chart `ψ` of `X` one can rebuild every strong
bundle chart `Φ` as `R'(u, h) = (r'(u), Γ(σ(r'(u)), h))`, `r'` a tame retraction onto the
overlap and `σ` the transition to `Φ`'s base chart, and the new charts are compatible with the
atlas), but the project has no such construction: it would need new `StrongBundleChart`s, their
compatibility and an atlas equivalence (substantial glue, not attempted). -/

#rt_check RoundTrip.V5_41.B_to_A
  [Polyfold.StrongBundle.IsGenCompactHomotopy.isCompact_solutionSet_restrict]
#rt_overlap RoundTrip.V5_41.B_to_A
  [Polyfold.StrongBundle.IsGenCompactHomotopy.isCompact_solutionSet_restrict]

end RoundTrip.V5_41
