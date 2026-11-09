import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_45

/-!
Round trip for V5_45 (Theorem 5.25).  `A` is the type of `Polyfold.theorem_5_25_preprint`, universes
instantiated at `0`.

Neither `A → B` nor `B → A` is proved.

* `A → B` fails for two independent reasons, both genuine differences of the statements:
  1. **Bump functions.**  B assumes `AdmitsBumpFunctionsWeak` (`f ≢ 0`), A needs
     `AdmitsBumpFunctions` (`f(x) ≠ 0`); the project has only strong ⟹ weak.
  2. **The neighbourhood `U`.**  B reads "an associated open neighbourhood `U`" universally: for
     *every* open `U ⊇ S_f` with `S_{f+s}` compact for all `s ∈ Γ^{+,1}_U(P)` there is a good
     `s ∈ Γ^{+,1}_U(P)`.  A only gives *some* such `U` (the one its proof builds from properness)
     with a good `s` supported in it; nothing in A controls `supp(s)` relative to a prescribed `U`.
  With both removed, i.e. for `BExStrong` (strong bumps, `∃ U`), the implication is proved:
  `A_to_BExStrong` (good position is A's; the sub-M-polyfold and the corner structure come out of
  A's `SolutionSetInGeneralPosition`).  B's tame strong bundle hypothesis is not needed.
* `B → A` fails:
  1. B assumes `IsTameStrongBundle Bd` (an equivalent strong bundle atlas whose base retractions
     are tame); A assumes only `PX.IsTame` (and tame germ data of `f`), which does not give such an
     atlas (no project lemma; it is not glue).
  2. A's conclusion `SolutionSetInGeneralPosition (f + s)` (transversality, *general* position at
     every zero, `S_{f+s}` a compact smooth submanifold in general position, tame, with
     `d_{S_{f+s}} = d_X`) is much more than B's good position plus corner structure.
  (B's other hypothesis, a `U` with the compactness property, would be available from properness,
  e.g. through `theorem_5_2_2_preprint`/`remark_5_3_4`; it is not the obstruction.)
-/

/-! **Refresh 2026-11-02** (HEAD after the germ reading of Definition 3.11 and the notions built
on it).
theorem_5_25_preprint and B now both use the germ-reading IsScFredholmSectionTame / IsGoodPositionGermTame.
The obstacles (weak bump functions and B's 'every U' for A ⇒ B; B's tame strong bundle atlas and
A's richer conclusion for B ⇒ A) are unrelated to the germ switch; A ⇒ BExStrong still checks.
Result unchanged.
-/

namespace RoundTrip.V5_45
open Polyfold

/-- The project's statement, universes `0`. -/
def A : Prop := type_of% @Polyfold.theorem_5_25_preprint.{0, 0}

theorem A_holds : A := @Polyfold.theorem_5_25_preprint.{0, 0}

/-- B with the strong reading of bump functions and an existential `U` (not the item; it isolates
the two differences). -/
def BExStrong : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (N : Bd.One → ℝ),
    IsTameStrongBundle Bd → PX.AdmitsBumpFunctions →
    Bd.IsScFredholmSectionTame f → Bd.IsProper f → Bd.IsAuxNorm N →
      ∃ U : Set X, IsOpen U ∧ solSet P f ⊆ U ∧
        (∀ s ∈ Bd.allowableSections N U, IsCompact (solSet P (sectionAdd P f s))) ∧
        ∃ s ∈ Bd.allowableSections N U,
          (∀ x ∈ solSet P (sectionAdd P f s), Bd.IsGoodPositionGermTame (sectionAdd P f s) x) ∧
          ∃ (hS : PX.IsSubMPolyfold (solSet P (sectionAdd P f s)))
            (_ : ParacompactSpace (solSet P (sectionAdd P f s))),
            (PX.subPolyfold hS).HasCornerStructure

theorem A_to_BExStrong : A → BExStrong := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f N hT hbump hf hP hN
  obtain ⟨U, hUo, hSU, hcpt, s, hs, hgood, hgp⟩ := hA hT.1 hbump hf hP hN
  obtain ⟨-, -, -, hsm, -, hcorner, -, -⟩ := hgp
  exact ⟨U, hUo, hSU, hcpt, s, hs, fun x hx => hgood x hx,
    hsm.isSubMPolyfold, PX.paracompactSpace_subtype _, hcorner⟩

#rt_check RoundTrip.V5_45.A_to_BExStrong [Polyfold.theorem_5_25_preprint]

end RoundTrip.V5_45
