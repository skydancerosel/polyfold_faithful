import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_30

/-!
Round trip for V5_30 (Theorem 5.13, the text's dense form).  Refreshed 2026-11-02: the comparison
row now also cites `StrongBundle.allowableDist_le_iff` (the project's pointwise bound
`N(s(x) − s'(x)) ≤ ε` is `ρ(s, s') ≤ ε`), and `theorem_5_3_5_preprint` now assumes the germ reading of
Definition 3.11 with tame germ data (`IsScFredholmSectionTame`, changed in place); B's
`IsScFredholmSection` is the germ reading too.

A = `theorem_5_3_5_preprint` ∧ `StrongBundle.allowableDist_le_iff` (universes at `0`).

* `B ⇒ A` (proved): `B_gives_theorem_5_13` (unchanged argument, see its docstring) and
  `allowableDist_le_iff'` (`allowableDist_le_iff` re-proved outright from the bound
  `sectionDistAt ≤ allowableDist`; B is not needed for this elementary property of a supremum).
* `A ⇒ B` (not proved): see the comment at the end.
-/

namespace RoundTrip.V5_30
open Polyfold

/-- The project's statement (Theorem 5.13, dense form, and `ρ ≤ ε` in pointwise form), universes
instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_5_3_5_preprint.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.allowableDist_le_iff.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_5_3_5_preprint.{0, 0}, @Polyfold.StrongBundle.allowableDist_le_iff.{0, 0}⟩

/-- The distance `N(s(x) − s'(x))` is symmetric (`N(−v) = N(v)` on each fibre). -/
theorem sectionDistAt_symm {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {Bd : StrongBundle PX P} {N : Bd.One → ℝ} (hN : Bd.IsAuxNorm N) {s s' : X → Y}
    (hs : Bd.IsScPlusSection s) (hs' : Bd.IsScPlusSection s') (x : X) :
    Bd.sectionDistAt N hs hs' x = Bd.sectionDistAt N hs' hs x := by
  unfold StrongBundle.sectionDistAt
  rw [← neg_sub, ← neg_one_smul ℝ (_ - _), (hN.fiber x).smul, abs_neg, abs_one, one_mul]

/-- `B ⇒ A`: A's hypotheses give B's (`AdmitsBumpFunctions ⇒ AdmitsBumpFunctionsWeak`, tame germ
data ⇒ germ data); B's dense set `O` gives, for every allowable `s'` and `ε > 0`, an `s ∈ O` within
`ε`; `f + s` is transversal and `S_{f+s}` compact by B, and the manifold structure with the index
of A (`SolutionSetIsManifold`) follows from transversality by Theorem 3.56
(`theorem_3_6_10_of_surjective`, applied to `f + s`, sc-Fredholm with tame germ data by
`theorem_3_1_18_tame`). -/
theorem B_gives_theorem_5_13 : B → type_of% @Polyfold.theorem_5_3_5_preprint.{0, 0} := by
  intro hB X _ _ _ PX Y _ _ _ P _ _ Bd hX hbump f hf hS N hN
  obtain ⟨U, hUo, hSU, hcpt, O, ⟨hOsub, hdense⟩, hO⟩ :=
    hB PX P Bd f N hX hbump.weak hf.toIsScFredholmSection hS hN
  refine ⟨U, hUo, hSU, hcpt, fun s' hs' hs'alw ε hε => ?_⟩
  obtain ⟨s, hsO, hs₁, hs₂, δ', hδ', hle⟩ := hdense s' hs'alw ε hε
  obtain ⟨htr, hcomp, -⟩ := hO s hsO
  refine ⟨s, hs₂, hOsub hsO, fun x => ?_, htr, hcomp, fun hne => ?_⟩
  · rw [sectionDistAt_symm hN hs₂ hs' x]
    exact (hle x).trans hδ'.le
  · exact theorem_3_6_10_of_surjective hX (theorem_3_1_18_tame hf hs₂) htr hne

/-- A's second conjunct, outright (elementary: `ρ` is a supremum of the pointwise distances). -/
theorem allowableDist_le_iff' : type_of% @Polyfold.StrongBundle.allowableDist_le_iff.{0, 0} := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd N U hN s s' ε hε
  exact ⟨fun h x => (StrongBundle.sectionDistAt_le_allowableDist hN s s' x).trans h,
    fun h => Real.iSup_le h hε⟩

/-- **`B ⇒ A`.** -/
theorem B_to_A : B → A := fun hB => ⟨B_gives_theorem_5_13 hB, allowableDist_le_iff'⟩

/-! `A ⇒ B` is not proved: B's hypotheses do not give A's.
* B assumes only `AdmitsBumpFunctionsWeak` (a bump function "not identically zero" with support in
  `U`), A needs `AdmitsBumpFunctions` (`f(x) ≠ 0`); the project has only the implication
  strong ⇒ weak (`AdmitsBumpFunctions.weak`).
  The project leaves "weak ⇒ pointwise" open at non-smooth points (`BumpWeakPointwise.lean`; it
  proves it only at smooth points of an sc-Banach space, `hasBumpAt_of_mem_smooth`).
* B assumes `IsScFredholmSection f`, A needs `IsScFredholmSectionTame f` (germ data, now in the
  germ reading on both sides, in tame strong bundle charts).  With `∂X = ∅` this is plausibly
  obtainable by shrinking charts to the interior of their quadrants, but the project has no such
  lemma.
* On the conclusion side B wants `HasCornerStructure` (corner charts with the constant
  sc-structure) of the induced structure on `S_{f+s}`, also when `S_{f+s} = ∅`; A gives
  `IsManifoldWithCornersLoc` (charts on relatively open subsets of quadrants in finite-dimensional
  sc-spaces), tameness and the index, and only for non-empty `S_{f+s}`. -/

#rt_check RoundTrip.V5_30.B_to_A [Polyfold.theorem_5_3_5_preprint, Polyfold.StrongBundle.allowableDist_le_iff]
#rt_overlap RoundTrip.V5_30.B_to_A [Polyfold.theorem_5_3_5_preprint, Polyfold.StrongBundle.allowableDist_le_iff]

end RoundTrip.V5_30
