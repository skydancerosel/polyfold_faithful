import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_13
import RoundTrip.Blind.V5_13_r2

/-!
Round trip for V5_13 (Corollary 5.8: `f^i` sc-Fredholm on `P^i`, with compact solution set),
against the second blind statement `RoundTrip.V5_13_r2.B` (`RoundTrip/Blind/V5_13_r2.lean`).
Inside this namespace `B` is the FIRST blind statement `RoundTrip.V5_13.B` (kept for the `_r1`
results at the end); the current one is always written `V5_13_r2.B`.

A = `corollary_5_2_5` ∧ `corollary_5_2_5_two` ∧ `StrongBundle.solutionSet_sectionShift` ∧
`isCompact_solutionSet_level` (universes at `0`): for an sc-Fredholm `f` (germ reading) with
compact solution set, `f¹` (and `f² = (f¹)¹`) is an sc-Fredholm section of the project's shifted
bundle `P¹ = B.shift` (`P²`) with compact solution set; the solution set of `f¹` (sc-smooth `f`)
is the part of `S_f` in `X₁`; the zeros in `X_i` are compact in `X_i` for every `i`.  No tameness.

B (r2): over a tame `X`, for an sc-Fredholm `f` (germ reading) with compact `f⁻¹(0)`, for every
`i` the iterated index raise `f^i` (`Data.iter`: `P^{i+1} = (P^i).shift`,
`f^{i+1} = (P^i).sectionShift f^i`) is an sc-Fredholm section of `P^i` and its solution set is
compact in `X^i`.

* `A ⇒ B` is proved (`A_to_B`): induction on `i`, the step being A's `corollary_5_2_5` applied to
  the bundle `P^i` (the hypothesis, not the project theorem); B's `zeroSet` is the project's
  `solutionSet` definitionally; the tameness hypothesis of B is not used.
* `B ⇒ A` fails: B assumes `PX.IsTame`, while `corollary_5_2_5`, `corollary_5_2_5_two` and
  `isCompact_solutionSet_level` hold for every M-polyfold; for tame `X`, B gives the first two
  (`B_gives_cor58_tame`).  `solutionSet_sectionShift` is an auxiliary identity for a merely
  sc-smooth `f`, which B does not mention, and `isCompact_solutionSet_level` is stated in the
  level space `X_i` with its own level topology, while B's compactness is in the iterated
  `X^i = ((X¹)¹ ⋯)` (identifying the two would be glue, not attempted, and needs tameness anyway).
-/

namespace RoundTrip.V5_13
open Polyfold

/-- The project's statement (Corollary 5.8 on the shifted bundle for `i = 1, 2`, the solution set
of `f¹`, the compact solution set on every level), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.corollary_5_2_5.{0, 0} ∧
  type_of% @Polyfold.corollary_5_2_5_two.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.solutionSet_sectionShift.{0, 0} ∧
  type_of% @Polyfold.isCompact_solutionSet_level.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.corollary_5_2_5.{0, 0}, @Polyfold.corollary_5_2_5_two.{0, 0},
    @Polyfold.StrongBundle.solutionSet_sectionShift.{0, 0},
    @Polyfold.isCompact_solutionSet_level.{0, 0}⟩

/-- One index raise, from A's `corollary_5_2_5` (B's `zeroSet` is the project's `solutionSet`). -/
theorem step (hA : A) (D : V5_13_r2.Data) (h : D.Bd.IsScFredholmSection D.f)
    (hS : IsCompact D.zeroSet) :
    D.shift.Bd.IsScFredholmSection D.shift.f ∧ IsCompact D.shift.zeroSet :=
  hA.1 h hS

/-- Every index raise, by induction. -/
theorem iter (hA : A) (D : V5_13_r2.Data) (h : D.Bd.IsScFredholmSection D.f)
    (hS : IsCompact D.zeroSet) :
    ∀ i, (D.iter i).Bd.IsScFredholmSection (D.iter i).f ∧ IsCompact (D.iter i).zeroSet
  | 0 => ⟨h, hS⟩
  | i + 1 => step hA (D.iter i) (iter hA D h hS i).1 (iter hA D h hS i).2

theorem A_to_B : A → V5_13_r2.B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f D _hT hf hS i
  exact iter hA D hf hS i

/-- B gives A's `corollary_5_2_5` and `corollary_5_2_5_two` for TAME `X` only. -/
theorem B_gives_cor58_tame (hB : V5_13_r2.B) :
    ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      (Bd : StrongBundle PX P) (f : X → Y),
      PX.IsTame → Bd.IsScFredholmSection f → IsCompact (solutionSet P f) →
        (Bd.shift.IsScFredholmSection (Bd.sectionShift f) ∧
          IsCompact (solutionSet Bd.shiftProj (Bd.sectionShift f))) ∧
        (Bd.shift.shift.IsScFredholmSection (Bd.shift.sectionShift (Bd.sectionShift f)) ∧
          IsCompact (solutionSet Bd.shift.shiftProj (Bd.shift.sectionShift (Bd.sectionShift f)))) := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f hT hf hS
  exact ⟨hB PX P Bd f hT hf hS 1, hB PX P Bd f hT hf hS 2⟩

#rt_check RoundTrip.V5_13.A_to_B [Polyfold.corollary_5_2_5, Polyfold.corollary_5_2_5_two,
  Polyfold.StrongBundle.solutionSet_sectionShift, Polyfold.isCompact_solutionSet_level]
#rt_check RoundTrip.V5_13.B_gives_cor58_tame [Polyfold.corollary_5_2_5,
  Polyfold.corollary_5_2_5_two, Polyfold.StrongBundle.solutionSet_sectionShift,
  Polyfold.isCompact_solutionSet_level]
#rt_overlap RoundTrip.V5_13.B_gives_cor58_tame [Polyfold.corollary_5_2_5, Polyfold.corollary_5_2_5_two,
  Polyfold.StrongBundle.solutionSet_sectionShift, Polyfold.isCompact_solutionSet_level]

/-! ### Against the first blind statement `RoundTrip.V5_13.B` (`RoundTrip/Blind/V5_13.lean`) -/

/-- (r1) The compactness conjunct of the first B follows from A. -/
theorem A_gives_B_compact_r1 (hA : A) :
    ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      (Bd : StrongBundle PX P) (f : X → Y),
      PX.IsTame → Bd.IsScFredholmSection f → IsCompact {x | IsZeroAt P f x} →
        ∀ i : ℕ, @IsCompact (PX.Level i) (PX.levelTopology i) {p | IsZeroAt P f p.1} := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f _hT hf hS i
  exact hA.2.2.2 hf hS i

/-- (r1) The first B gives A's last conjunct for tame `X` only. -/
theorem B_gives_A_tame_r1 (hB : B) :
    ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      (Bd : StrongBundle PX P) (f : X → Y),
      PX.IsTame → Bd.IsScFredholmSection f → IsCompact (solutionSet P f) → ∀ i : ℕ,
        IsCompact {x : PX.Level i | PX.levelVal i x ∈ solutionSet P f} := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f hT hf hS i
  exact (hB PX P Bd f hT hf hS i).2

#rt_check RoundTrip.V5_13.A_gives_B_compact_r1 [Polyfold.corollary_5_2_5,
  Polyfold.corollary_5_2_5_two, Polyfold.StrongBundle.solutionSet_sectionShift,
  Polyfold.isCompact_solutionSet_level]
#rt_check RoundTrip.V5_13.B_gives_A_tame_r1 [Polyfold.corollary_5_2_5, Polyfold.corollary_5_2_5_two,
  Polyfold.StrongBundle.solutionSet_sectionShift, Polyfold.isCompact_solutionSet_level]

end RoundTrip.V5_13
