import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_39

/-! **Refresh 2026-11-02** (HEAD after the germ reading of Definition 3.11 and the notions built
on it).
theorem_5_3_10_dense and B now both use the germ-reading IsScFredholmSectionTame. The obstacles
(weak vs pointwise bump functions; B's tame strong bundle atlas) are untouched by the germ switch;
A ⇒ BStrongBump still checks. Result unchanged.
-/

namespace RoundTrip.V5_39
open Polyfold

/-- The project's statement (Theorem 5.18, dense form), universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.theorem_5_3_10_dense.{0, 0}

theorem A_holds : A := @Polyfold.theorem_5_3_10_dense.{0, 0}

/-- The distance `N(s(x) − s'(x))` is symmetric (`N(−v) = N(v)` on each fibre). -/
theorem sectionDistAt_symm {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {Bd : StrongBundle PX P} {N : Bd.One → ℝ} (hN : Bd.IsAuxNorm N) {s s' : X → Y}
    (hs : Bd.IsScPlusSection s) (hs' : Bd.IsScPlusSection s') (x : X) :
    Bd.sectionDistAt N hs hs' x = Bd.sectionDistAt N hs' hs x := by
  unfold StrongBundle.sectionDistAt
  rw [← neg_sub, ← neg_one_smul ℝ (_ - _), (hN.fiber x).smul, abs_neg, abs_one, one_mul]

/-- B with the bump-function hypothesis read as in the project (`AdmitsBumpFunctions`,
`f(x) ≠ 0`) instead of B's literal reading (`AdmitsBumpFunctionsWeak`, `f ≢ 0`); everything else
as in B. -/
def BStrongBump : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (N : Bd.One → ℝ),
    IsTameStrongBundle Bd → PX.AdmitsBumpFunctions →
    Bd.IsScFredholmSectionTame f → IsCompact (solSet P f) → Bd.IsAuxNorm N →
      ∃ U : Set X, IsOpen U ∧ solSet P f ⊆ U ∧
        (∀ s ∈ Bd.allowableSections N U, IsCompact (solSet P (sectionAdd P f s))) ∧
        ∃ O : Set (X → Y), IsRhoDense Bd N (Bd.allowableSections N U) O ∧
          ∀ s ∈ O, ∀ x ∈ solSet P (sectionAdd P f s),
            Bd.IsGeneralPositionGerm (sectionAdd P f s) x

/-- B implies `BStrongBump` (its hypothesis is stronger). -/
theorem B_to_BStrongBump : B → BStrongBump := by
  intro hB X _ _ _ PX Y _ _ _ P _ _ Bd f N hT hbump
  exact hB PX P Bd f N hT hbump.weak

/-- `A ⇒ BStrongBump`: the only obstruction to `A ⇒ B` is the reading of "bump functions".
`O` := the allowable `s` with `f + s` in general position (`SolutionSetInGeneralPosition`); A's
density with `ε = δ/2` and the symmetry of `N` give B's `ρ`-density. -/
theorem A_to_BStrongBump : A → BStrongBump := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f N hT hbump hf hS hN
  obtain ⟨U, hUo, hSU, hcpt, hdense⟩ := hA hT.1 hbump hf hS hN
  refine ⟨U, hUo, hSU, hcpt,
    {s | s ∈ Bd.allowableSections N U ∧ Bd.SolutionSetInGeneralPosition (sectionAdd P f s)},
    ⟨fun s hs => hs.1, fun s hs δ hδ => ?_⟩, fun s hs x hx => hs.2.2.1 x hx⟩
  obtain ⟨s', hs', hs'alw, hdist, hgp⟩ := hdense s hs.1 hs (δ / 2) (half_pos hδ)
  refine ⟨s', ⟨hs'alw, hgp⟩, hs.1, hs', δ / 2, half_lt_self hδ, fun x => ?_⟩
  rw [sectionDistAt_symm hN hs.1 hs' x]
  exact hdist x

/-! Neither `A ⇒ B` nor `B ⇒ A` is proved.
* `A ⇒ B`: B assumes only `AdmitsBumpFunctionsWeak` ("not identically zero"), A needs
  `AdmitsBumpFunctions` (`f(x) ≠ 0`); the project has only strong ⇒ weak.  With the strong reading
  the implication holds (`A_to_BStrongBump`).
* `B ⇒ A`: B assumes `IsTameStrongBundle Bd` (an equivalent strong bundle atlas all of whose
  charts have tame base retractions), A only `PX.IsTame` and tame germ data at smooth points; the
  tame strong bundle atlas does not follow.  Moreover B's conclusion is only general position at
  every zero, while A's `SolutionSetInGeneralPosition` also asserts transversality (implied),
  compactness (implied by B's `U`), and the smooth-submanifold / corner / `d_S = d_X` structure of
  `S_{f+s}` (would need Theorems 4.18, 4.22-type arguments of the project). -/

#rt_check RoundTrip.V5_39.A_to_BStrongBump [Polyfold.theorem_5_3_10_dense]
#rt_check RoundTrip.V5_39.B_to_BStrongBump [Polyfold.theorem_5_3_10_dense]

end RoundTrip.V5_39
