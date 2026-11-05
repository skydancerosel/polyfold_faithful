import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_3

/-! Round trip for V5_3 (Definition 5.1: auxiliary norms).

The listed declarations are the definitions `StrongBundle.IsCompleteFiberNorm`,
`StrongBundle.IsAuxNorm` and the two lemmas `IsAuxNorm.nonneg`, `IsAuxNorm.smul`, so A is the
conjunction of the types of the two lemmas (universes at `0`).  B says that the project's
`IsAuxNorm` is the text's notion `IsAuxNormB`; it is proved outright (`B_holds`): the blind
topology `oneTopology` on `Y_{0,1}` is definitionally the project's instance on `Bd.One`
(`topology_eq`, `rfl`), the fibre conditions are the fields of `IsCompleteFiberNorm` in the same
order, and `0_x = toOne 0 = zeroOne x`. -/

namespace RoundTrip.V5_3
open Polyfold Filter Topology

/-- The project's statement: the two listed lemmas (`N ≥ 0`, `N(t v) = |t| N(v)`), universes at
`0`. -/
def A : Prop :=
  type_of% @Polyfold.StrongBundle.IsAuxNorm.nonneg.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.IsAuxNorm.smul.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.StrongBundle.IsAuxNorm.nonneg.{0, 0}, @Polyfold.StrongBundle.IsAuxNorm.smul.{0, 0}⟩

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The blind topology of `Y_{0,1}` is the project's. -/
theorem topology_eq (Bd : StrongBundle PX P) :
    (inferInstance : TopologicalSpace Bd.One) = oneTopology Bd := rfl

theorem proj_to_B (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (h : Bd.IsAuxNorm N) :
    IsAuxNormB Bd N :=
  ⟨h.continuous, fun x => ⟨(h.fiber x).eq_zero, (h.fiber x).smul, (h.fiber x).add_le,
    (h.fiber x).complete⟩, h.tendsto_zeroOne⟩

theorem B_to_proj (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (h : IsAuxNormB Bd N) :
    Bd.IsAuxNorm N :=
  ⟨h.1, fun x => ⟨(h.2.1 x).1, (h.2.1 x).2.1, (h.2.1 x).2.2.1, (h.2.1 x).2.2.2⟩, h.2.2⟩

/-- Non-negativity from the text's norm axioms on the fibre (re-proved, not the project lemma). -/
theorem nonneg_of_B (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (h : IsAuxNormB Bd N)
    (w : Bd.One) : 0 ≤ N w := by
  obtain ⟨-, hsm, hadd, -⟩ := h.2.1 (P (Bd.oneVal w))
  set v := Bd.ofOne w
  have h1 := hadd v (-v)
  have h2 := hsm (-1) v
  have h0 := hsm 0 v
  rw [neg_one_smul, abs_neg, abs_one, one_mul] at h2
  rw [zero_smul, abs_zero, zero_mul] at h0
  rw [add_neg_cancel, h2, h0] at h1
  have : N (Bd.toOne v) = N w := rfl
  linarith

end

/-- B (the project's auxiliary norms are the text's) holds outright. -/
theorem B_holds : B := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd N
  exact ⟨proj_to_B Bd N, B_to_proj Bd N⟩

/-- `A ⇒ B`: vacuous (B is proved outright). -/
theorem A_to_B : A → B := fun _ => B_holds

/-- `B ⇒ A`: B turns an auxiliary norm into the text's notion, whose fibre axioms give `N ≥ 0`
and the homogeneity. -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · intro X _ _ _ PX Y _ _ _ P _ _ Bd N hN w
    exact nonneg_of_B Bd N ((hB PX P Bd N).1 hN) w
  · intro X _ _ _ PX Y _ _ _ P _ _ Bd N hN y v t
    exact (((hB PX P Bd N).1 hN).2.1 y).2.1 t v

#rt_check RoundTrip.V5_3.A_to_B [Polyfold.StrongBundle.IsAuxNorm.nonneg,
  Polyfold.StrongBundle.IsAuxNorm.smul]
#rt_check RoundTrip.V5_3.B_to_A [Polyfold.StrongBundle.IsAuxNorm.nonneg,
  Polyfold.StrongBundle.IsAuxNorm.smul]
#rt_overlap RoundTrip.V5_3.B_to_A [Polyfold.StrongBundle.IsAuxNorm.nonneg,
  Polyfold.StrongBundle.IsAuxNorm.smul]
#rt_overlap RoundTrip.V5_3.A_to_B [Polyfold.StrongBundle.IsAuxNorm.nonneg,
  Polyfold.StrongBundle.IsAuxNorm.smul]

end RoundTrip.V5_3
