import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_5

/-!
Round trip for V4_5 (Theorem 4.2, the characterization).  `A` is the conjunction of the types of
`Polyfold.MPolyfold.theorem_4_1_2` and `Polyfold.MPolyfold.theorem_4_1_2_general`, universe
instantiated at `0`.

Glue:
* `X₀ = X_∞`: B's `P.smoothSet = Set.univ` vs A's `∀ x, x ∈ P.smoothSet` (`Set.eq_univ_iff_forall`).
* `1₀¹`: A fixes one junk value `x₀ : P.Level 1`, B asks the sc-smoothness for every junk value.
  Once `X₀ = X_∞ ⊆ X₁`, `toLevelOne x₀ = toLevelOne x₀'` (`toLevelOne_indep`), so the two agree;
  when `X = ∅` there is no `x₀` at all, and `HasCornerStructure` holds trivially.
* Tame centred charts: the same conjuncts in a different order.
* B ⇒ `theorem_4_1_2_general` (no tameness hypothesis): both (i) (`HasCornerStructure.isTame`) and
  (ii) (its tame charts cover `X`, `isTame_of_forall_exists_chart`) imply tameness, so B's
  tameness hypothesis can be discharged on either side of the equivalence.
-/

namespace RoundTrip.V4_5
open Polyfold

/-- The project's statement: Theorem 4.2 (text's form) and its general form, universe `0`. -/
def A : Prop :=
  type_of% @Polyfold.MPolyfold.theorem_4_1_2.{0} ∧ type_of% @Polyfold.MPolyfold.theorem_4_1_2_general.{0}

theorem A_holds : A := ⟨@Polyfold.MPolyfold.theorem_4_1_2.{0}, @Polyfold.MPolyfold.theorem_4_1_2_general.{0}⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

theorem toLevelOne_indep (hsm : ∀ x, x ∈ P.smoothSet) (x₀ x₁ : P.Level 1) :
    P.toLevelOne x₀ = P.toLevelOne x₁ := by
  funext x
  have hx : x ∈ P.levelSet 1 := Set.mem_iInter.1 (hsm x) 1
  simp only [MPolyfold.toLevelOne, dif_pos hx]

/-- A's centred tame chart condition. -/
def chartA (P : MPolyfold X) : Prop :=
  ∀ x, ∃ ψ : MChart X, P.IsChart ψ ∧ x ∈ ψ.source ∧ ψ x = 0 ∧
    IsTameRetract ψ.model.E ψ.model.C ψ.model.O ∧
    ∃ N : Submodule ℝ (ψ.model.E 0), (N : Set (ψ.model.E 0)) =
      tangentSpace ψ.model.E ψ.model.C ψ.model.O 0 ∧ FiniteDimensional ℝ N ∧
      IsInGoodPosition ψ.model.E ψ.model.C N

/-- B's centred tame chart condition. -/
def chartB (P : MPolyfold X) : Prop :=
  ∀ x : X, ∃ ψ : MChart X,
    P.IsChart ψ ∧ IsTameRetract ψ.model.E ψ.model.C ψ.model.O ∧
    x ∈ ψ.source ∧ ψ.toPartialEquiv x = 0 ∧
    ∃ N : Submodule ℝ (ψ.model.E.lvl 0),
      (N : Set (ψ.model.E.lvl 0)) = tangentSpace ψ.model.E ψ.model.C ψ.model.O 0 ∧
      FiniteDimensional ℝ N ∧ IsInGoodPosition ψ.model.E ψ.model.C N

theorem chartA_iff_chartB : chartA P ↔ chartB P := by
  constructor
  · intro h x
    obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := h x
    exact ⟨ψ, h1, h4, h2, h3, h5⟩
  · intro h x
    obtain ⟨ψ, h1, h4, h2, h3, h5⟩ := h x
    exact ⟨ψ, h1, h2, h3, h4, h5⟩

theorem isTame_of_chartA (h : chartA P) : P.IsTame :=
  MPolyfold.isTame_of_forall_exists_chart P fun x => by
    obtain ⟨ψ, h1, h2, -, h4, -⟩ := h x
    exact ⟨ψ, h1, h2, h4⟩

/-- B's (ii) with "for every junk value" ↔ A's (ii) with a given junk value. -/
theorem iiB_iff_iiA (x₀ : P.Level 1) :
    (P.smoothSet = Set.univ ∧ (∀ x₀ : P.Level 1, P.IsScSmoothMap P.shift (P.toLevelOne x₀)) ∧
        chartB P) ↔
      ((∀ x, x ∈ P.smoothSet) ∧ P.IsScSmoothMap P.shift (P.toLevelOne x₀) ∧ chartA P) := by
  rw [Set.eq_univ_iff_forall, chartA_iff_chartB]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2 x₀, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun x₁ => toLevelOne_indep h1 x₀ x₁ ▸ h2, h3⟩

end Glue

theorem A_to_B : A → B := by
  rintro ⟨hA, -⟩ X _ _ _ P hP
  by_cases hX : Nonempty X
  · obtain ⟨x⟩ := hX
    constructor
    · intro hc
      -- a point of `X₁`: a corner chart around `x` is modelled on an sc⁺-retract (Lemma 4.7 (i))
      obtain ⟨χ, hχ, hx, hcc⟩ := MPolyfold.hasCornerStructure_iff.1 hc x
      obtain ⟨R, hR, hRp⟩ := hcc.isScPlusRetract
      have hxs : x ∈ P.smoothSet := (MPolyfold.mem_smoothSet_iff hχ hx).2
        (lemma_4_1_7_i hRp (hR ▸ χ.mapsTo_model x hx))
      exact (iiB_iff_iiA _).2
        ((hA hP (P.levelMk 1 x (MPolyfold.smoothSet_subset_levelSet 1 hxs))).1 hc)
    · intro h
      have hsm : ∀ y, y ∈ P.smoothSet := Set.eq_univ_iff_forall.1 h.1
      exact (hA hP (P.levelMk 1 x (Set.mem_iInter.1 (hsm x) 1))).2
        ((iiB_iff_iiA _).1 h)
  · have hc : P.HasCornerStructure :=
      MPolyfold.hasCornerStructure_iff.2 fun x => (hX ⟨x⟩).elim
    refine ⟨fun _ => ⟨Set.eq_univ_iff_forall.2 fun x => (hX ⟨x⟩).elim,
      fun x₀ => (hX ⟨P.levelVal 1 x₀⟩).elim, fun x => (hX ⟨x⟩).elim⟩, fun _ => hc⟩

theorem B_to_A : B → A := by
  intro hB
  have gen : type_of% @Polyfold.MPolyfold.theorem_4_1_2_general.{0} := by
    intro X _ _ _ P x₀
    constructor
    · intro hc
      exact (iiB_iff_iiA x₀).1 ((hB X P hc.isTame).1 hc)
    · intro h
      have hP : P.IsTame := isTame_of_chartA h.2.2
      exact (hB X P hP).2 ((iiB_iff_iiA x₀).2 h)
  exact ⟨fun _ x₀ => gen x₀, gen⟩

#rt_check RoundTrip.V4_5.A_to_B [Polyfold.MPolyfold.theorem_4_1_2, Polyfold.MPolyfold.theorem_4_1_2_general]
#rt_check RoundTrip.V4_5.B_to_A [Polyfold.MPolyfold.theorem_4_1_2, Polyfold.MPolyfold.theorem_4_1_2_general]
#rt_overlap RoundTrip.V4_5.B_to_A [Polyfold.MPolyfold.theorem_4_1_2, Polyfold.MPolyfold.theorem_4_1_2_general]

end RoundTrip.V4_5
