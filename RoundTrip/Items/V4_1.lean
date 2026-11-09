import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_1

/-!
Round trip for V4_1 (Definition 4.1, corner charts and corner structures).  The decls list two
definitions (`MChart.IsCornerChart`, `MPolyfold.HasCornerStructure`, vocabulary) and four
theorems, so `A` is the conjunction of the types of `MPolyfold.hasCornerStructure_iff`,
`MPolyfold.HasCornerStructure.isTame`, `MChart.IsCornerChart.isTameRetract` and
`MChart.IsCornerChart.isScPlusRetract`, universe instantiated at `0`.

Glue:
* The project's corner chart is modelled literally on `LocalModel.ofRelOpen hU` over
  `ScBanach.const V`; B's corner chart on any relatively open `U ⊆ C` of a finite-dimensional
  sc-space whose inclusions are onto.  At the level of structures they agree:
  project ⇒ B by `IsCornerChart.finiteDimensional`, `ScBanach.toBase_surjective`,
  `IsCornerChart.isRelOpenInQuadrant`; B ⇒ project by
  `MChart.exists_isCornerChart_of_finiteDimensional` (compose with the identity
  `E → const E₀`, an sc-diffeomorphism by `ScBanach.scIsoConst`).
* Atlas "equivalent to the atlas of `X`" (project) vs "pairwise compatible, covering, charts of
  `P`" (B): via the local form `hasCornerStructure_iff` (A's first conjunct, used as hypothesis in
  A ⇒ B) and, in B ⇒ A, via B itself and `MPolyfold.IsChart.compatible`.
* A's chart-level conjuncts `IsCornerChart.isTameRetract` / `isScPlusRetract` are facts about the
  project's corner-chart vocabulary on which B is silent; in B ⇒ A they are proved outright
  (identity retraction is tame, `ScRetraction.id_isTame`; `remark_4_1_3_const`).
-/

namespace RoundTrip.V4_1
open Polyfold Set

def A : Prop :=
  type_of% @Polyfold.MPolyfold.hasCornerStructure_iff.{0} ∧
  type_of% @Polyfold.MPolyfold.HasCornerStructure.isTame.{0} ∧
  type_of% @Polyfold.MChart.IsCornerChart.isTameRetract.{0} ∧
  type_of% @Polyfold.MChart.IsCornerChart.isScPlusRetract.{0}

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.hasCornerStructure_iff.{0}, @Polyfold.MPolyfold.HasCornerStructure.isTame.{0},
    @Polyfold.MChart.IsCornerChart.isTameRetract.{0},
    @Polyfold.MChart.IsCornerChart.isScPlusRetract.{0}⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

omit [T2Space X] [ParacompactSpace X] in
/-- A project corner chart is a corner chart in B's sense. -/
theorem isCornerChartB_of {χ : MChart X} (h : χ.IsCornerChart) : IsCornerChartB χ := by
  have := h.finiteDimensional
  exact ⟨this, fun m => χ.model.E.toBase_surjective m, h.isRelOpenInQuadrant⟩

/-- A corner chart in B's sense which is a chart of `P` can be replaced, around each of its
points, by a project corner chart of `P`. -/
theorem exists_of_isCornerChartB {χ : MChart X} (hχ : P.IsChart χ) (h : IsCornerChartB χ)
    {x : X} (hx : x ∈ χ.source) :
    ∃ χ' : MChart X, P.IsChart χ' ∧ x ∈ χ'.source ∧ χ'.IsCornerChart := by
  obtain ⟨χ', h1, h2, h3, -⟩ :=
    MChart.exists_isCornerChart_of_finiteDimensional hχ h.2.2 h.1
  exact ⟨χ', h1, h2 ▸ hx, h3⟩

/-- The corner charts of `P` form a corner atlas in B's sense once they cover `X`. -/
theorem isCornerAtlasB_of (h : ∀ x : X, ∃ χ : MChart X, P.IsChart χ ∧ x ∈ χ.source ∧
    χ.IsCornerChart) : IsCornerAtlasB P {χ | P.IsChart χ ∧ χ.IsCornerChart} :=
  ⟨fun χ hχ => isCornerChartB_of hχ.2, fun χ hχ χ' hχ' => MPolyfold.IsChart.compatible P hχ.1 hχ'.1,
    fun x => by obtain ⟨χ, h1, h2, h3⟩ := h x; exact ⟨χ, ⟨h1, h3⟩, h2⟩, fun χ hχ => hχ.1⟩

/-- B's corner structure, in local form. -/
theorem local_of_B {S : Set (MChart X)} (hS : IsCornerAtlasB P S) (x : X) :
    ∃ χ : MChart X, P.IsChart χ ∧ x ∈ χ.source ∧ χ.IsCornerChart := by
  obtain ⟨χ, hχ, hx⟩ := hS.2.2.1 x
  exact exists_of_isCornerChartB (hS.2.2.2 χ hχ) (hS.1 χ hχ) hx

end Glue

theorem A_to_B : A → B := by
  rintro ⟨hiff, -, -, -⟩ X _ _ _ P
  constructor
  · intro h
    exact ⟨_, isCornerAtlasB_of (hiff.1 h)⟩
  · rintro ⟨S, hS⟩
    exact hiff.2 (local_of_B hS)

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {X} _ _ _ {P} => ?_, fun {X} _ _ _ {P} h => ?_, fun {X} _ {χ} h => ?_,
    fun {X} _ {χ} h => ?_⟩
  · constructor
    · intro h
      obtain ⟨S, hS⟩ := (hB X P).1 h
      exact local_of_B hS
    · intro h
      exact (hB X P).2 ⟨_, isCornerAtlasB_of h⟩
  · -- the corner atlas of B is an equivalent atlas of tame charts
    obtain ⟨S, h1, h2, h3, h4⟩ := (hB X P).1 h
    refine ⟨⟨S, h2, h3⟩, (MAtlas.equiv_iff _ _).2 fun φ hφ ψ hψ => h4 φ hφ ψ hψ,
      fun φ hφ => ?_⟩
    have hU := (h1 φ hφ).2.2
    exact ⟨ScRetraction.id hU, image_id _, ScRetraction.id_isTame hU⟩
  · -- chart level, outright: the identity retraction is tame
    obtain ⟨V, _, _, _, C, U, hU, hχ⟩ := h
    rw [hχ]
    exact ⟨ScRetraction.id hU, image_id _, ScRetraction.id_isTame hU⟩
  · -- chart level, outright: Remark 4.3 for the constant structure
    obtain ⟨V, _, _, _, C, U, hU, hχ⟩ := h
    rw [hχ]
    exact (remark_4_1_3_const V).2.2 C U hU.isScRetract

#rt_check RoundTrip.V4_1.A_to_B [Polyfold.MPolyfold.hasCornerStructure_iff, Polyfold.MPolyfold.HasCornerStructure.isTame, Polyfold.MChart.IsCornerChart.isTameRetract, Polyfold.MChart.IsCornerChart.isScPlusRetract]
#rt_check RoundTrip.V4_1.B_to_A [Polyfold.MPolyfold.hasCornerStructure_iff, Polyfold.MPolyfold.HasCornerStructure.isTame, Polyfold.MChart.IsCornerChart.isTameRetract, Polyfold.MChart.IsCornerChart.isScPlusRetract]
#rt_overlap RoundTrip.V4_1.B_to_A [Polyfold.MPolyfold.hasCornerStructure_iff, Polyfold.MPolyfold.HasCornerStructure.isTame, Polyfold.MChart.IsCornerChart.isTameRetract, Polyfold.MChart.IsCornerChart.isScPlusRetract]

end RoundTrip.V4_1
