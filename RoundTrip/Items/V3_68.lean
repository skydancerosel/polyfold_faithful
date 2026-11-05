import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_68

/-!
Round trip for V3_68 (Theorem 3.19), refreshed 2026-11-02 against HEAD (germ reading).  `A` is the
conjunction of the types of `Polyfold.theorem_3_19`, `Polyfold.theorem_3_19_linearization`,
`Polyfold.theorem_3_23`, `Polyfold.lemma_2_26`, `Polyfold.theorem_3_19_linearization_sc` and
(added 2026-11-02, second refresh) `Polyfold.StrongBundle.linAt_isScFredholm`, universes
instantiated at `0` (`MPolyfold.IsWithoutBoundary` is vocabulary).  The blind statement `B` is
unchanged.

Neither direction is proved; both gaps are genuine.

* `A → B`:
  - B's first clause (at **every** zero, in **every** strong bundle chart, `f'(x₀)` is
    sc-Fredholm) now follows from `A`: its new conjunct `StrongBundle.linAt_isScFredholm` gives
    it (`clause_one`, proved from the hypothesis `A`).  (`theorem_3_19_linearization_sc` alone
    gives it only in the chart of the germ data and only when `Tf(x₀)` is onto there.)
  - B's second clause: B assumes only `IsScFredholmSection` (germ data in any compatible chart, no
    tameness) and `IsLinSurjAt`; A's `theorem_3_19` needs tame germ data
    (`IsScFredholmSectionTame`) and the added `IsGoodPositionGermFilled`.  The project has no
    lemma producing tame germ data from `IsScFredholmSection` (not even for `d_X ≡ 0`); every
    implicit function theorem of the project assumes `IsScFredholmSectionTame`.  B's conclusions
    "dimension = index of `f'(x₀)` in every chart", "`f'(y)` onto in every chart" and
    "`ker f'(y) = T_yS(f, U)`" are not in A either.
* `B → A`: A contains Lemma 2.26 (`d_A ≤ d_X` for every sub-M-polyfold) and the boundary-case
  Theorem 3.23, which B (assuming `d_X ≡ 0` and only about the zero set of `f`) cannot give; A's
  `theorem_3_19_linearization(_sc)` is about the filling germ `Dg(0)` on all of `E` and needs no
  `d_X ≡ 0`; A's `theorem_3_19` concludes good position in a tame chart, a notion B does not mention;
  A's `linAt_isScFredholm` (every level Fredholm with the index of every germ datum) is more than
  B's first clause.
-/

namespace RoundTrip.V3_68
open Polyfold StrongRetr

/-- The project's statement: the theorems listed for Theorem 3.19, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_19.{0, 0} ∧ type_of% @Polyfold.theorem_3_19_linearization.{0, 0} ∧
    type_of% @Polyfold.theorem_3_23.{0, 0} ∧ type_of% @Polyfold.lemma_2_26.{0} ∧
    type_of% @Polyfold.theorem_3_19_linearization_sc.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.linAt_isScFredholm.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_19.{0, 0}, @Polyfold.theorem_3_19_linearization.{0, 0},
    @Polyfold.theorem_3_23.{0, 0}, @Polyfold.lemma_2_26.{0},
    @Polyfold.theorem_3_19_linearization_sc.{0, 0},
    @Polyfold.StrongBundle.linAt_isScFredholm.{0, 0}⟩

section Glue
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

omit [T2Space Y] [ParacompactSpace Y] in
/-- The conclusion of `linAt_isScFredholm` in a chart gives B's `ChartLinScFredholm` there. -/
lemma chartLin_of (f : X → Y) (x : X) (c : StrongBundleChart PX P) (hxV : x ∈ c.φ.source)
    (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x)
    (hzU : c.φ.model.E.toBase 1 z ∈ c.U)
    (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
    (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
    (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
    (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
      hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU))
    (hsc : IsScFredholm (hD.toScOperator.restrict hT hK hTK)) :
    ChartLinScFredholm c f x (fredholmIndex (hD.toScOperator.restrict hT hK hTK 0)) := by
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [c.r_image, hz]; exact c.φ.mapsTo_model x hxV
  set T := hD.toScOperator.restrict hT hK hTK with hTdef
  have hL : IsScOperator (T 0) := T.isScOperator
  have hLT : hL.toScOperator = T := ScOperator.ext_base (by rw [hL.toScOperator_zero])
  refine ⟨z, hz, rangeS (ρCLM c.isRetraction hzU), ?_, hT, hK, T 0, ?_, hL, ?_, ?_⟩
  · ext h
    rw [SetLike.mem_coe, mem_rangeS_ρCLM_iff c.isRetraction hzO hzU, hz]
    rfl
  · intro v
    change hD.toScOperator 0 v.1 = _
    rw [hD.toScOperator_zero]
  · rw [hLT]; exact hsc
  · rw [hLT, scIndex_eq_fredholmIndex]

end Glue

/-- **B's first clause from `A`**: by `A`'s conjunct `StrongBundle.linAt_isScFredholm`, at every
zero of an sc-Fredholm section and in every strong bundle chart around it, `f'(x₀)` is sc-Fredholm
in B's sense.  (`theorem_3_19_linearization_sc` alone gives this only in the chart of the germ
data and under surjectivity.) -/
theorem clause_one (hA : A) {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X) (hf : Bd.IsScFredholmSection f)
    (hx0 : IsZeroAt P f x₀) :
    ∀ c : StrongBundleChart PX P, Bd.IsChart c → x₀ ∈ c.φ.source →
      ∃ i : ℤ, ChartLinScFredholm c f x₀ i := by
  intro c hc hxV
  have hxs : x₀ ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hx0
  have hz : c.φ.model.E.toBase 1 (MPolyfold.levelLift c.φ 1 x₀) = c.φ x₀ :=
    PX.toBase_levelLift c.isChart hxV (Set.mem_iInter.1 hxs 1)
  have hzU : c.φ.model.E.toBase 1 (MPolyfold.levelLift c.φ 1 x₀) ∈ c.U := by
    rw [hz]
    exact StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ c.φ.mapsTo_model x₀ hxV)
  obtain ⟨hD, hT, hK, hTK, -, hsc, -⟩ := hA.2.2.2.2.2 hf hx0 hc hxV hz hzU
  exact ⟨_, chartLin_of f x₀ c hxV _ hz hzU hD hT hK hTK hsc⟩

#rt_check RoundTrip.V3_68.clause_one [Polyfold.theorem_3_19, Polyfold.theorem_3_19_linearization,
  Polyfold.theorem_3_23, Polyfold.lemma_2_26, Polyfold.theorem_3_19_linearization_sc,
  Polyfold.StrongBundle.linAt_isScFredholm]

end RoundTrip.V3_68
