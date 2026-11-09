import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_46

/-!
Round trip for V3_46 (Proposition 3.52), refreshed 2026-11-02 against HEAD (germ reading).
`A` is the conjunction of the types of the listed theorems `Polyfold.proposition_3_6_5_index`,
`Polyfold.proposition_3_6_5_local_index`, `Polyfold.ConjugationData.scDeriv_isFredholm_index`,
`Polyfold.ConjugationData.index_eq`, `Polyfold.proposition_3_6_5_preprint`, `Polyfold.proposition_3_6_5_local`,
`Polyfold.isFredholm_equiv_comp_equiv`, `Polyfold.proposition_3_1_10_basic_level_zero`,
`Polyfold.proposition_3_6_5_sc`, `Polyfold.proposition_3_6_5_local_sc`,
`Polyfold.ConjugationData.scDeriv_isScFredholm` and `Polyfold.StrongBundle.linAt_isScFredholm`,
universes instantiated at `0`.  (`ConjugationData` is vocabulary.)

* `A → B` is **proved** from the conjunct `StrongBundle.linAt_isScFredholm` (germ reading): for an
  sc-Fredholm section (B's tame section is one, `toIsScFredholmSection`) at a zero `x` and **any**
  strong bundle chart `c` around `x`, with `z` the level-1 lift of `φ(x)` (`x` is smooth), the
  restriction `Lin(z) : T_zO → K_z` of `D(f̂ ∘ r)(z)` is an sc-operator between the sc-subspaces
  `T_zO = Dr(z)E`, `K_z = ρ(z)F` and is sc-Fredholm, with level-0 index `dim d.Pn − dim d.Q` for
  every germ datum (filling germ, sc⁺-germ, conjugation) of Definition 3.11 at `x`.  The glue:
  `K_z = ρ(z)F` is B's fibre `{h | (φ(x), h) ∈ K}` (`mem_rangeS_ρCLM_iff`); B's sc-operator on
  `T_zO` is the level-0 map of the restricted sc-operator (`ScOperator.ext_base`); B's germ data
  (whole-chart filled version, sc-smooth `s` on `U`, tame chart) are germ data in the germ reading
  (`IsFilledVersion.isFillingGerm`, `IsScSmooth.isScSmoothGerm`, `IsTameChart.isChart`).
* `B → A` is not proved: B assumes a tame strong bundle and a tame sc-Fredholm section, whereas
  A's `proposition_3_6_5_preprint(_index,_sc)` need only an sc-Fredholm germ at `x₀` in an arbitrary bundle
  (and state the Fredholm property of `Dg(0)` on all of `E` for the filling); the remaining
  conjuncts are local lemmas (`proposition_3_6_5_local(_index,_sc)`, `ConjugationData.*`,
  `isFredholm_equiv_comp_equiv`, `proposition_3_1_10_basic_level_zero`) about which B says nothing.
-/

namespace RoundTrip.V3_46
open Polyfold StrongRetr

/-- The project's statement: the theorems listed for Proposition 3.52, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.proposition_3_6_5_index.{0, 0} ∧
    type_of% @Polyfold.proposition_3_6_5_local_index ∧
    type_of% @Polyfold.ConjugationData.scDeriv_isFredholm_index ∧
    type_of% @Polyfold.ConjugationData.index_eq ∧
    type_of% @Polyfold.proposition_3_6_5_preprint.{0, 0} ∧
    type_of% @Polyfold.proposition_3_6_5_local ∧
    type_of% @Polyfold.isFredholm_equiv_comp_equiv.{0, 0, 0, 0} ∧
    type_of% @Polyfold.proposition_3_1_10_basic_level_zero ∧
    type_of% @Polyfold.proposition_3_6_5_sc.{0, 0} ∧
    type_of% @Polyfold.proposition_3_6_5_local_sc ∧
    type_of% @Polyfold.ConjugationData.scDeriv_isScFredholm ∧
    type_of% @Polyfold.StrongBundle.linAt_isScFredholm.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.proposition_3_6_5_index.{0, 0}, @Polyfold.proposition_3_6_5_local_index,
    @Polyfold.ConjugationData.scDeriv_isFredholm_index, @Polyfold.ConjugationData.index_eq,
    @Polyfold.proposition_3_6_5_preprint.{0, 0}, @Polyfold.proposition_3_6_5_local,
    @Polyfold.isFredholm_equiv_comp_equiv.{0, 0, 0, 0}, @Polyfold.proposition_3_1_10_basic_level_zero,
    @Polyfold.proposition_3_6_5_sc.{0, 0}, @Polyfold.proposition_3_6_5_local_sc,
    @Polyfold.ConjugationData.scDeriv_isScFredholm, @Polyfold.StrongBundle.linAt_isScFredholm.{0, 0}⟩

section Glue
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

omit [T2Space Y] [ParacompactSpace Y] in
/-- The conclusion of `linAt_isScFredholm` in a chart gives B's `ChartLinScFredholm` there, with
the level-0 index. -/
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

theorem A_to_B : A → B := by
  intro hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlin⟩ := hA
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x _hTame hf hx0
  have hF : Bd.IsScFredholmSection f := hf.toIsScFredholmSection
  have hxs : x ∈ PX.smoothSet := hF.mem_smoothSet_of_isZeroAt hx0
  -- the data in a chart around `x`
  have hz : ∀ c : StrongBundleChart PX P, x ∈ c.φ.source →
      c.φ.model.E.toBase 1 (MPolyfold.levelLift c.φ 1 x) = c.φ x := fun c hxV =>
    PX.toBase_levelLift c.isChart hxV (Set.mem_iInter.1 hxs 1)
  have hzU : ∀ c : StrongBundleChart PX P, x ∈ c.φ.source →
      c.φ.model.E.toBase 1 (MPolyfold.levelLift c.φ 1 x) ∈ c.U := fun c hxV => by
    rw [hz c hxV]
    exact StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ c.φ.mapsTo_model x hxV)
  refine ⟨fun c hc hxV => ?_, fun c₀ h0 g s hdat D c hc hxV => ?_⟩
  · obtain ⟨hD, hT, hK, hTK, -, hsc, -⟩ := hlin hF hx0 hc hxV (hz c hxV) (hzU c hxV)
    exact ⟨_, chartLin_of f x c hxV _ (hz c hxV) (hzU c hxV) hD hT hK hTK hsc⟩
  · obtain ⟨hD, hT, hK, hTK, -, hsc, hlvl⟩ := hlin hF hx0 hc hxV (hz c hxV) (hzU c hxV)
    obtain ⟨hc₀, hxV₀, hφ₀, hfill, hs, hs0⟩ := hdat
    have hQ := c₀.relOpen.isPartialQuadrant.isQuadrantLike
    have hsg : IsScPlusGerm c₀.φ.model.C c₀.U s :=
      ⟨ScNbhdGerm.ofSet c₀.relOpen.relOpen h0, fun u hu => hu,
        hs.isScSmoothGerm hQ c₀.relOpen.relOpen h0⟩
    have hind := (hlvl 0).2.2 c₀ hc₀.isChart hxV₀ hφ₀ h0 g s
      (IsFilledVersion.isFillingGerm c₀.relOpen c₀.isRetraction h0 hfill) hsg hs0 D
    have := chartLin_of f x c hxV _ (hz c hxV) (hzU c hxV) hD hT hK hTK hsc
    rwa [hind] at this

#rt_check RoundTrip.V3_46.A_to_B [Polyfold.proposition_3_6_5_index, Polyfold.proposition_3_6_5_local_index,
  Polyfold.ConjugationData.scDeriv_isFredholm_index, Polyfold.ConjugationData.index_eq,
  Polyfold.proposition_3_6_5_preprint, Polyfold.proposition_3_6_5_local, Polyfold.isFredholm_equiv_comp_equiv,
  Polyfold.proposition_3_1_10_basic_level_zero, Polyfold.proposition_3_6_5_sc,
  Polyfold.proposition_3_6_5_local_sc, Polyfold.ConjugationData.scDeriv_isScFredholm,
  Polyfold.StrongBundle.linAt_isScFredholm]

end RoundTrip.V3_46
