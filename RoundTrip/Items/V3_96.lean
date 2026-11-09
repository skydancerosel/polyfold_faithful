import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_96

/-!
Round trip for V3_96 (Proposition 3.52 / Theorem 3.19: the linearization at a zero is
sc-Fredholm), refreshed 2026-11-02 against HEAD (germ reading).  `A` is the conjunction of the
types of the theorems among the decls (`StrongBundle.IsSurjLinOfIndex` is a definition,
vocabulary): `StrongBundle.linAt_index_of_conjugationData`,
`StrongBundle.isSurjLinOfIndex_of_conjugationData`,
`StrongBundle.IsGoodPositionGerm.exists_isSurjLinOfIndex`, `theorem_3_1_22_linearization_index`,
`finrank_ker_eq_fredholmIndex_of_surjective`, `StrongBundle.linAt_isScFredholm`,
`StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex`, `proposition_3_6_5_sc`,
`theorem_3_1_22_linearization_sc`, universes instantiated at `0`.

* `A → B` is **proved** from the conjunct `StrongBundle.linAt_isScFredholm`: for an sc-Fredholm
  section (germ reading) at a zero `x` and **every** strong bundle chart `c` around `x`, with `z`
  the level-`1` lift of `φ(x)` (`x` is smooth), `Lin(z) : T_zO → K_z` is an sc-operator between
  the sc-subspaces `T_zO`, `K_z = ρ(z)F` and is sc-Fredholm.  Glue: `K_z` is B's fibre
  `{h | (φ(x), h) ∈ K}` (`mem_rangeS_ρCLM_iff`), and B's sc-operator on `T_zO` is the level-0 map
  of the restricted sc-operator (`ScOperator.ext_base`).  The tame-bundle hypothesis of B is not
  needed.  (`A_to_B_level0`, the level-0 shadow proved in the audit from
  `linAt_index_of_conjugationData`, is kept, repaired for the germ form of that theorem.)
* `B → A` is not proved: B assumes a tame bundle and gives only the existence of an index per
  chart, while A needs no tameness, identifies the index as `n − N` for every conjugation, gives
  surjectivity and `dim ker = d` under good position, the sc-Fredholm property of `Dg(0)` on all of
  `E` for the filling germ, and contains the linear-algebra lemma
  `finrank_ker_eq_fredholmIndex_of_surjective`.
-/

namespace RoundTrip.V3_96
open Polyfold Set StrongRetr

/-- The project's statement, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.StrongBundle.linAt_index_of_conjugationData.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.isSurjLinOfIndex_of_conjugationData.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.IsGoodPositionGerm.exists_isSurjLinOfIndex.{0, 0} ∧
    type_of% @Polyfold.theorem_3_1_22_linearization_index.{0, 0} ∧
    type_of% @Polyfold.finrank_ker_eq_fredholmIndex_of_surjective.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.linAt_isScFredholm.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex.{0, 0} ∧
    type_of% @Polyfold.proposition_3_6_5_sc.{0, 0} ∧
    type_of% @Polyfold.theorem_3_1_22_linearization_sc.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.StrongBundle.linAt_index_of_conjugationData.{0, 0},
    @Polyfold.StrongBundle.isSurjLinOfIndex_of_conjugationData.{0, 0},
    @Polyfold.StrongBundle.IsGoodPositionGerm.exists_isSurjLinOfIndex.{0, 0},
    @Polyfold.theorem_3_1_22_linearization_index.{0, 0},
    @Polyfold.finrank_ker_eq_fredholmIndex_of_surjective.{0, 0},
    @Polyfold.StrongBundle.linAt_isScFredholm.{0, 0},
    @Polyfold.StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex.{0, 0},
    @Polyfold.proposition_3_6_5_sc.{0, 0},
    @Polyfold.theorem_3_1_22_linearization_sc.{0, 0}⟩

/-- **The level-`0` shadow of `B`**, from the hypothesis `A` (conjunct
`linAt_index_of_conjugationData`): at a zero of an sc-Fredholm section, the linearization
`Lin(z) : T_zO → K_z` is Fredholm in every strong bundle chart, at every level-`1` lift, with an
index `i` independent of the chart. -/
theorem A_to_B_level0 (hA : A) :
    ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      (Bd : StrongBundle PX P) (f : X → Y) (x : X),
      IsTameStrongBundle Bd → Bd.IsScFredholmSection f → IsZeroAt P f x →
        ∃ i : ℤ, ∀ c : StrongBundleChart PX P, Bd.IsChart c → x ∈ c.φ.source →
          ∀ (z : c.φ.model.E.lvl 1) (_ : c.φ.model.E.toBase 1 z = c.φ.toPartialEquiv x)
            (hzU : c.φ.model.E.toBase 1 z ∈ c.U)
            (L : ↥(rangeS (scDeriv c.U (r c.R) z)) →L[ℝ] ↥(rangeS (ρCLM c.isRetraction hzU))),
            (∀ v, (L v : c.F.lvl 0) = linAt c.U c.R (c.principal f) z v) →
              L.IsFredholm ∧ fredholmIndex L = i := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x _ hf hx
  obtain ⟨-, c₀, hc₀, hxV₀, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ :=
    hf.germ x (hf.mem_smoothSet_of_isZeroAt hx)
  obtain ⟨G, hGU, hgG, -⟩ := hfill.germ
  have hg1 := (hgG 1).1.isSc1GermWith_scDerivGerm
  obtain ⟨dc⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  refine ⟨Module.finrank ℝ dc.Pn - Module.finrank ℝ dc.Q, fun c hc hxV z hz hzU L hL => ?_⟩
  obtain ⟨hF, hind, -⟩ :=
    hA.1 hf.isScSmooth hx hc₀ hxV₀ hφ0 h0 hfill hGU hg1 hs hs0 dc hc hxV hz hzU L hL
  exact ⟨hF, hind⟩

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

theorem A_to_B : A → B := by
  intro hA
  obtain ⟨-, -, -, -, -, hlin, -⟩ := hA
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f x _hTame hf hx0 c hc hxV
  have hxs : x ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hx0
  have hz : c.φ.model.E.toBase 1 (MPolyfold.levelLift c.φ 1 x) = c.φ x :=
    PX.toBase_levelLift c.isChart hxV (Set.mem_iInter.1 hxs 1)
  have hzU : c.φ.model.E.toBase 1 (MPolyfold.levelLift c.φ 1 x) ∈ c.U := by
    rw [hz]
    exact StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ c.φ.mapsTo_model x hxV)
  obtain ⟨hD, hT, hK, hTK, -, hsc, -⟩ := hlin hf hx0 hc hxV hz hzU
  exact ⟨_, chartLin_of f x c hxV _ hz hzU hD hT hK hTK hsc⟩

#rt_check RoundTrip.V3_96.A_to_B_level0 [Polyfold.StrongBundle.linAt_index_of_conjugationData,
  Polyfold.StrongBundle.isSurjLinOfIndex_of_conjugationData,
  Polyfold.StrongBundle.IsGoodPositionGerm.exists_isSurjLinOfIndex,
  Polyfold.theorem_3_1_22_linearization_index, Polyfold.finrank_ker_eq_fredholmIndex_of_surjective,
  Polyfold.StrongBundle.linAt_isScFredholm,
  Polyfold.StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex, Polyfold.proposition_3_6_5_sc,
  Polyfold.theorem_3_1_22_linearization_sc]
#rt_check RoundTrip.V3_96.A_to_B [Polyfold.StrongBundle.linAt_index_of_conjugationData,
  Polyfold.StrongBundle.isSurjLinOfIndex_of_conjugationData,
  Polyfold.StrongBundle.IsGoodPositionGerm.exists_isSurjLinOfIndex,
  Polyfold.theorem_3_1_22_linearization_index, Polyfold.finrank_ker_eq_fredholmIndex_of_surjective,
  Polyfold.StrongBundle.linAt_isScFredholm,
  Polyfold.StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex, Polyfold.proposition_3_6_5_sc,
  Polyfold.theorem_3_1_22_linearization_sc]

end RoundTrip.V3_96
