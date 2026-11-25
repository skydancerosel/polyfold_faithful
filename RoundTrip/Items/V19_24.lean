import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_24

set_option maxSynthPendingDepth 3

/-! Round trip for V19_24 (2021 Proposition 19.4.2, p. 880: the three properness conditions are
equivalent).  Universes at `0`.  `A` = `proposition_19_4_2` ((v1) ⇔ (v2) ⇔ (v3) read with the limit
in the fibre, `PropernessV3Lim`) ∧ `one_iff_two` ∧ `two_three` ((v2) ⇒ (v3) as printed) ∧
`three_two_hyp` ((v3) as printed ⇒ (v2) when `T` is Hausdorff) ∧
`propernessV3_of_locallyCompactSpace` ∧ `proposition_19_4_2_v3_without_limit` ∧
`gluedBasic_propernessV3` ∧ `gluedBasic_not_propernessV2`.  `B` = for every representative `F`,
`(v1) ⇔ (v2)` and `(v2) ⇔ (v3)` with (v3) as printed (no `|Ψ(p)| = z`).

`B` does not hold: for `gluedBasic` (Remark 19.2.3, domains `ℝ`), (v3) as printed holds and (v2) does
not.  `not_B` re-proves these two facts from non-item lemmas (`orbitChartV3_of_locallyCompactSpace`,
`gluedBasic_natOpen`, `gluedLines_π_eq_iff`), so `B_to_A` (ex falso) passes `#rt_check`.  `A ⇒ B`
does not hold (`not_A_to_B`).  What `A` does give of `B`: (v1) ⇔ (v2) and (v2) ⇒ (v3)
(`A_to_B_part`). -/

namespace RoundTrip.V19_24
open Polyfold Polyfold.GroupoidalCategory Filter Topology

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_one_iff_two.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_two_three.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_three_two_hyp.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.propernessV3_of_locallyCompactSpace.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.proposition_19_4_2_v3_without_limit) ∧
  (type_of% @Polyfold.GroupoidalCategory.gluedBasic_propernessV3) ∧
  (type_of% @Polyfold.GroupoidalCategory.gluedBasic_not_propernessV2)

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_one_iff_two.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_two_three.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_three_two_hyp.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.propernessV3_of_locallyCompactSpace.{0},
    @Polyfold.GroupoidalCategory.proposition_19_4_2_v3_without_limit,
    @Polyfold.GroupoidalCategory.gluedBasic_propernessV3,
    @Polyfold.GroupoidalCategory.gluedBasic_not_propernessV2⟩

theorem natT_eq {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    (hB : B.U.HasClassUniformizers) : natT B.U = B.natTop hB :=
  TopologicalSpace.generateFrom_setOfPred_isOpen (B.natTop hB)

/-- `T^F_{Ψ,Ψ'}` is the topology of `B.M Ψ Ψ'` for a representative `F`. -/
theorem topology_eq {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    {F : B.U.TransitionData} (hF : (⟦F⟧ : B.U.TransitionConstruction) = B.𝓕)
    (Ψ Ψ' : B.U.Unif) : F.topology Ψ Ψ' = B.rep.topology Ψ Ψ' :=
  TopologicalSpace.ext (funext fun _ => propext (B.isOpen_M_iff hF).symm)

theorem tendsto_iff_of_eq {X : Type} {t₁ t₂ : TopologicalSpace X} (h : t₁ = t₂) (f : ℕ → X)
    (x : X) : @Tendsto ℕ X f atTop (@nhds X t₁ x) ↔ @Tendsto ℕ X f atTop (@nhds X t₂ x) := by
  subst h; rfl

theorem V1_iff {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    {F : B.U.TransitionData} (hF : (⟦F⟧ : B.U.TransitionConstruction) = B.𝓕) :
    V1 F ↔ B.PropernessV1 := by
  constructor
  · intro hv Ψ o
    obtain ⟨W, hWo, hoW, hW⟩ := hv Ψ o
    refine ⟨W, hWo, hoW, fun Ψ' h hs p hp => ?_⟩
    obtain ⟨φ, x, hφ, hx⟩ := hW Ψ' h hs ⟨p, hp⟩
    exact ⟨φ, hφ, x, (tendsto_iff_of_eq (topology_eq B hF Ψ Ψ') _ _).1 hx⟩
  · intro hv Ψ o
    obtain ⟨W, hWo, hoW, hW⟩ := hv Ψ o
    refine ⟨W, hWo, hoW, fun Ψ' h hs ⟨p, hp⟩ => ?_⟩
    obtain ⟨φ, hφ, x, hx⟩ := hW Ψ' h hs p hp
    exact ⟨φ, x, hφ, (tendsto_iff_of_eq (topology_eq B hF Ψ Ψ') _ _).2 hx⟩

theorem V2_iff {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    (hB : B.U.HasClassUniformizers) : V2 B.U ↔ B.PropernessV2 hB := by
  unfold V2 BasicConstruction.PropernessV2 Chapter19.OrbitChartV2
  rw [natT_eq B hB]
  rfl

theorem V3_iff {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    (hB : B.U.HasClassUniformizers) : V3 B.U ↔ B.PropernessV3 hB := by
  constructor
  · intro h Ψ o
    obtain ⟨W, hWo, hoW, hW⟩ := h Ψ o
    refine ⟨W, hWo, hoW, fun q hq z hz => ?_⟩
    obtain ⟨φ, p, hφ, hp, hl⟩ := hW q hq ⟨z, by rw [natT_eq B hB]; exact hz⟩
    exact ⟨φ, hφ, p, hp, hl⟩
  · intro h Ψ o
    obtain ⟨W, hWo, hoW, hW⟩ := h Ψ o
    refine ⟨W, hWo, hoW, fun q hq ⟨z, hz⟩ => ?_⟩
    obtain ⟨φ, hφ, p, hp, hl⟩ := hW q hq z (by rw [natT_eq B hB] at hz; exact hz)
    exact ⟨φ, p, hφ, hp, hl⟩

/-! ### `B` does not hold: `gluedBasic`, re-proved from non-item lemmas -/

section Glued
open EpGroupoid.Examples Set

theorem glued_lc (Ψ : gluedBasic.U.Unif) : LocallyCompactSpace Ψ.1.O := by
  obtain ⟨Ψ₁, α, hΨ₁⟩ := Ψ
  have h := gluedU_mem hΨ₁
  subst h
  exact inferInstanceAs (LocallyCompactSpace (Fin 1 → ℝ))

theorem glued_v3 : gluedBasic.PropernessV3 gluedBasic_hB := by
  let _inst := gluedBasic.natTop gluedBasic_hB
  intro Ψ o
  have := Ψ.1.P.metrizableSpace
  have := glued_lc Ψ
  exact Chapter19.orbitChartV3_of_locallyCompactSpace _ o

theorem glued_not_v2 : ¬ gluedBasic.PropernessV2 gluedBasic_hB := by
  intro hv
  let _inst := gluedBasic.natTop gluedBasic_hB
  obtain ⟨U, hU, h0, hcl⟩ := hv ⟨gluedUnif 1, ((0 : Fin 1 → ℝ), 1), rfl⟩ (0 : Fin 1 → ℝ)
  have hU' : IsOpen (U : Set (Fin 1 → ℝ)) := hU
  have hmem : gluedLines.π ((0 : Fin 1 → ℝ), -1) ∈
      closure ((fun q => gluedLines.π ((gluedUnif 1).obj q)) '' U) := by
    rw [mem_closure_iff]
    intro W hW hzW
    obtain ⟨V, hV, h0V, hsV⟩ := gluedBasic_natOpen hW hzW
    obtain ⟨t, ht, htp⟩ := exists_pos_mem_of_isOpen (hU'.inter hV) ⟨h0, h0V⟩
    refine ⟨gluedLines.π (t, 1), ?_, t, ht.1, rfl⟩
    rw [← gluedLines_π_eq_iff.2 ⟨rfl, Or.inr htp⟩]
    exact hsV t ht.2
  obtain ⟨q, hq⟩ := hcl hmem
  change gluedLines.π (q, 1) = gluedLines.π ((0 : Fin 1 → ℝ), -1) at hq
  obtain ⟨rfl, h | h⟩ := gluedLines_π_eq_iff.1 hq
  · exact absurd h (by decide)
  · exact lt_irrefl _ h

end Glued

/-- **`B` does not hold**: for `gluedBasic` and its representative, (v3) as printed holds and (v2)
does not. -/
theorem not_B : ¬ B := by
  intro hB'
  have h := (hB' gluedLines gluedBasic gluedBasic.rep gluedBasic_hB gluedBasic.mk_rep).2
  rw [V2_iff gluedBasic gluedBasic_hB, V3_iff gluedBasic gluedBasic_hB] at h
  exact glued_not_v2 (h.2 glued_v3)

/-- `A ⇒ B` does not hold (`A` holds, `B` does not). -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- What `A` gives of `B`: (v1) ⇔ (v2) and (v2) ⇒ (v3) as printed, for every representative. -/
theorem A_to_B_part : A → ∀ (C : GroupoidalCategory.{0}) (B : C.BasicConstruction)
    (F : B.U.TransitionData), B.U.HasClassUniformizers →
    Quotient.mk (GroupoidalCategory.UniformizerConstruction.TransitionData.setoid B.U) F = B.𝓕 →
    (V1 F ↔ V2 B.U) ∧ (V2 B.U → V3 B.U) := by
  intro hA C B F hB hF
  rw [V1_iff B hF, V2_iff B hB, V3_iff B hB]
  exact ⟨hA.2.1 B hB, hA.2.2.1 B hB⟩

/-- `B ⇒ A`, ex falso (`not_B`). -/
theorem B_to_A : B → A := fun h => (not_B h).elim

theorem main_B_to_A (h : B) :
    type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2.{0} :=
  (not_B h).elim

#rt_check RoundTrip.V19_24.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_one_iff_two,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_two_three,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_three_two_hyp,
  Polyfold.GroupoidalCategory.BasicConstruction.propernessV3_of_locallyCompactSpace,
  Polyfold.GroupoidalCategory.proposition_19_4_2_v3_without_limit,
  Polyfold.GroupoidalCategory.gluedBasic_propernessV3,
  Polyfold.GroupoidalCategory.gluedBasic_not_propernessV2]
#rt_check RoundTrip.V19_24.main_B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_one_iff_two,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_two_three,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_three_two_hyp,
  Polyfold.GroupoidalCategory.BasicConstruction.propernessV3_of_locallyCompactSpace,
  Polyfold.GroupoidalCategory.proposition_19_4_2_v3_without_limit,
  Polyfold.GroupoidalCategory.gluedBasic_propernessV3,
  Polyfold.GroupoidalCategory.gluedBasic_not_propernessV2]
#rt_check RoundTrip.V19_24.A_to_B_part [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_one_iff_two,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_two_three,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_three_two_hyp,
  Polyfold.GroupoidalCategory.BasicConstruction.propernessV3_of_locallyCompactSpace,
  Polyfold.GroupoidalCategory.proposition_19_4_2_v3_without_limit,
  Polyfold.GroupoidalCategory.gluedBasic_propernessV3,
  Polyfold.GroupoidalCategory.gluedBasic_not_propernessV2]
#rt_overlap RoundTrip.V19_24.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_one_iff_two,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_two_three,
  Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_2_three_two_hyp,
  Polyfold.GroupoidalCategory.BasicConstruction.propernessV3_of_locallyCompactSpace,
  Polyfold.GroupoidalCategory.proposition_19_4_2_v3_without_limit,
  Polyfold.GroupoidalCategory.gluedBasic_propernessV3,
  Polyfold.GroupoidalCategory.gluedBasic_not_propernessV2]

end RoundTrip.V19_24
