import Polyfold.Chapter19.CoveringMetrizability
import Polyfold.Chapter19.CoveringCounterexamples

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19, §19.7
"Covering Constructions": examples for **Proposition 19.7.15 (2)** (p. 915), the remark after
**Lemma 19.7.19** (p. 921) and **Theorem 19.7.25** (p. 925).  Numbers and pages are the 2021 text's.

# Examples for §19.7

## The examples

* **Two members of `F̂(0)` with the same `Ψ`.**  In the absolute-value example of
  `CoveringCounterexamples.lean` (`P : ℤ/2 ⋉ (ℤˣ × ℝ) → ℤ/2 ⋉ ℝ`), `twistCU` is a second proper
  covering uniformizer at `β = 0` over the same `Ψ` and the same sheet model
  `τ̂ : ℤ/2 ⋉ (ℤˣ × ℝ) → ℤ/2 ⋉ ℝ`, with `Ψ̂(i, x) = (σ(x) i, x)`, `σ(x) = −1` for `|x| > 1` and
  `σ(x) = 1` otherwise (`σ` is even, so `Ψ̂` is a functor; Definition 19.7.3 asks for no
  continuity of `Ψ̂`).  `twistBasic` has `F̂(0) = {absCU 0, twistCU}`; it is a basic construction
  for `P`
  (Definition 19.7.11, the same keyed transitions on `B`).  For `x = absCU 0`, `y = twistCU`, the
  top target map `t̂ : M(Ψ̂, Ψ̂') → E'` jumps at `|t| = 1`: `not_continuous_tgtHat_twistBasic`.
  So `t̂` is not a local homeomorphism (`proposition_19_7_15_two_without_compatible`), and the
  compatibility `IsCompatible` (an added hypothesis, the reading of l. 44572) is needed for
  Proposition 19.7.15 (2) and does not hold here (`not_isCompatible_twistBasic`).
* **The remark after Lemma 19.7.19** ("the number `k` of classes divides `ℓ`") does not hold as
  we read it: `not_remark_19_7_19_divides`, the connected sheet model `divModel` with three
  sheets `ℤˣ ⊕ {∗}`, `ℤ/2` swapping two of them (`ℓ = 3`, `k = 2`).
* **The witness for Theorem 19.7.25**: `theorem_19_7_25_absBasic` (the hypotheses `IsCompatible`,
  `HasClassUniformizers` and the metrizability of `T_{|B|}` hold for `absBasic`, with `ℤ/2`
  acting non-trivially).
-/

open Set Function Topology TopologicalSpace Filter

noncomputable section

namespace Polyfold

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples GCT.PolyfoldConstruction

section Twist

open Chapter19

/-- **The twist** `σ(x) = −1` for `|x| > 1`, `σ(x) = 1` otherwise. -/
def twistSign (x : Fin 1 → ℝ) : ℤˣ := if 1 < |x 0| then -1 else 1

theorem twistSign_mul_self (x : Fin 1 → ℝ) : twistSign x * twistSign x = 1 := Int.units_mul_self _

/-- `σ` is even: `σ(k x) = σ(x)` for `k ∈ ℤ/2`. -/
theorem twistSign_smul (k : ℤˣ) (x : Fin 1 → ℝ) : twistSign (k • x) = twistSign x := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · rw [one_smul]
  · simp only [twistSign, units_smul_rn_neg_one, Pi.neg_apply, abs_neg]

theorem twistSign_zero : twistSign (fun _ => 0) = 1 := by
  simp [twistSign]

theorem twistSign_two : twistSign (fun _ => 2) = -1 := by
  have : (1 : ℝ) < |(2 : ℝ)| := by norm_num
  simp only [twistSign, this, if_true]

/-- **The twisted proper covering uniformizer at `0`** (Definitions 19.7.3, 19.7.4): the sheet
model of `absCU 0` with `Ψ̂(i, x) = (σ(x) i, x)`. -/
def twistCU : CoveringUniformizer absCovP 0 where
  Ψ := absSliceUnif overlapSlice₀
  ObjE := ℤˣ × (absSliceUnif overlapSlice₀).O
  MorE := (absSliceUnif overlapSlice₀).G × (ℤˣ × (absSliceUnif overlapSlice₀).O)
  E := sheetEp (absSliceUnif overlapSlice₀).smooth_smul ℤˣ
  τ := sheetFunctor (absSliceUnif overlapSlice₀).smooth_smul ℤˣ
  model := (sliceCU overlapSlice₀ 0 (mem_univ _) zero_fix).model
  hat :=
    { obj := fun p => (twistSign (p.2 : overlapSlice₀.V).1 * p.1, (p.2 : overlapSlice₀.V).1)
      mor := fun φ => ((φ.1 : overlapSlice₀.H).1,
        (twistSign (φ.2.2 : overlapSlice₀.V).1 * φ.2.1, (φ.2.2 : overlapSlice₀.V).1))
      src_mor := fun _ => rfl
      tgt_mor := fun φ => by
        obtain ⟨⟨k, hk⟩, i, v⟩ := φ
        refine Prod.ext ?_ rfl
        change k * (twistSign v.1 * i) = twistSign (k • v.1) * (k * i)
        rw [twistSign_smul, mul_left_comm]
      mor_comp := fun _ _ _ => rfl
      mor_unit := fun _ => rfl }
  obj_pt := rfl
  injective_hat p q h := by
    have h2 : (p.2 : overlapSlice₀.V).1 = (q.2 : overlapSlice₀.V).1 := congrArg (fun r => r.2) h
    have h1 : twistSign (p.2 : overlapSlice₀.V).1 * p.1 =
        twistSign (q.2 : overlapSlice₀.V).1 * q.1 := congrArg (fun r => r.1) h
    rw [h2] at h1
    exact Prod.ext (mul_left_cancel h1) (Subtype.ext h2)
  full_hat := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => by
    have hs' : ψ.2 = (twistSign (x.2 : overlapSlice₀.V).1 * x.1, (x.2 : overlapSlice₀.V).1) := hs
    have ht' : ψ.1 • ψ.2 =
        (twistSign (x'.2 : overlapSlice₀.V).1 * x'.1, (x'.2 : overlapSlice₀.V).1) := ht
    rw [hs'] at ht'
    have h1 : ψ.1 * (twistSign (x.2 : overlapSlice₀.V).1 * x.1) =
        twistSign (x'.2 : overlapSlice₀.V).1 * x'.1 := congrArg Prod.fst ht'
    have h2 : ψ.1 • (x.2 : overlapSlice₀.V).1 = (x'.2 : overlapSlice₀.V).1 := congrArg Prod.snd ht'
    rw [← h2, twistSign_smul, mul_left_comm] at h1
    refine ⟨((⟨ψ.1, Subgroup.mem_top _⟩ : overlapSlice₀.H), x), rfl,
      Prod.ext (mul_left_cancel h1) (Subtype.ext h2), Prod.ext rfl hs'.symm⟩
  faithful_hat := (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs _ he =>
    Prod.ext (Subtype.ext (congrArg Prod.fst he)) hs
  obj_comm _ := rfl
  mor_comm _ := rfl
  cartesian_obj o a h := by
    refine ⟨(twistSign (o : overlapSlice₀.V).1 * a.1, o), rfl, Prod.ext ?_ h.symm⟩
    change twistSign (o : overlapSlice₀.V).1 * (twistSign (o : overlapSlice₀.V).1 * a.1) = a.1
    rw [← mul_assoc, twistSign_mul_self, one_mul]
  cartesian_mor φ p h := by
    have h1 : φ.1 = (p.1 : overlapSlice₀.H).1 := congrArg Prod.fst h
    have h2 : φ.2.2 = (p.2 : overlapSlice₀.V).1 := congrArg Prod.snd h
    refine ⟨(p.1, (twistSign (p.2 : overlapSlice₀.V).1 * φ.2.1, p.2)), rfl,
      Prod.ext h1.symm (Prod.ext ?_ h2.symm)⟩
    change twistSign (p.2 : overlapSlice₀.V).1 * (twistSign (p.2 : overlapSlice₀.V).1 * φ.2.1) =
      φ.2.1
    rw [← mul_assoc, twistSign_mul_self, one_mul]

/-- **`F̂` with the twisted member**: `F̂(β) = {absCU β}` for `β ≠ 0` and
`F̂(0) = {absCU 0, twistCU}` (Definition 19.7.7). -/
def twistHatU : CoveringUniformizerConstruction absCovP :=
  ⟨fun β => {Ψh | Ψh = absCU β ∨ ∃ h : (0 : Fin 1 → ℝ) = β, Ψh = h ▸ twistCU}⟩

theorem twistHatU_slice (Ψ : twistHatU.toUniformizerConstruction.Unif) :
    ∃ D : TranslationSlice ℤˣ (Fin 1 → ℝ), Ψ.1 = sliceUniformizer isScSmoothMap_units_smul D := by
  obtain ⟨Ψ₁, β, Ψh, hmem, hΨ⟩ := Ψ
  rcases hmem with rfl | ⟨rfl, rfl⟩
  · obtain ⟨D, hβ, hfix, h⟩ := absCU_eq β
    refine ⟨D, ?_⟩
    change Ψ₁ = _
    rw [← hΨ, h]
    rfl
  · refine ⟨overlapSlice₀, ?_⟩
    change Ψ₁ = _
    rw [← hΨ]
    rfl

/-- **The basic construction with the twisted member** (Definition 19.7.11): `twistHatU` with the
keyed transitions of `B`. -/
def twistBasic : CoveringBasicConstruction absCovP :=
  ⟨twistHatU, ⟦sliceData isScSmoothMap_units_smul twistHatU_slice⟧⟩

theorem twistBasic_hasClassUniformizers : twistBasic.HasClassUniformizers := fun z =>
  Quotient.inductionOn z fun β => ⟨β, rfl, absCU β, Or.inl rfl⟩

/-- The member `absCU 0` of `F̂(0)`. -/
def twistX : twistBasic.hatU.Unif :=
  ⟨0, sliceCU overlapSlice₀ 0 (mem_univ _) zero_fix, Or.inl absCU_zero.symm⟩

/-- The member `twistCU` of `F̂(0)`. -/
def twistY : twistBasic.hatU.Unif := ⟨0, twistCU, Or.inr ⟨rfl, rfl⟩⟩

/-- Both members of `F̂(0)` have the same `Ψ`. -/
theorem twistX_Ψ_eq : twistX.Ψh.Ψ = twistY.Ψh.Ψ := rfl

/-- `t ↦ (t)` in the slice `ℝ`. -/
abbrev twistPt (t : ℝ) : overlapSlice₀.V := ⟨fun _ => t, mem_univ _⟩

theorem continuous_twistPt : Continuous twistPt :=
  (continuous_pi fun _ => continuous_id).subtype_mk _

/-- The path `t ↦ ((1, t), 1_{(1, t)}, (σ(t), t)) ∈ M(Ψ̂, Ψ̂')`. -/
def twistPath (t : ℝ) : twistBasic.MHat twistX twistY :=
  CoveringBasicConstruction.toMHat (⟨((1 : ℤˣ), twistPt t), ((1 : ℤˣ), ((1 : ℤˣ), fun _ => t)),
    (twistSign (fun _ => t), twistPt t), rfl, by
      change (1 : ℤˣ) • ((1 : ℤˣ), (fun _ => t : Fin 1 → ℝ)) =
        (twistSign (fun _ => t) * twistSign (fun _ => t), fun _ => t)
      rw [one_smul, twistSign_mul_self]⟩ : twistX.Ψh.Trans twistY.Ψh)

/-- **The top target map `t̂ : M(Ψ̂, Ψ̂') → E'` of `twistBasic` is not continuous** (for
`Ψ̂ = absCU 0`, `Ψ̂' = twistCU`): along the continuous path `twistPath`, `t̂ = (σ(t), t)` jumps at
`|t| = 1`. -/
theorem not_continuous_tgtHat_twistBasic : ¬ Continuous (twistBasic.tgtHat twistX twistY) := by
  intro h
  obtain ⟨e, he⟩ := twistBasic.toBasic.proposition_19_3_7 twistX.toUnif
  have hpB : (fun t => twistBasic.pB twistX twistY (twistPath t)) =
      fun t => e ((1 : overlapSlice₀.H), twistPt t) := by
    funext t
    rw [he]
    refine TransitionSet.ext rfl rfl ?_
    change twistPt t = (1 : overlapSlice₀.H) • twistPt t
    rw [one_smul]
  have hc : Continuous twistPath := by
    refine continuous_induced_rng.2 ?_
    have hp : Continuous fun t => twistBasic.pB twistX twistY (twistPath t) := by
      rw [hpB]
      exact e.continuous.comp (continuous_const.prodMk continuous_twistPt)
    change Continuous fun t => (⟨(twistBasic.pB twistX twistY (twistPath t),
      ((1 : ℤˣ), twistPt t)), rfl⟩ : twistBasic.Fib twistX twistY)
    exact (hp.prodMk (continuous_const.prodMk continuous_twistPt)).subtype_mk _
  have h1 : Continuous fun t => (twistBasic.tgtHat twistX twistY (twistPath t)).1 :=
    continuous_fst.comp (h.comp hc)
  have h2 := PreconnectedSpace.constant inferInstance h1 (x := 0) (y := 2)
  change twistSign (fun _ => 0) = twistSign (fun _ => 2) at h2
  rw [twistSign_zero, twistSign_two] at h2
  exact absurd h2 (by decide)

/-- **2021 Proposition 19.7.15 (2), p. 915, for `t̂`, without a compatibility between the members
of `F̂(β)`** (why `IsCompatible`, the reading of l. 44572, is added): for the basic construction
`twistBasic` for the finite-to-one covering functor `P : ℤ/2 ⋉ (ℤˣ × ℝ) → ℤ/2 ⋉ ℝ`, whose `F̂(0)`
has two members over the same `Ψ` and the same sheet model (Definition 17.8.4),
`t̂ : M(Ψ̂, Ψ̂') → E'` is not a local homeomorphism. -/
theorem proposition_19_7_15_two_without_compatible :
    IsFiniteToOneCovering absCovP ∧ twistBasic.HasClassUniformizers ∧
      ¬ ∀ x y : twistBasic.hatU.Unif, IsLocalHomeomorph (twistBasic.tgtHat x y) :=
  ⟨absCovP_isFiniteToOneCovering, twistBasic_hasClassUniformizers, fun h =>
    not_continuous_tgtHat_twistBasic (h twistX twistY).continuous⟩

/-- **`IsCompatible` is not automatic**: it does not hold for `twistBasic`. -/
theorem not_isCompatible_twistBasic : ¬ twistBasic.IsCompatible := fun h =>
  not_continuous_tgtHat_twistBasic (h twistX twistY)

end Twist

/-! ### The remark after Lemma 19.7.19 -/

section Divides

/-- Three sheets `ℤˣ ⊕ {∗}`, `ℤ/2` swapping the first two and fixing the third. -/
abbrev divS : Type := ℤˣ ⊕ Unit

/-- **The connected sheet model** `ℤ/2 ⋉ ((ℤˣ ⊕ {∗}) × ℝ) → ℤ/2 ⋉ ℝ` (Definition 17.8.4,
`sheetModel`), `ō = 0`: `ℓ = #τ̂⁻¹(ō) = 3`. -/
def divModel : ProperCoveringModel (sheetFunctor isScSmoothMap_units_smul divS) :=
  sheetModel isScSmoothMap_units_smul divS 0 units_smul_zero_rn

theorem divModel_fiber : divModel.fiber =
    {((Sum.inl 1 : divS), (0 : Fin 1 → ℝ)), (Sum.inl (-1), 0), (Sum.inr (), 0)} := by
  ext ⟨s, v⟩
  change v = 0 ↔ _
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro rfl
    rcases s with i | ⟨⟩
    · rcases Int.units_eq_one_or i with rfl | rfl <;> simp
    · simp
  · rintro (⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩) <;> exact h

theorem divModel_π_inl (i : ℤˣ) :
    (sheetEp isScSmoothMap_units_smul divS).π ((Sum.inl i : divS), (0 : Fin 1 → ℝ)) =
      (sheetEp isScSmoothMap_units_smul divS).π (Sum.inl 1, 0) := by
  refine ((sheetEp isScSmoothMap_units_smul divS).π_eq_π_iff).2 ⟨(i⁻¹, (Sum.inl i, 0)), rfl, ?_⟩
  change (i⁻¹ • ((Sum.inl i : divS), (0 : Fin 1 → ℝ))) = (Sum.inl 1, 0)
  rw [Prod.smul_mk, units_smul_zero_rn]
  change ((Sum.inl (i⁻¹ * i) : divS), (0 : Fin 1 → ℝ)) = _
  rw [inv_mul_cancel]

theorem divModel_π_ne :
    (sheetEp isScSmoothMap_units_smul divS).π ((Sum.inl 1 : divS), (0 : Fin 1 → ℝ)) ≠
      (sheetEp isScSmoothMap_units_smul divS).π (Sum.inr (), 0) := by
  intro h
  obtain ⟨φ, hs, ht⟩ := ((sheetEp isScSmoothMap_units_smul divS).π_eq_π_iff).1 h
  have hs' : φ.2 = ((Sum.inl 1 : divS), (0 : Fin 1 → ℝ)) := hs
  have ht' : φ.1 • φ.2 = ((Sum.inr () : divS), (0 : Fin 1 → ℝ)) := ht
  rw [hs', Prod.smul_mk] at ht'
  have h1 := congrArg Prod.fst ht'
  change (Sum.inl (φ.1 * 1) : divS) = Sum.inr () at h1
  exact Sum.inl_ne_inr h1

/-- **The remark after Lemma 19.7.19, p. 921, "the number `k` of classes divides `ℓ`", does not
hold as we read it**: for the connected proper covering model `divModel` (`ℓ = 3` points over
`ō = 0`), the classes of `y ∼ y'` (Lemma 19.7.19), i.e. the images in `|E|`, number `k = 2`. -/
theorem not_remark_19_7_19_divides :
    divModel.Connected ∧ divModel.fiber.ncard = 3 ∧
      ((sheetEp isScSmoothMap_units_smul divS).π '' divModel.fiber).ncard = 2 ∧ ¬ (2 ∣ 3) := by
  refine ⟨(inferInstance : ConnectedSpace (Fin 1 → ℝ)), ?_, ?_, by decide⟩
  · rw [divModel_fiber]
    refine Set.ncard_eq_three.2 ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;> simp
  · rw [divModel_fiber]
    refine Set.ncard_eq_two.2 ⟨_, _, divModel_π_ne, ?_⟩
    simp only [image_insert_eq, image_singleton, divModel_π_inl]
    ext z
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto

end Divides

/-! ### The witness for Theorem 19.7.25 -/

/-- **The hypotheses of Theorem 19.7.25 hold for `absBasic`** (`ℤ/2` acting non-trivially):
`T_{|B|}` is metrizable, so `T_{|A|}` is metrizable and `P` is a proper covering functor of GCTs
(Definition 17.8.1); both sides of Proposition 19.7.23 hold. -/
theorem theorem_19_7_25_absBasic :
    absBasic.toBasic.PropernessV2 absBasic_hasClassUniformizers.toBasic ∧
    absBasic.PropernessV2A absCovP_isFiniteToOneCovering absBasic_isCompatible
      absBasic_hasClassUniformizers ∧
    @MetrizableSpace _ (absBasic.natTopA absCovP_isFiniteToOneCovering absBasic_isCompatible
        absBasic_hasClassUniformizers) ∧
      @GroupoidFunctor.IsProperCoveringGCT
        (absBasic.toGCTA absCovP_isFiniteToOneCovering absBasic_isCompatible
          absBasic_hasClassUniformizers not_theorem_19_7_25_four_b.1)
        (absBasic.toGCTB absBasic_hasClassUniformizers not_theorem_19_7_25_four_b.1) absCovP := by
  have hv := ((absBasic.toBasic.proposition_19_4_7 absBasic_hasClassUniformizers.toBasic).1
    not_theorem_19_7_25_four_b.1).1
  exact ⟨hv, (absBasic.proposition_19_7_23_hyp _ _ _).2 hv,
    (absBasic.theorem_19_7_25_one_hyp _ _ _ not_theorem_19_7_25_four_b.1).1,
    absBasic.theorem_19_7_25_three_hyp _ _ _ not_theorem_19_7_25_four_b.1⟩

end GroupoidalCategory

end Polyfold
