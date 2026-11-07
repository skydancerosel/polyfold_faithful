import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_52

/-! Round trip for V6_52 (the path category `PX`, p. 228).

A is the conjunction of the 23 theorems of the comparison row (universes at `0`; `smoothTransition_half`
has none).  B formalizes the composition `[ψ] * [φ]` with the LITERAL formula `ψ(β(s))` on
`[1/2, 1]`; the blind author predicted it false.  It is: `not_B` (for `β = κ(3s) + κ(3s − 2)`, the
constant path at `0` followed by the identity path of `ℝ¹` has no composite, since the two formulas
give `0` and `1` at `s = 1/2`).  Hence `A → B` is false and `B → A` holds only ex falso.

`BIntended` (formula `ψ(β(s) − 1)`, `β(0) = 0`, `β(1) = 2`) is compared too: `A_to_BIntended` is
proved from A's theorems plus glue (`betaConcat`, a composite for every admissible `β`, and
`scHomotopic_concatPath_of_beta`, every `β`-composite is homotopic rel end points to the project's
`concatPath`, by the straight-line homotopy of the inner reparametrizations).  `BIntended → A`
is not proved: A also states the groupoid laws (`concat_reverse`, `reverse_concat`, `inv_mk`), the
smoothness of the end points, `ScHomotopic.symm` for arbitrary maps, and technical tools
(`isScSmoothMap_ite`, `isScHomotopyRel_triHomotopy`, `smoothTransition_half`, …) that BIntended does
not state.  The glue below is proved without A's theorems (local copy `ite_smooth` of the two-piece
gluing, from `MPolyfold.isScSmoothMap_of_eventuallyEq`).
-/

namespace RoundTrip.V6_52
open Polyfold Set Filter Topology
open scoped ContDiff

/-- The project's statement (the 23 theorems of the row), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.smoothTransition_half ∧
  type_of% @Polyfold.isScSmoothMap_const_of_mem_smoothSet.{0} ∧
  type_of% @Polyfold.isScSmoothMap_ite.{0} ∧
  type_of% @Polyfold.isScSmoothMap_ite₃.{0} ∧
  type_of% @Polyfold.concatPath_of_le_two_thirds.{0} ∧
  type_of% @Polyfold.concatPath_of_one_third_le.{0} ∧
  type_of% @Polyfold.ScHomotopic.refl.{0} ∧
  type_of% @Polyfold.ScHomotopic.symm.{0} ∧
  type_of% @Polyfold.ScHomotopic.trans.{0} ∧
  type_of% @Polyfold.isScHomotopyRel_triHomotopy.{0} ∧
  type_of% @Polyfold.ScPath.source_mem_smoothSet.{0} ∧
  type_of% @Polyfold.ScPath.target_mem_smoothSet.{0} ∧
  type_of% @Polyfold.ScPath.concat_congr.{0} ∧
  type_of% @Polyfold.ScPath.const_concat.{0} ∧
  type_of% @Polyfold.ScPath.concat_const.{0} ∧
  type_of% @Polyfold.ScPath.concat_assoc.{0} ∧
  type_of% @Polyfold.ScPath.concat_reverse.{0} ∧
  type_of% @Polyfold.ScPath.reverse_concat.{0} ∧
  type_of% @Polyfold.PathCat.comp_mk.{0} ∧
  type_of% @Polyfold.PathCat.id_eq_mk.{0} ∧
  type_of% @Polyfold.PathCat.mk_eq_mk_iff.{0} ∧
  type_of% @Polyfold.PathCat.exists_eq_mk.{0} ∧
  type_of% @Polyfold.PathCat.inv_mk.{0}

theorem A_holds : A :=
  ⟨@Polyfold.smoothTransition_half, @Polyfold.isScSmoothMap_const_of_mem_smoothSet.{0},
    @Polyfold.isScSmoothMap_ite.{0}, @Polyfold.isScSmoothMap_ite₃.{0},
    @Polyfold.concatPath_of_le_two_thirds.{0}, @Polyfold.concatPath_of_one_third_le.{0},
    @Polyfold.ScHomotopic.refl.{0}, @Polyfold.ScHomotopic.symm.{0},
    @Polyfold.ScHomotopic.trans.{0}, @Polyfold.isScHomotopyRel_triHomotopy.{0},
    @Polyfold.ScPath.source_mem_smoothSet.{0}, @Polyfold.ScPath.target_mem_smoothSet.{0},
    @Polyfold.ScPath.concat_congr.{0}, @Polyfold.ScPath.const_concat.{0},
    @Polyfold.ScPath.concat_const.{0}, @Polyfold.ScPath.concat_assoc.{0},
    @Polyfold.ScPath.concat_reverse.{0}, @Polyfold.ScPath.reverse_concat.{0},
    @Polyfold.PathCat.comp_mk.{0}, @Polyfold.PathCat.id_eq_mk.{0},
    @Polyfold.PathCat.mk_eq_mk_iff.{0}, @Polyfold.PathCat.exists_eq_mk.{0},
    @Polyfold.PathCat.inv_mk.{0}⟩

local notation "κ" => Real.smoothTransition

/-! ### An admissible `β` and the refutation of the literal B -/

/-- `β₀(s) = κ(3s) + κ(3s − 2)`: smooth, `β₀ = κ(3s)` on `[0, 2/3]`, `β₀ = 1 + κ(3s − 2)` on
`[1/3, 1]` (the reparametrization behind the project's `concatPath`). -/
noncomputable def β₀ (s : ℝ) : ℝ := κ (3 * s) + κ (3 * s - 2)

theorem contDiff_β₀ : ContDiff ℝ ∞ β₀ :=
  (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)).add
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

theorem continuous_β₀ : Continuous β₀ := contDiff_β₀.continuous

theorem β₀_of_le {s : ℝ} (hs : s ≤ 2 / 3) : β₀ s = κ (3 * s) := by
  have h : κ (3 * s - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  rw [β₀, h, add_zero]

theorem β₀_of_ge {s : ℝ} (hs : 1 / 3 ≤ s) : β₀ s = 1 + κ (3 * s - 2) := by
  rw [β₀, Real.smoothTransition.one_of_one_le (by linarith)]

theorem β₀_zero : β₀ 0 = 0 := by
  rw [β₀_of_le (by norm_num), mul_zero, Real.smoothTransition.zero]

theorem β₀_one : β₀ 1 = 2 := by
  rw [β₀_of_ge (by norm_num), show (3 : ℝ) * 1 - 2 = 1 by norm_num, Real.smoothTransition.one]
  norm_num

theorem β₀_eq_one {s : ℝ} (h₁ : 1 / 3 ≤ s) (h₂ : s ≤ 2 / 3) : β₀ s = 1 := by
  have h : κ (3 * s - 2) = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  rw [β₀_of_ge h₁, h, add_zero]

theorem β₀_image₁ : β₀ '' Icc 0 (1 / 2) = Icc 0 1 := by
  apply Subset.antisymm
  · rintro _ ⟨s, hs, rfl⟩
    rw [β₀_of_le (by linarith [hs.2])]
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · have h := intermediate_value_Icc (show (0 : ℝ) ≤ 1 / 3 by norm_num)
      continuous_β₀.continuousOn
    rw [β₀_zero, β₀_eq_one le_rfl (by norm_num)] at h
    exact h.trans (image_mono (Icc_subset_Icc le_rfl (by norm_num)))

theorem β₀_image₂ : β₀ '' Icc (1 / 2) 1 = Icc 1 2 := by
  apply Subset.antisymm
  · rintro _ ⟨s, hs, rfl⟩
    rw [β₀_of_ge (by linarith [hs.1])]
    exact ⟨by linarith [Real.smoothTransition.nonneg (3 * s - 2)],
      by linarith [Real.smoothTransition.le_one (3 * s - 2)]⟩
  · have h := intermediate_value_Icc (show (2 / 3 : ℝ) ≤ 1 by norm_num)
      continuous_β₀.continuousOn
    rw [β₀_one, β₀_eq_one (by norm_num) le_rfl] at h
    exact h.trans (image_mono (Icc_subset_Icc (by norm_num) le_rfl))

theorem β₀_eventually : ∀ᶠ s in 𝓝 (1 / 2 : ℝ), β₀ s = β₀ (1 / 2) := by
  filter_upwards [Ioo_mem_nhds (show (1 / 3 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) < 2 / 3 by norm_num)] with s hs
  rw [β₀_eq_one hs.1.le hs.2.le, β₀_eq_one (by norm_num) (by norm_num)]

theorem isAdmissibleBetaB_β₀ : IsAdmissibleBetaB β₀ :=
  ⟨contDiff_β₀, β₀_image₁, β₀_image₂, β₀_eventually⟩

/-- **The literal B is false**: in `X = ℝ¹`, `φ` the constant path at `0` and `ψ = id` (from `0` to
`1`) have no `γ` with `γ = φ ∘ β₀` on `[0, 1/2]` and `γ = ψ ∘ β₀` on `[1/2, 1]`: at `s = 1/2` this
says `0 = ψ(β₀(1/2)) = ψ(1) = 1`. -/
theorem not_B : ¬ B := by
  intro hB
  obtain ⟨γ, -, h₁, h₂⟩ := (hB (rnPolyfold 1) β₀ isAdmissibleBetaB_β₀).2.2.1
    (fun _ => pt1 0) id (pt1 0) (pt1 0) (pt1 1)
    ⟨isScSmoothMap_rn_rn_of_contDiff contDiff_const, rfl, rfl⟩
    ⟨isScSmoothMap_rn_rn_of_contDiff contDiff_id, rfl, rfl⟩
  have e₁ := h₁ (1 / 2) ⟨by norm_num, le_rfl⟩
  have e₂ := h₂ (1 / 2) ⟨le_rfl, by norm_num⟩
  rw [e₁, β₀_eq_one (by norm_num) (by norm_num)] at e₂
  have := congrFun e₂ 0
  simp only [pt1_apply, id] at this
  norm_num at this

/-- `A → B` is false: A holds and B does not. -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B → A`, ex falso (B is false). -/
theorem B_to_A : B → A := fun h => (not_B h).elim

/-! ### Glue for the intended statement (without the item's theorems) -/

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- A map in two pieces along a continuous `σ`, the pieces agreeing near the break: sc-smooth
(local copy of the gluing lemma, from `MPolyfold.isScSmoothMap_of_eventuallyEq`). -/
theorem ite_smooth {m : ℕ} {σ : (Fin m → ℝ) → ℝ} (hσ : Continuous σ) {c ε : ℝ}
    (hε : 0 < ε) {g₁ g₂ : (Fin m → ℝ) → X} (hg₁ : (rnPolyfold m).IsScSmoothMap PX g₁)
    (hg₂ : (rnPolyfold m).IsScSmoothMap PX g₂) (h : ∀ q, |σ q - c| < ε → g₁ q = g₂ q) :
    (rnPolyfold m).IsScSmoothMap PX fun q => if σ q ≤ c then g₁ q else g₂ q := by
  refine MPolyfold.isScSmoothMap_of_eventuallyEq fun q => ?_
  rcases le_or_gt (σ q) c with hq | hq
  · refine ⟨g₁, hg₁, ?_⟩
    filter_upwards [(isOpen_lt hσ continuous_const).mem_nhds
      (show σ q < c + ε by linarith)] with p hp
    change σ p < c + ε at hp
    split_ifs with hpc
    · rfl
    · exact (h p (abs_sub_lt_iff.2 ⟨by linarith, by linarith [not_le.1 hpc]⟩)).symm
  · refine ⟨g₂, hg₂, ?_⟩
    filter_upwards [(isOpen_lt continuous_const hσ).mem_nhds hq] with p hp
    change c < σ p at hp
    rw [if_neg (not_le.2 hp)]

/-- `β(1/2) = 1` from the two image conditions. -/
theorem beta_half {β : ℝ → ℝ} (h₁ : β '' Icc 0 (1 / 2) = Icc 0 1)
    (h₂ : β '' Icc (1 / 2) 1 = Icc 1 2) : β (1 / 2) = 1 := by
  have a : β (1 / 2) ∈ Icc (0 : ℝ) 1 := h₁ ▸ mem_image_of_mem β ⟨by norm_num, le_rfl⟩
  have b : β (1 / 2) ∈ Icc (1 : ℝ) 2 := h₂ ▸ mem_image_of_mem β ⟨le_rfl, by norm_num⟩
  exact le_antisymm a.2 b.1

/-- An `ε`-neighbourhood of `1/2` on which `β = 1`. -/
theorem exists_beta_eq_one {β : ℝ → ℝ} (h₁ : β '' Icc 0 (1 / 2) = Icc 0 1)
    (h₂ : β '' Icc (1 / 2) 1 = Icc 1 2) (h : ∀ᶠ s in 𝓝 (1 / 2 : ℝ), β s = β (1 / 2)) :
    ∃ ε > 0, ∀ s, |s - 1 / 2| < ε → β s = 1 := by
  obtain ⟨ε, hε, hεβ⟩ := Metric.eventually_nhds_iff.1 h
  exact ⟨ε, hε, fun s hs => (hεβ (by rwa [Real.dist_eq])).trans (beta_half h₁ h₂)⟩

/-- The `β`-composite `φ(β(s))` on `s ≤ 1/2`, `ψ(β(s) − 1)` on `s > 1/2`. -/
noncomputable def betaConcat (β : ℝ → ℝ) (φ ψ : (Fin 1 → ℝ) → X) : (Fin 1 → ℝ) → X := fun q =>
  if q 0 ≤ 1 / 2 then φ (pt1 (β (q 0))) else ψ (pt1 (β (q 0) - 1))

theorem isScSmoothMap_betaConcat {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {ε : ℝ} (hε : 0 < ε)
    (hβc : ∀ s, |s - 1 / 2| < ε → β s = 1) {φ ψ : (Fin 1 → ℝ) → X}
    (hφ : (rnPolyfold 1).IsScSmoothMap PX φ) (hψ : (rnPolyfold 1).IsScSmoothMap PX ψ)
    (hj : φ (pt1 1) = ψ (pt1 0)) : (rnPolyfold 1).IsScSmoothMap PX (betaConcat β φ ψ) :=
  ite_smooth (σ := fun q => q 0) (continuous_apply 0) hε (isScSmoothMap_reparam hφ hβ)
    (isScSmoothMap_reparam hψ (hβ.sub contDiff_const)) fun q hq => by
      change φ (pt1 (β (q 0))) = ψ (pt1 (β (q 0) - 1))
      rw [hβc _ hq, sub_self, hj]

/-- **Every `β`-composite is homotopic rel end points to the project's `concatPath`**, by the
straight-line homotopy `(1 − τ) β(s) + τ κ(3s)` (resp. `(1 − τ)(β(s) − 1) + τ κ(3s − 2)`) of the
inner reparametrizations; near `s = 1/2` both pieces are the junction point. -/
theorem scHomotopic_concatPath_of_beta {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    (hβ1 : β 1 = 2) {ε : ℝ} (hε : 0 < ε) (hβc : ∀ s, |s - 1 / 2| < ε → β s = 1)
    {φ ψ γ : (Fin 1 → ℝ) → X} (hφ : (rnPolyfold 1).IsScSmoothMap PX φ)
    (hψ : (rnPolyfold 1).IsScSmoothMap PX ψ) (hj : φ (pt1 1) = ψ (pt1 0))
    (h₁ : ∀ s ∈ Icc (0 : ℝ) (1 / 2), γ (pt1 s) = φ (pt1 (β s)))
    (h₂ : ∀ s ∈ Icc (1 / 2 : ℝ) 1, γ (pt1 s) = ψ (pt1 (β s - 1))) :
    ScHomotopic PX γ (concatPath φ ψ) := by
  have hκ₁ : ContDiff ℝ ∞ fun t : ℝ => κ (3 * t) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)
  have hκ₂ : ContDiff ℝ ∞ fun t : ℝ => κ (3 * t - 2) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  refine ⟨fun q => if q 1 ≤ 1 / 2 then φ (pt1 ((1 - q 0) * β (q 1) + q 0 * κ (3 * q 1)))
    else ψ (pt1 ((1 - q 0) * (β (q 1) - 1) + q 0 * κ (3 * q 1 - 2))), ?_, ?_, ?_, ?_, ?_⟩
  · refine ite_smooth (σ := fun q => q 1) (continuous_apply 1)
      (lt_min hε (show (0 : ℝ) < 1 / 6 by norm_num))
      (isScSmoothMap_comp_pt1₂ hφ (contDiff_lerp hβ hκ₁))
      (isScSmoothMap_comp_pt1₂ hψ (contDiff_lerp (hβ.sub contDiff_const) hκ₂)) fun q hq => ?_
    have hq₁ : |q 1 - 1 / 2| < ε := hq.trans_le (min_le_left _ _)
    have hq₂ := abs_sub_lt_iff.1 (hq.trans_le (min_le_right _ _))
    change φ (pt1 ((1 - q 0) * β (q 1) + q 0 * κ (3 * q 1))) =
      ψ (pt1 ((1 - q 0) * (β (q 1) - 1) + q 0 * κ (3 * q 1 - 2)))
    rw [hβc _ hq₁, Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith), sub_self, mul_zero, mul_zero, add_zero,
      mul_one, mul_one, sub_add_cancel, hj]
  · intro t ht
    simp only [pt2_apply_zero, pt2_apply_one, sub_zero, one_mul, zero_mul, add_zero]
    split_ifs with h
    · exact (h₁ t ⟨ht.1, h⟩).symm
    · exact (h₂ t ⟨(not_le.1 h).le, ht.2⟩).symm
  · intro t _
    simp only [pt2_apply_zero, pt2_apply_one, sub_self, zero_mul, zero_add, one_mul]
    simp only [concatPath, pt1_apply]
    by_cases h : t ≤ 1 / 2 <;> simp
  · intro τ _
    simp only [pt2_apply_zero, pt2_apply_one]
    rw [if_pos (by norm_num), h₁ 0 ⟨le_rfl, by norm_num⟩, hβ0]
    simp only [mul_zero, Real.smoothTransition.zero, add_zero]
  · intro τ _
    simp only [pt2_apply_zero, pt2_apply_one]
    rw [if_neg (by norm_num), h₂ 1 ⟨by norm_num, le_rfl⟩, hβ1]
    have e : (1 - τ) * ((2 : ℝ) - 1) + τ * κ (3 * 1 - 2) = 2 - 1 := by
      rw [show (3 : ℝ) * 1 - 2 = 1 by norm_num, Real.smoothTransition.one]
      ring
    rw [e]

end Glue

/-! ### `A → BIntended` -/

theorem A_to_BIntended : A → BIntended := by
  intro hA
  obtain ⟨-, hconst, -, -, -, -, hrefl, hsymm, htrans, -, hsrc, -, hcongr, hcc, hcc', hassoc,
    -, -, -, -, -, -, -⟩ := hA
  intro X _ _ _ PX β hβ
  obtain ⟨⟨hβs, hβi₁, hβi₂, hβe⟩, hβ0, hβ1⟩ := hβ
  obtain ⟨ε, hε, hβc⟩ := exists_beta_eq_one hβi₁ hβi₂ hβe
  -- every `β`-composite of `φ`, `ψ` is homotopic to `concatPath φ ψ`
  have key : ∀ {φ ψ γ : (Fin 1 → ℝ) → X} {x y z : X}, IsPathB PX φ x y → IsPathB PX ψ y z →
      IsConcatIntB β φ ψ γ → ScHomotopic PX γ (concatPath φ ψ) :=
    fun hφ hψ hc => scHomotopic_concatPath_of_beta hβs hβ0 hβ1 hε hβc hφ.1 hψ.1
      (hφ.2.2.trans hψ.2.1.symm) hc.1 hc.2
  -- the paths as `ScPath`s
  let sp : ∀ {γ : (Fin 1 → ℝ) → X} {x y : X}, IsPathB PX γ x y → ScPath PX x y :=
    fun h => ⟨_, h.1, h.2.1, h.2.2⟩
  have hcat : ∀ {φ ψ : (Fin 1 → ℝ) → X} {x y z : X}, IsPathB PX φ x y → IsPathB PX ψ y z →
      IsPathB PX (concatPath φ ψ) x z := fun hφ hψ =>
    ⟨isScSmoothMap_concatPath hφ.1 hψ.1 (hφ.2.2.trans hψ.2.1.symm), concatPath_zero.trans hφ.2.1,
      concatPath_one.trans hψ.2.2⟩
  refine ⟨fun x hx => ⟨hconst hx, rfl, rfl⟩, fun x y => ⟨fun γ => hrefl γ.2.1,
    fun h => hsymm h, fun {a _ c} h₁ h₂ => htrans h₁ h₂ a.2.1 c.2.1⟩, ?_, ?_, ?_, ?_⟩
  · -- (ii) the composite exists
    intro φ ψ x y z hφ hψ
    have hj : φ (pt1 1) = ψ (pt1 0) := hφ.2.2.trans hψ.2.1.symm
    refine ⟨betaConcat β φ ψ, ⟨isScSmoothMap_betaConcat hβs hε hβc hφ.1 hψ.1 hj, ?_, ?_⟩,
      fun s hs => ?_, fun s hs => ?_⟩
    · change (if (0 : ℝ) ≤ 1 / 2 then _ else _) = x
      rw [if_pos (by norm_num), pt1_apply, hβ0, hφ.2.1]
    · change (if (1 : ℝ) ≤ 1 / 2 then _ else _) = z
      rw [if_neg (by norm_num), pt1_apply, hβ1, show (2 : ℝ) - 1 = 1 by norm_num, hψ.2.2]
    · change (if s ≤ 1 / 2 then _ else _) = _
      rw [if_pos hs.2, pt1_apply]
    · change (if s ≤ 1 / 2 then _ else _) = _
      split_ifs with h
      · have hs' : s = 1 / 2 := le_antisymm h hs.1
        subst hs'
        rw [pt1_apply, beta_half hβi₁ hβi₂, sub_self, hj]
      · rfl
  · -- (iii) well defined on classes
    intro φ φ' ψ ψ' γ γ' x y z hφ hφ' hψ hψ' hγ hγ' hφφ' hψψ' hc hc'
    have h₁ := key hφ hψ hc
    have h₂ := hsymm (key hφ' hψ' hc')
    have h₃ : ScHomotopic PX (concatPath φ ψ) (concatPath φ' ψ') :=
      hcongr (a := sp hφ) (a' := sp hφ') hφφ' (b := sp hψ) (b' := sp hψ') hψψ'
    exact htrans (htrans h₁ h₃ hγ.1 (hcat hφ' hψ').1) h₂ hγ.1 hγ'.1
  · -- (iv) associativity
    intro φ ψ χ γ₁ γ₂ γ₃ γ₄ w x y z hφ hψ hχ hγ₁ hc₁ hγ₂ hc₂ hγ₃ hc₃ hγ₄ hc₄
    have e₂ := key hγ₁ hχ hc₂
    have e₁ : ScHomotopic PX (concatPath γ₁ χ) (concatPath (concatPath φ ψ) χ) :=
      hcongr (a := sp hγ₁) (a' := sp (hcat hφ hψ)) (key hφ hψ hc₁) (b := sp hχ) (b' := sp hχ)
        (hrefl hχ.1)
    have e₀ : ScHomotopic PX (concatPath (concatPath φ ψ) χ) (concatPath φ (concatPath ψ χ)) :=
      hassoc (sp hφ) (sp hψ) (sp hχ)
    have e₃ : ScHomotopic PX (concatPath φ (concatPath ψ χ)) (concatPath φ γ₃) :=
      hcongr (a := sp hφ) (a' := sp hφ) (hrefl hφ.1) (b := sp (hcat hψ hχ)) (b' := sp hγ₃)
        (hsymm (key hψ hχ hc₃))
    have e₄ := hsymm (key hφ hγ₃ hc₄)
    have s₁ := (hcat hγ₁ hχ).1
    have s₂ := (hcat (hcat hφ hψ) hχ).1
    have s₃ := (hcat hφ (hcat hψ hχ)).1
    have s₄ := (hcat hφ hγ₃).1
    exact htrans (htrans (htrans (htrans e₂ e₁ hγ₂.1 s₂) e₀ hγ₂.1 s₃) e₃ hγ₂.1 s₄) e₄ hγ₂.1
      hγ₄.1
  · -- (v) identities
    intro φ γ x y hφ hγ
    have hx : x ∈ PX.smoothSet := hsrc (sp hφ)
    have hy : y ∈ PX.smoothSet := hsrc (sp hφ).reverse
    refine ⟨fun hcx hc => ?_, fun hcy hc => ?_⟩
    · exact htrans (key hcx hφ hc) (hcc (x := x) hx (sp hφ)) hγ.1 hφ.1
    · exact htrans (key hφ hcy hc) (hcc' (y := y) hy (sp hφ)) hγ.1 hφ.1

/-! `BIntended → A` is not proved: A also states the groupoid laws (`concat_reverse`,
`reverse_concat`, `PathCat.inv_mk`), the smoothness of end points (`source_mem_smoothSet`), the
symmetry of `ScHomotopic` for arbitrary maps, the presentation of `PathCat` (`comp_mk`, `id_eq_mk`,
`mk_eq_mk_iff`, `exists_eq_mk`) and technical tools (`isScSmoothMap_ite`, `isScSmoothMap_ite₃`,
`isScHomotopyRel_triHomotopy`, `smoothTransition_half`, the `concatPath` formulas).  BIntended's
category laws (iii)–(v) do give `concat_congr`, `const_concat`, `concat_const`, `concat_assoc` (take
`β = β₀`, for which `concatPath φ ψ` is a `β₀`-composite); the rest is not a consequence. -/

open Lean Elab Command in
/-- `#rt_check_except_defs T [d₁, …] [n₁, …]` (as in items V1_32, V2_24, V3_64, V6_19): the harness
traversal `rtCollect` with the bodies of the definitions `dᵢ` not unfolded; fails if the proof of
`T` reaches some `nᵢ` elsewhere. -/
elab "#rt_check_except_defs " t:ident " [" ds:ident,* "]" " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let seen := ds.getElems.foldl (fun s d => s.insert d.getId) NameSet.empty
  let used := rtCollect env roots.toList seen
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do throwError "FAIL: {t.getId} uses {bad} outside the bodies of the definitions"
  logInfo m!"OK: {t.getId} reaches the banned declarations only through the bodies of the definitions {ds.getElems.toList.map (·.getId)}"

#rt_check RoundTrip.V6_52.not_B [Polyfold.smoothTransition_half,
  Polyfold.isScSmoothMap_const_of_mem_smoothSet, Polyfold.isScSmoothMap_ite,
  Polyfold.isScSmoothMap_ite₃, Polyfold.concatPath_of_le_two_thirds,
  Polyfold.concatPath_of_one_third_le, Polyfold.ScHomotopic.refl, Polyfold.ScHomotopic.symm,
  Polyfold.ScHomotopic.trans, Polyfold.isScHomotopyRel_triHomotopy,
  Polyfold.ScPath.source_mem_smoothSet, Polyfold.ScPath.target_mem_smoothSet,
  Polyfold.ScPath.concat_congr, Polyfold.ScPath.const_concat, Polyfold.ScPath.concat_const,
  Polyfold.ScPath.concat_assoc, Polyfold.ScPath.concat_reverse, Polyfold.ScPath.reverse_concat,
  Polyfold.PathCat.comp_mk, Polyfold.PathCat.id_eq_mk, Polyfold.PathCat.mk_eq_mk_iff,
  Polyfold.PathCat.exists_eq_mk, Polyfold.PathCat.inv_mk]
-- `B_to_A` and `A_to_BIntended` cannot pass `#rt_check`/`#rt_check_soft`: their statements contain
-- `A`, which mentions `PathCat.category`, whose composition `ScPathClass.comp` is
-- `Quotient.map₂ ScPath.concat ScPath.concat_congr` (the banned `concat_congr`, proved with the banned
-- `isScSmoothMap_ite`, passed directly, not abstracted into a `_proof_N`).  The traversal with the
-- bodies of A's vocabulary definitions (`ScPathClass.comp`, `ScPathClass.reverse`, `PathCat.category`,
-- `PathCat.groupoid`, `ScPath.const`, `ScPath.setoid`) not unfolded passes.
/-- error: rt_check_soft FAIL: RoundTrip.V6_52.B_to_A uses [Polyfold.isScSmoothMap_ite, Polyfold.ScPath.concat_congr] -/
#guard_msgs in
#rt_check_soft RoundTrip.V6_52.B_to_A [Polyfold.smoothTransition_half,
  Polyfold.isScSmoothMap_const_of_mem_smoothSet, Polyfold.isScSmoothMap_ite,
  Polyfold.isScSmoothMap_ite₃, Polyfold.concatPath_of_le_two_thirds,
  Polyfold.concatPath_of_one_third_le, Polyfold.ScHomotopic.refl, Polyfold.ScHomotopic.symm,
  Polyfold.ScHomotopic.trans, Polyfold.isScHomotopyRel_triHomotopy,
  Polyfold.ScPath.source_mem_smoothSet, Polyfold.ScPath.target_mem_smoothSet,
  Polyfold.ScPath.concat_congr, Polyfold.ScPath.const_concat, Polyfold.ScPath.concat_const,
  Polyfold.ScPath.concat_assoc, Polyfold.ScPath.concat_reverse, Polyfold.ScPath.reverse_concat,
  Polyfold.PathCat.comp_mk, Polyfold.PathCat.id_eq_mk, Polyfold.PathCat.mk_eq_mk_iff,
  Polyfold.PathCat.exists_eq_mk, Polyfold.PathCat.inv_mk]
/-- error: rt_check_soft FAIL: RoundTrip.V6_52.A_to_BIntended uses [Polyfold.isScSmoothMap_ite, Polyfold.ScPath.concat_congr] -/
#guard_msgs in
#rt_check_soft RoundTrip.V6_52.A_to_BIntended [Polyfold.smoothTransition_half,
  Polyfold.isScSmoothMap_const_of_mem_smoothSet, Polyfold.isScSmoothMap_ite,
  Polyfold.isScSmoothMap_ite₃, Polyfold.concatPath_of_le_two_thirds,
  Polyfold.concatPath_of_one_third_le, Polyfold.ScHomotopic.refl, Polyfold.ScHomotopic.symm,
  Polyfold.ScHomotopic.trans, Polyfold.isScHomotopyRel_triHomotopy,
  Polyfold.ScPath.source_mem_smoothSet, Polyfold.ScPath.target_mem_smoothSet,
  Polyfold.ScPath.concat_congr, Polyfold.ScPath.const_concat, Polyfold.ScPath.concat_const,
  Polyfold.ScPath.concat_assoc, Polyfold.ScPath.concat_reverse, Polyfold.ScPath.reverse_concat,
  Polyfold.PathCat.comp_mk, Polyfold.PathCat.id_eq_mk, Polyfold.PathCat.mk_eq_mk_iff,
  Polyfold.PathCat.exists_eq_mk, Polyfold.PathCat.inv_mk]
#rt_check_except_defs RoundTrip.V6_52.B_to_A [Polyfold.ScPathClass.comp, Polyfold.ScPathClass.reverse, Polyfold.PathCat.category, Polyfold.PathCat.groupoid, Polyfold.ScPath.const, Polyfold.ScPath.setoid] [Polyfold.smoothTransition_half,
  Polyfold.isScSmoothMap_const_of_mem_smoothSet, Polyfold.isScSmoothMap_ite,
  Polyfold.isScSmoothMap_ite₃, Polyfold.concatPath_of_le_two_thirds,
  Polyfold.concatPath_of_one_third_le, Polyfold.ScHomotopic.refl, Polyfold.ScHomotopic.symm,
  Polyfold.ScHomotopic.trans, Polyfold.isScHomotopyRel_triHomotopy,
  Polyfold.ScPath.source_mem_smoothSet, Polyfold.ScPath.target_mem_smoothSet,
  Polyfold.ScPath.concat_congr, Polyfold.ScPath.const_concat, Polyfold.ScPath.concat_const,
  Polyfold.ScPath.concat_assoc, Polyfold.ScPath.concat_reverse, Polyfold.ScPath.reverse_concat,
  Polyfold.PathCat.comp_mk, Polyfold.PathCat.id_eq_mk, Polyfold.PathCat.mk_eq_mk_iff,
  Polyfold.PathCat.exists_eq_mk, Polyfold.PathCat.inv_mk]
#rt_check_except_defs RoundTrip.V6_52.A_to_BIntended [Polyfold.ScPathClass.comp, Polyfold.ScPathClass.reverse, Polyfold.PathCat.category, Polyfold.PathCat.groupoid, Polyfold.ScPath.const, Polyfold.ScPath.setoid] [Polyfold.smoothTransition_half,
  Polyfold.isScSmoothMap_const_of_mem_smoothSet, Polyfold.isScSmoothMap_ite,
  Polyfold.isScSmoothMap_ite₃, Polyfold.concatPath_of_le_two_thirds,
  Polyfold.concatPath_of_one_third_le, Polyfold.ScHomotopic.refl, Polyfold.ScHomotopic.symm,
  Polyfold.ScHomotopic.trans, Polyfold.isScHomotopyRel_triHomotopy,
  Polyfold.ScPath.source_mem_smoothSet, Polyfold.ScPath.target_mem_smoothSet,
  Polyfold.ScPath.concat_congr, Polyfold.ScPath.const_concat, Polyfold.ScPath.concat_const,
  Polyfold.ScPath.concat_assoc, Polyfold.ScPath.concat_reverse, Polyfold.ScPath.reverse_concat,
  Polyfold.PathCat.comp_mk, Polyfold.PathCat.id_eq_mk, Polyfold.PathCat.mk_eq_mk_iff,
  Polyfold.PathCat.exists_eq_mk, Polyfold.PathCat.inv_mk]
#rt_overlap RoundTrip.V6_52.B_to_A [Polyfold.smoothTransition_half,
  Polyfold.isScSmoothMap_const_of_mem_smoothSet, Polyfold.isScSmoothMap_ite,
  Polyfold.isScSmoothMap_ite₃, Polyfold.concatPath_of_le_two_thirds,
  Polyfold.concatPath_of_one_third_le, Polyfold.ScHomotopic.refl, Polyfold.ScHomotopic.symm,
  Polyfold.ScHomotopic.trans, Polyfold.isScHomotopyRel_triHomotopy,
  Polyfold.ScPath.source_mem_smoothSet, Polyfold.ScPath.target_mem_smoothSet,
  Polyfold.ScPath.concat_congr, Polyfold.ScPath.const_concat, Polyfold.ScPath.concat_const,
  Polyfold.ScPath.concat_assoc, Polyfold.ScPath.concat_reverse, Polyfold.ScPath.reverse_concat,
  Polyfold.PathCat.comp_mk, Polyfold.PathCat.id_eq_mk, Polyfold.PathCat.mk_eq_mk_iff,
  Polyfold.PathCat.exists_eq_mk, Polyfold.PathCat.inv_mk]
#rt_overlap RoundTrip.V6_52.A_to_BIntended [Polyfold.smoothTransition_half,
  Polyfold.isScSmoothMap_const_of_mem_smoothSet, Polyfold.isScSmoothMap_ite,
  Polyfold.isScSmoothMap_ite₃, Polyfold.concatPath_of_le_two_thirds,
  Polyfold.concatPath_of_one_third_le, Polyfold.ScHomotopic.refl, Polyfold.ScHomotopic.symm,
  Polyfold.ScHomotopic.trans, Polyfold.isScHomotopyRel_triHomotopy,
  Polyfold.ScPath.source_mem_smoothSet, Polyfold.ScPath.target_mem_smoothSet,
  Polyfold.ScPath.concat_congr, Polyfold.ScPath.const_concat, Polyfold.ScPath.concat_const,
  Polyfold.ScPath.concat_assoc, Polyfold.ScPath.concat_reverse, Polyfold.ScPath.reverse_concat,
  Polyfold.PathCat.comp_mk, Polyfold.PathCat.id_eq_mk, Polyfold.PathCat.mk_eq_mk_iff,
  Polyfold.PathCat.exists_eq_mk, Polyfold.PathCat.inv_mk]

end RoundTrip.V6_52
