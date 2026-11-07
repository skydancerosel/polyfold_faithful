import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_49

/-! Round trip for V6_49 (§6.5, sc-smooth paths in a chart and their concatenation, p. 227–228,
and the recollection of p. 201).

* `A`: the conjunction of the types of the item's theorems (universes at `0`):
  `MPolyfold.isScSmoothMap_of_eventuallyEq`, `pt1_apply`, `contDiff_pt1_comp`,
  `exists_nhds_scPath`, `concatPath_of_le`, `concatPath_of_gt`, `isScSmoothMap_concatPath`,
  `concatPath_zero`, `concatPath_one`, `concatPath_half₁`, `concatPath_half₂`,
  `isScSmoothMap_reparam`, `HasLocalPropagation.eq_trans` (`concatPath` is vocabulary).
* `B` (literal, with `ψ(β(s))` on `[1/2, 1]`) is FALSE: `not_B`.  At `s = 1/2` the two formulas
  give `φ(β(1/2))` and `ψ(β(1/2))`; for `φ = id`, `ψ = 1 + id` on `ℝ¹` these differ whatever
  `β(1/2)` is.  Hence `¬ (A → B)` and `B → A` only ex falso.
* Against `BIntended` (`ψ(β(s) − 1)`, `β(0) = 0`, `β(1) = 2`): `A_to_ClaimA` and
  `A_to_ClaimBInt` prove the first two conjuncts from `A` (the paths of an sc-smoothly
  contractible `U` are built from the contraction `H` with `concatPath`; the composition through
  an arbitrary admissible `β` is sc-smooth by locality, `isScSmoothMap_of_eventuallyEq`).  The
  third conjunct `ClaimC` (M-polyfolds are locally path connected; smooth points of one path
  component are joined by an sc⁺-smooth path) has no counterpart in `A` and is not proved.
-/

namespace RoundTrip.V6_49
open Polyfold Set Filter Topology
open scoped ContDiff

local notation "κ" => Real.smoothTransition

/-- The project's statement: the item's theorems, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.MPolyfold.isScSmoothMap_of_eventuallyEq.{0, 0} ∧
  type_of% @Polyfold.pt1_apply ∧
  type_of% @Polyfold.contDiff_pt1_comp ∧
  type_of% @Polyfold.exists_nhds_scPath.{0, 0} ∧
  type_of% @Polyfold.concatPath_of_le.{0} ∧
  type_of% @Polyfold.concatPath_of_gt.{0} ∧
  type_of% @Polyfold.isScSmoothMap_concatPath.{0} ∧
  type_of% @Polyfold.concatPath_zero.{0} ∧
  type_of% @Polyfold.concatPath_one.{0} ∧
  type_of% @Polyfold.concatPath_half₁.{0} ∧
  type_of% @Polyfold.concatPath_half₂.{0} ∧
  type_of% @Polyfold.isScSmoothMap_reparam.{0} ∧
  type_of% @Polyfold.HasLocalPropagation.eq_trans.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.isScSmoothMap_of_eventuallyEq.{0, 0}, @Polyfold.pt1_apply,
    @Polyfold.contDiff_pt1_comp, @Polyfold.exists_nhds_scPath.{0, 0},
    @Polyfold.concatPath_of_le.{0}, @Polyfold.concatPath_of_gt.{0},
    @Polyfold.isScSmoothMap_concatPath.{0}, @Polyfold.concatPath_zero.{0},
    @Polyfold.concatPath_one.{0}, @Polyfold.concatPath_half₁.{0},
    @Polyfold.concatPath_half₂.{0}, @Polyfold.isScSmoothMap_reparam.{0},
    @Polyfold.HasLocalPropagation.eq_trans.{0, 0}⟩

/-! ### The literal `B` is false -/

/-- The literal composition formula is contradictory at `s = 1/2`: for `φ = id` (from `0` to `1`)
and `ψ = 1 + id` (from `1` to `2`) on `ℝ¹`, `γ(1/2) = φ(β(1/2)) = ψ(β(1/2))` is impossible. -/
theorem not_ClaimBLit : ¬ ClaimBLit := by
  rintro ⟨⟨β, hβ⟩, h⟩
  have hφ : IsPathB (rnPolyfold 1) (fun s => s) (pt1 0) (pt1 1) :=
    ⟨isScSmoothMap_rn_rn_of_contDiff contDiff_id, rfl, rfl⟩
  have hψ : IsPathB (rnPolyfold 1) (fun s => pt1 (1 + s 0)) (pt1 1) (pt1 2) := by
    refine ⟨isScSmoothMap_rn_rn_of_contDiff
      (contDiff_pi.2 fun _ => contDiff_const.add (contDiff_apply ℝ ℝ (0 : Fin 1))), ?_, ?_⟩
    · funext i; simp [pt1]
    · funext i; simp [pt1]; norm_num
  obtain ⟨γ, -, h₁, h₂⟩ := h (rnPolyfold 1) β hβ _ _ _ _ _ hφ hψ
  have e₁ := h₁ (1 / 2) ⟨by norm_num, le_rfl⟩
  have e₂ := h₂ (1 / 2) ⟨le_rfl, by norm_num⟩
  have := congrFun (e₁.symm.trans e₂) 0
  simp [pt1] at this

theorem not_B : ¬ B := fun h => not_ClaimBLit h.2.1

/-- Hence `A ⇏ B` (`A` holds). -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B ⇒ A` only ex falso. -/
theorem B_to_A : B → A := fun h => (not_B h).elim

/-! ### Against the intended reading: the first two conjuncts of `BIntended` from `A` -/

/-- **(b), corrected, from `A`**: for an admissible `β` (constant `= 1` near `1/2`) the map equal
to `φ ∘ β` on `s ≤ 1/2` and to `ψ ∘ (β − 1)` on `s > 1/2` is sc-smooth by locality
(`isScSmoothMap_of_eventuallyEq`, `isScSmoothMap_reparam` from `A`). -/
theorem A_to_ClaimBInt (hA : A) : ClaimBInt := by
  obtain ⟨hloc, hpt, -, -, -, -, -, -, -, -, -, hrep, -⟩ := hA
  refine ⟨⟨fun s => Real.smoothTransition (3 * s) + Real.smoothTransition (3 * s - 2), ?_⟩, ?_⟩
  · -- `β(s) = κ(3s) + κ(3s − 2)`
    have hκc : Continuous κ := Real.smoothTransition.continuous
    refine ⟨⟨(Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)).add
      (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)),
      ?_, ?_, ?_⟩, ?_, ?_⟩
    · -- `β([0, 1/2]) = [0, 1]`
      have heq : EqOn (fun s => κ (3 * s) + κ (3 * s - 2)) (fun s => κ (3 * s)) (Icc 0 (1 / 2)) :=
        fun s hs => by
          simp only [Real.smoothTransition.zero_of_nonpos (by linarith [hs.2] : 3 * s - 2 ≤ 0),
            add_zero]
      rw [heq.image_eq]
      apply Subset.antisymm
      · rintro _ ⟨s, -, rfl⟩
        exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
      · intro y hy
        have hcont : ContinuousOn (fun s => κ (3 * s)) (Icc 0 (1 / 3)) :=
          (hκc.comp (continuous_const.mul continuous_id)).continuousOn
        have hivt := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 3) hcont
        have h0 : κ (3 * 0) = 0 := by simp
        have h1 : κ (3 * (1 / 3)) = 1 := by norm_num
        rw [h0, h1] at hivt
        obtain ⟨s, hs, hs'⟩ := hivt hy
        exact ⟨s, ⟨hs.1, by linarith [hs.2]⟩, hs'⟩
    · -- `β([1/2, 1]) = [1, 2]`
      have heq : EqOn (fun s => κ (3 * s) + κ (3 * s - 2)) (fun s => 1 + κ (3 * s - 2))
          (Icc (1 / 2) 1) := fun s hs => by
        simp only [Real.smoothTransition.one_of_one_le (by linarith [hs.1] : 1 ≤ 3 * s)]
      rw [heq.image_eq]
      apply Subset.antisymm
      · rintro _ ⟨s, -, rfl⟩
        exact ⟨by linarith [Real.smoothTransition.nonneg (3 * s - 2)],
          by linarith [Real.smoothTransition.le_one (3 * s - 2)]⟩
      · intro y hy
        have hcont : ContinuousOn (fun s => 1 + κ (3 * s - 2)) (Icc (2 / 3) 1) :=
          (continuous_const.add (hκc.comp ((continuous_const.mul continuous_id).sub
            continuous_const))).continuousOn
        have hivt := intermediate_value_Icc (by norm_num : (2 / 3 : ℝ) ≤ 1) hcont
        have h0 : 1 + κ (3 * (2 / 3) - 2) = 1 := by norm_num
        have h1 : 1 + κ (3 * 1 - 2) = 2 := by norm_num
        rw [h0, h1] at hivt
        obtain ⟨s, hs, hs'⟩ := hivt hy
        exact ⟨s, ⟨by linarith [hs.1], hs.2⟩, hs'⟩
    · -- constant near `1/2`
      have hmem : Ioo (1 / 3 : ℝ) (2 / 3) ∈ 𝓝 (1 / 2 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
      filter_upwards [hmem] with s hs
      rw [Real.smoothTransition.one_of_one_le (by linarith [hs.1] : 1 ≤ 3 * s),
        Real.smoothTransition.zero_of_nonpos (by linarith [hs.2] : 3 * s - 2 ≤ 0),
        Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 3 * (1 / 2)),
        Real.smoothTransition.zero_of_nonpos (by norm_num : 3 * (1 / 2 : ℝ) - 2 ≤ 0)]
    · show κ (3 * 0) + κ (3 * 0 - 2) = 0
      rw [Real.smoothTransition.zero_of_nonpos (by norm_num),
        Real.smoothTransition.zero_of_nonpos (by norm_num)]
      norm_num
    · show κ (3 * 1) + κ (3 * 1 - 2) = 2
      rw [Real.smoothTransition.one_of_one_le (by norm_num),
        Real.smoothTransition.one_of_one_le (by norm_num)]
      norm_num
  · intro X _ _ _ PX β hβ φ ψ x y z hφ hψ
    obtain ⟨⟨hβs, hβ₁, hβ₂, hβc⟩, hβ0, hβ1⟩ := hβ
    -- `β(1/2) = 1`
    have hb : β (1 / 2) = 1 := by
      have h1 : β (1 / 2) ∈ Icc (0 : ℝ) 1 := hβ₁ ▸ mem_image_of_mem β ⟨by norm_num, le_rfl⟩
      have h2 : β (1 / 2) ∈ Icc (1 : ℝ) 2 := hβ₂ ▸ mem_image_of_mem β ⟨le_rfl, by norm_num⟩
      exact le_antisymm h1.2 h2.1
    have hy : φ (pt1 1) = ψ (pt1 0) := hφ.2.2.trans hψ.2.1.symm
    set γ : (Fin 1 → ℝ) → X := fun s =>
      if s 0 ≤ 1 / 2 then φ (pt1 (β (s 0))) else ψ (pt1 (β (s 0) - 1)) with hγdef
    have hg₁ : (rnPolyfold 1).IsScSmoothMap PX fun s => φ (pt1 (β (s 0))) := hrep hφ.1 hβs
    have hg₂ : (rnPolyfold 1).IsScSmoothMap PX fun s => ψ (pt1 (β (s 0) - 1)) :=
      @hrep X _ _ _ PX ψ hψ.1 (fun t => β t - 1) (hβs.sub contDiff_const)
    obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hβc
    have hcont : Continuous fun s : Fin 1 → ℝ => s 0 := continuous_apply 0
    -- near `s = 1/2` both pieces are `φ(1) = ψ(0)`
    have hmid : ∀ s : Fin 1 → ℝ, dist (s 0) (1 / 2) < ε →
        φ (pt1 (β (s 0))) = ψ (pt1 (β (s 0) - 1)) := fun s hs => by
      rw [hεb hs, hb, sub_self]; exact hy
    have hγs : (rnPolyfold 1).IsScSmoothMap PX γ := by
      refine hloc fun s => ?_
      rcases le_or_gt (s 0) (1 / 2) with h | h
      · refine ⟨_, hg₁, ?_⟩
        filter_upwards [(isOpen_lt hcont continuous_const).mem_nhds
          (show s 0 < 1 / 2 + ε by linarith)] with p hp
        change p 0 < 1 / 2 + ε at hp
        simp only [hγdef]
        split_ifs with hp'
        · rfl
        · exact (hmid p (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [not_le.1 hp'])).symm
      · refine ⟨_, hg₂, ?_⟩
        filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds h] with p hp
        change 1 / 2 < p 0 at hp
        simp only [hγdef, if_neg (not_le.2 hp)]
    refine ⟨γ, ⟨hγs, ?_, ?_⟩, ?_, ?_⟩
    · simp only [hγdef, hpt, if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2), hβ0]; exact hφ.2.1
    · simp only [hγdef, hpt, if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2), hβ1]
      norm_num; exact hψ.2.2
    · intro s hs
      simp only [hγdef, hpt, if_pos hs.2]
    · intro s hs
      simp only [hγdef, hpt]
      split_ifs with h
      · have hs' : s = 1 / 2 := le_antisymm h hs.1
        subst hs'
        rw [hb, sub_self]; exact hy
      · rfl

/-- **(a) from `A`**: in an open sc-smoothly contractible `U ∋ x` (contraction `H` to `p`), the
paths `t ↦ H(κ(t), x)` (from `x` to `p`) and `t ↦ H(κ(1 − t), y)` (from `p` to `y`) are
sc-smooth with values in `U`, and their `concatPath` (from `A`) is a path in `U` from `x` to
`y`. -/
theorem A_to_ClaimA (hA : A) : ClaimA := by
  obtain ⟨-, hpt, hpt1c, -, hle, hgt, hcat, hcat0, hcat1, -, -, -, -⟩ := hA
  intro X _ _ _ PX _ U x y hUo hU hxU hxs hyU hys
  obtain ⟨H, hHs, hHU, hH0, p, hpU, hH1⟩ := hU
  have hκI : ∀ t, pt1 (κ t) ∈ Icc (0 : Fin 1 → ℝ) 1 := fun t =>
    pt1_mem_Icc ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- `t ↦ H(κ(σ(t)), u)` is sc-smooth for `u ∈ U` smooth
  have hpath : ∀ {u : X}, u ∈ U → u ∈ PX.smoothSet → ∀ {σ : ℝ → ℝ}, ContDiff ℝ ∞ σ →
      (rnPolyfold 1).IsScSmoothMap PX fun t => H (pt1 (κ (σ (t 0))), u) := by
    intro u hu hus σ hσ
    have hpair : (rnPolyfold 1).IsScSmoothOn ((rnPolyfold 1).prod PX)
        (fun t : Fin 1 → ℝ => (pt1 (κ (σ (t 0))), u)) univ :=
      MPolyfold.IsScSmoothOn.prodMk
        (isScSmoothMap_rn_rn_of_contDiff (hpt1c (Real.smoothTransition.contDiff.comp hσ)))
        (isScSmoothMap_const_of_mem_smoothSet hus)
    exact MPolyfold.IsScSmoothOn.comp hHs hpair fun t _ => ⟨mem_univ _, hu⟩
  set γ₁ : (Fin 1 → ℝ) → X := fun t => H (pt1 (κ (t 0)), x) with hγ₁
  set γ₂ : (Fin 1 → ℝ) → X := fun t => H (pt1 (κ (1 - t 0)), y) with hγ₂
  have hγ₁s : (rnPolyfold 1).IsScSmoothMap PX γ₁ := hpath hxU hxs contDiff_id
  have hγ₂s : (rnPolyfold 1).IsScSmoothMap PX γ₂ :=
    hpath hyU hys (σ := fun t => 1 - t) (contDiff_const.sub contDiff_id)
  have e10 : γ₁ (pt1 0) = x := by
    simp only [hγ₁, hpt, Real.smoothTransition.zero]; exact hH0 x hxU
  have e11 : γ₁ (pt1 1) = p := by
    simp only [hγ₁, hpt, Real.smoothTransition.one]; exact hH1 x hxU
  have e20 : γ₂ (pt1 0) = p := by
    simp only [hγ₂, hpt, sub_zero, Real.smoothTransition.one]; exact hH1 y hyU
  have e21 : γ₂ (pt1 1) = y := by
    simp only [hγ₂, hpt, sub_self, Real.smoothTransition.zero]; exact hH0 y hyU
  refine ⟨concatPath γ₁ γ₂, ⟨hcat hγ₁s hγ₂s (e11.trans e20.symm), hcat0.trans e10,
    hcat1.trans e21⟩, fun q _ => ?_⟩
  rcases le_or_gt (q 0) (1 / 2) with h | h
  · rw [hle h]; exact hHU _ (hκI _) x hxU
  · rw [hgt h]; exact hHU _ (hκI _) y hyU

/-- The first two conjuncts of `BIntended` from `A`; the third, `ClaimC`, is not in `A`. -/
theorem A_to_BIntended_ab (hA : A) : ClaimA ∧ ClaimBInt := ⟨A_to_ClaimA hA, A_to_ClaimBInt hA⟩

#rt_check RoundTrip.V6_49.B_to_A [Polyfold.MPolyfold.isScSmoothMap_of_eventuallyEq,
  Polyfold.pt1_apply, Polyfold.contDiff_pt1_comp, Polyfold.exists_nhds_scPath,
  Polyfold.concatPath_of_le, Polyfold.concatPath_of_gt, Polyfold.isScSmoothMap_concatPath,
  Polyfold.concatPath_zero, Polyfold.concatPath_one, Polyfold.concatPath_half₁,
  Polyfold.concatPath_half₂, Polyfold.isScSmoothMap_reparam, Polyfold.HasLocalPropagation.eq_trans]
#rt_overlap RoundTrip.V6_49.B_to_A [Polyfold.MPolyfold.isScSmoothMap_of_eventuallyEq,
  Polyfold.pt1_apply, Polyfold.contDiff_pt1_comp, Polyfold.exists_nhds_scPath,
  Polyfold.concatPath_of_le, Polyfold.concatPath_of_gt, Polyfold.isScSmoothMap_concatPath,
  Polyfold.concatPath_zero, Polyfold.concatPath_one, Polyfold.concatPath_half₁,
  Polyfold.concatPath_half₂, Polyfold.isScSmoothMap_reparam, Polyfold.HasLocalPropagation.eq_trans]
#rt_check RoundTrip.V6_49.not_B [Polyfold.MPolyfold.isScSmoothMap_of_eventuallyEq,
  Polyfold.pt1_apply, Polyfold.contDiff_pt1_comp, Polyfold.exists_nhds_scPath,
  Polyfold.concatPath_of_le, Polyfold.concatPath_of_gt, Polyfold.isScSmoothMap_concatPath,
  Polyfold.concatPath_zero, Polyfold.concatPath_one, Polyfold.concatPath_half₁,
  Polyfold.concatPath_half₂, Polyfold.isScSmoothMap_reparam, Polyfold.HasLocalPropagation.eq_trans]
#rt_check RoundTrip.V6_49.A_to_BIntended_ab [Polyfold.MPolyfold.isScSmoothMap_of_eventuallyEq,
  Polyfold.pt1_apply, Polyfold.contDiff_pt1_comp, Polyfold.exists_nhds_scPath,
  Polyfold.concatPath_of_le, Polyfold.concatPath_of_gt, Polyfold.isScSmoothMap_concatPath,
  Polyfold.concatPath_zero, Polyfold.concatPath_one, Polyfold.concatPath_half₁,
  Polyfold.concatPath_half₂, Polyfold.isScSmoothMap_reparam, Polyfold.HasLocalPropagation.eq_trans]

end RoundTrip.V6_49
