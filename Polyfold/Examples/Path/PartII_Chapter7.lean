import Polyfold.Examples.OrbifoldSquareStructure
import Polyfold.Chapter19.BasicRegularity
import Polyfold.Chapter7.ReducedCriterion
import Polyfold.Chapter7.Zhou
import Polyfold.Chapter8.TangentLocal

/-!
# Examples for the Chapter 7 and 8 rows of the path to Theorem 16.6.6

Examples, non-examples and characteristic properties for the rows V7.17 (natural
representations), V7.37 (`T_x`), V7.80 (local unique continuation), V7.84 (Proposition 7.4.2),
V8.2 (tangents of local sc-diffeomorphisms) and V8.19 (strong bundle maps), mostly on the worked
example `X5 = ℤ/5 ⋉ ℂ` and the trivial strong bundle `ℝⁿ × ℝᵏ → ℝⁿ`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold.Examples.Path

open Polyfold Polyfold.Examples.OrbifoldSquare EpGroupoid.Examples TrivialBundle

/-! ### V7.17: the natural representation of `G_x` -/

/-- Row V7.17, Theorem 7.1.13 (p. 293): every natural representation of `G_0` in `ℤ/5 ⋉ ℂ` is
the rotation action `Φ(g)(y) = ζ^g y`. -/
theorem v7_17_X5_Φ_eq (R : X5.NaturalRep 0) (g : X5.Isotropy 0) {y : Fin 2 → ℝ}
    (hy : y ∈ R.U) : R.Φ g y = rot (χ g.val.1) y :=
  action_Φ_eq isScSmoothMap_smul R g hy

/-- Row V7.17, Theorem 7.1.13 (p. 293): in `ℤ/5 ⋉ ℂ` the natural action of `G_0` is faithful:
only `g = 1` is the identity on `U(0)`. -/
theorem v7_17_X5_Φ_faithful (R : X5.NaturalRep 0) {g : X5.Isotropy 0}
    (hg : ∀ y ∈ R.U, R.Φ g y = y) : g = 1 := by
  by_contra hne
  have h2 : g.val.2 = 0 := g.src_val
  have h1 : g.val.1 ≠ 1 := fun h => hne (GroupoidStr.Isotropy.ext (Prod.ext h h2))
  have hN : R.U ∈ 𝓝[≠] (0 : Fin 2 → ℝ) :=
    mem_nhdsWithin_of_mem_nhds (R.isOpen_U.mem_nhds R.mem_U)
  obtain ⟨y, hyU, hy0⟩ := Filter.nonempty_of_mem (inter_mem hN self_mem_nhdsWithin)
  have hstay : rot (χ g.val.1) y = y := (v7_17_X5_Φ_eq R g hyU).symm.trans (hg y hyU)
  exact hy0 ((smul_eq_self_iff h1 y).1 hstay)

/-- Row V7.17, Theorem 7.1.13 (p. 293): inside every open neighbourhood of `0` there is a natural
representation of `G_0 ≅ ℤ/5` (five elements), acting by the rotations `y ↦ ζ^g y`. -/
theorem v7_17_X5_exists_naturalRep {V : Set (Fin 2 → ℝ)} (hV : IsOpen V)
    (h0 : (0 : Fin 2 → ℝ) ∈ V) :
    Nat.card (X5.Isotropy 0) = 5 ∧ ∃ R : X5.NaturalRep 0, R.U ⊆ V ∧
      ∀ g : X5.Isotropy 0, ∀ y ∈ R.U, R.Φ g y = rot (χ g.val.1) y := by
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr isotropyZeroEquiv.toEquiv, Nat.card_eq_fintype_card]
    rfl
  · obtain ⟨R, hR⟩ := X5.theorem_7_1_13 0 hV h0
    exact ⟨R, hR, fun g y hy => v7_17_X5_Φ_eq R g hy⟩

/-- The generator `ζ` of `G_0`, as a morphism `0 → 0` of `ℤ/5 ⋉ ℂ`. -/
def g0 : X5.Isotropy 0 :=
  actionIsotropy isScSmoothMap_smul (Multiplicative.ofAdd (1 : ZMod 5)) (smul_zero5 _)

theorem g0_ne_one : g0 ≠ 1 := fun h => by
  have h1 : (g0.val.1 : G5) = (1 : X5.Isotropy 0).val.1 := congrArg (fun g => g.val.1) h
  exact absurd h1 (by decide)

/-- The open set `{‖y‖ < 1} ∪ {2 < ‖y‖}` of `ℝ²`, which is not connected. -/
def twoPieces : Set (Fin 2 → ℝ) := {y | ‖y‖ < 1} ∪ {y | 2 < ‖y‖}

/-- The section `y ↦ (ζ, y)` on `‖y‖ < 1` and `y ↦ (1, y)` elsewhere. -/
def twistedSection (y : Fin 2 → ℝ) : G5 × (Fin 2 → ℝ) :=
  if ‖y‖ < 1 then (g0.val.1, y) else (1, y)

theorem norm_three : ‖(fun _ : Fin 2 => (3 : ℝ))‖ = 3 := by
  rw [pi_norm_const]
  norm_num

/-- Row V7.17, Theorem 7.1.13 (p. 293), the connectedness of `U`: on the disconnected open set
`{‖y‖ < 1} ∪ {2 < ‖y‖}` two continuous sections of `s` of `ℤ/5 ⋉ ℂ` through the morphism `ζ` at `0`
differ, so `Γ(g, ·)` is not determined by `Γ(g, x) = g` there. -/
theorem v7_17_sections_of_not_isPreconnected :
    IsOpen twoPieces ∧ (0 : Fin 2 → ℝ) ∈ twoPieces ∧ ¬ IsPreconnected twoPieces ∧
      ContinuousOn (fun y => (g0.val.1, y)) twoPieces ∧ ContinuousOn twistedSection twoPieces ∧
      (∀ y ∈ twoPieces, X5.src (g0.val.1, y) = y) ∧
      (∀ y ∈ twoPieces, X5.src (twistedSection y) = y) ∧
      twistedSection 0 = g0.val ∧
      ∃ y ∈ twoPieces, twistedSection y ≠ (g0.val.1, y) := by
  have ho1 : IsOpen {y : Fin 2 → ℝ | ‖y‖ < 1} := isOpen_lt continuous_norm continuous_const
  have ho2 : IsOpen {y : Fin 2 → ℝ | 2 < ‖y‖} := isOpen_lt continuous_const continuous_norm
  have h3 : (fun _ : Fin 2 => (3 : ℝ)) ∈ {y : Fin 2 → ℝ | 2 < ‖y‖} := by
    change 2 < ‖(fun _ : Fin 2 => (3 : ℝ))‖
    rw [norm_three]
    norm_num
  have h0 : (0 : Fin 2 → ℝ) ∈ {y : Fin 2 → ℝ | ‖y‖ < 1} := by
    change ‖(0 : Fin 2 → ℝ)‖ < 1
    rw [norm_zero]
    norm_num
  have hsrc : ∀ y, X5.src (twistedSection y) = y := fun y => by
    unfold twistedSection
    split_ifs <;> rfl
  refine ⟨ho1.union ho2, Or.inl h0, fun h => ?_,
    (continuous_const.prodMk continuous_id).continuousOn, fun y hy => ?_, fun y _ => rfl, fun y _ => hsrc y, ?_, ⟨_, Or.inr h3, ?_⟩⟩
  · obtain ⟨y, -, hy1, hy2⟩ := h _ _ ho1 ho2 subset_rfl ⟨0, Or.inl h0, h0⟩ ⟨_, Or.inr h3, h3⟩
    change ‖y‖ < 1 at hy1
    change 2 < ‖y‖ at hy2
    linarith
  · refine ContinuousAt.continuousWithinAt ?_
    rcases hy with hy | hy
    · have he : (fun z => (g0.val.1, z)) =ᶠ[𝓝 y] twistedSection := by
        filter_upwards [ho1.mem_nhds hy] with z hz
        change ‖z‖ < 1 at hz
        unfold twistedSection
        rw [if_pos hz]
      exact (continuous_const.prodMk continuous_id).continuousAt.congr he
    · have he : (fun z => ((1 : G5), z)) =ᶠ[𝓝 y] twistedSection := by
        filter_upwards [ho2.mem_nhds hy] with z hz
        change 2 < ‖z‖ at hz
        have hz' : ¬ ‖z‖ < 1 := by linarith
        unfold twistedSection
        rw [if_neg hz']
      exact (continuous_const.prodMk continuous_id).continuousAt.congr he
  · have h0' : ‖(0 : Fin 2 → ℝ)‖ < 1 := h0
    unfold twistedSection
    rw [if_pos h0']
    exact Prod.ext rfl g0.src_val.symm
  · have h3' : ¬ ‖(fun _ : Fin 2 => (3 : ℝ))‖ < 1 := by rw [norm_three]; norm_num
    unfold twistedSection
    rw [if_neg h3']
    intro h
    have h1 : (1 : G5) = g0.val.1 := congrArg Prod.fst h
    exact absurd h1 (by decide)

/-! ### V7.37: the subgroup `T_x` -/

/-- Row V7.37, the subgroup `T_x` (p. 310): the generator `ζ` of `G_0 ≅ ℤ/5`, a morphism
`0 → 0`, does not act trivially, so it is not in `T_0`. -/
theorem v7_37_X5_g0_not_mem_trivialSet : X5.tgt g0.val = 0 ∧ g0 ≠ 1 ∧ g0 ∉ X5.trivialSet 0 := by
  refine ⟨g0.tgt_val, g0_ne_one, fun h => g0_ne_one ?_⟩
  have h' : g0 ∈ X5.trivialSubgroup 0 := h
  rw [trivialSubgroup_X5, Subgroup.mem_bot] at h'
  exact h'

/-! ### V7.80 and V7.84: the local unique continuation property -/

/-- Row V7.80, Definition 7.2.18 (p. 321): `ℤ/5 ⋉ ℂ` has the local unique continuation
property. -/
theorem v7_80_isLUC_X5 : X5.IsLUC := X5.isLUC_of_isEffective isEffective_X5

/-- Row V7.84, Proposition 7.4.2 and Remark 7.4.3 (pp. 328–329): every natural representation of
`ℤ/5 ⋉ ℂ`, of any size, has the property of Definition 7.4.1. -/
theorem v7_84_X5_hasLUC (x : Fin 2 → ℝ) (R : X5.NaturalRep x) : R.HasLUC :=
  (X5.isLUC_iff_forall_naturalRep.1 v7_80_isLUC_X5) x R

/-- Row V7.84, Proposition 7.4.2 (p. 328): in the ep-groupoid of Remark 7.2.19 some natural
representation does not have the property of Definition 7.4.1. -/
theorem v7_84_jumping_exists_not_hasLUC :
    ∃ x, ∃ R : JumpingRetract.X.NaturalRep x, ¬ R.HasLUC := by
  by_contra h
  push Not at h
  exact JumpingRetract.not_isLUC (JumpingRetract.X.isLUC_iff_forall_naturalRep.2 h)

/-! ### V8.2: tangents of local sc-diffeomorphisms -/

/-- Row V8.2, tangents of local sc-diffeomorphisms (pp. 358–364): the tangent of the source map
`s` of `ℤ/5 ⋉ ℂ`, a local sc-diffeomorphism, is a surjective local sc-diffeomorphism
`T𝐗 → TX`. -/
theorem v8_2_X5_tangent_src :
    X5.PMor.tangentPolyfold.IsLocalScDiffeo X5.PObj.tangentPolyfold
        (MPolyfold.tangentMap X5.isLocalScDiffeo_src.isScSmoothMap) ∧
      Surjective (MPolyfold.tangentMap X5.isLocalScDiffeo_src.isScSmoothMap) :=
  ⟨X5.isLocalScDiffeo_src.tangentMap,
    X5.isLocalScDiffeo_src.surjective_tangentMap fun y => ⟨(1, y), rfl⟩⟩

/-! ### V8.19: strong bundle maps -/

variable {n n' k k' : ℕ}

/-- Row V8.19, strong bundle maps (pp. 373–396): a strong bundle map from `ℝⁿ × ℝᵏ → ℝⁿ` to
`ℝⁿ' × ℝᵏ' → ℝⁿ'` sends the zero of the fibre over `x` to the zero of the fibre over
`f(x)`. -/
theorem v8_19_map_zero {f : (Fin n → ℝ) → (Fin n' → ℝ)}
    {Φ : (Fin n → ℝ) × (Fin k → ℝ) → (Fin n' → ℝ) × (Fin k' → ℝ)}
    (h : (bundle n k).IsStrongBundleMap (bundle n' k') f Φ) (x : Fin n → ℝ) :
    Φ (x, 0) = (f x, 0) := by
  have h0 := congrArg Subtype.val ((h.fiberMap x).map_zero)
  rw [h.fiberMap_apply] at h0
  exact h0

/-- Row V8.19, strong bundle maps (pp. 373–396): for `e ≠ 0` the fibre translation
`(x, v) ↦ (x, v + e)` of `ℝⁿ × ℝᵏ`, which covers the identity, is not a strong bundle map. -/
theorem v8_19_not_isStrongBundleMap_shift {e : Fin k → ℝ} (he : e ≠ 0) :
    ¬ (bundle n k).IsStrongBundleMap (bundle n k) id
      (fun p : (Fin n → ℝ) × (Fin k → ℝ) => (p.1, p.2 + e)) := fun h => by
  have h0 := congrArg Prod.snd (v8_19_map_zero h (0 : Fin n → ℝ))
  simp only [zero_add] at h0
  exact he h0

end Polyfold.Examples.Path
