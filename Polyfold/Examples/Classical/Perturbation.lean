import Polyfold.Examples.Classical.Structure
import Polyfold.Chapter16.IndexZeroNormOneWitness

/-!
# The classical reduction: the auxiliary norm and the multisection of constant branches

Setting for the comparison of Theorem 16.6.6, 2021 p. 739 (index `0`) with the classical count
of a proper equivariant map `φ : ℝⁿ → ℝⁿ`, `φ (g • x) = σ g (φ x)`, in finite dimensions.

## What is formalized (namespace `Polyfold.Examples.Classical`)

* `gNorm σ w = ∑_g ‖σ g w‖` (sup norm of `ℝⁿ`): `gNorm_smul_invariant`, `norm_le_gNorm`.
* `NG σ`, `isAuxNorm_NG`: the auxiliary norm `N(x, w) = gNorm σ w`, invariant under the
  morphisms (Definition 12.2.1); `nG σ`, `isAuxNorm_nG`: the auxiliary norm on the strong
  polyfold bundle (Definition 16.3.9).
* `controlsCompactness_nG` (for a proper `φ`): `N(f(x)) ≤ 1` forces `‖φ x‖ ≤ 1`;
  `hasCompactSolutionSet` (`φ⁻¹{0}` is compact).
* `branchG σ c g`, `ΛG σ c`: the multisection with the constant branches `x ↦ (x, σ g c)`,
  `g ∈ G`, weight `1/#G` each; `ΛG_fSec`: `Λ(f(x)) = #{g | φ x = σ g c} / #G`;
  `isWFunctor_ΛG`, `isScPlusMultisection_ΛG` (Definition 13.2.1).
* **`isInGeneralPosition_ΛG`** (Definition 15.3.5), for a regular value `c` of `φ`: at a
  solution `φ x = σ g c` the linearization `Dφ(x)` is onto, since
  `Dφ(g • y) ∘ (g •) = σ g ∘ Dφ(y)` with `y = g⁻¹ • x`, `φ y = c`.
* `tG σ c`, `isControlledBy_tG` (for `gNorm σ c ≤ 1`), `isInGeneralPositionWith_tG`: the
  sc⁺-multisection `λ` of the strong polyfold bundle is controlled by `(n, Z)`, and `(f, λ)` is
  in general position.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure StrongBundleEquivalenceExamples
  StrongBundleLocalizationExamples SBLocalization StrongRetr Linearization15

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]

variable (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))

/-! ### The averaged norm -/

/-- `gNorm σ w = ∑_g ‖σ g w‖` (sup norm of `ℝⁿ`), a `σ`-invariant norm. -/
def gNorm (w : Fin n → ℝ) : ℝ := ∑ g : G, ‖σ g w‖

theorem continuous_gNorm : Continuous (gNorm σ) :=
  continuous_finsetSum _ fun g _ => continuous_norm.comp (σ g).continuous

theorem gNorm_nonneg (w : Fin n → ℝ) : 0 ≤ gNorm σ w :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- **`gNorm` is `σ`-invariant.** -/
theorem gNorm_smul_invariant (h : G) (w : Fin n → ℝ) : gNorm σ (σ h w) = gNorm σ w := by
  unfold gNorm
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => ?_
  rw [Equiv.coe_mulRight, map_mul]; rfl

/-- **`‖w‖ ≤ gNorm σ w`.** -/
theorem norm_le_gNorm (w : Fin n → ℝ) : ‖w‖ ≤ gNorm σ w := by
  have h1 : ‖σ 1 w‖ = ‖w‖ := by rw [map_one]; rfl
  rw [← h1]
  exact Finset.single_le_sum (f := fun g => ‖σ g w‖) (fun g _ => norm_nonneg _)
    (Finset.mem_univ 1)

theorem gNorm_zero : gNorm σ 0 = 0 := by
  simp [gNorm]

theorem gNorm_eq_zero_iff {w : Fin n → ℝ} : gNorm σ w = 0 ↔ w = 0 := by
  refine ⟨fun h => norm_eq_zero.1 (le_antisymm ((norm_le_gNorm σ w).trans h.le)
    (norm_nonneg _)), fun h => h ▸ gNorm_zero σ⟩

theorem gNorm_smul (t : ℝ) (w : Fin n → ℝ) : gNorm σ (t • w) = |t| * gNorm σ w := by
  simp only [gNorm, map_smul, norm_smul, Real.norm_eq_abs, ← Finset.mul_sum]

theorem gNorm_add_le (v w : Fin n → ℝ) : gNorm σ (v + w) ≤ gNorm σ v + gNorm σ w := by
  unfold gNorm
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun g _ => by rw [map_add]; exact norm_add_le _ _

/-! ### The auxiliary norm -/

/-- **The auxiliary norm** `N(x, w) = gNorm σ w`. -/
def NG : (bundle n n).One → ℝ := fun w => gNorm σ ((bundle n n).oneVal w).2

theorem NG_oneMk (w : (Fin n → ℝ) × (Fin n → ℝ)) (hw : w ∈ (bundle n n).oneSet) :
    NG σ ((bundle n n).oneMk w hw) = gNorm σ w.2 := by
  unfold NG
  rw [oneVal_oneMk]

/-- **`N` is an auxiliary norm** (Definition 5.1.1). -/
theorem isAuxNorm_NG_bundle : (bundle n n).IsAuxNorm (NG σ) where
  continuous := ((continuous_gNorm σ).comp continuous_snd).comp (bundle n n).continuous_oneVal
  fiber x :=
    { eq_zero := fun v hv => by
        have h0 : ((v : proj n n ⁻¹' {x}) : (Fin n → ℝ) × (Fin n → ℝ)).2 = 0 :=
          (gNorm_eq_zero_iff σ).1 hv
        refine Subtype.ext ((fibEquiv x).injective ?_)
        change ((v : proj n n ⁻¹' {x}) : (Fin n → ℝ) × (Fin n → ℝ)).2 =
          ((0 : proj n n ⁻¹' {x}) : (Fin n → ℝ) × (Fin n → ℝ)).2
        rw [h0, snd_zero]
      smul := fun t v => by
        change gNorm σ (((t • (v : proj n n ⁻¹' {x}) : proj n n ⁻¹' {x}) :
          (Fin n → ℝ) × (Fin n → ℝ)).2) = |t| * gNorm σ (((v : proj n n ⁻¹' {x}) :
            (Fin n → ℝ) × (Fin n → ℝ)).2)
        rw [snd_smul, gNorm_smul]
      add_le := fun v w => by
        change gNorm σ ((((v : proj n n ⁻¹' {x}) + (w : proj n n ⁻¹' {x}) : proj n n ⁻¹' {x}) :
          (Fin n → ℝ) × (Fin n → ℝ)).2) ≤ gNorm σ (((v : proj n n ⁻¹' {x}) :
            (Fin n → ℝ) × (Fin n → ℝ)).2) + gNorm σ (((w : proj n n ⁻¹' {x}) :
              (Fin n → ℝ) × (Fin n → ℝ)).2)
        rw [snd_add]; exact gNorm_add_le σ _ _
      complete := fun u hu => by
        set a : ℕ → (Fin n → ℝ) := fun j => ((u j : proj n n ⁻¹' {x}) :
          (Fin n → ℝ) × (Fin n → ℝ)).2 with ha
        have hsub : ∀ i j, NG σ ((bundle n n).toOne (u i - u j)) = gNorm σ (a i - a j) :=
          fun i j => by
            change gNorm σ ((((u i : proj n n ⁻¹' {x}) - (u j : proj n n ⁻¹' {x}) :
              proj n n ⁻¹' {x}) : (Fin n → ℝ) × (Fin n → ℝ)).2) = _
            rw [snd_sub]
        have hc : CauchySeq a := by
          refine Metric.cauchySeq_iff.2 fun ε hε => ?_
          obtain ⟨N₀, hN₀⟩ := hu ε hε
          exact ⟨N₀, fun i hi j hj => by
            rw [dist_eq_norm]
            exact (norm_le_gNorm σ _).trans_lt (by rw [← hsub]; exact hN₀ i hi j hj)⟩
        obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hc
        let v₀ : proj n n ⁻¹' {x} := ⟨(x, b), rfl⟩
        have hv₀ : v₀ ∈ (bundle n n).oneFiber x := by
          change ((v₀ : proj n n ⁻¹' {x}) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ (bundle n n).oneSet
          rw [oneSet_eq]; exact mem_univ _
        refine ⟨⟨v₀, hv₀⟩, ?_⟩
        have e : ∀ j, NG σ ((bundle n n).toOne (u j - ⟨v₀, hv₀⟩)) = gNorm σ (a j - b) :=
          fun j => by
            change gNorm σ ((((u j : proj n n ⁻¹' {x}) - v₀ : proj n n ⁻¹' {x}) :
              (Fin n → ℝ) × (Fin n → ℝ)).2) = _
            rw [snd_sub]
        simp only [e]
        have h1 : Tendsto (fun j => a j - b) atTop (𝓝 0) := tendsto_sub_nhds_zero_iff.2 hb
        have h2 := ((continuous_gNorm σ).tendsto 0).comp h1
        rw [gNorm_zero] at h2
        exact h2 }
  tendsto_zeroOne := fun w x hP hN => by
    refine TopologicalSpace.tendsto_nhds_generateFrom_iff.2 ?_
    rintro s ⟨c, ⟨a, rfl⟩, W, hW, rfl⟩ ⟨-, hz⟩
    have hlift : ∀ y : (Fin n → ℝ) × (Fin n → ℝ),
        (chart (k := n) a).liftOne y = (y.1 - a, y.2) :=
      fun y => Prod.ext rfl (invFun_toBase_one _)
    have hz' : ((x - a, 0) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ W := by
      have := hz
      change (chart (k := n) a).liftOne (fiberZero (proj n n) x) ∈ W at this
      rwa [hlift] at this
    have h2 : Tendsto (fun j => ((bundle n n).oneVal (w j)).2) atTop (𝓝 0) :=
      squeeze_zero_norm (fun j => norm_le_gNorm σ _) hN
    have h1 : Tendsto (fun j => (((bundle n n).oneVal (w j)).1 - a, ((bundle n n).oneVal (w j)).2))
        atTop (𝓝 ((x - a, 0) : (Fin n → ℝ) × (Fin n → ℝ))) :=
      (hP.sub_const a).prodMk_nhds h2
    filter_upwards [h1 (hW.mem_nhds hz')] with j hj
    refine ⟨mem_univ _, ?_⟩
    change (chart (k := n) a).liftOne ((bundle n n).oneVal (w j)) ∈ W
    rw [hlift]; exact hj

/-- **`N` is an auxiliary norm of the bundle over `G ⋉ ℝⁿ`** (Definition 12.2.1): the
morphisms act on the fibres by `σ g`, and `gNorm σ` is `σ`-invariant. -/
theorem isAuxNorm_NG : (AG σ).E.IsAuxNorm (NG σ) :=
  ⟨isAuxNorm_NG_bundle σ, fun h k φ _ e => by
    have e' : (bundle n n).oneVal h = actW σ φ.1 ((bundle n n).oneVal k) := e
    unfold NG
    rw [e', actW_apply]
    exact gNorm_smul_invariant σ φ.1 _⟩

/-- **The auxiliary norm `n` of the strong polyfold bundle** (Definition 16.3.9). -/
def nG : (AG σ).E.toEpGroupoid.OrbitSpace → ℝ := (clStructure σ).descend (NG σ)

theorem isAuxNorm_nG : (clBundle σ).IsAuxNorm (nG σ) := isAuxNorm_descend rfl (isAuxNorm_NG σ)

theorem normOf_nG : (clStructure σ).normOf (nG σ) = NG σ :=
  (clStructure σ).normOf_descend (isAuxNorm_NG σ).isOneInvariant

/-! ### `(n, Z)` controls compactness -/

variable {σ}

/-- **`(N, ℝⁿ)` controls the compactness of `f`** (Definition 15.3.1) for a proper `φ`:
`N(f(x)) ≤ 1` gives `‖φ x‖ ≤ 1`, and `φ⁻¹(closedBall 0 1)` is compact. -/
theorem controlsCompactness_fSec_univ {φ : (Fin n → ℝ) → (Fin n → ℝ)}
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) :
    ControlsCompactness (AG σ) (fSec φ) (NG σ) univ := by
  refine ⟨isAuxNorm_NG σ, isOpen_univ, GroupoidStr.isSaturated_univ _, subset_univ _, ?_⟩
  let K : Set (Fin n → ℝ) := φ ⁻¹' Metric.closedBall 0 1
  have hK : IsCompact K := hprop _ (isCompact_closedBall 0 1)
  have hsub : {x ∈ (univ : Set (AG σ).Obj) | (AG σ).B.AuxLe (NG σ) (fSec φ x) 1} ⊆
      (K : Set (AG σ).Obj) := by
    rintro (x : Fin n → ℝ) ⟨-, hw, hle⟩
    have hle' : gNorm σ (φ x) ≤ 1 := (NG_oneMk σ _ hw).symm.trans_le hle
    change φ x ∈ Metric.closedBall 0 1
    rw [mem_closedBall_zero_iff]
    exact (norm_le_gNorm σ _).trans hle'
  exact (hK.image (AG σ).X.continuous_π).closure_of_subset (image_mono hsub)

/-- **`(n, Z)` controls the compactness of the section `|x| ↦ |(x, φ x)|`** (Definition
16.6.3, with `U = Z = ℝⁿ/G`), for a proper `φ`. -/
theorem controlsCompactness_nG {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) :
    (clFredholmSection σ hφ heq).1.ControlsCompactness (nG σ)
      (univ : Set (AG σ).X.OrbitSpace) := by
  refine ((clRep σ hφ heq).controlsCompactness_iff (isAuxNorm_nG σ) isOpen_univ).2 ?_
  rw [preimage_univ]
  change ControlsCompactness (AG σ) (fSec φ) ((clStructure σ).normOf (nG σ)) univ
  rw [normOf_nG]
  exact controlsCompactness_fSec_univ hprop

/-- **The solution set is compact**: it is the image of `φ⁻¹{0}`, compact for a proper `φ`. -/
theorem hasCompactSolutionSet {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) :
    (clFredholmSection σ hφ heq).1.HasCompactSolutionSet := by
  refine (clRep σ hφ heq).hasCompactSolutionSet_iff.2 ?_
  have h : solutionSet (AG σ).P (fSec φ) = φ ⁻¹' {0} := by
    ext x
    exact isZeroAt_graphSection_iff
  change IsCompact ((AG σ).X.π '' solutionSet (AG σ).P (fSec φ))
  rw [h]
  exact (hprop _ isCompact_singleton).image (AG σ).X.continuous_π

/-! ### The multisection of constant branches -/

variable (σ)

/-- The constant branch `s_g(x) = (x, σ g c)`. -/
def branchG (c : Fin n → ℝ) (g : G) : (AG σ).Obj → (AG σ).W :=
  graphSection fun _ => σ g c

theorem branchG_apply (c : Fin n → ℝ) (g : G) (x : Fin n → ℝ) :
    branchG σ c g x = (x, σ g c) := rfl

theorem isScPlusSection_branchG (c : Fin n → ℝ) (g : G) :
    (AG σ).B.IsScPlusSection (branchG σ c g) :=
  isScPlusSection_graphSection contDiff_const

/-- The morphisms permute the branches: `h · s_g(x) = s_{hg}(h • x)`. -/
theorem actW_branchG (c : Fin n → ℝ) (h g : G) (x : Fin n → ℝ) :
    actW σ h (branchG σ c g x) = branchG σ c (h * g) (h • x) := by
  rw [branchG_apply, branchG_apply, actW_apply, map_mul]; rfl

open scoped _root_.Classical in
/-- **The multisection `Λ`** with the constant branches `s_g`, `g ∈ G`, of weight `1/#G`
each. -/
def ΛG (c : Fin n → ℝ) : (AG σ).W → ℚ≥0 := fun w =>
  ∑ g : G, if w = branchG σ c g ((AG σ).P w) then (1 / Fintype.card G : ℚ≥0) else 0

theorem one_div_card_pos : (0 : ℚ≥0) < 1 / Fintype.card G :=
  one_div_pos.2 (Nat.cast_pos.2 Fintype.card_pos)

theorem ΛG_pos_iff (c : Fin n → ℝ) (w : (AG σ).W) :
    0 < ΛG σ c w ↔ ∃ g : G, w = branchG σ c g ((AG σ).P w) := by
  classical
  unfold ΛG
  rw [Finset.sum_pos_iff]
  constructor
  · rintro ⟨g, -, hg⟩
    by_cases h : w = branchG σ c g ((AG σ).P w)
    · exact ⟨g, h⟩
    · rw [if_neg h] at hg
      exact absurd hg (lt_irrefl _)
  · rintro ⟨g, hg⟩
    refine ⟨g, Finset.mem_univ _, ?_⟩
    rw [if_pos hg]
    exact one_div_card_pos (G := G)

/-- `f(x) = s_g(x)` iff `φ x = σ g c`. -/
theorem fSec_eq_branchG_iff {φ : (Fin n → ℝ) → (Fin n → ℝ)} (c : Fin n → ℝ) (g : G)
    (x : Fin n → ℝ) : fSec φ x = branchG σ c g x ↔ φ x = σ g c :=
  ⟨fun h => congrArg Prod.snd h, fun h => Prod.ext rfl h⟩

/-- **`Λ(f(x)) = #{g | φ x = σ g c} / #G`.** -/
theorem ΛG_fSec (φ : (Fin n → ℝ) → (Fin n → ℝ)) (c x : Fin n → ℝ) :
    ΛG σ c (fSec φ x) =
      ((Finset.univ.filter fun g : G => φ x = σ g c).card : ℚ≥0) / Fintype.card G := by
  classical
  unfold ΛG
  have h : ∀ g : G, (if fSec φ x = branchG σ c g ((AG σ).P (fSec φ x))
      then (1 / Fintype.card G : ℚ≥0) else 0) =
      if φ x = σ g c then (1 / Fintype.card G : ℚ≥0) else 0 := fun g => by
    by_cases hg : φ x = σ g c
    · rw [if_pos hg]; exact if_pos ((fSec_eq_branchG_iff σ c g x).2 hg)
    · rw [if_neg hg]; exact if_neg fun h => hg ((fSec_eq_branchG_iff σ c g x).1 h)
  refine (Finset.sum_congr rfl fun g _ => h g).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- `Λ(f(x)) > 0` iff `φ x = σ g c` for some `g`. -/
theorem ΛG_fSec_pos_iff {φ : (Fin n → ℝ) → (Fin n → ℝ)} (c x : Fin n → ℝ) :
    0 < ΛG σ c (fSec φ x) ↔ ∃ g : G, φ x = σ g c :=
  (ΛG_pos_iff σ c _).trans (exists_congr fun g => fSec_eq_branchG_iff σ c g x)

theorem eq_branchG_actW_iff (c : Fin n → ℝ) (h g : G) (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    actW σ h w = branchG σ c g (h • w.1) ↔ w = branchG σ c (h⁻¹ * g) w.1 := by
  constructor
  · intro e
    have e1 := congrArg (actW σ h⁻¹) e
    rw [actW_inv_actW, actW_branchG, inv_smul_smul] at e1
    exact e1
  · intro e
    conv_lhs => rw [e]
    rw [actW_branchG, mul_inv_cancel_left]

/-- **`Λ` is a functor** `W → ℚ⁺` (Definition 13.2.1): the morphisms permute the branches. -/
theorem isWFunctor_ΛG (c : Fin n → ℝ) : IsWFunctor (AG σ) (ΛG σ c) := by
  classical
  rintro ⟨⟨⟨h, o⟩, w⟩, hq⟩
  change ΛG σ c (actW σ h w) = ΛG σ c w
  unfold ΛG
  refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g => ?_
  exact if_congr (eq_branchG_actW_iff σ c h g w) rfl rfl

/-- The branches `s_g`, indexed by `Fin #G`, with weight `1/#G`, are a local representation of
`Λ` on `ℝⁿ`. -/
theorem isLocalRepOn_ΛG (c : Fin n → ℝ) :
    IsLocalRepOn (AG σ) (ΛG σ c) univ (k := Fintype.card G)
      (fun i => branchG σ c ((Fintype.equivFin G).symm i))
      (fun _ => (1 / Fintype.card G : ℚ≥0)) := by
  classical
  refine ⟨fun _ => one_div_card_pos (G := G),
    fun i => IsScPlusSectionOn.of_isScPlusSection (isScPlusSection_branchG σ c _) isOpen_univ,
    ?_, fun w _ => ?_⟩
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div,
      div_self (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]
  · unfold ΛG
    refine Fintype.sum_equiv (Fintype.equivFin G) _ _ fun g => ?_
    simp only [Equiv.symm_apply_apply]

/-- **`Λ` is an sc⁺-multisection** (Definition 13.2.1). -/
theorem isScPlusMultisection_ΛG (c : Fin n → ℝ) : IsScPlusMultisection (AG σ) (ΛG σ c) :=
  ⟨isWFunctor_ΛG σ c, fun x₀ => hasLocalSectionStructure_of_isLocalRepOn isOpen_univ
    (mem_univ x₀) (isLocalRepOn_ΛG σ c)⟩

/-! ### General position -/

variable {σ}

/-- **Equivariance of the derivative**: `Dφ(g • y) (g • v) = σ g (Dφ(y) v)`. -/
theorem fderiv_smul_apply {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) (g : G) (y v : Fin n → ℝ) :
    fderiv ℝ φ (g • y) (g • v) = σ g (fderiv ℝ φ y v) := by
  have hd : ∀ z, HasFDerivAt φ (fderiv ℝ φ z) z := fun z =>
    ((hφ.differentiable (by simp)) z).hasFDerivAt
  have h1 : HasFDerivAt (φ ∘ rhoL g) ((fderiv ℝ φ (g • y)).comp (rhoL g)) y :=
    (hd (rhoL g y)).comp y (rhoL g).hasFDerivAt
  have h2 : HasFDerivAt ((σ g) ∘ φ) ((σ g).comp (fderiv ℝ φ y)) y :=
    (σ g).hasFDerivAt.comp y (hd y)
  have hfun : φ ∘ rhoL g = (σ g) ∘ φ := funext fun z => heq g z
  rw [hfun] at h1
  have := congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L v) (h1.unique h2)
  exact this

/-- **At a solution `φ x = σ g c` of a regular value `c`, `Dφ(x)` is onto.** -/
theorem surjective_fderiv_of_eq {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) {c : Fin n → ℝ}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x)) {g : G} {x : Fin n → ℝ}
    (hx : φ x = σ g c) : Surjective (fderiv ℝ φ x) := by
  have hy : φ (g⁻¹ • x) = c := by rw [heq, hx, σ_inv_apply]
  intro w
  obtain ⟨u, hu⟩ := hc _ hy (σ g⁻¹ w)
  refine ⟨g • u, ?_⟩
  have h := fderiv_smul_apply hφ heq g (g⁻¹ • x) u
  rw [smul_inv_smul] at h
  rw [h, hu, σ_apply_inv]

/-- `D(φ − const)(x) = Dφ(x)`. -/
theorem surjective_fderiv_sub_const {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    {x : Fin n → ℝ} (hs : Surjective (fderiv ℝ φ x)) (b : Fin n → ℝ) :
    Surjective (fderiv ℝ (φ - fun _ => b) x) := by
  have hd : HasFDerivAt (φ - fun _ => b) (fderiv ℝ φ x) x :=
    ((hφ.differentiable (by simp)) x).hasFDerivAt.sub_const b
  rw [hd.fderiv]
  exact hs

/-- In a chart of `ℝⁿ` (model `C` the whole space) the reduced tangent space is the tangent
space. -/
theorem mem_reducedTangentFiber_of_univ {φ : MChart (AG σ).Obj} (hφ : (AG σ).X.PObj.IsChart φ)
    {x : (AG σ).X.PObj.Level 1} (hx : (AG σ).X.PObj.levelVal 1 x ∈ φ.source) {k : ℕ}
    {V : ScBanach} (T : ScIso φ.model.E ((ScBanach.const (Fin k → ℝ)).prod V))
    (hT : φ.model.C = T 0 ⁻¹' quadrant k V 0) (hC : φ.model.C = univ)
    (α : (AG σ).X.PObj.tangentFiber x) : α ∈ reducedTangentFiber hφ hx T := by
  have h0 : ∀ (v : φ.model.E 0) (i : Fin k), (T 0 v).1 i = 0 := by
    intro v i
    have h1 : ∀ u : φ.model.E 0, 0 ≤ (T 0 u).1 i := fun u => by
      have hu : u ∈ T 0 ⁻¹' quadrant k V 0 := by rw [← hT, hC]; exact mem_univ u
      exact hu i
    have h2 := h1 v
    have h3 := h1 (-v)
    rw [map_neg] at h3
    have h4 : (-(T 0 v)).1 i = -((T 0 v).1 i) := rfl
    rw [h4] at h3
    linarith
  exact Submodule.mem_comap.2 ((mem_minimalSubspaceWith T).2 fun i _ => h0 _ i)

/-- **`(f, Λ)` is in general position** (Definition 15.3.5) for a regular value `c` of `φ`: at
a solution `φ x = σ g c`, in the chart centred at `x`, `(f − s_g)'(x) = Dφ(x)` is onto `ℝⁿ`,
and `ℝⁿ` has no boundary. -/
theorem isInGeneralPosition_ΛG {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) {c : Fin n → ℝ}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x)) :
    IsInGeneralPosition (AG σ) (fSec φ) (ΛG σ c) := by
  classical
  have hf := isScFredholmSectionFunctor_fSec (σ := σ) hφ heq
  refine isInGeneralPosition_iff_exists.2 fun x hpos => ?_
  set x₀ : Fin n → ℝ := (AG σ).X.PObj.levelVal 1 x with hx₀
  let ch : StrongBundleChart (AG σ).X.PObj (AG σ).P := chart (k := n) x₀
  have hch : (AG σ).B.IsChart ch := isChart_chart x₀
  have hx : (AG σ).X.PObj.levelVal 1 x ∈ ch.φ.source := mem_univ _
  obtain ⟨k, V, T, hT⟩ := ch.φ.model.isPartialQuadrant
  refine ⟨ch.φ, ch.isChart, hx, k, V, T, hT, fun L hL => ?_⟩
  have hsurj : Surjective L := by
    let d : LocalLinData (AG σ) (ΛG σ c) x :=
      ⟨univ, isOpen_univ, Fintype.card G, fun i => branchG σ c ((Fintype.equivFin G).symm i),
        fun _ => (1 / Fintype.card G : ℚ≥0), isLocalRepOn_ΛG σ c, ch, hch, subset_univ _, hx⟩
    rw [linearization_eq hf d] at hL
    obtain ⟨i, hi, hLi⟩ := (mem_support_linSumIntr_iff (k := Fintype.card G)
      (s := fun i => branchG σ c ((Fintype.equivFin G).symm i))
      (σ := fun _ => (1 / Fintype.card G : ℚ≥0)) hf.1.1.1
      (fun _ => one_div_card_pos (G := G)) (fun _ z _ => rfl) (subset_univ _) hx L).1 hL
    rw [← hLi]
    refine (surjective_toIntr_subDeriv_iff hf.1.1 (IsScPlusSectionOn.of_isScPlusSection
      (isScPlusSection_branchG σ c _) isOpen_univ) hch (subset_univ _) hx hi.symm).2 ?_
    have hsol : φ x₀ = σ ((Fintype.equivFin G).symm i) c := (congrArg Prod.snd hi).symm
    set z := levelLift ch.φ 1 ((AG σ).X.PObj.levelVal 1 x) with hzdef
    have hz : z = 0 := by
      have h1 : ch.φ.model.E.toBase 1 z = ch.φ ((AG σ).X.PObj.levelVal 1 x) :=
        (AG σ).X.PObj.toBase_levelLift ch.isChart hx ((AG σ).X.PObj.levelVal_mem x)
      have h2 : ch.φ x₀ = (0 : Fin n → ℝ) := sub_self (show Fin n → ℝ from x₀)
      exact h1.trans h2
    have he : ((fun y => ch.principal (fSec φ) y -
        ch.principal (branchG σ c ((Fintype.equivFin G).symm i)) y) ∘ r ch.R) =
        loc (φ - fun _ => σ ((Fintype.equivFin G).symm i) c) x₀ := by
      funext u
      rfl
    intro w _
    obtain ⟨v, hv⟩ := surjective_fderiv_sub_const hφ
      (surjective_fderiv_of_eq hφ heq hc hsol) (σ ((Fintype.equivFin G).symm i) c) w
    refine ⟨v, ⟨v, ?_⟩, ?_⟩
    · rw [hz]
      exact congrArg (fun S : (rnSc n) 0 →L[ℝ] (rnSc n) 0 => S v) (scDeriv_r (k := n) x₀)
    · change scDeriv ch.U ((fun y => ch.principal (fSec φ) y -
        ch.principal (branchG σ c ((Fintype.equivFin G).symm i)) y) ∘ r ch.R) z v = w
      rw [he, hz]
      exact (congrArg (fun S : (rnSc n) 0 →L[ℝ] (rnSc n) 0 => S v)
        (scDeriv_loc (hφ.sub contDiff_const) x₀)).trans hv
  intro w
  obtain ⟨α, hα⟩ := hsurj w
  exact ⟨⟨α, mem_reducedTangentFiber_of_univ ch.isChart hx T hT rfl α⟩, hα⟩

/-! ### The sc⁺-multisection of the strong polyfold bundle -/

variable (σ) in
/-- **The sc⁺-multisection `λ`** of the strong polyfold bundle `|ℝⁿ × ℝⁿ| → ℝⁿ/G`, the class
of `Λ` (Definition 16.5.1). -/
def tG (c : Fin n → ℝ) : ScPlusMultisection (clBundle σ) :=
  ⟦ofFunctor (clStructure σ) rfl (ΛG σ c) (isScPlusMultisection_ΛG σ c)⟧

/-- `N(Λ)(x) ≤ gNorm σ c`. -/
theorem pointwiseNorm_ΛG_le {c : Fin n → ℝ} (hc1 : gNorm σ c ≤ 1) (x : (AG σ).Obj) :
    pointwiseNorm (NG σ) (ΛG σ c) x ≤ 1 := by
  have hmem : ∀ w : (AG σ).W, w ∈ (AG σ).B.oneSet := fun w => by
    have h : (bundle n n).oneSet = univ := oneSet_eq
    exact h ▸ mem_univ w
  refine csSup_le ⟨_, mem_image_of_mem _ (⟨rfl, (ΛG_pos_iff σ c _).2 ⟨1, rfl⟩⟩ :
    branchG σ c 1 x ∈ suppAt (ΛG σ c) x)⟩ ?_
  rintro _ ⟨w, ⟨-, hw⟩, rfl⟩
  obtain ⟨g, hg⟩ := (ΛG_pos_iff σ c w).1 hw
  rw [normW_of_mem (NG σ) (hmem w)]
  refine (NG_oneMk σ w (hmem w)).trans_le ?_
  rw [hg]
  change gNorm σ (σ g c) ≤ 1
  rw [gNorm_smul_invariant]
  exact hc1

/-- **`λ` is controlled by `(n, Z)`** (Definition 16.5.4), for `gNorm σ c ≤ 1`. -/
theorem isControlledBy_tG {c : Fin n → ℝ} (hc1 : gNorm σ c ≤ 1) :
    (tG σ c).IsControlledBy (nG σ) (univ : Set (AG σ).X.OrbitSpace) := by
  refine ⟨fun z => ?_, subset_univ _⟩
  obtain ⟨x, rfl⟩ := (clStructure σ).surjective_γπ z
  set b := ofFunctor (clStructure σ) rfl (ΛG σ c) (isScPlusMultisection_ΛG σ c)
  have h := normLam_eq (c := clBundle σ) (S := clStructure σ) rfl (nG σ) (ΛG σ c) b.lam x
    fun w _ => b.comm w
  rw [normOf_nG] at h
  exact h.le.trans (pointwiseNorm_ΛG_le hc1 x)

/-- **`(f, λ)` is in general position** (Definition 16.6.4), for a regular value `c` of `φ`. -/
theorem isInGeneralPositionWith_tG {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) {c : Fin n → ℝ}
    (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x)) :
    (clFredholmSection σ hφ heq).1.IsInGeneralPositionWith (tG σ c) :=
  ⟨clRep σ hφ heq, ΛG σ c, isScPlusMultisection_ΛG σ c, rfl, rfl,
    isInGeneralPosition_ΛG hφ heq hc⟩

end Polyfold.Examples.Classical
