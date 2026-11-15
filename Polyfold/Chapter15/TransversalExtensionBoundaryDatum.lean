import Polyfold.Chapter15.TransversalExtensionWitness
import Polyfold.Chapter15.SingleSectionMultisection
import Polyfold.Chapter14.HalfSpaceConstSection

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, p. 698:
**Theorem 15.3.9** (Transversal Extension Theorem; 2017: Theorem 15.5) **with a non-zero
boundary datum**.

# Theorem 15.3.9 for the constant boundary datum `(x, −3/4)` on `H × ℝ → H`

The strong bundle `H × ℝ → H`, `H = [0, ∞) × ℝ`, over the trivial ep-groupoid of `H`, the
section `f(a, y) = ((a, y), a² + y² − 1)` of `TransversalExtensionWitness`, and over `∂H` the
multisection `Λ_v` of the constant section `(x, v)`, `v = −3/4` (`constMulti v`), with
`dom-supp(Λ_v) = ∂H ≠ ∅`.  For the auxiliary norm `N(x, w) = |w|` the pair `(N, H)` controls
compactness, `N(Λ_v) = 3/4 < 1 = h`, and at the boundary points where `f(x) = (x, v)`, that is
`x = (0, ±1/2)`, the operator `(f − s)'(x) = 2y η` is onto on `T^R_xH = {0} × ℝ`.

## What is formalized (namespace `Polyfold.HalfSpaceBundle`)

* `oneSet_bundle_eq`, `fibNormH` (`N(x, w) = |w|` on `W[1]`), `isAuxNorm_fibNormH`
  (Definition 5.1.1), `isAuxNorm_fibNormH_halfSEP` (with invariance under the morphisms).
* `controlsCompactness_halfDisc_univ`: `(N, H)` controls the compactness of `f`.
* `isScPlusSection_constSec`, `constMulti_eq_sectionMulti`, `isScPlusMultisection_constMulti`.
* `shiftedDiscMap` (`a² + y² − 1/4`), `isReducedOntoAtPt_halfDisc_constMulti`,
  **`isBoundaryFaceOnto_halfDisc_constMulti`** (the boundary hypothesis of Theorem 15.3.9).
* **`theorem_15_3_9_hypotheses_constDatum`**: `∂X ≠ ∅`, non-zero fibres,
  `boundaryDomSupp Λ_v ≠ ∅`, `Λ_v(f(0, 1/2)) > 0`, and every hypothesis of
  `theorem_15_3_9_statement (halfSEP 1 1)` for `f`, `(N, H)`, `Λ_v` and `h ≡ 1`.
* **`theorem_15_3_9_constDatum`**: the conclusion of Theorem 15.3.9 there: a structurable `Λ'`
  with `Λ' = Λ_v` over `∂H` (so `Λ'` charges `(x, −3/4)` at every boundary point), `N(Λ') < 1`,
  admissible and transversal, `Λ' ∘ f` a compact branched ep⁺-subgroupoid.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid Linearization15

variable {m k : ℕ}

/-! ### The auxiliary norm `N(x, w) = |w|` -/

/-- `W[1] = W` for `H × ℝᵏ → H` (constant sc-structures). -/
lemma oneSet_bundle_eq : (bundle m k).oneSet = univ := by
  refine eq_univ_of_forall fun y => ?_
  rintro c hc -
  rw [mem_singleton_iff.1 hc]
  exact (bijective_toBase_const _ 1).2 _

lemma snd_sub_fib {x : H m} (v w : proj m k ⁻¹' {x}) :
    ((v - w : proj m k ⁻¹' {x}) : H m × (Fin k → ℝ)).2 =
      (v : H m × (Fin k → ℝ)).2 - (w : H m × (Fin k → ℝ)).2 :=
  ((fibEquiv x).linearEquiv ℝ).map_sub v w

lemma snd_add_fib {x : H m} (v w : proj m k ⁻¹' {x}) :
    ((v + w : proj m k ⁻¹' {x}) : H m × (Fin k → ℝ)).2 =
      (v : H m × (Fin k → ℝ)).2 + (w : H m × (Fin k → ℝ)).2 :=
  ((fibEquiv x).linearEquiv ℝ).map_add v w

lemma snd_smul_fib {x : H m} (t : ℝ) (v : proj m k ⁻¹' {x}) :
    ((t • v : proj m k ⁻¹' {x}) : H m × (Fin k → ℝ)).2 = t • (v : H m × (Fin k → ℝ)).2 :=
  ((fibEquiv x).linearEquiv ℝ).map_smul t v

lemma snd_zero_fib (x : H m) : ((0 : proj m k ⁻¹' {x}) : H m × (Fin k → ℝ)).2 = 0 :=
  ((fibEquiv x).linearEquiv ℝ).map_zero

/-- **The fibre norm** `N(x, w) = |w|` on `W[1]` of `H × ℝᵏ → H`. -/
def fibNormH : (bundle m k).One → ℝ := fun w => ‖((bundle m k).oneVal w).2‖

/-- **The fibre norm is an auxiliary norm** (Definition 5.1.1). -/
theorem isAuxNorm_fibNormH : (bundle m k).IsAuxNorm (fibNormH (m := m) (k := k)) where
  continuous := (continuous_norm.comp continuous_snd).comp (bundle m k).continuous_oneVal
  fiber x :=
    { eq_zero := fun v hv => by
        have h0 : ((v : proj m k ⁻¹' {x}) : H m × (Fin k → ℝ)).2 = 0 := norm_eq_zero.1 hv
        refine Subtype.ext ((fibEquiv x).injective ?_)
        change ((v : proj m k ⁻¹' {x}) : H m × (Fin k → ℝ)).2 =
          ((0 : proj m k ⁻¹' {x}) : H m × (Fin k → ℝ)).2
        rw [h0, snd_zero_fib]
      smul := fun t v => by
        change ‖((t • (v : proj m k ⁻¹' {x}) : proj m k ⁻¹' {x}) : H m × (Fin k → ℝ)).2‖ =
          |t| * ‖((v : proj m k ⁻¹' {x}) : H m × (Fin k → ℝ)).2‖
        rw [snd_smul_fib, norm_smul, Real.norm_eq_abs]
      add_le := fun v w => by
        change ‖(((v : proj m k ⁻¹' {x}) + (w : proj m k ⁻¹' {x}) : proj m k ⁻¹' {x}) :
          H m × (Fin k → ℝ)).2‖ ≤ ‖((v : proj m k ⁻¹' {x}) : H m × (Fin k → ℝ)).2‖ +
            ‖((w : proj m k ⁻¹' {x}) : H m × (Fin k → ℝ)).2‖
        rw [snd_add_fib]; exact norm_add_le _ _
      complete := fun u hu => by
        set a : ℕ → Fin k → ℝ := fun j => ((u j : proj m k ⁻¹' {x}) : H m × (Fin k → ℝ)).2
          with ha
        have hsub : ∀ i j, fibNormH ((bundle m k).toOne (u i - u j)) = ‖a i - a j‖ :=
          fun i j => by
            change ‖(((u i : proj m k ⁻¹' {x}) - (u j : proj m k ⁻¹' {x}) : proj m k ⁻¹' {x}) :
              H m × (Fin k → ℝ)).2‖ = _
            rw [snd_sub_fib]
        have hc : CauchySeq a := by
          refine Metric.cauchySeq_iff.2 fun ε hε => ?_
          obtain ⟨N₀, hN₀⟩ := hu ε hε
          exact ⟨N₀, fun i hi j hj => by rw [dist_eq_norm, ← hsub]; exact hN₀ i hi j hj⟩
        obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hc
        let v₀ : proj m k ⁻¹' {x} := ⟨(x, b), rfl⟩
        have hv₀ : v₀ ∈ (bundle m k).oneFiber x := by
          change ((v₀ : proj m k ⁻¹' {x}) : H m × (Fin k → ℝ)) ∈ (bundle m k).oneSet
          rw [oneSet_bundle_eq]; exact mem_univ _
        refine ⟨⟨v₀, hv₀⟩, ?_⟩
        have e : ∀ j, fibNormH ((bundle m k).toOne (u j - ⟨v₀, hv₀⟩)) = ‖a j - b‖ := fun j => by
          change ‖(((u j : proj m k ⁻¹' {x}) - v₀ : proj m k ⁻¹' {x}) :
            H m × (Fin k → ℝ)).2‖ = _
          rw [snd_sub_fib]
        simp only [e]
        exact tendsto_iff_norm_sub_tendsto_zero.1 hb }
  tendsto_zeroOne := fun w x hP hN => by
    refine TopologicalSpace.tendsto_nhds_generateFrom_iff.2 ?_
    rintro s ⟨c, hc, W, hW, rfl⟩ ⟨-, hz⟩
    obtain rfl := mem_singleton_iff.1 hc
    have hlift : ∀ y : H m × (Fin k → ℝ),
        (chart₀ (m := m) (k := k)).liftOne y = ((y.1 : (halfSpaceSc m) 0), y.2) :=
      fun y => Prod.ext rfl (TrivialBundle.invFun_toBase_one _)
    have hz' : (((x : (halfSpaceSc m) 0), 0) : (halfSpaceSc m) 0 × (Fin k → ℝ)) ∈ W := by
      have := hz
      change (chart₀ (m := m) (k := k)).liftOne (fiberZero (proj m k) x) ∈ W at this
      rwa [hlift] at this
    have h1 : Tendsto (fun j => ((((bundle m k).oneVal (w j)).1 : (halfSpaceSc m) 0),
        ((bundle m k).oneVal (w j)).2)) atTop
        (𝓝 (((x : (halfSpaceSc m) 0), 0) : (halfSpaceSc m) 0 × (Fin k → ℝ))) := by
      refine ((continuous_subtype_val.tendsto x).comp hP).prodMk_nhds ?_
      exact tendsto_zero_iff_norm_tendsto_zero.2 hN
    filter_upwards [h1 (hW.mem_nhds hz')] with j hj
    refine ⟨⟨mem_univ _, mem_univ _⟩, ?_⟩
    change (chart₀ (m := m) (k := k)).liftOne ((bundle m k).oneVal (w j)) ∈ W
    rw [hlift]; exact hj

/-- `N(x, w) = |w|` is an auxiliary norm for the ep-groupoid bundle (the morphisms are units). -/
theorem isAuxNorm_fibNormH_halfSEP : (halfSEP m k).E.IsAuxNorm (fibNormH (m := m) (k := k)) :=
  ⟨isAuxNorm_fibNormH, fun h k' _ _ e => by rw [(bundle m k).oneVal_injective e]⟩

theorem fibNormH_oneMk (w : H m × (Fin k → ℝ)) (hw : w ∈ (bundle m k).oneSet) :
    fibNormH (m := m) (k := k) ((bundle m k).oneMk w hw) = ‖w.2‖ := by
  unfold fibNormH
  rw [oneVal_oneMk]

/-! ### `(N, H)` controls compactness -/

/-- **`(N, H)` controls the compactness of `f(a, y) = ((a, y), a² + y² − 1)`** (Definition
15.3.1): `N(f(x)) ≤ 1` means `|a² + y² − 1| ≤ 1`, so `|a|, |y| ≤ 2`. -/
theorem controlsCompactness_halfDisc_univ :
    ControlsCompactness (halfSEP 1 1) halfDiscSection (fibNormH (m := 1) (k := 1)) univ := by
  refine ⟨isAuxNorm_fibNormH_halfSEP, isOpen_univ, GroupoidStr.isSaturated_univ _,
    subset_univ _, ?_⟩
  let K : Set (H 1) := ((↑) : H 1 → (halfSpaceSc 1) 0) ⁻¹' Metric.closedBall (0 : Pm 1) 2
  have hK : IsCompact K :=
    (quadrant_isClosed 1 (rnSc 1) 0).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_closedBall _ _)
  have hsub : {x ∈ (univ : Set (halfSEP 1 1).Obj) |
      (halfSEP 1 1).B.AuxLe (fibNormH (m := 1) (k := 1)) (halfDiscSection x) 1} ⊆
      (K : Set (halfSEP 1 1).Obj) := by
    rintro (x : H 1) ⟨-, hw, hle⟩
    have hle' : ‖halfDiscMap (x : Pm 1)‖ ≤ 1 := (fibNormH_oneMk _ hw).symm.trans_le hle
    have h1 : ‖halfDiscMap (x : Pm 1) 0‖ ≤ 1 :=
      (norm_le_pi_norm (halfDiscMap (x : Pm 1)) 0).trans hle'
    change ‖(x : Pm 1).1 0 ^ 2 + (x : Pm 1).2 0 ^ 2 - 1‖ ≤ 1 at h1
    rw [Real.norm_eq_abs, abs_le] at h1
    change (x : Pm 1) ∈ Metric.closedBall (0 : Pm 1) 2
    rw [Metric.mem_closedBall, dist_zero_right, norm_prod_le_iff]
    refine ⟨(pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_,
      (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_⟩
    · rw [Subsingleton.elim i 0, Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [h1.2, sq_nonneg ((x : Pm 1).2 0), sq_nonneg ((x : Pm 1).1 0 - 2),
        sq_nonneg ((x : Pm 1).1 0 + 2)]
    · rw [Subsingleton.elim i 0, Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [h1.2, sq_nonneg ((x : Pm 1).1 0), sq_nonneg ((x : Pm 1).2 0 - 2),
        sq_nonneg ((x : Pm 1).2 0 + 2)]
  exact (hK.image (halfSEP 1 1).X.continuous_π).closure_of_subset (image_mono hsub)

/-! ### The boundary datum `Λ_v` -/

/-- The constant section is an sc⁺-section of `H × ℝᵏ → H`. -/
theorem isScPlusSection_constSec (v : Fin k → ℝ) :
    (halfSEP m k).B.IsScPlusSection (constSec v) := by
  obtain ⟨hsec, G, hG, hGs⟩ := isScPlusSectionOn_constSec (m := m) v
  exact ((halfSEP m k).B.isScPlusSection_iff _).2
    ⟨fun y => hsec y (mem_univ y), G, funext fun y => hG y (mem_univ y), hGs⟩

theorem constMulti_eq_sectionMulti (v : Fin k → ℝ) :
    constMulti (m := m) v = sectionMulti (constSec v) :=
  rfl

/-- **`Λ_v` is an sc⁺-multisection** on all of `W` (Definition 13.2.1). -/
theorem isScPlusMultisection_constMulti (v : Fin k → ℝ) :
    IsScPlusMultisection (halfSEP m k) (constMulti v) :=
  isScPlusMultisection_sectionMulti (fun _ => rfl) (isScPlusSection_constSec v)

/-- The datum `v = −3/4`. -/
def constDatum : Fin 1 → ℝ := fun _ => -(3 / 4)

theorem constDatum_ne_zero : constDatum ≠ 0 := fun h => by
  have := congrFun h 0
  norm_num [constDatum] at this

/-- `N(Λ_v)(x) = |v| = 3/4`. -/
theorem pointwiseNorm_constMulti_constDatum (x : (halfSEP 1 1).Obj) :
    pointwiseNorm (fibNormH (m := 1) (k := 1)) (constMulti constDatum) x = 3 / 4 := by
  have hmem : constSec (m := 1) constDatum x ∈ (halfSEP 1 1).B.oneSet := by
    rw [show (halfSEP 1 1).B.oneSet = univ from oneSet_bundle_eq]; exact mem_univ _
  refine ((pointwiseNorm_constMulti _ constDatum x).trans
    ((normW_of_mem _ hmem).trans (fibNormH_oneMk _ hmem))).trans ?_
  change ‖constDatum‖ = 3 / 4
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_) ?_
  · change ‖(-(3 / 4) : ℝ)‖ ≤ 3 / 4
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
  · have h := norm_le_pi_norm constDatum 0
    change ‖(-(3 / 4) : ℝ)‖ ≤ ‖constDatum‖ at h
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)] at h
    exact h

/-! ### General position at the boundary -/

/-- `ψ(a, y) = a² + y² − 1/4`, so that `f − s` is the graph section of `ψ`. -/
def shiftedDiscMap (p : Pm 1) : Fin 1 → ℝ := fun _ => p.1 0 ^ 2 + p.2 0 ^ 2 - 1 / 4

theorem shiftedDiscMap_eq (p : Pm 1) : shiftedDiscMap p = halfDiscMap p - constDatum := by
  funext i
  simp only [shiftedDiscMap, halfDiscMap, constDatum, Pi.sub_apply]
  ring

theorem contDiff_shiftedDiscMap : ContDiff ℝ ∞ shiftedDiscMap := by
  unfold shiftedDiscMap
  fun_prop

/-- **At a boundary zero, `Dψ` is onto on `{0} × ℝ`**: at `(0, y)` with `y² = 1/4`,
`Dψ(0, y)(0, η) = 2 y η`. -/
theorem shiftedDiscMap_onto_hyperplane {x : Pm 1} (h0 : shiftedDiscMap x = 0) (hb : x.1 0 = 0)
    (w : Fin 1 → ℝ) : ∃ v : Pm 1, v.1 0 = 0 ∧ fderiv ℝ shiftedDiscMap x v = w := by
  have hy : x.2 0 ^ 2 = 1 / 4 := by
    have := congrFun h0 0
    simp only [shiftedDiscMap, Pi.zero_apply, hb] at this
    linarith
  have hy0 : x.2 0 ≠ 0 := by
    intro h
    rw [h] at hy
    norm_num at hy
  have hd : HasFDerivAt shiftedDiscMap (ContinuousLinearMap.pi fun _ : Fin 1 =>
      (2 * x.1 0) • coordA + (2 * x.2 0) • coordY) x := by
    have e : shiftedDiscMap = fun p => halfDiscMap p - constDatum := funext shiftedDiscMap_eq
    rw [e]
    exact (hasFDerivAt_halfDiscMap x).sub_const constDatum
  refine ⟨(0, fun _ => w 0 / (2 * x.2 0)), rfl, ?_⟩
  rw [hd.fderiv]
  funext i
  rw [Subsingleton.elim i 0]
  simp [coordA, coordY]
  field_simp

/-- **`(f, Λ_v)` is in general position at the boundary points of `supp(Λ_v ∘ f)`**
(Definition 15.3.5): there `f(x) = (x, v)`, `f − s` is the graph section of `ψ`, and the
operator of `T(f, Λ_v)(x)` is that of `T(graph ψ, Λ₀)(x)`, onto on `T^R_xH`. -/
theorem isReducedOntoAtPt_halfDisc_constMulti (x : (halfSEP 1 1).X.PObj.Level 1)
    (hxb : (halfSEP 1 1).X.PObj.levelVal 1 x ∈ (halfSEP 1 1).X.PObj.boundary)
    (hpos : 0 < constMulti constDatum (halfDiscSection ((halfSEP 1 1).X.PObj.levelVal 1 x))) :
    IsReducedOntoAtPt halfDiscSection (constMulti constDatum) x := by
  set x₀ : H 1 := (halfSEP 1 1).X.PObj.levelVal 1 x with hx₀
  have hxs : halfDiscSection x₀ = constSec constDatum x₀ := (sectionMulti_pos_iff _ _).1 hpos
  have h0 : shiftedDiscMap (x₀ : Pm 1) = 0 := by
    rw [shiftedDiscMap_eq, sub_eq_zero]
    exact congrArg Prod.snd hxs
  have hb := (mem_boundary_halfSEP_iff 1 1 x₀).1 hxb
  obtain ⟨_, H⟩ := isInGeneralPositionAt_graphSection contDiff_shiftedDiscMap h0 hb
    (shiftedDiscMap_onto_hyperplane h0 hb)
  have hg0 : graphSection shiftedDiscMap x₀ = fiberZero (halfSEP 1 1).P x₀ :=
    (isZeroAt_graphSection_iff (k := 1) (φ := shiftedDiscMap) (x := x₀)).2 h0
  refine isReducedOntoAtPt_sectionMulti_of_zero (isScPlusSection_constSec constDatum)
    (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap)
    (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_shiftedDiscMap)
    (isChart_chart₀ (m := 1) (k := 1)) (x := x) (mem_univ _) hxs hg0 ?_ H
  unfold subDeriv
  congr 1
  funext u
  simp only [Function.comp_apply]
  change halfDiscMap _ - constDatum = shiftedDiscMap _ - 0
  rw [sub_zero, shiftedDiscMap_eq]

/-- **The boundary hypothesis of Theorem 15.3.9 holds** for `f` and `Λ_v`
(`isBoundaryFaceOnto_iff`, with the extension `Λ_v` itself). -/
theorem isBoundaryFaceOnto_halfDisc_constMulti :
    IsBoundaryFaceOnto halfDiscSection (constMulti constDatum) :=
  (isBoundaryFaceOnto_iff (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap)
    (isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap)
    (isScPlusMultisection_constMulti constDatum) fun _ _ => rfl).2
    fun x hxb _ hpos => isReducedOntoAtPt_halfDisc_constMulti x hxb hpos

/-! ### Theorem 15.3.9 -/

/-- The boundary point `(0, 1/2)` of `H`, where `f(x) = (x, −3/4)`. -/
def constDatumPoint : H 1 := ⟨(0, fun _ => 1 / 2), fun _ => le_rfl⟩

theorem constMulti_halfDisc_constDatumPoint :
    0 < constMulti constDatum (halfDiscSection constDatumPoint) := by
  refine (sectionMulti_pos_iff _ _).2 (Prod.ext rfl (funext fun i => ?_))
  change (0 : ℝ) ^ 2 + (1 / 2) ^ 2 - 1 = -(3 / 4)
  norm_num

/-- **All hypotheses of Theorem 15.3.9 with a non-zero boundary datum** (on `H × ℝ → H`,
`f(a, y) = ((a, y), a² + y² − 1)`, `Λ = Λ_v` the multisection of `(x, −3/4)` over `∂H`, `h ≡ 1`,
`N(x, w) = |w|`, `U = H`): the boundary is non-empty, every fibre is non-zero,
`boundaryDomSupp Λ_v ≠ ∅`, `supp(Λ_v ∘ f)` meets `∂H` (at `(0, 1/2)`), and every hypothesis of
`theorem_15_3_9_statement (halfSEP 1 1)` holds. -/
theorem theorem_15_3_9_hypotheses_constDatum :
    (halfSEP 1 1).X.PObj.boundary.Nonempty ∧
    (∀ y : (halfSEP 1 1).Obj, Nontrivial ((halfSEP 1 1).P ⁻¹' {y})) ∧
    (boundaryDomSupp (constMulti (m := 1) constDatum)).Nonempty ∧
    (∃ x ∈ (halfSEP 1 1).X.PObj.boundary, 0 < constMulti constDatum (halfDiscSection x)) ∧
    (halfSEP 1 1).X.IsTame ∧ (halfSEP 1 1).X.HasParacompactOrbitSpace ∧
    (halfSEP 1 1).X.PObj.AdmitsScPartitionsOfUnity ∧
    (halfSEP 1 1).E.IsScFredholmSectionFunctor halfDiscSection ∧
    (halfSEP 1 1).B.IsScFredholmSectionTame halfDiscSection ∧
    (halfSEP 1 1).E.HasCompactSolutionSetEp halfDiscSection ∧
    ControlsCompactness (halfSEP 1 1) halfDiscSection (fibNormH (m := 1) (k := 1)) univ ∧
    IsBoundaryStructurable (halfSEP 1 1) (constMulti constDatum) ∧
    boundaryDomSupp (constMulti (m := 1) constDatum) ⊆ univ ∧
    (∀ x ∈ (halfSEP 1 1).X.PObj.boundary,
      pointwiseNorm (fibNormH (m := 1) (k := 1)) (constMulti constDatum) x ≤ 1) ∧
    Continuous (fun _ : (halfSEP 1 1).Obj => (1 : ℝ)) ∧
    (∀ φ : (halfSEP 1 1).Mor, (fun _ : (halfSEP 1 1).Obj => (1 : ℝ)) ((halfSEP 1 1).X.src φ) =
      (fun _ : (halfSEP 1 1).Obj => (1 : ℝ)) ((halfSEP 1 1).X.tgt φ)) ∧
    (∀ _ : (halfSEP 1 1).Obj, (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1) ∧
    (∀ x ∈ (halfSEP 1 1).X.PObj.boundary,
      pointwiseNorm (fibNormH (m := 1) (k := 1)) (constMulti constDatum) x < 1) ∧
    IsBoundaryFaceOnto halfDiscSection (constMulti constDatum) :=
  ⟨⟨_, zero_mem_boundary_halfSEP 1 1⟩, nontrivial_fibre_halfSEP 1 1,
    boundaryDomSupp_constMulti_nonempty constDatum_ne_zero,
    ⟨_, (mem_boundary_halfSEP_iff 1 1 constDatumPoint).2 rfl, constMulti_halfDisc_constDatumPoint⟩,
    isTame_halfSEP 1 1, hasParacompactOrbitSpace_halfSEP 1 1,
    admitsScPartitionsOfUnity_halfSEP 1 1,
    isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap,
    isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap,
    hasCompactSolutionSetEp_halfDisc, controlsCompactness_halfDisc_univ,
    isBoundaryStructurable_constMulti constDatum, subset_univ _,
    fun x _ => by rw [pointwiseNorm_constMulti_constDatum]; norm_num, continuous_const,
    fun _ => rfl, fun _ => ⟨one_pos, le_rfl⟩,
    fun x _ => by rw [pointwiseNorm_constMulti_constDatum]; norm_num,
    isBoundaryFaceOnto_halfDisc_constMulti⟩

/-- **Theorem 15.3.9 with a non-zero boundary datum** (`theorem_15_3_9` applied to the instance
of `theorem_15_3_9_hypotheses_constDatum`): there is a structurable `Λ'` on `H × ℝ → H` equal to
`Λ_v` over `∂H` (so it charges `(x, −3/4)` at every `x ∈ ∂H`), with `N(Λ') < 1`, admissible and
transversal, and `Λ' ∘ f` is a compact branched ep⁺-subgroupoid. -/
theorem theorem_15_3_9_constDatum :
    ∃ Λ' : (halfSEP 1 1).W → ℚ≥0, IsStructurable (halfSEP 1 1) Λ' ∧
      (∀ w, (halfSEP 1 1).P w ∈ (halfSEP 1 1).X.PObj.boundary → Λ' w = constMulti constDatum w) ∧
      (∀ x ∈ (halfSEP 1 1).X.PObj.boundary, 0 < Λ' (constSec constDatum x)) ∧
      (∀ x, pointwiseNorm (fibNormH (m := 1) (k := 1)) Λ' x < 1) ∧
      IsAdmissible (halfSEP 1 1) halfDiscSection (fibNormH (m := 1) (k := 1)) univ Λ' ∧
      IsTransversal halfDiscSection Λ' ∧
      (halfSEP 1 1).X.IsBranchedEpSubgroupoid (fun z => (Λ' (halfDiscSection z) : ℚ)) ∧
      (halfSEP 1 1).X.IsCompactBranched (fun z => (Λ' (halfDiscSection z) : ℚ)) := by
  obtain ⟨-, -, -, -, hX, hpara, hPU, hf, hft, hS, hcc, hΛ, hdom, hN1, hc, hfun, hh, hNh,
    honto⟩ := theorem_15_3_9_hypotheses_constDatum
  obtain ⟨Λ', h1, h2, -, h4, h5, h6, h7, h8⟩ :=
    theorem_15_3_9 hX hpara hPU _ hf hft hS _ _ hcc _ hΛ hdom hN1 _ hc hfun hh hNh honto
  refine ⟨Λ', h1, h2, fun x hx => ?_, h4, h5, h6, h7, h8⟩
  rw [h2 (constSec constDatum x) hx]
  exact lt_of_lt_of_eq one_pos (constMulti_constSec constDatum x).symm

end HalfSpaceBundle

end Polyfold
