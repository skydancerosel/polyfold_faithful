import Polyfold.Chapter7.ReducedNotHausdorff
import Polyfold.Chapter7.Zhou

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 10:
**Remark 10.1.8, p. 467, and Appendix 10.6.3, p. 519** (both new in the 2021 edition), Zhou's
example: a finite group acting on an M-polyfold, and an sc-diffeomorphism `β` fixing a point
`x` with `|β(y)| = |y|` which is not of the form `y ↦ g ∗ y` near `x`.

## The text, paraphrased

(Appendix 10.6.3) On `ℝ ⊕ L²(ℝ)` with a weighted Sobolev sc-structure, the retraction
`r(s, f) = (s, π_{|s|} f)` (the moving projections of Appendix 1.4.4, used for `|s|`) has image
`Y` homeomorphic to `Σ = ℝ² ∖ {(0, t) | t ≠ 0}`.  `ℤ/2` acts by `(s, f) ↦ (s, −f)`, so
`ℤ/2 ⋉ Y` is an ep-groupoid.  `η(s, f) = (s, f)` for `s ≤ 0` and `(s, −f)` for `s > 0` is an
sc-diffeomorphism with `|η(y)| = |y|`, and it is not `y ↦ g ∗ y` for `g ∈ ℤ/2`.

## What is formalized (namespace `Polyfold.EpGroupoid.Examples.ZhouSigma`)

The moving projections are those of the project's Remark 4.1.3 family (`RemarkFourThree.fam`,
`fam t = 0` for `t ≤ 0`, a rank-one projection for `t > 0`, a loss family), in place of the
weighted Sobolev ones; the text's `π_{|s|}` is `fam₂ s = fam s + fam (−s)`.

* `IsLossFamily.add`, `IsLossFamily.sub`, `IsLossFamily.comp_neg`: loss families are closed
  under sums, differences and `p ↦ −p`.
* `fam₂`, `famη = fam s − fam (−s)` (loss families), the retraction `Rt₂`, its retract `O₂` (a
  line over each `s ≠ 0`, the point `0` over `s = 0`: `Σ`), the M-polyfold `P₂`, the action of
  `ℤ/2 = ℤˣ` by `(s, z) ↦ (s, ±z)` and the translation ep-groupoid `X₂ = ℤ/2 ⋉ O₂`.
* `ηO : O₂ → O₂`, `(s, z) ↦ (s, famη s z)`: `z` over `s > 0`, `−z` over `s < 0`.
* **`remark_10_1_8`**: `ηO` is an sc-diffeomorphism of `O₂` (its own inverse), fixes `0`,
  satisfies `|ηO(y)| = |y|`, and on no neighbourhood of `0` is it `y ↦ k • y` for one
  `k ∈ ℤ/2`.
* **`not_isLR`**: consequently `ℤ/2 ⋉ O₂` does not have the local regularity property (LR)
  (Definition 7.4.19): the guess of Remark 10.1.8 fails for every natural representation at `0`.

This file does not use the appendix's weighted Sobolev sc-structure `H^{m, δ_m}(ℝ)`; the example
is the same up to the choice of the moving projections (both retracts are `Σ`, with the same
action and the same `η` up to the sign convention).  The appendix's own construction, on
`H^{m, δ_m}(ℝ)` with its projections, is `ZhouTenSix.remark_10_1_8` (`GapP2_A2TenSix.lean`,
since 2026-11-12); this file is kept as a variant.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

noncomputable section

namespace Polyfold

/-! ### Closure properties of loss families -/

section LossFamily

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Z W : ScBanach} {L L' : V → ∀ m, Z m →L[ℝ] W m}

omit [FiniteDimensional ℝ V] in
/-- The sum of two loss families is a loss family. -/
theorem IsLossFamily.add (h : IsLossFamily L) (h' : IsLossFamily L') :
    IsLossFamily (fun p m => L p m + L' p m) where
  toBase p m z := by
    change W.toBase m (L p m z + L' p m z) = L p 0 (Z.toBase m z) + L' p 0 (Z.toBase m z)
    rw [map_add, h.toBase, h'.toBase]
  continuous m := (h.continuous m).add (h'.continuous m)
  contDiff m := by
    simpa only [ContinuousLinearMap.add_comp] using (h.contDiff m).add (h'.contDiff m)

omit [FiniteDimensional ℝ V] in
/-- The difference of two loss families is a loss family. -/
theorem IsLossFamily.sub (h : IsLossFamily L) (h' : IsLossFamily L') :
    IsLossFamily (fun p m => L p m - L' p m) where
  toBase p m z := by
    change W.toBase m (L p m z - L' p m z) = L p 0 (Z.toBase m z) - L' p 0 (Z.toBase m z)
    rw [map_sub, h.toBase, h'.toBase]
  continuous m := (h.continuous m).sub (h'.continuous m)
  contDiff m := by
    simpa only [ContinuousLinearMap.sub_comp] using (h.contDiff m).sub (h'.contDiff m)

omit [FiniteDimensional ℝ V] in
/-- `p ↦ L(−p)` is a loss family with `L`. -/
theorem IsLossFamily.comp_neg (h : IsLossFamily L) : IsLossFamily (fun p m => L (-p) m) where
  toBase p m z := h.toBase (-p) m z
  continuous m := (h.continuous m).comp (continuous_fst.neg.prodMk continuous_snd)
  contDiff m := (h.contDiff m).comp contDiff_neg

end LossFamily

namespace EpGroupoid.Examples.ZhouSigma

open RemarkFourThree ScOneExample JumpingRetract

/-! ### The two-sided moving projections -/

/-- `π_{|t|} = fam t + fam (−t)` (one of the two vanishes, and both at `t = 0`). -/
def fam₂ : ℝ → ∀ m, ScOneExample.X m →L[ℝ] ScOneExample.X m := fun t m => fam t m + fam (-t) m

/-- `famη t = fam t − fam (−t)`: `η` in the fibres. -/
def famη : ℝ → ∀ m, ScOneExample.X m →L[ℝ] ScOneExample.X m := fun t m => fam t m - fam (-t) m

theorem isLossFamily_fam₂ :
    IsLossFamily (V := ℝ) (Z := ScOneExample.X) (W := ScOneExample.X) fam₂ :=
  isLossFamily_fam.add isLossFamily_fam.comp_neg

theorem isLossFamily_famη :
    IsLossFamily (V := ℝ) (Z := ScOneExample.X) (W := ScOneExample.X) famη :=
  isLossFamily_fam.sub isLossFamily_fam.comp_neg

lemma fam_neg_of_pos {t : ℝ} (ht : 0 < t) (m : ℕ) : fam (-t) m = 0 := fam_of_nonpos (by linarith) m

lemma fam₂_of_pos {t : ℝ} (ht : 0 < t) (m : ℕ) : fam₂ t m = fam t m := by
  simp [fam₂, fam_neg_of_pos ht]

lemma fam₂_of_neg {t : ℝ} (ht : t < 0) (m : ℕ) : fam₂ t m = fam (-t) m := by
  simp [fam₂, fam_of_nonpos ht.le]

lemma fam₂_zero (m : ℕ) : fam₂ 0 m = 0 := by simp [fam₂, fam_of_nonpos le_rfl]

lemma famη_of_pos {t : ℝ} (ht : 0 < t) (m : ℕ) : famη t m = fam t m := by
  simp [famη, fam_neg_of_pos ht]

lemma famη_of_neg {t : ℝ} (ht : t < 0) (m : ℕ) : famη t m = -fam (-t) m := by
  simp [famη, fam_of_nonpos ht.le]

lemma famη_zero (m : ℕ) : famη 0 m = 0 := by simp [famη, fam_of_nonpos le_rfl]

lemma fam₂_idem (t : ℝ) (z : c0) : fam₂ t 0 (fam₂ t 0 z) = fam₂ t 0 z := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [fam₂_of_neg ht]; exact fam_idem _ z
  · simp [fam₂_zero]
  · rw [fam₂_of_pos ht]; exact fam_idem _ z

lemma fam₂_famη (t : ℝ) (z : c0) : fam₂ t 0 (famη t 0 z) = famη t 0 z := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [fam₂_of_neg ht, famη_of_neg ht]
    change fam (-t) 0 (-(fam (-t) 0 z)) = -(fam (-t) 0 z)
    rw [map_neg, fam_idem]
  · simp [fam₂_zero, famη_zero]
  · rw [fam₂_of_pos ht, famη_of_pos ht]; exact fam_idem _ z

/-- On the retract, `famη t z = z` over `t > 0`. -/
lemma famη_of_mem_pos {t : ℝ} (ht : 0 < t) {z : c0} (hz : fam₂ t 0 z = z) : famη t 0 z = z := by
  rw [famη_of_pos ht]; rwa [fam₂_of_pos ht] at hz

/-- On the retract, `famη t z = −z` over `t ≤ 0`. -/
lemma famη_of_mem_nonpos {t : ℝ} (ht : t ≤ 0) {z : c0} (hz : fam₂ t 0 z = z) :
    famη t 0 z = -z := by
  rcases ht.lt_or_eq with ht | rfl
  · rw [famη_of_neg ht]; rw [fam₂_of_neg ht] at hz
    change -(fam (-t) 0 z) = -z
    rw [hz]
  · rw [fam₂_zero] at hz
    have hz0 : z = 0 := hz.symm
    subst hz0
    rw [famη_zero]
    simp

/-! ### The retract `Σ` and the ep-groupoid `ℤ/2 ⋉ Σ` -/

/-- The sc-smooth retraction `(t, z) ↦ (t, π_{|t|} z)` of `ℝ ⊕ X`. -/
def Rt₂ : ScRetraction JumpingRetract.E univ :=
  isLossFamily_fam₂.retraction fun t y => fam₂_idem t y

/-- The retract `Σ = r(ℝ ⊕ X)`: a line over each `t ≠ 0`, the point `0` over `t = 0`. -/
abbrev O₂ : Set (JumpingRetract.E 0) := Rt₂.retract

lemma mem_O₂_iff (q : JumpingRetract.E 0) : q ∈ O₂ ↔ fam₂ q.1 0 q.2 = q.2 := by
  constructor
  · rintro ⟨p, -, rfl⟩
    exact fam₂_idem p.1 p.2
  · intro h
    exact ⟨q, mem_univ _, Prod.ext rfl h⟩

lemma smul_mem₂ (k : ℤˣ) (y : O₂) : ((y.1.1, c k • y.1.2) : JumpingRetract.E 0) ∈ O₂ := by
  rw [mem_O₂_iff]
  change fam₂ y.1.1 0 (c k • y.1.2) = c k • y.1.2
  rw [map_smul, (mem_O₂_iff _).1 y.2]

instance : MulAction ℤˣ O₂ where
  smul k y := ⟨(y.1.1, c k • y.1.2), smul_mem₂ k y⟩
  one_smul y := Subtype.ext (Prod.ext rfl (show c 1 • y.1.2 = y.1.2 by simp [c]))
  mul_smul k l y := Subtype.ext (Prod.ext rfl
    (show c (k * l) • y.1.2 = c k • c l • y.1.2 by simp [c, mul_smul]))

lemma smul_val₂ (k : ℤˣ) (y : O₂) :
    ((k • y : O₂) : JumpingRetract.E 0) = (y.1.1, c k • y.1.2) := rfl

lemma zero_mem₂ : (0 : JumpingRetract.E 0) ∈ O₂ := by rw [mem_O₂_iff]; exact map_zero _

/-- The base point `(0, 0)`. -/
def o₂ : O₂ := ⟨0, zero_mem₂⟩

/-- `Σ` as an M-polyfold, with its one chart. -/
def P₂ : MPolyfold O₂ := retractPolyfold Rt₂.isScRetract o₂

lemma retractChart_symm₂ (q : JumpingRetract.E 0) (hq : q ∈ O₂) :
    (retractChart Rt₂.isScRetract o₂).symm q = ⟨q, hq⟩ := by
  classical
  change (if h : q ∈ O₂ then (⟨q, h⟩ : O₂) else o₂) = ⟨q, hq⟩
  rw [dif_pos hq]

/-- A self-map of `Σ` induced by an sc-smooth map of `ℝ ⊕ X` preserving `Σ` is sc-smooth. -/
theorem isScSmoothMap_of_retractMap {f : O₂ → O₂} (hf : Continuous f)
    {g : JumpingRetract.E 0 → JumpingRetract.E 0}
    (hg : IsScSmoothRetractMap JumpingRetract.E univ O₂ JumpingRetract.E univ O₂ g)
    (hfg : ∀ y : O₂, (f y : JumpingRetract.E 0) = g y) :
    P₂.IsScSmoothMap P₂ f := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ hf.continuousOn
    fun y _ => ⟨retractChart Rt₂.isScRetract o₂, retractChart Rt₂.isScRetract o₂, univ,
      isChart_retractChart _ _, isChart_retractChart _ _, isOpen_univ, mem_univ _,
      fun z _ => ⟨mem_univ _, mem_univ _⟩, fun z _ => mem_univ _, ?_⟩
  have heq : EqOn g (⇑(retractChart Rt₂.isScRetract o₂) ∘ f ∘
      (retractChart Rt₂.isScRetract o₂).symm) O₂ := by
    intro q hq
    change g q = (f ((retractChart Rt₂.isScRetract o₂).symm q) : JumpingRetract.E 0)
    rw [retractChart_symm₂ q hq, hfg]
  have h2 : IsScSmoothRetractMap JumpingRetract.E univ (Subtype.val '' (univ : Set O₂))
      JumpingRetract.E univ O₂ (⇑(retractChart Rt₂.isScRetract o₂) ∘ f ∘
        (retractChart Rt₂.isScRetract o₂).symm) := by
    rw [Subtype.coe_image_univ]
    exact hg.congr heq
  exact h2

lemma continuous_smul₂ (k : ℤˣ) : Continuous fun y : O₂ => k • y := by
  change Continuous fun y : O₂ => (⟨(y.1.1, c k • y.1.2), smul_mem₂ k y⟩ : O₂)
  exact Continuous.subtype_mk ((continuous_subtype_val (p := (· ∈ O₂))).fst.prodMk
    ((continuous_subtype_val (p := (· ∈ O₂))).snd.const_smul (c k))) _

/-- `ℤ/2` acts on `Σ` sc-smoothly. -/
theorem isScSmoothMap_smul₂ (k : ℤˣ) : P₂.IsScSmoothMap P₂ fun y : O₂ => k • y :=
  isScSmoothMap_of_retractMap (continuous_smul₂ k)
    ((scaleOp (c k)).isScSmoothRetractMap Rt₂.isScRetract fun q hq => smul_mem₂ k ⟨q, hq⟩)
    fun _ => rfl

/-- **The ep-groupoid `ℤ/2 ⋉ Σ`** (2021 Appendix 10.6.3, `X := G ⋉ Y`). -/
abbrev X₂ : EpGroupoid O₂ (ℤˣ × O₂) :=
  Examples.actionEpGroupoid (P := P₂) isScSmoothMap_smul₂

/-! ### The map `η` -/

lemma famη_mem (y : JumpingRetract.E 0) : ((y.1, famη y.1 0 y.2) : JumpingRetract.E 0) ∈ O₂ := by
  rw [mem_O₂_iff]; exact fam₂_famη y.1 y.2

/-- **`η`** (2021 Appendix 10.6.3): `(t, z) ↦ (t, z)` over `t > 0`, `(t, −z)` over `t < 0`. -/
def ηO (y : O₂) : O₂ := ⟨(y.1.1, famη y.1.1 0 y.1.2), famη_mem y.1⟩

lemma ηO_of_pos (y : O₂) (hy : 0 < y.1.1) : ηO y = y :=
  Subtype.ext (Prod.ext rfl (famη_of_mem_pos hy ((mem_O₂_iff _).1 y.2)))

lemma ηO_of_nonpos (y : O₂) (hy : y.1.1 ≤ 0) : ηO y = (-1 : ℤˣ) • y :=
  Subtype.ext (Prod.ext rfl (by
    change famη y.1.1 0 y.1.2 = c (-1) • y.1.2
    rw [famη_of_mem_nonpos hy ((mem_O₂_iff _).1 y.2)]
    simp [c]))

lemma ηO_ηO (y : O₂) : ηO (ηO y) = y := by
  rcases le_or_gt y.1.1 0 with hy | hy
  · rw [ηO_of_nonpos y hy, ηO_of_nonpos _ (show ((-1 : ℤˣ) • y).1.1 ≤ 0 from hy), smul_smul]
    simp
  · rw [ηO_of_pos y hy, ηO_of_pos y hy]

lemma ηO_o₂ : ηO o₂ = o₂ := Subtype.ext (Prod.ext rfl (map_zero _))

lemma exists_smul_eq_ηO (y : O₂) : ∃ k : ℤˣ, k • y = ηO y := by
  rcases le_or_gt y.1.1 0 with hy | hy
  · exact ⟨-1, (ηO_of_nonpos y hy).symm⟩
  · exact ⟨1, by rw [one_smul, ηO_of_pos y hy]⟩

theorem continuous_ηO : Continuous ηO := by
  have h : Continuous fun q : JumpingRetract.E 0 => famη q.1 0 q.2 := isLossFamily_famη.continuous 0
  exact Continuous.subtype_mk ((continuous_subtype_val (p := (· ∈ O₂))).fst.prodMk
    (h.comp continuous_subtype_val)) _

theorem isScSmoothMap_ηO : P₂.IsScSmoothMap P₂ ηO := by
  refine isScSmoothMap_of_retractMap continuous_ηO
    ((isScSmoothRetractMap_iff_exists Rt₂.isScRetract).2 ⟨fun q _ => famη_mem q, Rt₂, rfl, ?_⟩)
    fun _ => rfl
  exact IsScSmooth.comp (isScDomain_univ _) (isScDomain_univ _)
    isLossFamily_famη.isScSmooth_famRetr Rt₂.isScSmooth (mapsTo_univ _ _)

/-- `η` is an sc-diffeomorphism of `Σ`, its own inverse. -/
theorem isScDiffeoOn_ηO : P₂.IsScDiffeoOn P₂ ηO ηO univ univ :=
  ⟨isScSmoothMap_ηO, isScSmoothMap_ηO, mapsTo_univ _ _, mapsTo_univ _ _,
    fun y _ => ηO_ηO y, fun y _ => ηO_ηO y⟩

/-- `|η(y)| = |y|`. -/
theorem π_ηO (y : O₂) : X₂.π (ηO y) = X₂.π y := by
  obtain ⟨k, hk⟩ := exists_smul_eq_ηO y
  exact X₂.π_eq_π_iff.2 (GroupoidStr.Isomorphic.symm ⟨(k, y), rfl, hk⟩)

/-! ### `η` is not given by the group near `0` -/

/-- `−1` moves every point with `z ≠ 0`. -/
lemma neg_smul_ne {y : O₂} (hz : y.1.2 ≠ 0) : (-1 : ℤˣ) • y ≠ y := fun h => hz <| by
  have h1 : c (-1) • y.1.2 = y.1.2 := congrArg (fun p : O₂ => p.1.2) h
  have h2 : (2 : ℝ) • y.1.2 = 0 := by
    rw [two_smul]; nth_rw 1 [← h1]; simp [c]
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

lemma ptz_ne_zero (n : ℕ) : node n • δv (nk n) ≠ 0 := fun h => by
  have h1 := congrArg (fun z : c0 => z (nk n)) h
  simp only [ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, δv_apply, ite_true, smul_eq_mul,
    mul_one, ZeroAtInftyContinuousMap.coe_zero, Pi.zero_apply] at h1
  exact (node_pos n).ne' h1

lemma tendsto_ptz : Tendsto (fun n => node n • δv (nk n)) atTop (𝓝 (0 : c0)) := by
  have hnode : Tendsto node atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
    (fun k => ?_) hnode)
  refine (norm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs, abs_of_pos (node_pos k)]
  exact mul_le_of_le_one_right (node_pos k).le (norm_δv_le _)

/-- The points `(±1/(n+1), (1/(n+1)) e_{n'})` of `Σ`. -/
def ptσ (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (n : ℕ) : O₂ :=
  ⟨(σ * node n, node n • δv (nk n)), by
    rw [mem_O₂_iff]
    change fam₂ (σ * node n) 0 (node n • δv (nk n)) = node n • δv (nk n)
    rcases hσ with rfl | rfl
    · rw [one_mul, fam₂_of_pos (node_pos n)]; exact fam_node_smul_δv n (node n)
    · rw [fam₂_of_neg (by have := node_pos n; linarith), neg_one_mul, neg_neg]
      exact fam_node_smul_δv n (node n)⟩

lemma tendsto_ptσ (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) : Tendsto (ptσ σ hσ) atTop (𝓝 o₂) := by
  rw [tendsto_subtype_rng]
  have hnode : Tendsto node atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h := (hnode.const_mul σ).prodMk_nhds tendsto_ptz
  rw [mul_zero] at h
  exact h

/-- On no neighbourhood of `0` is `η` the action of one `k ∈ ℤ/2`. -/
theorem exists_ηO_ne_smul {V : Set O₂} (hV : V ∈ 𝓝 o₂) (k : ℤˣ) : ∃ y ∈ V, ηO y ≠ k • y := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · obtain ⟨n, hn⟩ := ((tendsto_ptσ (-1) (Or.inr rfl)).eventually hV).exists
    refine ⟨_, hn, ?_⟩
    have hneg : (ptσ (-1) (Or.inr rfl) n).1.1 ≤ 0 := by
      change -1 * node n ≤ 0; have := node_pos n; linarith
    rw [ηO_of_nonpos _ hneg, one_smul]
    exact neg_smul_ne (ptz_ne_zero n)
  · obtain ⟨n, hn⟩ := ((tendsto_ptσ 1 (Or.inl rfl)).eventually hV).exists
    refine ⟨_, hn, ?_⟩
    have hpos : 0 < (ptσ 1 (Or.inl rfl) n).1.1 := by
      change 0 < 1 * node n; rw [one_mul]; exact node_pos n
    rw [ηO_of_pos _ hpos]
    exact (neg_smul_ne (ptz_ne_zero n)).symm

/-- **2021 Remark 10.1.8, p. 467, and Appendix 10.6.3, p. 519 (new in the 2021 edition)**:
for the finite group `ℤ/2` acting on the M-polyfold `Σ` by sc-diffeomorphisms, the map `η` is an
sc-diffeomorphism `Σ → Σ` fixing `0` with `|η(y)| = |y|` for all `y`, and on no neighbourhood of
`0` is it `y ↦ k ∗ y` for an element `k ∈ ℤ/2`. -/
theorem remark_10_1_8 :
    P₂.IsScDiffeoOn P₂ ηO ηO univ univ ∧ ηO o₂ = o₂ ∧ (∀ y, X₂.π (ηO y) = X₂.π y) ∧
      ∀ V ∈ 𝓝 o₂, ∀ k : ℤˣ, ∃ y ∈ V, ηO y ≠ k • y :=
  ⟨isScDiffeoOn_ηO, ηO_o₂, π_ηO, fun _ hV k => exists_ηO_ne_smul hV k⟩

/-! ### `ℤ/2 ⋉ Σ` does not have (LR) -/

/-- In a natural representation at `0`, `Φ(g)` is the action of the group element of `g`
(the first entry of `Γ(g, ·)` is locally constant on the connected `U(0)`). -/
lemma naturalRep_Φ_eq (R : X₂.NaturalRep o₂) (g : X₂.Isotropy o₂) {y : O₂} (hy : y ∈ R.U) :
    R.Φ g y = g.val.1 • y := by
  have hc : ContinuousOn (fun z => (R.Γ g z).1) R.U :=
    continuous_fst.comp_continuousOn (R.isScSmoothOn_Γ g).continuousOn
  have h1 : (R.Γ g y).1 = (R.Γ g o₂).1 :=
    R.isConnected_U.isPreconnected.constant hc hy R.mem_U
  rw [R.Γ_self] at h1
  have h2 : (R.Γ g y).2 = y := R.src_Γ g y hy
  rw [← R.tgt_Γ g y hy]
  change (R.Γ g y).1 • (R.Γ g y).2 = _
  rw [h1, h2]

/-- **`ℤ/2 ⋉ Σ` does not have the local regularity property** (Definition 7.4.19): every
natural representation `U(0)` is preserved by `η`, and `η|U(0)` is not `y ↦ g ∗ y`. -/
theorem not_isLR : ¬ X₂.IsLR := by
  intro h
  obtain ⟨R, -, hR⟩ := h o₂ univ isOpen_univ (mem_univ _)
  let gm : X₂.Isotropy o₂ := ⟨((-1 : ℤˣ), o₂), rfl, by
    change (-1 : ℤˣ) • o₂ = o₂
    exact (ηO_of_nonpos o₂ le_rfl).symm.trans ηO_o₂⟩
  have hmaps : MapsTo ηO R.U R.U := fun y hy => by
    rcases le_or_gt y.1.1 0 with hy0 | hy0
    · rw [ηO_of_nonpos y hy0, ← naturalRep_Φ_eq R gm hy]
      exact R.mapsTo_Φ gm hy
    · rwa [ηO_of_pos y hy0]
  have hd : X₂.PObj.IsScDiffeoOn X₂.PObj ηO ηO R.U R.U :=
    ⟨isScSmoothMap_ηO.mono R.isOpen_U (subset_univ _),
      isScSmoothMap_ηO.mono R.isOpen_U (subset_univ _), hmaps, hmaps,
      fun y _ => ηO_ηO y, fun y _ => ηO_ηO y⟩
  obtain ⟨g, hg⟩ := hR ηO ηO hd fun y _ => π_ηO y
  obtain ⟨y, hy, hne⟩ := exists_ηO_ne_smul (R.isOpen_U.mem_nhds R.mem_U) g.val.1
  exact hne ((hg y hy).trans (naturalRep_Φ_eq R g hy))

end EpGroupoid.Examples.ZhouSigma

end Polyfold
