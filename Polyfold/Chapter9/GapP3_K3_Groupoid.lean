import Polyfold.Chapter9.GapP3_K3_MPolyfold
import Polyfold.Chapter7.SubGroupoid
import Polyfold.Chapter7.ReducedCriterion
import Polyfold.Chapter7.Effective
import Polyfold.Chapter9.Boundary

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §9.5,
**Remark 9.5.20** (pp. 451–452; 2017: Remark 9.8), gap G.110: the ep-groupoid `ℤ/3 ⋉ X` and the
sub-ep-groupoid `∂X`.

# `ℤ/3 ⋉ X`, its effective isotropy, and the effective isotropy of `∂X`

## The text, paraphrased
(p. 451) `ℤ/3` acts on `X` by rotating the `ℂ`-factor, "we obtain the translation groupoid
`ℤ/3 ⋉ X` … which has the LUC property"; on `M = [−1,1] × {0}` the effective isotropy has order `3`.
(p. 452) `∂X = {(−1,0), (1,0)}` is a sub-ep-groupoid; "`G^eff_{x∈X} = ℤ/3`, but
`G^eff_{x∈∂X} = {1}` for `x ∈ ∂X`".

## What is formalized
* `K3.rotC k = ω^k`, `ω = −1/2 + i√3/2`; the action `k • (t, z) = (t, ω^k z)` of
  `K3.Z3 = Multiplicative (ZMod 3)` on `XR`.
* `K3.isScSmoothMap_smul`: it is sc-smooth (in the chart it is the sc-operator `rotOp` rotating
  `(a, b)`).
* **`K3.ε := actionEpGroupoid isScSmoothMap_smul`**, `ℤ/3 ⋉ X`; **`K3.isLUC_ε`** (via
  Proposition 7.2.21: `𝐗^T = {1} × X` is closed, `K3.nonEffectivePart_ε`).
* **`K3.card_effIsotropy_of_snd_eq_zero`**: `#G^eff_x = 3` for `x = (t, 0)`, in particular at the two
  points of `∂X` (`K3.card_effIsotropy_end`); `K3.card_effIsotropy_of_snd_ne_zero`: `= 1` off `M`.
* **`K3.isEpSubgroupoid_ends`**: `∂X = {(−1,0),(1,0)}` is an ep-subgroupoid (Definition 7.1.21:
  a sub-M-polyfold, saturated); **`K3.εB := subEpGroupoid isEpSubgroupoid_ends`**.
* **`K3.card_isotropy_εB`**: `#G_x = 3` in `∂X`, but **`K3.card_effIsotropy_εB`**: `#G^eff_x = 1` in
  `∂X` (every element acts trivially there).  **`K3.remark_9_5_20_effIsotropy`** collects the
  comparison.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology
open scoped Real

noncomputable section

namespace Polyfold

namespace K3

open RemarkFourThree ScOneExample EpGroupoid EpGroupoid.Examples

/-! ### The cube root of unity and the rotations -/

/-- `ω = −1/2 + i √3/2`. -/
def ω : ℂ := ⟨-1 / 2, √3 / 2⟩

lemma sqrt3_sq : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

lemma ω_sq : ω ^ 2 = ⟨-1 / 2, -(√3 / 2)⟩ := by
  apply Complex.ext <;> simp [ω, sq, Complex.mul_re, Complex.mul_im] <;> nlinarith [sqrt3_sq]

lemma ω_pow_three : ω ^ 3 = 1 := by
  rw [pow_succ, ω_sq]
  apply Complex.ext <;> simp [ω, Complex.mul_re, Complex.mul_im] <;> nlinarith [sqrt3_sq]

lemma ω_ne_one : ω ≠ 1 := fun h => by
  have := congrArg Complex.re h
  simp [ω] at this
  norm_num at this

lemma ω_sq_ne_one : ω ^ 2 ≠ 1 := fun h => by
  rw [ω_sq] at h
  have := congrArg Complex.re h
  simp at this
  norm_num at this

lemma ω_pow_mod (n : ℕ) : ω ^ (n % 3) = ω ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, ω_pow_three, one_pow, mul_one]

lemma norm_ω : ‖ω‖ = 1 := by
  have h : ‖ω‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [ω]
    nlinarith [sqrt3_sq]
  have h0 := norm_nonneg ω
  nlinarith

/-- `ℤ/3`. -/
abbrev Z3 : Type := Multiplicative (ZMod 3)

/-- The rotation `ω^k ∈ ℂ` of `k ∈ ℤ/3`. -/
def rotC (k : Z3) : ℂ := ω ^ (Multiplicative.toAdd k).val

lemma rotC_one : rotC 1 = 1 := by
  simp [rotC]

lemma rotC_mul (k l : Z3) : rotC (k * l) = rotC k * rotC l := by
  rw [rotC, rotC, rotC, toAdd_mul, ZMod.val_add, ω_pow_mod, pow_add]

lemma norm_rotC (k : Z3) : ‖rotC k‖ = 1 := by
  rw [rotC, norm_pow, norm_ω, one_pow]

lemma eq_one_of_rotC_eq_one {k : Z3} (h : rotC k = 1) : k = 1 := by
  rcases (show ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 by decide) (Multiplicative.toAdd k)
    with h0 | h1 | h2
  · exact toAdd_eq_zero.1 h0
  · rw [rotC, h1, show ZMod.val (1 : ZMod 3) = 1 from rfl, pow_one] at h
    exact absurd h ω_ne_one
  · rw [rotC, h2, show ZMod.val (2 : ZMod 3) = 2 from rfl] at h
    exact absurd h ω_sq_ne_one

lemma eq_one_of_rotC_mul {k : Z3} {z : ℂ} (hz : z ≠ 0) (h : rotC k * z = z) : k = 1 :=
  eq_one_of_rotC_eq_one (mul_right_cancel₀ hz (by rw [h, one_mul]))

/-! ### The action on `X` -/

lemma rot_mem {x : ℝ × ℂ} (hx : x ∈ Xs) (k : Z3) : (x.1, rotC k * x.2) ∈ Xs := by
  rcases mem_Xs_iff.1 hx with h | h | h
  · rw [h, mul_zero]; exact mem_Xs_iff.2 (Or.inl rfl)
  · rw [h, mul_zero]; exact mem_Xs_iff.2 (Or.inr (Or.inl rfl))
  · refine mem_Xs_iff.2 (Or.inr (Or.inr ⟨h.1, ?_⟩))
    rw [norm_mul, norm_rotC, one_mul]; exact h.2

instance : MulAction Z3 XR where
  smul k x := ⟨(x.1.1, rotC k * x.1.2), rot_mem x.2 k⟩
  one_smul x := Subtype.ext (Prod.ext rfl (by
    change rotC 1 * x.1.2 = x.1.2
    rw [rotC_one, one_mul]))
  mul_smul k l x := Subtype.ext (Prod.ext rfl (by
    change rotC (k * l) * x.1.2 = rotC k * (rotC l * x.1.2)
    rw [rotC_mul, mul_assoc]))

lemma smul_val (k : Z3) (x : XR) : ((k • x : XR) : ℝ × ℂ) = (x.1.1, rotC k * x.1.2) := rfl

lemma smul_eq_self_of_snd_eq_zero (k : Z3) {x : XR} (hx : x.1.2 = 0) : k • x = x :=
  Subtype.ext (Prod.ext rfl (by rw [smul_val, hx, mul_zero]))

lemma continuous_smul_XR (k : Z3) : Continuous fun x : XR => k • x := by
  change Continuous fun x : XR => (⟨(x.1.1, rotC k * x.1.2), rot_mem x.2 k⟩ : XR)
  exact Continuous.subtype_mk ((continuous_subtype_val.fst).prodMk
    ((continuous_subtype_val.snd).const_smul (rotC k))) _

/-! ### The action in the chart: the rotation `rotOp` of `(a, b)` -/

/-- `(a, b) ↦ (c a − s b, s a + c b)` on `Z2 = X ⊕ X`. -/
def rotZ (c s : ℝ) : ScOperator Z2 Z2 where
  lvl m := ((c • ContinuousLinearMap.fst ℝ (X m) (X m) - s • ContinuousLinearMap.snd ℝ (X m) (X m)).prod
    (s • ContinuousLinearMap.fst ℝ (X m) (X m) + c • ContinuousLinearMap.snd ℝ (X m) (X m)))
  incl_comm m x := by
    change (X.incl m (c • x.1 - s • x.2), X.incl m (s • x.1 + c • x.2)) =
      (c • X.incl m x.1 - s • X.incl m x.2, s • X.incl m x.1 + c • X.incl m x.2)
    simp only [map_sub, map_add, map_smul]

/-- The rotation by `ω^k` in the chart: `(p, a, b) ↦ (p, c a − s b, s a + c b)`. -/
def rotOp (k : Z3) : ScOperator E E :=
  ScOperator.prodMap (ScOperator.id _) (rotZ (rotC k).re (rotC k).im)

lemma rotOp_apply (k : Z3) (q : E 0) : rotOp k 0 q =
    (q.1, ((rotC k).re • q.2.1 - (rotC k).im • q.2.2, (rotC k).im • q.2.1 + (rotC k).re • q.2.2)) :=
  rfl

lemma wdisk_rot (k : Z3) (z : ℂ) : wdisk (rotC k * z) = rotC k * wdisk z := by
  rw [wdisk, wdisk, norm_mul, norm_rotC, one_mul, Complex.real_smul, Complex.real_smul]
  ring

lemma chart_smul (k : Z3) (x : XR) : chart (k • x) = rotOp k 0 (chart x) := by
  rw [chart_apply, chart_apply, rotOp_apply, smul_val]
  simp only [ψfun, wdisk_rot, Complex.mul_re, Complex.mul_im]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · simp only [sub_smul, mul_smul]
  · simp only [add_smul, mul_smul]
    abel

/-- **The action of `ℤ/3` on `X` is sc-smooth**: in the chart it is the sc-operator `rotOp k`. -/
theorem isScSmoothMap_smul (k : Z3) : P.IsScSmoothMap P fun x : XR => k • x := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ (continuous_smul_XR k).continuousOn
    fun y _ => ⟨chart, chart, univ, isChart_chart, isChart_chart, isOpen_univ, mem_univ _,
      fun z _ => ⟨mem_univ _, mem_univ _⟩, fun z _ => mem_univ _, ?_⟩
  have himg : chart.toPartialEquiv '' univ = O := chart.toPartialEquiv.image_source_eq_target
  have hmaps : MapsTo (rotOp k 0) O O := by
    intro q hq
    obtain ⟨x, -, rfl⟩ := himg.symm ▸ hq
    rw [← chart_smul]
    exact ψfun_mem_O (k • x).2
  have key : IsScSmoothRetractMap E (quadrant 2 Z2 0) O E (quadrant 2 Z2 0) O (rotOp k 0) :=
    (rotOp k).isScSmoothRetractMap Rt.isScRetract hmaps
  rw [himg]
  refine key.congr fun q hq => ?_
  obtain ⟨x, -, rfl⟩ := himg.symm ▸ hq
  change rotOp k 0 (chart x) = chart (k • chart.symm (chart x))
  rw [chart.symm_apply_apply (mem_univ x)]
  exact (chart_smul k x).symm

/-! ### `ℤ/3 ⋉ X` -/

/-- **`ℤ/3 ⋉ X`** (Remark 9.5.20, p. 451): the translation groupoid of the rotation action of `ℤ/3`
on the M-polyfold `X`. -/
abbrev ε : EpGroupoid XR (Z3 × XR) := actionEpGroupoid (P := P) isScSmoothMap_smul

lemma ε_src (φ : Z3 × XR) : ε.src φ = φ.2 := rfl

lemma ε_tgt (φ : Z3 × XR) : ε.tgt φ = φ.1 • φ.2 := rfl

/-- Points with `z ≠ 0` accumulate at every point of `M = [−1,1] × {0}`: `((1−s)t, s) → (t, 0)`. -/
lemma frequently_snd_ne_zero {x : XR} (hx : x.1.2 = 0) : ∃ᶠ y in 𝓝 x, y.1.2 ≠ 0 := by
  set s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) / 2 with hs
  have hs0 : ∀ n, 0 < s n := fun n => by positivity
  have hs1 : ∀ n, s n < 1 := fun n => by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simp only [hs]; linarith
  have hmem : ∀ n, (x.1.1 * (1 - s n), ((s n : ℝ) : ℂ)) ∈ Xs := fun n => by
    have hI := fst_mem_Icc_of_mem x.2
    refine mem_Xs_iff.2 (Or.inr (Or.inr ⟨⟨?_, ?_⟩, ?_⟩))
    · nlinarith [hs0 n, hs1 n, hI.1, hI.2]
    · nlinarith [hs0 n, hs1 n, hI.1, hI.2]
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs0 n)]; exact hs1 n
  set y : ℕ → XR := fun n => ⟨_, hmem n⟩ with hy
  have hst : Tendsto s atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2 : ℝ)
    rw [zero_div] at h
    exact h
  have hyt : Tendsto y atTop (𝓝 x) := by
    refine tendsto_subtype_rng.2 ?_
    have e : x.1 = (x.1.1 * (1 - 0), ((0 : ℝ) : ℂ)) := by
      rw [sub_zero, mul_one, Complex.ofReal_zero, ← hx]
    rw [e]
    exact (tendsto_const_nhds.mul (tendsto_const_nhds.sub hst)).prodMk_nhds
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hst)
  refine hyt.frequently (Frequently.of_forall fun n => ?_)
  change ((s n : ℝ) : ℂ) ≠ 0
  exact Complex.ofReal_ne_zero.2 (hs0 n).ne'

/-- No `k ≠ 1` fixes a neighbourhood of a point of `X`. -/
lemma eq_one_of_eventually {k : Z3} {x : XR} (h : ∀ᶠ y in 𝓝 x, k • y = y) : k = 1 := by
  by_cases hx : x.1.2 = 0
  · obtain ⟨y, hy0, hy⟩ := ((frequently_snd_ne_zero hx).and_eventually h).exists
    exact eq_one_of_rotC_mul hy0 (congrArg (fun y : XR => y.1.2) hy)
  · exact eq_one_of_rotC_mul hx (congrArg (fun y : XR => y.1.2) h.self_of_nhds)

/-- **`T_x = {1}` in `ℤ/3 ⋉ X`**: `g ∈ G_x` acts trivially iff `g = (1, x)`. -/
lemma mem_trivialSet_ε {x : XR} (g : ε.Isotropy x) : g ∈ ε.trivialSet x ↔ g.val.1 = 1 := by
  constructor
  · intro hg
    have h := ε.mem_trivialSet_iff_eventually.1 hg
    have hg2 : g.val = (g.val.1, x) := Prod.ext rfl g.src_val
    have ht : Tendsto (fun y : XR => (g.val.1, y)) (𝓝 x) (𝓝 g.val) := by
      rw [hg2]; exact (continuous_const.prodMk continuous_id).tendsto x
    exact eq_one_of_eventually ((ht.eventually h).mono fun y hy => hy.symm)
  · intro h1
    refine ε.mem_trivialSet_iff_eventually.2 ?_
    filter_upwards [((isOpen_discrete ({1} : Set Z3)).prod isOpen_univ).mem_nhds
      (show g.val ∈ ({1} : Set Z3) ×ˢ (univ : Set XR) from ⟨h1, mem_univ _⟩)] with ψ hψ
    change ψ.2 = ψ.1 • ψ.2
    rw [mem_singleton_iff.1 hψ.1, one_smul]

lemma isotropy_eq_one {x : XR} {g : ε.Isotropy x} (h : g.val.1 = 1) : g = 1 :=
  GroupoidStr.Isotropy.ext (Prod.ext h g.src_val)

/-- **`𝐗^T = {1} × X`** for `ℤ/3 ⋉ X`. -/
theorem nonEffectivePart_ε : ε.nonEffectivePart = {φ | φ.1 = 1} := by
  ext φ
  constructor
  · rintro ⟨x, g, hg, rfl⟩
    exact (mem_trivialSet_ε g).1 hg
  · intro h
    have ht : ε.tgt φ = φ.2 := by
      change φ.1 • φ.2 = φ.2
      rw [show φ.1 = 1 from h, one_smul]
    exact ⟨φ.2, ⟨φ, rfl, ht⟩, (mem_trivialSet_ε _).2 h, rfl⟩

/-- **`ℤ/3 ⋉ X` has the LUC property** (Remark 9.5.20, p. 451), by Proposition 7.2.21: `𝐗^T` is
closed. -/
theorem isLUC_ε : ε.IsLUC := by
  refine ε.proposition_7_2_21.2 ?_
  rw [nonEffectivePart_ε]
  exact isClosed_eq continuous_fst continuous_const

lemma normalClosure_trivialSet_ε (x : XR) :
    Subgroup.normalClosure (ε.trivialSet x) = ⊥ :=
  le_bot_iff.1 (Subgroup.normalClosure_le_normal fun g hg =>
    Subgroup.mem_bot.2 (isotropy_eq_one ((mem_trivialSet_ε g).1 hg)))

lemma card_quotient_of_eq_bot {G : Type*} [Group G] {N : Subgroup G} [N.Normal] (h : N = ⊥) :
    Nat.card (G ⧸ N) = Nat.card G := by
  subst h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (⊥ : Subgroup G), Subgroup.card_bot,
    mul_one]

lemma card_quotient_of_eq_top {G : Type*} [Group G] {N : Subgroup G} [N.Normal] (h : N = ⊤) :
    Nat.card (G ⧸ N) = 1 := by
  subst h
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := ⟨fun a b => by
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    exact QuotientGroup.eq.2 (Subgroup.mem_top _)⟩
  exact Nat.card_of_subsingleton (1 : G ⧸ (⊤ : Subgroup G))

/-- `G^eff_x ≅ G_x ≅ (ℤ/3)_x` in `ℤ/3 ⋉ X`. -/
lemma card_effIsotropy_ε (x : XR) :
    Nat.card (ε.EffIsotropy x) = Nat.card (MulAction.stabilizer Z3 x) := by
  rw [EpGroupoid.EffIsotropy, card_quotient_of_eq_bot (normalClosure_trivialSet_ε x)]
  exact Nat.card_congr (isotropyEquivStabilizer isScSmoothMap_smul x).toEquiv

lemma card_Z3 : Nat.card Z3 = 3 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- **`#G^eff_x = 3` on `M = [−1,1] × {0}`** (Remark 9.5.20, p. 451). -/
theorem card_effIsotropy_of_snd_eq_zero {x : XR} (hx : x.1.2 = 0) :
    Nat.card (ε.EffIsotropy x) = 3 := by
  rw [card_effIsotropy_ε, show MulAction.stabilizer Z3 x = ⊤ from
    eq_top_iff.2 fun k _ => MulAction.mem_stabilizer_iff.2 (smul_eq_self_of_snd_eq_zero k hx),
    Subgroup.card_top, card_Z3]

/-- `#G^eff_x = 1` off `M`. -/
theorem card_effIsotropy_of_snd_ne_zero {x : XR} (hx : x.1.2 ≠ 0) :
    Nat.card (ε.EffIsotropy x) = 1 := by
  rw [card_effIsotropy_ε, show MulAction.stabilizer Z3 x = ⊥ from
    eq_bot_iff.2 fun k hk => Subgroup.mem_bot.2 (eq_one_of_rotC_mul hx
      (congrArg (fun y : XR => y.1.2) (MulAction.mem_stabilizer_iff.1 hk))),
    Subgroup.card_bot]

/-! ### `∂X` as a sub-ep-groupoid -/

lemma snd_eq_zero_of_mem_boundary {x : XR} (hx : x ∈ P.boundary) : x.1.2 = 0 := by
  rw [boundary_eq] at hx
  rcases hx with h | h <;> rw [h]

/-- `#G^eff_x = 3` at the points of `∂X`, read in `X = ℤ/3 ⋉ X`. -/
theorem card_effIsotropy_end {x : XR} (hx : x ∈ P.boundary) : Nat.card (ε.EffIsotropy x) = 3 :=
  card_effIsotropy_of_snd_eq_zero (snd_eq_zero_of_mem_boundary hx)

lemma mem_smooth_of_snd_eq_zero (q : E 0) (h : q.2 = 0) : q ∈ E.smooth := by
  refine (ScScale.mem_smooth_iff _).2 fun m => ⟨((q.1 : V2), (0 : Z2 m)), ?_⟩
  rw [ScBanach.prod_toBase, ScBanach.const_toBase, map_zero]
  exact Prod.ext rfl h.symm

lemma mem_smoothSet_of_snd_eq_zero {x : XR} (hx : x.1.2 = 0) : x ∈ P.smoothSet := by
  rw [MPolyfold.mem_smoothSet_iff_of_isChart isChart_chart (mem_univ x)]
  refine mem_smooth_of_snd_eq_zero _ ?_
  change ((wdisk x.1.2).re • β (τ x.1.1), (wdisk x.1.2).im • β (τ x.1.1)) = 0
  rw [hx, wdisk_zero]
  simp

/-- **`∂X = {(−1,0),(1,0)}` is a sub-M-polyfold of `X`**: near each of its points it is the image
of a constant (sc-smooth) retraction. -/
theorem isSubMPolyfold_boundary : P.IsSubMPolyfold P.boundary := by
  intro a ha
  have ha' := ha
  rw [boundary_eq] at ha'
  have ha1 : a.1.1 * a.1.1 = 1 := by rcases ha' with h | h <;> rw [h] <;> norm_num
  refine ⟨{x | 0 < x.1.1 * a.1.1}, isOpen_lt continuous_const
    ((continuous_fst.comp continuous_subtype_val).mul continuous_const), by
      change 0 < a.1.1 * a.1.1; rw [ha1]; exact one_pos, fun _ => a, fun _ _ => ?_,
    (MPolyfold.isScSmoothMap_const_of_mem_smoothSet'
      (mem_smoothSet_of_snd_eq_zero (snd_eq_zero_of_mem_boundary ha))).mono
      (isOpen_lt continuous_const ((continuous_fst.comp continuous_subtype_val).mul
        continuous_const)) (subset_univ _), fun _ _ => rfl, ?_⟩
  · change 0 < a.1.1 * a.1.1; rw [ha1]; exact one_pos
  · ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      refine ⟨ha, ?_⟩
      change 0 < a.1.1 * a.1.1; rw [ha1]; exact one_pos
    · rintro ⟨hx, hxV⟩
      have hx' := hx
      rw [boundary_eq] at hx'
      change 0 < x.1.1 * a.1.1 at hxV
      refine ⟨a, by change 0 < a.1.1 * a.1.1; rw [ha1]; exact one_pos, ?_⟩
      apply Subtype.ext
      change a.1 = x.1
      rcases ha' with h | h <;> rcases hx' with h' | h'
      · rw [h, h']
      · exfalso; rw [h, h'] at hxV; norm_num at hxV
      · exfalso; rw [h, h'] at hxV; norm_num at hxV
      · rw [h, h']

/-- `∂X` is saturated in `ℤ/3 ⋉ X` (its points are fixed by `ℤ/3`). -/
theorem isSaturated_boundary : ε.IsSaturated P.boundary :=
  ε.isSaturated_iff.2 fun φ hφ => by
    change φ.1 • φ.2 ∈ P.boundary
    have h0 : φ.2.1.2 = 0 := snd_eq_zero_of_mem_boundary hφ
    rw [smul_eq_self_of_snd_eq_zero φ.1 h0]
    exact hφ

/-- **`∂X` is a sub-ep-groupoid of `ℤ/3 ⋉ X`** (Remark 9.5.20, p. 452; Definition 7.1.21). -/
theorem isEpSubgroupoid_boundary : ε.IsEpSubgroupoid P.boundary :=
  ⟨isSubMPolyfold_boundary, isSaturated_boundary⟩

/-- **The ep-groupoid `∂X`** (Proposition 7.1.22): the full subcategory of `ℤ/3 ⋉ X` on `∂X`. -/
abbrev εB := subEpGroupoid isEpSubgroupoid_boundary

/-- **`G_x ≅ ℤ/3` in `∂X`**: the morphisms of `∂X` at `x` are still `(k, x)`, `k ∈ ℤ/3`. -/
def isotropyEquivB (a : P.boundary) : εB.Isotropy a ≃ Z3 where
  toFun g := g.val.val.1
  invFun k := ⟨⟨(k, a.val), a.2, by
      change k • a.val ∈ P.boundary
      rw [smul_eq_self_of_snd_eq_zero k (snd_eq_zero_of_mem_boundary a.2)]; exact a.2⟩,
    rfl, Subtype.ext (smul_eq_self_of_snd_eq_zero k (snd_eq_zero_of_mem_boundary a.2))⟩
  left_inv g := GroupoidStr.Isotropy.ext (Subtype.ext (Prod.ext rfl
    (congrArg Subtype.val g.src_val).symm))
  right_inv _ := rfl

theorem card_isotropy_εB (a : P.boundary) : Nat.card (εB.Isotropy a) = 3 := by
  rw [Nat.card_congr (isotropyEquivB a), card_Z3]

/-- **In `∂X` every element of `G_x` acts trivially**: `s = t` on all of `∂𝐗`. -/
lemma mem_trivialSet_εB {a : P.boundary} (g : εB.Isotropy a) : g ∈ εB.trivialSet a :=
  εB.mem_trivialSet_iff_eventually.2 (Eventually.of_forall fun ψ => Subtype.ext
    (smul_eq_self_of_snd_eq_zero ψ.val.1 (snd_eq_zero_of_mem_boundary ψ.2.1)).symm)

/-- **`G^eff_x = {1}` for `x ∈ ∂X`, read in `∂X`** (Remark 9.5.20, p. 452). -/
theorem card_effIsotropy_εB (a : P.boundary) : Nat.card (εB.EffIsotropy a) = 1 :=
  card_quotient_of_eq_top (eq_top_iff.2 fun g _ =>
    Subgroup.subset_normalClosure (mem_trivialSet_εB g))

/-- **Remark 9.5.20 (2021, pp. 451–452), the effective isotropy of `∂X`**: `X` is an M-polyfold
with `∂X = {(−1,0),(1,0)}`; `ℤ/3 ⋉ X` has the LUC property and `#G^eff_x = 3` on
`M = [−1,1] × {0}`; `∂X` is a sub-ep-groupoid; at `x ∈ ∂X` the isotropy group is `ℤ/3` both in `X`
and in `∂X`, but `#G^eff_x = 3` read in `X` and `#G^eff_x = 1` read in `∂X`. -/
theorem remark_9_5_20_effIsotropy :
    P.boundary = {x | x.1 = (-1, 0) ∨ x.1 = (1, 0)} ∧ ε.IsLUC ∧
      (∀ x : XR, x.1.2 = 0 → Nat.card (ε.EffIsotropy x) = 3) ∧
      ε.IsEpSubgroupoid P.boundary ∧
      ∀ a : P.boundary, Nat.card (ε.Isotropy a) = 3 ∧ Nat.card (εB.Isotropy a) = 3 ∧
        Nat.card (ε.EffIsotropy a) = 3 ∧ Nat.card (εB.EffIsotropy a) = 1 := by
  refine ⟨boundary_eq, isLUC_ε, fun x hx => card_effIsotropy_of_snd_eq_zero hx,
    isEpSubgroupoid_boundary, fun a => ⟨?_, card_isotropy_εB a, card_effIsotropy_end a.2,
      card_effIsotropy_εB a⟩⟩
  exact (Nat.card_congr (isotropyEquivStabilizer isScSmoothMap_smul a.val).toEquiv).trans
    ((card_effIsotropy_ε a.val).symm.trans (card_effIsotropy_end a.2))

end K3

end Polyfold
