import Polyfold.Examples.Classical.ClassicalSum
import Polyfold.Examples.Classical.Perturbation
import Polyfold.Examples.OrbifoldSquareAlgebra
import Mathlib.RingTheory.Complex
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# The classical reduction: `z ↦ z^k` and `z ↦ z̄^k` on `ℂ/ℤₚ`

Data for the comparison of Theorem 16.6.6, 2021 p. 739 (index `0`) with the classical count,
in the cyclic case.  `G = ℤ/p` (written multiplicatively, `p ≠ 0`) acts on `V = ℂ = ℝ²` with
weight `1`, `g · z = ζ_p^g z`, `ζ_p = exp(2πi/p)`; the fibre `W = ℂ` carries the weight `k`
action `σk p k` (for `z ↦ z^k`) or the weight `−k` action `σnk p k` (for `z ↦ z̄^k`).

## What is formalized (namespace `Polyfold.Examples.Classical.Cyclic`)

* `Gp p = Multiplicative (ZMod p)`, `ζp p`, the character `χp p g = ζ_p^g`: `χp_mul`,
  `χp_injective`, `norm_χp`, `conj_χp` (`conj χ(g) = χ(g⁻¹)`).
* Scoped instances: `DistribMulAction (Gp p) (Fin 2 → ℝ)` (`g • x = rot (χp p g) x`),
  `SMulCommClass (Gp p) ℝ (Fin 2 → ℝ)`, `FaithfulSMul (Gp p) (Fin 2 → ℝ)`; `Gp p` is finite
  and discrete through Mathlib's instances.
* `σk p k g = rot (χ(g)^k)`, `σnk p k g = rot (χ(g⁻¹)^k)`; `hdet_σk`, `hdet_σnk`:
  `0 < det(g •) · det(σ g)`.
* `powMap k z = z^k`, `conjPowMap k z = z̄^k` (through `cE`): `contDiff_powMap`,
  `powMap_smul` (`φ(g • z) = σk g φ(z)`), `isCompact_preimage_powMap`, `fderiv_powMap`
  (`w ↦ k z^{k−1} w`), `det_fderiv_powMap` (`= |k z^{k−1}|²`), and the same for `conjPowMap`
  (`w ↦ k z̄^{k−1} w̄`, determinant `−|k z^{k−1}|²`).
* `c₀ p k = cE.symm t`, `t = 1 / gNorm (σk p k) (cE.symm 1) > 0`: `gNorm_σk_c₀`,
  `gNorm_σnk_c₀` (`= 1`); `surjective_fderiv_powMap`, `surjective_fderiv_conjPowMap`: `c₀` is
  a regular value of both maps.
* **`classicalCount_powMap`**: `classicalCount (Gp p) (powMap k) (c₀ p k) = k / p`, and
  **`classicalCount_conjPowMap`**: `classicalCount (Gp p) (conjPowMap k) (c₀ p k) = −(k / p)`
  (the fibre is the `k` roots of `t`; `sign det Dφ = 1`, resp. `−1`, at each).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Complex

open scoped ContDiff Real ComplexConjugate

noncomputable section

namespace Polyfold.Examples.Classical.Cyclic

open Polyfold.Examples.OrbifoldSquare (cE rot rot_apply cE_rot rot_one rot_mul surjective_rot)

/-! ### The group and its character -/

variable (p : ℕ) [NeZero p]

/-- `ℤ/p`, written multiplicatively. -/
abbrev Gp : Type := Multiplicative (ZMod p)

/-- `ζ_p = exp(2πi/p)`. -/
def ζp : ℂ := Complex.exp (2 * π * I / (p : ℕ))

theorem isPrimitiveRoot_ζp : IsPrimitiveRoot (ζp p) p :=
  Complex.isPrimitiveRoot_exp p (NeZero.ne p)

theorem ζp_ne_zero : ζp p ≠ 0 := Complex.exp_ne_zero _

/-- The character `χ(g) = ζ_p^g` of `ℤ/p`. -/
def χp (g : Gp p) : ℂ := ζp p ^ (Multiplicative.toAdd g).val

theorem χp_one : χp p 1 = 1 := by
  change ζp p ^ (0 : ZMod p).val = 1
  rw [ZMod.val_zero, pow_zero]

theorem χp_mul (g h : Gp p) : χp p (g * h) = χp p g * χp p h := by
  change ζp p ^ (Multiplicative.toAdd g + Multiplicative.toAdd h).val = _
  rw [χp, χp, ← pow_add, ZMod.val_add]
  exact (pow_eq_pow_mod _ (isPrimitiveRoot_ζp p).pow_eq_one).symm

theorem χp_ne_zero (g : Gp p) : χp p g ≠ 0 := pow_ne_zero _ (ζp_ne_zero p)

theorem χp_injective : Injective (χp p) := fun _ _ hgh =>
  Multiplicative.toAdd.injective
    (ZMod.val_injective p ((isPrimitiveRoot_ζp p).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hgh))

theorem norm_χp (g : Gp p) : ‖χp p g‖ = 1 := by
  rw [χp, norm_pow, (isPrimitiveRoot_ζp p).norm'_eq_one (NeZero.ne p), one_pow]

/-- `conj χ(g) = χ(g⁻¹)`. -/
theorem conj_χp (g : Gp p) : conj (χp p g) = χp p g⁻¹ := by
  refine mul_left_cancel₀ (χp_ne_zero p g) ?_
  rw [← χp_mul, mul_inv_cancel, χp_one, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_χp,
    one_pow, Complex.ofReal_one]

/-- The character as a monoid hom. -/
def χHom : Gp p →* ℂ where
  toFun := χp p
  map_one' := χp_one p
  map_mul' := χp_mul p

/-! ### The base action -/

/-- `ℤ/p` acts on `ℝ² = ℂ` by `g · z = ζ_p^g z`. -/
scoped instance instDistribMulAction : DistribMulAction (Gp p) (Fin 2 → ℝ) where
  smul g x := rot (χp p g) x
  one_smul x := by
    change rot (χp p 1) x = x
    rw [χp_one, rot_one]
  mul_smul g h x := by
    change rot (χp p (g * h)) x = rot (χp p g) (rot (χp p h) x)
    rw [χp_mul, rot_mul]
  smul_zero g := map_zero (rot (χp p g))
  smul_add g x y := map_add (rot (χp p g)) x y

theorem smul_def (g : Gp p) (x : Fin 2 → ℝ) : g • x = rot (χp p g) x := rfl

scoped instance instSMulCommClass : SMulCommClass (Gp p) ℝ (Fin 2 → ℝ) where
  smul_comm g r x := map_smul (rot (χp p g)) r x

scoped instance instFaithfulSMul : FaithfulSMul (Gp p) (Fin 2 → ℝ) where
  eq_of_smul_eq_smul {g h} hgh := by
    have h1 := hgh (cE.symm 1)
    rw [smul_def, smul_def, rot_apply, rot_apply, ContinuousLinearEquiv.apply_symm_apply,
      mul_one, mul_one] at h1
    exact χp_injective p (cE.symm.injective h1)

/-- `Gp p` is finite and discrete through Mathlib's instances. -/
theorem discreteTopology_Gp : DiscreteTopology (Gp p) := inferInstance

theorem card_Gp : Fintype.card (Gp p) = p := by
  rw [Fintype.card_multiplicative, ZMod.card]

/-! ### The fibre actions -/

/-- `c ↦ rot c` as a monoid hom. -/
def rotHom : ℂ →* ((Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) where
  toFun := rot
  map_one' := ContinuousLinearMap.ext rot_one
  map_mul' a b := ContinuousLinearMap.ext (rot_mul a b)

variable (k : ℕ)

/-- The weight `k` action on the fibre: `σk g w = ζ_p^{k g} w`. -/
def σk : Gp p →* ((Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) :=
  rotHom.comp ((powMonoidHom k).comp (χHom p))

/-- The weight `−k` action on the fibre: `σnk g w = ζ_p^{−k g} w`. -/
def σnk : Gp p →* ((Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) :=
  rotHom.comp ((powMonoidHom k).comp ((χHom p).comp invMonoidHom))

theorem σk_apply (g : Gp p) : σk p k g = rot (χp p g ^ k) := rfl

theorem σnk_apply (g : Gp p) : σnk p k g = rot (χp p g⁻¹ ^ k) := rfl

/-! ### Determinants -/

/-- The real determinant of `z ↦ c z` is `|c|²`. -/
theorem det_rot (c : ℂ) :
    LinearMap.det (rot c : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) = Complex.normSq c := by
  have h : (rot c : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) =
      (cE.symm.toLinearEquiv : ℂ →ₗ[ℝ] (Fin 2 → ℝ)) ∘ₗ Algebra.lmul ℝ ℂ c ∘ₗ
        (cE.symm.toLinearEquiv.symm : (Fin 2 → ℝ) →ₗ[ℝ] ℂ) := by
    ext x : 1
    rfl
  rw [h, LinearMap.det_conj, ← Algebra.norm_apply, Algebra.norm_complex_apply]

/-- Complex conjugation on `ℝ² = ℂ`. -/
def conjR : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (cE.symm : ℂ →L[ℝ] (Fin 2 → ℝ)).comp
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (cE : (Fin 2 → ℝ) →L[ℝ] ℂ))

theorem conjR_apply (x : Fin 2 → ℝ) : conjR x = cE.symm (conj (cE x)) := rfl

theorem det_conjR :
    LinearMap.det (conjR : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) = -1 := by
  have h : (conjR : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) =
      (cE.symm.toLinearEquiv : ℂ →ₗ[ℝ] (Fin 2 → ℝ)) ∘ₗ conjAe.toLinearEquiv.toLinearMap ∘ₗ
        (cE.symm.toLinearEquiv.symm : (Fin 2 → ℝ) →ₗ[ℝ] ℂ) := by
    ext x : 1
    rfl
  rw [h, LinearMap.det_conj, Complex.det_conjAe]

theorem surjective_conjR : Surjective conjR := fun w =>
  ⟨conjR w, by rw [conjR_apply, conjR_apply, ContinuousLinearEquiv.apply_symm_apply,
    Complex.conj_conj, ContinuousLinearEquiv.symm_apply_apply]⟩

theorem rhoL_eq (g : Gp p) : rhoL (n := 2) g = rot (χp p g) := rfl

/-- `0 < det(g •) · det(σk g)`. -/
theorem hdet_σk (g : Gp p) :
    0 < LinearMap.det (rhoL (n := 2) g : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) *
      LinearMap.det (σk p k g : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) := by
  rw [rhoL_eq, σk_apply, det_rot, det_rot]
  exact mul_pos (Complex.normSq_pos.2 (χp_ne_zero p g))
    (Complex.normSq_pos.2 (pow_ne_zero _ (χp_ne_zero p g)))

/-- `0 < det(g •) · det(σnk g)`. -/
theorem hdet_σnk (g : Gp p) :
    0 < LinearMap.det (rhoL (n := 2) g : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) *
      LinearMap.det (σnk p k g : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) := by
  rw [rhoL_eq, σnk_apply, det_rot, det_rot]
  exact mul_pos (Complex.normSq_pos.2 (χp_ne_zero p g))
    (Complex.normSq_pos.2 (pow_ne_zero _ (χp_ne_zero p g⁻¹)))

/-! ### The maps `z ↦ z^k` and `z ↦ z̄^k` -/

/-- `z ↦ z^k` on `ℝ² = ℂ`. -/
def powMap (x : Fin 2 → ℝ) : Fin 2 → ℝ := cE.symm (cE x ^ k)

/-- `z ↦ z̄^k` on `ℝ² = ℂ`. -/
def conjPowMap (x : Fin 2 → ℝ) : Fin 2 → ℝ := cE.symm (conj (cE x) ^ k)

theorem cE_powMap (x : Fin 2 → ℝ) : cE (powMap k x) = cE x ^ k := by
  rw [powMap, ContinuousLinearEquiv.apply_symm_apply]

theorem cE_conjPowMap (x : Fin 2 → ℝ) : cE (conjPowMap k x) = conj (cE x) ^ k := by
  rw [conjPowMap, ContinuousLinearEquiv.apply_symm_apply]

theorem contDiff_powMap : ContDiff ℝ ∞ (powMap k) :=
  cE.symm.contDiff.comp (cE.contDiff.pow k)

theorem contDiff_conjPowMap : ContDiff ℝ ∞ (conjPowMap k) :=
  cE.symm.contDiff.comp
    (((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp cE.contDiff).pow k)

/-- **Equivariance**: `(ζ^g z)^k = ζ^{k g} z^k`. -/
theorem powMap_smul (g : Gp p) (x : Fin 2 → ℝ) : powMap k (g • x) = σk p k g (powMap k x) := by
  rw [σk_apply, rot_apply, cE_powMap, powMap, smul_def, cE_rot, mul_pow]

/-- **Equivariance**: `(conj (ζ^g z))^k = ζ^{−k g} z̄^k`. -/
theorem conjPowMap_smul (g : Gp p) (x : Fin 2 → ℝ) :
    conjPowMap k (g • x) = σnk p k g (conjPowMap k x) := by
  rw [σnk_apply, rot_apply, cE_conjPowMap, conjPowMap, smul_def, cE_rot, map_mul, conj_χp,
    mul_pow]

/-! ### Properness -/

theorem isCompact_preimage_of_norm_le {f : ℂ → ℂ} (hf : Continuous f)
    (hle : ∀ z, ‖z‖ ≤ 1 + ‖f z‖) {K : Set ℂ} (hK : IsCompact K) : IsCompact (f ⁻¹' K) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine Metric.isCompact_of_isClosed_isBounded (hK.isClosed.preimage hf)
    ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + R)).subset fun z hz => ?_)
  have h1 := hR hz
  rw [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
  linarith [hle z]

theorem isCompact_preimage_cE {f : ℂ → ℂ} (hf : Continuous f)
    (hle : ∀ z, ‖z‖ ≤ 1 + ‖f z‖) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) :
    IsCompact ((fun x => cE.symm (f (cE x))) ⁻¹' K) := by
  have h1 : IsCompact (cE.symm ⁻¹' K) := cE.symm.toHomeomorph.isCompact_preimage.2 hK
  exact cE.toHomeomorph.isCompact_preimage.2 (isCompact_preimage_of_norm_le hf hle h1)

variable {k}

theorem norm_le_one_add_pow (hk : 0 < k) (r : ℝ) (hr : 0 ≤ r) : r ≤ 1 + r ^ k := by
  rcases le_total r 1 with h | h
  · linarith [pow_nonneg hr k]
  · have h1 : r ^ 1 ≤ r ^ k := pow_le_pow_right₀ h hk
    linarith [pow_one r]

/-- **`z ↦ z^k` is proper** (`|z^k| = |z|^k`). -/
theorem isCompact_preimage_powMap (hk : 0 < k) (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) :
    IsCompact (powMap k ⁻¹' K) :=
  isCompact_preimage_cE (continuous_pow k) (fun z => by
    rw [norm_pow]; exact norm_le_one_add_pow hk _ (norm_nonneg z)) hK

/-- **`z ↦ z̄^k` is proper.** -/
theorem isCompact_preimage_conjPowMap (hk : 0 < k) (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) :
    IsCompact (conjPowMap k ⁻¹' K) :=
  isCompact_preimage_cE (f := fun z => conj z ^ k)
    ((Complex.continuous_conj).pow k) (fun z => by
    rw [norm_pow, Complex.norm_conj]; exact norm_le_one_add_pow hk _ (norm_nonneg z)) hK

variable (k)

/-! ### Derivatives -/

/-- The derivative of `z ↦ z^k` at `z` is `w ↦ k z^{k−1} w`. -/
theorem hasFDerivAt_powMap (x : Fin 2 → ℝ) :
    HasFDerivAt (powMap k) (rot ((k : ℂ) * cE x ^ (k - 1))) x := by
  have h2 := (cE.hasFDerivAt (x := x)).pow k
  have h3 := (cE.symm.hasFDerivAt (x := cE x ^ k)).comp x h2
  refine h3.congr_fderiv ?_
  ext v : 1
  change cE.symm ((k • cE x ^ (k - 1)) • cE v) = cE.symm ((k : ℂ) * cE x ^ (k - 1) * cE v)
  congr 1
  simp [smul_eq_mul, nsmul_eq_mul]

theorem fderiv_powMap (x : Fin 2 → ℝ) :
    fderiv ℝ (powMap k) x = rot ((k : ℂ) * cE x ^ (k - 1)) :=
  (hasFDerivAt_powMap k x).fderiv

/-- The derivative of `z ↦ z̄^k` at `z` is `w ↦ k z̄^{k−1} w̄`. -/
theorem hasFDerivAt_conjPowMap (x : Fin 2 → ℝ) :
    HasFDerivAt (conjPowMap k) ((rot ((k : ℂ) * conj (cE x) ^ (k - 1))).comp conjR) x := by
  have h1 : HasFDerivAt (fun y => conj (cE y))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (cE : (Fin 2 → ℝ) →L[ℝ] ℂ)) x :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (cE : (Fin 2 → ℝ) →L[ℝ] ℂ)).hasFDerivAt
  have h2 := h1.pow k
  have h3 := (cE.symm.hasFDerivAt (x := conj (cE x) ^ k)).comp x h2
  refine h3.congr_fderiv ?_
  ext v : 1
  change cE.symm ((k • conj (cE x) ^ (k - 1)) • conj (cE v)) =
    cE.symm ((k : ℂ) * conj (cE x) ^ (k - 1) * cE (cE.symm (conj (cE v))))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  congr 1
  simp [smul_eq_mul, nsmul_eq_mul]

theorem fderiv_conjPowMap (x : Fin 2 → ℝ) :
    fderiv ℝ (conjPowMap k) x = (rot ((k : ℂ) * conj (cE x) ^ (k - 1))).comp conjR :=
  (hasFDerivAt_conjPowMap k x).fderiv

theorem det_fderiv_powMap (x : Fin 2 → ℝ) :
    LinearMap.det (fderiv ℝ (powMap k) x : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) =
      Complex.normSq ((k : ℂ) * cE x ^ (k - 1)) := by
  rw [fderiv_powMap, det_rot]

theorem det_fderiv_conjPowMap (x : Fin 2 → ℝ) :
    LinearMap.det (fderiv ℝ (conjPowMap k) x : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) =
      -Complex.normSq ((k : ℂ) * cE x ^ (k - 1)) := by
  rw [fderiv_conjPowMap, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, det_rot,
    det_conjR, mul_neg_one, map_mul, map_mul, map_pow, map_pow, Complex.normSq_conj]

/-! ### The value `c₀` -/

theorem gNorm_σnk (w : Fin 2 → ℝ) : gNorm (σnk p k) w = gNorm (σk p k) w := by
  unfold gNorm
  exact Equiv.sum_comp (Equiv.inv (Gp p)) (fun g => ‖σk p k g w‖)

theorem gNorm_σk_one_pos : 0 < gNorm (σk p k) (cE.symm 1) :=
  lt_of_le_of_ne (gNorm_nonneg _ _) fun h =>
    one_ne_zero (cE.symm.map_eq_zero_iff.1 ((gNorm_eq_zero_iff _).1 h.symm))

/-- `t = 1 / gNorm (σk p k) (cE.symm 1)`. -/
def tc : ℝ := (gNorm (σk p k) (cE.symm 1))⁻¹

theorem tc_pos : 0 < tc p k := inv_pos.2 (gNorm_σk_one_pos p k)

/-- **The value** `c₀ = t ∈ ℂ`, a real number `t > 0` with `gNorm c₀ = 1`. -/
def c₀ : Fin 2 → ℝ := cE.symm (tc p k : ℂ)

theorem c₀_eq_smul : c₀ p k = tc p k • cE.symm 1 := by
  rw [c₀, ← map_smul, Complex.real_smul, mul_one]

theorem gNorm_σk_c₀ : gNorm (σk p k) (c₀ p k) = 1 := by
  rw [c₀_eq_smul, gNorm_smul, abs_of_pos (tc_pos p k), tc,
    inv_mul_cancel₀ (gNorm_σk_one_pos p k).ne']

theorem gNorm_σnk_c₀ : gNorm (σnk p k) (c₀ p k) = 1 := by
  rw [gNorm_σnk, gNorm_σk_c₀]

/-! ### The fibre over `c₀` -/

variable {p k}

theorem powMap_eq_c₀_iff (x : Fin 2 → ℝ) : powMap k x = c₀ p k ↔ cE x ^ k = (tc p k : ℂ) := by
  rw [powMap, c₀, cE.symm.injective.eq_iff]

theorem conjPowMap_eq_c₀_iff (x : Fin 2 → ℝ) :
    conjPowMap k x = c₀ p k ↔ cE x ^ k = (tc p k : ℂ) := by
  rw [conjPowMap, c₀, cE.symm.injective.eq_iff, ← map_pow, ← Complex.conj_ofReal (tc p k),
    (starRingEnd ℂ).injective.eq_iff, Complex.conj_ofReal]

theorem cE_ne_zero_of_pow_eq (hk : 0 < k) {x : Fin 2 → ℝ} (hx : cE x ^ k = (tc p k : ℂ)) :
    cE x ≠ 0 := fun h0 => by
  rw [h0, zero_pow hk.ne'] at hx
  exact (tc_pos p k).ne' (Complex.ofReal_eq_zero.1 hx.symm)

/-- **`c₀` is a regular value of `z ↦ z^k`**: `Dφ(z) = k z^{k−1} ·` is onto for `z ≠ 0`. -/
theorem surjective_fderiv_powMap (hk : 0 < k) (x : Fin 2 → ℝ) (hx : powMap k x = c₀ p k) :
    Surjective (fderiv ℝ (powMap k) x) := by
  rw [fderiv_powMap]
  exact surjective_rot (mul_ne_zero (Nat.cast_ne_zero.2 hk.ne')
    (pow_ne_zero _ (cE_ne_zero_of_pow_eq hk ((powMap_eq_c₀_iff x).1 hx))))

/-- **`c₀` is a regular value of `z ↦ z̄^k`.** -/
theorem surjective_fderiv_conjPowMap (hk : 0 < k) (x : Fin 2 → ℝ)
    (hx : conjPowMap k x = c₀ p k) : Surjective (fderiv ℝ (conjPowMap k) x) := by
  rw [fderiv_conjPowMap, ContinuousLinearMap.coe_comp]
  refine (surjective_rot (mul_ne_zero (Nat.cast_ne_zero.2 hk.ne') (pow_ne_zero _ ?_))).comp
    surjective_conjR
  rw [map_ne_zero]
  exact cE_ne_zero_of_pow_eq hk ((conjPowMap_eq_c₀_iff x).1 hx)

theorem preimage_powMap (hk : 0 < k) :
    powMap k ⁻¹' {c₀ p k} = cE.symm '' ↑(Polynomial.nthRootsFinset k (tc p k : ℂ)) := by
  ext x
  rw [ContinuousLinearEquiv.image_symm_eq_preimage, mem_preimage, mem_preimage,
    mem_singleton_iff, powMap_eq_c₀_iff, Finset.mem_coe, Polynomial.mem_nthRootsFinset hk]

theorem preimage_conjPowMap (hk : 0 < k) :
    conjPowMap k ⁻¹' {c₀ p k} = cE.symm '' ↑(Polynomial.nthRootsFinset k (tc p k : ℂ)) := by
  ext x
  rw [ContinuousLinearEquiv.image_symm_eq_preimage, mem_preimage, mem_preimage,
    mem_singleton_iff, conjPowMap_eq_c₀_iff, Finset.mem_coe, Polynomial.mem_nthRootsFinset hk]

/-- A nonzero complex number has exactly `k` `k`-th roots. -/
theorem card_nthRootsFinset (hk : 0 < k) {a : ℂ} (ha : a ≠ 0) :
    (Polynomial.nthRootsFinset k a).card = k := by
  classical
  have hζ := Complex.isPrimitiveRoot_exp k hk.ne'
  rw [Polynomial.nthRootsFinset_def, Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup ha),
    hζ.card_nthRoots, if_pos ⟨a ^ ((k : ℂ)⁻¹), Complex.cpow_nat_inv_pow a hk.ne'⟩]

theorem tc_ne_zero : (tc p k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (tc_pos p k).ne'

/-! ### The classical counts -/

/-- **The classical count of `z ↦ z^k` on `ℂ/ℤₚ` is `k / p`**: the fibre over `c₀ = t > 0`
is the `k` roots of `t`, with `det Dφ(z) = |k z^{k−1}|² > 0` at each. -/
theorem classicalCount_powMap (hk : 0 < k) :
    classicalCount (Gp p) (powMap k) (c₀ p k) = (k : ℝ) / p := by
  unfold classicalCount
  rw [preimage_powMap hk, finsum_mem_image cE.symm.injective.injOn, finsum_mem_coe_finset,
    Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) fun z hz => ?_, Finset.sum_const,
    card_nthRootsFinset hk tc_ne_zero, card_Gp, nsmul_eq_mul, mul_one, div_eq_inv_mul]
  have hz' : z ^ k = (tc p k : ℂ) := (Polynomial.mem_nthRootsFinset hk _).1 hz
  have hz0 : z ≠ 0 := fun h0 => by
    rw [h0, zero_pow hk.ne'] at hz'
    exact tc_ne_zero hz'.symm
  rw [det_fderiv_powMap, ContinuousLinearEquiv.apply_symm_apply,
    sign_pos (Complex.normSq_pos.2 (mul_ne_zero (Nat.cast_ne_zero.2 hk.ne')
      (pow_ne_zero _ hz0)))]
  rfl

/-- **The classical count of `z ↦ z̄^k` on `ℂ/ℤₚ` is `−k / p`**: the same fibre, with
`det Dφ(z) = −|k z^{k−1}|² < 0` at each point (conjugation has determinant `−1`). -/
theorem classicalCount_conjPowMap (hk : 0 < k) :
    classicalCount (Gp p) (conjPowMap k) (c₀ p k) = -((k : ℝ) / p) := by
  unfold classicalCount
  rw [preimage_conjPowMap hk, finsum_mem_image cE.symm.injective.injOn, finsum_mem_coe_finset,
    Finset.sum_congr rfl (g := fun _ => (-1 : ℝ)) fun z hz => ?_, Finset.sum_const,
    card_nthRootsFinset hk tc_ne_zero, card_Gp, nsmul_eq_mul, mul_neg_one, div_eq_inv_mul,
    mul_neg]
  have hz' : z ^ k = (tc p k : ℂ) := (Polynomial.mem_nthRootsFinset hk _).1 hz
  have hz0 : z ≠ 0 := fun h0 => by
    rw [h0, zero_pow hk.ne'] at hz'
    exact tc_ne_zero hz'.symm
  rw [det_fderiv_conjPowMap, ContinuousLinearEquiv.apply_symm_apply,
    sign_neg (neg_neg_of_pos (Complex.normSq_pos.2 (mul_ne_zero (Nat.cast_ne_zero.2 hk.ne')
      (pow_ne_zero _ hz0))))]
  rfl

end Polyfold.Examples.Classical.Cyclic
