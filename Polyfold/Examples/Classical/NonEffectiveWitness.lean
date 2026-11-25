import Polyfold.Examples.Classical.NonEffectiveEffCount
import Polyfold.Examples.Classical.CyclicData

/-!
# The classical reduction without effectiveness: `z ↦ z^k` on `ℂ/(ℤ/2 × ℤ/p)`

Theorem 16.6.6, 2021 p. 739 (index `0`), for `G = ℤ/2 × ℤ/p` acting on `ℂ = ℝ²` through the
projection to `ℤ/p` (weight `1`), with the fibre action of weight `k` of `ℤ/p` (so `ℤ/2` acts
trivially on base and fibre), and the section `z ↦ z^k`, `k ≥ 1`.  The kernel of the action is
`K = ℤ/2 × {1}`, so `G ⋉ ℂ` is not effective.

## What is formalized (namespace `Polyfold.Examples.Classical.NonEffective.Witness`)

* Scoped instances: `DistribMulAction (G2 p) (Fin 2 → ℝ)`, `(a, g) • x = g • x`, and
  `SMulCommClass`; `σ2 p k (a, g) = σk p k g`.
* `card_baseKernel_G2`: `♯K = 2`; `card_G2`: `♯G = 2p`.
* `c₂ p k = cE.symm (t/2)`, `t = tc p k`: `gNorm_σ2_c₂` (`= 1`), `surjective_fderiv_powMap_c₂`
  (a regular value), `classicalCount_powMap_c₂` (`= k/(2p)`).
* `isLRLocal_EG_σ2n`: for a fibre action `σ2n` nontrivial on `K`, the bundle still has the local
  regularity property.
* **`count_countEff_powMap`**: an admissible perturbed solution set with the canonical orientation
  exists, and every such `Q` has `Q.count 1 = k/(2p)` and `Q.countEff 1 = k/p`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function

noncomputable section

namespace Polyfold.Examples.Classical.NonEffective.Witness

open StrongPolyfoldBundle PolyfoldClass Polyfold.Examples.Classical.Cyclic
open Polyfold.Examples.OrbifoldSquare (cE rot rot_apply surjective_rot)

variable (p : ℕ) [NeZero p] (k : ℕ)

/-- `ℤ/2 × ℤ/p`. -/
abbrev G2 : Type := Gp 2 × Gp p

/-- `ℤ/2 × ℤ/p` acts on `ℝ² = ℂ` through `ℤ/p`: `(a, g) · z = ζ_p^g z`. -/
scoped instance instDistribMulAction2 : DistribMulAction (G2 p) (Fin 2 → ℝ) :=
  DistribMulAction.compHom (Fin 2 → ℝ) (MonoidHom.snd (Gp 2) (Gp p))

theorem smul_def2 (q : G2 p) (x : Fin 2 → ℝ) : q • x = q.2 • x := rfl

scoped instance instSMulCommClass2 : SMulCommClass (G2 p) ℝ (Fin 2 → ℝ) where
  smul_comm q r x := smul_comm q.2 r x

/-- The fibre action `σ2 (a, g) = σk g` of weight `k` (trivial on `ℤ/2`). -/
def σ2 : G2 p →* ((Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) :=
  (σk p k).comp (MonoidHom.snd (Gp 2) (Gp p))

theorem σ2_apply (q : G2 p) : σ2 p k q = σk p k q.2 := rfl

theorem card_G2 : Fintype.card (G2 p) = 2 * p := by
  rw [Fintype.card_prod, card_Gp, card_Gp]

/-- **`K = ℤ/2 × {1}`, `♯K = 2`.** -/
theorem card_baseKernel_G2 : Nat.card (baseKernel (G2 p) 2) = 2 := by
  have e : baseKernel (G2 p) 2 ≃ Gp 2 :=
    { toFun := fun q => q.1.1
      invFun := fun a => ⟨(a, 1), fun z => one_smul (Gp p) z⟩
      left_inv := fun q => by
        refine Subtype.ext (Prod.ext rfl ?_)
        have h : ∀ z : Fin 2 → ℝ, q.1.2 • z = (1 : Gp p) • z := fun z =>
          (q.2 z).trans (one_smul (Gp p) z).symm
        exact (FaithfulSMul.eq_of_smul_eq_smul h).symm
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, card_Gp]

theorem hdet_σ2 (q : G2 p) :
    0 < LinearMap.det (rhoL (n := 2) q : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) *
      LinearMap.det (σ2 p k q : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) :=
  hdet_σk p k q.2

theorem powMap_smul2 (q : G2 p) (x : Fin 2 → ℝ) :
    powMap k (q • x) = σ2 p k q (powMap k x) :=
  powMap_smul p k q.2 x

/-! ### The value `c₂` -/

/-- `c₂ = t/2 ∈ ℂ`, `t = tc p k`. -/
def c₂ : Fin 2 → ℝ := cE.symm ((tc p k / 2 : ℝ) : ℂ)

theorem c₂_eq_smul : c₂ p k = (tc p k / 2) • cE.symm 1 := by
  rw [c₂, ← map_smul, Complex.real_smul, mul_one]

theorem gNorm_σ2_c₂ : gNorm (σ2 p k) (c₂ p k) = 1 := by
  have h1 : ∑ g : Gp p, ‖σk p k g (cE.symm 1)‖ = (tc p k)⁻¹ := by
    rw [tc, inv_inv]
    rfl
  have h2 : gNorm (σ2 p k) (c₂ p k) =
      ∑ _a : Gp 2, ∑ g : Gp p, ‖σk p k g (c₂ p k)‖ := Fintype.sum_prod_type _
  rw [h2, Finset.sum_const, Finset.card_univ, card_Gp, c₂_eq_smul]
  simp only [map_smul, norm_smul, Real.norm_eq_abs, ← Finset.mul_sum, h1]
  rw [abs_of_pos (by have := tc_pos p k; positivity)]
  have := (tc_pos p k).ne'
  field_simp
  norm_num

theorem tc2_ne_zero : ((tc p k / 2 : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (by have := tc_pos p k; positivity)

variable {p k}

theorem powMap_eq_c₂_iff (x : Fin 2 → ℝ) :
    powMap k x = c₂ p k ↔ cE x ^ k = ((tc p k / 2 : ℝ) : ℂ) := by
  rw [powMap, c₂, cE.symm.injective.eq_iff]

/-- **`c₂` is a regular value of `z ↦ z^k`.** -/
theorem surjective_fderiv_powMap_c₂ (hk : 0 < k) (x : Fin 2 → ℝ) (hx : powMap k x = c₂ p k) :
    Surjective (fderiv ℝ (powMap k) x) := by
  rw [fderiv_powMap]
  refine surjective_rot (mul_ne_zero (Nat.cast_ne_zero.2 hk.ne') (pow_ne_zero _ fun h0 => ?_))
  have hx' := (powMap_eq_c₂_iff x).1 hx
  rw [h0, zero_pow hk.ne'] at hx'
  exact tc2_ne_zero p k hx'.symm

theorem preimage_powMap_c₂ (hk : 0 < k) :
    powMap k ⁻¹' {c₂ p k} =
      cE.symm '' ↑(Polynomial.nthRootsFinset k ((tc p k / 2 : ℝ) : ℂ)) := by
  ext x
  rw [ContinuousLinearEquiv.image_symm_eq_preimage, mem_preimage, mem_preimage,
    mem_singleton_iff, powMap_eq_c₂_iff, Finset.mem_coe, Polynomial.mem_nthRootsFinset hk]

/-- **The classical count of `z ↦ z^k` on `ℂ/(ℤ/2 × ℤ/p)` is `k/(2p)`.** -/
theorem classicalCount_powMap_c₂ (hk : 0 < k) :
    classicalCount (G2 p) (powMap k) (c₂ p k) = (k : ℝ) / (2 * p) := by
  unfold classicalCount
  rw [preimage_powMap_c₂ hk, finsum_mem_image cE.symm.injective.injOn, finsum_mem_coe_finset,
    Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) fun z hz => ?_, Finset.sum_const,
    card_nthRootsFinset hk (tc2_ne_zero p k), card_G2, nsmul_eq_mul, mul_one, div_eq_inv_mul]
  · push_cast
    rfl
  have hz' : z ^ k = ((tc p k / 2 : ℝ) : ℂ) := (Polynomial.mem_nthRootsFinset hk _).1 hz
  have hz0 : z ≠ 0 := fun h0 => by
    rw [h0, zero_pow hk.ne'] at hz'
    exact tc2_ne_zero p k hz'.symm
  rw [det_fderiv_powMap, ContinuousLinearEquiv.apply_symm_apply,
    sign_pos (Complex.normSq_pos.2 (mul_ne_zero (Nat.cast_ne_zero.2 hk.ne')
      (pow_ne_zero _ hz0)))]
  rfl

/-- **`z ↦ z^k` on `ℂ/(ℤ/2 × ℤ/p)`, a non-effective case of Theorem 16.6.6 (2021 p. 739, index
`0`)**: `ℤ/2` acts trivially on base and fibre, `K = ℤ/2 × {1}`.  An admissible perturbed
solution set with the canonical orientation exists, and every such `Q` has
`Q.count 1 = k/(2p)` and `Q.countEff 1 = k/p`. -/
theorem count_countEff_powMap (hk : 0 < k) :
    (∃ Q : PointOrientedPerturbation
        (clFredholmSection (σ2 p k) (contDiff_powMap k) (powMap_smul2 p k)).1,
      Q.t = tG (σ2 p k) (c₂ p k) ∧
      Q.IsAdmissible (nG (σ2 p k)) (univ : Set (AG (σ2 p k)).X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet
        (clOrientationRep (σ2 p k) (contDiff_powMap k) (powMap_smul2 p k) (hdet_σ2 p k)) Q) ∧
    ∀ Q : PointOrientedPerturbation
        (clFredholmSection (σ2 p k) (contDiff_powMap k) (powMap_smul2 p k)).1,
      Q.IsAdmissible (nG (σ2 p k)) (univ : Set (AG (σ2 p k)).X.OrbitSpace) →
      IsCanonicalPointSolutionSet
        (clOrientationRep (σ2 p k) (contDiff_powMap k) (powMap_smul2 p k) (hdet_σ2 p k)) Q →
      Q.count (clOne (σ2 p k)) = (k : ℝ) / (2 * p) ∧
        Q.countEff (clOne (σ2 p k)) = (k : ℝ) / p := by
  obtain ⟨hex, hall⟩ := count_countEff_eq_classicalCount (σ2 p k) (hdet_σ2 p k)
    (contDiff_powMap k) (powMap_smul2 p k) (isCompact_preimage_powMap hk)
    (surjective_fderiv_powMap_c₂ hk) (gNorm_σ2_c₂ p k).le
  refine ⟨hex, fun Q hQ hcan => ?_⟩
  obtain ⟨h1, h2⟩ := hall Q hQ hcan
  rw [classicalCount_powMap_c₂ hk] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  rw [card_baseKernel_G2]
  have : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
  field_simp
  push_cast
  ring

/-! ### A fibre action nontrivial on `K` -/

variable (p k)

/-- `σ2n (a, g) = ζ₂^a ζ_p^{k g}`: `ℤ/2 × {1} = K` acts on the fibre by `±1`. -/
def σ2n : G2 p →* ((Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) :=
  rotHom.comp ((χHom 2).comp (MonoidHom.fst (Gp 2) (Gp p)) *
    ((powMonoidHom k).comp (χHom p)).comp (MonoidHom.snd (Gp 2) (Gp p)))

/-- **The local regularity of the bundle does not need a condition on `σ|K`**: for `σ2n`, which
is nontrivial on `K`, `ℝ² × ℝ² → ℝ²` over the non-effective `G2 p ⋉ ℝ²` has the local regularity
property (Definition 8.4.2, 2021 p. 382).  A regular value of an equivariant map then has empty
preimage (`preimage_eq_empty_of_ne_one`). -/
theorem isLRLocal_EG_σ2n :
    (EG (σ2n p k)).IsLRLocal ∧ ∃ q ∈ baseKernel (G2 p) 2, σ2n p k q ≠ 1 := by
  refine ⟨isLRLocal_EG _, (Multiplicative.ofAdd 1, 1), fun z => one_smul (Gp p) z, fun h => ?_⟩
  have h1 := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) => cE (L (cE.symm 1))) h
  simp only [σ2n, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.coe_fst,
    MonoidHom.coe_snd, map_one, mul_one, ContinuousLinearMap.one_apply] at h1
  change cE (rot (χp 2 (Multiplicative.ofAdd 1)) (cE.symm 1)) = cE (cE.symm 1) at h1
  rw [rot_apply, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
    mul_one, ← χp_one 2] at h1
  exact absurd (χp_injective 2 h1) (by decide)

end Polyfold.Examples.Classical.NonEffective.Witness
