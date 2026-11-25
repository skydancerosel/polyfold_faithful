import Polyfold.Examples.Classical.OrientedMain
import Polyfold.Examples.Classical.CyclicData

/-!
# The classical reduction for oriented spaces: `z ↦ z^k` on `ℂ` with its orientation

The hypotheses of `count_eq_orientedClassicalCount` hold in a non-degenerate case: `V = W = ℂ`
as a real space with `Complex.orientation` (the orientation of the basis `1, i`), `G = ℤ/p`
acting on `V` by `z ↦ ζ_p^g z` and on `W` by `w ↦ ζ_p^{k g} w`, `φ z = z^k` (`k ≥ 1`), and
the value `c = t`, the real number `t > 0` of `CyclicData`.  The coordinates are
`eC : ℂ ≃L[ℝ] ℝ²`, `a + b i ↦ (a, b)`.

## What is formalized (namespace `Polyfold.Examples.Classical.Oriented`)

* `orientation_map_eC`: `eC` carries `Complex.orientation` to the standard orientation of `ℝ²`.
* `injective_ρC`, `hdet_ρC_σC`, `contDiff_powC`, `powC_smul`, `isCompact_preimage_powC`,
  `surjective_fderiv_powC`, `sum_norm_σC_le`: the hypotheses.
* **`orientedClassicalCount_powC`**: the oriented classical count is `k / p`.
* **`count_powC`**: for the transported section an admissible perturbed solution set with the
  canonical orientation exists, and every such `Q` has `Q.count 1 = k / p`
  (Theorem 16.6.6, 2021 p. 739, index `0`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Module Complex

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical.Oriented

open StrongPolyfoldBundle PolyfoldClass

open Polyfold.Examples.OrbifoldSquare (cE rot_apply)

/-! ### The data -/

/-- `a ↦ (z ↦ a z)` as a monoid hom to `ℝ`-linear maps of `ℂ`. -/
def mulC : ℂ →* (ℂ →L[ℝ] ℂ) where
  toFun a := ContinuousLinearMap.mul ℝ ℂ a
  map_one' := ContinuousLinearMap.ext fun z => by simp
  map_mul' a b := ContinuousLinearMap.ext fun z => by simp [mul_assoc]

@[simp] theorem mulC_apply (a z : ℂ) : mulC a z = a * z := rfl

variable (p : ℕ) [NeZero p] (k : ℕ)

/-- `ℤ/p` acts on `V = ℂ` by `g · z = ζ_p^g z`. -/
def ρC : Cyclic.Gp p →* (ℂ →L[ℝ] ℂ) := mulC.comp (Cyclic.χHom p)

/-- `ℤ/p` acts on `W = ℂ` by `g · w = ζ_p^{k g} w`. -/
def σC : Cyclic.Gp p →* (ℂ →L[ℝ] ℂ) := mulC.comp ((powMonoidHom k).comp (Cyclic.χHom p))

@[simp] theorem ρC_apply (g : Cyclic.Gp p) (z : ℂ) : ρC p g z = Cyclic.χp p g * z := rfl

@[simp] theorem σC_apply (g : Cyclic.Gp p) (z : ℂ) : σC p k g z = Cyclic.χp p g ^ k * z := rfl

/-- `φ z = z^k`. -/
def powC (z : ℂ) : ℂ := z ^ k

/-- The value `c = t ∈ ℝ_{>0} ⊂ ℂ`. -/
def cC : ℂ := (Cyclic.tc p k : ℂ)

/-- The coordinates `ℂ ≃ ℝ²`, `a + b i ↦ (a, b)`. -/
def eC : ℂ ≃L[ℝ] (Fin 2 → ℝ) := cE.symm

/-! ### The hypotheses -/

/-- `eC` is positively oriented. -/
theorem orientation_map_eC :
    Orientation.map (Fin 2) eC.toLinearEquiv Complex.orientation = stdOrientation 2 := by
  rw [Complex.orientation, ← Module.Basis.orientation_map]
  congr 1
  refine Module.Basis.eq_of_apply_eq fun i => ?_
  rw [Module.Basis.map_apply, Pi.basisFun_apply, coe_basisOneI]
  funext j
  fin_cases i <;> fin_cases j <;> rfl

theorem injective_ρC : Injective (ρC p) := fun g h hgh => by
  have h1 := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) hgh
  simp only [ρC_apply, mul_one] at h1
  exact Cyclic.χp_injective p h1

theorem det_mulC (a : ℂ) : LinearMap.det (mulC a : ℂ →ₗ[ℝ] ℂ) = Complex.normSq a := by
  have h : (mulC a : ℂ →ₗ[ℝ] ℂ) = Algebra.lmul ℝ ℂ a := LinearMap.ext fun _ => rfl
  rw [h, ← Algebra.norm_apply, Algebra.norm_complex_apply]

theorem hdet_ρC_σC (g : Cyclic.Gp p) :
    0 < LinearMap.det (ρC p g : ℂ →ₗ[ℝ] ℂ) * LinearMap.det (σC p k g : ℂ →ₗ[ℝ] ℂ) := by
  change 0 < LinearMap.det (mulC (Cyclic.χp p g) : ℂ →ₗ[ℝ] ℂ) *
    LinearMap.det (mulC (Cyclic.χp p g ^ k) : ℂ →ₗ[ℝ] ℂ)
  rw [det_mulC, det_mulC]
  exact mul_pos (Complex.normSq_pos.2 (Cyclic.χp_ne_zero p g))
    (Complex.normSq_pos.2 (pow_ne_zero _ (Cyclic.χp_ne_zero p g)))

theorem contDiff_powC : ContDiff ℝ ∞ (powC k) := contDiff_id.pow k

theorem powC_smul (g : Cyclic.Gp p) (z : ℂ) : powC k (ρC p g z) = σC p k g (powC k z) := by
  simp [powC, mul_pow]

variable {k}

theorem isCompact_preimage_powC (hk : 0 < k) (K : Set ℂ) (hK : IsCompact K) :
    IsCompact (powC k ⁻¹' K) :=
  Cyclic.isCompact_preimage_of_norm_le (f := powC k) (continuous_pow k)
    (fun z => by
      rw [powC, norm_pow]
      exact Cyclic.norm_le_one_add_pow hk _ (norm_nonneg z)) hK

theorem surjective_fderiv_powC (hk : 0 < k) (z : ℂ) (hz : powC k z = cC p k) :
    Surjective (fderiv ℝ (powC k) z) := by
  have hz0 : z ≠ 0 := fun h0 => by
    rw [powC, h0, zero_pow hk.ne', cC] at hz
    exact Cyclic.tc_ne_zero hz.symm
  have ha : (k : ℂ) * z ^ (k - 1) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hk.ne') (pow_ne_zero _ hz0)
  have hd := ((hasDerivAt_pow k z).hasFDerivAt).restrictScalars ℝ
  rw [show powC k = fun x : ℂ => x ^ k from rfl, hd.fderiv]
  intro y
  refine ⟨y / ((k : ℂ) * z ^ (k - 1)), ?_⟩
  simp [div_mul_cancel₀ _ ha]

variable (k)

theorem eC_σC_cC (g : Cyclic.Gp p) : eC (σC p k g (cC p k)) = Cyclic.σk p k g (Cyclic.c₀ p k) := by
  rw [Cyclic.σk_apply, rot_apply, Cyclic.c₀, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- The norm condition: `∑_g ‖eC (σC g c)‖ = gNorm (σk p k) c₀ = 1`. -/
theorem sum_norm_σC_le : ∑ g : Cyclic.Gp p, ‖eC (σC p k g (cC p k))‖ ≤ 1 := by
  simp_rw [eC_σC_cC]
  exact (Cyclic.gNorm_σk_c₀ p k).le

/-! ### The count -/

theorem tφ_eC_powC : tφ eC eC (powC k) = Cyclic.powMap k := rfl

theorem eC_cC : eC (cC p k) = Cyclic.c₀ p k := rfl

variable {k}

/-- **The oriented classical count of `z ↦ z^k` on `ℂ` with `Complex.orientation` is `k / p`.** -/
theorem orientedClassicalCount_powC (hk : 0 < k) :
    orientedClassicalCount (Cyclic.Gp p) Complex.orientation Complex.orientation (powC k)
      (cC p k) = (k : ℝ) / p := by
  rw [← classicalCount_tφ eC eC orientation_map_eC orientation_map_eC, tφ_eC_powC, eC_cC]
  exact Cyclic.classicalCount_powMap hk

/-- **`z ↦ z^k` on `ℂ` with `Complex.orientation`, `G = ℤ/p`** (Theorem 16.6.6, 2021 p. 739,
index `0`): for the transported section an admissible perturbed solution set with the canonical
orientation exists, and every such `Q` has `Q.count 1 = k / p`. -/
theorem count_powC (hk : 0 < k) :
    letI := tAct eC (ρC p)
    haveI := tAct_smulCommClass eC (ρC p)
    haveI := tAct_faithfulSMul eC (ρC p) (injective_ρC p)
    (∃ Q : PointOrientedPerturbation (clFredholmSection (tσ eC (σC p k))
        (contDiff_tφ eC eC (contDiff_powC k)) (tφ_smul eC eC (ρC p) (σC p k) (powC_smul p k))).1,
      Q.t = tG (tσ eC (σC p k)) (eC (cC p k)) ∧
      Q.IsAdmissible (nG (tσ eC (σC p k))) (univ : Set (AG (tσ eC (σC p k))).X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet (clOrientationRep (tσ eC (σC p k))
        (contDiff_tφ eC eC (contDiff_powC k)) (tφ_smul eC eC (ρC p) (σC p k) (powC_smul p k))
        (hdet_transport eC eC (ρC p) (σC p k) (hdet_ρC_σC p k))) Q) ∧
    ∀ Q : PointOrientedPerturbation (clFredholmSection (tσ eC (σC p k))
        (contDiff_tφ eC eC (contDiff_powC k)) (tφ_smul eC eC (ρC p) (σC p k) (powC_smul p k))).1,
      Q.IsAdmissible (nG (tσ eC (σC p k))) (univ : Set (AG (tσ eC (σC p k))).X.OrbitSpace) →
      IsCanonicalPointSolutionSet (clOrientationRep (tσ eC (σC p k))
        (contDiff_tφ eC eC (contDiff_powC k)) (tφ_smul eC eC (ρC p) (σC p k) (powC_smul p k))
        (hdet_transport eC eC (ρC p) (σC p k) (hdet_ρC_σC p k))) Q →
      Q.count (clOne (tσ eC (σC p k))) = (k : ℝ) / p := by
  obtain ⟨hex, hall⟩ := count_eq_orientedClassicalCount eC eC (ρC p) (σC p k) (injective_ρC p)
    orientation_map_eC orientation_map_eC (hdet_ρC_σC p k) (contDiff_powC k) (powC_smul p k)
    (isCompact_preimage_powC hk) (surjective_fderiv_powC p hk) (sum_norm_σC_le p k)
  exact ⟨hex, fun Q hQ hcan => (hall Q hQ hcan).trans (orientedClassicalCount_powC p hk)⟩

end Polyfold.Examples.Classical.Oriented
