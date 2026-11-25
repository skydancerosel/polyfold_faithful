import Polyfold.Examples.Classical.ClassicalSum
import Polyfold.Examples.Classical.Perturbation

/-!
# The classical reduction: oriented finite-dimensional spaces

Transport of the data of the classical count from oriented finite-dimensional real normed spaces
`V`, `W` of dimension `n` to `ℝⁿ` with the orientation of the standard basis, for the comparison
with Theorem 16.6.6, 2021 p. 739 (index `0`).  Everything in this file is stated with Mathlib
objects only; no polyfold object enters.

## Conventions

* `stdOrientation n`: the orientation of `Pi.basisFun ℝ (Fin n)` on `ℝⁿ = Fin n → ℝ`.
* **`orientedSign oV oW L`** for `L : V →ₗ[ℝ] W` is `0` if `L` is not bijective; otherwise `1`
  if `Orientation.map (Fin n) (LinearEquiv.ofBijective L _) oV = oW` and `−1` if not.  No basis
  is chosen.  `orientedSign_eq_sign_det`: for linear isomorphisms `eV : V ≃L ℝⁿ`, `eW : W ≃L ℝⁿ`
  carrying `oV`, `oW` to `stdOrientation n`, it is the sign of `det (eW ∘ L ∘ eV⁻¹)`; in
  particular this sign does not depend on the choice of such `eV`, `eW`.
* **`orientedClassicalCount G oV oW φ c = (1/♯G) · ∑_{x ∈ φ⁻¹(c)} orientedSign oV oW (Dφ x)`**.
* The group `G` acts by `ρ : G →* (V →L[ℝ] V)` and `σ : G →* (W →L[ℝ] W)`; the product
  orientation of `V × W` is preserved iff `0 < det ρ(g) · det σ(g)` for all `g`.

## What is formalized (namespace `Polyfold.Examples.Classical.Oriented`)

* `tAct eV ρ`: the action `g • x = eV (ρ g (eV⁻¹ x))` on `ℝⁿ` (a `def`, used through `letI`),
  `tAct_smulCommClass`, and `tAct_faithfulSMul` (from `Function.Injective ρ`; the only place
  where faithfulness enters).
* `tσ eW σ g = eW ∘ σ g ∘ eW⁻¹`, `tφ eV eW φ = eW ∘ φ ∘ eV⁻¹`; the value is `eW c`.
* Transport of the hypotheses, none of which uses faithfulness: `hdet_transport`
  (`det (rhoL g) · det (tσ g) = det ρ(g) · det σ(g)`), `contDiff_tφ`, `tφ_smul` (equivariance),
  `isCompact_preimage_tφ` (properness), `surjective_fderiv_tφ` (regular value),
  `gNorm_tσ` (`gNorm (tσ eW σ) (eW c) = ∑_g ‖eW (σ g c)‖`).
* **`classicalCount_tφ`**:
  `classicalCount G (tφ eV eW φ) (eW c) = orientedClassicalCount G oV oW φ c`.
* `exists_positive_equiv`: for `n ≠ 0` and `finrank ℝ V = n`, every orientation is carried to
  `stdOrientation n` by some `eV : V ≃L[ℝ] ℝⁿ`.  (For `n = 0` this does not hold for the
  negative orientation of the zero space, which is why `eV`, `eW` are parameters below.)
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Module

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical.Oriented

/-! ### Orientations and the oriented sign -/

/-- The standard orientation of `ℝⁿ`: the orientation of the standard basis. -/
abbrev stdOrientation (n : ℕ) : Orientation ℝ (Fin n → ℝ) (Fin n) :=
  (Pi.basisFun ℝ (Fin n)).orientation

/-- `Orientation.map` of a composite is the composite of the `Orientation.map`s. -/
theorem orientation_map_trans {ι M N P : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] [AddCommGroup P] [Module ℝ P] (e : M ≃ₗ[ℝ] N) (f : N ≃ₗ[ℝ] P)
    (x : Orientation ℝ M ι) :
    Orientation.map ι (e.trans f) x = Orientation.map ι f (Orientation.map ι e x) := by
  induction x using Module.Ray.ind with
  | h v hv => rfl

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ}

open _root_.Classical in
/-- **The sign of a linear map relative to orientations** `oV`, `oW`: `0` if `L` is not
bijective, `1` if `L` carries `oV` to `oW`, and `−1` otherwise. -/
def orientedSign (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (L : V →ₗ[ℝ] W) : SignType :=
  if h : Bijective L then
    if Orientation.map (Fin n) (LinearEquiv.ofBijective L h) oV = oW then 1 else -1
  else 0

variable (G : Type) [Fintype G] in
/-- **The oriented classical count** `(1/♯G) · ∑_{x ∈ φ⁻¹(c)} orientedSign oV oW (Dφ x)`. -/
def orientedClassicalCount (oV : Orientation ℝ V (Fin n)) (oW : Orientation ℝ W (Fin n))
    (φ : V → W) (c : W) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ *
    ∑ᶠ x ∈ φ ⁻¹' {c}, (orientedSign oV oW (fderiv ℝ φ x : V →ₗ[ℝ] W) : ℝ)

/-- A linear endomorphism of a finite-dimensional space with nonzero determinant is bijective. -/
theorem bijective_of_det_ne_zero {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    {f : M →ₗ[ℝ] M} (h : LinearMap.det f ≠ 0) : Bijective f :=
  (Module.End.isUnit_iff f).1 ((LinearMap.isUnit_iff_isUnit_det f).2 (Ne.isUnit h))

/-- **The oriented sign in coordinates**: for linear isomorphisms `eV`, `eW` onto `ℝⁿ` carrying
`oV`, `oW` to the standard orientation, `orientedSign oV oW L = sign det (eW ∘ L ∘ eV⁻¹)`. -/
theorem orientedSign_eq_sign_det {oV : Orientation ℝ V (Fin n)} {oW : Orientation ℝ W (Fin n)}
    (eV : V ≃L[ℝ] (Fin n → ℝ)) (eW : W ≃L[ℝ] (Fin n → ℝ))
    (heV : Orientation.map (Fin n) eV.toLinearEquiv oV = stdOrientation n)
    (heW : Orientation.map (Fin n) eW.toLinearEquiv oW = stdOrientation n) (L : V →ₗ[ℝ] W) :
    orientedSign oV oW L = SignType.sign (LinearMap.det
      ((eW.toLinearEquiv : W →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ L ∘ₗ
        (eV.symm.toLinearEquiv : (Fin n → ℝ) →ₗ[ℝ] V))) := by
  have hcard : Fintype.card (Fin n) = finrank ℝ (Fin n → ℝ) := by simp
  have hcardW : Fintype.card (Fin n) = finrank ℝ W := by
    rw [hcard, eW.toLinearEquiv.finrank_eq]
  have hV : Orientation.map (Fin n) eV.symm.toLinearEquiv (stdOrientation n) = oV := by
    rw [← heV]
    exact (Orientation.map (Fin n) eV.toLinearEquiv).symm_apply_apply oV
  unfold orientedSign
  split_ifs with hL hm
  · set E := (eV.symm.toLinearEquiv.trans (LinearEquiv.ofBijective L hL)).trans eW.toLinearEquiv
    have hE : (E : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) =
        (eW.toLinearEquiv : W →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ L ∘ₗ
          (eV.symm.toLinearEquiv : (Fin n → ℝ) →ₗ[ℝ] V) := LinearMap.ext fun _ => rfl
    have hmap : Orientation.map (Fin n) E (stdOrientation n) = stdOrientation n := by
      rw [orientation_map_trans, orientation_map_trans, hV, hm, heW]
    rw [← hE, sign_pos ((Orientation.map_eq_iff_det_pos _ E hcard).1 hmap)]
  · set E := (eV.symm.toLinearEquiv.trans (LinearEquiv.ofBijective L hL)).trans eW.toLinearEquiv
    have hE : (E : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) =
        (eW.toLinearEquiv : W →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ L ∘ₗ
          (eV.symm.toLinearEquiv : (Fin n → ℝ) →ₗ[ℝ] V) := LinearMap.ext fun _ => rfl
    have hneg := (Orientation.ne_iff_eq_neg _ _ hcardW).1 hm
    have hmap : Orientation.map (Fin n) E (stdOrientation n) = -stdOrientation n := by
      rw [orientation_map_trans, orientation_map_trans, hV, hneg, Orientation.map_neg, heW]
    rw [← hE, sign_neg ((Orientation.map_eq_neg_iff_det_neg _ E hcard).1 hmap)]
  · have h0 : LinearMap.det ((eW.toLinearEquiv : W →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ L ∘ₗ
        (eV.symm.toLinearEquiv : (Fin n → ℝ) →ₗ[ℝ] V)) = 0 := by
      by_contra h
      apply hL
      have hb := bijective_of_det_ne_zero h
      have hL' : (L : V → W) = eW.symm ∘ (⇑((eW.toLinearEquiv : W →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ L ∘ₗ
          (eV.symm.toLinearEquiv : (Fin n → ℝ) →ₗ[ℝ] V))) ∘ eV := by
        funext x
        simp
      rw [hL']
      exact eW.symm.bijective.comp (hb.comp eV.bijective)
    rw [h0, sign_zero]

/-- The same for a continuous linear map `L`, with `eW ∘ L ∘ eV⁻¹` as a continuous linear map. -/
theorem orientedSign_eq_sign_det' {oV : Orientation ℝ V (Fin n)} {oW : Orientation ℝ W (Fin n)}
    (eV : V ≃L[ℝ] (Fin n → ℝ)) (eW : W ≃L[ℝ] (Fin n → ℝ))
    (heV : Orientation.map (Fin n) eV.toLinearEquiv oV = stdOrientation n)
    (heW : Orientation.map (Fin n) eW.toLinearEquiv oW = stdOrientation n) (L : V →L[ℝ] W) :
    orientedSign oV oW (L : V →ₗ[ℝ] W) = SignType.sign (LinearMap.det
      (((eW : W →L[ℝ] (Fin n → ℝ)).comp (L.comp (eV.symm : (Fin n → ℝ) →L[ℝ] V)) :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) :=
  orientedSign_eq_sign_det eV eW heV heW L

/-- **Positively oriented coordinates exist** in positive dimension. -/
theorem exists_positive_equiv [NeZero n] (o : Orientation ℝ V (Fin n)) (h : finrank ℝ V = n) :
    ∃ e : V ≃L[ℝ] (Fin n → ℝ), Orientation.map (Fin n) e.toLinearEquiv o = stdOrientation n := by
  have hc : Fintype.card (Fin n) = finrank ℝ V := by simp [h]
  set b := o.someBasis hc
  refine ⟨b.equivFun.toContinuousLinearEquiv, ?_⟩
  have hb : b.map b.equivFun = Pi.basisFun ℝ (Fin n) := by
    refine Module.Basis.eq_of_apply_eq fun i => ?_
    rw [Module.Basis.map_apply, Module.Basis.equivFun_apply, Module.Basis.repr_self,
      Pi.basisFun_apply, Finsupp.single_eq_pi_single]
  change Orientation.map (Fin n) b.equivFun o = _
  rw [← o.someBasis_orientation hc, ← Module.Basis.orientation_map, hb]

/-! ### The transported data -/

variable {G : Type} [Group G]

/-- **The transported action** `g • x = eV (ρ g (eV⁻¹ x))` on `ℝⁿ`. -/
@[instance_reducible]
def tAct (eV : V ≃L[ℝ] (Fin n → ℝ)) (ρ : G →* (V →L[ℝ] V)) : DistribMulAction G (Fin n → ℝ) where
  smul g x := eV (ρ g (eV.symm x))
  one_smul x := show eV (ρ 1 (eV.symm x)) = x by simp
  mul_smul g h x := show eV (ρ (g * h) (eV.symm x)) = eV (ρ g (eV.symm (eV (ρ h (eV.symm x))))) by
    rw [ContinuousLinearEquiv.symm_apply_apply, map_mul]
    rfl
  smul_zero g := show eV (ρ g (eV.symm 0)) = 0 by simp
  smul_add g x y := show eV (ρ g (eV.symm (x + y))) = eV (ρ g (eV.symm x)) + eV (ρ g (eV.symm y)) by
    simp

theorem tAct_smul_def (eV : V ≃L[ℝ] (Fin n → ℝ)) (ρ : G →* (V →L[ℝ] V)) (g : G)
    (x : Fin n → ℝ) : (letI := tAct eV ρ; g • x) = eV (ρ g (eV.symm x)) := rfl

theorem tAct_smulCommClass (eV : V ≃L[ℝ] (Fin n → ℝ)) (ρ : G →* (V →L[ℝ] V)) :
    letI := tAct eV ρ; SMulCommClass G ℝ (Fin n → ℝ) := by
  let := tAct eV ρ
  exact ⟨fun g r x => by
    change eV (ρ g (eV.symm (r • x))) = r • eV (ρ g (eV.symm x))
    simp⟩

/-- **Faithfulness transports**: an injective `ρ` gives a faithful transported action. -/
theorem tAct_faithfulSMul (eV : V ≃L[ℝ] (Fin n → ℝ)) (ρ : G →* (V →L[ℝ] V))
    (hρ : Injective ρ) : letI := tAct eV ρ; FaithfulSMul G (Fin n → ℝ) := by
  let := tAct eV ρ
  refine ⟨fun {g h} hgh => hρ (ContinuousLinearMap.ext fun v => ?_)⟩
  have := hgh (eV v)
  change eV (ρ g (eV.symm (eV v))) = eV (ρ h (eV.symm (eV v))) at this
  simpa using this

/-- **The transported fibre action** `tσ eW σ g = eW ∘ σ g ∘ eW⁻¹`. -/
def tσ (eW : W ≃L[ℝ] (Fin n → ℝ)) (σ : G →* (W →L[ℝ] W)) :
    G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) where
  toFun g := (eW : W →L[ℝ] (Fin n → ℝ)).comp ((σ g).comp (eW.symm : (Fin n → ℝ) →L[ℝ] W))
  map_one' := ContinuousLinearMap.ext fun x => by simp
  map_mul' g h := ContinuousLinearMap.ext fun x => by simp

@[simp] theorem tσ_apply (eW : W ≃L[ℝ] (Fin n → ℝ)) (σ : G →* (W →L[ℝ] W)) (g : G)
    (x : Fin n → ℝ) : tσ eW σ g x = eW (σ g (eW.symm x)) := rfl

/-- **The transported map** `tφ eV eW φ = eW ∘ φ ∘ eV⁻¹`. -/
def tφ (eV : V ≃L[ℝ] (Fin n → ℝ)) (eW : W ≃L[ℝ] (Fin n → ℝ)) (φ : V → W) :
    (Fin n → ℝ) → (Fin n → ℝ) :=
  fun x => eW (φ (eV.symm x))

@[simp] theorem tφ_apply (eV : V ≃L[ℝ] (Fin n → ℝ)) (eW : W ≃L[ℝ] (Fin n → ℝ)) (φ : V → W)
    (x : Fin n → ℝ) : tφ eV eW φ x = eW (φ (eV.symm x)) := rfl

/-! ### Transport of the hypotheses -/

variable (eV : V ≃L[ℝ] (Fin n → ℝ)) (eW : W ≃L[ℝ] (Fin n → ℝ))
  (ρ : G →* (V →L[ℝ] V)) (σ : G →* (W →L[ℝ] W)) {φ : V → W}

theorem det_rhoL_tAct (g : G) :
    (letI := tAct eV ρ
     haveI := tAct_smulCommClass eV ρ
     LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) =
      LinearMap.det (ρ g : V →ₗ[ℝ] V) := by
  let := tAct eV ρ
  have := tAct_smulCommClass eV ρ
  rw [← LinearMap.det_conj (ρ g : V →ₗ[ℝ] V) eV.toLinearEquiv]
  rfl

theorem det_tσ (g : G) :
    LinearMap.det (tσ eW σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) =
      LinearMap.det (σ g : W →ₗ[ℝ] W) := by
  rw [← LinearMap.det_conj (σ g : W →ₗ[ℝ] W) eW.toLinearEquiv]
  rfl

/-- **The orientation condition transports**: `det (rhoL g) · det (tσ g) = det ρ(g) · det σ(g)`. -/
theorem hdet_transport
    (hdet : ∀ g : G, 0 < LinearMap.det (ρ g : V →ₗ[ℝ] V) * LinearMap.det (σ g : W →ₗ[ℝ] W)) :
    letI := tAct eV ρ
    haveI := tAct_smulCommClass eV ρ
    ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (tσ eW σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := by
  intro g
  rw [det_rhoL_tAct, det_tσ]
  exact hdet g

theorem contDiff_tφ (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (tφ eV eW φ) :=
  eW.contDiff.comp (hφ.comp eV.symm.contDiff)

/-- **Equivariance transports.** -/
theorem tφ_smul (heq : ∀ (g : G) x, φ (ρ g x) = σ g (φ x)) :
    letI := tAct eV ρ
    ∀ (g : G) x, tφ eV eW φ (g • x) = tσ eW σ g (tφ eV eW φ x) := by
  intro g x
  change eW (φ (eV.symm (eV (ρ g (eV.symm x))))) = eW (σ g (eW.symm (eW (φ (eV.symm x)))))
  rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply, heq]

/-- **Properness transports.** -/
theorem isCompact_preimage_tφ (hprop : ∀ K, IsCompact K → IsCompact (φ ⁻¹' K)) :
    ∀ K, IsCompact K → IsCompact (tφ eV eW φ ⁻¹' K) := by
  intro K hK
  have h : tφ eV eW φ ⁻¹' K = eV '' (φ ⁻¹' (eW.symm '' K)) := by
    ext x
    simp only [mem_preimage, tφ_apply, mem_image]
    constructor
    · intro hx
      exact ⟨eV.symm x, ⟨eW (φ (eV.symm x)), hx, by simp⟩, by simp⟩
    · rintro ⟨v, ⟨w, hw, hwv⟩, rfl⟩
      rw [ContinuousLinearEquiv.symm_apply_apply, ← hwv, ContinuousLinearEquiv.apply_symm_apply]
      exact hw
  rw [h]
  exact (hprop _ (hK.image eW.symm.continuous)).image eV.continuous

theorem fderiv_tφ (x : Fin n → ℝ) :
    fderiv ℝ (tφ eV eW φ) x =
      (eW : W →L[ℝ] (Fin n → ℝ)).comp
        ((fderiv ℝ φ (eV.symm x)).comp (eV.symm : (Fin n → ℝ) →L[ℝ] V)) := by
  have h : tφ eV eW φ = eW ∘ (φ ∘ eV.symm) := rfl
  rw [h, ContinuousLinearEquiv.comp_fderiv, ContinuousLinearEquiv.comp_right_fderiv]

/-- **Regular values transport.** -/
theorem surjective_fderiv_tφ {c : W} (hc : ∀ x, φ x = c → Surjective (fderiv ℝ φ x)) :
    ∀ x, tφ eV eW φ x = eW c → Surjective (fderiv ℝ (tφ eV eW φ) x) := by
  intro x hx
  rw [fderiv_tφ, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
  exact eW.surjective.comp ((hc _ (eW.injective hx)).comp eV.symm.surjective)

/-- **The norm condition in the coordinates**: `gNorm (tσ eW σ) (eW c) = ∑_g ‖eW (σ g c)‖`. -/
theorem gNorm_tσ [Fintype G] (c : W) : gNorm (tσ eW σ) (eW c) = ∑ g : G, ‖eW (σ g c)‖ := by
  simp [gNorm]

/-! ### The count -/

theorem preimage_tφ (c : W) : tφ eV eW φ ⁻¹' {eW c} = eV '' (φ ⁻¹' {c}) := by
  ext x
  simp only [mem_preimage, tφ_apply, mem_singleton_iff, mem_image]
  constructor
  · intro hx
    exact ⟨eV.symm x, eW.injective hx, by simp⟩
  · rintro ⟨v, hv, rfl⟩
    rw [ContinuousLinearEquiv.symm_apply_apply, hv]

/-- **The classical count of the transported data is the oriented classical count.** -/
theorem classicalCount_tφ [Fintype G] {oV : Orientation ℝ V (Fin n)}
    {oW : Orientation ℝ W (Fin n)}
    (heV : Orientation.map (Fin n) eV.toLinearEquiv oV = stdOrientation n)
    (heW : Orientation.map (Fin n) eW.toLinearEquiv oW = stdOrientation n) (φ : V → W) (c : W) :
    classicalCount G (tφ eV eW φ) (eW c) = orientedClassicalCount G oV oW φ c := by
  unfold classicalCount orientedClassicalCount
  congr 1
  rw [preimage_tφ, finsum_mem_image eV.injective.injOn]
  refine finsum_mem_congr rfl fun v _ => ?_
  rw [orientedSign_eq_sign_det' eV eW heV heW, fderiv_tφ, ContinuousLinearEquiv.symm_apply_apply]

end Polyfold.Examples.Classical.Oriented
