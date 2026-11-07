import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_18

namespace RoundTrip.V6_18
open Polyfold Module

/-- The project's statement (`ι_φ` is bijective, the count `m + l = n`, the complement
`R(π) ⊕ span c̄ = ℝⁿ`, and Proposition 6.15), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.stabIota_bijective.{0, 0} ∧ type_of% @Polyfold.stab_card_eq.{0, 0} ∧
    type_of% @Polyfold.isCompl_range_stabPi_span.{0, 0} ∧
    type_of% @Polyfold.proposition_6_15.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.stabIota_bijective.{0, 0}, @Polyfold.stab_card_eq.{0, 0},
    @Polyfold.isCompl_range_stabPi_span.{0, 0}, @Polyfold.proposition_6_15.{0, 0}⟩

/-- `det_{std}(c)` is the determinant of the matrix with columns `c_j`. -/
theorem basisFun_det_eq {n : ℕ} (c : Fin n → Fin n → ℝ) :
    (Pi.basisFun ℝ (Fin n)).det c = Matrix.det (Matrix.of fun i j => c j i) := by
  rw [Basis.det_apply]
  congr 1

/-- B's classical Fredholm notion gives Mathlib's (Banach spaces). -/
theorem isFredholm_of_op {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {T : E →L[ℝ] F}
    (hT : IsFredholmOp T) : T.IsFredholm :=
  isFredholm_of_banach T hT.1 hT.2.1 hT.2.2

/-- `A ⇒ B`.  `m + l = n` is A's `stab_card_eq`.  B's `Φ_E` and `ψ` (any maps with the defining
properties) agree with the project's `(stabSeq hφ).phi` on the given vector and with `stabPsi`
(uniqueness on lines), so B's `ι_φ(h)` is the project's `stabIota h`, given by A's
Proposition 6.15.  The linear independence of `(c̄, r)` is read off the same formula: `ι_φ` is
injective (A), so `det(c̄, r)⁻¹ ≠ 0`. -/
theorem A_to_B : A → B := by
  intro hA E F _ _ _ _ _ _ n T φ hT hs g hg ψ hψ k m l a cbar bbar hk hm hkl ha hd hb
  have hT' := isFredholm_of_op hT
  have := hT'.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT'.finite_coker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  -- `a` as a basis
  obtain ⟨aB, rfl⟩ : ∃ aB : Basis (Fin k) ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)), ⇑aB = a :=
    ⟨_, coe_basisOfLinearIndependentOfCardEqFinrank' _ ha (by simp [hk])⟩
  -- `m + l = n` (A's `stab_card_eq`)
  have hn : m + l = n := hA.2.1 hT' hs hm (by rw [← hk]; exact hkl)
  have hC : m + l = finrank ℝ (Fin n → ℝ) := hn.trans (Module.finrank_fin_fun ℝ).symm
  -- B's `ι_φ(h)` is the project's `stabIota h`
  let h : fredholmDet T := wedge (⇑aB) hk ⊗ₜ[ℝ] dualVec (wedge (clsPhi T φ ∘ cbar) hm)
  have e1 : g h = (stabSeq hs).phi h :=
    (hg k m l aB (clsPhi T φ ∘ cbar) bbar cbar hk hm hkl hC ha hd hb (fun _ => rfl)).trans
      ((stabSeq hs).phi_wedge_tmul ha hk hd hm hb hkl (c := cbar) (fun _ => rfl) hC).symm
  have e2 : ψ = stabPsi hs :=
    linearMap_ext_of_ne_zero finrank_maxPowDual (dualVec_ne_zero finrank_maxPow (stdWedge_ne_zero n))
      (hψ.trans (stabPsi_dualVec_stdWedge hs).symm)
  have e3 : (TensorProduct.map LinearMap.id ψ ∘ₗ g) h = stabIota hT' hs h := by
    rw [LinearMap.comp_apply, e1, e2]
    rfl
  -- Proposition 6.15 (A)
  have h615 := hA.2.2.2 hT' hs aB cbar hd hm bbar hb hkl hn
  -- `h ≠ 0`, so `ι_φ(h) ≠ 0` and `det(c̄, r) ≠ 0`
  have hne : h ≠ 0 :=
    tmul_ne_zero_of_ne_zero (wedge_basis_ne_zero' aB hk)
      (dualVec_ne_zero finrank_maxPow ((wedge_ne_zero_iff hm).2 hd))
  have hne' : stabIota hT' hs h ≠ 0 := fun h0 =>
    hne ((hA.1 hT' hs).1 (h0.trans (map_zero _).symm))
  have hdet : (Pi.basisFun ℝ (Fin n)).det
      ((Fin.append cbar fun i => ((bbar i : E × (Fin n → ℝ)).2)) ∘ Fin.cast hn.symm) ≠ 0 := by
    intro h0
    rw [h0, inv_zero, zero_smul] at h615
    exact hne' h615
  refine ⟨⟨?_, hn⟩, fun hn' => ?_⟩
  · have hli := ((Pi.basisFun ℝ (Fin n)).is_basis_iff_det.2 (IsUnit.mk0 _ hdet)).1
    exact (linearIndependent_equiv (finCongr hn.symm)).1 hli
  · rw [e3]
    refine h615.trans (congrArg₂ (fun (t : ℝ) v => t⁻¹ • v) ?_ ?_)
    · exact basisFun_det_eq _
    · rfl

/-! `B ⇒ A` is not proved: A is more general than B.
* All four theorems of A are stated for arbitrary normed spaces `E`, `F` (the project `omit`s
  `CompleteSpace`), with Mathlib's `T.IsFredholm`; B only speaks about Banach spaces.  Reducing the
  non-complete case to B (e.g. through finite-dimensional models of `ker T`, `coker T`, `ker T_φ`
  and transport of all wedges) would be a substantial construction, not glue.
* `isCompl_range_stabPi_span` assumes neither that `T` is Fredholm (only `dim coker T < ∞`) nor
  that `T_φ` is onto; B always assumes both.
* `stabIota_bijective` (`ι_φ` is an isomorphism) is not stated in B; on Banach spaces it would follow
  from B's formula (a nonzero map of lines), as would `stab_card_eq` (B's `m + l = n`) and
  `proposition_6_15`, but the generality gap above remains. -/

#rt_check RoundTrip.V6_18.A_to_B [Polyfold.stabIota_bijective, Polyfold.stab_card_eq,
  Polyfold.isCompl_range_stabPi_span, Polyfold.proposition_6_15]

end RoundTrip.V6_18
