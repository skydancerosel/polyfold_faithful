import Polyfold.Chapter6.LocalDetBundle
import Polyfold.Chapter6.DetBundle
import Polyfold.Chapter6.DetNonOrientable
import Polyfold.Chapter6.ChartTransfer
import Polyfold.Examples.WeightedEllTwo
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Analysis.Convex.Contractible

/-!
# Examples for the linear orientation rows of Chapter 6

Examples, non-examples and characteristic properties for the rows V6.20 (Lemma 6.5.1),
V6.29 (orientations of line bundles), V6.30 (Proposition 6.6.1) and V6.53 (transfer between
chart points) of Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §§6.5–6.6.

* `lemma_6_5_1_fst`: Lemma 6.5.1 for the projection `ℝ × ℓ² → ℝ`, which is not Fredholm;
  `not_isGoodLeftProj_zero`: the identity is not a good left-projection for `0 : ℝ → ℝ`.
* `exists_two_lineOrientation_trivial`, `not_isLineOrientation_sign`: the trivial line bundle over
  `ℝ` has two orientations; the ray field that flips at `0` is not an orientation.
* `proposition_6_6_1_segment`: `DET` over the segment `{t · 1 : 1 ≤ t ≤ 2}` of `L(ℓ², ℓ²)` has two
  orientations, while `DET(ℓ², ℓ²)` over all Fredholm operators has none
  (`isEmpty_lineOrientation_det_ltwo`).
* `conjDet_neg_fst`: the identification `det(S) ≅ det(S)` given by `A = −1`, `Γ = −1` reverses the
  determinant line of the projection `ℝ × ℝ → ℝ`.
-/

set_option maxSynthPendingDepth 3

open Set Function Module Bundle

noncomputable section

namespace Polyfold.Examples.Path

open Polyfold Polyfold.Examples.WeightedEllTwo

/-! ### Lemma 6.5.1 (row V6.20) -/

section Lemma651

/-- The space `ℓ²` used in the examples is infinite-dimensional. -/
theorem not_finiteDimensional_L2 : ¬ FiniteDimensional ℝ L2 := fun _ =>
  not_surjective_incl
    ((LinearMap.injective_iff_surjective (f := (incl : L2 →ₗ[ℝ] L2))).1 incl_injective)

/-- The projection `ℝ × ℓ² → ℝ`. -/
abbrev fstL2 : ℝ × L2 →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ L2

/-- Row V6.20, Lemma 6.5.1 (p. 258): the projection `ℝ × ℓ² → ℝ` is not Fredholm (its kernel
`0 × ℓ²` is infinite-dimensional). -/
theorem not_isFredholm_fstL2 : ¬ fstL2.IsFredholm := by
  intro h
  have := h.finite_ker
  have hs : Surjective ((LinearMap.snd ℝ ℝ L2).comp
      (LinearMap.ker (fstL2 : ℝ × L2 →ₗ[ℝ] ℝ)).subtype) := fun v =>
    ⟨⟨((0 : ℝ), v), rfl⟩, rfl⟩
  exact not_finiteDimensional_L2 (Module.Finite.of_surjective _ hs)

/-- The projection `(a, v) ↦ (a, 0)` of `ℝ × ℓ²`. -/
abbrev projL2 : ℝ × L2 →L[ℝ] ℝ × L2 := (ContinuousLinearMap.inl ℝ ℝ L2).comp fstL2

theorem isIdempotentElem_projL2 : IsIdempotentElem projL2 := by
  ext x <;> rfl

theorem ker_projL2 : LinearMap.ker (((ContinuousLinearMap.id ℝ ℝ).comp fstL2 :
    ℝ × L2 →L[ℝ] ℝ) : ℝ × L2 →ₗ[ℝ] ℝ) = LinearMap.ker (projL2 : ℝ × L2 →ₗ[ℝ] ℝ × L2) := by
  ext x
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
    comp_apply, ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.inl_apply, Prod.mk_eq_zero, and_true]

/-- The identity of `ℝ` is a good left-projection for the projection `ℝ × ℓ² → ℝ`. -/
theorem isGoodLeftProj_fstL2 : IsGoodLeftProj fstL2 (ContinuousLinearMap.id ℝ ℝ) where
  isProj := ContinuousLinearMap.id_comp _
  finite_coker := inferInstance
  range_comp := by
    rw [ContinuousLinearMap.id_comp]
    refine (LinearMap.range_eq_top.2 fun a => ⟨(a, 0), rfl⟩).trans ?_
    exact (LinearMap.range_eq_top.2 fun a => ⟨a, rfl⟩).symm

/-- Row V6.20, Lemma 6.5.1 (p. 258): the conclusions of the lemma for the projection
`T : ℝ × ℓ² → ℝ`, `P = 1` and `Y = ℝ × 0`, although `T` is not Fredholm. -/
theorem lemma_6_5_1_fst : ¬ fstL2.IsFredholm ∧
    ∃ ε > 0, ∀ S : ℝ × L2 →L[ℝ] ℝ, ‖S - fstL2‖ < ε →
      IsGoodLeftProj S (ContinuousLinearMap.id ℝ ℝ) ∧
        ∃ e : LinearMap.range (projL2 : ℝ × L2 →ₗ[ℝ] ℝ × L2) ≃L[ℝ]
            LinearMap.range ((ContinuousLinearMap.id ℝ ℝ : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ),
          (e : LinearMap.range (projL2 : ℝ × L2 →ₗ[ℝ] ℝ × L2) →L[ℝ] _) =
            projRestrict (ContinuousLinearMap.id ℝ ℝ) S
              (LinearMap.range (projL2 : ℝ × L2 →ₗ[ℝ] ℝ × L2)) := by
  refine ⟨not_isFredholm_fstL2, lemma_6_5_1 isGoodLeftProj_fstL2 ?_⟩
  rw [ker_projL2]
  exact (ContinuousLinearMap.IsIdempotentElem.isTopCompl isIdempotentElem_projL2).symm

/-- Row V6.20, Lemma 6.5.1 (p. 258): the identity is not a good left-projection for the zero
operator of `ℝ`, so the hypothesis `P ∈ Π_T` of the lemma is not empty of content. -/
theorem not_isGoodLeftProj_zero :
    ¬ IsGoodLeftProj (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ) := by
  intro h
  have h1 : (1 : ℝ) ∈ LinearMap.range ((ContinuousLinearMap.id ℝ ℝ : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) :=
    ⟨1, rfl⟩
  rw [← h.range_comp] at h1
  obtain ⟨x, hx⟩ := h1
  simp at hx

end Lemma651

/-! ### Orientations of line bundles (row V6.29) -/

section LineBundles

/-- Row V6.29, orientations of line bundles over simply connected bases (p. 263): the trivial
line bundle `ℝ × ℝ → ℝ` has exactly two orientations. -/
theorem exists_two_lineOrientation_trivial :
    ∃ o₁ o₂ : LineOrientation (Bundle.Trivial ℝ ℝ), o₁ ≠ o₂ ∧
      ∀ o : LineOrientation (Bundle.Trivial ℝ ℝ), o = o₁ ∨ o = o₂ :=
  exists_two_lineOrientation

/-- The coordinate `1` for `b ≥ 0` and `−1` for `b < 0`. -/
def signVal (b : ℝ) : ℝ := if 0 ≤ b then 1 else -1

theorem signVal_ne_zero (b : ℝ) : signVal b ≠ 0 := by
  unfold signVal; split_ifs <;> norm_num

/-- The ray field of `ℝ × ℝ → ℝ` that is positive on `[0, ∞)` and negative on `(−∞, 0)`. -/
def signRay (b : ℝ) : Module.Ray ℝ (Bundle.Trivial ℝ ℝ b) :=
  rayOfNeZero ℝ (show Bundle.Trivial ℝ ℝ b from signVal b) (signVal_ne_zero b)

/-- Row V6.29, orientations of line bundles (p. 263): a choice of rays of the fibres of
`ℝ × ℝ → ℝ` that flips at `0` is not an orientation. -/
theorem not_isLineOrientation_sign : ¬ IsLineOrientation (Bundle.Trivial ℝ ℝ) signRay := by
  intro h
  have hev := h.eventually_posRay_iff (Bundle.Trivial.trivialization ℝ ℝ) (mem_univ (0 : ℝ))
  have hpos : ∀ b : ℝ, PosRay (Bundle.Trivial.trivialization ℝ ℝ) b (signRay b) ↔ 0 ≤ b := by
    intro b
    rw [signRay, posRay_ray_iff _ (mem_univ b)]
    change 0 < signVal b ↔ 0 ≤ b
    unfold signVal
    split_ifs with hb <;> simp [hb]
  simp only [hpos, le_refl, iff_true] at hev
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have : (0 : ℝ) ≤ -(ε / 2) := hball (by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hε)]
    exact half_lt_self hε)
  linarith

end LineBundles

/-! ### Proposition 6.6.1 (row V6.30) -/

section Proposition661

/-- `t · 1` is Fredholm on `ℓ²` for `t ≠ 0`. -/
theorem isFredholm_smul_id {t : ℝ} (ht : t ≠ 0) :
    (t • ContinuousLinearMap.id ℝ L2).IsFredholm := by
  have hs : Surjective (t • ContinuousLinearMap.id ℝ L2) := fun y =>
    ⟨t⁻¹ • y, by simp [smul_smul, ht]⟩
  refine isFredholm_of_surjective_of_finite_ker hs ?_
  have : LinearMap.ker ((t • ContinuousLinearMap.id ℝ L2 : L2 →L[ℝ] L2) : L2 →ₗ[ℝ] L2) = ⊥ :=
    LinearMap.ker_eq_bot.2 fun x y hxy => by
      simpa [ht] using hxy
  rw [this]
  infer_instance

/-- The segment `{t · 1 : 1 ≤ t ≤ 2}` of `L(ℓ², ℓ²)`. -/
def segL2 : Set (L2 →L[ℝ] L2) :=
  segment ℝ (ContinuousLinearMap.id ℝ L2) ((2 : ℝ) • ContinuousLinearMap.id ℝ L2)

theorem isFredholm_of_mem_segL2 : ∀ T ∈ segL2, T.IsFredholm := by
  rintro T ⟨a, b, ha, hb, hab, rfl⟩
  have hpos : 0 < a + 2 * b := by linarith
  have : a • ContinuousLinearMap.id ℝ L2 + b • ((2 : ℝ) • ContinuousLinearMap.id ℝ L2) =
      (a + 2 * b) • ContinuousLinearMap.id ℝ L2 := by
    rw [smul_smul, ← add_smul, mul_comm]
  rw [this]
  exact isFredholm_smul_id hpos.ne'

/-- Row V6.30, Proposition 6.6.1 (p. 263): over the segment `{t · 1 : 1 ≤ t ≤ 2}` of Fredholm
operators of `ℓ²`, `DET` is a line bundle with exactly two orientations. -/
theorem proposition_6_6_1_segment :
    VectorBundle ℝ ℝ (DetOn segL2 isFredholm_of_mem_segL2) ∧
      ∃ o₁ o₂ : LineOrientation (DetOn segL2 isFredholm_of_mem_segL2), o₁ ≠ o₂ ∧
        ∀ o : LineOrientation (DetOn segL2 isFredholm_of_mem_segL2), o = o₁ ∨ o = o₂ :=
  proposition_6_6_1 (convex_segment _ _) ⟨_, left_mem_segment ℝ _ _⟩ isFredholm_of_mem_segL2

end Proposition661

/-! ### Transfer of determinant lines (row V6.53) -/

section Transfer

/-- The projection `ℝ × ℝ → ℝ`, surjective with kernel `0 × ℝ`. -/
abbrev fstR : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ

theorem surjective_fstR : Surjective fstR := fun a => ⟨(a, 0), rfl⟩

theorem finrank_ker_fstR : 1 = finrank ℝ (LinearMap.ker (fstR : ℝ × ℝ →ₗ[ℝ] ℝ)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (fstR : ℝ × ℝ →ₗ[ℝ] ℝ)
  rw [LinearMap.range_eq_top.2 surjective_fstR, finrank_top, Module.finrank_prod,
    Module.finrank_self] at h
  omega

/-- The kernel vector `(0, 1)` of `ℝ × ℝ → ℝ`. -/
def kerVecR : Fin 1 → ℝ × ℝ := fun _ => (0, 1)

/-- The generator `(0, 1) ⊗ 1*` of `det(ℝ × ℝ → ℝ)`. -/
def detGenR : fredholmDet fstR :=
  kerDetVec fstR surjective_fstR kerVecR (fun _ => rfl) finrank_ker_fstR

theorem detGenR_ne_zero : detGenR ≠ 0 :=
  kerDetVec_ne_zero (isFredholm_of_finiteDimensional _) surjective_fstR _ _
    (linearIndependent_unique_iff.2 (by simp [kerVecR]))

/-- The conjugation relation `S ∘ A = Γ ∘ S` for `S` the projection, `A = −1`, `Γ = −1`. -/
theorem conj_neg_fstR : ∀ v, fstR (ContinuousLinearEquiv.neg ℝ v) =
    ContinuousLinearEquiv.neg ℝ (fstR v) := fun _ => rfl

/-- Row V6.53, transferring orientations between chart points (p. 273): the identification
`det(S) ≅ det(S)` of the conjugation `A = −1`, `Γ = −1` of the projection `S : ℝ × ℝ → ℝ` is `−1`
on the determinant line, so it reverses the orientation. -/
theorem conjDet_neg_fstR :
    conjDet (ContinuousLinearEquiv.neg ℝ) (ContinuousLinearEquiv.neg ℝ) conj_neg_fstR detGenR =
      (-1 : ℝ) • detGenR ∧ detGenR ≠ 0 := by
  refine ⟨?_, detGenR_ne_zero⟩
  have : FiniteDimensional ℝ (ℝ ⧸ LinearMap.range (fstR : ℝ × ℝ →ₗ[ℝ] ℝ)) := inferInstance
  have key : conjDet (ContinuousLinearEquiv.neg ℝ) (ContinuousLinearEquiv.neg ℝ) conj_neg_fstR
      detGenR = kerDetVec fstR surjective_fstR (fun i => -kerVecR i)
        (fun _ => by simp [kerVecR]) finrank_ker_fstR := by
    unfold detGenR kerDetVec
    rw [conjDet_wedge_tmul _ _ _ _ _ linearIndependent_empty_type]
    congr 2
  rw [key, kerDetVec_neg surjective_fstR odd_one (fun _ => rfl)]
  rfl

end Transfer

end Polyfold.Examples.Path
