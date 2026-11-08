import Polyfold.Chapter1.FredholmIndex

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 1, the items that
the 2021 edition changes or adds: **Remark 1.1.2** (p. 5, new in the 2021 edition) and
**Proposition 1.1.11** (p. 9; 2017: Proposition 1.4; preprint: Proposition 1.10), whose 2021
statement adds the index.

# Chapter 1 in the 2021 edition

## The text, paraphrased

(Remark 1.1.2, p. 5) "Banach space" usually means *Banachable* space: a vector space with a
topology induced by a complete norm.  All norms inducing the given topology are equivalent, by
the open mapping theorem; when the choice matters (contraction arguments) a norm is fixed.

(Proposition 1.1.11, p. 9) If `T : E → F` is sc-Fredholm and `S : E → F` is an sc⁺-operator,
then `T + S` is sc-Fredholm **and has the same index** (2017 and preprint: only "sc-Fredholm").
The proof (Appendix 1.4.1, pp. 15–16) is the one of the earlier texts; it does not argue the
index statement.

## What is formalized

* `Polyfold.proposition_1_1_11_2021`: `T + S` is sc-Fredholm and `ind(T + S) = ind(T)`, and on
  every level `(T + S)_m : E_m → F_m` is Fredholm of index `ind(T)`.  This is the conjunction of
  the existing `proposition_1_10` (`ScFredholm.lean`, the 2017/preprint statement),
  `proposition_1_10_index` and `proposition_1_10_index_lvl` (`FredholmIndex.lean`, where the
  index part was already proved from the invariance of the Fredholm index under compact
  perturbations, `fredholmIndex_add_isCompactOperator`).
* `Polyfold.remark_1_1_2_2021`, `Polyfold.remark_1_1_2_2021_openMapping`: the mathematical
  content of Remark 1.1.2.  A vector space with
  two norms is modelled by two normed spaces `E₁`, `E₂` and a linear equivalence `e : E₁ ≃ E₂`
  (the identity of the underlying vector space).  (1) If `e` is a homeomorphism (the two norms
  induce the same topology), the norms are equivalent: `‖e x‖ ≤ c ‖x‖` and `‖x‖ ≤ c ‖e x‖`.
  (2) If both norms are complete and `e` is continuous (one norm dominates the other), then `e`
  is a homeomorphism, hence (1) applies: this is where the open mapping theorem enters.

## What the text leaves implicit, and the choices made

* Remark 1.1.2's sentence "all norms inducing the given topology are equivalent" needs no
  completeness and no open mapping theorem (part (1): a continuous linear map between normed
  spaces is bounded); the open mapping theorem is what makes two *complete* norms, one dominating
  the other, equivalent (part (2)).  We record both readings.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

/-! ### Remark 1.1.2 -/

section Remark

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₂]

/-- **Remark 1.1.2, p. 5 (new in the 2021 edition)**, first reading: two norms on a vector space
that induce the same topology are equivalent.  For a linear equivalence `e : E₁ ≃ E₂` (the identity
of the vector space, `E₁` and `E₂` carrying the two norms) which is a homeomorphism, there is
`c > 0` with `‖e x‖ ≤ c ‖x‖` and `‖x‖ ≤ c ‖e x‖`. -/
theorem remark_1_1_2_2021 (e : E₁ ≃ₗ[ℝ] E₂) (he : Continuous e) (he' : Continuous e.symm) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, ‖e x‖ ≤ c * ‖x‖ ∧ ‖x‖ ≤ c * ‖e x‖ := by
  set f : E₁ →L[ℝ] E₂ := ⟨e.toLinearMap, he⟩
  set g : E₂ →L[ℝ] E₁ := ⟨e.symm.toLinearMap, he'⟩
  refine ⟨max ‖f‖ ‖g‖ + 1, by positivity, fun x => ⟨?_, ?_⟩⟩
  · have h1 : ‖e x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
    have h2 : ‖f‖ * ‖x‖ ≤ (max ‖f‖ ‖g‖ + 1) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (by linarith [le_max_left ‖f‖ ‖g‖]) (norm_nonneg x)
    linarith
  · have h1 : ‖g (e x)‖ ≤ ‖g‖ * ‖e x‖ := g.le_opNorm (e x)
    have hgx : g (e x) = x := e.symm_apply_apply x
    rw [hgx] at h1
    have h2 : ‖g‖ * ‖e x‖ ≤ (max ‖f‖ ‖g‖ + 1) * ‖e x‖ :=
      mul_le_mul_of_nonneg_right (by linarith [le_max_right ‖f‖ ‖g‖]) (norm_nonneg _)
    linarith

/-- **Remark 1.1.2, p. 5 (new in the 2021 edition)**, the open mapping theorem: if both norms are
complete and one dominates the other (`e : E₁ ≃ E₂` continuous), then `e⁻¹` is continuous, so the
two norms induce the same topology and are equivalent (`remark_1_1_2_2021`). -/
theorem remark_1_1_2_2021_openMapping [CompleteSpace E₁] [CompleteSpace E₂] (e : E₁ ≃ₗ[ℝ] E₂)
    (he : Continuous e) :
    Continuous e.symm ∧ ∃ c : ℝ, 0 < c ∧ ∀ x, ‖e x‖ ≤ c * ‖x‖ ∧ ‖x‖ ≤ c * ‖e x‖ := by
  set f : E₁ →L[ℝ] E₂ := ⟨e.toLinearMap, he⟩
  have hb : Bijective f := e.bijective
  set g := ContinuousLinearEquiv.ofBijective f (LinearMap.ker_eq_bot.2 hb.1)
    (LinearMap.range_eq_top.2 hb.2)
  have he' : Continuous e.symm := g.symm.continuous.congr fun y => by
    apply e.injective
    rw [e.apply_symm_apply]
    exact g.apply_symm_apply y
  exact ⟨he', remark_1_1_2_2021 e he he'⟩

end Remark

/-! ### Proposition 1.1.11 -/

section CompactPerturbation

variable {E F : ScBanach}

/-- **Proposition 1.1.11 (Compact Perturbation), p. 9** (2017: Proposition 1.4; preprint:
Proposition 1.10, whose statement has no index): if `T : E → F` is sc-Fredholm and `S` is an
sc⁺-operator, then `T + S` is sc-Fredholm **and has the same index**; moreover every level map
`(T + S)_m : E_m → F_m` is Fredholm of index `ind(T)`. -/
theorem proposition_1_1_11_2021 {T : ScOperator E F} (hT : IsScFredholm T) (S : ScPlus E F) :
    IsScFredholm (T + S.toScOperator) ∧ scIndex (T + S.toScOperator) = scIndex T ∧
      ∀ m, ((T + S.toScOperator) m).IsFredholm ∧
        fredholmIndex ((T + S.toScOperator) m) = scIndex T :=
  ⟨proposition_1_10 hT S, proposition_1_10_index hT S, proposition_1_10_index_lvl hT S⟩

end CompactPerturbation

end Polyfold
