import Polyfold.Chapter16.P3W4PB_Multisections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.5, formula (16.8),
p. 733 (2017: the formula after Definition 16.36), and the pointwise norm of Definition 13.2.3,
p. 608.  Numbers and pages are the 2021 text's.

# Continuity of `n(λ)`

## The text, paraphrased

(16.8) For an sc⁺-multisection `λ` of the strong polyfold bundle `p : Y → Z` and an auxiliary
norm `n`, `n(λ)(z) = max{n(y) | p(y) = z, λ(y) ≠ 0}` defines a continuous map `Z → [0, ∞)`.

## What is formalized

* `SBLocalization.IsScPlusMultisection.continuous_pointwiseNorm`: for an sc⁺-multisection
  functor `Λ` and a continuous `N : W_{0,1} → ℝ`, the pointwise norm `N(Λ)` (Definition 13.2.3)
  is continuous on `X`.  Near `x` it is `max_i N(sᵢ(y))` for a local section structure
  `(sᵢ, σᵢ)` (`IsLocalRepOn.pointwiseNorm_eq`), and the `sᵢ` are continuous into `W_{0,1}`.
* `StrongPolyfoldBundle.ScPlusMultisection.continuous_normLam`: **(16.8), the continuity**:
  `z ↦ n(λ)(z)` is continuous for every sc⁺-multisection `λ` and auxiliary norm `n` of `(p, c̄)`.
  It descends from `N(Λ)` along the open quotient map `x ↦ γ(|x|)` (`normLam_eq`, PB).
* `StrongPolyfoldBundle.ScPlusMultisection.normLam_nonneg`, `isGreatest_normLam`: the values
  are `≥ 0` and the maximum is attained, so `n(λ) : Z → [0, ∞)` as printed.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

variable {A : SEP.{u}}

/-- **The pointwise norm in a local section structure**: on `O`, `N(Λ)(y) = max_i N(sᵢ(y))`,
with `sᵢ = oneVal ∘ Gᵢ`. -/
theorem IsLocalRepOn.pointwiseNorm_eq {Λ : A.W → ℚ≥0} {O : Set A.Obj} {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ O s σ)
    (G : Fin k → A.Obj → A.B.One) (hG : ∀ i, ∀ y ∈ O, A.B.oneVal (G i y) = s i y)
    (N : A.B.One → ℝ) (hne : (Finset.univ : Finset (Fin k)).Nonempty) {y : A.Obj} (hy : y ∈ O) :
    pointwiseNorm N Λ y = Finset.univ.sup' hne fun i => N (G i y) := by
  rw [pointwiseNorm, h.suppAt_eq hy, Finset.sup'_eq_csSup_image, Finset.coe_univ, image_univ,
    ← range_comp]
  have e : (normW N ∘ fun i => s i y) = fun i => N (G i y) := funext fun i => by
    change normW N (s i y) = N (G i y)
    rw [← hG i y hy, normW_of_mem N (A.B.oneVal_mem _)]
    rfl
  rw [e]

/-- A local section structure has at least one section (the weights sum to `1`). -/
theorem IsLocalRepOn.univ_nonempty {Λ : A.W → ℚ≥0} {O : Set A.Obj} {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ O s σ) :
    (Finset.univ : Finset (Fin k)).Nonempty := by
  rcases k with _ | k
  · have := h.2.2.1
    simp at this
  · exact Finset.univ_nonempty

/-- **The pointwise norm `N(Λ)` of an sc⁺-multisection functor is continuous** for a continuous
`N : W_{0,1} → ℝ` (2021 Definition 13.2.3, p. 608, used for (16.8), p. 733). -/
theorem IsScPlusMultisection.continuous_pointwiseNorm {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) {N : A.B.One → ℝ} (hN : Continuous N) :
    Continuous (pointwiseNorm N Λ) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨O, k, s, σ, hO, hx, h⟩ := hΛ.exists_isLocalRepOn x
  choose G hG hGs using fun i => (h.2.1 i).2
  have hne := h.univ_nonempty
  have hc : ContinuousAt (fun y => Finset.univ.sup' hne fun i => N (G i y)) x :=
    ContinuousAt.finset_sup'_apply hne fun i _ =>
      hN.continuousAt.comp ((hGs i).continuousOn.continuousAt (hO.mem_nhds hx))
  refine hc.congr ?_
  filter_upwards [hO.mem_nhds hx] with y hy
  exact (h.pointwiseNorm_eq G hG N hne hy).symm

end SBLocalization

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure SBLocalization

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- `x ↦ γ(|x|)` is a quotient map (`π` is an open quotient map, Proposition 7.1.8, and `γ` a
homeomorphism). -/
theorem isQuotientMap_γπ (S : StrongPolyfoldBundleStructure p) :
    IsQuotientMap fun x : S.A.Obj => S.γ (S.A.X.π x) :=
  S.γ.isQuotientMap.comp S.A.X.proposition_7_1_8_isOpenQuotientMap.isQuotientMap

namespace ScPlusMultisection

/-- **(16.8), p. 733 (2017: after Definition 16.36): `n(λ)` is continuous**, for every
sc⁺-multisection `λ` and every auxiliary norm `n` of `(p, c̄)` (Definition 16.3.9). -/
theorem continuous_normLam (s : ScPlusMultisection c) {n : Y → ℝ} (hn : c.IsAuxNorm n) :
    Continuous (c.normLam n s.toFun) := by
  induction s using Quotient.inductionOn with | h a => ?_
  rw [toFun_mk, (isQuotientMap_γπ a.S).continuous_iff]
  have e : c.normLam n a.lam ∘ (fun x : a.S.A.Obj => a.S.γ (a.S.A.X.π x)) =
      pointwiseNorm (a.S.normOf n) a.Λ :=
    funext fun x => normLam_eq a.hS n a.Λ a.lam x fun w _ => a.comm w
  rw [e]
  exact a.isScPlusMultisection.continuous_pointwiseNorm (hn a.S a.hS).isAuxNorm.continuous

/-- **(16.8): the maximum is attained** over every `z` (`n(λ)(z)` is a value `n(y)`, `p(y) = z`,
`λ(y) > 0`). -/
theorem isGreatest_normLam (s : ScPlusMultisection c) (n : Y → ℝ) (z : Z) :
    IsGreatest (c.normY n '' {y | p y = z ∧ 0 < s.toFun y}) (c.normLam n s.toFun z) := by
  induction s using Quotient.inductionOn with | h a => ?_
  obtain ⟨x, rfl⟩ := a.S.surjective_γπ z
  rw [toFun_mk, normLam_eq a.hS n a.Λ a.lam x fun w _ => a.comm w,
    image_normY_eq a.hS n a.Λ a.lam x fun w _ => a.comm w]
  exact a.isScPlusMultisection.isGreatest_pointwiseNorm _ x

/-- **(16.8): `n(λ) ≥ 0`** for an auxiliary norm `n`. -/
theorem normLam_nonneg (s : ScPlusMultisection c) {n : Y → ℝ} (hn : c.IsAuxNorm n) (z : Z) :
    0 ≤ c.normLam n s.toFun z := by
  induction s using Quotient.inductionOn with | h a => ?_
  obtain ⟨x, rfl⟩ := a.S.surjective_γπ z
  rw [toFun_mk, normLam_eq a.hS n a.Λ a.lam x fun w _ => a.comm w]
  obtain ⟨w, -, hmax⟩ := (a.isScPlusMultisection.isGreatest_pointwiseNorm
    (a.S.normOf n) x).1
  rw [← hmax]
  exact normW_nonneg (hn a.S a.hS).isAuxNorm w

end ScPlusMultisection

end StrongPolyfoldBundle

end Polyfold
