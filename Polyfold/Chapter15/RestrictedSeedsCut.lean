import Polyfold.Chapter15.RelativeStepFamilies

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9** (Transversal Extension Theorem), steps (c)–(d), pp. 698–699, with the
functions of Remark 9.5.19 (p. 451) in place of sc-smooth bump functions.

# Seeds from one function

## The text, paraphrased

At a point `x` of `supp(Λ₀ ∘ f)` the proof takes finitely many sc⁺-sections `s_j` supported near
`x` and small, such that the images of the operators of `T(f, Λ₀)(x)` on `T^R_xX` and the
`s_j(x)` span `W_x`, also at the points of `supp(Λ₀ ∘ f)` near `x`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `normW_sectionSmul`: `N(g · s)(y) = |g(y)| · N(s(y))`.
* `isOpen_normW_lt`: `{y | N(s(y)) < M}` is open for an sc⁺-section `s`.
* `IsParamOntoVecRel.smul`: (15.1) relative to `Λ₀` at a point for vectors `v_j` is (15.1) for
  the vectors `a_j v_j`, `a_j ≠ 0`.
* **`exists_seeds_of_function`**: for global sc⁺-sections `S_j`, an open `O ∋ x` and `ε > 0`
  there is an open `O'' ∋ x` in `O` such that every sc-smooth `β : X → ℝ` with support in `O''`
  gives sc⁺-sections `s_j = c · ψ(β) · S_j` with support in `O`, `N(s_j) ≤ ε`, and (15.1)
  relative to `Λ₀` with the `s_j(y)` at every `y` with `β(y) ≠ 0` where it holds with the
  `S_j(y)`.

## Reading

`O''` is `O ∩ {y | N(S_j(y)) < M ∀ j}`; it is determined by the sections `S_j`, before `β`.  One
function per point is used, and it need not be equal to `1` near `x`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set Function Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-! ### The norm of a multiple of a section -/

/-- **`N((g · s)(y)) = |g(y)| · N(s(y))`** for an auxiliary norm (Definition 5.1.1 (1)), when
`s(y)` lies in `W_{0,1}`. -/
theorem normW_sectionSmul {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) {s : A.Obj → A.W}
    (hs : IsSection A.P s) (g : A.Obj → ℝ) {y : A.Obj} (h1 : s y ∈ A.B.oneSet) :
    normW N (Polyfold.sectionSmul A.P g s y) = |g y| * normW N (s y) := by
  let v : A.B.oneFiber y := ⟨⟨s y, hs y⟩, h1⟩
  have hv : Polyfold.sectionSmul A.P g s y = (((g y • v : A.B.oneFiber y) : A.P ⁻¹' {y}) : A.W) := by
    rw [sectionSmul_apply hs]
    rfl
  have hmem : Polyfold.sectionSmul A.P g s y ∈ A.B.oneSet := by rw [hv]; exact (g y • v).2
  rw [normW_of_mem N hmem]
  have e : A.B.oneMk (Polyfold.sectionSmul A.P g s y) hmem = A.B.toOne (g y • v) :=
    A.B.oneVal_injective (by rw [A.B.oneVal_oneMk, A.B.oneVal_toOne, hv])
  rw [e, (hN.fiber y).smul, normW_of_mem N h1]
  rfl

/-- **`{y | N(s(y)) < M}` is open** for an sc⁺-section `s` and an auxiliary norm `N`. -/
theorem isOpen_normW_lt {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) {s : A.Obj → A.W}
    (hs : A.B.IsScPlusSection s) (M : ℝ) : IsOpen {y : A.Obj | normW N (s y) < M} := by
  obtain ⟨-, G, hG, hGs⟩ := IsScPlusSectionOn.of_isScPlusSection hs isOpen_univ
  have hGc : Continuous G := continuousOn_univ.1 hGs.continuousOn
  have e : {y : A.Obj | normW N (s y) < M} = (fun y => N (G y)) ⁻¹' Iio M := by
    ext y
    have h1 := hs.mem_oneSet y
    have e1 : A.B.oneMk (s y) h1 = G y :=
      A.B.oneVal_injective (by rw [A.B.oneVal_oneMk, hG y (mem_univ y)])
    change normW N (s y) < M ↔ N (G y) < M
    rw [normW_of_mem N h1, e1]
  rw [e]
  exact isOpen_Iio.preimage (hN.continuous.comp hGc)

/-! ### Rescaling the vectors of (15.1) -/

/-- **(15.1) relative to `Λ₀` for the vectors `a_j v_j`, `a_j ≠ 0`.** -/
theorem IsParamOntoVecRel.smul {f : A.Obj → A.W} {Λ₀ : A.W → ℚ≥0} {x : A.X.PObj.Level 1}
    {ℓ : ℕ} {v v' : Fin ℓ → A.P ⁻¹' {A.X.PObj.levelVal 1 x}} (H : IsParamOntoVecRel f Λ₀ x v)
    {a : Fin ℓ → ℝ} (ha : ∀ j, a j ≠ 0) (hv : ∀ j, v' j = a j • v j) :
    IsParamOntoVecRel f Λ₀ x v' := by
  intro L hL φ hφ hx m V T hT w
  obtain ⟨u, hu, τ, hτ⟩ := H L hL φ hφ hx m V T hT w
  refine ⟨u, hu, fun j => τ j / a j, ?_⟩
  rw [← hτ]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hv j, smul_smul, div_mul_cancel₀ _ (ha j)]

/-- The function `t ↦ t / (1 + t²)`: smooth, bounded by `1`, and zero only at `0`. -/
def cutProfile (t : ℝ) : ℝ := t / (1 + t ^ 2)

theorem contDiff_cutProfile : ContDiff ℝ ∞ cutProfile :=
  contDiff_id.div (contDiff_const.add (contDiff_id.pow 2)) fun t => by positivity

theorem cutProfile_zero : cutProfile 0 = 0 := by simp [cutProfile]

theorem cutProfile_ne_zero {t : ℝ} (ht : t ≠ 0) : cutProfile t ≠ 0 :=
  div_ne_zero ht (by positivity)

theorem abs_cutProfile_le_one (t : ℝ) : |cutProfile t| ≤ 1 := by
  unfold cutProfile
  rw [abs_div, abs_of_pos (show (0 : ℝ) < 1 + t ^ 2 by positivity), div_le_one (by positivity)]
  have h := sq_nonneg (|t| - 1)
  have e : |t| ^ 2 = t ^ 2 := sq_abs t
  nlinarith

/-! ### Seeds from one function -/

/-- **Seeds from one function** (steps (c)–(d) of the proof of Theorem 15.3.9, 2021
pp. 698–699, with one function of Remark 9.5.19 per point).  Let `S_j` be finitely many global
sc⁺-sections, `N` an auxiliary norm, `O ∋ x` open and `ε > 0`.  There is an open `O'' ∋ x` in
`O` such that for every sc-smooth `β : X → ℝ` with support in `O''` there are sc⁺-sections `s_j`
with support in `O` and `N(s_j) ≤ ε` such that, at every `y ∈ X₁` with `β(y) ≠ 0`, (15.1)
relative to `Λ₀` with the vectors `S_j(y)` gives (15.1) with the vectors `s_j(y)`. -/
theorem exists_seeds_of_function (f : A.Obj → A.W) (Λ₀ : A.W → ℚ≥0) {N : A.B.One → ℝ}
    (hN : A.B.IsAuxNorm N) {ℓ : ℕ} {S : Fin ℓ → A.Obj → A.W}
    (hS : ∀ j, A.B.IsScPlusSection (S j)) {x : A.Obj} {O : Set A.Obj} (hO : IsOpen O)
    (hxO : x ∈ O) {ε : ℝ} (hε : 0 < ε) :
    ∃ O'' : Set A.Obj, IsOpen O'' ∧ x ∈ O'' ∧ O'' ⊆ O ∧
      ∀ β : A.Obj → ℝ, A.X.PObj.IsScSmoothMap realPolyfold β → tsupport β ⊆ O'' →
        ∃ (s : Fin ℓ → A.Obj → A.W) (hs : ∀ j, A.B.IsScPlusSection (s j)),
          (∀ j, sectionSupport A.P (s j) ⊆ O) ∧ (∀ j y, normW N (s j y) ≤ ε) ∧
          ∀ y : A.X.PObj.Level 1, β (A.X.PObj.levelVal 1 y) ≠ 0 →
            IsParamOntoVecRel f Λ₀ y
              (fun j => ⟨S j (A.X.PObj.levelVal 1 y), (hS j).1 _⟩) →
            IsParamOntoVecRel f Λ₀ y
              (fun j => ⟨s j (A.X.PObj.levelVal 1 y), (hs j).1 _⟩) := by
  classical
  set M : ℝ := 1 + ∑ j, normW N (S j x) with hMdef
  have hM0 : ∀ j, 0 ≤ normW N (S j x) := fun j => normW_nonneg hN _
  have hM : 0 < M := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hM0 j
    rw [hMdef]; linarith
  have hxM : ∀ j, normW N (S j x) < M := fun j => by
    have := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hM0 i) (Finset.mem_univ j)
    rw [hMdef]; linarith
  refine ⟨O ∩ ⋂ j, {y | normW N (S j y) < M},
    hO.inter (isOpen_iInter_of_finite fun j => isOpen_normW_lt hN (hS j) M),
    ⟨hxO, mem_iInter.2 hxM⟩, inter_subset_left, fun β hβ hsupp => ?_⟩
  set g : A.Obj → ℝ := fun y => ε / M * cutProfile (β y) with hg
  have hgsm : A.X.PObj.IsScSmoothMap realPolyfold g := by
    have h1 : A.X.PObj.IsScSmoothMap realPolyfold (cutProfile ∘ β) :=
      hβ.comp_contDiff contDiff_cutProfile
    have h2 : A.X.PObj.IsScSmoothMap realPolyfold
        ((fun t : ℝ => ε / M * t) ∘ (cutProfile ∘ β)) :=
      h1.comp_contDiff (contDiff_const.mul contDiff_id)
    exact h2
  have hg0 : ∀ y, β y = 0 → g y = 0 := fun y hy => by
    rw [hg]; dsimp only; rw [hy, cutProfile_zero, mul_zero]
  have hgne : ∀ y, β y ≠ 0 → g y ≠ 0 := fun y hy =>
    mul_ne_zero (div_pos hε hM).ne' (cutProfile_ne_zero hy)
  have hgle : ∀ y, |g y| ≤ ε / M := fun y => by
    rw [hg]; dsimp only
    rw [abs_mul, abs_of_pos (div_pos hε hM)]
    exact mul_le_of_le_one_right (div_pos hε hM).le (abs_cutProfile_le_one _)
  have hsec : ∀ j, IsSection A.P (S j) := fun j => (hS j).1
  refine ⟨fun j => Polyfold.sectionSmul A.P g (S j), fun j => (hS j).smul_left hgsm,
    fun j => ?_, fun j y => ?_, fun y hy H => ?_⟩
  · refine (closure_mono fun y hy => ?_).trans (hsupp.trans inter_subset_left)
    intro h0
    apply hy
    change Polyfold.sectionSmul A.P g (S j) y = fiberZero A.P y
    rw [sectionSmul_apply (hsec j), hg0 y h0, zero_smul]
    rfl
  · rw [normW_sectionSmul hN (hsec j) g ((hS j).mem_oneSet y)]
    by_cases hy : β y = 0
    · rw [hg0 y hy, abs_zero, zero_mul]; exact hε.le
    · have hyO : y ∈ O ∩ ⋂ j, {y | normW N (S j y) < M} := hsupp (subset_tsupport β hy)
      have hlt : normW N (S j y) < M := mem_iInter.1 hyO.2 j
      calc |g y| * normW N (S j y) ≤ ε / M * M :=
            mul_le_mul (hgle y) hlt.le (normW_nonneg hN _) (div_pos hε hM).le
        _ = ε := div_mul_cancel₀ ε hM.ne'
  · refine H.smul (a := fun _ => g (A.X.PObj.levelVal 1 y)) (fun _ => hgne _ hy) fun j => ?_
    exact Subtype.ext (sectionSmul_apply (hsec j) _)

end SBLocalization

end Polyfold
