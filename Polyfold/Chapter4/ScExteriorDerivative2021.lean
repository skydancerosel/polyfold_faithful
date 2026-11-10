import Polyfold.Chapter4.ScForms2021
import Mathlib.Analysis.Calculus.DifferentialForm.VectorField

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4: the exterior
derivative `d : Ωᵏ(Xⁱ) → Ωᵏ⁺¹(Xⁱ⁺¹)` (pp. 196–197, the formula for `dω` on p. 197; 2017 /
preprint: before Definition 4.27), with the Lie bracket of §4.5.1 (p. 200).  Numbers and pages are
the 2021 text's.

# The exterior derivative of sc-forms

## The text, paraphrased

(p. 197) For an sc-form `ω` on `Xⁱ` and sc-smooth vector fields `A₀, …, A_k`, `dω` on
`⊕_{k+1} T(Xⁱ⁺¹)` is given by "the familiar formula": a first sum of the terms
`(-1)ʲ D(ω(A₀, …, Âⱼ, …, A_k)) · Aⱼ`, and a second sum over `ℓ < j` of
`(-1)^{ℓ+k} ω([A_ℓ, Aⱼ], A₀, …, Â_ℓ, …, Âⱼ, …, A_k)`, where `[A, B] = DA·B − DB·A` (p. 200).
This defines `d` as a linear operator, which commutes with the inclusions, passes to `Ω*_∞(X)`
and has `d² = 0`.

## What is formalized

* **The invariant formula and Mathlib's `extDeriv`** (normed spaces, `E` any real normed space):
  `bookBracket A B = DA·B − DB·A = −lieBracket ℝ A B` (`bookBracket_eq_neg_lieBracket`);
  `invariantFormula σ ω V x`, the right side of the p. 197 formula with the sign `σ ℓ j` in front
  of the pair `ℓ < j`; `extDeriv_eq_invariantFormula`: with `σ ℓ j = (-1)^{ℓ+j+1}`
  (`correctSign`) the formula **is** `extDeriv` (from Mathlib's `extDeriv_apply_vectorField`), so
  it is tensorial and `d² = 0` (Mathlib's `extDeriv_extDeriv`).
* **The printed sign**: `invariantFormula_printedSign_counterexample` (`k = 1`, `ω = dy` on `ℝ²`,
  `A₀ = (1, 0)`, `A₁(p) = (0, p₁)`): with `(-1)^{ℓ+k}` (`printedSign`) the formula gives `2`, while
  `dω = 0`; the same with the sign `(-1)^{ℓ+j}` (`item158Sign`); and replacing `A₁` by `0`
  (the same value at `0`) gives `0`, so the printed expression is not tensorial.
* **The local exterior derivative in the sc-setting**, for `U` open in a partial quadrant of an
  sc-Banach space `E`: `ambientD U Ω` on `⊕_{k+1} T(U¹)`,
  `dΩ(y, h₀, …, h_k) = Σⱼ (-1)ʲ DΩ(y, h₀, …, ĥⱼ, …, h_k)(hⱼ, 0)` (`ambientD_apply`), built from
  `TΩ` and the sc-operators `whitneyDelete j`.  `IsScSmooth.ambientD`: `dΩ` is sc-smooth.
  `scDeriv_relation`: linear relations among the fibre values of `Ω` pass to `DΩ(·)(η, 0)`;
  hence `baseDerivAlt` and `ambientD_whitneyMk`: `dΩ(y, ·)` is the alternation of the base
  derivative (Mathlib's `alternatizeUncurryFin`), alternating `(k+1)`-linear.
  `IsAmbientScForm.ambientD`: **`d` maps sc-`k`-forms on `U` to sc-`(k+1)`-forms on `U¹`**.
* **In a local model** `(O, C, E)` with retraction `r`: `retractD R ω = d(ω ∘ ⊕ₖ Tr)` and
  `IsRetractScForm.retractD`: **`d` maps sc-forms on `O` to sc-forms on `O¹`**.

## What is not formalized

Not in this file, but in `ScFormsNatural2021.lean` – `ScFormsLower2021.lean`: the independence
of `retractD` from the retraction and from the chart (the step from the local `d` to `d` on an
M-polyfold, by the chain rule and the symmetry of second derivatives), `d` on an M-polyfold,
`d² = 0` in the sc-setting, the commutation with `X^{i+1} → X^i`, `d` on `Ω*_∞(X)` and
Definition 4.4.6.  Not formalized: the commutation of `d` with pull-backs along sc-smooth maps of
M-polyfolds (p. 198; the local form is `retractD_comp_retractWhitneyMap`), the wedge product,
and the relative complex `Ω*_∞(X, ∂X)`.
-/

open Set Function VectorField

noncomputable section

namespace Polyfold

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- **The Lie bracket of the text** (2021 §4.5.1, p. 200), on a normed space:
`[A, B](x) = DA(x)·B(x) − DB(x)·A(x)`. -/
def bookBracket (A B : E → E) (x : E) : E := fderiv ℝ A x (B x) - fderiv ℝ B x (A x)

/-- The text's bracket is the negative of Mathlib's `lieBracket` (`DB·A − DA·B`). -/
theorem bookBracket_eq_neg_lieBracket (A B : E → E) (x : E) :
    bookBracket A B x = -lieBracket ℝ A B x := by
  simp [bookBracket, lieBracket]

/-- **The right side of the formula for `dω` on p. 197**, for a `k`-form `ω` (`k = n + 1`) and
fields `V₀, …, V_k`, with the text's bracket and the sign `σ ℓ j` in front of the term of the pair
`ℓ < j`: `Σᵢ (-1)ⁱ D(ω(V₀, …, V̂ᵢ, …, V_k))·Vᵢ + Σ_{ℓ<j} σ ℓ j · ω([V_ℓ, Vⱼ], V₀, …, V̂_ℓ, …, V̂ⱼ, …)`
(the pair `(ℓ, j)` is `(i, j' + 1)` with `i ≤ j'`; the first sum is indexed by `j` in the text,
by `i` in its display). -/
def invariantFormula (σ : ℕ → ℕ → ℤ) (ω : E → E [⋀^Fin (n + 1)]→L[ℝ] ℝ)
    (V : Fin (n + 2) → E → E) (x : E) : ℝ :=
  (∑ i, (-1 : ℤ) ^ i.val • fderiv ℝ (fun x ↦ ω x (i.removeNth (V · x))) x (V i x)) +
    ∑ i : Fin (n + 1), ∑ j ≥ i, σ i.val (j.val + 1) •
      ω x (Matrix.vecCons (bookBracket (V i.castSucc) (V j.succ) x)
        (j.removeNth <| i.castSucc.removeNth (V · x)))

/-- The sign `(-1)^{ℓ+j+1}` for which the formula with the text's bracket is `dω`. -/
def correctSign (l j : ℕ) : ℤ := (-1) ^ (l + j + 1)

/-- The sign printed on p. 197, `(-1)^{ℓ+k}`, for `k`-forms. -/
def printedSign (k : ℕ) (l _j : ℕ) : ℤ := (-1) ^ (l + k)

/-- The sign `(-1)^{ℓ+j}` of the classical formula (Findings, item 158), which is the right one
for the bracket `DB·A − DA·B`. -/
def item158Sign (l j : ℕ) : ℤ := (-1) ^ (l + j)

/-- **2021 p. 197, the formula for `dω` with the sign `(-1)^{ℓ+j+1}`**: for a form `ω` and vector
fields `Vᵢ` differentiable at `x`, `dω(x)(V₀(x), …, V_k(x))` (Mathlib's `extDeriv`) is the
invariant formula with the text's bracket `[A, B] = DA·B − DB·A` and the sign `(-1)^{ℓ+j+1}`.
(From `extDeriv_apply_vectorField` and `bookBracket_eq_neg_lieBracket`.) -/
theorem extDeriv_eq_invariantFormula {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] ℝ} {V : Fin (n + 2) → E → E}
    {x : E} (hω : DifferentiableAt ℝ ω x) (hV : ∀ i, DifferentiableAt ℝ (V i) x) :
    extDeriv ω x (V · x) = invariantFormula correctSign ω V x := by
  have h : ∀ (v : E) (w : Fin n → E), ω x (Matrix.vecCons (-v) w) = -ω x (Matrix.vecCons v w) := by
    intro v w
    have := (ω x).map_update_smul (Matrix.vecCons v w) 0 (-1 : ℝ) v
    simpa [Matrix.vecCons, Fin.cons_update] using this
  rw [extDeriv_apply_vectorField hω hV, invariantFormula, sub_eq_add_neg]
  refine congrArg₂ (· + ·) (by simp) ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bookBracket_eq_neg_lieBracket, h, correctSign]
  simp [pow_succ, pow_add]


/-- `dy` on `ℝ²`. -/
def dyForm : ℝ × ℝ → (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ :=
  fun _ => ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ (0 : Fin 1)
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

lemma dyForm_apply (x : ℝ × ℝ) (v : Fin 1 → ℝ × ℝ) : dyForm x v = (v 0).2 := rfl

/-- The fields `A₀ = (1, 0)`, `A₁(p) = (0, p₁)`. -/
def cexField : Fin 2 → ℝ × ℝ → ℝ × ℝ :=
  ![fun _ => (1, 0), (ContinuousLinearMap.inr ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)]

/-- The fields `A₀ = (1, 0)`, `A₁ = 0`: the same values at `0`. -/
def cexField' : Fin 2 → ℝ × ℝ → ℝ × ℝ := ![fun _ => (1, 0), fun _ => 0]

lemma cexField_zero (x : ℝ × ℝ) : cexField 0 x = (1, 0) := rfl
lemma cexField_one (x : ℝ × ℝ) : cexField 1 x = (0, x.1) := rfl

/-- The formula on `(dy; (1, 0), (0, p₁))`, for any sign: `1 − σ(0, 1)`. -/
theorem invariantFormula_cexField (σ : ℕ → ℕ → ℤ) (x : ℝ × ℝ) :
    invariantFormula σ dyForm cexField x = 1 - σ 0 1 := by
  have h0 : (fun y : ℝ × ℝ => dyForm y ((0 : Fin 2).removeNth (cexField · y))) =
      ContinuousLinearMap.fst ℝ ℝ ℝ := by
    funext y; rfl
  have h1 : (fun y : ℝ × ℝ => dyForm y ((1 : Fin 2).removeNth (cexField · y))) = fun _ => 0 := by
    funext y; rfl
  have hA0 : fderiv ℝ (cexField 0) x = 0 := fderiv_const_apply _
  have hA1 : fderiv ℝ (cexField 1) x =
      (ContinuousLinearMap.inr ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) :=
    ContinuousLinearMap.fderiv _
  rw [invariantFormula, Fin.sum_univ_two, Fin.sum_univ_one]
  have hb : bookBracket (cexField (Fin.castSucc 0)) (cexField (Fin.succ 0)) x = (0, -1) := by
    change bookBracket (cexField 0) (cexField 1) x = _
    rw [bookBracket, hA0, hA1]; simp [cexField_zero]
  rw [h0, h1, ContinuousLinearMap.fderiv, fderiv_const_apply,
    Finset.sum_eq_single_of_mem 0 (by simp) (fun b _ hb => absurd (Fin.fin_one_eq_zero b) hb)]
  rw [show (0 : Fin 1).succ = Fin.succ 0 from rfl, hb, dyForm_apply]
  simp [cexField_zero, sub_eq_add_neg]


/-- The formula on `(dy; (1, 0), 0)`, for any sign: `0`. -/
theorem invariantFormula_cexField' (σ : ℕ → ℕ → ℤ) (x : ℝ × ℝ) :
    invariantFormula σ dyForm cexField' x = 0 := by
  have h0 : (fun y : ℝ × ℝ => dyForm y ((0 : Fin 2).removeNth (cexField' · y))) = fun _ => 0 := by
    funext y; rfl
  have h1 : (fun y : ℝ × ℝ => dyForm y ((1 : Fin 2).removeNth (cexField' · y))) = fun _ => 0 := by
    funext y; rfl
  have hb : bookBracket (cexField' (Fin.castSucc 0)) (cexField' (Fin.succ 0)) x = 0 := by
    change fderiv ℝ (fun _ => ((1 : ℝ), (0 : ℝ))) x 0 - fderiv ℝ (fun _ => (0 : ℝ × ℝ)) x (1, 0) = 0
    simp
  rw [invariantFormula, Fin.sum_univ_two, Fin.sum_univ_one, h0, h1, fderiv_const_apply,
    Finset.sum_eq_single_of_mem 0 (by simp) (fun b _ hb => absurd (Fin.fin_one_eq_zero b) hb)]
  rw [show (0 : Fin 1).succ = Fin.succ 0 from rfl, hb, dyForm_apply]
  simp

theorem differentiableAt_cexField (i : Fin 2) (x : ℝ × ℝ) : DifferentiableAt ℝ (cexField i) x := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact differentiableAt_const _
  · rw [Fin.fin_one_eq_zero j]
    exact ContinuousLinearMap.differentiableAt _

/-- `d(dy) = 0`. -/
theorem extDeriv_dyForm (x : ℝ × ℝ) : extDeriv dyForm x (cexField · x) = 0 := by
  rw [extDeriv_eq_invariantFormula (ω := dyForm)
      (differentiableAt_const (ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ (0 : Fin 1)
        (ContinuousLinearMap.snd ℝ ℝ ℝ))) (differentiableAt_cexField · x),
    invariantFormula_cexField, correctSign]
  norm_num

/-- **The formula for `dω` on p. 197 with the printed sign `(-1)^{ℓ+k}` does not hold as we read
it** (with the text's bracket of p. 200): for `k = 1`, `ω = dy` on `ℝ²`, `A₀ = (1, 0)`,
`A₁(p) = (0, p₁)`, its right side at `0` is `2` while `dω = 0`; the sign `(-1)^{ℓ+j}` of the
classical formula gives `2` as well; and for `A₁' = 0`, which agrees with `A₁` at `0`, the printed
right side is `0`, so it does not define a form.  (With `(-1)^{ℓ+j+1}` it is `dω`,
`extDeriv_eq_invariantFormula`.) -/
theorem invariantFormula_printedSign_counterexample : invariantFormula (printedSign 1) dyForm cexField 0 = 2 ∧
    invariantFormula item158Sign dyForm cexField 0 = 2 ∧
    extDeriv dyForm 0 (cexField · 0) = 0 ∧
    (∀ i, cexField i 0 = cexField' i 0) ∧
    invariantFormula (printedSign 1) dyForm cexField' 0 = 0 := by
  refine ⟨?_, ?_, extDeriv_dyForm 0, fun i => ?_, invariantFormula_cexField' _ 0⟩
  · rw [invariantFormula_cexField, printedSign]; norm_num
  · rw [invariantFormula_cexField, item158Sign]; norm_num
  · refine Fin.cases rfl (fun j => ?_) i
    rw [Fin.fin_one_eq_zero j]
    show ((0 : ℝ), (0 : ℝ × ℝ).1) = 0
    rfl

end NormedSpace

/-! ### The local exterior derivative of an sc-form on an open subset of a partial quadrant -/

namespace ScBanach

variable {E : ScBanach}

/-- Deleting the `j`-th of `k + 1` vectors, `(v₀, …, v_k) ↦ (v₀, …, v̂_j, …, v_k)`. -/
def removeNthL (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ} (j : Fin (k + 1)) :
    (Fin (k + 1) → V) →L[ℝ] (Fin k → V) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (j.succAbove i)

@[simp] lemma removeNthL_apply (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
    (j : Fin (k + 1)) (v : Fin (k + 1) → V) : removeNthL V j v = j.removeNth v := rfl

variable (E) in
/-- **The operator behind the `j`-th term of `dω`**: `⊕_{k+1} T(E¹) → T(⊕ₖ TE)`,
`(y, h₀, …, h_k) ↦ ((y, h₀, …, ĥ_j, …, h_k), (h_j, 0))`, an sc-operator. -/
def whitneyDelete (k : ℕ) (j : Fin (k + 1)) :
    ScOperator (E.shift.whitney (k + 1)) ((E.whitney k).tangent) where
  lvl m := ((ContinuousLinearMap.fst ℝ _ _).prod ((E.fiberPackL (m + 1) k).comp
      ((removeNthL (E (m + 1)) j).comp
        ((E.shift.fiberVecL m (k + 1)).comp (ContinuousLinearMap.snd ℝ _ _))))).prod
    (((ContinuousLinearMap.proj j).comp
      ((E.shift.fiberVecL m (k + 1)).comp (ContinuousLinearMap.snd ℝ _ _))).prod 0)
  incl_comm m q := by
    refine Prod.ext (Prod.ext rfl (fiberVecL_injective (funext fun i => ?_)))
      (Prod.ext ?_ (by change (E.fiberPow k).incl m 0 = 0; exact map_zero _))
    · change E.fiberVecL (m + 1) k ((E.fiberPow k).incl (m + 1) (E.fiberPackL (m + 2) k
          (j.removeNth (E.shift.fiberVecL (m + 1) (k + 1) q.2)))) i =
        E.fiberVecL (m + 1) k (E.fiberPackL (m + 1) k
          (j.removeNth (E.shift.fiberVecL m (k + 1) ((E.shift.fiberPow (k + 1)).incl m q.2)))) i
      rw [fiberVecL_incl, fiberVecL_fiberPackL, fiberVecL_fiberPackL,
        Fin.removeNth_apply, Fin.removeNth_apply, fiberVecL_incl (E := E.shift)]
    · change E.shift.incl m (E.shift.fiberVecL (m + 1) (k + 1) q.2 j) =
        E.shift.fiberVecL m (k + 1) ((E.shift.fiberPow (k + 1)).incl m q.2) j
      rw [fiberVecL_incl (E := E.shift)]

lemma whitneyDelete_apply {k : ℕ} (j : Fin (k + 1)) (q : (E.shift.whitney (k + 1)) 0) :
    E.whitneyDelete k j 0 q = ((q.1, E.fiberPackL 1 k (j.removeNth (whitneyVec q))),
      whitneyMk (whitneyVec q j) 0) := by
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change (0 : (E.fiberPow k) 0) = E.fiberPackL 0 k 0
  exact (map_zero _).symm

end ScBanach

variable {E : ScBanach} {C U : Set (E 0)} {k : ℕ}

/-- `whitneyDelete` maps `⊕_{k+1} T(U¹)` into `T(⊕ₖ TU)`. -/
lemma mapsTo_whitneyDelete (j : Fin (k + 1)) :
    MapsTo (E.whitneyDelete k j 0) (E.shift.whitneySet (k + 1) (E.lvlSet U 1))
      ((E.whitney k).tangentSet (E.whitneySet k U)) := fun q hq => by
  rw [ScBanach.whitneyDelete_apply]
  change (E.whitney k).toBase 1 (q.1, _) ∈ E.whitneySet k U
  rw [ScBanach.prod_toBase]
  exact ⟨(ScBanach.mem_whitneySet.1 hq : _), mem_univ _⟩

/-- **The local exterior derivative** (2021 p. 197, the formula in coordinates) of a map
`Ω : ⊕ₖ TU → ℝ`: on `⊕_{k+1} T(U¹)`,
`dΩ(y, h₀, …, h_k) = Σⱼ (-1)ʲ DΩ(y, h₀, …, ĥⱼ, …, h_k)(hⱼ, 0)`,
the `j`-th term being the second component of `TΩ ∘ whitneyDelete j`. -/
def ambientD (U : Set (E 0)) (Ω : (E.whitney k) 0 → ℝ) (q : (E.shift.whitney (k + 1)) 0) : ℝ :=
  ∑ j : Fin (k + 1), (-1 : ℝ) ^ j.val *
    (tangentMap (F := ScBanach.const ℝ) (E.whitneySet k U) Ω (E.whitneyDelete k j 0 q)).2

lemma ambientD_apply (Ω : (E.whitney k) 0 → ℝ) (q : (E.shift.whitney (k + 1)) 0) :
    ambientD U Ω q = ∑ j : Fin (k + 1), (-1 : ℝ) ^ j.val *
      scDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) Ω (q.1, E.fiberPackL 1 k (j.removeNth (ScBanach.whitneyVec q)))
        (ScBanach.whitneyMk (ScBanach.whitneyVec q j) 0) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ScBanach.whitneyDelete_apply]; rfl

/-- A real multiple of a real sc^k map is sc^k. -/
theorem IsSck.real_const_mul {X : ScBanach} {W : Set (X 0)} {n : ℕ} (hW : IsScDomain X W)
    {g : X 0 → (ScBanach.const ℝ) 0} (hg : IsSck n X (ScBanach.const ℝ) W g) (c : ℝ) :
    IsSck n X (ScBanach.const ℝ) W fun z => c * g z := by
  have h := IsSck.comp hW (isScDomain_univ _)
    ((ScOperator.ofConst (c • ContinuousLinearMap.id ℝ ℝ)).isScSmooth (isScDomain_univ _) n)
    hg (mapsTo_univ _ _)
  convert h using 1
  funext z; simp [ScOperator.ofConst]

/-- **The local exterior derivative is sc-smooth**: for `Ω` sc-smooth on `⊕ₖ TU`, `dΩ` is
sc-smooth on `⊕_{k+1} T(U¹)` (`TΩ` is sc-smooth and the `whitneyDelete j` are sc-operators). -/
theorem IsScSmooth.ambientD (hU : IsRelOpenInQuadrant E C U) {Ω : (E.whitney k) 0 → ℝ}
    (hΩ : IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet k U) Ω) :
    IsScSmooth (F := ScBanach.const ℝ) (E.shift.whitneySet (k + 1) (E.lvlSet U 1))
      (ambientD U Ω) := by
  have hD := (hU.shift.whitneySet (k + 1)).isScDomain
  have hT : IsScSmooth ((E.whitney k).tangentSet (E.whitneySet k U))
      (tangentMap (F := ScBanach.const ℝ) (E.whitneySet k U) Ω) := fun n => (hΩ (n + 1)).2
  have hj : ∀ j : Fin (k + 1), IsScSmooth (F := ScBanach.const ℝ)
      (E.shift.whitneySet (k + 1) (E.lvlSet U 1)) fun q =>
        (tangentMap (F := ScBanach.const ℝ) (E.whitneySet k U) Ω (E.whitneyDelete k j 0 q)).2 :=
    fun j =>
    ((ScBanach.prodSndOp _ _).isScSmooth (isScDomain_univ _)).comp hD (isScDomain_univ _)
      (hT.comp hD (hU.whitneySet k).isScDomain.tangentSet ((E.whitneyDelete k j).isScSmooth hD)
        (mapsTo_whitneyDelete j)) (mapsTo_univ _ _)
  intro n
  exact IsSck.sum hD Finset.univ fun j _ => (hj j n).real_const_mul hD _

/-! ### Fibre relations pass to the base derivative -/

/-- **Relations in the fibre pass to the derivative along the base**: if `Σₐ cₐ Ω(z, pₐ) = 0` for
all `z ∈ U₁` (fixed fibre points `pₐ` of level `1`), then `Σₐ cₐ DΩ(y, pₐ)(η, 0) = 0` for
`y ∈ U₂` and `η ∈ E₁`.  (Differentiate along `z ↦ (z, pₐ)` on level `1`, then use that `E₂` is
dense in `E₁`.) -/
theorem scDeriv_relation (hU : IsRelOpenInQuadrant E C U) {Ω : (E.whitney k) 0 → ℝ}
    (hΩ : IsSc1 (F := ScBanach.const ℝ) (E.whitneySet k U) Ω) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (p : ι → (E.fiberPow k) 1)
    (hrel : ∀ z ∈ E.lvlSet U 1, ∑ a ∈ s, c a * Ω (z, (E.fiberPow k).toBase 1 (p a)) = 0)
    {y : E 2} (hy : y ∈ E.shift.lvlSet (E.lvlSet U 1) 1) (η : E 1) :
    ∑ a ∈ s, c a * scDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) Ω (y, p a)
      (ScBanach.whitneyMk η 0) = 0 := by
  set S := E.shift.lvlSet (E.lvlSet U 1) 1
  set D := scDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) Ω
  have hmem : ∀ a, ∀ z ∈ S, ((z, p a) : (E.whitney k) 1) ∈ (E.whitney k).lvlSet (E.whitneySet k U) 1 :=
    fun a z hz => by
      rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase]; exact ⟨hz, mem_univ _⟩
  -- the derivative of `g : z ↦ Σ cₐ Ω(z, pₐ)` on level 1
  set g : E.shift 1 → ℝ := fun z => ∑ a ∈ s, c a • (Ω ∘ (E.whitney k).toBase 1) (z, p a) with hg
  have hderiv : HasFDerivWithinAt g
      (∑ a ∈ s, c a • (((D (y, p a)).comp ((E.whitney k).toBase 1)).comp
        (ContinuousLinearMap.inl ℝ (E.shift 1) ((E.fiberPow k) 1)))) S y := by
    refine HasFDerivWithinAt.fun_sum (u := s) (s := S) (x := y)
      (A := fun a (z : E.shift 1) => c a • (Ω ∘ (E.whitney k).toBase 1) (z, p a))
      (A' := fun a => c a • (((D (y, p a)).comp ((E.whitney k).toBase 1)).comp
        (ContinuousLinearMap.inl ℝ (E.shift 1) ((E.fiberPow k) 1)))) fun a _ => ?_
    have h1 := hΩ.isSc1With_scDeriv.hasFDerivWithinAt (y, p a) (hmem a y hy)
    have h2 : HasFDerivAt (fun z : E.shift 1 => ((z, p a) : (E.whitney k) 1))
        (ContinuousLinearMap.inl ℝ (E.shift 1) ((E.fiberPow k) 1)) y :=
      (hasFDerivAt_id y).prodMk (hasFDerivAt_const (p a) y)
    exact (h1.comp y h2.hasFDerivWithinAt (hmem a)).const_smul (c a)
  have hg0 : ∀ z ∈ S, g z = 0 := fun z hz => by
    simp only [hg, Function.comp_apply, smul_eq_mul]
    exact hrel _ hz
  have hzero : HasFDerivWithinAt g (0 : E.shift 1 →L[ℝ] ℝ) S y :=
    (hasFDerivWithinAt_const (0 : ℝ) y S).congr hg0 (hg0 y hy)
  have huniq := (hU.shift.isScDomain.uniqueDiffWithinAt 1 y hy).eq hderiv hzero
  -- extend from `E₂` to `E₁` by density
  set L : E.shift 0 →L[ℝ] ℝ := ∑ a ∈ s, c a • (D (y, p a)).comp
    (ContinuousLinearMap.inl ℝ (E.shift 0) ((E.fiberPow k) 0))
  have htb : ∀ z : E.shift 1, (E.whitney k).toBase 1
      (ContinuousLinearMap.inl ℝ (E.shift 1) ((E.fiberPow k) 1) z) =
        ContinuousLinearMap.inl ℝ (E.shift 0) ((E.fiberPow k) 0) (E.shift.toBase 1 z) := fun z => by
    rw [ContinuousLinearMap.inl_apply, ScBanach.prod_toBase, map_zero]; rfl
  have hLc : L.comp (E.shift.toBase 1) = 0 := by
    rw [← huniq]
    ext z
    simp only [L, ContinuousLinearMap.comp_apply, _root_.sum_apply,
      _root_.smul_apply, htb]
  have hL : (L : E.shift 0 → ℝ) ∘ E.shift.toBase 1 = (fun _ => (0 : ℝ)) ∘ E.shift.toBase 1 := by
    funext z
    exact congrArg (fun T : E.shift 1 →L[ℝ] ℝ => T z) hLc
  have := congrFun ((E.shift.denseRange_inclK 0 1 : DenseRange (E.shift.toBase 1)).equalizer
    L.continuous continuous_const hL) η
  simp only [L, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, smul_eq_mul] at this
  simpa [ScBanach.whitneyMk] using this

/-! ### Multilinearity and skew-symmetry of `dΩ` -/

section Alternating

variable (hU : IsRelOpenInQuadrant E C U) {Ω : (E.whitney k) 0 → ℝ}
  (hΩ : IsSc1 (F := ScBanach.const ℝ) (E.whitneySet k U) Ω)
  (hA : ∀ z ∈ E.lvlSet U 1, ∃ A : E 1 [⋀^Fin k]→ₗ[ℝ] ℝ, ∀ w : Fin k → E 1,
    Ω (z, (E.fiberPow k).toBase 1 (E.fiberPackL 1 k w)) = A w)
  {y : E 2} (hy : y ∈ E.shift.lvlSet (E.lvlSet U 1) 1)

include hU hΩ hA hy

omit hA in
lemma scDeriv_relation_fin {n : ℕ} (c : Fin n → ℝ) (p : Fin n → (E.fiberPow k) 1)
    (hrel : ∀ z ∈ E.lvlSet U 1, ∑ a, c a * Ω (z, (E.fiberPow k).toBase 1 (p a)) = 0) (η : E 1) :
    ∑ a, c a * scDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) Ω (y, p a)
      (ScBanach.whitneyMk η 0) = 0 :=
  scDeriv_relation hU hΩ Finset.univ c p hrel hy η

/-- **The derivative along the base of a fibrewise alternating map is fibrewise alternating**:
`w ↦ DΩ(y, w)(η, 0)` is an alternating `k`-linear map on `E₁` (`scDeriv_relation`). -/
def baseDerivAlt (η : E 1) : E 1 [⋀^Fin k]→ₗ[ℝ] ℝ where
  toFun w := scDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) Ω (y, E.fiberPackL 1 k w)
    (ScBanach.whitneyMk η 0)
  map_update_add' w i a b := by
    have h := scDeriv_relation_fin hU hΩ hy ![1, -1, -1]
      ![E.fiberPackL 1 k (update w i (a + b)), E.fiberPackL 1 k (update w i a),
        E.fiberPackL 1 k (update w i b)] (fun z hz => by
          obtain ⟨A, hA⟩ := hA z hz
          simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hA, A.map_update_add]
          ring) η
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h
    linarith
  map_update_smul' w i c a := by
    have h := scDeriv_relation_fin hU hΩ hy ![1, -c]
      ![E.fiberPackL 1 k (update w i (c • a)), E.fiberPackL 1 k (update w i a)] (fun z hz => by
          obtain ⟨A, hA⟩ := hA z hz
          simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hA,
            A.map_update_smul, smul_eq_mul]
          ring) η
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [smul_eq_mul]; linarith
  map_eq_zero_of_eq' w i j hij hne := by
    have h := scDeriv_relation_fin hU hΩ hy ![1] ![E.fiberPackL 1 k w] (fun z hz => by
          obtain ⟨A, hA⟩ := hA z hz
          simp only [Fin.sum_univ_one, Matrix.cons_val_zero, hA, A.map_eq_zero_of_eq w hij hne,
            mul_zero]) η
    simpa using h

lemma baseDerivAlt_apply (η : E 1) (w : Fin k → E 1) :
    baseDerivAlt hU hΩ hA hy η w = scDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) Ω
      (y, E.fiberPackL 1 k w) (ScBanach.whitneyMk η 0) := rfl

/-- `η ↦ (w ↦ DΩ(y, w)(η, 0))` is linear. -/
def baseDerivLin : E 1 →ₗ[ℝ] E 1 [⋀^Fin k]→ₗ[ℝ] ℝ where
  toFun := baseDerivAlt hU hΩ hA hy
  map_add' η η' := by
    ext w
    simp only [baseDerivAlt_apply, AlternatingMap.add_apply]
    rw [show ScBanach.whitneyMk (E := E) (η + η') 0 =
      ScBanach.whitneyMk η 0 + ScBanach.whitneyMk η' 0 by
        simp [ScBanach.whitneyMk], map_add]
  map_smul' c η := by
    ext w
    simp only [baseDerivAlt_apply, AlternatingMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [show ScBanach.whitneyMk (E := E) (c • η) 0 = c • ScBanach.whitneyMk η 0 by
        simp [ScBanach.whitneyMk], map_smul, smul_eq_mul]

/-- **`dΩ(y, ·)` is the alternation of `(η, w) ↦ DΩ(y, w)(η, 0)`**, hence alternating
`(k+1)`-linear on `E₁`. -/
theorem ambientD_whitneyMk (h : Fin (k + 1) → E 1) :
    ambientD U Ω (ScBanach.whitneyMk (E := E.shift) y h) =
      AlternatingMap.alternatizeUncurryFin (baseDerivLin hU hΩ hA hy) h := by
  rw [ambientD_apply, AlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ScBanach.whitneyVec_mk]
  simp [baseDerivLin, baseDerivAlt_apply]

end Alternating

/-! ### Sc-forms on an open subset of a partial quadrant and on a retract -/

/-- **An sc-differential `k`-form on `U`** (2021 Definition 4.4.1 for the M-polyfold `U`, open in
a partial quadrant `C ⊆ E`, whose tangent is `TU = U¹ ⊕ E`): an sc-smooth `Ω : U¹ ⊕ E^k → ℝ`
which on every fibre `E^k` over `z ∈ U₁` is alternating `k`-linear. -/
structure IsAmbientScForm (E : ScBanach) (U : Set (E 0)) (k : ℕ) (Ω : (E.whitney k) 0 → ℝ) :
    Prop where
  isScSmooth : IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet k U) Ω
  alternating : ∀ z ∈ E.lvlSet U 1, ∃ a : E 0 [⋀^Fin k]→ₗ[ℝ] ℝ, ∀ v : Fin k → E 0,
    Ω (ScBanach.whitneyMk z v) = a v

lemma fiberPow_toBase_fiberPackL (w : Fin k → E 1) :
    (E.fiberPow k).toBase 1 (E.fiberPackL 1 k w) = E.fiberPackL 0 k fun i => E.toBase 1 (w i) :=
  ScBanach.fiberVecL_injective (funext fun i => by
    rw [ScBanach.fiberVecL_toBase, ScBanach.fiberVecL_fiberPackL, ScBanach.fiberVecL_fiberPackL])

lemma IsAmbientScForm.alternating_one {Ω : (E.whitney k) 0 → ℝ} (hΩ : IsAmbientScForm E U k Ω) :
    ∀ z ∈ E.lvlSet U 1, ∃ A : E 1 [⋀^Fin k]→ₗ[ℝ] ℝ, ∀ w : Fin k → E 1,
      Ω (z, (E.fiberPow k).toBase 1 (E.fiberPackL 1 k w)) = A w := fun z hz => by
  obtain ⟨a, ha⟩ := hΩ.alternating z hz
  exact ⟨a.compLinearMap (E.toBase 1 : E 1 →ₗ[ℝ] E 0), fun w => by
    rw [fiberPow_toBase_fiberPackL]; exact ha _⟩

/-- **The exterior derivative of an sc-form on `U` is an sc-form on `U¹`**
(2021 p. 197, `d : Ωᵏ(Xⁱ) → Ωᵏ⁺¹(Xⁱ⁺¹)`, for `X = U` open in a partial quadrant): `dΩ` is
sc-smooth on `⊕_{k+1} T(U¹)` and alternating `(k+1)`-linear on the fibres. -/
theorem IsAmbientScForm.ambientD (hU : IsRelOpenInQuadrant E C U) {Ω : (E.whitney k) 0 → ℝ}
    (hΩ : IsAmbientScForm E U k Ω) :
    IsAmbientScForm E.shift (E.lvlSet U 1) (k + 1) (ambientD U Ω) where
  isScSmooth := IsScSmooth.ambientD hU hΩ.isScSmooth
  alternating _ hy := ⟨AlternatingMap.alternatizeUncurryFin
      (baseDerivLin hU (hΩ.isScSmooth 1).1 hΩ.alternating_one hy),
    fun h => ambientD_whitneyMk hU (hΩ.isScSmooth 1).1 hΩ.alternating_one hy h⟩

/-- **The local exterior derivative on a retract** `(O, C, E)` with retraction `r`:
`d_r ω = d(ω ∘ ⊕ₖ Tr)`, the exterior derivative of the extension of `ω` to `⊕ₖ TU`. -/
def retractD (R : ScRetraction E C) (ω : (E.whitney k) 0 → ℝ) :
    (E.shift.whitney (k + 1)) 0 → ℝ :=
  ambientD R.U (ω ∘ R.whitney k)

/-- The extension `ω ∘ ⊕ₖ Tr` of an sc-form on the retract `O` is an sc-form on `U`. -/
theorem IsRetractScForm.isAmbientScForm_comp (R : ScRetraction E C) {ω : (E.whitney k) 0 → ℝ}
    (hω : IsRetractScForm E C R.retract k ω) : IsAmbientScForm E R.U k (ω ∘ R.whitney k) where
  isScSmooth := hω.isScSmooth.comp_isScSmooth (R.whitney k) (R.whitney_retract k)
  alternating z hz := by
    have hx : levelMap R 1 z ∈ E.lvlSet R.retract 1 :=
      R.isSc1.isSc0.levelMap_mapsTo R.mapsTo_retract 1 hz
    obtain ⟨a, ha⟩ := hω.alternating _ hx
    refine ⟨a.compLinearMap (scDeriv R.U R z : E 0 →ₗ[ℝ] E 0), fun v => ?_⟩
    rw [Function.comp_apply, R.whitney_apply, whitneyMap_eq_mk, ScBanach.whitneyVec_mk]
    refine ha _ fun i => ?_
    show ((levelMap R 1 z, scDeriv R.U R z (v i)) : E.tangent 0) ∈ retractTangent E C R.retract
    rw [retractTangent_eq]
    exact R.mem_tangent_iff_exists.2 ⟨z, hz, v i, rfl⟩

/-- **The local exterior derivative maps sc-forms on `O` to sc-forms on `O¹`**
(2021 p. 197, `d : Ωᵏ(Xⁱ) → Ωᵏ⁺¹(Xⁱ⁺¹)`, in a local model; `retractD`).  The independence of the
retraction `r` is not shown. -/
theorem IsRetractScForm.retractD (R : ScRetraction E C) {ω : (E.whitney k) 0 → ℝ}
    (hω : IsRetractScForm E C R.retract k ω) :
    IsRetractScForm E.shift (E.lvlSet C 1) (E.lvlSet R.retract 1) (k + 1) (Polyfold.retractD R ω) where
  isScSmooth := by
    have hd := (hω.isAmbientScForm_comp R).ambientD R.relOpen
    refine ⟨mapsTo_univ _ _, fun R' hR' => ?_⟩
    refine hd.isScSmooth.comp R'.isScDomain (R.relOpen.shift.whitneySet (k + 1)).isScDomain
      R'.isScSmooth fun q hq => ?_
    have hq' := hR' ▸ R'.apply_mem_retract hq
    exact ⟨R.retract_subset hq'.1, mem_univ _⟩
  alternating x hx := by
    have hd := (hω.isAmbientScForm_comp R).ambientD R.relOpen
    obtain ⟨a, ha⟩ := hd.alternating x (R.retract_subset hx)
    exact ⟨a, fun v _ => ha v⟩

end Polyfold
