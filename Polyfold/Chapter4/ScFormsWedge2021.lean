import Polyfold.Chapter4.ScFormsPullback2021
import Polyfold.Chapter3.ParamPerturbation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4, p. 198:
"The pair `(Ω*_∞(X), d)` is a graded differential algebra".

# The wedge product of sc-differential forms

The text does not define the wedge product; it uses it through the phrase "graded differential
algebra" (p. 198, and for `Ω*_∞(X, ∂X)` on p. 199).  We take the classical one: for alternating
maps `a` of degree `k` and `b` of degree `l`,
`(a ∧ b)(v) = (k! l!)⁻¹ Σ_{σ ∈ S_{k+l}} sign σ · a(v_{σ(1)}, …, v_{σ(k)}) · b(v_{σ(k+1)}, …)`.

## What is formalized

* **Algebra** (`wedgeFun`, `deltaFun`): the formula above for arbitrary functions of `k` and `l`
  vectors, and `δA(v₀, …, v_n) = Σⱼ (−1)ʲ A(vⱼ)(v₀, …, v̂ⱼ, …, v_n)`.  The two Leibniz identities
  `δ(A ∧ b) = δA ∧ b` (`deltaFun_wedgeFun_left`) and `δ(a ∧ B) = (−1)ᵏ a ∧ δB`
  (`deltaFun_wedgeFun_right`) hold for arbitrary functions: they are identities between sums
  over permutations.  `altWedge a b` is the wedge of alternating maps, with `coe_altWedge`,
  bilinearity and naturality `altWedge_compLinearMap`.
* **Forms on an M-polyfold**: `MPolyfold.formWedge ω τ`, pointwise `ω(x) ∧ τ(x)`.
  `chartForm_formWedge`: its local representative is the local wedge `lwedge ω_φ τ_φ` on
  `⊕_{k+l} TO`; `formWedge_mem_scForms`: `Ωᵏ(X) ∧ Ωˡ(X) ⊆ Ωᵏ⁺ˡ(X)`.
  `formPullback_formWedge`: `f^*(ω ∧ τ) = f^*ω ∧ f^*τ`; `formLower_formWedge`.
* **The Leibniz rule** `extD_formWedge`: `d(ω ∧ τ) = dω ∧ ι^*τ + (−1)ᵏ ι^*ω ∧ dτ` in
  `Ωᵏ⁺ˡ⁺¹(X¹)` (`ι : X¹ → X`, `formCast` for the degree `(k+1)+l = (k+l)+1`).  Locally it is
  `ambientD_lwedge`: the derivative of the local wedge along the base is computed by the product
  rule and the two algebraic identities.
* **On `Ω*_∞(X)`** (the text's "graded differential algebra"): `formsWedge` on `Ωᵏ(Xⁱ)`,
  compatible with the maps of (4.4) (`formsWedge_formsMap`); the induced bilinear
  `formsInftyWedge : Ωᵏ_∞(X) × Ωˡ_∞(X) → Ωᵏ⁺ˡ_∞(X)`, `[ω] ∧ [τ] = [ω ∧ τ]`
  (`formsInftyWedge_of_of`); the Leibniz rule `formsInftyD_formsInftyWedge`; naturality
  `formsInftyPullback_formsInftyWedge`.

## Not formalized

Associativity, the unit and graded commutativity of `∧` (so `Ω*_∞(X)` is not yet stated to be a
graded algebra), and the wedge on `Ω*_∞(X, ∂X)`.
-/

open Set Function

noncomputable section

namespace Polyfold

/-! ### The algebra of the wedge product -/

section Algebra

variable {M M' : Type*}

/-- The normalising constant `(k! l!)⁻¹` of the wedge product. -/
def wedgeCoeff (k l : ℕ) : ℝ := ((k.factorial : ℝ) * l.factorial)⁻¹

/-- **The wedge formula**, for `k + l = N` and arbitrary functions `a`, `b` of `k`, `l` vectors:
`(k! l!)⁻¹ Σ_{σ ∈ S_N} sign σ · a(v ∘ σ ∘ ι₁) · b(v ∘ σ ∘ ι₂)`, with `ι₁ : Fin k → Fin N` and
`ι₂ : Fin l → Fin N` the first and the last block. -/
def wedgeFunAux {k l N : ℕ} (h : k + l = N) (a : (Fin k → M) → ℝ) (b : (Fin l → M) → ℝ)
    (v : Fin N → M) : ℝ :=
  wedgeCoeff k l * ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    (a (fun i => v (σ (Fin.cast h (Fin.castAdd l i)))) *
      b (fun j => v (σ (Fin.cast h (Fin.natAdd k j)))))

/-- **The wedge formula** in degree `k + l`. -/
abbrev wedgeFun {k l : ℕ} (a : (Fin k → M) → ℝ) (b : (Fin l → M) → ℝ) (v : Fin (k + l) → M) : ℝ :=
  wedgeFunAux rfl a b v

/-- Changing the degree `k + l` to an equal `N`. -/
lemma wedgeFun_cast {k l N : ℕ} (h : k + l = N) (a : (Fin k → M) → ℝ) (b : (Fin l → M) → ℝ)
    (v : Fin N → M) : wedgeFun a b (fun i => v (Fin.cast h i)) = wedgeFunAux h a b v := by
  subst h; rfl

/-- `δA(v₀, …, v_n) = Σⱼ (−1)ʲ A(vⱼ)(v₀, …, v̂ⱼ, …, v_n)` (Mathlib's `alternatizeUncurryFin`
formula, for arbitrary functions). -/
def deltaFun {n : ℕ} (A : M → (Fin n → M) → ℝ) (v : Fin (n + 1) → M) : ℝ :=
  ∑ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) * A (v j) (j.removeNth v)

lemma deltaFun_add {n : ℕ} (A B : M → (Fin n → M) → ℝ) (v : Fin (n + 1) → M) :
    deltaFun (fun η w => A η w + B η w) v = deltaFun A v + deltaFun B v := by
  simp only [deltaFun, mul_add, Finset.sum_add_distrib]

/-- **Congruence**: the wedge formula only evaluates `a` and `b` at `v ∘ e`. -/
lemma wedgeFunAux_congr {k l N : ℕ} (h : k + l = N) {a : (Fin k → M) → ℝ}
    {b : (Fin l → M) → ℝ} {a' : (Fin k → M') → ℝ} {b' : (Fin l → M') → ℝ} {v : Fin N → M}
    {v' : Fin N → M'} (ha : ∀ e : Fin k → Fin N, a (v ∘ e) = a' (v' ∘ e))
    (hb : ∀ e : Fin l → Fin N, b (v ∘ e) = b' (v' ∘ e)) :
    wedgeFunAux h a b v = wedgeFunAux h a' b' v' := by
  unfold wedgeFunAux
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [show (fun i => v (σ (Fin.cast h (Fin.castAdd l i)))) =
    v ∘ fun i => σ (Fin.cast h (Fin.castAdd l i)) from rfl, ha,
    show (fun j => v (σ (Fin.cast h (Fin.natAdd k j)))) =
    v ∘ fun j => σ (Fin.cast h (Fin.natAdd k j)) from rfl, hb]
  rfl

/-- The value of `cycleRange`. -/
lemma wedge_val_cycleRange {n : ℕ} (i j : Fin n) :
    ((Fin.cycleRange i j : Fin n) : ℕ) =
      if (j : ℕ) < i then (j : ℕ) + 1 else if (j : ℕ) = i then (0 : ℕ) else (j : ℕ) := by
  rcases lt_trichotomy (j : ℕ) i with h | h | h
  · rw [Fin.coe_cycleRange_of_lt (Fin.lt_def.2 h), if_pos h]
  · rw [Fin.coe_cycleRange_of_le (Fin.le_def.2 h.le), if_pos (Fin.ext h), if_neg (by omega),
      if_pos h]
  · rw [Fin.cycleRange_of_gt (Fin.lt_def.2 h), if_neg (by omega), if_neg (by omega)]

/-- The permutation of `Fin (n + 1)` sending `0` to `i` and `m + 1` to `succAbove i (σ m)`. -/
def wedgeInsertPerm {n : ℕ} (p : Fin (n + 1) × Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (Fin.cycleRange p.1).symm * Equiv.Perm.decomposeFin.symm (0, p.2)

lemma wedgeInsertPerm_zero {n : ℕ} (p : Fin (n + 1) × Equiv.Perm (Fin n)) :
    wedgeInsertPerm p 0 = p.1 := by
  simp [wedgeInsertPerm]

lemma wedgeInsertPerm_succ {n : ℕ} (p : Fin (n + 1) × Equiv.Perm (Fin n)) (m : Fin n) :
    wedgeInsertPerm p m.succ = p.1.succAbove (p.2 m) := by
  simp [wedgeInsertPerm]

lemma sign_wedgeInsertPerm {n : ℕ} (p : Fin (n + 1) × Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign (wedgeInsertPerm p) : ℤ) : ℝ) =
      (-1 : ℝ) ^ (p.1 : ℕ) * ((Equiv.Perm.sign p.2 : ℤ) : ℝ) := by
  simp [wedgeInsertPerm, Fin.sign_cycleRange]

lemma wedgeInsertPerm_bijective {n : ℕ} : Bijective (wedgeInsertPerm (n := n)) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun p q hpq => ?_, ?_⟩
  · have h1 : p.1 = q.1 := by rw [← wedgeInsertPerm_zero p, ← wedgeInsertPerm_zero q, hpq]
    have h2 : Equiv.Perm.decomposeFin.symm ((0 : Fin (n + 1)), p.2) =
        Equiv.Perm.decomposeFin.symm (0, q.2) := by
      have := hpq
      simp only [wedgeInsertPerm, h1] at this
      exact mul_left_cancel this
    have h3 := Equiv.Perm.decomposeFin.symm.injective h2
    exact Prod.ext h1 (by simpa using h3)
  · simp [Fintype.card_perm, Nat.factorial_succ]

/-- **Decomposing a permutation of `Fin (n + 1)` by the image of `0`**:
`Σ_τ sign τ · F(v(τ 0), v ∘ τ ∘ succ) = Σᵢ (−1)ⁱ Σ_σ sign σ · F(vᵢ, (v₀, …, v̂ᵢ, …, v_n) ∘ σ)`. -/
theorem wedge_sum_perm_succ_eq {n : ℕ} (F : M → (Fin n → M) → ℝ) (v : Fin (n + 1) → M) :
    ∑ τ : Equiv.Perm (Fin (n + 1)), ((Equiv.Perm.sign τ : ℤ) : ℝ) *
      F (v (τ 0)) (fun m => v (τ m.succ)) =
    ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) * ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * F (v i) (fun m => i.removeNth v (σ m)) := by
  rw [← (Equiv.ofBijective _ wedgeInsertPerm_bijective).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Equiv.ofBijective_apply, sign_wedgeInsertPerm, wedgeInsertPerm_zero,
    wedgeInsertPerm_succ,
    Fin.removeNth_apply]
  ring

lemma wedge_val_succAbove {n : ℕ} (j : Fin (n + 1)) (m : Fin n) :
    (j.succAbove m : ℕ) = if (m : ℕ) < j then (m : ℕ) else (m : ℕ) + 1 := by
  split_ifs with h
  · rw [Fin.succAbove_of_castSucc_lt j m (Fin.lt_def.2 (by simpa using h))]; simp
  · rw [Fin.succAbove_of_le_castSucc j m (Fin.le_def.2 (by simp; omega))]; simp

lemma wedge_removeNth_eq_fun {n : ℕ} {α : Type*} (j : Fin (n + 1)) (f : Fin (n + 1) → α) :
    j.removeNth f = fun m => f (j.succAbove m) := rfl

lemma wedge_neg_one_pow_mul_self (n : ℕ) : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by
  rw [← mul_pow]; norm_num

lemma wedgeCoeff_succ_left (k l : ℕ) : wedgeCoeff (k + 1) l * (k + 1 : ℕ) = wedgeCoeff k l := by
  unfold wedgeCoeff
  rw [Nat.factorial_succ]
  push_cast
  have h1 : (k.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (l.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma wedgeCoeff_succ_right (k l : ℕ) : wedgeCoeff k (l + 1) * (l + 1 : ℕ) = wedgeCoeff k l := by
  unfold wedgeCoeff
  rw [Nat.factorial_succ]
  push_cast
  have h1 : (k.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (l.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma wedge_sign_mul_cycleRange {n : ℕ} (τ : Equiv.Perm (Fin n)) (p : Fin n) :
    ((Equiv.Perm.sign (τ * Fin.cycleRange p) : ℤ) : ℝ) =
      ((Equiv.Perm.sign τ : ℤ) : ℝ) * (-1 : ℝ) ^ (p : ℕ) := by
  simp [Equiv.Perm.sign_mul, Fin.sign_cycleRange]

/-- The canonical arrangement: `0` is the distinguished slot, then the `k`, then the `l` slots. -/
def wedgeCanonSum {k l : ℕ} (F : M → (Fin k → M) → (Fin l → M) → ℝ) (v : Fin (k + l + 1) → M) : ℝ :=
  ∑ τ : Equiv.Perm (Fin (k + l + 1)), ((Equiv.Perm.sign τ : ℤ) : ℝ) *
    F (v (τ 0)) (fun m => v (τ (Fin.castAdd l m).succ)) (fun m => v (τ (Fin.natAdd k m).succ))

lemma wedgeCanonSum_eq {k l : ℕ} (F : M → (Fin k → M) → (Fin l → M) → ℝ) (v : Fin (k + l + 1) → M) :
    wedgeCanonSum F v = ∑ i : Fin (k + l + 1), (-1 : ℝ) ^ (i : ℕ) *
      ∑ σ : Equiv.Perm (Fin (k + l)), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        F (v i) (fun m => i.removeNth v (σ (Fin.castAdd l m)))
          (fun m => i.removeNth v (σ (Fin.natAdd k m))) :=
  wedge_sum_perm_succ_eq
    (fun x w => F x (fun m => w (Fin.castAdd l m)) (fun m => w (Fin.natAdd k m))) v

/-- **Leibniz, first factor**: `δ(η ↦ A(η) ∧ b) = δA ∧ b`, as functions of `k + l + 1` vectors
(the degree `(k + 1) + l` read as `(k + l) + 1` through `h`). -/
theorem deltaFun_wedgeFun_left {k l : ℕ} (h : k + 1 + l = k + l + 1) (A : M → (Fin k → M) → ℝ)
    (b : (Fin l → M) → ℝ) (v : Fin (k + l + 1) → M) :
    deltaFun (fun η w => wedgeFun (A η) b w) v = wedgeFunAux h (deltaFun A) b v := by
  have hj : ∀ j : Fin (k + 1), ∑ τ : Equiv.Perm (Fin (k + l + 1)),
      ((Equiv.Perm.sign τ : ℤ) : ℝ) * ((-1 : ℝ) ^ (j : ℕ) *
        A (v (τ (Fin.cast h (Fin.castAdd l j))))
          (j.removeNth fun i => v (τ (Fin.cast h (Fin.castAdd l i)))) *
        b (fun m => v (τ (Fin.cast h (Fin.natAdd (k + 1) m))))) =
      wedgeCanonSum (fun x w w' => A x w * b w') v := by
    intro j
    rw [← Equiv.sum_comp (Equiv.mulRight (Fin.cycleRange (Fin.cast h (Fin.castAdd l j))))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have e1 : ∀ m : Fin k, Fin.cycleRange (Fin.cast h (Fin.castAdd l j))
        (Fin.cast h (Fin.castAdd l (j.succAbove m))) = (Fin.castAdd l m).succ := fun m => by
      apply Fin.ext
      rw [wedge_val_cycleRange]
      simp only [Fin.val_cast, Fin.val_castAdd, wedge_val_succAbove, Fin.val_succ]
      split_ifs <;> omega
    have e2 : ∀ m : Fin l, Fin.cycleRange (Fin.cast h (Fin.castAdd l j))
        (Fin.cast h (Fin.natAdd (k + 1) m)) = (Fin.natAdd k m).succ := fun m => by
      apply Fin.ext
      rw [wedge_val_cycleRange]
      simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.val_succ]
      split_ifs <;> omega
    simp only [Equiv.coe_mulRight, wedge_sign_mul_cycleRange, Equiv.Perm.coe_mul, comp_apply,
      Fin.cycleRange_self, wedge_removeNth_eq_fun, e1, e2, Fin.val_cast, Fin.val_castAdd]
    have := wedge_neg_one_pow_mul_self (j : ℕ)
    linear_combination (((Equiv.Perm.sign τ : ℤ) : ℝ) * (A (v (τ 0)) fun m =>
      v (τ (Fin.castAdd l m).succ)) * b fun m => v (τ (Fin.natAdd k m).succ)) * this
  have hR : wedgeFunAux h (deltaFun A) b v = wedgeCoeff (k + 1) l *
      ∑ j : Fin (k + 1), ∑ τ : Equiv.Perm (Fin (k + l + 1)),
      ((Equiv.Perm.sign τ : ℤ) : ℝ) * ((-1 : ℝ) ^ (j : ℕ) *
        A (v (τ (Fin.cast h (Fin.castAdd l j))))
          (j.removeNth fun i => v (τ (Fin.cast h (Fin.castAdd l i)))) *
        b (fun m => v (τ (Fin.cast h (Fin.natAdd (k + 1) m))))) := by
    unfold wedgeFunAux deltaFun
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
  rw [hR, Finset.sum_congr rfl fun j _ => hj j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, wedgeCoeff_succ_left, wedgeCanonSum_eq,
    Finset.mul_sum]
  unfold deltaFun wedgeFun wedgeFunAux
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.cast_eq_self, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

/-- **Leibniz, second factor**: `δ(η ↦ a ∧ B(η)) = (−1)ᵏ a ∧ δB`, as functions of `k + l + 1`
vectors (`k + (l + 1) = (k + l) + 1` by definition). -/
theorem deltaFun_wedgeFun_right {k l : ℕ} (a : (Fin k → M) → ℝ) (B : M → (Fin l → M) → ℝ)
    (v : Fin (k + l + 1) → M) :
    deltaFun (fun η w => wedgeFun a (B η) w) v = (-1 : ℝ) ^ k * wedgeFun a (deltaFun B) v := by
  have hj : ∀ j : Fin (l + 1), ∑ τ : Equiv.Perm (Fin (k + l + 1)),
      ((Equiv.Perm.sign τ : ℤ) : ℝ) * ((-1 : ℝ) ^ k * ((-1 : ℝ) ^ (j : ℕ) *
        (a (fun i => v (τ (Fin.castAdd (l + 1) i))) *
          B (v (τ (Fin.natAdd k j))) (j.removeNth fun i => v (τ (Fin.natAdd k i)))))) =
      wedgeCanonSum (fun x w w' => a w * B x w') v := by
    intro j
    rw [← Equiv.sum_comp (Equiv.mulRight (Fin.cycleRange (n := k + l + 1) (Fin.natAdd k j)))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have e1 : ∀ m : Fin k, Fin.cycleRange (n := k + l + 1) (Fin.natAdd k j)
        (Fin.castAdd (l + 1) m : Fin (k + l + 1)) = (Fin.castAdd l m).succ := fun m => by
      apply Fin.ext
      rw [wedge_val_cycleRange]
      simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_succ]
      split_ifs <;> omega
    have e2 : ∀ m : Fin l, Fin.cycleRange (n := k + l + 1) (Fin.natAdd k j)
        (Fin.natAdd k (j.succAbove m) : Fin (k + l + 1)) = (Fin.natAdd k m).succ := fun m => by
      apply Fin.ext
      rw [wedge_val_cycleRange]
      simp only [Fin.val_natAdd, wedge_val_succAbove, Fin.val_succ]
      split_ifs <;> omega
    simp only [Equiv.coe_mulRight, wedge_sign_mul_cycleRange, Equiv.Perm.coe_mul, comp_apply,
      Fin.cycleRange_self, wedge_removeNth_eq_fun, e1, e2, Fin.val_natAdd]
    have h1 := wedge_neg_one_pow_mul_self (j : ℕ)
    have h2 := wedge_neg_one_pow_mul_self k
    rw [pow_add]
    linear_combination (((Equiv.Perm.sign τ : ℤ) : ℝ) * (a fun m => v (τ (Fin.castAdd l m).succ)) *
      (B (v (τ 0)) fun m => v (τ (Fin.natAdd k m).succ))) *
      ((-1 : ℝ) ^ k * (-1) ^ k * h1 + h2)
  have hR : (-1 : ℝ) ^ k * wedgeFun a (deltaFun B) v = wedgeCoeff k (l + 1) *
      ∑ j : Fin (l + 1), ∑ τ : Equiv.Perm (Fin (k + l + 1)),
      ((Equiv.Perm.sign τ : ℤ) : ℝ) * ((-1 : ℝ) ^ k * ((-1 : ℝ) ^ (j : ℕ) *
        (a (fun i => v (τ (Fin.castAdd (l + 1) i))) *
          B (v (τ (Fin.natAdd k j))) (j.removeNth fun i => v (τ (Fin.natAdd k i)))))) := by
    unfold wedgeFun wedgeFunAux deltaFun
    simp only [Fin.cast_eq_self]
    rw [Finset.sum_comm, ← mul_assoc, mul_comm ((-1 : ℝ) ^ k), mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hR, Finset.sum_congr rfl fun j _ => hj j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, wedgeCoeff_succ_right, wedgeCanonSum_eq,
    Finset.mul_sum]
  unfold deltaFun wedgeFun wedgeFunAux
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.cast_eq_self, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring


end Algebra

/-! ### The wedge product of alternating maps -/

section Alternating

variable [AddCommGroup M] [Module ℝ M] [AddCommGroup M'] [Module ℝ M'] {k l : ℕ}

/-- The multilinear map `v ↦ a(v₁, …, v_k) · b(v_{k+1}, …, v_{k+l})`. -/
def wedgeML (a : M [⋀^Fin k]→ₗ[ℝ] ℝ) (b : M [⋀^Fin l]→ₗ[ℝ] ℝ) :
    MultilinearMap ℝ (fun _ : Fin (k + l) => M) ℝ :=
  ((LinearMap.mul' ℝ ℝ).compMultilinearMap
    (a.toMultilinearMap.domCoprod b.toMultilinearMap)).domDomCongr finSumFinEquiv

lemma wedgeML_apply (a : M [⋀^Fin k]→ₗ[ℝ] ℝ) (b : M [⋀^Fin l]→ₗ[ℝ] ℝ) (v : Fin (k + l) → M) :
    wedgeML a b v = a (fun i => v (Fin.castAdd l i)) * b (fun j => v (Fin.natAdd k j)) := by
  simp [wedgeML]

/-- **The wedge product `a ∧ b` of alternating forms** of degrees `k` and `l` (the product of the
graded algebra of p. 198): `(k! l!)⁻¹ Σ_σ sign σ · a(v ∘ σ ∘ ι₁) · b(v ∘ σ ∘ ι₂)`
(`coe_altWedge`). -/
def altWedge (a : M [⋀^Fin k]→ₗ[ℝ] ℝ) (b : M [⋀^Fin l]→ₗ[ℝ] ℝ) : M [⋀^Fin (k + l)]→ₗ[ℝ] ℝ :=
  wedgeCoeff k l • MultilinearMap.alternatization (wedgeML a b)

theorem coe_altWedge (a : M [⋀^Fin k]→ₗ[ℝ] ℝ) (b : M [⋀^Fin l]→ₗ[ℝ] ℝ) :
    ⇑(altWedge a b) = wedgeFun a b := by
  funext v
  simp only [altWedge, AlternatingMap.smul_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply, wedgeML_apply, smul_eq_mul, wedgeFun, wedgeFunAux,
    Fin.cast_eq_self, Units.smul_def, zsmul_eq_mul]

lemma altWedge_apply (a : M [⋀^Fin k]→ₗ[ℝ] ℝ) (b : M [⋀^Fin l]→ₗ[ℝ] ℝ) (v : Fin (k + l) → M) :
    altWedge a b v = wedgeFun a b v := by rw [coe_altWedge]

/-- **Naturality**: `g^*(a ∧ b) = g^*a ∧ g^*b` for a linear map `g`. -/
theorem altWedge_compLinearMap (a : M [⋀^Fin k]→ₗ[ℝ] ℝ) (b : M [⋀^Fin l]→ₗ[ℝ] ℝ)
    (g : M' →ₗ[ℝ] M) :
    (altWedge a b).compLinearMap g = altWedge (a.compLinearMap g) (b.compLinearMap g) := by
  ext v
  simp only [AlternatingMap.compLinearMap_apply, altWedge_apply]
  exact wedgeFunAux_congr rfl (fun e => rfl) (fun e => rfl)

theorem altWedge_add_left (a a' : M [⋀^Fin k]→ₗ[ℝ] ℝ) (b : M [⋀^Fin l]→ₗ[ℝ] ℝ) :
    altWedge (a + a') b = altWedge a b + altWedge a' b := by
  ext v
  simp only [AlternatingMap.add_apply, altWedge_apply, wedgeFun, wedgeFunAux, ← mul_add,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem altWedge_add_right (a : M [⋀^Fin k]→ₗ[ℝ] ℝ) (b b' : M [⋀^Fin l]→ₗ[ℝ] ℝ) :
    altWedge a (b + b') = altWedge a b + altWedge a b' := by
  ext v
  simp only [AlternatingMap.add_apply, altWedge_apply, wedgeFun, wedgeFunAux, ← mul_add,
    ← Finset.sum_add_distrib]

theorem altWedge_smul_left (c : ℝ) (a : M [⋀^Fin k]→ₗ[ℝ] ℝ) (b : M [⋀^Fin l]→ₗ[ℝ] ℝ) :
    altWedge (c • a) b = c • altWedge a b := by
  ext v
  simp only [AlternatingMap.smul_apply, altWedge_apply, wedgeFun, wedgeFunAux, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem altWedge_smul_right (c : ℝ) (a : M [⋀^Fin k]→ₗ[ℝ] ℝ) (b : M [⋀^Fin l]→ₗ[ℝ] ℝ) :
    altWedge a (c • b) = c • altWedge a b := by
  ext v
  simp only [AlternatingMap.smul_apply, altWedge_apply, wedgeFun, wedgeFunAux, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

/-- The wedge product as a bilinear map. -/
def altWedgeₗ : (M [⋀^Fin k]→ₗ[ℝ] ℝ) →ₗ[ℝ] (M [⋀^Fin l]→ₗ[ℝ] ℝ) →ₗ[ℝ]
    (M [⋀^Fin (k + l)]→ₗ[ℝ] ℝ) :=
  LinearMap.mk₂ ℝ altWedge altWedge_add_left altWedge_smul_left altWedge_add_right
    altWedge_smul_right

end Alternating


/-! ### The local wedge product on the Whitney sums -/

namespace ScBanach

variable {E : ScBanach}

variable (E) in
/-- **Selecting vectors**: `(y, h₁, …, h_N) ↦ (y, h_{e(1)}, …, h_{e(k)})`, an sc-operator
`⊕_N TE → ⊕_k TE` for any `e : Fin k → Fin N`. -/
def whitneySel {N k : ℕ} (e : Fin k → Fin N) : ScOperator (E.whitney N) (E.whitney k) where
  lvl m := (ContinuousLinearMap.id ℝ (E (m + 1))).prodMap ((E.fiberPackL m k).comp
    ((ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (e i)).comp (E.fiberVecL m N)))
  incl_comm m q := by
    refine Prod.ext rfl (fiberVecL_injective (funext fun i => ?_))
    change E.fiberVecL m k ((E.fiberPow k).incl m (E.fiberPackL (m + 1) k
        (fun i => E.fiberVecL (m + 1) N q.2 (e i)))) i =
      E.fiberVecL m k
        (E.fiberPackL m k (fun i => E.fiberVecL m N ((E.fiberPow N).incl m q.2) (e i))) i
    rw [fiberVecL_incl, fiberVecL_fiberPackL, fiberVecL_fiberPackL, fiberVecL_incl]

lemma whitneySel_zero {N k : ℕ} (e : Fin k → Fin N) (q : (E.whitney N) 0) :
    E.whitneySel e 0 q = whitneyMk q.1 (fun i => whitneyVec q (e i)) := rfl

lemma whitneySel_one {N k : ℕ} (e : Fin k → Fin N) (y : E.shift 1) (w : Fin N → E 1) :
    E.whitneySel e 1 ((y, E.fiberPackL 1 N w) : (E.whitney N) 1) =
      ((y, E.fiberPackL 1 k (fun i => w (e i))) : (E.whitney k) 1) := by
  refine Prod.ext rfl ?_
  change E.fiberPackL 1 k (fun i => E.fiberVecL 1 N (E.fiberPackL 1 N w) (e i)) = _
  rw [fiberVecL_fiberPackL]

lemma whitneySel_mk_zero {N k : ℕ} (e : Fin k → Fin N) (η : E 1) :
    E.whitneySel e 0 (whitneyMk η 0) = whitneyMk η 0 := by
  rw [whitneySel_zero, whitneyVec_mk]; rfl

end ScBanach

variable {E : ScBanach} {C U O : Set (E 0)} {k l : ℕ}

lemma mapsTo_whitneySel {N : ℕ} (e : Fin k → Fin N) :
    MapsTo (E.whitneySel e 0) (E.whitneySet N U) (E.whitneySet k U) := fun _ hq =>
  ScBanach.mem_whitneySet.2 (ScBanach.mem_whitneySet.1 hq)

lemma mapsTo_whitneySel_retract {N : ℕ} (e : Fin k → Fin N) :
    MapsTo (E.whitneySel e 0) (retractWhitney E C O N) (retractWhitney E C O k) := fun q hq => by
  rw [ScBanach.whitneySel_zero]
  exact mem_retractWhitney_mk.2 ⟨hq.1, fun i => hq.2 (e i)⟩

/-- The first block `i ↦ σ(i)` and the last block `j ↦ σ(k + j)` of a permutation. -/
abbrev wedgeSelL (σ : Equiv.Perm (Fin (k + l))) (i : Fin k) : Fin (k + l) := σ (Fin.castAdd l i)
abbrev wedgeSelR (σ : Equiv.Perm (Fin (k + l))) (j : Fin l) : Fin (k + l) := σ (Fin.natAdd k j)

/-- **The local wedge product** `Ω ∧ Θ : ⊕_{k+l} TE → ℝ` of maps `Ω : ⊕_k TE → ℝ`,
`Θ : ⊕_l TE → ℝ`, fibrewise the wedge formula. -/
def lwedge (Ω : (E.whitney k) 0 → ℝ) (Θ : (E.whitney l) 0 → ℝ) (q : (E.whitney (k + l)) 0) : ℝ :=
  wedgeFun (fun w => Ω (ScBanach.whitneyMk q.1 w)) (fun w => Θ (ScBanach.whitneyMk q.1 w))
    (ScBanach.whitneyVec q)

/-- The local wedge as a sum of products of `Ω` and `Θ` composed with sc-operators. -/
lemma lwedge_eq_sum (Ω : (E.whitney k) 0 → ℝ) (Θ : (E.whitney l) 0 → ℝ) :
    lwedge Ω Θ = fun q => wedgeCoeff k l * ∑ σ : Equiv.Perm (Fin (k + l)),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * (Ω (E.whitneySel (wedgeSelL σ) 0 q) *
        Θ (E.whitneySel (wedgeSelR σ) 0 q)) := by
  funext q
  simp only [lwedge, wedgeFun, wedgeFunAux, Fin.cast_eq_self]
  rfl

/-- Finite sums of products of real sc-smooth maps are sc-smooth. -/
theorem wedge_isScSmooth_sum_mul {G : ScBanach} {W : Set (G 0)} (hW : IsScDomain G W) {ι : Type}
    [Fintype ι] (c₀ : ℝ) (c : ι → ℝ) {f g : ι → G 0 → ℝ}
    (hf : ∀ i, IsScSmooth (F := ScBanach.const ℝ) W (f i))
    (hg : ∀ i, IsScSmooth (F := ScBanach.const ℝ) W (g i)) :
    IsScSmooth (F := ScBanach.const ℝ) W fun q => c₀ * ∑ i, c i * (f i q * g i q) := by
  have hterm : ∀ i ∈ (Finset.univ : Finset ι), IsScSmooth (F := ScBanach.const ℝ) W
      fun q => c i * (f i q * g i q) := fun i _ =>
    (isScSmooth_const_real hW (c i)).smul hW ((hf i).smul hW (hg i))
  have hs := IsScSmooth.finsetSum hW Finset.univ hterm
  exact fun n => (hs n).real_const_mul hW c₀

/-- **The local wedge is sc-smooth** on `⊕_{k+l} TU` for `Ω`, `Θ` sc-smooth on `⊕_k TU`,
`⊕_l TU`. -/
theorem IsScSmooth.lwedge (hU : IsRelOpenInQuadrant E C U) {Ω : (E.whitney k) 0 → ℝ}
    {Θ : (E.whitney l) 0 → ℝ} (hΩ : IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet k U) Ω)
    (hΘ : IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet l U) Θ) :
    IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet (k + l) U) (lwedge Ω Θ) := by
  have hD := (hU.whitneySet (k + l)).isScDomain
  rw [lwedge_eq_sum]
  exact wedge_isScSmooth_sum_mul hD _ _
    (fun σ => hΩ.comp hD (hU.whitneySet k).isScDomain ((E.whitneySel (wedgeSelL σ)).isScSmooth hD)
      (mapsTo_whitneySel _))
    (fun σ => hΘ.comp hD (hU.whitneySet l).isScDomain ((E.whitneySel (wedgeSelR σ)).isScSmooth hD)
      (mapsTo_whitneySel _))

/-- **The local wedge of sc-forms on a retract is sc-smooth** on `⊕_{k+l} TO`. -/
theorem IsScSmoothRetractMap.lwedge (hO : IsScRetract E C O) {Ω : (E.whitney k) 0 → ℝ}
    {Θ : (E.whitney l) 0 → ℝ}
    (hΩ : IsScSmoothRetractMap (E.whitney k) (E.whitneySet k C) (retractWhitney E C O k)
      (ScBanach.const ℝ) univ univ Ω)
    (hΘ : IsScSmoothRetractMap (E.whitney l) (E.whitneySet l C) (retractWhitney E C O l)
      (ScBanach.const ℝ) univ univ Θ) :
    IsScSmoothRetractMap (E.whitney (k + l)) (E.whitneySet (k + l) C)
      (retractWhitney E C O (k + l)) (ScBanach.const ℝ) univ univ (lwedge Ω Θ) := by
  have hL : ∀ σ : Equiv.Perm (Fin (k + l)), IsScSmoothRetractMap (E.whitney (k + l))
      (E.whitneySet (k + l) C) (retractWhitney E C O (k + l)) (ScBanach.const ℝ) univ univ
      (Ω ∘ E.whitneySel (wedgeSelL σ) 0) := fun σ =>
    hΩ.comp ((E.whitneySel (wedgeSelL σ)).isScSmoothRetractMap (hO.whitney (k + l))
      (mapsTo_whitneySel_retract _)) (hO.whitney k)
  have hR : ∀ σ : Equiv.Perm (Fin (k + l)), IsScSmoothRetractMap (E.whitney (k + l))
      (E.whitneySet (k + l) C) (retractWhitney E C O (k + l)) (ScBanach.const ℝ) univ univ
      (Θ ∘ E.whitneySel (wedgeSelR σ) 0) := fun σ =>
    hΘ.comp ((E.whitneySel (wedgeSelR σ)).isScSmoothRetractMap (hO.whitney (k + l))
      (mapsTo_whitneySel_retract _)) (hO.whitney l)
  refine ⟨mapsTo_univ _ _, fun R hR' => ?_⟩
  rw [lwedge_eq_sum]
  exact wedge_isScSmooth_sum_mul R.isScDomain _ _ (fun σ => (hL σ).comp_isScSmooth R hR')
    (fun σ => (hR σ).comp_isScSmooth R hR')

/-! ### The Leibniz rule for the local wedge -/

section Leibniz

/-- `⊕ₖ T(E¹) → ⊕ₖ TE` on a point `(y, w)`. -/
lemma whitneyIncl_whitneyMk (y : E.shift 1) (w : Fin k → E 1) :
    E.whitneyIncl k 0 (ScBanach.whitneyMk (E := E.shift) y w) =
      ScBanach.whitneyMk (E.shift.toBase 1 y) fun i => E.toBase 1 (w i) := by
  rw [← whitneyMk_fst_vec (E.whitneyIncl k 0 _), ScBanach.whitneyIncl_fst]
  congr 1
  funext i
  rw [ScBanach.whitneyVec_whitneyIncl, ScBanach.whitneyVec_mk]

lemma mem_lvl_whitneySel {N : ℕ} (e : Fin k → Fin N) {p : (E.whitney N) 1}
    (hp : p ∈ (E.whitney N).lvlSet (E.whitneySet N U) 1) :
    E.whitneySel e 1 p ∈ (E.whitney k).lvlSet (E.whitneySet k U) 1 := by
  rw [mem_whitneySet_lvl_one] at hp ⊢; exact hp

/-- The derivative of `Ω ∘ (selection)` on level `1`. -/
lemma hasFDerivWithinAt_comp_whitneySel {N : ℕ} (e : Fin k → Fin N) {Ω : (E.whitney k) 0 → ℝ}
    (hΩ : IsSc1 (F := ScBanach.const ℝ) (E.whitneySet k U) Ω) {p : (E.whitney N) 1}
    (hp : p ∈ (E.whitney N).lvlSet (E.whitneySet N U) 1) :
    HasFDerivWithinAt (fun x => Ω (E.whitneySel e 0 ((E.whitney N).toBase 1 x)))
      (((scDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) Ω (E.whitneySel e 1 p)).comp
        (E.whitneySel e 0)).comp ((E.whitney N).toBase 1))
      ((E.whitney N).lvlSet (E.whitneySet N U) 1) p := by
  have h1 := hΩ.isSc1With_scDeriv.hasFDerivWithinAt _ (mem_lvl_whitneySel e hp)
  have h2 : HasFDerivWithinAt (E.whitneySel e 1) (E.whitneySel e 1)
      ((E.whitney N).lvlSet (E.whitneySet N U) 1) p :=
    (E.whitneySel e 1).hasFDerivAt.hasFDerivWithinAt
  have h3 := h1.comp p h2 fun x hx => mem_lvl_whitneySel e hx
  have heq : (fun x => Ω (E.whitneySel e 0 ((E.whitney N).toBase 1 x))) =
      (Ω ∘ (E.whitney k).toBase 1) ∘ E.whitneySel e 1 := funext fun x => by
    simp only [Function.comp_apply, (E.whitneySel e).toBase_comm 1 x]
  rw [heq]
  refine h3.congr_fderiv (ContinuousLinearMap.ext fun x => ?_)
  simp only [ContinuousLinearMap.comp_apply, (E.whitneySel e).toBase_comm 1 x]

/-- `dΩ` on `(y, w)` is `δ` of `A(η)(w') = DΩ(y, w')(η, 0)`. -/
lemma ambientD_whitneyMk_eq_deltaFun {Ω : (E.whitney k) 0 → ℝ} (y : E.shift 1)
    (w : Fin (k + 1) → E 1) :
    ambientD U Ω (ScBanach.whitneyMk (E := E.shift) y w) =
      deltaFun (fun η w' => scDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) Ω
        ((y, E.fiberPackL 1 k w') : (E.whitney k) 1) (ScBanach.whitneyMk η 0)) w := by
  rw [ambientD_apply, deltaFun, ScBanach.whitneyVec_mk]

variable (hU : IsRelOpenInQuadrant E C U) {Ω : (E.whitney k) 0 → ℝ} {Θ : (E.whitney l) 0 → ℝ}
  (hΩ : IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet k U) Ω)
  (hΘ : IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet l U) Θ)

include hU hΩ hΘ

/-- **The product rule for the local wedge**: the chosen derivative of `Ω ∧ Θ` at a point of
level `1`. -/
theorem scDeriv_lwedge {p : (E.whitney (k + l)) 1}
    (hp : p ∈ (E.whitney (k + l)).lvlSet (E.whitneySet (k + l) U) 1) :
    scDeriv (F := ScBanach.const ℝ) (E.whitneySet (k + l) U) (lwedge Ω Θ) p =
      wedgeCoeff k l • ∑ σ : Equiv.Perm (Fin (k + l)), ((Equiv.Perm.sign σ : ℤ) : ℝ) •
        (Ω (E.whitneySel (wedgeSelL σ) 0 ((E.whitney (k + l)).toBase 1 p)) •
          (scDeriv (F := ScBanach.const ℝ) (E.whitneySet l U) Θ
            (E.whitneySel (wedgeSelR σ) 1 p)).comp
            (E.whitneySel (wedgeSelR σ) 0) +
        Θ (E.whitneySel (wedgeSelR σ) 0 ((E.whitney (k + l)).toBase 1 p)) •
          (scDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) Ω
            (E.whitneySel (wedgeSelL σ) 1 p)).comp
            (E.whitneySel (wedgeSelL σ) 0)) := by
  have hD := (hU.whitneySet (k + l)).isScDomain
  refine ((IsScSmooth.lwedge hU hΩ hΘ) 1).1.scDeriv_eq_of_hasFDerivWithinAt hp
    (hD.uniqueDiffWithinAt 1 p hp) ?_
  have hterm : ∀ σ : Equiv.Perm (Fin (k + l)), HasFDerivWithinAt
      (fun x => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        (Ω (E.whitneySel (wedgeSelL σ) 0 ((E.whitney (k + l)).toBase 1 x)) *
          Θ (E.whitneySel (wedgeSelR σ) 0 ((E.whitney (k + l)).toBase 1 x))))
      (((Equiv.Perm.sign σ : ℤ) : ℝ) •
        (Ω (E.whitneySel (wedgeSelL σ) 0 ((E.whitney (k + l)).toBase 1 p)) •
          (((scDeriv (F := ScBanach.const ℝ) (E.whitneySet l U) Θ
            (E.whitneySel (wedgeSelR σ) 1 p)).comp (E.whitneySel (wedgeSelR σ) 0)).comp
              ((E.whitney (k + l)).toBase 1)) +
        Θ (E.whitneySel (wedgeSelR σ) 0 ((E.whitney (k + l)).toBase 1 p)) •
          (((scDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) Ω
            (E.whitneySel (wedgeSelL σ) 1 p)).comp (E.whitneySel (wedgeSelL σ) 0)).comp
              ((E.whitney (k + l)).toBase 1))))
      ((E.whitney (k + l)).lvlSet (E.whitneySet (k + l) U) 1) p := fun σ =>
    ((hasFDerivWithinAt_comp_whitneySel (wedgeSelL σ) (hΩ 1).1 hp).mul
      (hasFDerivWithinAt_comp_whitneySel (wedgeSelR σ) (hΘ 1).1 hp)).const_mul _
  have hsum := (HasFDerivWithinAt.fun_sum (u := Finset.univ) fun σ _ => hterm σ).const_mul
    (wedgeCoeff k l)
  rw [lwedge_eq_sum]
  refine hsum.congr_fderiv (ContinuousLinearMap.ext fun x => ?_)
  simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply, add_apply,
    ContinuousLinearMap.comp_apply]

/-- **The product rule, evaluated**: the derivative of `Ω ∧ Θ` along the base, at
`(y, w₁, …, w_{k+l})` in the direction `(η, 0)`, is `A(η) ∧ b + a ∧ B(η)` with
`A(η)(w') = DΩ(y, w')(η, 0)`, `B(η)(w') = DΘ(y, w')(η, 0)` and `a`, `b` the values one level
down. -/
theorem scDeriv_lwedge_apply {y : E.shift 1} (hy : E.shift.toBase 1 y ∈ E.lvlSet U 1)
    (w : Fin (k + l) → E 1) (η : E 1) :
    scDeriv (F := ScBanach.const ℝ) (E.whitneySet (k + l) U) (lwedge Ω Θ)
        ((y, E.fiberPackL 1 (k + l) w) : (E.whitney (k + l)) 1) (ScBanach.whitneyMk η 0) =
      wedgeFun (fun w' => scDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) Ω
          ((y, E.fiberPackL 1 k w') : (E.whitney k) 1) (ScBanach.whitneyMk η 0))
        (fun w' => Θ (E.whitneyIncl l 0 (ScBanach.whitneyMk (E := E.shift) y w'))) w +
      wedgeFun (fun w' => Ω (E.whitneyIncl k 0 (ScBanach.whitneyMk (E := E.shift) y w')))
        (fun w' => scDeriv (F := ScBanach.const ℝ) (E.whitneySet l U) Θ
          ((y, E.fiberPackL 1 l w') : (E.whitney l) 1) (ScBanach.whitneyMk η 0)) w := by
  have hp : ((y, E.fiberPackL 1 (k + l) w) : (E.whitney (k + l)) 1) ∈
      (E.whitney (k + l)).lvlSet (E.whitneySet (k + l) U) 1 := mem_whitneySet_lvl_one.2 hy
  rw [scDeriv_lwedge hU hΩ hΘ hp, wedgeFun, wedgeFun, wedgeFunAux, wedgeFunAux, ← mul_add,
    ← Finset.sum_add_distrib, _root_.smul_apply, _root_.sum_apply,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [_root_.smul_apply, _root_.add_apply,
    _root_.smul_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ScBanach.whitneySel_mk_zero, ScBanach.whitneySel_mk_zero, ScBanach.whitneySel_one,
    ScBanach.whitneySel_one, whitney_toBase_mk, ScBanach.whitneySel_zero,
    ScBanach.whitneySel_zero, ScBanach.whitneyVec_mk, whitneyIncl_whitneyMk,
    whitneyIncl_whitneyMk]
  simp only [smul_eq_mul, Fin.cast_eq_self]
  ring

/-- **The Leibniz rule for the local exterior derivative** (2021 p. 198, "graded differential
algebra", in a local model): on `⊕_{k+l+1} T(U¹)`,
`d(Ω ∧ Θ) = dΩ ∧ ι^*Θ + (−1)ᵏ ι^*Ω ∧ dΘ`, written on the vectors `h` of `q = (y, h)`; `ι^*` is the
inclusion `⊕ T(U¹) → ⊕ TU`, and `h : (k + 1) + l = (k + l) + 1` reads the degree of `dΩ ∧ ι^*Θ`. -/
theorem ambientD_lwedge (h : k + 1 + l = k + l + 1) {q : (E.shift.whitney (k + l + 1)) 0}
    (hq : q ∈ E.shift.whitneySet (k + l + 1) (E.lvlSet U 1)) :
    ambientD U (lwedge Ω Θ) q =
      wedgeFunAux h (fun w => ambientD U Ω (ScBanach.whitneyMk (E := E.shift) q.1 w))
          (fun w => Θ (E.whitneyIncl l 0 (ScBanach.whitneyMk (E := E.shift) q.1 w)))
          (ScBanach.whitneyVec q) +
        (-1 : ℝ) ^ k * wedgeFun
          (fun w => Ω (E.whitneyIncl k 0 (ScBanach.whitneyMk (E := E.shift) q.1 w)))
          (fun w => ambientD U Θ (ScBanach.whitneyMk (E := E.shift) q.1 w))
          (ScBanach.whitneyVec q) := by
  have hy : E.shift.toBase 1 q.1 ∈ E.lvlSet U 1 := ScBanach.mem_whitneySet.1 hq
  have key : ambientD U (lwedge Ω Θ) q = deltaFun (fun η w =>
      wedgeFun (fun w' => scDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) Ω
          ((q.1, E.fiberPackL 1 k w') : (E.whitney k) 1) (ScBanach.whitneyMk η 0))
        (fun w' => Θ (E.whitneyIncl l 0 (ScBanach.whitneyMk (E := E.shift) q.1 w'))) w +
      wedgeFun (fun w' => Ω (E.whitneyIncl k 0 (ScBanach.whitneyMk (E := E.shift) q.1 w')))
        (fun w' => scDeriv (F := ScBanach.const ℝ) (E.whitneySet l U) Θ
          ((q.1, E.fiberPackL 1 l w') : (E.whitney l) 1) (ScBanach.whitneyMk η 0)) w)
      (ScBanach.whitneyVec q) := by
    rw [ambientD_apply, deltaFun]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [scDeriv_lwedge_apply hU hΩ hΘ hy]
  rw [key, deltaFun_add, deltaFun_wedgeFun_left h, deltaFun_wedgeFun_right]
  congr 1
  · congr 1; funext w; rw [ambientD_whitneyMk_eq_deltaFun]
  · congr 2; funext w; rw [ambientD_whitneyMk_eq_deltaFun]

end Leibniz

/-- `lwedge` commutes with `⊕ Tg`: `(Ω ∧ Θ) ∘ ⊕_{k+l} Tg = (Ω ∘ ⊕_k Tg) ∧ (Θ ∘ ⊕_l Tg)`. -/
lemma lwedge_whitneyMap {F : ScBanach} (V : Set (F 0)) (g : F 0 → E 0)
    (Ω : (E.whitney k) 0 → ℝ) (Θ : (E.whitney l) 0 → ℝ) (p : (F.whitney (k + l)) 0) :
    lwedge Ω Θ (whitneyMap V g (k + l) p) =
      lwedge (Ω ∘ whitneyMap V g k) (Θ ∘ whitneyMap V g l) p := by
  unfold lwedge
  refine wedgeFunAux_congr rfl (fun e => ?_) (fun e => ?_) <;>
  · simp only [Function.comp_apply, whitneyMap_fst, whitneyMap_eq_mk V g _
      (ScBanach.whitneyMk p.1 _), ScBanach.whitneyVec_mk]
    congr 2
    funext i
    simp only [Function.comp_apply, whitneyVec_whitneyMap]

/-! ### The wedge product of sc-forms on an M-polyfold -/

namespace MPolyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {φ : MChart X} {k l : ℕ}

/-- **The wedge product of families of forms**, pointwise `(ω ∧ τ)(x) = ω(x) ∧ τ(x)` on the
tangent spaces `T_xX`, `x ∈ X¹` (the product of the graded algebra `Ω*(X)`, 2021 p. 198). -/
def formWedge (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin l]→ₗ[ℝ] ℝ) :
    ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin (k + l)]→ₗ[ℝ] ℝ := fun x => altWedge (ω x) (τ x)

lemma formWedge_apply (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin l]→ₗ[ℝ] ℝ) (x : P.Level 1)
    (α : Fin (k + l) → P.tangentFiber x) : formWedge ω τ x α = wedgeFun (ω x) (τ x) α :=
  altWedge_apply _ _ _

/-- Reading a family of `k`-forms as `k'`-forms for `k = k'` (`Fin k ≃ Fin k'`). -/
def formCast {k' : ℕ} (h : k = k') (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k']→ₗ[ℝ] ℝ := fun x =>
  (ω x).domDomCongr (finCongr h)

lemma formCast_apply {k' : ℕ} (h : k = k') (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (x : P.Level 1) (α : Fin k' → P.tangentFiber x) :
    formCast h ω x α = ω x fun i => α (Fin.cast h i) := rfl

@[simp] lemma formCast_rfl (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    formCast rfl ω = ω := rfl

/-- **The local representative of `ω ∧ τ`** is the local wedge of the representatives, on
`⊕_{k+l} TO`. -/
theorem chartForm_formWedge (hφ : P.IsChart φ)
    (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin l]→ₗ[ℝ] ℝ) :
    EqOn (chartForm hφ (formWedge ω τ)) (lwedge (chartForm hφ ω) (chartForm hφ τ))
      (retractWhitney φ.model.E φ.model.C φ.model.O (k + l)) := by
  intro q hq
  rw [chartForm, dif_pos hq, formWedge_apply]
  have hx := chartPoint_mem_source hφ hq.1
  have hlift := levelLift_chartPoint hφ hq.1
  unfold lwedge
  refine wedgeFunAux_congr rfl (fun e => ?_) (fun e => ?_) <;>
  · refine (chartForm_eq hφ _ hx _ (q := ScBanach.whitneyMk q.1 (ScBanach.whitneyVec q ∘ e))
      hlift.symm fun i => ?_).symm
    rw [ScBanach.whitneyVec_mk]
    exact (congrArg Prod.snd (tangentChartMap_mk_ofVec hφ (hq.2 (e i)))).symm

/-- **The wedge product of sc-forms is an sc-form**: `Ωᵏ(X) ∧ Ωˡ(X) ⊆ Ωᵏ⁺ˡ(X)`. -/
theorem formWedge_mem_scForms {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    {τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin l]→ₗ[ℝ] ℝ} (hω : ω ∈ P.scForms k)
    (hτ : τ ∈ P.scForms l) : formWedge ω τ ∈ P.scForms (k + l) := fun φ hφ =>
  (IsScSmoothRetractMap.lwedge φ.model.isScRetract (hω hφ) (hτ hφ)).congr fun _ hq =>
    (chartForm_formWedge hφ ω τ hq).symm

/-- **Naturality of the wedge product**: `f^*(ω ∧ τ) = f^*ω ∧ f^*τ` (2021 p. 198). -/
theorem formPullback_formWedge {f : X → Y} (hf : P.IsScSmoothMap Q f)
    (ω : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ)
    (τ : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin l]→ₗ[ℝ] ℝ) :
    formPullback hf (formWedge ω τ) = formWedge (formPullback hf ω) (formPullback hf τ) :=
  funext fun _ => altWedge_compLinearMap _ _ _

/-- The wedge product commutes with the maps `Ω(Xⁱ) → Ω(Xⁱ⁺¹)` of (4.4). -/
theorem formLower_formWedge (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin l]→ₗ[ℝ] ℝ) :
    formLower (formWedge ω τ) = formWedge (formLower ω) (formLower τ) :=
  funext fun _ => altWedge_compLinearMap _ _ _

/-! ### The Leibniz rule on an M-polyfold -/

section LeibnizGlobal

variable {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
  {τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin l]→ₗ[ℝ] ℝ}

/-- The value of `ι^*τ` at `x ∈ X²` in a chart: `(ι^*τ)(x)(α) = τ_φ(ι(φ¹(x), Tφ¹α))`, and
`τ_φ = τ_φ ∘ ⊕ Tr` there. -/
lemma formLower_eq_chartForm (hφ : P.IsChart φ) (y₀ : P.Level 1) {x : P.shift.Level 1}
    (hx : P.shift.levelVal 1 x ∈ (levelChart hφ y₀).source) {n : ℕ}
    (σ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin n]→ₗ[ℝ] ℝ) (β : Fin n → P.shift.tangentFiber x) :
    formLower σ x β = (chartForm hφ σ ∘ (chartRetraction φ).whitney n)
      (φ.model.E.whitneyIncl n 0 (ScBanach.whitneyMk (E := φ.model.E.shift)
        (levelLift (levelChart hφ y₀) 1 (P.shift.levelVal 1 x))
        fun i => (tangentChartMap (P.shift_isChart hφ y₀) (β i)).2)) := by
  have hχ := P.shift_isChart hφ y₀
  have hmem := whitneyMk_tangentChartMap_mem hφ y₀ hx β
  have hR := chartRetraction_retract φ
  have hinc := mapsTo_whitneyIncl φ.model.isScRetract n hmem
  rw [Function.comp_apply, (chartRetraction φ).whitney_apply,
    (chartRetraction φ).whitneyMap_eq_self (hR ▸ hinc), ← chartForm_formLower hφ σ y₀ hmem]
  refine (chartForm_eq hχ _ hx β rfl fun i => ?_).symm
  exact congrFun (ScBanach.whitneyVec_mk (E := φ.model.E.shift) _ _) i

/-- **2021 p. 198: the Leibniz rule** ("`(Ω*_∞(X), d)` is a graded differential algebra"): for
`ω ∈ Ωᵏ(X)` and `τ ∈ Ωˡ(X)`, `d(ω ∧ τ) = dω ∧ ι^*τ + (−1)ᵏ ι^*ω ∧ dτ` in `Ωᵏ⁺ˡ⁺¹(X¹)`, where
`ι^* = formLower` is the pull-back along `X¹ → X` (the text's identification in the direct
limit) and `formCast h` reads the degree `(k + 1) + l` as `(k + l) + 1`.  The proof is the local
`ambientD_lwedge` in the charts `⊕ Tφ¹`. -/
theorem extD_formWedge (h : k + 1 + l = k + l + 1) (hω : ω ∈ P.scForms k) (hτ : τ ∈ P.scForms l) :
    extD (formWedge ω τ) = formCast h (formWedge (extD ω) (formLower τ)) +
      (-1 : ℝ) ^ k • formWedge (formLower ω) (extD τ) := by
  funext x
  ext α
  have hφ : P.IsChart (dChart x) := dChart_isChart x
  have hx := mem_dLevelChart_source x
  set y₀ := P.shift.levelVal 1 x
  set φ := dChart x
  have hχ := P.shift_isChart hφ y₀
  have hq := whitneyMk_tangentChartMap_mem hφ y₀ hx α
  set R := chartRetraction φ
  have hRr : R.retract = φ.model.O := chartRetraction_retract φ
  have hωR : IsRetractScForm φ.model.E φ.model.C R.retract k (chartForm hφ ω) := by
    rw [hRr]; exact (mem_scForms.1 hω).isRetractScForm hφ
  have hτR : IsRetractScForm φ.model.E φ.model.C R.retract l (chartForm hφ τ) := by
    rw [hRr]; exact (mem_scForms.1 hτ).isRetractScForm hφ
  have hΩ := (hωR.isAmbientScForm_comp R).isScSmooth
  have hΘ := (hτR.isAmbientScForm_comp R).isScSmooth
  have hqU := R.mem_whitneySet_of_mem (by rw [hRr]; exact hq)
  have step1 : chartD hφ (formWedge ω τ) (ScBanach.whitneyMk (E := φ.model.E.shift)
      (levelLift (levelChart hφ y₀) 1 (P.shift.levelVal 1 x))
      fun i => (tangentChartMap hχ (α i)).2) =
      ambientD R.U (lwedge (chartForm hφ ω ∘ R.whitney k) (chartForm hφ τ ∘ R.whitney l))
        (ScBanach.whitneyMk (E := φ.model.E.shift)
          (levelLift (levelChart hφ y₀) 1 (P.shift.levelVal 1 x))
          fun i => (tangentChartMap hχ (α i)).2) := by
    refine ambientD_congr (R.relOpen.whitneySet (k + l)).isScDomain
      ((IsScSmooth.lwedge R.relOpen hΩ hΘ) 1).1 (fun p hp => ?_) hqU
    have hp' := R.whitney_mem hp
    rw [hRr] at hp'
    rw [Function.comp_apply, chartForm_formWedge hφ ω τ hp', R.whitney_apply, lwedge_whitneyMap]
    rfl
  rw [extD_apply hφ (formWedge_mem_scForms hω hτ) y₀ hx α, step1,
    ambientD_lwedge R.relOpen hΩ hΘ h hqU, Pi.add_apply, AlternatingMap.add_apply,
    Pi.smul_apply, AlternatingMap.smul_apply, formCast_apply, formWedge_apply, formWedge_apply,
    wedgeFun_cast, smul_eq_mul]
  have hv : ScBanach.whitneyVec (E := φ.model.E.shift) (ScBanach.whitneyMk (E := φ.model.E.shift)
      (levelLift (levelChart hφ y₀) 1 (P.shift.levelVal 1 x))
      fun i => (tangentChartMap hχ (α i)).2) = fun i => (tangentChartMap hχ (α i)).2 :=
    ScBanach.whitneyVec_mk (E := φ.model.E.shift) _ _
  rw [hv]
  congr 1
  · refine wedgeFunAux_congr h (fun e => ?_) (fun e => ?_)
    · exact (extD_apply hφ hω y₀ hx (α ∘ e)).symm
    · exact (formLower_eq_chartForm hφ y₀ hx τ (α ∘ e)).symm
  · congr 1
    erw [hv]
    refine wedgeFunAux_congr rfl (fun e => ?_) (fun e => ?_)
    · exact (formLower_eq_chartForm hφ y₀ hx ω (α ∘ e)).symm
    · exact (extD_apply hφ hτ y₀ hx (α ∘ e)).symm

end LeibnizGlobal

end MPolyfold

/-! ### The wedge product on `Ω*_∞(X)` -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {k : ℕ}

theorem formCast_mem_scForms {k' : ℕ} (h : k = k')
    {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} (hω : ω ∈ P.scForms k) :
    formCast h ω ∈ P.scForms k' := by
  subst h; exact hω

end MPolyfold

namespace BundledMPolyfold

open MPolyfold

universe u v

/-- `Ωᵏ_∞(X)` is an additive monoid (stated directly: the generic search times out). -/
@[reducible] def wedgeAddCommMonoidFormsInfty (A : BundledMPolyfold.{u}) (j : ℕ) :
    AddCommMonoid (A.formsInfty j) :=
  Module.DirectLimit.addCommMonoid _ _

/-- `Ωᵏ_∞(X)` is a real vector space (stated directly: the generic search times out). -/
@[reducible] def wedgeModuleFormsInfty (A : BundledMPolyfold.{u}) (j : ℕ) :
    Module ℝ (A.formsInfty j) :=
  Module.DirectLimit.module _ _



attribute [local instance high] wedgeAddCommMonoidFormsInfty wedgeModuleFormsInfty

variable (A : BundledMPolyfold.{u}) (k l : ℕ)

/-- The wedge product `Ωᵏ(Xⁱ) × Ωˡ(Xⁱ) → Ωᵏ⁺ˡ(Xⁱ)`, bilinear. -/
def formsWedge (i : ℕ) : A.forms k i →ₗ[ℝ] A.forms l i →ₗ[ℝ] A.forms (k + l) i :=
  LinearMap.mk₂ ℝ (fun ω τ => ⟨formWedge ω.1 τ.1, formWedge_mem_scForms ω.2 τ.2⟩)
    (fun _ _ _ => Subtype.ext (funext fun _ => altWedge_add_left _ _ _))
    (fun _ _ _ => Subtype.ext (funext fun _ => altWedge_smul_left _ _ _))
    (fun _ _ _ => Subtype.ext (funext fun _ => altWedge_add_right _ _ _))
    (fun _ _ _ => Subtype.ext (funext fun _ => altWedge_smul_right _ _ _))

lemma coe_formsWedge (i : ℕ) (ω : A.forms k i) (τ : A.forms l i) :
    (A.formsWedge k l i ω τ).1 = formWedge ω.1 τ.1 := rfl

variable {k l}

theorem formsWedge_formsStep (i : ℕ) (ω : A.forms k i) (τ : A.forms l i) :
    A.formsStep (k + l) i (A.formsWedge k l i ω τ) =
      A.formsWedge k l (i + 1) (A.formsStep k i ω) (A.formsStep l i τ) :=
  Subtype.ext (formLower_formWedge ω.1 τ.1)

theorem formsWedge_formsMap {i j : ℕ} (h : i ≤ j) (ω : A.forms k i) (τ : A.forms l i) :
    A.formsMap (k + l) i j h (A.formsWedge k l i ω τ) =
      A.formsWedge k l j (A.formsMap k i j h ω) (A.formsMap l i j h τ) := by
  induction j, h using Nat.le_induction with
  | base => simp only [formsMap_self, LinearMap.id_apply]
  | succ j hij ih =>
    rw [formsMap_succ A _ hij, LinearMap.comp_apply, ih, formsWedge_formsStep,
      formsMap_succ A k hij, formsMap_succ A l hij, LinearMap.comp_apply, LinearMap.comp_apply]

/-- The class of `ω ∧ τ` read at any common level `n ≥ i, j`. -/
def wedgeAt (i j n : ℕ) (hi : i ≤ n) (hj : j ≤ n) (ω : A.forms k i) (τ : A.forms l j) :
    A.formsInfty (k + l) :=
  A.formsInftyOf (k + l) n (A.formsWedge k l n (A.formsMap k i n hi ω) (A.formsMap l j n hj τ))

theorem wedgeAt_le {i j n n' : ℕ} (hi : i ≤ n) (hj : j ≤ n) (hn : n ≤ n') (ω : A.forms k i)
    (τ : A.forms l j) :
    A.wedgeAt i j n' (hi.trans hn) (hj.trans hn) ω τ = A.wedgeAt i j n hi hj ω τ := by
  have e1 : A.formsMap k i n' (hi.trans hn) ω = A.formsMap k n n' hn (A.formsMap k i n hi ω) :=
    (LinearMap.congr_fun (A.formsMap_comp k hi hn) ω).symm
  have e2 : A.formsMap l j n' (hj.trans hn) τ = A.formsMap l n n' hn (A.formsMap l j n hj τ) :=
    (LinearMap.congr_fun (A.formsMap_comp l hj hn) τ).symm
  unfold wedgeAt
  calc _ = A.formsInftyOf (k + l) n' (A.formsMap (k + l) n n' hn
        (A.formsWedge k l n (A.formsMap k i n hi ω) (A.formsMap l j n hj τ))) := by
          rw [A.formsWedge_formsMap hn, ← e1, ← e2]
    _ = _ := formsInftyOf_formsMap A (k + l) hn _

theorem wedgeAt_eq {i j n n' : ℕ} (hi : i ≤ n) (hj : j ≤ n) (hi' : i ≤ n') (hj' : j ≤ n')
    (ω : A.forms k i) (τ : A.forms l j) :
    A.wedgeAt i j n hi hj ω τ = A.wedgeAt i j n' hi' hj' ω τ :=
  (A.wedgeAt_le hi hj (le_max_left n n') ω τ).symm.trans
    (A.wedgeAt_le hi' hj' (le_max_right n n') ω τ)

variable (k l) in
/-- `(ω, τ) ↦ [ι^*ω ∧ ι^*τ]` on `Ωᵏ(Xⁱ) × Ωˡ(Xʲ)`, read on `X^{i+j}`; bilinear. -/
def wedgeAtₗ (i j : ℕ) : A.forms k i →ₗ[ℝ] A.forms l j →ₗ[ℝ] A.formsInfty (k + l) :=
  ((A.formsWedge k l (i + j)).compl₁₂ (A.formsMap k i (i + j) (Nat.le_add_right i j))
    (A.formsMap l j (i + j) (Nat.le_add_left j i))).compr₂ (A.formsInftyOf (k + l) (i + j))

theorem wedgeAtₗ_apply (i j : ℕ) (ω : A.forms k i) (τ : A.forms l j) :
    A.wedgeAtₗ k l i j ω τ =
      A.wedgeAt i j (i + j) (Nat.le_add_right i j) (Nat.le_add_left j i) ω τ :=
  rfl

theorem wedgeAtₗ_formsMap {i j j' : ℕ} (h : j ≤ j') (ω : A.forms k i) (τ : A.forms l j) :
    A.wedgeAtₗ k l i j' ω (A.formsMap l j j' h τ) = A.wedgeAtₗ k l i j ω τ := by
  rw [wedgeAtₗ_apply, wedgeAtₗ_apply]
  refine Eq.trans ?_ (A.wedgeAt_eq _ _ (Nat.le_add_right i j') (h.trans (Nat.le_add_left j' i))
    ω τ).symm
  unfold wedgeAt
  rw [← LinearMap.comp_apply (A.formsMap l j' (i + j') _), A.formsMap_comp l]

variable (k l) in
/-- `ω ↦ ([τ] ↦ [ω ∧ τ])` on `Ωᵏ(Xⁱ)`, with values in the linear maps on `Ωˡ_∞(X)`. -/
def formsInftyWedgeOf (i : ℕ) : A.forms k i →ₗ[ℝ] A.formsInfty l →ₗ[ℝ] A.formsInfty (k + l) :=
  (Module.DirectLimit.lift ℝ ℕ (fun j => ↥(A.forms l j)) (A.formsMap l)
    (fun j => (A.wedgeAtₗ k l i j).flip) fun _ _ h τ =>
      LinearMap.ext fun ω => A.wedgeAtₗ_formsMap h ω τ).flip

theorem formsInftyWedgeOf_of (i j : ℕ) (ω : A.forms k i) (τ : A.forms l j) :
    A.formsInftyWedgeOf k l i ω (A.formsInftyOf l j τ) =
      A.wedgeAt i j (i + j) (Nat.le_add_right i j) (Nat.le_add_left j i) ω τ := by
  rw [formsInftyWedgeOf, LinearMap.flip_apply, Module.DirectLimit.lift_of]
  exact A.wedgeAtₗ_apply i j ω τ

theorem formsInftyWedgeOf_formsMap {i i' : ℕ} (h : i ≤ i') (ω : A.forms k i) :
    A.formsInftyWedgeOf k l i' (A.formsMap k i i' h ω) = A.formsInftyWedgeOf k l i ω := by
  refine Module.DirectLimit.hom_ext fun j => LinearMap.ext fun τ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, formsInftyWedgeOf_of, formsInftyWedgeOf_of]
  refine Eq.trans ?_ (A.wedgeAt_eq (h.trans (Nat.le_add_right i' j)) (Nat.le_add_left j i') _ _
    ω τ)
  unfold wedgeAt
  rw [← LinearMap.comp_apply (A.formsMap k i' (i' + j) _), A.formsMap_comp k]

variable (k l) in
/-- **The wedge product on `Ω*_∞(X)`** (2021 p. 198, "graded differential algebra"):
`[ω] ∧ [τ] = [ω ∧ τ]` for representatives pulled back to a common level. -/
def formsInftyWedge : A.formsInfty k →ₗ[ℝ] A.formsInfty l →ₗ[ℝ] A.formsInfty (k + l) :=
  Module.DirectLimit.lift ℝ ℕ (fun i => ↥(A.forms k i)) (A.formsMap k)
    (A.formsInftyWedgeOf k l) fun _ _ h ω => A.formsInftyWedgeOf_formsMap h ω

theorem formsInftyWedge_of (i j : ℕ) (ω : A.forms k i) (τ : A.forms l j) :
    A.formsInftyWedge k l (A.formsInftyOf k i ω) (A.formsInftyOf l j τ) =
      A.wedgeAt i j (i + j) (Nat.le_add_right i j) (Nat.le_add_left j i) ω τ := by
  rw [formsInftyWedge, Module.DirectLimit.lift_of]
  exact A.formsInftyWedgeOf_of i j ω τ

/-- `[ω] ∧ [τ] = [ω ∧ τ]` for `ω`, `τ` on the same `Xⁱ`. -/
theorem formsInftyWedge_of_of (i : ℕ) (ω : A.forms k i) (τ : A.forms l i) :
    A.formsInftyWedge k l (A.formsInftyOf k i ω) (A.formsInftyOf l i τ) =
      A.formsInftyOf (k + l) i (A.formsWedge k l i ω τ) := by
  rw [formsInftyWedge_of, A.wedgeAt_eq _ _ (le_refl i) (le_refl i)]
  unfold wedgeAt
  rw [formsMap_self, formsMap_self, LinearMap.id_apply, LinearMap.id_apply]

/-! ### The Leibniz rule and naturality on `Ω*_∞(X)` -/

theorem formsInftyOf_formsStep (i : ℕ) (ω : A.forms k i) :
    A.formsInftyOf k (i + 1) (A.formsStep k i ω) = A.formsInftyOf k i ω := by
  have h := A.formsInftyOf_formsMap k (Nat.le_succ i) ω
  rwa [formsMap_succ A k le_rfl, formsMap_self, LinearMap.comp_id] at h

/-- Reading the degree `k` of `Ωᵏ(Xⁱ)` as `k' = k`. -/
def formsCast {k' : ℕ} (h : k = k') (i : ℕ) : A.forms k i →ₗ[ℝ] A.forms k' i :=
  h ▸ LinearMap.id

lemma coe_formsCast {k' : ℕ} (h : k = k') (i : ℕ) (ω : A.forms k i) :
    (A.formsCast h i ω).1 = formCast h ω.1 := by
  subst h; rfl

/-- Reading the degree `k` of `Ωᵏ_∞(X)` as `k' = k`. -/
def formsInftyCast {k' : ℕ} (h : k = k') : A.formsInfty k →ₗ[ℝ] A.formsInfty k' :=
  h ▸ LinearMap.id

lemma formsInftyCast_of {k' : ℕ} (h : k = k') (i : ℕ) (ω : A.forms k i) :
    A.formsInftyCast h (A.formsInftyOf k i ω) = A.formsInftyOf k' i (A.formsCast h i ω) := by
  subst h; rfl

/-- **The Leibniz rule on `Ωᵏ(Xⁱ)`**: `d(ω ∧ τ) = dω ∧ ι^*τ + (−1)ᵏ ι^*ω ∧ dτ`. -/
theorem formsD_formsWedge (h : k + 1 + l = k + l + 1) (i : ℕ) (ω : A.forms k i)
    (τ : A.forms l i) :
    A.formsD (k + l) i (A.formsWedge k l i ω τ) =
      A.formsCast h (i + 1) (A.formsWedge (k + 1) l (i + 1) (A.formsD k i ω) (A.formsStep l i τ)) +
        (-1 : ℝ) ^ k • A.formsWedge k (l + 1) (i + 1) (A.formsStep k i ω) (A.formsD l i τ) :=
  Subtype.ext (by
    rw [Submodule.coe_add, Submodule.coe_smul, coe_formsCast]
    exact extD_formWedge h ω.2 τ.2)

theorem formsInftyD_formsInftyWedge_of (h : k + 1 + l = k + l + 1) (n : ℕ) (ω : A.forms k n)
    (τ : A.forms l n) :
    A.formsInftyD (k + l) (A.formsInftyWedge k l (A.formsInftyOf k n ω) (A.formsInftyOf l n τ)) =
      A.formsInftyCast h (A.formsInftyWedge (k + 1) l (A.formsInftyD k (A.formsInftyOf k n ω))
        (A.formsInftyOf l n τ)) +
        (-1 : ℝ) ^ k • A.formsInftyWedge k (l + 1) (A.formsInftyOf k n ω)
          (A.formsInftyD l (A.formsInftyOf l n τ)) := by
  have e1 : A.formsInftyOf (k + (l + 1)) (n + 1) (A.formsWedge k (l + 1) (n + 1)
      (A.formsStep k n ω) (A.formsD l n τ)) = A.formsInftyWedge k (l + 1) (A.formsInftyOf k n ω)
        (A.formsInftyD l (A.formsInftyOf l n τ)) :=
    (A.formsInftyWedge_of_of (n + 1) (A.formsStep k n ω) (A.formsD l n τ)).symm.trans <| by
      rw [A.formsInftyOf_formsStep n ω, formsInftyD_of]
  have e2 : A.formsInftyOf (k + 1 + l) (n + 1) (A.formsWedge (k + 1) l (n + 1) (A.formsD k n ω)
      (A.formsStep l n τ)) = A.formsInftyWedge (k + 1) l (A.formsInftyD k (A.formsInftyOf k n ω))
        (A.formsInftyOf l n τ) :=
    (A.formsInftyWedge_of_of (n + 1) (A.formsD k n ω) (A.formsStep l n τ)).symm.trans <| by
      rw [A.formsInftyOf_formsStep n τ, formsInftyD_of]
  rewrite [formsInftyWedge_of_of, formsInftyD_of, formsD_formsWedge _ h]
  refine (LinearMap.map_add _ _ _).trans (congrArg₂ (· + ·) ?_ ?_)
  · exact (A.formsInftyCast_of h (n + 1) _).symm.trans (congrArg _ e2)
  · exact (LinearMap.map_smul _ _ _).trans (congrArg _ e1)

theorem formsInftyD_formsInftyWedge_aux (h : k + 1 + l = k + l + 1) (n : ℕ) (ω : A.forms k n)
    (τ : A.forms l n) {a : A.formsInfty k} {b : A.formsInfty l} (ha : a = A.formsInftyOf k n ω)
    (hb : b = A.formsInftyOf l n τ) :
    A.formsInftyD (k + l) (A.formsInftyWedge k l a b) =
      A.formsInftyCast h (A.formsInftyWedge (k + 1) l (A.formsInftyD k a) b) +
        (-1 : ℝ) ^ k • A.formsInftyWedge k (l + 1) a (A.formsInftyD l b) := by
  subst ha hb
  exact A.formsInftyD_formsInftyWedge_of h n ω τ

/-- **2021 p. 198: the Leibniz rule on `Ω*_∞(X)`**, `d(a ∧ b) = da ∧ b + (−1)ᵏ a ∧ db` for
`a ∈ Ωᵏ_∞(X)` (the degree `(k + 1) + l` of `da ∧ b` read as `(k + l) + 1` by `formsInftyCast`). -/
theorem formsInftyD_formsInftyWedge (h : k + 1 + l = k + l + 1) (a : A.formsInfty k)
    (b : A.formsInfty l) :
    A.formsInftyD (k + l) (A.formsInftyWedge k l a b) =
      A.formsInftyCast h (A.formsInftyWedge (k + 1) l (A.formsInftyD k a) b) +
        (-1 : ℝ) ^ k • A.formsInftyWedge k (l + 1) a (A.formsInftyD l b) := by
  induction a using Module.DirectLimit.induction_on with
  | ih i ω =>
  induction b using Module.DirectLimit.induction_on with
  | ih j τ =>
  exact A.formsInftyD_formsInftyWedge_aux h (i + j) _ _
    (A.formsInftyOf_formsMap k (Nat.le_add_right i j) ω).symm
    (A.formsInftyOf_formsMap l (Nat.le_add_left j i) τ).symm

/-- The pull-back commutes with the wedge product on `Ω(Yⁱ)`. -/
theorem formsPullback_formsWedge {B : BundledMPolyfold.{v}} (f : ScMap A.P B.P) (i : ℕ)
    (ω : B.forms k i) (τ : B.forms l i) :
    formsPullback f (k + l) i (B.formsWedge k l i ω τ) =
      A.formsWedge k l i (formsPullback f k i ω) (formsPullback f l i τ) :=
  Subtype.ext (formPullback_formWedge _ ω.1 τ.1)

theorem formsInftyPullback_formsInftyWedge_aux {B : BundledMPolyfold.{v}} (f : ScMap A.P B.P)
    (n : ℕ) (ω : B.forms k n) (τ : B.forms l n) {a : B.formsInfty k} {b : B.formsInfty l}
    (ha : a = B.formsInftyOf k n ω) (hb : b = B.formsInftyOf l n τ) :
    formsInftyPullback f (k + l) (B.formsInftyWedge k l a b) =
      A.formsInftyWedge k l (formsInftyPullback f k a) (formsInftyPullback f l b) := by
  subst ha hb
  refine (congrArg _ (B.formsInftyWedge_of_of n ω τ)).trans
    ((formsInftyPullback_of f (k + l) n _).trans
      ((congrArg _ (A.formsPullback_formsWedge f n ω τ)).trans
      ((A.formsInftyWedge_of_of n _ _).symm.trans ?_)))
  exact congrArg₂ (fun x y => A.formsInftyWedge k l x y) (formsInftyPullback_of f k n ω).symm
    (formsInftyPullback_of f l n τ).symm

/-- **2021 p. 198: `f^*(a ∧ b) = f^*a ∧ f^*b`** on `Ω*_∞(Y)` for an sc-smooth `f : X → Y`. -/
theorem formsInftyPullback_formsInftyWedge {B : BundledMPolyfold.{v}} (f : ScMap A.P B.P)
    (a : B.formsInfty k) (b : B.formsInfty l) :
    formsInftyPullback f (k + l) (B.formsInftyWedge k l a b) =
      A.formsInftyWedge k l (formsInftyPullback f k a) (formsInftyPullback f l b) := by
  induction a using Module.DirectLimit.induction_on with
  | ih i ω =>
  induction b using Module.DirectLimit.induction_on with
  | ih j τ =>
  exact A.formsInftyPullback_formsInftyWedge_aux f (i + j) _ _
    (B.formsInftyOf_formsMap k (Nat.le_add_right i j) ω).symm
    (B.formsInftyOf_formsMap l (Nat.le_add_left j i) τ).symm

end BundledMPolyfold

end Polyfold
