import Polyfold.Chapter4.ScFormsWedge2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4, p. 198:
"The pair `(Ω*_∞(X), d)` is a graded differential algebra".

# Associativity and graded commutativity of the wedge product

Continues `ScFormsWedge2021`, where the wedge product `∧` (classical `(k! l!)⁻¹` convention),
the Leibniz rule and naturality are proved.

## What is formalized

* **Algebra**: associativity `(a ∧ b) ∧ c = a ∧ (b ∧ c)` (`wedgeFun_assoc`) and graded
  commutativity `a ∧ b = (−1)^{kl} b ∧ a` (`wedgeFun_comm`) of the wedge formula, for arbitrary
  functions (sums over permutations, reindexed by block permutations and the rotation
  `finRotate^k` of sign `(−1)^{kl}`); for alternating maps `altWedge_assoc`, `altWedge_comm` and
  the unit `altWedge_altOne`, `altWedge_altOne_left`.
* **Forms**: `formWedge_assoc`, `formWedge_comm`, the `0`-form `formOne` (an sc-form,
  `formOne_mem_scForms`) with `formWedge_formOne`, `formCast_formWedge_formOne`.
* **`Ω*_∞(X)`**: `formsInftyWedge_assoc`, `formsInftyWedge_comm`, the unit `formsInftyOne`;
  `formsInftyGSemiring`, `formsInftyGAlgebra`: `Ω*_∞(X) = ⊕ₖ Ωᵏ_∞(X)` is a graded `ℝ`-algebra
  (Mathlib's `DirectSum.GAlgebra`, so `⊕ₖ Ωᵏ_∞(X)` is an `ℝ`-algebra); graded commutativity
  `formsInftyGraded_of_mul_of_comm`; `d` is a graded derivation of degree `+1`
  (`formsInftyGradedD_of_mul_of`), with `d² = 0` (`formsInftyGradedD_comp_self`): **the
  graded differential algebra of p. 198**.  `f^*` is a morphism of graded algebras
  (`formsInftyPullback_formsInftyWedge`, `formsInftyPullback_formsInftyOne`).

Degrees: `(k + l) + m` and `k + (l + m)` (also `k + l` and `l + k`, `0 + l` and `l`) are equal
but not definitionally; `formCast`, `formsInftyCast` (and `GradedMonoid.mk`, by
`gradedMonoid_mk_formsInftyCast`) mediate.
-/

open Set Function Equiv

noncomputable section

namespace Polyfold

section Algebra

variable {M : Type*}

/-- `ρ ∈ S_p` acting on the first block of `Fin (p + m)`. -/
def wedgeLiftLeft {p m : ℕ} (ρ : Perm (Fin p)) : Perm (Fin (p + m)) :=
  finSumFinEquiv.permCongr (ρ.sumCongr 1)

/-- `ρ ∈ S_m` acting on the last block of `Fin (p + m)`. -/
def wedgeLiftRight {p m : ℕ} (ρ : Perm (Fin m)) : Perm (Fin (p + m)) :=
  finSumFinEquiv.permCongr ((1 : Perm (Fin p)).sumCongr ρ)

@[simp] lemma wedgeLiftLeft_castAdd {p m : ℕ} (ρ : Perm (Fin p)) (i : Fin p) :
    wedgeLiftLeft (m := m) ρ (Fin.castAdd m i) = Fin.castAdd m (ρ i) := by
  simp [wedgeLiftLeft, permCongr_apply]

@[simp] lemma wedgeLiftLeft_natAdd {p m : ℕ} (ρ : Perm (Fin p)) (j : Fin m) :
    wedgeLiftLeft (m := m) ρ (Fin.natAdd p j) = Fin.natAdd p j := by
  simp [wedgeLiftLeft, permCongr_apply]

@[simp] lemma wedgeLiftRight_castAdd {p m : ℕ} (ρ : Perm (Fin m)) (i : Fin p) :
    wedgeLiftRight (p := p) ρ (Fin.castAdd m i) = Fin.castAdd m i := by
  simp [wedgeLiftRight, permCongr_apply]

@[simp] lemma wedgeLiftRight_natAdd {p m : ℕ} (ρ : Perm (Fin m)) (j : Fin m) :
    wedgeLiftRight (p := p) ρ (Fin.natAdd p j) = Fin.natAdd p (ρ j) := by
  simp [wedgeLiftRight, permCongr_apply]

lemma sign_wedgeLiftLeft {p m : ℕ} (ρ : Perm (Fin p)) :
    Perm.sign (wedgeLiftLeft (m := m) ρ) = Perm.sign ρ := by
  simp [wedgeLiftLeft, Perm.sign_permCongr, Perm.sign_sumCongr]

lemma sign_wedgeLiftRight {p m : ℕ} (ρ : Perm (Fin m)) :
    Perm.sign (wedgeLiftRight (p := p) ρ) = Perm.sign ρ := by
  simp [wedgeLiftRight, Perm.sign_permCongr, Perm.sign_sumCongr]

lemma wedge_sign_mul_cast {n : ℕ} (σ τ : Perm (Fin n)) :
    ((Perm.sign (σ * τ) : ℤ) : ℝ) = ((Perm.sign σ : ℤ) : ℝ) * ((Perm.sign τ : ℤ) : ℝ) := by
  rw [Perm.sign_mul, Units.val_mul, Int.cast_mul]

lemma wedge_sign_sq {n : ℕ} (ρ : Perm (Fin n)) :
    ((Perm.sign ρ : ℤ) : ℝ) * ((Perm.sign ρ : ℤ) : ℝ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

/-- **Collapsing an inner wedge sum on the first block**: summing `sign ρ · G(v ∘ σ ∘ ι₁ ∘ ρ)` over
`ρ ∈ S_p` inside the sum over `σ ∈ S_{p+m}` gives `p!` times the plain sum. -/
lemma wedge_sum_collapse_left {p m : ℕ} (G : (Fin p → M) → ℝ) (H : (Fin m → M) → ℝ)
    (v : Fin (p + m) → M) :
    ∑ σ : Perm (Fin (p + m)), ((Perm.sign σ : ℤ) : ℝ) *
      ((∑ ρ : Perm (Fin p), ((Perm.sign ρ : ℤ) : ℝ) * G (fun i => v (σ (Fin.castAdd m (ρ i))))) *
        H (fun j => v (σ (Fin.natAdd p j)))) =
      (p.factorial : ℝ) * ∑ σ : Perm (Fin (p + m)), ((Perm.sign σ : ℤ) : ℝ) *
        (G (fun i => v (σ (Fin.castAdd m i))) * H (fun j => v (σ (Fin.natAdd p j)))) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hc : ∀ ρ : Perm (Fin p), (∑ σ : Perm (Fin (p + m)), ((Perm.sign σ : ℤ) : ℝ) *
      (((Perm.sign ρ : ℤ) : ℝ) * G (fun i => v (σ (Fin.castAdd m (ρ i))))
        * H (fun j => v (σ (Fin.natAdd p j))))) =
      ∑ σ : Perm (Fin (p + m)), ((Perm.sign σ : ℤ) : ℝ) *
        (G (fun i => v (σ (Fin.castAdd m i))) * H (fun j => v (σ (Fin.natAdd p j)))) := by
    intro ρ
    refine Fintype.sum_equiv (Equiv.mulRight (wedgeLiftLeft (m := m) ρ)) _ _ fun σ => ?_
    simp only [Equiv.coe_mulRight, Perm.coe_mul, comp_apply, wedgeLiftLeft_castAdd,
      wedgeLiftLeft_natAdd, wedge_sign_mul_cast, sign_wedgeLiftLeft]
    ring
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Finset.mul_sum]

/-- **Collapsing an inner wedge sum on the last block.** -/
lemma wedge_sum_collapse_right {p m : ℕ} (G : (Fin p → M) → ℝ) (H : (Fin m → M) → ℝ)
    (v : Fin (p + m) → M) :
    ∑ σ : Perm (Fin (p + m)), ((Perm.sign σ : ℤ) : ℝ) *
      (G (fun i => v (σ (Fin.castAdd m i))) *
        ∑ ρ : Perm (Fin m), ((Perm.sign ρ : ℤ) : ℝ) * H (fun j => v (σ (Fin.natAdd p (ρ j))))) =
      (m.factorial : ℝ) * ∑ σ : Perm (Fin (p + m)), ((Perm.sign σ : ℤ) : ℝ) *
        (G (fun i => v (σ (Fin.castAdd m i))) * H (fun j => v (σ (Fin.natAdd p j)))) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hc : ∀ ρ : Perm (Fin m), (∑ σ : Perm (Fin (p + m)), ((Perm.sign σ : ℤ) : ℝ) *
      (G (fun i => v (σ (Fin.castAdd m i))) *
        (((Perm.sign ρ : ℤ) : ℝ) * H (fun j => v (σ (Fin.natAdd p (ρ j))))))) =
      ∑ σ : Perm (Fin (p + m)), ((Perm.sign σ : ℤ) : ℝ) *
        (G (fun i => v (σ (Fin.castAdd m i))) * H (fun j => v (σ (Fin.natAdd p j)))) := by
    intro ρ
    refine Fintype.sum_equiv (Equiv.mulRight (wedgeLiftRight (p := p) ρ)) _ _ fun σ => ?_
    simp only [Equiv.coe_mulRight, Perm.coe_mul, comp_apply, wedgeLiftRight_castAdd,
      wedgeLiftRight_natAdd, wedge_sign_mul_cast, sign_wedgeLiftRight]
    ring
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Finset.mul_sum]

lemma wedgeCoeff_assoc (k l m : ℕ) :
    wedgeCoeff (k + l) m * wedgeCoeff k l * ((k + l).factorial : ℝ) =
      wedgeCoeff k (l + m) * wedgeCoeff l m * ((l + m).factorial : ℝ) := by
  have h1 : ((k + l).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((l + m).factorial : ℝ) ≠ 0 := by positivity
  unfold wedgeCoeff
  field_simp

variable {k l m : ℕ}

/-- `(a ∧ b) ∧ c` as one sum over `S_{k+l+m}`. -/
lemma wedgeFun_wedgeFun_left (a : (Fin k → M) → ℝ) (b : (Fin l → M) → ℝ) (c : (Fin m → M) → ℝ)
    (v : Fin (k + l + m) → M) :
    wedgeFun (wedgeFun a b) c v =
      wedgeCoeff (k + l) m * wedgeCoeff k l * ((k + l).factorial : ℝ) *
        ∑ σ : Perm (Fin (k + l + m)), ((Perm.sign σ : ℤ) : ℝ) *
          ((a (fun i => v (σ (Fin.castAdd m (Fin.castAdd l i)))) *
            b (fun j => v (σ (Fin.castAdd m (Fin.natAdd k j))))) *
              c (fun r => v (σ (Fin.natAdd (k + l) r)))) := by
  have h := wedge_sum_collapse_left
    (fun u : Fin (k + l) → M => a (fun i => u (Fin.castAdd l i)) * b (fun j => u (Fin.natAdd k j)))
    c v
  simp only at h
  unfold wedgeFun wedgeFunAux
  simp only [Fin.cast_eq_self]
  rw [mul_assoc (wedgeCoeff _ _ * wedgeCoeff _ _), ← h, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

/-- `a ∧ (b ∧ c)` as one sum over `S_{k+(l+m)}`. -/
lemma wedgeFun_wedgeFun_right (a : (Fin k → M) → ℝ) (b : (Fin l → M) → ℝ) (c : (Fin m → M) → ℝ)
    (v : Fin (k + (l + m)) → M) :
    wedgeFun a (wedgeFun b c) v =
      wedgeCoeff k (l + m) * wedgeCoeff l m * ((l + m).factorial : ℝ) *
        ∑ σ : Perm (Fin (k + (l + m))), ((Perm.sign σ : ℤ) : ℝ) *
          (a (fun i => v (σ (Fin.castAdd (l + m) i))) *
            (b (fun j => v (σ (Fin.natAdd k (Fin.castAdd m j)))) *
              c (fun r => v (σ (Fin.natAdd k (Fin.natAdd l r)))))) := by
  have h := wedge_sum_collapse_right a
    (fun u : Fin (l + m) → M => b (fun j => u (Fin.castAdd m j)) * c (fun r => u (Fin.natAdd l r)))
    v
  simp only at h
  unfold wedgeFun wedgeFunAux
  simp only [Fin.cast_eq_self]
  rw [mul_assoc (wedgeCoeff _ _ * wedgeCoeff _ _), ← h, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

/-- **Associativity of the wedge formula**: `(a ∧ b) ∧ c = a ∧ (b ∧ c)`, the degree
`k + (l + m)` read as `(k + l) + m`.  It holds for arbitrary functions `a`, `b`, `c`. -/
theorem wedgeFun_assoc (a : (Fin k → M) → ℝ) (b : (Fin l → M) → ℝ) (c : (Fin m → M) → ℝ)
    (v : Fin (k + l + m) → M) :
    wedgeFun (wedgeFun a b) c v = wedgeFunAux (Nat.add_assoc k l m).symm a (wedgeFun b c) v := by
  set h := (Nat.add_assoc k l m).symm
  have p1 : ∀ i : Fin k, Fin.cast h (Fin.castAdd (l + m) i) = Fin.castAdd m (Fin.castAdd l i) :=
    fun i => Fin.ext rfl
  have p2 : ∀ j : Fin l, Fin.cast h (Fin.natAdd k (Fin.castAdd m j)) =
      Fin.castAdd m (Fin.natAdd k j) := fun j => Fin.ext rfl
  have p3 : ∀ r : Fin m, Fin.cast h (Fin.natAdd k (Fin.natAdd l r)) = Fin.natAdd (k + l) r :=
    fun r => Fin.ext (by simp [add_assoc])
  rw [← wedgeFun_cast h, wedgeFun_wedgeFun_left, wedgeFun_wedgeFun_right, wedgeCoeff_assoc]
  congr 1
  refine Fintype.sum_equiv (finCongr h).symm.permCongr _ _ fun σ => ?_
  simp only [Perm.sign_permCongr, permCongr_apply, finCongr_apply, finCongr_symm,
    Fin.cast_cast, Fin.cast_eq_self, p1, p2, p3]
  ring

lemma wedge_val_finRotate {n : ℕ} (y : Fin n) : ((finRotate n y : Fin n) : ℕ) = (y + 1) % n := by
  rcases n with _ | N
  · exact y.elim0
  rw [coe_finRotate]
  split_ifs with hy
  · subst hy; simp
  · have : (y : ℕ) + 1 < N + 1 := by
      have := Fin.val_lt_last hy
      omega
    rw [Nat.mod_eq_of_lt this]

lemma wedge_val_finRotate_pow {n : ℕ} (k : ℕ) (x : Fin n) :
    (((finRotate n ^ k) x : Fin n) : ℕ) = (x + k) % n := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt x.2]
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, wedge_val_finRotate, ih, Nat.add_mod (_ % n), Nat.mod_mod,
      ← Nat.add_mod, add_assoc]

lemma wedge_neg_one_pow_rotate (k l : ℕ) :
    (-1 : ℝ) ^ ((k + l - 1) * k) = (-1) ^ (k * l) := by
  rcases k with _ | k
  · simp
  · have h : (k + 1 + l - 1) * (k + 1) = (k + 1) * l + (k + 1) * (k + 1 - 1) := by
      rw [Nat.add_sub_cancel, show k + 1 + l - 1 = k + l by omega]; ring
    rw [h, pow_add, (Nat.even_mul_pred_self (k + 1)).neg_one_pow, mul_one]

lemma sign_finRotate_pow (k l : ℕ) :
    ((Perm.sign (finRotate (k + l) ^ k) : ℤ) : ℝ) = (-1) ^ (k * l) := by
  rw [map_pow, sign_finRotate, ← pow_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Int.cast_pow, Int.cast_neg, Int.cast_one, wedge_neg_one_pow_rotate]

/-- **Graded commutativity of the wedge formula**: `a ∧ b = (−1)^{kl} b ∧ a`, the degree `l + k`
read as `k + l`.  It holds for arbitrary functions `a`, `b`. -/
theorem wedgeFun_comm (a : (Fin k → M) → ℝ) (b : (Fin l → M) → ℝ) (v : Fin (k + l) → M) :
    wedgeFun a b v = (-1) ^ (k * l) * wedgeFunAux (Nat.add_comm l k) b a v := by
  set h := Nat.add_comm l k
  set r := finRotate (k + l) ^ k
  have p1 : ∀ j : Fin l, r (Fin.cast h (Fin.castAdd k j)) = Fin.natAdd k j := fun j => by
    ext
    rw [wedge_val_finRotate_pow, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
      Nat.mod_eq_of_lt (by omega), add_comm]
  have p2 : ∀ i : Fin k, r (Fin.cast h (Fin.natAdd l i)) = Fin.castAdd l i := fun i => by
    ext
    rw [wedge_val_finRotate_pow, Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd,
      show l + (i : ℕ) + k = i + (k + l) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hr : ((Perm.sign r : ℤ) : ℝ) = (-1) ^ (k * l) := sign_finRotate_pow k l
  unfold wedgeFun wedgeFunAux
  simp only [Fin.cast_eq_self]
  rw [show wedgeCoeff l k = wedgeCoeff k l by unfold wedgeCoeff; ring, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight r) _ _ fun σ => ?_
  simp only [Equiv.coe_mulRight, Perm.coe_mul, comp_apply, p1, p2, wedge_sign_mul_cast, hr]
  have : ((-1 : ℝ) ^ (k * l)) * (-1) ^ (k * l) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (-wedgeCoeff k l * ((Perm.sign σ : ℤ) : ℝ) *
    (b (fun j => v (σ (Fin.natAdd k j))) * a (fun i => v (σ (Fin.castAdd l i))))) * this

end Algebra

/-! ### Alternating maps -/

section Alternating

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {k l m : ℕ}

/-- **Associativity**: `(a ∧ b) ∧ c = a ∧ (b ∧ c)`, the degree `k + (l + m)` read as
`(k + l) + m`. -/
theorem altWedge_assoc (a : M [⋀^Fin k]→ₗ[ℝ] ℝ) (b : M [⋀^Fin l]→ₗ[ℝ] ℝ)
    (c : M [⋀^Fin m]→ₗ[ℝ] ℝ) :
    altWedge (altWedge a b) c =
      (altWedge a (altWedge b c)).domDomCongr (finCongr (Nat.add_assoc k l m).symm) := by
  ext v
  rw [AlternatingMap.domDomCongr_apply, altWedge_apply, altWedge_apply, coe_altWedge,
    coe_altWedge, wedgeFun_assoc, ← wedgeFun_cast]
  rfl

/-- **Graded commutativity**: `a ∧ b = (−1)^{kl} b ∧ a`, the degree `l + k` read as `k + l`. -/
theorem altWedge_comm (a : M [⋀^Fin k]→ₗ[ℝ] ℝ) (b : M [⋀^Fin l]→ₗ[ℝ] ℝ) :
    altWedge a b =
      ((-1 : ℝ) ^ (k * l)) • (altWedge b a).domDomCongr (finCongr (Nat.add_comm l k)) := by
  ext v
  rw [AlternatingMap.smul_apply, AlternatingMap.domDomCongr_apply, altWedge_apply, altWedge_apply,
    wedgeFun_comm, ← wedgeFun_cast, smul_eq_mul]
  rfl

/-- The unit `1 ∈ Λ⁰`. -/
abbrev altOne : M [⋀^Fin 0]→ₗ[ℝ] ℝ := AlternatingMap.constOfIsEmpty ℝ M (Fin 0) 1

/-- **The unit on the right**: `b ∧ 1 = b` (the degree `l + 0` is `l`). -/
theorem altWedge_altOne (b : M [⋀^Fin l]→ₗ[ℝ] ℝ) : altWedge b altOne = b := by
  ext v
  rw [altWedge_apply]
  unfold wedgeFun wedgeFunAux
  have h : ∀ σ : Perm (Fin (l + 0)), ((Perm.sign σ : ℤ) : ℝ) *
      (b (fun i => v (σ (Fin.cast rfl (Fin.castAdd 0 i)))) *
        altOne (fun j : Fin 0 => v (σ (Fin.cast rfl (Fin.natAdd l j))))) = b v := fun σ => by
    have hb := b.map_perm v σ
    simp only [Fin.cast_eq_self, Fin.castAdd_zero, AlternatingMap.constOfIsEmpty_apply,
      Function.const_apply, mul_one]
    change ((Perm.sign σ : ℤ) : ℝ) * b (v ∘ σ) = b v
    rw [hb, Units.smul_def, zsmul_eq_mul, ← mul_assoc, wedge_sign_sq, one_mul]
  rw [Finset.sum_congr rfl fun σ _ => h σ, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul, wedgeCoeff, Nat.factorial_zero, Nat.cast_one, mul_one,
    ← mul_assoc]
  change ((l.factorial : ℝ))⁻¹ * (l.factorial : ℝ) * b v = b v
  rw [inv_mul_cancel₀ (by positivity), one_mul]

/-- **The unit on the left**: `1 ∧ b = b`, the degree `0 + l` read as `l`. -/
theorem altWedge_altOne_left (b : M [⋀^Fin l]→ₗ[ℝ] ℝ) :
    (altWedge altOne b).domDomCongr (finCongr (Nat.zero_add l)) = b := by
  rw [altWedge_comm, zero_mul, pow_zero, one_smul, altWedge_altOne]
  ext v
  rfl

end Alternating

/-! ### Forms on an M-polyfold -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {k l m : ℕ}

/-- **Associativity** of the wedge product of forms: `(ω ∧ τ) ∧ η = ω ∧ (τ ∧ η)`, the degree
`k + (l + m)` read as `(k + l) + m` (`formCast`). -/
theorem formWedge_assoc (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin l]→ₗ[ℝ] ℝ)
    (η : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin m]→ₗ[ℝ] ℝ) :
    formWedge (formWedge ω τ) η =
      formCast (Nat.add_assoc k l m).symm (formWedge ω (formWedge τ η)) :=
  funext fun x => altWedge_assoc (ω x) (τ x) (η x)

/-- **Graded commutativity** of the wedge product of forms: `ω ∧ τ = (−1)^{kl} τ ∧ ω`. -/
theorem formWedge_comm (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ)
    (τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin l]→ₗ[ℝ] ℝ) :
    formWedge ω τ = ((-1 : ℝ) ^ (k * l)) • formCast (Nat.add_comm l k) (formWedge τ ω) :=
  funext fun x => altWedge_comm (ω x) (τ x)

variable (P) in
/-- The constant function `1`, as a `0`-form. -/
def formOne : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin 0]→ₗ[ℝ] ℝ := fun _ => altOne

theorem formOne_mem_scForms : formOne P ∈ P.scForms 0 := fun φ hφ =>
  (IsScSmoothRetractMap.real_const 1).congr fun q hq => by
    rw [chartForm, dif_pos hq]; rfl

theorem formLower_formOne : formLower (formOne P) = formOne P.shift := rfl

theorem formPullback_formOne {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {Q : MPolyfold Y} {f : X → Y} (hf : P.IsScSmoothMap Q f) :
    formPullback hf (formOne Q) = formOne P := rfl

/-- **The unit**: `τ ∧ 1 = τ`. -/
theorem formWedge_formOne (τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin l]→ₗ[ℝ] ℝ) :
    formWedge τ (formOne P) = τ :=
  funext fun x => altWedge_altOne (τ x)

/-- **The unit**: `1 ∧ τ = τ`, the degree `0 + l` read as `l`. -/
theorem formCast_formWedge_formOne (τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin l]→ₗ[ℝ] ℝ) :
    formCast (Nat.zero_add l) (formWedge (formOne P) τ) = τ :=
  funext fun x => altWedge_altOne_left (τ x)

end MPolyfold

/-! ### `Ω*_∞(X)` -/

namespace BundledMPolyfold

open MPolyfold

universe u

attribute [local instance high] wedgeAddCommMonoidFormsInfty wedgeModuleFormsInfty

variable (A : BundledMPolyfold.{u}) {k l m : ℕ}

/-- The `0`-form `1` on `Xⁱ`. -/
def formsOne (i : ℕ) : A.forms 0 i := ⟨formOne _, formOne_mem_scForms⟩

theorem formsStep_formsOne (i : ℕ) : A.formsStep 0 i (A.formsOne i) = A.formsOne (i + 1) :=
  Subtype.ext rfl

theorem formsMap_formsOne {i j : ℕ} (h : i ≤ j) :
    A.formsMap 0 i j h (A.formsOne i) = A.formsOne j := by
  induction j, h using Nat.le_induction with
  | base => rw [formsMap_self]; rfl
  | succ j hij ih =>
    rw [formsMap_succ A 0 hij, LinearMap.comp_apply, ih, formsStep_formsOne]

/-- **The unit `1 ∈ Ω⁰_∞(X)`**, the class of the constant function `1`. -/
def formsInftyOne : A.formsInfty 0 := A.formsInftyOf 0 0 (A.formsOne 0)

theorem formsInftyOf_formsOne (i : ℕ) : A.formsInftyOf 0 i (A.formsOne i) = A.formsInftyOne :=
  (congrArg (A.formsInftyOf 0 i) (A.formsMap_formsOne (Nat.zero_le i))).symm.trans
    (A.formsInftyOf_formsMap 0 (Nat.zero_le i) _)

theorem formsWedge_assoc (n : ℕ) (ω : A.forms k n) (τ : A.forms l n) (η : A.forms m n) :
    A.formsWedge (k + l) m n (A.formsWedge k l n ω τ) η =
      A.formsCast (Nat.add_assoc k l m).symm n
        (A.formsWedge k (l + m) n ω (A.formsWedge l m n τ η)) :=
  Subtype.ext ((formWedge_assoc ω.1 τ.1 η.1).trans (A.coe_formsCast (Nat.add_assoc k l m).symm n
    (A.formsWedge k (l + m) n ω (A.formsWedge l m n τ η))).symm)

theorem formsWedge_comm (n : ℕ) (ω : A.forms k n) (τ : A.forms l n) :
    A.formsWedge k l n ω τ =
      ((-1 : ℝ) ^ (k * l)) • A.formsCast (Nat.add_comm l k) n (A.formsWedge l k n τ ω) :=
  Subtype.ext ((formWedge_comm ω.1 τ.1).trans (by
    rw [Submodule.coe_smul, A.coe_formsCast]; rfl))

theorem formsWedge_formsOne (n : ℕ) (τ : A.forms l n) :
    A.formsWedge l 0 n τ (A.formsOne n) = τ :=
  Subtype.ext (formWedge_formOne τ.1)

theorem formsCast_formsWedge_formsOne (n : ℕ) (τ : A.forms l n) :
    A.formsCast (Nat.zero_add l) n (A.formsWedge 0 l n (A.formsOne n) τ) = τ :=
  Subtype.ext ((A.coe_formsCast _ n _).trans (formCast_formWedge_formOne τ.1))

theorem formsInftyWedge_assoc_aux (n : ℕ) (ω : A.forms k n) (τ : A.forms l n) (η : A.forms m n)
    {a : A.formsInfty k} {b : A.formsInfty l} {c : A.formsInfty m}
    (ha : a = A.formsInftyOf k n ω) (hb : b = A.formsInftyOf l n τ)
    (hc : c = A.formsInftyOf m n η) :
    A.formsInftyWedge (k + l) m (A.formsInftyWedge k l a b) c =
      A.formsInftyCast (Nat.add_assoc k l m).symm
        (A.formsInftyWedge k (l + m) a (A.formsInftyWedge l m b c)) := by
  subst ha hb hc
  calc _ = A.formsInftyWedge (k + l) m (A.formsInftyOf (k + l) n (A.formsWedge k l n ω τ))
          (A.formsInftyOf m n η) :=
        congrArg (fun x => A.formsInftyWedge (k + l) m x (A.formsInftyOf m n η))
          (A.formsInftyWedge_of_of n ω τ)
    _ = A.formsInftyOf (k + l + m) n (A.formsWedge (k + l) m n (A.formsWedge k l n ω τ) η) :=
        A.formsInftyWedge_of_of n _ _
    _ = A.formsInftyOf (k + l + m) n (A.formsCast (Nat.add_assoc k l m).symm n
          (A.formsWedge k (l + m) n ω (A.formsWedge l m n τ η))) :=
        congrArg _ (A.formsWedge_assoc n ω τ η)
    _ = A.formsInftyCast (Nat.add_assoc k l m).symm (A.formsInftyOf (k + (l + m)) n
          (A.formsWedge k (l + m) n ω (A.formsWedge l m n τ η))) :=
        (A.formsInftyCast_of _ n _).symm
    _ = A.formsInftyCast (Nat.add_assoc k l m).symm (A.formsInftyWedge k (l + m)
          (A.formsInftyOf k n ω) (A.formsInftyOf (l + m) n (A.formsWedge l m n τ η))) :=
        congrArg _ (A.formsInftyWedge_of_of n _ _).symm
    _ = _ := congrArg (fun x => A.formsInftyCast (Nat.add_assoc k l m).symm
          (A.formsInftyWedge k (l + m) (A.formsInftyOf k n ω) x))
          (A.formsInftyWedge_of_of n τ η).symm

/-- **2021 p. 198: associativity of `∧` on `Ω*_∞(X)`**, `(a ∧ b) ∧ c = a ∧ (b ∧ c)`, the degree
`k + (l + m)` read as `(k + l) + m` (`formsInftyCast`). -/
theorem formsInftyWedge_assoc (a : A.formsInfty k) (b : A.formsInfty l) (c : A.formsInfty m) :
    A.formsInftyWedge (k + l) m (A.formsInftyWedge k l a b) c =
      A.formsInftyCast (Nat.add_assoc k l m).symm
        (A.formsInftyWedge k (l + m) a (A.formsInftyWedge l m b c)) := by
  induction a using Module.DirectLimit.induction_on with
  | ih i ω =>
  induction b using Module.DirectLimit.induction_on with
  | ih j τ =>
  induction c using Module.DirectLimit.induction_on with
  | ih r η =>
  exact A.formsInftyWedge_assoc_aux (i + j + r) _ _ _
    (A.formsInftyOf_formsMap k (show i ≤ i + j + r by omega) ω).symm
    (A.formsInftyOf_formsMap l (show j ≤ i + j + r by omega) τ).symm
    (A.formsInftyOf_formsMap m (show r ≤ i + j + r by omega) η).symm

theorem formsInftyWedge_comm_aux (n : ℕ) (ω : A.forms k n) (τ : A.forms l n)
    {a : A.formsInfty k} {b : A.formsInfty l} (ha : a = A.formsInftyOf k n ω)
    (hb : b = A.formsInftyOf l n τ) :
    A.formsInftyWedge k l a b =
      ((-1 : ℝ) ^ (k * l)) • A.formsInftyCast (Nat.add_comm l k) (A.formsInftyWedge l k b a) := by
  subst ha hb
  calc _ = A.formsInftyOf (k + l) n (A.formsWedge k l n ω τ) := A.formsInftyWedge_of_of n ω τ
    _ = A.formsInftyOf (k + l) n (((-1 : ℝ) ^ (k * l)) •
          A.formsCast (Nat.add_comm l k) n (A.formsWedge l k n τ ω)) :=
        congrArg _ (A.formsWedge_comm n ω τ)
    _ = ((-1 : ℝ) ^ (k * l)) • A.formsInftyOf (k + l) n
          (A.formsCast (Nat.add_comm l k) n (A.formsWedge l k n τ ω)) := LinearMap.map_smul _ _ _
    _ = _ := congrArg _ ((A.formsInftyCast_of _ n _).symm.trans
          (congrArg _ (A.formsInftyWedge_of_of n τ ω).symm))

/-- **Graded commutativity of `∧` on `Ω*_∞(X)`**: `a ∧ b = (−1)^{kl} b ∧ a`, the degree `l + k`
read as `k + l`. -/
theorem formsInftyWedge_comm (a : A.formsInfty k) (b : A.formsInfty l) :
    A.formsInftyWedge k l a b =
      ((-1 : ℝ) ^ (k * l)) • A.formsInftyCast (Nat.add_comm l k) (A.formsInftyWedge l k b a) := by
  induction a using Module.DirectLimit.induction_on with
  | ih i ω =>
  induction b using Module.DirectLimit.induction_on with
  | ih j τ =>
  exact A.formsInftyWedge_comm_aux (i + j) _ _
    (A.formsInftyOf_formsMap k (Nat.le_add_right i j) ω).symm
    (A.formsInftyOf_formsMap l (Nat.le_add_left j i) τ).symm

/-- **The unit on the right**: `b ∧ 1 = b` on `Ω*_∞(X)`. -/
theorem formsInftyWedge_formsInftyOne (b : A.formsInfty l) :
    A.formsInftyWedge l 0 b A.formsInftyOne = b := by
  induction b using Module.DirectLimit.induction_on with
  | ih j τ =>
  calc _ = A.formsInftyWedge l 0 (A.formsInftyOf l j τ) (A.formsInftyOf 0 j (A.formsOne j)) :=
        congrArg _ (A.formsInftyOf_formsOne j).symm
    _ = A.formsInftyOf (l + 0) j (A.formsWedge l 0 j τ (A.formsOne j)) :=
        A.formsInftyWedge_of_of j _ _
    _ = _ := congrArg (A.formsInftyOf l j) (A.formsWedge_formsOne j τ)

/-- **The unit on the left**: `1 ∧ b = b` on `Ω*_∞(X)`, the degree `0 + l` read as `l`. -/
theorem formsInftyCast_formsInftyOne_wedge (b : A.formsInfty l) :
    A.formsInftyCast (Nat.zero_add l) (A.formsInftyWedge 0 l A.formsInftyOne b) = b := by
  induction b using Module.DirectLimit.induction_on with
  | ih j τ =>
  calc _ = A.formsInftyCast (Nat.zero_add l) (A.formsInftyWedge 0 l
          (A.formsInftyOf 0 j (A.formsOne j)) (A.formsInftyOf l j τ)) :=
        congrArg (fun x => A.formsInftyCast (Nat.zero_add l) (A.formsInftyWedge 0 l x _))
          (A.formsInftyOf_formsOne j).symm
    _ = A.formsInftyCast (Nat.zero_add l) (A.formsInftyOf (0 + l) j
          (A.formsWedge 0 l j (A.formsOne j) τ)) := congrArg _ (A.formsInftyWedge_of_of j _ _)
    _ = A.formsInftyOf l j (A.formsCast (Nat.zero_add l) j (A.formsWedge 0 l j (A.formsOne j) τ)) :=
        A.formsInftyCast_of _ j _
    _ = _ := congrArg (A.formsInftyOf l j) (A.formsCast_formsWedge_formsOne j τ)

/-! ### `Ω*_∞(X)` as a graded algebra -/

theorem gradedMonoid_mk_formsInftyCast {i j : ℕ} (h : i = j) (x : A.formsInfty i) :
    (GradedMonoid.mk j (A.formsInftyCast h x) : GradedMonoid fun k => A.formsInfty k) =
      GradedMonoid.mk i x := by
  subst h; rfl

/-- **`Ω*_∞(X)` is a graded semiring** under `∧` (2021 p. 198): the graded multiplication
`formsInftyWedge`, the unit `1`, associativity and bilinearity. -/
instance formsInftyGMul : GradedMonoid.GMul fun k => A.formsInfty k :=
  ⟨fun a b => A.formsInftyWedge _ _ a b⟩

instance formsInftyGOne : GradedMonoid.GOne fun k => A.formsInfty k := ⟨A.formsInftyOne⟩

instance formsInftyGSemiring : DirectSum.GSemiring fun k => A.formsInfty k where
  mul := GradedMonoid.GMul.mul
  mul_zero a := LinearMap.map_zero _
  zero_mul b := LinearMap.map_zero₂ _ b
  mul_add a b c := LinearMap.map_add _ b c
  add_mul a b c := LinearMap.map_add₂ _ a b c
  one := GradedMonoid.GOne.one
  one_mul := by
    rintro ⟨i, a⟩
    exact (A.gradedMonoid_mk_formsInftyCast (Nat.zero_add i) _).symm.trans
      (congrArg (GradedMonoid.mk i) (A.formsInftyCast_formsInftyOne_wedge a))
  mul_one := by
    rintro ⟨i, a⟩
    exact congrArg (GradedMonoid.mk i) (A.formsInftyWedge_formsInftyOne a)
  mul_assoc := by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨r, c⟩
    change GradedMonoid.mk (i + j + r) (A.formsInftyWedge (i + j) r (A.formsInftyWedge i j a b) c) =
      GradedMonoid.mk (i + (j + r)) (A.formsInftyWedge i (j + r) a (A.formsInftyWedge j r b c))
    rw [formsInftyWedge_assoc]
    exact A.gradedMonoid_mk_formsInftyCast _ _
  natCast n := n • A.formsInftyOne
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ n

theorem formsInfty_gMul (a : A.formsInfty k) (b : A.formsInfty l) :
    GradedMonoid.GMul.mul (A := fun k => A.formsInfty k) a b = A.formsInftyWedge k l a b := rfl

theorem formsInftyWedge_smul_formsInftyOne (r : ℝ) (x : A.formsInfty l) :
    GradedMonoid.mk (0 + l) (A.formsInftyWedge 0 l (r • A.formsInftyOne) x) =
      (GradedMonoid.mk l (r • x) : GradedMonoid fun k => A.formsInfty k) := by
  rw [LinearMap.map_smul₂, ← A.gradedMonoid_mk_formsInftyCast (Nat.zero_add l), LinearMap.map_smul,
    formsInftyCast_formsInftyOne_wedge]

/-- **`Ω*_∞(X)` is a graded `ℝ`-algebra** (2021 p. 198), with `ℝ → Ω⁰_∞(X)`, `r ↦ r · 1`. -/
instance formsInftyGAlgebra : DirectSum.GAlgebra ℝ fun k => A.formsInfty k where
  toFun := (LinearMap.toSpanSingleton ℝ _ A.formsInftyOne).toAddMonoidHom
  map_one := by
    change (1 : ℝ) • A.formsInftyOne = A.formsInftyOne
    exact one_smul ℝ _
  map_mul r s := by
    change GradedMonoid.mk 0 ((r * s) • A.formsInftyOne) =
      GradedMonoid.mk (0 + 0) (A.formsInftyWedge 0 0 (r • A.formsInftyOne) (s • A.formsInftyOne))
    rw [A.formsInftyWedge_smul_formsInftyOne, mul_smul]
  commutes r := by
    rintro ⟨i, x⟩
    change GradedMonoid.mk (0 + i) (A.formsInftyWedge 0 i (r • A.formsInftyOne) x) =
      GradedMonoid.mk (i + 0) (A.formsInftyWedge i 0 x (r • A.formsInftyOne))
    rw [A.formsInftyWedge_smul_formsInftyOne, LinearMap.map_smul, formsInftyWedge_formsInftyOne]
    rfl
  smul_def r := by
    rintro ⟨i, x⟩
    change GradedMonoid.mk i (r • x) =
      GradedMonoid.mk (0 + i) (A.formsInftyWedge 0 i (r • A.formsInftyOne) x)
    rw [A.formsInftyWedge_smul_formsInftyOne]

/-- The product of `Ω*_∞(X) = ⊕ₖ Ωᵏ_∞(X)` on homogeneous elements is `∧`. -/
theorem formsInftyGraded_of_mul_of (a : A.formsInfty k) (b : A.formsInfty l) :
    (DirectSum.of (fun k => A.formsInfty k) k a * DirectSum.of _ l b : A.formsInftyGraded) =
      DirectSum.of _ (k + l) (A.formsInftyWedge k l a b) :=
  DirectSum.of_mul_of a b

/-- **Graded commutativity on `Ω*_∞(X)`**: `a b = (−1)^{kl} b a` for `a`, `b` homogeneous of
degrees `k`, `l`. -/
theorem formsInftyGraded_of_mul_of_comm (a : A.formsInfty k) (b : A.formsInfty l) :
    (DirectSum.of (fun k => A.formsInfty k) k a * DirectSum.of _ l b : A.formsInftyGraded) =
      ((-1 : ℝ) ^ (k * l)) • (DirectSum.of _ l b * DirectSum.of _ k a) := by
  rw [formsInftyGraded_of_mul_of, formsInftyGraded_of_mul_of, formsInftyWedge_comm,
    ← DirectSum.lof_eq_of ℝ, LinearMap.map_smul, DirectSum.lof_eq_of]
  congr 1
  exact DirectSum.of_eq_of_gradedMonoid_eq (A.gradedMonoid_mk_formsInftyCast _ _)

/-- **2021 p. 198: `(Ω*_∞(X), d)` is a graded differential algebra**: `d` is a derivation of
degree `+1`, `d(a b) = (da) b + (−1)ᵏ a (db)` for `a` homogeneous of degree `k`
(`formsInftyD_formsInftyWedge`), with `d² = 0` (`formsInftyGradedD_comp_self`). -/
theorem formsInftyGradedD_of_mul_of (a : A.formsInfty k) (b : A.formsInfty l) :
    A.formsInftyGradedD (DirectSum.of (fun k => A.formsInfty k) k a * DirectSum.of _ l b) =
      A.formsInftyGradedD (DirectSum.of _ k a) * DirectSum.of _ l b +
        ((-1 : ℝ) ^ k) • (DirectSum.of _ k a * A.formsInftyGradedD (DirectSum.of _ l b)) := by
  have hD : ∀ (j : ℕ) (x : A.formsInfty j), A.formsInftyGradedD (DirectSum.of _ j x) =
      DirectSum.of (fun k => A.formsInfty k) (j + 1) (A.formsInftyD j x) := fun j x =>
    (congrArg A.formsInftyGradedD (DirectSum.lof_eq_of ℝ ℕ _ j x).symm).trans
      ((A.formsInftyGradedD_lof j x).trans (DirectSum.lof_eq_of ℝ ℕ _ _ _))
  have hof : ∀ (j : ℕ) (c : ℝ) (x : A.formsInfty j),
      DirectSum.of (fun k => A.formsInfty k) j (c • x) = c • DirectSum.of _ j x := fun j c x =>
    (DirectSum.lof_eq_of ℝ ℕ _ j _).symm.trans
      ((LinearMap.map_smul _ c x).trans (congrArg _ (DirectSum.lof_eq_of ℝ ℕ _ j x)))
  calc _ = A.formsInftyGradedD (DirectSum.of _ (k + l) (A.formsInftyWedge k l a b)) :=
        congrArg _ (A.formsInftyGraded_of_mul_of a b)
    _ = DirectSum.of _ (k + l + 1) (A.formsInftyD (k + l) (A.formsInftyWedge k l a b)) := hD _ _
    _ = DirectSum.of _ (k + l + 1)
          (A.formsInftyCast (Nat.add_right_comm k 1 l)
            (A.formsInftyWedge (k + 1) l (A.formsInftyD k a) b) +
          ((-1 : ℝ) ^ k) • A.formsInftyWedge k (l + 1) a (A.formsInftyD l b)) :=
        congrArg _ (A.formsInftyD_formsInftyWedge (Nat.add_right_comm k 1 l) a b)
    _ = DirectSum.of _ (k + l + 1) (A.formsInftyCast (Nat.add_right_comm k 1 l)
            (A.formsInftyWedge (k + 1) l (A.formsInftyD k a) b)) +
          ((-1 : ℝ) ^ k) • DirectSum.of _ (k + (l + 1))
            (A.formsInftyWedge k (l + 1) a (A.formsInftyD l b)) :=
        (map_add _ _ _).trans (congrArg _ (hof _ _ _))
    _ = DirectSum.of _ (k + 1 + l) (A.formsInftyWedge (k + 1) l (A.formsInftyD k a) b) +
          ((-1 : ℝ) ^ k) • DirectSum.of _ (k + (l + 1))
            (A.formsInftyWedge k (l + 1) a (A.formsInftyD l b)) :=
        congrArg (· + _) (DirectSum.of_eq_of_gradedMonoid_eq (A.gradedMonoid_mk_formsInftyCast _ _))
    _ = _ := (congrArg₂ (fun x y => x + ((-1 : ℝ) ^ k) • y)
        ((congrArg (· * DirectSum.of _ l b) (hD k a)).trans
          (A.formsInftyGraded_of_mul_of _ b)).symm
        ((congrArg (DirectSum.of _ k a * ·) (hD l b)).trans
          (A.formsInftyGraded_of_mul_of a _)).symm)

/-- **`f^*` preserves the unit**, so with `formsInftyPullback_formsInftyWedge` it is a morphism of
graded algebras `Ω*_∞(Y) → Ω*_∞(X)`. -/
theorem formsInftyPullback_formsInftyOne {B : BundledMPolyfold.{u}} (f : ScMap A.P B.P) :
    formsInftyPullback f 0 B.formsInftyOne = A.formsInftyOne :=
  (formsInftyPullback_of f 0 0 _).trans (congrArg _ (Subtype.ext rfl))

end BundledMPolyfold

end Polyfold
