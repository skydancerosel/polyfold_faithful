import Polyfold.Chapter4.VectorFields
import Polyfold.Chapter1.ScOneNotNormContinuous
import Polyfold.Chapter2.TameFaces

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 4, Appendix 4.5,
§4.5.1 "Definition of the Lie Bracket" (pp. 200–201), the level of the Lie bracket in the proof of
**Proposition 4.4.5** (p. 196; 2017: Proposition 4.5; preprint: Proposition 4.26).  §4.5.1 is new in
the 2021 edition.

# The level of the Lie bracket: a counterexample

## The text, paraphrased

(§4.5.1, p. 200) In a local model `O = r(U)`, the principal parts of sc-smooth vector fields `A`,
`B` satisfy `A(x) = Dr(x) A(x)`, `B(x) = Dr(x) B(x)` on `O₁`.  Differentiating at `x ∈ O₂` and using
the symmetry of `D²r(x)` shows that `DA(x) B(x) − DB(x) A(x)` lies in the fibre `(T_xO)₁` whenever
`x ∈ O₂`; this vector is `[A, B](x)`.  (p. 201) For `x ∈ O₂`, `[A, B](x)` "belongs to the level 1",
which is said to prove that `[A, B]` is an sc-smooth section of `TX|X² → X²`.

## What is formalized

* `BracketLevel.wshift`: the weighted shift `y ↦ (c_k y_{k+1})_k` on `c₀`.
* On the weighted sequence sc-Banach space `X` of `ScOneNotNormContinuous.lean`
  (`|x|_m = sup_k (k+1)^m |x_k|`, with `(k+1)^m x_k → 0`; level `m` is `c₀` in the coordinates
  `(k+1)^m x_k`), two sc-operators `X¹ → X`: `BracketLevel.opS`, `(Sx)_k = (−1)^k (k+1) x_k`
  (`diag((−1)^k)` on every level), and `BracketLevel.opT`, `(Tx)_k = (k+1) x_{k+1}` (on level `m`
  the weighted shift with weights `((k+1)/(k+2))^{m+1}`).
* `retractTangent_univ` (`TO = TE` for `O = E`), `isRetractVectorField_scOperator`: every
  sc-operator `E¹ → E` is a vector field on the local model `(E, E, E)` in the sense of 2021
  **Definition 4.4.3** (`IsRetractVectorField`); `idRetraction`, `retractLieBracket_scOperator`:
  for two of them the bracket `retractLieBracket` of §4.5.1 is the commutator `S₀ T₁ − T₀ S₁`.
  `BracketLevel.isRetractVectorField_opS`, `BracketLevel.isRetractVectorField_opT`.
* `BracketLevel.bracket_not_mem_level_one`: for `x_k = (k+1)^{-3}`, a point of `O₂ = X₂`
  (`BracketLevel.xPt`), `[S, T](x) ∉ X₁`.  `lieBracket_level_counterexample_2021`,
  `not_forall_lieBracket_mem_level_one_2021`: the sentence of p. 201 ("belongs to the level 1"), and
  that of p. 200 (here `T_xO = X₀`, so `(T_xO)₁ = X₁`), read as `[A, B](x) ∈ E₁` for `x ∈ O₂`,
  **do not hold as we read them**.

## What the text leaves implicit, and the choices made

* The hypotheses are those of the text: `(X, X, X)` with the identity retraction is a local model
  (the M-polyfold `X` with one chart), `S`, `T` are sc-smooth sections of `TO → O¹`, and `x ∈ O₂`.
  `DA(x)` is the derivative of `Ã = A ∘ r¹`, here `A` itself.
* What holds is the shifted statement: `x ∈ O_{m+2}` gives `[A, B](x) ∈ E_m`, i.e. `[A, B]` is an
  sc-smooth section of `TO|O² → O²` (`proposition_4_4_5_local_2021`, `VectorFields.lean`).  We read
  the two sentences as: `[A, B](x)` is a tangent vector at the point `x` of level `1` of `X¹`; this
  reading is the one formalized there.  Proposition 4.4.5 itself is not affected.
* The sketch in the docstring of `VectorFields.lean` (`E_m = ℓ²` with weights `4^{mk}`,
  `S = diag(2^k)`, `(Tx)_k = 2^k x_{k+1}`, `x_j = 4^{-j}/j`) is correct as it stands
  (`|x|_m² = Σ 4^{mk} x_k²`); the project has no weighted `ℓ²` sc-structure, so the same
  mechanism is formalized on the existing space `X`.  With polynomial weights the commutator of a
  diagonal operator and a shift loses only one level unless the diagonal oscillates, whence the
  sign `(−1)^k`: `[S, T]x = ((−1)^k (k+1)(2k+3) x_{k+1})_k`, and for `x_k = (k+1)^{-3}` the
  level-`1` coordinates `(k+1)[S, T](x)_k` have absolute value `P³ + P² ≥ 1/4`,
  `P = (k+1)/(k+2)`.
* "`∉ E₁`" is `∉ range (E.toBase 1)`, the project's encoding of the level `E₁ ⊆ E₀`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace BracketLevel

open ScOneExample

/-! ### Weighted shifts on `c₀` -/

/-- The weighted shift `y ↦ (c_k y_{k+1})_k` on `c₀` for a bounded weight `|c_k| ≤ B`. -/
def wshift (c : ℕ → ℝ) {B : ℝ} (hc : ∀ k, |c k| ≤ B) : c0 →L[ℝ] c0 :=
  LinearMap.mkContinuous
    { toFun := fun y => mkC0 (fun k => c k * y (k + 1)) (by
        refine squeeze_zero_norm (a := fun k => |B| * |y (k + 1)|) (fun k => ?_) ?_
        · rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right ((hc k).trans (le_abs_self B)) (abs_nonneg _)
        · simpa using (((tendsto_c0 y).comp (tendsto_add_atTop_nat 1)).abs.const_mul |B|))
      map_add' := fun y z => by ext k; simp [mul_add]
      map_smul' := fun r y => by ext k; simp; ring }
    |B| (fun y => by
      refine norm_le_of_forall (by positivity) fun k => ?_
      change |c k * y (k + 1)| ≤ |B| * ‖y‖
      rw [abs_mul]
      exact mul_le_mul ((hc k).trans (le_abs_self B)) (abs_apply_le_norm y _) (abs_nonneg _)
        (abs_nonneg _))

@[simp] lemma wshift_apply (c : ℕ → ℝ) {B : ℝ} (hc : ∀ k, |c k| ≤ B) (y : c0) (k : ℕ) :
    wshift c hc y k = c k * y (k + 1) := rfl

/-! ### The two vector fields -/

/-- The signs `(-1)^k`. -/
def sgn (k : ℕ) : ℝ := (-1) ^ k

lemma abs_sgn (k : ℕ) : |sgn k| = 1 := by simp [sgn]

lemma abs_sgn_le (k : ℕ) : |sgn k| ≤ 1 := (abs_sgn k).le

lemma sgn_succ (k : ℕ) : sgn (k + 1) = -sgn k := by simp [sgn, pow_succ]

/-- `S x = ((-1)^k (k+1) x_k)_k`, an sc-operator `X¹ → X`; on every level, in the coordinates
`(k+1)^m x_k`, it is `diag((-1)^k)`. -/
def opS : ScOperator X.shift X where
  lvl _ := diag sgn abs_sgn_le
  incl_comm m y := by
    ext k
    change w k * (sgn k * y k) = sgn k * (w k * y k)
    ring

/-- The weights `((k+1)/(k+2))^{m+1}` of `T` on level `m`. -/
def tw (m k : ℕ) : ℝ := (((k : ℝ) + 1) * w (k + 1)) ^ (m + 1)

lemma ratio_nonneg (k : ℕ) : 0 ≤ ((k : ℝ) + 1) * w (k + 1) :=
  mul_nonneg (by positivity) (w_pos _).le

lemma ratio_le_one (k : ℕ) : ((k : ℝ) + 1) * w (k + 1) ≤ 1 := by
  unfold w; push_cast
  rw [mul_one_div, div_le_one (by positivity)]
  linarith

lemma half_le_ratio (k : ℕ) : 1 / 2 ≤ ((k : ℝ) + 1) * w (k + 1) := by
  unfold w; push_cast
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma abs_tw_le (m k : ℕ) : |tw m k| ≤ 1 := by
  rw [tw, abs_of_nonneg (pow_nonneg (ratio_nonneg k) _)]
  exact pow_le_one₀ (ratio_nonneg k) (ratio_le_one k)

lemma w_mul_succ (k : ℕ) : w k * ((k : ℝ) + 1) = 1 := by
  unfold w; field_simp

/-- `T x = ((k+1) x_{k+1})_k`, an sc-operator `X¹ → X`; on level `m`, in the coordinates
`(k+1)^m x_k`, it is the weighted shift with weights `((k+1)/(k+2))^{m+1}`. -/
def opT : ScOperator X.shift X where
  lvl m := wshift (tw m) (abs_tw_le m)
  incl_comm m y := by
    ext k
    change w k * (tw (m + 1) k * y (k + 1)) = tw m k * (w (k + 1) * y (k + 1))
    unfold tw
    linear_combination ((((k : ℝ) + 1) * w (k + 1)) ^ (m + 1) * w (k + 1) * y (k + 1)) *
      w_mul_succ k

end BracketLevel

/-! ### Linear vector fields on `(E, E, E)` -/

/-- `TE = E¹ ⊕ E`: the tangent of the retract `(E, E, E)` is everything. -/
lemma retractTangent_univ (E : ScBanach) : retractTangent E univ univ = univ := by
  have hU : IsRelOpenInQuadrant E univ univ :=
    ⟨isPartialQuadrant_univ E, univ, isOpen_univ, (inter_univ _).symm⟩
  have h := retractTangent_eq (ScRetraction.id hU)
  have hR : (ScRetraction.id hU).retract = univ := image_id _
  rw [hR] at h
  rw [h]
  refine eq_univ_of_forall fun p => (ScRetraction.id hU).mem_tangent_iff.2 ⟨trivial, ?_⟩
  exact tangentMap_id_eqOn (isScDomain_univ E) trivial

/-- An sc-operator `S : E¹ → E` is (the principal part of) an sc-smooth vector field on the
local model `(E, E, E)` (2021 Definition 4.4.3, `IsRetractVectorField`). -/
theorem isRetractVectorField_scOperator {E : ScBanach} (S : ScOperator E.shift E) :
    IsRetractVectorField E univ univ (S 0) := by
  refine ⟨fun x _ => ?_, fun ρ _ => ?_⟩
  · rw [retractTangent_univ]; exact mem_univ _
  · exact ρ.isScSmooth.scPair ρ.isScDomain (IsScSmooth.comp ρ.isScDomain (isScDomain_univ _)
      (S.isScSmooth (isScDomain_univ _)) ρ.isScSmooth (mapsTo_univ _ _))

/-- The identity retraction of `E` (onto `O = E`). -/
def idRetraction (E : ScBanach) : ScRetraction E univ :=
  ScRetraction.id ⟨isPartialQuadrant_univ E, univ, isOpen_univ, (inter_univ _).symm⟩

lemma idRetraction_retract (E : ScBanach) : (idRetraction E).retract = univ := image_id _

/-- For linear vector fields the bracket is the commutator: `[S, T](x) = S₀(T₁ x) − T₀(S₁ x)`. -/
theorem retractLieBracket_scOperator {E : ScBanach} (S T : ScOperator E.shift E)
    (x : E.shift 1) :
    retractLieBracket (idRetraction E) (S 0) (T 0) x = S 0 (T 1 x) - T 0 (S 1 x) := by
  unfold retractLieBracket
  have hshift : ∀ A : E 1 → E 0, A ∘ (idRetraction E).shift = A := fun A => funext fun z => by
    simp only [comp_apply, ScRetraction.shift_apply]
    congr 1
    exact levelMap_eq_of_toBase_eq rfl
  rw [hshift, hshift]
  have hU : (idRetraction E).shift.U = univ := rfl
  rw [hU, ScOperator.scDeriv_eq S (isScDomain_univ _) trivial,
    ScOperator.scDeriv_eq T (isScDomain_univ _) trivial, S.levelMap_eq, T.levelMap_eq]

namespace BracketLevel

open ScOneExample

/-- The point `x_k = 1/(k+1)³` of `X₂`, in the level-`2` coordinates `(k+1)² x_k = 1/(k+1)`. -/
def xPt : X.shift 1 := mkC0 w tendsto_one_div_add_atTop_nhds_zero_nat

/-- `[S, T](x) ∉ X₁` for `x = xPt ∈ X₂`: in level-`1` coordinates `(k+1)[S, T](x)_k` has absolute
value `P³ + P² ≥ 1/4`, `P = (k+1)/(k+2)`, so it does not tend to `0`. -/
theorem bracket_not_mem_level_one :
    retractLieBracket (idRetraction X) (opS 0) (opT 0) xPt ∉ range (X.toBase 1) := by
  rw [retractLieBracket_scOperator]
  rintro ⟨z, hz⟩
  obtain ⟨K, hK⟩ := eventually_abs_lt (z : c0) (by norm_num : (0 : ℝ) < 1 / 4)
  have hk : (X.toBase 1 z : c0) K = ((opS 0 (opT 1 xPt) - opT 0 (opS 1 xPt) : X 0) : c0) K := by
    rw [hz]
  rw [X_toBase_apply, pow_one] at hk
  change w K * (z : c0) K = sgn K * (tw 1 K * w (K + 1)) - tw 0 K * (sgn (K + 1) * w (K + 1))
    at hk
  have hzK : (z : c0) K = sgn K * ((((K : ℝ) + 1) * w (K + 1)) ^ 3 +
      (((K : ℝ) + 1) * w (K + 1)) ^ 2) := by
    have h1 : (z : c0) K = ((K : ℝ) + 1) * (w K * (z : c0) K) := by
      rw [← mul_assoc, mul_comm ((K : ℝ) + 1), w_mul_succ, one_mul]
    rw [h1, hk, sgn_succ]; unfold tw; ring
  have hPh := half_le_ratio K
  have h := hK K le_rfl
  rw [hzK, abs_mul, abs_sgn, one_mul, abs_of_nonneg (by positivity)] at h
  nlinarith

/-- `S` is an sc-smooth vector field on `(X, X, X)` (2021 Definition 4.4.3). -/
theorem isRetractVectorField_opS :
    IsRetractVectorField X univ (idRetraction X).retract (opS 0) := by
  rw [idRetraction_retract]; exact isRetractVectorField_scOperator _

/-- `T` is an sc-smooth vector field on `(X, X, X)` (2021 Definition 4.4.3). -/
theorem isRetractVectorField_opT :
    IsRetractVectorField X univ (idRetraction X).retract (opT 0) := by
  rw [idRetraction_retract]; exact isRetractVectorField_scOperator _

end BracketLevel

/-- **2021 Appendix 4.5, §4.5.1, pp. 200–201** (does not hold as we read it): there are a local
model `(O, C, E)` with a retraction `r` onto `O`, two sc-smooth vector fields `A`, `B` on it (2021
Definition 4.4.3) and `x ∈ O₂` with `[A, B](x) ∉ E₁`. -/
theorem lieBracket_level_counterexample_2021 :
    ∃ (E : ScBanach) (R : ScRetraction E univ) (A B : E 1 → E 0),
      IsRetractVectorField E univ R.retract A ∧ IsRetractVectorField E univ R.retract B ∧
      ∃ x ∈ E.shift.lvlSet (E.lvlSet R.retract 1) 1,
        retractLieBracket R A B x ∉ range (E.toBase 1) := by
  refine ⟨ScOneExample.X, idRetraction _, BracketLevel.opS 0, BracketLevel.opT 0,
    BracketLevel.isRetractVectorField_opS, BracketLevel.isRetractVectorField_opT,
    BracketLevel.xPt, ?_, BracketLevel.bracket_not_mem_level_one⟩
  rw [idRetraction_retract]; trivial

/-- The negation of the sentence of 2021 p. 201, read as `[A, B](x) ∈ E₁` for every local model,
all vector fields `A`, `B` and all `x ∈ O₂`. -/
theorem not_forall_lieBracket_mem_level_one_2021 :
    ¬ ∀ (E : ScBanach) (R : ScRetraction E univ) (A B : E 1 → E 0),
      IsRetractVectorField E univ R.retract A → IsRetractVectorField E univ R.retract B →
      ∀ x ∈ E.shift.lvlSet (E.lvlSet R.retract 1) 1,
        retractLieBracket R A B x ∈ range (E.toBase 1) := by
  intro h
  obtain ⟨E, R, A, B, hA, hB, x, hx, hn⟩ := lieBracket_level_counterexample_2021
  exact hn (h E R A B hA hB x hx)

end Polyfold
