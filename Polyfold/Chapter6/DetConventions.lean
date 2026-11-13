import Polyfold.Chapter6.Stabilization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §§6.3–6.4: two remarks on
conventions for determinants.  Gaps G.57 and G.58.

# Conventions for determinants

## The alternative determinant (after Definition 6.4.1, p. 246; gap G.57)

Some authors use `λ(ker T) ⊗ λ(coker(T)*)` in place of `det(T) = λ(ker T) ⊗ λ*(coker T)`; the two
are naturally isomorphic once `λ*(A)` and `λ(A*)` are identified.  With the identification `ι` of
Definition 6.3.1 (`iotaDual`, natural by Proposition 6.3.2, `proposition_6_3_2`):

* `iotaDualEquiv`: `ι : λ(A*) ≅ λ*(A)` is an isomorphism for finite-dimensional `A`;
* `altLinDet T = λ(ker T) ⊗ λ((F / R(T))*)`, `altLinDetEquiv T : altLinDet T ≅ det(T)`
  (`id ⊗ ι`), computed by `altLinDetEquiv_tmul_dualBasis`:
  `(a₁ ∧ … ∧ aₖ) ⊗ (d₁* ∧ … ∧ dₘ*) ↦ (a₁ ∧ … ∧ aₖ) ⊗ (d₁ ∧ … ∧ dₘ)*` for a basis `d` of the cokernel
  and its dual basis; `altFredholmDetEquiv` for a Fredholm operator.

## The identification (6.25), preprint (95) (after Proposition 6.4.15, p. 257; gap G.58)

* `stdLine n : ℝ ≅ λ(ℝⁿ)`, `1 ↦ e₁ ∧ … ∧ eₙ` (`stdLine_one`), with inverse
  `c₁ ∧ … ∧ cₙ ↦ det([c₁, …, cₙ])` (`stdLine_symm_wedge`), the matrix with columns `cⱼ`;
* `stdLineDual n : λ*(ℝⁿ) ≅ ℝ*`, the dual (transpose) of `stdLine n`, with
  `(e₁ ∧ … ∧ eₙ)* ↦ 1*` (`stdLineDual_dualVec`): the isomorphism `σ` of Proposition 6.4.15;
* `tensorStdLine n V : V ⊗ λ(ℝⁿ) ≅ V`, `v ⊗ (e₁ ∧ … ∧ eₙ) ↦ v` (`tensorStdLine_tmul_stdWedge`), and
  `tensorStdLineDual n V : V ⊗ λ*(ℝⁿ) ≅ V`, `v ⊗ (e₁ ∧ … ∧ eₙ)* ↦ v`
  (`tensorStdLineDual_tmul_dualVec`), for every vector space `V` (the text asks `V`
  finite-dimensional; this is not needed).
-/

open Module TensorProduct

noncomputable section

namespace Polyfold

/-! ### `ι : λ(A*) ≅ λ*(A)` and the alternative determinant -/

section Alt

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- A nonzero linear map out of a line is injective. -/
theorem injective_of_finrank_eq_one {L M : Type*} [AddCommGroup L] [Module ℝ L] [AddCommGroup M]
    [Module ℝ M] (h1 : finrank ℝ L = 1) {g : L →ₗ[ℝ] M} (hg : g ≠ 0) : Function.Injective g := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  by_contra hne
  refine hg (LinearMap.ext fun w => ?_)
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one h1 hne w
  rw [map_smul, hv, smul_zero, LinearMap.zero_apply]

variable (A) [FiniteDimensional ℝ A]

/-- **Definition 6.3.1 (2021, p. 242), `ι` as an isomorphism**: `ι : λ(A*) → λ*(A)` is an
isomorphism of lines for finite-dimensional `A`. -/
def iotaDualEquiv : maxPow (Module.Dual ℝ A) ≃ₗ[ℝ] maxPowDual A :=
  LinearEquiv.ofBijective (iotaDual A) <| by
    have hinj := injective_of_finrank_eq_one finrank_maxPow (iotaDual_ne_zero (E := A))
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_maxPow.trans finrank_maxPowDual.symm)).1 hinj⟩

@[simp] theorem iotaDualEquiv_apply (ω : maxPow (Module.Dual ℝ A)) :
    iotaDualEquiv A ω = iotaDual A ω := rfl

variable {A}

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **The alternative determinant (2021, p. 246, after Definition 6.4.1)**:
`λ(ker T) ⊗ λ(coker(T)*)`. -/
abbrev altLinDet (T : E →ₗ[ℝ] F) : Type _ :=
  maxPow (LinearMap.ker T) ⊗[ℝ] maxPow (Module.Dual ℝ (F ⧸ LinearMap.range T))

/-- **The two determinants are isomorphic (2021, p. 246, after Definition 6.4.1)**:
`λ(ker T) ⊗ λ(coker(T)*) ≅ λ(ker T) ⊗ λ*(coker T) = det(T)` by `id ⊗ ι`, with `ι` of
Definition 6.3.1. -/
def altLinDetEquiv (T : E →ₗ[ℝ] F) [FiniteDimensional ℝ (F ⧸ LinearMap.range T)] :
    altLinDet T ≃ₗ[ℝ] linDet T :=
  TensorProduct.congr (LinearEquiv.refl ℝ _) (iotaDualEquiv _)

theorem altLinDetEquiv_tmul (T : E →ₗ[ℝ] F) [FiniteDimensional ℝ (F ⧸ LinearMap.range T)]
    (a : maxPow (LinearMap.ker T)) (e : maxPow (Module.Dual ℝ (F ⧸ LinearMap.range T))) :
    altLinDetEquiv T (a ⊗ₜ e) = a ⊗ₜ iotaDual _ e := rfl

/-- **The isomorphism on wedges**:
`(a₁ ∧ … ∧ aₖ) ⊗ (d₁* ∧ … ∧ dₘ*) ↦ (a₁ ∧ … ∧ aₖ) ⊗ (d₁ ∧ … ∧ dₘ)*`
for a basis `d` of `F / R(T)` and its dual basis `d*`. -/
theorem altLinDetEquiv_tmul_dualBasis (T : E →ₗ[ℝ] F)
    [FiniteDimensional ℝ (F ⧸ LinearMap.range T)] {k m : ℕ} (a : Fin k → LinearMap.ker T)
    (ha : k = finrank ℝ (LinearMap.ker T)) (d : Basis (Fin m) ℝ (F ⧸ LinearMap.range T))
    (hm : m = finrank ℝ (F ⧸ LinearMap.range T)) :
    altLinDetEquiv T (wedge a ha ⊗ₜ
        wedge (fun i => d.dualBasis i) (hm.trans Subspace.dual_finrank_eq.symm)) =
      wedge a ha ⊗ₜ dualVec (wedge d hm) := by
  rw [altLinDetEquiv_tmul, iotaDual_wedge_dualBasis]

/-- `λ(ker T) ⊗ λ(coker(T)*)` for a bounded operator. -/
abbrev altFredholmDet {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F) : Type _ :=
  altLinDet (T : E →ₗ[ℝ] F)

/-- **(2021, p. 246, after Definition 6.4.1)** For a Fredholm operator `T`,
`λ(ker T) ⊗ λ(coker(T)*) ≅ det(T)` (`altLinDetEquiv`). -/
def altFredholmDetEquiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {T : E →L[ℝ] F} (hT : T.IsFredholm) :
    altFredholmDet T ≃ₗ[ℝ] fredholmDet T :=
  haveI : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  altLinDetEquiv (T : E →ₗ[ℝ] F)

/-- For a Fredholm operator, `λ(ker T) ⊗ λ(coker(T)*)` is a line. -/
theorem finrank_altFredholmDet {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {T : E →L[ℝ] F} (hT : T.IsFredholm) :
    finrank ℝ (altFredholmDet T) = 1 :=
  (altFredholmDetEquiv hT).finrank_eq.trans (finrank_fredholmDet hT)

end Alt

/-! ### The identification (6.25) -/

section Std

variable (n : ℕ)

/-- **(6.25) (2021, p. 257, after Proposition 6.4.15)**: `ℝ ≅ λ(ℝⁿ)`, `r ↦ r · e₁ ∧ … ∧ eₙ`. -/
def stdLine : ℝ ≃ₗ[ℝ] maxPow (Fin n → ℝ) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℝ _ (stdWedge n))
    ⟨smul_left_injective ℝ (stdWedge_ne_zero n),
      fun w => exists_smul_eq_of_finrank_eq_one finrank_maxPow (stdWedge_ne_zero n) w⟩

@[simp] theorem stdLine_apply (r : ℝ) : stdLine n r = r • stdWedge n := rfl

/-- `1 ↦ e₁ ∧ … ∧ eₙ`. -/
theorem stdLine_one : stdLine n 1 = stdWedge n := by rw [stdLine_apply, one_smul]

/-- **The inverse of (6.25)**: `c₁ ∧ … ∧ cₙ ↦ det([c₁, …, cₙ])`, the determinant of the matrix with
columns `cⱼ`. -/
theorem stdLine_symm_wedge (c : Fin n → Fin n → ℝ) (h : n = finrank ℝ (Fin n → ℝ)) :
    (stdLine n).symm (wedge c h) = (Matrix.of fun i j => c j i).det := by
  rw [LinearEquiv.symm_apply_eq, stdLine_apply, stdWedge,
    wedge_eq_det_smul' (Pi.basisFun ℝ (Fin n)) c h, Basis.det_apply]
  congr 2

/-- **`σ : λ*(ℝⁿ) ≅ ℝ*` (2021, p. 257, Proposition 6.4.15 and after)**: the dual (transpose) of
(6.25), `φ ↦ φ ∘ stdLine n`. -/
def stdLineDual : maxPowDual (Fin n → ℝ) ≃ₗ[ℝ] Module.Dual ℝ ℝ :=
  (stdLine n).dualMap

theorem stdLineDual_apply (φ : maxPowDual (Fin n → ℝ)) (r : ℝ) :
    stdLineDual n φ r = φ (r • stdWedge n) := rfl

/-- `σ((e₁ ∧ … ∧ eₙ)*) = 1*`. -/
theorem stdLineDual_dualVec : stdLineDual n (dualVec (stdWedge n)) = dualVec (1 : ℝ) := by
  refine dual_ext_of_ne_zero (Module.finrank_self ℝ) one_ne_zero ?_
  rw [stdLineDual_apply, one_smul, dualVec_self finrank_maxPow (stdWedge_ne_zero n),
    dualVec_self (Module.finrank_self ℝ) one_ne_zero]

variable (V : Type*) [AddCommGroup V] [Module ℝ V]

/-- **`V ⊗ λ(ℝⁿ) ≅ V` (2021, p. 257)**: `v ⊗ ω ↦ (6.25)⁻¹(ω) · v`. -/
def tensorStdLine : V ⊗[ℝ] maxPow (Fin n → ℝ) ≃ₗ[ℝ] V :=
  (TensorProduct.congr (LinearEquiv.refl ℝ V) (stdLine n).symm).trans (TensorProduct.rid ℝ V)

theorem tensorStdLine_tmul (v : V) (ω : maxPow (Fin n → ℝ)) :
    tensorStdLine n V (v ⊗ₜ ω) = (stdLine n).symm ω • v := rfl

/-- `v ⊗ (e₁ ∧ … ∧ eₙ) ↦ v`. -/
theorem tensorStdLine_tmul_stdWedge (v : V) : tensorStdLine n V (v ⊗ₜ stdWedge n) = v := by
  rw [tensorStdLine_tmul, ← stdLine_one, LinearEquiv.symm_apply_apply, one_smul]

/-- `v ⊗ (c₁ ∧ … ∧ cₙ) ↦ det([c₁, …, cₙ]) · v`. -/
theorem tensorStdLine_tmul_wedge (v : V) (c : Fin n → Fin n → ℝ) (h : n = finrank ℝ (Fin n → ℝ)) :
    tensorStdLine n V (v ⊗ₜ wedge c h) = (Matrix.of fun i j => c j i).det • v := by
  rw [tensorStdLine_tmul, stdLine_symm_wedge]

/-- **`V ⊗ λ*(ℝⁿ) ≅ V` (2021, p. 257)**: `v ⊗ φ ↦ φ(e₁ ∧ … ∧ eₙ) · v`, through `σ` and
`ℝ* ≅ ℝ`, `1* ↦ 1`. -/
def tensorStdLineDual : V ⊗[ℝ] maxPowDual (Fin n → ℝ) ≃ₗ[ℝ] V :=
  (TensorProduct.congr (LinearEquiv.refl ℝ V)
    ((stdLineDual n).trans (LinearMap.ringLmapEquivSelf ℝ ℝ ℝ))).trans (TensorProduct.rid ℝ V)

theorem tensorStdLineDual_tmul (v : V) (φ : maxPowDual (Fin n → ℝ)) :
    tensorStdLineDual n V (v ⊗ₜ φ) = φ (stdWedge n) • v := by
  change stdLineDual n φ 1 • v = _
  rw [stdLineDual_apply, one_smul]

/-- `v ⊗ (e₁ ∧ … ∧ eₙ)* ↦ v`. -/
theorem tensorStdLineDual_tmul_dualVec (v : V) :
    tensorStdLineDual n V (v ⊗ₜ dualVec (stdWedge n)) = v := by
  rw [tensorStdLineDual_tmul, dualVec_self finrank_maxPow (stdWedge_ne_zero n), one_smul]

end Std

end Polyfold
