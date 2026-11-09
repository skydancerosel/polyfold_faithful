import Polyfold.Chapter6.LinOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 227–228: the objects `Or_x^f` of the functor of **Theorem 6.6.13 (preprint 6.37)** and its proof (an
orientation of `DET(f, φ(t))` is carried along a finite covering of the path by orientable
neighbourhoods) *(book 2017: Theorem 6.2, p. 213; see `BookConcordance.md`)*.

# Transferring orientations between chart points

## The text, paraphrased

For a smooth point `x`, `Lin(f, x)` is a convex set of Fredholm operators `T_xX → Y_x` and
`DET(f, x) = ⋃_{L ∈ Lin(f, x)} {L} × det(L)` is a line bundle over it (p. 219); `Or_x^f` is the
set of its two orientations (Definition 6.6.2 (preprint 6.27)).  (Theorem 6.6.13 (preprint 6.37)) There is a unique functor `Γ_f`
from the sc-smooth homotopy classes of paths to the bijections, `[φ] ↦ Γ_f([φ]) :
Or_{φ(0)}^f → Or_{φ(1)}^f`, agreeing with the local propagation `φ_*` in every orientable
neighbourhood.  Proof: for `t₀ ∈ [0, 1]` choose an orientable neighbourhood `U(φ(t₀))`; an
orientation at one `t` near `t₀` determines the orientations at the nearby `s`; by compactness of
`[0, 1]` a finite covering carries `o₀` at `φ(0)` to `o₁` at `φ(1)`.  `T_xX`, `Y_x`, `Lin(f, x)`
and `Or_x^f` are the same whichever neighbourhood is used.

## What is formalized

* Conjugation of determinant lines: for `A : E ≅ E'`, `Γ : F ≅ F'` and `S' A = Γ S`,
  `conjDet A Γ h : det(S) = λ(ker S) ⊗ λ*(coker S) ≅ det(S')`, the kernels by `A` and the
  cokernels by `Γ`; `conjDet_trans`, `conjDet_congr`, `conjDet_refl`; `gammaProj_conjDet` (the
  isomorphisms `γ^P` commute with `conjDet`, for projections with `P' Γ = Γ P`).
* `LineOrientation.conj A Γ hmem o`: for `Γ⁻¹ C' A ⊆ C`, an orientation `o` of `DET` over `C`
  gives the orientation `S' ↦ conjDet(o(Γ⁻¹ S' A))` of `DET` over `C'`; it is continuous, read in
  the local charts `DET(T, P, ε)` (`coord_conjDet_coordInv`); `conj_apply`, `conj_refl`,
  `conj_trans`, `conj_congr`.
* For two chart points `p`, `p'` at `x`: `ChartPoint.baseDeriv p p' = D(τ ∘ r_W)(z)`, the
  derivative of the base transition `τ = φ' ∘ φ⁻¹` (`baseDeriv_self`, and the chain rule
  `baseDeriv_trans`), and `ChartPoint.fiberMap p p' = Γ`, the fibre part at `z` of the strong
  bundle transition `Φ' ∘ Φ⁻¹` (`fiberMap_self`, `fiberMap_trans`).  They give
  `ChartPoint.transferT p p' : T_zO ≅ T_{z'}O'` and `ChartPoint.transferK p p' : K_z ≅ K'_{z'}`
  (`transferT_self_apply`, `transferT_trans_apply`, and the same for `K`).  Neither depends on
  `f`.
* `ChartPoint.scDeriv_principal_baseDeriv`: at a zero of an sc-smooth section `g`,
  `D(ĝ' ∘ r')(z') ∘ A = Γ ∘ D(ĝ ∘ r)(z)`.  `ChartPoint.IsScPlusOp.conj`: at a smooth point
  `Γ ∘ a ∘ A⁻¹` is sc⁺ when `a` is (`A⁻¹` and `Γ` are sc-operators, `isScOperator_baseDeriv`,
  `isScOperator_fiberMap`).  Hence `ChartPoint.mem_linSet_transfer_iff`:
  `L ∈ Lin_p(f, x) ↔ Γ ∘ L ∘ A⁻¹ ∈ Lin_{p'}(f, x)`.
* `ChartPoint.orTransfer p p' hf hx : p.Or f hf ≃ p'.Or f hf`, with `orTransfer_apply` (the value
  at `Γ L A⁻¹` is the image of the value at `L` under `det(L) ≅ det(Γ L A⁻¹)`),
  `orTransfer_self` and `orTransfer_trans`.

## Reading

`Lin(f, x)` and `Or_x^f` are made in a chart point `p` (`LinSet.lean`, `LinOrientation.lean`):
`T_xX` is read as `T_zO = Dr(z)E` and `Y_x` as `K_z = ρ(z)F` in the chart `p.c`.  Two chart
points at `x`, for instance from the orientable neighbourhoods of two values `t₀` in the proof of
Theorem 6.6.13 (preprint 6.37), give the different types `p.Or f hf` and `p'.Or f hf`; comparing orientations
there needs the identification `T_xX`, `Y_x` of the text, which is made explicit here by the
transition maps at `z`.  `A` is the derivative at `z` of `τ ∘ r_W`, with `r_W` the restriction of
`r` to `U ∩ r⁻¹(W)` for a fixed open `W` with `φ(V ∩ V') = O ∩ W`, a retraction onto the base
overlap.  `transferT` and `transferK` need no smoothness of `x`; it is used for the
sc⁺-operators, through the sc-subspaces `T_zO`, `K_z` and the sc-operators `A⁻¹`, `Γ`.
-/

open Module TensorProduct Bundle Topology Set

noncomputable section

namespace Polyfold

/-! ### The determinant isomorphism of a conjugation -/

section ConjLinear

variable {E F E' F' E'' F'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [NormedAddCommGroup F''] [NormedSpace ℝ F'']

variable (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F') {S : E →L[ℝ] F} {S' : E' →L[ℝ] F'}

/-- The wedge depends only on the family (not on the proof of `k = dim M`). -/
private theorem wedge_eq_of_eq {M : Type*} [AddCommGroup M] [Module ℝ M] {k : ℕ}
    {v w : Fin k → M} (h : v = w) (hv : k = finrank ℝ M) (hw : k = finrank ℝ M) :
    wedge v hv = wedge w hw := by
  subst h
  rfl

/-- **The kernels of conjugate operators**: `ker S ≅ ker S'`, `v ↦ A v`, for `S' ∘ A = Γ ∘ S`. -/
def conjKerEquiv (h : ∀ v, S' (A v) = Γ (S v)) :
    LinearMap.ker (S : E →ₗ[ℝ] F) ≃ₗ[ℝ] LinearMap.ker (S' : E' →ₗ[ℝ] F') where
  toFun v := ⟨A v, by
    have hv : S v = 0 := v.2
    change S' (A v) = 0
    rw [h, hv, map_zero]⟩
  map_add' v w := Subtype.ext (map_add A (v : E) w)
  map_smul' t v := Subtype.ext (map_smul A t (v : E))
  invFun w := ⟨A.symm w, by
    have hw : S' w = 0 := w.2
    change S (A.symm w) = 0
    apply Γ.injective
    rw [← h, ContinuousLinearEquiv.apply_symm_apply, hw, map_zero]⟩
  left_inv v := Subtype.ext (A.symm_apply_apply (v : E))
  right_inv w := Subtype.ext (A.apply_symm_apply (w : E'))

/-- `conjKerEquiv` is `A` on vectors. -/
@[simp] theorem coe_conjKerEquiv_apply (h : ∀ v, S' (A v) = Γ (S v))
    (v : LinearMap.ker (S : E →ₗ[ℝ] F)) : (conjKerEquiv A Γ h v : E') = A v := rfl

/-- `Γ(R(S)) = R(S')` for `S' ∘ A = Γ ∘ S`. -/
theorem map_range_eq_of_conj (h : ∀ v, S' (A v) = Γ (S v)) :
    (LinearMap.range (S : E →ₗ[ℝ] F)).map (Γ.toLinearEquiv : F →ₗ[ℝ] F') =
      LinearMap.range (S' : E' →ₗ[ℝ] F') := by
  ext y
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨A v, h v⟩
  · rintro ⟨w, rfl⟩
    refine ⟨S (A.symm w), ⟨A.symm w, rfl⟩, ?_⟩
    change Γ (S (A.symm w)) = S' w
    rw [← h, ContinuousLinearEquiv.apply_symm_apply]

/-- **The cokernels of conjugate operators**: `F / R(S) ≅ F' / R(S')`, `[y] ↦ [Γ y]`. -/
def conjCokerEquiv (h : ∀ v, S' (A v) = Γ (S v)) :
    (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) ≃ₗ[ℝ] (F' ⧸ LinearMap.range (S' : E' →ₗ[ℝ] F')) :=
  Submodule.Quotient.equiv _ _ Γ.toLinearEquiv (map_range_eq_of_conj A Γ h)

/-- `conjCokerEquiv` is induced by `Γ`. -/
@[simp] theorem conjCokerEquiv_mk (h : ∀ v, S' (A v) = Γ (S v)) (y : F) :
    conjCokerEquiv A Γ h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (Γ y) := rfl

/-- **The determinant isomorphism of a conjugation** `S' ∘ A = Γ ∘ S`:
`det(S) = λ(ker S) ⊗ λ*(coker S) ≅ λ(ker S') ⊗ λ*(coker S') = det(S')`, the kernels by `A` and
the cokernels by `Γ`. -/
def conjDet (h : ∀ v, S' (A v) = Γ (S v)) : fredholmDet S ≃ₗ[ℝ] fredholmDet S' :=
  TensorProduct.congr (maxPowEquiv (conjKerEquiv A Γ h))
    (maxPowDualEquiv (conjCokerEquiv A Γ h).symm)

/-- **`conjDet` on wedges**: `(a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)* ↦
(A a₁ ∧ … ∧ A aₙ) ⊗ ([Γ d₁] ∧ … ∧ [Γ d_l])*` for linearly independent `d`. -/
theorem conjDet_wedge_tmul (h : ∀ v, S' (A v) = Γ (S v))
    [FiniteDimensional ℝ (F' ⧸ LinearMap.range (S' : E' →ₗ[ℝ] F'))] {n l : ℕ}
    (a : Fin n → LinearMap.ker (S : E →ₗ[ℝ] F))
    (hn : n = finrank ℝ (LinearMap.ker (S : E →ₗ[ℝ] F)))
    {d : Fin l → F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)} (hd : LinearIndependent ℝ d)
    (hl : l = finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F))) :
    conjDet A Γ h (wedge a hn ⊗ₜ dualVec (wedge d hl)) =
      wedge (conjKerEquiv A Γ h ∘ a) (hn.trans (conjKerEquiv A Γ h).finrank_eq) ⊗ₜ
        dualVec (wedge (conjCokerEquiv A Γ h ∘ d)
          (hl.trans (conjCokerEquiv A Γ h).finrank_eq)) := by
  rw [conjDet, TensorProduct.congr_tmul, maxPowEquiv_wedge,
    maxPowDualEquiv_dualVec_symm _ hd]
  rfl

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- `λ(Φ' ∘ Φ) = λ(Φ') ∘ λ(Φ)` for isomorphisms. -/
theorem maxPowEquiv_trans {M N K : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] [AddCommGroup K] [Module ℝ K] (e : M ≃ₗ[ℝ] N) (e' : N ≃ₗ[ℝ] K) :
    maxPowEquiv (e ≪≫ₗ e') = maxPowEquiv e ≪≫ₗ maxPowEquiv e' := by
  apply LinearEquiv.toLinearMap_injective
  rw [LinearEquiv.coe_trans, coe_maxPowEquiv, coe_maxPowEquiv, coe_maxPowEquiv,
    ← maxPowMap_comp]
  rfl

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- `λ*(Φ' ∘ Φ) = λ*(Φ) ∘ λ*(Φ')` for isomorphisms. -/
theorem maxPowDualEquiv_trans {M N K : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] [AddCommGroup K] [Module ℝ K] (e : M ≃ₗ[ℝ] N) (e' : N ≃ₗ[ℝ] K) :
    maxPowDualEquiv (e ≪≫ₗ e') = maxPowDualEquiv e' ≪≫ₗ maxPowDualEquiv e := by
  rw [maxPowDualEquiv, maxPowDualEquiv, maxPowDualEquiv, maxPowEquiv_trans,
    LinearEquiv.dualMap_trans]

/-- **The determinant isomorphisms of conjugations compose.** -/
theorem conjDet_trans (A' : E' ≃L[ℝ] E'') (Γ' : F' ≃L[ℝ] F'') {S'' : E'' →L[ℝ] F''}
    (h : ∀ v, S' (A v) = Γ (S v)) (h' : ∀ v, S'' (A' v) = Γ' (S' v))
    (h'' : ∀ v, S'' ((A.trans A') v) = (Γ.trans Γ') (S v)) :
    (conjDet A Γ h).trans (conjDet A' Γ' h') = conjDet (A.trans A') (Γ.trans Γ') h'' := by
  rw [conjDet, conjDet, conjDet, ← TensorProduct.congr_trans, ← maxPowEquiv_trans,
    ← maxPowDualEquiv_trans]
  congr 2
  refine LinearEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (conjCokerEquiv (A.trans A') (Γ.trans Γ') h'').surjective y
  have hx : conjCokerEquiv (A.trans A') (Γ.trans Γ') h'' x =
      conjCokerEquiv A' Γ' h' (conjCokerEquiv A Γ h x) := by
    induction x using Submodule.Quotient.induction_on with
    | H y => rfl
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply, hx, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

/-- **`conjDet` depends only on the maps `A`, `Γ`.** -/
theorem conjDet_congr {A₁ A₂ : E ≃L[ℝ] E'} {Γ₁ Γ₂ : F ≃L[ℝ] F'} (hA : ∀ v, A₁ v = A₂ v)
    (hΓ : ∀ y, Γ₁ y = Γ₂ y) (h₁ : ∀ v, S' (A₁ v) = Γ₁ (S v))
    (h₂ : ∀ v, S' (A₂ v) = Γ₂ (S v)) : conjDet A₁ Γ₁ h₁ = conjDet A₂ Γ₂ h₂ := by
  obtain rfl : A₁ = A₂ := ContinuousLinearEquiv.ext (funext hA)
  obtain rfl : Γ₁ = Γ₂ := ContinuousLinearEquiv.ext (funext hΓ)
  rfl

/-- **`conjDet` of the identities** is the identification `det(S) = det(S')` for `S = S'`. -/
theorem conjDet_refl {S₁ S₂ : E →L[ℝ] F}
    (h : ∀ v, S₂ (ContinuousLinearEquiv.refl ℝ E v) = ContinuousLinearEquiv.refl ℝ F (S₁ v)) :
    conjDet (ContinuousLinearEquiv.refl ℝ E) (ContinuousLinearEquiv.refl ℝ F) h =
      linDetEquivOfEq (congrArg (fun T : E →L[ℝ] F => (T : E →ₗ[ℝ] F))
        (ContinuousLinearMap.ext fun v => (h v).symm)) := by
  obtain rfl : S₁ = S₂ := ContinuousLinearMap.ext fun v => (h v).symm
  rw [linDetEquivOfEq_self, conjDet]
  have h1 : conjKerEquiv (ContinuousLinearEquiv.refl ℝ E) (ContinuousLinearEquiv.refl ℝ F) h =
      LinearEquiv.refl ℝ _ := LinearEquiv.ext fun v => Subtype.ext rfl
  have h2 : (conjCokerEquiv (ContinuousLinearEquiv.refl ℝ E) (ContinuousLinearEquiv.refl ℝ F)
      h).symm = LinearEquiv.refl ℝ _ := by
    refine LinearEquiv.ext fun y => ?_
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      apply (conjCokerEquiv (ContinuousLinearEquiv.refl ℝ E) (ContinuousLinearEquiv.refl ℝ F)
        h).injective
      rw [LinearEquiv.apply_symm_apply]
      rfl
  rw [h1, h2, maxPowEquiv_refl, maxPowDualEquiv_refl, TensorProduct.congr_refl_refl]

end ConjLinear

/-! ### Good left-projections and `γ^P` under conjugation -/

section ConjProj

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [CompleteSpace E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [CompleteSpace F']

variable (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F') {S : E →L[ℝ] F} {S' : E' →L[ℝ] F'}

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `P' ∘ S' ∘ A = Γ ∘ P ∘ S` from `S' ∘ A = Γ ∘ S` and `P' ∘ Γ = Γ ∘ P`. -/
theorem conj_comp {P : F →L[ℝ] F} {P' : F' →L[ℝ] F'} (hP : ∀ y, P' (Γ y) = Γ (P y))
    (h : ∀ v, S' (A v) = Γ (S v)) : ∀ v, (P' ∘L S') (A v) = Γ ((P ∘L S) v) := fun v => by
  simp only [ContinuousLinearMap.comp_apply, h, hP]

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- **A conjugate of a good left-projection is one**: for `P ∈ Π_S`, `S' ∘ A = Γ ∘ S` and
`P' ∘ Γ = Γ ∘ P` (that is, `P' = Γ P Γ⁻¹`), `P' ∈ Π_{S'}`. -/
theorem IsGoodLeftProj.conj {P : F →L[ℝ] F} {P' : F' →L[ℝ] F'} (gP : IsGoodLeftProj S P)
    (hP : ∀ y, P' (Γ y) = Γ (P y)) (h : ∀ v, S' (A v) = Γ (S v)) : IsGoodLeftProj S' P' where
  isProj := by
    refine ContinuousLinearMap.ext fun y => ?_
    obtain ⟨y, rfl⟩ := Γ.surjective y
    have hPP : P (P y) = P y := DFunLike.congr_fun gP.isProj y
    rw [ContinuousLinearMap.comp_apply, hP, hP, hPP]
  finite_coker := by
    have := gP.finite_coker
    exact (conjCokerEquiv Γ Γ hP).finiteDimensional
  range_comp := by
    rw [← map_range_eq_of_conj A Γ (conj_comp A Γ hP h), gP.range_comp,
      map_range_eq_of_conj Γ Γ hP]

set_option maxHeartbeats 400000 in
-- The determinant isomorphisms of the conjugation unfold through several `maxPow` layers.
/-- **`γ^P` commutes with the determinant isomorphisms of a conjugation**: for `S' ∘ A = Γ ∘ S`,
`P' ∘ Γ = Γ ∘ P`, `P ∈ Π_S` and `P' ∈ Π_{S'}`, `γ^{P'}_{S'} ∘ det(A, Γ) = det(A, Γ) ∘ γ^P_S`
(the second `det(A, Γ)` for `P' S' ∘ A = Γ ∘ P S`). -/
theorem gammaProj_conjDet {P : F →L[ℝ] F} {P' : F' →L[ℝ] F'} (hP : ∀ y, P' (Γ y) = Γ (P y))
    (h : ∀ v, S' (A v) = Γ (S v)) (hS : S.IsFredholm) (hS' : S'.IsFredholm)
    (gP : IsGoodLeftProj S P) (gP' : IsGoodLeftProj S' P') (x : fredholmDet S) :
    gammaProj hS' gP' (conjDet A Γ h x) =
      conjDet A Γ (conj_comp A Γ hP h) (gammaProj hS gP x) := by
  have := hS.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) := hS.finite_coker
  have := hS'.finite_ker
  have : FiniteDimensional ℝ (F' ⧸ LinearMap.range (S' : E' →ₗ[ℝ] F')) := hS'.finite_coker
  have := gP.finite_coker
  have := gP'.finite_coker
  have := (gP.isFredholm_comp hS).finite_ker
  have := (gP'.isFredholm_comp hS').finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range ((P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    (gP.isFredholm_comp hS).finite_coker
  have : FiniteDimensional ℝ (F' ⧸ LinearMap.range ((P' ∘L S' : E' →L[ℝ] F') : E' →ₗ[ℝ] F')) :=
    (gP'.isFredholm_comp hS').finite_coker
  obtain ⟨a⟩ : Nonempty (Basis (Fin (finrank ℝ (LinearMap.ker (S : E →ₗ[ℝ] F)))) ℝ
      (LinearMap.ker (S : E →ₗ[ℝ] F))) := ⟨Module.finBasis ℝ _⟩
  obtain ⟨d⟩ : Nonempty (Basis (Fin (finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)))) ℝ
      (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F))) := ⟨Module.finBasis ℝ _⟩
  obtain ⟨j, b, hb, hj⟩ := exists_linearIndependent_append (projSeqJ S P) (proposition_6_4_10 gP).1
    a.linearIndependent rfl
  choose c hc using fun i => (proposition_6_4_10 gP).2.2.2 (d i)
  have hC : finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) + j =
      finrank ℝ (F ⧸ LinearMap.range ((P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    ((projSeq gP).finrank_eq_of_families rfl rfl hj).trans (cokerCompEquiv gP).symm.finrank_eq
  have hli := (projSeq gP).linearIndependent_append_lift a.linearIndependent rfl
    d.linearIndependent rfl hb hj hc (hC.trans (cokerCompEquiv gP).finrank_eq)
  have hPS := conj_comp A Γ hP h
  have hJ : ∀ v, projSeqJ S' P' ((conjKerEquiv A Γ h) v) =
      (conjKerEquiv A Γ hPS) (projSeqJ S P v) := fun v => Subtype.ext rfl
  have hPhi : ∀ w, projSeqPhi S' P' ((conjKerEquiv A Γ hPS) w) =
      (conjCokerEquiv Γ Γ hP) (projSeqPhi S P w) := fun w => by
    change Submodule.Quotient.mk (S' (A w)) = Submodule.Quotient.mk (Γ (S w))
    rw [h]
  have hPi : ∀ q, projSeqPi (T := S') gP'.isProj ((conjCokerEquiv Γ Γ hP) q) =
      (conjCokerEquiv A Γ h) (projSeqPi (T := S) gP.isProj q) := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      change Submodule.Quotient.mk (Γ y - P' (Γ y)) = Submodule.Quotient.mk (Γ (y - P y))
      rw [hP, map_sub]
  have hcc : ∀ q, (cokerCompEquiv gP').symm ((conjCokerEquiv Γ Γ hP) q) =
      (conjCokerEquiv A Γ hPS) ((cokerCompEquiv gP).symm q) := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H y => rfl
  have hb' : LinearIndependent ℝ (Fin.append (projSeqJ S' P' ∘ ((conjKerEquiv A Γ h) ∘ a))
      ((conjKerEquiv A Γ hPS) ∘ b)) := by
    have e : Fin.append (projSeqJ S' P' ∘ ((conjKerEquiv A Γ h) ∘ a))
        ((conjKerEquiv A Γ hPS) ∘ b) =
          (conjKerEquiv A Γ hPS) ∘ Fin.append (projSeqJ S P ∘ a) b := by
      rw [comp_append]
      rfl
    rw [e]
    exact hb.map' (conjKerEquiv A Γ hPS).toLinearMap (conjKerEquiv A Γ hPS).ker
  have hc' : ∀ i, projSeqPi (T := S') gP'.isProj (((conjCokerEquiv Γ Γ hP) ∘ c) i) =
      ((conjCokerEquiv A Γ h) ∘ d) i := fun i => by
    simp only [Function.comp_apply]
    rw [hPi, hc]
  have hw₀ : wedge a rfl ⊗ₜ[ℝ] dualVec (wedge d rfl) ≠ 0 :=
    tmul_ne_zero_of_ne_zero (wedge_basis_ne_zero _)
      (dualVec_ne_zero finrank_maxPow (wedge_basis_ne_zero _))
  have key : (((conjDet A Γ h).trans (gammaProj hS' gP') : fredholmDet S ≃ₗ[ℝ] _) :
      fredholmDet S →ₗ[ℝ] fredholmDet (P' ∘L S')) =
      (((gammaProj hS gP).trans (conjDet A Γ hPS) : fredholmDet S ≃ₗ[ℝ] _) :
        fredholmDet S →ₗ[ℝ] fredholmDet (P' ∘L S')) := by
    refine linearMap_ext_of_ne_zero (finrank_fredholmDet hS) hw₀ ?_
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
    rw [conjDet_wedge_tmul A Γ h (⇑a) rfl d.linearIndependent rfl]
    have ha' : LinearIndependent ℝ (⇑(conjKerEquiv A Γ h) ∘ ⇑a) :=
      a.linearIndependent.map' (conjKerEquiv A Γ h).toLinearMap (conjKerEquiv A Γ h).ker
    have hd' : LinearIndependent ℝ (⇑(conjCokerEquiv A Γ h) ∘ ⇑d) :=
      d.linearIndependent.map' (conjCokerEquiv A Γ h).toLinearMap (conjCokerEquiv A Γ h).ker
    have step := gammaProj_wedge_tmul hS' gP' ha' (conjKerEquiv A Γ h).finrank_eq hd'
      (conjCokerEquiv A Γ h).finrank_eq hb' (hj.trans (conjKerEquiv A Γ hPS).finrank_eq) hc'
      (hC.trans (conjCokerEquiv A Γ hPS).finrank_eq)
    have hd2 : LinearIndependent ℝ
        (⇑(cokerCompEquiv gP).symm ∘ Fin.append c (⇑(projSeqPhi S P) ∘ b)) :=
      hli.map' (cokerCompEquiv gP).symm.toLinearMap (cokerCompEquiv gP).symm.ker
    rw [step, gammaProj_wedge_tmul hS gP a.linearIndependent rfl d.linearIndependent rfl hb hj hc
      hC, conjDet_wedge_tmul A Γ hPS _ _ hd2]
    congr 1
    · apply wedge_eq_of_eq
      rw [comp_append]
      rfl
    · congr 1
      apply wedge_eq_of_eq
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Function.comp_apply, Fin.append_left]
        exact hcc (c i)
      · simp only [Function.comp_apply, Fin.append_right]
        rw [hPhi]
        exact hcc _
  exact LinearMap.congr_fun key x

/-- `conjDet` read on the fibres `DetFiber` of `DET`. -/
def conjDetFiber {S : FredholmOp E F} {S' : FredholmOp E' F'} (h : ∀ v, S'.1 (A v) = Γ (S.1 v)) :
    DetFiber S ≃ₗ[ℝ] DetFiber S' :=
  conjDet (S := S.1) (S' := S'.1) A Γ h

set_option maxHeartbeats 400000 in
-- The determinant isomorphisms of the conjugation unfold through several `maxPow` layers.
/-- **The coordinate change of a conjugation in two local determinant charts**: for charts `c` of
`DET(E, F)` and `c'` of `DET(E', F')` with `c'.P = Γ c.P Γ⁻¹`, and `S' ∘ A = Γ ∘ S` with `S`, `S'`
in the balls, `c'`-coordinate of `det(A, Γ)` of the `c`-frame vector `(γ^P_S)⁻¹ ω(S)` is
`det(kerProj' ∘ A ∘ kᵢ(S))` (in the basis `Module.finBasis` of `c'.K`) divided by a constant (the
determinant of `[Γ eᵢ]` for the basis `eᵢ` of `F / R(P)`). -/
theorem coord_conjDet_coordInv (c : LocalDetChart E F) (c' : LocalDetChart E' F')
    (hP : ∀ y, c'.P (Γ y) = Γ (c.P y)) (hk : finrank ℝ c'.K = finrank ℝ c.K)
    (hl : finrank ℝ (F' ⧸ LinearMap.range (c'.P : F' →ₗ[ℝ] F')) =
      finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)))
    {S : FredholmOp E F} {S' : FredholmOp E' F'} (h : ∀ v, S'.1 (A v) = Γ (S.1 v))
    (hS : ‖S.1 - c.T‖ < c.ε) (hS' : ‖S'.1 - c'.T‖ < c'.ε) :
    c'.coord S' (conjDetFiber A Γ h (c.coordInv S 1)) =
      ((Module.finBasis ℝ c'.K).reindex (finCongr hk)).det
          (fun i => c'.kerProj (A (c.kerMap S.1 (Module.finBasis ℝ c.K i)))) *
        (((Module.finBasis ℝ (F' ⧸ LinearMap.range (c'.P : F' →ₗ[ℝ] F'))).reindex
          (finCongr hl)).det (fun i => conjCokerEquiv Γ Γ hP
            (Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) i)))⁻¹ := by
  have g := c.isGoodLeftProj_of_lt S.1 hS
  have g' := c'.isGoodLeftProj_of_lt S'.1 hS'
  have := c'.finiteDimensional_coker S'.1 hS'
  have hPS := conj_comp A Γ hP h
  rw [c'.coord_apply hS', c.coordInv_apply hS]
  change dualVec (c'.frame S'.1 hS') (gammaProj S'.2 g' (conjDet A Γ h
    ((gammaProj S.2 g).symm ((1 : ℝ) • c.frame S.1 hS)))) = _
  rw [one_smul]
  have hω : c.frame S.1 hS = wedge (c.kerFrame S.1 hS) (c.kerEquiv S.1 hS).finrank_eq ⊗ₜ
      dualVec (wedge (c.cokerFrame S.1 hS) (cokerCompEquiv g).symm.finrank_eq) := rfl
  rw [gammaProj_conjDet A Γ hP h S.2 S'.2 g g', LinearEquiv.apply_symm_apply, hω,
    conjDet_wedge_tmul A Γ hPS _ _ (c.cokerFrame_linearIndependent S.1 hS)]
  have key := c'.linDetEquivOfEq_wedge_tmul S'.1 hS' (T₀ := ((c'.P ∘L S'.1 : E' →L[ℝ] F') :
      E' →ₗ[ℝ] F')) rfl (⇑(conjKerEquiv A Γ hPS) ∘ c.kerFrame S.1 hS)
    ((c.kerEquiv S.1 hS).finrank_eq.trans (conjKerEquiv A Γ hPS).finrank_eq)
    (⇑(conjCokerEquiv A Γ hPS) ∘ c.cokerFrame S.1 hS)
    ((cokerCompEquiv g).symm.finrank_eq.trans (conjCokerEquiv A Γ hPS).finrank_eq) hk hl
    g'.range_comp
  rw [linDetEquivOfEq_self, LinearEquiv.refl_apply] at key
  rw [key, map_smul, dualVec_self (finrank_fredholmDet (g'.isFredholm_comp S'.2))
    (c'.frame_ne_zero S'.1 hS'), smul_eq_mul, mul_one]
  have hq : ∀ q, Submodule.quotEquivOfEq _ _ g'.range_comp
      (conjCokerEquiv A Γ hPS ((cokerCompEquiv g).symm q)) = conjCokerEquiv Γ Γ hP q := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H y => rfl
  congr 2
  congr 1
  funext i
  exact hq _

/-- The coordinate change is linear: `c'(conj h) = c(h) · c'(conj (c⁻¹ 1))`. -/
theorem coord_conjDetFiber (c : LocalDetChart E F) (c' : LocalDetChart E' F')
    {S : FredholmOp E F} {S' : FredholmOp E' F'} (h : ∀ v, S'.1 (A v) = Γ (S.1 v))
    (hS : S ∈ c.baseSet) (x : DetFiber S) :
    c'.coord S' (conjDetFiber A Γ h x) =
      c.coord S x * c'.coord S' (conjDetFiber A Γ h (c.coordInv S 1)) := by
  have := LinearMap.map_smul ((c'.coord S') ∘ₗ (conjDetFiber A Γ h).toLinearMap ∘ₗ c.coordInv S)
    (c.coord S x) 1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, smul_eq_mul, mul_one,
    c.coordInv_coord hS] at this
  exact this

end ConjProj

/-! ### Conjugating an orientation of `DET` over a set of operators -/

section ConjOrientation

variable {E F E' F' E'' F'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [CompleteSpace E'']
  [NormedAddCommGroup F''] [NormedSpace ℝ F''] [CompleteSpace F'']
variable (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F')
  {C : Set (E →L[ℝ] F)} {hC : ∀ T ∈ C, T.IsFredholm}
  {C' : Set (E' →L[ℝ] F')} {hC' : ∀ T ∈ C', T.IsFredholm}

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `S' ↦ Γ⁻¹ S' A` is continuous. -/
theorem continuous_conjOp :
    Continuous fun S' : E' →L[ℝ] F' => (Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E') :=
  continuous_const.clm_comp (continuous_id.clm_comp continuous_const)

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- The map `C' → C`, `S' ↦ Γ⁻¹ S' A`. -/
def conjMap (hmem : ∀ S' ∈ C', ((Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E')) ∈ C) :
    C' → C :=
  fun S' => ⟨_, hmem S'.1 S'.2⟩

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `S' ↦ Γ⁻¹ S' A` is continuous on `C'`. -/
theorem continuous_conjMap
    (hmem : ∀ S' ∈ C', ((Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E')) ∈ C) :
    Continuous (conjMap A Γ hmem) :=
  ((continuous_conjOp A Γ).comp continuous_subtype_val).subtype_mk _

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `S'` and `Γ⁻¹ S' A` are conjugate. -/
theorem conjMap_spec
    (hmem : ∀ S' ∈ C', ((Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E')) ∈ C) (S' : C') :
    ∀ v, (fredholmIncl hC' S').1 (A v) = Γ ((fredholmIncl hC (conjMap A Γ hmem S')).1 v) :=
  fun _ => (Γ.apply_symm_apply _).symm

/-- The rays `S' ↦ conjDet (o (Γ⁻¹ S' A))` of `DET` over `C'`. -/
def conjRay (hmem : ∀ S' ∈ C', ((Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E')) ∈ C)
    (o : ∀ b, Module.Ray ℝ (DetOn C hC b)) (b : C') : Module.Ray ℝ (DetOn C' hC' b) :=
  Module.Ray.map (conjDetFiber A Γ (conjMap_spec (hC := hC) (hC' := hC') A Γ hmem b))
    (o (conjMap A Γ hmem b))

/-- The conjugated rays form an orientation: near `S'₀` the conjugated section of a local
section near `Γ⁻¹ S'₀ A` is continuous, read in a chart at `S'₀` with projection `Γ P Γ⁻¹`. -/
theorem isLineOrientation_conj
    (hmem : ∀ S' ∈ C', ((Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E')) ∈ C)
    (o : LineOrientation (DetOn C hC)) :
    IsLineOrientation (DetOn C' hC') (conjRay A Γ hmem o.1) := by
  intro b₀
  obtain ⟨U, hU, σ, hσc, hσ⟩ := o.2 (conjMap A Γ hmem b₀)
  obtain ⟨c, hc⟩ : ∃ c : LocalDetChart E F,
      c = localDetChartAt (fredholmIncl hC (conjMap A Γ hmem b₀)) := ⟨_, rfl⟩
  have hb : fredholmIncl hC (conjMap A Γ hmem b₀) ∈ c.baseSet :=
    hc ▸ mem_baseSet_localDetChartAt _
  have gP := c.isGoodLeftProj_of_lt (fredholmIncl hC (conjMap A Γ hmem b₀)).1 hb
  have hP' : ∀ y, ((Γ : F →L[ℝ] F') ∘L c.P ∘L (Γ.symm : F' →L[ℝ] F)) (Γ y) = Γ (c.P y) :=
    fun y => by simp
  obtain ⟨c', hc'T, hc'P⟩ := exists_localDetChart_of_proj (fredholmIncl hC' b₀).2
    (gP.conj A Γ hP' (conjMap_spec A Γ hmem b₀))
  have hP : ∀ y, c'.P (Γ y) = Γ (c.P y) := by rw [hc'P]; exact hP'
  have hb' : fredholmIncl hC' b₀ ∈ c'.baseSet := by
    change ‖_ - c'.T‖ < c'.ε
    rw [hc'T, sub_self, norm_zero]
    exact c'.ε_pos
  have hk : finrank ℝ c'.K = finrank ℝ c.K :=
    (c'.kerEquiv _ hb').finrank_eq.trans ((conjKerEquiv A Γ
      (conj_comp A Γ hP (conjMap_spec A Γ hmem b₀))).finrank_eq.symm.trans
        (c.kerEquiv _ hb).finrank_eq.symm)
  have hl : finrank ℝ (F' ⧸ LinearMap.range (c'.P : F' →ₗ[ℝ] F')) =
      finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) :=
    (conjCokerEquiv Γ Γ hP).finrank_eq.symm
  obtain ⟨e, -, he, hee⟩ := (proposition_6_5_8 (E := E) (F := F)).2 c
  obtain ⟨e', -, he', hee'⟩ := (proposition_6_5_8 (E := E') (F := F')).2 c'
  have hU' : conjMap A Γ hmem ⁻¹' (U ∩ fredholmIncl hC ⁻¹' c.baseSet) ∩
      fredholmIncl hC' ⁻¹' c'.baseSet ∈ 𝓝 b₀ := by
    refine Filter.inter_mem ((continuous_conjMap A Γ hmem).continuousAt.preimage_mem_nhds
      (Filter.inter_mem hU ?_)) ?_
    · exact (c.isOpen_baseSet.preimage (fredholmIncl hC).continuous).mem_nhds hb
    · exact (c'.isOpen_baseSet.preimage (fredholmIncl hC').continuous).mem_nhds hb'
  refine ⟨_, hU', fun b => conjDetFiber A Γ (conjMap_spec (hC := hC) (hC' := hC') A Γ hmem b)
    (σ (conjMap A Γ hmem b)), ?_, fun b hb => ?_⟩
  swap
  · obtain ⟨hne, hray⟩ := hσ _ hb.1.1
    refine ⟨(LinearEquiv.map_ne_zero_iff _).2 hne, ?_⟩
    change Module.Ray.map _ (o.1 _) = _
    rw [hray]
    rfl
  have hsrc : conjMap A Γ hmem ⁻¹' (U ∩ fredholmIncl hC ⁻¹' c.baseSet) ∩
      fredholmIncl hC' ⁻¹' c'.baseSet ⊆ (fun b : C' => (⟨fredholmIncl hC' b,
        conjDetFiber A Γ (conjMap_spec A Γ hmem b) (σ (conjMap A Γ hmem b))⟩ :
          TotalSpace ℝ (DetFiber (E := E') (F := F')))) ⁻¹' e'.source :=
    fun b hb => e'.mem_source.2 (by rw [he']; exact hb.2)
  have key : ContinuousOn (fun b : C' => (⟨fredholmIncl hC' b,
      conjDetFiber A Γ (conjMap_spec A Γ hmem b) (σ (conjMap A Γ hmem b))⟩ :
        TotalSpace ℝ (DetFiber (E := E') (F := F'))))
      (conjMap A Γ hmem ⁻¹' (U ∩ fredholmIncl hC ⁻¹' c.baseSet) ∩
        fredholmIncl hC' ⁻¹' c'.baseSet) := by
    refine (e'.toOpenPartialHomeomorph.continuousOn_iff_continuousOn_comp_left hsrc).2 ?_
    have h1 : ContinuousOn (fun b : C => (⟨fredholmIncl hC b, σ b⟩ :
        TotalSpace ℝ (DetFiber (E := E) (F := F)))) U :=
      (Pullback.continuous_lift ℝ _ _).comp_continuousOn hσc
    have h2 : ContinuousOn (fun b : C => e ⟨fredholmIncl hC b, σ b⟩)
        (U ∩ fredholmIncl hC ⁻¹' c.baseSet) :=
      e.continuousOn.comp (h1.mono inter_subset_left)
        (fun b hb => e.mem_source.2 (by rw [he]; exact hb.2))
    have h3 := (continuous_snd.comp_continuousOn h2).comp
      (continuous_conjMap A Γ hmem).continuousOn (fun b (hb : b ∈ conjMap A Γ hmem ⁻¹'
        (U ∩ fredholmIncl hC ⁻¹' c.baseSet) ∩ fredholmIncl hC' ⁻¹' c'.baseSet) => hb.1)
    have h4 : ContinuousOn (fun b : C' =>
        ((Module.finBasis ℝ c'.K).reindex (finCongr hk)).det
          (fun i => c'.kerProj (A (c.kerMap (fredholmIncl hC (conjMap A Γ hmem b)).1
            (Module.finBasis ℝ c.K i)))))
        (conjMap A Γ hmem ⁻¹' (U ∩ fredholmIncl hC ⁻¹' c.baseSet) ∩
          fredholmIncl hC' ⁻¹' c'.baseSet) := by
      refine (continuous_basis_det _).comp_continuousOn (continuousOn_pi.2 fun i =>
        c'.kerProj.continuous.comp_continuousOn (A.continuous.comp_continuousOn ?_))
      exact (c.continuousOn_kerMap_apply _).comp
        ((continuous_conjOp A Γ).comp continuous_subtype_val).continuousOn
        (fun b hb => hb.1.2)
    have he'φ : (e'.toOpenPartialHomeomorph ∘ fun b : C' => (⟨fredholmIncl hC' b,
        conjDetFiber A Γ (conjMap_spec A Γ hmem b) (σ (conjMap A Γ hmem b))⟩ :
          TotalSpace ℝ (DetFiber (E := E') (F := F')))) = fun b => (fredholmIncl hC' b,
            c'.coord (fredholmIncl hC' b)
              (conjDetFiber A Γ (conjMap_spec A Γ hmem b) (σ (conjMap A Γ hmem b)))) :=
      funext fun b => hee' _
    rw [he'φ]
    refine (fredholmIncl hC').continuous.continuousOn.prodMk
      ((h3.mul (h4.mul (continuousOn_const (c :=
        (((Module.finBasis ℝ (F' ⧸ LinearMap.range (c'.P : F' →ₗ[ℝ] F'))).reindex
          (finCongr hl)).det (fun i => conjCokerEquiv Γ Γ hP
            (Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) i)))⁻¹)))).congr
        fun b hb => ?_)
    change c'.coord _ _ = (e _).2 * _
    rw [hee]
    exact (coord_conjDetFiber A Γ c c' (conjMap_spec A Γ hmem b) hb.1.2 _).trans
      (congrArg (fun t => c.coord _ (σ (conjMap A Γ hmem b)) * t)
        (coord_conjDet_coordInv A Γ c c' hP hk hl (conjMap_spec A Γ hmem b) hb.1.2 hb.2))
  exact (inducing_pullbackTotalSpaceEmbedding ℝ _ _).continuousOn_iff.2
    (continuousOn_id.prodMk key)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F] in
/-- A linear automorphism acting as the identity fixes every ray. -/
theorem ray_map_eq_self {M : Type*} [AddCommMonoid M] [Module ℝ M] (e : M ≃ₗ[ℝ] M)
    (h : ∀ x, e x = x) (r : Module.Ray ℝ M) : Module.Ray.map e r = r := by
  rw [show e = LinearEquiv.refl ℝ M from LinearEquiv.ext h, Module.Ray.map_refl]
  rfl

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F] in
/-- `Ray.map` of a composite. -/
theorem ray_map_map {M N K : Type*} [AddCommMonoid M] [Module ℝ M] [AddCommMonoid N]
    [Module ℝ N] [AddCommMonoid K] [Module ℝ K] (e : M ≃ₗ[ℝ] N) (e' : N ≃ₗ[ℝ] K)
    (r : Module.Ray ℝ M) :
    Module.Ray.map e' (Module.Ray.map e r) = Module.Ray.map (e ≪≫ₗ e') r := by
  induction r using Module.Ray.ind with
  | h v hv => rfl

/-- **Conjugating an orientation.** For isomorphisms `A : E ≅ E'`, `Γ : F ≅ F'` with
`Γ⁻¹ S' A ∈ C` for every `S' ∈ C'`, an orientation `o` of `DET` over `C` gives the orientation
`S' ↦ conjDet (o (Γ⁻¹ S' A))` of `DET` over `C'`. -/
def LineOrientation.conj
    (hmem : ∀ S' ∈ C', ((Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E')) ∈ C)
    (o : LineOrientation (DetOn C hC)) : LineOrientation (DetOn C' hC') :=
  ⟨conjRay A Γ hmem o.1, isLineOrientation_conj A Γ hmem o⟩

/-- `o.conj` at `S'` is `conjDet` of `o` at any `S` conjugate to `S'` (which is `Γ⁻¹ S' A`). -/
theorem LineOrientation.conj_apply_of_conj
    (hmem : ∀ S' ∈ C', ((Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E')) ∈ C)
    (o : LineOrientation (DetOn C hC)) (b : C) (b' : C')
    (h : ∀ v, (fredholmIncl hC' b').1 (A v) = Γ ((fredholmIncl hC b).1 v)) :
    o.conj A Γ hmem b' = Module.Ray.map (conjDetFiber A Γ h) (o b) := by
  obtain rfl : b = conjMap A Γ hmem b' := Subtype.ext (ContinuousLinearMap.ext fun v => by
    change b.1 v = Γ.symm (b'.1 (A v))
    rw [show b'.1 (A v) = Γ (b.1 v) from h v, ContinuousLinearEquiv.symm_apply_apply])
  rfl

/-- `o.conj` at `S'` is `conjDet` of `o` at `S` whenever `S' A = Γ S`. -/
theorem LineOrientation.conj_apply
    (hmem : ∀ S' ∈ C', ((Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E')) ∈ C)
    (o : LineOrientation (DetOn C hC)) {S : E →L[ℝ] F} (hS : S ∈ C) {S' : E' →L[ℝ] F'}
    (hS' : S' ∈ C') (h : ∀ v, S' (A v) = Γ (S v)) :
    o.conj (hC' := hC') A Γ hmem ⟨S', hS'⟩ = Module.Ray.map (conjDet A Γ h) (o ⟨S, hS⟩) :=
  o.conj_apply_of_conj A Γ hmem ⟨S, hS⟩ ⟨S', hS'⟩ h

/-- Conjugating by the identities does nothing. -/
theorem LineOrientation.conj_refl
    (hmem : ∀ S' ∈ C, (((ContinuousLinearEquiv.refl ℝ F).symm : F →L[ℝ] F) ∘L S' ∘L
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E)) ∈ C)
    (o : LineOrientation (DetOn C hC)) :
    o.conj (ContinuousLinearEquiv.refl ℝ E) (ContinuousLinearEquiv.refl ℝ F) hmem = o := by
  refine Subtype.ext (funext fun b => ?_)
  change o.conj _ _ hmem b = o b
  have h : ∀ v, (fredholmIncl hC b).1 (ContinuousLinearEquiv.refl ℝ E v) =
      ContinuousLinearEquiv.refl ℝ F ((fredholmIncl hC b).1 v) := fun _ => rfl
  rw [o.conj_apply_of_conj _ _ hmem b b h]
  exact ray_map_eq_self _ (fun x => (DFunLike.congr_fun (conjDet_refl h) x).trans
    (DFunLike.congr_fun (linDetEquivOfEq_self _ _) x)) _

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] [CompleteSpace E'']
  [CompleteSpace F''] in
/-- `Γ⁻¹ C' A ⊆ C` and `Γ'⁻¹ C'' A' ⊆ C'` give `(Γ Γ')⁻¹ C'' (A A') ⊆ C`. -/
theorem conj_mem_trans (A' : E' ≃L[ℝ] E'') (Γ' : F' ≃L[ℝ] F'') {C'' : Set (E'' →L[ℝ] F'')}
    (hmem : ∀ S' ∈ C', ((Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E')) ∈ C)
    (hmem' : ∀ S'' ∈ C'', ((Γ'.symm : F'' →L[ℝ] F') ∘L S'' ∘L (A' : E' →L[ℝ] E'')) ∈ C') :
    ∀ S'' ∈ C'', (((Γ.trans Γ').symm : F'' →L[ℝ] F) ∘L S'' ∘L
      ((A.trans A' : E ≃L[ℝ] E'') : E →L[ℝ] E'')) ∈ C := fun S'' hS'' => by
  convert hmem _ (hmem' S'' hS'') using 1
  exact ContinuousLinearMap.ext fun _ => rfl

/-- Conjugating twice is conjugating by the composites. -/
theorem LineOrientation.conj_trans (A' : E' ≃L[ℝ] E'') (Γ' : F' ≃L[ℝ] F'')
    {C'' : Set (E'' →L[ℝ] F'')} {hC'' : ∀ T ∈ C'', T.IsFredholm}
    (hmem : ∀ S' ∈ C', ((Γ.symm : F' →L[ℝ] F) ∘L S' ∘L (A : E →L[ℝ] E')) ∈ C)
    (hmem' : ∀ S'' ∈ C'', ((Γ'.symm : F'' →L[ℝ] F') ∘L S'' ∘L (A' : E' →L[ℝ] E'')) ∈ C')
    (hmem'' : ∀ S'' ∈ C'', (((Γ.trans Γ').symm : F'' →L[ℝ] F) ∘L S'' ∘L
      ((A.trans A' : E ≃L[ℝ] E'') : E →L[ℝ] E'')) ∈ C)
    (o : LineOrientation (DetOn C hC)) :
    (o.conj (hC' := hC') A Γ hmem).conj (hC' := hC'') A' Γ' hmem' =
      o.conj (A.trans A') (Γ.trans Γ') hmem'' := by
  refine Subtype.ext (funext fun b => ?_)
  change (o.conj A Γ hmem).conj A' Γ' hmem' b = o.conj (A.trans A') (Γ.trans Γ') hmem'' b
  have h₁ := conjMap_spec (hC := hC') (hC' := hC'') A' Γ' hmem' b
  have h₂ := conjMap_spec (hC := hC) (hC' := hC') A Γ hmem (conjMap A' Γ' hmem' b)
  have h₃ : ∀ v, (fredholmIncl hC'' b).1 ((A.trans A') v) = (Γ.trans Γ')
      ((fredholmIncl hC (conjMap A Γ hmem (conjMap A' Γ' hmem' b))).1 v) := fun v => by
    rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply, ← h₂, h₁]
  rw [LineOrientation.conj_apply_of_conj A' Γ' hmem' _ _ b h₁,
    LineOrientation.conj_apply_of_conj A Γ hmem o _ _ h₂,
    LineOrientation.conj_apply_of_conj (A.trans A') (Γ.trans Γ') hmem'' o _ b h₃]
  exact (ray_map_map _ _ _).trans (congrArg (fun e => Module.Ray.map e _)
    (LinearEquiv.ext fun x => DFunLike.congr_fun (conjDet_trans A Γ A' Γ' h₂ h₁ h₃) x))

/-- Conjugation depends only on the maps `A` and `Γ`. -/
theorem LineOrientation.conj_congr {A₁ A₂ : E ≃L[ℝ] E'} {Γ₁ Γ₂ : F ≃L[ℝ] F'}
    (hA : ∀ v, A₁ v = A₂ v) (hΓ : ∀ y, Γ₁ y = Γ₂ y)
    (hmem₁ : ∀ S' ∈ C', ((Γ₁.symm : F' →L[ℝ] F) ∘L S' ∘L (A₁ : E →L[ℝ] E')) ∈ C)
    (hmem₂ : ∀ S' ∈ C', ((Γ₂.symm : F' →L[ℝ] F) ∘L S' ∘L (A₂ : E →L[ℝ] E')) ∈ C)
    (o : LineOrientation (DetOn C hC)) :
    o.conj (hC' := hC') A₁ Γ₁ hmem₁ = o.conj A₂ Γ₂ hmem₂ := by
  obtain rfl : A₁ = A₂ := ContinuousLinearEquiv.ext (funext hA)
  obtain rfl : Γ₁ = Γ₂ := ContinuousLinearEquiv.ext (funext hΓ)
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- Every set of operators is closed under conjugation by the identities. -/
theorem conj_mem_refl (D : Set (E →L[ℝ] F)) :
    ∀ S ∈ D, (((ContinuousLinearEquiv.refl ℝ F).symm : F →L[ℝ] F) ∘L S ∘L
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E)) ∈ D :=
  fun _ hS => hS

end ConjOrientation

/-! ### Chart points at the same point -/

universe u v

open StrongRetr

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

namespace ChartPoint

variable {x : X} (p p' p'' : ChartPoint B x)

/-! ### The base transition at `z` -/

/-- An open `W` with `φ(V ∩ V') = O ∩ W` (`MChart.exists_isOpen_image_eq`). -/
def overlapW : Set (p.c.φ.model.E 0) :=
  (p.c.φ.exists_isOpen_image_eq (s := p.c.φ.source ∩ p'.c.φ.source) inter_subset_left
    (p.c.φ.isOpen_source.inter p'.c.φ.isOpen_source)).choose

theorem isOpen_overlapW : IsOpen (p.overlapW p') :=
  (p.c.φ.exists_isOpen_image_eq (s := p.c.φ.source ∩ p'.c.φ.source) inter_subset_left
    (p.c.φ.isOpen_source.inter p'.c.φ.isOpen_source)).choose_spec.1

theorem overlap_eq : p.c.φ.overlap p'.c.φ = p.c.φ.model.O ∩ p.overlapW p' :=
  (p.c.φ.exists_isOpen_image_eq (s := p.c.φ.source ∩ p'.c.φ.source) inter_subset_left
    (p.c.φ.isOpen_source.inter p'.c.φ.isOpen_source)).choose_spec.2

/-- The base retraction `r` restricted to `U ∩ r⁻¹(W)`, a retraction onto `φ(V ∩ V')`. -/
def baseRet : ScRetraction p.c.φ.model.E p.c.φ.model.C :=
  (p.c.isRetraction.baseRetraction p.c.relOpen).restrict (p.isOpen_overlapW p')

theorem baseRet_apply (u : p.c.φ.model.E 0) : p.baseRet p' u = r p.c.R u := rfl

theorem baseRet_U_subset : (p.baseRet p').U ⊆ p.c.U := inter_subset_left

theorem baseRet_retract : (p.baseRet p').retract = p.c.φ.overlap p'.c.φ := by
  rw [baseRet, ScRetraction.restrict_retract, p.c.base_retract]
  exact (p.overlap_eq p').symm

theorem toBase_z_mem_overlap : p.c.φ.model.E.toBase 1 p.z ∈ p.c.φ.overlap p'.c.φ := by
  rw [p.toBase_z]
  exact p.c.φ.mem_overlap p'.c.φ p.mem_source p'.mem_source

theorem z_mem_baseRet : p.z ∈ p.c.φ.model.E.lvlSet (p.baseRet p').U 1 :=
  (p.baseRet p').lvlSet_retract_subset 1 (by
    rw [ScBanach.mem_lvlSet, baseRet_retract]; exact p.toBase_z_mem_overlap p')

theorem toBase_z_mem_O : p.c.φ.model.E.toBase 1 p.z ∈ p.c.φ.model.O := by
  rw [p.toBase_z]; exact p.c.φ.mapsTo_model x p.mem_source

theorem r_toBase_z : r p.c.R (p.c.φ.model.E.toBase 1 p.z) = p.c.φ.model.E.toBase 1 p.z :=
  r_eq_self p.c.isRetraction p.mem_O

theorem transition_toBase_z :
    p.c.φ.transition p'.c.φ (p.c.φ.model.E.toBase 1 p.z) = p'.c.φ.model.E.toBase 1 p'.z := by
  rw [p.toBase_z, p.c.φ.transition_apply p'.c.φ p.mem_source, p'.toBase_z]

/-- `τ ∘ r_W` is sc¹ on `U ∩ r⁻¹(W)` (the base charts are compatible). -/
theorem isSc1_transition :
    IsSc1 (p.baseRet p').U (p.c.φ.transition p'.c.φ ∘ p.baseRet p') :=
  ((p.c.isChart.compatible p'.c.isChart (P := PX)).1.comp_isScSmooth _
    (p.baseRet_retract p')).isSc1

theorem levelMap_transition :
    levelMap (p.c.φ.transition p'.c.φ ∘ p.baseRet p') 1 p.z = p'.z := by
  apply levelMap_eq_of_toBase_eq
  change p'.c.φ.model.E.toBase 1 p'.z =
    p.c.φ.transition p'.c.φ (r p.c.R (p.c.φ.model.E.toBase 1 p.z))
  rw [p.r_toBase_z, p.transition_toBase_z p']

/-- The points of `r_W(U ∩ r⁻¹(W))` are the points `φ(y)`, `y ∈ V ∩ V'`. -/
theorem exists_eq_of_mem_baseRet {u : p.c.φ.model.E 0} (hu : u ∈ (p.baseRet p').U) :
    ∃ y, y ∈ p.c.φ.source ∧ y ∈ p'.c.φ.source ∧ r p.c.R u = p.c.φ y := by
  have h := (p.baseRet p').apply_mem_retract hu
  rw [baseRet_retract] at h
  obtain ⟨y, ⟨hy, hy'⟩, hyu⟩ := h
  exact ⟨y, hy, hy', hyu.symm⟩

/-- **`a = D(τ ∘ r)(z)`**: the derivative at `z` of the base transition `τ = φ' ∘ φ⁻¹` (composed
with the retraction `r_W` onto `φ(V ∩ V')`). -/
def baseDeriv : p.c.φ.model.E 0 →L[ℝ] p'.c.φ.model.E 0 :=
  scDeriv (p.baseRet p').U (p.c.φ.transition p'.c.φ ∘ p.baseRet p') p.z

/-- **`D(φ ∘ φ⁻¹ ∘ r)(z) = Dr(z)`.** -/
theorem baseDeriv_self (v : p.c.φ.model.E 0) :
    p.baseDeriv p v = scDeriv p.c.U (r p.c.R) p.z v := by
  have hr1 : IsSc1 p.c.U (r p.c.R) := (r_isScSmooth p.c.relOpen p.c.isRetraction).isSc1
  refine congrArg (fun L : p.c.φ.model.E 0 →L[ℝ] p.c.φ.model.E 0 => L v)
    (scDeriv_eq_of_eqOn_relOpen (p.baseRet p).relOpen (p.isSc1_transition p) hr1 subset_rfl
      (p.baseRet_U_subset p) (fun u hu => ?_) (p.z_mem_baseRet p))
  obtain ⟨y, hy, -, hyu⟩ := p.exists_eq_of_mem_baseRet p hu
  change p.c.φ.transition p.c.φ (r p.c.R u) = r p.c.R u
  rw [hyu, p.c.φ.transition_apply p.c.φ hy]

/-- **The chain rule for the base transitions** at `z`: `D(τ'' ∘ r)(z) = D(τ' ∘ r')(z') ∘
D(τ ∘ r)(z)` for `τ = φ' ∘ φ⁻¹`, `τ' = φ'' ∘ φ'⁻¹`, `τ'' = φ'' ∘ φ⁻¹` (on the triple overlap
`τ' ∘ r' ∘ τ ∘ r = τ'' ∘ r`). -/
theorem baseDeriv_trans (v : p.c.φ.model.E 0) :
    p.baseDeriv p'' v = p'.baseDeriv p'' (p.baseDeriv p' v) := by
  set R₁ := p.baseRet p'
  set R₂ := p'.baseRet p''
  set R₃ := p.baseRet p''
  set R₁₃ := R₁.restrict (p.isOpen_overlapW p'')
  have hV₁ : R₁₃.U ⊆ R₁.U := inter_subset_left
  have hV₃ : R₁₃.U ⊆ R₃.U := fun u hu => ⟨(p.baseRet_U_subset p') hu.1, hu.2⟩
  have hzV : p.z ∈ p.c.φ.model.E.lvlSet R₁₃.U 1 :=
    ⟨p.z_mem_baseRet p', (p.z_mem_baseRet p'').2⟩
  -- the three points over `r u`
  have hpts : ∀ u ∈ R₁₃.U, ∃ y, y ∈ p.c.φ.source ∧ y ∈ p'.c.φ.source ∧ y ∈ p''.c.φ.source ∧
      r p.c.R u = p.c.φ y := by
    intro u hu
    obtain ⟨y, hy, hy', hyu⟩ := p.exists_eq_of_mem_baseRet p' (hV₁ hu)
    obtain ⟨y', hy₁, hy'', hyu'⟩ := p.exists_eq_of_mem_baseRet p'' (hV₃ hu)
    have : y = y' := by
      rw [← p.c.φ.symm_apply_apply hy, ← p.c.φ.symm_apply_apply hy₁, ← hyu, ← hyu']
    subst this
    exact ⟨y, hy, hy', hy'', hyu⟩
  have hf := p.isSc1_transition p'
  have hg := p'.isSc1_transition p''
  have hh := p.isSc1_transition p''
  have hmaps : MapsTo (p.c.φ.transition p'.c.φ ∘ R₁) R₁₃.U R₂.U := by
    intro u hu
    obtain ⟨y, hy, hy', hy'', hyu⟩ := hpts u hu
    refine R₂.retract_subset ?_
    rw [baseRet_retract]
    change p.c.φ.transition p'.c.φ (r p.c.R u) ∈ _
    rw [hyu, p.c.φ.transition_apply p'.c.φ hy]
    exact p'.c.φ.mem_overlap p''.c.φ hy' hy''
  have heq : EqOn ((p'.c.φ.transition p''.c.φ ∘ R₂) ∘ (p.c.φ.transition p'.c.φ ∘ R₁))
      (p.c.φ.transition p''.c.φ ∘ R₃) R₁₃.U := by
    intro u hu
    obtain ⟨y, hy, hy', hy'', hyu⟩ := hpts u hu
    have hR₂ : R₂ (p'.c.φ y) = p'.c.φ y := R₂.apply_eq_self_of_mem_retract (by
      rw [baseRet_retract]; exact p'.c.φ.mem_overlap p''.c.φ hy' hy'')
    change p'.c.φ.transition p''.c.φ (R₂ (p.c.φ.transition p'.c.φ (r p.c.R u))) =
      p.c.φ.transition p''.c.φ (r p.c.R u)
    rw [hyu, p.c.φ.transition_apply p'.c.φ hy, hR₂, p'.c.φ.transition_apply p''.c.φ hy',
      p.c.φ.transition_apply p''.c.φ hy]
  have hfV := hf.of_subset hV₁
  have hgf := (theorem_1_3_1' R₁₃.isScDomain R₂.isScDomain hfV hg hmaps).1
  have h1 := scDeriv_comp_apply' R₁₃.relOpen R₂.relOpen hfV hg hmaps hzV v
  rw [p.levelMap_transition p'] at h1
  have h2 : scDeriv R₁₃.U (p.c.φ.transition p'.c.φ ∘ R₁) p.z = p.baseDeriv p' :=
    scDeriv_eq_of_eqOn_relOpen R₁₃.relOpen hfV hf subset_rfl hV₁ (fun _ _ => rfl) hzV
  have h3 : scDeriv R₁₃.U ((p'.c.φ.transition p''.c.φ ∘ R₂) ∘ (p.c.φ.transition p'.c.φ ∘ R₁))
      p.z = p.baseDeriv p'' :=
    scDeriv_eq_of_eqOn_relOpen R₁₃.relOpen hgf hh subset_rfl hV₃ heq hzV
  rw [h2, h3] at h1
  exact h1.symm

/-- `D(τ ∘ r)(z)` takes values in `T_{z'}O'` (it is `Dr'(z') ∘ D(τ ∘ r)(z)`). -/
theorem baseDeriv_mem_T (v : p.c.φ.model.E 0) : p.baseDeriv p' v ∈ p'.T := by
  rw [p.baseDeriv_trans p' p' v, p'.baseDeriv_self]
  exact ⟨_, rfl⟩

/-- `D(τ' ∘ r')(z') ∘ D(τ ∘ r)(z) = id` on `T_zO`. -/
theorem baseDeriv_baseDeriv {v : p.c.φ.model.E 0} (hv : v ∈ p.T) :
    p'.baseDeriv p (p.baseDeriv p' v) = v := by
  rw [← p.baseDeriv_trans p' p v, p.baseDeriv_self]
  obtain ⟨w, rfl⟩ := hv
  exact scDeriv_r_idem_at p.c.relOpen p.c.isRetraction p.mem_O w

/-- `D(τ ∘ r)(z)` is an sc-operator at a smooth point (Proposition 1.2.1 (preprint 1.16)'s remark). -/
theorem isScOperator_baseDeriv (hx : x ∈ PX.smoothSet) : IsScOperator (p.baseDeriv p') :=
  (p.isSc1_transition p').isSc1With_scDeriv.scOperator_deriv (p.z_mem_baseRet p')
    (p.z_mem_smoothLvl hx)

/-! ### The fibre transition at `z` -/

theorem symm_toBase_z_mem_source :
    p.c.φ.symm (p.c.φ.model.E.toBase 1 p.z) ∈ p'.c.φ.source := by
  rw [p.toBase_z, p.c.φ.symm_apply_apply p.mem_source]; exact p'.mem_source

/-- **`Γ = (Φ' ∘ Φ⁻¹)(z, ·)`**: the fibre part at `z` of the strong bundle transition
(`StrongBundleChart.transitionFiberCLM`, precomposed with `ρ(z)`). -/
def fiberMap : p.c.F 0 →L[ℝ] p'.c.F 0 :=
  p.c.transitionFiberCLM p'.c p.toBase_z_mem_O (p.symm_toBase_z_mem_source p')

theorem fiberMap_apply (k : p.c.F 0) : p.fiberMap p' k =
    (p.c.transition p'.c (p.c.φ.model.E.toBase 1 p.z, ρ p.c.R (p.c.φ.model.E.toBase 1 p.z) k)).2 :=
  rfl

theorem mem_K_of_mem {k : p.c.F 0} (hk : k ∈ p.K) : (p.c.φ.model.E.toBase 1 p.z, k) ∈ p.c.K := by
  obtain ⟨k₀, rfl⟩ := hk
  exact p.c.mem_K_ρ p.toBase_z_mem_O k₀

theorem transition_eq {k : p.c.F 0} (hk : (p.c.φ.model.E.toBase 1 p.z, k) ∈ p.c.K) :
    p.c.transition p'.c (p.c.φ.model.E.toBase 1 p.z, k) =
      (p'.c.φ.model.E.toBase 1 p'.z, (p.c.transition p'.c (p.c.φ.model.E.toBase 1 p.z, k)).2) := by
  refine Prod.ext ?_ rfl
  rw [p.c.transition_fst p'.c hk (p.symm_toBase_z_mem_source p')]
  exact p.transition_toBase_z p'

theorem fiberMap_apply_of_mem {k : p.c.F 0} (hk : k ∈ p.K) :
    p.fiberMap p' k = (p.c.transition p'.c (p.c.φ.model.E.toBase 1 p.z, k)).2 :=
  p.c.transitionFiberCLM_apply_of_mem p'.c _ _ (p.mem_K_of_mem hk)

theorem fiberMap_mem_K {k : p.c.F 0} (hk : k ∈ p.K) : p.fiberMap p' k ∈ p'.K := by
  have hK : (p'.c.φ.model.E.toBase 1 p'.z, p.fiberMap p' k) ∈ p'.c.K := by
    rw [p.fiberMap_apply_of_mem p' hk, ← p.transition_eq p' (p.mem_K_of_mem hk)]
    exact p.c.transition_mem_K p'.c (p.mem_K_of_mem hk) (p.symm_toBase_z_mem_source p')
  exact ⟨p.fiberMap p' k, ρ_eq_self_of_mem_K p'.c.isRetraction p'.mem_U hK⟩

/-- `(Φ ∘ Φ⁻¹)(z, ·) = id` on `K_z`. -/
theorem fiberMap_self {k : p.c.F 0} (hk : k ∈ p.K) : p.fiberMap p k = k := by
  rw [p.fiberMap_apply_of_mem p hk]
  change (p.c (p.c.toPartialEquiv.symm (p.c.φ.model.E.toBase 1 p.z, k))).2 = k
  rw [p.c.apply_symm (p.mem_K_of_mem hk)]

/-- **The cocycle identity for the fibre transitions** at `z` on `K_z`:
`(Φ'' ∘ Φ⁻¹)(z, ·) = (Φ'' ∘ Φ'⁻¹)(z', ·) ∘ (Φ' ∘ Φ⁻¹)(z, ·)`. -/
theorem fiberMap_trans {k : p.c.F 0} (hk : k ∈ p.K) :
    p.fiberMap p'' k = p'.fiberMap p'' (p.fiberMap p' k) := by
  have hK := p.mem_K_of_mem hk
  rw [p.fiberMap_apply_of_mem p'' hk, p'.fiberMap_apply_of_mem p'' (p.fiberMap_mem_K p' hk),
    p.fiberMap_apply_of_mem p' hk, ← p.transition_eq p' hK]
  change (p''.c (p.c.toPartialEquiv.symm (p.c.φ.model.E.toBase 1 p.z, k))).2 =
    (p''.c (p'.c.toPartialEquiv.symm
      (p'.c (p.c.toPartialEquiv.symm (p.c.φ.model.E.toBase 1 p.z, k))))).2
  rw [p'.c.toPartialEquiv.left_inv (p'.c.mem_source_of_proj (by
    rw [p.c.proj_symm hK]; exact p.symm_toBase_z_mem_source p'))]

/-! ### The identifications `T_zO ≅ T_{z'}O'` and `K_z ≅ K'_{z'}` -/

/-- **`T_xX` read in `p` and in `p'`**: `D(τ ∘ r)(z) : T_zO ≅ T_{z'}O'`. -/
def transferT : ↥p.T ≃L[ℝ] ↥p'.T :=
  restrictEquiv p.T p'.T (p.baseDeriv p') (p'.baseDeriv p) (fun v _ => p.baseDeriv_mem_T p' v)
    (fun w _ => p'.baseDeriv_mem_T p w) (fun _ hv => p.baseDeriv_baseDeriv p' hv)
    (fun _ hw => p'.baseDeriv_baseDeriv p hw)

/-- **`Y_x` read in `p` and in `p'`**: `Γ : K_z ≅ K'_{z'}`. -/
def transferK : ↥p.K ≃L[ℝ] ↥p'.K :=
  restrictEquiv p.K p'.K (p.fiberMap p') (p'.fiberMap p) (fun _ hk => p.fiberMap_mem_K p' hk)
    (fun _ hk => p'.fiberMap_mem_K p hk)
    (fun _ hk => by rw [← p.fiberMap_trans p' p hk, p.fiberMap_self hk])
    (fun _ hk => by rw [← p'.fiberMap_trans p p' hk, p'.fiberMap_self hk])

@[simp] theorem coe_transferT_apply (v : ↥p.T) :
    (p.transferT p' v : p'.c.φ.model.E 0) = p.baseDeriv p' v := rfl

@[simp] theorem coe_transferK_apply (k : ↥p.K) :
    (p.transferK p' k : p'.c.F 0) = p.fiberMap p' k := rfl

theorem transferT_symm_apply (w : ↥p'.T) : (p.transferT p').symm w = p'.transferT p w := rfl

theorem transferK_symm_apply (k : ↥p'.K) : (p.transferK p').symm k = p'.transferK p k := rfl

theorem transferT_self_apply (v : ↥p.T) : p.transferT p v = v :=
  Subtype.ext (by
    rw [coe_transferT_apply, baseDeriv_self]
    obtain ⟨w, hw⟩ := v.2
    rw [← hw]
    exact scDeriv_r_idem_at p.c.relOpen p.c.isRetraction p.mem_O w)

theorem transferK_self_apply (k : ↥p.K) : p.transferK p k = k :=
  Subtype.ext (p.fiberMap_self k.2)

theorem transferT_trans_apply (v : ↥p.T) :
    p'.transferT p'' (p.transferT p' v) = p.transferT p'' v :=
  Subtype.ext (p.baseDeriv_trans p' p'' v).symm

theorem transferK_trans_apply (k : ↥p.K) :
    p'.transferK p'' (p.transferK p' k) = p.transferK p'' k :=
  Subtype.ext (p.fiberMap_trans p' p'' k.2).symm

/-! ### The bundle transition near `z` -/

/-- The bundle retraction `R` restricted to `R⁻¹(W × F)`, a retraction onto `Φ(P⁻¹(V ∩ V'))`. -/
def bundleRet : ScRetraction (p.c.φ.model.E.prod p.c.F) (p.c.φ.model.C ×ˢ univ) :=
  (p.c.isRetraction.toScRetraction p.c.relOpen).restrict ((p.isOpen_overlapW p').prod isOpen_univ)

theorem bundleRet_retract : (p.bundleRet p').retract = p.c.overlap p'.c := by
  rw [bundleRet, ScRetraction.restrict_retract]
  exact (p.c.overlap_eq_inter_prod p'.c (p.overlap_eq p')).symm

/-- `Φ' ∘ Φ⁻¹ ∘ R` is sc-smooth near the fibre over `z` (the bundle charts are compatible). -/
theorem isScSmooth_bundleTransition :
    IsScSmooth (F := p'.c.φ.model.E.prod p'.c.F) (p.bundleRet p').U
      (p.c.transition p'.c ∘ p.bundleRet p') :=
  (StrongBundle.IsChart.transition_isScSmoothRetractMap p.isChart p'.isChart).comp_isScSmooth _
    (p.bundleRet_retract p')

theorem R_toBase_z (k : p.c.F 0) :
    p.c.R (p.c.φ.model.E.toBase 1 p.z, k) =
      (p.c.φ.model.E.toBase 1 p.z, ρ p.c.R (p.c.φ.model.E.toBase 1 p.z) k) := by
  rw [apply_eq p.c.isRetraction p.mem_U, p.r_toBase_z]

theorem toBase_z_mem_overlapW : p.c.φ.model.E.toBase 1 p.z ∈ p.overlapW p' := by
  have : p.c.φ.model.E.toBase 1 p.z ∈ p.c.φ.model.O ∩ p.overlapW p' := by
    rw [← p.overlap_eq p']; exact p.toBase_z_mem_overlap p'
  exact this.2

theorem mem_bundleRet (k : p.c.F 0) :
    ((p.c.φ.model.E.toBase 1 p.z, k) : (p.c.φ.model.E.prod p.c.F) 0) ∈ (p.bundleRet p').U :=
  ⟨⟨p.mem_U, mem_univ _⟩, by
    change p.c.R (p.c.φ.model.E.toBase 1 p.z, k) ∈ p.overlapW p' ×ˢ univ
    rw [p.R_toBase_z]; exact ⟨p.toBase_z_mem_overlapW p', mem_univ _⟩⟩

theorem bundleTransition_apply (k : p.c.F 0) :
    ((p.c.transition p'.c ∘ p.bundleRet p') (p.c.φ.model.E.toBase 1 p.z, k)).2 =
      p.fiberMap p' k := by
  change (p.c.transition p'.c (p.c.R (p.c.φ.model.E.toBase 1 p.z, k))).2 = _
  rw [p.R_toBase_z]
  rfl

/-- **`Γ` is an sc-operator** at a smooth point: `Φ' ∘ Φ⁻¹ ∘ R` is sc⁰ on `[0]`, so it maps
`(z, F_m)` to level `m` (copied from `linAt_chart_change_sc`). -/
theorem isScOperator_fiberMap (hx : x ∈ PX.smoothSet) : IsScOperator (p.fiberMap p') := by
  refine isScOperator_of_mapsTo fun m k => ?_
  obtain ⟨zm, hzm⟩ := (p.c.φ.model.E.mem_smoothLvl_iff).1 (p.z_mem_smoothLvl hx) m
  have hpm : (p.c.φ.model.E.prod p.c.F).toBase m ((zm, k) : (p.c.φ.model.E.prod p.c.F) m) =
      ((p.c.φ.model.E.toBase 1 p.z, p.c.F.toBase m k) : (p.c.φ.model.E.prod p.c.F) 0) := by
    rw [ScBanach.prod_toBase, hzm]
  have hq : ((zm, k) : (p.c.φ.model.E.prod p.c.F) m) ∈
      (p.c.φ.model.E.prod p.c.F).lvlSet (p.bundleRet p').U m := by
    rw [ScBanach.mem_lvlSet, hpm]; exact p.mem_bundleRet p' _
  obtain ⟨q, hq⟩ := (p.isScSmooth_bundleTransition p').isSc1.isSc0.mem_range m _ hq
  rw [hpm] at hq
  have h2 := congrArg Prod.snd hq
  rw [ScBanach.prod_toBase] at h2
  exact ⟨q.2, by rw [← p.bundleTransition_apply p']; exact h2⟩

/-! ### The linearizations in `p` and `p'` -/

/-- **The linearizations of a section in two chart points are conjugate**: at a zero `x` of an
sc-smooth section `g`, `D(ĝ' ∘ r')(z') ∘ D(τ ∘ r)(z) = Γ ∘ D(ĝ ∘ r)(z)` (the identity `key` of
`linAt_chart_change_sc`, for the canonical `D(τ ∘ r)(z)` and `Γ`). -/
theorem scDeriv_principal_baseDeriv {g : X → Y} (hg : B.IsScSmoothSection g)
    (hx0 : IsZeroAt P g x) (v : p.c.φ.model.E 0) :
    scDeriv p'.c.U (p'.c.principal g ∘ r p'.c.R) p'.z (p.baseDeriv p' v) =
      p.fiberMap p' (scDeriv p.c.U (p.c.principal g ∘ r p.c.R) p.z v) := by
  have hf : IsSection P g := hg.1
  have hz1 : p.z ∈ p.c.φ.model.E.lvlSet (p.baseRet p').U 1 := p.z_mem_baseRet p'
  have hRwU : (p.baseRet p').U ⊆ p.c.U := p.baseRet_U_subset p'
  have hr1 : IsSc1 p.c.U (r p.c.R) := (r_isScSmooth p.c.relOpen p.c.isRetraction).isSc1
  have hfr : IsSc1 p.c.U (p.c.principal g ∘ r p.c.R) := hg.isSc1_principal_comp_r p.isChart
  have hfr' : IsSc1 p'.c.U (p'.c.principal g ∘ r p'.c.R) := hg.isSc1_principal_comp_r p'.isChart
  have hrRw : IsSc1 (p.baseRet p').U (r p.c.R) := hr1.of_subset hRwU
  have hfrRw : IsSc1 (p.baseRet p').U (p.c.principal g ∘ r p.c.R) := hfr.of_subset hRwU
  have hDfr : scDeriv (p.baseRet p').U (p.c.principal g ∘ r p.c.R) p.z =
      scDeriv p.c.U (p.c.principal g ∘ r p.c.R) p.z :=
    scDeriv_eq_of_eqOn_relOpen (p.baseRet p').relOpen hfrRw hfr subset_rfl hRwU
      (fun _ _ => rfl) hz1
  set RK := p.bundleRet p' with hRKdef
  set Φ : (p.c.φ.model.E.prod p.c.F) 0 → p'.c.F 0 :=
    fun q => ((p.c.transition p'.c ∘ RK) q).2 with hΦdef
  have hΦ : IsSc1 RK.U Φ := ((p.isScSmooth_bundleTransition p').snd RK.isScDomain).isSc1
  have hSD : ∀ u ∈ (p.baseRet p').U, ((u, 0) : (p.c.φ.model.E.prod p.c.F) 0) ∈ RK.U :=
    fun u hu => ⟨⟨hu.1, mem_univ _⟩, ⟨hu.2, mem_univ _⟩⟩
  have hzero : ∀ u ∈ (p.baseRet p').U, Φ (u, 0) = 0 := by
    intro u hu
    have hru : r p.c.R u ∈ p.c.φ.overlap p'.c.φ := by
      rw [← p.baseRet_retract p']; exact (p.baseRet p').apply_mem_retract hu
    have hR0 : p.c.R (u, 0) = (r p.c.R u, 0) := by
      rw [apply_eq p.c.isRetraction hu.1, (ρ_isLinear p.c.isRetraction hu.1).map_zero]
    have hK0 : (r p.c.R u, (0 : p.c.F 0)) ∈ p.c.K := by
      rw [← hR0]; exact ⟨(u, 0), ⟨hu.1, mem_univ _⟩, rfl⟩
    change (p.c.transition p'.c (p.c.R (u, 0))).2 = 0
    rw [hR0]
    exact p.c.transition_snd_zero p'.c hK0 (p.c.φ.symm_mem_of_mem_overlap p'.c.φ hru)
  set σ := scPair (r p.c.R) (p.c.principal g ∘ r p.c.R) with hσdef
  have hσmem : ∀ u ∈ (p.baseRet p').U, ∃ y₁, y₁ ∈ p.c.φ.source ∧ y₁ ∈ p'.c.φ.source ∧
      r p.c.R u = p.c.φ y₁ ∧ σ u = p.c (g y₁) ∧ σ u ∈ RK.retract := by
    intro u hu
    obtain ⟨y₁, hy₁, hy₁', hy₁u⟩ := p.exists_eq_of_mem_baseRet p' hu
    have hσu : σ u = p.c (g y₁) := by
      change (r p.c.R u, p.c.principal g (r p.c.R u)) = p.c (g y₁)
      rw [hy₁u, p.c.apply_section' hf hy₁]
    refine ⟨y₁, hy₁, hy₁', hy₁u, hσu, ?_⟩
    rw [hRKdef, p.bundleRet_retract p', hσu]
    exact ⟨g y₁, ⟨p.c.mem_source_of_proj (by rw [hf]; exact hy₁),
      p'.c.mem_source_of_proj (by rw [hf]; exact hy₁')⟩, rfl⟩
  have hmapsσ : MapsTo σ (p.baseRet p').U RK.U := fun u hu => by
    obtain ⟨-, -, -, -, -, h⟩ := hσmem u hu
    exact RK.retract_subset h
  have hσ1 : IsSc1 (p.baseRet p').U σ := hrRw.scPair' hfrRw
  have hEq : EqOn ((p'.c.principal g ∘ r p'.c.R) ∘ (p.c.φ.transition p'.c.φ ∘ p.baseRet p'))
      (Φ ∘ σ) (p.baseRet p').U := by
    intro u hu
    obtain ⟨y₁, hy₁, hy₁', hru, hσu, hσK⟩ := hσmem u hu
    have hτu : p.c.φ.transition p'.c.φ (r p.c.R u) = p'.c.φ y₁ := by
      rw [hru, p.c.φ.transition_apply p'.c.φ hy₁]
    have hr' : r p'.c.R (p'.c.φ y₁) = p'.c.φ y₁ :=
      r_eq_self p'.c.isRetraction (by rw [p'.c.r_image]; exact p'.c.φ.mapsTo_model y₁ hy₁')
    change p'.c.principal g (r p'.c.R (p.c.φ.transition p'.c.φ (r p.c.R u))) =
      (p.c.transition p'.c (RK (σ u))).2
    rw [RK.apply_eq_self_of_mem_retract hσK, hσu]
    change _ = (p'.c (p.c.toPartialEquiv.symm (p.c (g y₁)))).2
    rw [p.c.toPartialEquiv.left_inv (p.c.mem_source_of_proj (by rw [hf]; exact hy₁)),
      p'.c.apply_section' hf hy₁', hτu, hr']
  have hmapsτ : MapsTo (p.c.φ.transition p'.c.φ ∘ p.baseRet p') (p.baseRet p').U p'.c.U :=
    fun u hu => by
      obtain ⟨y₁, hy₁, hy₁', hru⟩ := p.exists_eq_of_mem_baseRet p' hu
      change p.c.φ.transition p'.c.φ (r p.c.R u) ∈ p'.c.U
      rw [hru, p.c.φ.transition_apply p'.c.φ hy₁]
      exact mem_U_of_mem_O p'.c.isRetraction
        (by rw [p'.c.r_image]; exact p'.c.φ.mapsTo_model y₁ hy₁')
  have hτ1 := p.isSc1_transition p'
  have hℓ : IsSc1 (p.baseRet p').U
      ((p'.c.principal g ∘ r p'.c.R) ∘ (p.c.φ.transition p'.c.φ ∘ p.baseRet p')) :=
    (theorem_1_3_1' (p.baseRet p').isScDomain p'.c.relOpen.isScDomain hτ1 hfr' hmapsτ).1
  have hΦσ : IsSc1 (p.baseRet p').U (Φ ∘ σ) :=
    (theorem_1_3_1' (p.baseRet p').isScDomain RK.isScDomain hσ1 hΦ hmapsσ).1
  have hDeq : scDeriv (p.baseRet p').U
      ((p'.c.principal g ∘ r p'.c.R) ∘ (p.c.φ.transition p'.c.φ ∘ p.baseRet p')) p.z =
        scDeriv (p.baseRet p').U (Φ ∘ σ) p.z :=
    scDeriv_eq_of_eqOn_relOpen (p.baseRet p').relOpen hℓ hΦσ subset_rfl subset_rfl hEq hz1
  have hfz : p.c.principal g (p.c.φ.model.E.toBase 1 p.z) = 0 := by
    rw [p.toBase_z]; exact (p.c.isZeroAt_iff hf p.mem_source).1 hx0
  have hlevσ : levelMap σ 1 p.z = ((p.z, 0) : (p.c.φ.model.E.prod p.c.F) 1) := by
    apply levelMap_eq_of_toBase_eq
    rw [ScBanach.prod_toBase, map_zero]
    change ((p.c.φ.model.E.toBase 1 p.z, (0 : p.c.F 0)) : (p.c.φ.model.E.prod p.c.F) 0) =
      (r p.c.R (p.c.φ.model.E.toBase 1 p.z),
        p.c.principal g (r p.c.R (p.c.φ.model.E.toBase 1 p.z)))
    rw [p.r_toBase_z, hfz]
  have hΓ : ∀ k, Φ (p.c.φ.model.E.toBase 1 p.z, k) = p.fiberMap p' k :=
    p.bundleTransition_apply p'
  have h1 := scDeriv_comp_apply' (p.baseRet p').relOpen p'.c.relOpen hτ1 hfr' hmapsτ hz1 v
  rw [p.levelMap_transition p'] at h1
  have h2 := scDeriv_comp_apply' (p.baseRet p').relOpen RK.relOpen hσ1 hΦ hmapsσ hz1 v
  rw [hlevσ, hσdef, scDeriv_scPair (p.baseRet p').relOpen hrRw hfrRw hz1,
    ContinuousLinearMap.prod_apply,
    scDeriv_fiber_of_vanishing (p.baseRet p').relOpen hΦ hz1 hSD (p.mem_bundleRet p') hzero
      (p.fiberMap p') hΓ] at h2
  change scDeriv p'.c.U _ p'.z
    (scDeriv (p.baseRet p').U (p.c.φ.transition p'.c.φ ∘ p.baseRet p') p.z v) = _
  rw [h1, hDeq, ← h2, hDfr]

variable {p p'} in
/-- **Conjugation preserves sc⁺-operators** at a smooth point: for an sc⁺-operator
`a : T_zO → K_z`, `Γ ∘ a ∘ A⁻¹ : T_{z'}O' → K'_{z'}` is one (`A⁻¹ = D(τ' ∘ r')(z')` and `Γ` are
sc-operators, `isScOperator_baseDeriv`, `isScOperator_fiberMap`). -/
theorem IsScPlusOp.conj (hx : x ∈ PX.smoothSet) {a : ↥p.T →L[ℝ] ↥p.K} (ha : p.IsScPlusOp a) :
    p'.IsScPlusOp ((p.transferK p' : ↥p.K →L[ℝ] ↥p'.K) ∘L a ∘L
      (p'.transferT p : ↥p'.T →L[ℝ] ↥p.T)) := by
  obtain ⟨hT, hK, S, hS⟩ := ha
  have hT' := p'.isScSubspace_T hx
  have hK' := p'.isScSubspace_K hx
  have hA := p'.isScOperator_baseDeriv p hx
  have hΓ := p.isScOperator_fiberMap p' hx
  let aop := hA.toScOperator.restrict hT' hT (fun v _ => by
    rw [hA.toScOperator_zero]; exact p'.baseDeriv_mem_T p v)
  let γop := hΓ.toScOperator.restrict hK hK' (fun k hk => by
    rw [hΓ.toScOperator_zero]; exact p.fiberMap_mem_K p' hk)
  refine ⟨hT', hK', γop.shift.comp (S.comp aop), fun v => ?_⟩
  have h1 := hS (aop 0 v)
  have h2 := hΓ.toScOperator.incl_comm 0 (S 0 (aop 0 v)).1
  have h3 : (⟨(aop 0 v).1, (aop 0 v).2⟩ : ↥p.T) = p'.transferT p ⟨v.1, v.2⟩ :=
    Subtype.ext (by
      change hA.toScOperator 0 v.1 = p'.baseDeriv p v.1
      rw [hA.toScOperator_zero])
  change p'.c.F.incl 0 (hΓ.toScOperator 1 (S 0 (aop 0 v)).1) =
    p.fiberMap p' (a (p'.transferT p ⟨v.1, v.2⟩) : p.c.F 0)
  rw [h2, hΓ.toScOperator_zero]
  exact congrArg (p.fiberMap p') (h1.trans (congrArg (fun t => (a t : p.c.F 0)) h3))

/-- **Conjugation maps `Lin(f, x)` in `p` into `Lin(f, x)` in `p'`** at a smooth point: for
`L = (f + s)'(x) + a`, `Γ ∘ L ∘ A⁻¹ = (f + s)'(x) + Γ ∘ a ∘ A⁻¹` in `p'`
(`scDeriv_principal_baseDeriv`, `IsScPlusOp.conj`). -/
theorem conj_mem_linSet (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) :
    ((p.transferK p' : ↥p.K →L[ℝ] ↥p'.K) ∘L L ∘L (p'.transferT p : ↥p'.T →L[ℝ] ↥p.T)) ∈
      p'.linSet f := by
  obtain ⟨s, hs, hz, a, ha, hLa⟩ := hL
  have hg : B.IsScSmoothSection (sectionAdd P f s) := hf.isScSmooth.sectionAdd hs
  refine ⟨s, hs, hz, _, ha.conj hx, fun w => ?_⟩
  change p.fiberMap p' (L (p'.transferT p w) : p.c.F 0) =
    scDeriv p'.c.U (p'.c.principal (sectionAdd P f s) ∘ r p'.c.R) p'.z w +
      p.fiberMap p' (a (p'.transferT p w) : p.c.F 0)
  rw [hLa, map_add, linAt_apply, ← p.scDeriv_principal_baseDeriv p' hg hz, coe_transferT_apply,
    p'.baseDeriv_baseDeriv p w.2]

/-- **`Lin(f, x)` in `p'` is the conjugate of `Lin(f, x)` in `p`**:
`L ∈ Lin_p(f, x) ↔ Γ ∘ L ∘ A⁻¹ ∈ Lin_{p'}(f, x)`. -/
theorem mem_linSet_transfer_iff (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    (L : ↥p.T →L[ℝ] ↥p.K) :
    L ∈ p.linSet f ↔ ((p.transferK p' : ↥p.K →L[ℝ] ↥p'.K) ∘L L ∘L
      ((p.transferT p').symm : ↥p'.T →L[ℝ] ↥p.T)) ∈ p'.linSet f := by
  refine ⟨fun hL => p.conj_mem_linSet p' hf hx hL, fun hL => ?_⟩
  convert p'.conj_mem_linSet p hf hx hL using 1
  refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
  change (L v : p.c.F 0) = (p'.transferK p (p.transferK p' (L (p'.transferT p
    (p.transferT p' v)))) : p.c.F 0)
  rw [transferK_trans_apply, transferK_self_apply, transferT_trans_apply, transferT_self_apply]

/-- The hypothesis of `LineOrientation.conj` for `A`, `Γ`: `Γ⁻¹ ∘ L' ∘ A ∈ Lin_p(f, x)` for
`L' ∈ Lin_{p'}(f, x)`. -/
theorem transfer_mem_linSet (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet) :
    ∀ L' ∈ p'.linSet f, (((p.transferK p').symm : ↥p'.K →L[ℝ] ↥p.K) ∘L L' ∘L
      (p.transferT p' : ↥p.T →L[ℝ] ↥p'.T)) ∈ p.linSet f :=
  fun _ hL' => p'.conj_mem_linSet p hf hx hL'

/-! ### Transferring orientations: `Or_x^f` in `p` and in `p'` -/

/-- `Γ L A⁻¹` is conjugate to `L`: `(Γ L A⁻¹)(A v) = Γ(L v)`. -/
theorem transfer_conj_apply (L : ↥p.T →L[ℝ] ↥p.K) (v : ↥p.T) :
    ((p.transferK p' : ↥p.K →L[ℝ] ↥p'.K) ∘L L ∘L (p'.transferT p : ↥p'.T →L[ℝ] ↥p.T))
      (p.transferT p' v) = p.transferK p' (L v) := by
  change p.transferK p' (L (p'.transferT p (p.transferT p' v))) = _
  rw [transferT_trans_apply, transferT_self_apply]

/-- Transferring from `p` to `p'` and back is the identity. -/
theorem conj_transfer_transfer (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    (o : p.Or f hf) :
    (o.conj (hC' := p'.isFredholm_of_mem_linSet hf) (p.transferT p') (p.transferK p')
      (p.transfer_mem_linSet p' hf hx)).conj (hC' := p.isFredholm_of_mem_linSet hf)
        (p'.transferT p) (p'.transferK p) (p'.transfer_mem_linSet p hf hx) = o :=
  (LineOrientation.conj_trans (hC' := p'.isFredholm_of_mem_linSet hf)
    (hC'' := p.isFredholm_of_mem_linSet hf) _ _ _ _ (p.transfer_mem_linSet p' hf hx)
    (p'.transfer_mem_linSet p hf hx)
    (conj_mem_trans _ _ _ _ (p.transfer_mem_linSet p' hf hx) (p'.transfer_mem_linSet p hf hx))
    o).trans
  ((LineOrientation.conj_congr (hC' := p.isFredholm_of_mem_linSet hf)
    (A₁ := (p.transferT p').trans (p'.transferT p)) (A₂ := ContinuousLinearEquiv.refl ℝ ↥p.T)
    (Γ₁ := (p.transferK p').trans (p'.transferK p)) (Γ₂ := ContinuousLinearEquiv.refl ℝ ↥p.K)
    (fun v => (p.transferT_trans_apply p' p v).trans (p.transferT_self_apply v))
    (fun k => (p.transferK_trans_apply p' p k).trans (p.transferK_self_apply k)) _
    (conj_mem_refl _) o).trans (LineOrientation.conj_refl _ o))

/-- **The canonical identification of `Or_x^f` read in `p` and in `p'`** at a smooth point: `o`
goes to `L' ↦ conjDet(o(Γ⁻¹ L' A))` (`LineOrientation.conj` for `A = transferT p p'`,
`Γ = transferK p p'`); the inverse is the transfer from `p'` to `p`. -/
def orTransfer (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet) :
    p.Or f hf ≃ p'.Or f hf where
  toFun o := o.conj (hC' := p'.isFredholm_of_mem_linSet hf) (p.transferT p') (p.transferK p')
    (p.transfer_mem_linSet p' hf hx)
  invFun o := o.conj (hC' := p.isFredholm_of_mem_linSet hf) (p'.transferT p) (p'.transferK p)
    (p'.transfer_mem_linSet p hf hx)
  left_inv o := p.conj_transfer_transfer p' hf hx o
  right_inv o := p'.conj_transfer_transfer p hf hx o

/-- **The defining property of `orTransfer`**: its value at `Γ L A⁻¹` is the image of the value
at `L` under `conjDet A Γ : det(L) ≅ det(Γ L A⁻¹)`. -/
theorem orTransfer_apply (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet) (o : p.Or f hf)
    {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) :
    p.orTransfer p' hf hx o ⟨_, p.conj_mem_linSet p' hf hx hL⟩ =
      Module.Ray.map (conjDet (p.transferT p') (p.transferK p') (p.transfer_conj_apply p' L))
        (o ⟨L, hL⟩) :=
  LineOrientation.conj_apply (hC' := p'.isFredholm_of_mem_linSet hf) _ _ _ o hL _ _

/-- `orTransfer` from `p` to itself is the identity. -/
theorem orTransfer_self (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet) :
    p.orTransfer p hf hx = Equiv.refl _ :=
  Equiv.ext fun o => (LineOrientation.conj_congr (hC' := p.isFredholm_of_mem_linSet hf)
    (A₁ := p.transferT p) (A₂ := ContinuousLinearEquiv.refl ℝ ↥p.T)
    (Γ₁ := p.transferK p) (Γ₂ := ContinuousLinearEquiv.refl ℝ ↥p.K)
    p.transferT_self_apply p.transferK_self_apply _ (conj_mem_refl _) o).trans
      (LineOrientation.conj_refl _ o)

/-- **The cocycle identity**: transferring from `p` to `p'` and then to `p''` is transferring
from `p` to `p''`. -/
theorem orTransfer_trans (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet) :
    (p.orTransfer p' hf hx).trans (p'.orTransfer p'' hf hx) = p.orTransfer p'' hf hx :=
  Equiv.ext fun o => (LineOrientation.conj_trans (hC' := p'.isFredholm_of_mem_linSet hf)
    (hC'' := p''.isFredholm_of_mem_linSet hf) _ _ _ _ (p.transfer_mem_linSet p' hf hx)
    (p'.transfer_mem_linSet p'' hf hx)
    (conj_mem_trans _ _ _ _ (p.transfer_mem_linSet p' hf hx) (p'.transfer_mem_linSet p'' hf hx))
    o).trans
    (LineOrientation.conj_congr (hC' := p''.isFredholm_of_mem_linSet hf)
      (A₁ := (p.transferT p').trans (p'.transferT p'')) (A₂ := p.transferT p'')
      (Γ₁ := (p.transferK p').trans (p'.transferK p'')) (Γ₂ := p.transferK p'')
      (p.transferT_trans_apply p' p'') (p.transferK_trans_apply p' p'') _
      (p.transfer_mem_linSet p'' hf hx) o)

end ChartPoint

end Polyfold
