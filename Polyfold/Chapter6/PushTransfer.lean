import Polyfold.Chapter6.PropagationWellDefined
import Polyfold.Chapter6.ChartTransfer

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 222–228: the local propagation `o ↦ φ_* o` and **Theorem 6.6.13 (preprint 6.37)** (the functor `Γ_f`, whose
objects `Or_x^f` do not refer to a chart) *(book 2017: Theorem 6.2; see `BookConcordance.md`)*.

# The local push-forward does not depend on the chart

## The text, paraphrased

Along an sc-smooth path `φ` the push-forward `o₁ = φ_* o₀` is made from the kernels
`L_t = ker F_t'(φ(t), 0)`, the isomorphisms `Φ_{E_t}` of the exact sequences (96) and the
continuation of orientations of `λ(L_t)`.  In the proof of Theorem 6.6.13 (preprint 6.37) an orientation of
`DET(f, φ(t))` is carried along a finite covering of `[0, 1]` by orientable neighbourhoods; the
objects `Or_x^f` are the same for all of them.

## What is formalized

* Conjugation of stabilizations, for isomorphisms `A : E ≅ E'`, `Γ : F ≅ F'` with `T' A = Γ T`
  and `φ' = Γ φ`: `stabSign_conj` (`α(T') = α(T)`), `coprod_conj`, `ker_coprod_conj`
  (`ker(T' ⊕ φ') = (A × 1) ker(T ⊕ φ)`), `surjective_coprod_conj`, and **the naturality of the
  stabilization isomorphism** `stabRayEquiv_conjDet` (with `conj_stab_key`, from
  Proposition 6.4.15 (preprint 6.15) at both operators): `Φ_{E'} ∘ conjDet(A, Γ) = λ(M) ∘ Φ_E` on rays, for
  identifications of the kernels compatible with `A × 1` and `M`; the regroupings
  `ray_trans_conj_aux`, `equiv_conj_push_aux`.
* `SubspaceFamily.cont_map`: **continuation is natural** under a jointly continuous family of
  linear maps injective on the members (`isLineOrientation_map`).
* For chart points `p`, `p'` at `x`: `ChartPoint.fiberMap_principal` (the principal parts of a
  section are related by `Γ`), `ChartPoint.conj_of_linAt`, `ChartPoint.conj_of_principal` (the
  stabilized operators of the two charts are conjugate), `ChartPoint.baseDeriv_chartPt_eq`, and
  `continuous_baseDeriv` (along a continuous level-`1` lift, `(q, v) ↦ D(τ ∘ r)(z_q) v` is
  jointly continuous, from the sc⁰ tangent map of `τ ∘ r_W`).
* `IsStabKernels.exists_transfer`: a family of stabilized kernels in a chart `c` is carried by
  `D(τ ∘ r)(z_q) × 1` to one in a second chart `c'` (same sections); `IsStabKernels.orRay_transfer`:
  the orientations read in `λ(Λ_q)` correspond under `orTransfer`.
* **`IsPush.transfer`**: a push-forward along `γ` in the chart `c`, conjugated by `orTransfer` at
  the end points, is a push-forward along `γ` in the chart `c'`; and
  `HasLocalPropagation.push_compat`: for two neighbourhoods with the local propagation property in
  two charts, the push-forwards along a path in both correspond under `orTransfer`.

## Reading

`Or_x^f` is chart-free in the text; here it is made in a chart point (`LinOrientation.lean`) and
the two readings are identified by `ChartPoint.orTransfer` (`ChartTransfer.lean`).  The
propagation in two charts is compared through `orTransfer` at the end points: the sections `S`,
`s₁, …, s_k` are kept and only the family of kernels changes, by the derivative of the base
transition.  The comparison needs the joint continuity of `(t, v) ↦ D(τ ∘ r)(z_t) v`, for which
the path is assumed sc-smooth (as in the text).
-/

open Module TensorProduct Bundle Topology Set Filter

noncomputable section

namespace Polyfold

/-! ### Conjugate stabilizations -/

section ConjStab

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F') {T : E →L[ℝ] F} {T' : E' →L[ℝ] F'} {k : ℕ}
  {φ : (Fin k → ℝ) →L[ℝ] F} {φ' : (Fin k → ℝ) →L[ℝ] F'}

/-- **The sign `α` is invariant under conjugation**: `dim coker T' = dim coker T` for
`T' A = Γ T`. -/
theorem stabSign_conj (h : ∀ v, T' (A v) = Γ (T v)) : stabSign T' = stabSign T := by
  rw [stabSign, stabSign, ← (conjCokerEquiv A Γ h).finrank_eq]

/-- **Conjugate stabilizations**: `(T' ⊕ φ') ∘ (A × 1) = Γ ∘ (T ⊕ φ)` for `T' A = Γ T` and
`φ' = Γ φ`. -/
theorem coprod_conj (h : ∀ v, T' (A v) = Γ (T v)) (hφφ : ∀ μ, φ' μ = Γ (φ μ))
    (w : E × (Fin k → ℝ)) :
    (T'.coprod φ') ((A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin k → ℝ))) w) =
      Γ ((T.coprod φ) w) := by
  obtain ⟨v, μ⟩ := w
  rw [ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.coprod_apply, map_add, h, hφφ]
  rfl

/-- **The kernels of conjugate stabilizations**: `ker(T' ⊕ φ') = (A × 1) ker(T ⊕ φ)`. -/
theorem ker_coprod_conj (h : ∀ v, T' (A v) = Γ (T v)) (hφφ : ∀ μ, φ' μ = Γ (φ μ)) :
    LinearMap.ker ((T'.coprod φ' : E' × (Fin k → ℝ) →L[ℝ] F') : E' × (Fin k → ℝ) →ₗ[ℝ] F') =
      (LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)).map
        (((A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin k → ℝ)) :
          (E × (Fin k → ℝ)) ≃L[ℝ] (E' × (Fin k → ℝ))) :
            E × (Fin k → ℝ) →L[ℝ] E' × (Fin k → ℝ)) :
              E × (Fin k → ℝ) →ₗ[ℝ] E' × (Fin k → ℝ)) := by
  ext w
  constructor
  · intro hw
    refine ⟨(A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin k → ℝ))).symm w, ?_,
      (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin k → ℝ))).apply_symm_apply w⟩
    have hw' : (T'.coprod φ') w = 0 := hw
    change (T.coprod φ) _ = 0
    apply Γ.injective
    rw [← coprod_conj A Γ h hφφ, ContinuousLinearEquiv.apply_symm_apply, hw', map_zero]
  · rintro ⟨u, hu, rfl⟩
    have hu' : (T.coprod φ) u = 0 := hu
    change (T'.coprod φ') ((A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin k → ℝ))) u) = 0
    rw [coprod_conj A Γ h hφφ, hu', map_zero]

/-- A conjugate of a surjective stabilization is surjective. -/
theorem surjective_coprod_conj (h : ∀ v, T' (A v) = Γ (T v)) (hφφ : ∀ μ, φ' μ = Γ (φ μ))
    (hφ : Function.Surjective (T.coprod φ)) : Function.Surjective (T'.coprod φ') := fun y' => by
  obtain ⟨u, hu⟩ := hφ (Γ.symm y')
  exact ⟨A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin k → ℝ)) u, by
    rw [coprod_conj A Γ h hφφ, hu, ContinuousLinearEquiv.apply_symm_apply]⟩

/-- **The naturality of the stabilization isomorphism, as linear maps**: for identifications
`ι : ker(T ⊕ φ) ≅ L`, `ι' : ker(T' ⊕ φ') ≅ L'` and `M : L ≅ L'` with `ι' (A × 1) = M ι`,
`λ(ι') ∘ (det(T' ⊕ φ') ≅ λ) ∘ ι_{φ'} ∘ conjDet(A, Γ) = λ(M) ∘ λ(ι) ∘ (det(T ⊕ φ) ≅ λ) ∘ ι_φ`
(Proposition 6.4.15 (preprint 6.15) at `T` and at `T'`, with the data `a`, `c̄`, `b̄` and `A a`, `c̄`, `(A × 1) b̄`;
the determinant in (94) is the same). -/
theorem conj_stab_key (h : ∀ v, T' (A v) = Γ (T v)) (hφφ : ∀ μ, φ' μ = Γ (φ μ))
    (hT : T.IsFredholm) (hT' : T'.IsFredholm)
    (hφ : Function.Surjective (T.coprod φ)) (hφ' : Function.Surjective (T'.coprod φ'))
    {W W' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W']
    {L : Submodule ℝ W} {L' : Submodule ℝ W'} [FiniteDimensional ℝ L] [FiniteDimensional ℝ L']
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] L)
    (ι' : LinearMap.ker ((T'.coprod φ' : E' × (Fin k → ℝ) →L[ℝ] F') :
      E' × (Fin k → ℝ) →ₗ[ℝ] F') ≃ₗ[ℝ] L')
    (M : L ≃ₗ[ℝ] L')
    (hM : ∀ v, ι' (conjKerEquiv (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin k → ℝ))) Γ
      (coprod_conj A Γ h hφφ) v) = M (ι v)) :
    ((maxPowEquiv ι').toLinearMap ∘ₗ (detEquivOfSurjective hφ').toLinearMap ∘ₗ
      stabIota hT' hφ' ∘ₗ (conjDet A Γ h).toLinearMap) =
      ((maxPowEquiv M).toLinearMap ∘ₗ (maxPowEquiv ι).toLinearMap ∘ₗ
        (detEquivOfSurjective hφ).toLinearMap ∘ₗ stabIota hT hφ) := by
  classical
  have := hT.finite_ker
  have := hT'.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have : FiniteDimensional ℝ (F' ⧸ LinearMap.range (T' : E' →ₗ[ℝ] F')) := hT'.finite_coker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  have := finiteDimensional_ker_coprod (T := T') (φ := φ')
  let N := conjKerEquiv (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin k → ℝ))) Γ
    (coprod_conj A Γ h hφφ)
  let K := conjKerEquiv A Γ h
  let C := conjCokerEquiv A Γ h
  obtain ⟨cbar, hd⟩ := exists_stabClass_linearIndependent hT hφ
  let a := Module.finBasis ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))
  obtain ⟨l, bbar, hb, hkl⟩ := exists_stabJ_completion (φ := φ) hT a
  have hn := stab_card_eq hT hφ rfl hkl
  let a' := a.map K
  have hcl : stabClass T' φ' ∘ cbar = C ∘ (stabClass T φ ∘ cbar) := funext fun i => by
    change Submodule.Quotient.mk (φ' (cbar i)) = C (Submodule.Quotient.mk (φ (cbar i)))
    rw [conjCokerEquiv_mk, hφφ]
  have hd' : LinearIndependent ℝ (stabClass T' φ' ∘ cbar) := by
    rw [hcl]; exact hd.map' C.toLinearMap C.ker
  have hm' : finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) =
      finrank ℝ (F' ⧸ LinearMap.range (T' : E' →ₗ[ℝ] F')) := C.finrank_eq
  have hJ : stabJ T' φ' ∘ ⇑a' = N ∘ (stabJ T φ ∘ ⇑a) := funext fun i => Subtype.ext (by
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, coe_stabJ,
      Basis.map_apply]
    change ((K (a i) : E'), (0 : Fin k → ℝ)) = (A (a i : E), 0)
    rfl)
  have hb' : LinearIndependent ℝ (Fin.append (stabJ T' φ' ∘ ⇑a') (N ∘ bbar)) := by
    rw [hJ, ← comp_append]; exact hb.map' N.toLinearMap N.ker
  have hkl' := hkl.trans N.finrank_eq
  have h615 := proposition_6_4_15 hT hφ a cbar hd rfl bbar hb hkl hn
  have h615' := proposition_6_4_15 hT' hφ' a' cbar hd' hm' (N ∘ bbar) hb' hkl' hn
  have e1 : conjDet A Γ h (wedge a (by rw [Module.finrank_eq_card_basis a, Fintype.card_fin]) ⊗ₜ
      dualVec (wedge (stabClass T φ ∘ cbar) rfl)) =
      wedge a' (by rw [Module.finrank_eq_card_basis a', Fintype.card_fin]) ⊗ₜ
        dualVec (wedge (stabClass T' φ' ∘ cbar) hm') := by
    rw [conjDet_wedge_tmul A Γ h a _ hd rfl]
    exact congrArg₂ (fun x y => x ⊗ₜ[ℝ] dualVec y)
      (wedge_congr_fun (Basis.coe_map a K).symm _ _) (wedge_congr_fun hcl.symm _ _)
  have hdet : (Pi.basisFun ℝ (Fin k)).det (Fin.append cbar
      (fun i => (((N ∘ bbar) i : E' × (Fin k → ℝ))).2) ∘ Fin.cast hn.symm) =
      (Pi.basisFun ℝ (Fin k)).det (Fin.append cbar
        (fun i => ((bbar i : E × (Fin k → ℝ))).2) ∘ Fin.cast hn.symm) := rfl
  have hfin : ⇑ι' ∘ Fin.append (stabJ T' φ' ∘ ⇑a') (N ∘ bbar) =
      ⇑M ∘ ⇑ι ∘ Fin.append (stabJ T φ ∘ ⇑a) bbar := by
    rw [hJ, ← comp_append]
    funext i
    exact hM _
  have hgen : maxPowEquiv ι' (detEquivOfSurjective hφ' (stabIota hT' hφ' (conjDet A Γ h
      (wedge a (by rw [Module.finrank_eq_card_basis a, Fintype.card_fin]) ⊗ₜ
        dualVec (wedge (stabClass T φ ∘ cbar) rfl))))) =
      maxPowEquiv M (maxPowEquiv ι (detEquivOfSurjective hφ (stabIota hT hφ
        (wedge a (by rw [Module.finrank_eq_card_basis a, Fintype.card_fin]) ⊗ₜ
          dualVec (wedge (stabClass T φ ∘ cbar) rfl))))) := by
    refine (congrArg (fun y => maxPowEquiv ι' (detEquivOfSurjective hφ' (stabIota hT' hφ' y)))
      e1).trans ?_
    refine (congrArg (fun y => maxPowEquiv ι' (detEquivOfSurjective hφ' y)) h615').trans ?_
    refine Eq.trans ?_ (congrArg (fun y => maxPowEquiv M (maxPowEquiv ι
      (detEquivOfSurjective hφ y))) h615).symm
    refine (congrArg (maxPowEquiv ι') ((LinearEquiv.map_smul _ _ _).trans
      (congrArg (_ • ·) (detEquivOfSurjective_tmul_stabOne hφ' _)))).trans ?_
    refine Eq.trans ?_ (congrArg (fun y => maxPowEquiv M (maxPowEquiv ι y))
      ((LinearEquiv.map_smul _ _ _).trans
        (congrArg (_ • ·) (detEquivOfSurjective_tmul_stabOne hφ _)))).symm
    refine (LinearEquiv.map_smul _ _ _).trans ?_
    refine Eq.trans ?_ ((congrArg (maxPowEquiv M) (LinearEquiv.map_smul _ _ _)).trans
      (LinearEquiv.map_smul _ _ _)).symm
    rw [hdet, maxPowEquiv_wedge, maxPowEquiv_wedge, maxPowEquiv_wedge]
    exact congrArg _ (wedge_congr_fun hfin _ _)
  exact tensor_line_ext finrank_maxPow finrank_maxPowDual (wedge_basis_ne_zero' _ _)
    (dualVec_ne_zero finrank_maxPow ((wedge_ne_zero_iff _).2 hd)) hgen

/-- **The stabilization isomorphism is natural under conjugation**: for `T' A = Γ T`, `φ' = Γ φ`
and identifications `ι`, `ι'`, `M` of the kernels with `ι' (A × 1) = M ι`, the ray of `det(T')`
obtained by `conjDet(A, Γ)` goes under `Φ_{E'}` (`stabRayEquiv`) to the image under `λ(M)` of the
ray obtained by `Φ_E`. -/
theorem stabRayEquiv_conjDet (h : ∀ v, T' (A v) = Γ (T v)) (hφφ : ∀ μ, φ' μ = Γ (φ μ))
    (hT : T.IsFredholm) (hT' : T'.IsFredholm)
    (hφ : Function.Surjective (T.coprod φ)) (hφ' : Function.Surjective (T'.coprod φ'))
    {W W' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W']
    {L : Submodule ℝ W} {L' : Submodule ℝ W'} [FiniteDimensional ℝ L] [FiniteDimensional ℝ L']
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] L)
    (ι' : LinearMap.ker ((T'.coprod φ' : E' × (Fin k → ℝ) →L[ℝ] F') :
      E' × (Fin k → ℝ) →ₗ[ℝ] F') ≃ₗ[ℝ] L')
    (M : L ≃ₗ[ℝ] L')
    (hM : ∀ v, ι' (conjKerEquiv (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin k → ℝ))) Γ
      (coprod_conj A Γ h hφφ) v) = M (ι v))
    (r : Module.Ray ℝ (fredholmDet T)) :
    stabRayEquiv hT' hφ' ι' (Module.Ray.map (conjDet A Γ h) r) =
      Module.Ray.map (maxPowEquiv M) (stabRayEquiv hT hφ ι r) := by
  have key := conj_stab_key A Γ h hφφ hT hT' hφ hφ' ι ι' M hM
  induction r using Module.Ray.ind with | h v hv => ?_
  have hv' : conjDet A Γ h v ≠ 0 := (conjDet A Γ h).map_ne_zero_iff.2 hv
  obtain ⟨h1, e1'⟩ := stabRayEquiv_ray hT' hφ' ι' _ hv'
  obtain ⟨h2, e2⟩ := stabRayEquiv_ray hT hφ ι v hv
  refine (congrArg (stabRayEquiv hT' hφ' ι') (Module.Ray.map_apply _ _ _)).trans ?_
  refine e1'.trans (Eq.trans ?_ (congrArg (Module.Ray.map (maxPowEquiv M)) e2).symm)
  refine Eq.trans ?_ (Module.Ray.map_apply _ _ _).symm
  exact rayOfNeZero_eq_of_eq _ _ (LinearMap.congr_fun key v)

end ConjStab

/-- **Regrouping three-step identifications of rays** (the shape of `IsStabKernels.orRay`): if
`oe' ∘ tr = λ(C) ∘ oe` and `R' ∘ λ(C) = λ(N) ∘ R`, then `R' ∘ u ∘ oe' ∘ tr = λ(N) ∘ R ∘ u ∘ oe`
(units act on rays compatibly with `Module.Ray.map`). -/
theorem ray_trans_conj_aux {O O' D D' L L' : Type*} [AddCommMonoid D] [Module ℝ D]
    [AddCommMonoid D'] [Module ℝ D'] [AddCommMonoid L] [Module ℝ L] [AddCommMonoid L']
    [Module ℝ L'] (oe : O ≃ Module.Ray ℝ D) (oe' : O' ≃ Module.Ray ℝ D') (tr : O ≃ O')
    (C : D ≃ₗ[ℝ] D') (u u' : ℝˣ) (R : Module.Ray ℝ D ≃ Module.Ray ℝ L)
    (R' : Module.Ray ℝ D' ≃ Module.Ray ℝ L') (N : L ≃ₗ[ℝ] L')
    (hval : ∀ o, oe' (tr o) = Module.Ray.map C (oe o)) (hu : u' = u)
    (hR : ∀ r, R' (Module.Ray.map C r) = Module.Ray.map N (R r)) (o : O) :
    ((oe'.trans (MulAction.toPerm u')).trans R') (tr o) =
      Module.Ray.map N (((oe.trans (MulAction.toPerm u)).trans R) o) := by
  subst hu
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, hval,
    MulAction.toPerm_apply, MulAction.toPerm_apply, ← hR]
  congr 1
  generalize oe o = r
  induction r using Module.Ray.ind with | h v hv => ?_
  rw [smul_rayOfNeZero, Module.Ray.map_apply, Module.Ray.map_apply, smul_rayOfNeZero]
  exact rayOfNeZero_eq_of_eq _ _ (by rw [Units.smul_def, Units.smul_def, map_smul])

/-- **Regrouping for `IsPush.transfer`**: if `oa' ∘ T₀ = μ_a ∘ oa`, `ob' ∘ T₁ = μ_b ∘ ob` and
`κ' ∘ μ_a = μ_b ∘ κ`, then `T₁ ∘ ob⁻¹ ∘ κ ∘ oa ∘ T₀⁻¹ = ob'⁻¹ ∘ κ' ∘ oa'`. -/
theorem equiv_conj_push_aux {O₀ O₁ O₀' O₁' R₀ R₁ R₀' R₁' : Type*} (T₀ : O₀ ≃ O₀')
    (T₁ : O₁ ≃ O₁') (oa : O₀ ≃ R₀) (ob : O₁ ≃ R₁) (oa' : O₀' ≃ R₀') (ob' : O₁' ≃ R₁')
    (κ : R₀ ≃ R₁) (κ' : R₀' ≃ R₁') (μa : R₀ → R₀') (μb : R₁ → R₁')
    (ha : ∀ o, oa' (T₀ o) = μa (oa o)) (hb : ∀ o, ob' (T₁ o) = μb (ob o))
    (hκ : ∀ r, κ' (μa r) = μb (κ r)) :
    (T₀.symm.trans (oa.trans (κ.trans ob.symm))).trans T₁ = oa'.trans (κ'.trans ob'.symm) := by
  refine Equiv.ext fun o' => ?_
  obtain ⟨o, rfl⟩ := T₀.surjective o'
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [Equiv.eq_symm_apply, hb, Equiv.apply_symm_apply, ha, hκ]

/-! ### Continuation along images of families -/

namespace SubspaceFamily

variable {Q : Type*} [TopologicalSpace Q] [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]
  {W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W']
  [NormedSpace ℝ W']

/-- **Continuation is natural under images**: for a jointly continuous family `J_q` and
identifications `e_q : L_q ≅ L'_q` given by `J_q`, continuing `λ(e_{q₀}) r` in `Λ'` is `λ(e_{q₁})`
of continuing `r` in `Λ` (the images of the orientations of `λ(Λ)` are orientations of `λ(Λ')`,
`isLineOrientation_map`). -/
theorem cont_map (Λ : SubspaceFamily Q W) (J : Q → W →L[ℝ] W')
    (hJ : Continuous fun p : Q × W => J p.1 p.2) (Λ' : SubspaceFamily Q W')
    (e : ∀ q, Λ.L q ≃ₗ[ℝ] Λ'.L q) (he : ∀ q (v : Λ.L q), (e q v : W') = J q v) (q₀ q₁ : Q)
    (r : Module.Ray ℝ (Λ.det q₀)) :
    Λ'.cont q₀ q₁ (Module.Ray.map (maxPowEquiv (e q₀)) r) =
      Module.Ray.map (maxPowEquiv (e q₁)) (Λ.cont q₀ q₁ r) := by
  obtain ⟨o, rfl⟩ := exists_lineOrientation_apply_eq (L := Λ.det) q₀ r
  let o' : LineOrientation Λ'.det := ⟨_, Λ.isLineOrientation_map J hJ Λ' e he o⟩
  exact (Λ'.cont_eq o' q₀ q₁).trans
    (congrArg (Module.Ray.map (maxPowEquiv (e q₁))) (Λ.cont_eq o q₀ q₁)).symm

end SubspaceFamily

/-! ### Two chart points at the same point -/

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

namespace ChartPoint

variable {x : X} (p p' : ChartPoint B x)

/-- **The principal parts of a section in two chart points** are related by the fibre
transition: `Γ(ĝ(φ(x))) = ĝ'(φ'(x))`. -/
theorem fiberMap_principal {g : X → Y} (hg : IsSection P g) :
    p.fiberMap p' (p.c.principal g (p.c.φ x)) = p'.c.principal g (p'.c.φ x) := by
  have hsrc : g x ∈ p.c.toPartialEquiv.source :=
    p.c.mem_source_of_proj (by rw [hg]; exact p.mem_source)
  rw [p.fiberMap_apply_of_mem p' (p.principal_mem_K hg), p.toBase_z,
    ← p.c.apply_section' hg p.mem_source]
  change (p'.c (p.c.toPartialEquiv.symm (p.c (g x)))).2 = _
  rw [p.c.toPartialEquiv.left_inv hsrc, p'.c.apply_section' hg p'.mem_source]

/-- **The linearizations in two chart points are conjugate**: for operators `T`, `T'` given by
the linearizations of an sc-smooth section `g` with `g(x) = 0` in `p` and `p'`,
`T'(A v) = Γ(T v)` (`scDeriv_principal_baseDeriv`). -/
theorem conj_of_linAt {g : X → Y} (hg : B.IsScSmoothSection g) (hx0 : IsZeroAt P g x)
    {T : ↥p.T →L[ℝ] ↥p.K} (hT : ∀ v, (T v : p.c.F 0) = linAt p.c.U p.c.R (p.c.principal g) p.z v)
    {T' : ↥p'.T →L[ℝ] ↥p'.K}
    (hT' : ∀ v, (T' v : p'.c.F 0) = linAt p'.c.U p'.c.R (p'.c.principal g) p'.z v) (v : ↥p.T) :
    T' (p.transferT p' v) = p.transferK p' (T v) :=
  Subtype.ext ((hT' _).trans ((p.scDeriv_principal_baseDeriv p' hg hx0 v).trans
    (congrArg (p.fiberMap p') (hT v).symm)))

/-- **The stabilizing maps in two chart points are conjugate**: for `φ(μ) = Σ μᵢ ŝᵢ(φ(x))` and
`φ'(μ) = Σ μᵢ ŝ'ᵢ(φ'(x))`, `φ' = Γ φ` (`fiberMap_principal`). -/
theorem conj_of_principal {k : ℕ} (s : Fin k → X → Y) (hs : ∀ i, IsSection P (s i))
    {φ : (Fin k → ℝ) →L[ℝ] ↥p.K}
    (hφ : ∀ μ, (φ μ : p.c.F 0) = ∑ i, μ i • p.c.principal (s i) (p.c.φ x))
    {φ' : (Fin k → ℝ) →L[ℝ] ↥p'.K}
    (hφ' : ∀ μ, (φ' μ : p'.c.F 0) = ∑ i, μ i • p'.c.principal (s i) (p'.c.φ x))
    (μ : Fin k → ℝ) : φ' μ = p.transferK p' (φ μ) := by
  refine Subtype.ext ?_
  rw [hφ', coe_transferK_apply, hφ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, p.fiberMap_principal p' (hs i)]

end ChartPoint

/-- **`D(τ ∘ r)(z)` depends only on the charts and the lifts** (not on the point, which enters only
through proofs). -/
theorem ChartPoint.baseDeriv_chartPt_eq {c c' : StrongBundleChart PX P} (hc : B.IsChart c)
    (hc' : B.IsChart c') {x₁ x₂ : X} (hx₁ : x₁ ∈ c.φ.source) (hx₁' : x₁ ∈ c'.φ.source)
    (hx₂ : x₂ ∈ c.φ.source) (hx₂' : x₂ ∈ c'.φ.source) {z₁ z₂ : c.φ.model.E 1} (hz : z₁ = z₂)
    {z₁' z₂' : c'.φ.model.E 1} (hz' : z₁' = z₂') (h₁ : c.φ.model.E.toBase 1 z₁ = c.φ x₁)
    (h₂ : c.φ.model.E.toBase 1 z₂ = c.φ x₂) (h₁' : c'.φ.model.E.toBase 1 z₁' = c'.φ x₁)
    (h₂' : c'.φ.model.E.toBase 1 z₂' = c'.φ x₂) (v : c.φ.model.E 0) :
    (chartPt c hc hx₁ z₁ h₁).baseDeriv (chartPt c' hc' hx₁' z₁' h₁') v =
      (chartPt c hc hx₂ z₂ h₂).baseDeriv (chartPt c' hc' hx₂' z₂' h₂') v := by
  subst hz hz'
  rfl

/-- **The base derivatives vary continuously along a continuous lift**: for points `y(q)` in the
domains of two charts and level-`1` lifts `z_q` continuous in `q`, `(q, v) ↦ D(τ ∘ r)(z_q) v` is
jointly continuous (the tangent map of the sc¹ map `τ ∘ r_W` is sc⁰, and `W` depends only on the
charts). -/
theorem continuous_baseDeriv {Q : Type*} [TopologicalSpace Q] {c c' : StrongBundleChart PX P}
    (hc : B.IsChart c) (hc' : B.IsChart c') {y : Q → X} (hy : ∀ q, y q ∈ c.φ.source)
    (hy' : ∀ q, y q ∈ c'.φ.source) (z : Q → c.φ.model.E 1)
    (hz : ∀ q, c.φ.model.E.toBase 1 (z q) = c.φ (y q)) (z' : Q → c'.φ.model.E 1)
    (hz' : ∀ q, c'.φ.model.E.toBase 1 (z' q) = c'.φ (y q)) (hzc : Continuous z) :
    Continuous (Y := c'.φ.model.E 0) fun w : Q × c.φ.model.E 0 =>
      (chartPt c hc (hy w.1) (z w.1) (hz w.1)).baseDeriv
        (chartPt c' hc' (hy' w.1) (z' w.1) (hz' w.1)) w.2 := by
  refine continuous_iff_continuousAt.2 fun w₀ => ?_
  let p₀ := chartPt c hc (hy w₀.1) (z w₀.1) (hz w₀.1)
  let p₀' := chartPt c' hc' (hy' w₀.1) (z' w₀.1) (hz' w₀.1)
  have h1 := (p₀.isSc1_transition p₀').isSc1With_scDeriv.continuousOn_deriv
  have hmem : ∀ w : Q × c.φ.model.E 0, ((z w.1, w.2) : c.φ.model.E 1 × c.φ.model.E 0) ∈
      {p | p.1 ∈ c.φ.model.E.lvlSet (p₀.baseRet p₀').U 1} := fun w =>
    (chartPt c hc (hy w.1) (z w.1) (hz w.1)).z_mem_baseRet
      (chartPt c' hc' (hy' w.1) (z' w.1) (hz' w.1))
  exact (h1.comp_continuous ((hzc.comp continuous_fst).prodMk continuous_snd) hmem).continuousAt

/-! ### Stabilized kernels in a second chart -/

section StabKernels

variable {Q : Type*} [TopologicalSpace Q]

namespace IsStabKernels

variable {c c' : StrongBundleChart PX P} {hc : B.IsChart c} {y : Q → X}
  {hy : ∀ q, y q ∈ c.φ.source} {S : Q → X → Y} {k : ℕ} {s : Fin k → Q → X → Y}
  {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}

/-- **Stabilized kernels in a second chart**: a family `Λ` of stabilized kernels in the chart `c`
is carried by `J_q = D(τ ∘ r)(z_q) × 1` (for lifts `z_q` continuous in `q`) to a family `Λ'` of
stabilized kernels in a second chart `c'`, with the same points and sections; `M_q : Λ_q ≅ Λ'_q`
is `J_q` on the members. -/
theorem exists_transfer (hΛ : IsStabKernels f c hc y hy S s Λ) (hf : B.IsScFredholmSection f)
    (hc' : B.IsChart c') (hy' : ∀ q, y q ∈ c'.φ.source) (z : Q → c.φ.model.E 1)
    (hz : ∀ q, c.φ.model.E.toBase 1 (z q) = c.φ (y q)) (hzc : Continuous z)
    (z' : Q → c'.φ.model.E 1) (hz' : ∀ q, c'.φ.model.E.toBase 1 (z' q) = c'.φ (y q)) :
    ∃ (Λ' : SubspaceFamily Q (c'.φ.model.E 0 × (Fin k → ℝ))) (M : ∀ q, Λ.L q ≃ₗ[ℝ] Λ'.L q),
      IsStabKernels f c' hc' y hy' S s Λ' ∧ ∀ q (v : Λ.L q),
        (M q v : c'.φ.model.E 0 × (Fin k → ℝ)) =
          ((chartPt c hc (hy q) (z q) (hz q)).baseDeriv
            (chartPt c' hc' (hy' q) (z' q) (hz' q))).prodMap
              (ContinuousLinearMap.id ℝ (Fin k → ℝ)) v := by
  let J : Q → c.φ.model.E 0 × (Fin k → ℝ) →L[ℝ] c'.φ.model.E 0 × (Fin k → ℝ) := fun q =>
    ((chartPt c hc (hy q) (z q) (hz q)).baseDeriv
      (chartPt c' hc' (hy' q) (z' q) (hz' q))).prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ))
  have hJc : Continuous fun w : Q × (c.φ.model.E 0 × (Fin k → ℝ)) => J w.1 w.2 :=
    ((continuous_baseDeriv hc hc' hy hy' z hz z' hz' hzc).comp
      (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd
  have hsp := fun q => hΛ.spec q rfl (hy q) (z q) (hz q)
    ((chartPt c hc (hy q) (z q) (hz q)).stabT hf (hΛ.isScPlusSection q) (hΛ.zero q))
    (fun _ => rfl)
    ((chartPt c hc (hy q) (z q) (hz q)).stabPhi (fun i => s i q) (fun i => hΛ.isSection i q))
    (fun μ => ChartPoint.coe_stabPhi _ _ _ μ)
  have hT : ∀ q, ∀ v ∈ Λ.L q, v.1 ∈ (chartPt c hc (hy q) (z q) (hz q)).T := fun q v hv => by
    rw [(hsp q).2] at hv
    obtain ⟨w, -, rfl⟩ := hv
    exact w.1.2
  have hinj : ∀ q, Set.InjOn (J q) (Λ.L q) := fun q v hv v' hv' hvv => by
    have h1 := congrArg (fun w => (chartPt c' hc' (hy' q) (z' q) (hz' q)).baseDeriv
      (chartPt c hc (hy q) (z q) (hz q)) w.1) hvv
    have h2 := congrArg Prod.snd hvv
    dsimp only at h1
    exact Prod.ext (((ChartPoint.baseDeriv_baseDeriv _ _ (hT q v hv)).symm.trans h1).trans
      (ChartPoint.baseDeriv_baseDeriv _ _ (hT q v' hv'))) h2
  obtain ⟨Λ', hΛ'⟩ := Λ.exists_map J hJc hinj
  have hinj' : ∀ q, Function.Injective ((J q : c.φ.model.E 0 × (Fin k → ℝ) →ₗ[ℝ]
      c'.φ.model.E 0 × (Fin k → ℝ)) ∘ₗ (Λ.L q).subtype) :=
    fun q v v' hvv => Subtype.ext (hinj q v.2 v'.2 hvv)
  refine ⟨Λ', fun q => (LinearEquiv.ofInjective _ (hinj' q)).trans (LinearEquiv.ofEq _ _
    (by rw [hΛ' q, LinearMap.range_comp, Submodule.range_subtype])), ⟨hΛ.isScPlusSection,
    hΛ.zero, hΛ.isSection, fun q => ⟨z' q, hz' q⟩, ?_⟩, fun q v => rfl⟩
  intro q x hq hxc z₁ hz₁ T' hT' φ' hφ'
  subst hq
  obtain rfl : z₁ = z' q := c'.φ.model.E.toBase_injective 1 (hz₁.trans (hz' q).symm)
  have hconj := (chartPt c hc (hy q) (z q) (hz q)).conj_of_linAt
    (chartPt c' hc' hxc (z' q) hz₁) (hf.isScSmooth.sectionAdd (hΛ.isScPlusSection q)) (hΛ.zero q)
    (T := (chartPt c hc (hy q) (z q) (hz q)).stabT hf (hΛ.isScPlusSection q) (hΛ.zero q))
    (fun _ => rfl) hT'
  have hφconj := (chartPt c hc (hy q) (z q) (hz q)).conj_of_principal
    (chartPt c' hc' hxc (z' q) hz₁) (fun i => s i q) (fun i => hΛ.isSection i q)
    (φ := (chartPt c hc (hy q) (z q) (hz q)).stabPhi (fun i => s i q)
      (fun i => hΛ.isSection i q))
    (fun μ => ChartPoint.coe_stabPhi _ _ _ μ) hφ'
  refine ⟨surjective_coprod_conj _ _ hconj hφconj (hsp q).1, ?_⟩
  rw [hΛ' q, (hsp q).2, ker_coprod_conj _ _ hconj hφconj, ← Submodule.map_comp,
    ← Submodule.map_comp]
  rfl

/-- **The orientations read in `λ(Λ_q)` correspond under `orTransfer`**: for stabilized kernels
`Λ`, `Λ'` with the same data in two charts and `M : Λ_q ≅ Λ'_q` given by `D(τ ∘ r)(z) × 1`,
`orRay'_q (orTransfer o) = λ(M) (orRay_q o)` (`stabSign_conj`, `stabRayEquiv_conjDet`). -/
theorem orRay_transfer (hΛ : IsStabKernels f c hc y hy S s Λ) {hc' : B.IsChart c'}
    {hy' : ∀ q, y q ∈ c'.φ.source} {Λ' : SubspaceFamily Q (c'.φ.model.E 0 × (Fin k → ℝ))}
    (hΛ' : IsStabKernels f c' hc' y hy' S s Λ') (hf : B.IsScFredholmSection f) (q : Q) {x : X}
    (hq : y q = x) (hx : x ∈ PX.smoothSet) (z : c.φ.model.E 1)
    (hz : c.φ.model.E.toBase 1 z = c.φ x) (z' : c'.φ.model.E 1)
    (hz' : c'.φ.model.E.toBase 1 z' = c'.φ x) (M : Λ.L q ≃ₗ[ℝ] Λ'.L q)
    (hM : ∀ v : Λ.L q, (M v : c'.φ.model.E 0 × (Fin k → ℝ)) =
      ((chartPt c hc (hq ▸ hy q) z hz).baseDeriv (chartPt c' hc' (hq ▸ hy' q) z' hz')).prodMap
        (ContinuousLinearMap.id ℝ (Fin k → ℝ)) v)
    (o : (chartPt c hc (hq ▸ hy q) z hz).Or f hf) :
    hΛ'.orRay hf q hq hx z' hz' ((chartPt c hc (hq ▸ hy q) z hz).orTransfer
        (chartPt c' hc' (hq ▸ hy' q) z' hz') hf hx o) =
      Module.Ray.map (maxPowEquiv M) (hΛ.orRay hf q hq hx z hz o) := by
  subst hq
  have h0 : IsZeroAt P (sectionAdd P f (S q)) (y q) := hΛ.zero q
  let p := chartPt c hc (hy q) z hz
  let p' := chartPt c' hc' (hy' q) z' hz'
  have : CompleteSpace ↥p.T :=
    (fun p : ChartPoint B (y q) => (inferInstance : CompleteSpace ↥p.T)) _
  have : CompleteSpace ↥p.K :=
    (fun p : ChartPoint B (y q) => (inferInstance : CompleteSpace ↥p.K)) _
  have : CompleteSpace ↥p'.T :=
    (fun p : ChartPoint B (y q) => (inferInstance : CompleteSpace ↥p.T)) _
  have : CompleteSpace ↥p'.K :=
    (fun p : ChartPoint B (y q) => (inferInstance : CompleteSpace ↥p.K)) _
  let T := p.stabT hf (hΛ.isScPlusSection q) h0
  let T' := p'.stabT hf (hΛ.isScPlusSection q) h0
  let φ := p.stabPhi (fun i => s i q) (fun i => hΛ.isSection i q)
  let φ' := p'.stabPhi (fun i => s i q) (fun i => hΛ.isSection i q)
  have hTm := p.stabT_mem_linSet hf (hΛ.isScPlusSection q) h0 hx
  have hT'm := p'.stabT_mem_linSet hf (hΛ.isScPlusSection q) h0 hx
  have hconj : ∀ v, T' (p.transferT p' v) = p.transferK p' (T v) :=
    p.conj_of_linAt p' (hf.isScSmooth.sectionAdd (hΛ.isScPlusSection q)) h0 (T := T)
      (fun _ => rfl) (T' := T') (fun _ => rfl)
  have hφconj : ∀ μ, φ' μ = p.transferK p' (φ μ) :=
    p.conj_of_principal p' (fun i => s i q) (fun i => hΛ.isSection i q) (φ := φ)
      (fun μ => p.coe_stabPhi _ _ μ) (φ' := φ') (fun μ => p'.coe_stabPhi _ _ μ)
  have hsq := hΛ.spec q rfl (hy q) z hz T (fun _ => rfl) φ (fun μ => p.coe_stabPhi _ _ μ)
  have hsq' := hΛ'.spec q rfl (hy' q) z' hz' T' (fun _ => rfl) φ'
    (fun μ => p'.coe_stabPhi _ _ μ)
  have hval : ∀ o', p'.orEquivRay hf hT'm (p.orTransfer p' hf hx o') =
      Module.Ray.map (conjDet (p.transferT p') (p.transferK p') hconj) (p.orEquivRay hf hTm o') :=
    fun o' => LineOrientation.conj_apply (hC' := p'.isFredholm_of_mem_linSet hf) _ _
      (p.transfer_mem_linSet p' hf hx) o' hTm hT'm hconj
  have hM' : ∀ v, kerEquivMap p'.T.subtypeL Subtype.val_injective hsq'.2
      (conjKerEquiv ((p.transferT p').prodCongr (ContinuousLinearEquiv.refl ℝ (Fin k → ℝ)))
        (p.transferK p') (coprod_conj _ _ hconj hφconj) v) =
      M (kerEquivMap p.T.subtypeL Subtype.val_injective hsq.2 v) := fun v => by
    refine Subtype.ext ?_
    rw [hM]
    exact Prod.ext rfl rfl
  exact ray_trans_conj_aux (p.orEquivRay hf hTm) (p'.orEquivRay hf hT'm) (p.orTransfer p' hf hx)
    (conjDet (p.transferT p') (p.transferK p') hconj) (stabSign T) (stabSign T')
    (stabRayEquiv (p.isFredholm_of_mem_linSet hf _ hTm) hsq.1
      (kerEquivMap p.T.subtypeL Subtype.val_injective hsq.2))
    (stabRayEquiv (p'.isFredholm_of_mem_linSet hf _ hT'm) hsq'.1
      (kerEquivMap p'.T.subtypeL Subtype.val_injective hsq'.2))
    (maxPowEquiv M) hval (stabSign_conj _ _ hconj)
    (stabRayEquiv_conjDet (p.transferT p') (p.transferK p') hconj hφconj
      (p.isFredholm_of_mem_linSet hf _ hTm) (p'.isFredholm_of_mem_linSet hf _ hT'm) hsq.1 hsq'.1
      (kerEquivMap p.T.subtypeL Subtype.val_injective hsq.2)
      (kerEquivMap p'.T.subtypeL Subtype.val_injective hsq'.2) M hM') o

end IsStabKernels

end StabKernels

/-! ### The push-forward in two charts -/

section Push

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **A push-forward in one chart is a push-forward in any other chart**: for an sc-smooth path
`γ` in the domains of two charts `c`, `c'`, a push-forward `e` along `γ` in `c`, conjugated by
`orTransfer` at the end points, is a push-forward along `γ` in `c'` (with the same sections; the
kernels are carried by `D(τ ∘ r)(z_t) × 1`, `IsStabKernels.exists_transfer`). -/
theorem IsPush.transfer {hf : B.IsScFredholmSection f} {c c' : StrongBundleChart PX P}
    (hc : B.IsChart c) (hc' : B.IsChart c') {γ : (Fin 1 → ℝ) → X}
    (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source)
    (hγ' : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c'.φ.source) {x₀ x₁ : X}
    (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hx₀ : x₀ ∈ c.φ.source) (hx₁ : x₁ ∈ c.φ.source)
    (hx₀' : x₀ ∈ c'.φ.source) (hx₁' : x₁ ∈ c'.φ.source) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet)
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf}
    (he : IsPush f hf c hc γ hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁ e) :
    IsPush f hf c' hc' γ hγ' h₀ h₁ hx₀' hx₁' hs₀ hs₁
      ((((chartPtOf c hc hx₀ hs₀).orTransfer (chartPtOf c' hc' hx₀' hs₀) hf hs₀).symm.trans
        e).trans ((chartPtOf c hc hx₁ hs₁).orTransfer (chartPtOf c' hc' hx₁' hs₁) hf hs₁)) := by
  obtain ⟨S, hS, hz, k, s, hs, Λ, hΛ, rfl⟩ := he
  obtain ⟨zc, hzcc, hzc⟩ := exists_continuousOn_lift_chart hγs c.isChart
  obtain ⟨zc', -, hzc'⟩ := exists_continuousOn_lift_chart hγs c'.isChart
  have hzQ : Continuous fun q : Icc (0 : Fin 1 → ℝ) 1 => zc q :=
    hzcc.comp_continuous continuous_subtype_val fun q => hγ q q.2
  obtain ⟨Λ', M, hΛ', hM⟩ := hΛ.exists_transfer hf hc' (fun q => hγ' q q.2) (fun q => zc q)
    (fun q => hzc q (hγ q q.2)) hzQ (fun q => zc' q) (fun q => hzc' q (hγ' q q.2))
  refine ⟨S, hS, hz, k, s, hs, Λ', hΛ', ?_⟩
  -- the end points and the lifts there
  let a : Icc (0 : Fin 1 → ℝ) 1 := ⟨pt1 0, pt1_mem_Icc (left_mem_Icc.2 zero_le_one)⟩
  let b : Icc (0 : Fin 1 → ℝ) 1 := ⟨pt1 1, pt1_mem_Icc (right_mem_Icc.2 zero_le_one)⟩
  have e₀ : zc a = (exists_lift_of_smooth c hx₀ hs₀).choose :=
    c.φ.model.E.toBase_injective 1 ((hzc _ (hγ a a.2)).trans ((congrArg c.φ h₀).trans
      (exists_lift_of_smooth c hx₀ hs₀).choose_spec.symm))
  have e₁ : zc b = (exists_lift_of_smooth c hx₁ hs₁).choose :=
    c.φ.model.E.toBase_injective 1 ((hzc _ (hγ b b.2)).trans ((congrArg c.φ h₁).trans
      (exists_lift_of_smooth c hx₁ hs₁).choose_spec.symm))
  have e₀' : zc' a = (exists_lift_of_smooth c' hx₀' hs₀).choose :=
    c'.φ.model.E.toBase_injective 1 ((hzc' _ (hγ' a a.2)).trans ((congrArg c'.φ h₀).trans
      (exists_lift_of_smooth c' hx₀' hs₀).choose_spec.symm))
  have e₁' : zc' b = (exists_lift_of_smooth c' hx₁' hs₁).choose :=
    c'.φ.model.E.toBase_injective 1 ((hzc' _ (hγ' b b.2)).trans ((congrArg c'.φ h₁).trans
      (exists_lift_of_smooth c' hx₁' hs₁).choose_spec.symm))
  have hMa : ∀ v : Λ.L a, (M a v : c'.φ.model.E 0 × (Fin k → ℝ)) =
      ((chartPtOf c hc hx₀ hs₀).baseDeriv (chartPtOf c' hc' hx₀' hs₀)).prodMap
        (ContinuousLinearMap.id ℝ (Fin k → ℝ)) (v : c.φ.model.E 0 × (Fin k → ℝ)) := fun v =>
    (hM a v).trans (Prod.ext (ChartPoint.baseDeriv_chartPt_eq hc hc' _ _ _ _ e₀ e₀' _ _ _ _ _) rfl)
  have hMb : ∀ v : Λ.L b, (M b v : c'.φ.model.E 0 × (Fin k → ℝ)) =
      ((chartPtOf c hc hx₁ hs₁).baseDeriv (chartPtOf c' hc' hx₁' hs₁)).prodMap
        (ContinuousLinearMap.id ℝ (Fin k → ℝ)) (v : c.φ.model.E 0 × (Fin k → ℝ)) := fun v =>
    (hM b v).trans (Prod.ext (ChartPoint.baseDeriv_chartPt_eq hc hc' _ _ _ _ e₁ e₁' _ _ _ _ _) rfl)
  let J : Icc (0 : Fin 1 → ℝ) 1 → c.φ.model.E 0 × (Fin k → ℝ) →L[ℝ]
      c'.φ.model.E 0 × (Fin k → ℝ) := fun q =>
    ((chartPt c hc (hγ q q.2) (zc q) (hzc q (hγ q q.2))).baseDeriv
      (chartPt c' hc' (hγ' q q.2) (zc' q) (hzc' q (hγ' q q.2)))).prodMap
        (ContinuousLinearMap.id ℝ (Fin k → ℝ))
  have hJc : Continuous fun w : Icc (0 : Fin 1 → ℝ) 1 × (c.φ.model.E 0 × (Fin k → ℝ)) =>
      J w.1 w.2 :=
    ((continuous_baseDeriv hc hc' (fun q : Icc (0 : Fin 1 → ℝ) 1 => hγ q q.2)
      (fun q => hγ' q q.2) (fun q => zc q)
      (fun q => hzc q (hγ q q.2)) (fun q => zc' q) (fun q => hzc' q (hγ' q q.2)) hzQ).comp
        (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd
  rw [hΛ.push_eq_orRay, hΛ'.push_eq_orRay]
  exact equiv_conj_push_aux _ _ _ _ _ _ _ _ (Module.Ray.map (maxPowEquiv (M a)))
    (Module.Ray.map (maxPowEquiv (M b)))
    (fun o => hΛ.orRay_transfer hΛ' hf a h₀ hs₀ (exists_lift_of_smooth c hx₀ hs₀).choose
      (exists_lift_of_smooth c hx₀ hs₀).choose_spec (exists_lift_of_smooth c' hx₀' hs₀).choose
      (exists_lift_of_smooth c' hx₀' hs₀).choose_spec (M a) hMa o)
    (fun o => hΛ.orRay_transfer hΛ' hf b h₁ hs₁ (exists_lift_of_smooth c hx₁ hs₁).choose
      (exists_lift_of_smooth c hx₁ hs₁).choose_spec (exists_lift_of_smooth c' hx₁' hs₁).choose
      (exists_lift_of_smooth c' hx₁' hs₁).choose_spec (M b) hMb o)
    (fun r => SubspaceFamily.cont_map Λ J hJc Λ' M hM a b r)

/-- **The local push-forwards in two charts correspond under `orTransfer`**: for neighbourhoods
`U`, `U'` with the local propagation property in charts `c`, `c'` and an sc-smooth path `γ` in
`U ∩ U'` with smooth end points, the push-forwards along `γ` in `c` and in `c'` are conjugate by
`orTransfer` at the end points (`IsPush.transfer` and the uniqueness in `U'`). -/
theorem HasLocalPropagation.push_compat {hf : B.IsScFredholmSection f}
    {c c' : StrongBundleChart PX P} {hc : B.IsChart c} {hc' : B.IsChart c'} {U U' : Set X}
    (hU : HasLocalPropagation f hf c hc U) (hU' : HasLocalPropagation f hf c' hc' U')
    {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U) (hγ' : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U')
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hx₀ : x₀ ∈ c.φ.source)
    (hx₁ : x₁ ∈ c.φ.source) (hx₀' : x₀ ∈ c'.φ.source) (hx₁' : x₁ ∈ c'.φ.source)
    (hs₀ : x₀ ∈ PX.smoothSet) (hs₁ : x₁ ∈ PX.smoothSet)
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf}
    {e' : (chartPtOf c' hc' hx₀' hs₀).Or f hf ≃ (chartPtOf c' hc' hx₁' hs₁).Or f hf}
    (he : IsPush f hf c hc γ (fun q hq => hU.subset (hγ q hq)) h₀ h₁ hx₀ hx₁ hs₀ hs₁ e)
    (he' : IsPush f hf c' hc' γ (fun q hq => hU'.subset (hγ' q hq)) h₀ h₁ hx₀' hx₁' hs₀ hs₁ e') :
    e' = (((chartPtOf c hc hx₀ hs₀).orTransfer (chartPtOf c' hc' hx₀' hs₀) hf hs₀).symm.trans
      e).trans ((chartPtOf c hc hx₁ hs₁).orTransfer (chartPtOf c' hc' hx₁' hs₁) hf hs₁) :=
  hU'.eq γ γ hγs hγs hγ' hγ' h₀ h₁ h₀ h₁ hx₀' hx₁' hs₀ hs₁ _ _ he'
    (IsPush.transfer hc hc' hγs (fun q hq => hU.subset (hγ q hq))
      (fun q hq => hU'.subset (hγ' q hq)) h₀ h₁ hx₀ hx₁ hx₀' hx₁' hs₀ hs₁ he)

end Push

end Polyfold
