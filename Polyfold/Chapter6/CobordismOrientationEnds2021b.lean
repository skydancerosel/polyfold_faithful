import Polyfold.Chapter6.CobordismOrientationEnds2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Remark 6.6.19**, p. 276
(preprint Remark 6.42), and the proof of **Theorem 6.7.1**, p. 278: the tangent orientation given
by the product orientation `e ∧ o`.

# The tangent orientation of the product orientation

For `L` onto and `L̂ = Γ⁻¹ (L ⊕ 0) A` (the linearization `(σ, v) ↦ Lv` of `f̃`), the orientation
`e ∧ o` of `det L̂` read in `λ(ker L̂)`, `ker L̂ = ℝ × ker L`, is `ê ∧ (o` read in `λ(ker L))`.
In coordinates `ι̂(s, w) = (s, ι w)` of the two kernels it is the standard orientation of
`ℝ^{k+1}` exactly when `o` is the standard orientation of `ℝ^k`:

`pullOr_surjRay_extConjDetFirst_iff` is this statement for operators between Banach spaces
(through `surjRay_extConjDetFirst`, from `stabRayEquiv_extConjDetFirst` with a stabilization by
`ℝ⁰`). The chart form is in `CobordismOrientationEnds2021c.lean`.
-/

open Set Filter Topology Manifold Module

noncomputable section

namespace Polyfold

universe u v

/-! ### A constant family of subspaces, and kernels of stabilizations by `ℝ⁰` -/

section Const

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The family over a point with the one member `L`. -/
def SubspaceFamily.constUnit (L : Submodule ℝ W) [FiniteDimensional ℝ L] :
    SubspaceFamily PUnit.{1} W where
  L _ := L
  n := finrank ℝ L
  finiteDimensional _ := inferInstance
  finrank_eq _ := rfl
  exists_frame _ := ⟨univ, isOpen_univ, mem_univ _, fun i _ => (Module.finBasis ℝ L i : W),
    fun _ => continuousOn_const, fun _ _ => ⟨fun i => (Module.finBasis ℝ L i).2,
      (Module.finBasis ℝ L).linearIndependent.map' L.subtype (Submodule.ker_subtype L)⟩⟩

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- For a stabilization by `ℝ⁰`, the kernel of `T ⊕ φ` read in `V × ℝ⁰` is
`{(v, 0) | v ∈ j(ker T)}`. -/
theorem map_ker_coprod_fin_zero (T : E →L[ℝ] F) (φ : (Fin 0 → ℝ) →L[ℝ] F) (j : E →L[ℝ] V) :
    (LinearMap.ker ((T.coprod φ : E × (Fin 0 → ℝ) →L[ℝ] F) : E × (Fin 0 → ℝ) →ₗ[ℝ] F)).map
        ((j.prodMap (ContinuousLinearMap.id ℝ (Fin 0 → ℝ)) :
          E × (Fin 0 → ℝ) →L[ℝ] V × (Fin 0 → ℝ)) : E × (Fin 0 → ℝ) →ₗ[ℝ] V × (Fin 0 → ℝ)) =
      ((LinearMap.ker (T : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V)).map
        (ContinuousLinearMap.inl ℝ V (Fin 0 → ℝ) : V →ₗ[ℝ] V × (Fin 0 → ℝ)) := by
  have hφ0 : ∀ μ, φ μ = 0 := fun μ => by rw [Subsingleton.elim μ 0, map_zero]
  ext ⟨w, μ⟩
  simp only [Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨u, μ'⟩, hker, hw⟩
    refine ⟨j u, ⟨u, ?_, rfl⟩, ?_⟩
    · change T u + φ μ' = 0 at hker
      rwa [hφ0, add_zero] at hker
    · rw [← hw]
      exact Prod.ext rfl (Subsingleton.elim _ _)
  · rintro ⟨v, ⟨u, hu, rfl⟩, hvw⟩
    refine ⟨(u, 0), ?_, ?_⟩
    · change T u + φ 0 = 0
      rw [map_zero, add_zero]
      exact hu
    · rw [← hvw]
      rfl

/-- `N ≅ L`, `v ↦ (v, 0)`, for `L = {(v, 0) | v ∈ N} ⊆ V × ℝ⁰`. -/
def inlEquiv {N : Submodule ℝ V} {L : Submodule ℝ (V × (Fin 0 → ℝ))}
    (h : N.map (ContinuousLinearMap.inl ℝ V (Fin 0 → ℝ) : V →ₗ[ℝ] V × (Fin 0 → ℝ)) = L) :
    N ≃ₗ[ℝ] L :=
  (Submodule.equivMapOfInjective
    (ContinuousLinearMap.inl ℝ V (Fin 0 → ℝ) : V →ₗ[ℝ] V × (Fin 0 → ℝ))
    (fun _ _ h => congrArg Prod.fst h) N).trans (LinearEquiv.ofEq _ _ h)

theorem coe_inlEquiv {N : Submodule ℝ V} {L : Submodule ℝ (V × (Fin 0 → ℝ))}
    (h : N.map (ContinuousLinearMap.inl ℝ V (Fin 0 → ℝ) : V →ₗ[ℝ] V × (Fin 0 → ℝ)) = L)
    (v : N) : (inlEquiv h v : V × (Fin 0 → ℝ)) = ((v : V), 0) := rfl

end Const

/-! ### The statement for operators -/

section Operators

variable {E F E' F' V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The sign `α(T)` of a surjective operator acts trivially. -/
theorem stabSign_smul_of_surjective {T : E →L[ℝ] F} (hTs : Function.Surjective T)
    (r : Module.Ray ℝ (fredholmDet T)) : stabSign T • r = r := by
  rw [stabSign_of_surjective hTs, one_smul]

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- **`e ∧ o` read in the kernel of `L̂` is `ê ∧ (o` read in the kernel of `L)`** (2021
Remark 6.6.19, the vector `e` first), for `L` onto, `L̂ = Γ⁻¹ (L ⊕ 0) A`, and the kernels read
in `V` and `ℝ¹ × V` through `j` and `j' = (pr₂ A, j pr₁ A)`. -/
theorem surjRay_extConjDetFirst (A : E' ≃L[ℝ] E × (Fin 1 → ℝ)) (Γ : F' ≃L[ℝ] F)
    {T : E →L[ℝ] F} (hT : T.IsFredholm) (hT' : (extConjOp A Γ T).IsFredholm)
    (hTs : Function.Surjective T) (hTs' : Function.Surjective (extConjOp A Γ T))
    (j : E →L[ℝ] V) (hj : Function.Injective j) (j' : E' →L[ℝ] (Fin 1 → ℝ) × V)
    (hj' : Function.Injective j') (hjj : ∀ v, j' v = ((A v).2, j (A v).1))
    {N : Submodule ℝ V} (hN : (LinearMap.ker (T : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N)
    {N' : Submodule ℝ ((Fin 1 → ℝ) × V)}
    (hN' : (LinearMap.ker ((extConjOp A Γ T : E' →L[ℝ] F') : E' →ₗ[ℝ] F')).map
      (j' : E' →ₗ[ℝ] (Fin 1 → ℝ) × V) = N')
    (Λ : SubspaceFamily PUnit.{1} (V × (Fin 0 → ℝ)))
    (hΛ : Λ.L PUnit.unit = N.map
      (ContinuousLinearMap.inl ℝ V (Fin 0 → ℝ) : V →ₗ[ℝ] V × (Fin 0 → ℝ)))
    (hΛ' : N'.map (ContinuousLinearMap.inl ℝ ((Fin 1 → ℝ) × V) (Fin 0 → ℝ) :
      (Fin 1 → ℝ) × V →ₗ[ℝ] ((Fin 1 → ℝ) × V) × (Fin 0 → ℝ)) = Λ.prodLine.L PUnit.unit)
    (r : Module.Ray ℝ (fredholmDet T)) :
    Module.Ray.map (maxPowEquiv (inlEquiv hΛ'))
        (surjRay hTs' j' hj' hN' (Module.Ray.map (extConjDetFirst A Γ hT hT') r)) =
      Module.Ray.map (Λ.prodLineWedgeEquiv PUnit.unit)
        (Module.Ray.map (maxPowEquiv (inlEquiv hΛ.symm)) (surjRay hTs j hj hN r)) := by
  obtain ⟨φ, hφdef⟩ : ∃ φ : (Fin 0 → ℝ) →L[ℝ] F, φ = 0 := ⟨0, rfl⟩
  obtain ⟨φ', hφ'def⟩ : ∃ φ' : (Fin 0 → ℝ) →L[ℝ] F', φ' = 0 := ⟨0, rfl⟩
  have hφφ : ∀ μ, φ μ = Γ (φ' μ) := fun μ => by simp [hφdef, hφ'def]
  have hφ : Function.Surjective (T.coprod φ) := fun w => by
    obtain ⟨v, hv⟩ := hTs w
    exact ⟨(v, 0), by rw [ContinuousLinearMap.coprod_apply, map_zero, add_zero, hv]⟩
  have hφ' : Function.Surjective ((extConjOp A Γ T).coprod φ') := fun w => by
    obtain ⟨v, hv⟩ := hTs' w
    exact ⟨(v, 0), by rw [ContinuousLinearMap.coprod_apply, map_zero, add_zero, hv]⟩
  have hL : Λ.L PUnit.unit = (LinearMap.ker ((T.coprod φ : E × (Fin 0 → ℝ) →L[ℝ] F) :
      E × (Fin 0 → ℝ) →ₗ[ℝ] F)).map ((j.prodMap (ContinuousLinearMap.id ℝ (Fin 0 → ℝ)) :
        E × (Fin 0 → ℝ) →L[ℝ] V × (Fin 0 → ℝ)) : E × (Fin 0 → ℝ) →ₗ[ℝ] V × (Fin 0 → ℝ)) := by
    rw [hΛ, map_ker_coprod_fin_zero, hN]
  have hL' : Λ.prodLine.L PUnit.unit = (LinearMap.ker (((extConjOp A Γ T).coprod φ' :
      E' × (Fin 0 → ℝ) →L[ℝ] F') : E' × (Fin 0 → ℝ) →ₗ[ℝ] F')).map
      ((j'.prodMap (ContinuousLinearMap.id ℝ (Fin 0 → ℝ)) :
        E' × (Fin 0 → ℝ) →L[ℝ] ((Fin 1 → ℝ) × V) × (Fin 0 → ℝ)) :
          E' × (Fin 0 → ℝ) →ₗ[ℝ] ((Fin 1 → ℝ) × V) × (Fin 0 → ℝ)) := by
    rw [← hΛ', map_ker_coprod_fin_zero, hN']
  have h1 := stabRayEquiv_extConjDetFirst A Γ hφφ hT hT' hφ hφ' (kerEquivMap j hj hL)
    (kerEquivMap j' hj' hL') (Λ.prodLineWedgeEquiv PUnit.unit)
    (prodLineWedgeEquiv_compat A Γ hT hφφ j hj j' hj' hjj Λ PUnit.unit hL hL') r
  have h2 := stabRayEquiv_eq_surjRay hT hTs hφ j hj hL hN (inlEquiv hΛ.symm)
    (coe_inlEquiv hΛ.symm) r
  have h3 := stabRayEquiv_eq_surjRay hT' hTs' hφ' j' hj' hL' hN' (inlEquiv hΛ')
    (coe_inlEquiv hΛ') (Module.Ray.map (extConjDetFirst A Γ hT hT') r)
  have h2' := (congrArg (stabRayEquiv hT hφ (kerEquivMap j hj hL))
    (stabSign_smul_of_surjective hTs _)).symm.trans h2
  have h3' := (congrArg (stabRayEquiv hT' hφ' (kerEquivMap j' hj' hL'))
    (stabSign_smul_of_surjective hTs' _)).symm.trans h3
  exact h3'.symm.trans (h1.trans (congrArg (Module.Ray.map (Λ.prodLineWedgeEquiv PUnit.unit)) h2'))

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- **The product orientation in coordinates of the kernels**: for `L` onto,
`L̂ = Γ⁻¹ (L ⊕ 0) A`, and coordinates `ι : ℝ^k ≅ ker L`, `ι̂ : ℝ^{k+1} ≅ ker L̂` with
`ι̂(s, w) = (s, ι w)`, the orientation `e ∧ o` of `det L̂` reads in `ι̂` as the standard
orientation of `ℝ^{k+1}` iff `o` reads in `ι` as the standard orientation of `ℝ^k`. -/
theorem pullOr_surjRay_extConjDetFirst_iff (A : E' ≃L[ℝ] E × (Fin 1 → ℝ)) (Γ : F' ≃L[ℝ] F)
    {T : E →L[ℝ] F} (hT : T.IsFredholm) (hT' : (extConjOp A Γ T).IsFredholm)
    (hTs : Function.Surjective T) (hTs' : Function.Surjective (extConjOp A Γ T))
    (j : E →L[ℝ] V) (hj : Function.Injective j) (j' : E' →L[ℝ] (Fin 1 → ℝ) × V)
    (hj' : Function.Injective j') (hjj : ∀ v, j' v = ((A v).2, j (A v).1))
    {N : Submodule ℝ V} (hN : (LinearMap.ker (T : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N)
    {N' : Submodule ℝ ((Fin 1 → ℝ) × V)}
    (hN' : (LinearMap.ker ((extConjOp A Γ T : E' →L[ℝ] F') : E' →ₗ[ℝ] F')).map
      (j' : E' →ₗ[ℝ] (Fin 1 → ℝ) × V) = N')
    {k : ℕ} (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] N)
    (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N')
    (hι : ∀ s w, ((ι' (consE s w) : N') : (Fin 1 → ℝ) × V) = ((fun _ => s), (ι w : V)))
    (r : Module.Ray ℝ (fredholmDet T)) :
    pullOr finrank_euclideanSpace_fin ι'
        (surjRay hTs' j' hj' hN' (Module.Ray.map (extConjDetFirst A Γ hT hT') r)) =
        stdOrientation (k + 1) ↔
      pullOr finrank_euclideanSpace_fin ι (surjRay hTs j hj hN r) = stdOrientation k := by
  have := ι.finiteDimensional
  have := ι'.finiteDimensional
  set L₀ := N.map (ContinuousLinearMap.inl ℝ V (Fin 0 → ℝ) : V →ₗ[ℝ] V × (Fin 0 → ℝ))
    with hL₀
  have : FiniteDimensional ℝ L₀ := (inlEquiv (N := N) (L := L₀) rfl).finiteDimensional
  set Λ := SubspaceFamily.constUnit L₀ with hΛdef
  have hΛ : Λ.L PUnit.unit = L₀ := rfl
  have hLeq : Λ.L PUnit.unit = (LinearMap.ker ((T.coprod (0 : (Fin 0 → ℝ) →L[ℝ] F) :
      E × (Fin 0 → ℝ) →L[ℝ] F) : E × (Fin 0 → ℝ) →ₗ[ℝ] F)).map
      ((j.prodMap (ContinuousLinearMap.id ℝ (Fin 0 → ℝ)) :
        E × (Fin 0 → ℝ) →L[ℝ] V × (Fin 0 → ℝ)) : E × (Fin 0 → ℝ) →ₗ[ℝ] V × (Fin 0 → ℝ)) := by
    rw [hΛ, hL₀, map_ker_coprod_fin_zero, hN]
  have hΛ' : N'.map (ContinuousLinearMap.inl ℝ ((Fin 1 → ℝ) × V) (Fin 0 → ℝ) :
      (Fin 1 → ℝ) × V →ₗ[ℝ] ((Fin 1 → ℝ) × V) × (Fin 0 → ℝ)) = Λ.prodLine.L PUnit.unit := by
    rw [← hN', ← map_ker_coprod_fin_zero (extConjOp A Γ T) (0 : (Fin 0 → ℝ) →L[ℝ] F') j',
      ← map_ker_extConjOp_eq A Γ T (0 : (Fin 0 → ℝ) →L[ℝ] F) (0 : (Fin 0 → ℝ) →L[ℝ] F')
        (fun μ => by simp) j j' hjj, ← hLeq]
    rfl
  have key := surjRay_extConjDetFirst A Γ hT hT' hTs hTs' j hj j' hj' hjj hN hN' Λ hΛ hΛ' r
  have hdim : 1 + finrank ℝ (Λ.L PUnit.unit) = finrank ℝ (Λ.prodLine.L PUnit.unit) := by
    rw [Λ.finrank_eq, Λ.prodLine.finrank_eq]; rfl
  have hι2 : ∀ s w, (ι'.trans (inlEquiv hΛ')) (consE s w) =
      s • Λ.prodLineEr PUnit.unit + Λ.prodLineJr PUnit.unit ((ι.trans (inlEquiv hΛ.symm)) w) := by
    intro s w
    apply Subtype.ext
    change (((ι' (consE s w) : N') : (Fin 1 → ℝ) × V), (0 : Fin 0 → ℝ)) =
      s • prodLineE V 0 + prodLineJ V 0 ((ι w : V), 0)
    rw [hι]
    refine Prod.ext (Prod.ext (funext fun i => ?_) ?_) (Subsingleton.elim _ _)
    · simp [prodLineE]
    · simp [prodLineE]
  rw [← pullOr_trans finrank_euclideanSpace_fin ι' (inlEquiv hΛ'), key,
    ← pullOr_trans finrank_euclideanSpace_fin ι (inlEquiv hΛ.symm) (surjRay hTs j hj hN r)]
  exact pullOr_wedgeExtLeft_eq_std_iff (ι.trans (inlEquiv hΛ.symm)) (ι'.trans (inlEquiv hΛ'))
    (Λ.prodLineJr PUnit.unit) (Λ.prodLineEr PUnit.unit) hdim hι2
    (Λ.prodLineWedgeEquiv PUnit.unit) (fun _ => rfl) _

end Operators

end Polyfold
