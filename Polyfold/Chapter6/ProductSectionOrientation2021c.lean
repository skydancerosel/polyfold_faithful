import Polyfold.Chapter6.ProductSectionOrientation2021b
import Polyfold.Chapter6.OrientationMainClean
import Polyfold.Chapter5.CylinderPerturbation2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19** (preprint Remark 6.42, p. 230), the orientation of `f̂(x, t) = f(x) + s(x, t)`
over `X × [0, 1]` as an orientation of the section `f̂` (Definition 6.6.16).

# The lift of push-forward data from `X` to `ℝ¹ × X`

## What is formalized

* `liftProd S`: for a section `S` of `π*P` over `ℝ¹ × X`, the section
  `(τ, (t, x)) ↦ S(τ, x)` of the pull-back of `π*P` to `ℝ¹ × (ℝ¹ × X)`; it is sc⁺ when `S` is
  (`isScPlusSection_liftProd`), and its slices are the `t`-constant lifts of the slices of `S`
  (`pullbackSlice_liftProd`).
-/

open Module TensorProduct Bundle Topology Set Filter

noncomputable section

namespace Polyfold

universe u v

/-! ### Sections pulled back along `(τ, (t, x)) ↦ (τ, x)` -/

section LiftProd

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **`Ŝ(τ, (t, x)) = S(τ, x)`**: a section `S` of `π*P` over `ℝᵐ × X` pulled back to
`ℝᵐ × (ℝⁿ × X)` along `(τ, (t, x)) ↦ (τ, x)`, as a section of the pull-back of `π*P → ℝⁿ × X`. -/
def liftProd {m n : ℕ} (S : (Fin m → ℝ) × X → pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))
    (hS : IsSection (pullbackProj P Prod.snd) S) :
    (Fin m → ℝ) × ((Fin n → ℝ) × X) →
      pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
        (Prod.snd : (Fin m → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X) :=
  pullbackLift Prod.snd
    (fun w => paramLift (n := n) (pullbackSlice S w.1) (hS.pullbackSlice w.1) w.2) fun _ => rfl

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The slices of `Ŝ` are the `t`-constant lifts of the slices of `S`. -/
theorem pullbackSlice_liftProd {m n : ℕ}
    (S : (Fin m → ℝ) × X → pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))
    (hS : IsSection (pullbackProj P Prod.snd) S) (τ : Fin m → ℝ) :
    pullbackSlice (liftProd (n := n) S hS) τ =
      paramLift (n := n) (pullbackSlice S τ) (hS.pullbackSlice τ) :=
  rfl

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
theorem isSection_liftProd {m n : ℕ}
    (S : (Fin m → ℝ) × X → pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))
    (hS : IsSection (pullbackProj P Prod.snd) S) :
    IsSection (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X)) Prod.snd)
      (liftProd (n := n) S hS) :=
  isSection_pullbackLift _

/-- The sc-operator `ℝᵐ ⊕ (ℝⁿ ⊕ E) → ℝᵐ ⊕ E`, `(a, (b, u)) ↦ (a, u)`. -/
def rnDropOp (m n : ℕ) (E : ScBanach) :
    ScOperator ((rnSc m).prod ((rnSc n).prod E)) ((rnSc m).prod E) where
  lvl k := (ContinuousLinearMap.fst ℝ (Fin m → ℝ) ((Fin n → ℝ) × E k)).prod
    ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (E k)).comp
      (ContinuousLinearMap.snd ℝ (Fin m → ℝ) ((Fin n → ℝ) × E k)))
  incl_comm _ _ := rfl

/-- **`Ŝ` is an sc⁺-section** when `S` is: in the product charts over a chart `c` of `P`, its
representative is that of `S` composed with `(a, (b, u)) ↦ (a, u)`. -/
theorem isScPlusSection_liftProd {m n : ℕ}
    [ParacompactSpace ((Fin m → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]
    [ParacompactSpace ((Fin n → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    [ParacompactSpace ((Fin m → ℝ) × ((Fin n → ℝ) × X))]
    [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin m → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
    {S : (Fin m → ℝ) × X → pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsScPlusSection S) :
    ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold m) ((rnPolyfold n).prod PX))).IsScPlusSection
      (liftProd (n := n) S hS.1) := by
  set S' := liftProd (n := n) S hS.1 with hS'
  have hsec : IsSection (pullbackProj (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      Prod.snd) S' := isSection_pullbackLift _
  refine StrongBundle.isScPlusSection_of_local hsec fun z => ?_
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem B z.2.2
  -- the product charts at `z = (τ, (t, x))` and at `(τ, x)`
  set c₁ := (PullbackChartData.ofProd c z.2.1).toChart (S' z).1.2 with hc₁
  set c' := (PullbackChartData.ofProd c₁ z.1).toChart (S' z) with hc'
  set pc := (PullbackChartData.ofProd c z.1).toChart (S (z.1, z.2.2)) with hpc
  have hmem₁ : c₁ ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).atlas.charts :=
    ⟨_, _, hc, rfl⟩
  have hmem' : c' ∈ ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold m) ((rnPolyfold n).prod PX))).atlas.charts :=
    ⟨_, _, hmem₁, rfl⟩
  have hmem : pc ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).atlas.charts :=
    ⟨_, _, hc, rfl⟩
  obtain ⟨hrange, hsm⟩ := hS.2 pc hmem
  have hsrc : ∀ w ∈ c'.φ.source, ((w.1, w.2.2) : (Fin m → ℝ) × X) ∈ pc.φ.source :=
    fun w hw => ⟨mem_univ _, hw.2.2⟩
  refine ⟨c', hmem', ⟨mem_univ _, mem_univ _, hxc⟩, fun w hw => hrange _ (hsrc w hw), ?_⟩
  have hO : IsScRetract c'.φ.model.E c'.φ.model.C c'.φ.model.O := c'.φ.model.isScRetract
  have hT : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O pc.φ.model.E
      pc.φ.model.C pc.φ.model.O (rnDropOp m n c.φ.model.E 0) :=
    (rnDropOp m n c.φ.model.E).isScSmoothRetractMap hO fun p hp =>
      show ((p.1, p.2.2) : (Fin m → ℝ) × c.φ.model.E 0) ∈ univ ×ˢ c.φ.model.O from
        ⟨mem_univ _, hp.2.2⟩
  have hcomp := hsm.comp hT pc.φ.model.isScRetract
  refine ⟨fun w hw => ?_, fun R hR => ?_⟩
  · have hws := c'.φ.symm_mapsTo hw
    exact c'.liftOne_mem (c'.mem_source_of_proj (by rw [hsec]; exact hws))
      (hrange _ (hsrc _ hws))
  · have hU := R.isScDomain
    have h1 := (hcomp.comp_isScSmooth R hR).snd hU
    have h2 := R.isScSmooth.scPair hU h1
    refine h2.congr hU fun w hw => ?_
    have hRw : R w ∈ c'.φ.model.O := by rw [← hR]; exact R.apply_mem_retract hw
    change (R w, (StrongBundle.localRepOne pc S (rnDropOp m n c.φ.model.E 0 (R w))).2) =
      StrongBundle.localRepOne c' S' (R w)
    generalize R w = p at hRw ⊢
    obtain ⟨a, b, u⟩ := p
    have hu : u ∈ c.φ.model.O := hRw.2.2
    set a' : Fin m → ℝ := a
    set b' : Fin n → ℝ := b
    change ((a', (b', u)),
        Function.invFun (c.F.toBase 1) (c (S (a' + z.1, c.φ.symm u)).1.2).2) =
      ((a' + z.1 - z.1, (b' + z.2.1 - z.2.1, c.φ (c.φ.symm u))),
        Function.invFun (c.F.toBase 1) (c (S (a' + z.1, c.φ.symm u)).1.2).2)
    rw [c.φ.apply_symm_apply hu, add_sub_cancel_right, add_sub_cancel_right]

end LiftProd

/-! ### The stabilization of `L̂ = Γ⁻¹ (L ⊕ 0) A` -/

section ExtConjStab

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  (A : E' ≃L[ℝ] E × (Fin 1 → ℝ)) (Γ : F' ≃L[ℝ] F) {T : E →L[ℝ] F} {k : ℕ}
  {φ : (Fin k → ℝ) →L[ℝ] F} {φ' : (Fin k → ℝ) →L[ℝ] F'}

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- **`ker(L̂ ⊕ φ̂) ≅ ker(L̃ ⊕ φ)`** by `A × 1`, for `φ = Γ φ̂`. -/
def extConjKerEquiv (hφφ : ∀ μ, φ μ = Γ (φ' μ)) :
    LinearMap.ker (((extConjOp A Γ T).coprod φ' : E' × (Fin k → ℝ) →L[ℝ] F') :
        E' × (Fin k → ℝ) →ₗ[ℝ] F') ≃ₗ[ℝ]
      LinearMap.ker (((extOp T).coprod φ : (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →L[ℝ] F) :
        (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →ₗ[ℝ] F) :=
  conjKerEquiv (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin k → ℝ))) Γ
    (coprod_conj A Γ (extConjOp_conj A Γ T) hφφ)

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
theorem coe_extConjKerEquiv_symm (hφφ : ∀ μ, φ μ = Γ (φ' μ))
    (w : LinearMap.ker (((extOp T).coprod φ : (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →L[ℝ] F) :
        (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →ₗ[ℝ] F)) :
    (((extConjKerEquiv A Γ hφφ).symm w : _) : E' × (Fin k → ℝ)) =
      (A.symm (w : (E × (Fin 1 → ℝ)) × (Fin k → ℝ)).1,
        (w : (E × (Fin 1 → ℝ)) × (Fin k → ℝ)).2) := rfl

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- `conjDet ∘ extConjDetFirst = extDetFirst` on rays. -/
theorem ray_map_conjDet_extConjDetFirst (hT : T.IsFredholm)
    (hT' : (extConjOp A Γ T).IsFredholm) (r : Module.Ray ℝ (fredholmDet T)) :
    Module.Ray.map (conjDet A Γ (extConjOp_conj A Γ T))
        (Module.Ray.map (extConjDetFirst A Γ hT hT') r) =
      Module.Ray.map (extDetFirst hT) r := by
  induction r using Module.Ray.ind with | h v hv => ?_
  refine (congrArg (Module.Ray.map (conjDet A Γ (extConjOp_conj A Γ T)))
    (Module.Ray.map_apply _ _ _)).trans ?_
  refine (Module.Ray.map_apply _ _ _).trans (Eq.trans ?_ (Module.Ray.map_apply _ _ _).symm)
  refine rayOfNeZero_eq_of_eq _ _ ?_
  have h := extConjDetFirst_apply A Γ hT hT' v
  exact (congrArg (conjDet A Γ (extConjOp_conj A Γ T)) h).trans
    ((conjDet A Γ (extConjOp_conj A Γ T)).apply_symm_apply _)

omit [CompleteSpace E'] [CompleteSpace F'] in
/-- **The stabilization isomorphism and `h ↦ e ∧ h`, for `L̂ = Γ⁻¹ (L ⊕ 0) A`**: with the kernels
of `L̂ ⊕ φ̂` and `L̃ ⊕ φ` identified by `A × 1`, reading `extConjDetFirst r` in
`λ(ker(L̂ ⊕ φ̂))` is `Ψ` of reading `r` in `λ(ker(L ⊕ φ))`, for every `Ψ` which is
`w ↦ ê ∧ j(w)` through the identifications (`stabRayEquiv_conjDet`,
`stabRayEquiv_extDetFirst`). -/
theorem stabRayEquiv_extConjDetFirst (hφφ : ∀ μ, φ μ = Γ (φ' μ)) (hT : T.IsFredholm)
    (hT' : (extConjOp A Γ T).IsFredholm) (hφ : Function.Surjective (T.coprod φ))
    (hφ' : Function.Surjective ((extConjOp A Γ T).coprod φ'))
    {W W' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W']
    {L₀ : Submodule ℝ W} {L₀' : Submodule ℝ W'} [FiniteDimensional ℝ L₀]
    [FiniteDimensional ℝ L₀']
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] L₀)
    (ι' : LinearMap.ker (((extConjOp A Γ T).coprod φ' : E' × (Fin k → ℝ) →L[ℝ] F') :
        E' × (Fin k → ℝ) →ₗ[ℝ] F') ≃ₗ[ℝ] L₀')
    (Ψ : maxPow L₀ ≃ₗ[ℝ] maxPow L₀')
    (hΨ : ∀ w, Ψ (maxPowEquiv ι w) =
      maxPowEquiv ((extConjKerEquiv A Γ hφφ).symm.trans ι') (extStabWedge hT w))
    (r : Module.Ray ℝ (fredholmDet T)) :
    stabRayEquiv hT' hφ' ι' (Module.Ray.map (extConjDetFirst A Γ hT hT') r) =
      Module.Ray.map Ψ (stabRayEquiv hT hφ ι r) := by
  have h1 := stabRayEquiv_conjDet A Γ (extConjOp_conj A Γ T) hφφ hT' (isFredholm_extOp hT) hφ'
    (surjective_coprod_extOp hφ) ι' ((extConjKerEquiv A Γ hφφ).symm.trans ι')
    (LinearEquiv.refl ℝ L₀')
    (fun v => congrArg ι' ((extConjKerEquiv A Γ hφφ).symm_apply_apply v))
    (Module.Ray.map (extConjDetFirst A Γ hT hT') r)
  have h2 := stabRayEquiv_extDetFirst hT hφ ι ((extConjKerEquiv A Γ hφφ).symm.trans ι') Ψ hΨ r
  have h3 := ray_map_conjDet_extConjDetFirst A Γ hT hT' r
  have h4 : ∀ x : Module.Ray ℝ (maxPow L₀'),
      Module.Ray.map (maxPowEquiv (LinearEquiv.refl ℝ L₀')) x = x := fun x => by
    rw [maxPowEquiv_refl]
    induction x using Module.Ray.ind with | h v hv => rfl
  exact ((h4 _).symm.trans h1.symm).trans ((congrArg (stabRayEquiv (isFredholm_extOp hT)
    (surjective_coprod_extOp hφ) ((extConjKerEquiv A Γ hφφ).symm.trans ι')) h3).trans h2)

omit [CompleteSpace E] [CompleteSpace F] in
/-- **`w ↦ ê ∧ j(w)` read through identifications of the kernels**: if `ι₂ ê = e'` and
`ι₂ ∘ j = M ∘ ι`, then `e' ∧ M(λ(ι) w) = λ(ι₂)(ê ∧ j(w))`. -/
theorem wedgeExtLeft_maxPowEquiv_eq (hT : T.IsFredholm)
    {W W' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W']
    {L₀ : Submodule ℝ W} {L₀' : Submodule ℝ W'} [FiniteDimensional ℝ L₀]
    [FiniteDimensional ℝ L₀']
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] L₀)
    (ι₂ : LinearMap.ker (((extOp T).coprod φ : (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →L[ℝ] F) :
      (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →ₗ[ℝ] F) ≃ₗ[ℝ] L₀')
    (M : L₀ →ₗ[ℝ] L₀') (e' : L₀') (h : 1 + finrank ℝ L₀ = finrank ℝ L₀')
    (hE : ι₂ (extStabE T φ) = e') (hJ : ∀ x, ι₂ (extStabJ T φ x) = M (ι x))
    (w : maxPow (LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F))) :
    wedgeExtLeft M ![e'] h (maxPowEquiv ι w) = maxPowEquiv ι₂ (extStabWedge hT w) := by
  have := hT.finite_ker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  have key : (wedgeExtLeft M ![e'] h) ∘ₗ (maxPowEquiv ι).toLinearMap =
      (maxPowEquiv ι₂).toLinearMap ∘ₗ extStabWedge hT := by
    refine maxPow_linearMap_ext (Module.finBasis ℝ _) rfl ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [maxPowEquiv_wedge, wedgeExtLeft_wedge, extStabWedge, wedgeExtLeft_wedge,
      maxPowEquiv_wedge]
    refine wedge_congr_fun ?_ _ _
    funext i
    induction i using Fin.addCases with
    | left i =>
      fin_cases i
      simp only [Fin.append_left, Function.comp_apply]
      exact hE.symm
    | right j =>
      simp only [Fin.append_right, Function.comp_apply]
      exact (hJ _).symm
  exact LinearMap.congr_fun key w

end ExtConjStab

/-! ### The family `ℝ × Λ` -/

section ProdLine

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}

variable (V k) in
/-- `((σ, v), μ) ↦ (v, μ)`. -/
def prodLinePr : ((Fin 1 → ℝ) × V) × (Fin k → ℝ) →L[ℝ] V × (Fin k → ℝ) :=
  ((ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) V).comp
    (ContinuousLinearMap.fst ℝ ((Fin 1 → ℝ) × V) (Fin k → ℝ))).prod
    (ContinuousLinearMap.snd ℝ ((Fin 1 → ℝ) × V) (Fin k → ℝ))

variable (V k) in
/-- `(v, μ) ↦ ((0, v), μ)`. -/
def prodLineJ : V × (Fin k → ℝ) →L[ℝ] ((Fin 1 → ℝ) × V) × (Fin k → ℝ) :=
  ((ContinuousLinearMap.inr ℝ (Fin 1 → ℝ) V).comp
    (ContinuousLinearMap.fst ℝ V (Fin k → ℝ))).prod (ContinuousLinearMap.snd ℝ V (Fin k → ℝ))

variable (V k) in
/-- `((σ, v), μ) ↦ σ`. -/
def prodLineC : ((Fin 1 → ℝ) × V) × (Fin k → ℝ) →L[ℝ] (Fin 1 → ℝ) :=
  (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) V).comp
    (ContinuousLinearMap.fst ℝ ((Fin 1 → ℝ) × V) (Fin k → ℝ))

variable (V k) in
/-- `ê = ((1, 0), 0)`. -/
def prodLineE : ((Fin 1 → ℝ) × V) × (Fin k → ℝ) := ((fun _ => 1, 0), 0)

@[simp] theorem prodLinePr_apply (w : ((Fin 1 → ℝ) × V) × (Fin k → ℝ)) :
    prodLinePr V k w = (w.1.2, w.2) := rfl

@[simp] theorem prodLineJ_apply (w : V × (Fin k → ℝ)) : prodLineJ V k w = ((0, w.1), w.2) := rfl

@[simp] theorem prodLineC_apply (w : ((Fin 1 → ℝ) × V) × (Fin k → ℝ)) :
    prodLineC V k w = w.1.1 := rfl

theorem prodLineC_E : prodLineC V k (prodLineE V k) = Pi.single 0 1 := by
  funext i
  rw [Subsingleton.elim i 0]
  simp [prodLineE]

theorem prodLinePr_E : prodLinePr V k (prodLineE V k) = 0 := rfl

theorem prodLineJ_injective : Function.Injective (prodLineJ V k) := fun x y h => by
  have h1 := congrArg (fun w : ((Fin 1 → ℝ) × V) × (Fin k → ℝ) => w.1.2) h
  have h2 := congrArg (fun w : ((Fin 1 → ℝ) × V) × (Fin k → ℝ) => w.2) h
  exact Prod.ext h1 h2

namespace SubspaceFamily

variable {Q : Type*} [TopologicalSpace Q] (Λ : SubspaceFamily Q (V × (Fin k → ℝ)))

/-- The members of `ℝ × Λ`: `{((σ, v), μ) | (v, μ) ∈ Λ_q}`. -/
def prodLineL (q : Q) : Submodule ℝ (((Fin 1 → ℝ) × V) × (Fin k → ℝ)) :=
  (Λ.L q).comap (prodLinePr V k : ((Fin 1 → ℝ) × V) × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ))

theorem mem_prodLineL {q : Q} {w : ((Fin 1 → ℝ) × V) × (Fin k → ℝ)} :
    w ∈ Λ.prodLineL q ↔ (w.1.2, w.2) ∈ Λ.L q := Iff.rfl

/-- `Λ_q × ℝ ≅ (ℝ × Λ)_q`. -/
def prodLineEquiv (q : Q) : (Λ.L q × (Fin 1 → ℝ)) ≃ₗ[ℝ] Λ.prodLineL q where
  toFun w := ⟨((w.2, (w.1 : V × (Fin k → ℝ)).1), (w.1 : V × (Fin k → ℝ)).2), w.1.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := (⟨((x : ((Fin 1 → ℝ) × V) × (Fin k → ℝ)).1.2,
    (x : ((Fin 1 → ℝ) × V) × (Fin k → ℝ)).2), x.2⟩, (x : ((Fin 1 → ℝ) × V) × (Fin k → ℝ)).1.1)
  left_inv _ := rfl
  right_inv _ := rfl

theorem finiteDimensional_prodLineL (q : Q) : FiniteDimensional ℝ (Λ.prodLineL q) :=
  (Λ.prodLineEquiv q).finiteDimensional

theorem finrank_prodLineL (q : Q) : finrank ℝ (Λ.prodLineL q) = 1 + Λ.n := by
  rw [← (Λ.prodLineEquiv q).finrank_eq, Module.finrank_prod, Λ.finrank_eq,
    Module.finrank_fin_fun, add_comm]

/-- The frame `ê, J(e₁), …, J(eₙ)` of `ℝ × Λ` made from a frame of `Λ`. -/
def prodLineFrameFun (e : Fin Λ.n → Q → V × (Fin k → ℝ)) :
    Fin (1 + Λ.n) → Q → ((Fin 1 → ℝ) × V) × (Fin k → ℝ) :=
  fun i q => Fin.append (fun _ : Fin 1 => prodLineE V k) (fun j => prodLineJ V k (e j q)) i

theorem prodLineFrameFun_continuousOn {e : Fin Λ.n → Q → V × (Fin k → ℝ)} {U : Set Q}
    (he : ∀ i, ContinuousOn (e i) U) (i : Fin (1 + Λ.n)) :
    ContinuousOn (Λ.prodLineFrameFun e i) U := by
  unfold prodLineFrameFun
  induction i using Fin.addCases with
  | left i => simp only [Fin.append_left]; exact continuousOn_const
  | right j =>
    simp only [Fin.append_right]
    exact (prodLineJ V k).continuous.comp_continuousOn (he j)

theorem prodLineFrameFun_mem {e : Fin Λ.n → Q → V × (Fin k → ℝ)} {q : Q}
    (he : ∀ i, e i q ∈ Λ.L q) (i : Fin (1 + Λ.n)) : Λ.prodLineFrameFun e i q ∈ Λ.prodLineL q := by
  unfold prodLineFrameFun
  induction i using Fin.addCases with
  | left i => simp only [Fin.append_left]; exact (Λ.L q).zero_mem
  | right j => simp only [Fin.append_right]; exact he j

theorem prodLineFrameFun_linearIndependent {e : Fin Λ.n → Q → V × (Fin k → ℝ)} {q : Q}
    (he : LinearIndependent ℝ fun i => e i q) :
    LinearIndependent ℝ fun i => Λ.prodLineFrameFun e i q := by
  have h := linearIndependent_single_append
    ((prodLineC V k : ((Fin 1 → ℝ) × V) × (Fin k → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))
    (he.map' (prodLineJ V k : V × (Fin k → ℝ) →ₗ[ℝ] ((Fin 1 → ℝ) × V) × (Fin k → ℝ))
      (LinearMap.ker_eq_bot.2 prodLineJ_injective)) (fun i => rfl) (e := prodLineE V k)
      prodLineC_E
  have hfun : (fun i => Λ.prodLineFrameFun e i q) =
      Fin.append ![prodLineE V k] ((prodLineJ V k : V × (Fin k → ℝ) →ₗ[ℝ]
        ((Fin 1 → ℝ) × V) × (Fin k → ℝ)) ∘ fun i => e i q) := by
    funext i
    unfold prodLineFrameFun
    induction i using Fin.addCases with
    | left i => fin_cases i; simp only [Fin.append_left]; rfl
    | right j => simp only [Fin.append_right]; rfl
  rw [hfun]
  exact h

/-- **The family `ℝ × Λ`** of the subspaces `{((σ, v), μ) | (v, μ) ∈ Λ_q}` of
`(ℝ¹ × V) × ℝᵏ`, of dimension `1 + dim Λ` (the stabilized kernels of `f̂` along a path are
`ℝ ×` those of `f`). -/
def prodLine : SubspaceFamily Q (((Fin 1 → ℝ) × V) × (Fin k → ℝ)) where
  L := Λ.prodLineL
  n := 1 + Λ.n
  finiteDimensional := Λ.finiteDimensional_prodLineL
  finrank_eq := Λ.finrank_prodLineL
  exists_frame q₀ := by
    obtain ⟨U, hU, hq₀, e, he, h⟩ := Λ.exists_frame q₀
    exact ⟨U, hU, hq₀, Λ.prodLineFrameFun e, Λ.prodLineFrameFun_continuousOn he, fun q hq =>
      ⟨Λ.prodLineFrameFun_mem (h q hq).1, Λ.prodLineFrameFun_linearIndependent (h q hq).2⟩⟩

@[simp] theorem prodLine_L (q : Q) : Λ.prodLine.L q = Λ.prodLineL q := rfl

@[simp] theorem prodLine_n : Λ.prodLine.n = 1 + Λ.n := rfl

/-- The frame of `ℝ × Λ` over the domain of a frame of `Λ`. -/
def Frame.prodLine {Λ : SubspaceFamily Q (V × (Fin k → ℝ))} (ε : Λ.Frame) : Λ.prodLine.Frame where
  U := ε.U
  isOpen := ε.isOpen
  e := Λ.prodLineFrameFun ε.e
  continuousOn := Λ.prodLineFrameFun_continuousOn ε.continuousOn
  mem q hq := Λ.prodLineFrameFun_mem (ε.mem q hq)
  linearIndependent q hq := Λ.prodLineFrameFun_linearIndependent (ε.linearIndependent q hq)

/-- `J` on the members: `Λ_q → (ℝ × Λ)_q`. -/
def prodLineJr (q : Q) : Λ.L q →ₗ[ℝ] Λ.prodLine.L q :=
  (prodLineJ V k : V × (Fin k → ℝ) →ₗ[ℝ] ((Fin 1 → ℝ) × V) × (Fin k → ℝ)).restrict
    (p := Λ.L q) (q := Λ.prodLineL q) fun _ hv => hv

/-- `ê` as a member of `(ℝ × Λ)_q`. -/
def prodLineEr (q : Q) : Λ.prodLine.L q := ⟨prodLineE V k, (Λ.L q).zero_mem⟩

/-- **`λ(Λ_q) → λ((ℝ × Λ)_q)`, `w ↦ ê ∧ J(w)`** (the 2021 convention, the new vector first). -/
def prodLineWedge (q : Q) : maxPow (Λ.L q) →ₗ[ℝ] maxPow (Λ.prodLine.L q) :=
  wedgeExtLeft (Λ.prodLineJr q) ![Λ.prodLineEr q]
    (by rw [Λ.finrank_eq, Λ.prodLine.finrank_eq]; rfl)

theorem prodLineWedge_wedgeAt (ε : Λ.Frame) {q : Q} (hq : q ∈ ε.U) :
    Λ.prodLineWedge q (ε.wedgeAt q) = ε.prodLine.wedgeAt q := by
  rw [ε.wedgeAt_of_mem hq, ε.prodLine.wedgeAt_of_mem hq]
  refine (wedgeExtLeft_wedge _ _ _ _ _).trans (wedge_congr_fun ?_ _ _)
  funext i
  apply Subtype.ext
  change _ = Fin.append (fun _ : Fin 1 => prodLineE V k) (fun j => prodLineJ V k (ε.e j q)) i
  induction i using Fin.addCases with
  | left i => fin_cases i; simp only [Fin.append_left]; rfl
  | right j => simp only [Fin.append_right]; rfl

theorem prodLineWedge_bijective (q : Q) : Function.Bijective (Λ.prodLineWedge q) := by
  refine bijective_of_apply_ne_zero_of_finrank_eq_one finrank_maxPow finrank_maxPow
    (Λ.prodLineWedge q) (v := (Λ.frameAt q).wedgeAt q) ?_
  rw [Λ.prodLineWedge_wedgeAt _ (Λ.mem_frameAt q)]
  exact (Λ.frameAt q).prodLine.wedgeAt_ne_zero (Λ.mem_frameAt q)

/-- `w ↦ ê ∧ J(w)` as an isomorphism of lines. -/
def prodLineWedgeEquiv (q : Q) : maxPow (Λ.L q) ≃ₗ[ℝ] maxPow (Λ.prodLine.L q) :=
  LinearEquiv.ofBijective (Λ.prodLineWedge q) (Λ.prodLineWedge_bijective q)

/-- **`w ↦ ê ∧ J(w)` carries continuous orientations of `λ(Λ)` to continuous orientations of
`λ(ℝ × Λ)`** (in the frames `ê, J(e)` the coordinate is that in the frame `e`). -/
theorem isLineOrientation_prodLine (o : LineOrientation Λ.det) :
    IsLineOrientation Λ.prodLine.det fun q => Module.Ray.map (Λ.prodLineWedgeEquiv q) (o q) := by
  intro q₀
  obtain ⟨U, hU, σ, hσ, hσo⟩ := o.2 q₀
  refine ⟨U, hU, fun q => Λ.prodLineWedge q (σ q), fun q hq => ?_, fun q hq => ?_⟩
  · set ε := Λ.frameAt q
    have hqε : q ∈ ε.U := Λ.mem_frameAt q
    have hkey : ∀ b ∈ ε.U, Λ.prodLineWedge b (σ b) = ε.coord b (σ b) • ε.prodLine.wedgeAt b := by
      intro b hb
      have h1 := ε.coord_smul_wedgeAt hb (σ b)
      calc Λ.prodLineWedge b (σ b) = Λ.prodLineWedge b (ε.coord b (σ b) • ε.wedgeAt b) := by
            rw [h1]
        _ = ε.coord b (σ b) • Λ.prodLineWedge b (ε.wedgeAt b) := LinearMap.map_smul _ _ _
        _ = _ := congrArg (ε.coord b (σ b) • ·) (Λ.prodLineWedge_wedgeAt ε hb)
    refine (Λ.prodLine.continuousWithinAt_section_iff ε.prodLine hqε).2 ?_
    refine ((Λ.continuousWithinAt_section_iff ε hqε).1 (hσ q hq)).congr_of_eventuallyEq ?_ ?_
    · exact eventually_nhdsWithin_of_eventually_nhds (Filter.eventually_of_mem
        (ε.isOpen.mem_nhds hqε) fun b hb => by
          change ε.prodLine.coord b (Λ.prodLineWedge b (σ b)) = _
          rw [hkey b hb, map_smul, ε.prodLine.coord_wedgeAt hb, smul_eq_mul, mul_one])
    · rw [hkey q hqε, map_smul, ε.prodLine.coord_wedgeAt hqε, smul_eq_mul, mul_one]
  · obtain ⟨h0, hoq⟩ := hσo q hq
    exact ⟨(Λ.prodLineWedgeEquiv q).map_ne_zero_iff.2 h0,
      (congrArg (Module.Ray.map (Λ.prodLineWedgeEquiv q)) hoq).trans (Module.Ray.map_apply _ _ _)⟩

/-- **Continuation commutes with `w ↦ ê ∧ J(w)`.** -/
theorem cont_prodLine [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q] (q₀ q₁ : Q)
    (r : Module.Ray ℝ (Λ.det q₀)) :
    Λ.prodLine.cont q₀ q₁ (Module.Ray.map (Λ.prodLineWedgeEquiv q₀) r) =
      Module.Ray.map (Λ.prodLineWedgeEquiv q₁) (Λ.cont q₀ q₁ r) := by
  obtain ⟨o, rfl⟩ := exists_lineOrientation_apply_eq (L := Λ.det) q₀ r
  let o' : LineOrientation Λ.prodLine.det := ⟨_, Λ.isLineOrientation_prodLine o⟩
  exact (Λ.prodLine.cont_eq o' q₀ q₁).trans
    (congrArg (Module.Ray.map (Λ.prodLineWedgeEquiv q₁)) (Λ.cont_eq o q₀ q₁)).symm

end SubspaceFamily

section ExtConjKer

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- **`ker(L̂ ⊕ φ̂)` read in `(ℝ¹ × V) × ℝᵏ`** is `{((σ, v), μ) | (v, μ) ∈ ker(L ⊕ φ)}` read in
`V × ℝᵏ`: for `L̂ = Γ⁻¹ (L ⊕ 0) A`, `φ = Γ φ̂`, and inclusions `j : E → V`, `j' : E' → ℝ¹ × V`
with `j' = (pr₂ A, j pr₁ A)`. -/
theorem map_ker_extConjOp_eq (A : E' ≃L[ℝ] E × (Fin 1 → ℝ)) (Γ : F' ≃L[ℝ] F) (T : E →L[ℝ] F)
    (φ : (Fin k → ℝ) →L[ℝ] F) (φ' : (Fin k → ℝ) →L[ℝ] F') (hφφ : ∀ μ, φ μ = Γ (φ' μ))
    (j : E →L[ℝ] V) (j' : E' →L[ℝ] (Fin 1 → ℝ) × V)
    (hj' : ∀ v, j' v = ((A v).2, j (A v).1)) :
    ((LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
        E × (Fin k → ℝ) →ₗ[ℝ] F)).map
      ((j.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        E × (Fin k → ℝ) →L[ℝ] V × (Fin k → ℝ)) : E × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ))).comap
        (prodLinePr V k : ((Fin 1 → ℝ) × V) × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ)) =
      (LinearMap.ker (((extConjOp A Γ T).coprod φ' : E' × (Fin k → ℝ) →L[ℝ] F') :
        E' × (Fin k → ℝ) →ₗ[ℝ] F')).map
      ((j'.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        E' × (Fin k → ℝ) →L[ℝ] ((Fin 1 → ℝ) × V) × (Fin k → ℝ)) :
          E' × (Fin k → ℝ) →ₗ[ℝ] ((Fin 1 → ℝ) × V) × (Fin k → ℝ)) := by
  have hconj : ∀ u : E' × (Fin k → ℝ),
      Γ ((extConjOp A Γ T).coprod φ' u) = T (A u.1).1 + φ u.2 := fun u => by
    rw [ContinuousLinearMap.coprod_apply, map_add, ← extConjOp_conj, ← hφφ, extOp_apply]
  refine Submodule.ext fun w => ?_
  constructor
  · rintro ⟨u, hu, hue⟩
    have hu' : T u.1 + φ u.2 = 0 := hu
    have h1 : j u.1 = w.1.2 := congrArg Prod.fst hue
    have h2 : u.2 = w.2 := congrArg Prod.snd hue
    refine ⟨(A.symm (u.1, w.1.1), u.2), ?_, ?_⟩
    · change (extConjOp A Γ T).coprod φ' (A.symm (u.1, w.1.1), u.2) = 0
      apply Γ.injective
      rw [hconj, map_zero, A.apply_symm_apply]
      exact hu'
    · change ((j' (A.symm (u.1, w.1.1)), u.2) : ((Fin 1 → ℝ) × V) × (Fin k → ℝ)) = w
      rw [hj', A.apply_symm_apply]
      exact Prod.ext (Prod.ext rfl h1) h2
  · rintro ⟨u, hu, rfl⟩
    have hu' : (extConjOp A Γ T).coprod φ' u = 0 := hu
    refine ⟨((A u.1).1, u.2), ?_, ?_⟩
    · change T (A u.1).1 + φ u.2 = 0
      rw [← hconj, hu', map_zero]
    · change ((j (A u.1).1, u.2) : V × (Fin k → ℝ)) = ((j' u.1).2, u.2)
      rw [hj']

end ExtConjKer

end ProdLine

/-! ### `w ↦ ê ∧ J(w)` and the stabilization of `L̂` -/

section ProdLineCompat

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
  {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  {Q : Type*} [TopologicalSpace Q]

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- **The map `w ↦ ê ∧ J(w)` of the family `ℝ × Λ` is `extStabWedge` read through the
identifications of the kernels** (`A × 1` and the inclusions `j`, `j' = (pr₂ A, j pr₁ A)`). -/
theorem prodLineWedgeEquiv_compat (A : E' ≃L[ℝ] E × (Fin 1 → ℝ)) (Γ : F' ≃L[ℝ] F)
    {T : E →L[ℝ] F} (hT : T.IsFredholm) {φ : (Fin k → ℝ) →L[ℝ] F}
    {φ' : (Fin k → ℝ) →L[ℝ] F'} (hφφ : ∀ μ, φ μ = Γ (φ' μ))
    (j : E →L[ℝ] V) (hj : Function.Injective j) (j' : E' →L[ℝ] (Fin 1 → ℝ) × V)
    (hj' : Function.Injective j') (hjj : ∀ v, j' v = ((A v).2, j (A v).1))
    (Λ : SubspaceFamily Q (V × (Fin k → ℝ))) (q : Q)
    (hL : Λ.L q = (LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
        E × (Fin k → ℝ) →ₗ[ℝ] F)).map
      ((j.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        E × (Fin k → ℝ) →L[ℝ] V × (Fin k → ℝ)) : E × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ)))
    (hL' : Λ.prodLine.L q = (LinearMap.ker (((extConjOp A Γ T).coprod φ' :
        E' × (Fin k → ℝ) →L[ℝ] F') : E' × (Fin k → ℝ) →ₗ[ℝ] F')).map
      ((j'.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        E' × (Fin k → ℝ) →L[ℝ] ((Fin 1 → ℝ) × V) × (Fin k → ℝ)) :
          E' × (Fin k → ℝ) →ₗ[ℝ] ((Fin 1 → ℝ) × V) × (Fin k → ℝ)))
    (w : maxPow (LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F))) :
    Λ.prodLineWedgeEquiv q (maxPowEquiv (kerEquivMap j hj hL) w) =
      maxPowEquiv ((extConjKerEquiv A Γ hφφ).symm.trans (kerEquivMap j' hj' hL'))
        (extStabWedge hT w) := by
  refine wedgeExtLeft_maxPowEquiv_eq hT (kerEquivMap j hj hL)
    ((extConjKerEquiv A Γ hφφ).symm.trans (kerEquivMap j' hj' hL')) (Λ.prodLineJr q)
    (Λ.prodLineEr q) (by rw [Λ.finrank_eq, Λ.prodLine.finrank_eq]; rfl) ?_ (fun x => ?_) w
  · apply Subtype.ext
    change ((j' (A.symm (0, fun _ => 1)), (0 : Fin k → ℝ)) :
      ((Fin 1 → ℝ) × V) × (Fin k → ℝ)) = prodLineE V k
    rw [hjj, A.apply_symm_apply]
    exact Prod.ext (Prod.ext rfl (map_zero j)) rfl
  · apply Subtype.ext
    change ((j' (A.symm ((x : E × (Fin k → ℝ)).1, 0)), (x : E × (Fin k → ℝ)).2) :
      ((Fin 1 → ℝ) × V) × (Fin k → ℝ)) =
        ((0, j (x : E × (Fin k → ℝ)).1), (x : E × (Fin k → ℝ)).2)
    rw [hjj, A.apply_symm_apply]

end ProdLineCompat

/-! ### The stabilized kernels of `f̃` along a path of `ℝ¹ × X` -/

section ProdKernels

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] {f : X → Y}

variable (B) in
/-- The pull-back `π*P` of `P` to `ℝ¹ × X`. -/
abbrev prodBundle : StrongBundle ((rnPolyfold 1).prod PX)
    (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X)) :=
  B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)

/-- The product chart `(r ↦ r) × φ` of `π*P` over a chart `c` of `P`. -/
abbrev prodChart (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) :
    StrongBundleChart ((rnPolyfold 1).prod PX) (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X)) :=
  (PullbackChartData.ofProd c 0).toChart q₀

theorem isChart_prodChart {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) :
    (prodBundle B).IsChart (prodChart c q₀) :=
  (PullbackChartData.ofProd c 0).isChart_toChart B _ hc q₀

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
theorem mem_prodChart_source {c : StrongBundleChart PX P}
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) {x : X} (hx : x ∈ c.φ.source)
    (t : Fin 1 → ℝ) : ((t, x) : (Fin 1 → ℝ) × X) ∈ (prodChart c q₀).φ.source :=
  ⟨mem_univ _, hx⟩

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
/-- `f̃ + s̃ = (f + s)~` for the `t`-constant lifts. -/
theorem sectionAdd_paramLift {g s : X → Y} (hg : IsSection P g) (hs : IsSection P s) :
    sectionAdd (pullbackProj P Prod.snd) (paramLift (n := 1) g hg) (paramLift (n := 1) s hs) =
      paramLift (n := 1) (sectionAdd P g s) (hg.sectionAdd hs) :=
  eq_of_pullbackSlice_eq ((isSection_pullbackLift _).sectionAdd (isSection_pullbackLift _))
    (isSection_pullbackLift _) fun τ =>
      pullbackSlice_sectionAdd_paramLift hg (isSection_pullbackLift _) τ

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
/-- The `t`-constant lift is `constLift`. -/
theorem paramLift_eq_constLift {s : X → Y} (hs : IsSection P s) :
    paramLift (n := 1) s hs = constLift s hs :=
  eq_of_pullbackSlice_eq (isSection_pullbackLift _) (isSection_constLift s hs) fun τ =>
    (pullbackSlice_constLift s hs τ).symm

/-- **The `t`-constant lift of an sc⁺-section is an sc⁺-section** of `π*P`. -/
theorem isScPlusSection_paramLift {s : X → Y} (hs : B.IsScPlusSection s) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection
      (paramLift (n := 1) s hs.1) := by
  rw [paramLift_eq_constLift]
  exact isScPlusSection_constLift hs

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (t : Fin 1 → ℝ)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))

/-- **The linearization of `g̃` in the product chart point** is `(σ, v) ↦ g'(x) v`
(`StrongBundle.scDeriv_paramSection_apply`). -/
theorem linAt_prodPt_paramLift {g : X → Y} (hg : B.IsScSmoothSection g)
    (v : ↥(p.prodPt t q₀).T) :
    linAt (p.prodPt t q₀).c.U (p.prodPt t q₀).c.R
        ((p.prodPt t q₀).c.principal (paramLift (n := 1) g hg.1)) (p.prodPt t q₀).z v =
      linAt p.c.U p.c.R (p.c.principal g) p.z (p.prodT t q₀ v).1 := by
  have h0s := StrongBundle.isScPlusSection_fiberZero (B := B)
  have hz0 : ∀ u ∈ p.c.φ.model.O, p.c.principal (fiberZero P) u = 0 := fun u hu =>
    p.c.snd_fiberZero (p.c.φ.symm_mapsTo hu)
  have hgs := hg.isSc1_principal_comp_r p.isChart
  have heq : EqOn (p.c.principal g ∘ StrongRetr.r p.c.R)
      ((fun u => p.c.principal g u +
        ∑ i, (t + 0) i • p.c.principal (fiberZero P) u) ∘ StrongRetr.r p.c.R) p.c.U :=
    fun u hu => by
      simp only [Function.comp_apply, hz0 _ (p.c.r_mem_O hu), smul_zero, Finset.sum_const_zero,
        add_zero]
  have hD := scDeriv_eq_of_eqOn_relOpen p.c.relOpen (hgs.congr heq) hgs subset_rfl subset_rfl
    heq.symm (z := p.z) p.mem_U
  have h1 := StrongBundle.scDeriv_paramSection_apply hg
    (fun _ : Fin 1 => h0s) p.isChart 0 q₀ t p.mem_U v.1
  have h2 : ∑ i, v.1.1 i • p.c.principal (fiberZero P)
      (StrongRetr.r p.c.R (p.c.φ.model.E.toBase 1 p.z)) = 0 := by
    rw [hz0 _ (p.c.r_mem_O p.mem_U)]
    simp
  rw [h2, add_zero, hD] at h1
  rw [paramLift_eq_paramSection_zero hg.1]
  exact h1

/-- The principal part of `s̃` at `(t, x)` in the product chart is that of `s` at `x`. -/
theorem principal_prodPt_paramLift {s : X → Y} (hs : IsSection P s) :
    (p.prodPt t q₀).c.principal (paramLift (n := 1) s hs) ((p.prodPt t q₀).c.φ (t, x)) =
      p.c.principal s (p.c.φ x) := by
  have h1 : (p.prodPt t q₀).c.φ.symm ((p.prodPt t q₀).c.φ (t, x)) = (t, x) :=
    (p.prodPt t q₀).c.φ.symm_apply_apply (p.prodPt t q₀).mem_source
  have h2 : p.c.φ.symm (p.c.φ x) = x := p.c.φ.symm_apply_apply p.mem_source
  change ((p.prodPt t q₀).c (paramLift (n := 1) s hs
    ((p.prodPt t q₀).c.φ.symm ((p.prodPt t q₀).c.φ (t, x))))).2 =
      (p.c (s (p.c.φ.symm (p.c.φ x)))).2
  rw [h1, h2]
  rfl

end ChartPoint

/-- The product chart point over `chartPt c hc hx z hz` is the chart point of the product chart
with the lift `(t, z)`. -/
theorem chartPt_prodChart_eq {c : StrongBundleChart PX P} (hc : B.IsChart c) {x : X}
    (hx : x ∈ c.φ.source) (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x)
    (t : Fin 1 → ℝ) (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (hxc : ((t, x) : (Fin 1 → ℝ) × X) ∈ (prodChart c q₀).φ.source)
    (hz' : (prodChart c q₀).φ.model.E.toBase 1 (t, z) = (prodChart c q₀).φ (t, x)) :
    chartPt (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀) hxc (t, z) hz' =
      (chartPt c hc hx z hz).prodPt t q₀ := rfl

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
/-- The level-`1` point `(t, z)` lifts `(t, φ(x))` in the product chart. -/
theorem prodChart_toBase {c : StrongBundleChart PX P} {x : X}
    (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x)
    (t : Fin 1 → ℝ) (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) :
    (prodChart c q₀).φ.model.E.toBase 1 (t, z) = (prodChart c q₀).φ (t, x) := by
  change ((rnSc 1).prod c.φ.model.E).toBase 1 (t, z) =
    ((t - 0, c.φ x) : (Fin 1 → ℝ) × c.φ.model.E 0)
  rw [ScBanach.prod_toBase, ScBanach.const_toBase, sub_zero, hz]

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
/-- A level-`1` lift of a point of the product chart is `(t, z)` for a lift `z` in `c`. -/
theorem prodChart_lift_eq {c : StrongBundleChart PX P} {x : X}
    (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x)
    (t : Fin 1 → ℝ) (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (z' : (prodChart c q₀).φ.model.E 1)
    (hz' : (prodChart c q₀).φ.model.E.toBase 1 z' = (prodChart c q₀).φ (t, x)) : z' = (t, z) :=
  (prodChart c q₀).φ.model.E.toBase_injective 1 (hz'.trans (prodChart_toBase z hz t q₀).symm)

namespace IsStabKernels

variable {Q : Type*} [TopologicalSpace Q] {c : StrongBundleChart PX P} {hc : B.IsChart c}
  {y : Q → X} {hy : ∀ q, y q ∈ c.φ.source} {S : Q → X → Y} {k : ℕ} {s : Fin k → Q → X → Y}
  {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}

/-- **The stabilized kernels of `f̃` along `q ↦ (τ(q), y(q))`** are `ℝ × Λ` in the product chart,
for the `t`-constant lifts of the sections: at `(τ, y)` the operators are `L̂ = prodLin L` and
`φ̂ = prodStab φ`, and `ker(L̂ ⊕ φ̂) = {((σ, v), μ) | (v, μ) ∈ ker(L ⊕ φ)}`. -/
theorem prodLift (hΛ : IsStabKernels f c hc y hy S s Λ) (hf : B.IsScFredholmSection f)
    (τ : Q → (Fin 1 → ℝ)) (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) :
    IsStabKernels (B := prodBundle B) (paramLift (n := 1) f hf.isScSmooth.1)
      (prodChart c q₀) (isChart_prodChart hc q₀)
      (fun q => (τ q, y q)) (fun q => mem_prodChart_source q₀ (hy q) (τ q))
      (fun q => paramLift (n := 1) (S q) (hΛ.isScPlusSection q).1)
      (fun i q => paramLift (n := 1) (s i q) (hΛ.isSection i q)) Λ.prodLine where
  isScPlusSection q := isScPlusSection_paramLift (hΛ.isScPlusSection q)
  zero q := by
    rw [sectionAdd_paramLift]
    exact (isZeroAt_pullback_iff_pullbackSlice (isSection_pullbackLift _) (τ q) (y q)).2
      (hΛ.zero q)
  isSection i q := isSection_pullbackLift _
  exists_lift q := by
    obtain ⟨z, hz⟩ := hΛ.exists_lift q
    exact ⟨(τ q, z), prodChart_toBase z hz (τ q) q₀⟩
  spec q x hq hxc z' hz' T' hT' φ' hφ' := by
    subst hq
    obtain ⟨z, hz⟩ := hΛ.exists_lift q
    obtain rfl := prodChart_lift_eq z hz (τ q) q₀ z' hz'
    let p := chartPt c hc (hy q) z hz
    set T := p.stabT hf (hΛ.isScPlusSection q) (hΛ.zero q) with hTdef
    set φ := p.stabPhi (fun i => s i q) (fun i => hΛ.isSection i q) with hφdef
    have hsp := hΛ.spec q rfl (hy q) z hz T (fun _ => rfl) φ (fun μ => p.coe_stabPhi _ _ μ)
    have hTeq : T' = p.prodLin (τ q) q₀ T := by
      refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
      refine (hT' v).trans ?_
      rw [sectionAdd_paramLift]
      refine (p.linAt_prodPt_paramLift (τ q) q₀
        (hf.isScSmooth.sectionAdd (hΛ.isScPlusSection q)) v).trans ?_
      exact (p.coe_prodLin_apply (τ q) q₀ T v).symm
    have hφeq : φ' = p.prodStab (τ q) q₀ φ := by
      refine ContinuousLinearMap.ext fun μ => Subtype.ext ?_
      refine (hφ' μ).trans ?_
      change _ = ((φ μ : ↥p.K) : c.F 0)
      rw [p.coe_stabPhi]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← p.principal_prodPt_paramLift (τ q) q₀ (hΛ.isSection i q)]
      rfl
    subst hTeq hφeq
    refine ⟨p.surjective_coprod_prodLin (τ q) q₀ hsp.1, ?_⟩
    exact (congrArg (Submodule.comap (prodLinePr (c.φ.model.E 0) k :
        ((Fin 1 → ℝ) × c.φ.model.E 0) × (Fin k → ℝ) →ₗ[ℝ] c.φ.model.E 0 × (Fin k → ℝ)))
      hsp.2).trans (map_ker_extConjOp_eq (p.prodT (τ q) q₀) (p.prodK (τ q) q₀) T φ
        (p.prodStab (τ q) q₀ φ) (p.prodStab_conj (τ q) q₀ φ) p.T.subtypeL
        (p.prodPt (τ q) q₀).T.subtypeL (fun _ => rfl))

end IsStabKernels

end ProdKernels

end Polyfold
