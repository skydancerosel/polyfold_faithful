import Polyfold.Chapter6.ProductSectionOrientation2021c

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19** (preprint Remark 6.42, p. 230), continued: the product orientation `e ∧ o` of
`f̃(t, x) = f(x)` over `ℝ¹ × X` is carried by the push-forwards of `f̃`.
-/

open Module TensorProduct Bundle Topology Set Filter

noncomputable section

namespace Polyfold

universe u v


/-- **Regrouping three-step identifications of rays** (the shape of `IsStabKernels.orRay`), for
a map `tr` of orientations: if `oe' ∘ tr = λ(C) ∘ oe` and `R' ∘ λ(C) = λ(N) ∘ R`, then
`R' ∘ u ∘ oe' ∘ tr = λ(N) ∘ R ∘ u ∘ oe` (`ray_trans_conj_aux` for a map which is not given as a
bijection). -/
theorem ray_trans_map_aux {O O' D D' L L' : Type*} [AddCommMonoid D] [Module ℝ D]
    [AddCommMonoid D'] [Module ℝ D'] [AddCommMonoid L] [Module ℝ L] [AddCommMonoid L']
    [Module ℝ L'] (oe : O ≃ Module.Ray ℝ D) (oe' : O' ≃ Module.Ray ℝ D') (tr : O → O')
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

/-! ### The product orientation of `f̃` and its reading in the stabilized kernels -/

/-- A shortcut for the action of `ℝˣ` on the rays of a real module (the search through
`DistribMulAction ℝˣ` is slow on determinant lines over chart points of pulled-back bundles). -/
local instance (priority := 10000) rayUnitsMulAction {M : Type*} [AddCommMonoid M] [Module ℝ M] :
    MulAction ℝˣ (Module.Ray ℝ M) := inferInstance


section ProdOrZero

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (t : Fin 1 → ℝ)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))

/-- `Lin(f̃ + 0, (t, x)) = Lin(f̃, (t, x))`. -/
theorem linSet_paramLift_add_zero (hf : B.IsScFredholmSection f) :
    (p.prodPt t q₀).linSet (sectionAdd (pullbackProj P Prod.snd)
        (paramLift (n := 1) f hf.isScSmooth.1) (fiberZero (pullbackProj P Prod.snd))) =
      (p.prodPt t q₀).linSet (paramLift (n := 1) f hf.isScSmooth.1) :=
  (p.prodPt t q₀).linSet_sectionAdd (isSection_pullbackLift _)
    (StrongBundle.isScPlusSection_fiberZero (B := prodBundle B))

/-- **`L̂ ∈ Lin(f̃, (t, x))`** for `L ∈ Lin(f, x)`. -/
theorem prodLin_mem_linSet_paramLift (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) :
    p.prodLin t q₀ L ∈ (p.prodPt t q₀).linSet (paramLift (n := 1) f hf.isScSmooth.1) :=
  p.linSet_paramLift_add_zero t q₀ hf ▸ p.prodLin_mem_linSet t q₀ hf hx
    (StrongBundle.isScPlusSection_fiberZero (B := prodBundle B)) hL

/-- **The product orientation of `f̃(t, x) = f(x)`** at `(t, x)` (2021 Remark 6.6.19 for `s = 0`):
`prodOrFirst` for the zero section, read as an orientation of `DET(f̃, (t, x))`
(`Lin(f̃ + 0) = Lin(f̃)`). -/
def prodOrFirst₀ (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    (hne : (p.linSet f).Nonempty) (o : p.Or f hf) :
    (p.prodPt t q₀).Or (paramLift (n := 1) f hf.isScSmooth.1) hf.param :=
  (p.prodPt t q₀).orCongr (theorem_3_1_18_preprint hf.param
      (StrongBundle.isScPlusSection_fiberZero (B := prodBundle B))) hf.param
    (p.linSet_paramLift_add_zero t q₀ hf)
    (p.prodOrFirst t q₀ hf hx (StrongBundle.isScPlusSection_fiberZero (B := prodBundle B)) hne o)

/-- **`prodOrFirst₀` at `L̂`** is `h ↦ e ∧ h` of `o(L)`, for every `L ∈ Lin(f, x)`. -/
theorem prodOrFirst₀_apply (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    (hne : (p.linSet f).Nonempty) (o : p.Or f hf) (L : ↥p.T →L[ℝ] ↥p.K)
    (hL : L ∈ p.linSet f) :
    p.prodOrFirst₀ t q₀ hf hx hne o
        ⟨p.prodLin t q₀ L, p.prodLin_mem_linSet_paramLift t q₀ hf hx hL⟩ =
      Module.Ray.map (extConjDetFirst (p.prodT t q₀) (p.prodK t q₀)
        (p.isFredholm_of_mem_linSet hf L hL)
        ((p.prodPt t q₀).isFredholm_of_mem_linSet hf.param _
          (p.prodLin_mem_linSet_paramLift t q₀ hf hx hL))) (o ⟨L, hL⟩) :=
  ((p.prodPt t q₀).orCongr_apply _ hf.param (p.linSet_paramLift_add_zero t q₀ hf) _
    (p.prodLin_mem_linSet_paramLift t q₀ hf hx hL)).trans
    (p.prodOrFirst_apply t q₀ hf hx
      (StrongBundle.isScPlusSection_fiberZero (B := prodBundle B)) hne o L hL)

/-- `(f̃ + S̃)'(t, x) = ((f + S)'(x))^`. -/
theorem stabT_prodPt (hf : B.IsScFredholmSection f) {S : X → Y} (hS : B.IsScPlusSection S)
    (hx0 : IsZeroAt P (sectionAdd P f S) x)
    (hS' : (prodBundle B).IsScPlusSection (paramLift (n := 1) S hS.1))
    (hx0' : IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (paramLift (n := 1) f hf.isScSmooth.1) (paramLift (n := 1) S hS.1)) (t, x)) :
    (p.prodPt t q₀).stabT hf.param hS' hx0' = p.prodLin t q₀ (p.stabT hf hS hx0) := by
  refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
  rw [coe_stabT, sectionAdd_paramLift]
  exact (p.linAt_prodPt_paramLift t q₀ (hf.isScSmooth.sectionAdd hS) v).trans
    ((p.coe_stabT hf hS hx0 _).symm.trans
      (p.coe_prodLin_apply t q₀ (p.stabT hf hS hx0) v).symm)

/-- `φ̂` of the `t`-constant lifts is `prodStab φ`. -/
theorem stabPhi_prodPt {k : ℕ} (s : Fin k → X → Y) (hs : ∀ i, IsSection P (s i))
    (hs' : ∀ i, IsSection (pullbackProj P Prod.snd) (paramLift (n := 1) (s i) (hs i))) :
    (p.prodPt t q₀).stabPhi (fun i => paramLift (n := 1) (s i) (hs i)) hs' =
      p.prodStab t q₀ (p.stabPhi s hs) := by
  refine ContinuousLinearMap.ext fun μ => Subtype.ext ?_
  rw [coe_stabPhi]
  change _ = ((p.stabPhi s hs μ : ↥p.K) : p.c.F 0)
  rw [p.coe_stabPhi]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← p.principal_prodPt_paramLift t q₀ (hs i)]
  rfl

/-- `α(L̂) = α(L)`: the cokernels of `L̂ = Γ⁻¹ (L ⊕ 0) A` and of `L` have the same dimension. -/
theorem stabSign_prodLin (L : ↥p.T →L[ℝ] ↥p.K) : stabSign (p.prodLin t q₀ L) = stabSign L := by
  have h1 : stabSign (extOp L) = stabSign (p.prodLin t q₀ L) :=
    stabSign_conj (p.prodT t q₀) (p.prodK t q₀) (p.prodLin_conj t q₀ L)
  rw [← h1, stabSign, stabSign, (extCoker L).finrank_eq]

/-- The inclusion `T_{(t, z)} → ℝ¹ × E₀`, with its target written as a product. -/
abbrev prodIncl : ↥(p.prodPt t q₀).T →L[ℝ] (Fin 1 → ℝ) × p.c.φ.model.E 0 :=
  (p.prodPt t q₀).T.subtypeL

theorem prodIncl_injective : Function.Injective (p.prodIncl t q₀) := Subtype.val_injective

/-- **The product orientation read in the stabilized kernels**: for `L ∈ Lin(f, x)` with a
stabilization `L ⊕ φ` onto and kernels `Λ_q`, `(ℝ × Λ)_q`, reading `prodOrFirst₀ o` at
`L̂ ⊕ φ̂` is `w ↦ ê ∧ J(w)` of reading `o` at `L ⊕ φ` (`stabRayEquiv_extConjDetFirst`,
`prodLineWedgeEquiv_compat`). The operators `T₁ = L̂`, `φ₁ = φ̂` enter through equations. -/
theorem stabRay_prodOrFirst₀_aux (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    (o : p.Or f hf) {T : ↥p.T →L[ℝ] ↥p.K} (hT : T ∈ p.linSet f) {k : ℕ}
    (φ : (Fin k → ℝ) →L[ℝ] ↥p.K) (hs : Function.Surjective (T.coprod φ))
    {Q : Type*} [TopologicalSpace Q] (Λ : SubspaceFamily Q (p.c.φ.model.E 0 × (Fin k → ℝ)))
    (q : Q)
    (hL : Λ.L q = (LinearMap.ker ((T.coprod φ : _ →L[ℝ] ↥p.K) :
          ↥p.T × (Fin k → ℝ) →ₗ[ℝ] ↥p.K)).map
        (((p.T.subtypeL.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ))) :
          ↥p.T × (Fin k → ℝ) →L[ℝ] p.c.φ.model.E 0 × (Fin k → ℝ)) :
            ↥p.T × (Fin k → ℝ) →ₗ[ℝ] p.c.φ.model.E 0 × (Fin k → ℝ)))
    {T₁ : ↥(p.prodPt t q₀).T →L[ℝ] ↥(p.prodPt t q₀).K} (hT₁e : T₁ = p.prodLin t q₀ T)
    (hT₁ : T₁ ∈ (p.prodPt t q₀).linSet (paramLift (n := 1) f hf.isScSmooth.1))
    {φ₁ : (Fin k → ℝ) →L[ℝ] ↥(p.prodPt t q₀).K} (hφ₁e : φ₁ = p.prodStab t q₀ φ)
    (hs₁ : Function.Surjective (T₁.coprod φ₁))
    (hL' : Λ.prodLine.L q = (LinearMap.ker ((T₁.coprod φ₁ : _ →L[ℝ] ↥(p.prodPt t q₀).K) :
          ↥(p.prodPt t q₀).T × (Fin k → ℝ) →ₗ[ℝ] ↥(p.prodPt t q₀).K)).map
        ((((p.prodIncl t q₀).prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ))) :
          ↥(p.prodPt t q₀).T × (Fin k → ℝ) →L[ℝ]
            ((Fin 1 → ℝ) × p.c.φ.model.E 0) × (Fin k → ℝ)) :
            ↥(p.prodPt t q₀).T × (Fin k → ℝ) →ₗ[ℝ]
              ((Fin 1 → ℝ) × p.c.φ.model.E 0) × (Fin k → ℝ))) :
    ((((p.prodPt t q₀).orEquivRay hf.param hT₁).trans (MulAction.toPerm (stabSign T₁))).trans
        (stabRayEquiv ((p.prodPt t q₀).isFredholm_of_mem_linSet hf.param _ hT₁) hs₁
          (kerEquivMap (p.prodIncl t q₀) (p.prodIncl_injective t q₀) hL')))
        (p.prodOrFirst₀ t q₀ hf hx ⟨T, hT⟩ o) =
      Module.Ray.map (Λ.prodLineWedgeEquiv q)
        ((((p.orEquivRay hf hT).trans (MulAction.toPerm (stabSign T))).trans
          (stabRayEquiv (p.isFredholm_of_mem_linSet hf _ hT) hs
            (kerEquivMap p.T.subtypeL Subtype.val_injective hL))) o) := by
  subst hT₁e hφ₁e
  have hFr := p.isFredholm_of_mem_linSet hf _ hT
  have hFr' := (p.prodPt t q₀).isFredholm_of_mem_linSet hf.param _ hT₁
  exact ray_trans_map_aux (p.orEquivRay hf hT) ((p.prodPt t q₀).orEquivRay hf.param hT₁)
    (p.prodOrFirst₀ t q₀ hf hx ⟨T, hT⟩)
    (extConjDetFirst (p.prodT t q₀) (p.prodK t q₀) hFr hFr') (stabSign T)
    (stabSign (p.prodLin t q₀ T))
    (stabRayEquiv hFr hs (kerEquivMap p.T.subtypeL Subtype.val_injective hL))
    (stabRayEquiv hFr' hs₁ (kerEquivMap (p.prodIncl t q₀) (p.prodIncl_injective t q₀) hL'))
    (Λ.prodLineWedgeEquiv q)
    (fun o' => p.prodOrFirst₀_apply t q₀ hf hx ⟨T, hT⟩ o' T hT)
    (p.stabSign_prodLin t q₀ T)
    (stabRayEquiv_extConjDetFirst (p.prodT t q₀) (p.prodK t q₀)
      (p.prodStab_conj t q₀ φ) hFr hFr' hs hs₁
      (kerEquivMap p.T.subtypeL Subtype.val_injective hL)
      (kerEquivMap (p.prodIncl t q₀) (p.prodIncl_injective t q₀) hL')
      (Λ.prodLineWedgeEquiv q)
      (prodLineWedgeEquiv_compat (p.prodT t q₀) (p.prodK t q₀) hFr (p.prodStab_conj t q₀ φ)
        p.T.subtypeL Subtype.val_injective (p.prodIncl t q₀) (p.prodIncl_injective t q₀)
        (fun _ => rfl) Λ q hL hL')) o

end ChartPoint

end ProdOrZero

end Polyfold
