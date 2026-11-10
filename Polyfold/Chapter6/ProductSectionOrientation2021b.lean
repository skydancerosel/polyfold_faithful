import Polyfold.Chapter6.ProductSectionOrientation2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19** (preprint Remark 6.42, p. 230), continued from
`ProductSectionOrientation2021.lean`: the product orientation `h ↦ h̃ = e ∧ h` of
`f̂ = f̃ + S` over `ℝ¹ × X` does not depend on the chart in which it is read.

# The product orientation in two charts

## The text, paraphrased

(2021, Remark 6.6.19) `L̃(a, b) = La` is oriented by `h̃ = (e ∧ a₁ ∧ … ∧ aₙ) ⊗ (b₁ ∧ … ∧ b_l)*`
when `L` is oriented by `h`; "this convention is compatible with the choices which have to be
made during the construction".  One of these choices is the chart of `X` at `x` in which
`DET(f, x)` and `DET(f̂, (t, x))` are read (`ChartPoint.prodOrFirst` is defined in the product
chart point `prodPt` over a chart point `p` of `X`).

## What is formalized

* The transition of two product chart points `p.prodPt t q₀`, `p'.prodPt t q₀'` at `(t, x)`:
  `baseDeriv_prodPt` (`D(τ̂ ∘ r̂)(t, z) = 1 × D(τ ∘ r)(z)`), `fiberMap_prodPt` (`Γ̂ = Γ`),
  `prodT_transferT_prodPt` (`Â = A × 1` under `prodT`), `prodK_transferK_prodPt`,
  `transfer_prodLin` (`Γ̂ L̂ Â⁻¹ = (Γ L A⁻¹)^`).
* `conjDet_prod_extDetFirst`: for `L' A = Γ L`, `conjDet(A × 1, Γ)` commutes with the 2021 map
  `h ↦ e ∧ h` (`extDetFirst`), with no sign; `conjDet_extConjDetFirst_of_conj`: the same after
  the swaps of the factors (`extConjDetFirst`), for abstract product identifications.
* **`ChartPoint.orTransfer_prodPt_prodOrFirst`**: the product orientation of 2021 Remark 6.6.19
  read over `p`, transferred to the product chart point over `p'` (`orTransfer`), is the product
  orientation of the transfer of `o`.  This is the chart independence needed to make
  `(t, x) ↦ prodOrFirst` a map `z ↦ ô_z ∈ Or_z^{f̂}` (Definition 6.6.16) on `ℝ¹ × X`.

## Reading

As in `ProductOrientation.lean`: `X × [0, 1]` is read as `ℝ¹ × X` (decision D2), the extra
factor is placed second in `E × ℝ¹`, and `e = (0, 1)`.  The charts of `ℝ¹ × X` used are the
product charts `(r ↦ r) × φ` (`PullbackChartData.ofProd`), whose transitions are `1 × (φ' ∘ φ⁻¹)`.
-/

open Module TensorProduct Bundle Topology Set Filter

noncomputable section

namespace Polyfold

open StrongRetr

universe u v

/-! ### `conjDet (A × 1, Γ)` commutes with `h ↦ e ∧ h` -/

section ConjExtFirst

variable {E F E' F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F')

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `A × 1` conjugates `L̃ = L ⊕ 0` to `L̃'` when `A`, `Γ` conjugate `L` to `L'`. -/
theorem extOp_conj_prod {L : E →L[ℝ] F} {L' : E' →L[ℝ] F'} (h : ∀ v, L' (A v) = Γ (L v))
    (v : E × (Fin 1 → ℝ)) :
    extOp L' ((A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) v) = Γ (extOp L v) := by
  rw [extOp_apply, extOp_apply]
  exact h v.1

set_option maxHeartbeats 1600000 in
omit [CompleteSpace E'] [CompleteSpace F'] in
/-- **`conjDet (A × 1, Γ) ∘ extDetFirst_L = extDetFirst_{L'} ∘ conjDet (A, Γ)`** for
`L' A = Γ L`: on a generator `(a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)*` both sides are
`(e ∧ (A a₁, 0) ∧ … ∧ (A aₙ, 0)) ⊗ ([Γ d₁] ∧ … ∧ [Γ d_l])*`. -/
theorem conjDet_prod_extDetFirst {L : E →L[ℝ] F} {L' : E' →L[ℝ] F'}
    (h : ∀ v, L' (A v) = Γ (L v)) (hL : L.IsFredholm) (hL' : L'.IsFredholm) (y : fredholmDet L) :
    conjDet (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) Γ (extOp_conj_prod A Γ h)
        (extDetFirst hL y) =
      extDetFirst hL' (conjDet A Γ h y) := by
  have := hL.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (L : E →ₗ[ℝ] F)) := hL.finite_coker
  have : FiniteDimensional ℝ (F' ⧸ LinearMap.range (L' : E' →ₗ[ℝ] F')) := hL'.finite_coker
  have : FiniteDimensional ℝ (F' ⧸ LinearMap.range (extOp L' : E' × (Fin 1 → ℝ) →ₗ[ℝ] F')) :=
    (extCoker L').symm.finiteDimensional
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (extOp L : E × (Fin 1 → ℝ) →ₗ[ℝ] F)) :=
    (extCoker L).symm.finiteDimensional
  set a := Module.finBasis ℝ (LinearMap.ker (L : E →ₗ[ℝ] F))
  set d := Module.finBasis ℝ (F ⧸ LinearMap.range (L : E →ₗ[ℝ] F))
  have hd := d.linearIndependent
  have hd₁ : LinearIndependent ℝ ((extCoker L).symm ∘ d) :=
    hd.map' (extCoker L).symm.toLinearMap (extCoker L).symm.ker
  have hd₂ : LinearIndependent ℝ (conjCokerEquiv A Γ h ∘ d) :=
    hd.map' (conjCokerEquiv A Γ h).toLinearMap (conjCokerEquiv A Γ h).ker
  have hker : conjKerEquiv (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) Γ
      (extOp_conj_prod A Γ h) ∘ Fin.cons (α := fun _ => LinearMap.ker
        (extOp L : E × (Fin 1 → ℝ) →ₗ[ℝ] F)) (extE L) (stabJ L 0 ∘ a) =
      Fin.cons (α := fun _ => LinearMap.ker (extOp L' : E' × (Fin 1 → ℝ) →ₗ[ℝ] F')) (extE L')
        (stabJ L' 0 ∘ (conjKerEquiv A Γ h ∘ a)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · apply Subtype.ext
      change (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) ((0 : E), fun _ => (1 : ℝ)) =
        ((0 : E'), fun _ => (1 : ℝ))
      rw [ContinuousLinearEquiv.prodCongr_apply, map_zero]
      rfl
    · apply Subtype.ext
      rfl
  have hcok : conjCokerEquiv (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) Γ
      (extOp_conj_prod A Γ h) ∘ ((extCoker L).symm ∘ d) =
      (extCoker L').symm ∘ (conjCokerEquiv A Γ h ∘ d) := by
    funext i
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (d i)
    simp only [Function.comp_apply, ← hy]
    rfl
  have hext : ∀ f g : fredholmDet L →ₗ[ℝ] fredholmDet (extOp L'),
      f (wedge a rfl ⊗ₜ dualVec (wedge d rfl)) = g (wedge a rfl ⊗ₜ dualVec (wedge d rfl)) →
        f = g := fun f g hfg =>
    tensor_line_ext (L₁ := maxPow (LinearMap.ker (L : E →ₗ[ℝ] F)))
      (L₂ := maxPowDual (F ⧸ LinearMap.range (L : E →ₗ[ℝ] F))) (N := fredholmDet (extOp L'))
      (f := f) (g := g) finrank_maxPow finrank_maxPowDual (wedge_basis_ne_zero' a rfl)
      (dualVec_ne_zero finrank_maxPow (wedge_basis_ne_zero' d rfl)) hfg
  have key : ((conjDet (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) Γ
        (extOp_conj_prod A Γ h)).toLinearMap ∘ₗ (extDetFirst hL).toLinearMap)
        (wedge a rfl ⊗ₜ dualVec (wedge d rfl)) =
      ((extDetFirst hL').toLinearMap ∘ₗ (conjDet A Γ h).toLinearMap)
        (wedge a rfl ⊗ₜ dualVec (wedge d rfl)) := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [extDetFirst_wedge_tmul hL a rfl hd rfl, conjDet_wedge_tmul _ _ _ _ _ hd₁,
      conjDet_wedge_tmul A Γ h a rfl hd rfl, extDetFirst_wedge_tmul hL' _ _ hd₂]
    exact congrArg₂ (fun u w => u ⊗ₜ[ℝ] dualVec w) (wedge_congr_fun hker _ _)
      (wedge_congr_fun hcok _ _)
  exact LinearMap.congr_fun (hext ((conjDet (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ)))
      Γ (extOp_conj_prod A Γ h)).toLinearMap ∘ₗ (extDetFirst hL).toLinearMap)
    ((extDetFirst hL').toLinearMap ∘ₗ (conjDet A Γ h).toLinearMap) key) y

end ConjExtFirst

section ProdTransfer

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]

namespace ChartPoint

variable {x : X} (p p' : ChartPoint B x) (t : Fin 1 → ℝ)
  (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))

/-- **The base transition of two product chart points is `1 × (τ ∘ r)`**: its derivative at
`(t, z)` is `(σ, v) ↦ (σ, D(τ ∘ r)(z) v)`. -/
theorem baseDeriv_prodPt (v : (Fin 1 → ℝ) × p.c.φ.model.E 0) :
    (p.prodPt t q₀).baseDeriv (p'.prodPt t q₀') v = (v.1, p.baseDeriv p' v.2) := by
  set P₁ := p.prodPt t q₀ with hP₁
  set P₂ := p'.prodPt t q₀' with hP₂
  set R₁ := p.baseRet p' with hR₁
  -- the transition of the charts of `X` after the retraction, sc-smooth on `R₁.U`
  have hg : IsScSmooth R₁.U (p.c.φ.transition p'.c.φ ∘ R₁) :=
    (p.c.isChart.compatible p'.c.isChart (P := PX)).1.comp_isScSmooth _ (p.baseRet_retract p')
  -- the product retraction `1 × r` on `ℝ¹ × R₁.U`
  let Rhat : ScRetraction ((rnSc 1).prod p.c.φ.model.E) (univ ×ˢ p.c.φ.model.C) :=
    (ScRetraction.id (rn_relOpen_univ 1)).prod R₁
  let V := (Rhat.restrict (P₁.isOpen_overlapW P₂)).U
  have hV : IsRelOpenInQuadrant ((rnSc 1).prod p.c.φ.model.E) (univ ×ˢ p.c.φ.model.C) V :=
    (Rhat.restrict (P₁.isOpen_overlapW P₂)).relOpen
  have hV₁ : V ⊆ (P₁.baseRet P₂).U := fun u hu =>
    ⟨⟨mem_univ _, p.baseRet_U_subset p' hu.1.2⟩, hu.2⟩
  have hV₂ : V ⊆ univ ×ˢ R₁.U := inter_subset_left
  have hf₂ : IsScSmooth (E := (rnSc 1).prod p.c.φ.model.E) (F := (rnSc 1).prod p'.c.φ.model.E)
      (univ ×ˢ R₁.U) (Prod.map (id : (Fin 1 → ℝ) → (Fin 1 → ℝ)) (p.c.φ.transition p'.c.φ ∘ R₁)) :=
    IsScSmooth.prodMap (rn_relOpen_univ 1).isScDomain R₁.isScDomain
      ((rn_relOpen_univ 1).prod R₁.relOpen).isScDomain (isScSmooth_id (isScDomain_univ (rnSc 1)))
      hg
  have heq : EqOn (P₁.c.φ.transition P₂.c.φ ∘ P₁.baseRet P₂)
      (Prod.map (id : (Fin 1 → ℝ) → (Fin 1 → ℝ)) (p.c.φ.transition p'.c.φ ∘ R₁)) V := by
    intro u _
    refine Prod.ext ?_ rfl
    change u.1 + 0 - 0 = u.1
    simp
  have hzb : ((rnSc 1).prod p.c.φ.model.E).toBase 1 ((t, p.z) : ((rnSc 1).prod p.c.φ.model.E) 1) =
      (t, p.c.φ.model.E.toBase 1 p.z) := by
    rw [ScBanach.prod_toBase, ScBanach.const_toBase]
  have hz₁ : p.c.φ.model.E.toBase 1 p.z ∈ R₁.U := p.z_mem_baseRet p'
  have hz : P₁.z ∈ ((rnSc 1).prod p.c.φ.model.E).lvlSet V 1 := by
    change ((rnSc 1).prod p.c.φ.model.E).toBase 1 (t, p.z) ∈ V
    rw [hzb]
    refine ⟨⟨mem_univ _, hz₁⟩, ?_⟩
    change (t, r p.c.R (p.c.φ.model.E.toBase 1 p.z)) ∈ P₁.overlapW P₂
    rw [p.r_toBase_z]
    have h := P₁.toBase_z_mem_overlapW P₂
    change ((rnSc 1).prod p.c.φ.model.E).toBase 1 (t, p.z) ∈ P₁.overlapW P₂ at h
    rwa [hzb] at h
  have hz' : P₁.z ∈ ((rnSc 1).prod p.c.φ.model.E).lvlSet (univ ×ˢ R₁.U) 1 :=
    ((rnSc 1).prod p.c.φ.model.E).lvlSet_mono hV₂ 1 hz
  have h1 := scDeriv_eq_of_eqOn_relOpen hV (P₁.isSc1_transition P₂) hf₂.isSc1 hV₁ hV₂ heq hz
  have h2 := scDeriv_prodMap (F := rnSc 1) (F' := p'.c.φ.model.E) (rn_relOpen_univ 1) R₁.relOpen
    (isScSmooth_id (isScDomain_univ (rnSc 1))) hg hz'
  have hid : scDeriv (E := rnSc 1) (F := rnSc 1) univ id (t : (rnSc 1) 1) =
      ContinuousLinearMap.id ℝ (Fin 1 → ℝ) :=
    IsSc1.scDeriv_eqOn (isSc1With_id univ) ((rn_relOpen_univ 1).isScDomain.uniqueDiffWithinAt 1)
      (by rw [ScBanach.mem_lvlSet]; exact mem_univ _)
  have h3 : P₁.baseDeriv P₂ = (ContinuousLinearMap.id ℝ (Fin 1 → ℝ)).prodMap (p.baseDeriv p') := by
    refine (h1.trans h2).trans ?_
    exact congrArg (fun L : (rnSc 1) 0 →L[ℝ] (rnSc 1) 0 => L.prodMap (p.baseDeriv p')) hid
  exact ContinuousLinearMap.ext_iff.1 h3 v

/-- **The fibre transition of two product chart points is that of the chart points**: `Γ̂ = Γ`
on `K_z` (the pulled-back charts have the fibre transitions of `c`, `c'` at `g(t, z) = z`). -/
theorem fiberMap_prodPt {k : p.c.F 0} (hk : k ∈ p.K) :
    (p.prodPt t q₀).fiberMap (p'.prodPt t q₀') k = p.fiberMap p' k := by
  have hk' : k ∈ (p.prodPt t q₀).K := (p.mem_prodPt_K_iff t q₀ k).2 hk
  have hK : (p.c.φ.model.E.toBase 1 p.z, k) ∈ p.c.K := p.mem_K_of_mem hk
  have hzb : ((rnSc 1).prod p.c.φ.model.E).toBase 1 ((t, p.z) : ((rnSc 1).prod p.c.φ.model.E) 1) =
      (t, p.c.φ.model.E.toBase 1 p.z) := by
    rw [ScBanach.prod_toBase, ScBanach.const_toBase]
  have hPy : P (p.c.toPartialEquiv.symm (p.c.φ.model.E.toBase 1 p.z, k)) = x := by
    rw [p.c.proj_symm hK]
    change p.c.φ.symm (p.c.φ.model.E.toBase 1 p.z) = x
    rw [p.toBase_z, p.c.φ.symm_apply_apply p.mem_source]
  have hzP : ((PullbackChartData.ofProd p.c 0).toChart q₀).φ.model.E.toBase 1 (p.prodPt t q₀).z =
      ((t, p.c.φ.model.E.toBase 1 p.z) : ((rnSc 1).prod p.c.φ.model.E) 0) := by
    change ((rnSc 1).prod p.c.φ.model.E).toBase 1 (t, p.z) = _
    exact hzb
  have hmem : ((((t, p.c.φ.model.E.toBase 1 p.z) : ((rnSc 1).prod p.c.φ.model.E) 0), k) :
        ((PullbackChartData.ofProd p.c 0).toChart q₀).φ.model.E 0 ×
          ((PullbackChartData.ofProd p.c 0).toChart q₀).F 0) ∈
      ((PullbackChartData.ofProd p.c 0).toChart q₀).overlap
        ((PullbackChartData.ofProd p'.c 0).toChart q₀') := by
    refine (PullbackChartData.mem_overlap_iff _ _ _ _).2
      ⟨⟨((t, x), p.c.toPartialEquiv.symm (p.c.φ.model.E.toBase 1 p.z, k)), hPy⟩,
        ⟨mem_univ _, p.mem_source⟩, ⟨mem_univ _, p'.mem_source⟩, ?_⟩
    change ((t - 0, p.c.φ x), (p.c (p.c.toPartialEquiv.symm (p.c.φ.model.E.toBase 1 p.z, k))).2) =
      ((t, p.c.φ.model.E.toBase 1 p.z), k)
    rw [sub_zero, ← p.toBase_z, p.c.apply_symm hK]
  have hg : (PullbackChartData.ofProd p.c 0).g
      ((t, p.c.φ.model.E.toBase 1 p.z) : ((rnSc 1).prod p.c.φ.model.E) 0) =
      p.c.φ.model.E.toBase 1 p.z := by
    change p.c.φ (p.c.φ.symm (p.c.φ.model.E.toBase 1 p.z)) = _
    exact p.c.φ.apply_symm_apply p.toBase_z_mem_O
  rw [(p.prodPt t q₀).fiberMap_apply_of_mem (p'.prodPt t q₀') hk', p.fiberMap_apply_of_mem p' hk]
  change (((PullbackChartData.ofProd p.c 0).toChart q₀).transition
    ((PullbackChartData.ofProd p'.c 0).toChart q₀')
    (((PullbackChartData.ofProd p.c 0).toChart q₀).φ.model.E.toBase 1 (p.prodPt t q₀).z, k)).2 = _
  rw [hzP]
  refine (congrArg Prod.snd (PullbackChartData.transition_eqOn _ _ _ _ hmem)).symm.trans ?_
  change (p.c.transition p'.c ((PullbackChartData.ofProd p.c 0).g
    ((t, p.c.φ.model.E.toBase 1 p.z) : ((rnSc 1).prod p.c.φ.model.E) 0), k)).2 = _
  rw [hg]

/-- **`Â = A × 1`**: under `prodT`, the identification `T_{(t,z)} ≅ T_{(t,z')}` of the product
chart points is `(v, σ) ↦ (A v, σ)`. -/
theorem prodT_transferT_prodPt (w : ↥(p.prodPt t q₀).T) :
    p'.prodT t q₀' ((p.prodPt t q₀).transferT (p'.prodPt t q₀') w) =
      (p.transferT p' (p.prodT t q₀ w).1, (p.prodT t q₀ w).2) := by
  refine Prod.ext (Subtype.ext ?_) ?_
  · change (((p.prodPt t q₀).transferT (p'.prodPt t q₀') w).1 :
      (Fin 1 → ℝ) × p'.c.φ.model.E 0).2 = p.baseDeriv p' ((w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2)
    rw [coe_transferT_apply]
    exact congrArg Prod.snd (p.baseDeriv_prodPt p' t q₀ q₀' w.1)
  · change (((p.prodPt t q₀).transferT (p'.prodPt t q₀') w).1 :
      (Fin 1 → ℝ) × p'.c.φ.model.E 0).1 = (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1
    rw [coe_transferT_apply]
    exact congrArg Prod.fst (p.baseDeriv_prodPt p' t q₀ q₀' w.1)

/-- **`Γ̂ = Γ`**: under `prodK`, the identification `K̂_z ≅ K̂'_{z'}` of the product chart points is
that of the chart points. -/
theorem prodK_transferK_prodPt (k : ↥(p.prodPt t q₀).K) :
    p'.prodK t q₀' ((p.prodPt t q₀).transferK (p'.prodPt t q₀') k) =
      p.transferK p' (p.prodK t q₀ k) := by
  refine Subtype.ext ?_
  change (p.prodPt t q₀).fiberMap (p'.prodPt t q₀') k.1 = p.fiberMap p' k.1
  exact p.fiberMap_prodPt p' t q₀ q₀' ((p.mem_prodPt_K_iff t q₀ k.1).1 k.2)

/-- **The conjugate of `L̂` is the lift of the conjugate of `L`**: `Γ̂ L̂ Â⁻¹ = (Γ L A⁻¹)^`. -/
theorem transfer_prodLin (L : ↥p.T →L[ℝ] ↥p.K) :
    (((p.prodPt t q₀).transferK (p'.prodPt t q₀') :
        ↥(p.prodPt t q₀).K →L[ℝ] ↥(p'.prodPt t q₀').K) ∘L p.prodLin t q₀ L ∘L
      ((p'.prodPt t q₀').transferT (p.prodPt t q₀) :
        ↥(p'.prodPt t q₀').T →L[ℝ] ↥(p.prodPt t q₀).T)) =
    p'.prodLin t q₀' ((p.transferK p' : ↥p.K →L[ℝ] ↥p'.K) ∘L L ∘L
      (p'.transferT p : ↥p'.T →L[ℝ] ↥p.T)) := by
  refine ContinuousLinearMap.ext fun w => (p'.prodK t q₀').injective ?_
  have h2 : (p.prodT t q₀ ((p'.prodPt t q₀').transferT (p.prodPt t q₀) w)).1 =
      p'.transferT p (p'.prodT t q₀' w).1 :=
    congrArg Prod.fst (p'.prodT_transferT_prodPt p t q₀' q₀ w)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe, prodK_transferK_prodPt]
  apply Subtype.ext
  rw [coe_transferK_apply, coe_prodK, coe_prodK, coe_prodLin_apply, coe_prodLin_apply, h2]
  rfl

end ChartPoint

end ProdTransfer

/-! ### The product orientation in two product chart points -/

section ConjExtFirstAbstract

variable {E F E' F' E₁ F₁ E₁' F₁' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [CompleteSpace F₁]
  [NormedAddCommGroup E₁'] [NormedSpace ℝ E₁'] [CompleteSpace E₁']
  [NormedAddCommGroup F₁'] [NormedSpace ℝ F₁'] [CompleteSpace F₁']

set_option maxHeartbeats 1600000 in
omit [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₁'] [CompleteSpace F₁'] in
/-- **`conjDet(Â, Γ̂) ∘ extConjDetFirst = extConjDetFirst ∘ conjDet(A, Γ)`** for product
identifications `A₁ : E₁ ≅ E × ℝ`, `A₁' : E₁' ≅ E' × ℝ`, `Γ₁`, `Γ₁'` and transfers `A`, `Γ`,
`Â`, `Γ̂` with `A₁' Â = (A × 1) A₁` and `Γ₁' Γ̂ = Γ Γ₁`. -/
theorem conjDet_extConjDetFirst_of_conj (A₁ : E₁ ≃L[ℝ] E × (Fin 1 → ℝ)) (Γ₁ : F₁ ≃L[ℝ] F)
    (A₁' : E₁' ≃L[ℝ] E' × (Fin 1 → ℝ)) (Γ₁' : F₁' ≃L[ℝ] F') (A : E ≃L[ℝ] E') (Γ : F ≃L[ℝ] F')
    (Ah : E₁ ≃L[ℝ] E₁') (Γh : F₁ ≃L[ℝ] F₁')
    (hA : ∀ v, A₁' (Ah v) = (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) (A₁ v))
    (hΓ : ∀ k, Γ₁' (Γh k) = Γ (Γ₁ k)) {L : E →L[ℝ] F} {L' : E' →L[ℝ] F'}
    (h : ∀ v, L' (A v) = Γ (L v))
    (hconj : ∀ v, extConjOp A₁' Γ₁' L' (Ah v) = Γh (extConjOp A₁ Γ₁ L v))
    (hL : L.IsFredholm) (hL' : L'.IsFredholm) (hLh : (extConjOp A₁ Γ₁ L).IsFredholm)
    (hLh' : (extConjOp A₁' Γ₁' L').IsFredholm) (y : fredholmDet L) :
    conjDet Ah Γh hconj (extConjDetFirst A₁ Γ₁ hL hLh y) =
      extConjDetFirst A₁' Γ₁' hL' hLh' (conjDet A Γ h y) := by
  have hc : (conjDet (S := extConjOp A₁ Γ₁ L) (S' := extConjOp A₁' Γ₁' L') Ah Γh hconj).trans
        (conjDet (S := extConjOp A₁' Γ₁' L') (S' := extOp L') A₁' Γ₁'
          (extConjOp_conj A₁' Γ₁' L')) =
      (conjDet (S := extConjOp A₁ Γ₁ L) (S' := extOp L) A₁ Γ₁ (extConjOp_conj A₁ Γ₁ L)).trans
        (conjDet (S := extOp L) (S' := extOp L')
          (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) Γ
          (extOp_conj_prod A Γ h)) := by
    rw [conjDet_trans Ah Γh A₁' Γ₁' hconj (extConjOp_conj A₁' Γ₁' L') (fun v => by
        rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
          extConjOp_conj A₁' Γ₁' L', hconj]),
      conjDet_trans A₁ Γ₁ (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) Γ
        (extConjOp_conj A₁ Γ₁ L) (extOp_conj_prod A Γ h) (fun v => by
        rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
          extOp_conj_prod A Γ h, extConjOp_conj A₁ Γ₁ L])]
    exact conjDet_congr (fun v => by
        rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply, hA])
      (fun k => by rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply, hΓ])
      _ _
  set u := (conjDet A₁ Γ₁ (extConjOp_conj A₁ Γ₁ L)).symm (extDetFirst hL y) with hu
  have h1 : conjDet A₁' Γ₁' (extConjOp_conj A₁' Γ₁' L') (conjDet Ah Γh hconj u) =
      conjDet (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) Γ (extOp_conj_prod A Γ h)
        (conjDet A₁ Γ₁ (extConjOp_conj A₁ Γ₁ L) u) :=
    LinearEquiv.congr_fun hc u
  have h2 : conjDet A₁ Γ₁ (extConjOp_conj A₁ Γ₁ L) u = extDetFirst hL y :=
    LinearEquiv.apply_symm_apply _ _
  have e3 := conjDet_prod_extDetFirst A Γ h hL hL' y
  have e1 : conjDet Ah Γh hconj (extConjDetFirst A₁ Γ₁ hL hLh y) = conjDet Ah Γh hconj u :=
    congrArg (conjDet Ah Γh hconj) (extConjDetFirst_apply _ _ _ _ y)
  have e2 : conjDet Ah Γh hconj u = (conjDet A₁' Γ₁' (extConjOp_conj A₁' Γ₁' L')).symm
      (extDetFirst hL' (conjDet A Γ h y)) :=
    (LinearEquiv.eq_symm_apply _).2 (h1.trans ((congrArg _ h2).trans e3))
  exact e1.trans (e2.trans (extConjDetFirst_apply _ _ _ _ _).symm)

end ConjExtFirstAbstract

section ProdOrIndep

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p p' : ChartPoint B x) (t : Fin 1 → ℝ)
  (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))

omit [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
/-- `Lin(f, x)` read in `p'` is nonempty when it is in `p`. -/
theorem nonempty_linSet_transfer (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    (hne : (p.linSet f).Nonempty) : (p'.linSet f).Nonempty :=
  let ⟨_, hL⟩ := hne
  ⟨_, p.conj_mem_linSet p' hf hx hL⟩

/-- **`L̂' Â = Γ̂ L̂`** for `L' = Γ L A⁻¹` (`transfer_prodLin` pointwise). -/
theorem prodLin_transfer_conj_apply (L : ↥p.T →L[ℝ] ↥p.K) (v : ↥(p.prodPt t q₀).T) :
    p'.prodLin t q₀' ((p.transferK p' : ↥p.K →L[ℝ] ↥p'.K) ∘L L ∘L
        (p'.transferT p : ↥p'.T →L[ℝ] ↥p.T))
      ((p.prodPt t q₀).transferT (p'.prodPt t q₀') v) =
      (p.prodPt t q₀).transferK (p'.prodPt t q₀') (p.prodLin t q₀ L v) := by
  have h := ContinuousLinearMap.ext_iff.1 (p.transfer_prodLin p' t q₀ q₀' L)
    ((p.prodPt t q₀).transferT (p'.prodPt t q₀') v)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe, transferT_trans_apply,
    transferT_self_apply] at h
  exact h.symm

/-- `A₁' Â = (A × 1) A₁` for the product chart points. -/
theorem prodT_transferT_prodPt' (v : ↥(p.prodPt t q₀).T) :
    p'.prodT t q₀' ((p.prodPt t q₀).transferT (p'.prodPt t q₀') v) =
      ((p.transferT p').prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) (p.prodT t q₀ v) :=
  p.prodT_transferT_prodPt p' t q₀ q₀' v

/-- **The determinant isomorphisms `h ↦ e ∧ h` in two product chart points are conjugate**:
`conjDet(Â, Γ̂) ∘ extConjDetFirst_p = extConjDetFirst_{p'} ∘ conjDet(A, Γ)` on `det(L)`. -/
theorem extConjDetFirst_transfer (L : ↥p.T →L[ℝ] ↥p.K) (hL : L.IsFredholm)
    (hL' : ((p.transferK p' : ↥p.K →L[ℝ] ↥p'.K) ∘L L ∘L
      (p'.transferT p : ↥p'.T →L[ℝ] ↥p.T)).IsFredholm)
    (hLh : (p.prodLin t q₀ L).IsFredholm)
    (hLh' : (p'.prodLin t q₀' ((p.transferK p' : ↥p.K →L[ℝ] ↥p'.K) ∘L L ∘L
      (p'.transferT p : ↥p'.T →L[ℝ] ↥p.T))).IsFredholm) (y : fredholmDet L) :
    conjDet ((p.prodPt t q₀).transferT (p'.prodPt t q₀'))
        ((p.prodPt t q₀).transferK (p'.prodPt t q₀')) (p.prodLin_transfer_conj_apply p' t q₀ q₀' L)
        (extConjDetFirst (p.prodT t q₀) (p.prodK t q₀) hL hLh y) =
      extConjDetFirst (p'.prodT t q₀') (p'.prodK t q₀') hL' hLh'
        (conjDet (p.transferT p') (p.transferK p') (p.transfer_conj_apply p' L) y) :=
  conjDet_extConjDetFirst_of_conj (p.prodT t q₀) (p.prodK t q₀) (p'.prodT t q₀') (p'.prodK t q₀')
    (p.transferT p') (p.transferK p') ((p.prodPt t q₀).transferT (p'.prodPt t q₀'))
    ((p.prodPt t q₀).transferK (p'.prodPt t q₀')) (p.prodT_transferT_prodPt' p' t q₀ q₀')
    (p.prodK_transferK_prodPt p' t q₀ q₀') (L := L) (L' := _) (p.transfer_conj_apply p' L)
    (p.prodLin_transfer_conj_apply p' t q₀ q₀' L) hL hL' hLh hLh' y

set_option maxHeartbeats 1600000 in
/-- **Chart independence of the product orientation of 2021 Remark 6.6.19**: for two chart
points `p`, `p'` at `x`, the product orientation `ô = e ∧ o` read in the product chart point
over `p`, transferred to the product chart point over `p'`, is the product orientation of the
transfer of `o`.  *Proof*: both are orientations of `DET(f̂, (t, x))` (a connected family), so it
suffices to compare them at one `L̂' = (Γ L₀ A⁻¹)^`; there the transfer is `conjDet(Â, Γ̂)`
with `Â = A × 1`, `Γ̂ = Γ` (`prodT_transferT_prodPt`, `prodK_transferK_prodPt`), and
`conjDet(A × 1, Γ)` commutes with `h ↦ e ∧ h` (`conjDet_prod_extDetFirst`). -/
theorem orTransfer_prodPt_prodOrFirst (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (hne : (p.linSet f).Nonempty) (o : p.Or f hf) :
    (p.prodPt t q₀).orTransfer (p'.prodPt t q₀') (theorem_3_1_18_preprint hf.param hS)
        (prod_rn_mem_smoothSet_iff.2 hx) (p.prodOrFirst t q₀ hf hx hS hne o) =
      p'.prodOrFirst t q₀' hf hx hS (p.nonempty_linSet_transfer p' hf hx hne)
        (p.orTransfer p' hf hx o) := by
  obtain ⟨L₀, hL₀⟩ := id hne
  have hf' := theorem_3_1_18_preprint hf.param hS
  have : PreconnectedSpace ((p'.prodPt t q₀').linSet
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)) :=
    isPreconnected_iff_preconnectedSpace.1 ((p'.prodPt t q₀').convex_linSet hf').isPreconnected
  have hL₀' : ((p.transferK p' : ↥p.K →L[ℝ] ↥p'.K) ∘L L₀ ∘L
      (p'.transferT p : ↥p'.T →L[ℝ] ↥p.T)) ∈ p'.linSet f := p.conj_mem_linSet p' hf hx hL₀
  have hLh := p.prodLin_mem_linSet t q₀ hf hx hS hL₀
  have hLh' := p'.prodLin_mem_linSet t q₀' hf hx hS hL₀'
  have hx' : (t, x) ∈ ((rnPolyfold 1).prod PX).smoothSet := prod_rn_mem_smoothSet_iff.2 hx
  have eR : p'.prodOrFirst t q₀' hf hx hS (p.nonempty_linSet_transfer p' hf hx hne)
      (p.orTransfer p' hf hx o) ⟨_, hLh'⟩ =
      Module.Ray.map (extConjDetFirst (p'.prodT t q₀') (p'.prodK t q₀')
        (p'.isFredholm_of_mem_linSet hf _ hL₀')
        ((p'.prodPt t q₀').isFredholm_of_mem_linSet hf' _ hLh'))
        (p.orTransfer p' hf hx o ⟨_, hL₀'⟩) :=
    p'.prodOrFirst_apply t q₀' hf hx hS _ _ _ hL₀'
  have eR2 : p.orTransfer p' hf hx o ⟨_, hL₀'⟩ =
      Module.Ray.map (conjDet (p.transferT p') (p.transferK p') (p.transfer_conj_apply p' L₀))
        (o ⟨L₀, hL₀⟩) :=
    p.orTransfer_apply p' hf hx o hL₀
  have eL : (p.prodPt t q₀).orTransfer (p'.prodPt t q₀') hf' hx'
      (p.prodOrFirst t q₀ hf hx hS hne o) ⟨_, hLh'⟩ =
      Module.Ray.map (conjDet ((p.prodPt t q₀).transferT (p'.prodPt t q₀'))
        ((p.prodPt t q₀).transferK (p'.prodPt t q₀'))
        (p.prodLin_transfer_conj_apply p' t q₀ q₀' L₀))
        (p.prodOrFirst t q₀ hf hx hS hne o ⟨_, hLh⟩) :=
    LineOrientation.conj_apply (hC' := (p'.prodPt t q₀').isFredholm_of_mem_linSet hf') _ _ _ _
      hLh hLh' _
  have eL2 : p.prodOrFirst t q₀ hf hx hS hne o ⟨_, hLh⟩ =
      Module.Ray.map (extConjDetFirst (p.prodT t q₀) (p.prodK t q₀)
        (p.isFredholm_of_mem_linSet hf _ hL₀) ((p.prodPt t q₀).isFredholm_of_mem_linSet hf' _ hLh))
        (o ⟨L₀, hL₀⟩) :=
    p.prodOrFirst_apply t q₀ hf hx hS hne o L₀ hL₀
  have hequiv : (extConjDetFirst (p.prodT t q₀) (p.prodK t q₀) (p.isFredholm_of_mem_linSet hf _ hL₀)
        ((p.prodPt t q₀).isFredholm_of_mem_linSet hf' _ hLh)) ≪≫ₗ
      conjDet ((p.prodPt t q₀).transferT (p'.prodPt t q₀'))
        ((p.prodPt t q₀).transferK (p'.prodPt t q₀'))
        (p.prodLin_transfer_conj_apply p' t q₀ q₀' L₀) =
      conjDet (p.transferT p') (p.transferK p') (p.transfer_conj_apply p' L₀) ≪≫ₗ
        extConjDetFirst (p'.prodT t q₀') (p'.prodK t q₀') (p'.isFredholm_of_mem_linSet hf _ hL₀')
          ((p'.prodPt t q₀').isFredholm_of_mem_linSet hf' _ hLh') :=
    LinearEquiv.ext fun y => p.extConjDetFirst_transfer p' t q₀ q₀' L₀ _ _ _ _ y
  have m1 := ray_map_map (extConjDetFirst (p.prodT t q₀) (p.prodK t q₀)
    (p.isFredholm_of_mem_linSet hf _ hL₀) ((p.prodPt t q₀).isFredholm_of_mem_linSet hf' _ hLh))
    (conjDet ((p.prodPt t q₀).transferT (p'.prodPt t q₀'))
      ((p.prodPt t q₀).transferK (p'.prodPt t q₀')) (p.prodLin_transfer_conj_apply p' t q₀ q₀' L₀))
    (o ⟨L₀, hL₀⟩)
  have m2 := ray_map_map (conjDet (p.transferT p') (p.transferK p') (p.transfer_conj_apply p' L₀))
    (extConjDetFirst (p'.prodT t q₀') (p'.prodK t q₀') (p'.isFredholm_of_mem_linSet hf _ hL₀')
      ((p'.prodPt t q₀').isFredholm_of_mem_linSet hf' _ hLh')) (o ⟨L₀, hL₀⟩)
  have m3 := congrArg (fun e => Module.Ray.map e (o ⟨L₀, hL₀⟩)) hequiv
  refine LineOrientation.eq_of_apply_eq ⟨_, hLh'⟩ ?_
  refine (eL.trans (congrArg (Module.Ray.map (conjDet ((p.prodPt t q₀).transferT (p'.prodPt t q₀'))
    ((p.prodPt t q₀).transferK (p'.prodPt t q₀'))
    (p.prodLin_transfer_conj_apply p' t q₀ q₀' L₀))) eL2)).trans ?_
  refine Eq.trans ?_ (eR.trans (congrArg (Module.Ray.map (extConjDetFirst (p'.prodT t q₀')
    (p'.prodK t q₀') (p'.isFredholm_of_mem_linSet hf _ hL₀')
    ((p'.prodPt t q₀').isFredholm_of_mem_linSet hf' _ hLh'))) eR2)).symm
  exact m1.trans (m3.trans m2.symm)

end ChartPoint

end ProdOrIndep

end Polyfold
