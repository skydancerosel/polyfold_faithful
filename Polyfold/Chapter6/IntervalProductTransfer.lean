import Polyfold.Chapter6.IntervalProductKernels

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19** (preprint Remark 6.42, p. 230) over the M-polyfold with boundary `[0, 1] × X`:
the orientation `e ∧ o` of `f̂` does not depend on the chart in which it is read.

# The orientation `e ∧ o` in two product charts of `[0, 1] × X`

## What is formalized

* `UnitCube.trans_eq_affine`, `hasFDerivAt_trans`: the coordinate change of the two charts of
  `[0, 1]` is affine with slope the product of their signs (`+1` between equal charts, `−1`
  between `t ↦ t` and `t ↦ 1 − t`).
* `ChartPoint.baseDeriv_ivPt`: the base transition of two product chart points
  `p.ivPt b`, `p'.ivPt b'` at `(t, x)` has the derivative `(σ, v) ↦ (± σ, D(τ ∘ r)(z) v)`;
  `fiberMap_ivPt`: the fibre transition is that of the chart points of `X`;
  `ivT_transferT_ivPt`: under `ivT` (which carries the sign of its chart) the transition is
  `A × 1`, with no sign.
* **`ChartPoint.orTransfer_ivPt_ivOrFirst`**: the orientation `e ∧ o` read over `(p, b)`,
  transferred to the product chart point over `(p', b')`, is `e ∧` (the transfer of `o`), for
  any two charts of `X` and any two charts of `[0, 1]` at the point: the standard orientation of
  `[0, 1]` is the same in the chart `t ↦ t` and in the chart `t ↦ 1 − t`.
-/

open Module TensorProduct Bundle Topology Set Filter

noncomputable section

namespace Polyfold

open StrongRetr UnitCube

universe u v

/-! ### The coordinate change of `[0, 1]` -/

namespace UnitCube

/-- The coordinate change of two charts of `[0, 1]` is affine, with slope the product of the
signs of the charts. -/
lemma trans_eq_affine (b b' : Fin 1 → Bool) :
    ∃ k : Fin 1 → ℝ, ∀ v, trans b b' v = (ivSign b * ivSign b') • v + k := by
  refine ⟨fun _ => (if b' 0 then 0 else 1) + ivSign b' * (if b 0 then 0 else 1), fun v => ?_⟩
  funext i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  simp only [trans, fl, ivSign, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  cases b 0 <;> cases b' 0 <;> simp <;> ring

/-- The derivative of the coordinate change of `[0, 1]`. -/
lemma hasFDerivAt_trans (b b' : Fin 1 → Bool) (a : Fin 1 → ℝ) :
    HasFDerivAt (trans b b') ((ivSign b * ivSign b') • ContinuousLinearMap.id ℝ (Fin 1 → ℝ)) a := by
  obtain ⟨k, hk⟩ := trans_eq_affine b b'
  have h : trans b b' = fun v => (ivSign b * ivSign b') • v + k := funext hk
  rw [h]
  exact ((hasFDerivAt_id a).const_smul (ivSign b * ivSign b')).add_const k

/-- The sc-derivative of the coordinate change of `[0, 1]` at a point of `[0, 1)`, the boundary
point included. -/
lemma scDeriv_trans (b b' : Fin 1 → Bool) {a : Fin 1 → ℝ} (ha : a ∈ modelO 1) :
    scDeriv (E := rnSc 1) (F := rnSc 1) (modelO 1) (trans b b') (a : (rnSc 1) 1) =
      (ivSign b * ivSign b') • ContinuousLinearMap.id ℝ (Fin 1 → ℝ) := by
  have hrel := isRelOpen_modelO 1
  have hsm : IsScSmooth (E := rnSc 1) (F := rnSc 1) (modelO 1) (trans b b') :=
    IsScSmooth.of_contDiffOn_finiteDimensional hrel.isScDomain (contDiff_trans b b').contDiffOn
  have h1 := hasFDerivWithinAt_scDeriv_rnRel hsm.isSc1 ha
  exact (uniqueDiffWithinAt_rnRel hrel ha).eq h1 (hasFDerivAt_trans b b' a).hasFDerivWithinAt

end UnitCube

/-! ### The transition of two product chart points -/

section IvTransfer

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))]

namespace ChartPoint

variable {x : X} (p p' : ChartPoint B x) (b : Fin 1 → Bool) {t : Fin 1 → unitInterval}
  (ht : t ∈ (chart b).source) (b' : Fin 1 → Bool) (ht' : t ∈ (chart b').source)
  (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))

/-- **The base transition of two product chart points is `(± 1) × (τ ∘ r)`**: its derivative at
`(χ_b(t), z)` is `(σ, v) ↦ (± σ, D(τ ∘ r)(z) v)`, the sign the product of the signs of the two
charts of `[0, 1]`. -/
theorem baseDeriv_ivPt (v : (Fin 1 → ℝ) × p.c.φ.model.E 0) :
    (p.ivPt b ht q₀).baseDeriv (p'.ivPt b' ht' q₀') v =
      ((ivSign b * ivSign b') • v.1, p.baseDeriv p' v.2) := by
  set P₁ := p.ivPt b ht q₀ with hP₁
  set P₂ := p'.ivPt b' ht' q₀' with hP₂
  set R₁ := p.baseRet p' with hR₁
  have hrel := isRelOpen_modelO 1
  have hg : IsScSmooth R₁.U (p.c.φ.transition p'.c.φ ∘ R₁) :=
    (p.c.isChart.compatible p'.c.isChart (P := PX)).1.comp_isScSmooth _ (p.baseRet_retract p')
  let Rhat : ScRetraction ((rnSc 1).prod p.c.φ.model.E) (halfC 1 ×ˢ p.c.φ.model.C) :=
    (ScRetraction.id hrel).prod R₁
  let V := (Rhat.restrict (P₁.isOpen_overlapW P₂)).U
  have hV : IsRelOpenInQuadrant ((rnSc 1).prod p.c.φ.model.E) (halfC 1 ×ˢ p.c.φ.model.C) V :=
    (Rhat.restrict (P₁.isOpen_overlapW P₂)).relOpen
  have hV₁ : V ⊆ (P₁.baseRet P₂).U := fun u hu =>
    ⟨⟨hu.1.1, p.baseRet_U_subset p' hu.1.2⟩, hu.2⟩
  have hV₂ : V ⊆ modelO 1 ×ˢ R₁.U := inter_subset_left
  have htr : IsScSmooth (E := rnSc 1) (F := rnSc 1) (modelO 1) (trans b b') :=
    IsScSmooth.of_contDiffOn_finiteDimensional hrel.isScDomain (contDiff_trans b b').contDiffOn
  have hf₂ : IsScSmooth (E := (rnSc 1).prod p.c.φ.model.E) (F := (rnSc 1).prod p'.c.φ.model.E)
      (modelO 1 ×ˢ R₁.U) (Prod.map (trans b b') (p.c.φ.transition p'.c.φ ∘ R₁)) :=
    IsScSmooth.prodMap hrel.isScDomain R₁.isScDomain (hrel.prod R₁.relOpen).isScDomain htr hg
  have heq : EqOn (P₁.c.φ.transition P₂.c.φ ∘ P₁.baseRet P₂)
      (Prod.map (trans b b') (p.c.φ.transition p'.c.φ ∘ R₁)) V := by
    intro u hu
    exact Prod.ext (chart_transition_eqOn b b' hu.1.1) rfl
  have hzb : ((rnSc 1).prod p.c.φ.model.E).toBase 1
      (((chart b t : Fin 1 → ℝ), p.z) : ((rnSc 1).prod p.c.φ.model.E) 1) =
      ((chart b t : Fin 1 → ℝ), p.c.φ.model.E.toBase 1 p.z) := p.ivPt_toBase b ht q₀
  have hz₁ : p.c.φ.model.E.toBase 1 p.z ∈ R₁.U := p.z_mem_baseRet p'
  have hz : P₁.z ∈ ((rnSc 1).prod p.c.φ.model.E).lvlSet V 1 := by
    change ((rnSc 1).prod p.c.φ.model.E).toBase 1
      (((chart b t : Fin 1 → ℝ), p.z) : ((rnSc 1).prod p.c.φ.model.E) 1) ∈ V
    rw [hzb]
    refine ⟨⟨chart_mem_modelO ht, hz₁⟩, ?_⟩
    change ((chart b t : Fin 1 → ℝ), r p.c.R (p.c.φ.model.E.toBase 1 p.z)) ∈ P₁.overlapW P₂
    rw [p.r_toBase_z]
    have h := P₁.toBase_z_mem_overlapW P₂
    change ((rnSc 1).prod p.c.φ.model.E).toBase 1
      (((chart b t : Fin 1 → ℝ), p.z) : ((rnSc 1).prod p.c.φ.model.E) 1) ∈
        P₁.overlapW P₂ at h
    rwa [hzb] at h
  have hz' : P₁.z ∈ ((rnSc 1).prod p.c.φ.model.E).lvlSet (modelO 1 ×ˢ R₁.U) 1 :=
    ((rnSc 1).prod p.c.φ.model.E).lvlSet_mono hV₂ 1 hz
  have h1 := scDeriv_eq_of_eqOn_relOpen hV (P₁.isSc1_transition P₂) hf₂.isSc1 hV₁ hV₂ heq hz
  have h2 := scDeriv_prodMap (F := rnSc 1) (F' := p'.c.φ.model.E) hrel R₁.relOpen htr hg hz'
  have hid := scDeriv_trans b b' (chart_mem_modelO ht)
  have h3 : P₁.baseDeriv P₂ =
      ((ivSign b * ivSign b') • ContinuousLinearMap.id ℝ (Fin 1 → ℝ)).prodMap
        (p.baseDeriv p') := by
    refine (h1.trans h2).trans ?_
    exact congrArg (fun L : (rnSc 1) 0 →L[ℝ] (rnSc 1) 0 => L.prodMap (p.baseDeriv p')) hid
  exact ContinuousLinearMap.ext_iff.1 h3 v

/-- **The fibre transition of two product chart points is that of the chart points**: `Γ̂ = Γ`
on `K_z`. -/
theorem fiberMap_ivPt {k : p.c.F 0} (hk : k ∈ p.K) :
    (p.ivPt b ht q₀).fiberMap (p'.ivPt b' ht' q₀') k = p.fiberMap p' k := by
  have hk' : k ∈ (p.ivPt b ht q₀).K := (p.mem_ivPt_K_iff b ht q₀ k).2 hk
  have hK : (p.c.φ.model.E.toBase 1 p.z, k) ∈ p.c.K := p.mem_K_of_mem hk
  have hzP : (ivChart b p.c q₀).φ.model.E.toBase 1 (p.ivPt b ht q₀).z =
      (((chart b t : Fin 1 → ℝ), p.c.φ.model.E.toBase 1 p.z) :
        ((rnSc 1).prod p.c.φ.model.E) 0) := p.ivPt_toBase b ht q₀
  have hPy : P (p.c.toPartialEquiv.symm (p.c.φ.model.E.toBase 1 p.z, k)) = x := by
    rw [p.c.proj_symm hK]
    change p.c.φ.symm (p.c.φ.model.E.toBase 1 p.z) = x
    rw [p.toBase_z, p.c.φ.symm_apply_apply p.mem_source]
  have hmem : (((((chart b t : Fin 1 → ℝ), p.c.φ.model.E.toBase 1 p.z) :
        ((rnSc 1).prod p.c.φ.model.E) 0), k) :
        (ivChart b p.c q₀).φ.model.E 0 × (ivChart b p.c q₀).F 0) ∈
      (ivChart b p.c q₀).overlap (ivChart b' p'.c q₀') := by
    refine (PullbackChartData.mem_overlap_iff _ _ _ _).2
      ⟨⟨((t, x), p.c.toPartialEquiv.symm (p.c.φ.model.E.toBase 1 p.z, k)), hPy⟩,
        ⟨ht, p.mem_source⟩, ⟨ht', p'.mem_source⟩, ?_⟩
    change (((chart b t : Fin 1 → ℝ), p.c.φ x),
        (p.c (p.c.toPartialEquiv.symm (p.c.φ.model.E.toBase 1 p.z, k))).2) =
      (((chart b t : Fin 1 → ℝ), p.c.φ.model.E.toBase 1 p.z), k)
    rw [← p.toBase_z, p.c.apply_symm hK]
  have hg : (ivData b p.c).g
      (((chart b t : Fin 1 → ℝ), p.c.φ.model.E.toBase 1 p.z) :
        ((rnSc 1).prod p.c.φ.model.E) 0) = p.c.φ.model.E.toBase 1 p.z := by
    change p.c.φ (p.c.φ.symm (p.c.φ.model.E.toBase 1 p.z)) = _
    exact p.c.φ.apply_symm_apply p.toBase_z_mem_O
  rw [(p.ivPt b ht q₀).fiberMap_apply_of_mem (p'.ivPt b' ht' q₀') hk',
    p.fiberMap_apply_of_mem p' hk]
  change ((ivChart b p.c q₀).transition (ivChart b' p'.c q₀')
    ((ivChart b p.c q₀).φ.model.E.toBase 1 (p.ivPt b ht q₀).z, k)).2 = _
  rw [hzP]
  refine (congrArg Prod.snd (PullbackChartData.transition_eqOn _ _ _ _ hmem)).symm.trans ?_
  change (p.c.transition p'.c ((ivData b p.c).g
    (((chart b t : Fin 1 → ℝ), p.c.φ.model.E.toBase 1 p.z) :
      ((rnSc 1).prod p.c.φ.model.E) 0), k)).2 = _
  rw [hg]

/-- **`Â = A × 1`**: under `ivT`, the identification `T_{(t,z)} ≅ T_{(t,z')}` of two product
chart points is `(v, σ) ↦ (A v, σ)`, for equal and for different charts of `[0, 1]`: `ivT`
carries the sign of its chart, and the two signs and the slope of the coordinate change cancel. -/
theorem ivT_transferT_ivPt (w : ↥(p.ivPt b ht q₀).T) :
    p'.ivT b' ht' q₀' ((p.ivPt b ht q₀).transferT (p'.ivPt b' ht' q₀') w) =
      (p.transferT p' (p.ivT b ht q₀ w).1, (p.ivT b ht q₀ w).2) := by
  refine Prod.ext (Subtype.ext ?_) ?_
  · change Prod.snd (α := Fin 1 → ℝ) (β := p'.c.φ.model.E 0)
      ((p.ivPt b ht q₀).transferT (p'.ivPt b' ht' q₀') w).1 =
        p.baseDeriv p' (Prod.snd (α := Fin 1 → ℝ) (β := p.c.φ.model.E 0) w.1)
    rw [coe_transferT_apply]
    exact congrArg Prod.snd (p.baseDeriv_ivPt p' b ht b' ht' q₀ q₀' w.1)
  · change ivSign b' • Prod.fst (α := Fin 1 → ℝ) (β := p'.c.φ.model.E 0)
      ((p.ivPt b ht q₀).transferT (p'.ivPt b' ht' q₀') w).1 =
        ivSign b • Prod.fst (α := Fin 1 → ℝ) (β := p.c.φ.model.E 0) w.1
    rw [coe_transferT_apply]
    refine (congrArg (fun y : Fin 1 → ℝ => ivSign b' • y)
      (congrArg Prod.fst (p.baseDeriv_ivPt p' b ht b' ht' q₀ q₀' w.1))).trans ?_
    change ivSign b' • ((ivSign b * ivSign b') •
      Prod.fst (α := Fin 1 → ℝ) (β := p.c.φ.model.E 0) w.1) = _
    rw [smul_smul, mul_comm (ivSign b) (ivSign b'), ← mul_assoc, ivSign_mul_self, one_mul]

/-- **`Γ̂ = Γ`**: under `ivK`, the identification `K̂_z ≅ K̂'_{z'}` of the product chart points is
that of the chart points. -/
theorem ivK_transferK_ivPt (k : ↥(p.ivPt b ht q₀).K) :
    p'.ivK b' ht' q₀' ((p.ivPt b ht q₀).transferK (p'.ivPt b' ht' q₀') k) =
      p.transferK p' (p.ivK b ht q₀ k) := by
  refine Subtype.ext ?_
  change (p.ivPt b ht q₀).fiberMap (p'.ivPt b' ht' q₀') k.1 = p.fiberMap p' k.1
  exact p.fiberMap_ivPt p' b ht b' ht' q₀ q₀' ((p.mem_ivPt_K_iff b ht q₀ k.1).1 k.2)

/-- **The conjugate of `L̂` is the lift of the conjugate of `L`**: `Γ̂ L̂ Â⁻¹ = (Γ L A⁻¹)^`. -/
theorem transfer_ivLin (L : ↥p.T →L[ℝ] ↥p.K) :
    (((p.ivPt b ht q₀).transferK (p'.ivPt b' ht' q₀') :
        ↥(p.ivPt b ht q₀).K →L[ℝ] ↥(p'.ivPt b' ht' q₀').K) ∘L p.ivLin b ht q₀ L ∘L
      ((p'.ivPt b' ht' q₀').transferT (p.ivPt b ht q₀) :
        ↥(p'.ivPt b' ht' q₀').T →L[ℝ] ↥(p.ivPt b ht q₀).T)) =
    p'.ivLin b' ht' q₀' ((p.transferK p' : ↥p.K →L[ℝ] ↥p'.K) ∘L L ∘L
      (p'.transferT p : ↥p'.T →L[ℝ] ↥p.T)) := by
  refine ContinuousLinearMap.ext fun w => (p'.ivK b' ht' q₀').injective ?_
  have h2 : (p.ivT b ht q₀ ((p'.ivPt b' ht' q₀').transferT (p.ivPt b ht q₀) w)).1 =
      p'.transferT p (p'.ivT b' ht' q₀' w).1 :=
    congrArg Prod.fst (p'.ivT_transferT_ivPt p b' ht' b ht q₀' q₀ w)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe, ivK_transferK_ivPt]
  apply Subtype.ext
  rw [coe_transferK_apply, coe_ivK, coe_ivK, coe_ivLin_apply, coe_ivLin_apply, h2]
  rfl

end ChartPoint

end IvTransfer

section IvOrIndep

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p p' : ChartPoint B x) (b : Fin 1 → Bool) {t : Fin 1 → unitInterval}
  (ht : t ∈ (chart b).source) (b' : Fin 1 → Bool) (ht' : t ∈ (chart b').source)
  (q₀ q₀' : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))

/-- **`L̂' Â = Γ̂ L̂`** for `L' = Γ L A⁻¹` (`transfer_ivLin` pointwise). -/
theorem ivLin_transfer_conj_apply (L : ↥p.T →L[ℝ] ↥p.K) (v : ↥(p.ivPt b ht q₀).T) :
    p'.ivLin b' ht' q₀' ((p.transferK p' : ↥p.K →L[ℝ] ↥p'.K) ∘L L ∘L
        (p'.transferT p : ↥p'.T →L[ℝ] ↥p.T))
      ((p.ivPt b ht q₀).transferT (p'.ivPt b' ht' q₀') v) =
      (p.ivPt b ht q₀).transferK (p'.ivPt b' ht' q₀') (p.ivLin b ht q₀ L v) := by
  have h := ContinuousLinearMap.ext_iff.1 (p.transfer_ivLin p' b ht b' ht' q₀ q₀' L)
    ((p.ivPt b ht q₀).transferT (p'.ivPt b' ht' q₀') v)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe, transferT_trans_apply,
    transferT_self_apply] at h
  exact h.symm

/-- `A₁' Â = (A × 1) A₁` for the product chart points. -/
theorem ivT_transferT_ivPt' (v : ↥(p.ivPt b ht q₀).T) :
    p'.ivT b' ht' q₀' ((p.ivPt b ht q₀).transferT (p'.ivPt b' ht' q₀') v) =
      ((p.transferT p').prodCongr (ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ))) (p.ivT b ht q₀ v) :=
  p.ivT_transferT_ivPt p' b ht b' ht' q₀ q₀' v

/-- **The determinant isomorphisms `h ↦ e ∧ h` in two product chart points are conjugate**:
`conjDet(Â, Γ̂) ∘ extConjDetFirst_p = extConjDetFirst_{p'} ∘ conjDet(A, Γ)` on `det(L)`. -/
theorem extConjDetFirst_transfer_iv (L : ↥p.T →L[ℝ] ↥p.K) (hL : L.IsFredholm)
    (hL' : ((p.transferK p' : ↥p.K →L[ℝ] ↥p'.K) ∘L L ∘L
      (p'.transferT p : ↥p'.T →L[ℝ] ↥p.T)).IsFredholm)
    (hLh : (p.ivLin b ht q₀ L).IsFredholm)
    (hLh' : (p'.ivLin b' ht' q₀' ((p.transferK p' : ↥p.K →L[ℝ] ↥p'.K) ∘L L ∘L
      (p'.transferT p : ↥p'.T →L[ℝ] ↥p.T))).IsFredholm) (y : fredholmDet L) :
    conjDet ((p.ivPt b ht q₀).transferT (p'.ivPt b' ht' q₀'))
        ((p.ivPt b ht q₀).transferK (p'.ivPt b' ht' q₀'))
            (p.ivLin_transfer_conj_apply p' b ht b' ht' q₀ q₀' L)
        (extConjDetFirst (p.ivT b ht q₀) (p.ivK b ht q₀) hL hLh y) =
      extConjDetFirst (p'.ivT b' ht' q₀') (p'.ivK b' ht' q₀') hL' hLh'
        (conjDet (p.transferT p') (p.transferK p') (p.transfer_conj_apply p' L) y) :=
  conjDet_extConjDetFirst_of_conj (p.ivT b ht q₀) (p.ivK b ht q₀) (p'.ivT b' ht' q₀')
      (p'.ivK b' ht' q₀')
    (p.transferT p') (p.transferK p') ((p.ivPt b ht q₀).transferT (p'.ivPt b' ht' q₀'))
    ((p.ivPt b ht q₀).transferK (p'.ivPt b' ht' q₀')) (p.ivT_transferT_ivPt' p' b ht b' ht' q₀ q₀')
    (p.ivK_transferK_ivPt p' b ht b' ht' q₀ q₀') (L := L) (L' := _) (p.transfer_conj_apply p' L)
    (p.ivLin_transfer_conj_apply p' b ht b' ht' q₀ q₀' L) hL hL' hLh hLh' y

set_option maxHeartbeats 1600000 in
-- the determinant lines over the two product chart points are compared term by term
/-- **Chart independence of the orientation `e ∧ o` of 2021 Remark 6.6.19 over `[0, 1] × X`**:
for two chart points `p`, `p'` at `x` and two charts `χ_b`, `χ_{b'}` of `[0, 1]` at `t`, the
orientation `ô = e ∧ o` read in the product chart point over `(p, b)`, transferred to the product
chart point over `(p', b')`, is the orientation `e ∧` (the transfer of `o`).  *Proof*: both are
orientations of `DET(f̂, (t, x))` (a connected family), so it suffices to compare them at one
`L̂' = (Γ L₀ A⁻¹)^`; there the transfer is `conjDet(Â, Γ̂)` with `Â = A × 1`, `Γ̂ = Γ`
(`ivT_transferT_ivPt`, `ivK_transferK_ivPt`), and `conjDet(A × 1, Γ)` commutes with
`h ↦ e ∧ h` (`conjDet_prod_extDetFirst`). -/
theorem orTransfer_ivPt_ivOrFirst (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
        (hx : x ∈ PX.smoothSet)
    {S : (Fin 1 → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hne : (p.linSet f).Nonempty) (o : p.Or f hf) :
    (p.ivPt b ht q₀).orTransfer (p'.ivPt b' ht' q₀') (theorem_3_1_18_preprint hfc hS)
        (prod_cube_mem_smoothSet_iff.2 hx) (p.ivOrFirst b ht q₀ hf hfc hx hS hne o) =
      p'.ivOrFirst b' ht' q₀' hf hfc hx hS (p.nonempty_linSet_transfer p' hf hx hne)
        (p.orTransfer p' hf hx o) := by
  obtain ⟨L₀, hL₀⟩ := id hne
  have hf' := theorem_3_1_18_preprint hfc hS
  have : PreconnectedSpace ((p'.ivPt b' ht' q₀').linSet
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)) :=
    isPreconnected_iff_preconnectedSpace.1 ((p'.ivPt b' ht' q₀').convex_linSet hf').isPreconnected
  have hL₀' : ((p.transferK p' : ↥p.K →L[ℝ] ↥p'.K) ∘L L₀ ∘L
      (p'.transferT p : ↥p'.T →L[ℝ] ↥p.T)) ∈ p'.linSet f := p.conj_mem_linSet p' hf hx hL₀
  have hLh := p.ivLin_mem_linSet b ht q₀ hf hx hS hL₀
  have hLh' := p'.ivLin_mem_linSet b' ht' q₀' hf hx hS hL₀'
  have hx' : (t, x) ∈ ((cubePolyfold 1).prod PX).smoothSet := prod_cube_mem_smoothSet_iff.2 hx
  have eR : p'.ivOrFirst b' ht' q₀' hf hfc hx hS (p.nonempty_linSet_transfer p' hf hx hne)
      (p.orTransfer p' hf hx o) ⟨_, hLh'⟩ =
      Module.Ray.map (extConjDetFirst (p'.ivT b' ht' q₀') (p'.ivK b' ht' q₀')
        (p'.isFredholm_of_mem_linSet hf _ hL₀')
        ((p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hf' _ hLh'))
        (p.orTransfer p' hf hx o ⟨_, hL₀'⟩) :=
    p'.ivOrFirst_apply b' ht' q₀' hf hfc hx hS _ _ _ hL₀'
  have eR2 : p.orTransfer p' hf hx o ⟨_, hL₀'⟩ =
      Module.Ray.map (conjDet (p.transferT p') (p.transferK p') (p.transfer_conj_apply p' L₀))
        (o ⟨L₀, hL₀⟩) :=
    p.orTransfer_apply p' hf hx o hL₀
  have eL : (p.ivPt b ht q₀).orTransfer (p'.ivPt b' ht' q₀') hf' hx'
      (p.ivOrFirst b ht q₀ hf hfc hx hS hne o) ⟨_, hLh'⟩ =
      Module.Ray.map (conjDet ((p.ivPt b ht q₀).transferT (p'.ivPt b' ht' q₀'))
        ((p.ivPt b ht q₀).transferK (p'.ivPt b' ht' q₀'))
        (p.ivLin_transfer_conj_apply p' b ht b' ht' q₀ q₀' L₀))
        (p.ivOrFirst b ht q₀ hf hfc hx hS hne o ⟨_, hLh⟩) :=
    LineOrientation.conj_apply (hC' := (p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hf') _ _ _ _
      hLh hLh' _
  have eL2 : p.ivOrFirst b ht q₀ hf hfc hx hS hne o ⟨_, hLh⟩ =
      Module.Ray.map (extConjDetFirst (p.ivT b ht q₀) (p.ivK b ht q₀)
        (p.isFredholm_of_mem_linSet hf _ hL₀) ((p.ivPt b ht q₀).isFredholm_of_mem_linSet hf' _ hLh))
        (o ⟨L₀, hL₀⟩) :=
    p.ivOrFirst_apply b ht q₀ hf hfc hx hS hne o L₀ hL₀
  have hequiv : (extConjDetFirst (p.ivT b ht q₀) (p.ivK b ht q₀)
      (p.isFredholm_of_mem_linSet hf _ hL₀)
        ((p.ivPt b ht q₀).isFredholm_of_mem_linSet hf' _ hLh)) ≪≫ₗ
      conjDet ((p.ivPt b ht q₀).transferT (p'.ivPt b' ht' q₀'))
        ((p.ivPt b ht q₀).transferK (p'.ivPt b' ht' q₀'))
        (p.ivLin_transfer_conj_apply p' b ht b' ht' q₀ q₀' L₀) =
      conjDet (p.transferT p') (p.transferK p') (p.transfer_conj_apply p' L₀) ≪≫ₗ
        extConjDetFirst (p'.ivT b' ht' q₀') (p'.ivK b' ht' q₀')
            (p'.isFredholm_of_mem_linSet hf _ hL₀')
          ((p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hf' _ hLh') :=
    LinearEquiv.ext fun y => p.extConjDetFirst_transfer_iv p' b ht b' ht' q₀ q₀' L₀ _ _ _ _ y
  have m1 := ray_map_map (extConjDetFirst (p.ivT b ht q₀) (p.ivK b ht q₀)
    (p.isFredholm_of_mem_linSet hf _ hL₀) ((p.ivPt b ht q₀).isFredholm_of_mem_linSet hf' _ hLh))
    (conjDet ((p.ivPt b ht q₀).transferT (p'.ivPt b' ht' q₀'))
      ((p.ivPt b ht q₀).transferK (p'.ivPt b' ht' q₀'))
          (p.ivLin_transfer_conj_apply p' b ht b' ht' q₀ q₀' L₀))
    (o ⟨L₀, hL₀⟩)
  have m2 := ray_map_map (conjDet (p.transferT p') (p.transferK p') (p.transfer_conj_apply p' L₀))
    (extConjDetFirst (p'.ivT b' ht' q₀') (p'.ivK b' ht' q₀') (p'.isFredholm_of_mem_linSet hf _ hL₀')
      ((p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hf' _ hLh')) (o ⟨L₀, hL₀⟩)
  have m3 := congrArg (fun e => Module.Ray.map e (o ⟨L₀, hL₀⟩)) hequiv
  refine LineOrientation.eq_of_apply_eq ⟨_, hLh'⟩ ?_
  refine (eL.trans (congrArg (Module.Ray.map (conjDet ((p.ivPt b ht q₀).transferT
      (p'.ivPt b' ht' q₀'))
    ((p.ivPt b ht q₀).transferK (p'.ivPt b' ht' q₀'))
    (p.ivLin_transfer_conj_apply p' b ht b' ht' q₀ q₀' L₀))) eL2)).trans ?_
  refine Eq.trans ?_ (eR.trans (congrArg (Module.Ray.map (extConjDetFirst (p'.ivT b' ht' q₀')
    (p'.ivK b' ht' q₀') (p'.isFredholm_of_mem_linSet hf _ hL₀')
    ((p'.ivPt b' ht' q₀').isFredholm_of_mem_linSet hf' _ hLh'))) eR2)).symm
  exact m1.trans (m3.trans m2.symm)

end ChartPoint

end IvOrIndep

end Polyfold
