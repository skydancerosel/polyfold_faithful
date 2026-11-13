import Polyfold.Chapter3.LinearizationChartChange

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §3.1: the linearization
`f'(y) : T_yX → Y_y` of an sc-smooth section at a zero (before Definition 3.1.4, used in
Theorem 3.1.22 (preprint 3.19), p. 100, and Definition 3.6.6), as an intrinsic linear map.

# The intrinsic linearization `f'(y) : T_yX → Y_y` at a zero

The project has the linear structure of `T_xX` (`tangentFiber`, `TangentSpaceLinear`) and of the
fibres `Y_y = P⁻¹(y)` (instance arguments of `StrongBundle`), and the linearization in a strong
bundle chart, `Lin(z) = D(f̂ ∘ r)(z)|_{T_zO}` (`linAt`).  Here:

* `StrongBundleChart.fiberLin c hy : Y_y →ₗ F`, the fibre part of `Φ` (linear, injective,
  `fiberLin_injective`), whose range contains every `k` with `(φ(y), k) ∈ K`
  (`mem_range_fiberLin`); the fibre operator `Γ(z)` of a transition is
  `Φ'_y ∘ Φ_y⁻¹` (`transitionFiberCLM_fiberLin`).
* `StrongBundleChart.linChart c f hx : T_xX →ₗ F`, `α ↦ D(f̂ ∘ r)(φ(x)) (Tφ α)`, and at a zero its
  values lie in `Φ_y(Y_y)` (`linChart_mem`).
* **`StrongBundle.linIntr hf hc hx h0 : T_xX →ₗ[ℝ] Y_x`**, the text's `f'(x)` read through the
  chart `c`: `Φ_x⁻¹ ∘ Lin(φ(x)) ∘ Tφ`.
* **`StrongBundle.linIntr_chart_independent`**: it does not depend on the chart.  The proof is the
  chain rule `linAt_chart_change_key`
  (`Γ(z) ∘ D(f̂ ∘ r)(z) = D(f̂' ∘ r')(z') ∘ D(τ ∘ r_W)(z)`), with
  `Tφ' = D(τ ∘ r_W)(φ(x)) ∘ Tφ` on `T_xX` (`transitionCLM_spec`, `retractTangentMap_apply`) and
  `Γ(z) = Φ'_x ∘ Φ_x⁻¹`.
-/

open Set Function Module

noncomputable section

namespace Polyfold

universe u v

open StrongRetr MPolyfold

section FiberLin

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundleChart

variable (c c' : StrongBundleChart PX P)

/-- The fibre part `Φ_y : Y_y → F` of a strong bundle chart, a linear map. -/
def fiberLin {y : X} (hy : y ∈ c.φ.source) : (P ⁻¹' {y}) →ₗ[ℝ] c.F 0 where
  toFun v := (c (v : Y)).2
  map_add' := (c.fiber_linear y hy).map_add
  map_smul' := (c.fiber_linear y hy).map_smul

@[simp] lemma fiberLin_apply {y : X} (hy : y ∈ c.φ.source) (v : P ⁻¹' {y}) :
    c.fiberLin hy v = (c (v : Y)).2 := rfl

lemma fiberLin_src {y : X} (hy : y ∈ c.φ.source) (v : P ⁻¹' {y}) :
    (v : Y) ∈ c.toPartialEquiv.source :=
  c.mem_source_of_proj (by rw [show P v = y from v.2]; exact hy)

lemma apply_fiberLin {y : X} (hy : y ∈ c.φ.source) (v : P ⁻¹' {y}) :
    c (v : Y) = (c.φ y, c.fiberLin hy v) :=
  Prod.ext (by rw [c.fst_apply (by rw [show P v = y from v.2]; exact hy), show P v = y from v.2])
    rfl

lemma fiberLin_injective {y : X} (hy : y ∈ c.φ.source) : Injective (c.fiberLin hy) := by
  intro v w h
  apply Subtype.ext
  apply c.toPartialEquiv.injOn (c.fiberLin_src hy v) (c.fiberLin_src hy w)
  rw [c.apply_fiberLin hy v, c.apply_fiberLin hy w, h]

lemma mem_range_fiberLin {y : X} (hy : y ∈ c.φ.source) {k : c.F 0} (hk : (c.φ y, k) ∈ c.K) :
    k ∈ LinearMap.range (c.fiberLin hy) := by
  have hP : P (c.toPartialEquiv.symm (c.φ y, k)) = y := by
    rw [c.proj_symm hk]; exact c.φ.symm_apply_apply hy
  refine ⟨⟨_, hP⟩, ?_⟩
  change (c (c.toPartialEquiv.symm (c.φ y, k))).2 = k
  rw [c.apply_symm hk]

/-- The fibre operator `Γ(z)` of the transition `Φ' ∘ Φ⁻¹` over `z = φ(y)` is `Φ'_y ∘ Φ_y⁻¹`. -/
lemma transitionFiberCLM_fiberLin {y : X} (hy : y ∈ c.φ.source) (hy' : y ∈ c'.φ.source)
    {u : c.φ.model.E 0} (hu : u = c.φ y) (hO : u ∈ c.φ.model.O)
    (hV' : c.φ.symm u ∈ c'.φ.source) (v : P ⁻¹' {y}) :
    c.transitionFiberCLM c' hO hV' (c.fiberLin hy v) = c'.fiberLin hy' v := by
  subst hu
  have hK : (c.φ y, c.fiberLin hy v) ∈ c.K := by
    rw [← c.apply_fiberLin hy v, ← c.image_source]; exact ⟨_, c.fiberLin_src hy v, rfl⟩
  rw [c.transitionFiberCLM_apply_of_mem c' hO hV' hK]
  change (c' (c.toPartialEquiv.symm (c.φ y, c.fiberLin hy v))).2 = _
  rw [← c.apply_fiberLin hy v, c.toPartialEquiv.left_inv (c.fiberLin_src hy v)]
  rfl

/-- The linearization read in the chart `c`, before identifying the fibre:
`α ↦ D(f̂ ∘ r)(φ(x)) (Tφ α) : T_xX → F`. -/
def linChart (f : X → Y) {x : PX.Level 1} (hx : PX.levelVal 1 x ∈ c.φ.source) :
    PX.tangentFiber x →ₗ[ℝ] c.F 0 :=
  ((scDeriv c.U (c.principal f ∘ r c.R) (levelLift c.φ 1 (PX.levelVal 1 x)) :
      c.φ.model.E 0 →L[ℝ] c.F 0) : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ∘ₗ
    (tangentFiberModel c.isChart hx).subtype ∘ₗ
      (tangentFiberLinearEquiv c.isChart hx).toLinearMap

lemma linChart_apply (f : X → Y) {x : PX.Level 1} (hx : PX.levelVal 1 x ∈ c.φ.source)
    (α : PX.tangentFiber x) :
    c.linChart f hx α = scDeriv c.U (c.principal f ∘ r c.R) (levelLift c.φ 1 (PX.levelVal 1 x))
      (tangentFiberEquiv c.isChart hx α : c.φ.model.E 0) := rfl

end StrongBundleChart

end FiberLin

section Intrinsic

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

lemma StrongBundle.isSc1_principal_comp_r (hf : B.IsScSmoothSection f)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) : IsSc1 c.U (c.principal f ∘ r c.R) := by
  have h1 := (hf.isScSmoothRetractMap hc).comp_isScSmooth
    (c.isRetraction.baseRetraction c.relOpen) c.base_retract
  exact ((h1.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl).isSc1

/-- At a zero, the values of the chart linearization lie in the fibre `Φ_x(Y_x)`. -/
theorem StrongBundleChart.linChart_mem (hf : B.IsScSmoothSection f)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) {x : PX.Level 1}
    (hx : PX.levelVal 1 x ∈ c.φ.source) (h0 : IsZeroAt P f (PX.levelVal 1 x))
    (α : PX.tangentFiber x) : c.linChart f hx α ∈ LinearMap.range (c.fiberLin hx) := by
  have ha : c.φ.model.E.toBase 1 (levelLift c.φ 1 (PX.levelVal 1 x)) = c.φ (PX.levelVal 1 x) :=
    PX.toBase_levelLift c.isChart hx (levelVal_mem x)
  have hyO : c.φ (PX.levelVal 1 x) ∈ c.φ.model.O := c.φ.mapsTo_model _ hx
  have hzO : c.φ.model.E.toBase 1 (levelLift c.φ 1 (PX.levelVal 1 x)) ∈ r c.R '' c.U := by
    rw [c.r_image, ha]; exact hyO
  have hρ := rho_scDeriv_comp_r c.relOpen c.isRetraction (StrongBundle.isSc1_principal_comp_r hf hc)
    (fun x hx => c.principal_mem_K hf.1 (c.r_image ▸ hx)) hzO
    (by rw [ha]; exact (c.isZeroAt_iff hf.1 hx).1 h0)
    (tangentFiberEquiv c.isChart hx α : c.φ.model.E 0)
  rw [ρCLM_apply] at hρ
  apply c.mem_range_fiberLin hx
  have hK := c.mem_K_ρ hyO (c.linChart f hx α)
  rw [StrongBundleChart.linChart_apply, ← ha, hρ] at hK
  rw [StrongBundleChart.linChart_apply, ← ha]
  exact hK

/-- **The linearization `f'(x) : T_xX → Y_x` of a section at a zero** (2021 §3.1, before
Definition 3.1.4), read through a strong bundle chart `c` around `x`:
`f'(x) = Φ_x⁻¹ ∘ D(f̂ ∘ r)(φ(x)) ∘ Tφ`.  It does not depend on `c`
(`StrongBundle.linIntr_chart_independent`). -/
def StrongBundle.linIntr (hf : B.IsScSmoothSection f) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {x : PX.Level 1} (hx : PX.levelVal 1 x ∈ c.φ.source)
    (h0 : IsZeroAt P f (PX.levelVal 1 x)) : PX.tangentFiber x →ₗ[ℝ] P ⁻¹' {PX.levelVal 1 x} :=
  (LinearEquiv.ofInjective (c.fiberLin hx) (c.fiberLin_injective hx)).symm.toLinearMap ∘ₗ
    (c.linChart f hx).codRestrict _ (c.linChart_mem hf hc hx h0)

theorem StrongBundle.fiberLin_linIntr (hf : B.IsScSmoothSection f) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {x : PX.Level 1} (hx : PX.levelVal 1 x ∈ c.φ.source)
    (h0 : IsZeroAt P f (PX.levelVal 1 x)) (α : PX.tangentFiber x) :
    c.fiberLin hx (B.linIntr hf hc hx h0 α) = c.linChart f hx α := by
  set e := LinearEquiv.ofInjective (c.fiberLin hx) (c.fiberLin_injective hx)
  have h := congrArg Subtype.val (e.apply_symm_apply
    ((c.linChart f hx).codRestrict _ (c.linChart_mem hf hc hx h0) α))
  rw [LinearEquiv.ofInjective_apply] at h
  exact h

/-- **The chart independence of `f'(x)`**: the linearizations through two strong bundle charts of
`B` around a zero `x ∈ X₁` agree. -/
theorem StrongBundle.linIntr_chart_independent (hf : B.IsScSmoothSection f)
    {c c' : StrongBundleChart PX P} (hc : B.IsChart c) (hc' : B.IsChart c') {x : PX.Level 1}
    (hx : PX.levelVal 1 x ∈ c.φ.source) (hx' : PX.levelVal 1 x ∈ c'.φ.source)
    (h0 : IsZeroAt P f (PX.levelVal 1 x)) :
    B.linIntr hf hc hx h0 = B.linIntr hf hc' hx' h0 := by
  set y := PX.levelVal 1 x with hy
  set a := levelLift c.φ 1 y with hadef
  set a' := levelLift c'.φ 1 y with ha'def
  have ha : c.φ.model.E.toBase 1 a = c.φ y := PX.toBase_levelLift c.isChart hx (levelVal_mem x)
  have ha' : c'.φ.model.E.toBase 1 a' = c'.φ y :=
    PX.toBase_levelLift c'.isChart hx' (levelVal_mem x)
  have hyO : c.φ y ∈ c.φ.model.O := c.φ.mapsTo_model _ hx
  have hzO : c.φ.model.E.toBase 1 a ∈ r c.R '' c.U := by rw [c.r_image, ha]; exact hyO
  have hzU : c.φ.model.E.toBase 1 a ∈ c.U := mem_U_of_mem_O c.isRetraction hzO
  have hzOO : c.φ.model.E.toBase 1 a ∈ c.φ.model.O := by rw [ha]; exact hyO
  have hzV' : c.φ.symm (c.φ.model.E.toBase 1 a) ∈ c'.φ.source := by
    rw [ha, c.φ.symm_apply_apply hx]; exact hx'
  obtain ⟨Rw, hRw, ⟨W, hWo, hW⟩, key⟩ := linAt_chart_change_key c c' hf.1
    (StrongBundle.IsChart.transition_isScSmoothRetractMap hc hc')
    (hf.isScSmoothRetractMap hc) (hf.isScSmoothRetractMap hc') hx hx' h0 ha ha' hzU hzOO hzV'
  -- `Tφ' = D(τ ∘ r_W)(φ(x)) ∘ Tφ` on `T_xX`
  have htrans : ∀ α : PX.tangentFiber x,
      (tangentFiberEquiv c'.isChart hx' α : c'.φ.model.E 0) =
        scDeriv Rw.U (c.φ.transition c'.φ ∘ Rw) a (tangentFiberEquiv c.isChart hx α) := by
    intro α
    rw [tangentFiberEquiv_eq_transition c.isChart hx c'.isChart hx' α]
    set v := tangentFiberEquiv c.isChart hx α
    change transitionCLM c.isChart hx c'.isChart hx' v = _
    have hspec := transitionCLM_spec c.isChart hx c'.isChart hx' v.2
    have hp : ((a, (v : c.φ.model.E 0)) : c.φ.model.E.tangent 0) ∈
        retractTangent c.φ.model.E c.φ.model.C (c.φ.overlap c'.φ) := by
      rw [hW, retractTangent_inter_isOpen c.φ.model.isScRetract hWo]
      refine ⟨(mem_tangentFiberModel c.isChart hx).1 v.2, ?_, mem_univ _⟩
      change c.φ.model.E.toBase 1 a ∈ W
      have : c.φ y ∈ c.φ.overlap c'.φ := c.φ.mem_overlap c'.φ hx hx'
      rw [hW] at this
      rw [ha]; exact this.2
    have happ := retractTangentMap_apply ((c.isChart.compatible c'.isChart (P := PX)).1) Rw hRw hp
    rw [happ] at hspec
    exact (congrArg Prod.snd hspec).symm
  refine LinearMap.ext fun α => c'.fiberLin_injective hx' ?_
  rw [StrongBundle.fiberLin_linIntr,
    ← c.transitionFiberCLM_fiberLin c' hx hx' ha hzOO hzV', StrongBundle.fiberLin_linIntr,
    StrongBundleChart.linChart_apply, StrongBundleChart.linChart_apply, htrans α]
  exact (key _).symm

end Intrinsic

end Polyfold
