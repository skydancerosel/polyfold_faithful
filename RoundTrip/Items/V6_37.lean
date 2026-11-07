import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_37

/-! Round trip for V6_37 (the stabilized section `F`, its slices `F_t`, `L_t = ker F_t'(φ(t), 0)`
and the product-chart linearization `F_t' = T ⊕ Φ` that (96) presupposes).  A is the conjunction of
the eleven theorems of the row (`sliceProj`, `sliceIncl`, `paramDerivAt` are definitions),
universes at `0`.

* `A_to_B` is not proved, and is believed false in B's generality (see the JSON).  What fails is
  one hypothesis: A's linearization formula `StrongBundle.scDeriv_paramSection_apply` needs the slice
  `f − s(·, t)` to be an sc-smooth section and the `sᵢ(·, t)` to be sc⁺-sections of `P` on ALL of
  `X`, while B only has `s`, `sᵢ` sc⁺ on an open neighbourhood of `[0, 1] × U` and reads the
  linearizations in EVERY chart point `p` of `φ(t)` (whose domain may leave that neighbourhood,
  where the project's `scDeriv`, hence `linAt`, is the junk value `0`).
  `B_concl_of_A` proves B's conclusion from A under exactly that extra (satisfiable) hypothesis,
  with every other hypothesis of B unused: the coordinate identification `e` comes from A's
  `ofProd_mem_tangent_iff` and the formula from A's `scDeriv_paramSection_apply` at `a = r₀ = 0`.
* `B_to_A` is not proved: B is (the global case of) one instance of one conjunct of A
  (`scDeriv_paramSection_apply` at the centre `a = 0` of a product chart centred at `r₀ = 0`); the
  other conjuncts (the formula at a general point, the tangent spaces and fibres of product charts,
  the double product chart over `ℝᵏ × ℝⁿ × X`, the slice kernel `J(ker(T ⊕ φ))`, `T ∈ Lin(f, x)`,
  the surjectivity of `T ⊕ φ`) are not in B. -/

namespace RoundTrip.V6_37
open Polyfold StrongRetr

/-- The project's statement (the eleven theorems of the row), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.PullbackChartData.ofProd_scDeriv_r_apply.{0, 0} ∧
  type_of% @Polyfold.PullbackChartData.ofProd_mem_tangent_iff.{0, 0} ∧
  type_of% @Polyfold.PullbackChartData.mem_K_ofProd_iff.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.scDeriv_ofProd_slice_apply.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.scDeriv_paramSection_apply.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.scDeriv_paramSection_ofProd_ofProd.{0, 0} ∧
  type_of% @Polyfold.linKer_inf_ker_sliceProj_eq_map.{0, 0} ∧
  type_of% @Polyfold.exists_sliceOps.{0, 0} ∧
  type_of% @Polyfold.mem_linSet_sectionAdd_pullbackSlice.{0, 0} ∧
  type_of% @Polyfold.surjective_coprod_of_isLinSurjAt.{0, 0} ∧
  type_of% @Polyfold.exists_sliceKernel.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.PullbackChartData.ofProd_scDeriv_r_apply.{0, 0},
    @Polyfold.PullbackChartData.ofProd_mem_tangent_iff.{0, 0},
    @Polyfold.PullbackChartData.mem_K_ofProd_iff.{0, 0},
    @Polyfold.StrongBundle.scDeriv_ofProd_slice_apply.{0, 0},
    @Polyfold.StrongBundle.scDeriv_paramSection_apply.{0, 0},
    @Polyfold.StrongBundle.scDeriv_paramSection_ofProd_ofProd.{0, 0},
    @Polyfold.linKer_inf_ker_sliceProj_eq_map.{0, 0},
    @Polyfold.exists_sliceOps.{0, 0},
    @Polyfold.mem_linSet_sectionAdd_pullbackSlice.{0, 0},
    @Polyfold.surjective_coprod_of_isLinSurjAt.{0, 0},
    @Polyfold.exists_sliceKernel.{0, 0}⟩

/-- **B's conclusion from A, for globally sc-smooth slices.**  At a chart point `p` of `x` and the
product chart built from it, if the slice `f − s(·, t)` is an sc-smooth section and the slices
`sᵢ(·, t)` are sc⁺-sections of `P` (A's hypotheses of `scDeriv_paramSection_apply`; B has them only
near `U`), then B's coordinate identification and formula `F_t'(w) = T (e w).2 + Φ (e w).1` hold.
Only A is used (its conjuncts `ofProd_mem_tangent_iff` and `scDeriv_paramSection_apply`). -/
theorem B_concl_of_A (hA : A) {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace ↥(pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace ↥W]
    [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace
      ↥(pullbackSpace (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X))
        (Subtype.val : W → (Fin 1 → ℝ) × X))]
    {Bd : StrongBundle PX P} {f : X → Y} (hf : IsSection P f) {s : Sec1 P}
    (hs : IsSection (pullbackProj P Prod.snd) s) {k : ℕ} {σ : Fin k → Sec1 P}
    (hσ : ∀ i, IsSection (pullbackProj P Prod.snd) (σ i)) (t : Fin 1 → ℝ) {x : X}
    (p : ChartPoint Bd x) (q₀ : ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X)))
    (hg : Bd.IsScSmoothSection (sectionDiff P f (pullbackSlice s t)))
    (hsi : ∀ i, Bd.IsScPlusSection (pullbackSlice (σ i) t)) :
    let T : ↥p.T →L[ℝ] p.c.F.lvl 0 :=
      linAt p.c.U p.c.R (p.c.principal (sectionDiff P f (pullbackSlice s t))) p.z
    let Φ : (Fin k → ℝ) →L[ℝ] p.c.F.lvl 0 :=
      p.K.subtypeL ∘L p.stabPhi (fun i => pullbackSlice (σ i) t)
        (fun i => isSection_slice (σ i) (hσ i) t)
    let c' := prodChart p k q₀
    let Lt : ↥(TProd p k q₀) →L[ℝ] p.c.F.lvl 0 :=
      linAt c'.U c'.R (c'.principal (Ft f hf s hs σ hσ t)) (zProd p k q₀)
    ∃ e : ↥(TProd p k q₀) ≃L[ℝ] (Fin k → ℝ) × ↥p.T,
      (∀ w : ↥(TProd p k q₀),
        (e w).1 = Prod.fst (α := Fin k → ℝ) (β := p.c.φ.model.E.lvl 0)
          (w : c'.φ.model.E.lvl 0) ∧
        ((e w).2 : p.c.φ.model.E.lvl 0) = Prod.snd (α := Fin k → ℝ)
          (β := p.c.φ.model.E.lvl 0) (w : c'.φ.model.E.lvl 0)) ∧
      ∀ w : ↥(TProd p k q₀), Lt w = T (e w).2 + Φ (e w).1 := by
  intro T Φ c' Lt
  have hu : p.c.φ.model.E.toBase 1 p.z ∈ p.c.U := p.mem_U
  -- the tangent space of the product chart (A: `ofProd_mem_tangent_iff`)
  have htan : ∀ w : (Fin k → ℝ) × p.c.φ.model.E.lvl 0, w ∈ TProd p k q₀ ↔ w.2 ∈ p.T :=
    fun w => hA.2.1 p.c 0 q₀ 0 hu w
  let E0 := p.c.φ.model.E.lvl 0
  let fwd : ↥(TProd p k q₀) →L[ℝ] (Fin k → ℝ) × ↥p.T :=
    ((ContinuousLinearMap.fst ℝ (Fin k → ℝ) E0).comp (TProd p k q₀).subtypeL).prod
      (((ContinuousLinearMap.snd ℝ (Fin k → ℝ) E0).comp (TProd p k q₀).subtypeL).codRestrict
        p.T fun w => (htan w.1).1 w.2)
  let bwd : (Fin k → ℝ) × ↥p.T →L[ℝ] ↥(TProd p k q₀) :=
    ((ContinuousLinearMap.fst ℝ (Fin k → ℝ) ↥p.T).prod
      (p.T.subtypeL.comp (ContinuousLinearMap.snd ℝ (Fin k → ℝ) ↥p.T))).codRestrict
      (TProd p k q₀) fun v => (htan _).2 v.2.2
  let e : ↥(TProd p k q₀) ≃L[ℝ] (Fin k → ℝ) × ↥p.T :=
    ContinuousLinearEquiv.equivOfInverse fwd bwd (fun w => rfl) (fun v => rfl)
  refine ⟨e, fun w => ⟨rfl, rfl⟩, fun w => ?_⟩
  -- the formula (A: `scDeriv_paramSection_apply` at `a = r₀ = 0`)
  have h := hA.2.2.2.2.1 hg hsi p.isChart 0 q₀ 0 hu (w.1 : (Fin k → ℝ) × E0)
  have hfun : (fun u => p.c.principal (sectionDiff P f (pullbackSlice s t)) u +
      ∑ i, ((0 : Fin k → ℝ) + 0) i • p.c.principal (pullbackSlice (σ i) t) u) =
      p.c.principal (sectionDiff P f (pullbackSlice s t)) := funext fun u => by simp
  rw [hfun] at h
  have hzO : p.c.φ.model.E.toBase 1 p.z ∈ r p.c.R '' p.c.U := p.mem_O
  have hr : r p.c.R (p.c.φ.model.E.toBase 1 p.z) = p.c.φ x := by
    rw [r_eq_self p.c.isRetraction hzO, p.toBase_z]
  rw [hr] at h
  refine h.trans ?_
  change _ = scDeriv p.c.U (p.c.principal (sectionDiff P f (pullbackSlice s t)) ∘ r p.c.R) p.z
      (w.1 : (Fin k → ℝ) × E0).2 + ((p.stabPhi (fun i => pullbackSlice (σ i) t)
        (fun i => isSection_slice (σ i) (hσ i) t) (w.1 : (Fin k → ℝ) × E0).1 : ↥p.K) : p.c.F.lvl 0)
  exact congrArg _ (p.coe_stabPhi _ _ _).symm

/-! ### Why B's generality fails: the junk linearization -/

/-- The project's `linAt` is `0` when `f̂ ∘ r` is not sc¹ on the whole chart domain `U`
(`scDeriv` is a choice, junk `0` otherwise). -/
theorem linAt_eq_zero_of_not_isSc1 {E F : ScBanach} {U : Set (E 0)}
    {R : E 0 × F 0 → E 0 × F 0} {fb : E 0 → F 0} (z : E 1) (h : ¬ IsSc1 U (fb ∘ r R)) :
    linAt U R fb z = 0 := by
  ext v
  show scDeriv U (fb ∘ r R) z v = 0
  unfold scDeriv
  rw [dif_neg h]
  rfl

/-- **B's conclusion in a chart point where `F̂_t ∘ r` is not sc¹ forces `Φ = 0`**, i.e.
`sᵢ(φ(t), t) = 0` read in the chart for every `i`.  B's hypotheses make `s`, `sᵢ` sc⁺ only near
`[0, 1] × U`, while B quantifies over every chart point `p` of `φ(t)`; in a chart whose domain
leaves that neighbourhood (where `s` is arbitrary) `F̂_t ∘ r` need not be sc¹, so B is believed
false in its generality. -/
theorem B_concl_forces_Phi_zero {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace ↥(pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace ↥W]
    [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace
      ↥(pullbackSpace (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X))
        (Subtype.val : W → (Fin 1 → ℝ) × X))]
    {Bd : StrongBundle PX P} {f : X → Y} (hf : IsSection P f) {s : Sec1 P}
    (hs : IsSection (pullbackProj P Prod.snd) s) {k : ℕ} {σ : Fin k → Sec1 P}
    (hσ : ∀ i, IsSection (pullbackProj P Prod.snd) (σ i)) (t : Fin 1 → ℝ) {x : X}
    (p : ChartPoint Bd x) (q₀ : ↥(pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X)))
    (hjunk : ¬ IsSc1 (prodChart p k q₀).U
      ((prodChart p k q₀).principal (Ft f hf s hs σ hσ t) ∘ r (prodChart p k q₀).R))
    (h : ∃ e : ↥(TProd p k q₀) ≃L[ℝ] (Fin k → ℝ) × ↥p.T,
      ∀ w : ↥(TProd p k q₀),
        linAt (prodChart p k q₀).U (prodChart p k q₀).R
            ((prodChart p k q₀).principal (Ft f hf s hs σ hσ t)) (zProd p k q₀) w =
          linAt p.c.U p.c.R (p.c.principal (sectionDiff P f (pullbackSlice s t))) p.z (e w).2 +
            (p.K.subtypeL ∘L p.stabPhi (fun i => pullbackSlice (σ i) t)
              (fun i => isSection_slice (σ i) (hσ i) t)) (e w).1) :
    ∀ μ : Fin k → ℝ, ((p.stabPhi (fun i => pullbackSlice (σ i) t)
      (fun i => isSection_slice (σ i) (hσ i) t) μ : ↥p.K) : p.c.F.lvl 0) = 0 := by
  obtain ⟨e, he⟩ := h
  intro μ
  have h1 := he (e.symm (μ, 0))
  rw [linAt_eq_zero_of_not_isSc1 _ hjunk, ContinuousLinearEquiv.apply_symm_apply] at h1
  have h2 := h1.symm
  simp at h2
  exact h2

#rt_check RoundTrip.V6_37.B_concl_of_A [Polyfold.PullbackChartData.ofProd_scDeriv_r_apply,
  Polyfold.PullbackChartData.ofProd_mem_tangent_iff, Polyfold.PullbackChartData.mem_K_ofProd_iff,
  Polyfold.StrongBundle.scDeriv_ofProd_slice_apply, Polyfold.StrongBundle.scDeriv_paramSection_apply,
  Polyfold.StrongBundle.scDeriv_paramSection_ofProd_ofProd,
  Polyfold.linKer_inf_ker_sliceProj_eq_map, Polyfold.exists_sliceOps,
  Polyfold.mem_linSet_sectionAdd_pullbackSlice, Polyfold.surjective_coprod_of_isLinSurjAt,
  Polyfold.exists_sliceKernel]

end RoundTrip.V6_37
