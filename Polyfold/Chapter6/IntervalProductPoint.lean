import Polyfold.Chapter6.SectionOrientationProdFirst
import Polyfold.Chapter6.CubeStabKernels

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19** (preprint Remark 6.42, p. 230) over the M-polyfold with boundary `[0, 1] × X`.

# The product chart points of `[0, 1] × X`

## The text, paraphrased

For an oriented sc-Fredholm section `(f, o)` of `P : Y → X` and an sc⁺-section `s` of the
pull-back of `Y` to `X × [0, 1]`, the section `f̂(x, t) = f(x) + s(x, t)` has a natural
orientation made from `o` and the standard orientation of `[0, 1]`: `L̃(a, b) = La` on
`T_{(x, t)}(X × [0, 1])` is oriented by `e ∧ h` when `L` is oriented by `h`.

## What is formalized

`[0, 1] × X` is the M-polyfold `(cubePolyfold 1).prod PX` (the parameter first), with the
boundary `{0, 1} × X`; its charts are the products of the two corner charts `t ↦ t` on `[0, 1)`
and `t ↦ 1 − t` on `(0, 1]` of `[0, 1]` (`UnitCube.chart b`) with the charts of `X`.

* `ivBundle B`: the pull-back of `P` to `[0, 1] × X`; `ivChart b c q₀`: the product chart.
* `ivSign b`: the sign of the chart `b` of `[0, 1]` (`+1` for `t ↦ t`, `−1` for `t ↦ 1 − t`).
* `ChartPoint.ivPt`: the product chart point at `(t, x)`, `t` in the domain of the chart `b`,
  boundary points included; `mem_ivPt_T_iff`, `mem_ivPt_K_iff`: `T_{(t, x)} = ℝ × T_xX` (the
  tangent space at a boundary point is the full space) and the fibre is that of `x`.
* `ivT`: `A(σ, v) = (v, ± σ)`, the sign that of the chart, so that `e = (0, 1)` is the standard
  direction of `[0, 1]` in both charts; `ivK`, `ivLin` (`L̂(σ, v) = Lv`).
* `isScPlusSection_cubeLift`: the `t`-constant lift of an sc⁺-section is sc⁺ over `[0, 1] × X`.
* `linAt_ivPt_cubeLift`: the linearization of a `t`-constant lift is `(σ, v) ↦ g'(x) v`.
* `ivLin_mem_linSet`: **`L̂ ∈ Lin(f̂, (t, x))`** for `L ∈ Lin(f, x)`, `f̂ = f̃ + S` with `S` an
  sc⁺-section over `[0, 1] × X`.
-/

open Module TensorProduct Bundle Topology Set Filter

noncomputable section

namespace Polyfold

open StrongRetr UnitCube

universe u v

section IvChart

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))]

variable (B) in
/-- The pull-back `π*P` of `P` to `[0, 1] × X`. -/
abbrev ivBundle : StrongBundle ((cubePolyfold 1).prod PX)
    (pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X)) :=
  B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX)

/-- The identity retraction of the model `[0, 1)` of the charts of `[0, 1]`. -/
def ivRetr (b : Fin 1 → Bool) : ScRetraction (chart b).model.E (chart b).model.C :=
  ScRetraction.id (isRelOpen_modelO 1)

lemma ivRetr_retract (b : Fin 1 → Bool) : (ivRetr b).retract = (chart b).model.O := by
  change _root_.id '' modelO 1 = _
  rw [image_id]
  rfl

/-- The data of the product chart `χ_b × φ_c` of `[0, 1] × X`. -/
abbrev ivData (b : Fin 1 → Bool) (c : StrongBundleChart PX P) :
    PullbackChartData PX P ((cubePolyfold 1).prod PX) Prod.snd :=
  PullbackChartData.ofProdChart (isChart_chart b) (ivRetr b) (ivRetr_retract b) c

/-- **The product chart `χ_b × φ_c`** of `π*P` over `[0, 1] × X`, for the chart `χ_b` of
`[0, 1]` (`t ↦ t` on `[0, 1)` for `b = true`, `t ↦ 1 − t` on `(0, 1]` for `b = false`). -/
abbrev ivChart (b : Fin 1 → Bool) (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)) :
    StrongBundleChart ((cubePolyfold 1).prod PX)
      (pullbackProj P (Prod.snd : (Fin 1 → unitInterval) × X → X)) :=
  (ivData b c).toChart q₀

theorem isChart_ivChart (b : Fin 1 → Bool) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)) :
    (ivBundle B).IsChart (ivChart b c q₀) :=
  (ivData b c).isChart_toChart B _ hc q₀

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] in
theorem mem_ivChart_source {b : Fin 1 → Bool} {c : StrongBundleChart PX P}
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)) {x : X}
    (hx : x ∈ c.φ.source) {t : Fin 1 → unitInterval} (ht : t ∈ (chart b).source) :
    ((t, x) : (Fin 1 → unitInterval) × X) ∈ (ivChart b c q₀).φ.source :=
  ⟨ht, hx⟩

/-- **The sign of the chart `χ_b` of `[0, 1]`**: `+1` for `t ↦ t`, `−1` for `t ↦ 1 − t`. -/
def ivSign (b : Fin 1 → Bool) : ℝ := if b 0 then 1 else -1

lemma ivSign_mul_self (b : Fin 1 → Bool) : ivSign b * ivSign b = 1 := by
  unfold ivSign; split <;> norm_num

lemma ivSign_ne_zero (b : Fin 1 → Bool) : ivSign b ≠ 0 := fun h => by
  have := ivSign_mul_self b
  rw [h] at this
  norm_num at this

/-- The image of a point of the domain of `χ_b` lies in the model `[0, 1)`. -/
lemma chart_mem_modelO {b : Fin 1 → Bool} {t : Fin 1 → unitInterval}
    (ht : t ∈ (chart b).source) : (chart b t : Fin 1 → ℝ) ∈ modelO 1 :=
  (chart b).mapsTo_model t ht

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] in
/-- `D(1 × r)(a, u) = 1 × Dr(u)` in the product chart, at every level-`1` point `(a, u)`,
`a ∈ [0, 1)` (the boundary point `a = 0` included). -/
lemma ivChart_scDeriv_r_apply (b : Fin 1 → Bool) (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)) {a : Fin 1 → ℝ}
    (ha : a ∈ modelO 1) {u : c.φ.model.E 1} (hu : c.φ.model.E.toBase 1 u ∈ c.U)
    (v : (Fin 1 → ℝ) × c.φ.model.E 0) :
    scDeriv (ivChart b c q₀).U (r (ivChart b c q₀).R)
      ((a, u) : (ivChart b c q₀).φ.model.E 1) v = (v.1, scDeriv c.U (r c.R) u v.2) := by
  have hrel := isRelOpen_modelO 1
  have ha1 : (ScBanach.const (Fin 1 → ℝ)).toBase 1 a ∈ modelO 1 := by
    rw [ScBanach.const_toBase]; exact ha
  have h0' : ((a, u) : (rnSc 1 |>.prod c.φ.model.E) 1) ∈
      (rnSc 1 |>.prod c.φ.model.E).lvlSet (modelO 1 ×ˢ c.U) 1 := by
    rw [lvlSet_prod]; exact ⟨ha1, hu⟩
  have h1 := scDeriv_prodMap (F := rnSc 1) (F' := c.φ.model.E) hrel c.relOpen
    (isScSmooth_id hrel.isScDomain)
    (c.isRetraction.baseRetraction c.relOpen).isScSmooth h0'
  have e := congrArg (fun L : (rnSc 1 |>.prod c.φ.model.E) 0 →L[ℝ]
    (rnSc 1 |>.prod c.φ.model.E) 0 => L v) h1
  have h2 : scDeriv (E := rnSc 1) (F := rnSc 1) (modelO 1) id (a : (rnSc 1) 1) =
      ContinuousLinearMap.id ℝ (Fin 1 → ℝ) :=
    IsSc1.scDeriv_eqOn (isSc1With_id _) (hrel.isScDomain.uniqueDiffWithinAt 1) ha1
  refine e.trans (Prod.ext ?_ rfl)
  exact congrArg (fun L : (rnSc 1) 0 →L[ℝ] (rnSc 1) 0 => L v.1) h2

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] in
/-- The tangent space of the product chart at a level-`1` point `(a, u)`:
`T_{(a, u)}([0, 1) × O) = ℝ × T_uO`, also at `a = 0`. -/
lemma ivChart_mem_tangent_iff (b : Fin 1 → Bool) (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)) {a : Fin 1 → ℝ}
    (ha : a ∈ modelO 1) {u : c.φ.model.E 1} (hu : c.φ.model.E.toBase 1 u ∈ c.U)
    (w : (Fin 1 → ℝ) × c.φ.model.E 0) :
    w ∈ rangeS (scDeriv (ivChart b c q₀).U (r (ivChart b c q₀).R)
      ((a, u) : (ivChart b c q₀).φ.model.E 1)) ↔
      w.2 ∈ rangeS (scDeriv c.U (r c.R) u) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.2, congrArg Prod.snd ((ivChart_scDeriv_r_apply b c q₀ ha hu y).symm.trans hy)⟩
  · rintro ⟨y, hy⟩
    exact ⟨(w.1, y), (ivChart_scDeriv_r_apply b c q₀ ha hu (w.1, y)).trans (Prod.ext rfl hy)⟩

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] in
/-- **The fibres of the product chart** over `(a, u)` are the fibres of `c` over `u`. -/
lemma mem_K_ivChart_iff (b : Fin 1 → Bool) (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    {w : (Fin 1 → ℝ) × c.φ.model.E 0} (hw1 : w.1 ∈ modelO 1) (hw : w.2 ∈ c.φ.model.O)
    (k : c.F 0) :
    ((w, k) : (ivChart b c q₀).φ.model.E 0 × c.F 0) ∈ (ivChart b c q₀).K ↔ (w.2, k) ∈ c.K := by
  change _ ∈ pullbackRetraction (ivData b c).c.R (ivData b c).RZ (ivData b c).g ''
    ((ivData b c).RZ.U ×ˢ univ) ↔ _
  rw [(ivData b c).image_eq_Kg]
  have hg : (ivData b c).g w = w.2 := by
    change c.φ (c.φ.symm w.2) = w.2
    exact c.φ.apply_symm_apply hw
  have hR : w ∈ (ivData b c).RZ.retract := by
    rw [(ivData b c).RZ_retract]
    exact ⟨hw1, hw⟩
  change w ∈ (ivData b c).RZ.retract ∧ ((ivData b c).g w, k) ∈ c.K ↔ _
  rw [hg]
  exact ⟨fun h => h.2, fun h => ⟨hR, h⟩⟩

end IvChart

/-! ### The product chart point -/

section IvPoint

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))]

namespace ChartPoint

variable {x : X} (p : ChartPoint B x)

/-- **The product chart point** at `(t, x) ∈ [0, 1] × X`, for `t` in the domain of the chart
`χ_b` of `[0, 1]` (`t = 0` for `b = true` and `t = 1` for `b = false` included): the product
chart `χ_b × φ` over the chart `c` of `p`, with the level-`1` point `(χ_b(t), z)`. -/
def ivPt (b : Fin 1 → Bool) {t : Fin 1 → unitInterval} (ht : t ∈ (chart b).source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)) :
    ChartPoint (ivBundle B) (t, x) where
  c := ivChart b p.c q₀
  isChart := isChart_ivChart b p.isChart q₀
  mem_source := ⟨ht, p.mem_source⟩
  z := ((chart b t : Fin 1 → ℝ), p.z)
  toBase_z := by
    change ((rnSc 1).prod p.c.φ.model.E).toBase 1 ((chart b t : Fin 1 → ℝ), p.z) =
      (((chart b t : Fin 1 → ℝ), p.c.φ x) : (Fin 1 → ℝ) × p.c.φ.model.E 0)
    rw [ScBanach.prod_toBase, ScBanach.const_toBase, p.toBase_z]

variable (b : Fin 1 → Bool) {t : Fin 1 → unitInterval} (ht : t ∈ (chart b).source)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))

/-- **`T_{(t, x)}([0, 1] × X) = ℝ × T_xX`** in the product chart, at every `t ∈ [0, 1]`. -/
theorem mem_ivPt_T_iff (w : (Fin 1 → ℝ) × p.c.φ.model.E 0) :
    w ∈ (p.ivPt b ht q₀).T ↔ w.2 ∈ p.T :=
  ivChart_mem_tangent_iff b p.c q₀ (chart_mem_modelO ht) p.mem_U w

/-- The base point of the product chart point. -/
theorem ivPt_toBase :
    (p.ivPt b ht q₀).c.φ.model.E.toBase 1 (p.ivPt b ht q₀).z =
      (((chart b t : Fin 1 → ℝ), p.c.φ.model.E.toBase 1 p.z) :
        (Fin 1 → ℝ) × p.c.φ.model.E 0) := by
  change ((rnSc 1).prod p.c.φ.model.E).toBase 1 ((chart b t : Fin 1 → ℝ), p.z) = _
  rw [ScBanach.prod_toBase, ScBanach.const_toBase]

/-- **`Ŷ_{(t, x)} = Y_x`** in the product chart. -/
theorem mem_ivPt_K_iff (k : p.c.F 0) : k ∈ (p.ivPt b ht q₀).K ↔ k ∈ p.K := by
  have h1 := mem_rangeS_ρCLM_iff (p.ivPt b ht q₀).c.isRetraction (p.ivPt b ht q₀).mem_O
    (p.ivPt b ht q₀).mem_U (k := k)
  have h2 := mem_rangeS_ρCLM_iff p.c.isRetraction p.mem_O p.mem_U (k := k)
  refine h1.trans (Iff.trans ?_ h2.symm)
  rw [p.ivPt_toBase b ht q₀]
  exact mem_K_ivChart_iff b p.c q₀
    (w := ((chart b t : Fin 1 → ℝ), p.c.φ.model.E.toBase 1 p.z)) (chart_mem_modelO ht)
    (p.c.r_image ▸ p.mem_O) k

/-- **`A : T_{(t, z)} → T_zO × ℝ¹`**, `(σ, v) ↦ (v, ± σ)`, the sign that of the chart `χ_b`:
the vector `(0, 1)` of `T_zO × ℝ¹` is the standard direction of `[0, 1]` (the direction of
increasing `t`), in the chart `t ↦ t` and in the chart `t ↦ 1 − t`. -/
def ivT : ↥(p.ivPt b ht q₀).T ≃L[ℝ] ↥p.T × (Fin 1 → ℝ) :=
  ContinuousLinearEquiv.equivOfInverse
    ((((ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) (p.c.φ.model.E 0)).comp
      (p.ivPt b ht q₀).T.subtypeL).codRestrict p.T fun w =>
        (p.mem_ivPt_T_iff b ht q₀ w.1).1 w.2).prod
      (ivSign b • (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) (p.c.φ.model.E 0)).comp
        (p.ivPt b ht q₀).T.subtypeL))
    ((((ContinuousLinearMap.inr ℝ (Fin 1 → ℝ) (p.c.φ.model.E 0)).comp
      (p.T.subtypeL.comp (ContinuousLinearMap.fst ℝ ↥p.T (Fin 1 → ℝ)))) +
      ivSign b • ((ContinuousLinearMap.inl ℝ (Fin 1 → ℝ) (p.c.φ.model.E 0)).comp
        (ContinuousLinearMap.snd ℝ ↥p.T (Fin 1 → ℝ)))).codRestrict (p.ivPt b ht q₀).T fun w =>
          (p.mem_ivPt_T_iff b ht q₀ _).2 (by simp))
    (fun w => Subtype.ext (Prod.ext (by
      change ((0 : Fin 1 → ℝ) + ivSign b •
        (ivSign b • Prod.fst (α := Fin 1 → ℝ) (β := p.c.φ.model.E 0) w.1) : Fin 1 → ℝ) =
          Prod.fst (α := Fin 1 → ℝ) (β := p.c.φ.model.E 0) w.1
      rw [zero_add, smul_smul, ivSign_mul_self, one_smul]) (by
      change (Prod.snd (α := Fin 1 → ℝ) (β := p.c.φ.model.E 0) w.1 +
        ivSign b • (0 : p.c.φ.model.E 0) : p.c.φ.model.E 0) =
          Prod.snd (α := Fin 1 → ℝ) (β := p.c.φ.model.E 0) w.1
      rw [smul_zero, add_zero])))
    (fun y => Prod.ext (Subtype.ext (by
      change ((y.1 : p.c.φ.model.E 0) + ivSign b • (0 : p.c.φ.model.E 0) : p.c.φ.model.E 0) =
        (y.1 : p.c.φ.model.E 0)
      rw [smul_zero, add_zero])) (by
      change (ivSign b • ((0 : Fin 1 → ℝ) + ivSign b • y.2) : Fin 1 → ℝ) = y.2
      rw [zero_add, smul_smul, ivSign_mul_self, one_smul]))

/-- `A(σ, v) = (v, ± σ)`: the first component. -/
@[simp] theorem coe_ivT_fst (w : ↥(p.ivPt b ht q₀).T) :
    ((p.ivT b ht q₀ w).1 : p.c.φ.model.E 0) = (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2 := rfl

/-- `A(σ, v) = (v, ± σ)`: the second component. -/
@[simp] theorem ivT_snd (w : ↥(p.ivPt b ht q₀).T) :
    (p.ivT b ht q₀ w).2 = ivSign b • (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 := rfl

/-- `A⁻¹(v, σ) = (± σ, v)`. -/
theorem coe_ivT_symm (y : ↥p.T × (Fin 1 → ℝ)) :
    ((((p.ivT b ht q₀).symm y : ↥(p.ivPt b ht q₀).T).1 : (p.ivPt b ht q₀).c.φ.model.E 0) :
        (Fin 1 → ℝ) × p.c.φ.model.E 0) =
      (ivSign b • y.2, (y.1 : p.c.φ.model.E 0)) := by
  refine Prod.ext ?_ ?_
  · change ((0 : Fin 1 → ℝ) + ivSign b • y.2 : Fin 1 → ℝ) = _
    rw [zero_add]
  · change ((y.1 : p.c.φ.model.E 0) + ivSign b • (0 : p.c.φ.model.E 0) : p.c.φ.model.E 0) = _
    rw [smul_zero, add_zero]

/-- **`Γ : Ŷ_{(t, x)} → Y_x`**: the identity of `K_z`. -/
def ivK : ↥(p.ivPt b ht q₀).K ≃L[ℝ] ↥p.K :=
  ContinuousLinearEquiv.equivOfInverse
    ((p.ivPt b ht q₀).K.subtypeL.codRestrict p.K fun k => (p.mem_ivPt_K_iff b ht q₀ k.1).1 k.2)
    (p.K.subtypeL.codRestrict (p.ivPt b ht q₀).K fun k => (p.mem_ivPt_K_iff b ht q₀ k.1).2 k.2)
    (fun _ => rfl) (fun _ => rfl)

/-- `Γ` is the identity of `K_z`. -/
@[simp] theorem coe_ivK (k : ↥(p.ivPt b ht q₀).K) :
    ((p.ivK b ht q₀ k : ↥p.K) : p.c.F 0) = (k.1 : p.c.F 0) := rfl

/-- `Γ⁻¹` is the identity of `K_z`. -/
@[simp] theorem coe_ivK_symm (k : ↥p.K) :
    (((p.ivK b ht q₀).symm k : ↥(p.ivPt b ht q₀).K).1 : p.c.F 0) = (k : p.c.F 0) := rfl

/-- **The text's `L̃(a, b) = La` read in the product chart**: `L̂ = Γ⁻¹ (L ⊕ 0) A`, i.e.
`(σ, v) ↦ Lv`. -/
abbrev ivLin (L : ↥p.T →L[ℝ] ↥p.K) : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).K :=
  extConjOp (p.ivT b ht q₀) (p.ivK b ht q₀) L

/-- `L̂(σ, v) = Lv`. -/
theorem coe_ivLin_apply (L : ↥p.T →L[ℝ] ↥p.K) (w : ↥(p.ivPt b ht q₀).T) :
    ((p.ivLin b ht q₀ L w : ↥(p.ivPt b ht q₀).K).1 : p.c.F 0) =
      (L (p.ivT b ht q₀ w).1 : p.c.F 0) := by
  change (((p.ivK b ht q₀).symm (extOp L (p.ivT b ht q₀ w)) : ↥(p.ivPt b ht q₀).K).1 :
    p.c.F 0) = _
  rw [extOp_apply]
  rfl

/-- `L̃ ∘ A = Γ ∘ L̂`. -/
theorem ivLin_conj (L : ↥p.T →L[ℝ] ↥p.K) (w : ↥(p.ivPt b ht q₀).T) :
    extOp L (p.ivT b ht q₀ w) = p.ivK b ht q₀ (p.ivLin b ht q₀ L w) :=
  extConjOp_conj _ _ L w

/-- **The sc⁺-operators lift**: for an sc⁺-operator `a : T_zO → K_z`, `(σ, v) ↦ a(v)` is an
sc⁺-operator `T_{(t, z)} → K_z` at a smooth point. -/
theorem IsScPlusOp.ivPt (hx : x ∈ PX.smoothSet) {a : ↥p.T →L[ℝ] ↥p.K} (ha : p.IsScPlusOp a) :
    (p.ivPt b ht q₀).IsScPlusOp (((p.ivK b ht q₀).symm : ↥p.K →L[ℝ] ↥(p.ivPt b ht q₀).K) ∘L a ∘L
      ((ContinuousLinearMap.fst ℝ ↥p.T (Fin 1 → ℝ)) ∘L
        (p.ivT b ht q₀ : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥p.T × (Fin 1 → ℝ)))) := by
  obtain ⟨hT, hK, S, hS⟩ := ha
  have hx' : (t, x) ∈ ((cubePolyfold 1).prod PX).smoothSet := prod_cube_mem_smoothSet_iff.2 hx
  have hT' := (p.ivPt b ht q₀).isScSubspace_T hx'
  have hK' := (p.ivPt b ht q₀).isScSubspace_K hx'
  let aop : ScOperator ((p.ivPt b ht q₀).c.φ.model.E.ofSubspace hT')
      (p.c.φ.model.E.ofSubspace hT) :=
    (ScBanach.prodSndOp (rnSc 1) p.c.φ.model.E).restrict hT' hT
      (fun v hv => (p.mem_ivPt_T_iff b ht q₀ v).1 hv)
  let γop : ScOperator (p.c.F.ofSubspace hK) ((p.ivPt b ht q₀).c.F.ofSubspace hK') :=
    (ScOperator.id p.c.F).restrict hK hK' (fun k hk => (p.mem_ivPt_K_iff b ht q₀ k).2 hk)
  refine ⟨hT', hK', γop.shift.comp (S.comp aop), fun v => ?_⟩
  exact hS (aop 0 v)

/-- **The stabilization `φ̂ = Γ⁻¹ ∘ φ : ℝᵏ → Ŷ_{(t, x)}`** of the product chart point. -/
abbrev ivStab {k : ℕ} (φ : (Fin k → ℝ) →L[ℝ] ↥p.K) :
    (Fin k → ℝ) →L[ℝ] ↥(p.ivPt b ht q₀).K :=
  ((p.ivK b ht q₀).symm : ↥p.K →L[ℝ] ↥(p.ivPt b ht q₀).K) ∘L φ

theorem ivStab_conj {k : ℕ} (φ : (Fin k → ℝ) →L[ℝ] ↥p.K) (μ : Fin k → ℝ) :
    φ μ = p.ivK b ht q₀ (p.ivStab b ht q₀ φ μ) :=
  ((p.ivK b ht q₀).apply_symm_apply _).symm

/-- `L̂ ⊕ φ̂` is onto when `L ⊕ φ` is. -/
theorem surjective_coprod_ivLin {k : ℕ} {L : ↥p.T →L[ℝ] ↥p.K} {φ : (Fin k → ℝ) →L[ℝ] ↥p.K}
    (hφ : Function.Surjective (L.coprod φ)) :
    Function.Surjective ((p.ivLin b ht q₀ L).coprod (p.ivStab b ht q₀ φ)) := by
  intro y
  obtain ⟨w, hw⟩ := surjective_coprod_extOp hφ (p.ivK b ht q₀ y)
  refine ⟨((p.ivT b ht q₀).symm w.1, w.2), (p.ivK b ht q₀).injective ?_⟩
  rw [← coprod_conj (p.ivT b ht q₀) (p.ivK b ht q₀) (p.ivLin_conj b ht q₀ L)
    (p.ivStab_conj b ht q₀ φ)]
  simpa using hw

/-- `α(L̂) = α(L)`. -/
theorem stabSign_ivLin (L : ↥p.T →L[ℝ] ↥p.K) : stabSign (p.ivLin b ht q₀ L) = stabSign L := by
  have h1 : stabSign (extOp L) = stabSign (p.ivLin b ht q₀ L) :=
    stabSign_conj (p.ivT b ht q₀) (p.ivK b ht q₀) (p.ivLin_conj b ht q₀ L)
  rw [← h1, stabSign, stabSign, (extCoker L).finrank_eq]

end ChartPoint

end IvPoint

/-! ### Sections over `[0, 1]ⁿ × X` -/

section IvSections

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- A section of `pr₂*P` over `T × X` is determined by its slices. -/
theorem eq_of_prodSlice_eq {T : Type*} {S₁ S₂ : T × X → pullbackSpace P (Prod.snd : T × X → X)}
    (h₁ : IsSection (pullbackProj P Prod.snd) S₁) (h₂ : IsSection (pullbackProj P Prod.snd) S₂)
    (h : ∀ t, prodSlice S₁ t = prodSlice S₂ t) : S₁ = S₂ := by
  funext z
  exact Subtype.ext (Prod.ext ((h₁ z).trans (h₂ z).symm) (congrFun (h z.1) z.2))

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- `f̃ + s̃ = (f + s)~` for the `t`-constant lifts to `[0, 1]ⁿ × X`. -/
theorem sectionAdd_cubeLift {n : ℕ} {g s : X → Y} (hg : IsSection P g) (hs : IsSection P s) :
    sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := n) g hg) (cubeLift (n := n) s hs) =
      cubeLift (n := n) (sectionAdd P g s) (hg.sectionAdd hs) :=
  eq_of_prodSlice_eq ((isSection_pullbackLift _).sectionAdd (isSection_pullbackLift _))
    (isSection_pullbackLift _) fun t =>
      prodSlice_sectionAdd_pullbackLift hg (isSection_pullbackLift _) t

/-- **The `t`-constant lift of an sc⁺-section is an sc⁺-section** of `pr₂*P` over
`[0, 1]ⁿ × X`: in the product charts `χ_b × φ_c` its representative is that of `s` composed with
`(a, u) ↦ u`. -/
theorem isScPlusSection_cubeLift {n : ℕ}
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]
    {s : X → Y} (hs : B.IsScPlusSection s) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).IsScPlusSection
      (cubeLift (n := n) s hs.1) := by
  set S' := cubeLift (n := n) s hs.1 with hS'
  have hsec : IsSection (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X)) S' :=
    isSection_pullbackLift _
  refine StrongBundle.isScPlusSection_of_local hsec fun z => ?_
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem B z.2
  set b := corner z.1 with hb
  obtain ⟨Rb, hRb⟩ := (chart b).model.isScRetract
  set c' := (PullbackChartData.ofProdChart (isChart_chart b) Rb hRb c).toChart (S' z) with hc'
  have hmem' :
      c' ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).atlas.charts :=
    ⟨_, _, hc, rfl⟩
  obtain ⟨hrange, hsm⟩ := hs.2 c hc
  refine ⟨c', hmem', ⟨mem_chart_corner z.1, hxc⟩, fun w hw => hrange _ hw.2, ?_⟩
  have hO : IsScRetract c'.φ.model.E c'.φ.model.C c'.φ.model.O := c'.φ.model.isScRetract
  have hT : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O c.φ.model.E
      c.φ.model.C c.φ.model.O (ScBanach.prodSndOp (rnSc n) c.φ.model.E 0) :=
    (ScBanach.prodSndOp (rnSc n) c.φ.model.E).isScSmoothRetractMap hO fun p hp => hp.2
  have hcomp := hsm.comp hT c.φ.model.isScRetract
  refine ⟨fun w hw => ?_, fun R hR => ?_⟩
  · have hws := c'.φ.symm_mapsTo hw
    exact c'.liftOne_mem (c'.mem_source_of_proj (by rw [hsec]; exact hws)) (hrange _ hws.2)
  · have hU := R.isScDomain
    have h1 := (hcomp.comp_isScSmooth R hR).snd hU
    have h2 := R.isScSmooth.scPair hU h1
    refine h2.congr hU fun w hw => ?_
    have hRw : R w ∈ c'.φ.model.O := by rw [← hR]; exact R.apply_mem_retract hw
    change (R w, (StrongBundle.localRepOne c s
      (ScBanach.prodSndOp (rnSc n) c.φ.model.E 0 (R w))).2) = StrongBundle.localRepOne c' S' (R w)
    generalize R w = p at hRw ⊢
    obtain ⟨a, u⟩ := p
    have hu : u ∈ c.φ.model.O := hRw.2
    have ha : a ∈ (chart b).model.O := hRw.1
    set a' : Fin n → ℝ := a
    change ((a', u), Function.invFun (c.F.toBase 1) (c (s (c.φ.symm u))).2) =
      (((chart b ((chart b).symm a') : Fin n → ℝ), c.φ (c.φ.symm u)),
        Function.invFun (c.F.toBase 1) (c (s (c.φ.symm u))).2)
    rw [c.φ.apply_symm_apply hu, (chart b).apply_symm_apply ha]
    rfl

/-- **`Ŝ(τ, (t, x)) = S(τ, x)`**: a section `S` of `π*P` over `ℝᵐ × X` pulled back to
`ℝᵐ × ([0, 1]ⁿ × X)` along `(τ, (t, x)) ↦ (τ, x)`. -/
def cubeLiftProd {m n : ℕ}
    (S : (Fin m → ℝ) × X → pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))
    (hS : IsSection (pullbackProj P Prod.snd) S) :
    (Fin m → ℝ) × ((Fin n → unitInterval) × X) →
      pullbackSpace (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
        (Prod.snd : (Fin m → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X) :=
  pullbackLift Prod.snd
    (fun w => cubeLift (n := n) (pullbackSlice S w.1) (hS.pullbackSlice w.1) w.2) fun _ => rfl

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The slices of `Ŝ` are the `t`-constant lifts of the slices of `S`. -/
theorem pullbackSlice_cubeLiftProd {m n : ℕ}
    (S : (Fin m → ℝ) × X → pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))
    (hS : IsSection (pullbackProj P Prod.snd) S) (τ : Fin m → ℝ) :
    pullbackSlice (cubeLiftProd (n := n) S hS) τ =
      cubeLift (n := n) (pullbackSlice S τ) (hS.pullbackSlice τ) :=
  rfl

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
theorem isSection_cubeLiftProd {m n : ℕ}
    (S : (Fin m → ℝ) × X → pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))
    (hS : IsSection (pullbackProj P Prod.snd) S) :
    IsSection (pullbackProj (pullbackProj P (Prod.snd : (Fin n → unitInterval) × X → X))
      Prod.snd) (cubeLiftProd (n := n) S hS) :=
  isSection_pullbackLift _

/-- **`Ŝ` is an sc⁺-section** when `S` is: in the product charts over a chart `c` of `P`, its
representative is that of `S` composed with `(a, (b, u)) ↦ (a, u)`. -/
theorem isScPlusSection_cubeLiftProd {m n : ℕ}
    [ParacompactSpace ((Fin m → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]
    [ParacompactSpace ((Fin n → unitInterval) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → unitInterval) × X → X))]
    [ParacompactSpace ((Fin m → ℝ) × ((Fin n → unitInterval) × X))]
    [ParacompactSpace (pullbackSpace (pullbackProj P
      (Prod.snd : (Fin n → unitInterval) × X → X))
      (Prod.snd : (Fin m → ℝ) × ((Fin n → unitInterval) × X) → (Fin n → unitInterval) × X))]
    {S : (Fin m → ℝ) × X → pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsScPlusSection S) :
    ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold m) ((cubePolyfold n).prod PX))).IsScPlusSection
      (cubeLiftProd (n := n) S hS.1) := by
  set S' := cubeLiftProd (n := n) S hS.1 with hS'
  have hsec : IsSection (pullbackProj (pullbackProj P
      (Prod.snd : (Fin n → unitInterval) × X → X)) Prod.snd) S' := isSection_pullbackLift _
  refine StrongBundle.isScPlusSection_of_local hsec fun z => ?_
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem B z.2.2
  set b := corner z.2.1 with hb
  obtain ⟨Rb, hRb⟩ := (chart b).model.isScRetract
  -- the product charts at `z = (τ, (t, x))` and at `(τ, x)`
  set c₁ := (PullbackChartData.ofProdChart (isChart_chart b) Rb hRb c).toChart (S' z).1.2
    with hc₁
  set c' := (PullbackChartData.ofProd c₁ z.1).toChart (S' z) with hc'
  set pc := (PullbackChartData.ofProd c z.1).toChart (S (z.1, z.2.2)) with hpc
  have hmem₁ :
      c₁ ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).atlas.charts :=
    ⟨_, _, hc, rfl⟩
  have hmem' : c' ∈ ((B.pullback (MPolyfold.isScSmoothMap_snd (cubePolyfold n) PX)).pullback
      (MPolyfold.isScSmoothMap_snd (rnPolyfold m) ((cubePolyfold n).prod PX))).atlas.charts :=
    ⟨_, _, hmem₁, rfl⟩
  have hmem : pc ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).atlas.charts :=
    ⟨_, _, hc, rfl⟩
  obtain ⟨hrange, hsm⟩ := hS.2 pc hmem
  have hsrc : ∀ w ∈ c'.φ.source, ((w.1, w.2.2) : (Fin m → ℝ) × X) ∈ pc.φ.source :=
    fun w hw => ⟨mem_univ _, hw.2.2⟩
  refine ⟨c', hmem', ⟨mem_univ _, mem_chart_corner z.2.1, hxc⟩,
    fun w hw => hrange _ (hsrc w hw), ?_⟩
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
    obtain ⟨a, b₁, u⟩ := p
    have hu : u ∈ c.φ.model.O := hRw.2.2
    have hb₁ : b₁ ∈ (chart b).model.O := hRw.2.1
    set a' : Fin m → ℝ := a
    set b' : Fin n → ℝ := b₁
    change ((a', (b', u)),
        Function.invFun (c.F.toBase 1) (c (S (a' + z.1, c.φ.symm u)).1.2).2) =
      ((a' + z.1 - z.1, ((chart b ((chart b).symm b') : Fin n → ℝ), c.φ (c.φ.symm u))),
        Function.invFun (c.F.toBase 1) (c (S (a' + z.1, c.φ.symm u)).1.2).2)
    rw [c.φ.apply_symm_apply hu, add_sub_cancel_right, (chart b).apply_symm_apply hb₁]
    rfl

end IvSections

/-! ### `L̂ ∈ Lin(f̂, (t, x))` over `[0, 1] × X` -/

section IvLinSet

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (b : Fin 1 → Bool) {t : Fin 1 → unitInterval}
  (ht : t ∈ (chart b).source)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))

/-- **The linearization of `g̃` in the product chart point** is `(σ, v) ↦ g'(x) v`: the chain
rule for `ĝ ∘ r` composed with `(a, u) ↦ u`, on the relatively open subset `[0, 1) × U` of the
partial quadrant `[0, ∞) × C`. -/
theorem linAt_ivPt_cubeLift {g : X → Y} (hg : B.IsScSmoothSection g)
    (v : ↥(p.ivPt b ht q₀).T) :
    linAt (p.ivPt b ht q₀).c.U (p.ivPt b ht q₀).c.R
        ((p.ivPt b ht q₀).c.principal (cubeLift (n := 1) g hg.1)) (p.ivPt b ht q₀).z v =
      linAt p.c.U p.c.R (p.c.principal g) p.z (p.ivT b ht q₀ v).1 := by
  set pc := ivChart b p.c q₀ with hpc
  have hG : IsSc1 p.c.U (p.c.principal g ∘ r p.c.R) := hg.isSc1_principal_comp_r p.isChart
  set pr := ScBanach.prodSndOp (rnSc 1) p.c.φ.model.E with hpr
  have hpr1 : IsSc1 (E := pc.φ.model.E) (F := p.c.φ.model.E) pc.U (pr 0) :=
    ((pr.isScSmooth pc.relOpen.isScDomain) 1).1
  have hpr0 : IsSc0 pc.φ.model.E p.c.φ.model.E univ (pr 0) := pr.isSc0
  have hmaps : MapsTo (pr 0) pc.U p.c.U := fun w hw => hw.2
  have hz : (p.ivPt b ht q₀).z ∈ pc.φ.model.E.lvlSet pc.U 1 := (p.ivPt b ht q₀).mem_U
  have hchain := scDeriv_comp_apply' pc.relOpen p.c.relOpen hpr1 hG hmaps hz
    (v.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0)
  have hlvl : levelMap (E := pc.φ.model.E) (F := p.c.φ.model.E) (pr 0) 1 (p.ivPt b ht q₀).z =
      p.z := by
    apply p.c.φ.model.E.toBase_injective 1
    refine (IsSc0.toBase_levelMap hpr0 (x := (p.ivPt b ht q₀).z)
      (mem_univ _)).trans ?_
    exact congrArg Prod.snd (p.ivPt_toBase b ht q₀)
  have hDpr : scDeriv (E := pc.φ.model.E) (F := p.c.φ.model.E) pc.U (pr 0) (p.ivPt b ht q₀).z =
      pr 0 := pr.scDeriv_eq pc.relOpen.isScDomain hz
  rw [hlvl, hDpr] at hchain
  exact hchain.symm

/-- The principal part of `s̃` at `(t, x)` in the product chart is that of `s` at `x`. -/
theorem principal_ivPt_cubeLift {s : X → Y} (hs : IsSection P s) :
    (p.ivPt b ht q₀).c.principal (cubeLift (n := 1) s hs) ((p.ivPt b ht q₀).c.φ (t, x)) =
      p.c.principal s (p.c.φ x) := by
  have h1 : (p.ivPt b ht q₀).c.φ.symm ((p.ivPt b ht q₀).c.φ (t, x)) = (t, x) :=
    (p.ivPt b ht q₀).c.φ.symm_apply_apply (p.ivPt b ht q₀).mem_source
  have h2 : p.c.φ.symm (p.c.φ x) = x := p.c.φ.symm_apply_apply p.mem_source
  change ((p.ivPt b ht q₀).c (cubeLift (n := 1) s hs
    ((p.ivPt b ht q₀).c.φ.symm ((p.ivPt b ht q₀).c.φ (t, x))))).2 =
      (p.c (s (p.c.φ.symm (p.c.φ x)))).2
  rw [h1, h2]
  rfl

/-- **`L̂ ∈ Lin(f̂, (t, x))`** for `L ∈ Lin(f, x)` (2021 Remark 6.6.19, "`L̃` belongs to the
linearization space of `f̂` at `(x, t)`"), at a smooth point `x` and every `t ∈ [0, 1]`, for
`f̂ = f̃ + S` with an sc⁺-section `S` over `[0, 1] × X`: for `L = (f + s)'(x) + a`, take
`ŝ = s̃ − S`; then `f̂ + ŝ = (f + s)~`, whose linearization is `(σ, v) ↦ (f + s)'(x) v`. -/
theorem ivLin_mem_linSet (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S) {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) :
    p.ivLin b ht q₀ L ∈ (p.ivPt b ht q₀).linSet
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) := by
  obtain ⟨s₀, hs₀, hz₀, a, ha, hLa⟩ := hL
  have hfs : IsSection P f := hf.isScSmooth.1
  have hg : B.IsScSmoothSection (sectionAdd P f s₀) := hf.isScSmooth.sectionAdd hs₀
  have hŝ₀ := isScPlusSection_cubeLift (n := 1) (B := B) hs₀
  have hŝ : (ivBundle B).IsScPlusSection
      (sectionDiff (pullbackProj P Prod.snd) (cubeLift (n := 1) s₀ hs₀.1) S) :=
    hŝ₀.add (hS.smul_left (isScSmoothMap_real_const _))
  have hpl : IsSection (pullbackProj P Prod.snd) (cubeLift (n := 1) f hfs) :=
    isSection_pullbackLift _
  have hsum : sectionAdd (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hfs) S)
      (sectionDiff (pullbackProj P Prod.snd) (cubeLift (n := 1) s₀ hs₀.1) S) =
        cubeLift (n := 1) (sectionAdd P f s₀) hg.1 := by
    rw [sectionAdd_sectionAdd_sectionDiff hpl hS.1 hŝ₀.1]
    exact sectionAdd_cubeLift hfs hs₀.1
  refine ⟨_, hŝ, ?_, _, IsScPlusOp.ivPt p b ht q₀ hx ha, fun v => ?_⟩
  · rw [hsum]
    exact (isZeroAt_iff_prodSlice (isSection_pullbackLift _) t x).2 hz₀
  · rw [hsum, p.linAt_ivPt_cubeLift b ht q₀ hg v, coe_ivLin_apply, hLa]
    rfl

end ChartPoint

end IvLinSet

end Polyfold
