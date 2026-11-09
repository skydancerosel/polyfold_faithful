import Polyfold.Chapter2.TangentMap
import Polyfold.Chapter2.Metrizable

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 8,
§8.1, the proof of **Proposition 8.1.16** (p. 369, new in the 2021 edition): the tool it uses on
the second tangent bundle `T(TX)`.

# Vertical vectors in `T(TX)`

## The text, paraphrased

(Proof of Proposition 8.1.16, pp. 369–370) For an isotropy element `(g, h)` of a smooth
`b ∈ T_xX`, the natural action `H = Tt ∘ (Ts|U(g, h))⁻¹` lifts `ĝ` (8.16); if `T(g, h) = TH(b)` is
the identity, differentiating (8.16) and using that `Tτ_X : T_b(TX) → T_xX` is onto gives
`Tg = id`.

## What is formalized

The step is carried out with the **vertical vectors** of `T(TX)`: for `α ∈ TX` on level `1` over
`x` and `w ∈ T_xX`, the vector `vert α w ∈ T_α(TX)` whose chart representative is
`(Tφ(α), (0, h))` when `Tφ(w) = (φ(x), h)`.  The facts used are:

* `IsSc1.scDeriv_tangentMap_vert` (sc-calculus): for `f` of class sc² on `U`,
  `D(Tf)(x, h)(0, v) = (0, Df(x) v)`, by differentiating along the line `t ↦ (x, h + t u)`,
  `u ∈ E₁`, and density of `E₁` in `E₀`.
* `ScRetraction.mem_tangent_tangentRetraction_vert`, `retractTangentMap_tangent_vert` (retracts):
  `(a, (0, v)) ∈ T(TO)` for `a ∈ (TO)₁` over `x` and `(x, v) ∈ TO`, and
  `T(Tf)(a, (0, v)) = (Tf(a), (0, Df(x) v))`.
* `MPolyfold.vert`, `tangentProj_vert` (`vert α w ∈ T_α(TX)`), `tangentChartMap_vert` (its
  representative in every chart `T(Tφ)`), `vert_injective` and **`tangentMap_tangentMap_vert`**
  (naturality: `T(Tf)(vert α w) = vert (Tf α) (Tf w)` for every sc-smooth `f : X → Y`).

This replaces the text's "differentiating (8.16) and `Tτ_X` onto": a vertical vector at `b` is
mapped by `TH(b)` to the vertical vector of `Tg(w)`, so `TH(b) = id` forces `Tg = id`
(`TangentZhouReflect2021.lean`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

/-! ### Sc-calculus: the derivative of `Tf` in the vertical direction -/

section Calculus

variable {E F : ScBanach}

/-- `E₁` is dense in `E₀`. -/
theorem ScBanach.denseRange_toBase_one (E : ScBanach) : DenseRange (E.toBase 1) :=
  E.denseRange_inclK 0 1

/-- **The derivative of `Tf` in the vertical direction**: if `f` is sc¹ on `U` and `Tf` is sc¹ on
`TU`, then for `p = (x, h) ∈ (TU)₁` and `v ∈ E₀`, `D(Tf)(p)(0, v) = (0, Df(x) v)`. -/
theorem IsSc1.scDeriv_tangentMap_vert {U : Set (E 0)} {f : E 0 → F 0}
    (hg : IsSc1 (E.tangentSet U) (tangentMap U f)) {p : E.tangent 1}
    (hp : p ∈ E.tangent.lvlSet (E.tangentSet U) 1) (v : E 0) :
    scDeriv (E.tangentSet U) (tangentMap U f) p (((0 : E 1), v) : E.tangent 0) =
      (((0 : F 1), scDeriv U f (E.shift.toBase 1 p.1) v) : F.tangent 0) := by
  set D2 := scDeriv (E.tangentSet U) (tangentMap U f) p
  set D := scDeriv U f (E.shift.toBase 1 p.1)
  have hD := hg.isSc1With_scDeriv.hasFDerivWithinAt p hp
  have key : ∀ u : E 1, D2 (((0 : E 1), E.toBase 1 u) : E.tangent 0) =
      (((0 : F 1), D (E.toBase 1 u)) : F.tangent 0) := by
    intro u
    let d : E.tangent 1 := ((0 : E 2), u)
    let ℓ : ℝ → E.tangent 1 := fun t => p + t • d
    have hℓ : HasDerivAt ℓ d 0 := by
      simpa [ℓ] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add p
    have hmaps : ∀ t, ℓ t ∈ E.tangent.lvlSet (E.tangentSet U) 1 := by
      intro t
      rw [ScBanach.mem_lvlSet_tangentSet] at hp ⊢
      simpa [ℓ, d] using hp
    have hℓ0 : ℓ 0 = p := by simp [ℓ]
    have h1 : HasDerivWithinAt ((tangentMap U f ∘ E.tangent.toBase 1) ∘ ℓ)
        ((D2.comp (E.tangent.toBase 1)) d) univ 0 := by
      have hD' : HasFDerivWithinAt (tangentMap U f ∘ E.tangent.toBase 1)
          (D2.comp (E.tangent.toBase 1)) (E.tangent.lvlSet (E.tangentSet U) 1) (ℓ 0) := by
        rw [hℓ0]; exact hD
      exact hD'.comp_hasDerivWithinAt (0 : ℝ) hℓ.hasDerivWithinAt fun t _ => hmaps t
    have hb : ∀ t, E.tangent.toBase 1 (ℓ t) =
        (((E.shift.toBase 1 p.1, E.toBase 1 p.2 + t • E.toBase 1 u)) : E.tangent 0) := by
      intro t
      simp only [ℓ, map_add, map_smul]
      rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase]
      refine Prod.ext ?_ rfl
      simp [d]
    have hfun : (tangentMap U f ∘ E.tangent.toBase 1) ∘ ℓ = fun t : ℝ =>
        (((levelMap f 1 (E.shift.toBase 1 p.1),
          D (E.toBase 1 p.2) + t • D (E.toBase 1 u)) : F.tangent 0)) := by
      funext t
      rw [Function.comp_apply, Function.comp_apply, hb t]
      change ((levelMap f 1 (E.shift.toBase 1 p.1), D (E.toBase 1 p.2 + t • E.toBase 1 u)) :
        F.tangent 0) = _
      rw [map_add, map_smul]
    have h2 : HasDerivAt ((tangentMap U f ∘ E.tangent.toBase 1) ∘ ℓ)
        (((0 : F 1), D (E.toBase 1 u)) : F.tangent 0) 0 := by
      rw [hfun]
      have hc := hasDerivAt_const (0 : ℝ) (levelMap f 1 (E.shift.toBase 1 p.1))
      have hl := ((hasDerivAt_id (0 : ℝ)).smul_const (D (E.toBase 1 u))).const_add
        (D (E.toBase 1 p.2))
      simp only [id, one_smul] at hl
      exact hc.prodMk hl
    have h3 := (h1.hasDerivAt univ_mem).unique h2
    have hd : E.tangent.toBase 1 d = (((0 : E 1), E.toBase 1 u) : E.tangent 0) := by
      rw [ScBanach.tangent_toBase]
      refine Prod.ext ?_ rfl
      simp [d]
    rwa [ContinuousLinearMap.comp_apply, hd] at h3
  have hcont1 : Continuous fun w : E 0 => D2 (((0 : E 1), w) : E.tangent 0) :=
    D2.continuous.comp (continuous_const.prodMk continuous_id)
  have hcont2 : Continuous fun w : E 0 => (((0 : F 1), D w) : F.tangent 0) :=
    continuous_const.prodMk D.continuous
  exact congrFun (E.denseRange_toBase_one.equalizer hcont1 hcont2 (funext key)) v

end Calculus

/-! ### Retracts: vertical vectors of `T(TO)` -/

section Retract

variable {E E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}

/-- `Tr` is sc¹ on `TU` for an sc-smooth retraction `r`. -/
lemma ScRetraction.isSc1_tangentMap (R : ScRetraction E C) :
    IsSc1 (E.tangentSet R.U) (tangentMap R.U R) :=
  (isScSmooth_iff.1 R.isScSmooth).2.isSc1

/-- **Vertical vectors of `T(TO)`**: for `a ∈ (TO)₁` with base point `x` and `(x, v) ∈ TO`,
`(a, (0, v))` is a fixed point of `T(Tr)`, i.e. lies in `T(TO)`. -/
theorem ScRetraction.mem_tangent_tangentRetraction_vert (R : ScRetraction E C) {a : E.tangent 1}
    (ha : E.tangent.toBase 1 a ∈ R.tangent) {v : E 0}
    (hv : (((E.tangent.toBase 1 a).1, v) : E.tangent 0) ∈ R.tangent) :
    ((a, ((0 : E 1), v)) : E.tangent.tangent 0) ∈ R.tangentRetraction.tangent := by
  have hfst : (E.tangent.toBase 1 a).1 = E.shift.toBase 1 a.1 := by rw [ScBanach.tangent_toBase]
  have haU : a ∈ E.tangent.lvlSet (E.tangentSet R.U) 1 := R.tangent_subset ha
  rw [R.tangentRetraction.mem_tangent_iff]
  refine ⟨haU, ?_⟩
  change ((levelMap (tangentMap R.U R) 1 a,
    scDeriv (E.tangentSet R.U) (tangentMap R.U R) a (((0 : E 1), v) : E.tangent 0)) :
      E.tangent.tangent 0) = (a, ((0 : E 1), v))
  rw [R.isSc1_tangentMap.scDeriv_tangentMap_vert haU v]
  have h1 : levelMap (tangentMap R.U R) 1 a = a :=
    levelMap_eq_of_toBase_eq (R.mem_tangent_iff.1 ha).2.symm
  have h2 : scDeriv R.U R (E.shift.toBase 1 a.1) v = v := by
    rw [← hfst]
    exact (R.mem_tangent_iff_of_mem (R.fst_mem_of_mem_tangent ha)).1 hv
  rw [h1, h2]

/-- `T(f ∘ r) = Tf ∘ Tr` on `TU`. -/
lemma IsScSmoothRetractMap.tangentMap_comp_retraction {O' : Set (E' 0)} {f : E 0 → E' 0}
    (R : ScRetraction E C) (hf : IsScSmoothRetractMap E C R.retract E' C' O' f) {p : E.tangent 0}
    (hp : p ∈ E.tangentSet R.U) :
    tangentMap R.U (f ∘ R) p = retractTangentMap E C R.retract f (tangentMap R.U R p) := by
  have h1 : tangentMap R.U R p ∈ retractTangent E C R.retract := by
    rw [retractTangent_eq]; exact ⟨p, hp, rfl⟩
  rw [retractTangentMap_eqOn hf R rfl h1]
  obtain ⟨_, hchain⟩ := theorem_1_3_1 R.relOpen R.relOpen R.isSc1 (hf.comp_isScSmooth R rfl).isSc1
    R.mapsTo
  have hcongr : EqOn (tangentMap R.U (f ∘ R)) (tangentMap R.U ((f ∘ R) ∘ R)) (E.tangentSet R.U) :=
    (hf.comp_isScSmooth R rfl).isSc1.tangentMap_congr R.isScDomain fun y hy => by
      simp only [Function.comp_apply, R.idem y hy]
  exact (hcongr hp).trans (hchain hp)

/-- **`T(Tf)` on vertical vectors**: for an sc-smooth `f : O → O'`, `a ∈ (TO)₁` over `x` and
`(x, v) ∈ TO`, `(a, (0, v)) ∈ T(TO)` and `T(Tf)(a, (0, v)) = (·, (0, Df(x) v))`. -/
theorem retractTangentMap_tangent_vert {O : Set (E 0)} {O' : Set (E' 0)} {f : E 0 → E' 0}
    (hf : IsScSmoothRetractMap E C O E' C' O' f) (hO : IsScRetract E C O)
    (hO' : IsScRetract E' C' O') {a : E.tangent 1}
    (ha : E.tangent.toBase 1 a ∈ retractTangent E C O) {v : E 0}
    (hv : (((E.tangent.toBase 1 a).1, v) : E.tangent 0) ∈ retractTangent E C O) :
    ((a, ((0 : E 1), v)) : E.tangent.tangent 0) ∈
        retractTangent E.tangent (E.tangentSet C) (retractTangent E C O) ∧
      (retractTangentMap E.tangent (E.tangentSet C) (retractTangent E C O)
        (retractTangentMap E C O f) (a, ((0 : E 1), v))).2 =
        (((0 : E' 1), (retractTangentMap E C O f ((E.tangent.toBase 1 a).1, v)).2) :
          E'.tangent 0) := by
  obtain ⟨R, rfl⟩ := hO
  have hvR := hv
  rw [retractTangent_eq] at ha hvR
  have hmem' : ((a, ((0 : E 1), v)) : E.tangent.tangent 0) ∈
      retractTangent E.tangent (E.tangentSet C) (retractTangent E C R.retract) := by
    rw [← R.tangentRetraction_retract, retractTangent_eq]
    exact R.mem_tangent_tangentRetraction_vert ha hvR
  refine ⟨hmem', ?_⟩
  have hT := hf.tangent R.isScRetract hO'
  rw [retractTangentMap_eqOn hT R.tangentRetraction R.tangentRetraction_retract hmem']
  have hsm := hf.comp_isScSmooth R rfl
  have hsm1 : IsSc1 (E.tangentSet R.U) (tangentMap R.U (f ∘ R)) := (isScSmooth_iff.1 hsm).2.isSc1
  have hcongr : EqOn (tangentMap (E.tangentSet R.U) (tangentMap R.U (f ∘ R)))
      (tangentMap (E.tangentSet R.U) (retractTangentMap E C R.retract f ∘ R.tangentRetraction))
      (E.tangent.tangentSet (E.tangentSet R.U)) :=
    hsm1.tangentMap_congr R.isScDomain.tangentSet fun p hp =>
      hf.tangentMap_comp_retraction R hp
  have haU : a ∈ E.tangent.lvlSet (E.tangentSet R.U) 1 := R.tangent_subset ha
  change (tangentMap (E.tangentSet R.U)
    (retractTangentMap E C R.retract f ∘ R.tangentRetraction) (a, ((0 : E 1), v))).2 = _
  rw [← hcongr haU]
  change scDeriv (E.tangentSet R.U) (tangentMap R.U (f ∘ R)) a (((0 : E 1), v) : E.tangent 0) = _
  rw [hsm1.scDeriv_tangentMap_vert haU v, retractTangentMap_apply hf R rfl hv,
    ScBanach.tangent_toBase]

end Retract

/-! ### Vertical vectors of `T(TX)` -/

namespace MPolyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

section Vert

/-- `T(φ(s)) = Tφ(p⁻¹(s))` for an open `s ⊆ V`. -/
theorem image_tangentChart_preimage {φ : MChart X} (hφ : P.IsChart φ) (α₀ : P.TangentSpace)
    {s : Set X} (hs : s ⊆ φ.source) (hso : IsOpen s) :
    tangentChart hφ α₀ '' {γ | P.levelVal 1 (P.tangentProj γ) ∈ s} =
      retractTangent φ.model.E φ.model.C (φ '' s) := by
  ext a
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    have hγφ : γ ∈ tangentChartSet φ := hs hγ
    refine (TangentPre.mem_retractTangent_image_iff hs hso ?_).2 (tangentChartMap_mem hφ hγφ)
    change φ.model.E.toBase 1 (tangentChartMap hφ γ).1 ∈ φ '' s
    rw [tangentChartMap_fst hφ hγφ, P.toBase_levelLift hφ hγφ (levelVal_mem _)]
    exact ⟨_, hγ, rfl⟩
  · intro ha
    have hfst : φ.model.E.toBase 1 a.1 ∈ φ '' s :=
      retractTangent_fst_mem (φ.isScRetract_image hs hso) ha
    have haO : a ∈ retractTangent φ.model.E φ.model.C φ.model.O :=
      (TangentPre.mem_retractTangent_image_iff hs hso hfst).1 ha
    refine ⟨TangentSpace.mk (TangentPre.ofVec hφ haO), ?_, tangentChartMap_mk_ofVec hφ haO⟩
    change φ.symm (φ.model.E.toBase 1 a.1) ∈ s
    obtain ⟨y, hy, hyeq⟩ := hfst
    rw [← hyeq, φ.symm_apply_apply (hs hy)]
    exact hy

variable {φ : MChart X} (hφ : P.IsChart φ)

/-- The chart representative `(Tφ(α), (0, h))` of the vertical vector at `α` given by `w`, where
`Tφ(w) = (φ(x), h)`. -/
def vertRep (α w : P.TangentSpace) : φ.model.E.tangent.tangent 0 :=
  (levelLift (tangentChart hφ α) 1 α, ((0 : φ.model.E 1), (tangentChartMap hφ w).2))

variable {hφ}

theorem toBase_vertRep_fst {α : P.TangentSpace} (hα : α ∈ P.tangentPolyfold.levelSet 1)
    (hαφ : α ∈ tangentChartSet φ) (w : P.TangentSpace) :
    φ.model.E.tangent.toBase 1 (vertRep hφ α w).1 = tangentChartMap hφ α :=
  P.tangentPolyfold.toBase_levelLift (P.tangentPolyfold_isChart hφ α) hαφ hα

theorem vertRep_snd_eq {α w : P.TangentSpace} (hαφ : α ∈ tangentChartSet φ)
    (hw : P.tangentProj w = P.tangentProj α) :
    ((tangentChartMap hφ α).1, (tangentChartMap hφ w).2) = tangentChartMap hφ w := by
  have hwφ : w ∈ tangentChartSet φ := by
    change P.levelVal 1 (P.tangentProj w) ∈ φ.source; rw [hw]; exact hαφ
  refine Prod.ext ?_ rfl
  rw [tangentChartMap_fst hφ hαφ, tangentChartMap_fst hφ hwφ, hw]

/-- The vertical representative lies in `T(TO)`, and in `T(T(φ(s)))` when the base point lies in
the open `s ⊆ V`. -/
theorem vertRep_mem_image {α : P.TangentSpace} (hα : α ∈ P.tangentPolyfold.levelSet 1)
    {s : Set X} (hs : s ⊆ φ.source) (hso : IsOpen s) (hαs : P.levelVal 1 (P.tangentProj α) ∈ s)
    {w : P.TangentSpace} (hw : P.tangentProj w = P.tangentProj α) :
    vertRep hφ α w ∈ retractTangent φ.model.E.tangent (φ.model.E.tangentSet φ.model.C)
      (retractTangent φ.model.E φ.model.C (φ '' s)) := by
  have hαφ : α ∈ tangentChartSet φ := hs hαs
  have hwφ : w ∈ tangentChartSet φ := by
    change P.levelVal 1 (P.tangentProj w) ∈ φ.source; rw [hw]; exact hαφ
  have hO := φ.isScRetract_image hs hso
  have himg := image_tangentChart_preimage hφ α hs hso
  have ha : φ.model.E.tangent.toBase 1 (vertRep hφ α w).1 ∈
      retractTangent φ.model.E φ.model.C (φ '' s) := by
    rw [toBase_vertRep_fst hα hαφ, ← himg]; exact ⟨α, hαs, rfl⟩
  have hv : (((φ.model.E.tangent.toBase 1 (vertRep hφ α w).1).1, (tangentChartMap hφ w).2) :
      φ.model.E.tangent 0) ∈ retractTangent φ.model.E φ.model.C (φ '' s) := by
    rw [toBase_vertRep_fst hα hαφ, vertRep_snd_eq hαφ hw, ← himg]
    refine ⟨w, ?_, rfl⟩
    change P.levelVal 1 (P.tangentProj w) ∈ s; rw [hw]; exact hαs
  exact (retractTangentMap_tangent_vert (isScSmoothRetractMap_id (φ '' s)) hO hO ha hv).1

theorem vertRep_mem {α : P.TangentSpace} (hα : α ∈ P.tangentPolyfold.levelSet 1)
    (hαφ : α ∈ tangentChartSet φ) {w : P.TangentSpace} (hw : P.tangentProj w = P.tangentProj α) :
    vertRep hφ α w ∈ retractTangent φ.model.E.tangent (φ.model.E.tangentSet φ.model.C)
      (retractTangent φ.model.E φ.model.C φ.model.O) := by
  have h := vertRep_mem_image (hφ := hφ) hα subset_rfl φ.isOpen_source hαφ hw
  rwa [φ.image_source] at h

variable (P) in
/-- The chart of `X` chosen at the base point of `α ∈ TX`. -/
def vertChart (α : P.TangentSpace) : MChart X :=
  (P.exists_isChart_mem_source (P.levelVal 1 (P.tangentProj α))).choose

theorem isChart_vertChart (α : P.TangentSpace) : P.IsChart (P.vertChart α) :=
  (P.exists_isChart_mem_source _).choose_spec.1

theorem mem_vertChart (α : P.TangentSpace) : α ∈ tangentChartSet (P.vertChart α) :=
  (P.exists_isChart_mem_source _).choose_spec.2

variable (P) in
/-- **The vertical vector** `vert α w ∈ T_α(TX)` for `α ∈ (TX)₁` and `w ∈ T_{p(α)}X`: in the chart
`T(Tφ)` it is `(Tφ(α), (0, h))`, `Tφ(w) = (φ(x), h)` (`tangentChartMap_vert`). -/
def vert (α : P.TangentSpace) (hα : α ∈ P.tangentPolyfold.levelSet 1) (w : P.TangentSpace)
    (hw : P.tangentProj w = P.tangentProj α) : P.tangentPolyfold.TangentSpace :=
  TangentSpace.mk (TangentPre.ofVec (P.tangentPolyfold_isChart (P.isChart_vertChart α) α)
    (vertRep_mem (hφ := P.isChart_vertChart α) hα (P.mem_vertChart α) hw))

/-- Vertical vectors with equal data are equal. -/
theorem vert_congr {α α' : P.TangentSpace} (hαα : α = α')
    (hα : α ∈ P.tangentPolyfold.levelSet 1) (hα' : α' ∈ P.tangentPolyfold.levelSet 1)
    {w w' : P.TangentSpace} (hww : w = w') (hw : P.tangentProj w = P.tangentProj α)
    (hw' : P.tangentProj w' = P.tangentProj α') : P.vert α hα w hw = P.vert α' hα' w' hw' := by
  subst hαα hww; rfl

/-- `vert α w` lies over `α`. -/
theorem levelVal_tangentProj_vert (α : P.TangentSpace) (hα : α ∈ P.tangentPolyfold.levelSet 1)
    (w : P.TangentSpace) (hw : P.tangentProj w = P.tangentProj α) :
    P.tangentPolyfold.levelVal 1 (P.tangentPolyfold.tangentProj (P.vert α hα w hw)) = α := by
  have hφ := P.isChart_vertChart α
  have hαφ := P.mem_vertChart α
  change (tangentChart hφ α).symm ((P.vertChart α).model.E.tangent.toBase 1
    (vertRep hφ α w).1) = α
  rw [toBase_vertRep_fst hα hαφ]
  exact (tangentChart hφ α).symm_apply_apply hαφ

theorem tangentProj_vert (α : P.TangentSpace) (hα : α ∈ P.tangentPolyfold.levelSet 1)
    (w : P.TangentSpace) (hw : P.tangentProj w = P.tangentProj α) :
    P.tangentPolyfold.tangentProj (P.vert α hα w hw) = P.tangentPolyfold.levelMk 1 α hα :=
  level_ext (by rw [levelVal_tangentProj_vert, levelVal_levelMk])

/-- **`vert α w` in any chart**: in the chart `T(Tφ')` of `T(TX)` induced by a chart `φ'` of `X`
around the base point, `vert α w` is `(Tφ'(α), (0, h'))` with `Tφ'(w) = (φ'(x), h')`. -/
theorem tangentChartMap_vert {φ' : MChart X} (hφ' : P.IsChart φ') (α : P.TangentSpace)
    (hα : α ∈ P.tangentPolyfold.levelSet 1) (hαφ' : α ∈ tangentChartSet φ') (w : P.TangentSpace)
    (hw : P.tangentProj w = P.tangentProj α) :
    tangentChartMap (P.tangentPolyfold_isChart hφ' α) (P.vert α hα w hw) = vertRep hφ' α w := by
  set φ := P.vertChart α
  have hφ : P.IsChart φ := P.isChart_vertChart α
  have hαφ : α ∈ tangentChartSet φ := P.mem_vertChart α
  have hΦ := P.tangentPolyfold_isChart hφ α
  have hΦ' := P.tangentPolyfold_isChart hφ' α
  have hwφ : w ∈ tangentChartSet φ := by
    change P.levelVal 1 (P.tangentProj w) ∈ φ.source; rw [hw]; exact hαφ
  have hso : IsOpen (φ.source ∩ φ'.source) := φ.isOpen_source.inter φ'.isOpen_source
  have hαs : P.levelVal 1 (P.tangentProj α) ∈ φ.source ∩ φ'.source := ⟨hαφ, hαφ'⟩
  have hA := vertRep_mem (hφ := hφ) hα hαφ hw
  have hAov' := vertRep_mem_image (hφ := hφ) hα inter_subset_left hso hαs hw
  have hAov : vertRep hφ α w ∈ retractTangent (tangentChart hφ α).model.E
      (tangentChart hφ α).model.C ((tangentChart hφ α).overlap (tangentChart hφ' α)) := by
    rw [tangentChart_overlap hφ α hφ' α]; exact hAov'
  have hvmem : P.vert α hα w hw ∈ tangentChartSet (tangentChart hφ' α) := by
    change P.tangentPolyfold.levelVal 1 (P.tangentPolyfold.tangentProj (P.vert α hα w hw)) ∈
      tangentChartSet φ'
    rw [levelVal_tangentProj_vert]; exact hαφ'
  refine Prod.ext ?_ ?_
  · rw [tangentChartMap_fst hΦ' hvmem, levelVal_tangentProj_vert]; rfl
  · have h1 := tangentChartMap_mk_ofVec_of_mem hΦ hΦ' hA hAov
    change (tangentChartMap hΦ' (TangentSpace.mk (TangentPre.ofVec hΦ hA))).2 = _
    rw [h1]
    have hG := (hφ.compatible hφ' (P := P)).1.tangent (φ.isScRetract_overlap φ')
      (φ'.isScRetract_overlap φ)
    have heq : EqOn (retractTangentMap φ.model.E φ.model.C (φ.overlap φ') (φ.transition φ'))
        ((tangentChart hφ α).transition (tangentChart hφ' α))
        (retractTangent φ.model.E φ.model.C (φ.overlap φ')) :=
      fun a ha => (tangentChart_transition hφ α hφ' α ha).symm
    have hcongr := retractTangentMap_congr hG (φ.isScRetract_overlap φ').tangentSet heq hAov'
    have hov : (tangentChart hφ α).overlap (tangentChart hφ' α) =
        retractTangent φ.model.E φ.model.C (φ.overlap φ') := tangentChart_overlap hφ α hφ' α
    have hv : (((φ.model.E.tangent.toBase 1 (vertRep hφ α w).1).1, (tangentChartMap hφ w).2) :
        φ.model.E.tangent 0) ∈ retractTangent φ.model.E φ.model.C (φ.overlap φ') := by
      rw [toBase_vertRep_fst hα hαφ, vertRep_snd_eq hαφ hw]
      exact (TangentPre.mem_retractTangent_image_iff inter_subset_left hso (by
        rw [tangentChartMap_fst hφ hwφ, P.toBase_levelLift hφ hwφ (levelVal_mem _), hw]
        exact ⟨_, hαs, rfl⟩)).2 (tangentChartMap_mem hφ hwφ)
    have ha : φ.model.E.tangent.toBase 1 (vertRep hφ α w).1 ∈
        retractTangent φ.model.E φ.model.C (φ.overlap φ') := by
      rw [toBase_vertRep_fst hα hαφ]
      exact (TangentPre.mem_retractTangent_image_iff inter_subset_left hso (by
        rw [tangentChartMap_fst hφ hαφ, P.toBase_levelLift hφ hαφ (levelVal_mem _)]
        exact ⟨_, hαs, rfl⟩)).2 (tangentChartMap_mem hφ hαφ)
    have h3 : retractTangentMap (tangentChart hφ α).model.E (tangentChart hφ α).model.C
        ((tangentChart hφ α).overlap (tangentChart hφ' α))
        ((tangentChart hφ α).transition (tangentChart hφ' α)) (vertRep hφ α w) =
      retractTangentMap φ.model.E.tangent (φ.model.E.tangentSet φ.model.C)
        (retractTangent φ.model.E φ.model.C (φ.overlap φ'))
        (retractTangentMap φ.model.E φ.model.C (φ.overlap φ') (φ.transition φ'))
        (vertRep hφ α w) := by
      rw [hcongr]; exact congrArg (fun S => retractTangentMap φ.model.E.tangent
        (φ.model.E.tangentSet φ.model.C) S ((tangentChart hφ α).transition (tangentChart hφ' α))
        (vertRep hφ α w)) hov
    rw [h3]
    refine ((retractTangentMap_tangent_vert (hφ.compatible hφ' (P := P)).1
      (φ.isScRetract_overlap φ') (φ'.isScRetract_overlap φ) ha hv).2).trans ?_
    rw [toBase_vertRep_fst hα hαφ, vertRep_snd_eq hαφ hw]
    have hwov : tangentChartMap hφ w ∈ retractTangent φ.model.E φ.model.C (φ.overlap φ') := by
      rw [← vertRep_snd_eq hαφ hw, ← toBase_vertRep_fst hα hαφ w]; exact hv
    rw [← tangentChartMap_mk_ofVec_of_mem hφ hφ' (tangentChartMap_mem hφ hwφ) hwov,
      mk_ofVec_tangentChartMap hφ hwφ]
    rfl

/-- **`vert α` is injective**. -/
theorem vert_injective {α : P.TangentSpace} {hα : α ∈ P.tangentPolyfold.levelSet 1}
    {w w' : P.TangentSpace} {hw : P.tangentProj w = P.tangentProj α}
    {hw' : P.tangentProj w' = P.tangentProj α} (h : P.vert α hα w hw = P.vert α hα w' hw') :
    w = w' := by
  have hφ := P.isChart_vertChart α
  have hαφ := P.mem_vertChart α
  have h1 := congrArg (tangentChartMap (P.tangentPolyfold_isChart hφ α)) h
  rw [tangentChartMap_vert hφ α hα hαφ, tangentChartMap_vert hφ α hα hαφ] at h1
  have h2 : (tangentChartMap hφ w).2 = (tangentChartMap hφ w').2 :=
    congrArg (fun z : (P.vertChart α).model.E.tangent.tangent 0 => z.2.2) h1
  have hwφ : w ∈ tangentChartSet (P.vertChart α) := by
    change P.levelVal 1 (P.tangentProj w) ∈ (P.vertChart α).source; rw [hw]; exact hαφ
  have hw'φ : w' ∈ tangentChartSet (P.vertChart α) := by
    change P.levelVal 1 (P.tangentProj w') ∈ (P.vertChart α).source; rw [hw']; exact hαφ
  apply tangentChartMap_injOn hφ hwφ hw'φ
  rw [← vertRep_snd_eq hαφ hw, ← vertRep_snd_eq hαφ hw', h2]

/-- `T(V ∩ f⁻¹(V')) = TV ∩ (Tf)⁻¹(TV')`. -/
theorem fdom_tangentChart {f : X → Y} (hf : P.IsScSmoothMap Q f) {φ : MChart X}
    (hφ : P.IsChart φ) {ψ : MChart Y} (hψ : Q.IsChart ψ) (α₀ : P.TangentSpace)
    (β₀ : Q.TangentSpace) :
    TangentPre.fdom (tangentChart hφ α₀) (tangentMap hf) (tangentChart hψ β₀) =
      {γ | P.levelVal 1 (P.tangentProj γ) ∈ TangentPre.fdom φ f ψ} := by
  ext γ
  change P.levelVal 1 (P.tangentProj γ) ∈ φ.source ∧
    Q.levelVal 1 (Q.tangentProj (tangentMap hf γ)) ∈ ψ.source ↔ _
  rw [levelVal_tangentProj_tangentMap]
  rfl

/-- **Naturality of vertical vectors**: for an sc-smooth `f : X → Y`,
`T(Tf)(vert α w) = vert (Tf α) (Tf w)`. -/
theorem tangentMap_tangentMap_vert {f : X → Y} (hf : P.IsScSmoothMap Q f)
    (hTf : P.tangentPolyfold.IsScSmoothMap Q.tangentPolyfold (tangentMap hf))
    (α : P.TangentSpace) (hα : α ∈ P.tangentPolyfold.levelSet 1) (w : P.TangentSpace)
    (hw : P.tangentProj w = P.tangentProj α) :
    tangentMap hTf (P.vert α hα w hw) =
      Q.vert (tangentMap hf α) (hTf.mapsTo_levelSet 1 hα) (tangentMap hf w)
        (level_ext (by
          rw [levelVal_tangentProj_tangentMap, levelVal_tangentProj_tangentMap, hw])) := by
  obtain ⟨φ, hφ, hαφ⟩ := P.exists_isChart_mem_source (P.levelVal 1 (P.tangentProj α))
  obtain ⟨ψ, hψ, hfψ⟩ := Q.exists_isChart_mem_source (f (P.levelVal 1 (P.tangentProj α)))
  have hαφ' : α ∈ tangentChartSet φ := hαφ
  have hΦ := P.tangentPolyfold_isChart hφ α
  have hΨ := Q.tangentPolyfold_isChart hψ (tangentMap hf α)
  have hfα : tangentMap hf α ∈ tangentChartSet ψ := by
    change Q.levelVal 1 (Q.tangentProj (tangentMap hf α)) ∈ ψ.source
    rw [levelVal_tangentProj_tangentMap]; exact hfψ
  have hwφ : w ∈ tangentChartSet φ := by
    change P.levelVal 1 (P.tangentProj w) ∈ φ.source; rw [hw]; exact hαφ
  have hβΦ : P.vert α hα w hw ∈ tangentChartSet (tangentChart hφ α) := by
    change P.tangentPolyfold.levelVal 1 (P.tangentPolyfold.tangentProj (P.vert α hα w hw)) ∈
      tangentChartSet φ
    rw [levelVal_tangentProj_vert]; exact hαφ'
  have hTβ : tangentMap hTf (P.vert α hα w hw) ∈
      tangentChartSet (tangentChart hψ (tangentMap hf α)) := by
    change Q.tangentPolyfold.levelVal 1
      (Q.tangentPolyfold.tangentProj (tangentMap hTf (P.vert α hα w hw))) ∈ tangentChartSet ψ
    rw [levelVal_tangentProj_tangentMap, levelVal_tangentProj_vert]; exact hfα
  have hvmem : Q.vert (tangentMap hf α) (hTf.mapsTo_levelSet 1 hα) (tangentMap hf w)
      (level_ext (by rw [levelVal_tangentProj_tangentMap, levelVal_tangentProj_tangentMap, hw])) ∈
      tangentChartSet (tangentChart hψ (tangentMap hf α)) := by
    change Q.tangentPolyfold.levelVal 1 (Q.tangentPolyfold.tangentProj (Q.vert _ _ _ _)) ∈
      tangentChartSet ψ
    rw [levelVal_tangentProj_vert]; exact hfα
  apply tangentChartMap_injOn hΨ hTβ hvmem
  rw [tangentChartMap_vert hψ _ _ hfα]
  refine Prod.ext ?_ ?_
  · rw [tangentChartMap_fst hΨ hTβ, levelVal_tangentProj_tangentMap, levelVal_tangentProj_vert]
    rfl
  · have hfβ : tangentMap hf (P.tangentPolyfold.levelVal 1
        (P.tangentPolyfold.tangentProj (P.vert α hα w hw))) ∈
        (tangentChart hψ (tangentMap hf α)).source := by
      rw [levelVal_tangentProj_vert]; exact hfα
    rw [tangentChartMap_tangentMap hTf hΦ hΨ hβΦ hfβ, tangentChartMap_vert hφ α hα hαφ' w hw]
    set s := TangentPre.fdom φ f ψ
    have hso : IsOpen s := TangentPre.isOpen_fdom hf φ ψ
    have hαs : P.levelVal 1 (P.tangentProj α) ∈ s := ⟨hαφ, hfψ⟩
    have hss : s ⊆ φ.source := inter_subset_left
    have himg := image_tangentChart_preimage hφ α hss hso
    have hS : tangentChart hφ α '' TangentPre.fdom (tangentChart hφ α) (tangentMap hf)
        (tangentChart hψ (tangentMap hf α)) = retractTangent φ.model.E φ.model.C (φ '' s) := by
      rw [fdom_tangentChart hf hφ hψ]; exact himg
    have hF := TangentPre.isScSmoothRetractMap_coord hf hφ hψ subset_rfl hso
    have hO := φ.isScRetract_image hss hso
    have hG := hF.tangent hO ψ.model.isScRetract
    have heq : EqOn (retractTangentMap φ.model.E φ.model.C (φ '' s) (ψ ∘ f ∘ φ.symm))
        (tangentChart hψ (tangentMap hf α) ∘ tangentMap hf ∘ (tangentChart hφ α).symm)
        (retractTangent φ.model.E φ.model.C (φ '' s)) := by
      intro a ha
      have hfst := retractTangent_fst_mem hO ha
      have haO : a ∈ retractTangent φ.model.E φ.model.C φ.model.O :=
        (TangentPre.mem_retractTangent_image_iff hss hso hfst).1 ha
      have hmk : (tangentChart hφ α).symm a = TangentSpace.mk (TangentPre.ofVec hφ haO) :=
        tangentChartInv_of_mem hφ α haO
      have hmkφ : TangentSpace.mk (TangentPre.ofVec hφ haO) ∈ tangentChartSet φ :=
        (TangentPre.ofVec hφ haO).mem_source
      have hfmk : f (P.levelVal 1 (P.tangentProj (TangentSpace.mk (TangentPre.ofVec hφ haO)))) ∈
          ψ.source := by
        change f (φ.symm (φ.model.E.toBase 1 a.1)) ∈ ψ.source
        obtain ⟨y, hy, hyeq⟩ := hfst
        rw [← hyeq, φ.symm_apply_apply hy.1]; exact hy.2
      change _ = tangentChartMap hψ (tangentMap hf ((tangentChart hφ α).symm a))
      rw [hmk, tangentChartMap_tangentMap hf hφ hψ hmkφ hfmk, tangentChartMap_mk_ofVec hφ haO]
    have hA := vertRep_mem_image (hφ := hφ) hα hss hso hαs hw
    have h3 : retractTangentMap (tangentChart hφ α).model.E (tangentChart hφ α).model.C
        (retractTangent φ.model.E φ.model.C (φ '' s))
        (tangentChart hψ (tangentMap hf α) ∘ tangentMap hf ∘ (tangentChart hφ α).symm)
        (vertRep hφ α w) =
      retractTangentMap φ.model.E.tangent (φ.model.E.tangentSet φ.model.C)
        (retractTangent φ.model.E φ.model.C (φ '' s))
        (retractTangentMap φ.model.E φ.model.C (φ '' s) (ψ ∘ f ∘ φ.symm)) (vertRep hφ α w) :=
      (retractTangentMap_congr hG hO.tangentSet heq hA).symm
    rw [hS, h3]
    have ha : φ.model.E.tangent.toBase 1 (vertRep hφ α w).1 ∈
        retractTangent φ.model.E φ.model.C (φ '' s) := by
      rw [toBase_vertRep_fst hα hαφ', ← himg]; exact ⟨α, hαs, rfl⟩
    have hv : (((φ.model.E.tangent.toBase 1 (vertRep hφ α w).1).1, (tangentChartMap hφ w).2) :
        φ.model.E.tangent 0) ∈ retractTangent φ.model.E φ.model.C (φ '' s) := by
      rw [toBase_vertRep_fst hα hαφ', vertRep_snd_eq hαφ' hw, ← himg]
      refine ⟨w, ?_, rfl⟩
      change P.levelVal 1 (P.tangentProj w) ∈ s; rw [hw]; exact hαs
    refine ((retractTangentMap_tangent_vert hF hO ψ.model.isScRetract ha hv).2).trans ?_
    have hfw : f (P.levelVal 1 (P.tangentProj w)) ∈ ψ.source := by rw [hw]; exact hfψ
    rw [toBase_vertRep_fst hα hαφ', vertRep_snd_eq hαφ' hw,
      ← tangentChartMap_tangentMap hf hφ hψ hwφ hfw]
    rfl

end Vert

end MPolyfold

end Polyfold
