import Polyfold.Chapter4.ScFormsNatural2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4, p. 197
(2017 pp. 149–150; preprint: before Definition 4.27): the exterior derivative
`d : Ωᵏ(X) → Ωᵏ⁺¹(X¹)` on an M-polyfold `X` (gap G.39).  Applied to the lift `Xⁱ` it is the
book's `Ωᵏ(Xⁱ) → Ωᵏ⁺¹(Xⁱ⁺¹)`.

# The exterior derivative on an M-polyfold

## What is proved

* `chartD hφ ω = d_r(ω_φ)`, the local exterior derivative of the representative `ω_φ` on
  `⊕ₖ TO`, with the retraction `chartRetraction φ`.
* `chartD_transition`: `d(ω_ψ) ∘ ⊕_{k+1} T(ψ ∘ φ⁻¹)¹ = d(ω_φ)` on the overlap, from the naturality
  of `ScFormsNatural2021` and `chartForm_transition`.
* `extD ω`: at `x ∈ X²`, the alternating map `d(ω_φ)(φ(x), Tφ¹ ·)` on `T_x(X¹)`, for one chart
  chosen at `x`; `extD_apply`: the same formula holds in every chart of `X` around `x`.
* `extD_mem_scForms`: `dω ∈ Ωᵏ⁺¹(X¹)` for `ω ∈ Ωᵏ(X)`; its representative in the level chart `φ¹`
  is `d(ω_φ)` (`chartForm_extD`).
* `extD_add`, `extD_smul`, `extDₗ`: `d` is linear.

## Relation to the book

The book defines `dω` by the invariant formula with vector fields; here `d` is the local formula
in charts.  On a normed space the two agree (`extDeriv_eq_invariantFormula` in
`ScExteriorDerivative2021`, with the sign `(-1)^{ℓ+j+1}` for the text's bracket); the sc version
of that identity is not formalized.  Domain and target are the book's: `ω` an sc-form on `X`,
`dω` an sc-form on `X¹`.
-/

open Set Function

noncomputable section

namespace Polyfold

/-! ### Linearity of the local exterior derivative -/

section Linear

variable {E F : ScBanach} {U : Set (E 0)} {k : ℕ}

/-- The chosen derivative is additive: `D(f + g)(x) = Df(x) + Dg(x)` on `U₁`. -/
theorem scDeriv_add (hU : IsScDomain E U) {f g : E 0 → F 0} (hf : IsSc1 U f) (hg : IsSc1 U g)
    (hfg : IsSc1 U fun z => f z + g z) {x : E 1} (hx : x ∈ E.lvlSet U 1) :
    scDeriv U (fun z => f z + g z) x = scDeriv U f x + scDeriv U g x :=
  hfg.scDeriv_eq_of_hasFDerivWithinAt hx (hU.uniqueDiffWithinAt 1 x hx) (by
    rw [ContinuousLinearMap.add_comp]
    exact (hf.isSc1With_scDeriv.hasFDerivWithinAt x hx).add
      (hg.isSc1With_scDeriv.hasFDerivWithinAt x hx))

/-- The chosen derivative of a real function is homogeneous: `D(c f)(x) = c Df(x)` on `U₁`. -/
theorem scDeriv_const_mul (hU : IsScDomain E U) {f : E 0 → (ScBanach.const ℝ) 0}
    (hf : IsSc1 U f) (c : ℝ) (hcf : IsSc1 (F := ScBanach.const ℝ) U fun z => c * f z)
    {x : E 1} (hx : x ∈ E.lvlSet U 1) :
    scDeriv (F := ScBanach.const ℝ) U (fun z => c * f z) x = c • scDeriv U f x :=
  hcf.scDeriv_eq_of_hasFDerivWithinAt hx (hU.uniqueDiffWithinAt 1 x hx) (by
    rw [ContinuousLinearMap.smul_comp]
    exact (hf.isSc1With_scDeriv.hasFDerivWithinAt x hx).const_mul c)

/-- `d(Ω + Ω') = dΩ + dΩ'`. -/
theorem ambientD_add (hU : IsScDomain (E.whitney k) (E.whitneySet k U))
    {Ω Ω' : (E.whitney k) 0 → ℝ} (hΩ : IsSc1 (F := ScBanach.const ℝ) (E.whitneySet k U) Ω)
    (hΩ' : IsSc1 (F := ScBanach.const ℝ) (E.whitneySet k U) Ω')
    (hΩΩ' : IsSc1 (F := ScBanach.const ℝ) (E.whitneySet k U) fun p => Ω p + Ω' p)
    {q : (E.shift.whitney (k + 1)) 0} (hq : q ∈ E.shift.whitneySet (k + 1) (E.lvlSet U 1)) :
    ambientD U (fun p => Ω p + Ω' p) q = ambientD U Ω q + ambientD U Ω' q := by
  have hp : ∀ j : Fin (k + 1),
      ((q.1, E.fiberPackL 1 k (j.removeNth (ScBanach.whitneyVec q))) : (E.whitney k) 1) ∈
        (E.whitney k).lvlSet (E.whitneySet k U) 1 := fun _ =>
    mem_whitneySet_lvl_one.2 (ScBanach.mem_whitneySet.1 hq)
  rw [ambientD_apply, ambientD_apply, ambientD_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [scDeriv_add hU hΩ hΩ' hΩΩ' (hp j), ← mul_add]
  rfl

/-- `d(c Ω) = c dΩ`. -/
theorem ambientD_const_mul (hU : IsScDomain (E.whitney k) (E.whitneySet k U))
    {Ω : (E.whitney k) 0 → ℝ} (hΩ : IsSc1 (F := ScBanach.const ℝ) (E.whitneySet k U) Ω) (c : ℝ)
    (hcΩ : IsSc1 (F := ScBanach.const ℝ) (E.whitneySet k U) fun p => c * Ω p)
    {q : (E.shift.whitney (k + 1)) 0} (hq : q ∈ E.shift.whitneySet (k + 1) (E.lvlSet U 1)) :
    ambientD U (fun p => c * Ω p) q = c * ambientD U Ω q := by
  have hp : ∀ j : Fin (k + 1),
      ((q.1, E.fiberPackL 1 k (j.removeNth (ScBanach.whitneyVec q))) : (E.whitney k) 1) ∈
        (E.whitney k).lvlSet (E.whitneySet k U) 1 := fun _ =>
    mem_whitneySet_lvl_one.2 (ScBanach.mem_whitneySet.1 hq)
  rw [ambientD_apply, ambientD_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [scDeriv_const_mul hU hΩ c hcΩ (hp j), mul_left_comm]
  rfl

variable {C : Set (E 0)}

/-- `d_r(ω + ω') = d_r ω + d_r ω'` for sc-forms on a retract. -/
theorem retractD_add (R : ScRetraction E C) {ω ω' : (E.whitney k) 0 → ℝ}
    (hω : IsRetractScForm E C R.retract k ω) (hω' : IsRetractScForm E C R.retract k ω')
    {q : (E.shift.whitney (k + 1)) 0} (hq : q ∈ E.shift.whitneySet (k + 1) (E.lvlSet R.U 1)) :
    retractD R (fun p => ω p + ω' p) q = retractD R ω q + retractD R ω' q := by
  have hS := (R.relOpen.whitneySet k).isScDomain
  have h1 := (hω.isAmbientScForm_comp R).isScSmooth
  have h2 := (hω'.isAmbientScForm_comp R).isScSmooth
  exact ambientD_add hS (h1 1).1 (h2 1).1 (IsSck.add hS (h1 1) (h2 1)).1 hq

/-- `d_r(c ω) = c d_r ω` for sc-forms on a retract. -/
theorem retractD_const_mul (R : ScRetraction E C) {ω : (E.whitney k) 0 → ℝ}
    (hω : IsRetractScForm E C R.retract k ω) (c : ℝ)
    {q : (E.shift.whitney (k + 1)) 0} (hq : q ∈ E.shift.whitneySet (k + 1) (E.lvlSet R.U 1)) :
    retractD R (fun p => c * ω p) q = c * retractD R ω q := by
  have hS := (R.relOpen.whitneySet k).isScDomain
  have h1 := (hω.isAmbientScForm_comp R).isScSmooth
  exact ambientD_const_mul hS (h1 1).1 c (IsSck.real_const_mul hS (h1 1) c).1 hq

end Linear

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {φ ψ : MChart X} {k : ℕ}

/-! ### Chart change of tangent vectors -/

section Tangent

variable (hφ : P.IsChart φ) (hψ : P.IsChart ψ)

/-- `Tφ` maps `TV ∩ TV'` into `T(φ(V ∩ V'))`. -/
lemma tangentChartMap_mem_overlap {α : P.TangentSpace} (hα : α ∈ tangentChartSet φ)
    (hα' : α ∈ tangentChartSet ψ) :
    tangentChartMap hφ α ∈ retractTangent φ.model.E φ.model.C (φ.overlap ψ) := by
  refine (TangentPre.mem_retractTangent_image_iff inter_subset_left
    (φ.isOpen_source.inter ψ.isOpen_source) ?_).2 (tangentChartMap_mem hφ hα)
  change φ.model.E.toBase 1 (tangentChartMap hφ α).1 ∈ φ.overlap ψ
  rw [tangentChartMap_fst hφ hα, P.toBase_levelLift hφ hα (levelVal_mem _)]
  exact ⟨_, ⟨hα, hα'⟩, rfl⟩

/-- **Chart change of a tangent vector**: `Tψ(α) = T(ψ ∘ φ⁻¹)(Tφ(α))` on `TV ∩ TV'`. -/
lemma tangentChartMap_eq_transition {α : P.TangentSpace} (hα : α ∈ tangentChartSet φ)
    (hα' : α ∈ tangentChartSet ψ) :
    tangentChartMap hψ α = retractTangentMap φ.model.E φ.model.C (φ.overlap ψ) (φ.transition ψ)
      (tangentChartMap hφ α) := by
  conv_lhs => rw [← mk_ofVec_tangentChartMap hφ hα]
  exact tangentChartMap_mk_ofVec_of_mem hφ hψ _ (tangentChartMap_mem_overlap hφ hα hα')

/-- The tangent map of the transition of two level charts is the tangent map of the level-`1`
transition map, `T(ψ¹ ∘ (φ¹)⁻¹) = T((ψ ∘ φ⁻¹)¹)` on `T(φ(V ∩ V')¹)`. -/
lemma retractTangentMap_levelChart_transition (x₀ y₀ : P.Level 1)
    {a : φ.model.E.shift.tangent 0}
    (ha : a ∈ retractTangent φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
      (φ.model.E.lvlSet (φ.overlap ψ) 1)) :
    retractTangentMap (levelChart hφ x₀).model.E (levelChart hφ x₀).model.C
        ((levelChart hφ x₀).overlap (levelChart hψ y₀))
        ((levelChart hφ x₀).transition (levelChart hψ y₀)) a =
      retractTangentMap φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
        (φ.model.E.lvlSet (φ.overlap ψ) 1) (levelMap (φ.transition ψ) 1) a := by
  rw [levelChart_overlap hφ x₀ hψ y₀]
  exact (retractTangentMap_congr ((hφ.compatible hψ (P := P)).1.shift (φ.isScRetract_overlap ψ))
    (φ.isScRetract_overlap ψ).shift (fun z hz =>
      (levelChart_transition hφ x₀ hψ y₀ (φ.overlap_subset ψ hz)).symm) ha).symm

end Tangent

/-! ### The local exterior derivative in a chart -/

/-- **The exterior derivative in a chart**: `d(ω_φ) = d_r ω_φ : ⊕_{k+1} T(O¹) → ℝ`, the local
exterior derivative (`retractD`) of the local representative `ω_φ` (`chartForm`). -/
def chartD (hφ : P.IsChart φ) (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    (φ.model.E.shift.whitney (k + 1)) 0 → ℝ :=
  retractD (chartRetraction φ) (chartForm hφ ω)

variable (hφ : P.IsChart φ)

/-- `d(ω_φ)` is an sc-differential `(k + 1)`-form on the local model `(O¹, C¹, E¹)`. -/
theorem IsScForm.chartD {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hω : P.IsScForm k ω) :
    IsRetractScForm φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
      (φ.model.E.lvlSet φ.model.O 1) (k + 1) (chartD hφ ω) := by
  have h := hω.isRetractScForm hφ
  rw [← chartRetraction_retract φ] at h ⊢
  exact h.retractD _

/-- **Chart independence of the local exterior derivative** (2021 p. 197): on
`⊕_{k+1} T(φ(V ∩ V')¹)`, `d(ω_ψ) ∘ ⊕_{k+1} T(ψ ∘ φ⁻¹)¹ = d(ω_φ)`. -/
theorem chartD_transition (hψ : P.IsChart ψ)
    {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} (hω : P.IsScForm k ω)
    {q : (φ.model.E.shift.whitney (k + 1)) 0}
    (hq : q ∈ retractWhitney φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
      (φ.model.E.lvlSet (φ.overlap ψ) 1) (k + 1)) :
    chartD hψ ω (retractWhitneyMap φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
      (φ.model.E.lvlSet (φ.overlap ψ) 1) (levelMap (φ.transition ψ) 1) (k + 1) q) =
      chartD hφ ω q := by
  obtain ⟨R₁, hR₁⟩ := φ.isScRetract_overlap ψ
  obtain ⟨R₂, hR₂⟩ := ψ.isScRetract_overlap φ
  have hf := (hφ.compatible hψ (P := P)).1
  have hωφ := hω.isRetractScForm hφ
  have hωψ := hω.isRetractScForm hψ
  have hq' := ((hf.shift (φ.isScRetract_overlap ψ)).whitney (φ.isScRetract_overlap ψ).shift
    (ψ.isScRetract_overlap φ).shift (k + 1)).mapsTo hq
  have h4 := retractD_eq_of_subset (chartRetraction ψ) (chartRetraction_retract ψ) R₂ hR₂
    (ψ.overlap_subset φ) hωψ hq'
  have h3 := retractD_comp_retractWhitneyMap R₁ hR₁ R₂ hR₂ hf
    (hωψ.mono ψ.model.isScRetract (ψ.isScRetract_overlap φ) (ψ.overlap_subset φ)) hq
  have h1 := retractD_eq_of_subset (chartRetraction φ) (chartRetraction_retract φ) R₁ hR₁
    (φ.overlap_subset ψ) hωφ hq
  have hω₁ : IsRetractScForm φ.model.E φ.model.C R₁.retract k (chartForm hφ ω) := by
    rw [hR₁]; exact hωφ.mono φ.model.isScRetract (φ.isScRetract_overlap ψ) (φ.overlap_subset ψ)
  have h2 : retractD R₁ (chartForm hψ ω ∘
      retractWhitneyMap φ.model.E φ.model.C (φ.overlap ψ) (φ.transition ψ) k) q =
      retractD R₁ (chartForm hφ ω) q := by
    refine retractD_congr R₁ hω₁ (fun p hp => ?_) (R₁.mem_whitneySet_of_mem (hR₁ ▸ hq))
    rw [hR₁] at hp
    exact (chartForm_transition hφ hψ ω hp).symm
  unfold chartD
  rw [← h4, ← h3, h2, h1]

/-! ### The exterior derivative on `X` -/

section Global

variable {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}

/-- The chart `φ_x` of `X` around the base point of `x ∈ X²` used to define `dω(x)`. -/
abbrev dChart (x : P.shift.Level 1) : MChart X := P.someChart (liftBase x)

lemma dChart_isChart (x : P.shift.Level 1) : P.IsChart (dChart x) := P.someChart_isChart _

/-- Its level chart `φ_x¹`, a chart of `X¹` around `x`. -/
abbrev dLevelChart (x : P.shift.Level 1) : MChart (P.Level 1) :=
  levelChart (dChart_isChart x) (P.shift.levelVal 1 x)

lemma dLevelChart_isChart (x : P.shift.Level 1) : P.shift.IsChart (dLevelChart x) :=
  P.shift_isChart _ _

lemma mem_dLevelChart_source (x : P.shift.Level 1) :
    P.shift.levelVal 1 x ∈ (dLevelChart x).source :=
  P.mem_someChart_source _

/-- The alternating map on `(E¹)^{k+1}` which agrees with `d(ω_φ)(φ(x), ·)` on
`(T_{φ(x)}O¹)^{k+1}`, in the chart `φ = φ_x` (a choice). -/
def dAlt (hω : P.IsScForm k ω) (x : P.shift.Level 1) :
    (dChart x).model.E.shift 0 [⋀^Fin (k + 1)]→ₗ[ℝ] ℝ :=
  ((hω.chartD (dChart_isChart x)).alternating (levelLift (dLevelChart x) 1 (P.shift.levelVal 1 x))
    (levelLift_mem_lvlSet_one (dLevelChart_isChart x) (mem_dLevelChart_source x))).choose

lemma dAlt_spec (hω : P.IsScForm k ω) (x : P.shift.Level 1)
    {v : Fin (k + 1) → (dChart x).model.E.shift 0}
    (hv : ∀ i, v i ∈ tangentFiberModel (dLevelChart_isChart x) (mem_dLevelChart_source x)) :
    chartD (dChart_isChart x) ω
      (ScBanach.whitneyMk (levelLift (dLevelChart x) 1 (P.shift.levelVal 1 x)) v) = dAlt hω x v :=
  ((hω.chartD (dChart_isChart x)).alternating (levelLift (dLevelChart x) 1 (P.shift.levelVal 1 x))
    (levelLift_mem_lvlSet_one (dLevelChart_isChart x) (mem_dLevelChart_source x))).choose_spec v hv

open scoped Classical in
/-- **2021 p. 197 (the exterior derivative)** (2017 pp. 149–150; preprint: before Definition 4.27):
for an sc-differential `k`-form `ω` on `X`, `dω` is the family of alternating `(k + 1)`-linear maps
on the tangent spaces `T_x(X¹)`, `x ∈ X²`, which in a chart `φ` around `x` is `d(ω_φ)(φ(x), ·)` read
through `Tφ¹` — the local exterior derivative `d_r ω_φ` of `ScExteriorDerivative2021`. It does not
depend on the chart (`extD_apply`). (`0` if `ω` is not an sc-form.) -/
@[irreducible] def extD (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    ∀ x : P.shift.Level 1, P.shift.tangentFiber x [⋀^Fin (k + 1)]→ₗ[ℝ] ℝ := fun x =>
  if hω : P.IsScForm k ω then
    (dAlt hω x).compLinearMap
      ((tangentFiberModel (dLevelChart_isChart x) (mem_dLevelChart_source x)).subtype ∘ₗ
        (tangentFiberLinearEquiv (dLevelChart_isChart x) (mem_dLevelChart_source x)).toLinearMap)
  else 0

lemma extD_apply_dChart (hω : P.IsScForm k ω) (x : P.shift.Level 1)
    (α : Fin (k + 1) → P.shift.tangentFiber x) :
    extD ω x α = chartD (dChart_isChart x) ω
      (ScBanach.whitneyMk (levelLift (dLevelChart x) 1 (P.shift.levelVal 1 x))
        fun i => (tangentChartMap (dLevelChart_isChart x) (α i)).2) := by
  rw [extD, dif_pos hω, AlternatingMap.compLinearMap_apply]
  exact (dAlt_spec hω x fun i =>
    tangentChartMap_snd_mem_model (dLevelChart_isChart x) (mem_dLevelChart_source x) (α i).2).symm

/-- **The exterior derivative in an arbitrary chart**: for a chart `φ` of `X` around the base
point of `x ∈ X²` and `αᵢ ∈ T_x(X¹)` with `Tφ¹(αᵢ) = (φ(x), hᵢ)`,
`dω(x)(α₀, …, α_k) = d(ω_φ)(φ(x), h₀, …, h_k)`. -/
theorem extD_apply (hω : P.IsScForm k ω) (y₀ : P.Level 1) {x : P.shift.Level 1}
    (hx : P.shift.levelVal 1 x ∈ (levelChart hφ y₀).source)
    (α : Fin (k + 1) → P.shift.tangentFiber x) :
    extD ω x α = chartD hφ ω
      (ScBanach.whitneyMk (levelLift (levelChart hφ y₀) 1 (P.shift.levelVal 1 x))
        fun i => (tangentChartMap (P.shift_isChart hφ y₀) (α i)).2) := by
  have hφ₀ := dChart_isChart x
  have hχ := P.shift_isChart hφ y₀
  have hχ₀ := dLevelChart_isChart x
  have hx₀ := mem_dLevelChart_source x
  rw [extD_apply_dChart hω x α]
  have hα : ∀ i, (α i : P.shift.TangentSpace) ∈ tangentChartSet (levelChart hφ y₀) := fun i =>
    mem_tangentChartSet_of_mem_fiber hx (α i).2
  have hα₀ : ∀ i, (α i : P.shift.TangentSpace) ∈ tangentChartSet (dLevelChart x) := fun i =>
    mem_tangentChartSet_of_mem_fiber hx₀ (α i).2
  set z := levelLift (levelChart hφ y₀) 1 (P.shift.levelVal 1 x) with hz
  have hfst : ∀ i, ((z, (tangentChartMap hχ (α i)).2) : φ.model.E.shift.tangent 0) =
      tangentChartMap hχ (α i) := fun i =>
    Prod.ext (tangentChartMap_fst_of_mem_fiber hχ hx (α i).2).symm rfl
  have hmem : ∀ i, ((z, (tangentChartMap hχ (α i)).2) : φ.model.E.shift.tangent 0) ∈
      retractTangent φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
        (φ.model.E.lvlSet (φ.overlap (dChart x)) 1) := fun i => by
    rw [hfst i, ← levelChart_overlap hφ y₀ hφ₀ (P.shift.levelVal 1 x)]
    exact tangentChartMap_mem_overlap hχ (hα i) (hα₀ i)
  have hq : ScBanach.whitneyMk z (fun i => (tangentChartMap hχ (α i)).2) ∈
      retractWhitney φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
        (φ.model.E.lvlSet (φ.overlap (dChart x)) 1) (k + 1) :=
    mem_retractWhitney_mk.2 ⟨retractTangent_fst_mem (φ.isScRetract_overlap _).shift (hmem 0), hmem⟩
  have h1 : levelMap (E := φ.model.E.shift) (F := (dLevelChart x).model.E)
      (levelMap (φ.transition (dChart x)) 1) 1 z =
      levelLift (dLevelChart x) 1 (P.shift.levelVal 1 x) := by
    refine levelMap_eq_of_toBase_eq ?_
    have e1 := P.shift.toBase_levelLift hχ₀ hx₀ (levelVal_mem x)
    have e2 := P.shift.toBase_levelLift hχ hx (levelVal_mem x)
    refine e1.trans ((levelMap_transition_levelLift hφ hφ₀ hx hx₀).symm.trans ?_)
    exact congrArg (levelMap (φ.transition (dChart x)) 1) e2.symm
  have h2 : ∀ i, (retractTangentMap φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
      (φ.model.E.lvlSet (φ.overlap (dChart x)) 1) (levelMap (φ.transition (dChart x)) 1)
      (z, (tangentChartMap hχ (α i)).2)).2 = (tangentChartMap hχ₀ (α i)).2 := fun i => by
    have hB := retractTangentMap_levelChart_transition hφ hφ₀ y₀ (P.shift.levelVal 1 x) (hmem i)
    refine (congrArg Prod.snd hB.symm).trans ?_
    rw [hfst i, ← tangentChartMap_eq_transition hχ hχ₀ (hα i) (hα₀ i)]
  have h3 : retractWhitneyMap φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
      (φ.model.E.lvlSet (φ.overlap (dChart x)) 1) (levelMap (φ.transition (dChart x)) 1) (k + 1)
      (ScBanach.whitneyMk z fun i => (tangentChartMap hχ (α i)).2) =
      ScBanach.whitneyMk (levelLift (dLevelChart x) 1 (P.shift.levelVal 1 x))
        fun i => (tangentChartMap hχ₀ (α i)).2 := by
    have hv : ScBanach.whitneyVec (E := φ.model.E.shift)
        (ScBanach.whitneyMk z fun i => (tangentChartMap hχ (α i)).2) =
        fun i => (tangentChartMap hχ (α i)).2 :=
      ScBanach.whitneyVec_mk (E := φ.model.E.shift) _ _
    have h0 : (ScBanach.whitneyMk (E := φ.model.E.shift) z
        fun i => (tangentChartMap hχ (α i)).2).1 = z := rfl
    unfold retractWhitneyMap
    rw [h0, h1, hv]
    exact congrArg _ (funext h2)
  exact (congrArg (chartD hφ₀ ω) h3.symm).trans (chartD_transition hφ hφ₀ hω hq)

/-- **The local representative of `dω`**: in the level chart `φ¹` of `X¹`,
`(dω)_{φ¹} = d(ω_φ)` on `⊕_{k+1} T(O¹)`. -/
theorem chartForm_extD (hω : P.IsScForm k ω) (y₀ : P.Level 1)
    {q : (φ.model.E.shift.whitney (k + 1)) 0}
    (hq : q ∈ retractWhitney φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
      (φ.model.E.lvlSet φ.model.O 1) (k + 1)) :
    chartForm (P.shift_isChart hφ y₀) (extD ω) q = chartD hφ ω q := by
  have hχ := P.shift_isChart hφ y₀
  have hq' : q ∈ retractWhitney (levelChart hφ y₀).model.E (levelChart hφ y₀).model.C
      (levelChart hφ y₀).model.O (k + 1) := hq
  conv_lhs => unfold chartForm
  split_ifs with h
  swap; · exact absurd hq' h
  rw [extD_apply hφ hω y₀ (chartPoint_mem_source hχ h.1)]
  have e1 : levelLift (levelChart hφ y₀) 1 (P.shift.levelVal 1 (chartPoint hχ h.1)) = q.1 :=
    levelLift_chartPoint hχ h.1
  have e2 : ∀ i, (tangentChartMap hχ (TangentSpace.mk (TangentPre.ofVec hχ (h.2 i)))).2 =
      ScBanach.whitneyVec q i := fun i =>
    congrArg Prod.snd (tangentChartMap_mk_ofVec hχ (h.2 i))
  exact congrArg (chartD hφ ω)
    ((congrArg₂ (ScBanach.whitneyMk (E := φ.model.E.shift)) e1 (funext e2)).trans
      (whitneyMk_fst_vec q))

/-- **2021 p. 197: `d` maps `Ωᵏ(X)` to `Ωᵏ⁺¹(X¹)`** (2017 p. 150; preprint: before Definition
4.27; gap G.39): the exterior derivative of an sc-differential `k`-form on `X` is an sc-differential
`(k + 1)`-form on `X¹`.  Its local representatives in the level charts, which cover `X²`, are the
local exterior derivatives `d(ω_φ)` (`chartForm_extD`), sc-smooth by
`IsRetractScForm.retractD`. -/
theorem extD_mem_scForms (hω : ω ∈ P.scForms k) : extD ω ∈ P.shift.scForms (k + 1) := by
  refine isScForm_of_cover _ fun x =>
    ⟨dLevelChart x, dLevelChart_isChart x, mem_dLevelChart_source x, ?_⟩
  exact ((mem_scForms.1 hω).chartD (dChart_isChart x)).isScSmooth.congr fun q hq =>
    (chartForm_extD (dChart_isChart x) hω _ hq).symm

/-! ### Linearity of `d` -/

/-- `(φ¹(x), Tφ¹(α₁), …, Tφ¹(α_n)) ∈ ⊕_n T(O¹)` for `αᵢ ∈ T_x(X¹)`. -/
lemma whitneyMk_tangentChartMap_mem (y₀ : P.Level 1) {n : ℕ} {x : P.shift.Level 1}
    (hx : P.shift.levelVal 1 x ∈ (levelChart hφ y₀).source)
    (α : Fin n → P.shift.tangentFiber x) :
    ScBanach.whitneyMk (E := φ.model.E.shift)
        (levelLift (levelChart hφ y₀) 1 (P.shift.levelVal 1 x))
        (fun i => (tangentChartMap (P.shift_isChart hφ y₀) (α i)).2) ∈
      retractWhitney φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
        (φ.model.E.lvlSet φ.model.O 1) n := by
  have hχ := P.shift_isChart hφ y₀
  refine mem_retractWhitney_mk.2 ⟨levelLift_mem_lvlSet_one hχ hx, fun i => ?_⟩
  have e : ((levelLift (levelChart hφ y₀) 1 (P.shift.levelVal 1 x),
      (tangentChartMap hχ (α i)).2) : φ.model.E.shift.tangent 0) = tangentChartMap hχ (α i) :=
    Prod.ext (tangentChartMap_fst_of_mem_fiber hχ hx (α i).2).symm rfl
  rw [e]
  exact tangentChartMap_mem hχ (mem_tangentChartSet_of_mem_fiber hx (α i).2)

lemma chartD_add {ω τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hω : P.IsScForm k ω) (hτ : P.IsScForm k τ) {q : (φ.model.E.shift.whitney (k + 1)) 0}
    (hq : q ∈ retractWhitney φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
      (φ.model.E.lvlSet φ.model.O 1) (k + 1)) :
    chartD hφ (ω + τ) q = chartD hφ ω q + chartD hφ τ q := by
  have h1 := hω.isRetractScForm hφ
  have h2 := hτ.isRetractScForm hφ
  rw [← chartRetraction_retract φ] at h1 h2 hq
  unfold chartD
  rw [show chartForm hφ (ω + τ) = fun p => chartForm hφ ω p + chartForm hφ τ p from
    funext (chartForm_add hφ ω τ)]
  exact retractD_add _ h1 h2 ((chartRetraction φ).mem_whitneySet_of_mem hq)

lemma chartD_smul (c : ℝ) {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hω : P.IsScForm k ω) {q : (φ.model.E.shift.whitney (k + 1)) 0}
    (hq : q ∈ retractWhitney φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
      (φ.model.E.lvlSet φ.model.O 1) (k + 1)) :
    chartD hφ (c • ω) q = c * chartD hφ ω q := by
  have h1 := hω.isRetractScForm hφ
  rw [← chartRetraction_retract φ] at h1 hq
  unfold chartD
  rw [show chartForm hφ (c • ω) = fun p => c * chartForm hφ ω p from
    funext (chartForm_smul hφ c ω)]
  exact retractD_const_mul _ h1 c ((chartRetraction φ).mem_whitneySet_of_mem hq)

/-- `d(ω + τ) = dω + dτ`. -/
theorem extD_add {ω τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hω : P.IsScForm k ω) (hτ : P.IsScForm k τ) : extD (ω + τ) = extD ω + extD τ := by
  have hωτ : P.IsScForm k (ω + τ) := (P.scForms k).add_mem hω hτ
  funext x
  ext α
  rw [Pi.add_apply, AlternatingMap.add_apply, extD_apply_dChart hωτ, extD_apply_dChart hω,
    extD_apply_dChart hτ]
  exact chartD_add (dChart_isChart x) hω hτ
    (whitneyMk_tangentChartMap_mem (dChart_isChart x) _ (mem_dLevelChart_source x) α)

/-- `d(c ω) = c dω`. -/
theorem extD_smul (c : ℝ) {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hω : P.IsScForm k ω) : extD (c • ω) = c • extD ω := by
  have hcω : P.IsScForm k (c • ω) := (P.scForms k).smul_mem c hω
  funext x
  ext α
  rw [Pi.smul_apply, AlternatingMap.smul_apply, extD_apply_dChart hcω, extD_apply_dChart hω,
    smul_eq_mul]
  exact chartD_smul (dChart_isChart x) c hω
    (whitneyMk_tangentChartMap_mem (dChart_isChart x) _ (mem_dLevelChart_source x) α)

variable (P k) in
/-- **The exterior derivative `d : Ωᵏ(X) → Ωᵏ⁺¹(X¹)` as a linear operator** (2021 p. 197:
"This defines the exterior derivative as a linear operator"; 2017 p. 150; preprint: before
Definition 4.27),
with `X¹` the M-polyfold `P.shift`; applied to `X^i` it is `Ωᵏ(Xⁱ) → Ωᵏ⁺¹(Xⁱ⁺¹)`. -/
def extDₗ : P.scForms k →ₗ[ℝ] P.shift.scForms (k + 1) where
  toFun ω := ⟨extD ω.1, extD_mem_scForms ω.2⟩
  map_add' ω τ := Subtype.ext (extD_add ω.2 τ.2)
  map_smul' c ω := Subtype.ext (extD_smul c ω.2)

@[simp] lemma coe_extDₗ (ω : P.scForms k) : (extDₗ P k ω : _) = extD ω.1 := rfl

end Global

end MPolyfold

end Polyfold
