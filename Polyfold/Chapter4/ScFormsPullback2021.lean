import Polyfold.Chapter4.ScFormsLower2021
import Polyfold.Chapter2.TangentMapLinear

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4, p. 198
(2017 p. 150 and preprint p. 168, after the Stokes theorem, one sentence): the pull-back `f^*`
of sc-differential forms along an sc-smooth map `f : X → Y` of M-polyfolds, and
`f^* ∘ d_Y = d_X ∘ f^*` (part of gap G.80).  Numbers and pages are the 2021 text's.

# Pull-back of sc-forms along sc-smooth maps

## The text, paraphrased

(p. 198) An sc-smooth `f : X → Y` induces `f^* : Ω*_∞(Y) → Ω*_∞(X)` "in the usual way": for a
representative `ω ∈ Ωᵏ(Yⁱ)`, `f^*ω = ω ∘ (Tf ⊕ ⋯ ⊕ Tf)` on `⊕ₖ T(Xⁱ)`, with `f` raised to the
index `i`.  "The reader can verify" `f^* ∘ d_Y = d_X ∘ f^*`, the limit of the commutative squares
`Ωᵏ(Yⁱ) → Ωᵏ(Xⁱ)`, `Ωᵏ⁺¹(Yⁱ⁺¹) → Ωᵏ⁺¹(Xⁱ⁺¹)`.  (2017 and preprint: only the first sentence.)

## What is formalized

* `tangentFiberMap hf x : T_xX →L[ℝ] T_{f(x)}Y` (`tangentMapCLM`), over the index raise
  `liftLevelOneMap hf : X¹ → Y¹` (sc-smooth: `isScSmoothMap_liftLevelOneMap`).
* `formPullback hf ω`: `(f^*ω)(x)(α₁, …, α_k) = ω(f(x))(Tf α₁, …, Tf α_k)` for any family `ω` of
  alternating forms on the tangent spaces of `Y` (`formPullbackₗ`: linear in `ω`).
* `chartForm_formPullback`: in charts `φ` of `X`, `ψ` of `Y`, `(f^*ω)_φ = ω_ψ ∘ ⊕ₖ T(ψ ∘ f ∘ φ⁻¹)`
  on `⊕ₖ T(φ(V ∩ f⁻¹V'))`; hence **`formPullback_mem_scForms`**: `f^*` maps `Ωᵏ(Y)` to `Ωᵏ(X)`.
* **`extD_formPullback`**: `d(f^*ω) = (f¹)^*(dω)` for `ω ∈ Ωᵏ(Y)`, as forms on `X¹`; in charts
  (`chartD_formPullback`) this is the naturality of the local `d`,
  `retractD_comp_retractWhitneyMap`.
* Functoriality: `formPullback_id`, `formPullback_comp` (`(g ∘ f)^* = f^* ∘ g^*`),
  `formPullback_congr`, and `formLower_formPullback` (`f^*` commutes with the inclusions
  `X¹ → X`, `Y¹ → Y` of the directed system (4.4)).
* On the lifts (`BundledMPolyfold`, `f : ScMap A.P B.P`, `f^i = A.liftMap f i`):
  `formsPullback f k i : Ωᵏ(Yⁱ) → Ωᵏ(Xⁱ)`, commuting with (4.4) (`formsPullback_formsMap`);
  **`formsInftyPullback f k : Ωᵏ_∞(Y) → Ωᵏ_∞(X)`** (the limit map), with
  **`formsInftyD_comp_formsInftyPullback`** (`d ∘ f^* = f^* ∘ d`), `formsInftyPullback_id`,
  `formsInftyPullback_comp` (`ScMap.id`, `ScMap.comp`), and the induced map
  `scDeRhamPullback f k : Hᵏ_sc(Y) → Hᵏ_sc(X)` on the cohomology of Definition 4.4.6.

## The reading

* "Raising the index" is `liftLevelOneMap` on `X¹` and `BundledMPolyfold.liftMap` on `Xⁱ`;
  `Tf` on the fibres is `tangentMapCLM` (2021 Theorem 2.3.16 fibrewise).
* `f^*ω` is defined for every family of alternating forms, so that it applies verbatim to
  `ω ∈ Ωᵏ(Yⁱ)` for every `i`; no hypothesis on `f` beyond sc-smoothness.
-/

open Set Function

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}
  {f : X → Y} {k : ℕ}

/-! ### The map `f¹ : X¹ → Y¹` and `Tf` on the fibres -/

@[simp] lemma levelVal_liftLevelOneMap (hf : P.IsScSmoothMap Q f) (x : P.Level 1) :
    Q.levelVal 1 (liftLevelOneMap hf x) = f (P.levelVal 1 x) := rfl

/-- The index raise `f¹ = liftLevelOneMap hf : X¹ → Y¹` is sc-smooth (`IsScSmoothMap.levelOne`). -/
theorem isScSmoothMap_liftLevelOneMap (hf : P.IsScSmoothMap Q f) :
    P.shift.IsScSmoothMap Q.shift (liftLevelOneMap hf) :=
  IsScSmoothMap.levelOne hf fun _ => rfl

/-- **`Tf : T_xX → T_{f(x)}Y`** on the fibres over `x ∈ X¹`, a continuous linear map
(`tangentMapCLM`, 2021 Theorem 2.3.16). -/
def tangentFiberMap (hf : P.IsScSmoothMap Q f) (x : P.Level 1) :
    P.tangentFiber x →L[ℝ] Q.tangentFiber (liftLevelOneMap hf x) :=
  tangentMapCLM hf rfl

@[simp] lemma coe_tangentFiberMap_apply (hf : P.IsScSmoothMap Q f) {x : P.Level 1}
    (α : P.tangentFiber x) : (tangentFiberMap hf x α : Q.TangentSpace) = tangentMap hf α.1 :=
  tangentMapCLM_apply hf rfl α

/-! ### The pull-back of a family of forms -/

/-- **2021 p. 198: the pull-back `f^*ω`** (2017 p. 150; preprint p. 168: "in the usual way") of a
family of alternating `k`-forms on the tangent spaces of `Y` along an sc-smooth `f : X → Y`:
`(f^*ω)(x)(α₁, …, α_k) = ω(f(x))(Tf α₁, …, Tf α_k)`, `x ∈ X¹`, `αᵢ ∈ T_xX` (the text's
`ω ∘ (Tf ⊕ ⋯ ⊕ Tf)`). -/
def formPullback (hf : P.IsScSmoothMap Q f)
    (ω : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ) :
    ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ := fun x =>
  (ω (liftLevelOneMap hf x)).compLinearMap
    (tangentFiberMap hf x : P.tangentFiber x →ₗ[ℝ] Q.tangentFiber (liftLevelOneMap hf x))

lemma formPullback_apply (hf : P.IsScSmoothMap Q f)
    (ω : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ) (x : P.Level 1)
    (α : Fin k → P.tangentFiber x) :
    formPullback hf ω x α = ω (liftLevelOneMap hf x) fun i => tangentFiberMap hf x (α i) := rfl

/-- `(f^*ω)(x)(α) = ω(y)(β)` whenever `y = f(x)` and `βᵢ = Tf αᵢ` as vectors of `TY`. -/
lemma formPullback_eq (hf : P.IsScSmoothMap Q f)
    (ω : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ) {x : P.Level 1}
    (α : Fin k → P.tangentFiber x) {y : Q.Level 1} (hy : f (P.levelVal 1 x) = Q.levelVal 1 y)
    (β : Fin k → Q.tangentFiber y) (hβ : ∀ i, tangentMap hf (α i).1 = β i) :
    formPullback hf ω x α = ω y β := by
  rw [formPullback_apply]
  exact altFamily_congr ω (level_ext (show Q.levelVal 1 (liftLevelOneMap hf x) = _ from hy)) _ _
    fun i => by
    rw [coe_tangentFiberMap_apply, hβ i]

lemma formPullback_add (hf : P.IsScSmoothMap Q f)
    (ω τ : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ) :
    formPullback hf (ω + τ) = formPullback hf ω + formPullback hf τ := rfl

lemma formPullback_smul (hf : P.IsScSmoothMap Q f) (c : ℝ)
    (ω : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ) :
    formPullback hf (c • ω) = c • formPullback hf ω := rfl

variable (k) in
/-- The pull-back `ω ↦ f^*ω` is linear. -/
def formPullbackₗ (hf : P.IsScSmoothMap Q f) :
    (∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ) →ₗ[ℝ]
      (∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) where
  toFun := formPullback hf
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-! ### The local representative of the pull-back -/

section Chart

variable (hf : P.IsScSmoothMap Q f) {φ : MChart X} {ψ : MChart Y} (hφ : P.IsChart φ)
  (hψ : Q.IsChart ψ)

omit [T2Space X] [ParacompactSpace X] in
/-- A point `q ∈ ⊕ₖ TO` whose base point lies in the open part `φ(s)` lies in `⊕ₖ T(φ(s))`. -/
lemma mem_retractWhitney_image {s : Set X} (hs : s ⊆ φ.source) (hso : IsOpen s)
    {q : (φ.model.E.whitney k) 0} (hq : q ∈ retractWhitney φ.model.E φ.model.C φ.model.O k)
    (hqs : φ.model.E.toBase 1 q.1 ∈ φ '' s) :
    q ∈ retractWhitney φ.model.E φ.model.C (φ '' s) k :=
  ⟨hqs, fun i => (TangentPre.mem_retractTangent_image_iff hs hso hqs).2 (hq.2 i)⟩

include hφ in
/-- The point `(φ(x), Tφ α₁, …, Tφ α_k)` lies in `⊕ₖ T(φ(s))` when `x ∈ s`. -/
lemma whitneyMk_tangentChartMap_mem_image {s : Set X} (hs : s ⊆ φ.source) (hso : IsOpen s)
    {x : P.Level 1} (hx : P.levelVal 1 x ∈ s) (α : Fin k → P.tangentFiber x) :
    ScBanach.whitneyMk (levelLift φ 1 (P.levelVal 1 x)) (fun i => (tangentChartMap hφ (α i)).2) ∈
      retractWhitney φ.model.E φ.model.C (φ '' s) k := by
  refine mem_retractWhitney_image hs hso (mem_retractWhitney_mk.2
    ⟨levelLift_mem_lvlSet_one hφ (hs hx), fun i => ?_⟩) ?_
  · have e : ((levelLift φ 1 (P.levelVal 1 x), (tangentChartMap hφ (α i)).2) :
        φ.model.E.tangent 0) = tangentChartMap hφ (α i) :=
      Prod.ext (tangentChartMap_fst_of_mem_fiber hφ (hs hx) (α i).2).symm rfl
    rw [e]
    exact tangentChartMap_mem hφ (mem_tangentChartSet_of_mem_fiber (hs hx) (α i).2)
  · change φ.model.E.toBase 1 (levelLift φ 1 (P.levelVal 1 x)) ∈ φ '' s
    rw [P.toBase_levelLift hφ (hs hx) (levelVal_mem x)]
    exact ⟨_, hx, rfl⟩

/-- **The local representative of the pull-back**: on `⊕ₖ T(φ(V ∩ f⁻¹(V')))`,
`(f^*ω)_φ = ω_ψ ∘ ⊕ₖ T(ψ ∘ f ∘ φ⁻¹)`. -/
theorem chartForm_formPullback (ω : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ)
    {q : (φ.model.E.whitney k) 0}
    (hq : q ∈ retractWhitney φ.model.E φ.model.C (φ '' TangentPre.fdom φ f ψ) k) :
    chartForm hφ (formPullback hf ω) q =
      chartForm hψ ω (retractWhitneyMap φ.model.E φ.model.C (φ '' TangentPre.fdom φ f ψ)
        (ψ ∘ f ∘ φ.symm) k q) := by
  have hVφ : TangentPre.fdom φ f ψ ⊆ φ.source := inter_subset_left
  have hVo := TangentPre.isOpen_fdom hf φ ψ
  have hO := φ.isScRetract_image hVφ hVo
  have hq' : q ∈ retractWhitney φ.model.E φ.model.C φ.model.O k :=
    retractWhitney_mono φ.model.isScRetract hO (φ.image_subset_model hVφ) hq
  rw [chartForm, dif_pos hq']
  set x := chartPoint hφ hq'.1 with hxdef
  have hxV : P.levelVal 1 x ∈ TangentPre.fdom φ f ψ := by
    obtain ⟨y, hy, hyeq⟩ := (hq.1 : φ.model.E.toBase 1 q.1 ∈ φ '' TangentPre.fdom φ f ψ)
    rw [levelVal_chartPoint, ← hyeq, φ.symm_apply_apply (hVφ hy)]
    exact hy
  have hlift : levelLift φ 1 (P.levelVal 1 x) = q.1 := levelLift_chartPoint hφ hq'.1
  rw [formPullback_apply]
  symm
  refine chartForm_eq hψ ω (x := liftLevelOneMap hf x) hxV.2 _ ?_ fun i => ?_
  · change levelMap (ψ ∘ f ∘ φ.symm) 1 q.1 = _
    rw [← hlift, levelMap_coord_levelLift hxV.1 hφ hψ hxV.2 (levelVal_mem x)
      (hf.mapsTo_levelSet 1 (levelVal_mem x))]
    rfl
  · rw [retractWhitneyMap, ScBanach.whitneyVec_mk, coe_tangentFiberMap_apply]
    have hα : TangentSpace.mk (TangentPre.ofVec hφ (hq'.2 i)) ∈ tangentChartSet (P := P) φ :=
      (TangentPre.ofVec hφ (hq'.2 i)).mem_source
    have hfα : f (P.levelVal 1 (P.tangentProj (TangentSpace.mk (TangentPre.ofVec hφ (hq'.2 i))))) ∈
        ψ.source := hxV.2
    rw [tangentChartMap_tangentMap hf hφ hψ hα hfα, tangentChartMap_mk_ofVec]

/-- The pull-back of an sc-form is sc-smooth in every chart of `X`. -/
theorem isChartScSmooth_formPullback {ω : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hω : ω ∈ Q.scForms k) : IsChartScSmooth hφ (formPullback hf ω) := by
  refine IsScSmoothRetractMap.of_locally (mapsTo_univ _ _) fun q hq => ?_
  obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f (P.levelVal 1 (chartPoint hφ hq.1)))
  have hVφ : TangentPre.fdom φ f ψ ⊆ φ.source := inter_subset_left
  have hVo := TangentPre.isOpen_fdom hf φ ψ
  have hO := φ.isScRetract_image hVφ hVo
  obtain ⟨W, hW, hWeq⟩ := φ.exists_isOpen_image_eq hVφ hVo
  have hqW : φ.model.E.toBase 1 q.1 ∈ φ '' TangentPre.fdom φ f ψ :=
    ⟨_, ⟨chartPoint_mem_source hφ hq.1, hfx⟩, φ.apply_symm_apply hq.1⟩
  refine ⟨{q | φ.model.E.toBase 1 q.1 ∈ W},
    hW.preimage ((φ.model.E.toBase 1).continuous.comp continuous_fst), (hWeq ▸ hqW).2, ?_⟩
  rw [← retractWhitney_inter_isOpen φ.model.isScRetract hW, ← hWeq]
  have ht := (TangentPre.isScSmoothRetractMap_coord hf hφ hψ subset_rfl hVo).whitney hO
    ψ.model.isScRetract k
  exact ((hω hψ).comp ht (ψ.model.isScRetract.whitney k)).congr fun q hq =>
    (chartForm_formPullback hf hφ hψ ω hq).symm

end Chart

/-- **2021 p. 198: the pull-back of an sc-form is an sc-form** (2017 p. 150; preprint p. 168):
for `f : X → Y` sc-smooth and `ω ∈ Ωᵏ(Y)`, `f^*ω ∈ Ωᵏ(X)` (the text's `ω ∘ (Tf ⊕ ⋯ ⊕ Tf)`). -/
theorem formPullback_mem_scForms (hf : P.IsScSmoothMap Q f)
    {ω : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ} (hω : ω ∈ Q.scForms k) :
    formPullback hf ω ∈ P.scForms k :=
  fun _ hφ => isChartScSmooth_formPullback hf hφ hω

/-! ### Functoriality and the inclusion `X¹ → X` -/

/-- **`id^* = id`**. -/
theorem formPullback_id (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ) :
    formPullback (isScSmoothMap_id (P := P)) ω = ω := by
  funext x
  ext α
  refine formPullback_eq _ ω α rfl α fun i => ?_
  rw [tangentMap_id]
  rfl

/-- **`(g ∘ f)^* = f^* ∘ g^*`** (the chain rule `T(g ∘ f) = Tg ∘ Tf`). -/
theorem formPullback_comp {g : Y → Z} (hg : Q.IsScSmoothMap S g) (hf : P.IsScSmoothMap Q f)
    (ω : ∀ z : S.Level 1, S.tangentFiber z [⋀^Fin k]→ₗ[ℝ] ℝ) :
    formPullback (hg.comp hf) ω = formPullback hf (formPullback hg ω) := by
  funext x
  ext α
  rw [formPullback_apply hf, formPullback_apply hg]
  refine formPullback_eq _ ω α rfl _ fun i => ?_
  rw [tangentMap_comp hg hf, Function.comp_apply, coe_tangentFiberMap_apply,
    coe_tangentFiberMap_apply]

/-- **The pull-back commutes with the inclusions `X¹ → X`, `Y¹ → Y`**: for an index raise
`f₁ : X¹ → Y¹` of `f`, `f₁^*(ι^*ω) = ι^*(f^*ω)` as forms on `X¹` (`formLower` is `ι^*`). -/
theorem formLower_formPullback (hf : P.IsScSmoothMap Q f) {f₁ : P.Level 1 → Q.Level 1}
    (hf₁ : ∀ x, Q.levelVal 1 (f₁ x) = f (P.levelVal 1 x))
    (h₁ : P.shift.IsScSmoothMap Q.shift f₁)
    (ω : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ) :
    formPullback h₁ (formLower ω) = formLower (formPullback hf ω) := by
  funext x
  ext α
  rw [formPullback_apply, formLower_apply, formLower_apply, formPullback_apply]
  refine altFamily_congr ω (level_ext (hf₁ _)) _ _ fun i => ?_
  rw [coe_lowerFiberCLM_apply, coe_tangentFiberMap_apply, coe_tangentFiberMap_apply,
    coe_lowerFiberCLM_apply]
  exact tangentLower_tangentMap hf hf₁ (α i).1

/-! ### `d` commutes with the pull-back -/

section Natural

variable (hf : P.IsScSmoothMap Q f) {φ : MChart X} {ψ : MChart Y} (hφ : P.IsChart φ)
  (hψ : Q.IsChart ψ)

/-- **The local exterior derivative of the pull-back**: on `⊕_{k+1} T(φ(V ∩ f⁻¹(V'))¹)`,
`d((f^*ω)_φ) = d(ω_ψ) ∘ ⊕_{k+1} T(ψ ∘ f ∘ φ⁻¹)¹` (the naturality of the local `d`,
`retractD_comp_retractWhitneyMap`). -/
theorem chartD_formPullback {ω : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ}
    (hω : ω ∈ Q.scForms k) {q : (φ.model.E.shift.whitney (k + 1)) 0}
    (hq : q ∈ retractWhitney φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
      (φ.model.E.lvlSet (φ '' TangentPre.fdom φ f ψ) 1) (k + 1)) :
    chartD hφ (formPullback hf ω) q =
      chartD hψ ω (retractWhitneyMap φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
        (φ.model.E.lvlSet (φ '' TangentPre.fdom φ f ψ) 1) (levelMap (ψ ∘ f ∘ φ.symm) 1) (k + 1)
        q) := by
  have hVφ : TangentPre.fdom φ f ψ ⊆ φ.source := inter_subset_left
  have hVo := TangentPre.isOpen_fdom hf φ ψ
  have hO := φ.isScRetract_image hVφ hVo
  obtain ⟨R₁, hR₁⟩ := hO
  have hcoord := TangentPre.isScSmoothRetractMap_coord hf hφ hψ subset_rfl hVo
  have hpω := (mem_scForms.1 (formPullback_mem_scForms hf hω)).isRetractScForm hφ
  have h1 := retractD_eq_of_subset (chartRetraction φ) (chartRetraction_retract φ) R₁ hR₁
    (φ.image_subset_model hVφ) hpω hq
  have hσ : IsRetractScForm φ.model.E φ.model.C R₁.retract k
      (chartForm hφ (formPullback hf ω)) := by
    rw [hR₁]
    exact hpω.mono φ.model.isScRetract (hR₁ ▸ R₁.isScRetract) (φ.image_subset_model hVφ)
  have h2 : retractD R₁ (chartForm hψ ω ∘ retractWhitneyMap φ.model.E φ.model.C
      (φ '' TangentPre.fdom φ f ψ) (ψ ∘ f ∘ φ.symm) k) q =
      retractD R₁ (chartForm hφ (formPullback hf ω)) q :=
    retractD_congr R₁ hσ (fun p hp => by
      rw [hR₁] at hp
      exact chartForm_formPullback hf hφ hψ ω hp) (R₁.mem_whitneySet_of_mem (hR₁ ▸ hq))
  have h3 := retractD_comp_retractWhitneyMap R₁ hR₁ (chartRetraction ψ) (chartRetraction_retract ψ)
    hcoord ((mem_scForms.1 hω).isRetractScForm hψ) hq
  unfold chartD
  rw [← h1, ← h2, h3]

end Natural

/-- **2021 p. 198: `d` commutes with the pull-back** (the commutative square of p. 198, left to the
reader; not in the 2017 text and the preprint): for `f : X → Y` sc-smooth and `ω ∈ Ωᵏ(Y)`,
`d(f^*ω) = (f¹)^*(dω)` as `(k + 1)`-forms on `X¹`, with `f¹ : X¹ → Y¹` the index raise
(`liftLevelOneMap`).  Proved chartwise from the naturality of the local `d`. -/
theorem extD_formPullback (hf : P.IsScSmoothMap Q f)
    {ω : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ} (hω : ω ∈ Q.scForms k) :
    extD (formPullback hf ω) = formPullback (isScSmoothMap_liftLevelOneMap hf) (extD ω) := by
  funext x
  ext α
  set x₁ := P.shift.levelVal 1 x with hx₁
  set f₁ := liftLevelOneMap hf with hf₁def
  have hf₁ : P.shift.IsScSmoothMap Q.shift f₁ := isScSmoothMap_liftLevelOneMap hf
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source (P.levelVal 1 x₁)
  obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f (P.levelVal 1 x₁))
  set V := TangentPre.fdom φ f ψ with hVdef
  have hVφ : V ⊆ φ.source := inter_subset_left
  have hVo : IsOpen V := TangentPre.isOpen_fdom hf φ ψ
  have hO := φ.isScRetract_image hVφ hVo
  have hcoord := TangentPre.isScSmoothRetractMap_coord hf hφ hψ subset_rfl hVo
  set χ := levelChart hφ x₁ with hχdef
  have hχ : P.shift.IsChart χ := P.shift_isChart hφ x₁
  set ψ₁ := levelChart hψ (f₁ x₁) with hψ₁def
  have hψ₁ : Q.shift.IsChart ψ₁ := Q.shift_isChart hψ (f₁ x₁)
  have hx : x₁ ∈ χ.source := hxφ
  -- the point `q₀ = (φ¹(x), Tφ¹ α₀, …, Tφ¹ α_k)` and its membership
  have hs : {y : P.Level 1 | P.levelVal 1 y ∈ V} ⊆ χ.source := fun y hy => hVφ hy
  have hso : IsOpen {y : P.Level 1 | P.levelVal 1 y ∈ V} :=
    (continuous_levelVal 1).isOpen_preimage _ hVo
  have hq₀ : ScBanach.whitneyMk (E := φ.model.E.shift)
      (levelLift (levelChart hφ x₁) 1 (P.shift.levelVal 1 x))
      (fun i => (tangentChartMap (P.shift_isChart hφ x₁) (α i)).2) ∈
      retractWhitney φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1)
        (φ.model.E.lvlSet (φ '' V) 1) (k + 1) := by
    have h := whitneyMk_tangentChartMap_mem_image hχ hs hso (x := x) ⟨hxφ, hfx⟩ α
    rw [levelChart_image_preimage hφ x₁ hVφ] at h
    exact h
  -- the two local representatives of `f¹` agree
  have heq : EqOn (levelMap (ψ ∘ f ∘ φ.symm) 1) (ψ₁ ∘ f₁ ∘ χ.symm)
      (φ.model.E.lvlSet (φ '' V) 1) := by
    intro z hz
    have hzO : φ.model.E.toBase 1 z ∈ φ.model.O := φ.image_subset_model hVφ hz
    have hx' : P.levelVal 1 (χ.symm z) ∈ V := by
      rw [levelChart_symm_apply hφ x₁ hzO]
      obtain ⟨v, hv, hvz⟩ := hz
      rw [← hvz, φ.symm_apply_apply (hVφ hv)]
      exact hv
    have e := levelChart_apply_levelOne (f₁ := f₁) (fun _ => rfl) hφ hψ x₁ (f₁ x₁) hx'.1 hx'.2
    rw [χ.apply_symm_apply (z := z) hzO] at e
    exact e.symm
  have hset : χ '' TangentPre.fdom χ f₁ ψ₁ = φ.model.E.lvlSet (φ '' V) 1 :=
    levelChart_image_preimage hφ x₁ hVφ
  -- both sides in charts
  refine (extD_apply hφ (formPullback_mem_scForms hf hω) x₁ hx α).trans <|
    (chartD_formPullback hf hφ hψ hω hq₀).trans ?_
  rw [formPullback_apply]
  refine Eq.trans ?_ (extD_apply hψ hω (f₁ x₁) (x := liftLevelOneMap hf₁ x) hfx _).symm
  refine congrArg (chartD hψ ω) ?_
  unfold retractWhitneyMap
  refine congrArg₂ (ScBanach.whitneyMk (E := ψ.model.E.shift)) ?_ (funext fun i => ?_)
  · refine (IsSc0.levelMap_congr heq hq₀.1).trans ?_
    exact levelMap_coord_levelLift (P := P.shift) (Q := Q.shift) (f := f₁) hx hχ hψ₁ hfx
      (P.shift.levelVal_mem x) (hf₁.mapsTo_levelSet 1 (P.shift.levelVal_mem x))
  · have hα : (α i).1 ∈ tangentChartSet (P := P.shift) χ :=
      mem_tangentChartSet_of_mem_fiber hx (α i).2
    have hfα : f₁ (P.shift.levelVal 1 (P.shift.tangentProj (α i).1)) ∈ ψ₁.source := by
      rw [tangentProj_eq_of_mem_fiber (α i).2]; exact hfx
    have hv : ((ScBanach.whitneyMk (E := φ.model.E.shift)
        (levelLift (levelChart hφ x₁) 1 (P.shift.levelVal 1 x))
        (fun i => (tangentChartMap (P.shift_isChart hφ x₁) (α i)).2)).1,
        ScBanach.whitneyVec (ScBanach.whitneyMk (E := φ.model.E.shift)
          (levelLift (levelChart hφ x₁) 1 (P.shift.levelVal 1 x))
          (fun i => (tangentChartMap (P.shift_isChart hφ x₁) (α i)).2)) i) =
        tangentChartMap hχ (α i) :=
      Prod.ext (tangentChartMap_fst_of_mem_fiber hχ hx (α i).2).symm
        (congrFun (ScBanach.whitneyVec_mk (E := φ.model.E.shift) _ _) i)
    have h1 := retractTangentMap_congr (hcoord.shift hO) hO.shift heq (hq₀.2 i)
    rw [coe_tangentFiberMap_apply, tangentChartMap_tangentMap hf₁ hχ hψ₁ hα hfα, hset]
    refine (congrArg Prod.snd h1).trans ?_
    exact congrArg (fun a => (retractTangentMap _ _ _ (ψ₁ ∘ f₁ ∘ χ.symm) a).2) hv

/-- The pull-back depends only on the map (not on the proof of its sc-smoothness). -/
theorem formPullback_congr {f' : X → Y} (hf : P.IsScSmoothMap Q f) (hf' : P.IsScSmoothMap Q f')
    (h : ∀ x, f x = f' x) (ω : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ) :
    formPullback hf ω = formPullback hf' ω := by
  obtain rfl : f = f' := funext h
  rfl

namespace ScMap

variable (P) in
/-- The identity, as an `ScMap`. -/
def id : ScMap P P := ⟨_root_.id, isScSmoothMap_id⟩

/-- The composite of two `ScMap`s. -/
def comp (g : ScMap Q S) (f : ScMap P Q) : ScMap P S :=
  ⟨g ∘ f, g.isScSmoothMap.comp f.isScSmoothMap⟩

@[simp] lemma id_apply (x : X) : ScMap.id P x = x := rfl

@[simp] lemma comp_apply (g : ScMap Q S) (f : ScMap P Q) (x : X) : g.comp f x = g (f x) := rfl

end ScMap

end MPolyfold

/-! ### The pull-back on `Ωᵏ(Xⁱ)` and on `Ωᵏ_∞(X)` -/

namespace BundledMPolyfold

open MPolyfold

universe u v w

variable {A : BundledMPolyfold.{u}} {B : BundledMPolyfold.{v}} (f : ScMap A.P B.P) (k : ℕ)

/-- The pull-back `(f^i)^* : Ωᵏ(Y^i) → Ωᵏ(X^i)` along the index raise `f^i : X^i → Y^i`. -/
def formsPullback (i : ℕ) : B.forms k i →ₗ[ℝ] A.forms k i :=
  LinearMap.codRestrict (A.forms k i)
    ((formPullbackₗ k (A.liftMap f i).isScSmoothMap).domRestrict (B.forms k i))
    fun ω => formPullback_mem_scForms _ ω.2

lemma coe_formsPullback (i : ℕ) (ω : B.forms k i) :
    (formsPullback f k i ω).1 = formPullback (A.liftMap f i).isScSmoothMap ω.1 := rfl

/-- The pull-back commutes with the steps `Ωᵏ(Xⁱ) → Ωᵏ(Xⁱ⁺¹)` of the directed system (4.4). -/
theorem formsPullback_formsStep (i : ℕ) (ω : B.forms k i) :
    formsPullback f k (i + 1) (B.formsStep k i ω) = A.formsStep k i (formsPullback f k i ω) :=
  Subtype.ext (formLower_formPullback (A.liftMap f i).isScSmoothMap (f₁ := (A.liftMap f (i + 1)))
    (fun _ => rfl) (A.liftMap f (i + 1)).isScSmoothMap ω.1)

/-- The pull-back commutes with the maps `Ωᵏ(Xⁱ) → Ωᵏ(Xʲ)` of the directed system (4.4). -/
theorem formsPullback_formsMap {i j : ℕ} (h : i ≤ j) (ω : B.forms k i) :
    formsPullback f k j (B.formsMap k i j h ω) = A.formsMap k i j h (formsPullback f k i ω) := by
  induction j, h using Nat.le_induction with
  | base => rw [formsMap_self, formsMap_self]; rfl
  | succ j hij ih =>
    rw [formsMap_succ B k hij, LinearMap.comp_apply, formsPullback_formsStep, ih,
      formsMap_succ A k hij, LinearMap.comp_apply]

/-- **2021 p. 198: the pull-back `f^* : Ωᵏ_∞(Y) → Ωᵏ_∞(X)`** (2017 p. 150; preprint p. 168) of an
sc-smooth map `f : X → Y`: the map induced on the direct limits by the pull-backs
`(f^i)^* : Ωᵏ(Y^i) → Ωᵏ(X^i)` (`formsPullback_formsMap`), as the text describes it. -/
def formsInftyPullback : B.formsInfty k →ₗ[ℝ] A.formsInfty k :=
  Module.DirectLimit.lift ℝ ℕ (fun i => ↥(B.forms k i)) (B.formsMap k)
    (fun i => (A.formsInftyOf k i).comp (formsPullback f k i)) fun i j h ω => by
      simp only [LinearMap.comp_apply]
      rw [formsPullback_formsMap, formsInftyOf_formsMap]

theorem formsInftyPullback_of (i : ℕ) (ω : B.forms k i) :
    formsInftyPullback f k (B.formsInftyOf k i ω) = A.formsInftyOf k i (formsPullback f k i ω) :=
  Module.DirectLimit.lift_of _ _ _

/-- `d` commutes with the pull-back on `Ωᵏ(Xⁱ) → Ωᵏ⁺¹(Xⁱ⁺¹)` (`extD_formPullback`). -/
theorem formsD_formsPullback (i : ℕ) (ω : B.forms k i) :
    A.formsD k i (formsPullback f k i ω) = formsPullback f (k + 1) (i + 1) (B.formsD k i ω) :=
  Subtype.ext (extD_formPullback (A.liftMap f i).isScSmoothMap ω.2)

/-- **2021 p. 198: `f^* ∘ d_Y = d_X ∘ f^*` on `Ωᵏ_∞(Y)`** (not in the 2017 text and the preprint):
the limit of the squares `formsD_formsPullback`, as the text says. -/
theorem formsInftyD_comp_formsInftyPullback :
    (A.formsInftyD k).comp (formsInftyPullback f k) =
      (formsInftyPullback f (k + 1)).comp (B.formsInftyD k) := by
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  simp only [LinearMap.comp_apply]
  rw [formsInftyPullback_of, formsInftyD_of, formsInftyD_of, formsInftyPullback_of,
    formsD_formsPullback]

/-! ### Functoriality on `Ωᵏ_∞` -/

theorem liftMap_id_apply : ∀ (i : ℕ) (y : (A.lift i).carrier), A.liftMap (ScMap.id A.P) i y = y
  | 0, _ => rfl
  | i + 1, y => level_ext (P := (A.lift i).P) (liftMap_id_apply i ((A.lift i).P.levelVal 1 y))

theorem liftMap_comp_apply {C : BundledMPolyfold.{w}} (g : ScMap B.P C.P) (f : ScMap A.P B.P) :
    ∀ (i : ℕ) (y : (A.lift i).carrier),
      A.liftMap (g.comp f) i y = B.liftMap g i (A.liftMap f i y)
  | 0, _ => rfl
  | i + 1, y => level_ext (P := (C.lift i).P) (liftMap_comp_apply g f i ((A.lift i).P.levelVal 1 y))

theorem formsPullback_id (i : ℕ) (ω : A.forms k i) : formsPullback (ScMap.id A.P) k i ω = ω :=
  Subtype.ext ((formPullback_congr _ isScSmoothMap_id (liftMap_id_apply i) ω.1).trans
    (formPullback_id ω.1))

theorem formsPullback_comp {C : BundledMPolyfold.{w}} (g : ScMap B.P C.P) (i : ℕ)
    (ω : C.forms k i) :
    formsPullback (g.comp f) k i ω = formsPullback f k i (formsPullback g k i ω) :=
  Subtype.ext ((formPullback_congr _ ((B.liftMap g i).isScSmoothMap.comp
    (A.liftMap f i).isScSmoothMap) (liftMap_comp_apply g f i) ω.1).trans
    (formPullback_comp _ _ ω.1))

/-- **`id^* = id` on `Ωᵏ_∞(X)`**. -/
theorem formsInftyPullback_id : formsInftyPullback (ScMap.id A.P) k = LinearMap.id := by
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  rw [LinearMap.comp_apply, formsInftyPullback_of, formsPullback_id]
  rfl

/-- **`(g ∘ f)^* = f^* ∘ g^*` on `Ωᵏ_∞`**. -/
theorem formsInftyPullback_comp {C : BundledMPolyfold.{w}} (g : ScMap B.P C.P) :
    formsInftyPullback (g.comp f) k = (formsInftyPullback f k).comp (formsInftyPullback g k) := by
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  simp only [LinearMap.comp_apply]
  rw [formsInftyPullback_of, formsInftyPullback_of, formsInftyPullback_of, formsPullback_comp]

/-! ### The induced map on the sc-de Rham cohomology -/

/-- `f^*` maps closed forms to closed forms. -/
def closedFormsPullback :
    LinearMap.ker (B.formsInftyD k) →ₗ[ℝ] LinearMap.ker (A.formsInftyD k) :=
  (formsInftyPullback f k).restrict fun ω hω => by
    rw [LinearMap.mem_ker] at hω ⊢
    refine (LinearMap.congr_fun (formsInftyD_comp_formsInftyPullback f k) ω).trans ?_
    rw [LinearMap.comp_apply, hω, map_zero]

@[simp] lemma coe_closedFormsPullback (c : LinearMap.ker (B.formsInftyD k)) :
    (closedFormsPullback f k c : A.formsInfty k) = formsInftyPullback f k c := rfl

/-- `f^*` maps exact forms to exact forms. -/
theorem formsInftyPullback_mem_formsInftyDRange :
    ∀ (k : ℕ) {ω : B.formsInfty k}, ω ∈ B.formsInftyDRange k →
      formsInftyPullback f k ω ∈ A.formsInftyDRange k
  | 0, ω, hω => by
    have h0 : ω = 0 := (Submodule.mem_bot ℝ).1 hω
    rw [h0, map_zero]
    exact Submodule.zero_mem _
  | k + 1, _, ⟨β, rfl⟩ =>
    ⟨formsInftyPullback f k β, LinearMap.congr_fun (formsInftyD_comp_formsInftyPullback f k) β⟩

/-- **The induced map `f^* : Hᵏ_sc(Y) → Hᵏ_sc(X)`** on the sc-de Rham cohomology (Definition
4.4.6), from `f^* ∘ d = d ∘ f^*`. -/
def scDeRhamPullback : B.scDeRham k →ₗ[ℝ] A.scDeRham k :=
  Submodule.mapQ _ _ (closedFormsPullback f k) fun _ hc =>
    formsInftyPullback_mem_formsInftyDRange f k hc

theorem scDeRhamPullback_mk (c : LinearMap.ker (B.formsInftyD k)) :
    scDeRhamPullback f k (B.scDeRhamMk k c) = A.scDeRhamMk k (closedFormsPullback f k c) := rfl

end BundledMPolyfold

end Polyfold
