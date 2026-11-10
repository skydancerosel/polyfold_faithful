import Polyfold.Chapter4.ScFormsGlobal2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4, p. 198
(2017 p. 150; preprint: before Definition 4.27): `d² = 0` for the exterior derivative of
sc-differential forms.

# `d ∘ d = 0`

## What is proved

* `sum_removeNth_symm_eq_zero`: a double alternating sum `Σᵢ (-1)ⁱ Σⱼ (-1)ʲ G(vᵢ, (v̂ᵢ)ⱼ, …)`
  vanishes when `G` is symmetric in its first two arguments.
* `ambientD_ambientD`: `d(dΩ) = 0` on `⊕_{k+2} T(U²)` for an sc-smooth `Ω` on `⊕ₖ TU`, `U`
  relatively open in a partial quadrant.  The derivative of `dΩ` is a sum of second derivatives
  of `Ω` (`scDeriv_ambientD_whitneyMk`), which cancel by `scSecondDeriv_symm`.
* `retractD_shift_retractD`: `d_{r¹}(d_r ω) = 0` on a retract.
* `extD_extD`: `d(dω) = 0` in `Ωᵏ⁺²(X²)` for `ω ∈ Ωᵏ(X)`, `X` an M-polyfold.

The book states `d² = 0` on `Ω*_∞(X)`; that form is `formsInftyD_comp_formsInftyD` in
`ScFormsLower2021`.
-/

open Set Function

noncomputable section

namespace Polyfold

/-! ### The algebra: a double alternating sum of a symmetric expression vanishes -/

section Algebra

/-- `Σᵢ (-1)ⁱ Σⱼ (-1)ʲ G(vᵢ, (v̂ᵢ)ⱼ, (v̂ᵢ)^ⱼ) = 0` when `G` is symmetric in its first two
arguments (the cancellation behind `d ∘ d = 0`). -/
theorem sum_removeNth_symm_eq_zero {M : Type*} {n : ℕ} (G : M → M → (Fin n → M) → ℝ)
    (hG : ∀ a b w, G a b w = G b a w) (v : Fin (n + 2) → M) :
    ∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) * ∑ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) *
      G (v i) (i.removeNth v j) (j.removeNth (i.removeNth v)) = 0 := by
  simp only [Finset.mul_sum]
  rw [Fin.sum_sum_eq_sum_triangle_add]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_Ici] at hj
  have H₁ : i.castSucc.removeNth v j = v j.succ := by
    simp [Fin.removeNth_apply, Fin.succAbove_of_le_castSucc, hj]
  have H₂ : j.succ.removeNth v i = v i.castSucc := by
    simp [Fin.removeNth_apply, Fin.succAbove_of_castSucc_lt, hj]
  have H₃ : j.removeNth (i.castSucc.removeNth v) = i.removeNth (j.succ.removeNth v) := by
    rw [Fin.removeNth_removeNth_eq_swap]; simp [Fin.predAbove, Fin.succAbove, not_lt.2 hj]
  rw [H₁, H₂, H₃, hG (v j.succ), Fin.val_castSucc, Fin.val_succ, pow_succ]
  ring

end Algebra

/-! ### The derivative of `dΩ` along the base -/

section Local

variable {E : ScBanach} {C U : Set (E 0)} {k : ℕ}

/-- The chosen derivative of a finite real combination of real sc¹ maps. -/
theorem scDeriv_sum_const_mul {W : Set (E 0)} (hW : IsScDomain E W) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) {f : ι → E 0 → (ScBanach.const ℝ) 0}
    (hf : ∀ i ∈ s, IsSc1 (F := ScBanach.const ℝ) W (f i))
    (hs : IsSc1 (F := ScBanach.const ℝ) W fun z => ∑ i ∈ s, c i * f i z) {x : E 1}
    (hx : x ∈ E.lvlSet W 1) :
    scDeriv (F := ScBanach.const ℝ) W (fun z => ∑ i ∈ s, c i * f i z) x =
      ∑ i ∈ s, c i • scDeriv (F := ScBanach.const ℝ) W (f i) x :=
  hs.scDeriv_eq_of_hasFDerivWithinAt hx (hW.uniqueDiffWithinAt 1 x hx) (by
    rw [ContinuousLinearMap.finsetSum_comp]
    simp only [ContinuousLinearMap.smul_comp]
    exact HasFDerivWithinAt.fun_sum fun i hi =>
      ((hf i hi).isSc1With_scDeriv.hasFDerivWithinAt x hx).const_mul (c i))

lemma whitneyDelete_whitneyMk_zero (j : Fin (k + 1)) (η : E.shift 1) :
    E.whitneyDelete k j 0 (ScBanach.whitneyMk (E := E.shift) η 0) =
      (((η, 0) : (E.whitney k) 1), (0 : (E.whitney k) 0)) := by
  rw [ScBanach.whitneyDelete_apply]
  refine Prod.ext (Prod.ext rfl ?_) ?_
  · change E.fiberPackL 1 k (j.removeNth (ScBanach.whitneyVec
      (ScBanach.whitneyMk (E := E.shift) η 0))) = 0
    rw [ScBanach.whitneyVec_mk]
    exact map_zero _
  · change ScBanach.whitneyMk (ScBanach.whitneyVec (ScBanach.whitneyMk (E := E.shift) η 0) j) 0 = 0
    rw [ScBanach.whitneyVec_mk]
    exact Prod.ext rfl (map_zero _)

lemma whitneyDelete_one_mk (j : Fin (k + 1)) (y : E.shift.shift 1) (W : Fin (k + 1) → E.shift 1) :
    E.whitneyDelete k j 1 (y, E.shift.fiberPackL 1 (k + 1) W) =
      (((y, E.fiberPackL 2 k (j.removeNth W)) : (E.whitney k).shift 1),
        ((W j, 0) : (E.whitney k) 1)) := by
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext ?_ rfl)
  · change E.fiberPackL 2 k (j.removeNth (E.shift.fiberVecL 1 (k + 1)
      (E.shift.fiberPackL 1 (k + 1) W))) = _
    rw [ScBanach.fiberVecL_fiberPackL]
  · change E.shift.fiberVecL 1 (k + 1) (E.shift.fiberPackL 1 (k + 1) W) j = W j
    rw [ScBanach.fiberVecL_fiberPackL]

variable (hU : IsRelOpenInQuadrant E C U) {Ω : (E.whitney k) 0 → ℝ}
  (hΩ : IsScSmooth (F := ScBanach.const ℝ) (E.whitneySet k U) Ω)
include hU hΩ

/-- The `j`-th term `q ↦ DΩ(whitneyDelete j q)` of `dΩ` is sc-smooth. -/
lemma isScSmooth_ambientD_term (j : Fin (k + 1)) :
    IsScSmooth (F := ScBanach.const ℝ) (E.shift.whitneySet (k + 1) (E.lvlSet U 1)) fun q =>
      (tangentMap (F := ScBanach.const ℝ) (E.whitneySet k U) Ω (E.whitneyDelete k j 0 q)).2 := by
  have hD := (hU.shift.whitneySet (k + 1)).isScDomain
  have hT : IsScSmooth ((E.whitney k).tangentSet (E.whitneySet k U))
      (tangentMap (F := ScBanach.const ℝ) (E.whitneySet k U) Ω) := fun n => (hΩ (n + 1)).2
  exact ((ScBanach.prodSndOp _ _).isScSmooth (isScDomain_univ _)).comp hD (isScDomain_univ _)
    (hT.comp hD (hU.whitneySet k).isScDomain.tangentSet ((E.whitneyDelete k j).isScSmooth hD)
      (mapsTo_whitneyDelete j)) (mapsTo_univ _ _)

/-- The derivative of the `j`-th term of `dΩ`. -/
lemma scDeriv_ambientD_term (j : Fin (k + 1)) {p : (E.shift.whitney (k + 1)) 1}
    (hp : p ∈ (E.shift.whitney (k + 1)).lvlSet (E.shift.whitneySet (k + 1) (E.lvlSet U 1)) 1)
    (u : (E.shift.whitney (k + 1)) 0) :
    scDeriv (F := ScBanach.const ℝ) (E.shift.whitneySet (k + 1) (E.lvlSet U 1)) (fun q =>
      (tangentMap (F := ScBanach.const ℝ) (E.whitneySet k U) Ω (E.whitneyDelete k j 0 q)).2) p u =
      (scDeriv ((E.whitney k).tangentSet (E.whitneySet k U))
        (tangentMap (F := ScBanach.const ℝ) (E.whitneySet k U) Ω) (E.whitneyDelete k j 1 p)
        (E.whitneyDelete k j 0 u)).2 := by
  have hD := (hU.shift.whitneySet (k + 1)).isScDomain
  have hTD := (hU.whitneySet k).isScDomain.tangentSet
  have hT1 : IsSc1 ((E.whitney k).tangentSet (E.whitneySet k U))
      (tangentMap (F := ScBanach.const ℝ) (E.whitneySet k U) Ω) := (hΩ 2).2.1
  have hDel := ((E.whitneyDelete k j).isScSmooth hD 1).1
  have hTDel : IsSc1 (E.shift.whitneySet (k + 1) (E.lvlSet U 1))
      (tangentMap (F := ScBanach.const ℝ) (E.whitneySet k U) Ω ∘ E.whitneyDelete k j 0) :=
    (theorem_1_3_1' hD hTD hDel hT1 (mapsTo_whitneyDelete j)).1
  have hSnd := ((ScBanach.prodSndOp (ScBanach.const ℝ).shift (ScBanach.const ℝ)).isScSmooth
    (isScDomain_univ _) 1).1
  change scDeriv _ ((ScBanach.prodSndOp (ScBanach.const ℝ).shift (ScBanach.const ℝ) 0) ∘
    (tangentMap (F := ScBanach.const ℝ) (E.whitneySet k U) Ω ∘ E.whitneyDelete k j 0)) p u = _
  rw [scDeriv_comp hD (isScDomain_univ _) hTDel hSnd (mapsTo_univ _ _) hp,
    ScOperator.scDeriv_eq _ (isScDomain_univ _) (mem_univ _),
    scDeriv_comp hD hTD hDel hT1 (mapsTo_whitneyDelete j) hp,
    ScOperator.scDeriv_eq _ hD hp, ScOperator.levelMap_eq]
  rfl

/-- **The derivative of `dΩ` along the base**: `D(dΩ)(p)(η, 0) = Σⱼ (-1)ʲ D²Ω(pⱼ)(aⱼ, (η, 0))`,
the second derivatives of `Ω` at the points `(pⱼ, aⱼ) = whitneyDelete j p`. -/
theorem scDeriv_ambientD_whitneyMk {p : (E.shift.whitney (k + 1)) 1}
    (hp : p ∈ (E.shift.whitney (k + 1)).lvlSet (E.shift.whitneySet (k + 1) (E.lvlSet U 1)) 1)
    (η : E.shift 1) :
    scDeriv (F := ScBanach.const ℝ) (E.shift.whitneySet (k + 1) (E.lvlSet U 1)) (ambientD U Ω) p
        (ScBanach.whitneyMk (E := E.shift) η 0) =
      ∑ j : Fin (k + 1), (-1 : ℝ) ^ j.val *
        scSecondDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) Ω
          (E.whitneyDelete k j 1 p).1 (E.whitneyDelete k j 1 p).2 ((η, 0) : (E.whitney k) 1) := by
  have hD := (hU.shift.whitneySet (k + 1)).isScDomain
  have h := scDeriv_sum_const_mul hD Finset.univ (fun j : Fin (k + 1) => (-1 : ℝ) ^ j.val)
    (f := fun j q =>
      (tangentMap (F := ScBanach.const ℝ) (E.whitneySet k U) Ω (E.whitneyDelete k j 0 q)).2)
    (fun j _ => (isScSmooth_ambientD_term hU hΩ j 1).1)
    ((IsScSmooth.ambientD hU hΩ 1).1) hp
  change scDeriv (F := ScBanach.const ℝ) _ (fun z => ∑ j : Fin (k + 1), (-1 : ℝ) ^ j.val *
    (tangentMap (F := ScBanach.const ℝ) (E.whitneySet k U) Ω (E.whitneyDelete k j 0 z)).2) p _ = _
  rw [h, _root_.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [_root_.smul_apply, scDeriv_ambientD_term hU hΩ j hp,
    whitneyDelete_whitneyMk_zero, smul_eq_mul]
  rfl

/-- **`d ∘ d = 0` for the local exterior derivative** (2021 p. 198, `d² = 0`, in the model): for
an sc-smooth `Ω : ⊕ₖ TU → ℝ`, `d(dΩ) = 0` on `⊕_{k+2} T(U²)` (symmetry of the second
derivatives, `scSecondDeriv_symm`, and `sum_removeNth_symm_eq_zero`). -/
theorem ambientD_ambientD {q : (E.shift.shift.whitney (k + 2)) 0}
    (hq : q ∈ E.shift.shift.whitneySet (k + 2) (E.shift.lvlSet (E.lvlSet U 1) 1)) :
    ambientD (E.lvlSet U 1) (ambientD U Ω) q = 0 := by
  have hp : ∀ i : Fin (k + 2),
      ((q.1, E.shift.fiberPackL 1 (k + 1) (i.removeNth (ScBanach.whitneyVec q))) :
        (E.shift.whitney (k + 1)) 1) ∈
        (E.shift.whitney (k + 1)).lvlSet (E.shift.whitneySet (k + 1) (E.lvlSet U 1)) 1 :=
    fun _ => mem_whitneySet_lvl_one.2 (ScBanach.mem_whitneySet.1 hq)
  have hz : ∀ w : Fin k → E 2, ((q.1, E.fiberPackL 2 k w) : (E.whitney k) 2) ∈
      (E.whitney k).lvlSet (E.whitneySet k U) 2 := fun w => by
    have h1 := ScBanach.mem_whitneySet.1 hq
    rw [ScBanach.mem_lvlSet, ScBanach.mem_whitneySet, ScBanach.prod_toBase]
    exact h1
  set G : E 2 → E 2 → (Fin k → E 2) → ℝ := fun a b w =>
    scSecondDeriv (F := ScBanach.const ℝ) (E.whitneySet k U) Ω
      ((q.1, E.fiberPackL 2 k w) : (E.whitney k).shift 1)
      ((b, 0) : (E.whitney k) 1) ((a, 0) : (E.whitney k) 1) with hG
  have hGs : ∀ a b w, G a b w = G b a w := fun a b w =>
    scSecondDeriv_symm (hU.whitneySet k) (hΩ 2) (hz w) _ _
  rw [ambientD_apply]
  refine Eq.trans ?_ (sum_removeNth_symm_eq_zero G hGs (ScBanach.whitneyVec q))
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [scDeriv_ambientD_whitneyMk hU hΩ (hp i)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [whitneyDelete_one_mk]

omit hU hΩ in
/-- **`d ∘ d = 0` on a retract**: `d_{r¹}(d_r ω) = 0` on `⊕_{k+2} T(U²)` for an sc-form `ω` on
the retract `O = r(U)` and the retraction `r¹` of `U¹` onto `O¹`. -/
theorem retractD_shift_retractD (R : ScRetraction E C) {ω : (E.whitney k) 0 → ℝ}
    (hω : IsRetractScForm E C R.retract k ω) {q : (E.shift.shift.whitney (k + 2)) 0}
    (hq : q ∈ E.shift.shift.whitneySet (k + 2) (E.shift.lvlSet R.shift.U 1)) :
    retractD R.shift (retractD R ω) q = 0 := by
  have hΩ₀ := hω.isAmbientScForm_comp R
  have hdΩ := hΩ₀.ambientD R.relOpen
  change ambientD R.shift.U (ambientD R.U (ω ∘ R.whitney k) ∘
    whitneyMap R.shift.U R.shift (k + 1)) q = 0
  rw [ambientD_comp_whitneyMap R.shift.relOpen R.shift.relOpen R.shift.isScSmooth R.shift.mapsTo
    hdΩ hq]
  exact ambientD_ambientD R.relOpen hΩ₀.isScSmooth
    (mapsTo_whitneyMap R.shift.shift.isSc1.isSc0 R.shift.shift.mapsTo (k + 2) hq)

end Local

/-! ### `d ∘ d = 0` on an M-polyfold -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {φ : MChart X} {k : ℕ} {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}

/-- In a level chart `φ¹` of `X¹`, the local exterior derivative of `dω` vanishes on
`⊕_{k+2} T(O²)`. -/
theorem chartD_extD_eq_zero (hφ : P.IsChart φ) (hω : P.IsScForm k ω) (y₀ : P.Level 1)
    {q : (φ.model.E.shift.shift.whitney (k + 2)) 0}
    (hq : q ∈ retractWhitney φ.model.E.shift.shift
      (φ.model.E.shift.lvlSet (φ.model.E.lvlSet φ.model.C 1) 1)
      (φ.model.E.shift.lvlSet (φ.model.E.lvlSet φ.model.O 1) 1) (k + 2)) :
    chartD (P.shift_isChart hφ y₀) (extD ω) q = 0 := by
  have hχ := P.shift_isChart hφ y₀
  have hR := chartRetraction_retract φ
  have hR1 : (chartRetraction φ).shift.retract = φ.model.E.lvlSet φ.model.O 1 := by
    rw [(chartRetraction φ).shift_retract, hR]
  have hd := hω.chartD hφ
  have hωφ : IsRetractScForm φ.model.E φ.model.C (chartRetraction φ).retract k
      (chartForm hφ ω) := by
    rw [hR]; exact hω.isRetractScForm hφ
  have hq1 : q ∈ retractWhitney φ.model.E.shift.shift
      (φ.model.E.shift.lvlSet (φ.model.E.lvlSet φ.model.C 1) 1)
      (φ.model.E.shift.lvlSet (chartRetraction φ).shift.retract 1) (k + 2) := by
    rw [hR1]; exact hq
  have key : ∀ R' : ScRetraction φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1),
      R'.retract = φ.model.E.lvlSet φ.model.O 1 → retractD R' (chartForm hχ (extD ω)) q = 0 := by
    intro R' hR'
    have hd' : IsRetractScForm φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1) R'.retract (k + 1)
        (chartD hφ ω) := by
      rw [hR']; exact hd
    have hq' : q ∈ retractWhitney φ.model.E.shift.shift
        (φ.model.E.shift.lvlSet (φ.model.E.lvlSet φ.model.C 1) 1)
        (φ.model.E.shift.lvlSet R'.retract 1) (k + 2) := by
      rw [hR']; exact hq
    have h1 : retractD R' (chartForm hχ (extD ω)) q = retractD R' (chartD hφ ω) q :=
      retractD_congr R' hd' (fun p hp => by
        rw [hR'] at hp
        exact (chartForm_extD hφ hω y₀ hp).symm) (R'.mem_whitneySet_of_mem hq')
    rw [h1, retractD_eq_of_subset (chartRetraction φ).shift hR1 R' hR' subset_rfl hd hq]
    exact retractD_shift_retractD (chartRetraction φ) hωφ
      ((chartRetraction φ).shift.mem_whitneySet_of_mem hq1)
  exact key (chartRetraction (levelChart hφ y₀)) (chartRetraction_retract _)

/-- **2021 p. 198: `d² = 0`** (2017 p. 150; preprint: before Definition 4.27): for an
sc-differential `k`-form `ω` on `X`, `d(dω) = 0` as a `(k + 2)`-form on `X²`. In the level charts
`φ²` it is the local statement `retractD_shift_retractD` (symmetry of second derivatives). -/
theorem extD_extD (hω : ω ∈ P.scForms k) : extD (extD ω) = 0 := by
  have hdω := extD_mem_scForms hω
  funext x
  ext α
  set x₁ := P.shift.shift.levelVal 1 x
  have hφ := dChart_isChart x₁
  have hχ := P.shift_isChart hφ (P.shift.levelVal 1 x₁)
  have hx : P.shift.shift.levelVal 1 x ∈ (levelChart hχ x₁).source := mem_dLevelChart_source x₁
  rw [extD_apply hχ hdω x₁ hx α, Pi.zero_apply, AlternatingMap.zero_apply]
  exact chartD_extD_eq_zero hφ (mem_scForms.1 hω) _ (whitneyMk_tangentChartMap_mem hχ x₁ hx α)

end MPolyfold

end Polyfold
