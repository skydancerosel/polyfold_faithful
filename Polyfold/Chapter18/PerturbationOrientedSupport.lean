import Polyfold.Chapter18.PerturbationOrientedWitness
import Polyfold.Chapter15.ParamOntoBridge
import Polyfold.Chapter3.TameGermData
import Polyfold.Chapter18.ImplicitFunctionTheorem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.6, p. 861: **the orientation clause of Theorem 18.6.1 with a non-empty solution set**, on the
reflection bundle of Chapter 17, with the trivial multisection functor `Λ₀` (Definition 18.3.1,
`zeroFunctor`) and general position in the sense of Definition 15.3.5.  Numbers and pages are the
2021 text's.

# A non-empty `Θ = Λ ∘ f` in the orientation clause of Theorem 18.6.1

`C = ℤ/2 ⋉ ℝ`, `E = ℝ × ℝ` with `−1` acting by `(x, v) ↦ (−x, −v)`, `f(x) = (x, x)`
(`reflDiag`), in the covering model of one copy of `Ψ̄` (`reflSingleModel`).

* `SBLocalization.isInGeneralPositionAt_zeroMultisection_of_chart`: **Definition 15.3.5 at a zero
  `x₀` of `f`, for the trivial multisection, read in one chart centred at `x₀` and one
  presentation of its partial quadrant** (the reduced tangent space does not depend on the chart,
  Definition 2.5.8, and the only operator of `T(f, Λ₀)(x₀)` is `f'(x₀)`).
* `isInGeneralPositionAt_reflSingleModel_zero`, **`isInGeneralPositionIn_reflDiag_zeroFunctor`**:
  `(f^Ψ̄, Γ̄^*Λ₀)` is in general position ((4) of Theorem 18.6.1): `supp(Λ₀ ∘ f^Ψ̄)` is the one
  point `(·, 0)`, where `D f^Ψ̄(0) = id` in the translation chart and `0` is interior.
* `isScPlusMultisectionIn_reflV_zeroFunctor`, `pointwiseNormFunctor_reflV_zeroFunctor_eq_zero`
  (`N(Λ₀) = 0` for every auxiliary norm), `orbitDomSupp_reflV_zeroFunctor`
  (`|dom-supp(Λ₀)| = ∅`), `zeroFunctor_reflDiag_pos_iff` (`supp(Λ₀ ∘ f) = {0}`).
* **`theorem_18_6_1_oriented_witness_support`**: all hypotheses of
  `theorem_18_6_1_oriented` hold for `Λ₀` (an orientation `o` of `f`, `(N, U)` controlling
  compactness, `N(Λ₀) ≤ 1`, `|dom-supp(Λ₀)| ⊆ U`, (4), and the index hypothesis with `n = 0`),
  and its conclusion is about the oriented branched ep⁺-subcategory `Θ = Λ₀ ∘ f` with
  `Θ(x) > 0 ⟺ x = 0` and `Θ(0) = 1`: the solution set is non-empty, and it is the point with
  isotropy `ℤ/2`.

## Why the reflection bundle and not the half-plane

On the half-plane construction (`HalfSpaceReflection.halfQ`, `∂C ≠ ∅`) the automorphism `−1` of
`(a, 0)` acts on `T_{(a,0)}H = ℝ²` by `(α, β) ↦ (α, −β)` (determinant `−1`) and trivially on the
fibre `ℝ`; it then acts by `−1` on the determinant line of every linearization at `(a, 0)`, so no
sc-Fredholm section functor of that bundle is orientable (Definition 18.5.4), and the
orientation clause has no instance there.  The reflection bundle has `∂C = ∅`; `−1` acts by `−1`
on both `T_0ℝ` and the fibre, hence trivially on the determinant line.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology
open scoped ENNReal

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-- **General position of `(f, Λ₀)` at a zero, read in one chart centred at it** (Definition
15.3.5 at one point). -/
theorem isInGeneralPositionAt_zeroMultisection_of_chart {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) {x₀ : A.Obj}
    (hxc : x₀ ∈ c.φ.source) (hφ0 : c.φ x₀ = 0) (hx0 : f x₀ = fiberZero A.P x₀) {n : ℕ}
    {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (honto : ∀ k, ((0 : c.φ.model.E 0), k) ∈ c.K →
      ∃ u : ↥(rangeS (scDeriv c.U (r c.R) 0)), (u : c.φ.model.E 0) ∈ minimalSubspaceWith T 0 ∧
        linAt c.U c.R (c.principal f) 0 u = k) :
    IsInGeneralPositionAt f (zeroMultisection A) x₀ := by
  classical
  have hpos : 0 < zeroMultisection A (f x₀) := by
    unfold zeroMultisection
    rw [if_pos (by rw [hf.1.1.1 x₀]; exact hx0)]
    exact one_pos
  have hx1 := mem_levelSet_one_of_pos hf (isScPlusMultisection_zeroMultisection A) hpos
  refine ⟨hx1, ?_⟩
  set x := A.X.PObj.levelMk 1 x₀ hx1 with hxdef
  have hxv : A.X.PObj.levelVal 1 x = x₀ := A.X.PObj.levelVal_levelMk _ _ _
  have hx : A.X.PObj.levelVal 1 x ∈ c.φ.source := by rw [hxv]; exact hxc
  have hφ0' : c.φ (A.X.PObj.levelVal 1 x) = 0 := by rw [hxv]; exact hφ0
  have hx0' : f (A.X.PObj.levelVal 1 x) = fiberZero A.P (A.X.PObj.levelVal 1 x) := by
    rw [hxv]; exact hx0
  intro L hL ψ hψ hxψ n' V T' hT'
  rw [← reducedTangentFiber_eq (hφ := c.isChart) (hx := hx) (T := T)
    (hψ := hψ) (hx' := hxψ) (T' := T') hT hT']
  rw [← (mem_support_linearization_zero_iff hf hc hx hx0' L).1 hL]
  have key := (onto_chart_iff (A := A) (ℓ := 0) (s := fun j => j.elim0) (hft := hft)
    (hsec := fun j => j.elim0) (hc := hc) (hx := hx) (hφ0 := hφ0') (hx0 := hx0')
    (T := T)).2 ?_
  · intro w
    obtain ⟨v, hv, τ, he⟩ := key w
    refine ⟨⟨v, hv⟩, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at he
    exact he
  · intro q hq
    obtain ⟨u, hu, he⟩ := honto q hq
    refine ⟨u, hu, fun j => j.elim0, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact he

end SBLocalization

namespace GCT.VectorBundle.ReflectionBundle

open StrongRetr GroupoidalCategory StrongPolyfoldBundleConstruction PolyfoldConstruction
  TrivialBundle SBLocalization

/-- **`(f^Ψ̄, Λ₀)` is in general position at the zero `(·, 0)`** (Definition 15.3.5 at one
point): `D f^Ψ̄(0) = id` in the translation chart, and `0` is an interior point. -/
theorem isInGeneralPositionAt_reflSingleModel_zero :
    IsInGeneralPositionAt (A := reflSingleModel) (reflQ.modelSection reflSingle.Ψ reflDiag)
      (zeroMultisection reflSingleModel) (⟨(), (0 : Fin 1 → ℝ)⟩ : reflSingleModel.Obj) := by
  have hf := reflQ.modelFred reflSingle.Ψ isScFredholmSectionFunctor_reflDiag
  have hft := reflQ.modelFredTame reflSingle.Ψ isScFredholmSectionFunctorTame_reflDiag
  have hφ0 : (reflSingleChartPt 0).c.φ (⟨(), (0 : Fin 1 → ℝ)⟩ : reflSingleModel.Obj) = 0 := by
    have := (reflSingleChartPt 0).toBase_z
    have hz : (reflSingleChartPt 0).z = 0 := rfl
    rw [hz, map_zero] at this
    exact this.symm
  refine isInGeneralPositionAt_zeroMultisection_of_chart hf hft (reflSingleChartPt 0).isChart
    (reflSingleChartPt 0).mem_source hφ0 isZeroAt_reflSingleModel_zero
    (TrivialBundle.univPres _) (TrivialBundle.univ_eq_univPres _) fun k _ => ?_
  have htop : rangeS (scDeriv (reflSingleChartPt 0).c.U (r (reflSingleChartPt 0).c.R) 0) = ⊤ :=
    reflSingleChartPt_T 0
  refine ⟨⟨k, by rw [htop]; exact Submodule.mem_top⟩,
    (mem_minimalSubspaceWith _).2 fun i _ => i.elim0, ?_⟩
  rw [linAt_apply, scDeriv_principal_reflSingleChartPt]
  rfl


/-- `(x, v) = (x, 0)` in `E` iff `v = 0`. -/
theorem reflV_objMk_eq_objMk_zero_iff (α v : Fin 1 → ℝ) :
    reflV.objMk α v = reflV.objMk α 0 ↔ v = 0 :=
  ⟨fun h => congrArg (fun e => (toPair e).2) h, fun h => by rw [h]; rfl⟩

/-- `Λ₀(x, v) > 0` iff `v = 0`. -/
theorem reflV_zeroFunctor_pos_iff (α v : Fin 1 → ℝ) :
    0 < reflV.zeroFunctor (reflV.objMk α v) ↔ v = 0 := by
  classical
  unfold zeroFunctor
  rw [← reflV_objMk_eq_objMk_zero_iff α v]
  change 0 < (if reflV.objMk α v = reflV.objMk α 0 then 1 else 0 : ℚ≥0) ↔ _
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => one_pos⟩
  · exact ⟨fun h' => absurd h' (lt_irrefl 0), fun h' => absurd h' h⟩

/-- **`supp(Λ₀ ∘ f) = {0}`**: `Λ₀(f(x)) = Λ₀(x, x) > 0` iff `x = 0`. -/
theorem zeroFunctor_reflDiag_pos_iff (α : Fin 1 → ℝ) :
    0 < reflV.zeroFunctor (reflDiag.toFun α) ↔ α = 0 :=
  reflV_zeroFunctor_pos_iff α α

/-- `|dom-supp(Λ₀)| = ∅`: `Λ₀` charges no non-zero vector. -/
theorem orbitDomSupp_reflV_zeroFunctor : orbitDomSupp reflV.zeroFunctor = ∅ := by
  unfold orbitDomSupp
  have : {α : Fin 1 → ℝ | ∃ v : reflV.V α, v ≠ 0 ∧ 0 < reflV.zeroFunctor (reflV.objMk α v)} =
      ∅ :=
    eq_empty_of_forall_notMem fun α ⟨v, hv, hpos⟩ => hv ((reflV_zeroFunctor_pos_iff α v).1 hpos)
  rw [this, image_empty, closure_empty]

/-- **`N(Λ₀) = 0`** for an auxiliary norm `N`: `N(x, 0) = 0`. -/
theorem pointwiseNormFunctor_reflV_zeroFunctor_eq_zero {N : reflV.EObj → ℝ≥0∞}
    (hN : reflQ.IsAuxNormFunctor N) (α : Fin 1 → ℝ) :
    pointwiseNormFunctor N reflV.zeroFunctor α = 0 := by
  have hNc := hN reflSingle
  have hset : {v : reflV.V α | 0 < reflV.zeroFunctor (reflV.objMk α v)} = {0} := by
    ext v
    exact reflV_zeroFunctor_pos_iff α v
  have hval : pointwiseNormFunctor N reflV.zeroFunctor α = N (reflV.objMk α 0) := by
    unfold pointwiseNormFunctor
    rw [hset, image_singleton, sSup_singleton]
  have hw : (⟨(), (α, 0)⟩ : reflQ.ModelW reflSingle.Ψ) ∈ (reflQ.modelSEP reflSingle.Ψ).B.oneSet :=
    (StrongBundle.mem_oneSet_sigma_iff (B := fun _ : Unit => bundle 1 1) (i := ()) (α, 0)).2
      (((bundle 1 1).mem_oneSet_iff (c := chart 0) (mem_range_self 0) (mem_univ _)).2
        ((bijective_toBase_const _ 1).2 _))
  have hne : pointwiseNormFunctor N reflV.zeroFunctor α ≠ ⊤ := by
    rw [hval]
    exact hNc.ne_top _ hw
  have h := reflQ.pointwiseNorm_bundlePull_of_ne_top hNc reflV.zeroFunctor ⟨(), α⟩ hne
  rw [reflQ.bundlePull_zeroFunctor] at h
  have h' : (pointwiseNormFunctor N reflV.zeroFunctor α).toReal = 0 :=
    h.trans (pointwiseNorm_zeroMultisection (A := reflQ.modelSEP reflSingle.Ψ)
      hNc.isAuxNorm.isAuxNorm ⟨(), α⟩)
  exact ((ENNReal.toReal_eq_zero_iff _).1 h').resolve_right hne

/-- `Γ̄^*Λ₀` is an sc⁺-multisection (it is the trivial multisection of the model). -/
theorem isScPlusMultisectionIn_reflV_zeroFunctor :
    reflQ.IsScPlusMultisectionIn reflSingle.Ψ reflV.zeroFunctor := by
  change IsScPlusMultisection reflSingleModel (reflQ.bundlePull reflSingle.Ψ reflV.zeroFunctor)
  rw [reflQ.bundlePull_zeroFunctor]
  exact isScPlusMultisection_zeroMultisection _

/-- A zero `(·, q)` of `f^Ψ̄` charged by `Λ₀` is `q = 0`. -/
theorem eq_zero_of_zeroMultisection_reflSingleModel_pos {q : Fin 1 → ℝ}
    (h : 0 < zeroMultisection reflSingleModel
      (reflQ.modelSection reflSingle.Ψ reflDiag (⟨(), q⟩ : reflSingleModel.Obj))) : q = 0 := by
  classical
  have hf := reflQ.modelFred reflSingle.Ψ isScFredholmSectionFunctor_reflDiag
  have h0 : IsZeroAt reflSingleModel.P (reflQ.modelSection reflSingle.Ψ reflDiag)
      (⟨(), q⟩ : reflSingleModel.Obj) := by
    unfold zeroMultisection at h
    split_ifs at h with he
    · have hp := hf.1.1.1 (⟨(), q⟩ : reflSingleModel.Obj)
      rw [hp] at he
      exact he
    · exact absurd h (lt_irrefl 0)
  have h1 := (reflQ.isZeroAt_modelSection_iff reflSingle.Ψ reflDiag _).1 h0
  exact congrArg (fun e => (toPair e).2) h1

/-- **`(f, Λ₀)` is in general position in the model** ((4) of Theorem 18.6.1): `supp(Λ₀ ∘ f^Ψ̄)`
is the one point `(·, 0)`, where `D f^Ψ̄(0) = id`. -/
theorem isInGeneralPositionIn_reflDiag_zeroFunctor :
    reflQ.IsInGeneralPositionIn reflSingle.Ψ reflDiag reflV.zeroFunctor := by
  have hf := reflQ.modelFred reflSingle.Ψ isScFredholmSectionFunctor_reflDiag
  change IsInGeneralPosition reflSingleModel (reflQ.modelSection reflSingle.Ψ reflDiag)
    (reflQ.bundlePull reflSingle.Ψ reflV.zeroFunctor)
  rw [reflQ.bundlePull_zeroFunctor]
  refine (isInGeneralPosition_iff_forall_at hf (isScPlusMultisection_zeroMultisection _)).2 ?_
  rintro ⟨⟨⟩, q⟩ hq
  obtain rfl := eq_zero_of_zeroMultisection_reflSingleModel_pos hq
  exact isInGeneralPositionAt_reflSingleModel_zero

/-- **The orientation clause of Theorem 18.6.1 (p. 861) with a non-empty `Θ`**: for the diagonal
section `f(x) = (x, x)` of the reflection bundle and the trivial multisection functor `Λ₀`, all
hypotheses of `theorem_18_6_1_oriented` hold, `Θ = Λ₀ ∘ f` has support exactly `{0}`
(`Θ(0) = 1`, the point with isotropy `ℤ/2`), and `Θ` carries the canonical orientation. -/
theorem theorem_18_6_1_oriented_witness_support :
    ∃ (N : reflV.EObj → ℝ≥0∞) (U : Set GCT.reflection.toGroupoidStr.OrbitSpace),
      reflQ.IsAuxNormFunctor N ∧ reflDiag.ControlsCompactness N U ∧
      IsMorInvariant reflV.zeroFunctor ∧
      reflQ.IsScPlusMultisectionIn reflSingle.Ψ reflV.zeroFunctor ∧
      (∀ α, pointwiseNormFunctor N reflV.zeroFunctor α ≤ 1) ∧ orbitDomSupp reflV.zeroFunctor ⊆ U ∧
      reflQ.IsInGeneralPositionIn reflSingle.Ψ reflDiag reflV.zeroFunctor ∧
      ∃ o, reflQ.IsOrientation isScFredholmSectionFunctor_reflDiag
        reflection_admitsModelBumpFunctions reflectionConstruction_isTame
        isScFredholmSectionFunctorTame_reflDiag reflQ_hasStrongBundleUniformizers o ∧
      ∃ O : reflectionConstruction.OrientedSubcategory,
        O.Θ = (fun α => (reflV.zeroFunctor (reflDiag.toFun α) : ℚ)) ∧
        (∀ α, 0 < O.Θ α ↔ α = 0) ∧ O.Θ 0 = 1 ∧
        (∀ x ∈ reflSingleModel.X.PObj.smoothSet,
          O.T reflSingle.base x = canonicalOrientation (A := reflSingleModel)
            (reflQ.bundlePull reflSingle.Ψ reflV.zeroFunctor)
            (reflQ.modelFred reflSingle.Ψ isScFredholmSectionFunctor_reflDiag).2
            (reflQ.modelSec reflection_admitsModelBumpFunctions reflSingle)
            (reflQ.pullCat isScFredholmSectionFunctor_reflDiag
              reflection_admitsModelBumpFunctions reflQ_hasStrongBundleUniformizers reflSingle o)
            x) ∧
        IsCanonicalFor (A := reflSingleModel) (reflQ.bundlePull reflSingle.Ψ reflV.zeroFunctor)
          (reflQ.modelFred reflSingle.Ψ isScFredholmSectionFunctor_reflDiag).2
          (reflQ.modelSec reflection_admitsModelBumpFunctions reflSingle)
          (reflQ.pullCat isScFredholmSectionFunctor_reflDiag
            reflection_admitsModelBumpFunctions reflQ_hasStrongBundleUniformizers reflSingle o) 0
          (canonicalOrientation (A := reflSingleModel)
            (reflQ.bundlePull reflSingle.Ψ reflV.zeroFunctor)
            (reflQ.modelFred reflSingle.Ψ isScFredholmSectionFunctor_reflDiag).2
            (reflQ.modelSec reflection_admitsModelBumpFunctions reflSingle)
            (reflQ.pullCat isScFredholmSectionFunctor_reflDiag
              reflection_admitsModelBumpFunctions reflQ_hasStrongBundleUniformizers reflSingle
              o)) := by
  obtain ⟨hT, hb, hf, hfT, -, -, -⟩ := reflDiag_orientation_hyp
  obtain ⟨⟨N, hN⟩, hU⟩ := reflDiag_stronglyControlsCompactness
  obtain ⟨U, hU⟩ := hU N hN
  have hN1 : ∀ α, pointwiseNormFunctor N reflV.zeroFunctor α ≤ 1 := fun α => by
    rw [pointwiseNormFunctor_reflV_zeroFunctor_eq_zero hN α]
    exact zero_le_one
  have hdom : orbitDomSupp reflV.zeroFunctor ⊆ U := by
    rw [orbitDomSupp_reflV_zeroFunctor]
    exact empty_subset _
  obtain ⟨o, ho⟩ := reflDiag_isOrientable
  obtain ⟨O, hΘ, hT1, hT2⟩ := theorem_18_6_1_oriented reflSingle hT hb hf hfT
    reflQ_hasStrongBundleUniformizers ho hN hU.controlsCompactness isMorInvariant_zeroFunctor
    isScPlusMultisectionIn_reflV_zeroFunctor hN1 hdom isInGeneralPositionIn_reflDiag_zeroFunctor
    (n := 0) (fun x _ => isIndexAt_reflSingleModel x)
  have hpos : ∀ α, 0 < O.Θ α ↔ α = 0 := fun α => by
    rw [hΘ]
    exact NNRat.cast_pos.trans (zeroFunctor_reflDiag_pos_iff α)
  have h0 : O.Θ 0 = 1 := by
    classical
    rw [hΘ]
    change ((if reflV.objMk 0 0 = reflV.objMk 0 0 then 1 else 0 : ℚ≥0) : ℚ) = 1
    rw [if_pos rfl, NNRat.cast_one]
  exact ⟨N, U, hN, hU.controlsCompactness, isMorInvariant_zeroFunctor,
    isScPlusMultisectionIn_reflV_zeroFunctor, hN1, hdom, isInGeneralPositionIn_reflDiag_zeroFunctor,
    o, ho, O, hΘ, hpos, h0, hT1, hT2⟩

end GCT.VectorBundle.ReflectionBundle

end Polyfold
