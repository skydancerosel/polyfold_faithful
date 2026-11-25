import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V18_41

set_option maxSynthPendingDepth 3

/-! Round trip for V18_41 (2021 Theorem 18.4.4, pp. 855–856; 2017: Theorem 18.7), the
∂-extension theorem.

`A` is the conjunction of the types of the item's eleven theorems (the four general ones at
universe `0`; the definitions are vocabulary).  The main conjunct is `theorem_18_4_4_modelFree`.

**`B` does not hold** (`not_B`).  `B` takes the auxiliary norm in the form `IsAuxNormBook`
(Definition 18.1.7's printed clauses, without the continuity of `|N|` on `|E_{0,1}|`).  Such a
norm may jump across `|∂C|`: on the half-space bundle `ℤ/2 ⋉ (H × ℝ) → ℤ/2 ⋉ H`
(`HalfSpaceReflection`), `N(α, w) = a(|α|)·|w|` with `a = 1` on `|∂C|` and `a = 2` elsewhere
satisfies `IsAuxNormBook` (`IsAuxNormBook.baseScale`).  Take `Λ = Λ_v` (`v = −3/4`, the constant
section's multisection, structurable over `∂C`), `U = |C|`, `β = 1`: all hypotheses of `B` hold
(`N(Λ) = 3/4 < 1` on `∂C`).  A structurable `Λ'` with `Λ' = Λ` on `∂C` has, in the model
`halfSingle`, a continuous pointwise norm `|·|(Γ̄^*Λ')` (`continuous_pointwiseNorm`), which is
`≥ 3/4` at the corner; at the interior points `(|t|, 0)` the bound `N(Λ') ≤ 1` forces it
`≤ 1/2`.  Continuity at `t = 0` gives the contradiction.

Other differences, independent of the norm: `B` asks `N(Λ) < β` at every object of `∂C`
(forcing `β > 0` on `∂C`), `A` only over `|dom-supp(Λ)|`; `B` assumes
`Q.HasStrongBundleUniformizers`, `A` does not; `B` uses Definition 18.4.1's partitions of unity
in the ep-groupoid sense (`AdmitsModelPartitionsOfUnity`, saturated covers), `A` the M-polyfold
partitions of unity of a covering model (`HasModelMPolyfoldPartitionsOfUnity`), which give the
former (`remark_18_4_2`) but are not known to follow from it.  `A_to_B` is not provable (`A`
holds, `B` does not); `B_to_A` holds only vacuously (by `not_B`) and is not included. -/

namespace RoundTrip.V18_41
open Set Filter Topology
open Polyfold Polyfold.HalfSpaceBundle Polyfold.GCT.VectorBundle
open Polyfold.GCT.VectorBundle.HalfSpaceReflection
open Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction

/-- The project's statement (the general theorems at universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_4_4.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_4_4_modelFree.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.IsBoundaryStructurableIn.of_comparison.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isBoundaryStructurableFunctor_iff.{0}) ∧
  (type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_4_4_witness) ∧
  (type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_4_4_modelFree_witness) ∧
  (type_of% @Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_hasModelMPolyfoldPartitionsOfUnity) ∧
  (type_of% @Polyfold.GCT.VectorBundle.HalfSpaceReflection.halfQ_hasModelMPolyfoldPartitionsOfUnity) ∧
  (type_of% @Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_4_4_modelFree_witness_boundary) ∧
  (type_of% @Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_4_4_modelFree_witness_constDatum) ∧
  (type_of% @Polyfold.GCT.VectorBundle.HalfSpaceReflection.isBoundaryStructurableFunctor_constFunctor)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_4_4.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_4_4_modelFree.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.IsBoundaryStructurableIn.of_comparison.{0},
    @Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isBoundaryStructurableFunctor_iff.{0},
    @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_4_4_witness,
    @Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_4_4_modelFree_witness,
    @Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_hasModelMPolyfoldPartitionsOfUnity,
    @Polyfold.GCT.VectorBundle.HalfSpaceReflection.halfQ_hasModelMPolyfoldPartitionsOfUnity,
    @Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_4_4_modelFree_witness_boundary,
    @Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_4_4_modelFree_witness_constDatum,
    @Polyfold.GCT.VectorBundle.HalfSpaceReflection.isBoundaryStructurableFunctor_constFunctor⟩

/-- `Λ_v` is structurable over `∂C` (the project's proof of
`isBoundaryStructurableFunctor_constFunctor`, an item theorem, copied from non-item lemmas). -/
theorem isBSF_constFunctor (v : Fin 1 → ℝ) :
    halfQ.IsBoundaryStructurableFunctor (constFunctor v) := by
  refine ⟨isMorInvariant_constFunctor v, halfSingle, ?_⟩
  change SBLocalization.IsBoundaryStructurable (halfQ.modelSEP halfSingle.Ψ)
    (halfQ.bundlePull halfSingle.Ψ (constFunctor v))
  have hW := halfQ.isWFunctor_bundlePull halfSingle.Ψ (isMorInvariant_constFunctor v)
  rw [bundlePull_constFunctor] at hW ⊢
  exact SBLocalization.isBoundaryStructurable_sectionMulti_of_isWFunctor
    (isScPlusSection_modelConstSec v) hW
    (halfS.isTame_modelEpGroupoid (Ψ := halfQ.modelBase halfSingle.Ψ) halfS_isTame)
    (halfQ.hasParacompactOrbitSpace_model halfSingle)

open Classical in
/-- `a = 1` on `|∂C|`, `a = 2` elsewhere. -/
noncomputable def jumpA (z : halfC.toGroupoidStr.OrbitSpace) : ℝ :=
  if z ∈ halfC.toGroupoidStr.π '' halfS.boundarySet then 1 else 2

theorem one_le_jumpA (z) : 1 ≤ jumpA z := by
  unfold jumpA; split_ifs <;> norm_num

theorem jumpA_of_mem {α : halfC.Obj} (h : α ∈ halfS.boundarySet) :
    jumpA (halfC.toGroupoidStr.π α) = 1 := if_pos ⟨α, h, rfl⟩

theorem jumpA_of_not_mem {α : halfC.Obj} (h : α ∉ halfS.boundarySet) :
    jumpA (halfC.toGroupoidStr.π α) = 2 := by
  refine if_neg fun h' => h ?_
  rw [← halfS.isSaturated_boundarySet]
  exact h'

/-- `N(α, w) = a(|α|) · |w|`. -/
noncomputable def Nj : halfV.EObj → ENNReal := halfV.baseScale jumpA halfNorm

theorem isAuxNormBook_Nj : halfQ.IsAuxNormBook Nj :=
  isAuxNormIn_halfNorm.isAuxNormBook.baseScale one_le_jumpA

theorem Nj_objMk (α : halfC.Obj) (w : Fin 1 → ℝ) :
    Nj (halfV.objMk α w) = ENNReal.ofReal (jumpA (halfC.toGroupoidStr.π α)) * ENNReal.ofReal ‖w‖ :=
  rfl

theorem norm_constDatum : ‖constDatum‖ = 3 / 4 := by
  rw [norm_fin_one]; norm_num [constDatum]

theorem pnf_le {Λ : halfV.EObj → ℚ≥0} {α : halfC.Obj} {r : ℝ}
    (h : ∀ w : Fin 1 → ℝ, 0 < Λ (halfV.objMk α w) → ENNReal.ofReal ‖w‖ ≤ ENNReal.ofReal r) :
    pointwiseNormFunctor halfNorm Λ α ≤ ENNReal.ofReal r :=
  sSup_le (by rintro _ ⟨w, hw, rfl⟩; exact h w hw)

theorem not_B : ¬ B := by
  intro hB
  have hPU : halfS.AdmitsModelPartitionsOfUnity :=
    ⟨halfQ.baseCoveringFamily halfSingle,
      (halfS.remark_18_4_2 _).2.2 halfModel_admitsScPartitionsOfUnity⟩
  obtain ⟨Λ', hst, hle, -, heq⟩ := hB halfC halfS halfV halfQ halfQ_hasStrongBundleUniformizers
    halfS_isTame hPU Nj isAuxNormBook_Nj (constFunctor constDatum)
    (isBSF_constFunctor _) univ isOpen_univ (subset_univ _)
    (fun _ => 1) ⟨fun _ => rfl, fun _ => continuous_const⟩ (fun _ => zero_le_one)
    (subset_univ _) (by
      intro α hα
      rw [pointwiseNormFunctor_constFunctor, Nj_objMk, jumpA_of_mem hα, norm_constDatum,
        ENNReal.ofReal_one, one_mul]
      exact ENNReal.ofReal_lt_one.2 (by norm_num))
  -- `|w| ≤ N(Λ')(α)/a(|α|)` for charged `w`
  have hcharged : ∀ (α : halfC.Obj) (w : Fin 1 → ℝ), 0 < Λ' (halfV.objMk α w) →
      ENNReal.ofReal (jumpA (halfC.toGroupoidStr.π α)) * ENNReal.ofReal ‖w‖ ≤ ENNReal.ofReal 1 :=
    fun α w hw => le_trans (le_sSup (s := (fun v => Nj (halfV.objMk α v)) ''
      {v | 0 < Λ' (halfV.objMk α v)}) ⟨w, hw, rfl⟩) (hle α)
  have hle1 : ∀ α : halfC.Obj, pointwiseNormFunctor halfNorm Λ' α ≤ ENNReal.ofReal 1 := by
    intro α
    refine pnf_le fun w hw => le_trans ?_ (hcharged α w hw)
    refine le_mul_of_one_le_left zero_le ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_jumpA _)
  have hhalf : ∀ α : halfC.Obj, α ∉ halfS.boundarySet →
      pointwiseNormFunctor halfNorm Λ' α ≤ ENNReal.ofReal (1 / 2) := by
    intro α hα
    refine pnf_le fun w hw => ?_
    have h := hcharged α w hw
    rw [jumpA_of_not_mem hα, ← ENNReal.ofReal_mul (by norm_num)] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff zero_le_one).1 h
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hcorner : ENNReal.ofReal (3 / 4) ≤ pointwiseNormFunctor halfNorm Λ' corner := by
    have hpos : 0 < Λ' (halfV.objMk corner constDatum) := by
      rw [heq _ corner_mem_boundarySet, constFunctor_objMk, if_pos rfl]
      exact one_pos
    have := le_sSup (s := (fun v => halfNorm (halfV.objMk corner v)) ''
      {v | 0 < Λ' (halfV.objMk corner v)}) ⟨constDatum, hpos, rfl⟩
    change halfNorm (halfV.objMk corner constDatum) ≤ pointwiseNormFunctor halfNorm Λ' corner at this
    rw [halfNorm_objMk, norm_constDatum] at this
    exact this
  -- the model
  have hm := ((halfQ.remark_18_3_4 halfSingle).1 hst).2.1
  have hcont := hm.continuous_pointwiseNorm isAuxNormIn_halfNorm.isAuxNorm.isAuxNorm.continuous
  set f : (halfQ.modelSEP halfSingle.Ψ).Obj → ℝ := fun x =>
    (pointwiseNormFunctor halfNorm Λ' ((halfS.modelFunctor (halfQ.modelBase halfSingle.Ψ)).obj x)).toReal
    with hf
  have hfeq : f = SBLocalization.pointwiseNorm (halfQ.modelNorm halfSingle.Ψ halfNorm)
      (halfQ.bundlePull halfSingle.Ψ Λ') := by
    funext x
    exact halfQ.pointwiseNorm_bundlePull_of_ne_top isAuxNormIn_halfNorm Λ' x
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle1 _))
  rw [← hfeq] at hcont
  -- the path `t ↦ (|t|, 0)`
  let p : ℝ → (halfQ.modelSEP halfSingle.Ψ).Obj := fun t =>
    ⟨(), ⟨(((fun _ => |t|), (0 : Fin 1 → ℝ)) : Pm 1), fun _ => abs_nonneg t⟩⟩
  have hp : Continuous p := by
    refine continuous_sigmaMk.comp (Continuous.subtype_mk ?_ _)
    exact (continuous_pi fun _ => continuous_abs).prodMk continuous_const
  have hp0 : p 0 = ⟨(), corner⟩ := by
    refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
    change (((fun _ => |(0:ℝ)|), (0 : Fin 1 → ℝ)) : Pm 1) = 0
    ext i <;> simp
  have hf0 : 3 / 4 ≤ f (p 0) := by
    rw [hp0]
    change 3 / 4 ≤ (pointwiseNormFunctor halfNorm Λ' corner).toReal
    have := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle1 _)) hcorner
    rwa [ENNReal.toReal_ofReal (by norm_num)] at this
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 5 / 8 < f (p t) :=
    (hcont.comp hp).continuousAt.eventually (lt_mem_nhds (by linarith : (5 / 8 : ℝ) < f (p 0)))
  obtain ⟨t, ht, ht0⟩ := (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin |>.exists
    (f := 𝓝[>] (0 : ℝ))
  have hnb : (⟨(((fun _ => |t|), (0 : Fin 1 → ℝ)) : Pm 1), fun _ => abs_nonneg t⟩ : H 1) ∉
      halfS.boundarySet := by
    rw [mem_boundarySet_iff]
    change |t| ≠ 0
    exact abs_ne_zero.2 (ne_of_gt ht0)
  have h2 := hhalf _ hnb
  have : f (p t) ≤ 1 / 2 := by
    change (pointwiseNormFunctor halfNorm Λ' _).toReal ≤ 1 / 2
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rwa [ENNReal.toReal_ofReal (by norm_num)] at this
  linarith


#rt_check RoundTrip.V18_41.not_B
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_4_4,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_4_4_modelFree,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.IsBoundaryStructurableIn.of_comparison,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isBoundaryStructurableFunctor_iff,
   Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_4_4_witness,
   Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_4_4_modelFree_witness,
   Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_hasModelMPolyfoldPartitionsOfUnity,
   Polyfold.GCT.VectorBundle.HalfSpaceReflection.halfQ_hasModelMPolyfoldPartitionsOfUnity,
   Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_4_4_modelFree_witness_boundary,
   Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_4_4_modelFree_witness_constDatum,
   Polyfold.GCT.VectorBundle.HalfSpaceReflection.isBoundaryStructurableFunctor_constFunctor]
#rt_overlap RoundTrip.V18_41.not_B
  [Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_4_4,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_4_4_modelFree,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.IsBoundaryStructurableIn.of_comparison,
   Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.isBoundaryStructurableFunctor_iff,
   Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_4_4_witness,
   Polyfold.GCT.VectorBundle.ReflectionBundle.theorem_18_4_4_modelFree_witness,
   Polyfold.GCT.VectorBundle.ReflectionBundle.reflQ_hasModelMPolyfoldPartitionsOfUnity,
   Polyfold.GCT.VectorBundle.HalfSpaceReflection.halfQ_hasModelMPolyfoldPartitionsOfUnity,
   Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_4_4_modelFree_witness_boundary,
   Polyfold.GCT.VectorBundle.HalfSpaceReflection.theorem_18_4_4_modelFree_witness_constDatum,
   Polyfold.GCT.VectorBundle.HalfSpaceReflection.isBoundaryStructurableFunctor_constFunctor]

end RoundTrip.V18_41
