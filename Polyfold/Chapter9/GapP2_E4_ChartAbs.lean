import Polyfold.Chapter9.GapP2_E3_Density

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes", pp. 438–445 (gap G.107).  Numbers and pages
are the 2021 text's.

# The integral of `|ω|` over a piece of a sheet in a graph chart

For an evaluation of forms `F : X.FormEval n Ω` and a graph chart `c` of an `n`-dimensional
submanifold `N` (`GapP2_E3_GraphChart.lean`), `F.chartAbs c ω A = ∫_{c(A ∩ N)} |ω(∂₁, …, ∂ₙ)|`.
This is the total variation of the integrals `∫_B ω|(N, o)`, `B ⊆ A`, and it does not depend
on the graph chart:

* `abs_chartInteg_le`: `|∫_A ω|(N, o)| ≤ ∫_A |ω|` in every chart;
* `chartAbs_congr`: two graph charts of two sheets give the same `∫_A |ω|` on a common
  measurable set where their tangent spaces agree (the change of variables of
  `GraphChart.setIntegral_coord_image_eq`, with `|ω(β)| = |det| · |ω(α)|`);
* `chartAbs_mapDiffeo`: invariance under the sc-diffeomorphisms whose tangent maps are those of
  morphisms;
* `chartAbs_mono`, `chartAbs_hasSum`: monotone and countably additive.

These are used to integrate over sheets which do not lie in one graph chart
(`GapP2_E4_MultiChart.lean`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {n : ℕ} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] (F : X.FormEval n Ω)

namespace FormEval

variable {N N' : Set Obj}

/-- **`∫_A |ω|` in the graph chart `c` of `N`**: `∫_{c(A ∩ N)} |ω(c.tvec)|`. -/
def chartAbs (c : X.PObj.GraphChart n N) (ω : Ω) (A : Set Obj) : ℝ :=
  ∫ u in c.coord '' (A ∩ N), |F.ev ω (c.tvec (c.q u))|

theorem chartAbs_nonneg (c : X.PObj.GraphChart n N) (ω : Ω) (A : Set Obj) :
    0 ≤ F.chartAbs c ω A :=
  integral_nonneg fun _ => abs_nonneg _

/-- `|∫_A ω|(N, g)| ≤ ∫_A |ω|` in every graph chart, for every field `g` of oriented tangent
spaces. -/
theorem abs_chartInteg_le (c : X.PObj.GraphChart n N) (ω : Ω) (g : Obj → X.PObj.OrTangent)
    (A : Set Obj) : |F.chartInteg c ω g A| ≤ F.chartAbs c ω A := by
  unfold chartInteg chartAbs
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext u
  rw [Real.norm_eq_abs, abs_density]

theorem chartAbs_mono (c : X.PObj.GraphChart n N) (ω : Ω)
    (hint : IntegrableOn (fun u => F.ev ω (c.tvec (c.q u))) c.dom volume) {A B : Set Obj}
    (h : A ∩ N ⊆ B) : F.chartAbs c ω A ≤ F.chartAbs c ω B := by
  unfold chartAbs
  refine setIntegral_mono_set (IntegrableOn.mono_set (f := fun u => |F.ev ω (c.tvec (c.q u))|) (t := c.dom) (Integrable.abs hint) (image_mono inter_subset_right))
    (Eventually.of_forall fun _ => abs_nonneg _) ?_
  exact (image_mono (subset_inter h inter_subset_right)).eventuallyLE

/-- **Countable additivity of `∫ |ω|`.** -/
theorem chartAbs_hasSum (c : X.PObj.GraphChart n N) (ω : Ω)
    (hint : IntegrableOn (fun u => F.ev ω (c.tvec (c.q u))) c.dom volume) (A : ℕ → Set Obj)
    (hAm : ∀ k, NullMeasurableSet (c.coord '' (A k ∩ N)) volume)
    (hd : Pairwise (Function.onFun Disjoint A)) :
    HasSum (fun k => F.chartAbs c ω (A k)) (F.chartAbs c ω (⋃ k, A k)) := by
  have himg : c.coord '' ((⋃ k, A k) ∩ N) = ⋃ k, c.coord '' (A k ∩ N) := by
    rw [iUnion_inter, image_iUnion]
  unfold chartAbs
  rw [himg]
  refine hasSum_integral_iUnion_ae hAm (fun i j hij => Disjoint.aedisjoint ?_) ?_
  · refine disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have : b = a := c.injOn_coord hb.2 ha.2 hab
    subst this
    exact disjoint_left.1 (hd hij) ha.1 hb.1
  · exact IntegrableOn.mono_set (f := fun u => |F.ev ω (c.tvec (c.q u))|) (t := c.dom) (Integrable.abs hint) (iUnion_subset fun k => image_mono inter_subset_right)

/-- **`∫_A |ω|` does not depend on the graph chart**: two graph charts of two `n`-dimensional
sheets give the same value on a common measurable subset where the tangent spaces agree. -/
theorem chartAbs_congr (hN : X.PObj.IsSubmanifoldOfDim N n)
    (hN' : X.PObj.IsSubmanifoldOfDim N' n) (c : X.PObj.GraphChart n N)
    (c' : X.PObj.GraphChart n N') (ω : Ω) {A : Set Obj} (hA : A ⊆ N ∩ N')
    (hAm : NullMeasurableSet (c.coord '' A) volume)
    (hT : ∀ y ∈ A, X.PObj.submanifoldTangent N y = X.PObj.submanifoldTangent N' y) :
    F.chartAbs c ω A = F.chartAbs c' ω A := by
  have hAN : A ∩ N = A := inter_eq_left.2 fun y hy => (hA hy).1
  have hAN' : A ∩ N' = A := inter_eq_left.2 fun y hy => (hA hy).2
  unfold chartAbs
  rw [hAN, hAN']
  refine (MPolyfold.GraphChart.setIntegral_coord_image_eq c c' hN.1 hA hAm hT
    (ρ := fun y => |F.ev ω (c.tvec y)|) (ρ' := fun y => |F.ev ω (c'.tvec y)|)
    fun y hy D hD => ?_).symm
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => D (MPolyfold.GraphChart.bvec j) i
    with hM
  have hdet : M.det = D.det := MPolyfold.GraphChart.det_matrix_bvec D
  have hmem : ∀ i, c.tvec y i ∈ X.PObj.submanifoldTangent N' y := fun i =>
    hT y hy ▸ c.tvec_mem (hA hy).1 i
  have hev : F.ev ω (c.tvec y) = M.det * F.ev ω (c'.tvec y) :=
    F.ev_det ω hN'.1 (hA hy).2 c'.isChart (c'.subset_source (hA hy).2) (c'.tvec y) (c.tvec y)
      (c'.tvec_mem (hA hy).2) hmem M hD
  change |F.ev ω (c.tvec y)| = |D.det| * |F.ev ω (c'.tvec y)|
  rw [hev, abs_mul, hdet]

/-- **`∫ |ω|` is invariant under the sc-diffeomorphisms whose tangent maps are those of
morphisms.** -/
theorem chartAbs_mapDiffeo (hN : X.PObj.IsSmoothSubmanifold N) (c : X.PObj.GraphChart n N)
    {f f' : Obj → Obj} {U U' : Set Obj} (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U')
    (hNU : N ⊆ U) (hmor : X.IsMorTangentOn hf N) (ω : Ω) {A : Set Obj} (hA : A ⊆ N)
    (hAm : NullMeasurableSet (c.coord '' A) volume) :
    F.chartAbs (c.mapDiffeo hN hf hNU) ω (f '' A) = F.chartAbs c ω A := by
  have hAN : A ∩ N = A := inter_eq_left.2 hA
  have hAN' : f '' A ∩ f '' N = f '' A := inter_eq_left.2 (image_mono hA)
  have himg : (c.mapDiffeo hN hf hNU).coord '' (f '' A) = c.coord '' A := by
    rw [image_image]
    exact image_congr fun y hy => c.mapDiffeo_coord hN hf hNU (hA hy)
  unfold chartAbs
  rw [hAN, hAN', himg]
  refine setIntegral_congr_ae₀ hAm (Eventually.of_forall ?_)
  rintro _ ⟨y, hy, rfl⟩
  have hyN := hA hy
  change |F.ev ω ((c.mapDiffeo hN hf hNU).tvec (f (c.q (c.coord y))))| =
    |F.ev ω (c.tvec (c.q (c.coord y)))|
  rw [c.q_coord' hyN]
  have htv : (c.mapDiffeo hN hf hNU).tvec (f y) =
      fun i => MPolyfold.tangentMapOn hf.isScSmoothOn (c.tvec y i) :=
    funext fun i => c.mapDiffeo_tvec hN hf hNU hyN i
  rw [htv, F.ev_tangentMapOn hN hf hmor ω hyN (c.tvec y) (c.tvec_mem hyN)]

end FormEval

end EpGroupoid

end Polyfold
