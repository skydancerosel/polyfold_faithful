import Polyfold.Chapter15.CanonicalLift
import Polyfold.Chapter9.MathlibSolutionSets
import Polyfold.Chapter9.OrientationBasic
import Polyfold.Chapter11.BranchedEquivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702 (before **Theorem 15.4.1**; 2017: before Theorem 15.6): the tangent space of a branch
`Mᵢ = {f = sᵢ}` is the kernel of `(f − sᵢ)'(y)`.

# `T_yMᵢ = ker (f − sᵢ)'(y)`

## The text, paraphrased

(pp. 701–702) For `y ∈ supp(Λ ∘ f)` the operators `(f − sᵢ)'(y)` with `f(y) = sᵢ(y)` are onto, and
the orientation `o_{i,y}` they inherit from `o` orients `ker (f − sᵢ)'(y)`, the tangent space
`T_yMᵢ` of the solution set `Mᵢ` of `f = sᵢ`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`exists_branch_tangent_eq_ker`**: for a local sc⁺-section `s` on the open set `O` and a point
  `x ∈ O` with `f(x) = s(x)` at which the branch `(f − s)|O` is in good position (Part I's
  Definition 3.6.6 in a tame chart), there are an open `V ∋ x` in `O` and `d` such that
  `M = {y ∈ V | f(y) = s(y)}` is a `d`-dimensional submanifold of `X` (Remark 9.1.1), and at every
  `y ∈ M`, in every strong bundle chart `c` with domain in `O`, the chart vectors of `T_yM`
  (Chapter 9's `submanifoldTangent`) are the kernel of `D((f̂ − ŝ) ∘ r)(z)` on `T_zO`.
* `kerSet`, `kerSet_eq_coe_map_ker`: that kernel as a set and as the image in `E₀` of the kernel
  of `subOp` (the operator `(f − s)'(y) : T_zO → K_z` of Theorem 15.4.1 in a chart point).

The proof transports Part I's `exists_tangentSpace_eq_linKer` (Theorem 3.6.8) and
`theorem_3_6_8_isSubmanifoldOfDim` from `W|O` to `X` along the inclusion `O → X`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-- **The kernel of `(f − s)'(y)` in the chart `c`** at the level-`1` point `z`: the vectors of
`T_zO` annihilated by `D((f̂ − ŝ) ∘ r)(z)`. -/
def kerSet (c : StrongBundleChart A.X.PObj A.P) (f s : A.Obj → A.W) (z : c.φ.model.E 1) :
    Set (c.φ.model.E 0) :=
  {v | v ∈ rangeS (scDeriv c.U (r c.R) z) ∧ subDeriv c f s z v = 0}

/-- **`kerSet` is the image in `E₀` of the kernel of `subOp`** in a chart point. -/
theorem kerSet_eq_coe_map_ker {f s : A.Obj → A.W} {O : Set A.Obj} {y : A.Obj}
    (hf : A.B.IsScSmoothSection f) (hs : IsScPlusSectionOn A s O) (p : ChartPoint A.B y)
    (hsub : p.c.φ.source ⊆ O) (hfs : f y = s y) :
    kerSet p.c f s p.z =
      ((LinearMap.ker ((subOp hf hs p hsub hfs : ↥p.T →L[ℝ] ↥p.K) : ↥p.T →ₗ[ℝ] ↥p.K)).map
        (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) : Set (p.c.φ.model.E 0)) := by
  ext v
  constructor
  · rintro ⟨hv, h0⟩
    refine ⟨⟨v, hv⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact Subtype.ext h0
  · rintro ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hw
    exact ⟨w.2, congrArg Subtype.val hw⟩

section Restrict

variable {O : Set A.Obj} (hO : IsOpen O) [Nonempty O] [ParacompactSpace O]
  [ParacompactSpace (pullbackSpace A.P (Subtype.val : O → A.Obj))]

include hO in
/-- **`T_yM = ker (f − s)'(y)` near a point of good position** (2021 pp. 701–702; Part I's
Theorem 3.6.8 on `W|O`): if `(f − s)|O` is in good position at `x`, `f(x) = s(x)`, there are an
open `V ∋ x` inside `O` and `d` such that `M = {y ∈ V | f(y) = s(y)}` is a `d`-dimensional
submanifold of `X`, its points are smooth, the branch is in good position at each of them, and in
every strong bundle chart `c` with domain in `O` around `y ∈ M`, at the level-`1` point `z` over
`φ(y)`, the chart vectors of `T_yM` are the kernel of `D((f̂ − ŝ) ∘ r)(z)` on `T_zO`. -/
theorem exists_branch_tangent_eq_ker {f : A.Obj → A.W} (hft : A.B.IsScFredholmSectionTame f)
    {s : A.Obj → A.W} (hs : IsScPlusSectionOn A s O) {x : A.Obj} (hxO : x ∈ O) (hfs : f x = s x)
    (hgp : (A.B.restrictOpen hO).IsGoodPositionGermTame (subRestrict (O := O) f s hft.isScSmooth.1)
      ⟨x, hxO⟩) :
    ∃ (V : Set A.Obj) (d : ℕ), IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
      A.X.PObj.IsSubmanifoldOfDim {y ∈ V | f y = s y} d ∧
      ∀ y ∈ V, f y = s y → y ∈ A.X.PObj.smoothSet ∧
        (∀ hyO : y ∈ O, (A.B.restrictOpen hO).IsGoodPositionGermTame
          (subRestrict (O := O) f s hft.isScSmooth.1) ⟨y, hyO⟩) ∧
        ∀ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c → c.φ.source ⊆ O →
          y ∈ c.φ.source → ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y →
            chartVec c.isChart '' A.X.PObj.submanifoldTangent {y ∈ V | f y = s y} y =
              kerSet c f s z := by
  have hf := hft.isScSmooth.1
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs
  have hzero : ∀ y : O, IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
      (subRestrict (O := O) f s hf) y ↔ f y.1 = s y.1 := fun y => by
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact isZeroAt_subSec_iff hf hs.1 y.2
  have hx0 := (hzero ⟨x, hxO⟩).2 hfs
  obtain ⟨Va, hVao, hxVa, hgoodA, htan⟩ := exists_tangentSpace_eq_linKer hgO hgp hx0
  obtain ⟨Vb, d, hVbo, hxVb, -, hdimB⟩ := theorem_3_6_8_isSubmanifoldOfDim hgO hgp hx0
  set g := subRestrict (O := O) f s hf with hg
  set W : Set O := Va ∩ Vb with hW
  have hWo : IsOpen W := hVao.inter hVbo
  have hSW : solutionSet (pullbackProj A.P (Subtype.val : O → A.Obj)) g ∩ W =
      solutionSet (pullbackProj A.P (Subtype.val : O → A.Obj)) g ∩ Vb ∩ Va := by
    ext v; simp only [hW, mem_inter_iff]; tauto
  have hdimW : (A.X.PObj.restrictOpen hO).IsSubmanifoldOfDim
      (solutionSet (pullbackProj A.P (Subtype.val : O → A.Obj)) g ∩ W) d := by
    rw [hSW]; exact hdimB.inter_isOpen hVao
  have himg := hdimW.image_isScDiffeoOn
    (MPolyfold.isScDiffeoOn_subtypeVal (P := A.X.PObj) hO) (subset_univ _)
  have hM : {y ∈ Subtype.val '' W | f y = s y} =
      Subtype.val '' (solutionSet (pullbackProj A.P (Subtype.val : O → A.Obj)) g ∩ W) := by
    ext y
    constructor
    · rintro ⟨⟨v, hvW, rfl⟩, hfy⟩; exact ⟨v, ⟨(hzero v).2 hfy, hvW⟩, rfl⟩
    · rintro ⟨v, ⟨hv0, hvW⟩, rfl⟩; exact ⟨⟨v, hvW, rfl⟩, (hzero v).1 hv0⟩
  refine ⟨Subtype.val '' W, d, hO.isOpenMap_subtype_val W hWo, ⟨⟨x, hxO⟩, ⟨hxVa, hxVb⟩, rfl⟩,
    ?_, hM ▸ himg, ?_⟩
  · rintro _ ⟨v, -, rfl⟩; exact v.2
  rintro _ ⟨v, hvW, rfl⟩ hfy
  have hv0 := (hzero v).2 hfy
  have hys : v.1 ∈ A.X.PObj.smoothSet := (MPolyfold.mem_smoothSet_restrictOpen_iff hO v).1
    (hgO.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hv0)
  refine ⟨hys, fun _ => hgoodA v hvW.1 hv0, fun c hc hsub hyc z hz => ?_⟩
  set M : Set A.Obj := {y ∈ Subtype.val '' W | f y = s y} with hMdef
  have hM1 : A.X.PObj.IsSmoothSubmanifold M := (hM ▸ himg).1
  have hyM : v.1 ∈ M := ⟨⟨v, hvW, rfl⟩, hfy⟩
  set dd := hM1.data hyM with hdd
  have hyV : v.1 ∈ dd.V := hM1.mem_data_V hyM
  have hy1 : v.1 ∈ A.X.PObj.levelSet 1 := smoothSet_subset_levelSet 1 hys
  have hzl : levelLift c.φ 1 v.1 = z :=
    c.φ.model.E.toBase_injective 1 ((A.X.PObj.toBase_levelLift c.isChart hyc hy1).trans hz.symm)
  rw [chartVec_image_submanifoldTangent c.isChart dd hyM hyV hyc, hzl]
  set q₀ := g v with hq₀
  have hc' : (A.B.restrictOpen hO).IsChart (c.restrictTo A.B.continuous hO hsub q₀) :=
    restrictOpen_isChart_restrictTo hO hc hsub q₀
  set G : Set O := Subtype.val ⁻¹' (dd.toSubData.shrink c.φ) ∩ W with hG
  have hGo : IsOpen G :=
    ((dd.toSubData.isOpen_shrink c.φ).preimage continuous_subtype_val).inter hWo
  have hvG : v ∈ G := ⟨dd.toSubData.mem_shrink c.φ hyM hyV hyc, hvW⟩
  have himgeq : (c.restrictTo A.B.continuous hO hsub q₀).φ ''
      (G ∩ (solutionSet (pullbackProj A.P (Subtype.val : O → A.Obj)) g ∩ Va)) =
      c.φ '' (dd.toSubData.shrink c.φ ∩ M) := by
    ext w
    constructor
    · rintro ⟨u, ⟨⟨hu1, huW⟩, hu0, -⟩, rfl⟩
      exact ⟨u.1, ⟨hu1, ⟨u, huW, rfl⟩, (hzero u).1 hu0⟩, rfl⟩
    · rintro ⟨_, ⟨hu1, ⟨u, huW, rfl⟩, hfu⟩, rfl⟩
      exact ⟨u, ⟨⟨hu1, huW⟩, (hzero u).2 hfu, huW.1⟩, rfl⟩
  have hQ : IsScRetract c.φ.model.E c.φ.model.C
      ((c.restrictTo A.B.continuous hO hsub q₀).φ ''
        (G ∩ (solutionSet (pullbackProj A.P (Subtype.val : O → A.Obj)) g ∩ Va))) := by
    obtain ⟨R, hR⟩ := dd.toSubData.isScRetract_image c.φ c.isChart
    exact ⟨R, hR.trans himgeq.symm⟩
  have h2 := htan v hvW.1 hv0 (c.restrictTo A.B.continuous hO hsub q₀) hc' hyc G hGo
    (fun u hu => dd.toSubData.shrink_subset_source c.φ hu.1) hvG hQ z hz
  have h2' := (congrArg (fun Q => tangentSpace c.φ.model.E c.φ.model.C Q z) himgeq).symm.trans h2
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U :=
    mem_U_of_mem_O c.isRetraction (by rw [c.r_image, hz]; exact c.φ.mapsTo_model v.1 hyc)
  have e := scDeriv_restrictTo_subRestrict hO hft hs hc hsub q₀ hzU
  refine h2'.trans ?_
  ext w
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at ht
    exact ⟨t.2, (congrArg (fun L : c.φ.model.E 0 →L[ℝ] c.F 0 => L t.1) e).symm.trans ht⟩
  · rintro ⟨hw, h0⟩
    refine ⟨⟨w, hw⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact (congrArg (fun L : c.φ.model.E 0 →L[ℝ] c.F 0 => L w) e).trans h0

end Restrict

end SBLocalization

end Polyfold
