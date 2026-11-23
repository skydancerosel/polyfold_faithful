import Polyfold.Examples.OrbifoldSquareInfSection
import Polyfold.Examples.OrbifoldSquareInfPaths
import Polyfold.Examples.OrbifoldSquareSign

/-!
# The orbifold `(ℂ × H)/ℤ₅` and the section `(z, e) ↦ (z², e)`: the positive orientation

The infinite-dimensional version of the worked example `ℂ/ℤ₅`, `z ↦ z²`, for Hofer–Wysocki–Zehnder,
*Polyfold and Fredholm Theory* (Springer 2021), Theorem 16.6.6, 2021 p. 739, with Theorems 6.6.11
and 6.6.17.

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquareInf`)

* `exists_isContOrOn_sqInf`: a continuous orientation of `f` over `ℂ × H` (any two sc-smooth
  paths with the same end points are homotopic).
* `negConstInf b`: the sc⁺-section `(z, e) ↦ ((z, −b), (e, 0))`; `isZeroAt_negConstInf_iff`;
  **`bijective_stabT_sqInf`**: for `z ≠ 0`, `(f − (b, 0))'(z, 0) = (2z, id)` is an isomorphism,
  in every chart point.
* `famInf g`: the sc⁺-section `(t, (z, e)) ↦ ((z, g(t)), (e, 0))` of the pull-back bundle over
  `ℝᵐ × (ℂ × H)`.
* `IsPosAtInf o y`: `o` is positive at `(f − f(y, 0))'(y, 0)`; **`isPosAtInf_iff`**: for a
  continuous orientation, positivity at `y₀ ≠ 0` and at `y₁ ≠ 0` are equivalent.
* `infOrientationPos`: the continuous orientation which is positive at `(f − f(y, 0))'(y, 0)`
  for every `y ≠ 0`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.OrbifoldSquareInf

open TrivialBundle EpGroupoid EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure StrongBundleEquivalenceExamples
  StrongBundleLocalizationExamples SBLocalization StrongRetr WeightedEllTwo OrbifoldSquare

/-- The points `(y, 0)` are smooth. -/
theorem mem_smoothSet_mk_h0 (y : Fin 2 → ℝ) : ((y, h0) : Ainf.Obj) ∈ Ainf.X.PObj.smoothSet :=
  (mem_smoothSet_Ainf_iff (x := ((y, h0) : (Fin 2 → ℝ) × HObj))).2 H.smooth.zero_mem

/-! ### A continuous orientation -/

/-- **`f` has a continuous orientation over all of `ℂ × H`** (Theorem 6.6.17 and
Definition 6.6.16: two sc-smooth paths with the same end points are homotopic). -/
theorem exists_isContOrOn_sqInf :
    haveI := paracompactSpace_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_pullback Ainf.B
    haveI := paracompactSpace_rn_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_rn_pullback Ainf.B
    ∃ o : ∀ a (hs : a ∈ Ainf.X.PObj.smoothSet),
        Orx (B := Ainf.B) sqInf isScFredholmSectionFunctor_sqInf.2 a hs,
      IsSectionOrientation (B := Ainf.B) sqInf isScFredholmSectionFunctor_sqInf.2 o ∧
      @Continuous _ _ _ (orTopology (orLocalTransport isTame_Ainf admitsBumpFunctions_Ainf
        isScFredholmSectionTame_sqInf hasScPlusSectionsThrough_Ainf)) (orSec o) ∧
      IsContOrOn (orLocalTransport isTame_Ainf admitsBumpFunctions_Ainf
        isScFredholmSectionTame_sqInf hasScPlusSectionsThrough_Ainf) univ o := by
  have := paracompactSpace_rn_prod Ainf.X.PObj
  have := paracompactSpace_rn_pullback Ainf.B
  have := paracompactSpace_rn_rn_prod Ainf.X.PObj
  have := paracompactSpace_rn_rn_pullback Ainf.B
  obtain ⟨o, ho, hc⟩ := exists_continuous_orSec_of_hom_eq isTame_Ainf admitsBumpFunctions_Ainf
    isScFredholmSectionTame_sqInf hasScPlusSectionsThrough_Ainf
    (fun {_ _} a b => PathCat.hom_eq_inf a b)
  exact ⟨o, ho, hc, isContOrOn_univ_of_continuous_orSec
    (fun _ hy => exists_two_orx _ hy hasScPlusSectionsThrough_Ainf)
    Ainf.X.PObj.hasConnectedSmoothNbhds hc⟩

/-! ### The sections `(z, e) ↦ ((z, −b), (e, 0))` -/

/-- The section `(z, e) ↦ ((z, −b), (e, 0))`. -/
def negConstInf (b : Fin 2 → ℝ) : Ainf.Obj → Ainf.W := Prod.map (negConst b) (constSec 0)

theorem isScPlusSection_negConstInf (b : Fin 2 → ℝ) : Ainf.B.IsScPlusSection (negConstInf b) :=
  StrongBundle.IsScPlusSection.prod (isScPlusSection_negConst b)
    (isScPlusSection_constSec H.smooth.zero_mem)

local instance instParaObjInf₁ : ParacompactSpace ((Fin 2 → ℝ) × HObj) :=
  SEP.instParacompactObjProd A5 AH

local instance instParaObjInf₂ : ParacompactSpace ((Fin 2 → ℝ) × AH.Obj) :=
  SEP.instParacompactObjProd A5 AH

local instance instParaWInf₁ :
    ParacompactSpace (((Fin 2 → ℝ) × (Fin 2 → ℝ)) × (HObj × H 0)) :=
  SEP.instParacompactWProd A5 AH

local instance instParaWInf₂ : ParacompactSpace (((Fin 2 → ℝ) × (Fin 2 → ℝ)) × AH.W) :=
  SEP.instParacompactWProd A5 AH

/-- The chart of `Ainf.B` centred at `z₀` on the `ℂ` factor. -/
abbrev chInf (z₀ : Fin 2 → ℝ) : StrongBundleChart Ainf.X.PObj Ainf.P :=
  (chart (k := 2) z₀).prod (LocalBundle.chart (F := H) relOpen_H h0)

theorem isChart_chInf (z₀ : Fin 2 → ℝ) : Ainf.B.IsChart (chInf z₀) :=
  StrongBundle.IsChart.prod (isChart_chart (k := 2) z₀)
    (LocalBundle.isChart_chart (F := H) relOpen_H h0)

/-- The principal part of `f + S_b` in the chart `chInf z₀`: `(a, v) ↦ ((a + z₀)² − b, v)`. -/
theorem principal_chInf (z₀ b : Fin 2 → ℝ) (u : (Fin 2 → ℝ) × H 0) :
    (chInf z₀).principal (sectionAdd Ainf.P sqInf (negConstInf b)) u =
      (OrbifoldSquare.sq (u.1 + z₀) - b, u.2) := by
  have hf := isScFredholmSectionFunctor_sqInf.2
  rw [(chInf z₀).principal_sectionAdd hf.isScSmooth.1 (isScPlusSection_negConstInf b).1
    (show u ∈ (chInf z₀).φ.model.O from ⟨mem_univ _, mem_univ _⟩)]
  have h1 : ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm u.2 : H 0) = u.2 :=
    (LocalBundle.baseChart relOpen_H h0).toPartialEquiv.right_inv (mem_univ _)
  refine Prod.ext ?_ ?_
  · change OrbifoldSquare.sq (u.1 + z₀) + -b = OrbifoldSquare.sq (u.1 + z₀) - b
    rw [sub_eq_add_neg]
  · change ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm u.2 : H 0) + 0 = u.2
    rw [h1, add_zero]

/-- `(f + S_b)(z, e) = 0` iff `z² = b` and `e = 0`. -/
theorem isZeroAt_negConstInf_iff {b : Fin 2 → ℝ} {x : (Fin 2 → ℝ) × HObj} :
    IsZeroAt Ainf.P (sectionAdd Ainf.P sqInf (negConstInf b)) (x : Ainf.Obj) ↔
      OrbifoldSquare.sq x.1 = b ∧ x.2 = h0 := by
  have hf := isScFredholmSectionFunctor_sqInf.2
  have hFs := hf.isScSmooth.sectionAdd (isScPlusSection_negConstInf b)
  have hsrc : (x : Ainf.Obj) ∈ (chInf x.1).φ.source := ⟨mem_univ _, mem_univ _⟩
  have hφ : (chInf x.1).φ (x : Ainf.Obj) = ((0 : Fin 2 → ℝ), (x.2 : H 0)) :=
    Prod.ext (sub_self (show Fin 2 → ℝ from x.1)) rfl
  refine ((chInf x.1).isZeroAt_iff hFs.1 hsrc).trans ?_
  have e : (chInf x.1).principal (sectionAdd Ainf.P sqInf (negConstInf b))
      ((chInf x.1).φ (x : Ainf.Obj)) = (OrbifoldSquare.sq x.1 - b, (x.2 : H 0)) := by
    refine (congrArg ((chInf x.1).principal (sectionAdd Ainf.P sqInf (negConstInf b))) hφ).trans ?_
    refine (principal_chInf x.1 b _).trans ?_
    change (OrbifoldSquare.sq (0 + x.1) - b, (x.2 : H 0)) = _
    rw [zero_add]
  rw [e]
  constructor
  · intro h
    exact ⟨sub_eq_zero.1 (congrArg Prod.fst h), Subtype.ext (congrArg Prod.snd h)⟩
  · rintro ⟨h1, h2⟩
    refine Prod.ext (sub_eq_zero.2 h1) ?_
    change (x.2 : H 0) = 0
    rw [h2]
    rfl

theorem isZeroAt_negConstInf (y : Fin 2 → ℝ) :
    IsZeroAt Ainf.P (sectionAdd Ainf.P sqInf (negConstInf (OrbifoldSquare.sq y)))
      ((y, h0) : Ainf.Obj) :=
  (isZeroAt_negConstInf_iff (x := ((y, h0) : (Fin 2 → ℝ) × HObj))).2 ⟨rfl, rfl⟩

/-- **`(f − (b, 0))'(z, 0) = (2z, id)` is an isomorphism for `z ≠ 0`**, in every chart point at
`(z, 0)`. -/
theorem bijective_stabT_sqInf {z : Fin 2 → ℝ} (hz : z ≠ 0) {S : Ainf.Obj → Ainf.W}
    (hS : Ainf.B.IsScPlusSection S) {b : Fin 2 → ℝ} (hSe : S = negConstInf b)
    (h0z : IsZeroAt Ainf.P (sectionAdd Ainf.P sqInf S) ((z, h0) : Ainf.Obj))
    (p : ChartPoint Ainf.B ((z, h0) : Ainf.Obj)) :
    Bijective (p.stabT isScFredholmSectionFunctor_sqInf.2 hS h0z) := by
  subst hSe
  have hf := isScFredholmSectionFunctor_sqInf.2
  have hFs := hf.isScSmooth.sectionAdd hS
  let c : StrongBundleChart Ainf.X.PObj Ainf.P := chInf z
  have hc : Ainf.B.IsChart c := isChart_chInf z
  have hsrc : ((z, h0) : Ainf.Obj) ∈ c.φ.source := ⟨mem_univ _, mem_univ _⟩
  have hφ : c.φ ((z, h0) : Ainf.Obj) = ((0 : Fin 2 → ℝ), (0 : H 0)) :=
    Prod.ext (sub_self (show Fin 2 → ℝ from z)) rfl
  let p₀ : ChartPoint Ainf.B ((z, h0) : Ainf.Obj) :=
    { c := c
      isChart := hc
      mem_source := hsrc
      z := ((0 : Fin 2 → ℝ), (0 : H 1))
      toBase_z := by
        rw [hφ]
        exact Prod.ext rfl (map_zero _) }
  refine ChartPoint.bijective_stabT_of_bijective (p := p₀) p hf hS h0z ?_
  have hzU : p₀.z ∈ c.φ.model.E.lvlSet c.U 1 := by
    change c.φ.model.E.toBase 1 p₀.z ∈ c.U
    exact ⟨mem_univ _, mem_univ _⟩
  have hbase : c.φ.model.E.toBase 1 p₀.z = ((0 : Fin 2 → ℝ), (0 : H 0)) :=
    p₀.toBase_z.trans hφ
  have hr : r c.R = id := funext fun u => rfl
  have hDr : scDeriv c.U (r c.R) p₀.z = ContinuousLinearMap.id ℝ _ := by
    rw [hr]
    exact scDeriv_eq_of_hasFDerivAt c.relOpen (isScSmooth_id c.relOpen.isScDomain 1).isSc1 hzU
      (hasFDerivAt_id _)
  have hcne : (2 * cE z) ≠ 0 := mul_ne_zero two_ne_zero fun h => hz (cE.map_eq_zero_iff.1 h)
  let L : ((Fin 2 → ℝ) × H 0) →L[ℝ] ((Fin 2 → ℝ) × H 0) :=
    (rot (2 * cE z)).prodMap (ContinuousLinearMap.id ℝ (H 0))
  have hcomp : (c.principal (sectionAdd Ainf.P sqInf (negConstInf b)) ∘ r c.R) =
      fun u : (Fin 2 → ℝ) × H 0 => (OrbifoldSquare.sq (u.1 + z) - b, u.2) := by
    rw [hr]
    funext u
    exact principal_chInf z b u
  have hd1 : HasFDerivAt (fun a : Fin 2 → ℝ => OrbifoldSquare.sq (a + z) - b)
      (rot (2 * cE z)) 0 := by
    have h1 : HasFDerivAt OrbifoldSquare.sq (rot (2 * cE z)) ((0 : Fin 2 → ℝ) + z) := by
      rw [zero_add]; exact hasFDerivAt_sq z
    have h2 := h1.comp (0 : Fin 2 → ℝ) ((hasFDerivAt_id (0 : Fin 2 → ℝ)).add_const z)
    exact h2.sub_const b
  have hd : HasFDerivAt (fun u : (Fin 2 → ℝ) × H 0 => (OrbifoldSquare.sq (u.1 + z) - b, u.2))
      L ((0 : Fin 2 → ℝ), (0 : H 0)) := by
    have ha : HasFDerivAt (fun u : (Fin 2 → ℝ) × H 0 => OrbifoldSquare.sq (u.1 + z) - b)
        ((rot (2 * cE z)).comp (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (H 0)))
        ((0 : Fin 2 → ℝ), (0 : H 0)) :=
      (show HasFDerivAt (fun a : Fin 2 → ℝ => OrbifoldSquare.sq (a + z) - b) (rot (2 * cE z))
        (Prod.fst ((0 : Fin 2 → ℝ), (0 : H 0))) from hd1).comp _ hasFDerivAt_fst
    exact ha.prodMk hasFDerivAt_snd
  have hDg : scDeriv c.U (c.principal (sectionAdd Ainf.P sqInf (negConstInf b)) ∘ r c.R) p₀.z =
      L := by
    refine scDeriv_eq_of_hasFDerivAt c.relOpen
      ((isScSmooth_principal_comp_r (A := Ainf) hFs hc) 1).isSc1 hzU ?_
    rw [hcomp]
    exact hbase ▸ hd
  have hL : ∀ v : ↥p₀.T, ((p₀.stabT hf hS h0z v : ↥p₀.K) : c.F 0) = L (v : c.φ.model.E 0) := by
    intro v
    rw [ChartPoint.coe_stabT, linAt_apply]
    exact congrArg (fun D : c.φ.model.E 0 →L[ℝ] c.F 0 => D (v : c.φ.model.E 0)) hDg
  have hLinj : Injective L := by
    intro a a' h
    have k1 := congrArg Prod.fst h
    have k2 := congrArg Prod.snd h
    exact Prod.ext (OrbifoldSquare.injective_rot hcne k1) k2
  constructor
  · intro v w hvw
    have h := congrArg (fun t : ↥p₀.K => (t : c.F 0)) hvw
    simp only [hL] at h
    exact Subtype.ext (hLinj h)
  · intro w
    obtain ⟨a, ha⟩ := surjective_rot hcne ((w : c.F 0) : (Fin 2 → ℝ) × H 0).1
    let v : (Fin 2 → ℝ) × H 0 := (a, ((w : c.F 0) : (Fin 2 → ℝ) × H 0).2)
    have hvT : v ∈ p₀.T :=
      ⟨v, congrArg (fun D : c.φ.model.E 0 →L[ℝ] c.φ.model.E 0 => D v) hDr⟩
    refine ⟨⟨v, hvT⟩, Subtype.ext ?_⟩
    rw [hL]
    exact Prod.ext ha rfl

/-! ### The family `(t, (z, e)) ↦ ((z, g(t)), (e, 0))` -/

section Family

variable {m : ℕ}

/-- The constant section through the `i`-th basis vector of the fibre `ℂ`, and `0` in `H`. -/
def basisInf (i : Fin 2) : Ainf.Obj → Ainf.W := Prod.map (basisSection 2 2 i) (constSec 0)

theorem isScPlusSection_basisInf (i : Fin 2) : Ainf.B.IsScPlusSection (basisInf i) :=
  StrongBundle.IsScPlusSection.prod (isScPlusSection_graphSection contDiff_const)
    (isScPlusSection_constSec H.smooth.zero_mem)

/-- **The section `(t, (z, e)) ↦ ((z, g(t)), (e, 0))`** of the pull-back of `Ainf.B` to
`ℝᵐ × (ℂ × H)`. -/
def famInf (g : (Fin m → ℝ) → (Fin 2 → ℝ)) :
    (Fin m → ℝ) × Ainf.Obj → pullbackSpace Ainf.P (Prod.snd : (Fin m → ℝ) × Ainf.Obj → _) :=
  reparamSection g (paramComb basisInf fun i => (isScPlusSection_basisInf i).1)
    (isSection_pullbackLift _)

/-- The slices of `famInf g` are the sections `(z, e) ↦ ((z, g(t)), (e, 0))`. -/
theorem pullbackSlice_famInf (g : (Fin m → ℝ) → (Fin 2 → ℝ)) (q : Fin m → ℝ) :
    pullbackSlice (famInf g) q = negConstInf (-(g q)) := by
  funext x
  obtain ⟨z, e⟩ : (Fin 2 → ℝ) × HObj := x
  set w : Ainf.P ⁻¹' {((z, e) : Ainf.Obj)} :=
    fiberComb basisInf (fun i => (isScPlusSection_basisInf i).1) (g q, ((z, e) : Ainf.Obj))
    with hw
  change (w : Ainf.W) = negConstInf (-(g q)) ((z, e) : Ainf.Obj)
  let PH' : HObj × H 0 → HObj := LocalBundle.proj (E := H) (U := (univ : Set (H 0))) (F := H)
  let Φ := prodFiberCLE (proj 2 2) PH' ((z, e) : (Fin 2 → ℝ) × HObj)
  let b : Fin 2 → (Prod.map (proj 2 2) PH' ⁻¹' {((z, e) : (Fin 2 → ℝ) × HObj)}) := fun i =>
    ⟨basisInf i ((z, e) : Ainf.Obj), rfl⟩
  have hsum : Φ w = ∑ i, g q i • Φ (b i) := by
    have hw' : w = ∑ i, g q i • b i := rfl
    rw [hw', map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul Φ _ _
  have h1 : (((Φ w).1 : proj 2 2 ⁻¹' {z}) : (Fin 2 → ℝ) × (Fin 2 → ℝ)) = (z, g q) := by
    have := congrArg Prod.fst hsum
    rw [Prod.fst_sum] at this
    refine (congrArg Subtype.val this).trans ?_
    have h := pullbackSlice_famSection (n := 2) (k := 2) (m := m) g q
    exact congrFun h z
  have h2 : (((Φ w).2 : PH' ⁻¹' {e}) : HObj × H 0) = (e, (0 : H 0)) := by
    have := congrArg Prod.snd hsum
    rw [Prod.snd_sum] at this
    refine (congrArg Subtype.val this).trans ?_
    have h0' : (⟨(e, (0 : H 0)), rfl⟩ : PH' ⁻¹' {e}) = 0 := by
      apply (LocalBundle.fibEquiv (F := H) e).injective
      exact ((LocalBundle.fibEquiv (F := H) e).linearEquiv ℝ).map_zero.symm
    have hs : (∑ i : Fin 2, (g q i • (Φ (b i)).2)) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        have hb : (Φ (b i)).2 = (⟨(e, (0 : H 0)), rfl⟩ : PH' ⁻¹' {e}) := rfl
        rw [hb, h0', smul_zero]
    refine (congrArg Subtype.val hs).trans ?_
    refine Prod.ext rfl ?_
    exact ((LocalBundle.fibEquiv (F := H) e).linearEquiv ℝ).map_zero
  refine Prod.ext (h1.trans ?_) h2
  refine Prod.ext rfl ?_
  change g q = - -(g q)
  rw [neg_neg]

/-- **`famInf g` is an sc⁺-section** for a `C^∞` map `g`. -/
theorem isScPlusSection_famInf {g : (Fin m → ℝ) → (Fin 2 → ℝ)} (hg : ContDiff ℝ ∞ g) :
    haveI := paracompactSpace_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_pullback Ainf.B
    (Ainf.B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m)
      Ainf.X.PObj)).IsScPlusSection (famInf g) := by
  have := paracompactSpace_rn_prod Ainf.X.PObj
  have := paracompactSpace_rn_pullback Ainf.B
  exact (StrongBundle.isScPlusSection_paramComb (B := Ainf.B)
    (fun i : Fin 2 => isScPlusSection_basisInf i)).reparamSmooth hg

end Family

/-! ### Positivity at the points `(y, 0)`, `y ≠ 0` -/

/-- **The orientation `o` is positive at `(f − f(y, 0))'(y, 0) = (2y, id)`.** -/
def IsPosAtInf (o : ∀ a (hs : a ∈ Ainf.X.PObj.smoothSet),
    Orx (B := Ainf.B) sqInf isScFredholmSectionFunctor_sqInf.2 a hs) (y : Fin 2 → ℝ) : Prop :=
  IsPosOr isScFredholmSectionFunctor_sqInf.2 (mem_smoothSet_mk_h0 y)
    (o ((y, h0) : Ainf.Obj) (mem_smoothSet_mk_h0 y))
    (negConstInf (OrbifoldSquare.sq y)) (isScPlusSection_negConstInf _) (isZeroAt_negConstInf y)

/-- **A continuous orientation which is positive at one point `(y₀, 0)`, `y₀ ≠ 0`, is positive at
every `(y₁, 0)`, `y₁ ≠ 0`**: along the path `t ↦ (y₀ · exp(t w), 0)` the linearizations
`(f − f(γ_t))'(γ_t) = (2γ_t, id)` are isomorphisms (`isPosOr_iff_of_path`). -/
theorem isPosAtInf_iff
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Ainf.Obj)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace Ainf.P
      (Prod.snd : (Fin n → ℝ) × Ainf.Obj → Ainf.Obj))]
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Ainf.Obj))]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace
      (pullbackProj Ainf.P (Prod.snd : (Fin n → ℝ) × Ainf.Obj → Ainf.Obj))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Ainf.Obj) → (Fin n → ℝ) × Ainf.Obj))]
    {o : ∀ a (hs : a ∈ Ainf.X.PObj.smoothSet),
      Orx (B := Ainf.B) sqInf isScFredholmSectionFunctor_sqInf.2 a hs}
    (ho : IsContOrOn (orLocalTransport isTame_Ainf admitsBumpFunctions_Ainf
      isScFredholmSectionTame_sqInf hasScPlusSectionsThrough_Ainf) univ o)
    {y₀ y₁ : Fin 2 → ℝ} (h₀ : y₀ ≠ 0) (h₁ : y₁ ≠ 0) : IsPosAtInf o y₀ ↔ IsPosAtInf o y₁ := by
  have hf := isScFredholmSectionFunctor_sqInf.2
  have hc₀ : cE y₀ ≠ 0 := fun h => h₀ (cE.map_eq_zero_iff.1 h)
  have hc₁ : cE y₁ ≠ 0 := fun h => h₁ (cE.map_eq_zero_iff.1 h)
  set w : ℂ := Complex.log (cE y₁ / cE y₀) with hwdef
  have hw : Complex.exp w = cE y₁ / cE y₀ := Complex.exp_log (div_ne_zero hc₁ hc₀)
  let γ₂ : (Fin 1 → ℝ) → (Fin 2 → ℝ) := fun q => cE.symm (cE y₀ * Complex.exp ((q 0 : ℂ) * w))
  have hγd : ContDiff ℝ ∞ γ₂ := by
    refine cE.symm.contDiff.comp (contDiff_const.mul ?_)
    refine (Complex.contDiff_exp (𝕜 := ℝ)).comp ?_
    exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 1))).mul contDiff_const
  let γ : (Fin 1 → ℝ) → Ainf.Obj := fun q => ((γ₂ q, h0) : (Fin 2 → ℝ) × HObj)
  have hγs : (rnPolyfold 1).IsScSmoothMap Ainf.X.PObj γ :=
    isScSmoothMap_curve_const hγd H.smooth.zero_mem
  have hγ0 : ∀ q, γ₂ q ≠ 0 := fun q h => by
    have h' : cE (γ₂ q) = 0 := by rw [h, map_zero]
    rw [ContinuousLinearEquiv.apply_symm_apply] at h'
    exact mul_ne_zero hc₀ (Complex.exp_ne_zero _) h'
  have hg : ContDiff ℝ ∞ fun q : Fin 1 → ℝ => -OrbifoldSquare.sq (γ₂ q) :=
    (contDiff_sq.comp hγd).neg
  have hS := isScPlusSection_famInf hg
  have hslice : ∀ q, pullbackSlice (famInf fun q : Fin 1 → ℝ => -OrbifoldSquare.sq (γ₂ q)) q =
      negConstInf (OrbifoldSquare.sq (γ₂ q)) := fun q =>
    (pullbackSlice_famInf _ q).trans (by rw [neg_neg])
  have hzq : ∀ q, IsZeroAt Ainf.P (sectionAdd Ainf.P sqInf
      (pullbackSlice (famInf fun q : Fin 1 → ℝ => -OrbifoldSquare.sq (γ₂ q)) q)) (γ q) :=
    fun q => by
      exact (congrArg (fun T : Ainf.Obj → Ainf.W =>
        IsZeroAt Ainf.P (sectionAdd Ainf.P sqInf T) (γ q)) (hslice q)).mpr
          (isZeroAt_negConstInf _)
  have hz : ∀ q : Fin 1 → ℝ, IsZeroAt (pullbackProj Ainf.P Prod.snd)
      (sectionAdd (pullbackProj Ainf.P Prod.snd) (paramLift sqInf hf.isScSmooth.1)
        (famInf fun q : Fin 1 → ℝ => -OrbifoldSquare.sq (γ₂ q))) (q, γ q) := fun q => by
    refine (isZeroAt_pullback_iff_pullbackSlice (P := Ainf.P)
      ((isSection_pullbackLift _).sectionAdd hS.1) q (γ q)).2 ?_
    have e := pullbackSlice_sectionAdd_paramLift (P := Ainf.P) hf.isScSmooth.1 hS.1 q
    exact (congrArg (fun T : Ainf.Obj → Ainf.W => IsZeroAt Ainf.P T (γ q)) e).mpr (hzq q)
  have key := isPosOr_iff_of_path isTame_Ainf admitsBumpFunctions_Ainf
    isScFredholmSectionTame_sqInf hasScPlusSectionsThrough_Ainf ho hγs
    (fun _ _ => mem_univ _) hS (Eventually.of_forall hz)
    (fun q _ p h0 => bijective_stabT_sqInf (hγ0 q) _ (hslice q) h0 p)
    (mem_smoothSet_mk_h0 _) (mem_smoothSet_mk_h0 _) (hzq _) (hzq _)
  have e0 : γ₂ (pt1 0) = y₀ := by
    change cE.symm (cE y₀ * Complex.exp (((0 : ℝ) : ℂ) * w)) = y₀
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
      ContinuousLinearEquiv.symm_apply_apply]
  have e1 : γ₂ (pt1 1) = y₁ := by
    change cE.symm (cE y₀ * Complex.exp (((1 : ℝ) : ℂ) * w)) = y₁
    rw [Complex.ofReal_one, one_mul, hw, mul_div_cancel₀ _ hc₀,
      ContinuousLinearEquiv.symm_apply_apply]
  have e0' : γ (pt1 0) = ((y₀, h0) : Ainf.Obj) := congrArg (fun a => ((a, h0) : Ainf.Obj)) e0
  have e1' : γ (pt1 1) = ((y₁, h0) : Ainf.Obj) := congrArg (fun a => ((a, h0) : Ainf.Obj)) e1
  have c0 := isPosOr_congr_pt hf o e0' (mem_smoothSet_mk_h0 _) (mem_smoothSet_mk_h0 _)
    ((hslice (pt1 0)).trans (by rw [e0])) (hS.pullbackSlice _) (isScPlusSection_negConstInf _)
    (hzq _) (isZeroAt_negConstInf y₀)
  have c1 := isPosOr_congr_pt hf o e1' (mem_smoothSet_mk_h0 _) (mem_smoothSet_mk_h0 _)
    ((hslice (pt1 1)).trans (by rw [e1])) (hS.pullbackSlice _) (isScPlusSection_negConstInf _)
    (hzq _) (isZeroAt_negConstInf y₁)
  exact c0.symm.trans (key.trans c1)

/-! ### The orientation which is positive at the points `(y, 0)`, `y ≠ 0` -/

/-- **`f` has a continuous orientation over `ℂ × H` which is positive at
`(f − f(1, 0))'(1, 0) = (2, id)`**: of the two continuous orientations, exactly one is. -/
theorem exists_isContOrOn_isPosAtInf :
    haveI := paracompactSpace_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_pullback Ainf.B
    haveI := paracompactSpace_rn_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_rn_pullback Ainf.B
    ∃ o : ∀ a (hs : a ∈ Ainf.X.PObj.smoothSet),
        Orx (B := Ainf.B) sqInf isScFredholmSectionFunctor_sqInf.2 a hs,
      IsContOrOn (orLocalTransport isTame_Ainf admitsBumpFunctions_Ainf
        isScFredholmSectionTame_sqInf hasScPlusSectionsThrough_Ainf) univ o ∧
      IsPosAtInf o (cE.symm 1) := by
  have := paracompactSpace_rn_prod Ainf.X.PObj
  have := paracompactSpace_rn_pullback Ainf.B
  have := paracompactSpace_rn_rn_prod Ainf.X.PObj
  have := paracompactSpace_rn_rn_pullback Ainf.B
  obtain ⟨o, -, -, ho⟩ := exists_isContOrOn_sqInf
  have hf := isScFredholmSectionFunctor_sqInf.2
  have h2 : IsTwoPointed sqInf hf := fun x hs =>
    exists_two_orx hf hs hasScPlusSectionsThrough_Ainf
  by_cases hp : IsPosAtInf o (cE.symm 1)
  · exact ⟨o, ho, hp⟩
  · refine ⟨fun y hy => orOther (o y hy), ho.other _ h2, ?_⟩
    have hne : (cE.symm (1 : ℂ) : Fin 2 → ℝ) ≠ 0 := fun h =>
      one_ne_zero (cE.symm.map_eq_zero_iff.1 h)
    have hs := mem_smoothSet_mk_h0 (cE.symm (1 : ℂ))
    have hall : ∀ a : Orx (B := Ainf.B) sqInf hf ((cE.symm (1 : ℂ), h0) : Ainf.Obj) hs,
        a = o _ hs ∨ a = orOther (o _ hs) := fun a => by
      by_cases h : a = o _ hs
      · exact Or.inl h
      · exact Or.inr ((eq_orOther_iff h2 _ _).2 h)
    have hb := bijective_stabT_sqInf hne (isScPlusSection_negConstInf _) rfl
      (isZeroAt_negConstInf _)
      (chartPtOf (orChart Ainf.B ((cE.symm (1 : ℂ), h0) : Ainf.Obj)) (isChart_orChart _)
        (mem_orChart _) hs)
    rcases ChartPoint.isPos_or_isPos (ChartPoint.stabT_mem_linSet _ hf
      (isScPlusSection_negConstInf _) (isZeroAt_negConstInf _) hs) hb hall with h | h
    · exact absurd h hp
    · exact h

/-- **The orientation of `f` which is positive at the points `(y, 0)`, `y ≠ 0`.** -/
def infOrientationPos : ∀ a (hs : a ∈ Ainf.X.PObj.smoothSet),
    Orx (B := Ainf.B) sqInf isScFredholmSectionFunctor_sqInf.2 a hs :=
  exists_isContOrOn_isPosAtInf.choose

theorem isContOrOn_infOrientationPos :
    haveI := paracompactSpace_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_pullback Ainf.B
    haveI := paracompactSpace_rn_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_rn_pullback Ainf.B
    IsContOrOn (orLocalTransport isTame_Ainf admitsBumpFunctions_Ainf
      isScFredholmSectionTame_sqInf hasScPlusSectionsThrough_Ainf) univ infOrientationPos :=
  exists_isContOrOn_isPosAtInf.choose_spec.1

/-- `infOrientationPos` is continuous for Part I's topology on `O_f`. -/
theorem continuous_orSec_infOrientationPos :
    haveI := paracompactSpace_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_pullback Ainf.B
    haveI := paracompactSpace_rn_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_rn_pullback Ainf.B
    @Continuous _ _ _ (orTopology (orLocalTransport isTame_Ainf admitsBumpFunctions_Ainf
      isScFredholmSectionTame_sqInf hasScPlusSectionsThrough_Ainf)) (orSec infOrientationPos) := by
  have := paracompactSpace_rn_prod Ainf.X.PObj
  have := paracompactSpace_rn_pullback Ainf.B
  have := paracompactSpace_rn_rn_prod Ainf.X.PObj
  have := paracompactSpace_rn_rn_pullback Ainf.B
  let := orTopology (orLocalTransport isTame_Ainf admitsBumpFunctions_Ainf
    isScFredholmSectionTame_sqInf hasScPlusSectionsThrough_Ainf)
  have h := continuousOn_orSec isContOrOn_infOrientationPos
  rw [preimage_univ] at h
  exact continuousOn_univ.1 h

theorem isSectionOrientation_infOrientationPos :
    haveI := paracompactSpace_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_pullback Ainf.B
    IsSectionOrientation (B := Ainf.B) sqInf isScFredholmSectionFunctor_sqInf.2
      infOrientationPos := by
  have := paracompactSpace_rn_prod Ainf.X.PObj
  have := paracompactSpace_rn_pullback Ainf.B
  have := paracompactSpace_rn_rn_prod Ainf.X.PObj
  have := paracompactSpace_rn_rn_pullback Ainf.B
  exact (isSectionOrientation_iff_continuous isTame_Ainf admitsBumpFunctions_Ainf
    isScFredholmSectionTame_sqInf hasScPlusSectionsThrough_Ainf infOrientationPos).2
    continuous_orSec_infOrientationPos

/-- **`infOrientationPos` is positive at every `(y, 0)`, `y ≠ 0`.** -/
theorem isPosAtInf_infOrientationPos {y : Fin 2 → ℝ} (hy : y ≠ 0) :
    IsPosAtInf infOrientationPos y := by
  have := paracompactSpace_rn_prod Ainf.X.PObj
  have := paracompactSpace_rn_pullback Ainf.B
  have := paracompactSpace_rn_rn_prod Ainf.X.PObj
  have := paracompactSpace_rn_rn_pullback Ainf.B
  have hne : (cE.symm (1 : ℂ) : Fin 2 → ℝ) ≠ 0 := fun h =>
    one_ne_zero (cE.symm.map_eq_zero_iff.1 h)
  exact (isPosAtInf_iff isContOrOn_infOrientationPos hne hy).1
    exists_isContOrOn_isPosAtInf.choose_spec.2

end Polyfold.Examples.OrbifoldSquareInf
