import Polyfold.Examples.Classical.ProductSection
import Polyfold.Examples.Classical.ProductDetSign

/-!
# The classical reduction crossed with `H`: morphisms and linearizations in the product charts

For the strong bundle `(ℝⁿ × ℝⁿ) × (H ◁ H)` over `(G ⋉ ℝⁿ) × H` (`ProductSetup.lean`) and the
section `f(x, e) = ((x, φ x), (e, e))` (`ProductSection.lean`): the maps `Tφ` and `μ(φ, ·)` of a
morphism `φ = ((g, x), 0)` (§12.5, 2021 pp. 592–594; `EpStrongBundle.morTx`, `morKx`) and the
linearizations `(f + S)'` (Definition 6.2.1, 2021), read in the product of the translation chart
of `ℝⁿ` and the chart of `H`, for Theorem 16.6.6 (2021 p. 739).  This is the product analogue of
`MorphismCharts.lean`.

## What is formalized (namespace `Polyfold.Examples.Classical.Product`)

* `stdPtP σ x`: the chart point of the product chart `chP σ x` at `(x, 0)` (with `z = 0`);
  `stdPtP_T`, `stdPtP_K`: its spaces `T_0` and `K_0` are all of `ℝⁿ × H_0`; `tEquivP`, `kEquivP`:
  the identifications with `ℝⁿ × H_0` (the coercions); `orTEquivP`, `orKEquivP`: the same read
  in the chosen chart point `orPt`.
* `gP σ ψ`: the sc⁺-section `(x, e) ↦ ((x, ψ x), (e, 0))`; `principal_chP`: the principal part
  of `f + gP σ ψ` in the product chart is `(a, v) ↦ ((φ + ψ)(a + x), v)`.
* **`stabT_stdP`**, **`orKEquivP_stabT`**, **`stabT_eq_blk`**: `(f + S)'(y, 0)` is
  `D(φ + ψ)(y) ⊕ id_{H_0}`, in the product chart point and in the chosen chart point;
  `bijective_stabT_P`: it is an isomorphism in every chart point when `D(φ + ψ)(y)` is.
* **`blk_mem_linSet`**: every block operator `A ⊕ id_{H_0}` lies in `Lin(f, (y, 0))` (it is
  `(f + S)'(y, 0)` for `S(x, e) = ((x, A(x − y) − φ x), (e, 0))`).
* `exists_srcInv_eqP`: near `(x, e)` the inverse of `s` on the sheet of `((g, x), e)` is
  `(y, e') ↦ ((g, y), e')`; `baseDeriv_movPtP`, `fiberMap_movPtP`: from the product chart at
  `(x, 0)` (restricted to the sheet) carried along the isomorphism of `((g, x), 0)` to the
  product chart at `(g • x, 0)`, the base and fibre transitions are `g • ⊕ id` and `σ g ⊕ id`.
* **`morTx_stdP`**, **`morKx_stdP`**: `T((g, x), 0)` and `μ(((g, x), 0), ·)` read through
  `orTEquivP`, `orKEquivP` are `(v, w) ↦ (g • v, w)` and `(k, w) ↦ (σ g k, w)`;
  `morTx_eq_conjP`, `morKx_eq_conjP`: at an isotropy morphism they are conjugate to
  `ρ(g) ⊕ id` and `σ(g) ⊕ id`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical.Product

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure WeightedEllTwo SBLocalization StrongRetr
  Polyfold.Examples.OrbifoldSquareInf Polyfold.Examples.Classical

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]
  [FaithfulSMul G (Fin n → ℝ)]
  (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) {φ : (Fin n → ℝ) → (Fin n → ℝ)}

/-! ### The product chart point -/

/-- The chart of `(AP σ).B` centred at `x` on the `ℝⁿ` factor. -/
abbrev chP (x : Fin n → ℝ) : StrongBundleChart (AP σ).X.PObj (AP σ).P :=
  (chart (k := n) x).prod (LocalBundle.chart (F := H) relOpen_H h0)

theorem isChart_chP (x : Fin n → ℝ) : (AP σ).B.IsChart (chP σ x) :=
  StrongBundle.IsChart.prod (isChart_chart (k := n) x)
    (LocalBundle.isChart_chart (F := H) relOpen_H h0)

theorem chP_apply (x : Fin n → ℝ) :
    (chP σ x).φ ((x, h0) : (AP σ).Obj) = ((0 : Fin n → ℝ), (0 : H 0)) :=
  Prod.ext (sub_self (show Fin n → ℝ from x)) rfl

/-- **The chart point of the product chart at `(x, 0)`**, with `z = 0`. -/
def stdPtP (x : Fin n → ℝ) : ChartPoint (AP σ).B ((x, h0) : (AP σ).Obj) where
  c := chP σ x
  isChart := isChart_chP σ x
  mem_source := ⟨mem_univ _, mem_univ _⟩
  z := ((0 : Fin n → ℝ), (0 : H 1))
  toBase_z := by
    rw [chP_apply]
    exact Prod.ext rfl (map_zero _)

theorem r_chP (x : Fin n → ℝ) : r (chP σ x).R = id := funext fun _ => rfl

theorem scDeriv_r_stdPtP (x : Fin n → ℝ) :
    scDeriv (stdPtP σ x).c.U (r (stdPtP σ x).c.R) (stdPtP σ x).z = ContinuousLinearMap.id ℝ _ := by
  have hzU : (stdPtP σ x).z ∈ (stdPtP σ x).c.φ.model.E.lvlSet (stdPtP σ x).c.U 1 := by
    change (stdPtP σ x).c.φ.model.E.toBase 1 (stdPtP σ x).z ∈ (stdPtP σ x).c.U
    exact ⟨mem_univ _, mem_univ _⟩
  change scDeriv (chP σ x).U (r (chP σ x).R) (stdPtP σ x).z = _
  rw [r_chP]
  exact scDeriv_eq_of_hasFDerivAt (chP σ x).relOpen
    (isScSmooth_id (chP σ x).relOpen.isScDomain 1).isSc1 hzU (hasFDerivAt_id _)

theorem stdPtP_T (x : Fin n → ℝ) : (stdPtP σ x).T = ⊤ := by
  change rangeS (scDeriv (stdPtP σ x).c.U (r (stdPtP σ x).c.R) (stdPtP σ x).z) = ⊤
  rw [rangeS, scDeriv_r_stdPtP]
  exact LinearMap.range_id

theorem stdPtP_K (x : Fin n → ℝ) : (stdPtP σ x).K = ⊤ := by
  refine eq_top_iff.2 fun k _ => ⟨k, rfl⟩

theorem mem_stdPtP_T (x : Fin n → ℝ) (v : (stdPtP σ x).c.φ.model.E 0) : v ∈ (stdPtP σ x).T := by
  rw [stdPtP_T]; exact Submodule.mem_top

theorem mem_stdPtP_K (x : Fin n → ℝ) (k : (stdPtP σ x).c.F 0) : k ∈ (stdPtP σ x).K := by
  rw [stdPtP_K]; exact Submodule.mem_top

/-- `T_{(x, 0)}(ℝⁿ × H)` read in the product chart point: `T_0 = ℝⁿ × H_0`. -/
def tEquivP (x : Fin n → ℝ) : ↥(stdPtP σ x).T ≃L[ℝ] (Fin n → ℝ) × H 0 where
  toFun v := ((v : (stdPtP σ x).c.φ.model.E 0) : (Fin n → ℝ) × H 0)
  invFun w := ⟨w, mem_stdPtP_T σ x w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

/-- The fibre `ℝⁿ × H_0` read in the product chart point: `K_0 = ℝⁿ × H_0`. -/
def kEquivP (x : Fin n → ℝ) : ↥(stdPtP σ x).K ≃L[ℝ] (Fin n → ℝ) × H 0 where
  toFun k := ((k : (stdPtP σ x).c.F 0) : (Fin n → ℝ) × H 0)
  invFun w := ⟨w, mem_stdPtP_K σ x w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

@[simp] theorem tEquivP_apply (x : Fin n → ℝ) (v : ↥(stdPtP σ x).T) :
    tEquivP σ x v = ((v : (stdPtP σ x).c.φ.model.E 0) : (Fin n → ℝ) × H 0) := rfl

@[simp] theorem kEquivP_apply (x : Fin n → ℝ) (k : ↥(stdPtP σ x).K) :
    kEquivP σ x k = ((k : (stdPtP σ x).c.F 0) : (Fin n → ℝ) × H 0) := rfl

@[simp] theorem coe_tEquivP_symm (x : Fin n → ℝ) (w : (Fin n → ℝ) × H 0) :
    (((tEquivP σ x).symm w : ↥(stdPtP σ x).T) : (stdPtP σ x).c.φ.model.E 0) = w := rfl

@[simp] theorem coe_kEquivP_symm (x : Fin n → ℝ) (w : (Fin n → ℝ) × H 0) :
    (((kEquivP σ x).symm w : ↥(stdPtP σ x).K) : (stdPtP σ x).c.F 0) = w := rfl

/-- `T_{(x, 0)}(ℝⁿ × H)` read in the chosen chart point and identified with `ℝⁿ × H_0`. -/
def orTEquivP (x : Fin n → ℝ) (hs : ((x, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet) :
    ↥(orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).T ≃L[ℝ] (Fin n → ℝ) × H 0 :=
  ((orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).transferT (stdPtP σ x)).trans (tEquivP σ x)

/-- The fibre over `(x, 0)` read in the chosen chart point and identified with `ℝⁿ × H_0`. -/
def orKEquivP (x : Fin n → ℝ) (hs : ((x, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet) :
    ↥(orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).K ≃L[ℝ] (Fin n → ℝ) × H 0 :=
  ((orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).transferK (stdPtP σ x)).trans (kEquivP σ x)

theorem orTEquivP_apply (x : Fin n → ℝ) (hs : ((x, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (v : ↥(orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).T) :
    orTEquivP σ x hs v =
      tEquivP σ x ((orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).transferT (stdPtP σ x) v) := rfl

theorem orKEquivP_apply (x : Fin n → ℝ) (hs : ((x, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (k : ↥(orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).K) :
    orKEquivP σ x hs k =
      kEquivP σ x ((orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).transferK (stdPtP σ x) k) := rfl

/-! ### Linearizations in the product chart point -/

/-- The sc⁺-section `(x, e) ↦ ((x, ψ x), (e, 0))`. -/
abbrev gP (ψ : (Fin n → ℝ) → (Fin n → ℝ)) : (AP σ).Obj → (AP σ).W :=
  Prod.map (graphSection ψ) (constSec 0)

theorem isScPlusSection_gP {ψ : (Fin n → ℝ) → (Fin n → ℝ)} (hψ : ContDiff ℝ ∞ ψ) :
    (AP σ).B.IsScPlusSection (gP σ ψ) :=
  StrongBundle.IsScPlusSection.prod (isScPlusSection_graphSection hψ)
    (isScPlusSection_constSec H.smooth.zero_mem)

/-- The principal part of `f + S` in the product chart at `x`: `(a, v) ↦ ((φ + ψ)(a + x), v)`. -/
theorem principal_chP (hf : (AP σ).B.IsScFredholmSection (fP σ φ))
    {ψ : (Fin n → ℝ) → (Fin n → ℝ)} (hS : (AP σ).B.IsScPlusSection (gP σ ψ)) (x : Fin n → ℝ)
    (u : (Fin n → ℝ) × H 0) :
    (chP σ x).principal (sectionAdd (AP σ).P (fP σ φ) (gP σ ψ)) u = ((φ + ψ) (u.1 + x), u.2) := by
  rw [(chP σ x).principal_sectionAdd hf.isScSmooth.1 hS.1
    (show u ∈ (chP σ x).φ.model.O from ⟨mem_univ _, mem_univ _⟩)]
  have h1 : ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm u.2 : H 0) = u.2 :=
    (LocalBundle.baseChart relOpen_H h0).toPartialEquiv.right_inv (mem_univ _)
  refine Prod.ext rfl ?_
  change ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm u.2 : H 0) + 0 = u.2
  rw [h1, add_zero]

/-- **`(f + S)'(y, 0)` read in the product chart point is `D(φ + ψ)(y) ⊕ id`** for
`f(x, e) = ((x, φ x), (e, e))` and `S(x, e) = ((x, ψ x), (e, 0))`. -/
theorem stabT_stdP {ψ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hf : (AP σ).B.IsScFredholmSection (fP σ φ)) (hS : (AP σ).B.IsScPlusSection (gP σ ψ))
    {y : Fin n → ℝ}
    (hz : IsZeroAt (AP σ).P (sectionAdd (AP σ).P (fP σ φ) (gP σ ψ)) ((y, h0) : (AP σ).Obj))
    (v : ↥(stdPtP σ y).T) :
    kEquivP σ y ((stdPtP σ y).stabT hf hS hz v) =
      (fderiv ℝ (φ + ψ) y (tEquivP σ y v).1, (tEquivP σ y v).2) := by
  have hFs := hf.isScSmooth.sectionAdd hS
  have hzU : (stdPtP σ y).z ∈ (chP σ y).φ.model.E.lvlSet (chP σ y).U 1 := by
    change (chP σ y).φ.model.E.toBase 1 (stdPtP σ y).z ∈ (chP σ y).U
    exact ⟨mem_univ _, mem_univ _⟩
  have hbase : (chP σ y).φ.model.E.toBase 1 (stdPtP σ y).z = ((0 : Fin n → ℝ), (0 : H 0)) :=
    (stdPtP σ y).toBase_z.trans (chP_apply σ y)
  let L : ((Fin n → ℝ) × H 0) →L[ℝ] ((Fin n → ℝ) × H 0) :=
    (fderiv ℝ (φ + ψ) y).prodMap (ContinuousLinearMap.id ℝ (H 0))
  have hcomp : ((chP σ y).principal (sectionAdd (AP σ).P (fP σ φ) (gP σ ψ)) ∘ r (chP σ y).R) =
      fun u : (Fin n → ℝ) × H 0 => ((φ + ψ) (u.1 + y), u.2) := by
    rw [r_chP]
    funext u
    exact principal_chP σ hf hS y u
  have hd1 : HasFDerivAt (fun a : Fin n → ℝ => (φ + ψ) (a + y)) (fderiv ℝ (φ + ψ) y) 0 := by
    have h1 : HasFDerivAt (φ + ψ) (fderiv ℝ (φ + ψ) y) ((0 : Fin n → ℝ) + y) := by
      rw [zero_add]
      exact ((hφ.add hψ).differentiable (by simp) y).hasFDerivAt
    exact h1.comp (0 : Fin n → ℝ) ((hasFDerivAt_id (0 : Fin n → ℝ)).add_const y)
  have hd : HasFDerivAt (fun u : (Fin n → ℝ) × H 0 => ((φ + ψ) (u.1 + y), u.2))
      L ((0 : Fin n → ℝ), (0 : H 0)) := by
    have ha : HasFDerivAt (fun u : (Fin n → ℝ) × H 0 => (φ + ψ) (u.1 + y))
        ((fderiv ℝ (φ + ψ) y).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (H 0)))
        ((0 : Fin n → ℝ), (0 : H 0)) :=
      (show HasFDerivAt (fun a : Fin n → ℝ => (φ + ψ) (a + y)) (fderiv ℝ (φ + ψ) y)
        (Prod.fst ((0 : Fin n → ℝ), (0 : H 0))) from hd1).comp _ hasFDerivAt_fst
    exact ha.prodMk hasFDerivAt_snd
  have hDg : scDeriv (chP σ y).U
      ((chP σ y).principal (sectionAdd (AP σ).P (fP σ φ) (gP σ ψ)) ∘ r (chP σ y).R)
        (stdPtP σ y).z = L := by
    refine scDeriv_eq_of_hasFDerivAt (chP σ y).relOpen
      ((isScSmooth_principal_comp_r (A := AP σ) hFs (isChart_chP σ y)) 1).isSc1 hzU ?_
    rw [hcomp]
    exact hbase ▸ hd
  rw [kEquivP_apply, ChartPoint.coe_stabT, linAt_apply]
  exact congrArg (fun D : (chP σ y).φ.model.E 0 →L[ℝ] (chP σ y).F 0 =>
    (D ((v : (stdPtP σ y).c.φ.model.E 0)) : (Fin n → ℝ) × H 0)) hDg

/-- **`(f + S)'(y, 0)` is an isomorphism in every chart point** when `D(φ + ψ)(y)` is. -/
theorem bijective_stabT_P {ψ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) (hf : (AP σ).B.IsScFredholmSection (fP σ φ))
    (hS : (AP σ).B.IsScPlusSection (gP σ ψ)) {y : Fin n → ℝ}
    (hz : IsZeroAt (AP σ).P (sectionAdd (AP σ).P (fP σ φ) (gP σ ψ)) ((y, h0) : (AP σ).Obj))
    (hb : Bijective (fderiv ℝ (φ + ψ) y)) (p : ChartPoint (AP σ).B ((y, h0) : (AP σ).Obj)) :
    Bijective (p.stabT hf hS hz) := by
  refine ChartPoint.bijective_stabT_of_bijective (p := stdPtP σ y) p hf hS hz ?_
  have e : ⇑((stdPtP σ y).stabT hf hS hz) = ⇑(kEquivP σ y).symm ∘
      ⇑((fderiv ℝ (φ + ψ) y).prodMap (ContinuousLinearMap.id ℝ (H 0))) ∘ ⇑(tEquivP σ y) := by
    funext v
    apply (kEquivP σ y).injective
    rw [stabT_stdP σ hφ hψ hf hS hz v]
    rw [comp_apply, comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  rw [e]
  exact (kEquivP σ y).symm.bijective.comp
    ((hb.prodMap bijective_id).comp (tEquivP σ y).bijective)

/-- **`(f + S)'(y, 0)` read in the chosen chart point is `D(φ + ψ)(y) ⊕ id`** through
`orTEquivP`, `orKEquivP`. -/
theorem orKEquivP_stabT {ψ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) (hf : (AP σ).B.IsScFredholmSection (fP σ φ))
    (hS : (AP σ).B.IsScPlusSection (gP σ ψ)) {y : Fin n → ℝ}
    (hz : IsZeroAt (AP σ).P (sectionAdd (AP σ).P (fP σ φ) (gP σ ψ)) ((y, h0) : (AP σ).Obj))
    (hs : ((y, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (v : ↥(orPt (AP σ).B ((y, h0) : (AP σ).Obj) hs).T) :
    orKEquivP σ y hs ((orPt (AP σ).B ((y, h0) : (AP σ).Obj) hs).stabT hf hS hz v) =
      (fderiv ℝ (φ + ψ) y (orTEquivP σ y hs v).1, (orTEquivP σ y hs v).2) := by
  rw [orKEquivP_apply, orTEquivP_apply,
    ← ChartPoint.stabT_transferT (stdPtP σ y) hf hS hz v]
  exact stabT_stdP σ hφ hψ hf hS hz _

/-- **`(f + S)'(y, 0)` in the chosen chart point is the block operator `D(φ + ψ)(y) ⊕ id`.** -/
theorem stabT_eq_blk {ψ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) (hf : (AP σ).B.IsScFredholmSection (fP σ φ))
    (hS : (AP σ).B.IsScPlusSection (gP σ ψ)) {y : Fin n → ℝ}
    (hz : IsZeroAt (AP σ).P (sectionAdd (AP σ).P (fP σ φ) (gP σ ψ)) ((y, h0) : (AP σ).Obj))
    (hs : ((y, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet) :
    (orPt (AP σ).B ((y, h0) : (AP σ).Obj) hs).stabT hf hS hz =
      blk (orTEquivP σ y hs) (orKEquivP σ y hs) (fderiv ℝ (φ + ψ) y) := by
  ext1 v
  apply (orKEquivP σ y hs).injective
  rw [orKEquivP_stabT σ hφ hψ hf hS hz hs v, blk_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- The zero of `f + S` at `(y, 0)` for `S(x, e) = ((x, ψ x), (e, 0))` with `φ + ψ` vanishing at
`y`. -/
theorem isZeroAt_gP (hf : (AP σ).B.IsScFredholmSection (fP σ φ))
    {ψ : (Fin n → ℝ) → (Fin n → ℝ)} (hS : (AP σ).B.IsScPlusSection (gP σ ψ)) {y : Fin n → ℝ}
    (hy : (φ + ψ) y = 0) :
    IsZeroAt (AP σ).P (sectionAdd (AP σ).P (fP σ φ) (gP σ ψ)) ((y, h0) : (AP σ).Obj) := by
  have hFs := hf.isScSmooth.sectionAdd hS
  refine ((chP σ y).isZeroAt_iff hFs.1 (show ((y, h0) : (AP σ).Obj) ∈ (chP σ y).φ.source from
    ⟨mem_univ _, mem_univ _⟩)).2 ?_
  rw [chP_apply, principal_chP σ hf hS y]
  refine Prod.ext ?_ rfl
  change (φ + ψ) (0 + y) = 0
  rw [zero_add, hy]

variable {σ} in
/-- **Every block operator `A ⊕ id` lies in `Lin(f, (y, 0))`**, read in the chosen chart point:
it is `(f + S)'(y, 0)` for `S(x, e) = ((x, A(x − y) − φ(x)), (e, 0))`. -/
theorem blk_mem_linSet (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (y : Fin n → ℝ) (hs : ((y, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    blk (orTEquivP σ y hs) (orKEquivP σ y hs) A ∈
      (orPt (AP σ).B ((y, h0) : (AP σ).Obj) hs).linSet (fP σ φ) := by
  have hf := (isScFredholmSectionFunctor_fP (σ := σ) hφ heq).2
  set ψ : (Fin n → ℝ) → (Fin n → ℝ) := fun u => A (u - y) - φ u with hψdef
  have hψ : ContDiff ℝ ∞ ψ := (A.contDiff.comp (contDiff_id.sub contDiff_const)).sub hφ
  have hsum : φ + ψ = fun u => A (u - y) := by
    funext u
    change φ u + (A (u - y) - φ u) = A (u - y)
    rw [add_sub_cancel]
  have hS := isScPlusSection_gP σ hψ
  have hz : IsZeroAt (AP σ).P (sectionAdd (AP σ).P (fP σ φ) (gP σ ψ)) ((y, h0) : (AP σ).Obj) :=
    isZeroAt_gP σ hf hS (by rw [hsum]; simp)
  have hD : fderiv ℝ (φ + ψ) y = A := by
    rw [hsum]
    exact (A.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const y)).fderiv
  rw [← hD, ← stabT_eq_blk σ hφ hψ hf hS hz hs]
  exact (orPt (AP σ).B ((y, h0) : (AP σ).Obj) hs).stabT_mem_linSet hf hS hz hs

/-! ### Derivatives read through local agreement -/

/-- The sc-derivative at `z` of an sc¹ map which agrees near `z` with a map `h` differentiable at
`z` (in the classical sense) is `Dh(z)`. -/
theorem scDeriv_eq_of_eqOn_nhds {E F : ScBanach} {C U N : Set (E 0)}
    (hU : IsRelOpenInQuadrant E C U) {f : E 0 → F 0} (hf : IsSc1 U f) {z : E 1}
    (hz : z ∈ E.lvlSet U 1) (hN : IsOpen N) (hzN : E.toBase 1 z ∈ N) {h : E 0 → F 0}
    (heq : EqOn f h (U ∩ N)) {D : E 0 →L[ℝ] F 0} (hD : HasFDerivAt h D (E.toBase 1 z)) :
    scDeriv U f z = D := by
  have hV := hU.inter_isOpen hN
  have hzV : z ∈ E.lvlSet (U ∩ N) 1 := ⟨hz, hzN⟩
  apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
  have d₁ := (hf.isSc1With_scDeriv.hasFDerivWithinAt z hz).mono
    (E.lvlSet_mono (inter_subset_left (t := N)) 1)
  have d₂ : HasFDerivWithinAt (f ∘ E.toBase 1) (D.comp (E.toBase 1)) (E.lvlSet (U ∩ N) 1) z :=
    (hD.comp_hasFDerivWithinAt z (E.toBase 1).hasFDerivAt.hasFDerivWithinAt).congr
      (fun x hx => heq hx) (heq hzV)
  exact (hV.isScDomain.uniqueDiffWithinAt 1 z hzV).eq d₁ d₂

/-! ### The sheet of a morphism `((g, x), e)` -/

/-- **Near `(x, e)`, the inverse of `s` on the sheet of `((g, x), e)` is
`(y, e') ↦ ((g, y), e')`** (`s` is continuous with inverse through `((g, x), e)`, and `G` is
discrete). -/
theorem exists_srcInv_eqP (ψ : (G × (Fin n → ℝ)) × HObj) :
    ∃ N : Set ((Fin n → ℝ) × HObj), IsOpen N ∧ (ψ.1.2, ψ.2) ∈ N ∧
      N ⊆ ((XP G n).sheetAt ψ).srcSet ∧
        ∀ y ∈ N, ((XP G n).sheetAt ψ).srcInv y = ((ψ.1.1, y.1), y.2) := by
  set S := (XP G n).sheetAt ψ
  have hs := S.isScDiffeoOn_src
  have hψ : S.srcInv (ψ.1.2, ψ.2) = ψ := hs.left_inv ψ ((XP G n).mem_sheetAt ψ)
  have hψs : (ψ.1.2, ψ.2) ∈ S.srcSet := hs.mapsTo ((XP G n).mem_sheetAt ψ)
  have ho : IsOpen (S.srcSet ∩ S.srcInv ⁻¹' ((fun m : (G × (Fin n → ℝ)) × HObj => m.1.1) ⁻¹'
      {ψ.1.1})) :=
    hs.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hs.isOpen_target
      ((isOpen_discrete {ψ.1.1}).preimage continuous_fst.fst)
  refine ⟨_, ho, ⟨hψs, ?_⟩, inter_subset_left, fun y hy => ?_⟩
  · change (S.srcInv (ψ.1.2, ψ.2)).1.1 = ψ.1.1
    rw [hψ]
  · have h1 : (S.srcInv y).1.1 = ψ.1.1 := hy.2
    have h2 : ((S.srcInv y).1.2, (S.srcInv y).2) = y := hs.right_inv y hy.1
    have h3 : (S.srcInv y).1.2 = y.1 := congrArg Prod.fst h2
    have h4 : (S.srcInv y).2 = y.2 := congrArg Prod.snd h2
    exact Prod.ext (Prod.ext h1 h3) h4

/-- The product chart at `x` restricted to `s(sheet)` of a morphism `ψ` with `s(ψ) = (x, 0)`. -/
def resPtP (ψ : (AP σ).Mor) {x : Fin n → ℝ} (hx : (AP σ).X.src ψ = ((x, h0) : (AP σ).Obj)) :
    ChartPoint (AP σ).B ((x, h0) : (AP σ).Obj) :=
  chartPt ((chP σ x).restrict (s := ((AP σ).X.sheetAt ψ).srcSet)
      (fun _ _ => ⟨mem_univ _, mem_univ _⟩) (EpStrongBundle.isOpen_srcSet (X := (AP σ).X) ψ))
    ((isChart_chP σ x).restrict _ _) (EpStrongBundle.mem_srcSet (X := (AP σ).X) hx)
    ((0 : Fin n → ℝ), (0 : H 1)) (by
      change _ = (chP σ x).φ ((x, h0) : (AP σ).Obj)
      rw [chP_apply]
      exact Prod.ext rfl (map_zero _))

theorem resPtP_sub (ψ : (AP σ).Mor) {x : Fin n → ℝ}
    (hx : (AP σ).X.src ψ = ((x, h0) : (AP σ).Obj)) :
    (resPtP σ ψ hx).c.φ.source ⊆ ((AP σ).X.sheetAt ψ).srcSet := fun _ hw => hw

theorem symm_baseChart (u : H 0) :
    (LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm u = (⟨u, mem_univ _⟩ : HObj) :=
  Subtype.ext ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.right_inv (mem_univ _))

/-- From the restricted product chart to the product chart the base derivative is the
identity. -/
theorem baseDeriv_resPtP (ψ : (AP σ).Mor) {x : Fin n → ℝ}
    (hx : (AP σ).X.src ψ = ((x, h0) : (AP σ).Obj)) (v : (resPtP σ ψ hx).c.φ.model.E 0) :
    ((resPtP σ ψ hx).baseDeriv (stdPtP σ x) v : (Fin n → ℝ) × H 0) = v := by
  have h := scDeriv_eq_of_eqOn_nhds ((resPtP σ ψ hx).baseRet (stdPtP σ x)).relOpen
    ((resPtP σ ψ hx).isSc1_transition (stdPtP σ x)) ((resPtP σ ψ hx).z_mem_baseRet (stdPtP σ x))
    isOpen_univ (mem_univ _) (h := id) (fun u _ => ?_)
    (hasFDerivAt_id (𝕜 := ℝ) _)
  · exact congrArg (fun T : (Fin n → ℝ) × H 0 →L[ℝ] (Fin n → ℝ) × H 0 => T v) h
  · exact Prod.ext (add_sub_cancel_right (u.1 : Fin n → ℝ) x)
      ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.right_inv (mem_univ _))

/-- The restricted product chart at `s(ψ)` carried to `t(ψ)` along the isomorphism of `ψ`. -/
abbrev movPtP (ψ : (AP σ).Mor) {x x' : Fin n → ℝ}
    (hx : (AP σ).X.src ψ = ((x, h0) : (AP σ).Obj))
    (hx' : (AP σ).X.tgt ψ = ((x', h0) : (AP σ).Obj)) :
    ChartPoint (AP σ).B ((x', h0) : (AP σ).Obj) :=
  ((AP σ).E.morIso ψ).pullPt (resPtP σ ψ hx) (resPtP_sub σ ψ hx)
    (EpStrongBundle.mem_tgtSet hx') ((AP σ).E.morIso_ϕ_eq hx hx')

/-- **From the carried chart to the product chart at `(g • x, 0)` the base derivative is
`(v, w) ↦ (g • v, w)`**: near `0` the base transition is `(u, w) ↦ (g • (u + x) − g • x, w)`. -/
theorem baseDeriv_movPtP (ψ : (AP σ).Mor) {x x' : Fin n → ℝ}
    (hx : (AP σ).X.src ψ = ((x, h0) : (AP σ).Obj))
    (hx' : (AP σ).X.tgt ψ = ((x', h0) : (AP σ).Obj))
    (v : (movPtP σ ψ hx hx').c.φ.model.E 0) :
    ((movPtP σ ψ hx hx').baseDeriv (stdPtP σ x') v : (Fin n → ℝ) × H 0) =
      (rhoL ψ.1.1).prodMap (ContinuousLinearMap.id ℝ (H 0)) v := by
  obtain ⟨N, hNo, hxN, -, hN⟩ := exists_srcInv_eqP ψ
  obtain ⟨⟨g, x₀⟩, e⟩ := ψ
  have h1 : x₀ = x := congrArg Prod.fst hx
  have h2 : e = h0 := congrArg Prod.snd hx
  have h3 : g • x₀ = x' := congrArg Prod.fst hx'
  subst h1 h2 h3
  let L : ((Fin n → ℝ) × H 0) →L[ℝ] ((Fin n → ℝ) × H 0) :=
    (rhoL g).prodMap (ContinuousLinearMap.id ℝ (H 0))
  have hc : Continuous fun u : (Fin n → ℝ) × H 0 =>
      ((u.1 + x₀, (⟨u.2, mem_univ _⟩ : HObj)) : (Fin n → ℝ) × HObj) :=
    (continuous_fst.add continuous_const).prodMk (continuous_snd.subtype_mk _)
  have h := scDeriv_eq_of_eqOn_nhds ((movPtP σ _ hx hx').baseRet (stdPtP σ _)).relOpen
    ((movPtP σ _ hx hx').isSc1_transition (stdPtP σ _))
    ((movPtP σ _ hx hx').z_mem_baseRet (stdPtP σ _))
    (hNo.preimage hc) ?_ (h := L) (fun (u : (Fin n → ℝ) × H 0) hu => ?_) L.hasFDerivAt
  · exact congrArg (fun T : (Fin n → ℝ) × H 0 →L[ℝ] (Fin n → ℝ) × H 0 => T v) h
  · have hz : (movPtP σ _ hx hx').c.φ.model.E.toBase 1 (movPtP σ _ hx hx').z =
        ((0 : Fin n → ℝ), (0 : H 0)) := Prod.ext rfl (map_zero _)
    have e2 : (fun u : (Fin n → ℝ) × H 0 =>
        ((u.1 + x₀, (⟨u.2, mem_univ _⟩ : HObj)) : (Fin n → ℝ) × HObj))
          ((movPtP σ _ hx hx').c.φ.model.E.toBase 1 (movPtP σ _ hx hx').z) = (x₀, h0) := by
      rw [hz]
      exact Prod.ext (zero_add x₀) (Subtype.ext rfl)
    change (fun u : (Fin n → ℝ) × H 0 =>
        ((u.1 + x₀, (⟨u.2, mem_univ _⟩ : HObj)) : (Fin n → ℝ) × HObj))
          ((movPtP σ _ hx hx').c.φ.model.E.toBase 1 (movPtP σ _ hx hx').z) ∈ N
    rw [e2]
    exact hxN
  · have hu' : ((u.1 + x₀, (⟨u.2, mem_univ _⟩ : HObj)) :
        (Fin n → ℝ) × HObj) ∈ N := hu.2
    change ((((XP G n).tgt (((XP G n).sheetAt ((g, x₀), h0)).srcInv
      (u.1 + x₀, (LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm u.2))).1
        - g • x₀, (((XP G n).tgt (((XP G n).sheetAt ((g, x₀), h0)).srcInv
      (u.1 + x₀, (LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm u.2))).2
        : H 0)) : (Fin n → ℝ) × H 0) = L u
    rw [symm_baseChart]
    erw [hN _ hu']
    change ((g • (u.1 + x₀) - g • x₀, u.2) : (Fin n → ℝ) × H 0) = (g • u.1, u.2)
    rw [smul_add, add_sub_cancel_right]

/-- From the restricted product chart to the product chart the fibre transition is the
identity. -/
theorem fiberMap_resPtP (ψ : (AP σ).Mor) {x : Fin n → ℝ}
    (hx : (AP σ).X.src ψ = ((x, h0) : (AP σ).Obj)) (k : (resPtP σ ψ hx).c.F 0) :
    ((resPtP σ ψ hx).fiberMap (stdPtP σ x) k : (Fin n → ℝ) × H 0) = k := rfl

/-- **From the carried chart to the product chart at `(g • x, 0)` the fibre transition is
`(k, w) ↦ (σ g k, w)`**: the bundle map of the isomorphism of `ψ = ((g, x), 0)` is
`μ(s⁻¹(·), ·)`, `σ g` on `ℝⁿ` and the identity on `H`. -/
theorem fiberMap_movPtP (ψ : (AP σ).Mor) {x x' : Fin n → ℝ}
    (hx : (AP σ).X.src ψ = ((x, h0) : (AP σ).Obj))
    (hx' : (AP σ).X.tgt ψ = ((x', h0) : (AP σ).Obj)) (k : (movPtP σ ψ hx hx').c.F 0) :
    ((movPtP σ ψ hx hx').fiberMap (stdPtP σ x') k : (Fin n → ℝ) × H 0) =
      (σ ψ.1.1).prodMap (ContinuousLinearMap.id ℝ (H 0)) k := by
  obtain ⟨N, -, hxN, -, hN⟩ := exists_srcInv_eqP ψ
  obtain ⟨⟨g, x₀⟩, e⟩ := ψ
  have h1 : x₀ = x := congrArg Prod.fst hx
  have h2 : e = h0 := congrArg Prod.snd hx
  have h3 : g • x₀ = x' := congrArg Prod.fst hx'
  subst h1 h2 h3
  have hz : (movPtP σ _ hx hx').c.φ.model.E.toBase 1 (movPtP σ _ hx hx').z =
      ((0 : Fin n → ℝ), (0 : H 0)) := Prod.ext rfl (map_zero _)
  rw [ChartPoint.fiberMap_apply, hz]
  revert k
  intro (k : (Fin n → ℝ) × H 0)
  set w : (AP σ).W := ((((0 : Fin n → ℝ) + x₀, k.1),
    ((LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm (0 : H 0), k.2)) : (AP σ).W) with hw
  change ((((AP σ).E.sectionAct ((AP σ).X.sheetAt ((g, x₀), h0)).srcInv w).1.2,
    ((AP σ).E.sectionAct ((AP σ).X.sheetAt ((g, x₀), h0)).srcInv w).2.2) : (Fin n → ℝ) × H 0) =
      (σ g k.1, k.2)
  have hy : (((0 : Fin n → ℝ) + x₀,
      (LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm (0 : H 0)) :
        (Fin n → ℝ) × HObj) ∈ N := by
    rw [symm_baseChart, zero_add]
    exact hxN
  have h : (AP σ).P w = (AP σ).X.src (((AP σ).X.sheetAt ((g, x₀), h0)).srcInv ((AP σ).P w)) := by
    change (((0 : Fin n → ℝ) + x₀,
      (LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm (0 : H 0)) :
        (Fin n → ℝ) × HObj) = (XP G n).src (((XP G n).sheetAt ((g, x₀), h0)).srcInv
          ((0 : Fin n → ℝ) + x₀,
            (LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm (0 : H 0)))
    erw [hN _ hy]
    rfl
  rw [(AP σ).E.sectionAct_of_eq _ h]
  change ((σ (((XP G n).sheetAt ((g, x₀), h0)).srcInv
    ((0 : Fin n → ℝ) + x₀, (LocalBundle.baseChart relOpen_H h0).toPartialEquiv.symm (0 : H 0))).1.1
      k.1, k.2) : (Fin n → ℝ) × H 0) = (σ g k.1, k.2)
  erw [hN _ hy]

/-! ### `Tφ` and `μ(φ, ·)` of a morphism read in the product charts -/

/-- **`Tψ` read in the product charts is `(v, w) ↦ (g • v, w)`**, `ψ = ((g, x), 0)`. -/
theorem morTx_stdP' (ψ : (AP σ).Mor) {x x' : Fin n → ℝ}
    (hx : (AP σ).X.src ψ = ((x, h0) : (AP σ).Obj))
    (hx' : (AP σ).X.tgt ψ = ((x', h0) : (AP σ).Obj))
    (hs : ((x, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (hs' : ((x', h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (v : ↥(orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).T) :
    orTEquivP σ x' hs' ((AP σ).E.morTx ψ hx hx' hs hs' v) =
      (ψ.1.1 • (orTEquivP σ x hs v).1, (orTEquivP σ x hs v).2) := by
  have e1 := (AP σ).E.morTx_eq ψ hx hx' hs hs' (resPtP σ ψ hx) (resPtP_sub σ ψ hx) v
  have e2 : (orPt (AP σ).B ((x', h0) : (AP σ).Obj) hs').transferT (stdPtP σ x')
      ((AP σ).E.morTx ψ hx hx' hs hs' v) = (movPtP σ ψ hx hx').transferT (stdPtP σ x')
        ((orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).transferT (resPtP σ ψ hx) v) :=
    (congrArg ((orPt (AP σ).B ((x', h0) : (AP σ).Obj) hs').transferT (stdPtP σ x')) e1).trans
      (ChartPoint.transferT_trans_apply _ _ _ _)
  have e3 : (orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).transferT (stdPtP σ x) v =
      (resPtP σ ψ hx).transferT (stdPtP σ x)
        ((orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).transferT (resPtP σ ψ hx) v) :=
    (ChartPoint.transferT_trans_apply _ _ _ _).symm
  set w := (orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).transferT (resPtP σ ψ hx) v
  set L : ((Fin n → ℝ) × H 0) →L[ℝ] ((Fin n → ℝ) × H 0) :=
    (rhoL ψ.1.1).prodMap (ContinuousLinearMap.id ℝ (H 0))
  calc orTEquivP σ x' hs' ((AP σ).E.morTx ψ hx hx' hs hs' v)
      = tEquivP σ x' ((movPtP σ ψ hx hx').transferT (stdPtP σ x') w) := congrArg (tEquivP σ x') e2
    _ = L (w : (resPtP σ ψ hx).c.φ.model.E 0) := baseDeriv_movPtP σ ψ hx hx' _
    _ = L (tEquivP σ x ((resPtP σ ψ hx).transferT (stdPtP σ x) w)) :=
        congrArg L (baseDeriv_resPtP σ ψ hx _).symm
    _ = L (orTEquivP σ x hs v) := congrArg (fun t => L (tEquivP σ x t)) e3.symm
    _ = _ := rfl

/-- **`μ(ψ, ·)` read in the product charts is `(k, w) ↦ (σ g k, w)`**, `ψ = ((g, x), 0)`. -/
theorem morKx_stdP' (ψ : (AP σ).Mor) {x x' : Fin n → ℝ}
    (hx : (AP σ).X.src ψ = ((x, h0) : (AP σ).Obj))
    (hx' : (AP σ).X.tgt ψ = ((x', h0) : (AP σ).Obj))
    (hs : ((x, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (hs' : ((x', h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (k : ↥(orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).K) :
    orKEquivP σ x' hs' ((AP σ).E.morKx ψ hx hx' hs hs' k) =
      (σ ψ.1.1 (orKEquivP σ x hs k).1, (orKEquivP σ x hs k).2) := by
  have e1 := (AP σ).E.morKx_eq ψ hx hx' hs hs' (resPtP σ ψ hx) (resPtP_sub σ ψ hx) k
  have e2 : (orPt (AP σ).B ((x', h0) : (AP σ).Obj) hs').transferK (stdPtP σ x')
      ((AP σ).E.morKx ψ hx hx' hs hs' k) = (movPtP σ ψ hx hx').transferK (stdPtP σ x')
        ((orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).transferK (resPtP σ ψ hx) k) :=
    (congrArg ((orPt (AP σ).B ((x', h0) : (AP σ).Obj) hs').transferK (stdPtP σ x')) e1).trans
      (ChartPoint.transferK_trans_apply _ _ _ _)
  have e3 : (orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).transferK (stdPtP σ x) k =
      (resPtP σ ψ hx).transferK (stdPtP σ x)
        ((orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).transferK (resPtP σ ψ hx) k) :=
    (ChartPoint.transferK_trans_apply _ _ _ _).symm
  set w := (orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).transferK (resPtP σ ψ hx) k
  set L : ((Fin n → ℝ) × H 0) →L[ℝ] ((Fin n → ℝ) × H 0) :=
    (σ ψ.1.1).prodMap (ContinuousLinearMap.id ℝ (H 0))
  calc orKEquivP σ x' hs' ((AP σ).E.morKx ψ hx hx' hs hs' k)
      = kEquivP σ x' ((movPtP σ ψ hx hx').transferK (stdPtP σ x') w) := congrArg (kEquivP σ x') e2
    _ = L (w : (resPtP σ ψ hx).c.F 0) := fiberMap_movPtP σ ψ hx hx' _
    _ = L (kEquivP σ x ((resPtP σ ψ hx).transferK (stdPtP σ x) w)) :=
        congrArg L (fiberMap_resPtP σ ψ hx _).symm
    _ = L (orKEquivP σ x hs k) := congrArg (fun t => L (kEquivP σ x t)) e3.symm
    _ = _ := rfl

/-- **`T((g, x), 0) : T_{(x, 0)} → T_{(g • x, 0)}` read in the product charts is
`(v, w) ↦ (g • v, w)`.** -/
theorem morTx_stdP (g : G) {x x' : Fin n → ℝ}
    (hx : (AP σ).X.src (((g, x), h0) : (AP σ).Mor) = ((x, h0) : (AP σ).Obj))
    (hx' : (AP σ).X.tgt (((g, x), h0) : (AP σ).Mor) = ((x', h0) : (AP σ).Obj))
    (hs : ((x, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (hs' : ((x', h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (v : ↥(orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).T) :
    orTEquivP σ x' hs' ((AP σ).E.morTx (((g, x), h0) : (AP σ).Mor) hx hx' hs hs' v) =
      (g • (orTEquivP σ x hs v).1, (orTEquivP σ x hs v).2) :=
  morTx_stdP' σ ((g, x), h0) hx hx' hs hs' v

/-- **`μ(((g, x), 0), ·)` read in the product charts is `(k, w) ↦ (σ g k, w)`.** -/
theorem morKx_stdP (g : G) {x x' : Fin n → ℝ}
    (hx : (AP σ).X.src (((g, x), h0) : (AP σ).Mor) = ((x, h0) : (AP σ).Obj))
    (hx' : (AP σ).X.tgt (((g, x), h0) : (AP σ).Mor) = ((x', h0) : (AP σ).Obj))
    (hs : ((x, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (hs' : ((x', h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (k : ↥(orPt (AP σ).B ((x, h0) : (AP σ).Obj) hs).K) :
    orKEquivP σ x' hs' ((AP σ).E.morKx (((g, x), h0) : (AP σ).Mor) hx hx' hs hs' k) =
      (σ g (orKEquivP σ x hs k).1, (orKEquivP σ x hs k).2) :=
  morKx_stdP' σ ((g, x), h0) hx hx' hs hs' k

/-- **At an isotropy morphism `((g, x), 0)`, `g • x = x`, `T((g, x), 0)` is conjugate to
`ρ(g) ⊕ id`.** -/
theorem morTx_eq_conjP (g : G) {x : Fin n → ℝ}
    (hgx : (AP σ).X.tgt (((g, x), h0) : (AP σ).Mor) = ((x, h0) : (AP σ).Obj))
    (hs : ((x, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet) :
    ⇑((AP σ).E.morTx (((g, x), h0) : (AP σ).Mor) (x := ((x, h0) : (AP σ).Obj)) rfl hgx hs hs) =
      ⇑(orTEquivP σ x hs).symm ∘ ⇑((rhoL g).prodMap (ContinuousLinearMap.id ℝ (H 0))) ∘
        ⇑(orTEquivP σ x hs) := by
  funext v
  apply (orTEquivP σ x hs).injective
  rw [morTx_stdP σ g rfl hgx hs hs v, comp_apply, comp_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- **At an isotropy morphism `((g, x), 0)`, `μ(((g, x), 0), ·)` is conjugate to
`σ(g) ⊕ id`.** -/
theorem morKx_eq_conjP (g : G) {x : Fin n → ℝ}
    (hgx : (AP σ).X.tgt (((g, x), h0) : (AP σ).Mor) = ((x, h0) : (AP σ).Obj))
    (hs : ((x, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet) :
    ⇑((AP σ).E.morKx (((g, x), h0) : (AP σ).Mor) (x := ((x, h0) : (AP σ).Obj)) rfl hgx hs hs) =
      ⇑(orKEquivP σ x hs).symm ∘ ⇑((σ g).prodMap (ContinuousLinearMap.id ℝ (H 0))) ∘
        ⇑(orKEquivP σ x hs) := by
  funext k
  apply (orKEquivP σ x hs).injective
  rw [morKx_stdP σ g rfl hgx hs hs k, comp_apply, comp_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

end Polyfold.Examples.Classical.Product
