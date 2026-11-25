import Polyfold.Examples.Classical.Setup
import Polyfold.Chapter18.OrientationWitness

/-!
# The classical reduction: morphisms of `G ⋉ ℝⁿ` read in the translation charts

For the strong bundle `ℝⁿ × ℝⁿ → ℝⁿ` over `G ⋉ ℝⁿ` (`Setup.lean`), the maps `Tφ` and `μ(φ, ·)`
of a morphism `φ = (g, x)` (§12.5, 2021 pp. 592–594; `EpStrongBundle.morTx`, `morKx`) and the
linearizations of graph sections (Definition 6.2.1, 2021), read in the translation chart points.

## What is formalized (namespace `Polyfold.Examples.Classical`)

* `stdPt σ x`: the chart point of the translation chart `y ↦ y − x` at `x` (with `z = 0`);
  `stdPt_T`, `stdPt_K`: its spaces `T_0` and `K_0` are all of `ℝⁿ`; `tEquiv`, `kEquiv`: the
  identifications with `ℝⁿ` (the coercions).
* `exists_srcInv_eq`: near `x` the inverse of `s` on the sheet of `(g, x)` is `y ↦ (g, y)`;
  `baseDeriv_movPt`, `fiberMap_movPt`: from the translation chart at `x` (restricted to the
  sheet) carried along the isomorphism of `(g, x)` to the translation chart at `g • x`, the base
  and fibre transitions are `g •` and `σ g`.
* **`morTx_std`**, **`morKx_std`**: `T(g, x)` and `μ((g, x), ·)`, read from the chosen chart
  points through the translation chart points, are `v ↦ g • v` and `k ↦ σ g k`.
* `morTx_eq_conj`, `morKx_eq_conj`, **`det_morTx`**, **`det_morKx`**: at an isotropy morphism
  (`g • x = x`) they are conjugate to `ρ(g)` and `σ(g)`, so `det T(g, x) = det ρ(g)` and
  `det μ((g, x), ·) = det σ(g)`.
* `stabT_std`, `stabT_std_fderiv`: `(f + S)'(y)` for the graph sections of `φ` and `ψ` is
  `D(φ + ψ)(y)` in the translation chart point; `zeroLin_std`: at a zero of the graph section of
  `φ` the linearization is `Dφ(y)`.
* `exists_mem_linSet_std`: every linear map `A : ℝⁿ → ℝⁿ` is read in the translation chart point
  as a member of `Lin(f, y)` (`(f + S)'(y)` for the graph section of `u ↦ A(u − y) − φ(u)`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical

open TrivialBundle EpGroupoid.Examples StrongBundle StrongRetr

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]
  (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))

theorem toBase_zero_chart (x : Fin n → ℝ) :
    (chart (k := n) x).φ.model.E.toBase 1 (0 : (chart (k := n) x).φ.model.E 1) =
      (chart (k := n) x).φ x := by
  rw [map_zero]
  exact (sub_self (show Fin n → ℝ from x)).symm

/-- The chart point of the translation chart `y ↦ y − x` at `x`, with `z = 0`. -/
def stdPt (x : Fin n → ℝ) : ChartPoint (AG (G := G) σ).B x :=
  chartPt (chart (k := n) x) (isChart_chart x) (mem_univ _) 0 (toBase_zero_chart x)

theorem stdPt_T (x : Fin n → ℝ) : (stdPt σ x).T = ⊤ := by
  change rangeS (scDeriv (chart (k := n) x).U (r (chart (k := n) x).R) 0) = ⊤
  rw [rangeS, scDeriv_r]
  exact LinearMap.range_id

theorem stdPt_K (x : Fin n → ℝ) : (stdPt σ x).K = ⊤ := by
  refine eq_top_iff.2 fun k _ => ⟨k, rfl⟩

theorem mem_stdPt_T (x : Fin n → ℝ) (v : (stdPt σ x).c.φ.model.E 0) :
    v ∈ (stdPt σ x).T := by
  rw [stdPt_T]; exact Submodule.mem_top

theorem mem_stdPt_K (x : Fin n → ℝ) (k : (stdPt σ x).c.F 0) :
    k ∈ (stdPt σ x).K := by
  rw [stdPt_K]; exact Submodule.mem_top

/-- `T_xℝⁿ` read in the translation chart point: `T_0ℝⁿ = ℝⁿ`. -/
def tEquiv (x : Fin n → ℝ) : ↥(stdPt σ x).T ≃L[ℝ] (Fin n → ℝ) where
  toFun v := (v : (stdPt σ x).c.φ.model.E 0)
  invFun w := ⟨w, mem_stdPt_T σ x w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

/-- The fibre `ℝⁿ` read in the translation chart point: `K_0 = ℝⁿ`. -/
def kEquiv (x : Fin n → ℝ) : ↥(stdPt σ x).K ≃L[ℝ] (Fin n → ℝ) where
  toFun k := (k : (stdPt σ x).c.F 0)
  invFun w := ⟨w, mem_stdPt_K σ x w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

@[simp] theorem tEquiv_apply (x : Fin n → ℝ) (v : ↥(stdPt σ x).T) :
    tEquiv σ x v = (v : (stdPt σ x).c.φ.model.E 0) := rfl

@[simp] theorem kEquiv_apply (x : Fin n → ℝ) (k : ↥(stdPt σ x).K) :
    kEquiv σ x k = (k : (stdPt σ x).c.F 0) := rfl

/-! ### Derivatives in `ℝⁿ` read through local agreement -/

/-- On `ℝⁿ` with the constant sc-structure, the sc-derivative at `z` of an sc¹ map which agrees
near `z` with a `C^∞` map `h` is `Dh(z)`. -/
theorem scDeriv_eq_fderiv_of_eqOn {m : ℕ} {C U N : Set (Fin n → ℝ)}
    (hU : IsRelOpenInQuadrant (rnSc n) C U) {f : (Fin n → ℝ) → (Fin m → ℝ)}
    (hf : IsSc1 (E := rnSc n) (F := rnSc m) U f) {z : (rnSc n) 1}
    (hz : (rnSc n).toBase 1 z ∈ U) (hN : IsOpen N) (hzN : (rnSc n).toBase 1 z ∈ N)
    {h : (Fin n → ℝ) → (Fin m → ℝ)} (hh : ContDiff ℝ ∞ h) (heq : EqOn f h (U ∩ N))
    {D : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)} (hD : HasFDerivAt h D ((rnSc n).toBase 1 z)) :
    scDeriv (E := rnSc n) (F := rnSc m) U f z = D := by
  have hh1 : IsSc1 (E := rnSc n) (F := rnSc m) univ h :=
    (isScSmooth_of_bijective_toBase (bijective_toBase_const _) (bijective_toBase_const _)
      (isScDomain_univ _) hh.contDiffOn).isSc1
  rw [scDeriv_eq_of_eqOn_relOpen (hU.inter_isOpen hN) hf hh1 inter_subset_left (subset_univ _)
    heq ⟨hz, hzN⟩]
  exact (scDeriv_univ_const hh z).trans hD.fderiv

/-! ### The sheet of a morphism `(g, x)` -/

/-- **Near `x`, the inverse of `s` on the sheet of `(g, x)` is `y ↦ (g, y)`** (`s` is
continuous with inverse through `(g, x)`, and `G` is discrete). -/
theorem exists_srcInv_eq (ψ : G × (Fin n → ℝ)) :
    ∃ N : Set (Fin n → ℝ), IsOpen N ∧ ψ.2 ∈ N ∧ N ⊆ ((XG G n).sheetAt ψ).srcSet ∧
      ∀ y ∈ N, ((XG G n).sheetAt ψ).srcInv y = (ψ.1, y) := by
  set S := (XG G n).sheetAt ψ
  have hs := S.isScDiffeoOn_src
  have hψ : S.srcInv ψ.2 = ψ := hs.left_inv ψ ((XG G n).mem_sheetAt ψ)
  have hψs : ψ.2 ∈ S.srcSet := hs.mapsTo ((XG G n).mem_sheetAt ψ)
  have ho : IsOpen (S.srcSet ∩ S.srcInv ⁻¹' (Prod.fst ⁻¹' {ψ.1})) :=
    hs.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hs.isOpen_target
      ((isOpen_discrete {ψ.1}).preimage continuous_fst)
  refine ⟨_, ho, ⟨hψs, ?_⟩, inter_subset_left, fun y hy => ?_⟩
  · change (S.srcInv ψ.2).1 = ψ.1
    rw [hψ]
  · have h1 : (S.srcInv y).1 = ψ.1 := hy.2
    have h2 : (S.srcInv y).2 = y := hs.right_inv y hy.1
    exact Prod.ext h1 h2

/-- The translation chart at `x` restricted to `s(sheet)` of a morphism `ψ` with `s(ψ) = x`. -/
def resPt (ψ : G × (Fin n → ℝ)) {x : Fin n → ℝ} (hx : (AG (G := G) σ).X.src ψ = x) :
    ChartPoint (AG (G := G) σ).B x :=
  chartPt ((chart (k := n) x).restrict (s := ((AG (G := G) σ).X.sheetAt ψ).srcSet)
      (subset_univ _) (EpStrongBundle.isOpen_srcSet (X := (AG (G := G) σ).X) ψ))
    ((isChart_chart x).restrict _ _) (EpStrongBundle.mem_srcSet (X := (AG (G := G) σ).X) hx) 0
    (toBase_zero_chart x)

theorem resPt_sub (ψ : G × (Fin n → ℝ)) {x : Fin n → ℝ} (hx : (AG (G := G) σ).X.src ψ = x) :
    (resPt σ ψ hx).c.φ.source ⊆ ((AG (G := G) σ).X.sheetAt ψ).srcSet := fun _ hw => hw

/-- From the restricted translation chart to the translation chart the base derivative is the
identity. -/
theorem baseDeriv_resPt (ψ : G × (Fin n → ℝ)) {x : Fin n → ℝ}
    (hx : (AG (G := G) σ).X.src ψ = x) (v : (resPt σ ψ hx).c.φ.model.E 0) :
    ((resPt σ ψ hx).baseDeriv (stdPt σ x) v : Fin n → ℝ) = v := by
  have h := scDeriv_eq_fderiv_of_eqOn (n := n) (m := n)
    ((resPt σ ψ hx).baseRet (stdPt σ x)).relOpen
    ((resPt σ ψ hx).isSc1_transition (stdPt σ x)) (z := (resPt σ ψ hx).z)
    ((resPt σ ψ hx).z_mem_baseRet (stdPt σ x)) isOpen_univ
    (mem_univ _) (ContinuousLinearMap.id ℝ (Fin n → ℝ)).contDiff (fun u _ => ?_)
    (ContinuousLinearMap.id ℝ (Fin n → ℝ)).hasFDerivAt
  · exact congrArg (fun T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => T v) h
  · change u + x - x = u
    exact add_sub_cancel_right u x

/-- The restricted translation chart at `s(ψ)` carried to `t(ψ)` along the isomorphism of `ψ`. -/
abbrev movPt (ψ : G × (Fin n → ℝ)) {x x' : Fin n → ℝ} (hx : (AG (G := G) σ).X.src ψ = x)
    (hx' : (AG (G := G) σ).X.tgt ψ = x') : ChartPoint (AG (G := G) σ).B x' :=
  ((AG (G := G) σ).E.morIso ψ).pullPt (resPt σ ψ hx) (resPt_sub σ ψ hx)
    (EpStrongBundle.mem_tgtSet hx') ((AG (G := G) σ).E.morIso_ϕ_eq hx hx')

/-- **From the carried chart to the translation chart at `g • x` the base derivative is
`v ↦ g • v`**: near `0` the base transition is `u ↦ g • (u + x) − g • x`. -/
theorem baseDeriv_movPt (ψ : G × (Fin n → ℝ)) {x x' : Fin n → ℝ}
    (hx : (AG (G := G) σ).X.src ψ = x) (hx' : (AG (G := G) σ).X.tgt ψ = x')
    (v : (movPt σ ψ hx hx').c.φ.model.E 0) :
    ((movPt σ ψ hx hx').baseDeriv (stdPt σ x') v : Fin n → ℝ) = rhoL ψ.1 v := by
  obtain ⟨N, hNo, hxN, -, hN⟩ := exists_srcInv_eq ψ
  subst hx hx'
  have h := scDeriv_eq_fderiv_of_eqOn (n := n) (m := n)
    ((movPt σ ψ rfl rfl).baseRet (stdPt σ _)).relOpen
    ((movPt σ ψ rfl rfl).isSc1_transition (stdPt σ _)) (z := (movPt σ ψ rfl rfl).z)
    ((movPt σ ψ rfl rfl).z_mem_baseRet (stdPt σ _)) (hNo.preimage (continuous_add_const ψ.2))
    (show (0 : Fin n → ℝ) + ψ.2 ∈ N by rw [zero_add]; exact hxN) (rhoL ψ.1).contDiff
    (fun u hu => ?_) (rhoL ψ.1).hasFDerivAt
  · exact congrArg (fun T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => T v) h
  · have hu' : u + ψ.2 ∈ N := hu.2
    change (XG G n).tgt (((XG G n).sheetAt ψ).srcInv (u + ψ.2)) - (XG G n).tgt ψ = ψ.1 • u
    rw [hN _ hu']
    change ψ.1 • (u + ψ.2) - ψ.1 • ψ.2 = ψ.1 • u
    rw [smul_add, add_sub_cancel_right]

/-- From the restricted translation chart to the translation chart the fibre transition is the
identity. -/
theorem fiberMap_resPt (ψ : G × (Fin n → ℝ)) {x : Fin n → ℝ}
    (hx : (AG (G := G) σ).X.src ψ = x) (k : (resPt σ ψ hx).c.F 0) :
    ((resPt σ ψ hx).fiberMap (stdPt σ x) k : Fin n → ℝ) = k := rfl

/-- **From the carried chart to the translation chart at `g • x` the fibre transition is
`σ g`**: the bundle map of the isomorphism of `ψ = (g, x)` is `μ(s⁻¹(x), ·) = μ((g, x), ·)` over
`x`. -/
theorem fiberMap_movPt (ψ : G × (Fin n → ℝ)) {x x' : Fin n → ℝ}
    (hx : (AG (G := G) σ).X.src ψ = x) (hx' : (AG (G := G) σ).X.tgt ψ = x')
    (k : (movPt σ ψ hx hx').c.F 0) :
    ((movPt σ ψ hx hx').fiberMap (stdPt σ x') k : Fin n → ℝ) = σ ψ.1 k := by
  obtain ⟨N, -, hxN, -, hN⟩ := exists_srcInv_eq ψ
  subst hx hx'
  have hy : (0 : Fin n → ℝ) + ψ.2 ∈ N := by rw [zero_add]; exact hxN
  have h : (AG (G := G) σ).P (((0 : Fin n → ℝ) + ψ.2, k) : (Fin n → ℝ) × (Fin n → ℝ)) =
      (AG (G := G) σ).X.src (((AG (G := G) σ).X.sheetAt ψ).srcInv
        ((AG (G := G) σ).P (((0 : Fin n → ℝ) + ψ.2, k) : (Fin n → ℝ) × (Fin n → ℝ)))) := by
    change (0 : Fin n → ℝ) + ψ.2 = (((XG G n).sheetAt ψ).srcInv ((0 : Fin n → ℝ) + ψ.2)).2
    rw [hN _ hy]
  change (((AG (G := G) σ).E.sectionAct ((AG (G := G) σ).X.sheetAt ψ).srcInv
    (((0 : Fin n → ℝ) + ψ.2, k) : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ))).2 =
      σ ψ.1 k
  rw [(AG (G := G) σ).E.sectionAct_of_eq _ h]
  change σ (((XG G n).sheetAt ψ).srcInv ((0 : Fin n → ℝ) + ψ.2)).1 k = σ ψ.1 k
  rw [hN _ hy]

/-! ### `Tφ` and `μ(φ, ·)` of a morphism read in the translation charts -/

/-- **`Tψ` read in the translation charts is `v ↦ g • v`**, `ψ = (g, x)`. -/
theorem morTx_std' (ψ : G × (Fin n → ℝ)) {x x' : Fin n → ℝ}
    (hx : (AG (G := G) σ).X.src ψ = x) (hx' : (AG (G := G) σ).X.tgt ψ = x')
    (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet) (hs' : x' ∈ (AG (G := G) σ).X.PObj.smoothSet)
    (v : ↥(orPt (AG (G := G) σ).B x hs).T) :
    tEquiv σ x' ((orPt (AG (G := G) σ).B x' hs').transferT (stdPt σ x')
        ((AG (G := G) σ).E.morTx ψ hx hx' hs hs' v)) =
      ψ.1 • tEquiv σ x ((orPt (AG (G := G) σ).B x hs).transferT (stdPt σ x) v) := by
  have e1 := (AG (G := G) σ).E.morTx_eq ψ hx hx' hs hs' (resPt σ ψ hx) (resPt_sub σ ψ hx) v
  have e2 : (orPt (AG (G := G) σ).B x' hs').transferT (stdPt σ x')
      ((AG (G := G) σ).E.morTx ψ hx hx' hs hs' v) = (movPt σ ψ hx hx').transferT (stdPt σ x')
        ((orPt (AG (G := G) σ).B x hs).transferT (resPt σ ψ hx) v) :=
    (congrArg ((orPt (AG (G := G) σ).B x' hs').transferT (stdPt σ x')) e1).trans
      (ChartPoint.transferT_trans_apply _ _ _ _)
  have e3 : (orPt (AG (G := G) σ).B x hs).transferT (stdPt σ x) v =
      (resPt σ ψ hx).transferT (stdPt σ x)
        ((orPt (AG (G := G) σ).B x hs).transferT (resPt σ ψ hx) v) :=
    (ChartPoint.transferT_trans_apply _ _ _ _).symm
  set w := (orPt (AG (G := G) σ).B x hs).transferT (resPt σ ψ hx) v
  calc _ = tEquiv σ x' ((movPt σ ψ hx hx').transferT (stdPt σ x') w) := congrArg (tEquiv σ x') e2
    _ = rhoL ψ.1 (w : (resPt σ ψ hx).c.φ.model.E 0) := baseDeriv_movPt σ ψ hx hx' _
    _ = rhoL ψ.1 (tEquiv σ x ((resPt σ ψ hx).transferT (stdPt σ x) w)) :=
        congrArg (rhoL ψ.1) (baseDeriv_resPt σ ψ hx _).symm
    _ = _ := congrArg (fun t => rhoL ψ.1 (tEquiv σ x t)) e3.symm

/-- **`μ(ψ, ·)` read in the translation charts is `σ g`**, `ψ = (g, x)`. -/
theorem morKx_std' (ψ : G × (Fin n → ℝ)) {x x' : Fin n → ℝ}
    (hx : (AG (G := G) σ).X.src ψ = x) (hx' : (AG (G := G) σ).X.tgt ψ = x')
    (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet) (hs' : x' ∈ (AG (G := G) σ).X.PObj.smoothSet)
    (k : ↥(orPt (AG (G := G) σ).B x hs).K) :
    kEquiv σ x' ((orPt (AG (G := G) σ).B x' hs').transferK (stdPt σ x')
        ((AG (G := G) σ).E.morKx ψ hx hx' hs hs' k)) =
      σ ψ.1 (kEquiv σ x ((orPt (AG (G := G) σ).B x hs).transferK (stdPt σ x) k)) := by
  have e1 := (AG (G := G) σ).E.morKx_eq ψ hx hx' hs hs' (resPt σ ψ hx) (resPt_sub σ ψ hx) k
  have e2 : (orPt (AG (G := G) σ).B x' hs').transferK (stdPt σ x')
      ((AG (G := G) σ).E.morKx ψ hx hx' hs hs' k) = (movPt σ ψ hx hx').transferK (stdPt σ x')
        ((orPt (AG (G := G) σ).B x hs).transferK (resPt σ ψ hx) k) :=
    (congrArg ((orPt (AG (G := G) σ).B x' hs').transferK (stdPt σ x')) e1).trans
      (ChartPoint.transferK_trans_apply _ _ _ _)
  have e3 : (orPt (AG (G := G) σ).B x hs).transferK (stdPt σ x) k =
      (resPt σ ψ hx).transferK (stdPt σ x)
        ((orPt (AG (G := G) σ).B x hs).transferK (resPt σ ψ hx) k) :=
    (ChartPoint.transferK_trans_apply _ _ _ _).symm
  set w := (orPt (AG (G := G) σ).B x hs).transferK (resPt σ ψ hx) k
  calc _ = kEquiv σ x' ((movPt σ ψ hx hx').transferK (stdPt σ x') w) := congrArg (kEquiv σ x') e2
    _ = σ ψ.1 (w : (resPt σ ψ hx).c.F 0) := fiberMap_movPt σ ψ hx hx' _
    _ = σ ψ.1 (kEquiv σ x ((resPt σ ψ hx).transferK (stdPt σ x) w)) :=
        congrArg (σ ψ.1) (fiberMap_resPt σ ψ hx _).symm
    _ = _ := congrArg (fun t => σ ψ.1 (kEquiv σ x t)) e3.symm

/-- **`T(g, x) : T_xℝⁿ → T_{g•x}ℝⁿ` read in the translation charts is `v ↦ g • v`.** -/
theorem morTx_std (g : G) {x x' : Fin n → ℝ}
    (hx : (AG (G := G) σ).X.src ((g, x) : (AG (G := G) σ).Mor) = x)
    (hx' : (AG (G := G) σ).X.tgt ((g, x) : (AG (G := G) σ).Mor) = x')
    (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet) (hs' : x' ∈ (AG (G := G) σ).X.PObj.smoothSet)
    (v : ↥(orPt (AG (G := G) σ).B x hs).T) :
    tEquiv σ x' ((orPt (AG (G := G) σ).B x' hs').transferT (stdPt σ x')
        ((AG (G := G) σ).E.morTx ((g, x) : (AG (G := G) σ).Mor) hx hx' hs hs' v)) =
      g • tEquiv σ x ((orPt (AG (G := G) σ).B x hs).transferT (stdPt σ x) v) :=
  morTx_std' σ (g, x) hx hx' hs hs' v

/-- **`μ((g, x), ·) : W_x → W_{g•x}` read in the translation charts is `σ g`.** -/
theorem morKx_std (g : G) {x x' : Fin n → ℝ}
    (hx : (AG (G := G) σ).X.src ((g, x) : (AG (G := G) σ).Mor) = x)
    (hx' : (AG (G := G) σ).X.tgt ((g, x) : (AG (G := G) σ).Mor) = x')
    (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet) (hs' : x' ∈ (AG (G := G) σ).X.PObj.smoothSet)
    (k : ↥(orPt (AG (G := G) σ).B x hs).K) :
    kEquiv σ x' ((orPt (AG (G := G) σ).B x' hs').transferK (stdPt σ x')
        ((AG (G := G) σ).E.morKx ((g, x) : (AG (G := G) σ).Mor) hx hx' hs hs' k)) =
      σ g (kEquiv σ x ((orPt (AG (G := G) σ).B x hs).transferK (stdPt σ x) k)) :=
  morKx_std' σ (g, x) hx hx' hs hs' k

/-! ### Determinants at an isotropy morphism -/

/-- `T_xℝⁿ` read in the chosen chart point and identified with `ℝⁿ`. -/
def orTEquiv (x : Fin n → ℝ) (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet) :
    ↥(orPt (AG (G := G) σ).B x hs).T ≃L[ℝ] (Fin n → ℝ) :=
  ((orPt (AG (G := G) σ).B x hs).transferT (stdPt σ x)).trans (tEquiv σ x)

/-- `W_x` read in the chosen chart point and identified with `ℝⁿ`. -/
def orKEquiv (x : Fin n → ℝ) (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet) :
    ↥(orPt (AG (G := G) σ).B x hs).K ≃L[ℝ] (Fin n → ℝ) :=
  ((orPt (AG (G := G) σ).B x hs).transferK (stdPt σ x)).trans (kEquiv σ x)

/-- **At an isotropy morphism `(g, x)`, `g • x = x`, `T(g, x)` is conjugate to `ρ(g)`.** -/
theorem morTx_eq_conj (g : G) {x : Fin n → ℝ}
    (hgx : (AG (G := G) σ).X.tgt ((g, x) : (AG (G := G) σ).Mor) = x)
    (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet) :
    (((AG (G := G) σ).E.morTx ((g, x) : (AG (G := G) σ).Mor) (x := x) rfl hgx hs hs :
        ↥(orPt (AG (G := G) σ).B x hs).T →L[ℝ] ↥(orPt (AG (G := G) σ).B x hs).T) :
        ↥(orPt (AG (G := G) σ).B x hs).T →ₗ[ℝ] ↥(orPt (AG (G := G) σ).B x hs).T) =
      ((orTEquiv σ x hs).symm : (Fin n → ℝ) →ₗ[ℝ] ↥(orPt (AG (G := G) σ).B x hs).T) ∘ₗ
        ((rhoL g : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ
          ((orTEquiv σ x hs) : ↥(orPt (AG (G := G) σ).B x hs).T →ₗ[ℝ] (Fin n → ℝ)) := by
  refine LinearMap.ext fun v => (orTEquiv σ x hs).injective ?_
  change orTEquiv σ x hs ((AG (G := G) σ).E.morTx ((g, x) : (AG (G := G) σ).Mor) (x := x) rfl hgx
    hs hs v) = orTEquiv σ x hs ((orTEquiv σ x hs).symm (rhoL g (orTEquiv σ x hs v)))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact morTx_std σ g rfl hgx hs hs v

/-- **At an isotropy morphism `(g, x)`, `μ((g, x), ·)` is conjugate to `σ(g)`.** -/
theorem morKx_eq_conj (g : G) {x : Fin n → ℝ}
    (hgx : (AG (G := G) σ).X.tgt ((g, x) : (AG (G := G) σ).Mor) = x)
    (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet) :
    (((AG (G := G) σ).E.morKx ((g, x) : (AG (G := G) σ).Mor) (x := x) rfl hgx hs hs :
        ↥(orPt (AG (G := G) σ).B x hs).K →L[ℝ] ↥(orPt (AG (G := G) σ).B x hs).K) :
        ↥(orPt (AG (G := G) σ).B x hs).K →ₗ[ℝ] ↥(orPt (AG (G := G) σ).B x hs).K) =
      ((orKEquiv σ x hs).symm : (Fin n → ℝ) →ₗ[ℝ] ↥(orPt (AG (G := G) σ).B x hs).K) ∘ₗ
        ((σ g : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ
          ((orKEquiv σ x hs) : ↥(orPt (AG (G := G) σ).B x hs).K →ₗ[ℝ] (Fin n → ℝ)) := by
  refine LinearMap.ext fun k => (orKEquiv σ x hs).injective ?_
  change orKEquiv σ x hs ((AG (G := G) σ).E.morKx ((g, x) : (AG (G := G) σ).Mor) (x := x) rfl hgx
    hs hs k) = orKEquiv σ x hs ((orKEquiv σ x hs).symm (σ g (orKEquiv σ x hs k)))
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact morKx_std σ g rfl hgx hs hs k

/-- **`det T(g, x) = det ρ(g)`** at an isotropy morphism `(g, x)`. -/
theorem det_morTx (g : G) {x : Fin n → ℝ}
    (hgx : (AG (G := G) σ).X.tgt ((g, x) : (AG (G := G) σ).Mor) = x)
    (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet) :
    LinearMap.det (((AG (G := G) σ).E.morTx ((g, x) : (AG (G := G) σ).Mor) (x := x) rfl hgx hs hs :
        ↥(orPt (AG (G := G) σ).B x hs).T →L[ℝ] ↥(orPt (AG (G := G) σ).B x hs).T) :
        ↥(orPt (AG (G := G) σ).B x hs).T →ₗ[ℝ] ↥(orPt (AG (G := G) σ).B x hs).T) =
      LinearMap.det ((rhoL g : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := by
  rw [morTx_eq_conj]
  exact LinearMap.det_conj _ (orTEquiv σ x hs).symm.toLinearEquiv

/-- **`det μ((g, x), ·) = det σ(g)`** at an isotropy morphism `(g, x)`. -/
theorem det_morKx (g : G) {x : Fin n → ℝ}
    (hgx : (AG (G := G) σ).X.tgt ((g, x) : (AG (G := G) σ).Mor) = x)
    (hs : x ∈ (AG (G := G) σ).X.PObj.smoothSet) :
    LinearMap.det (((AG (G := G) σ).E.morKx ((g, x) : (AG (G := G) σ).Mor) (x := x) rfl hgx hs hs :
        ↥(orPt (AG (G := G) σ).B x hs).K →L[ℝ] ↥(orPt (AG (G := G) σ).B x hs).K) :
        ↥(orPt (AG (G := G) σ).B x hs).K →ₗ[ℝ] ↥(orPt (AG (G := G) σ).B x hs).K) =
      LinearMap.det ((σ g : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := by
  rw [morKx_eq_conj]
  exact LinearMap.det_conj _ (orKEquiv σ x hs).symm.toLinearEquiv

/-! ### Linearizations of graph sections in the translation chart point -/

/-- The sum of two graph sections is the graph section of the sum. -/
theorem sectionAdd_graphSection_std (φ ψ : (Fin n → ℝ) → (Fin n → ℝ)) :
    sectionAdd (proj n n) (graphSection φ) (graphSection ψ) = graphSection (φ + ψ) := by
  funext x
  rw [sectionAdd_apply isSection_graphSection isSection_graphSection]
  exact Prod.ext (fst_fiber _) (snd_add _ _)

theorem mem_smoothSet_AG_std (y : Fin n → ℝ) : y ∈ (AG (G := G) σ).X.PObj.smoothSet := by
  change y ∈ (rnPolyfold n).smoothSet
  rw [rnPolyfold_smoothSet]
  exact mem_univ y

/-- **`(f + S)'(y)` read in the translation chart point is `D(φ + ψ)(y)`** for the graph
sections `f = (x, φ(x))` and `S = (x, ψ(x))`. -/
theorem stabT_std {φ ψ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) (hf : (AG (G := G) σ).B.IsScFredholmSection (fSec φ))
    (hS : (AG (G := G) σ).B.IsScPlusSection (graphSection ψ)) {y : Fin n → ℝ}
    (h0 : IsZeroAt (AG (G := G) σ).P
      (sectionAdd (AG (G := G) σ).P (fSec φ) (graphSection ψ)) y)
    {D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (hD : HasFDerivAt (φ + ψ) D y)
    (v : ↥(stdPt σ y).T) :
    kEquiv σ y ((stdPt σ y).stabT hf hS h0 v) = D (tEquiv σ y v) := by
  have he : ((chart (k := n) y).principal (sectionAdd (proj n n) (graphSection φ)
      (graphSection ψ)) ∘ r (chart (k := n) y).R) = loc (φ + ψ) y := by
    rw [sectionAdd_graphSection_std]
    funext u
    rfl
  change scDeriv (chart (k := n) y).U ((chart (k := n) y).principal
    (sectionAdd (proj n n) (graphSection φ) (graphSection ψ)) ∘ r (chart (k := n) y).R) 0
      (v : (stdPt σ y).c.φ.model.E 0) = _
  rw [he]
  exact (congrArg (fun T : (rnSc n) 0 →L[ℝ] (rnSc n) 0 => T (v : (stdPt σ y).c.φ.model.E 0))
    (scDeriv_loc (show ContDiff ℝ ∞ (φ + ψ) from hφ.add hψ) y)).trans
      (DFunLike.congr_fun hD.fderiv _)

/-- The fderiv form of `stabT_std`. -/
theorem stabT_std_fderiv {φ ψ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) (hf : (AG (G := G) σ).B.IsScFredholmSection (fSec φ))
    (hS : (AG (G := G) σ).B.IsScPlusSection (graphSection ψ)) {y : Fin n → ℝ}
    (h0 : IsZeroAt (AG (G := G) σ).P
      (sectionAdd (AG (G := G) σ).P (fSec φ) (graphSection ψ)) y)
    (v : ↥(stdPt σ y).T) :
    kEquiv σ y ((stdPt σ y).stabT hf hS h0 v) = fderiv ℝ (φ + ψ) y (tEquiv σ y v) :=
  stabT_std σ hφ hψ hf hS h0 (((hφ.add hψ).differentiable (by simp)) y).hasFDerivAt v

/-- **The linearization `D(f̂ ∘ r)(y)` at a zero of the graph section `f = (x, φ(x))`, read in
the translation chart point, is `Dφ(y)`.** -/
theorem zeroLin_std {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (hg : (AG (G := G) σ).B.IsScSmoothSection (fSec φ)) {y : Fin n → ℝ}
    (h0 : IsZeroAt (AG (G := G) σ).P (fSec φ) y) (v : ↥(stdPt σ y).T) :
    kEquiv σ y ((stdPt σ y).zeroLin hg h0 v) = fderiv ℝ φ y (tEquiv σ y v) := by
  change scDeriv (chart (k := n) y).U ((chart (k := n) y).principal (graphSection φ) ∘
    r (chart (k := n) y).R) 0 (v : (stdPt σ y).c.φ.model.E 0) = _
  have he : ((chart (k := n) y).principal (graphSection φ) ∘ r (chart (k := n) y).R) =
      loc φ y := by
    funext u
    rfl
  rw [he, scDeriv_loc hφ y]
  rfl

/-- **Every linear map `ℝⁿ → ℝⁿ` is read in the translation chart point as a member of
`Lin(f, y)`** for the graph section `f = (x, φ(x))` of a `C^∞` map: it is `(f + S)'(y)` for the
graph section `S` of `u ↦ A(u − y) − φ(u)`. -/
theorem exists_mem_linSet_std {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContDiff ℝ ∞ φ)
    (hf : (AG (G := G) σ).B.IsScFredholmSection (fSec φ)) (y : Fin n → ℝ)
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    ∃ L : ↥(stdPt σ y).T →L[ℝ] ↥(stdPt σ y).K,
      L ∈ (stdPt σ y).linSet (B := (AG (G := G) σ).B) (fSec φ) ∧
        ∀ v, kEquiv σ y (L v) = A (tEquiv σ y v) := by
  set ψ : (Fin n → ℝ) → (Fin n → ℝ) := fun u => A (u - y) - φ u with hψdef
  have hψ : ContDiff ℝ ∞ ψ := (A.contDiff.comp (contDiff_id.sub contDiff_const)).sub hφ
  have hsum : φ + ψ = fun u => A (u - y) := by
    funext u
    change φ u + (A (u - y) - φ u) = A (u - y)
    rw [add_sub_cancel]
  have hS : (bundle n n).IsScPlusSection (graphSection ψ) := isScPlusSection_graphSection hψ
  have h0 : IsZeroAt (AG (G := G) σ).P
      (sectionAdd (AG (G := G) σ).P (fSec φ) (graphSection ψ)) y := by
    change IsZeroAt (proj n n) (sectionAdd (proj n n) (graphSection φ) (graphSection ψ)) y
    rw [sectionAdd_graphSection_std, hsum]
    refine isZeroAt_graphSection_iff.2 ?_
    rw [sub_self, map_zero]
  have hD : HasFDerivAt (φ + ψ) A y := by
    rw [hsum]
    have := A.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const y)
    simpa using this
  exact ⟨(stdPt σ y).stabT hf hS h0,
    (stdPt σ y).stabT_mem_linSet hf hS h0 (mem_smoothSet_AG_std σ y),
    fun v => stabT_std σ hφ hψ hf hS h0 hD v⟩

end Polyfold.Examples.Classical
