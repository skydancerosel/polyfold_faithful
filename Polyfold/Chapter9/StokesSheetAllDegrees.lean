import Polyfold.Chapter9.StokesSheet

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, proof of **Theorems 9.5.17 and 9.5.18 (Stokes), pp. 450–451** (2017:
Theorems 9.6, 9.7), gap G.110.  Numbers and pages are the 2021 text's.

# Stokes on the sheets of one `U(x_k)`, in every dimension `n = m + 1 ≥ 1`

The statements of `StokesSheet.lean` carry the hypothesis `0 < m` (dimension `n ≥ 2`):
there the restriction of `β·ω` to a sheet is read through the evaluation on frames, which is cut
off to `0` in degree `0`.  Here the product rule `(β·ω)|_N = β·(ω|_N)` is proved from the
definitions of the product and of the restriction, in every degree `k ≥ 0`, and the statements
are restated without `0 < m` (suffix `_all`).

## What is formalized

* `BundledMPolyfold.castFun`, `castForms_formSmulFun`, `EP.castFun_liftFun`: the product `β·ω`
  on `Ωᵏ_ep(Xⁱ)` read in `Ωᵏ((Ob X)ⁱ)`.
* **`EP.formsInftyRestrict_epFormsInftySmul_all`**: `(β·a)|_N = β·(a|_N)`, every degree.
* `EP.formsInftyRestrict_smul_eq_zero_all`, `EP.formsInftyRestrict_d_smul_eq_zero_all`:
  `(β·ω)|_N` and `(d(β·ω))|_N` vanish off `supp β`, every degree.
* `EP.integ_d_smul_eq_zero_all`, `EP.integ_d_smul_eq_boundaryIntegral_all`,
  **`EP.stokes_one_structure_all`**, `EP.stokes_off_support_all`: E5's statements without the
  hypothesis `0 < m`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

universe u

open MPolyfold

/-! ### The product `β·ω` under the transport of forms -/

namespace BundledMPolyfold

variable {k : ℕ}

/-- Transport of a real function along an equality of bundled M-polyfolds. -/
def castFun {B B' : BundledMPolyfold.{u}} (h : B = B') (β : B.carrier → ℝ) : B'.carrier → ℝ := by
  subst h
  exact β

theorem castFun_comp_levelVal {B B' : BundledMPolyfold.{u}} (h : B = B') (β : B.carrier → ℝ) :
    castFun (congrArg BundledMPolyfold.shift h) (β ∘ B.P.levelVal 1) =
      castFun h β ∘ B'.P.levelVal 1 := by
  subst h
  rfl

/-- The transport of forms commutes with the product by a function. -/
theorem castForms_formSmulFun {B B' : BundledMPolyfold.{u}} (h : B = B') (β : B.carrier → ℝ)
    (ω ω' : B.P.scForms k) (hω : ω'.1 = MPolyfold.formSmulFun β ω.1) :
    (castForms k h ω').1 = MPolyfold.formSmulFun (castFun h β) (castForms k h ω).1 := by
  subst h
  exact hω

end BundledMPolyfold

namespace EP

variable (A : EP.{u}) {n k : ℕ}

/-- `β|Xⁱ`, read on `(Ob X)ⁱ`, is `β` after the inclusion `(Ob X)ⁱ → Ob X`. -/
theorem castFun_liftFun (β : A.Obj → ℝ) : ∀ i : ℕ,
    BundledMPolyfold.castFun (B := (A.lift i).objPolyfold) (A.objPolyfold_lift i)
      (A.liftFun β i) = β ∘ A.objPolyfold.incl i
  | 0 => rfl
  | i + 1 =>
    (BundledMPolyfold.castFun_comp_levelVal (B := (A.lift i).objPolyfold)
      (A.objPolyfold_lift i) (A.liftFun β i)).trans
      (congrArg (· ∘ (A.objPolyfold.lift i).P.levelVal 1) (castFun_liftFun β i))

variable {N : Set A.Obj} [ParacompactSpace N] {hY : A.X.PObj.IsSubMPolyfold N}
  {hcs : (subPolyfold hY).HasCornerStructureOfDim n}
  [inst : ChartedSpace (EuclideanQuadrant n) N] {β : A.Obj → ℝ}

/-- **`(β·a)|_N = β·(a|_N)` in every degree `k ≥ 0`** (2021 Theorem 9.5.18, proof, p. 451:
`ω_k = β_k ω`), for an sc-smooth function `β` constant on the orbits and a sheet `N` with a
corner structure: E5's `formsInftyRestrict_epFormsInftySmul` without the hypothesis `0 < k`
(and without the smoothness of `N`), from the definitions of the product and the restriction. -/
theorem formsInftyRestrict_epFormsInftySmul_all
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (a : A.epFormsInfty k) (y : N)
    (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    formsInftyRestrict k hcs (A.epFormsInftyToObj k (A.epFormsInftySmul β k hβ hinv a)) y v =
      β y.1 * formsInftyRestrict k hcs (A.epFormsInftyToObj k a) y v := by
  obtain ⟨i, ω, rfl⟩ := A.exists_epFormsInftyOf_eq k a
  rw [epFormsInftySmul_of, epFormsInftyToObj_of, epFormsInftyToObj_of]
  have e : ∀ τ : A.objPolyfold.forms k i,
      formsInftyRestrict k hcs (A.objPolyfold.formsInftyOf k i τ) = scFormRestrict k hcs i τ :=
    fun τ => formsInftyRestrict_of hcs i τ
  rw [e, e]
  set g : ScMap (subPolyfold hY) A.objPolyfold.P := subInclScMap hY with hg
  have h1 : (A.epFormsToObj k i (A.epFormsSmul β k hβ hinv i ω)).1 =
      MPolyfold.formSmulFun (β ∘ A.objPolyfold.incl i) (A.epFormsToObj k i ω).1 := by
    rw [← A.castFun_liftFun β i]
    exact BundledMPolyfold.castForms_formSmulFun (B := (A.lift i).objPolyfold)
      (A.objPolyfold_lift i) (A.liftFun β i) (A.epFormsToForms k i ω)
      (A.epFormsToForms k i (A.epFormsSmul β k hβ hinv i ω)) rfl
  have e0 : ∀ τ : A.objPolyfold.forms k i, scFormRestrict k hcs i τ y v =
      τ.1 (liftLevelOneMap (alongLift hcs g i).isScSmoothMap (hcs.levelOne y)) fun j =>
        tangentFiberMap (alongLift hcs g i).isScSmoothMap (hcs.levelOne y)
          ((hcs.coords y).fiberMap (hcs.levelOne_mem_coords y) (v j)) := fun τ => rfl
  rw [e0, e0, h1, MPolyfold.formSmulFun_apply]
  congr 1
  exact congrArg β (incl_alongLift hcs g i y)

/-- **`(β·ω)|_N` vanishes off the support of `β`, in every degree** (E5's
`formsInftyRestrict_smul_eq_zero` without the hypothesis `0 < k`). -/
theorem formsInftyRestrict_smul_eq_zero_all (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (ω : A.epFormsInfty k) (y : N)
    (hy : y.1 ∉ tsupport β) :
    formsInftyRestrict k hcs (A.epFormsInftyToObj k (A.epFormsInftySmul β k hβ hinv ω)) y =
      0 := by
  ext v
  rw [A.formsInftyRestrict_epFormsInftySmul_all hβ hinv ω y v,
    image_eq_zero_of_notMem_tsupport hy, zero_mul]
  rfl

/-- **`(d(β·ω))|_N` vanishes off the support of `β`, in every degree** (`d` is local on the
manifold `N`; E5's `formsInftyRestrict_d_smul_eq_zero` without the hypothesis `0 < k`). -/
theorem formsInftyRestrict_d_smul_eq_zero_all
    (hch : inst = (subPolyfold hY).cornerChartedSpace hcs)
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (ω : A.epFormsInfty k) (y : N)
    (hy : y.1 ∉ tsupport β) :
    formsInftyRestrict (k + 1) hcs (A.epFormsInftyToObj (k + 1)
      (A.epFormsInftyD k (A.epFormsInftySmul β k hβ hinv ω))) y = 0 := by
  set a := A.epFormsInftySmul β k hβ hinv ω with ha
  have e : A.epFormsInftyToObj (k + 1) (A.epFormsInftyD k a) =
      A.objPolyfold.formsInftyD k (A.epFormsInftyToObj k a) :=
    (LinearMap.congr_fun (A.formsInftyD_comp_epFormsInftyToObj k) a).symm
  have e2 := extDeriv_formsInftyRestrict (hcs := hcs) hch (A.epFormsInftyToObj k a)
  rw [e]
  refine (congrFun e2.symm y).trans ?_
  refine ManifoldForm.extDeriv_eq_zero_of_eventually_eq_zero ?_
  have hopen : IsOpen {z : N | z.1 ∉ tsupport β} :=
    (isClosed_tsupport β).isOpen_compl.preimage continuous_subtype_val
  filter_upwards [hopen.mem_nhds hy] with z hz
  exact A.formsInftyRestrict_smul_eq_zero_all hβ hinv ω z hz

/-! ### The sheets of one structure -/

variable {m : ℕ} {Θ : A.Obj → ℚ}

/-- **The integrals of `d(β·ω)` over the subsets of a sheet disjoint from `supp β` vanish**
(2021 p. 451), for sheets of every dimension `m + 1 ≥ 1`: E5's `integ_d_smul_eq_zero` without the
hypothesis `0 < m`. -/
theorem integ_d_smul_eq_zero_all {x : A.Obj}
    (C : A.X.OrientedTameStructure (m + 1) Θ x) (i : C.ι)
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (ω : A.epFormsInfty m) {B : Set A.Obj}
    (hd : Disjoint B (tsupport β)) :
    (A.epFormsInftyEval (m + 1)).integ (A.epFormsInftyD m (A.epFormsInftySmul β m hβ hinv ω))
      (C.M i) (C.orient i).tangent B = 0 := by
  let _ := A.X.PObj.paracompactSpace_subtype (C.M i)
  let hcs := C.toTameBranchingStructure.hasCornerStructureOfDim C.isSubmanifoldOfDim i
  let _ := (subPolyfold (C.isSubmanifoldOfDim i).1.isSubMPolyfold).cornerChartedSpace hcs
  refine EpGroupoid.FormEval.integ_eq_zero_of_ev_eq_zero _ _ _ fun y hy α hα => ?_
  exact A.epFormsInftyEval_eq_zero_of_restrict (hcs := hcs) (Nat.succ_pos m)
    (C.isSubmanifoldOfDim i) (C.orient i) _ ⟨y, hy.2⟩
    (A.formsInftyRestrict_d_smul_eq_zero_all rfl hβ hinv ω ⟨y, hy.2⟩
      fun h => Set.disjoint_left.1 hd hy.1 h) hα

/-- **The standard Stokes theorem on one sheet, for the integral of §9.5** (the third equality of
the display on p. 451, proof of Theorem 9.5.18), for sheets of every dimension `m + 1 ≥ 1`:
`∫_{(Mᵢ,oᵢ)} d(βω) = ∫_{∂(Mᵢ,oᵢ)} βω` for `supp β ⊆ U(x)^*`, `Θ` compact.  E5's
`integ_d_smul_eq_boundaryIntegral` without the hypothesis `0 < m`. -/
theorem integ_d_smul_eq_boundaryIntegral_all (hcpt : A.X.IsCompactBranched Θ)
    {x : A.Obj} (C : A.X.OrientedTameStructure (m + 1) Θ x)
    (hS : ∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets)
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ))
    (hsupp : tsupport β ⊆ A.X.π ⁻¹' (A.X.π '' C.U)) (ω : A.epFormsInfty m) (i : C.ι) :
    (A.epFormsInftyEval (m + 1)).integ (A.epFormsInftyD m (A.epFormsInftySmul β m hβ hinv ω))
        (C.M i) (C.orient i).tangent (C.M i) =
      (C.orientedSheet (A.epFormsInftyEval (m + 1)) hS i).boundaryIntegral
        (A.epFormsInftyToObj m (A.epFormsInftySmul β m hβ hinv ω)) := by
  set a := A.epFormsInftySmul β m hβ hinv ω with ha
  set Ns := C.orientedSheet (A.epFormsInftyEval (m + 1)) hS i with hNs
  have hK : IsCompact (C.M i ∩ tsupport β) :=
    C.toTameBranchingStructure.isCompact_inter hcpt (isClosed_tsupport β)
      (EpGroupoid.isSaturated_tsupport hinv) hsupp i
  let _ := A.X.PObj.paracompactSpace_subtype (C.M i)
  have := EpGroupoid.FormEval.sigmaCompactSpace_of_mem_sheets (hS i)
  let hcs := C.toTameBranchingStructure.hasCornerStructureOfDim C.isSubmanifoldOfDim i
  let _ := (subPolyfold (C.isSubmanifoldOfDim i).1.isSubMPolyfold).cornerChartedSpace hcs
  have := (subPolyfold (C.isSubmanifoldOfDim i).1.isSubMPolyfold).isManifold_cornerChartedSpace
    hcs
  have h0 : Ns.VanishesOff (tsupport β) (A.epFormsInftyToObj m a) := fun y hy =>
    A.formsInftyRestrict_smul_eq_zero_all (hcs := hcs) hβ hinv ω y hy
  have hst := Ns.stokes (isClosed_tsupport β) hK (A.epFormsInftyToObj m a) h0
  have e : (BundledMPolyfold.of A.X.PObj).formsInftyD m (A.epFormsInftyToObj m a) =
      A.epFormsInftyToObj (m + 1) (A.epFormsInftyD m a) :=
    LinearMap.congr_fun (A.formsInftyD_comp_epFormsInftyToObj m) a
  rw [← hst, e]
  have hc : IsCompact (ManifoldForm.tsupport (formsInftyRestrict (m + 1) hcs
      (A.epFormsInftyToObj (m + 1) (A.epFormsInftyD m a)))) := by
    have hcl : IsClosed ((↑) ⁻¹' tsupport β : Set (C.M i)) :=
      (isClosed_tsupport β).preimage continuous_subtype_val
    have hcp : IsCompact ((↑) ⁻¹' tsupport β : Set (C.M i)) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
      exact hK
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal (fun y hy => ?_) hcl)
    by_contra hyC
    exact hy (A.formsInftyRestrict_d_smul_eq_zero_all rfl hβ hinv ω y hyC)
  exact A.epFormsInftyEval_integ_eq_integral (hcs := hcs) rfl (Nat.succ_pos m) (hS i)
    (C.orient i) (A.epFormsInftyD m a) hc

variable (Φ : A.epFormsInfty (m + 1) →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp Θ)
    (A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ))
  (c : A.Obj → ℝ) (Good : ∀ x, A.X.OrientedTameStructure (m + 1) Θ x → Prop)

/-- **The second and third equalities of the display on p. 451** (proof of Theorem 9.5.18), in
every dimension `m + 1 ≥ 1`: for `Φ` with the local formula of Theorem 9.5.4 or 9.5.5 (weights
`c`), a structure `C` of the class at `x`, an sc-smooth `β` constant on the orbits with
`supp β ⊆ U(x)^*` and `ω ∈ Ωᵐ_{ep,∞}(X)`: `Φ(d(βω))(S) = c(x) ∑ᵢ σᵢ ∫_{∂(Mᵢ,oᵢ)} βω`.  E5's
`stokes_one_structure` without the hypothesis `0 < m`. -/
theorem stokes_one_structure_all (hcpt : A.X.IsCompactBranched Θ)
    (hGS : ∀ x C, Good x C → ∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets)
    (hcov : ∀ x ∈ EpGroupoid.supp Θ, ∃ C, Good x C)
    (hΦ : ∀ (η : A.epFormsInfty (m + 1)) (x : A.Obj)
      (C : A.X.OrientedTameStructure (m + 1) Θ x), Good x C →
      ∀ K : Set (A.X.orbitSupp Θ),
        MeasurableSet[A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        Φ η K = c x * C.sheetSum ((A.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m))
          η (A.X.π ⁻¹' (Subtype.val '' K)))
    {x : A.Obj} (C : A.X.OrientedTameStructure (m + 1) Θ x) (hC : Good x C)
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ))
    (hsupp : tsupport β ⊆ A.X.π ⁻¹' (A.X.π '' C.U)) (ω : A.epFormsInfty m) :
    Φ (A.epFormsInftyD m (A.epFormsInftySmul β m hβ hinv ω)) univ =
      c x * ∑ i, (C.σ i : ℝ) *
        (C.orientedSheet (A.epFormsInftyEval (m + 1)) (hGS x C hC) i).boundaryIntegral
          (A.epFormsInftyToObj m (A.epFormsInftySmul β m hβ hinv ω)) := by
  have h1 := EpGroupoid.measure_univ_eq_of_integ_eq_zero
    ((A.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m)) Φ c Good hcpt hGS hcov hΦ
    (A.epFormsInftyD m (A.epFormsInftySmul β m hβ hinv ω)) C hC (isClosed_tsupport β)
    (EpGroupoid.isSaturated_tsupport hinv) hsupp
    (fun x' C' _ i B _ hd => A.integ_d_smul_eq_zero_all C' i hβ hinv ω hd)
  rw [h1]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact A.integ_d_smul_eq_boundaryIntegral_all hcpt C (hGS x C hC) hβ hinv hsupp ω i

/-- **The term `k = 0` of the proof of Theorem 9.5.18** (p. 451; `U_0^*` does not meet
`supp Θ`), in every dimension `m + 1 ≥ 1`: if `supp β` does not meet `supp Θ`, then
`Φ(d(βω))(S) = 0`.  E5's `stokes_off_support` without the hypothesis `0 < m`. -/
theorem stokes_off_support_all (hcpt : A.X.IsCompactBranched Θ)
    (hcov : ∀ x ∈ EpGroupoid.supp Θ, ∃ C, Good x C)
    (hΦ : ∀ (η : A.epFormsInfty (m + 1)) (x : A.Obj)
      (C : A.X.OrientedTameStructure (m + 1) Θ x), Good x C →
      ∀ K : Set (A.X.orbitSupp Θ),
        MeasurableSet[A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        Φ η K = c x * C.sheetSum ((A.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m))
          η (A.X.π ⁻¹' (Subtype.val '' K)))
    (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ))
    (hd : Disjoint (tsupport β) (EpGroupoid.supp Θ)) (ω : A.epFormsInfty m) :
    Φ (A.epFormsInftyD m (A.epFormsInftySmul β m hβ hinv ω)) univ = 0 :=
  EpGroupoid.measure_eq_zero_of_integ_eq_zero
    ((A.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m)) Φ c Good hcpt hcov hΦ _
    (@MeasurableSet.univ _ (A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ))
    fun _ C _ i _ hB => A.integ_d_smul_eq_zero_all C i hβ hinv ω
      (Set.disjoint_left.2 fun _ hy hyβ => Set.disjoint_left.1 hd hyβ
        (C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i (hB hy).1))

end EP

end Polyfold
