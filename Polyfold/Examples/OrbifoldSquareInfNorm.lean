import Polyfold.Examples.OrbifoldSquareInfBundle
import Polyfold.Examples.OrbifoldSquarePerturbation
import Polyfold.Chapter15.ProductAuxNorm
import Polyfold.Chapter15.ProductMultisection

/-!
# The orbifold `(ℂ × H)/ℤ₅`: the auxiliary norm and the control of compactness

For the infinite-dimensional version of the worked example for Hofer–Wysocki–Zehnder, *Polyfold
and Fredholm Theory* (Springer 2021), Theorem 16.6.6, 2021 p. 739, with Definitions 5.1.1, 8.3.5
and 15.3.1.

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquareInf`)

* `NH`: the auxiliary norm of `H ◁ H`: `N(e, h) = |h|_1` for `h ∈ H_1`; `isAuxNorm_NH_bundle`
  (Definition 5.1.1), `isAuxNorm_NH` (Definition 8.3.5).
* `controlsCompactness_idSec`: `(N, H)` controls the compactness of `e ↦ (e, e)`
  (Definition 15.3.1): `{e | |e|_1 ≤ 1}` has compact closure in `H_0`, the inclusion
  `H_1 → H_0` being compact.
* `Ninf`, `isAuxNorm_Ninf`, **`controlsCompactness_sqInf_univ`**: the product norm
  `max(|w|, |h|_1)` controls the compactness of `(z, e) ↦ ((z, z²), (e, e))`.
* `normW_Ninf_zero`: `N((z, w), (e, 0)) = |w|`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold.Examples.OrbifoldSquareInf

open TrivialBundle EpGroupoid.Examples StrongBundle WeightedEllTwo OrbifoldSquare SBLocalization

/-- The one chart of `H ◁ H`. -/
abbrev chH : StrongBundleChart PH (LocalBundle.proj (E := H) (U := (univ : Set (H 0))) (F := H)) :=
  LocalBundle.chart relOpen_H h0

theorem chH_mem : chH ∈ BH.atlas.charts := mem_singleton _

/-- The lift of the fibre part to `H_1`. -/
def lift1 (v : H 0) : H 1 := invFun (H.toBase 1) v

theorem lift1_toBase (a : H 1) : lift1 (H.toBase 1 a) = a :=
  leftInverse_invFun (H.toBase_injective 1) a

theorem toBase_lift1 {v : H 0} (hv : v ∈ range (H.toBase 1)) : H.toBase 1 (lift1 v) = v :=
  invFun_eq hv

theorem mem_oneSet_BH {y : HObj × H 0} : y ∈ BH.oneSet ↔ y.2 ∈ range (H.toBase 1) :=
  BH.mem_oneSet_iff chH_mem (mem_univ y)

theorem lift1_add {v w : H 0} (hv : v ∈ range (H.toBase 1)) (hw : w ∈ range (H.toBase 1)) :
    lift1 (v + w) = lift1 v + lift1 w := by
  obtain ⟨a, rfl⟩ := hv
  obtain ⟨b, rfl⟩ := hw
  rw [← map_add, lift1_toBase, lift1_toBase, lift1_toBase]

theorem lift1_sub {v w : H 0} (hv : v ∈ range (H.toBase 1)) (hw : w ∈ range (H.toBase 1)) :
    lift1 (v - w) = lift1 v - lift1 w := by
  obtain ⟨a, rfl⟩ := hv
  obtain ⟨b, rfl⟩ := hw
  rw [← map_sub, lift1_toBase, lift1_toBase, lift1_toBase]

theorem lift1_smul (t : ℝ) {v : H 0} (hv : v ∈ range (H.toBase 1)) :
    lift1 (t • v) = t • lift1 v := by
  obtain ⟨a, rfl⟩ := hv
  rw [← map_smul, lift1_toBase, lift1_toBase]

/-- **The auxiliary norm of `H ◁ H`**: `N(e, h) = |h|_1`. -/
def NH : BH.One → ℝ := fun w => ‖lift1 (BH.oneVal w).2‖

theorem NH_oneMk (y : HObj × H 0) (hy : y ∈ BH.oneSet) : NH (BH.oneMk y hy) = ‖lift1 y.2‖ := rfl

theorem continuous_liftOne_BH : Continuous fun y : BH.One => chH.liftOne (BH.oneVal y) := by
  have h := BH.continuousOn_liftOne chH_mem
  have e : {y : BH.One | BH.oneVal y ∈ chH.toPartialEquiv.source} = univ :=
    eq_univ_of_forall fun y => mem_univ _
  rw [e] at h
  exact continuousOn_univ.1 h

/-- The fibre of `H ◁ H` over `x`. -/
abbrev Fib (x : HObj) : Type :=
  ↥(LocalBundle.proj (E := H) (U := (univ : Set (H 0))) (F := H) ⁻¹' {x})

/-- The fibre part of a point of the fibre over `x`. -/
def fpart {x : HObj} (v : Fib x) : H 0 := (v : HObj × H 0).2

theorem fpart_add {x : HObj} (v w : Fib x) : fpart (v + w) = fpart v + fpart w := rfl

theorem fpart_sub {x : HObj} (v w : Fib x) : fpart (v - w) = fpart v - fpart w :=
  ((LocalBundle.fibEquiv (F := H) x).linearEquiv ℝ).map_sub v w

theorem fpart_smul {x : HObj} (t : ℝ) (v : Fib x) : fpart (t • v) = t • fpart v := rfl

theorem fpart_mem {x : HObj} (v : BH.oneFiber x) : fpart (v : Fib x) ∈ range (H.toBase 1) :=
  mem_oneSet_BH.1 v.2

theorem NH_toOne {x : HObj} (v : BH.oneFiber x) :
    NH (BH.toOne v) = ‖lift1 (fpart (v : Fib x))‖ := rfl

theorem NH_toOne_add {x : HObj} (v w : BH.oneFiber x) :
    NH (BH.toOne (v + w)) = ‖lift1 (fpart (v : Fib x)) + lift1 (fpart (w : Fib x))‖ := by
  rw [NH_toOne, Submodule.coe_add, fpart_add, lift1_add (fpart_mem v) (fpart_mem w)]

theorem NH_toOne_sub {x : HObj} (v w : BH.oneFiber x) :
    NH (BH.toOne (v - w)) = ‖lift1 (fpart (v : Fib x)) - lift1 (fpart (w : Fib x))‖ := by
  rw [NH_toOne, Submodule.coe_sub, fpart_sub, lift1_sub (fpart_mem v) (fpart_mem w)]

theorem NH_toOne_smul {x : HObj} (t : ℝ) (v : BH.oneFiber x) :
    NH (BH.toOne (t • v)) = |t| * NH (BH.toOne v) := by
  rw [NH_toOne, NH_toOne, Submodule.coe_smul, fpart_smul, lift1_smul t (fpart_mem v), norm_smul,
    Real.norm_eq_abs]

theorem isCompleteFiberNorm_NH (x : HObj) : BH.IsCompleteFiberNorm NH x where
  eq_zero := fun v hv => by
    rw [NH_toOne, norm_eq_zero] at hv
    have h0 : fpart (v : Fib x) = 0 := by
      rw [← toBase_lift1 (fpart_mem v), hv, map_zero]
    refine Subtype.ext ((LocalBundle.fibEquiv (F := H) x).injective ?_)
    exact h0
  smul := NH_toOne_smul
  add_le := fun v w => by
    rw [NH_toOne_add, NH_toOne, NH_toOne]
    exact norm_add_le _ _
  complete := fun u hu => by
    set a : ℕ → H 1 := fun j => lift1 (fpart (u j : Fib x)) with ha
    have hc : CauchySeq a := by
      refine Metric.cauchySeq_iff.2 fun ε hε => ?_
      obtain ⟨N₀, hN₀⟩ := hu ε hε
      exact ⟨N₀, fun i hi j hj => by
        rw [dist_eq_norm, ← NH_toOne_sub]; exact hN₀ i hi j hj⟩
    obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hc
    let v₀ : Fib x := ⟨(x, H.toBase 1 b), rfl⟩
    have hv₀ : v₀ ∈ BH.oneFiber x := mem_oneSet_BH.2 ⟨b, rfl⟩
    refine ⟨⟨v₀, hv₀⟩, ?_⟩
    have e : ∀ j, NH (BH.toOne (u j - ⟨v₀, hv₀⟩)) = ‖a j - b‖ := fun j => by
      rw [NH_toOne_sub]
      change ‖a j - lift1 (H.toBase 1 b)‖ = _
      rw [lift1_toBase]
    simp only [e]
    exact tendsto_iff_norm_sub_tendsto_zero.1 hb

/-- **`N` is an auxiliary norm of `H ◁ H`** (Definition 5.1.1). -/
theorem isAuxNorm_NH_bundle : BH.IsAuxNorm NH where
  continuous := continuous_norm.comp (continuous_snd.comp continuous_liftOne_BH)
  fiber := isCompleteFiberNorm_NH
  tendsto_zeroOne := fun w x hP hN => by
    refine TopologicalSpace.tendsto_nhds_generateFrom_iff.2 ?_
    rintro s ⟨c, hc, W, hW, rfl⟩ ⟨-, hz⟩
    obtain rfl : c = chH := mem_singleton_iff.1 hc
    have hz' : (((x : H 0), (0 : H 1)) : H 0 × H 1) ∈ W := by
      have h1 : chH.liftOne (BH.oneVal (BH.zeroOne x)) = ((x : H 0), lift1 (0 : H 0)) := rfl
      have h2 : lift1 (0 : H 0) = 0 := by
        have := lift1_toBase (0 : H 1)
        rwa [map_zero] at this
      rw [← h2, ← h1]
      exact hz
    have h2 : Tendsto (fun j => lift1 (BH.oneVal (w j)).2) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.2 hN
    have h3 : Tendsto (fun j => (((BH.oneVal (w j)).1 : HObj) : H 0)) atTop (𝓝 (x : H 0)) :=
      (continuous_subtype_val.tendsto x).comp hP
    have h1 := h3.prodMk_nhds h2
    filter_upwards [h1 (hW.mem_nhds hz')] with j hj
    exact ⟨mem_univ _, hj⟩

/-- **`N` is an auxiliary norm of `H ◁ H` over the trivial ep-groupoid** (Definition 8.3.5). -/
theorem isAuxNorm_NH : AH.E.IsAuxNorm NH :=
  ⟨isAuxNorm_NH_bundle, fun h k φ hk e => by
    have e' : BH.oneVal h = BH.oneVal k := e
    rw [BH.oneVal_injective e']⟩

/-- **`(N, H)` controls the compactness of `e ↦ (e, e)`** (Definition 15.3.1): `N(e, e) ≤ 1`
means `|e|_1 ≤ 1`, and the inclusion `H_1 → H_0` is compact. -/
theorem controlsCompactness_idSec : ControlsCompactness AH idSec NH univ := by
  refine ⟨isAuxNorm_NH, isOpen_univ, GroupoidStr.isSaturated_univ _, subset_univ _, ?_⟩
  have hK0 : IsCompact (closure (H.incl 0 '' Metric.closedBall (0 : H 1) 1)) :=
    (H.incl_isCompactOperator 0).isCompact_closure_image_closedBall 1
  let K : Set AH.Obj := (fun e : H 0 => (hpt e : AH.Obj)) ''
    closure (H.incl 0 '' Metric.closedBall (0 : H 1) 1)
  have hK : IsCompact K := hK0.image (continuous_id.subtype_mk _)
  have hsub : {x ∈ (univ : Set AH.Obj) | AH.B.AuxLe NH (idSec x) 1} ⊆ K := by
    rintro (x : HObj) ⟨-, hw, hle⟩
    have hle' : ‖lift1 (x : H 0)‖ ≤ 1 := hle
    have hx : (x : H 0) ∈ range (H.toBase 1) := mem_oneSet_BH.1 hw
    refine ⟨(x : H 0), subset_closure ⟨lift1 (x : H 0), ?_, toBase_lift1 hx⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hle'
  exact (hK.image AH.X.continuous_π).closure_of_subset (image_mono hsub)

/-! ### The product norm -/

/-- **The auxiliary norm of `(ℂ × ℂ) × (H ◁ H)`**: `N((z, w), (e, h)) = max(|w|, |h|_1)`. -/
def Ninf : Ainf.B.One → ℝ := A5.B.prodAuxNorm AH.B N5 NH

/-- **`Ninf` is an auxiliary norm** (Definition 8.3.5). -/
theorem isAuxNorm_Ninf : Ainf.E.IsAuxNorm Ninf :=
  EpStrongBundle.isAuxNorm_prodAuxNorm isAuxNorm_N5 isAuxNorm_NH

/-- **`(Ninf, ℂ × H)` controls the compactness of `(z, e) ↦ ((z, z²), (e, e))`**
(Definition 15.3.1). -/
theorem controlsCompactness_sqInf_univ : ControlsCompactness Ainf sqInf Ninf univ := by
  have h := ControlsCompactness.prod controlsCompactness_sqSection_univ controlsCompactness_idSec
  rw [univ_prod_univ] at h
  exact h

/-- A point `(e, 0)` of `H ◁ H` lies in the `(0, 1)`-level. -/
theorem zero_mem_oneSet_BH (x : HObj) : ((x, (0 : H 0)) : HObj × H 0) ∈ BH.oneSet :=
  mem_oneSet_BH.2 ⟨0, map_zero _⟩

/-- `N(e, 0) = 0`. -/
theorem normW_NH_zero (x : HObj) : normW (A := AH) NH ((x, (0 : H 0)) : AH.W) = 0 := by
  rw [normW_of_mem (A := AH) NH (zero_mem_oneSet_BH x)]
  change ‖lift1 (0 : H 0)‖ = 0
  have := lift1_toBase (0 : H 1)
  rw [map_zero] at this
  rw [this, norm_zero]

/-- **`N((z, w), (e, 0)) = |w|`.** -/
theorem normW_Ninf_zero (p : A5.W) (x : HObj) :
    normW (A := Ainf) Ninf ((p, ((x, (0 : H 0)) : AH.W)) : Ainf.W) = ‖cE p.2‖ := by
  have hp : p ∈ A5.B.oneSet := by
    have h : (bundle 2 2).oneSet = univ := oneSet_eq
    exact h ▸ mem_univ p
  have h := normW_prodAuxNorm (A := A5) (A' := AH) N5 NH
    (w := ((p, ((x, (0 : H 0)) : AH.W)) : Ainf.W)) hp (zero_mem_oneSet_BH x)
  have h1 : normW (A := A5) N5 p = ‖cE p.2‖ :=
    (normW_of_mem (A := A5) N5 hp).trans (N5_oneMk p hp)
  have h2 := normW_NH_zero x
  change normW (A := Ainf) (A5.B.prodAuxNorm AH.B N5 NH) _ = _
  rw [h, h1]
  change max ‖cE p.2‖ (normW (A := AH) NH ((x, (0 : H 0)) : AH.W)) = _
  rw [h2]
  exact max_eq_left (norm_nonneg _)

end Polyfold.Examples.OrbifoldSquareInf
