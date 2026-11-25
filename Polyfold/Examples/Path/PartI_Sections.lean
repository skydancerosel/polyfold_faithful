import Polyfold.Examples.Path.PartI_StrongBundle
import Polyfold.Chapter3.LinearizationCharts
import Polyfold.Chapter3.BookGerms

/-!
# Fillers, linearizations, parametrized perturbations, tame charts: examples
(rows V3.7, V3.78, V3.91, V3.103)

* `isFillingGerm_id_sq`: for the identity strong bundle retraction of `ℝ ◁ ℝ`, `g(x) = x²` fills
  itself.
* `linAt_id_Rc`: for the identity retraction of `ℝ ◁ ℝ`, the linearization of a `C¹` principal
  part `k` at `z` is `h ↦ k'(z) h`; `linAt_sq_sub_one`: at the zero `1` of `k(x) = x² − 1` it is
  `h ↦ 2h`; `linAt_const_one_exp`: away from zeros the linearization depends on the chart.
* `isScFredholmSection_param_idSec`: Theorem 3.1.21 for `e ↦ (e, e)` on `H ◁ H` and the constant
  sc⁺-section `e ↦ (e, b)`.
* `isTameChart_chH`: the chart `(e, h) ↦ (e, h)` of `H ◁ H` is tame.
-/

open Set Function Topology

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Path

open StrongRetr

/-! ### Fillers -/

theorem isStrongBundleRetraction_id_Rc :
    IsStrongBundleRetraction (E := Rc) (F := Rc) univ id :=
  isStrongBundleRetraction_id_of_relOpen relOpen_univ_Rc

/-- Row V3.7, Definition 3.1.4 (p. 91): for the identity strong bundle retraction of `ℝ ◁ ℝ`, the
principal part `g(x) = x²` is filled by itself. -/
theorem isFillingGerm_id_sq :
    IsFillingGerm relOpen_univ_Rc isStrongBundleRetraction_id_Rc (mem_univ 0)
      (fun x : ℝ => x ^ 2) (fun x : ℝ => x ^ 2) :=
  (isFilling2021_of_R_eq_self relOpen_univ_Rc isStrongBundleRetraction_id_Rc (fun _ => rfl)
    (mem_univ 0) ((isScSmooth_iff_contDiffOn_const relOpen_univ_Rc.isScDomain _).2
      (contDiff_id.pow 2).contDiffOn)).isFillingGerm

/-! ### The linearization -/

/-- Row V3.78 (p. 136): for the identity strong bundle retraction of `ℝ ◁ ℝ`, the linearization
at `z` of a `C¹` principal part `k` is `h ↦ k'(z) h`. -/
theorem linAt_id_Rc {k : ℝ → ℝ} (hk : ContDiff ℝ 1 k) (z : ℝ)
    (x : ↥(rangeS (scDeriv (E := Rc) (F := Rc) univ (r (E := Rc) (F := Rc) id) z))) :
    linAt (E := Rc) (F := Rc) univ id k z x = deriv k z * (x : ℝ) := by
  rw [linAt_apply]
  change scDeriv (E := Rc) (F := Rc) univ k z x = _
  rw [scDeriv_const_eq_fderiv hk, ← fderiv_apply_one_eq_deriv, mul_comm]
  change _ = (x : ℝ) • (fderiv ℝ k z 1)
  rw [← map_smul, smul_eq_mul, mul_one]

/-- Row V3.78, an example at a zero: for `k(x) = x² − 1`, at the zero `z = 1` the linearization
is `h ↦ 2h`. -/
theorem linAt_sq_sub_one
    (x : ↥(rangeS (scDeriv (E := Rc) (F := Rc) univ (r (E := Rc) (F := Rc) id) 1))) :
    linAt (E := Rc) (F := Rc) univ id (fun u : ℝ => u ^ 2 - 1) 1 x = 2 * (x : ℝ) := by
  rw [linAt_id_Rc (k := fun u : ℝ => u ^ 2 - 1) ((contDiff_id.pow 2).sub contDiff_const)]
  simp

/-- Row V3.78, away from zeros: the section `x ↦ (x, 1)` of `ℝ ◁ ℝ` has the principal part `1` in
the chart `(x, h) ↦ (x, h)` and `eˣ` in the chart `(x, h) ↦ (x, eˣ h)`; at `z`, where the section
does not vanish, the first linearization is `0` and the second `h ↦ e^z h`. -/
theorem linAt_const_one_exp (z : ℝ)
    (x : ↥(rangeS (scDeriv (E := Rc) (F := Rc) univ (r (E := Rc) (F := Rc) id) z))) :
    linAt (E := Rc) (F := Rc) univ id (fun _ : ℝ => (1 : ℝ)) z x = 0 ∧
      linAt (E := Rc) (F := Rc) univ id Real.exp z x = Real.exp z * (x : ℝ) := by
  rw [linAt_id_Rc contDiff_const, linAt_id_Rc Real.contDiff_exp, Real.deriv_exp]
  simp

/-! ### Theorem 3.1.21 and tame charts on `H ◁ H` -/

section BH

open OrbifoldSquareInf WeightedEllTwo StrongBundle

/-- Row V3.91, Theorem 3.1.21 (p. 100): for the sc-Fredholm section `e ↦ (e, e)` of `H ◁ H → H`
and the sc⁺-section `e ↦ (e, b)` with `b` smooth, `F(r, e) = (e, e + r b)` is an sc-Fredholm
section of the pull-back bundle over `ℝ × H`. -/
theorem isScFredholmSection_param_idSec {b : H 0} (hb : b ∈ H.smooth) :
    (BH.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PH)).IsScFredholmSection
      (paramSection idSec isScFredholmSectionTame_idSec.isScSmooth.1 (fun _ => constSec b)
        fun _ => (isScPlusSection_constSec hb).1) :=
  theorem_3_1_21' isScFredholmSectionTame_idSec.toIsScFredholmSection
    fun _ => isScPlusSection_constSec hb

/-- Row V3.103, a tame chart (§3.6, p. 135): the chart `(e, h) ↦ (e, h)` of `H ◁ H → H`, whose
base retraction is the identity, is a tame strong bundle chart. -/
theorem isTameChart_chH : BH.IsTameChart chH :=
  isTameChart_of_eqOn_id isChart_chH fun _ _ => rfl

end BH

end Polyfold.Examples.Path
