import Polyfold.Chapter6.ChartTransfer
import Polyfold.Chapter5.RestrictOpen

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.2, p. 208
(**Definition 6.2.1**: the linearizations `Lin(f, x)`, read in a chart), in the form used on
p. 703 for Corollary 15.4.4.

# A chart point and its restriction to an open set

## What is formalized

For a chart point `p` of a strong bundle at `x` (a strong bundle chart `c` around `x` and the
level-`1` point over `φ(x)`) and an open `V ∋ x`:

* `ChartPoint.restr`: the chart point of the chart `c` restricted to `dom φ ∩ V`
  (`StrongBundleChart.restrictInter`), with the same level-`1` point.
* `ChartPoint.restr_T`: the two chart points have the same `T_zO`.
* `ChartPoint.coe_transferT_restr`, `ChartPoint.coe_transferT_to_restr`,
  `ChartPoint.coe_transferK_restr`: the identifications `T_zO ≅ T_zO`, `K_z ≅ K_z` of the two
  chart points (`ChartPoint.transferT`, `ChartPoint.transferK`) are the identity of the model
  spaces.

So an operator read in the restricted chart point, where a section given on `V` only can be
linearized, is the same operator read in `p`.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

open StrongRetr

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) {V : Set X} (hV : IsOpen V) (hx : x ∈ V)

/-- **The chart point of the chart of `p` restricted to `dom φ ∩ V`**, with the same level-`1`
point. -/
def restr : ChartPoint B x where
  c := p.c.restrictInter hV
  isChart := p.isChart.restrictInter hV
  mem_source := ⟨p.mem_source, hx⟩
  z := p.z
  toBase_z := p.toBase_z

theorem restr_source_subset : (p.restr hV hx).c.φ.source ⊆ V := inter_subset_right

theorem restr_source_subset_source : (p.restr hV hx).c.φ.source ⊆ p.c.φ.source :=
  inter_subset_left

theorem restr_U_subset : (p.restr hV hx).c.U ⊆ p.c.U := p.c.restrictInter_U_subset hV

/-- The derivative of the retraction at `z` is the same for the restricted chart. -/
theorem restr_scDeriv_r :
    scDeriv (p.restr hV hx).c.U (r p.c.R) p.z = scDeriv p.c.U (r p.c.R) p.z := by
  have hr1 : IsSc1 p.c.U (r p.c.R) := (r_isScSmooth p.c.relOpen p.c.isRetraction).isSc1
  have hr2 : IsSc1 (p.restr hV hx).c.U (r p.c.R) :=
    (r_isScSmooth (p.restr hV hx).c.relOpen (p.restr hV hx).c.isRetraction).isSc1
  exact scDeriv_eq_of_eqOn_relOpen (p.restr hV hx).c.relOpen hr2 hr1 subset_rfl
    (p.restr_U_subset hV hx) (fun _ _ => rfl) (p.restr hV hx).mem_U

/-- **`T_zO` is the same for the restricted chart.** -/
theorem restr_T : (p.restr hV hx).T = p.T :=
  congrArg (fun L : p.c.φ.model.E 0 →L[ℝ] p.c.φ.model.E 0 => rangeS L) (p.restr_scDeriv_r hV hx)

/-- **`D(φ ∘ φ⁻¹ ∘ r)(z) = Dr(z)`** from the restricted chart to the chart. -/
theorem restr_baseDeriv (v : p.c.φ.model.E 0) :
    (p.restr hV hx).baseDeriv p v = scDeriv p.c.U (r p.c.R) p.z v := by
  have hr1 : IsSc1 p.c.U (r p.c.R) := (r_isScSmooth p.c.relOpen p.c.isRetraction).isSc1
  refine congrArg (fun L : p.c.φ.model.E 0 →L[ℝ] p.c.φ.model.E 0 => L v)
    (scDeriv_eq_of_eqOn_relOpen ((p.restr hV hx).baseRet p).relOpen
      ((p.restr hV hx).isSc1_transition p) hr1 subset_rfl
      (((p.restr hV hx).baseRet_U_subset p).trans (p.restr_U_subset hV hx)) (fun u hu => ?_)
      ((p.restr hV hx).z_mem_baseRet p))
  have hex := (p.restr hV hx).exists_eq_of_mem_baseRet p hu
  obtain ⟨y, hy, hy', hyu⟩ := hex
  exact (congrArg ((p.restr hV hx).c.φ.transition p.c.φ) hyu).trans
    (((p.restr hV hx).c.φ.transition_apply p.c.φ hy).trans hyu.symm)

/-- **`D(φ ∘ φ⁻¹ ∘ r)(z) = Dr(z)`** from the chart to the restricted chart. -/
theorem baseDeriv_restr (v : p.c.φ.model.E 0) :
    p.baseDeriv (p.restr hV hx) v = scDeriv p.c.U (r p.c.R) p.z v := by
  have hr1 : IsSc1 p.c.U (r p.c.R) := (r_isScSmooth p.c.relOpen p.c.isRetraction).isSc1
  refine congrArg (fun L : p.c.φ.model.E 0 →L[ℝ] p.c.φ.model.E 0 => L v)
    (scDeriv_eq_of_eqOn_relOpen (p.baseRet (p.restr hV hx)).relOpen
      (p.isSc1_transition (p.restr hV hx)) hr1 subset_rfl
      (p.baseRet_U_subset (p.restr hV hx)) (fun u hu => ?_)
      (p.z_mem_baseRet (p.restr hV hx)))
  have hex := p.exists_eq_of_mem_baseRet (p.restr hV hx) hu
  obtain ⟨y, hy, hy', hyu⟩ := hex
  change p.c.φ.transition (p.restr hV hx).c.φ (r p.c.R u) = r p.c.R u
  rw [hyu, p.c.φ.transition_apply (p.restr hV hx).c.φ hy]
  rfl

/-- `Dr(z)` is the identity on `T_zO`. -/
theorem scDeriv_r_of_mem_T {v : p.c.φ.model.E 0} (hv : v ∈ p.T) :
    scDeriv p.c.U (r p.c.R) p.z v = v := by
  obtain ⟨h, rfl⟩ := hv
  exact scDeriv_r_idem_at p.c.relOpen p.c.isRetraction p.mem_O h

/-- **`T_zO` of the restricted chart point and of `p` are identified by the identity.** -/
theorem coe_transferT_restr (v : ↥(p.restr hV hx).T) :
    (((p.restr hV hx).transferT p v : ↥p.T).1 : p.c.φ.model.E 0) = v.1 :=
  (p.restr_baseDeriv hV hx v.1).trans
    (p.scDeriv_r_of_mem_T ((congrArg (v.1 ∈ ·) (p.restr_T hV hx)).mp v.2))

/-- **`T_zO` of `p` and of the restricted chart point are identified by the identity.** -/
theorem coe_transferT_to_restr (v : ↥p.T) :
    ((p.transferT (p.restr hV hx) v : ↥(p.restr hV hx).T).1 : p.c.φ.model.E 0) = v.1 :=
  (p.baseDeriv_restr hV hx v.1).trans (p.scDeriv_r_of_mem_T v.2)

/-- **`K_z` of the restricted chart point and of `p` are identified by the identity.** -/
theorem coe_transferK_restr (k : ↥(p.restr hV hx).K) :
    (((p.restr hV hx).transferK p k : ↥p.K).1 : p.c.F 0) = k.1 := by
  have hK := (p.restr hV hx).mem_K_of_mem k.2
  have hK' : (p.c.φ.model.E.toBase 1 p.z, (k.1 : p.c.F 0)) ∈ p.c.K :=
    ((p.c.mem_restrict_K_iff _ _).1 hK).1
  refine ((p.restr hV hx).fiberMap_apply_of_mem p k.2).trans ?_
  exact congrArg Prod.snd (p.c.apply_symm hK')

end ChartPoint

end Polyfold
