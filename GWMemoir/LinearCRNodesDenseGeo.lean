import GWMemoir.GlueDataNodes

/-!
# Forms read in disc charts and in polar coordinates at a node

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §1.2 (p. 7), §2.4 (p. 51):
the relations between the two readings of a form along a constant map, in a disc chart
(`formDiscRep`: `ξ(∂_d)` in the chart at the centre) and in the polar coordinates of a neck
(`formNeckRep`: `ξ(∂_s σ)`), on an atlas satisfying `GlueCharts`.

* `form_mfderiv`: `ξ(τ_* w)` is `ξ` read in the chart at `c` on `D(chart_c ∘ τ) w`.
* `mfderiv_discPt_dir`: `discPt_* (∂_d) = ε · T_{c → y} e_d`.
* `mfderiv_polarSh`, `mfderiv_polar_add_int`: the shifted polar coordinates have the derivative
  of `σ` at the shifted point; `σ` is periodic in `t` to first order.
* **`formAt_eq_polar`**: in the disc `i`, at a point of the neck `j`, `ξ(∂_d)` is
  `ε_i⁻¹ ξ(σ_*(Dψ e_d))` with `ψ` the change of charts `fDn` to the neck.
* **`polar_eq_formAt`**: in the neck `j`, at a point of the disc `i`, `ξ(σ_* w)` is
  `∑_d (D(chart ∘ σ) w)_d ξ(∂_d)`.
* `antiJ_dt`: for an anti-linear `ξ`, `ξ(∂_t σ) = -J ξ(∂_s σ)`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

section Geo

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m}

/-- The derivative of a map into `S`, read in the chart at `c`. -/
lemma tcc_mfderivN {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {τ : F → X.S} {z : F}
    (hτ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E2) τ z) (c : X.S)
    (hz : τ z ∈ (extChartAt 𝓘(ℝ, E2) c).source) (w : F) :
    tangentCoordChange 𝓘(ℝ, E2) (τ z) c (τ z) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E2) τ z w) =
      fderiv ℝ (fun z => extChartAt 𝓘(ℝ, E2) c (τ z)) z w := by
  have hz' : τ z ∈ (chartAt E2 c).source := by rwa [extChartAt_source] at hz
  have hc : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) (chartAt E2 c) (τ z) :=
    mdifferentiableAt_atlas (ChartedSpace.chart_mem_atlas _) hz'
  have h := mfderiv_comp z hc hτ
  rw [mfderiv_eq_fderiv, mfderiv_chartAt_eq_tangentCoordChange hz'] at h
  exact (congrArg (fun L => L w) h).symm

variable {q : Q}

/-- **`ξ(τ_* w)` read in the chart at `c`.** -/
lemma form_mfderiv (ξ : Form E X) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {τ : F → X.S} {z : F} (hτ : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E2) τ z) (c : X.S)
    (hz : τ z ∈ (extChartAt 𝓘(ℝ, E2) c).source) (w : F) :
    ξ (τ z) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E2) τ z w) =
      formAt (fun _ : X.S => q) c ξ (τ z)
        (fderiv ℝ (fun z => extChartAt 𝓘(ℝ, E2) c (τ z)) z w) := by
  have key : ∀ v : E2, tangentCoordChange 𝓘(ℝ, E2) c (τ z) (τ z)
      (tangentCoordChange 𝓘(ℝ, E2) (τ z) c (τ z) v) = v := fun v => by
    rw [tangentCoordChange_comp ⟨⟨mem_extChartAt_source _, hz⟩, mem_extChartAt_source _⟩,
      tangentCoordChange_self (mem_extChartAt_source _)]
  rw [formAt_of_const (fun _ => rfl), ContinuousLinearMap.comp_apply, ← tcc_mfderivN hτ c hz w]
  exact (congrArg (ξ (τ z)) (key _)).symm

lemma formAt_expand (c y : X.S) (ξ : Form E X) (V : E2) :
    formAt (fun _ : X.S => q) c ξ y V =
      ∑ d : Fin 2, V d • formAt (fun _ : X.S => q) c ξ y (EuclideanSpace.single d 1) := by
  conv_lhs => rw [← single_add_single_eq V, single_eq_smul 0 (V 0), single_eq_smul 1 (V 1)]
  rw [Fin.sum_univ_two, map_add, map_smul, map_smul]

variable (hT : ChartsOnto X)
include hT

/-- `discPt_* (∂_d) = ε · T_{c → y} e_d`. -/
lemma mfderiv_discPt_dir (z : X.S) (ε : ℝ) (p : ℝ × ℝ) (d : Fin 2) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.discPt z ε) p (dir2 d) =
      ε • tangentCoordChange 𝓘(ℝ, E2) z (X.discPt z ε p) (X.discPt z ε p)
        (EuclideanSpace.single d 1) := by
  have hsymm : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2) (extChartAt 𝓘(ℝ, E2) z).symm
      (X.place z ε p) := ((contMDiff_extChartAt_symm hT z) _).mdifferentiableAt (by simp)
  have hpl : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.place z ε) p :=
    (hasFDerivAt_place z ε p).differentiableAt.mdifferentiableAt
  have hchain2 : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.discPt z ε) p =
      (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) (extChartAt 𝓘(ℝ, E2) z).symm (X.place z ε p)).comp
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.place z ε) p) :=
    mfderiv_comp (f := X.place z ε) (g := (extChartAt 𝓘(ℝ, E2) z).symm) p hsymm hpl
  rw [hchain2]
  erw [ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv, fderiv_place_dir,
    ContinuousLinearMap.map_smul, mfderiv_extChartAt_symm_eq hT]
  rfl

/-- `ξ(∂_d)` in the disc chart, through the derivative of `discPt`. -/
lemma formAt_single_eq (z : X.S) {ε : ℝ} (hε : ε ≠ 0) (p : ℝ × ℝ) (ξ : Form E X) (d : Fin 2) :
    formAt (fun _ : X.S => q) z ξ (X.discPt z ε p) (EuclideanSpace.single d 1) =
      ε⁻¹ • ξ (X.discPt z ε p) (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.discPt z ε) p (dir2 d)) := by
  rw [mfderiv_discPt_dir hT, map_smul, inv_smul_smul₀ hε, formAt_of_const (fun _ => rfl)]
  rfl

end Geo

/-! ## The polar coordinates of the necks -/

section Polar

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m}

lemma mfderiv_comp_add {f : ℝ × ℝ → X.S} {y c : ℝ × ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) f (y + c)) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (fun y => f (y + c)) y =
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) f (y + c) := by
  have ht : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun y => y + c) y :=
    (differentiableAt_id.add_const c).mdifferentiableAt
  have h := mfderiv_comp (f := fun y => y + c) (g := f) y hf ht
  rw [mfderiv_eq_fderiv, fderiv_add_const, fderiv_fun_id] at h
  exact h.trans (ContinuousLinearMap.comp_id _)

variable {q : Q} {A : SectionAtlas (E := E) X (fun _ => q)} (H : GlueCharts A)
include H

lemma mdifferentiableAt_polar (j : Fin A.nn) (x : ℝ × ℝ) :
    MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x := by
  have h := (contMDiff_polarSh H j 0 0 x).mdifferentiableAt (by simp)
  have e : polarSh A j 0 0 = X.polar (A.hol j) := by funext y; simp [polarSh]
  rwa [e] at h

lemma mfderiv_polarSh (j : Fin A.nn) (α β : ℝ) (y : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (polarSh A j α β) y =
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) (y.1 + α, y.2 + β) := by
  have e : polarSh A j α β = fun y => X.polar (A.hol j) (y + (α, β)) := rfl
  rw [e, mfderiv_comp_add (mdifferentiableAt_polar H j _)]
  rfl

lemma mfderiv_polar_add_int (j : Fin A.nn) (s t : ℝ) (n : ℤ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) (s, t + n) =
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) (s, t) := by
  have e : (fun y => X.polar (A.hol j) (y + (0, (n : ℝ)))) = X.polar (A.hol j) := by
    funext y
    rw [show y + (0, (n : ℝ)) = (y.1, y.2 + n) by ext <;> simp, polar_add_int]
  have h := mfderiv_comp_add (f := X.polar (A.hol j)) (y := (s, t)) (c := (0, (n : ℝ)))
    (mdifferentiableAt_polar H j _)
  rw [e] at h
  rw [h]
  congr 1
  ext <;> simp

/-- For a form anti-linear at `σ(x)`, `ξ(∂_t σ) = -J ξ(∂_s σ)`. -/
lemma antiJ_dt (J : AlmostComplexStructure E Q) (j : Fin A.nn) (x : ℝ × ℝ) {ξ : Form E X}
    (hξ : ξ (X.polar (A.hol j) x) ∈ X.antiLinearForms J q (X.polar (A.hol j) x)) :
    ξ (X.polar (A.hol j) x) (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x (0, 1)) =
      -J.J q (ξ (X.polar (A.hol j) x)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x (1, 0))) := by
  have hp : expPolar x ∈ (A.hol j).target := by rw [H.target j]; trivial
  rw [(polar_deriv (A.isHol j) hp ((H.smooth_symm j _).mdifferentiableAt (by simp))).2]
  have h1 := (NodalSurface.mem_antiLinearForms J X).1 hξ
    (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j)) x (1, 0))
  rw [h1, neg_neg]

variable (hT : ChartsOnto X)
include hT

/-- **`ξ(∂_d)` in the disc `i` at a point of the neck `j`**: `ε_i⁻¹ ξ(σ_*(Dψ e_d))`, with `ψ`
the change of charts `fDn` from the disc to the neck (rotated by `θ a`). -/
theorem formAt_eq_polar {i : Fin A.nd} {j : Fin A.nn} (a : Fin 2) {p : ℝ × ℝ}
    (hp : p ∈ UDn A i j a) (ξ : Form E X) (d : Fin 2) :
    formAt (fun _ : X.S => q) (A.center i) ξ (X.discPt (A.center i) (A.ε i) p)
        (EuclideanSpace.single d 1) =
      (A.ε i)⁻¹ • ξ (X.discPt (A.center i) (A.ε i) p)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar (A.hol j))
          ((fDn A i j a p).1 + A.s0 j, (fDn A i j a p).2 + -thetaN a)
          (fderiv ℝ (fDn A i j a) p (dir2 d))) := by
  rw [formAt_single_eq hT _ (A.ε_pos i).ne']
  congr 2
  have hev : polarSh A j (A.s0 j) (-thetaN a) ∘ fDn A i j a =ᶠ[𝓝 p]
      X.discPt (A.center i) (A.ε i) := by
    filter_upwards [(isOpen_UDn H hT i j a).mem_nhds hp] with p' hp'
    have h2 : cSgn a * wN A i j p' ∈ Complex.slitPlane := hp'.2
    exact polarSh_fDn H a hp'.1 (right_ne_zero_of_mul (Complex.slitPlane_ne_zero h2))
  rw [← hev.mfderiv_eq]
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fDn A i j a) p :=
    ((contDiffAt_fDn H hT a hp).differentiableAt (by simp)).mdifferentiableAt
  have hg : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (polarSh A j (A.s0 j) (-thetaN a))
      (fDn A i j a p) := (contMDiff_polarSh H j _ _ _).mdifferentiableAt (by simp)
  rw [mfderiv_comp p hg hf, mfderiv_eq_fderiv, mfderiv_polarSh H]
  rfl

/-- **`ξ(σ_* w)` at a point of the disc `i`**: `∑_d (D(chart_i ∘ σ) w)_d ξ(∂_d)`. -/
theorem polar_eq_formAt (i : Fin A.nd) (j : Fin A.nn) (α β : ℝ) {z : ℝ × ℝ}
    (hz : polarSh A j α β z ∈ (extChartAt 𝓘(ℝ, E2) (A.center i)).source) (ξ : Form E X)
    (w : ℝ × ℝ) :
    ξ (polarSh A j α β z) (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (polarSh A j α β) z w) =
      ∑ d : Fin 2, (fderiv ℝ (fun z => extChartAt 𝓘(ℝ, E2) (A.center i) (polarSh A j α β z))
        z w) d • formAt (fun _ : X.S => q) (A.center i) ξ (polarSh A j α β z)
          (EuclideanSpace.single d 1) := by
  rw [form_mfderiv (q := q) ξ ((contMDiff_polarSh H j α β z).mdifferentiableAt (by simp)) _ hz w,
    formAt_expand]

end Polar

end GWMemoir
