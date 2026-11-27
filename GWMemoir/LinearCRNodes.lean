import GWMemoir.LinearCRSphere
import GWMemoir.NodalPair
import GWMemoir.SectionAtlasNodes

/-!
# The linearized Cauchy–Riemann operator at a constant map from two spheres joined at a node

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Proposition 4.23,
p. 118, level `0`, `a = 0`): at the constant map `u ≡ q` from `twoSpheres` (two spheres joined at
the nodal pair `{e₂, e₂}`, `GWMemoir.NodalPair`), the kernel of `D η = ½ (dη + J(q) ∘ dη ∘ j)` on
the sections of class `(3, δ₀)` with matching values at the node is a copy of `E = T_qQ`.

This file holds the parts of the plan which are about sections and do not depend on the
neck rows of the operator:

* **`eq_const_of_holo_off_pt2`**: a continuous `η : S² → E`, differentiable with
  `dη ∘ j = J₀ ∘ dη` off `e₂`, is constant (the proof of `eq_const_of_holo_sphere3` uses
  holomorphy only on the image of `σ₁ = holChart 1`, which misses `e₂`);
* **`eq_const_of_holo_twoSpheres`**: on `twoSpheres`, a continuous section, holomorphic off the
  nodal points and with matching values at the nodal pair, is constant: on each sphere it is
  constant by the previous statement, and the matching identifies the two constants;
* polar coordinates `σ(s, t) = φ⁻¹(e^{-2π(s+it)})` at a nodal point with a holomorphic chart
  `φ`: a section whose expression `v⁺ = η ∘ σ` is differentiable at `p` is differentiable at
  `σ(p)` (`mdifferentiableAt_of_polar`), and if moreover `∂_t v⁺ = J₀ ∂_s v⁺` then `η` is
  holomorphic there (`holo_of_polar`);
* **`neck_C1`**: for a section of class `(3, δ₀)` the expression `v⁺` is `C¹` on `s > s₀`
  (`H³ ⊂ C¹` on the strip, applied to the neck block and to its rotation by `½` in `t`);
* **`formInPolar_projF`**: in polar coordinates the form `½(dη + J₀ ∘ dη ∘ j)` is
  `½(∂_s v⁺ + J₀ ∂_t v⁺)` (with `∂_t σ = j ∂_s σ`, `polar_deriv`).

The kernel statements built on these are in `GWMemoir.LinearCRNodesKernel`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. Holomorphic maps `S² → E` off `e₂` are constant -/

section Sphere

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A continuous `η : S² → E`, differentiable with `dη ∘ j = J₀ ∘ dη` off `e₂`, is
constant.**  Liouville in the chart `σ₁`, whose image misses `e₂`, and continuity at `e₂`. -/
theorem eq_const_of_holo_off_pt2 {η : S2 → E} (hc : Continuous η)
    (hmd : ∀ y, y ≠ pt 2 → MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) η y) (J₀ : E →L[ℝ] E)
    (hJ : ∀ w, J₀ (J₀ w) = -w)
    (hh : ∀ y, y ≠ pt 2 → ∀ w, mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η y (jStdMap y w) =
      J₀ (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η y w)) (y : S2) :
    η y = η (pt 2) := by
  set f : ℂ → E := fun z => η (sig.symm z)
  have hne : ∀ z, sig.symm z ≠ pt 2 := fun z => (mem_sig_source_iff _).1 (sig_symm_mem z)
  have hτ := fun z => mdifferentiable_holChart_symm 1 (by norm_num) z
  have hfm : ∀ z, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f z := fun z =>
    (hmd _ (hne z)).comp z (hτ z)
  have hf : Differentiable ℝ f := fun z => mdifferentiableAt_iff_differentiableAt.1 (hfm z)
  have hmf : ∀ z v, fderiv ℝ f z v = mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η (sig.symm z) (Dtau z v) := by
    intro z v
    have h : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f z = (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η (sig.symm z)).comp
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) sig.symm z) := mfderiv_comp z (hmd _ (hne z)) (hτ z)
    rw [mfderiv_eq_fderiv] at h
    exact congrArg (fun T => T v) h
  have hCR : ∀ z v, fderiv ℝ f z (Complex.I * v) = J₀ (fderiv ℝ f z v) := by
    intro z v; rw [hmf, hmf, Dtau_I]; exact hh _ (hne z) _
  have hb : Bornology.IsBounded (range f) :=
    (isCompact_range hc).isBounded.subset (range_comp_subset_range _ _)
  have hsig : ∀ y, y ≠ pt 2 → η y = f 0 := by
    intro y hy
    rw [← sig.left_inv ((mem_sig_source_iff y).2 hy)]
    exact const_of_CR hf J₀ hJ hCR hb (sig y)
  have h2 : η (pt 2) = f 0 := by
    set τ' := (holChart (-1) (by norm_num)).symm
    have hτ'c : ContinuousAt (fun w => η (τ' w)) 0 :=
      hc.continuousAt.comp (mdifferentiable_holChart_symm (-1) (by norm_num) 0).continuousAt
    have h1 : Tendsto (fun w => η (τ' w)) (𝓝[≠] 0) (𝓝 (η (pt 2))) := by
      rw [← holChart_neg_symm_zero]; exact hτ'c.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun w => η (τ' w)) (𝓝[≠] 0) (𝓝 (f 0)) := by
      refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun w hw => ?_)
      have e : τ' w = sig.symm w⁻¹ := by
        rw [← holChart_neg_symm_inv w⁻¹ (inv_ne_zero hw), inv_inv]
      change f 0 = η (τ' w)
      rw [e]
      exact (hsig _ (hne _)).symm
    exact tendsto_nhds_unique h1 h2
  by_cases hy : y = pt 2
  · rw [hy]
  · rw [hsig y hy, h2]

end Sphere

/-! ## 2. Two spheres joined at a node -/

section TwoSpheres

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma twoSpheres_offNode_iff (y : twoSpheres.S) :
    (∀ p ∈ twoSpheres.nodes, y ∉ p) ↔ y ≠ Sum.inl (pt 2) ∧ y ≠ Sum.inr (pt 2) := by
  constructor
  · intro h
    refine ⟨fun hy => h _ (mem_singleton _) (hy ▸ Sym2.mem_mk_left _ _),
      fun hy => h _ (mem_singleton _) (hy ▸ Sym2.mem_mk_right _ _)⟩
  · rintro ⟨h1, h2⟩ p hp hyp
    obtain rfl : p = s(Sum.inl (pt 2), Sum.inr (pt 2)) := hp
    rcases Sym2.mem_iff.1 hyp with h | h
    exacts [h1 h, h2 h]

lemma twoSpheres_j_inl (x : S2) : twoSpheres.j.J (Sum.inl x) = jStdMap x := rfl

lemma twoSpheres_j_inr (x : S2) : twoSpheres.j.J (Sum.inr x) = jStdMap x := rfl

/-- The restriction of a section of `twoSpheres` to one sphere satisfies the hypotheses of
`eq_const_of_holo_off_pt2`. -/
lemma holo_comp_inl {η : twoSpheres.S → E} {J₀ : E →L[ℝ] E}
    (hmd : ∀ y, (∀ p ∈ twoSpheres.nodes, y ∉ p) → MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) η y)
    (hh : ∀ y, (∀ p ∈ twoSpheres.nodes, y ∉ p) → ∀ w,
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η y (twoSpheres.j.J y w) = J₀ (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η y w))
    (x : S2) (hx : x ≠ pt 2) :
    MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) (η ∘ Sum.inl) x ∧ ∀ w,
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) (η ∘ Sum.inl) x (jStdMap x w) =
        J₀ (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) (η ∘ Sum.inl) x w) := by
  have hoff : ∀ p ∈ twoSpheres.nodes, (Sum.inl x : twoSpheres.S) ∉ p :=
    (twoSpheres_offNode_iff _).2 ⟨fun h => hx (Sum.inl_injective h), Sum.inl_ne_inr⟩
  refine ⟨mdifferentiableAt_inl_iff.1 (hmd _ hoff), fun w => ?_⟩
  have e := mfderiv_inl (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, E)) (M' := S2) η x
  erw [← e]
  exact hh _ hoff w

lemma holo_comp_inr {η : twoSpheres.S → E} {J₀ : E →L[ℝ] E}
    (hmd : ∀ y, (∀ p ∈ twoSpheres.nodes, y ∉ p) → MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) η y)
    (hh : ∀ y, (∀ p ∈ twoSpheres.nodes, y ∉ p) → ∀ w,
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η y (twoSpheres.j.J y w) = J₀ (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η y w))
    (x : S2) (hx : x ≠ pt 2) :
    MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) (η ∘ Sum.inr) x ∧ ∀ w,
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) (η ∘ Sum.inr) x (jStdMap x w) =
        J₀ (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) (η ∘ Sum.inr) x w) := by
  have hoff : ∀ p ∈ twoSpheres.nodes, (Sum.inr x : twoSpheres.S) ∉ p :=
    (twoSpheres_offNode_iff _).2 ⟨Sum.inr_ne_inl, fun h => hx (Sum.inr_injective h)⟩
  refine ⟨mdifferentiableAt_inr_iff.1 (hmd _ hoff), fun w => ?_⟩
  have e := mfderiv_inr (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, E)) (M := S2) η x
  erw [← e]
  exact hh _ hoff w

/-- **On two spheres joined at a node, a continuous section, holomorphic off the nodal points,
with matching values at the nodal pair, is constant.** -/
theorem eq_const_of_holo_twoSpheres {η : twoSpheres.S → E} (hc : Continuous η)
    (J₀ : E →L[ℝ] E) (hJ : ∀ w, J₀ (J₀ w) = -w)
    (hmd : ∀ y, (∀ p ∈ twoSpheres.nodes, y ∉ p) → MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) η y)
    (hh : ∀ y, (∀ p ∈ twoSpheres.nodes, y ∉ p) → ∀ w,
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η y (twoSpheres.j.J y w) = J₀ (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η y w))
    (hm : IsMatchingSection twoSpheres η) (y : twoSpheres.S) :
    η y = η (Sum.inl (pt 2)) := by
  rcases y with x | x
  · exact eq_const_of_holo_off_pt2 (η := η ∘ Sum.inl) (hc.comp continuous_inl)
      (fun x hx => (holo_comp_inl hmd hh x hx).1) J₀ hJ
      (fun x hx => (holo_comp_inl hmd hh x hx).2) x
  · have h := eq_const_of_holo_off_pt2 (η := η ∘ Sum.inr) (hc.comp continuous_inr)
      (fun x hx => (holo_comp_inr hmd hh x hx).1) J₀ hJ
      (fun x hx => (holo_comp_inr hmd hh x hx).2) x
    exact h.trans (hm _ _ (mem_singleton _)).symm

end TwoSpheres

/-! ## 3. Sections in polar coordinates -/

section Polar

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {m : ℕ} {X : NodalSurface m}

lemma expPolar_ne_zero (p : ℝ × ℝ) : expPolar p ≠ 0 := Complex.exp_ne_zero _

lemma expPolar_def (p : ℝ × ℝ) :
    expPolar p = Complex.exp (-2 * Real.pi * ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := rfl

/-- The inverse of `expPolar` near `expPolar p`: `ζ ↦ p - (log (ζ / e^{-2π(s+it)}))/(2π)`, read
as a point `(s, t)` (real part, imaginary part). -/
def logPolar (p : ℝ × ℝ) (ζ : ℂ) : ℝ × ℝ :=
  (p.1 - (Complex.log (ζ / expPolar p)).re / (2 * Real.pi),
    p.2 - (Complex.log (ζ / expPolar p)).im / (2 * Real.pi))

lemma logPolar_self (p : ℝ × ℝ) : logPolar p (expPolar p) = p := by
  simp [logPolar, div_self (expPolar_ne_zero p)]

lemma expPolar_logPolar (p : ℝ × ℝ) {ζ : ℂ} (hζ : ζ ≠ 0) : expPolar (logPolar p ζ) = ζ := by
  set w := Complex.log (ζ / expPolar p)
  have hw : Complex.exp w = ζ / expPolar p :=
    Complex.exp_log (div_ne_zero hζ (expPolar_ne_zero p))
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have e : -2 * (Real.pi : ℂ) * ((((logPolar p ζ).1 : ℝ) : ℂ) + (((logPolar p ζ).2 : ℝ) : ℂ) *
      Complex.I) = -2 * Real.pi * ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) + w := by
    simp only [logPolar]
    push_cast
    conv_rhs => rw [← Complex.re_add_im w]
    field_simp
    ring
  rw [expPolar_def, e, Complex.exp_add, hw, ← expPolar_def]
  field_simp [expPolar_ne_zero p]

/-- `logPolar p` is differentiable at `expPolar p`, with a derivative `M` satisfying
`M (i z) = (-(M z)₂, (M z)₁)`: the derivative of the inverse of a holomorphic map. -/
lemma hasFDerivAt_logPolar (p : ℝ × ℝ) : ∃ M : ℂ →L[ℝ] ℝ × ℝ,
    HasFDerivAt (logPolar p) M (expPolar p) ∧
      ∀ z, M (Complex.I * z) = (-(M z).2, (M z).1) := by
  set e := expPolar p
  have he : e ≠ 0 := expPolar_ne_zero p
  have h1 : e / e ∈ Complex.slitPlane := by rw [div_self he]; exact Complex.one_mem_slitPlane
  have hg := ((hasDerivAt_id e).div_const e).clog h1
  set d := 1 / e / (e / e)
  set G : ℂ →L[ℝ] ℂ := ((1 : ℂ →L[ℂ] ℂ).smulRight d).restrictScalars ℝ
  have hG : HasFDerivAt (fun ζ => Complex.log (ζ / e)) G e := hg.hasFDerivAt.restrictScalars ℝ
  have hGz : ∀ z, G z = z * d := fun z => by simp [G]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  set M : ℂ →L[ℝ] ℝ × ℝ := ((-(2 * Real.pi)⁻¹) • (Complex.reCLM.comp G)).prod
    ((-(2 * Real.pi)⁻¹) • (Complex.imCLM.comp G))
  refine ⟨M, ?_, fun z => ?_⟩
  · have hre := ((Complex.reCLM.hasFDerivAt.comp e hG).const_smul (-(2 * Real.pi)⁻¹)).const_add
      p.1
    have him := ((Complex.imCLM.hasFDerivAt.comp e hG).const_smul (-(2 * Real.pi)⁻¹)).const_add
      p.2
    refine (hre.prodMk him).congr_of_eventuallyEq (Eventually.of_forall fun ζ => ?_)
    simp only [logPolar, e]
    ext <;> simp <;> ring
  · simp only [M, ContinuousLinearMap.prod_apply, smul_apply,
      ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply, hGz, smul_eq_mul]
    ext
    · simp; ring
    · simp; ring

variable {φ : OpenPartialHomeomorph X.S ℂ} {x : X.S}

/-- Near a point of the polar coordinates, `η = (η ∘ σ ∘ logPolar p) ∘ φ`. -/
lemma eventuallyEq_polar (η : X.S → E) {p : ℝ × ℝ}
    (hp : expPolar p ∈ φ.target) :
    η =ᶠ[𝓝 (X.polar φ p)] fun y => η (X.polar φ (logPolar p (φ y))) := by
  set y₀ := X.polar φ p
  have hy₀ : y₀ ∈ φ.source := X.polar_mem_source hp
  have hφy₀ : φ y₀ = expPolar p := φ.right_inv hp
  have hW : φ.source ∩ φ ⁻¹' {ζ | ζ ≠ 0} ∈ 𝓝 y₀ :=
    (φ.isOpen_inter_preimage isOpen_ne).mem_nhds ⟨hy₀, by
      rw [mem_preimage, hφy₀]; exact expPolar_ne_zero p⟩
  filter_upwards [hW] with y hy
  rw [NodalSurface.polar_eq, expPolar_logPolar p hy.2, φ.left_inv hy.1]

/-- **A section differentiable in polar coordinates is differentiable**: if `v⁺ = η ∘ σ` is
differentiable at `p`, then `η` is differentiable at `σ(p)`, and
`dη(σ p) = d(v⁺ ∘ logPolar p)(e_p) ∘ dφ(σ p)`. -/
theorem mdifferentiableAt_of_polar (hφ : X.IsHolChart φ x) {η : X.S → E} {p : ℝ × ℝ}
    (hp : expPolar p ∈ φ.target)
    (hv : DifferentiableAt ℝ (fun q => η (X.polar φ q)) p) :
    MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) η (X.polar φ p) ∧
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η (X.polar φ p) =
        (fderiv ℝ (fun ζ => η (X.polar φ (logPolar p ζ))) (expPolar p)).comp
          (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) φ (X.polar φ p)) := by
  set y₀ := X.polar φ p
  have hy₀ : y₀ ∈ φ.source := X.polar_mem_source hp
  have hφy₀ : φ y₀ = expPolar p := φ.right_inv hp
  obtain ⟨M, hM, -⟩ := hasFDerivAt_logPolar p
  have hF : DifferentiableAt ℝ (fun ζ => η (X.polar φ (logPolar p ζ))) (expPolar p) := by
    have hv' : DifferentiableAt ℝ (fun q => η (X.polar φ q)) (logPolar p (expPolar p)) := by
      rwa [logPolar_self]
    exact hv'.comp (expPolar p) hM.differentiableAt
  have hφd : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) φ y₀ := (hφ.2.2 y₀ hy₀).1
  have hF' : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun ζ => η (X.polar φ (logPolar p ζ)))
      (φ y₀) := by rw [hφy₀]; exact hF.mdifferentiableAt
  have hcomp := hF'.comp y₀ hφd
  have hev := eventuallyEq_polar η hp
  refine ⟨hcomp.congr_of_eventuallyEq hev, ?_⟩
  rw [hev.mfderiv_eq]
  have h := mfderiv_comp y₀ hF' hφd
  rw [mfderiv_eq_fderiv, hφy₀] at h
  exact h

/-- **Holomorphy from polar coordinates**: if `v⁺ = η ∘ σ` is differentiable at `p` with
`∂_t v⁺ = J₀ ∂_s v⁺` and `J₀² = -1`, then `dη ∘ j = J₀ ∘ dη` at `σ(p)`. -/
theorem holo_of_polar (hφ : X.IsHolChart φ x) {η : X.S → E} {p : ℝ × ℝ}
    (hp : expPolar p ∈ φ.target)
    (hv : DifferentiableAt ℝ (fun q => η (X.polar φ q)) p) (J₀ : E →L[ℝ] E)
    (hJ : ∀ w, J₀ (J₀ w) = -w)
    (hCR : fderiv ℝ (fun q => η (X.polar φ q)) p (0, 1) =
      J₀ (fderiv ℝ (fun q => η (X.polar φ q)) p (1, 0))) (w : E2) :
    mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η (X.polar φ p) (X.j.J (X.polar φ p) w) =
      J₀ (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η (X.polar φ p) w) := by
  set y₀ := X.polar φ p
  have hy₀ : y₀ ∈ φ.source := X.polar_mem_source hp
  obtain ⟨M, hM, hMI⟩ := hasFDerivAt_logPolar p
  set v := fun q => η (X.polar φ q)
  have hv' : DifferentiableAt ℝ v (logPolar p (expPolar p)) := by rwa [logPolar_self]
  have hFd : fderiv ℝ (fun ζ => η (X.polar φ (logPolar p ζ))) (expPolar p) =
      (fderiv ℝ v p).comp M := by
    have h := (hv'.hasFDerivAt.comp (expPolar p) hM).fderiv
    rw [logPolar_self] at h
    exact h
  have hdv : ∀ a b : ℝ, fderiv ℝ v p (-b, a) = J₀ (fderiv ℝ v p (a, b)) := by
    intro a b
    have e1 : ∀ c d : ℝ, (c, d) = c • ((1 : ℝ), (0 : ℝ)) + d • ((0 : ℝ), (1 : ℝ)) := by
      intro c d; ext <;> simp
    rw [e1 (-b) a, e1 a b, map_add, map_smul, map_smul, map_add, map_smul, map_smul, map_add,
      map_smul, map_smul, hCR, hJ]
    simp only [neg_smul, smul_neg]
    abel
  have hφj := (hφ.2.2 y₀ hy₀).2 w
  rw [(mdifferentiableAt_of_polar hφ hp hv).2, hFd]
  change fderiv ℝ v p (M (show ℂ from mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) φ y₀ (X.j.J y₀ w))) =
    J₀ (fderiv ℝ v p (M (show ℂ from mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) φ y₀ w)))
  rw [hφj, hMI, hdv]

end Polar

/-! ## 4. Sections of class `(3, δ₀)` on the necks are `C¹` -/

section NeckC1

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {q : Q} {A : SectionAtlas (E := E) X (fun _ => q)}
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

lemma tcc_const (v : E) : tangentCoordChange 𝓘(ℝ, E) q q q v = v :=
  tangentCoordChange_self (mem_extChartAt_source q)

lemma expPolar_add_int (s t : ℝ) (n : ℤ) : expPolar (s, t + n) = expPolar (s, t) := by
  simp only [expPolar]
  have : -2 * Real.pi * ((s : ℂ) + ((t + n : ℝ) : ℂ) * Complex.I) =
      -2 * Real.pi * ((s : ℂ) + (t : ℂ) * Complex.I) + (-n : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma polar_add_int (φ : OpenPartialHomeomorph X.S ℂ) (s t : ℝ) (n : ℤ) :
    X.polar φ (s, t + n) = X.polar φ (s, t) := by
  rw [NodalSurface.polar_eq, NodalSurface.polar_eq, expPolar_add_int]

variable (A) in
/-- The expression `v⁺ = η ∘ σ_j` of a section in the polar coordinates of the neck `j`. -/
def vPolar (j : Fin A.nn) (η : Section E X) : ℝ × ℝ → E := fun x => η (X.polar (A.hol j) x)

lemma neckRep_const (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) (η : Section E X)
    (x : ℝ × ℝ) : neckRep A j k η x = Real.smoothTransition x.1 *
      (crd k (vPolar A j η (x.1 + A.s0 j, x.2)) - crd k (η (A.node j))) := by
  simp only [neckRep, neckConst, vPolar, tcc_const]

lemma neckRep_add_int (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) (η : Section E X)
    (s t : ℝ) (n : ℤ) : neckRep A j k η (s, t + n) = neckRep A j k η (s, t) := by
  simp only [neckRep, polar_add_int]

variable (A) in
/-- The open set `s > s₀`, `t + ϑ ∈ (0, 1)` of the neck `j`. -/
def neckU (j : Fin A.nn) (ϑ : ℝ) : Set (ℝ × ℝ) := {x | A.s0 j < x.1 ∧ 0 < x.2 + ϑ ∧ x.2 + ϑ < 1}

lemma isOpen_neckU (j : Fin A.nn) (ϑ : ℝ) : IsOpen (neckU A j ϑ) := by
  have h1 : IsOpen {x : ℝ × ℝ | A.s0 j < x.1} := isOpen_lt continuous_const continuous_fst
  have h2 : IsOpen {x : ℝ × ℝ | 0 < x.2 + ϑ} :=
    isOpen_lt continuous_const (continuous_snd.add continuous_const)
  have h3 : IsOpen {x : ℝ × ℝ | x.2 + ϑ < 1} :=
    isOpen_lt (continuous_snd.add continuous_const) continuous_const
  exact h1.inter (h2.inter h3)

/-- The rotated neck block agrees with the rotated neck representative on `s > 0`. -/
lemma eqOn_shH_neckRep (hc : IsContSection (fun _ => q) η) {v : (blocks A δ h0 hmono) 0}
    (hr : IsRep η v) (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) (ϑ : ℝ) {g : ℝ × ℝ → ℝ}
    (hg : Continuous g)
    (hwg : (H.val (Neck.shH 0 ϑ (neckBlock v j k).2) : ℝ × ℝ → ℝ) =ᵐ[cyl] g) :
    EqOn g (fun y => neckRep A j k η (y.1, y.2 - ϑ)) (Ioi 0 ×ˢ Ioo 0 1) := by
  have hV : IsOpen (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1) := isOpen_Ioi.prod isOpen_Ioo
  have hae : g =ᵐ[cyl] fun y => neckRep A j k η (y.1, y.2 - ϑ) := by
    have h1 := Neck.val_shH 0 ϑ (neckBlock v j k).2
    have h2 := (Neck.measurePreserving_shT 0 ϑ).quasiMeasurePreserving.ae_eq_comp
      (hr.2 j k).2
    refine hwg.symm.trans (h1.trans (h2.trans (Eventually.of_forall fun y => ?_)))
    simp only [Function.comp_apply, Neck.shT, sub_zero]
    obtain ⟨n, hn⟩ := Neck.rot_int ϑ y.2
    rw [hn, neckRep_add_int]
  rw [cyl_eq_vol_restrict] at hae
  have hsub : Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1 ⊆ univ ×ˢ Ioc 0 1 :=
    prod_mono (subset_univ _) Ioo_subset_Ioc_self
  refine Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hsub hae) hV
    hg.continuousOn ?_
  refine (continuousOn_neckRep A continuous_const hc j k).comp (by fun_prop) fun y hy => ?_
  exact ⟨hy.1, mem_univ _⟩

/-- **A section of class `(3, δ₀)` is `C¹` in polar coordinates** on `s > s₀`, `t + ϑ ∈ (0, 1)`
(`H³ ⊂ C¹` on the neck block rotated by `ϑ`). -/
theorem neck_C1 (hc : IsContSection (fun _ => q) η) {v : (blocks A δ h0 hmono) 0}
    (hr : IsRep η v) (j : Fin A.nn) (ϑ : ℝ) :
    ∃ Vs Vt : ℝ × ℝ → E, ContinuousOn Vs (neckU A j ϑ) ∧ ContinuousOn Vt (neckU A j ϑ) ∧
      ∀ x ∈ neckU A j ϑ, HasFDerivAt (vPolar A j η)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Vs x) +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Vt x)) x := by
  choose g gs gt hg hgs hgt hwg _ _ hder using
    fun k => exists_C1_rep (Neck.shH 0 ϑ (neckBlock v j k).2)
  have heq := fun k => eqOn_shH_neckRep hc hr j k ϑ (hg k) (hwg k)
  set b := Module.finBasis ℝ E
  set c : E := η (A.node j)
  set β := Real.smoothTransition
  set β' := deriv Real.smoothTransition
  have hβd : ∀ y, HasDerivAt β (β' y) y := fun y =>
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero y).hasDerivAt
  have hβ'c : Continuous β' := (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  set G : ℝ × ℝ → E := fun y => ∑ k, g k y • b k
  set Gs : ℝ × ℝ → E := fun y => ∑ k, gs k y • b k
  set Gt : ℝ × ℝ → E := fun y => ∑ k, gt k y • b k
  have hGc : Continuous G := continuous_finsetSum _ fun k _ => (hg k).smul continuous_const
  have hGsc : Continuous Gs := continuous_finsetSum _ fun k _ => (hgs k).smul continuous_const
  have hGtc : Continuous Gt := continuous_finsetSum _ fun k _ => (hgt k).smul continuous_const
  have hGd : ∀ y ∈ openStrip, HasFDerivAt G ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Gs y) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Gt y)) y := by
    intro y hy
    have h := HasFDerivAt.fun_sum (u := Finset.univ) fun k _ => (hder k y hy).smul_const (b k)
    refine h.congr_fderiv (ContinuousLinearMap.ext fun z => ?_)
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply,
      smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul, Gs, Gt, Finset.smul_sum, add_smul, Finset.sum_add_distrib, smul_smul]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring_nf
  set T : ℝ × ℝ → ℝ × ℝ := fun x => x - (A.s0 j, -ϑ)
  have hTU : ∀ x ∈ neckU A j ϑ, T x ∈ Ioi 0 ×ˢ Ioo 0 1 := fun x hx => by
    obtain ⟨h1, h2, h3⟩ := hx
    refine ⟨?_, ?_, ?_⟩ <;> simp [T] <;> linarith
  have hTS : ∀ x ∈ neckU A j ϑ, T x ∈ openStrip := fun x hx =>
    ⟨mem_univ _, (hTU x hx).2⟩
  have hβpos : ∀ x ∈ neckU A j ϑ, 0 < β (x.1 - A.s0 j) := fun x hx =>
    Real.smoothTransition.pos_of_pos (by linarith [hx.1])
  -- `v⁺ = c + β⁻¹ • G ∘ T` on the neck
  have hrep : ∀ x ∈ neckU A j ϑ, vPolar A j η x = c + (β (x.1 - A.s0 j))⁻¹ • G (T x) := by
    intro x hx
    have hG : G (T x) = β (x.1 - A.s0 j) • (vPolar A j η x - c) := by
      simp only [G]
      rw [← crd_basis_sum (vPolar A j η x - c), Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [heq k (hTU x hx)]
      dsimp only
      rw [neckRep_const, smul_smul, map_sub]
      simp only [T, Prod.fst_sub, Prod.snd_sub, sub_neg_eq_add, sub_add_cancel, add_sub_cancel_right]
      rfl
    rw [hG, smul_smul, inv_mul_cancel₀ (hβpos x hx).ne', one_smul, add_sub_cancel]
  set Vs : ℝ × ℝ → E := fun x => (β (x.1 - A.s0 j))⁻¹ • Gs (T x) +
    (-(β (x.1 - A.s0 j) ^ 2)⁻¹ * β' (x.1 - A.s0 j)) • G (T x)
  set Vt : ℝ × ℝ → E := fun x => (β (x.1 - A.s0 j))⁻¹ • Gt (T x)
  have hTc : Continuous T := by fun_prop
  have hβc : Continuous fun x : ℝ × ℝ => β (x.1 - A.s0 j) :=
    Real.smoothTransition.continuous.comp (by fun_prop)
  refine ⟨Vs, Vt, ?_, ?_, fun x hx => ?_⟩
  · intro x hx
    have hne := (hβpos x hx).ne'
    refine ContinuousAt.continuousWithinAt ?_
    refine ((hβc.continuousAt.inv₀ hne).smul (hGsc.comp hTc).continuousAt).add ?_
    refine ((((hβc.continuousAt.pow 2).inv₀ (pow_ne_zero 2 hne)).neg).mul
      ((hβ'c.comp (by fun_prop : Continuous fun x : ℝ × ℝ => x.1 - A.s0 j)).continuousAt)).smul
      (hGc.comp hTc).continuousAt
  · intro x hx
    exact ((hβc.continuousAt.inv₀ (hβpos x hx).ne').smul
      (hGtc.comp hTc).continuousAt).continuousWithinAt
  · have hne := (hβpos x hx).ne'
    have hT' : HasFDerivAt T (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x :=
      (hasFDerivAt_id x).sub_const _
    have hGT := (hGd (T x) (hTS x hx)).comp x hT'
    have hr' : HasDerivAt (fun s => (β (s - A.s0 j))⁻¹)
        (-(β (x.1 - A.s0 j) ^ 2)⁻¹ * β' (x.1 - A.s0 j)) x.1 := by
      have h1 : HasDerivAt (fun s => β (s - A.s0 j)) (β' (x.1 - A.s0 j)) x.1 := by
        simpa using (hβd (x.1 - A.s0 j)).comp_sub_const x.1 (A.s0 j)
      have h2 := h1.inv hne
      have e : -(β (x.1 - A.s0 j) ^ 2)⁻¹ * β' (x.1 - A.s0 j) =
          -β' (x.1 - A.s0 j) / β (x.1 - A.s0 j) ^ 2 := by ring
      rw [e]
      exact h2
    have hr2 := hr'.comp_hasFDerivAt x (hasFDerivAt_fst (𝕜 := ℝ) (p := x))
    have hsm := (hr2.smul hGT).const_add c
    have hev : (fun y => c + ((fun s => (β (s - A.s0 j))⁻¹) ∘ Prod.fst) y • (G ∘ T) y) =ᶠ[𝓝 x]
        vPolar A j η := by
      filter_upwards [(isOpen_neckU j ϑ).mem_nhds hx] with y hy
      exact (hrep y hy).symm
    refine (hsm.congr_of_eventuallyEq hev.symm).congr_fderiv (ContinuousLinearMap.ext fun z => ?_)
    simp only [Function.comp_apply, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_add, smul_smul, Vs, Vt, add_smul]
    module

end NeckC1

/-! ## 5. The derivative of the polar coordinates -/

section PolarDeriv

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {φ : OpenPartialHomeomorph X.S ℂ} {x : X.S}

/-- `expPolar` is differentiable, with `∂_t e^{-2π(s+it)} = i ∂_s e^{-2π(s+it)}`. -/
lemma hasFDerivAt_expPolar (p : ℝ × ℝ) : ∃ L : ℝ × ℝ →L[ℝ] ℂ,
    HasFDerivAt expPolar L p ∧ L (0, 1) = Complex.I * L (1, 0) := by
  have hf : HasFDerivAt (fun p : ℝ × ℝ => (-2 * Real.pi : ℂ) *
      (Complex.ofRealCLM p.1 + Complex.ofRealCLM p.2 * Complex.I))
      ((-2 * Real.pi : ℂ) • ((Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
        Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)))) p :=
    (((Complex.ofRealCLM.hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ))).add
      ((Complex.ofRealCLM.hasFDerivAt.comp p (hasFDerivAt_snd (𝕜 := ℝ))).mul_const
        Complex.I)).const_mul (-2 * Real.pi : ℂ))
  refine ⟨_, hf.cexp.congr_of_eventuallyEq (Eventually.of_forall fun p => ?_), ?_⟩
  · simp [expPolar]
  · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      Complex.ofRealCLM_apply, smul_eq_mul]
    push_cast
    ring

/-- `dφ(y)` as a map `ℝ² → ℂ`. -/
def dChart (φ : OpenPartialHomeomorph X.S ℂ) (y : X.S) : E2 →L[ℝ] ℂ :=
  mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) φ y

/-- `dφ⁻¹(ζ)` as a map `ℂ → ℝ²`. -/
def dChartInv (φ : OpenPartialHomeomorph X.S ℂ) (ζ : ℂ) : ℂ →L[ℝ] E2 :=
  mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) φ.symm ζ

/-- `φ⁻¹` is holomorphic where it is differentiable: `dφ⁻¹(i z) = j dφ⁻¹(z)`. -/
lemma mfderiv_symm_I (hφ : X.IsHolChart φ x) {ζ : ℂ} (hζ : ζ ∈ φ.target)
    (hsm : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) φ.symm ζ) (z : ℂ) :
    dChartInv φ ζ (Complex.I * z) = X.j.J (φ.symm ζ) (dChartInv φ ζ z) := by
  have hy : φ.symm ζ ∈ φ.source := φ.map_target hζ
  have hφd : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) φ (φ.symm ζ) := (hφ.2.2 _ hy).1
  have hid : ∀ w : ℂ, dChart φ (φ.symm ζ) (dChartInv φ ζ w) = w := by
    have h := mfderiv_comp ζ hφd hsm
    have hev : ((φ : X.S → ℂ) ∘ (φ.symm : ℂ → X.S)) =ᶠ[𝓝 ζ] id := by
      filter_upwards [φ.open_target.mem_nhds hζ] with ζ' hζ' using φ.right_inv hζ'
    have h2 : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((φ : X.S → ℂ) ∘ (φ.symm : ℂ → X.S)) ζ =
        ContinuousLinearMap.id ℝ ℂ := by
      rw [hev.mfderiv_eq, mfderiv_id]; rfl
    intro w
    exact congrArg (fun L => L w) (h.symm.trans h2)
  have hinj : Injective (dChart φ (φ.symm ζ)) := by
    have hsurj : Surjective (dChart φ (φ.symm ζ)) := fun w => ⟨_, hid w⟩
    have hfin : Module.finrank ℝ E2 = Module.finrank ℝ ℂ := by
      simp [Complex.finrank_real_complex]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
      (f := ((dChart φ (φ.symm ζ) : E2 →L[ℝ] ℂ) : E2 →ₗ[ℝ] ℂ))).2 hsurj
  apply hinj
  have hj : ∀ v, dChart φ (φ.symm ζ) (X.j.J (φ.symm ζ) v) =
      Complex.I * dChart φ (φ.symm ζ) v := (hφ.2.2 _ hy).2
  rw [hid, hj, hid]

/-- **The polar coordinates are holomorphic**: where `φ⁻¹` is differentiable, `σ` is
differentiable and `∂_t σ = j ∂_s σ`. -/
lemma polar_deriv (hφ : X.IsHolChart φ x) {p : ℝ × ℝ} (hp : expPolar p ∈ φ.target)
    (hsm : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) φ.symm (expPolar p)) :
    MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar φ) p ∧
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar φ) p (0, 1) =
        X.j.J (X.polar φ p) (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar φ) p (1, 0)) := by
  obtain ⟨L, hL, hLI⟩ := hasFDerivAt_expPolar p
  have hE : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) expPolar p :=
    hL.differentiableAt.mdifferentiableAt
  have he : X.polar φ = φ.symm ∘ expPolar := rfl
  have hd := hsm.comp p hE
  refine ⟨he ▸ hd, ?_⟩
  have hc := mfderiv_comp p hsm hE
  rw [mfderiv_eq_fderiv, hL.fderiv] at hc
  rw [he, hc]
  change dChartInv φ (expPolar p) (L (0, 1)) =
    X.j.J (φ.symm (expPolar p)) (dChartInv φ (expPolar p) (L (1, 0)))
  rw [hLI, mfderiv_symm_I hφ hp hsm]

/-- **The polar expression of `projF J₀ dη`**: where `φ⁻¹` is differentiable and `η` is
differentiable at `σ(p)`, `ξ(σ)(∂_s σ) = ½ (∂_s v⁺ + J₀ ∂_t v⁺)` for `ξ = projF J₀ dη`. -/
theorem formInPolar_projF {q : Q} (hφ : X.IsHolChart φ x) {η : X.S → E} {p : ℝ × ℝ}
    (hp : expPolar p ∈ φ.target) (hsm : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) φ.symm (expPolar p))
    (hd : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) η (X.polar φ p)) (J₀ : E →L[ℝ] E) :
    X.formInPolar (fun _ => q) (projF J₀ (dForm η)) φ x p =
      (1 / 2 : ℝ) • (fderiv ℝ (fun q => η (X.polar φ q)) p (1, 0) +
        J₀ (fderiv ℝ (fun q => η (X.polar φ q)) p (0, 1))) := by
  obtain ⟨hσ, hj⟩ := polar_deriv hφ hp hsm
  have hc := mfderiv_comp p hd hσ
  rw [mfderiv_eq_fderiv] at hc
  have h10 : fderiv ℝ (fun q => η (X.polar φ q)) p (1, 0) =
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η (X.polar φ p)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar φ) p (1, 0)) := congrArg (fun L => L (1, 0)) hc
  have h01 : fderiv ℝ (fun q => η (X.polar φ q)) p (0, 1) =
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η (X.polar φ p)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E2) (X.polar φ) p (0, 1)) := congrArg (fun L => L (0, 1)) hc
  rw [h10, h01, hj]
  simp only [NodalSurface.formInPolar, tcc_const, projF, twist, dForm, Pi.smul_apply,
    Pi.add_apply]
  rfl

end PolarDeriv

end GWMemoir
