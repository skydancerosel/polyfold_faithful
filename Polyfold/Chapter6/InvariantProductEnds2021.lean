import Polyfold.Chapter4.ManifoldFaceForms2021
import Polyfold.Chapter6.ProperHomotopy2021

/-!
# The ends of the cobordism `S_F` (2021 Theorem 6.7.1, independence of the perturbation)

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021): the end computations in
the proof of Theorem 6.7.1 (pp. 277–278; preprint Theorem 6.43), where the solution set `S_F` of
`F(t, x) = f(x) + Ŝ(t, x)` over `ℝ¹ × X` (Remark 6.6.19, p. 276; reading D2: `ℝ¹ × X` in place
of `[0, 1] × X`) is `ℝ × S_i` near its ends, oriented by `e ∧ o_{S_i}`, with boundary orientation
outward vector first (Definition 9.3.8, p. 427).

Everything is stated for an abstract `(k+1)`-manifold with corners `M` with a product end over a
`k`-manifold `N`:

* `ProductEnd k N M a b`: an open part of `M` identified with `(a, b) × N` by `φ`, such that the
  product charts `(t, y) ↦ (t − a, e(y))` (`endChart`, built from `consQuad`) of the charts
  `e = chartAt y` of `N` belong to the maximal atlas of `M`; `modelEnd` is a model instance.
* `ProductEnd.IsEndProductOrientation oM oN`: `oM = e ∧ oN` on the end (the time direction
  first), a hypothesis (wave 1c-2 proves it for the orientation of `S_F`); it holds for the
  standard orientations on `modelEnd` (`modelEnd_isEndProductOrientation`).
* `ProductEnd.integral_end_fubini`: a form `Θ` supported in the end whose coefficient in the
  product charts is `h(t)` times that of `ω` on `N` has `∫_M Θ = (∫ₐᵇ h) ∫_N ω`; for
  `Θ = g′(t) dt ∧ p₁^*ω`, `∫_{S_F} g′ dt ∧ p₁^*ω = (∫ g′) ∫_{S_i} ω`.
* `ProductEnd.boundaryIntegral_end_sign`, `ProductEnd.faceIntegral_end_sign`: for `β` reading
  as `h(t) dt ∧ β_N` (`dtWedge`), `∫_{∂M} β = −(∫ₐᵇ h) ∫_{∂N} β_N`: the piece `(a, b) × ∂N` of
  `∂M` carries `−(e ∧ o_{∂N})` (reading R-f); proved from `integral_end_fubini` for `dβ`
  (`extDerivWithin_dtWedge_stdFrame`: `d(h dt ∧ η) = −h dt ∧ dη`) and Stokes' theorem.
* `StrongBundle.IsCobordismData.solutionSet_left_eq_prod` (and `right`, and the parts cut out by
  a condition on `X` such as the index): `S_F ∩ {t ≤ 1/8} = {t ≤ 1/8} × S_{f+σ₀}` as sets.
* General tools: `ManifoldForm.ContMDiffForm.contDiffOn_chartForm` (a `C^r` form is `C^r` in every
  chart of the maximal atlas), `ManifoldForm.integral_eq_chartIntegral_of_mem_maximalAtlas`
  (localization in such a chart), `setIntegral_consE_mul` (Fubini in `ℝ × ℝ^k`).

Not built here: the corner coordinates of `S_F` from those of `S_i` (`CornerCoords.prodRn`), which
would give a `ProductEnd` for the index parts of `S_F` with their corner charted spaces, and the
expression of the forms `p₁^*ω` in the product charts.
-/

open Set Filter Topology Manifold Module MeasureTheory

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

/-! ### Coordinates on `ℝ^{k+1} = ℝ × ℝ^k` -/

section Coordinates

variable {k : ℕ}

/-- `(s, z) ↦ (s, z₀, …, z_{k-1})`: the time coordinate first. -/
def consE (s : ℝ) (z : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin (k + 1)) :=
  WithLp.toLp 2 (Fin.cons s (WithLp.ofLp z))

/-- `y ↦ (y₁, …, y_k)`: forgetting the time coordinate. -/
def tailE (y : EuclideanSpace ℝ (Fin (k + 1))) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))

@[simp] theorem consE_zero (s : ℝ) (z : EuclideanSpace ℝ (Fin k)) : consE s z 0 = s := rfl

@[simp] theorem consE_succ (s : ℝ) (z : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    consE s z i.succ = z i := rfl

@[simp] theorem tailE_apply (y : EuclideanSpace ℝ (Fin (k + 1))) (i : Fin k) :
    tailE y i = y i.succ := rfl

@[simp] theorem tailE_consE (s : ℝ) (z : EuclideanSpace ℝ (Fin k)) : tailE (consE s z) = z := rfl

@[simp] theorem consE_tailE (y : EuclideanSpace ℝ (Fin (k + 1))) : consE (y 0) (tailE y) = y := by
  ext i
  refine Fin.cases rfl (fun j => rfl) i

theorem continuous_consE : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin k) => consE p.1 p.2 := by
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_fst
  · exact (PiLp.continuous_apply 2 _ j).comp continuous_snd

theorem continuous_tailE : Continuous (tailE (k := k)) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => PiLp.continuous_apply 2 _ i.succ)

end Coordinates

/-! ### Fubini in the coordinates `ℝ^{k+1} = ℝ × ℝ^k` -/

section ConsFubini

variable (k : ℕ)

/-- `y ↦ (y₀, (y₁, …, y_k))` as a measurable equivalence `ℝ^{k+1} ≃ ℝ × ℝ^k`. -/
def consEquiv : EuclideanSpace ℝ (Fin (k + 1)) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin k) :=
  ((MeasurableEquiv.toLp 2 (Fin (k + 1) → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.toLp 2 (Fin k → ℝ)))

variable {k}

theorem consEquiv_apply (y : EuclideanSpace ℝ (Fin (k + 1))) :
    consEquiv k y = (y 0, tailE y) := rfl

variable (k) in
theorem measurePreserving_consEquiv : MeasurePreserving (consEquiv k) := by
  have h1 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (k + 1))
  have h2 := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => (volume : Measure ℝ)) 0
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin k))
  rw [← Measure.volume_eq_prod] at h3
  exact (h3.comp (h2.comp h1) :)

/-- **Fubini in the coordinates `ℝ × ℝ^k`**: the integral of `F(y₀) G(y₁, …, y_k)` over
`{y₀ ∈ S, (y₁, …, y_k) ∈ T}` is `∫_S F · ∫_T G`. -/
theorem setIntegral_consE_mul (S : Set ℝ) (T : Set (EuclideanSpace ℝ (Fin k))) (F : ℝ → ℝ)
    (G : EuclideanSpace ℝ (Fin k) → ℝ) :
    ∫ y in {y : EuclideanSpace ℝ (Fin (k + 1)) | y 0 ∈ S ∧ tailE y ∈ T}, F (y 0) * G (tailE y) =
      (∫ s in S, F s) * ∫ z in T, G z := by
  have h := (measurePreserving_consEquiv k).setIntegral_preimage_emb
    (consEquiv k).measurableEmbedding (fun p => F p.1 * G p.2) (S ×ˢ T)
  rw [Measure.volume_eq_prod, setIntegral_prod_mul] at h
  exact h

/-- The shift `s ↦ s + a` of `(0, b − a)` onto `(a, b)`. -/
theorem setIntegral_Ioo_add (h : ℝ → ℝ) (a b : ℝ) :
    ∫ s in Ioo 0 (b - a), h (s + a) = ∫ t in Ioo a b, h t := by
  have := (measurePreserving_add_right (volume : Measure ℝ) a).setIntegral_preimage_emb
    (measurableEmbedding_addRight a) h (Ioo a b)
  rwa [preimage_add_const_Ioo, sub_self] at this

end ConsFubini

/-! ### The forms `dt ∧ η` on `ℝ × ℝ^k` -/

section DtWedge

variable {k m : ℕ}

variable (k) in
/-- `y ↦ (y₁, …, y_k)` as a continuous linear map `ℝ^{k+1} → ℝ^k`. -/
def tailCLM : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  LinearMap.toContinuousLinearMap
    { toFun := tailE
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] theorem tailCLM_apply (y : EuclideanSpace ℝ (Fin (k + 1))) : tailCLM k y = tailE y := rfl

variable (k m) in
/-- **`dt ∧ ·`**: the `(m+1)`-form `dt ∧ η` on `ℝ × ℝ^k` of an `m`-form `η` on `ℝ^k`,
`(dt ∧ η)(v₀, …, v_m) = ∑ⱼ (-1)ʲ dt(vⱼ) η(v₀', …, v̂ⱼ', …, v_m')` (primes: the `ℝ^k`
components), as a continuous linear map in `η`. -/
def dtWedgeCLM : (EuclideanSpace ℝ (Fin k) [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ]
    (EuclideanSpace ℝ (Fin (k + 1)) [⋀^Fin (m + 1)]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℝ).comp
    ((ContinuousLinearMap.smulRightL ℝ _ _ (EuclideanSpace.proj (0 : Fin (k + 1)))).comp
      (ContinuousAlternatingMap.compContinuousLinearMapCLM (tailCLM k)))

/-- The form `dt ∧ η`. -/
abbrev dtWedge (η : EuclideanSpace ℝ (Fin k) [⋀^Fin m]→L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin (k + 1)) [⋀^Fin (m + 1)]→L[ℝ] ℝ :=
  dtWedgeCLM k m η

theorem dtWedge_apply (η : EuclideanSpace ℝ (Fin k) [⋀^Fin m]→L[ℝ] ℝ)
    (w : Fin (m + 1) → EuclideanSpace ℝ (Fin (k + 1))) :
    dtWedge η w = ∑ j : Fin (m + 1),
      (-1) ^ (j : ℕ) • (w j 0 * η (fun l => tailE (j.removeNth w l))) := by
  simp only [dtWedge, dtWedgeCLM, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]
  rfl

/-- `dt ∧ η` vanishes on vectors with no `t`-component. -/
theorem dtWedge_apply_of_zero (η : EuclideanSpace ℝ (Fin k) [⋀^Fin m]→L[ℝ] ℝ)
    {w : Fin (m + 1) → EuclideanSpace ℝ (Fin (k + 1))} (hw : ∀ j, w j 0 = 0) :
    dtWedge η w = 0 := by
  rw [dtWedge_apply]
  exact Finset.sum_eq_zero fun j _ => by rw [hw j, zero_mul, smul_zero]

/-- `(dt ∧ η)(∂ₜ, v₁, …, v_m) = η(v₁', …, v_m')` for `v₁, …, v_m` with no `t`-component. -/
theorem dtWedge_apply_of_first (η : EuclideanSpace ℝ (Fin k) [⋀^Fin m]→L[ℝ] ℝ)
    {w : Fin (m + 1) → EuclideanSpace ℝ (Fin (k + 1))} (h0 : w 0 0 = 1)
    (hw : ∀ j : Fin m, w j.succ 0 = 0) :
    dtWedge η w = η (fun l => tailE (w l.succ)) := by
  rw [dtWedge_apply, Fin.sum_univ_succ, h0]
  rw [Finset.sum_eq_zero fun j _ => by rw [hw j, zero_mul, smul_zero]]
  simp only [Fin.val_zero, pow_zero, one_mul, one_smul, add_zero, Fin.removeNth_zero]
  rfl

theorem tailE_stdFrame_zero : tailE (stdFrame (k + 1) 0) = 0 := by
  ext i; rw [tailE_apply, stdFrame_apply_apply]; simp [Fin.succ_ne_zero]

theorem tailE_stdFrame_succ (i : Fin k) : tailE (stdFrame (k + 1) i.succ) = stdFrame k i := by
  ext j; rw [tailE_apply, stdFrame_apply_apply, stdFrame_apply_apply]; simp

theorem stdFrame_succ_apply_zero (i : Fin k) : stdFrame (k + 1) i.succ 0 = 0 := by
  rw [stdFrame_apply_apply]; simp [(Fin.succ_ne_zero i).symm]

theorem stdFrame_apply_zero_zero : stdFrame (k + 1) 0 0 = 1 := by
  rw [stdFrame_apply_apply]; simp

/-- **`d(h(t) dt ∧ η) = −h(t) dt ∧ dη`** in coordinates: if `F = h(t + a) · dt ∧ G` near `y` (on
a set `s` with unique derivatives mapped into `T` by the projection), with `h` differentiable and
`G` differentiable within `T`, then the coefficient of `dF` is `−h` times the coefficient of
`dG`. -/
theorem extDerivWithin_dtWedge_stdFrame {s : Set (EuclideanSpace ℝ (Fin (m + 1 + 1)))}
    {T : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    {F : EuclideanSpace ℝ (Fin (m + 1 + 1)) →
      EuclideanSpace ℝ (Fin (m + 1 + 1)) [⋀^Fin (m + 1)]→L[ℝ] ℝ}
    {G : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1)) [⋀^Fin m]→L[ℝ] ℝ}
    {h : ℝ → ℝ} {a : ℝ} {y : EuclideanSpace ℝ (Fin (m + 1 + 1))} (hy : y ∈ s)
    (hs : UniqueDiffWithinAt ℝ s y) (hsT : MapsTo tailE s T)
    (hF : ∀ z ∈ s, F z = h (z 0 + a) • dtWedge (G (tailE z)))
    (hh : DifferentiableAt ℝ h (y 0 + a)) (hG : DifferentiableWithinAt ℝ G T (tailE y)) :
    extDerivWithin F s y (stdFrame (m + 1 + 1)) =
      -(h (y 0 + a) * extDerivWithin G T (tailE y) (stdFrame (m + 1))) := by
  set G' := fderivWithin ℝ G T (tailE y)
  set c' : EuclideanSpace ℝ (Fin (m + 1 + 1)) →L[ℝ] ℝ :=
    deriv h (y 0 + a) • EuclideanSpace.proj (0 : Fin (m + 1 + 1))
  have hc : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin (m + 1 + 1)) => h (z 0 + a)) c' y := by
    have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin (m + 1 + 1)) => z 0 + a)
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (m + 1 + 1)) :
          EuclideanSpace ℝ (Fin (m + 1 + 1)) →L[ℝ] ℝ) y := by
      have := ((EuclideanSpace.proj (0 : Fin (m + 1 + 1)) :
        EuclideanSpace ℝ (Fin (m + 1 + 1)) →L[ℝ] ℝ).hasFDerivAt (x := y)).add_const a
      exact this
    exact hh.hasDerivAt.comp_hasFDerivAt y h1
  have hf : HasFDerivWithinAt (fun z => dtWedge (G (tailE z)))
      ((dtWedgeCLM (m + 1) m).comp (G'.comp (tailCLM (m + 1)))) s y :=
    (dtWedgeCLM (m + 1) m).hasFDerivAt.comp_hasFDerivWithinAt y
      (hG.hasFDerivWithinAt.comp y (tailCLM (m + 1)).hasFDerivWithinAt hsT)
  have hL : HasFDerivWithinAt (fun z => h (z 0 + a) • dtWedge (G (tailE z))) _ s y :=
    hc.hasFDerivWithinAt.smul hf
  rw [extDerivWithin_congr' (ω₂ := fun z => h (z 0 + a) • dtWedge (G (tailE z))) hF hy,
    extDerivWithin, hL.fderivWithin hs, extDerivWithin,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  have h0 : ∀ j : Fin (m + 1), Fin.removeNth 0 (stdFrame (m + 1 + 1)) j 0 = 0 := fun j => by
    rw [Fin.removeNth_zero]; exact stdFrame_succ_apply_zero j
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    tailCLM_apply, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply]
  rw [tailE_stdFrame_zero, map_zero, map_zero, dtWedge_apply_of_zero _ h0]
  simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply, smul_zero, zero_add]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hw : dtWedgeCLM (m + 1) m (G' (stdFrame (m + 1) i))
      (Fin.removeNth i.succ (stdFrame (m + 1 + 1))) =
      G' (stdFrame (m + 1) i) (Fin.removeNth i (stdFrame (m + 1))) := by
    rw [dtWedge_apply_of_first]
    · congr 1
      funext l
      simp only [Fin.removeNth_apply, Fin.succ_succAbove_succ, tailE_stdFrame_succ]
    · simp only [Fin.removeNth_apply, Fin.succ_succAbove_zero]; exact stdFrame_apply_zero_zero
    · intro j
      simp only [Fin.removeNth_apply, Fin.succ_succAbove_succ]
      exact stdFrame_succ_apply_zero _
  have hp :
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (m + 1 + 1))) (stdFrame (m + 1 + 1) i.succ) = 0 :=
    stdFrame_succ_apply_zero i
  rw [tailE_stdFrame_succ, hw]
  simp only [c', smul_apply, Fin.val_succ, pow_succ, smul_eq_mul]
  rw [hp]
  ring

end DtWedge

/-! ### The product quadrant chart -/

section ConsQuad

variable {k : ℕ} (a b : ℝ)

theorem consE_nonneg {s : ℝ} (hs : 0 ≤ s) (z : EuclideanQuadrant k) (i : Fin (k + 1)) :
    0 ≤ consE s z.1 i :=
  Fin.cases hs (fun j => z.2 j) i

/-- **The product quadrant chart** `(t, z) ↦ (t − a, z)`, an open embedding of `(a, b) × [0,∞)ᵏ`
onto `{q ∈ [0,∞)^{k+1} | 0 < q₀ < b − a}`: the time coordinate is the first one, and it is
interior. -/
def consQuad : OpenPartialHomeomorph (ℝ × EuclideanQuadrant k) (EuclideanQuadrant (k + 1)) where
  toFun p := ⟨consE (max (p.1 - a) 0) p.2.1, consE_nonneg (le_max_right _ _) p.2⟩
  invFun q := (q.1 0 + a, ⟨tailE q.1, fun i => q.2 i.succ⟩)
  source := Ioo a b ×ˢ univ
  target := {q | q.1 0 ∈ Ioo 0 (b - a)}
  map_source' := by
    rintro ⟨t, z⟩ ⟨ht, -⟩
    change max (t - a) 0 ∈ Ioo 0 (b - a)
    rw [max_eq_left (by linarith [ht.1])]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  map_target' := by
    rintro q hq
    exact ⟨⟨by linarith [hq.1], by linarith [hq.2]⟩, mem_univ _⟩
  left_inv' := by
    rintro ⟨t, z⟩ ⟨ht, -⟩
    refine Prod.ext ?_ (Subtype.ext rfl)
    change max (t - a) 0 + a = t
    rw [max_eq_left (by linarith [ht.1]), sub_add_cancel]
  right_inv' := by
    rintro q hq
    apply Subtype.ext
    simp only [add_sub_cancel_right]
    rw [max_eq_left hq.1.le]
    exact consE_tailE q.1
  open_source := isOpen_Ioo.prod isOpen_univ
  open_target := isOpen_Ioo.preimage ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val)
  continuousOn_toFun := by
    refine Continuous.continuousOn (Continuous.subtype_mk ?_ _)
    exact continuous_consE.comp (((continuous_fst.sub continuous_const).max continuous_const).prodMk
      (continuous_subtype_val.comp continuous_snd))
  continuousOn_invFun := by
    refine Continuous.continuousOn (Continuous.prodMk ?_ (Continuous.subtype_mk ?_ _))
    · exact ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val).add continuous_const
    · exact continuous_tailE.comp continuous_subtype_val

variable {a b}

theorem consQuad_source : (consQuad (k := k) a b).source = Ioo a b ×ˢ univ := rfl

theorem consQuad_target : (consQuad (k := k) a b).target = {q | q.1 0 ∈ Ioo 0 (b - a)} := rfl

theorem consQuad_apply {t : ℝ} (ht : a < t) (z : EuclideanQuadrant k) :
    (consQuad a b (t, z)).1 = consE (t - a) z.1 := by
  change consE (max (t - a) 0) z.1 = _
  rw [max_eq_left (by linarith)]

theorem consQuad_symm_apply (q : EuclideanQuadrant (k + 1)) :
    (consQuad a b).symm q = (q.1 0 + a, ⟨tailE q.1, fun i => q.2 i.succ⟩) := rfl

end ConsQuad

/-! ### Forms in charts of the maximal atlas -/

namespace ManifoldForm

section GeneralCharts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ}

/-- **A form multiplied by a function continuous near its support** is continuous: if `ω` is
continuous and `f` is continuous on an open set `U ⊇ tsupport ω`, then `f ω` is continuous. -/
theorem contMDiffForm_zero_smulFun_of_continuousOn {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContinuousOn f U) {ω : ManifoldForm I M k} (hω : ContMDiffForm I 0 ω)
    (hsU : tsupport ω ⊆ U) : ContMDiffForm I 0 (smulFun f ω) := fun x => by
  rw [contDiffOn_zero]
  intro y hy
  have hsymm := continuousOn_extChartAt_symm (I := I) x y hy
  have heq : chartForm I (chartAt H x) (smulFun f ω) =
      fun z => f ((extChartAt I x).symm z) • chartForm I (chartAt H x) ω z := by
    funext z; exact chartForm_smulFun _ _ _ _
  rw [heq]
  by_cases hyU : (extChartAt I x).symm y ∈ U
  · exact ((hf.continuousAt (hU.mem_nhds hyU)).comp_continuousWithinAt hsymm).smul
      (contDiffOn_zero.1 (hω x) y hy)
  · have hyK : (extChartAt I x).symm y ∉ tsupport ω := fun h => hyU (hsU h)
    have hev : (fun z => f ((extChartAt I x).symm z) • chartForm I (chartAt H x) ω z) =ᶠ[𝓝[
        (extChartAt I x).target] y] fun _ => 0 := by
      filter_upwards [hsymm.preimage_mem_nhdsWithin ((isClosed_closure).isOpen_compl.mem_nhds hyK)]
        with z hz
      rw [chartForm_eq_zero_of_notMem (K := tsupport ω) (fun p hp => eq_zero_of_notMem_tsupport hp)
        _ hz, smul_zero]
    exact continuousWithinAt_const.congr_of_eventuallyEq hev (hev.self_of_nhdsWithin hy)

variable [IsManifold I ∞ M]

/-- **A `C^r` form is `C^r` in every chart of the maximal atlas** (the definition
`ContMDiffForm` asks it in the charts `chartAt H x` only). -/
theorem ContMDiffForm.contDiffOn_chartForm {r : WithTop ℕ∞} (hr : r ≤ ∞) {ω : ManifoldForm I M k}
    (hω : ContMDiffForm I r ω) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) :
    ContDiffOn ℝ r (chartForm I e ω) (e.extend I).target := fun y hy => by
  set p := (e.extend I).symm y
  set c := chartAt H p
  have hc := IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) p
  have hp : p ∈ e.source := by rw [← e.extend_source (I := I)]; exact (e.extend I).map_target hy
  have hy' : e.extend I p = y := (e.extend I).right_inv hy
  have hpc : p ∈ c.source := mem_chart_source H p
  have hev := chartForm_eventuallyEq_formPullback he hc ω hp hpc
  rw [hy'] at hev
  have hφ := I.contDiffWithinAt_extendCoordChange' (n := ∞) he hc hp hpc
  rw [hy'] at hφ
  have hfx : I.extendCoordChange e c y = c.extend I p := by
    rw [← hy']
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply]
    rw [e.extend_left_inv hp]
  have hmaps : MapsTo (I.extendCoordChange e c) (range I) (range I) := fun z _ => by
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
      OpenPartialHomeomorph.extend_coe]
    exact mem_range_self _
  have hyI : y ∈ range I := e.extend_target_subset_range hy
  have hd : ContDiffWithinAt ℝ r (chartForm I c ω) (range I) (c.extend I p) :=
    (hω p _ (mem_extChartAt_target p)).mono_of_mem_nhdsWithin
      (extChartAt_target_mem_nhdsWithin p)
  have h1 : ContDiffWithinAt ℝ r (fun z => chartForm I c ω (I.extendCoordChange e c z))
      (range I) y := by
    rw [← hfx] at hd
    exact hd.comp y (hφ.of_le hr) hmaps
  have h2 : ContDiffWithinAt ℝ r (fderivWithin ℝ (I.extendCoordChange e c) (range I))
      (range I) y := hφ.fderivWithin_right I.uniqueDiffOn (add_one_le_infty hr) hyI
  exact ((ContDiffWithinAt.formPullback' h1 h2).congr_of_eventuallyEq hev
    (hev.self_of_nhdsWithin hyI)).mono e.extend_target_subset_range

end GeneralCharts

section Localization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
  [IsManifold (𝓠 n) ∞ M] [T2Space M] [SigmaCompactSpace M] {o : TangentOrientation (𝓠 n) M n}

/-- **A form supported in a signed chart of the maximal atlas**: if `ω` (continuous) vanishes
outside a compact set `K` lying in a region `V` of a chart `e` of the maximal atlas on which `o`
reads as `signedOr b (stdOrientation n)`, then `∫_M ω = orSign b · ∫_e ω`
(`integral_eq_chartIntegral` for an arbitrary chart instead of `chartAt H x₀`). -/
theorem integral_eq_chartIntegral_of_mem_maximalAtlas (ho : o.IsContinuous (𝓠 n) ∞)
    {ω : ManifoldForm (𝓠 n) M n} (hω : ContMDiffForm (𝓠 n) 0 ω)
    {e : OpenPartialHomeomorph M (EuclideanQuadrant n)}
    (he : e ∈ IsManifold.maximalAtlas (𝓠 n) ∞ M) {V : Set M} (hV : V ⊆ e.source) {b : Bool}
    (hb : ∀ x ∈ V, orientationIn e x (o x) = signedOr b (stdOrientation n))
    {K : Set M} (hK : IsCompact K) (hKV : K ⊆ V) (hω0 : ∀ x ∉ K, ω x = 0) :
    integral o ω = orSign b * chartIntegral e ω := by
  have hsK : tsupport ω ⊆ K := closure_minimal (fun x hx => by_contra fun h => hx (hω0 x h))
    hK.isClosed
  obtain ⟨T, ⟨D⟩⟩ := exists_integrationData ho hK
  rw [integral_eq_integrationData ho hω (hK.of_isClosed_subset isClosed_closure hsK) D hsK]
  have step : ∀ j, orSign (D.sign j) * chartIntegral (D.chart j) (smulFun (D.ρ j) ω) =
      orSign b * chartIntegral e (smulFun (D.ρ j) ω) :=
    fun j => orSign_mul_chartIntegral_eq he
      (IsManifold.chart_mem_maximalAtlas (D.center j)) (K := _root_.tsupport (D.ρ j) ∩ K)
      (fun x hx => ⟨hV (hKV hx.2), D.region_subset j (D.tsupport_subset j hx.1)⟩)
      (fun x hx => smulFun_eq_zero_of_notMem hω0 hx) (fun x hx => hb x (hKV hx.2))
      (fun x hx => D.orientationIn_eq j x (D.tsupport_subset j hx.1))
  rw [IntegrationData.integral, Finset.sum_congr rfl fun j _ => step j, ← Finset.mul_sum,
    ← chartIntegral_finsetSum Finset.univ (fun j _ =>
      ((D.contMDiffForm_smulFun (by simp) j hω).contDiffOn_chartForm (by simp) he).continuousOn)
      (fun j _ => hK.inter_left (isClosed_tsupport (D.ρ j)))
      (fun j _ => fun x hx => hV (hKV hx.2))
      (fun j _ => fun x hx => smulFun_eq_zero_of_notMem hω0 hx),
    finsetSum_smulFun_eq_self Finset.univ D.sum_eq_one subset_rfl hω0]

end Localization

end ManifoldForm

/-! ### Product ends -/

section ProductEnd

variable {k : ℕ} {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanQuadrant k) N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (k + 1)) M] {a b : ℝ}

/-- **The product chart** of a chart `e` of `N` through an identification `φ` of an open part of
`M` with `(a, b) × N`: `p ↦ (t − a, e(y))` for `φ(p) = (t, y)`, the time coordinate first. -/
def endChart (φ : OpenPartialHomeomorph M (ℝ × N)) (a b : ℝ)
    (e : OpenPartialHomeomorph N (EuclideanQuadrant k)) :
    OpenPartialHomeomorph M (EuclideanQuadrant (k + 1)) :=
  (φ.trans ((OpenPartialHomeomorph.refl ℝ).prod e)).trans (consQuad a b)

variable (k N M a b) in
/-- **A product end** of the `(k+1)`-manifold `M` over the `k`-manifold `N` (the ends
`(a, b) × S_i` of the cobordism `S_F` in the proof of 2021 Theorem 6.7.1, p. 278): an open part
`φ.source` of `M` identified with `(a, b) × N` by `φ`, such that the product charts
`(t, y) ↦ (t − a, e(y))` of the charts `e = chartAt y` of `N` belong to the maximal atlas of `M`
(the identification is a diffeomorphism). -/
structure ProductEnd where
  /-- The identification of the end with `(a, b) × N`. -/
  φ : OpenPartialHomeomorph M (ℝ × N)
  target_eq : φ.target = Ioo a b ×ˢ univ
  chart_mem : ∀ x : N, endChart φ a b (chartAt (EuclideanQuadrant k) x) ∈
    IsManifold.maximalAtlas (𝓠 (k + 1)) ∞ M

namespace ProductEnd

variable (E : ProductEnd k N M a b)

/-- The product chart of a chart `e` of `N`. -/
abbrev chart (e : OpenPartialHomeomorph N (EuclideanQuadrant k)) :
    OpenPartialHomeomorph M (EuclideanQuadrant (k + 1)) :=
  endChart E.φ a b e

theorem mem_target {p : M} (hp : p ∈ E.φ.source) : (E.φ p).1 ∈ Ioo a b := by
  have h := E.φ.map_source hp
  rw [E.target_eq] at h
  exact h.1

theorem mem_chart_source {e : OpenPartialHomeomorph N (EuclideanQuadrant k)} {p : M} :
    p ∈ (E.chart e).source ↔ p ∈ E.φ.source ∧ (E.φ p).2 ∈ e.source := by
  simp only [chart, endChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.prod_source, OpenPartialHomeomorph.refl_source, mem_inter_iff,
    mem_preimage, mem_prod, mem_univ, true_and, consQuad_source, OpenPartialHomeomorph.trans_apply,
    OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply, id, and_true]
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, E.mem_target h1⟩

theorem chart_apply {e : OpenPartialHomeomorph N (EuclideanQuadrant k)} {p : M}
    (hp : p ∈ E.φ.source) : (E.chart e p).1 = consE ((E.φ p).1 - a) (e (E.φ p).2).1 := by
  simp only [chart, endChart, OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.prod_apply,
    OpenPartialHomeomorph.refl_apply, id]
  exact consQuad_apply (E.mem_target hp).1 _

/-- The extended product chart: `p ↦ (t − a, e(y))` in `ℝ^{k+1}`. -/
theorem chart_extend_apply {e : OpenPartialHomeomorph N (EuclideanQuadrant k)} {p : M}
    (hp : p ∈ E.φ.source) :
    (E.chart e).extend (𝓠 (k + 1)) p =
      consE ((E.φ p).1 - a) (e.extend (𝓠 k) (E.φ p).2) := by
  rw [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
    Function.comp_apply]
  exact E.chart_apply hp

/-- The point of the end with coordinates `(s, z)` in the product chart of `e`. -/
def pt (e : OpenPartialHomeomorph N (EuclideanQuadrant k)) (y : EuclideanSpace ℝ (Fin (k + 1))) :
    M :=
  E.φ.symm (y 0 + a, (e.extend (𝓠 k)).symm (tailE y))

theorem mem_chart_extend_target {e : OpenPartialHomeomorph N (EuclideanQuadrant k)}
    {y : EuclideanSpace ℝ (Fin (k + 1))} :
    y ∈ ((E.chart e).extend (𝓠 (k + 1))).target ↔
      y 0 ∈ Ioo 0 (b - a) ∧ tailE y ∈ (e.extend (𝓠 k)).target := by
  rw [OpenPartialHomeomorph.extend_target_eq_image_source,
    OpenPartialHomeomorph.extend_target_eq_image_source]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hp1, hp2⟩ := E.mem_chart_source.1 hp
    rw [E.chart_extend_apply hp1, consE_zero, tailE_consE]
    have ht := E.mem_target hp1
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, mem_image_of_mem _ hp2⟩
  · rintro ⟨hy0, w, hw, hwy⟩
    have hmem : (y 0 + a, w) ∈ E.φ.target := by
      rw [E.target_eq]; exact ⟨⟨by linarith [hy0.1], by linarith [hy0.2]⟩, mem_univ _⟩
    have hsrc := E.φ.map_target hmem
    have happ := E.φ.right_inv hmem
    refine ⟨E.φ.symm (y 0 + a, w), E.mem_chart_source.2 ⟨hsrc, by rw [happ]; exact hw⟩, ?_⟩
    rw [E.chart_extend_apply hsrc, happ, hwy]
    simp

theorem pt_mem {e : OpenPartialHomeomorph N (EuclideanQuadrant k)}
    {y : EuclideanSpace ℝ (Fin (k + 1))} (hy : y ∈ ((E.chart e).extend (𝓠 (k + 1))).target) :
    E.pt e y ∈ (E.chart e).source ∧
      E.φ (E.pt e y) = (y 0 + a, (e.extend (𝓠 k)).symm (tailE y)) := by
  obtain ⟨hy0, hy1⟩ := E.mem_chart_extend_target.1 hy
  have hmem : (y 0 + a, (e.extend (𝓠 k)).symm (tailE y)) ∈ E.φ.target := by
    rw [E.target_eq]; exact ⟨⟨by linarith [hy0.1], by linarith [hy0.2]⟩, mem_univ _⟩
  have hsrc := E.φ.map_target hmem
  have happ := E.φ.right_inv hmem
  refine ⟨E.mem_chart_source.2 ⟨hsrc, ?_⟩, happ⟩
  rw [pt, happ]
  have := (e.extend (𝓠 k)).map_target hy1
  rwa [e.extend_source] at this

/-- The inverse of the extended product chart: `(s, z) ↦ φ⁻¹(s + a, e⁻¹(z))`. -/
theorem chart_extend_symm {e : OpenPartialHomeomorph N (EuclideanQuadrant k)}
    {y : EuclideanSpace ℝ (Fin (k + 1))} (hy : y ∈ ((E.chart e).extend (𝓠 (k + 1))).target) :
    ((E.chart e).extend (𝓠 (k + 1))).symm y = E.pt e y := by
  obtain ⟨h1, h2⟩ := E.pt_mem hy
  obtain ⟨hy0, hy1⟩ := E.mem_chart_extend_target.1 hy
  have hext : (E.chart e).extend (𝓠 (k + 1)) (E.pt e y) = y := by
    rw [E.chart_extend_apply (E.mem_chart_source.1 h1).1, h2, add_sub_cancel_right,
      PartialEquiv.right_inv _ hy1, consE_tailE]
  rw [← hext, (E.chart e).extend_left_inv h1, hext]

/-! #### The product orientation and the integral over a product end -/

open ManifoldForm

variable (oM : TangentOrientation (𝓠 (k + 1)) M (k + 1)) (oN : TangentOrientation (𝓠 k) N k)

/-- **The product orientation `e ∧ o_N` on a product end** (the orientation of `S_F` on its ends
in the proof of 2021 Theorem 6.7.1, p. 278, the time direction `e = ∂ₜ` first): in each product
chart `(t − a, e(y))`, `e = chartAt y₀`, the orientation `o_M` reads as the standard orientation
of `ℝ^{k+1}` exactly where `o_N` reads as the standard orientation of `ℝ^k` in `e`. -/
def IsEndProductOrientation : Prop :=
  ∀ y₀ : N, ∀ x ∈ (E.chart (chartAt (EuclideanQuadrant k) y₀)).source,
    (orientationIn (E.chart (chartAt (EuclideanQuadrant k) y₀)) x (oM x) =
        stdOrientation (k + 1) ↔
      orientationIn (chartAt (EuclideanQuadrant k) y₀) (E.φ x).2 (oN (E.φ x).2) =
        stdOrientation k)

variable {E oM oN}

/-- On a product end with the product orientation, a product chart has the sign of the chart of
`N` it is made of. -/
theorem IsEndProductOrientation.orientationIn_eq (hor : E.IsEndProductOrientation oM oN)
    {y₀ : N} {x : M} (hx : x ∈ (E.chart (chartAt (EuclideanQuadrant k) y₀)).source) {b : Bool}
    (hb : orientationIn (chartAt (EuclideanQuadrant k) y₀) (E.φ x).2 (oN (E.φ x).2) =
      signedOr b (stdOrientation k)) :
    orientationIn (E.chart (chartAt (EuclideanQuadrant k) y₀)) x (oM x) =
      signedOr b (stdOrientation (k + 1)) := by
  cases b
  · rw [signedOr_false] at hb ⊢
    have h1 : orientationIn (E.chart (chartAt (EuclideanQuadrant k) y₀)) x (oM x) ≠
        stdOrientation (k + 1) := fun h =>
      Module.Ray.ne_neg_self (stdOrientation k) (((hor y₀ x hx).1 h).symm.trans hb)
    exact (Orientation.eq_or_eq_neg _ (stdOrientation (k + 1)) (by simp)).resolve_left h1
  · rw [signedOr_true] at hb ⊢
    exact (hor y₀ x hx).2 hb

/-- **The chart integral over a product chart** of an `(k+1)`-form whose coefficient is
`h(t)` times the coefficient of `ω` in `e`: `∫_{ê} Θ = (∫ₐᵇ h) · ∫_e ω`. -/
theorem chartIntegral_eq_mul {e : OpenPartialHomeomorph N (EuclideanQuadrant k)}
    {Θ : ManifoldForm (𝓠 (k + 1)) M (k + 1)} {ω : ManifoldForm (𝓠 k) N k} (h : ℝ → ℝ)
    (hprod : ∀ y ∈ ((E.chart e).extend (𝓠 (k + 1))).target,
      chartForm (𝓠 (k + 1)) (E.chart e) Θ y (stdFrame (k + 1)) =
        h (y 0 + a) * chartForm (𝓠 k) e ω (tailE y) (stdFrame k)) :
    chartIntegral (E.chart e) Θ = (∫ t in Ioo a b, h t) * chartIntegral e ω := by
  have hT : ((E.chart e).extend (𝓠 (k + 1))).target =
      {y | y 0 ∈ Ioo 0 (b - a) ∧ tailE y ∈ (e.extend (𝓠 k)).target} := by
    ext y; exact E.mem_chart_extend_target
  rw [chartIntegral, chartIntegral, topFormIntegral, topFormIntegral,
    setIntegral_congr_fun (measurableSet_extend_target _) hprod, hT, ← setIntegral_Ioo_add]
  exact setIntegral_consE_mul (Ioo 0 (b - a)) _ (fun s => h (s + a))
    (fun z => chartForm (𝓠 k) e ω z (stdFrame k))

variable [IsManifold (𝓠 k) ∞ N] [IsManifold (𝓠 (k + 1)) ∞ M] [T2Space N] [SigmaCompactSpace N]
  [T2Space M] [SigmaCompactSpace M]

/-- **Integration over a product end** (the end computation in the proof of 2021 Theorem 6.7.1,
p. 278; preprint Theorem 6.43): if a continuous `(k+1)`-form `Θ` with compact support in the
end `(a, b) × N` has, in the product charts, coefficient `h(t)` times the coefficient of a
continuous compactly supported `k`-form `ω` on `N`, and `M` carries the product orientation
`e ∧ o_N` on the end (`IsEndProductOrientation`), then `∫_M Θ = (∫ₐᵇ h) · ∫_N ω`.  For
`Θ = g′(t) dt ∧ p₁^*ω` this is `∫_{S_F} g′(t) dt ∧ p₁^*ω = (∫ g′) ∫_{S_i} ω`.  The text uses this
for `S_F`; here it is proved for an abstract product end, the product form of `Θ` being a
hypothesis on its coefficients. -/
theorem integral_end_fubini (hoM : oM.IsContinuous (𝓠 (k + 1)) ∞)
    (hoN : oN.IsContinuous (𝓠 k) ∞) (hor : E.IsEndProductOrientation oM oN)
    {Θ : ManifoldForm (𝓠 (k + 1)) M (k + 1)} (hΘ : ContMDiffForm (𝓠 (k + 1)) 0 Θ)
    (hΘc : IsCompact (ManifoldForm.tsupport Θ)) (hΘs : ManifoldForm.tsupport Θ ⊆ E.φ.source)
    {ω : ManifoldForm (𝓠 k) N k} (hω : ContMDiffForm (𝓠 k) 0 ω)
    (hωc : IsCompact (ManifoldForm.tsupport ω)) (h : ℝ → ℝ)
    (hprod : ∀ y₀ : N,
      ∀ y ∈ ((E.chart (chartAt (EuclideanQuadrant k) y₀)).extend (𝓠 (k + 1))).target,
        chartForm (𝓠 (k + 1)) (E.chart (chartAt (EuclideanQuadrant k) y₀)) Θ y
            (stdFrame (k + 1)) =
          h (y 0 + a) * chartForm (𝓠 k) (chartAt (EuclideanQuadrant k) y₀) ω (tailE y)
            (stdFrame k)) :
    ManifoldForm.integral oM Θ = (∫ t in Ioo a b, h t) * ManifoldForm.integral oN ω := by
  set pr : M → N := fun x => (E.φ x).2 with hpr_def
  have hpr : ContinuousOn pr E.φ.source := continuous_snd.comp_continuousOn E.φ.continuousOn
  have hsN : IsCompact (ManifoldForm.tsupport ω ∪ pr '' ManifoldForm.tsupport Θ) :=
    hωc.union (hΘc.image_of_continuousOn (hpr.mono hΘs))
  obtain ⟨T, ⟨D⟩⟩ := exists_integrationData hoN hsN
  set ρ' : {x // x ∈ T} → M → ℝ := fun j => E.φ.source.indicator fun x => D.ρ j (pr x)
    with hρ'
  have hρ'c : ∀ j, ContinuousOn (ρ' j) E.φ.source := fun j =>
    ((D.contMDiff_ρ j).continuous.comp_continuousOn hpr).congr fun x hx => indicator_of_mem hx _
  have hΘj : ∀ j, ContMDiffForm (𝓠 (k + 1)) 0 (smulFun (ρ' j) Θ) := fun j =>
    contMDiffForm_zero_smulFun_of_continuousOn E.φ.open_source (hρ'c j) hΘ hΘs
  set K : {x // x ∈ T} → Set M := fun j =>
    ManifoldForm.tsupport Θ ∩ pr ⁻¹' _root_.tsupport (D.ρ j) with hK_def
  have hKc : ∀ j, IsCompact (K j) := fun j => hΘc.of_isClosed_subset
    ((hpr.mono hΘs).preimage_isClosed_of_isClosed isClosed_closure (isClosed_tsupport _))
    inter_subset_left
  have hΘj0 : ∀ j, ∀ x ∉ K j, smulFun (ρ' j) Θ x = 0 := by
    intro j x hx
    rw [smulFun_apply]
    by_cases h1 : x ∈ ManifoldForm.tsupport Θ
    · simp only [hρ']
      rw [indicator_of_mem (hΘs h1), image_eq_zero_of_notMem_tsupport fun h2 => hx ⟨h1, h2⟩,
        zero_smul]
    · rw [eq_zero_of_notMem_tsupport h1, smul_zero]
  have hΘjc : ∀ j, IsCompact (ManifoldForm.tsupport (smulFun (ρ' j) Θ)) := fun j =>
    (hKc j).of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => by_contra fun h' => hx (hΘj0 j x h')) (hKc j).isClosed)
  have hsum : ∑ j, smulFun (ρ' j) Θ = Θ :=
    finsetSum_smulFun_eq_self Finset.univ (s := ManifoldForm.tsupport Θ) (fun x hx => by
      simp only [hρ', indicator_of_mem (hΘs hx)]
      exact D.sum_eq_one _ (Or.inr ⟨x, hx, rfl⟩)) subset_rfl
      (fun x hx => eq_zero_of_notMem_tsupport hx)
  rw [← hsum, integral_finsetSum hoM Finset.univ (fun j _ => hΘj j) (fun j _ => hΘjc j),
    integral_eq_integrationData hoN hω hωc D subset_union_left, IntegrationData.integral,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hb : ∀ x ∈ (E.chart (D.chart j)).source ∩ pr ⁻¹' D.region j,
      orientationIn (E.chart (D.chart j)) x (oM x) =
        signedOr (D.sign j) (stdOrientation (k + 1)) :=
    fun x hx => hor.orientationIn_eq hx.1 (D.orientationIn_eq j _ hx.2)
  have hKV : K j ⊆ (E.chart (D.chart j)).source ∩ pr ⁻¹' D.region j := fun x hx =>
    ⟨E.mem_chart_source.2 ⟨hΘs hx.1, D.region_subset j (D.tsupport_subset j hx.2)⟩,
      D.tsupport_subset j hx.2⟩
  rw [integral_eq_chartIntegral_of_mem_maximalAtlas hoM (hΘj j) (E.chart_mem (D.center j))
    inter_subset_left hb (hKc j) hKV (hΘj0 j), E.chartIntegral_eq_mul h (ω := smulFun (D.ρ j) ω)]
  · ring
  · intro y hy
    obtain ⟨h1, h2⟩ := E.pt_mem hy
    have hρy : ρ' j (((E.chart (D.chart j)).extend (𝓠 (k + 1))).symm y) =
        D.ρ j (((D.chart j).extend (𝓠 k)).symm (tailE y)) := by
      simp only [hρ']
      rw [E.chart_extend_symm hy, indicator_of_mem (E.mem_chart_source.1 h1).1]
      simp only [hpr_def, h2]
    rw [chartForm_smulFun, chartForm_smulFun, ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul, smul_eq_mul, hρy, hprod (D.center j) y hy]
    ring

end ProductEnd

end ProductEnd

/-! ### The model product end: the hypotheses are satisfiable -/

section ModelEnd

variable (k : ℕ) (a b : ℝ)

/-- **The model product end** `(0, b − a) × [0,∞)^k ⊆ [0,∞)^{k+1}`, identified with
`(a, b) × [0,∞)^k` by `q ↦ (q₀ + a, (q₁, …, q_k))`: the structure `ProductEnd` is
satisfiable. -/
def modelEnd : ProductEnd k (EuclideanQuadrant k) (EuclideanQuadrant (k + 1)) a b where
  φ := (consQuad a b).symm
  target_eq := rfl
  chart_mem x := by
    have h : endChart (consQuad (k := k) a b).symm a b (chartAt (EuclideanQuadrant k) x) =
        (consQuad a b).symm.trans (consQuad a b) := by
      rw [endChart, chartAt_self_eq, OpenPartialHomeomorph.refl_prod_refl,
        OpenPartialHomeomorph.trans_refl]
    rw [h]
    exact StructureGroupoid.mem_maximalAtlas_of_eqOnSource (consQuad a b).symm_trans_self
      (StructureGroupoid.mem_maximalAtlas_of_mem_groupoid _ (ofSet_mem_contDiffGroupoid _))

variable {k a b}

/-- The product charts of the model end are the identity on their sources. -/
theorem modelEnd_chart_apply (y₀ : EuclideanQuadrant k) {p : EuclideanQuadrant (k + 1)}
    (hp : p ∈ ((modelEnd k a b).chart (chartAt (EuclideanQuadrant k) y₀)).source) :
    (modelEnd k a b).chart (chartAt (EuclideanQuadrant k) y₀) p = p := by
  have hp' := ((modelEnd k a b).mem_chart_source.1 hp).1
  change consQuad a b (((OpenPartialHomeomorph.refl ℝ).prod (chartAt (EuclideanQuadrant k) y₀))
    ((consQuad a b).symm p)) = p
  rw [chartAt_self_eq, OpenPartialHomeomorph.refl_prod_refl, OpenPartialHomeomorph.refl_apply,
    id, (consQuad a b).right_inv hp']

/-- In the model space, a chart which is the identity on its source has derivative `id` relative
to the identity chart. -/
theorem chartChangeDeriv_refl_of_eqOn {e : OpenPartialHomeomorph (EuclideanQuadrant k)
    (EuclideanQuadrant k)} (he : ∀ p ∈ e.source, e p = p) {x : EuclideanQuadrant k}
    (hx : x ∈ e.source) :
    chartChangeDeriv (𝓠 k) (OpenPartialHomeomorph.refl _) e x = ContinuousLinearMap.id ℝ _ := by
  unfold chartChangeDeriv
  have hxI : (OpenPartialHomeomorph.refl (EuclideanQuadrant k)).extend (𝓠 k) x = 𝓠 k x := rfl
  rw [hxI, Filter.EventuallyEq.fderivWithin_eq (f := id), fderivWithin_id]
  · exact (𝓠 k).uniqueDiffWithinAt_image
  · have hU : (𝓠 k).symm ⁻¹' e.source ∈ 𝓝[range (𝓠 k)] (𝓠 k x) :=
      mem_nhdsWithin_of_mem_nhds ((e.open_source.preimage (𝓠 k).continuous_symm).mem_nhds
        (by rw [mem_preimage, (𝓠 k).left_inv]; exact hx))
    filter_upwards [hU, self_mem_nhdsWithin] with z hz hzI
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
      OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id]
    rw [he _ hz, (𝓠 k).right_inv hzI]
  · simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
      OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id,
      (𝓠 k).left_inv, he _ hx]

/-- **The standard orientations make the model end a product-oriented end**: the hypothesis
`IsEndProductOrientation` is satisfiable. -/
theorem modelEnd_isEndProductOrientation :
    (modelEnd k a b).IsEndProductOrientation
      (fun x => modelOrToTangent x (stdOrientation (k + 1)))
      (fun y => modelOrToTangent y (stdOrientation k)) := by
  intro y₀ x hx
  refine iff_of_true ?_ ?_
  · rw [orientationIn, chartAt_self_eq, chartChangeDeriv_refl_of_eqOn
      (fun p hp => modelEnd_chart_apply y₀ hp) hx]
    exact signMap_id _
  · rw [orientationIn, chartAt_self_eq, chartAt_self_eq,
      chartChangeDeriv_self (mem_univ _ : _ ∈ (OpenPartialHomeomorph.refl _).source)]
    exact signMap_id _

end ModelEnd

/-! ### The boundary of a product end -/

section EndBoundary

open ManifoldForm

variable {n : ℕ} {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanQuadrant (n + 1)) N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (n + 1 + 1)) M] {a b : ℝ}
  (E : ProductEnd (n + 1) N M a b)

/-- Chart targets have unique derivatives. -/
theorem uniqueDiffOn_extend_target {k : ℕ} {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X (EuclideanQuadrant k)) :
    UniqueDiffOn ℝ (e.extend (𝓠 k)).target := fun y hy => by
  have hx : (e.extend (𝓠 k)).symm y ∈ e.source := by
    rw [← e.extend_source (I := 𝓠 k)]; exact (e.extend (𝓠 k)).map_target hy
  have hT := e.extend_target_mem_nhdsWithin (I := 𝓠 k) hx
  rw [(e.extend (𝓠 k)).right_inv hy] at hT
  have := ((𝓠 k).uniqueDiffOn y (e.extend_target_subset_range hy)).inter' hT
  rwa [inter_eq_right.2 e.extend_target_subset_range] at this

variable [IsManifold (𝓠 (n + 1)) ∞ N] [IsManifold (𝓠 (n + 1 + 1)) ∞ M]

/-- **`d(h(t) dt ∧ β_N) = −h(t) dt ∧ dβ_N` on a product end**: the coefficient of `dβ` in a
product chart is `−h(t)` times the coefficient of `dβ_N`, if `β` reads as `h(t) dt ∧ β_N` in
that chart. -/
theorem ProductEnd.chartForm_extDeriv_stdFrame
    {e : OpenPartialHomeomorph N (EuclideanQuadrant (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓠 (n + 1)) ∞ N)
    (he' : E.chart e ∈ IsManifold.maximalAtlas (𝓠 (n + 1 + 1)) ∞ M)
    {β : ManifoldForm (𝓠 (n + 1 + 1)) M (n + 1)} (hβ : ContMDiffForm (𝓠 (n + 1 + 1)) 1 β)
    {βN : ManifoldForm (𝓠 (n + 1)) N n} (hβN : ContMDiffForm (𝓠 (n + 1)) 1 βN)
    {h : ℝ → ℝ} (hh : Differentiable ℝ h)
    (hprod : ∀ y ∈ ((E.chart e).extend (𝓠 (n + 1 + 1))).target,
      chartForm (𝓠 (n + 1 + 1)) (E.chart e) β y =
        h (y 0 + a) • dtWedge (chartForm (𝓠 (n + 1)) e βN (tailE y)))
    {y : EuclideanSpace ℝ (Fin (n + 1 + 1))}
    (hy : y ∈ ((E.chart e).extend (𝓠 (n + 1 + 1))).target) :
    chartForm (𝓠 (n + 1 + 1)) (E.chart e) (extDeriv β) y (stdFrame (n + 1 + 1)) =
      -h (y 0 + a) * chartForm (𝓠 (n + 1)) e (extDeriv βN) (tailE y) (stdFrame (n + 1)) := by
  have hT : MapsTo tailE ((E.chart e).extend (𝓠 (n + 1 + 1))).target
      (e.extend (𝓠 (n + 1))).target :=
    fun z hz => (E.mem_chart_extend_target.1 hz).2
  have hG : DifferentiableWithinAt ℝ (chartForm (𝓠 (n + 1)) e βN) (e.extend (𝓠 (n + 1))).target
      (tailE y) :=
    (hβN.contDiffOn_chartForm (by simp) he).differentiableOn one_ne_zero _ (hT hy)
  rw [chartForm_extDeriv_of_mem_target he' hβ hy, chartForm_extDeriv_of_mem_target he hβN (hT hy),
    extDerivWithin_dtWedge_stdFrame hy (uniqueDiffOn_extend_target _ _ hy) hT hprod (hh _) hG,
    neg_mul]

variable [T2Space N] [SigmaCompactSpace N] [T2Space M] [SigmaCompactSpace M]
  {oM : TangentOrientation (𝓠 (n + 1 + 1)) M (n + 1 + 1)}
  {oN : TangentOrientation (𝓠 (n + 1)) N (n + 1)}

/-- **The boundary of a product end carries `−(e ∧ o_{∂N})`** (reading R-f of the proof of
2021 Theorem 6.7.1, p. 278; preprint Theorem 6.43; boundary orientation of Definition 9.3.8,
p. 427: with outward normal first, `(a, b) × ∂N ⊆ ∂M` is oriented by
`−(e ∧ o_{∂N})`), as an identity of boundary integrals: for a `C¹` form `β` with compact support
in the end reading as `h(t) dt ∧ β_N` in the product charts,
`∫_{∂M} β = −(∫ₐᵇ h) · ∫_{∂N} β_N`.  Proved from `integral_end_fubini` for `dβ`
(`d(h dt ∧ β_N) = −h dt ∧ dβ_N`) and Stokes' theorem on `M` and on `N`.  The text uses the
sign in the boundary terms of the cobordism argument; here it is proved for an abstract product
end. -/
theorem ProductEnd.boundaryIntegral_end_sign (hoM : oM.IsContinuous (𝓠 (n + 1 + 1)) ∞)
    (hoN : oN.IsContinuous (𝓠 (n + 1)) ∞) (hor : E.IsEndProductOrientation oM oN)
    {β : ManifoldForm (𝓠 (n + 1 + 1)) M (n + 1)} (hβ : ContMDiffForm (𝓠 (n + 1 + 1)) 1 β)
    (hβc : IsCompact (ManifoldForm.tsupport β)) (hβs : ManifoldForm.tsupport β ⊆ E.φ.source)
    {βN : ManifoldForm (𝓠 (n + 1)) N n} (hβN : ContMDiffForm (𝓠 (n + 1)) 1 βN)
    (hβNc : IsCompact (ManifoldForm.tsupport βN)) {h : ℝ → ℝ} (hh : Differentiable ℝ h)
    (hprod : ∀ y₀ : N,
      ∀ y ∈ ((E.chart (chartAt (EuclideanQuadrant (n + 1)) y₀)).extend (𝓠 (n + 1 + 1))).target,
        chartForm (𝓠 (n + 1 + 1)) (E.chart (chartAt (EuclideanQuadrant (n + 1)) y₀)) β y =
          h (y 0 + a) •
            dtWedge (chartForm (𝓠 (n + 1)) (chartAt (EuclideanQuadrant (n + 1)) y₀) βN (tailE y))) :
    ManifoldForm.boundaryIntegral oM β =
      -(∫ t in Ioo a b, h t) * ManifoldForm.boundaryIntegral oN βN := by
  rw [← integral_extDeriv_eq_boundaryIntegral hoM hβ hβc,
    ← integral_extDeriv_eq_boundaryIntegral hoN hβN hβNc,
    E.integral_end_fubini hoM hoN hor (contMDiffForm_zero_extDeriv hβ)
      (hβc.of_isClosed_subset isClosed_closure (tsupport_extDeriv_subset β))
      ((tsupport_extDeriv_subset β).trans hβs) (contMDiffForm_zero_extDeriv hβN)
      (hβNc.of_isClosed_subset isClosed_closure (tsupport_extDeriv_subset βN)) (fun t => -h t)
      fun y₀ y hy => E.chartForm_extDeriv_stdFrame (IsManifold.chart_mem_maximalAtlas y₀)
        (E.chart_mem y₀) hβ hβN hh (hprod y₀) hy,
    MeasureTheory.integral_neg]

/-- **The face-form version** (for 3a-2: the boundary term `∫_{∂S} τ` of 2021 Theorem 6.7.1,
p. 277, on an end of `S_F`): for top-degree face data `σ` on `∂M` and `σ_N` on `∂N` with `C¹`
compactly supported extensions `β`, `β_N` as in `boundaryIntegral_end_sign`,
`∫_{∂M} σ = −(∫ₐᵇ h) · ∫_{∂N} σ_N`. -/
theorem ProductEnd.faceIntegral_end_sign (hoM : oM.IsContinuous (𝓠 (n + 1 + 1)) ∞)
    (hoN : oN.IsContinuous (𝓠 (n + 1)) ∞) (hor : E.IsEndProductOrientation oM oN)
    {β : ManifoldForm (𝓠 (n + 1 + 1)) M (n + 1)} (hβ : ContMDiffForm (𝓠 (n + 1 + 1)) 1 β)
    (hβc : IsCompact (ManifoldForm.tsupport β)) (hβs : ManifoldForm.tsupport β ⊆ E.φ.source)
    {σ : FaceFormData M (n + 1) (n + 1)} (hσ : IsExtendedBy σ β)
    {βN : ManifoldForm (𝓠 (n + 1)) N n} (hβN : ContMDiffForm (𝓠 (n + 1)) 1 βN)
    (hβNc : IsCompact (ManifoldForm.tsupport βN)) {σN : FaceFormData N n n}
    (hσN : IsExtendedBy σN βN) {h : ℝ → ℝ} (hh : Differentiable ℝ h)
    (hprod : ∀ y₀ : N,
      ∀ y ∈ ((E.chart (chartAt (EuclideanQuadrant (n + 1)) y₀)).extend (𝓠 (n + 1 + 1))).target,
        chartForm (𝓠 (n + 1 + 1)) (E.chart (chartAt (EuclideanQuadrant (n + 1)) y₀)) β y =
          h (y 0 + a) •
            dtWedge (chartForm (𝓠 (n + 1)) (chartAt (EuclideanQuadrant (n + 1)) y₀) βN (tailE y))) :
    faceIntegral oM σ = -(∫ t in Ioo a b, h t) * faceIntegral oN σN := by
  rw [faceIntegral_eq hoM hβ hβc hσ, faceIntegral_eq hoN hβN hβNc hσN]
  exact E.boundaryIntegral_end_sign hoM hoN hor hβ hβc hβs hβN hβNc hh hprod

/-- The face signs alternate: `faceSign (i + 1) = −faceSign i`.  The face `{y_{i+1} = 0}` of
`(a, b) × [0,∞)^{n+1}` is `(a, b)` times the face `{z_i = 0}` of `[0,∞)^{n+1}`, the time
coordinate first: the sign `−1` of reading R-f in the chart sums. -/
theorem faceSign_succ (i : Fin (n + 1)) : faceSign i.succ = -faceSign i := by
  rw [faceSign, faceSign, Fin.val_succ, pow_succ]
  ring

end EndBoundary

/-! ### The ends of the solution set `S_F` of the cobordism -/

section SolutionEnds

variable {n : ℕ} {X : Type*} {Y : Type*} {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})]

/-- **The zeros of a section of `π*P → ℝⁿ × X` over a set `A` of parameters on which its slices are
all `g`** form the product `A × S_g`. -/
theorem solutionSet_inter_fst_preimage_eq_prod
    {G : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hG : IsSection (pullbackProj P Prod.snd) G) {A : Set (Fin n → ℝ)} {g : X → Y}
    (hA : ∀ t ∈ A, pullbackSlice G t = g) :
    solutionSet (pullbackProj P Prod.snd) G ∩ Prod.fst ⁻¹' A = A ×ˢ solutionSet P g := by
  ext ⟨t, x⟩
  refine ⟨fun ⟨hz, ht⟩ => ⟨ht, ?_⟩, fun ⟨ht, hx⟩ => ⟨?_, ht⟩⟩
  · have := (isZeroAt_pullback_iff_pullbackSlice hG t x).1 hz
    rwa [hA t ht] at this
  · exact (isZeroAt_pullback_iff_pullbackSlice hG t x).2 (by rw [hA t ht]; exact hx)

namespace StrongBundle.IsCobordismData

variable [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle PX P} {f : X → Y} {hf : IsSection P f} {σ₀ σ₁ : X → Y}
  {Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}

/-- **The left end of `S_F`** (proof of 2021 Theorem 6.7.1, p. 278; Remark 6.6.19, p. 276):
over `t ≤ 1/8` the solution set of `F = f̃ + Ŝ` is `{t ≤ 1/8} × S_{f+σ₀}`. -/
theorem solutionSet_left_eq_prod (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) :
    solutionSet (pullbackProj P Prod.snd) (homotopySection f hf Ŝ) ∩ {z | z.1 0 ≤ 1 / 8} =
      {t : Fin 1 → ℝ | t 0 ≤ 1 / 8} ×ˢ solutionSet P (sectionAdd P f σ₀) :=
  solutionSet_inter_fst_preimage_eq_prod ((isSection_pullbackLift _).sectionAdd hC.isSection)
    fun _ ht => hC.pullbackSlice_le ht

/-- **The right end of `S_F`**: over `t ≥ 7/8` it is `{t ≥ 7/8} × S_{f+σ₁}`. -/
theorem solutionSet_right_eq_prod (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) :
    solutionSet (pullbackProj P Prod.snd) (homotopySection f hf Ŝ) ∩ {z | 7 / 8 ≤ z.1 0} =
      {t : Fin 1 → ℝ | 7 / 8 ≤ t 0} ×ˢ solutionSet P (sectionAdd P f σ₁) :=
  solutionSet_inter_fst_preimage_eq_prod ((isSection_pullbackLift _).sectionAdd hC.isSection)
    fun _ ht => hC.pullbackSlice_ge ht

/-- **The left end of a part of `S_F`** cut out by a condition `Q` on the `X`-component (for
`Q = {x | B.IsIndexAt f x k}`: the index part `{t ≤ 1/8} × (S_{f+σ₀})_k`). -/
theorem solutionSet_left_inter_eq_prod (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) (Q : Set X) :
    solutionSet (pullbackProj P Prod.snd) (homotopySection f hf Ŝ) ∩
        {z | z.1 0 ≤ 1 / 8 ∧ z.2 ∈ Q} =
      {t : Fin 1 → ℝ | t 0 ≤ 1 / 8} ×ˢ (solutionSet P (sectionAdd P f σ₀) ∩ Q) := by
  ext z
  have h := Set.ext_iff.1 hC.solutionSet_left_eq_prod z
  simp only [mem_inter_iff, mem_ofPred_eq, mem_prod] at h ⊢
  tauto

/-- **The right end of a part of `S_F`** cut out by a condition `Q` on the `X`-component. -/
theorem solutionSet_right_inter_eq_prod (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) (Q : Set X) :
    solutionSet (pullbackProj P Prod.snd) (homotopySection f hf Ŝ) ∩
        {z | 7 / 8 ≤ z.1 0 ∧ z.2 ∈ Q} =
      {t : Fin 1 → ℝ | 7 / 8 ≤ t 0} ×ˢ (solutionSet P (sectionAdd P f σ₁) ∩ Q) := by
  ext z
  have h := Set.ext_iff.1 hC.solutionSet_right_eq_prod z
  simp only [mem_inter_iff, mem_ofPred_eq, mem_prod] at h ⊢
  tauto

end StrongBundle.IsCobordismData

end SolutionEnds

end Polyfold
