import GWMemoir.LinearCRNodes

/-!
# The kernel of the linearized Cauchy–Riemann operator at a constant map from two spheres

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Proposition 4.23,
p. 118, level `0`, `a = 0`), at the constant map `u ≡ q` from `twoSpheres`.  The statements are
about sections: a section `η` of class `(3, δ₀)` with representative `v` whose form
`½(dη + J(q) ∘ dη ∘ j)` has representative `0`.

* **`holo_off_of_isFormRep_zero`** (any nodal surface, constant `u`): such an `η` is
  differentiable with `dη ∘ j = J(q) ∘ dη` off the nodal points.  On a disc core this is the
  argument of `projF_eq_zero_of_linOp`; on a neck core `v⁺ = η ∘ σ` is `C¹` (`neck_C1`), the
  form is `½(∂_s v⁺ + J(q) ∂_t v⁺)` (`formInPolar_projF`), which vanishes on `0 < t < 1` by
  continuity, and on `t = 0` by continuity of the derivative of the block rotated by `½`.
* **`eq_const_of_isFormRep_zero`** (`twoSpheres`): with matching values at the node, `η` is a
  constant `e` and `v = constBlocks e`; **`isFormRep_zero_iff`**: conversely constants qualify.
* **`kerN_eq_range`**, **`kerEquiv`**: the set `kerN` of such representatives is the image of
  the linear injection `constBlocksN : E →ₗ[ℝ] blocks`, so `E ≃ₗ[ℝ] kerN`.
* **Witness** `exists_sectionAtlas_twoSpheres`: an atlas of `twoSpheres` whose neck charts are
  `holChartInl/Inr`, whose inverses are differentiable (`NeckSmooth`).

The hypothesis `NeckSmooth A` (the inverses of the neck charts are differentiable) is used to
compute `dη` from `v⁺`; for `holChartInl/Inr` it is `neckSmooth_of_hol_twoSpheres`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 6. Sections whose `∂̄`-form has representative `0` -/

section Kernel

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {q : Q} {A : SectionAtlas (E := E) X (fun _ => q)}
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

variable (A) in
/-- The inverses of the neck charts are differentiable (true for `holChartInl/Inr`). -/
def NeckSmooth : Prop :=
  ∀ j, ∀ ζ ∈ (A.hol j).target, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) (A.hol j).symm ζ

/-- **The representatives determine the blocks**: two block tuples representing the same
section are equal. -/
lemma IsRep.unique' {η : Section E X} {v w : (blocks A δ h0 hmono) 0} (h : IsRep η v)
    (h' : IsRep η w) : v = w := by
  refine Prod.ext (funext fun ik => H_ext_ae ((h.1 ik.1 ik.2).trans (h'.1 ik.1 ik.2).symm))
    (funext fun jk => Prod.ext ((h.2 jk.1 jk.2).1.trans (h'.2 jk.1 jk.2).1.symm)
      (H_ext_ae (((h.2 jk.1 jk.2).2).trans ((h'.2 jk.1 jk.2).2).symm)))

/-- The point `(s, t)` is a limit of points with `0 < t < ½` when `t = 0`. -/
lemma mem_closure_neckU {j : Fin A.nn} {x : ℝ × ℝ} (hx : x ∈ neckU A j (1 / 2))
    (hx0 : x.2 = 0) : x ∈ closure (neckU A j (1 / 2) ∩ neckU A j 0) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨(x.1, min (ε / 2) (1 / 4)), ⟨⟨hx.1, ?_, ?_⟩, hx.1, ?_, ?_⟩, ?_⟩
  · have := lt_min (half_pos hε) (by norm_num : (0 : ℝ) < 1 / 4); linarith
  · have := min_le_right (ε / 2) (1 / 4); linarith
  · have := lt_min (half_pos hε) (by norm_num : (0 : ℝ) < 1 / 4); linarith
  · have := min_le_right (ε / 2) (1 / 4); linarith
  · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero, hx0, zero_sub, abs_neg,
      abs_of_pos (lt_min (half_pos hε) (by norm_num))]
    exact max_lt hε (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε))

variable (J : AlmostComplexStructure E Q)

/-- On `s > s₀`, `0 < t < 1`: if `projF J₀ dη` has neck representative `0`, then
`∂_t v⁺ = J₀ ∂_s v⁺`. -/
lemma neck_CR_of_isFormRep_zero (hsm : NeckSmooth A) {η : Section E X}
    (hc : IsContSection (fun _ => q) η) {v : (blocks A δ h0 hmono) 0} (hr : IsRep η v)
    (hD : IsFormRep (A := A) (δ := δ) (h0 := h0) (hmono := hmono)
      (projF (J.J q) (dForm η)) 0) (j : Fin A.nn) {Vs Vt : ℝ × ℝ → E}
    (hVs : ContinuousOn Vs (neckU A j 0)) (hVt : ContinuousOn Vt (neckU A j 0))
    (hV : ∀ x ∈ neckU A j 0, HasFDerivAt (vPolar A j η)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Vs x) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Vt x)) x) :
    ∀ x ∈ neckU A j 0, Vt x = J.J q (Vs x) := by
  set U := neckU A j 0
  have hU := isOpen_neckU (A := A) j 0
  have hfd : ∀ x ∈ U, fderiv ℝ (vPolar A j η) x (1, 0) = Vs x ∧
      fderiv ℝ (vPolar A j η) x (0, 1) = Vt x := fun x hx => by
    rw [(hV x hx).fderiv]; simp
  have hform : ∀ x ∈ U, X.formInPolar (fun _ => q) (projF (J.J q) (dForm η)) (A.hol j)
      (A.node j) x = (1 / 2 : ℝ) • (Vs x + J.J q (Vt x)) := by
    intro x hx
    have hp := (A.neck_chart j x hx.1.le).1
    have hd := (mdifferentiableAt_of_polar (A.isHol j) hp (hV x hx).differentiableAt).1
    rw [formInPolar_projF (A.isHol j) hp (hsm j _ hp) hd, ← (hfd x hx).1, ← (hfd x hx).2]
    rfl
  have hzero : ∀ k, ∀ x ∈ U, Real.smoothTransition (x.1 - A.s0 j) *
      crd k ((1 / 2 : ℝ) • (Vs x + J.J q (Vt x))) = 0 := by
    intro k
    have hae : formNeckRep A j k (projF (J.J q) (dForm η)) =ᵐ[cyl] 0 :=
      (hD.2 j k).symm.trans (val_zero_ae (k := 2) (hd := Neck.δ_nonneg δ h0 hmono 0))
    rw [cyl_eq_vol_restrict] at hae
    have hsub : U ⊆ univ ×ˢ Ioc 0 1 := fun x hx =>
      ⟨mem_univ _, by have := hx.2; constructor <;> linarith⟩
    have hae' := ae_restrict_of_ae_restrict_of_subset hsub hae
    have heqU : EqOn (formNeckRep A j k (projF (J.J q) (dForm η)))
        (fun x => Real.smoothTransition (x.1 - A.s0 j) *
          crd k ((1 / 2 : ℝ) • (Vs x + J.J q (Vt x)))) U := fun x hx => by
      simp only [formNeckRep, hform x hx]
    have hae2 : (fun x => Real.smoothTransition (x.1 - A.s0 j) *
        crd k ((1 / 2 : ℝ) • (Vs x + J.J q (Vt x)))) =ᵐ[volume.restrict U] 0 := by
      filter_upwards [hae', ae_restrict_mem hU.measurableSet] with x h1 h2
      exact (heqU h2).symm.trans h1
    have hcont : ContinuousOn (fun x => Real.smoothTransition (x.1 - A.s0 j) *
        crd k ((1 / 2 : ℝ) • (Vs x + J.J q (Vt x)))) U :=
      (Real.smoothTransition.continuous.comp (by fun_prop)).continuousOn.mul
        ((crd k).continuous_of_finiteDimensional.comp_continuousOn
          ((hVs.add ((J.J q).continuous.comp_continuousOn hVt)).const_smul _))
    exact Measure.eqOn_open_of_ae_eq hae2 hU hcont continuousOn_const
  intro x hx
  have hpos : 0 < Real.smoothTransition (x.1 - A.s0 j) :=
    Real.smoothTransition.pos_of_pos (by linarith [hx.1])
  have h0' : Vs x + J.J q (Vt x) = 0 := by
    refine (Module.finBasis ℝ E).ext_elem fun k => ?_
    have := hzero k x hx
    rw [map_smul, smul_eq_mul] at this
    have h2 : crd k (Vs x + J.J q (Vt x)) = 0 := by
      have := (mul_eq_zero.1 this).resolve_left hpos.ne'
      exact (mul_eq_zero.1 this).resolve_left (by norm_num)
    simpa using h2
  have := congrArg (J.J q) h0'
  rw [map_add, J.J_J, map_zero] at this
  exact (add_neg_eq_zero.1 this).symm

include J in
/-- **A section whose `projF J₀ dη` has representative `0` is holomorphic off the nodal
points**: on a disc core by `H³ ⊂ C¹` and continuity, on a neck core by the polar chain rule. -/
theorem holo_off_of_isFormRep_zero (hT : ChartsOnto X) (hsm : NeckSmooth A) {η : Section E X}
    (hc : IsContSection (fun _ => q) η) {v : (blocks A δ h0 hmono) 0} (hr : IsRep η v)
    (hD : IsFormRep (A := A) (δ := δ) (h0 := h0) (hmono := hmono)
      (projF (J.J q) (dForm η)) 0) (y : X.S) (hy : ∀ p ∈ X.nodes, y ∉ p) :
    MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E) η y ∧ ∀ w,
      mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η y (X.j.J y w) = J.J q (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) η y w) := by
  have hu : ∀ x, (fun _ : X.S => q) x = q := fun _ => rfl
  have hηc := continuous_of_isContSection hu hc
  rcases A.cover y with ⟨i, p₀, hp₀, rfl⟩ | ⟨j, hj | ⟨p, hp, rfl⟩⟩
  · -- a disc core
    have hp₀D : p₀ ∈ discD := mem_discD_of_core hp₀
    have D := fun k => (exists_discC1 hT hu hηc hr i k).some
    have hmd := (formDiscRep_dForm hT hu D hp₀D).1
    refine ⟨hmd, fun w => holo_of_projF (J := J) ?_ w⟩
    have hp2 : 1 / 4 ≤ p₀.2 ∧ p₀.2 ≤ 3 / 4 := by
      constructor <;> nlinarith [sq_nonneg p₀.1, sq_nonneg (p₀.2 - 1 / 4),
        sq_nonneg (p₀.2 - 3 / 4)]
    have hzero : formAt (fun _ => q) (A.center i) (projF (J.J q) (dForm η))
        (X.discPt (A.center i) (A.ε i) p₀) = 0 := by
      refine E2_ext fun d => ?_
      refine (Module.finBasis ℝ E).ext_elem fun k => ?_
      have hae : formDiscRep A i d k (projF (J.J q) (dForm η)) =ᵐ[cyl] 0 :=
        (hD.1 i d k).symm.trans (val_zero_ae (k := 2) (hd := Neck.δ_nonneg δ h0 hmono 0))
      have := eq_zero_of_ae_of_continuousAt (by linarith) (by linarith)
        (continuousAt_formDiscRep_projF hT hu D hηc (J.J q) hp₀D d k) hae
      rw [formDiscRep, discCut_eq_one hp₀, one_mul] at this
      simpa using this
    refine eq_zero_of_formAt (discPt_mem_source hT _ _ _) ?_ hzero
    exact mem_extChartAt_source q
  · -- the nodal point itself
    obtain ⟨a, ha, hja⟩ := A.node_nodal j
    exact absurd (hj ▸ hja) (hy a ha)
  · -- a neck core
    set n : ℤ := ⌊p.2⌋
    set p' : ℝ × ℝ := (p.1, p.2 - n)
    have hpp : X.polar (A.hol j) p = X.polar (A.hol j) p' := by
      have := polar_add_int (A.hol j) p.1 (p.2 - n) n
      rw [sub_add_cancel] at this
      exact this
    have ht0 : 0 ≤ p'.2 := sub_nonneg.2 (Int.floor_le p.2)
    have ht1 : p'.2 < 1 := by
      have := Int.lt_floor_add_one p.2; simp only [p']; linarith
    have hs : A.s0 j < p'.1 := by simp only [p']; linarith
    obtain ⟨Vs, Vt, hVs, hVt, hV⟩ := neck_C1 hc hr j 0
    have hCR0 := neck_CR_of_isFormRep_zero J hsm hc hr hD j hVs hVt hV
    -- `∂_t v⁺ = J₀ ∂_s v⁺` and differentiability at `p'`
    have key : DifferentiableAt ℝ (vPolar A j η) p' ∧
        fderiv ℝ (vPolar A j η) p' (0, 1) = J.J q (fderiv ℝ (vPolar A j η) p' (1, 0)) := by
      by_cases hlt : 0 < p'.2
      · have hx : p' ∈ neckU A j 0 := ⟨hs, by simpa using hlt, by simpa using ht1⟩
        refine ⟨(hV p' hx).differentiableAt, ?_⟩
        rw [(hV p' hx).fderiv]; simpa using hCR0 p' hx
      · have h0 : p'.2 = 0 := le_antisymm (not_lt.1 hlt) ht0
        obtain ⟨Vs', Vt', hVs', hVt', hV'⟩ := neck_C1 hc hr j (1 / 2)
        have hx : p' ∈ neckU A j (1 / 2) := ⟨hs, by rw [h0]; norm_num, by rw [h0]; norm_num⟩
        refine ⟨(hV' p' hx).differentiableAt, ?_⟩
        rw [(hV' p' hx).fderiv]
        simp only [add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
          ContinuousLinearMap.coe_snd', one_smul, zero_smul, add_zero, zero_add]
        -- `Vt' - J₀ Vs'` vanishes on the points with `0 < t < ½` and is continuous
        set F : ℝ × ℝ → E := fun x => Vt' x - J.J q (Vs' x)
        have hF : ContinuousOn F (neckU A j (1 / 2)) :=
          hVt'.sub ((J.J q).continuous.comp_continuousOn hVs')
        have hFS : ∀ x ∈ neckU A j (1 / 2) ∩ neckU A j 0, F x = 0 := by
          intro x hx
          have e1 := (hV' x hx.1).fderiv
          have e2 := (hV x hx.2).fderiv
          have hs' : Vs' x = Vs x := by
            have := congrArg (fun L => L (1, 0)) (e1.symm.trans e2); simpa using this
          have ht' : Vt' x = Vt x := by
            have := congrArg (fun L => L (0, 1)) (e1.symm.trans e2); simpa using this
          simp only [F, hs', ht', hCR0 x hx.2, sub_self]
        have hcl := mem_closure_neckU hx h0
        have hNe : (𝓝[neckU A j (1 / 2) ∩ neckU A j 0] p').NeBot :=
          mem_closure_iff_nhdsWithin_neBot.1 hcl
        have hT1 : Tendsto F (𝓝[neckU A j (1 / 2) ∩ neckU A j 0] p') (𝓝 (F p')) :=
          ((hF p' hx).mono inter_subset_left).tendsto
        have hT2 : Tendsto F (𝓝[neckU A j (1 / 2) ∩ neckU A j 0] p') (𝓝 0) :=
          tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx => (hFS x hx).symm)
        exact sub_eq_zero.1 (tendsto_nhds_unique hT1 hT2)
    have hp' := (A.neck_chart j p' hs.le).1
    rw [hpp]
    exact ⟨(mdifferentiableAt_of_polar (A.isHol j) hp' key.1).1,
      holo_of_polar (A.isHol j) hp' key.1 (J.J q) (J.J_J q) key.2⟩

end Kernel

/-! ## 7. On `twoSpheres` -/

section TwoSpheres

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

theorem twoSpheres_chartsOnto : ChartsOnto twoSpheres := twoSpheres_target

/-- **`Dη = 0` forces `η` constant** (Memoir §4, Proposition 4.23, `a = 0`): a continuous
section with matching values at the node, representative `v`, and `projF J(q) dη` of
representative `0` is a constant `e`, and `v = constBlocks e`. -/
theorem eq_const_of_isFormRep_zero (hsm : NeckSmooth A) {η : Section E twoSpheres}
    (hc : IsContSection (fun _ => q) η) (hm : IsMatchingSection twoSpheres η)
    {v : (blocks A δ h0 hmono) 0} (hr : IsRep η v)
    (hD : IsFormRep (A := A) (δ := δ) (h0 := h0) (hmono := hmono)
      (projF (J.J q) (dForm η)) 0) :
    η = (fun _ => η (Sum.inl (pt 2))) ∧ v = constBlocks A δ h0 hmono (η (Sum.inl (pt 2))) := by
  have hu : ∀ x, (fun _ : twoSpheres.S => q) x = q := fun _ => rfl
  have hηc := continuous_of_isContSection hu hc
  have H := fun y hy => holo_off_of_isFormRep_zero J twoSpheres_chartsOnto hsm hc hr hD y hy
  have hconst : η = fun _ => η (Sum.inl (pt 2)) :=
    funext (eq_const_of_holo_twoSpheres hηc (J.J q) (J.J_J q) (fun y hy => (H y hy).1)
      (fun y hy => (H y hy).2) hm)
  exact ⟨hconst, IsRep.unique' (hconst ▸ hr) (isRep_constBlocks A _)⟩

/-- The constants are in the kernel: `dη = 0`. -/
theorem isFormRep_zero_iff (hsm : NeckSmooth A) {η : Section E twoSpheres}
    (hc : IsContSection (fun _ => q) η) (hm : IsMatchingSection twoSpheres η)
    {v : (blocks A δ h0 hmono) 0} (hr : IsRep η v) :
    IsFormRep (A := A) (δ := δ) (h0 := h0) (hmono := hmono) (projF (J.J q) (dForm η)) 0 ↔
      ∃ e : E, η = fun _ => e := by
  refine ⟨fun hD => ⟨_, (eq_const_of_isFormRep_zero J hsm hc hm hr hD).1⟩, ?_⟩
  rintro ⟨e, rfl⟩
  rw [dForm_const, projF_zero]
  exact isFormRep_zero

variable (A δ h0 hmono) in
/-- The constant blocks as a linear map `E →ₗ[ℝ] blocks` (on any nodal surface the blocks of
`η ≡ e` are `(bump·e_k(e))` on the discs and `(e_k(e), 0)` on the necks). -/
def constBlocksN : E →ₗ[ℝ] (blocks A δ h0 hmono) 0 where
  toFun := constBlocks A δ h0 hmono
  map_add' e e' := by
    have h := (isRep_constBlocks (δ := δ) (h0 := h0) (hmono := hmono) A e).add
      (isRep_constBlocks (δ := δ) (h0 := h0) (hmono := hmono) A e')
    exact IsRep.unique' (isRep_constBlocks A (e + e')) h
  map_smul' c e := by
    have h := (isRep_constBlocks (δ := δ) (h0 := h0) (hmono := hmono) A e).smul c
    exact IsRep.unique' (isRep_constBlocks A (c • e)) h

/-- On `twoSpheres` the constant blocks are distinct: the constant `e_k(e)` of a neck block
recovers `e`. -/
theorem constBlocksN_injective : Injective (constBlocksN A δ h0 hmono) := by
  intro e e' h
  obtain ⟨p, hp⟩ := twoSpheres_nodes_nonempty
  obtain ⟨j, -⟩ := A.nodal_node p hp _ (Sym2.out_fst_mem p)
  refine (Module.finBasis ℝ E).ext_elem fun k => ?_
  have := congrArg (fun w : (blocks A δ h0 hmono) 0 => (w.2 (j, k)).1) h
  exact this

variable (A δ h0 hmono) in
/-- The representatives `v` of continuous matching sections `η` with `projF J(q) dη`
of representative `0`. -/
def kerN : Set ((blocks A δ h0 hmono) 0) :=
  {v | ∃ η : Section E twoSpheres, IsContSection (fun _ => q) η ∧
    IsMatchingSection twoSpheres η ∧ IsRep η v ∧
    IsFormRep (A := A) (δ := δ) (h0 := h0) (hmono := hmono) (projF (J.J q) (dForm η)) 0}

/-- **The kernel is the constants** (Memoir §4, Proposition 4.23, `a = 0`). -/
theorem kerN_eq_range (hsm : NeckSmooth A) :
    kerN J A δ h0 hmono = LinearMap.range (constBlocksN A δ h0 hmono) := by
  ext v
  constructor
  · rintro ⟨η, hc, hm, hr, hD⟩
    exact ⟨_, ((eq_const_of_isFormRep_zero J hsm hc hm hr hD).2).symm⟩
  · rintro ⟨e, rfl⟩
    have hu : ∀ x, (fun _ : twoSpheres.S => q) x = q := fun _ => rfl
    refine ⟨fun _ => e, isContSection_of_const hu continuous_const, fun _ _ _ => rfl,
      isRep_constBlocks A e, ?_⟩
    rw [dForm_const, projF_zero]
    exact isFormRep_zero

/-- **The kernel is a copy of `E = T_qQ`**: `E ≃ₗ[ℝ] range constBlocksN`, and the range is
`kerN` (`kerN_eq_range`). -/
def kerEquiv : E ≃ₗ[ℝ] LinearMap.range (constBlocksN A δ h0 hmono) :=
  LinearEquiv.ofInjective _ constBlocksN_injective

/-! ## 8. Witness -/

variable {Q' : Type} [TopologicalSpace Q'] [ChartedSpace E Q'] [IsManifold 𝓘(ℝ, E) ∞ Q']

section Witness

variable {m : ℕ} (X : NodalSurface m)

open NodalSurface in
/-- A copy of `exists_sectionAtlas_of_hol` with the holomorphic charts at the nodal points
prescribed: `A.hol j = φ₀ (A.node j)`. -/
theorem exists_sectionAtlas_of_holChart (u : X.S → Q') (hu : Continuous u)
    (φ₀ : X.S → OpenPartialHomeomorph X.S ℂ) (hφ₀ : ∀ x ∈ X.nodalPts, X.IsHolChart (φ₀ x) x) :
    ∃ A : SectionAtlas (E := E) X u, ∀ j, A.hol j = φ₀ (A.node j) := by
  have hN := X.finite_nodalPts
  have hNc : IsClosed X.nodalPts := hN.isClosed
  have := hN.fintype
  set φ : X.nodalPts → OpenPartialHomeomorph X.S ℂ := fun x => φ₀ x.1
  have hφ : ∀ x : X.nodalPts, X.IsHolChart (φ x) x := fun x => hφ₀ x.1 x.2
  choose s0 hs0 using fun x : X.nodalPts => exists_neck_s0 (E := E) hu (hφ x)
  -- the small discs around the nodal points
  set O : X.nodalPts → Set X.S := fun x =>
    (φ x).source ∩ φ x ⁻¹' Metric.ball 0 (Real.exp (-2 * Real.pi * (s0 x + 1)))
  have hOo : ∀ x, IsOpen (O x) := fun x => (φ x).isOpen_inter_preimage Metric.isOpen_ball
  have hxO : ∀ x, x.1 ∈ O x := fun x =>
    ⟨(hφ x).1, by rw [mem_preimage, (hφ x).2.1]; exact Metric.mem_ball_self (Real.exp_pos _)⟩
  set K : Set X.S := (⋃ x, O x)ᶜ
  have hK : IsCompact K := (isOpen_iUnion hOo).isClosed_compl.isCompact
  have hKN : ∀ z ∈ K, z ∉ X.nodalPts := fun z hz hzN =>
    hz (mem_iUnion.2 ⟨⟨z, hzN⟩, hxO ⟨z, hzN⟩⟩)
  set e := Fintype.equivFin X.nodalPts
  -- the disc charts away from the nodal points
  have hW : ∀ z : X.S, z ∉ X.nodalPts → ∃ ε > 0, ∀ w ∈ Metric.ball (extChartAt 𝓘(ℝ, E2) z z) ε,
      w ∈ (extChartAt 𝓘(ℝ, E2) z).target ∧
        u ((extChartAt 𝓘(ℝ, E2) z).symm w) ∈ (extChartAt 𝓘(ℝ, E) (u z)).source ∧
        (extChartAt 𝓘(ℝ, E2) z).symm w ∉ X.nodalPts := by
    intro z hz
    have h1 : (extChartAt 𝓘(ℝ, E2) z).target ∈ 𝓝 (extChartAt 𝓘(ℝ, E2) z z) :=
      extChartAt_target_mem_nhds z
    have hsc : ContinuousAt (extChartAt 𝓘(ℝ, E2) z).symm (extChartAt 𝓘(ℝ, E2) z z) :=
      continuousAt_extChartAt_symm z
    have h2 : (fun w => u ((extChartAt 𝓘(ℝ, E2) z).symm w)) ⁻¹' (extChartAt 𝓘(ℝ, E) (u z)).source
        ∈ 𝓝 (extChartAt 𝓘(ℝ, E2) z z) := by
      refine (hu.continuousAt.comp hsc).preimage_mem_nhds ?_
      rw [Function.comp_apply, extChartAt_to_inv]
      exact extChartAt_source_mem_nhds (u z)
    have h3 : (extChartAt 𝓘(ℝ, E2) z).symm ⁻¹' X.nodalPtsᶜ ∈ 𝓝 (extChartAt 𝓘(ℝ, E2) z z) := by
      refine hsc.preimage_mem_nhds ?_
      rw [extChartAt_to_inv]
      exact hNc.isOpen_compl.mem_nhds hz
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem (inter_mem h1 h2) h3)
    exact ⟨ε, hε, fun w hw => ⟨(hball hw).1.1, (hball hw).1.2, (hball hw).2⟩⟩
  choose! ε hε hball using hW
  set U : X.S → Set X.S := fun z => (extChartAt 𝓘(ℝ, E2) z).source ∩
    (extChartAt 𝓘(ℝ, E2) z) ⁻¹' Metric.ball (extChartAt 𝓘(ℝ, E2) z z) (ε z / 4) with hU
  have hUo : ∀ z, IsOpen (U z) := fun z =>
    (continuousOn_extChartAt z).isOpen_inter_preimage (isOpen_extChartAt_source z)
      Metric.isOpen_ball
  have hUz : ∀ z ∈ K, z ∈ U z := fun z hz =>
    ⟨mem_extChartAt_source z, Metric.mem_ball_self (by linarith [hε z (hKN z hz)])⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => U z) (fun z => hUo z)
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hUz y hy⟩)
  have hplace : ∀ z (p : ℝ × ℝ), 0 < ε z → p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 < 1 / 8 →
      X.place z (ε z) p ∈ Metric.ball (extChartAt 𝓘(ℝ, E2) z z) (ε z) := by
    intro z p hεz hp
    rw [Metric.mem_ball, NodalSurface.place, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hεz.le]
    have hn :
        ‖EuclideanSpace.single (0 : Fin 2) p.1 + EuclideanSpace.single 1 (p.2 - 1 / 2)‖ < 1 := by
      have := norm_sq_single_add_single p.1 (p.2 - 1 / 2)
      nlinarith [norm_nonneg (EuclideanSpace.single (0 : Fin 2) p.1 +
        EuclideanSpace.single 1 (p.2 - 1 / 2))]
    nlinarith
  have hcK : ∀ i : Fin t.card, (t.equivFin.symm i).1.1 ∉ X.nodalPts := fun i =>
    hKN _ (t.equivFin.symm i).1.2
  refine ⟨{
    nd := t.card
    center := fun i => (t.equivFin.symm i).1.1
    ε := fun i => ε (t.equivFin.symm i).1.1
    ε_pos := fun i => hε _ (hcK i)
    disc_chart := fun i p hp =>
      ⟨(hball _ (hcK i) _ (hplace _ p (hε _ (hcK i)) hp)).1,
        (hball _ (hcK i) _ (hplace _ p (hε _ (hcK i)) hp)).2.1⟩
    disc_avoid := fun i p hp q hq hmem =>
      (hball _ (hcK i) _ (hplace _ p (hε _ (hcK i)) hp)).2.2 ⟨q, hq, hmem⟩
    nn := Fintype.card X.nodalPts
    node := fun j => (e.symm j).1
    hol := fun j => φ (e.symm j)
    s0 := fun j => s0 (e.symm j)
    isHol := fun j => hφ (e.symm j)
    neck_chart := fun j => hs0 (e.symm j)
    node_nodal := fun j => (e.symm j).2
    nodal_node := fun q hq x hx => ⟨e ⟨x, q, hq, hx⟩, by simp⟩
    cover := fun y => ?_ }, fun j => rfl⟩
  by_cases hyK : y ∈ K
  · left
    obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.1 (ht hyK)
    obtain ⟨hys, hyb⟩ := hyz
    refine ⟨t.equivFin ⟨z, hzt⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    have hεz := hε z.1 (hKN z.1 z.2)
    set w : E2 := (ε z.1)⁻¹ • (extChartAt 𝓘(ℝ, E2) z.1 y - extChartAt 𝓘(ℝ, E2) z.1 z.1) with hw
    have hwn : ‖w‖ < 1 / 4 := by
      rw [hw, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hεz.le), ← dist_eq_norm]
      rw [mem_preimage, Metric.mem_ball] at hyb
      rw [inv_mul_lt_iff₀ hεz]; linarith
    refine ⟨(w 0, w 1 + 1 / 2), ?_, ?_⟩
    · have h := norm_sq_single_add_single (w 0) (w 1)
      rw [single_add_single_eq] at h
      simp only [add_sub_cancel_right]
      nlinarith [norm_nonneg w]
    · have hpl : X.place z.1 (ε z.1) (w 0, w 1 + 1 / 2) = extChartAt 𝓘(ℝ, E2) z.1 y := by
        rw [NodalSurface.place]
        simp only [add_sub_cancel_right]
        rw [single_add_single_eq, hw, smul_smul, mul_inv_cancel₀ hεz.ne', one_smul,
          add_sub_cancel]
      rw [NodalSurface.discPt, hpl, (extChartAt 𝓘(ℝ, E2) z.1).left_inv hys]
  · right
    obtain ⟨x, hyO⟩ := mem_iUnion.1 (not_not.1 hyK)
    refine ⟨e x, ?_⟩
    simp only [Equiv.symm_apply_apply]
    obtain ⟨hys, hyb⟩ := hyO
    rw [mem_preimage, mem_ball_zero_iff] at hyb
    rcases eq_or_polar_of_small (hφ x) _ hys hyb with h | ⟨p, hp, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, hp.le, h⟩

end Witness

/-- The inverses of `holChartInl/Inr` are smooth. -/
theorem mdifferentiableAt_holChartInl_symm (ζ : ℂ) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) holChartInl.symm ζ := by
  rw [holChartInl, OpenPartialHomeomorph.lift_openEmbedding_symm]
  exact ((ContMDiff.inl (I := 𝓘(ℝ, E2)) (M := S2) (M' := S2) (n := ∞)).mdifferentiable
    (by simp) _).comp ζ (mdifferentiable_holChart_symm (-1) (by norm_num) ζ)

theorem mdifferentiableAt_holChartInr_symm (ζ : ℂ) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E2) holChartInr.symm ζ := by
  rw [holChartInr, OpenPartialHomeomorph.lift_openEmbedding_symm]
  exact ((ContMDiff.inr (I := 𝓘(ℝ, E2)) (M := S2) (M' := S2) (n := ∞)).mdifferentiable
    (by simp) _).comp ζ (mdifferentiable_holChart_symm (-1) (by norm_num) ζ)

/-- The chart `holChartInl` on the first sphere and `holChartInr` on the second. -/
def holTwo (x : S22) : OpenPartialHomeomorph S22 ℂ :=
  Sum.elim (fun _ => holChartInl) (fun _ => holChartInr) x

/-- **Witness**: `twoSpheres` has, for every `q`, an atlas with differentiable neck chart
inverses, so the hypotheses of `eq_const_of_isFormRep_zero` hold. -/
theorem exists_sectionAtlas_twoSpheres (q : Q) :
    ∃ A : SectionAtlas (E := E) twoSpheres (fun _ => q), NeckSmooth A := by
  have hmem : ∀ x ∈ twoSpheres.nodalPts, x = Sum.inl (pt 2) ∨ x = Sum.inr (pt 2) := by
    rintro x ⟨p, hp, hx⟩
    by_contra h
    simp only [not_or] at h
    exact ((twoSpheres_offNode_iff x).2 h) p hp hx
  obtain ⟨A, hA⟩ := exists_sectionAtlas_of_holChart (E := E) twoSpheres (fun _ => q)
    continuous_const holTwo fun x hx => by
      rcases hmem x hx with rfl | rfl
      · exact isHolChart_inl
      · exact isHolChart_inr
  refine ⟨A, fun j ζ _ => ?_⟩
  rw [hA j]
  generalize A.node j = y
  rcases y with y | y
  · exact mdifferentiableAt_holChartInl_symm ζ
  · exact mdifferentiableAt_holChartInr_symm ζ

end TwoSpheres

end GWMemoir
