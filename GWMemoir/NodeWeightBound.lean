import GWMemoir.NeckTestForms
import GWMemoir.CokernelNodes

/-!
# `D` is not onto for `δ₀ ≥ 2π` at a constant map from two spheres

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Proposition 4.23,
p. 118, level `0`, `a = 0`), at the constant map `u ≡ q` from two spheres joined at a node
(`twoSpheres`), with the standard neck charts (`IsStdNeck`).

* `lowerBlocks`: the blocks of weight `δ₀` are blocks of every smaller weight `δ'₀`
  (`inclH`), with the same representatives (`IsRep.lower`).
* `neckFE`, **`isTest_neckFE`**: `β(s - s₀) e_k*(½ (∂_s V + J₀ ∂_t V))` is a test function when
  `V` is smooth, periodic in `t`, and `∂_t V = J₀ ∂_s V` for `s > 0`; **`formNeckRep_projF_eq`**:
  for a smooth section `ξ` it is the neck representative of `½ (dξ + J₀ dξ j)`, `V = ξ ∘ σ`.
* **`exists_isFormRep_exSection`**: for every weight `δ₀`, the form `η = ½ (dξ + J₀ dξ j)` of
  the section `ξ = χ(z) z·e` of §4 has its representatives in the fibre blocks: `η` vanishes near
  the node, its neck blocks are test functions, and its disc blocks are those of weight `0` cut
  off by `chiP` (`ChartChange.op` with `ψ = id`).
* **`isRep_add_const_of_linOpN`** (the regularity at the node): if `w ∈ H^{3,δ₀}_c` and `D w`
  represents `½ (dξ + J(q) dξ j)` for a smooth section `ξ` with matching values at the node, then
  `w` is represented by `ξ` plus a constant.  Lowered to the weight `δ'₀ = 0` (`lowerBlocks`),
  `ξ` has blocks (`smoothBlocks2`), and `w - ξ` has `D = 0`, hence is constant
  (`eq_const_of_isFormRep_zero`).  `exSection_eq_of_linOpN`: the case `ξ = χ(z) z·e`.
* **`not_surjective_linCRN_of_two_pi_le`**: for `δ₀ ≥ 2π`, `D` is not onto: `ξ + c` is not in
  `H^{3,δ₀}_c` (`not_mem_sectionSpace_of_two_pi_le`).
  **`not_surjective_linCRN_twoSpheres_uncond`**: the existence form;
  **`linCRN_onto_dichotomy_twoSpheres`**: onto for `0 < δ₀ < 2π`
  (`linCRN_isFredholm_twoSpheres_uncond`), not onto for `δ₀ ≥ 2π`;
  **`linCRN_surjective_iff_twoSpheres`**: on one atlas with gluing data, for all `δ₀ > 0`,
  `D` is onto exactly when `δ₀ < 2π`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. Lowering the weight of the section blocks -/

section Lower

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {m : ℕ} {X : NodalSurface m} {u : X.S → Q} {A : SectionAtlas (E := E) X u}
  {δ δ' : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ} {h0' : 0 ≤ δ' 0}
  {hmono' : StrictMono δ'}

variable (h0' hmono') in
/-- The blocks of weight `δ₀` as blocks of a smaller weight `δ'₀`. -/
def lowerBlocks (hle : δ' 0 ≤ δ 0) (w : (blocks A δ h0 hmono) 0) :
    (blocks A δ' h0' hmono') 0 :=
  (fun ik => inclH (Neck.δ_nonneg δ' h0' hmono' 0) (Neck.δ_nonneg δ h0 hmono 0) le_rfl hle
      (w.1 ik),
    fun jk => ((w.2 jk).1, inclH (Neck.δ_nonneg δ' h0' hmono' 0) (Neck.δ_nonneg δ h0 hmono 0)
      le_rfl hle (w.2 jk).2))

/-- Lowering the weight keeps the representatives. -/
theorem IsRep.lower (hle : δ' 0 ≤ δ 0) {η : Section E X} {w : (blocks A δ h0 hmono) 0}
    (h : IsRep η w) : IsRep η (lowerBlocks h0' hmono' hle w) :=
  ⟨fun i k => h.1 i k, fun j k => h.2 j k⟩

end Lower

/-! ## 2. The neck test functions -/

section NeckF

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `β(s - s₀) · e_k*(½ (∂_s V + J₀ ∂_t V))`. -/
def neckFE (J₀ : E →L[ℝ] E) (V : ℝ × ℝ → E) (s₀ : ℝ) (k : Fin (Module.finrank ℝ E))
    (p : ℝ × ℝ) : ℝ :=
  Real.smoothTransition (p.1 - s₀) *
    crd k ((1 / 2 : ℝ) • (fderiv ℝ V p (1, 0) + J₀ (fderiv ℝ V p (0, 1))))

lemma fderiv_add_zero_one {V : ℝ × ℝ → E} (hp : ∀ s t, V (s, t + 1) = V (s, t)) (x : ℝ × ℝ) :
    fderiv ℝ V (x + (0, 1)) = fderiv ℝ V x := by
  have : (fun y => V (y + ((0 : ℝ), (1 : ℝ)))) = V := by
    funext y; obtain ⟨s, t⟩ := y; simpa using hp s t
  rw [← fderiv_comp_add_right, this]

/-- **The neck test functions**: for `V` smooth, periodic in `t`, with `∂_t V = J₀ ∂_s V` for
`s > 0`, the function `β(s - s₀) e_k*(½ (∂_s V + J₀ ∂_t V))` is a test function. -/
theorem isTest_neckFE {J₀ : E →L[ℝ] E} (hJ : ∀ v, J₀ (J₀ v) = -v) {V : ℝ × ℝ → E}
    (hV : ContDiff ℝ ∞ V) (hper : ∀ s t, V (s, t + 1) = V (s, t))
    (hCR : ∀ p : ℝ × ℝ, 0 < p.1 → fderiv ℝ V p (0, 1) = J₀ (fderiv ℝ V p (1, 0)))
    (s₀ : ℝ) (k : Fin (Module.finrank ℝ E)) : IsTest (neckFE J₀ V s₀ k) where
  smooth := by
    have hd : ContDiff ℝ ∞ (fderiv ℝ V) := hV.fderiv_right (m := ∞) le_rfl
    exact (Real.smoothTransition.contDiff.comp (contDiff_fst.sub contDiff_const)).mul
      ((crdL k).contDiff.comp (contDiff_const.smul ((hd.clm_apply contDiff_const).add
        (J₀.contDiff.comp (hd.clm_apply contDiff_const)))))
  periodic s t := by
    have := fderiv_add_zero_one hper (s, t)
    simp only [Prod.mk_add_mk, add_zero] at this
    simp only [neckFE, this]
  bddSupp := ⟨|s₀|, fun s t hs => by
    simp only [neckFE]
    rcases le_or_gt s 0 with h | h
    · rw [abs_of_nonpos h] at hs
      rw [Real.smoothTransition.zero_of_nonpos (by linarith [neg_abs_le s₀]), zero_mul]
    · rw [hCR (s, t) h, hJ, add_neg_cancel, smul_zero, map_zero, mul_zero]⟩

end NeckF

/-! ## 3. The neck representatives of `∂̄ξ` -/

section NeckRep

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}

/-- For a smooth section `ξ`, the neck representative of `½ (dξ + J₀ dξ j)` is
`neckFE J₀ (ξ ∘ σ) s₀ k`. -/
theorem formNeckRep_projF_eq (hsm : NeckSmooth A) {ξ : Section E twoSpheres}
    (hξ : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ ξ) (J₀ : E →L[ℝ] E) (j : Fin A.nn)
    (k : Fin (Module.finrank ℝ E)) :
    formNeckRep A j k (projF J₀ (dForm ξ)) =
      neckFE J₀ (fun p => ξ (twoSpheres.polar (A.hol j) p)) (A.s0 j) k := by
  funext p
  simp only [formNeckRep, neckFE]
  rcases le_or_gt p.1 (A.s0 j) with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul, zero_mul]
  · have hp := (A.neck_chart j p h.le).1
    rw [formInPolar_projF (A.isHol j) hp (hsm j _ hp) (hξ.mdifferentiable (by simp) _) J₀]

lemma ePol_zero : ePol 0 = expPolar := by
  funext p; simp [ePol]

lemma contDiff_expPolar : ContDiff ℝ ∞ expPolar := ePol_zero ▸ contDiff_ePol 0

variable {J₀ : E →L[ℝ] E}

lemma cmulL_I (v : E) : cmulL J₀ Complex.I v = J₀ v := by simp [cmulL_apply]

/-- In the polar coordinates at `inl e₂`, `ξ = χ(z) z·e` reads `χ(ζ) ζ·e`, `ζ = e^{-2π(s+it)}`. -/
lemma exSection_polar_inl (hA : IsStdNeck A) {j : Fin A.nn} (hj : A.node j = Sum.inl (pt 2))
    (e : E) : (fun p => exSection J₀ 0 e (twoSpheres.polar (A.hol j) p)) =
      fun p => chiC (expPolar p) • cmulL J₀ (expPolar p) e := by
  funext p
  rw [hA j, hj, polar_nodeChart_inl]
  simp only [exSection, Sum.elim_inl, holChart_holChart_symm, zero_add]

lemma exSection_polar_inr (hA : IsStdNeck A) {j : Fin A.nn} (hj : A.node j = Sum.inr (pt 2))
    (e : E) : (fun p => exSection J₀ 0 e (twoSpheres.polar (A.hol j) p)) = fun _ => 0 := by
  funext p
  rw [hA j, hj, polar_nodeChart_inr]
  rfl

/-- `ζ ↦ χ(ζ) ζ·e` along `ζ = e^{-2π(s+it)}` is holomorphic for `s > 0` (`χ = 1` there). -/
lemma cr_chiC_expPolar (hJ : ∀ v, J₀ (J₀ v) = -v) (e : E) (p : ℝ × ℝ) (hp : 0 < p.1) :
    fderiv ℝ (fun p => chiC (expPolar p) • cmulL J₀ (expPolar p) e) p (0, 1) =
      J₀ (fderiv ℝ (fun p => chiC (expPolar p) • cmulL J₀ (expPolar p) e) p (1, 0)) := by
  have hev : (fun p => chiC (expPolar p) • cmulL J₀ (expPolar p) e) =ᶠ[𝓝 p]
      fun p => (cmulL J₀).flip e (expPolar p) := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with x hx
    rw [chiC_eq_one, one_smul, ContinuousLinearMap.flip_apply]
    rw [norm_expPolar, Real.exp_le_one_iff]
    have : (0 : ℝ) < x.1 := hx
    nlinarith [Real.pi_pos]
  obtain ⟨L, hL, hLI⟩ := hasFDerivAt_expPolar p
  have hd : HasFDerivAt (fun p => (cmulL J₀).flip e (expPolar p)) _ p :=
    ((cmulL J₀).flip e).hasFDerivAt.comp p hL
  rw [hev.fderiv_eq, hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, hLI]
  rw [cmulL_mul hJ, cmulL_I]

/-- The neck representatives of `∂̄ξ`, `ξ = χ(z) z·e`, are test functions. -/
theorem isTest_neckFE_exSection (hA : IsStdNeck A) (hJ : ∀ v, J₀ (J₀ v) = -v) (e : E)
    (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) :
    IsTest (neckFE J₀ (fun p => exSection J₀ 0 e (twoSpheres.polar (A.hol j) p)) (A.s0 j) k) := by
  rcases A.node_cases j with hj | hj
  · rw [exSection_polar_inl hA hj]
    refine isTest_neckFE hJ ?_ (fun s t => by rw [expPolar_add_one]) (cr_chiC_expPolar hJ e) _ k
    exact (contDiff_chiC.comp contDiff_expPolar).smul
      ((cmulL J₀).contDiff.comp contDiff_expPolar |>.clm_apply contDiff_const)
  · rw [exSection_polar_inr hA hj]
    refine isTest_neckFE hJ contDiff_const (fun _ _ => rfl) (fun p _ => ?_) _ k
    simp

end NeckRep

/-! ## 4. `∂̄ξ` in the fibre, for every weight -/

section Fibre

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)} (hsm : NeckSmooth A) (G : GlueDataN A)
  (hA : IsStdNeck A)

include hsm G hA in
/-- **`∂̄ξ` is in the fibre for every weight** (the example of §4): the representatives of
`η = ½ (dξ + J(q) dξ j)`, `ξ = χ(z) z·e`, lie in the fibre blocks of weight `δ₀`, for every
`δ₀ ≥ 0`.  The neck blocks are test functions (`isTest_neckFE_exSection`: `η = 0` near the
node); the disc blocks are those of a weight `δ'₀ < 2π` (`D` of `smoothBlocks2`) cut off by
`chiP`, which is `1` on the disc. -/
theorem exists_isFormRep_exSection {δ' : ℕ → ℝ} (h0' : 0 ≤ δ' 0) (hmono' : StrictMono δ')
    (hδ' : δ' 0 < 2 * Real.pi) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (e : E) :
    ∃ b : (fibreBlocks A δ h0 hmono) 0,
      IsFormRep (projF (J.J q) (dForm (exSection (J.J q) 0 e))) b := by
  have hξ : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ (exSection (J.J q) 0 e) := contMDiff_exSection 0 e
  have hc := (exSection_cont_matching (q := q) (J₀ := J.J q) 0 e).1
  have hr' := isFormRep_linOpN twoSpheres_chartsOnto hsm G hc
    (isRep_smoothBlocks2 δ' h0' hmono' hξ hA hδ') (J.J q)
  set b' := linOpN twoSpheres_chartsOnto G δ' h0' hmono' (J.J q)
    (smoothBlocks2 δ' h0' hmono' hξ hA hδ')
  have hd0 := Neck.δ_nonneg δ h0 hmono 0
  have hd0' := Neck.δ_nonneg δ' h0' hmono' 0
  refine ⟨(fun idk => ChartChange.op idCC 2 hd0' contDiff_chiP tsupport_chiP hd0 (b'.1 idk),
    fun jk => toH 2 hd0 (isTest_neckFE_exSection hA (J.J_J q) e jk.1 jk.2)),
    fun i d k => ?_, fun j k => ?_⟩
  · have h1 := ChartChange.coeFn_op (D := idCC) contDiff_chiP tsupport_chiP hd0 (b'.1 (i, d, k))
    filter_upwards [h1, hr'.1 i d k] with x hx1 hx2
    refine hx1.trans ?_
    change chiP x * H.val (b'.1 (i, d, k)) x = _
    rw [show H.val (b'.1 (i, d, k)) x = _ from hx2]
    simp only [formDiscRep]
    rw [← mul_assoc, mul_comm (chiP x), discCut_mul_chiP]
  · rw [formNeckRep_projF_eq hsm hξ]
    exact MemLp.coeFn_toLp ((isTest_neckFE_exSection hA (J.J_J q) e j k).memLp 2)

include hsm G hA in
/-- **The regularity at the node** (the missing lemma of the example of §4): if `w ∈ H^{3,δ₀}_c`
(any `δ₀ ≥ 0`) and `D w` represents `½ (dξ + J(q) dξ j)` for a smooth section `ξ` with matching
values at the node, then `w` is represented by `ξ` plus a constant.  Lowered to the weight
`δ'₀ = 0` (`lowerBlocks`), `ξ` has blocks (`smoothBlocks2`), the two sections have the same `D`,
so `w - ξ` has `D = 0` and is a constant (`eq_const_of_isFormRep_zero`). -/
theorem isRep_add_const_of_linOpN {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}
    {ξ : Section E twoSpheres} (hξ : ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ ξ)
    (hmξ' : ξ (Sum.inl (pt 2)) = ξ (Sum.inr (pt 2)))
    {w : (blocks A δ h0 hmono) 0} (hw : w ∈ sectionSpace A δ h0 hmono)
    (hD : IsFormRep (projF (J.J q) (dForm ξ))
      (linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) w)) :
    ∃ c : E, IsRep (fun x => ξ x + c) w := by
  set δ' : ℕ → ℝ := fun n => n
  have h0' : 0 ≤ δ' 0 := by simp [δ']
  have hmono' : StrictMono δ' := Nat.strictMono_cast
  have hδ' : δ' 0 < 2 * Real.pi := by simp [δ', Real.pi_pos]
  have hle : δ' 0 ≤ δ 0 := by simpa [δ'] using h0
  have hcξ : IsContSection (fun _ => q) ξ := isContSection_of_const (fun _ => rfl) hξ.continuous
  have hmξ := isMatchingSection_twoSpheres hmξ'
  have hrξ := isRep_smoothBlocks2 δ' h0' hmono' hξ hA hδ'
  have hDξ := isFormRep_linOpN twoSpheres_chartsOnto hsm G hcξ hrξ (J.J q)
  rw [sectionSpace_eq_sectionsSub continuous_const A δ h0 hmono] at hw
  obtain ⟨ϖ, hcϖ, hmϖ, hrϖ⟩ := hw
  have hDϖ := isFormRep_linOpN twoSpheres_chartsOnto hsm G hcϖ hrϖ (J.J q)
  have hrϖ' : IsRep ϖ (lowerBlocks h0' hmono' hle w) := hrϖ.lower hle
  have hDϖ' := isFormRep_linOpN twoSpheres_chartsOnto hsm G hcϖ hrϖ' (J.J q)
  -- the forms of `ϖ` and `ξ` have the same representatives
  have hsame : IsFormRep (projF (J.J q) (dForm ϖ))
      (linOpN twoSpheres_chartsOnto G δ' h0' hmono' (J.J q)
        (smoothBlocks2 δ' h0' hmono' hξ hA hδ')) :=
    ⟨fun i d k => (hDξ.1 i d k).trans ((hD.1 i d k).symm.trans (hDϖ.1 i d k)),
      fun j k => (hDξ.2 j k).trans ((hD.2 j k).symm.trans (hDϖ.2 j k))⟩
  have heq := hDϖ'.unique hsame
  -- `ϖ - ξ` has `D = 0`
  have hr0 := hrϖ'.add (hrξ.smul (-1))
  have hc0 := hcϖ.add (hcξ.smul (-1))
  have hm0 : IsMatchingSection twoSpheres (ϖ + (-1 : ℝ) • ξ) := fun x y hxy => by
    change ϖ x + (-1 : ℝ) • ξ x = ϖ y + (-1 : ℝ) • ξ y
    rw [hmϖ x y hxy, show ξ x = ξ y from hmξ x y hxy]
  have hD0 := isFormRep_linOpN twoSpheres_chartsOnto hsm G hc0 hr0 (J.J q)
  have h00 : linOpN twoSpheres_chartsOnto G δ' h0' hmono' (J.J q)
      (lowerBlocks h0' hmono' hle w + (-1 : ℝ) • smoothBlocks2 δ' h0' hmono' hξ hA hδ') = 0 := by
    rw [map_add, map_smul, heq, neg_one_smul, add_neg_cancel]
  rw [h00] at hD0
  obtain ⟨hconst, -⟩ := eq_const_of_isFormRep_zero J hsm hc0 hm0 hr0 hD0
  refine ⟨(ϖ + (-1 : ℝ) • ξ) (Sum.inl (pt 2)), ?_⟩
  have hϖeq : ϖ = fun x => ξ x + (ϖ + (-1 : ℝ) • ξ) (Sum.inl (pt 2)) := by
    funext x
    rw [← congrFun hconst x]
    simp only [Pi.add_apply, neg_one_smul, Pi.neg_apply]
    abel
  rw [← hϖeq]
  exact hrϖ

include hsm G hA in
/-- The regularity at the node for the section of §4: a preimage under `D` of
`½ (dξ + J(q) dξ j)`, `ξ = χ(z) z·e`, is represented by `c + χ(z) z·e`. -/
theorem exSection_eq_of_linOpN {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ} (e : E)
    {w : (blocks A δ h0 hmono) 0} (hw : w ∈ sectionSpace A δ h0 hmono)
    (hD : IsFormRep (projF (J.J q) (dForm (exSection (J.J q) 0 e)))
      (linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) w)) :
    ∃ c : E, IsRep (exSection (J.J q) c e) w := by
  obtain ⟨c, hc⟩ := isRep_add_const_of_linOpN J hsm G hA (contMDiff_exSection 0 e)
    (by simp [exSection, holChart_neg_pt2]) hw hD
  refine ⟨c, ?_⟩
  convert hc using 1
  funext x
  rcases x with y | y
  · simp only [exSection, Sum.elim_inl, zero_add, add_comm]
  · simp only [exSection, Sum.elim_inr, zero_add]

/-! ## 5. `D` is not onto for `δ₀ ≥ 2π` -/

variable (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

include hA in
/-- **`D` is not onto for `δ₀ ≥ 2π`** (Memoir Prop 4.23, `a = 0`, two spheres joined at a node,
the example of §4): on every atlas with the standard neck charts and all gluing data, when
`E ≠ 0`.  The form `½ (dξ + J(q) dξ j)` of `ξ = χ(z) z·e` lies in the fibre
(`exists_isFormRep_exSection`); a preimage would be `ξ + c` (`exSection_eq_of_linOpN`), which is
not in `H^{3,δ₀}_c` (`not_mem_sectionSpace_of_two_pi_le`). -/
theorem not_surjective_linCRN_of_two_pi_le [Nontrivial E] (hδ : 2 * Real.pi ≤ δ 0) :
    ¬ Surjective (linCRN2 J hsm G δ h0 hmono) := by
  intro hs
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  obtain ⟨b, hb⟩ := exists_isFormRep_exSection J hsm G hA (δ' := fun n : ℕ => (n : ℝ))
    (by simp) Nat.strictMono_cast (by simp [Real.pi_pos]) δ h0 hmono e
  have hbF : b ∈ fibreSpace J A δ h0 hmono :=
    formsSub_le J A δ h0 hmono ⟨_, fun x _ => projF_mem J q _ x, hb⟩
  obtain ⟨w, hw⟩ := hs ⟨b, hbF⟩
  have hlin : linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) w = b :=
    congrArg Subtype.val hw
  obtain ⟨c, hc⟩ := exSection_eq_of_linOpN J hsm G hA e w.2 (hlin ▸ hb)
  exact not_mem_sectionSpace_of_two_pi_le hA hδ (J.J_J q) c he ⟨w, w.2, hc⟩

end Fibre

section Main

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) (q : Q)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- **`D` is not onto for `δ₀ ≥ 2π`, unconditional form**: for every `J`, `q` (with `E ≠ 0`)
and `δ₀ ≥ 2π`, there are an atlas with the standard neck charts and gluing data, as in
`linCRN_isFredholm_twoSpheres_uncond`, on which `D` is not onto. -/
theorem not_surjective_linCRN_twoSpheres_uncond [Nontrivial E] (hδ : 2 * Real.pi ≤ δ 0) :
    ∃ (A : SectionAtlas (E := E) twoSpheres (fun _ => q)) (hsm : NeckSmooth A)
      (G : GlueDataN A), IsStdNeck A ∧ GlueCharts A ∧
        ¬ Surjective (linCRN2 J hsm G δ h0 hmono) := by
  obtain ⟨A, hA, hG, hsm, ⟨G⟩, -⟩ := exists_glueAtlas_twoSpheres (E := E) q
  exact ⟨A, hsm, G, hA, hG, not_surjective_linCRN_of_two_pi_le J hsm G hA δ h0 hmono hδ⟩

/-- **The two ranges of the weight** (Memoir Prop 4.23, `a = 0`, two spheres joined at a node):
for `0 < δ₀ < 2π` there are an atlas and gluing data on which `D` is Fredholm and onto, of index
`dim E` (`linCRN_isFredholm_twoSpheres_uncond`); for `δ₀ ≥ 2π`, on every atlas with the standard
neck charts and all gluing data, `D` is not onto (when `E ≠ 0`). -/
theorem linCRN_onto_dichotomy_twoSpheres [Nontrivial E] :
    (0 < δ 0 → δ 0 < 2 * Real.pi →
      ∃ (A : SectionAtlas (E := E) twoSpheres (fun _ => q)) (hsm : NeckSmooth A)
        (G : GlueDataN A), IsStdNeck A ∧ GlueCharts A ∧
          ContinuousLinearMap.IsFredholm (linCRN2 J hsm G δ h0 hmono) ∧
          Surjective (linCRN2 J hsm G δ h0 hmono) ∧
          fredholmIndex (linCRN2 J hsm G δ h0 hmono) = Module.finrank ℝ E) ∧
    (2 * Real.pi ≤ δ 0 → ∀ (A : SectionAtlas (E := E) twoSpheres (fun _ => q))
      (hsm : NeckSmooth A) (G : GlueDataN A), IsStdNeck A →
        ¬ Surjective (linCRN2 J hsm G δ h0 hmono)) := by
  refine ⟨fun hδ hδ' => ?_, fun hδ A hsm G hA =>
    not_surjective_linCRN_of_two_pi_le J hsm G hA δ h0 hmono hδ⟩
  obtain ⟨A, hsm, G, hA, hG, h1, h2, h3, -⟩ :=
    linCRN_isFredholm_twoSpheres_uncond J q δ h0 hmono hδ hδ'
  exact ⟨A, hsm, G, hA, hG, h1, h2, h3⟩

/-- **One atlas for all weights**: there are an atlas with the standard neck charts and gluing
data on which, for every weight with `δ₀ > 0`, `D` is onto exactly when `δ₀ < 2π` (`E ≠ 0`). -/
theorem linCRN_surjective_iff_twoSpheres [Nontrivial E] :
    ∃ (A : SectionAtlas (E := E) twoSpheres (fun _ => q)) (hsm : NeckSmooth A)
      (G : GlueDataN A), IsStdNeck A ∧ GlueCharts A ∧
        ∀ (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ), 0 < δ 0 →
          (Surjective (linCRN2 J hsm G δ h0 hmono) ↔ δ 0 < 2 * Real.pi) := by
  obtain ⟨A, hA, hG, hsm, ⟨G⟩, -⟩ := exists_glueAtlas_twoSpheres (E := E) q
  refine ⟨A, hsm, G, hA, hG, fun δ h0 hmono hδ => ⟨fun hs => ?_, fun hδ' => ?_⟩⟩
  · by_contra h
    exact not_surjective_linCRN_of_two_pi_le J hsm G hA δ h0 hmono (not_lt.1 h) hs
  · exact (linCRN_isFredholm_twoSpheres_of_glueCharts J δ h0 hmono hsm G hA hG hδ hδ').2.1

end Main

end GWMemoir
