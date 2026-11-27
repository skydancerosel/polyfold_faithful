import GWMemoir.EllipticEstimate
import GWMemoir.LinearCRFredholm

/-!
# The elliptic estimate for the linearized Cauchy–Riemann operator on the three-pointed sphere

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Props 4.7, 4.23): the
estimate `‖ξ‖_{H^{3,δ₀}} ≤ C (‖Dξ‖_{H^{2,δ₀}} + ‖ξ‖_{L²})` for `D = linCR` at a constant map from
`sphere3` (`GWMemoir.LinearCRFredholm`).

* `estimate_of_compact`: an estimate `‖x‖ ≤ C (‖Tx‖ + ‖Kx‖)` with `K` compact improves to
  `‖x‖ ≤ C' (‖Tx‖ + ‖L K x‖)` when `Tx = 0`, `LKx = 0` force `x = 0`.
* `val_dtH_of_chiP`: for `u = χ u`, `∂_t u = (∂_t χ) u + χ ∂_t u`.
* `crOp_eq`: on the disc block `i`, read without weight,
  `∂_s v_k + b ∑_l J_{kl} ∂_t v_l = 2 ε_i (D v)_{i,0,k} + Z_{i,0,k} + b ∑_l J_{kl} ((∂_t χ) v_l
  + χ Z_{i,1,l})`, with `b = ±1` from `jMat_disc_const` and `J_{kl}` the matrix of `J(q)`.
* `estimate_disc`: `‖v_{i,k}‖_{H^{3,0}} ≤ C (‖D v‖ + ‖v‖_{H^{2,0}})`, from `cyl_estimate`;
  with the weight transfer `v = χ v` (`chiP_mul_of_mem`) this bounds `‖v‖_{H^{3,δ₀}}`.
* **`ellipticEstimate_sphere3`**: the named proposition `EllipticEstimate` holds, by
  `estimate_of_compact` with the compact inclusion `H^{3,δ₀} → H^{2,0}` (`0 < δ₀`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology InnerProductSpace NNReal
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. Improving an estimate with a compact term -/

section Compact

variable {X F G H' : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H'] [NormedSpace ℝ H']

/-- An estimate `‖x‖ ≤ C (‖Tx‖ + ‖Kx‖)` with `K` compact gives `‖x‖ ≤ C' (‖Tx‖ + ‖L K x‖)`
when `Tx = 0` and `LKx = 0` force `x = 0`. -/
theorem estimate_of_compact {T : X →L[ℝ] F} {K : X →L[ℝ] G} (hK : IsCompactOperator K)
    (L : G →L[ℝ] H') (hinj : ∀ x, T x = 0 → L (K x) = 0 → x = 0) {C : ℝ}
    (hC : ∀ x, ‖x‖ ≤ C * (‖T x‖ + ‖K x‖)) :
    ∃ C' : ℝ, ∀ x, ‖x‖ ≤ C' * (‖T x‖ + ‖L (K x)‖) := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ y : X, ‖y‖ = 1 ∧ ‖T y‖ + ‖L (K y)‖ < 1 / (n + 1) := by
    intro n
    obtain ⟨x, hx⟩ := hcon (n + 1)
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
    refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
    · simp only [map_smul, norm_smul, norm_inv, norm_norm]
      rw [← mul_add, ← div_eq_inv_mul, div_lt_iff₀ hxn, div_mul_eq_mul_div, one_mul,
        lt_div_iff₀ (by positivity), mul_comm]
      exact hx
  choose y hy1 hy using hseq
  obtain ⟨S, hS, hSsub⟩ := hK.image_closedBall_subset_compact (f := (K : X →ₗ[ℝ] G)) 1
  have hmem : ∀ n, K (y n) ∈ S := fun n => hSsub ⟨y n, by
    rw [Metric.mem_closedBall, dist_zero_right]; exact (hy1 n).le, rfl⟩
  obtain ⟨z, -, φ, hφ, hlim⟩ := hS.tendsto_subseq hmem
  have hsmall : Tendsto (fun n => (1 : ℝ) / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hT0 : Tendsto (fun n => T (y (φ n))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => by
      linarith [hy (φ n), norm_nonneg (L (K (y (φ n))))]) hsmall
  have hL0 : Tendsto (fun n => L (K (y (φ n)))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => by
      linarith [hy (φ n), norm_nonneg (T (y (φ n)))]) hsmall
  set C' : ℝ≥0 := ⟨2 * max C 0, by positivity⟩
  set Ψ : X →L[ℝ] F × G := T.prod K
  have hΨ : AntilipschitzWith C' Ψ := by
    refine AddMonoidHomClass.antilipschitz_of_bound Ψ fun x => ?_
    have h1 := hC x
    have h2 : ‖T x‖ ≤ ‖Ψ x‖ := le_max_left _ _
    have h3 : ‖K x‖ ≤ ‖Ψ x‖ := le_max_right _ _
    change ‖x‖ ≤ 2 * max C 0 * ‖Ψ x‖
    have h4 : C * (‖T x‖ + ‖K x‖) ≤ max C 0 * (‖T x‖ + ‖K x‖) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    nlinarith [le_max_right C 0]
  have hΨlim : Tendsto (fun n => Ψ (y (φ n))) atTop (𝓝 (0, z)) := hT0.prodMk_nhds hlim
  have hcau : CauchySeq (fun n => y (φ n)) := by
    have h' : CauchySeq (fun n => Ψ (y (φ n))) := hΨlim.cauchySeq
    have h'' := (hΨ.isUniformInducing Ψ.uniformContinuous).cauchy_map_iff
      (F := map (fun n => y (φ n)) atTop)
    rw [Filter.map_map] at h''
    exact h''.1 h'
  obtain ⟨y₀, hy₀⟩ := cauchySeq_tendsto_of_complete hcau
  have hn : ‖y₀‖ = 1 := by
    have := (continuous_norm.tendsto _).comp hy₀
    simp only [Function.comp_def, hy1] at this
    exact (tendsto_nhds_unique tendsto_const_nhds this).symm
  have hTy : T y₀ = 0 := tendsto_nhds_unique ((T.continuous.tendsto _).comp hy₀) hT0
  have hLy : L (K y₀) = 0 :=
    tendsto_nhds_unique (((L.comp K).continuous.tendsto _).comp hy₀) hL0
  rw [hinj y₀ hTy hLy, norm_zero] at hn
  exact zero_ne_one hn

/-- Finitely many bounds `f i x ≤ C_i g x` with `g ≥ 0` have a common constant. -/
lemma exists_common_bound {ι α : Type*} [Fintype ι] {f : ι → α → ℝ} {g : α → ℝ}
    (hg : ∀ x, 0 ≤ g x) (h : ∀ i, ∃ C : ℝ, ∀ x, f i x ≤ C * g x) :
    ∃ C : ℝ, ∀ i x, f i x ≤ C * g x := by
  choose C hC using h
  refine ⟨∑ i, |C i|, fun i x => (hC i x).trans (mul_le_mul_of_nonneg_right ?_ (hg x))⟩
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |C i|)
    (fun i _ => abs_nonneg _) (Finset.mem_univ i))

end Compact

/-! ## 2. The cut-off `χ` of the strip -/

section Cutoff

variable {δ : ℝ} {hδ : 0 ≤ δ}

/-- `∂_t χ`. -/
def dtChiP (p : ℝ × ℝ) : ℝ := fderiv ℝ chiP p (0, 1)

lemma contDiff_dtChiP : ContDiff ℝ ∞ dtChiP := ChartChange.contDiff_dir contDiff_chiP _

lemma tsupport_dtChiP : tsupport dtChiP ⊆ KP :=
  (ChartChange.tsupport_dir_subset _ _).trans tsupport_chiP

lemma compMul_zero_fun (f : Lp ℝ 2 cyl) : idCC.compMul (fun _ => (0 : ℝ)) f = 0 := by
  have hs : tsupport (fun _ : ℝ × ℝ => (0 : ℝ)) ⊆ idCC.K := by
    rw [show (fun _ : ℝ × ℝ => (0 : ℝ)) = 0 from rfl, tsupport_zero]; exact empty_subset _
  refine Lp.ext ?_
  filter_upwards [idCC.coeFn_compMul continuous_const hs f, Lp.coeFn_zero ℝ 2 cyl] with x h1 h2
  rw [h1, h2, zero_mul]; rfl

/-- **`∂_t (χ u) = (∂_t χ) u + χ ∂_t u`**, for `u = χ u`. -/
lemma val_dtH_of_chiP (u : H 3 hδ) (hu : idCC.compMul chiP (H.val u) = H.val u) :
    H.val (dtH 2 hδ u) =
      idCC.compMul dtChiP (H.val u) + idCC.compMul chiP (H.val (dtH 2 hδ u)) := by
  have hw := ChartChange.hasWeakDeriv_evL (D := idCC) (k := 3) (hδ := hδ) contDiff_chiP
    tsupport_chiP (i := 0) (j := 1) (by norm_num) u
  rw [ChartChange.evL_L0, hu] at hw
  have hd := dv_unique (H.toSub u) (idxT 2) hw (Lp.memLp _)
  have e1 : H.val (dtH 2 hδ u) = ChartChange.evL idCC 3 hδ
      (ChartChange.terms idCC.ψ (ChartChange.L0 chiP) 0 1) u :=
    Lp.ext ((coeFn_dtH u).trans hd)
  have e2 : ChartChange.terms idCC.ψ (ChartChange.L0 chiP) 0 1 = [(dtChiP, 0, 0),
      (fun _ => (0 : ℝ), 1, 0), (chiP, 0, 1)] := by
    have hψ : ∀ x, fderiv ℝ idCC.ψ x (0, 1) = (0, 1) := fun x => by
      change fderiv ℝ id x (0, 1) = _; rw [fderiv_id]; rfl
    simp only [ChartChange.terms, ChartChange.L0, ChartChange.step, Function.iterate_one,
      Function.iterate_zero, id_eq, hψ, mul_zero, mul_one]
    rfl
  have e3 : ChartChange.dvAt 3 hδ 0 0 u = H.val u :=
    Lp.ext ((ChartChange.coeFn_dvAt (by norm_num) u).trans (dv_idx0 (H.toSub u)))
  have e4 : ChartChange.dvAt 3 hδ 0 1 u = H.val (dtH 2 hδ u) :=
    Lp.ext ((ChartChange.coeFn_dvAt (by norm_num) u).trans (coeFn_dtH u).symm)
  conv_lhs => rw [e1, e2]
  change idCC.compMul dtChiP (ChartChange.dvAt 3 hδ 0 0 u) +
    (idCC.compMul (fun _ => (0 : ℝ)) (ChartChange.dvAt 3 hδ 1 0 u) +
      (idCC.compMul chiP (ChartChange.dvAt 3 hδ 0 1 u) + 0)) = _
  rw [e3, e4, compMul_zero_fun, zero_add, add_zero]

end Cutoff

/-! ## 3. The operator in a disc chart, without weight -/

section Inclusions

variable {m : ℕ} {δ δ' : ℝ}

lemma val_dsH_inclH (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hδδ : δ ≤ δ') (u : H (m + 1) hδ') :
    H.val (dsH m hδ (inclH hδ hδ' le_rfl hδδ u)) = H.val (dsH m hδ' u) :=
  Lp.ext ((coeFn_dsH _).trans ((dv_unique (H.toSub (inclH hδ hδ' le_rfl hδδ u)) (idxS m)
    (dv_spec (H.toSub u) (idxS m)).1 (dv_memLp _ _)).trans (coeFn_dsH u).symm))

lemma val_dtH_inclH (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ') (hδδ : δ ≤ δ') (u : H (m + 1) hδ') :
    H.val (dtH m hδ (inclH hδ hδ' le_rfl hδδ u)) = H.val (dtH m hδ' u) :=
  Lp.ext ((coeFn_dtH _).trans ((dv_unique (H.toSub (inclH hδ hδ' le_rfl hδδ u)) (idxT m)
    (dv_spec (H.toSub u) (idxT m)).1 (dv_memLp _ _)).trans (coeFn_dtH u).symm))

lemma compMul_const_mul {a : ℝ × ℝ → ℝ} (ha : Continuous a) (haK : tsupport a ⊆ KP) (c : ℝ)
    (f : Lp ℝ 2 cyl) : idCC.compMul (fun p => c * a p) f = c • idCC.compMul a f := by
  have hs : tsupport (fun p => c * a p) ⊆ idCC.K :=
    (tsupport_mul_subset_right (f := fun _ => c)).trans haK
  refine Lp.ext ?_
  filter_upwards [idCC.coeFn_compMul (b := fun p => c * a p) (continuous_const.mul ha) hs f,
    idCC.coeFn_compMul ha haK f, Lp.coeFn_smul c (idCC.compMul a f)] with x h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2, smul_eq_mul, mul_assoc]

end Inclusions

section Sphere

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q} {A : SectionAtlas (E := E) sphere3 (fun _ => q)}
  (G : GlueData A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- `H^{3,δ₀} → H^{3,0}`. -/
abbrev inc3 : H 3 (Neck.δ_nonneg δ h0 hmono 0) →L[ℝ] H 3 (le_refl (0 : ℝ)) :=
  inclH (le_refl 0) (Neck.δ_nonneg δ h0 hmono 0) le_rfl h0

/-- `H^{3,δ₀} → H^{2,0}`. -/
abbrev inc2 : H 3 (Neck.δ_nonneg δ h0 hmono 0) →L[ℝ] H 2 (le_refl (0 : ℝ)) :=
  inclH (le_refl 0) (Neck.δ_nonneg δ h0 hmono 0) (by norm_num) h0

/-- `H^{2,δ₀} → H^{2,0}`. -/
abbrev inc22 : H 2 (Neck.δ_nonneg δ h0 hmono 0) →L[ℝ] H 2 (le_refl (0 : ℝ)) :=
  inclH (le_refl 0) (Neck.δ_nonneg δ h0 hmono 0) le_rfl h0

/-- Multiplication by `χ` on `H^{2,0}`. -/
abbrev chiOp : H 2 (le_refl (0 : ℝ)) →L[ℝ] H 2 (le_refl (0 : ℝ)) :=
  idCC.op 2 (le_refl 0) contDiff_chiP tsupport_chiP (le_refl 0)

/-- Multiplication by `∂_t χ` on `H^{2,0}`. -/
abbrev dtChiOp : H 2 (le_refl (0 : ℝ)) →L[ℝ] H 2 (le_refl (0 : ℝ)) :=
  idCC.op 2 (le_refl 0) contDiff_dtChiP tsupport_dtChiP (le_refl 0)

/-- The zeroth-order term `Z` of `GWMemoir.zBlock`, from the blocks read in `H^{2,0}`. -/
def zW (o : Ix A) : (blocks A δ h0 hmono) 0 →L[ℝ] H 2 (le_refl (0 : ℝ)) :=
  ∑ j, ((G.D o.1 j).op 2 (le_refl 0) (G.hcZ sphere3_chartsOnto o.2.1 o.1 j)
    (G.hsZ sphere3_chartsOnto o.2.1 o.1 j) (le_refl 0)).comp
      ((inc2 δ h0 hmono).comp (secProj δ h0 hmono (j, o.2.2)))

lemma val_zW (o : Ix A) (v : (blocks A δ h0 hmono) 0) :
    H.val (zW G δ h0 hmono o v) = H.val (zBlock sphere3_chartsOnto G δ h0 hmono o v) := by
  change valCLM 2 _ (zW G δ h0 hmono o v) =
    valCLM 2 _ (zBlock sphere3_chartsOnto G δ h0 hmono o v)
  rw [zW, zBlock, sum_apply, sum_apply, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ =>
    (ChartChange.val_op (G.hcZ sphere3_chartsOnto o.2.1 o.1 j)
      (G.hsZ sphere3_chartsOnto o.2.1 o.1 j) (le_refl 0) (inc2 δ h0 hmono (v.1 (j, o.2.2)))).trans
    (ChartChange.val_op (G.hcZ sphere3_chartsOnto o.2.1 o.1 j)
      (G.hsZ sphere3_chartsOnto o.2.1 o.1 j) (Neck.δ_nonneg δ h0 hmono 0)
        (incl32 δ h0 hmono (v.1 (j, o.2.2)))).symm

variable {δ h0 hmono} in
/-- The projection term of `D` on the block `(i, 0, k)`: `b χ ∑_l J_{kl} R_{i,1,l}`. -/
lemma val_fOp_i0k {i : Fin A.nd} {b : ℝ} (hb : ∀ p, jMat (X := sphere3) (A.center i)
      (sphere3.discPt (A.center i) (A.ε i) p) (EuclideanSpace.single 0 1) =
        b • EuclideanSpace.single 1 1)
    (y : (fibreBlocks A δ h0 hmono) 0) (k : Fin (Module.finrank ℝ E)) :
    H.val ((fOp δ h0 hmono (fun _ _ => idCC) (aPI A (J.J q))
      (fun _ _ => contDiff_aP sphere3_chartsOnto (J.J q) _ _ _ _ _ _)
      (fun _ _ => tsupport_aP (J.J q) _ _ _ _ _ _) (srcP A) 0 y).1 (i, 0, k)) =
      ∑ l, (b * Jc (J.J q) k l) • idCC.compMul chiP (H.val (y.1 (i, 1, l))) := by
  refine (val_fOp ..).trans ?_
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have e0 : ∀ l, aPI A (J.J q) (i, 0, k) (0, l) = fun _ => (0 : ℝ) := fun l => by
    funext p; simp [aPI, aP, hb p]
  have e1 : ∀ l, aPI A (J.J q) (i, 0, k) (1, l) = fun p => (b * Jc (J.J q) k l) * chiP p :=
    fun l => by funext p; simp [aPI, aP, hb p]; ring
  simp only [e0, e1, compMul_zero_fun, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [compMul_const_mul contDiff_chiP.continuous tsupport_chiP]
  rfl

variable {δ h0 hmono} in
/-- **The operator in the disc chart `i`, read in `H^{2,0}`**: for `v = χ v`,
`∂_s v_k + b ∑_l J_{kl} ∂_t v_l = 2 ε_i (D v)_{i,0,k} + Z_{i,0,k}
  + b ∑_l J_{kl} ((∂_t χ) v_l + χ Z_{i,1,l})`. -/
theorem crOp_eq (v : (blocks A δ h0 hmono) 0)
    (hχ : ∀ jk, idCC.compMul chiP (H.val (v.1 jk)) = H.val (v.1 jk)) {i : Fin A.nd} {b : ℝ}
    (hb : ∀ p, jMat (X := sphere3) (A.center i) (sphere3.discPt (A.center i) (A.ε i) p)
      (EuclideanSpace.single 0 1) = b • EuclideanSpace.single 1 1)
    (k : Fin (Module.finrank ℝ E)) :
    crOp 2 (fun k l => b * Jc (J.J q) k l) (fun l => inc3 δ h0 hmono (v.1 (i, l))) k =
      (2 * A.ε i) • inc22 δ h0 hmono
          ((linOp sphere3_chartsOnto G δ h0 hmono (J.J q) v).1 (i, 0, k)) +
        zW G δ h0 hmono (i, 0, k) v + ∑ l, (b * Jc (J.J q) k l) •
          (dtChiOp (inc2 δ h0 hmono (v.1 (i, l))) + chiOp (zW G δ h0 hmono (i, 1, l) v)) := by
  apply valCLM_injective (m := 2) (hδ := le_refl (0 : ℝ))
  have hε : A.ε i ≠ 0 := (A.ε_pos i).ne'
  set hd := Neck.δ_nonneg δ h0 hmono 0
  set y := rOp sphere3_chartsOnto G δ h0 hmono v
  have hD : valCLM 2 (le_refl 0) (inc22 δ h0 hmono
      ((linOp sphere3_chartsOnto G δ h0 hmono (J.J q) v).1 (i, 0, k))) =
      (1 / 2 : ℝ) • (H.val (y.1 (i, 0, k)) + H.val ((fOp δ h0 hmono (fun _ _ => idCC)
        (aPI A (J.J q)) (fun _ _ => contDiff_aP sphere3_chartsOnto (J.J q) _ _ _ _ _ _)
        (fun _ _ => tsupport_aP (J.J q) _ _ _ _ _ _) (srcP A) 0 y).1 (i, 0, k))) := rfl
  rw [val_fOp_i0k J hb y k] at hD
  have hR : ∀ o : Ix A, H.val (y.1 o) = (A.ε o.1)⁻¹ • (valCLM 2 hd (dH δ h0 hmono o.2.1
      (v.1 (o.1, o.2.2))) - valCLM 2 (le_refl 0) (zW G δ h0 hmono o v)) := fun o => by
    change valCLM 2 hd ((A.ε o.1)⁻¹ • (_ - _)) = _
    rw [map_smul, map_sub]
    congr 2
    exact (val_zW G δ h0 hmono o v).symm
  have a1 : ∀ l, valCLM 2 (le_refl 0) (dsH 2 (le_refl 0) (inc3 δ h0 hmono (v.1 (i, l)))) =
      valCLM 2 hd (dH δ h0 hmono 0 (v.1 (i, l))) := fun l => val_dsH_inclH _ _ _ _
  have a2 : ∀ l, valCLM 2 (le_refl 0) (dtH 2 (le_refl 0) (inc3 δ h0 hmono (v.1 (i, l)))) =
      valCLM 2 hd (dH δ h0 hmono 1 (v.1 (i, l))) := fun l => val_dtH_inclH _ _ _ _
  have a5 : ∀ l, valCLM 2 (le_refl 0) (dtChiOp (inc2 δ h0 hmono (v.1 (i, l)))) =
      idCC.compMul dtChiP (valCLM 3 hd (v.1 (i, l))) := fun l =>
    ChartChange.val_op contDiff_dtChiP tsupport_dtChiP (le_refl 0) _
  have a6 : ∀ l, valCLM 2 (le_refl 0) (chiOp (zW G δ h0 hmono (i, 1, l) v)) =
      idCC.compMul chiP (valCLM 2 (le_refl 0) (zW G δ h0 hmono (i, 1, l) v)) := fun l =>
    ChartChange.val_op contDiff_chiP tsupport_chiP (le_refl 0) _
  have a7 : ∀ l, idCC.compMul chiP (valCLM 2 hd (dH δ h0 hmono 1 (v.1 (i, l)))) =
      valCLM 2 hd (dH δ h0 hmono 1 (v.1 (i, l))) - idCC.compMul dtChiP (valCLM 3 hd (v.1 (i, l))) :=
    fun l => eq_sub_of_add_eq' (val_dtH_of_chiP (v.1 (i, l)) (hχ (i, l))).symm
  simp only [crOp, map_add, map_sum, map_smul]
  rw [hD]
  simp only [hR, a1, a2, a5, a6, map_smul, map_sub, a7]
  set S := valCLM 2 hd (dH δ h0 hmono 0 (v.1 (i, k)))
  set Z0 := valCLM 2 (le_refl 0) (zW G δ h0 hmono (i, 0, k) v)
  have hsum : ∑ l, (b * Jc (J.J q) k l) • (A.ε i)⁻¹ • (valCLM 2 hd (dH δ h0 hmono 1 (v.1 (i, l))) -
      idCC.compMul dtChiP (valCLM 3 hd (v.1 (i, l))) -
        idCC.compMul chiP (valCLM 2 (le_refl 0) (zW G δ h0 hmono (i, 1, l) v))) =
      (A.ε i)⁻¹ • (∑ l, (b * Jc (J.J q) k l) • valCLM 2 hd (dH δ h0 hmono 1 (v.1 (i, l))) -
        ∑ l, (b * Jc (J.J q) k l) • (idCC.compMul dtChiP (valCLM 3 hd (v.1 (i, l))) +
          idCC.compMul chiP (valCLM 2 (le_refl 0) (zW G δ h0 hmono (i, 1, l) v)))) := by
    rw [← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_comm, sub_sub, smul_sub]
  rw [hsum]
  set X := ∑ l, (b * Jc (J.J q) k l) • valCLM 2 hd (dH δ h0 hmono 1 (v.1 (i, l)))
  set Y := ∑ l, (b * Jc (J.J q) k l) • (idCC.compMul dtChiP (valCLM 3 hd (v.1 (i, l))) +
    idCC.compMul chiP (valCLM 2 (le_refl 0) (zW G δ h0 hmono (i, 1, l) v)))
  rw [← smul_add, smul_smul, smul_smul, show 2 * A.ε i * (1 / 2) * (A.ε i)⁻¹ = 1 by
    field_simp, one_smul]
  abel

/-! ## 4. The estimate -/

lemma isCxMat_Jc {J₀ : E →L[ℝ] E} (hJ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ E) {b : ℝ}
    (hb : b ^ 2 = 1) : IsCxMat fun k l => b * Jc J₀ k l := by
  intro k l
  have e : ∀ j, b * Jc J₀ k j * (b * Jc J₀ j l) =
      b ^ 2 * (Jc J₀ k j * crd j (J₀ (Module.finBasis ℝ E l))) := fun j => by
    simp only [Jc]; ring
  rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum, sum_Jc, hb, one_mul]
  have h2 : J₀ (J₀ (Module.finBasis ℝ E l)) = -(Module.finBasis ℝ E l) := by
    have := congrArg (fun L => L (Module.finBasis ℝ E l)) hJ
    simpa using this
  rw [h2, map_neg]
  simp only [crd, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : k = l
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The blocks read in `H^{2,0}`. -/
def kOp : (blocks A δ h0 hmono) 0 →L[ℝ]
    (Fin A.nd × Fin (Module.finrank ℝ E) → H 2 (le_refl (0 : ℝ))) :=
  ContinuousLinearMap.pi fun jk => (inc2 δ h0 hmono).comp (secProj δ h0 hmono jk)

/-- The term `Z` on the blocks read in `H^{2,0}`. -/
def zK (o : Ix A) :
    (Fin A.nd × Fin (Module.finrank ℝ E) → H 2 (le_refl (0 : ℝ))) →L[ℝ] H 2 (le_refl (0 : ℝ)) :=
  ∑ j, ((G.D o.1 j).op 2 (le_refl 0) (G.hcZ sphere3_chartsOnto o.2.1 o.1 j)
    (G.hsZ sphere3_chartsOnto o.2.1 o.1 j) (le_refl 0)).comp
      (ContinuousLinearMap.proj (j, o.2.2))

lemma zW_eq (o : Ix A) (v : (blocks A δ h0 hmono) 0) :
    zW G δ h0 hmono o v = zK G o (kOp δ h0 hmono v) := by
  rw [zW, zK, sum_apply, sum_apply]; rfl

/-- The right side of `crOp_eq` as a bounded operator of `(D v, v)`. -/
def phiOp (i : Fin A.nd) (b : ℝ) (k : Fin (Module.finrank ℝ E)) :
    (fibreBlocks A δ h0 hmono) 0 × (Fin A.nd × Fin (Module.finrank ℝ E) →
      H 2 (le_refl (0 : ℝ))) →L[ℝ] H 2 (le_refl (0 : ℝ)) :=
  ((2 * A.ε i) • ((inc22 δ h0 hmono).comp ((ContinuousLinearMap.proj (i, 0, k)).comp
      (ContinuousLinearMap.fst ℝ _ _)))).comp (ContinuousLinearMap.fst ℝ _ _) +
    (zK G (i, 0, k)).comp (ContinuousLinearMap.snd ℝ _ _) +
    ∑ l, (b * Jc (J.J q) k l) • ((dtChiOp.comp (ContinuousLinearMap.proj (i, l)) +
      chiOp.comp (zK G (i, 1, l))).comp (ContinuousLinearMap.snd ℝ _ _))

variable {δ h0 hmono} in
lemma crOp_eq_phiOp (v : (blocks A δ h0 hmono) 0)
    (hχ : ∀ jk, idCC.compMul chiP (H.val (v.1 jk)) = H.val (v.1 jk)) {i : Fin A.nd} {b : ℝ}
    (hb : ∀ p, jMat (X := sphere3) (A.center i) (sphere3.discPt (A.center i) (A.ε i) p)
      (EuclideanSpace.single 0 1) = b • EuclideanSpace.single 1 1)
    (k : Fin (Module.finrank ℝ E)) :
    crOp 2 (fun k l => b * Jc (J.J q) k l) (fun l => inc3 δ h0 hmono (v.1 (i, l))) k =
      phiOp J G δ h0 hmono i b k
        (linOp sphere3_chartsOnto G δ h0 hmono (J.J q) v, kOp δ h0 hmono v) := by
  rw [crOp_eq J G v hχ hb k, phiOp, add_apply,
    add_apply, sum_apply, zW_eq]
  refine congrArg₂ _ rfl (Finset.sum_congr rfl fun l _ => ?_)
  rw [zW_eq]; rfl

variable {δ h0 hmono} in
/-- **The estimate against `H^{2,0}`** on the disc block `i`:
`‖v_{i,k}‖_{H^{3,0}} ≤ C (‖D v‖ + ‖v‖_{H^{2,0}})`, for `v = χ v`. -/
lemma estimate_disc (i : Fin A.nd) : ∃ C : ℝ, ∀ v : {v : (blocks A δ h0 hmono) 0 //
    ∀ jk, idCC.compMul chiP (H.val (v.1 jk)) = H.val (v.1 jk)}, ∀ k,
      ‖inc3 δ h0 hmono (v.1.1 (i, k))‖ ≤ C * (‖linOp sphere3_chartsOnto G δ h0 hmono (J.J q) v.1‖ +
        ‖kOp δ h0 hmono v.1‖) := by
  obtain ⟨b, hb2, hb⟩ := jMat_disc_const (A.center i) (A.ε i)
  obtain ⟨C0, hC0⟩ := cyl_estimate _ (isCxMat_Jc (J.sq q) hb2) 2
  set M := (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) + ∑ l, ‖phiOp J G δ h0 hmono i b l‖
  refine ⟨max C0 0 * M, fun ⟨v, hχ⟩ k => ?_⟩
  set N := ‖linOp sphere3_chartsOnto G δ h0 hmono (J.J q) v‖ + ‖kOp δ h0 hmono v‖
  have hN : 0 ≤ N := by positivity
  have h1 : ∀ l, ‖H.val (inc3 δ h0 hmono (v.1 (i, l)))‖ ≤ N := fun l => by
    have e : ‖H.val (inc3 δ h0 hmono (v.1 (i, l)))‖ = ‖H.val (kOp δ h0 hmono v (i, l))‖ := rfl
    rw [e, ← norm_wdv_idx0]
    exact (norm_wdv_le _ _).trans ((norm_le_pi_norm (kOp δ h0 hmono v) (i, l)).trans
      (le_add_of_nonneg_left (norm_nonneg _)))
  have h2 : ∀ l, ‖crOp 2 (fun k l => b * Jc (J.J q) k l)
      (fun l => inc3 δ h0 hmono (v.1 (i, l))) l‖ ≤ ‖phiOp J G δ h0 hmono i b l‖ * N := fun l => by
    rw [crOp_eq_phiOp J G v hχ hb l]
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hS : ∑ l, ‖H.val (inc3 δ h0 hmono (v.1 (i, l)))‖ + ∑ l, ‖crOp 2
      (fun k l => b * Jc (J.J q) k l) (fun l => inc3 δ h0 hmono (v.1 (i, l))) l‖ ≤ M * N := by
    have := add_le_add (Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => h1 l)
      (Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => h2 l)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul] at this
    linarith
  have hk := hC0 (fun l => inc3 δ h0 hmono (v.1 (i, l))) k
  have hS0 : 0 ≤ ∑ l, ‖H.val (inc3 δ h0 hmono (v.1 (i, l)))‖ + ∑ l, ‖crOp 2
      (fun k l => b * Jc (J.J q) k l) (fun l => inc3 δ h0 hmono (v.1 (i, l))) l‖ := by positivity
  calc ‖inc3 δ h0 hmono (v.1 (i, k))‖ ≤ max C0 0 * (∑ l, ‖H.val (inc3 δ h0 hmono (v.1 (i, l)))‖ +
        ∑ l, ‖crOp 2 (fun k l => b * Jc (J.J q) k l) (fun l => inc3 δ h0 hmono (v.1 (i, l))) l‖) :=
        hk.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hS0)
    _ ≤ max C0 0 * (M * N) := mul_le_mul_of_nonneg_left hS (le_max_right _ _)
    _ = max C0 0 * M * N := by ring

variable {δ h0 hmono} in
/-- On `sphere3` every section has `v = χ v` on its disc blocks: its representatives carry the
cut-off `β` (`discRep`), and `β χ = β`. -/
lemma chiP_mul_of_mem {v : (blocks A δ h0 hmono) 0} (hv : v ∈ sectionSpace A δ h0 hmono)
    (jk : Fin A.nd × Fin (Module.finrank ℝ E)) :
    idCC.compMul chiP (H.val (v.1 jk)) = H.val (v.1 jk) := by
  rw [sectionSpace_eq_of_nodes_empty continuous_const rfl A δ h0 hmono] at hv
  obtain ⟨η, -, -, hr⟩ := hv
  obtain ⟨i, k⟩ := jk
  refine Lp.ext ?_
  filter_upwards [idCC.coeFn_compMul contDiff_chiP.continuous tsupport_chiP (H.val (v.1 (i, k))),
    hr.1 i k] with x h1 h2
  rw [h1]
  change chiP x * H.val (discBlock v i k) x = H.val (discBlock v i k) x
  rw [h2, discRep, ← mul_assoc, mul_comm (chiP x), discCut_mul_chiP]

/-- **The elliptic estimate on `sphere3`** (Memoir §4, at a constant map): the named proposition
`EllipticEstimate`, `‖ξ‖_{H^{3,δ₀}} ≤ C (‖Dξ‖_{H^{2,δ₀}} + ‖ξ‖_{L²})`. -/
theorem ellipticEstimate_sphere3 (hδ : 0 < δ 0) : EllipticEstimate J G δ h0 hmono hδ := by
  set hd := Neck.δ_nonneg δ h0 hmono 0
  have hnn : IsEmpty (Fin A.nn) := isEmpty_neck_of_nodes_empty rfl A
  obtain ⟨C1, hC1⟩ := exists_common_bound (ι := Fin A.nd)
    (f := fun i (x : {v : (blocks A δ h0 hmono) 0 // ∀ jk, idCC.compMul chiP (H.val (v.1 jk)) =
      H.val (v.1 jk)} × Fin (Module.finrank ℝ E)) => ‖inc3 δ h0 hmono (x.1.1.1 (i, x.2))‖)
    (g := fun x => ‖linOp sphere3_chartsOnto G δ h0 hmono (J.J q) x.1.1‖ +
      ‖kOp δ h0 hmono x.1.1‖) (fun x => by positivity)
    (fun i => by
      obtain ⟨C, hC⟩ := estimate_disc J G (δ := δ) (h0 := h0) (hmono := hmono) i
      exact ⟨C, fun x => hC x.1 x.2⟩)
  -- the weight transfer `v = χ v`, from `H^{3,0}` to `H^{3,δ₀}`
  set chi3 : H 3 (le_refl (0 : ℝ)) →L[ℝ] H 3 hd :=
    idCC.op 3 (le_refl 0) contDiff_chiP tsupport_chiP hd
  have hχv : ∀ {v : (blocks A δ h0 hmono) 0}, v ∈ sectionSpace A δ h0 hmono → ∀ jk,
      chi3 (inc3 δ h0 hmono (v.1 jk)) = v.1 jk := fun hv jk => by
    apply valCLM_injective (m := 3) (hδ := hd)
    exact (ChartChange.val_op contDiff_chiP tsupport_chiP hd _).trans (chiP_mul_of_mem hv jk)
  set K' := (kOp δ h0 hmono).comp (sectionSpace A δ h0 hmono).subtypeL
  set C2 := ‖chi3‖ * max C1 0
  have hmain : ∀ w : sectionSpace A δ h0 hmono,
      ‖w‖ ≤ C2 * (‖linCR3 J G δ h0 hmono w‖ + ‖K' w‖) := by
    intro w
    have hv := w.2
    set v : (blocks A δ h0 hmono) 0 := (w : (blocks A δ h0 hmono) 0)
    have hN : 0 ≤ C2 * (‖linCR3 J G δ h0 hmono w‖ + ‖K' w‖) := by positivity
    have hb : ∀ jk, ‖v.1 jk‖ ≤ C2 * (‖linCR3 J G δ h0 hmono w‖ + ‖K' w‖) := by
      rintro ⟨i, k⟩
      have h1 := hC1 i (⟨v, chiP_mul_of_mem hv⟩, k)
      have h1' : ‖inc3 δ h0 hmono (v.1 (i, k))‖ ≤ max C1 0 *
          (‖linCR3 J G δ h0 hmono w‖ + ‖K' w‖) :=
        h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      rw [← hχv hv (i, k)]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h1' (norm_nonneg _)
    have e : ‖w‖ = ‖v‖ := rfl
    rw [e]
    refine norm_prod_le_iff.2 ⟨(pi_norm_le_iff_of_nonneg hN).2 hb, ?_⟩
    rw [show v.2 = 0 from funext fun jk => isEmptyElim jk.1, norm_zero]
    exact hN
  -- the compact term, and `L² → H^{2,0}`
  have hK : IsCompactOperator K' := by
    have : IsCompactOperator (kOp (A := A) δ h0 hmono) := isCompactOperator_pi fun jk => by
      rw [ContinuousLinearMap.coe_comp]
      exact (isCompactOperator_inclH (m := 2) (le_refl (0 : ℝ)) hd hδ).comp_clm _
    rw [ContinuousLinearMap.coe_comp]
    exact this.comp_clm _
  set L : (Fin A.nd × Fin (Module.finrank ℝ E) → H 2 (le_refl (0 : ℝ))) →L[ℝ]
      (Fin A.nd × Fin (Module.finrank ℝ E) → H 0 (le_refl (0 : ℝ))) :=
    ContinuousLinearMap.pi fun jk =>
      (inclH (le_refl (0 : ℝ)) (le_refl (0 : ℝ)) (Nat.zero_le 2) le_rfl).comp
        (ContinuousLinearMap.proj jk)
  have hl2 : ∀ w, l2Op (A := A) δ h0 hmono hδ w = L (K' w) := fun w => rfl
  have hinj : ∀ w, linCR3 J G δ h0 hmono w = 0 → L (K' w) = 0 → w = 0 := by
    intro w _ h
    refine Subtype.ext (Prod.ext (funext fun jk => ?_) (funext fun jk => isEmptyElim jk.1))
    have h' := congrFun h jk
    have h2 : inc2 δ h0 hmono ((w : (blocks A δ h0 hmono) 0).1 jk) = 0 :=
      inclH_injective (le_refl (0 : ℝ)) (le_refl (0 : ℝ)) (Nat.zero_le 2) le_rfl
        (h'.trans (map_zero _).symm)
    exact inclH_injective (le_refl (0 : ℝ)) hd (by norm_num : 2 ≤ 3) h0
      (h2.trans (map_zero _).symm)
  obtain ⟨C, hC⟩ := estimate_of_compact hK L hinj hmain
  exact ⟨C, fun w => by rw [hl2]; exact hC w⟩

end Sphere

end GWMemoir
