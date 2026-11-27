import GWMemoir.LinearCRNodesOpNeck
import GWMemoir.NeckEstimate
import GWMemoir.EllipticEstimateSphere

/-!
# The elliptic estimate for the linearized Cauchy–Riemann operator at a node

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4 (Proposition 4.23,
p. 118, level `0`, `a = 0`), at a constant map from two spheres joined at a node (`twoSpheres`),
with `0 < δ₀ < 2π`: for `D = linCRN`,
`‖ξ‖_{H^{3,δ₀}_c} ≤ C (‖Dξ‖_{H^{2,δ₀}} + ‖Kξ‖)` with `K` compact, so `D` has closed range.

* `mulHW`: multiplication by a compactly supported `χ(s)`, from `H^{m,δ}` to `H^{m,δ'}` for any
  two weights (the derivatives of `χ u` vanish off the support of `χ`).
* `jMat_disc_const_two`: in each disc chart of `S² ⊔ S²`, `j ∂_s = b ∂_t`, `b = ±1` constant,
  through `inl`/`inr` (`jMat_disc_const`).
* `kOpN`: the compact operator, `v ↦ (v_{disc} ∈ H^{2,0}, v_{neck} ∈ H^{2,0}, c_{neck} ∈ ℝ)`
  (Rellich, `isCompactOperator_inclH`, `0 < δ₀`).
* `crOp_eqN`, `estimate_discN`: on the disc blocks the argument of `estimate_disc`, with the
  zeroth-order term `zBlockN` read through `kOpN`.
* `neckRowN_eq`: on the neck block `(j, k)`, the shifted `(∂_s + J(q) ∂_t) v_j` is twice the neck
  row of `D` plus `β'(s - s₀)(v⁺ - c)` read through `kOpN` (compactly supported in `s`);
  `estimate_neckN`, from `neck_estimate` (no lower-order term, `0 < δ₀ < 2π`).
* **`linCRN_estimate_twoSpheres`**, **`linCRN_isClosed_range_twoSpheres`** (Peetre,
  `isClosed_range_of_estimate`; the kernel is finite-dimensional, `linCRN_ker_equiv`).
* **`linCRN_isFredholm_twoSpheres`**: with the density of the range as hypothesis, `D` is
  surjective and Fredholm of index `dim E`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology NNReal
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. Multiplication by a compactly supported `χ(s)` changes the weight -/

section MulW

variable {m : ℕ} {δ δ' : ℝ} {hδ : 0 ≤ δ} {hδ' : 0 ≤ δ'}

lemma hasCompactSupport_iteratedDeriv_s {χ : ℝ → ℝ} (hc : HasCompactSupport χ) (i : ℕ) :
    HasCompactSupport (iteratedDeriv i χ) := by
  induction i with
  | zero => simpa using hc
  | succ i ih => rw [iteratedDeriv_succ]; exact ih.deriv

lemma memLp_wt_leib_of_supp {χ : ℝ → ℝ} (h : Mult m χ) (hc : HasCompactSupport χ)
    {G : ℕ → ℕ → ℝ × ℝ → ℝ} (hG : ∀ a b, MemLp (G a b) 2 cyl) (a b : ℕ) :
    MemLp (fun x => wt δ' x * leib χ G a b x) 2 cyl := by
  have e : (fun x => wt δ' x * leib χ G a b x) = fun x => ∑ i ∈ Finset.range (a + 1),
      (a.choose i : ℝ) * ((Real.exp (δ' * |x.1|) * iteratedDeriv i χ x.1) * G (a - i) b x) := by
    funext x; simp only [leib, Finset.mul_sum, wt]; refine Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  refine memLp_finsetSum _ fun i _ => ?_
  have hcont : Continuous fun s : ℝ => Real.exp (δ' * |s|) * iteratedDeriv i χ s :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
      (contDiff_iteratedDeriv h.smooth i).continuous
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support
    ((hasCompactSupport_iteratedDeriv_s hc i).mul_left)
  exact (memLp_mul ((hcont.comp continuous_fst).aestronglyMeasurable)
    (fun x => by simpa [Real.norm_eq_abs] using hC x.1) (hG _ _)).const_mul _

lemma mulχ_mem_of_supp {χ : ℝ → ℝ} (h : Mult m χ) (hc : HasCompactSupport χ) (u : Hsub m hδ) :
    mulχ χ h u ∈ Hsub m hδ' :=
  fun a b hab => ⟨_, mulχ_hwd h u hab, memLp_wt_leib_of_supp h hc (Gu_memLp u) a b⟩

/-- Multiplication by a compactly supported `χ(s)`, `H^{m,δ} → H^{m,δ'}` (closed graph). -/
def mulHW (χ : ℝ → ℝ) (h : Mult m χ) (hc : HasCompactSupport χ) :
    H m hδ →L[ℝ] H m hδ' :=
  let L : H m hδ →ₗ[ℝ] H m hδ' :=
    { toFun := fun u => (⟨mulχ χ h (valCLM m hδ u), mulχ_mem_of_supp h hc (H.toSub u)⟩ :
        Hsub m hδ')
      map_add' := fun u v => valCLM_injective (by
        change mulχ χ h (valCLM m hδ (u + v)) = mulχ χ h (valCLM m hδ u) + mulχ χ h (valCLM m hδ v)
        rw [map_add, map_add])
      map_smul' := fun c u => valCLM_injective (by
        change mulχ χ h (valCLM m hδ (c • u)) = c • mulχ χ h (valCLM m hδ u)
        rw [map_smul, map_smul]) }
  ⟨L, L.continuous_of_seq_closed_graph fun u x y hu hy => by
    apply valCLM_injective
    have h1 := ((valCLM m hδ').continuous.tendsto y).comp hy
    have h2 := (((mulχ χ h).comp (valCLM m hδ)).continuous.tendsto x).comp hu
    exact tendsto_nhds_unique h1 h2⟩

lemma val_mulHW (χ : ℝ → ℝ) (h : Mult m χ) (hc : HasCompactSupport χ) (u : H m hδ) :
    valCLM m hδ' (mulHW (hδ' := hδ') χ h hc u) = mulχ χ h (valCLM m hδ u) := rfl

end MulW

/-! ## 2. Compactness of a product -/

section CompactProd

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma isCompactOperator_prodN {f : X →L[ℝ] Y} {g : X →L[ℝ] Z} (hf : IsCompactOperator f)
    (hg : IsCompactOperator g) : IsCompactOperator (f.prod g) := by
  obtain ⟨K, hK, hKn⟩ := hf
  obtain ⟨K', hK', hKn'⟩ := hg
  refine ⟨K ×ˢ K', hK.prod hK', ?_⟩
  have : (⇑(f.prod g)) ⁻¹' (K ×ˢ K') = f ⁻¹' K ∩ g ⁻¹' K' := by ext x; simp
  rw [this]
  exact Filter.inter_mem hKn hKn'

end CompactProd

/-! ## 3. `j` in the disc charts of `S² ⊔ S²` -/

section JTwo

lemma discPt_inl_two (z : S2) (ε : ℝ) (p : ℝ × ℝ) :
    twoSpheres.discPt (Sum.inl z) ε p = Sum.inl (sphere3.discPt z ε p) := by
  change (extChartAt 𝓘(ℝ, E2) (Sum.inl z : S22)).symm
    (extChartAt 𝓘(ℝ, E2) (Sum.inl z : S22) (Sum.inl z) + _) =
      Sum.inl ((extChartAt 𝓘(ℝ, E2) z).symm (extChartAt 𝓘(ℝ, E2) z z + _))
  rw [extChartAt_inl_symm, extChartAt_inl_apply]
  rfl

lemma discPt_inr_two (z : S2) (ε : ℝ) (p : ℝ × ℝ) :
    twoSpheres.discPt (Sum.inr z) ε p = Sum.inr (sphere3.discPt z ε p) := by
  change (extChartAt 𝓘(ℝ, E2) (Sum.inr z : S22)).symm
    (extChartAt 𝓘(ℝ, E2) (Sum.inr z : S22) (Sum.inr z) + _) =
      Sum.inr ((extChartAt 𝓘(ℝ, E2) z).symm (extChartAt 𝓘(ℝ, E2) z z + _))
  rw [extChartAt_inr_symm, extChartAt_inr_apply]
  rfl

lemma jMat_inl_two (z y : S2) :
    jMat (X := twoSpheres) (Sum.inl z) (Sum.inl y) = jMat (X := sphere3) z y := by
  simp only [jMat]
  erw [tangentCoordChange_inl (I := 𝓘(ℝ, E2)) (M' := S2) y z y,
    tangentCoordChange_inl (I := 𝓘(ℝ, E2)) (M' := S2) z y y]
  rfl

lemma jMat_inr_two (z y : S2) :
    jMat (X := twoSpheres) (Sum.inr z) (Sum.inr y) = jMat (X := sphere3) z y := by
  simp only [jMat]
  erw [tangentCoordChange_inr (I := 𝓘(ℝ, E2)) (M := S2) y z y,
    tangentCoordChange_inr (I := 𝓘(ℝ, E2)) (M := S2) z y y]
  rfl

/-- **In each disc chart of `S² ⊔ S²`, `j ∂_s = b ∂_t`, `b = ±1` constant.** -/
theorem jMat_disc_const_two (z : twoSpheres.S) (ε : ℝ) : ∃ b : ℝ, b ^ 2 = 1 ∧ ∀ p : ℝ × ℝ,
    jMat (X := twoSpheres) z (twoSpheres.discPt z ε p) (EuclideanSpace.single 0 1) =
      b • EuclideanSpace.single 1 1 := by
  rcases z with z | z
  · obtain ⟨b, hb, h⟩ := jMat_disc_const z ε
    exact ⟨b, hb, fun p => by rw [discPt_inl_two]; erw [jMat_inl_two]; exact h p⟩
  · obtain ⟨b, hb, h⟩ := jMat_disc_const z ε
    exact ⟨b, hb, fun p => by rw [discPt_inr_two]; erw [jMat_inr_two]; exact h p⟩

end JTwo

/-! ## 4. The compact operator and the zeroth-order term -/

section Ops

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)} (G : GlueDataN A)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- The target of the compact operator: the disc blocks and the neck remainders in `H^{2,0}`,
the neck constants in `ℝ`. -/
abbrev KTgt (A : SectionAtlas (E := E) twoSpheres (fun _ => q)) : Type :=
  (Fin A.nd × Fin (Module.finrank ℝ E) → H 2 (le_refl (0 : ℝ))) ×
    ((Fin A.nn × Fin (Module.finrank ℝ E) → H 2 (le_refl (0 : ℝ))) ×
      (Fin A.nn × Fin (Module.finrank ℝ E) → ℝ))

/-- **The compact operator** `v ↦ (v_{disc} ∈ H^{2,0}, v_{neck} ∈ H^{2,0}, c_{neck})`. -/
def kOpN : (blocks A δ h0 hmono) 0 →L[ℝ] KTgt A :=
  (ContinuousLinearMap.pi fun ik => (inc2 δ h0 hmono).comp (secProj δ h0 hmono ik)).prod
    ((ContinuousLinearMap.pi fun jk => (inc2 δ h0 hmono).comp (neckW δ h0 hmono jk)).prod
      (ContinuousLinearMap.pi fun jk => neckC δ h0 hmono jk))

theorem isCompactOperator_kOpN (hδ : 0 < δ 0) :
    IsCompactOperator (kOpN (A := A) δ h0 hmono) := by
  have hi : IsCompactOperator (inc2 δ h0 hmono) :=
    isCompactOperator_inclH (m := 2) (le_refl (0 : ℝ)) (Neck.δ_nonneg δ h0 hmono 0) hδ
  refine isCompactOperator_prodN (isCompactOperator_pi fun ik => ?_)
    (isCompactOperator_prodN (isCompactOperator_pi fun jk => ?_) ?_)
  · rw [ContinuousLinearMap.coe_comp]; exact hi.comp_clm _
  · rw [ContinuousLinearMap.coe_comp]; exact hi.comp_clm _
  · exact isCompactOperator_of_finiteDimensional_range _

/-- The zeroth-order term `zBlockN` read through `kOpN`, in `H^{2,0}`. -/
def zKN (o : Ix A) : KTgt A →L[ℝ] H 2 (le_refl (0 : ℝ)) :=
  ∑ i', ((G.D o.1 i').op 2 (le_refl 0)
      (contDiff_coefZ twoSpheres_chartsOnto o.2.1 (G.ρ i') _ _ _ _ (G.hρ i'))
      (G.hsZ twoSpheres_chartsOnto o.2.1 o.1 i') (le_refl 0)).comp
        ((ContinuousLinearMap.proj (i', o.2.2)).comp (ContinuousLinearMap.fst ℝ _ _)) +
  ∑ j, ∑ a, ((G.Dn o.1 j a).op 2 (le_refl 0) (G.cN_smooth o.2.1 o.1 j a)
      (G.cN_supp o.2.1 o.1 j a) (le_refl 0)).comp
        ((Neck.shH 0 (G.θ a)).comp ((ContinuousLinearMap.proj (j, o.2.2)).comp
          ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))) +
  ∑ j, ((ContinuousLinearMap.proj (j, o.2.2)).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))).smulRight
    (toHdisc (contDiff_cstD twoSpheres_chartsOnto G o.2.1 o.1 j) (tsupport_cstD G o.2.1 o.1 j) 2
      (le_refl 0))

lemma valCLM_shH {m : ℕ} {d : ℝ} {hd : 0 ≤ d} (R ϑ : ℝ) (u : H m hd) :
    valCLM m hd (Neck.shH R ϑ u) = Neck.shLp R ϑ (valCLM m hd u) := rfl

lemma valCLM_op (D : ChartChange) {k : ℕ} {d d' : ℝ} (hd : 0 ≤ d) {a : ℝ × ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (haK : tsupport a ⊆ D.K) (hd' : 0 ≤ d') (u : H k hd) :
    valCLM k hd' (D.op k hd ha haK hd' u) = D.compMul a (valCLM k hd u) :=
  ChartChange.val_op ha haK hd' u

lemma val_zKN (o : Ix A) (v : (blocks A δ h0 hmono) 0) :
    H.val (zKN G o (kOpN δ h0 hmono v)) =
      H.val (zBlockN twoSpheres_chartsOnto G δ h0 hmono o v) := by
  change valCLM 2 _ (zKN G o (kOpN δ h0 hmono v)) =
    valCLM 2 _ (zBlockN twoSpheres_chartsOnto G δ h0 hmono o v)
  simp only [zKN, zBlockN, add_apply, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_add, map_sum,
    map_smul]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun i' _ => ?_
    rw [valCLM_op, valCLM_op]; rfl
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    rw [valCLM_op, valCLM_op]; rfl

end Ops

/-! ## 5. The disc rows -/

section Disc

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  (G : GlueDataN A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

variable {δ h0 hmono} in
/-- The projection term of `D` on the block `(i, 0, k)`: `b χ ∑_l J_{kl} R_{i,1,l}`. -/
lemma val_fOp_i0kN {i : Fin A.nd} {b : ℝ} (hb : ∀ p, jMat (X := twoSpheres) (A.center i)
      (twoSpheres.discPt (A.center i) (A.ε i) p) (EuclideanSpace.single 0 1) =
        b • EuclideanSpace.single 1 1)
    (y : (fibreBlocks A δ h0 hmono) 0) (k : Fin (Module.finrank ℝ E)) :
    H.val ((fOp δ h0 hmono (fun _ _ => idCC) (aPI A (J.J q))
      (fun _ _ => contDiff_aP twoSpheres_chartsOnto (J.J q) _ _ _ _ _ _)
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
  + b ∑_l J_{kl} ((∂_t χ) v_l + χ Z_{i,1,l})`, with `Z` read through `kOpN`. -/
theorem crOp_eqN (v : (blocks A δ h0 hmono) 0)
    (hχ : ∀ jk, idCC.compMul chiP (H.val (v.1 jk)) = H.val (v.1 jk)) {i : Fin A.nd} {b : ℝ}
    (hb : ∀ p, jMat (X := twoSpheres) (A.center i) (twoSpheres.discPt (A.center i) (A.ε i) p)
      (EuclideanSpace.single 0 1) = b • EuclideanSpace.single 1 1)
    (k : Fin (Module.finrank ℝ E)) :
    crOp 2 (fun k l => b * Jc (J.J q) k l) (fun l => inc3 δ h0 hmono (v.1 (i, l))) k =
      (2 * A.ε i) • inc22 δ h0 hmono
          ((linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v).1 (i, 0, k)) +
        zKN G (i, 0, k) (kOpN δ h0 hmono v) + ∑ l, (b * Jc (J.J q) k l) •
          (dtChiOp (inc2 δ h0 hmono (v.1 (i, l))) +
            chiOp (zKN G (i, 1, l) (kOpN δ h0 hmono v))) := by
  apply valCLM_injective (m := 2) (hδ := le_refl (0 : ℝ))
  have hε : A.ε i ≠ 0 := (A.ε_pos i).ne'
  set hd := Neck.δ_nonneg δ h0 hmono 0
  set y := rOpN twoSpheres_chartsOnto G δ h0 hmono v
  have hD : valCLM 2 (le_refl 0) (inc22 δ h0 hmono
      ((linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v).1 (i, 0, k))) =
      (1 / 2 : ℝ) • (H.val (y.1 (i, 0, k)) + H.val ((fOp δ h0 hmono (fun _ _ => idCC)
        (aPI A (J.J q)) (fun _ _ => contDiff_aP twoSpheres_chartsOnto (J.J q) _ _ _ _ _ _)
        (fun _ _ => tsupport_aP (J.J q) _ _ _ _ _ _) (srcP A) 0 y).1 (i, 0, k))) := rfl
  rw [val_fOp_i0kN J hb y k] at hD
  have hR : ∀ o : Ix A, H.val (y.1 o) = (A.ε o.1)⁻¹ • (valCLM 2 hd (dH δ h0 hmono o.2.1
      (v.1 (o.1, o.2.2))) - valCLM 2 (le_refl 0) (zKN G o (kOpN δ h0 hmono v))) := fun o => by
    change valCLM 2 hd ((A.ε o.1)⁻¹ • (_ - _)) = _
    rw [map_smul, map_sub]
    congr 2
    exact (val_zKN G δ h0 hmono o v).symm
  have a1 : ∀ l, valCLM 2 (le_refl 0) (dsH 2 (le_refl 0) (inc3 δ h0 hmono (v.1 (i, l)))) =
      valCLM 2 hd (dH δ h0 hmono 0 (v.1 (i, l))) := fun l => val_dsH_inclH _ _ _ _
  have a2 : ∀ l, valCLM 2 (le_refl 0) (dtH 2 (le_refl 0) (inc3 δ h0 hmono (v.1 (i, l)))) =
      valCLM 2 hd (dH δ h0 hmono 1 (v.1 (i, l))) := fun l => val_dtH_inclH _ _ _ _
  have a5 : ∀ l, valCLM 2 (le_refl 0) (dtChiOp (inc2 δ h0 hmono (v.1 (i, l)))) =
      idCC.compMul dtChiP (valCLM 3 hd (v.1 (i, l))) := fun l =>
    ChartChange.val_op contDiff_dtChiP tsupport_dtChiP (le_refl 0) _
  have a6 : ∀ l, valCLM 2 (le_refl 0) (chiOp (zKN G (i, 1, l) (kOpN δ h0 hmono v))) =
      idCC.compMul chiP (valCLM 2 (le_refl 0) (zKN G (i, 1, l) (kOpN δ h0 hmono v))) := fun l =>
    ChartChange.val_op contDiff_chiP tsupport_chiP (le_refl 0) _
  have a7 : ∀ l, idCC.compMul chiP (valCLM 2 hd (dH δ h0 hmono 1 (v.1 (i, l)))) =
      valCLM 2 hd (dH δ h0 hmono 1 (v.1 (i, l))) - idCC.compMul dtChiP (valCLM 3 hd (v.1 (i, l))) :=
    fun l => eq_sub_of_add_eq' (val_dtH_of_chiP (v.1 (i, l)) (hχ (i, l))).symm
  simp only [crOp, map_add, map_sum, map_smul]
  rw [hD]
  simp only [hR, a1, a2, a5, a6, map_smul, map_sub, a7]
  set S := valCLM 2 hd (dH δ h0 hmono 0 (v.1 (i, k)))
  set Z0 := valCLM 2 (le_refl 0) (zKN G (i, 0, k) (kOpN δ h0 hmono v))
  have hsum : ∑ l, (b * Jc (J.J q) k l) • (A.ε i)⁻¹ • (valCLM 2 hd (dH δ h0 hmono 1 (v.1 (i, l))) -
      idCC.compMul dtChiP (valCLM 3 hd (v.1 (i, l))) -
        idCC.compMul chiP (valCLM 2 (le_refl 0) (zKN G (i, 1, l) (kOpN δ h0 hmono v)))) =
      (A.ε i)⁻¹ • (∑ l, (b * Jc (J.J q) k l) • valCLM 2 hd (dH δ h0 hmono 1 (v.1 (i, l))) -
        ∑ l, (b * Jc (J.J q) k l) • (idCC.compMul dtChiP (valCLM 3 hd (v.1 (i, l))) +
          idCC.compMul chiP (valCLM 2 (le_refl 0) (zKN G (i, 1, l) (kOpN δ h0 hmono v))))) := by
    rw [← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_comm, sub_sub, smul_sub]
  rw [hsum]
  rw [← smul_add, smul_smul, smul_smul, show 2 * A.ε i * (1 / 2) * (A.ε i)⁻¹ = 1 by
    field_simp, one_smul]
  abel

/-- The right side of `crOp_eqN` as a bounded operator of `(D v, kOpN v)`. -/
def phiOpN (i : Fin A.nd) (b : ℝ) (k : Fin (Module.finrank ℝ E)) :
    (fibreBlocks A δ h0 hmono) 0 × KTgt A →L[ℝ] H 2 (le_refl (0 : ℝ)) :=
  ((2 * A.ε i) • ((inc22 δ h0 hmono).comp ((ContinuousLinearMap.proj (i, 0, k)).comp
      (ContinuousLinearMap.fst ℝ _ _)))).comp (ContinuousLinearMap.fst ℝ _ _) +
    (zKN G (i, 0, k)).comp (ContinuousLinearMap.snd ℝ _ _) +
    ∑ l, (b * Jc (J.J q) k l) • ((dtChiOp.comp ((ContinuousLinearMap.proj (i, l)).comp
      (ContinuousLinearMap.fst ℝ _ _)) + chiOp.comp (zKN G (i, 1, l))).comp
        (ContinuousLinearMap.snd ℝ _ _))

variable {δ h0 hmono} in
/-- **The estimate against `H^{2,0}`** on the disc block `i`:
`‖v_{i,k}‖_{H^{3,0}} ≤ C (‖D v‖ + ‖kOpN v‖)`, for `v = χ v`. -/
lemma estimate_discN (i : Fin A.nd) : ∃ C : ℝ, ∀ v : {v : (blocks A δ h0 hmono) 0 //
    ∀ jk, idCC.compMul chiP (H.val (v.1 jk)) = H.val (v.1 jk)}, ∀ k,
      ‖inc3 δ h0 hmono (v.1.1 (i, k))‖ ≤
        C * (‖linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v.1‖ + ‖kOpN δ h0 hmono v.1‖) := by
  obtain ⟨b, hb2, hb⟩ := jMat_disc_const_two (A.center i) (A.ε i)
  obtain ⟨C0, hC0⟩ := cyl_estimate _ (isCxMat_Jc (J.sq q) hb2) 2
  set M := (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) +
    ∑ l, ‖phiOpN J G δ h0 hmono i b l‖
  refine ⟨max C0 0 * M, fun ⟨v, hχ⟩ k => ?_⟩
  set N := ‖linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v‖ + ‖kOpN δ h0 hmono v‖
  have hN : 0 ≤ N := by positivity
  have h1 : ∀ l, ‖H.val (inc3 δ h0 hmono (v.1 (i, l)))‖ ≤ N := fun l => by
    have e : ‖H.val (inc3 δ h0 hmono (v.1 (i, l)))‖ =
      ‖H.val ((kOpN δ h0 hmono v).1 (i, l))‖ := rfl
    rw [e, ← norm_wdv_idx0]
    exact (norm_wdv_le _ _).trans ((norm_le_pi_norm (kOpN δ h0 hmono v).1 (i, l)).trans
      ((norm_fst_le _).trans (le_add_of_nonneg_left (norm_nonneg _))))
  have h2 : ∀ l, ‖crOp 2 (fun k l => b * Jc (J.J q) k l)
      (fun l => inc3 δ h0 hmono (v.1 (i, l))) l‖ ≤ ‖phiOpN J G δ h0 hmono i b l‖ * N := by
    intro l
    have e := crOp_eqN J G v hχ hb l
    have e' : crOp 2 (fun k l => b * Jc (J.J q) k l) (fun l => inc3 δ h0 hmono (v.1 (i, l))) l =
        phiOpN J G δ h0 hmono i b l
          (linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v, kOpN δ h0 hmono v) := by
      rw [e, phiOpN, add_apply, add_apply,
        sum_apply]
      exact congrArg₂ _ rfl (Finset.sum_congr rfl fun l _ => rfl)
    rw [e']
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
/-- On `twoSpheres` every section has `v = χ v` on its disc blocks (`discCut χ = discCut`). -/
lemma chiP_mul_of_memN {v : (blocks A δ h0 hmono) 0} (hv : v ∈ sectionSpace A δ h0 hmono)
    (jk : Fin A.nd × Fin (Module.finrank ℝ E)) :
    idCC.compMul chiP (H.val (v.1 jk)) = H.val (v.1 jk) := by
  rw [sectionSpace_eq_sectionsSub continuous_const A δ h0 hmono] at hv
  obtain ⟨η, -, -, hr⟩ := hv
  obtain ⟨i, k⟩ := jk
  refine Lp.ext ?_
  filter_upwards [idCC.coeFn_compMul contDiff_chiP.continuous tsupport_chiP (H.val (v.1 (i, k))),
    hr.1 i k] with x h1 h2
  rw [h1]
  change chiP x * H.val (discBlock v i k) x = H.val (discBlock v i k) x
  rw [h2, discRep, ← mul_assoc, mul_comm (chiP x), discCut_mul_chiP]

end Disc

/-! ## 6. The neck rows -/

section Neck

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  (G : GlueDataN A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- The shifted `(∂_s + J₀ ∂_t) v_j (s - s₀, t)` of the neck row `(j, k)`. -/
def xBlk (J₀ : E →L[ℝ] E) (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) 0 →L[ℝ] H 2 (Neck.δ_nonneg δ h0 hmono 0) :=
  (Neck.shH (A.s0 jk.1) 0).comp
      ((dsH 2 (Neck.δ_nonneg δ h0 hmono 0)).comp (neckW δ h0 hmono jk)) +
    ∑ l, Jm J₀ jk.2 l • (Neck.shH (A.s0 jk.1) 0).comp
      ((dtH 2 (Neck.δ_nonneg δ h0 hmono 0)).comp (neckW δ h0 hmono (jk.1, l)))

/-- The term `β'(s - s₀)(v⁺ - c)` of the neck row `(j, k)`. -/
def psiBlk (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    (blocks A δ h0 hmono) 0 →L[ℝ] H 2 (Neck.δ_nonneg δ h0 hmono 0) :=
  ∑ i, ∑ a, (Neck.shH 0 (G.θ a)).comp
      (((G.Dd jk.1 i a).op 2 (Neck.δ_nonneg δ h0 hmono 0) (G.cD_smooth jk.1 i a)
        (G.cD_supp jk.1 i a) (Neck.δ_nonneg δ h0 hmono 0)).comp
          ((incl32 δ h0 hmono).comp (secProj δ h0 hmono (i, jk.2)))) +
    (Neck.mulHL (mulN (A.s0 jk.1) (G.χ jk.1))
      (mult_mulN (G.χ_smooth jk.1) (G.χ_zero jk.1) 2)).comp
        ((Neck.shH (A.s0 jk.1) 0).comp ((incl32 δ h0 hmono).comp (neckW δ h0 hmono jk))) -
    (neckC δ h0 hmono jk).smulRight
      (toH 2 (Neck.δ_nonneg δ h0 hmono 0) (isTest_cstN (s₀ := A.s0 jk.1) (G.χ_smooth jk.1)))

lemma neckRowN_def (J₀ : E →L[ℝ] E) (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    neckRowN G δ h0 hmono J₀ jk =
      (1 / 2 : ℝ) • xBlk δ h0 hmono J₀ jk - (1 / 2 : ℝ) • psiBlk G δ h0 hmono jk := rfl

lemma xBlk_apply (J₀ : E →L[ℝ] E) (jk : Fin A.nn × Fin (Module.finrank ℝ E))
    (v : (blocks A δ h0 hmono) 0) :
    xBlk δ h0 hmono J₀ jk v = Neck.shH (A.s0 jk.1) 0 (crOpW 2 (Neck.δ_nonneg δ h0 hmono 0)
      (Jc J₀) (fun l => neckW δ h0 hmono (jk.1, l) v) jk.2) := by
  simp only [xBlk, crOpW, add_apply, sum_apply,
    smul_apply, ContinuousLinearMap.comp_apply, map_add, map_sum, map_smul]
  rfl

/-- **The neck row of `D`**: the shifted `(∂_s + J₀ ∂_t) v_j` is twice the neck row plus
`β'(s - s₀)(v⁺ - c)`. -/
theorem neckRowN_eq (J₀ : E →L[ℝ] E) (jk : Fin A.nn × Fin (Module.finrank ℝ E))
    (v : (blocks A δ h0 hmono) 0) :
    Neck.shH (A.s0 jk.1) 0 (crOpW 2 (Neck.δ_nonneg δ h0 hmono 0) (Jc J₀)
      (fun l => neckW δ h0 hmono (jk.1, l) v) jk.2) =
      (2 : ℝ) • neckRowN G δ h0 hmono J₀ jk v + psiBlk G δ h0 hmono jk v := by
  rw [← xBlk_apply, neckRowN_def, sub_apply, smul_apply,
    smul_apply]
  module

/-- The term `β'(s - s₀)(v⁺ - c)` read through `kOpN`: its pieces are compactly supported. -/
def psiN (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    KTgt A →L[ℝ] H 2 (Neck.δ_nonneg δ h0 hmono 0) :=
  ∑ i, ∑ a, (Neck.shH 0 (G.θ a)).comp
      (((G.Dd jk.1 i a).op 2 (le_refl 0) (G.cD_smooth jk.1 i a)
        (G.cD_supp jk.1 i a) (Neck.δ_nonneg δ h0 hmono 0)).comp
          ((ContinuousLinearMap.proj (i, jk.2)).comp (ContinuousLinearMap.fst ℝ _ _))) +
    (mulHW (mulN (A.s0 jk.1) (G.χ jk.1)) (mult_mulN (G.χ_smooth jk.1) (G.χ_zero jk.1) 2)
      (hasCompactSupport_mulN (G.χ_zero jk.1))).comp
        ((Neck.shH (A.s0 jk.1) 0).comp ((ContinuousLinearMap.proj jk).comp
          ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))) -
    ((ContinuousLinearMap.proj jk).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))).smulRight
      (toH 2 (Neck.δ_nonneg δ h0 hmono 0) (isTest_cstN (s₀ := A.s0 jk.1) (G.χ_smooth jk.1)))

lemma psiN_eq (jk : Fin A.nn × Fin (Module.finrank ℝ E)) (v : (blocks A δ h0 hmono) 0) :
    psiN G δ h0 hmono jk (kOpN δ h0 hmono v) = psiBlk G δ h0 hmono jk v := by
  simp only [psiN, psiBlk, add_apply, sub_apply,
    sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply]
  congr 2
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
    congr 1
    apply valCLM_injective
    rw [valCLM_op, valCLM_op]; rfl

variable (J : AlmostComplexStructure E Q) in
/-- **The estimate on the neck blocks** (`neck_estimate`, `0 < δ₀ < 2π`):
`‖v_{j,k}‖_{H^{3,δ₀}} ≤ C (‖D v‖ + ‖kOpN v‖)`. -/
theorem estimate_neckN (hδ : 0 < δ 0) (hδ' : δ 0 < 2 * Real.pi) : ∃ C : ℝ,
    ∀ jk (v : (blocks A δ h0 hmono) 0), ‖neckW δ h0 hmono jk v‖ ≤
      C * (‖linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v‖ + ‖kOpN δ h0 hmono v‖) := by
  set hd := Neck.δ_nonneg δ h0 hmono 0
  have hJ : IsCxMat (Jc (J.J q)) := by
    have := isCxMat_Jc (J.sq q) (b := 1) (by norm_num)
    simpa only [one_mul] using this
  obtain ⟨CN, hCN⟩ := neck_estimate (hδ := hd) hJ hδ hδ' 2
  refine exists_common_bound (ι := Fin A.nn × Fin (Module.finrank ℝ E))
    (f := fun jk v => ‖neckW δ h0 hmono jk v‖)
    (g := fun v => ‖linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v‖ + ‖kOpN δ h0 hmono v‖)
    (fun v => by positivity) fun jk => ?_
  obtain ⟨j, k⟩ := jk
  set Sh : H 2 hd →L[ℝ] H 2 hd := Neck.shH (-(A.s0 j)) (-0)
  refine ⟨max CN 0 * ∑ l, ‖Sh‖ * (2 + ‖psiN G δ h0 hmono (j, l)‖), fun v => ?_⟩
  set N := ‖linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v‖ + ‖kOpN δ h0 hmono v‖
  have hN : 0 ≤ N := by positivity
  set g : Fin (Module.finrank ℝ E) → H (2 + 1) hd := fun l => neckW δ h0 hmono (j, l) v
  have hl : ∀ l, ‖crOpW 2 hd (Jc (J.J q)) g l‖ ≤ ‖Sh‖ * (2 + ‖psiN G δ h0 hmono (j, l)‖) * N := by
    intro l
    have e : crOpW 2 hd (Jc (J.J q)) g l = Sh ((2 : ℝ) • neckRowN G δ h0 hmono (J.J q) (j, l) v +
        psiN G δ h0 hmono (j, l) (kOpN δ h0 hmono v)) := by
      rw [psiN_eq, ← neckRowN_eq G δ h0 hmono (J.J q) (j, l) v]
      exact (Neck.shH_shH _ _ _).symm
    have hrow : ‖neckRowN G δ h0 hmono (J.J q) (j, l) v‖ ≤
        ‖linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v‖ := by
      have e2 : neckRowN G δ h0 hmono (J.J q) (j, l) v =
          (linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v).2 (j, l) := rfl
      rw [e2]
      exact (norm_le_pi_norm _ (j, l)).trans (norm_snd_le _)
    have hpsi := (psiN G δ h0 hmono (j, l)).le_opNorm (kOpN δ h0 hmono v)
    rw [e]
    refine (Sh.le_opNorm _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hk : ‖kOpN δ h0 hmono v‖ ≤ N := le_add_of_nonneg_left (norm_nonneg _)
    have hD : ‖linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v‖ ≤ N :=
      le_add_of_nonneg_right (norm_nonneg _)
    nlinarith [norm_nonneg (psiN G δ h0 hmono (j, l)), norm_nonneg (kOpN δ h0 hmono v)]
  have hS : ∑ l, ‖crOpW 2 hd (Jc (J.J q)) g l‖ ≤
      (∑ l, ‖Sh‖ * (2 + ‖psiN G δ h0 hmono (j, l)‖)) * N := by
    rw [Finset.sum_mul]; exact Finset.sum_le_sum fun l _ => hl l
  have hS0 : 0 ≤ ∑ l, ‖crOpW 2 hd (Jc (J.J q)) g l‖ := by positivity
  calc ‖neckW δ h0 hmono (j, k) v‖ = ‖g k‖ := rfl
    _ ≤ CN * ∑ l, ‖crOpW 2 hd (Jc (J.J q)) g l‖ := hCN g k
    _ ≤ max CN 0 * ∑ l, ‖crOpW 2 hd (Jc (J.J q)) g l‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hS0
    _ ≤ max CN 0 * ((∑ l, ‖Sh‖ * (2 + ‖psiN G δ h0 hmono (j, l)‖)) * N) :=
        mul_le_mul_of_nonneg_left hS (le_max_right _ _)
    _ = _ := by ring

end Neck

/-! ## 7. The estimate, closed range, Fredholm -/

section Main

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  (hsm : NeckSmooth A) (G : GlueDataN A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

instance sectionSpace_completeSpace_twoSpheres : CompleteSpace (sectionSpace A δ h0 hmono) :=
  (isClosed_sectionSpace A δ h0 hmono).completeSpace_coe

/-- `D = linCRN` on `twoSpheres`, `J₀ = J(q)`. -/
abbrev linCRN2 : sectionSpace A δ h0 hmono →L[ℝ] fibreSpace J A δ h0 hmono :=
  linCRN twoSpheres_chartsOnto hsm G δ h0 hmono J

/-- The compact operator on the section space. -/
abbrev kSecN : sectionSpace A δ h0 hmono →L[ℝ] KTgt A :=
  (kOpN δ h0 hmono).comp (sectionSpace A δ h0 hmono).subtypeL

theorem isCompactOperator_kSecN (hδ : 0 < δ 0) : IsCompactOperator (kSecN (A := A) δ h0 hmono) := by
  rw [ContinuousLinearMap.coe_comp]
  exact (isCompactOperator_kOpN δ h0 hmono hδ).comp_clm _

instance finiteDimensional_ker_linCRN2 : FiniteDimensional ℝ (linCRN2 J hsm G δ h0 hmono).ker :=
  LinearEquiv.finiteDimensional (linCRN_ker_equiv J hsm G δ h0 hmono)

/-- **The elliptic estimate at a node** (Memoir §4, Prop 4.23, `a = 0`, two spheres joined at a
node, `0 < δ₀ < 2π`): `‖ξ‖_{H^{3,δ₀}_c} ≤ C (‖Dξ‖_{H^{2,δ₀}} + ‖Kξ‖)`, with `K = kSecN` compact
(`isCompactOperator_kSecN`). The atlas data `NeckSmooth A`, `GlueDataN A` exist for every `q`
(`exists_glueDataN`). -/
theorem linCRN_estimate_twoSpheres (hδ : 0 < δ 0) (hδ' : δ 0 < 2 * Real.pi) :
    ∃ C : ℝ, ∀ w : sectionSpace A δ h0 hmono,
      ‖w‖ ≤ C * (‖linCRN2 J hsm G δ h0 hmono w‖ + ‖kSecN δ h0 hmono w‖) := by
  set hd := Neck.δ_nonneg δ h0 hmono 0
  obtain ⟨C1, hC1⟩ := exists_common_bound (ι := Fin A.nd)
    (f := fun i (x : {v : (blocks A δ h0 hmono) 0 // ∀ jk, idCC.compMul chiP (H.val (v.1 jk)) =
      H.val (v.1 jk)} × Fin (Module.finrank ℝ E)) => ‖inc3 δ h0 hmono (x.1.1.1 (i, x.2))‖)
    (g := fun x => ‖linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) x.1.1‖ +
      ‖kOpN δ h0 hmono x.1.1‖) (fun x => by positivity)
    (fun i => by
      obtain ⟨C, hC⟩ := estimate_discN J G (δ := δ) (h0 := h0) (hmono := hmono) i
      exact ⟨C, fun x => hC x.1 x.2⟩)
  obtain ⟨C2, hC2⟩ := estimate_neckN G δ h0 hmono J hδ hδ'
  set chi3 : H 3 (le_refl (0 : ℝ)) →L[ℝ] H 3 hd :=
    idCC.op 3 (le_refl 0) contDiff_chiP tsupport_chiP hd
  have hχv : ∀ {v : (blocks A δ h0 hmono) 0}, v ∈ sectionSpace A δ h0 hmono → ∀ jk,
      chi3 (inc3 δ h0 hmono (v.1 jk)) = v.1 jk := fun hv jk => by
    apply valCLM_injective (m := 3) (hδ := hd)
    exact (ChartChange.val_op contDiff_chiP tsupport_chiP hd _).trans (chiP_mul_of_memN hv jk)
  set C := ‖chi3‖ * max C1 0 + max C2 0 + 1
  refine ⟨C, fun w => ?_⟩
  have hv := w.2
  set v : (blocks A δ h0 hmono) 0 := (w : (blocks A δ h0 hmono) 0)
  set N := ‖linCRN2 J hsm G δ h0 hmono w‖ + ‖kSecN δ h0 hmono w‖
  have hN : 0 ≤ N := by positivity
  have eN : N = ‖linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v‖ + ‖kOpN δ h0 hmono v‖ := rfl
  have hCN : ∀ {a : ℝ}, a ≤ C → a * N ≤ C * N := fun h => mul_le_mul_of_nonneg_right h hN
  have hc1 : ‖chi3‖ * max C1 0 ≤ C := by
    have := le_max_right C2 0; linarith
  have hc2 : max C2 0 ≤ C := by
    have : 0 ≤ ‖chi3‖ * max C1 0 := mul_nonneg (norm_nonneg _) (le_max_right _ _)
    linarith
  have hc3 : (1 : ℝ) ≤ C := by
    have : 0 ≤ ‖chi3‖ * max C1 0 := mul_nonneg (norm_nonneg _) (le_max_right _ _)
    linarith [le_max_right C2 0]
  have hdisc : ∀ jk, ‖v.1 jk‖ ≤ C * N := by
    rintro ⟨i, k⟩
    have h1 := hC1 i (⟨v, chiP_mul_of_memN hv⟩, k)
    have h1' : ‖inc3 δ h0 hmono (v.1 (i, k))‖ ≤ max C1 0 * N := by
      rw [eN]; exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    rw [← hχv hv (i, k)]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    calc ‖chi3‖ * ‖inc3 δ h0 hmono (v.1 (i, k))‖ ≤ ‖chi3‖ * (max C1 0 * N) :=
          mul_le_mul_of_nonneg_left h1' (norm_nonneg _)
      _ = (‖chi3‖ * max C1 0) * N := by ring
      _ ≤ C * N := hCN hc1
  have hneck : ∀ jk, ‖v.2 jk‖ ≤ C * N := by
    intro jk
    have hc : ‖(v.2 jk).1‖ ≤ C * N := by
      have e : (v.2 jk).1 = (kOpN δ h0 hmono v).2.2 jk := rfl
      have : ‖(v.2 jk).1‖ ≤ N := by
        rw [e, eN]
        exact (norm_le_pi_norm _ jk).trans ((norm_snd_le _).trans ((norm_snd_le _).trans
          (le_add_of_nonneg_left (norm_nonneg _))))
      calc ‖(v.2 jk).1‖ ≤ 1 * N := by rw [one_mul]; exact this
        _ ≤ C * N := hCN hc3
    have hr : ‖(v.2 jk).2‖ ≤ C * N := by
      have e : (v.2 jk).2 = neckW δ h0 hmono jk v := rfl
      rw [e]
      calc ‖neckW δ h0 hmono jk v‖ ≤ C2 * N := by rw [eN]; exact hC2 jk v
        _ ≤ max C2 0 * N := mul_le_mul_of_nonneg_right (le_max_left _ _) hN
        _ ≤ C * N := hCN hc2
    exact norm_prod_le_iff.2 ⟨hc, hr⟩
  have hCN0 : 0 ≤ C * N := mul_nonneg (by linarith) hN
  change ‖v‖ ≤ C * N
  exact norm_prod_le_iff.2 ⟨(pi_norm_le_iff_of_nonneg hCN0).2 hdisc,
    (pi_norm_le_iff_of_nonneg hCN0).2 hneck⟩

/-- **`D` has closed range at a node** (Peetre, `isClosed_range_of_estimate`; the kernel is
`E`, `linCRN_ker_equiv`), for `0 < δ₀ < 2π`. -/
theorem linCRN_isClosed_range_twoSpheres (hδ : 0 < δ 0) (hδ' : δ 0 < 2 * Real.pi) :
    IsClosed ((linCRN2 J hsm G δ h0 hmono).range : Set (fibreSpace J A δ h0 hmono)) := by
  obtain ⟨C, hC⟩ := linCRN_estimate_twoSpheres J hsm G δ h0 hmono hδ hδ'
  exact isClosed_range_of_estimate (isCompactOperator_kSecN δ h0 hmono hδ) inferInstance hC

/-- **Closed and dense range: `D` is onto** (as in `cokernelVanishes_of_denseRange`). -/
theorem linCRN_surjective_of_denseRange (hδ : 0 < δ 0) (hδ' : δ 0 < 2 * Real.pi)
    (hd : DenseRange (linCRN2 J hsm G δ h0 hmono)) : Surjective (linCRN2 J hsm G δ h0 hmono) := by
  have hc := linCRN_isClosed_range_twoSpheres J hsm G δ h0 hmono hδ hδ'
  have hr : ((linCRN2 J hsm G δ h0 hmono).range : Set (fibreSpace J A δ h0 hmono)) =
      range (linCRN2 J hsm G δ h0 hmono) := LinearMap.coe_range _
  rw [hr] at hc
  intro y
  have : y ∈ closure (range (linCRN2 J hsm G δ h0 hmono)) := hd.closure_eq ▸ mem_univ y
  rwa [hc.closure_eq] at this

/-- **`D` is Fredholm of index `dim E` at a constant map from two spheres joined at a node**
(Memoir §4, Prop 4.23, p. 118, level `0`, `a = 0`), for `0 < δ₀ < 2π`, given the density of
its range (the hypothesis of `cokernelVanishes_of_denseRange`). -/
theorem linCRN_isFredholm_twoSpheres (hδ : 0 < δ 0) (hδ' : δ 0 < 2 * Real.pi)
    (hd : DenseRange (linCRN2 J hsm G δ h0 hmono)) :
    ContinuousLinearMap.IsFredholm (linCRN2 J hsm G δ h0 hmono) ∧
      fredholmIndex (linCRN2 J hsm G δ h0 hmono) = Module.finrank ℝ E := by
  have hs := linCRN_surjective_of_denseRange J hsm G δ h0 hmono hδ hδ' hd
  have htop : (linCRN2 J hsm G δ h0 hmono).range = ⊤ := LinearMap.range_eq_top.2 hs
  refine ⟨isFredholm_of_banach _ inferInstance ?_ ?_, ?_⟩
  · rw [htop]; exact isClosed_univ
  · rw [htop]; exact Submodule.CoFG.top
  · have htop' : LinearMap.range (linCRN2 J hsm G δ h0 hmono).toLinearMap = ⊤ :=
      LinearMap.range_eq_top (f := (linCRN2 J hsm G δ h0 hmono).toLinearMap) |>.2 hs
    have : Subsingleton (fibreSpace J A δ h0 hmono ⧸
        LinearMap.range (linCRN2 J hsm G δ h0 hmono).toLinearMap) :=
      Submodule.Quotient.subsingleton_iff.2 htop'
    rw [fredholmIndex, linIndex, Module.finrank_zero_of_subsingleton (R := ℝ)
      (M := fibreSpace J A δ h0 hmono ⧸ LinearMap.range (linCRN2 J hsm G δ h0 hmono).toLinearMap),
      Nat.cast_zero, sub_zero]
    exact_mod_cast finrank_linCRN_ker J hsm G δ h0 hmono

end Main

end GWMemoir
