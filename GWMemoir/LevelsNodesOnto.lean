import GWMemoir.LevelsNodesEstimate
import GWMemoir.LevelsNodesDense

/-!
# `D` with nodes on every level: onto, regular, sc-Fredholm

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, Propositions 4.7 (p. 102),
4.8 (p. 104), 4.23 (p. 118), 4.25 (p. 121), at a constant map `u ≡ q` from two spheres joined at a
node (`twoSpheres`), for weights `0 < δ₀ < δ₁ < ⋯` with `δ_m < 2π` for all `m`.

Write `X_m`, `Y_m` for the levels of the section space and of the fibre (`sectionScale`,
`fibreScale`: the closed subspaces `A ∩ (blocks)_m`), and `D_m = crLvN m : X_m → Y_m`, the
operator `linOpNL` of `GWMemoir.LevelsNodesOp`.  The argument is the one of
`GWMemoir.LevelRegularitySphere`:

* `D_0` is onto (`linCRN_isFredholm_twoSpheres_of_glueCharts`); the kernel of every `D_m` is the
  constants (`linOpN_eq_zero_iff`), which lie on every level and are smooth points (`cstLvN`).
* **Regularity at `n` from surjectivity at `n`** (`regularity_of_surjectiveN`): density of the
  range on level `n + 1` (`denseNL`), the open mapping theorem for `D_n`, the kernel correction,
  and the closed range of `ζ ↦ (Dζ, ζ)` from the estimate on level `n + 1`
  (`ellipticEstimateNL`).  Surjectivity at `n + 1` follows (`surjective_succN`).
* `levelRegularity_twoSpheres`: elliptic regularity from level `n` to level `n + 1`.

The densities of the smooth points, the sc-structures and the sc-Fredholm property are in
`GWMemoir.LevelsNodesFredholm`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology NNReal
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. The constants on every level -/

section Const

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
  (hA : IsStdNeck A) (hδ : ∀ m, δ m < 2 * Real.pi)

lemma contMDiff_cstSec (e : E) :
    ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E) ∞ (fun _ => e : Section E twoSpheres) := contMDiff_const

lemma constBlocks_eq_smoothBlocks2 (e : E) (hδ0 : δ 0 < 2 * Real.pi) :
    constBlocks A δ h0 hmono e = smoothBlocks2 δ h0 hmono (contMDiff_cstSec e) hA hδ0 :=
  IsRep.unique' (isRep_constBlocks A e) (isRep_smoothBlocks2 δ h0 hmono (contMDiff_cstSec e) hA hδ0)

/-- The constant section `e` on level `m` of the section space. -/
def cstLvN (m : ℕ) (e : E) : (sectionScale A δ h0 hmono) m :=
  ⟨smoothBlocks2L δ h0 hmono (contMDiff_cstSec e) hA m (hδ m), by
    rw [ScBanach.mem_levelSub, toBase_smoothBlocks2L δ h0 hmono _ hA m (hδ m) (hδ 0)]
    exact smoothNeckRep_mem δ h0 hmono (contMDiff_cstSec e) hA (hδ 0) rfl⟩

lemma toBase_cstLvN (m : ℕ) (e : E) :
    (blocks A δ h0 hmono).toBase m (cstLvN δ h0 hmono hA hδ m e).1 = constBlocks A δ h0 hmono e :=
  (toBase_smoothBlocks2L δ h0 hmono _ hA m (hδ m) (hδ 0)).trans
    (constBlocks_eq_smoothBlocks2 δ h0 hmono hA e (hδ 0)).symm

lemma cstLvN_mem_smoothLvl (m : ℕ) (e : E) :
    (cstLvN δ h0 hmono hA hδ m e).1 ∈ (blocks A δ h0 hmono).smoothLvl m :=
  smoothBlocks2L_mem_smoothLvl δ h0 hmono (contMDiff_cstSec e) hA hδ m

lemma incl_cstLvN (n : ℕ) (e : E) :
    (sectionScale A δ h0 hmono).incl n (cstLvN δ h0 hmono hA hδ (n + 1) e) =
      cstLvN δ h0 hmono hA hδ n e := by
  apply Subtype.ext
  apply (blocks A δ h0 hmono).toBase_injective n
  change (blocks A δ h0 hmono).toBase (n + 1) (cstLvN δ h0 hmono hA hδ (n + 1) e).1 = _
  rw [toBase_cstLvN, toBase_cstLvN]

end Const

/-! ## 2. The level maps -/

section Levels

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q}
  {A : SectionAtlas (E := E) twoSpheres (fun _ => q)} (hsm : NeckSmooth A) (G : GlueDataN A)
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

include hsm in
lemma linOpNL_mem (m : ℕ) {w : (blocks A δ h0 hmono) m}
    (hw : w ∈ (blocks A δ h0 hmono).levelSub (sectionSpace A δ h0 hmono) m) :
    linOpNL twoSpheres_chartsOnto G δ h0 hmono m (J.J q) w ∈
      (fibreBlocks A δ h0 hmono).levelSub (fibreSpace J A δ h0 hmono) m := by
  rw [ScBanach.mem_levelSub, toBase_linOpNL]
  exact linOpN_mem twoSpheres_chartsOnto hsm G J hw

/-- **`D` on level `m`**: `X_m → Y_m`, sections of class `(3+m, δ_m)` to forms of class
`(2+m, δ_m)`. -/
def crLvN (m : ℕ) : (sectionScale A δ h0 hmono) m →L[ℝ] (fibreScale J A δ h0 hmono) m :=
  ((linOpNL twoSpheres_chartsOnto G δ h0 hmono m (J.J q)).comp
    ((blocks A δ h0 hmono).levelSub (sectionSpace A δ h0 hmono) m).subtypeL).codRestrict _
    fun w => linOpNL_mem J hsm G δ h0 hmono m w.2

lemma crLvN_val (m : ℕ) (x : (sectionScale A δ h0 hmono) m) :
    (crLvN J hsm G δ h0 hmono m x).1 = linOpNL twoSpheres_chartsOnto G δ h0 hmono m (J.J q) x.1 :=
  rfl

lemma linOpNL_zero (v : (blocks A δ h0 hmono) 0) :
    linOpNL twoSpheres_chartsOnto G δ h0 hmono 0 (J.J q) v =
      linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) v :=
  toBase_linOpNL twoSpheres_chartsOnto G δ h0 hmono 0 (J.J q) v

/-- The level maps commute with the inclusions. -/
lemma crLvN_incl (n : ℕ) (x : (sectionScale A δ h0 hmono) (n + 1)) :
    (fibreScale J A δ h0 hmono).incl n (crLvN J hsm G δ h0 hmono (n + 1) x) =
      crLvN J hsm G δ h0 hmono n ((sectionScale A δ h0 hmono).incl n x) := by
  apply Subtype.ext
  apply (fibreBlocks A δ h0 hmono).toBase_injective n
  change (fibreBlocks A δ h0 hmono).toBase (n + 1)
      (linOpNL twoSpheres_chartsOnto G δ h0 hmono (n + 1) (J.J q) x.1) =
    (fibreBlocks A δ h0 hmono).toBase n
      (linOpNL twoSpheres_chartsOnto G δ h0 hmono n (J.J q) ((blocks A δ h0 hmono).incl n x.1))
  rw [toBase_linOpNL, toBase_linOpNL]
  rfl

variable (hA : IsStdNeck A) (hδ : ∀ m, δ m < 2 * Real.pi)

lemma crLvN_cstLvN (m : ℕ) (e : E) :
    crLvN J hsm G δ h0 hmono m (cstLvN δ h0 hmono hA hδ m e) = 0 := by
  apply Subtype.ext
  apply (fibreBlocks A δ h0 hmono).toBase_injective m
  rw [crLvN_val, toBase_linOpNL, toBase_cstLvN]
  exact ((linOpN_eq_zero_iff J hsm G δ h0 hmono (constBlocksN_mem δ h0 hmono e)).2
    ⟨e, rfl⟩).trans (map_zero _).symm

/-- **The kernel of `D_m` is the constants.** -/
lemma crLvN_ker (m : ℕ) (c : (sectionScale A δ h0 hmono) m)
    (hc : crLvN J hsm G δ h0 hmono m c = 0) : ∃ e : E, c = cstLvN δ h0 hmono hA hδ m e := by
  have h1 : linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q)
      ((blocks A δ h0 hmono).toBase m c.1) = 0 := by
    rw [← toBase_linOpNL, ← crLvN_val J hsm G, hc]
    exact map_zero _
  obtain ⟨e, he⟩ := (linOpN_eq_zero_iff J hsm G δ h0 hmono c.2).1 h1
  refine ⟨e, Subtype.ext ((blocks A δ h0 hmono).toBase_injective m ?_)⟩
  rw [toBase_cstLvN]
  exact he.symm

lemma crLvN_ker_lift (n : ℕ) (c : (sectionScale A δ h0 hmono) n)
    (hc : crLvN J hsm G δ h0 hmono n c = 0) :
    ∃ e : E, c = (sectionScale A δ h0 hmono).incl n (cstLvN δ h0 hmono hA hδ (n + 1) e) := by
  obtain ⟨e, he⟩ := crLvN_ker J hsm G δ h0 hmono hA hδ n c hc
  exact ⟨e, he.trans (incl_cstLvN δ h0 hmono hA hδ n e).symm⟩

/-! ## 3. The estimate and the dense range on every level -/

variable (hδ0 : 0 < δ 0)

include hδ0 hδ in
/-- **The estimate on level `n + 1`**: `‖ζ‖ ≤ C (‖Dζ‖ + ‖ζ‖_{X_n})` on `X_{n+1}`. -/
lemma estimate_succN (n : ℕ) : ∃ C : ℝ, ∀ ζ : (sectionScale A δ h0 hmono) (n + 1),
    ‖ζ‖ ≤ C * (‖crLvN J hsm G δ h0 hmono (n + 1) ζ‖ + ‖(sectionScale A δ h0 hmono).incl n ζ‖) := by
  obtain ⟨C, hC⟩ := ellipticEstimateNL J G δ h0 hmono (n + 1)
    (hδ0.trans_le (hmono.monotone (Nat.zero_le _))) (hδ (n + 1))
  set K := ‖kLowN (A := A) δ h0 hmono n‖
  refine ⟨max C 0 * (1 + K), fun ζ => ?_⟩
  have h1 := hC ζ.1 ζ.2
  rw [kOpNL_succ] at h1
  have e1 : ‖ζ‖ = ‖ζ.1‖ := rfl
  have e2 : ‖crLvN J hsm G δ h0 hmono (n + 1) ζ‖ =
      ‖linOpNL twoSpheres_chartsOnto G δ h0 hmono (n + 1) (J.J q) ζ.1‖ := rfl
  have e3 : ‖(sectionScale A δ h0 hmono).incl n ζ‖ = ‖(blocks A δ h0 hmono).incl n ζ.1‖ := rfl
  have h2 : ‖kLowN δ h0 hmono n ((blocks A δ h0 hmono).incl n ζ.1)‖ ≤
      K * ‖(blocks A δ h0 hmono).incl n ζ.1‖ := ContinuousLinearMap.le_opNorm _ _
  rw [e1, e2, e3]
  have hK : 0 ≤ K := norm_nonneg _
  have ha := norm_nonneg (linOpNL twoSpheres_chartsOnto G δ h0 hmono (n + 1) (J.J q) ζ.1)
  have hb := norm_nonneg ((blocks A δ h0 hmono).incl n ζ.1)
  have hc := norm_nonneg (kLowN δ h0 hmono n ((blocks A δ h0 hmono).incl n ζ.1))
  generalize ‖kLowN δ h0 hmono n ((blocks A δ h0 hmono).incl n ζ.1)‖ = c at h1 h2 hc
  generalize ‖linOpNL twoSpheres_chartsOnto G δ h0 hmono (n + 1) (J.J q) ζ.1‖ = a at h1 ha ⊢
  generalize ‖(blocks A δ h0 hmono).incl n ζ.1‖ = b at h2 hb ⊢
  generalize ‖ζ.1‖ = z at h1 ⊢
  generalize K = K' at h2 hK ⊢
  have hM : C ≤ max C 0 := le_max_left _ _
  have hM0 : 0 ≤ max C 0 := le_max_right _ _
  generalize max C 0 = M at hM hM0 ⊢
  have s1 : C * (a + c) ≤ M * (a + c) := mul_le_mul_of_nonneg_right hM (add_nonneg ha hc)
  have s2 : M * (a + c) ≤ M * (a + K' * b) :=
    mul_le_mul_of_nonneg_left (by linarith) hM0
  have s3 : M * (a + K' * b) ≤ M * (1 + K') * (a + b) := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hM0
    nlinarith
  linarith

variable (hG : GlueCharts A)

include hA hG hδ in
/-- **The range of `D_m` is dense** in `Y_m`. -/
lemma denseRange_crLvN (m : ℕ) : DenseRange (crLvN J hsm G δ h0 hmono m) := by
  intro y
  have key : ∀ (s : Set ((fibreBlocks A δ h0 hmono).levelSub (fibreSpace J A δ h0 hmono) m))
      (y' : (fibreBlocks A δ h0 hmono).levelSub (fibreSpace J A δ h0 hmono) m),
      (y' : (fibreBlocks A δ h0 hmono) m) ∈ closure (Subtype.val '' s) → y' ∈ closure s :=
    fun s y' h => closure_subtype.2 h
  refine key (range (crLvN J hsm G δ h0 hmono m)) y
    (closure_mono ?_ (denseNL J δ h0 hmono hsm G hA hG hδ m y.1 y.2))
  rintro _ ⟨w, -, hw, rfl⟩
  exact ⟨crLvN J hsm G δ h0 hmono m ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩, rfl⟩

/-! ## 4. Regularity and surjectivity on every level -/

include hA hG hδ0 hδ in
/-- **Regularity at level `n` from surjectivity at level `n`.** -/
theorem regularity_of_surjectiveN (n : ℕ) (hs : Surjective (crLvN J hsm G δ h0 hmono n))
    (v : (blocks A δ h0 hmono) n)
    (hv : (blocks A δ h0 hmono).toBase n v ∈ sectionSpace A δ h0 hmono)
    (hD : linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) ((blocks A δ h0 hmono).toBase n v) ∈
      range ((fibreBlocks A δ h0 hmono).toBase (n + 1))) :
    (blocks A δ h0 hmono).toBase n v ∈ range ((blocks A δ h0 hmono).toBase (n + 1)) := by
  obtain ⟨y, hy⟩ := hD
  have hyF : (fibreBlocks A δ h0 hmono).toBase (n + 1) y ∈ fibreSpace J A δ h0 hmono := by
    rw [hy]; exact linOpN_mem twoSpheres_chartsOnto hsm G J hv
  let xv : (sectionScale A δ h0 hmono) n := ⟨v, hv⟩
  let yY : (fibreScale J A δ h0 hmono) (n + 1) := ⟨y, hyF⟩
  have hTv : crLvN J hsm G δ h0 hmono n xv = (fibreScale J A δ h0 hmono).incl n yY := by
    apply Subtype.ext
    apply (fibreBlocks A δ h0 hmono).toBase_injective n
    change (fibreBlocks A δ h0 hmono).toBase n
      (linOpNL twoSpheres_chartsOnto G δ h0 hmono n (J.J q) v) =
        (fibreBlocks A δ h0 hmono).toBase (n + 1) y
    rw [toBase_linOpNL]
    exact hy.symm
  -- approximation of `y` by `D z_k`
  obtain ⟨z, hzr, hz⟩ :=
    mem_closure_iff_seq_limit.1 (denseRange_crLvN J hsm G δ h0 hmono hA hδ hG (n + 1) yY)
  choose ζ0 hζ0 using hzr
  -- the open mapping theorem for `D_n`
  obtain ⟨C, -, hpre⟩ := (crLvN J hsm G δ h0 hmono n).exists_preimage_norm_le hs
  choose x hx hxn using fun k => hpre ((fibreScale J A δ h0 hmono).incl n (z k - yY))
  have hr : Tendsto (fun k => (fibreScale J A δ h0 hmono).incl n (z k - yY)) atTop (𝓝 0) := by
    have h1 := hz.sub_const yY
    rw [sub_self] at h1
    have := (((fibreScale J A δ h0 hmono).incl n).continuous.tendsto 0).comp h1
    rw [map_zero] at this
    exact this
  have hx0 : Tendsto x atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (hr.norm.const_mul C)
    rw [norm_zero, mul_zero] at h
    exact squeeze_zero (fun k => norm_nonneg _) hxn h
  -- the kernel correction
  have hc : ∀ k, crLvN J hsm G δ h0 hmono n
      ((sectionScale A δ h0 hmono).incl n (ζ0 k) - x k - xv) = 0 := fun k => by
    rw [map_sub, map_sub, ← crLvN_incl, hζ0 k, hx k, hTv, ← map_sub, ← map_sub, sub_sub,
      sub_add_cancel, sub_self, map_zero]
  choose e he using fun k => crLvN_ker_lift J hsm G δ h0 hmono hA hδ n _ (hc k)
  set ζ : ℕ → (sectionScale A δ h0 hmono) (n + 1) :=
    fun k => ζ0 k - cstLvN δ h0 hmono hA hδ (n + 1) (e k) with hζ
  have hζT : ∀ k, crLvN J hsm G δ h0 hmono (n + 1) (ζ k) = z k := fun k => by
    rw [hζ, map_sub, hζ0 k, crLvN_cstLvN, sub_zero]
  have hζi : ∀ k, (sectionScale A δ h0 hmono).incl n (ζ k) = x k + xv := fun k => by
    rw [hζ, map_sub, ← he k]
    abel
  -- the closed range of `ζ ↦ (Dζ, ζ)`
  obtain ⟨C1, hC1⟩ := estimate_succN J hsm G δ h0 hmono hδ hδ0 n
  set Ψ : (sectionScale A δ h0 hmono) (n + 1) →L[ℝ]
      (fibreScale J A δ h0 hmono) (n + 1) × (sectionScale A δ h0 hmono) n :=
    (crLvN J hsm G δ h0 hmono (n + 1)).prod ((sectionScale A δ h0 hmono).incl n) with hΨdef
  set C' : ℝ≥0 := ⟨2 * max C1 0, by positivity⟩
  have hΨ : AntilipschitzWith C' Ψ := by
    refine AddMonoidHomClass.antilipschitz_of_bound Ψ fun w => ?_
    have h1 := hC1 w
    have h2 : ‖crLvN J hsm G δ h0 hmono (n + 1) w‖ ≤ ‖Ψ w‖ := le_max_left _ _
    have h3 : ‖(sectionScale A δ h0 hmono).incl n w‖ ≤ ‖Ψ w‖ := le_max_right _ _
    change ‖w‖ ≤ 2 * max C1 0 * ‖Ψ w‖
    have h4 : C1 * (‖crLvN J hsm G δ h0 hmono (n + 1) w‖ +
        ‖(sectionScale A δ h0 hmono).incl n w‖) ≤ max C1 0 *
        (‖crLvN J hsm G δ h0 hmono (n + 1) w‖ + ‖(sectionScale A δ h0 hmono).incl n w‖) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    nlinarith [le_max_right C1 0]
  have hcl : IsClosed (range Ψ) := hΨ.isClosed_range Ψ.uniformContinuous
  have hlim : Tendsto (fun k => Ψ (ζ k)) atTop (𝓝 (yY, xv)) := by
    have e1 : (fun k => Ψ (ζ k)) = fun k => (z k, x k + xv) :=
      funext fun k => Prod.ext (hζT k) (hζi k)
    rw [e1]
    have h2 : Tendsto (fun k => x k + xv) atTop (𝓝 (0 + xv)) := hx0.add_const xv
    rw [zero_add] at h2
    exact hz.prodMk_nhds h2
  obtain ⟨w, hw⟩ := hcl.closure_eq ▸
    mem_closure_of_tendsto hlim (Eventually.of_forall fun k => mem_range_self (ζ k))
  have hwv : (sectionScale A δ h0 hmono).incl n w = xv := congrArg Prod.snd hw
  exact ⟨w.1, congrArg ((blocks A δ h0 hmono).toBase n) (congrArg Subtype.val hwv)⟩

include hA hG hδ0 hδ in
/-- Surjectivity at level `n + 1` from surjectivity at level `n`. -/
theorem surjective_succN (n : ℕ) (hs : Surjective (crLvN J hsm G δ h0 hmono n)) :
    Surjective (crLvN J hsm G δ h0 hmono (n + 1)) := by
  intro y
  obtain ⟨x, hx⟩ := hs ((fibreScale J A δ h0 hmono).incl n y)
  have hD : linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) ((blocks A δ h0 hmono).toBase n x.1) ∈
      range ((fibreBlocks A δ h0 hmono).toBase (n + 1)) := by
    refine ⟨y.1, ?_⟩
    rw [← toBase_linOpNL, ← crLvN_val J hsm G, hx]
    rfl
  obtain ⟨w, hw⟩ := regularity_of_surjectiveN J hsm G δ h0 hmono hA hδ hδ0 hG n hs x.1 x.2 hD
  have hwm : w ∈ (blocks A δ h0 hmono).levelSub (sectionSpace A δ h0 hmono) (n + 1) := by
    rw [ScBanach.mem_levelSub, hw]; exact x.2
  let x' : (sectionScale A δ h0 hmono) (n + 1) := ⟨w, hwm⟩
  have hix : (sectionScale A δ h0 hmono).incl n x' = x :=
    Subtype.ext ((blocks A δ h0 hmono).toBase_injective n hw)
  refine ⟨x', (fibreScale J A δ h0 hmono).incl_injective n ?_⟩
  rw [crLvN_incl, hix, hx]

include hA hG hδ0 hδ in
/-- **`D` is onto on level `0`.** -/
theorem crLvN_zero_surjective : Surjective (crLvN J hsm G δ h0 hmono 0) := by
  intro y
  obtain ⟨w, hw⟩ := (linCRN_isFredholm_twoSpheres_of_glueCharts J δ h0 hmono hsm G hA hG hδ0
    (hδ 0)).2.1 ⟨y.1, y.2⟩
  exact ⟨⟨w.1, w.2⟩, Subtype.ext ((linOpNL_zero J G δ h0 hmono w.1).trans
    (congrArg Subtype.val hw))⟩

include hA hG hδ0 hδ in
/-- **`D` is onto on every level**: `H^{3+m,δ_m} → H^{2+m,δ_m}`. -/
theorem crLvN_surjective (m : ℕ) : Surjective (crLvN J hsm G δ h0 hmono m) := by
  induction m with
  | zero => exact crLvN_zero_surjective J hsm G δ h0 hmono hA hδ hδ0 hG
  | succ m ih => exact surjective_succN J hsm G δ h0 hmono hA hδ hδ0 hG m ih

include hsm hA hG hδ0 hδ in
/-- **Elliptic regularity of `D` from level `n` to level `n + 1`** at a constant map from
`twoSpheres`: a section of class `(3+n, δ_n)` whose image `Dξ` is of class `(3+n, δ_{n+1})` is
of class `(4+n, δ_{n+1})`. -/
theorem levelRegularity_twoSpheres (n : ℕ) (v : (blocks A δ h0 hmono) n)
    (hv : (blocks A δ h0 hmono).toBase n v ∈ sectionSpace A δ h0 hmono)
    (hD : linOpN twoSpheres_chartsOnto G δ h0 hmono (J.J q) ((blocks A δ h0 hmono).toBase n v) ∈
      range ((fibreBlocks A δ h0 hmono).toBase (n + 1))) :
    (blocks A δ h0 hmono).toBase n v ∈ range ((blocks A δ h0 hmono).toBase (n + 1)) :=
  regularity_of_surjectiveN J hsm G δ h0 hmono hA hδ hδ0 hG n
    (crLvN_surjective J hsm G δ h0 hmono hA hδ hδ0 hG n) v hv hD

end Levels

end GWMemoir
