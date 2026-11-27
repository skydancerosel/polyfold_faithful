import GWMemoir.LevelRegularityEstimate
import GWMemoir.LevelRegularityDense

/-!
# Elliptic regularity of `D` on every level, at a constant map from the three-pointed sphere

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, Propositions 4.7 (p. 102),
4.8 (p. 104), 4.23 (p. 118), in the local model of `GWMemoir.LinearModelFredholm`: the surface
`sphere3` and a constant map `u ≡ q`.  Here **`levelRegularity_sphere3`** proves the proposition
`LevelRegularity` of that file, for `0 < δ₀`, and the main results of that file then hold without
it.

## The argument

`sphere3` has no nodes, so the section space has only disc blocks; their representatives carry the
cut-off of the disc charts, and the weights play no role in the analysis.  Write `X_m`, `Y_m` for
the levels of the section space and of the fibre, and `D_m : X_m → Y_m` for the level maps of
`crSc`.  By induction on `n`:

* `D_0` is onto (`crBase_surjective`, the Cauchy transform with the estimate on level `0`).
* **Regularity at `n` from surjectivity at `n`** (`regularity_of_surjective`).  Let `ξ ∈ X_n` with
  `Dξ = y ∈ Y_{n+1}`.  By `denseL`, `y = lim D z_k` in `Y_{n+1}` with `z_k ∈ X_{n+1}`.  By the open
  mapping theorem for `D_n` there are `x_k ∈ X_n`, `x_k → 0`, with `D x_k = D z_k - y`.  Then
  `z_k - x_k - ξ` lies in the kernel of `D_n`, the constants (`linCR_ker_sphere3`), which lie on
  every level (`constBlocksL`); so `ζ_k = ξ + x_k` lies in `X_{n+1}`, with `D ζ_k = D z_k`.  The
  estimate on level `n + 1` (`ellipticEstimateL`) says that `ζ ↦ (Dζ, ζ)`, `X_{n+1} → Y_{n+1} × X_n`,
  is bounded below, so it has a closed range, which contains `lim (D ζ_k, ζ_k) = (y, ξ)`.  Hence
  `ξ ∈ X_{n+1}`.
* Surjectivity at `n + 1` follows from surjectivity and regularity at `n`
  (`surjective_succ`).

## Main results

* `crSc_val`, `crSc_surjective`: every level map `H^{3+m,δ_m} → H^{2+m,δ_m}` is onto.
* **`levelRegularity_sphere3`**.
* `crSc_isScFredholm_uncond`, `memoir_proposition_4_7_sphere3_uncond`,
  `memoir_proposition_4_23_sphere3_uncond`, `memoir_proposition_4_8_sphere3_uncond`,
  **`isScFredholmGerm2021_sphere3_uncond`**: the results of `GWMemoir.LinearModelFredholm` with the
  hypothesis `LevelRegularity` removed.  The data exist (`localModel_witness_E2`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology NNReal
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

section Sphere

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable (J : AlmostComplexStructure E Q) {q : Q} {A : SectionAtlas (E := E) sphere3 (fun _ => q)}
  (G : GlueData A) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-! ## 1. The level maps of `crSc` -/

/-- The level map `D_m` of `crSc` is `linOpL m` on the blocks. -/
lemma crSc_val (m : ℕ) (x : (secSc A δ h0 hmono) m) :
    (crSc J G δ h0 hmono m x).1 = linOpL sphere3_chartsOnto G δ h0 hmono m (J.J q) x.1 := by
  have hnn : IsEmpty (Fin A.nn) := isEmpty_neck_of_nodes_empty rfl A
  apply (fibreBlocks A δ h0 hmono).toBase_injective m
  calc (fibreBlocks A δ h0 hmono).toBase m (crSc J G δ h0 hmono m x).1
      = ((fibSc J A δ h0 hmono).toBase m (crSc J G δ h0 hmono m x)).1 :=
        ((fibreBlocks A δ h0 hmono).ofSubspaceScale_coe_toBase
          (isClosed_fibreSpace J A δ h0 hmono) m _).symm
    _ = (crSc J G δ h0 hmono 0 ((secSc A δ h0 hmono).toBase m x)).1 := by
        rw [ScOperator.toBase_comm]
    _ = linOp sphere3_chartsOnto G δ h0 hmono (J.J q) ((secSc A δ h0 hmono).toBase m x).1 := by
        rw [crSc_zero]; rfl
    _ = linOp sphere3_chartsOnto G δ h0 hmono (J.J q) ((blocks A δ h0 hmono).toBase m x.1) :=
        congrArg _ ((blocks A δ h0 hmono).ofSubspaceScale_coe_toBase
          (isClosed_sectionSpace A δ h0 hmono) m x)
    _ = _ := (toBase_linOpL sphere3_chartsOnto G δ h0 hmono hnn m (J.J q) x.1).symm

/-- The kernel of `D_m` is the constants. -/
lemma crSc_ker (m : ℕ) (c : (secSc A δ h0 hmono) m) (hc : crSc J G δ h0 hmono m c = 0) :
    ∃ e : E, ((secSc A δ h0 hmono).toBase m c).1 = constBlocks A δ h0 hmono e := by
  have h0' : crBase J G δ h0 hmono ((secSc A δ h0 hmono).toBase m c) = 0 := by
    rw [← crSc_zero, ← ScOperator.toBase_comm, hc, map_zero]
  exact (linCR_ker_sphere3 J G δ h0 hmono ((secSc A δ h0 hmono).toBase m c).2).1
    (congrArg Subtype.val h0')

/-- The constant section `e` on level `m`. -/
def cstL (m : ℕ) (e : E) : (secSc A δ h0 hmono) m :=
  ⟨constBlocksL A δ h0 hmono m e, by
    rw [ScBanach.mem_levelSub, toBase_constBlocksL]
    exact constBlocks_mem_sectionSpace δ h0 hmono e⟩

lemma toBase_cstL (m : ℕ) (e : E) :
    ((secSc A δ h0 hmono).toBase m (cstL δ h0 hmono m e)).1 = constBlocks A δ h0 hmono e :=
  ((blocks A δ h0 hmono).ofSubspaceScale_coe_toBase (isClosed_sectionSpace A δ h0 hmono) m _).trans
    (toBase_constBlocksL A δ h0 hmono m e)

lemma crSc_cstL (m : ℕ) (e : E) : crSc J G δ h0 hmono m (cstL δ h0 hmono m e) = 0 := by
  apply (fibSc J A δ h0 hmono).toBase_injective m
  rw [ScOperator.toBase_comm, map_zero, crSc_zero]
  apply Subtype.ext
  rw [crBase_apply, toBase_cstL]
  exact (linCR_ker_sphere3 J G δ h0 hmono (constBlocks_mem_sectionSpace δ h0 hmono e)).2 ⟨e, rfl⟩

/-- An element of the kernel of `D_n` lies on level `n + 1`. -/
lemma crSc_ker_lift (n : ℕ) (c : (secSc A δ h0 hmono) n) (hc : crSc J G δ h0 hmono n c = 0) :
    ∃ e : E, c = (secSc A δ h0 hmono).incl n (cstL δ h0 hmono (n + 1) e) := by
  obtain ⟨e, he⟩ := crSc_ker J G δ h0 hmono n c hc
  refine ⟨e, (secSc A δ h0 hmono).toBase_injective n (Subtype.ext ?_)⟩
  rw [he, ← ScScale.toBase_succ, toBase_cstL]

/-! ## 2. The estimate and the density on the levels of the sc-structure -/

/-- **The estimate on level `n + 1`**: `‖ζ‖ ≤ C (‖Dζ‖ + ‖ζ‖_{X_n})` on `X_{n+1}`. -/
lemma estimate_succ (n : ℕ) : ∃ C : ℝ, ∀ ζ : (secSc A δ h0 hmono) (n + 1),
    ‖ζ‖ ≤ C * (‖crSc J G δ h0 hmono (n + 1) ζ‖ + ‖(secSc A δ h0 hmono).incl n ζ‖) := by
  obtain ⟨C, hC⟩ := ellipticEstimateL J G δ h0 hmono (n + 1)
  set K := ‖kLow (A := A) δ h0 hmono n‖
  refine ⟨max C 0 * (1 + K), fun ζ => ?_⟩
  have h1 := hC ζ.1 ζ.2
  rw [kOpL_succ] at h1
  have e1 : ‖ζ‖ = ‖ζ.1‖ := rfl
  have e2 : ‖crSc J G δ h0 hmono (n + 1) ζ‖ =
      ‖linOpL sphere3_chartsOnto G δ h0 hmono (n + 1) (J.J q) ζ.1‖ := by
    rw [← crSc_val]; rfl
  have e3 : ‖(secSc A δ h0 hmono).incl n ζ‖ = ‖(blocks A δ h0 hmono).incl n ζ.1‖ := rfl
  have h2 : ‖kLow δ h0 hmono n ((blocks A δ h0 hmono).incl n ζ.1)‖ ≤
      K * ‖(blocks A δ h0 hmono).incl n ζ.1‖ := ContinuousLinearMap.le_opNorm _ _
  rw [e1, e2, e3]
  have hK : 0 ≤ K := norm_nonneg _
  have ha := norm_nonneg (linOpL sphere3_chartsOnto G δ h0 hmono (n + 1) (J.J q) ζ.1)
  have hb := norm_nonneg ((blocks A δ h0 hmono).incl n ζ.1)
  have hm : C * (‖linOpL sphere3_chartsOnto G δ h0 hmono (n + 1) (J.J q) ζ.1‖ +
      ‖kLow δ h0 hmono n ((blocks A δ h0 hmono).incl n ζ.1)‖) ≤
      max C 0 * (‖linOpL sphere3_chartsOnto G δ h0 hmono (n + 1) (J.J q) ζ.1‖ +
      K * ‖(blocks A δ h0 hmono).incl n ζ.1‖) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _))
  have hm2 : max C 0 * (‖linOpL sphere3_chartsOnto G δ h0 hmono (n + 1) (J.J q) ζ.1‖ +
      K * ‖(blocks A δ h0 hmono).incl n ζ.1‖) ≤ max C 0 * (1 + K) *
      (‖linOpL sphere3_chartsOnto G δ h0 hmono (n + 1) (J.J q) ζ.1‖ +
        ‖(blocks A δ h0 hmono).incl n ζ.1‖) := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
    nlinarith
  linarith

/-- **The range of `D_m` is dense** in `Y_m`. -/
lemma denseRange_crSc (m : ℕ) : DenseRange (crSc J G δ h0 hmono m) := by
  intro y
  have key : ∀ (s : Set ((fibreBlocks A δ h0 hmono).levelSub (fibreSpace J A δ h0 hmono) m))
      (y' : (fibreBlocks A δ h0 hmono).levelSub (fibreSpace J A δ h0 hmono) m),
      (y' : (fibreBlocks A δ h0 hmono) m) ∈ closure (Subtype.val '' s) → y' ∈ closure s :=
    fun s y' h => closure_subtype.2 h
  refine key (range (crSc J G δ h0 hmono m)) y
    (closure_mono ?_ (denseL J G δ h0 hmono m y.1 y.2))
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨crSc J G δ h0 hmono m ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩, crSc_val J G δ h0 hmono m ⟨w, hw⟩⟩

/-! ## 3. Regularity and surjectivity on every level -/

/-- **Regularity at level `n` from surjectivity at level `n`.** -/
theorem regularity_of_surjective (n : ℕ) (hs : Surjective (crSc J G δ h0 hmono n))
    (v : (blocks A δ h0 hmono) n)
    (hv : (blocks A δ h0 hmono).toBase n v ∈ sectionSpace A δ h0 hmono)
    (hD : linOp sphere3_chartsOnto G δ h0 hmono (J.J q) ((blocks A δ h0 hmono).toBase n v) ∈
      range ((fibreBlocks A δ h0 hmono).toBase (n + 1))) :
    (blocks A δ h0 hmono).toBase n v ∈ range ((blocks A δ h0 hmono).toBase (n + 1)) := by
  obtain ⟨y, hy⟩ := hD
  have hnn : IsEmpty (Fin A.nn) := isEmpty_neck_of_nodes_empty rfl A
  have hyF : (fibreBlocks A δ h0 hmono).toBase (n + 1) y ∈ fibreSpace J A δ h0 hmono := by
    rw [hy]; exact linOp_mem rfl sphere3_chartsOnto (fun _ => rfl) G J hv
  let xv : (secSc A δ h0 hmono) n := ⟨v, hv⟩
  let yY : (fibSc J A δ h0 hmono) (n + 1) := ⟨y, hyF⟩
  have hTv : (crSc J G δ h0 hmono) n xv = (fibSc J A δ h0 hmono).incl n yY := by
    apply Subtype.ext
    rw [crSc_val]
    apply (fibreBlocks A δ h0 hmono).toBase_injective n
    rw [toBase_linOpL sphere3_chartsOnto G δ h0 hmono hnn n (J.J q)]
    exact hy.symm
  -- approximation of `y` by `D z_k`
  obtain ⟨z, hzr, hz⟩ := mem_closure_iff_seq_limit.1 (denseRange_crSc J G δ h0 hmono (n + 1) yY)
  choose ζ0 hζ0 using hzr
  -- the open mapping theorem for `D_n`
  obtain ⟨C, -, hpre⟩ := ((crSc J G δ h0 hmono) n).exists_preimage_norm_le hs
  choose x hx hxn using fun k => hpre ((fibSc J A δ h0 hmono).incl n (z k - yY))
  have hr : Tendsto (fun k => (fibSc J A δ h0 hmono).incl n (z k - yY)) atTop (𝓝 0) := by
    have h1 := hz.sub_const yY
    rw [sub_self] at h1
    have := (((fibSc J A δ h0 hmono).incl n).continuous.tendsto 0).comp h1
    rw [map_zero] at this
    exact this
  have hx0 : Tendsto x atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (hr.norm.const_mul C)
    rw [norm_zero, mul_zero] at h
    exact squeeze_zero (fun k => norm_nonneg _) hxn h
  -- the kernel correction
  have hc : ∀ k, (crSc J G δ h0 hmono) n ((secSc A δ h0 hmono).incl n (ζ0 k) - x k - xv) = 0 := fun k => by
    rw [map_sub, map_sub, ← (crSc J G δ h0 hmono).incl_comm, hζ0 k, hx k, hTv, ← map_sub, ← map_sub, sub_sub,
      sub_add_cancel, sub_self, map_zero]
  choose e he using fun k => crSc_ker_lift J G δ h0 hmono n _ (hc k)
  set ζ : ℕ → (secSc A δ h0 hmono) (n + 1) := fun k => ζ0 k - cstL δ h0 hmono (n + 1) (e k) with hζ
  have hζT : ∀ k, (crSc J G δ h0 hmono) (n + 1) (ζ k) = z k := fun k => by
    rw [hζ, map_sub, hζ0 k, crSc_cstL, sub_zero]
  have hζi : ∀ k, (secSc A δ h0 hmono).incl n (ζ k) = x k + xv := fun k => by
    rw [hζ, map_sub, ← he k]
    abel
  -- the closed range of `ζ ↦ (Dζ, ζ)`
  obtain ⟨C1, hC1⟩ := estimate_succ J G δ h0 hmono n
  set Ψ : (secSc A δ h0 hmono) (n + 1) →L[ℝ] (fibSc J A δ h0 hmono) (n + 1) × (secSc A δ h0 hmono) n := ((crSc J G δ h0 hmono) (n + 1)).prod ((secSc A δ h0 hmono).incl n) with hΨdef
  set C' : ℝ≥0 := ⟨2 * max C1 0, by positivity⟩
  have hΨ : AntilipschitzWith C' Ψ := by
    refine AddMonoidHomClass.antilipschitz_of_bound Ψ fun w => ?_
    have h1 := hC1 w
    have h2 : ‖(crSc J G δ h0 hmono) (n + 1) w‖ ≤ ‖Ψ w‖ := le_max_left _ _
    have h3 : ‖(secSc A δ h0 hmono).incl n w‖ ≤ ‖Ψ w‖ := le_max_right _ _
    change ‖w‖ ≤ 2 * max C1 0 * ‖Ψ w‖
    have h4 : C1 * (‖(crSc J G δ h0 hmono) (n + 1) w‖ + ‖(secSc A δ h0 hmono).incl n w‖) ≤ max C1 0 * (‖(crSc J G δ h0 hmono) (n + 1) w‖ + ‖(secSc A δ h0 hmono).incl n w‖) :=
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
  have hwv : (secSc A δ h0 hmono).incl n w = xv := congrArg Prod.snd hw
  exact ⟨w.1, congrArg ((blocks A δ h0 hmono).toBase n) (congrArg Subtype.val hwv)⟩

/-- Surjectivity at level `n + 1` from surjectivity at level `n`. -/
theorem surjective_succ (n : ℕ) (hs : Surjective (crSc J G δ h0 hmono n)) :
    Surjective (crSc J G δ h0 hmono (n + 1)) := by
  have hnn : IsEmpty (Fin A.nn) := isEmpty_neck_of_nodes_empty rfl A
  intro y
  obtain ⟨x, hx⟩ := hs ((fibSc J A δ h0 hmono).incl n y)
  have hD : linOp sphere3_chartsOnto G δ h0 hmono (J.J q) ((blocks A δ h0 hmono).toBase n x.1) ∈
      range ((fibreBlocks A δ h0 hmono).toBase (n + 1)) := by
    refine ⟨y.1, ?_⟩
    rw [← toBase_linOpL sphere3_chartsOnto G δ h0 hmono hnn n (J.J q), ← crSc_val, hx]
    rfl
  have hreg := regularity_of_surjective J G δ h0 hmono n hs x.1 x.2 hD
  have hx0 : ((secSc A δ h0 hmono).toBase n x).1 ∈ range ((blocks A δ h0 hmono).toBase (n + 1)) := by
    rw [show ((secSc A δ h0 hmono).toBase n x).1 = (blocks A δ h0 hmono).toBase n x.1 from
      (blocks A δ h0 hmono).ofSubspaceScale_coe_toBase (isClosed_sectionSpace A δ h0 hmono) n x]
    exact hreg
  obtain ⟨x', hx'⟩ := (mem_range_toBase_ofSubspace (blocks A δ h0 hmono)
    (sphere3_sectionsDense q A δ h0 hmono) (n + 1) _).2 hx0
  have hix : (secSc A δ h0 hmono).incl n x' = x := (secSc A δ h0 hmono).toBase_injective n hx'
  refine ⟨x', (fibSc J A δ h0 hmono).incl_injective n ?_⟩
  exact ((crSc J G δ h0 hmono).incl_comm n x').trans (by rw [hix, hx])

/-- **`D` is onto on every level**: `H^{3+m,δ_m} → H^{2+m,δ_m}` (with `0 < δ₀`). -/
theorem crSc_surjective (hδ : 0 < δ 0) (m : ℕ) : Surjective (crSc J G δ h0 hmono m) := by
  induction m with
  | zero => rw [crSc_zero]; exact crBase_surjective J G δ h0 hmono hδ
  | succ m ih => exact surjective_succ J G δ h0 hmono m ih

/-- **Elliptic regularity of `D` from level `n` to level `n + 1`** at a constant map from
`sphere3`, with `0 < δ₀`: a section of class `(3+n, δ_n)` whose image `Dξ` is of class
`(3+n, δ_{n+1})` is of class `(4+n, δ_{n+1})`.  This is the proposition `LevelRegularity` of
`GWMemoir.LinearModelFredholm`. -/
theorem levelRegularity_sphere3 (hδ : 0 < δ 0) : LevelRegularity J G δ h0 hmono :=
  fun n v hv hD => regularity_of_surjective J G δ h0 hmono n (crSc_surjective J G δ h0 hmono hδ n)
    v hv hD

/-! ## 4. The results of `GWMemoir.LinearModelFredholm` without `LevelRegularity` -/

/-- **`D` is sc-Fredholm** at a constant map from `sphere3` (Definition 1.1.9 of the book), with
`0 < δ₀`: Fredholm on every level `H^{3+m,δ_m} → H^{2+m,δ_m}`, with kernel the constants. -/
theorem crSc_isScFredholm_uncond (hδ : 0 < δ 0) : IsScFredholm (crSc J G δ h0 hmono) :=
  crSc_isScFredholm J G δ h0 hmono hδ (levelRegularity_sphere3 J G δ h0 hmono hδ)

/-- **Memoir Proposition 4.7, p. 102, in the local model at `u ≡ q`**, with `0 < δ₀`: `ξ ↦ Dξ`
is sc-smooth and regularizing on `O = H^{3,δ₀}_c(S², u*TQ)`. -/
theorem memoir_proposition_4_7_sphere3_uncond (hδ : 0 < δ 0) :
    Prop_4_7 univ (crSc J G δ h0 hmono 0) :=
  memoir_proposition_4_7_sphere3 J G δ h0 hmono (levelRegularity_sphere3 J G δ h0 hmono hδ)

/-- **Memoir Proposition 4.23, p. 118, in the local model at `u ≡ q`**, with `0 < δ₀`, no
`(a, v)` coordinates and `H` the whole section space. -/
theorem memoir_proposition_4_23_sphere3_uncond (hδ : 0 < δ 0) :
    Prop_4_23 univ (crSc J G δ h0 hmono 0) ⊥ ⊤
      ((crSc J G δ h0 hmono).isScSmooth (relOpen_of_isOpen isOpen_univ).isScDomain) :=
  memoir_proposition_4_23_sphere3 J G δ h0 hmono hδ (levelRegularity_sphere3 J G δ h0 hmono hδ)

/-- **Memoir Proposition 4.8, p. 104, in the local model at `u ≡ q`**, with `0 < δ₀`. -/
theorem memoir_proposition_4_8_sphere3_uncond (hδ : 0 < δ 0) :
    Prop_4_8 univ (crSc J G δ h0 hmono 0) :=
  memoir_proposition_4_8_sphere3 J G δ h0 hmono hδ (levelRegularity_sphere3 J G δ h0 hmono hδ)

/-- **`∂̄_J` is an sc-Fredholm germ at `u ≡ q`** in the local model `O ◁ F → O`
(Definition 3.1.11 of the book, 2021 p. 96), with `0 < δ₀`. -/
theorem isScFredholmGerm2021_sphere3_uncond (hδ : 0 < δ 0) :
    (LocalBundle.bundle (fibSc J A δ h0 hmono)
      (relOpen_of_isOpen (E := secSc A δ h0 hmono) isOpen_univ) lmPt).IsScFredholmGerm2021
        (LocalBundle.sec (crSc J G δ h0 hmono 0)) lmPt :=
  isScFredholmGerm2021_sphere3 J G δ h0 hmono hδ (levelRegularity_sphere3 J G δ h0 hmono hδ)

end Sphere

end GWMemoir
