import GWMemoir.Gluing

/-!
# Memoir §2.4, Lemma 2.48: the total glued map on continuous maps

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, pp. 47–48.

* `glueL`, `antiL`: `⊕_a : E → E⁺_a` and `⊖_a : E → E⁻_a` as linear maps; `totalGlue = (⊕_a, ⊖_a)`.
* `totalInv`: the inverse (2.6), (2.7) (`memoir_eq_2_6_2_7`).
* **Lemma 2.48**: `totalGlue_bijective`, `totalGlueEquiv` (for `R ≥ 2`); in terms of the gluing
  parameter `a`, `memoir_lemma_2_48` in `GWMemoir.GluingSplicing`.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace GWMemoir.Neck

variable {β : ℝ → ℝ} {R ϑ : ℝ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ## Lemma 2.48 -/

section Lemma248

variable (hβ : IsCutoff β) (hR2 : 2 ≤ R)
include hβ hR2

/-- Integrating `⊕_a(h⁺,h⁻)` over `{R/2} × S¹` gives `av_a(h⁺,h⁻)` (Memoir p. 47). -/
theorem av_eq_circ_glue {h : (HalfP → V) × (HalfN → V)} (h1 : Continuous h.1)
    (h2 : Continuous h.2) :
    av R h = circ (extZ (by linarith) (glue β R ϑ h)) (R / 2) := by
  have hm : R / 2 ∈ Icc 0 R := ⟨by linarith, by linarith⟩
  have hb := βa_half (R := R) hβ
  unfold circ
  simp_rw [extZ_of_mem (by linarith) _ hm]
  simp only [glue, hb, sh, show R / 2 - R = -(R / 2) by ring]
  have i1 : Integrable fun t : S1 => (1 / 2 : ℝ) • extP h.1 (R / 2, t) :=
    (integrable_circ (continuous_extP h1) _).smul _
  have i2 : Integrable fun t : S1 => (1 - 1 / 2 : ℝ) • extN h.2 (-(R / 2), t - (ϑ : S1)) :=
    (((continuous_extN h2).comp (continuous_const.prodMk
      (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).smul _
  rw [integral_add i1 i2, integral_smul, integral_smul,
    integral_sub_right_eq_self (fun t => extN h.2 (-(R / 2), t))]
  simp only [av, circ]; norm_num [smul_add]

lemma continuous_coreInv {v : Zcyl R → V} {w : ℝ × S1 → V} (hv : Continuous v)
    (hw : Continuous w) :
    Continuous (coreInv β R ϑ (by linarith) v w).1 ∧ Continuous (coreInv β R ϑ (by linarith) v w).2 := by
  have hR : (0 : ℝ) ≤ R := by linarith
  have hb := continuous_βa (R := R) hβ
  have hg := continuous_γa (R := R) hβ
  have hV := continuous_extZ hR hv
  constructor
  · have hz : Continuous fun z : HalfP => (z.1.1, z.2) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hz1 : Continuous fun z : HalfP => z.1.1 := continuous_subtype_val.comp continuous_fst
    exact ((hg.comp hz1).inv₀ fun _ => γa_ne _).smul
      (((hb.comp hz1).smul (hV.comp hz)).sub ((continuous_const.sub (hb.comp hz1)).smul (hw.comp hz)))
  · have hz : Continuous fun z : HalfN => ush R ϑ (z.1.1, z.2) :=
      continuous_ush.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    have hz1 : Continuous fun z : HalfN => (ush R ϑ (z.1.1, z.2)).1 := continuous_fst.comp hz
    exact ((hg.comp hz1).inv₀ fun _ => γa_ne _).smul
      (((continuous_const.sub (hb.comp hz1)).smul (hV.comp hz)).add ((hb.comp hz1).smul (hw.comp hz)))

/-- `⊖_a` maps `E` into `E⁻_a`: the anti-glued map has antipodal asymptotic constants
`⊖_a(h)(-∞) = -⊖_a(h)(+∞)` (Memoir p. 46). -/
theorem anti_mem {h : (HalfP → V) × (HalfN → V)} (hh : h ∈ pairSp V) :
    anti β R ϑ h ∈ minusSp V := by
  obtain ⟨h1, h2, c, hc1, hc2⟩ := hh
  set a := av R h
  have hb := continuous_βa (R := R) hβ
  refine ⟨?_, -(c + -a), ?_, ?_⟩
  · have : anti β R ϑ h = fun x => antiHat β R ϑ h x - (2 * βa β R x.1 - 1) • a :=
      funext (anti_eq h)
    rw [this]
    exact (continuous_antiHat hβ h1 h2).sub
      ((continuous_const.mul (hb.comp continuous_fst)).sub continuous_const |>.smul continuous_const)
  · refine ((hc1.const_add (-a)).neg).congr (S₀ := R / 2 + 1) fun x hx => ?_
    simp only [anti]
    rw [βa_zero hβ hx]; module
  · rw [neg_neg]
    refine ((LimBot.comp_sh (R := R) (ϑ := ϑ) hc2).const_add (-a)).congr (S₀ := R / 2 - 1)
      fun x hx => ?_
    simp only [anti]
    rw [βa_one hβ hx]; module

variable (ϑ V) in
/-- `⊕_a : E → E⁺_a`. -/
def glueL : pairSp V →ₗ[ℝ] plusSp V R :=
  (glueLin β R ϑ).restrict fun _ hh => continuous_glue hβ hh.1 hh.2.1

variable (ϑ V) in
/-- `⊖_a : E → E⁻_a`. -/
def antiL : pairSp V →ₗ[ℝ] minusSp V where
  toFun h := ⟨anti β R ϑ h, anti_mem hβ hR2 h.2⟩
  map_add' h k := by
    ext x
    simp only [Submodule.coe_add, Pi.add_apply, anti_eq]
    have e1 := congrFun ((antiHatLin β R ϑ).map_add h.1 k.1) x
    have e2 := (avL R).map_add h k
    simp only [antiHatLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, avL,
      Submodule.coe_add] at e1 e2
    rw [e1, e2]; module
  map_smul' r h := by
    ext x
    simp only [Submodule.coe_smul, Pi.smul_apply, anti_eq, RingHom.id_apply]
    have e1 := congrFun ((antiHatLin β R ϑ).map_smul r h.1) x
    have e2 := (avL R).map_smul r h
    simp only [antiHatLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, avL,
      Submodule.coe_smul] at e1 e2
    rw [e1, e2]; module

variable (ϑ V) in
/-- The total glued map `Φ_a = (⊕_a, ⊖_a) : E → E⁺_a ⊕ E⁻_a` (Memoir p. 47). -/
def totalGlue : pairSp V →ₗ[ℝ] plusSp V R × minusSp V :=
  (glueL ϑ V hβ).prod (antiL ϑ V hβ hR2)

variable (β ϑ) in
/-- The inverse of the total glued map: formulas (2.6) and (2.7), with
`w̃ = w + (2β_a - 1)[v]` and `[v] = ∫_{S¹} v(R/2, t) dt`. -/
def totalInv (v : Zcyl R → V) (w : ℝ × S1 → V) : (HalfP → V) × (HalfN → V) :=
  coreInv β R ϑ (by linarith) v fun x =>
    w x + (2 * βa β R x.1 - 1) • circ (extZ (by linarith) v) (R / 2)

theorem totalInv_mem {v : Zcyl R → V} {w : ℝ × S1 → V} (hv : v ∈ plusSp V R)
    (hw : w ∈ minusSp V) : totalInv β ϑ hR2 v w ∈ pairSp V := by
  obtain ⟨hw1, c, hc1, hc2⟩ := hw
  have hb := continuous_βa (R := R) hβ
  set c₀ := circ (extZ (by linarith) v) (R / 2)
  have hwt : Continuous fun x : ℝ × S1 => w x + (2 * βa β R x.1 - 1) • c₀ :=
    hw1.add (((continuous_const.mul (hb.comp continuous_fst)).sub continuous_const).smul
      continuous_const)
  obtain ⟨k1, k2⟩ := continuous_coreInv (ϑ := ϑ) hβ hR2 hv hwt
  refine ⟨k1, k2, -c + c₀, ?_, ?_⟩
  · refine ((hc1.neg).const_add c₀).congr (S₀ := R / 2 + 1) fun x hx => ?_
    obtain ⟨s, t⟩ := x
    have hb0 : βa β R s = 0 := βa_zero hβ hx
    simp only [totalInv]
    rw [coreInv_fst _ v _ (by simp only at hx; linarith), γa_of_βa_zero hb0, hb0]
    simp only [mul_zero, zero_sub, inv_one, one_smul, sub_zero, zero_smul, neg_smul]
    abel
  · refine ((LimBot.comp_ush (R := R) (ϑ := ϑ) hc2).const_add c₀).congr (S₀ := -(R / 2) - 1)
      fun x hx => ?_
    have hx0 : x.1 ≤ 0 := by linarith
    have hs : (ush R ϑ x).1 ≤ R := by simp only [ush]; linarith
    have hb1 : βa β R (ush R ϑ x).1 = 1 := βa_one hβ (by simp only [ush]; linarith)
    conv_lhs => rw [← sh_ush (R := R) (ϑ := ϑ) x]
    simp only [totalInv]
    rw [show ush R ϑ x = ((ush R ϑ x).1, (ush R ϑ x).2) from rfl, coreInv_snd _ v _ hs,
      γa_of_βa_one hb1, hb1]
    simp only [sub_self, zero_smul, zero_add, inv_one, one_smul, mul_one]
    norm_num [c₀]

theorem totalGlue_injective : Function.Injective (totalGlue ϑ V hβ hR2) := by
  intro h k hhk
  have hR : (0 : ℝ) ≤ R := by linarith
  have eg : glue β R ϑ h.1 = glue β R ϑ k.1 := congrArg Subtype.val (congrArg Prod.fst hhk)
  have ea : anti β R ϑ h.1 = anti β R ϑ k.1 := congrArg Subtype.val (congrArg Prod.snd hhk)
  have eav : av R h.1 = av R k.1 := by
    rw [av_eq_circ_glue hβ hR2 h.2.1 h.2.2.1, av_eq_circ_glue hβ hR2 k.2.1 k.2.2.1, eg]
  have eh : antiHat β R ϑ h.1 = antiHat β R ϑ k.1 := by
    funext x
    have := congrFun ea x
    rw [anti_eq, anti_eq, eav] at this
    exact sub_left_injective this
  apply Subtype.ext
  rw [← coreInv_glue (ϑ := ϑ) hβ hR2 h.1, ← coreInv_glue (ϑ := ϑ) hβ hR2 k.1, eg, eh]

theorem totalGlue_totalInv {v : Zcyl R → V} {w : ℝ × S1 → V} (hv : v ∈ plusSp V R)
    (hw : w ∈ minusSp V) :
    totalGlue ϑ V hβ hR2 ⟨totalInv β ϑ hR2 v w, totalInv_mem (ϑ := ϑ) hβ hR2 hv hw⟩ = (⟨v, hv⟩, ⟨w, hw⟩) := by
  have hg : glue β R ϑ (totalInv β ϑ hR2 v w) = v := glue_coreInv hβ hR2 v _
  have hm := totalInv_mem (ϑ := ϑ) hβ hR2 hv hw
  refine Prod.ext (Subtype.ext hg) (Subtype.ext (funext fun x => ?_))
  change anti β R ϑ (totalInv β ϑ hR2 v w) x = w x
  rw [anti_eq, av_eq_circ_glue hβ hR2 hm.1 hm.2.1, hg]
  simp only [totalInv]
  rw [antiHat_coreInv hβ hR2]
  abel

/-- **Lemma 2.48** (Memoir p. 47), for `R ≥ 2`: the total glued map
`Φ_a = (⊕_a, ⊖_a) : E → E⁺_a ⊕ E⁻_a` is bijective. -/
theorem totalGlue_bijective : Function.Bijective (totalGlue ϑ V hβ hR2) :=
  ⟨totalGlue_injective (ϑ := ϑ) hβ hR2, fun ⟨⟨_, hv⟩, ⟨_, hw⟩⟩ =>
    ⟨⟨_, totalInv_mem (ϑ := ϑ) hβ hR2 hv hw⟩, totalGlue_totalInv (ϑ := ϑ) hβ hR2 hv hw⟩⟩

variable (ϑ V) in
/-- The isomorphism `Φ_a : E ≅ E⁺_a ⊕ E⁻_a`. -/
def totalGlueEquiv : pairSp V ≃ₗ[ℝ] plusSp V R × minusSp V :=
  LinearEquiv.ofBijective _ (totalGlue_bijective (ϑ := ϑ) hβ hR2)

/-- The inverse of `Φ_a` is given by (2.6) and (2.7) (Memoir p. 48). -/
theorem memoir_eq_2_6_2_7 (v : plusSp V R) (w : minusSp V) :
    ((totalGlueEquiv ϑ V hβ hR2).symm (v, w) : (HalfP → V) × (HalfN → V)) =
      totalInv β ϑ hR2 v.1 w.1 := by
  have e : (totalGlueEquiv ϑ V hβ hR2).symm (v, w) =
      ⟨totalInv β ϑ hR2 v.1 w.1, totalInv_mem (ϑ := ϑ) hβ hR2 v.2 w.2⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    exact (totalGlue_totalInv (ϑ := ϑ) hβ hR2 v.2 w.2).symm
  rw [e]

end Lemma248
end GWMemoir.Neck
