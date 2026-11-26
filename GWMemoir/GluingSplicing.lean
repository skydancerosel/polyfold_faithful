import GWMemoir.GluingLemma248

/-!
# Memoir §2.4: the decomposition (2.8) and the projection `π_a`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, pp. 48–49.

For the total glued map `Φ_a` of Lemma 2.48 (`GWMemoir.GluingLemma248`), on continuous maps:

* `memoir_eq_2_8`: `E = ker ⊕_a ⊕ ker ⊖_a`.
* `piA`: the projection `π_a` onto `ker ⊖_a` along `ker ⊕_a`, `π_a h = Φ_a⁻¹(⊕_a h, 0)`;
  `piA_idem`, `piA_eq_self_iff` (its image is `ker ⊖_a`), `piA_eq_zero_iff` (its kernel is
  `ker ⊕_a`).
* `memoir_eq_2_10`, `memoir_eq_2_11`: the explicit formulas for `π_a`.
-/

open Set Filter Topology MeasureTheory

set_option linter.unusedSectionVars false

noncomputable section

namespace GWMemoir.Neck

variable {β : ℝ → ℝ} {R ϑ : ℝ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ## 1. The decomposition (2.8), the projection `π_a` and the formulas (2.10), (2.11) -/

lemma isCompl_ker_of_bijective {M A B : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup A]
    [Module ℝ A] [AddCommGroup B] [Module ℝ B] (f : M →ₗ[ℝ] A) (g : M →ₗ[ℝ] B)
    (hfg : Function.Bijective (f.prod g)) : IsCompl (LinearMap.ker f) (LinearMap.ker g) := by
  constructor
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hx1, hx2⟩
    have : (f.prod g) x = (f.prod g) 0 := by
      simp [LinearMap.mem_ker.1 hx1, LinearMap.mem_ker.1 hx2]
    exact (Submodule.mem_bot ℝ).2 (hfg.1 this)
  · rw [codisjoint_iff_le_sup]
    intro x _
    obtain ⟨y, hy⟩ := hfg.2 (f x, 0)
    obtain ⟨z, hz⟩ := hfg.2 (0, g x)
    have hy1 : f y = f x := congrArg Prod.fst hy
    have hy2 : g y = 0 := congrArg Prod.snd hy
    have hz1 : f z = 0 := congrArg Prod.fst hz
    have hz2 : g z = g x := congrArg Prod.snd hz
    have hxyz : x = z + y := hfg.1 (by
      show (f x, g x) = (f (z + y), g (z + y))
      rw [map_add, map_add, hy1, hy2, hz1, hz2]
      simp)
    rw [hxyz]
    exact Submodule.add_mem_sup (LinearMap.mem_ker.2 hz1) (LinearMap.mem_ker.2 hy2)

lemma alg_pi (b : ℝ) (P N A : V) :
    (b ^ 2 + (1 - b) ^ 2)⁻¹ • (b • (b • P + (1 - b) • N) - (1 - b) • ((2 * b - 1) • A)) =
      (1 - b / (b ^ 2 + (1 - b) ^ 2)) • A + (b ^ 2 / (b ^ 2 + (1 - b) ^ 2)) • P +
        (b * (1 - b) / (b ^ 2 + (1 - b) ^ 2)) • N := by
  have hg := gam_ne b
  have c1 : 1 - b / (b ^ 2 + (1 - b) ^ 2) = (b ^ 2 + (1 - b) ^ 2)⁻¹ * (-(1 - b) * (2 * b - 1)) := by
    field_simp; ring
  rw [c1]; simp only [div_eq_inv_mul]; module

lemma alg_pi' (b : ℝ) (P N A : V) :
    ((1 - b) ^ 2 + (1 - (1 - b)) ^ 2)⁻¹ • ((1 - (1 - b)) • ((1 - b) • P + (1 - (1 - b)) • N) +
      (1 - b) • ((2 * (1 - b) - 1) • A)) =
      (1 - b / (b ^ 2 + (1 - b) ^ 2)) • A + (b * (1 - b) / (b ^ 2 + (1 - b) ^ 2)) • P +
        (b ^ 2 / (b ^ 2 + (1 - b) ^ 2)) • N := by
  have hg := gam_ne b
  have e : (1 - b) ^ 2 + (1 - (1 - b)) ^ 2 = b ^ 2 + (1 - b) ^ 2 := by ring
  have c1 : 1 - b / (b ^ 2 + (1 - b) ^ 2) = (b ^ 2 + (1 - b) ^ 2)⁻¹ * ((1 - b) * (1 - 2 * b)) := by
    field_simp; ring
  rw [e, c1]; simp only [div_eq_inv_mul]; module

section Projection

variable (hβ : IsCutoff β) (hR2 : 2 ≤ R)
include hβ hR2

/-- **(2.8)** (Memoir p. 48): `E = ker ⊕_a ⊕ ker ⊖_a`. -/
theorem memoir_eq_2_8 :
    IsCompl (LinearMap.ker (glueL (R := R) ϑ V hβ)) (LinearMap.ker (antiL ϑ V hβ hR2)) :=
  isCompl_ker_of_bijective _ _ (totalGlue_bijective (ϑ := ϑ) hβ hR2)

variable (ϑ V) in
/-- The projection `π_a : E → E` onto `ker ⊖_a` along `ker ⊕_a` (Memoir p. 48):
`π_a h = Φ_a⁻¹(⊕_a h, 0)`. -/
def piA : pairSp V →ₗ[ℝ] pairSp V :=
  (totalGlueEquiv ϑ V hβ hR2).symm.toLinearMap ∘ₗ LinearMap.inl ℝ _ _ ∘ₗ glueL (R := R) ϑ V hβ

lemma totalGlue_piA (h : pairSp V) :
    totalGlue ϑ V hβ hR2 (piA ϑ V hβ hR2 h) = (glueL (R := R) ϑ V hβ h, 0) :=
  (totalGlueEquiv ϑ V hβ hR2).apply_symm_apply _

/-- `⊕_a(π_a h) = ⊕_a h`. -/
theorem glueL_piA (h : pairSp V) : glueL (R := R) ϑ V hβ (piA ϑ V hβ hR2 h) = glueL (R := R) ϑ V hβ h :=
  congrArg Prod.fst (totalGlue_piA hβ hR2 h)

/-- `⊖_a(π_a h) = 0`. -/
theorem antiL_piA (h : pairSp V) : antiL ϑ V hβ hR2 (piA ϑ V hβ hR2 h) = 0 :=
  congrArg Prod.snd (totalGlue_piA hβ hR2 h)

/-- `π_a` is a projection. -/
theorem piA_idem (h : pairSp V) : piA ϑ V hβ hR2 (piA ϑ V hβ hR2 h) = piA ϑ V hβ hR2 h :=
  totalGlue_injective hβ hR2 (by rw [totalGlue_piA, totalGlue_piA, glueL_piA])

/-- `π_a h = h` iff `⊖_a h = 0`: the image of `π_a` is `ker ⊖_a`. -/
theorem piA_eq_self_iff (h : pairSp V) :
    piA ϑ V hβ hR2 h = h ↔ antiL ϑ V hβ hR2 h = 0 := by
  constructor
  · intro e; rw [← e]; exact antiL_piA hβ hR2 h
  · intro e
    exact totalGlue_injective hβ hR2 (by rw [totalGlue_piA]; exact Prod.ext rfl e.symm)

/-- The kernel of `π_a` is `ker ⊕_a`. -/
theorem piA_eq_zero_iff (h : pairSp V) : piA ϑ V hβ hR2 h = 0 ↔ glueL (R := R) ϑ V hβ h = 0 := by
  constructor
  · intro e; rw [← glueL_piA hβ hR2 h, e, map_zero]
  · intro e
    exact totalGlue_injective hβ hR2 (by rw [totalGlue_piA, e, map_zero]; rfl)

lemma piA_coe (h : pairSp V) :
    (piA ϑ V hβ hR2 h : (HalfP → V) × (HalfN → V)) =
      coreInv β R ϑ (by linarith) (glue β R ϑ h.1) fun x => (2 * βa β R x.1 - 1) • av R h.1 := by
  have e := memoir_eq_2_6_2_7 (ϑ := ϑ) hβ hR2 (glueL (R := R) ϑ V hβ h) 0
  change ((totalGlueEquiv ϑ V hβ hR2).symm (glueL (R := R) ϑ V hβ h, 0) : (HalfP → V) × (HalfN → V)) = _
  rw [e]
  simp only [totalInv]
  have hg : ((glueL (R := R) ϑ V hβ h : plusSp V R) : Zcyl R → V) = glue β R ϑ h.1 := rfl
  rw [hg, ← av_eq_circ_glue hβ hR2 h.2.1 h.2.2.1]
  simp

/-- **(2.10)** (Memoir p. 48): `π_a(h⁺,h⁻) = (η⁺,η⁻)` with
`η⁺(s,t) = (1 - β_a/γ_a) av_a + (β_a²/γ_a) h⁺(s,t) + (β_a(1 - β_a)/γ_a) h⁻(s - R, t - ϑ)`
(the last term vanishes for `s ≥ R/2 + 1`, where `h⁻(s - R, ·)` is not defined). -/
theorem memoir_eq_2_10 (h : pairSp V) {s : ℝ} (hs : 0 ≤ s) (t : S1) :
    (piA ϑ V hβ hR2 h).1.1 (⟨s, hs⟩, t) =
      (1 - βa β R s / γa β R s) • av R h.1 + (βa β R s ^ 2 / γa β R s) • h.1.1 (⟨s, hs⟩, t) +
        (βa β R s * (1 - βa β R s) / γa β R s) • extN h.1.2 (s - R, t - (ϑ : S1)) := by
  have hR : (0 : ℝ) ≤ R := by linarith
  rw [piA_coe]
  change (γa β R s)⁻¹ • (βa β R s • extZ hR (glue β R ϑ h.1) (s, t) -
      (1 - βa β R s) • ((2 * βa β R s - 1) • av R h.1)) = _
  rw [← extP_of_nonneg h.1.1 hs t]
  rcases lt_or_ge R s with hs' | hs'
  · have hb : βa β R s = 0 := βa_zero hβ (by linarith)
    rw [γa_of_βa_zero hb, hb]; simp
  rw [extZ_of_mem hR _ ⟨hs, hs'⟩, γa_def]
  simp only [glue, sh]
  exact alg_pi _ _ _ _

/-- **(2.11)** (Memoir p. 49): `η⁻(s',t') = (1 - β_a(-s')/γ_a(-s')) av_a
+ (β_a(-s')(1 - β_a(-s'))/γ_a(-s')) h⁺(s' + R, t' + ϑ) + (β_a(-s')²/γ_a(-s')) h⁻(s',t')`. -/
theorem memoir_eq_2_11 (h : pairSp V) {s : ℝ} (hs : s ≤ 0) (t : S1) :
    (piA ϑ V hβ hR2 h).1.2 (⟨s, hs⟩, t) =
      (1 - βa β R (-s) / γa β R (-s)) • av R h.1 +
        (βa β R (-s) * (1 - βa β R (-s)) / γa β R (-s)) • extP h.1.1 (s + R, t + (ϑ : S1)) +
        (βa β R (-s) ^ 2 / γa β R (-s)) • h.1.2 (⟨s, hs⟩, t) := by
  have hR : (0 : ℝ) ≤ R := by linarith
  rw [piA_coe]
  change (γa β R (s + R))⁻¹ • ((1 - βa β R (s + R)) • extZ hR (glue β R ϑ h.1) (s + R, t + ϑ) +
      βa β R (s + R) • ((2 * βa β R (s + R) - 1) • av R h.1)) = _
  have hsh : sh R ϑ (s + R, t + (ϑ : S1)) = (s, t) := by simp [sh]
  rw [← extN_of_nonpos h.1.2 hs, ← hsh]
  rcases lt_or_ge (s + R) 0 with hs' | hs'
  · have hb : βa β R (s + R) = 1 := βa_one hβ (by linarith)
    have hb' : βa β R (-s) = 0 := by rw [βa_add_R hβ] at hb; linarith
    rw [γa_of_βa_one hb, γa_of_βa_zero hb', hb, hb']; norm_num
  rw [extZ_of_mem hR _ ⟨hs', by linarith⟩, γa_def, γa_def]
  simp only [glue]
  rw [βa_add_R hβ]
  exact alg_pi' _ _ _ _

end Projection

/-! ## 2. The hat versions: `F`, `⊕̂_a`, `⊖̂_a`, `π̂_a` and (2.12) -/

section Hat

variable (V) in
/-- `F`: pairs `(ξ⁺,ξ⁻)` of continuous maps with common asymptotic constant `0`, uniformly in `t`
(Memoir pp. 50–51). -/
def hatSp : Submodule ℝ ((HalfP → V) × (HalfN → V)) where
  carrier := {h | Continuous h.1 ∧ Continuous h.2 ∧ LimTop (extP h.1) 0 ∧ LimBot (extN h.2) 0}
  add_mem' := by
    rintro h k ⟨h1, h2, hc1, hc2⟩ ⟨k1, k2, hd1, hd2⟩
    refine ⟨h1.add k1, h2.add k2, ?_, ?_⟩
    · show LimTop (extP h.1 + extP k.1) 0; simpa using hc1.add hd1
    · show LimBot (extN h.2 + extN k.2) 0; simpa using hc2.add hd2
  zero_mem' := ⟨continuous_const, continuous_const, LimTop.zero, LimBot.zero⟩
  smul_mem' := by
    rintro r h ⟨h1, h2, hc1, hc2⟩
    refine ⟨h1.const_smul r, h2.const_smul r, ?_, ?_⟩
    · show LimTop (r • extP h.1) 0; simpa using hc1.smul r
    · show LimBot (r • extN h.2) 0; simpa using hc2.smul r

variable (V) in
/-- The target `F̂_a` of `⊖̂_a`: continuous maps `C_a → V` with both asymptotic constants `0`. -/
def hatMinusSp : Submodule ℝ (ℝ × S1 → V) where
  carrier := {w | Continuous w ∧ LimTop w 0 ∧ LimBot w 0}
  add_mem' := by
    rintro w w' ⟨h1, hc1, hc2⟩ ⟨k1, hd1, hd2⟩
    exact ⟨h1.add k1, by simpa using hc1.add hd1, by simpa using hc2.add hd2⟩
  zero_mem' := ⟨continuous_const, LimTop.zero, LimBot.zero⟩
  smul_mem' := by
    rintro r w ⟨h1, hc1, hc2⟩
    exact ⟨h1.const_smul r, by simpa using hc1.smul r, by simpa using hc2.smul r⟩

lemma hatSp_le : hatSp V ≤ pairSp V := fun _ ⟨h1, h2, hc1, hc2⟩ => ⟨h1, h2, 0, hc1, hc2⟩

variable (hβ : IsCutoff β) (hR2 : 2 ≤ R)
include hβ hR2

theorem antiHat_mem {h : (HalfP → V) × (HalfN → V)} (hh : h ∈ hatSp V) :
    antiHat β R ϑ h ∈ hatMinusSp V := by
  obtain ⟨h1, h2, hc1, hc2⟩ := hh
  refine ⟨continuous_antiHat hβ h1 h2, ?_, ?_⟩
  · have := hc1.neg
    rw [neg_zero] at this
    refine this.congr (S₀ := R / 2 + 1) fun x hx => ?_
    simp only [antiHat]
    rw [βa_zero hβ hx]; simp
  · refine (LimBot.comp_sh (R := R) (ϑ := ϑ) hc2).congr (S₀ := R / 2 - 1) fun x hx => ?_
    simp only [antiHat]
    rw [βa_one hβ hx]; simp

theorem coreInv_mem_hat {v : Zcyl R → V} {w : ℝ × S1 → V} (hv : v ∈ plusSp V R)
    (hw : w ∈ hatMinusSp V) : coreInv β R ϑ (by linarith) v w ∈ hatSp V := by
  obtain ⟨hw1, hc1, hc2⟩ := hw
  obtain ⟨k1, k2⟩ := continuous_coreInv (ϑ := ϑ) hβ hR2 hv hw1
  refine ⟨k1, k2, ?_, ?_⟩
  · have := hc1.neg
    rw [neg_zero] at this
    refine this.congr (S₀ := R / 2 + 1) fun x hx => ?_
    obtain ⟨s, t⟩ := x
    have hb0 : βa β R s = 0 := βa_zero hβ hx
    rw [coreInv_fst _ v _ (by simp only at hx; linarith), γa_of_βa_zero hb0, hb0]
    simp
  · refine (LimBot.comp_ush (R := R) (ϑ := ϑ) hc2).congr (S₀ := -(R / 2) - 1) fun x hx => ?_
    have hs : (ush R ϑ x).1 ≤ R := by simp only [ush]; linarith
    have hb1 : βa β R (ush R ϑ x).1 = 1 := βa_one hβ (by simp only [ush]; linarith)
    conv_lhs => rw [← sh_ush (R := R) (ϑ := ϑ) x]
    rw [show ush R ϑ x = ((ush R ϑ x).1, (ush R ϑ x).2) from rfl, coreInv_snd _ v _ hs,
      γa_of_βa_one hb1, hb1]
    simp

variable (ϑ V) in
/-- `⊕̂_a : F → E⁺_a`, given by the same formula as `⊕_a` (Memoir p. 51). -/
def glueHatL : hatSp V →ₗ[ℝ] plusSp V R :=
  (glueLin β R ϑ).restrict fun _ hh => continuous_glue hβ hh.1 hh.2.1

variable (ϑ V) in
/-- `⊖̂_a : F → F̂_a` (Memoir p. 51). -/
def antiHatL : hatSp V →ₗ[ℝ] hatMinusSp V :=
  (antiHatLin β R ϑ).restrict fun _ hh => antiHat_mem hβ hR2 hh

variable (ϑ V) in
/-- The total hat-gluing `Φ̂_a = (⊕̂_a, ⊖̂_a) : F → E⁺_a ⊕ F̂_a` (Memoir p. 52). -/
def totalHat : hatSp V →ₗ[ℝ] plusSp V R × hatMinusSp V :=
  (glueHatL (R := R) ϑ V hβ).prod (antiHatL ϑ V hβ hR2)

/-- The level-0 (continuous) form of **Theorem 2.50(1)** (Memoir p. 52), for `R ≥ 2`: the total
hat-gluing `Φ̂_a` is bijective, with inverse the solution operator of (2.5). -/
theorem memoir_hat_gluing_bijective : Function.Bijective (totalHat ϑ V hβ hR2) := by
  refine ⟨fun h k hhk => ?_, fun ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ => ⟨⟨_, coreInv_mem_hat (ϑ := ϑ) hβ hR2 hv hw⟩, ?_⟩⟩
  · have eg : glue β R ϑ h.1 = glue β R ϑ k.1 := congrArg Subtype.val (congrArg Prod.fst hhk)
    have eh : antiHat β R ϑ h.1 = antiHat β R ϑ k.1 :=
      congrArg Subtype.val (congrArg Prod.snd hhk)
    apply Subtype.ext
    rw [← coreInv_glue (ϑ := ϑ) hβ hR2 h.1, ← coreInv_glue (ϑ := ϑ) hβ hR2 k.1, eg, eh]
  · exact Prod.ext (Subtype.ext (glue_coreInv hβ hR2 v w))
      (Subtype.ext (antiHat_coreInv hβ hR2 v w))

variable (ϑ V) in
/-- The isomorphism `Φ̂_a : F ≅ E⁺_a ⊕ F̂_a`. -/
def totalHatEquiv : hatSp V ≃ₗ[ℝ] plusSp V R × hatMinusSp V :=
  LinearEquiv.ofBijective _ (memoir_hat_gluing_bijective (ϑ := ϑ) hβ hR2)

/-- `F = ker ⊕̂_a ⊕ ker ⊖̂_a` (Memoir p. 51). -/
theorem memoir_hat_decomposition :
    IsCompl (LinearMap.ker (glueHatL (R := R) ϑ V hβ)) (LinearMap.ker (antiHatL ϑ V hβ hR2)) :=
  isCompl_ker_of_bijective _ _ (memoir_hat_gluing_bijective (ϑ := ϑ) hβ hR2)

variable (ϑ V) in
/-- The projection `π̂_a : F → F` onto `ker ⊖̂_a` along `ker ⊕̂_a` (Memoir p. 51). -/
def piHat : hatSp V →ₗ[ℝ] hatSp V :=
  (totalHatEquiv ϑ V hβ hR2).symm.toLinearMap ∘ₗ LinearMap.inl ℝ _ _ ∘ₗ glueHatL (R := R) ϑ V hβ

lemma totalHat_piHat (h : hatSp V) :
    totalHat ϑ V hβ hR2 (piHat ϑ V hβ hR2 h) = (glueHatL (R := R) ϑ V hβ h, 0) :=
  (totalHatEquiv ϑ V hβ hR2).apply_symm_apply _

lemma glueHatL_piHat (h : hatSp V) :
    glueHatL (R := R) ϑ V hβ (piHat ϑ V hβ hR2 h) = glueHatL (R := R) ϑ V hβ h :=
  congrArg Prod.fst (totalHat_piHat hβ hR2 h)

theorem piHat_idem (h : hatSp V) : piHat ϑ V hβ hR2 (piHat ϑ V hβ hR2 h) = piHat ϑ V hβ hR2 h :=
  (memoir_hat_gluing_bijective (ϑ := ϑ) hβ hR2).1 (by
    rw [totalHat_piHat, totalHat_piHat, glueHatL_piHat])

theorem piHat_eq_self_iff (h : hatSp V) :
    piHat ϑ V hβ hR2 h = h ↔ antiHatL ϑ V hβ hR2 h = 0 := by
  constructor
  · intro e; rw [← e]; exact congrArg Prod.snd (totalHat_piHat hβ hR2 h)
  · intro e
    exact (memoir_hat_gluing_bijective (ϑ := ϑ) hβ hR2).1
      (by rw [totalHat_piHat]; exact Prod.ext rfl e.symm)

theorem piHat_eq_zero_iff (h : hatSp V) :
    piHat ϑ V hβ hR2 h = 0 ↔ glueHatL (R := R) ϑ V hβ h = 0 := by
  constructor
  · intro e; rw [← glueHatL_piHat hβ hR2 h, e, map_zero]
  · intro e
    exact (memoir_hat_gluing_bijective (ϑ := ϑ) hβ hR2).1
      (by rw [totalHat_piHat, e, map_zero]; rfl)

lemma piHat_coe (h : hatSp V) :
    (piHat ϑ V hβ hR2 h : (HalfP → V) × (HalfN → V)) =
      coreInv β R ϑ (by linarith) (glue β R ϑ h.1) 0 := by
  have e : piHat ϑ V hβ hR2 h = ⟨_, coreInv_mem_hat (ϑ := ϑ) hβ hR2 (glueHatL (R := R) ϑ V hβ h).2
      (hatMinusSp V).zero_mem⟩ := by
    change (totalHatEquiv ϑ V hβ hR2).symm (glueHatL (R := R) ϑ V hβ h, 0) = _
    rw [LinearEquiv.symm_apply_eq]
    exact Prod.ext (Subtype.ext (glue_coreInv hβ hR2 _ _).symm)
      (Subtype.ext (antiHat_coreInv hβ hR2 _ _).symm)
  rw [e]; rfl

/-- **(2.12)**, first line (Memoir p. 51): `π̂_a(ξ⁺,ξ⁻) = (η⁺,η⁻)` with
`η⁺(s,t) = (β_a²/γ_a) ξ⁺(s,t) + (β_a(1 - β_a)/γ_a) ξ⁻(s - R, t - ϑ)`. -/
theorem memoir_eq_2_12_plus (h : hatSp V) {s : ℝ} (hs : 0 ≤ s) (t : S1) :
    (piHat ϑ V hβ hR2 h).1.1 (⟨s, hs⟩, t) =
      (βa β R s ^ 2 / γa β R s) • h.1.1 (⟨s, hs⟩, t) +
        (βa β R s * (1 - βa β R s) / γa β R s) • extN h.1.2 (s - R, t - (ϑ : S1)) := by
  have hR : (0 : ℝ) ≤ R := by linarith
  rw [piHat_coe]
  change (γa β R s)⁻¹ • (βa β R s • extZ hR (glue β R ϑ h.1) (s, t) -
      (1 - βa β R s) • (0 : ℝ × S1 → V) (s, t)) = _
  rw [← extP_of_nonneg h.1.1 hs t]
  rcases lt_or_ge R s with hs' | hs'
  · have hb : βa β R s = 0 := βa_zero hβ (by linarith)
    rw [γa_of_βa_zero hb, hb]; simp
  rw [extZ_of_mem hR _ ⟨hs, hs'⟩, γa_def]
  simp only [glue, sh, Pi.zero_apply, smul_zero, sub_zero, div_eq_inv_mul]
  module

/-- **(2.12)**, second line (Memoir p. 51): `η⁻(s',t') = (β_a(-s')(1 - β_a(-s'))/γ_a(-s'))
ξ⁺(s' + R, t' + ϑ) + (β_a(-s')²/γ_a(-s')) ξ⁻(s',t')`. -/
theorem memoir_eq_2_12_minus (h : hatSp V) {s : ℝ} (hs : s ≤ 0) (t : S1) :
    (piHat ϑ V hβ hR2 h).1.2 (⟨s, hs⟩, t) =
      (βa β R (-s) * (1 - βa β R (-s)) / γa β R (-s)) • extP h.1.1 (s + R, t + (ϑ : S1)) +
        (βa β R (-s) ^ 2 / γa β R (-s)) • h.1.2 (⟨s, hs⟩, t) := by
  have hR : (0 : ℝ) ≤ R := by linarith
  rw [piHat_coe]
  change (γa β R (s + R))⁻¹ • ((1 - βa β R (s + R)) • extZ hR (glue β R ϑ h.1) (s + R, t + ϑ) +
      βa β R (s + R) • (0 : ℝ × S1 → V) (s + R, t + ϑ)) = _
  have hsh : sh R ϑ (s + R, t + (ϑ : S1)) = (s, t) := by simp [sh]
  rw [← extN_of_nonpos h.1.2 hs, ← hsh]
  rcases lt_or_ge (s + R) 0 with hs' | hs'
  · have hb : βa β R (s + R) = 1 := βa_one hβ (by linarith)
    have hb' : βa β R (-s) = 0 := by rw [βa_add_R hβ] at hb; linarith
    rw [γa_of_βa_one hb, hb', hb]; simp
  rw [extZ_of_mem hR _ ⟨hs', by linarith⟩, γa_def, γa_def]
  simp only [glue]
  rw [βa_add_R hβ]
  have e : (1 - βa β R (-s)) ^ 2 + (1 - (1 - βa β R (-s))) ^ 2 =
      βa β R (-s) ^ 2 + (1 - βa β R (-s)) ^ 2 := by ring
  rw [e]
  simp only [Pi.zero_apply, smul_zero, add_zero, div_eq_inv_mul, sub_sub_cancel]
  module

end Hat

/-! ## 3. The memoir's parameters: Lemma 2.48 and Theorem 2.50(1) at level 0 -/

theorem two_le_glLength {a : ℂ} (h0 : a ≠ 0) (h : ‖a‖ < 1 / 2) : 2 ≤ glLength a := by
  linarith [four_lt_glLength h0 h]

/-- **Lemma 2.48** (Memoir p. 47), at level 0: for a gluing parameter `0 < |a| < 1/2`, with
`R = φ(|a|)` and `a = |a| e^{-2πiϑ}`, the total glued map `Φ_a = (⊕_a, ⊖_a) : E → E⁺_a ⊕ E⁻_a`
is a linear isomorphism; its inverse is (2.6), (2.7) (`memoir_eq_2_6_2_7`). -/
theorem memoir_lemma_2_48 (hβ : IsCutoff β) {a : ℂ} (h0 : a ≠ 0) (h : ‖a‖ < 1 / 2) :
    Function.Bijective (totalGlue (glTwist a) V hβ (two_le_glLength h0 h)) :=
  totalGlue_bijective hβ _

/-- The hat version (Memoir p. 52), at level 0: `Φ̂_a = (⊕̂_a, ⊖̂_a) : F → E⁺_a ⊕ F̂_a` is a linear
isomorphism for `0 < |a| < 1/2`. -/
theorem memoir_hat_gluing_iso (hβ : IsCutoff β) {a : ℂ} (h0 : a ≠ 0) (h : ‖a‖ < 1 / 2) :
    Function.Bijective (totalHat (glTwist a) V hβ (two_le_glLength h0 h)) :=
  memoir_hat_gluing_bijective hβ _

/-! ## 4. Proposition 2.51: the exponential map in a flat chart commutes with gluing -/

lemma norm_glue_le_max (hβ : IsCutoff β) (h : (HalfP → V) × (HalfN → V)) (z : Zcyl R) :
    ‖glue β R ϑ h z‖ ≤ max ‖extP h.1 (z.1.1, z.2)‖ ‖extN h.2 (sh R ϑ (z.1.1, z.2))‖ := by
  obtain ⟨hb0, hb1⟩ := hβ.mem (z.1.1 - R / 2)
  set b := βa β R z.1.1
  have hb0' : 0 ≤ b := hb0
  have hb1' : b ≤ 1 := hb1
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hb0', Real.norm_of_nonneg (by linarith)]
  nlinarith [le_max_left ‖extP h.1 (z.1.1, z.2)‖ ‖extN h.2 (sh R ϑ (z.1.1, z.2))‖,
    le_max_right ‖extP h.1 (z.1.1, z.2)‖ ‖extN h.2 (sh R ϑ (z.1.1, z.2))‖]

section Prop251

variable {Q : Type*} (ψ : Q ≃ V) {T : Q → Type*} [∀ p, AddCommGroup (T p)] [∀ p, Module ℝ (T p)]
  (dψ : ∀ p, T p ≃ₗ[ℝ] V) (ex : ∀ p, T p → Q)

/-- The chart `ψ : R(q) → ℝ²ⁿ` is flat for the exponential map over `R₂(q) = ψ⁻¹(B₂(0))`:
`ψ(exp_p X) = ψ(p) + Tψ(p) X` for `|X|_p ≤ 2`, the metric being the pull-back of the Euclidean one
(Memoir p. 52). -/
def IsFlatExp : Prop :=
  ∀ p (X : T p), ‖ψ p‖ < 2 → ‖dψ p X‖ ≤ 2 → ψ (ex p X) = ψ p + dψ p X

/-- The flat chart `ψ = id` on `V`, with `exp_p X = p + X`, satisfies the hypothesis. -/
theorem isFlatExp_id :
    IsFlatExp (Equiv.refl V) (T := fun _ => V) (fun _ => LinearEquiv.refl ℝ V) (fun p X => p + X) :=
  fun _ _ _ _ => rfl

variable (β R ϑ) in
/-- The glued map `⊕_a(u) : Z_a → Q`, `ψ(⊕_a(u)[s,t]) = ⊕⁰_a(ψ∘u⁺, ψ∘u⁻)[s,t]` (Memoir p. 53);
here `u = (u⁺,u⁻)` is given in the holomorphic polar coordinates `h_x`, `h_y`. -/
def glueQ (u : (HalfP → Q) × (HalfN → Q)) : Zcyl R → Q :=
  fun z => ψ.symm (glue β R ϑ (fun x => ψ (u.1 x), fun x => ψ (u.2 x)) z)

variable (β R ϑ) in
/-- The glued section `⊕_a(η)`, `Tψ(⊕_a(u)[s,t]) ⊕_a(η)[s,t] = ⊕⁰_a(Tψ(u⁺)η⁺, Tψ(u⁻)η⁻)[s,t]`
(Memoir p. 53). -/
def glueT (u : (HalfP → Q) × (HalfN → Q)) (η : (∀ x, T (u.1 x)) × (∀ x, T (u.2 x))) :
    ∀ z, T (glueQ β R ϑ ψ u z) :=
  fun z => (dψ _).symm (glue β R ϑ (fun x => dψ _ (η.1 x), fun x => dψ _ (η.2 x)) z)

/-- `exp_u(η)`, in the coordinates `h_x`, `h_y`. -/
def expSec (u : (HalfP → Q) × (HalfN → Q)) (η : (∀ x, T (u.1 x)) × (∀ x, T (u.2 x))) :
    (HalfP → Q) × (HalfN → Q) :=
  (fun x => ex _ (η.1 x), fun x => ex _ (η.2 x))

/-- **Proposition 2.51** (Memoir p. 53): `exp_{⊕_a(u)}(⊕_a(η)) = ⊕_a(exp_u(η))`, for `u` with
values in `R₂(q)` and `|η| ≤ 2` (so that `exp_u(η)` is computed in the flat chart). -/
theorem memoir_proposition_2_51 (hβ : IsCutoff β) (hex : IsFlatExp ψ dψ ex)
    (u : (HalfP → Q) × (HalfN → Q)) (η : (∀ x, T (u.1 x)) × (∀ x, T (u.2 x)))
    (hu1 : ∀ x, ‖ψ (u.1 x)‖ < 2) (hu2 : ∀ x, ‖ψ (u.2 x)‖ < 2)
    (hη1 : ∀ x, ‖dψ _ (η.1 x)‖ ≤ 2) (hη2 : ∀ x, ‖dψ _ (η.2 x)‖ ≤ 2) :
    (fun z => ex _ (glueT β R ϑ ψ dψ u η z)) = glueQ β R ϑ ψ (expSec ex u η) := by
  funext z
  apply ψ.injective
  set U : (HalfP → V) × (HalfN → V) := (fun x => ψ (u.1 x), fun x => ψ (u.2 x))
  set W : (HalfP → V) × (HalfN → V) := (fun x => dψ _ (η.1 x), fun x => dψ _ (η.2 x))
  have hU : ψ (glueQ β R ϑ ψ u z) = glue β R ϑ U z := ψ.apply_symm_apply _
  have hW : dψ _ (glueT β R ϑ ψ dψ u η z) = glue β R ϑ W z := (dψ _).apply_symm_apply _
  have n1 : ‖ψ (glueQ β R ϑ ψ u z)‖ < 2 := by
    rw [hU]
    refine (norm_glue_le_max hβ U z).trans_lt (max_lt ?_ ?_)
    · exact hu1 _
    · exact hu2 _
  have n2 : ‖dψ _ (glueT β R ϑ ψ dψ u η z)‖ ≤ 2 := by
    rw [hW]
    refine (norm_glue_le_max hβ W z).trans (max_le ?_ ?_)
    · exact hη1 _
    · exact hη2 _
  have hE : (fun x => ψ ((expSec ex u η).1 x), fun x => ψ ((expSec ex u η).2 x)) = U + W :=
    Prod.ext (funext fun x => hex _ _ (hu1 x) (hη1 x)) (funext fun x => hex _ _ (hu2 x) (hη2 x))
  rw [hex _ _ n1 n2, hU, hW]
  change _ = ψ (ψ.symm _)
  rw [ψ.apply_symm_apply, hE]
  exact (congrFun ((glueLin β R ϑ).map_add U W) z).symm

end Prop251

end GWMemoir.Neck
