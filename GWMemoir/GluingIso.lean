import GWMemoir.GluingLevels

/-!
# Memoir §2.4, Theorem 2.49: the total glued map as an sc-isomorphism, and the splicing

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §2.4, pp. 49–51.

* **`memoir_theorem_2_49_one`** (Theorem 2.49(1), for a fixed parameter): for `0 < |a| < 1/2`,
  the levels `Phi m` of `GWMemoir.GluingLevels` (`Φ_a = (⊕_a, ⊖_a)` in the coordinates
  `h^± = c + r^±`, `(1 - 2β_a) c' + w`) form an sc-isomorphism `E ≅ G^a`, with inverse `Psi m`
  (the Sobolev form of (2.6), (2.7)).  Only `R ≥ 2` is used (`gluingScIso`).
* `piLvl`: the projection `π_a = Φ_a⁻¹ ∘ (⊕_a, 0) ∘ Φ_a` onto `ker ⊖_a` along `ker ⊕_a`, on each
  level (`piLvl_idem`, `antiGlue_piLvl`, `glue_piLvl`); `piSc` extends it by `π₀ = id`.
* **`MemoirTheorem249Two`** (Theorem 2.49(2), as a statement): `(a, h) ↦ π_a h` is sc-smooth on
  `B_{1/2} ⊕ E`, so that `(π, E, B_{1/2})` is an sc-smooth splicing.  This is the sc-smoothness in
  the gluing parameter; it is stated here and not proved.
-/

open Set Filter Topology MeasureTheory
open Polyfold Polyfold.CylinderSobolev

set_option linter.unusedSectionVars false

noncomputable section

namespace GWMemoir.Neck

variable {β : ℝ → ℝ} {R : ℝ}

/-! ## 1. Theorem 2.49(1) at a fixed parameter -/

section Quot

variable (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (m : ℕ)

/-- The quotient maps, typed on `H^{3+m,δ_m}(ℝ × S¹)`. -/
def qP : H (3 + m) (δ_nonneg δ h0 hmono m) →L[ℝ] (scHalfPos δ h0 hmono) m := (LP δ h0 hmono m).mkQL
def qN : H (3 + m) (δ_nonneg δ h0 hmono m) →L[ℝ] (scHalfNeg δ h0 hmono) m := (LN δ h0 hmono m).mkQL
def qZ : H (3 + m) (δ_nonneg δ h0 hmono m) →L[ℝ] (scFin δ h0 hmono R) m :=
  (LZ δ h0 hmono R m).mkQL

lemma le3 : 3 + m ≤ 3 + (m + 1) := by omega

end Quot

section Inverse

variable {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}
variable (hβ : IsCutoff β) (hR2 : 2 ≤ R) (ϑ : ℝ) (m : ℕ)
include hβ hR2

local notation "M1" => m1 hβ R (3 + m)
local notation "M2" => m2 hβ R (3 + m)
local notation "M3" => m3 hβ R (3 + m)
local notation "M4" => m4 hβ R (3 + m)
local notation "M5" => m5 hβ R (3 + m)
local notation "χm" => toH (3 + m) (δ_nonneg δ h0 hmono m) (isTest_chiZ R)
local notation "χ1" => toH (3 + (m + 1)) (δ_nonneg δ h0 hmono (m + 1)) (isTest_chiZ R)
local notation "QP" => qP δ h0 hmono m
local notation "QN" => qN δ h0 hmono m
local notation "QZ" => qZ δ h0 hmono (R := R) m
local notation "ι" => inclH (δ_nonneg δ h0 hmono m) (δ_nonneg δ h0 hmono (m + 1))
  (le3 m) (hmono.monotone (Nat.le_succ m))

theorem psi_phi (x : (scPair δ h0 hmono) m) :
    Psi δ h0 hmono hβ hR2 ϑ m (Phi δ h0 hmono hβ hR2 ϑ m x) = x := by
  obtain ⟨c, p, q⟩ := x
  obtain ⟨a, rfl⟩ : ∃ a, QP a = p := Submodule.mkQ_surjective _ p
  obtain ⟨b, rfl⟩ : ∃ b, QN b = q := Submodule.mkQ_surjective _ q
  set V : H (3 + m) (δ_nonneg δ h0 hmono m) :=
    c • χm + mulHL _ M1 a + mulHL _ M2 (shH R ϑ b) with hV
  have htr : TZ δ h0 hmono hR2 m (QZ V) -
      (TP δ h0 hmono hR2 m (QP a) + TN δ h0 hmono hR2 m (QN b)) = c := by
    change trH (hm3 m) (R / 2) V -
      ((1 / 2 : ℝ) • trH (hm3 m) (R / 2) a + (1 / 2 : ℝ) • trH (hm3 m) (-(R / 2)) b) = c
    rw [hV, map_add, map_add, map_smul, trH_mulHL, trH_mulHL, trH_shH,
      trH_chi (h0 := h0) (hmono := hmono) hβ hR2 m,
      βa_half' hβ hR2, show R / 2 - R = -(R / 2) by ring, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change TZ δ h0 hmono hR2 m (QZ V) -
      (TP δ h0 hmono hR2 m (QP a) + TN δ h0 hmono hR2 m (QN b)) = c
    exact htr
  · change PP δ h0 hmono hβ hR2 m (QZ V) - (TZ δ h0 hmono hR2 m (QZ V) -
      (TP δ h0 hmono hR2 m (QP a) + TN δ h0 hmono hR2 m (QN b))) • eP δ h0 hmono hβ (R := R) m -
      WP δ h0 hmono hβ (R := R) m (mulHL _ M5 a + mulHL _ M1 (shH R ϑ b)) = QP a
    rw [htr]
    change QP (mulHL _ M3 V) - c • QP (mulHL _ M3 χm) -
      QP (mulHL _ M4 (mulHL _ M5 a + mulHL _ M1 (shH R ϑ b))) = QP a
    rw [← map_smul, ← map_sub, ← map_sub, hV, identA (h0 := h0) (hmono := hmono) hβ hR2 ϑ m]
  · change PN δ h0 hmono hβ hR2 ϑ m (QZ V) - (TZ δ h0 hmono hR2 m (QZ V) -
      (TP δ h0 hmono hR2 m (QP a) + TN δ h0 hmono hR2 m (QN b))) •
        eN δ h0 hmono hβ (R := R) ϑ m +
      WN δ h0 hmono hβ (R := R) ϑ m (mulHL _ M5 a + mulHL _ M1 (shH R ϑ b)) = QN b
    rw [htr]
    change QN (shH (-R) (-ϑ) (mulHL _ M4 V)) - c • QN (shH (-R) (-ϑ) (mulHL _ M4 χm)) +
      QN (shH (-R) (-ϑ) (mulHL _ M3 (mulHL _ M5 a + mulHL _ M1 (shH R ϑ b)))) = QN b
    rw [← map_smul, ← map_sub, ← map_add, ← map_smul, ← map_sub, ← map_add, hV,
      identB (h0 := h0) (hmono := hmono) hβ hR2 ϑ m, shH_shH]

theorem phi_psi (y : (scG δ h0 hmono R) m) :
    Phi δ h0 hmono hβ hR2 ϑ m (Psi δ h0 hmono hβ hR2 ϑ m y) = y := by
  obtain ⟨v, c', w⟩ := y
  obtain ⟨v, rfl⟩ : ∃ v', QZ v' = v := Submodule.mkQ_surjective _ v
  obtain ⟨w, rfl⟩ : ∃ w' : H (3 + m) (δ_nonneg δ h0 hmono m), w' = w := ⟨w, rfl⟩
  set c := trH (hm3 m) (R / 2) v - c' with hc
  set Xp : H (3 + m) (δ_nonneg δ h0 hmono m) :=
    mulHL _ M3 v - c • mulHL _ M3 χm - mulHL _ M4 w with hXp
  set Xn : H (3 + m) (δ_nonneg δ h0 hmono m) :=
    mulHL _ M4 v - c • mulHL _ M4 χm + mulHL _ M3 w with hXn
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change QZ (c • χm + mulHL _ M1 Xp + mulHL _ M2 (shH R ϑ (shH (-R) (-ϑ) Xn))) = QZ v
    rw [shH_shH', hXp, hXn, identC (h0 := h0) (hmono := hmono) hβ hR2 m]
  · change (1 / 2 : ℝ) • trH (hm3 m) (R / 2) Xp +
      (1 / 2 : ℝ) • trH (hm3 m) (-(R / 2)) (shH (-R) (-ϑ) Xn) = c'
    rw [trH_shH, show -(R / 2) - -R = R / 2 by ring, hXp, hXn]
    simp only [map_add, map_sub, map_smul, trH_mulHL, trH_chi (h0 := h0) (hmono := hmono) hβ hR2 m,
      βa_half' hβ hR2, F3_half,
      F4_half, smul_eq_mul]
    rw [hc]; ring
  · change mulHL _ M5 Xp + mulHL _ M1 (shH R ϑ (shH (-R) (-ϑ) Xn)) = w
    rw [shH_shH', hXp, hXn, identD (h0 := h0) (hmono := hmono) hβ hR2 m]

theorem phi_incl (x : (scPair δ h0 hmono) (m + 1)) :
    (scG δ h0 hmono R).incl m (Phi δ h0 hmono hβ hR2 ϑ (m + 1) x) =
      Phi δ h0 hmono hβ hR2 ϑ m ((scPair δ h0 hmono).incl m x) := by
  obtain ⟨c, p, q⟩ := x
  obtain ⟨a, rfl⟩ : ∃ a, qP δ h0 hmono (m + 1) a = p := Submodule.mkQ_surjective _ p
  obtain ⟨b, rfl⟩ : ∃ b, qN δ h0 hmono (m + 1) b = q := Submodule.mkQ_surjective _ q
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change QZ (ι (c • χ1 + mulHL _ (m1 hβ R (3 + (m + 1))) a +
        mulHL _ (m2 hβ R (3 + (m + 1))) (shH R ϑ b))) =
      QZ (c • χm + mulHL _ M1 (ι a) + mulHL _ M2 (shH R ϑ (ι b)))
    exact congrArg _ (valCLM_injective rfl)
  · change (1 / 2 : ℝ) • trH (hm3 (m + 1)) (R / 2) a +
        (1 / 2 : ℝ) • trH (hm3 (m + 1)) (-(R / 2)) b =
      (1 / 2 : ℝ) • trH (hm3 m) (R / 2) (ι a) +
        (1 / 2 : ℝ) • trH (hm3 m) (-(R / 2)) (ι b)
    rw [trH_eq_of_val (hm3 (m + 1)) (hm3 m) (R / 2) (u' := ι a) rfl,
      trH_eq_of_val (hm3 (m + 1)) (hm3 m) (-(R / 2)) (u' := ι b) rfl]
  · change ι (mulHL _ (m5 hβ R (3 + (m + 1))) a +
        mulHL _ (m1 hβ R (3 + (m + 1))) (shH R ϑ b)) =
      mulHL _ M5 (ι a) + mulHL _ M1 (shH R ϑ (ι b))
    exact valCLM_injective rfl

variable (δ h0 hmono) in
/-- The total glued map `Φ_a`, at a fixed parameter, as an sc-isomorphism `E ≅ G^a`. -/
def gluingScIso : ScIso (scPair δ h0 hmono) (scG δ h0 hmono R) where
  lvl m := ContinuousLinearEquiv.equivOfInverse (Phi δ h0 hmono hβ hR2 ϑ m)
    (Psi δ h0 hmono hβ hR2 ϑ m) (psi_phi hβ hR2 ϑ m) (phi_psi hβ hR2 ϑ m)
  incl_comm m x := phi_incl hβ hR2 ϑ m x

end Inverse

/-- **Theorem 2.49(1)** (Memoir p. 50), for a fixed parameter: for every gluing parameter
`0 < |a| < 1/2`, with `R = φ(|a|)` and `a = |a| e^{-2πiϑ}`, the total glued map
`Φ_a = (⊕_a, ⊖_a) : E → G^a` (in the coordinates `h^± = c + r^±`, level `m` given by `Phi m`) is an
sc-linear isomorphism.  (For `a = 0` the memoir sets `Φ₀ = (id, 0)`, `G⁰ = E ⊕ {0}`.) -/
theorem memoir_theorem_2_49_one (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
    (hβ : IsCutoff β) {a : ℂ} (ha0 : a ≠ 0) (ha : ‖a‖ < 1 / 2) :
    ∃ T : ScIso (scPair δ h0 hmono) (scG δ h0 hmono (glLength a)),
      ∀ m x, T m x = Phi δ h0 hmono hβ (two_le_glLength ha0 ha) (glTwist a) m x :=
  ⟨gluingScIso δ h0 hmono hβ (two_le_glLength ha0 ha) (glTwist a), fun _ _ => rfl⟩


/-! ## 2. The splicing projection `π_a` and Theorem 2.49(2) -/

section Splicing

variable (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
variable (hβ : IsCutoff β) (hR2 : 2 ≤ R) (ϑ : ℝ) (m : ℕ)

/-- `v ↦ (v, 0, 0)`: the elements of `G^a_m` with vanishing anti-gluing part. -/
def gIn : (scFin δ h0 hmono R) m →L[ℝ] (scG δ h0 hmono R) m :=
  (ContinuousLinearMap.id ℝ _).prod 0

/-- The projection `π_a = Φ_a⁻¹ ∘ (⊕_a, 0) ∘ Φ_a` on `E_m` (Memoir p. 50): onto `ker ⊖_a` along
`ker ⊕_a`. -/
def piLvl : (scPair δ h0 hmono) m →L[ℝ] (scPair δ h0 hmono) m :=
  (Psi δ h0 hmono hβ hR2 ϑ m).comp
    ((gIn δ h0 hmono (R := R) m).comp ((qrV δ h0 hmono m).comp (Phi δ h0 hmono hβ hR2 ϑ m)))

lemma phi_piLvl (x : (scPair δ h0 hmono) m) :
    Phi δ h0 hmono hβ hR2 ϑ m (piLvl δ h0 hmono hβ hR2 ϑ m x) =
      ((Phi δ h0 hmono hβ hR2 ϑ m x).1, 0) := by
  change Phi δ h0 hmono hβ hR2 ϑ m (Psi δ h0 hmono hβ hR2 ϑ m _) = _
  rw [phi_psi]; rfl

/-- `⊕_a ∘ π_a = ⊕_a`. -/
lemma glue_piLvl (x : (scPair δ h0 hmono) m) :
    (Phi δ h0 hmono hβ hR2 ϑ m (piLvl δ h0 hmono hβ hR2 ϑ m x)).1 =
      (Phi δ h0 hmono hβ hR2 ϑ m x).1 := by
  rw [phi_piLvl]

/-- `⊖_a ∘ π_a = 0`. -/
lemma antiGlue_piLvl (x : (scPair δ h0 hmono) m) :
    (Phi δ h0 hmono hβ hR2 ϑ m (piLvl δ h0 hmono hβ hR2 ϑ m x)).2 = 0 := by
  rw [phi_piLvl]

/-- `π_a ∘ π_a = π_a`. -/
lemma piLvl_idem (x : (scPair δ h0 hmono) m) :
    piLvl δ h0 hmono hβ hR2 ϑ m (piLvl δ h0 hmono hβ hR2 ϑ m x) =
      piLvl δ h0 hmono hβ hR2 ϑ m x := by
  change Psi δ h0 hmono hβ hR2 ϑ m (gIn δ h0 hmono (R := R) m
      (Phi δ h0 hmono hβ hR2 ϑ m (piLvl δ h0 hmono hβ hR2 ϑ m x)).1) = _
  rw [glue_piLvl]; rfl

/-- `π_a h = h` exactly when `⊖_a h = 0`. -/
lemma piLvl_eq_self_iff (x : (scPair δ h0 hmono) m) :
    piLvl δ h0 hmono hβ hR2 ϑ m x = x ↔ (Phi δ h0 hmono hβ hR2 ϑ m x).2 = 0 := by
  constructor
  · intro h; rw [← h]; exact antiGlue_piLvl δ h0 hmono hβ hR2 ϑ m x
  · intro h
    apply (gluingScIso δ h0 hmono hβ hR2 ϑ m).injective
    change Phi δ h0 hmono hβ hR2 ϑ m _ = Phi δ h0 hmono hβ hR2 ϑ m x
    rw [phi_piLvl]
    exact Prod.ext rfl h.symm

/-- The splicing on `B_{1/2} ⊕ E₀`: `π_a` for `0 < |a| < 1/2` (`R = φ(|a|)`, `ϑ` the twist of
`a`), and `π_a = id` otherwise (`π₀ = id`, Memoir p. 50). -/
def piSc (p : ℂ × (scPair δ h0 hmono) 0) : (scPair δ h0 hmono) 0 :=
  if h : p.1 ≠ 0 ∧ ‖p.1‖ < 1 / 2 then
    piLvl δ h0 hmono hβ (two_le_glLength h.1 h.2) (glTwist p.1) 0 p.2
  else p.2

lemma piSc_zero (x : (scPair δ h0 hmono) 0) : piSc δ h0 hmono hβ (0, x) = x := by
  simp [piSc]

/-- **Theorem 2.49(2)** (Memoir p. 50), as a statement: the map `(a, (h⁺, h⁻)) ↦ π_a(h⁺, h⁻)` is
sc-smooth on `B_{1/2} ⊕ E`, where `E = ℝ ⊕ H^{3+m,δ_m}(ℝ⁺ × S¹) ⊕ H^{3+m,δ_m}(ℝ⁻ × S¹)` is the
space of pairs with a common asymptotic constant; with `piLvl_idem` this makes `(π, E, B_{1/2})`
an sc-smooth splicing.  Here the gluing profile is the exponential one, `φ(r) = e^{1/r} - e`. -/
def MemoirTheorem249Two : Prop :=
  IsScSmooth (E := (ScBanach.const ℂ).prod (scPair δ h0 hmono)) (F := scPair δ h0 hmono)
    {p | ‖p.1‖ < 1 / 2} (piSc δ h0 hmono hβ)

end Splicing

end GWMemoir.Neck
