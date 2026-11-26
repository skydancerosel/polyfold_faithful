import GWMemoir.GluingIso

/-!
# Scales with an offset, and Theorem 2.50 (hat gluing) on the Sobolev levels

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §2.4, pp. 49–52.

* `scaleGWOff ℓ δ`: the scale `E_m = H^{ℓ+m,δ_m}(ℝ × S¹)` (`δ₀ ≥ 0`, `δ` strictly increasing).
  For `ℓ = 3` it is `scaleGW` of `GWMemoir.Skeleton` (`scaleGWOff_three`); the bundle fibres use
  `ℓ = 2` (Memoir p. 51).  `scCylOff ℓ δ` adds the density of the smooth points.
* `scRestrOff ℓ δ I`: the restriction of `H^{ℓ+m,δ_m}(ℝ × S¹)` to `I × S¹`, the quotient by the maps
  vanishing on `I × S¹`, as in `GWMemoir.HalfCylinders` (offset `3`); `scHalfPosOff`,
  `scHalfNegOff`,
  `scFinOff`.
* `scFHat ℓ δ = H^{ℓ+m,δ_m}(ℝ⁺ × S¹) ⊕ H^{ℓ+m,δ_m}(ℝ⁻ × S¹)` and
  `scGHat ℓ δ R = H^{ℓ+m}(Z_a) ⊕ H^{ℓ+m,δ_m}(C_a)`: for `ℓ = 2` the spaces `F` and `Ĝ^a` of p. 51.
  No asymptotic constants: the common constant of a pair in `F` is `0`.
* `PhiHat ℓ … m`: the total hat gluing `Φ̂_a = (⊕̂_a, ⊖̂_a)` on level `m`,
  `⊕̂_a(ξ) = β_a ξ⁺ + (1 - β_a) τ ξ⁻` on `Z_a`, `⊖̂_a(ξ) = -(1 - β_a) ξ⁺ + β_a τ ξ⁻` on `C_a`,
  with `τ ξ(s,t) = ξ(s - R, t - ϑ)`; its inverse `PsiHat` is the Sobolev form of (2.12).
* **`memoir_theorem_2_50_one`**: Theorem 2.50(1) for a fixed `0 < |a| < 1/2`, an sc-isomorphism
  `F ≅ Ĝ^a`.  The memoir prints the domain as `E`; we read it as `F`, the space of pairs defined
  just before the theorem, on which `⊕̂_a` and `⊖̂_a` are defined.
* **`MemoirTheorem250Two`**: Theorem 2.50(2), the sc-smoothness of `(a, ξ) ↦ π̂_a ξ` on
  `B_{1/2} ⊕ F`, as a named proposition (`π̂_0 = id`).
-/

open Set Filter Topology MeasureTheory
open Polyfold Polyfold.CylinderSobolev

set_option linter.unusedSectionVars false

noncomputable section

namespace GWMemoir.Neck

/-! ## 1. The scale `H^{ℓ+m,δ_m}(ℝ × S¹)` -/

section Offset

variable (ℓ : ℕ) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- The scale `E_m = H^{ℓ+m,δ_m}(ℝ × S¹)` (Memoir pp. 49, 51), for an offset `ℓ`. -/
def scaleGWOff : ScScale where
  lvl m := H (ℓ + m) (δ_nonneg δ h0 hmono m)
  incl m := inclH _ _ (Nat.le_succ (ℓ + m)) (hmono (Nat.lt_succ_self m)).le
  incl_injective _ := inclH_injective _ _ _ _
  incl_isCompactOperator m := isCompactOperator_inclH _ _ (hmono (Nat.lt_succ_self m))

/-- For `ℓ = 3` this is the scale `scaleGW` of the skeleton. -/
theorem scaleGWOff_three : scaleGWOff 3 δ h0 hmono = scaleGW δ h0 hmono := rfl

lemma val_toBaseOff : ∀ (m : ℕ) (u : (scaleGWOff ℓ δ h0 hmono) m),
    H.val ((scaleGWOff ℓ δ h0 hmono).toBase m u) = H.val u
  | 0, _ => rfl
  | m + 1, u => by
    rw [ScScale.toBase_succ, val_toBaseOff m]; rfl

lemma toBase_toH_off {φ : ℝ × ℝ → ℝ} (hφ : IsTest φ) (m : ℕ) :
    (scaleGWOff ℓ δ h0 hmono).toBase m (toH (ℓ + m) (δ_nonneg δ h0 hmono m) hφ) =
      toH ℓ (δ_nonneg δ h0 hmono 0) hφ :=
  valCLM_injective (val_toBaseOff ℓ δ h0 hmono m _)

/-- `E_m = H^{ℓ+m,δ_m}(ℝ × S¹)` as an sc-Banach space: the test functions are smooth points and
are dense in every level. -/
def scCylOff : ScBanach where
  toScScale := scaleGWOff ℓ δ h0 hmono
  dense_smooth m := by
    refine (dense_test (ℓ + m) (δ_nonneg δ h0 hmono m)).mono ?_
    rintro _ ⟨φ, hφ, rfl⟩
    refine (scaleGWOff ℓ δ h0 hmono).mem_smoothLvl_iff.2 fun j =>
      ⟨toH (ℓ + j) (δ_nonneg δ h0 hmono j) hφ, ?_⟩
    rw [toBase_toH_off, toBase_toH_off]

lemma scCylOff_lvl (m : ℕ) :
    (scCylOff ℓ δ h0 hmono) m = H (ℓ + m) (δ_nonneg δ h0 hmono m) := rfl

theorem scCylOff_three : scCylOff 3 δ h0 hmono = scCyl δ h0 hmono := rfl

/-- The maps of `E₀ = H^{ℓ,δ₀}(ℝ × S¹)` vanishing on `I × S¹`. -/
def vanishHOff (I : Set ℝ) (hI : MeasurableSet I) : Submodule ℝ ((scCylOff ℓ δ h0 hmono) 0) :=
  (vanishLp I hI).comap (valCLM ℓ (δ_nonneg δ h0 hmono 0) : H ℓ _ →ₗ[ℝ] Lp ℝ 2 cyl)

lemma isClosed_vanishHOff (I : Set ℝ) (hI : MeasurableSet I) :
    IsClosed (vanishHOff ℓ δ h0 hmono I hI : Set ((scCylOff ℓ δ h0 hmono) 0)) :=
  (isClosed_vanishLp I hI).preimage (valCLM ℓ _).continuous

/-- `H^{ℓ+m,δ_m}(ℝ × S¹)` restricted to `I × S¹` (Proposition 1.1.8 of the book, 2021 p. 9). -/
def scRestrOff (I : Set ℝ) (hI : MeasurableSet I) : ScBanach :=
  (scCylOff ℓ δ h0 hmono).quotient (isClosed_vanishHOff ℓ δ h0 hmono I hI)

/-- `H^{ℓ+m,δ_m}(ℝ⁺ × S¹)`. -/
def scHalfPosOff : ScBanach := scRestrOff ℓ δ h0 hmono (Ioi 0) measurableSet_Ioi

/-- `H^{ℓ+m,δ_m}(ℝ⁻ × S¹)`. -/
def scHalfNegOff : ScBanach := scRestrOff ℓ δ h0 hmono (Iio 0) measurableSet_Iio

/-- `H^{ℓ+m}(Z_a)`, `Z_a = [0,R] × S¹`. -/
def scFinOff (R : ℝ) : ScBanach := scRestrOff ℓ δ h0 hmono (Ioo 0 R) measurableSet_Ioo

theorem scHalfPosOff_three : scHalfPosOff 3 δ h0 hmono = scHalfPos δ h0 hmono := rfl

/-- The space `F` of Memoir p. 51 (for `ℓ = 2`): pairs `ξ^± ∈ H^{ℓ+m,δ_m}(ℝ^± × S¹)`, with common
asymptotic constant `0`; real-valued (the `ℝ²ⁿ`-valued space is its `2n`-fold product). -/
def scFHat : ScBanach := (scHalfPosOff ℓ δ h0 hmono).prod (scHalfNegOff ℓ δ h0 hmono)

/-- The space `Ĝ^a = H^{ℓ}(Z_a) ⊕ H^{ℓ,δ₀}(C_a)` of Memoir p. 51 (for `ℓ = 2`), `a ≠ 0`, with
levels `H^{ℓ+m}(Z_a) ⊕ H^{ℓ+m,δ_m}(C_a)`; `C_a` in its coordinates `[s,t]` is `ℝ × S¹`. -/
def scGHat (R : ℝ) : ScBanach := (scFinOff ℓ δ h0 hmono R).prod (scCylOff ℓ δ h0 hmono)

/-- The level-`m` vanishing subspaces. -/
abbrev LPo (m : ℕ) :=
  (scCylOff ℓ δ h0 hmono).levelSub (vanishHOff ℓ δ h0 hmono (Ioi 0) measurableSet_Ioi) m
abbrev LNo (m : ℕ) :=
  (scCylOff ℓ δ h0 hmono).levelSub (vanishHOff ℓ δ h0 hmono (Iio 0) measurableSet_Iio) m
abbrev LZo (R : ℝ) (m : ℕ) :=
  (scCylOff ℓ δ h0 hmono).levelSub (vanishHOff ℓ δ h0 hmono (Ioo 0 R) measurableSet_Ioo) m

variable {ℓ δ h0 hmono}

lemma memLo {I : Set ℝ} {hI : MeasurableSet I} {m : ℕ} {u : (scCylOff ℓ δ h0 hmono) m} :
    u ∈ (scCylOff ℓ δ h0 hmono).levelSub (vanishHOff ℓ δ h0 hmono I hI) m ↔
      Van I (valCLM (ℓ + m) (δ_nonneg δ h0 hmono m) u) := by
  rw [ScBanach.mem_levelSub]
  have := val_toBaseOff ℓ δ h0 hmono m u
  exact (Iff.of_eq (congrArg (· ∈ vanishLp I hI) this)).trans mem_vanishLp

end Offset

/-! ## 2. Pointwise identities of the hat gluing -/

section Ident

variable {β : ℝ → ℝ} {R ϑ : ℝ} (hβ : IsCutoff β) {k : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}
include hβ

/-- `Ψ̂ ∘ Φ̂ = id` on representatives, the `ξ⁺` component. -/
lemma hatIdentA (a b : H k hδ) :
    mulHL _ (m3 hβ R k) (mulHL _ (m1 hβ R k) a + mulHL _ (m2 hβ R k) (shH R ϑ b)) -
      mulHL _ (m4 hβ R k) (mulHL _ (m5 hβ R k) a + mulHL _ (m1 hβ R k) (shH R ϑ b)) = a := by
  simp only [map_add]
  have h1 := comb_sub (m3 hβ R k) (m1 hβ R k) (m4 hβ R k) (m5 hβ R k)
    (fun s => e31_45 (βa β R s)) a
  have h2 := comb_sub (m3 hβ R k) (m2 hβ R k) (m4 hβ R k) (m1 hβ R k)
    (fun s => e32_41 (βa β R s)) (shH R ϑ b)
  linear_combination (norm := module) h1 + h2

/-- `Ψ̂ ∘ Φ̂ = id` on representatives, the `ξ⁻` component before `τ⁻¹`. -/
lemma hatIdentB (a b : H k hδ) :
    mulHL _ (m4 hβ R k) (mulHL _ (m1 hβ R k) a + mulHL _ (m2 hβ R k) (shH R ϑ b)) +
      mulHL _ (m3 hβ R k) (mulHL _ (m5 hβ R k) a + mulHL _ (m1 hβ R k) (shH R ϑ b)) =
      shH R ϑ b := by
  simp only [map_add]
  have h1 := comb_add (m4 hβ R k) (m1 hβ R k) (m3 hβ R k) (m5 hβ R k)
    (fun s => e41_35 (βa β R s)) a
  have h2 := comb_add (m4 hβ R k) (m2 hβ R k) (m3 hβ R k) (m1 hβ R k)
    (fun s => e42_31 (βa β R s)) (shH R ϑ b)
  linear_combination (norm := module) h1 + h2

/-- `Φ̂ ∘ Ψ̂ = id` on representatives, the `Z_a` component. -/
lemma hatIdentC (v w : H k hδ) :
    mulHL _ (m1 hβ R k) (mulHL _ (m3 hβ R k) v - mulHL _ (m4 hβ R k) w) +
      mulHL _ (m2 hβ R k) (mulHL _ (m4 hβ R k) v + mulHL _ (m3 hβ R k) w) = v := by
  simp only [map_add, map_sub]
  have h1 := comb_add (m1 hβ R k) (m3 hβ R k) (m2 hβ R k) (m4 hβ R k)
    (fun s => e13_24 (βa β R s)) v
  have h3 := comb_sub (m2 hβ R k) (m3 hβ R k) (m1 hβ R k) (m4 hβ R k)
    (fun s => e23_14 (βa β R s)) w
  linear_combination (norm := module) h1 + h3

/-- `Φ̂ ∘ Ψ̂ = id` on representatives, the `C_a` component. -/
lemma hatIdentD (v w : H k hδ) :
    mulHL _ (m5 hβ R k) (mulHL _ (m3 hβ R k) v - mulHL _ (m4 hβ R k) w) +
      mulHL _ (m1 hβ R k) (mulHL _ (m4 hβ R k) v + mulHL _ (m3 hβ R k) w) = w := by
  simp only [map_add, map_sub]
  have h1 := comb_add (m5 hβ R k) (m3 hβ R k) (m1 hβ R k) (m4 hβ R k)
    (fun s => e53_14 (βa β R s)) v
  have h3 := comb_sub (m1 hβ R k) (m3 hβ R k) (m5 hβ R k) (m4 hβ R k)
    (fun s => e13_54 (βa β R s)) w
  linear_combination (norm := module) h1 + h3

end Ident

/-! ## 3. The total hat gluing on the levels -/

section Levels

variable (ℓ : ℕ) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
variable {β : ℝ → ℝ} {R : ℝ} (hβ : IsCutoff β) (hR2 : 2 ≤ R) (ϑ : ℝ) (m : ℕ)

local notation "Hk" => H (ℓ + m) (δ_nonneg δ h0 hmono m)

/-- `ξ⁺ ↦ [β_a ξ⁺]_{Z_a}`. -/
def APh : (scHalfPosOff ℓ δ h0 hmono) m →L[ℝ] (scFinOff ℓ δ h0 hmono R) m :=
  (LPo ℓ δ h0 hmono m).liftQL ((LZo ℓ δ h0 hmono R m).mkQL.comp (mulHL _ (m1 hβ R (ℓ + m))))
    fun _ hu => (Submodule.Quotient.mk_eq_zero _).2 (memLo.2 (van_mulHL (memLo.1 hu) _
      fun _ hs hs' => absurd hs.1 hs'))

/-- `ξ⁻ ↦ [(1 - β_a) τ ξ⁻]_{Z_a}`. -/
def ANh : (scHalfNegOff ℓ δ h0 hmono) m →L[ℝ] (scFinOff ℓ δ h0 hmono R) m :=
  (LNo ℓ δ h0 hmono m).liftQL ((LZo ℓ δ h0 hmono R m).mkQL.comp
      ((mulHL _ (m2 hβ R (ℓ + m))).comp (shH R ϑ))) fun _ hu =>
    (Submodule.Quotient.mk_eq_zero _).2 (memLo.2 (van_mulHL (I := Iio R)
      (van_shH (memLo.1 hu) R ϑ fun s hs => by simp only [mem_Iio] at hs ⊢; linarith) _
      fun _ hs hs' => absurd hs.2 hs'))

/-- `ξ⁺ ↦ -(1 - β_a) ξ⁺` on `C_a`. -/
def BPh : (scHalfPosOff ℓ δ h0 hmono) m →L[ℝ] (scCylOff ℓ δ h0 hmono) m :=
  (LPo ℓ δ h0 hmono m).liftQL (mulHL _ (m5 hβ R (ℓ + m))) fun _ hu =>
    eq_zero_of_van_univ (van_mulHL (memLo.1 hu) _ fun s _ hs => by
      simp only [mem_Ioi, not_lt] at hs
      rw [βa_one hβ (by linarith), sub_self])

/-- `ξ⁻ ↦ β_a τ ξ⁻` on `C_a`. -/
def BNh : (scHalfNegOff ℓ δ h0 hmono) m →L[ℝ] (scCylOff ℓ δ h0 hmono) m :=
  (LNo ℓ δ h0 hmono m).liftQL ((mulHL _ (m1 hβ R (ℓ + m))).comp (shH R ϑ)) fun _ hu =>
    eq_zero_of_van_univ (van_mulHL (I := Iio R)
      (van_shH (memLo.1 hu) R ϑ fun s hs => by simp only [mem_Iio] at hs ⊢; linarith) _
      fun s _ hs => by
        simp only [mem_Iio, not_lt] at hs
        exact βa_zero hβ (by linarith))

/-- `v ↦ [(β_a/γ_a) v]_{ℝ⁺}`. -/
def PPh : (scFinOff ℓ δ h0 hmono R) m →L[ℝ] (scHalfPosOff ℓ δ h0 hmono) m :=
  (LZo ℓ δ h0 hmono R m).liftQL ((LPo ℓ δ h0 hmono m).mkQL.comp (mulHL _ (m3 hβ R (ℓ + m))))
    fun _ hu => (Submodule.Quotient.mk_eq_zero _).2 (memLo.2 (van_mulHL (memLo.1 hu) _
      fun s hs hs' => by
        simp only [mem_Ioi] at hs
        simp only [mem_Ioo, not_and_or, not_lt] at hs'
        rcases hs' with h | h
        · exact absurd hs (not_lt.2 h)
        · rw [βa_zero hβ (by linarith), F3_zero]))

/-- `v ↦ [τ⁻¹((1 - β_a)/γ_a) v]_{ℝ⁻}`. -/
def PNh : (scFinOff ℓ δ h0 hmono R) m →L[ℝ] (scHalfNegOff ℓ δ h0 hmono) m :=
  (LZo ℓ δ h0 hmono R m).liftQL ((LNo ℓ δ h0 hmono m).mkQL.comp
      ((shH (-R) (-ϑ)).comp (mulHL _ (m4 hβ R (ℓ + m))))) fun _ hu =>
    (Submodule.Quotient.mk_eq_zero _).2 (memLo.2 (van_shH (I := Iio R)
      (van_mulHL (memLo.1 hu) _ fun s hs hs' => by
        simp only [mem_Iio] at hs
        simp only [mem_Ioo, not_and_or, not_lt] at hs'
        rcases hs' with h | h
        · rw [βa_one hβ (by linarith), F4_one]
        · exact absurd hs (not_lt.2 h)) (-R) (-ϑ)
      fun s hs => by simp only [mem_Iio] at hs ⊢; linarith))

/-- `w ↦ [((1 - β_a)/γ_a) w]_{ℝ⁺}`. -/
def WPh : (scCylOff ℓ δ h0 hmono) m →L[ℝ] (scHalfPosOff ℓ δ h0 hmono) m :=
  (LPo ℓ δ h0 hmono m).mkQL.comp (mulHL _ (m4 hβ R (ℓ + m)))

/-- `w ↦ [τ⁻¹(β_a/γ_a) w]_{ℝ⁻}`. -/
def WNh : (scCylOff ℓ δ h0 hmono) m →L[ℝ] (scHalfNegOff ℓ δ h0 hmono) m :=
  (LNo ℓ δ h0 hmono m).mkQL.comp ((shH (-R) (-ϑ)).comp (mulHL _ (m3 hβ R (ℓ + m))))

/-- Level `m` of the total hat gluing `Φ̂_a = (⊕̂_a, ⊖̂_a)` (Memoir p. 51):
`(ξ⁺, ξ⁻) ↦ (β_a ξ⁺ + (1 - β_a) τ ξ⁻, -(1 - β_a) ξ⁺ + β_a τ ξ⁻)`. -/
def PhiHat : (scFHat ℓ δ h0 hmono) m →L[ℝ] (scGHat ℓ δ h0 hmono R) m :=
  ((APh ℓ δ h0 hmono hβ m).comp (ContinuousLinearMap.fst ℝ _ _) +
      (ANh ℓ δ h0 hmono hβ ϑ m).comp (ContinuousLinearMap.snd ℝ _ _)).prod
    ((BPh ℓ δ h0 hmono hβ hR2 m).comp (ContinuousLinearMap.fst ℝ _ _) +
      (BNh ℓ δ h0 hmono hβ hR2 ϑ m).comp (ContinuousLinearMap.snd ℝ _ _))

lemma phiHat_apply (p : (scHalfPosOff ℓ δ h0 hmono) m) (q : (scHalfNegOff ℓ δ h0 hmono) m) :
    PhiHat ℓ δ h0 hmono hβ hR2 ϑ m (p, q) =
      (APh ℓ δ h0 hmono hβ m p + ANh ℓ δ h0 hmono hβ ϑ m q,
        BPh ℓ δ h0 hmono hβ hR2 m p + BNh ℓ δ h0 hmono hβ hR2 ϑ m q) := rfl

/-- Level `m` of the inverse, the Sobolev form of (2.12):
`ξ⁺ = (β_a/γ_a) v - ((1 - β_a)/γ_a) w`, `ξ⁻ = τ⁻¹(((1 - β_a)/γ_a) v + (β_a/γ_a) w)`. -/
def PsiHat : (scGHat ℓ δ h0 hmono R) m →L[ℝ] (scFHat ℓ δ h0 hmono) m :=
  ((PPh ℓ δ h0 hmono hβ hR2 m).comp (ContinuousLinearMap.fst ℝ _ _) -
      (WPh ℓ δ h0 hmono hβ (R := R) m).comp (ContinuousLinearMap.snd ℝ _ _)).prod
    ((PNh ℓ δ h0 hmono hβ hR2 ϑ m).comp (ContinuousLinearMap.fst ℝ _ _) +
      (WNh ℓ δ h0 hmono hβ (R := R) ϑ m).comp (ContinuousLinearMap.snd ℝ _ _))

/-- The quotient maps, typed on `H^{ℓ+m,δ_m}(ℝ × S¹)`. -/
def qPo : Hk →L[ℝ] (scHalfPosOff ℓ δ h0 hmono) m := (LPo ℓ δ h0 hmono m).mkQL
def qNo : Hk →L[ℝ] (scHalfNegOff ℓ δ h0 hmono) m := (LNo ℓ δ h0 hmono m).mkQL
def qZo : Hk →L[ℝ] (scFinOff ℓ δ h0 hmono R) m := (LZo ℓ δ h0 hmono R m).mkQL

local notation "QP" => qPo ℓ δ h0 hmono m
local notation "QN" => qNo ℓ δ h0 hmono m
local notation "QZ" => qZo ℓ δ h0 hmono (R := R) m

theorem psiHat_phiHat (x : (scFHat ℓ δ h0 hmono) m) :
    PsiHat ℓ δ h0 hmono hβ hR2 ϑ m (PhiHat ℓ δ h0 hmono hβ hR2 ϑ m x) = x := by
  obtain ⟨p, q⟩ := x
  obtain ⟨a, rfl⟩ : ∃ a, QP a = p := Submodule.mkQ_surjective _ p
  obtain ⟨b, rfl⟩ : ∃ b, QN b = q := Submodule.mkQ_surjective _ q
  refine Prod.ext ?_ ?_
  · change QP (mulHL _ (m3 hβ R (ℓ + m)) (mulHL _ (m1 hβ R (ℓ + m)) a +
        mulHL _ (m2 hβ R (ℓ + m)) (shH R ϑ b))) -
      QP (mulHL _ (m4 hβ R (ℓ + m)) (mulHL _ (m5 hβ R (ℓ + m)) a +
        mulHL _ (m1 hβ R (ℓ + m)) (shH R ϑ b))) = QP a
    rw [← map_sub, hatIdentA hβ]
  · change QN (shH (-R) (-ϑ) (mulHL _ (m4 hβ R (ℓ + m)) (mulHL _ (m1 hβ R (ℓ + m)) a +
        mulHL _ (m2 hβ R (ℓ + m)) (shH R ϑ b)))) +
      QN (shH (-R) (-ϑ) (mulHL _ (m3 hβ R (ℓ + m)) (mulHL _ (m5 hβ R (ℓ + m)) a +
        mulHL _ (m1 hβ R (ℓ + m)) (shH R ϑ b)))) = QN b
    rw [← map_add, ← map_add, hatIdentB hβ, shH_shH]

theorem phiHat_psiHat (y : (scGHat ℓ δ h0 hmono R) m) :
    PhiHat ℓ δ h0 hmono hβ hR2 ϑ m (PsiHat ℓ δ h0 hmono hβ hR2 ϑ m y) = y := by
  obtain ⟨v, w⟩ := y
  obtain ⟨v, rfl⟩ : ∃ v', QZ v' = v := Submodule.mkQ_surjective _ v
  obtain ⟨w, rfl⟩ : ∃ w' : Hk, w' = w := ⟨w, rfl⟩
  refine Prod.ext ?_ ?_
  · change QZ (mulHL _ (m1 hβ R (ℓ + m)) (mulHL _ (m3 hβ R (ℓ + m)) v -
        mulHL _ (m4 hβ R (ℓ + m)) w) +
      mulHL _ (m2 hβ R (ℓ + m)) (shH R ϑ (shH (-R) (-ϑ) (mulHL _ (m4 hβ R (ℓ + m)) v +
        mulHL _ (m3 hβ R (ℓ + m)) w)))) = QZ v
    rw [shH_shH', hatIdentC hβ]
  · change mulHL _ (m5 hβ R (ℓ + m)) (mulHL _ (m3 hβ R (ℓ + m)) v -
        mulHL _ (m4 hβ R (ℓ + m)) w) +
      mulHL _ (m1 hβ R (ℓ + m)) (shH R ϑ (shH (-R) (-ϑ) (mulHL _ (m4 hβ R (ℓ + m)) v +
        mulHL _ (m3 hβ R (ℓ + m)) w))) = w
    rw [shH_shH', hatIdentD hβ]

local notation "ι" => inclH (δ_nonneg δ h0 hmono m) (δ_nonneg δ h0 hmono (m + 1))
  (Nat.le_succ (ℓ + m)) (hmono.monotone (Nat.le_succ m))

theorem phiHat_incl (x : (scFHat ℓ δ h0 hmono) (m + 1)) :
    (scGHat ℓ δ h0 hmono R).incl m (PhiHat ℓ δ h0 hmono hβ hR2 ϑ (m + 1) x) =
      PhiHat ℓ δ h0 hmono hβ hR2 ϑ m ((scFHat ℓ δ h0 hmono).incl m x) := by
  obtain ⟨p, q⟩ := x
  obtain ⟨a, rfl⟩ : ∃ a, qPo ℓ δ h0 hmono (m + 1) a = p := Submodule.mkQ_surjective _ p
  obtain ⟨b, rfl⟩ : ∃ b, qNo ℓ δ h0 hmono (m + 1) b = q := Submodule.mkQ_surjective _ q
  refine Prod.ext ?_ ?_
  · change QZ (ι (mulHL _ (m1 hβ R (ℓ + (m + 1))) a +
        mulHL _ (m2 hβ R (ℓ + (m + 1))) (shH R ϑ b))) =
      QZ (mulHL _ (m1 hβ R (ℓ + m)) (ι a) + mulHL _ (m2 hβ R (ℓ + m)) (shH R ϑ (ι b)))
    exact congrArg _ (valCLM_injective rfl)
  · change ι (mulHL _ (m5 hβ R (ℓ + (m + 1))) a +
        mulHL _ (m1 hβ R (ℓ + (m + 1))) (shH R ϑ b)) =
      mulHL _ (m5 hβ R (ℓ + m)) (ι a) + mulHL _ (m1 hβ R (ℓ + m)) (shH R ϑ (ι b))
    exact valCLM_injective rfl

variable {m} in
/-- The total hat gluing `Φ̂_a`, at a fixed parameter, as an sc-isomorphism `F ≅ Ĝ^a`. -/
def hatGluingScIso : ScIso (scFHat ℓ δ h0 hmono) (scGHat ℓ δ h0 hmono R) where
  lvl m := ContinuousLinearEquiv.equivOfInverse (PhiHat ℓ δ h0 hmono hβ hR2 ϑ m)
    (PsiHat ℓ δ h0 hmono hβ hR2 ϑ m) (psiHat_phiHat ℓ δ h0 hmono hβ hR2 ϑ m)
    (phiHat_psiHat ℓ δ h0 hmono hβ hR2 ϑ m)
  incl_comm m x := phiHat_incl ℓ δ h0 hmono hβ hR2 ϑ m x

end Levels

/-- **Theorem 2.50(1)** (Memoir p. 52), for a fixed parameter: for every gluing parameter
`0 < |a| < 1/2`, with `R = φ(|a|)` and `a = |a| e^{-2πiϑ}`, the total hat gluing
`Φ̂_a = (⊕̂_a, ⊖̂_a) : F → Ĝ^a` (level `m` given by `PhiHat 2 … m`) is an sc-linear isomorphism,
`F_m = H^{2+m,δ_m}(ℝ⁺ × S¹) ⊕ H^{2+m,δ_m}(ℝ⁻ × S¹)`, `Ĝ^a_m = H^{2+m}(Z_a) ⊕ H^{2+m,δ_m}(C_a)`.
The memoir prints the domain as `E`; we read it as `F`.  (For `a = 0`, `Ĝ⁰ = F ⊕ {0}`.) -/
theorem memoir_theorem_2_50_one (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
    {β : ℝ → ℝ} (hβ : IsCutoff β) {a : ℂ} (ha0 : a ≠ 0) (ha : ‖a‖ < 1 / 2) :
    ∃ T : ScIso (scFHat 2 δ h0 hmono) (scGHat 2 δ h0 hmono (glLength a)),
      ∀ m x, T m x = PhiHat 2 δ h0 hmono hβ (two_le_glLength ha0 ha) (glTwist a) m x :=
  ⟨hatGluingScIso 2 δ h0 hmono hβ (two_le_glLength ha0 ha) (glTwist a), fun _ _ => rfl⟩

/-- The same for every offset `ℓ` (the levels `H^{ℓ+m,δ_m}`); `ℓ = 2` is Theorem 2.50(1). -/
theorem hat_gluing_scIso_off (ℓ : ℕ) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
    {β : ℝ → ℝ} (hβ : IsCutoff β) {a : ℂ} (ha0 : a ≠ 0) (ha : ‖a‖ < 1 / 2) :
    ∃ T : ScIso (scFHat ℓ δ h0 hmono) (scGHat ℓ δ h0 hmono (glLength a)),
      ∀ m x, T m x = PhiHat ℓ δ h0 hmono hβ (two_le_glLength ha0 ha) (glTwist a) m x :=
  ⟨hatGluingScIso ℓ δ h0 hmono hβ (two_le_glLength ha0 ha) (glTwist a), fun _ _ => rfl⟩

/-! ## 4. The projection `π̂_a` and Theorem 2.50(2) -/

section Splicing

variable (ℓ : ℕ) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
variable {β : ℝ → ℝ} {R : ℝ} (hβ : IsCutoff β) (hR2 : 2 ≤ R) (ϑ : ℝ) (m : ℕ)

/-- `v ↦ (v, 0)`: the elements of `Ĝ^a_m` with vanishing hat anti-gluing part. -/
def gInHat : (scFinOff ℓ δ h0 hmono R) m →L[ℝ] (scGHat ℓ δ h0 hmono R) m :=
  (ContinuousLinearMap.id ℝ _).prod 0

/-- The projection `π̂_a = Φ̂_a⁻¹ ∘ (⊕̂_a, 0) ∘ Φ̂_a` on `F_m`, onto `ker ⊖̂_a` along `ker ⊕̂_a`
(Memoir p. 51, formula (2.12)). -/
def piHatLvl : (scFHat ℓ δ h0 hmono) m →L[ℝ] (scFHat ℓ δ h0 hmono) m :=
  (PsiHat ℓ δ h0 hmono hβ hR2 ϑ m).comp ((gInHat ℓ δ h0 hmono (R := R) m).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp (PhiHat ℓ δ h0 hmono hβ hR2 ϑ m)))

lemma phiHat_piHatLvl (x : (scFHat ℓ δ h0 hmono) m) :
    PhiHat ℓ δ h0 hmono hβ hR2 ϑ m (piHatLvl ℓ δ h0 hmono hβ hR2 ϑ m x) =
      ((PhiHat ℓ δ h0 hmono hβ hR2 ϑ m x).1, 0) := by
  change PhiHat ℓ δ h0 hmono hβ hR2 ϑ m (PsiHat ℓ δ h0 hmono hβ hR2 ϑ m _) = _
  rw [phiHat_psiHat]; rfl

/-- `π̂_a ∘ π̂_a = π̂_a`. -/
lemma piHatLvl_idem (x : (scFHat ℓ δ h0 hmono) m) :
    piHatLvl ℓ δ h0 hmono hβ hR2 ϑ m (piHatLvl ℓ δ h0 hmono hβ hR2 ϑ m x) =
      piHatLvl ℓ δ h0 hmono hβ hR2 ϑ m x := by
  change PsiHat ℓ δ h0 hmono hβ hR2 ϑ m (gInHat ℓ δ h0 hmono (R := R) m
      (PhiHat ℓ δ h0 hmono hβ hR2 ϑ m (piHatLvl ℓ δ h0 hmono hβ hR2 ϑ m x)).1) = _
  rw [phiHat_piHatLvl]; rfl

/-- `π̂_a ξ = ξ` exactly when `⊖̂_a ξ = 0`. -/
lemma piHatLvl_eq_self_iff (x : (scFHat ℓ δ h0 hmono) m) :
    piHatLvl ℓ δ h0 hmono hβ hR2 ϑ m x = x ↔ (PhiHat ℓ δ h0 hmono hβ hR2 ϑ m x).2 = 0 := by
  constructor
  · intro h; rw [← h, phiHat_piHatLvl]
  · intro h
    apply (hatGluingScIso ℓ δ h0 hmono hβ hR2 ϑ m).injective
    change PhiHat ℓ δ h0 hmono hβ hR2 ϑ m _ = PhiHat ℓ δ h0 hmono hβ hR2 ϑ m x
    rw [phiHat_piHatLvl]
    exact Prod.ext rfl h.symm

/-- The family `π̂` on `B_{1/2} ⊕ F₀`: `π̂_a` for `0 < |a| < 1/2` (`R = φ(|a|)`, `ϑ` the twist of
`a`), and `π̂_a = id` otherwise (`π̂₀ = id`, Memoir p. 51). -/
def piHatSc (p : ℂ × (scFHat ℓ δ h0 hmono) 0) : (scFHat ℓ δ h0 hmono) 0 :=
  if h : p.1 ≠ 0 ∧ ‖p.1‖ < 1 / 2 then
    piHatLvl ℓ δ h0 hmono hβ (two_le_glLength h.1 h.2) (glTwist p.1) 0 p.2
  else p.2

lemma piHatSc_zero (x : (scFHat ℓ δ h0 hmono) 0) : piHatSc ℓ δ h0 hmono hβ (0, x) = x := by
  simp [piHatSc]

lemma piHatSc_idem (p : ℂ × (scFHat ℓ δ h0 hmono) 0) :
    piHatSc ℓ δ h0 hmono hβ (p.1, piHatSc ℓ δ h0 hmono hβ p) = piHatSc ℓ δ h0 hmono hβ p := by
  unfold piHatSc
  split_ifs with h
  · exact piHatLvl_idem ℓ δ h0 hmono hβ _ _ 0 _
  · rfl

/-- **Theorem 2.50(2)** (Memoir p. 52), as a named proposition: the map
`π̂ : B_{1/2} ⊕ F → F`, `(a, (ξ⁺, ξ⁻)) ↦ π̂_a(ξ⁺, ξ⁻)`, is sc-smooth, where
`F_m = H^{2+m,δ_m}(ℝ⁺ × S¹) ⊕ H^{2+m,δ_m}(ℝ⁻ × S¹)`; with `piHatSc_idem` this makes
`(π̂, F, B_{1/2})` an sc-smooth splicing.  The gluing profile is the exponential one. -/
def MemoirTheorem250Two : Prop :=
  IsScSmooth (E := (ScBanach.const ℂ).prod (scFHat 2 δ h0 hmono)) (F := scFHat 2 δ h0 hmono)
    {p | ‖p.1‖ < 1 / 2} (piHatSc 2 δ h0 hmono hβ)

end Splicing

end GWMemoir.Neck
