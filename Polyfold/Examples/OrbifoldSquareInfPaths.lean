import Polyfold.Examples.OrbifoldSquareInfBundle
import Polyfold.Chapter12.OrientationGeneralizedIsoOriented

/-!
# The orbifold `(ℂ × H)/ℤ₅`: sc-smooth paths in `ℂ × H`

For the worked example of Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021),
Theorem 16.6.6, 2021 p. 739, with Definition 6.6.14 and Theorem 6.6.17 (the path category).

## What is formalized

* `isScSmoothMap_rn_base_iff`: a map `ℝᵐ → E` into the one-chart M-polyfold of an sc-Banach space
  `E` is sc-smooth iff it is sc-smooth as a map of sc-Banach spaces.
* `mem_smoothSet_Ainf_iff`: `(z, e) ∈ ℂ × H` is a smooth point iff `e ∈ H_∞`.
* `isScSmoothMap_rn_Ainf`: `q ↦ (a(q), e(q))` is sc-smooth into `ℂ × H` for `a` of class `C^∞`
  and `e` sc-smooth; `isScSmoothMap_curve_const`: the path `t ↦ (z(t), e)`, `e ∈ H_∞`.
* **`scHomotopic_inf`**, **`PathCat.hom_eq_inf`**: two sc-smooth paths of `ℂ × H` with the same
  end points are sc-smoothly homotopic with end points fixed (the straight-line homotopy), so the
  path category of `ℂ × H` has at most one morphism between two points.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology CategoryTheory

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.OrbifoldSquareInf

open TrivialBundle WeightedEllTwo OrbifoldSquare

/-! ### Maps `ℝᵐ → E` into the one-chart M-polyfold of `E` -/

section OneChart

variable {E : ScBanach} (hU : IsRelOpenInQuadrant E (univ : Set (E 0)) univ)
  (u₀ : ↥(univ : Set (E 0))) {m : ℕ}

theorem rnChart_image_univ : rnChart m 0 '' univ = univ :=
  eq_univ_of_forall fun (r : Fin m → ℝ) => ⟨r, mem_univ _, show r - 0 = r from sub_zero r⟩

/-- **A map `ℝᵐ → E` into the one-chart M-polyfold of `E` is sc-smooth iff it is sc-smooth as a
map of sc-Banach spaces.** -/
theorem isScSmoothMap_rn_base_iff {g : (Fin m → ℝ) → ↥(univ : Set (E 0))} :
    (rnPolyfold m).IsScSmoothMap (LocalBundle.basePolyfold hU u₀) g ↔
      IsScSmooth (E := rnSc m) (F := E) univ fun r => (g r : E 0) := by
  have hUm : IsRelOpenInQuadrant (rnSc m) univ univ := rn_relOpen_univ m
  constructor
  · intro hg
    have h := hg.smooth (rnChart m 0) (retractChart hU.isScRetract u₀) (isChart_rnChart 0)
      (isChart_retractChart hU.isScRetract u₀) univ isOpen_univ
      (fun _ _ => ⟨mem_univ _, mem_univ _⟩) (mapsTo_univ _ _)
    rw [rnChart_image_univ] at h
    have h' : IsScSmoothRetractMap (rnSc m) univ univ E univ univ
        (fun r => (g (r + 0) : E 0)) := h
    obtain ⟨-, R, hR, hs⟩ := (isScSmoothRetractMap_iff_exists hUm.isScRetract).1 h'
    have hsub : R.retract ⊆ R.U := R.retract_subset
    rw [hR] at hsub
    have hRU : R.U = univ := eq_univ_of_univ_subset hsub
    rw [hRU] at hs
    refine hs.congr (isScDomain_univ _) fun r _ => ?_
    have hr : R r = r := R.apply_eq_self_of_mem_retract (by rw [hR]; exact mem_univ r)
    change (g (R r + 0) : E 0) = g r
    rw [hr, add_zero]
  · intro hs
    refine MPolyfold.isScSmoothMap_of_local fun x => ⟨rnChart m 0,
      retractChart hU.isScRetract u₀, univ, isChart_rnChart 0,
      isChart_retractChart hU.isScRetract u₀, isOpen_univ, mem_univ x, subset_univ _,
      mapsTo_univ _ _, ?_⟩
    rw [rnChart_image_univ]
    change IsScSmoothRetractMap (rnSc m) univ univ E univ univ (fun r => (g (r + 0) : E 0))
    refine (isScSmoothRetractMap_iff_exists hUm.isScRetract).2
      ⟨mapsTo_univ _ _, ScRetraction.id hUm, image_id _, ?_⟩
    refine hs.congr (isScDomain_univ _) fun r _ => ?_
    change (g r : E 0) = g (r + 0)
    rw [add_zero]

end OneChart

/-! ### Smooth points and sc-smooth maps into `ℂ × H` -/

/-- **`(z, e)` is a smooth point of `ℂ × H` iff `e ∈ H_∞`.** -/
theorem mem_smoothSet_Ainf_iff {x : (Fin 2 → ℝ) × HObj} :
    x ∈ Ainf.X.PObj.smoothSet ↔ ((x.2 : HObj) : H 0) ∈ H.smooth := by
  have h : x ∈ ((rnPolyfold 2).prod PH).smoothSet ↔
      x.1 ∈ (rnPolyfold 2).smoothSet ∧ x.2 ∈ PH.smoothSet := MPolyfold.mem_smoothSet_prod
  have h1 : x.1 ∈ (rnPolyfold 2).smoothSet := by rw [rnPolyfold_smoothSet]; exact mem_univ _
  exact h.trans ((and_iff_right h1).trans (LocalBundle.mem_smoothSet_iff relOpen_H h0))

/-- A `C^∞` map `ℝᵐ → ℝⁿ` is sc-smooth for the constant sc-structures. -/
theorem isScSmooth_rn_of_contDiff {m : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {a : (Fin m → ℝ) → V} (ha : ContDiff ℝ ∞ a) :
    IsScSmooth (E := rnSc m) (F := ScBanach.const V) univ a :=
  (isScSmooth_iff_contDiffOn_const (V := Fin m → ℝ) (W := V) (isScDomain_univ _) _).2
    ha.contDiffOn

/-- **`q ↦ (a(q), e(q))` is sc-smooth into `ℂ × H`**, for `a : ℝᵐ → ℂ` of class `C^∞` and
`e : ℝᵐ → H` sc-smooth. -/
theorem isScSmoothMap_rn_Ainf {m : ℕ} {a : (Fin m → ℝ) → Fin 2 → ℝ} (ha : ContDiff ℝ ∞ a)
    {e : (Fin m → ℝ) → H 0} (he : IsScSmooth (E := rnSc m) (F := H) univ e) :
    (rnPolyfold m).IsScSmoothMap Ainf.X.PObj fun q => ((a q, hpt (e q)) : (Fin 2 → ℝ) × HObj) := by
  have h1 : (rnPolyfold m).IsScSmoothMap (rnPolyfold 2) a := isScSmoothMap_rn_rn_of_contDiff ha
  have h2 : (rnPolyfold m).IsScSmoothMap PH fun q => hpt (e q) :=
    (isScSmoothMap_rn_base_iff relOpen_H h0).2 he
  exact MPolyfold.IsScSmoothOn.prodMk h1 h2

/-- **The path `t ↦ (z(t), e)` is sc-smooth**, for a `C^∞` curve `z` in `ℂ` and `e ∈ H_∞`. -/
theorem isScSmoothMap_curve_const {z : (Fin 1 → ℝ) → Fin 2 → ℝ} (hz : ContDiff ℝ ∞ z)
    {e : H 0} (he : e ∈ H.smooth) :
    (rnPolyfold 1).IsScSmoothMap Ainf.X.PObj fun t => ((z t, hpt e) : (Fin 2 → ℝ) × HObj) :=
  isScSmoothMap_rn_Ainf hz (isScSmooth_const_of_mem_smooth (isScDomain_univ _) he)

/-- The two components of an sc-smooth map `ℝᵐ → ℂ × H`. -/
theorem contDiff_fst_and_isScSmooth_snd {m : ℕ} {γ : (Fin m → ℝ) → (Fin 2 → ℝ) × HObj}
    (hγ : (rnPolyfold m).IsScSmoothMap Ainf.X.PObj γ) :
    ContDiff ℝ ∞ (fun q => (γ q).1) ∧
      IsScSmooth (E := rnSc m) (F := H) univ fun q => (((γ q).2 : HObj) : H 0) := by
  have hγ' : (rnPolyfold m).IsScSmoothMap ((rnPolyfold 2).prod PH) γ := hγ
  exact ⟨contDiff_of_isScSmoothMap_rn_rn ((MPolyfold.isScSmoothMap_fst _ _).comp hγ'),
    (isScSmoothMap_rn_base_iff relOpen_H h0).1 ((MPolyfold.isScSmoothMap_snd _ _).comp hγ')⟩

/-! ### The straight-line homotopy -/

/-- **Two sc-smooth paths in `ℂ × H` with the same end points are sc-smoothly homotopic with end
points fixed**, by the straight-line homotopy `(τ, t) ↦ (1 − τ) γ₀(t) + τ γ₁(t)`. -/
theorem scHomotopic_inf {γ₀ γ₁ : (Fin 1 → ℝ) → (Fin 2 → ℝ) × HObj}
    (h₀ : (rnPolyfold 1).IsScSmoothMap Ainf.X.PObj γ₀)
    (h₁ : (rnPolyfold 1).IsScSmoothMap Ainf.X.PObj γ₁) (hs : γ₀ (pt1 0) = γ₁ (pt1 0))
    (ht : γ₀ (pt1 1) = γ₁ (pt1 1)) : ScHomotopic Ainf.X.PObj γ₀ γ₁ := by
  obtain ⟨c₀, s₀⟩ := contDiff_fst_and_isScSmooth_snd h₀
  obtain ⟨c₁, s₁⟩ := contDiff_fst_and_isScSmooth_snd h₁
  have hp : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => pt1 (q 1) :=
    contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ (1 : Fin 2)
  have hq : ContDiff ℝ ∞ fun q : Fin 2 → ℝ => q 0 := contDiff_apply ℝ ℝ (0 : Fin 2)
  have hd : IsScDomain (rnSc 2) univ := isScDomain_univ _
  have hp' : IsScSmooth (E := rnSc 2) (F := rnSc 1) univ fun q : Fin 2 → ℝ => pt1 (q 1) :=
    isScSmooth_rn_of_contDiff hp
  have hq' : IsScSmooth (E := rnSc 2) (F := ScBanach.const ℝ) univ fun q : Fin 2 → ℝ => q 0 :=
    isScSmooth_rn_of_contDiff hq
  have hq'' : IsScSmooth (E := rnSc 2) (F := ScBanach.const ℝ) univ
      fun q : Fin 2 → ℝ => 1 - q 0 := isScSmooth_rn_of_contDiff (contDiff_const.sub hq)
  have t₀ : IsScSmooth (E := rnSc 2) (F := H) univ
      fun q : Fin 2 → ℝ => (((γ₀ (pt1 (q 1))).2 : HObj) : H 0) :=
    IsScSmooth.comp hd (isScDomain_univ _) s₀ hp' (mapsTo_univ _ _)
  have t₁ : IsScSmooth (E := rnSc 2) (F := H) univ
      fun q : Fin 2 → ℝ => (((γ₁ (pt1 (q 1))).2 : HObj) : H 0) :=
    IsScSmooth.comp hd (isScDomain_univ _) s₁ hp' (mapsTo_univ _ _)
  have hc : ContDiff ℝ ∞ fun q : Fin 2 → ℝ =>
      (1 - q 0) • (γ₀ (pt1 (q 1))).1 + q 0 • (γ₁ (pt1 (q 1))).1 :=
    ((contDiff_const.sub hq).smul (c₀.comp hp)).add (hq.smul (c₁.comp hp))
  have hsm := isScSmoothMap_rn_Ainf hc
    (e := fun q : Fin 2 → ℝ => (1 - q 0) • (((γ₀ (pt1 (q 1))).2 : HObj) : H 0) +
      q 0 • (((γ₁ (pt1 (q 1))).2 : HObj) : H 0))
    (IsScSmooth.add hd (IsScSmooth.smul hd hq'' t₀) (IsScSmooth.smul hd hq' t₁))
  refine ⟨_, hsm, ?_, ?_, ?_, ?_⟩
  · intro t _
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp only [pt2_apply_zero, pt2_apply_one, sub_zero, one_smul, zero_smul, add_zero]
    · simp only [hpt_val, pt2_apply_zero, pt2_apply_one, sub_zero, one_smul, zero_smul,
        add_zero]
  · intro t _
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp only [pt2_apply_zero, pt2_apply_one, sub_self, one_smul, zero_smul, zero_add]
    · simp only [hpt_val, pt2_apply_zero, pt2_apply_one, sub_self, one_smul, zero_smul,
        zero_add]
  · intro τ _
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp only [pt2_apply_zero, pt2_apply_one]
      rw [← hs, ← add_smul, sub_add_cancel, one_smul]
    · simp only [hpt_val, pt2_apply_zero, pt2_apply_one]
      rw [← hs, ← add_smul, sub_add_cancel, one_smul]
  · intro τ _
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp only [pt2_apply_zero, pt2_apply_one]
      rw [← ht, ← add_smul, sub_add_cancel, one_smul]
    · simp only [hpt_val, pt2_apply_zero, pt2_apply_one]
      rw [← ht, ← add_smul, sub_add_cancel, one_smul]

/-- **The path category of `ℂ × H` has at most one morphism between two points.** -/
theorem PathCat.hom_eq_inf {x y : PathCat Ainf.X.PObj} (a b : x ⟶ y) : a = b := by
  obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
  obtain ⟨ψ, rfl⟩ := PathCat.exists_eq_mk b
  exact PathCat.mk_eq_mk_iff.2 (scHomotopic_inf φ.isScSmoothMap ψ.isScSmoothMap
    (φ.source.trans ψ.source.symm) (φ.target.trans ψ.target.symm))

end Polyfold.Examples.OrbifoldSquareInf
