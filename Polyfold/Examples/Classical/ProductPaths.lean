import Polyfold.Examples.Classical.ProductSetup

/-!
# The classical reduction crossed with the weighted `ℓ²` factor: sc-smooth paths in `ℝⁿ × H`

For Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Theorem 16.6.6,
2021 p. 739, with Definition 6.6.14 and Theorem 6.6.17 (the path category).  The statements are
those of `OrbifoldSquareInfPaths.lean` with `ℂ = ℝ²` replaced by `ℝⁿ`.

## What is formalized (namespace `Polyfold.Examples.Classical.Product`)

* `isScSmoothMap_rn_AP`: `q ↦ (a(q), e(q))` is sc-smooth into `ℝⁿ × H` for `a` of class `C^∞` and
  `e` sc-smooth; `isScSmoothMap_curve_AP`: the path `t ↦ (a(t), e(t))`.
* `contDiff_fst_and_isScSmooth_snd_AP`: the two components of an sc-smooth map `ℝᵐ → ℝⁿ × H`.
* **`scHomotopic_AP`**, **`PathCat.hom_eq_AP`**: two sc-smooth paths of `ℝⁿ × H` with the same end
  points are sc-smoothly homotopic relative to the end points (the straight-line homotopy), so the path
  category of `ℝⁿ × H` has at most one morphism between two points.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology CategoryTheory

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical.Product

open TrivialBundle WeightedEllTwo Polyfold.Examples.OrbifoldSquareInf

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]
  (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))

/-- **`q ↦ (a(q), e(q))` is sc-smooth into `ℝⁿ × H`**, for `a : ℝᵐ → ℝⁿ` of class `C^∞` and
`e : ℝᵐ → H` sc-smooth. -/
theorem isScSmoothMap_rn_AP {m : ℕ} {a : (Fin m → ℝ) → Fin n → ℝ} (ha : ContDiff ℝ ∞ a)
    {e : (Fin m → ℝ) → H 0} (he : IsScSmooth (E := rnSc m) (F := H) univ e) :
    (rnPolyfold m).IsScSmoothMap (AP σ).X.PObj
      fun q => ((a q, hpt (e q)) : (Fin n → ℝ) × HObj) := by
  have h1 : (rnPolyfold m).IsScSmoothMap (rnPolyfold n) a := isScSmoothMap_rn_rn_of_contDiff ha
  have h2 : (rnPolyfold m).IsScSmoothMap PH fun q => hpt (e q) :=
    (isScSmoothMap_rn_base_iff relOpen_H h0).2 he
  exact MPolyfold.IsScSmoothOn.prodMk h1 h2

/-- The two components of an sc-smooth map `ℝᵐ → ℝⁿ × H`. -/
theorem contDiff_fst_and_isScSmooth_snd_AP {m : ℕ} {γ : (Fin m → ℝ) → (Fin n → ℝ) × HObj}
    (hγ : (rnPolyfold m).IsScSmoothMap (AP σ).X.PObj γ) :
    ContDiff ℝ ∞ (fun q => (γ q).1) ∧
      IsScSmooth (E := rnSc m) (F := H) univ fun q => (((γ q).2 : HObj) : H 0) := by
  have hγ' : (rnPolyfold m).IsScSmoothMap ((rnPolyfold n).prod PH) γ := hγ
  exact ⟨contDiff_of_isScSmoothMap_rn_rn ((MPolyfold.isScSmoothMap_fst _ _).comp hγ'),
    (isScSmoothMap_rn_base_iff relOpen_H h0).1 ((MPolyfold.isScSmoothMap_snd _ _).comp hγ')⟩

/-- **Two sc-smooth paths in `ℝⁿ × H` with the same end points are sc-smoothly homotopic with end
points held**, by the straight-line homotopy `(τ, t) ↦ (1 − τ) γ₀(t) + τ γ₁(t)`. -/
theorem scHomotopic_AP {γ₀ γ₁ : (Fin 1 → ℝ) → (Fin n → ℝ) × HObj}
    (h₀ : (rnPolyfold 1).IsScSmoothMap (AP σ).X.PObj γ₀)
    (h₁ : (rnPolyfold 1).IsScSmoothMap (AP σ).X.PObj γ₁) (hs : γ₀ (pt1 0) = γ₁ (pt1 0))
    (ht : γ₀ (pt1 1) = γ₁ (pt1 1)) : ScHomotopic (AP σ).X.PObj γ₀ γ₁ := by
  obtain ⟨c₀, s₀⟩ := contDiff_fst_and_isScSmooth_snd_AP σ h₀
  obtain ⟨c₁, s₁⟩ := contDiff_fst_and_isScSmooth_snd_AP σ h₁
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
  have hsm := isScSmoothMap_rn_AP σ hc
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

/-- **The path category of `ℝⁿ × H` has at most one morphism between two points.** -/
theorem PathCat.hom_eq_AP {x y : PathCat (AP σ).X.PObj} (a b : x ⟶ y) : a = b := by
  obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
  obtain ⟨ψ, rfl⟩ := PathCat.exists_eq_mk b
  exact PathCat.mk_eq_mk_iff.2 (scHomotopic_AP σ φ.isScSmoothMap ψ.isScSmoothMap
    (φ.source.trans ψ.source.symm) (φ.target.trans ψ.target.symm))

end Polyfold.Examples.Classical.Product
