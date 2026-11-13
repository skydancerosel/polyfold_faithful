import Polyfold.Chapter3.GoodComplementIntersection

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §3.8.1.4:
**Lemma 3.8.9** (preprint 3.66), p. 150, with the good complement `(N ∩ W) ⊕ N^⊥` as an
sc-complement.

# `(N ∩ W) ⊕ N^⊥` is a good sc-complement of `Ñ`

`Polyfold.lemma_3_8_9` gives the good complement `(N ∩ W) ⊕ N^⊥` of `Ñ` in the project's sense
(the algebraic splitting `E₀ = Ñ ⊕ ((N ∩ W) ⊕ N^⊥)`).  The text's Definition 3.1.24 asks for an
sc-complement.  This file supplies it:

* `Polyfold.ScBanach.isScSubspace_sup_of_le_smooth`: `A ⊕ G` is an sc-subspace when `G` is one and
  `A ⊆ E_∞` is finite-dimensional (closedness from Mathlib, density by translating by a lift of
  the `A`-part);
* `Polyfold.ScBanach.isCompl_levelSub_of_isScSplitting`: if `E = N ⊕ P` is an sc-splitting with
  `N ⊆ E_∞` and `N = Ñ ⊕ A`, then `E_m = Ñ_m ⊕ (A ⊕ P)_m` on every level;
* `Polyfold.lemma_3_8_9_sc`: **Lemma 3.8.9** with the text's notions on both sides:
  `Ñ` is in good position (`IsInGoodPositionSc`) with good sc-complement `(N ∩ W) ⊕ N^⊥`
  (`IsScGoodComplement`).
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

namespace ScBanach

variable (E : ScBanach)

/-- The sum of an sc-subspace `G` and a finite-dimensional subspace `A ⊆ E_∞` is an
sc-subspace. -/
theorem isScSubspace_sup_of_le_smooth {A G : Submodule ℝ (E 0)} [FiniteDimensional ℝ A]
    (hA : A ≤ E.smooth) (hG : E.IsScSubspace G) : E.IsScSubspace (A ⊔ G) := by
  refine ⟨?_, fun m x hx => ?_⟩
  · rw [sup_comm]; exact Submodule.isClosed_sup_finiteDimensional G A hG.1
  obtain ⟨a, ha, g, hg, hag⟩ := Submodule.mem_sup.1 (E.mem_levelSub.1 hx)
  obtain ⟨am, ham⟩ := (ScScale.mem_smooth_iff E.toScScale).1 (hA ha) m
  have hxg : x - am ∈ E.levelSub G m := by
    rw [mem_levelSub, map_sub, ham, ← hag, add_sub_cancel_left]; exact hg
  have hcl := hG.2 m hxg
  have hcont : Continuous fun y : E m => am + y := continuous_const.add continuous_id
  have hmaps : (fun y : E m => am + y) '' (E.levelSub G m ∩ E.smoothLvl m) ⊆
      E.levelSub (A ⊔ G) m ∩ E.smoothLvl m := by
    rintro _ ⟨y, ⟨hyG, hys⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · change E.toBase m (am + y) ∈ A ⊔ G
      rw [map_add, ham]
      exact Submodule.add_mem_sup ha hyG
    · change E.toBase m (am + y) ∈ E.smooth
      rw [map_add, ham]
      exact E.smooth.add_mem (hA ha) hys
  have := image_closure_subset_closure_image hcont ⟨_, hcl, rfl⟩
  have hx' : (fun y : E m => am + y) (x - am) = x := add_sub_cancel am x
  rw [hx'] at this
  exact closure_mono hmaps this

variable {E}

/-- Level by level, `N = Ñ ⊕ A` and `E = N ⊕ P` give `E_m = Ñ_m ⊕ (A ⊕ P)_m` when `N ⊆ E_∞`. -/
theorem isCompl_levelSub_of_isScSplitting {N P Ñ A : Submodule ℝ (E 0)}
    (hNP : E.IsScSplitting N P) (hN : N ≤ E.smooth) (hÑ : Ñ ≤ N) (hA : A ≤ N)
    (hdisj : Disjoint Ñ A) (hsup : Ñ ⊔ A = N) (m : ℕ) :
    IsCompl (E.levelSub Ñ m) (E.levelSub (A ⊔ P) m) := by
  have hNP0 : IsCompl N P := by have := hNP.2.2 0; rwa [levelSub_zero, levelSub_zero] at this
  -- the base-level complement
  have hc : IsCompl Ñ (A ⊔ P) := by
    refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx'
      have hbN : b ∈ N := by
        have := N.sub_mem (hÑ hx) (hA ha)
        rwa [add_sub_cancel_left] at this
      have hb0 : b = 0 := (Submodule.disjoint_def.1 hNP0.disjoint) b hbN hb
      subst hb0
      rw [add_zero] at hx ⊢
      exact (Submodule.disjoint_def.1 hdisj) a hx ha
    · rw [codisjoint_iff, ← sup_assoc, hsup, hNP0.sup_eq_top]
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    apply E.toBase_injective m
    rw [map_zero]
    exact (Submodule.disjoint_def.1 hc.disjoint) _ hx hx'
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1
      ((hNP.2.2 m).sup_eq_top ▸ Submodule.mem_top : x ∈ E.levelSub N m ⊔ E.levelSub P m)
    have huN : E.toBase m u ∈ Ñ ⊔ A := by rw [hsup]; exact hu
    obtain ⟨ñ, hñ, a, ha, hña⟩ := Submodule.mem_sup.1 huN
    obtain ⟨ñm, hñm⟩ := (ScScale.mem_smooth_iff E.toScScale).1 (hN (hÑ hñ)) m
    have hñm' : ñm ∈ E.levelSub Ñ m := by rw [mem_levelSub, hñm]; exact hñ
    have hrest : x - ñm ∈ E.levelSub (A ⊔ P) m := by
      rw [mem_levelSub, ← huv, map_sub, map_add, hñm, ← hña]
      have : ñ + a + E.toBase m v - ñ = a + E.toBase m v := by abel
      rw [this]
      exact Submodule.add_mem_sup ha hv
    have := Submodule.add_mem_sup hñm' hrest
    rwa [add_sub_cancel] at this

end ScBanach

/-- **Lemma 3.8.9 (preprint 3.66)**, 2021 p. 150, with the text's notions on both sides: if `N`
is in good position to `C = [0, ∞)ⁿ ⊕ W` with good sc-complement `N^⊥` and `Ñ` is an algebraic
complement of `N ∩ W` in `N`, then `Ñ` is in good position to `C` (`IsInGoodPositionSc`) with good
sc-complement `(N ∩ W) ⊕ N^⊥`. -/
theorem lemma_3_8_9_sc {n : ℕ} {W : ScBanach}
    {N P Ñ : Submodule ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0)}
    [FiniteDimensional ℝ N] (hN : IsInGoodPositionSc _ (quadrant n W 0) N)
    (hP : IsScGoodComplement _ (quadrant n W 0) N P)
    (hÑ : Ñ ≤ N) (hdisj : Disjoint Ñ (N ⊓ wPart n W)) (hsup : Ñ ⊔ (N ⊓ wPart n W) = N) :
    IsInGoodPositionSc _ (quadrant n W 0) Ñ ∧
      IsScGoodComplement _ (quadrant n W 0) Ñ ((N ⊓ wPart n W) ⊔ P) := by
  have hNs := hP.le_smooth
  have : FiniteDimensional ℝ Ñ := Submodule.finiteDimensional_of_le hÑ
  have : FiniteDimensional ℝ (N ⊓ wPart n W : Submodule ℝ _) :=
    Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨hgp, hgc⟩ := lemma_3_8_9 hN hP hÑ hdisj hsup
  have hsplit : ScBanach.IsScSplitting _ Ñ ((N ⊓ wPart n W) ⊔ P) :=
    ⟨(ScBanach.proposition_1_1_7_iff _ Ñ).2 (hÑ.trans hNs),
      ScBanach.isScSubspace_sup_of_le_smooth _ (inf_le_left.trans hNs) hP.isScSplitting.2.1,
      ScBanach.isCompl_levelSub_of_isScSplitting hP.isScSplitting hNs hÑ inf_le_left hdisj hsup⟩
  have hsc : IsScGoodComplement _ (quadrant n W 0) Ñ ((N ⊓ wPart n W) ⊔ P) :=
    ⟨hsplit, hgc.exists_eps⟩
  exact ⟨⟨hgp.interior_nonempty, ⟨_, hsc⟩⟩, hsc⟩

end Polyfold
