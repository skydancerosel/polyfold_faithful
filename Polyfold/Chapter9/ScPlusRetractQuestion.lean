import Polyfold.Chapter9.BoundaryPositionConverse

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.2,
**Question 4.2.4** (p. 187; preprint: the question after Proposition 4.15, p. 159).

# The "T" of Question 4.2.4 is not an sc⁺-retract

## The text

Question 4.2.4 asks whether a sub-M-polyfold `A` with `A = A_∞` and `dim T_aA` finite and
locally constant is a smooth finite-dimensional submanifold, and considers the set
`T = {(x, 0) ∈ ℝ² | −1 < x < 1} ∪ {(0, y) ∈ ℝ² | y ∈ [0, 1)}`: "Is it possible to find an
sc-smooth retract `(O, E, E)` … so that `T` is homeomorphic to `O` and `O = O_∞`?  From our
previous discussion this is impossible if we require `O` to be an sc⁺-retract."

## What is formalized

The settled part, the last sentence:
* `Question424.not_homeomorph_open`: no relatively open neighbourhood of `(0, 0)` in `T` is
  homeomorphic to an open subset of a finite-dimensional real normed space (`T` is not a
  topological manifold at the branch point).  By the dimension `k` of the space: `k = 0` (a point
  is not a neighbourhood in `T`), `k = 1` (two of the three arms of `T` would go to the same side of
  the image of `(0, 0)` in `ℝ`, and their images overlap), `k ≥ 2` (a punctured ball is connected,
  but a punctured neighbourhood of `(0, 0)` in `T` is not).
* `Question424.question_4_2_4_scPlus`: if `(O, E, E)` is an sc⁺-retract (`C = E`), then `O` is not
  homeomorphic to `T`.  Near every point an sc⁺-retract without boundary is the graph of a map on
  its finite-dimensional tangent space (`ScRetraction.IsScPlus.exists_flat`, the argument of 2021
  Lemma 9.2.13, with `C = E` so that `T_zO ⊆ E_z = E`).  `O = O_∞` holds automatically
  (Lemma 4.1.7).

The question itself (the first part, and the sc-retract case without the sc⁺ hypothesis) is open in
the text and is not addressed.
-/

open Set Filter Topology Metric Module

noncomputable section

namespace Polyfold

namespace Question424

/-- **The "T" of Question 4.2.4**: `{(x, 0) | −1 < x < 1} ∪ {(0, y) | 0 ≤ y < 1}` in `ℝ²`. -/
def tSet : Set (ℝ × ℝ) :=
  {p | -1 < p.1 ∧ p.1 < 1 ∧ p.2 = 0} ∪ {p | p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 < 1}

lemma zero_mem_tSet : ((0 : ℝ), (0 : ℝ)) ∈ tSet := Or.inl ⟨by norm_num, by norm_num, rfl⟩

/-- A continuous injective arc in `ℝ` leaves its starting point to one side. -/
lemma arc_side {f : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (hf : ContinuousOn f (Icc 0 ε))
    (hinj : InjOn f (Icc 0 ε)) :
    (∀ s ∈ Ioc 0 ε, f 0 < f s) ∨ (∀ s ∈ Ioc 0 ε, f s < f 0) := by
  have hpre : IsPreconnected (f '' Ioc 0 ε) :=
    isPreconnected_Ioc.image f (hf.mono Ioc_subset_Icc_self)
  have hne : ∀ s ∈ Ioc 0 ε, f s ≠ f 0 := fun s hs h =>
    (ne_of_gt hs.1) (hinj (Ioc_subset_Icc_self hs) (left_mem_Icc.2 hε.le) h)
  by_contra hc
  simp only [not_or, not_forall, not_lt, exists_prop] at hc
  obtain ⟨⟨s₁, hs₁, h₁⟩, ⟨s₂, hs₂, h₂⟩⟩ := hc
  obtain ⟨s, hs, hfs⟩ := hpre.Icc_subset (mem_image_of_mem f hs₁) (mem_image_of_mem f hs₂) ⟨h₁, h₂⟩
  exact hne s hs hfs

/-- Two continuous arcs in `ℝ` from the same point, both going up, have overlapping images. -/
lemma arc_overlap {f f' : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (hf : ContinuousOn f (Icc 0 ε))
    (hf' : ContinuousOn f' (Icc 0 ε)) (h0 : f' 0 = f 0)
    (hs : ∀ s ∈ Ioc 0 ε, f 0 < f s) (hs' : ∀ s ∈ Ioc 0 ε, f 0 < f' s) :
    ∃ s ∈ Ioc 0 ε, ∃ s' ∈ Ioc 0 ε, f s = f' s' := by
  set c := f 0 with hc
  have hεm : ε ∈ Ioc 0 ε := ⟨hε, le_rfl⟩
  have hb := hs ε hεm
  have hb' := hs' ε hεm
  set t := c + (min (f ε) (f' ε) - c) / 2 with ht
  have hmin := lt_min hb hb'
  have hct : c < t := by rw [ht]; linarith
  have htb : t ≤ f ε := by have := min_le_left (f ε) (f' ε); rw [ht]; linarith
  have htb' : t ≤ f' ε := by have := min_le_right (f ε) (f' ε); rw [ht]; linarith
  have hnear : ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 ε) → g 0 = c → ∃ s ∈ Ioc 0 ε, g s < t := by
    intro g hg hg0
    obtain ⟨η, hη, hηg⟩ := Metric.continuousWithinAt_iff.1 (hg 0 (left_mem_Icc.2 hε.le))
      (t - c) (by linarith)
    have hpos : 0 < min (η / 2) ε := lt_min (by linarith) hε
    refine ⟨min (η / 2) ε, ⟨hpos, min_le_right _ _⟩, ?_⟩
    have hd : dist (min (η / 2) ε) 0 < η := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have h := hηg ⟨hpos.le, min_le_right _ _⟩ hd
    rw [Real.dist_eq, hg0] at h
    have := (abs_lt.1 h).2
    linarith
  obtain ⟨s₀, hs₀, hs₀t⟩ := hnear f hf rfl
  obtain ⟨s₀', hs₀', hs₀t'⟩ := hnear f' hf' h0
  have hpre := isPreconnected_Ioc.image f (hf.mono Ioc_subset_Icc_self)
  have hpre' := isPreconnected_Ioc.image f' (hf'.mono Ioc_subset_Icc_self)
  obtain ⟨s, hs, hfs⟩ := hpre.Icc_subset (mem_image_of_mem f hs₀) (mem_image_of_mem f hεm)
    ⟨hs₀t.le, htb⟩
  obtain ⟨s', hs', hfs'⟩ := hpre'.Icc_subset (mem_image_of_mem f' hs₀')
    (mem_image_of_mem f' hεm) ⟨hs₀t'.le, htb'⟩
  exact ⟨s, hs, s', hs', hfs.trans hfs'.symm⟩

lemma norm_prod_lt {p : ℝ × ℝ} {δ : ℝ} (h1 : |p.1| < δ) (h2 : |p.2| < δ) : ‖p‖ < δ := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_lt h1 h2

variable {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]

/-- **The "T" is not a topological manifold at `(0, 0)`**: no relatively open neighbourhood `S`
of `(0, 0)` in `T` (`T ∩ B(0, δ) ⊆ S ⊆ T`) is homeomorphic (`Φ : S → V`, `Ψ : V → S` continuous
and mutually inverse) to an open subset `V` of a finite-dimensional real normed space. -/
theorem not_homeomorph_open {S : Set (ℝ × ℝ)} (hST : S ⊆ tSet) {δ : ℝ} (hδ : 0 < δ)
    (hS : tSet ∩ ball 0 δ ⊆ S) {V : Set N} (hV : IsOpen V) {Φ : ℝ × ℝ → N} {Ψ : N → ℝ × ℝ}
    (hΦ : ContinuousOn Φ S) (hΨ : ContinuousOn Ψ V) (hΦV : MapsTo Φ S V) (hΨS : MapsTo Ψ V S)
    (hΨΦ : ∀ p ∈ S, Ψ (Φ p) = p) (hΦΨ : ∀ v ∈ V, Φ (Ψ v) = v) : False := by
  have hinj : InjOn Φ S := fun p hp p' hp' h => by rw [← hΨΦ p hp, h, hΨΦ p' hp']
  set ε : ℝ := min δ 1 / 2 with hεdef
  have hε : 0 < ε := by have := lt_min hδ one_pos; rw [hεdef]; linarith
  have hεδ : ε < δ := by have := min_le_left δ 1; rw [hεdef]; linarith
  have hε1 : ε < 1 := by have := min_le_right δ 1; rw [hεdef]; linarith
  have hmemS : ∀ p : ℝ × ℝ, p ∈ tSet → |p.1| ≤ ε → |p.2| ≤ ε → p ∈ S := fun p hp h1 h2 =>
    hS ⟨hp, mem_ball_zero_iff.2 (norm_prod_lt (h1.trans_lt hεδ) (h2.trans_lt hεδ))⟩
  -- the three arms
  have ha1 : ∀ s ∈ Icc 0 ε, ((s, 0) : ℝ × ℝ) ∈ S := fun s hs =>
    hmemS _ (Or.inl ⟨by linarith [hs.1], by linarith [hs.2], rfl⟩)
      (by rw [abs_of_nonneg hs.1]; exact hs.2) (by simp [hε.le])
  have ha2 : ∀ s ∈ Icc 0 ε, ((-s, 0) : ℝ × ℝ) ∈ S := fun s hs =>
    hmemS _ (Or.inl ⟨by linarith [hs.2], by linarith [hs.1], rfl⟩)
      (by rw [abs_neg, abs_of_nonneg hs.1]; exact hs.2) (by simp [hε.le])
  have ha3 : ∀ s ∈ Icc 0 ε, ((0, s) : ℝ × ℝ) ∈ S := fun s hs =>
    hmemS _ (Or.inr ⟨rfl, hs.1, by linarith [hs.2]⟩) (by simp [hε.le])
      (by rw [abs_of_nonneg hs.1]; exact hs.2)
  have h00 : ((0 : ℝ), (0 : ℝ)) ∈ S := ha1 0 (left_mem_Icc.2 hε.le)
  have hc1 : ContinuousOn (fun s : ℝ => Φ (s, 0)) (Icc 0 ε) :=
    hΦ.comp (by fun_prop : Continuous fun s : ℝ => ((s, 0) : ℝ × ℝ)).continuousOn
      fun s hs => ha1 s hs
  have hc2 : ContinuousOn (fun s : ℝ => Φ (-s, 0)) (Icc 0 ε) :=
    hΦ.comp (by fun_prop : Continuous fun s : ℝ => ((-s, 0) : ℝ × ℝ)).continuousOn
      fun s hs => ha2 s hs
  have hc3 : ContinuousOn (fun s : ℝ => Φ (0, s)) (Icc 0 ε) :=
    hΦ.comp (by fun_prop : Continuous fun s : ℝ => ((0, s) : ℝ × ℝ)).continuousOn
      fun s hs => ha3 s hs
  rcases (by omega : finrank ℝ N = 0 ∨ finrank ℝ N = 1 ∨ 2 ≤ finrank ℝ N) with h0 | h1 | h2
  · -- dimension `0`: `V` has at most one point
    have := Module.finrank_zero_iff.1 h0
    have h := hinj (ha1 ε ⟨hε.le, le_rfl⟩) h00 (Subsingleton.elim _ _)
    simp only [Prod.mk.injEq, and_true] at h
    linarith
  · -- dimension `1`: three arms, two sides
    set L : N ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (h1.trans (finrank_self ℝ).symm)
    set f1 : ℝ → ℝ := fun s => L (Φ (s, 0)) with hf1
    set f2 : ℝ → ℝ := fun s => L (Φ (-s, 0)) with hf2
    set f3 : ℝ → ℝ := fun s => L (Φ (0, s)) with hf3
    have hf1c : ContinuousOn f1 (Icc 0 ε) := L.continuous.comp_continuousOn hc1
    have hf2c : ContinuousOn f2 (Icc 0 ε) := L.continuous.comp_continuousOn hc2
    have hf3c : ContinuousOn f3 (Icc 0 ε) := L.continuous.comp_continuousOn hc3
    have h20 : f2 0 = f1 0 := by simp [hf1, hf2]
    have h30 : f3 0 = f1 0 := by simp [hf1, hf3]
    have hi1 : InjOn f1 (Icc 0 ε) := fun s hs s' hs' h => by
      have := hinj (ha1 s hs) (ha1 s' hs') (L.injective h)
      simpa using this
    have hi2 : InjOn f2 (Icc 0 ε) := fun s hs s' hs' h => by
      have := hinj (ha2 s hs) (ha2 s' hs') (L.injective h)
      simpa using this
    have hi3 : InjOn f3 (Icc 0 ε) := fun s hs s' hs' h => by
      have := hinj (ha3 s hs) (ha3 s' hs') (L.injective h)
      simpa using this
    -- distinct arms have disjoint images away from `0`
    have hx12 : ∀ s ∈ Ioc 0 ε, ∀ s' ∈ Ioc 0 ε, f1 s ≠ f2 s' := fun s hs s' hs' h => by
      have := hinj (ha1 s (Ioc_subset_Icc_self hs)) (ha2 s' (Ioc_subset_Icc_self hs'))
        (L.injective h)
      simp only [Prod.mk.injEq, and_true] at this
      linarith [hs.1, hs'.1]
    have hx13 : ∀ s ∈ Ioc 0 ε, ∀ s' ∈ Ioc 0 ε, f1 s ≠ f3 s' := fun s hs s' hs' h => by
      have := hinj (ha1 s (Ioc_subset_Icc_self hs)) (ha3 s' (Ioc_subset_Icc_self hs'))
        (L.injective h)
      simp only [Prod.mk.injEq] at this
      linarith [hs.1, this.1]
    have hx23 : ∀ s ∈ Ioc 0 ε, ∀ s' ∈ Ioc 0 ε, f2 s ≠ f3 s' := fun s hs s' hs' h => by
      have := hinj (ha2 s (Ioc_subset_Icc_self hs)) (ha3 s' (Ioc_subset_Icc_self hs'))
        (L.injective h)
      simp only [Prod.mk.injEq] at this
      linarith [hs.1, this.1]
    -- the pair lemma, going up or going down
    have hpair : ∀ g g' : ℝ → ℝ, ContinuousOn g (Icc 0 ε) → ContinuousOn g' (Icc 0 ε) →
        g' 0 = g 0 → (∀ s ∈ Ioc 0 ε, ∀ s' ∈ Ioc 0 ε, g s ≠ g' s') →
        ((∀ s ∈ Ioc 0 ε, g 0 < g s) ∧ (∀ s ∈ Ioc 0 ε, g' 0 < g' s)) ∨
        ((∀ s ∈ Ioc 0 ε, g s < g 0) ∧ (∀ s ∈ Ioc 0 ε, g' s < g' 0)) → False := by
      intro g g' hg hg' hgg hx hside
      rcases hside with ⟨hu, hu'⟩ | ⟨hd, hd'⟩
      · obtain ⟨s, hs, s', hs', h⟩ :=
          arc_overlap hε hg hg' hgg hu fun s hs => hgg ▸ hu' s hs
        exact hx s hs s' hs' h
      · obtain ⟨s, hs, s', hs', h⟩ := arc_overlap (f := fun s => -g s) (f' := fun s => -g' s) hε
          hg.neg hg'.neg (by simp [hgg]) (fun s hs => neg_lt_neg (hd s hs))
          (fun s hs => by have := hd' s hs; rw [hgg] at this; exact neg_lt_neg this)
        exact hx s hs s' hs' (neg_inj.1 h)
    rcases arc_side hε hf1c hi1 with u1 | d1 <;> rcases arc_side hε hf2c hi2 with u2 | d2 <;>
      rcases arc_side hε hf3c hi3 with u3 | d3
    · exact hpair f1 f2 hf1c hf2c h20 hx12 (Or.inl ⟨u1, u2⟩)
    · exact hpair f1 f2 hf1c hf2c h20 hx12 (Or.inl ⟨u1, u2⟩)
    · exact hpair f1 f3 hf1c hf3c h30 hx13 (Or.inl ⟨u1, u3⟩)
    · exact hpair f2 f3 hf2c hf3c (h30.trans h20.symm) hx23 (Or.inr ⟨d2, d3⟩)
    · exact hpair f2 f3 hf2c hf3c (h30.trans h20.symm) hx23 (Or.inl ⟨u2, u3⟩)
    · exact hpair f1 f3 hf1c hf3c h30 hx13 (Or.inr ⟨d1, d3⟩)
    · exact hpair f1 f2 hf1c hf2c h20 hx12 (Or.inr ⟨d1, d2⟩)
    · exact hpair f1 f2 hf1c hf2c h20 hx12 (Or.inr ⟨d1, d2⟩)
  · -- dimension `≥ 2`: a punctured ball is connected
    have hrank : 1 < Module.rank ℝ N := by
      rw [← Module.finrank_eq_rank]; exact_mod_cast h2
    set q := Φ (0, 0) with hqdef
    have hq : q ∈ V := hΦV h00
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV q hq
    set a := r / 2 with hadef
    have ha : 0 < a := by rw [hadef]; linarith
    set ρ : N → N := fun w => q + (min 1 (a / ‖w - q‖)) • (w - q) with hρdef
    have hρc : ContinuousOn ρ {q}ᶜ := by
      refine continuousOn_const.add (ContinuousOn.smul ?_ (by fun_prop))
      refine continuous_min.comp_continuousOn (continuousOn_const.prodMk
        (continuousOn_const.div (by fun_prop) fun w hw => ?_))
      exact norm_ne_zero_iff.2 (sub_ne_zero.2 hw)
    have hρn : ∀ w, w ≠ q → ‖ρ w - q‖ = min ‖w - q‖ a := by
      intro w hw
      have hd : 0 < ‖w - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hw)
      simp only [hρdef, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      rw [abs_of_nonneg (le_min zero_le_one (div_nonneg ha.le hd.le)), min_mul_of_nonneg _ _ hd.le,
        one_mul, div_mul_cancel₀ _ hd.ne']
    have hρfix : ∀ w, w ≠ q → ‖w - q‖ ≤ a → ρ w = w := by
      intro w hw hwa
      have hd : 0 < ‖w - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hw)
      have : min 1 (a / ‖w - q‖) = 1 := min_eq_left ((one_le_div hd).2 hwa)
      simp only [hρdef, this, one_smul, add_sub_cancel]
    set Sb := ρ '' {q}ᶜ with hSb
    have hSpre : IsPreconnected Sb :=
      (isConnected_compl_singleton_of_one_lt_rank hrank q).isPreconnected.image ρ hρc
    have hSV : Sb ⊆ V := by
      rintro _ ⟨w, hw, rfl⟩
      refine hrV (mem_ball_iff_norm.2 ?_)
      rw [hρn w hw]
      exact lt_of_le_of_lt (min_le_right _ _) (by rw [hadef]; linarith)
    have hSq : q ∉ Sb := by
      rintro ⟨w, hw, h⟩
      have := hρn w hw
      rw [h, sub_self, norm_zero] at this
      have hd : 0 < ‖w - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hw)
      exact absurd this (ne_of_lt (lt_min hd ha))
    set K := Ψ '' Sb with hK
    have hKpre : IsPreconnected K := hSpre.image Ψ (hΨ.mono hSV)
    have hKT : K ⊆ tSet := by
      rintro _ ⟨w, hw, rfl⟩; exact hST (hΨS (hSV hw))
    have hK0 : ((0 : ℝ), (0 : ℝ)) ∉ K := by
      rintro ⟨w, hw, h⟩
      have : w = q := by rw [← hΦΨ w (hSV hw), h]
      exact hSq (this ▸ hw)
    -- points of the two horizontal arms in `K`
    have hcw : ∀ g : ℝ → N, ContinuousOn g (Icc 0 ε) → g 0 = q →
        ∃ η > 0, ∀ s ∈ Icc 0 ε, s < η → ‖g s - q‖ ≤ a := by
      intro g hg hg0
      obtain ⟨η, hη, hηg⟩ := Metric.continuousWithinAt_iff.1 (hg 0 (left_mem_Icc.2 hε.le)) a ha
      refine ⟨η, hη, fun s hs hsη => ?_⟩
      have h := hηg hs (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]; exact hsη)
      rw [dist_eq_norm, hg0] at h
      exact h.le
    obtain ⟨η₁, hη₁, h₁⟩ := hcw _ hc1 rfl
    obtain ⟨η₂, hη₂, h₂⟩ := hcw _ hc2 (by simp [hqdef])
    set s := min (min η₁ η₂ / 2) ε with hsdef
    have hs0 : 0 < s := lt_min (by have := lt_min hη₁ hη₂; linarith) hε
    have hsε : s ∈ Icc 0 ε := ⟨hs0.le, min_le_right _ _⟩
    have hsη₁ : s < η₁ := lt_of_le_of_lt (min_le_left _ _)
      (by have := min_le_left η₁ η₂; have := lt_min hη₁ hη₂; linarith)
    have hsη₂ : s < η₂ := lt_of_le_of_lt (min_le_left _ _)
      (by have := min_le_right η₁ η₂; have := lt_min hη₁ hη₂; linarith)
    have hmemK : ∀ p ∈ S, p ≠ ((0 : ℝ), (0 : ℝ)) → ‖Φ p - q‖ ≤ a → p ∈ K := by
      intro p hp hp0 hpa
      have hne : Φ p ≠ q := fun h => hp0 (hinj hp h00 h)
      exact ⟨Φ p, ⟨Φ p, hne, hρfix _ hne hpa⟩, hΨΦ p hp⟩
    have hp1 : ((s, 0) : ℝ × ℝ) ∈ K := hmemK _ (ha1 s hsε)
      (by simp [hs0.ne']) (h₁ s hsε hsη₁)
    have hp2 : ((-s, 0) : ℝ × ℝ) ∈ K := hmemK _ (ha2 s hsε)
      (by simp [hs0.ne']) (h₂ s hsε hsη₂)
    -- the separation of `T ∖ {0}`
    set U₁ : Set (ℝ × ℝ) := {p | 0 < p.1} with hU₁
    set U₂ : Set (ℝ × ℝ) := {p | p.1 < 0} ∪ {p | 0 < p.2} with hU₂
    have hU₁o : IsOpen U₁ := isOpen_lt continuous_const continuous_fst
    have hU₂o : IsOpen U₂ :=
      (isOpen_lt continuous_fst continuous_const).union (isOpen_lt continuous_const continuous_snd)
    have hcover : K ⊆ U₁ ∪ U₂ := by
      intro p hp
      have hpT := hKT hp
      have hp0 : p ≠ ((0 : ℝ), (0 : ℝ)) := fun h => hK0 (h ▸ hp)
      rcases hpT with ⟨-, -, h2⟩ | ⟨h1, h2, -⟩
      · rcases lt_trichotomy p.1 0 with h | h | h
        · exact Or.inr (Or.inl h)
        · exact absurd (Prod.ext h h2) hp0
        · exact Or.inl h
      · rcases eq_or_lt_of_le h2 with h | h
        · exact absurd (Prod.ext h1 h.symm) hp0
        · exact Or.inr (Or.inr h)
    obtain ⟨p, hpK, hp₁, hp₂⟩ := hKpre U₁ U₂ hU₁o hU₂o hcover
      ⟨_, hp1, (show (0 : ℝ) < ((s, 0) : ℝ × ℝ).1 from hs0)⟩
      ⟨_, hp2, Or.inl (show ((-s, 0) : ℝ × ℝ).1 < 0 from neg_neg_of_pos hs0)⟩
    rcases hKT hpK with ⟨-, -, h2⟩ | ⟨h1, -, -⟩
    · change 0 < p.1 at hp₁
      rcases hp₂ with h | h
      · exact absurd h (not_lt.2 hp₁.le)
      · change 0 < p.2 at h; rw [h2] at h; exact lt_irrefl 0 h
    · change 0 < p.1 at hp₁; rw [h1] at hp₁; exact lt_irrefl 0 hp₁


/-- **2021 Question 4.2.4, the settled part** (p. 187): "From our previous discussion this is
impossible if we require `O` to be an sc⁺-retract."  If `(O, E, E)` is an sc⁺-retract (partial
quadrant `C = E`), then `O` is not homeomorphic to the "T" (`tSet`).  (`O = O_∞` holds for every
sc⁺-retract, Lemma 4.1.7.)  *Proof*: at the point `o` corresponding to `(0, 0)` the retract is,
near `o`, homeomorphic to an open subset of its finite-dimensional tangent space
(`ScRetraction.IsScPlus.exists_flat`; the minimal subspace of `C = E` is `E`), which
`not_homeomorph_open` excludes. -/
theorem question_4_2_4_scPlus {E : ScBanach} {O : Set (E 0)} (hO : IsScPlusRetract E univ O) :
    IsEmpty (tSet ≃ₜ O) := by
  classical
  refine ⟨fun e => ?_⟩
  obtain ⟨t, htO, ht⟩ := hO
  set p₀ : tSet := ⟨((0 : ℝ), (0 : ℝ)), zero_mem_tSet⟩ with hp₀
  have ho : (e p₀ : E 0) ∈ t.retract := htO ▸ (e p₀).2
  obtain ⟨z, hz, -⟩ := exists_smoothLvl_one_of_mem_smooth (lemma_4_1_7_i ht ho)
  have hzt : E.toBase 1 z ∈ t.retract := hz ▸ ho
  obtain ⟨n, W, T, hT⟩ := isPartialQuadrant_univ E
  have := lemma_4_1_7_ii ht hzt
  have hred : LinearMap.range (scDeriv t.U t z : E 0 →ₗ[ℝ] E 0) ≤
      minimalSubspaceWith T (E.toBase 1 z) := by
    intro v _
    refine (mem_minimalSubspaceWith T).2 fun i _ => ?_
    exfalso
    have hq : coordVec T (fun _ => -1) ∈ T 0 ⁻¹' quadrant n W 0 := hT ▸ mem_univ _
    have h := hq i
    rw [coord_coordVec] at h
    norm_num at h
  set N := LinearMap.range (scDeriv t.U t z : E 0 →ₗ[ℝ] E 0) with hNdef
  obtain ⟨G, V, χ, Γ, hG, hoG, hV, hχ, hΓ, hΓχ, hχΓ⟩ := ht.exists_flat T hT hzt hNdef hred
  rw [hz] at hoG
  rw [htO] at hχ hΓ hΓχ
  have hOG : IsScRetract E univ (O ∩ G) := proposition_2_3_1_one (htO ▸ t.isScRetract) hG
  have hχc : ContinuousOn χ (O ∩ G) := hχ.continuousOn hOG
  have hVr : IsScRetract (ScBanach.const N) univ V :=
    (⟨isPartialQuadrant_univ _, V, hV, (inter_univ V).symm⟩ :
      IsRelOpenInQuadrant (ScBanach.const N) univ V).isScRetract
  have hΓc : ContinuousOn Γ V := hΓ.continuousOn hVr
  have hΓV : ∀ v ∈ V, Γ v ∈ O ∩ G := fun v hv => hΓ.mapsTo hv
  have hχV : ∀ u ∈ O ∩ G, χ u ∈ V := fun u hu => hχ.mapsTo hu
  -- the transferred maps between `S ⊆ T` and `V`
  set S : Set (ℝ × ℝ) := {p | ∃ hp : p ∈ tSet, (e ⟨p, hp⟩ : E 0) ∈ G} with hSdef
  set Φ : ℝ × ℝ → N := fun p => if hp : p ∈ tSet then χ (e ⟨p, hp⟩) else 0 with hΦdef
  set Ψ : N → ℝ × ℝ := fun v => if hv : Γ v ∈ O then (e.symm ⟨Γ v, hv⟩ : ℝ × ℝ) else 0
    with hΨdef
  have hST : S ⊆ tSet := fun p hp => hp.1
  -- `S` is a relatively open neighbourhood of `(0, 0)` in `T`
  have hSo : IsOpen {p : tSet | (e p : E 0) ∈ G} :=
    hG.preimage (continuous_subtype_val.comp e.continuous)
  obtain ⟨U', hU'o, hU'⟩ := isOpen_induced_iff.1 hSo
  have h0U' : ((0 : ℝ), (0 : ℝ)) ∈ U' := by
    have : p₀ ∈ Subtype.val ⁻¹' U' := by rw [hU']; exact hoG
    exact this
  obtain ⟨δ, hδ, hδU'⟩ := Metric.isOpen_iff.1 hU'o _ h0U'
  have hS : tSet ∩ ball 0 δ ⊆ S := by
    rintro p ⟨hpT, hpb⟩
    refine ⟨hpT, ?_⟩
    have : (⟨p, hpT⟩ : tSet) ∈ Subtype.val ⁻¹' U' := hδU' hpb
    rw [hU'] at this
    exact this
  -- continuity
  have hΦc : ContinuousOn Φ S := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hg : Continuous fun p : S => (e ⟨p.1, p.2.1⟩ : E 0) :=
      continuous_subtype_val.comp (e.continuous.comp
        (continuous_subtype_val.subtype_mk fun p : S => p.2.1))
    have hmem : ∀ p : S, (e ⟨p.1, p.2.1⟩ : E 0) ∈ O ∩ G := fun p => ⟨(e _).2, p.2.2⟩
    refine (hχc.comp_continuous hg hmem).congr fun p => ?_
    simp only [Set.domRestrict_apply, hΦdef, Function.comp_apply, dif_pos p.2.1]
  have hΨc : ContinuousOn Ψ V := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hg : Continuous fun v : V => (⟨Γ v, (hΓV v v.2).1⟩ : O) :=
      (hΓc.domRestrict).subtype_mk _
    refine (continuous_subtype_val.comp (e.symm.continuous.comp hg)).congr fun v => ?_
    simp only [Set.domRestrict_apply, hΨdef, Function.comp_apply, dif_pos (hΓV v v.2).1]
  -- the maps
  have hΦV : MapsTo Φ S V := by
    intro p hp
    simp only [hΦdef, dif_pos hp.1]
    exact hχV _ ⟨(e _).2, hp.2⟩
  have hΨval : ∀ v (hv : v ∈ V), Ψ v = (e.symm ⟨Γ v, (hΓV v hv).1⟩ : ℝ × ℝ) := fun v hv => by
    simp only [hΨdef, dif_pos (hΓV v hv).1]
  have hΨS : MapsTo Ψ V S := by
    intro v hv
    rw [hΨval v hv]
    refine ⟨(e.symm _).2, ?_⟩
    have : (⟨((e.symm ⟨Γ v, (hΓV v hv).1⟩ : tSet) : ℝ × ℝ), (e.symm _).2⟩ : tSet) =
        e.symm ⟨Γ v, (hΓV v hv).1⟩ := Subtype.ext rfl
    rw [this, e.apply_symm_apply]
    exact (hΓV v hv).2
  have hΨΦ : ∀ p ∈ S, Ψ (Φ p) = p := by
    intro p hp
    set u : E 0 := (e ⟨p, hp.1⟩ : E 0) with hudef
    have hu : u ∈ O ∩ G := ⟨(e _).2, hp.2⟩
    have hΦp : Φ p = χ u := by simp only [hΦdef, dif_pos hp.1, hudef]
    rw [hΦp, hΨval _ (hχV _ hu)]
    have : (⟨Γ (χ u), (hΓV _ (hχV _ hu)).1⟩ : O) = e ⟨p, hp.1⟩ :=
      Subtype.ext (hΓχ _ hu)
    rw [this, e.symm_apply_apply]
  have hΦΨ : ∀ v ∈ V, Φ (Ψ v) = v := by
    intro v hv
    rw [hΨval v hv]
    simp only [hΦdef, dif_pos (e.symm ⟨Γ v, (hΓV v hv).1⟩).2]
    have : (⟨((e.symm ⟨Γ v, (hΓV v hv).1⟩ : tSet) : ℝ × ℝ), (e.symm _).2⟩ : tSet) =
        e.symm ⟨Γ v, (hΓV v hv).1⟩ := Subtype.ext rfl
    rw [this, e.apply_symm_apply]
    exact hχΓ v hv
  exact not_homeomorph_open hST hδ hS hV hΦc hΨc hΦV hΨS hΨΦ hΦΨ

end Question424

end Polyfold
