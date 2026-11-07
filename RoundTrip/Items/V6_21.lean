import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_21

/-! Round trip for V6_21 (Lemma 6.18: the kernels `ker(P S)` form a trivial bundle).

`A` is the type of `LocalDetChart.lemma_6_18` (universes at `0`); `LocalDetChart` (the data
`(T, P, Y, ε)` with the conclusions of Lemma 6.17), `ySol` (`y(·, S) = −(P S|_Y)⁻¹ P S`),
`kerMap` (`k ↦ k + y(k, S)`) and `kerProj` (projection onto `ker(P T)` along `Y`) are definitions
(vocabulary).

`A → B` (proved): B's hypotheses are exactly the fields of a `LocalDetChart` `c`; `y S k :=
c.ySol S k`; B's homeomorphism is `(S, k) ↦ (S, kerMap S k)` with inverse `(S, x) ↦ (S, kerProj x)`
(A's third and fourth conjuncts), continuous by A's first conjunct and the continuity of `kerProj`.

`B → A` (proved): B's `y` is identified with the project's `ySol` on `ball × ker(P T)` (both solve
`y ∈ Y`, `P S (k + y) = 0`, and `P S|_Y` is injective on the ball).  Then A's second conjunct is
B's equation, A's third comes from `Φ ∘ Φ⁻¹ = id` and B's formula for `Φ⁻¹`, and A's first
(continuity of `(S, x) ↦ kerMap S x` on `ball × E`, not only on `ball × ker(P T)`) from B's joint
continuity of `y` and `kerMap S x = kerMap S (kerProj x)` on the ball (`kerMap S` kills `Y`).  A's
fourth conjunct, `kerProj (kerMap S k) = k` for EVERY `S` (also outside the ball, where `ySol` is
the project's junk extension with `(P S|_Y)⁻¹ := 0`), is not in B; it is proved directly from
`ySol_mem` (`y(x, S) ∈ Y`).
-/

namespace RoundTrip.V6_21
open Polyfold

/-- The project's statement (Lemma 6.18), universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.LocalDetChart.lemma_6_18.{0, 0}

theorem A_holds : A := @Polyfold.LocalDetChart.lemma_6_18.{0, 0}

/-- The chart `(T, P, Y, ε)` of B's data. -/
noncomputable def mkChart {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) (P : F →L[ℝ] F) (Y : Submodule ℝ E) (ε : ℝ) (hT : T.IsFredholm)
    (hP : IsGoodLeftProj T P)
    (hY : Submodule.IsTopCompl (LinearMap.ker ((P.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F)) Y)
    (hε : 0 < ε)
    (hball : ∀ S : E →L[ℝ] F, ‖S - T‖ < ε →
      IsGoodLeftProj S P ∧
      ∃ e : Y ≃L[ℝ] LinearMap.range (P : F →ₗ[ℝ] F), ∀ y : Y, (e y : F) = P (S y)) :
    LocalDetChart E F where
  T := T
  isFredholm := hT
  P := P
  isGoodLeftProj := hP
  Y := Y
  isTopCompl := hY
  ε := ε
  ε_pos := hε
  isGoodLeftProj_of_lt S hS := (hball S hS).1
  exists_equiv_of_lt S hS := by
    obtain ⟨e, he⟩ := (hball S hS).2
    exact ⟨e, ContinuousLinearMap.ext fun y => Subtype.ext (he y)⟩

/-- `A ⇒ B`: `y = ySol` of the chart built from B's data. -/
theorem A_to_B : A → B := by
  intro hA E F _ _ _ _ _ _ T P Y ε hT hP hY hε hball
  obtain ⟨c, hcT, hcP, hcY, hcε⟩ : ∃ c : LocalDetChart E F, c.T = T ∧ c.P = P ∧ c.Y = Y ∧
      c.ε = ε := ⟨mkChart T P Y ε hT hP hY hε hball, rfl, rfl, rfl, rfl⟩
  subst hcT hcP hcY hcε
  obtain ⟨h1, h2, h3, h4⟩ := hA c
  have hmem : ∀ S : Metric.ball c.T c.ε, ‖(S : E →L[ℝ] F) - c.T‖ < c.ε := fun S =>
    mem_ball_iff_norm.1 S.2
  have hkm : ∀ (S : E →L[ℝ] F) (x : E), c.kerMap S x = x + c.ySol S x := fun S x => rfl
  -- continuity of `(S, k) ↦ y(k, S)` on `ball × K`
  have hcontK : Continuous (fun p : Metric.ball c.T c.ε ×
      LinearMap.ker ((c.P.comp c.T : E →L[ℝ] F) : E →ₗ[ℝ] F) => c.kerMap p.1 p.2) := by
    have hg : Continuous (fun p : Metric.ball c.T c.ε ×
        LinearMap.ker ((c.P.comp c.T : E →L[ℝ] F) : E →ₗ[ℝ] F) => ((p.1 : E →L[ℝ] F), (p.2 : E))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    have h1' := ContinuousOn.comp_continuous h1 hg fun p => hmem p.1
    exact h1'
  have hcont : Continuous (fun p : Metric.ball c.T c.ε ×
      LinearMap.ker ((c.P.comp c.T : E →L[ℝ] F) : E →ₗ[ℝ] F) => c.ySol p.1 p.2) := by
    have : (fun p : Metric.ball c.T c.ε × LinearMap.ker ((c.P.comp c.T : E →L[ℝ] F) : E →ₗ[ℝ] F) =>
        c.ySol p.1 p.2) = fun p => c.kerMap p.1 p.2 - (p.2 : E) := by
      funext p
      rw [hkm]
      abel
    rw [this]
    exact hcontK.sub (continuous_subtype_val.comp continuous_snd)
  have hker : ∀ (S : Metric.ball c.T c.ε) (k : LinearMap.ker ((c.P.comp c.T : E →L[ℝ] F) : E →ₗ[ℝ] F)),
      c.P ((S : E →L[ℝ] F) ((k : E) + c.ySol S k)) = 0 := fun S k =>
    h2 S (hmem S) k k.2
  refine ⟨fun S k => c.ySol S k, fun S k => ⟨c.ySol_mem S k, hker S k⟩,
    fun S => ((c.ySol S : E →ₗ[ℝ] E).comp (LinearMap.ker
      ((c.P.comp c.T : E →L[ℝ] F) : E →ₗ[ℝ] F)).subtype).isLinear, hcont, ?_⟩
  refine ⟨
    { toFun := fun p => ⟨(p.1, (p.2 : E) + c.ySol p.1 p.2), hker p.1 p.2⟩
      invFun := fun q => (q.1.1, c.kerProj q.1.2)
      left_inv := fun p => Prod.ext rfl (h4 p.1 p.2)
      right_inv := fun q => Subtype.ext (Prod.ext rfl (h3 q.1.1 (hmem q.1.1) q.1.2 q.2))
      continuous_toFun := by
        refine Continuous.subtype_mk (continuous_fst.prodMk ?_) _
        exact (continuous_subtype_val.comp continuous_snd).add hcont
      continuous_invFun := by
        refine (continuous_fst.comp continuous_subtype_val).prodMk ?_
        exact c.kerProj.continuous.comp (continuous_snd.comp continuous_subtype_val) },
    fun S k => rfl, fun q => rfl⟩

/-- `B ⇒ A` (see the module docstring). -/
theorem B_to_A : B → A := by
  intro hB E F _ _ _ _ _ _ c
  have hball : ∀ S : E →L[ℝ] F, ‖S - c.T‖ < c.ε →
      IsGoodLeftProj S c.P ∧
      ∃ e : c.Y ≃L[ℝ] LinearMap.range (c.P : F →ₗ[ℝ] F), ∀ y : c.Y, (e y : F) = c.P (S y) :=
    fun S hS => ⟨c.isGoodLeftProj_of_lt S hS, by
      obtain ⟨e, he⟩ := c.exists_equiv_of_lt S hS
      exact ⟨e, fun y => by rw [← coe_projRestrict_apply, ← he]; rfl⟩⟩
  obtain ⟨y, hy, -, hcont, Φ, hΦ, hΦs⟩ :=
    hB c.T c.P c.Y c.ε c.isFredholm c.isGoodLeftProj c.isTopCompl c.ε_pos hball
  have hkm : ∀ (S : E →L[ℝ] F) (x : E), c.kerMap S x = x + c.ySol S x := fun S x => rfl
  -- `P S|_Y` is injective on the ball
  have hinj : ∀ S : E →L[ℝ] F, ‖S - c.T‖ < c.ε → ∀ z ∈ c.Y, c.P (S z) = 0 → z = 0 := by
    intro S hS z hz h0
    have := c.inverse_projRestrict_apply S hS ⟨z, hz⟩
    have h0' : projRestrict c.P S c.Y ⟨z, hz⟩ = 0 := Subtype.ext h0
    rw [h0', map_zero] at this
    exact (congrArg Subtype.val this).symm
  -- B's `y` is the project's `ySol` on `ball × K`
  have hyid : ∀ (S : Metric.ball c.T c.ε) (k : c.K), y S k = c.ySol S k := by
    intro S k
    have hS : ‖(S : E →L[ℝ] F) - c.T‖ < c.ε := mem_ball_iff_norm.1 S.2
    have h1 := (hy S k).2
    have h2 := c.proj_apply_ySol S hS k
    rw [← sub_eq_zero]
    refine hinj S hS _ (c.Y.sub_mem (hy S k).1 (c.ySol_mem S k)) ?_
    rw [map_add, map_add] at h1
    rw [map_sub, map_sub, h2, sub_neg_eq_add, add_comm]
    exact h1
  -- `kerMap S z = 0` for `z ∈ Y` on the ball
  have hkY : ∀ S : E →L[ℝ] F, ‖S - c.T‖ < c.ε → ∀ z ∈ c.Y, c.kerMap S z = 0 := by
    intro S hS z hz
    have h2 := c.proj_apply_ySol S hS z
    rw [hkm, ← neg_neg (c.ySol S z), ← sub_eq_add_neg, sub_eq_zero]
    refine (sub_eq_zero.1 (hinj S hS _ (c.Y.sub_mem hz (c.Y.neg_mem (c.ySol_mem S z))) ?_))
    rw [map_sub, map_sub, map_neg, map_neg, h2, neg_neg, sub_self]
  -- `kerMap S x = kerMap S (kerProj x)` on the ball
  have hkP : ∀ S : E →L[ℝ] F, ‖S - c.T‖ < c.ε → ∀ x : E, c.kerMap S x = c.kerMap S (c.kerProj x) := by
    intro S hS x
    have hx : x - (c.kerProj x : E) ∈ c.Y := Submodule.sub_projection_mem c.isTopCompl.isCompl x
    have := hkY S hS _ hx
    rw [map_sub, sub_eq_zero] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- continuity on `ball × E`
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : Set.domRestrict {p : (E →L[ℝ] F) × E | ‖p.1 - c.T‖ < c.ε}
        (fun p : (E →L[ℝ] F) × E => c.kerMap p.1 p.2) = fun p =>
          (c.kerProj p.1.2 : E) + y ⟨p.1.1, mem_ball_iff_norm.2 p.2⟩ (c.kerProj p.1.2) := by
      funext p
      rw [Set.domRestrict_apply, hkP p.1.1 p.2 p.1.2, hkm,
        hyid ⟨p.1.1, mem_ball_iff_norm.2 p.2⟩ (c.kerProj p.1.2)]
    rw [heq]
    have hg : Continuous fun p : {p : (E →L[ℝ] F) × E | ‖p.1 - c.T‖ < c.ε} =>
        ((⟨p.1.1, mem_ball_iff_norm.2 p.2⟩ : Metric.ball c.T c.ε), c.kerProj p.1.2) :=
      (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _).prodMk
        (c.kerProj.continuous.comp (continuous_snd.comp continuous_subtype_val))
    exact (continuous_subtype_val.comp
      (c.kerProj.continuous.comp (continuous_snd.comp continuous_subtype_val))).add
      (hcont.comp hg)
  · -- `kerMap S k ∈ ker(P S)`
    intro S hS k hk
    have h1 := (hy ⟨S, mem_ball_iff_norm.2 hS⟩ ⟨k, hk⟩).2
    rw [hyid] at h1
    exact h1
  · -- `kerMap S (kerProj x) = x` on `ker(P S)`, from `Φ ∘ Φ⁻¹ = id`
    intro S hS x hx
    let q : {p : Metric.ball c.T c.ε × E //
        p.2 ∈ LinearMap.ker ((c.P.comp (p.1 : E →L[ℝ] F) : E →L[ℝ] F) : E →ₗ[ℝ] F)} :=
      ⟨(⟨S, mem_ball_iff_norm.2 hS⟩, x), hx⟩
    have h1 := Φ.apply_symm_apply q
    have h2 := hΦs q
    rw [h2] at h1
    have h3 := congrArg Subtype.val h1
    rw [hΦ] at h3
    have h4 := congrArg Prod.snd h3
    rw [hkm, ← hyid ⟨S, mem_ball_iff_norm.2 hS⟩ (c.kerProj x)]
    exact h4
  · -- `kerProj (kerMap S k) = k` for every `S` (not in B: outside the ball `ySol` is junk)
    intro S k
    rw [hkm, map_add, LocalDetChart.kerProj, Submodule.projectionOntoL_apply_left,
      (Submodule.projectionOntoL_apply_eq_zero_iff _).2 (c.ySol_mem S k), add_zero]

#rt_check RoundTrip.V6_21.A_to_B [Polyfold.LocalDetChart.lemma_6_18]
#rt_check RoundTrip.V6_21.B_to_A [Polyfold.LocalDetChart.lemma_6_18]
#rt_overlap RoundTrip.V6_21.B_to_A [Polyfold.LocalDetChart.lemma_6_18]

end RoundTrip.V6_21
