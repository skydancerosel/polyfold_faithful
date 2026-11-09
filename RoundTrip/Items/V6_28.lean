import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_28

/-! Round trip for V6_28 (Lemma 6.25, the transition maps of the local determinant bundles).

A = `lemma_6_5_9` ∧ `lemma_6_5_9_local` (universes at `0`): the transition function
`g(S) = ω'(S)*(γ^{P'}_S (γ^P_S)⁻¹ ω(S))` is continuous and nowhere zero on the common ball
(and, locally, a continuous nowhere-zero function).
B = `Formula` (Corollary 6.13 for the transition on each fibre, for every `Q ≤ P, P'` good for
`P S`, `P' S`) ∧ `TopIso` (in the frames, `(S, t) ↦ (S, g(S) t)` is a homeomorphism of
`(ball ∩ ball') × ℝ`).

* `A ⇒ B`: `TopIso` from `lemma_6_5_9` (an explicit homeomorphism with inverse `t ↦ t / g(S)`);
  `Formula` is `corollary_6_4_12` (a project lemma of §6.2, not part of the item) after
  `Q ∈ Π_{P S}`, `Q ≤ P` ⇒ `Q ∈ Π_S` — it is proved outright, without the hypothesis.
* `B ⇒ A`: `g(S) = (Φ(S, 1)).2` is continuous on the subtype; `g(S) ≠ 0` since `Φ` is injective
  and `Φ(S, 0) = (S, 0)`; the local form takes `N = ball ∩ ball'`.
-/

namespace RoundTrip.V6_28
open Polyfold

/-- The project's statement (Lemma 6.25 and its local form), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.lemma_6_5_9.{0, 0} ∧ type_of% @Polyfold.lemma_6_5_9_local.{0, 0}

theorem A_holds : A := ⟨@Polyfold.lemma_6_5_9.{0, 0}, @Polyfold.lemma_6_5_9_local.{0, 0}⟩

section
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- `Q ∈ Π_{P S}` and `Q ≤ P` give `Q ∈ Π_S` (`Q P S = Q S`). -/
theorem isGoodLeftProj_of_comp {S : E →L[ℝ] F} {P Q : F →L[ℝ] F} (hQP : ProjLE Q P)
    (h : IsGoodLeftProj (P ∘L S) Q) : IsGoodLeftProj S Q := by
  refine ⟨h.isProj, h.finite_coker, ?_⟩
  have e : Q ∘L S = Q ∘L (P ∘L S) := by rw [← ContinuousLinearMap.comp_assoc, ← hQP.1]
  rw [e]
  exact h.range_comp

/-- B's `Formula` is Corollary 6.13 (proved outright; it does not use A). -/
theorem formula_holds : Formula (E := E) (F := F) := by
  intro c c' S hS hS' Q hQ hQ' hPS hP'S hQS hQS' h
  exact (corollary_6_4_12 (T := (S : E →L[ℝ] F)) S.2 (isGoodLeftProj_of_comp hQ hQS)
    (c'.isGoodLeftProj_of_lt S hS') (c.isGoodLeftProj_of_lt S hS) hQ hQ' h).symm

/-- `TopIso` from the continuity and non-vanishing of the transition function. -/
theorem topIso_of
    (hA : ∀ c c' : LocalDetChart E F,
      ContinuousOn (fun S : FredholmOp E F => c'.coord S (c.coordInv S 1))
          (c.baseSet ∩ c'.baseSet) ∧
        ∀ S ∈ c.baseSet ∩ c'.baseSet, c'.coord S (c.coordInv S 1) ≠ 0) :
    TopIso (E := E) (F := F) := by
  intro c c'
  set g : ↥(c.baseSet ∩ c'.baseSet) → ℝ :=
    fun S => c'.coord (S : FredholmOp E F) (c.coordInv (S : FredholmOp E F) 1) with hgdef
  have hg : Continuous g := (hA c c').1.domRestrict
  have hg0 : ∀ S, g S ≠ 0 := fun S => (hA c c').2 S S.2
  have hlin : ∀ (S : ↥(c.baseSet ∩ c'.baseSet)) (t : ℝ),
      c'.coord (S : FredholmOp E F) (c.coordInv (S : FredholmOp E F) t) = g S * t := by
    intro S t
    have e : c.coordInv (S : FredholmOp E F) t = t • c.coordInv (S : FredholmOp E F) 1 := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [e, map_smul, smul_eq_mul, mul_comm]
  refine ⟨{ toFun := fun p => (p.1, g p.1 * p.2)
            invFun := fun p => (p.1, (g p.1)⁻¹ * p.2)
            left_inv := fun p => ?_
            right_inv := fun p => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun S t => ?_⟩
  · simp only
    rw [← mul_assoc, inv_mul_cancel₀ (hg0 p.1), one_mul]
  · simp only
    rw [← mul_assoc, mul_inv_cancel₀ (hg0 p.1), one_mul]
  · exact continuous_fst.prodMk ((hg.comp continuous_fst).mul continuous_snd)
  · exact continuous_fst.prodMk (((hg.comp continuous_fst).inv₀ fun p => hg0 p.1).mul
      continuous_snd)
  · change (S, g S * t) = _
    rw [hlin]

end

/-- `A ⇒ B`: `TopIso` from `lemma_6_5_9`; `Formula` from `corollary_6_4_12`. -/
theorem A_to_B : A → B := by
  intro hA E F _ _ _ _ _ _
  exact ⟨formula_holds, topIso_of fun c c' => hA.1 c c'⟩

/-- `B ⇒ A`: the transition function is the second coordinate of `Φ(S, 1)`. -/
theorem B_to_A : B → A := by
  have key : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F], B →
      ∀ c c' : LocalDetChart E F,
        ContinuousOn (fun S : FredholmOp E F => c'.coord S (c.coordInv S 1))
            (c.baseSet ∩ c'.baseSet) ∧
          ∀ S ∈ c.baseSet ∩ c'.baseSet, c'.coord S (c.coordInv S 1) ≠ 0 := by
    intro E F _ _ _ _ _ _ hB c c'
    obtain ⟨Φ, hΦ⟩ := (hB E F).2 c c'
    refine ⟨?_, fun S hS => ?_⟩
    · rw [continuousOn_iff_continuous_domRestrict]
      have e : (c.baseSet ∩ c'.baseSet).domRestrict
          (fun S : FredholmOp E F => c'.coord S (c.coordInv S 1)) =
          fun S => (Φ (S, 1)).2 := by
        funext S
        rw [hΦ]
        rfl
      rw [e]
      exact continuous_snd.comp (Φ.continuous.comp (continuous_id.prodMk continuous_const))
    · intro h0
      have h1 := hΦ ⟨S, hS⟩ 1
      have h2 := hΦ ⟨S, hS⟩ 0
      rw [map_zero, map_zero] at h2
      have h1' : Φ (⟨S, hS⟩, 1) = (⟨S, hS⟩, 0) := by rw [h1]; simp only [h0]
      have := Φ.injective (h1'.trans h2.symm)
      exact one_ne_zero (congrArg Prod.snd this)
  intro hB
  refine ⟨fun c c' => key hB c c', fun c c' S₀ hS₀ => ?_⟩
  refine ⟨c.baseSet ∩ c'.baseSet,
    (c.isOpen_baseSet.inter c'.isOpen_baseSet).mem_nhds hS₀,
    fun S => c'.coord S (c.coordInv S 1), (key hB c c').1, fun S hS => ⟨(key hB c c').2 S hS, rfl⟩⟩

#rt_check RoundTrip.V6_28.A_to_B [Polyfold.lemma_6_5_9, Polyfold.lemma_6_5_9_local]
#rt_check RoundTrip.V6_28.B_to_A [Polyfold.lemma_6_5_9, Polyfold.lemma_6_5_9_local]
#rt_overlap RoundTrip.V6_28.B_to_A [Polyfold.lemma_6_5_9, Polyfold.lemma_6_5_9_local]

end RoundTrip.V6_28
