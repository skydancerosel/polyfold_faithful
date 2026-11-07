import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_11

/-!
Round trip for V6_11 (Lemma 6.10).  `A` is `lemma_6_10 ∧ lemma_6_10_text_reading` (universes of
`lemma_6_10` at `0`; `lemma_6_10_text_reading` has none).

* `A ⇒ B`: `lemma_6_10` (no Fredholm hypothesis, no completeness) specializes to B.
* `B ⇒ A` is not proved.  Partial result `B_to_lemma_6_10_banach`: B gives `lemma_6_10` for
  every `T` between Banach spaces, Fredholm or not (apply B to `id_F`, which is Fredholm and has
  `Π_id ⊇ Π_T`, then `R(P'' T) = R(P'' P T) = P''(R(P)) = R(P'')`).  What B cannot give:
  `lemma_6_10` on incomplete normed spaces, and the conjunct `lemma_6_10_text_reading`, a concrete
  statement about `ℝ²` that has nothing to do with B.
* `B_proof` (the blind literal reading of the proof's construction) is false: `not_B_proof`
  (the blind's own example: `P` onto `ℝe₁` along `ℝe₂`, `P'` onto `ℝe₁` along `ℝ(e₁ + e₂)`,
  `X = X' = 0`, `Z = ker P`, `P'' = P`; then `P'' ≤ P'` fails).  Moreover A's second conjunct
  alone refutes it: `text_reading_to_not_B_proof` builds, for ANY `P, P'` of
  `lemma_6_10_text_reading`, complements `X, X', Z` and the projection `P''` of B_proof, so the
  project's `lemma_6_10_text_reading` says exactly that B_proof's construction fails.
-/

namespace RoundTrip.V6_11
open Polyfold

/-- The project's statement: Lemma 6.10 and the text-reading counterexample, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.lemma_6_10.{0, 0} ∧ type_of% @Polyfold.lemma_6_10_text_reading

theorem A_holds : A := ⟨@Polyfold.lemma_6_10, @Polyfold.lemma_6_10_text_reading⟩

section Glue

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- B's good left-projections are the project's. -/
theorem isGLP_iff (T : E →L[ℝ] F) (P : F →L[ℝ] F) : IsGLP T P ↔ IsGoodLeftProj T P :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.isProj, h.finite_coker, h.range_comp⟩⟩

/-- `id_F` is Fredholm (classically). -/
theorem isFredholmOp_id : IsFredholmOp (ContinuousLinearMap.id ℝ F) := by
  have hk : LinearMap.ker ((ContinuousLinearMap.id ℝ F : F →L[ℝ] F) : F →ₗ[ℝ] F) = ⊥ :=
    LinearMap.ker_eq_bot.2 (fun x y h => h)
  have hr : LinearMap.range ((ContinuousLinearMap.id ℝ F : F →L[ℝ] F) : F →ₗ[ℝ] F) = ⊤ :=
    LinearMap.range_eq_top.2 (fun y => ⟨y, rfl⟩)
  refine ⟨?_, ?_, ?_⟩
  · rw [hk]; infer_instance
  · rw [hr]; exact isClosed_univ
  · rw [hr]
    have : Subsingleton (F ⧸ (⊤ : Submodule ℝ F)) := Submodule.Quotient.subsingleton_iff.2 rfl
    infer_instance

/-- Every good left-projection of `T` is one of `id`. -/
theorem isGLP_id {T : E →L[ℝ] F} {P : F →L[ℝ] F} (hP : IsGoodLeftProj T P) :
    IsGLP (ContinuousLinearMap.id ℝ F) P :=
  ⟨hP.isProj, hP.finite_coker, by rw [ContinuousLinearMap.comp_id]⟩

/-- If `P'' = P'' P` and `R(P T) = R(P)`, then `R(P'' T) = R(P'')` (proved here, not taken from
the project). -/
theorem range_comp_of_le {T : E →L[ℝ] F} {P P'' : F →L[ℝ] F} (hP : IsGoodLeftProj T P)
    (h : P'' = P'' ∘L P) :
    LinearMap.range ((P'' ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) =
      LinearMap.range (P'' : F →ₗ[ℝ] F) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨T x, rfl⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ : P y ∈ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
      rw [hP.range_comp]; exact ⟨y, rfl⟩
    refine ⟨x, ?_⟩
    have hx' : P (T x) = P y := hx
    change P'' (T x) = P'' y
    calc P'' (T x) = (P'' ∘L P) (T x) := by rw [← h]
      _ = P'' (P (T x)) := rfl
      _ = P'' (P y) := by rw [hx']
      _ = (P'' ∘L P) y := rfl
      _ = P'' y := by rw [← h]

end Glue

theorem A_to_B : A → B := by
  intro hA E F _ _ _ _ _ _ T _ P hP P' hP'
  obtain ⟨P'', h, h1, h2⟩ := hA.1 ((isGLP_iff T P).1 hP) ((isGLP_iff T P').1 hP')
  exact ⟨P'', (isGLP_iff T P'').2 h, h1, h2⟩

/-- **Partial `B ⇒ A`**: B gives `lemma_6_10` for every `T` between Banach spaces (no Fredholm
hypothesis), via `id_F`. -/
theorem B_to_lemma_6_10_banach (hB : B) {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {T : E →L[ℝ] F} {P P' : F →L[ℝ] F} (hP : IsGoodLeftProj T P) (hP' : IsGoodLeftProj T P') :
    ∃ P'' : F →L[ℝ] F, IsGoodLeftProj T P'' ∧ ProjLE P'' P ∧ ProjLE P'' P' := by
  obtain ⟨P'', hP'', h1, h2⟩ :=
    hB F F (ContinuousLinearMap.id ℝ F) isFredholmOp_id P (isGLP_id hP) P' (isGLP_id hP')
  exact ⟨P'', ⟨hP''.1, hP''.2.1, range_comp_of_le hP h1.1⟩, h1, h2⟩

/-! ### `B_proof` is false -/

/-- **`¬ B_proof`**: the blind's example. -/
theorem not_B_proof : ¬ B_proof := by
  intro hB
  set P : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearMap.inl ℝ ℝ ℝ ∘L ContinuousLinearMap.fst ℝ ℝ ℝ with hPdef
  set P' : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearMap.inl ℝ ℝ ℝ ∘L (ContinuousLinearMap.fst ℝ ℝ ℝ -
      ContinuousLinearMap.snd ℝ ℝ ℝ) with hP'def
  have hPv : ∀ v, P v = (v.1, 0) := fun v => rfl
  have hP'v : ∀ v, P' v = (v.1 - v.2, 0) := fun v => rfl
  have hPP : P ∘L P = P := by ext <;> simp [hPv]
  have hP'P' : P' ∘L P' = P' := by ext <;> simp [hP'v]
  have hR : LinearMap.range (P : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) =
      LinearMap.range (P' : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact ⟨(v.1, 0), by simp [hPv, hP'v]⟩
    · rintro _ ⟨v, rfl⟩
      exact ⟨(v.1 - v.2, 0), by simp [hPv, hP'v]⟩
  have hI : LinearMap.range (P : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) ⊓
      LinearMap.range (P' : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) =
      LinearMap.range (P : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) := by rw [hR, inf_idem]
  have hglp : ∀ Q : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ), Q ∘L Q = Q →
      Q ∈ PiT (ContinuousLinearMap.id ℝ (ℝ × ℝ)) := fun Q hQ =>
    ⟨hQ, inferInstance, by rw [ContinuousLinearMap.comp_id]⟩
  have hcompl : IsCompl (LinearMap.ker (P : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))
      (LinearMap.range (P : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))) :=
    (isTopCompl_range_ker_of_comp_self hPP).isCompl.symm
  obtain ⟨-, -, hle'⟩ := hB (ℝ × ℝ) (ℝ × ℝ) (ContinuousLinearMap.id ℝ (ℝ × ℝ))
    isFredholmOp_id P (hglp P hPP) P' (hglp P' hP'P') ⊥ ⊥
    (LinearMap.ker (P : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)))
    (Submodule.closed_of_finiteDimensional _) (bot_inf_eq _) (by rw [bot_sup_eq, hI])
    (Submodule.closed_of_finiteDimensional _) (bot_inf_eq _) (by rw [bot_sup_eq, hI, hR])
    (Submodule.closed_of_finiteDimensional _) (by rw [bot_sup_eq, bot_sup_eq, hI]; exact hcompl)
    P hPP hI.symm (by rw [sup_bot_eq, sup_bot_eq])
  have h := DFunLike.congr_fun hle'.1 ((0 : ℝ), (1 : ℝ))
  simp only [ContinuousLinearMap.comp_apply, hPv, hP'v] at h
  norm_num at h

/-- **A's second conjunct refutes `B_proof`**: for any `P, P'` as in `lemma_6_10_text_reading`, the
complements `X, X', Z` and the projection `P''` of B_proof exist, and B_proof would put `P''` below
both. -/
theorem text_reading_to_not_B_proof : type_of% @Polyfold.lemma_6_10_text_reading → ¬ B_proof := by
  intro hA hB
  obtain ⟨P, P', hP, hP', hno⟩ := hA
  set RP := LinearMap.range (P : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
  set RP' := LinearMap.range (P' : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
  set I := RP ⊓ RP' with hIdef
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl I
  have hCI : C ⊔ I = ⊤ := by rw [sup_comm]; exact hC.sup_eq_top
  have hCI' : C ⊓ I = ⊥ := by rw [inf_comm]; exact hC.inf_eq_bot
  -- `X = R(P) ∩ C`, `X' = R(P') ∩ C`: complements of `I` in `R(P)`, `R(P')`
  set X := RP ⊓ C
  set X' := RP' ⊓ C
  have hXI : X ⊓ I = ⊥ := le_bot_iff.1 (hCI' ▸ inf_le_inf_right I inf_le_right)
  have hX'I : X' ⊓ I = ⊥ := le_bot_iff.1 (hCI' ▸ inf_le_inf_right I inf_le_right)
  have hXs : X ⊔ I = RP := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro v hv
    have hv' : v ∈ C ⊔ I := hCI ▸ Submodule.mem_top
    obtain ⟨c, hc, i, hi, rfl⟩ := Submodule.mem_sup.1 hv'
    have hcP : c ∈ RP := by
      have := RP.sub_mem hv hi.1
      simpa using this
    exact Submodule.add_mem_sup ⟨hcP, hc⟩ hi
  have hX's : X' ⊔ I = RP' := by
    apply le_antisymm (sup_le inf_le_left inf_le_right)
    intro v hv
    have hv' : v ∈ C ⊔ I := hCI ▸ Submodule.mem_top
    obtain ⟨c, hc, i, hi, rfl⟩ := Submodule.mem_sup.1 hv'
    have hcP : c ∈ RP' := by
      have := RP'.sub_mem hv hi.2
      simpa using this
    exact Submodule.add_mem_sup ⟨hcP, hc⟩ hi
  -- `Z` a complement of `X ⊕ X' ⊕ I`
  obtain ⟨Z, hZ⟩ := Submodule.exists_isCompl (X ⊔ X' ⊔ I)
  have hZc : IsCompl Z (X ⊔ X' ⊔ I) := hZ.symm
  -- `I` and `Z ⊕ X ⊕ X'` are complements
  have hcompl : IsCompl I (Z ⊔ X ⊔ X') := by
    constructor
    · rw [Submodule.disjoint_def]
      intro v hvI hv
      obtain ⟨zx, hzx, x', hx', rfl⟩ := Submodule.mem_sup.1 hv
      obtain ⟨z, hz, x, hx, rfl⟩ := Submodule.mem_sup.1 hzx
      have hzS : z ∈ X ⊔ X' ⊔ I := by
        have : z = (z + x + x') - x - x' := by abel
        rw [this]
        refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
        · exact (le_sup_right : I ≤ X ⊔ X' ⊔ I) hvI
        · exact (le_sup_left.trans le_sup_left : X ≤ X ⊔ X' ⊔ I) hx
        · exact (le_sup_right.trans le_sup_left : X' ≤ X ⊔ X' ⊔ I) hx'
      have hz0 : z = 0 := (Submodule.disjoint_def.1 hZc.disjoint) z hz hzS
      subst hz0
      have hx'I : x' ∈ I := by
        refine ⟨?_, hx'.1⟩
        have : x' = (0 + x + x') - x := by abel
        rw [this]
        exact RP.sub_mem hvI.1 hx.1
      have hx'0 : x' = 0 := by
        have h' : x' ∈ X' ⊓ I := ⟨hx', hx'I⟩
        rw [hX'I] at h'
        simpa using h'
      subst hx'0
      have hxI : x ∈ I := by simpa using hvI
      have h' : x ∈ X ⊓ I := ⟨hx, hxI⟩
      rw [hXI] at h'
      simpa using h'
    · rw [codisjoint_iff, eq_top_iff, ← hZc.sup_eq_top]
      refine sup_le ?_ (sup_le (sup_le ?_ ?_) le_sup_left)
      · exact le_sup_left.trans (le_sup_left.trans le_sup_right)
      · exact le_sup_right.trans (le_sup_left.trans le_sup_right)
      · exact le_sup_right.trans le_sup_right
  -- `P''` the projection onto `I` along `Z ⊕ X ⊕ X'`
  have htop : Submodule.IsTopCompl I (Z ⊔ X ⊔ X') :=
    Submodule.IsCompl.isTopCompl_of_finiteDimensional_quotient hcompl
      (Submodule.closed_of_finiteDimensional _)
  have hglp : ∀ Q : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ), IsGoodLeftProj (ContinuousLinearMap.id ℝ (ℝ × ℝ)) Q →
      Q ∈ PiT (ContinuousLinearMap.id ℝ (ℝ × ℝ)) := fun Q hQ =>
    ⟨hQ.isProj, hQ.finite_coker, hQ.range_comp⟩
  have key := hB (ℝ × ℝ) (ℝ × ℝ) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) isFredholmOp_id P
    (hglp P hP) P' (hglp P' hP') X X' Z (Submodule.closed_of_finiteDimensional _) hXI hXs
    (Submodule.closed_of_finiteDimensional _) hX'I hX's (Submodule.closed_of_finiteDimensional _)
    hZc (I.projectionL (Z ⊔ X ⊔ X') htop) (Submodule.isIdempotentElem_projectionL htop)
    (Submodule.range_projectionL htop) (Submodule.ker_projectionL htop)
  exact hno _ (Submodule.isIdempotentElem_projectionL htop) (Submodule.range_projectionL htop)
    ⟨key.2.1, key.2.2⟩

/-- Hence `A ⇒ ¬ B_proof`. -/
theorem A_to_not_B_proof : A → ¬ B_proof := fun hA => text_reading_to_not_B_proof hA.2

#rt_check RoundTrip.V6_11.A_to_B [Polyfold.lemma_6_10, Polyfold.lemma_6_10_text_reading]
#rt_check RoundTrip.V6_11.B_to_lemma_6_10_banach [Polyfold.lemma_6_10,
  Polyfold.lemma_6_10_text_reading]
#rt_check RoundTrip.V6_11.not_B_proof [Polyfold.lemma_6_10, Polyfold.lemma_6_10_text_reading]
#rt_check RoundTrip.V6_11.text_reading_to_not_B_proof [Polyfold.lemma_6_10,
  Polyfold.lemma_6_10_text_reading]
#rt_check RoundTrip.V6_11.A_to_not_B_proof [Polyfold.lemma_6_10,
  Polyfold.lemma_6_10_text_reading]
#rt_overlap RoundTrip.V6_11.B_to_lemma_6_10_banach [Polyfold.lemma_6_10,
  Polyfold.lemma_6_10_text_reading]

end RoundTrip.V6_11
