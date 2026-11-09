import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_20

/-! Round trip for V6_20 (Lemma 6.17: `P ∈ Π_S` and `P S|_Y ≅ R(P)` for `S` near `T`).

`A` is the type of `lemma_6_5_1` (universes at `0`); `FredholmOp` and `projRestrict`
(`P S|_Y : Y → R(P)`, `y ↦ P S y`) are definitions (vocabulary).

`A → B` (proved): B is A with the extra hypothesis that `T` is Fredholm (unused); A's
`(e : Y →L R(P)) = projRestrict P S Y` gives B's pointwise `e y = P (S y)`.

`B → A` (proved): A has no Fredholm hypothesis on `T`.  B is applied to a different Fredholm
operator: `T'' = P T|_Y : Y → F` on the Banach space `Y` (closed in `E`), which is injective with
range `R(P T) = R(P)` (closed, finite codimension), hence Fredholm (`isFredholm_of_banach`), with
`P ∈ Π_{T''}`, `ker(P T'') = 0` and complement `⊤`.  B gives `ε'`; for `‖S − T‖ < ε'/(‖P‖+1)`,
`S'' = P S|_Y` satisfies `‖S'' − T''‖ ≤ ‖P‖ ‖S − T‖ < ε'`, so `P ∈ Π_{S''}` (whence
`R(P S) = R(P)`) and `y ↦ P S'' y = P S y` is an isomorphism `⊤ ≅ R(P)`, whence `P S|_Y` is
bijective and (open mapping theorem) a topological isomorphism.
-/

namespace RoundTrip.V6_20
open Polyfold

/-- The project's statement (Lemma 6.17), universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.lemma_6_5_1.{0, 0}

theorem A_holds : A := @Polyfold.lemma_6_5_1.{0, 0}

/-- `A ⇒ B`: B is A with the extra (unused) hypothesis `T.IsFredholm`. -/
theorem A_to_B : A → B := by
  intro hA E F _ _ _ _ _ _ T P Y _hT hP hY
  obtain ⟨ε, hε, h⟩ := hA hP hY
  refine ⟨ε, hε, fun S hS => ?_⟩
  obtain ⟨h1, e, he⟩ := h S hS
  refine ⟨h1, e, fun y => ?_⟩
  have := congrArg Subtype.val (DFunLike.congr_fun he y)
  simpa using this

/-- `B ⇒ A`, by applying B to `T'' = P T|_Y : Y → F` (see the module docstring). -/
theorem B_to_A : B → A := by
  intro hB E F _ _ _ _ _ _ T P hP Y hY
  have : CompleteSpace Y := hY.isClosed'.completeSpace_coe
  have : CompleteSpace (LinearMap.range (P : F →ₗ[ℝ] F)) := hP.isClosed_range.completeSpace_coe
  have hPP : ∀ x : F, P (P x) = P x := fun x => by
    have := congrArg (fun A : F →L[ℝ] F => A x) hP.isProj
    simpa using this
  set T'' : Y →L[ℝ] F := (P ∘L T) ∘L Y.subtypeL with hT''
  have hT''y : ∀ y : Y, T'' y = P (T y) := fun y => rfl
  -- `ker T'' = 0`
  have hker : LinearMap.ker (T'' : Y →ₗ[ℝ] F) = ⊥ := by
    refine (LinearMap.ker_eq_bot').2 fun y hy => ?_
    have hK : (y : E) ∈ LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) := hy
    exact Subtype.ext (Submodule.disjoint_def.1 hY.isCompl.disjoint _ hK y.2)
  -- `R(T'') = R(P)`
  have hrange : LinearMap.range (T'' : Y →ₗ[ℝ] F) = LinearMap.range (P : F →ₗ[ℝ] F) := by
    refine le_antisymm ?_ fun r hr => ?_
    · rintro _ ⟨y, rfl⟩
      exact ⟨T y, rfl⟩
    · rw [← hP.range_comp] at hr
      obtain ⟨x, hx⟩ := hr
      set k := (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).projection Y hY.isCompl x
      have hk : k ∈ LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) :=
        Submodule.projection_apply_mem _ _
      have hy : x - k ∈ Y := Submodule.sub_projection_mem hY.isCompl x
      refine ⟨⟨x - k, hy⟩, ?_⟩
      have hk' : P (T k) = 0 := hk
      have hx' : P (T x) = r := hx
      change P (T (x - k)) = r
      rw [map_sub, map_sub, hk', sub_zero, hx']
  have hT''F : T''.IsFredholm := by
    refine isFredholm_of_banach T'' ?_ ?_ ?_
    · change FiniteDimensional ℝ (LinearMap.ker (T'' : Y →ₗ[ℝ] F))
      rw [hker]
      infer_instance
    · change IsClosed (LinearMap.range (T'' : Y →ₗ[ℝ] F) : Set F)
      rw [hrange]
      exact hP.isClosed_range
    · change Module.Finite ℝ (F ⧸ LinearMap.range (T'' : Y →ₗ[ℝ] F))
      rw [hrange]
      exact hP.finite_coker
  have hPT'' : P ∘L T'' = T'' := by
    ext y
    exact hPP _
  have hgood : IsGoodLeftProj T'' P := ⟨hP.isProj, hP.finite_coker, by rw [hPT'', hrange]⟩
  have hY' : Submodule.IsTopCompl
      (LinearMap.ker ((P.comp T'' : Y →L[ℝ] F) : Y →ₗ[ℝ] F)) (⊤ : Submodule ℝ Y) := by
    have : LinearMap.ker ((P.comp T'' : Y →L[ℝ] F) : Y →ₗ[ℝ] F) = ⊥ := by
      rw [hPT'', hker]
    rw [this]
    refine ⟨isCompl_bot_top, ?_⟩
    have h0 : ∀ y : Y, (⊥ : Submodule ℝ Y).projection ⊤ isCompl_bot_top y = 0 :=
      fun y => (Submodule.mem_bot ℝ).1 (Submodule.projection_apply_mem _ _)
    exact continuous_const.congr fun y => (h0 y).symm
  obtain ⟨ε', hε', hball⟩ := hB T'' P ⊤ hT''F hgood hY'
  refine ⟨ε' / (‖P‖ + 1), by positivity, fun S hS => ?_⟩
  set S'' : Y →L[ℝ] F := (P ∘L S) ∘L Y.subtypeL with hS''
  have hS''y : ∀ y : Y, S'' y = P (S y) := fun y => rfl
  have hdist : ‖S'' - T''‖ < ε' := by
    have h1 : ‖S'' - T''‖ ≤ ‖P‖ * ‖S - T‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
      have h : (S'' - T'') y = P ((S - T) y) := by
        simp [hS''y, hT''y, map_sub]
      calc ‖(S'' - T'') y‖ = ‖P ((S - T) y)‖ := by rw [h]
        _ ≤ ‖P‖ * ‖(S - T) y‖ := P.le_opNorm _
        _ ≤ ‖P‖ * (‖S - T‖ * ‖(y : E)‖) := by gcongr; exact (S - T).le_opNorm _
        _ = ‖P‖ * ‖S - T‖ * ‖y‖ := by rw [mul_assoc]; rfl
    have h2 : ‖S - T‖ * (‖P‖ + 1) < ε' := (lt_div_iff₀ (by positivity)).1 hS
    nlinarith [norm_nonneg (S - T), norm_nonneg P]
  obtain ⟨hgS, e', he'⟩ := hball S'' hdist
  have he'' : ∀ z : (⊤ : Submodule ℝ Y), (e' z : F) = P (S z) := fun z => by
    rw [he' z, hS''y, hPP]
  refine ⟨⟨hP.isProj, hP.finite_coker, ?_⟩, ?_⟩
  · refine le_antisymm ?_ fun r hr => ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨S x, rfl⟩
    · obtain ⟨z, hz⟩ := e'.surjective ⟨r, hr⟩
      refine ⟨(z : Y), ?_⟩
      have := congrArg Subtype.val hz
      rw [he''] at this
      exact this
  · have hinj : LinearMap.ker (projRestrict P S Y : Y →ₗ[ℝ] LinearMap.range (P : F →ₗ[ℝ] F)) = ⊥ := by
      refine (LinearMap.ker_eq_bot').2 fun y hy => ?_
      have h0 : e' ⟨y, Submodule.mem_top⟩ = 0 := by
        apply Subtype.ext
        rw [he'']
        exact congrArg Subtype.val hy
      have := congrArg Subtype.val ((LinearEquiv.map_eq_zero_iff e'.toLinearEquiv).1 h0)
      exact this
    have hsurj : LinearMap.range
        (projRestrict P S Y : Y →ₗ[ℝ] LinearMap.range (P : F →ₗ[ℝ] F)) = ⊤ := by
      refine LinearMap.range_eq_top.2 fun r => ?_
      obtain ⟨z, hz⟩ := e'.surjective r
      refine ⟨(z : Y), Subtype.ext ?_⟩
      rw [← hz, he'']
      rfl
    exact ⟨ContinuousLinearEquiv.ofBijective (projRestrict P S Y) hinj hsurj,
      ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

#rt_check RoundTrip.V6_20.A_to_B [Polyfold.lemma_6_5_1]
#rt_check RoundTrip.V6_20.B_to_A [Polyfold.lemma_6_5_1]
#rt_overlap RoundTrip.V6_20.B_to_A [Polyfold.lemma_6_5_1]

end RoundTrip.V6_20
