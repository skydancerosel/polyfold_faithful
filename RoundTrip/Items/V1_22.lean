import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_22

/-! Round trip for V1_22 (Lemma 1.24: `d_C` does not depend on the presentation `T`).

`A` is the conjunction of the types of `Polyfold.quadrantDeg_eq_of_equiv`, `Polyfold.lemma_1_3_4`
and `Polyfold.lemma_1_3_4_dim`.  None has universe parameters (`ScBanach` lives in `Type`).

`B → A`: `lemma_1_3_4` is `B`; `lemma_1_3_4_dim` follows from `B` at `x = T⁻¹ 0`; and the core
`quadrantDeg_eq_of_equiv` (for a level-0 linear equivalence `S` that need not be an
sc-isomorphism) is reduced to `B` by noting that `S` maps `0 × W₀` onto `0 × W'₀`, so it induces a
linear equivalence `e : ℝⁿ ≃ ℝⁿ'` on the half-line coordinates with `(S p).1 = e p.1`; `B` is then
applied to the two presentations `id` and `e × id` of the quadrant in `ℝⁿ ⊕ W`. -/

namespace RoundTrip.V1_22
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.quadrantDeg_eq_of_equiv) ∧ (type_of% @Polyfold.lemma_1_3_4) ∧
    (type_of% @Polyfold.lemma_1_3_4_dim)

theorem A_holds : A :=
  ⟨@Polyfold.quadrantDeg_eq_of_equiv, @Polyfold.lemma_1_3_4, @Polyfold.lemma_1_3_4_dim⟩

theorem A_to_B : A → B := by
  intro hA E C n n' W W' T T' hT hT' x hx
  exact hA.2.1 T T' hT hT' hx

section Glue

variable {n n' : ℕ} {W W' : ScBanach}

local macro "V" n:term:max W:term:max : term => `((((ScBanach.const (Fin $n → ℝ)).prod $W) 0))

/-- A quadrant-preserving linear equivalence kills the half-line coordinates of `0 × W₀`. -/
theorem fst_apply_zero_fst (S : (V n W) ≃L[ℝ] (V n' W'))
    (hS : ∀ q, q ∈ quadrant n W 0 ↔ S q ∈ quadrant n' W' 0) (w : W 0) :
    (S ((0 : Fin n → ℝ), w)).1 = 0 := by
  have h1 : S ((0 : Fin n → ℝ), w) ∈ quadrant n' W' 0 :=
    (hS ((0 : Fin n → ℝ), w)).1 (fun i => by simp)
  have h2 : S ((0 : Fin n → ℝ), -w) ∈ quadrant n' W' 0 :=
    (hS ((0 : Fin n → ℝ), -w)).1 (fun i => by simp)
  have h3 : S ((0 : Fin n → ℝ), -w) = - S ((0 : Fin n → ℝ), w) := by
    rw [← map_neg]; congr 1; ext <;> simp
  rw [h3] at h2
  funext i
  rw [Pi.zero_apply]
  have a := h1 i
  have b := h2 i
  change 0 ≤ -((S ((0 : Fin n → ℝ), w)).1 i) at b
  exact le_antisymm (by linarith) a

/-- The first component of `S p` only depends on `p.1`. -/
theorem fst_apply_eq (S : (V n W) ≃L[ℝ] (V n' W'))
    (hS : ∀ q, q ∈ quadrant n W 0 ↔ S q ∈ quadrant n' W' 0) (p : V n W) :
    (S p).1 = (S (p.1, (0 : W 0))).1 := by
  have : p = (p.1, (0 : W 0)) + ((0 : Fin n → ℝ), p.2) := by ext <;> simp
  conv_lhs => rw [this, map_add]
  rw [Prod.fst_add, fst_apply_zero_fst S hS, add_zero]

theorem symm_quadrant (S : (V n W) ≃L[ℝ] (V n' W'))
    (hS : ∀ q, q ∈ quadrant n W 0 ↔ S q ∈ quadrant n' W' 0) :
    ∀ q, q ∈ quadrant n' W' 0 ↔ S.symm q ∈ quadrant n W 0 := fun q => by
  rw [hS (S.symm q), ContinuousLinearEquiv.apply_symm_apply]

/-- The induced linear equivalence on the half-line coordinates. -/
noncomputable def coordEquiv (S : (V n W) ≃L[ℝ] (V n' W'))
    (hS : ∀ q, q ∈ quadrant n W 0 ↔ S q ∈ quadrant n' W' 0) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n' → ℝ) where
  toFun a := (S (a, (0 : W 0))).1
  map_add' a b := by
    rw [← Prod.fst_add, ← map_add]; congr 2; ext <;> simp
  map_smul' c a := by
    rw [RingHom.id_apply, ← Prod.smul_fst, ← map_smul]; congr 2; ext <;> simp
  invFun b := (S.symm (b, (0 : W' 0))).1
  left_inv a := by
    change (S.symm ((S (a, (0 : W 0))).1, (0 : W' 0))).1 = a
    rw [← fst_apply_eq S.symm (symm_quadrant S hS), ContinuousLinearEquiv.symm_apply_apply]
  right_inv b := by
    change (S ((S.symm (b, (0 : W' 0))).1, (0 : W 0))).1 = b
    rw [← fst_apply_eq S hS, ContinuousLinearEquiv.apply_symm_apply]

/-- The presentation `e × id : ℝⁿ ⊕ W ≅ ℝⁿ' ⊕ W` (an sc-isomorphism since `ℝⁿ` is constant). -/
noncomputable def prodIso (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n' → ℝ)) :
    ScIso ((ScBanach.const (Fin n → ℝ)).prod W) ((ScBanach.const (Fin n' → ℝ)).prod W) where
  lvl m := (LinearEquiv.toContinuousLinearEquiv e).prodCongr (ContinuousLinearEquiv.refl ℝ (W m))
  incl_comm _ _ := rfl

end Glue

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · -- `quadrantDeg_eq_of_equiv` from `B`, via the presentations `id` and `e × id`
    intro n n' W W' S hS p hp
    let e := coordEquiv S hS
    have he : ∀ q : ((ScBanach.const (Fin n → ℝ)).prod W) 0, e q.1 = (S q).1 := fun q =>
      (fst_apply_eq S hS q).symm
    have hC : (ScIso.refl ((ScBanach.const (Fin n → ℝ)).prod W)).lvl 0 ⁻¹' quadrant n W 0 =
        (prodIso (W := W) e).lvl 0 ⁻¹' quadrant n' W 0 := by
      ext q
      change q ∈ quadrant n W 0 ↔ ∀ i, 0 ≤ e q.1 i
      rw [hS q, he q]
      rfl
    have h := hB _ _ n n' W W (ScIso.refl _) (prodIso e) rfl hC p hp
    change (Finset.univ.filter fun i => p.1 i = 0).card =
      (Finset.univ.filter fun i => e p.1 i = 0).card at h
    change (Finset.univ.filter fun i => p.1 i = 0).card =
      (Finset.univ.filter fun i => (S p).1 i = 0).card
    rw [h, he p]
  · intro E C n n' W W' T T' hT hT' x hx
    exact hB E C n n' W W' T T' hT hT' x hx
  · -- `n = n'`: `B` at the point `T⁻¹ 0`, whose index is `n` resp. `n'`
    intro E C n n' W W' T T' hT hT'
    have hx : (T 0).symm 0 ∈ C := by
      rw [hT, Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
      intro i; exact le_rfl
    have h := hB E C n n' W W' T T' hT hT' _ hx
    have hT0 : T 0 ((T 0).symm 0) = 0 := ContinuousLinearEquiv.apply_symm_apply _ _
    have hT'0 : T' 0 ((T 0).symm 0) = 0 := by
      rw [map_zero, map_zero]
    simp only [degIndexWith] at h
    rw [hT0, hT'0, quadrantDeg_zero, quadrantDeg_zero] at h
    exact h

#rt_check RoundTrip.V1_22.A_to_B [Polyfold.quadrantDeg_eq_of_equiv, Polyfold.lemma_1_3_4,
  Polyfold.lemma_1_3_4_dim]
#rt_check RoundTrip.V1_22.B_to_A [Polyfold.quadrantDeg_eq_of_equiv, Polyfold.lemma_1_3_4,
  Polyfold.lemma_1_3_4_dim]
#rt_overlap RoundTrip.V1_22.B_to_A [Polyfold.quadrantDeg_eq_of_equiv, Polyfold.lemma_1_3_4,
  Polyfold.lemma_1_3_4_dim]

end RoundTrip.V1_22
