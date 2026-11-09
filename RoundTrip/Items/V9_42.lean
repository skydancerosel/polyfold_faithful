import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_42

/-! Round trip for V9_42 (Lemma 9.4.4, 2021 p. 431; 2017: Lemma 9.13: a point of
`K(i, i') = Mᵢ ∩ Mᵢ'` is essential for `K ⊆ Mᵢ` iff it is for `K ⊆ Mᵢ'`).

The item lists the definitions `MPolyfold.SheetGeometry`, `graphSheets`, `graphSheetGeometry`
(vocabulary) and one theorem, so `A` is the type of `lemma_9_4_4_mixed_dim` (no universe
parameters): for `Mᵢ = ℝ` and `Mᵢ' = ℝ²` (models `𝓘(ℝ, ℝ)`, `𝓘(ℝ, Fin 2 → ℝ)`) and
`K = ℝ × 0`, every point is essential for `K ⊆ Mᵢ` and none for `K ⊆ Mᵢ'`: Lemma 9.4.4 fails
for sheets of different dimensions.

In the project Lemma 9.4.4 itself is **not a theorem**: the essential points of the sheets of an
M-polyfold are abstract data of a `SheetGeometry`, and the lemma is its field `ess_comm`
(`ess N (N ∩ N') = ess N' (N' ∩ N)`), assumed.  Its witness `graphSheetGeometry` (graphs over
the first axis of `ℝ²`) computes `ess` in the common chart `z ↦ z 0` of all its sheets, where the
field holds by `inter_comm` (the reference sheet does not enter `graphEss` at all).

`B` states the lemma for the text's notion in the blind local model: `n`-dimensional manifolds
with corners `N` with a `C^∞` immersion `j : N → F` (a Banach space) that is an embedding, all of
the same dimension `n`, and `K^e` computed with the project's `essentialSet` in `N`.

* `A ⇒ B` fails: `A` (a counterexample for *different* dimensions) says nothing about sheets of
  equal dimension, and nothing in the project proves Lemma 9.4.4 for an actual manifold structure
  on the sheets (no sheet carries one; `SheetGeometry` takes the lemma as data).  We believe `B`
  is true: if `z_k ∈ K` are full points for `K ⊆ Nᵢ` (`span TC_{Nᵢ}(jᵢ⁻¹K) = ℝⁿ`), then
  `T_{z_k}Mᵢ = Djᵢ(ℝⁿ) ⊆ span TC_F(K, z_k) ⊆ Djᵢ'(span TC_{Nᵢ'}(jᵢ'⁻¹K)) ⊆ T_{z_k}Mᵢ'` (the
  middle inclusion uses that `Djᵢ'` is injective, hence bounded below, and `jᵢ'` is an embedding);
  equal dimensions force equality, so `z_k` are full points for `K ⊆ Nᵢ'`, and
  `jᵢ'⁻¹(z_k) → jᵢ'⁻¹(z)`.  Formalizing this is proving the lemma (left to the reader by the
  text), not glue.
* `B ⇒ A` (`B_to_A`) is vacuous: `A`'s counterexample is re-proved outright (`mixed_dim_re`, a
  copy of the project's proof from non-item lemmas); `B` (equal dimensions) does not bear on it.
* `B_of_imp`: `B`'s two equalities follow from its implication (applied to `(i, i')` and
  `(i', i)`), so `B`'s content is the implication.
-/

namespace RoundTrip.V9_42
open Polyfold Set
open scoped Manifold

/-- The project's statement. -/
def A : Prop := type_of% @Polyfold.lemma_9_4_4_mixed_dim

theorem A_holds : A := Polyfold.lemma_9_4_4_mixed_dim

/-- `A`'s counterexample, re-proved outright (a copy of the project's proof). -/
theorem mixed_dim_re :
    essentialSet 𝓘(ℝ, ℝ) (univ : Set ℝ) = univ ∧
      essentialSet 𝓘(ℝ, Fin 2 → ℝ) (lineH : Set (Fin 2 → ℝ)) = ∅ ∧
      range (fun s : ℝ => (Pi.single 0 s : Fin 2 → ℝ)) = lineH := by
  refine ⟨?_, ?_, ?_⟩
  · refine eq_univ_of_forall fun s => ⟨mem_univ s, fun _ => s, fun _ => ⟨mem_univ s, ?_⟩,
      tendsto_const_nhds⟩
    rw [relTangent_self, tangentConeAt_univ, Submodule.span_univ]
  · refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨-, u, hu, -⟩ := hz
    have h := (hu 0).2
    rw [relTangent_self] at h
    have hle : Submodule.span ℝ (tangentConeAt ℝ (lineH : Set (Fin 2 → ℝ)) (u 0)) ≤ lineH :=
      Submodule.span_le.2 (tangentConeAt_subset_submodule isClosed_lineH (hu 0).1)
    rw [h] at hle
    exact lineH_ne_top (top_le_iff.1 hle)
  · ext v
    simp only [mem_range, SetLike.mem_coe, mem_lineH]
    constructor
    · rintro ⟨s, rfl⟩
      simp
    · intro hv
      refine ⟨v 0, ?_⟩
      funext i
      fin_cases i
      · simp
      · simp [hv]

/-- `B ⇒ A`, vacuously: `A` is re-proved outright. -/
theorem B_to_A : B → A := fun _ => mixed_dim_re

/-- `B`'s essential points lie in `K`. -/
theorem ess_subset {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : SheetB n F) (K : Set F) : S.ess K ⊆ K := by
  rintro _ ⟨w, hw, rfl⟩
  exact hw.1

/-- **`B` reduces to its implication**: the two equalities follow from it for `(i, i')` and
`(i', i)` (`K(i, i') = K(i', i)`). -/
theorem B_of_imp
    (h : ∀ (n : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (x : F)
      (L : LocalStrB n F x) (i i' : L.ι),
      ∀ z ∈ L.K i i', z ∈ (L.S i).ess (L.K i i') → z ∈ (L.S i').ess (L.K i i')) : B := by
  intro n F _ _ _ x L i i'
  have hK : L.K i' i = L.K i i' := inter_comm _ _
  have h1 := h n F x L i i'
  have h2 := h n F x L i' i
  rw [hK] at h2
  have heq : (L.S i).ess (L.K i i') = (L.S i').ess (L.K i i') :=
    Subset.antisymm (fun z hz => h1 z (ess_subset _ _ hz) hz)
      (fun z hz => h2 z (ess_subset _ _ hz) hz)
  exact ⟨h1, heq, by rw [heq]⟩

#rt_check RoundTrip.V9_42.B_to_A [Polyfold.lemma_9_4_4_mixed_dim]
#rt_overlap RoundTrip.V9_42.B_to_A [Polyfold.lemma_9_4_4_mixed_dim]
#rt_check RoundTrip.V9_42.B_of_imp [Polyfold.lemma_9_4_4_mixed_dim]
#print axioms RoundTrip.V9_42.B_to_A

end RoundTrip.V9_42
