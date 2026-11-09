import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_41

/-! Round trip for V9_41 (Property (T), 2021 p. 430; 2017 p. 316, and Lemma 9.4.3).

The item lists the definition `OrientedBranchingStructure.PropertyT` (vocabulary) and three
theorems; `A` is the conjunction of their types, universes at `0`:
`OrTangent.eq_or_eq_or_eq_of_isOrientedAt` (of three orientations of one tangent set two
coincide), `exists_ne_isOrientedAt` (`T_yA` has an orientation other than a given one) and the
witness `propertyT_example935B1` (Example 9.3.5's first structure has (T) on `U(0) = ℝ²`).

`B` is the conjunction of (a) the project's `PropertyT V` is the text's (T) on `V` (`PropTB`, the
cases `ε = 1` and `ε = -1` as two implications) and (b) **Lemma 9.4.3**: for every oriented local
branching structure at `x ∈ supp Θ` (`Θ` branched, tame, orientable, `n`-dimensional; sheets
`n`-dimensional with tame induced structure) there is an open `U'(x) ⊆ U(x)` on which (T) holds.

* (a) holds outright (`propertyT_iff`): pure logic.  The project's `PropertyT` is the iff
  "`T_{y₀}(Mᵢ, oᵢ) = T_{y₀}(Mᵢ', oᵢ')` ↔ `T_y(Mᵢ, oᵢ) = T_y(Mᵢ', oᵢ')`"; `B`'s `ε = 1` case is
  its forward half, the `ε = -1` case its backward half by contraposition (no orientation fact
  is needed: "two orientations of one space differ" is literally `≠` on both sides).
* `A ⇒ B` fails at (b): **Lemma 9.4.3 is not in `A`**, nor anywhere in the project (its module
  docstring: "Not formalized: Lemma 9.4.3 (it needs the convergence of the oriented frames ... in a
  chart)").  `A` says nothing about shrinking `U(x)`; `A`'s three theorems concern a single
  tangent set and one example.  We believe (b) is true for the project's notions: its
  `SubmanifoldOrientation` carries a continuity condition (a continuous positive frame field in a
  chart near each point, for `n > 0`), which is what the text's proof by contradiction uses
  (limits of tangent spaces and of the sign `ε` at `x`); proving it is proving Lemma 9.4.3.
* `B ⇒ A` (`B_to_A`): the witness is obtained through (a): `PropTB` for Example 9.3.5's first
  structure on `U(0)` is checked by hand (two different sheets `G⁺⁺, G⁻⁻` meet only at `0`), and
  (a) turns it into the project's `PropertyT`.  The two orientation facts are not consequences
  of `B` (they are not about (T)); they are re-proved outright from non-item lemmas
  (`exists_two_orientations`, `exists_two_orientations_submanifoldTangent`,
  `OrTangent.dim_eq_of_isOrientedAt`), as copies of the project's proofs.
-/

set_option maxSynthPendingDepth 3

namespace RoundTrip.V9_41
open Polyfold Set

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.MPolyfold.OrTangent.eq_or_eq_or_eq_of_isOrientedAt.{0} ∧
  type_of% @Polyfold.MPolyfold.exists_ne_isOrientedAt.{0} ∧
  type_of% @Polyfold.propertyT_example935B1

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.OrTangent.eq_or_eq_or_eq_of_isOrientedAt,
    @Polyfold.MPolyfold.exists_ne_isOrientedAt, Polyfold.propertyT_example935B1⟩

/-! ### (a): the project's `PropertyT` is `PropTB` -/

section PropT
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {x : Obj}

/-- **`B` (a), outright**: the iff of the project is the two implications of `B`. -/
theorem propertyT_iff (Bs : X.OrientedBranchingStructure Θ x) (V : Set Obj) :
    Bs.PropertyT V ↔ PropTB Bs V := by
  constructor
  · intro h i i' y₀ hy₀ y hy h₀ h₁
    have e := h i i' y₀ (by rw [inter_assoc]; exact hy₀) y (by rw [inter_assoc]; exact hy) h₀ h₁
    exact ⟨e.1, fun hne heq => hne (e.2 heq)⟩
  · intro h i i' y₀ hy₀ y hy h₀ h₁
    have e := h i i' y₀ (by rw [← inter_assoc]; exact hy₀) y (by rw [← inter_assoc]; exact hy)
      h₀ h₁
    refine ⟨e.1, fun heq => ?_⟩
    by_contra hne
    exact e.2 hne heq

end PropT

/-! ### Outright re-proofs of the two orientation facts (copies of the project's proofs) -/

section Reproofs
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

theorem eq_or_eq_or_eq_re {y : X} {g₁ g₂ g₃ : MPolyfold.OrTangent P}
    (h₁ : P.IsOrientedAt y g₁) (h₂ : P.IsOrientedAt y g₂) (h₃ : P.IsOrientedAt y g₃)
    (h₁₂ : g₁.carrier = g₂.carrier) (h₁₃ : g₁.carrier = g₃.carrier) :
    g₁ = g₂ ∨ g₁ = g₃ ∨ g₂ = g₃ := by
  have e₂ := MPolyfold.OrTangent.dim_eq_of_isOrientedAt h₁ h₂ h₁₂
  have e₃ := MPolyfold.OrTangent.dim_eq_of_isOrientedAt h₁ h₃ h₁₃
  obtain ⟨n₁, L, O₁⟩ := g₁
  obtain ⟨n₂, L₂, O₂⟩ := g₂
  obtain ⟨n₃, L₃, O₃⟩ := g₃
  simp only at h₁₂ h₁₃ e₂ e₃
  subst h₁₂ h₁₃ e₂ e₃
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  obtain ⟨N, hN, hfin, hr, -⟩ := h₁.isChartOrientation hφ hyφ
  have := hfin
  obtain ⟨A, B, -, hAB⟩ := MPolyfold.exists_two_orientations hφ hyφ h₁.1 hN hr
  rcases (hAB _).1 h₁ with rfl | rfl <;> rcases (hAB _).1 h₂ with rfl | rfl <;>
    rcases (hAB _).1 h₃ with rfl | rfl <;> simp

theorem exists_ne_re {A : Set X} {n : ℕ} (hA : P.IsSubmanifoldOfDim A n) {y : X}
    (hy : y ∈ A) (O : Set (Fin n → P.TangentSpace)) :
    ∃ O', O' ≠ O ∧ P.IsOrientedAt y ⟨n, P.submanifoldTangent A y, O'⟩ := by
  obtain ⟨O₁, O₂, h12, hO⟩ := MPolyfold.exists_two_orientations_submanifoldTangent hA hy
  by_cases h : O = O₁
  · exact ⟨O₂, fun e => h12 (h.symm.trans e.symm), (hO _).2 (Or.inr rfl)⟩
  · exact ⟨O₁, fun e => h e.symm, (hO _).2 (Or.inl rfl)⟩

end Reproofs

/-- `B`'s (T) for Example 9.3.5's first structure on `U(0)`, by hand: two different sheets meet
only at `0`, so `y₀ = y`. -/
theorem propTB_example935B1 (ε : Bool → Bool) :
    PropTB (example935B1 ε 0) (example935B1 ε 0).U := by
  intro i i' y₀ hy₀ y hy _ _
  by_cases h : i = i'
  · subst h
    exact ⟨fun _ => rfl, fun hne => (hne rfl).elim⟩
  · have hne : i.1 ≠ i'.1 := fun e => h (Subtype.ext e)
    rw [eq_zero_of_mem_graph2_beta1 hne hy₀.2.1.1 hy₀.2.2.1,
      eq_zero_of_mem_graph2_beta1 hne hy.2.1.1 hy.2.2.1]
    exact ⟨id, id⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨@eq_or_eq_or_eq_re, @exists_ne_re, fun ε => ?_⟩
  exact (hB.1 _ _ _ _ _ (example935B1 ε 0) _).2 (propTB_example935B1 ε)

/-- What does hold of `B`: its part (a), outright. -/
theorem B_a_holds : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Θ : Obj → ℚ) (x : Obj) (Bs : X.OrientedBranchingStructure Θ x) (V : Set Obj),
    Bs.PropertyT V ↔ PropTB Bs V :=
  fun _ _ _ _ _ _ _ _ _ _ _ Bs V => propertyT_iff Bs V

#rt_check RoundTrip.V9_41.B_to_A [Polyfold.MPolyfold.OrTangent.eq_or_eq_or_eq_of_isOrientedAt,
  Polyfold.MPolyfold.exists_ne_isOrientedAt, Polyfold.propertyT_example935B1]
#rt_overlap RoundTrip.V9_41.B_to_A [Polyfold.MPolyfold.OrTangent.eq_or_eq_or_eq_of_isOrientedAt,
  Polyfold.MPolyfold.exists_ne_isOrientedAt, Polyfold.propertyT_example935B1]
#rt_check RoundTrip.V9_41.B_a_holds [Polyfold.MPolyfold.OrTangent.eq_or_eq_or_eq_of_isOrientedAt,
  Polyfold.MPolyfold.exists_ne_isOrientedAt, Polyfold.propertyT_example935B1]
#print axioms RoundTrip.V9_41.B_to_A

end RoundTrip.V9_41
