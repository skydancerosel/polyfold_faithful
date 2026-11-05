import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_10

/-! Round trip for V1_10 (Definition 1.11: partial quadrants and the tuples `(U, C, E)`).

`A` is the conjunction of the types of the theorems in the item's declaration list:
`quadrant_convex`, `quadrant_isClosed`, `lvlSet_quadrant`, `IsPartialQuadrant.convex`,
`IsPartialQuadrant.isClosed`, `IsPartialQuadrant.uniqueDiffWithinAt_lvlSet`,
`isPartialQuadrant_univ` (the definitions `quadrant`, `IsPartialQuadrant`, `IsRelOpenInQuadrant`
are vocabulary).  None has universe parameters (`ScBanach` lives in `Type`).

`B` says the project's `IsPartialQuadrant` / `IsRelOpenInQuadrant` are the text's notions.  The two
definitions differ only in presentation:
* the project writes `C = T₀⁻¹([0,∞)ⁿ ⊕ W₀)`, the text `T₀(C) = [0,∞)ⁿ ⊕ W₀` together with
  "`C` closed convex"; since `T₀` is bijective the first two agree, and closedness/convexity follow
  (these are exactly `A`'s `IsPartialQuadrant.isClosed` / `.convex`, used in `A_to_B`);
* the project writes `U = O ∩ C` with `O ⊆ E₀` open, the text "`U ⊆ C` open in the subspace
  topology of `C`"; these agree by the definition of the subspace topology. -/

namespace RoundTrip.V1_10
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.quadrant_convex) ∧ (type_of% @Polyfold.quadrant_isClosed) ∧
    (type_of% @Polyfold.lvlSet_quadrant) ∧ (type_of% @Polyfold.IsPartialQuadrant.convex) ∧
    (type_of% @Polyfold.IsPartialQuadrant.isClosed) ∧
    (type_of% @Polyfold.IsPartialQuadrant.uniqueDiffWithinAt_lvlSet) ∧
    (type_of% @Polyfold.isPartialQuadrant_univ)

theorem A_holds : A :=
  ⟨@Polyfold.quadrant_convex, @Polyfold.quadrant_isClosed, @Polyfold.lvlSet_quadrant,
    @Polyfold.IsPartialQuadrant.convex, @Polyfold.IsPartialQuadrant.isClosed,
    @Polyfold.IsPartialQuadrant.uniqueDiffWithinAt_lvlSet, @Polyfold.isPartialQuadrant_univ⟩

/-- The image/preimage forms of "`T` maps `C` onto the quadrant" agree (`T₀` is bijective). -/
theorem image_eq_iff {E : ScBanach} {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (C : Set (E.lvl 0)) :
    (T.lvl 0) '' C = {p | ∀ i, 0 ≤ p.1 i} ↔ C = T 0 ⁻¹' quadrant n W 0 := by
  constructor
  · intro h
    rw [← Set.preimage_image_eq C (T.lvl 0).injective, h]
    rfl
  · rintro rfl
    exact Set.image_preimage_eq _ (T.lvl 0).surjective

/-- "`U = O ∩ C` with `O` open" is "`U ⊆ C` open in the subspace topology of `C`". -/
theorem relOpen_iff {X : Type} [TopologicalSpace X] (C U : Set X) :
    (∃ O : Set X, IsOpen O ∧ U = O ∩ C) ↔ U ⊆ C ∧ IsOpen (Subtype.val ⁻¹' U : Set C) := by
  constructor
  · rintro ⟨O, hO, rfl⟩
    refine ⟨inter_subset_right, ?_⟩
    have : (Subtype.val ⁻¹' (O ∩ C) : Set C) = Subtype.val ⁻¹' O := by
      ext ⟨x, hx⟩; simp
    rw [this]
    exact hO.preimage continuous_subtype_val
  · rintro ⟨hUC, hU⟩
    obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 hU
    refine ⟨O, hO, ?_⟩
    ext x
    constructor
    · intro hx
      have hxC := hUC hx
      have : (⟨x, hxC⟩ : C) ∈ (Subtype.val ⁻¹' U : Set C) := hx
      rw [← hOU] at this
      exact ⟨this, hxC⟩
    · rintro ⟨hxO, hxC⟩
      have : (⟨x, hxC⟩ : C) ∈ (Subtype.val ⁻¹' O : Set C) := hxO
      rw [hOU] at this
      exact this

theorem A_to_B : A → B := by
  intro hA
  have hPQ : ∀ (E : ScBanach) (C : Set (E.lvl 0)), IsPartialQuadrant E C ↔
      IsPartialQuadrantText E C := by
    intro E C
    constructor
    · intro hC
      refine ⟨hA.2.2.2.2.1 hC, hA.2.2.2.1 hC, ?_⟩
      obtain ⟨n, W, T, hT⟩ := hC
      exact ⟨n, W, T, (image_eq_iff T C).2 hT⟩
    · rintro ⟨-, -, n, W, T, hT⟩
      exact ⟨n, W, T, (image_eq_iff T C).1 hT⟩
  refine ⟨hPQ, fun E C U => ?_⟩
  constructor
  · rintro ⟨hC, hU⟩
    exact ⟨(hPQ E C).1 hC, (relOpen_iff C U).1 hU⟩
  · rintro ⟨hC, hU⟩
    exact ⟨(hPQ E C).2 hC, (relOpen_iff C U).2 hU⟩

/-- `lvlSet_quadrant`, re-proved outright (it is one of `A`'s conjuncts, so the project's
`IsPartialQuadrant.lvlSet_eq` / `interior_lvlSet_nonempty`, which use it, are avoided below). -/
theorem lvlSet_quadrant' (n : ℕ) (W : ScBanach) (m : ℕ) :
    ((ScBanach.const (Fin n → ℝ)).prod W).lvlSet (quadrant n W 0) m = quadrant n W m := by
  ext p
  rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase]
  change (∀ i, 0 ≤ (ScBanach.const (Fin n → ℝ)).toBase m p.1 i) ↔ ∀ i, 0 ≤ p.1 i
  rw [ScBanach.const_toBase]

/-- The level-`m` part of a partial quadrant has nonempty interior (re-proved without
`lvlSet_quadrant`). -/
theorem interior_lvlSet_nonempty' {E : ScBanach} {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (m : ℕ) :
    (interior (E.lvlSet (T 0 ⁻¹' quadrant n W 0) m)).Nonempty := by
  have h : E.lvlSet (T 0 ⁻¹' quadrant n W 0) m = T m ⁻¹' quadrant n W m := by
    ext x
    rw [ScBanach.mem_lvlSet, mem_preimage, mem_preimage, ← T.toBase_comm,
      ← ScBanach.mem_lvlSet, lvlSet_quadrant']
  rw [h, ← (T m).isOpenMap.preimage_interior_eq_interior_preimage (T m).continuous]
  exact (quadrant_interior_nonempty n W m).preimage (T m).surjective

/-- `B → A`.  Only `IsPartialQuadrant.convex`, `.isClosed` and (through convexity)
`.uniqueDiffWithinAt_lvlSet` follow from `B`; the other four conjuncts are facts about the model
quadrant `[0,∞)ⁿ ⊕ W` and the trivial partial quadrant `C = E`, re-proved here outright (`B`, a
characterization of the definitions, says nothing about them). -/
theorem B_to_A : B → A := by
  intro hB
  have hconv : ∀ {E : ScBanach} {C : Set (E.lvl 0)}, IsPartialQuadrant E C → Convex ℝ C :=
    fun {E C} hC => ((hB.1 E C).1 hC).2.1
  refine ⟨?_, ?_, ?_, hconv, fun {E C} hC => ((hB.1 E C).1 hC).1, ?_, ?_⟩
  · -- quadrant_convex (outright)
    intro n W m p hp q hq a b ha hb _ i
    exact add_nonneg (mul_nonneg ha (hp i)) (mul_nonneg hb (hq i))
  · -- quadrant_isClosed (outright)
    intro n W m
    have : quadrant n W m = ⋂ i, {p : (Fin n → ℝ) × W m | 0 ≤ p.1 i} := Set.ofPred_forall _
    rw [this]
    exact isClosed_iInter fun i =>
      isClosed_le continuous_const ((continuous_apply i).comp continuous_fst)
  · -- lvlSet_quadrant (outright)
    exact lvlSet_quadrant'
  · -- uniqueDiffWithinAt_lvlSet: convexity of `C` from `B`, propagated to the levels
    intro E C hC m x hx
    have hc := E.convex_lvlSet (hconv hC) m
    obtain ⟨n, W, T, rfl⟩ := hC
    exact uniqueDiffWithinAt_convex hc (interior_lvlSet_nonempty' T m) (subset_closure hx)
  · -- isPartialQuadrant_univ (outright)
    intro E
    refine ⟨0, E, ?_, ?_⟩
    · exact
        { lvl := fun m => (ContinuousLinearEquiv.uniqueProd ℝ (E m) (Fin 0 → ℝ)).symm
          incl_comm := fun m x => Prod.ext (funext fun i => i.elim0) rfl }
    · ext x; simp [quadrant]

#rt_check RoundTrip.V1_10.A_to_B [Polyfold.quadrant_convex, Polyfold.quadrant_isClosed,
  Polyfold.lvlSet_quadrant, Polyfold.IsPartialQuadrant.convex, Polyfold.IsPartialQuadrant.isClosed,
  Polyfold.IsPartialQuadrant.uniqueDiffWithinAt_lvlSet, Polyfold.isPartialQuadrant_univ]
#rt_check RoundTrip.V1_10.B_to_A [Polyfold.quadrant_convex, Polyfold.quadrant_isClosed,
  Polyfold.lvlSet_quadrant, Polyfold.IsPartialQuadrant.convex, Polyfold.IsPartialQuadrant.isClosed,
  Polyfold.IsPartialQuadrant.uniqueDiffWithinAt_lvlSet, Polyfold.isPartialQuadrant_univ]
#rt_overlap RoundTrip.V1_10.B_to_A [Polyfold.quadrant_convex, Polyfold.quadrant_isClosed,
  Polyfold.lvlSet_quadrant, Polyfold.IsPartialQuadrant.convex, Polyfold.IsPartialQuadrant.isClosed,
  Polyfold.IsPartialQuadrant.uniqueDiffWithinAt_lvlSet, Polyfold.isPartialQuadrant_univ]

end RoundTrip.V1_10
