import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_47

/-!
Round trip for V4_47 (proof of Theorem 4.22 (3): an sc-complement inside `T^R_aO`).  `A` is the
conjunction of the types of `Polyfold.exists_scComplement_le` and
`Polyfold.isGeneralPositionRetractAt_of_sup_eq_top` (no universe parameters).

B is the step in an M-polyfold chart: `X` tame, `A` a smooth submanifold with data `(V, s)`,
`V ⊆ dom φ`, `φ` a chart on a tame retract with presentation `T`, `a ∈ A ∩ V`, `N = T_z(φ(A ∩ V))`,
`M = T_zO`, and `N + E_0 = E`; conclusions `M = N + (E_0 ∩ M) = N + T^R_zO` and an sc-complement of
`N` in `M` inside `T^R_zO = M ∩ E_z`.

`A_to_B` (from the second conjunct): the data `(V, s)` is the project's `SubmanifoldData` with
`W = V` (since `V ⊆ dom φ`); `exists_chartRetraction` gives the sc⁺-retraction `t` onto
`φ(A ∩ V)`, so `N = range Dt(z)` is finite-dimensional and smooth (Lemma 4.7), `z` is smooth, and a
tame retraction `R` onto `O` (B's `IsTameRetract`) is tame for the presentation `T`; then
`isGeneralPositionRetractAt_of_sup_eq_top` gives the sc-complement `B' ⊆ M ∩ E_z` with
`M = N ⊕ B'` levelwise, and the two submodule equalities follow by the modular law.

`B → A` fails: both conjuncts of `A` are general (any sc-space, any sc-retract `Q`, any
finite-dimensional smooth `N` and sc-subspace `TR`), while `B` only speaks of tangent spaces of
images of sc⁺-retractions in charts of M-polyfolds.
-/

namespace RoundTrip.V4_47
open Polyfold

def A : Prop :=
  type_of% @Polyfold.exists_scComplement_le ∧
    type_of% @Polyfold.isGeneralPositionRetractAt_of_sup_eq_top

theorem A_holds : A :=
  ⟨@Polyfold.exists_scComplement_le, @Polyfold.isGeneralPositionRetractAt_of_sup_eq_top⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- The project's sc⁺-retractions on open sets are B's (copied from V4_9/V4_33). -/
theorem retractionOn_iff (P : MPolyfold X) (r : X → X) (V : Set X) :
    P.IsScPlusRetractionOn r V ↔ IsScPlusRetractionOnB P r V := by
  constructor
  · intro h
    refine ⟨h.isScSmoothOn.isOpen, h.isScSmoothOn, h.mapsTo, h.idem, h.mem_levelSet,
      fun g hg => ?_⟩
    rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
    · exact MPolyfold.IsScSmoothOn.of_exists_charts h.isScSmoothOn.isOpen
        (fun y _ => (IsEmpty.false y).elim) (fun y _ => (IsEmpty.false y).elim)
    · refine (h.isScSmoothOn_one (g x)).congr fun y hy => ?_
      change P.toLevelOne (g x) (r y) = g y
      rw [← hg y hy, MPolyfold.toLevelOne_levelVal]
  · rintro ⟨-, h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, fun x₀ =>
      h5 _ fun x hx => MPolyfold.levelVal_toLevelOne x₀ (h4 x hx)⟩

end Glue

theorem A_to_B : A → B := by
  rintro ⟨-, hgen⟩ X _ _ _ P S _ _ V s φ n Wq T hs himg hφ htr hVφ hT a z N M ⟨haS, haV⟩ hz hN hM
    hsup
  -- the data of Definition 4.13, with `W = V`
  let d : P.SubmanifoldData S := ⟨V, s, hs.1, (retractionOn_iff P s V).2 hs, himg⟩
  have hshrink : d.toSubData.shrink φ = V := by
    ext x
    simp only [MPolyfold.SubData.shrink, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · exact fun h => h.1.1
    · intro hx
      exact ⟨⟨hx, hVφ hx⟩, hs.2.2.1 hx, hVφ (hs.2.2.1 hx)⟩
  have haφ : a ∈ φ.source := hVφ haV
  -- the tame retraction onto `O`
  obtain ⟨R, hR, hRt⟩ := htr
  have hRT := hRt n Wq T hT
  -- the sc⁺ chart retraction onto `φ(A ∩ V)`
  obtain ⟨t, ht, htp, -⟩ := d.exists_chartRetraction hφ (P.levelMk 1 a (d.mem_levelSet_one haS haV))
    R hR
  have ht' : t.retract = φ '' (S ∩ V) := by rw [ht, hshrink, Set.inter_comm]
  have htR : t.retract ⊆ R.retract := by
    rw [ht, hR]; exact φ.image_subset_model fun _ hy => d.toSubData.shrink_subset_source φ hy.1
  have hzt : z ∈ φ.model.E.lvlSet t.retract 1 := by
    rw [ScBanach.mem_lvlSet, ht', hz]; exact ⟨a, ⟨haS, haV⟩, rfl⟩
  have hzs : z ∈ φ.model.E.smoothLvl 1 := by
    change φ.model.E.toBase 1 z ∈ (φ.model.E.smooth : Set (φ.model.E 0))
    rw [hz]; exact d.apply_mem_smooth hφ haS haV haφ
  have hNt : N = LinearMap.range (scDeriv t.U t z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) := by
    refine SetLike.coe_injective (hN.trans ?_)
    rw [← ht']; exact tangentSpace_eq_coe_submodule t hzt
  have : FiniteDimensional ℝ N := by rw [hNt]; exact lemma_4_1_7_ii htp hzt
  have hNs : N ≤ φ.model.E.smooth :=
    (φ.model.E.proposition_1_1_7_iff N).1 (hNt ▸ (t.isScSplitting_range_scDeriv hzt hzs).1)
  have hN' : (N : Set (φ.model.E 0)) = tangentSpace φ.model.E φ.model.C t.retract z := by
    rw [ht']; exact hN
  -- the second conjunct of `A`
  obtain ⟨N', M', B', hN'', hM', hB'le, hB'sc, hsplit⟩ :=
    hgen T hT hRT t.isScRetract htR hzt hzs hN' hNs hsup
  have hNN : N' = N := SetLike.coe_injective (hN''.trans hN'.symm)
  have hMM : M' = M := SetLike.coe_injective (hM'.trans (by rw [hR]; exact hM.symm))
  subst hNN hMM
  have hMNB : M' = N' ⊔ B' := by
    have := (hsplit 0).2
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero, ScBanach.levelSub_zero, eq_comm] at this
  have hNM : N' ≤ M' := hMNB ▸ le_sup_left
  have h1 : M' = N' ⊔ (minimalSubspaceWith T 0 ⊓ M') := by
    refine le_antisymm (fun v hv => ?_) (sup_le hNM inf_le_right)
    have hv' : v ∈ N' ⊔ minimalSubspaceWith T 0 := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨u, hu, k, hk, rfl⟩ := Submodule.mem_sup.1 hv'
    refine Submodule.add_mem_sup hu ⟨hk, ?_⟩
    have : k = (u + k) - u := by abel
    rw [this]
    exact M'.sub_mem hv (hNM hu)
  have h2 : N' ⊔ (M' ⊓ minimalSubspaceWith T (φ.model.E.toBase 1 z)) = M' :=
    le_antisymm (sup_le hNM inf_le_left) (le_of_eq_of_le hMNB (sup_le_sup_left hB'le _))
  refine ⟨h1, by rw [← h1, h2], B', hB'sc, hB'le, fun m => ⟨(hsplit m).1.eq_bot, (hsplit m).2⟩⟩

#rt_check RoundTrip.V4_47.A_to_B [Polyfold.exists_scComplement_le,
  Polyfold.isGeneralPositionRetractAt_of_sup_eq_top]

end RoundTrip.V4_47
