import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_42

/-!
Round trip for V4_42 (Lemma 4.19).  `A` is the conjunction of the types of
`Polyfold.isGoodComplement_sup_range`, `Polyfold.lemma_4_19` and
`Polyfold.IsInGoodPositionIn.isInGoodPosition` (no universe parameters): pure linear algebra in an
sc-Banach space `E` with a presentation `T` of `C`, a bounded idempotent `π` with
`(1 − π)E ⊆ E₀` (the minimal subspace at `0`), `N` in good position to `C` inside `πE` with an
ALGEBRAIC complement `Y`; conclusions with algebraic complements (`IsGoodComplement`,
`IsInGoodPosition`).

`A → B` (uses the first conjunct): B's `Z ⊆ C` is a subspace, hence lies in the minimal subspace
`E₀` (coordinates vanish: `z, −z ∈ C`); `π` := the sc-projection onto `T₀O` along `Z` (from B's
sc-splitting `E = T₀O ⊕ Z`, `IsScSplitting.scProj`), so `(1 − π)E = Z`; then
`isGoodComplement_sup_range` gives the `ε`-property of `Y ⊕ Z`.  B asks in addition that
`E = N ⊕ (Y ⊕ Z)` be an **sc**-splitting: `N` is an sc-subspace (it is `Dt(0)E` for a retraction
`t` onto `φ(A ∩ V)` at the smooth point `0`, `ScRetraction.isScSplitting_range_scDeriv`), `Y ⊕ Z`
is closed (`= π⁻¹(Y)`) with dense smooth points, and on every level
`(Y ⊕ Z)_m = Y_m ⊕ Z_m`, `E_m = N_m ⊕ Y_m ⊕ Z_m` (from `E_m = (T₀O)_m ⊕ Z_m` and
`(T₀O)_m = N_m ⊕ Y_m`).  Tameness of the chart is not needed (B's `Z` is given).

`B → A` is not attempted: A is general linear algebra (any `E`, any bounded idempotent `π` with
`(1 − π)E ⊆ E₀`, any subspace `N ⊆ πE` with an algebraic good complement), B only the instance at
a tame chart of an M-polyfold, with `N` the tangent space of a smooth submanifold, `π`'s kernel
given as an sc-complement and the good complement `Y` an sc-complement.
-/

namespace RoundTrip.V4_42
open Polyfold

def A : Prop :=
  type_of% @Polyfold.isGoodComplement_sup_range ∧
    type_of% @Polyfold.lemma_4_19 ∧
    type_of% @Polyfold.IsInGoodPositionIn.isInGoodPosition

theorem A_holds : A :=
  ⟨@Polyfold.isGoodComplement_sup_range, @Polyfold.lemma_4_19,
    @Polyfold.IsInGoodPositionIn.isInGoodPosition⟩

section Glue

variable {E : ScBanach}

/-- `(Y ⊕ Z)_m = Y_m ⊕ Z_m` when `Y ⊆ M` and `E = M ⊕ Z` is an sc-splitting. -/
theorem levelSub_sup {M Y Z : Submodule ℝ (E 0)} (hMZ : E.IsScSplitting M Z) (hYM : Y ≤ M)
    (m : ℕ) : E.levelSub (Y ⊔ Z) m = E.levelSub Y m ⊔ E.levelSub Z m := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (show E.toBase m x ∈ Y ⊔ Z from hx)
    obtain ⟨u, hu, w, hw, rfl⟩ := hMZ.exists_add m x
    have h0 := hMZ.2.2 0
    simp only [ScBanach.levelSub_zero] at h0
    have hd : E.toBase m u - y = z - E.toBase m w := by
      rw [map_add] at hyz
      rw [sub_eq_sub_iff_add_eq_add, add_comm z, hyz, add_comm]
    have hMm : E.toBase m u - y ∈ M := M.sub_mem hu (hYM hy)
    have hZm : E.toBase m u - y ∈ Z := hd ▸ Z.sub_mem hz hw
    have h00 : E.toBase m u - y = 0 := by
      have := h0.disjoint.le_bot ⟨hMm, hZm⟩
      exact (Submodule.mem_bot ℝ).1 this
    have huY : u ∈ E.levelSub Y m := by
      change E.toBase m u ∈ Y
      rw [sub_eq_zero.1 h00]; exact hy
    exact Submodule.add_mem_sup huY hw
  · exact sup_le (Submodule.comap_mono le_sup_left) (Submodule.comap_mono le_sup_right)

/-- **`E = N ⊕ (Y ⊕ Z)` is an sc-splitting** when `E = M ⊕ Z` is one, `N` and `Y` are
sc-subspaces and `M_m = N_m ⊕ Y_m` on every level. -/
theorem isScSplitting_sup {M N Y Z : Submodule ℝ (E 0)} (hMZ : E.IsScSplitting M Z)
    (hN : E.IsScSubspace N) (hY : E.IsScSubspace Y) (hYM : Y ≤ M)
    (hNY : ∀ m : ℕ, E.levelSub N m ⊓ E.levelSub Y m = ⊥ ∧
      E.levelSub N m ⊔ E.levelSub Y m = E.levelSub M m) :
    E.IsScSplitting N (Y ⊔ Z) := by
  set π := hMZ.scProj 0 with hπdef
  have hπM : ∀ x ∈ M, π x = x := fun x hx =>
    (Submodule.projectionL_eq_self_iff _ _).2 (show x ∈ E.levelSub M 0 from hx)
  have hπZ : ∀ x ∈ Z, π x = 0 := fun x hx =>
    (Submodule.projectionL_apply_eq_zero_iff _).2 (show x ∈ E.levelSub Z 0 from hx)
  have hπmem : ∀ x, π x ∈ M := fun x => Submodule.projectionL_apply_mem _ x
  have hsubZ : ∀ x, x - π x ∈ Z := fun x => by
    have := hMZ.sub_proj_mem 0 x
    have h2 : (hMZ.proj 0 x : E 0) = π x := by
      obtain ⟨a, ha, b, hb, rfl⟩ := hMZ.exists_add 0 x
      rw [hMZ.proj_add 0 ha hb, map_add, hπM a ha, hπZ b hb, add_zero]
    rw [← h2]; exact this
  -- `Y ⊕ Z = π⁻¹(Y)`: closed
  have hpre : ((Y ⊔ Z : Submodule ℝ (E 0)) : Set (E 0)) = π ⁻¹' (Y : Set (E 0)) := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_preimage]
    constructor
    · intro hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add, hπM y (hYM hy), hπZ z hz, add_zero]; exact hy
    · intro hx
      have : x = π x + (x - π x) := by abel
      rw [this]; exact Submodule.add_mem_sup hx (hsubZ x)
  have hcl : IsClosed ((Y ⊔ Z : Submodule ℝ (E 0)) : Set (E 0)) := by
    rw [hpre]; exact hY.1.preimage π.continuous
  refine ⟨hN, ⟨hcl, fun m x hx => ?_⟩, fun m => ?_⟩
  · -- density of the smooth points of `(Y ⊕ Z)_m = Y_m ⊕ Z_m`
    rw [SetLike.mem_coe, levelSub_sup hMZ hYM m] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    refine map_mem_closure₂ continuous_add (hY.2 m hy) (hMZ.2.1.2 m hz) ?_
    rintro a ⟨ha, has⟩ b ⟨hb, hbs⟩
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, levelSub_sup hMZ hYM m]; exact Submodule.add_mem_sup ha hb
    · simp only [ScScale.smoothLvl, Set.mem_preimage, map_add, SetLike.mem_coe] at has hbs ⊢
      exact E.smooth.add_mem has hbs
  · rw [levelSub_sup hMZ hYM m]
    obtain ⟨h1, h2⟩ := hNY m
    have hc := hMZ.2.2 m
    refine IsCompl.of_eq ?_ ?_
    · rw [eq_bot_iff]
      rintro x ⟨hxN, hxYZ⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hxYZ
      have hyM : y ∈ E.levelSub M m := h2 ▸ Submodule.mem_sup_right hy
      have hxM : y + z ∈ E.levelSub M m := h2 ▸ Submodule.mem_sup_left hxN
      have hzM : z ∈ E.levelSub M m := by
        have := Submodule.sub_mem _ hxM hyM
        rwa [add_sub_cancel_left] at this
      have hz0 : z = 0 := (Submodule.mem_bot ℝ).1 (hc.disjoint.le_bot ⟨hzM, hz⟩)
      rw [hz0, add_zero] at hxN ⊢
      exact h1 ▸ ⟨hxN, hy⟩
    · rw [← sup_assoc, h2]; exact hc.sup_eq_top

end Glue

theorem A_to_B : A → B := by
  rintro ⟨hsup, -, -⟩ X _ _ _ P S _ _ a V s φ hs himg haSV hφ _ hVφ hφa N M Y Z hN hM hNM hint
    hgc hMZ hZC
  obtain ⟨hYM, hYsc, hNYlev, ε, hε, hgood⟩ := hgc
  obtain ⟨n, Wq, T, hT⟩ := φ.model.isPartialQuadrant
  -- `N` is an sc-subspace: `N = Dt(0)E` for a retraction `t` onto `φ(A ∩ V)`
  let d : P.SubData S := ⟨V, s, hs.1, hs.2.2.1, hs.2.1, hs.2.2.2.1, himg⟩
  have hshrink : d.shrink φ = V := by
    ext x
    simp only [MPolyfold.SubData.shrink, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · exact fun h => h.1.1
    · intro hx
      exact ⟨⟨hx, hVφ hx⟩, hs.2.2.1 hx, hVφ (hs.2.2.1 hx)⟩
  have hQ : IsScRetract φ.model.E φ.model.C (φ.toPartialEquiv '' (S ∩ V)) := by
    have := d.isScRetract_image φ hφ
    rwa [hshrink, Set.inter_comm] at this
  obtain ⟨t, ht⟩ := hQ
  have h0t : (0 : φ.model.E 1) ∈ φ.model.E.lvlSet t.retract 1 := by
    rw [ScBanach.mem_lvlSet, ht, map_zero]; exact ⟨a, haSV, hφa⟩
  have hs0 : (0 : φ.model.E 1) ∈ φ.model.E.smoothLvl 1 := by
    change φ.model.E.toBase 1 0 ∈ (φ.model.E.smooth : Set (φ.model.E 0))
    rw [map_zero]; exact φ.model.E.smooth.zero_mem
  have hNt : N = LinearMap.range (scDeriv t.U t 0 : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) := by
    refine SetLike.coe_injective (hN.trans ?_)
    rw [← ht]; exact tangentSpace_eq_coe_submodule t h0t
  have hNsc : φ.model.E.IsScSubspace N := hNt ▸ (t.isScSplitting_range_scDeriv h0t hs0).1
  -- the projection onto `M` along `Z`
  set π := hMZ.scProj 0 with hπdef
  have hπM : ∀ x ∈ M, π x = x := fun x hx =>
    (Submodule.projectionL_eq_self_iff _ _).2 (show x ∈ φ.model.E.levelSub M 0 from hx)
  have hπZ : ∀ x ∈ Z, π x = 0 := fun x hx =>
    (Submodule.projectionL_apply_eq_zero_iff _).2 (show x ∈ φ.model.E.levelSub Z 0 from hx)
  have hπmem : ∀ x, π x ∈ M := fun x => Submodule.projectionL_apply_mem _ x
  have hπ : ∀ x, π (π x) = π x := fun x => hπM _ (hπmem x)
  have hrange : rangeS π = M := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact hπmem x
    · intro x hx; exact ⟨x, hπM x hx⟩
  have hK : LinearMap.range
      (ContinuousLinearMap.id ℝ (φ.model.E 0) - π : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) = Z := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨u, hu, w, hw, hx⟩ := hMZ.exists_add 0 x
      change x - π x ∈ Z
      have hx' : x = u + w := hx
      rw [hx', map_add, hπM u hu, hπZ w hw, add_zero, add_sub_cancel_left]; exact hw
    · intro z hz
      refine ⟨z, ?_⟩
      change z - π z = z
      rw [hπZ z hz, sub_zero]
  have hZmin : Z ≤ minimalSubspaceWith T 0 := by
    intro z hz
    refine (mem_minimalSubspaceWith T).2 fun i _ => ?_
    have h1 : z ∈ φ.model.C := hZC hz
    have h2 : -z ∈ φ.model.C := hZC (Z.neg_mem hz)
    rw [hT] at h1 h2
    have a1 : 0 ≤ (T 0 z).1 i := h1 i
    have a2 : 0 ≤ (T 0 (-z)).1 i := h2 i
    rw [map_neg] at a2
    have a2' : 0 ≤ -(T 0 z).1 i := a2
    linarith
  have h0 := hNYlev 0
  simp only [ScBanach.levelSub_zero] at h0
  have hgoodC : ∀ x ∈ N, ∀ p ∈ Y, ‖p‖ ≤ ε * ‖x‖ →
      (x ∈ φ.model.C ↔ x + p ∈ φ.model.C) := by
    intro x hx p hp hle
    have h := hgood x hx p hp hle
    have hxM : x ∈ M := hNM hx
    have hxpM : x + p ∈ M := M.add_mem hxM (hYM hp)
    simp only [Set.mem_inter_iff, SetLike.mem_coe] at h
    exact ⟨fun hc => (h.1 ⟨hxM, hc⟩).2, fun hc => (h.2 ⟨hxpM, hc⟩).2⟩
  have hgc := hsup T hT π hπ (hK ▸ hZmin) (hrange ▸ hNM) (hrange ▸ hYM) h0.1
    (hrange ▸ h0.2) hε hgoodC
  rw [hK] at hgc
  have hsplit := isScSplitting_sup hMZ hNsc hYsc hYM hNYlev
  have hpre : (Subtype.val ⁻¹' ((M : Set (φ.model.E 0)) ∩ φ.model.C) : Set N) =
      Subtype.val ⁻¹' φ.model.C := by
    ext ⟨x, hx⟩
    simp only [Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨fun h => h.2, fun h => ⟨hNM hx, h⟩⟩
  refine ⟨⟨hpre ▸ hint, Y ⊔ Z, hsplit, hgc.exists_eps⟩, hsplit, hgc.exists_eps⟩

#rt_check RoundTrip.V4_42.A_to_B [Polyfold.isGoodComplement_sup_range, Polyfold.lemma_4_19,
  Polyfold.IsInGoodPositionIn.isInGoodPosition]
#rt_overlap RoundTrip.V4_42.A_to_B [Polyfold.isGoodComplement_sup_range, Polyfold.lemma_4_19,
  Polyfold.IsInGoodPositionIn.isInGoodPosition]

end RoundTrip.V4_42
