import Polyfold.Chapter4.ScPlus
import Polyfold.Chapter3.GlobalIFTCenter
import Polyfold.Chapter3.LinearizationCharts

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I: **re-centring of
charts and of strong bundle charts at a smooth point**, used without comment in Theorem 4.2 (ii)
("every point `x ∈ X` is contained in a tame sc-smooth polyfold chart `(V, ψ, (O, C, E))` satisfying
`ψ(x) = 0`"), in the proof of Theorem 4.18 and in Lemma 5.11 (a strong bundle chart centred at `x`);
Definition 2.33 (the partial quadrant `C_e`) *(book 2017: Theorem 4.1, Theorem 4.2, Lemma 5.3;
Definition 2.16; see `BookConcordance.md`)*.

# Re-centring of charts

## The text, paraphrased

(Definition 2.33) For `C = [0,∞)ⁿ ⊕ W` and `e ∈ C`, `C_e = ⋂_{i ∈ I(e)} H_i` is the partial quadrant
associated with `e` and `E_e = ⋂_{i ∈ I(e)} E_i` the minimal subspace.  (Theorem 4.2 (ii), proof of
Theorem 4.18, Lemma 5.11) Charts `ψ` with `ψ(x) = 0` at a given point; the text never says how they
are obtained from a chart `φ` of the atlas.

## What is formalized

* **The partial quadrant `C_e`** for a presentation `T : E ≅ ℝⁿ ⊕ W` of `C`:
  `recentreIso T e : E ≅ ℝ^{I(e)} ⊕ (ℝ^{rest} ⊕ W)` (reordering the half-line coordinates) with
  `partialQuadrantAtWith_eq_preimage` and `isPartialQuadrant_partialQuadrantAtWith` (`C_e` is a
  partial quadrant); `image_sub_partialQuadrantAtWith` (`C_e − e = C_e`); the neighbourhood
  `recentreNbhd T e = G(e)` of `e` with `recentreNbhd_inter_eq` (`C ∩ G(e) = C_e ∩ G(e)`).
* **Tameness data are unchanged near `e`**: `degIndexWith_recentreIso`, `degIndex_sub_recentre`
  (`d_{C_e}(v − e) = d_C(v)` for `v ∈ G(e) ∩ C`), `minimalSubspaceWith_recentreIso` (the minimal
  subspaces of `v − e` for `T_e` and of `v` for `T` agree), `partialQuadrantAtWith_recentreIso`
  (likewise `C_v`).
* Translations: `isScSmooth_add_const`, `isScSmooth_sub_const` (by a smooth vector), and
  `isScDiffeoQuadrant_translate`: `v ↦ v − e` is an sc-diffeomorphism of a relatively open
  `U ⊆ G(e) ∩ C` onto the relatively open `U − e ⊆ C_e` (`relOpen_translate`).
* `ScRetraction.restrictIn` (a retraction with domain `U ∩ r⁻¹(W) ∩ W ⊆ W`; tame if `r` is,
  `ScRetraction.IsTameWith.restrictIn`, `ScRetraction.restrictIn_isTame`),
  `isScRetract_recentre`, `isTameRetract_recentre` (**a tame retract stays tame**: the transported
  retraction `r(u + e) − e`, `IsScDiffeoQuadrant.isTame_transport`).
* **`MChart.recentre`**: for a chart `φ : V → O ⊆ C`, a presentation `T` of `C` and a smooth `e ∈ C`,
  the chart `φ_e = φ − e` on `V ∩ φ⁻¹(G(e))`, modelled on the retract `(O ∩ G(e)) − e` in the
  partial quadrant `C_e` (`MChart.restrict` followed by `MChart.compDiffeo`), with
  `MChart.recentre_isChart` (**a chart of the M-polyfold**, compatible with the atlas),
  `recentre_apply_self` (`φ_e(x) = 0` for `e = φ(x)`), `MChart.isTameRetract_recentre` (tame model)
  and `MChart.chartDegIndex_recentre`; `MPolyfold.exists_centredChart`,
  `MPolyfold.IsTame.exists_centredChart` (every smooth point lies in a (tame) chart centred at it).
* **`StrongBundleChart.recentre`**: over `φ_e`, the strong bundle retraction
  `R_e(u, h) = (r(u + e) − e, Γ(u + e, h))` on `(U ∩ r⁻¹(G) ∩ G − e) ◁ F`
  (`IsStrongBundleRetraction.restrictIn`, `IsStrongBundleRetraction.translate`) and
  `Φ_e(y) = (Φ(y)₁ − e, Φ(y)₂)`; `StrongBundleChart.Compatible.recentre` (compatibility on `[0]` and
  `[1]` passes to `c_e`) and `StrongBundle.IsChart.recentre`: **`B.IsChart` for the re-centred
  chart**; `StrongBundle.IsChart.exists_centred`.

## What the text leaves implicit, and the choices made

* The re-centred chart exists only at **smooth** points: translation by `e` is sc⁰ only if `e ∈ E_∞`
  (it must map `E_m` into `E_m` for every `m`).  Theorem 4.2 (ii) needs it at every point, which is
  smooth there because `X₀ = X_∞`.
* `C − e` is not a partial quadrant (it is not a cone at `0` unless `e ∈ C ∩ −C`); the model of the
  re-centred chart lives in `C_e`, which agrees with `C` only near `e` (on `G(e)`), so the chart
  must be restricted to `φ⁻¹(G(e))`.  That `C_e` is a partial quadrant and `C_e − e = C_e` are
  asserted in Definition 2.33 without proof; the presentation of `C_e` reorders the coordinates
  (`ℝ^{I(e)}` first, the others joined to `W`).
* Strong bundle charts are re-centred by translating the base only; the fibre coordinate is
  unchanged.  The translation `(u, h) ↦ (u − e, h)` is sc-smooth on `E ⊕ F` and on `E ⊕ F¹` because
  `(e, 0)` is smooth in both.
* Everything is stated for a given presentation `T` of `C` (as `Tame.lean` does); tameness is for all
  presentations (`ScRetraction.IsTame`), so it does not depend on the choice.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

/-! ### The partial quadrant `C_e` and the neighbourhood on which it agrees with `C` -/

section Presentation

variable {E : ScBanach} {n : ℕ} {W : ScBanach} (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))

/-- The neighbourhood `G(e) = {v | λ_i(v) > 0 for every i with λ_i(e) ≠ 0}` of `e ∈ C` (presentation
`T`), on which the partial quadrant `C_e` of Definition 2.33 agrees with `C`
(`recentreNbhd_inter_eq`). -/
def recentreNbhd (e : E 0) : Set (E 0) := {v | ∀ i, (T 0 e).1 i ≠ 0 → 0 < (T 0 v).1 i}

lemma isOpen_recentreNbhd (e : E 0) : IsOpen (recentreNbhd T e) := by
  have : recentreNbhd T e = ⋂ i : {i : Fin n // (T 0 e).1 i ≠ 0}, {v | 0 < (T 0 v).1 i.1} := by
    ext v
    simp only [recentreNbhd, mem_iInter, Subtype.forall]; rfl
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_coord T i.1)

variable {T} {C : Set (E 0)}

lemma mem_recentreNbhd (hT : C = T 0 ⁻¹' quadrant n W 0) {e : E 0} (heC : e ∈ C) :
    e ∈ recentreNbhd T e := fun i hi => lt_of_le_of_ne (coord_nonneg hT heC i) (Ne.symm hi)

/-- On `G(e)`, the partial quadrants `C` and `C_e` agree ("`C_e` agrees with `C` near `e`"). -/
theorem recentreNbhd_inter_eq (hT : C = T 0 ⁻¹' quadrant n W 0) (e : E 0) :
    recentreNbhd T e ∩ C = recentreNbhd T e ∩ partialQuadrantAtWith T e := by
  ext v
  constructor
  · rintro ⟨hG, hv⟩
    exact ⟨hG, fun i _ => coord_nonneg hT hv i⟩
  · rintro ⟨hG, hv⟩
    refine ⟨hG, ?_⟩
    rw [hT]
    intro i
    by_cases hi : (T 0 e).1 i = 0
    · exact hv i hi
    · exact (hG i hi).le

variable (T) in
/-- `C_e` is invariant under translation by `e`: `v + e ∈ C_e ↔ v ∈ C_e`. -/
lemma add_mem_partialQuadrantAtWith_iff (e v : E 0) :
    v + e ∈ partialQuadrantAtWith T e ↔ v ∈ partialQuadrantAtWith T e := by
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  simp only [map_add, Prod.fst_add, Pi.add_apply, hi, add_zero]

variable (T) in
lemma sub_mem_partialQuadrantAtWith_iff (e v : E 0) :
    v - e ∈ partialQuadrantAtWith T e ↔ v ∈ partialQuadrantAtWith T e := by
  rw [← add_mem_partialQuadrantAtWith_iff T e (v - e), sub_add_cancel]

variable (T) in
/-- **`C_e − e = C_e`**: the translate of the partial quadrant `C_e` by `−e` is `C_e` itself. -/
theorem image_sub_partialQuadrantAtWith (e : E 0) :
    (fun v => v - e) '' partialQuadrantAtWith T e = partialQuadrantAtWith T e := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (sub_mem_partialQuadrantAtWith_iff T e v).2 hv
  · intro hu
    exact ⟨u + e, (add_mem_partialQuadrantAtWith_iff T e u).2 hu, add_sub_cancel_right u e⟩

variable (T) in
/-- The indices `I(e)` of the half-line coordinates vanishing at `e`. -/
abbrev zeroIdx (e : E 0) : Type := {i : Fin n // (T 0 e).1 i = 0}

variable (T) in
/-- The indices of the half-line coordinates not vanishing at `e`. -/
abbrev posIdx (e : E 0) : Type := {i : Fin n // ¬ (T 0 e).1 i = 0}

variable (T) in
/-- The number `d = #I(e)` of vanishing coordinates. -/
abbrev recentreDim (e : E 0) : ℕ := Fintype.card (zeroIdx T e)

variable (T) in
/-- The enumeration `Fin d ≃ I(e)`. -/
abbrev zeroIdxEnum (e : E 0) : Fin (recentreDim T e) → Fin n :=
  fun j => ((Fintype.equivFin (zeroIdx T e)).symm j).1

lemma zeroIdxEnum_mem (e : E 0) (j : Fin (recentreDim T e)) :
    (T 0 e).1 (zeroIdxEnum T e j) = 0 := ((Fintype.equivFin (zeroIdx T e)).symm j).2

lemma zeroIdxEnum_injective (e : E 0) : Injective (zeroIdxEnum T e) := fun _ _ h =>
  (Fintype.equivFin (zeroIdx T e)).symm.injective (Subtype.ext h)

lemma zeroIdxEnum_equivFin (e : E 0) {i : Fin n} (hi : (T 0 e).1 i = 0) :
    zeroIdxEnum T e (Fintype.equivFin (zeroIdx T e) ⟨i, hi⟩) = i := by
  simp only [zeroIdxEnum, Equiv.symm_apply_apply]

variable (T) in
/-- The splitting `ℝⁿ ≅ ℝ^{I(e)} × ℝ^{rest}` of the half-line coordinates. -/
def splitCoordsL (e : E 0) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin (recentreDim T e) → ℝ) × (posIdx T e → ℝ) where
  toFun a := (fun j => a (zeroIdxEnum T e j), fun i => a i.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p i := if h : (T 0 e).1 i = 0 then p.1 (Fintype.equivFin (zeroIdx T e) ⟨i, h⟩)
    else p.2 ⟨i, h⟩
  left_inv a := by
    funext i
    by_cases h : (T 0 e).1 i = 0
    · simp only [dif_pos h, zeroIdxEnum_equivFin e h]
    · simp only [dif_neg h]
  right_inv p := by
    refine Prod.ext (funext fun j => ?_) (funext fun i => ?_)
    · simp only [dif_pos (zeroIdxEnum_mem e j)]
      have : (⟨zeroIdxEnum T e j, zeroIdxEnum_mem e j⟩ : zeroIdx T e) =
          (Fintype.equivFin (zeroIdx T e)).symm j := rfl
      rw [this, Equiv.apply_symm_apply]
    · simp only [dif_neg i.2]

variable (T) in
/-- The sc-isomorphism `ℝⁿ ⊕ W ≅ ℝ^{I(e)} ⊕ (ℝ^{rest} ⊕ W)` reordering the coordinates. -/
def splitCoordsIso (e : E 0) :
    ScIso ((ScBanach.const (Fin n → ℝ)).prod W)
      ((ScBanach.const (Fin (recentreDim T e) → ℝ)).prod
        ((ScBanach.const (posIdx T e → ℝ)).prod W)) where
  lvl m := ((splitCoordsL T e).toContinuousLinearEquiv.prodCongr
      (ContinuousLinearEquiv.refl ℝ (W m))).trans
    (ContinuousLinearEquiv.prodAssoc ℝ (Fin (recentreDim T e) → ℝ) (posIdx T e → ℝ) (W m))
  incl_comm _ _ := rfl

variable (T) in
/-- **The presentation of `C_e`**: `T_e = (reordering) ∘ T : E ≅ ℝ^{I(e)} ⊕ (ℝ^{rest} ⊕ W)`. -/
def recentreIso (e : E 0) :
    ScIso E ((ScBanach.const (Fin (recentreDim T e) → ℝ)).prod
      ((ScBanach.const (posIdx T e → ℝ)).prod W)) :=
  T.trans (splitCoordsIso T e)

lemma recentreIso_fst (e v : E 0) (j : Fin (recentreDim T e)) :
    ((recentreIso T e) 0 v).1 j = (T 0 v).1 (zeroIdxEnum T e j) := rfl

variable (T) in
/-- `C_e = T_e⁻¹([0,∞)^{I(e)} ⊕ (ℝ^{rest} ⊕ W))`. -/
theorem partialQuadrantAtWith_eq_preimage (e : E 0) :
    partialQuadrantAtWith T e = (recentreIso T e) 0 ⁻¹' quadrant (recentreDim T e)
      ((ScBanach.const (posIdx T e → ℝ)).prod W) 0 := by
  ext v
  change (∀ i, (T 0 e).1 i = 0 → 0 ≤ (T 0 v).1 i) ↔ ∀ j, 0 ≤ ((recentreIso T e) 0 v).1 j
  constructor
  · intro h j
    rw [recentreIso_fst]
    exact h _ (zeroIdxEnum_mem e j)
  · intro h i hi
    have := h (Fintype.equivFin (zeroIdx T e) ⟨i, hi⟩)
    rwa [recentreIso_fst, zeroIdxEnum_equivFin e hi] at this

variable (T) in
/-- **`C_e` is a partial quadrant** (Definition 2.33 asserts it). -/
theorem isPartialQuadrant_partialQuadrantAtWith (e : E 0) :
    IsPartialQuadrant E (partialQuadrantAtWith T e) :=
  ⟨_, _, recentreIso T e, partialQuadrantAtWith_eq_preimage T e⟩

/-- Near `e`, the vanishing coordinates of `v − e` for `T_e` are those of `v` for `T`. -/
lemma recentreIso_fst_sub (e v : E 0) (j : Fin (recentreDim T e)) :
    ((recentreIso T e) 0 (v - e)).1 j = (T 0 v).1 (zeroIdxEnum T e j) := by
  rw [recentreIso_fst, map_sub, Prod.fst_sub, Pi.sub_apply, zeroIdxEnum_mem e j, sub_zero]

/-- On `G(e)` every coordinate vanishing at `v` vanishes at `e`. -/
lemma zero_of_mem_recentreNbhd {e v : E 0} (hv : v ∈ recentreNbhd T e) {i : Fin n}
    (hi : (T 0 v).1 i = 0) : (T 0 e).1 i = 0 := by
  by_contra h
  exact (hv i h).ne' hi

/-- **The degeneracy index is unchanged by re-centring**: `d_{C_e}(v − e) = d_C(v)` computed with
the presentations `T_e`, `T`, for `v ∈ G(e)`. -/
theorem degIndexWith_recentreIso {e v : E 0} (hv : v ∈ recentreNbhd T e) :
    degIndexWith (recentreIso T e) (v - e) = degIndexWith T v := by
  change (Finset.univ.filter fun j => ((recentreIso T e) 0 (v - e)).1 j = 0).card =
    (Finset.univ.filter fun i => (T 0 v).1 i = 0).card
  refine Finset.card_bij (fun j _ => zeroIdxEnum T e j) (fun j hj => ?_)
    (fun _ _ _ _ h => zeroIdxEnum_injective e h) (fun i hi => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rwa [recentreIso_fst_sub] at hj
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hie := zero_of_mem_recentreNbhd hv hi
    refine ⟨Fintype.equivFin (zeroIdx T e) ⟨i, hie⟩, ?_, zeroIdxEnum_equivFin e hie⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [recentreIso_fst_sub, zeroIdxEnum_equivFin e hie]
    exact hi

/-- **`d_{C_e}(v − e) = d_C(v)` near `e`** (Definition 1.23 / 2.33), for `v ∈ G(e) ∩ C`. -/
theorem degIndex_sub_recentre (hT : C = T 0 ⁻¹' quadrant n W 0) {e v : E 0}
    (hv : v ∈ recentreNbhd T e) (hvC : v ∈ C) :
    degIndex E (partialQuadrantAtWith T e) (v - e) = degIndex E C v := by
  rw [degIndex_eq (recentreIso T e) (partialQuadrantAtWith_eq_preimage T e)
    ((sub_mem_partialQuadrantAtWith_iff T e v).2 (subset_partialQuadrantAtWith T hT e hvC)),
    degIndex_eq T hT hvC, degIndexWith_recentreIso hv]

/-- **The minimal subspaces are unchanged by re-centring**: `E^{T_e}_{v − e} = E^T_v` for
`v ∈ G(e)` (Definition 2.33). -/
theorem minimalSubspaceWith_recentreIso {e v : E 0} (hv : v ∈ recentreNbhd T e) :
    minimalSubspaceWith (recentreIso T e) (v - e) = minimalSubspaceWith T v := by
  ext u
  rw [mem_minimalSubspaceWith, mem_minimalSubspaceWith]
  constructor
  · intro h i hi
    have hie := zero_of_mem_recentreNbhd hv hi
    have := h (Fintype.equivFin (zeroIdx T e) ⟨i, hie⟩)
      (by rw [recentreIso_fst_sub, zeroIdxEnum_equivFin e hie]; exact hi)
    rwa [recentreIso_fst, zeroIdxEnum_equivFin e hie] at this
  · intro h j hj
    rw [recentreIso_fst_sub] at hj
    rw [recentreIso_fst]
    exact h _ hj

/-- **The partial quadrants `C_x` are unchanged by re-centring**: `(C_e)^{T_e}_{v − e} = C^T_v` for
`v ∈ G(e)`. -/
theorem partialQuadrantAtWith_recentreIso {e v : E 0} (hv : v ∈ recentreNbhd T e) :
    partialQuadrantAtWith (recentreIso T e) (v - e) = partialQuadrantAtWith T v := by
  ext u
  change (∀ j, ((recentreIso T e) 0 (v - e)).1 j = 0 → 0 ≤ ((recentreIso T e) 0 u).1 j) ↔
    ∀ i, (T 0 v).1 i = 0 → 0 ≤ (T 0 u).1 i
  constructor
  · intro h i hi
    have hie := zero_of_mem_recentreNbhd hv hi
    have := h (Fintype.equivFin (zeroIdx T e) ⟨i, hie⟩)
      (by rw [recentreIso_fst_sub, zeroIdxEnum_equivFin e hie]; exact hi)
    rwa [recentreIso_fst, zeroIdxEnum_equivFin e hie] at this
  · intro h j hj
    rw [recentreIso_fst_sub] at hj
    rw [recentreIso_fst]
    exact h _ hj

end Presentation

/-! ### Translations by smooth vectors -/

section Translate

variable {E : ScBanach}

/-- **Translation by a smooth vector is sc-smooth**: for `a ∈ E_∞`, `v ↦ v + a` has the level maps
`x ↦ x + a_m` (`a_m` the lift of `a` to `E_m`), which are smooth. -/
theorem isScSmooth_add_const {a : E 0} (ha : a ∈ E.smooth) {U : Set (E 0)} (hU : IsScDomain E U) :
    IsScSmooth U (fun v => v + a) := by
  choose lift hlift using (E.mem_smooth_iff).1 ha
  have hlev : ∀ m, levelMap (fun v : E 0 => v + a) m = fun x => x + lift m := fun m =>
    funext fun x => levelMap_eq_of_toBase_eq (by rw [map_add, hlift])
  refine IsScSmooth.of_contDiffOn_levels hU
    (fun m x _ => ⟨x + lift m, by rw [map_add, hlift]⟩) fun m => ?_
  rw [hlev]
  exact (contDiff_id.add contDiff_const).contDiffOn

theorem isScSmooth_sub_const {a : E 0} (ha : a ∈ E.smooth) {U : Set (E 0)} (hU : IsScDomain E U) :
    IsScSmooth U (fun v => v - a) :=
  (isScSmooth_add_const (E.smooth.neg_mem ha) hU).congr hU fun v _ => (sub_eq_add_neg v a).symm

variable {n : ℕ} {W : ScBanach} {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} {C : Set (E 0)}

/-- The translate `U − e = {u | u + e ∈ U}` of a relatively open `U ⊆ G(e) ∩ C` is relatively open
in `C_e`. -/
theorem relOpen_translate (hT : C = T 0 ⁻¹' quadrant n W 0) {e : E 0} {U : Set (E 0)}
    (hU : IsRelOpenInQuadrant E C U) (hUG : U ⊆ recentreNbhd T e) :
    IsRelOpenInQuadrant E (partialQuadrantAtWith T e) ((fun u => u + e) ⁻¹' U) := by
  obtain ⟨O, hO, rfl⟩ := hU.relOpen
  refine ⟨isPartialQuadrant_partialQuadrantAtWith T e,
    (fun u => u + e) ⁻¹' (O ∩ recentreNbhd T e),
    (hO.inter (isOpen_recentreNbhd T e)).preimage (continuous_id.add continuous_const), ?_⟩
  ext u
  simp only [mem_preimage, mem_inter_iff]
  constructor
  · rintro ⟨hO', hC⟩
    exact ⟨⟨hO', hUG ⟨hO', hC⟩⟩,
      (add_mem_partialQuadrantAtWith_iff T e u).1 (subset_partialQuadrantAtWith T hT e hC)⟩
  · rintro ⟨⟨hO', hG⟩, hCe⟩
    refine ⟨hO', ?_⟩
    have : u + e ∈ recentreNbhd T e ∩ partialQuadrantAtWith T e :=
      ⟨hG, (add_mem_partialQuadrantAtWith_iff T e u).2 hCe⟩
    rw [← recentreNbhd_inter_eq hT e] at this
    exact this.2

/-- **The translation `v ↦ v − e` is an sc-diffeomorphism** from a relatively open `U ⊆ G(e) ∩ C`
onto `U − e ⊆ C_e` (`e` smooth). -/
theorem isScDiffeoQuadrant_translate (hT : C = T 0 ⁻¹' quadrant n W 0) {e : E 0}
    (he : e ∈ E.smooth) {U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    (hUG : U ⊆ recentreNbhd T e) :
    IsScDiffeoQuadrant hU (relOpen_translate hT hU hUG) (fun v => v - e) (fun u => u + e) where
  isScSmooth := isScSmooth_sub_const he hU.isScDomain
  isScSmooth_inv := isScSmooth_add_const he (relOpen_translate hT hU hUG).isScDomain
  mapsTo v hv := by
    change v - e + e ∈ U
    rw [sub_add_cancel]; exact hv
  mapsTo_inv _ hu := hu
  left_inv v _ := sub_add_cancel v e
  right_inv u _ := add_sub_cancel_right u e

end Translate

/-! ### Retractions with domain in an open set -/

section RestrictIn

variable {E : ScBanach} {C : Set (E 0)}

/-- The restriction of an sc-smooth retraction `r : U → U` to `U ∩ r⁻¹(W) ∩ W`, `W` open: a
retraction onto `r(U) ∩ W` whose domain lies in `W` (a variant of Proposition 2.10 (1)). -/
def ScRetraction.restrictIn (R : ScRetraction E C) {W : Set (E 0)} (hW : IsOpen W) :
    ScRetraction E C where
  U := R.U ∩ R ⁻¹' W ∩ W
  toFun := R
  relOpen := (R.relOpen_inter_preimage hW).inter_isOpen hW
  mapsTo y hy := ⟨⟨R.mapsTo hy.1.1, by
    change R (R y) ∈ W
    rw [R.idem y hy.1.1]; exact hy.1.2⟩, hy.1.2⟩
  isScSmooth := R.isScSmooth.of_subset ((R.relOpen_inter_preimage hW).inter_isOpen hW).isScDomain
    fun y hy => hy.1.1
  idem y hy := R.idem y hy.1.1

variable (R : ScRetraction E C) {W : Set (E 0)} (hW : IsOpen W)

lemma ScRetraction.restrictIn_U : (R.restrictIn hW).U = R.U ∩ R ⁻¹' W ∩ W := rfl

lemma ScRetraction.restrictIn_U_subset : (R.restrictIn hW).U ⊆ W := fun _ hy => hy.2

lemma ScRetraction.restrictIn_apply (y : E 0) : R.restrictIn hW y = R y := rfl

lemma ScRetraction.restrictIn_retract : (R.restrictIn hW).retract = R.retract ∩ W := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨R.apply_mem_retract hy.1.1, hy.1.2⟩
  · rintro ⟨hz, hzW⟩
    refine ⟨z, ⟨⟨R.retract_subset hz, ?_⟩, hzW⟩, R.apply_eq_self_of_mem_retract hz⟩
    change R z ∈ W
    rw [R.apply_eq_self_of_mem_retract hz]; exact hzW

/-- On the restricted domain, the derivative of the retraction is unchanged. -/
lemma ScRetraction.scDeriv_restrictIn {x : E 1} (hx : x ∈ E.lvlSet (R.restrictIn hW).U 1) :
    scDeriv (R.restrictIn hW).U (R.restrictIn hW) x = scDeriv R.U R x :=
  scDeriv_eq_of_eqOn_relOpen (R.restrictIn hW).relOpen (R.restrictIn hW).isSc1 R.isSc1 subset_rfl
    (fun _ hy => hy.1.1) (fun _ _ => rfl) hx

/-- The restriction of a tame retraction to `U ∩ r⁻¹(W) ∩ W` is tame. -/
theorem ScRetraction.IsTameWith.restrictIn {n : ℕ} {W' : ScBanach}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W')} (h : R.IsTameWith T) :
    (R.restrictIn hW).IsTameWith T where
  degIndex_apply x hx := h.degIndex_apply x hx.1.1
  exists_complement x hx hs := by
    have hx' : x ∈ E.lvlSet R.retract 1 := by
      have : E.toBase 1 x ∈ (R.restrictIn hW).retract := hx
      rw [R.restrictIn_retract] at this; exact this.1
    rw [R.scDeriv_restrictIn hW ((R.restrictIn hW).lvlSet_retract_subset 1 hx)]
    exact h.exists_complement x hx' hs

theorem ScRetraction.restrictIn_isTame (h : R.IsTame) : (R.restrictIn hW).IsTame :=
  fun n W' T hT => (h n W' T hT).restrictIn R hW

end RestrictIn

/-! ### The re-centred retract -/

section RecentreRetract

variable {E : ScBanach} {n : ℕ} {W : ScBanach} {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}
  {C : Set (E 0)}

/-- **The re-centred retract**: for a retract `(O, C, E)` and a smooth `e ∈ C`,
`((O ∩ G(e)) − e, C_e, E)` is a retract (the retraction `r(u + e) − e` on the translate of
`U ∩ r⁻¹(G) ∩ G`). -/
theorem isScRetract_recentre (hT : C = T 0 ⁻¹' quadrant n W 0) {e : E 0} (he : e ∈ E.smooth)
    {O : Set (E 0)} (hO : IsScRetract E C O) :
    IsScRetract E (partialQuadrantAtWith T e) ((fun v => v - e) '' (O ∩ recentreNbhd T e)) := by
  obtain ⟨R, rfl⟩ := hO
  have hG := isOpen_recentreNbhd T e
  have h := isScDiffeoQuadrant_translate hT he (R.restrictIn hG).relOpen
    (R.restrictIn_U_subset hG)
  exact ⟨h.transport (R.restrictIn hG) rfl, by rw [h.transport_retract, R.restrictIn_retract]⟩

/-- **A tame retract stays tame under re-centring**: for a tame retract `(O, C, E)` and a smooth
`e ∈ C`, `((O ∩ G(e)) − e, C_e, E)` is a tame retract (the restriction to `G(e)` is tame,
`ScRetraction.restrictIn_isTame`, and the translation carries tameness,
`IsScDiffeoQuadrant.isTame_transport`, by `d_{C_e}(v − e) = d_C(v)` and the invariance of the
minimal subspaces). -/
theorem isTameRetract_recentre (hT : C = T 0 ⁻¹' quadrant n W 0) {e : E 0} (he : e ∈ E.smooth)
    {O : Set (E 0)} (hO : IsTameRetract E C O) :
    IsTameRetract E (partialQuadrantAtWith T e) ((fun v => v - e) '' (O ∩ recentreNbhd T e)) := by
  obtain ⟨R, rfl, hR⟩ := hO
  have hG := isOpen_recentreNbhd T e
  have h := isScDiffeoQuadrant_translate hT he (R.restrictIn hG).relOpen
    (R.restrictIn_U_subset hG)
  exact ⟨h.transport (R.restrictIn hG) rfl, by rw [h.transport_retract, R.restrictIn_retract],
    h.isTame_transport _ rfl (R.restrictIn_isTame hG hR)⟩

end RecentreRetract

/-! ### The re-centred chart -/

section RecentreChart

universe u

variable {X : Type u} [TopologicalSpace X] (φ : MChart X)
  {n : ℕ} {W : ScBanach} (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
  (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) (e : φ.model.E 0) (he : e ∈ φ.model.E.smooth)

/-- The domain `V_e = V ∩ φ⁻¹(G(e))` of the re-centred chart. -/
def MChart.recentreSource : Set X := φ.source ∩ φ ⁻¹' recentreNbhd T e

lemma MChart.isOpen_recentreSource : IsOpen (φ.recentreSource T e) :=
  φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source (isOpen_recentreNbhd T e)

lemma MChart.image_recentreSource :
    φ '' φ.recentreSource T e = φ.model.O ∩ recentreNbhd T e := by
  rw [MChart.recentreSource, image_inter_preimage, φ.image_source]

/-- The relatively open set `C ∩ G(e)` on which the translation is an sc-diffeomorphism. -/
lemma MChart.relOpen_recentreDom :
    IsRelOpenInQuadrant φ.model.E φ.model.C (φ.model.C ∩ recentreNbhd T e) :=
  ⟨φ.model.isPartialQuadrant, recentreNbhd T e, isOpen_recentreNbhd T e, inter_comm _ _⟩

lemma MChart.recentreSource_subset : φ.recentreSource T e ⊆ φ.source := inter_subset_left

include hT he in
/-- **The re-centred chart** `φ_e = φ − e : V ∩ φ⁻¹(G(e)) → (O ∩ G(e)) − e ⊆ C_e` (for `e = φ(x)`
it is centred at `x`: `MChart.recentre_apply_self`): the chart `φ` restricted to `φ⁻¹(G(e))`
(`MChart.restrict`) composed with the translation by `−e` (`MChart.compDiffeo`), modelled on the
retract `(O ∩ G(e)) − e` in the partial quadrant `C_e = C_e − e` of Definition 2.33. -/
def MChart.recentre : MChart X :=
  (φ.restrict (s := φ.recentreSource T e) inter_subset_left (φ.isOpen_recentreSource T e)).compDiffeo
    (hU := φ.relOpen_recentreDom T e)
    (isScDiffeoQuadrant_translate hT he (φ.relOpen_recentreDom T e) inter_subset_right)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨φ.apply_mem_C hx.1, hx.2⟩)
    (by
      change IsScRetract φ.model.E (partialQuadrantAtWith T e)
        ((fun v => v - e) '' (φ '' φ.recentreSource T e))
      rw [φ.image_recentreSource]
      exact isScRetract_recentre hT he φ.model.isScRetract)

lemma MChart.recentre_source : (φ.recentre T hT e he).source = φ.recentreSource T e := rfl

lemma MChart.recentre_apply (x : X) : φ.recentre T hT e he x = φ x - e := rfl

lemma MChart.recentre_symm_apply (z : φ.model.E 0) :
    (φ.recentre T hT e he).symm z = φ.symm (z + e) := rfl

lemma MChart.recentre_model_E : (φ.recentre T hT e he).model.E = φ.model.E := rfl

lemma MChart.recentre_model_C :
    (φ.recentre T hT e he).model.C = partialQuadrantAtWith T e := rfl

lemma MChart.recentre_model_O :
    (φ.recentre T hT e he).model.O = (fun v => v - e) '' (φ.model.O ∩ recentreNbhd T e) := by
  change (fun v => v - e) '' (φ '' φ.recentreSource T e) = _
  rw [φ.image_recentreSource]

/-- The re-centred chart at `e = φ(x)` contains `x`. -/
lemma MChart.mem_recentre_source {x : X} (hx : x ∈ φ.source) (hxe : φ x = e) :
    x ∈ (φ.recentre T hT e he).source :=
  ⟨hx, by rw [mem_preimage, hxe]; exact mem_recentreNbhd hT (hxe ▸ φ.apply_mem_C hx)⟩

/-- **The re-centred chart at `e = φ(x)` is centred at `x`**: `φ_e(x) = 0`. -/
lemma MChart.recentre_apply_self {x : X} (hxe : φ x = e) : φ.recentre T hT e he x = 0 := by
  change φ x - e = 0
  rw [hxe, sub_self]

/-- **The re-centred chart is a chart of the M-polyfold** (compatible with the atlas): its
transition maps to a chart `ψ` are `(ψ ∘ φ⁻¹) ∘ (· + e)` and `(· − e) ∘ (φ ∘ ψ⁻¹)`
(`MChart.compDiffeo_isChart`). -/
theorem MChart.recentre_isChart [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
    (hφ : P.IsChart φ) :
    P.IsChart (φ.recentre T hT e he) :=
  MChart.compDiffeo_isChart
    (MPolyfold.IsChart.restrict P hφ inter_subset_left (φ.isOpen_recentreSource T e)) _ _ _

/-- **Tameness of the model is preserved by re-centring**. -/
theorem MChart.isTameRetract_recentre (htame : IsTameRetract φ.model.E φ.model.C φ.model.O) :
    IsTameRetract (φ.recentre T hT e he).model.E (φ.recentre T hT e he).model.C
      (φ.recentre T hT e he).model.O := by
  rw [MChart.recentre_model_O]
  exact Polyfold.isTameRetract_recentre hT he htame

/-- **The degeneracy index of the re-centred chart**: `d_{C_e}(φ_e(y)) = d_C(φ(y))` on the domain of
`φ_e` (Definition 2.22 computed in the chart). -/
theorem MChart.chartDegIndex_recentre {y : X} (hy : y ∈ (φ.recentre T hT e he).source) :
    MPolyfold.chartDegIndex (φ.recentre T hT e he) y = MPolyfold.chartDegIndex φ y :=
  degIndex_sub_recentre hT hy.2 (φ.apply_mem_C hy.1)

end RecentreChart

/-! ### Translations of the base in `E ⊕ F` -/

section TranslateFst

/-- `(u, h) ↦ (u − e, h)`. -/
def subFst {α β : Type*} [Sub α] (e : α) (p : α × β) : α × β := (p.1 - e, p.2)

/-- `(u, h) ↦ (u + e, h)`. -/
def addFst {α β : Type*} [Add α] (e : α) (p : α × β) : α × β := (p.1 + e, p.2)

lemma addFst_subFst {α β : Type*} [AddGroup α] (e : α) (p : α × β) :
    addFst e (subFst e p) = p := Prod.ext (sub_add_cancel p.1 e) rfl

lemma subFst_addFst {α β : Type*} [AddGroup α] (e : α) (p : α × β) :
    subFst e (addFst e p) = p := Prod.ext (add_sub_cancel_right p.1 e) rfl

variable {E F : ScBanach}

lemma mem_smooth_prod_zero {e : E 0} (he : e ∈ E.smooth) :
    ((e, 0) : (E.prod F) 0) ∈ (E.prod F).smooth := by
  have : ((e, 0) : (E.prod F) 0) ∈ (E.prod F).smoothLvl 0 := by
    rw [ScBanach.prod_smoothLvl]; exact ⟨he, F.smooth.zero_mem⟩
  exact this

/-- `(u, h) ↦ (u + e, h)` is sc-smooth on `E ⊕ F` for smooth `e`. -/
theorem isScSmooth_addFst {e : E 0} (he : e ∈ E.smooth) {U : Set ((E.prod F) 0)}
    (hU : IsScDomain (E.prod F) U) :
    IsScSmooth (E := E.prod F) (F := E.prod F) U (addFst (β := F 0) e) :=
  (isScSmooth_add_const (mem_smooth_prod_zero (F := F) he) hU).congr hU fun p _ => by
    show p + (e, 0) = addFst e p
    exact Prod.ext rfl (add_zero p.2)

/-- `(u, h) ↦ (u − e, h)` is sc-smooth on `E ⊕ F` for smooth `e`. -/
theorem isScSmooth_subFst {e : E 0} (he : e ∈ E.smooth) {U : Set ((E.prod F) 0)}
    (hU : IsScDomain (E.prod F) U) :
    IsScSmooth (E := E.prod F) (F := E.prod F) U (subFst (β := F 0) e) :=
  (isScSmooth_sub_const (mem_smooth_prod_zero (F := F) he) hU).congr hU fun p _ => by
    show p - (e, 0) = subFst e p
    exact Prod.ext rfl (sub_zero p.2)

lemma continuous_addFst (e : E 0) : Continuous (addFst (β := F 0) e) :=
  (continuous_fst.add continuous_const).prodMk continuous_snd

lemma continuous_subFst (e : E 0) : Continuous (subFst (β := F 0) e) :=
  (continuous_fst.sub continuous_const).prodMk continuous_snd

/-- A map sc-smooth on all of `E` is sc-smooth between any retracts it maps into each other. -/
theorem isScSmoothRetractMap_of_isScSmooth_univ {E' : ScBanach} {C O : Set (E 0)}
    {C' O' : Set (E' 0)} {g : E 0 → E' 0} (hg : IsScSmooth (univ : Set (E 0)) g)
    (hmaps : MapsTo g O O') : IsScSmoothRetractMap E C O E' C' O' g where
  mapsTo := hmaps
  comp_isScSmooth R _ :=
    IsScSmooth.comp R.isScDomain (isScDomain_univ _) hg R.isScSmooth (mapsTo_univ _ _)

end TranslateFst

/-! ### Re-centring strong bundle retractions -/

section StrongRetraction

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- The restriction of a strong bundle retraction to `(U ∩ r⁻¹(G) ∩ G) ◁ F`, `G` open. -/
theorem IsStrongBundleRetraction.restrictIn (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) {G : Set (E 0)} (hG : IsOpen G) :
    IsStrongBundleRetraction ((hR.baseRetraction hU).restrictIn hG).U R where
  mapsTo p hp := by
    refine ⟨?_, mem_univ _⟩
    have h1 := hR.apply_fst hp.1.1.1 p.2
    rw [Prod.mk.eta] at h1
    rw [h1]
    exact ((hR.baseRetraction hU).restrictIn hG).mapsTo hp.1
  fst_independent u hu := hR.fst_independent u hu.1.1
  fiber_linear u hu := hR.fiber_linear u hu.1.1
  preserves_filtration m k hk u hu := hR.preserves_filtration m k hk u hu.1.1
  isScSmooth_zero := hR.isScSmooth_zero.of_subset
    (((hR.baseRetraction hU).restrictIn hG).relOpen.prod_univ F).isScDomain
    (prod_mono (fun _ hu => hu.1.1) subset_rfl)
  isScSmooth_one := hR.isScSmooth_one.of_subset
    (((hR.baseRetraction hU).restrictIn hG).relOpen.prod_univ F.shift).isScDomain
    (prod_mono (fun _ hu => hu.1.1) subset_rfl)
  idem p hp := hR.idem p ⟨hp.1.1.1, mem_univ _⟩

lemma IsStrongBundleRetraction.restrictIn_base_retract (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) {G : Set (E 0)} (hG : IsOpen G) :
    ((hR.restrictIn hU hG).baseRetraction ((hR.baseRetraction hU).restrictIn hG).relOpen).retract =
      (hR.baseRetraction hU).retract ∩ G :=
  (hR.baseRetraction hU).restrictIn_retract hG

variable {n : ℕ} {W : ScBanach} {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}

/-- **The translated strong bundle retraction** `R'(u, h) = (r(u + e) − e, Γ(u + e, h))` on
`(U − e) ◁ F`, for `U ⊆ G(e)` and a smooth `e`. -/
theorem IsStrongBundleRetraction.translate (hT : C = T 0 ⁻¹' quadrant n W 0) {e : E 0}
    (he : e ∈ E.smooth) (hU : IsRelOpenInQuadrant E C U) (hUG : U ⊆ recentreNbhd T e)
    (hR : IsStrongBundleRetraction U R) :
    IsStrongBundleRetraction ((fun u => u + e) ⁻¹' U) (subFst e ∘ R ∘ addFst e) where
  mapsTo p hp := by
    refine ⟨?_, mem_univ _⟩
    change (R (addFst e p)).1 - e + e ∈ U
    rw [sub_add_cancel]
    exact (hR.mapsTo (show addFst e p ∈ U ×ˢ univ from ⟨hp.1, mem_univ _⟩)).1
  fst_independent u hu h h' := by
    change (R (u + e, h)).1 - e = (R (u + e, h')).1 - e
    rw [hR.fst_independent (u + e) hu h h']
  fiber_linear u hu := hR.fiber_linear (u + e) hu
  preserves_filtration m k hk u hu hum h hh := by
    obtain ⟨em, hem⟩ := (E.mem_smooth_iff.1 he) m
    have hum' : u + e ∈ range (E.toBase m) := by
      obtain ⟨um, rfl⟩ := hum
      exact ⟨um + em, by rw [map_add, hem]⟩
    obtain ⟨h1, h2⟩ := hR.preserves_filtration m k hk (u + e) hu hum' h hh
    refine ⟨?_, h2⟩
    obtain ⟨vm, hvm⟩ := h1
    exact ⟨vm - em, by rw [map_sub, hvm, hem]; rfl⟩
  isScSmooth_zero := by
    have hD := ((relOpen_translate hT hU hUG).prod_univ F).isScDomain
    have hmaps : MapsTo (addFst (β := F 0) e) (((fun u => u + e) ⁻¹' U) ×ˢ univ) (U ×ˢ univ) :=
      fun p hp => ⟨hp.1, mem_univ _⟩
    have h1 : IsScSmooth (((fun u => u + e) ⁻¹' U) ×ˢ (univ : Set (F 0))) (R ∘ addFst e) :=
      IsScSmooth.comp (E := E.prod F) (F := E.prod F) (G := E.prod F) hD (hU.prod_univ F).isScDomain hR.isScSmooth_zero (isScSmooth_addFst he hD)
        hmaps
    exact IsScSmooth.comp hD (isScDomain_univ _) (isScSmooth_subFst he (isScDomain_univ _)) h1
      (mapsTo_univ _ _)
  isScSmooth_one := by
    have hD := ((relOpen_translate hT hU hUG).prod_univ F.shift).isScDomain
    have hmaps : MapsTo (addFst (β := F.shift 0) e) (((fun u => u + e) ⁻¹' U) ×ˢ univ)
        (U ×ˢ univ) := fun p hp => ⟨hp.1, mem_univ _⟩
    have h1 : IsScSmooth (((fun u => u + e) ⁻¹' U) ×ˢ (univ : Set (F.shift 0)))
        (shiftFiber R ∘ addFst e) :=
      IsScSmooth.comp (E := E.prod F.shift) (F := E.prod F.shift) (G := E.prod F.shift) hD (hU.prod_univ F.shift).isScDomain hR.isScSmooth_one
        (isScSmooth_addFst (F := F.shift) he hD) hmaps
    exact IsScSmooth.comp hD (isScDomain_univ _)
      (isScSmooth_subFst (F := F.shift) he (isScDomain_univ _)) h1 (mapsTo_univ _ _)
  idem p hp := by
    change subFst e (R (addFst e (subFst e (R (addFst e p))))) = subFst e (R (addFst e p))
    have hp' : addFst e p ∈ U ×ˢ univ := ⟨hp.1, mem_univ _⟩
    rw [addFst_subFst, hR.idem _ hp']

/-- The base retract of the translated strong bundle retraction is the translate `r(U) − e`. -/
theorem IsStrongBundleRetraction.translate_base_retract (hT : C = T 0 ⁻¹' quadrant n W 0)
    {e : E 0} (he : e ∈ E.smooth) (hU : IsRelOpenInQuadrant E C U) (hUG : U ⊆ recentreNbhd T e)
    (hR : IsStrongBundleRetraction U R) :
    ((hR.translate hT he hU hUG).baseRetraction (relOpen_translate hT hU hUG)).retract =
      (fun v => v - e) '' (hR.baseRetraction hU).retract := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(R (u + e, 0)).1, ⟨u + e, hu, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨v - e, show v - e + e ∈ U by rw [sub_add_cancel]; exact hv, ?_⟩
    change (R (v - e + e, 0)).1 - e = (R (v, 0)).1 - e
    rw [sub_add_cancel]

end StrongRetraction

/-! ### Re-centred strong bundle charts -/

section StrongChart

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundleChart

variable (c : StrongBundleChart PX P)

lemma mem_source_iff' {y : Y} : y ∈ c.toPartialEquiv.source ↔ P y ∈ c.φ.source := by
  rw [c.source_eq]; exact Iff.rfl

lemma apply_mem_K' {y : Y} (hy : y ∈ c.toPartialEquiv.source) : c y ∈ c.K := by
  have := c.toPartialEquiv.map_source hy
  rwa [c.target_eq] at this

lemma R_apply_of_mem_K {k : c.φ.model.E 0 × c.F 0} (hk : k ∈ c.K) : c.R k = k := by
  obtain ⟨q, hq, rfl⟩ := hk
  exact c.isRetraction.idem q hq

variable {n : ℕ} {W : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
  (hT : c.φ.model.C = T 0 ⁻¹' quadrant n W 0) (e : c.φ.model.E 0) (he : e ∈ c.φ.model.E.smooth)

/-- The base retraction `r` of the chart restricted to `U ∩ r⁻¹(G(e)) ∩ G(e)`. -/
abbrev recentreBaseR : ScRetraction c.φ.model.E c.φ.model.C :=
  (c.isRetraction.baseRetraction c.relOpen).restrictIn (isOpen_recentreNbhd T e)

lemma recentreBaseR_retract :
    (c.recentreBaseR T e).retract = c.φ.model.O ∩ recentreNbhd T e := by
  rw [ScRetraction.restrictIn_retract, c.base_retract]

lemma recentre_mem_target {y : Y} (hy : P y ∈ c.φ.recentreSource T e) :
    subFst e (c y) ∈ (subFst e ∘ c.R ∘ addFst e) ''
      (((fun u => u + e) ⁻¹' (c.recentreBaseR T e).U) ×ˢ univ) := by
  have hys : y ∈ c.toPartialEquiv.source := (c.mem_source_iff').2 hy.1
  have hK := c.apply_mem_K' hys
  have h1 : (c y).1 ∈ (c.recentreBaseR T e).retract := by
    rw [c.recentreBaseR_retract, c.covers y hys]
    exact ⟨c.φ.mapsTo_model _ hy.1, hy.2⟩
  refine ⟨subFst e (c y), ⟨?_, mem_univ _⟩, ?_⟩
  · change (c y).1 - e + e ∈ (c.recentreBaseR T e).U
    rw [sub_add_cancel]
    exact (c.recentreBaseR T e).retract_subset h1
  · change subFst e (c.R (addFst e (subFst e (c y)))) = subFst e (c y)
    rw [addFst_subFst, c.R_apply_of_mem_K hK]

lemma recentre_addFst_mem_K {p : c.φ.model.E 0 × c.F 0}
    (hp : p ∈ (subFst e ∘ c.R ∘ addFst e) ''
      (((fun u => u + e) ⁻¹' (c.recentreBaseR T e).U) ×ˢ univ)) :
    addFst e p ∈ c.K ∧ (addFst e p).1 ∈ recentreNbhd T e := by
  obtain ⟨q, hq, rfl⟩ := hp
  change addFst e (subFst e (c.R (addFst e q))) ∈ c.K ∧
    (addFst e (subFst e (c.R (addFst e q)))).1 ∈ recentreNbhd T e
  rw [addFst_subFst]
  have hqU : addFst e q ∈ (c.recentreBaseR T e).U ×ˢ (univ : Set (c.F 0)) := ⟨hq.1, mem_univ _⟩
  refine ⟨⟨addFst e q, ⟨hqU.1.1.1, mem_univ _⟩, rfl⟩, ?_⟩
  have := ((c.isRetraction.restrictIn c.relOpen (isOpen_recentreNbhd T e)).mapsTo hqU).1
  exact (c.isRetraction.baseRetraction c.relOpen).restrictIn_U_subset (isOpen_recentreNbhd T e) this

/-- The re-centred bundle chart `Φ_e(y) = (Φ(y)₁ − e, Φ(y)₂)` on `P⁻¹(V ∩ φ⁻¹(G(e)))`. -/
def recentrePE : PartialEquiv Y (c.φ.model.E 0 × c.F 0) where
  toFun y := subFst e (c y)
  invFun p := c.toPartialEquiv.symm (addFst e p)
  source := P ⁻¹' c.φ.recentreSource T e
  target := (subFst e ∘ c.R ∘ addFst e) ''
    (((fun u => u + e) ⁻¹' (c.recentreBaseR T e).U) ×ˢ univ)
  map_source' y hy := c.recentre_mem_target T e hy
  map_target' p hp := by
    obtain ⟨hK, hG⟩ := c.recentre_addFst_mem_K T e hp
    have hK' : addFst e p ∈ c.toPartialEquiv.target := by rw [c.target_eq]; exact hK
    have hs := c.toPartialEquiv.map_target hK'
    refine ⟨(c.mem_source_iff').1 hs, ?_⟩
    change c.φ (P (c.toPartialEquiv.symm (addFst e p))) ∈ recentreNbhd T e
    rw [← c.covers _ hs, c.toPartialEquiv.right_inv hK']
    exact hG
  left_inv' y hy := by
    rw [addFst_subFst]
    exact c.toPartialEquiv.left_inv ((c.mem_source_iff').2 hy.1)
  right_inv' p hp := by
    obtain ⟨hK, -⟩ := c.recentre_addFst_mem_K T e hp
    have hK' : addFst e p ∈ c.toPartialEquiv.target := by rw [c.target_eq]; exact hK
    change subFst e (c.toPartialEquiv (c.toPartialEquiv.symm (addFst e p))) = p
    rw [c.toPartialEquiv.right_inv hK', subFst_addFst]

/-- **The re-centred strong bundle chart**: over the re-centred base chart `φ_e = φ − e`, the
strong bundle retraction `R_e(u, h) = (r(u + e) − e, Γ(u + e, h))` on `(U ∩ r⁻¹(G) ∩ G − e) ◁ F`
(only the base is translated), and `Φ_e(y) = (Φ(y)₁ − e, Φ(y)₂)`. -/
def recentre : StrongBundleChart PX P where
  φ := c.φ.recentre T hT e he
  isChart := c.φ.recentre_isChart T hT e he c.isChart
  F := c.F
  U := (fun u : c.φ.model.E 0 => u + e) ⁻¹' (c.recentreBaseR T e).U
  R := subFst e ∘ c.R ∘ addFst e
  relOpen := relOpen_translate hT (c.recentreBaseR T e).relOpen
    ((c.isRetraction.baseRetraction c.relOpen).restrictIn_U_subset _)
  isRetraction := (c.isRetraction.restrictIn c.relOpen (isOpen_recentreNbhd T e)).translate hT he
    (c.recentreBaseR T e).relOpen
    ((c.isRetraction.baseRetraction c.relOpen).restrictIn_U_subset _)
  base_retract := by
    have h1 := IsStrongBundleRetraction.translate_base_retract hT he (c.recentreBaseR T e).relOpen
      ((c.isRetraction.baseRetraction c.relOpen).restrictIn_U_subset _)
      (c.isRetraction.restrictIn c.relOpen (isOpen_recentreNbhd T e))
    have h2 := IsStrongBundleRetraction.restrictIn_base_retract c.relOpen c.isRetraction
      (isOpen_recentreNbhd T e)
    refine h1.trans ?_
    rw [h2, c.base_retract]
    exact (MChart.recentre_model_O c.φ T hT e he).symm
  toPartialEquiv := c.recentrePE T e
  source_eq := rfl
  target_eq := rfl
  continuousOn_toFun := by
    have hsub : (c.recentrePE T e).source ⊆ c.toPartialEquiv.source := fun y hy =>
      (c.mem_source_iff').2 hy.1
    exact (continuous_subFst (F := c.F) e).comp_continuousOn (c.continuousOn_toFun.mono hsub)
  continuousOn_invFun := by
    refine c.continuousOn_invFun.comp (continuous_addFst (F := c.F) e).continuousOn
      fun p hp => ?_
    rw [c.target_eq]
    exact (c.recentre_addFst_mem_K T e hp).1
  covers y hy := congrArg (fun v => v - e) (c.covers y ((c.mem_source_iff').2 hy.1))
  fiber_linear x hx := c.fiber_linear x hx.1

lemma recentre_apply (y : Y) : c.recentre T hT e he y = subFst e (c y) := rfl

lemma recentre_symm_apply (p : c.φ.model.E 0 × c.F 0) :
    (c.recentre T hT e he).toPartialEquiv.symm p = c.toPartialEquiv.symm (addFst e p) := rfl

lemma recentre_source :
    (c.recentre T hT e he).toPartialEquiv.source = P ⁻¹' c.φ.recentreSource T e := rfl

lemma recentre_φ : (c.recentre T hT e he).φ = c.φ.recentre T hT e he := rfl

lemma recentre_R : (c.recentre T hT e he).R = subFst e ∘ c.R ∘ addFst e := rfl

lemma mem_recentre_source_iff {y : Y} :
    y ∈ (c.recentre T hT e he).toPartialEquiv.source ↔
      y ∈ c.toPartialEquiv.source ∧ (c y).1 ∈ recentreNbhd T e := by
  constructor
  · intro hy
    have hys := (c.mem_source_iff').2 hy.1
    exact ⟨hys, by rw [c.covers y hys]; exact hy.2⟩
  · rintro ⟨hys, hG⟩
    refine ⟨(c.mem_source_iff').1 hys, ?_⟩
    change c.φ (P y) ∈ recentreNbhd T e
    rw [← c.covers y hys]; exact hG

end StrongBundleChart

end StrongChart

/-! ### Compatibility of the re-centred strong bundle chart -/

section StrongCompat

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundleChart

variable (c c'' : StrongBundleChart PX P) {n : ℕ} {W : ScBanach}
  (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
  (hT : c.φ.model.C = T 0 ⁻¹' quadrant n W 0) (e : c.φ.model.E 0) (he : e ∈ c.φ.model.E.smooth)

/-- The overlap of the re-centred chart with `c''`, seen in the re-centred chart: the translate of
the part of `Φ(P⁻¹(V ∩ V''))` over `G(e)`. -/
lemma recentre_overlap :
    (c.recentre T hT e he).overlap c'' =
      subFst e '' (c.overlap c'' ∩ (recentreNbhd T e ×ˢ univ)) := by
  ext k
  constructor
  · rintro ⟨y, ⟨hy', hy''⟩, rfl⟩
    have := (c.mem_recentre_source_iff T hT e he).1 hy'
    exact ⟨c y, ⟨⟨y, ⟨this.1, hy''⟩, rfl⟩, this.2, mem_univ _⟩, rfl⟩
  · rintro ⟨_, ⟨⟨y, ⟨hy, hy''⟩, rfl⟩, hG, -⟩, rfl⟩
    exact ⟨y, ⟨(c.mem_recentre_source_iff T hT e he).2 ⟨hy, hG⟩, hy''⟩, rfl⟩

/-- The overlap of `c''` with the re-centred chart, seen in `c''`. -/
lemma mem_overlap_recentre_iff {k : c''.φ.model.E 0 × c''.F 0} :
    k ∈ c''.overlap (c.recentre T hT e he) ↔
      k ∈ c''.overlap c ∧ (c''.transition c k).1 ∈ recentreNbhd T e := by
  constructor
  · rintro ⟨y, ⟨hy'', hy'⟩, rfl⟩
    have := (c.mem_recentre_source_iff T hT e he).1 hy'
    refine ⟨⟨y, ⟨hy'', this.1⟩, rfl⟩, ?_⟩
    rw [c''.transition_apply c hy'']; exact this.2
  · rintro ⟨⟨y, ⟨hy'', hy⟩, rfl⟩, hG⟩
    rw [c''.transition_apply c hy''] at hG
    exact ⟨y, ⟨hy'', (c.mem_recentre_source_iff T hT e he).2 ⟨hy, hG⟩⟩, rfl⟩

/-- `Φ''(P⁻¹(V'' ∩ V_e))` is an open part of `Φ''(P⁻¹(V'' ∩ V))`. -/
lemma overlap_recentre_eq (hP : Continuous P) :
    ∃ Wo, IsOpen Wo ∧ c''.overlap (c.recentre T hT e he) = c''.overlap c ∩ Wo := by
  obtain ⟨Wo, hWo, hWoeq⟩ := (c''.toMChart hP).exists_isOpen_image_eq
    (s := c''.toPartialEquiv.source ∩ (c.recentre T hT e he).toPartialEquiv.source)
    inter_subset_left ((c''.isOpen_source hP).inter ((c.recentre T hT e he).isOpen_source hP))
  refine ⟨Wo, hWo, ?_⟩
  ext k
  constructor
  · intro hk
    refine ⟨((c.mem_overlap_recentre_iff c'' T hT e he).1 hk).1, ?_⟩
    have : k ∈ (c''.toMChart hP) '' (c''.toPartialEquiv.source ∩
        (c.recentre T hT e he).toPartialEquiv.source) := hk
    rw [hWoeq] at this; exact this.2
  · rintro ⟨hk, hkW⟩
    have : k ∈ (c''.toMChart hP).model.O ∩ Wo := ⟨c''.overlap_subset_K c hk, hkW⟩
    rw [← hWoeq] at this; exact this

variable {c c''} in
/-- **Compatibility passes to the re-centred chart**: if `c` is compatible with `c''`, so is the
re-centred chart `c_e`.  Its transition maps are `(Φ'' ∘ Φ⁻¹) ∘ (u, h) ↦ (u + e, h)` and
`(u, h) ↦ (u − e, h) ∘ (Φ ∘ Φ''⁻¹)` on `[0]` and `[1]` (translations by the smooth vector
`(e, 0)`, sc-smooth on both structures). -/
theorem Compatible.recentre (hP : Continuous P) (hcc : c.Compatible c'') :
    (c.recentre T hT e he).Compatible c'' := by
  have hG := isOpen_recentreNbhd T e
  have hO := c.isScRetract_overlap c'' hP
  have hO1 := c.isScRetract_overlap_one c'' hP
  have hO'' := c''.isScRetract_overlap c hP
  have hO''1 := c''.isScRetract_overlap_one c hP
  obtain ⟨Wo, hWo, hWoeq⟩ := c.overlap_recentre_eq c'' T hT e he hP
  have hov := c.recentre_overlap c'' T hT e he
  have hmapT : ∀ k ∈ c.overlap c'' ∩ (recentreNbhd T e ×ˢ univ),
      c.transition c'' k ∈ c''.overlap (c.recentre T hT e he) := by
    rintro _ ⟨⟨y, ⟨hy, hy''⟩, rfl⟩, hG', -⟩
    rw [c.transition_apply c'' hy]
    exact ⟨y, ⟨hy'', (c.mem_recentre_source_iff T hT e he).2 ⟨hy, hG'⟩⟩, rfl⟩
  have hmapT' : ∀ k ∈ c''.overlap (c.recentre T hT e he),
      c''.transition c k ∈ c.overlap c'' ∩ (recentreNbhd T e ×ˢ univ) := by
    intro k hk
    obtain ⟨hk1, hkG⟩ := (c.mem_overlap_recentre_iff c'' T hT e he).1 hk
    obtain ⟨y, ⟨hy'', hy⟩, rfl⟩ := hk1
    rw [c''.transition_apply c hy''] at hkG ⊢
    exact ⟨⟨y, ⟨hy, hy''⟩, rfl⟩, hkG, mem_univ _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `[0]`, `c_e → c''`: `(Φ'' ∘ Φ⁻¹) ∘ (· + (e, 0))`
    have h1 : IsScSmoothRetractMap (c.φ.model.E.prod c.F) (partialQuadrantAtWith T e ×ˢ univ)
        ((c.recentre T hT e he).overlap c'') (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ)
        (c.overlap c'') (addFst e) :=
      isScSmoothRetractMap_of_isScSmooth_univ (isScSmooth_addFst he (isScDomain_univ _)) (by
        rw [hov]; rintro _ ⟨k, hk, rfl⟩; rw [addFst_subFst]; exact hk.1)
    refine (hcc.1.comp h1 hO).mono_target ?_
    rw [hov]
    rintro _ ⟨k, hk, rfl⟩
    change c.transition c'' (addFst e (subFst e k)) ∈ _
    rw [addFst_subFst]
    exact hmapT k hk
  · -- `[0]`, `c'' → c_e`: `(· − (e, 0)) ∘ (Φ ∘ Φ''⁻¹)`
    have g1 : IsScSmoothRetractMap (c''.φ.model.E.prod c''.F) (c''.φ.model.C ×ˢ univ)
        (c''.overlap (c.recentre T hT e he)) (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ)
        (c.overlap c'' ∩ (recentreNbhd T e ×ˢ univ)) (c''.transition c) := by
      rw [hWoeq]
      exact (hcc.2.1.restrict hO'').mono_target (by rw [← hWoeq]; exact hmapT')
    have g2 : IsScSmoothRetractMap (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ)
        (c.overlap c'' ∩ (recentreNbhd T e ×ˢ univ)) (c.φ.model.E.prod c.F)
        (partialQuadrantAtWith T e ×ˢ univ) ((c.recentre T hT e he).overlap c'') (subFst e) :=
      isScSmoothRetractMap_of_isScSmooth_univ (isScSmooth_subFst he (isScDomain_univ _)) (by
        rw [hov]; exact mapsTo_image _ _)
    exact g2.comp g1 (proposition_2_10_1 hO (hG.prod isOpen_univ))
  · -- `[1]`, `c_e → c''`
    have h1 : IsScSmoothRetractMap (c.φ.model.E.prod c.F.shift)
        (partialQuadrantAtWith T e ×ˢ univ) (strongShiftOne ((c.recentre T hT e he).overlap c''))
        (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ) (strongShiftOne (c.overlap c''))
        (addFst e) :=
      isScSmoothRetractMap_of_isScSmooth_univ
        (isScSmooth_addFst (F := c.F.shift) he (isScDomain_univ _)) (fun p hp => by
          have hp' : (p.1, c.F.toBase 1 p.2) ∈ (c.recentre T hT e he).overlap c'' := hp
          rw [hov] at hp'
          obtain ⟨k, hk, hkp⟩ := hp'
          change addFst e (p.1, c.F.toBase 1 p.2) ∈ c.overlap c''
          rw [← hkp, addFst_subFst]
          exact hk.1)
    refine (hcc.2.2.1.comp h1 hO1).mono_target fun p hp => ?_
    have hp' : (p.1, c.F.toBase 1 p.2) ∈ (c.recentre T hT e he).overlap c'' := hp
    rw [hov] at hp'
    obtain ⟨k, hk, hkp⟩ := hp'
    have hkk : addFst e (p.1, c.F.toBase 1 p.2) = k := by rw [← hkp, addFst_subFst]
    have hr := hcc.2.2.2.2.1 k hk.1 (by rw [← hkk]; exact ⟨p.2, rfl⟩)
    change ((c.transition c'' (addFst e (p.1, c.F.toBase 1 p.2))).1,
      c''.F.toBase 1 (Function.invFun (c''.F.toBase 1)
        (c.transition c'' (addFst e (p.1, c.F.toBase 1 p.2))).2)) ∈
          c''.overlap (c.recentre T hT e he)
    rw [hkk, Function.invFun_eq hr]
    exact hmapT k hk
  · -- `[1]`, `c'' → c_e`
    have hss : strongShiftOne (c''.overlap (c.recentre T hT e he)) =
        strongShiftOne (c''.overlap c) ∩ (c''.φ.model.E.prodShiftInclOp c''.F 0) ⁻¹' Wo := by
      rw [hWoeq]; rfl
    have g1 : IsScSmoothRetractMap (c''.φ.model.E.prod c''.F.shift) (c''.φ.model.C ×ˢ univ)
        (strongShiftOne (c''.overlap (c.recentre T hT e he))) (c.φ.model.E.prod c.F.shift)
        (c.φ.model.C ×ˢ univ) (strongShiftOne (c.overlap c'') ∩ (recentreNbhd T e ×ˢ univ))
        (shiftFiber (c''.transition c)) := by
      rw [hss]
      refine (hcc.2.2.2.1.restrict hO''1).mono_target ?_
      rintro p ⟨hp, hpW⟩
      have hk : (p.1, c''.F.toBase 1 p.2) ∈ c''.overlap (c.recentre T hT e he) := by
        rw [hWoeq]; exact ⟨hp, hpW⟩
      have hr := hcc.2.2.2.2.2 _ hp ⟨p.2, rfl⟩
      have hm := hmapT' _ hk
      refine ⟨?_, hm.2.1, mem_univ _⟩
      change ((c''.transition c (p.1, c''.F.toBase 1 p.2)).1,
        c.F.toBase 1 (Function.invFun (c.F.toBase 1)
          (c''.transition c (p.1, c''.F.toBase 1 p.2)).2)) ∈ c.overlap c''
      rw [Function.invFun_eq hr]
      exact hm.1
    have g2 : IsScSmoothRetractMap (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ)
        (strongShiftOne (c.overlap c'') ∩ (recentreNbhd T e ×ˢ univ))
        (c.φ.model.E.prod c.F.shift) (partialQuadrantAtWith T e ×ˢ univ)
        (strongShiftOne ((c.recentre T hT e he).overlap c'')) (subFst e) :=
      isScSmoothRetractMap_of_isScSmooth_univ
        (isScSmooth_subFst (F := c.F.shift) he (isScDomain_univ _)) (fun p hp => by
          change subFst e (p.1, c.F.toBase 1 p.2) ∈ (c.recentre T hT e he).overlap c''
          rw [hov]
          exact ⟨_, ⟨hp.1, hp.2.1, mem_univ _⟩, rfl⟩)
    exact g2.comp g1 (proposition_2_10_1 hO1 (hG.prod isOpen_univ))
  · -- the fibre condition on `F₁`, `c_e → c''`
    intro x hx hx2
    rw [hov] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    change (c.transition c'' (addFst e (subFst e k))).2 ∈ _
    rw [addFst_subFst]
    exact hcc.2.2.2.2.1 k hk.1 hx2
  · -- the fibre condition on `F₁`, `c'' → c_e`
    intro x hx hx2
    exact hcc.2.2.2.2.2 x ((c.mem_overlap_recentre_iff c'' T hT e he).1 hx).1 hx2

end StrongBundleChart

namespace StrongBundle

variable [T2Space Y] [ParacompactSpace Y] {B : StrongBundle PX P}

/-- **The re-centred strong bundle chart is a strong bundle chart of `P`** (compatible with the
atlas of `B`): for a strong bundle chart `c` of `P`, a presentation `T` of `C` and a smooth
`e ∈ C`, the chart `c_e` with `R_e(u, h) = (r(u + e) − e, Γ(u + e, h))` over `φ_e = φ − e`
satisfies `B.IsChart`. -/
theorem IsChart.recentre {c : StrongBundleChart PX P} (hc : B.IsChart c) {n : ℕ} {W : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n W 0) (e : c.φ.model.E 0)
    (he : e ∈ c.φ.model.E.smooth) : B.IsChart (c.recentre T hT e he) :=
  fun c'' hc'' => (hc c'' hc'').recentre T hT e he B.continuous

end StrongBundle

end StrongCompat

/-! ### Centred charts at smooth points -/

section Centred

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **Every smooth point lies in a chart centred at it** (the charts `ψ(x) = 0` of Theorem 4.2 (ii),
of the proof of Theorem 4.18 and of Lemma 5.11): for a chart `φ` of `X` and `x ∈ dom φ ∩ X_∞`, the
re-centred chart `φ_x = φ − φ(x)` (on `V ∩ φ⁻¹(G(φ(x)))`, modelled in `C_{φ(x)}`) is a chart of the
M-polyfold with `φ_x(x) = 0`, the same degeneracy index as `φ` on its domain, and a tame model if
`φ` has one. -/
theorem MPolyfold.exists_centredChart {φ : MChart X} (hφ : P.IsChart φ) {x : X}
    (hx : x ∈ φ.source) (hs : x ∈ P.smoothSet) :
    ∃ χ : MChart X, P.IsChart χ ∧ x ∈ χ.source ∧ χ.source ⊆ φ.source ∧ χ x = 0 ∧
      (∀ y ∈ χ.source, MPolyfold.chartDegIndex χ y = MPolyfold.chartDegIndex φ y) ∧
      (IsTameRetract φ.model.E φ.model.C φ.model.O →
        IsTameRetract χ.model.E χ.model.C χ.model.O) := by
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have he : φ x ∈ φ.model.E.smooth := (MPolyfold.mem_smoothSet_iff hφ hx).1 hs
  exact ⟨φ.recentre T hT (φ x) he, φ.recentre_isChart T hT (φ x) he hφ,
    φ.mem_recentre_source T hT (φ x) he hx rfl, φ.recentreSource_subset T (φ x),
    φ.recentre_apply_self T hT (φ x) he rfl, fun y hy => φ.chartDegIndex_recentre T hT (φ x) he hy,
    φ.isTameRetract_recentre T hT (φ x) he⟩

/-- **In a tame M-polyfold every smooth point lies in a tame chart centred at it** (Theorem 4.2 (ii)
"every point `x ∈ X` is contained in a tame sc-smooth polyfold chart `(V, ψ, (O, C, E))` satisfying
`ψ(x) = 0`", for `x ∈ X_∞`). -/
theorem MPolyfold.IsTame.exists_centredChart (hP : P.IsTame) {x : X} (hs : x ∈ P.smoothSet) :
    ∃ χ : MChart X, P.IsChart χ ∧ x ∈ χ.source ∧ χ x = 0 ∧
      IsTameRetract χ.model.E χ.model.C χ.model.O := by
  obtain ⟨φ, hφ, hx, htame⟩ := MPolyfold.IsTame.exists_chart P hP x
  obtain ⟨χ, hχ, hxχ, -, h0, -, ht⟩ := MPolyfold.exists_centredChart hφ hx hs
  exact ⟨χ, hχ, hxχ, h0, ht htame⟩

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Pr : Y → X}
  [∀ x, AddCommGroup (Pr ⁻¹' {x})] [∀ x, Module ℝ (Pr ⁻¹' {x})] {B : StrongBundle P Pr}

/-- **Every smooth point of the base lies in a strong bundle chart centred at it** (the centred
strong bundle charts of Lemma 5.11): for a strong bundle chart `c` of `P` and
`x ∈ dom φ ∩ X_∞`, the re-centred chart `c_x` (only the base translated) is a strong bundle chart of
`P` with `φ_x(x) = 0` on smaller domains. -/
theorem StrongBundle.IsChart.exists_centred {c : StrongBundleChart P Pr} (hc : B.IsChart c)
    {x : X} (hx : x ∈ c.φ.source) (hs : x ∈ P.smoothSet) :
    ∃ c' : StrongBundleChart P Pr, B.IsChart c' ∧ x ∈ c'.φ.source ∧ c'.φ x = 0 ∧
      c'.φ.source ⊆ c.φ.source ∧ c'.toPartialEquiv.source ⊆ c.toPartialEquiv.source := by
  obtain ⟨n, W, T, hT⟩ := c.φ.model.isPartialQuadrant
  have he : c.φ x ∈ c.φ.model.E.smooth := (MPolyfold.mem_smoothSet_iff c.isChart hx).1 hs
  refine ⟨c.recentre T hT (c.φ x) he, hc.recentre T hT (c.φ x) he,
    c.φ.mem_recentre_source T hT (c.φ x) he hx rfl, c.φ.recentre_apply_self T hT (c.φ x) he rfl,
    c.φ.recentreSource_subset T (c.φ x), fun y hy => ?_⟩
  exact ((c.mem_recentre_source_iff T hT (c.φ x) he).1 hy).1

end Centred

end Polyfold
