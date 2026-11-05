import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_56

open Set Filter Topology Function Module

noncomputable section

namespace RoundTrip.V3_56
open Polyfold

/-- The project's statement: `proposition_3_69` (no universe parameters).  `QuadrantNormalForm`
is vocabulary. -/
def A : Prop := type_of% @Polyfold.proposition_3_69

theorem A_holds : A := @Polyfold.proposition_3_69

/-- `N ∩ W` as a subspace of `N` (the project's `ker (fst ∘ ι_N)`) has the dimension of the
blind `N ⊓ Wsub`. -/
lemma finrank_ker_fst_eq (n : ℕ) (W : ScBanach) (N : Submodule ℝ ((Emod n W).lvl 0))
    [FiniteDimensional ℝ N] :
    finrank ℝ (LinearMap.ker ((LinearMap.fst ℝ (Fin n → ℝ) (W.lvl 0)).comp N.subtype)) =
      finrank ℝ (N ⊓ Wsub n W : Submodule ℝ _) := by
  have h1 : LinearMap.ker ((LinearMap.fst ℝ (Fin n → ℝ) (W.lvl 0)).comp N.subtype) =
      (Wsub n W).comap N.subtype := by
    ext z
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    change (z : (Fin n → ℝ) × W.lvl 0).1 = 0 ↔ ∀ i, (z : (Fin n → ℝ) × W.lvl 0).1 i = 0
    exact ⟨fun h i => congrFun h i, fun h => funext h⟩
  rw [h1, ← Submodule.map_comap_subtype]
  exact (Submodule.equivMapOfInjective N.subtype N.injective_subtype _).finrank_eq

/-- A ⇒ B: the blind good position (sc-complement) gives the project's (algebraic complement);
`d_C = dC` on the quadrant; (2) is the project's additive form. -/
theorem A_to_B : A → B := by
  intro hA n W N _ _ hgp x hx
  obtain ⟨hint, Y, hsplit, ε, hε, hgood⟩ := hgp
  have hNY : IsCompl N Y := by simpa using hsplit.2.2 0
  have hN : IsInGoodPosition _ (quadrant n W 0) N := ⟨hint, Y, ⟨hNY, ε, hε, hgood⟩⟩
  obtain ⟨h1, h2⟩ := hA hN hx
  rw [show quadC n W = quadrant n W 0 from rfl]
  refine ⟨fun hxW => ?_, fun hxW => ?_⟩
  · have hx1 : (x : (Fin n → ℝ) × W.lvl 0).1 ≠ 0 := fun h => hxW fun i => congrFun h i
    rw [h1 hx1, degIndex_quadrant hx]
    rfl
  · have hx1 : (x : (Fin n → ℝ) × W.lvl 0).1 = 0 := funext hxW
    have := h2 hx1
    rw [finrank_ker_fst_eq] at this
    exact Nat.eq_sub_of_add_eq this

#rt_check RoundTrip.V3_56.A_to_B [Polyfold.proposition_3_69]

/-- The degeneracy index is carried by an sc-isomorphism (Lemma 1.24 for the presentation
`T ∘ S`); `0` on both sides if the set is not a partial quadrant. -/
lemma degIndex_scIso {E F : ScBanach} (S : ScIso E F) (C : Set (F 0)) {x : E 0}
    (hx : S 0 x ∈ C) : degIndex E (S 0 ⁻¹' C) x = degIndex F C (S 0 x) := by
  classical
  by_cases hC : IsPartialQuadrant F C
  · obtain ⟨n, W, T, rfl⟩ := hC
    have h2 : degIndex E (S 0 ⁻¹' (T 0 ⁻¹' quadrant n W 0)) x = degIndexWith (S.trans T) x :=
      degIndex_eq (S.trans T) rfl hx
    rw [h2, degIndex_eq T rfl hx]
    rfl
  · have hC' : ¬ IsPartialQuadrant E (S 0 ⁻¹' C) := by
      rintro ⟨n, W, T, hT⟩
      refine hC ⟨n, W, S.symm.trans T, ?_⟩
      ext y
      have h := Set.ext_iff.1 hT ((S 0).symm y)
      simp only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] at h
      exact h
    rw [degIndex, dif_neg hC', degIndex, dif_neg hC]

/-- If every point of `E₀` is smooth, every algebraic splitting into closed subspaces is an
sc-splitting. -/
lemma isScSplitting_of_smooth_eq_top (E : ScBanach) (hE : E.smooth = ⊤)
    {N P : Submodule ℝ (E 0)} (hN : IsClosed (N : Set (E 0))) (hP : IsClosed (P : Set (E 0)))
    (h : IsCompl N P) : E.IsScSplitting N P := by
  have hsurj : ∀ m (y : E 0), ∃ z : E m, E.toBase m z = y := fun m y =>
    (ScScale.mem_smooth_iff _).1 (by rw [hE]; exact Submodule.mem_top) m
  have hsm : ∀ m, E.smoothLvl m = univ := fun m => by
    ext z
    simp only [ScScale.smoothLvl, mem_preimage, hE, Submodule.top_coe, mem_univ]
  have hsub : ∀ A : Submodule ℝ (E 0), IsClosed (A : Set (E 0)) → E.IsScSubspace A :=
    fun A hA => ⟨hA, fun m => by rw [hsm m, inter_univ]; exact subset_closure⟩
  refine ⟨hsub N hN, hsub P hP, fun m => IsCompl.of_eq ?_ ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    rw [Submodule.mem_inf] at hz
    have h0 : E.toBase m z ∈ N ⊓ P := Submodule.mem_inf.2 ⟨hz.1, hz.2⟩
    rw [h.inf_eq_bot, Submodule.mem_bot] at h0
    rw [Submodule.mem_bot]
    exact E.toBase_injective m (by rw [h0, map_zero])
  · rw [eq_top_iff]
    intro z _
    have hz : E.toBase m z ∈ N ⊔ P := by rw [h.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hz
    obtain ⟨a', ha'⟩ := hsurj m a
    obtain ⟨b', hb'⟩ := hsurj m b
    have hz' : z = a' + b' := E.toBase_injective m (by rw [map_add, ha', hb', hab])
    rw [hz']
    exact Submodule.add_mem_sup (show E.toBase m a' ∈ N by rw [ha']; exact ha)
      (show E.toBase m b' ∈ P by rw [hb']; exact hb)

/-- B ⇒ A: the project's `N` (not necessarily smooth, algebraic good complement `P`) is moved
into the finite-dimensional model `ℝⁿ ⊕ K`, `K = pr_W(N) ⊆ W₀` with the constant sc-structure,
by the isometric embedding `j(a, k) = (a, k)`; there every point is smooth, every algebraic
splitting is an sc-splitting, and `j⁻¹(P)` is a good complement of `j⁻¹(N) ≅ N`.  `B` is applied
there and the degeneracy index is carried back along `j⁻¹(N) ≅ N` (`degIndex_scIso`). -/
theorem B_to_A : B → A := by
  intro hB n W N _ hN x hx
  classical
  set K : Submodule ℝ (W.lvl 0) :=
    N.map (LinearMap.snd ℝ (Fin n → ℝ) (W.lvl 0) : (Emod n W).lvl 0 →ₗ[ℝ] W.lvl 0) with hK
  set W' : ScBanach := ScBanach.const K with hW'
  let j : (Emod n W').lvl 0 →ₗ[ℝ] (Emod n W).lvl 0 :=
    LinearMap.prodMap LinearMap.id K.subtype
  have hj : ∀ v : (Emod n W').lvl 0, j v = ((v.1, (v.2 : W.lvl 0)) : (Fin n → ℝ) × W.lvl 0) :=
    fun v => rfl
  have hj_inj : Injective j := by
    intro v w h
    have h1 : (j v).1 = (j w).1 := congrArg Prod.fst h
    have h2 : (j v).2 = (j w).2 := congrArg Prod.snd h
    exact Prod.ext h1 (Subtype.ext h2)
  have hj_norm : ∀ v, ‖j v‖ = ‖v‖ := fun v => rfl
  have hNj : ∀ y ∈ N, ∃ v, j v = y := fun y hy =>
    ⟨(y.1, ⟨y.2, Submodule.mem_map_of_mem hy⟩), rfl⟩
  set N' : Submodule ℝ ((Emod n W').lvl 0) := N.comap j with hN'
  obtain ⟨P, hP⟩ := hN.exists_goodComplement
  obtain ⟨ε, hε, hgood⟩ := hP.exists_eps
  set P' : Submodule ℝ ((Emod n W').lvl 0) := P.comap j with hP'
  have hsm : (Emod n W').smooth = ⊤ := ScBanach.smooth_eq_top_of_finiteDimensional _
  have hcompl : IsCompl N' P' := by
    refine IsCompl.of_eq ?_ ?_
    · rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_inf] at hv
      have h0 : j v ∈ N ⊓ P := Submodule.mem_inf.2 ⟨hv.1, hv.2⟩
      rw [hP.isCompl.inf_eq_bot, Submodule.mem_bot] at h0
      rw [Submodule.mem_bot]
      exact hj_inj (by rw [h0, map_zero])
    · rw [eq_top_iff]
      intro v _
      have hv : j v ∈ N ⊔ P := by rw [hP.isCompl.sup_eq_top]; trivial
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hv
      obtain ⟨a', rfl⟩ := hNj a ha
      have hb' : v - a' ∈ P' := by
        show j (v - a') ∈ P
        rw [map_sub, ← hab, add_sub_cancel_left]
        exact hb
      exact Submodule.mem_sup.2 ⟨a', ha, v - a', hb', add_sub_cancel a' v⟩
  -- `N' ≅ N`
  let e0 : N' →ₗ[ℝ] N := (j.comp N'.subtype).codRestrict N fun v => v.2
  have he0 : ∀ w : N', ((e0 w : N) : (Emod n W).lvl 0) = j w := fun w => rfl
  have he_bij : Bijective e0 := by
    refine ⟨fun a b h => Subtype.ext (hj_inj (congrArg Subtype.val h)), fun y => ?_⟩
    obtain ⟨v, hv⟩ := hNj y y.2
    exact ⟨⟨v, show j v ∈ N by rw [hv]; exact y.2⟩, Subtype.ext hv⟩
  let e : N' ≃ₗ[ℝ] N := LinearEquiv.ofBijective e0 he_bij
  have he : ∀ w : N', ((e w : N) : (Emod n W).lvl 0) = j w := fun w => rfl
  -- good position of `N'` in the finite-dimensional model
  have hgp : IsInGoodPositionSc (Emod n W') (quadC n W') N' := by
    refine ⟨?_, P', isScSplitting_of_smooth_eq_top _ hsm (Submodule.closed_of_finiteDimensional _)
      (Submodule.closed_of_finiteDimensional _) hcompl, ε, hε, ?_⟩
    · obtain ⟨y, hy⟩ := hN.interior_nonempty
      let ψ : N' ≃ₜ N := e.toContinuousLinearEquiv.toHomeomorph
      have hpre : ψ ⁻¹' (Subtype.val ⁻¹' quadrant n W 0 : Set N) =
          (Subtype.val ⁻¹' quadC n W' : Set N') := by
        ext v; rfl
      refine ⟨ψ.symm y, ?_⟩
      rw [← hpre, ← ψ.preimage_interior, mem_preimage, ψ.apply_symm_apply]
      exact hy
    · intro y hy p hp hle
      have h := hgood (j y) hy (j p) hp (by rw [hj_norm, hj_norm]; exact hle)
      rw [← map_add] at h
      exact h
  have hNs : N' ≤ (Emod n W').smooth := by rw [hsm]; exact le_top
  -- the point
  set x' : N' := e.symm x with hx'def
  have hjx : j (x' : (Emod n W').lvl 0) = (x : (Emod n W).lvl 0) := by
    rw [← he, hx'def, e.apply_symm_apply]
  have hx'1 : (x' : (Fin n → ℝ) × K).1 = (x : (Fin n → ℝ) × W.lvl 0).1 := congrArg Prod.fst hjx
  have hx'C : (x' : (Emod n W').lvl 0) ∈ quadC n W' := by
    intro i
    show 0 ≤ (x' : (Fin n → ℝ) × K).1 i
    rw [hx'1]; exact hx i
  obtain ⟨hB1, hB2⟩ := hB n W' N' hNs hgp x' hx'C
  -- the degeneracy index along `N' ≅ N`
  let S : ScIso (ScBanach.const N') (ScBanach.const N) :=
    { lvl := fun _ => e.toContinuousLinearEquiv
      incl_comm := fun _ _ => rfl }
  have hSx : S 0 x' = x := e.apply_symm_apply x
  have hdeg : degIndex (ScBanach.const N) (Subtype.val ⁻¹' quadrant n W 0) x =
      degIndex (ScBanach.const N') (Subtype.val ⁻¹' quadC n W') x' := by
    have h1 := degIndex_scIso S (Subtype.val ⁻¹' quadrant n W 0 : Set N) (x := x')
      (by rw [hSx]; exact hx)
    have hset : (S 0 ⁻¹' (Subtype.val ⁻¹' quadrant n W 0 : Set N)) =
        (Subtype.val ⁻¹' quadC n W' : Set N') := by
      ext v; rfl
    rw [hset, hSx] at h1
    exact h1.symm
  refine ⟨fun hx1 => ?_, fun hx1 => ?_⟩
  · have hx'W : (x' : (Emod n W').lvl 0) ∉ Wsub n W' := fun h =>
      hx1 (by rw [← hx'1]; exact funext h)
    rw [hdeg, hB1 hx'W, degIndex_quadrant hx]
    show (Finset.univ.filter fun i => (x' : (Fin n → ℝ) × K).1 i = 0).card =
      (Finset.univ.filter fun i => (x : (Fin n → ℝ) × W.lvl 0).1 i = 0).card
    rw [hx'1]
  · have hx'W : (x' : (Emod n W').lvl 0) ∈ Wsub n W' := fun i => by
      show (x' : (Fin n → ℝ) × K).1 i = 0
      rw [hx'1, hx1]; rfl
    have h2 := hB2 hx'W
    have hrank1 : finrank ℝ N' = finrank ℝ N := e.finrank_eq
    have hker : LinearMap.ker ((LinearMap.fst ℝ (Fin n → ℝ) (W.lvl 0)).comp N.subtype) =
        (LinearMap.ker ((LinearMap.fst ℝ (Fin n → ℝ) (W'.lvl 0)).comp N'.subtype)).map
          (e : N' →ₗ[ℝ] N) := by
      ext z
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        Submodule.coe_subtype, LinearMap.fst_apply, Submodule.mem_map]
      constructor
      · intro hz
        refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
        have h3 : j ((e.symm z : N') : (Emod n W').lvl 0) = (z : (Emod n W).lvl 0) := by
          rw [← he, e.apply_symm_apply]
        have h4 := congrArg Prod.fst h3
        exact h4.trans hz
      · rintro ⟨w, hw, rfl⟩
        exact hw
    have hrank2 : finrank ℝ (N' ⊓ Wsub n W' : Submodule ℝ _) =
        finrank ℝ (LinearMap.ker ((LinearMap.fst ℝ (Fin n → ℝ) (W.lvl 0)).comp N.subtype)) := by
      rw [← finrank_ker_fst_eq n W' N', hker, LinearEquiv.finrank_map_eq]
    have hle : finrank ℝ (N' ⊓ Wsub n W' : Submodule ℝ _) ≤ finrank ℝ N' := by
      rw [← finrank_ker_fst_eq n W' N']; exact Submodule.finrank_le _
    rw [hdeg, h2, ← hrank2, ← hrank1]
    exact Nat.sub_add_cancel hle

#rt_check RoundTrip.V3_56.B_to_A [Polyfold.proposition_3_69]
#rt_overlap RoundTrip.V3_56.B_to_A [Polyfold.proposition_3_69]

end RoundTrip.V3_56
