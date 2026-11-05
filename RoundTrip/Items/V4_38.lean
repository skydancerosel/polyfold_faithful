import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_38

/-!
Round trip for V4_38 (Definition 4.16).  The item lists the definitions `IsGoodPositionRetractAt`,
`SubmanifoldData.IsGoodPositionChart`, `MPolyfold.IsGoodPositionAt` and one theorem,
`Polyfold.MPolyfold.SubmanifoldData.isGoodPositionChart_iff` (the explicit chart form
`Dt(z)E` in good position to `C_z` inside `Dr(z)E`); so `A` is the type of that theorem
(universe `0`).

The content of the item is B: the project's `IsGoodPositionAt` is the text's notion read in a
chart (B's `IsGoodPositionAtB`), for tame `X`, a smooth submanifold `A` and `a ∈ A`.  It is proved
outright (`B_holds`); `A` plays no role in it, and `B` plays no role in `A` (re-proved outright
in `B_to_A`): both directions are vacuous for the audit and flagged.

Differences between the two definitions, and the glue:
* B asks `V ⊆ dom φ` for the data of Definition 4.13 and uses `φ(A ∩ V)`; the project allows any
  data with `a ∈ V`, `a ∈ dom φ` and uses the shrunk set `W = V ∩ dom φ ∩ s⁻¹(V ∩ dom φ)`.
  Project ⇒ B: replace `V` by `W` (an sc⁺-retraction restricts to the open `s`-invariant `W`);
  B ⇒ project: when `V ⊆ dom φ`, `W = V`.
* B's cone is `T_zO ∩ C_z`, the project's `C_z` (equal on vectors of `T_zO`).
* **B's good complement is an sc-complement inside `T_zO`; the project's only an algebraic
  complement.**  B ⇒ project is immediate (level `0`).  Project ⇒ B needs the tameness of `X`
  (B's hypothesis): in a tame chart `ψ` centred at `a` (`IsTame.exists_centredChart`), `N` is in
  good position to `C` in `E` (`IsGoodPositionAt.isInGoodPosition_of_tame`, Lemma 4.19 through
  chart independence), `N = Dt(0)E` is finite-dimensional and smooth (Lemma 4.7 for the
  sc⁺-retraction `t` of `exists_chartRetraction`), `T₀O = Dr(0)E` is an sc-subspace, and the
  closed good complement of `exists_proj_goodComplement` cut down to `T₀O` is an sc-complement
  (`isGoodPositionInB_of`, the upgrade of V3_82).
-/

namespace RoundTrip.V4_38
open Polyfold

def A : Prop := type_of% @Polyfold.MPolyfold.SubmanifoldData.isGoodPositionChart_iff.{0}

theorem A_holds : A := @Polyfold.MPolyfold.SubmanifoldData.isGoodPositionChart_iff.{0}

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

/-- Definition 4.13: the project's notion is B's (V4_29/V4_33). -/
theorem smooth_iff (P : MPolyfold X) (S : Set X) :
    P.IsSmoothSubmanifold S ↔ IsSmoothSubmanifoldB P S := by
  constructor
  · intro h a ha
    obtain ⟨V, hV, haV, s, hs, himg⟩ := h a ha
    exact ⟨V, s, hV, haV, (retractionOn_iff P s V).1 hs, himg⟩
  · intro h a ha
    obtain ⟨V, s, hV, haV, hs, himg⟩ := h a ha
    exact ⟨V, hV, haV, s, (retractionOn_iff P s V).2 hs, himg⟩

end Glue

section GoodPosition

open Set

/-- B's good position inside `M` (sc-complement, cone `M ∩ K`) gives the project's (algebraic
complement, cone `K`). -/
theorem isInGoodPositionIn_of_B {E : ScBanach} {M N : Submodule ℝ (E 0)} {K : Set (E 0)}
    (h : IsGoodPositionInB E M ((M : Set (E 0)) ∩ K) N) : IsInGoodPositionIn E M K N := by
  obtain ⟨hNM, hint, Y, hYM, -, hsplit, ε, hε, hgood⟩ := h
  have hpre : (Subtype.val ⁻¹' ((M : Set (E 0)) ∩ K) : Set N) = Subtype.val ⁻¹' K := by
    ext ⟨n, hn⟩
    simp only [mem_preimage, mem_inter_iff, SetLike.mem_coe]
    exact ⟨fun h => h.2, fun h => ⟨hNM hn, h⟩⟩
  have h0 := hsplit 0
  simp only [ScBanach.levelSub_zero] at h0
  refine ⟨hNM, hpre ▸ hint, Y, hYM, h0.1, h0.2, ε, hε, fun n hn p hp hle => ?_⟩
  have h := hgood n hn p hp hle
  have hnM : n ∈ M := hNM hn
  have hnpM : n + p ∈ M := M.add_mem hnM (hYM hp)
  simp only [mem_inter_iff, SetLike.mem_coe] at h
  exact ⟨fun hc => (h.1 ⟨hnM, hc⟩).2, fun hc => (h.2 ⟨hnpM, hc⟩).2⟩

/-- **The sc good complement** (the upgrade of V3_82, `isInGoodPositionSc_of`, with B's
packaging): if the finite-dimensional smooth subspace `N` of the sc-subspace `M` is in good
position to the partial quadrant `C` in `E`, then it is in good position to `M ∩ C` inside `M`
with an sc-complement `Y ∩ M`, `Y` a closed good complement (`exists_proj_goodComplement`). -/
theorem isGoodPositionInB_of {E : ScBanach} {C : Set (E 0)} (hC : IsPartialQuadrant E C)
    {T N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N] (hT : E.IsScSubspace T) (hNT : N ≤ T)
    (hNs : N ≤ E.smooth) (hgp : IsInGoodPosition E C N) :
    IsGoodPositionInB E T ((T : Set (E 0)) ∩ C) N := by
  obtain ⟨π, hπN, -, hY⟩ := exists_proj_goodComplement hC hgp
  set Y := LinearMap.ker (π : E 0 →ₗ[ℝ] N) with hYdef
  have hYc : IsClosed (Y : Set (E 0)) := π.isClosed_ker
  have hlift : ∀ m, ∀ n : N, ∃ y : E m, E.toBase m y = n := fun m n =>
    (E.mem_smooth_iff.1 (hNs n.2)) m
  have hπY : ∀ {z : E 0}, z ∈ Y ↔ π z = 0 := fun {z} => LinearMap.mem_ker
  refine ⟨hNT, ?_, Y ⊓ T, inf_le_right, ⟨hYc.inter hT.1, ?_⟩, fun m => ⟨?_, ?_⟩, ?_⟩
  · have hpre : (Subtype.val ⁻¹' ((T : Set (E 0)) ∩ C) : Set N) = Subtype.val ⁻¹' C := by
      ext ⟨n, hn⟩
      simp only [mem_preimage, mem_inter_iff, SetLike.mem_coe]
      exact ⟨fun h => h.2, fun h => ⟨hNT hn, h⟩⟩
    rw [hpre]; exact hgp.interior_nonempty
  · intro m x hx
    let fN : E.levelSub N m →ₗ[ℝ] N :=
      ((E.toBase m : E m →ₗ[ℝ] E 0).restrict (p := E.levelSub N m) (q := N) fun _ hz => hz)
    have hfN : Function.Bijective fN := by
      refine ⟨fun a b hab => Subtype.ext (E.toBase_injective m ?_), fun n => ?_⟩
      · exact congrArg Subtype.val hab
      · obtain ⟨y, hy⟩ := hlift m n
        exact ⟨⟨y, show E.toBase m y ∈ N by rw [hy]; exact n.2⟩, Subtype.ext hy⟩
    let eN := LinearEquiv.ofBijective fN hfN
    let L : N →L[ℝ] E m :=
      LinearMap.toContinuousLinearMap ((E.levelSub N m).subtype ∘ₗ (eN.symm : N →ₗ[ℝ] _))
    have hL : ∀ n : N, E.toBase m (L n) = n := fun n => by
      have := congrArg Subtype.val (eN.apply_symm_apply n)
      exact this
    let Φ : E m → E m := fun z => z - L (π (E.toBase m z))
    have hΦc : Continuous Φ :=
      continuous_id.sub (L.continuous.comp (π.continuous.comp (E.toBase m).continuous))
    have hΦx : Φ x = x := by
      have : π (E.toBase m x) = 0 := hπY.1 hx.1
      simp only [Φ, this, map_zero, sub_zero]
    have hΦS : Φ '' (E.levelSub T m ∩ E.smoothLvl m) ⊆ E.levelSub (Y ⊓ T) m ∩ E.smoothLvl m := by
      rintro _ ⟨t, ⟨htT, hts⟩, rfl⟩
      have hb : E.toBase m (Φ t) = E.toBase m t - (π (E.toBase m t) : E 0) := by
        simp only [Φ, map_sub, hL]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · change E.toBase m (Φ t) ∈ Y
        rw [hb, hπY, map_sub, hπN, sub_self]
      · change E.toBase m (Φ t) ∈ T
        rw [hb]; exact T.sub_mem htT (hNT (π _).2)
      · change E.toBase m (Φ t) ∈ E.smooth
        rw [hb]; exact E.smooth.sub_mem hts (hNs (π _).2)
    have hxT : x ∈ (E.levelSub T m : Set (E m)) := hx.2
    have h1 := hT.2 m hxT
    rw [← hΦx]
    exact closure_mono hΦS (image_closure_subset_closure_image hΦc (mem_image_of_mem Φ h1))
  · rw [eq_bot_iff]
    rintro x ⟨hxN, hxP⟩
    have h1 : E.toBase m x ∈ N ⊓ Y := ⟨hxN, hxP.1⟩
    rw [hY.isCompl.inf_eq_bot, Submodule.mem_bot] at h1
    exact (Submodule.mem_bot ℝ).2 (E.toBase_injective m (by rw [h1, map_zero]))
  · apply le_antisymm
    · exact sup_le (fun x hx => hNT hx) (fun x hx => hx.2)
    · intro x hx
      obtain ⟨y, hy⟩ := hlift m (π (E.toBase m x))
      have hyN : y ∈ E.levelSub N m := show E.toBase m y ∈ N by rw [hy]; exact (π _).2
      have hxy : x - y ∈ E.levelSub (Y ⊓ T) m := by
        refine ⟨?_, ?_⟩
        · change E.toBase m (x - y) ∈ Y
          rw [hπY, map_sub, map_sub, hy, hπN, sub_self]
        · change E.toBase m (x - y) ∈ T
          rw [map_sub]; exact T.sub_mem hx (hNT hyN)
      have := Submodule.add_mem_sup hyN hxy
      rwa [add_sub_cancel] at this
  · obtain ⟨ε, hε, hgood⟩ := hY.exists_eps
    refine ⟨ε, hε, fun n hn p hp hle => ?_⟩
    have h := hgood n hn p hp.1 hle
    simp only [mem_inter_iff, SetLike.mem_coe]
    exact ⟨fun h1 => ⟨T.add_mem (hNT hn) hp.2, h.1 h1.2⟩, fun h1 => ⟨hNT hn, h.2 h1.2⟩⟩

end GoodPosition

section Restrict

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {S : Set X}

/-- The sc⁺-retraction of Definition 4.13 restricts to the shrunk open set `W` of a chart. -/
theorem isScPlusRetractionOn_shrink (d : P.SubmanifoldData S) (φ : MChart X) :
    P.IsScPlusRetractionOn d.s (d.toSubData.shrink φ) :=
  ⟨d.isScPlusRetractionOn.isScSmoothOn.mono (d.toSubData.isOpen_shrink φ) fun _ hx => hx.1.1,
    d.toSubData.mapsTo_shrink φ, fun x hx => d.isScPlusRetractionOn.idem x hx.1.1,
    fun x hx => d.isScPlusRetractionOn.mem_levelSet x hx.1.1, fun x₀ =>
    (d.isScPlusRetractionOn.isScSmoothOn_one x₀).mono (d.toSubData.isOpen_shrink φ)
      fun _ hx => hx.1.1⟩

end Restrict

/-- **Definition 4.16**: the project's notion is B's (for tame `X`). -/
theorem B_holds : B := by
  intro X _ _ _ P S a hP hSB ha
  have hS : P.IsSmoothSubmanifold S := (smooth_iff P S).2 hSB
  constructor
  · intro h
    obtain ⟨ψ, hψ, haψ, hψ0, htame⟩ := hP.exists_centredChart (hS.subset_smoothSet ha)
    set d := hS.data ha
    have had : a ∈ d.V := hS.mem_data_V ha
    obtain ⟨n, Wq, T, hT⟩ := ψ.model.isPartialQuadrant
    have hz : ψ.model.E.toBase 1 0 = ψ a := by rw [map_zero, hψ0]
    obtain ⟨N, M, hN, hM, hgp⟩ := h.isGoodPositionChart d hψ T hT had haψ hz
    have hgpE : IsInGoodPosition ψ.model.E ψ.model.C N :=
      h.isInGoodPosition_of_tame d had hψ haψ hψ0 htame hN
    obtain ⟨R, hR⟩ := ψ.model.isScRetract
    have h01 : (0 : ψ.model.E 1) ∈ ψ.model.E.lvlSet R.retract 1 := by
      rw [ScBanach.mem_lvlSet, hR, hz]; exact ψ.mapsTo_model a haψ
    have hs0 : (0 : ψ.model.E 1) ∈ ψ.model.E.smoothLvl 1 := by
      change ψ.model.E.toBase 1 0 ∈ (ψ.model.E.smooth : Set (ψ.model.E 0))
      rw [map_zero]; exact ψ.model.E.smooth.zero_mem
    have hMR : M = LinearMap.range (scDeriv R.U R 0 : ψ.model.E 0 →ₗ[ℝ] ψ.model.E 0) := by
      refine SetLike.coe_injective (hM.trans ?_)
      rw [← hR]; exact tangentSpace_eq_coe_submodule R h01
    have hMsc : ψ.model.E.IsScSubspace M := hMR ▸ (R.isScSplitting_range_scDeriv h01 hs0).1
    obtain ⟨t, ht, htp, -⟩ :=
      d.exists_chartRetraction hψ (P.levelMk 1 a (hS.mem_levelSet_one ha)) R hR
    have h0t : (0 : ψ.model.E 1) ∈ ψ.model.E.lvlSet t.retract 1 := by
      rw [ScBanach.mem_lvlSet, ht, hz]
      exact ⟨a, ⟨d.toSubData.mem_shrink ψ ha had haψ, ha⟩, rfl⟩
    have hNt : N = LinearMap.range (scDeriv t.U t 0 : ψ.model.E 0 →ₗ[ℝ] ψ.model.E 0) := by
      refine SetLike.coe_injective (hN.trans ?_)
      rw [← ht]; exact tangentSpace_eq_coe_submodule t h0t
    have : FiniteDimensional ℝ N := by rw [hNt]; exact lemma_4_7_ii htp h0t
    have hNs : N ≤ ψ.model.E.smooth :=
      (ψ.model.E.proposition_1_6_iff N).1 (hNt ▸ (t.isScSplitting_range_scDeriv h0t hs0).1)
    refine ⟨d.toSubData.shrink ψ, d.s, ψ, n, Wq, T, 0, N, M,
      (retractionOn_iff P d.s _).1 (isScPlusRetractionOn_shrink d ψ), ?_,
      d.toSubData.mem_shrink ψ ha had haψ, hψ, d.toSubData.shrink_subset_source ψ, hT, hz, ?_, hM,
      ?_⟩
    · rw [Set.inter_comm]; exact d.toSubData.image_shrink ψ
    · rw [Set.inter_comm]; exact hN
    · rw [map_zero, partialQuadrantAtWith_zero, ← hT]
      exact isGoodPositionInB_of ⟨n, Wq, T, hT⟩ hMsc hgp.le hNs hgpE
  · rintro ⟨V, s, φ, n, Wq, T, z, N, M, hs, himg, haV, hφ, hVφ, hT, hz, hN, hM, hgp⟩
    let d : P.SubmanifoldData S := ⟨V, s, hs.1, (retractionOn_iff P s V).2 hs, himg⟩
    have hshrink : d.toSubData.shrink φ = V := by
      ext x
      simp only [MPolyfold.SubData.shrink, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · exact fun h => h.1.1
      · intro hx
        exact ⟨⟨hx, hVφ hx⟩, hs.2.2.1 hx, hVφ (hs.2.2.1 hx)⟩
    refine ⟨ha, d, φ, n, Wq, T, z, haV, hφ, hVφ haV, hT, hz, N, M, ?_, hM,
      isInGoodPositionIn_of_B hgp⟩
    rw [hshrink, Set.inter_comm]; exact hN

theorem A_to_B : A → B := fun _ => B_holds

/-- A re-proved outright (the chart form of the tangent spaces, `tangentSpace_eq_coe_submodule`),
without B. -/
theorem B_to_A : B → A := by
  intro _ X _ _ _ P S d φ n Wq T z R hR t ht hz
  have hzt : z ∈ φ.model.E.lvlSet t.retract 1 := by rw [ScBanach.mem_lvlSet, ht]; exact hz
  have hzR : z ∈ φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hR]
    exact φ.image_subset_model (fun _ hx => d.toSubData.shrink_subset_source φ hx.1) hz
  have hN : ((rangeS (scDeriv t.U t z) : Submodule ℝ (φ.model.E 0)) : Set (φ.model.E 0)) =
      tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ S)) z := by
    rw [← ht]; exact (tangentSpace_eq_coe_submodule t hzt).symm
  have hM : ((rangeS (scDeriv R.U R z) : Submodule ℝ (φ.model.E 0)) : Set (φ.model.E 0)) =
      tangentSpace φ.model.E φ.model.C φ.model.O z := by
    rw [← hR]; exact (tangentSpace_eq_coe_submodule R hzR).symm
  constructor
  · rintro ⟨N, M, hN', hM', hg⟩
    rw [SetLike.coe_injective (hN'.trans hN.symm), SetLike.coe_injective (hM'.trans hM.symm)] at hg
    exact hg
  · intro hg
    exact ⟨_, _, hN, hM, hg⟩

#rt_check RoundTrip.V4_38.A_to_B [Polyfold.MPolyfold.SubmanifoldData.isGoodPositionChart_iff]
#rt_check RoundTrip.V4_38.B_to_A [Polyfold.MPolyfold.SubmanifoldData.isGoodPositionChart_iff]
#rt_overlap RoundTrip.V4_38.B_to_A [Polyfold.MPolyfold.SubmanifoldData.isGoodPositionChart_iff]
#rt_check RoundTrip.V4_38.B_holds [Polyfold.MPolyfold.SubmanifoldData.isGoodPositionChart_iff]

end RoundTrip.V4_38
