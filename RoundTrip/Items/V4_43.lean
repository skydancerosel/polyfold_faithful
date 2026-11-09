import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_43

/-!
Round trip for V4_43 (Remark 4.20: good position is an open condition).  `A` is the conjunction of
the types of `Polyfold.tangentSpace_eq_range_graph`, `Polyfold.MPolyfold.remark_4_2_9` (universe
`0`), `Polyfold.lemma_3_6_9_relOpen` and `Polyfold.IsInGoodPosition.isInGoodPositionIn_of_le`.

B states Remark 4.20 with B's chart reading `IsGoodPositionAtB` of Definition 4.16 (verbatim the
one of the blind V4_38).  The glue is that of V4_38 (copied below, `gp_iff` = V4_38's `B_holds`):
for tame `X`, a smooth submanifold `A` and `a ∈ A`, the project's `IsGoodPositionAt` agrees with
`IsGoodPositionAtB` (the project's good complement is algebraic, B's an sc-complement; the upgrade
uses tameness, Lemma 4.19 through chart independence and a closed good complement cut down to
`T₀O`, as in V3_82).

* `A_to_B`: translate the hypothesis with `gp_iff`, apply `remark_4_2_9` (from `A`), translate
  back at every `b ∈ U ∩ A`.
* `B → A` is proved only for the main conjunct (`B_to_A_main`, `remark_4_2_9` itself, by the same
  translation); the other three conjuncts are general lemmas of the proof (the tangent space of
  a graph, Lemma 3.55 for relatively open domains, good position in `E` ⇒ inside any `T ⊇ N`)
  that B does not contain.
-/

namespace RoundTrip.V4_43
open Polyfold

/-- The project's statement, universe `0`. -/
def A : Prop :=
  type_of% @Polyfold.tangentSpace_eq_range_graph ∧
    type_of% @Polyfold.MPolyfold.remark_4_2_9.{0} ∧
    type_of% @Polyfold.lemma_3_6_9_relOpen ∧
    type_of% @Polyfold.IsInGoodPosition.isInGoodPositionIn_of_le

theorem A_holds : A :=
  ⟨@Polyfold.tangentSpace_eq_range_graph, @Polyfold.MPolyfold.remark_4_2_9.{0},
    @Polyfold.lemma_3_6_9_relOpen, @Polyfold.IsInGoodPosition.isInGoodPositionIn_of_le⟩

/-! ### The glue of V4_38 (Definition 4.16 in a chart), copied -/

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

/-- **Definition 4.16** (V4_38's `B_holds`): the project's notion is B's (for tame `X`). -/
theorem gp_iff : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) (A : Set X) (a : X), P.IsTame → IsSmoothSubmanifoldB P A → a ∈ A →
      (P.IsGoodPositionAt A a ↔ IsGoodPositionAtB P A a) := by
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
    have : FiniteDimensional ℝ N := by rw [hNt]; exact lemma_4_1_7_ii htp h0t
    have hNs : N ≤ ψ.model.E.smooth :=
      (ψ.model.E.proposition_1_1_7_iff N).1 (hNt ▸ (t.isScSplitting_range_scDeriv h0t hs0).1)
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

theorem A_to_B : A → B := by
  rintro ⟨-, h420, -, -⟩ X _ _ _ P S a hP hSB ha hgp
  have hS : P.IsSmoothSubmanifold S := (smooth_iff P S).2 hSB
  obtain ⟨U, hU, haU, hU'⟩ := h420 hP hS ((gp_iff X P S a hP hSB ha).2 hgp)
  exact ⟨U, hU, haU, fun b hb => (gp_iff X P S b hP hSB hb.2).1 (hU' b hb)⟩

/-- B gives the main conjunct of A (Remark 4.20 itself). -/
theorem B_to_A_main : B → type_of% @Polyfold.MPolyfold.remark_4_2_9.{0} := by
  intro hB X _ _ _ P hP S hS a hgp
  have hSB : IsSmoothSubmanifoldB P S := (smooth_iff P S).1 hS
  have ha : a ∈ S := hgp.1
  obtain ⟨U, hU, haU, hU'⟩ := hB X P S a hP hSB ha ((gp_iff X P S a hP hSB ha).1 hgp)
  exact ⟨U, hU, haU, fun b hb => (gp_iff X P S b hP hSB hb.2).2 (hU' b hb)⟩

#rt_check RoundTrip.V4_43.A_to_B [Polyfold.tangentSpace_eq_range_graph,
  Polyfold.MPolyfold.remark_4_2_9, Polyfold.lemma_3_6_9_relOpen,
  Polyfold.IsInGoodPosition.isInGoodPositionIn_of_le]
#rt_check RoundTrip.V4_43.B_to_A_main [Polyfold.tangentSpace_eq_range_graph,
  Polyfold.MPolyfold.remark_4_2_9, Polyfold.lemma_3_6_9_relOpen,
  Polyfold.IsInGoodPosition.isInGoodPositionIn_of_le]
#rt_overlap RoundTrip.V4_43.B_to_A_main [Polyfold.tangentSpace_eq_range_graph,
  Polyfold.MPolyfold.remark_4_2_9, Polyfold.lemma_3_6_9_relOpen,
  Polyfold.IsInGoodPosition.isInGoodPositionIn_of_le]

end RoundTrip.V4_43
