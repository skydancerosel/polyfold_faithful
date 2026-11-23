import Polyfold.Chapter2.LocConnected

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §2.1–§2.3
(sc-smooth retracts and M-polyfolds, pp. 23–46); used with the natural representations of
Theorem 7.1.13 (p. 244) on connected neighbourhoods.

# Compact connected sets around compact sets near a point of an M-polyfold

## What is formalized

* `ScRetraction.exists_ball_cone`: for `o ∈ O = r(U)` and a neighbourhood `W` of `o` there is
  `ε > 0` such that every compact `K ⊆ O ∩ B_ε(o)` lies, together with `o`, in a compact
  connected subset of `O ∩ W`: the image under `r` of the cone `{o + τ(p − o)}` over `K`.
* **`MPolyfold.exists_nhds_compact_connected`**: every point `x` of an M-polyfold has, inside
  every neighbourhood `u`, an open neighbourhood `N` such that every compact `K ⊆ N` lies,
  together with `x`, in a compact connected subset of `u`.

## Reading

An M-polyfold need not be locally compact; the statement is about compact subsets near `x`.
Only level `0` is used.
-/

open Set Filter Topology Function
open scoped unitInterval

noncomputable section

namespace Polyfold

namespace ScRetraction

variable {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C)

/-- **`r` maps cones over compact sets to compact connected sets**: for `o ∈ O = r(U)` and a
neighbourhood `W` of `o` there is `ε > 0` such that for every compact `K ⊆ O ∩ B_ε(o)` there is a
compact connected `Z ⊆ O ∩ W` with `K ∪ {o} ⊆ Z`. -/
theorem exists_ball_cone {o : E 0} (ho : o ∈ R.retract) {W : Set (E 0)} (hW : W ∈ 𝓝 o) :
    ∃ ε > 0, ∀ K : Set (E 0), IsCompact K → K ⊆ R.retract ∩ Metric.ball o ε →
      ∃ Z : Set (E 0), IsCompact Z ∧ IsPreconnected Z ∧ K ⊆ Z ∧ o ∈ Z ∧ Z ⊆ R.retract ∩ W := by
  have hoU : o ∈ R.U := R.retract_subset ho
  have hro : R o = o := R.apply_eq_self_of_mem_retract ho
  obtain ⟨O', hO'o, hO'⟩ := R.relOpen.relOpen
  have hUC : R.U ⊆ C := by rw [hO']; exact inter_subset_right
  have hcont : ContinuousOn R R.U := R.isSc1.isSc0.continuousOn_base
  have hpre : R ⁻¹' W ∈ 𝓝[R.U] o := hcont o hoU (by rw [hro]; exact hW)
  obtain ⟨ε₁, hε₁, hε₁W⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  obtain ⟨δ, hδ, hδO'⟩ := Metric.isOpen_iff.1 hO'o o (by rw [hO'] at hoU; exact hoU.1)
  set B := Metric.ball o (min ε₁ δ) ∩ C with hB
  have hBU : ∀ q ∈ B, q ∈ R.U ∧ R q ∈ W := fun q hq => by
    have hqU : q ∈ R.U := by
      rw [hO']
      exact ⟨hδO' (Metric.ball_subset_ball (min_le_right _ _) hq.1), hq.2⟩
    exact ⟨hqU, hε₁W ⟨Metric.ball_subset_ball (min_le_left _ _) hq.1, hqU⟩⟩
  have hε : 0 < min ε₁ δ := lt_min hε₁ hδ
  refine ⟨min ε₁ δ, hε, fun K hK hKO => ?_⟩
  set K' : Set (E 0) := insert o K with hK'
  have hK'c : IsCompact K' := hK.insert o
  have hK'O : K' ⊆ R.retract ∩ Metric.ball o (min ε₁ δ) :=
    insert_subset ⟨ho, Metric.mem_ball_self hε⟩ hKO
  have hline : ∀ p ∈ K', ∀ τ ∈ I, AffineMap.lineMap o p τ ∈ B := fun p hp τ hτ =>
    ((convex_ball _ _).inter R.relOpen.isPartialQuadrant.convex).lineMap_mem
      ⟨Metric.mem_ball_self hε, hUC hoU⟩
      ⟨(hK'O hp).2, hUC (R.retract_subset (hK'O hp).1)⟩ hτ
  set F : ℝ × E 0 → E 0 := fun q => R (AffineMap.lineMap o q.2 q.1) with hF
  have hlc : Continuous fun q : ℝ × E 0 => (AffineMap.lineMap o q.2 q.1 : E 0) := by
    have e : (fun q : ℝ × E 0 => (AffineMap.lineMap o q.2 q.1 : E 0)) =
        fun q => q.1 • (q.2 - o) + o := by
      funext q
      rw [AffineMap.lineMap_apply]
      simp [vsub_eq_sub, vadd_eq_add]
    rw [e]
    exact (continuous_fst.smul (continuous_snd.sub continuous_const)).add continuous_const
  have hFc : ContinuousOn F (I ×ˢ K') :=
    hcont.comp hlc.continuousOn fun q hq => (hBU _ (hline q.2 hq.2 q.1 hq.1)).1
  refine ⟨F '' (I ×ˢ K'), (isCompact_Icc.prod hK'c).image_of_continuousOn hFc, ?_, ?_, ?_, ?_⟩
  · have e : F '' (I ×ˢ K') = ⋃ p ∈ K', (fun τ : ℝ => F (τ, p)) '' I := by
      ext z
      simp only [mem_image, mem_prod, mem_iUnion, exists_prop, Prod.exists]
      constructor
      · rintro ⟨τ, p, ⟨hτ, hp⟩, rfl⟩
        exact ⟨p, hp, τ, hτ, rfl⟩
      · rintro ⟨p, hp, τ, hτ, rfl⟩
        exact ⟨τ, p, ⟨hτ, hp⟩, rfl⟩
    rw [e, biUnion_eq_iUnion]
    refine isPreconnected_iUnion ⟨o, mem_iInter.2 fun p => ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩⟩
      fun p => ?_
    · change R (AffineMap.lineMap o (p : E 0) (0 : ℝ)) = o
      rw [AffineMap.lineMap_apply_zero, hro]
    · refine isPreconnected_Icc.image _ (hFc.comp (continuous_id.prodMk
        continuous_const).continuousOn fun τ hτ => ⟨hτ, p.2⟩)
  · intro p hp
    refine ⟨(1, p), ⟨⟨zero_le_one, le_rfl⟩, mem_insert_of_mem o hp⟩, ?_⟩
    change R (AffineMap.lineMap o p (1 : ℝ)) = p
    rw [AffineMap.lineMap_apply_one, R.apply_eq_self_of_mem_retract (hKO hp).1]
  · refine ⟨(0, o), ⟨⟨le_rfl, zero_le_one⟩, mem_insert o K⟩, ?_⟩
    change R (AffineMap.lineMap o o (0 : ℝ)) = o
    rw [AffineMap.lineMap_apply_zero, hro]
  · rintro _ ⟨q, hq, rfl⟩
    have h := hBU _ (hline q.2 hq.2 q.1 hq.1)
    exact ⟨R.apply_mem_retract h.1, h.2⟩

end ScRetraction

namespace MPolyfold

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

include P in
/-- **Compact sets near a point lie in compact connected sets**: every point `x` of an
M-polyfold has, inside every neighbourhood `u`, an open neighbourhood `N` such that every compact
`K ⊆ N` lies, together with `x`, in a compact connected subset of `u`. -/
theorem exists_nhds_compact_connected {x : X} {u : Set X} (hu : u ∈ 𝓝 x) :
    ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ N ⊆ u ∧ ∀ K : Set X, IsCompact K → K ⊆ N →
      ∃ Z : Set X, IsCompact Z ∧ IsPreconnected Z ∧ K ⊆ Z ∧ x ∈ Z ∧ Z ⊆ u := by
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source x
  obtain ⟨u', hu'u, hu'o, hxu'⟩ := mem_nhds_iff.1 hu
  obtain ⟨W, hWo, hWs⟩ :=
    φ.exists_isOpen_image_eq (inter_subset_right (s := u')) (hu'o.inter φ.isOpen_source)
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  have hxO : φ x ∈ R.retract := hR ▸ φ.mapsTo_model x hx
  have hxW : φ x ∈ W := by
    have : φ x ∈ φ '' (u' ∩ φ.source) := mem_image_of_mem φ ⟨hxu', hx⟩
    rw [hWs] at this
    exact this.2
  obtain ⟨ε, hε, hcone⟩ := R.exists_ball_cone hxO (hWo.mem_nhds hxW)
  have hNo : IsOpen (u' ∩ φ.source ∩ φ ⁻¹' Metric.ball (φ x) ε) := by
    have h := φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source
      (Metric.isOpen_ball (x := φ x) (ε := ε))
    have e : u' ∩ φ.source ∩ φ ⁻¹' Metric.ball (φ x) ε =
        u' ∩ (φ.source ∩ φ ⁻¹' Metric.ball (φ x) ε) := inter_assoc _ _ _
    rw [e]
    exact hu'o.inter h
  refine ⟨_, hNo, ⟨⟨hxu', hx⟩, Metric.mem_ball_self hε⟩,
    fun y hy => hu'u hy.1.1, fun K hK hKN => ?_⟩
  have hKs : K ⊆ φ.source := fun y hy => (hKN hy).1.2
  obtain ⟨Z₀, hZ₀c, hZ₀p, hKZ₀, hxZ₀, hZ₀⟩ := hcone (φ '' K)
    (hK.image_of_continuousOn (φ.continuousOn_toFun.mono hKs)) (by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨hR ▸ φ.mapsTo_model y (hKs hy), (hKN hy).2⟩)
  have hsymm : ContinuousOn φ.symm Z₀ :=
    φ.continuousOn_invFun.mono fun z hz => hR ▸ (hZ₀ hz).1
  refine ⟨φ.symm '' Z₀, hZ₀c.image_of_continuousOn hsymm, hZ₀p.image _ hsymm, fun y hy => ?_,
    ⟨φ x, hxZ₀, φ.symm_apply_apply hx⟩, ?_⟩
  · exact ⟨φ y, hKZ₀ ⟨y, hy, rfl⟩, φ.symm_apply_apply (hKs hy)⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ φ '' (u' ∩ φ.source) := by
      rw [hWs]
      exact ⟨hR ▸ (hZ₀ hz).1, (hZ₀ hz).2⟩
    obtain ⟨w, hw, rfl⟩ := hz'
    rw [φ.symm_apply_apply hw.2]
    exact hu'u hw.1

end MPolyfold

end Polyfold
