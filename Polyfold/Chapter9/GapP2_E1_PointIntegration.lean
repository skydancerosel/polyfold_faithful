import Polyfold.Chapter9.GapP2_E1_SheetIntegration
import Polyfold.Chapter9.GapP2_E2BoundaryNull

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 9, §9.5:
a witness for the structure `SheetIntegration` of `GapP2_E1_SheetIntegration.lean`, in dimension
`0`, for every ep-groupoid.

# Integration over oriented points

For `n = 0` the sheets of a branched ep⁺-subgroupoid are smooth points `{p}`, a `0`-form is a
function `f : X → ℝ` with `f(s(φ)) = f(t(φ))` for all morphisms (Definition 8.2.1 for `k = 0`), an
orientation of `{p}` is a sign (2021 p. 422: `Λ^max 0 = ℝ`; in the repository the positive
orientation is the one with a positive frame, the empty frame), and
`∫_{{p}} f|({p}, o) = ± f(p)`.

* `pointSheets X` (the empty set and the smooth points), `invariantFunctions X` (the `0`-forms),
  `frameSign` (the sign of an oriented tangent set of dimension `0`), `pointInteg`.
* **`pointIntegration X : X.SheetIntegration (SheetNullSets.point (pointSheets X))
  (invariantFunctions X)`**: all fields of `SheetIntegration` hold, with the null sets of
  dimension `0` (`SheetNullSets.point`, agent E2: only the sets not meeting the sheet), so that the
  hypotheses of the theorems of `GapP2_E1_LocalMeasure.lean` and `GapP2_E1_BranchedIntegral.lean`
  on the integration are satisfiable, with integrals that do not vanish
  (`pointIntegration_integ_singleton`).

The two orientations of a point have opposite integrals because a tangent set of dimension `0`
has at most one frame: `dim_eq_zero_of_isOrientedAt_singleton`, `frameSign_eq_neg`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module
open scoped symmDiff

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

section Defs

variable (X : EpGroupoid Obj Mor)

/-- The sheets of dimension `0`: the empty set and the smooth points. -/
def pointSheets : Set (Set Obj) := {N | N = ∅ ∨ ∃ p ∈ X.PObj.smoothSet, N = {p}}

/-- **The `0`-forms of the ep-groupoid**: the functions on the objects that are invariant under
the morphisms (Definition 8.2.1 for `k = 0`, without the smoothness). -/
def invariantFunctions : Submodule ℝ (Obj → ℝ) where
  carrier := {f | ∀ φ : Mor, f (X.src φ) = f (X.tgt φ)}
  add_mem' := fun hf hg φ => by rw [Pi.add_apply, Pi.add_apply, hf φ, hg φ]
  zero_mem' := fun _ => rfl
  smul_mem' := fun c f hf φ => by rw [Pi.smul_apply, Pi.smul_apply, hf φ]

end Defs

variable {X : EpGroupoid Obj Mor}

open scoped Classical in
/-- The sign of an oriented tangent set of dimension `0`: `+1` if it has a positive frame (the
empty frame), `-1` otherwise. -/
def frameSign (g : X.PObj.OrTangent) : ℝ := if g.frames.Nonempty then 1 else -1

open scoped Classical in
/-- `∫_A f|({p}, o) = ± f(p)` if `p ∈ A`, and `0` otherwise. -/
def pointInteg (f : Obj → ℝ) (N : Set Obj) (g : Obj → X.PObj.OrTangent) (A : Set Obj) : ℝ :=
  if h : (A ∩ N).Nonempty then frameSign (g h.some) * f h.some else 0

theorem pointInteg_of_mem {f : Obj → ℝ} {N : Set Obj} {g : Obj → X.PObj.OrTangent}
    {A : Set Obj} (hN : N.Subsingleton) {p : Obj} (hp : p ∈ A ∩ N) :
    pointInteg f N g A = frameSign (g p) * f p := by
  have h : (A ∩ N).Nonempty := ⟨p, hp⟩
  rw [pointInteg, dif_pos h, hN h.some_mem.2 hp.2]

theorem pointInteg_of_empty {f : Obj → ℝ} {N : Set Obj} {g : Obj → X.PObj.OrTangent}
    {A : Set Obj} (h : A ∩ N = ∅) : pointInteg f N g A = 0 := by
  rw [pointInteg, dif_neg (by rw [h]; exact not_nonempty_empty)]

theorem subsingleton_of_mem_pointSheets {N : Set Obj} (hN : N ∈ pointSheets X) :
    N.Subsingleton := by
  rcases hN with rfl | ⟨p, -, rfl⟩
  · exact subsingleton_empty
  · exact subsingleton_singleton

omit [T2Space Obj] [ParacompactSpace Obj] in
/-- Every set is measurable in a point. -/
theorem isMeasIn_point {S : Set (Set Obj)} {N : Set Obj} (hN : N.Subsingleton) (A : Set Obj) :
    (SheetNullSets.point S).IsMeasIn N A := by
  by_cases h : (A ∩ N).Nonempty
  · have hAN : A ∩ N = N := Subset.antisymm inter_subset_right fun y hy => by
      obtain ⟨p, hp⟩ := h
      rw [hN hy hp.2]; exact hp
    refine ⟨univ, MeasurableSet.univ, SheetNullSets.point_isNull_iff.2 ?_⟩
    rw [hAN, univ_inter, symmDiff_self]
    exact empty_disjoint _
  · refine ⟨∅, MeasurableSpace.measurableSet_empty _, SheetNullSets.point_isNull_iff.2 ?_⟩
    rw [not_nonempty_iff_eq_empty.1 h, empty_inter, symmDiff_self]
    exact empty_disjoint _

/-- **An oriented tangent set with the carrier `T_p{p}` has dimension `0`.** -/
theorem dim_eq_zero_of_isOrientedAt_singleton {p : Obj} (hp : p ∈ X.PObj.smoothSet)
    {g : X.PObj.OrTangent} (h : X.PObj.IsOrientedAt p g)
    (hc : g.carrier = X.PObj.submanifoldTangent {p} p) : g.dim = 0 := by
  obtain ⟨φ, hφ, hpφ⟩ := X.PObj.exists_isChart_mem_source p
  obtain ⟨N, hN, -, hr, -⟩ := h.isChartOrientation hφ hpφ
  rw [hc, MPolyfold.chartVec_image_submanifoldTangent_singleton hφ hp hpφ] at hN
  have hbot : N = ⊥ := (Submodule.eq_bot_iff N).2 fun v hv => by
    have : v ∈ (N : Set (φ.model.E 0)) := hv
    rw [hN] at this
    exact this
  rw [← hr, hbot, finrank_bot]

/-- **The two orientations of a tangent set of dimension `0` have opposite signs.** -/
theorem frameSign_eq_neg {g g' : X.PObj.OrTangent} (hd : g.dim = 0) (hd' : g'.dim = 0)
    (hc : g.carrier = g'.carrier) (hne : g ≠ g') : frameSign g = -frameSign g' := by
  obtain ⟨d, L, F⟩ := g
  obtain ⟨d', L', F'⟩ := g'
  simp only at hd hd' hc
  subst hd hd' hc
  have hFF : F ≠ F' := fun h => hne (by rw [h])
  by_cases hF : F.Nonempty <;> by_cases hF' : F'.Nonempty
  · exact absurd (hF.eq_univ.trans hF'.eq_univ.symm) hFF
  · simp [frameSign, hF, hF']
  · simp [frameSign, hF, hF']
  · exact absurd ((not_nonempty_iff_eq_empty.1 hF).trans (not_nonempty_iff_eq_empty.1 hF').symm) hFF

theorem frameSign_map (F : X.PObj.TangentSpace → X.PObj.TangentSpace) (g : X.PObj.OrTangent) :
    frameSign (g.map F) = frameSign g := by
  classical
  unfold frameSign
  change (if ((fun v => F ∘ v) '' g.frames).Nonempty then (1 : ℝ) else -1) = _
  by_cases h : g.frames.Nonempty
  · rw [if_pos h, if_pos (h.image _)]
  · rw [if_neg h, if_neg fun h' => h (Set.image_nonempty.1 h')]

theorem eq_singleton_of_mem_pointSheets {N : Set Obj} (hN : N ∈ pointSheets X) {p : Obj}
    (hp : p ∈ N) : p ∈ X.PObj.smoothSet ∧ N = {p} := by
  rcases hN with rfl | ⟨q, hq, rfl⟩
  · exact hp.elim
  · obtain rfl := mem_singleton_iff.1 hp
    exact ⟨hq, rfl⟩

variable (X) in
/-- **Integration over oriented points**: a `SheetIntegration` in dimension `0`, for every
ep-groupoid; the forms are the invariant functions, the sheets the smooth points, and
`∫_{{p}} f|({p}, o) = ± f(p)`. -/
def pointIntegration :
    X.SheetIntegration (SheetNullSets.point (pointSheets X)) (invariantFunctions X) where
  integ ω N g A := pointInteg (ω : Obj → ℝ) N g A
  integ_add ω τ N g A := by
    unfold pointInteg
    split_ifs
    · rw [Submodule.coe_add, Pi.add_apply, mul_add]
    · rw [add_zero]
  integ_smul c ω N g A := by
    unfold pointInteg
    split_ifs
    · rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring
    · rw [mul_zero]
  lindelof N hN := by
    have : Subsingleton N := (subsingleton_coe N).2 (subsingleton_of_mem_pointSheets hN)
    infer_instance
  inter_mem N hN V _ := by
    rcases hN with rfl | ⟨p, hp, rfl⟩
    · exact Or.inl (empty_inter V)
    · by_cases hpV : p ∈ V
      · exact Or.inr ⟨p, hp, by rw [inter_eq_left.2 (singleton_subset_iff.2 hpV)]⟩
      · exact Or.inl (singleton_inter_eq_empty.2 hpV)
  isMeasIn_inter N hN N' _ := isMeasIn_point (subsingleton_of_mem_pointSheets hN) _
  isNull_tangent_ne N hN N' hN' := by
    refine SheetNullSets.point_isNull_iff.2 (disjoint_left.2 ?_)
    rintro y ⟨⟨hyN, hyN'⟩, hne⟩ -
    rw [(eq_singleton_of_mem_pointSheets hN hyN).2,
      (eq_singleton_of_mem_pointSheets hN' hyN').2] at hne
    exact hne rfl
  isMeasIn_tangent_eq N hN N' _ _ _ _ _ := isMeasIn_point (subsingleton_of_mem_pointSheets hN) _
  integ_hasSum ω N hN m o A hA _ hd := by
    have hNs := subsingleton_of_mem_pointSheets hN
    by_cases h : ((⋃ k, A k) ∩ N).Nonempty
    · obtain ⟨p, hpU, hpN⟩ := h
      obtain ⟨k₀, hk₀⟩ := mem_iUnion.1 hpU
      have h0 : ∀ k, k ≠ k₀ → pointInteg (ω : Obj → ℝ) N o.tangent (A k) = 0 := fun k hk =>
        pointInteg_of_empty (eq_empty_of_forall_notMem fun y hy => by
          have hyp : y = p := hNs hy.2 hpN
          exact Set.disjoint_left.1 (hd hk) hy.1 (hyp ▸ hk₀))
      have h1 := hasSum_single k₀ h0
      rw [pointInteg_of_mem hNs ⟨hk₀, hpN⟩] at h1
      rw [pointInteg_of_mem hNs ⟨hpU, hpN⟩]
      exact h1
    · have hU := not_nonempty_iff_eq_empty.1 h
      have h0 : ∀ k, pointInteg (ω : Obj → ℝ) N o.tangent (A k) = 0 := fun k =>
        pointInteg_of_empty (eq_empty_of_forall_notMem fun y hy =>
          (hU ▸ (⟨mem_iUnion.2 ⟨k, hy.1⟩, hy.2⟩ : y ∈ (⋃ k, A k) ∩ N) : y ∈ (∅ : Set Obj)))
      rw [pointInteg_of_empty hU]
      simp only [h0]
      exact hasSum_zero
  integ_null ω N _ m o A hA hnull :=
    pointInteg_of_empty (by
      rw [inter_eq_left.2 hA]
      exact (SheetNullSets.point_isNull_iff.1 hnull).eq_bot_of_le hA)
  integ_congr ω N hN N' hN' m m' o o' A hA _ heq := by
    have hNs := subsingleton_of_mem_pointSheets hN
    have hNs' := subsingleton_of_mem_pointSheets hN'
    by_cases h : A.Nonempty
    · obtain ⟨p, hp⟩ := h
      rw [pointInteg_of_mem hNs ⟨hp, (hA hp).1⟩, pointInteg_of_mem hNs' ⟨hp, (hA hp).2⟩,
        heq p hp]
    · rw [not_nonempty_iff_eq_empty.1 h, pointInteg_of_empty (empty_inter _),
        pointInteg_of_empty (empty_inter _)]
  integ_neg ω N hN N' hN' m m' o o' A hA _ hne := by
    have hNs := subsingleton_of_mem_pointSheets hN
    have hNs' := subsingleton_of_mem_pointSheets hN'
    by_cases h : A.Nonempty
    · obtain ⟨p, hp⟩ := h
      obtain ⟨hps, hNp⟩ := eq_singleton_of_mem_pointSheets hN (hA hp).1
      obtain ⟨-, hN'p⟩ := eq_singleton_of_mem_pointSheets hN' (hA hp).2
      have hd : (o.tangent p).dim = 0 :=
        dim_eq_zero_of_isOrientedAt_singleton hps (o.isOrientedAt_tangent (hA hp).1)
          (by rw [MPolyfold.SubmanifoldOrientation.tangent_carrier, hNp])
      have hd' : (o'.tangent p).dim = 0 :=
        dim_eq_zero_of_isOrientedAt_singleton hps (o'.isOrientedAt_tangent (hA hp).2)
          (by rw [MPolyfold.SubmanifoldOrientation.tangent_carrier, hN'p])
      rw [pointInteg_of_mem hNs ⟨hp, (hA hp).1⟩, pointInteg_of_mem hNs' ⟨hp, (hA hp).2⟩,
        frameSign_eq_neg hd hd' (by
          rw [MPolyfold.SubmanifoldOrientation.tangent_carrier,
            MPolyfold.SubmanifoldOrientation.tangent_carrier]
          exact (hne p hp).1) (hne p hp).2, neg_mul]
    · rw [not_nonempty_iff_eq_empty.1 h, pointInteg_of_empty (empty_inter _),
        pointInteg_of_empty (empty_inter _), neg_zero]
  image_mem N hN f f' U U' hf hNU _ := by
    rcases hN with rfl | ⟨p, hp, rfl⟩
    · exact Or.inl (image_empty f)
    · refine Or.inr ⟨f p, mem_iInter.2 fun k => ?_, image_singleton⟩
      exact hf.isScSmoothOn.mapsTo_levelSet k ⟨hNU rfl, mem_iInter.1 hp k⟩
  isMeasIn_image N hN f f' U U' hf _ _ A _ _ :=
    isMeasIn_point ((subsingleton_of_mem_pointSheets hN).image f) _
  integ_image ω N hN m o hM f f' U U' hf hNU hmor A hA _ := by
    have hNs := subsingleton_of_mem_pointSheets hN
    by_cases h : A.Nonempty
    · obtain ⟨p, hp⟩ := h
      obtain ⟨ψ, hsrc, htgt, -⟩ := hmor p (hA hp)
      have hinv : (ω : Obj → ℝ) (f p) = (ω : Obj → ℝ) p := by
        have := ω.2 ψ
        rw [hsrc, htgt] at this
        exact this.symm
      rw [pointInteg_of_mem (A := f '' A) (N := f '' N) (p := f p) (hNs.image f)
          ⟨⟨p, hp, rfl⟩, ⟨p, hA hp, rfl⟩⟩,
        pointInteg_of_mem hNs ⟨hp, hA hp⟩,
        MPolyfold.SubmanifoldOrientation.mapDiffeo_tangent o hM hf hNU (hA hp), frameSign_map,
        hinv]
    · rw [not_nonempty_iff_eq_empty.1 h, image_empty, pointInteg_of_empty (empty_inter _),
        pointInteg_of_empty (empty_inter _)]

/-- **The integrals of `pointIntegration` do not vanish**: over a point `p` with an orientation
`o`, the integral of the `0`-form `f` is `± f(p)`. -/
theorem pointIntegration_integ_singleton (ω : invariantFunctions X) {p : Obj} {m : ℕ}
    (o : X.PObj.SubmanifoldOrientation {p} m) :
    (pointIntegration X).integ ω {p} o.tangent {p} =
      frameSign (o.tangent p) * (ω : Obj → ℝ) p :=
  pointInteg_of_mem subsingleton_singleton ⟨rfl, rfl⟩

end EpGroupoid

end Polyfold
