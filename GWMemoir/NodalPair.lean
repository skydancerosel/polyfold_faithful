import GWMemoir.Witnesses

/-!
# Two spheres joined at a node

HWZ, *Applications of Polyfold Theory I* (Memoirs AMS 248, no. 1179), Definitions 1.2 and 1.4,
pp. 3–4, with a domain of two components.

* §1, the disjoint union `M ⊕ M'` of Mathlib's `ChartedSpace.sum`: charts, `writtenInExtChartAt`,
  `ContMDiffAt`, `MDifferentiableAt`, `mfderiv` and `tangentCoordChange` at `inl`/`inr` points
  are those of the component (`contMDiffAt_inl_iff`, `mfderiv_inl`, `tangentCoordChange_inl`, …).
* `AlmostComplexStructure.sum`: the almost complex structure of a disjoint union.
* `NodalSurface.isClassNear_const`: a constant map is of class `(k, δ)` near a point with a
  holomorphic chart onto `ℂ`.
* `twoSpheres : NodalSurface 4`: `S² ⊔ S²`, with `j = jStd ⊔ jStd`, marked points
  `e₀, e₁` on each sphere, and the nodal pair `{e₂ on the first, e₂ on the second}` (Memoir
  Definition 1.2; connected through the node, two domain components).
* `twoSpheresStableMap om q k δ : StableMap om 4 k δ`: the constant map, a stable map of class
  `(k, δ)` (Memoir Definition 1.4): at the nodal points it is of class `(k, δ)` in the lifted
  holomorphic charts `σ₋₁`, `H^k_loc` elsewhere, area zero, and each component carries three
  special points.
-/

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Topology
open Set Function

noncomputable section

namespace GWMemoir

/-! ## 1. Disjoint unions -/

section DisjointUnion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M M' : Type*} [TopologicalSpace M] [TopologicalSpace M'] [ChartedSpace H M] [ChartedSpace H M']
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

theorem extChartAt_inl_symm (x : M) :
    ⇑(extChartAt I (Sum.inl x : M ⊕ M')).symm = Sum.inl ∘ (extChartAt I x).symm := by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [extChartAt, OpenPartialHomeomorph.extend_coe_symm, extChartAt,
    OpenPartialHomeomorph.extend_coe_symm, ChartedSpace.sum_chartAt_inl,
    OpenPartialHomeomorph.lift_openEmbedding_symm]
  rfl

theorem extChartAt_inr_symm (x : M') :
    ⇑(extChartAt I (Sum.inr x : M ⊕ M')).symm = Sum.inr ∘ (extChartAt I x).symm := by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [extChartAt, OpenPartialHomeomorph.extend_coe_symm, extChartAt,
    OpenPartialHomeomorph.extend_coe_symm, ChartedSpace.sum_chartAt_inr,
    OpenPartialHomeomorph.lift_openEmbedding_symm]
  rfl

theorem extChartAt_inl_comp (x : M) :
    ⇑(extChartAt I (Sum.inl x : M ⊕ M')) ∘ Sum.inl = extChartAt I x :=
  funext fun _ => extChartAt_inl_apply

theorem extChartAt_inr_comp (x : M') :
    ⇑(extChartAt I (Sum.inr x : M ⊕ M')) ∘ Sum.inr = extChartAt I x :=
  funext fun _ => extChartAt_inr_apply

theorem continuousAt_inl_iff {f : M ⊕ M' → N} {x : M} :
    ContinuousAt f (Sum.inl x) ↔ ContinuousAt (f ∘ Sum.inl) x :=
  Topology.IsOpenEmbedding.inl.continuousAt_iff.symm

theorem continuousAt_inr_iff {f : M ⊕ M' → N} {x : M'} :
    ContinuousAt f (Sum.inr x) ↔ ContinuousAt (f ∘ Sum.inr) x :=
  Topology.IsOpenEmbedding.inr.continuousAt_iff.symm

theorem writtenInExtChartAt_inl (f : M ⊕ M' → N) (x : M) :
    writtenInExtChartAt I I' (Sum.inl x) f = writtenInExtChartAt I I' x (f ∘ Sum.inl) := by
  simp only [writtenInExtChartAt, extChartAt_inl_symm]
  rfl

theorem writtenInExtChartAt_inr (f : M ⊕ M' → N) (x : M') :
    writtenInExtChartAt I I' (Sum.inr x) f = writtenInExtChartAt I I' x (f ∘ Sum.inr) := by
  simp only [writtenInExtChartAt, extChartAt_inr_symm]
  rfl

theorem contMDiffAt_inl_iff {f : M ⊕ M' → N} {x : M} {n : ℕ∞ω} :
    ContMDiffAt I I' n f (Sum.inl x) ↔ ContMDiffAt I I' n (f ∘ Sum.inl) x := by
  rw [contMDiffAt_iff, contMDiffAt_iff, continuousAt_inl_iff, extChartAt_inl_apply,
    extChartAt_inl_symm]
  rfl

theorem contMDiffAt_inr_iff {f : M ⊕ M' → N} {x : M'} {n : ℕ∞ω} :
    ContMDiffAt I I' n f (Sum.inr x) ↔ ContMDiffAt I I' n (f ∘ Sum.inr) x := by
  rw [contMDiffAt_iff, contMDiffAt_iff, continuousAt_inr_iff, extChartAt_inr_apply,
    extChartAt_inr_symm]
  rfl

theorem mdifferentiableAt_inl_iff {f : M ⊕ M' → N} {x : M} :
    MDifferentiableAt I I' f (Sum.inl x) ↔ MDifferentiableAt I I' (f ∘ Sum.inl) x := by
  rw [mdifferentiableAt_iff, mdifferentiableAt_iff, continuousAt_inl_iff, extChartAt_inl_apply,
    writtenInExtChartAt_inl]

theorem mdifferentiableAt_inr_iff {f : M ⊕ M' → N} {x : M'} :
    MDifferentiableAt I I' f (Sum.inr x) ↔ MDifferentiableAt I I' (f ∘ Sum.inr) x := by
  rw [mdifferentiableAt_iff, mdifferentiableAt_iff, continuousAt_inr_iff, extChartAt_inr_apply,
    writtenInExtChartAt_inr]

theorem mfderiv_inl (f : M ⊕ M' → N) (x : M) :
    (mfderiv I I' f (Sum.inl x) : E →L[𝕜] E') = mfderiv I I' (f ∘ Sum.inl) x := by
  by_cases h : MDifferentiableAt I I' (f ∘ Sum.inl) x
  · simp only [mfderiv, mdifferentiableAt_inl_iff, h, writtenInExtChartAt_inl,
      extChartAt_inl_apply]
    split_ifs <;> rfl
  · rw [mfderiv_zero_of_not_mdifferentiableAt (mt mdifferentiableAt_inl_iff.1 h),
      mfderiv_zero_of_not_mdifferentiableAt h]
    rfl

theorem mfderiv_inr (f : M ⊕ M' → N) (x : M') :
    (mfderiv I I' f (Sum.inr x) : E →L[𝕜] E') = mfderiv I I' (f ∘ Sum.inr) x := by
  by_cases h : MDifferentiableAt I I' (f ∘ Sum.inr) x
  · simp only [mfderiv, mdifferentiableAt_inr_iff, h, writtenInExtChartAt_inr,
      extChartAt_inr_apply]
    split_ifs <;> rfl
  · rw [mfderiv_zero_of_not_mdifferentiableAt (mt mdifferentiableAt_inr_iff.1 h),
      mfderiv_zero_of_not_mdifferentiableAt h]
    rfl

theorem tangentCoordChange_inl [IsManifold I 1 M] [IsManifold I 1 M'] (a b c : M) :
    tangentCoordChange I (Sum.inl a : M ⊕ M') (Sum.inl b) (Sum.inl c) =
      tangentCoordChange I a b c := by
  rw [tangentCoordChange_def, tangentCoordChange_def, extChartAt_inl_symm, ← Function.comp_assoc,
    extChartAt_inl_comp, extChartAt_inl_apply]

theorem tangentCoordChange_inr [IsManifold I 1 M] [IsManifold I 1 M'] (a b c : M') :
    tangentCoordChange I (Sum.inr a : M ⊕ M') (Sum.inr b) (Sum.inr c) =
      tangentCoordChange I a b c := by
  rw [tangentCoordChange_def, tangentCoordChange_def, extChartAt_inr_symm, ← Function.comp_assoc,
    extChartAt_inr_comp, extChartAt_inr_apply]

theorem mem_chart_source_inl {x₀ x : M} (hx : x ∈ (chartAt H x₀).source) :
    (Sum.inl x : M ⊕ M') ∈ (chartAt H (Sum.inl x₀ : M ⊕ M')).source := by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [ChartedSpace.sum_chartAt_inl, OpenPartialHomeomorph.lift_openEmbedding_source]
  exact ⟨x, hx, rfl⟩

theorem mem_chart_source_inr {x₀ x : M'} (hx : x ∈ (chartAt H x₀).source) :
    (Sum.inr x : M ⊕ M') ∈ (chartAt H (Sum.inr x₀ : M ⊕ M')).source := by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [ChartedSpace.sum_chartAt_inr, OpenPartialHomeomorph.lift_openEmbedding_source]
  exact ⟨x, hx, rfl⟩

theorem extChartAt_target_inl (x : M) :
    (extChartAt I (Sum.inl x : M ⊕ M')).target = (extChartAt I x).target := by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [extChartAt_target, extChartAt_target, ChartedSpace.sum_chartAt_inl,
    OpenPartialHomeomorph.lift_openEmbedding_target]

theorem extChartAt_target_inr (x : M') :
    (extChartAt I (Sum.inr x : M ⊕ M')).target = (extChartAt I x).target := by
  have : Nonempty H := nonempty_of_chartedSpace x
  rw [extChartAt_target, extChartAt_target, ChartedSpace.sum_chartAt_inr,
    OpenPartialHomeomorph.lift_openEmbedding_target]

theorem coordChange_inl [IsManifold I 1 M] [IsManifold I 1 M'] (a b c : M) :
    (tangentBundleCore I (M ⊕ M')).coordChange (achart H (Sum.inl a)) (achart H (Sum.inl b))
      (Sum.inl c) = (tangentBundleCore I M).coordChange (achart H a) (achart H b) c :=
  tangentCoordChange_inl a b c

theorem coordChange_inr [IsManifold I 1 M] [IsManifold I 1 M'] (a b c : M') :
    (tangentBundleCore I (M ⊕ M')).coordChange (achart H (Sum.inr a)) (achart H (Sum.inr b))
      (Sum.inr c) = (tangentBundleCore I M').coordChange (achart H a) (achart H b) c :=
  tangentCoordChange_inr a b c

end DisjointUnion

/-! ## 2. The almost complex structure of a disjoint union -/

section SumACS

variable {M M' : Type} [TopologicalSpace M] [ChartedSpace E2 M] [IsManifold 𝓘(ℝ, E2) ∞ M]
  [TopologicalSpace M'] [ChartedSpace E2 M'] [IsManifold 𝓘(ℝ, E2) ∞ M']

/-- The almost complex structure `j₁ ⊔ j₂` of `M ⊕ M'`; smooth in tangent coordinates since the
tangent coordinate changes at `inl`/`inr` points are those of the component. -/
def AlmostComplexStructure.sum (j₁ : AlmostComplexStructure E2 M)
    (j₂ : AlmostComplexStructure E2 M') : AlmostComplexStructure E2 (M ⊕ M') where
  J := Sum.elim j₁.J j₂.J
  sq := by
    rintro (x | x)
    exacts [j₁.sq x, j₂.sq x]
  smooth := by
    rintro (x₀ | x₀)
    · rw [contMDiffAt_inl_iff]
      refine (j₁.smooth x₀).congr_of_eventuallyEq ?_
      filter_upwards [(chartAt E2 x₀).open_source.mem_nhds (mem_chart_source E2 x₀)] with x hx
      have hx' := mem_chart_source_inl (M' := M') hx
      simp only [Function.comp_apply]
      rw [inTangentCoordinates_eq (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, E2)) id id _ hx' hx',
        inTangentCoordinates_eq (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, E2)) id id _ hx hx]
      simp only [id, coordChange_inl, Sum.elim_inl]
    · rw [contMDiffAt_inr_iff]
      refine (j₂.smooth x₀).congr_of_eventuallyEq ?_
      filter_upwards [(chartAt E2 x₀).open_source.mem_nhds (mem_chart_source E2 x₀)] with x hx
      have hx' := mem_chart_source_inr (M := M) hx
      simp only [Function.comp_apply]
      rw [inTangentCoordinates_eq (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, E2)) id id _ hx' hx',
        inTangentCoordinates_eq (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, E2)) id id _ hx hx]
      simp only [id, coordChange_inr, Sum.elim_inr]

end SumACS

/-! ## 3. Two spheres joined at a node -/

/-- `S² ⊔ S²`. -/
abbrev S22 := S2 ⊕ S2

/-- The marked points `e₀, e₁` on each sphere. -/
def markedTwo : Fin 4 → S22 := ![Sum.inl (pt 0), Sum.inl (pt 1), Sum.inr (pt 0), Sum.inr (pt 1)]

theorem markedTwo_injective : Injective markedTwo := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [markedTwo, pt_injective.eq_iff] at h ⊢

/-- The nodal relation of `twoSpheres`. -/
def nodeRel (x y : S22) : Prop :=
  s(x, y) ∈ ({s(Sum.inl (pt 2), Sum.inr (pt 2))} : Set (Sym2 S22))

/-- The two spheres are connected through the node. -/
theorem connectedSpace_quot_nodeRel : ConnectedSpace (Quot nodeRel) := by
  have h1 : IsConnected (range fun x : S2 => Quot.mk nodeRel (Sum.inl x)) :=
    isConnected_range (continuous_quot_mk.comp continuous_inl)
  have h2 : IsConnected (range fun x : S2 => Quot.mk nodeRel (Sum.inr x)) :=
    isConnected_range (continuous_quot_mk.comp continuous_inr)
  have hmeet : Quot.mk nodeRel (Sum.inl (pt 2)) = Quot.mk nodeRel (Sum.inr (pt 2)) :=
    Quot.sound (mem_singleton _)
  have hne : ((range fun x : S2 => Quot.mk nodeRel (Sum.inl x)) ∩
      range fun x : S2 => Quot.mk nodeRel (Sum.inr x)).Nonempty :=
    ⟨Quot.mk nodeRel (Sum.inl (pt 2)), ⟨pt 2, rfl⟩, ⟨pt 2, hmeet.symm⟩⟩
  have hu := IsConnected.union hne h1 h2
  have huniv : ((range fun x : S2 => Quot.mk nodeRel (Sum.inl x)) ∪
      range fun x : S2 => Quot.mk nodeRel (Sum.inr x)) = univ := by
    refine eq_univ_of_forall fun q => ?_
    induction q using Quot.ind with
    | mk p => rcases p with x | x; exacts [Or.inl ⟨x, rfl⟩, Or.inr ⟨x, rfl⟩]
  rw [huniv] at hu
  exact connectedSpace_iff_univ.2 hu

/-- **Witness for Memoir Definition 1.2 with two components**: two round spheres `(S², j)`
joined at the nodal pair `{e₂ ∈ S²₁, e₂ ∈ S²₂}`, with the marked points `e₀, e₁` on each. -/
def twoSpheres : NodalSurface 4 where
  S := S22
  j := jStd.sum jStd
  marked := ⟨markedTwo, markedTwo_injective⟩
  nodes := {s(Sum.inl (pt 2), Sum.inr (pt 2))}
  finite_nodes := finite_singleton _
  not_diag p hp := by
    rw [mem_singleton_iff] at hp
    subst hp
    rw [Sym2.mk_isDiag_iff]
    exact Sum.inl_ne_inr
  disjoint p hp q hq _ _ _ := by rw [mem_singleton_iff] at hp hq; rw [hp, hq]
  marked_not_nodal i p hp := by
    rw [mem_singleton_iff] at hp
    subst hp
    rw [Sym2.mem_iff]
    fin_cases i <;> simp [markedTwo, pt_injective.eq_iff]
  connected := connectedSpace_quot_nodeRel

theorem twoSpheres_nodes_nonempty : twoSpheres.nodes.Nonempty := singleton_nonempty _

/-- The domain of `twoSpheres` has two components. -/
theorem twoSpheres_not_connectedSpace : ¬ ConnectedSpace twoSpheres.S := by
  intro h
  have : ConnectedSpace S22 := h
  rcases isClopen_iff.1 (isClopen_range_inl (X := S2) (Y := S2)) with h' | h'
  · exact (eq_empty_iff_forall_notMem.1 h') (Sum.inl (pt 0)) ⟨pt 0, rfl⟩
  · have : (Sum.inr (pt 0) : S22) ∈ range Sum.inl := by rw [h']; trivial
    obtain ⟨y, hy⟩ := this
    exact Sum.inl_ne_inr hy

theorem connectedComponent_inl (a : S2) :
    connectedComponent (Sum.inl a : S22) = range Sum.inl :=
  Subset.antisymm (isClopen_range_inl.connectedComponent_subset ⟨a, rfl⟩)
    ((isConnected_range continuous_inl).isPreconnected.subset_connectedComponent ⟨a, rfl⟩)

theorem connectedComponent_inr (a : S2) :
    connectedComponent (Sum.inr a : S22) = range Sum.inr :=
  Subset.antisymm (isClopen_range_inr.connectedComponent_subset ⟨a, rfl⟩)
    ((isConnected_range continuous_inr).isPreconnected.subset_connectedComponent ⟨a, rfl⟩)

theorem twoSpheres_special_finite : twoSpheres.special.Finite := by
  refine (finite_range _).union
    ((Set.toFinite ({Sum.inl (pt 2), Sum.inr (pt 2)} : Set S22)).subset ?_)
  rintro x ⟨p, hp, hx⟩
  obtain rfl : p = s(Sum.inl (pt 2), Sum.inr (pt 2)) := hp
  exact Sym2.mem_iff.1 hx

theorem inl_pt2_mem_special : (Sum.inl (pt 2) : S22) ∈ twoSpheres.special :=
  Or.inr ⟨_, rfl, Sym2.mem_mk_left _ _⟩

theorem inr_pt2_mem_special : (Sum.inr (pt 2) : S22) ∈ twoSpheres.special :=
  Or.inr ⟨_, rfl, Sym2.mem_mk_right _ _⟩

/-- A component with three distinct special points (and finitely many special points in all)
is not unstable. -/
theorem NodalSurface.not_unstable_of_three {m : ℕ} (X : NodalSurface m) (hfin : X.special.Finite)
    (x a b c : X.S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ X.special ∩ connectedComponent x) (hb : b ∈ X.special ∩ connectedComponent x)
    (hc : c ∈ X.special ∩ connectedComponent x) : ¬ X.IsUnstableComponent x := by
  have hsub : ({a, b, c} : Set X.S) ⊆ X.special ∩ connectedComponent x := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨ha, hb, hc⟩
  have h3 : 3 ≤ (X.special ∩ connectedComponent x).ncard := by
    rw [← Set.ncard_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩]
    exact Set.ncard_le_ncard hsub (hfin.subset inter_subset_left)
  rintro (⟨_, h⟩ | ⟨_, h⟩)
  · omega
  · rw [h] at ha
    exact ha

theorem inl_mem_connectedComponent (x a : S2) :
    (Sum.inl a : S22) ∈ connectedComponent (Sum.inl x : S22) := by
  rw [connectedComponent_inl]; exact ⟨a, rfl⟩

theorem inr_mem_connectedComponent (x a : S2) :
    (Sum.inr a : S22) ∈ connectedComponent (Sum.inr x : S22) := by
  rw [connectedComponent_inr]; exact ⟨a, rfl⟩

theorem inl_pt_ne {i j : Fin 3} (h : i ≠ j) : (Sum.inl (pt i) : S22) ≠ Sum.inl (pt j) :=
  fun e => h (pt_injective (Sum.inl_injective e))

theorem inr_pt_ne {i j : Fin 3} (h : i ≠ j) : (Sum.inr (pt i) : S22) ≠ Sum.inr (pt j) :=
  fun e => h (pt_injective (Sum.inr_injective e))

/-- Each component of `twoSpheres` carries three special points: it is stable. -/
theorem twoSpheres_not_unstable (x : twoSpheres.S) : ¬ twoSpheres.IsUnstableComponent x := by
  rcases x with x | x
  · exact twoSpheres.not_unstable_of_three twoSpheres_special_finite _ (Sum.inl (pt 0))
      (Sum.inl (pt 1)) (Sum.inl (pt 2)) (inl_pt_ne (by decide)) (inl_pt_ne (by decide))
      (inl_pt_ne (by decide)) ⟨Or.inl ⟨0, rfl⟩, inl_mem_connectedComponent x _⟩
      ⟨Or.inl ⟨1, rfl⟩, inl_mem_connectedComponent x _⟩
      ⟨inl_pt2_mem_special, inl_mem_connectedComponent x _⟩
  · exact twoSpheres.not_unstable_of_three twoSpheres_special_finite _ (Sum.inr (pt 0))
      (Sum.inr (pt 1)) (Sum.inr (pt 2)) (inr_pt_ne (by decide)) (inr_pt_ne (by decide))
      (inr_pt_ne (by decide)) ⟨Or.inl ⟨2, rfl⟩, inr_mem_connectedComponent x _⟩
      ⟨Or.inl ⟨3, rfl⟩, inr_mem_connectedComponent x _⟩
      ⟨inr_pt2_mem_special, inr_mem_connectedComponent x _⟩

theorem twoSpheres_target (x : twoSpheres.S) : (extChartAt 𝓘(ℝ, E2) x).target = univ := by
  rcases x with x | x
  · exact (extChartAt_target_inl (M' := S2) x).trans (S2_target x)
  · exact (extChartAt_target_inr (M := S2) x).trans (S2_target x)

/-! ## 4. Holomorphic charts at the nodal points -/

/-- `σ₋₁` (centred at `e₂`) on the first sphere. -/
def holChartInl : OpenPartialHomeomorph S22 ℂ :=
  (holChart (-1) (by norm_num)).lift_openEmbedding Topology.IsOpenEmbedding.inl

/-- `σ₋₁` (centred at `e₂`) on the second sphere. -/
def holChartInr : OpenPartialHomeomorph S22 ℂ :=
  (holChart (-1) (by norm_num)).lift_openEmbedding Topology.IsOpenEmbedding.inr

theorem pt2_mem_holChart_neg_source : pt 2 ∈ (holChart (-1) (by norm_num)).source := by
  change (-1) * (pt 2 : E3) 2 ≠ 1
  simp [pt]
  norm_num

theorem holChart_neg_pt2 : holChart (-1) (by norm_num) (pt 2) = 0 := by
  change stereoC (-1) (pt 2) = 0
  simp [stereoC, pt]

theorem isHolChart_inl : twoSpheres.IsHolChart holChartInl (Sum.inl (pt 2)) := by
  have hcomp : (holChartInl ∘ Sum.inl : S2 → ℂ) = holChart (-1) (by norm_num) :=
    funext fun _ => OpenPartialHomeomorph.lift_openEmbedding_apply _ _
  refine ⟨⟨pt 2, pt2_mem_holChart_neg_source, rfl⟩, ?_, ?_⟩
  · exact (OpenPartialHomeomorph.lift_openEmbedding_apply _ _).trans holChart_neg_pt2
  · rintro _ ⟨y, hy, rfl⟩
    have hh := holChart_holo (-1) (by norm_num) y hy
    have e := mfderiv_inl (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, ℂ)) (holChartInl : S22 → ℂ) y
    rw [hcomp] at e
    refine ⟨?_, fun v => ?_⟩
    · change MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) (holChartInl : S22 → ℂ) (Sum.inl y)
      rw [mdifferentiableAt_inl_iff, hcomp]
      exact hh.1
    · change (show ℂ from mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) (holChartInl : S22 → ℂ) (Sum.inl y)
          (jStdMap y v)) = Complex.I *
        (show ℂ from mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) (holChartInl : S22 → ℂ) (Sum.inl y) v)
      rw [e]
      exact hh.2 v

theorem isHolChart_inr : twoSpheres.IsHolChart holChartInr (Sum.inr (pt 2)) := by
  have hcomp : (holChartInr ∘ Sum.inr : S2 → ℂ) = holChart (-1) (by norm_num) :=
    funext fun _ => OpenPartialHomeomorph.lift_openEmbedding_apply _ _
  refine ⟨⟨pt 2, pt2_mem_holChart_neg_source, rfl⟩, ?_, ?_⟩
  · exact (OpenPartialHomeomorph.lift_openEmbedding_apply _ _).trans holChart_neg_pt2
  · rintro _ ⟨y, hy, rfl⟩
    have hh := holChart_holo (-1) (by norm_num) y hy
    have e := mfderiv_inr (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, ℂ)) (holChartInr : S22 → ℂ) y
    rw [hcomp] at e
    refine ⟨?_, fun v => ?_⟩
    · change MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) (holChartInr : S22 → ℂ) (Sum.inr y)
      rw [mdifferentiableAt_inr_iff, hcomp]
      exact hh.1
    · change (show ℂ from mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) (holChartInr : S22 → ℂ) (Sum.inr y)
          (jStdMap y v)) = Complex.I *
        (show ℂ from mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) (holChartInr : S22 → ℂ) (Sum.inr y) v)
      rw [e]
      exact hh.2 v

/-! ## 5. The constant stable map on two spheres -/

section ConstMap

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ Q] in
/-- A constant map is of class `(k, δ)` near a point carrying a holomorphic chart onto `ℂ`. -/
theorem NodalSurface.isClassNear_const {m : ℕ} (X : NodalSurface m)
    {φ : OpenPartialHomeomorph X.S ℂ} {x : X.S} (hφ : X.IsHolChart φ x) (ht : φ.target = univ)
    (k : ℕ) (δ : ℝ) (q : Q) : X.IsClassNear (E := E) k δ (fun _ => q) x := by
  refine ⟨φ, hφ, 0, fun _ _ => ⟨by rw [ht]; trivial, mem_extChartAt_source q⟩,
    fun ℓ => ?_⟩
  convert memH_cutoff_mul_const k δ 0 using 1
  funext p
  simp

/-- **Witness for Memoir Definitions 1.1, 1.2 and 1.4 with two components**: the constant map
from two spheres joined at a node, with two marked points on each, is a stable map of class
`(k, δ)` for every target `(Q, ω)`, `k` and `δ`. -/
def twoSpheresStableMap (om : SymplecticForm E Q) (q : Q) (k : ℕ) (δ : ℝ) :
    StableMap om 4 k δ where
  dom := twoSpheres
  u _ := q
  continuous := continuous_const
  nodal p hp x hx := by
    obtain rfl : p = s(Sum.inl (pt 2), Sum.inr (pt 2)) := hp
    rcases Sym2.mem_iff.1 hx with rfl | rfl
    · exact twoSpheres.isClassNear_const isHolChart_inl rfl k δ q
    · exact twoSpheres.isClassNear_const isHolChart_inr rfl k δ q
  regular x _ := isHlocNear_const twoSpheres twoSpheres_target k q x
  matching _ _ _ := rfl
  area_nonneg x := (twoSpheres.area_const om q x).symm.le
  stable x h := absurd h (twoSpheres_not_unstable x)

end ConstMap

/-- A stable map of class `(3, δ₀)` into `(ℝ², ω₀)` whose domain has two components joined at a
node exists. -/
theorem exists_stableMap_two_components (δ₀ : ℝ) :
    ∃ α : StableMap omE2 4 3 δ₀, α.dom.nodes.Nonempty ∧ ¬ ConnectedSpace α.dom.S :=
  ⟨twoSpheresStableMap omE2 0 3 δ₀, twoSpheres_nodes_nonempty, twoSpheres_not_connectedSpace⟩

end GWMemoir
