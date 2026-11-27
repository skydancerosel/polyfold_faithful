import GWMemoir.CompletenessNodes

/-!
# Atlases of semi-norms at the nodes (Memoir p. 66)

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §3.1, p. 66.

The witness that the atlases of `GWMemoir.SectionSpaces`, whose neck blocks are honest
holomorphic polar coordinates, exist on surfaces with nodes, so that `sectionsClosed` and
`constraintsClosed` (`GWMemoir.CompletenessNodes`) are not vacuous there.

* `exists_neck_s0`: at a point with a holomorphic chart `φ`, for every continuous `u`, there is
  `s₀` with `e^{-2π(s+it)} ∈ φ.target` and `u(σ(s,t))` in the chart of `Q` at `u(x)` for `s ≥ s₀`.
* **`exists_sectionAtlas_of_hol`**: if every nodal point carries a holomorphic chart, every
  continuous `u` has an atlas: polar coordinates at the nodal points, and finitely many disc
  charts, avoiding the nodal points, on the compact complement of small discs around them.
* **`StableMap.exists_sectionAtlas`**: every stable map has an atlas (Definition 1.4 gives the
  holomorphic charts at the nodal points); `StableMap.sectionsClosed`,
  `StableMap.constraintsClosed`.
* `nodalStableMap_sectionsClosed`: the instance on the constant map from the noded sphere, a
  surface with a nodal pair.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Set Filter Topology MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

namespace NodalSurface

variable {m : ℕ} (X : NodalSurface m)

/-- The nodal points `|D|`. -/
def nodalPts : Set X.S := {x | ∃ q ∈ X.nodes, x ∈ q}

lemma finite_nodalPts : X.nodalPts.Finite := by
  have e : X.nodalPts = ⋃ q ∈ X.nodes, {x | x ∈ q} := by
    ext x; simp [nodalPts]
  rw [e]
  refine X.finite_nodes.biUnion fun q _ => ?_
  induction q using Sym2.ind with
  | _ a b =>
    exact ((Set.finite_singleton b).insert a).subset fun x hx => by
      rcases Sym2.mem_iff.1 hx with rfl | rfl <;> simp

variable {X}

/-- **Polar coordinates from some `s₀` on**: at a point with a holomorphic chart, for every
continuous `u`. -/
lemma exists_neck_s0 {u : X.S → Q} (hu : Continuous u) {φ : OpenPartialHomeomorph X.S ℂ}
    {x : X.S} (hφ : X.IsHolChart φ x) : ∃ s0 : ℝ, ∀ p : ℝ × ℝ, s0 ≤ p.1 →
      expPolar p ∈ φ.target ∧ u (X.polar φ p) ∈ (extChartAt 𝓘(ℝ, E) (u x)).source := by
  obtain ⟨hxs, hφ0, -⟩ := hφ
  have h0t : (0 : ℂ) ∈ φ.target := hφ0 ▸ φ.map_source hxs
  have hsym : φ.symm 0 = x := by rw [← hφ0, φ.left_inv hxs]
  have hV : φ.target ∩ (u ∘ φ.symm) ⁻¹' (extChartAt 𝓘(ℝ, E) (u x)).source ∈ 𝓝 (0 : ℂ) := by
    refine inter_mem (φ.open_target.mem_nhds h0t) ?_
    refine (hu.continuousAt.comp (φ.continuousAt_symm h0t)).preimage_mem_nhds ?_
    rw [Function.comp_apply, hsym]
    exact extChartAt_source_mem_nhds (u x)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hV
  have hπ := Real.pi_pos
  refine ⟨-Real.log r / (2 * Real.pi) + 1, fun p hp => ?_⟩
  have hn : ‖expPolar p‖ < r := by
    rw [norm_expPolar]
    have h1 : -2 * Real.pi * (-Real.log r / (2 * Real.pi) + 1) = Real.log r + -2 * Real.pi := by
      field_simp
      ring
    have h2 : Real.exp (-2 * Real.pi) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    calc Real.exp (-2 * Real.pi * p.1)
        ≤ Real.exp (-2 * Real.pi * (-Real.log r / (2 * Real.pi) + 1)) :=
          Real.exp_le_exp.2 (by nlinarith)
      _ = r * Real.exp (-2 * Real.pi) := by rw [h1, Real.exp_add, Real.exp_log hr]
      _ < r := by nlinarith
  exact hball (mem_ball_zero_iff.2 hn)

/-- Near the centre of a holomorphic chart, every point is the centre or a point
`σ(s, t)` with `s > T`. -/
lemma eq_or_polar_of_small {φ : OpenPartialHomeomorph X.S ℂ} {x : X.S} (hφ : X.IsHolChart φ x)
    (T : ℝ) {y : X.S} (hy : y ∈ φ.source) (hyb : ‖φ y‖ < Real.exp (-2 * Real.pi * T)) :
    y = x ∨ ∃ p : ℝ × ℝ, T < p.1 ∧ y = X.polar φ p := by
  obtain ⟨hxs, hφ0, -⟩ := hφ
  by_cases hyx : y = x
  · exact Or.inl hyx
  right
  have hφy : φ y ≠ 0 := fun h => hyx (φ.injOn hy hxs (h.trans hφ0.symm))
  obtain ⟨q, hq, hq1⟩ := exists_expPolar_eq hφy
  refine ⟨q, ?_, by rw [polar_eq, hq, φ.left_inv hy]⟩
  have hlog : Real.log ‖φ y‖ < -2 * Real.pi * T :=
    (Real.log_lt_iff_lt_exp (norm_pos_iff.2 hφy)).2 hyb
  rw [hq1, lt_div_iff₀ (by positivity)]
  linarith

end NodalSurface

open NodalSurface

variable {m : ℕ} (X : NodalSurface m)

/-- **Witness**: if every nodal point carries a holomorphic chart, every continuous `u` has an
atlas of semi-norms (Memoir p. 66). -/
theorem exists_sectionAtlas_of_hol (u : X.S → Q) (hu : Continuous u)
    (hhol : ∀ x ∈ X.nodalPts, ∃ φ, X.IsHolChart φ x) :
    Nonempty (SectionAtlas (E := E) X u) := by
  have hN := X.finite_nodalPts
  have hNc : IsClosed X.nodalPts := hN.isClosed
  have := hN.fintype
  choose φ hφ using fun x : X.nodalPts => hhol x.1 x.2
  choose s0 hs0 using fun x : X.nodalPts => exists_neck_s0 (E := E) hu (hφ x)
  -- the small discs around the nodal points
  set O : X.nodalPts → Set X.S := fun x =>
    (φ x).source ∩ φ x ⁻¹' Metric.ball 0 (Real.exp (-2 * Real.pi * (s0 x + 1)))
  have hOo : ∀ x, IsOpen (O x) := fun x => (φ x).isOpen_inter_preimage Metric.isOpen_ball
  have hxO : ∀ x, x.1 ∈ O x := fun x =>
    ⟨(hφ x).1, by rw [mem_preimage, (hφ x).2.1]; exact Metric.mem_ball_self (Real.exp_pos _)⟩
  set K : Set X.S := (⋃ x, O x)ᶜ
  have hK : IsCompact K := (isOpen_iUnion hOo).isClosed_compl.isCompact
  have hKN : ∀ z ∈ K, z ∉ X.nodalPts := fun z hz hzN =>
    hz (mem_iUnion.2 ⟨⟨z, hzN⟩, hxO ⟨z, hzN⟩⟩)
  set e := Fintype.equivFin X.nodalPts
  -- the disc charts away from the nodal points
  have hW : ∀ z : X.S, z ∉ X.nodalPts → ∃ ε > 0, ∀ w ∈ Metric.ball (extChartAt 𝓘(ℝ, E2) z z) ε,
      w ∈ (extChartAt 𝓘(ℝ, E2) z).target ∧
        u ((extChartAt 𝓘(ℝ, E2) z).symm w) ∈ (extChartAt 𝓘(ℝ, E) (u z)).source ∧
        (extChartAt 𝓘(ℝ, E2) z).symm w ∉ X.nodalPts := by
    intro z hz
    have h1 : (extChartAt 𝓘(ℝ, E2) z).target ∈ 𝓝 (extChartAt 𝓘(ℝ, E2) z z) :=
      extChartAt_target_mem_nhds z
    have hsc : ContinuousAt (extChartAt 𝓘(ℝ, E2) z).symm (extChartAt 𝓘(ℝ, E2) z z) :=
      continuousAt_extChartAt_symm z
    have h2 : (fun w => u ((extChartAt 𝓘(ℝ, E2) z).symm w)) ⁻¹' (extChartAt 𝓘(ℝ, E) (u z)).source
        ∈ 𝓝 (extChartAt 𝓘(ℝ, E2) z z) := by
      refine (hu.continuousAt.comp hsc).preimage_mem_nhds ?_
      rw [Function.comp_apply, extChartAt_to_inv]
      exact extChartAt_source_mem_nhds (u z)
    have h3 : (extChartAt 𝓘(ℝ, E2) z).symm ⁻¹' X.nodalPtsᶜ ∈ 𝓝 (extChartAt 𝓘(ℝ, E2) z z) := by
      refine hsc.preimage_mem_nhds ?_
      rw [extChartAt_to_inv]
      exact hNc.isOpen_compl.mem_nhds hz
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem (inter_mem h1 h2) h3)
    exact ⟨ε, hε, fun w hw => ⟨(hball hw).1.1, (hball hw).1.2, (hball hw).2⟩⟩
  choose! ε hε hball using hW
  set U : X.S → Set X.S := fun z => (extChartAt 𝓘(ℝ, E2) z).source ∩
    (extChartAt 𝓘(ℝ, E2) z) ⁻¹' Metric.ball (extChartAt 𝓘(ℝ, E2) z z) (ε z / 4) with hU
  have hUo : ∀ z, IsOpen (U z) := fun z =>
    (continuousOn_extChartAt z).isOpen_inter_preimage (isOpen_extChartAt_source z)
      Metric.isOpen_ball
  have hUz : ∀ z ∈ K, z ∈ U z := fun z hz =>
    ⟨mem_extChartAt_source z, Metric.mem_ball_self (by linarith [hε z (hKN z hz)])⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => U z) (fun z => hUo z)
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hUz y hy⟩)
  have hplace : ∀ z (p : ℝ × ℝ), 0 < ε z → p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 < 1 / 8 →
      X.place z (ε z) p ∈ Metric.ball (extChartAt 𝓘(ℝ, E2) z z) (ε z) := by
    intro z p hεz hp
    rw [Metric.mem_ball, NodalSurface.place, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hεz.le]
    have hn :
        ‖EuclideanSpace.single (0 : Fin 2) p.1 + EuclideanSpace.single 1 (p.2 - 1 / 2)‖ < 1 := by
      have := norm_sq_single_add_single p.1 (p.2 - 1 / 2)
      nlinarith [norm_nonneg (EuclideanSpace.single (0 : Fin 2) p.1 +
        EuclideanSpace.single 1 (p.2 - 1 / 2))]
    nlinarith
  have hcK : ∀ i : Fin t.card, (t.equivFin.symm i).1.1 ∉ X.nodalPts := fun i =>
    hKN _ (t.equivFin.symm i).1.2
  refine ⟨{
    nd := t.card
    center := fun i => (t.equivFin.symm i).1.1
    ε := fun i => ε (t.equivFin.symm i).1.1
    ε_pos := fun i => hε _ (hcK i)
    disc_chart := fun i p hp =>
      ⟨(hball _ (hcK i) _ (hplace _ p (hε _ (hcK i)) hp)).1,
        (hball _ (hcK i) _ (hplace _ p (hε _ (hcK i)) hp)).2.1⟩
    disc_avoid := fun i p hp q hq hmem =>
      (hball _ (hcK i) _ (hplace _ p (hε _ (hcK i)) hp)).2.2 ⟨q, hq, hmem⟩
    nn := Fintype.card X.nodalPts
    node := fun j => (e.symm j).1
    hol := fun j => φ (e.symm j)
    s0 := fun j => s0 (e.symm j)
    isHol := fun j => hφ (e.symm j)
    neck_chart := fun j => hs0 (e.symm j)
    node_nodal := fun j => (e.symm j).2
    nodal_node := fun q hq x hx => ⟨e ⟨x, q, hq, hx⟩, by simp⟩
    cover := fun y => ?_ }⟩
  by_cases hyK : y ∈ K
  · left
    obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.1 (ht hyK)
    obtain ⟨hys, hyb⟩ := hyz
    refine ⟨t.equivFin ⟨z, hzt⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    have hεz := hε z.1 (hKN z.1 z.2)
    set w : E2 := (ε z.1)⁻¹ • (extChartAt 𝓘(ℝ, E2) z.1 y - extChartAt 𝓘(ℝ, E2) z.1 z.1) with hw
    have hwn : ‖w‖ < 1 / 4 := by
      rw [hw, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hεz.le), ← dist_eq_norm]
      rw [mem_preimage, Metric.mem_ball] at hyb
      rw [inv_mul_lt_iff₀ hεz]; linarith
    refine ⟨(w 0, w 1 + 1 / 2), ?_, ?_⟩
    · have h := norm_sq_single_add_single (w 0) (w 1)
      rw [single_add_single_eq] at h
      simp only [add_sub_cancel_right]
      nlinarith [norm_nonneg w]
    · have hpl : X.place z.1 (ε z.1) (w 0, w 1 + 1 / 2) = extChartAt 𝓘(ℝ, E2) z.1 y := by
        rw [NodalSurface.place]
        simp only [add_sub_cancel_right]
        rw [single_add_single_eq, hw, smul_smul, mul_inv_cancel₀ hεz.ne', one_smul,
          add_sub_cancel]
      rw [NodalSurface.discPt, hpl, (extChartAt 𝓘(ℝ, E2) z.1).left_inv hys]
  · right
    obtain ⟨x, hyO⟩ := mem_iUnion.1 (not_not.1 hyK)
    refine ⟨e x, ?_⟩
    simp only [Equiv.symm_apply_apply]
    obtain ⟨hys, hyb⟩ := hyO
    rw [mem_preimage, mem_ball_zero_iff] at hyb
    rcases eq_or_polar_of_small (hφ x) _ hys hyb with h | ⟨p, hp, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, hp.le, h⟩

/-! ## Stable maps -/

variable {om : SymplecticForm E Q}

/-- **Every stable map has an atlas of semi-norms** (Memoir p. 66): Definition 1.4 gives a
holomorphic chart at every nodal point. -/
theorem StableMap.exists_sectionAtlas {k : ℕ} {δ : ℝ} (α : StableMap om m k δ) :
    Nonempty (SectionAtlas (E := E) α.dom α.u) :=
  exists_sectionAtlas_of_hol α.dom α.u α.continuous fun x ⟨q, hq, hx⟩ => by
    obtain ⟨φ, hφ, -⟩ := α.nodal q hq x hx
    exact ⟨φ, hφ⟩

/-- `SectionsClosed` for every stable map and every atlas. -/
theorem StableMap.sectionsClosed {k : ℕ} {δ' : ℝ} (α : StableMap om m k δ')
    (A : SectionAtlas (E := E) α.dom α.u) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) :
    SectionsClosed A δ h0 hmono :=
  GWMemoir.sectionsClosed α.continuous A δ h0 hmono

/-- `ConstraintsClosed` for every stable map and every atlas. -/
theorem StableMap.constraintsClosed {k : ℕ} {δ' : ℝ} (α : StableMap om m k δ')
    (A : SectionAtlas (E := E) α.dom α.u) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
    (C : LinearConstraints α.dom E) : ConstraintsClosed A δ h0 hmono C :=
  GWMemoir.constraintsClosed α.continuous A δ h0 hmono C

/-- **Instance with a node**: the constant map from the noded sphere (a nodal pair) has an
atlas, and `SectionsClosed` holds for each of its atlases. -/
theorem nodalStableMap_sectionsClosed (om : SymplecticForm E Q) (q : Q) (k : ℕ) (δ' : ℝ) :
    (nodalStableMap om q k δ').dom.nodes.Nonempty ∧
      Nonempty (SectionAtlas (E := E) (nodalStableMap om q k δ').dom
        (nodalStableMap om q k δ').u) ∧
      ∀ (A : SectionAtlas (E := E) (nodalStableMap om q k δ').dom (nodalStableMap om q k δ').u)
        (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ), SectionsClosed A δ h0 hmono :=
  ⟨sphereNode_nodes_nonempty, (nodalStableMap om q k δ').exists_sectionAtlas,
    fun A δ h0 hmono => (nodalStableMap om q k δ').sectionsClosed A δ h0 hmono⟩

end GWMemoir
