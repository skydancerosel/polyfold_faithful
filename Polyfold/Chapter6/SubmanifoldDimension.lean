import Polyfold.Chapter4.SmoothSubmanifoldBasics

/-!
# Dimension of submanifolds

The predicates `HasDimAt` and `IsSubmanifoldOfDim` and the rank of tangent spaces under chart
changes. The propositions of Chapter 9 are in `Chapter9/Propositions.lean`.
-/

set_option maxSynthPendingDepth 3
open Set Module Submodule Filter Topology
noncomputable section
namespace Polyfold
section TangentDim
variable {E E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}

/-- The tangent space of a retract at a level-`1` point is a linear subspace: it equals its span. -/
theorem coe_span_tangentSpace {Q : Set (E 0)} (hQ : IsScRetract E C Q) {z : E 1}
    (hz : z ∈ E.lvlSet Q 1) :
    (span ℝ (tangentSpace E C Q z) : Set (E 0)) = tangentSpace E C Q z := by
  obtain ⟨S, rfl⟩ := hQ
  rw [tangentSpace_eq_coe_submodule S hz, span_eq]

/-- **The dimension of the tangent space of a sub-retract is carried by a germ of
sc-diffeomorphisms**: in the situation of `IsGoodPositionRetractAt.transport`, the derivative
`D(F ∘ r)(z)` restricts to a linear isomorphism `T_zQ ≅ T_{F(z)}Q'` (inverse `D(G ∘ r')(F(z))`),
so the two tangent spaces have the same `finrank`. -/
theorem finrank_span_tangentSpace_eq {R : ScRetraction E C} {R' : ScRetraction E' C'}
    {F : E 0 → E' 0} {G : E' 0 → E 0} (h : R.IsDiffeoGerm R' F G)
    (hFs : IsScSmooth R.U (F ∘ R)) (hGs : IsScSmooth R'.U (G ∘ R'))
    {Q : Set (E 0)} {Q' : Set (E' 0)} (hQ : IsScRetract E C Q) (hQ' : IsScRetract E' C' Q')
    (hQR : Q ⊆ R.retract) (hQ'R : Q' ⊆ R'.retract) (hFQ : MapsTo F Q Q') (hGQ : MapsTo G Q' Q)
    {z : E 1} (hz : z ∈ E.lvlSet Q 1) :
    finrank ℝ (span ℝ (tangentSpace E C Q z)) =
      finrank ℝ (span ℝ (tangentSpace E' C' Q' (levelMap (F ∘ R) 1 z))) := by
  have hx : z ∈ E.lvlSet R.retract 1 := hQR hz
  have hy' : levelMap (F ∘ R) 1 z ∈ E'.lvlSet R'.retract 1 := h.image_mem hx
  have hzQ' : levelMap (F ∘ R) 1 z ∈ E'.lvlSet Q' 1 := by
    rw [ScBanach.mem_lvlSet, h.toBase_image hx]; exact hFQ hz
  have himg : levelMap (G ∘ R') 1 (levelMap (F ∘ R) 1 z) = z := h.image_image hx
  have hT := coe_span_tangentSpace hQ hz
  have hT' := coe_span_tangentSpace hQ' hzQ'
  have ha : ∀ v ∈ span ℝ (tangentSpace E C Q z),
      scDeriv R.U (F ∘ R) z v ∈ span ℝ (tangentSpace E' C' Q' (levelMap (F ∘ R) 1 z)) := by
    intro v hv
    rw [← SetLike.mem_coe, hT] at hv
    rw [← SetLike.mem_coe, hT']
    exact scDeriv_mem_tangentSpace_of_subset R hFs hQ hQ' hQR hFQ hz hv
  have ha' : ∀ w ∈ span ℝ (tangentSpace E' C' Q' (levelMap (F ∘ R) 1 z)),
      scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) w ∈ span ℝ (tangentSpace E C Q z) := by
    intro w hw
    rw [← SetLike.mem_coe, hT'] at hw
    rw [← SetLike.mem_coe, hT]
    have := scDeriv_mem_tangentSpace_of_subset R' hGs hQ' hQ hQ'R hGQ hzQ' hw
    rwa [himg] at this
  have h1 : ∀ v ∈ span ℝ (tangentSpace E C Q z),
      scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) (scDeriv R.U (F ∘ R) z v) = v := by
    intro v hv
    rw [← SetLike.mem_coe, hT] at hv
    have hv' := tangentSpace_subset_of_subset R hQ hQR hz hv
    rw [tangentSpace_eq_range R hx] at hv'
    obtain ⟨w, rfl⟩ := hv'
    rw [h.deriv_inv_deriv hx]
    exact congrArg (fun L : E 0 →L[ℝ] E 0 => L w) (R.scDeriv_comp_self hx)
  have h2 : ∀ w ∈ span ℝ (tangentSpace E' C' Q' (levelMap (F ∘ R) 1 z)),
      scDeriv R.U (F ∘ R) z (scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) w) = w := by
    intro w hw
    rw [← SetLike.mem_coe, hT'] at hw
    have hw' := tangentSpace_subset_of_subset R' hQ' hQ'R hzQ' hw
    rw [tangentSpace_eq_range R' hy'] at hw'
    obtain ⟨u, rfl⟩ := hw'
    rw [h.deriv_deriv_inv hx]
    exact congrArg (fun L : E' 0 →L[ℝ] E' 0 => L u) (R'.scDeriv_comp_self hy')
  exact (restrictEquiv _ _ _ _ ha ha' h1 h2).toLinearEquiv.finrank_eq

end TangentDim

namespace MPolyfold
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

variable (P : MPolyfold X) in
/-- **The dimension of a smooth finite-dimensional submanifold at a point** (Remark 9.1.1: "the
dimension of `T_mM`"): `A` has dimension `k` at `a ∈ A` if, for some data `d` of Definition 4.13
at `a`, some chart `φ` of `X` at `a` and the level-`1` point `z` over `φ(a)`, the tangent space
`T_aA = T_z(φ(W ∩ A))` (Remark 4.14) has dimension `k`.  `T_aX` carries no linear structure in
Part I (point G.7), so the condition is stated in a chart, as Definition 4.16 is; it then holds for
all charts (`HasDimAt.finrank_eq`), and `k` is unique (`HasDimAt.unique`). -/
def HasDimAt (A : Set X) (a : X) (k : ℕ) : Prop :=
  a ∈ A ∧ ∃ (d : P.SubmanifoldData A) (φ : MChart X) (z : φ.model.E 1),
    a ∈ d.V ∧ P.IsChart φ ∧ a ∈ φ.source ∧ φ.model.E.toBase 1 z = φ a ∧
    finrank ℝ (span ℝ (tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) z)) = k

variable {P : MPolyfold X}

/-- **The chart change for the dimension of the tangent spaces of `A`**: for charts `φ`, `φ'` of
`X`, open `G ⊆ dom φ`, `G' ⊆ dom φ'` with `φ(G ∩ A)`, `φ'(G' ∩ A)` retracts, a smooth point
`a ∈ A ∩ G ∩ G'` and level-`1` points `z`, `z'` over `φ(a)`, `φ'(a)`, the tangent spaces
`T_z(φ(G ∩ A))` and `T_{z'}(φ'(G' ∩ A))` have the same dimension (`chart_change_of_transport`
for the property "`finrank T_zQ = k`", with `finrank_span_tangentSpace_eq`). -/
theorem finrank_tangentSpace_chart_change {P : MPolyfold X} {φ φ' : MChart X} (hφ : P.IsChart φ)
    (hφ' : P.IsChart φ') {A G G' : Set X} (hG : IsOpen G) (hG' : IsOpen G')
    (hGφ : G ⊆ φ.source) (hGφ' : G' ⊆ φ'.source)
    (hQ : IsScRetract φ.model.E φ.model.C (φ '' (G ∩ A)))
    (hQ' : IsScRetract φ'.model.E φ'.model.C (φ' '' (G' ∩ A))) {a : X} (haA : a ∈ A)
    (haG : a ∈ G) (haG' : a ∈ G') (has : a ∈ P.smoothSet) {z : φ.model.E 1}
    {z' : φ'.model.E 1} (hz : φ.model.E.toBase 1 z = φ a)
    (hz' : φ'.model.E.toBase 1 z' = φ' a) :
    finrank ℝ (span ℝ (tangentSpace φ.model.E φ.model.C (φ '' (G ∩ A)) z)) =
      finrank ℝ (span ℝ (tangentSpace φ'.model.E φ'.model.C (φ' '' (G' ∩ A)) z')) := by
  have hzs : z ∈ φ.model.E.smoothLvl 1 := by
    change φ.model.E.toBase 1 z ∈ (φ.model.E.smooth : Set (φ.model.E 0))
    rw [hz]; exact (mem_smoothSet_iff hφ (hGφ haG)).1 has
  obtain ⟨n, Wq, T, hT⟩ := φ.model.isPartialQuadrant
  obtain ⟨n', Wq', T', hT'⟩ := φ'.model.isPartialQuadrant
  exact chart_change_of_transport
    (fun E C _ Q _ _ _ w => finrank ℝ (span ℝ (tangentSpace E C Q w)) =
      finrank ℝ (span ℝ (tangentSpace φ.model.E φ.model.C (φ '' (G ∩ A)) z)))
    (fun _ _ _ _ _ _ _ _ _ _ hQ _ h => by rw [← hQ]; exact h)
    (fun _ _ _ _ _ _ _ _ h hF hG _ _ hQ hQ' hQR hQ'R hFQ hGQ _ hz _ _ _ _ _ _ _ _ _ hk => by
      rw [← finrank_span_tangentSpace_eq h hF hG hQ hQ' hQR hQ'R hFQ hGQ hz]; exact hk)
    hφ hφ' hG hG' hGφ hGφ' hQ hQ' haA haG haG' hz hz' hzs T hT T' hT' rfl |>.symm

/-- **The dimension is independent of the choices** (the chart, the data of Definition 4.13, or
any open piece `G` of a chart domain on which `A` is a retract): if `A` has dimension `k` at `a`,
the tangent space at `a` of every such chart model of `A` has dimension `k`. -/
theorem HasDimAt.finrank_eq' {A : Set X} {a : X} {k : ℕ} (h : P.HasDimAt A a k)
    {φ' : MChart X} (hφ' : P.IsChart φ') {G' : Set X} (hG' : IsOpen G') (hGφ' : G' ⊆ φ'.source)
    (hQ' : IsScRetract φ'.model.E φ'.model.C (φ' '' (G' ∩ A))) (haG' : a ∈ G')
    {z' : φ'.model.E 1} (hz' : φ'.model.E.toBase 1 z' = φ' a) :
    finrank ℝ (span ℝ (tangentSpace φ'.model.E φ'.model.C (φ' '' (G' ∩ A)) z')) = k := by
  obtain ⟨haA, d, φ, z, ha, hφ, haφ, hz, hk⟩ := h
  have has : a ∈ P.smoothSet := by
    have := d.apply_mem_smooth hφ haA ha haφ
    exact (mem_smoothSet_iff hφ haφ).2 this
  rw [← hk]
  exact (finrank_tangentSpace_chart_change hφ hφ' (d.toSubData.isOpen_shrink φ) hG'
    (d.toSubData.shrink_subset_source φ) hGφ' (d.toSubData.isScRetract_image φ hφ) hQ' haA
    (d.toSubData.mem_shrink φ haA ha haφ) haG' has hz hz').symm

/-- **The dimension is independent of the choices**, for the chart models of Definition 4.13. -/
theorem HasDimAt.finrank_eq {A : Set X} {a : X} {k : ℕ} (h : P.HasDimAt A a k)
    (d' : P.SubmanifoldData A) {φ' : MChart X} (hφ' : P.IsChart φ') {z' : φ'.model.E 1}
    (ha' : a ∈ d'.V) (haφ' : a ∈ φ'.source) (hz' : φ'.model.E.toBase 1 z' = φ' a) :
    finrank ℝ (span ℝ (tangentSpace φ'.model.E φ'.model.C
      (φ' '' (d'.toSubData.shrink φ' ∩ A)) z')) = k :=
  h.finrank_eq' hφ' (d'.toSubData.isOpen_shrink φ') (d'.toSubData.shrink_subset_source φ')
    (d'.toSubData.isScRetract_image φ' hφ') (d'.toSubData.mem_shrink φ' h.1 ha' haφ') hz'

/-- The dimension of `A` at `a` can be read in any chart model `φ(G ∩ A)` of `A`. -/
theorem hasDimAt_of_finrank {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : X} (haA : a ∈ A)
    {φ : MChart X} (hφ : P.IsChart φ) {G : Set X} (hG : IsOpen G) (hGφ : G ⊆ φ.source)
    (hQ : IsScRetract φ.model.E φ.model.C (φ '' (G ∩ A))) (haG : a ∈ G) {z : φ.model.E 1}
    (hz : φ.model.E.toBase 1 z = φ a) {k : ℕ}
    (hk : finrank ℝ (span ℝ (tangentSpace φ.model.E φ.model.C (φ '' (G ∩ A)) z)) = k) :
    P.HasDimAt A a k := by
  set d := hA.data haA
  refine ⟨haA, d, φ, z, hA.mem_data_V haA, hφ, hGφ haG, hz, ?_⟩
  rw [← hk]
  exact (finrank_tangentSpace_chart_change hφ hφ (d.toSubData.isOpen_shrink φ) hG
    (d.toSubData.shrink_subset_source φ) hGφ (d.toSubData.isScRetract_image φ hφ) hQ haA
    (d.toSubData.mem_shrink φ haA (hA.mem_data_V haA) (hGφ haG)) haG
    (hA.subset_smoothSet haA) hz hz)

/-- **The dimension is a germ**: for `V` open and `a ∈ V`, `A ∩ V` has dimension `k` at `a` iff
`A` has. -/
theorem hasDimAt_inter_isOpen_iff {A V : Set X} (hA : P.IsSmoothSubmanifold A) (hV : IsOpen V)
    {a : X} (haV : a ∈ V) {k : ℕ} : P.HasDimAt (A ∩ V) a k ↔ P.HasDimAt A a k := by
  have hset : ∀ G : Set X, G ∩ (A ∩ V) = (G ∩ V) ∩ A := fun G => by
    ext; simp only [mem_inter_iff]; tauto
  constructor
  · rintro ⟨⟨haA, -⟩, d, φ, z, ha, hφ, haφ, hz, hk⟩
    have hQ := d.toSubData.isScRetract_image φ hφ
    rw [hset] at hQ hk
    exact hasDimAt_of_finrank hA haA hφ ((d.toSubData.isOpen_shrink φ).inter hV)
      (fun x hx => d.toSubData.shrink_subset_source φ hx.1) hQ
      ⟨d.toSubData.mem_shrink φ ⟨haA, haV⟩ ha haφ, haV⟩ hz hk
  · intro h
    have haA : a ∈ A := h.1
    have hAV := hA.inter_isOpen hV
    set d := hAV.data ⟨haA, haV⟩
    obtain ⟨φ, hφ, haφ⟩ := P.exists_isChart_mem_source a
    have hs : φ a ∈ φ.model.E.smooth := (mem_smoothSet_iff hφ haφ).1 (hA.subset_smoothSet haA)
    obtain ⟨z, hz, -⟩ := exists_smoothLvl_one_of_mem_smooth hs
    refine ⟨⟨haA, haV⟩, d, φ, z, hAV.mem_data_V ⟨haA, haV⟩, hφ, haφ, hz, ?_⟩
    have hQ := d.toSubData.isScRetract_image φ hφ
    rw [hset] at hQ ⊢
    exact h.finrank_eq' hφ ((d.toSubData.isOpen_shrink φ).inter hV)
      (fun x hx => d.toSubData.shrink_subset_source φ hx.1) hQ
      ⟨d.toSubData.mem_shrink φ ⟨haA, haV⟩ (hAV.mem_data_V ⟨haA, haV⟩) haφ, haV⟩ hz

variable (P) in
/-- **An `n`-dimensional submanifold** (Remark 9.1.1): a smooth finite-dimensional submanifold
(Definition 4.13 [4.4]) with `dim T_aA = n` at every point. -/
def IsSubmanifoldOfDim (A : Set X) (n : ℕ) : Prop :=
  P.IsSmoothSubmanifold A ∧ ∀ a ∈ A, P.HasDimAt A a n

end MPolyfold
end Polyfold
end
