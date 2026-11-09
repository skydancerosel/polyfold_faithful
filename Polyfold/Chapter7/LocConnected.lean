import Polyfold.Chapter2.MPolyfold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017), Part II, Chapter 7: the connected
neighbourhoods used for the natural representation (the discussion after **Theorem 7.1.13 (2017: 7.1)**,
pp. 231–233, **Proposition 7.1.15 (2017: 7.5)**, pp. 233–236, and the proof of **Theorem 7.6.1 (2017: 7.5)**, pp. 253–254) and
the connected components of **Corollary 7.3.8 (2017: 7.2)** (p. 326 (2017 p. 247)).

# Local path connectedness of retracts and M-polyfolds

## The text, paraphrased

(p. 231) "We choose the connected open neighborhood `U(x) ⊂ X` so small that `𝐔(x)` splits into
`#G_x`-many (disjoint) connected components" `𝐔(g)`, `g ∈ G_x`.  (Proposition 7.1.15 (2017: 7.5)) A finite set
`Y` of isomorphic objects has "mutually disjoint connected open neighborhoods `U(y)` contained in
`V`".  (Proof of Theorem 7.6.1 (2017: 7.5)) "For every `g ∈ G_{x₀}` we choose two contractible open
neighborhoods `N^t_g` and `N^s_g`" on which `t` and `s` are sc-diffeomorphisms; "since the `N_g`
are disjoint and since the structure maps are continuous we conclude that `Φ` is a homomorphism".
(Corollary 7.3.8 (2017: 7.2)) "We work in a connected component of `K`".  The text does not state that these
connected neighbourhoods exist.

## What is formalized

* `ScRetraction.exists_ball_joinedIn`: **`r` maps segments to paths**.  For `o ∈ O = r(U)` and a
  neighbourhood `W` of `o` there is `ε > 0` such that every `p ∈ O` with `‖p − o‖ < ε` is joined
  to `o` inside `O ∩ W` by the path `τ ↦ r(o + τ(p − o))`: the segment lies in the convex set
  `B_ε(o) ∩ C ⊆ U`, and `r` fixes `o` and `p`.
* `IsScRetract.locallyPathConnectedSpace`: **an sc-smooth retract is locally path connected**.
* `MChart.pathComponentIn_mem_nhds` and `MPolyfold.locallyPathConnectedSpace`: **an M-polyfold is
  locally path connected** (through any chart around the point; only level `0` is used).
* Consequences for an M-polyfold `X`: `MPolyfold.locallyConnectedSpace`;
  `MPolyfold.hasBasis_isOpen_isConnected` and `MPolyfold.hasBasis_isOpen_isPathConnected`
  (connected, resp. path connected, open neighbourhoods form a neighbourhood basis);
  `MPolyfold.exists_isOpen_isConnected_subset`; **components are open**:
  `MPolyfold.isOpen_connectedComponent`, `MPolyfold.isOpen_connectedComponentIn` (components of
  open sets), `MPolyfold.isOpen_pathComponentIn`; `MPolyfold.isConnected_iff_isPathConnected`
  for open sets; and `MPolyfold.locallyPathConnectedSpace_quotient`: every quotient of `X`, in
  particular an orbit space `|X|`, is locally path connected, so its components are open.
* `exists_pairwiseDisjoint_isOpen_isConnected` (and `MPolyfold.…`): finitely many points of a
  Hausdorff locally connected space have pairwise disjoint connected open neighbourhoods inside
  a given open set (Proposition 7.1.15 (2017: 7.5)).
* `eqOn_sections_of_isPreconnected`: two continuous sections of a locally injective `p : M → X`,
  `M` Hausdorff, agree on a preconnected set as soon as they agree at one point (Mathlib's
  `IsSeparatedMap.eqOn_of_comp_eqOn`).  For a local homeomorphism `s` this is the uniqueness of
  `Γ(g, ·) = s_g⁻¹` on a connected `U`, which makes `Φ` a homomorphism.

## Reading

* "Connected" is Mathlib's `IsConnected` (nonempty and preconnected); open connected sets of an
  M-polyfold are path connected (`MPolyfold.isConnected_iff_isPathConnected`).
* The "contractible" neighbourhoods `N^t_g`, `N^s_g` of the proof of Theorem 7.6.1 (2017: 7.5) are not
  formalized: the proof needs only connectedness (plan II.6, 3), which is provided here.  The
  segment homotopy `(p, τ) ↦ r(o + τ(p − o))` contracts `O ∩ B_ε(o)` inside the larger `O ∩ W`;
  that small neighbourhoods are themselves contractible is not claimed.
* The paths are continuous paths at level `0`, not sc-smooth paths; sc-smooth paths between
  smooth points are `exists_nhds_scPath` of Chapter 6 (`ScPaths.lean`).
-/

open Set Filter Topology Function
open scoped unitInterval

noncomputable section

namespace Polyfold

/-! ### Retracts -/

namespace ScRetraction

variable {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C)

/-- **`r` maps segments to paths**: for `o ∈ O = r(U)` and a neighbourhood `W` of `o` there is
`ε > 0` such that every `p ∈ O` with `‖p − o‖ < ε` is joined to `o` inside `O ∩ W`, by the path
`τ ↦ r(o + τ(p − o))`. -/
theorem exists_ball_joinedIn {o : E 0} (ho : o ∈ R.retract) {W : Set (E 0)} (hW : W ∈ 𝓝 o) :
    ∃ ε > 0, ∀ p ∈ R.retract, p ∈ Metric.ball o ε → JoinedIn (R.retract ∩ W) o p := by
  have hoU : o ∈ R.U := R.retract_subset ho
  have hro : R o = o := R.apply_eq_self_of_mem_retract ho
  obtain ⟨O', hO'o, hO'⟩ := R.relOpen.relOpen
  have hUC : R.U ⊆ C := by rw [hO']; exact inter_subset_right
  have hcont : ContinuousOn R R.U := R.isSc1.isSc0.continuousOn_base
  -- `r⁻¹(W)` is a neighbourhood of `o` in `U`, and `U` contains `B_δ(o) ∩ C`
  have hpre : R ⁻¹' W ∈ 𝓝[R.U] o := hcont o hoU (by rw [hro]; exact hW)
  obtain ⟨ε₁, hε₁, hε₁W⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  obtain ⟨δ, hδ, hδO'⟩ := Metric.isOpen_iff.1 hO'o o (by rw [hO'] at hoU; exact hoU.1)
  set B := Metric.ball o (min ε₁ δ) ∩ C with hB
  have hBU : ∀ q ∈ B, q ∈ R.U ∧ R q ∈ W := fun q hq => by
    have hqU : q ∈ R.U := by
      rw [hO']
      exact ⟨hδO' (Metric.ball_subset_ball (min_le_right _ _) hq.1), hq.2⟩
    exact ⟨hqU, hε₁W ⟨Metric.ball_subset_ball (min_le_left _ _) hq.1, hqU⟩⟩
  refine ⟨min ε₁ δ, lt_min hε₁ hδ, fun p hp hpB => ?_⟩
  -- the segment from `o` to `p` lies in the convex set `B`
  have hline : ∀ τ ∈ I, AffineMap.lineMap o p τ ∈ B := fun τ hτ =>
    ((convex_ball _ _).inter R.relOpen.isPartialQuadrant.convex).lineMap_mem
      ⟨Metric.mem_ball_self (lt_min hε₁ hδ), hUC hoU⟩ ⟨hpB, hUC (R.retract_subset hp)⟩ hτ
  refine JoinedIn.ofLine (f := fun τ : ℝ => R (AffineMap.lineMap o p τ)) ?_ ?_ ?_ ?_
  · exact hcont.comp AffineMap.lineMap_continuous.continuousOn fun τ hτ => (hBU _ (hline τ hτ)).1
  · simp only [AffineMap.lineMap_apply_zero, hro]
  · simp only [AffineMap.lineMap_apply_one, R.apply_eq_self_of_mem_retract hp]
  · rintro _ ⟨τ, hτ, rfl⟩
    exact ⟨R.apply_mem_retract (hBU _ (hline τ hτ)).1, (hBU _ (hline τ hτ)).2⟩

end ScRetraction

/-- **An sc-smooth retract is locally path connected** (with the topology of `E₀`). -/
theorem IsScRetract.locallyPathConnectedSpace {E : ScBanach} {C O : Set (E 0)}
    (h : IsScRetract E C O) : LocallyPathConnectedSpace O := by
  obtain ⟨R, rfl⟩ := h
  refine locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.2 fun o u hu hou => ?_
  obtain ⟨W, hWo, rfl⟩ := isOpen_induced_iff.1 hu
  obtain ⟨ε, hε, hjoin⟩ := R.exists_ball_joinedIn o.2 (hWo.mem_nhds hou)
  refine mem_of_superset ((Metric.isOpen_ball.preimage continuous_subtype_val).mem_nhds
    (Metric.mem_ball_self hε)) fun q hq => ?_
  have hj := hjoin q q.2 hq
  have hqW : q ∈ Subtype.val ⁻¹' W := hj.target_mem.2
  rw [← Subtype.image_preimage_coe] at hj
  exact (IsInducing.subtypeVal.joinedIn_image hou hqW).1 hj

/-! ### M-polyfolds -/

namespace MChart

variable {X : Type*} [TopologicalSpace X]

/-- **Path components near a point of a chart domain are neighbourhoods**: for `x` in the domain
of a chart `φ` and a neighbourhood `u` of `x`, the path component of `x` in `u` is a neighbourhood
of `x` (it contains `φ⁻¹(B_ε(φ(x)))` for small `ε`). -/
theorem pathComponentIn_mem_nhds (φ : MChart X) {x : X} (hx : x ∈ φ.source) {u : Set X}
    (hu : u ∈ 𝓝 x) : pathComponentIn u x ∈ 𝓝 x := by
  obtain ⟨u', hu'u, hu'o, hxu'⟩ := mem_nhds_iff.1 hu
  refine mem_of_superset ?_ (pathComponentIn_mono hu'u)
  obtain ⟨W, hWo, hWs⟩ :=
    φ.exists_isOpen_image_eq (inter_subset_right (s := u')) (hu'o.inter φ.isOpen_source)
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  have hxO : φ x ∈ R.retract := hR ▸ φ.mapsTo_model x hx
  have hxW : φ x ∈ W := by
    have : φ x ∈ φ '' (u' ∩ φ.source) := mem_image_of_mem φ ⟨hxu', hx⟩
    rw [hWs] at this
    exact this.2
  obtain ⟨ε, hε, hjoin⟩ := R.exists_ball_joinedIn hxO (hWo.mem_nhds hxW)
  have hN : φ.source ∩ φ ⁻¹' Metric.ball (φ x) ε ∈ 𝓝 x :=
    (φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source Metric.isOpen_ball).mem_nhds
      ⟨hx, Metric.mem_ball_self hε⟩
  refine mem_of_superset hN fun y hy => ?_
  have hyO : φ y ∈ R.retract := hR ▸ φ.mapsTo_model y hy.1
  have hj := (hjoin _ hyO hy.2).map_continuousOn (f := φ.symm)
    (φ.continuousOn_invFun.mono fun z hz => hR ▸ hz.1)
  rw [φ.symm_apply_apply hx, φ.symm_apply_apply hy.1] at hj
  refine hj.mono ?_
  rintro _ ⟨z, ⟨hzO, hzW⟩, rfl⟩
  have hz : z ∈ φ '' (u' ∩ φ.source) := by
    rw [hWs]
    exact ⟨hR ▸ hzO, hzW⟩
  obtain ⟨w, hw, rfl⟩ := hz
  rw [φ.symm_apply_apply hw.2]
  exact hw.1

end MChart

namespace MPolyfold

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

include P

/-- **An M-polyfold is locally path connected.** -/
theorem locallyPathConnectedSpace : LocallyPathConnectedSpace X :=
  locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.2 fun x _ hu hxu => by
    obtain ⟨φ, -, hx⟩ := P.exists_isChart_mem_source x
    exact φ.pathComponentIn_mem_nhds hx (hu.mem_nhds hxu)

/-- An M-polyfold is locally connected. -/
theorem locallyConnectedSpace : LocallyConnectedSpace X :=
  have := P.locallyPathConnectedSpace
  inferInstance

/-- **Connected open neighbourhoods form a neighbourhood basis** of every point of an
M-polyfold. -/
theorem hasBasis_isOpen_isConnected (x : X) :
    (𝓝 x).HasBasis (fun U : Set X => IsOpen U ∧ x ∈ U ∧ IsConnected U) id :=
  have := P.locallyConnectedSpace
  LocallyConnectedSpace.open_connected_basis x

/-- **Path connected open neighbourhoods form a neighbourhood basis** of every point of an
M-polyfold. -/
theorem hasBasis_isOpen_isPathConnected (x : X) :
    (𝓝 x).HasBasis (fun U : Set X => IsOpen U ∧ x ∈ U ∧ IsPathConnected U) id :=
  have := P.locallyPathConnectedSpace
  isOpen_isPathConnected_basis x

/-- Every neighbourhood of a point of an M-polyfold contains a connected open neighbourhood. -/
theorem exists_isOpen_isConnected_subset {x : X} {V : Set X} (hV : V ∈ 𝓝 x) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ IsConnected U := by
  obtain ⟨U, ⟨hUo, hxU, hUc⟩, hUV⟩ := (P.hasBasis_isOpen_isConnected x).mem_iff.1 hV
  exact ⟨U, hUo, hxU, hUV, hUc⟩

/-- **Components are open**: the connected components of an M-polyfold are open. -/
theorem isOpen_connectedComponent (x : X) : IsOpen (connectedComponent x) :=
  have := P.locallyConnectedSpace
  _root_.isOpen_connectedComponent

/-- **Components of open sets are open** in an M-polyfold. -/
theorem isOpen_connectedComponentIn {U : Set X} (hU : IsOpen U) (x : X) :
    IsOpen (connectedComponentIn U x) :=
  have := P.locallyConnectedSpace
  hU.connectedComponentIn

/-- Path components of open sets are open in an M-polyfold. -/
theorem isOpen_pathComponentIn {U : Set X} (hU : IsOpen U) (x : X) :
    IsOpen (pathComponentIn U x) :=
  have := P.locallyPathConnectedSpace
  hU.pathComponentIn x

/-- An open subset of an M-polyfold is connected iff it is path connected. -/
theorem isConnected_iff_isPathConnected {U : Set X} (hU : IsOpen U) :
    IsConnected U ↔ IsPathConnected U :=
  have := P.locallyPathConnectedSpace
  hU.isConnected_iff_isPathConnected

/-- **Quotients of an M-polyfold are locally path connected**; in particular an orbit space
`|X| = X/∼` with the quotient topology is, and its connected components are open. -/
theorem locallyPathConnectedSpace_quotient (r : Setoid X) :
    LocallyPathConnectedSpace (Quotient r) :=
  have := P.locallyPathConnectedSpace
  inferInstance

end MPolyfold

/-! ### Disjoint connected neighbourhoods and sections over connected sets -/

/-- **Disjoint connected neighbourhoods of finitely many points** (Proposition 7.1.15 (2017: 7.5)): in a
Hausdorff locally connected space, finitely many points of an open set `V` have pairwise disjoint
connected open neighbourhoods contained in `V`. -/
theorem exists_pairwiseDisjoint_isOpen_isConnected {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyConnectedSpace X] {S V : Set X} (hS : S.Finite) (hV : IsOpen V) (hSV : S ⊆ V) :
    ∃ U : X → Set X, (∀ y ∈ S, IsOpen (U y) ∧ y ∈ U y ∧ U y ⊆ V ∧ IsConnected (U y)) ∧
      S.PairwiseDisjoint U := by
  obtain ⟨U₀, hU₀, hdisj⟩ := hS.t2_separation
  have hmem : ∀ y ∈ S, y ∈ U₀ y ∩ V := fun y hy => ⟨(hU₀ y).1, hSV hy⟩
  refine ⟨fun y => connectedComponentIn (U₀ y ∩ V) y, fun y hy => ⟨?_, ?_, ?_, ?_⟩,
    hdisj.mono fun y => (connectedComponentIn_subset _ _).trans inter_subset_left⟩
  · exact ((hU₀ y).2.inter hV).connectedComponentIn
  · exact mem_connectedComponentIn (hmem y hy)
  · exact (connectedComponentIn_subset _ _).trans inter_subset_right
  · exact isConnected_connectedComponentIn_iff.2 (hmem y hy)

/-- **Disjoint connected neighbourhoods of finitely many points of an M-polyfold**, contained
in a given open set (Proposition 7.1.15 (2017: 7.5)). -/
theorem MPolyfold.exists_pairwiseDisjoint_isOpen_isConnected {X : Type*} [TopologicalSpace X]
    [T2Space X] [ParacompactSpace X] (P : MPolyfold X) {S V : Set X} (hS : S.Finite)
    (hV : IsOpen V) (hSV : S ⊆ V) :
    ∃ U : X → Set X, (∀ y ∈ S, IsOpen (U y) ∧ y ∈ U y ∧ U y ⊆ V ∧ IsConnected (U y)) ∧
      S.PairwiseDisjoint U :=
  have := P.locallyConnectedSpace
  Polyfold.exists_pairwiseDisjoint_isOpen_isConnected hS hV hSV

/-- **Sections of a locally injective map agree on a connected set if they agree at one
point**: if `p : M → X` is locally injective, `M` is Hausdorff, `σ₁, σ₂` are continuous on a
preconnected `U` with `p ∘ σᵢ = id` on `U`, and `σ₁(y₀) = σ₂(y₀)` for some `y₀ ∈ U`, then
`σ₁ = σ₂` on `U`.  (For the source map `s` of an ep-groupoid this is the uniqueness of
`Γ(g, ·) = s_g⁻¹` on a connected `U`.) -/
theorem eqOn_sections_of_isPreconnected {M X : Type*} [TopologicalSpace M] [T2Space M]
    [TopologicalSpace X] {p : M → X} (hp : IsLocallyInjective p) {U : Set X}
    (hU : IsPreconnected U) {σ₁ σ₂ : X → M} (h₁ : ContinuousOn σ₁ U) (h₂ : ContinuousOn σ₂ U)
    (hσ₁ : ∀ y ∈ U, p (σ₁ y) = y) (hσ₂ : ∀ y ∈ U, p (σ₂ y) = y) {y₀ : X} (hy₀ : y₀ ∈ U)
    (h₀ : σ₁ y₀ = σ₂ y₀) : EqOn σ₁ σ₂ U :=
  (T2Space.isSeparatedMap p).eqOn_of_comp_eqOn hp hU h₁ h₂
    (fun y hy => by simp only [comp_apply, hσ₁ y hy, hσ₂ y hy]) hy₀ h₀

end Polyfold
