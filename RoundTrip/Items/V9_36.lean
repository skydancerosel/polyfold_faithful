import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_36

/-! Round trip for V9_36 (Definition 9.3.8, p. 427 of the 2021 book; 2017: Definition 9.9: the
boundary orientation of an oriented `M`).

The item lists the definition `MPolyfold.boundaryFrames O K e` (vocabulary: the frames `a` of
`K` with `(e, a) ∈ O`, Definition 9.3.8 with `T_y∂M` and the outward `e` as data) and six
theorems; `A` is the conjunction of their types, universes at `0`:
`exists_basis_orientation_iff_det_pos`, `exists_boundary_orientation`, `det_cons_smul_add`
(linear algebra), `MPolyfold.isOrientedAt_boundaryFrames` (for `K ⊆ T_yM` with `m`-dimensional
chart image and `e ∉ K`, the frames orient `K`), `MPolyfold.boundaryFrames_eq` (unchanged under
`e ↦ c e + k`, `c > 0`, `k ∈ K`, in a chart) and `exists_boundaryFrames_graph` (a witness with
two opposite orientations).

* `A → B` is not proved, and the failure is a genuine difference.  `B` asks, for an oriented
  `(m+1)`-dimensional `M` with tame induced structure and `d_M(y) = 1`: (a) outward vectors
  exist (chart vector outside the positive tangent cone of the chart image of `M`) and the
  frames of `T_y∂M` do not depend on the outward vector; (b) near `y`, `∂M` is an
  `m`-dimensional submanifold with an orientation (continuous frames) given by the rule.  `A`
  takes `K = T_y∂M` and `e` as data and assumes what `B` asserts: that `K` has `m`-dimensional
  chart image, `e ∉ K`, and that two outward vectors are related by `e' = c e + k`.  None of
  these is derived for `T_y∂M` and outward vectors of a tame `M`.  `∂M` being a submanifold near
  `y`, with a continuous boundary orientation, is also not formalized: the project lists
  "`T_y∂M = T^R_yM` and the outward direction from the cones `C_yM`" and "the continuity of
  `o_{∂M}`" as not formalized.
* `B_to_A` cannot use `B` (`B` is about submanifolds and says nothing about the linear algebra
  or about arbitrary data `K`, `e`); it re-proves `A` outright, as verbatim copies of the
  project's proofs (renamed `…_c`). -/

namespace RoundTrip.V9_36
open Polyfold Polyfold.MPolyfold Set Module Submodule Filter Topology
open scoped ContDiff

set_option maxSynthPendingDepth 3

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.exists_basis_orientation_iff_det_pos.{0}) ∧
  (type_of% @Polyfold.exists_boundary_orientation.{0}) ∧
  (type_of% @Polyfold.det_cons_smul_add.{0}) ∧
  (type_of% @Polyfold.MPolyfold.isOrientedAt_boundaryFrames.{0}) ∧
  (type_of% @Polyfold.MPolyfold.boundaryFrames_eq.{0}) ∧
  (type_of% @Polyfold.exists_boundaryFrames_graph)

theorem A_holds : A :=
  ⟨@Polyfold.exists_basis_orientation_iff_det_pos.{0}, @Polyfold.exists_boundary_orientation.{0},
    @Polyfold.det_cons_smul_add.{0}, @Polyfold.MPolyfold.isOrientedAt_boundaryFrames.{0},
    @Polyfold.MPolyfold.boundaryFrames_eq.{0}, @Polyfold.exists_boundaryFrames_graph⟩

/-! ### Copies of the project's proofs -/

section BoundaryLinear

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A family `w` of `k` vectors is a basis of the orientation of a basis `B₀` iff
`det_{B₀} w > 0`. -/
theorem exists_basis_orientation_iff_det_pos_c {V : Type*} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (B₀ : Basis (Fin k) ℝ V) (w : Fin k → V) :
    (∃ b : Basis (Fin k) ℝ V, ⇑b = w ∧ b.orientation = B₀.orientation) ↔ 0 < B₀.det w := by
  constructor
  · rintro ⟨b, rfl, hb⟩
    exact (B₀.orientation_eq_iff_det_pos b).1 hb.symm
  · intro hpos
    have : FiniteDimensional ℝ V := Module.Finite.of_basis B₀
    have hli : LinearIndependent ℝ w :=
      (B₀.is_basis_iff_det.2 (isUnit_iff_ne_zero.2 hpos.ne')).1
    have hcard : Fintype.card (Fin k) = finrank ℝ V := by rw [finrank_eq_card_basis B₀]
    have hb := coe_basisOfLinearIndependentOfCardEqFinrank' (K := ℝ) w hli hcard
    exact ⟨_, hb, ((B₀.orientation_eq_iff_det_pos _).2 (by rw [hb]; exact hpos)).symm⟩

/-- The same for families of a submodule `N`, given by their values in `E`. -/
theorem exists_basis_coe_iff_det_pos_c {N : Submodule ℝ E} {k : ℕ} (B₀ : Basis (Fin k) ℝ N)
    (u : Fin k → E) (w : Fin k → N) (hw : ∀ i, (w i : E) = u i) :
    (∃ b : Basis (Fin k) ℝ N, (∀ i, (b i : E) = u i) ∧ b.orientation = B₀.orientation) ↔
      0 < B₀.det w := by
  rw [← exists_basis_orientation_iff_det_pos_c]
  refine exists_congr fun b => and_congr ⟨fun h => funext fun i => Subtype.ext ((h i).trans
    (hw i).symm), fun h i => by rw [h, hw]⟩ Iff.rfl

/-- **The orientation convention of Definition 9.3.8, in linear algebra**: for an oriented
`(m+1)`-dimensional space `N_L` (positive basis `B₀`), a hyperplane `N_K ⊆ N_L` and
`v₀ ∈ N_L ∖ N_K`, there is an orientation `ω_K` of `N_K` whose positive bases `(a₁, …, a_m)` are
exactly those with `(v₀, a₁, …, a_m)` positive for `B₀`. -/
theorem exists_boundary_orientation_c {NL NK : Submodule ℝ E} (hle : NK ≤ NL) {m : ℕ}
    (B₀ : Basis (Fin (m + 1)) ℝ NL) (hK : finrank ℝ NK = m) {v₀ : E} (hv₀ : v₀ ∈ NL)
    (hv₀K : v₀ ∉ NK) :
    ∃ ωK : Orientation ℝ NK (Fin m), ∀ (u : Fin m → E) (a : Fin m → NK), (∀ i, (a i : E) = u i) →
      ((∃ b : Basis (Fin m) ℝ NK, (∀ i, (b i : E) = u i) ∧ b.orientation = ωK) ↔
        0 < B₀.det (Fin.cons (⟨v₀, hv₀⟩ : NL) fun i => Submodule.inclusion hle (a i))) := by
  have : FiniteDimensional ℝ NL := Module.Finite.of_basis B₀
  have : FiniteDimensional ℝ NK := Submodule.finiteDimensional_of_le hle
  let incl : NK →ₗ[ℝ] NL := Submodule.inclusion hle
  let g : NK [⋀^Fin m]→ₗ[ℝ] ℝ := (B₀.det.curryLeft ⟨v₀, hv₀⟩).compLinearMap incl
  have hg : ∀ a : Fin m → NK, g a = B₀.det (Fin.cons (⟨v₀, hv₀⟩ : NL) fun i => incl (a i)) :=
    fun a => rfl
  have hcard : Fintype.card (Fin (m + 1)) = finrank ℝ NL := by rw [finrank_eq_card_basis B₀]
  have hli : ∀ b : Basis (Fin m) ℝ NK,
      LinearIndependent ℝ (Fin.cons (⟨v₀, hv₀⟩ : NL) fun i => incl (b i)) := fun b => by
    refine linearIndependent_finCons.2 ⟨b.linearIndependent.map' incl
      (LinearMap.ker_eq_bot.2 (Submodule.inclusion_injective hle)), fun hmem => hv₀K ?_⟩
    have hspan : span ℝ (range fun i => incl (b i)) ≤ LinearMap.range incl :=
      span_le.2 (range_subset_iff.2 fun i => LinearMap.mem_range_self incl (b i))
    obtain ⟨c, hc⟩ := hspan hmem
    have : (c : E) = v₀ := congrArg Subtype.val hc
    exact this ▸ c.2
  have hne : ∀ b : Basis (Fin m) ℝ NK, g b ≠ 0 := fun b => by
    rw [hg, ← coe_basisOfLinearIndependentOfCardEqFinrank' (K := ℝ) _ (hli b) hcard]
    exact (B₀.isUnit_det _).ne_zero
  let b₀ : Basis (Fin m) ℝ NK := Module.finBasisOfFinrankEq ℝ NK hK
  have hrel : ∀ b : Basis (Fin m) ℝ NK, g b = g b₀ * b₀.det b := fun b => by
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det b₀ g]
    rfl
  have hA : ∀ b : Basis (Fin m) ℝ NK,
      b.orientation = (if 0 < g b₀ then b₀.orientation else -b₀.orientation) ↔ 0 < g b :=
    fun b => by
    have hdet : b₀.det b ≠ 0 := (b₀.isUnit_det b).ne_zero
    rw [hrel b]
    split_ifs with h
    · rw [eq_comm, b₀.orientation_eq_iff_det_pos, mul_pos_iff_of_pos_left h]
    · have h' : g b₀ < 0 := lt_of_le_of_ne (not_lt.1 h) (hne b₀)
      rw [← b₀.orientation_ne_iff_eq_neg, Ne, eq_comm, b₀.orientation_eq_iff_det_pos]
      constructor
      · intro hn
        exact mul_pos_of_neg_of_neg h' (lt_of_le_of_ne (not_lt.1 hn) hdet)
      · intro hp hpos
        have := mul_neg_of_neg_of_pos h' hpos
        linarith
  refine ⟨if 0 < g b₀ then b₀.orientation else -b₀.orientation, fun u a ha => ?_⟩
  rw [← hg]
  constructor
  · rintro ⟨b, hb, hbo⟩
    have : ⇑b = a := funext fun i => Subtype.ext ((hb i).trans (ha i).symm)
    rw [← this]; exact (hA b).1 hbo
  · intro hpos
    have hliw := (B₀.is_basis_iff_det.2 (isUnit_iff_ne_zero.2 (hg a ▸ hpos).ne')).1
    have hlia : LinearIndependent ℝ a := (linearIndependent_finCons.1 hliw).1.of_comp incl
    have hcardK : Fintype.card (Fin m) = finrank ℝ NK := by rw [Fintype.card_fin, hK]
    have hb := coe_basisOfLinearIndependentOfCardEqFinrank' (K := ℝ) a hlia hcardK
    exact ⟨_, fun i => by rw [hb, ha], (hA _).2 (by rw [hb]; exact hpos)⟩

/-- `det(c v + k, a) = c det(v, a)` for `k` in the span of the hyperplane `N_K ∋ aᵢ`. -/
theorem det_cons_smul_add_c {NL NK : Submodule ℝ E} (hle : NK ≤ NL) {m : ℕ}
    (B₀ : Basis (Fin (m + 1)) ℝ NL) (hK : finrank ℝ NK = m) (v : NL) (c : ℝ) (k : NK)
    (a : Fin m → NK) :
    B₀.det (Fin.cons (c • v + Submodule.inclusion hle k) fun i => Submodule.inclusion hle (a i)) =
      c * B₀.det (Fin.cons v fun i => Submodule.inclusion hle (a i)) := by
  have : FiniteDimensional ℝ NL := Module.Finite.of_basis B₀
  have : FiniteDimensional ℝ NK := Submodule.finiteDimensional_of_le hle
  have h0 : B₀.det (Fin.cons (Submodule.inclusion hle k) fun i => Submodule.inclusion hle (a i)) =
      0 := by
    refine AlternatingMap.map_linearDependent _ _ fun hli => ?_
    have hli' : LinearIndependent ℝ (Fin.cons k a : Fin (m + 1) → NK) := by
      refine LinearIndependent.of_comp (Submodule.inclusion hle) ?_
      rw [Fin.comp_cons]
      exact hli
    have := hli'.fintype_card_le_finrank
    rw [Fintype.card_fin, hK] at this
    omega
  have h := congrArg (fun f => f fun i => Submodule.inclusion hle (a i))
    (map_add (B₀.det.curryLeft) (c • v) (Submodule.inclusion hle k))
  simp only [map_smul, AlternatingMap.add_apply, AlternatingMap.smul_apply,
    AlternatingMap.curryLeft_apply_apply, smul_eq_mul] at h
  exact h.trans (by rw [show Matrix.vecCons (Submodule.inclusion hle k)
    (fun i => Submodule.inclusion hle (a i)) = Fin.cons (Submodule.inclusion hle k)
      (fun i => Submodule.inclusion hle (a i)) from rfl, h0, add_zero]; rfl)

end BoundaryLinear

section MP

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {φ : MChart X}

/-- The positive frames of `T_yM` with first vector `e` and the others in `K`, by a
determinant in a chart. -/
theorem cons_mem_chartFrames_iff_c (hφ : P.IsChart φ) {m : ℕ} {L K : Set P.TangentSpace}
    (hKL : K ⊆ L) {NL NK : Submodule ℝ (φ.model.E 0)} (hle : NK ≤ NL)
    (hNK : (NK : Set (φ.model.E 0)) = chartVec hφ '' K) (B₀ : Basis (Fin (m + 1)) ℝ NL)
    {e : P.TangentSpace} (he : e ∈ L) (hv₀ : chartVec hφ e ∈ NL) {a : Fin m → P.TangentSpace}
    (ha : ∀ i, a i ∈ K) :
    Fin.cons e a ∈ chartFrames hφ L NL B₀.orientation ↔
      0 < B₀.det (Fin.cons (⟨chartVec hφ e, hv₀⟩ : NL) fun i => Submodule.inclusion hle
        (⟨chartVec hφ (a i), by rw [← SetLike.mem_coe, hNK]; exact ⟨a i, ha i, rfl⟩⟩ : NK)) := by
  rw [← exists_basis_coe_iff_det_pos_c B₀ (chartVec hφ ∘ Fin.cons e a)]
  · constructor
    · rintro ⟨-, h⟩; exact h
    · intro h
      refine ⟨Fin.forall_fin_succ.2 ⟨by simpa using he, fun j => by simpa using hKL (ha j)⟩, h⟩
  · refine Fin.forall_fin_succ.2 ⟨by simp, fun j => by simp⟩

/-- **Definition 9.3.8 defines an orientation of `T_y∂M`**: if `K ⊆ T_yM` has as chart image an
`m`-dimensional subspace and `e ∈ T_yM` is not in it, `boundaryFrames O K e` orients `K`. -/
theorem isOrientedAt_boundaryFrames_c {y : X} {m : ℕ} {L K : Set P.TangentSpace}
    {O : Set (Fin (m + 1) → P.TangentSpace)} (hO : P.IsOrientedAt y ⟨m + 1, L, O⟩) (hKL : K ⊆ L)
    (hφ : P.IsChart φ) (hyφ : y ∈ φ.source) (NK : Submodule ℝ (φ.model.E 0))
    (hNK : (NK : Set (φ.model.E 0)) = chartVec hφ '' K) (hrank : finrank ℝ NK = m)
    {e : P.TangentSpace} (he : e ∈ L) (heK : chartVec hφ e ∉ NK) :
    P.IsOrientedAt y ⟨m, K, boundaryFrames O K e⟩ := by
  obtain ⟨NL, hNL, hfin, hrankL, ωL, hOeq⟩ := hO.isChartOrientation hφ hyφ
  have hle : NK ≤ NL := fun v hv => by
    rw [← SetLike.mem_coe, hNK] at hv
    obtain ⟨α, hα, rfl⟩ := hv
    rw [← SetLike.mem_coe, hNL]
    exact ⟨α, hKL hα, rfl⟩
  have hv₀ : chartVec hφ e ∈ NL := by rw [← SetLike.mem_coe, hNL]; exact ⟨e, he, rfl⟩
  let B₀ : Basis (Fin (m + 1)) ℝ NL :=
    (Module.finBasisOfFinrankEq ℝ NL hrankL).adjustToOrientation ωL
  have hB₀ : B₀.orientation = ωL := Basis.orientation_adjustToOrientation _ _
  obtain ⟨ωK, hωK⟩ := exists_boundary_orientation_c hle B₀ hrank hv₀ heK
  refine ⟨fun α hα => hO.1 α (hKL hα), φ, hφ, hyφ, NK, hNK,
    Submodule.finiteDimensional_of_le hle, hrank, ωK, ?_⟩
  ext a
  constructor
  · rintro ⟨ha, hcons⟩
    change Fin.cons e a ∈ O at hcons
    rw [show O = chartFrames hφ L NL ωL from hOeq, ← hB₀,
      cons_mem_chartFrames_iff_c hφ hKL hle hNK B₀ he hv₀ ha] at hcons
    exact ⟨ha, (hωK _ _ fun i => rfl).2 hcons⟩
  · rintro ⟨ha, hb⟩
    refine ⟨ha, ?_⟩
    rw [show O = chartFrames hφ L NL ωL from hOeq, ← hB₀,
      cons_mem_chartFrames_iff_c hφ hKL hle hNK B₀ he hv₀ ha]
    exact (hωK _ _ fun i => rfl).1 hb

/-- **Definition 9.3.8 does not depend on the choice of `e`** within `e + K`, up to positive
multiples: `chartVec e' = c · chartVec e + k` with `c > 0` and `k` in the chart image of `K` give
the same boundary frames (two outward vectors are related this way). -/
theorem boundaryFrames_eq_c {y : X} {m : ℕ} {L K : Set P.TangentSpace}
    {O : Set (Fin (m + 1) → P.TangentSpace)} (hO : P.IsOrientedAt y ⟨m + 1, L, O⟩) (hKL : K ⊆ L)
    (hφ : P.IsChart φ) (hyφ : y ∈ φ.source) (NK : Submodule ℝ (φ.model.E 0))
    (hNK : (NK : Set (φ.model.E 0)) = chartVec hφ '' K) (hrank : finrank ℝ NK = m)
    {e e' : P.TangentSpace} (he : e ∈ L) (he' : e' ∈ L) {c : ℝ} (hc : 0 < c)
    (hk : chartVec hφ e' - c • chartVec hφ e ∈ NK) :
    boundaryFrames O K e' = boundaryFrames O K e := by
  obtain ⟨NL, hNL, hfin, hrankL, ωL, hOeq⟩ := hO.isChartOrientation hφ hyφ
  have hle : NK ≤ NL := fun v hv => by
    rw [← SetLike.mem_coe, hNK] at hv
    obtain ⟨α, hα, rfl⟩ := hv
    rw [← SetLike.mem_coe, hNL]
    exact ⟨α, hKL hα, rfl⟩
  have hv₀ : chartVec hφ e ∈ NL := by rw [← SetLike.mem_coe, hNL]; exact ⟨e, he, rfl⟩
  have hv₀' : chartVec hφ e' ∈ NL := by rw [← SetLike.mem_coe, hNL]; exact ⟨e', he', rfl⟩
  let B₀ : Basis (Fin (m + 1)) ℝ NL :=
    (Module.finBasisOfFinrankEq ℝ NL hrankL).adjustToOrientation ωL
  have hB₀ : B₀.orientation = ωL := Basis.orientation_adjustToOrientation _ _
  have hsplit : (⟨chartVec hφ e', hv₀'⟩ : NL) =
      c • (⟨chartVec hφ e, hv₀⟩ : NL) + Submodule.inclusion hle ⟨_, hk⟩ :=
    Subtype.ext (by simp)
  ext a
  change ((∀ i, a i ∈ K) ∧ Fin.cons e' a ∈ O) ↔ ((∀ i, a i ∈ K) ∧ Fin.cons e a ∈ O)
  refine and_congr_right fun ha => ?_
  rw [show O = chartFrames hφ L NL ωL from hOeq, ← hB₀,
    cons_mem_chartFrames_iff_c hφ hKL hle hNK B₀ he' hv₀' ha,
    cons_mem_chartFrames_iff_c hφ hKL hle hNK B₀ he hv₀ ha, hsplit,
    det_cons_smul_add_c hle B₀ hrank, mul_pos_iff_of_pos_left hc]

end MP

section BoundaryWitness

open MPolyfold

/-- **Satisfiability of Definition 9.3.8**: on an oriented graph `G ⊆ ℝ²` at `z ∈ G`, with
`K = T_z∂` the zero vectors of `T_zG` and `e`, `e'` of chart vectors `±(1, β'(z₀))`, the boundary
frames orient `K`, and the two orientations differ (the two ends of an oriented arc get opposite
signs). -/
theorem exists_boundaryFrames_graph_c {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {z : Fin 2 → ℝ}
    (hz : z ∈ graph2 β) :
    ∃ (K : Set (rnPolyfold 2).TangentSpace) (e e' : (rnPolyfold 2).TangentSpace),
      (rnPolyfold 2).IsOrientedAt z ⟨0, K, boundaryFrames (graphFrames β 1 z) K e⟩ ∧
      (rnPolyfold 2).IsOrientedAt z ⟨0, K, boundaryFrames (graphFrames β 1 z) K e'⟩ ∧
      boundaryFrames (graphFrames β 1 z) K e ≠ boundaryFrames (graphFrames β 1 z) K e' := by
  set L := (rnPolyfold 2).submanifoldTangent (graph2 β) z
  have himg := chartVec_image_graph2 hβ hz
  have hex : ∀ v ∈ span ℝ {graphDir β z}, ∃ α ∈ L, chartVec idChart2 α = v := fun v hv => by
    have : v ∈ chartVec idChart2 '' L := by rw [himg]; exact hv
    obtain ⟨α, hα, h⟩ := this
    exact ⟨α, hα, h⟩
  obtain ⟨e, he, hce⟩ := hex _ (subset_span (mem_singleton _))
  obtain ⟨e', he', hce'⟩ := hex _ (neg_mem (subset_span (mem_singleton _)))
  obtain ⟨o, ho, hco⟩ := hex 0 (zero_mem _)
  let K := {α ∈ L | chartVec idChart2 α = 0}
  have hKL : K ⊆ L := fun α hα => hα.1
  have hNK : ((⊥ : Submodule ℝ ((rnChart 2 0).model.E 0)) : Set ((rnChart 2 0).model.E 0)) =
      chartVec idChart2 '' K := by
    ext v
    rw [Submodule.bot_coe, mem_singleton_iff]
    constructor
    · rintro rfl; exact ⟨o, ⟨ho, hco⟩, hco⟩
    · rintro ⟨α, hα, rfl⟩; exact hα.2
  have hO := isOrientedAt_graphFrames hβ one_ne_zero hz
  have hrank : finrank ℝ (⊥ : Submodule ℝ ((rnChart 2 0).model.E 0)) = 0 := finrank_bot ℝ _
  refine ⟨K, e, e', isOrientedAt_boundaryFrames_c hO hKL idChart2 (mem_univ z) ⊥ hNK hrank he ?_,
    isOrientedAt_boundaryFrames_c hO hKL idChart2 (mem_univ z) ⊥ hNK hrank he' ?_, ?_⟩
  · rw [hce, Submodule.mem_bot]; exact graphDir_ne_zero β z
  · rw [hce', Submodule.mem_bot, neg_eq_zero]; exact graphDir_ne_zero β z
  · intro h
    have h1 : (Fin.elim0 : Fin 0 → (rnPolyfold 2).TangentSpace) ∈
        boundaryFrames (graphFrames β 1 z) K e := by
      refine ⟨fun i => i.elim0, ?_, 1, one_pos, ?_⟩
      · change (Fin.cons e (Fin.elim0 : Fin 0 → (rnPolyfold 2).TangentSpace) :
          Fin 1 → (rnPolyfold 2).TangentSpace) 0 ∈ L
        simpa using he
      · change chartVec idChart2 ((Fin.cons e (Fin.elim0 : Fin 0 → (rnPolyfold 2).TangentSpace) :
          Fin 1 → (rnPolyfold 2).TangentSpace) 0) =
          (1 * 1) • graphDir β z
        simp [hce]
    rw [h] at h1
    obtain ⟨-, -, c, hc, hc'⟩ := h1
    have h3 : chartVec idChart2 ((Fin.cons e' (Fin.elim0 : Fin 0 → (rnPolyfold 2).TangentSpace) :
          Fin 1 → (rnPolyfold 2).TangentSpace) 0) =
        -graphDir β z := by simpa using hce'
    rw [h3, mul_one] at hc'
    have h2 : (c + 1) • graphDir β z = 0 := by rw [add_smul, one_smul, ← hc', neg_add_cancel]
    rcases smul_eq_zero.1 h2 with h4 | h4
    · linarith
    · exact graphDir_ne_zero β z h4


end BoundaryWitness

/-- `B → A`, by re-proving `A` outright. -/
theorem B_to_A : B → A := fun _ =>
  ⟨@exists_basis_orientation_iff_det_pos_c, @exists_boundary_orientation_c, @det_cons_smul_add_c,
    @isOrientedAt_boundaryFrames_c, @boundaryFrames_eq_c, @exists_boundaryFrames_graph_c⟩

#rt_check RoundTrip.V9_36.B_to_A [Polyfold.exists_basis_orientation_iff_det_pos,
  Polyfold.exists_boundary_orientation, Polyfold.det_cons_smul_add,
  Polyfold.MPolyfold.isOrientedAt_boundaryFrames, Polyfold.MPolyfold.boundaryFrames_eq,
  Polyfold.exists_boundaryFrames_graph]
#rt_overlap RoundTrip.V9_36.B_to_A [Polyfold.exists_basis_orientation_iff_det_pos,
  Polyfold.exists_boundary_orientation, Polyfold.det_cons_smul_add,
  Polyfold.MPolyfold.isOrientedAt_boundaryFrames, Polyfold.MPolyfold.boundaryFrames_eq,
  Polyfold.exists_boundaryFrames_graph]

end RoundTrip.V9_36
