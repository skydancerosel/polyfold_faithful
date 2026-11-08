import Polyfold.Chapter9.OrientationUniqueness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.3 "Orientations": **Definition 9.3.8** (2021 p. 427; 2017: Definition
9.9), (9.11) (2021 p. 427, new in the 2021 edition), **Proposition 9.3.9** (2021 p. 428, new in
the 2021 edition), **Definition 9.3.10** (2021 p. 428; 2017: Definition 9.11, with (9.12) there
numbered (9.11)) and **Remark 9.3.11** (2021 p. 429; 2017: Remark 9.9).  Numbers and pages are the
2021 text's, the 2017 ones in parentheses.

# Boundary orientations

## The text, paraphrased

(Before (9.11)) For an oriented `Θ` and `y ∈ U(x) ∩ ∂X`, split `T̂_Θ(y) = ∑ σᵢ T_y(Mᵢ, oᵢ)` by
`ℓ = d_{Mᵢ}(y)`; for `ℓ ≠ ℓ'` the tangent spaces never coincide (Lemma 9.3.7), so for two
oriented branching structures the degree-`ℓ` parts agree (9.11).  (Definition 9.3.8) For an
oriented `n`-dimensional `(M, o)` and `y ∈ ∂M` with `d_M(y) = 1`, a basis `(a₁, …, a_{n-1})` of
`T_y∂M` is positive iff `(e, a₁, …, a_{n-1})` is positive for `o_y`, `e` outward pointing.
(9.12), (Definition 9.3.10) For an oriented tame `Θ`, `T̂_{∂Θ}(y) = 0` off `supp(Θ)` and
`T̂_{∂Θ}(y) = ∑_{y ∈ ∂Mᵢ, d_{Mᵢ}(y) = 1} σᵢ T_y(∂Mᵢ, o_{∂Mᵢ})` on `U(x)`.  (Proposition 9.3.9)
This does not depend on the local branching structures.  (Remark 9.3.11) The non-tame case is
open.

## What is formalized

* Linear algebra: `exists_basis_orientation_iff_det_pos`, `exists_boundary_orientation` (the
  convention defines an orientation of a hyperplane), `det_cons_smul_add`.
* **Definition 9.3.8**: `MPolyfold.boundaryFrames O K e`; it orients `K`
  (`isOrientedAt_boundaryFrames`, for `K ⊆ T_yM` with `m`-dimensional chart image and `e ∉ K`)
  and depends on `e` only up to `e ↦ c e + k`, `c > 0`, `k ∈ K` (`boundaryFrames_eq`);
  satisfiability with two opposite orientations: `exists_boundaryFrames_graph`.
* Lemma 9.3.7 without charts: `subDegIndex_eq_of_submanifoldTangent_eq`; the degree of an
  oriented tangent space `HasSubDegree` and `hasSubDegree_tangent_iff`.
* **(9.11)**: `EpGroupoid.degreePart`, `degreePart_orientedSum`, `eq_9_11`.
* **Definition 9.3.10**: `boundaryLift bd T` (9.12); **Proposition 9.3.9**: `proposition_9_3_9`.

## What the text leaves implicit, and the choices made

* `T_y∂M` and the outward vector `e` enter Definition 9.3.8 as data `K`, `e` (with `K` of
  codimension `1` and `e ∉ K`); two outward vectors differ by `c e + k`, `c > 0`, under which the
  frames are unchanged.
* (9.12) is written with the boundary operation `bd : T_y(M, o) ↦ T_y(∂M, o_{∂M})` as a function
  of the oriented tangent space, which is what Proposition 9.3.9's appeal to "the discussion
  preceding it" provides.  The condition `y ∈ ∂Mᵢ` is implied by `d_{Mᵢ}(y) = 1`.

## Not formalized, and why

* That `T_y∂M = T_y^R M` and the outward half-space are determined by `T_yM` for tame `M` with
  `d_M(y) = 1` (via the cones `C_yM` of the proof of Lemma 9.3.7), i.e. that Definition 9.3.8
  gives such a function `bd`: the partial cones of submanifolds are not formalized.
* The continuity of `o_{∂M}` along `∂M` and its extension to the closed faces (Figure 9.1).
* Remark 9.3.11: no formal content.
-/

set_option maxSynthPendingDepth 3

open Set Module Submodule Filter Topology CategoryTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

/-! ### Definition 9.3.8: linear algebra -/

section BoundaryLinear

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A family `w` of `k` vectors is a basis of the orientation of a basis `B₀` iff
`det_{B₀} w > 0`. -/
theorem exists_basis_orientation_iff_det_pos {V : Type*} [AddCommGroup V] [Module ℝ V] {k : ℕ}
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
theorem exists_basis_coe_iff_det_pos {N : Submodule ℝ E} {k : ℕ} (B₀ : Basis (Fin k) ℝ N)
    (u : Fin k → E) (w : Fin k → N) (hw : ∀ i, (w i : E) = u i) :
    (∃ b : Basis (Fin k) ℝ N, (∀ i, (b i : E) = u i) ∧ b.orientation = B₀.orientation) ↔
      0 < B₀.det w := by
  rw [← exists_basis_orientation_iff_det_pos]
  refine exists_congr fun b => and_congr ⟨fun h => funext fun i => Subtype.ext ((h i).trans
    (hw i).symm), fun h i => by rw [h, hw]⟩ Iff.rfl

/-- **The orientation convention of Definition 9.3.8, in linear algebra**: for an oriented
`(m+1)`-dimensional space `N_L` (positive basis `B₀`), a hyperplane `N_K ⊆ N_L` and
`v₀ ∈ N_L ∖ N_K`, there is an orientation `ω_K` of `N_K` whose positive bases `(a₁, …, a_m)` are
exactly those with `(v₀, a₁, …, a_m)` positive for `B₀`. -/
theorem exists_boundary_orientation {NL NK : Submodule ℝ E} (hle : NK ≤ NL) {m : ℕ}
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
theorem det_cons_smul_add {NL NK : Submodule ℝ E} (hle : NK ≤ NL) {m : ℕ}
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

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {φ : MChart X}

/-! ### Definition 9.3.8: boundary frames -/

/-- **Definition 9.3.8, 2021 p. 427 (2017: Definition 9.9) (the boundary orientation
convention)**: for an oriented `(m+1)`-dimensional
`T_yM` (positive frames `O`), the subset `K = T_y∂M` and a vector `e ∈ T_yM`, the frames
`(a₁, …, a_m)` of `K` such that `(e, a₁, …, a_m)` is positive. -/
def boundaryFrames {m : ℕ} (O : Set (Fin (m + 1) → P.TangentSpace)) (K : Set P.TangentSpace)
    (e : P.TangentSpace) : Set (Fin m → P.TangentSpace) :=
  {a | (∀ i, a i ∈ K) ∧ Fin.cons e a ∈ O}

/-- The positive frames of `T_yM` with first vector `e` and the others in `K`, by a
determinant in a chart. -/
theorem cons_mem_chartFrames_iff (hφ : P.IsChart φ) {m : ℕ} {L K : Set P.TangentSpace}
    (hKL : K ⊆ L) {NL NK : Submodule ℝ (φ.model.E 0)} (hle : NK ≤ NL)
    (hNK : (NK : Set (φ.model.E 0)) = chartVec hφ '' K) (B₀ : Basis (Fin (m + 1)) ℝ NL)
    {e : P.TangentSpace} (he : e ∈ L) (hv₀ : chartVec hφ e ∈ NL) {a : Fin m → P.TangentSpace}
    (ha : ∀ i, a i ∈ K) :
    Fin.cons e a ∈ chartFrames hφ L NL B₀.orientation ↔
      0 < B₀.det (Fin.cons (⟨chartVec hφ e, hv₀⟩ : NL) fun i => Submodule.inclusion hle
        (⟨chartVec hφ (a i), by rw [← SetLike.mem_coe, hNK]; exact ⟨a i, ha i, rfl⟩⟩ : NK)) := by
  rw [← exists_basis_coe_iff_det_pos B₀ (chartVec hφ ∘ Fin.cons e a)]
  · constructor
    · rintro ⟨-, h⟩; exact h
    · intro h
      refine ⟨Fin.forall_fin_succ.2 ⟨by simpa using he, fun j => by simpa using hKL (ha j)⟩, h⟩
  · refine Fin.forall_fin_succ.2 ⟨by simp, fun j => by simp⟩

/-- **Definition 9.3.8 defines an orientation of `T_y∂M`**: if `K ⊆ T_yM` has as chart image an
`m`-dimensional subspace and `e ∈ T_yM` is not in it, `boundaryFrames O K e` orients `K`. -/
theorem isOrientedAt_boundaryFrames {y : X} {m : ℕ} {L K : Set P.TangentSpace}
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
  obtain ⟨ωK, hωK⟩ := exists_boundary_orientation hle B₀ hrank hv₀ heK
  refine ⟨fun α hα => hO.1 α (hKL hα), φ, hφ, hyφ, NK, hNK,
    Submodule.finiteDimensional_of_le hle, hrank, ωK, ?_⟩
  ext a
  constructor
  · rintro ⟨ha, hcons⟩
    change Fin.cons e a ∈ O at hcons
    rw [show O = chartFrames hφ L NL ωL from hOeq, ← hB₀,
      cons_mem_chartFrames_iff hφ hKL hle hNK B₀ he hv₀ ha] at hcons
    exact ⟨ha, (hωK _ _ fun i => rfl).2 hcons⟩
  · rintro ⟨ha, hb⟩
    refine ⟨ha, ?_⟩
    rw [show O = chartFrames hφ L NL ωL from hOeq, ← hB₀,
      cons_mem_chartFrames_iff hφ hKL hle hNK B₀ he hv₀ ha]
    exact (hωK _ _ fun i => rfl).1 hb

/-- **Definition 9.3.8 does not depend on the choice of `e`** within `e + K`, up to positive
multiples: `chartVec e' = c · chartVec e + k` with `c > 0` and `k` in the chart image of `K` give
the same boundary frames (two outward vectors are related this way). -/
theorem boundaryFrames_eq {y : X} {m : ℕ} {L K : Set P.TangentSpace}
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
    cons_mem_chartFrames_iff hφ hKL hle hNK B₀ he' hv₀' ha,
    cons_mem_chartFrames_iff hφ hKL hle hNK B₀ he hv₀ ha, hsplit,
    det_cons_smul_add hle B₀ hrank, mul_pos_iff_of_pos_left hc]

/-! ### Lemma 9.3.7 intrinsically, and the degree of an oriented tangent space -/

/-- **Lemma 9.3.7 without charts**: for smooth submanifolds with tame induced structures through
`y`, `T_yM₁ = T_yM₂` implies `d_{M₁}(y) = d_{M₂}(y)` (`subDegIndex_eq_of_tangentSpace_eq` in a
chart of the atlas at `y`). -/
theorem subDegIndex_eq_of_submanifoldTangent_eq {A₁ A₂ : Set X} (hA₁ : P.IsSmoothSubmanifold A₁)
    (hA₂ : P.IsSmoothSubmanifold A₂) (ht₁ : P.HasTameInducedStructure A₁)
    (ht₂ : P.HasTameInducedStructure A₂) {y : X} (hy₁ : y ∈ A₁) (hy₂ : y ∈ A₂)
    (h : P.submanifoldTangent A₁ y = P.submanifoldTangent A₂ y) :
    P.subDegIndex hA₁.isSubMPolyfold ⟨y, hy₁⟩ = P.subDegIndex hA₂.isSubMPolyfold ⟨y, hy₂⟩ := by
  obtain ⟨φ, hφm, hyφ⟩ := P.atlas.cover y
  have hφ := P.isChart_of_mem hφm
  have hyV₁ := hA₁.mem_data_V hy₁
  have hyV₂ := hA₂.mem_data_V hy₂
  have hy1 : y ∈ P.levelSet 1 := (hA₁.data hy₁).mem_levelSet_one hy₁ hyV₁
  have hz := P.toBase_levelLift hφ hyφ hy1
  refine subDegIndex_eq_of_tangentSpace_eq hA₁ hA₂ ht₁ ht₂ hy₁ hy₂ (hA₁.data hy₁) (hA₂.data hy₂)
    hφ hyV₁ hyV₂ hyφ hz ?_
  rw [← chartVec_image_submanifoldTangent hφ (hA₁.data hy₁) hy₁ hyV₁ hyφ,
    ← chartVec_image_submanifoldTangent hφ (hA₂.data hy₂) hy₂ hyV₂ hyφ, h]

variable (P) in
/-- **An oriented tangent space of degree `ℓ` at `y`**: its underlying space is `T_yM` for a smooth
submanifold `M ∋ y` with tame induced structure and `d_M(y) = ℓ`.  By Lemma 9.3.7 this does not
depend on `M` (`hasSubDegree_tangent_iff`). -/
def HasSubDegree (y : X) (ℓ : ℕ) (g : OrTangent P) : Prop :=
  ∃ (A : Set X) (hA : P.IsSmoothSubmanifold A) (hy : y ∈ A), P.HasTameInducedStructure A ∧
    P.submanifoldTangent A y = g.carrier ∧ P.subDegIndex hA.isSubMPolyfold ⟨y, hy⟩ = ℓ

theorem SubmanifoldOrientation.hasSubDegree_tangent_iff {A : Set X} {n : ℕ}
    (o : P.SubmanifoldOrientation A n) (hA : P.IsSmoothSubmanifold A)
    (ht : P.HasTameInducedStructure A) {y : X} (hy : y ∈ A) {ℓ : ℕ} :
    P.HasSubDegree y ℓ (o.tangent y) ↔ P.subDegIndex hA.isSubMPolyfold ⟨y, hy⟩ = ℓ := by
  constructor
  · rintro ⟨A', hA', hy', ht', hT, hd⟩
    rw [← hd]
    exact subDegIndex_eq_of_submanifoldTangent_eq hA hA' ht ht' hy hy' hT.symm
  · intro h
    exact ⟨A, hA, hy, ht, rfl, h⟩

end MPolyfold

/-! ### Satisfiability of Definition 9.3.8: the two ends of an oriented arc -/

section BoundaryWitness

open MPolyfold

/-- **Satisfiability of Definition 9.3.8**: on an oriented graph `G ⊆ ℝ²` at `z ∈ G`, with
`K = T_z∂` the zero vectors of `T_zG` and `e`, `e'` of chart vectors `±(1, β'(z₀))`, the boundary
frames orient `K`, and the two orientations differ (the two ends of an oriented arc get opposite
signs). -/
theorem exists_boundaryFrames_graph {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {z : Fin 2 → ℝ}
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
  refine ⟨K, e, e', isOrientedAt_boundaryFrames hO hKL idChart2 (mem_univ z) ⊥ hNK hrank he ?_,
    isOrientedAt_boundaryFrames hO hKL idChart2 (mem_univ z) ⊥ hNK hrank he' ?_, ?_⟩
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

/-! ### (9.11), Proposition 9.3.9 and Definition 9.3.10 -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
variable {Θ : Obj → ℚ}

variable (X) in
open scoped Classical in
/-- **The degree-`ℓ` part** of an element of `Gr̂(X)` at `y`: the terms whose oriented tangent space
has degree `ℓ` (`HasSubDegree`). -/
def degreePart (y : Obj) (ℓ : ℕ) (w : X.PObj.OrTangent →₀ ℚ) : X.PObj.OrTangent →₀ ℚ :=
  w.filter (X.PObj.HasSubDegree y ℓ)

open scoped Classical in
/-- For an oriented branching structure with tame `Mᵢ`, the degree-`ℓ` part of
`∑ σᵢ T_y(Mᵢ, oᵢ)` is `∑_{d_{Mᵢ}(y) = ℓ} σᵢ T_y(Mᵢ, oᵢ)`. -/
theorem degreePart_orientedSum {x : Obj} (B : X.OrientedBranchingStructure Θ x)
    (ht : ∀ i, X.PObj.HasTameInducedStructure (B.M i)) (y : Obj) (ℓ : ℕ) :
    X.degreePart y ℓ (B.orientedSum y) =
      ∑ i with ∃ hy : y ∈ B.M i,
          X.PObj.subDegIndex (B.isSmoothSubmanifold i).isSubMPolyfold ⟨y, hy⟩ = ℓ,
        Finsupp.single ((B.orient i).tangent y) (B.σ i) := by
  rw [degreePart, OrientedBranchingStructure.orientedSum, Finsupp.filter_sum, Finset.sum_filter,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hiff := fun hy : y ∈ B.M i =>
    (B.orient i).hasSubDegree_tangent_iff (B.isSmoothSubmanifold i) (ht i) hy (ℓ := ℓ)
  by_cases hy : y ∈ B.M i
  · rw [if_pos hy]
    by_cases hd : X.PObj.subDegIndex (B.isSmoothSubmanifold i).isSubMPolyfold ⟨y, hy⟩ = ℓ
    · rw [if_pos ⟨hy, hd⟩, Finsupp.filter_single_of_pos _ ((hiff hy).2 hd)]
    · rw [if_neg (show ¬∃ hy' : y ∈ B.M i,
          X.PObj.subDegIndex (B.isSmoothSubmanifold i).isSubMPolyfold ⟨y, hy'⟩ = ℓ
          from fun ⟨_, hd'⟩ => hd hd'),
        Finsupp.filter_single_of_neg _ fun h => hd ((hiff hy).1 h)]
  · rw [if_neg hy, if_neg (show ¬∃ hy' : y ∈ B.M i,
        X.PObj.subDegIndex (B.isSmoothSubmanifold i).isSubMPolyfold ⟨y, hy'⟩ = ℓ
        from fun ⟨hy', _⟩ => hy hy')]

open scoped Classical in
/-- **(9.11), 2021 p. 427 (new in the 2021 edition)**: for two oriented branching structures with
tame `Mᵢ` (Definition 9.3.6) giving the same `T̂_Θ(y)`, the parts with `d_{Mᵢ}(y) = ℓ` agree, for
every `ℓ`. -/
theorem eq_9_11 {x x' : Obj} (B : X.OrientedBranchingStructure Θ x)
    (B' : X.OrientedBranchingStructure Θ x') (ht : ∀ i, X.PObj.HasTameInducedStructure (B.M i))
    (ht' : ∀ i, X.PObj.HasTameInducedStructure (B'.M i)) {y : Obj}
    (h : B.orientedSum y = B'.orientedSum y) (ℓ : ℕ) :
    (∑ i with ∃ hy : y ∈ B.M i,
        X.PObj.subDegIndex (B.isSmoothSubmanifold i).isSubMPolyfold ⟨y, hy⟩ = ℓ,
      Finsupp.single ((B.orient i).tangent y) (B.σ i)) =
    ∑ i with ∃ hy : y ∈ B'.M i,
        X.PObj.subDegIndex (B'.isSmoothSubmanifold i).isSubMPolyfold ⟨y, hy⟩ = ℓ,
      Finsupp.single ((B'.orient i).tangent y) (B'.σ i) := by
  rw [← degreePart_orientedSum B ht, ← degreePart_orientedSum B' ht', h]

variable (X) in
/-- **Definition 9.3.10, 2021 p. 428 (2017: Definition 9.11) (boundary orientation), formula
(9.12)**: for an orientation `T̂_Θ` and the
boundary operation `bd : T_y(M, o) ↦ T_y(∂M, o_{∂M})` of Definition 9.3.8, `T̂_{∂Θ}(y)` is the image
under `bd` of the degree-`1` part of `T̂_Θ(y)`. -/
def boundaryLift (bd : X.PObj.OrTangent → X.PObj.OrTangent) (T : Obj → X.PObj.OrTangent →₀ ℚ)
    (y : Obj) : X.PObj.OrTangent →₀ ℚ :=
  (X.degreePart y 1 (T y)).mapDomain bd

open scoped Classical in
/-- **Proposition 9.3.9, 2021 p. 428 (new in the 2021 edition)**: `T̂_{∂Θ}` vanishes on
`X_∞ ∖ supp(Θ)`, and on `U(x)` it is given by (9.12),
`∑_{d_{Mᵢ}(y) = 1} σᵢ · T_y(∂Mᵢ, o_{∂Mᵢ})`, for every oriented branching structure with tame `Mᵢ`
representing `T̂_Θ` there: the definition does not depend on the structure.
(`d_{Mᵢ}(y) = 1` implies `y ∈ ∂Mᵢ`.) -/
theorem proposition_9_3_9 (bd : X.PObj.OrTangent → X.PObj.OrTangent)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T) :
    (∀ y ∈ X.PObj.smoothSet, y ∉ supp Θ → X.boundaryLift bd T y = 0) ∧
    ∀ (x : Obj) (B : X.OrientedBranchingStructure Θ x),
      (∀ i, X.PObj.HasTameInducedStructure (B.M i)) →
      (∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = B.orientedSum y) →
      ∀ y ∈ B.U, y ∈ X.PObj.smoothSet →
        X.boundaryLift bd T y = ∑ i with ∃ hy : y ∈ B.M i,
            X.PObj.subDegIndex (B.isSmoothSubmanifold i).isSubMPolyfold ⟨y, hy⟩ = 1,
          Finsupp.single (bd ((B.orient i).tangent y)) (B.σ i) := by
  refine ⟨fun y hy hys => ?_, fun x B ht hB y hy hys => ?_⟩
  · rw [boundaryLift, hT.eq_zero_of_not_mem hy hys, degreePart, Finsupp.filter_zero,
      Finsupp.mapDomain_zero]
  · rw [boundaryLift, hB y hy hys, degreePart_orientedSum B ht, Finsupp.mapDomain_finsetSum]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_single

end EpGroupoid

end Polyfold
