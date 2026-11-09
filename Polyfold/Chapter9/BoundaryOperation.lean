import Polyfold.Chapter9.OrientationBoundary
import Polyfold.Chapter2.PartialConeQuadrant

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.3 "Orientations": **Definition 9.3.8** (2021 p. 427; 2017: Definition 9.9,
p. 313), **Proposition 9.3.9** (2021 p. 428, new in the 2021 edition) and **Definition 9.3.10**
(2021 p. 428; 2017: Definition 9.11, p. 314), with the boundary operation built from `M` itself.
Numbers and pages are the 2021 text's, the 2017 ones in parentheses.

# The boundary operation of Definition 9.3.8, from the submanifold

## The text, paraphrased

(Before Definition 9.3.8) For a tame `M`, the points with `d_M(y) = 1` form an open dense part
of `∂M`, a manifold.  (Definition 9.3.8) For an oriented `(M, o)` and `y ∈ ∂M` with
`d_M(y) = 1`, a basis `(a₁, …, a_{n-1})` of `T_y∂M` is positive iff `(e, a₁, …, a_{n-1})` is
positive for `o_y`, `e` outward pointing; the resulting `o_{∂M}` fits continuously together.
(Lemma 9.3.7, proof) `d_M(y) = dim(T_yM / T^R_yM)`, with the partial quadrant `C_yM`.

## What is formalized

* **Presented charts** `MPolyfold.PresentedChart P y`: a chart at `y` with a presentation of its
  partial quadrant, in which `E_y` (`red`) and `C_y` (`cone`) of Definition 2.33 are read off at
  `φ(y)`.  **Chart independence**: a chart change acts on chart vectors over `y` by a continuous
  linear map carrying `E_y` into `E'_y` and `C_y` into `C'_y` (`PresentedChart.exists_clm`).
* The intrinsic notions on `T_yX`: `IsReducedVec y α` (`α ∈ T^R_yX`), `IsInwardVec y α`
  (`α ∈ C_yX`), chart-independent (`isReducedVec_iff`, `isInwardVec_iff`); the reduced
  codimension `HasReducedCodim y ℓ g` (`dim(L / L ∩ T^R_yX) = ℓ`), chart independent
  (`hasReducedCodim_iff`, through `quotDim_eq_of_inverse`).
* **`d_M(y)` is the reduced codimension of `T_yM`** for tame `M` (`subDegIndex_eq_quotDim_span`,
  Lemma 9.3.7's proof), so Chapter 9's degree `HasSubDegree` is the reduced codimension on tangent
  spaces of tame submanifolds (`hasSubDegree_iff`).
* **The partial cone spans `T_yM`** (`exists_sub_eq_of_mem_range`,
  `exists_sub_eq_vec_submanifoldTangent`): every vector of `T_yM` is a difference of two vectors
  of `C_yM = T_yM ∩ C_y`; so if `T_yM` has reduced codimension `1` (any submanifold, tame or
  not), it contains an inward vector off `T^R_yM` (`isBoundaryAdmissible_of_submanifold`), `C_yM`
  is a half-space of `T_yM` bounded by `T^R_yM` (`exists_coeff_halfSpace`), outward vectors exist
  (`IsBoundaryAdmissible.exists_outward`) and any two are related by `e' = c e + k`, `c > 0`,
  `k ∈ T^R_yM` (`exists_pos_sub_mem_of_not_mem`, `IsBoundaryAdmissible.exists_pos`).
* **The boundary operation** `MPolyfold.boundaryOp : OrTangent P → OrTangent P`, defined from the
  ambient structure alone: `T_y(M, o) ↦ (T^R_yM, o_∂)` with the frames `a` of `T^R_yM` such that
  `(e, a)` is positive for *every* outward `e`.  For `T_yM` of reduced codimension `1` with an
  inward vector off `T^R_yM` (in particular for every submanifold with `d_M(y) = 1`):
  `boundaryOp_eq` (it is Definition 9.3.8's `boundaryFrames O K e` for *any* outward `e`: the
  independence of the outward vector), `isOrientedAt_boundaryOp` (an orientation of `T_y∂M`),
  `boundaryOp_dim`, `boundaryOp_carrier`.
* **`T_y∂M = T^R_yM`** (`chartVec_image_boundaryCarrier`: the chart image of the boundary
  carrier is the reduced tangent space `T^R_z Q` of the induced chart of `M`) and **outward means
  "not in `C_yM`"** (`isOutward_iff_not_mem_partialCone`, with Part I's partial cone of the
  induced chart).
* **Definition 9.3.8 for a submanifold** `SubmanifoldOrientation.boundaryOp_tangent` (for `M`
  with `d_M(y) = 1`, tame or with reduced codimension `1`).
* **Definition 9.3.10 and Proposition 9.3.9 with this operation**: `boundaryLift X.PObj.boundaryOp`
  (`proposition_9_3_9_boundaryOp`, no data hypothesis); the intrinsic `T̂_{∂Θ}`
  `EpGroupoid.boundaryOrientation` (filter by reduced codimension `1`), with
  `boundaryLift_boundaryOp_eq_boundaryOrientation` (they agree for tame oriented `Θ̂`,
  `IsTameOrientation`, Definition 9.3.10's hypothesis) and `proposition_9_3_9_boundaryOrientation`.
* Witnesses: `isTameOrientation_zero`, `isTameOrientation_of_degIndex_eq_zero`; the situation of
  Definition 9.3.8 occurs, at the corner of the half-line `[0, ∞)`
  (`exists_isBoundaryAdmissible_halfLine`).
* Along sc-diffeomorphisms, equivalences and generalized isomorphisms (Theorem 11.3.9) the
  operation is studied in `Chapter11/BoundaryOrientationEquiv.lean`.

## What the text leaves implicit, and the choices made

* `T_yX` carries no linear structure in Part I (gap G.7): `T^R_yX` and `C_yX` are read in a
  presented chart, and shown independent of it.  `T_y∂M` is the set of vectors of `T_yM` lying in
  `T^R_yX` (equivalently `T^R_yM` of the induced structure).
* "Outward pointing" is read as: in `T_yM`, not in the partial cone `C_yX` (equivalently not in
  `C_yM = T_yM ∩ C_yX`).  The boundary frames are those positive for every outward vector, which
  makes `boundaryOp` a function of the oriented tangent set (no choice); for `d_M(y) = 1` this is
  Definition 9.3.8 for any single outward vector.
* The text's `d_M(y) = 1` is, for tame `M`, the reduced codimension `1` of `T_yM`
  (Lemma 9.3.7's proof); the intrinsic `boundaryOrientation` filters by the latter, which needs no
  quantifier over submanifolds.

## Not formalized, and why

* That `o_{∂M}` "fits continuously together": this would be a `SubmanifoldOrientation` of the
  stratum `∂₁M = {d_M = 1}`, whose continuity clause needs `∂₁M` as a smooth submanifold with
  `T_y∂₁M = T^R_yM`, and a continuous outward field along it.  The stratum is not formalized as a
  submanifold, so the operation is defined and studied pointwise only.  The extension to the
  closed faces (Figure 9.1) and Remark 9.3.11 are not formalized either.
-/

set_option maxSynthPendingDepth 3

open Set Module Submodule Filter Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### A linear-algebra lemma on `dim(A / A ∩ B)` -/

/-- `dim(A / A ∩ B) = dim(A' / A' ∩ B')` when a linear map `Λ` maps `A` onto `A'` with left inverse
`Λ'` on `A`, and `Λ`, `Λ'` map `B`, `B'` into each other. -/
theorem quotDim_eq_of_inverse {V V' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V']
    [Module ℝ V'] (Λ : V →ₗ[ℝ] V') (Λ' : V' →ₗ[ℝ] V) {A B : Submodule ℝ V}
    {A' B' : Submodule ℝ V'} (hA : A.map Λ = A') (hinv : ∀ v ∈ A, Λ' (Λ v) = v)
    (hB : ∀ v ∈ B, Λ v ∈ B') (hB' : ∀ w ∈ B', Λ' w ∈ B) : quotDim A B = quotDim A' B' := by
  have hmapA : ∀ v ∈ A, Λ v ∈ A' := fun v hv => hA ▸ mem_map_of_mem hv
  have hA'mem : ∀ w ∈ A', Λ' w ∈ A ∧ Λ (Λ' w) = w := by
    intro w hw
    rw [← hA] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    rw [hinv v hv]
    exact ⟨hv, rfl⟩
  let e : A ≃ₗ[ℝ] A' :=
    { toFun := fun v => ⟨Λ v.1, hmapA v.1 v.2⟩
      invFun := fun w => ⟨Λ' w.1, (hA'mem w.1 w.2).1⟩
      map_add' := fun v w => Subtype.ext (map_add Λ v.1 w.1)
      map_smul' := fun c v => Subtype.ext (map_smul Λ c v.1)
      left_inv := fun v => Subtype.ext (hinv v v.2)
      right_inv := fun w => Subtype.ext (hA'mem w w.2).2 }
  unfold quotDim
  refine LinearEquiv.finrank_eq (Submodule.Quotient.equiv _ _ e ?_)
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hB _ hv
  · intro hw
    refine ⟨e.symm w, hB' _ hw, e.apply_symm_apply w⟩

/-- `dim(A / A ∩ B) = 0` for `A = 0`. -/
theorem quotDim_bot_left {V : Type*} [AddCommGroup V] [Module ℝ V] (B : Submodule ℝ V) :
    quotDim (⊥ : Submodule ℝ V) B = 0 := by
  unfold quotDim
  have : Subsingleton (↥(⊥ : Submodule ℝ V)) := inferInstance
  exact finrank_zero_of_subsingleton

/-! ### The half-space lemma -/

section HalfSpace

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The partial cone of `T_yM` is a half-space** (linear algebra): let `S` be a convex cone
containing the subspace `H`, with `S ∩ (−S) ⊆ H`, and `N` a subspace with `dim(N / N ∩ H) = 1`
containing some `s ∈ S ∖ H`.  Then every `v ∈ N` is `v = c s + h` with `h ∈ H`, and `v ∈ S` iff
`c ≥ 0`. -/
theorem exists_coeff_halfSpace {N H : Submodule ℝ V} {S : Set V}
    (hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) (hsmul : ∀ t : ℝ, 0 ≤ t → ∀ a ∈ S, t • a ∈ S)
    (hHS : (H : Set V) ⊆ S) (hneg : ∀ a ∈ S, -a ∈ S → a ∈ H) (h1 : quotDim N H = 1) {s : V}
    (hsN : s ∈ N) (hsS : s ∈ S) (hsH : s ∉ H) (v : V) (hv : v ∈ N) :
    ∃ c : ℝ, v - c • s ∈ H ∧ (v ∈ S ↔ 0 ≤ c) := by
  set H' := H.comap N.subtype
  have hq : (Submodule.Quotient.mk (⟨s, hsN⟩ : N) : N ⧸ H') ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hsH
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hq).1 h1
    (Submodule.Quotient.mk (⟨v, hv⟩ : N))
  have hmem : v - c • s ∈ H := by
    have : (⟨v, hv⟩ : N) - c • ⟨s, hsN⟩ ∈ H' := by
      rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_smul, hc]
    exact this
  refine ⟨c, hmem, ⟨fun hvS => ?_, fun hc0 => ?_⟩⟩
  · by_contra hneg'
    push Not at hneg'
    have h2 : -v ∈ S := by
      have : -v = (-c) • s + (-(v - c • s)) := by
        rw [neg_smul, neg_sub]; abel
      rw [this]
      exact hadd _ (hsmul _ (by linarith) _ hsS) _ (hHS (H.neg_mem hmem))
    have hvH := hneg v hvS h2
    have hcs : c • s ∈ H := by
      have := H.sub_mem hvH hmem
      rwa [sub_sub_cancel] at this
    exact hsH (by
      have := H.smul_mem c⁻¹ hcs
      rwa [smul_smul, inv_mul_cancel₀ hneg'.ne, one_smul] at this)
  · have : v = c • s + (v - c • s) := by abel
    rw [this]
    exact hadd _ (hsmul _ hc0 _ hsS) _ (hHS hmem)

/-- **Two outward vectors are related by `e' = c e + k`, `c > 0`, `k ∈ H`** (in the situation of
`exists_coeff_halfSpace`, "outward" meaning `∉ S`). -/
theorem exists_pos_sub_mem_of_not_mem {N H : Submodule ℝ V} {S : Set V}
    (hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) (hsmul : ∀ t : ℝ, 0 ≤ t → ∀ a ∈ S, t • a ∈ S)
    (hHS : (H : Set V) ⊆ S) (hneg : ∀ a ∈ S, -a ∈ S → a ∈ H) (h1 : quotDim N H = 1) {s : V}
    (hsN : s ∈ N) (hsS : s ∈ S) (hsH : s ∉ H) {e e' : V} (he : e ∈ N) (he' : e' ∈ N)
    (heS : e ∉ S) (he'S : e' ∉ S) : ∃ c : ℝ, 0 < c ∧ e' - c • e ∈ H := by
  obtain ⟨a, ha, haS⟩ := exists_coeff_halfSpace hadd hsmul hHS hneg h1 hsN hsS hsH e he
  obtain ⟨b, hb, hbS⟩ := exists_coeff_halfSpace hadd hsmul hHS hneg h1 hsN hsS hsH e' he'
  have ha0 : a < 0 := lt_of_not_ge fun h => heS (haS.2 h)
  have hb0 : b < 0 := lt_of_not_ge fun h => he'S (hbS.2 h)
  refine ⟨b / a, div_pos_of_neg_of_neg hb0 ha0, ?_⟩
  have : e' - (b / a) • e = (e' - b • s) - (b / a) • (e - a • s) := by
    rw [smul_sub, smul_smul, div_mul_cancel₀ _ ha0.ne]; abel
  rw [this]
  exact H.sub_mem hb (H.smul_mem _ ha)

/-- With `dim(N / N ∩ H) = 1` and `N` finite-dimensional, `dim(N ∩ H) = dim N - 1`. -/
theorem finrank_inf_eq_of_quotDim_eq_one {N H : Submodule ℝ V} [FiniteDimensional ℝ N]
    (h1 : quotDim N H = 1) : finrank ℝ ↥(N ⊓ H) + 1 = finrank ℝ N := by
  have h := Submodule.finrank_quotient_add_finrank (H.comap N.subtype)
  unfold quotDim at h1
  rw [h1] at h
  have he : (H.comap N.subtype) ≃ₗ[ℝ] ↥(N ⊓ H) :=
    { toFun := fun v => ⟨v.1.1, v.1.2, v.2⟩
      invFun := fun w => ⟨⟨w.1, w.2.1⟩, w.2.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← he.finrank_eq]
  omega

end HalfSpace

/-! ### Presented charts -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

variable (P) in
/-- **A presented chart at `y`**: a chart `φ` of `X` around `y` with a presentation
`T : E ≅ ℝⁿ ⊕ W` of its partial quadrant, `C = T⁻¹([0,∞)ⁿ ⊕ W)`.  In it the minimal subspace
`E_{φ(y)}` and the partial quadrant `C_{φ(y)}` of Definition 2.33 are the chart forms of
`T^R_yX` and `C_yX`. -/
structure PresentedChart (y : X) where
  /-- The chart. -/
  φ : MChart X
  isChart : P.IsChart φ
  mem_source : y ∈ φ.source
  /-- The number of `[0,∞)`-factors. -/
  n : ℕ
  /-- The linear factor. -/
  W : ScBanach
  /-- The presentation. -/
  T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)
  hT : φ.model.C = T 0 ⁻¹' quadrant n W 0

namespace PresentedChart

variable {y : X} (c : P.PresentedChart y)

/-- The chart vector of a tangent vector in `c`. -/
def vec (α : P.TangentSpace) : c.φ.model.E 0 := chartVec c.isChart α

/-- `E_{φ(y)}`, the chart form of `T^R_yX`. -/
def red : Submodule ℝ (c.φ.model.E 0) := minimalSubspaceWith c.T (c.φ y)

/-- `C_{φ(y)}`, the chart form of `C_yX`. -/
def cone : Set (c.φ.model.E 0) := partialQuadrantAtWith c.T (c.φ y)

theorem red_subset_cone : (c.red : Set (c.φ.model.E 0)) ⊆ c.cone :=
  minimalSubspaceWith_subset_partialQuadrantAtWith _ _

theorem add_mem_cone {a b : c.φ.model.E 0} (ha : a ∈ c.cone) (hb : b ∈ c.cone) :
    a + b ∈ c.cone := fun i hi => by
  have h1 := ha i hi
  have h2 := hb i hi
  simp only [map_add, Prod.fst_add, Pi.add_apply]
  exact add_nonneg h1 h2

theorem smul_mem_cone {t : ℝ} (ht : 0 ≤ t) {a : c.φ.model.E 0} (ha : a ∈ c.cone) :
    t • a ∈ c.cone := fun i hi => by
  have h1 := ha i hi
  simp only [map_smul, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg ht h1

theorem mem_red_of_mem_cone {a : c.φ.model.E 0} (ha : a ∈ c.cone) (ha' : -a ∈ c.cone) :
    a ∈ c.red := by
  refine (mem_minimalSubspaceWith c.T).2 fun i hi => ?_
  have h1 := ha i hi
  have h2 := ha' i hi
  simp only [map_neg, Prod.fst_neg, Pi.neg_apply, neg_nonneg] at h2
  exact le_antisymm h2 h1

/-- **The chart change of a presented chart**: on the fibre over `y` it acts on chart vectors by
a continuous linear map `L = D(ψ ∘ φ⁻¹)` with `L(E_{φ(y)}) ⊆ E'_{ψ(y)}` (two-sided sign argument)
and `L(C_{φ(y)}) ⊆ C'_{ψ(y)}` (one-sided sign argument). -/
theorem exists_clm (c' : P.PresentedChart y) (hy : y ∈ P.levelSet 1) :
    ∃ L : c.φ.model.E 0 →L[ℝ] c'.φ.model.E 0,
      (∀ α : P.TangentSpace, P.levelVal 1 (P.tangentProj α) = y → c'.vec α = L (c.vec α)) ∧
      MapsTo L c.red c'.red ∧ MapsTo L c.cone c'.cone := by
  obtain ⟨φ, hφ, hyφ, n, W, T, hT⟩ := c
  obtain ⟨ψ, hψ, hyψ, n', W', T', hT'⟩ := c'
  obtain ⟨R, hR⟩ := φ.isScRetract_overlap ψ
  have hf := (hφ.compatible hψ (P := P)).1
  have hz : φ.model.E.toBase 1 (levelLift φ 1 y) = φ y := P.toBase_levelLift hφ hyφ hy
  have hzO : levelLift φ 1 y ∈ φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, hR]
    exact φ.mem_overlap ψ hyφ hyψ
  have hzU := R.lvlSet_retract_subset 1 hzO
  have hsm := (hf.comp_isScSmooth R hR).isSc1
  have hC : MapsTo (φ.transition ψ ∘ R) R.U ψ.model.C := fun w hw => by
    have h1 : R w ∈ φ.overlap ψ := hR ▸ R.apply_mem_retract hw
    obtain ⟨x', hx', hx'eq⟩ := hf.mapsTo h1
    rw [Function.comp_apply, ← hx'eq]
    exact ψ.apply_mem_C hx'.1
  have hval : (φ.transition ψ ∘ R) (φ y) = ψ y := by
    rw [Function.comp_apply, R.apply_eq_self_of_mem_retract (hR ▸ φ.mem_overlap ψ hyφ hyψ),
      φ.transition_apply ψ hyφ]
  refine ⟨scDeriv R.U (φ.transition ψ ∘ R) (levelLift φ 1 y), fun α hα => ?_, ?_, ?_⟩
  · have hαφ : α ∈ tangentChartSet φ := by change _ ∈ φ.source; rw [hα]; exact hyφ
    have hmem := tangentChartMap_mem hφ hαφ
    have hfst : (tangentChartMap hφ α).1 = levelLift φ 1 y := by
      rw [tangentChartMap_fst hφ hαφ, hα]
    have hov : (tangentChartMap hφ α) ∈ retractTangent φ.model.E φ.model.C (φ.overlap ψ) := by
      have hsub : φ.source ∩ ψ.source ⊆ φ.source := inter_subset_left
      refine (TangentPre.mem_retractTangent_image_iff hsub
        (φ.isOpen_source.inter ψ.isOpen_source) ?_).2 hmem
      rw [hfst, hz]
      exact ⟨y, ⟨hyφ, hyψ⟩, rfl⟩
    have h1 := tangentChartMap_mk_ofVec_of_mem hφ hψ hmem hov
    rw [mk_ofVec_tangentChartMap hφ hαφ] at h1
    change chartVec hψ α = _
    unfold chartVec
    rw [h1, retractTangentMap_apply hf R hR hov, hfst]
    rfl
  · have h := IsSc1With.mapsTo_minimalSubspace T hT T' hT' R.relOpen hsm.isSc1With_scDeriv hC hzU
    rw [hz, hval] at h
    exact h
  · have h := IsSc1With.mapsTo_partialQuadrant T hT T' hT' R.relOpen hsm.isSc1With_scDeriv hC hzU
    rw [hz, hval] at h
    exact h

end PresentedChart

/-- Every point has a presented chart. -/
theorem nonempty_presentedChart (y : X) : Nonempty (P.PresentedChart y) := by
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  exact ⟨⟨φ, hφ, hyφ, n, W, T, hT⟩⟩

/-! ### `T^R_yX`, `C_yX` and the reduced codimension, intrinsically -/

variable (P) in
/-- **`α ∈ T^R_yX`**: in every presented chart at `y`, the chart vector of `α` lies in
`E_{φ(y)}` (Definitions 2.27, 2.33). -/
def IsReducedVec (y : X) (α : P.TangentSpace) : Prop :=
  ∀ c : P.PresentedChart y, c.vec α ∈ c.red

variable (P) in
/-- **`α ∈ C_yX`** (the partial cone): in every presented chart at `y`, the chart vector of `α`
lies in `C_{φ(y)}`. -/
def IsInwardVec (y : X) (α : P.TangentSpace) : Prop :=
  ∀ c : P.PresentedChart y, c.vec α ∈ c.cone

/-- `T^R_yX` may be read in any one presented chart. -/
theorem isReducedVec_iff {y : X} (c : P.PresentedChart y) {α : P.TangentSpace}
    (hα : P.levelVal 1 (P.tangentProj α) = y) : P.IsReducedVec y α ↔ c.vec α ∈ c.red := by
  refine ⟨fun h => h c, fun h c' => ?_⟩
  have hy : y ∈ P.levelSet 1 := hα ▸ levelVal_mem _
  obtain ⟨L, hL, hred, -⟩ := c.exists_clm c' hy
  rw [hL α hα]
  exact hred h

/-- `C_yX` may be read in any one presented chart. -/
theorem isInwardVec_iff {y : X} (c : P.PresentedChart y) {α : P.TangentSpace}
    (hα : P.levelVal 1 (P.tangentProj α) = y) : P.IsInwardVec y α ↔ c.vec α ∈ c.cone := by
  refine ⟨fun h => h c, fun h c' => ?_⟩
  have hy : y ∈ P.levelSet 1 := hα ▸ levelVal_mem _
  obtain ⟨L, hL, -, hcone⟩ := c.exists_clm c' hy
  rw [hL α hα]
  exact hcone h

/-- `dim(L / L ∩ E_y)` of a set of vectors over `y` does not depend on the presented chart. -/
theorem PresentedChart.quotDim_span_eq {y : X} (c c' : P.PresentedChart y)
    {L : Set P.TangentSpace} (hL : ∀ α ∈ L, P.levelVal 1 (P.tangentProj α) = y) :
    quotDim (span ℝ (c.vec '' L)) c.red = quotDim (span ℝ (c'.vec '' L)) c'.red := by
  rcases L.eq_empty_or_nonempty with rfl | ⟨α₀, hα₀⟩
  · simp only [image_empty, span_empty, quotDim_bot_left]
  have hy : y ∈ P.levelSet 1 := hL α₀ hα₀ ▸ levelVal_mem _
  obtain ⟨Λ, hΛ, hred, -⟩ := c.exists_clm c' hy
  obtain ⟨Λ', hΛ', hred', -⟩ := c'.exists_clm c hy
  refine quotDim_eq_of_inverse (Λ : c.φ.model.E 0 →ₗ[ℝ] c'.φ.model.E 0)
    (Λ' : c'.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) ?_ ?_ (fun v hv => hred hv) (fun w hw => hred' hw)
  · rw [Submodule.map_span, image_image]
    congr 1
    exact image_congr fun α hα => (hΛ α (hL α hα)).symm
  · intro v hv
    have heq : Set.EqOn ((Λ' : c'.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) ∘ₗ
        (Λ : c.φ.model.E 0 →ₗ[ℝ] c'.φ.model.E 0))
        (LinearMap.id : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) (c.vec '' L) := by
      rintro _ ⟨α, hα, rfl⟩
      simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
        LinearMap.id_coe, id]
      rw [← hΛ α (hL α hα), ← hΛ' α (hL α hα)]
    exact LinearMap.eqOn_span' heq hv

variable (P) in
/-- **The reduced codimension `dim(L / L ∩ T^R_yX) = ℓ`** of an oriented tangent set, read in every
presented chart at `y`.  For `T_yM`, `M` tame, it is `d_M(y)` (`subDegIndex_eq_quotDim_span`). -/
def HasReducedCodim (y : X) (ℓ : ℕ) (g : OrTangent P) : Prop :=
  ∀ c : P.PresentedChart y, quotDim (span ℝ (c.vec '' g.carrier)) c.red = ℓ

/-- The reduced codimension may be read in any one presented chart. -/
theorem hasReducedCodim_iff {y : X} (c : P.PresentedChart y) {ℓ : ℕ} {g : OrTangent P}
    (hg : ∀ α ∈ g.carrier, P.levelVal 1 (P.tangentProj α) = y) :
    P.HasReducedCodim y ℓ g ↔ quotDim (span ℝ (c.vec '' g.carrier)) c.red = ℓ :=
  ⟨fun h => h c, fun h c' => (c.quotDim_span_eq c' hg).symm.trans h⟩

/-! ### `d_M(y)` is the reduced codimension of `T_yM` (Lemma 9.3.7's proof) -/

/-- The chart image of `T_yA` in a presented chart is the tangent space `T_zQ = Dr(z)E` of the
induced chart `Q = φ(W ∩ A)`, a linear subspace. -/
theorem span_vec_submanifoldTangent {A : Set X} (hA : P.IsSmoothSubmanifold A) {y : X}
    (hy : y ∈ A) (c : P.PresentedChart y) (R : ScRetraction c.φ.model.E c.φ.model.C)
    (hR : R.retract = c.φ '' ((hA.data hy).toSubData.shrink c.φ ∩ A)) :
    c.vec '' P.submanifoldTangent A y =
        (LinearMap.range (scDeriv R.U R (levelLift c.φ 1 y) :
          c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) : Set (c.φ.model.E 0)) ∧
      levelLift c.φ 1 y ∈ c.φ.model.E.lvlSet R.retract 1 := by
  have hyV := hA.mem_data_V hy
  have hy1 : y ∈ P.levelSet 1 := ((hA.data hy).mem_levelSet_one hy hyV)
  have hz : c.φ.model.E.toBase 1 (levelLift c.φ 1 y) = c.φ y :=
    P.toBase_levelLift c.isChart c.mem_source hy1
  have hzR : levelLift c.φ 1 y ∈ c.φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, hR]
    exact mem_image_of_mem _ ⟨(hA.data hy).toSubData.mem_shrink c.φ hy hyV c.mem_source, hy⟩
  refine ⟨?_, hzR⟩
  change chartVec c.isChart '' _ = _
  rw [chartVec_image_submanifoldTangent c.isChart (hA.data hy) hy hyV c.mem_source, ← hR,
    tangentSpace_eq_coe_submodule R hzR]

/-- **`d_M(y) = dim(T_yM / T^R_yM)`** for a smooth submanifold with tame induced structure, in
every presented chart (Lemma 9.3.7's proof, Remark 2.5.9;
`subDegIndex_eq_quotDim_of_hasTameInducedStructure`). -/
theorem subDegIndex_eq_quotDim_span {A : Set X} (hA : P.IsSmoothSubmanifold A)
    (ht : P.HasTameInducedStructure A) {y : X} (hy : y ∈ A) (c : P.PresentedChart y) :
    P.subDegIndex hA.isSubMPolyfold ⟨y, hy⟩ =
      quotDim (span ℝ (c.vec '' P.submanifoldTangent A y)) c.red := by
  obtain ⟨R, hR⟩ := (hA.data hy).toSubData.isScRetract_image c.φ c.isChart
  obtain ⟨himg, hzR⟩ := span_vec_submanifoldTangent hA hy c R hR
  have hyV := hA.mem_data_V hy
  have hy1 : y ∈ P.levelSet 1 := ((hA.data hy).mem_levelSet_one hy hyV)
  have hz : c.φ.model.E.toBase 1 (levelLift c.φ 1 y) = c.φ y :=
    P.toBase_levelLift c.isChart c.mem_source hy1
  rw [subDegIndex_eq_quotDim_of_hasTameInducedStructure hA ht (hA.data hy) c.isChart R hR c.T c.hT
    (a := ⟨y, hy⟩) hyV c.mem_source hz, himg, Submodule.span_eq]
  unfold quotDim reducedTangentSpaceWith
  rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq, hz]
  rfl

/-- **Chapter 9's degree is the reduced codimension** on tangent spaces of tame submanifolds:
`HasSubDegree y ℓ g` iff `g` is the tangent set of some tame submanifold through `y` and has
reduced codimension `ℓ` (Lemma 9.3.7). -/
theorem hasSubDegree_iff {y : X} {ℓ : ℕ} {g : OrTangent P} :
    P.HasSubDegree y ℓ g ↔ (∃ (A : Set X) (_ : P.IsSmoothSubmanifold A), y ∈ A ∧
      P.HasTameInducedStructure A ∧ P.submanifoldTangent A y = g.carrier) ∧
      P.HasReducedCodim y ℓ g := by
  constructor
  · rintro ⟨A, hA, hy, ht, hT, hd⟩
    refine ⟨⟨A, hA, hy, ht, hT⟩, fun c => ?_⟩
    rw [← hT, ← subDegIndex_eq_quotDim_span hA ht hy c, hd]
  · rintro ⟨⟨A, hA, hy, ht, hT⟩, hcod⟩
    obtain ⟨c⟩ := P.nonempty_presentedChart y
    refine ⟨A, hA, hy, ht, hT, ?_⟩
    rw [subDegIndex_eq_quotDim_span hA ht hy c, hT]
    exact hcod c

/-- For an oriented tame submanifold, the degree of `T_y(M, o)` is the reduced codimension. -/
theorem SubmanifoldOrientation.hasSubDegree_iff_hasReducedCodim {A : Set X} {n : ℕ}
    (o : P.SubmanifoldOrientation A n) (hA : P.IsSmoothSubmanifold A)
    (ht : P.HasTameInducedStructure A) {y : X} (hy : y ∈ A) {ℓ : ℕ} :
    P.HasSubDegree y ℓ (o.tangent y) ↔ P.HasReducedCodim y ℓ (o.tangent y) :=
  hasSubDegree_iff.trans ⟨fun h => h.2, fun h => ⟨⟨A, hA, hy, ht, rfl⟩, h⟩⟩

/-! ### The partial cone spans `T_yM` -/

/-- **`T_xO` is spanned by `C_xO`** for every sc-smooth retraction (tame or not): `v = Dr(x)u`
with `u = u⁺ − u⁻`, `u^± ∈ C`, and `Dr(x)C_x ⊆ C_x`. -/
theorem exists_sub_eq_of_mem_range {E : ScBanach} {C : Set (E 0)} {n : ℕ} {W : ScBanach}
    (R : ScRetraction E C) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) {v : E 0}
    (hv : v ∈ LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) :
    ∃ p q : E 0, p ∈ LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0) ∧
      p ∈ partialQuadrantAtWith T (E.toBase 1 x) ∧
      q ∈ LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0) ∧
      q ∈ partialQuadrantAtWith T (E.toBase 1 x) ∧ v = p - q := by
  obtain ⟨u, rfl⟩ := hv
  set a : Fin n → ℝ := (T 0 u).1
  set w := (T 0 u).2
  set up : E 0 := (T 0).symm ((fun i => max (a i) 0, w) : (Fin n → ℝ) × W 0)
  set um : E 0 := (T 0).symm ((fun i => max (-(a i)) 0, 0) : (Fin n → ℝ) × W 0)
  have hu : u = up - um := by
    apply (T 0).injective
    rw [map_sub]
    simp only [up, um, ContinuousLinearEquiv.apply_symm_apply]
    refine Prod.ext (funext fun i => ?_) ?_
    · change a i = max (a i) 0 - max (-(a i)) 0
      rcases le_total 0 (a i) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · change w = w - 0
      rw [sub_zero]
  have hcone : ∀ (b : Fin n → ℝ), (∀ i, 0 ≤ b i) → ∀ w' : W 0,
      (T 0).symm ((b, w') : (Fin n → ℝ) × W 0) ∈ partialQuadrantAtWith T (E.toBase 1 x) :=
    fun b hb w' i _ => by
      simp only [ContinuousLinearEquiv.apply_symm_apply]
      exact hb i
  have hDC := R.scDeriv_mapsTo_partialQuadrant T hT hx
  refine ⟨scDeriv R.U R x up, scDeriv R.U R x um, ⟨up, rfl⟩,
    hDC (hcone _ (fun i => le_max_right _ _) w), ⟨um, rfl⟩,
    hDC (hcone _ (fun i => le_max_right _ _) 0), ?_⟩
  change scDeriv R.U R x u = _
  rw [hu, map_sub]

/-- **`C_yM` spans `T_yM`**: in a presented chart every vector of the chart image of `T_yA` is a
difference of two such vectors lying in `C_{φ(y)}`. -/
theorem exists_sub_eq_vec_submanifoldTangent {A : Set X} (hA : P.IsSmoothSubmanifold A) {y : X}
    (hy : y ∈ A) (c : P.PresentedChart y) {α : P.TangentSpace}
    (hα : α ∈ P.submanifoldTangent A y) :
    ∃ β ∈ P.submanifoldTangent A y, ∃ γ ∈ P.submanifoldTangent A y,
      c.vec β ∈ c.cone ∧ c.vec γ ∈ c.cone ∧ c.vec α = c.vec β - c.vec γ := by
  obtain ⟨R, hR⟩ := (hA.data hy).toSubData.isScRetract_image c.φ c.isChart
  obtain ⟨himg, hzR⟩ := span_vec_submanifoldTangent hA hy c R hR
  have hyV := hA.mem_data_V hy
  have hy1 : y ∈ P.levelSet 1 := ((hA.data hy).mem_levelSet_one hy hyV)
  have hz : c.φ.model.E.toBase 1 (levelLift c.φ 1 y) = c.φ y :=
    P.toBase_levelLift c.isChart c.mem_source hy1
  have hv : c.vec α ∈ LinearMap.range (scDeriv R.U R (levelLift c.φ 1 y) :
      c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) := by
    rw [← SetLike.mem_coe, ← himg]; exact mem_image_of_mem _ hα
  obtain ⟨p, q, hp, hpC, hq, hqC, hpq⟩ := exists_sub_eq_of_mem_range R c.T c.hT hzR hv
  have hp' : p ∈ c.vec '' P.submanifoldTangent A y := by rw [himg]; exact hp
  have hq' : q ∈ c.vec '' P.submanifoldTangent A y := by rw [himg]; exact hq
  obtain ⟨β, hβ, rfl⟩ := hp'
  obtain ⟨γ, hγ, rfl⟩ := hq'
  rw [hz] at hpC hqC
  exact ⟨β, hβ, γ, hγ, hpC, hqC, hpq⟩

/-- `dim(A / A ∩ B) = 0` for `A ⊆ B`. -/
theorem quotDim_eq_zero_of_le {V : Type*} [AddCommGroup V] [Module ℝ V] {A B : Submodule ℝ V}
    (h : A ≤ B) : quotDim A B = 0 := by
  unfold quotDim
  have : Subsingleton (A ⧸ B.comap A.subtype) :=
    Submodule.Quotient.subsingleton_iff.2 (Submodule.comap_subtype_eq_top.2 h)
  exact finrank_zero_of_subsingleton

/-! ### The boundary operation of Definition 9.3.8 -/

variable (P) in
/-- `α ∈ T^R_yX` at its base point `y`. -/
def IsReducedTangent (α : P.TangentSpace) : Prop :=
  P.IsReducedVec (P.levelVal 1 (P.tangentProj α)) α

variable (P) in
/-- **`α` points outward**: `α ∉ C_yX` at its base point `y` (in `T_yM` with `d_M(y) = 1` this is
`−α ∈ C_yM ∖ T^R_yM`, the text's outward pointing vectors). -/
def IsOutwardTangent (α : P.TangentSpace) : Prop :=
  ¬ P.IsInwardVec (P.levelVal 1 (P.tangentProj α)) α

variable (P) in
/-- **`T_y∂M`** for `L = T_yM`: the vectors of `L` lying in `T^R_yX`, which is `T^R_yM`
(`chartVec_image_boundaryCarrier`). -/
def boundaryCarrier (L : Set P.TangentSpace) : Set P.TangentSpace :=
  {α ∈ L | P.IsReducedTangent α}

variable (P) in
/-- **The boundary operation `T_y(M, o) ↦ T_y(∂M, o_{∂M})` of Definition 9.3.8** (2021 p. 427;
2017: Definition 9.9), built from the ambient structure alone: an oriented tangent set
`(L, O)` of dimension `m + 1` goes to `T_y∂M = boundaryCarrier L` of dimension `m`, with the
frames `a` of `T_y∂M` such that `(e, a)` is positive for every outward `e ∈ L`.  In the
situation of Definition 9.3.8 this is `boundaryFrames O (T_y∂M) e` for any single outward `e`
(`boundaryOp_eq`), and an orientation of `T_y∂M` (`isOrientedAt_boundaryOp`).  (For dimension
`0` the value is irrelevant.) -/
def boundaryOp : OrTangent P → OrTangent P
  | ⟨0, L, _⟩ => ⟨0, P.boundaryCarrier L, ∅⟩
  | ⟨m + 1, L, O⟩ => ⟨m, P.boundaryCarrier L,
      {a | (∀ i, a i ∈ P.boundaryCarrier L) ∧
        ∀ e ∈ L, P.IsOutwardTangent e → (Fin.cons e a : Fin (m + 1) → P.TangentSpace) ∈ O}⟩

theorem boundaryOp_carrier (g : OrTangent P) :
    (P.boundaryOp g).carrier = P.boundaryCarrier g.carrier := by
  obtain ⟨_ | m, L, O⟩ := g <;> rfl

theorem boundaryOp_dim (g : OrTangent P) : (P.boundaryOp g).dim = g.dim - 1 := by
  obtain ⟨_ | m, L, O⟩ := g <;> rfl

theorem boundaryCarrier_eq {y : X} {L : Set P.TangentSpace}
    (hL : ∀ α ∈ L, P.levelVal 1 (P.tangentProj α) = y) :
    P.boundaryCarrier L = {α ∈ L | P.IsReducedVec y α} := by
  ext α
  refine and_congr_right fun hα => ?_
  unfold IsReducedTangent
  rw [hL α hα]

theorem isOutwardTangent_iff {y : X} {α : P.TangentSpace}
    (hα : P.levelVal 1 (P.tangentProj α) = y) : P.IsOutwardTangent α ↔ ¬ P.IsInwardVec y α := by
  unfold IsOutwardTangent
  rw [hα]

/-- The chart image of `T_y∂M` is `T_yM ∩ E_{φ(y)}`, read in the chart. -/
theorem PresentedChart.vec_image_boundaryCarrier {y : X} (c : P.PresentedChart y)
    {L : Set P.TangentSpace} (hL : ∀ α ∈ L, P.levelVal 1 (P.tangentProj α) = y) :
    c.vec '' P.boundaryCarrier L = c.vec '' L ∩ c.red := by
  rw [boundaryCarrier_eq hL]
  ext v
  constructor
  · rintro ⟨α, ⟨hα, hred⟩, rfl⟩
    exact ⟨⟨α, hα, rfl⟩, (isReducedVec_iff c (hL α hα)).1 hred⟩
  · rintro ⟨⟨α, hα, rfl⟩, hv⟩
    exact ⟨α, ⟨hα, (isReducedVec_iff c (hL α hα)).2 hv⟩, rfl⟩

variable (P) in
/-- **The situation of Definition 9.3.8** (`y ∈ ∂M` with `d_M(y) = 1`): `g` over `y` has reduced
codimension `1` and contains a vector of `C_yX ∖ T^R_yX`.  For `T_yM`, `M` any smooth
submanifold, the second condition follows from the first
(`isBoundaryAdmissible_of_submanifold`). -/
def IsBoundaryAdmissible (y : X) (g : OrTangent P) : Prop :=
  P.HasReducedCodim y 1 g ∧ ∃ s ∈ g.carrier, P.IsInwardVec y s ∧ ¬ P.IsReducedVec y s

/-- The chart description of an oriented tangent set and of its boundary carrier. -/
theorem IsOrientedAt.chartData {y : X} {d : ℕ} {L : Set P.TangentSpace}
    {O : Set (Fin d → P.TangentSpace)} (hO : P.IsOrientedAt y ⟨d, L, O⟩)
    (c : P.PresentedChart y) :
    ∃ N : Submodule ℝ (c.φ.model.E 0), (N : Set (c.φ.model.E 0)) = chartVec c.isChart '' L ∧
      span ℝ (c.vec '' L) = N ∧ FiniteDimensional ℝ N ∧ finrank ℝ N = d ∧
      ((N ⊓ c.red : Submodule ℝ (c.φ.model.E 0)) : Set (c.φ.model.E 0)) =
        chartVec c.isChart '' P.boundaryCarrier L := by
  obtain ⟨N, hN, hfin, hrank, -, -⟩ := hO.isChartOrientation c.isChart c.mem_source
  have hspan : span ℝ (c.vec '' L) = N := by
    change span ℝ (chartVec c.isChart '' L) = N
    rw [← hN, Submodule.span_eq]
  refine ⟨N, hN, hspan, hfin, hrank, ?_⟩
  change _ = c.vec '' P.boundaryCarrier L
  rw [c.vec_image_boundaryCarrier hO.1, Submodule.coe_inf]
  change _ = chartVec c.isChart '' L ∩ _
  rw [hN]

/-- **Two outward vectors differ by `e' = t e + k`, `t > 0`, `k ∈ T_y∂M`** (read in a chart), in
the situation of Definition 9.3.8. -/
theorem IsBoundaryAdmissible.exists_pos {y : X} {g : OrTangent P} (hO : P.IsOrientedAt y g)
    (hadm : P.IsBoundaryAdmissible y g) (c : P.PresentedChart y) {e e' : P.TangentSpace}
    (he : e ∈ g.carrier) (he' : e' ∈ g.carrier) (heo : ¬ P.IsInwardVec y e)
    (he'o : ¬ P.IsInwardVec y e') :
    ∃ t : ℝ, 0 < t ∧ c.vec e' - t • c.vec e ∈ span ℝ (c.vec '' g.carrier) ⊓ c.red := by
  obtain ⟨s, hs, hsin, hsred⟩ := hadm.2
  have hL := hO.1
  have hsN : c.vec s ∈ span ℝ (c.vec '' g.carrier) := subset_span (mem_image_of_mem _ hs)
  have heN : c.vec e ∈ span ℝ (c.vec '' g.carrier) := subset_span (mem_image_of_mem _ he)
  have he'N : c.vec e' ∈ span ℝ (c.vec '' g.carrier) := subset_span (mem_image_of_mem _ he')
  obtain ⟨t, ht, hmem⟩ := exists_pos_sub_mem_of_not_mem (S := c.cone)
    (fun a ha b hb => c.add_mem_cone ha hb) (fun t ht a ha => c.smul_mem_cone ht ha)
    c.red_subset_cone (fun a ha ha' => c.mem_red_of_mem_cone ha ha') (hadm.1 c) hsN
    ((isInwardVec_iff c (hL s hs)).1 hsin) (fun h => hsred ((isReducedVec_iff c (hL s hs)).2 h))
    heN he'N (fun h => heo ((isInwardVec_iff c (hL e he)).2 h))
    (fun h => he'o ((isInwardVec_iff c (hL e' he')).2 h))
  exact ⟨t, ht, Submodule.mem_inf.2 ⟨Submodule.sub_mem _ he'N (Submodule.smul_mem _ _ heN), hmem⟩⟩

/-- **Outward vectors exist** in the situation of Definition 9.3.8 (`−s` for an inward `s` off
`T^R_yX`). -/
theorem IsBoundaryAdmissible.exists_outward {y : X} {g : OrTangent P} (hO : P.IsOrientedAt y g)
    (hadm : P.IsBoundaryAdmissible y g) : ∃ e ∈ g.carrier, ¬ P.IsInwardVec y e := by
  obtain ⟨c⟩ := P.nonempty_presentedChart y
  obtain ⟨s, hs, hsin, hsred⟩ := hadm.2
  obtain ⟨N, hN, -⟩ := hO.isChartOrientation c.isChart c.mem_source
  have hsN : chartVec c.isChart s ∈ N := by rw [← SetLike.mem_coe, hN]; exact mem_image_of_mem _ hs
  have hneg : -chartVec c.isChart s ∈ (N : Set (c.φ.model.E 0)) := N.neg_mem hsN
  rw [hN] at hneg
  obtain ⟨e, he, hev⟩ := hneg
  refine ⟨e, he, fun hein => hsred ((isReducedVec_iff c (hO.1 s hs)).2 ?_)⟩
  have h1 := (isInwardVec_iff c (hO.1 e he)).1 hein
  change chartVec c.isChart e ∈ c.cone at h1
  rw [hev] at h1
  exact c.mem_red_of_mem_cone ((isInwardVec_iff c (hO.1 s hs)).1 hsin) h1

/-- **Definition 9.3.8 does not depend on the outward vector**: in its situation,
`boundaryOp (L, O)` is `(T_y∂M, boundaryFrames O (T_y∂M) e)` for *every* outward `e ∈ L`. -/
theorem boundaryOp_eq {y : X} {m : ℕ} {L : Set P.TangentSpace}
    {O : Set (Fin (m + 1) → P.TangentSpace)} (hO : P.IsOrientedAt y ⟨m + 1, L, O⟩)
    (hadm : P.IsBoundaryAdmissible y ⟨m + 1, L, O⟩) {e : P.TangentSpace} (he : e ∈ L)
    (heo : ¬ P.IsInwardVec y e) :
    P.boundaryOp ⟨m + 1, L, O⟩ =
      ⟨m, P.boundaryCarrier L, boundaryFrames O (P.boundaryCarrier L) e⟩ := by
  obtain ⟨c⟩ := P.nonempty_presentedChart y
  obtain ⟨N, -, hspan, hfin, hrank, hNK⟩ := hO.chartData c
  have hcod : quotDim N c.red = 1 := hspan ▸ hadm.1 c
  have hrankK : finrank ℝ ↥(N ⊓ c.red) = m := by
    have := finrank_inf_eq_of_quotDim_eq_one hcod
    omega
  have hKL : P.boundaryCarrier L ⊆ L := fun α hα => hα.1
  change (⟨m, P.boundaryCarrier L, _⟩ : OrTangent P) = _
  congr 1
  ext a
  constructor
  · rintro ⟨ha, hall⟩
    exact ⟨ha, hall e he ((isOutwardTangent_iff (hO.1 e he)).2 heo)⟩
  · rintro ⟨ha, hcons⟩
    refine ⟨ha, fun e' he' he'o => ?_⟩
    obtain ⟨t, ht, hmem⟩ := hadm.exists_pos hO c he he' heo
      ((isOutwardTangent_iff (hO.1 e' he')).1 he'o)
    rw [hspan] at hmem
    have h := boundaryFrames_eq hO hKL c.isChart c.mem_source (N ⊓ c.red) hNK hrankK he he' ht
      hmem
    have h2 : a ∈ boundaryFrames O (P.boundaryCarrier L) e' := by rw [h]; exact ⟨ha, hcons⟩
    exact h2.2

/-- **Definition 9.3.8 defines an orientation of `T_y∂M`**: in its situation, `boundaryOp g` is
an oriented tangent set over `y`, of dimension `dim g - 1` and carrier `T_y∂M`. -/
theorem isOrientedAt_boundaryOp {y : X} {g : OrTangent P} (hO : P.IsOrientedAt y g)
    (hadm : P.IsBoundaryAdmissible y g) : P.IsOrientedAt y (P.boundaryOp g) := by
  obtain ⟨d, L, O⟩ := g
  obtain ⟨c⟩ := P.nonempty_presentedChart y
  obtain ⟨N, -, hspan, hfin, hrank, hNK⟩ := hO.chartData c
  have hcod : quotDim N c.red = 1 := hspan ▸ hadm.1 c
  cases d with
  | zero =>
    exfalso
    have hN0 : N = ⊥ := Submodule.finrank_eq_zero.1 hrank
    rw [hN0, quotDim_bot_left] at hcod
    exact zero_ne_one hcod
  | succ m =>
    have hrankK : finrank ℝ ↥(N ⊓ c.red) = m := by
      have := finrank_inf_eq_of_quotDim_eq_one hcod
      omega
    obtain ⟨e, he, heo⟩ := hadm.exists_outward hO
    rw [boundaryOp_eq hO hadm he heo]
    refine isOrientedAt_boundaryFrames hO (fun α hα => hα.1) c.isChart c.mem_source (N ⊓ c.red)
      hNK hrankK he fun h => heo ((isInwardVec_iff c (hO.1 e he)).2 ?_)
    exact c.red_subset_cone (Submodule.mem_inf.1 h).2

/-- **For `T_yM`, `M` a smooth submanifold, reduced codimension `1` is the situation of
Definition 9.3.8**: the partial cone `C_yM` spans `T_yM` (`exists_sub_eq_vec_submanifoldTangent`),
so some vector of `C_yM` lies off `T^R_yM`. -/
theorem isBoundaryAdmissible_of_submanifold {A : Set X} (hA : P.IsSmoothSubmanifold A) {y : X}
    (hy : y ∈ A) {g : OrTangent P} (hO : P.IsOrientedAt y g)
    (hg : g.carrier = P.submanifoldTangent A y) (hcod : P.HasReducedCodim y 1 g) :
    P.IsBoundaryAdmissible y g := by
  refine ⟨hcod, ?_⟩
  obtain ⟨c⟩ := P.nonempty_presentedChart y
  have hnot : ¬ c.vec '' g.carrier ⊆ c.red := fun h => by
    have := hcod c
    rw [quotDim_eq_zero_of_le (span_le.2 h)] at this
    exact zero_ne_one this
  obtain ⟨_, ⟨α, hα, rfl⟩, hαred⟩ := not_subset.1 hnot
  rw [hg] at hα
  obtain ⟨β, hβ, γ, hγ, hβC, hγC, hsub⟩ := exists_sub_eq_vec_submanifoldTangent hA hy c hα
  rw [← hg] at hβ hγ
  by_cases hβred : c.vec β ∈ c.red
  · refine ⟨γ, hγ, (isInwardVec_iff c (hO.1 γ hγ)).2 hγC, fun h => hαred ?_⟩
    rw [hsub]
    exact c.red.sub_mem hβred ((isReducedVec_iff c (hO.1 γ hγ)).1 h)
  · exact ⟨β, hβ, (isInwardVec_iff c (hO.1 β hβ)).2 hβC,
      fun h => hβred ((isReducedVec_iff c (hO.1 β hβ)).1 h)⟩

/-- **`T_y∂M = T^R_yM`**: the chart image of the boundary carrier of `T_yA` is the reduced tangent
space `T^R_z Q = T_zQ ∩ E_z` (Definitions 2.27, 2.38) of the chart `Q = φ(W ∩ A)` of the induced
structure of `A` (same partial quadrant as `φ`). -/
theorem chartVec_image_boundaryCarrier {A : Set X} (hA : P.IsSmoothSubmanifold A) {y : X}
    (hy : y ∈ A) (c : P.PresentedChart y) (R : ScRetraction c.φ.model.E c.φ.model.C)
    (hR : R.retract = c.φ '' ((hA.data hy).toSubData.shrink c.φ ∩ A)) :
    chartVec c.isChart '' P.boundaryCarrier (P.submanifoldTangent A y) =
      (reducedTangentSpaceWith R c.T (levelLift c.φ 1 y) : Set (c.φ.model.E 0)) := by
  obtain ⟨himg, hzR⟩ := span_vec_submanifoldTangent hA hy c R hR
  have hyV := hA.mem_data_V hy
  have hy1 : y ∈ P.levelSet 1 := ((hA.data hy).mem_levelSet_one hy hyV)
  have hz : c.φ.model.E.toBase 1 (levelLift c.φ 1 y) = c.φ y :=
    P.toBase_levelLift c.isChart c.mem_source hy1
  change c.vec '' _ = _
  rw [c.vec_image_boundaryCarrier (fun α hα => hα.1), himg, reducedTangentSpaceWith,
    Submodule.coe_inf, hz]
  rfl

/-- **Outward means "not in `C_yM`"**: for `e ∈ T_yA`, `e` is outward iff its chart vector is not
in the partial cone `C_zQ = T_zQ ∩ C_z` (Definition 2.27) of the induced chart of `A`. -/
theorem isOutward_iff_not_mem_partialCone {A : Set X} (hA : P.IsSmoothSubmanifold A) {y : X}
    (hy : y ∈ A) (c : P.PresentedChart y) (R : ScRetraction c.φ.model.E c.φ.model.C)
    (hR : R.retract = c.φ '' ((hA.data hy).toSubData.shrink c.φ ∩ A)) {e : P.TangentSpace}
    (he : e ∈ P.submanifoldTangent A y) :
    P.IsOutwardTangent e ↔ chartVec c.isChart e ∉ partialConeWith R c.T (levelLift c.φ 1 y) := by
  obtain ⟨himg, hzR⟩ := span_vec_submanifoldTangent hA hy c R hR
  have hyV := hA.mem_data_V hy
  have hy1 : y ∈ P.levelSet 1 := ((hA.data hy).mem_levelSet_one hy hyV)
  have hz : c.φ.model.E.toBase 1 (levelLift c.φ 1 y) = c.φ y :=
    P.toBase_levelLift c.isChart c.mem_source hy1
  have hrange : chartVec c.isChart e ∈ range (scDeriv R.U R (levelLift c.φ 1 y)) := by
    have : c.vec e ∈ c.vec '' P.submanifoldTangent A y := mem_image_of_mem _ he
    rw [himg] at this
    obtain ⟨u, hu⟩ := this
    exact ⟨u, hu⟩
  rw [isOutwardTangent_iff he.1, isInwardVec_iff c he.1, partialConeWith, hz]
  exact not_congr ⟨fun h => ⟨hrange, h⟩, fun h => h.2⟩

/-- **Definition 9.3.8 for an oriented submanifold**: for `(M, o)` of dimension `m + 1` and
`y ∈ M` with `d_M(y) = 1` (reduced codimension `1` of `T_yM`; for tame `M` this is
`subDegIndex = 1`, `subDegIndex_eq_quotDim_span`), `T_y(∂M, o_{∂M}) = boundaryOp (T_y(M, o))` is an
orientation of `T_y∂M`, given by `boundaryFrames o_y (T_y∂M) e` for every outward `e`. -/
theorem SubmanifoldOrientation.boundaryOp_tangent {A : Set X} {m : ℕ}
    (o : P.SubmanifoldOrientation A (m + 1)) (hA : P.IsSmoothSubmanifold A) {y : X} (hy : y ∈ A)
    (hcod : P.HasReducedCodim y 1 (o.tangent y)) :
    P.IsOrientedAt y (P.boundaryOp (o.tangent y)) ∧
      (P.boundaryOp (o.tangent y)).carrier = P.boundaryCarrier (P.submanifoldTangent A y) ∧
      (∃ e ∈ P.submanifoldTangent A y, P.IsOutwardTangent e) ∧
      ∀ e ∈ P.submanifoldTangent A y, P.IsOutwardTangent e →
        P.boundaryOp (o.tangent y) = ⟨m, P.boundaryCarrier (P.submanifoldTangent A y),
          boundaryFrames (o.frames y) (P.boundaryCarrier (P.submanifoldTangent A y)) e⟩ := by
  have hO := o.isOrientedAt_tangent hy
  have hadm := isBoundaryAdmissible_of_submanifold hA hy hO rfl hcod
  refine ⟨isOrientedAt_boundaryOp hO hadm, boundaryOp_carrier _, ?_, fun e he heo =>
    boundaryOp_eq hO hadm he ((isOutwardTangent_iff he.1).1 heo)⟩
  obtain ⟨e, he, heo⟩ := hadm.exists_outward hO
  exact ⟨e, he, (isOutwardTangent_iff he.1).2 heo⟩

/-- The same for tame `M`, with the text's `d_M(y) = 1`. -/
theorem SubmanifoldOrientation.boundaryOp_tangent_of_tame {A : Set X} {m : ℕ}
    (o : P.SubmanifoldOrientation A (m + 1)) (hA : P.IsSmoothSubmanifold A)
    (ht : P.HasTameInducedStructure A) {y : X} (hy : y ∈ A)
    (hd : P.subDegIndex hA.isSubMPolyfold ⟨y, hy⟩ = 1) :
    P.IsOrientedAt y (P.boundaryOp (o.tangent y)) ∧
      (P.boundaryOp (o.tangent y)).carrier = P.boundaryCarrier (P.submanifoldTangent A y) ∧
      (∃ e ∈ P.submanifoldTangent A y, P.IsOutwardTangent e) ∧
      ∀ e ∈ P.submanifoldTangent A y, P.IsOutwardTangent e →
        P.boundaryOp (o.tangent y) = ⟨m, P.boundaryCarrier (P.submanifoldTangent A y),
          boundaryFrames (o.frames y) (P.boundaryCarrier (P.submanifoldTangent A y)) e⟩ :=
  o.boundaryOp_tangent hA hy fun c => by
    rw [SubmanifoldOrientation.tangent_carrier, ← subDegIndex_eq_quotDim_span hA ht hy c]
    exact hd

/-- **Every tangent set `T_yA` of a smooth submanifold has an orientation** (Remark 4.14: its chart
image is a finite-dimensional subspace). -/
theorem exists_isOrientedAt_submanifoldTangent {A : Set X} (hA : P.IsSmoothSubmanifold A) {y : X}
    (hy : y ∈ A) : ∃ (n : ℕ) (O : Set (Fin n → P.TangentSpace)),
      P.IsOrientedAt y ⟨n, P.submanifoldTangent A y, O⟩ := by
  obtain ⟨c⟩ := P.nonempty_presentedChart y
  have hyV := hA.mem_data_V hy
  have hy1 : y ∈ P.levelSet 1 := ((hA.data hy).mem_levelSet_one hy hyV)
  have hz : c.φ.model.E.toBase 1 (levelLift c.φ 1 y) = c.φ y :=
    P.toBase_levelLift c.isChart c.mem_source hy1
  obtain ⟨-, -, -, N, hN, hfin⟩ := (hA.data hy).remark_4_14 c.isChart hy hyV c.mem_source hz
  rw [← chartVec_image_submanifoldTangent c.isChart (hA.data hy) hy hyV c.mem_source] at hN
  obtain ⟨O₁, O₂, -, hO⟩ := exists_two_orientations c.isChart c.mem_source (fun α hα => hα.1) hN
    (n := finrank ℝ N) rfl
  exact ⟨_, O₁, (hO O₁).2 (Or.inl rfl)⟩

/-- **Satisfiability of Definition 9.3.8 in this form**: at the corner `0` of the half-line
`[0, ∞)` (`d_M(0) = 1` for `M = [0, ∞)`, a tame submanifold of itself), every orientation of
`T_0M` is in the situation of Definition 9.3.8, and `boundaryOp` gives an orientation of
`T_0∂M`. -/
theorem exists_isBoundaryAdmissible_halfLine :
    ∃ g : OrTangent (quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))),
      (quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))).IsOrientedAt halfLineCorner g ∧
      g.carrier = (quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))).submanifoldTangent univ
        halfLineCorner ∧
      (quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))).IsBoundaryAdmissible halfLineCorner g ∧
      (quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))).IsOrientedAt halfLineCorner
        ((quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))).boundaryOp g) := by
  set Q := quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))
  have hA : Q.IsSmoothSubmanifold univ := halfLine_hasCornerStructure.isSmoothSubmanifold_univ
  have ht : Q.HasTameInducedStructure univ :=
    hasTameInducedStructure_univ _ (quadrantPolyfold_isTame 1 _)
  have hy : halfLineCorner ∈ (univ : Set (quadrant 1 (ScBanach.const (Fin 0 → ℝ)) 0)) :=
    mem_univ _
  have hd : Q.subDegIndex hA.isSubMPolyfold ⟨halfLineCorner, hy⟩ = 1 := by
    refine le_antisymm ?_ ((mem_submanifoldBoundary_iff_subDegIndex hA hy).1
      halfLineCorner_mem_submanifoldBoundary)
    refine (subDegIndex_le _ _).trans (le_of_eq ?_)
    exact quadrantPolyfold_degIndex_zero 1 _
  obtain ⟨n, O, hO⟩ := exists_isOrientedAt_submanifoldTangent hA hy
  have hcod : Q.HasReducedCodim halfLineCorner 1 ⟨n, Q.submanifoldTangent univ halfLineCorner, O⟩ :=
    fun c => by
      change quotDim (span ℝ (c.vec '' Q.submanifoldTangent univ halfLineCorner)) c.red = 1
      rw [← subDegIndex_eq_quotDim_span hA ht hy c, hd]
  have hadm := isBoundaryAdmissible_of_submanifold hA hy hO rfl hcod
  exact ⟨_, hO, rfl, hadm, isOrientedAt_boundaryOp hO hadm⟩

end MPolyfold

/-! ### Definition 9.3.10 and Proposition 9.3.9 with the boundary operation -/

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
variable {Θ : Obj → ℚ}

variable (X) in
open scoped Classical in
/-- **The part of reduced codimension `ℓ`** of an element of `Gr̂(X)` at `y`: the terms whose
oriented tangent set has `dim(L / L ∩ T^R_yX) = ℓ` (for tame `Mᵢ`, `d_{Mᵢ}(y) = ℓ`). -/
def reducedCodimPart (y : Obj) (ℓ : ℕ) (w : X.PObj.OrTangent →₀ ℚ) : X.PObj.OrTangent →₀ ℚ :=
  w.filter (X.PObj.HasReducedCodim y ℓ)

variable (X) in
/-- **`T̂_{∂Θ}` of (9.12), Definition 9.3.10** (2021 p. 428; 2017: Definition 9.11), with the
boundary operation of Definition 9.3.8 built from the submanifolds (`boundaryOp`) and the degree
read as the reduced codimension: `T̂_{∂Θ}(y) = ∑_{d_{Mᵢ}(y) = 1} σᵢ T_y(∂Mᵢ, o_{∂Mᵢ})`.  It is a
function of `T̂_Θ(y)`, so it does not depend on any structure; it agrees with Chapter 9's
`boundaryLift X.PObj.boundaryOp` for oriented tame `Θ̂`
(`boundaryLift_boundaryOp_eq_boundaryOrientation`). -/
def boundaryOrientation (T : Obj → X.PObj.OrTangent →₀ ℚ) (y : Obj) : X.PObj.OrTangent →₀ ℚ :=
  (X.reducedCodimPart y 1 (T y)).mapDomain X.PObj.boundaryOp

variable (X) in
/-- **An oriented tame `Θ̂`** (the hypothesis of Definition 9.3.10, 2021 p. 427): every
`x ∈ supp(Θ)` has an oriented local branching structure with tame `Mᵢ` (Definition 9.3.6)
representing `T̂_Θ` near `x`.  Witnesses: `isTameOrientation_zero`,
`isTameOrientation_of_degIndex_eq_zero` (no boundary, e.g. `ℝⁿ`). -/
def IsTameOrientation (Θ : Obj → ℚ) (T : Obj → X.PObj.OrTangent →₀ ℚ) : Prop :=
  ∀ x ∈ supp Θ, ∃ B : X.OrientedBranchingStructure Θ x,
    (∀ i, X.PObj.HasTameInducedStructure (B.M i)) ∧
      ∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = B.orientedSum y

theorem isTameOrientation_zero : X.IsTameOrientation 0 0 := fun _ hx =>
  (lt_irrefl (0 : ℚ) hx).elim

/-- Without boundary (`d_X ≡ 0`, e.g. `ℝⁿ`) every orientation is tame
(`hasTameInducedStructure_of_degIndex_eq_zero`). -/
theorem isTameOrientation_of_degIndex_eq_zero (h0 : ∀ a, X.PObj.degIndex a = 0)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T) : X.IsTameOrientation Θ T :=
  fun x hx => by
    obtain ⟨B, hB⟩ := hT.locallyOriented x hx
    exact ⟨B, fun i => hasTameInducedStructure_of_degIndex_eq_zero (B.isSmoothSubmanifold i)
      fun a _ => h0 a, hB⟩

open scoped Classical in
/-- The reduced-codimension-`ℓ` part of `∑ σᵢ T_y(Mᵢ, oᵢ)` (any oriented structure). -/
theorem reducedCodimPart_orientedSum {x : Obj} (B : X.OrientedBranchingStructure Θ x) (y : Obj)
    (ℓ : ℕ) :
    X.reducedCodimPart y ℓ (B.orientedSum y) =
      ∑ i with y ∈ B.M i ∧ X.PObj.HasReducedCodim y ℓ ((B.orient i).tangent y),
        Finsupp.single ((B.orient i).tangent y) (B.σ i) := by
  rw [reducedCodimPart, OrientedBranchingStructure.orientedSum, Finsupp.filter_sum,
    Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hy : y ∈ B.M i
  · rw [if_pos hy]
    by_cases hd : X.PObj.HasReducedCodim y ℓ ((B.orient i).tangent y)
    · rw [if_pos ⟨hy, hd⟩, Finsupp.filter_single_of_pos _ hd]
    · rw [if_neg fun h => hd h.2, Finsupp.filter_single_of_neg _ hd]
  · rw [if_neg hy, if_neg fun h => hy h.1]

/-- **Chapter 9's degree-`ℓ` part is the reduced-codimension-`ℓ` part** for oriented tame `Θ̂`
(Lemma 9.3.7's proof: `d_{Mᵢ}(y) = dim(T_yMᵢ / T^R_yMᵢ)`). -/
theorem degreePart_eq_reducedCodimPart {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsOrientation Θ T) (htame : X.IsTameOrientation Θ T) {y : Obj}
    (hys : y ∈ X.PObj.smoothSet) (ℓ : ℕ) :
    X.degreePart y ℓ (T y) = X.reducedCodimPart y ℓ (T y) := by
  classical
  by_cases hy : y ∈ supp Θ
  · obtain ⟨B, hBt, hB⟩ := htame y hy
    rw [hB y B.mem_U hys, degreePart_orientedSum B hBt, reducedCodimPart_orientedSum]
    refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
    constructor
    · rintro ⟨hyi, hd⟩
      refine ⟨hyi, fun c => ?_⟩
      rw [SubmanifoldOrientation.tangent_carrier, ← subDegIndex_eq_quotDim_span
        (B.isSmoothSubmanifold i) (hBt i) hyi c, hd]
    · rintro ⟨hyi, hd⟩
      obtain ⟨c⟩ := X.PObj.nonempty_presentedChart y
      refine ⟨hyi, ?_⟩
      rw [subDegIndex_eq_quotDim_span (B.isSmoothSubmanifold i) (hBt i) hyi c]
      exact hd c
  · rw [hT.eq_zero_of_not_mem hys hy, degreePart, reducedCodimPart, Finsupp.filter_zero,
      Finsupp.filter_zero]

/-- **Definition 9.3.10 with the boundary operation of Definition 9.3.8**: for oriented tame
`Θ̂`, Chapter 9's `T̂_{∂Θ} = boundaryLift bd T̂_Θ` with `bd = boundaryOp` is the intrinsic
`boundaryOrientation` (on `X_∞`). -/
theorem boundaryLift_boundaryOp_eq_boundaryOrientation {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsOrientation Θ T) (htame : X.IsTameOrientation Θ T) {y : Obj}
    (hys : y ∈ X.PObj.smoothSet) :
    X.boundaryLift X.PObj.boundaryOp T y = X.boundaryOrientation T y := by
  rw [boundaryLift, boundaryOrientation, degreePart_eq_reducedCodimPart hT htame hys]

open scoped Classical in
/-- **Proposition 9.3.9, 2021 p. 428 (new in the 2021 edition), for `boundaryOrientation`**:
`T̂_{∂Θ}` vanishes on `X_∞ ∖ supp(Θ)`, and on `U(x)` it is (9.12),
`∑_{d_{Mᵢ}(y) = 1} σᵢ · T_y(∂Mᵢ, o_{∂Mᵢ})`, for every oriented branching structure representing
`T̂_Θ` there; each term `T_y(∂Mᵢ, o_{∂Mᵢ}) = boundaryOp (T_y(Mᵢ, oᵢ))` is an orientation of
`T_y∂Mᵢ = T^R_yMᵢ` given by Definition 9.3.8 with any outward vector
(`SubmanifoldOrientation.boundaryOp_tangent`). -/
theorem proposition_9_3_9_boundaryOrientation {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsOrientation Θ T) :
    (∀ y ∈ X.PObj.smoothSet, y ∉ supp Θ → X.boundaryOrientation T y = 0) ∧
    ∀ (x : Obj) (B : X.OrientedBranchingStructure Θ x),
      (∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = B.orientedSum y) →
      ∀ y ∈ B.U, y ∈ X.PObj.smoothSet →
        X.boundaryOrientation T y =
          ∑ i with y ∈ B.M i ∧ X.PObj.HasReducedCodim y 1 ((B.orient i).tangent y),
            Finsupp.single (X.PObj.boundaryOp ((B.orient i).tangent y)) (B.σ i) := by
  refine ⟨fun y hy hys => ?_, fun x B hB y hy hys => ?_⟩
  · rw [boundaryOrientation, hT.eq_zero_of_not_mem hy hys, reducedCodimPart, Finsupp.filter_zero,
      Finsupp.mapDomain_zero]
  · rw [boundaryOrientation, hB y hy hys, reducedCodimPart_orientedSum,
      Finsupp.mapDomain_finsetSum]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_single

open scoped Classical in
/-- **Proposition 9.3.9 with the boundary operation of Definition 9.3.8** (no data hypothesis):
Chapter 9's `proposition_9_3_9` for `bd = boundaryOp`. -/
theorem proposition_9_3_9_boundaryOp {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsOrientation Θ T) :
    (∀ y ∈ X.PObj.smoothSet, y ∉ supp Θ → X.boundaryLift X.PObj.boundaryOp T y = 0) ∧
    ∀ (x : Obj) (B : X.OrientedBranchingStructure Θ x),
      (∀ i, X.PObj.HasTameInducedStructure (B.M i)) →
      (∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = B.orientedSum y) →
      ∀ y ∈ B.U, y ∈ X.PObj.smoothSet →
        X.boundaryLift X.PObj.boundaryOp T y = ∑ i with ∃ hy : y ∈ B.M i,
            X.PObj.subDegIndex (B.isSmoothSubmanifold i).isSubMPolyfold ⟨y, hy⟩ = 1,
          Finsupp.single (X.PObj.boundaryOp ((B.orient i).tangent y)) (B.σ i) :=
  proposition_9_3_9 X.PObj.boundaryOp hT

end EpGroupoid

end Polyfold
