import Polyfold.Chapter9.Tangent
import Polyfold.Chapter9.BoundaryPositionConverse

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.2 "The Tangent and Boundary of Θ": **Proposition 9.2.15** (pp. 420–421;
2017: Proposition 9.4, pp. 308–309), **Definition 9.2.16** (p. 421; 2017: Definition 9.7,
pp. 309–310) and **Remark 9.2.17** (p. 421; 2017: Remark 9.6, p. 310).  Numbers and pages are the
2021 text's, the 2017 ones in parentheses.

# The boundary `∂Θ` of a branched ep⁺-subgroupoid

## The text, paraphrased

(Proposition 9.2.15, "well-definedness of `∂Θ`") For a branched ep⁺-subgroupoid `Θ`, a point
`x ∈ supp(Θ) ∩ ∂X` and two local branching structures `(Mᵢ, σᵢ)`, `(N_j, τ_j)` on `U(x)`:
(1) `∑_{i : y ∈ ∂Mᵢ} σᵢ = ∑_{j : y ∈ ∂N_j} τ_j` for `y ∈ U(x)` (9.8); (2) these sums vanish where
`d_X(y) = 0`; (3) there is a functor `∂Θ : X → ℚ⁺` with `supp(∂Θ) ⊆ ∂X` and, for
`x ∈ supp(∂Θ)` and any local branching structure on `U(x)`,
`∂Θ(y) = ∑_{i : y ∈ Mᵢ, d_{Mᵢ}(y) ≥ 1} σᵢ` on `U(x)`.  The proof of (1) splits
`TΘ(y) = ∑ σᵢ · T_yMᵢ` (independent of the structure) into the parts with `d_{Mᵢ}(y) ≥ 1` and
`= 0`, a natural decomposition by Lemma 9.2.13 and the remark after it; for (2) all `d_{Mᵢ}`
vanish near a point with `d_X = 0`; (3) follows from (1), (2).

(Definition 9.2.16) The functor `∂Θ`, "uniquely characterized" by (1) `supp(∂Θ) ⊆ ∂X` and (2) the
formula of (3) for `x ∈ supp(∂Θ)` and any local branching structure on `U(x)`, is the boundary
of `Θ`.

(Remark 9.2.17) `∂Θ` need not have nice properties; for the tame branched ep⁺-subgroupoids of
Definition 9.3.6 the boundaries are nice enough for integration and orientation.

## Main declarations

* `MPolyfold.submanifoldBoundary` (`∂M ⊆ X`: the points with `d_M ≥ 1` for the induced
  structure, `subDegIndex`), read through Remark 9.2.14 (`remark_9_2_14_iff`):
  `MPolyfold.mem_submanifoldBoundary_iff` (`y ∈ ∂M ⟺ y ∈ M ∧ y ∈ ∂X ∧ T_yM ⊄ T_y^R X`), with
  `mem_submanifoldBoundary_inter_isOpen_iff` (germs) and `mem_submanifoldBoundary_image_iff`
  (sc-diffeomorphisms).
* **The sets `T_yM` compared in `TX`**: `MPolyfold.IsTangentReducedAt.of_submanifoldTangent_subset`
  and `isTangentReducedAt_iff_of_submanifoldTangent_eq` (`T_yM ⊆ T_y^R X` depends only on the set
  `T_yM ⊆ TX`, via the chart description
  `SubmanifoldData.tangentChartMap_of_mem_submanifoldTangent`,
  `SubmanifoldData.exists_mem_submanifoldTangent`), `MPolyfold.IsReducedTangentSet` (the property
  of a tangent set `L`), `isReducedTangentSet_iff`; transport: `IsTangentReducedAt.image`,
  `isTangentReducedAt_image_iff`.
* **Definition 9.2.16**: `EpGroupoid.boundaryTheta` (`∂Θ(y)` is the part `boundaryPart` of the
  formal sum `TΘ(y)` on the tangent sets `L ⊄ T_y^R X`, for `y ∈ ∂X`; `0` off `∂X`), with the local
  formula `boundaryTheta_eq` for every local branching structure and every `y ∈ U(x)`.
* **Proposition 9.2.15**: `EpGroupoid.proposition_9_2_15_1`, `proposition_9_2_15_2`,
  `proposition_9_2_15_3` (functor `isFunctorial_boundaryTheta`, `∂Θ ≥ 0`, `supp(∂Θ) ⊆ ∂X`, the
  local formula), and the natural decomposition of the proof, `filter_tangentValue_eq`.
* The characterization of Definition 9.2.16: `IsBoundaryCharacterized`,
  `isBoundaryCharacterized_boundaryTheta`, `isBoundaryCharacterized_zero`,
  `boundaryTheta_eq_zero_of_unique`, `eq_boundaryTheta`,
  `not_unique_isBoundaryCharacterized_halfLine`.
* Remark 9.2.17: `boundaryTheta_le` (`∂Θ ≤ Θ`) and `boundaryTheta_halfLineCorner` (`∂Θ` is not
  `Θ` restricted to `∂X`).
* **Witnesses**, all branched ep⁺-subgroupoids with independent tangent sums in a trivial
  ep-groupoid: the indicator of a smooth point of any M-polyfold (`isSmoothSubmanifold_singleton`,
  `isTangentReducedAt_singleton`: `T_p{p} ⊆ T_p^R X`, so `∂Θ = 0`,
  `boundaryTheta_indicator_of_mem`), at the corner `0` of the half-line `[0, ∞)`
  (`boundaryTheta_halfLineCorner`: `0 ∈ ∂X ∩ supp(Θ)`, `Θ(0) = 1`, `∂Θ(0) = 0`), and `Θ = 1` on
  `[0, ∞)` (`boundaryTheta_halfLine_one`: `∂Θ(0) = 1`, from
  `HasCornerStructure.isSmoothSubmanifold_univ` and `halfLineCorner_mem_submanifoldBoundary`,
  `T_0[0, ∞) = ℝ ⊄ T_0^R X = {0}`).  The ℝⁿ point indicator: `boundaryTheta_indicator`,
  `proposition_9_2_15_3_indicator`.

## What the text leaves implicit, and the choices made

* The independence of `TΘ(y) = ∑ σᵢ · T_yMᵢ` from the local branching structure (Theorem 9.2.1) is
  the hypothesis `HasIndependentTangentSums`, as in `Tangent.lean` (`theorem_9_2_1`); every
  witness here discharges it (`hasIndependentTangentSums_of_subset_goodSet`).
* "`y ∈ ∂Mᵢ`" is `y ∈ Mᵢ` with `d_{Mᵢ}(y) ≥ 1` for the induced M-polyfold structure of `Mᵢ`
  (Proposition 2.21), the reading of (3) and Definition 9.2.16 (2), and is used through Remark
  9.2.14: `y ∈ ∂X` and `T_yMᵢ ⊄ T_y^R X`.
* `TΘ(y)` is a formal sum of tangent sets `T_yMᵢ ⊆ TX` (`Tangent.lean`), so the splitting of the
  proof of (1) needs "`T_yMᵢ ⊆ T_y^R X`" as a property of the set `T_yMᵢ`: two submanifolds through
  `y` with the same tangent set are both reduced or both not (`isReducedTangentSet_iff`).
* `∂Θ` is defined intrinsically from `TΘ`, without a choice of local branching structure; the local
  formula holds on every `U(x)`, not only for `x ∈ supp(∂Θ)`.  For (1) and (2) the hypotheses
  `x ∈ supp(Θ) ∩ ∂X` and "`Θ` branched" are not needed, and (2) needs no independence
  (`d_{Mᵢ} ≤ d_X`, Lemma 2.26).
* `ℚ⁺` is `ℚ_{≥ 0}` and functors to `ℚ` are `IsFunctorial`, as in `Basic.lean`.

## Statements that do not hold as we read them

* Definition 9.2.16's "uniquely characterized": (1), (2) as printed are satisfied by `F = 0` for
  every `Θ` (`supp(0) = ∅`, so (2) is vacuous, `isBoundaryCharacterized_zero`); they determine
  `∂Θ` only when `∂Θ = 0` (`boundaryTheta_eq_zero_of_unique`), and for `Θ = 1` on `[0, ∞)` they do
  not (`not_unique_isBoundaryCharacterized_halfLine`).  `∂Θ` is unique among the `F` that vanish
  off `supp(Θ)` and satisfy (2) at the points of `supp(Θ)` (`eq_boundaryTheta`); at points of
  `cl(supp(Θ)) ∖ supp(Θ)` no local branching structure is given, so the vanishing off `supp(Θ)` is
  needed as a separate condition.

## Possible misprints

* "In view of Proposition 9.2.13" before Definition 9.2.16 (2017: "Proposition 9.9"): `9.2.13` is
  Lemma 9.2.13 (2017: Lemma 9.9); the definition rests on Proposition 9.2.15, presumably meant.
* Definition 9.2.16 (also 2017): "a branched ep⁺-groupoid" for "a branched ep⁺-subgroupoid".
* Remark 9.2.17 (also 2017): "In Section 9.5, Definition 9.3.6" (2017: "Definition 9.10"); the
  definition is in §9.3 "Orientations" (pp. 425–426), presumably Section 9.3.

## Not formalized

* Remark 9.2.17 has no formal content beyond `boundaryTheta_le` and `boundaryTheta_halfLineCorner`;
  its forward reference is Definition 9.3.6 (`BoundaryPosition.lean`).
* Theorem 9.2.1's independence for every branched ep⁺-subgroupoid is not used (a hypothesis).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

namespace SubmanifoldData

variable {A : Set X} (d : P.SubmanifoldData A) {φ : MChart X} (hφ : P.IsChart φ)
include hφ

/-- Locality: `T(φ ∘ s ∘ φ⁻¹)` computed on `φ(V ∩ dom φ ∩ s⁻¹(dom φ))` agrees with the one
computed on `φ(W)`, `W = V ∩ dom φ ∩ s⁻¹(V ∩ dom φ)` (the set of Remark 4.14), on `T(φ(W))`. -/
theorem retractTangentMap_fdomOn_eq {a : φ.model.E.tangent 0}
    (ha : a ∈ retractTangent φ.model.E φ.model.C (φ '' d.toSubData.shrink φ)) :
    retractTangentMap φ.model.E φ.model.C (φ '' TangentPre.fdomOn d.V φ d.s φ)
        (φ ∘ d.s ∘ φ.symm) a =
      retractTangentMap φ.model.E φ.model.C (φ '' d.toSubData.shrink φ) (φ ∘ d.s ∘ φ.symm) a := by
  have hs := d.isScPlusRetractionOn.isScSmoothOn
  have hWo := TangentPre.isOpen_fdomOn hs φ φ
  have hWsub := TangentPre.fdomOn_subset d.V φ d.s φ
  have hsub : d.toSubData.shrink φ ⊆ TangentPre.fdomOn d.V φ d.s φ :=
    fun x hx => ⟨⟨hx.1.1, hx.1.2⟩, hx.2.2⟩
  obtain ⟨K, hK, hKeq⟩ := φ.exists_isOpen_image_eq (d.toSubData.shrink_subset_source φ)
    (d.toSubData.isOpen_shrink φ)
  have heq : φ '' d.toSubData.shrink φ = φ '' TangentPre.fdomOn d.V φ d.s φ ∩ K := by
    have := φ.image_inter_eq_inter (B := univ) hWsub hsub hKeq
    simpa only [inter_univ] using this
  have hf := TangentPre.isScSmoothRetractMap_coordOn hs hφ hφ subset_rfl hWo
  have hO := φ.isScRetract_image hWsub hWo
  rw [heq] at ha ⊢
  exact (retractTangentMap_inter_isOpen hf hO hK ha).symm

/-- **`Ts` in the chart `φ`**: for `α` over `y ∈ A ∩ V ∩ dom φ`,
`Tφ(Ts α) = T(φ ∘ s ∘ φ⁻¹)(Tφ α)` (formula (5) for `s`, computed on the set of Remark 4.14). -/
theorem tangentChartMap_tmap_shrink {α : P.TangentSpace} {y : X} (hyA : y ∈ A) (hyV : y ∈ d.V)
    (hyφ : y ∈ φ.source) (hα : P.levelVal 1 (P.tangentProj α) = y) :
    tangentChartMap hφ (d.tmap α) =
      retractTangentMap φ.model.E φ.model.C (φ '' d.toSubData.shrink φ) (φ ∘ d.s ∘ φ.symm)
        (tangentChartMap hφ α) := by
  have hsy : d.s y = y := d.apply_eq_self ⟨hyA, hyV⟩
  have hαW : α ∈ P.tangentPreimage (TangentPre.fdomOn d.V φ d.s φ) := by
    change P.levelVal 1 (P.tangentProj α) ∈ TangentPre.fdomOn d.V φ d.s φ
    rw [hα]
    exact ⟨⟨hyV, hyφ⟩, show d.s y ∈ φ.source from hsy.symm ▸ hyφ⟩
  rw [tmap, tangentChartMap_tangentMapOn _ hφ hφ hαW]
  apply d.retractTangentMap_fdomOn_eq hφ
  have hαφ : α ∈ tangentChartSet φ := by change _ ∈ φ.source; rw [hα]; exact hyφ
  refine (TangentPre.mem_retractTangent_image_iff (d.toSubData.shrink_subset_source φ)
    (d.toSubData.isOpen_shrink φ) ?_).2 (tangentChartMap_mem hφ hαφ)
  rw [tangentChartMap_fst hφ hαφ, P.toBase_levelLift hφ hαφ (levelVal_mem _), hα]
  exact ⟨y, d.toSubData.mem_shrink φ hyA hyV hyφ, rfl⟩

/-- **The chart description of `T_yA`, one inclusion**: for `α ∈ T_yA`,
`Tφ(α) = (z, h)` with `z` the level-`1` lift of `φ(y)` and `h ∈ T_z(φ(W ∩ A))`. -/
theorem tangentChartMap_of_mem_submanifoldTangent {α : P.TangentSpace} {y : X} (hyA : y ∈ A)
    (hyV : y ∈ d.V) (hyφ : y ∈ φ.source) (hα : α ∈ P.submanifoldTangent A y) :
    (tangentChartMap hφ α).1 = levelLift φ 1 y ∧
      (tangentChartMap hφ α).2 ∈
        tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) (levelLift φ 1 y) := by
  obtain ⟨hαy, hfix⟩ := (mem_submanifoldTangent_iff d hyV).1 hα
  have hαφ : α ∈ tangentChartSet φ := by change _ ∈ φ.source; rw [hαy]; exact hyφ
  have h1 : (tangentChartMap hφ α).1 = levelLift φ 1 y := by rw [tangentChartMap_fst hφ hαφ, hαy]
  refine ⟨h1, ?_⟩
  have hy1 : y ∈ P.levelSet 1 := d.mem_levelSet_one hyA hyV
  have hz : φ.model.E.toBase 1 (levelLift φ 1 y) = φ y := P.toBase_levelLift hφ hyφ hy1
  obtain ⟨-, h2, -⟩ := d.remark_4_2_2 hφ hyA hyV hyφ hz
  rw [← h2]
  have hmem := tangentChartMap_mem hφ hαφ
  have hv : tangentChartMap hφ α = (levelLift φ 1 y, (tangentChartMap hφ α).2) := Prod.ext h1 rfl
  refine ⟨(tangentChartMap hφ α).2, ?_, ?_⟩
  · have : ((levelLift φ 1 y, (tangentChartMap hφ α).2) : φ.model.E.tangent 0) ∈
        retractTangent φ.model.E φ.model.C φ.model.O := hv ▸ hmem
    exact this
  · have h3 := d.tangentChartMap_tmap_shrink hφ hyA hyV hyφ hαy
    rw [hfix] at h3
    beta_reduce
    rw [← hv, ← h3]

/-- **The chart description of `T_yA`, the other inclusion**: every `h ∈ T_z(φ(W ∩ A))` is the
second component of `Tφ(α)` for some `α ∈ T_yA`. -/
theorem exists_mem_submanifoldTangent {y : X} (hyA : y ∈ A) (hyV : y ∈ d.V) (hyφ : y ∈ φ.source)
    {h : φ.model.E 0}
    (hh : h ∈ tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A))
      (levelLift φ 1 y)) :
    ∃ α ∈ P.submanifoldTangent A y, tangentChartMap hφ α = (levelLift φ 1 y, h) := by
  have hy1 : y ∈ P.levelSet 1 := d.mem_levelSet_one hyA hyV
  have hz : φ.model.E.toBase 1 (levelLift φ 1 y) = φ y := P.toBase_levelLift hφ hyφ hy1
  obtain ⟨-, h2, -⟩ := d.remark_4_2_2 hφ hyA hyV hyφ hz
  rw [← h2] at hh
  obtain ⟨h', hh', rfl⟩ := hh
  have ha' : ((levelLift φ 1 y, h') : φ.model.E.tangent 0) ∈
      retractTangent φ.model.E φ.model.C φ.model.O := hh'
  set α' := TangentSpace.mk (TangentPre.ofVec hφ ha') with hα'def
  have hα'y : P.levelVal 1 (P.tangentProj α') = y := by
    rw [hα'def, tangentProj_mk, TangentPre.ofVec_x]
    change φ.symm (φ.model.E.toBase 1 (levelLift φ 1 y)) = y
    rw [hz, φ.symm_apply_apply hyφ]
  have hα'V : α' ∈ P.tangentPreimage d.V := by change _ ∈ d.V; rw [hα'y]; exact hyV
  have hsy : d.s y = y := d.apply_eq_self ⟨hyA, hyV⟩
  have hbase : P.levelVal 1 (P.tangentProj (d.tmap α')) = y := by
    rw [d.levelVal_tangentProj_tmap hα'V, hα'y, hsy]
  refine ⟨d.tmap α', (mem_submanifoldTangent_iff d hyV).2 ⟨hbase, ?_⟩, ?_⟩
  · have hs := d.isScPlusRetractionOn.isScSmoothOn
    exact tangentMapOn_tangentMapOn_eq hs hs hs d.isOpen subset_rfl subset_rfl
      d.isScPlusRetractionOn.mapsTo (fun x hx => d.isScPlusRetractionOn.idem x hx) hα'V
  · have hφ' : d.tmap α' ∈ tangentChartSet φ := by change _ ∈ φ.source; rw [hbase]; exact hyφ
    refine Prod.ext ?_ ?_
    · rw [tangentChartMap_fst hφ hφ', hbase]
    · rw [d.tangentChartMap_tmap_shrink hφ hyA hyV hyφ hα'y, tangentChartMap_mk_ofVec]

end SubmanifoldData

/-- **The chart form of `T_yA ⊆ T_yA'`**: an inclusion of the tangent sets in `TX` gives the
inclusion of the chart tangent spaces `T_z(φ(W ∩ A)) ⊆ T_z(φ(W' ∩ A'))`. -/
theorem tangentSpace_subset_of_submanifoldTangent_subset {A A' : Set X}
    (d : P.SubmanifoldData A) (d' : P.SubmanifoldData A') {φ : MChart X} (hφ : P.IsChart φ)
    {y : X} (hyA : y ∈ A) (hyV : y ∈ d.V) (hyA' : y ∈ A') (hyV' : y ∈ d'.V)
    (hyφ : y ∈ φ.source) (h : P.submanifoldTangent A y ⊆ P.submanifoldTangent A' y) :
    tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) (levelLift φ 1 y) ⊆
      tangentSpace φ.model.E φ.model.C (φ '' (d'.toSubData.shrink φ ∩ A')) (levelLift φ 1 y) := by
  intro v hv
  obtain ⟨α, hα, hαv⟩ := d.exists_mem_submanifoldTangent hφ hyA hyV hyφ hv
  have := (d'.tangentChartMap_of_mem_submanifoldTangent hφ hyA' hyV' hyφ (h hα)).2
  rwa [hαv] at this

/-- **`T_yA ⊆ T_y^R X` depends only on the set `T_yA ⊆ TX`**: if `T_yA' ⊆ T_yA` and
`T_yA ⊆ T_y^R X`, then `T_yA' ⊆ T_y^R X`. -/
theorem IsTangentReducedAt.of_submanifoldTangent_subset {A A' : Set X} {y : X}
    (h : P.IsTangentReducedAt A y) (hA' : P.IsSmoothSubmanifold A') (hyA' : y ∈ A')
    (hsub : P.submanifoldTangent A' y ⊆ P.submanifoldTangent A y) :
    P.IsTangentReducedAt A' y := by
  obtain ⟨hyA, d, -, -, -, -, -, hyV, -⟩ := id h
  set d' := hA'.data hyA'
  have hyV' : y ∈ d'.V := hA'.mem_data_V hyA'
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hy1 : y ∈ P.levelSet 1 := d.mem_levelSet_one hyA hyV
  have hz : φ.model.E.toBase 1 (levelLift φ 1 y) = φ y := P.toBase_levelLift hφ hyφ hy1
  have hred := h.isReducedChart d hφ T hT hyV hyφ hz
  refine ⟨hyA', d', φ, n, W, T, levelLift φ 1 y, hyV', hφ, hyφ, hT, hz, fun v hv => hred ?_⟩
  exact tangentSpace_subset_of_submanifoldTangent_subset d' d hφ hyA' hyV' hyA hyV hyφ hsub hv

/-- `T_yA ⊆ T_y^R X` iff `T_yA' ⊆ T_y^R X` when `T_yA = T_yA'`. -/
theorem isTangentReducedAt_iff_of_submanifoldTangent_eq {A A' : Set X}
    (hA : P.IsSmoothSubmanifold A) (hA' : P.IsSmoothSubmanifold A') {y : X} (hyA : y ∈ A)
    (hyA' : y ∈ A') (heq : P.submanifoldTangent A y = P.submanifoldTangent A' y) :
    P.IsTangentReducedAt A y ↔ P.IsTangentReducedAt A' y :=
  ⟨fun h => h.of_submanifoldTangent_subset hA' hyA' heq.ge,
    fun h => h.of_submanifoldTangent_subset hA hyA heq.le⟩

/-! ### Transport along sc-diffeomorphisms -/

/-- The image of an open subset of `U` under an sc-diffeomorphism `f : U → U'` is open. -/
theorem IsScDiffeoOn.isOpen_image' {f g : X → X} {U U' : Set X} (hf : P.IsScDiffeoOn P f g U U')
    {S : Set X} (hS : IsOpen S) (hSU : S ⊆ U) : IsOpen (f '' S) := by
  have h : f '' S = U' ∩ g ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hf.mapsTo (hSU hx), by rw [mem_preimage, hf.left_inv x (hSU hx)]; exact hx⟩
    · rintro ⟨hy, hgy⟩
      exact ⟨g y, hgy, hf.right_inv y hy⟩
  rw [h]
  exact hf.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hf.isScSmoothOn_inv.isOpen hS

/-- **`T_aA ⊆ T_a^R X` is carried by sc-diffeomorphisms**: for `f : U → U'` an
sc-diffeomorphism and `A ⊆ U`, `T_aA ⊆ T_a^R X` gives `T_{f(a)} f(A) ⊆ T_{f(a)}^R X`.  *Proof*:
for a chart `ψ` around `f(a)`, the chart `χ = ψ ∘ f` around `a` (`transportChart`) has the chart
model `χ(W ∩ A) = ψ(f(W) ∩ f(A))`; the condition holds there (every chart), and the chart change
in `ψ` from `f(W)` to the set of the data of `f(A)` is `isReducedTangentAt_chart_change`. -/
theorem IsTangentReducedAt.image {f g : X → X} {U U' : Set X} (hf : P.IsScDiffeoOn P f g U U')
    {A : Set X} (hfA : P.IsSmoothSubmanifold (f '' A)) (hAU : A ⊆ U) {a : X}
    (h : P.IsTangentReducedAt A a) : P.IsTangentReducedAt (f '' A) (f a) := by
  obtain ⟨haA, d, -, -, -, -, -, haV, -⟩ := id h
  have hfaA : f a ∈ f '' A := ⟨a, haA, rfl⟩
  obtain ⟨ψ, hψ, hfaψ⟩ := P.exists_isChart_mem_source (f a)
  obtain ⟨n, W, T, hT⟩ := ψ.model.isPartialQuadrant
  set χ := transportChart hf ψ with hχdef
  have hχ : P.IsChart χ := transportChart_isChart hf hψ
  have haχ : a ∈ χ.source := ⟨hAU haA, hfaψ⟩
  have hfa1 : f a ∈ P.levelSet 1 := hfA.mem_levelSet_one hfaA
  have hz : ψ.model.E.toBase 1 (levelLift ψ 1 (f a)) = ψ (f a) := P.toBase_levelLift hψ hfaψ hfa1
  have hred := h.isReducedChart d hχ T hT haV haχ hz
  set G := f '' d.toSubData.shrink χ with hGdef
  have hWU : d.toSubData.shrink χ ⊆ U := fun x hx => (d.toSubData.shrink_subset_source χ hx).1
  have hinj : InjOn f U := fun x hx x' hx' hxx' => by
    rw [← hf.left_inv x hx, ← hf.left_inv x' hx', hxx']
  have himg : χ '' (d.toSubData.shrink χ ∩ A) = ψ '' (G ∩ f '' A) := by
    change (ψ ∘ f) '' _ = _
    rw [image_comp, hinj.image_inter hWU hAU]
  have hred' : IsReducedTangentAt ψ.model.E ψ.model.C (ψ '' (G ∩ f '' A)) T
      (levelLift ψ 1 (f a)) := by
    rw [← himg]; exact hred
  set d' := hfA.data hfaA
  have hfaV' : f a ∈ d'.V := hfA.mem_data_V hfaA
  have hG : IsOpen G := hf.isOpen_image' (d.toSubData.isOpen_shrink χ) hWU
  have hGψ : G ⊆ ψ.source := by
    rintro _ ⟨x, hx, rfl⟩; exact (d.toSubData.shrink_subset_source χ hx).2
  have hQ : IsScRetract ψ.model.E ψ.model.C (ψ '' (G ∩ f '' A)) := by
    rw [← himg]; exact d.toSubData.isScRetract_image χ hχ
  have hzs : levelLift ψ 1 (f a) ∈ ψ.model.E.smoothLvl 1 := by
    change ψ.model.E.toBase 1 _ ∈ (ψ.model.E.smooth : Set (ψ.model.E 0))
    rw [hz]; exact d'.apply_mem_smooth hψ hfaA hfaV' hfaψ
  have hres := isReducedTangentAt_chart_change hψ hψ hG (d'.toSubData.isOpen_shrink ψ) hGψ
    (d'.toSubData.shrink_subset_source ψ) hQ (d'.toSubData.isScRetract_image ψ hψ) hfaA
    ⟨a, d.toSubData.mem_shrink χ haA haV haχ, rfl⟩ (d'.toSubData.mem_shrink ψ hfaA hfaV' hfaψ)
    hz hz hzs T hT T hT hred'
  exact ⟨hfaA, d', ψ, n, W, T, _, hfaV', hψ, hfaψ, hT, hz, hres⟩

/-- `T_{f(a)} f(A) ⊆ T_{f(a)}^R X` iff `T_aA ⊆ T_a^R X`, for an sc-diffeomorphism `f : U → U'`
and a smooth submanifold `A ⊆ U`. -/
theorem isTangentReducedAt_image_iff {f g : X → X} {U U' : Set X}
    (hf : P.IsScDiffeoOn P f g U U') {A : Set X} (hA : P.IsSmoothSubmanifold A) (hAU : A ⊆ U)
    {a : X} (ha : a ∈ A) : P.IsTangentReducedAt (f '' A) (f a) ↔ P.IsTangentReducedAt A a := by
  have hfA := hA.image_of_isScDiffeoOn hf hAU
  refine ⟨fun h => ?_, fun h => h.image hf hfA hAU⟩
  have hgf : g '' (f '' A) = A := by
    rw [image_image]
    exact (image_congr fun y hy => hf.left_inv y (hAU hy)).trans (image_id' A)
  have hfAU' : f '' A ⊆ U' := image_subset_iff.2 fun y hy => hf.mapsTo (hAU hy)
  have := h.image hf.symm (hgf.symm ▸ hA) hfAU'
  rwa [hgf, hf.left_inv a (hAU ha)] at this

/-! ### `L ⊆ T_y^R X` for tangent sets, and `∂M` -/

variable (P) in
/-- **`L ⊆ T_y^R X` for a tangent set `L = T_yA`** of a smooth submanifold `A ∋ y`: some smooth
submanifold `A` through `y` with `T_yA = L` has `T_yA ⊆ T_y^R X`.  By
`isReducedTangentSet_iff` it then holds for every such `A`: the condition depends on the set
`L ⊆ TX` only. -/
def IsReducedTangentSet (y : X) (L : Set P.TangentSpace) : Prop :=
  ∃ A, P.IsSmoothSubmanifold A ∧ y ∈ A ∧ P.submanifoldTangent A y = L ∧ P.IsTangentReducedAt A y

theorem isReducedTangentSet_iff {A : Set X} (hA : P.IsSmoothSubmanifold A) {y : X} (hy : y ∈ A) :
    P.IsReducedTangentSet y (P.submanifoldTangent A y) ↔ P.IsTangentReducedAt A y :=
  ⟨fun ⟨_, hA', hyA', heq, h⟩ =>
    (isTangentReducedAt_iff_of_submanifoldTangent_eq hA' hA hyA' hy heq).1 h,
    fun h => ⟨A, hA, hy, rfl, h⟩⟩

variable (P) in
/-- **`∂M` as a subset of `X`**: the points `y ∈ M` with `d_M(y) ≥ 1` (the boundary of the
induced structure, `mem_submanifoldBoundary_iff_mem_boundary`; `∅` unless `M` is a smooth
submanifold). -/
def submanifoldBoundary (A : Set X) : Set X :=
  {y | ∃ (hA : P.IsSmoothSubmanifold A) (hy : y ∈ A), 1 ≤ P.subDegIndex hA.isSubMPolyfold ⟨y, hy⟩}

theorem mem_submanifoldBoundary_iff_subDegIndex {A : Set X} (hA : P.IsSmoothSubmanifold A)
    {y : X} (hy : y ∈ A) :
    y ∈ P.submanifoldBoundary A ↔ 1 ≤ P.subDegIndex hA.isSubMPolyfold ⟨y, hy⟩ :=
  ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hA, hy, h⟩⟩

/-- `y ∈ ∂M` iff `y` lies in the boundary of the induced M-polyfold structure of `M`. -/
theorem mem_submanifoldBoundary_iff_mem_boundary {A : Set X} (hA : P.IsSmoothSubmanifold A)
    (a : A) : a.1 ∈ P.submanifoldBoundary A ↔
      (letI := P.paracompactSpace_subtype A; a ∈ (subPolyfold hA.isSubMPolyfold).boundary) :=
  (mem_submanifoldBoundary_iff_subDegIndex hA a.2).trans
    (mem_boundary_subPolyfold_iff hA.isSubMPolyfold a).symm

/-- **`∂M` read through Remark 9.2.14** (`remark_9_2_14_iff`): `y ∈ ∂M` iff `y ∈ M`, `y ∈ ∂X`
and `T_yM ⊄ T_y^R X`. -/
theorem mem_submanifoldBoundary_iff {A : Set X} (hA : P.IsSmoothSubmanifold A) {y : X} :
    y ∈ P.submanifoldBoundary A ↔ y ∈ A ∧ y ∈ P.boundary ∧ ¬ P.IsTangentReducedAt A y := by
  constructor
  · rintro ⟨_, hy, h⟩
    exact ⟨hy, (remark_9_2_14_iff hA ⟨y, hy⟩).1 ((mem_boundary_subPolyfold_iff _ _).2 h)⟩
  · rintro ⟨hy, hb⟩
    exact ⟨hA, hy, (mem_boundary_subPolyfold_iff _ _).1 ((remark_9_2_14_iff hA ⟨y, hy⟩).2 hb)⟩

/-- `∂M ⊆ ∂X` (Lemma 2.26). -/
theorem submanifoldBoundary_subset_boundary (A : Set X) :
    P.submanifoldBoundary A ⊆ P.boundary := fun _ ⟨hA, _, h⟩ =>
  remark_9_2_14_mem_boundary hA.isSubMPolyfold h

/-- `∂M` is a germ: `y ∈ ∂(M ∩ V) ↔ y ∈ ∂M` for `V` open, `y ∈ V`. -/
theorem mem_submanifoldBoundary_inter_isOpen_iff {A : Set X} (hA : P.IsSmoothSubmanifold A)
    {V : Set X} (hV : IsOpen V) {y : X} (hyV : y ∈ V) :
    y ∈ P.submanifoldBoundary (A ∩ V) ↔ y ∈ P.submanifoldBoundary A := by
  have hAV := hA.inter_isOpen hV
  rw [mem_submanifoldBoundary_iff hA, mem_submanifoldBoundary_iff hAV]
  constructor
  · rintro ⟨hy, hb, hT⟩
    exact ⟨hy.1, hb, fun h => hT ((isTangentReducedAt_iff_of_submanifoldTangent_eq hA hAV hy.1 hy
      (submanifoldTangent_inter_isOpen hV hyV).symm).1 h)⟩
  · rintro ⟨hy, hb, hT⟩
    exact ⟨⟨hy, hyV⟩, hb, fun h => hT ((isTangentReducedAt_iff_of_submanifoldTangent_eq hA hAV hy
      ⟨hy, hyV⟩ (submanifoldTangent_inter_isOpen hV hyV).symm).2 h)⟩

/-- **`∂M` is carried by sc-diffeomorphisms**: `f(a) ∈ ∂(f(A))` iff `a ∈ ∂A`. -/
theorem mem_submanifoldBoundary_image_iff {f g : X → X} {U U' : Set X}
    (hf : P.IsScDiffeoOn P f g U U') {A : Set X} (hA : P.IsSmoothSubmanifold A) (hAU : A ⊆ U)
    {a : X} (haU : a ∈ U) :
    f a ∈ P.submanifoldBoundary (f '' A) ↔ a ∈ P.submanifoldBoundary A := by
  have hfA := hA.image_of_isScDiffeoOn hf hAU
  have hinj : InjOn f U := fun x hx x' hx' hxx' => by
    rw [← hf.left_inv x hx, ← hf.left_inv x' hx', hxx']
  have hmem : f a ∈ f '' A ↔ a ∈ A := hinj.mem_image_iff hAU haU
  rw [mem_submanifoldBoundary_iff hA, mem_submanifoldBoundary_iff hfA, hmem,
    ← hf.mem_boundary_iff haU]
  constructor
  · rintro ⟨ha, hb, hT⟩
    exact ⟨ha, hb, fun h => hT ((isTangentReducedAt_image_iff hf hA hAU ha).2 h)⟩
  · rintro ⟨ha, hb, hT⟩
    exact ⟨ha, hb, fun h => hT ((isTangentReducedAt_image_iff hf hA hAU ha).1 h)⟩

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-! ### The boundary part of a formal sum -/

open scoped Classical in
variable (X) in
/-- **The boundary part** `∑_{L ⊄ T_y^R X} c_L` of a formal sum `∑ c_L · L` (`L ⊆ T_y^R X` read
by `IsReducedTangentSet`). -/
def boundaryPart (y : Obj) (w : Set X.PObj.TangentSpace →₀ ℚ) : ℚ :=
  w.sum fun L c => if ¬ X.PObj.IsReducedTangentSet y L then c else 0

open scoped Classical in
theorem boundaryPart_sum_single {ι : Type*} [Fintype ι] (y : Obj)
    (L : ι → Set X.PObj.TangentSpace) (c : ι → ℚ) :
    X.boundaryPart y (∑ i, Finsupp.single (L i) (c i)) =
      ∑ i, if ¬ X.PObj.IsReducedTangentSet y (L i) then c i else 0 := by
  rw [boundaryPart]
  refine (Finsupp.sum_finsetSum_index (fun _ => ?_) (fun _ _ _ => ?_)).symm.trans ?_
  · exact ite_self 0
  · split_ifs <;> simp
  · exact Finset.sum_congr rfl fun i _ => Finsupp.sum_single_index (ite_self 0)

theorem boundaryPart_zero (y : Obj) : X.boundaryPart y 0 = 0 := Finsupp.sum_zero_index

theorem boundaryPart_nonneg {x : Obj} {w : Set X.PObj.TangentSpace →₀ ℚ} (hw : w ∈ X.Gr x)
    (y : Obj) : 0 ≤ X.boundaryPart y w := by
  rw [boundaryPart, Finsupp.sum]
  refine Finset.sum_nonneg fun L _ => ?_
  split_ifs <;> first | exact le_rfl | exact hw.1 L

/-! ### Definition 9.2.16: the boundary `∂Θ` -/

open scoped Classical in
variable (X) in
/-- **2021 Definition 9.2.16, p. 421 (2017: Definition 9.7, p. 309) (the boundary `∂Θ`)**:
`∂Θ(y) = ∑_{L ⊄ T_y^R X} σ_L` for `y ∈ ∂X`, where `TΘ(y) = ∑ σ_L · L` (Theorem 9.2.1), and
`∂Θ(y) = 0` for `y ∉ ∂X`: the intrinsic form of the sum in the proof of Proposition 9.2.15 (1).
Locally `∂Θ(y) = ∑_{i : y ∈ Mᵢ, d_{Mᵢ}(y) ≥ 1} σᵢ` for every local branching structure
(`boundaryTheta_eq`). -/
def boundaryTheta (Θ : Obj → ℚ) (y : Obj) : ℚ :=
  if y ∈ X.PObj.boundary then X.boundaryPart y (X.tangentValue Θ y) else 0

theorem boundaryTheta_eq_zero_of_not_mem_boundary {Θ : Obj → ℚ} {y : Obj}
    (hy : y ∉ X.PObj.boundary) : X.boundaryTheta Θ y = 0 := if_neg hy

theorem boundaryTheta_eq_zero_of_not_mem_supp {Θ : Obj → ℚ} {y : Obj} (hy : y ∉ supp Θ) :
    X.boundaryTheta Θ y = 0 := by
  rw [boundaryTheta, X.tangentValue_eq_zero hy, boundaryPart_zero, ite_self]

theorem boundaryTheta_nonneg (Θ : Obj → ℚ) (y : Obj) : 0 ≤ X.boundaryTheta Θ y := by
  rw [boundaryTheta]
  split_ifs
  exacts [boundaryPart_nonneg (X.tangentValue_mem Θ y) y, le_rfl]

/-- `supp(∂Θ) ⊆ ∂X ∩ supp(Θ)`. -/
theorem supp_boundaryTheta_subset (Θ : Obj → ℚ) :
    supp (X.boundaryTheta Θ) ⊆ X.PObj.boundary ∩ supp Θ := fun y hy => by
  refine ⟨by_contra fun hb => ?_, by_contra fun hs => ?_⟩
  · have h : 0 < X.boundaryTheta Θ y := hy
    rw [boundaryTheta_eq_zero_of_not_mem_boundary hb] at h
    exact lt_irrefl _ h
  · have h : 0 < X.boundaryTheta Θ y := hy
    rw [boundaryTheta_eq_zero_of_not_mem_supp hs] at h
    exact lt_irrefl _ h

open scoped Classical in
/-- **The local formula for `∂Θ`** (Proposition 9.2.15 (3), Definition 9.2.16 (2)): for every local
branching structure `(Mᵢ)`, `(σᵢ)` on `U(x)` and `y ∈ U(x)`,
`∂Θ(y) = ∑_{i : y ∈ ∂Mᵢ} σᵢ = ∑_{i : y ∈ Mᵢ, d_{Mᵢ}(y) ≥ 1} σᵢ`.  *Proof* (the text's proof of
Proposition 9.2.15 (1)): `TΘ(y) = ∑_{y ∈ Mᵢ} σᵢ · T_yMᵢ` (the restricted structure at `y`); for
`y ∈ ∂X`, `y ∈ ∂Mᵢ` iff `T_yMᵢ ⊄ T_y^R X` (Remark 9.2.14, `remark_9_2_14_iff`), a condition on
the set `T_yMᵢ ⊆ TX` (`isReducedTangentSet_iff`); for `y ∉ ∂X` no `y ∈ ∂Mᵢ` (Lemma 2.26). -/
theorem boundaryTheta_eq {Θ : Obj → ℚ} (hind : X.HasIndependentTangentSums Θ) {x : Obj}
    (B : X.LocalBranchingStructure Θ x) {y : Obj} (hy : y ∈ B.U) :
    X.boundaryTheta Θ y = ∑ i with y ∈ X.PObj.submanifoldBoundary (B.M i), B.σ i := by
  rw [boundaryTheta]
  split_ifs with hb
  · rw [X.tangentValue_eq hind (B.restrictAt hy), LocalBranchingStructure.tangentSum,
      boundaryPart_sum_single, ← Finset.sum_filter]
    have hT : ∀ i' : (B.restrictAt hy).ι,
        X.PObj.IsReducedTangentSet y (X.PObj.submanifoldTangent ((B.restrictAt hy).M i') y) ↔
          X.PObj.IsTangentReducedAt (B.M i'.1) y := fun i' => by
      rw [LocalBranchingStructure.restrictAt_M,
        MPolyfold.submanifoldTangent_inter_isOpen (B.isOpen_nbhdAt y) (B.mem_nbhdAt_self hy),
        MPolyfold.isReducedTangentSet_iff (B.isSmoothSubmanifold i'.1) i'.2]
    refine Finset.sum_bij (fun a _ => a.1) (fun a ha => ?_) (fun a _ b _ hab => Subtype.ext hab)
      (fun i hi => ?_) fun _ _ => rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact (MPolyfold.mem_submanifoldBoundary_iff (B.isSmoothSubmanifold a.1)).2
        ⟨a.2, hb, (hT a).not.1 ha⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨hyi, -, hr⟩ := (MPolyfold.mem_submanifoldBoundary_iff (B.isSmoothSubmanifold i)).1 hi
      exact ⟨⟨i, hyi⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hT ⟨i, hyi⟩).not.2 hr⟩, rfl⟩
  · exact (Finset.sum_eq_zero fun i hi => absurd
      (MPolyfold.submanifoldBoundary_subset_boundary _ (Finset.mem_filter.1 hi).2) hb).symm

/-! ### Proposition 9.2.15 -/

open scoped Classical in
/-- **2021 Proposition 9.2.15 (1), p. 420 (2017: Proposition 9.4 (1), p. 308)**: for two local
branching structures `(Mᵢ)`, `(σᵢ)` and `(N_j)`, `(τ_j)` of `Θ` at `x`, and `y` in both domains,
`∑_{i : y ∈ ∂Mᵢ} σᵢ = ∑_{j : y ∈ ∂N_j} τ_j` (9.8).  The independence of `TΘ` (Theorem 9.2.1) is
the hypothesis `HasIndependentTangentSums`, as in `theorem_9_2_1`; the hypotheses
`x ∈ supp(Θ) ∩ ∂X` and "`Θ` a branched ep⁺-subgroupoid" are not needed. -/
theorem proposition_9_2_15_1 {Θ : Obj → ℚ} (hind : X.HasIndependentTangentSums Θ) {x : Obj}
    (B B' : X.LocalBranchingStructure Θ x) {y : Obj} (hy : y ∈ B.U) (hy' : y ∈ B'.U) :
    ∑ i with y ∈ X.PObj.submanifoldBoundary (B.M i), B.σ i =
      ∑ j with y ∈ X.PObj.submanifoldBoundary (B'.M j), B'.σ j := by
  rw [← X.boundaryTheta_eq hind B hy, ← X.boundaryTheta_eq hind B' hy']

open scoped Classical in
/-- **2021 Proposition 9.2.15 (2), p. 420 (2017: Proposition 9.4 (2))**: the sums (9.8) vanish at
`y` with `d_X(y) = 0`, as does the formal sum `∑_{i : y ∈ Mᵢ, d_{Mᵢ}(y) ≥ 1} σᵢ · T_yMᵢ` (the
text's proof): `d_{Mᵢ}(y) ≤ d_X(y) = 0` (Lemma 2.26).  No independence is needed. -/
theorem proposition_9_2_15_2 {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x)
    {y : Obj} (hy0 : X.PObj.degIndex y = 0) :
    ∑ i with y ∈ X.PObj.submanifoldBoundary (B.M i), B.σ i = 0 ∧
      ∑ i with y ∈ X.PObj.submanifoldBoundary (B.M i),
        Finsupp.single (X.PObj.submanifoldTangent (B.M i) y) (B.σ i) = 0 := by
  have hnot : ∀ i ∈ Finset.univ.filter fun i => y ∈ X.PObj.submanifoldBoundary (B.M i), False :=
    fun i hi => by
      have h := MPolyfold.submanifoldBoundary_subset_boundary _ (Finset.mem_filter.1 hi).2
      change 1 ≤ X.PObj.degIndex y at h
      omega
  exact ⟨Finset.sum_eq_zero fun i hi => (hnot i hi).elim,
    Finset.sum_eq_zero fun i hi => (hnot i hi).elim⟩

/-- **`∂Θ` is a functor**: `∂Θ(s φ) = ∂Θ(t φ)`.  For `s φ ∈ supp(Θ)` the transported structure
`φ̂(Mᵢ ∩ U(φ))` at `t φ` has `t φ ∈ ∂φ̂(Mᵢ ∩ U(φ))` iff `s φ ∈ ∂Mᵢ`
(`mem_submanifoldBoundary_image_iff`). -/
theorem isFunctorial_boundaryTheta {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) : X.IsFunctorial (X.boundaryTheta Θ) := by
  classical
  intro φ
  by_cases hs : X.src φ ∈ supp Θ
  · obtain ⟨B⟩ := hΘ.localBranching _ hs
    rw [X.boundaryTheta_eq hind B B.mem_U,
      X.boundaryTheta_eq hind (B.transport hΘ.isFunctorial φ) (B.transport hΘ.isFunctorial φ).mem_U]
    refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
    have hd := X.isScDiffeoOn_hat' φ
    have hS := hd.isScSmoothOn.isOpen
    change _ ↔ X.tgt φ ∈ X.PObj.submanifoldBoundary (X.hat φ '' (B.M i ∩ (X.sheetAt φ).srcSet))
    rw [← X.hat_src φ, MPolyfold.mem_submanifoldBoundary_image_iff hd
      ((B.isSmoothSubmanifold i).inter_isOpen hS) inter_subset_right (X.src_mem_sheetAt φ),
      MPolyfold.mem_submanifoldBoundary_inter_isOpen_iff (B.isSmoothSubmanifold i) hS
        (X.src_mem_sheetAt φ)]
  · have ht : X.tgt φ ∉ supp Θ := fun h => hs (by
      change 0 < Θ (X.src φ); rw [hΘ.isFunctorial φ]; exact h)
    rw [boundaryTheta_eq_zero_of_not_mem_supp hs, boundaryTheta_eq_zero_of_not_mem_supp ht]

open scoped Classical in
/-- **2021 Proposition 9.2.15 (3), p. 421 (2017: Proposition 9.4 (3))**: `∂Θ : X → ℚ⁺` is a
functor with `supp(∂Θ) ⊆ ∂X`, and for `x ∈ supp(∂Θ)`, any local branching structure on `U(x)`
and `y ∈ U(x)`, `∂Θ(y) = ∑_{i : y ∈ Mᵢ, d_{Mᵢ}(y) ≥ 1} σᵢ` (`y ∈ ∂Mᵢ` is, by definition,
`y ∈ Mᵢ` and `d_{Mᵢ}(y) ≥ 1`: `mem_submanifoldBoundary_iff_subDegIndex`).  The local formula holds
at every `x`, not only on `supp(∂Θ)` (`boundaryTheta_eq`). -/
theorem proposition_9_2_15_3 {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) :
    X.IsFunctorial (X.boundaryTheta Θ) ∧ (∀ y, 0 ≤ X.boundaryTheta Θ y) ∧
      supp (X.boundaryTheta Θ) ⊆ X.PObj.boundary ∧
      ∀ x ∈ supp (X.boundaryTheta Θ), ∀ B : X.LocalBranchingStructure Θ x, ∀ y ∈ B.U,
        X.boundaryTheta Θ y = ∑ i with y ∈ X.PObj.submanifoldBoundary (B.M i), B.σ i :=
  ⟨X.isFunctorial_boundaryTheta hΘ hind, X.boundaryTheta_nonneg Θ,
    fun _ hy => (X.supp_boundaryTheta_subset Θ hy).1,
    fun _ _ B _ hy => X.boundaryTheta_eq hind B hy⟩

open scoped Classical in
/-- **The natural decomposition in the proof of Proposition 9.2.15 (1)**: for `y ∈ U(x) ∩ ∂X`,
the part `∑_{i : y ∈ Mᵢ, d_{Mᵢ}(y) ≥ 1} σᵢ · T_yMᵢ` of `TΘ(y)` is the part of `TΘ(y)` on the
tangent sets `L ⊄ T_y^R X`, hence independent of the local branching structure (and the part with
`d_{Mᵢ}(y) = 0` is the complementary part, `Finsupp.filter_pos_add_filter_neg`). -/
theorem filter_tangentValue_eq {Θ : Obj → ℚ} (hind : X.HasIndependentTangentSums Θ) {x : Obj}
    (B : X.LocalBranchingStructure Θ x) {y : Obj} (hy : y ∈ B.U) (hb : y ∈ X.PObj.boundary) :
    (X.tangentValue Θ y).filter (fun L => ¬ X.PObj.IsReducedTangentSet y L) =
      ∑ i with y ∈ X.PObj.submanifoldBoundary (B.M i),
        Finsupp.single (X.PObj.submanifoldTangent (B.M i) y) (B.σ i) := by
  have hT : ∀ i' : (B.restrictAt hy).ι,
      X.PObj.submanifoldTangent ((B.restrictAt hy).M i') y =
        X.PObj.submanifoldTangent (B.M i'.1) y := fun i' =>
    MPolyfold.submanifoldTangent_inter_isOpen (B.isOpen_nbhdAt y) (B.mem_nbhdAt_self hy)
  have hR : ∀ i' : (B.restrictAt hy).ι,
      X.PObj.IsReducedTangentSet y (X.PObj.submanifoldTangent ((B.restrictAt hy).M i') y) ↔
        X.PObj.IsTangentReducedAt (B.M i'.1) y := fun i' => by
    rw [hT i', MPolyfold.isReducedTangentSet_iff (B.isSmoothSubmanifold i'.1) i'.2]
  rw [X.tangentValue_eq hind (B.restrictAt hy), LocalBranchingStructure.tangentSum,
    Finsupp.filter_sum]
  have hsingle : ∀ i' : (B.restrictAt hy).ι,
      (Finsupp.single (X.PObj.submanifoldTangent ((B.restrictAt hy).M i') y)
        ((B.restrictAt hy).σ i')).filter (fun L => ¬ X.PObj.IsReducedTangentSet y L) =
        if ¬ X.PObj.IsTangentReducedAt (B.M i'.1) y then
          Finsupp.single (X.PObj.submanifoldTangent (B.M i'.1) y) (B.σ i'.1) else 0 := fun i' => by
    by_cases h : X.PObj.IsTangentReducedAt (B.M i'.1) y
    · rw [if_neg (not_not.2 h)]
      exact Finsupp.filter_single_of_neg (fun L => ¬ X.PObj.IsReducedTangentSet y L)
        (fun h' => h' ((hR i').2 h))
    · rw [if_pos h, Finsupp.filter_single_of_pos (fun L => ¬ X.PObj.IsReducedTangentSet y L)
        ((hR i').not.2 h), hT i']
      rfl
  rw [Finset.sum_congr rfl fun i' _ => hsingle i', ← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ => a.1) (fun a ha => ?_) (fun a _ b _ hab => Subtype.ext hab)
    (fun i hi => ?_) fun _ _ => rfl
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact (MPolyfold.mem_submanifoldBoundary_iff (B.isSmoothSubmanifold a.1)).2 ⟨a.2, hb, ha⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hyi, -, hr⟩ := (MPolyfold.mem_submanifoldBoundary_iff (B.isSmoothSubmanifold i)).1 hi
    exact ⟨⟨i, hyi⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hr⟩, rfl⟩

/-! ### Definition 9.2.16: the characterization of `∂Θ` -/

open scoped Classical in
variable (X) in
/-- **The two properties of 2021 Definition 9.2.16 as printed**: (1) `supp(F) ⊆ ∂X`; (2) for
`x ∈ supp(F)`, every local branching structure of `Θ` on `U(x)` and `y ∈ U(x)`,
`F(y) = ∑_{i : y ∈ Mᵢ, d_{Mᵢ}(y) ≥ 1} σᵢ`. -/
def IsBoundaryCharacterized (Θ F : Obj → ℚ) : Prop :=
  supp F ⊆ X.PObj.boundary ∧ ∀ x ∈ supp F, ∀ B : X.LocalBranchingStructure Θ x, ∀ y ∈ B.U,
    F y = ∑ i with y ∈ X.PObj.submanifoldBoundary (B.M i), B.σ i

/-- **Definition 9.2.16, existence**: `∂Θ` has the properties (1), (2) (Proposition 9.2.15). -/
theorem isBoundaryCharacterized_boundaryTheta {Θ : Obj → ℚ}
    (hind : X.HasIndependentTangentSums Θ) :
    X.IsBoundaryCharacterized Θ (X.boundaryTheta Θ) :=
  ⟨fun _ hy => (X.supp_boundaryTheta_subset Θ hy).1, fun _ _ B _ hy => X.boundaryTheta_eq hind B hy⟩

/-- **The properties (1), (2) of Definition 9.2.16, as printed, do not determine `∂Θ`** as we
read them: the zero functor has them for every `Θ` (its support is empty, so (2) is vacuous).
So they characterize `∂Θ` only if `∂Θ = 0` (`boundaryTheta_eq_zero_of_unique`); the reading
under which `∂Θ` is unique is `eq_boundaryTheta`. -/
theorem isBoundaryCharacterized_zero (Θ : Obj → ℚ) : X.IsBoundaryCharacterized Θ 0 :=
  ⟨fun _ h => (lt_irrefl (0 : ℚ) h).elim, fun _ h => (lt_irrefl (0 : ℚ) h).elim⟩

theorem boundaryTheta_eq_zero_of_unique {Θ : Obj → ℚ}
    (h : ∀ F, X.IsBoundaryCharacterized Θ F → F = X.boundaryTheta Θ) : X.boundaryTheta Θ = 0 :=
  (h 0 (X.isBoundaryCharacterized_zero Θ)).symm

open scoped Classical in
/-- **2021 Definition 9.2.16, uniqueness, in the reading where it holds**: a function `F` which
vanishes off `supp(Θ)` and satisfies the local formula (2) at the points `x` of `supp(Θ)` (for
one local branching structure at `x`, at `y = x`) is `∂Θ`.  (Off `supp(Θ)` there may be no local
branching structure at all, at points of the closure of `supp(Θ)`, so (2) alone does not reach
them; and (2) required only on `supp(F)` is satisfied by `F = 0`,
`isBoundaryCharacterized_zero`.) -/
theorem eq_boundaryTheta {Θ : Obj → ℚ}
    (hind : X.HasIndependentTangentSums Θ) {F : Obj → ℚ} (h0 : ∀ y ∉ supp Θ, F y = 0)
    (hloc : ∀ x ∈ supp Θ, ∃ B : X.LocalBranchingStructure Θ x,
      F x = ∑ i with x ∈ X.PObj.submanifoldBoundary (B.M i), B.σ i) :
    F = X.boundaryTheta Θ := by
  funext y
  by_cases hy : y ∈ supp Θ
  · obtain ⟨B, hB⟩ := hloc y hy
    rw [hB, X.boundaryTheta_eq hind B B.mem_U]
  · rw [h0 y hy, boundaryTheta_eq_zero_of_not_mem_supp hy]

/-- `∂Θ ≤ Θ`: on `U(x)`, `∂Θ(y) = ∑_{y ∈ ∂Mᵢ} σᵢ ≤ ∑_{y ∈ Mᵢ} σᵢ = Θ(y)`. -/
theorem boundaryTheta_le {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) (y : Obj) : X.boundaryTheta Θ y ≤ Θ y := by
  classical
  by_cases hy : y ∈ supp Θ
  · obtain ⟨B⟩ := hΘ.localBranching y hy
    rw [X.boundaryTheta_eq hind B B.mem_U, B.eq_sum y B.mem_U]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i _ _ => (B.σ_pos i).le
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ((MPolyfold.mem_submanifoldBoundary_iff (B.isSmoothSubmanifold i)).1 hi).1
  · rw [boundaryTheta_eq_zero_of_not_mem_supp hy]
    exact hΘ.nonneg y

end EpGroupoid

/-! ### Witnesses -/

/-- **`∂Θ` for the indicator of a point of `ℝⁿ`**: `∂ℝⁿ = ∅`, so `∂Θ = 0`. -/
theorem boundaryTheta_indicator (n : ℕ) (p : Fin n → ℝ) :
    (EpGroupoid.trivial (rnPolyfold n)).boundaryTheta (({p} : Set (Fin n → ℝ)).indicator 1) = 0 :=
  funext fun _ => EpGroupoid.boundaryTheta_eq_zero_of_not_mem_boundary
    (by change ¬ 1 ≤ (rnPolyfold n).degIndex _; rw [rnPolyfold_degIndex]; omega)

/-- **Satisfiability of the hypotheses of Proposition 9.2.15**: for the indicator `Θ` of a point
of `ℝⁿ` (nonempty support), `Θ` is a branched ep⁺-subgroupoid with independent tangent sums, so
Proposition 9.2.15 (1)–(3) apply. -/
theorem proposition_9_2_15_3_indicator (n : ℕ) (p : Fin n → ℝ) :
    (EpGroupoid.trivial (rnPolyfold n)).IsFunctorial
      ((EpGroupoid.trivial (rnPolyfold n)).boundaryTheta (({p} : Set (Fin n → ℝ)).indicator 1)) :=
  (EpGroupoid.proposition_9_2_15_3 (EpGroupoid.isBranchedEpSubgroupoid_indicator n p)
    (hasIndependentTangentSums_indicator n p)).1

/-! ### A point of `X` as a submanifold: `T_pM ⊆ T_p^R X` and `p ∉ ∂M` -/

/-- A map constant on an sc-domain has vanishing sc-derivative on `U₁` (uniqueness of the
derivative on `U₁`, `IsScDomain.uniqueDiffWithinAt_one`, and density of `E₁` in `E₀`). -/
theorem scDeriv_eq_zero_of_eqOn_const {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0}
    (hf : IsSc1 U f) (hU : IsScDomain E U) {q : F 0} (hc : ∀ x ∈ U, f x = q) {x : E 1}
    (hx : x ∈ E.lvlSet U 1) : scDeriv U f x = 0 := by
  have h1 := hf.isSc1With_scDeriv.hasFDerivWithinAt x hx
  have h2 : HasFDerivWithinAt (f ∘ E.toBase 1) (0 : E 1 →L[ℝ] F 0) (E.lvlSet U 1) x :=
    (hasFDerivWithinAt_const q x _).congr (fun y hy => hc _ hy) (hc _ hx)
  have h3 := (hU.uniqueDiffWithinAt_one x hx).eq h1 h2
  have hd : Dense (Submodule.span ℝ (range (E.toBase 1)) : Set (E 0)) :=
    Dense.mono Submodule.subset_span (E.denseRange_inclK 0 1)
  refine ContinuousLinearMap.ext_on hd ?_
  rintro _ ⟨y, rfl⟩
  have := congrArg (fun L : E 1 →L[ℝ] F 0 => L y) h3
  simpa using this

/-- The tangent space of a one-point retract `{q}` is `{0}`. -/
theorem tangentSpace_singleton_subset {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C)
    {q : E 0} (hR : R.retract = {q}) {z : E 1} (hz : E.toBase 1 z = q) :
    tangentSpace E C {q} z ⊆ {0} := by
  have hzR : z ∈ E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hR, hz]; rfl
  rw [← hR, tangentSpace_eq_range R hzR]
  rintro _ ⟨v, rfl⟩
  have hc : ∀ u ∈ R.U, R u = q := fun u hu => by
    have := R.apply_mem_retract hu
    rw [hR] at this
    exact this
  rw [scDeriv_eq_zero_of_eqOn_const R.isSc1 R.isScDomain hc (R.lvlSet_retract_subset 1 hzR)]
  rfl

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- The constant map at a smooth point is sc-smooth between any two M-polyfolds (for maps out of
`ℝᵐ` this is `isScSmoothMap_const_of_mem_smoothSet`). -/
theorem isScSmoothMap_const_of_mem_smoothSet' {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] {Q : MPolyfold Y} {q : Y} (hq : q ∈ Q.smoothSet) :
    P.IsScSmoothMap Q fun _ => q := by
  refine MPolyfold.isScSmoothMap_of_local fun x => ?_
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source x
  obtain ⟨ψ, hψ, hqψ⟩ := Q.exists_isChart_mem_source q
  refine ⟨φ, ψ, φ.source, hφ, hψ, φ.isOpen_source, hx, subset_rfl, fun _ _ => hqψ, ?_⟩
  rw [φ.image_source]
  have hsm : ψ q ∈ ψ.model.E.smooth := ψ.model.E.mem_smooth_iff.2 fun k =>
    (Q.mem_levelSet_iff hψ hqψ).1 (mem_iInter.1 hq k)
  exact ⟨fun _ _ => ψ.mapsTo_model q hqψ,
    fun R _ => isScSmooth_const_of_mem_smooth R.isScDomain hsm⟩

/-- A smooth point `p` is a smooth finite-dimensional submanifold `{p}` (Definition 4.13; the
constant map `p` is an sc⁺-retraction onto `{p}`), as `rnPolyfold_isSmoothSubmanifold_singleton`
for `ℝⁿ`. -/
theorem isSmoothSubmanifold_singleton {p : X} (hp : p ∈ P.smoothSet) :
    P.IsSmoothSubmanifold {p} := by
  have hp1 : p ∈ P.levelSet 1 := MPolyfold.smoothSet_subset_levelSet (P := P) 1 hp
  have : Nonempty X := ⟨p⟩
  intro a _
  refine ⟨univ, isOpen_univ, mem_univ a, fun _ => p,
    ⟨isScSmoothMap_const_of_mem_smoothSet' hp, fun _ _ => mem_univ _, fun _ _ => rfl,
      fun _ _ => hp1, fun x₀ => ?_⟩, ?_⟩
  · refine isScSmoothMap_const_of_mem_smoothSet'
      ((MPolyfold.mem_shift_smoothSet_iff (P.toLevelOne x₀ p)).2 ?_)
    rw [MPolyfold.levelVal_toLevelOne x₀ hp1]
    exact hp
  · ext y
    simp [eq_comm]

/-- **A point has `T_p{p} ⊆ T_p^R X`** (its chart tangent space is `{0}`), so `d_{p}(p) = 0`
(Lemma 9.2.13, `subDegIndex_eq_zero_of_isTangentReducedAt`), also at points of `∂X`. -/
theorem isTangentReducedAt_singleton {p : X} (hA : P.IsSmoothSubmanifold {p}) :
    P.IsTangentReducedAt {p} p := by
  set d := hA.data (mem_singleton p)
  have hpV : p ∈ d.V := hA.mem_data_V (mem_singleton p)
  obtain ⟨φ, hφ, hpφ⟩ := P.exists_isChart_mem_source p
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hp1 : p ∈ P.levelSet 1 := hA.mem_levelSet_one (mem_singleton p)
  have hz : φ.model.E.toBase 1 (levelLift φ 1 p) = φ p := P.toBase_levelLift hφ hpφ hp1
  refine ⟨mem_singleton p, d, φ, n, W, T, levelLift φ 1 p, hpV, hφ, hpφ, hT, hz, ?_⟩
  have hQ : φ '' (d.toSubData.shrink φ ∩ {p}) = {φ p} := by
    rw [inter_eq_right.2 (singleton_subset_iff.2
      (d.toSubData.mem_shrink φ (mem_singleton p) hpV hpφ)), image_singleton]
  obtain ⟨R, hR⟩ := d.toSubData.isScRetract_image φ hφ
  intro v hv
  change v ∈ tangentSpace _ _ (φ '' (d.toSubData.shrink φ ∩ {p})) _ at hv
  rw [hQ] at hv
  rw [mem_singleton_iff.1 (tangentSpace_singleton_subset R (hR.trans hQ) hz hv)]
  exact (minimalSubspaceWith T _).zero_mem

/-- A point `p` is never in `∂{p}`. -/
theorem not_mem_submanifoldBoundary_singleton (p : X) : p ∉ P.submanifoldBoundary {p} := by
  rintro ⟨hA, hp, h⟩
  have := subDegIndex_eq_zero_of_isTangentReducedAt hA (a := ⟨p, hp⟩)
    (isTangentReducedAt_singleton hA)
  omega

end MPolyfold

namespace EpGroupoid

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)

/-- The local branching structure of the indicator of a smooth point `p` of an M-polyfold `Z` in
the trivial ep-groupoid: `U = Z`, `M = {p}`, weight `1` (as `localBranchingStructure_indicator`
for `ℝⁿ`). -/
def localBranchingStructure_indicator_of_mem {p : Z} (hp : p ∈ P.smoothSet) :
    (trivial P).LocalBranchingStructure (({p} : Set Z).indicator 1) p where
  U := univ
  isOpen_U := isOpen_univ
  mem_U := mem_univ p
  ι := PUnit
  M _ := {p}
  subset_U _ := subset_univ _
  isSmoothSubmanifold _ := MPolyfold.isSmoothSubmanifold_singleton hp
  mem_M _ := rfl
  isProperMap _ := (continuous_inclusion _).isProperMap
  σ _ := 1
  σ_pos _ := one_pos
  eq_sum y _ := by
    by_cases hy : y = p
    · subst hy; simp
    · simp [hy]

omit [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] in
theorem supp_indicator_singleton' (p : Z) :
    supp (({p} : Set Z).indicator (1 : Z → ℚ)) = {p} := by
  ext y
  by_cases hy : y = p
  · subst hy; simp [supp]
  · simp [supp, hy]

/-- The indicator of a smooth point is a branched ep⁺-subgroupoid of the trivial ep-groupoid. -/
theorem isBranchedEpSubgroupoid_indicator_of_mem {p : Z} (hp : p ∈ P.smoothSet) :
    (trivial P).IsBranchedEpSubgroupoid (({p} : Set Z).indicator 1) where
  nonneg y := by
    by_cases hy : y = p
    · subst hy; simp
    · simp [hy]
  isFunctorial _ := rfl
  support_subset y hy := by
    rw [supp_indicator_singleton'] at hy
    rw [mem_singleton_iff.1 hy]; exact hp
  paracompactSpace_orbitSupp := by
    have hc : IsCompact ((trivial P).orbitSupp (({p} : Set Z).indicator 1)) := by
      unfold orbitSupp
      rw [supp_indicator_singleton']
      exact isCompact_singleton.image (trivial P).continuous_π
    have := isCompact_iff_compactSpace.1 hc
    infer_instance
  localBranching y hy := by
    rw [supp_indicator_singleton'] at hy
    rw [mem_singleton_iff.1 hy]
    exact ⟨localBranchingStructure_indicator_of_mem P hp⟩

/-- Its tangent sums are independent (every point of the support is good). -/
theorem hasIndependentTangentSums_indicator_of_mem {p : Z} (hp : p ∈ P.smoothSet) :
    (trivial P).HasIndependentTangentSums (({p} : Set Z).indicator 1) := by
  refine hasIndependentTangentSums_of_subset_goodSet fun y hy => ?_
  rw [supp_indicator_singleton'] at hy
  rw [mem_singleton_iff.1 hy]
  refine ⟨by rw [supp_indicator_singleton']; rfl, p,
    localBranchingStructure_indicator_of_mem P hp, mem_univ p,
    mem_iUnion.2 ⟨PUnit.unit, rfl⟩, univ, isOpen_univ, mem_univ p, subset_rfl,
    fun _ _ _ _ => rfl⟩

/-- **`∂Θ = 0` for the indicator of a smooth point** (`p ∉ ∂{p}`), even if `p ∈ ∂X`. -/
theorem boundaryTheta_indicator_of_mem {p : Z} (hp : p ∈ P.smoothSet) :
    (trivial P).boundaryTheta (({p} : Set Z).indicator 1) = 0 := by
  classical
  funext y
  by_cases hy : y = p
  · subst hy
    rw [(trivial P).boundaryTheta_eq (hasIndependentTangentSums_indicator_of_mem P hp)
      (localBranchingStructure_indicator_of_mem P hp) (mem_univ y)]
    refine Finset.sum_eq_zero fun i hi => absurd (Finset.mem_filter.1 hi).2 ?_
    exact MPolyfold.not_mem_submanifoldBoundary_singleton (P := P) y
  · exact boundaryTheta_eq_zero_of_not_mem_supp (by rw [supp_indicator_singleton']; exact hy)

end EpGroupoid

/-- The corner `0` of the half-line `[0, ∞) = [0, ∞) ⊕ ℝ⁰` (`quadrantPolyfold 1 ℝ⁰`). -/
def halfLineCorner : quadrant 1 (ScBanach.const (Fin 0 → ℝ)) 0 :=
  ⟨0, MPolyfold.zero_mem_quadrant 1 _⟩

theorem halfLineCorner_mem_smoothSet :
    halfLineCorner ∈ (MPolyfold.quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))).smoothSet := by
  have hφ :=
    (MPolyfold.isRelOpenInQuadrant_quadrant 1 (ScBanach.const (Fin 0 → ℝ))).selfChart_isChart
    (MPolyfold.quadrant_nonempty 1 (ScBanach.const (Fin 0 → ℝ)))
  refine (MPolyfold.mem_smoothSet_iff_of_isChart hφ (mem_univ _)).2 ?_
  exact Submodule.zero_mem _

theorem halfLineCorner_mem_boundary :
    halfLineCorner ∈ (MPolyfold.quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))).boundary := by
  change 1 ≤ (MPolyfold.quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))).degIndex halfLineCorner
  rw [halfLineCorner, MPolyfold.quadrantPolyfold_degIndex_zero]

/-- **The corner of the half-line as a witness**: for the indicator `Θ` of the corner `0` of
`[0, ∞)` (a branched ep⁺-subgroupoid with independent tangent sums), `0 ∈ ∂X ∩ supp(Θ)` but
`∂Θ(0) = 0 < Θ(0) = 1`: `∂Θ` is not the restriction of `Θ` to `∂X` (the text before Lemma 9.2.13:
"this is not(!) always the case").  Also a witness at a boundary point for Lemma 9.2.13
(2) ⇒ (1) (`lemma_9_2_13_two_one`): `0 ∈ {0} ∩ ∂X` with `T_0{0} ⊆ T_0^R X`. -/
theorem boundaryTheta_halfLineCorner :
    let P := MPolyfold.quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))
    let Θ := ({halfLineCorner} : Set (quadrant 1 (ScBanach.const (Fin 0 → ℝ)) 0)).indicator
      (1 : quadrant 1 (ScBanach.const (Fin 0 → ℝ)) 0 → ℚ)
    (EpGroupoid.trivial P).IsBranchedEpSubgroupoid Θ ∧
      (EpGroupoid.trivial P).HasIndependentTangentSums Θ ∧
      halfLineCorner ∈ P.boundary ∧ Θ halfLineCorner = 1 ∧
      (EpGroupoid.trivial P).boundaryTheta Θ halfLineCorner = 0 ∧
      P.IsTangentReducedAt {halfLineCorner} halfLineCorner := by
  intro P Θ
  refine ⟨EpGroupoid.isBranchedEpSubgroupoid_indicator_of_mem P halfLineCorner_mem_smoothSet,
    EpGroupoid.hasIndependentTangentSums_indicator_of_mem P halfLineCorner_mem_smoothSet,
    halfLineCorner_mem_boundary, by simp [Θ], ?_, MPolyfold.isTangentReducedAt_singleton
      (MPolyfold.isSmoothSubmanifold_singleton halfLineCorner_mem_smoothSet)⟩
  rw [EpGroupoid.boundaryTheta_indicator_of_mem P halfLineCorner_mem_smoothSet]
  rfl

/-! ### The half-line as a submanifold of itself: `∂Θ ≠ 0` -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **An M-polyfold with a corner structure (Definition 4.1) is a smooth finite-dimensional
submanifold of itself**: `s = id` on `V = X` is an sc⁺-retraction (`X₀ = X_∞` and `1₀¹` is
sc-smooth, from the corner charts, `isScSmoothMap_toLevelOne_of_cover`). -/
theorem HasCornerStructure.isSmoothSubmanifold_univ (hP : P.HasCornerStructure) :
    P.IsSmoothSubmanifold univ := by
  have hc := hasCornerStructure_iff.1 hP
  have hcov : ∀ x, ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧
      IsScPlusRetract φ.model.E φ.model.C φ.model.O := fun x => by
    obtain ⟨χ, hχ, hx, hcorner⟩ := hc x
    exact ⟨χ, hχ, hx, hcorner.isScPlusRetract⟩
  have hsm : ∀ x, x ∈ P.smoothSet := fun x => by
    obtain ⟨χ, hχ, hx, hcorner⟩ := hc x
    exact (P.mem_smoothSet_iff_of_isChart hχ hx).2 (hcorner.mem_smooth _)
  intro a _
  refine ⟨univ, isOpen_univ, mem_univ a, id, ⟨isScSmoothMap_id, fun _ _ => mem_univ _,
    fun _ _ => rfl, fun x _ => MPolyfold.smoothSet_subset_levelSet (P := P) 1 (hsm x),
    fun x₀ => (isScSmoothMap_toLevelOne_of_cover x₀ hcov).2⟩, by simp⟩

end MPolyfold

namespace EpGroupoid

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z)

/-- In the trivial ep-groupoid, `|supp(Θ)|` is paracompact when `supp(Θ)` is closed
(`π : Z → |Z|` is a homeomorphism, `trivialOrbitHomeomorph`). -/
theorem paracompactSpace_orbitSupp_trivial_of_isClosed {Θ : Z → ℚ} (h : IsClosed (supp Θ)) :
    ParacompactSpace ((trivial P).orbitSupp Θ) := by
  have : ParacompactSpace (supp Θ) := h.isClosedEmbedding_subtypeVal.paracompactSpace
  exact ((trivialOrbitHomeomorph P).symm.image (supp Θ)).paracompactSpace_iff.1 inferInstance

/-- The local branching structure of the constant functor `Θ = 1` of an M-polyfold `Z` with a
corner structure, in the trivial ep-groupoid: `U = Z`, `M = Z`, weight `1`. -/
def localBranchingStructure_one (hP : P.HasCornerStructure) (x : Z) :
    (trivial P).LocalBranchingStructure (fun _ => 1) x where
  U := univ
  isOpen_U := isOpen_univ
  mem_U := mem_univ x
  ι := PUnit
  M _ := univ
  subset_U _ := subset_rfl
  isSmoothSubmanifold _ := hP.isSmoothSubmanifold_univ
  mem_M _ := mem_univ x
  isProperMap _ := (Homeomorph.setCongr (rfl : (univ : Set Z) = univ)).isProperMap
  σ _ := 1
  σ_pos _ := one_pos
  eq_sum y _ := by simp

omit [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] in
theorem supp_one : supp (fun _ : Z => (1 : ℚ)) = univ := by
  ext y; simp [supp]

/-- `Θ = 1` is a branched ep⁺-subgroupoid of the trivial ep-groupoid of `Z`. -/
theorem isBranchedEpSubgroupoid_one (hP : P.HasCornerStructure) :
    (trivial P).IsBranchedEpSubgroupoid fun _ => 1 where
  nonneg _ := zero_le_one
  isFunctorial _ := rfl
  support_subset y _ := by
    obtain ⟨χ, hχ, hy, hcorner⟩ := MPolyfold.hasCornerStructure_iff.1 hP y
    exact (P.mem_smoothSet_iff_of_isChart hχ hy).2 (hcorner.mem_smooth _)
  paracompactSpace_orbitSupp :=
    paracompactSpace_orbitSupp_trivial_of_isClosed P (by rw [supp_one]; exact isClosed_univ)
  localBranching x _ := ⟨localBranchingStructure_one P hP x⟩

/-- Its tangent sums are independent (every point is good). -/
theorem hasIndependentTangentSums_one (hP : P.HasCornerStructure) :
    (trivial P).HasIndependentTangentSums fun _ => 1 := by
  refine hasIndependentTangentSums_of_subset_goodSet fun y hy => ?_
  exact ⟨hy, y, localBranchingStructure_one P hP y, mem_univ y,
    mem_iUnion.2 ⟨PUnit.unit, mem_univ y⟩, univ, isOpen_univ, mem_univ y, subset_rfl,
    fun _ _ _ _ => rfl⟩

/-- **`∂Θ` for `Θ = 1`**: `∂Θ = 1` on `∂Z`, the indicator of `∂Z` (each `y ∈ ∂Z` with
`T_yZ ⊄ T_y^R Z` is in `∂M` for `M = Z`). -/
theorem boundaryTheta_one (hP : P.HasCornerStructure) {y : Z}
    (hy : y ∈ P.submanifoldBoundary univ) :
    (trivial P).boundaryTheta (fun _ => 1) y = 1 := by
  classical
  rw [(trivial P).boundaryTheta_eq (hasIndependentTangentSums_one P hP)
    (localBranchingStructure_one P hP y) (mem_univ y)]
  change ∑ i ∈ Finset.univ.filter fun (_ : PUnit) => y ∈ P.submanifoldBoundary univ, (1 : ℚ) = 1
  rw [Finset.filter_true_of_mem fun _ _ => hy]
  simp

end EpGroupoid

namespace MPolyfold

local notation "Wq" => ScBanach.const (Fin 0 → ℝ)

/-- The half-line `[0, ∞)` (`quadrantPolyfold 1 ℝ⁰`) has a corner structure (its chart `id` is,
with the same map, a corner chart, `MChart.exists_isCornerChart_of_finiteDimensional`). -/
theorem halfLine_hasCornerStructure : (quadrantPolyfold 1 Wq).HasCornerStructure := by
  refine hasCornerStructure_iff.2 fun x => ?_
  have hφ := (isRelOpenInQuadrant_quadrant 1 Wq).selfChart_isChart (quadrant_nonempty 1 Wq)
  have hfin : FiniteDimensional ℝ (((ScBanach.const (Fin 1 → ℝ)).prod Wq) 0) := by
    change FiniteDimensional ℝ ((Fin 1 → ℝ) × (Fin 0 → ℝ)); infer_instance
  obtain ⟨χ', hχ', hsrc, hc, -⟩ := MChart.exists_isCornerChart_of_finiteDimensional hφ
    (isRelOpenInQuadrant_quadrant 1 Wq) hfin
  exact ⟨χ', hχ', hsrc ▸ mem_univ x, hc⟩

/-- The image of an open subset of `[0, ∞)` under the chart `id` is relatively open in the
quadrant. -/
theorem halfLine_isRelOpenInQuadrant_image {S : Set (quadrant 1 Wq 0)} (hS : IsOpen S) :
    IsRelOpenInQuadrant ((ScBanach.const (Fin 1 → ℝ)).prod Wq) (quadrant 1 Wq 0)
      (Subtype.val '' S) := by
  obtain ⟨G, hG, rfl⟩ := isOpen_induced_iff.1 hS
  exact ⟨(isRelOpenInQuadrant_quadrant 1 Wq).isPartialQuadrant, G, hG, by
    rw [Subtype.image_preimage_coe, inter_comm]⟩

theorem halfLine_refl_zero :
    (((ScIso.refl ((ScBanach.const (Fin 1 → ℝ)).prod Wq)).lvl 0) 0).1 0 = 0 := by
  rw [map_zero]; rfl

/-- **The corner `0` of `[0, ∞)` is in `∂[0, ∞)`** for `[0, ∞)` as a submanifold of itself: in the
chart `id` with `T = id`, `T_0[0, ∞) = ℝ` (`tangentSpace_relOpen`) and `T_0^R X = {0}`
(`mem_minimalSubspaceWith`). -/
theorem halfLineCorner_mem_submanifoldBoundary :
    halfLineCorner ∈ (quadrantPolyfold 1 Wq).submanifoldBoundary univ := by
  set P := quadrantPolyfold 1 Wq
  have hA := halfLine_hasCornerStructure.isSmoothSubmanifold_univ
  refine (mem_submanifoldBoundary_iff hA).2 ⟨mem_univ _, halfLineCorner_mem_boundary, fun h => ?_⟩
  have hQ := isRelOpenInQuadrant_quadrant 1 Wq
  have hne := quadrant_nonempty 1 Wq
  set φ := (LocalModel.ofRelOpen hQ).selfChart hne
  have hφ : P.IsChart φ := hQ.selfChart_isChart hne
  set d := hA.data (mem_univ halfLineCorner)
  have hcV : halfLineCorner ∈ d.V := hA.mem_data_V (mem_univ _)
  have hz : φ.model.E.toBase 1 0 = φ halfLineCorner := by rw [map_zero]; rfl
  have hred := h.isReducedChart d hφ (ScIso.refl _) (by ext; rfl) hcV (mem_univ _) hz
  have hU : IsRelOpenInQuadrant φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ univ)) :=
    halfLine_isRelOpenInQuadrant_image ((d.toSubData.isOpen_shrink φ).inter isOpen_univ)
  have hmem : φ.model.E.toBase 1 0 ∈ φ '' (d.toSubData.shrink φ ∩ univ) :=
    hz ▸ ⟨halfLineCorner, ⟨d.toSubData.mem_shrink φ (mem_univ _) hcV (mem_univ _), mem_univ _⟩, rfl⟩
  have hv := hred (show ((fun _ => (1 : ℝ), 0) : ((ScBanach.const (Fin 1 → ℝ)).prod Wq) 0) ∈
    tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ univ)) 0 by
      rw [tangentSpace_relOpen hU hmem]; exact mem_univ _)
  have := (mem_minimalSubspaceWith (ScIso.refl _)).1 hv 0 (by
    rw [map_zero]; exact halfLine_refl_zero)
  exact one_ne_zero this

end MPolyfold

/-- **`∂Θ ≠ 0` (a witness for Definition 9.2.16)**: for `Θ = 1` on the half-line `X = [0, ∞)`
(a branched ep⁺-subgroupoid with independent tangent sums, `M = X` with weight `1`),
`∂Θ(0) = 1 = Θ(0)`: the corner is in `∂M` (`T_0M = ℝ ⊄ T_0^R X = {0}`). -/
theorem boundaryTheta_halfLine_one :
    let P := MPolyfold.quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))
    (EpGroupoid.trivial P).IsBranchedEpSubgroupoid (fun _ => 1) ∧
      (EpGroupoid.trivial P).HasIndependentTangentSums (fun _ => 1) ∧
      (EpGroupoid.trivial P).boundaryTheta (fun _ => 1) halfLineCorner = 1 := by
  intro P
  exact ⟨EpGroupoid.isBranchedEpSubgroupoid_one P MPolyfold.halfLine_hasCornerStructure,
    EpGroupoid.hasIndependentTangentSums_one P MPolyfold.halfLine_hasCornerStructure,
    EpGroupoid.boundaryTheta_one P MPolyfold.halfLine_hasCornerStructure
      MPolyfold.halfLineCorner_mem_submanifoldBoundary⟩

/-- **The printed properties of Definition 9.2.16 do not determine `∂Θ`, with `∂Θ ≠ 0`**: for
`Θ = 1` on `[0, ∞)`, both `F = 0` and `F = ∂Θ` have (1) and (2), and `∂Θ ≠ 0`. -/
theorem not_unique_isBoundaryCharacterized_halfLine :
    let P := MPolyfold.quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))
    (EpGroupoid.trivial P).IsBoundaryCharacterized (fun _ => 1) 0 ∧
      (EpGroupoid.trivial P).IsBoundaryCharacterized (fun _ => 1)
        ((EpGroupoid.trivial P).boundaryTheta fun _ => 1) ∧
      (EpGroupoid.trivial P).boundaryTheta (fun _ => 1) ≠ 0 := by
  intro P
  obtain ⟨-, hind, h1⟩ := boundaryTheta_halfLine_one
  refine ⟨EpGroupoid.isBoundaryCharacterized_zero _,
    EpGroupoid.isBoundaryCharacterized_boundaryTheta hind, fun h => ?_⟩
  have := congrFun h halfLineCorner
  rw [h1] at this
  exact one_ne_zero this

end Polyfold
