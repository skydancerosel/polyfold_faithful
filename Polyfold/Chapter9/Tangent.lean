import Polyfold.Chapter9.GoodPoints
import Polyfold.Chapter9.Propositions
import Polyfold.Chapter8.TangentEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.2 "The Tangent and Boundary of Θ", the tangent of `Θ`: the formal sums
`Gr(x)` and the category `Gr(X)` (p. 409; 2017: pp. 297–298), **Theorem 9.2.1** (pp. 409–410;
2017: Theorem 9.1, p. 298) with its proof after Lemma 9.2.7 (pp. 412–418; 2017: pp. 301–306),
and **Definition 9.2.12** (p. 418; 2017: Definition 9.6, p. 306).  Numbers and pages are the 2021
text's, the 2017 ones in parentheses.  The good-point analysis (Definition 9.2.2 – Lemma 9.2.7)
is in `Polyfold/Chapter9/GoodPoints.lean`.

# The tangent `TΘ` of a branched ep⁺-subgroupoid

## The text, paraphrased

(p. 409) For a smooth object `x`, `Gr(x)` is the set of finite formal sums `∑ σ_L · L`,
`σ_L ∈ ℚ`, `σ_L ≥ 0`, of smooth finite-dimensional linear subspaces `L ⊆ T_xX` (equal subspaces
are added), and `Gr(X) = ⋃_{x ∈ X_∞} Gr(x)` with `π : Gr(X) → X_∞`.  `Gr(X)` is a category: a
morphism is `(L, φ)` with `φ ∈ 𝐗_∞`, `L ∈ Gr(s φ)`, from `L` to `∑ σ_L · Tφ(L)`;
`(L, ψ) ∘ (K, φ) = (K, ψ ∘ φ)`, identities `(L, 1_{π(L)})`; `π(L, φ) = φ` makes `π` a functor.
(Theorem 9.2.1) A branched ep⁺-subgroupoid `Θ` has a natural section functor
`TΘ : X_∞ → Gr(X)`, `π ∘ TΘ = Id`, characterized by (1) `TΘ(x) = ∑ σᵢ · T_xMᵢ` for any local
branching structure at `x ∈ supp(Θ)`, the zero-sum off `supp(Θ)`, and (2)
`TΘ(φ) = (TΘ(s φ), φ)`.  The difficulty is the independence in (1); it suffices to treat the
equidimensional case and put `TΘ = ∑ TΘ_k`.  *Proof* (pp. 412–418): at a good point `Θ` is
`Θ(x) · δ_{M_x}` near `x`, so `TΘ(y) = Θ(y) · T_yM_x`.  At a bad point the indices are grouped by
`T_xMᵢ`; Proposition 9.2.8 splits each class `Ξ` into `I^1 ⊔ ⋯ ⊔ I^p` with sequences of good
points `x^e_k → x` lying exactly on the `Mᵢ`, `i ∈ I^e`, built in a chart from a vector `h₀` in
the interior of `L ∩ C` (Lemma 9.2.9), the graph representation of the `Mᵢ`, `i ∈ Ξ`, over a
cone around `h₀` (Lemma 9.2.10) and the inversion of `a ↦ a + PA(a)a` (Lemma 9.2.11); the sums
`∑_{i ∈ I^e} σᵢ = Θ(x^e_k)` are then intrinsic.  (Definition 9.2.12) `TΘ : TX → ℚ⁺` is
`TΘ(h) = 0` over `Θ(x) = 0` and `TΘ(h) = ∑_{i : h ∈ TMᵢ} σᵢ` on `TU(x)`; it is well defined (two
structures give the same sum) and a branched ep⁺-subgroupoid, the local branching structure on
`TU(x)` being `(TMᵢ)`, `(σᵢ)` (p. 409).

## What is formalized

* **`T_yA` without linear structure** (gap G.7): `MPolyfold.submanifoldTangent P A y`, the
  vectors over `y` fixed by `Ts` for the sc⁺-retraction `s` of some data of Definition 4.13
  (Remark 4.14: `T_yA = Ts(y)(T_yX)`).  `mem_submanifoldTangent_iff` (any data computes it,
  through `SubmanifoldData.tmap_eq_of_tmap_eq`: `s' ∘ s = s` near `y` and the chain rule),
  `submanifoldTangent_subset_tangentFiber` (`T_yA ⊆ T_yX`), `mem_of_mem_submanifoldTangent`,
  `submanifoldTangent_congr` (a germ), `submanifoldTangent_inter_isOpen`,
  `submanifoldTangent_image` (`T_{f(a)}f(A) = Tf(T_aA)` for sc-diffeomorphisms).
* **`Gr(x)`, `Gr(X)`**: `EpGroupoid.Gr`, `grPush` (`∑ σ_L · Tφ(L)`), `grPush_mem`,
  `grPush_comp`, `grPush_unit`; `GrObj` with its `Category` instance; `SmoothCat` (`X_∞`, the
  full subcategory `fullSub`) and the projection functor `grProj`.  On fibres:
  `tangentMor_unit_of_eq`, `tangentMor_injOn`, `tangentMor_eq_tangentMapOn_hat` (`Tφ = Tφ̂`).
* **Theorem 9.2.1**: `LocalBranchingStructure.tangentSum` (`∑ σᵢ · T_xMᵢ`), `tangentSum_mem`,
  `tangentSum_eq_zero` (off `supp(Θ)`); the independence predicate `HasIndependentTangentSums`;
  `tangentValue` (`TΘ(x)`), `tangentValue_eq`, `grPush_tangentValue` (naturality, through
  `transport` and `tangentSum_transport`); `tangentSection` (`TΘ`) and `theorem_9_2_1`.
* **The independence** (the difficult part of (1)): `tangentSum_eq_of_isGoodPoint` (at good
  points, no hypothesis); `tangentSum_eq_of_eqOn` (the equidimensional case, granted tangent
  slices `MPolyfold.HasTangentSlicesAt`); `tangentSum_eq_of_dimPartsAgreeNear` (the reduction to
  the equidimensional case); `hasIndependentTangentSums_of_subset_goodSet`,
  `..._of_isOfDim`, `..._of_dimPartsAgreeNear`, `..._of_proposition_9_1_12`.
* **Definition 9.2.12**: `grEval`, `tangentTheta` (`TΘ`), `tangentTheta_eq_zero`,
  `tangentTheta_eq` (the local formula for every structure), `sum_tangent_eq_sum_tangent` (well
  defined), `tangentTheta_nonneg`, `isFunctorial_tangentTheta`, and
  `isBranchedEpSubgroupoid_tangentTheta` (with `tangentSubmanifold`, `TangentBranchingHyp`,
  `tangentBranchingStructure`).
* **Satisfiability**: `hasTangentSlicesAt_rn_zero` (`ℝ⁰`), `hasIndependentTangentSums_indicator`
  (the indicator of a point of `ℝⁿ`), `hasIndependentTangentSums_zero`,
  `tangentBranchingHyp_zero`, `isBranchedEpSubgroupoid_tangentTheta_zero`.

## What the text leaves implicit, and the choices made

* The generators of `Gr(x)` are taken to be all subsets `L ⊆ T_xX`: Part I's `T_xX` carries no
  linear structure here (gap G.7).  The values of `TΘ` are the `T_xMᵢ`, which are
  finite-dimensional subspaces in a chart by Remark 4.14 (`remark_4_2_2`); the linear algebra stays
  in the charts.  Formal sums are finitely supported weights `Set TX →₀ ℚ`, so "`σᵢ · Lᵢ + σⱼ · Lⱼ
  = (σᵢ + σⱼ) · L` for `Lᵢ = Lⱼ = L`" is built in.
* A morphism `(L, φ)` of `Gr(X)` is recorded by `φ` with `s φ = π(L)`, `t φ = π(L')` and
  `L' = ∑ σ_L · Tφ(L)`; `φ ∈ 𝐗_∞` follows from `s φ ∈ X_∞` (`mem_smoothSet_of_src`).
* `π ∘ TΘ = Id_{X_∞}` holds definitionally.  The characterization in Theorem 9.2.1 is by
  construction: objects and morphisms of `TΘ` are given by (1) and (2).
* The independence in (1) is the hypothesis `HasIndependentTangentSums` of `theorem_9_2_1`; it
  is proved (a) at good points outright, (b) in the equidimensional case from tangent slices, and
  (c) in general from (b) and the agreement of the dimensional decompositions (Proposition
  9.1.12, stated in `Propositions.lean` but not proved).  In place of Proposition 9.2.8 and its
  finite induction we count over a slice: for a class `L` of tangent spaces, a set `F` near `x`
  meeting each `Mᵢ` with `T_xMᵢ = L` once and missing the other `Mᵢ` gives
  `∑_{T_xMᵢ = L} σᵢ = ∑_{y ∈ F} Θ(y)`, which is intrinsic.  The existence of such `F`
  (`HasTangentSlicesAt`) is the chart fact behind Lemmas 9.2.9–9.2.11 (a cone around `h₀` and the
  graph representation), taken as a hypothesis.
* Transport along morphisms (Definition 9.2.12): `LocalBranchingStructure.transport` uses the
  sheet's `φ̂` and `Θ ∘ φ̂ = Θ`.
* Definition 9.2.12 reads `h ∈ TMᵢ` as `h ∈ T_{p(h)}Mᵢ` (`tangentSubmanifold`).  That `TΘ` is a
  branched ep⁺-subgroupoid needs Part I facts about the `TMᵢ` (smooth finite-dimensional
  submanifolds of `TX` of smooth points, closed in `TU(x)`) and the paracompactness of
  `|supp(TΘ)|`, which the text does not discuss; these form `TangentBranchingHyp`.
* Possible misprints: "This completes the proof of Theorem 9.2.8" (p. 418) is presumably Theorem
  9.2.1; "it suffices to prove the proposition" (p. 410) refers to Theorem 9.2.1; in
  `∑_{i ∈ I | y ∈ M_j} σᵢ · T_yMᵢ` (p. 418) the index is presumably `i`; the introduction (p. 408)
  calls `TΘ : TX → ℚ⁺` a "branched ep-subgroupoid", Definition 9.2.12 an ep⁺-subgroupoid.

## Not formalized, and why

* **Proposition 9.2.8 and Lemmas 9.2.9–9.2.11** (the graph representation of the `Mᵢ` over a cone
  in `T_xMᵢ ∩ C`, the inversion of `a ↦ a + PA(a)a`, the sequences of good points): they need
  sc-complements, the mean value formula for sc⁺-retractions and an inverse function argument
  inside a partial quadrant, none of which is available for Part I's tangent spaces.  Their
  content enters as `HasTangentSlicesAt`, proved only for `ℝ⁰`.
* The Part I facts in `TangentBranchingHyp`, proved only for `Θ = 0`.
* The chart description of `submanifoldTangent` (its image under a tangent chart map is the
  tangent space `T_z(φ(W ∩ A))` of the sub-retract, Remark 4.14, `remark_4_2_2`): not needed for
  the results here, which use only the data independence and the calculus of
  `submanifoldTangent`; it is what would identify the generators of `TΘ(x)` as linear
  subspaces.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### The tangent set `T_yA` of a smooth finite-dimensional submanifold -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **The chain rule on open sets, in the form used below**: for `f` sc-smooth on `U`, `g`
sc-smooth on `V`, `h` sc-smooth on `U'`, an open `W ⊆ U ∩ U'` with `f(W) ⊆ V` and `g ∘ f = h` on
`W`, `Tg (Tf α) = Th α` over `W`. -/
theorem tangentMapOn_tangentMapOn_eq {f g h : X → X} {U V U' W : Set X}
    (hf : P.IsScSmoothOn P f U) (hg : P.IsScSmoothOn P g V) (hh : P.IsScSmoothOn P h U')
    (hW : IsOpen W) (hWU : W ⊆ U) (hWU' : W ⊆ U') (hfW : MapsTo f W V)
    (heq : EqOn (g ∘ f) h W) {α : P.TangentSpace} (hα : α ∈ P.tangentPreimage W) :
    tangentMapOn hg (tangentMapOn hf α) = tangentMapOn hh α := by
  have hfW' : P.IsScSmoothOn P f W := hf.mono hW hWU
  have h1 := tangentMapOn_comp hg hfW' hfW hα
  have h2 : tangentMapOn hfW' α = tangentMapOn hf α := tangentMapOn_mono hf hW hWU hα
  have h3 : tangentMapOn (hg.comp hfW' hfW) α = tangentMapOn hh α :=
    tangentMapOn_congr _ _ hW subset_rfl hWU' heq hα
  rw [Function.comp_apply, h2] at h1
  rw [← h1, h3]

namespace SubmanifoldData

variable {A : Set X} (d : P.SubmanifoldData A)

/-- `Ts : TV → TV`, the tangent map of the sc⁺-retraction `s : V → V` of the data. -/
def tmap : P.TangentSpace → P.TangentSpace :=
  tangentMapOn d.isScPlusRetractionOn.isScSmoothOn

theorem levelVal_tangentProj_tmap {α : P.TangentSpace} (hα : α ∈ P.tangentPreimage d.V) :
    P.levelVal 1 (P.tangentProj (d.tmap α)) = d.s (P.levelVal 1 (P.tangentProj α)) :=
  levelVal_tangentProj_tangentMapOn _ hα

/-- The same retraction, for a set `A'` with `A ∩ V = A' ∩ V`. -/
def congrSet {A' : Set X} (h : A ∩ d.V = A' ∩ d.V) : P.SubmanifoldData A' where
  V := d.V
  s := d.s
  isOpen := d.isOpen
  isScPlusRetractionOn := d.isScPlusRetractionOn
  image := d.image.trans h

@[simp] theorem congrSet_V {A' : Set X} (h : A ∩ d.V = A' ∩ d.V) : (d.congrSet h).V = d.V := rfl

theorem tmap_congrSet {A' : Set X} (h : A ∩ d.V = A' ∩ d.V) : (d.congrSet h).tmap = d.tmap := rfl

/-- The data restricted to an open set `V'`: the open set `W = V ∩ V' ∩ s⁻¹(V ∩ V')`
(as in `IsSmoothSubmanifold.exists_subset`), the same retraction. -/
def restrict {V' : Set X} (hV' : IsOpen V') : P.SubmanifoldData A where
  V := d.V ∩ V' ∩ d.s ⁻¹' (d.V ∩ V')
  s := d.s
  isOpen := (d.isScPlusRetractionOn.isScSmoothOn.continuousOn.mono inter_subset_left)
    |>.isOpen_inter_preimage (d.isOpen.inter hV') (d.isOpen.inter hV')
  isScPlusRetractionOn := by
    have hWo : IsOpen (d.V ∩ V' ∩ d.s ⁻¹' (d.V ∩ V')) :=
      (d.isScPlusRetractionOn.isScSmoothOn.continuousOn.mono inter_subset_left)
        |>.isOpen_inter_preimage (d.isOpen.inter hV') (d.isOpen.inter hV')
    refine d.isScPlusRetractionOn.mono hWo (fun y hy => hy.1.1) fun y hy => ?_
    refine ⟨⟨d.isScPlusRetractionOn.mapsTo hy.1.1, hy.2.2⟩, ?_⟩
    change d.s (d.s y) ∈ d.V ∩ V'
    rw [d.isScPlusRetractionOn.idem y hy.1.1]
    exact hy.2
  image := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hz : d.s y ∈ d.s '' d.V := ⟨y, hy.1.1, rfl⟩
      rw [d.image] at hz
      refine ⟨hz.1, ⟨hz.2, hy.2.2⟩, ?_⟩
      change d.s (d.s y) ∈ d.V ∩ V'
      rw [d.isScPlusRetractionOn.idem y hy.1.1]
      exact hy.2
    · rintro ⟨hzA, hz⟩
      refine ⟨z, hz, ?_⟩
      exact d.apply_eq_self ⟨hzA, hz.1.1⟩

theorem restrict_V_subset {V' : Set X} (hV' : IsOpen V') : (d.restrict hV').V ⊆ V' :=
  fun _ hy => hy.1.2

theorem mem_restrict_V {V' : Set X} (hV' : IsOpen V') {y : X} (hyA : y ∈ A) (hyV : y ∈ d.V)
    (hyV' : y ∈ V') : y ∈ (d.restrict hV').V :=
  ⟨⟨hyV, hyV'⟩, by
    change d.s y ∈ d.V ∩ V'
    rw [d.apply_eq_self ⟨hyA, hyV⟩]
    exact ⟨hyV, hyV'⟩⟩

theorem tmap_restrict {V' : Set X} (hV' : IsOpen V') {α : P.TangentSpace}
    (hα : α ∈ P.tangentPreimage (d.restrict hV').V) : (d.restrict hV').tmap α = d.tmap α :=
  tangentMapOn_mono d.isScPlusRetractionOn.isScSmoothOn (d.restrict hV').isOpen
    (fun _ hy => hy.1.1) hα

/-- A vector fixed by `Ts` lies over a point of `A`. -/
theorem mem_of_tmap_eq {α : P.TangentSpace} (hα : α ∈ P.tangentPreimage d.V)
    (hfix : d.tmap α = α) : P.levelVal 1 (P.tangentProj α) ∈ A := by
  have h := d.levelVal_tangentProj_tmap hα
  rw [hfix] at h
  rw [h]
  have : d.s (P.levelVal 1 (P.tangentProj α)) ∈ d.s '' d.V := ⟨_, hα, rfl⟩
  rw [d.image] at this
  exact this.1

/-- **Independence of the data**: a vector over `y ∈ V ∩ V'` fixed by `Ts` is fixed by `Ts'` for
any other data `(V', s')` of `A` (`s' ∘ s = s` near `y`, and the chain rule). -/
theorem tmap_eq_of_tmap_eq (d' : P.SubmanifoldData A) {α : P.TangentSpace}
    (hα : α ∈ P.tangentPreimage d.V) (hα' : α ∈ P.tangentPreimage d'.V) (hfix : d.tmap α = α) :
    d'.tmap α = α := by
  have hs := d.isScPlusRetractionOn.isScSmoothOn
  set y := P.levelVal 1 (P.tangentProj α)
  have hy : d.s y = y := by
    have h := d.levelVal_tangentProj_tmap hα
    rw [hfix] at h
    exact h.symm
  set W := d.V ∩ d.s ⁻¹' d'.V
  have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage d.isOpen d'.isOpen
  have hαW : α ∈ P.tangentPreimage W := ⟨hα, by change d.s y ∈ d'.V; rw [hy]; exact hα'⟩
  have heq : EqOn (d'.s ∘ d.s) d.s W := fun w hw => by
    have h1 : d.s w ∈ d.s '' d.V := ⟨w, hw.1, rfl⟩
    rw [d.image] at h1
    exact d'.apply_eq_self ⟨h1.1, hw.2⟩
  have h := tangentMapOn_tangentMapOn_eq hs d'.isScPlusRetractionOn.isScSmoothOn hs hW
    inter_subset_left inter_subset_left (fun w hw => hw.2) heq hαW
  change tangentMapOn _ (d.tmap α) = d.tmap α at h
  rw [hfix] at h
  exact h

end SubmanifoldData

variable (P) in
/-- **The tangent space `T_yA ⊆ T_yX` of a smooth finite-dimensional submanifold** (Remark 4.14:
`T_yA = Ts(y)(T_yX)`, 2021 §9.2 p. 409), as a subset of Part I's tangent bundle `TX`: the
vectors over `y` fixed by `Ts` for the sc⁺-retraction `s` of some data of Definition 4.13 at `y`
(by `SubmanifoldData.tmap_eq_of_tmap_eq` the choice of the data does not matter; the fixed
vectors of the idempotent `Ts(y)` form its image).  It needs no linear structure on `T_yX`
(gap G.7).  Its chart description (Remark 4.14 in a chart, `remark_4_2_2`) is not formalized
here. -/
def submanifoldTangent (A : Set X) (y : X) : Set P.TangentSpace :=
  {α | P.levelVal 1 (P.tangentProj α) = y ∧ ∃ d : P.SubmanifoldData A, y ∈ d.V ∧ d.tmap α = α}

/-- `T_yA` computed with any data of Definition 4.13 at `y`. -/
theorem mem_submanifoldTangent_iff {A : Set X} (d : P.SubmanifoldData A) {y : X} (hy : y ∈ d.V)
    {α : P.TangentSpace} :
    α ∈ P.submanifoldTangent A y ↔ P.levelVal 1 (P.tangentProj α) = y ∧ d.tmap α = α := by
  constructor
  · rintro ⟨hα, d', hy', hfix⟩
    have hαd : α ∈ P.tangentPreimage d.V := by change _ ∈ d.V; rw [hα]; exact hy
    have hαd' : α ∈ P.tangentPreimage d'.V := by change _ ∈ d'.V; rw [hα]; exact hy'
    exact ⟨hα, d'.tmap_eq_of_tmap_eq d hαd' hαd hfix⟩
  · rintro ⟨hα, hfix⟩
    exact ⟨hα, d, hy, hfix⟩

theorem levelVal_tangentProj_of_mem {A : Set X} {y : X} {α : P.TangentSpace}
    (h : α ∈ P.submanifoldTangent A y) : P.levelVal 1 (P.tangentProj α) = y := h.1

/-- `T_yA = ∅` unless `y ∈ A`. -/
theorem mem_of_mem_submanifoldTangent {A : Set X} {y : X} {α : P.TangentSpace}
    (h : α ∈ P.submanifoldTangent A y) : y ∈ A := by
  obtain ⟨hα, d, hy, hfix⟩ := h
  have hαd : α ∈ P.tangentPreimage d.V := by change _ ∈ d.V; rw [hα]; exact hy
  have := d.mem_of_tmap_eq hαd hfix
  rwa [hα] at this

/-- `T_yA ⊆ T_yX`. -/
theorem submanifoldTangent_subset_tangentFiber {A : Set X} {y : X} (hy : y ∈ P.levelSet 1) :
    P.submanifoldTangent A y ⊆ P.tangentFiber (P.levelMk 1 y hy) := fun _ hα =>
  level_ext (by rw [hα.1, levelVal_levelMk])

theorem submanifoldTangent_subset_of_inter_eq {A A' V : Set X} (hV : IsOpen V) {y : X}
    (hyV : y ∈ V) (h : A ∩ V = A' ∩ V) :
    P.submanifoldTangent A y ⊆ P.submanifoldTangent A' y := by
  intro α hα
  have hyA : y ∈ A := mem_of_mem_submanifoldTangent hα
  obtain ⟨hαy, d, hy, hfix⟩ := hα
  set d₁ := d.restrict hV
  have hy₁ : y ∈ d₁.V := d.mem_restrict_V hV hyA hy hyV
  have hα₁ : α ∈ P.tangentPreimage d₁.V := by change _ ∈ d₁.V; rw [hαy]; exact hy₁
  have hfix₁ : d₁.tmap α = α := (d.tmap_restrict hV hα₁).trans hfix
  have hA : A ∩ d₁.V = A' ∩ d₁.V := by
    have hsub := d.restrict_V_subset hV
    rw [← inter_eq_right.2 hsub, ← inter_assoc, h, inter_assoc]
  exact ⟨hαy, d₁.congrSet hA, hy₁, hfix₁⟩

/-- **`T_yA` is a germ**: if `A` and `A'` agree near `y`, `T_yA = T_yA'`. -/
theorem submanifoldTangent_congr {A A' V : Set X} (hV : IsOpen V) {y : X} (hyV : y ∈ V)
    (h : A ∩ V = A' ∩ V) : P.submanifoldTangent A y = P.submanifoldTangent A' y :=
  Subset.antisymm (submanifoldTangent_subset_of_inter_eq hV hyV h)
    (submanifoldTangent_subset_of_inter_eq hV hyV h.symm)

/-- `T_y(A ∩ V) = T_yA` for `V` open, `y ∈ V`. -/
theorem submanifoldTangent_inter_isOpen {A V : Set X} (hV : IsOpen V) {y : X} (hyV : y ∈ V) :
    P.submanifoldTangent (A ∩ V) y = P.submanifoldTangent A y :=
  submanifoldTangent_congr hV hyV (by rw [inter_assoc, inter_self])

/-- One inclusion of `T_{f(a)}(f(A)) = Tf(T_aA)`. -/
theorem image_submanifoldTangent_subset {f g : X → X} {U U' : Set X}
    (hf : P.IsScDiffeoOn P f g U U') {A : Set X} (hfA : P.IsSmoothSubmanifold (f '' A))
    (hAU : A ⊆ U) {a : X} (ha : a ∈ A) :
    tangentMapOn hf.isScSmoothOn '' P.submanifoldTangent A a ⊆
      P.submanifoldTangent (f '' A) (f a) := by
  rintro _ ⟨α, hα, rfl⟩
  obtain ⟨hαa, d, hy, hfix⟩ := hα
  set d' := hfA.data ⟨a, ha, rfl⟩
  have hfa' : f a ∈ d'.V := hfA.mem_data_V ⟨a, ha, rfl⟩
  have hs := d.isScPlusRetractionOn.isScSmoothOn
  have hsa : d.s a = a := d.apply_eq_self ⟨ha, hy⟩
  set W := (d.V ∩ U) ∩ d.s ⁻¹' (U ∩ f ⁻¹' d'.V)
  have hW : IsOpen W := (hs.continuousOn.mono inter_subset_left).isOpen_inter_preimage
    (d.isOpen.inter hf.isScSmoothOn.isOpen)
    (hf.isScSmoothOn.continuousOn.isOpen_inter_preimage hf.isScSmoothOn.isOpen d'.isOpen)
  have haW : a ∈ W := ⟨⟨hy, hAU ha⟩, by
    change d.s a ∈ U ∩ f ⁻¹' d'.V; rw [hsa]; exact ⟨hAU ha, hfa'⟩⟩
  have hαW : α ∈ P.tangentPreimage W := by change _ ∈ W; rw [hαa]; exact haW
  have hfs : P.IsScSmoothOn P (f ∘ d.s) W :=
    hf.isScSmoothOn.comp (hs.mono hW fun _ hw => hw.1.1) fun w hw => hw.2.1
  -- `T(f ∘ s) α = Tf (Ts α) = Tf α`
  have h1 : tangentMapOn hf.isScSmoothOn (d.tmap α) = tangentMapOn hfs α :=
    tangentMapOn_tangentMapOn_eq hs hf.isScSmoothOn hfs hW (fun _ hw => hw.1.1) subset_rfl
      (fun w hw => hw.2.1) (fun _ _ => rfl) hαW
  rw [hfix] at h1
  -- `s' ∘ (f ∘ s) = f ∘ s` on `W`
  have heq : EqOn (d'.s ∘ (f ∘ d.s)) (f ∘ d.s) W := fun w hw => by
    have h2 : d.s w ∈ d.s '' d.V := ⟨w, hw.1.1, rfl⟩
    rw [d.image] at h2
    exact d'.apply_eq_self ⟨⟨d.s w, h2.1, rfl⟩, hw.2.2⟩
  have h3 := tangentMapOn_tangentMapOn_eq hfs d'.isScPlusRetractionOn.isScSmoothOn hfs hW
    subset_rfl subset_rfl (fun w hw => hw.2.2) heq hαW
  have hbase : P.levelVal 1 (P.tangentProj (tangentMapOn hf.isScSmoothOn α)) = f a := by
    rw [levelVal_tangentProj_tangentMapOn _ (show α ∈ P.tangentPreimage U from by
      change _ ∈ U; rw [hαa]; exact hAU ha), hαa]
  refine ⟨hbase, d', hfa', ?_⟩
  change tangentMapOn _ (tangentMapOn hf.isScSmoothOn α) = tangentMapOn hf.isScSmoothOn α
  rw [h1, h3]

/-- `Tf ∘ Tg = id` over `U'` for an sc-diffeomorphism `f : U → U'` with inverse `g`. -/
theorem IsScDiffeoOn.tangentMapOn_tangentMapOn_inv {f g : X → X} {U U' : Set X}
    (hf : P.IsScDiffeoOn P f g U U') {β : P.TangentSpace} (hβ : β ∈ P.tangentPreimage U') :
    tangentMapOn hf.isScSmoothOn (tangentMapOn hf.isScSmoothOn_inv β) = β := by
  have hfg : P.IsScSmoothOn P (f ∘ g) U' := hf.isScSmoothOn.comp hf.isScSmoothOn_inv hf.mapsTo_inv
  rw [tangentMapOn_tangentMapOn_eq hf.isScSmoothOn_inv hf.isScSmoothOn hfg
    hf.isScSmoothOn_inv.isOpen subset_rfl subset_rfl hf.mapsTo_inv (fun _ _ => rfl) hβ]
  exact tangentMapOn_eqOn_id hfg (fun y hy => hf.right_inv y hy) hβ

/-- **The tangent space of the image of a submanifold under an sc-diffeomorphism**:
`T_{f(a)}(f(A)) = Tf(T_aA)` for `f : U → U'` an sc-diffeomorphism and `A ⊆ U`. -/
theorem submanifoldTangent_image {f g : X → X} {U U' : Set X} (hf : P.IsScDiffeoOn P f g U U')
    {A : Set X} (hA : P.IsSmoothSubmanifold A) (hAU : A ⊆ U) {a : X} (ha : a ∈ A) :
    P.submanifoldTangent (f '' A) (f a) =
      tangentMapOn hf.isScSmoothOn '' P.submanifoldTangent A a := by
  have hfA := hA.image_of_isScDiffeoOn hf hAU
  refine Subset.antisymm (fun β hβ => ?_) (image_submanifoldTangent_subset hf hfA hAU ha)
  have hfAU' : f '' A ⊆ U' := image_subset_iff.2 fun y hy => hf.mapsTo (hAU hy)
  have hgf : g '' (f '' A) = A := by
    rw [image_image]
    exact (image_congr fun y hy => hf.left_inv y (hAU hy)).trans (image_id' A)
  have hga : g (f a) = a := hf.left_inv a (hAU ha)
  have h := image_submanifoldTangent_subset hf.symm (hgf.symm ▸ hA) hfAU' ⟨a, ha, rfl⟩
  rw [hgf, hga] at h
  have hβU' : β ∈ P.tangentPreimage U' := by
    change _ ∈ U'; rw [hβ.1]; exact hf.mapsTo (hAU ha)
  exact ⟨_, h ⟨β, hβ, rfl⟩, hf.tangentMapOn_tangentMapOn_inv hβU'⟩

end MPolyfold

/-! ### Tangent slices (the Part I fact behind Lemmas 9.2.9–9.2.11) -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

variable (P : MPolyfold X) in
/-- **Tangent slices at `x` in dimension `n`** (the Part I fact used in the proof of Theorem
9.2.1, 2021 Lemmas 9.2.9–9.2.11, pp. 414–415; 2017: Lemmas 9.6–9.8): for finitely many
`n`-dimensional submanifolds `A_k` through `x`, one of them `A_{k₀}`, and an open `W ∋ x`, there
is a set `F ⊆ W` meeting every `A_k` with `T_xA_k = T_xA_{k₀}` in exactly one point and missing
every other `A_k`.  In a chart one takes, for `L = T_xA_{k₀}`, a complement `C` and a vector
`h₀ ∈ L` outside the finitely many proper subspaces `L ∩ T_xA_k`, and `F` the piece of the fibre
`h₀ t + C` near `h₀ t` (a sector), `t > 0` small (the graph representation of Lemmas 9.2.9 and
9.2.10).  Not proved here; satisfiable (`hasTangentSlicesAt_rn_zero`). -/
def HasTangentSlicesAt (x : X) (n : ℕ) : Prop :=
  ∀ (κ : Type u) [Fintype κ] (A : κ → Set X), (∀ k, P.IsSubmanifoldOfDim (A k) n) →
    (∀ k, x ∈ A k) → ∀ (k₀ : κ) (W : Set X), IsOpen W → x ∈ W → ∃ F ⊆ W, ∀ k,
      (P.submanifoldTangent (A k) x = P.submanifoldTangent (A k₀) x → ∃! y, y ∈ F ∩ A k) ∧
      (P.submanifoldTangent (A k) x ≠ P.submanifoldTangent (A k₀) x → F ∩ A k = ∅)

end MPolyfold

/-- **Satisfiability of `HasTangentSlicesAt`**: in the M-polyfold `ℝ⁰` (one point) every
submanifold through `x` is `{x}`, and `F = {x}` is a slice. -/
theorem hasTangentSlicesAt_rn_zero (x : Fin 0 → ℝ) (n : ℕ) :
    (rnPolyfold 0).HasTangentSlicesAt x n := by
  intro κ _ A _ hx k₀ W _ hxW
  have hA : ∀ k, A k = univ := fun k => eq_univ_of_forall fun y => by
    rw [Subsingleton.elim y x]; exact hx k
  refine ⟨({x} : Set (Fin 0 → ℝ)), singleton_subset_iff.2 hxW,
    fun k => ⟨fun _ => ⟨x, ⟨rfl, hx k⟩, fun y hy => hy.1⟩,
    fun h => (h (by rw [hA k, hA k₀])).elim⟩⟩

/-! ### `Tφ` on fibres, and through the sheet -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- `Tφ` maps `T_{s φ}X` into `T_{t φ}X`. -/
theorem levelVal_tangentProj_tangentMor {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1)
    {α : X.PObj.TangentSpace} (hα : X.PObj.levelVal 1 (X.PObj.tangentProj α) = X.src φ) :
    X.PObj.levelVal 1 (X.PObj.tangentProj (X.tangentMor φ α)) = X.tgt φ := by
  obtain ⟨v, rfl, rfl⟩ := X.exists_tSrc_eq' hφ hα
  rw [X.tangentMor_tSrc, X.levelVal_tangentProj_tTgt]

/-- `T1_x = id` on `T_xX`. -/
theorem tangentMor_unit_of_eq {x : Obj} {α : X.PObj.TangentSpace}
    (hα : X.PObj.levelVal 1 (X.PObj.tangentProj α) = x) : X.tangentMor (X.unit x) α = α := by
  subst hα
  have h := X.tangentMor_tSrc (X.tUnit α)
  rwa [X.tBase_tUnit, X.tSrc_tUnit, X.tTgt_tUnit] at h

/-- `Tφ⁻¹ ∘ Tφ = id` on `T_{s φ}X`. -/
theorem tangentMor_inv_tangentMor {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1)
    {α : X.PObj.TangentSpace} (hα : X.PObj.levelVal 1 (X.PObj.tangentProj α) = X.src φ) :
    X.tangentMor (X.inv φ) (X.tangentMor φ α) = α := by
  rw [← X.tangentMor_comp hφ (X.src_inv φ) hα, X.inv_comp, X.tangentMor_unit_of_eq hα]

/-- `Tφ` is injective on `T_{s φ}X`. -/
theorem tangentMor_injOn {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) :
    InjOn (X.tangentMor φ) {α | X.PObj.levelVal 1 (X.PObj.tangentProj α) = X.src φ} :=
  fun a ha b hb h => by
    rw [← X.tangentMor_inv_tangentMor hφ ha, h, X.tangentMor_inv_tangentMor hφ hb]

/-- **`Tφ = Tφ̂(s φ)`**: Chapter 7's `tangentMor` (`Tt ∘ (Ts|T_φ𝐗)⁻¹`) is the tangent map of
the local sc-diffeomorphism `φ̂ = t ∘ (s|𝐔)⁻¹` of the chosen sheet, on `T_{s φ}X`. -/
theorem tangentMor_eq_tangentMapOn_hat {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1)
    {α : X.PObj.TangentSpace} (hα : X.PObj.levelVal 1 (X.PObj.tangentProj α) = X.src φ) :
    X.tangentMor φ α = MPolyfold.tangentMapOn (X.isScDiffeoOn_hat φ).isScSmoothOn α := by
  obtain ⟨v, hv, rfl⟩ := X.exists_tSrc_eq' hφ hα
  have hd := (X.sheetAt φ).isScDiffeoOn_src
  have hvS : X.tBase v ∈ (X.sheetAt φ).carrier := by rw [hv]; exact X.mem_sheetAt φ
  have hαS : X.tSrc v ∈ X.PObj.tangentPreimage (X.sheetAt φ).srcSet := by
    change X.PObj.levelVal 1 (X.PObj.tangentProj (X.tSrc v)) ∈ (X.sheetAt φ).srcSet
    rw [X.levelVal_tangentProj_tSrc]; exact hd.mapsTo hvS
  have key : X.tangentMor (X.tBase v) (X.tSrc v) = X.tTgt v := X.tangentMor_tSrc v
  rw [hv] at key
  rw [key]
  have h1 := MPolyfold.tangentMap_tangentMapOn X.isScSmoothMap_tgt hd.isScSmoothOn_inv hαS
  rw [tangentMapOn_srcInv_tSrc hd hvS] at h1
  change MPolyfold.tangentMap X.isScSmoothMap_tgt v = _
  rw [h1]
  exact MPolyfold.tangentMapOn_congr _ _ hd.isScSmoothOn_inv.isOpen subset_rfl subset_rfl
    (fun _ _ => rfl) hαS

/-! ### `Gr(x)`, `Gr(X)` and the projection functor (2021 p. 409) -/

variable (X) in
/-- **`Gr(x)`** (2021 p. 409; 2017: p. 297): the finite formal sums `∑ σ_L · L` with rational
`σ_L ≥ 0`, as finitely supported weights on subsets `L ⊆ T_xX` (the vectors of `L` lie over
`x`).  The text's generators are the smooth finite-dimensional linear subspaces of `T_xX`; with
no linear structure on Part I's `T_xX` (gap G.7) we allow all subsets, and the values of `TΘ`
are the `T_xMᵢ`, which are such subspaces in a chart (Remark 4.14). -/
def Gr (x : Obj) : Set (Set X.PObj.TangentSpace →₀ ℚ) :=
  {w | (∀ L, 0 ≤ w L) ∧ ∀ L ∈ w.support, ∀ α ∈ L, X.PObj.levelVal 1 (X.PObj.tangentProj α) = x}

theorem zero_mem_Gr (x : Obj) : (0 : Set X.PObj.TangentSpace →₀ ℚ) ∈ X.Gr x :=
  ⟨fun _ => le_rfl, fun L hL => by simp at hL⟩

variable (X) in
/-- The target `t(∑ σ_L · L, φ) = ∑ σ_L · Tφ(L)` of a morphism of `Gr(X)` (2021 p. 409). -/
def grPush (φ : Mor) (w : Set X.PObj.TangentSpace →₀ ℚ) : Set X.PObj.TangentSpace →₀ ℚ :=
  w.mapDomain (image (X.tangentMor φ))

theorem grPush_mem {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) {w : Set X.PObj.TangentSpace →₀ ℚ}
    (hw : w ∈ X.Gr (X.src φ)) : X.grPush φ w ∈ X.Gr (X.tgt φ) := by
  classical
  refine ⟨fun L => ?_, fun L hL α hα => ?_⟩
  · rw [grPush, Finsupp.mapDomain, Finsupp.sum_apply]
    refine Finset.sum_nonneg fun L' _ => ?_
    dsimp only
    rw [Finsupp.single_apply]
    split_ifs
    · exact hw.1 L'
    · exact le_rfl
  · obtain ⟨L', hL', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hL)
    obtain ⟨β, hβ, rfl⟩ := hα
    exact X.levelVal_tangentProj_tangentMor hφ (hw.2 L' hL' β hβ)

theorem grPush_comp {φ ψ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) (hψφ : X.src ψ = X.tgt φ)
    {w : Set X.PObj.TangentSpace →₀ ℚ} (hw : w ∈ X.Gr (X.src φ)) :
    X.grPush (X.comp ψ φ) w = X.grPush ψ (X.grPush φ w) := by
  rw [grPush, grPush, grPush, ← Finsupp.mapDomain_comp]
  refine Finsupp.mapDomain_congr fun L hL => ?_
  rw [Function.comp_apply, image_image]
  exact image_congr fun α hα => X.tangentMor_comp hφ hψφ (hw.2 L hL α hα)

theorem grPush_unit {x : Obj} {w : Set X.PObj.TangentSpace →₀ ℚ} (hw : w ∈ X.Gr x) :
    X.grPush (X.unit x) w = w := by
  rw [grPush]
  conv_rhs => rw [← Finsupp.mapDomain_id (v := w)]
  exact Finsupp.mapDomain_congr fun L hL =>
    (image_congr fun α hα => X.tangentMor_unit_of_eq (hw.2 L hL α hα)).trans (image_id L)

variable (X) in
/-- **An object of `Gr(X) = ⋃_{x ∈ X_∞} Gr(x)`** (2021 p. 409): a smooth object `x` with a
formal sum in `Gr(x)`. -/
structure GrObj where
  /-- The base point `π(L) = x`. -/
  pt : Obj
  smooth : pt ∈ X.PObj.smoothSet
  /-- The formal sum `L = ∑ σ_L · L`. -/
  sum : Set X.PObj.TangentSpace →₀ ℚ
  mem : sum ∈ X.Gr pt

/-- A morphism of `Gr(X)` with `s φ ∈ X_∞` lies in `𝐗_∞` (`ml(s φ) = ml(φ)`). -/
theorem mem_smoothSet_of_src {φ : Mor} (h : X.src φ ∈ X.PObj.smoothSet) :
    φ ∈ X.PMor.smoothSet :=
  mem_iInter.2 fun m => (X.mem_levelSet_src_iff φ m).1 (mem_iInter.1 h m)

theorem mem_levelSet_one_of_src {φ : Mor} (h : X.src φ ∈ X.PObj.smoothSet) :
    φ ∈ X.PMor.levelSet 1 :=
  (X.mem_levelSet_src_iff φ 1).1 (mem_iInter.1 h 1)

/-- **The category `Gr(X)`** (2021 p. 409): a morphism `(L, φ) : L → L'` is `φ ∈ 𝐗_∞`
(automatic: `mem_smoothSet_of_src`) with `s φ = π(L)`, `t φ = π(L')` and
`L' = ∑ σ_L · Tφ(L)`; `(L, ψ) ∘ (K, φ) = (K, ψ ∘ φ)`, identities `(L, 1_{π(L)})`. -/
instance : Category.{u} X.GrObj where
  Hom a b := {φ : Mor // X.src φ = a.pt ∧ X.tgt φ = b.pt ∧ X.grPush φ a.sum = b.sum}
  id a := ⟨X.unit a.pt, X.src_unit _, X.tgt_unit _, X.grPush_unit a.mem⟩
  comp {a b c} f g := ⟨X.comp g.1 f.1,
    (X.src_comp _ _ (g.2.1.trans f.2.2.1.symm)).trans f.2.1,
    (X.tgt_comp _ _ (g.2.1.trans f.2.2.1.symm)).trans g.2.2.1, by
      have hf1 : f.1 ∈ X.PMor.levelSet 1 :=
        X.mem_levelSet_one_of_src (by rw [f.2.1]; exact a.smooth)
      have hw : a.sum ∈ X.Gr (X.src f.1) := by rw [f.2.1]; exact a.mem
      rw [X.grPush_comp hf1 (g.2.1.trans f.2.2.1.symm) hw, f.2.2.2, g.2.2.2]⟩
  id_comp f := Subtype.ext (GroupoidStr.comp_unit_of_eq (G := X.toGroupoidStr) f.2.1)
  comp_id f := Subtype.ext (GroupoidStr.unit_comp_of_eq (G := X.toGroupoidStr) f.2.2.1)
  assoc f g h := Subtype.ext (X.comp_assoc _ _ _ (h.2.1.trans g.2.2.1.symm)
    (g.2.1.trans f.2.2.1.symm)).symm

@[simp] theorem GrObj.comp_val {a b c : X.GrObj} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).1 = X.comp g.1 f.1 := rfl

@[simp] theorem GrObj.id_val (a : X.GrObj) : (𝟙 a : a ⟶ a).1 = X.unit a.pt := rfl

variable (X) in
/-- `X_∞` as a category: the full subcategory of the smooth objects (Chapter 7's `fullSub`,
through the bridge `GroupoidStr.Ob`). -/
abbrev SmoothCat : Type u := (X.toGroupoidStr.fullSub X.PObj.smoothSet).Ob

/-- The object of `X` underlying an object of `X_∞`. -/
def SmoothCat.pt (x : X.SmoothCat) : Obj := (x : X.PObj.smoothSet).1

theorem SmoothCat.smooth (x : X.SmoothCat) : x.pt ∈ X.PObj.smoothSet := (x : X.PObj.smoothSet).2

/-- The morphism of `X` underlying a morphism of `X_∞`. -/
def SmoothCat.mor {x y : X.SmoothCat} (f : x ⟶ y) : Mor := f.1.1

theorem SmoothCat.src_mor {x y : X.SmoothCat} (f : x ⟶ y) : X.src (SmoothCat.mor f) = x.pt :=
  congrArg Subtype.val f.2.1

theorem SmoothCat.tgt_mor {x y : X.SmoothCat} (f : x ⟶ y) : X.tgt (SmoothCat.mor f) = y.pt :=
  congrArg Subtype.val f.2.2

theorem SmoothCat.mor_comp {x y z : X.SmoothCat} (f : x ⟶ y) (g : y ⟶ z) :
    SmoothCat.mor (f ≫ g) = X.comp (SmoothCat.mor g) (SmoothCat.mor f) := by
  have h : X.src g.1.1 = X.tgt f.1.1 := (SmoothCat.src_mor g).trans (SmoothCat.tgt_mor f).symm
  change ((X.toGroupoidStr.fullSub X.PObj.smoothSet).comp g.1 f.1).1 = _
  simp only [GroupoidStr.fullSub, dif_pos h]
  rfl

theorem SmoothCat.mor_id (x : X.SmoothCat) : SmoothCat.mor (𝟙 x) = X.unit x.pt := rfl

variable (X) in
/-- **The projection functor `π : Gr(X) → X_∞`** (2021 p. 409): `π(L) = x` for `L ∈ Gr(x)`,
`π(L, φ) = φ`. -/
def grProj : X.GrObj ⥤ X.SmoothCat where
  obj a := (⟨a.pt, a.smooth⟩ : X.PObj.smoothSet)
  map {a b} f := ⟨⟨f.1, by rw [f.2.1]; exact a.smooth, by rw [f.2.2.1]; exact b.smooth⟩,
    Subtype.ext f.2.1, Subtype.ext f.2.2.1⟩
  map_id _ := rfl
  map_comp {a b c} f g := by
    apply Subtype.ext
    apply Subtype.ext
    have h : X.src g.1 = X.tgt f.1 := g.2.1.trans f.2.2.1.symm
    change X.comp g.1 f.1 = ((X.toGroupoidStr.fullSub X.PObj.smoothSet).comp _ _).1
    simp only [GroupoidStr.fullSub, dif_pos h]

/-! ### `∑ σᵢ · T_xMᵢ` for a local branching structure -/

namespace LocalBranchingStructure

variable {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x)

/-- **`∑_{i ∈ I} σᵢ · T_xMᵢ ∈ Gr(x)`**, the value of `TΘ` at `x` computed with the local
branching structure `B` (2021 Theorem 9.2.1 (1), p. 410). -/
def tangentSum : Set X.PObj.TangentSpace →₀ ℚ :=
  ∑ i, Finsupp.single (X.PObj.submanifoldTangent (B.M i) x) (B.σ i)

open scoped Classical in
theorem tangentSum_apply (L : Set X.PObj.TangentSpace) :
    B.tangentSum L = ∑ i, if X.PObj.submanifoldTangent (B.M i) x = L then B.σ i else 0 := by
  rw [tangentSum, Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun i _ => Finsupp.single_apply

theorem tangentSum_mem : B.tangentSum ∈ X.Gr x := by
  classical
  refine ⟨fun L => ?_, fun L hL α hα => ?_⟩
  · rw [B.tangentSum_apply]
    exact Finset.sum_nonneg fun i _ => by split_ifs; exacts [(B.σ_pos i).le, le_rfl]
  · have : ∃ i, X.PObj.submanifoldTangent (B.M i) x = L := by
      by_contra h
      push Not at h
      exact (Finsupp.mem_support_iff.1 hL)
        (by rw [B.tangentSum_apply]; exact Finset.sum_eq_zero fun i _ => if_neg (h i))
    obtain ⟨i, rfl⟩ := this
    exact MPolyfold.levelVal_tangentProj_of_mem hα

/-- Off `supp(Θ)` a local branching structure has no submanifolds. -/
theorem isEmpty_of_not_mem (hx : x ∉ supp Θ) : IsEmpty B.ι := by
  classical
  refine ⟨fun i => hx ?_⟩
  change 0 < Θ x
  rw [B.eq_sum x B.mem_U]
  exact lt_of_lt_of_le (B.σ_pos i) (Finset.single_le_sum (fun j _ => (B.σ_pos j).le)
    (Finset.mem_filter.2 ⟨Finset.mem_univ i, B.mem_M i⟩))

/-- Off `supp(Θ)` the sum is the zero-sum. -/
theorem tangentSum_eq_zero (hx : x ∉ supp Θ) : B.tangentSum = 0 := by
  have := B.isEmpty_of_not_mem hx
  rw [tangentSum, Finset.univ_eq_empty, Finset.sum_empty]

/-! #### Good points (Definition 9.2.2): the sum is intrinsic -/

/-- Near a good point `x` of `B` every `Mᵢ` is `supp(Θ)`. -/
theorem exists_eq_supp_of_isGoodPoint (h : B.IsGoodPoint x) :
    ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧ ∀ i, B.M i ∩ V = supp Θ ∩ V := by
  obtain ⟨-, V, hV, hxV, hVU, hVM⟩ := h
  refine ⟨V, hV, hxV, fun i => ?_⟩
  ext z
  constructor
  · rintro ⟨hzi, hzV⟩
    exact ⟨(B.mem_supp_iff (hVU hzV)).2 ⟨i, hzi⟩, hzV⟩
  · rintro ⟨hzs, hzV⟩
    obtain ⟨j, hzj⟩ := (B.mem_supp_iff (hVU hzV)).1 hzs
    have h1 : z ∈ V ∩ B.M j := ⟨hzV, hzj⟩
    rw [hVM j i (B.mem_M j) (B.mem_M i)] at h1
    exact ⟨h1.2, hzV⟩

/-- At a good point all `T_xMᵢ` agree, and `∑ σᵢ · T_xMᵢ = Θ(x) · T_xM_{i₀}`. -/
theorem tangentSum_eq_single_of_isGoodPoint (h : B.IsGoodPoint x) (i₀ : B.ι) :
    B.tangentSum = Finsupp.single (X.PObj.submanifoldTangent (B.M i₀) x) (Θ x) := by
  classical
  obtain ⟨V, hV, hxV, hM⟩ := B.exists_eq_supp_of_isGoodPoint h
  have hT : ∀ i, X.PObj.submanifoldTangent (B.M i) x = X.PObj.submanifoldTangent (B.M i₀) x :=
    fun i => MPolyfold.submanifoldTangent_congr hV hxV ((hM i).trans (hM i₀).symm)
  rw [tangentSum, B.eq_sum x B.mem_U, Finset.filter_true_of_mem fun i _ => B.mem_M i,
    Finsupp.single_finsetSum]
  exact Finset.sum_congr rfl fun i _ => by rw [hT i]

/-- **Theorem 9.2.1 (1) at good points**: if `x` is a good point (Definition 9.2.2), the sum
`∑ σᵢ · T_xMᵢ` does not depend on the local branching structure (Lemma 9.2.3). -/
theorem tangentSum_eq_of_isGoodPoint (B' : X.LocalBranchingStructure Θ x)
    (h : B.IsGoodPoint x) : B.tangentSum = B'.tangentSum := by
  have h' := B.lemma_9_2_3 B' B.mem_U B'.mem_U h
  obtain ⟨i₀, -⟩ := mem_iUnion.1 (show x ∈ ⋃ i, B.M i from h.1)
  obtain ⟨j₀, -⟩ := mem_iUnion.1 (show x ∈ ⋃ j, B'.M j from h'.1)
  rw [B.tangentSum_eq_single_of_isGoodPoint h i₀, B'.tangentSum_eq_single_of_isGoodPoint h' j₀]
  obtain ⟨V, hV, hxV, hM⟩ := B.exists_eq_supp_of_isGoodPoint h
  obtain ⟨V', hV', hxV', hM'⟩ := B'.exists_eq_supp_of_isGoodPoint h'
  congr 1
  refine MPolyfold.submanifoldTangent_congr (hV.inter hV') ⟨hxV, hxV'⟩ ?_
  calc B.M i₀ ∩ (V ∩ V') = (B.M i₀ ∩ V) ∩ V' := (inter_assoc _ _ _).symm
    _ = (supp Θ ∩ V) ∩ V' := by rw [hM i₀]
    _ = (supp Θ ∩ V') ∩ V := by rw [inter_assoc, inter_comm V, ← inter_assoc]
    _ = (B'.M j₀ ∩ V') ∩ V := by rw [hM' j₀]
    _ = B'.M j₀ ∩ (V ∩ V') := by rw [inter_assoc, inter_comm V']

/-! #### The fibre count (the proof of Theorem 9.2.1, after Lemma 9.2.11) -/

open scoped Classical in
/-- **The fibre count**: two `n`-dimensional local branching structures at `x`, for functors
`Θ`, `Θ'` agreeing near `x`, give the same sum `∑ σᵢ · T_xMᵢ`, granted tangent slices at `x`
(`HasTangentSlicesAt`, the content of Lemmas 9.2.9–9.2.11).  For a class `L` of tangent spaces,
a slice `F` meets each `Mᵢ`, `N_j` with tangent `L` once and misses the others, so
`∑_{T_xMᵢ = L} σᵢ = ∑_{y ∈ F} Θ(y) = ∑_{y ∈ F} Θ'(y) = ∑_{T_xN_j = L} τ_j`. -/
theorem tangentSum_eq_of_eqOn {Θ' : Obj → ℚ} (B' : X.LocalBranchingStructure Θ' x) {n : ℕ}
    (hB : B.IsOfDim n) (hB' : B'.IsOfDim n) (hsl : X.PObj.HasTangentSlicesAt x n)
    {W : Set Obj} (hW : IsOpen W) (hxW : x ∈ W) (hΘ : ∀ y ∈ W, Θ y = Θ' y) :
    B.tangentSum = B'.tangentSum := by
  ext L
  rw [B.tangentSum_apply, B'.tangentSum_apply]
  let A : B.ι ⊕ B'.ι → Set Obj := Sum.elim B.M B'.M
  by_cases hL : ∃ k₀, X.PObj.submanifoldTangent (A k₀) x = L
  swap
  · push Not at hL
    have h1 : ∀ i, X.PObj.submanifoldTangent (B.M i) x ≠ L := fun i => hL (Sum.inl i)
    have h2 : ∀ j, X.PObj.submanifoldTangent (B'.M j) x ≠ L := fun j => hL (Sum.inr j)
    simp only [h1, h2, if_false, Finset.sum_const_zero]
  obtain ⟨k₀, hk₀⟩ := hL
  have hAdim : ∀ k, X.PObj.IsSubmanifoldOfDim (A k) n := fun k => by
    cases k with
    | inl i => exact hB i
    | inr j => exact hB' j
  have hAx : ∀ k, x ∈ A k := fun k => by
    cases k with
    | inl i => exact B.mem_M i
    | inr j => exact B'.mem_M j
  have hWo : IsOpen (W ∩ B.U ∩ B'.U) := (hW.inter B.isOpen_U).inter B'.isOpen_U
  obtain ⟨F, hFW, hF⟩ := hsl (B.ι ⊕ B'.ι) A hAdim hAx k₀ _ hWo ⟨⟨hxW, B.mem_U⟩, B'.mem_U⟩
  have hgood : ∀ k, X.PObj.submanifoldTangent (A k) x = L →
      ∃ y, y ∈ F ∩ A k ∧ ∀ y', y' ∈ F ∩ A k → y' = y :=
    fun k hk => (hF k).1 (hk.trans hk₀.symm)
  have hbad : ∀ k, X.PObj.submanifoldTangent (A k) x ≠ L → F ∩ A k = ∅ :=
    fun k hk => (hF k).2 fun h => hk (h.trans hk₀)
  have : Nonempty Obj := ⟨x⟩
  choose! pt hpt hpt_uniq using hgood
  let S : Finset Obj :=
    (Finset.univ.filter fun k => X.PObj.submanifoldTangent (A k) x = L).image pt
  have hSF : ∀ y ∈ S, y ∈ F := fun y hy => by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
    exact (hpt k (Finset.mem_filter.1 hk).2).1
  have hcount : ∀ k (c : ℚ), (∑ y ∈ S, if y ∈ A k then c else 0) =
      if X.PObj.submanifoldTangent (A k) x = L then c else 0 := fun k c => by
    by_cases hk : X.PObj.submanifoldTangent (A k) x = L
    · rw [if_pos hk, Finset.sum_eq_single (pt k)]
      · exact if_pos (hpt k hk).2
      · intro y hyS hne
        exact if_neg fun hyA => hne (hpt_uniq k hk y ⟨hSF y hyS, hyA⟩)
      · intro hn
        exact (hn (Finset.mem_image_of_mem pt
          (Finset.mem_filter.2 ⟨Finset.mem_univ k, hk⟩))).elim
    · rw [if_neg hk]
      refine Finset.sum_eq_zero fun y hy => if_neg fun hyA => ?_
      have h1 : y ∈ F ∩ A k := ⟨hSF y hy, hyA⟩
      rw [hbad k hk] at h1
      exact h1
  have hB1 : (∑ i, if X.PObj.submanifoldTangent (B.M i) x = L then B.σ i else 0) =
      ∑ y ∈ S, Θ y := by
    rw [Finset.sum_congr rfl fun y hy => B.eq_sum y (hFW (hSF y hy)).1.2]
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (hcount (Sum.inl i) (B.σ i)).symm
  have hB2 : (∑ j, if X.PObj.submanifoldTangent (B'.M j) x = L then B'.σ j else 0) =
      ∑ y ∈ S, Θ' y := by
    rw [Finset.sum_congr rfl fun y hy => B'.eq_sum y (hFW (hSF y hy)).2]
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (hcount (Sum.inr j) (B'.σ j)).symm
  rw [hB1, hB2]
  exact Finset.sum_congr rfl fun y hy => hΘ y (hFW (hSF y hy)).1.1

/-- The sum splits along the dimensional decomposition (Proposition 9.1.11):
`∑ σᵢ · T_xMᵢ = ∑_k ∑_{i ∈ I_k} σᵢ · T_xMᵢ`. -/
theorem tangentSum_eq_sum_dimPartStructure (dim : B.ι → ℕ) (K : Finset ℕ)
    (hK : ∀ i, dim i ∈ K) :
    B.tangentSum = ∑ k ∈ K, (B.dimPartStructure dim k).tangentSum := by
  rw [tangentSum, ← Finset.sum_fiberwise_of_maps_to (g := dim) (t := K) (fun i _ => hK i)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tangentSum]
  exact Finset.sum_subtype _ (fun i => by simp)
    (fun i => Finsupp.single (X.PObj.submanifoldTangent (B.M i) x) (B.σ i))

/-- **Theorem 9.2.1 (1), the reduction to the equidimensional case** (the text's
`TΘ = ∑ TΘ_k`, p. 410): if the dimensional
decompositions of two local branching structures agree near `x` (Proposition 9.1.12) and there
are tangent slices at `x`, the two sums agree. -/
theorem tangentSum_eq_of_dimPartsAgreeNear (B' : X.LocalBranchingStructure Θ x)
    {dim : B.ι → ℕ} {dim' : B'.ι → ℕ} (hdim : ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hdim' : ∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j))
    (hagree : DimPartsAgreeNear B B' dim dim') (hsl : ∀ n, X.PObj.HasTangentSlicesAt x n) :
    B.tangentSum = B'.tangentSum := by
  classical
  obtain ⟨V, hV, hxV, -, hVk⟩ := hagree
  let K := Finset.univ.image dim ∪ Finset.univ.image dim'
  rw [B.tangentSum_eq_sum_dimPartStructure dim K
      (fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))),
    B'.tangentSum_eq_sum_dimPartStructure dim' K
      (fun j => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))]
  exact Finset.sum_congr rfl fun k _ => (B.dimPartStructure dim k).tangentSum_eq_of_eqOn
    (B'.dimPartStructure dim' k) (B.dimPartStructure_isOfDim hdim k)
    (B'.dimPartStructure_isOfDim hdim' k) (hsl k) hV hxV (hVk k)

end LocalBranchingStructure

/-! ### Independence of the local branching structure -/

variable (X) in
/-- **The sums `∑ σᵢ · T_xMᵢ` do not depend on the local branching structure** (the content of
2021 Theorem 9.2.1 (1), "where `(Mᵢ)` and `(σᵢ)` is any local branching structure"). -/
def HasIndependentTangentSums (Θ : Obj → ℚ) : Prop :=
  ∀ (x : Obj) (B B' : X.LocalBranchingStructure Θ x), B.tangentSum = B'.tangentSum

/-- **The independence, from Proposition 9.1.12**: if the dimensional decompositions of any two
local branching structures agree near the base point (`DimPartsAgreeNear`, the conclusion of
Proposition 9.1.12, with dimension labellings) and there are tangent slices at the points of
`supp(Θ)` (Lemmas 9.2.9–9.2.11), the sums are independent. -/
theorem hasIndependentTangentSums_of_dimPartsAgreeNear {Θ : Obj → ℚ}
    (h : ∀ (x : Obj) (B B' : X.LocalBranchingStructure Θ x), x ∈ supp Θ →
      ∃ (dim : B.ι → ℕ) (dim' : B'.ι → ℕ), (∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i)) ∧
        (∀ j, X.PObj.IsSubmanifoldOfDim (B'.M j) (dim' j)) ∧
        LocalBranchingStructure.DimPartsAgreeNear B B' dim dim')
    (hsl : ∀ x ∈ supp Θ, ∀ n, X.PObj.HasTangentSlicesAt x n) :
    X.HasIndependentTangentSums Θ := by
  intro x B B'
  by_cases hx : x ∈ supp Θ
  · obtain ⟨dim, dim', hdim, hdim', hagree⟩ := h x B B' hx
    exact B.tangentSum_eq_of_dimPartsAgreeNear B' hdim hdim' hagree (hsl x hx)
  · rw [B.tangentSum_eq_zero hx, B'.tangentSum_eq_zero hx]

/-- The independence for a branched ep⁺-subgroupoid, granted Proposition 9.1.12 (stated, not
proved, in `Propositions.lean`), dimension labellings of the local branching structures and
tangent slices. -/
theorem hasIndependentTangentSums_of_proposition_9_1_12 (hP : X.Proposition_9_1_12)
    {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hlab : ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x),
      ∃ dim : B.ι → ℕ, ∀ i, X.PObj.IsSubmanifoldOfDim (B.M i) (dim i))
    (hsl : ∀ x ∈ supp Θ, ∀ n, X.PObj.HasTangentSlicesAt x n) :
    X.HasIndependentTangentSums Θ :=
  hasIndependentTangentSums_of_dimPartsAgreeNear (fun x B B' _ => by
    obtain ⟨dim, hdim⟩ := hlab x B
    obtain ⟨dim', hdim'⟩ := hlab x B'
    exact ⟨dim, dim', hdim, hdim', hP Θ hΘ x B B' dim dim' hdim hdim'⟩) hsl

/-- **The independence in the equidimensional case** (no Proposition 9.1.12 needed): if all
local branching structures are `n`-dimensional and there are tangent slices. -/
theorem hasIndependentTangentSums_of_isOfDim {Θ : Obj → ℚ} {n : ℕ}
    (hdim : ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x), B.IsOfDim n)
    (hsl : ∀ x ∈ supp Θ, X.PObj.HasTangentSlicesAt x n) : X.HasIndependentTangentSums Θ := by
  intro x B B'
  by_cases hx : x ∈ supp Θ
  · exact B.tangentSum_eq_of_eqOn B' (hdim x B) (hdim x B') (hsl x hx)
      (B.isOpen_U.inter B'.isOpen_U) ⟨B.mem_U, B'.mem_U⟩ fun _ _ => rfl
  · rw [B.tangentSum_eq_zero hx, B'.tangentSum_eq_zero hx]

/-- **The independence when every point of `supp(Θ)` is good** (Definition 9.2.2, Lemma 9.2.3):
no further hypothesis. -/
theorem hasIndependentTangentSums_of_subset_goodSet {Θ : Obj → ℚ}
    (h : supp Θ ⊆ X.goodSet Θ) : X.HasIndependentTangentSums Θ := by
  intro x B B'
  by_cases hx : x ∈ supp Θ
  · exact B.tangentSum_eq_of_isGoodPoint B' (remark_9_2_4_a (h hx) B B.mem_U)
  · rw [B.tangentSum_eq_zero hx, B'.tangentSum_eq_zero hx]

/-! ### Transport along a morphism -/

variable (X) in
/-- The inverse `s ∘ (t|𝐔)⁻¹` of `φ̂` on the chosen sheet (Definition 7.4). -/
def hatInv (φ : Mor) : Obj → Obj := fun z => X.src ((X.sheetAt φ).tgtInv z)

theorem isScDiffeoOn_hat' (φ : Mor) :
    X.PObj.IsScDiffeoOn X.PObj (X.hat φ) (X.hatInv φ) (X.sheetAt φ).srcSet
      (X.sheetAt φ).tgtSet :=
  X.isScDiffeoOn_hat φ

theorem hatInv_tgt (φ : Mor) : X.hatInv φ (X.tgt φ) = X.src φ := by
  rw [← X.hat_src φ]
  exact (X.isScDiffeoOn_hat' φ).left_inv _ (X.src_mem_sheetAt φ)

namespace LocalBranchingStructure

variable {Θ : Obj → ℚ}

/-- The domain `φ̂(U(s φ) ∩ U(x))` of the transported structure. -/
def transportU {φ : Mor} (B : X.LocalBranchingStructure Θ (X.src φ)) : Set Obj :=
  (X.sheetAt φ).tgtSet ∩ X.hatInv φ ⁻¹' (B.U ∩ (X.sheetAt φ).srcSet)

theorem mem_hat_image_iff {φ : Mor} (B : X.LocalBranchingStructure Θ (X.src φ)) {i : B.ι}
    {y : Obj} (hy : y ∈ B.transportU) :
    y ∈ X.hat φ '' (B.M i ∩ (X.sheetAt φ).srcSet) ↔ X.hatInv φ y ∈ B.M i := by
  constructor
  · rintro ⟨z, ⟨hzM, hzS⟩, rfl⟩
    rwa [(X.isScDiffeoOn_hat' φ).left_inv z hzS]
  · intro h
    exact ⟨X.hatInv φ y, ⟨h, hy.2.2⟩, (X.isScDiffeoOn_hat' φ).right_inv y hy.1⟩

open scoped Classical in
/-- **Transport of a local branching structure along a morphism** (2021 Definition 9.2.12,
p. 418, through the local sc-diffeomorphisms of the morphisms): for `φ : x → y` and a structure
`(Mᵢ)`, `(σᵢ)` at `x`, the
`φ̂(Mᵢ ∩ U(x))` with the same weights form a structure at `y` (`Θ` is functorial, so
`Θ ∘ φ̂ = Θ`). -/
def transport (hΘ : X.IsFunctorial Θ) (φ : Mor) (B : X.LocalBranchingStructure Θ (X.src φ)) :
    X.LocalBranchingStructure Θ (X.tgt φ) where
  U := B.transportU
  isOpen_U := (X.isScDiffeoOn_hat' φ).isScSmoothOn_inv.continuousOn.isOpen_inter_preimage
    (X.isScDiffeoOn_hat' φ).isScSmoothOn_inv.isOpen
    (B.isOpen_U.inter (X.isScDiffeoOn_hat' φ).isScSmoothOn.isOpen)
  mem_U := ⟨X.tgt_mem_sheetAt φ, by
    rw [mem_preimage, X.hatInv_tgt]; exact ⟨B.mem_U, X.src_mem_sheetAt φ⟩⟩
  ι := B.ι
  M i := X.hat φ '' (B.M i ∩ (X.sheetAt φ).srcSet)
  subset_U i := by
    rintro _ ⟨z, ⟨hzM, hzS⟩, rfl⟩
    refine ⟨(X.isScDiffeoOn_hat' φ).mapsTo hzS, ?_⟩
    rw [mem_preimage, (X.isScDiffeoOn_hat' φ).left_inv z hzS]
    exact ⟨B.subset_U i hzM, hzS⟩
  isSmoothSubmanifold i := ((B.isSmoothSubmanifold i).inter_isOpen
    (X.isScDiffeoOn_hat' φ).isScSmoothOn.isOpen).image_of_isScDiffeoOn (X.isScDiffeoOn_hat' φ)
    inter_subset_right
  mem_M i := ⟨X.src φ, ⟨B.mem_M i, X.src_mem_sheetAt φ⟩, X.hat_src φ⟩
  isProperMap i := by
    refine (isProperMap_inclusion_iff _).2 ?_
    have hmaps : MapsTo (X.hatInv φ) B.transportU B.U := fun y hy => hy.2.1
    have hc := (B.isClosed_M i).preimage
      (((X.isScDiffeoOn_hat' φ).isScSmoothOn_inv.continuousOn.mono inter_subset_left)
        |>.mapsToRestrict hmaps)
    have heq : ((↑) ⁻¹' (X.hat φ '' (B.M i ∩ (X.sheetAt φ).srcSet)) : Set B.transportU) =
        hmaps.restrict _ _ _ ⁻¹' ((↑) ⁻¹' B.M i) := by
      ext y
      exact B.mem_hat_image_iff y.2
    change IsClosed ((↑) ⁻¹' (X.hat φ '' (B.M i ∩ (X.sheetAt φ).srcSet)) : Set B.transportU)
    rw [heq]
    exact hc
  σ := B.σ
  σ_pos := B.σ_pos
  eq_sum y hy := by
    have h1 : Θ y = Θ (X.hatInv φ y) := by
      rw [← Sheet.apply_hat hΘ (X.sheetAt φ) hy.2.2]
      congr 1
      exact ((X.isScDiffeoOn_hat' φ).right_inv y hy.1).symm
    rw [h1, B.eq_sum _ hy.2.1]
    exact Finset.sum_congr (Finset.filter_congr fun i _ => (B.mem_hat_image_iff hy).symm)
      fun _ _ => rfl

/-- **The sum of the transported structure is the pushed sum**:
`∑ σᵢ · T_y(φ̂(Mᵢ)) = ∑ σᵢ · Tφ(T_xMᵢ)` (`submanifoldTangent_image`, `Tφ = Tφ̂(x)`). -/
theorem tangentSum_transport (hΘ : X.IsFunctorial Θ) {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1)
    (B : X.LocalBranchingStructure Θ (X.src φ)) :
    (B.transport hΘ φ).tangentSum = X.grPush φ B.tangentSum := by
  rw [tangentSum, tangentSum, grPush, Finsupp.mapDomain_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.mapDomain_single]
  congr 1
  have hd := X.isScDiffeoOn_hat' φ
  have hS := hd.isScSmoothOn.isOpen
  have h := MPolyfold.submanifoldTangent_image hd ((B.isSmoothSubmanifold i).inter_isOpen hS)
    inter_subset_right ⟨B.mem_M i, X.src_mem_sheetAt φ⟩
  rw [X.hat_src φ, MPolyfold.submanifoldTangent_inter_isOpen hS (X.src_mem_sheetAt φ)] at h
  change X.PObj.submanifoldTangent (X.hat φ '' (B.M i ∩ (X.sheetAt φ).srcSet)) (X.tgt φ) = _
  rw [h]
  exact image_congr fun α hα =>
    (X.tangentMor_eq_tangentMapOn_hat hφ (MPolyfold.levelVal_tangentProj_of_mem hα)).symm

end LocalBranchingStructure

/-! ### Theorem 9.2.1: the section functor `TΘ : X_∞ → Gr(X)` -/

open scoped Classical in
variable (X) in
/-- **`TΘ(x)`** (2021 Theorem 9.2.1 (1), p. 410): `∑ σᵢ · T_xMᵢ` for a chosen local branching
structure at `x`, the zero-sum if there is none (in particular off `supp(Θ)`). -/
def tangentValue (Θ : Obj → ℚ) (x : Obj) : Set X.PObj.TangentSpace →₀ ℚ :=
  if h : Nonempty (X.LocalBranchingStructure Θ x) then h.some.tangentSum else 0

theorem tangentValue_mem (Θ : Obj → ℚ) (x : Obj) : X.tangentValue Θ x ∈ X.Gr x := by
  unfold tangentValue
  split_ifs with h
  · exact h.some.tangentSum_mem
  · exact X.zero_mem_Gr x

/-- `TΘ(x)` is the zero-sum for `x ∉ supp(Θ)`. -/
theorem tangentValue_eq_zero {Θ : Obj → ℚ} {x : Obj} (hx : x ∉ supp Θ) :
    X.tangentValue Θ x = 0 := by
  unfold tangentValue
  split_ifs with h
  · exact h.some.tangentSum_eq_zero hx
  · rfl

/-- `TΘ(x) = ∑ σᵢ · T_xMᵢ` for every local branching structure at `x`. -/
theorem tangentValue_eq {Θ : Obj → ℚ} (hind : X.HasIndependentTangentSums Θ) {x : Obj}
    (B : X.LocalBranchingStructure Θ x) : X.tangentValue Θ x = B.tangentSum := by
  rw [tangentValue, dif_pos ⟨B⟩]
  exact hind x _ B

/-- **Naturality of `TΘ`**: `∑ σ_L · Tφ(L) = TΘ(t φ)` for `L = TΘ(s φ)` (transport). -/
theorem grPush_tangentValue {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) (φ : Mor) :
    X.grPush φ (X.tangentValue Θ (X.src φ)) = X.tangentValue Θ (X.tgt φ) := by
  by_cases hs : X.src φ ∈ supp Θ
  · obtain ⟨B⟩ := hΘ.localBranching _ hs
    rw [X.tangentValue_eq hind B, X.tangentValue_eq hind (B.transport hΘ.isFunctorial φ),
      B.tangentSum_transport hΘ.isFunctorial (X.mem_levelSet_one_of_src (hΘ.support_subset hs))]
  · have ht : X.tgt φ ∉ supp Θ := fun h => hs (by
      change 0 < Θ (X.src φ); rw [hΘ.isFunctorial φ]; exact h)
    rw [X.tangentValue_eq_zero hs, X.tangentValue_eq_zero ht, grPush, Finsupp.mapDomain_zero]

/-- **The section functor `TΘ : X_∞ → Gr(X)`** (2021 Theorem 9.2.1, pp. 409–410):
`x ↦ TΘ(x)`, `φ ↦ (TΘ(s φ), φ)`. -/
def tangentSection {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) : X.SmoothCat ⥤ X.GrObj where
  obj x := ⟨x.pt, x.smooth, X.tangentValue Θ x.pt, X.tangentValue_mem Θ x.pt⟩
  map {x y} f := ⟨SmoothCat.mor f, SmoothCat.src_mor f, SmoothCat.tgt_mor f, by
    change X.grPush (SmoothCat.mor f) (X.tangentValue Θ x.pt) = X.tangentValue Θ y.pt
    rw [← SmoothCat.src_mor f, ← SmoothCat.tgt_mor f]
    exact X.grPush_tangentValue hΘ hind _⟩
  map_id x := Subtype.ext (SmoothCat.mor_id x)
  map_comp f g := Subtype.ext (SmoothCat.mor_comp f g)

/-- **Theorem 9.2.1, p. 409 (2017: Theorem 9.1, p. 298)**: for a branched ep⁺-subgroupoid `Θ`
whose sums `∑ σᵢ · T_xMᵢ` do not depend on the local branching structure
(`HasIndependentTangentSums`; sufficient conditions: `hasIndependentTangentSums_of_subset_goodSet`,
`..._of_isOfDim`, `..._of_proposition_9_1_12`), the section functor `TΘ : X_∞ → Gr(X)`
satisfies `π ∘ TΘ = Id_{X_∞}`, (1) `TΘ(x) = ∑ σᵢ · T_xMᵢ` for **any** local branching structure
at `x ∈ supp(Θ)`, the zero-sum for `x ∉ supp(Θ)`, and (2) `TΘ(φ) = (TΘ(s φ), φ)`. -/
theorem theorem_9_2_1 {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) :
    X.tangentSection hΘ hind ⋙ X.grProj = 𝟭 X.SmoothCat ∧
      (∀ (x : X.SmoothCat), x.pt ∈ supp Θ → ∀ B : X.LocalBranchingStructure Θ x.pt,
        ((X.tangentSection hΘ hind).obj x).sum =
          ∑ i, Finsupp.single (X.PObj.submanifoldTangent (B.M i) x.pt) (B.σ i)) ∧
      (∀ (x : X.SmoothCat), x.pt ∉ supp Θ → ((X.tangentSection hΘ hind).obj x).sum = 0) ∧
      (∀ {x y : X.SmoothCat} (f : x ⟶ y),
        ((X.tangentSection hΘ hind).obj x).pt = X.src (SmoothCat.mor f) ∧
          ((X.tangentSection hΘ hind).map f).1 = SmoothCat.mor f) := by
  exact ⟨rfl, fun x _ B => X.tangentValue_eq hind B, fun x hx => X.tangentValue_eq_zero hx,
    fun f => ⟨(SmoothCat.src_mor f).symm, rfl⟩⟩

/-! ### Definition 9.2.12: the tangent `TΘ : TX → ℚ⁺` -/

open scoped Classical in
/-- The value `∑_{L ∋ h} σ_L` of a formal sum `∑ σ_L · L` at a vector `h`. -/
def grEval (w : Set X.PObj.TangentSpace →₀ ℚ) (h : X.PObj.TangentSpace) : ℚ :=
  w.sum fun L c => if h ∈ L then c else 0

theorem grEval_nonneg {x : Obj} {w : Set X.PObj.TangentSpace →₀ ℚ} (hw : w ∈ X.Gr x)
    (h : X.PObj.TangentSpace) : 0 ≤ grEval w h := by
  rw [grEval, Finsupp.sum]
  refine Finset.sum_nonneg fun L _ => ?_
  split_ifs
  exacts [hw.1 L, le_rfl]

theorem grEval_zero (h : X.PObj.TangentSpace) :
    grEval (0 : Set X.PObj.TangentSpace →₀ ℚ) h = 0 := Finsupp.sum_zero_index

open scoped Classical in
theorem grEval_sum_single {ι : Type*} [Fintype ι] (L : ι → Set X.PObj.TangentSpace)
    (c : ι → ℚ) (h : X.PObj.TangentSpace) :
    grEval (∑ i, Finsupp.single (L i) (c i)) h = ∑ i, if h ∈ L i then c i else 0 := by
  rw [grEval]
  refine (Finsupp.sum_finsetSum_index (fun _ => ?_) (fun _ _ _ => ?_)).symm.trans ?_
  · exact ite_self 0
  · split_ifs <;> simp
  · exact Finset.sum_congr rfl fun i _ => Finsupp.sum_single_index (ite_self 0)

/-- `(∑ σ_L · Tφ(L))(Tφ h) = (∑ σ_L · L)(h)` for `h ∈ T_{s φ}X` (`Tφ` is injective there). -/
theorem grEval_grPush {φ : Mor} (hφ : φ ∈ X.PMor.levelSet 1) {w : Set X.PObj.TangentSpace →₀ ℚ}
    (hw : w ∈ X.Gr (X.src φ)) {α : X.PObj.TangentSpace}
    (hα : X.PObj.levelVal 1 (X.PObj.tangentProj α) = X.src φ) :
    grEval (X.grPush φ w) (X.tangentMor φ α) = grEval w α := by
  classical
  rw [grEval, grPush]
  refine (Finsupp.sum_mapDomain_index (fun _ => ?_) (fun _ _ _ => ?_)).trans ?_
  · exact ite_self 0
  · split_ifs <;> simp
  refine Finsupp.sum_congr fun L hL => ?_
  have hiff : X.tangentMor φ α ∈ X.tangentMor φ '' L ↔ α ∈ L :=
    (X.tangentMor_injOn hφ).mem_image_iff (fun β hβ => hw.2 L hL β hβ) hα
  simp only [hiff]

variable (X) in
/-- **Definition 9.2.12, p. 418 (2017: Definition 9.6, p. 306) (the tangent of `Θ`)**:
`TΘ : TX → ℚ⁺`, `TΘ(h) = ∑_{L ∋ h} σ_L` where `TΘ(x) = ∑ σ_L · L` (Theorem 9.2.1) for `h`
over `x`; locally `TΘ(h) = ∑_{i : h ∈ TMᵢ} σᵢ` (`tangentTheta_eq`), and `TΘ(h) = 0` if
`Θ(x) = 0` (`tangentTheta_eq_zero`). -/
def tangentTheta (Θ : Obj → ℚ) (h : X.PObj.TangentSpace) : ℚ :=
  grEval (X.tangentValue Θ (X.PObj.levelVal 1 (X.PObj.tangentProj h))) h

/-- `TΘ(h) = 0` for `h ∈ T_xX` with `Θ(x) = 0`. -/
theorem tangentTheta_eq_zero {Θ : Obj → ℚ} {h : X.PObj.TangentSpace}
    (hx : Θ (X.PObj.levelVal 1 (X.PObj.tangentProj h)) = 0) : X.tangentTheta Θ h = 0 := by
  have hs : X.PObj.levelVal 1 (X.PObj.tangentProj h) ∉ supp Θ := fun h' => by
    change 0 < Θ _ at h'
    rw [hx] at h'
    exact lt_irrefl 0 h'
  rw [tangentTheta, X.tangentValue_eq_zero hs, grEval_zero]

open scoped Classical in
/-- **Definition 9.2.12, the local formula**: on `TU(x)`, `TΘ(h) = ∑_{i : h ∈ TMᵢ} σᵢ` for every
local branching structure `(Mᵢ)`, `(σᵢ)` on `U(x)` (`TMᵢ ∋ h` means `h ∈ T_yMᵢ`, `y = p(h)`). -/
theorem tangentTheta_eq {Θ : Obj → ℚ} (hind : X.HasIndependentTangentSums Θ) {x : Obj}
    (B : X.LocalBranchingStructure Θ x) {h : X.PObj.TangentSpace}
    (hh : X.PObj.levelVal 1 (X.PObj.tangentProj h) ∈ B.U) :
    X.tangentTheta Θ h = ∑ i with h ∈ X.PObj.submanifoldTangent (B.M i)
      (X.PObj.levelVal 1 (X.PObj.tangentProj h)), B.σ i := by
  rw [tangentTheta, X.tangentValue_eq hind (B.restrictAt hh), LocalBranchingStructure.tangentSum,
    grEval_sum_single, ← Finset.sum_filter]
  have hT : ∀ i : B.ι, X.PObj.submanifoldTangent (B.M i ∩ B.nbhdAt
      (X.PObj.levelVal 1 (X.PObj.tangentProj h))) (X.PObj.levelVal 1 (X.PObj.tangentProj h)) =
      X.PObj.submanifoldTangent (B.M i) (X.PObj.levelVal 1 (X.PObj.tangentProj h)) := fun i =>
    MPolyfold.submanifoldTangent_inter_isOpen (B.isOpen_nbhdAt _) (B.mem_nbhdAt_self hh)
  refine Finset.sum_bij (fun a _ => a.1) (fun a ha => ?_) (fun a _ b _ hab => Subtype.ext hab)
    (fun i hi => ?_) fun _ _ => rfl
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, LocalBranchingStructure.restrictAt_M,
      hT] at ha ⊢
    exact ha
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨⟨i, MPolyfold.mem_of_mem_submanifoldTangent hi⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    change h ∈ X.PObj.submanifoldTangent (B.M i ∩ B.nbhdAt _) _
    rw [hT]
    exact hi

open scoped Classical in
/-- **Definition 9.2.12, well defined** (p. 418): for two local branching structures on `U(x)`,
`∑_{i : h ∈ TMᵢ} σᵢ = ∑_{j : h ∈ TN_j} τ_j` for `h ∈ TU(x)`. -/
theorem sum_tangent_eq_sum_tangent {Θ : Obj → ℚ} (hind : X.HasIndependentTangentSums Θ)
    {x : Obj} (B B' : X.LocalBranchingStructure Θ x) {h : X.PObj.TangentSpace}
    (hh : X.PObj.levelVal 1 (X.PObj.tangentProj h) ∈ B.U)
    (hh' : X.PObj.levelVal 1 (X.PObj.tangentProj h) ∈ B'.U) :
    (∑ i with h ∈ X.PObj.submanifoldTangent (B.M i)
      (X.PObj.levelVal 1 (X.PObj.tangentProj h)), B.σ i) =
      ∑ j with h ∈ X.PObj.submanifoldTangent (B'.M j)
        (X.PObj.levelVal 1 (X.PObj.tangentProj h)), B'.σ j := by
  rw [← X.tangentTheta_eq hind B hh, ← X.tangentTheta_eq hind B' hh']

theorem tangentTheta_nonneg (Θ : Obj → ℚ) (h : X.PObj.TangentSpace) :
    0 ≤ X.tangentTheta Θ h :=
  grEval_nonneg (X.tangentValue_mem Θ _) h

/-- **`TΘ` is a functor on `T(X, 𝐗)`** ("the local definitions fit together"):
`TΘ(Ts(v)) = TΘ(Tt(v))` for `v ∈ T𝐗`, since `Tt(v) = Tφ(Ts(v))` and `TΘ(t φ)` is the push of
`TΘ(s φ)` along `Tφ` (Theorem 9.2.1 (2)). -/
theorem isFunctorial_tangentTheta {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) :
    X.tangentEpGroupoid.IsFunctorial (X.tangentTheta Θ) := by
  intro v
  change X.tangentTheta Θ (X.tSrc v) = X.tangentTheta Θ (X.tTgt v)
  rw [tangentTheta, tangentTheta, X.levelVal_tangentProj_tSrc, X.levelVal_tangentProj_tTgt,
    ← X.grPush_tangentValue hΘ hind, ← X.tangentMor_tSrc v,
    grEval_grPush (X.tBase_mem_levelSet v) (X.tangentValue_mem Θ _)
      (X.levelVal_tangentProj_tSrc v)]

/-! ### Definition 9.2.12: `TΘ` is a branched ep⁺-subgroupoid -/

/-- For `U` open and finitely many `A_j` closed in `U`, `{z ∈ U | z ∈ A_j ⇒ y ∈ A_j}` is open. -/
theorem isOpen_setOf_mem_imp {Z : Type*} [TopologicalSpace Z] {ι : Type*} [Finite ι] {U : Set Z}
    (hU : IsOpen U) (A : ι → Set Z) (hA : ∀ j, IsClosed ((↑) ⁻¹' A j : Set U)) (y : Z) :
    IsOpen {z | z ∈ U ∧ ∀ j, z ∈ A j → y ∈ A j} := by
  classical
  have hdiff : ∀ j, IsOpen (U \ A j) := fun j => by
    have h := hU.isOpenMap_subtype_val _ (hA j).isOpen_compl
    convert h using 1
    ext z
    constructor
    · rintro ⟨hzU, hzA⟩
      exact ⟨⟨z, hzU⟩, hzA, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw⟩
  have h : {z | z ∈ U ∧ ∀ j, z ∈ A j → y ∈ A j} =
      U ∩ ⋂ j, (if y ∈ A j then U else U \ A j) := by
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨hz, h⟩
      refine ⟨hz, fun j => ?_⟩
      split_ifs with hj
      · exact hz
      · exact ⟨hz, fun hzj => hj (h j hzj)⟩
    · rintro ⟨hz, h⟩
      refine ⟨hz, fun j hzj => ?_⟩
      by_contra hj
      have h' := h j
      rw [if_neg hj] at h'
      exact h'.2 hzj
  rw [h]
  refine hU.inter (isOpen_iInter_of_finite fun j => ?_)
  split_ifs
  · exact hU
  · exact hdiff j

variable (X) in
/-- `TA ⊆ TX`: the vectors `h` with `h ∈ T_{p(h)}A` (the text's `TMᵢ`). -/
def tangentSubmanifold (A : Set Obj) : Set X.PObj.TangentSpace :=
  {h | h ∈ X.PObj.submanifoldTangent A (X.PObj.levelVal 1 (X.PObj.tangentProj h))}

variable (X) in
/-- **The Part I facts behind "`TΘ` is a branched ep⁺-subgroupoid"** (Definition 9.2.12, where
"the local branching structure on `TU(x)` is given by `(TMᵢ)`, `(σᵢ)`", p. 409): for every local
branching structure `(Mᵢ)` of `Θ` the tangent bundles `TMᵢ` are smooth finite-dimensional
submanifolds of the tangent M-polyfold `TX` consisting of smooth points and closed in
`TU(x) = p⁻¹(U(x))`; and `|supp(TΘ)|` is paracompact (the condition new in 2021, not discussed
for `TΘ` in the text).  Satisfiable: `tangentBranchingHyp_zero`. -/
structure TangentBranchingHyp (Θ : Obj → ℚ) : Prop where
  isSmoothSubmanifold : ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x) (i : B.ι),
    X.tangentEpGroupoid.PObj.IsSmoothSubmanifold (X.tangentSubmanifold (B.M i))
  subset_smoothSet : ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x) (i : B.ι),
    X.tangentSubmanifold (B.M i) ⊆ X.tangentEpGroupoid.PObj.smoothSet
  isClosed : ∀ (x : Obj) (B : X.LocalBranchingStructure Θ x) (i : B.ι),
    IsClosed ((↑) ⁻¹' X.tangentSubmanifold (B.M i) : Set (X.PObj.tangentPreimage B.U))
  paracompactSpace : ParacompactSpace (X.tangentEpGroupoid.orbitSupp (X.tangentTheta Θ))

/-- The domain `{h' ∈ TU(y) | h' ∈ TMᵢ ⇒ h ∈ TMᵢ}` of the local branching structure of `TΘ`
at `h`. -/
def tangentNbhd {Θ : Obj → ℚ} {y : Obj} (B : X.LocalBranchingStructure Θ y)
    (h : X.PObj.TangentSpace) : Set X.PObj.TangentSpace :=
  {h' | h' ∈ X.PObj.tangentPreimage B.U ∧
    ∀ i, h' ∈ X.tangentSubmanifold (B.M i) → h ∈ X.tangentSubmanifold (B.M i)}

open scoped Classical in
/-- **The local branching structure of `TΘ` at `h ∈ TU(y)`** (p. 409): the domain
`tangentNbhd B h`, the submanifolds `TMᵢ ∩ tangentNbhd B h` for the `i` with `h ∈ TMᵢ`, the
weights `σᵢ`. -/
def tangentBranchingStructure {Θ : Obj → ℚ} (hind : X.HasIndependentTangentSums Θ)
    (hT : X.TangentBranchingHyp Θ) {y : Obj} (B : X.LocalBranchingStructure Θ y)
    (h : X.PObj.TangentSpace) (hh : X.PObj.levelVal 1 (X.PObj.tangentProj h) ∈ B.U) :
    X.tangentEpGroupoid.LocalBranchingStructure (X.tangentTheta Θ) h where
  U := tangentNbhd B h
  isOpen_U := isOpen_setOf_mem_imp (MPolyfold.isOpen_tangentPreimage B.isOpen_U) _
    (hT.isClosed y B) h
  mem_U := ⟨hh, fun _ hi => hi⟩
  ι := ULift.{max u 1} {i // h ∈ X.tangentSubmanifold (B.M i)}
  M i := X.tangentSubmanifold (B.M i.down.1) ∩ tangentNbhd B h
  subset_U _ := inter_subset_right
  isSmoothSubmanifold i := (hT.isSmoothSubmanifold y B i.down.1).inter_isOpen
    (isOpen_setOf_mem_imp (MPolyfold.isOpen_tangentPreimage B.isOpen_U) _ (hT.isClosed y B) h)
  mem_M i := ⟨i.down.2, hh, fun _ hi => hi⟩
  isProperMap i := by
    refine (isProperMap_inclusion_iff _).2 ?_
    have hc := (hT.isClosed y B i.down.1).preimage
      (continuous_inclusion (fun _ hz => hz.1 : tangentNbhd B h ⊆ X.PObj.tangentPreimage B.U))
    convert hc using 1
    ext z
    exact ⟨fun h => h.1, fun h => ⟨h, z.2⟩⟩
  σ i := B.σ i.down.1
  σ_pos i := B.σ_pos i.down.1
  eq_sum h' hh' := by
    rw [X.tangentTheta_eq hind B hh'.1]
    symm
    refine Finset.sum_bij (fun a _ => a.down.1) (fun a ha => ?_)
      (fun a _ b _ hab => ULift.ext _ _ (Subtype.ext hab)) (fun i hi => ?_) fun _ _ => rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ha.1
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine ⟨⟨⟨i, hh'.2 i hi⟩⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hi, hh'⟩

/-- **Definition 9.2.12, p. 418 (2017: Definition 9.6, p. 306)**: for a branched
ep⁺-subgroupoid `Θ` with independent tangent sums (Theorem 9.2.1), the tangent
`TΘ : TX → ℚ⁺` is a branched ep⁺-subgroupoid of `T(X, 𝐗)`, granted the Part I facts
`TangentBranchingHyp` on the `TMᵢ`; locally it is `∑_{i : h ∈ TMᵢ} σᵢ` (`tangentTheta_eq`),
independently of the local branching structure (`sum_tangent_eq_sum_tangent`). -/
theorem isBranchedEpSubgroupoid_tangentTheta {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hind : X.HasIndependentTangentSums Θ) (hT : X.TangentBranchingHyp Θ) :
    X.tangentEpGroupoid.IsBranchedEpSubgroupoid (X.tangentTheta Θ) := by
  classical
  have hbase : ∀ h ∈ supp (X.tangentTheta Θ),
      X.PObj.levelVal 1 (X.PObj.tangentProj h) ∈ supp Θ := fun h hh => by
    by_contra hy
    have h0 : Θ (X.PObj.levelVal 1 (X.PObj.tangentProj h)) = 0 :=
      le_antisymm (not_lt.1 hy) (hΘ.nonneg _)
    have hh' : 0 < X.tangentTheta Θ h := hh
    rw [X.tangentTheta_eq_zero h0] at hh'
    exact lt_irrefl 0 hh'
  refine ⟨X.tangentTheta_nonneg Θ, X.isFunctorial_tangentTheta hΘ hind, fun h hh => ?_,
    hT.paracompactSpace, fun h hh => ?_⟩
  · obtain ⟨B⟩ := hΘ.localBranching _ (hbase h hh)
    have hh' : 0 < X.tangentTheta Θ h := hh
    rw [X.tangentTheta_eq hind B B.mem_U] at hh'
    obtain ⟨i, hi, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hh'.ne'
    exact hT.subset_smoothSet _ B i (Finset.mem_filter.1 hi).2
  · obtain ⟨B⟩ := hΘ.localBranching _ (hbase h hh)
    exact ⟨X.tangentBranchingStructure hind hT B h B.mem_U⟩

/-- The zero functor has independent tangent sums (all are the zero-sum). -/
theorem hasIndependentTangentSums_zero : X.HasIndependentTangentSums 0 := fun x B B' => by
  have hx : x ∉ supp (0 : Obj → ℚ) := fun h => lt_irrefl (0 : ℚ) h
  rw [B.tangentSum_eq_zero hx, B'.tangentSum_eq_zero hx]

/-- **Satisfiability of `TangentBranchingHyp`**: for `Θ = 0` (no local branching structure has a
submanifold, and `supp(TΘ) = ∅`). -/
theorem tangentBranchingHyp_zero : X.TangentBranchingHyp 0 := by
  have hx : ∀ x : Obj, x ∉ supp (0 : Obj → ℚ) := fun _ h => lt_irrefl (0 : ℚ) h
  have hempty : X.tangentEpGroupoid.orbitSupp (X.tangentTheta 0) = ∅ := by
    rw [orbitSupp, image_eq_empty]
    ext h
    simp only [mem_empty_iff_false, iff_false]
    intro hh
    have hh' : 0 < X.tangentTheta 0 h := hh
    rw [X.tangentTheta_eq_zero rfl] at hh'
    exact lt_irrefl 0 hh'
  refine ⟨fun x B i => ((B.isEmpty_of_not_mem (hx x)).false i).elim,
    fun x B i => ((B.isEmpty_of_not_mem (hx x)).false i).elim,
    fun x B i => ((B.isEmpty_of_not_mem (hx x)).false i).elim, ?_⟩
  rw [hempty]
  have : CompactSpace (∅ : Set X.tangentEpGroupoid.OrbitSpace) :=
    isCompact_iff_compactSpace.1 isCompact_empty
  infer_instance

/-- With `Θ = 0`: `TΘ = 0` is a branched ep⁺-subgroupoid of `T(X, 𝐗)`, through
`isBranchedEpSubgroupoid_tangentTheta`. -/
theorem isBranchedEpSubgroupoid_tangentTheta_zero :
    X.tangentEpGroupoid.IsBranchedEpSubgroupoid (X.tangentTheta 0) :=
  X.isBranchedEpSubgroupoid_tangentTheta (isBranchedEpSubgroupoid_zero X)
    X.hasIndependentTangentSums_zero X.tangentBranchingHyp_zero

end EpGroupoid

/-- **Satisfiability of `HasIndependentTangentSums` with nonempty support**: the indicator of a
point `p` of `ℝⁿ` (every point of its support is good). -/
theorem hasIndependentTangentSums_indicator (n : ℕ) (p : Fin n → ℝ) :
    (EpGroupoid.trivial (rnPolyfold n)).HasIndependentTangentSums
      (({p} : Set (Fin n → ℝ)).indicator 1) := by
  refine EpGroupoid.hasIndependentTangentSums_of_subset_goodSet fun y hy => ?_
  rw [EpGroupoid.supp_indicator_singleton] at hy
  rw [mem_singleton_iff.1 hy]
  refine ⟨by rw [EpGroupoid.supp_indicator_singleton]; rfl, p,
    EpGroupoid.localBranchingStructure_indicator n p, mem_univ p,
    mem_iUnion.2 ⟨(), rfl⟩, univ, isOpen_univ, mem_univ p, subset_rfl, fun _ _ _ _ => rfl⟩

end Polyfold
