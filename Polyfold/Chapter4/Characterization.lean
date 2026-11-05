import Polyfold.Chapter4.ScPlusGraph
import Polyfold.Chapter4.Recentre
import Polyfold.Chapter3.GoodComplementProjection

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §4.1,
Definition 4.1 and Theorem 4.2 *(book 2017: Definition 4.1, Theorem 4.1; see
`BookConcordance.md`)*.

# M-polyfolds that are manifolds with boundary with corners

## The text, paraphrased

(Definition 4.1) An M-polyfold `X` has a compatible smooth manifold structure with boundary with
corners if it admits an atlas of sc-smoothly compatible charts `(V, φ, (U, C, ℝⁿ))`, `φ : V → U`
an sc-diffeomorphism from an open `V ⊆ X` onto a relatively open subset `U` of a partial quadrant
`C` in `ℝⁿ` (or in a finite-dimensional vector space), with the constant sc-structure.  The
transition maps are sc-diffeomorphisms between relatively open subsets of partial quadrants in
finite-dimensional spaces, hence classically `C^∞`, and the atlas is that of a smooth manifold
with boundary with corners.  (Theorem 4.2) For a tame M-polyfold `X` the following are equivalent:
(i) `X` has such a structure; (ii) `X₀ = X_∞`, the identity `1₀¹ : X → X¹` is sc-smooth, and every
`x ∈ X` lies in a tame chart `(V, ψ, (O, C, E))` with `ψ(x) = 0` whose tangent space `T₀O` is
finite-dimensional and in good position to `C`.  *Proof.* (i) ⇒ (ii): the identity of `U` is a
tame retraction, `U = U_∞` and `1₀¹ : U → U¹` is sc-smooth.  (ii) ⇒ (i): by Proposition 4.8 the
model `O` of `ψ` is an sc⁺-retract; Proposition 4.9 gives an sc-diffeomorphism `p : O' → V` of a
neighbourhood `O'` of `0` in `O` onto a relatively open `V ⊆ T₀O ∩ C`, and `p ∘ ψ` on `ψ⁻¹(O')` is
a chart onto the finite-dimensional model `(V, T₀O ∩ C, T₀O)`; "carrying out this construction
around every point we obtain a smoothly compatible atlas of tame charts".

## What is formalized

* `MChart.IsCornerChart` (a chart modelled on `LocalModel.ofRelOpen` of a relatively open
  `U ⊆ C` in `ScBanach.const V`, `V` finite-dimensional) and `MPolyfold.HasCornerStructure`
  (**Definition 4.1**: an atlas of corner charts equivalent to the atlas of `X`; the dimension may
  vary from chart to chart), with `hasCornerStructure_iff` (local form: every point lies in a
  corner chart of the structure), `HasCornerStructure.isTame`,
  `MChart.IsCornerChart.contDiffOn_transition` (**the transition maps are `C^∞`** on the overlaps,
  one-sided at the boundary, by `isScSmooth_iff_contDiffOn_const`).
* The relation to the manifolds with corners of Chapter 3:
  `exists_isCornerChart_of_finiteDimensional` (a chart onto a relatively open subset of a partial quadrant in an sc-Banach space with
  finite-dimensional `E₀` is, with the same map, a corner chart for the constant structure, through
  `ScBanach.scIsoConst`), `hasCornerStructure_iff_finiteDimensional` (the right-hand side is the
  definition of `MPolyfold.IsManifoldWithCornersLoc` of `GlobalIFTTheorems.lean`),
  `isManifoldWithCorners_iff` (`IsManifoldWithCorners n` of `TangentGerm.lean` is a corner
  structure all of whose charts have dimension `n`), `IsManifoldWithCorners.hasCornerStructure`.
* `MChart.compRetract`, `MChart.compRetract_isChart`: the chart `f ∘ φ` for an sc-diffeomorphism
  `f` between the retract `(O, C, E)` of `φ` and another retract (Definition 2.7), a chart of the
  M-polyfold; `MChart.compDiffeo` is the special case of an sc-diffeomorphism between relatively
  open sets.
* **Theorem 4.2**: `MPolyfold.theorem_4_2` (the text's statement, for tame `X`) and
  `MPolyfold.theorem_4_2_general` (the same for every M-polyfold).  (i) ⇒ (ii):
  `isScSmoothMap_toLevelOne_of_cover` (Proposition 4.8 in each corner chart, whose model is an
  sc⁺-retract by `remark_4_3_const`) and `MChart.IsCornerChart.exists_centred_tame` (the corner
  chart re-centred at `x`, `MChart.recentre`, modelled on a relatively open subset of `C_{φ(x)}`;
  `tangentSpace_relOpen`: `T₀O = E`; `isInGoodPosition_top`).  (ii) ⇒ (i):
  `CornerChartData` (the closed good complement `Y`, the projection `p` along `Y`, `W`, `V`, `Γ`
  of Proposition 4.9), `exists_cornerChartData`, the chart `CornerChartData.chart = p ∘ ψ` on
  `ψ⁻¹(W)` with `chart_isChart`, `chart_isCornerChart`, `theorem_4_2_chart`, and
  `hasCornerStructure_of_centred` (without the tameness of the charts).

## What the text leaves implicit, and the choices made

* **Several dimensions.**  Definition 4.1 allows the dimension of `C ⊆ ℝⁿ` to vary from chart to
  chart, so `HasCornerStructure` is not `IsManifoldWithCorners n` (fixed `n`) but the analogue of
  `IsManifoldWithCornersLoc`; that the dimension is locally constant (invariance of dimension for
  the `C^∞` transition maps) is not formalized.
* **The constant sc-structure** is part of the definition (the model space is `ScBanach.const V`).
  It is no restriction: an sc-Banach space with finite-dimensional `E₀` is sc-isomorphic to `E₀`
  with the constant structure (Finding Chapter 4, item 6), and the identity map is an
  sc-diffeomorphism between the two models (`IsRelOpenInQuadrant.isScDiffeoQuadrant_toConst`).
* "`φ : V → U` an sc-diffeomorphism" and "sc-smoothly compatible" are read as: the charts are
  compatible with the charts of `X` (`MPolyfold.IsChart`), i.e. the corner atlas is equivalent to
  the atlas of `X` (`MAtlas.Equiv`, as for `IsTame` and `IsManifoldWithCorners`).  "The atlas
  defines the structure of a smooth manifold with boundary with corners" is formalized as the
  `C^∞` property of the transition maps; no link to Mathlib's `ModelWithCorners` is made (the
  models vary from chart to chart).
* **Centred charts.**  (ii) asks for charts with `ψ(x) = 0`; in (i) ⇒ (ii) they are obtained by
  re-centring the corner chart at `x` (Finding Chapter 4, item 1), which the text does not
  mention: the model becomes a relatively open subset of the partial quadrant `C_{φ(x)}` (not of
  `C`), still in the same finite-dimensional space, and the text's checks "the identity is tame,
  `U = U_∞`, `1₀¹` sc-smooth" do not cover `T₀O = E` and its good position (complement `0`).
* **Tameness is not used.**  Neither the tameness of `X` nor that of the charts in (ii) enters the
  proof of (ii) ⇒ (i) (Proposition 4.9 does not need it), and (i) makes `X` tame
  (`HasCornerStructure.isTame`); `theorem_4_2_general` drops the hypothesis.
* **The projection.**  As in Proposition 4.9 (Findings Chapter 4, items 20–21) `p` is the
  projection onto `T₀O` along a *closed* good complement `Y`, not `Dt(0)`.  Here nothing is added:
  a closed good complement exists for every finite-dimensional subspace in good position
  (`exists_proj_goodComplement`, the normal form of Proposition 3.22), and it is chosen.
* **Compatibility of the charts `p ∘ ψ`** ("a smoothly compatible atlas") is not argued in the
  text: `p ∘ ψ` is compatible with every chart `φ'` of `X` because its transition maps are
  `(φ' ∘ ψ⁻¹) ∘ Γ` and `p ∘ (ψ ∘ φ'⁻¹)`, compositions of sc-smooth maps between retracts
  (`MChart.compRetract_isChart`); two such charts are then compatible with each other by the
  locality of compatibility (`MPolyfold.IsChart.compatible`), and their atlas is equivalent to that
  of `X` (`hasCornerStructure_iff`) — the pattern of `theorem_3_27_isChart` and
  `theorem_3_27_atlas_equiv`.
-/

open Set Filter Topology Function Module
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### Finite-dimensional sc-Banach spaces: every point is smooth -/

/-- In an sc-Banach space with finite-dimensional `E₀` every point is smooth (all levels are equal,
`ScBanach.toBase_surjective`). -/
theorem ScBanach.mem_smooth_of_finiteDimensional (E : ScBanach) [FiniteDimensional ℝ (E 0)]
    (x : E 0) : x ∈ E.smooth :=
  (E.mem_smooth_iff).2 fun m => E.toBase_surjective m x

/-! ### The tangent space of a relatively open subset of a partial quadrant -/

section RelOpen

variable {E : ScBanach} {C U : Set (E 0)}

/-- The tangent space of a relatively open subset `U` of a partial quadrant (the retract of the
identity retraction) is the whole space: `T_xU = E` for `x ∈ U₁`. -/
theorem tangentSpace_relOpen (hU : IsRelOpenInQuadrant E C U) {x : E 1}
    (hx : E.toBase 1 x ∈ U) : tangentSpace E C U x = univ := by
  have hret : (ScRetraction.id hU).retract = U := image_id U
  have hx' : x ∈ E.lvlSet (ScRetraction.id hU).retract 1 := by rw [hret]; exact hx
  have h := tangentSpace_eq_range (ScRetraction.id hU) hx'
  rw [hret] at h
  rw [h]
  have hD : scDeriv (ScRetraction.id hU).U (ScRetraction.id hU) x =
      ContinuousLinearMap.id ℝ (E 0) :=
    IsSc1.scDeriv_eqOn (isSc1With_id U) (hU.isScDomain.uniqueDiffWithinAt 1) hx
  rw [hD]
  exact range_id

/-- The whole space is in good position to a partial quadrant (the good complement `0`). -/
theorem isInGoodPosition_top (hC : IsPartialQuadrant E C) : IsInGoodPosition E C ⊤ where
  interior_nonempty := by
    obtain ⟨z, hz⟩ := hC.interior_lvlSet_nonempty 0
    have hopen : IsOpenMap (Subtype.val : (⊤ : Submodule ℝ (E 0)) → E 0) :=
      IsOpen.isOpenMap_subtype_val (s := ((⊤ : Submodule ℝ (E 0)) : Set (E 0)))
        (by rw [Submodule.top_coe]; exact isOpen_univ)
    refine ⟨⟨z, Submodule.mem_top⟩, ?_⟩
    rw [← hopen.preimage_interior_eq_interior_preimage continuous_subtype_val]
    exact hz
  exists_goodComplement := ⟨⊥, isCompl_top_bot, 1, one_pos, fun x _ p hp _ => by
    rw [(Submodule.mem_bot ℝ).1 hp, add_zero]⟩

end RelOpen

/-! ### Charts composed with an sc-diffeomorphism between retracts -/

section CompRetract

universe u

variable {X : Type u} [TopologicalSpace X] (φ : MChart X) (M : LocalModel)
  {f : φ.model.E 0 → M.E 0} {g : M.E 0 → φ.model.E 0}

/-- **The chart `f ∘ φ`** for a chart `φ : V → O` and an sc-diffeomorphism `f : O → O'` between
the retracts `(O, C, E)` and `(O', C', E')` (Definition 2.7, with inverse `g`): a chart onto the
model `M = (O', C', E')`.  (`MChart.compDiffeo` is the case of an sc-diffeomorphism of relatively
open sets containing `O`.) -/
def MChart.compRetract
    (hf : IsScSmoothRetractMap φ.model.E φ.model.C φ.model.O M.E M.C M.O f)
    (hg : IsScSmoothRetractMap M.E M.C M.O φ.model.E φ.model.C φ.model.O g)
    (hgf : ∀ z ∈ φ.model.O, g (f z) = z) (hfg : ∀ w ∈ M.O, f (g w) = w) : MChart X where
  model := M
  toPartialEquiv :=
    { toFun := f ∘ φ
      invFun := φ.symm ∘ g
      source := φ.source
      target := M.O
      map_source' := fun x hx => hf.mapsTo (φ.mapsTo_model x hx)
      map_target' := fun w hw => φ.symm_mapsTo (hg.mapsTo hw)
      left_inv' := fun x hx => by
        simp only [Function.comp_apply]
        rw [hgf _ (φ.mapsTo_model x hx), φ.symm_apply_apply hx]
      right_inv' := fun w hw => by
        simp only [Function.comp_apply]
        rw [φ.apply_symm_apply (hg.mapsTo hw), hfg w hw] }
  isOpen_source := φ.isOpen_source
  target_eq := rfl
  continuousOn_toFun :=
    (hf.continuousOn φ.model.isScRetract).comp φ.continuousOn_toFun fun x hx => φ.mapsTo_model x hx
  continuousOn_invFun := φ.continuousOn_invFun.comp (hg.continuousOn M.isScRetract) hg.mapsTo

variable {φ M}
variable (hf : IsScSmoothRetractMap φ.model.E φ.model.C φ.model.O M.E M.C M.O f)
    (hg : IsScSmoothRetractMap M.E M.C M.O φ.model.E φ.model.C φ.model.O g)
    (hgf : ∀ z ∈ φ.model.O, g (f z) = z) (hfg : ∀ w ∈ M.O, f (g w) = w)

lemma MChart.compRetract_source : (φ.compRetract M hf hg hgf hfg).source = φ.source := rfl

lemma MChart.compRetract_apply (x : X) : φ.compRetract M hf hg hgf hfg x = f (φ x) := rfl

lemma MChart.compRetract_model : (φ.compRetract M hf hg hgf hfg).model = M := rfl

/-- **The chart `f ∘ φ` is a chart of the M-polyfold structure**: its transition maps to a chart
`φ'` of the atlas are `(φ' ∘ φ⁻¹) ∘ g` and `f ∘ (φ ∘ φ'⁻¹)`, compositions of sc-smooth maps between
retracts (the pattern of `MChart.compDiffeo_isChart` and `theorem_3_27_isChart`). -/
theorem MChart.compRetract_isChart [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
    (hφ : P.IsChart φ) : P.IsChart (φ.compRetract M hf hg hgf hfg) := by
  intro φ' hφ'
  have hcompat := MPolyfold.IsChart.compatible P hφ (P.isChart_of_mem hφ')
  set κ := φ.compRetract M hf hg hgf hfg with hκ
  have hov : κ.overlap φ' = f '' (φ.overlap φ') := by
    change (f ∘ φ) '' (φ.source ∩ φ'.source) = f '' (φ '' (φ.source ∩ φ'.source))
    rw [image_comp]
  constructor
  · -- `κ → φ'`: `(φ' ∘ φ⁻¹) ∘ g`
    have h1 : IsScSmoothRetractMap M.E M.C (κ.overlap φ') φ.model.E φ.model.C (φ.overlap φ') g := by
      refine (hg.mono_source M.isScRetract (κ.overlap_subset φ')).mono_target ?_
      rw [hov]
      rintro _ ⟨z, hz, rfl⟩
      rw [hgf z (φ.overlap_subset φ' hz)]
      exact hz
    exact hcompat.1.comp h1 (φ.isScRetract_overlap φ')
  · -- `φ' → κ`: `f ∘ (φ ∘ φ'⁻¹)`
    have h1 : IsScSmoothRetractMap φ.model.E φ.model.C (φ.overlap φ') M.E M.C (κ.overlap φ') f := by
      refine (hf.mono_source φ.model.isScRetract (φ.overlap_subset φ')).mono_target ?_
      rw [hov]
      exact mapsTo_image f _
    exact h1.comp hcompat.2 (φ.isScRetract_overlap φ')

end CompRetract

/-! ### Corner charts and Definition 4.1 -/

section Corner

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A **corner chart** `(V, φ, (U, C, ℝⁿ))` of Definition 4.1: the local model is a relatively open
subset `U` of a partial quadrant `C` in a finite-dimensional space `V` with the **constant
sc-structure** (`ScBanach.const V`), with the identity retraction (`LocalModel.ofRelOpen`). -/
def MChart.IsCornerChart (χ : MChart X) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V) (_ : FiniteDimensional ℝ V)
    (C U : Set V) (hU : IsRelOpenInQuadrant (ScBanach.const V) C U),
    χ.model = LocalModel.ofRelOpen hU

namespace MChart.IsCornerChart

variable {χ : MChart X} (h : χ.IsCornerChart)
include h

/-- The model of a corner chart is a relatively open subset of a partial quadrant. -/
theorem isRelOpenInQuadrant : IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O := by
  obtain ⟨V, _, _, _, C, U, hU, hχ⟩ := h
  rw [hχ]
  exact hU

/-- The model space of a corner chart is finite-dimensional. -/
theorem finiteDimensional : FiniteDimensional ℝ (χ.model.E 0) := by
  obtain ⟨V, _, _, _, C, U, hU, hχ⟩ := h
  rw [hχ]
  change FiniteDimensional ℝ V
  infer_instance

/-- The model of a corner chart is a tame retract (the identity retraction,
`ScRetraction.id_isTame`). -/
theorem isTameRetract : IsTameRetract χ.model.E χ.model.C χ.model.O :=
  ⟨ScRetraction.id h.isRelOpenInQuadrant, image_id _, ScRetraction.id_isTame _⟩

/-- The model of a corner chart is an sc⁺-retract (Remark 4.3: a retract in a finite-dimensional
space with the constant structure is an sc⁺-retract, `remark_4_3_const`). -/
theorem isScPlusRetract : IsScPlusRetract χ.model.E χ.model.C χ.model.O := by
  obtain ⟨V, _, _, _, C, U, hU, hχ⟩ := h
  rw [hχ]
  exact (remark_4_3_const V).2.2 C U hU.isScRetract

/-- Every point of the model space of a corner chart is smooth. -/
theorem mem_smooth (z : χ.model.E 0) : z ∈ χ.model.E.smooth := by
  have := h.finiteDimensional
  exact χ.model.E.mem_smooth_of_finiteDimensional z

end MChart.IsCornerChart

namespace MPolyfold

variable [T2Space X] [ParacompactSpace X]

/-- **Definition 4.1**: the M-polyfold `X` **has a compatible smooth manifold structure with
boundary with corners** if it admits an atlas, equivalent to its atlas, of sc-smoothly compatible
corner charts `(V, φ, (U, C, ℝⁿ))`: `φ : V → U` an sc-diffeomorphism onto a relatively open subset
`U` of a partial quadrant `C` in a finite-dimensional space with the constant sc-structure
(`MChart.IsCornerChart`).  As in the text, the dimension may vary from chart to chart. -/
def HasCornerStructure (P : MPolyfold X) : Prop :=
  ∃ A : MAtlas X, A.Equiv P.atlas ∧ ∀ χ ∈ A.charts, χ.IsCornerChart

variable {P : MPolyfold X}

/-- **Definition 4.1 is local**: `X` has a corner structure iff every point lies in a corner chart
of the M-polyfold structure (the atlas of all corner charts of the maximal atlas is then
equivalent to the atlas of `X`). -/
theorem hasCornerStructure_iff :
    P.HasCornerStructure ↔
      ∀ x : X, ∃ χ : MChart X, P.IsChart χ ∧ x ∈ χ.source ∧ χ.IsCornerChart := by
  constructor
  · rintro ⟨A, hA, hc⟩ x
    obtain ⟨χ, hχ, hx⟩ := A.cover x
    exact ⟨χ, P.isChart_of_mem_equiv hA hχ, hx, hc χ hχ⟩
  · intro h
    let A : MAtlas X :=
      { charts := {χ | P.IsChart χ ∧ χ.IsCornerChart}
        compatible := fun φ hφ ψ hψ => IsChart.compatible P hφ.1 hψ.1
        cover := fun x => by
          obtain ⟨χ, hχ, hx, hc⟩ := h x
          exact ⟨χ, ⟨hχ, hc⟩, hx⟩ }
    exact ⟨A, (MAtlas.equiv_iff _ _).2 fun φ hφ ψ hψ => hφ.1 ψ hψ, fun φ hφ => hφ.2⟩

/-- **A manifold with boundary with corners is tame** (its corner charts are modelled on the tame
retracts `(U, C, ℝⁿ)` with the identity retraction). -/
theorem HasCornerStructure.isTame (h : P.HasCornerStructure) : P.IsTame := by
  obtain ⟨A, hA, hc⟩ := h
  exact ⟨A, hA, fun χ hχ => (hc χ hχ).isTameRetract⟩

end MPolyfold

end Corner

/-! ### The transition maps are classically smooth -/

section Transition

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The overlap `φ(V ∩ V')` of a chart whose model is relatively open in a partial quadrant is
relatively open. -/
theorem MChart.isRelOpenInQuadrant_overlap {χ : MChart X}
    (hχ : IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O) (χ' : MChart X) :
    IsRelOpenInQuadrant χ.model.E χ.model.C (χ.overlap χ') := by
  obtain ⟨W, hW, hWeq⟩ := χ.exists_isOpen_image_eq (s := χ.source ∩ χ'.source) inter_subset_left
    (χ.isOpen_source.inter χ'.isOpen_source)
  change IsRelOpenInQuadrant χ.model.E χ.model.C (χ '' (χ.source ∩ χ'.source))
  rw [hWeq]
  exact hχ.inter_isOpen hW

/-- **The transition maps between corner charts are classically smooth** (Definition 4.1: "the
transition maps ... are sc-diffeomorphisms between relatively open subsets of partial quadrants in
finite-dimensional vector spaces, and therefore are classically smooth maps, i.e., of class
`C^∞`"): for compatible corner charts `χ`, `χ'` the transition map `χ' ∘ χ⁻¹` is `C^∞` on the
overlap `χ(V ∩ V')` (one-sided derivatives at the boundary; `isScSmooth_iff_contDiffOn_const`). -/
theorem MChart.IsCornerChart.contDiffOn_transition {χ χ' : MChart X} (hχ : χ.IsCornerChart)
    (hχ' : χ'.IsCornerChart) (h : χ.Compatible χ') :
    ContDiffOn ℝ ∞ (χ.transition χ') (χ.overlap χ') := by
  have hov := MChart.isRelOpenInQuadrant_overlap hχ.isRelOpenInQuadrant χ'
  have hsm : IsScSmooth (χ.overlap χ') (χ.transition χ') :=
    h.1.comp_isScSmooth (ScRetraction.id hov) (image_id _)
  obtain ⟨M, pe, ho, ht, hc1, hc2⟩ := χ
  obtain ⟨M', pe', ho', ht', hc1', hc2'⟩ := χ'
  obtain ⟨V, _, _, _, C, U, hU, hM⟩ := hχ
  obtain ⟨V', _, _, _, C', U', hU', hM'⟩ := hχ'
  change M = _ at hM
  change M' = _ at hM'
  subst hM hM'
  exact (isScSmooth_iff_contDiffOn_const (V := V) (W := V') hov.isScDomain _).1 hsm

end Transition

/-! ### Finite-dimensional models carry the constant structure -/

section ConstModel

universe u

variable {E : ScBanach} [FiniteDimensional ℝ (E 0)]

/-- A partial quadrant of a finite-dimensional `E` is a partial quadrant of `E₀` with the constant
structure (through `ScBanach.scIsoConst`). -/
theorem IsPartialQuadrant.toConst {C : Set (E 0)} (hC : IsPartialQuadrant E C) :
    IsPartialQuadrant (ScBanach.const (E 0)) C := by
  obtain ⟨n, W, T, rfl⟩ := hC
  refine ⟨n, W, E.scIsoConst.symm.trans T, ?_⟩
  ext x
  have hx : (E.scIsoConst 0).symm x = x := by
    apply (E.scIsoConst 0).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, ScBanach.scIsoConst_apply, ScScale.toBase_zero]
  change T 0 x ∈ quadrant n W 0 ↔ T 0 ((E.scIsoConst 0).symm x) ∈ quadrant n W 0
  rw [hx]

theorem IsRelOpenInQuadrant.toConst {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) :
    IsRelOpenInQuadrant (ScBanach.const (E 0)) C U :=
  ⟨hU.isPartialQuadrant.toConst, hU.relOpen⟩

/-- The identity `E₀ → E₀` is an sc-diffeomorphism from `(U, C, E)` onto `(U, C, E₀)` with the
constant structure (the sc-isomorphism `ScBanach.scIsoConst` of a finite-dimensional space). -/
theorem IsRelOpenInQuadrant.isScDiffeoQuadrant_toConst {C U : Set (E 0)}
    (hU : IsRelOpenInQuadrant E C U) :
    IsScDiffeoQuadrant hU hU.toConst (id : E 0 → (ScBanach.const (E 0)) 0)
      (id : (ScBanach.const (E 0)) 0 → E 0) where
  isScSmooth := by
    refine (E.scIsoConst.toScOperator.isScSmooth hU.isScDomain).congr hU.isScDomain fun x _ => ?_
    change E.toBase 0 x = x
    rfl
  isScSmooth_inv := by
    refine (E.scIsoConst.symm.toScOperator.isScSmooth hU.toConst.isScDomain).congr
      hU.toConst.isScDomain fun x _ => ?_
    change (E.scIsoConst 0).symm x = x
    apply (E.scIsoConst 0).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, ScBanach.scIsoConst_apply, ScScale.toBase_zero]
  mapsTo := mapsTo_id U
  mapsTo_inv := mapsTo_id U
  left_inv _ _ := rfl
  right_inv _ _ := rfl

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **The constant sc-structure is no restriction** (Definition 4.1 and Finding Chapter 4, item 6):
a chart of `X` modelled on a relatively open subset of a partial quadrant in an sc-Banach space
with finite-dimensional `E₀` is, with the same map, a corner chart modelled on `E₀` with the
constant structure (`MChart.compDiffeo` with the identity, an sc-diffeomorphism by
`ScBanach.scIsoConst`). -/
theorem MChart.exists_isCornerChart_of_finiteDimensional {χ : MChart X} (hχ : P.IsChart χ)
    (hU : IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O)
    (hfin : FiniteDimensional ℝ (χ.model.E 0)) :
    ∃ χ' : MChart X, P.IsChart χ' ∧ χ'.source = χ.source ∧ χ'.IsCornerChart ∧
      finrank ℝ (χ'.model.E 0) = finrank ℝ (χ.model.E 0) := by
  have h := hU.isScDiffeoQuadrant_toConst
  have hU' : IsRelOpenInQuadrant (ScBanach.const (χ.model.E 0)) χ.model.C
      ((id : (ScBanach.const (χ.model.E 0)) 0 → _) '' χ.model.O) := by
    rw [image_id]; exact hU.toConst
  refine ⟨χ.compDiffeo h subset_rfl hU'.isScRetract, MChart.compDiffeo_isChart hχ h subset_rfl _,
    rfl,
    ⟨χ.model.E 0, inferInstance, inferInstance, hfin, χ.model.C, _, hU', rfl⟩, rfl⟩

end ConstModel

/-! ### Definition 4.1 and the manifolds with corners of Chapter 3 -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **Definition 4.1 with arbitrary finite-dimensional models**: `X` has a corner structure iff it
has an equivalent atlas of charts modelled on relatively open subsets of partial quadrants in
sc-Banach spaces with finite-dimensional `E₀` (no condition on the sc-structure, which is then
the constant one up to `ScBanach.scIsoConst`).  The right-hand side is, verbatim, the definition
of `MPolyfold.IsManifoldWithCornersLoc` (`GlobalIFTTheorems.lean`, the manifolds with corners of
locally constant dimension of Theorem 3.27, not imported here). -/
theorem hasCornerStructure_iff_finiteDimensional :
    P.HasCornerStructure ↔ ∃ A : MAtlas X, A.Equiv P.atlas ∧ ∀ χ ∈ A.charts,
      IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O ∧ FiniteDimensional ℝ (χ.model.E 0) := by
  constructor
  · rintro ⟨A, hA, hc⟩
    exact ⟨A, hA, fun χ hχ => ⟨(hc χ hχ).isRelOpenInQuadrant, (hc χ hχ).finiteDimensional⟩⟩
  · rintro ⟨A, hA, hc⟩
    refine hasCornerStructure_iff.2 fun x => ?_
    obtain ⟨χ, hχ, hx⟩ := A.cover x
    obtain ⟨χ', hχ', hsrc, hcorner, -⟩ :=
      MChart.exists_isCornerChart_of_finiteDimensional (P.isChart_of_mem_equiv hA hχ) (hc χ hχ).1
        (hc χ hχ).2
    exact ⟨χ', hχ', hsrc ▸ hx, hcorner⟩

/-- **The manifolds with corners of dimension `n` of Theorem 3.27** (`IsManifoldWithCorners n`,
`TangentGerm.lean`) are the M-polyfolds with a corner structure of Definition 4.1 all of whose
corner charts have dimension `n`. -/
theorem isManifoldWithCorners_iff {n : ℕ} :
    P.IsManifoldWithCorners n ↔ ∃ A : MAtlas X, A.Equiv P.atlas ∧ ∀ χ ∈ A.charts,
      χ.IsCornerChart ∧ finrank ℝ (χ.model.E 0) = n := by
  constructor
  · rintro ⟨A, hA, hc⟩
    let B : MAtlas X :=
      { charts := {χ | P.IsChart χ ∧ χ.IsCornerChart ∧ finrank ℝ (χ.model.E 0) = n}
        compatible := fun φ hφ ψ hψ => IsChart.compatible P hφ.1 hψ.1
        cover := fun x => by
          obtain ⟨χ, hχ, hx⟩ := A.cover x
          obtain ⟨χ', hχ', hsrc, hcorner, hdim⟩ :=
            MChart.exists_isCornerChart_of_finiteDimensional (P.isChart_of_mem_equiv hA hχ)
              (hc χ hχ).1 (hc χ hχ).2.1
          exact ⟨χ', ⟨hχ', hcorner, hdim.trans (hc χ hχ).2.2⟩, hsrc ▸ hx⟩ }
    exact ⟨B, (MAtlas.equiv_iff _ _).2 fun φ hφ ψ hψ => hφ.1 ψ hψ, fun φ hφ => hφ.2⟩
  · rintro ⟨A, hA, hc⟩
    exact ⟨A, hA, fun χ hχ => ⟨(hc χ hχ).1.isRelOpenInQuadrant, (hc χ hχ).1.finiteDimensional,
      (hc χ hχ).2⟩⟩

/-- A manifold with corners of dimension `n` (Theorem 3.27) has a corner structure in the sense of
Definition 4.1. -/
theorem IsManifoldWithCorners.hasCornerStructure {n : ℕ} (h : P.IsManifoldWithCorners n) :
    P.HasCornerStructure := by
  obtain ⟨A, hA, hc⟩ := isManifoldWithCorners_iff.1 h
  exact ⟨A, hA, fun χ hχ => (hc χ hχ).1⟩

end MPolyfold

/-! ### The first condition of Theorem 4.2 (ii) from a cover by sc⁺-retracts -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- If every point lies in a chart modelled on an sc⁺-retract, then `X₀ = X_∞` and
`1₀¹ : X → X¹` is sc-smooth (Proposition 4.8 in each chart, `proposition_4_8_chart`, and the
locality of sc-smoothness; the direction (⇐) of `isScSmoothMap_toLevelOne_iff` with a cover in
place of all charts). -/
theorem isScSmoothMap_toLevelOne_of_cover (x₀ : P.Level 1)
    (h : ∀ x, ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧
      IsScPlusRetract φ.model.E φ.model.C φ.model.O) :
    (∀ x, x ∈ P.smoothSet) ∧ P.IsScSmoothMap P.shift (P.toLevelOne x₀) := by
  have hloc : ∀ x, ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧ φ.source ⊆ P.smoothSet ∧
      P.IsScSmoothOn P.shift (P.toLevelOne x₀) φ.source := fun x => by
    obtain ⟨φ, hφ, hx, hplus⟩ := h x
    exact ⟨φ, hφ, hx, (proposition_4_8_chart hφ x₀).1 hplus⟩
  have hsm : ∀ x, x ∈ P.smoothSet := fun x => by
    obtain ⟨φ, -, hx, hsub, -⟩ := hloc x
    exact hsub hx
  refine ⟨hsm, IsScSmoothOn.of_exists_charts isOpen_univ ?_ fun x _ => ?_⟩
  · refine continuousOn_univ.2 (continuous_iff_continuousAt.2 fun x => ?_)
    obtain ⟨φ, -, hx, -, hφs⟩ := hloc x
    exact hφs.continuousOn.continuousAt (φ.isOpen_source.mem_nhds hx)
  · obtain ⟨φ, hφ, hx, hsub, hφs⟩ := hloc x
    have hlev : MapsTo (P.toLevelOne x₀) φ.source (levelChart hφ x₀).source := fun y hy => by
      change P.levelVal 1 (P.toLevelOne x₀ y) ∈ φ.source
      rw [levelVal_toLevelOne x₀ (smoothSet_subset_levelSet 1 (hsub hy))]; exact hy
    exact ⟨φ, levelChart hφ x₀, φ.source, hφ, P.shift_isChart hφ x₀, φ.isOpen_source, hx,
      fun y hy => ⟨mem_univ _, hy⟩, hlev, hφs.smooth φ (levelChart hφ x₀) hφ
        (P.shift_isChart hφ x₀) φ.source φ.isOpen_source (fun y hy => ⟨hy, hy⟩) hlev⟩

end MPolyfold

/-! ### (i) ⇒ (ii): centred corner charts -/

section Centred

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- The translate `S − e` of a set is its preimage under `u ↦ u + e`. -/
lemma image_sub_const_eq_preimage_add' {V : Type*} [AddGroup V] (S : Set V) (e : V) :
    (fun v => v - e) '' S = (fun u => u + e) ⁻¹' S := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    change v - e + e ∈ S
    rw [sub_add_cancel]; exact hv
  · intro hz
    exact ⟨z + e, hz, add_sub_cancel_right z e⟩

/-- **Every point of a corner chart is the centre of a corner-type chart** (the re-centring
`MChart.recentre` at `e = χ(x)`, which is smooth since all points of a finite-dimensional space
are): a chart `ψ` of `X` with `ψ(x) = 0`, modelled on a relatively open subset of the partial
quadrant `C_e` in the same finite-dimensional space. -/
theorem MChart.IsCornerChart.exists_centred {χ : MChart X} (hχ : P.IsChart χ)
    (hc : χ.IsCornerChart) {x : X} (hx : x ∈ χ.source) :
    ∃ ψ : MChart X, P.IsChart ψ ∧ x ∈ ψ.source ∧ ψ x = 0 ∧
      IsRelOpenInQuadrant ψ.model.E ψ.model.C ψ.model.O ∧ FiniteDimensional ℝ (ψ.model.E 0) := by
  obtain ⟨n, W, T, hT⟩ := χ.model.isPartialQuadrant
  have he : χ x ∈ χ.model.E.smooth := hc.mem_smooth (χ x)
  refine ⟨χ.recentre T hT (χ x) he, χ.recentre_isChart T hT (χ x) he hχ,
    χ.mem_recentre_source T hT (χ x) he hx rfl, χ.recentre_apply_self T hT (χ x) he rfl, ?_,
    hc.finiteDimensional⟩
  have hG := isOpen_recentreNbhd T (χ x)
  have h := relOpen_translate hT (hc.isRelOpenInQuadrant.inter_isOpen hG) inter_subset_right
  rw [← image_sub_const_eq_preimage_add'] at h
  rw [MChart.recentre_model_O]
  exact h

/-- **(i) ⇒ (ii) at one point**: a point of a corner chart lies in a tame chart `ψ` of `X` with
`ψ(x) = 0`, whose model is an sc⁺-retract with `T₀O = E` finite-dimensional and in good position to
`C` (the identity retraction of a relatively open subset of a partial quadrant is tame, its
tangent space is the whole space, and the whole space is in good position with the complement
`0`). -/
theorem MChart.IsCornerChart.exists_centred_tame {χ : MChart X} (hχ : P.IsChart χ)
    (hc : χ.IsCornerChart) {x : X} (hx : x ∈ χ.source) :
    ∃ ψ : MChart X, P.IsChart ψ ∧ x ∈ ψ.source ∧ ψ x = 0 ∧
      IsTameRetract ψ.model.E ψ.model.C ψ.model.O ∧
      ∃ N : Submodule ℝ (ψ.model.E 0), (N : Set (ψ.model.E 0)) =
        tangentSpace ψ.model.E ψ.model.C ψ.model.O 0 ∧ FiniteDimensional ℝ N ∧
        IsInGoodPosition ψ.model.E ψ.model.C N := by
  obtain ⟨ψ, hψ, hxψ, h0, hrel, hfin⟩ := hc.exists_centred hχ hx
  refine ⟨ψ, hψ, hxψ, h0, ⟨ScRetraction.id hrel, image_id _, ScRetraction.id_isTame _⟩, ⊤, ?_,
    inferInstance, isInGoodPosition_top ψ.model.isPartialQuadrant⟩
  rw [Submodule.top_coe, tangentSpace_relOpen hrel]
  rw [map_zero, ← h0]
  exact ψ.mapsTo_model x hxψ

end Centred

/-! ### (ii) ⇒ (i): the corner chart `p ∘ ψ` -/

section CornerChart

universe u

variable {X : Type u} [TopologicalSpace X]

/-- **The data of the corner chart `p ∘ ψ`** of the proof of Theorem 4.2 for a chart `ψ` of `X`
with `0 ∈ O` and a finite-dimensional subspace `N` (the tangent space `T₀O`): a closed good
complement `Y` of `N`, the projection `p : E → N` along `Y`, an open `W ∋ 0` in `E`, a relatively
open `V ∋ 0` in the partial quadrant `N ∩ C` of `N`, and the inverse `Γ : V → O ∩ W` of `p`, such
that `p` and `Γ` are mutually inverse sc-smooth maps between the retracts `(O ∩ W, C, E)` and
`(V, N ∩ C, N)` (Proposition 4.9). -/
structure CornerChartData (ψ : MChart X) (N : Submodule ℝ (ψ.model.E 0)) [FiniteDimensional ℝ N]
    where
  /-- The good complement `Y` of `N`. -/
  Y : Submodule ℝ (ψ.model.E 0)
  isGoodComplement : IsGoodComplement ψ.model.E ψ.model.C N Y
  isClosed_Y : IsClosed (Y : Set (ψ.model.E 0))
  /-- The projection `p : E → N` along `Y`. -/
  p : ψ.model.E 0 →L[ℝ] N
  p_N : ∀ n : N, p n = n
  p_Y : ∀ y ∈ Y, p y = 0
  /-- The open set `W` of `E` with `O ∩ W` the domain of `p`. -/
  W : Set (ψ.model.E 0)
  isOpen_W : IsOpen W
  zero_mem_W : (0 : ψ.model.E 0) ∈ W
  /-- The relatively open subset `V` of `N ∩ C`. -/
  V : Set N
  V_relOpen : IsRelOpenInQuadrant (ScBanach.const N) (Subtype.val ⁻¹' ψ.model.C) V
  zero_mem_V : (0 : N) ∈ V
  /-- The inverse `Γ : V → O ∩ W` of `p`. -/
  Γ : N → ψ.model.E 0
  p_map : IsScSmoothRetractMap ψ.model.E ψ.model.C (ψ.model.O ∩ W) (ScBanach.const N)
    (Subtype.val ⁻¹' ψ.model.C) V p
  Γ_map : IsScSmoothRetractMap (ScBanach.const N) (Subtype.val ⁻¹' ψ.model.C) V ψ.model.E
    ψ.model.C (ψ.model.O ∩ W) Γ
  Γ_p : ∀ u ∈ ψ.model.O ∩ W, Γ (p u) = u
  p_Γ : ∀ a ∈ V, p (Γ a) = a

namespace CornerChartData

variable {ψ : MChart X} {N : Submodule ℝ (ψ.model.E 0)} [FiniteDimensional ℝ N]
  (d : CornerChartData ψ N)

/-- The local model `(V, N ∩ C, N)` of the corner chart. -/
def model : LocalModel := LocalModel.ofRelOpen d.V_relOpen

/-- The domain `ψ⁻¹(W)` of the corner chart. -/
abbrev source : Set X := ψ.source ∩ ψ ⁻¹' d.W

lemma isOpen_source : IsOpen d.source :=
  ψ.continuousOn_toFun.isOpen_inter_preimage ψ.isOpen_source d.isOpen_W

lemma image_source : ψ '' d.source = ψ.model.O ∩ d.W := by
  rw [source, image_inter_preimage, ψ.image_source]

/-- **The corner chart `p ∘ ψ : ψ⁻¹(W) → V`** of the proof of Theorem 4.2: the chart `ψ`
restricted to `ψ⁻¹(W)` (`MChart.restrict`) composed with the sc-diffeomorphism `p : O ∩ W → V` of
Proposition 4.9 (`MChart.compRetract`), modelled on `(V, N ∩ C, N)`. -/
def chart : MChart X :=
  (ψ.restrict (s := d.source) (fun _ hy => hy.1) d.isOpen_source).compRetract d.model
    (f := d.p) (g := d.Γ)
    (by have h := d.p_map; rw [← d.image_source] at h; exact h)
    (by have h := d.Γ_map; rw [← d.image_source] at h; exact h)
    (by have h := d.Γ_p; rw [← d.image_source] at h; exact h)
    d.p_Γ

lemma chart_source : d.chart.source = ψ.source ∩ ψ ⁻¹' d.W := rfl

lemma chart_apply (y : X) : (d.chart y : N) = d.p (ψ y) := rfl

lemma chart_symm_apply (a : N) : d.chart.symm a = ψ.symm (d.Γ a) := rfl

lemma chart_model : d.chart.model = LocalModel.ofRelOpen d.V_relOpen := rfl

/-- The corner chart `p ∘ ψ` is a corner chart (Definition 4.1), modelled on `(V, N ∩ C, N)`. -/
theorem chart_isCornerChart : d.chart.IsCornerChart :=
  ⟨N, inferInstance, inferInstance, inferInstance, _, _, d.V_relOpen, rfl⟩

/-- The corner chart `p ∘ ψ` is a chart of the M-polyfold structure (`MChart.compRetract_isChart`
for the restriction of `ψ`). -/
theorem chart_isChart [T2Space X] [ParacompactSpace X] {P : MPolyfold X} (hψ : P.IsChart ψ) :
    P.IsChart d.chart :=
  MChart.compRetract_isChart _ _ _ _
    (MPolyfold.IsChart.restrict P hψ (fun _ hy => hy.1) d.isOpen_source)

/-- A point `x` with `ψ(x) = 0` lies in the domain of the corner chart, and `(p ∘ ψ)(x) = 0`. -/
theorem mem_chart_source {x : X} (hx : x ∈ ψ.source) (h0 : ψ x = 0) : x ∈ d.chart.source :=
  ⟨hx, by rw [mem_preimage, h0]; exact d.zero_mem_W⟩

theorem chart_apply_eq_zero {x : X} (h0 : ψ x = 0) : (d.chart x : N) = 0 := by
  rw [chart_apply, h0, map_zero]
  rfl

end CornerChartData

/-- **Existence of the corner chart data (Proposition 4.9 in a chart)**: if the model `(O, C, E)`
of `ψ` is an sc⁺-retract with `0 ∈ O` and `N = T₀O` is finite-dimensional and in good position to
`C`, then the data of the corner chart `p ∘ ψ` exist: the closed good complement `Y` and the
projection `p` along it come from `exists_proj_goodComplement` (Proposition 3.22's normal form;
`p` even maps `C` into `C`), and `W`, `V`, `Γ` from `proposition_4_9` applied to an
sc⁺-retraction onto `O` (Definition 4.6). -/
theorem exists_cornerChartData {ψ : MChart X}
    (hplus : IsScPlusRetract ψ.model.E ψ.model.C ψ.model.O) (h0 : (0 : ψ.model.E 0) ∈ ψ.model.O)
    {N : Submodule ℝ (ψ.model.E 0)} [FiniteDimensional ℝ N]
    (hN : (N : Set (ψ.model.E 0)) = tangentSpace ψ.model.E ψ.model.C ψ.model.O 0)
    (hgood : IsInGoodPosition ψ.model.E ψ.model.C N) : Nonempty (CornerChartData ψ N) := by
  obtain ⟨R, hR, hRp⟩ := hplus
  obtain ⟨π, hπN, -, hY⟩ := exists_proj_goodComplement ψ.model.isPartialQuadrant hgood
  have h0' : (0 : ψ.model.E 0) ∈ R.retract := hR ▸ h0
  have hN' : (N : Set (ψ.model.E 0)) = tangentSpace ψ.model.E ψ.model.C R.retract 0 := hR ▸ hN
  obtain ⟨W, V, Γ, hW, h0W, hV, h0V, -, hpΓ, -, -, hΓp, -, hpmap, hΓmap⟩ :=
    proposition_4_9 R hRp h0' hN' hgood hY π.isClosed_ker π hπN fun y hy => LinearMap.mem_ker.1 hy
  rw [hR] at hΓp hpmap hΓmap
  exact ⟨⟨_, hY, π.isClosed_ker, π, hπN, fun y hy => LinearMap.mem_ker.1 hy, W, hW, h0W, V, hV,
    h0V, Γ, hpmap, hΓmap, hΓp, hpΓ⟩⟩

end CornerChart

/-! ### Theorem 4.2 -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **The corner charts of (ii) ⇒ (i)** (the proof of Theorem 4.2): if `X₀ = X_∞` and
`1₀¹ : X → X¹` is sc-smooth, then for every chart `ψ : V → O` of `X` with `ψ(x) = 0` whose tangent
space `N = T₀O` is finite-dimensional and in good position to `C`, the chart `p ∘ ψ` on `ψ⁻¹(W)`
(`CornerChartData.chart`: `p` the projection onto `N` along a closed good complement, `W` from
Proposition 4.9) is a corner chart of `X` (Definition 4.1) modelled on `(V, N ∩ C, N)` with
`(p ∘ ψ)(x) = 0`.  *Proof* (the text's): by Proposition 4.8 the model `O` is an sc⁺-retract
(`isScSmoothMap_toLevelOne_iff`), and Proposition 4.9 gives the sc-diffeomorphism
`p : O ∩ W → V`. -/
theorem theorem_4_2_chart (x₀ : P.Level 1) (hsm : ∀ x, x ∈ P.smoothSet)
    (hmap : P.IsScSmoothMap P.shift (P.toLevelOne x₀)) {ψ : MChart X} (hψ : P.IsChart ψ)
    {x : X} (hx : x ∈ ψ.source) (h0 : ψ x = 0) {N : Submodule ℝ (ψ.model.E 0)}
    [FiniteDimensional ℝ N]
    (hN : (N : Set (ψ.model.E 0)) = tangentSpace ψ.model.E ψ.model.C ψ.model.O 0)
    (hgood : IsInGoodPosition ψ.model.E ψ.model.C N) :
    ∃ d : CornerChartData ψ N, P.IsChart d.chart ∧ x ∈ d.chart.source ∧ (d.chart x : N) = 0 ∧
      d.chart.IsCornerChart := by
  have hplus := (isScSmoothMap_toLevelOne_iff x₀).1 ⟨hsm, hmap⟩ ψ hψ
  have h0O : (0 : ψ.model.E 0) ∈ ψ.model.O := h0 ▸ ψ.mapsTo_model x hx
  obtain ⟨d⟩ := exists_cornerChartData hplus h0O hN hgood
  exact ⟨d, d.chart_isChart hψ, d.mem_chart_source hx h0, d.chart_apply_eq_zero h0,
    d.chart_isCornerChart⟩

/-- **Theorem 4.2, (ii) ⇒ (i)**, without the tameness of the charts: if `X₀ = X_∞`, `1₀¹ : X → X¹`
is sc-smooth and every point `x` lies in a chart `ψ` with `ψ(x) = 0` whose `T₀O` is
finite-dimensional and in good position to `C`, then `X` has a corner structure (the charts
`p ∘ ψ` of `theorem_4_2_chart` form an atlas equivalent to the atlas of `X`,
`hasCornerStructure_iff`). -/
theorem hasCornerStructure_of_centred (x₀ : P.Level 1) (hsm : ∀ x, x ∈ P.smoothSet)
    (hmap : P.IsScSmoothMap P.shift (P.toLevelOne x₀))
    (hc : ∀ x, ∃ ψ : MChart X, P.IsChart ψ ∧ x ∈ ψ.source ∧ ψ x = 0 ∧
      ∃ N : Submodule ℝ (ψ.model.E 0), (N : Set (ψ.model.E 0)) =
        tangentSpace ψ.model.E ψ.model.C ψ.model.O 0 ∧ FiniteDimensional ℝ N ∧
        IsInGoodPosition ψ.model.E ψ.model.C N) :
    P.HasCornerStructure := by
  refine hasCornerStructure_iff.2 fun x => ?_
  obtain ⟨ψ, hψ, hx, h0, N, hN, hfin, hgood⟩ := hc x
  obtain ⟨d, hd, hxd, -, hcd⟩ := theorem_4_2_chart x₀ hsm hmap hψ hx h0 hN hgood
  exact ⟨d.chart, hd, hxd, hcd⟩

/-- **Theorem 4.2 (Characterization)**, for every M-polyfold `X` (the tameness of `X` assumed by
the text is not used; `theorem_4_2` is the text's form): the following are equivalent.
(i) `X` has a compatible smooth manifold structure with boundary with corners
(`HasCornerStructure`, Definition 4.1).
(ii) `X₀ = X_∞`, the identity `1₀¹ : X → X¹` is sc-smooth (`toLevelOne x₀`, with an arbitrary
junk value `x₀` off `X₁`), and every point `x` is contained in a tame chart `(V, ψ, (O, C, E))`
of `X` with `ψ(x) = 0` whose tangent space `T₀O` is finite-dimensional and in good position to
the partial quadrant `C`.
*Proof* (the text's). (i) ⇒ (ii): corner charts are modelled on sc⁺-retracts (Remark 4.3), so
`X₀ = X_∞` and `1₀¹` is sc-smooth (Proposition 4.8 in each chart,
`isScSmoothMap_toLevelOne_of_cover`); the corner chart around `x`, re-centred at `x`
(`MChart.recentre`), is a chart onto a relatively open subset of a partial quadrant, tame with the
identity retraction, with `T₀O = E` finite-dimensional and in good position
(`MChart.IsCornerChart.exists_centred_tame`).  (ii) ⇒ (i): `hasCornerStructure_of_centred`
(Propositions 4.8 and 4.9). -/
theorem theorem_4_2_general (x₀ : P.Level 1) :
    P.HasCornerStructure ↔
      (∀ x, x ∈ P.smoothSet) ∧ P.IsScSmoothMap P.shift (P.toLevelOne x₀) ∧
      ∀ x, ∃ ψ : MChart X, P.IsChart ψ ∧ x ∈ ψ.source ∧ ψ x = 0 ∧
        IsTameRetract ψ.model.E ψ.model.C ψ.model.O ∧
        ∃ N : Submodule ℝ (ψ.model.E 0), (N : Set (ψ.model.E 0)) =
          tangentSpace ψ.model.E ψ.model.C ψ.model.O 0 ∧ FiniteDimensional ℝ N ∧
          IsInGoodPosition ψ.model.E ψ.model.C N := by
  constructor
  · intro h
    have hloc := hasCornerStructure_iff.1 h
    obtain ⟨hsm, hmap⟩ := isScSmoothMap_toLevelOne_of_cover x₀ fun x => by
      obtain ⟨χ, hχ, hx, hc⟩ := hloc x
      exact ⟨χ, hχ, hx, hc.isScPlusRetract⟩
    refine ⟨hsm, hmap, fun x => ?_⟩
    obtain ⟨χ, hχ, hx, hc⟩ := hloc x
    exact hc.exists_centred_tame hχ hx
  · rintro ⟨hsm, hmap, hc⟩
    refine hasCornerStructure_of_centred x₀ hsm hmap fun x => ?_
    obtain ⟨ψ, hψ, hx, h0, -, N, hN, hfin, hgood⟩ := hc x
    exact ⟨ψ, hψ, hx, h0, N, hN, hfin, hgood⟩

/-- **Theorem 4.2 (Characterization)**, the text's form: for a tame M-polyfold `X`, (i) `X` has a
compatible smooth manifold structure with boundary with corners (Definition 4.1) iff (ii)
`X₀ = X_∞`, `1₀¹ : X → X¹` is sc-smooth, and every `x ∈ X` lies in a tame chart `ψ` with
`ψ(x) = 0` whose `T₀O` is finite-dimensional and in good position to `C`.  The tameness of `X` is
not used (`theorem_4_2_general`); (i) implies it (`HasCornerStructure.isTame`). -/
theorem theorem_4_2 (_hP : P.IsTame) (x₀ : P.Level 1) :
    P.HasCornerStructure ↔
      (∀ x, x ∈ P.smoothSet) ∧ P.IsScSmoothMap P.shift (P.toLevelOne x₀) ∧
      ∀ x, ∃ ψ : MChart X, P.IsChart ψ ∧ x ∈ ψ.source ∧ ψ x = 0 ∧
        IsTameRetract ψ.model.E ψ.model.C ψ.model.O ∧
        ∃ N : Submodule ℝ (ψ.model.E 0), (N : Set (ψ.model.E 0)) =
          tangentSpace ψ.model.E ψ.model.C ψ.model.O 0 ∧ FiniteDimensional ℝ N ∧
          IsInGoodPosition ψ.model.E ψ.model.C N :=
  theorem_4_2_general x₀

end MPolyfold

end Polyfold
