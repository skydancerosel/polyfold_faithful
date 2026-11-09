import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_50

/-!
Round trip for V3_50 (Theorem 3.56, the step from the tangent germ property).  `A` is the type of
`Polyfold.theorem_3_6_10_of_tangentGerm`, universes instantiated at `0` (`solutionSet` is
vocabulary).

A is a statement about an arbitrary nonempty solution set with the regular `n`-dimensional
tangent germ property in an M-polyfold without boundary, for one **fixed** `n`, and it has no
Fredholm hypothesis at all.  B has the text's analytic hypotheses (tame strong bundle, `∂X = ∅`,
sc-Fredholm section, surjective linearization at every zero) and a dimension that may vary.

Glue for `A → B`:
* A is applied to an arbitrary set `M`: every `M ⊆ X` is the solution set of the section
  `y ↦ (y, 1_{M^c}(y))` of the trivial bundle `X × ℝ → X` (`A_of_set`).
* `PX.boundary = ∅` is `IsWithoutBoundary` (`isWithoutBoundary_iff`); B's `IsLinSurjAt` at a zero
  (`d_X = 0`) gives `IsGoodPositionGermTame` (`isGoodPositionGerm_of_isLinSurjAt`, as in V3_86).
  Then the project's `theorem_3_6_8_two` (Theorem 3.54 (2), not part of A) gives, at every zero
  `y`, a regular datum of dimension `d(y)` on a chart domain `U_y`, along which the dimension is
  constant; so the local piece `S ∩ U_y` has the regular `d(y)`-dimensional tangent germ property
  (shrinking the data as in the project's proof of `theorem_3_1_26_of_nearby`), and **A** makes it a
  sub-M-polyfold whose induced structure is a `d(y)`-dimensional manifold with corners.
* Gluing (`isSubMPolyfold_of_pieces`, `loc_of_pieces`): the pieces `S ∩ U_y` are open in `S`; a
  retraction for a piece restricted to `V ∩ U_y` is one for `S`; and the inclusion
  `S ∩ U_y → S` is an sc-diffeomorphism onto the open set `S ∩ U_y` (both directions are locally
  `i⁻¹ ∘ r ∘ i`, Proposition 2.21), so the corner charts of the pieces transport
  (`transportChart`) to corner charts of the induced structure of `S`.
* `d_S ≡ 0` by Lemma 2.26 (`d_S ≤ d_X = 0`), and `IsManifoldWithCornersLoc` with `d_S ≡ 0` gives
  B's atlas of charts onto open subsets of finite-dimensional spaces (`boundaryless_of_loc`, from
  V3_86).  `S = ∅` is handled with the empty atlas.

**Refresh 2026-11-02 (germ reading at HEAD).**  A (`theorem_3_6_10_of_tangentGerm`) is unchanged.
B's `IsScFredholmSectionTame` now denotes the text's germ reading of Definition 3.11 (filling and
sc⁺-section only germs); the glue lemmas `isGoodPositionGerm_of_isLinSurjAt` and
`theorem_3_6_8_two` used here are now their germ-reading forms, and the proof checks unchanged.
B ⇒ A still fails (A is about arbitrary tangent-germ sets of one fixed dimension).
-/

namespace RoundTrip.V3_50
open Polyfold Set

/-- The project's statement: `theorem_3_6_10_of_tangentGerm`, universes at `0`. -/
def A : Prop := type_of% @Polyfold.theorem_3_6_10_of_tangentGerm.{0, 0}

theorem A_holds : A := @Polyfold.theorem_3_6_10_of_tangentGerm.{0, 0}

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-! ### Every set is a solution set -/

/-- The fibre of the trivial bundle `X × ℝ → X` over `x` is `ℝ`. -/
def fibEquiv (x : X) : ↥((Prod.fst : X × ℝ → X) ⁻¹' {x}) ≃ ℝ where
  toFun p := p.1.2
  invFun r := ⟨(x, r), rfl⟩
  left_inv p := by
    obtain ⟨⟨a, b⟩, h⟩ := p
    simp only [mem_preimage, mem_singleton_iff] at h
    subst h
    rfl
  right_inv _ := rfl

/-- The fibrewise group structure of the trivial bundle. -/
@[instance_reducible] noncomputable def fibGroup : ∀ x : X, AddCommGroup ↥((Prod.fst : X × ℝ → X) ⁻¹' {x}) :=
  fun x => (fibEquiv x).addCommGroup

/-- A, applied to an arbitrary set `M` (the solution set of a section of `X × ℝ → X`). -/
theorem A_of_set (hA : A) (hX : PX.IsWithoutBoundary) {M : Set X} {n : ℕ} (hne : M.Nonempty)
    (hM : ∀ x ∈ M, ∃ d : PX.TangentGermChart M x n, d.IsRegular) :
    ∃ hsub : PX.IsSubMPolyfold M,
      haveI := PX.paracompactSpace_subtype M
      (MPolyfold.subPolyfold hsub).IsManifoldWithCorners n ∧ (MPolyfold.subPolyfold hsub).IsWithoutBoundary := by
  classical
  let _ := fibGroup (X := X)
  let f' : X → X × ℝ := fun y => (y, if y ∈ M then 0 else 1)
  have e : solutionSet (Prod.fst : X × ℝ → X) f' = M := by
    ext y
    change f' y = ((0 : ↥((Prod.fst : X × ℝ → X) ⁻¹' {y})) : X × ℝ) ↔ y ∈ M
    have h0 : ((0 : ↥((Prod.fst : X × ℝ → X) ⁻¹' {y})) : X × ℝ) = (y, 0) := rfl
    rw [h0]
    by_cases hy : y ∈ M <;> simp [f', hy]
  have h := hA (PX := PX) (P := (Prod.fst : X × ℝ → X)) hX (f := f') (n := n) (e ▸ hne) (e ▸ hM)
  have key : ∀ S : Set X, S = M → (∃ hsub : PX.IsSubMPolyfold S,
      haveI := PX.paracompactSpace_subtype S
      (MPolyfold.subPolyfold hsub).IsManifoldWithCorners n ∧
        (MPolyfold.subPolyfold hsub).IsWithoutBoundary) →
      ∃ hsub : PX.IsSubMPolyfold M,
        haveI := PX.paracompactSpace_subtype M
        (MPolyfold.subPolyfold hsub).IsManifoldWithCorners n ∧
          (MPolyfold.subPolyfold hsub).IsWithoutBoundary := by
    rintro S rfl h
    exact h
  exact key _ e h

/-! ### Locality of sc-smoothness -/

theorem isScSmoothOn_of_locally {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    {Q : MPolyfold Z} {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W]
    {R : MPolyfold W} {f : Z → W} {U : Set Z} (hU : IsOpen U)
    (h : ∀ z ∈ U, ∃ V : Set Z, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ∃ g : Z → W, Q.IsScSmoothOn R g V ∧ EqOn f g V) :
    Q.IsScSmoothOn R f U := by
  have hloc : ∀ z ∈ U, ∃ V : Set Z, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧ Q.IsScSmoothOn R f V := by
    intro z hz
    obtain ⟨V, hV, hzV, hVU, g, hg, hfg⟩ := h z hz
    exact ⟨V, hV, hzV, hVU, hg.congr hfg.symm⟩
  have hcont : ContinuousOn f U := by
    refine continuousOn_of_locally_continuousOn fun z hz => ?_
    obtain ⟨V, hV, hzV, -, hfV⟩ := hloc z hz
    exact ⟨V, hV, hzV, hfV.continuousOn.mono inter_subset_right⟩
  refine MPolyfold.IsScSmoothOn.of_exists_charts hU hcont fun z hz => ?_
  obtain ⟨V, hV, hzV, hVU, hfV⟩ := hloc z hz
  obtain ⟨φ, hφ, hzφ⟩ := Q.exists_isChart_mem_source z
  obtain ⟨ψ, hψ, hfzψ⟩ := R.exists_isChart_mem_source (f z)
  have hV₀ : IsOpen ((V ∩ φ.source) ∩ f ⁻¹' ψ.source) :=
    (hfV.continuousOn.mono inter_subset_left).isOpen_inter_preimage (hV.inter φ.isOpen_source)
      ψ.isOpen_source
  exact ⟨φ, ψ, _, hφ, hψ, hV₀, ⟨⟨hzV, hzφ⟩, hfzψ⟩, fun x hx => ⟨hVU hx.1.1, hx.1.2⟩,
    fun x hx => hx.2, hfV.smooth φ ψ hφ hψ _ hV₀ (fun x hx => ⟨hx.1.1, hx.1.2⟩) fun x hx => hx.2⟩

/-! ### An open piece `S ∩ U` of a sub-M-polyfold `S` -/

variable {S : Set X}

/-- The inclusion `S ∩ U → S` is sc-smooth for the induced structures. -/
theorem inclusion_isScSmooth (hS : PX.IsSubMPolyfold S) {U : Set X}
    (hT : PX.IsSubMPolyfold (S ∩ U)) [ParacompactSpace S] [ParacompactSpace ↥(S ∩ U)] :
    (PX.subPolyfold hT).IsScSmoothOn (PX.subPolyfold hS)
      (Set.inclusion (inter_subset_left : S ∩ U ⊆ S)) univ := by
  refine isScSmoothOn_of_locally isOpen_univ fun t _ => ?_
  set d := hS.data t.2.1
  have hVo : IsOpen (Subtype.val ⁻¹' d.V : Set ↥(S ∩ U)) := d.isOpen.preimage continuous_subtype_val
  refine ⟨Subtype.val ⁻¹' d.V, hVo, hS.mem_data_V t.2.1, subset_univ _,
    d.retractInto ⟨t.1, t.2.1⟩ ∘ Subtype.val, ?_, fun t' ht' => ?_⟩
  · exact (MPolyfold.subPolyfold_retraction_isScSmooth hS d _).comp
      ((MPolyfold.subPolyfold_inclusion_isScSmooth hT).mono hVo (subset_univ _)) fun t' ht' => ht'
  · apply Subtype.ext
    change t'.1 = (d.retractInto ⟨t.1, t.2.1⟩ t'.1).1
    rw [d.retractInto_val _ ht', d.apply_eq_self ⟨t'.2.1, ht'⟩]

open scoped Classical in
/-- The inverse of the inclusion on the open set `S ∩ U ⊆ S` (junk value `t₀` elsewhere). -/
noncomputable def toPiece {U : Set X} (t₀ : ↥(S ∩ U)) (y : S) : ↥(S ∩ U) :=
  if h : y.1 ∈ U then ⟨y.1, y.2, h⟩ else t₀

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
lemma toPiece_of_mem {U : Set X} (t₀ : ↥(S ∩ U)) {y : S} (hy : y.1 ∈ U) :
    toPiece t₀ y = ⟨y.1, y.2, hy⟩ := by
  rw [toPiece, dif_pos hy]

theorem toPiece_isScSmooth (hS : PX.IsSubMPolyfold S) {U : Set X} (hU : IsOpen U)
    (hT : PX.IsSubMPolyfold (S ∩ U)) [ParacompactSpace S] [ParacompactSpace ↥(S ∩ U)]
    (t₀ : ↥(S ∩ U)) :
    (PX.subPolyfold hS).IsScSmoothOn (PX.subPolyfold hT) (toPiece t₀)
      (Subtype.val ⁻¹' U) := by
  have hUo : IsOpen (Subtype.val ⁻¹' U : Set S) := hU.preimage continuous_subtype_val
  refine isScSmoothOn_of_locally hUo fun y hy => ?_
  set d := hT.data (⟨y.2, hy⟩ : y.1 ∈ S ∩ U)
  have hVo : IsOpen (Subtype.val ⁻¹' U ∩ Subtype.val ⁻¹' d.V : Set S) :=
    hUo.inter (d.isOpen.preimage continuous_subtype_val)
  refine ⟨Subtype.val ⁻¹' U ∩ Subtype.val ⁻¹' d.V, hVo,
    ⟨hy, hT.mem_data_V (⟨y.2, hy⟩ : y.1 ∈ S ∩ U)⟩, inter_subset_left,
    d.retractInto t₀ ∘ Subtype.val, ?_, fun y' hy' => ?_⟩
  · exact (MPolyfold.subPolyfold_retraction_isScSmooth hT d t₀).comp
      ((MPolyfold.subPolyfold_inclusion_isScSmooth hS).mono hVo (subset_univ _))
      fun y' hy' => hy'.2
  · apply Subtype.ext
    change (toPiece t₀ y').1 = (d.retractInto t₀ y'.1).1
    rw [toPiece_of_mem t₀ hy'.1, d.retractInto_val _ hy'.2,
      d.apply_eq_self ⟨⟨y'.2, hy'.1⟩, hy'.2⟩]

/-- The inclusion `S ∩ U → S` is an sc-diffeomorphism onto the open set `S ∩ U` of `S`. -/
theorem piece_diffeo (hS : PX.IsSubMPolyfold S) {U : Set X} (hU : IsOpen U)
    (hT : PX.IsSubMPolyfold (S ∩ U)) [ParacompactSpace S] [ParacompactSpace ↥(S ∩ U)]
    (t₀ : ↥(S ∩ U)) :
    (PX.subPolyfold hS).IsScDiffeoOn (PX.subPolyfold hT) (toPiece t₀)
      (Set.inclusion (inter_subset_left : S ∩ U ⊆ S)) (Subtype.val ⁻¹' U) univ :=
  ⟨toPiece_isScSmooth hS hU hT t₀, inclusion_isScSmooth hS hT, mapsTo_univ _ _,
    fun t _ => t.2.2, fun y hy => by apply Subtype.ext; rw [Set.coe_inclusion, toPiece_of_mem t₀ hy],
    fun t _ => by rw [toPiece_of_mem t₀ t.2.2]⟩

/-- `S` is a sub-M-polyfold if it is one near each of its points. -/
theorem isSubMPolyfold_of_pieces
    (h : ∀ y ∈ S, ∃ U : Set X, IsOpen U ∧ y ∈ U ∧ PX.IsSubMPolyfold (S ∩ U)) :
    PX.IsSubMPolyfold S := by
  intro y hy
  obtain ⟨U, hU, hyU, hT⟩ := h y hy
  obtain ⟨V, hV, hyV, r, hmaps, hsm, hidem, himg⟩ := hT y ⟨hy, hyU⟩
  have hr : ∀ x ∈ V, r x ∈ (S ∩ U) ∩ V := fun x hx => himg ▸ ⟨x, hx, rfl⟩
  refine ⟨V ∩ U, hV.inter hU, ⟨hyV, hyU⟩, r, fun x hx => ⟨(hr x hx.1).2, (hr x hx.1).1.2⟩,
    hsm.mono (hV.inter hU) inter_subset_left, fun x hx => hidem x hx.1, ?_⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(hr x hx.1).1.1, (hr x hx.1).2, (hr x hx.1).1.2⟩
  · rintro ⟨hzS, hzV, hzU⟩
    have : z ∈ r '' V := himg ▸ ⟨⟨hzS, hzU⟩, hzV⟩
    obtain ⟨w, hw, rfl⟩ := this
    exact ⟨r w, ⟨hmaps hw, hzU⟩, hidem w hw⟩

/-- The induced structure of `S` is a manifold with corners (of locally constant dimension) if
the induced structures of open pieces `S ∩ U` covering `S` are. -/
theorem loc_of_pieces (hS : PX.IsSubMPolyfold S) [ParacompactSpace S]
    (h : ∀ y ∈ S, ∃ (U : Set X) (_ : IsOpen U) (_ : y ∈ U) (hT : PX.IsSubMPolyfold (S ∩ U)),
      haveI := PX.paracompactSpace_subtype (S ∩ U)
      (PX.subPolyfold hT).IsManifoldWithCornersLoc) :
    (PX.subPolyfold hS).IsManifoldWithCornersLoc := by
  refine ⟨{ charts := {κ | (PX.subPolyfold hS).IsChart κ ∧
              IsRelOpenInQuadrant κ.model.E κ.model.C κ.model.O ∧ FiniteDimensional ℝ (κ.model.E 0)}
            compatible := fun φ hφ ψ hψ => MPolyfold.IsChart.compatible _ hφ.1 hψ.1
            cover := fun y => ?_ },
    (MAtlas.equiv_iff _ _).2 fun φ hφ ψ hψ => hφ.1 ψ hψ, fun φ hφ => hφ.2⟩
  obtain ⟨U, hU, hyU, hT, hloc⟩ := h y.1 y.2
  have := PX.paracompactSpace_subtype (S ∩ U)
  obtain ⟨A, hA, hcA⟩ := hloc
  let t : ↥(S ∩ U) := ⟨y.1, y.2, hyU⟩
  obtain ⟨χ, hχA, htχ⟩ := A.cover t
  have hχ := (PX.subPolyfold hT).isChart_of_mem_equiv hA hχA
  have hdiff := piece_diffeo hS hU hT t
  refine ⟨MPolyfold.transportChart hdiff χ, ⟨MPolyfold.transportChart_isChart hdiff hχ, ?_,
    (hcA χ hχA).2⟩, hyU, ?_⟩
  · change IsRelOpenInQuadrant χ.model.E χ.model.C (χ '' (univ ∩ χ.source))
    rw [univ_inter, χ.image_source]
    exact (hcA χ hχA).1
  · change toPiece t y ∈ χ.source
    rw [toPiece_of_mem t hyU]
    exact htχ

/-! ### B's hypotheses -/

variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The local pieces: at every zero `y`, a chart domain `U ∋ y` on which `S ∩ U` has the regular
tangent germ property of one dimension (Theorem 3.54 (2), `theorem_3_6_8_two`). -/
theorem local_piece {Bd : StrongBundle PX P} {f : X → Y} (hfs : IsSection P f)
    (hall : ∀ x, IsZeroAt P f x → Bd.IsGoodPositionGermTame f x) {y : X}
    (hy : y ∈ solutionSet P f) :
    ∃ (U : Set X) (_ : IsOpen U) (_ : y ∈ U) (d : ℕ), ∀ z ∈ solutionSet P f ∩ U,
      ∃ D : PX.TangentGermChart (solutionSet P f ∩ U) z d, D.IsRegular := by
  obtain ⟨d, D, -, -, hdim⟩ := theorem_3_6_8_two hfs (hall y hy) hy isOpen_univ (mem_univ y)
    fun z _ hz => hall z hz
  refine ⟨D.φ.source, D.φ.isOpen_source, D.mem_source, d, fun z hz => ?_⟩
  obtain ⟨dz, Dz, hregz, hsubz, -⟩ := theorem_3_6_8_two hfs (hall z hz.1) hz.1 D.φ.isOpen_source
    hz.2 fun w _ hw => hall w hw
  have hdz : dz = d := hdim z hz dz Dz
  subst hdz
  have himage : Dz.φ '' ((solutionSet P f ∩ D.φ.source) ∩ Dz.φ.source) =
      (fun v : Dz.N => (v : Dz.φ.model.E 0) + Dz.δ v) '' Dz.V := by
    rw [← Dz.image_eq]
    congr 1
    ext w
    constructor
    · rintro ⟨⟨hw0, -⟩, hwsrc⟩; exact ⟨hw0, hwsrc⟩
    · rintro ⟨hw0, hwsrc⟩; exact ⟨⟨hw0, hsubz hwsrc⟩, hwsrc⟩
  exact ⟨Dz.shrink _ subset_rfl Dz.φ.isOpen_source Dz.mem_source Dz.V_relOpen Dz.zero_mem_V
    subset_rfl himage, Dz.shrink_isRegular _ subset_rfl Dz.φ.isOpen_source Dz.mem_source
    Dz.V_relOpen Dz.zero_mem_V subset_rfl himage hregz.isScSmooth hregz.π_mem⟩

/-- B's conclusion for an empty set: the empty atlas. -/
theorem empty_case {S : Set X} (hS : ¬ S.Nonempty) :
    ∃ (hsub : PX.IsSubMPolyfold S) (_ : ParacompactSpace S),
      HasBoundarylessManifoldStructure (PX.subPolyfold hsub) := by
  have hsub : PX.IsSubMPolyfold S := fun a ha => absurd ⟨a, ha⟩ hS
  have hpc := PX.paracompactSpace_subtype S
  exact ⟨hsub, hpc, ⟨∅, fun φ hφ => absurd hφ (notMem_empty φ), fun y => absurd ⟨y.1, y.2⟩ hS⟩,
    (MAtlas.equiv_iff _ _).2 fun φ hφ => absurd hφ (notMem_empty φ),
    fun φ hφ => absurd hφ (notMem_empty φ)⟩

end Glue

section GlueOpen

variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {QZ : MPolyfold Z}

/-- A chart of `QZ` modelled on a relatively open subset of a partial quadrant in a
finite-dimensional space, at a point `z` with `d(z) = 0`, gives a chart of `QZ` around `z` onto an
open subset of `E₀` with the constant structure and `C = univ`. -/
theorem exists_open_chart {χ : MChart Z} (hχ : QZ.IsChart χ)
    (hU : IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O)
    (hfin : FiniteDimensional ℝ (χ.model.E 0)) {z : Z} (hz : z ∈ χ.source)
    (hd : QZ.degIndex z = 0) :
    ∃ χ' : MChart Z, QZ.IsChart χ' ∧ z ∈ χ'.source ∧
      ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V) (_ : FiniteDimensional ℝ V)
        (U : Set V) (hU : IsRelOpenInQuadrant (ScBanach.const V) Set.univ U),
        χ'.model = LocalModel.ofRelOpen hU := by
  obtain ⟨n, W, T, hT⟩ := hU.isPartialQuadrant
  obtain ⟨G, hG, hOG⟩ := hU.relOpen
  -- `d_C(χ z) = 0`: the chart is a tame retract
  have htame : IsTameRetract χ.model.E χ.model.C χ.model.O :=
    ⟨ScRetraction.id hU, image_id _, ScRetraction.id_isTame _⟩
  have hdeg : degIndexWith T (χ z) = 0 := by
    have h1 := QZ.degIndex_eq_chartDegIndex_of_isTameRetract hχ htame hz
    rw [hd, MPolyfold.chartDegIndex, degIndex_eq T hT (χ.apply_mem_C hz)] at h1
    exact h1.symm
  have hcoord : ∀ i, (T 0 (χ z)).1 i ≠ 0 := by
    simp only [degIndexWith, quadrantDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies] at hdeg
    exact hdeg
  -- the open set where all quadrant coordinates are positive
  set W' : Set (χ.model.E 0) := {v | ∀ i, 0 < (T 0 v).1 i} with hW'
  have hW'o : IsOpen W' := by
    have : W' = ⋂ i, (fun v => (T 0 v).1 i) ⁻¹' Ioi 0 := by ext v; simp [hW']
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_Ioi.preimage
      ((continuous_apply i).comp (continuous_fst.comp (T 0).continuous))
  have hW'C : W' ⊆ χ.model.C := fun v hv => by
    rw [hT]; exact fun i => (hv i).le
  have hzW' : χ z ∈ W' := by
    have hzC := χ.apply_mem_C hz
    rw [hT] at hzC
    exact fun i => lt_of_le_of_ne (hzC i) (hcoord i).symm
  -- restrict the chart
  set s : Set Z := χ.source ∩ χ ⁻¹' W' with hs
  have hss : s ⊆ χ.source := inter_subset_left
  have hso : IsOpen s := χ.continuousOn_toFun.isOpen_inter_preimage χ.isOpen_source hW'o
  have himg : χ '' s = χ.model.O ∩ W' := by
    rw [hs, image_inter_preimage, χ.image_source]
  have hopen : IsOpen (χ '' s) := by
    rw [himg, hOG, inter_assoc, inter_eq_right.2 hW'C]
    exact hG.inter hW'o
  set χ₁ := χ.restrict hss hso with hχ₁
  have hχ₁c : QZ.IsChart χ₁ := MPolyfold.IsChart.restrict QZ hχ hss hso
  -- the identity onto the constant structure with `C = univ`
  have hU₁ : IsRelOpenInQuadrant χ.model.E χ.model.C (χ '' s) :=
    ⟨hU.isPartialQuadrant, χ '' s, hopen,
      (inter_eq_left.2 ((χ.image_subset_model hss).trans χ.model.O_subset_C)).symm⟩
  have hU₂ : IsRelOpenInQuadrant (ScBanach.const (χ.model.E 0)) univ (χ '' s) :=
    ⟨isPartialQuadrant_univ _, χ '' s, hopen, (inter_univ _).symm⟩
  have d := hU₁.isScDiffeoQuadrant_toConst
  have h : IsScDiffeoQuadrant hU₁ hU₂ (id : χ.model.E 0 → (ScBanach.const (χ.model.E 0)) 0)
      (id : (ScBanach.const (χ.model.E 0)) 0 → χ.model.E 0) :=
    ⟨d.isScSmooth, d.isScSmooth_inv, d.mapsTo, d.mapsTo_inv, d.left_inv, d.right_inv⟩
  have hU₃ : IsRelOpenInQuadrant (ScBanach.const (χ.model.E 0)) univ
      ((id : χ.model.E 0 → (ScBanach.const (χ.model.E 0)) 0) '' (χ '' s)) := by
    rw [image_id]; exact hU₂
  refine ⟨χ₁.compDiffeo h subset_rfl hU₃.isScRetract, MChart.compDiffeo_isChart hχ₁c h subset_rfl _,
    ⟨hz, hzW'⟩, χ.model.E 0, inferInstance, inferInstance, hfin, _, hU₃, rfl⟩

/-- `IsManifoldWithCornersLoc` and `d ≡ 0` give B's boundaryless manifold structure. -/
theorem boundaryless_of_loc (hc : QZ.IsManifoldWithCornersLoc) (hb : QZ.IsWithoutBoundary) :
    HasBoundarylessManifoldStructure QZ := by
  obtain ⟨A, hA, hcA⟩ := hc
  let A' : MAtlas Z :=
    { charts := {χ | QZ.IsChart χ ∧ ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V)
        (_ : FiniteDimensional ℝ V) (U : Set V)
        (hU : IsRelOpenInQuadrant (ScBanach.const V) Set.univ U), χ.model = LocalModel.ofRelOpen hU}
      compatible := fun φ hφ ψ hψ => MPolyfold.IsChart.compatible QZ hφ.1 hψ.1
      cover := fun z => by
        obtain ⟨χ, hχA, hz⟩ := A.cover z
        obtain ⟨χ', hχ', hz', hrest⟩ := exists_open_chart (QZ.isChart_of_mem_equiv hA hχA)
          (hcA χ hχA).1 (hcA χ hχA).2 hz (hb z)
        exact ⟨χ', ⟨hχ', hrest⟩, hz'⟩ }
  exact ⟨A', (MAtlas.equiv_iff _ _).2 fun φ hφ ψ hψ => hφ.1 ψ hψ, fun φ hφ => hφ.2⟩

end GlueOpen

theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f _ hb hf hsurj
  have hX : PX.IsWithoutBoundary := PX.isWithoutBoundary_iff.2 hb
  have hall : ∀ x, IsZeroAt P f x → Bd.IsGoodPositionGermTame f x := fun x hx =>
    StrongBundle.isGoodPositionGerm_of_isLinSurjAt hf hx (hX x) (hsurj x hx)
  have hfs : IsSection P f := hf.isScSmooth.1
  by_cases hne : (solutionSet P f).Nonempty
  · -- every point has an open piece which is, by A, a manifold with corners
    have hpieces : ∀ y ∈ solutionSet P f, ∃ (U : Set X) (_ : IsOpen U) (_ : y ∈ U)
        (hT : PX.IsSubMPolyfold (solutionSet P f ∩ U)),
        haveI := PX.paracompactSpace_subtype (solutionSet P f ∩ U)
        (PX.subPolyfold hT).IsManifoldWithCornersLoc := by
      intro y hy
      obtain ⟨U, hU, hyU, d, hreg⟩ := local_piece hfs hall hy
      obtain ⟨hT, hman, -⟩ :=
        A_of_set (PX := PX) (M := solutionSet P f ∩ U) hA hX ⟨y, hy, hyU⟩ hreg
      have := PX.paracompactSpace_subtype (solutionSet P f ∩ U)
      exact ⟨U, hU, hyU, hT, hman.isManifoldWithCornersLoc⟩
    have hS : PX.IsSubMPolyfold (solutionSet P f) := isSubMPolyfold_of_pieces fun y hy => by
      obtain ⟨U, hU, hyU, hT, -⟩ := hpieces y hy
      exact ⟨U, hU, hyU, hT⟩
    have := PX.paracompactSpace_subtype (solutionSet P f)
    have hSb : (PX.subPolyfold hS).IsWithoutBoundary := fun y => by
      have := lemma_2_4_6 hS y
      rw [hX y.1] at this
      exact Nat.le_zero.1 this
    exact ⟨hS, inferInstance, boundaryless_of_loc (loc_of_pieces hS hpieces) hSb⟩
  · exact empty_case hne

#rt_check RoundTrip.V3_50.A_to_B [Polyfold.theorem_3_6_10_of_tangentGerm]

end RoundTrip.V3_50
