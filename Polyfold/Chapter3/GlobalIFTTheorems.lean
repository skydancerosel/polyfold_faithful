import Polyfold.Chapter3.SolutionGermRecentre
import Polyfold.Chapter3.GlobalIFT
import Polyfold.Chapter3.GlobalIFTNearbySurj

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1 and §3.6:
**the implicit function theorems assembled** — Theorem 3.54 (2), Theorems 3.19, 3.23 and Corollary
3.24, and the global Theorems 3.56 and 3.57 — from the graph description of the solution set
(`GlobalIFT.lean`), the tangent germ data at the centre (`GlobalIFTCenter.lean`), the good position
at the nearby zeros (`GlobalIFTNearbySurj.lean`) and the regularity of the solution germ away from
the centre (`SolutionGermRecentre.lean`), through Theorem 3.27 (`TangentGerm.lean`).

# The sc-Fredholm implicit function theorems

## The text, paraphrased

(Theorem 3.54) Let `f` be an sc-Fredholm section of a tame strong bundle, `f(x) = 0` and `(f, x)`
in good position.  Then there is an open neighbourhood `V` of `x` such that the solution set
`S = {y ∈ V | f(y) = 0}` has the properties: (1) at every `y ∈ S` the germ `(f, y)` is in good
position; (2) `S` is a sub-M-polyfold of `X` and the induced structure is equivalent to that of a
manifold with boundary with corners.  (Theorem 3.19, interior case) `d_X ≡ 0`, `f(x₀) = 0`,
`f'(x₀)` surjective: `f'(x₀)` is sc-Fredholm, and the local solution set is a manifold whose
dimension is the index; `f'(y)` is surjective and `ker f'(y) = T_yS` for `y ∈ S(f, U)`.
(Theorem 3.23, boundary case) `f'(x)` surjective with kernel in good position: `S(f, U)` consists
of smooth points, is a tame sub-M-polyfold with a uniquely determined structure of a manifold
with boundary with corners.  (Corollary 3.24 = Theorem 3.57) If this holds at every zero, the
solution set `S = {x | f(x) = 0}` is a sub-M-polyfold whose induced structure is tame and that of a
manifold with boundary with corners.  (Theorem 3.56) `∂X = ∅`, `f'(x)` surjective at every zero:
`S` is a manifold without boundary.

## What is formalized

* `Polyfold.MPolyfold.IsManifoldWithCornersLoc`, `Polyfold.theorem_3_27_loc`: **Theorem 3.27 with
  locally constant dimension**: the data of Definition 3.25 (2) at every point, of a dimension that
  may vary with the point, with `IsRegular`, give a sub-M-polyfold whose induced structure is tame
  and has an equivalent atlas of finite-dimensional corner charts (same proof as `theorem_3_27`).
* `Polyfold.theorem_3_54_tangentGermChart_solutionSet_wholeChart`: the data of Definition 3.25 (2) for the
  **global** solution set `solutionSet P f` at a zero in good position (the chart of
  `theorem_3_54_tangentGermChart_proj_wholeChart` restricted to `Vx`), with `π(O) ⊆ C`.
* `Polyfold.theorem_3_54_two_wholeChart`: **Theorem 3.54 (2)** under the hypothesis that every zero near
  `x₀` is in good position: regular data (`IsRegular`) of Definition 3.25 (2) for the solution set
  at `x₀`, on a chart whose source lies in the given neighbourhood, and the local constancy of the
  dimension `d = dim ker f'(x₀)` along the solution set.
* `Polyfold.theorem_3_54_wholeChart`: **Theorem 3.54 (1) and (2)** under the **added hypothesis**
  `IsGoodPositionGermFilledWholeChart` (condition (3) of the filler at the nearby zeros, `theorem_3_54_one_wholeChart`);
  (3) is `theorem_3_54_graph_wholeChart` / `theorem_3_54_graph_proj_wholeChart` and (4) is `theorem_3_54_nearby_kernel_wholeChart`.
* `Polyfold.theorem_3_23_of_nearby_wholeChart`, `Polyfold.theorem_3_23_wholeChart`: **Theorem 3.23**: an open `U ∋ x`
  such that `S(f, U) = {y ∈ U | f(y) = 0}` consists of smooth points, is a sub-M-polyfold whose
  induced structure is tame and that of a manifold with boundary with corners of dimension
  `d = dim ker f'(x)`; under "every zero near `x` is in good position", resp. under
  `IsGoodPositionGermFilledWholeChart`.
* `Polyfold.theorem_3_19_linearization_wholeChart`, `Polyfold.theorem_3_19_wholeChart`: **Theorem 3.19** (`d_X ≡ 0`):
  `f'(x₀)` is a Fredholm operator (Proposition 3.52), and the local solution set is a manifold
  without boundary (in the chart form `IsWithoutBoundary` of the induced structure, Lemma 2.26).
* `Polyfold.theorem_3_57_wholeChart`, `Polyfold.corollary_3_24_wholeChart`: **Theorem 3.57 / Corollary 3.24** with the
  text's hypotheses (`f` an sc-Fredholm section of a tame strong bundle, `(f, x)` in good position
  at every zero `x`, in a tame chart, `IsGoodPositionGermTameWholeChart`, Definitions 3.50, 3.53):
  `S = solutionSet P f` is a sub-M-polyfold, the induced structure is tame and
  that of a manifold with boundary with corners of locally constant dimension.
* `Polyfold.theorem_3_56_wholeChart`: **Theorem 3.56** (`∂X = ∅`): the same, and the induced structure is
  without boundary.
* `Polyfold.solutionSetDim`, `Polyfold.theorem_3_57_dim_wholeChart`: the decomposition `S = ⋃ₙ Sₙ` into the
  parts of dimension `n` (open and closed in `S`, pairwise disjoint), each a sub-M-polyfold with a
  tame induced structure equivalent to an `n`-dimensional manifold with boundary with corners
  (Theorem 3.27 with fixed dimension).

## What the text leaves implicit, and the choices made (the findings)

* **Theorem 3.54 (1) is used here under an added hypothesis** (Findings 100–107): the text's
  argument for the surjectivity of `f'(y)` at the nearby zeros `y` needs condition (3) of
  Definition 3.4 at `ϕ(y)` for the filler at `x₀`, which the definition imposes at `0` only
  (`IsGoodPositionGermFilledWholeChart`).  Theorem 3.54 (2), Theorems 3.19 and 3.23 therefore come here in two
  forms: with the nearby good position as an explicit hypothesis (`_of_nearby`), and under
  `IsGoodPositionGermFilledWholeChart`.  Theorem 3.54 (1) **with the text's hypotheses** was proved later
  (`theorem_3_54_one'_wholeChart`, Findings 180–189), and `theorem_3_54'_wholeChart`, `theorem_3_23'_wholeChart`, `theorem_3_19'_wholeChart`
  (`GlobalIFTNearbyOnto.lean`) state the local theorems with the text's hypotheses; moreover the
  filler condition `IsGoodPositionGermFilledWholeChart` follows from good position
  (`isGoodPositionGermFilled_of_isGoodPositionGerm_wholeChart`, `GlobalIFTIndex.lean`, Finding 174).  The
  global theorems 3.56, 3.57 and Corollary 3.24 assume good position at **every** zero, which is the
  text's hypothesis, so no hypothesis is added there.
* **"Good position" in the interior case** (Theorem 3.19, Theorem 3.56): the text identifies, for
  `∂X = ∅`, good position of `(f, x)` with the surjectivity of `f'(x)`; here the hypothesis is
  `IsGoodPositionGermWholeChart` (Definition 3.53 in the chart form), as in the boundary case.  The
  identification (in a tame chart, `d_X(x) = 0` makes the kernel condition void) and the theorems
  with the text's hypothesis "`f'(x)` surjective" are in `GlobalIFTIndex.lean`
  (`isGoodPositionGerm_iff_isLinSurjAt_wholeChart`, `theorem_3_19_of_surjective_wholeChart`,
  `theorem_3_56_of_surjective_wholeChart`; Finding 173), as are the clauses "the dimension agrees with the
  Fredholm index" (`theorem_3_19_index_wholeChart`, `theorem_3_23_index_wholeChart`, `theorem_3_54_two_index_wholeChart`; Finding
  170) and "`ker f'(y) = T_yS`" in a chart (`theorem_3_54_ker_eq_tangent_wholeChart`; Finding 172).
* **The dimension**: Theorem 3.27 (`theorem_3_27`) fixes the dimension `n`.  The dimension
  `d(x) = dim ker f'(x)` of the solution set is locally constant (`exists_isRegular_of_locally`,
  from the re-centring lemma) but need not be globally constant; so Theorem 3.57 is stated with
  `IsManifoldWithCornersLoc` (locally constant dimension, `theorem_3_27_loc`), and
  `theorem_3_57_dim_wholeChart` gives the fixed-dimension statement for each part `Sₙ`.
* **Tameness** (Definitions 3.50, 3.51 and the proof of Proposition 3.52, which ask for the germ
  data in a tame strong bundle chart): the germs are in good position in tame charts
  (`IsGoodPositionGermTameWholeChart`), and where a theorem concludes the good position of the nearby zeros
  the section has tame germ data (`IsScFredholmSectionTameWholeChart`); `TameGerms.lean`, Findings 190–199.
* **"Uniquely determined structure" and "the same as the one defined in Proposition 2.21"**
  (Theorem 3.23 (2)): the structure is the induced one of Proposition 2.21 (`subPolyfold`), and
  the charts `π ∘ ϕ` form an atlas equivalent to it (Theorem 3.27); uniqueness is not stated
  separately.
-/

open Set Filter Topology Function Module ContinuousLinearMap

set_option linter.unusedSectionVars false

noncomputable section

namespace Polyfold

/-! ### Theorem 3.27 with locally constant dimension -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **Manifold with boundary with corners of locally constant dimension**: the M-polyfold structure
has an equivalent atlas all of whose charts are modelled on relatively open subsets of partial
quadrants of finite-dimensional spaces (cf. `IsManifoldWithCorners n`, where the dimension is
`n` for every chart). -/
def IsManifoldWithCornersLoc (Q : MPolyfold X) : Prop :=
  ∃ A : MAtlas X, A.Equiv Q.atlas ∧ ∀ χ ∈ A.charts,
    IsRelOpenInQuadrant χ.model.E χ.model.C χ.model.O ∧ FiniteDimensional ℝ (χ.model.E 0)

/-- A manifold with corners of dimension `n` has locally constant dimension. -/
theorem IsManifoldWithCorners.isManifoldWithCornersLoc {Q : MPolyfold X} {n : ℕ}
    (h : Q.IsManifoldWithCorners n) : Q.IsManifoldWithCornersLoc := by
  obtain ⟨A, hA, h⟩ := h
  exact ⟨A, hA, fun χ hχ => ⟨(h χ hχ).1, (h χ hχ).2.1⟩⟩

/-- **Theorem 3.27 (1), first clause, with locally constant dimension**: if every point of `M` has
regular data of Definition 3.25 (2) of some dimension, `M` is a sub-M-polyfold
(`theorem_3_27_isSubMPolyfold`, whose proof is pointwise). -/
theorem theorem_3_27_loc_isSubMPolyfold {M : Set X}
    (hM : ∀ x ∈ M, ∃ (n : ℕ) (d : P.TangentGermChart M x n), d.IsRegular) :
    P.IsSubMPolyfold M := by
  intro a ha
  obtain ⟨n, d, hreg⟩ := hM a ha
  exact ⟨d.U₀, d.isOpen_U₀ hreg, d.mem_U₀, d.s, fun y hy => (d.s_mem hy).2, d.s_isScSmoothOn hreg,
    fun y hy => d.s_s hy, d.image_s⟩

/-- The charts `π ∘ ϕ` of all the regular data of Definition 3.25 (2), of any dimension. -/
def tangentChartsLoc (M : Set X) : Set (MChart M) :=
  {κ | ∃ (x : X) (_ : x ∈ M) (n : ℕ) (d : P.TangentGermChart M x n) (hreg : d.IsRegular) (a₀ : M),
    κ = d.chart hreg a₀}

variable {M : Set X}

/-- Every chart `π ∘ ϕ` is a chart of the induced structure (Theorem 3.27 (2), as
`theorem_3_27_isChart`). -/
theorem theorem_3_27_loc_isChart [ParacompactSpace M]
    (hM : ∀ x ∈ M, ∃ (n : ℕ) (d : P.TangentGermChart M x n), d.IsRegular) {x : X} {n : ℕ}
    (d : P.TangentGermChart M x n) (hreg : d.IsRegular) (a₀ : M) :
    (subPolyfold (theorem_3_27_loc_isSubMPolyfold P hM)).IsChart (d.chart hreg a₀) := by
  rintro _ ⟨d', φ', hφ', b₀, rfl⟩
  exact d.chart_compatible_subChart hreg a₀ d' hφ' b₀

/-- The charts `π ∘ ϕ` are pairwise compatible. -/
theorem tangentChartsLoc_compatible [ParacompactSpace M]
    (hM : ∀ x ∈ M, ∃ (n : ℕ) (d : P.TangentGermChart M x n), d.IsRegular) :
    ∀ κ ∈ tangentChartsLoc P M, ∀ κ' ∈ tangentChartsLoc P M, κ.Compatible κ' := by
  rintro _ ⟨x, hx, n, d, hreg, a₀, rfl⟩ _ ⟨x', hx', n', d', hreg', a₀', rfl⟩
  have hsub := theorem_3_27_loc_isSubMPolyfold P hM
  refine MChart.compatible_of_locally _ _ (subAtlas hsub).charts ?_ ?_ fun y _ => ?_
  · intro χ hχ
    exact theorem_3_27_loc_isChart P hM d hreg a₀ χ hχ
  · intro χ hχ
    exact (theorem_3_27_loc_isChart P hM d' hreg' a₀' χ hχ).symm
  · exact (subAtlas hsub).cover y

/-- The atlas of the charts `π ∘ ϕ`. -/
def germAtlasLoc [ParacompactSpace M]
    (hM : ∀ x ∈ M, ∃ (n : ℕ) (d : P.TangentGermChart M x n), d.IsRegular) (hne : M.Nonempty) :
    MAtlas M where
  charts := tangentChartsLoc P M
  compatible := tangentChartsLoc_compatible P hM
  cover y := by
    obtain ⟨n, d, hreg⟩ := hM y.1 y.2
    exact ⟨d.chart hreg ⟨hne.some, hne.some_mem⟩, ⟨y.1, y.2, n, d, hreg, _, rfl⟩, d.mem_U₀⟩

/-- The atlas of the charts `π ∘ ϕ` is equivalent to the induced atlas of Proposition 2.21. -/
theorem theorem_3_27_loc_atlas_equiv [ParacompactSpace M]
    (hM : ∀ x ∈ M, ∃ (n : ℕ) (d : P.TangentGermChart M x n), d.IsRegular) (hne : M.Nonempty) :
    (germAtlasLoc P hM hne).Equiv (subPolyfold (theorem_3_27_loc_isSubMPolyfold P hM)).atlas := by
  rw [MAtlas.equiv_iff]
  rintro _ ⟨x, hx, n, d, hreg, a₀, rfl⟩ χ hχ
  exact theorem_3_27_loc_isChart P hM d hreg a₀ χ hχ

/-- **Theorem 3.27 (1) with locally constant dimension**: the induced structure is tame. -/
theorem theorem_3_27_loc_isTame [ParacompactSpace M]
    (hM : ∀ x ∈ M, ∃ (n : ℕ) (d : P.TangentGermChart M x n), d.IsRegular) (hne : M.Nonempty) :
    (subPolyfold (theorem_3_27_loc_isSubMPolyfold P hM)).IsTame := by
  refine ⟨germAtlasLoc P hM hne, theorem_3_27_loc_atlas_equiv P hM hne, ?_⟩
  rintro _ ⟨x, hx, n, d, hreg, a₀, rfl⟩
  exact d.model_isTameRetract

/-- **Theorem 3.27 (1) with locally constant dimension**: the induced structure is that of a
manifold with boundary with corners (of locally constant dimension). -/
theorem theorem_3_27_loc_isManifoldWithCornersLoc [ParacompactSpace M]
    (hM : ∀ x ∈ M, ∃ (n : ℕ) (d : P.TangentGermChart M x n), d.IsRegular) (hne : M.Nonempty) :
    (subPolyfold (theorem_3_27_loc_isSubMPolyfold P hM)).IsManifoldWithCornersLoc := by
  refine ⟨germAtlasLoc P hM hne, theorem_3_27_loc_atlas_equiv P hM hne, ?_⟩
  rintro _ ⟨x, hx, n, d, hreg, a₀, rfl⟩
  exact ⟨(d.chart_isCorner hreg a₀).1, (d.chart_isCorner hreg a₀).2.1⟩

end MPolyfold

/-- **Theorem 3.27 with locally constant dimension** (under the regularity conditions `IsRegular`
at every point): a subset `M` of an M-polyfold `X` with the tangent germ property at every point,
of a dimension that may depend on the point, is a sub-M-polyfold of `X` whose induced structure is
tame and equivalent to the structure of a manifold with boundary with corners of locally constant
dimension; the charts are the maps `y ↦ π ∘ ϕ(y)`. -/
theorem theorem_3_27_loc {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) {M : Set X} (hne : M.Nonempty)
    (hM : ∀ x ∈ M, ∃ (n : ℕ) (d : P.TangentGermChart M x n), d.IsRegular) :
    ∃ hsub : P.IsSubMPolyfold M,
      haveI := P.paracompactSpace_subtype M
      (MPolyfold.subPolyfold hsub).IsTame ∧ (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
      ∀ x (hx : x ∈ M) (n : ℕ) (d : P.TangentGermChart M x n) (hreg : d.IsRegular) (a₀ : M),
        (MPolyfold.subPolyfold hsub).IsChart (d.chart hreg a₀) ∧
          (⟨x, hx⟩ : M) ∈ (d.chart hreg a₀).source := by
  have := P.paracompactSpace_subtype M
  exact ⟨MPolyfold.theorem_3_27_loc_isSubMPolyfold P hM, MPolyfold.theorem_3_27_loc_isTame P hM hne,
    MPolyfold.theorem_3_27_loc_isManifoldWithCornersLoc P hM hne, fun x hx n d hreg a₀ =>
      ⟨MPolyfold.theorem_3_27_loc_isChart P hM d hreg a₀, d.mem_chart_source hreg a₀ hx⟩⟩

/-! ### The solution set of an sc-Fredholm section -/

section SolutionSet

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **The data of Definition 3.25 (2) for the global solution set** `solutionSet P f` at a zero
`x₀` in good position, with `π(O) ⊆ C`: the chart `ψ ∘ ϕ` of `theorem_3_54_tangentGermChart_proj_wholeChart`
restricted to the neighbourhood `Vx` of Theorem 3.54 (3) (`TangentGermChart.shrink`), so that the
solution set in the chart domain is the solution set in `Vx`. -/
theorem theorem_3_54_tangentGermChart_solutionSet_wholeChart (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x₀ d,
      ∀ z ∈ D.φ.model.O, (D.π z : D.φ.model.E 0) ∈ D.φ.model.C := by
  obtain ⟨Vx, d, hVxo, hx₀Vx, D, hπ⟩ := theorem_3_54_tangentGermChart_proj_wholeChart hf hg hx₀
  have hs : D.φ.source ∩ Vx ⊆ D.φ.source := inter_subset_left
  have hso : IsOpen (D.φ.source ∩ Vx) := D.φ.isOpen_source.inter hVxo
  have hxs : x₀ ∈ D.φ.source ∩ Vx := ⟨D.mem_source, hx₀Vx⟩
  have himage : D.φ '' (solutionSet P f ∩ (D.φ.source ∩ Vx)) =
      (fun v : D.N => (v : D.φ.model.E 0) + D.δ v) '' D.V := by
    rw [← D.image_eq]
    congr 1
    ext y
    constructor
    · rintro ⟨hyS, hysrc, hyVx⟩; exact ⟨⟨hyVx, hyS⟩, hysrc⟩
    · rintro ⟨⟨hyVx, hyS⟩, hysrc⟩; exact ⟨hyS, hysrc, hyVx⟩
  refine ⟨d, D.shrink (solutionSet P f) hs hso hxs D.V_relOpen D.zero_mem_V subset_rfl himage, ?_⟩
  intro z hz
  rw [D.shrink_π]
  exact hπ z (D.φ.image_subset_model hs hz)

/-- **Theorem 3.54 (2), under the hypothesis that every zero near `x₀` is in good position**
(the conclusion of Theorem 3.54 (1), which is proved under an added hypothesis in
`theorem_3_54_one_wholeChart`).  Let `f` be a section of a strong bundle, `f(x₀) = 0`, `(f, x₀)` in good
position in a tame chart (`IsGoodPositionGermTameWholeChart`), and let every zero in an open `Vx₀ ∋ x₀` be in
good position in a tame chart.  Then the solution set `S = solutionSet P f` has at `x₀` regular data of Definition
3.25 (2) (`TangentGermChart` with `IsRegular`: `σ` sc-smooth in the set sense and `π(O) ⊆ C`) of
dimension `d = dim ker D(h + t)(0)`, on a chart whose source lies in `Vx₀`; and the dimension is
locally constant along `S`: every datum of Definition 3.25 (2) for `S` at a point of the chart
domain has dimension `d`.  By `theorem_3_54_tangentGermChart_solutionSet_wholeChart` at `x₀` and at the
nearby zeros, and the re-centring (`exists_isRegular_of_locally`). -/
theorem theorem_3_54_two_wholeChart (hf : IsSection P f) {x₀ : X} (hg : B.IsGoodPositionGermTameWholeChart f x₀)
    (hx₀ : IsZeroAt P f x₀)
    {Vx₀ : Set X} (hVx₀ : IsOpen Vx₀) (hx₀V : x₀ ∈ Vx₀)
    (hall : ∀ y ∈ Vx₀, IsZeroAt P f y → B.IsGoodPositionGermTameWholeChart f y) :
    ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x₀ d, D.IsRegular ∧ D.φ.source ⊆ Vx₀ ∧
      ∀ y ∈ solutionSet P f ∩ D.φ.source,
        ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d := by
  obtain ⟨d, D, hπ⟩ := theorem_3_54_tangentGermChart_solutionSet_wholeChart hf hg hx₀
  have hM : ∀ y ∈ solutionSet P f ∩ Vx₀,
      ∃ n' : ℕ, Nonempty (PX.TangentGermChart (solutionSet P f) y n') := fun y hy => by
    obtain ⟨d', D', -⟩ :=
      theorem_3_54_tangentGermChart_solutionSet_wholeChart hf (hall y hy.2 hy.1) hy.1
    exact ⟨d', ⟨D'⟩⟩
  obtain ⟨D', hreg, hsub, hdim⟩ := D.exists_isRegular_of_locally hπ hVx₀ hx₀V hM
  exact ⟨d, D', hreg, hsub, hdim⟩

/-- **Theorem 3.54 (1) and (2)**, under the **added hypothesis** `IsGoodPositionGermFilledWholeChart`
(the filler at `x₀` satisfies condition (3) of Definition 3.4 at the nearby zeros; Findings
100–107).  For an sc-Fredholm section `f` with tame germ data (`IsScFredholmSectionTameWholeChart`),
`f(x₀) = 0` and `(f, x₀)` in good position in a tame chart with such a filler, there is an open
`Vx ∋ x₀` with: (1) at every zero `y ∈ Vx` the germ `(f, y)` is in good position in a tame chart
(`theorem_3_54_one_wholeChart`); (2) the
solution set has at `x₀` regular data of Definition 3.25 (2) of dimension `d`, on a chart with
source in `Vx`, with the dimension locally constant (`theorem_3_54_two_wholeChart`); so Theorem 3.27 applies
to the local solution set (`theorem_3_23_wholeChart`).  Part (3), the graph description, is
`theorem_3_54_graph_proj_wholeChart`; part (4), the kernel at the nearby zeros, is `theorem_3_54_nearby_kernel_wholeChart`. -/
theorem theorem_3_54_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) {x₀ : X}
    (hg : B.IsGoodPositionGermFilledWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ Vx : Set X, IsOpen Vx ∧ x₀ ∈ Vx ∧ (∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGermTameWholeChart f y) ∧
      ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x₀ d, D.IsRegular ∧ D.φ.source ⊆ Vx ∧
        ∀ y ∈ solutionSet P f ∩ D.φ.source,
          ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d := by
  obtain ⟨Vx, hVxo, hx₀Vx, hall⟩ := theorem_3_54_one_wholeChart hf hg hx₀
  exact ⟨Vx, hVxo, hx₀Vx, hall,
    theorem_3_54_two_wholeChart hf.isScSmooth.1 hg.isGoodPositionGermTame hx₀ hVxo hx₀Vx hall⟩

/-- **Theorem 3.23 (implicit function theorem, boundary case), under the hypothesis that every
zero near `x` is in good position.**  Let `f` be an sc-Fredholm section of a strong bundle,
`f(x) = 0`, `(f, x)` in good position in a tame chart (`f'(x)` surjective with kernel in good
position, Definition 3.53, `IsGoodPositionGermTameWholeChart`), and every zero in an open `Vx₀ ∋ x` in good
position in a tame chart.  Then there is
an open neighbourhood `U ⊆ Vx₀` of `x` such that the local solution set
`S(f, U) = {y ∈ U | f(y) = 0}` consists of smooth points, is a sub-M-polyfold of `X`, and the
induced M-polyfold structure (Proposition 2.21) is tame and equivalent to the structure of a
`d`-dimensional manifold with boundary with corners, `d = dim ker f'(x)`.  (`U` is the source of
the regular chart of `theorem_3_54_two_wholeChart`; at every `y ∈ S(f, U)` the regular chart of
`theorem_3_54_two_wholeChart` at `y` has dimension `d` by the local constancy, and Theorem 3.27 applies.) -/
theorem theorem_3_23_of_nearby_wholeChart (hf : B.IsScFredholmSectionWholeChart f) {x : X} (hx : IsZeroAt P f x)
    (hg : B.IsGoodPositionGermTameWholeChart f x)
    {Vx₀ : Set X} (hVx₀ : IsOpen Vx₀) (hxV : x ∈ Vx₀)
    (hall : ∀ y ∈ Vx₀, IsZeroAt P f y → B.IsGoodPositionGermTameWholeChart f y) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ Vx₀ ∧ (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ d : ℕ, ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d := by
  obtain ⟨d, D, hreg, hsub, hdim⟩ := theorem_3_54_two_wholeChart hf.isScSmooth.1 hg hx hVx₀ hxV hall
  set U := D.φ.source with hU
  set S' := {y ∈ U | IsZeroAt P f y} with hS'
  -- every point of `S(f, U)` has regular data of Definition 3.25 (2) for `S(f, U)` of dimension `d`
  have hS'reg : ∀ y ∈ S', ∃ d' : PX.TangentGermChart S' y d, d'.IsRegular := by
    intro y hy
    obtain ⟨dy, Dy, hregy, hsuby, -⟩ := theorem_3_54_two_wholeChart hf.isScSmooth.1 (hall y (hsub hy.1) hy.2)
      hy.2 (D.φ.isOpen_source.inter hVx₀) ⟨hy.1, hsub hy.1⟩ fun z hz hz0 => hall z hz.2 hz0
    have hdy : dy = d := hdim y ⟨hy.2, hy.1⟩ dy Dy
    subst hdy
    have himage : Dy.φ '' (S' ∩ Dy.φ.source) =
        (fun v : Dy.N => (v : Dy.φ.model.E 0) + Dy.δ v) '' Dy.V := by
      rw [← Dy.image_eq]
      congr 1
      ext z
      constructor
      · rintro ⟨⟨-, hz0⟩, hzsrc⟩; exact ⟨hz0, hzsrc⟩
      · rintro ⟨hz0, hzsrc⟩; exact ⟨⟨(hsuby hzsrc).1, hz0⟩, hzsrc⟩
    exact ⟨Dy.shrink S' subset_rfl Dy.φ.isOpen_source Dy.mem_source Dy.V_relOpen Dy.zero_mem_V
      subset_rfl himage, Dy.shrink_isRegular S' subset_rfl Dy.φ.isOpen_source Dy.mem_source
      Dy.V_relOpen Dy.zero_mem_V subset_rfl himage hregy.isScSmooth hregy.π_mem⟩
  have hne : S'.Nonempty := ⟨x, D.mem_source, hx⟩
  obtain ⟨hsubM, htameS, hman, -⟩ := theorem_3_27 PX hne hS'reg
  exact ⟨U, D.φ.isOpen_source, D.mem_source, hsub, fun y _ hy => hf.mem_smoothSet_of_isZeroAt hy,
    d, hsubM, htameS, hman⟩

/-- **Theorem 3.23 (implicit function theorem, boundary case)**, under the **added hypothesis**
`IsGoodPositionGermFilledWholeChart` (through Theorem 3.54 (1), `theorem_3_54_one_wholeChart`): an open neighbourhood
`U` of the zero `x` such that every zero in `U` is in good position (in a tame chart), `S(f, U)`
consists of smooth points, is a sub-M-polyfold of `X`, and the induced structure is tame and that of a
`d`-dimensional manifold with boundary with corners. -/
theorem theorem_3_23_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) {x : X} (hx : IsZeroAt P f x)
    (hg : B.IsGoodPositionGermFilledWholeChart f x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermTameWholeChart f y) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ d : ℕ, ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d := by
  obtain ⟨Vx, hVxo, hxVx, hall⟩ := theorem_3_54_one_wholeChart hf hg hx
  obtain ⟨U, hUo, hxU, hUV, hsm, d, hsub, h1, h2⟩ :=
    theorem_3_23_of_nearby_wholeChart hf.toIsScFredholmSectionWholeChart hx hg.isGoodPositionGermTame hVxo hxVx hall
  exact ⟨U, hUo, hxU, fun y hy hy0 => hall y (hUV hy) hy0, hsm, d, hsub, h1, h2⟩

/-- **Theorem 3.19, the first clause**: for an sc-Fredholm section and a zero `x₀` in good position
(in the interior case the text's hypothesis is "`f'(x₀)` surjective"), the linearization is a
Fredholm operator — Proposition 3.52 in the chart at `x₀` (`proposition_3_52_wholeChart`).  The index clause
here is that of `proposition_3_52_wholeChart` ("`n − N` for some natural numbers", vacuous); the index of the
conjugation is `theorem_3_19_linearization_index_wholeChart` (`GlobalIFTIndex.lean`), and the text's
"`f'(x₀)` is sc-Fredholm" (all levels) is `theorem_3_19_linearization_sc_wholeChart`
(`FredholmGermLinearizationSc.lean`). -/
theorem theorem_3_19_linearization_wholeChart (hf : B.IsScFredholmSectionWholeChart f) {x₀ : X}
    (hx₀ : IsZeroAt P f x₀) (hg : B.IsGoodPositionGermWholeChart f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
      (_ : IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g)
      (h1 : ∀ x, StrongRetr.ρCLM c.isRetraction h0
          (scDeriv c.U g 0 (scDeriv c.U (StrongRetr.r c.R) 0 x)) =
        scDeriv c.U g 0 (scDeriv c.U (StrongRetr.r c.R) 0 x)) (n N : ℕ),
      IsFredholm (scDeriv c.U g 0) ∧ fredholmIndex (scDeriv c.U g 0) = n - N ∧
      IsFredholm (fillerRestrict (scDeriv c.U (StrongRetr.r c.R) 0)
        (StrongRetr.ρCLM c.isRetraction h0) (scDeriv c.U g 0) h1) ∧
      fredholmIndex (fillerRestrict (scDeriv c.U (StrongRetr.r c.R) 0)
        (StrongRetr.ρCLM c.isRetraction h0) (scDeriv c.U g 0) h1) = n - N :=
  proposition_3_52_wholeChart hf.isScSmooth.1 hg.isScFredholmGerm hx₀

/-- **Theorem 3.19 (implicit function theorem, interior case)**, under the **added hypothesis**
`IsGoodPositionGermFilledWholeChart` at `x₀` (Finding 100): for an M-polyfold `X` with `d_X ≡ 0`, an
sc-Fredholm section `f` with tame germ data (`IsScFredholmSectionTameWholeChart`) and a zero `x₀` with
`(f, x₀)` in good position (in the interior case, the text: `f'(x₀)` surjective), there is an open
neighbourhood `U` of `x₀` such that every zero in `U` is in good position in a tame chart (in
particular `f'(y)` is surjective), and the local solution set `S(f, U)` is a sub-M-polyfold of `X` whose induced
structure is that of a `d`-dimensional manifold without boundary (`IsWithoutBoundary`, Lemma
2.26).  The first clause of the text, "`f'(x₀)` is sc-Fredholm", is `theorem_3_19_linearization_wholeChart`;
"the dimension agrees with the Fredholm index" is `theorem_3_19_index_wholeChart` and "`ker f'(y) = T_yS(f, U)`"
is `theorem_3_54_ker_eq_tangent_wholeChart` (`GlobalIFTIndex.lean`); with the text's hypotheses (no
`IsGoodPositionGermFilledWholeChart`) it is `theorem_3_19'_wholeChart`. -/
theorem theorem_3_19_wholeChart (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSectionTameWholeChart f) {x₀ : X}
    (hx₀ : IsZeroAt P f x₀) (hg : B.IsGoodPositionGermFilledWholeChart f x₀) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermTameWholeChart f y) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ d : ℕ, ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d ∧
          (MPolyfold.subPolyfold hsub).IsWithoutBoundary := by
  obtain ⟨U, hUo, hxU, hgood, hsm, d, hsub, -, h2⟩ := theorem_3_23_wholeChart hf hx₀ hg
  have := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
  refine ⟨U, hUo, hxU, hgood, hsm, d, hsub, h2, fun y => ?_⟩
  have := lemma_2_26 hsub y
  rw [hX y.1] at this
  exact Nat.le_zero.1 this

/-- **Theorem 3.57 (global implicit function theorem, boundary case) with the text's
hypotheses.**  Let `f` be an sc-Fredholm section of a strong bundle `P : Y → X` such that at every
zero `x` the germ `(f, x)` is in good position in a tame chart (Definitions 3.50, 3.53,
`IsGoodPositionGermTameWholeChart`: `f'(x)` surjective with `ker f'(x)` in good position to `C_xX`).  Then the
solution set `S = solutionSet P f` (assumed nonempty) is a sub-M-polyfold of `X`, its induced
M-polyfold structure is tame and equivalent to the structure of a manifold with boundary with
corners of locally constant dimension; at every `x ∈ S` the data of Definition 3.25 (2) are
regular, of a dimension `d(x)` which is constant on a neighbourhood of `x` in `S`.
(`theorem_3_54_two_wholeChart` at every zero, `theorem_3_27_loc`.)  No hypothesis is added. -/
theorem theorem_3_57_wholeChart (hf : B.IsScFredholmSectionWholeChart f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTameWholeChart f x) (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        ∀ x ∈ solutionSet P f, ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x d,
          D.IsRegular ∧ ∀ y ∈ solutionSet P f ∩ D.φ.source,
            ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d := by
  have hloc : ∀ x ∈ solutionSet P f, ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x d,
      D.IsRegular ∧ ∀ y ∈ solutionSet P f ∩ D.φ.source,
        ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d := fun x hx => by
    obtain ⟨d, D, hreg, -, hdim⟩ := theorem_3_54_two_wholeChart hf.isScSmooth.1 (hall x hx) hx
      isOpen_univ (mem_univ x) fun y _ hy => hall y hy
    exact ⟨d, D, hreg, hdim⟩
  have hS : ∀ x ∈ solutionSet P f, ∃ (n : ℕ) (d : PX.TangentGermChart (solutionSet P f) x n),
      d.IsRegular := fun x hx => by
    obtain ⟨d, D, hreg, -⟩ := hloc x hx
    exact ⟨d, D, hreg⟩
  obtain ⟨hsub, h1, h2, -⟩ := theorem_3_27_loc PX hne hS
  exact ⟨hsub, h1, h2, hloc⟩

/-- **Corollary 3.24** (= Theorem 3.57): if at every zero `x` the linearization `f'(x)` is
surjective with kernel in good position, the solution set is a sub-M-polyfold with tame induced
structure, equivalent to a manifold with boundary with corners (of locally constant dimension). -/
theorem corollary_3_24_wholeChart (hf : B.IsScFredholmSectionWholeChart f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTameWholeChart f x) (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc := by
  obtain ⟨hsub, h1, h2, -⟩ := theorem_3_57_wholeChart hf hall hne
  exact ⟨hsub, h1, h2⟩

/-- **Theorem 3.56 (global implicit function theorem, `∂X = ∅`) with the text's hypotheses**:
for an M-polyfold without boundary and an sc-Fredholm section `f` with `(f, x)` in good position
at every zero (the text: `f'(x)` surjective), the solution set is a sub-M-polyfold of `X` whose
induced structure is that of a manifold without boundary, of locally constant dimension
(Theorem 3.57 and Lemma 2.26: `d_S ≤ d_X = 0`). -/
theorem theorem_3_56_wholeChart (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSectionWholeChart f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTameWholeChart f x) (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        (MPolyfold.subPolyfold hsub).IsWithoutBoundary := by
  have := PX.paracompactSpace_subtype (solutionSet P f)
  obtain ⟨hsub, -, h2, -⟩ := theorem_3_57_wholeChart hf hall hne
  refine ⟨hsub, h2, fun y => ?_⟩
  have := lemma_2_26 hsub y
  rw [hX y.1] at this
  exact Nat.le_zero.1 this

/-! ### The parts of the solution set of a fixed dimension -/

variable (PX P f) in
/-- The part `Sₙ` of the solution set at whose points the data of Definition 3.25 (2) have
dimension `n`. -/
def solutionSetDim (n : ℕ) : Set X :=
  {x ∈ solutionSet P f | Nonempty (PX.TangentGermChart (solutionSet P f) x n)}

variable (PX P f) in
/-- The open set `Uₙ`: the union of the sources of the regular charts of dimension `n` along which
the dimension is constant. -/
def solutionSetDimOpen (n : ℕ) : Set X :=
  ⋃ (x : X) (_ : x ∈ solutionSet P f) (D : PX.TangentGermChart (solutionSet P f) x n)
    (_ : D.IsRegular)
    (_ : ∀ y ∈ solutionSet P f ∩ D.φ.source,
      ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = n), D.φ.source

lemma isOpen_solutionSetDimOpen (n : ℕ) : IsOpen (solutionSetDimOpen PX P f n) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun D => isOpen_iUnion fun _ =>
    isOpen_iUnion fun _ => D.φ.isOpen_source

/-- **Theorem 3.57 with the dimension**: under the hypotheses of Theorem 3.57, the solution set
`S` is the disjoint union of the parts `Sₙ` of dimension `n`, each open and closed in `S`, and
each nonempty `Sₙ` is a sub-M-polyfold of `X` whose induced structure is tame and equivalent to
that of an `n`-dimensional manifold with boundary with corners (Theorem 3.27 with fixed dimension,
`theorem_3_27`).  The local constancy of the dimension is `theorem_3_54_two_wholeChart`. -/
theorem theorem_3_57_dim_wholeChart (hf : B.IsScFredholmSectionWholeChart f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTameWholeChart f x) :
    solutionSet P f = ⋃ n, solutionSetDim PX P f n ∧
    (∀ n m, n ≠ m → Disjoint (solutionSetDim PX P f n) (solutionSetDim PX P f m)) ∧
    (∀ n, solutionSetDim PX P f n = solutionSet P f ∩ solutionSetDimOpen PX P f n) ∧
    (∀ n, ∃ F : Set X, IsClosed F ∧ solutionSetDim PX P f n = solutionSet P f ∩ F) ∧
    ∀ n, (solutionSetDim PX P f n).Nonempty →
      ∃ hsub : PX.IsSubMPolyfold (solutionSetDim PX P f n),
        haveI := PX.paracompactSpace_subtype (solutionSetDim PX P f n)
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners n := by
  classical
  have hloc : ∀ x ∈ solutionSet P f, ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x d,
      D.IsRegular ∧ ∀ y ∈ solutionSet P f ∩ D.φ.source,
        ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d := fun x hx => by
    obtain ⟨d, D, hreg, -, hdim⟩ := theorem_3_54_two_wholeChart hf.isScSmooth.1 (hall x hx) hx
      isOpen_univ (mem_univ x) fun y _ hy => hall y hy
    exact ⟨d, D, hreg, hdim⟩
  -- the dimension of any datum at a point is the dimension of the regular datum there
  have hdimAt : ∀ x ∈ solutionSet P f, ∀ (n m : ℕ), PX.TangentGermChart (solutionSet P f) x n →
      PX.TangentGermChart (solutionSet P f) x m → n = m := by
    intro x hx n m Dn Dm
    obtain ⟨d, D, -, hdim⟩ := hloc x hx
    rw [hdim x ⟨hx, D.mem_source⟩ n Dn, hdim x ⟨hx, D.mem_source⟩ m Dm]
  -- `Sₙ = S ∩ Uₙ`
  have hopen : ∀ n, solutionSetDim PX P f n = solutionSet P f ∩ solutionSetDimOpen PX P f n := by
    intro n
    ext x
    constructor
    · rintro ⟨hx, ⟨Dn⟩⟩
      obtain ⟨d, D, hreg, hdim⟩ := hloc x hx
      have hd : d = n := (hdimAt x hx d n D Dn).symm ▸ rfl
      subst hd
      refine ⟨hx, ?_⟩
      simp only [solutionSetDimOpen, mem_iUnion]
      exact ⟨x, hx, D, hreg, hdim, D.mem_source⟩
    · rintro ⟨hx, hU⟩
      simp only [solutionSetDimOpen, mem_iUnion] at hU
      obtain ⟨x', hx', D, -, hdim, hxsrc⟩ := hU
      obtain ⟨d, Dx, -, -⟩ := hloc x hx
      have hd : d = n := hdim x ⟨hx, hxsrc⟩ d Dx
      subst hd
      exact ⟨hx, ⟨Dx⟩⟩
  have hdisj : ∀ n m, n ≠ m → Disjoint (solutionSetDim PX P f n) (solutionSetDim PX P f m) := by
    intro n m hnm
    rw [disjoint_left]
    rintro x ⟨hx, ⟨Dn⟩⟩ ⟨-, ⟨Dm⟩⟩
    exact hnm (hdimAt x hx n m Dn Dm)
  have hcover : solutionSet P f = ⋃ n, solutionSetDim PX P f n := by
    ext x
    simp only [mem_iUnion]
    constructor
    · intro hx
      obtain ⟨d, D, -, -⟩ := hloc x hx
      exact ⟨d, hx, ⟨D⟩⟩
    · rintro ⟨n, hx, -⟩
      exact hx
  refine ⟨hcover, hdisj, hopen, fun n => ?_, fun n hne => ?_⟩
  · -- closed in `S`: the complement of the other open parts
    refine ⟨(⋃ m ∈ ({n}ᶜ : Set ℕ), solutionSetDimOpen PX P f m)ᶜ,
      (isOpen_biUnion fun m _ => isOpen_solutionSetDimOpen m).isClosed_compl, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_iUnion, mem_singleton_iff, not_exists, exists_prop]
    constructor
    · intro hx
      refine ⟨hx.1, fun m hm => ?_⟩
      obtain ⟨hm, hxU⟩ := hm
      have hxm : x ∈ solutionSetDim PX P f m := by rw [hopen m]; exact ⟨hx.1, hxU⟩
      exact hm ((hdimAt x hx.1 n m hx.2.some hxm.2.some).symm)
    · rintro ⟨hx, hnot⟩
      obtain ⟨d, D, -, -⟩ := hloc x hx
      by_cases hd : d = n
      · subst hd; exact ⟨hx, ⟨D⟩⟩
      · exfalso
        have hxd : x ∈ solutionSetDim PX P f d := ⟨hx, ⟨D⟩⟩
        rw [hopen d] at hxd
        exact hnot d ⟨hd, hxd.2⟩
  · -- each nonempty `Sₙ` is a sub-M-polyfold with the structure of an `n`-manifold
    have hSn : ∀ x ∈ solutionSetDim PX P f n,
        ∃ d : PX.TangentGermChart (solutionSetDim PX P f n) x n, d.IsRegular := by
      rintro x ⟨hx, ⟨Dn⟩⟩
      obtain ⟨d, D, hreg, hdim⟩ := hloc x hx
      have hd : d = n := (hdimAt x hx d n D Dn).symm ▸ rfl
      subst hd
      have himage : D.φ '' (solutionSetDim PX P f d ∩ D.φ.source) =
          (fun v : D.N => (v : D.φ.model.E 0) + D.δ v) '' D.V := by
        rw [← D.image_eq]
        congr 1
        ext z
        constructor
        · rintro ⟨⟨hz, -⟩, hzsrc⟩; exact ⟨hz, hzsrc⟩
        · rintro ⟨hz, hzsrc⟩
          obtain ⟨dz, Dz, -, -⟩ := hloc z hz
          have hdz : dz = d := hdim z ⟨hz, hzsrc⟩ dz Dz
          subst hdz
          exact ⟨⟨hz, ⟨Dz⟩⟩, hzsrc⟩
      exact ⟨D.shrink (solutionSetDim PX P f d) subset_rfl D.φ.isOpen_source D.mem_source
        D.V_relOpen D.zero_mem_V subset_rfl himage,
        D.shrink_isRegular _ subset_rfl D.φ.isOpen_source D.mem_source D.V_relOpen D.zero_mem_V
          subset_rfl himage hreg.isScSmooth hreg.π_mem⟩
    obtain ⟨hsub, h1, h2, -⟩ := theorem_3_27 PX hne hSn
    exact ⟨hsub, h1, h2⟩

end SolutionSet

end Polyfold
