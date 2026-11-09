import Polyfold.Chapter3.GlobalIFTTheorems
import Polyfold.Chapter3.GlobalIFTCenterG
import Polyfold.Chapter3.GlobalIFTNearbySurjG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.3 and §3.6,
**the implicit function theorems (Theorems 3.1.22, 3.1.26, 3.6.8, 3.6.10, 3.6.11 (preprint 3.19, 3.23, 3.54, 3.56, 3.57), Corollary 3.1.27 (preprint 3.24)) for
sc-Fredholm sections in the text's germ reading of Definition 3.1.11 (preprint 3.11)** (phase 2).

# The main theorems, germ reading

## What is formalized

The germ forms of the theorems of `GlobalIFTTheorems.lean`, with the hypotheses in the germ
reading (`IsScFredholmSection`, `IsScFredholmSectionTame`, `IsGoodPositionGerm`,
`IsGoodPositionGermTame`, `IsGoodPositionGermFilled`) and the **same conclusions**:

* `Polyfold.theorem_3_6_8_tangentGermChart_solutionSet`, `Polyfold.theorem_3_6_8_two`:
  Theorem 3.6.8 (preprint 3.54) (2) for the global solution set, and under the hypothesis that every zero near `x₀`
  is in good position;
* `Polyfold.theorem_3_6_8`: **Theorem 3.6.8 (preprint 3.54) (1) and (2)** under `IsGoodPositionGermFilled`;
* `Polyfold.theorem_3_1_26_of_nearby`, `Polyfold.theorem_3_1_26`: **Theorem 3.1.26 (preprint 3.23)**;
* `Polyfold.theorem_3_1_22_linearization`, `Polyfold.theorem_3_1_22`: **Theorem 3.1.22 (preprint 3.19)**
  (the linearization is Fredholm, Proposition 3.52 for germs; the local solution set);
* `Polyfold.theorem_3_6_11`, `Polyfold.corollary_3_1_27`, `Polyfold.theorem_3_6_10`,
  `Polyfold.theorem_3_6_11_dim`: **Theorems 3.6.11, 3.6.10 (preprint 3.57, 3.56) and Corollary 3.1.27 (preprint 3.24)** with the text's
  hypotheses (good position in a tame chart at every zero, in the germ reading).

## What the text leaves implicit, and the choices made (the findings)

The proofs are those of `GlobalIFTTheorems.lean` with `theorem_3_6_8_tangentGermChart_proj`
and `theorem_3_6_8_one` in place of the old theorems: the assembly (re-centring,
`exists_isRegular_of_locally`, Theorem 3.2.3 (preprint 3.27)) takes place on the `E'`-side and in `X`, and never
touches the filling or the sc⁺-section.  The added hypothesis `IsGoodPositionGermFilled` of
Theorems 3.6.8 (preprint 3.54) (1), 3.23 and 3.19 is the germ form of `IsGoodPositionGermFilledWholeChart` (Findings
100–107); with the text's hypotheses, Theorem 3.6.8 (preprint 3.54) (1) is `theorem_3_6_8_one'`, and the main
theorems without the added hypothesis are `theorem_3_6_8'`, `theorem_3_1_26'`,
`theorem_3_1_22'` (`GlobalIFTNearbyOntoG.lean`).
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

section SolutionSet

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **The data of Definition 3.2.1 (preprint 3.25) (2) for the global solution set at a zero in good position,
germ reading** (phase 2; the germ form of `theorem_3_6_8_tangentGermChart_solutionSet_wholeChart`). -/
theorem theorem_3_6_8_tangentGermChart_solutionSet (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x₀ d,
      ∀ z ∈ D.φ.model.O, (D.π z : D.φ.model.E 0) ∈ D.φ.model.C := by
  obtain ⟨Vx, d, hVxo, hx₀Vx, D, hπ⟩ := theorem_3_6_8_tangentGermChart_proj hf hg hx₀
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

/-- **Theorem 3.6.8 (preprint 3.54) (2), under the hypothesis that every zero near `x₀` is in good position, germ
reading** (phase 2; the germ form of `theorem_3_6_8_two_wholeChart`): regular data of Definition 3.2.1 (preprint 3.25) (2)
for `S = solutionSet P f` at `x₀`, of dimension `d`, on a chart with source in `Vx₀`, with the
dimension locally constant along `S`. -/
theorem theorem_3_6_8_two (hf : IsSection P f) {x₀ : X} (hg : B.IsGoodPositionGermTame f x₀)
    (hx₀ : IsZeroAt P f x₀)
    {Vx₀ : Set X} (hVx₀ : IsOpen Vx₀) (hx₀V : x₀ ∈ Vx₀)
    (hall : ∀ y ∈ Vx₀, IsZeroAt P f y → B.IsGoodPositionGermTame f y) :
    ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x₀ d, D.IsRegular ∧ D.φ.source ⊆ Vx₀ ∧
      ∀ y ∈ solutionSet P f ∩ D.φ.source,
        ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d := by
  obtain ⟨d, D, hπ⟩ := theorem_3_6_8_tangentGermChart_solutionSet hf hg hx₀
  have hM : ∀ y ∈ solutionSet P f ∩ Vx₀,
      ∃ n' : ℕ, Nonempty (PX.TangentGermChart (solutionSet P f) y n') := fun y hy => by
    obtain ⟨d', D', -⟩ :=
      theorem_3_6_8_tangentGermChart_solutionSet hf (hall y hy.2 hy.1) hy.1
    exact ⟨d', ⟨D'⟩⟩
  obtain ⟨D', hreg, hsub, hdim⟩ := D.exists_isRegular_of_locally hπ hVx₀ hx₀V hM
  exact ⟨d, D', hreg, hsub, hdim⟩

/-- **Theorem 3.6.8 (preprint 3.54) (1) and (2), germ reading** (phase 2; the germ form of `theorem_3_6_8_wholeChart`), under
the **added hypothesis** `IsGoodPositionGermFilled`.  For an sc-Fredholm section `f` with tame
germ data in the germ reading (`IsScFredholmSectionTame`), `f(x₀) = 0` and `(f, x₀)` in good
position in a tame chart with a filling germ satisfying condition (3) at the nearby zeros, there
is an open `Vx ∋ x₀` with: (1) at every zero `y ∈ Vx` the germ `(f, y)` is in good position in a
tame chart (`theorem_3_6_8_one`); (2) the solution set has at `x₀` regular data of Definition
3.25 (2) of dimension `d`, on a chart with source in `Vx`, with the dimension locally constant
(`theorem_3_6_8_two`).  Part (3) is `theorem_3_6_8_graph_proj`, part (4)
`theorem_3_6_8_nearby_kernel`. -/
theorem theorem_3_6_8 (hf : B.IsScFredholmSectionTame f) {x₀ : X}
    (hg : B.IsGoodPositionGermFilled f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ Vx : Set X, IsOpen Vx ∧ x₀ ∈ Vx ∧
      (∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGermTame f y) ∧
      ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x₀ d, D.IsRegular ∧ D.φ.source ⊆ Vx ∧
        ∀ y ∈ solutionSet P f ∩ D.φ.source,
          ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d := by
  obtain ⟨Vx, hVxo, hx₀Vx, hall⟩ := theorem_3_6_8_one hf hg hx₀
  exact ⟨Vx, hVxo, hx₀Vx, hall,
    theorem_3_6_8_two hf.isScSmooth.1 hg.isGoodPositionGermTame hx₀ hVxo hx₀Vx hall⟩

/-- **Theorem 3.1.26 (preprint 3.23) (implicit function theorem, boundary case), under the hypothesis that every
zero near `x` is in good position, germ reading** (phase 2; the germ form of
`theorem_3_1_26_of_nearby_wholeChart`): an open `U ⊆ Vx₀` around the zero `x` such that the local solution set
`S(f, U)` consists of smooth points, is a sub-M-polyfold of `X`, and the induced structure is
tame and that of a `d`-dimensional manifold with boundary with corners. -/
theorem theorem_3_1_26_of_nearby (hf : B.IsScFredholmSection f) {x : X} (hx : IsZeroAt P f x)
    (hg : B.IsGoodPositionGermTame f x)
    {Vx₀ : Set X} (hVx₀ : IsOpen Vx₀) (hxV : x ∈ Vx₀)
    (hall : ∀ y ∈ Vx₀, IsZeroAt P f y → B.IsGoodPositionGermTame f y) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ Vx₀ ∧ (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ d : ℕ, ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d := by
  obtain ⟨d, D, hreg, hsub, hdim⟩ := theorem_3_6_8_two hf.isScSmooth.1 hg hx hVx₀ hxV hall
  set U := D.φ.source with hU
  set S' := {y ∈ U | IsZeroAt P f y} with hS'
  -- every point of `S(f, U)` has regular data of Definition 3.2.1 (preprint 3.25) (2) for `S(f, U)` of dimension `d`
  have hS'reg : ∀ y ∈ S', ∃ d' : PX.TangentGermChart S' y d, d'.IsRegular := by
    intro y hy
    obtain ⟨dy, Dy, hregy, hsuby, -⟩ := theorem_3_6_8_two hf.isScSmooth.1
      (hall y (hsub hy.1) hy.2) hy.2 (D.φ.isOpen_source.inter hVx₀) ⟨hy.1, hsub hy.1⟩
      fun z hz hz0 => hall z hz.2 hz0
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
  obtain ⟨hsubM, htameS, hman, -⟩ := theorem_3_2_3_of_isRegular PX hne hS'reg
  exact ⟨U, D.φ.isOpen_source, D.mem_source, hsub, fun y _ hy => hf.mem_smoothSet_of_isZeroAt hy,
    d, hsubM, htameS, hman⟩

/-- **Theorem 3.1.26 (preprint 3.23) (implicit function theorem, boundary case), germ reading** (phase 2; the germ
form of `theorem_3_1_26_wholeChart`), under the **added hypothesis** `IsGoodPositionGermFilled` (through
Theorem 3.6.8 (preprint 3.54) (1), `theorem_3_6_8_one`): an open neighbourhood `U` of the zero `x` such that
every zero in `U` is in good position (in a tame chart, germ reading), `S(f, U)` consists of
smooth points, is a sub-M-polyfold of `X`, and the induced structure is tame and that of a
`d`-dimensional manifold with boundary with corners. -/
theorem theorem_3_1_26 (hf : B.IsScFredholmSectionTame f) {x : X} (hx : IsZeroAt P f x)
    (hg : B.IsGoodPositionGermFilled f x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermTame f y) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ d : ℕ, ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d := by
  obtain ⟨Vx, hVxo, hxVx, hall⟩ := theorem_3_6_8_one hf hg hx
  obtain ⟨U, hUo, hxU, hUV, hsm, d, hsub, h1, h2⟩ :=
    theorem_3_1_26_of_nearby hf.toIsScFredholmSection hx hg.isGoodPositionGermTame hVxo hxVx
      hall
  exact ⟨U, hUo, hxU, fun y hy hy0 => hall y (hUV hy) hy0, hsm, d, hsub, h1, h2⟩

/-- **Theorem 3.1.22 (preprint 3.19), the first clause, germ reading** (phase 2; the germ form of
`theorem_3_1_22_linearization_wholeChart`): for an sc-Fredholm section in the germ reading and a zero `x₀` in
good position, the linearization `Tf(x₀) = Dg(0)|_{T₀O}` in the chart of Definition 3.1.11 (preprint 3.11) is a
Fredholm operator of index `n − N`, and so is `Dg(0)` — Proposition 3.6.5 (preprint 3.52) for germs
(`proposition_3_6_5_preprint`), with `Dg(0)` the value at `0` of a derivative family of the filling
germ `g`. -/
theorem theorem_3_1_22_linearization (hf : B.IsScFredholmSection f) {x₀ : X}
    (hx₀ : IsZeroAt P f x₀) (hg : B.IsGoodPositionGerm f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
      (_ : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
      (G : ScNbhdGerm c.φ.model.E c.φ.model.C) (_ : G.U 0 ⊆ c.U) (_ : IsScSmoothGerm G g)
      (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0) (_ : IsSc1GermWith G g Dg)
      (h1 : ∀ x, StrongRetr.ρCLM c.isRetraction h0 (Dg 0 (scDeriv c.U (StrongRetr.r c.R) 0 x)) =
        Dg 0 (scDeriv c.U (StrongRetr.r c.R) 0 x)) (n N : ℕ),
      ContinuousLinearMap.IsFredholm (Dg 0) ∧ fredholmIndex (Dg 0) = n - N ∧
      ContinuousLinearMap.IsFredholm (fillerRestrict (scDeriv c.U (StrongRetr.r c.R) 0)
        (StrongRetr.ρCLM c.isRetraction h0) (Dg 0) h1) ∧
      fredholmIndex (fillerRestrict (scDeriv c.U (StrongRetr.r c.R) 0)
        (StrongRetr.ρCLM c.isRetraction h0) (Dg 0) h1) = n - N :=
  proposition_3_6_5_preprint hf.isScSmooth.1 hg.isScFredholmGerm hx₀

/-- **Theorem 3.1.22 (preprint 3.19) (implicit function theorem, interior case), germ reading** (phase 2; the germ
form of `theorem_3_1_22_wholeChart`), under the **added hypothesis** `IsGoodPositionGermFilled` at `x₀`: for an
M-polyfold `X` with `d_X ≡ 0`, an sc-Fredholm section `f` with tame germ data in the germ reading
and a zero `x₀` with `(f, x₀)` in good position, there is an open neighbourhood `U` of `x₀` such
that every zero in `U` is in good position in a tame chart, and the local solution set `S(f, U)`
is a sub-M-polyfold of `X` whose induced structure is that of a `d`-dimensional manifold without
boundary.  The first clause, "`f'(x₀)` is sc-Fredholm", is `theorem_3_1_22_linearization`. -/
theorem theorem_3_1_22 (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSectionTame f) {x₀ : X}
    (hx₀ : IsZeroAt P f x₀) (hg : B.IsGoodPositionGermFilled f x₀) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermTame f y) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ d : ℕ, ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d ∧
          (MPolyfold.subPolyfold hsub).IsWithoutBoundary := by
  obtain ⟨U, hUo, hxU, hgood, hsm, d, hsub, -, h2⟩ := theorem_3_1_26 hf hx₀ hg
  have := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
  refine ⟨U, hUo, hxU, hgood, hsm, d, hsub, h2, fun y => ?_⟩
  have := lemma_2_4_6 hsub y
  rw [hX y.1] at this
  exact Nat.le_zero.1 this

/-- **Theorem 3.6.11 (preprint 3.57) (global implicit function theorem, boundary case) with the text's hypotheses,
germ reading** (phase 2; the germ form of `theorem_3_6_11_wholeChart`).  Let `f` be an sc-Fredholm section in
the germ reading such that at every zero `x` the germ `(f, x)` is in good position in a tame chart
(`IsGoodPositionGermTame`).  Then the solution set `S` (assumed nonempty) is a sub-M-polyfold of
`X`, its induced M-polyfold structure is tame and equivalent to the structure of a manifold with
boundary with corners of locally constant dimension; at every `x ∈ S` the data of Definition 3.2.1 (preprint 3.25)
(2) are regular, of a dimension `d(x)` constant on a neighbourhood of `x` in `S`.  No hypothesis
is added. -/
theorem theorem_3_6_11 (hf : B.IsScFredholmSection f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTame f x)
    (hne : (solutionSet P f).Nonempty) :
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
    obtain ⟨d, D, hreg, -, hdim⟩ := theorem_3_6_8_two hf.isScSmooth.1 (hall x hx) hx
      isOpen_univ (mem_univ x) fun y _ hy => hall y hy
    exact ⟨d, D, hreg, hdim⟩
  have hS : ∀ x ∈ solutionSet P f, ∃ (n : ℕ) (d : PX.TangentGermChart (solutionSet P f) x n),
      d.IsRegular := fun x hx => by
    obtain ⟨d, D, hreg, -⟩ := hloc x hx
    exact ⟨d, D, hreg⟩
  obtain ⟨hsub, h1, h2, -⟩ := theorem_3_2_3_loc_of_isRegular PX hne hS
  exact ⟨hsub, h1, h2, hloc⟩

/-- **Corollary 3.1.27 (preprint 3.24) (= Theorem 3.57), germ reading** (phase 2; the germ form of
`corollary_3_1_27_wholeChart`). -/
theorem corollary_3_1_27 (hf : B.IsScFredholmSection f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTame f x)
    (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc := by
  obtain ⟨hsub, h1, h2, -⟩ := theorem_3_6_11 hf hall hne
  exact ⟨hsub, h1, h2⟩

/-- **Theorem 3.6.10 (preprint 3.56) (global implicit function theorem, `∂X = ∅`) with the text's hypotheses, germ
reading** (phase 2; the germ form of `theorem_3_6_10_wholeChart`): for an M-polyfold without boundary and an
sc-Fredholm section `f` in the germ reading with `(f, x)` in good position at every zero, the
solution set is a sub-M-polyfold of `X` whose induced structure is that of a manifold without
boundary, of locally constant dimension. -/
theorem theorem_3_6_10 (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSection f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTame f x)
    (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        (MPolyfold.subPolyfold hsub).IsWithoutBoundary := by
  have := PX.paracompactSpace_subtype (solutionSet P f)
  obtain ⟨hsub, -, h2, -⟩ := theorem_3_6_11 hf hall hne
  refine ⟨hsub, h2, fun y => ?_⟩
  have := lemma_2_4_6 hsub y
  rw [hX y.1] at this
  exact Nat.le_zero.1 this

/-- **Theorem 3.6.11 (preprint 3.57) with the dimension, germ reading** (phase 2; the germ form of
`theorem_3_6_11_dim_wholeChart`): under the hypotheses of `theorem_3_6_11`, the solution set `S` is the
disjoint union of the parts `Sₙ` of dimension `n`, each open and closed in `S`, and each nonempty
`Sₙ` is a sub-M-polyfold of `X` whose induced structure is tame and equivalent to that of an
`n`-dimensional manifold with boundary with corners. -/
theorem theorem_3_6_11_dim (hf : B.IsScFredholmSection f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTame f x) :
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
    obtain ⟨d, D, hreg, -, hdim⟩ := theorem_3_6_8_two hf.isScSmooth.1 (hall x hx) hx
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
    obtain ⟨hsub, h1, h2, -⟩ := theorem_3_2_3_of_isRegular PX hne hSn
    exact ⟨hsub, h1, h2⟩

end SolutionSet

end Polyfold
