import Polyfold.Chapter9.MathlibManifoldBridge
import Polyfold.Chapter3.MainTheorems2021
import Polyfold.Chapter3.TangentGermProjecting
import Polyfold.Chapter6.SolutionOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941;
2014 preprint): the solution sets of the implicit function theorems and of the perturbation
theorems **in Mathlib's language**, with their dimension the Fredholm index: **Theorem 3.1.22**
(p. 100; preprint 3.19), **Theorem 3.2.3** (p. 106; preprint 3.27), **Theorem 3.6.8** (p. 136;
preprint 3.54), **Theorem 3.6.10** (p. 140; preprint 3.56), **Theorem 5.3.10** (p. 220; preprint
5.18), **Theorem 6.6.18** (p. 274; preprint 6.41) and **Lemma 6.6.5** (p. 265; preprint 6.30).
Numbers and pages are the 2021 text's, older numbers in parentheses.

# Solution sets as Mathlib manifolds, with the dimension the index

## The text, paraphrased

(Theorem 3.1.22) If `f'(x₀)` is onto at a zero `x₀`, the solution set near `x₀` is a smooth
manifold of dimension `ind(f, x₀)`.  (Theorem 3.6.8) At a zero in good position, the solution set
near it is a manifold with boundary with corners of dimension `ind(f, x₀)`, `T_yS = ker f'(y)`.
(Theorems 3.6.10, 5.3.10, 6.6.18) The solution set of a section transversal to the zero section
(resp. in general position at every zero) is a smooth (compact) manifold (with boundary with
corners) of dimension the Fredholm index; (Lemma 6.6.5) the solution set near a family of zeros is
a manifold with boundary with corners.

## What is formalized

The dimension of the solution set is read off `T_yS = ker f'(y)` (`exists_tangentSpace_eq_linKer`,
Theorem 3.6.8) and `dim ker f'(y) = ind f'(y)` for onto `f'(y)`
(`StrongBundle.IsSurjLinOfIndex.finrank_linKer`):

* `StrongBundle.isSurjLinOfIndex_of_isLinSurjAt`: "`f'(y)` onto" (`IsLinSurjAt`) and
  "`ind f'(y) = d`" (`IsLinOfIndex`) give `IsSurjLinOfIndex f y d`
  (`finrank_ker_eq_fredholmIndex_of_surjective`).
* `StrongBundle.hasDimAt_solutionSet_inter`: at a zero `y` in good position with `f'(y)` onto of
  index `d`, the solution set has dimension `d` at `y` (Remark 9.1.1's `HasDimAt`).
* **Theorem 3.6.8 with the dimension** (`theorem_3_6_8_isSubmanifoldOfDim`): near a zero in good
  position the solution set is an `n`-dimensional submanifold, `n = ind f'(y)`, with no global
  hypothesis on the index (`theorem_3_54_index_locally_constant`).
* **The dimension of the solution set is the index**: `StrongBundle.isSubmanifoldOfDim_solutionSet`
  (good position at every zero, `IsSurjLinOfIndex` at every zero) and its forms with the index
  hypothesis `IsLinOfIndex f y d` at every zero:
  `StrongBundle.SolutionSetInGeneralPosition.isSubmanifoldOfDim` (Theorem 5.3.10's conclusion,
  Theorem 6.6.18), `StrongBundle.isSubmanifoldOfDim_solutionSet_of_isTransversal` (the transversal
  case of Theorems 3.1.22 and 3.6.10, `d_X ≡ 0`).
* **The Mathlib statements**: `StrongBundle.SolutionSetInGeneralPosition.isManifold` (the solution
  set is compact and `IsManifold (modelWithCornersEuclideanQuadrant d) ∞ S`),
  `theorem_6_6_18_isManifold` (Theorem 6.6.18, first sentence: a proper sc-Fredholm section in
  general position at every zero over a tame `X`), `theorem_5_3_10_isManifold` (Theorem 5.3.10:
  the solution sets of the perturbed sections `f + s_λ`, `λ ∉ CV`), `theorem_3_6_10_isManifold`
  (Theorems 3.1.22 / 3.6.10: `IsManifold (𝓡 d) ∞ S`), `theorem_3_1_26_isManifold` (Theorem
  3.1.26: the local statement at a zero in good position, `IsManifold
  (modelWithCornersEuclideanQuadrant d) ∞ S(f, U)`).
* **Theorem 3.2.3 under the tangent germ property alone** (`theorem_3_2_3_isManifold_2021`,
  `theorem_3_2_3_isManifold_2021def`): the Mathlib form of `theorem_3_2_3_isManifold` with the
  text's hypothesis `HasTangentGermProperty` (`TangentGermProjecting.lean`) in place of the
  regular data.
* `IsSubmanifoldOfDim.eq_of_hasCornerStructureOfDim`: the dimension of the corner charts of the
  induced structure is the dimension of the submanifold (`tangentSpace_relOpen`), so the `d` of
  `IsManifoldWithCorners d` in Theorems 3.1.26 and 3.2.3 is the one of `IsSubmanifoldOfDim`.

## What the text leaves implicit, and the choices made

* "Of dimension the Fredholm index": the index is `IsLinOfIndex f y d`, "`f'(y)` is Fredholm of
  index `d` in every strong bundle chart around `y`".  It is locally constant along the zero set
  (Proposition 6.2.2, `theorem_3_54_index_locally_constant`); the global statements take one index
  `d` for all zeros (the text's "the index of `f`"), the local one (`theorem_3_6_8_isSubmanifoldOfDim`)
  takes none.
* Gaps G.62 and G.67 (Lemma 6.6.5, Theorem 6.6.18) asked for the solution set as a manifold with
  boundary with corners; that part is closed here.  The submersion `π : S → [0, 1]` with its fibres,
  the smooth bundle `L` over `[0, 1]` (G.62), and the orientation of `S` as a Mathlib manifold
  (G.67) are not treated.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function Module Manifold MeasureTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-! ### The index at a zero with `f'(y)` onto -/

/-- **"`f'(y)` onto of index `d`" from "`f'(y)` onto" and "`ind f'(y) = d`"**: for an onto
Fredholm operator `dim ker = ind` (`finrank_ker_eq_fredholmIndex_of_surjective`), and `f'(y)` is
onto in every chart (`IsLinSurjAt.linAt_surjective`). -/
theorem StrongBundle.isSurjLinOfIndex_of_isLinSurjAt (hf : B.IsScSmoothSection f) {y : X}
    (hy0 : IsZeroAt P f y) (hs : B.IsLinSurjAt f y) {d : ℕ} (hi : B.IsLinOfIndex f y d) :
    B.IsSurjLinOfIndex f y d := by
  intro c hc hyV z hz hzU L hL
  obtain ⟨hF, hind⟩ := hi c hc hyV z hz hzU L hL
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [hz, c.r_image]; exact c.φ.mapsTo_model y hyV
  have hsurj : Surjective L := by
    rintro ⟨k, hk⟩
    have hkK : (c.φ y, k) ∈ c.K := by
      have := (mem_rangeS_ρCLM_iff c.isRetraction hzO hzU).1 hk
      rwa [hz] at this
    obtain ⟨x, hx⟩ := hs.linAt_surjective hf hy0 hc hyV hz k hkK
    exact ⟨x, Subtype.ext ((hL x).trans hx)⟩
  refine ⟨hsurj, hF, hind, ?_⟩
  have := finrank_ker_eq_fredholmIndex_of_surjective hF hsurj
  rw [hind] at this
  exact_mod_cast this

/-! ### The dimension of the solution set at a zero -/

/-- **The solution set has dimension `ind f'(y)` at a zero `y` in good position** (Theorem 3.6.8
(3), "`T_yS = ker f'(y)`", with Remark 9.1.1's `HasDimAt`): there is an open `V ∋ y` on which every
zero is in good position, `S ∩ V` is a smooth submanifold (Definition 4.2.1) and, if `f'(y)` is onto
of index `d`, `dim T_y(S ∩ V) = d`.  *Proof*: in the tame chart `c` of the germ data at `y`
(`c.φ(y) = 0`), `T₀(φ(G ∩ S ∩ V)) = ker Lin(0)` (`exists_tangentSpace_eq_linKer`) has dimension `d`
(`IsSurjLinOfIndex.finrank_linKer`). -/
theorem StrongBundle.hasDimAt_solutionSet_inter (hft : B.IsScFredholmSectionTame f) {y : X}
    (hgp : B.IsGoodPositionGermTame f y) (hy0 : IsZeroAt P f y) {d : ℕ}
    (hidx : B.IsSurjLinOfIndex f y d) :
    ∃ V : Set X, IsOpen V ∧ y ∈ V ∧
      (∀ y' ∈ V, IsZeroAt P f y' → B.IsGoodPositionGermTame f y') ∧
      PX.IsSmoothSubmanifold (solutionSet P f ∩ V) ∧ PX.HasDimAt (solutionSet P f ∩ V) y d := by
  obtain ⟨V, hVo, hyV, hall, hid⟩ := exists_tangentSpace_eq_linKer hft hgp hy0
  have hA := StrongBundle.isSmoothSubmanifold_solutionSet_inter hft.isScSmooth.1 hVo hall
  refine ⟨V, hVo, hyV, hall, hA, ?_⟩
  have hys := hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hy0
  obtain ⟨-, c, hct, hyc, hφ0, -⟩ := hft.germTame y hys
  have hc : B.IsChart c := hct.isChart
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ y := by rw [map_zero, hφ0]
  have hyA : y ∈ solutionSet P f ∩ V := ⟨hy0, hyV⟩
  set dd := hA.data hyA
  have hG := dd.toSubData.isOpen_shrink c.φ
  have hGc := dd.toSubData.shrink_subset_source c.φ
  have hyG := dd.toSubData.mem_shrink c.φ hyA (hA.mem_data_V hyA) hyc
  have hQ := dd.toSubData.isScRetract_image c.φ c.isChart
  refine MPolyfold.hasDimAt_of_finrank hA hyA c.isChart hG hGc hQ hyG hz ?_
  rw [hid y hyV hy0 c hc hyc _ hG hGc hyG hQ 0 hz, Submodule.span_eq]
  exact (hidx.finrank_linKer hft.isScSmooth hy0 hc hyc 0 hz).2

/-- **Theorem 3.6.8 (2), (3) with the dimension** (p. 136; preprint 3.54): near a zero `x₀` in good
position the solution set is an `n`-dimensional smooth submanifold (`IsSubmanifoldOfDim`), where
`n = ind f'(y) = dim ker f'(y)` at every zero `y` nearby (no hypothesis on the index: it is locally
constant, `theorem_3_54_index_locally_constant`). -/
theorem theorem_3_6_8_isSubmanifoldOfDim (hft : B.IsScFredholmSectionTame f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (V : Set X) (d : ℕ), IsOpen V ∧ x₀ ∈ V ∧
      (∀ y ∈ V, IsZeroAt P f y → B.IsGoodPositionGermTame f y ∧ B.IsSurjLinOfIndex f y d) ∧
      PX.IsSubmanifoldOfDim (solutionSet P f ∩ V) d := by
  obtain ⟨Vx, d, hVxo, hx₀Vx, hind⟩ := theorem_3_54_index_locally_constant hft hg hx₀
  obtain ⟨V₁, hV₁o, hx₀V₁, hall, -⟩ := exists_tangentSpace_eq_linKer hft hg hx₀
  set V := V₁ ∩ Vx with hVdef
  have hVo : IsOpen V := hV₁o.inter hVxo
  have hall' : ∀ y ∈ V, IsZeroAt P f y → B.IsGoodPositionGermTame f y ∧ B.IsSurjLinOfIndex f y d :=
    fun y hy hy0 => ⟨hall y hy.1 hy0, hind y hy.2 hy0⟩
  have hA : PX.IsSmoothSubmanifold (solutionSet P f ∩ V) :=
    StrongBundle.isSmoothSubmanifold_solutionSet_inter hft.isScSmooth.1 hVo
      fun y hy hy0 => (hall' y hy hy0).1
  refine ⟨V, d, hVo, ⟨hx₀V₁, hx₀Vx⟩, hall', hA, fun y hy => ?_⟩
  obtain ⟨V', hV'o, hyV', -, hA', hdim⟩ :=
    StrongBundle.hasDimAt_solutionSet_inter hft (hall' y hy.2 hy.1).1 hy.1 (hall' y hy.2 hy.1).2
  have h1 : PX.HasDimAt ((solutionSet P f ∩ V') ∩ V) y d :=
    (MPolyfold.hasDimAt_inter_isOpen_iff hA' hVo hy.2).2 hdim
  rw [inter_right_comm] at h1
  exact (MPolyfold.hasDimAt_inter_isOpen_iff hA hV'o hyV').1 h1

/-! ### The dimension of the solution set is the index -/

/-- **The solution set is an `d`-dimensional submanifold** if every zero is in good position and
`f'(y)` is onto of index `d` at every zero. -/
theorem StrongBundle.isSubmanifoldOfDim_solutionSet (hft : B.IsScFredholmSectionTame f)
    (hall : ∀ y, IsZeroAt P f y → B.IsGoodPositionGermTame f y) {d : ℕ}
    (hidx : ∀ y, IsZeroAt P f y → B.IsSurjLinOfIndex f y d) :
    PX.IsSubmanifoldOfDim (solutionSet P f) d := by
  have hS : PX.IsSmoothSubmanifold (solutionSet P f) := by
    have := StrongBundle.isSmoothSubmanifold_solutionSet_inter hft.isScSmooth.1 isOpen_univ
      fun y _ hy0 => hall y hy0
    rwa [inter_univ] at this
  refine ⟨hS, fun y hy => ?_⟩
  obtain ⟨V, hVo, hyV, -, -, hdim⟩ :=
    StrongBundle.hasDimAt_solutionSet_inter hft (hall y hy) hy (hidx y hy)
  exact (MPolyfold.hasDimAt_inter_isOpen_iff hS hVo hyV).1 hdim

/-- Good position of the solution set (Definition 4.2.5) from general position
(`SolutionSetInGeneralPosition`, Lemma 4.2.8). -/
theorem StrongBundle.SolutionSetInGeneralPosition.isGoodPositionAt (hX : PX.IsTame)
    (h : B.SolutionSetInGeneralPosition f) :
    ∀ y ∈ solutionSet P f, PX.IsGoodPositionAt (solutionSet P f) y := by
  obtain ⟨-, -, -, hS, hgpS, -⟩ := h
  exact fun y hy => (hgpS y hy).isGoodPositionAt hX hS

/-- **The solution set of a section in general position is a `d`-dimensional submanifold**, `d`
the index (Theorem 5.3.10's conclusion `SolutionSetInGeneralPosition`, Theorem 6.6.18): general
position gives good position of the germ (`IsGeneralPositionGerm.isGoodPositionGermTame`) and
`f'(y)` onto. -/
theorem StrongBundle.SolutionSetInGeneralPosition.isSubmanifoldOfDim
    (hft : B.IsScFredholmSectionTame f) (h : B.SolutionSetInGeneralPosition f) {d : ℕ}
    (hidx : ∀ y, IsZeroAt P f y → B.IsLinOfIndex f y d) :
    PX.IsSubmanifoldOfDim (solutionSet P f) d :=
  StrongBundle.isSubmanifoldOfDim_solutionSet hft
    (fun y hy => (h.2.1 y hy).isGoodPositionGermTame hft hy)
    fun y hy => StrongBundle.isSurjLinOfIndex_of_isLinSurjAt hft.isScSmooth hy (h.1 y hy) (hidx y hy)

/-- **The transversal case over an M-polyfold without boundary** (Theorems 3.1.22, 3.6.10): the
solution set of a section with `f'(y)` onto of index `d` at every zero is a `d`-dimensional
submanifold (`isGoodPositionGerm_of_isLinSurjAt`: without boundary, good position is
surjectivity). -/
theorem StrongBundle.isSubmanifoldOfDim_solutionSet_of_isTransversal (hX : PX.IsWithoutBoundary)
    (hft : B.IsScFredholmSectionTame f) (htr : B.IsTransversal f) {d : ℕ}
    (hidx : ∀ y, IsZeroAt P f y → B.IsLinOfIndex f y d) :
    PX.IsSubmanifoldOfDim (solutionSet P f) d :=
  StrongBundle.isSubmanifoldOfDim_solutionSet hft
    (fun y hy => StrongBundle.isGoodPositionGerm_of_isLinSurjAt hft hy (hX y) (htr y hy))
    fun y hy => StrongBundle.isSurjLinOfIndex_of_isLinSurjAt hft.isScSmooth hy (htr y hy) (hidx y hy)

/-! ### The Mathlib statements -/

/-- **Theorem 5.3.10's conclusion in Mathlib's language** (gaps G.62, G.67, the manifold part): for
a tame `X` and an sc-Fredholm section `f` (tame germ data) of index `d` whose solution set is in
general position (`SolutionSetInGeneralPosition`), `S = f⁻¹(0)` is compact and, with the charted
space of its induced corner structure, a smooth manifold with boundary and corners of dimension
`d`: `IsManifold (modelWithCornersEuclideanQuadrant d) ∞ S`. -/
theorem StrongBundle.SolutionSetInGeneralPosition.isManifold (hX : PX.IsTame)
    (hft : B.IsScFredholmSectionTame f) (h : B.SolutionSetInGeneralPosition f) {d : ℕ}
    (hidx : ∀ y, IsZeroAt P f y → B.IsLinOfIndex f y d) :
    IsCompact (solutionSet P f) ∧
      letI := PX.paracompactSpace_subtype (solutionSet P f)
      letI := (MPolyfold.subPolyfold (h.isSubmanifoldOfDim hft hidx).1.isSubMPolyfold).cornerChartedSpace
        ((h.isSubmanifoldOfDim hft hidx).hasCornerStructureOfDim_of_tame hX (h.isGoodPositionAt hX))
      IsManifold (modelWithCornersEuclideanQuadrant d) ∞ (solutionSet P f) :=
  letI := PX.paracompactSpace_subtype (solutionSet P f)
  ⟨h.2.2.1, MPolyfold.isManifold_cornerChartedSpace _⟩

/-- **Theorem 6.6.18, first sentence, in Mathlib's language** (p. 274; preprint 6.41; gap G.67,
the manifold part): over a tame `X`, for a proper sc-Fredholm section `f` (tame germ data) of index
`d` with `(f, x)` in general position at every zero, the solution set `S = f⁻¹(0)` is a smooth
compact manifold with boundary and corners of dimension `d` (`theorem_6_41_solutionSet`). -/
theorem theorem_6_6_18_isManifold (hX : PX.IsTame) (hft : B.IsScFredholmSectionTame f)
    (hP : B.IsProper f) (hgp : ∀ x, IsZeroAt P f x → B.IsGeneralPositionGerm f x) {d : ℕ}
    (hidx : ∀ y, IsZeroAt P f y → B.IsLinOfIndex f y d) :
    IsCompact (solutionSet P f) ∧
      letI := PX.paracompactSpace_subtype (solutionSet P f)
      letI := (MPolyfold.subPolyfold
        ((theorem_6_41_solutionSet hX hft hP hgp).isSubmanifoldOfDim hft hidx).1.isSubMPolyfold).cornerChartedSpace
        (((theorem_6_41_solutionSet hX hft hP hgp).isSubmanifoldOfDim hft hidx).hasCornerStructureOfDim_of_tame
          hX ((theorem_6_41_solutionSet hX hft hP hgp).isGoodPositionAt hX))
      IsManifold (modelWithCornersEuclideanQuadrant d) ∞ (solutionSet P f) :=
  (theorem_6_41_solutionSet hX hft hP hgp).isManifold hX hft hidx

/-- **Theorem 5.3.10 in Mathlib's language** (p. 220; preprint 5.18): under the hypotheses of
`theorem_5_18` (tame `X` with sc-smooth bump functions, `f` sc-Fredholm with tame germ data and
compact solution set, an auxiliary norm `N`), for every `λ` with `‖λ‖ < δ`, `λ ∉ CV`, the perturbed
section `f + s_λ` has a compact solution set in general position which, if `f + s_λ` has index `d`
at its zeros, is a smooth manifold with boundary and corners of dimension `d`
(`SolutionSetInGeneralPosition.isManifold`; `f + s_λ` is sc-Fredholm with tame germ data by
Theorem 3.1.16, `theorem_3_15_tame`). -/
theorem theorem_5_3_10_isManifold (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      ∀ (s₀ : X → Y) (hs₀ : B.IsScPlusSection s₀), sectionSupport P s₀ ⊆ U → ∀ ε > 0,
        (∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ 1 - ε) →
        ∃ (m : ℕ) (t : Fin m → X → Y) (ht : ∀ i, B.IsScPlusSection (t i)),
          ∃ δ > 0, ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
            ∀ lam : Fin m → ℝ, ‖lam‖ < δ → lam ∉ CV → ∀ d : ℕ,
              ∃ (hft : B.IsScFredholmSectionTame
                  (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam)))
                (hgp : B.SolutionSetInGeneralPosition
                  (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam))),
                ∀ hidx : ∀ y, IsZeroAt P (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam)) y →
                    B.IsLinOfIndex (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam)) y d,
                  IsCompact (solutionSet P
                    (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam))) ∧
                  letI := PX.paracompactSpace_subtype (solutionSet P
                    (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam)))
                  letI := (MPolyfold.subPolyfold
                    (hgp.isSubmanifoldOfDim hft hidx).1.isSubMPolyfold).cornerChartedSpace
                    ((hgp.isSubmanifoldOfDim hft hidx).hasCornerStructureOfDim_of_tame hX
                      (hgp.isGoodPositionAt hX))
                  IsManifold (modelWithCornersEuclideanQuadrant d) ∞ (solutionSet P
                    (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam))) := by
  obtain ⟨U, hUo, hSU, -, hmain⟩ := theorem_5_18 hX hbump hf hS hN
  refine ⟨U, hUo, hSU, fun s₀ hs₀ hsupp ε hε hNε => ?_⟩
  obtain ⟨m, t, ht, -, -, δ, hδ, CV, hCV, hlam⟩ := hmain s₀ hs₀ hsupp ε hε hNε
  refine ⟨m, t, ht, δ, hδ, CV, hCV, fun lam h1 h2 d => ?_⟩
  obtain ⟨-, hgp⟩ := hlam lam h1 h2
  have hft : B.IsScFredholmSectionTame
      (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam)) :=
    theorem_3_15_tame hf (isScPlusSection_paramSlice hs₀ ht lam)
  exact ⟨hft, hgp, fun hidx => hgp.isManifold hX hft hidx⟩

/-- **Theorems 3.1.22 and 3.6.10 in Mathlib's language** (pp. 100, 140; preprint 3.19, 3.56): over an
M-polyfold without boundary, the solution set of an sc-Fredholm section (tame germ data) with
`f'(y)` onto of index `d` at every zero is, with the charted space of its induced structure, a
smooth manifold without boundary of dimension `d`: `IsManifold (𝓡 d) ∞ S`. -/
theorem theorem_3_6_10_isManifold (hX : PX.IsWithoutBoundary) (hft : B.IsScFredholmSectionTame f)
    (htr : B.IsTransversal f) {d : ℕ} (hidx : ∀ y, IsZeroAt P f y → B.IsLinOfIndex f y d) :
    letI := PX.paracompactSpace_subtype (solutionSet P f)
    letI := (MPolyfold.subPolyfold
      (StrongBundle.isSubmanifoldOfDim_solutionSet_of_isTransversal hX hft htr hidx).1.isSubMPolyfold).interiorChartedSpace
      ((StrongBundle.isSubmanifoldOfDim_solutionSet_of_isTransversal hX hft htr
        hidx).hasCornerStructureOfDim_of_degIndex_eq_zero fun y _ => hX y)
      ((StrongBundle.isSubmanifoldOfDim_solutionSet_of_isTransversal hX hft htr
        hidx).1.subPolyfold_degIndex_eq_zero fun y _ => hX y)
    IsManifold (𝓡 d) ∞ (solutionSet P f) :=
  letI := PX.paracompactSpace_subtype (solutionSet P f)
  MPolyfold.isManifold_interiorChartedSpace _ _

/-- **Theorem 3.1.26 in Mathlib's language** (p. 103; preprint 3.23): for an sc-Fredholm section
with tame germ data and a zero `x` in good position, there is an open `U ∋ x` such that
`S(f, U) = {y ∈ U | f(y) = 0}` is, with the charted space of its induced corner structure, a smooth
manifold with boundary and corners `IsManifold (modelWithCornersEuclideanQuadrant d) ∞ S(f, U)`
for some `d` (`theorem_3_1_26_2021def`, `IsManifoldWithCorners.hasCornerStructureOfDim`). -/
theorem theorem_3_1_26_isManifold (hf : B.IsScFredholmSectionTame2021 f) {x : X}
    (hx : IsZeroAt P f x) (hg : B.IsGoodPositionGermTame2021 f x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ (d : ℕ) (hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y}),
        letI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        ∃ h : (MPolyfold.subPolyfold hsub).HasCornerStructureOfDim d,
          letI := (MPolyfold.subPolyfold hsub).cornerChartedSpace h
          IsManifold (modelWithCornersEuclideanQuadrant d) ∞ {y ∈ U | IsZeroAt P f y} := by
  obtain ⟨U, hUo, hxU, -, -, d, hsub, -, hcor⟩ := theorem_3_1_26_2021def hf hx hg
  refine ⟨U, hUo, hxU, d, hsub, ?_⟩
  let _ := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
  exact ⟨hcor.hasCornerStructureOfDim, MPolyfold.isManifold_cornerChartedSpace _⟩

/-! ### Theorem 3.2.3 under the tangent germ property alone -/

/-- **Theorem 3.2.3 in Mathlib's language, with the text's hypothesis only** (p. 106; preprint
3.27): a nonempty `M ⊆ X` with the `n`-dimensional tangent germ property (Definition 3.2.1,
`HasTangentGermProperty`) is, with the charted space of its induced corner structure, a smooth
manifold with boundary and corners `IsManifold (modelWithCornersEuclideanQuadrant n) ∞ M`
(`theorem_3_2_3_isManifold` with the regular data of `HasTangentGermProperty.exists_isRegular`). -/
theorem theorem_3_2_3_isManifold_2021 (P : MPolyfold X) {M : Set X} {n : ℕ} [ParacompactSpace M]
    (hne : M.Nonempty) (hM : P.HasTangentGermProperty M n) :
    letI := (MPolyfold.subPolyfold
      (theorem_3_27_isSubMPolyfold P fun _ hx => hM.exists_isRegular hx)).cornerChartedSpace
      (MPolyfold.theorem_3_27_isManifoldWithCorners P (fun _ hx => hM.exists_isRegular hx)
        hne).hasCornerStructureOfDim
    IsManifold (modelWithCornersEuclideanQuadrant n) ∞ M :=
  MPolyfold.theorem_3_2_3_isManifold P (fun _ hx => hM.exists_isRegular hx) hne

/-- **Theorem 3.2.3 in Mathlib's language, with Definition 3.2.1 as written**
(`HasTangentGermProperty2021`, `hasTangentGermProperty2021_iff`). -/
theorem theorem_3_2_3_isManifold_2021def (P : MPolyfold X) {M : Set X} {n : ℕ}
    [ParacompactSpace M] (hne : M.Nonempty) (hM : P.HasTangentGermProperty2021 M n) :
    letI := (MPolyfold.subPolyfold (theorem_3_27_isSubMPolyfold P fun _ hx =>
      ((MPolyfold.hasTangentGermProperty2021_iff P).1 hM).exists_isRegular hx)).cornerChartedSpace
      (MPolyfold.theorem_3_27_isManifoldWithCorners P (fun _ hx =>
        ((MPolyfold.hasTangentGermProperty2021_iff P).1 hM).exists_isRegular hx)
        hne).hasCornerStructureOfDim
    IsManifold (modelWithCornersEuclideanQuadrant n) ∞ M :=
  theorem_3_2_3_isManifold_2021 P hne ((MPolyfold.hasTangentGermProperty2021_iff P).1 hM)

/-! ### The dimension of the corner charts is the dimension of the submanifold -/

/-- **The two dimensions agree**: if the induced structure on the `m`-dimensional submanifold `A`
has a corner structure of dimension `n`, then `n = m` (the tangent space of a corner chart's model
is the whole model space, `tangentSpace_relOpen`, of dimension `n`; it has dimension `m` by
`IsSubmanifoldOfDim.tangentSpace_subPolyfold_chart`). -/
theorem MPolyfold.IsSubmanifoldOfDim.eq_of_hasCornerStructureOfDim {A : Set X} {m n : ℕ}
    (hA : PX.IsSubmanifoldOfDim A m) [ParacompactSpace A] (hne : A.Nonempty)
    (h : (MPolyfold.subPolyfold hA.1.isSubMPolyfold).HasCornerStructureOfDim n) : n = m := by
  obtain ⟨a₀, ha₀⟩ := hne
  set a : A := ⟨a₀, ha₀⟩
  obtain ⟨χ, hχ, haχ, hc, hn⟩ := h a
  have h1 : a ∈ (MPolyfold.subPolyfold hA.1.isSubMPolyfold).levelSet 1 :=
    (hA.1.mem_levelSet_subPolyfold_iff a 1).2 (hA.1.mem_levelSet_one a.2)
  have hz := (MPolyfold.subPolyfold hA.1.isSubMPolyfold).toBase_levelLift hχ haχ h1
  obtain ⟨-, hdim⟩ := hA.tangentSpace_subPolyfold_chart hχ haχ hz
  rw [tangentSpace_relOpen hc.isRelOpenInQuadrant (hz ▸ χ.mapsTo_model a haχ),
    Submodule.span_univ, finrank_top] at hdim
  exact hn.symm.trans hdim

end Polyfold
