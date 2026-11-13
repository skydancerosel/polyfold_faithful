import Polyfold.Chapter15.P3W6G6_ParamOntoBridge

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3,
**Theorem 15.3.7** (General Position; 2017: Theorem 15.4), pp. 693–698.

# Theorem 15.3.7 under the hypotheses of the text and a good system

## The text, paraphrased

At `x ∈ S_f` the proof picks smooth `w_1, …, w_ℓ ∈ W_x` with `f'(x)(T^R_xX) + span{w_j} = W_x`,
extends them to small sc⁺-sections `s_j`, and (15.1) with `s_j(y)` persists at the points of
`S_f` near `x`; the text refers to Part I for these steps (Theorems 5.3.5, 5.3.10).

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`hasPointwiseParamOnto`**: GA's `HasPointwiseParamOnto A f N` (smooth `w_j ∈ W_x` with
  `N(w_j) < ε` and (15.1)), for `X` with sc-smooth bump functions, `f` an sc-Fredholm section
  functor with tame germ data and `N` an auxiliary norm.  *Proof*: Part I's
  `exists_sections_isParamGP` in a tame chart centred at `x`, for the auxiliary norm `(2/ε)·N`,
  and the bridge `isParamOntoVec_iff_isParamGP`; `w_j = s_j(x)` is smooth since `x` is.
* **`hasParamOntoOpen`**: GA's `HasParamOntoOpen A f` for tame `X`.  *Proof*: the bridge at `x`
  gives (i)–(ii); Part I's `isGeneralPositionGerm_paramSection_of_isParamGP` gives general
  position of `F(t, y) = f(y) + Σ_j t_j s_j(y)` on `ℝ^ℓ × X` at `(0, x)`; general position is
  open along the zeros of `F` (`exists_isOpen_isGeneralPositionGerm`, `ℝ^ℓ × X` tame); at a zero
  `(0, y)` nearby, Part I's `isParamGP_of_isGeneralPositionGerm` gives (i)–(ii) in a tame chart
  centred at `y`, and the bridge gives (15.1) at `y`.
* **`theorem_15_3_7_of_goodSystem`**: Theorem 15.3.7 (G's `theorem_15_3_7_statement`, with the
  "structurable" addendum) from a good system alone: GA's `theorem_15_3_7_of_pointwise` with
  both Props discharged here and GB's `hasParametricGeneralPosition`.
* **`theorem_15_3_7_of_paracompact`**: the same for an ep-groupoid with paracompact orbit space
  (Theorem 13.1.8 gives the good system).
* `theorem_15_3_7_statement_epSEP_zero_of_goodSystem`: the statement on `ℝⁿ × ℝ⁰ → ℝⁿ`
  through this route.

## Reading

* The good system is needed only for the addendum "`Λ` can be taken structurable" (Definition
  13.3.6 asks for a good system); Remark 15.3.8 notes that the theorem does not assume
  paracompactness of `|X|`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-- At a zero `y ∈ X₁` of `f` there is a tame chart centred at `y` with a presentation of its
partial quadrant. -/
theorem exists_tameChart_centred {f : A.Obj → A.W} (hft : A.B.IsScFredholmSectionTame f)
    {y : A.Obj} (hy0 : f y = fiberZero A.P y) :
    ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ y ∈ c.φ.source ∧ c.φ y = 0 ∧
      ∃ (n : ℕ) (Wq : ScBanach) (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
        c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0 := by
  have hys : y ∈ A.X.PObj.smoothSet := mem_smoothSet_of_eq hft isOpen_univ
    (isScPlusSectionOn_fiberZero isOpen_univ) (mem_univ y) hy0
  obtain ⟨-, c, hc, hyc, hφ0, -⟩ := hft.germTame y hys
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  exact ⟨c, hc, hyc, hφ0, n, Wq, T, hT⟩

/-! ### The pointwise choice -/

/-- **The pointwise choice of the proof of Theorem 15.3.7 holds** (GA's `HasPointwiseParamOnto`):
for `X` with sc-smooth bump functions, `f` an sc-Fredholm section functor with tame germ data
and an auxiliary norm `N`, at every `x ∈ S_f` and for every `ε > 0` there are smooth
`w_j ∈ W_x` with `N(w_j) < ε` and (15.1) at `x`. -/
theorem hasPointwiseParamOnto (hbump : A.X.AdmitsBumpFunctionsPointwise) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) : HasPointwiseParamOnto A f N := by
  intro x hx ε hε
  have hx0 : f (A.X.PObj.levelVal 1 x) = fiberZero A.P (A.X.PObj.levelVal 1 x) := hx
  have hys : A.X.PObj.levelVal 1 x ∈ A.X.PObj.smoothSet := mem_smoothSet_of_eq hft isOpen_univ
    (isScPlusSectionOn_fiberZero isOpen_univ) (mem_univ _) hx0
  obtain ⟨c, hc, hxc, hφ0, n, Wq, T, hT⟩ := exists_tameChart_centred hft hx0
  have ha : (0 : ℝ) < 2 / ε := div_pos two_pos hε
  obtain ⟨k, s, hs, -, hsN, hGP⟩ := exists_sections_isParamGP
    (EpGroupoid.theorem_12_3_2_1.1 hbump) (hN.const_mul ha) hft hx0 hc hxc hφ0 T hT
    isOpen_univ (mem_univ _)
  have hon := (isParamOntoVec_iff_isParamGP hf hft (fun j => (hs j).1) hc.1 hxc hφ0 hx0 T
    hT).2 hGP
  refine ⟨k, fun j => ⟨s j (A.X.PObj.levelVal 1 x), (hs j).1 _⟩, fun j => ?_, fun j => ?_, hon⟩
  · exact mem_iInter.2 fun m =>
      (hs j).isScSmoothSection'.2.mapsTo_levelSet m (mem_iInter.1 hys m)
  · have h1 := (hs j).mem_oneSet (A.X.PObj.levelVal 1 x)
    change normW N (s j (A.X.PObj.levelVal 1 x)) < ε
    rw [normW_of_mem N h1]
    have h2 := hsN j (A.X.PObj.levelVal 1 x) h1
    have h3 : N (A.B.oneMk (s j (A.X.PObj.levelVal 1 x)) h1) ≤ ε / 2 := by
      rw [div_mul_eq_mul_div, div_le_one hε] at h2
      linarith
    linarith

/-! ### The openness of (15.1) -/

/-- **The openness of (15.1) along `S_f` holds** (GA's `HasParamOntoOpen`) for tame `X` and an
sc-Fredholm section functor `f` with tame germ data: Part I's openness of general position along
the solution set of the parametrized section, read through the bridge. -/
theorem hasParamOntoOpen (hX : A.X.IsTame) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f) :
    HasParamOntoOpen A f := by
  intro ℓ s hs x hx hon
  have := MPolyfold.paracompactSpace_prod (rnPolyfold ℓ) A.X.PObj
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin ℓ → ℝ) × A.Obj → A.Obj))
    ((rnPolyfold ℓ).prod A.X.PObj) A.B
  have hx0 : f (A.X.PObj.levelVal 1 x) = fiberZero A.P (A.X.PObj.levelVal 1 x) := hx
  obtain ⟨c, hc, hxc, hφ0, n, Wq, T, hT⟩ := exists_tameChart_centred hft hx0
  have hGP := (isParamOntoVec_iff_isParamGP hf hft (fun j => (hs j).1) hc.1 hxc hφ0 hx0 T
    hT).1 hon
  have hgerm := isGeneralPositionGerm_paramSection_of_isParamGP hft hs hx0 hc hxc hφ0 T hT hGP
  have hzero : ∀ y : A.Obj, f y = fiberZero A.P y → IsZeroAt (pullbackProj A.P Prod.snd)
      (paramSection f hft.isScSmooth.1 s fun i => (hs i).1) ((0 : Fin ℓ → ℝ), y) := by
    intro y hy0
    rw [isZeroAt_paramSection_iff]
    change IsZeroAt A.P (paramSlice f hft.isScSmooth.1 s (fun i => (hs i).1) 0) y
    rw [paramSlice_zero]
    exact hy0
  obtain ⟨W₀, hW₀o, h0W₀, -, hW₀⟩ := exists_isOpen_isGeneralPositionGerm (prod_rn_isTame hX)
    (theorem_3_1_21_tame hft hs) (hzero _ hx0) hgerm
  refine ⟨(fun y => ((0 : Fin ℓ → ℝ), y)) ⁻¹' W₀,
    hW₀o.preimage (continuous_const.prodMk continuous_id), h0W₀, fun y hyW hy => ?_⟩
  have hy0 : f (A.X.PObj.levelVal 1 y) = fiberZero A.P (A.X.PObj.levelVal 1 y) := hy
  obtain ⟨-, hgp, -⟩ := hW₀ _ hyW (hzero _ hy0)
  obtain ⟨c', hc', hyc', hφ0', n', Wq', T', hT'⟩ := exists_tameChart_centred hft hy0
  have hGP' := isParamGP_of_isGeneralPositionGerm hft hs hy0 hc' hyc' hφ0' T' hT' hgp
  exact (isParamOntoVec_iff_isParamGP hf hft (fun j => (hs j).1) hc'.1 hyc' hφ0' hy0 T'
    hT').2 hGP'

/-! ### Theorem 15.3.7 -/

/-- **Theorem 15.3.7 (General Position; 2017: Theorem 15.4), pp. 693–694**, as stated
(`theorem_15_3_7_statement`: `X` tame with sc-smooth bump functions, `f` an sc-Fredholm section
functor with tame germ data and compact `|S_f|`, `(N, U)` controlling compactness, `h` a
continuous functor into `(0, 1]`; then a structurable `Λ` with (1)–(4)), from a good system
alone.  The two analytic steps of the proof are proved: the local constructions
(`hasPointwiseParamOnto`, `hasParamOntoOpen`, through GA's `theorem_15_3_7_of_pointwise`) and
the parametric transversality (GB's `hasParametricGeneralPosition`).  The good system is the
content of the addendum "`Λ` can be taken structurable" (Definition 13.3.6). -/
theorem theorem_15_3_7_of_goodSystem (h𝒰 : Nonempty A.X.GoodSystem) :
    theorem_15_3_7_statement A :=
  theorem_15_3_7_of_pointwise h𝒰 fun htame hbump _ hf hft hS _ _ hcc =>
    ⟨hasPointwiseParamOnto hbump hf hft hcc.1.isAuxNorm, hasParamOntoOpen htame hf hft,
      hasParametricGeneralPosition htame hf hft hS hcc⟩

/-- **Theorem 15.3.7 for an ep-groupoid with paracompact orbit space**: Theorem 13.1.8 gives the
good system. -/
theorem theorem_15_3_7_of_paracompact (hX : A.X.HasParacompactOrbitSpace) :
    theorem_15_3_7_statement A := by
  obtain ⟨𝒰, -⟩ := A.X.theorem_13_1_8 hX (fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => mem_univ _)
  exact theorem_15_3_7_of_goodSystem ⟨𝒰⟩

/-- **The statement on `ℝⁿ × ℝ⁰ → ℝⁿ`** through `theorem_15_3_7_of_goodSystem`. -/
theorem theorem_15_3_7_statement_epSEP_zero_of_goodSystem (n : ℕ) :
    theorem_15_3_7_statement (StrongBundleEquivalenceExamples.epSEP n 0) :=
  theorem_15_3_7_of_goodSystem (nonempty_goodSystem_epSEP_zero n)

end SBLocalization

end Polyfold
