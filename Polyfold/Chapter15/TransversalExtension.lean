import Polyfold.Chapter15.GeneralPositionBranched
import Polyfold.Chapter14.BoundaryStructured
import Polyfold.Chapter9.CoveringFromText

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, pp. 694–699:
**Theorem 15.3.9** (Transversal Extension Theorem; 2017: Theorem 15.5), as a statement and as a
reduction of it to the ∂-Extension Theorem 14.1.9 and two steps of the text's proof.

# The Transversal Extension Theorem

## The text, paraphrased

Over a tame ep-groupoid with paracompact `|X|` and sc-smooth partitions of unity, let `f` be
sc-Fredholm with compact `|S_f|`, `(N, U)` controlling compactness, and `Λ : W|∂X → ℚ⁺` an
`(N, U)`-admissible structurable sc⁺-multisection with `N(Λ) < h` on `∂X` for a continuous functor
`h : X → (0, 1]`, such that `T(f|∂X, Λ)(x)` is "surjective with respect to intersections of local
faces" at every smooth `x ∈ ∂X`.  Then there is a structurable `Λ̃ : W → ℚ⁺` with (1)
`Λ̃|(W|∂X) = Λ`, (2) dom-supp in `U` and `N(Λ̃) < h`, so `Λ̃` is admissible, (3) `T(f, Λ̃)` onto on
`supp(Λ̃ ∘ f)`; moreover `Λ̃ ∘ f` is a compact tame branched ep⁺-subgroupoid.

The proof (pp. 698–699): (a) pick a continuous functor `h₀` with `N(Λ) < h₀ < h` on `∂X`,
supported in `U`; (b) Theorem 14.1.9 extends `Λ` to a structurable `Λ₀` with `N(Λ₀) ≤ h₀`,
dom-supp in `U`; (c) the boundary assumption gives transversality of `(f, Λ₀)` near `∂X`; (d) away
from `∂X` one "argues as in Theorem 15.3.7" with parameter-dependent perturbations `Λ_t` whose
domain support avoids `∂X`, and takes `Λ̃ = Λ_t ⊕ Λ₀` for small `t`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `IsReducedOntoAtPt f Λ x`: Definition 15.3.5 at one point (`IsInGeneralPosition` is the
  conjunction over `supp(Λ ∘ f)`, `isInGeneralPosition_iff_forall_reducedOntoAtPt`).
* `IsBoundaryFaceOnto f Λ`: the reading of "`T(f|∂X, Λ)(x)` surjective with respect to
  intersections of local faces, for every smooth `x ∈ ∂X`" (see Reading below).
* **`theorem_15_3_9_statement A : Prop`**: the theorem as printed (readings below).
* Two steps of the proof as propositions: `lemma_15_3_9_cutoff_statement` (step (a)) and
  `theorem_15_3_7_relative_statement` (steps (c)–(d): the relative form of the general position
  theorem that the proof invokes with "argue as in Theorem 15.3.7").
* **`theorem_15_3_9_hyp`**: `theorem_14_1_9_statement A → lemma_15_3_9_cutoff_statement A →
  theorem_15_3_7_relative_statement A → theorem_15_3_9_statement A` (steps (b) and the
  assembly, including the "moreover" via Theorem 15.3.7's "in particular",
  `theorem_15_3_7_in_particular_hyp`).
* Witnesses: on `ℝⁿ × ℝ⁰ → ℝⁿ` (`epSEP n 0`) the three propositions and the statement hold
  (`…_epSEP_zero`), so none of them is vacuous on that example.

## Reading

* "Surjective with respect to intersections of local faces": the smallest intersection of the
  tangent spaces of the local faces at `x` is `T^R_xX` (Part I, Definition 2.5.8), and onto on it
  implies onto on every larger intersection; so the condition is read as onto on `T^R_xX`, i.e.
  general position at `x` (D15.3.5).  The restriction of `(f − sᵢ)'(x)` to `T^R_xX` only involves
  the values of `sᵢ` on the faces, so it is the same for every sc⁺ extension of `Λ`; we ask the
  condition for every sc⁺-multisection `Λ'` on `W` agreeing with `Λ` over `∂X` (the independence
  of the extension is not proved here).
* `Λ : W|∂X → ℚ⁺` is a function on `W` of which only the values over `∂X` enter (as in B1's
  `IsBoundaryStructurable`); "(U, N)-admissible" over `∂X` is `boundaryDomSupp Λ ⊆ U` and
  `N(Λ) ≤ 1` on `∂X`.
* `U` is open and saturated (`ControlsCompactness`); the text says "a saturated subset".
* As in §15.2–15.3, `f` carries tame germ data (`IsScFredholmSectionTame`), the inherited Part I
  hypothesis of Theorem 3.6.8.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}}

/-! ### General position at one point -/

/-- **Definition 15.3.5 at one point** (p. 693): every operator `L` of `T(f,Λ)(x)` is onto on
`T^R_xX`, read in every chart of `X` at `x` and every presentation of its partial quadrant (as in
P's `IsInGeneralPosition`). -/
def IsReducedOntoAtPt (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) (x : A.X.PObj.Level 1) : Prop :=
  ∀ L ∈ (linearization f Λ x).support, ∀ (φ : MChart A.Obj) (hφ : A.X.PObj.IsChart φ)
    (hx : A.X.PObj.levelVal 1 x ∈ φ.source) (k : ℕ) (V : ScBanach)
    (T : ScIso φ.model.E ((ScBanach.const (Fin k → ℝ)).prod V)),
    φ.model.C = T 0 ⁻¹' quadrant k V 0 →
      Surjective (L.domRestrict (reducedTangentFiber hφ hx T))

/-- Definition 15.3.5 is general position at every point of `supp(Λ ∘ f)`. -/
theorem isInGeneralPosition_iff_forall_reducedOntoAtPt {f : A.Obj → A.W} {Λ : A.W → ℚ≥0} :
    IsInGeneralPosition A f Λ ↔
      ∀ x : A.X.PObj.Level 1, 0 < Λ (f (A.X.PObj.levelVal 1 x)) → IsReducedOntoAtPt f Λ x :=
  Iff.rfl

/-- **The boundary hypothesis of Theorem 15.3.9** (p. 694), "`T(f|∂X, Λ)(x)` is surjective with
respect to intersections of local faces for every smooth `x ∈ ∂X`", read as onto on `T^R_xX`
(general position at `x`) for every sc⁺-multisection `Λ'` on `W` that agrees with `Λ` over
`∂X` (the restriction to `T^R_xX` only sees the face values). -/
def IsBoundaryFaceOnto (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) : Prop :=
  ∀ Λ' : A.W → ℚ≥0, IsScPlusMultisection A Λ' →
    (∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ w) →
    ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
      A.X.PObj.levelVal 1 x ∈ A.X.PObj.smoothSet → 0 < Λ (f (A.X.PObj.levelVal 1 x)) →
        IsReducedOntoAtPt f Λ' x

/-! ### The statement -/

variable (A) in
/-- **Theorem 15.3.9 (Transversal Extension Theorem; 2017: Theorem 15.5), p. 698**, as a
proposition.  `X` tame with paracompact `|X|` and sc-smooth partitions of unity (Definition 5.5.1
for the M-polyfold of objects, as in B1's Theorem 14.1.9), `f` sc-Fredholm with tame germ data
(inherited) and compact `|S_f|`, `(N, U)` controlling compactness, `Λ : W|∂X → ℚ⁺`
structurable (Definition 14.1.7) and `(N, U)`-admissible over `∂X`, `h : X → (0, 1]` a
continuous functor with `N(Λ) < h` on `∂X`, and the boundary hypothesis `IsBoundaryFaceOnto`.
Then there is a structurable `Λ̃` with (1) `Λ̃ = Λ` over `∂X`, (2) `dom-supp(Λ̃) ⊆ U`,
`N(Λ̃) < h`, `Λ̃` `(N, U)`-admissible, (3) `T(f, Λ̃)` onto on `supp(Λ̃ ∘ f)`, and `Λ̃ ∘ f` a compact
branched ep⁺-subgroupoid. -/
def theorem_15_3_9_statement : Prop :=
  A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.PObj.AdmitsScPartitionsOfUnity →
  ∀ f : A.Obj → A.W, A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
    A.E.HasCompactSolutionSetEp f →
  ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
  ∀ Λ : A.W → ℚ≥0, IsBoundaryStructurable A Λ → boundaryDomSupp Λ ⊆ U →
    (∀ x ∈ A.X.PObj.boundary, pointwiseNorm N Λ x ≤ 1) →
  ∀ h : A.Obj → ℝ, Continuous h → (∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) →
    (∀ x, 0 < h x ∧ h x ≤ 1) → (∀ x ∈ A.X.PObj.boundary, pointwiseNorm N Λ x < h x) →
    IsBoundaryFaceOnto f Λ →
  ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧ (∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ w) ∧
    domSupp Λ' ⊆ U ∧ (∀ x, pointwiseNorm N Λ' x < h x) ∧ IsAdmissible A f N U Λ' ∧
    IsTransversal f Λ' ∧ A.X.IsBranchedEpSubgroupoid (fun z => (Λ' (f z) : ℚ)) ∧
    A.X.IsCompactBranched (fun z => (Λ' (f z) : ℚ))

/-! ### Two steps of the proof, as propositions -/

variable (A) in
/-- **Step (a) of the proof of Theorem 15.3.9** (p. 698, "we first take a continuous functor
`h₀`"): for `Λ : W|∂X → ℚ⁺` sc⁺ over `∂X` with `N(Λ) < h` on `∂X` and dom-supp in the saturated
open `U`, there is a continuous functor `h₀ ≥ 0`, supported in `U`, with `h₀ < h` and
`N(Λ) < h₀` on `dom-supp(Λ)`; these are the hypotheses Theorem 14.1.9 needs, with the margin
`h₀ < h` used at the end. -/
def lemma_15_3_9_cutoff_statement : Prop :=
  A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.PObj.AdmitsScPartitionsOfUnity →
  ∀ Λ : A.W → ℚ≥0, IsBoundaryScPlusMultisection A Λ →
  ∀ N : A.B.One → ℝ, A.E.IsAuxNorm N →
  ∀ U : Set A.Obj, IsOpen U → A.X.IsSaturated U → boundaryDomSupp Λ ⊆ U →
  ∀ h : A.Obj → ℝ, Continuous h → (∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) → (∀ x, 0 < h x) →
    (∀ x ∈ A.X.PObj.boundary, pointwiseNorm N Λ x < h x) →
  ∃ h₀ : A.Obj → ℝ, Continuous h₀ ∧ (∀ x, 0 ≤ h₀ x) ∧
    (∀ φ, h₀ (A.X.tgt φ) = h₀ (A.X.src φ)) ∧ tsupport h₀ ⊆ U ∧ (∀ x, h₀ x < h x) ∧
    ∀ x ∈ boundaryDomSupp Λ, pointwiseNorm N Λ x < h₀ x

variable (A) in
/-- **Steps (c)–(d) of the proof of Theorem 15.3.9** (pp. 698–699), the relative form of the
general position theorem ("we can argue as in Theorem 15.3.7"): given a structurable `Λ₀` with
dom-supp in `U`, `N(Λ₀) < h`, and `(f, Λ₀)` in general position at the points of
`supp(Λ₀ ∘ f) ∩ ∂X`, there is a structurable `Λ̃` agreeing with `Λ₀` over `∂X`, with dom-supp in
`U`, `N(Λ̃) < h`, and `(f, Λ̃)` transversal and in general position.  (In the text,
`Λ̃ = Λ_t ⊕ Λ₀` with `Λ_t` supported away from `∂X`; openness of general position gives the
neighbourhood `Q` of the boundary part of the support.) -/
def theorem_15_3_7_relative_statement : Prop :=
  A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.PObj.AdmitsScPartitionsOfUnity →
  ∀ f : A.Obj → A.W, A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
    A.E.HasCompactSolutionSetEp f →
  ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
  ∀ h : A.Obj → ℝ, Continuous h → (∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) →
    (∀ x, 0 < h x ∧ h x ≤ 1) →
  ∀ Λ₀ : A.W → ℚ≥0, IsStructurable A Λ₀ → domSupp Λ₀ ⊆ U → (∀ x, pointwiseNorm N Λ₀ x < h x) →
    (∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
      0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsReducedOntoAtPt f Λ₀ x) →
  ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧ (∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ₀ w) ∧
    domSupp Λ' ⊆ U ∧ (∀ x, pointwiseNorm N Λ' x < h x) ∧ IsTransversal f Λ' ∧
    IsInGeneralPosition A f Λ'

/-! ### The reduction -/

/-- Transversality from general position, for an sc-Fredholm section functor (every operator of
the support is onto on `T_xX ⊇ T^R_xX`). -/
theorem IsInGeneralPosition.isTransversal {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (hgp : IsInGeneralPosition A f Λ) : IsTransversal f Λ := by
  intro x hx
  have hx1 := mem_levelSet_one_of_pos hf hΛ hx
  refine ⟨hx, hx1, fun L hL => hgp.surjective ?_ hL⟩
  rw [A.X.PObj.levelVal_levelMk]; exact hx

/-- **Theorem 15.3.9 (Transversal Extension Theorem), p. 694, reduced to Theorem 14.1.9 and two
steps of the text's proof**: if the ∂-Extension Theorem (`theorem_14_1_9_statement`, B1), the
choice of the cut-off `h₀` (step (a)) and the relative general position theorem (steps (c)–(d))
hold for `A`, then Theorem 15.3.9 holds for `A`.  Step (b) (the application of Theorem 14.1.9 with
`Ũ = U` and `f = h₀`), the boundary transversality of the extension (from `IsBoundaryFaceOnto`,
at smooth points by `mem_smoothSet_of_pos`), admissibility (`isAdmissible_of_domSupp_subset`)
and the "moreover" (Theorem 15.3.7's "in particular") are proved here. -/
theorem theorem_15_3_9_hyp (h149 : theorem_14_1_9_statement A)
    (hcut : lemma_15_3_9_cutoff_statement A) (hrel : theorem_15_3_7_relative_statement A) :
    theorem_15_3_9_statement A := by
  intro hX hpara hPU f hf hft hS N U hcc Λ hΛ hdomU _ h hc hfun hh hNh honto
  obtain ⟨h₀, h0c, h0nn, h0fun, h0supp, h0lt, h0gt⟩ :=
    hcut hX hpara hPU Λ hΛ.1 N hcc.1 U hcc.2.1 hcc.2.2.1 hdomU h hc hfun (fun x => (hh x).1) hNh
  obtain ⟨Λ₀, hΛ₀, hΛ₀N, hΛ₀dom, hΛ₀bd⟩ :=
    h149 hX hpara hPU Λ hΛ N hcc.1 U hcc.2.1 hcc.2.2.1 hdomU h₀ h0c h0nn h0fun h0supp h0gt
  have hsec : IsSection A.P f := hf.1.1.1
  have hgp0 : ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
      0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsReducedOntoAtPt f Λ₀ x := by
    intro x hx hpos
    have hbd : A.P (f (A.X.PObj.levelVal 1 x)) ∈ A.X.PObj.boundary := by rw [hsec]; exact hx
    have hpos' : 0 < Λ (f (A.X.PObj.levelVal 1 x)) := by rwa [← hΛ₀bd _ hbd]
    exact honto Λ₀ hΛ₀.1 hΛ₀bd x hx (mem_smoothSet_of_pos hft hΛ₀.1 hpos) hpos'
  obtain ⟨Λ', hΛ', hbd', hdom', hN', htr', hgp'⟩ :=
    hrel hX hpara hPU f hf hft hS N U hcc h hc hfun hh Λ₀ hΛ₀ hΛ₀dom
      (fun x => (hΛ₀N x).trans_lt (h0lt x)) hgp0
  have hN1 : ∀ x, pointwiseNorm N Λ' x ≤ 1 := fun x => (hN' x).le.trans (hh x).2
  obtain ⟨hbr, hcpt⟩ := theorem_15_3_7_in_particular_hyp hf hft hcc hΛ'.1 hN1 hdom' hgp'
  exact ⟨Λ', hΛ', fun w hw => (hbd' w hw).trans (hΛ₀bd w hw), hdom', hN',
    isAdmissible_of_domSupp_subset hsec hcc.2.2.2.1 hΛ'.1 hN1 hdom', htr', hbr, hcpt⟩

/-! ### Witnesses on `ℝⁿ × ℝ⁰ → ℝⁿ` -/

/-- `∂X = ∅` for the trivial ep-groupoid of `ℝⁿ` (`d ≡ 0`). -/
theorem boundary_epSEP_eq_empty (n : ℕ) :
    (StrongBundleEquivalenceExamples.epSEP n 0).X.PObj.boundary = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  have h1 : 1 ≤ (StrongBundleEquivalenceExamples.epSEP n 0).X.PObj.degIndex x := hx
  have h0 : (StrongBundleEquivalenceExamples.epSEP n 0).X.PObj.degIndex x = 0 :=
    EpGroupoid.degIndex_rnPolyfold_trivial n x
  rw [h0] at h1
  exact absurd h1 (by norm_num)

/-- `boundaryDomSupp Λ = ∅` on the example (no boundary). -/
theorem boundaryDomSupp_epSEP (n : ℕ) (Λ : (StrongBundleEquivalenceExamples.epSEP n 0).W → ℚ≥0) :
    boundaryDomSupp Λ = ∅ := by
  rw [boundaryDomSupp, closure_empty_iff, eq_empty_iff_forall_notMem]
  rintro x ⟨hx, -⟩
  rw [boundary_epSEP_eq_empty] at hx
  exact hx

/-- **Step (a) holds on the example** (`h₀ = 0`: there is no boundary). -/
theorem lemma_15_3_9_cutoff_statement_epSEP_zero (n : ℕ) :
    lemma_15_3_9_cutoff_statement (StrongBundleEquivalenceExamples.epSEP n 0) := by
  intro _ _ _ Λ _ _ _ _ _ _ _ h _ _ hpos _
  refine ⟨fun _ => 0, continuous_const, fun _ => le_rfl, fun _ => rfl, by simp,
    fun x => hpos x, ?_⟩
  rw [boundaryDomSupp_epSEP]
  exact fun x hx => absurd hx (notMem_empty x)

/-- **Steps (c)–(d) hold on the example** (`Λ̃ = Λ₀`: every pair is in general position). -/
theorem theorem_15_3_7_relative_statement_epSEP_zero (n : ℕ) :
    theorem_15_3_7_relative_statement (StrongBundleEquivalenceExamples.epSEP n 0) := by
  intro _ _ _ f hf _ _ N U _ h _ _ _ Λ₀ hΛ₀ hdom hN _
  have hgp := isInGeneralPosition_epSEP_zero n f Λ₀
  exact ⟨Λ₀, hΛ₀, fun _ _ => rfl, hdom, hN, hgp.isTransversal hf hΛ₀.1, hgp⟩

/-- **Theorem 15.3.9 holds on the example**: there is no boundary, and the trivial multisection
`Λ₀` has all the conclusions (every pair is in general position). -/
theorem theorem_15_3_9_statement_epSEP_zero (n : ℕ) :
    theorem_15_3_9_statement (StrongBundleEquivalenceExamples.epSEP n 0) := by
  intro _ hpara _ f hf hft _ N U hcc Λ _ _ _ h _ _ hh _ _
  have hgp := isInGeneralPosition_epSEP_zero n f (zeroMultisection _)
  have hΛ₀ := isScPlusMultisection_zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)
  have hN0 := pointwiseNorm_zeroMultisection (A := StrongBundleEquivalenceExamples.epSEP n 0)
    hcc.1.isAuxNorm
  have hdom : domSupp (zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0)) ⊆ U := by
    rw [domSupp_zeroMultisection]; exact empty_subset _
  have hN1 : ∀ x, pointwiseNorm N (zeroMultisection _) x ≤ 1 := fun x => by rw [hN0]; norm_num
  obtain ⟨hbr, hcpt⟩ := theorem_15_3_7_in_particular_hyp hf hft hcc hΛ₀ hN1 hdom hgp
  refine ⟨zeroMultisection _, isStructurable_zeroMultisection hpara, fun w hw => ?_, hdom,
    fun x => by rw [hN0]; exact (hh x).1,
    isAdmissible_of_domSupp_subset hf.1.1.1 hcc.2.2.2.1 hΛ₀ hN1 hdom,
    hgp.isTransversal hf hΛ₀, hbr, hcpt⟩
  rw [boundary_epSEP_eq_empty] at hw
  exact absurd hw (notMem_empty _)

end SBLocalization

end Polyfold
