import Polyfold.Chapter15.RelativeLocalFamilies
import Polyfold.Chapter15.TransversalExtensionWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9**, steps (c)–(d), pp. 698–699, with sc-smooth bump functions in place of
sc-smooth partitions of unity.

# The relative step of Theorem 15.3.9 from bump functions

## The text, paraphrased

Steps (c)–(d): near `supp(Λ₀ ∘ f) ∩ ∂X` the extension `Λ₀` is already in general position; away
from `∂X` one argues as in Theorem 15.3.7, which assumes sc-smooth bump functions only.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `relative_local_families_of_bump`: the relative local families of the proof
  (`HasLocalGPFamiliesRel` with domain support in `U ∖ ∂X`) for tame `X` with sc-smooth bump
  functions on the object M-polyfold.  The proof of `relative_local_families_holds` uses the
  partitions of unity of its statement only through their bump functions.
* **`theorem_15_3_7_relative_of_bump`**: steps (c)–(d) of the proof of Theorem 15.3.9 (the
  conclusion of `theorem_15_3_7_relative_statement`) for tame `X` with sc-smooth bump functions;
  no paracompactness and no partitions of unity.
* `theorem_15_3_7_relative_of_bump_halfSEP`: the hypotheses hold on the half-plane example
  `halfSEP 1 1` (`∂X ≠ ∅`, non-zero fibres, `supp(Λ₀ ∘ f) ∩ ∂X ≠ ∅`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold EpGroupoid SEP

variable {A : SEP.{u}}

/-- **The relative local families of the proof of Theorem 15.3.9 from bump functions**: for tame
`X` whose object M-polyfold admits sc-smooth bump functions, `f` sc-Fredholm with tame germ data,
`(N, U)` controlling compactness, `h : X → (0, 1]` a continuous functor and `Λ₀` structurable with
dom-supp in `U`, `N(Λ₀) < h`, and `(f, Λ₀)` in general position at the points of
`supp(Λ₀ ∘ f) ∩ ∂X`, the local general position families relative to `Λ₀` with domain support
in `U ∖ ∂X` and size `h − N(Λ₀)` exist. -/
theorem relative_local_families_of_bump (hX : A.X.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N : A.B.One → ℝ} {U : Set A.Obj} (hcc : ControlsCompactness A f N U) {h : A.Obj → ℝ}
    (hc : Continuous h) (hfun : ∀ φ, h (A.X.src φ) = h (A.X.tgt φ))
    (hh : ∀ x, 0 < h x ∧ h x ≤ 1) {Λ₀ : A.W → ℚ≥0} (hΛ₀ : IsStructurable A Λ₀)
    (hdom : domSupp Λ₀ ⊆ U) (hN : ∀ x, pointwiseNorm N Λ₀ x < h x)
    (hbd : ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
      0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsReducedOntoAtPt f Λ₀ x) :
    HasLocalGPFamiliesRel A f Λ₀ N (U ∩ A.X.PObj.boundaryᶜ)
      (fun x => h x - pointwiseNorm N Λ₀ x) := by
  obtain ⟨D, -⟩ := hΛ₀.2
  have h𝒰 : Nonempty A.X.GoodSystem := ⟨D.𝒰⟩
  have hNB : A.B.IsAuxNorm N := hcc.1.isAuxNorm
  refine hasLocalGPFamiliesRel_of_boundary h𝒰 hNB (fun x hxb hpos => ?_)
    (exists_relGPFamily_of_seeds h𝒰 hf hcc hΛ₀.1 hdom hc hfun (fun x => (hh x).2) hN
      (hasLocalParamSeedsRel hX hbump hf hft hΛ₀.1 hNB))
  have hx1 := mem_levelSet_one_of_pos hf hΛ₀.1 hpos
  exact exists_isOpen_isReducedOntoAtPt hX hf hft hΛ₀.1 hx1
    (hbd _ (by rw [A.X.PObj.levelVal_levelMk]; exact hxb)
      (by rw [A.X.PObj.levelVal_levelMk]; exact hpos))

/-- **Steps (c)–(d) of the proof of Theorem 15.3.9 (pp. 698–699) from bump functions**: for tame
`X` whose object M-polyfold admits sc-smooth bump functions, `f` sc-Fredholm with tame germ data,
`(N, U)` controlling compactness, `h : X → (0, 1]` a continuous functor and `Λ₀` structurable with
dom-supp in `U`, `N(Λ₀) < h` and `(f, Λ₀)` in general position at the points of
`supp(Λ₀ ∘ f) ∩ ∂X`, there is a structurable `Λ'` equal to `Λ₀` over `∂X`, with dom-supp in `U`,
`N(Λ') < h`, `(f, Λ')` transversal and in general position.  This is the conclusion of
`theorem_15_3_7_relative_statement` without its partitions of unity and paracompactness. -/
theorem theorem_15_3_7_relative_of_bump (hX : A.X.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N : A.B.One → ℝ} {U : Set A.Obj} (hcc : ControlsCompactness A f N U) {h : A.Obj → ℝ}
    (hc : Continuous h) (hfun : ∀ φ, h (A.X.src φ) = h (A.X.tgt φ))
    (hh : ∀ x, 0 < h x ∧ h x ≤ 1) {Λ₀ : A.W → ℚ≥0} (hΛ₀ : IsStructurable A Λ₀)
    (hdom : domSupp Λ₀ ⊆ U) (hN : ∀ x, pointwiseNorm N Λ₀ x < h x)
    (hbd : ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
      0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsReducedOntoAtPt f Λ₀ x) :
    ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧ (∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ₀ w) ∧
      domSupp Λ' ⊆ U ∧ (∀ x, pointwiseNorm N Λ' x < h x) ∧ IsTransversal f Λ' ∧
      IsInGeneralPosition A f Λ' :=
  theorem_15_3_7_relative_hyp hf (continuousOn_univ.1 hft.isScSmooth.2.continuousOn) hcc hh
    hΛ₀ hdom hN (relative_local_families_of_bump hX hbump hf hft hcc hc hfun hh hΛ₀ hdom hN hbd)
    (hasParametricGeneralPositionRel hX hf hft hcc hΛ₀.1 (fun x => (hN x).le.trans (hh x).2)
      hdom)

end SBLocalization

namespace HalfSpaceBundle

open SBLocalization

/-- **The relative step from bump functions on the half-plane example**, with `∂X ≠ ∅`, non-zero
fibres and `supp(Λ₀ ∘ f) ∩ ∂X ≠ ∅` (`theorem_15_3_7_relative_hypotheses_halfSEP`; the bump
functions come from the partitions of unity of `halfSEP 1 1`). -/
theorem theorem_15_3_7_relative_of_bump_halfSEP :
    (halfSEP 1 1).X.PObj.boundary.Nonempty ∧
    (∀ y : (halfSEP 1 1).Obj, Nontrivial ((halfSEP 1 1).P ⁻¹' {y})) ∧
    (∃ x ∈ (halfSEP 1 1).X.PObj.boundary,
      0 < zeroMultisection (halfSEP 1 1) (halfDiscSection x)) ∧
    ∃ (N : (halfSEP 1 1).B.One → ℝ) (U : Set (halfSEP 1 1).Obj),
      ControlsCompactness (halfSEP 1 1) halfDiscSection N U ∧
      ∃ Λ' : (halfSEP 1 1).W → ℚ≥0, IsStructurable (halfSEP 1 1) Λ' ∧
        (∀ w, (halfSEP 1 1).P w ∈ (halfSEP 1 1).X.PObj.boundary →
          Λ' w = zeroMultisection (halfSEP 1 1) w) ∧
        domSupp Λ' ⊆ U ∧ (∀ x, pointwiseNorm N Λ' x < 1) ∧
        IsTransversal halfDiscSection Λ' ∧
        IsInGeneralPosition (halfSEP 1 1) halfDiscSection Λ' := by
  obtain ⟨hne, hfib, hsupp, hX, -, hPU, hf, hft, -, N, U, hcc, hc, hfun, hh, hΛ, hdom, hN, hgp⟩ :=
    theorem_15_3_7_relative_hypotheses_halfSEP
  exact ⟨hne, hfib, hsupp, N, U, hcc, theorem_15_3_7_relative_of_bump hX hPU.admitsBumpFunctions
    hf hft hcc hc hfun hh hΛ hdom hN hgp⟩

end HalfSpaceBundle

end Polyfold
