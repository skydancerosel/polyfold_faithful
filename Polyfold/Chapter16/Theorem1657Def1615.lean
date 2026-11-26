import Polyfold.Chapter7.ObjectPartitionsOfUnity
import Polyfold.Chapter16.PolyfoldBoundaryExtension
import Polyfold.Chapter16.PolyfoldBundleExamples
import Polyfold.Chapter16.IndexZeroInheritedCorrespondenceWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
**Theorem 16.5.7** (p. 735) under **Definition 16.1.5 (2)** (p. 708).

# Theorem 16.5.7 with "`Z` admits sc-smooth partitions of unity" as in Definition 16.1.5 (2)

Theorem 16.5.7 assumes that the polyfold `Z` admits sc-smooth partitions of unity, which by
Definition 16.1.5 (2) means that some model `(X, α) ∈ c` admits them as an ep-groupoid
(Definition 7.5.5: saturated covers, invariant partitions).  Its proof uses Theorem 14.1.9
(p. 646) in a model, which asks that the object space `X`, viewed as an M-polyfold, admit
sc-smooth partitions of unity (Definition 5.5.1).  The step between the two is
`EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity`
(`Chapter7/ObjectPartitionsOfUnity.lean`): an ep-groupoid with sc-smooth partitions of unity has
an object M-polyfold with sc-smooth partitions of unity.

## What is formalized

* `admitsScPartitionsOfUnity_models`: Definition 16.1.5 (2) gives sc-smooth partitions of unity
  of the object M-polyfold of every model `S ∈ c̄`; `admitsScPartitionsOfUnity_iff_models`, the
  two conditions are equivalent (the converse by Theorem 7.5.7).
* **`theorem_16_5_7_def_16_1_5`**: Theorem 16.5.7 with the hypothesis
  `c.polyfold.AdmitsScPartitionsOfUnity` (Definition 16.1.5 (2)), from `theorem_16_5_7`.
* `theorem_16_5_7_def_16_1_5_witness`: the hypotheses are jointly satisfiable over the tame
  polyfold `|ℤ/3 × ℝ ⇉ ℝ|` (non-trivial isotropy), with an auxiliary norm.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- **Definition 16.1.5 (2) in every model**: if the polyfold `Z` admits sc-smooth partitions of
unity (Definition 16.1.5 (2), p. 708), the object M-polyfold of every model `S ∈ c̄` admits
sc-smooth partitions of unity (Definition 5.5.1): Proposition 16.1.4 (2) carries Definition 7.5.5
to every model, and `admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity` passes to the objects. -/
theorem admitsScPartitionsOfUnity_models (hPU : c.polyfold.AdmitsScPartitionsOfUnity) :
    ∀ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c → S.A.X.PObj.AdmitsScPartitionsOfUnity :=
  fun S hS => EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity
    ((PolyfoldClass.definition_16_1_5_two c.polyfold).1 hPU S.toPolyfoldStructure
      (by rw [← hS]; rfl))

/-- **Definition 16.1.5 (2) and the condition on the object M-polyfolds of the models agree**:
`Z` admits sc-smooth partitions of unity iff the object M-polyfold of every model `S ∈ c̄`
does (the converse by Theorem 7.5.7, p. 342, in one model). -/
theorem admitsScPartitionsOfUnity_iff_models :
    c.polyfold.AdmitsScPartitionsOfUnity ↔
      ∀ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c → S.A.X.PObj.AdmitsScPartitionsOfUnity := by
  refine ⟨admitsScPartitionsOfUnity_models, fun h => ?_⟩
  obtain ⟨S, hS⟩ := Quotient.exists_rep c
  exact ⟨S.toPolyfoldStructure, by rw [← hS]; rfl, S.A.X.theorem_7_5_7 S.paracompact (h S hS)⟩

/-- **2021 Theorem 16.5.7, p. 735**, with "`Z` admits sc-smooth partitions of unity" read as
Definition 16.1.5 (2), p. 708 (`c.polyfold.AdmitsScPartitionsOfUnity`: some model admits them as
an ep-groupoid, Definition 7.5.5): over a tame polyfold `Z`, with an auxiliary norm `n`, a
structurable sc⁺-multisection `λ` over `∂Z`, an open `Ũ ⊇ dom-supp(λ)` and a continuous
`f ≥ 0` with `tsupport f ⊆ Ũ` and `n(λ) < f` on `dom-supp(λ)`, there is a structurable
sc⁺-multisection `λ'` with (1) `n(λ') ≤ f`, (2) `dom-supp(λ') ⊆ Ũ`, (3) `λ' = λ` over `∂Z`. -/
theorem theorem_16_5_7_def_16_1_5 (hc : c.IsTame) (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    {n : Y → ℝ} (hn : c.IsAuxNorm n) (s : BoundaryMultisection c) (hs : s.IsStructurable)
    {U : Set Z} (hU : IsOpen U) (hdom : s.domSupp ⊆ U) {f : Z → ℝ} (hf : Continuous f)
    (hf0 : ∀ z, 0 ≤ f z) (hfU : tsupport f ⊆ U)
    (hlt : ∀ z ∈ s.domSupp, c.normLam n s.toFun z < f z) :
    ∃ t : ScPlusMultisection c, t.IsStructurable ∧ (∀ z, c.normLam n t.toFun z ≤ f z) ∧
      t.domSupp ⊆ U ∧ ∀ y, p y ∈ c.polyfold.boundary → t.toFun y = s.toFun y :=
  theorem_16_5_7 hc (admitsScPartitionsOfUnity_models hPU) hn s hs hU hdom hf hf0 hfU hlt

/-- **The hypotheses of `theorem_16_5_7_def_16_1_5` are jointly satisfiable**: the polyfold
`|ℤ/3 × ℝ ⇉ ℝ|` of `z3Bundle 1` (isotropy `ℤ/3`) is tame and admits sc-smooth partitions of
unity (Definition 16.1.5 (2)), it carries an auxiliary norm, and the zero multisection over
`∂Z`, `Ũ = ∅` and `f = 0` meet the conditions on `λ, Ũ, f`. -/
theorem theorem_16_5_7_def_16_1_5_witness :
    (z3Bundle 1).IsTame ∧ (z3Bundle 1).polyfold.AdmitsScPartitionsOfUnity ∧
      ∃ n, (z3Bundle 1).IsAuxNorm n ∧
        ∃ (s : BoundaryMultisection (z3Bundle 1)) (U : Set _) (f : _ → ℝ), s.IsStructurable ∧
          IsOpen U ∧ s.domSupp ⊆ U ∧ Continuous f ∧ (∀ z, 0 ≤ f z) ∧ tsupport f ⊆ U ∧
          ∀ z ∈ s.domSupp, (z3Bundle 1).normLam n s.toFun z < f z := by
  obtain ⟨n, hn⟩ := z3Bundle_exists_auxNorm 1
  obtain ⟨s, hs, hd, ht, hlt⟩ := theorem_16_5_7_hyp_witness (n := n) (z3Bundle_isTame 1)
  exact ⟨z3Bundle_isTame 1, StrongBundleLocalizationExamples.z3Bundle_admitsScPartitionsOfUnity,
    n, hn, s, ∅, fun _ => 0, hs, isOpen_empty, hd, continuous_const, fun _ => le_rfl, ht, hlt⟩

end StrongPolyfoldBundle

end Polyfold
