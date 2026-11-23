import Polyfold.Chapter15.RestrictedBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, **Definition
15.3.1** (p. 691) and the hypotheses on `Λ` in **Theorem 15.4.3** (p. 702), on the restriction
`W|V → X|V` of a strong bundle to a saturated open set `V` (Proposition 7.1.22, p. 250).

# Controlling pairs and transversal perturbations restrict to saturated open sets

## The text, paraphrased

(Definition 15.3.1) `(N, U)` controls the compactness of `f` if `N` is an auxiliary norm, `U` a
saturated open neighbourhood of `S_f`, and the orbit space of `{x ∈ U | N(f(x)) ≤ 1}` has compact
closure in `|X|`.

## What is formalized (namespace `Polyfold.SBLocalization`)

For `V` open and saturated in `X`:

* `isOpenEmbedding_orbitMap_restr`: `|X|V| → |X|` is an open embedding.
* **`controlsCompactness_restr`**: if `(N, U)` controls the compactness of `f` and
  `π⁻¹(cl |{x ∈ U | N(f(x)) ≤ 1}|) ⊆ V`, then `(N|V, U ∩ V)` controls the compactness of `f|V`.
* **`isTransversalPerturbation_restr`**: under the same inclusion a transversal perturbation
  `(N, U, Λ)` of `f` restricts to a transversal perturbation `(N|V, U ∩ V, Λ|V)` of `f|V`.

## Reading

The closure in Definition 15.3.1 for `f|V` is taken in `|X|V|`, which is the open subset `π(V)`
of `|X|`; the inclusion hypothesis keeps the closure taken in `|X|` inside `π(V)`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold SEP

variable {A : SEP.{u}} {V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V)

/-- `|X|V| → |X|` is injective: a morphism of `X` between points of `V` is a morphism of
`X|V`. -/
theorem injective_orbitMap_restr : Injective (A.baseEP.subFunctor hV).orbitMap := by
  intro p q hpq
  obtain ⟨a, rfl⟩ := (A.restr hV).X.surjective_π p
  obtain ⟨b, rfl⟩ := (A.restr hV).X.surjective_π q
  obtain ⟨φ, hs, ht⟩ := A.X.π_eq_π_iff.1 hpq
  have hφ : φ ∈ A.X.morOn V := ⟨hs ▸ restrBase_mem hV a, ht ▸ restrBase_mem hV b⟩
  exact (A.restr hV).X.π_eq_π_iff.2 ⟨(⟨φ, hφ⟩ : A.X.morOn V),
    restrBase_injective hV hs, restrBase_injective hV ht⟩

/-- **`|X|V| → |X|` is an open embedding** for `V` open. -/
theorem isOpenEmbedding_orbitMap_restr (hVo : IsOpen V) :
    IsOpenEmbedding (A.baseEP.subFunctor hV).orbitMap :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (A.baseEP.subFunctor hV).continuous_orbitMap (injective_orbitMap_restr hV)
    ((A.baseEP.subFunctor hV).isOpenMap_orbitMap hVo.isOpenEmbedding_subtypeVal.isOpenMap)

/-- The preimage in `X|V` of a saturated set is saturated. -/
theorem isSaturated_preimage_restrBase {U : Set A.Obj} (hU : A.X.IsSaturated U) :
    (A.restr hV).X.IsSaturated (restrBase hV ⁻¹' U) := by
  refine (A.restr hV).X.isSaturated_iff.2 fun φ hφ => ?_
  have h := A.X.isSaturated_iff.1 hU ((A.baseEP.subFunctor hV).mor φ)
  have hs : A.X.src ((A.baseEP.subFunctor hV).mor φ) = restrBase hV ((A.restr hV).X.src φ) :=
    (A.baseEP.subFunctor hV).src_mor φ
  have ht : A.X.tgt ((A.baseEP.subFunctor hV).mor φ) = restrBase hV ((A.restr hV).X.tgt φ) :=
    (A.baseEP.subFunctor hV).tgt_mor φ
  rw [hs, ht] at h
  exact h hφ

/-- **Definition 15.3.1 restricts to a saturated open set containing the controlled set**: if
`(N, U)` controls the compactness of `f` and `π⁻¹(cl |{x ∈ U | N(f(x)) ≤ 1}|) ⊆ V`, then
`(N|V, U ∩ V)` controls the compactness of `f|V`. -/
theorem controlsCompactness_restr (hVo : IsOpen V) {f : A.Obj → A.W} (hf : IsSection A.P f)
    {N : A.B.One → ℝ} {U : Set A.Obj} (h : ControlsCompactness A f N U)
    (hK : A.X.π ⁻¹' closure (A.X.π '' {x ∈ U | A.B.AuxLe N (f x) 1}) ⊆ V) :
    ControlsCompactness (A.restr hV) (restrSec hV f hf) (restrNorm hV N)
      (restrBase hV ⁻¹' U) := by
  obtain ⟨hN, hUo, hUs, hSU, hC⟩ := h
  refine ⟨isAuxNorm_restrNorm hV hN, hUo.preimage (continuous_restrBase hV),
    isSaturated_preimage_restrBase hV hUs, ?_, ?_⟩
  · rw [solutionSet_restrSec]
    exact preimage_mono hSU
  · set K := closure (A.X.π '' {x ∈ U | A.B.AuxLe N (f x) 1}) with hKdef
    have hemb := isOpenEmbedding_orbitMap_restr hV hVo
    have hrange : K ⊆ range (A.baseEP.subFunctor hV).orbitMap := by
      intro p hp
      obtain ⟨x, rfl⟩ := A.X.surjective_π p
      exact ⟨(A.restr hV).X.π (⟨x, hK hp⟩ : V), rfl⟩
    have hpre : IsCompact ((A.baseEP.subFunctor hV).orbitMap ⁻¹' K) :=
      (hemb.isInducing.isCompact_preimage_iff hrange).2 hC
    have hcl : IsClosed ((A.baseEP.subFunctor hV).orbitMap ⁻¹' K) :=
      isClosed_closure.preimage hemb.continuous
    refine hpre.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcl)
    rintro _ ⟨a, ⟨haU, hle⟩, rfl⟩
    exact subset_closure ⟨restrBase hV a, ⟨haU, (auxLe_restrNorm_iff hV _).1 hle⟩, rfl⟩

/-- **A transversal perturbation restricts to a saturated open set containing the controlled
set** (the hypotheses on `Λ` in Theorem 15.4.3, p. 702): if `(N, U, Λ)` is a transversal
perturbation of the sc-Fredholm section functor `f` and
`π⁻¹(cl |{x ∈ U | N(f(x)) ≤ 1}|) ⊆ V`, then `(N|V, U ∩ V, Λ|V)` is a transversal perturbation of
`f|V`. -/
theorem isTransversalPerturbation_restr (hVo : IsOpen V) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) {N : A.B.One → ℝ} {U : Set A.Obj} {Λ : A.W → ℚ≥0}
    (h : IsTransversalPerturbation A f N U Λ)
    (hK : A.X.π ⁻¹' closure (A.X.π '' {x ∈ U | A.B.AuxLe N (f x) 1}) ⊆ V) :
    IsTransversalPerturbation (A.restr hV) (restrSec hV f hf.1.1.1) (restrNorm hV N)
      (restrBase hV ⁻¹' U) (restrMult hV Λ) :=
  ⟨controlsCompactness_restr hV hVo hf.1.1.1 h.1 hK,
    isScPlusMultisection_restrMult hV hVo h.2.1, domSupp_restrMult_subset hV h.2.2.1,
    fun a => (pointwiseNorm_restrMult hV N Λ a).le.trans (h.2.2.2.1 _),
    isTransversal_restr hV hVo hf h.2.1 h.2.2.2.2⟩

/-- The set `U ∩ V` of the restricted pair, as a subset of the subtype `V`. -/
theorem restrBase_preimage (U : Set A.Obj) :
    restrBase hV ⁻¹' U = (Subtype.val ⁻¹' U : Set V) := rfl

end SBLocalization

end Polyfold
