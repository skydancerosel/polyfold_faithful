import Polyfold.Chapter12.OrientationGeneralizedIsoOrbitMap
import Polyfold.Chapter12.OrientationGeneralizedIsoExample

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
p. 595, **Theorem 12.5.7** (2017: Theorem 12.12), with **Remark 10.5.5** (p. 508): two
different generalized strong bundle isomorphisms with the same map of orbit spaces induce the
same map of orientations, in an example.

## The example

`W = ℝ × ℝᵏ → ℝ` over `ℤ/3 × ℝ ⇉ ℝ` with the trivial actions (`z3SEP k`, Remark 10.5.5): the
base is not effective, the bundle has the local regularity property
(`isLRLocal_z3EpBundle`), and `[1_W] ≠ [Inv]` although `|[1_W]| = |[Inv]|`
(`remark_10_5_5`).  For the graph section `f` of a `C^∞` map `φ : ℝ → ℝᵏ`:

* `isScFredholmSectionFunctor_graphSection_z3`: `f` is an sc-Fredholm section functor.
* **`orbitOrMap_inv_eq_orbitOrMap_id`**: `[Inv]_* f = [1]_* f = f`, the two classes differ, and
  `|[Inv]|_* = |[1]|_*` on `|O_f|` (`GenSBMap.orbitOrMap_eq_of_orbitMap_eq`).  The fibres are
  non-zero for `k ≥ 1` (`nontrivial_fibre_z3SEP`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

open scoped ContDiff

noncomputable section

namespace Polyfold

namespace StrongBundleLocalizationExamples

open SBLocalization StrongBundleEquivalenceExamples TrivialBundle EpStrongBundle
open LocalizationLRBundleBaseExamples

variable {k : ℕ} {φ : (Fin 1 → ℝ) → (Fin k → ℝ)}

/-- **The graph section of a `C^∞` map is an sc-Fredholm section functor** of `ℝ × ℝᵏ → ℝ` over
`ℤ/3 × ℝ ⇉ ℝ` (the action on the fibres is trivial). -/
theorem isScFredholmSectionFunctor_graphSection_z3 (hφ : ContDiff ℝ ∞ φ) :
    (z3SEP k).E.IsScFredholmSectionFunctor (graphSection φ) := by
  obtain ⟨⟨hs, -⟩, hfred⟩ := graphSection_mem_fredholmSectionFunctors_epBundle (n := 1) hφ
  exact ⟨⟨hs, fun _ => rfl⟩, hfred⟩

/-- For `k ≥ 1` every fibre of `ℝ × ℝᵏ → ℝ` is a non-zero vector space. -/
theorem nontrivial_fibre_z3SEP [NeZero k] (y : (z3SEP k).Obj) :
    Nontrivial ((z3SEP k).P ⁻¹' {y}) :=
  (TrivialBundle.fibEquiv (n := 1) (k := k) y).nontrivial

/-- **Two different generalized strong bundle isomorphisms with the same map of orientations**:
on `W = ℝ × ℝᵏ → ℝ` over `ℤ/3 × ℝ ⇉ ℝ` (not effective, with the local regularity property) the
classes `[Inv]` and `[1_W]` differ, both push the graph section `f` of a `C^∞` map to `f`, and
`|[Inv]|_* = |[1_W]|_*` on `|O_f|`. -/
theorem orbitOrMap_inv_eq_orbitOrMap_id (hφ : ContDiff ℝ ∞ φ) :
    ∃ (hF : (z3SEP k).E.IsScFredholmSectionFunctor (graphSection φ))
      (hsec : (z3SEP k).B.HasScPlusSectionsThrough)
      (hInv : (SDiagram.ofHom (z3InvHom k)).cls.IsGeneralizedIso)
      (hId : (SDiagram.id (z3SEP k)).cls.IsGeneralizedIso)
      (h₁ : graphSection φ = GenSBMap.pushforward hInv (graphSection φ))
      (h₂ : graphSection φ = GenSBMap.pushforward hId (graphSection φ)),
      (SDiagram.ofHom (z3InvHom k)).cls ≠ (SDiagram.id (z3SEP k)).cls ∧
      (SDiagram.ofHom (z3InvHom k)).cls.orbitMap = (SDiagram.id (z3SEP k)).cls.orbitMap ∧
      (z3SEP k).E.IsLRLocal ∧
      GenSBMap.orbitOrMap hInv hF hF h₁ hsec hsec = GenSBMap.orbitOrMap hId hF hF h₂ hsec hsec := by
  have hF := isScFredholmSectionFunctor_graphSection_z3 (k := k) hφ
  have hsec : (z3SEP k).B.HasScPlusSectionsThrough := hasScPlusSectionsThrough_epSEP 1 k
  obtain ⟨hInv, hId, horb, -, hne⟩ := remark_10_5_5 k
  have h₂ : graphSection φ = GenSBMap.pushforward hId (graphSection φ) :=
    ((GenSBMap.pushforward_eq hId rfl (SEP.equivalences.id_mem _) hF.1).trans
      (SDiagram.pushforward_id _ hF.1)).symm
  have h₁ : graphSection φ = GenSBMap.pushforward hInv (graphSection φ) :=
    h₂.trans (pushforward_inv_eq_pushforward_id k hInv hId hF.1).symm
  exact ⟨hF, hsec, hInv, hId, h₁, h₂, hne, horb, isLRLocal_z3EpBundle k,
    GenSBMap.orbitOrMap_eq_of_orbitMap_eq hInv hId hF hF h₁ h₂ hsec hsec horb
      (isLRLocal_z3EpBundle k)⟩

end StrongBundleLocalizationExamples

end Polyfold
