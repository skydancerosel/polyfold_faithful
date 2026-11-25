import Polyfold.Examples.Classical.Main
import Polyfold.Examples.Classical.CyclicData

/-!
# The classical reduction: `z ↦ z^k` and `z ↦ z̄^k` on `ℂ/ℤₚ`

Theorem 16.6.6, 2021 p. 739 (index `0`), for `G = ℤ/p` acting on `ℂ` with weight `1` and the
sections `z ↦ z^k` (fibre weight `k`) and `z ↦ z̄^k` (fibre weight `−k`) of `|ℂ × ℂ| → ℂ/ℤₚ`,
`k ≥ 1`: combining `count_eq_classicalCount` with the classical counts of `CyclicData`.

## What is formalized (namespace `Polyfold.Examples.Classical.Cyclic`)

* **`count_powMap`**: for `z ↦ z^k` an admissible perturbed solution set with the canonical
  orientation and `Q.t = tG (σk p k) (c₀ p k)` exists, and every admissible `Q` with the
  canonical orientation has `Q.count 1 = k / p`.
* **`count_pow_two_five`**: for `z ↦ z²` on `ℂ/ℤ₅` the count is `2/5`.
* **`count_conjPowMap`**: the same for `z ↦ z̄^k`, with count `−k / p`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function

noncomputable section

namespace Polyfold.Examples.Classical.Cyclic

open StrongPolyfoldBundle PolyfoldClass

variable {p : ℕ} [NeZero p] {k : ℕ}

/-- **`z ↦ z^k` on `ℂ/ℤₚ`** (Theorem 16.6.6, 2021 p. 739, index `0`): an admissible perturbed
solution set with the canonical orientation exists, and every such `Q` has
`Q.count 1 = k / p`. -/
theorem count_powMap (hk : 0 < k) :
    (∃ Q : PointOrientedPerturbation
        (clFredholmSection (σk p k) (contDiff_powMap k) (powMap_smul p k)).1,
      Q.t = tG (σk p k) (c₀ p k) ∧
      Q.IsAdmissible (nG (σk p k)) (univ : Set (AG (σk p k)).X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet
        (clOrientationRep (σk p k) (contDiff_powMap k) (powMap_smul p k) (hdet_σk p k)) Q) ∧
    ∀ Q : PointOrientedPerturbation
        (clFredholmSection (σk p k) (contDiff_powMap k) (powMap_smul p k)).1,
      Q.IsAdmissible (nG (σk p k)) (univ : Set (AG (σk p k)).X.OrbitSpace) →
      IsCanonicalPointSolutionSet
        (clOrientationRep (σk p k) (contDiff_powMap k) (powMap_smul p k) (hdet_σk p k)) Q →
      Q.count (clOne (σk p k)) = (k : ℝ) / p := by
  obtain ⟨-, hex, hall⟩ := count_eq_classicalCount (σk p k) (hdet_σk p k) (contDiff_powMap k)
    (powMap_smul p k) (isCompact_preimage_powMap hk) (surjective_fderiv_powMap hk)
    (gNorm_σk_c₀ p k).le
  exact ⟨hex, fun Q hQ hcan => (hall Q hQ hcan).trans (classicalCount_powMap hk)⟩

/-- **`z ↦ z²` on `ℂ/ℤ₅`**: every admissible perturbed solution set with the canonical
orientation has `Q.count 1 = 2/5`. -/
theorem count_pow_two_five
    (Q : PointOrientedPerturbation
      (clFredholmSection (σk 5 2) (contDiff_powMap 2) (powMap_smul 5 2)).1)
    (hQ : Q.IsAdmissible (nG (σk 5 2)) (univ : Set (AG (σk 5 2)).X.OrbitSpace))
    (hcan : IsCanonicalPointSolutionSet
      (clOrientationRep (σk 5 2) (contDiff_powMap 2) (powMap_smul 5 2) (hdet_σk 5 2)) Q) :
    Q.count (clOne (σk 5 2)) = 2 / 5 := by
  rw [(count_powMap (p := 5) (k := 2) (by norm_num)).2 Q hQ hcan]
  norm_num

/-- **`z ↦ z̄^k` on `ℂ/ℤₚ`**, fibre weight `−k` (Theorem 16.6.6, 2021 p. 739, index `0`): an
admissible perturbed solution set with the canonical orientation exists, and every such `Q` has
`Q.count 1 = −k / p`. -/
theorem count_conjPowMap (hk : 0 < k) :
    (∃ Q : PointOrientedPerturbation
        (clFredholmSection (σnk p k) (contDiff_conjPowMap k) (conjPowMap_smul p k)).1,
      Q.t = tG (σnk p k) (c₀ p k) ∧
      Q.IsAdmissible (nG (σnk p k)) (univ : Set (AG (σnk p k)).X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet
        (clOrientationRep (σnk p k) (contDiff_conjPowMap k) (conjPowMap_smul p k)
          (hdet_σnk p k)) Q) ∧
    ∀ Q : PointOrientedPerturbation
        (clFredholmSection (σnk p k) (contDiff_conjPowMap k) (conjPowMap_smul p k)).1,
      Q.IsAdmissible (nG (σnk p k)) (univ : Set (AG (σnk p k)).X.OrbitSpace) →
      IsCanonicalPointSolutionSet
        (clOrientationRep (σnk p k) (contDiff_conjPowMap k) (conjPowMap_smul p k)
          (hdet_σnk p k)) Q →
      Q.count (clOne (σnk p k)) = -((k : ℝ) / p) := by
  obtain ⟨-, hex, hall⟩ := count_eq_classicalCount (σnk p k) (hdet_σnk p k)
    (contDiff_conjPowMap k) (conjPowMap_smul p k) (isCompact_preimage_conjPowMap hk)
    (surjective_fderiv_conjPowMap hk) (gNorm_σnk_c₀ p k).le
  exact ⟨hex, fun Q hQ hcan => (hall Q hQ hcan).trans (classicalCount_conjPowMap hk)⟩

end Polyfold.Examples.Classical.Cyclic
