import Polyfold.Chapter14.BoundaryCommensurableSum
import Polyfold.Chapter14.HalfSpaceConstSection

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.5, Lemma 14.5.2
(p. 672): **a witness with non-empty boundary and non-zero fibres** on the half-space bundle
`H × ℝᵏ → H`, `H = [0, ∞) × ℝᵐ`.

# The commensurable sum over the boundary of the half-space

For `v ≠ 0` the constant section `x ↦ (x, v)` gives a structured sc⁺-multisection `Λ_v` over
`∂H` with `dom-supp(Λ_v) ≠ ∅` (`HalfSpaceBundle.constMulti`).  With the two functors
`β₁ = β₂ = 1/2` (locally finite, `β₁ + β₂ = 1`), the hypotheses of `lemma_14_5_2` hold, the
family `(β_a ⊙ Λ_v)` is locally finite over `∂H`, and its commensurable sum has the class of
`Λ_v` (`lemma_14_5_2_witness`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

namespace HalfSpaceBundle

open SBLocalization StrongBundle EpGroupoid

variable {m k : ℕ}

/-- **Lemma 14.5.2 on the half-space bundle**: for `v ≠ 0` there is a structured tuple `T` over
`∂H` with functor `Λ_v` and non-empty `dom-supp`, the family `(β_a ⊙ Λ_v)_{a ∈ Fin 2}` with
`β_a ≡ 1/2` is locally finite over `∂H`, and its commensurable sum over the data of `T` has the
sections of `T`, the functor `Λ_v` over `∂H`, and the class of `T`. -/
theorem lemma_14_5_2_witness {v : Fin k → ℝ} (hv : v ≠ 0) :
    ∃ T : BoundaryStructuredTuple (halfSEP m k), T.Λ = constMulti v ∧
      (boundaryDomSupp T.Λ).Nonempty ∧
      ∃ hlfΛ : BoundaryCommData.IsLocallyFiniteBoundaryFamily
          (fun _ : Fin 2 => multisectionSmulFun (fun _ => (2 : ℝ)⁻¹) T.Λ),
        (∀ w, (halfSEP m k).P w ∈ (halfSEP m k).X.PObj.boundary →
          BoundaryCommData.lfSum (fun _ : Fin 2 => BoundaryCommData.smulOver T
            (β := fun _ => (2 : ℝ)⁻¹) (fun _ => rfl) (isScSmoothMap_real_const _)) hlfΛ w =
            constMulti v w) ∧
        BoundaryStructuredTuple.Equiv
          (BoundaryCommData.Over.lfSum (fun _ : Fin 2 => BoundaryCommData.smulOver T
            (β := fun _ => (2 : ℝ)⁻¹) (fun _ => rfl) (isScSmoothMap_real_const _)) hlfΛ).toTuple
          T := by
  obtain ⟨T, hT⟩ := isBoundaryStructurable_iff.1 (isBoundaryStructurable_constMulti (m := m) v)
  have hsum : ∀ y ∈ (halfSEP m k).X.PObj.boundary, ∑ᶠ _ : Fin 2, (2 : ℝ)⁻¹ = 1 := fun _ _ => by
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  obtain ⟨hlfΛ, -, hmult, hequiv⟩ := BoundaryCommData.lemma_14_5_2 T (fun (_ : Fin 2) _ =>
    (2 : ℝ)⁻¹) (fun _ _ => rfl) (fun _ => isScSmoothMap_real_const _)
    (fun y => ⟨univ, isOpen_univ, mem_univ y, toFinite _⟩) hsum
  refine ⟨T, hT, hT ▸ boundaryDomSupp_constMulti_nonempty hv, hlfΛ,
    fun w hw => (hmult w hw).trans (by rw [hT]), hequiv⟩

end HalfSpaceBundle

end Polyfold
