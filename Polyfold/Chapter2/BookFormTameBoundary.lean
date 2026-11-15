import Polyfold.Chapter2.TameBoundaryNonCentred

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, Appendix §2.7.4:
**Proposition 2.7.12** (p. 83), **Theorem 2.7.13** with the characterization after it and
**Definition 2.7.14** (pp. 83–84), all new in the 2021 edition, each in one statement.

# The tame boundary `bX` in book form

## The text, paraphrased

(Proposition 2.7.12) For any two representatives `(x, V, θ)`, `(x', V', θ')`, the images of
`U(x, V, θ) ∩ U(x', V', θ')` under `Φ_{(x,V,θ)}` and `Φ_{(x',V',θ')}` are open in `θ` and `θ'`, and
the transition map `Φ_{(x',V',θ')} ∘ Φ_{(x,V,θ)}⁻¹` between them is an sc-diffeomorphism.
(Theorem 2.7.13) For a tame `X`: (1) `bX` has a natural metrizable topology; (2) a natural tame
M-polyfold structure; (3) `B : bX → X` is sc-smooth; (4) `d_X(B(p)) − 1 = d_{bX}(p)`.  The topology
and the structure are characterized by: for every class and every representative, `U(x, V, θ)` is
open and `Φ_{(x,V,θ)} : U(x, V, θ) → θ` is a homeomorphism and an sc-diffeomorphism, `θ` with the
structure induced from `V`.  (Definition 2.7.14) The tame boundary is the diagram `B : bX → X`,
with image `∂X`.

## What is formalized

* `MPolyfold.proposition_2_7_12_book`: Proposition 2.7.12 as printed, for every pair of
  representatives (`proposition_2_7_12_scDiffeo_nonCentred`).
* `MPolyfold.theorem_2_7_13_book`: (1)–(4), the characterization, the uniqueness of the topology
  and of the M-polyfold structure, and Definition 2.7.14's `range B = ∂X`, in one statement,
  assembled from `theorem_2_7_13` (topology), `theorem_2_7_13_structure`,
  `phi_isScDiffeoOn_nonCentred`, `tameBoundaryPolyfold_unique_allReps` and
  `range_tameBoundaryMap`.

## The reading

* **"Onto `θ`" for every representative** does not hold as we read it (`not_surjOn_phiTot`, row
  V2.105): the image of `Φ_{(x,V,θ)}` is the open subset `θ ∩ V^x` of `θ` (`reachSet`).  The book
  form states the characterization as: for every representative, `U(x, V, θ)` is open,
  `Φ_{(x,V,θ)}` is an open embedding (a homeomorphism onto its image) and an sc-diffeomorphism onto
  `θ ∩ V^x`; for `V` centred at `x`, `Φ_{(x,V,θ)}` is a bijection onto `θ` and `θ ∩ V^x = θ`, which
  is the printed statement.
* "Uniquely characterized" is read as: a topology for which every `U(x, V, θ)` is open and every
  `Φ` is an open map into `θ` is `T_{bX}`; an M-polyfold structure on `(bX, T_{bX})` for which
  every `Φ` is an sc-diffeomorphism onto `θ ∩ V^x` has an atlas equivalent to ours.  Both
  hypotheses are satisfied by `T_{bX}` and `tameBoundaryPolyfold` themselves (the first and third
  conjuncts of the characterization).
-/

open Set Function Topology

noncomputable section

namespace Polyfold

namespace MPolyfold

open TameBoundary TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **2021 Proposition 2.7.12, p. 83** (new in the 2021 edition), as printed, for every pair of
representatives `(x, V, θ)`, `(x', V', θ')`, centred or not: `Φ_{(x,V,θ)}(U ∩ U')` is open in `θ`,
`Φ_{(x',V',θ')}(U ∩ U')` is open in `θ'`, and the transition map `Φ_{(x',V',θ')} ∘ Φ_{(x,V,θ)}⁻¹`
between them is an sc-diffeomorphism (the faces carrying their sub-M-polyfold structures), the
identity on the underlying points of `X`.  This is `proposition_2_7_12_scDiffeo_nonCentred`. -/
theorem proposition_2_7_12_book (hP : P.IsTame) (t t' : BTriple (P.isCornerIndex_degIndex hP)) :
    letI := P.paracompactSpace_subtype t.θ
    letI := P.paracompactSpace_subtype t'.θ
    IsOpen {y : t.θ | (y : X) ∈ bMap _ '' (uSet _ t ∩ uSet _ t')} ∧
      IsOpen {y : t'.θ | (y : X) ∈ bMap _ '' (uSet _ t ∩ uSet _ t')} ∧
      (P.facePolyfold hP t.mem.1.1 t.mem_faces.1).IsScDiffeoOn
        (P.facePolyfold hP t'.mem.1.1 t'.mem_faces.1)
        (P.phiTot hP t' ∘ phiInv _ t) (P.phiTot hP t ∘ phiInv _ t')
        {y : t.θ | (y : X) ∈ bMap _ '' (uSet _ t ∩ uSet _ t')}
        {y : t'.θ | (y : X) ∈ bMap _ '' (uSet _ t ∩ uSet _ t')} ∧
      ∀ y : t.θ, (y : X) ∈ bMap _ '' (uSet _ t ∩ uSet _ t') →
        ((P.phiTot hP t' (phiInv _ t y) : t'.θ) : X) = y :=
  P.proposition_2_7_12_scDiffeo_nonCentred hP t t'

/-- **2021 Theorem 2.7.13, pp. 83–84, with the characterization after it and Definition 2.7.14**
(new in the 2021 edition), in book form, for a tame M-polyfold `X`:
(1) `bX` carries the metrizable topology `T_{bX}`;
(2) `bX` carries the tame M-polyfold structure `tameBoundaryPolyfold`;
(3) `B : bX → X` is sc-smooth;
(4) `d_X(B(p)) − 1 = d_{bX}(p)`;
the characterization: for every representative `(x, V, θ)`, `U(x, V, θ)` is open,
`Φ_{(x,V,θ)}` is an open embedding into `θ` and an sc-diffeomorphism of `U(x, V, θ)` onto the
open set `θ ∩ V^x`
(inverse `phiInv`); for `V` centred at `x`, `Φ_{(x,V,θ)}` is a bijection onto `θ` and `θ ∩ V^x = θ`;
`T_{bX}` is the only topology for which every `U(x, V, θ)` is open and every `Φ` is open into `θ`,
and every M-polyfold structure on `bX` for which every `Φ` is an sc-diffeomorphism onto
`θ ∩ V^x` is equivalent to `tameBoundaryPolyfold`; and (Definition 2.7.14) `B` has image `∂X`.
"Onto `θ`" for non-centred `V` does not hold as we read it (`not_surjOn_phiTot`). -/
theorem theorem_2_7_13_book (hP : P.IsTame) :
    MetrizableSpace (P.TameBoundarySpace hP) ∧
      (P.tameBoundaryPolyfold hP).IsTame ∧
      (P.tameBoundaryPolyfold hP).IsScSmoothMap P (P.tameBoundaryMap hP) ∧
      (∀ p, P.degIndex (P.tameBoundaryMap hP p) - 1 = (P.tameBoundaryPolyfold hP).degIndex p) ∧
      (∀ t : BTriple (P.isCornerIndex_degIndex hP),
        IsOpen (uSet _ t) ∧ IsOpenEmbedding (phi _ t) ∧
          letI := P.paracompactSpace_subtype t.θ
          (P.tameBoundaryPolyfold hP).IsScDiffeoOn (P.facePolyfold hP t.mem.1.1 t.mem_faces.1)
            (P.phiTot hP t) (phiInv _ t) (uSet _ t) (P.reachSet hP t)) ∧
      (∀ t : BTriple (P.isCornerIndex_degIndex hP), IsCenteredAt P.degIndex t.x t.V →
        Bijective (phi _ t) ∧ P.reachSet hP t = univ) ∧
      (∀ τ : TopologicalSpace (P.TameBoundarySpace hP),
        (∀ t, IsOpen[τ] (uSet (P.isCornerIndex_degIndex hP) t)) →
          (∀ t U, IsOpen[τ] U → ∃ N, IsOpen N ∧
            bMap (P.isCornerIndex_degIndex hP) '' (U ∩ uSet _ t) = N ∩ t.θ) →
            τ = bTopology (P.isCornerIndex_degIndex hP)) ∧
      (∀ Q' : MPolyfold (P.TameBoundarySpace hP),
        (∀ t : BTriple (P.isCornerIndex_degIndex hP),
          letI := P.paracompactSpace_subtype t.θ
          Q'.IsScDiffeoOn (P.facePolyfold hP t.mem.1.1 t.mem_faces.1) (P.phiTot hP t)
            (phiInv _ t) (uSet _ t) (P.reachSet hP t)) →
          Q'.atlas.Equiv (P.tameBoundaryPolyfold hP).atlas) ∧
      range (P.tameBoundaryMap hP) = P.boundary := by
  obtain ⟨hmet, hopen, hemb, huniq, -⟩ := P.theorem_2_7_13 hP
  obtain ⟨htame, hsmooth, hdeg, -⟩ := P.theorem_2_7_13_structure hP
  exact ⟨hmet, htame, hsmooth, hdeg,
    fun t => ⟨hopen t, hemb t, P.phi_isScDiffeoOn_nonCentred hP t⟩,
    fun t ht => ⟨phi_bijective_of_isCenteredAt _ ht, P.reachSet_eq_univ_of_isCenteredAt hP ht⟩,
    huniq, fun Q' h => P.tameBoundaryPolyfold_unique_allReps hP Q' h,
    P.range_tameBoundaryMap hP⟩

end MPolyfold

end Polyfold
