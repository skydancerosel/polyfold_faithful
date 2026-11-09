import Polyfold.Chapter7.TameBoundaryEpStructure
import Polyfold.Chapter2.TameBoundaryNonCentred

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 7,
Appendix §7.6.5.2 "The Case of Tame Ep-Groupoids": **Theorem 7.6.9** (p. 355) and the
characterization after it, for every representative (new in the 2021 edition; there is no 2017
counterpart).  Numbers and pages are the 2021 text's.

# Theorem 7.6.9 with the characterization for every representative

## The text, paraphrased

(Theorem 7.6.9, p. 355) For a tame ep-groupoid `(X, 𝐗)`: (1) `bX` and `b𝐗` carry natural
metrizable topologies; (2) natural tame M-polyfold structures; (3) both maps `B` are sc-smooth;
(4) `d_X(B(p)) − 1 = d_{bX}(p)`, and likewise on `b𝐗`; (5) `(bX, b𝐗)` with `s, t, u, ι, m` is a
tame ep-groupoid.  The topology and the structure of `bX` and `b𝐗` are characterized as in
Theorem 2.7.13.

## What is formalized

`theorem_7_6_9_full_2021` (`TameBoundaryEpStructure.lean`) states the characterization and its
uniqueness for representatives `(x, V, θ)` whose `V` is centred at `x` (V7.101).  Part I has both
for every representative (`MPolyfold.phi_isScDiffeoOn_nonCentred_2021`,
`MPolyfold.tameBoundaryPolyfold_unique_allReps_2021`; gap G.78, closed), and the structures of
the boundary ep-groupoid are Part I's `tameBoundaryPolyfold` of the object and the morphism
M-polyfold (`bPObj`, `bPMor`).  So:

* `EpGroupoid.theorem_7_6_9_allReps_2021`: (1)–(5) and `B` an ep-functor, as in
  `theorem_7_6_9_full_2021`; and, for **every** representative `t = (x, V, θ)` of `bX` and of
  `b𝐗`, `U(x, V, θ)` is open, the image `θ ∩ V^x` (`reachSet`) is open in `θ`, and `Φ_t`
  (`phiTot`) is an sc-diffeomorphism from `U(x, V, θ)` onto it with inverse `phiInv`; the image
  is all of `θ` when `V` is centred at `x`; and every M-polyfold structure on `bX`, resp. `b𝐗`,
  with this property for every representative has an atlas equivalent to that of `bPObj`, resp.
  `bPMor`.

## Choices

* As in Part I (V2.104, V2.105), "an sc-diffeomorphism onto `θ`" holds as we read it only for
  `V` centred at `x`; for every representative the image is the open subset `θ ∩ V^x` of `θ`,
  which is `θ` in the centred case (`MPolyfold.reachSet_eq_univ_of_isCenteredAt`).
* The hypotheses of both uniqueness statements are satisfied by `bPObj` and `bPMor` themselves
  (the characterization clauses); the tameness hypothesis is met by
  `trivial_quadrant_boundaryEp_witness`.
* (4) is stated as printed, with natural-number subtraction, as in `theorem_7_6_9_full_2021`.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

namespace EpGroupoid

open TameBoundary MPolyfold

universe w

variable {Obj Mor : Type w} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- **2021 Theorem 7.6.9 (p. 355) in full, with the characterization for every
representative**: (1) `bX`, `b𝐗` metrizable; (2) `bPObj`, `bPMor` tame; (3) both maps `B`
sc-smooth; (4) `d_X(B p) − 1 = d_{bX}(p)`, `d_𝐗(B a) − 1 = d_{b𝐗}(a)`; (5) the tame ep-groupoid
`boundaryEpGroupoid` with its structure maps, and `B` an ep-functor; and (2), the
characterization: for every representative `t = (x, V, θ)` of `bX` and of `b𝐗`, `U(x, V, θ)` and
`θ ∩ V^x` are open, `Φ_t` is an sc-diffeomorphism `U(x, V, θ) → θ ∩ V^x` (all of `θ` for `V`
centred at `x`), and every M-polyfold structure with this property for every representative has
an atlas equivalent to `bPObj`, resp. `bPMor`. -/
theorem theorem_7_6_9_allReps_2021 (hX : X.IsTame) :
    -- (1)
    TopologicalSpace.MetrizableSpace (X.bObj hX) ∧ TopologicalSpace.MetrizableSpace (X.bMor hX) ∧
      -- (2), tameness
      (X.bPObj hX).IsTame ∧ (X.bPMor hX).IsTame ∧
      -- (3)
      (X.bPObj hX).IsScSmoothMap X.PObj (X.PObj.tameBoundaryMap hX) ∧
      (X.bPMor hX).IsScSmoothMap X.PMor (X.PMor.tameBoundaryMap (X.isTame_PMor hX)) ∧
      -- (4)
      (∀ p, X.PObj.degIndex (X.PObj.tameBoundaryMap hX p) - 1 = (X.bPObj hX).degIndex p) ∧
      (∀ a, X.PMor.degIndex (X.PMor.tameBoundaryMap (X.isTame_PMor hX) a) - 1 =
        (X.bPMor hX).degIndex a) ∧
      -- (5), the tame ep-groupoid and its structure maps
      (X.boundaryEpGroupoid hX).IsTame ∧
      (X.boundaryEpGroupoid hX).toGroupoidStr = X.boundaryGroupoid hX ∧
      (X.boundaryEpGroupoid hX).PObj = X.bPObj hX ∧ (X.boundaryEpGroupoid hX).PMor = X.bPMor hX ∧
      (X.bPMor hX).IsLocalScDiffeo (X.bPObj hX) (X.bSrc hX) ∧
      (X.bPMor hX).IsLocalScDiffeo (X.bPObj hX) (X.bTgt hX) ∧
      (X.bPObj hX).IsScSmoothMap (X.bPMor hX) (X.bUnit hX) ∧
      (X.bPMor hX).IsScSmoothMap (X.bPMor hX) (X.bInv hX) ∧
      IsScSmoothComp (X.bPObj hX) (X.bPMor hX) (X.bSrc hX) (X.bTgt hX) (X.bComp hX)
        (isLocalScDiffeo_bSrc hX) (isLocalScDiffeo_bTgt hX).isScSmoothMap ∧
      -- `B` is an ep-functor
      (∃ F : EpFunctor (X.boundaryEpGroupoid hX) X,
        F.obj = X.PObj.tameBoundaryMap hX ∧ F.mor = X.PMor.tameBoundaryMap (X.isTame_PMor hX)) ∧
      -- (2), the characterization, for every representative, for `bX` and for `b𝐗`
      (∀ t : BTriple (X.cornerObj hX),
        IsOpen (uSet _ t) ∧ IsOpen (X.PObj.reachSet hX t) ∧
        (IsCenteredAt X.PObj.degIndex t.x t.V → X.PObj.reachSet hX t = univ) ∧
        letI := X.PObj.paracompactSpace_subtype t.θ
        (X.bPObj hX).IsScDiffeoOn (X.PObj.facePolyfold hX t.mem.1.1 t.mem_faces.1)
          (X.PObj.phiTot hX t) (phiInv _ t) (uSet _ t) (X.PObj.reachSet hX t)) ∧
      (∀ t : BTriple (X.cornerMor hX),
        IsOpen (uSet _ t) ∧ IsOpen (X.PMor.reachSet (X.isTame_PMor hX) t) ∧
        (IsCenteredAt X.PMor.degIndex t.x t.V → X.PMor.reachSet (X.isTame_PMor hX) t = univ) ∧
        letI := X.PMor.paracompactSpace_subtype t.θ
        (X.bPMor hX).IsScDiffeoOn
          (X.PMor.facePolyfold (X.isTame_PMor hX) t.mem.1.1 t.mem_faces.1)
          (X.PMor.phiTot (X.isTame_PMor hX) t) (phiInv _ t) (uSet _ t)
          (X.PMor.reachSet (X.isTame_PMor hX) t)) ∧
      -- (2), the uniqueness, for every representative, for `bX` and for `b𝐗`
      (∀ Q' : MPolyfold (X.bObj hX),
        (∀ t : BTriple (X.cornerObj hX),
          letI := X.PObj.paracompactSpace_subtype t.θ
          Q'.IsScDiffeoOn (X.PObj.facePolyfold hX t.mem.1.1 t.mem_faces.1) (X.PObj.phiTot hX t)
            (phiInv _ t) (uSet _ t) (X.PObj.reachSet hX t)) →
        Q'.atlas.Equiv (X.bPObj hX).atlas) ∧
      ∀ Q' : MPolyfold (X.bMor hX),
        (∀ t : BTriple (X.cornerMor hX),
          letI := X.PMor.paracompactSpace_subtype t.θ
          Q'.IsScDiffeoOn (X.PMor.facePolyfold (X.isTame_PMor hX) t.mem.1.1 t.mem_faces.1)
            (X.PMor.phiTot (X.isTame_PMor hX) t) (phiInv _ t) (uSet _ t)
            (X.PMor.reachSet (X.isTame_PMor hX) t)) →
        Q'.atlas.Equiv (X.bPMor hX).atlas := by
  obtain ⟨m₀, m₁, t₀, t₁, s₀, s₁, d₀, d₁, h5, e₁, e₂, e₃, hs, ht, hu, hi, hc, hF, -⟩ :=
    theorem_7_6_9_full_2021 hX
  refine ⟨m₀, m₁, t₀, t₁, s₀, s₁, d₀, d₁, h5, e₁, e₂, e₃, hs, ht, hu, hi, hc, hF, fun t => ?_,
    fun t => ?_, X.PObj.tameBoundaryPolyfold_unique_allReps_2021 hX,
    X.PMor.tameBoundaryPolyfold_unique_allReps_2021 (X.isTame_PMor hX)⟩
  · let _ := X.PObj.paracompactSpace_subtype t.θ
    let _ : ParacompactSpace (X.PObj.TameBoundarySpace hX) := X.paracompactSpace_bObj hX
    have h := X.PObj.phi_isScDiffeoOn_nonCentred_2021 hX t
    exact ⟨h.isScSmoothOn.isOpen, X.PObj.isOpen_reachSet hX t,
      X.PObj.reachSet_eq_univ_of_isCenteredAt hX, h⟩
  · let _ := X.PMor.paracompactSpace_subtype t.θ
    let _ : ParacompactSpace (X.PMor.TameBoundarySpace (X.isTame_PMor hX)) :=
      X.paracompactSpace_bMor hX
    have h := X.PMor.phi_isScDiffeoOn_nonCentred_2021 (X.isTame_PMor hX) t
    exact ⟨h.isScSmoothOn.isOpen, X.PMor.isOpen_reachSet (X.isTame_PMor hX) t,
      X.PMor.reachSet_eq_univ_of_isCenteredAt (X.isTame_PMor hX), h⟩

end EpGroupoid

end Polyfold
