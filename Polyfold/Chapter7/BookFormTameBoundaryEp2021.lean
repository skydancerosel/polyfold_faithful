import Polyfold.Chapter7.TameBoundaryFull

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 7,
Appendix §7.6.5.2: **Theorem 7.6.9** (p. 355, new in the 2021 edition) with the characterization
after it, in one statement.

# Theorem 7.6.9 in book form

## The text, paraphrased

(Theorem 7.6.9, p. 355) For a tame ep-groupoid `(X, 𝐗)`: (1) `bX` and `b𝐗` carry natural metrizable
topologies; (2) natural tame M-polyfold structures; (3) both maps `B` are sc-smooth;
(4) `d_X(B(p)) − 1 = d_{bX}(p)`, and likewise on `b𝐗`; (5) `(bX, b𝐗)` with `s, t, u, ι, m` is a tame
ep-groupoid.  The topologies and the M-polyfold structures are characterized as in Theorem 2.7.13:
every `U(x, V, θ)` is open and every `Φ_{(x,V,θ)} : U(x, V, θ) → θ` is a homeomorphism and an
sc-diffeomorphism.

## What is formalized

* `EpGroupoid.theorem_7_6_9_book`: (1)–(5), `B` an ep-functor, and the characterization of both
  the topologies and the M-polyfold structures of `bX` and `b𝐗` (existence and uniqueness), in one
  statement.  The topological half (open embeddings `Φ`, uniqueness of the topologies) is
  `theorem_7_6_9` (row V7.98); the rest is `theorem_7_6_9_allReps` (rows V7.100, V7.101); for the
  centred case `phi_bijective_of_isCenteredAt`.

## The reading

* As in Part I (rows V2.104, V2.105, and `Chapter2/BookFormTameBoundary2021.lean`), "a
  homeomorphism and an sc-diffeomorphism onto `θ`" holds as we read it for `V` centred at `x`;
  for every representative `Φ_{(x,V,θ)}` is an open embedding and an sc-diffeomorphism onto the
  open subset `θ ∩ V^x` (`reachSet`) of `θ`, which is `θ` in the centred case.
* "Characterized" is read as uniqueness: a topology for which every `U` is open and every `Φ` is
  an open map into `θ` is `T_{bX}` (resp. `T_{b𝐗}`); an M-polyfold structure for which every `Φ`
  is an sc-diffeomorphism onto `θ ∩ V^x` has an atlas equivalent to `bPObj` (resp. `bPMor`).  The
  hypotheses are satisfied by `T_{bX}`, `bPObj` (resp. `T_{b𝐗}`, `bPMor`) themselves.
* (4) is stated as printed, with natural-number subtraction (`B` takes values where `d ≥ 1`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

namespace EpGroupoid

open TameBoundary MPolyfold

universe w

variable {Obj Mor : Type w} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- **2021 Theorem 7.6.9, p. 355** (new in the 2021 edition), with the characterization after it,
in book form, for a tame ep-groupoid `(X, 𝐗)`:
(1) `bX`, `b𝐗` are metrizable, and `T_{bX}`, `T_{b𝐗}` are the only topologies for which every
`U(x, V, θ)` is open and every `Φ_{(x,V,θ)}` is open into `θ`;
(2) `bPObj`, `bPMor` are tame; for every representative `(x, V, θ)` of `bX` and of `b𝐗`,
`U(x, V, θ)` is open, `Φ_{(x,V,θ)}` is an open embedding and an sc-diffeomorphism of `U(x, V, θ)`
onto the open set `θ ∩ V^x` (`reachSet`), and for `V` centred at `x` it is a bijection onto `θ`
(`θ ∩ V^x = θ`); every M-polyfold structure with this property is equivalent to `bPObj`, resp.
`bPMor`;
(3) both maps `B` are sc-smooth; (4) `d_X(B p) − 1 = d_{bX}(p)`, `d_𝐗(B a) − 1 = d_{b𝐗}(a)`;
(5) `boundaryEpGroupoid` is a tame ep-groupoid with the groupoid `(bX, b𝐗)` of (7.25)–(7.29) and
the structures `bPObj`, `bPMor` (`s, t` local sc-diffeomorphisms, `u, ι` sc-smooth, `m`
sc-smooth on the fibred product), and `B` is an ep-functor.
"Onto `θ`" for non-centred `V` does not hold as we read it (`not_surjOn_phiTot`). -/
theorem theorem_7_6_9_book (hX : X.IsTame) :
    -- (1), with the uniqueness of the topologies
    TopologicalSpace.MetrizableSpace (X.bObj hX) ∧ TopologicalSpace.MetrizableSpace (X.bMor hX) ∧
      (∀ τ : TopologicalSpace (X.bObj hX), (∀ t, IsOpen[τ] (uSet (X.cornerObj hX) t)) →
        (∀ t U, IsOpen[τ] U → ∃ N, IsOpen N ∧
          bMap (X.cornerObj hX) '' (U ∩ uSet _ t) = N ∩ t.θ) →
        τ = bTopology (X.cornerObj hX)) ∧
      (∀ τ : TopologicalSpace (X.bMor hX), (∀ t, IsOpen[τ] (uSet (X.cornerMor hX) t)) →
        (∀ t U, IsOpen[τ] U → ∃ N, IsOpen N ∧
          bMap (X.cornerMor hX) '' (U ∩ uSet _ t) = N ∩ t.θ) →
        τ = bTopology (X.cornerMor hX)) ∧
      -- (2), tameness
      (X.bPObj hX).IsTame ∧ (X.bPMor hX).IsTame ∧
      -- (2), the characterization, for every representative, for `bX` and for `b𝐗`
      (∀ t : BTriple (X.cornerObj hX),
        IsOpen (uSet _ t) ∧ IsOpenEmbedding (phi _ t) ∧ IsOpen (X.PObj.reachSet hX t) ∧
        (IsCenteredAt X.PObj.degIndex t.x t.V →
          Bijective (phi _ t) ∧ X.PObj.reachSet hX t = univ) ∧
        letI := X.PObj.paracompactSpace_subtype t.θ
        (X.bPObj hX).IsScDiffeoOn (X.PObj.facePolyfold hX t.mem.1.1 t.mem_faces.1)
          (X.PObj.phiTot hX t) (phiInv _ t) (uSet _ t) (X.PObj.reachSet hX t)) ∧
      (∀ t : BTriple (X.cornerMor hX),
        IsOpen (uSet _ t) ∧ IsOpenEmbedding (phi _ t) ∧
        IsOpen (X.PMor.reachSet (X.isTame_PMor hX) t) ∧
        (IsCenteredAt X.PMor.degIndex t.x t.V →
          Bijective (phi _ t) ∧ X.PMor.reachSet (X.isTame_PMor hX) t = univ) ∧
        letI := X.PMor.paracompactSpace_subtype t.θ
        (X.bPMor hX).IsScDiffeoOn
          (X.PMor.facePolyfold (X.isTame_PMor hX) t.mem.1.1 t.mem_faces.1)
          (X.PMor.phiTot (X.isTame_PMor hX) t) (phiInv _ t) (uSet _ t)
          (X.PMor.reachSet (X.isTame_PMor hX) t)) ∧
      -- (2), the uniqueness of the structures, for `bX` and for `b𝐗`
      (∀ Q' : MPolyfold (X.bObj hX),
        (∀ t : BTriple (X.cornerObj hX),
          letI := X.PObj.paracompactSpace_subtype t.θ
          Q'.IsScDiffeoOn (X.PObj.facePolyfold hX t.mem.1.1 t.mem_faces.1) (X.PObj.phiTot hX t)
            (phiInv _ t) (uSet _ t) (X.PObj.reachSet hX t)) →
        Q'.atlas.Equiv (X.bPObj hX).atlas) ∧
      (∀ Q' : MPolyfold (X.bMor hX),
        (∀ t : BTriple (X.cornerMor hX),
          letI := X.PMor.paracompactSpace_subtype t.θ
          Q'.IsScDiffeoOn (X.PMor.facePolyfold (X.isTame_PMor hX) t.mem.1.1 t.mem_faces.1)
            (X.PMor.phiTot (X.isTame_PMor hX) t) (phiInv _ t) (uSet _ t)
            (X.PMor.reachSet (X.isTame_PMor hX) t)) →
        Q'.atlas.Equiv (X.bPMor hX).atlas) ∧
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
      ∃ F : EpFunctor (X.boundaryEpGroupoid hX) X,
        F.obj = X.PObj.tameBoundaryMap hX ∧ F.mor = X.PMor.tameBoundaryMap (X.isTame_PMor hX) := by
  obtain ⟨-, -, hT₀, hT₁, hτ₀, hτ₁, -⟩ := theorem_7_6_9 hX
  obtain ⟨m₀, m₁, t₀, t₁, s₀, s₁, d₀, d₁, h5, e₁, e₂, e₃, hs, ht, hu, hi, hc, hF, c₀, c₁, u₀,
    u₁⟩ := theorem_7_6_9_allReps hX
  refine ⟨m₀, m₁, hτ₀, hτ₁, t₀, t₁, fun t => ?_, fun t => ?_, u₀, u₁, s₀, s₁, d₀, d₁, h5, e₁,
    e₂, e₃, hs, ht, hu, hi, hc, hF⟩
  · obtain ⟨hU, hR, hC, hD⟩ := c₀ t
    exact ⟨hU, (hT₀ t).2, hR, fun hc => ⟨phi_bijective_of_isCenteredAt _ hc, hC hc⟩, hD⟩
  · obtain ⟨hU, hR, hC, hD⟩ := c₁ t
    exact ⟨hU, (hT₁ t).2, hR, fun hc => ⟨phi_bijective_of_isCenteredAt _ hc, hC hc⟩, hD⟩

end EpGroupoid

end Polyfold
