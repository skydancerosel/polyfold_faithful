import Polyfold
/-! Blind formalization of V16_24 (the text's Part II, §16.4, Proposition 16.4.3, p. 730 of the
Springer 2021 book; 2017: Proposition 16.6).

Text: `A = supp θ` has a natural smooth manifold (orbifold) structure for `θ` of manifold-type
(orbifold-type), induced from the overhead (Proposition 9.1.9, Theorem 11.3.3).

Choices:
- Setting: `Z : Type` (universe `0`), a polyfold `c`, a branched suborbifold
  `θ = [Θ, (X, α)] : c.BranchedSuborbifold` (Definition 16.4.1), representatives
  `a : c.BranchedRep` with `⟦a⟧ = θ`; `supp θ = {z | θ(z) > 0}` (the project's
  `BranchedSuborbifold.supp`), `|supp Θ| = a.p.X.X.orbitSupp a.Θ ⊆ |X|`.
- Manifold-type / orbifold-type: the project's `BranchedSuborbifold.IsManifoldType` /
  `IsOrbifoldType` (`#print`ed: some representative is of that type, Definition 9.1.8).
- "induced from the overhead": on each representative, `α` maps `|supp Θ|` onto `supp θ`
  (conjunct (0)), and the structure of Proposition 9.1.9 on `|supp Θ|` is transported to
  `supp θ`.  "natural" = the transported structure does not depend on the representative.
- Manifold type.  The smooth manifold structure of Proposition 9.1.9 (1) on `|supp Θ|` is the
  project's `IsInducedSuppStructure a PZ` (`#print`ed: `supp Θ` is an ep-subgroupoid and a
  smooth finite-dimensional submanifold of `X`, and the M-polyfold structure `PZ` on
  `|supp Θ|` makes `supp Θ → |supp Θ|` a local sc-diffeomorphism).  I read "smooth manifold
  structure" as such a (finite-dimensional) M-polyfold structure, not as a Mathlib
  `ChartedSpace`.  Claims: (M1) such a `PZ` exists on every representative; (M2) for two
  representatives `a, a'` and induced `PZ, PZ'`, the transition `e : |supp Θ| → |supp Θ'|`,
  `α' ∘ e = α`, with inverse `g`, is an sc-diffeomorphism (`MPolyfold.IsScDiffeoOn` on `univ`).
  The paracompact/Hausdorff instances on `|supp Θ|` that the project's M-polyfold notion needs
  are quantified (they hold: `|supp Θ|` is a subspace of the metrizable `|X|`).  The existence of
  `e, g` follows from (0) and the injectivity of `α, α'`.
- Orbifold type.  The orbifold structure of `|supp Θ|` (Proposition 9.1.9 (2) / Theorem 11.3.3)
  is the ep-groupoid `X|supp Θ` (the project's `EP.sub`, the restriction to an ep-subgroupoid),
  with `supp Θ` a smooth finite-dimensional submanifold of `X`, together with the map
  `|X|supp Θ| → supp θ`, `|x| ↦ α(|x|)`.  Claims: (O1) `supp Θ` is an ep-subgroupoid and a smooth
  finite-dimensional submanifold; (O2) `|x| ↦ α(|x|)` is a homeomorphism `|X|supp Θ| ≃ₜ supp θ`;
  (O3) for two representatives the two orbifold structures on `supp θ` are equivalent: a
  generalized isomorphism `𝔥 : X|supp Θ → X'|supp Θ'` with `α' ∘ |𝔥| = α` (Definition 16.1.2's
  notion of equivalence, read on `supp θ`).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_24
open Polyfold

variable {Z : Type} [TopologicalSpace Z] {c : PolyfoldClass Z}

/-- (0) `α` maps `|supp Θ|` onto `supp θ`, for every representative. -/
def ImageSupp (θ : c.BranchedSuborbifold) : Prop :=
  ∀ a : c.BranchedRep, ⟦a⟧ = θ → a.p.β '' (a.p.X.X.orbitSupp a.Θ) = θ.supp

/-- Manifold type: the structure of Proposition 9.1.9 (1) exists on every representative, and the
transitions between representatives are sc-diffeomorphisms. -/
def ManifoldPart (θ : c.BranchedSuborbifold) : Prop :=
  θ.IsManifoldType →
    (∀ a : c.BranchedRep, ⟦a⟧ = θ →
      ∀ [ParacompactSpace ↑(a.p.X.X.orbitSupp a.Θ)] [T2Space ↑(a.p.X.X.orbitSupp a.Θ)],
        ∃ PZ : MPolyfold ↑(a.p.X.X.orbitSupp a.Θ),
          PolyfoldClass.BranchedSuborbifold.IsInducedSuppStructure a PZ) ∧
    (∀ a a' : c.BranchedRep, ⟦a⟧ = θ → ⟦a'⟧ = θ →
      ∀ [ParacompactSpace ↑(a.p.X.X.orbitSupp a.Θ)] [T2Space ↑(a.p.X.X.orbitSupp a.Θ)]
        [ParacompactSpace ↑(a'.p.X.X.orbitSupp a'.Θ)] [T2Space ↑(a'.p.X.X.orbitSupp a'.Θ)]
        (PZ : MPolyfold ↑(a.p.X.X.orbitSupp a.Θ)) (PZ' : MPolyfold ↑(a'.p.X.X.orbitSupp a'.Θ)),
        PolyfoldClass.BranchedSuborbifold.IsInducedSuppStructure a PZ →
        PolyfoldClass.BranchedSuborbifold.IsInducedSuppStructure a' PZ' →
        ∀ (e : ↑(a.p.X.X.orbitSupp a.Θ) → ↑(a'.p.X.X.orbitSupp a'.Θ))
          (g : ↑(a'.p.X.X.orbitSupp a'.Θ) → ↑(a.p.X.X.orbitSupp a.Θ)),
          (∀ x, a'.p.β (e x).1 = a.p.β x.1) → (∀ y, a.p.β (g y).1 = a'.p.β y.1) →
          MPolyfold.IsScDiffeoOn PZ PZ' e g Set.univ Set.univ)

/-- Orbifold type: `X|supp Θ` with `|x| ↦ α(|x|)` is an orbifold structure on `supp θ`, and the
structures from two representatives are equivalent. -/
def OrbifoldPart (θ : c.BranchedSuborbifold) : Prop :=
  θ.IsOrbifoldType →
    (∀ a : c.BranchedRep, ⟦a⟧ = θ →
      ∃ _hA : a.p.X.X.IsEpSubgroupoid (EpGroupoid.supp a.Θ),
        a.p.X.X.PObj.IsSmoothSubmanifold (EpGroupoid.supp a.Θ)) ∧
    (∀ a : c.BranchedRep, ⟦a⟧ = θ → ∀ hA : a.p.X.X.IsEpSubgroupoid (EpGroupoid.supp a.Θ),
      ∃ h : (a.p.X.sub hA).X.OrbitSpace ≃ₜ ↑θ.supp,
        ∀ x : (a.p.X.sub hA).Obj, (h (Quotient.mk _ x) : Z) = a.p.β (Quotient.mk _ x.1)) ∧
    (∀ a a' : c.BranchedRep, ⟦a⟧ = θ → ⟦a'⟧ = θ →
      ∀ (hA : a.p.X.X.IsEpSubgroupoid (EpGroupoid.supp a.Θ))
        (hA' : a'.p.X.X.IsEpSubgroupoid (EpGroupoid.supp a'.Θ)),
        ∃ 𝔥 : ({ toEP := a.p.X.sub hA } : EPLocalization.EPLoc) ⟶ { toEP := a'.p.X.sub hA' },
          EPLocalization.EPLoc.IsGeneralizedIso 𝔥 ∧
          ∀ (x : (a.p.X.sub hA).Obj) (y : (a'.p.X.sub hA').Obj),
            EPLocalization.EPLoc.orbitMap 𝔥 (Quotient.mk _ x) = Quotient.mk _ y →
              a'.p.β (Quotient.mk _ y.1) = a.p.β (Quotient.mk _ x.1))

/-- Proposition 16.4.3: `supp θ` carries the natural manifold (orbifold) structure induced from
the representatives, for `θ` of manifold (orbifold) type. -/
def B : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] (c : PolyfoldClass Z) (θ : c.BranchedSuborbifold),
    ImageSupp θ ∧ ManifoldPart θ ∧ OrbifoldPart θ

end RoundTrip.V16_24
