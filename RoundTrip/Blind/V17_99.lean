import Polyfold
/-! Blind formalization of V17_99 (the text's Part II, §17.5, Proposition 17.5.5, p. 814 of the
Springer 2021 book; 2017: Proposition 17.9).

Text: (1) for manifold-type `Θ`, `|supp(Θ)|` is naturally a smooth finite-dimensional manifold;
(2) for orbifold-type `Θ` it carries a natural orbifold structure (details left to the reader).

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`, and a branched ep⁺-subcategory `Θ` (`S.IsBranchedSubcategory Θ`,
  Definition 17.5.1; presupposed, Definition 17.5.4 is about these).  `|supp(Θ)|` = the
  project's `C.toGroupoidStr.orbitSupp Θ ⊆ |C|`.  Manifold-type / orbifold-type = the project's
  `C.IsManifoldTypeBranched Θ` / `C.IsOrbifoldTypeBranched Θ` (Definition 17.5.4 (1), (2), by
  their docstrings).
- "naturally", "induced": the structure comes from the models.  For a covering family `Ψ`
  (`S.CoveringFamily`), `X_Ψ` = `S.modelEP c.Ψ`, `Γ_Ψ` = `S.modelFunctor c.Ψ`,
  `Γ_Ψ^*Θ` = `S.modelPull c.Ψ Θ` (the text's constructions, from the vocabulary).  Conjunct (0):
  `|Γ_Ψ|` maps `|supp(Γ_Ψ^*Θ)|` onto `|supp(Θ)|` for every `Ψ` (the identification along which
  the structures are transported).  I do not use the project's `suppHomeomorph`.
- Manifold type.  "smooth finite-dimensional manifold structure" on `|supp(Θ)|`: an M-polyfold
  structure `PZ` on `|supp(Θ)|` (not a Mathlib `ChartedSpace`) such that for EVERY covering
  family `Ψ`: the structure of Proposition 9.1.9 (1) exists on `|supp(Γ_Ψ^*Θ)|` (the project's
  `EpGroupoid.IsSuppStructure`: `supp` is an ep-subgroupoid and a smooth finite-dimensional
  submanifold of `X_Ψ`, and `PZ_Ψ` makes `supp → |supp|` a local sc-diffeomorphism), and for
  every such `PZ_Ψ` the map `|Γ_Ψ| : |supp(Γ_Ψ^*Θ)| → |supp(Θ)|` (with an inverse `g`) is an
  sc-diffeomorphism `PZ_Ψ → PZ`.  One `PZ` for all `Ψ` is my reading of "naturally".  The
  Hausdorff/paracompact instances on the support subspaces that the project's M-polyfolds need
  are quantified (they hold: subspaces of metrizable spaces).
- Orbifold type (as in my reading of Proposition 16.4.3, `RoundTrip/Blind/V16_24.lean`): the
  orbifold structure is the ep-groupoid `X_Ψ|supp(Γ_Ψ^*Θ)` (project's `EP.sub`) with the map
  `|x| ↦ |Γ_Ψ(x)|` to `|supp(Θ)|`.  Claims: (O1) `supp(Γ_Ψ^*Θ)` is an ep-subgroupoid and a smooth
  finite-dimensional submanifold of `X_Ψ`; (O2) `|x| ↦ |Γ_Ψ(x)|` is a homeomorphism
  `|X_Ψ|supp| ≃ₜ |supp(Θ)|`; (O3) "natural": for two covering families there is a generalized
  isomorphism between the two restricted ep-groupoids compatible with these maps.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_99
open Polyfold

variable {C : GCT.{0}} (S : C.PolyfoldConstruction)

/-- `|Γ_Ψ|` maps `|supp(Γ_Ψ^*Θ)|` onto `|supp(Θ)|`, for every covering family. -/
def ImageSupp (Θ : C.Obj → ℚ) : Prop :=
  ∀ c : S.CoveringFamily,
    (S.modelFunctor c.Ψ).orbitMap '' ((S.modelEP c.Ψ).X.orbitSupp (S.modelPull c.Ψ Θ)) =
      C.toGroupoidStr.orbitSupp Θ

/-- Manifold type: one M-polyfold structure on `|supp(Θ)|`, sc-diffeomorphic through `|Γ_Ψ|` to
the structure of Proposition 9.1.9 (1) on every model. -/
def ManifoldPart (Θ : C.Obj → ℚ) : Prop :=
  C.IsManifoldTypeBranched Θ →
    ∀ [ParacompactSpace ↑(C.toGroupoidStr.orbitSupp Θ)]
      [T2Space ↑(C.toGroupoidStr.orbitSupp Θ)],
    ∃ PZ : MPolyfold ↑(C.toGroupoidStr.orbitSupp Θ),
      ∀ (c : S.CoveringFamily)
        [ParacompactSpace ↑((S.modelEP c.Ψ).X.orbitSupp (S.modelPull c.Ψ Θ))]
        [T2Space ↑((S.modelEP c.Ψ).X.orbitSupp (S.modelPull c.Ψ Θ))],
        (∃ PZc : MPolyfold ↑((S.modelEP c.Ψ).X.orbitSupp (S.modelPull c.Ψ Θ)),
          (S.modelEP c.Ψ).X.IsSuppStructure (S.modelPull c.Ψ Θ) PZc) ∧
        ∀ (PZc : MPolyfold ↑((S.modelEP c.Ψ).X.orbitSupp (S.modelPull c.Ψ Θ))),
          (S.modelEP c.Ψ).X.IsSuppStructure (S.modelPull c.Ψ Θ) PZc →
          ∀ (e : ↑((S.modelEP c.Ψ).X.orbitSupp (S.modelPull c.Ψ Θ)) →
              ↑(C.toGroupoidStr.orbitSupp Θ))
            (g : ↑(C.toGroupoidStr.orbitSupp Θ) →
              ↑((S.modelEP c.Ψ).X.orbitSupp (S.modelPull c.Ψ Θ))),
            (∀ x, (e x).1 = (S.modelFunctor c.Ψ).orbitMap x.1) →
            (∀ y, (S.modelFunctor c.Ψ).orbitMap (g y).1 = y.1) →
            MPolyfold.IsScDiffeoOn PZc PZ e g Set.univ Set.univ

/-- Orbifold type: `X_Ψ|supp(Γ_Ψ^*Θ)` with `|x| ↦ |Γ_Ψ(x)|` is an orbifold structure on
`|supp(Θ)|`, and the structures from two covering families are equivalent. -/
def OrbifoldPart (Θ : C.Obj → ℚ) : Prop :=
  C.IsOrbifoldTypeBranched Θ →
    (∀ c : S.CoveringFamily,
      ∃ _hA : (S.modelEP c.Ψ).X.IsEpSubgroupoid (EpGroupoid.supp (S.modelPull c.Ψ Θ)),
        (S.modelEP c.Ψ).X.PObj.IsSmoothSubmanifold (EpGroupoid.supp (S.modelPull c.Ψ Θ))) ∧
    (∀ (c : S.CoveringFamily)
      (hA : (S.modelEP c.Ψ).X.IsEpSubgroupoid (EpGroupoid.supp (S.modelPull c.Ψ Θ))),
      ∃ h : ((S.modelEP c.Ψ).sub hA).X.OrbitSpace ≃ₜ ↑(C.toGroupoidStr.orbitSupp Θ),
        ∀ x : ((S.modelEP c.Ψ).sub hA).Obj,
          (h (((S.modelEP c.Ψ).sub hA).X.π x)).1 =
            (S.modelFunctor c.Ψ).orbitMap ((S.modelEP c.Ψ).X.π x.1)) ∧
    (∀ (c c' : S.CoveringFamily)
      (hA : (S.modelEP c.Ψ).X.IsEpSubgroupoid (EpGroupoid.supp (S.modelPull c.Ψ Θ)))
      (hA' : (S.modelEP c'.Ψ).X.IsEpSubgroupoid (EpGroupoid.supp (S.modelPull c'.Ψ Θ))),
      ∃ 𝔥 : ({ toEP := (S.modelEP c.Ψ).sub hA } : EPLocalization.EPLoc) ⟶
          { toEP := (S.modelEP c'.Ψ).sub hA' },
        EPLocalization.EPLoc.IsGeneralizedIso 𝔥 ∧
        ∀ (x : ((S.modelEP c.Ψ).sub hA).Obj) (y : ((S.modelEP c'.Ψ).sub hA').Obj),
          EPLocalization.EPLoc.orbitMap 𝔥 (((S.modelEP c.Ψ).sub hA).X.π x) =
              ((S.modelEP c'.Ψ).sub hA').X.π y →
            (S.modelFunctor c'.Ψ).orbitMap ((S.modelEP c'.Ψ).X.π y.1) =
              (S.modelFunctor c.Ψ).orbitMap ((S.modelEP c.Ψ).X.π x.1))

/-- Proposition 17.5.5: `|supp(Θ)|` carries the natural manifold (orbifold) structure, for `Θ`
of manifold (orbifold) type. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (Θ : C.Obj → ℚ), S.IsBranchedSubcategory Θ →
    ImageSupp S Θ ∧ ManifoldPart S Θ ∧ OrbifoldPart S Θ

end RoundTrip.V17_99
