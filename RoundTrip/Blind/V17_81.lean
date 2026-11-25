import Polyfold
/-! Blind formalization of V17_81 (the text's §17.4, Theorem 17.4.16, p. 801 of the Springer 2021
book; new in the 2021 edition).

Text: for the natural structures on the `M(Ψ_θ, Ψ'_{θ'})` all structure maps are sc-smooth and
`s, t` are local sc-diffeomorphisms.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a TAME polyfold structure
  `S : C.PolyfoldConstruction` (`hT : S.IsTame`; §17.4 works with tame polyfolds) and
  `hS : S.HasUniformizers` (`F(α) ≠ ∅`; the project's tame boundary category `bC`, hence
  `M(Ψ_θ, Ψ'_{θ'})`, is built with it, and the text presupposes uniformizers at every object).
- The face uniformizers `Ψ_θ` are given by data `(Ψ, ō, U(ō), θ)`: the project's
  `S.FaceData` (`#print`ed: a uniformizer `Ψ` of `F`, a point `ō` FIXED by `G` (the text's "`G`
  the isotropy group", p. 792), a good open neighbourhood `U(ō)` (17.53) and a face
  `θ ∈ F_{U(ō)}` of it).  B ranges over all such data `d, d', d''`.
- `M(Ψ_θ, Ψ'_{θ'})` = the project's `GoodNbhd.FTr` (the transition set, in `bC`, of
  `θ ∋ x ↦ Ψ_θ(x)` and `θ' ∋ x' ↦ Ψ'_{θ'}(x')`), with its natural topology and M-polyfold
  structure of Definition 17.4.14 = the project's `GoodNbhd.ftrPolyfold` (the structure for which
  (17.74) `M(Ψ_θ, Ψ'_{θ'}) ≃ M(Ψ, Ψ')*_{θ,θ'}` is an sc-diffeomorphism onto the sub-M-polyfold
  `M(Ψ, Ψ')*_{θ,θ'}` of `M(Ψ, Ψ')`).  These are the text's definitions, taken from the
  vocabulary; I did not re-derive Definition 17.4.14.
- `θ` carries its structure as a sub-M-polyfold of `O` (Theorem 2.5.17), the project's
  `GoodNbhd.faceSubPolyfold`.
- The structure maps (Definition 17.1.5, p. 746) are the transition-set maps in `bC` (the
  project's generic `GroupoidStr.TransitionSet.src/tgt/inv/unit/mul`): `s : M(Ψ_θ, Ψ'_{θ'}) → θ`,
  `t : → θ'`, `ι : M(Ψ_θ, Ψ'_{θ'}) → M(Ψ'_{θ'}, Ψ_θ)`, `u : θ → M(Ψ_θ, Ψ_θ)`,
  `m : M(Ψ'_{θ'}, Ψ''_{θ''}) ₛ×ₜ M(Ψ_θ, Ψ'_{θ'}) → M(Ψ_θ, Ψ''_{θ''})`.
- "sc-smooth" = `MPolyfold.IsScSmoothMap`; "local sc-diffeomorphism" = `IsLocalScDiffeo`;
  `m` sc-smooth = the project's `MPolyfold.IsScSmoothOnFibredProduct` (sc-smooth on the
  sub-M-polyfold fibred product of the product), whose proof arguments are the claims on `s`
  and `t`.  "All structure maps": `s, t, ι, u, m`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_81
open Polyfold GCT.PolyfoldConstruction

noncomputable section

variable {C : GCT.{0}} {S : C.PolyfoldConstruction}

/-- `M(Ψ_θ, Ψ'_{θ'})` for face data `d, d'`, with the natural structure. -/
abbrev FT (hT : S.IsTame) (hS : S.HasUniformizers) (d d' : S.FaceData) : Type :=
  GoodNbhd.FTr hT hS d.V d'.V d.hθ d'.hθ

/-- The natural M-polyfold structure of `M(Ψ_θ, Ψ'_{θ'})` (Definition 17.4.14). -/
def FTM (hT : S.IsTame) (hS : S.HasUniformizers) (d d' : S.FaceData) :
    MPolyfold (FT hT hS d d') :=
  GoodNbhd.ftrPolyfold hT hS d.V d'.V d.hθ d'.hθ

/-- The face `θ` as a sub-M-polyfold of `O`. -/
def θM (hT : S.IsTame) (d : S.FaceData) : MPolyfold ↑d.θ :=
  GoodNbhd.faceSubPolyfold hT d.V d.hθ

/-- `s(x, Φ, x') = x`. -/
def src (hT : S.IsTame) (hS : S.HasUniformizers) (d d' : S.FaceData) (a : FT hT hS d d') :
    ↑d.θ :=
  GroupoidStr.TransitionSet.src (a : GoodNbhd.FaceTr hT hS d.V d'.V d.hθ d'.hθ)

/-- `t(x, Φ, x') = x'`. -/
def tgt (hT : S.IsTame) (hS : S.HasUniformizers) (d d' : S.FaceData) (a : FT hT hS d d') :
    ↑d'.θ :=
  GroupoidStr.TransitionSet.tgt (a : GoodNbhd.FaceTr hT hS d.V d'.V d.hθ d'.hθ)

/-- `ι(x, Φ, x') = (x', Φ⁻¹, x)`. -/
def inv (hT : S.IsTame) (hS : S.HasUniformizers) (d d' : S.FaceData) (a : FT hT hS d d') :
    FT hT hS d' d :=
  GroupoidStr.TransitionSet.inv (a : GoodNbhd.FaceTr hT hS d.V d'.V d.hθ d'.hθ)

/-- `u(x) = (x, 1, x)`. -/
def unit (hT : S.IsTame) (hS : S.HasUniformizers) (d : S.FaceData) (x : ↑d.θ) :
    FT hT hS d d :=
  (GroupoidStr.TransitionSet.unit x : GoodNbhd.FaceTr hT hS d.V d.V d.hθ d.hθ)

/-- `m((x', Φ', x''), (x, Φ, x')) = (x, Φ' ∘ Φ, x'')` on the fibred product. -/
def mul (hT : S.IsTame) (hS : S.HasUniformizers) (d d' d'' : S.FaceData)
    (p : ↑(MPolyfold.fibredProduct (src hT hS d' d'') (tgt hT hS d d'))) : FT hT hS d d'' :=
  GroupoidStr.TransitionSet.comp (p.1.1 : GoodNbhd.FaceTr hT hS d'.V d''.V d'.hθ d''.hθ)
    (p.1.2 : GoodNbhd.FaceTr hT hS d.V d'.V d.hθ d'.hθ) (by
    obtain ⟨⟨⟨s₁, m₁, t₁, hs₁, ht₁⟩, ⟨s₂, m₂, t₂, hs₂, ht₂⟩⟩, h⟩ := p
    change s₁ = t₂ at h
    subst h
    exact hs₁.trans ht₂.symm)

end

/-- Theorem 17.4.16: for the natural M-polyfold structures on the `M(Ψ_θ, Ψ'_{θ'})`, `s` and `t`
are local sc-diffeomorphisms and `ι`, `u`, `m` are sc-smooth. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (hT : S.IsTame) (hS : S.HasUniformizers),
    ∃ (hs : ∀ d d' : S.FaceData,
          (FTM hT hS d d').IsLocalScDiffeo (θM hT d) (src hT hS d d'))
      (_ht : ∀ d d' : S.FaceData,
          (FTM hT hS d d').IsLocalScDiffeo (θM hT d') (tgt hT hS d d')),
      (∀ d d' : S.FaceData, (FTM hT hS d d').IsScSmoothMap (FTM hT hS d' d) (inv hT hS d d')) ∧
      (∀ d : S.FaceData, (θM hT d).IsScSmoothMap (FTM hT hS d d) (unit hT hS d)) ∧
      (∀ d d' d'' : S.FaceData,
        ∃ hts : (FTM hT hS d d').IsScSmoothMap (θM hT d') (tgt hT hS d d'),
          MPolyfold.IsScSmoothOnFibredProduct (FTM hT hS d' d'') (FTM hT hS d d')
            (FTM hT hS d d'') (hs d' d'') hts (mul hT hS d d' d''))

end RoundTrip.V17_81
