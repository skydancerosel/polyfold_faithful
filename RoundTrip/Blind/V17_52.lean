import Polyfold
/-! Blind formalization of V17_52 (the text's §17.2, Proposition 17.2.15, p. 781 of the Springer
2021 book; 2017: Proposition 17.4).

Text: `M(TΨ, TΨ')` has a natural M-polyfold structure with the maps (17.42) as charts; `s, t` are
local sc-diffeomorphisms, `ι` an sc-diffeomorphism, `u` and `m` sc-smooth.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`, and `hU : S.HasUniformizers` (needed because the project's tangent
  uniformizers on objects `TΨ = S.tangentUnifObj hU Ψ`, hence `M(TΨ₁, TΨ₂)`, are built with it;
  the text presupposes the reference uniformizers `Ψ_α ∈ F(α)`, pp. 769–771).
- `M(TΨ₁, TΨ₂)` = the project's `S.TTr hU Ψ₁ Ψ₂` (the transition set in `TC` of
  `TΨ₁, TΨ₂ : TOᵢ → TC`), for all uniformizers `Ψ₁, Ψ₂, Ψ₃` of `F`.
- The underlying topology is the natural topology of Definition 17.2.13, defined here myself
  (`natTop`) as the final topology of all maps (17.42) (`S.tangentTrChart hU T` for every
  `o ∈ M(Ψ₁, Ψ₂)` and every admissible triple `T` at `o`); the project's `tangentTrTopology`,
  `TTrM` and `tangentTrPolyfold` are not used.
- An M-polyfold structure needs `T2Space` and `ParacompactSpace` instances; they are part of the
  existential (`NatStr`: a family, over all pairs `Ψ₁, Ψ₂`, of these instances and of an
  M-polyfold structure `P Ψ₁ Ψ₂` on `(M(TΨ₁, TΨ₂), natTop)`).
- `TOᵢ` = Part I's tangent M-polyfold `Ψᵢ.P.tangentPolyfold`.
- "with the maps (17.42) as charts": every map (17.42) `TU(o) → M(TΨ₁, TΨ₂)` (`TU(o) = p⁻¹(U(o))`
  open in `TO₁`) has open image and is an sc-diffeomorphism from the open subset `TU(o)` of `TO₁`
  onto its image (`MPolyfold.IsScDiffeoOn`, for some extension `f` of the map to `TO₁` and some
  inverse `g`).
- Structure maps: the transition-set maps of Definition 17.1.5 in `TC` (the project's generic
  `GroupoidStr.TransitionSet.src/tgt/inv/unit/mul`).  "`s, t` local sc-diffeomorphisms" =
  `MPolyfold.IsLocalScDiffeo` into `TO₁`, `TO₂`; "`ι` an sc-diffeomorphism": `ι` is sc-smooth
  `M(TΨ₁, TΨ₂) → M(TΨ₂, TΨ₁)` for all pairs (its inverse is `ι` of the swapped pair, so this
  is the full claim); "`u` sc-smooth" = `MPolyfold.IsScSmoothMap`; "`m` sc-smooth" = the
  project's `MPolyfold.IsScSmoothOnFibredProduct` (sc-smooth on the sub-M-polyfold
  `M(TΨ₂, TΨ₃) ₛ×ₜ M(TΨ₁, TΨ₂)` of the product, Definition 17.1.8 (c)), whose proof arguments are
  the claims on `s` and `t`.
- B is the conjunction of these claims for one family `NatStr`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_52
open Polyfold

noncomputable section

/-- The natural topology (Definition 17.2.13): the final topology of the maps (17.42). -/
@[instance_reducible] def natTop {C : GCT.{0}} (S : C.PolyfoldConstruction)
    (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) : TopologicalSpace (S.TTr hU Ψ₁ Ψ₂) :=
  ⨆ i : (o : S.Tr Ψ₁ Ψ₂) × S.AdmissibleTriple o,
    TopologicalSpace.coinduced (S.tangentTrChart hU i.2) inferInstance

/-- `M(TΨ₁, TΨ₂)` with the natural topology. -/
def NT {C : GCT.{0}} (S : C.PolyfoldConstruction) (hU : S.HasUniformizers)
    (Ψ₁ Ψ₂ : S.Unif) : Type 1 := S.TTr hU Ψ₁ Ψ₂

instance {C : GCT.{0}} (S : C.PolyfoldConstruction) (hU : S.HasUniformizers)
    (Ψ₁ Ψ₂ : S.Unif) : TopologicalSpace (NT S hU Ψ₁ Ψ₂) := natTop S hU Ψ₁ Ψ₂

/-- A family of M-polyfold structures on the `(M(TΨ₁, TΨ₂), natTop)`. -/
structure NatStr {C : GCT.{0}} (S : C.PolyfoldConstruction) (hU : S.HasUniformizers) where
  t2 : ∀ Ψ₁ Ψ₂ : S.Unif, T2Space (NT S hU Ψ₁ Ψ₂)
  pc : ∀ Ψ₁ Ψ₂ : S.Unif, ParacompactSpace (NT S hU Ψ₁ Ψ₂)
  P : ∀ Ψ₁ Ψ₂ : S.Unif, @MPolyfold (NT S hU Ψ₁ Ψ₂) _ (t2 Ψ₁ Ψ₂) (pc Ψ₁ Ψ₂)

/-- `M(TΨ₁, TΨ₂)` with the structure `N`. -/
def NTN {C : GCT.{0}} {S : C.PolyfoldConstruction} {hU : S.HasUniformizers} (_N : NatStr S hU)
    (Ψ₁ Ψ₂ : S.Unif) : Type 1 := NT S hU Ψ₁ Ψ₂

variable {C : GCT.{0}} {S : C.PolyfoldConstruction} {hU : S.HasUniformizers}

instance (N : NatStr S hU) (Ψ₁ Ψ₂ : S.Unif) : TopologicalSpace (NTN N Ψ₁ Ψ₂) :=
  natTop S hU Ψ₁ Ψ₂
instance (N : NatStr S hU) (Ψ₁ Ψ₂ : S.Unif) : T2Space (NTN N Ψ₁ Ψ₂) := N.t2 Ψ₁ Ψ₂
instance (N : NatStr S hU) (Ψ₁ Ψ₂ : S.Unif) : ParacompactSpace (NTN N Ψ₁ Ψ₂) := N.pc Ψ₁ Ψ₂

/-- The M-polyfold `M(TΨ₁, TΨ₂)` of `N`. -/
def NatStr.M (N : NatStr S hU) (Ψ₁ Ψ₂ : S.Unif) : MPolyfold (NTN N Ψ₁ Ψ₂) := N.P Ψ₁ Ψ₂

/-- The map (17.42) `TU(o) → M(TΨ₁, TΨ₂)` of an admissible triple, into `NTN N Ψ₁ Ψ₂`. -/
def chart (N : NatStr S hU) {Ψ₁ Ψ₂ : S.Unif} {o : S.Tr Ψ₁ Ψ₂} (T : S.AdmissibleTriple o)
    (k : ↑(Ψ₁.1.P.tangentPreimage T.srcSet)) : NTN N Ψ₁ Ψ₂ :=
  S.tangentTrChart hU T k

/-- `s(q, φ, q') = q`. -/
def src (N : NatStr S hU) (Ψ₁ Ψ₂ : S.Unif) (a : NTN N Ψ₁ Ψ₂) : Ψ₁.1.P.TangentSpace :=
  GroupoidStr.TransitionSet.src (a : S.TTr hU Ψ₁ Ψ₂)

/-- `t(q, φ, q') = q'`. -/
def tgt (N : NatStr S hU) (Ψ₁ Ψ₂ : S.Unif) (a : NTN N Ψ₁ Ψ₂) : Ψ₂.1.P.TangentSpace :=
  GroupoidStr.TransitionSet.tgt (a : S.TTr hU Ψ₁ Ψ₂)

/-- `ι(q, φ, q') = (q', φ⁻¹, q)`. -/
def inv (N : NatStr S hU) (Ψ₁ Ψ₂ : S.Unif) (a : NTN N Ψ₁ Ψ₂) : NTN N Ψ₂ Ψ₁ :=
  GroupoidStr.TransitionSet.inv (a : S.TTr hU Ψ₁ Ψ₂)

/-- `u(q) = (q, 1, q)`. -/
def unit (N : NatStr S hU) (Ψ : S.Unif) (q : Ψ.1.P.TangentSpace) : NTN N Ψ Ψ :=
  (GroupoidStr.TransitionSet.unit q : S.TTr hU Ψ Ψ)

/-- `m` on the fibred product `M(TΨ₂, TΨ₃) ₛ×ₜ M(TΨ₁, TΨ₂)`. -/
def mul (N : NatStr S hU) (Ψ₁ Ψ₂ Ψ₃ : S.Unif)
    (p : ↑(MPolyfold.fibredProduct (src N Ψ₂ Ψ₃) (tgt N Ψ₁ Ψ₂))) : NTN N Ψ₁ Ψ₃ :=
  GroupoidStr.TransitionSet.comp (p.1.1 : S.TTr hU Ψ₂ Ψ₃) (p.1.2 : S.TTr hU Ψ₁ Ψ₂) (by
    obtain ⟨⟨⟨s₁, m₁, t₁, hs₁, ht₁⟩, ⟨s₂, m₂, t₂, hs₂, ht₂⟩⟩, h⟩ := p
    change s₁ = t₂ at h
    subst h
    exact hs₁.trans ht₂.symm)

end

/-- Proposition 17.2.15: the natural M-polyfold structure on the `M(TΨ₁, TΨ₂)` (the maps
(17.42) as charts), with `s, t` local sc-diffeomorphisms, `ι` an sc-diffeomorphism, `u`, `m`
sc-smooth. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (hU : S.HasUniformizers),
    ∃ N : NatStr S hU,
      -- the maps (17.42) are charts
      (∀ (Ψ₁ Ψ₂ : S.Unif) (o : S.Tr Ψ₁ Ψ₂) (T : S.AdmissibleTriple o),
        IsOpen (Set.range (chart N T)) ∧
        ∃ (f : Ψ₁.1.P.TangentSpace → NTN N Ψ₁ Ψ₂) (g : NTN N Ψ₁ Ψ₂ → Ψ₁.1.P.TangentSpace),
          (∀ k : ↑(Ψ₁.1.P.tangentPreimage T.srcSet), f k = chart N T k) ∧
          Ψ₁.1.P.tangentPolyfold.IsScDiffeoOn (N.M Ψ₁ Ψ₂) f g (Ψ₁.1.P.tangentPreimage T.srcSet)
            (Set.range (chart N T))) ∧
      ∃ (hs : ∀ Ψ₁ Ψ₂ : S.Unif, (N.M Ψ₁ Ψ₂).IsLocalScDiffeo Ψ₁.1.P.tangentPolyfold (src N Ψ₁ Ψ₂))
        (_ht : ∀ Ψ₁ Ψ₂ : S.Unif, (N.M Ψ₁ Ψ₂).IsLocalScDiffeo Ψ₂.1.P.tangentPolyfold (tgt N Ψ₁ Ψ₂)),
        (∀ Ψ₁ Ψ₂ : S.Unif, (N.M Ψ₁ Ψ₂).IsScSmoothMap (N.M Ψ₂ Ψ₁) (inv N Ψ₁ Ψ₂)) ∧
        (∀ Ψ : S.Unif, Ψ.1.P.tangentPolyfold.IsScSmoothMap (N.M Ψ Ψ) (unit N Ψ)) ∧
        (∀ Ψ₁ Ψ₂ Ψ₃ : S.Unif, ∃ hts : (N.M Ψ₁ Ψ₂).IsScSmoothMap Ψ₂.1.P.tangentPolyfold (tgt N Ψ₁ Ψ₂),
          MPolyfold.IsScSmoothOnFibredProduct (N.M Ψ₂ Ψ₃) (N.M Ψ₁ Ψ₂) (N.M Ψ₁ Ψ₃)
            (hs Ψ₂ Ψ₃) hts (mul N Ψ₁ Ψ₂ Ψ₃))

end RoundTrip.V17_52
