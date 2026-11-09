import Polyfold
/-! Blind formalization of V9_56 (the Springer 2021 book, Part II, §9.5, Lemma 9.5.11, p. 445;
2017: Lemma 9.19, p. 326): morphism invariance, the isotropy and set part.

Text: for a morphism `φ : x → x'` with local sc-diffeomorphism `φ̂ : U(x) → U(x')`,
`μ^U_ω(K) = μ^{U'}_ω(K)` for `K ⊆ |M_U| = |M_{U'}|`; likewise for the effective measures under
(LUC).

Choices:
- The item is "the isotropy and set part": the measures (integrals of sc-differential forms)
  are not in the vocabulary and are not formalized.  The local measures are
  `(1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω` (effective: `1/♯G^eff_x`), so the isotropy part is `G_x ≅ G_{x'}`
  (`g ↦ φ ∘ g ∘ φ⁻¹`, hence `♯G_x = ♯G_{x'}`; effective: the conjugation maps `T_x` onto
  `T_{x'}`, hence `♯G^eff_x = ♯G^eff_{x'}`), and the set part is `|M_U| = |M_{U'}|` and that `φ̂`
  carries the preimage of `K` in `M_U` onto its preimage in `M_{U'}`.
- Setting: `Obj Mor : Type` (universe 0), the project's ep-groupoid `X`, `Θ` a branched
  ep⁺-subgroupoid (project's `IsBranchedEpSubgroupoid`; its functoriality gives `Θ ∘ φ̂ = Θ`).
  `x = s(φ)`, `x' = t(φ)`.  `U(x)`, `U(x')`: connected, with the natural actions of `G_x`,
  `G_{x'}` (my `IsNatAction`, copied from `RoundTrip/Blind/V9_34.lean`), each with a local
  branching structure of `Θ` (project's `LocalBranchingStructure`, arbitrary; `M_U = ⋃ Mᵢ`,
  `M_{U'} = ⋃ M'ⱼ`).
- "the local sc-diffeomorphism `φ̂ : U(x) → U(x')`" (Definition 7.4: `φ̂ = t ∘ (s|𝐔(φ))⁻¹`): my
  `IsLocalHatB`: a section `σ : U → 𝐗` of `s` (`s(σ(y)) = y`), sc-smooth, with open image (the
  sheet `𝐔(φ)`), `σ(x) = φ`, and `φ̂ = t ∘ σ` an sc-diffeomorphism of `U` onto `U'` (project's
  `IsScDiffeoOn`).
- `G_x`: the project's `X.Isotropy x`; `φ ∘ g ∘ φ⁻¹ = comp (comp φ g) (inv φ)`.  `T_x`,
  `G^eff_x`, (LUC): the project's `trivialSubgroup`, `EffIsotropy`, `IsLUC` (compared in
  `RoundTrip/Blind/V7_37.lean`, `V7_41.lean`, `V8_45.lean`).
- `K ⊆ |M_U|`: `K ⊆ π(M_U)`; its preimages: `M_U ∩ π⁻¹(K)`, `M_{U'} ∩ π⁻¹(K)`.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_56
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The natural `G_x`-action on the open neighbourhood `U` of `x` (the data `Φ`, `Γ` of
Theorem 7.1), as in `RoundTrip/Blind/V7_21.lean` and `RoundTrip/Blind/V9_34.lean`. -/
structure IsNatAction (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj)
    (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor) : Prop where
  isOpen : IsOpen U
  mem : x ∈ U
  diffeo : ∀ g, ∃ ψ : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj (Φ g) ψ U U
  hom : ∀ g h, ∀ y ∈ U, Φ (g * h) y = Φ g (Φ h y)
  smooth : ∀ g, X.PObj.IsScSmoothOn X.PMor (Γ g) U
  Γ_x : ∀ g, Γ g x = g.val
  src_tgt : ∀ g, ∀ y ∈ U, X.src (Γ g y) = y ∧ X.tgt (Γ g y) = Φ g y
  unique : ∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃! g, Γ g (X.src h) = h

/-- `H = {g ∈ G_x | g ∗ y = y}`, the elements of `G_x` fixing `y`. -/
def stabB {X : EpGroupoid Obj Mor} {x : Obj} (Φ : X.Isotropy x → Obj → Obj) (y : Obj) :
    Set (X.Isotropy x) :=
  {g | Φ g y = y}

end

/-- `R` is a set of representatives of the left cosets of `H` in `G`, `G = ⨆_{r ∈ R} rH`:
every `g` is `r h` (`h ∈ H`) for exactly one `r ∈ R`. -/
def IsLeftCosetRepsB {G : Type} [Group G] (H R : Set G) : Prop :=
  ∀ g : G, ∃! r : G, r ∈ R ∧ ∃ h ∈ H, g = r * h

/-- `φ̂ = t ∘ σ : U → U'` is the local sc-diffeomorphism of the morphism `φ` (Definition 7.4):
`σ` is the inverse of `s` on an open sheet `𝐔(φ) = σ(U)` through `φ`. -/
structure IsLocalHatB {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (φ : Mor) (U U' : Set Obj) (σ : Obj → Mor) : Prop where
  isOpen : IsOpen U
  mem : X.src φ ∈ U
  sect : ∀ y ∈ U, X.src (σ y) = y
  at_src : σ (X.src φ) = φ
  smooth : X.PObj.IsScSmoothOn X.PMor σ U
  isOpen_sheet : IsOpen (σ '' U)
  diffeo : ∃ ψ : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj (fun y => X.tgt (σ y)) ψ U U'

/-- **Lemma 9.5.11, the isotropy and set part**: `g ↦ φ ∘ g ∘ φ⁻¹` is an isomorphism
`G_x ≅ G_{x'}` (so `♯G_x = ♯G_{x'}`); `|M_U| = |M_{U'}|`; `φ̂` maps the preimage of `K ⊆ |M_U|`
in `M_U` onto its preimage in `M_{U'}`; under (LUC) the isomorphism maps `T_x` onto `T_{x'}` and
`♯G^eff_x = ♯G^eff_{x'}`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    ∀ (φ : Mor) (U U' : Set Obj) (σ : Obj → Mor), IsLocalHatB X φ U U' σ →
    ∀ (Φ : X.Isotropy (X.src φ) → Obj → Obj) (Γ : X.Isotropy (X.src φ) → Obj → Mor)
      (Φ' : X.Isotropy (X.tgt φ) → Obj → Obj) (Γ' : X.Isotropy (X.tgt φ) → Obj → Mor),
      IsNatAction X (X.src φ) U Φ Γ → IsConnected U →
      IsNatAction X (X.tgt φ) U' Φ' Γ' → IsConnected U' →
    ∀ (B : X.LocalBranchingStructure Θ (X.src φ)) (B' : X.LocalBranchingStructure Θ (X.tgt φ)),
      B.U = U → B'.U = U' →
      -- `G_x ≅ G_{x'}` by conjugation with `φ`
      (∃ c : X.Isotropy (X.src φ) ≃* X.Isotropy (X.tgt φ),
        ∀ g, (c g).val = X.comp (X.comp φ g.val) (X.inv φ)) ∧
      Nat.card (X.Isotropy (X.src φ)) = Nat.card (X.Isotropy (X.tgt φ)) ∧
      -- `|M_U| = |M_{U'}|`
      X.π '' (⋃ i, B.M i) = X.π '' (⋃ j, B'.M j) ∧
      -- the preimages correspond under `φ̂`
      (∀ K : Set X.OrbitSpace, K ⊆ X.π '' (⋃ i, B.M i) →
        (⋃ j, B'.M j) ∩ X.π ⁻¹' K = (fun y => X.tgt (σ y)) '' ((⋃ i, B.M i) ∩ X.π ⁻¹' K)) ∧
      -- the effective orders, under (LUC)
      (X.IsLUC →
        (∀ c : X.Isotropy (X.src φ) ≃* X.Isotropy (X.tgt φ),
          (∀ g, (c g).val = X.comp (X.comp φ g.val) (X.inv φ)) →
          ∀ g, g ∈ X.trivialSubgroup (X.src φ) ↔ c g ∈ X.trivialSubgroup (X.tgt φ)) ∧
        Nat.card (X.EffIsotropy (X.src φ)) = Nat.card (X.EffIsotropy (X.tgt φ)))

end RoundTrip.V9_56
