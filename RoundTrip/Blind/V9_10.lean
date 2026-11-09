import Polyfold
/-! Blind formalization of V9_10 (the Springer 2021 book, Part II, §9.1, Proposition 9.1.12,
p. 408, new in the 2021 edition; proof in §9.6.1, pp. 452–457): the dimensional decomposition
does not depend on the structure.

Text: for two local branching structures of `Θ` on `U(x)` there is an open `G_x`-invariant
`V(x) ⊆ U(x)` (with the usual properties) on which the two dimensional decompositions `Θ_k`
agree.

Choices:
- Setting: `Obj Mor : Type` (universe 0), the project's `X : EpGroupoid Obj Mor`; `Θ` a branched
  ep⁺-subgroupoid (my `IsBranchedB`, copied from `RoundTrip/Blind/V9_1.lean`), `x` an object.
- "two local branching structures of `Θ` on `U(x)`": two structures at `x` (my `IsLBSB` of V9_1)
  with the SAME open domain `U` (literal; different domains reduce to this by the restriction
  remark), with arbitrary finite index types `ι`, `ι'`.
- "the dimensional decomposition" of a structure (from the proof of Proposition 9.1.11:
  `Θ_k(y) = ∑_{i ∈ I_k, y ∈ Mᵢ} σᵢ`, `I_k` the indices of the `k`-dimensional `Mᵢ`): I use the
  pointwise local dimension, `Θ_k(y) = ∑ σᵢ` over the `i` with `y ∈ Mᵢ` and `dim T_yMᵢ = k`
  (`dimPartB`; the dimension read in a chart, `HasDimB`, copied from `RoundTrip/Blind/V9_2.lean`).
  When every `Mᵢ` has one dimension this is the text's formula; it needs no constant-dimension
  hypothesis (near `x` every `Mᵢ` has constant dimension, Remark 9.1.1).
- "open `G_x`-invariant `V(x)` (with the usual properties)": an open `V` with `x ∈ V ⊆ U` that
  is the domain of a natural representation of `G_x` (Theorem 7.1.13 [2017: 7.1]; my
  `IsNatRepData`, copied from `RoundTrip/Blind/V7_17.lean`: every `Φ(g)` an sc-diffeomorphism of
  `V` onto `V`, so `V` is `G_x`-invariant).  "The usual properties" is read as the properties of
  Theorem 7.1.13.
- "agree": `Θ_k(y) = Θ'_k(y)` for all `k` and `y ∈ V`.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_10
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `supp(Θ) = {x | Θ(x) > 0}`. -/
def suppB (Θ : Obj → ℚ) : Set Obj := {x | 0 < Θ x}

/-- The inclusion `A → U` is proper: preimages of compact subsets of `U` are compact. -/
def IsProperInclB (A U : Set Obj) : Prop :=
  ∀ K : Set Obj, K ⊆ U → IsCompact K → IsCompact (K ∩ A)

open Classical in
/-- **Definition 9.1.2 (2)–(4)**: `(U, (Mᵢ)_{i ∈ ι}, (σᵢ)_{i ∈ ι})` is a local branching structure
of `Θ` at `x`. -/
def IsLBSB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (x : Obj) {ι : Type} [Fintype ι]
    (U : Set Obj) (M : ι → Set Obj) (σ : ι → ℚ) : Prop :=
  IsOpen U ∧ x ∈ U ∧
  (∀ i, M i ⊆ U ∧ X.PObj.IsSmoothSubmanifold (M i) ∧ x ∈ M i ∧ IsProperInclB (M i) U) ∧
  (∀ i, 0 < σ i) ∧
  ∀ y ∈ U, Θ y = ∑ i with y ∈ M i, σ i

/-- **Definition 9.1.2**: `Θ` is a branched ep⁺-subgroupoid of `X`. -/
def IsBranchedB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) : Prop :=
  -- `Θ : X → ℚ⁺` is a functor
  (∀ x, 0 ≤ Θ x) ∧ (∀ φ : Mor, Θ (X.src φ) = Θ (X.tgt φ)) ∧
  -- (1)
  suppB Θ ⊆ X.PObj.smoothSet ∧ ParacompactSpace ↥(X.π '' suppB Θ) ∧
  -- (2)–(4) at every point of the support
  ∀ x ∈ suppB Θ, ∃ (ι : Type) (_ : Fintype ι) (U : Set Obj) (M : ι → Set Obj) (σ : ι → ℚ),
    IsLBSB X Θ x U M σ

end

section
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]

/-- `T_yX`: the tangent vectors over `y` (the fibre of `p : TX → X¹` over `y ∈ X₁`). -/
def TxXB (P : MPolyfold Z) (y : Z) : Set P.TangentSpace :=
  {α | P.levelVal 1 (P.tangentProj α) = y}

/-- `T_yM = Tr(y)(T_yX)` for the sc⁺-retractions `r` of the data of Definition 4.13 of `M` at
`y` (the union over all such data; by Part I it does not depend on the data). -/
def TyMB (P : MPolyfold Z) (M : Set Z) (y : Z) : Set P.TangentSpace :=
  {α | ∃ d : P.SubmanifoldData M, y ∈ d.V ∧ ∃ β ∈ TxXB P y, d.tmap β = α}

/-- The chart image `{h | (φ(y), h) = Tφ(α), α ∈ S}` of a set `S` of tangent vectors. -/
def chartImgB {P : MPolyfold Z} {φ : MChart Z} (hφ : P.IsChart φ) (S : Set P.TangentSpace) :
    Set (φ.model.E.lvl 0) :=
  (fun α => (MPolyfold.tangentChartMap hφ α).2) '' S

/-- Remark 9.1.1: `M` has (local) dimension `n` at `y`: in a chart `φ` around `y`, `T_yM` is an
`n`-dimensional linear subspace of `E`. -/
def HasDimB (P : MPolyfold Z) (M : Set Z) (y : Z) (n : ℕ) : Prop :=
  ∃ (φ : MChart Z) (hφ : P.IsChart φ), y ∈ φ.source ∧
    ∃ S : Submodule ℝ (φ.model.E.lvl 0), FiniteDimensional ℝ S ∧
      chartImgB hφ (TyMB P M y) = (S : Set (φ.model.E.lvl 0)) ∧ Module.finrank ℝ S = n

end

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The isotropy group `G_x`: the morphisms `x → x` (as in `RoundTrip/Blind/V7_17.lean`). -/
def Gx (X : EpGroupoid Obj Mor) (x : Obj) : Type := {g : Mor // X.src g = x ∧ X.tgt g = x}

/-- The natural representation of `G_x` on `U` (Theorem 7.1.13 [2017: 7.1]; copied from
`RoundTrip/Blind/V7_17.lean`): `Φ : G_x → Diff_sc(U)` a homomorphism, `Γ : G_x × U → 𝐗`
sc-smooth with (1) `Γ(g, x) = g`, (2) `s Γ(g, y) = y`, `t Γ(g, y) = Φ(g)(y)`, (3) `Γ` bijective
onto the morphisms between points of `U`. -/
def IsNatRepData (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj)
    (Φ : Gx X x → Obj → Obj) (Γ : Gx X x → Obj → Mor) : Prop :=
  (∀ g : Gx X x, ∃ ψ : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj (Φ g) ψ U U) ∧
  (∀ g h k : Gx X x, k.1 = X.comp g.1 h.1 → ∀ y ∈ U, Φ k y = Φ g (Φ h y)) ∧
  (∀ g : Gx X x, X.PObj.IsScSmoothOn X.PMor (Γ g) U) ∧
  (∀ g : Gx X x, Γ g x = g.1) ∧
  (∀ g : Gx X x, ∀ y ∈ U, X.src (Γ g y) = y ∧ X.tgt (Γ g y) = Φ g y) ∧
  (∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃! g : Gx X x, Γ g (X.src h) = h) ∧
  Set.BijOn (fun p : Gx X x × Obj => Γ p.1 p.2) (Set.univ ×ˢ U)
    {φ : Mor | X.src φ ∈ U ∧ X.tgt φ ∈ U}

end

open Classical in
/-- The `k`-dimensional part `Θ_k(y) = ∑_{i : y ∈ Mᵢ, dim T_yMᵢ = k} σᵢ` of a structure. -/
noncomputable def dimPartB {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (P : MPolyfold Z) {ι : Type} [Fintype ι] (M : ι → Set Z) (σ : ι → ℚ) (k : ℕ) (y : Z) : ℚ :=
  ∑ i with y ∈ M i ∧ HasDimB P (M i) y k, σ i

/-- Proposition 9.1.12: two local branching structures of `Θ` on `U(x)` have the same
dimensional decomposition on some open `G_x`-invariant `V ∋ x` inside `U(x)` carrying the natural
representation. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), IsBranchedB X Θ →
    ∀ (x : Obj) (ι ι' : Type) [Fintype ι] [Fintype ι'] (U : Set Obj)
      (M : ι → Set Obj) (σ : ι → ℚ) (M' : ι' → Set Obj) (σ' : ι' → ℚ),
      IsLBSB X Θ x U M σ → IsLBSB X Θ x U M' σ' →
      ∃ (V : Set Obj) (Φ : Gx X x → Obj → Obj) (Γ : Gx X x → Obj → Mor),
        IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ IsNatRepData X x V Φ Γ ∧
        ∀ (k : ℕ), ∀ y ∈ V, dimPartB X.PObj M σ k y = dimPartB X.PObj M' σ' k y

end RoundTrip.V9_10
