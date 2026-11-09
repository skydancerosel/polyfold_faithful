import Polyfold
/-! Blind formalization of V9_13 (the Springer 2021 book, Part II, §9.2, Theorem 9.2.1, p. 409;
2017: Theorem 9.1, p. 298): the tangent section `T_Θ`.

Text: associated with a branched ep⁺-subgroupoid `Θ` there is a natural section functor
`T_Θ : X^∞ → Gr(X)`, `π ∘ T_Θ = Id`, characterized by (1) `T_Θ(x) = ∑ᵢ σᵢ T_xMᵢ` for any local
branching structure at `x ∈ supp(Θ)`, the zero sum otherwise, and
(2) `T_Θ(φ) = (T_Θ(s(φ)), φ)`.

Choices:
- Setting: `Obj Mor : Type` (universe 0), the project's `X : EpGroupoid Obj Mor`; `Θ` a branched
  ep⁺-subgroupoid and its local branching structures: my `IsBranchedB`, `IsLBSB` (copied from
  `RoundTrip/Blind/V9_1.lean`).
- `T_xMᵢ = Tr(x)(T_xX)` (2021 p. 409): my `TyMB`, the image of the vectors over `x` under the
  project's `d.tmap = Tr` for some data `d` of Part I's Definition 4.13 at `x` (union over the
  data; it does not depend on them, `RoundTrip/Blind/V9_12.lean`).
- `Gr(x)`, `Gr(X)`, `φ_*`: as in my `RoundTrip/Blind/V9_11.lean` (`GrB`: finitely supported
  `ℚ`-weights on finite-dimensional linear subspaces of `T_xX`, linearity read in a chart;
  `pushB φ (∑ σ_L L) = ∑ σ_L Tφ(L)` with the project's `tangentMor`; morphisms
  `(x, a) → (y, φ_* a)` of `Gr(X)` are the pairs `(a, φ)`).  The formal sum `∑ᵢ σᵢ T_xMᵢ` is
  `∑ᵢ single (T_xMᵢ) σᵢ` (equal tangent spaces add their weights).
- What the theorem asserts, as I read it: (1) is a definition only if `∑ᵢ σᵢ T_xMᵢ` is the same
  for ANY two local branching structures at `x` (with any domains), and it must lie in `Gr(x)`;
  (2) defines a morphism of `Gr(X)` exactly when `φ_*(T_Θ(s φ)) = T_Θ(t φ)` for every morphism
  `φ` (between smooth objects).  Off the support (`Θ(x) = 0`) `T_Θ(x) = 0`, `0 ∈ Gr(x)`, and
  `φ_* 0 = 0`; since `Θ` is a functor, `s φ ∈ supp Θ ↔ t φ ∈ supp Θ`, so the condition is stated
  for any structures at `s φ` and `t φ` (which exist only on the support, or with empty index
  sets).  Given these, `x ↦ (x, T_Θ(x))`, `φ ↦ (T_Θ(s φ), φ)` is a functor (morphisms of `Gr(X)`
  are determined by their `φ`) with `π ∘ T_Θ = Id`; B is the conjunction of (1), the membership
  and the morphism condition.  "Natural" is not formalized further.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_13
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

/-- The chart image `{h | (φ(y), h) = Tφ(α), α ∈ S}` of a set `S` of tangent vectors. -/
def chartImgB {P : MPolyfold Z} {φ : MChart Z} (hφ : P.IsChart φ) (S : Set P.TangentSpace) :
    Set (φ.model.E.lvl 0) :=
  (fun α => (MPolyfold.tangentChartMap hφ α).2) '' S

/-- `L` is a finite-dimensional linear subspace of `T_yX`: `L ⊆ T_yX`, and in a chart `φ` around
`y` (through which `T_yX` is identified with the linear subspace `T_{φ(y)}O` of `E₀`) `L` is a
finite-dimensional linear subspace. -/
def IsFinDimSubspaceB (P : MPolyfold Z) (y : Z) (L : Set P.TangentSpace) : Prop :=
  L ⊆ TxXB P y ∧
    ∃ (φ : MChart Z) (hφ : P.IsChart φ), y ∈ φ.source ∧
      ∃ S : Submodule ℝ (φ.model.E.lvl 0), FiniteDimensional ℝ S ∧
        chartImgB hφ L = (S : Set (φ.model.E.lvl 0))

end

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `Gr(x)`: the finite formal sums `∑ σ_L · L` (`σ_L ∈ ℚ`) of finite-dimensional linear
subspaces `L ⊆ T_xX`, as finitely supported weights on sets of tangent vectors. -/
def GrB (X : EpGroupoid Obj Mor) (x : Obj) : Set (Set X.PObj.TangentSpace →₀ ℚ) :=
  {a | ∀ L ∈ a.support, IsFinDimSubspaceB X.PObj x L}

/-- The image `∑ σ_L · Tφ(L)` of a formal sum under (the tangent `Tφ` of) a morphism `φ`. -/
noncomputable def pushB (X : EpGroupoid Obj Mor) (φ : Mor) (a : Set X.PObj.TangentSpace →₀ ℚ) :
    Set X.PObj.TangentSpace →₀ ℚ :=
  Finsupp.mapDomain (fun L => X.tangentMor φ '' L) a

end

section
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]

/-- `T_yM = Tr(y)(T_yX)` for the sc⁺-retractions `r` of the data of Definition 4.13 of `M` at
`y` (union over the data). -/
def TyMB (P : MPolyfold Z) (M : Set Z) (y : Z) : Set P.TangentSpace :=
  {α | ∃ d : P.SubmanifoldData M, y ∈ d.V ∧ ∃ β ∈ TxXB P y, d.tmap β = α}

/-- The formal sum `∑ᵢ σᵢ · T_xMᵢ`. -/
noncomputable def tsumB (P : MPolyfold Z) {ι : Type} [Fintype ι] (M : ι → Set Z) (σ : ι → ℚ)
    (x : Z) : Set P.TangentSpace →₀ ℚ :=
  ∑ i, Finsupp.single (TyMB P (M i) x) (σ i)

end

/-- Theorem 9.2.1: `∑ σᵢ T_xMᵢ` does not depend on the local branching structure, lies in
`Gr(x)`, and is carried by every morphism `φ` from `s φ` to `t φ`; so `T_Θ` is a section functor
`X^∞ → Gr(X)`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), IsBranchedB X Θ →
    -- (1) `T_Θ(x)` is independent of the local branching structure at `x`
    (∀ (x : Obj) (ι ι' : Type) [Fintype ι] [Fintype ι'] (U U' : Set Obj)
      (M : ι → Set Obj) (σ : ι → ℚ) (M' : ι' → Set Obj) (σ' : ι' → ℚ),
      IsLBSB X Θ x U M σ → IsLBSB X Θ x U' M' σ' →
        tsumB X.PObj M σ x = tsumB X.PObj M' σ' x) ∧
    -- `T_Θ(x) ∈ Gr(x)`
    (∀ (x : Obj) (ι : Type) [Fintype ι] (U : Set Obj) (M : ι → Set Obj) (σ : ι → ℚ),
      IsLBSB X Θ x U M σ → tsumB X.PObj M σ x ∈ GrB X x) ∧
    -- (2) `(T_Θ(s φ), φ)` is a morphism `T_Θ(s φ) → T_Θ(t φ)` of `Gr(X)`
    (∀ (φ : Mor) (ι ι' : Type) [Fintype ι] [Fintype ι'] (U U' : Set Obj)
      (M : ι → Set Obj) (σ : ι → ℚ) (M' : ι' → Set Obj) (σ' : ι' → ℚ),
      IsLBSB X Θ (X.src φ) U M σ → IsLBSB X Θ (X.tgt φ) U' M' σ' →
        pushB X φ (tsumB X.PObj M σ (X.src φ)) = tsumB X.PObj M' σ' (X.tgt φ))

end RoundTrip.V9_13
