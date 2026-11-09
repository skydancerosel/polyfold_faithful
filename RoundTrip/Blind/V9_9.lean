import Polyfold
/-! Blind formalization of V9_9 (the Springer 2021 book, Part II, §9.1, Proposition 9.1.11,
pp. 407–408; 2017: Proposition 9.2, p. 297): the dimensional decomposition.

Text: a branched ep⁺-subgroupoid `Θ` determines a unique sequence `Θ₀, Θ₁, …` of branched
ep⁺-subgroupoids characterized by (1) `Θ_k` is `k`-dimensional and (2) `Θ = Θ₀ + Θ₁ + ⋯`, the
sum locally finite.  (Proof: at `x ∈ supp Θ` take a symmetric structure, split
`I = I₀ ⊔ ⋯ ⊔ I_n` by the dimension of the `Mᵢ`, `Θ_k(y) = ∑_{i ∈ I_k, y ∈ Mᵢ} σᵢ`; independence
of the structure is Proposition 9.1.12.)

Choices:
- Setting: `Obj Mor : Type` (universe 0), the project's `X : EpGroupoid Obj Mor`.
- "branched ep⁺-subgroupoid": my `IsBranchedB` (copied from `RoundTrip/Blind/V9_1.lean`, choices
  recorded there).  "`k`-dimensional": my `IsNDimB` (copied from `RoundTrip/Blind/V9_2.lean`:
  every point of the support has SOME local branching structure all of whose sheets have
  dimension `k`, the dimension of `T_mMᵢ` read in a chart).
- "unique sequence ... characterized by (1), (2)": `∃!` of a family `Θk : ℕ → Obj → ℚ` with
  (1) every `Θk k` a `k`-dimensional branched ep⁺-subgroupoid, (2) `Θ(y) = ∑ᶠ_k Θ_k(y)` for every
  object `y`, and "locally finite": every object has a neighbourhood on which only finitely many
  `Θ_k` are not identically zero (in `X`; since the `Θ_k` are functors and `π` is open this is the
  same as in `|X|`).
- The proof sketch is not part of B.
- FALSE AS STATED (I believe): the uniqueness fails.  In the trivial ep-groupoid of `ℝ²`, the
  indicator `Θ = 1_L` of the line `L = ℝ × 0` has the decompositions `Θ₁ = 1_L`, `Θ_k = 0`
  otherwise, and `Θ₀ = 1_{0}`, `Θ₁ = 1_{L ∖ 0}`, `Θ_k = 0` otherwise (`{0}` is a `0`-dimensional
  submanifold, `L ∖ 0` is properly embedded in `ℝ² ∖ 0`).  What the proof shows is that the
  construction does not depend on the structure.  I formalize the statement literally (with `∃!`).
  (The project's vocabulary docstring of `Proposition_9_1_11` says the same; I had noticed it
  while grepping the vocabulary.)
-/
namespace RoundTrip.V9_9
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

/-- `Θ` is `n`-dimensional (copied from `RoundTrip/Blind/V9_2.lean`). -/
def IsNDimB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (n : ℕ) : Prop :=
  ∀ x ∈ suppB Θ, ∃ (ι : Type) (_ : Fintype ι) (U : Set Obj) (M : ι → Set Obj) (σ : ι → ℚ),
    IsLBSB X Θ x U M σ ∧ ∀ i, ∀ m ∈ M i, HasDimB X.PObj (M i) m n

/-- The family `(Θ_k)` is locally finite. -/
def IsLocFinB (Θk : ℕ → Obj → ℚ) : Prop :=
  ∀ y : Obj, ∃ W ∈ nhds y, {k | ∃ z ∈ W, Θk k z ≠ 0}.Finite

/-- (1) and (2) of Proposition 9.1.11. -/
def IsDimDecompB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (Θk : ℕ → Obj → ℚ) : Prop :=
  (∀ k, IsBranchedB X (Θk k) ∧ IsNDimB X (Θk k) k) ∧ IsLocFinB Θk ∧
    ∀ y : Obj, Θ y = ∑ᶠ k, Θk k y

end

/-- Proposition 9.1.11: a branched ep⁺-subgroupoid has a unique locally finite decomposition
into `k`-dimensional branched ep⁺-subgroupoids `Θ_k`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ),
    IsBranchedB X Θ → ∃! Θk : ℕ → Obj → ℚ, IsDimDecompB X Θ Θk

end RoundTrip.V9_9
