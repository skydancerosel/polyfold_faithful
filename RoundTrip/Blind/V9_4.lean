import Polyfold
/-! Blind formalization of V9_4 (the Springer 2021 book, Part II, §9.1, Remark 9.1.3 (b),
p. 403; 2017: Remark 9.2 (b), p. 292): local branching structures are not unique.

Text: local branching structures are in general not unique, even close to `x`: on `ℝ²` with
identity morphisms only, the graphs `G₁`, `G₂` of smooth `β₁` (`= 0` for `s ≤ 0`, `> 0` for
`s > 0`) and `β₂` (`> 0` for `s < 0`, `= 0` for `s ≥ 0`), with weights `1`, define
`Θ(p) = #{i | p ∈ Gᵢ}`, which is also described by the graphs of `γ₁ = 0` and a `γ₂` with
`γ₂(s) > 0` for `s ≠ 0`.

Choices:
- "`ℝ²` with identity morphisms only": the project's trivial ep-groupoid
  `EpGroupoid.trivial (rnPolyfold 2)` of the M-polyfold `ℝ² = Fin 2 → ℝ` (vocabulary: `𝐗 = X = Z`,
  all structure maps the identity; `rnPolyfold 2` is `ℝ²` with the chart `id`).  Points
  `p = (p 0, p 1)`; the graph of `β` is `{p | p 1 = β (p 0)}`.
- "smooth": `ContDiff ℝ (⊤ : ℕ∞)` (`C^∞`).  The text's `G₁, G₂` are indexed by `Fin 2`
  (`0 ↦ G₁`, `1 ↦ G₂`), likewise `γ₁, γ₂`.
- "branched ep⁺-subgroupoid", "local branching structure": my `IsBranchedB`, `IsLBSB` (copied
  from `RoundTrip/Blind/V9_1.lean`).
- Claims, as I read the remark: (a) `Θ` is a branched ep⁺-subgroupoid, and at every point `x` of
  its support the graphs through `x`, cut down to some open `U ∋ x`, with weights `1`, form a local
  branching structure ("with weights 1, define `Θ`"); at `x = 0` the two graphs on `U = ℝ²` do.
  (b) there is a smooth `γ₂` with `γ₂(s) > 0` for `s ≠ 0` such that `Θ(p) = #{i | p ∈ graph γᵢ}`
  for all `p`, and the graphs of `γ₁ = 0`, `γ₂` on `U = ℝ²` with weights `1` are a local branching
  structure of `Θ` at `0` ("also described by").  (c) "not unique, even close to `x`" (`x = 0`, the
  only point where the graphs meet): on no open `V ∋ 0` do the two families restrict to the same
  family of sets, `{G₁ ∩ V, G₂ ∩ V} ≠ {Γ₁ ∩ V, Γ₂ ∩ V}`.
- `γ₂` is existential (the text: "a `γ₂`"; presumably `γ₂ = β₁ + β₂`).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_4
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

/-- `ℝ²` with identity morphisms only. -/
noncomputable abbrev X2 : EpGroupoid (Fin 2 → ℝ) (Fin 2 → ℝ) :=
  EpGroupoid.trivial (rnPolyfold 2)

/-- The graph `{(s, β(s))}` of `β : ℝ → ℝ` in `ℝ²`. -/
def graphB (β : ℝ → ℝ) : Set (Fin 2 → ℝ) := {p | p 1 = β (p 0)}

/-- The hypotheses on `β₁`, `β₂`. -/
def HypB (β₁ β₂ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) β₁ ∧ ContDiff ℝ (⊤ : ℕ∞) β₂ ∧
  (∀ s : ℝ, s ≤ 0 → β₁ s = 0) ∧ (∀ s : ℝ, 0 < s → 0 < β₁ s) ∧
  (∀ s : ℝ, s < 0 → 0 < β₂ s) ∧ (∀ s : ℝ, 0 ≤ s → β₂ s = 0)

open Classical in
/-- `Θ(p) = #{i | p ∈ Gᵢ}` for a pair of sets `G₀, G₁`. -/
noncomputable def countB (G : Fin 2 → Set (Fin 2 → ℝ)) (p : Fin 2 → ℝ) : ℚ :=
  ((Finset.univ.filter (fun i => p ∈ G i)).card : ℚ)

open Classical in
/-- Remark 9.1.3 (b). -/
def B : Prop :=
  ∀ β₁ β₂ : ℝ → ℝ, HypB β₁ β₂ →
    -- (a) `Θ` is a branched ep⁺-subgroupoid with the graph structures, weights `1`
    IsBranchedB X2 (countB ![graphB β₁, graphB β₂]) ∧
    (∀ x ∈ suppB (countB ![graphB β₁, graphB β₂]), ∃ U : Set (Fin 2 → ℝ),
      IsLBSB X2 (countB ![graphB β₁, graphB β₂]) x U
        (fun i : {i : Fin 2 // x ∈ ![graphB β₁, graphB β₂] i} =>
          ![graphB β₁, graphB β₂] i.1 ∩ U) (fun _ => 1)) ∧
    IsLBSB X2 (countB ![graphB β₁, graphB β₂]) 0 Set.univ ![graphB β₁, graphB β₂] (fun _ => 1) ∧
    -- (b) the same `Θ` by the graphs of `γ₁ = 0` and `γ₂`
    ∃ γ₂ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) γ₂ ∧ (∀ s : ℝ, s ≠ 0 → 0 < γ₂ s) ∧
      (∀ p, countB ![graphB β₁, graphB β₂] p = countB ![graphB 0, graphB γ₂] p) ∧
      IsLBSB X2 (countB ![graphB β₁, graphB β₂]) 0 Set.univ ![graphB 0, graphB γ₂]
        (fun _ => 1) ∧
      -- (c) the two structures differ on every neighbourhood of `0`
      ∀ V : Set (Fin 2 → ℝ), IsOpen V → (0 : Fin 2 → ℝ) ∈ V →
        ({graphB β₁ ∩ V, graphB β₂ ∩ V} : Set (Set (Fin 2 → ℝ))) ≠
          {graphB 0 ∩ V, graphB γ₂ ∩ V}

end RoundTrip.V9_4
