import Polyfold
/-! Blind formalization of V9_7 (the Springer 2021 book, Part II, §9.1, the restriction remark,
p. 404, and Lemma 9.1.7, p. 405; 2017: Lemma 9.2, p. 294): restrictions and symmetric local
branching structures.

Text: a local branching structure on `U(x)` restricts to `Nᵢ = Mᵢ ∩ V(x₀)` on `V(x₀) ⊆ U(x)`
with the same weights (some `Nᵢ` may be empty).  For every `x` with `Θ(x) > 0` there are an open
`U(x)` with the natural `G_x`-action, properly embedded submanifolds `(Mᵢ)_{i ∈ I}`, a
`G_x`-action on `I` and weights `σᵢ > 0` with (1) `g ∗ Mᵢ = M_{g(i)}`, (2) `σᵢ = σ_{g(i)}`,
(3) `Θ(y) = ∑_{y ∈ Mᵢ} σᵢ` on `U(x)`; the proof uses `J = I × G_x`, `M_{(i,g)} = g ∗ Mᵢ`,
`σ_{(i,g)} = σᵢ / |G_x|`.

Choices:
- Setting: `Obj Mor : Type` (universe 0), the project's `X : EpGroupoid Obj Mor`.  Local
  branching structures, branched ep⁺-subgroupoids: my `IsLBSB`, `IsBranchedB` (copied from
  `RoundTrip/Blind/V9_1.lean`; proper inclusions read as "compact sets have compact preimages").
- (R) The restriction: for a structure `(U, Mᵢ, σᵢ)` at `x`, a point `x₀ ∈ U` and an open `V`
  with `x₀ ∈ V ⊆ U`, the `Nᵢ = Mᵢ ∩ V` with the same `σᵢ` satisfy everything of Definition 9.1.2
  (2)–(4) on `V` except passing through a point (`IsLocalRepB`: `Nᵢ ⊆ V` submanifolds, possibly
  empty, with proper inclusions, `σᵢ > 0`, `Θ(y) = ∑_{y ∈ Nᵢ} σᵢ` on `V`).  No hypothesis on `Θ`
  besides the structure.
- `G_x` and "the natural `G_x`-action" on `U(x)`: my `Gx` and `IsNatRepData` (copied from
  `RoundTrip/Blind/V7_17.lean`: the data `Φ, Γ` of Theorem 7.1.13 [2017: 7.1] on `U`; `g ∗ y` is
  `Φ g y`; `U` is not asked to be connected).  A `G_x`-action on `I`: a map
  `act : G_x → I → I` with `act(g ∘ h) = act g ∘ act h` and `act(1_x) = id` (`IsActionB`).
- (L) Lemma 9.1.7: "properly embedded submanifolds `(Mᵢ)` ... with (3)" is read as a local
  branching structure at `x` on `U(x)` (in particular the `Mᵢ` pass through `x`; the lemma is used
  as giving local branching structures).  (1) is `Φ g '' Mᵢ = M_{act g i}`, (2)
  `σ_{act g i} = σᵢ`.  Hypothesis: `Θ` is a branched ep⁺-subgroupoid and `Θ(x) > 0`.
- (C) The construction of the proof, as a claim: given a structure `(U', Mᵢ, σᵢ)` at `x` and a
  natural representation on an open `U ∋ x` inside `U'` (`g ∗ Mᵢ` only makes sense where the
  action is defined, so I use `Mᵢ ∩ U`), the family `M_{(i,g)} = Φ g '' (Mᵢ ∩ U)`,
  `σ_{(i,g)} = σᵢ / |G_x|`, indexed by `J = I × G_x` with `h · (i, g) = (i, h ∘ g)`, is a symmetric
  structure on `U`.  `|G_x|` is `Fintype.card` for a `Fintype (Gx X x)` structure taken as an
  argument (the isotropy groups are finite, 2017 Proposition 7.4, so there is exactly one).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_7
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

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

open Classical in
/-- `(Nᵢ, σᵢ)` represents `Θ` on the open set `V`: submanifolds `Nᵢ ⊆ V` (possibly empty) with
proper inclusions, weights `σᵢ > 0`, `Θ(y) = ∑_{y ∈ Nᵢ} σᵢ` for `y ∈ V`. -/
def IsLocalRepB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) {ι : Type} [Fintype ι]
    (V : Set Obj) (N : ι → Set Obj) (σ : ι → ℚ) : Prop :=
  IsOpen V ∧
  (∀ i, N i ⊆ V ∧ X.PObj.IsSmoothSubmanifold (N i) ∧ IsProperInclB (N i) V) ∧
  (∀ i, 0 < σ i) ∧
  ∀ y ∈ V, Θ y = ∑ i with y ∈ N i, σ i

/-- `act : G_x → I → I` is an action of the group `G_x` (product `g ∘ h`, unit `1_x`). -/
def IsActionB (X : EpGroupoid Obj Mor) (x : Obj) {ι : Type} (act : Gx X x → ι → ι) : Prop :=
  (∀ g h k : Gx X x, k.1 = X.comp g.1 h.1 → ∀ i, act k i = act g (act h i)) ∧
  (∀ e : Gx X x, e.1 = X.unit x → ∀ i, act e i = i)

/-- The conclusion of Lemma 9.1.7: a local branching structure at `x` on the domain `U` of a
natural representation `(Φ, Γ)` of `G_x`, with an action of `G_x` on the index set such that
(1) `g ∗ Mᵢ = M_{g(i)}` and (2) `σ_{g(i)} = σᵢ`. -/
def IsSymB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (x : Obj) (U : Set Obj)
    (Φ : Gx X x → Obj → Obj) (Γ : Gx X x → Obj → Mor) {ι : Type} [Fintype ι]
    (M : ι → Set Obj) (σ : ι → ℚ) (act : Gx X x → ι → ι) : Prop :=
  IsNatRepData X x U Φ Γ ∧ IsLBSB X Θ x U M σ ∧ IsActionB X x act ∧
  (∀ g i, Φ g '' M i = M (act g i)) ∧ (∀ g i, σ (act g i) = σ i)

/-- The product `h ∘ g` in `G_x`. -/
def mulGx (X : EpGroupoid Obj Mor) (x : Obj) (h g : Gx X x) : Gx X x :=
  ⟨X.comp h.1 g.1, by
    refine ⟨?_, ?_⟩
    · rw [X.src_comp _ _ (h.2.1.trans g.2.2.symm)]; exact g.2.1
    · rw [X.tgt_comp _ _ (h.2.1.trans g.2.2.symm)]; exact h.2.2⟩

end

/-- The restriction remark and Lemma 9.1.7 (with the construction of its proof). -/
def B : Prop :=
  -- (R) restriction of a local branching structure to an open `V(x₀) ⊆ U(x)`
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (x : Obj) (ι : Type) [Fintype ι] (U : Set Obj)
    (M : ι → Set Obj) (σ : ι → ℚ), IsLBSB X Θ x U M σ →
      ∀ x₀ ∈ U, ∀ V : Set Obj, IsOpen V → x₀ ∈ V → V ⊆ U →
        IsLocalRepB X Θ V (fun i => M i ∩ V) σ) ∧
  -- (L) Lemma 9.1.7: symmetric local branching structures exist
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), IsBranchedB X Θ →
      ∀ x : Obj, 0 < Θ x →
        ∃ (U : Set Obj) (Φ : Gx X x → Obj → Obj) (Γ : Gx X x → Obj → Mor) (ι : Type)
          (_ : Fintype ι) (M : ι → Set Obj) (σ : ι → ℚ) (act : Gx X x → ι → ι),
          IsSymB X Θ x U Φ Γ M σ act) ∧
  -- (C) the construction of the proof: `J = I × G_x`, `M_{(i,g)} = g ∗ Mᵢ`, `σᵢ / |G_x|`
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), IsBranchedB X Θ →
      ∀ (x : Obj) [Fintype (Gx X x)] (ι : Type) [Fintype ι] (U' : Set Obj)
        (M : ι → Set Obj) (σ : ι → ℚ), IsLBSB X Θ x U' M σ →
        ∀ (U : Set Obj) (Φ : Gx X x → Obj → Obj) (Γ : Gx X x → Obj → Mor),
          IsOpen U → x ∈ U → U ⊆ U' → IsNatRepData X x U Φ Γ →
          IsSymB X Θ x U Φ Γ (fun j : ι × Gx X x => Φ j.2 '' (M j.1 ∩ U))
            (fun j => σ j.1 / (Fintype.card (Gx X x) : ℚ))
            (fun h j => (j.1, mulGx X x h j.2)))

end RoundTrip.V9_7
