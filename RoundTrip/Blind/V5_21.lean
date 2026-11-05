import Polyfold
/-! Blind formalization of V5_21 (the text's §5.3, p. 174: the space `Γ^{+,1}_U(P)`).

Text: `Γ^{+,1}_U(P)` is the set of `s ∈ Γ^+(P)` with `supp(s) ⊆ U` and `N(s(x)) ≤ 1` for all `x`;
it is a metric space for `ρ(s, s') = sup_x N(s(x) − s'(x))`, and it is not complete.

Choices:
- This item is a definition plus properties.  B is the conjunction of: (1) the project's
  `Bd.allowableSections N U` is the text's set `Gamma1 Bd N U` written below (for all `N`, `U`);
  (2) `ρ` is a metric on `Γ^{+,1}_U(P)` (finite, nonnegative, `ρ(s, s) = 0`, symmetric,
  `ρ(s, s') = 0 → s = s'`, triangle inequality), for every auxiliary norm `N` and open `U`;
  (3) "not complete".
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`, as in
  `RoundTrip/Blind/V5_7.lean` / `V5_29.lean`.  No tameness, no section `f`: the definition and the
  metric do not involve them.
- `Γ^+(P)`: sc⁺-sections, the project's `Bd.IsScPlusSection` (Definition 2.52, checked with
  `#print`: a section whose principal parts take values in `F₁` and are sc-smooth into `K[1]`).
- `supp(s) = cl{x | s(x) ≠ 0_x}` (`suppB`, my own, the closure in `X`); `N(y) ≤ r` for `y ∈ Y`:
  `y ∈ Y_{0,1}` and `N(y) ≤ r` (`NLe`, as in V5_7, i.e. `N = ∞` off `Y_{0,1}`).  `N : Y_{0,1} → ℝ`
  is a map on the project's type `Bd.One` (the subtype of `Y_{0,1}`).
- `N(s(x) − s'(x))`: `fibDist`, the difference taken in the fibre `(Y_{0,1})_x` (the project's
  submodule `Bd.oneFiber x`, checked: `{v ∈ P⁻¹(x) | v ∈ Y_{0,1}}`; `Bd.toOne` its inclusion into
  `Bd.One`); junk value `0` when `s(x)` or `s'(x)` is not in that fibre (never the case on
  `Γ^{+,1}_U(P)`).  `ρ(s, s') = ⨆_x N(s(x) − s'(x))` (real `iSup`; finiteness is asserted
  separately as `BddAbove`, so the junk value of an unbounded `iSup` is never relied on).
- "Not complete": a metric space is complete if every `ρ`-Cauchy sequence in it `ρ`-converges to a
  point of it.  READING: the text says the space "is not complete"; taken literally for EVERY
  strong bundle, `N` and `U` this is false (e.g. `U = ∅`, or `X = ∅`: then `Γ^{+,1}_U(P) = {0}` is
  complete).  I read it as "not complete in general": NOT every such space is complete, i.e. there
  is a strong bundle, an auxiliary norm `N` and an open `U` for which `(Γ^{+,1}_U(P), ρ)` is not
  complete.  `BUniversal` (NOT the item, only an aid) is the literal universal reading; I believe
  it is false.
- Nothing else looks false to me.
-/
namespace RoundTrip.V5_21
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- `N(y) ≤ r`, with `N(y) = ∞` for `y ∉ Y_{0,1}`. -/
def NLe (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (y : Y) (r : ℝ) : Prop :=
  ∃ hy : y ∈ Bd.oneSet, N ⟨y, hy⟩ ≤ r

/-- The support `supp(s) = cl{x | s(x) ≠ 0_x}` of a section. -/
def suppB (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (s : X → Y) : Set X :=
  closure {x | s x ≠ ((0 : P ⁻¹' {x}) : Y)}

/-- `N(s(x) − s'(x))`, the difference taken in the fibre `(Y_{0,1})_x` (junk `0` if `s(x)` or
`s'(x)` is not a point of that fibre). -/
noncomputable def fibDist (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (s s' : X → Y) (x : X) : ℝ :=
  open Classical in
  if h : (P (s x) = x ∧ P (s' x) = x) ∧ (s x ∈ Bd.oneSet ∧ s' x ∈ Bd.oneSet) then
    N (Bd.toOne ((⟨⟨s x, h.1.1⟩, h.2.1⟩ : Bd.oneFiber x) - ⟨⟨s' x, h.1.2⟩, h.2.2⟩))
  else 0

/-- **`Γ^{+,1}_U(P)`**: the sc⁺-sections `s` with `supp(s) ⊆ U` and `N(s(x)) ≤ 1` for all `x`. -/
def Gamma1 (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (U : Set X) : Set (X → Y) :=
  {s | Bd.IsScPlusSection s ∧ suppB P s ⊆ U ∧ ∀ x, NLe Bd N (s x) 1}

/-- `ρ(s, s') = sup_x N(s(x) − s'(x))`. -/
noncomputable def rho (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (s s' : X → Y) : ℝ :=
  ⨆ x, fibDist Bd N s s' x

/-- `ρ` is a metric on `Γ^{+,1}_U(P)`. -/
def IsRhoMetric (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (U : Set X) : Prop :=
  ∀ s ∈ Gamma1 Bd N U, ∀ s' ∈ Gamma1 Bd N U, ∀ s'' ∈ Gamma1 Bd N U,
    BddAbove (Set.range (fibDist Bd N s s')) ∧
    0 ≤ rho Bd N s s' ∧
    rho Bd N s s = 0 ∧
    rho Bd N s s' = rho Bd N s' s ∧
    (rho Bd N s s' = 0 → s = s') ∧
    rho Bd N s s'' ≤ rho Bd N s s' + rho Bd N s' s''

/-- `(Γ^{+,1}_U(P), ρ)` is complete: every `ρ`-Cauchy sequence in it `ρ`-converges to a point of
it. -/
def IsRhoComplete (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (U : Set X) : Prop :=
  ∀ u : ℕ → X → Y, (∀ n, u n ∈ Gamma1 Bd N U) →
    (∀ ε > 0, ∃ K : ℕ, ∀ m ≥ K, ∀ n ≥ K, rho Bd N (u m) (u n) < ε) →
      ∃ s ∈ Gamma1 Bd N U, ∀ ε > 0, ∃ K : ℕ, ∀ n ≥ K, rho Bd N (u n) s < ε

end

/-- `Γ^{+,1}_U(P)` (the project's `allowableSections` is the text's set); `ρ` is a metric on it
for every auxiliary norm and open `U`; and the metric space is not complete in general. -/
def B : Prop :=
  -- (1) the definition
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (U : Set X),
      Bd.allowableSections N U = Gamma1 Bd N U) ∧
  -- (2) a metric space
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (U : Set X),
      Bd.IsAuxNorm N → IsOpen U → IsRhoMetric Bd N U) ∧
  -- (3) not complete (in general)
  ¬ (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (U : Set X),
      Bd.IsAuxNorm N → IsOpen U → IsRhoComplete Bd N U)

/-- Not the item: the literal universal reading of "not complete" (I believe it is false). -/
def BUniversal : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (U : Set X),
      Bd.IsAuxNorm N → IsOpen U → ¬ IsRhoComplete Bd N U

end RoundTrip.V5_21
