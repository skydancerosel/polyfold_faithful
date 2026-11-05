import Polyfold
/-! Blind formalization of V5_22 (the text's §5.3, Remark 5.12, p. 174).

Text: if `s` is in the completion of `Γ^{+,1}_U(P)`, the solution set of `f + s = 0` is still
compact, provided `f` has a compact solution set and `U` is adapted to `N`.

Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`, as in
  `RoundTrip/Blind/V5_21.lean` (the definition of `Γ^{+,1}_U(P)`, whose prelude I reuse).
- `f`: the sc-Fredholm section of §5.3 (presupposed: the remark is about "the" section `f` of the
  section; some continuity of `f` is needed for the claim): the project's
  `Bd.IsScFredholmSection f` (Definition 3.14, checked with `#print` in earlier blind files).  No
  tameness: the remark does not say "tame" and nothing in it needs it (Lemma 5.11, which does,
  states tameness explicitly).
- `N`: an auxiliary norm, `Bd.IsAuxNorm N` (Definition 5.1).  "Compact solution set":
  `{x | f(x) = 0_x}` compact in `X`.
- "`U` adapted to `N`": READING.  I take it to be the neighbourhood of Definition 5.4 (3)
  (properness), which Theorem 5.5 provides for an sc-Fredholm `f` with compact solution set over a
  tame `X`: `U` is open, contains `f⁻¹(0)`, and `cl_X{x ∈ U | N(f(x)) ≤ 1}` is compact (with
  `N(f(x)) = ∞` off `Y_{0,1}`).  With this reading the remark is the elementary observation
  `S_{f+s} ⊆ {x ∈ U | N(f(x)) ≤ 1}` (`s = 0` off `U`, `N(f(x)) = N(−s(x)) ≤ 1` on `S_{f+s}`).
  The other possible reading — `U` the neighbourhood of Definition 5.4 (2) (`S_{f+s}` compact for
  every `s ∈ Γ^{+,1}_U(P)`) — would be a weaker hypothesis, hence a stronger claim; I did not use
  it.
- `Γ^{+,1}_U(P)`: `Gamma1` (as in V5_21: sc⁺-sections, `Bd.IsScPlusSection`, Definition 2.52,
  with `cl{s ≠ 0} ⊆ U` and `N(s(x)) ≤ 1` for all `x`).
- "the completion of `Γ^{+,1}_U(P)`" (for the metric `ρ(s, s') = sup_x N(s(x) − s'(x))`): its
  points are identified with sections, as the text does when it speaks of `f + s`: since every fibre
  `(Y_{0,1})_x` is complete for `N` (Definition 5.1 (1)), a `ρ`-Cauchy sequence converges uniformly
  (in `N`) to a section `s : X → Y_{0,1}`, and conversely.  So `s` is in the completion iff `s` is
  a section of `P` with values in `Y_{0,1}` such that for every `ε > 0` some `s' ∈ Γ^{+,1}_U(P)`
  has `N(s(x) − s'(x)) ≤ ε` for all `x` (`InCompletion`; `fibDist` is the difference in the fibre
  `(Y_{0,1})_x`, the project's `Bd.oneFiber x`).
- "the solution set of `f + s = 0`": `{x | (f + s)(x) = 0_x}`, `f + s` the fibrewise sum, the
  project's `sectionAdd` (checked: the sum in `P⁻¹(x)`); compact in `X`.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_22
open Polyfold

/-- The solution set `S_g = {x | g(x) = 0_x}`. -/
def solSet {X Y : Type} (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (g : X → Y) : Set X :=
  {x | g x = ((0 : P ⁻¹' {x}) : Y)}

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

/-- `s` is (the section representing) a point of the `ρ`-completion of `Γ^{+,1}_U(P)`: a section
with values in `Y_{0,1}` which is a uniform `N`-limit of elements of `Γ^{+,1}_U(P)`. -/
def InCompletion (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (U : Set X) (s : X → Y) : Prop :=
  IsSection P s ∧ (∀ x, s x ∈ Bd.oneSet) ∧
    ∀ ε > 0, ∃ s' ∈ Gamma1 Bd N U, ∀ x, fibDist Bd N s s' x ≤ ε

/-- `U` is adapted to `N` (for `f`): an open neighbourhood of `f⁻¹(0)` with
`cl_X{x ∈ U | N(f(x)) ≤ 1}` compact (Definition 5.4 (3)). -/
def IsAdapted (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (f : X → Y) (U : Set X) : Prop :=
  IsOpen U ∧ solSet P f ⊆ U ∧ IsCompact (closure {x | x ∈ U ∧ NLe Bd N (f x) 1})

end

/-- Remark 5.12: for an sc-Fredholm section with compact solution set, an auxiliary norm `N` and
`U` adapted to `N`, every `s` in the completion of `Γ^{+,1}_U(P)` gives a compact solution set of
`f + s = 0`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (N : Bd.One → ℝ) (U : Set X),
    Bd.IsScFredholmSection f → IsCompact (solSet P f) → Bd.IsAuxNorm N → IsAdapted Bd N f U →
      ∀ s : X → Y, InCompletion Bd N U s → IsCompact (solSet P (sectionAdd P f s))

end RoundTrip.V5_22
