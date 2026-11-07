import Polyfold
/-! Blind formalization of V6_30 (the text's §6.5, Proposition 6.26, p. 219).

Text: `DET(f, x) = ⋃_{L ∈ Lin(f,x)} {L} × det(L)` has in a natural way the structure of a
topological line bundle over `Lin(f, x)`, and two possible orientations, the base being convex,
hence contractible.

Choices:
- Setting: `X Y : Type` (universe 0); `PX : MPolyfold X`, `P : Y → X` with the fibrewise linear
  structure as instances on the fibres, `Bd : StrongBundle PX P` (as in the earlier blind files,
  e.g. `RoundTrip/Blind/V5_31.lean`); `f` an sc-Fredholm section (`IsScFredholmSection`) and `x` a
  smooth point (`x ∈ PX.smoothSet`; `Lin(f, x)` is defined at smooth points, Definition 6.1).
  No tameness and no bump functions: the text assumes neither.
- `T_xX → Y_x` is read in a strong bundle chart: B quantifies over all the project's chart points
  `p : ChartPoint Bd x` (a chart of the atlas around `x` and the level-`1` lift `z` of `φ(x)`;
  `T_xX = T_zO = p.T`, `Y_x = K_z = p.K`).
- `Lin(f, x)`: the project's `ChartPoint.linSet f p` (checked with `#print`: the operators
  `(f + s)'(x) + a : T_zO → K_z` for an sc⁺-section `s` with `(f + s)(x) = 0` and an sc⁺-operator
  `a`; the text's `(f − s)'(x) + a` with `s(x) = f(x)`).  It is a subset of the normed space
  `L(T_zO, K_z)`; "convex" and "contractible" are for this set with the norm topology.
  The sc⁺-section `s` is a global sc⁺-section of `P` in the project's definition.  If no
  sc⁺-section through `f(x)` exists, `Lin(f, x)` is empty, it is not contractible, and the line
  bundle over it has exactly one orientation; the text takes `Lin(f, x) ≠ ∅` for granted.  B is
  stated literally, without a nonemptiness hypothesis (see the report).
- `DET(f, x)`: the project's `ChartPoint.detLin f p hf` (checked with `#print`: `DetOn` of
  `Lin(f, x)`, the pull-back of `DET(T_zO, K_z)` along the inclusion `Lin(f, x) → F(T_zO, K_z)`).
  "Has in a natural way the structure of a topological line bundle": with this (pull-back)
  topology it is a vector bundle with fibre `ℝ`: `VectorBundle ℝ ℝ (ChartPoint.detLin f p hf)`
  for the pull-back fibre bundle structure (the instance is found by `#synth`; so this conjunct is
  close to definitional).
- "two possible orientations": the orientations of this line bundle (`LineOrientation`, checked
  with `#print`: a ray of every fibre, locally that of a continuous nowhere vanishing section) are
  exactly two: `Nat.card = 2`.
- The text gives convexity and contractibility as the reason; both are claims of the text, so
  both are conjuncts.
- Nothing looks false to me (modulo the nonemptiness of `Lin(f, x)` above).
-/
namespace RoundTrip.V6_30
open Polyfold

/-- Proposition 6.26: `Lin(f, x)` is convex and contractible, `DET(f, x)` is a topological line
bundle over it, and it has exactly two orientations. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f) (x : X),
    x ∈ PX.smoothSet → ∀ p : ChartPoint Bd x,
      Convex ℝ (p.linSet f) ∧ ContractibleSpace ↥(p.linSet f) ∧
      VectorBundle ℝ ℝ (ChartPoint.detLin f p hf) ∧
      Nat.card (LineOrientation (ChartPoint.detLin f p hf)) = 2

end RoundTrip.V6_30
