import Polyfold
/-! Blind formalization of V6_60 (the text's §6.5, Definition 6.40, p. 229).

Text: an orientation of `f` assigns to every smooth `y` an orientation `o^f_y` of `DET(f, y)` such
that, for every smooth `x` and every orientable neighbourhood `U(x)`, the restriction to `U_∞` is
one of the two continuous orientations.

Choices:
- This item is a definition.  B says that, for every map `o : y ↦ o_y ∈ Or_y^f` on the smooth
  points, the project's `IsSectionOrientation f hf o` is the text's notion `D640 f hf o` below.
- Setting as in my `RoundTrip/Blind/V6_59.lean`: `X Y : Type` (universe 0), `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances, `Bd : StrongBundle PX P`, `f` an
  sc-Fredholm section (`Bd.IsScFredholmSection f`, Definition 3.14); the paracompactness
  instances of `ℝⁿ × X` and of the pulled-back bundles are instance binders (true anyway, and
  arguments of the project's push-forward vocabulary).  No tameness hypothesis: the definition
  makes sense without it (the text states it in the tame setting of §6.5).
- `o^f_y`: an element of `Orx f hf y hy` (the orientations of `DET(f, y)`, Definition 6.27, read in
  the project's chosen chart at `y`; trusted).
- "orientable neighbourhood `U(x)`" (Definition 6.36), as in `V6_59.lean` and NOT the project's
  `IsOrientableNbhd` (a pair `V ⊆ U` without contractibility): an open `U ∋ x` which is
  sc-smoothly contractible (`IsScContractibleB`, my definition: an sc-smooth `H : ℝ¹ × X → X` on
  an open neighbourhood of `[0, 1] × U`, `H([0, 1] × U) ⊆ U`, `H(1, ·) = id`, `H(0, ·)` constant
  on `U`; Proposition 6.28 (1) and its proof) and has the local propagation property
  (`HasLocalPropagation f hf c hc U`, the project's, Theorem 6.35's conclusion, in a chart `c` of
  the atlas with `U ⊆ dom c`; the push-forward is built in one chart, p. 222).
- "every orientable neighbourhood": every such `U` AND every chart `c` in which `U` has the local
  propagation property (the continuity condition refers to the push-forwards in that chart).
- "the restriction to `U_∞` is one of the two continuous orientations": the project's
  `IsContinuousOrientation f hf c hc hUc (le_refl U)` (Definition 6.36: every push-forward along an
  sc-smooth path in `U` from `y₁` to `y₂` maps `o_{y₁}` to `o_{y₂}`) of `y ↦ o_y` on `U ∩ X_∞`, read
  in the chart `c` by `toChartOr` (trusted).  "One of the two" adds nothing.
- Nothing looks false to me.
-/
namespace RoundTrip.V6_60
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- `U` is **sc-smoothly contractible**: an sc-smooth `H : ℝ¹ × X → X` on an open neighbourhood of
`[0, 1] × U`, mapping `[0, 1] × U` into `U`, with `H(1, ·) = id` and `H(0, ·)` constant on `U`. -/
def IsScContractibleB (PX : MPolyfold X) (U : Set X) : Prop :=
  ∃ (H : (Fin 1 → ℝ) × X → X) (y₀ : X) (W : Set ((Fin 1 → ℝ) × X)),
    IsOpen W ∧ Set.Icc (0 : Fin 1 → ℝ) 1 ×ˢ U ⊆ W ∧
    ((rnPolyfold 1).prod PX).IsScSmoothOn PX H W ∧
    (∀ t ∈ Set.Icc (0 : Fin 1 → ℝ) 1, ∀ y ∈ U, H (t, y) ∈ U) ∧
    (∀ y ∈ U, H (pt1 1, y) = y) ∧ (∀ y ∈ U, H (pt1 0, y) = y₀)

/-- **Definition 6.40**: `y ↦ o_y` is an orientation of `f`: for every smooth `x`, every
orientable neighbourhood `U` of `x` (open, sc-smoothly contractible, with the local propagation
property in the chart `c`), `y ↦ o_y` on `U_∞` is a continuous orientation. -/
def D640 {Bd : StrongBundle PX P} (f : X → Y) (hf : Bd.IsScFredholmSection f)
    (o : (y : X) → (hy : y ∈ PX.smoothSet) → Orx f hf y hy) : Prop :=
  ∀ x ∈ PX.smoothSet, ∀ (U : Set X) (c : StrongBundleChart PX P) (hc : Bd.IsChart c)
    (hUc : U ⊆ c.φ.source),
    IsOpen U → x ∈ U → IsScContractibleB PX U → HasLocalPropagation f hf c hc U →
      IsContinuousOrientation f hf c hc hUc (le_refl U)
        (fun y hy hys => toChartOr hf hys c hc (hUc hy) (o y hys))

end

/-- Definition 6.40: the project's "orientation of `f`" is the text's. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f)
    (o : (y : X) → (hy : y ∈ PX.smoothSet) → Orx f hf y hy),
    IsSectionOrientation f hf o ↔ D640 f hf o

end RoundTrip.V6_60
