import Polyfold
/-! Blind formalization of V6_59 (the text's §6.5, Definition 6.39 and the sentence "an
equivalent version" linking it to Definition 6.38, p. 229).

Text: "An equivalent version": `f` is orientable if there is a map `y ↦ o_y`, `y ∈ U_∞`, `o_y` an
orientation of `DET(f, y)`, such that every smooth `x` has an orientable neighbourhood `U(x)` on
which `y ↦ o_y` is one of the two continuous orientations.

Choices:
- B is the conjunction of (1) Definition 6.39: the project's `IsOrientableSection' f hf` is the
  text's notion `D639 f hf` written below; (2) the claimed equivalence: over a tame `X`, for the
  functor `Γ_f` of Theorem 6.37, Definition 6.38 (`D638 Γ_f`) holds iff `D639 f hf`.
- Setting: `X Y : Type` (universe 0); `PX : MPolyfold X`, `P : Y → X` with the fibrewise linear
  structure as instances, `Bd : StrongBundle PX P`, `f` an sc-Fredholm section
  (`Bd.IsScFredholmSection f`, Definition 3.14; the orientation vocabulary of the project is
  indexed by such a proof `hf`).  The paracompactness instances of `ℝⁿ × X` and of the pulled-back
  bundles over `ℝⁿ × X` are instance arguments of the project's push-forward vocabulary
  (`HasLocalPropagation`, `IsContinuousOrientation`); they hold anyway (metrizable spaces), so B
  takes them as instance binders.
- "`y ∈ U_∞`": read as `y ∈ X_∞` (all smooth points of `X`; `U` is not yet introduced at that point
  of the sentence, evidently a misprint).  `o_y ∈ Or_y^f` is `Orx f hf y hy` (the orientations of
  `DET(f, y)`, read in the project's chosen chart at `y`, Definition 6.27; trusted).
- "Orientable neighbourhood `U(x)`" (Definition 6.36, p. 227; Theorem 6.35; Proposition 6.28 (1)):
  an open `U ∋ x`, sc-smoothly contractible, on which "the local propagation can be carried out".
  I did NOT use the project's `IsOrientableNbhd` (it is a pair `V ⊆ U` with `V` joined by paths in
  `U` and no contractibility, not the text's notion).  Instead:
  * sc-smoothly contractible (`IsScContractibleB`, my definition): an sc-smooth
    `H : ℝ¹ × X → X`, defined (sc-smooth, `IsScSmoothOn` of Definition 2.14 on the product
    M-polyfold `ℝ¹ × X`) on an open neighbourhood of `[0, 1] × U`, with `H([0, 1] × U) ⊆ U`,
    `H(1, ·) = id` and `H(0, ·)` constant on `U` (the proof of Proposition 6.28 contracts
    `U = r(V')` by `(t, y) ↦ r(ty)`, which is of this kind);
  * the local propagation property: the project's `HasLocalPropagation f hf c hc U` in a chart `c`
    of the atlas (`Bd.IsChart c`) with `U ⊆ dom c` (the text builds the push-forward in one strong
    bundle chart, p. 222; the property is: push-forwards exist along sc-smooth paths in `U` with
    smooth end points and agree for two paths with the same end points — Theorem 6.35's
    conclusion, trusted).
- "`y ↦ o_y` is one of the two continuous orientations on `U`" (Definition 6.36): the project's
  `IsContinuousOrientation f hf c hc hUc (le_refl U) o|_U` (every push-forward `e` along an
  sc-smooth path in `U` from `y₁` to `y₂` maps `o_{y₁}` to `o_{y₂}`), with `o_y` read in the chart
  `c` by `toChartOr` (the identification of `Or_y^f` in two charts; trusted).  "One of the two" is
  not a further condition.
- `Γ_f` (Theorem 6.37) is not built here: B quantifies over every family
  `Γ([φ]) : Or_x^f ≃ Or_y^f` on the morphisms of `PX` which is a functor (identities, composition)
  and has property (∗) of Theorem 6.37 on the sc-smoothly contractible open sets (the project's
  `IsStarPropertyOn` with that family of sets: for every chart `c`, every such `U` with the local
  propagation property in `c`, every sc-smooth path `φ` in `U` and every push-forward `e` along `φ`,
  `Γ([φ])` is `e` read in the charts).  By the uniqueness in Theorem 6.37 this is `Γ_f`; if no such
  family exists, part (2) is vacuous.
- Definition 6.38 (`D638`): for smooth `x`, `y` and any two classes `[φ], [ψ] : x ⟶ y`,
  `Γ_f([φ]) = Γ_f([ψ])` ("in the same path component" is implied by the existence of `[φ]`).
- Doubt: the direction 6.38 ⇒ 6.39 needs orientable neighbourhoods around every smooth point
  (Theorem 6.35, proved in the text with Proposition 6.28 (3), (4), i.e. sc⁺-sections through
  given points); B uses only the text's hypotheses (tame `X`, sc-Fredholm `f`).
-/
namespace RoundTrip.V6_59
open Polyfold CategoryTheory

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

/-- **Definition 6.39**: there is `y ↦ o_y ∈ Or_y^f` on `X_∞` such that every smooth `x` has an
orientable neighbourhood `U(x)` (open, `x ∈ U`, sc-smoothly contractible, with the local
propagation property in a chart `c`) on which `y ↦ o_y` is a continuous orientation. -/
def D639 {Bd : StrongBundle PX P} (f : X → Y) (hf : Bd.IsScFredholmSection f) : Prop :=
  ∃ o : (y : X) → (hy : y ∈ PX.smoothSet) → Orx f hf y hy,
    ∀ x ∈ PX.smoothSet, ∃ (U : Set X) (c : StrongBundleChart PX P) (hc : Bd.IsChart c)
      (hUc : U ⊆ c.φ.source),
      IsOpen U ∧ x ∈ U ∧ IsScContractibleB PX U ∧ HasLocalPropagation f hf c hc U ∧
      IsContinuousOrientation f hf c hc hUc (le_refl U)
        (fun y hy hys => toChartOr hf hys c hc (hUc hy) (o y hys))

/-- The text's `Γ_f` (Theorem 6.37): a functor `PX → O_f` on morphisms (identities to identities,
composition to composition) with property (∗) on the sc-smoothly contractible open sets. -/
def IsGammaF {Bd : StrongBundle PX P} (f : X → Y) (hf : Bd.IsScFredholmSection f)
    (Γ : (x y : PathCat PX) → (x ⟶ y) → Orx f hf x.pt x.smooth ≃ Orx f hf y.pt y.smooth) :
    Prop :=
  (∀ x : PathCat PX, Γ x x (𝟙 x) = Equiv.refl _) ∧
  (∀ (x y z : PathCat PX) (φ : x ⟶ y) (ψ : y ⟶ z), Γ x z (φ ≫ ψ) = (Γ x y φ).trans (Γ y z ψ)) ∧
  IsStarPropertyOn f hf (fun U => IsOpen U ∧ IsScContractibleB PX U) Γ

/-- **Definition 6.38** for `Γ = Γ_f`: `Γ_f([φ])` does not depend on the class `[φ] : x ⟶ y`. -/
def D638 {Bd : StrongBundle PX P} {f : X → Y} {hf : Bd.IsScFredholmSection f}
    (Γ : (x y : PathCat PX) → (x ⟶ y) → Orx f hf x.pt x.smooth ≃ Orx f hf y.pt y.smooth) :
    Prop :=
  ∀ (x y : PathCat PX) (φ ψ : x ⟶ y), Γ x y φ = Γ x y ψ

end

/-- Definition 6.39 (the project's `IsOrientableSection'` is the text's notion) and its
equivalence, over a tame `X`, with Definition 6.38 for the functor `Γ_f` of Theorem 6.37. -/
def B : Prop :=
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f),
      IsOrientableSection' f hf ↔ D639 f hf) ∧
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f),
    PX.IsTame →
    ∀ Γ : (x y : PathCat PX) → (x ⟶ y) → Orx f hf x.pt x.smooth ≃ Orx f hf y.pt y.smooth,
      IsGammaF f hf Γ → (D638 Γ ↔ D639 f hf))

end RoundTrip.V6_59
