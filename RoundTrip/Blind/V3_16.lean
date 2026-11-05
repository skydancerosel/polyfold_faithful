import Polyfold
/-! Blind formalization of V3_16 (the text's §3.1, Definition 3.14, p. 70). Choices:
- This item is a definition.  `B` states that the project's notion of Definition 3.14
  (`StrongBundle.IsScFredholmSection`, the declaration whose docstring is "Definition 3.14") is the
  text's notion, written here as `IsScFredholmSectionB`, for sections of a *tame* strong bundle (the
  text's setting).
- Setting: `X Y : Type` (universe 0), `PX : MPolyfold X`, `P : Y → X` with the fibrewise linear
  structure as instances, `Bd : StrongBundle PX P`, tame (`IsTameStrongBundle`, as in the earlier
  blind files: tame base and an *equivalent* strong bundle atlas of charts with tame base retraction
  — a property of the given structure).  `f` a section (`IsSection P f`, presupposed by "a section
  `f`").
- (1) "sc-smooth": `StrongBundle.IsScSmoothSection` (Definition 2.52; trusted).
- (2) "regularizing": `x ∈ X_m` is `x ∈ PX.levelSet m` (trusted: some compatible chart maps `x` into
  `E_m`); `Y_{m,k}` is written here (`YlevelB`): the points `y` that some strong bundle chart
  compatible with the bundle's atlas maps into `E_m ⊕ F_k` (the text's double filtration of `Y`; by
  the invariance of the filtration this does not depend on the chart).
- (3) "`(f, x)` is an sc-Fredholm germ at every smooth point `x`": `x ∈ PX.smoothSet` (`X_∞`) and the
  text's Definition 3.11 as written in my blind file V3_13 (`IsScFredholmGermB`, copied below with
  its prelude: germ data in a strong bundle chart with *tame* base retraction — the filling of
  Definition 3.4 is defined for tame strong local bundles — filled version, sc⁺-germ `s`,
  conjugation to a basic germ, all at the germ level).  Doubt: the project's docstring says
  tameness plays no role in its version; if the project's germ notion allows non-tame charts, the
  two may differ there.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_16
open Polyfold Filter Topology

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A **tame strong bundle**: tame base, and an equivalent strong bundle atlas of charts whose base
retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

end

/-- **Definitions 3.4/3.6**: `g` is a filling (filled version) of the principal part `f̂` of a
section of `K = R(U ◁ F) → O`, `O = r(U)`, all near `0`. -/
def IsFillingB {E F : ScBanach} (C U : Set (E.lvl 0))
    (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0) (fhat g : E.lvl 0 → F.lvl 0) : Prop :=
  -- `g` is an sc-smooth section germ of `U ◁ F → U`, and condition (3)
  (∃ G : ScNbhdGerm E C, (∀ x ∈ G.U 0, x ∈ U) ∧ IsScSmoothGerm G g ∧
    ∃ Dk : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0,
      IsSc1GermWith G (fun y => g y - (R ((R (y, 0)).1, g y)).2) Dk ∧
    ∃ Dr : E.lvl 1 → E.lvl 0 →L[ℝ] E.lvl 0, IsSc1With U (fun u => (R (u, 0)).1) Dr ∧
      Set.BijOn (Dk 0) {v | Dr 0 v = 0} {h | (R (0, h)).2 = 0} ∧
      ∃ c : ℝ, ∀ v, Dr 0 v = 0 → ‖v‖ ≤ c * ‖Dk 0 v‖) ∧
  -- (1) `f̂ = g` on `O` near `0`
  (∀ᶠ x in 𝓝 (0 : E.lvl 0), x ∈ (fun u => (R (u, 0)).1) '' U → fhat x = g x) ∧
  -- (2) `g(y) = ρ(r(y))g(y)`, `y ∈ U` near `0`, forces `y ∈ O`
  (∀ᶠ y in 𝓝 (0 : E.lvl 0), y ∈ U → g y = (R ((R (y, 0)).1, g y)).2 →
    y ∈ (fun u => (R (u, 0)).1) '' U)

/-- A local sc⁺-section `s : U → F¹` of `U ◁ F → U` near `0`: an sc-smooth germ into `F¹`. -/
def IsScPlusGermB {E F : ScBanach} (C U : Set (E.lvl 0)) (s : E.lvl 0 → F.lvl 1) : Prop :=
  ∃ G : ScNbhdGerm E C, (∀ x ∈ G.U 0, x ∈ U) ∧ IsScSmoothGerm (F := F.shift) G s

/-- The quadrant `[0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ ⊆ ℝⁿ`. -/
def stdQuad (n k : ℕ) : Set (Fin n → ℝ) := {a | ∀ i : Fin n, (i : ℕ) < k → 0 ≤ a i}

/-- **Definition 3.11, conjugation**: the section `u ↦ (u, k(u))` of `U ◁ F → U` is conjugated near
`0` to a basic germ by a strong bundle isomorphism `Ψ` covering an sc-diffeomorphism `ψ`,
`ψ(0) = 0`: `Ψ ∘ k ∘ ψ⁻¹` is a basic germ `O([0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ ⊕ W, 0) → ℝᴺ ⊕ W`. -/
def ConjBasicB {E F : ScBanach} (C U : Set (E.lvl 0)) (k : E.lvl 0 → F.lvl 0) : Prop :=
  ∃ U₀ : Set (E.lvl 0), IsRelOpenInQuadrant E C U₀ ∧ (0 : E.lvl 0) ∈ U₀ ∧ U₀ ⊆ U ∧
  ∃ (n kq N : ℕ) (_ : kq ≤ n) (W : ScBanach)
    (U' : Set ((ScBanach.paramProd (Fin n → ℝ) W).lvl 0)),
    IsRelOpenInQuadrant (ScBanach.paramProd (Fin n → ℝ) W) (stdQuad n kq ×ˢ Set.univ) U' ∧
    ∃ (Ψ : E.lvl 0 × F.lvl 0 →
          (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 × (ScBanach.paramProd (Fin N → ℝ) W).lvl 0)
      (Ψ' : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 × (ScBanach.paramProd (Fin N → ℝ) W).lvl 0 →
          E.lvl 0 × F.lvl 0),
      IsStrongBundleIso U₀ U' Ψ Ψ' ∧ (Ψ (0, 0)).1 = 0 ∧
      ∃ (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (stdQuad n kq ×ˢ Set.univ))
        (Bc : (Fin n → ℝ) × W.lvl 0 → W.lvl 0),
        (∀ x ∈ G.U 0, x ∈ U') ∧
        IsBasicGerm (stdQuad n kq) G
          (fun u' => (Ψ ((Ψ' (u', 0)).1, k (Ψ' (u', 0)).1)).2) Bc

/-- **Definition 3.11**: `(f, x₀)` is an sc-Fredholm germ: at the smooth point `x₀`, in a (tame)
strong bundle chart with `φ(x₀) = 0`, the principal part has a filled version `g`, and there is a
local sc⁺-section `s` with `s(0) = g(0)` such that `g − s` is conjugated to a basic germ. -/
def IsScFredholmGermB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ c : StrongBundleChart PX P, Bd.IsChart c ∧
    (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame ∧
    x₀ ∈ c.φ.source ∧ c.φ.toPartialEquiv x₀ = 0 ∧
    ∃ (g : c.φ.model.E.lvl 0 → c.F.lvl 0) (s : c.φ.model.E.lvl 0 → c.F.lvl 1),
      IsFillingB c.φ.model.C c.U c.R (c.principal f) g ∧
      IsScPlusGermB c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
      ConjBasicB c.φ.model.C c.U (fun u => g u - c.F.toBase 1 (s u))

/-- The double filtration `Y_{m,k}` of `Y`: points that a strong bundle chart (compatible with the
bundle's atlas) maps into `E_m ⊕ F_k`. -/
def YlevelB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (m k : ℕ) : Set Y :=
  {y | ∃ c : StrongBundleChart PX P, Bd.IsChart c ∧ y ∈ c.toPartialEquiv.source ∧
    (c.toPartialEquiv y).1 ∈ Set.range (c.φ.model.E.toBase m) ∧
    (c.toPartialEquiv y).2 ∈ Set.range (c.F.toBase k)}

/-- **Definition 3.14**: `f` is an sc-Fredholm section: (1) sc-smooth, (2) regularizing,
(3) an sc-Fredholm germ at every smooth point. -/
def IsScFredholmSectionB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) : Prop :=
  Bd.IsScSmoothSection f ∧
  (∀ m : ℕ, ∀ x ∈ PX.levelSet m, f x ∈ YlevelB Bd m (m + 1) → x ∈ PX.levelSet (m + 1)) ∧
  (∀ x ∈ PX.smoothSet, IsScFredholmGermB Bd f x)

/-- Definition 3.14: for sections of a tame strong bundle, the project's sc-Fredholm sections are
exactly the text's. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P), IsTameStrongBundle Bd →
      ∀ f : X → Y, IsSection P f →
        (Bd.IsScFredholmSection f ↔ IsScFredholmSectionB Bd f)

end RoundTrip.V3_16
