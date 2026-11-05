import Polyfold
/-! Blind formalization of V3_13 (the text's §3.1, Definition 3.11, p. 69). Choices:
- This item is a definition.  `B` states that the project's notion of Definition 3.11
  (`StrongBundle.IsScFredholmGerm`, the declaration whose docstring is "Definition 3.11") is the
  text's notion, written here as `IsScFredholmGermB`.
- Setting: `X Y : Type` (universe 0; nothing depends on it).  `PX : MPolyfold X`, `P : Y → X` with
  the fibrewise linear structure as instances on `P ⁻¹' {x}`, `Bd : StrongBundle PX P`.  The text
  states Definitions 3.4–3.14 for a *tame* strong bundle; this is a hypothesis of `B`
  (`IsTameStrongBundle`, as in the earlier blind files: tame base and an *equivalent* strong bundle
  atlas of charts with tame base retraction — a property of the given structure, not "every
  compatible chart is tame").  `f` is a section (`IsSection P f`), `x₀ ∈ X`.
- The chart (Definitions 3.6/3.11): a strong bundle chart `c` compatible with the bundle's atlas
  (`StrongBundle.IsChart`) with `x₀` in its domain and `φ(x₀) = 0`.  Since a filling (Definition
  3.4) is defined only for a *tame* strong local bundle `K = R(U ◁ F) → O`, I require the chart's
  base retraction `r` to be tame (`ScRetraction.IsTame` of `baseRetraction`).  Doubt: the project's
  `IsScFredholmGerm` may allow non-tame charts; if the two are inequivalent, this is where.
- `f̂ = c.principal f`, the principal part of `Φ ∘ f ∘ φ⁻¹` (trusted: `(Φ(f(φ⁻¹ z))).2`).
- "Filled version `(g, 0)`" (Definitions 3.4, 3.6), written out here (`IsFillingB`), all at the
  germ level as the text says: `g` is an sc-smooth section germ of `U ◁ F → U` at `0`, i.e. an
  sc-smooth germ `O(C, 0) → F` (Definition 3.2: project `ScNbhdGerm`/`IsScSmoothGerm`, on a germ of
  neighbourhoods inside `U`); (1) `f̂ = g` on `O = r(U)` near `0`; (2) `y ∈ U` near `0` with
  `g(y) = ρ(r(y))g(y)` lies in `O`; (3) the linearization at `0` of the germ
  `y ↦ [1 − ρ(r(y))]g(y)` (a derivative family `Dk` of this sc¹-germ) maps `ker Dr(0)` (`Dr` a
  derivative family of the sc-smooth `r` on `U`, Definition 1.14) bijectively onto
  `ker ρ(0) = {h | ρ(0)h = 0}` with bounded inverse (topological linear isomorphism).  Here
  `r(u) = (R(u, 0))₁`, `ρ(u)h = (R(u, h))₂`.
- "Local sc⁺-section `s`" of `U ◁ F → U`: a map `s : E₀ → F₁` which is an sc-smooth germ at `0`
  into `F¹` (`IsScPlusGermB`; germ reading of "local"), with `s(0) = g(0)` in `F₀`.
- "`g − s` conjugated to a basic germ" (`ConjBasicB`): a relatively open neighbourhood `U₀ ⊆ U` of
  `0` in `C` (germ reading: the text's `U ◁ F` may be shrunk), `n, k ≤ n, N : ℕ`, an sc-Banach
  space `W`, `U'` relatively open in `C' = [0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ ⊕ W ⊆ ℝⁿ ⊕ W` (literally the text's
  quadrant of Definition 3.7, `stdQuad`), a strong bundle isomorphism `Ψ : U₀ ◁ F → U' ◁ F'`,
  `F' = ℝᴺ ⊕ W`, with inverse `Ψ'` (project `IsStrongBundleIso`; its base maps are the
  sc-diffeomorphism `ψ` and `ψ⁻¹`), `ψ(0) = 0`, such that the push-forward
  `u' ↦ (Ψ(ψ⁻¹u', (g − s)(ψ⁻¹u')))₂` is a basic germ (project `IsBasicGerm`, Definition 3.7) on a
  germ of neighbourhoods inside `U'`.
- "at the smooth point `x₀`": `x₀ ∈ PX.smoothSet` (redundant given `φ(x₀) = 0`).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_13
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

/-- Definition 3.11: for a section of a tame strong bundle, the project's sc-Fredholm germs are
exactly the text's. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P), IsTameStrongBundle Bd →
      ∀ (f : X → Y) (x₀ : X), IsSection P f →
        (Bd.IsScFredholmGerm f x₀ ↔ IsScFredholmGermB Bd f x₀)

end RoundTrip.V3_13
