import Polyfold
/-! Blind formalization of V2_58 (the text's §2.5, Definition 2.51 and the remarks after it, p. 52).

Text: a strong bundle over the M-polyfold `X` is a continuous surjection `P : Y → X` from a
paracompact Hausdorff space `Y` (each fibre a Banach space) with an equivalence class of strong
bundle atlases.  The charts induce a double filtration `Y_{m,k}` of `Y` and M-polyfolds `Y[i]`
(`i = 0, 1`) with `Y[i]_m = Y_{m,m+i}`; the projections `P[i] : Y[i] → X` are sc-smooth.

Choices:
- This item is a definition plus properties.  Setting: `X Y : Type` (spaces put in `Type`; the
  project's notions are universe-polymorphic, this is the instance `u = v = 0`).  `X` is an
  M-polyfold (`[T2Space X] [ParacompactSpace X]`, `PX : MPolyfold X`, Definition 2.13).  The
  linear structure of the fibres `P⁻¹(x)` is given as instances `[∀ x, AddCommGroup (P ⁻¹' {x})]`
  `[∀ x, Module ℝ (P ⁻¹' {x})]`; their topology is the subspace topology of `Y`; "each fibre has
  the structure of a Banach space" is `IsBanachable` (checked with `#print`: linearly homeomorphic
  to a complete normed space).
- Strong bundle charts, atlases and their equivalence (Definition 2.50, not this item) are the
  project's `StrongBundleChart`, `StrongBundleAtlas`, `StrongBundleAtlas.Equiv` (checked with
  `#print`: a base chart `φ` with `PX.IsChart φ`, a strong bundle retraction `R` on `U ◁ F`
  with base retract `O`, a homeomorphism `Φ : P⁻¹(V) → K = R(U ◁ F)` covering `φ` and linear on
  fibres; compatibility = `(Φ' ∘ Φ⁻¹)[i]` sc-smooth for `i = 0, 1`; atlases = pairwise compatible
  charts covering `Y`; `A ~ A'` iff some atlas has chart set `A ∪ A'`).
- B (a): "equivalence class" presupposes that atlas equivalence is an equivalence relation; B
  asserts it (as in my `RoundTrip/Blind/V2_12.lean` for M-polyfold atlases).
- B (b): the text's notion (`IsStrongBundleStructureB`: `Y` Hausdorff paracompact, `P`
  continuous surjective, fibres Banachable, `𝒜` the class of an atlas) is exactly the class of
  the atlas of a project `StrongBundle` (checked with `#print`: fields `continuous`, `surjective`,
  `banachable`, `atlas`, with `[T2Space Y] [ParacompactSpace Y]`; the atlas represents the class).
- The double filtration (my `filtB`): `y ∈ Y_{m,k}` iff `Φ(y) ∈ K_{m,k} = K ∩ (E_m ⊕ F_k)` for a
  chart `Φ` of the atlas around `y` (`InKB`: base component in the range of `E_m → E₀`, fibre
  component in the range of `F_k → F₀`).  Index range `0 ≤ k ≤ m + 1` (the text's range; for
  `k > m + 1` the condition is not chart independent).  "The charts induce a double filtration" is
  read as: (c) the condition does not depend on the chart, for charts of the same atlas or of
  equivalent atlases (so `Y_{m,k}` depends only on the strong bundle structure), and (d) the sets
  are nested, `Y_{m+1,k} ⊆ Y_{m,k}` and `Y_{m,k+1} ⊆ Y_{m,k}` in the range.  B also says the
  project's `doubleLevel` (defined with "every chart of the atlas around `y`") and `oneSet`
  (`Y_{0,1}`) are these sets.
- `Y[0]`: `Y` with the charts `Φ : P⁻¹(V) → K` as M-polyfold charts with model
  `(K, C ◁ F, E ◁ F)` — the project's `StrongBundleChart.toMChart` (checked with `#print`: model
  `c.model = (c.K, C ×ˢ univ, E.prod F)` and map `c.toPartialEquiv`).  B: some M-polyfold structure
  on `Y` has exactly these charts as its atlas (i.e. they are pairwise compatible M-polyfold
  charts), its level sets are `Y_{m,m}` (`MPolyfold.levelSet`, the text's `X_m`), and `P` is
  sc-smooth from it to `X` (`IsScSmoothMap`, Definition 2.14).
- `Y[1]`: the project's `Bd.One` (the subtype `Y_{0,1}` = `oneSet`) with `Bd.toMPolyfold1`
  (checked with `#print`: atlas `atlas1` of the charts `oneChart = Φ[1]`, `y ↦ (Φ(y)₁, Φ(y)₂`
  lifted to `F₁)`, source `P⁻¹(V) ∩ Y_{0,1}`, model `(K[1], C ◁ F, E ◁ F¹)`).  I did not print
  the topology instance on `Bd.One` (its name, `instTopologicalSpaceOne`, is not in the vocabulary
  and was only seen through `#synth`); it is forced by the atlas, since the charts are
  homeomorphisms of open sets covering `Bd.One` onto subsets of `E₀ ⊕ F₁`, which determines the
  topology — this is the text's topology of `Y[1]`.  B: the level sets of `Y[1]`, seen in `Y`
  through the inclusion `oneVal`, are `Y_{m,m+1}`, and `P[1] = P ∘ oneVal` is sc-smooth.
- `Y[i]` are stated for the representative atlas of the strong bundle (independence of the
  representative is stated only for the filtration, in (c)).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_58
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The equivalence class `{A' | A ~ A'}` of the strong bundle atlas `A` (Definition 2.50). -/
def classB (A : StrongBundleAtlas PX P) : Set (StrongBundleAtlas PX P) :=
  {A' | A.Equiv A'}

/-- `Φ(y) ∈ K_{m,k} = K ∩ (E_m ⊕ F_k)` for the strong bundle chart `(Φ, P⁻¹(V), K, U ◁ F)`
(for `y ∈ P⁻¹(V)`, `Φ(y) ∈ K` already). -/
def InKB (c : StrongBundleChart PX P) (m k : ℕ) (y : Y) : Prop :=
  (c.toPartialEquiv y).1 ∈ Set.range (c.φ.model.E.toBase m) ∧
    (c.toPartialEquiv y).2 ∈ Set.range (c.F.toBase k)

/-- The double filtration `Y_{m,k}` induced by the atlas `A`: `y ∈ Y_{m,k}` iff `Φ(y) ∈ K_{m,k}`
for a chart `Φ` of `A` around `y`. -/
def filtB (A : StrongBundleAtlas PX P) (m k : ℕ) : Set Y :=
  {y | ∃ c ∈ A.charts, y ∈ c.toPartialEquiv.source ∧ InKB c m k y}

end

/-- **Definition 2.51**: a strong bundle structure on `P : Y → X`: `Y` is Hausdorff and
paracompact, `P` is a continuous surjection, every fibre is a Banach space, and `𝒜` is an
equivalence class of strong bundle atlases. -/
def IsStrongBundleStructureB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) {Y : Type} [TopologicalSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (𝒜 : Set (StrongBundleAtlas PX P)) : Prop :=
  T2Space Y ∧ ParacompactSpace Y ∧ Continuous P ∧ Function.Surjective P ∧
    (∀ x, IsBanachable (P ⁻¹' {x})) ∧ ∃ A : StrongBundleAtlas PX P, 𝒜 = classB A

/-- Definition 2.51 and the remarks after it: strong bundles (an equivalence class of strong
bundle atlases) are the project's `StrongBundle`s; the charts induce a well-defined double
filtration `Y_{m,k}`; `Y[0]` (charts `Φ`) and `Y[1]` (charts `Φ[1]`) are M-polyfolds with
`Y[i]_m = Y_{m,m+i}`, and `P[0]`, `P[1]` are sc-smooth. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})],
    -- (a) presupposed by "equivalence class": equivalence of strong bundle atlases
    Equivalence (StrongBundleAtlas.Equiv (PX := PX) (P := P)) ∧
    -- (b) strong bundle structures = classes of the atlases of project strong bundles
    (∀ 𝒜 : Set (StrongBundleAtlas PX P), IsStrongBundleStructureB PX P 𝒜 ↔
      ∃ (_ : T2Space Y) (_ : ParacompactSpace Y) (Bd : StrongBundle PX P), 𝒜 = classB Bd.atlas) ∧
    -- (c) the double filtration is induced by the structure: for `0 ≤ k ≤ m + 1`, `Φ(y) ∈ K_{m,k}`
    -- does not depend on the chart (of the atlas, or of an equivalent atlas) around `y`
    (∀ A A' : StrongBundleAtlas PX P, A.Equiv A' →
      ∀ c ∈ A.charts, ∀ c' ∈ A'.charts, ∀ y : Y,
        y ∈ c.toPartialEquiv.source → y ∈ c'.toPartialEquiv.source →
        ∀ m k : ℕ, k ≤ m + 1 → (InKB c m k y ↔ InKB c' m k y)) ∧
    (∀ [T2Space Y] [ParacompactSpace Y] (Bd : StrongBundle PX P),
      -- (d) it is a double filtration (nested), and it is the project's `doubleLevel`, `oneSet`
      (∀ m k : ℕ, k ≤ m + 1 → filtB Bd.atlas (m + 1) k ⊆ filtB Bd.atlas m k) ∧
      (∀ m k : ℕ, k ≤ m → filtB Bd.atlas m (k + 1) ⊆ filtB Bd.atlas m k) ∧
      (∀ m k : ℕ, k ≤ m + 1 → Bd.doubleLevel m k = filtB Bd.atlas m k) ∧
      Bd.oneSet = filtB Bd.atlas 0 1 ∧
      -- (e) `Y[0]`: the charts `Φ` form an M-polyfold atlas of `Y`, with `Y[0]_m = Y_{m,m}`,
      -- and `P[0] : Y[0] → X` is sc-smooth
      (∃ Q : MPolyfold Y,
        Q.atlas.charts = (fun c => c.toMChart Bd.continuous) '' Bd.atlas.charts ∧
        (∀ m : ℕ, Q.levelSet m = filtB Bd.atlas m m) ∧
        Q.IsScSmoothMap PX P) ∧
      -- (f) `Y[1]` (on `Y_{0,1}`, charts `Φ[1]`): `Y[1]_m = Y_{m,m+1}`, and
      -- `P[1] : Y[1] → X` is sc-smooth
      (∀ m : ℕ, Bd.oneVal '' Bd.toMPolyfold1.levelSet m = filtB Bd.atlas m (m + 1)) ∧
      Bd.toMPolyfold1.IsScSmoothMap PX (P ∘ Bd.oneVal))

end RoundTrip.V2_58
