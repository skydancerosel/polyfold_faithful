import Polyfold
/-! Blind formalization of V6_57 (the text's §6.5, Theorem 6.37 and its proof, p. 228).

Text: for a strong bundle over a tame `X` and an sc-Fredholm `f` there is a uniquely determined
functor `Γ_f : PX → 𝒪_f`, `x ↦ Or^f_x`, `[φ] ↦ Γ_f([φ]) : Or^f_x → Or^f_y`, with property (∗):
for every sc-smoothly contractible open `U(x)` on which `f` has the local propagation property,
`φ_* = Γ_f([φ])` for every sc-smooth path `φ` in `U`.

Choices:
- Setting: as in `RoundTrip/Blind/V6_48.lean` (`X Y : Type`, `Bd : StrongBundle PX P`,
  `PX.IsTame`, `f` sc-Fredholm, `Bd.IsScFredholmSection f`; the paracompactness instance families
  only because the project's `HasLocalPropagation`/`IsPush` take them; true facts).  NOT added:
  hypotheses giving sc⁺-sections (bump functions); DOUBT as in V6_48/V6_55 (the push-forwards and
  the two-element `Or^f_x` need them).
- `PX` (V6_52): objects the smooth points, morphisms `x → y` the classes of sc-smooth paths from
  `x` to `y` (paths as in V6_48: sc-smooth `γ : ℝ¹ → X`, only `[0, 1]` mattering) under sc-smooth
  homotopy with end points fixed (the project's `ScHomotopic`, checked with `#print`, see V6_51).
  Composition `[ψ] * [φ] = [γ]` with `γ = φ ∘ β` on `[0, 1/2]` and `γ = ψ ∘ (β − 1)` on `[1/2, 1]`
  for a reparametrization `β` (smooth, `β(0) = 0`, `β(1) = 2`, `β([0, 1/2]) = [0, 1]`,
  `β([1/2, 1]) = [1, 2]`, constant near `1/2`): the p. 228 formula WITH the evident correction of
  its misprint `ψ(β(s))` (see V6_49, V6_52; with the literal formula `PX` is not a category).
- `𝒪_f`: objects the sets `Or^f_x`, morphisms bijections.  `Or^f_x` is the project's
  `Orx f hf x hx` (checked with `#print`: `ChartPoint.Or` — the orientations of `DET(f, x)`,
  Definition 6.27 — in the chart point of a chosen chart `orChart Bd x` at `x`).  I state the
  functor with values in bijections `≃`; with all maps as morphisms nothing changes (functors from
  a groupoid take values in bijections).
- A functor `Γ : PX → 𝒪_f` with `Γ(x) = Or^f_x` is encoded by its values on representatives, a
  family `G x y γ : Or^f_x ≃ Or^f_y` for every sc-smooth path `γ` from `x` to `y`, which
  (`IsFunctorB`) is constant on homotopy classes, sends constant paths to identities, and sends a
  composite `γ` of `φ`, `ψ` (for every admissible `β`) to `G ψ ∘ G φ`.
- Property (∗) (`IsStarB`): for every strong bundle chart `c`, every open sc-smoothly contractible
  `U` (as in V6_48, `IsScContractibleB`) with the local propagation property in `c` (the project's
  `HasLocalPropagation`, checked, see V6_48), every sc-smooth path `γ` in `U` (`γ([0, 1]) ⊆ U`)
  from `x` to `y`, and every push-forward `e` along `γ` in `c` (the project's `IsPush`, the text's
  `φ_*`): `G γ = κ_y⁻¹ ∘ e ∘ κ_x`, where `κ_x : Or^f_x ≃` (the orientations read in `c`) is the
  canonical identification of the chart change (the project's `toChartOr`, i.e.
  `ChartPoint.orTransfer`; trusted, docstring: "the canonical identification of `Or_x^f` read in
  `p` and in `p'`").  The text's "`U(x)`" only names the point `U` is a neighbourhood of; no
  condition on `x` is added.
- "Uniquely determined": `∃!` such a family `G` (equality of families of bijections).
- Nothing looks false to me apart from the DOUBT.
-/
namespace RoundTrip.V6_57
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  {Bd : StrongBundle PX P}

variable (PX) in
/-- `U` is sc-smoothly contractible (as in V6_48). -/
def IsScContractibleB (U : Set X) : Prop :=
  ∃ H : (Fin 1 → ℝ) × X → X,
    ((rnPolyfold 1).prod PX).IsScSmoothOn PX H (Set.univ ×ˢ U) ∧
    (∀ q ∈ Set.Icc (0 : Fin 1 → ℝ) 1, ∀ u ∈ U, H (q, u) ∈ U) ∧
    (∀ u ∈ U, H (pt1 0, u) = u) ∧
    ∃ p ∈ U, ∀ u ∈ U, H (pt1 1, u) = p

variable (PX) in
/-- `γ` is an sc-smooth path (on `ℝ¹`) from `x` to `y`. -/
def IsPathB (γ : (Fin 1 → ℝ) → X) (x y : X) : Prop :=
  (rnPolyfold 1).IsScSmoothMap PX γ ∧ γ (pt1 0) = x ∧ γ (pt1 1) = y

/-- `γ([0, 1]) ⊆ U`. -/
def PathInB (γ : (Fin 1 → ℝ) → X) (U : Set X) : Prop :=
  ∀ q ∈ Set.Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U

/-- The reparametrization `β` of the composition (as in V6_51). -/
def IsAdmissibleBetaB (β : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) β ∧ β 0 = 0 ∧ β 1 = 2 ∧ β '' Set.Icc 0 (1 / 2) = Set.Icc 0 1 ∧
    β '' Set.Icc (1 / 2) 1 = Set.Icc 1 2 ∧ ∀ᶠ s in nhds (1 / 2 : ℝ), β s = β (1 / 2)

/-- `γ` represents `[ψ] * [φ]`: `φ ∘ β` on `[0, 1/2]`, `ψ ∘ (β − 1)` on `[1/2, 1]`. -/
def IsConcatB (β : ℝ → ℝ) (φ ψ γ : (Fin 1 → ℝ) → X) : Prop :=
  (∀ s ∈ Set.Icc (0 : ℝ) (1 / 2), γ (pt1 s) = φ (pt1 (β s))) ∧
    ∀ s ∈ Set.Icc (1 / 2 : ℝ) 1, γ (pt1 s) = ψ (pt1 (β s - 1))

variable (PX) in
/-- The data of a functor `PX → 𝒪_f` with objects `Or^f_x`, on representatives: a bijection
`Or^f_x ≃ Or^f_y` for every sc-smooth path from `x` to `y`. -/
abbrev GammaDataB (f : X → Y) (hf : Bd.IsScFredholmSection f) : Type :=
  ∀ (x y : X) (hx : x ∈ PX.smoothSet) (hy : y ∈ PX.smoothSet) (γ : (Fin 1 → ℝ) → X),
    IsPathB PX γ x y → (Orx f hf x hx ≃ Orx f hf y hy)

/-- `G` is a functor `PX → 𝒪_f`: constant on classes, identities to identities, composites to
composites. -/
def IsFunctorB (f : X → Y) (hf : Bd.IsScFredholmSection f) (G : GammaDataB PX f hf) : Prop :=
  (∀ (x y : X) (hx : x ∈ PX.smoothSet) (hy : y ∈ PX.smoothSet) (γ γ' : (Fin 1 → ℝ) → X)
      (hγ : IsPathB PX γ x y) (hγ' : IsPathB PX γ' x y),
      ScHomotopic PX γ γ' → G x y hx hy γ hγ = G x y hx hy γ' hγ') ∧
  (∀ (x : X) (hx : x ∈ PX.smoothSet) (h : IsPathB PX (fun _ => x) x x),
      G x x hx hx (fun _ => x) h = Equiv.refl _) ∧
  (∀ β : ℝ → ℝ, IsAdmissibleBetaB β →
    ∀ (x y z : X) (hx : x ∈ PX.smoothSet) (hy : y ∈ PX.smoothSet) (hz : z ∈ PX.smoothSet)
      (φ ψ γ : (Fin 1 → ℝ) → X) (hφ : IsPathB PX φ x y) (hψ : IsPathB PX ψ y z)
      (hγ : IsPathB PX γ x z), IsConcatB β φ ψ γ →
      G x z hx hz γ hγ = (G x y hx hy φ hφ).trans (G y z hy hz ψ hψ))

/-- Property (∗): in every open sc-smoothly contractible `U` with the local propagation property in
a chart `c`, `G` along a path in `U` is the push-forward `φ_*` (read in the chosen charts). -/
def IsStarB (f : X → Y) (hf : Bd.IsScFredholmSection f) (G : GammaDataB PX f hf) : Prop :=
  ∀ (c : StrongBundleChart PX P) (hc : Bd.IsChart c) (U : Set X),
    IsOpen U → IsScContractibleB PX U → HasLocalPropagation f hf c hc U →
    ∀ (x y : X) (hx : x ∈ PX.smoothSet) (hy : y ∈ PX.smoothSet) (γ : (Fin 1 → ℝ) → X)
      (hγ : IsPathB PX γ x y), PathInB γ U →
      ∀ (hγc : ∀ q ∈ Set.Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source) (hxc : x ∈ c.φ.source)
        (hyc : y ∈ c.φ.source)
        (e : ChartPoint.Or f (chartPtOf c hc hxc hx) hf ≃
          ChartPoint.Or f (chartPtOf c hc hyc hy) hf),
        IsPush f hf c hc γ hγc hγ.2.1 hγ.2.2 hxc hyc hx hy e →
          G x y hx hy γ hγ =
            (toChartOr hf hx c hc hxc).trans (e.trans (toChartOr hf hy c hc hyc).symm)

end

/-- Theorem 6.37: there is a unique functor `Γ_f : PX → 𝒪_f`, `x ↦ Or^f_x`, with property (∗). -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f),
    PX.IsTame → ∃! G : GammaDataB PX f hf, IsFunctorB f hf G ∧ IsStarB f hf G

end RoundTrip.V6_57
