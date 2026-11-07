import Polyfold
/-! Blind formalization of V6_56 (the text's §6.5, the proof of Theorem 6.37, p. 228).

Text: for a path `φ` and `t₀ ∈ [0, 1]` one chooses an orientable neighbourhood `U(φ(t₀))` and an
open interval `I(t₀)` on which orientations propagate; using the compactness of `[0, 1]` and a
finite covering, `o₀` is transported to `o₁`; "by a covering argument" `φ_*` depends only on `[φ]`,
and the uniqueness of `Γ_f` is called obvious.

Choices:
- B is the conjunction of the four claims of the proof: (a) at every `t₀ ∈ [0, 1]` there are an
  orientable neighbourhood `U` of `φ(t₀)` and an open interval `I ∋ t₀` with
  `φ(I ∩ [0, 1]) ⊆ U`; (b) the transport of `o₀ ∈ Or^f_{φ(0)}` by local push-forwards along a
  finite subdivision of `[0, 1]` exists and gives a well-defined `o₁ ∈ Or^f_{φ(1)}` (independent of
  the subdivision and of all choices); (c) the transport depends only on the class `[φ]`; (d) the
  functor `Γ_f` of Theorem 6.37 is unique.
- Setting: as in `RoundTrip/Blind/V6_48.lean` (`X Y : Type`, `Bd : StrongBundle PX P`,
  `PX.IsTame`, `f` sc-Fredholm, `Bd.IsScFredholmSection f`; paracompactness instance families only
  because the project's `HasLocalPropagation`/`IsPush` take them).  The DOUBT of V6_48/V6_55 (no
  hypothesis giving sc⁺-sections) applies.
- Paths: sc-smooth `γ : ℝ¹ → X`, only `[0, 1]` mattering (V6_48); homotopy: the project's
  `ScHomotopic` (checked, see V6_51).  `Or^f_x`: the project's `Orx f hf x hx` (orientations of
  `DET(f, x)` in a chosen chart, checked with `#print`); an orientation read in another chart `c`
  through the canonical identification `toChartOr` (`ChartPoint.orTransfer`).
- Orientable neighbourhood (Definition 6.36, as in V6_50, `IsOrNbhdB`): open, containing the
  point, sc-smoothly contractible (`IsScContractibleB`, V6_48), with the local propagation
  property (`HasLocalPropagation`, checked) in a strong bundle chart `c`.
- (a): "open interval `I(t₀)`": `I = (a, b)` with `a < t₀ < b`, and `φ(t) ∈ U` for
  `t ∈ I ∩ [0, 1]` ("on which orientations propagate": the piece of the path over `I` lies in the
  orientable neighbourhood).
- (b), (c): the transport is the relation `ChainB γ 0 x o₀ 1 y o₁` ("`o₀` is transported to
  `o₁`"), defined inductively: a single step from `a` to `b` (`a ≤ b`) is allowed when
  `γ([a, b])` lies in an orientable neighbourhood `U` of `γ(a)` in a chart `c` and a push-forward
  `e` (the project's `IsPush`) in `c` along the piece `s ↦ γ(a + s(b − a))` maps `o_a` to `o_b`
  (read in `c` via `toChartOr`); chains are composed at intermediate times (this is the
  transport along a finite subdivision `0 = s₀ ≤ s₁ ≤ … ≤ s_N = 1`).  (b): for every `o₀` there is
  exactly one `o₁` with `ChainB γ 0 x o₀ 1 y o₁`.  (c): homotopic paths (end points fixed) have
  the same transport relation.
- (d): uniqueness of the functor of Theorem 6.37: any two families `G`, `G'` that are functors
  `PX → 𝒪_f` (`IsFunctorB`) with property (∗) (`IsStarB`) are equal; these two notions are copied
  from `RoundTrip/Blind/V6_57.lean` (composition with the corrected p. 228 formula
  `ψ(β(s) − 1)`, see V6_49).
- Nothing looks false to me apart from the DOUBT.
-/
namespace RoundTrip.V6_56
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

/-- Definition 6.36 (as in V6_50): an orientable neighbourhood of `(f, x)` in the chart `c`. -/
def IsOrNbhdB (f : X → Y) (hf : Bd.IsScFredholmSection f) (c : StrongBundleChart PX P)
    (hc : Bd.IsChart c) (U : Set X) (x : X) : Prop :=
  IsOpen U ∧ x ∈ U ∧ IsScContractibleB PX U ∧ HasLocalPropagation f hf c hc U

/-- The piece `s ↦ γ(a + s (b − a))` of a path over `[a, b]`. -/
def pieceB (γ : (Fin 1 → ℝ) → X) (a b : ℝ) : (Fin 1 → ℝ) → X :=
  fun q => γ (pt1 (a + q 0 * (b - a)))

/-- The transport of orientations along `γ` from time `a` (point `x`, orientation `ox`) to time
`b` (point `y`, orientation `oy`) by local push-forwards in orientable neighbourhoods, along a
finite subdivision of `[a, b]`. -/
inductive ChainB (f : X → Y) (hf : Bd.IsScFredholmSection f) (γ : (Fin 1 → ℝ) → X) :
    (a : ℝ) → (x : X) → (hx : x ∈ PX.smoothSet) → Orx f hf x hx →
    (b : ℝ) → (y : X) → (hy : y ∈ PX.smoothSet) → Orx f hf y hy → Prop
  | step {a b : ℝ} {x y : X} {hx : x ∈ PX.smoothSet} {hy : y ∈ PX.smoothSet}
      {ox : Orx f hf x hx} {oy : Orx f hf y hy} (hab : a ≤ b)
      (c : StrongBundleChart PX P) (hc : Bd.IsChart c) (U : Set X)
      (hN : IsOrNbhdB f hf c hc U x) (hsub : ∀ t ∈ Set.Icc a b, γ (pt1 t) ∈ U)
      (hpc : ∀ q ∈ Set.Icc (0 : Fin 1 → ℝ) 1, pieceB γ a b q ∈ c.φ.source)
      (h₀ : pieceB γ a b (pt1 0) = x) (h₁ : pieceB γ a b (pt1 1) = y)
      (hxc : x ∈ c.φ.source) (hyc : y ∈ c.φ.source)
      (e : ChartPoint.Or f (chartPtOf c hc hxc hx) hf ≃
        ChartPoint.Or f (chartPtOf c hc hyc hy) hf)
      (he : IsPush f hf c hc (pieceB γ a b) hpc h₀ h₁ hxc hyc hx hy e)
      (hmap : e (toChartOr hf hx c hc hxc ox) = toChartOr hf hy c hc hyc oy) :
      ChainB f hf γ a x hx ox b y hy oy
  | trans {a m b : ℝ} {x z y : X} {hx : x ∈ PX.smoothSet} {hz : z ∈ PX.smoothSet}
      {hy : y ∈ PX.smoothSet} {ox : Orx f hf x hx} {oz : Orx f hf z hz} {oy : Orx f hf y hy} :
      ChainB f hf γ a x hx ox m z hz oz → ChainB f hf γ m z hz oz b y hy oy →
      ChainB f hf γ a x hx ox b y hy oy

/-- The reparametrization `β` of the composition (as in V6_51, V6_57). -/
def IsAdmissibleBetaB (β : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) β ∧ β 0 = 0 ∧ β 1 = 2 ∧ β '' Set.Icc 0 (1 / 2) = Set.Icc 0 1 ∧
    β '' Set.Icc (1 / 2) 1 = Set.Icc 1 2 ∧ ∀ᶠ s in nhds (1 / 2 : ℝ), β s = β (1 / 2)

/-- `γ` represents `[ψ] * [φ]` (corrected p. 228 formula, as in V6_57). -/
def IsConcatB (β : ℝ → ℝ) (φ ψ γ : (Fin 1 → ℝ) → X) : Prop :=
  (∀ s ∈ Set.Icc (0 : ℝ) (1 / 2), γ (pt1 s) = φ (pt1 (β s))) ∧
    ∀ s ∈ Set.Icc (1 / 2 : ℝ) 1, γ (pt1 s) = ψ (pt1 (β s - 1))

variable (PX) in
/-- The data of a functor `PX → 𝒪_f` on representatives (as in V6_57). -/
abbrev GammaDataB (f : X → Y) (hf : Bd.IsScFredholmSection f) : Type :=
  ∀ (x y : X) (hx : x ∈ PX.smoothSet) (hy : y ∈ PX.smoothSet) (γ : (Fin 1 → ℝ) → X),
    IsPathB PX γ x y → (Orx f hf x hx ≃ Orx f hf y hy)

/-- `G` is a functor `PX → 𝒪_f` (as in V6_57). -/
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

/-- Property (∗) (as in V6_57). -/
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

/-- The proof of Theorem 6.37: local orientable neighbourhoods along a path, a well-defined
transport along finite subdivisions, its homotopy invariance, and the uniqueness of `Γ_f`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f),
    PX.IsTame →
    -- (a) orientable neighbourhoods `U(φ(t₀))` and intervals `I(t₀)`
    (∀ γ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX γ →
      ∀ t₀ ∈ Set.Icc (0 : ℝ) 1, ∃ (c : StrongBundleChart PX P) (hc : Bd.IsChart c) (U : Set X),
        IsOrNbhdB f hf c hc U (γ (pt1 t₀)) ∧
        ∃ a b : ℝ, a < t₀ ∧ t₀ < b ∧ ∀ t ∈ Set.Ioo a b ∩ Set.Icc 0 1, γ (pt1 t) ∈ U) ∧
    -- (b) `o₀` is transported to a well-defined `o₁`
    (∀ (γ : (Fin 1 → ℝ) → X) (x y : X), IsPathB PX γ x y →
      ∀ (hx : x ∈ PX.smoothSet) (hy : y ∈ PX.smoothSet) (o₀ : Orx f hf x hx),
        ∃! o₁ : Orx f hf y hy, ChainB f hf γ 0 x hx o₀ 1 y hy o₁) ∧
    -- (c) the transport depends only on `[φ]`
    (∀ (γ γ' : (Fin 1 → ℝ) → X) (x y : X), IsPathB PX γ x y → IsPathB PX γ' x y →
      ScHomotopic PX γ γ' →
      ∀ (hx : x ∈ PX.smoothSet) (hy : y ∈ PX.smoothSet) (o₀ : Orx f hf x hx)
        (o₁ : Orx f hf y hy),
        ChainB f hf γ 0 x hx o₀ 1 y hy o₁ → ChainB f hf γ' 0 x hx o₀ 1 y hy o₁) ∧
    -- (d) uniqueness of `Γ_f`
    (∀ G G' : GammaDataB PX f hf, IsFunctorB f hf G → IsStarB f hf G →
      IsFunctorB f hf G' → IsStarB f hf G' → G = G')

end RoundTrip.V6_56
