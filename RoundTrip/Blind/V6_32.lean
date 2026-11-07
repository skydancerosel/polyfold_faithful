import Polyfold
/-! Blind formalization of V6_32 (the text's §6.5, Proposition 6.28, p. 220).

Text: for an sc-Fredholm section `f`, every smooth `x` has an open `U` with (1) `U` sc-smoothly
contractible; (2) `{y ∈ cl_X(U) | f(y) = 0}` compact; (3) for every sc-smooth path
`φ : [0, 1] → U` an sc⁺-section `s : U × [0, 1] → Y` with `s(φ(t), t) = f(φ(t))`; (4) for
`t₀ ∈ [0, 1]`, `y₀ ∈ U_∞` and a smooth `e₀ ∈ Y_{y₀}` an sc⁺-section `q` with `q(y₀, t₀) = e₀`.
The proof contracts `U = r(V')`, `V'` convex, by `(t, y) ↦ r(ty)`.

Choices:
- Setting: `X Y : Type` (universe 0); `PX : MPolyfold X`, `P : Y → X` with the fibrewise linear
  structure as instances on the fibres, `Bd : StrongBundle PX P` (as in the earlier blind files);
  `f` sc-Fredholm (`IsScFredholmSection`); `x ∈ PX.smoothSet`.  No tameness, no bump functions
  (the text assumes neither).  "an open `U`": an open neighbourhood of `x` (`x ∈ U`).
- `[0, 1]` is `Set.Icc 0 1` in `ℝ¹ = Fin 1 → ℝ` (with `rnPolyfold 1`, the project's M-polyfold
  `ℝ¹`), products are written `ℝ¹ × X` (the project's order) for the text's `U × [0, 1]`.  The
  vocabulary has no M-polyfold `[0, 1]`; a map or section "on `[0, 1] × U`" is read as one which
  is sc-smooth (resp. sc⁺) on some open subset of `ℝ¹ × X` containing `[0, 1] × U`.
  (`(t, y) ↦ r(ty)` of the proof is defined and sc-smooth on such an open set.)
- (1) "sc-smoothly contractible": an `H : ℝ¹ × X → X`, sc-smooth on an open set containing
  `[0, 1] × U` (`IsScSmoothOn` for the product M-polyfold `ℝ¹ × X`), with `H([0, 1] × U) ⊆ U`,
  `H(1, ·) = id` and `H(0, ·)` constant on `U`.
- (2): `IsCompact {y | y ∈ closure U ∧ f(y) = 0}` (`IsZeroAt`).
- (3) "sc-smooth path `φ : [0, 1] → U`": `φ : ℝ¹ → X` sc-smooth on an open set containing `[0, 1]`
  with `φ([0, 1]) ⊆ U`.  "sc⁺-section `s : U × [0, 1] → Y`": a section of the pull-back
  `π*P → ℝ¹ × X` along `π = Prod.snd` (`pullbackSpace`, `StrongBundle.pullback`) which is an
  sc⁺-section of the restriction of `π*P` to an open set `W ⊇ [0, 1] × U`
  (`StrongBundle.restrictOpen`, `restrictSection`); its value at `(t, y)` read in `Y` is
  `pullbackSlice s t y`.  Values off `W` are irrelevant.
- (4) `y₀ ∈ U_∞ = U ∩ X_∞`; "smooth `e₀ ∈ Y_{y₀}`": `e₀` a smooth point of the M-polyfold `Y[0]`
  (`Bd.toMPolyfold0.smoothSet`, as in the project's `HasScPlusSectionsThrough`) with
  `P(e₀) = y₀`; `q` an sc⁺-section over `[0, 1] × U` as in (3), with `q(t₀, y₀) = e₀`.
- Technical hypotheses: the sc-smoothness `hπ` of `π : ℝ¹ × X → X` is quantified over (it is true;
  the pull-back bundle needs it); paracompactness of `ℝⁿ × X`, of `π*Y`, of the subsets of
  `ℝ¹ × X` and of the restricted total spaces are instance hypotheses (true for M-polyfolds,
  which are metrizable; the project's restriction and pull-back constructions take them as
  instance arguments).
- Nothing looks false to me.
-/
namespace RoundTrip.V6_32
open Polyfold

/-- `[0, 1] ⊆ ℝ¹`. -/
def I1 : Set (Fin 1 → ℝ) := Set.Icc 0 1

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace ↥(pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace ↥W]
  [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace
    ↥(pullbackSpace (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X))
      (Subtype.val : W → (Fin 1 → ℝ) × X))]

/-- A (set-theoretic) section candidate of `π*P → ℝ¹ × X`. -/
abbrev Sec1 (P : Y → X) : Type :=
  (Fin 1 → ℝ) × X → ↥(pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))

/-- `s` is a section of `π*P` which is an sc⁺-section over the open set `W ⊆ ℝ¹ × X`. -/
def IsScPlusOn (Bd : StrongBundle PX P)
    (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd) (W : Set ((Fin 1 → ℝ) × X))
    (s : Sec1 P) : Prop :=
  ∃ (hW : IsOpen W) (hne : Nonempty ↥W) (hs : IsSection (pullbackProj P Prod.snd) s),
    letI := hne
    ((Bd.pullback hπ).restrictOpen hW).IsScPlusSection
      (restrictSection (pullbackProj P Prod.snd) W s hs)

/-- `s` is an sc⁺-section over (an open neighbourhood of) `A ⊆ ℝ¹ × X`. -/
def IsScPlusNear (Bd : StrongBundle PX P)
    (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd) (A : Set ((Fin 1 → ℝ) × X))
    (s : Sec1 P) : Prop :=
  ∃ W, A ⊆ W ∧ IsScPlusOn Bd hπ W s

/-- `φ : ℝ¹ → X` is an sc-smooth path on `[0, 1]`. -/
def IsScPathOn (PX : MPolyfold X) (φ : (Fin 1 → ℝ) → X) : Prop :=
  ∃ V, I1 ⊆ V ∧ (rnPolyfold 1).IsScSmoothOn PX φ V

/-- (1) `U` is sc-smoothly contractible. -/
def IsScContractible (PX : MPolyfold X) (U : Set X) : Prop :=
  ∃ (H : (Fin 1 → ℝ) × X → X) (y₀ : X),
    (∃ W, I1 ×ˢ U ⊆ W ∧ ((rnPolyfold 1).prod PX).IsScSmoothOn PX H W) ∧
    (∀ t ∈ I1, ∀ y ∈ U, H (t, y) ∈ U) ∧ (∀ y ∈ U, H (pt1 1, y) = y) ∧
    (∀ y ∈ U, H (pt1 0, y) = y₀)

/-- (3) along every sc-smooth path in `U` there is an sc⁺-section `s` with
`s(φ(t), t) = f(φ(t))`. -/
def HasPathSections (Bd : StrongBundle PX P)
    (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd) (f : X → Y) (U : Set X) : Prop :=
  ∀ φ : (Fin 1 → ℝ) → X, IsScPathOn PX φ → (∀ t ∈ I1, φ t ∈ U) →
    ∃ s : Sec1 P, IsScPlusNear Bd hπ (I1 ×ˢ U) s ∧ ∀ t ∈ I1, pullbackSlice s t (φ t) = f (φ t)

/-- (4) sc⁺-sections over `[0, 1] × U` through every smooth fibre point over `[0, 1] × U_∞`. -/
def HasPointSections (Bd : StrongBundle PX P)
    (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd) (U : Set X) : Prop :=
  ∀ t₀ ∈ I1, ∀ y₀ ∈ U ∩ PX.smoothSet, ∀ e₀ ∈ Bd.toMPolyfold0.smoothSet, P e₀ = y₀ →
    ∃ q : Sec1 P, IsScPlusNear Bd hπ (I1 ×ˢ U) q ∧ pullbackSlice q t₀ y₀ = e₀

/-- The properties (1)–(4) of Proposition 6.28 for the open neighbourhood `U` of `x`. -/
def IsNbhd628 (Bd : StrongBundle PX P)
    (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd) (f : X → Y) (x : X)
    (U : Set X) : Prop :=
  IsOpen U ∧ x ∈ U ∧ IsScContractible PX U ∧
    IsCompact {y | y ∈ closure U ∧ IsZeroAt P f y} ∧
    HasPathSections Bd hπ f U ∧ HasPointSections Bd hπ U

end

/-- Proposition 6.28: every smooth point has an open neighbourhood `U` with (1)–(4). -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace ↥(pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace ↥W]
    [∀ W : Set ((Fin 1 → ℝ) × X), ParacompactSpace
      ↥(pullbackSpace (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X))
        (Subtype.val : W → (Fin 1 → ℝ) × X))]
    (Bd : StrongBundle PX P) (f : X → Y), Bd.IsScFredholmSection f →
    ∀ hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd,
    ∀ x ∈ PX.smoothSet, ∃ U : Set X, IsNbhd628 Bd hπ f x U

end RoundTrip.V6_32
