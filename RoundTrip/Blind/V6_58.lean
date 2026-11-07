import Polyfold
/-! Blind formalization of V6_58 (the text's §6.5, Definition 6.38, p. 229).

Text: an sc-Fredholm section `f` over a tame `X` is orientable if, for any two smooth points `x`,
`y` in the same path component, `Γ_f([φ])` does not depend on the class `[φ] : x → y`.

Choices:
- This item is a definition.  B says that the project's `IsOrientableSection` (labelled
  "Definition 6.38") is the text's notion `IsOrientableB` written below.
- Setting: as in `RoundTrip/Blind/V6_48.lean` (`X Y : Type`, `Bd : StrongBundle PX P`, `PX.IsTame`,
  `f` sc-Fredholm).  The project's predicate takes further arguments that the text's definition
  does not have: `PX.AdmitsBumpFunctions`, `Bd.IsScFredholmSectionTame f` (instead of
  `IsScFredholmSection`), `Bd.HasScPlusSectionsThrough`, and four families of paracompactness
  instances.  B quantifies over them only so that the project's side can be stated; my side
  `IsOrientableB` uses only `PX` tame (implicit in the setting) and `f` sc-Fredholm
  (`hfT.toIsScFredholmSection`, the parent projection of `IsScFredholmSectionTame`, checked with
  `#print`).  (If those extra hypotheses are what makes `Γ_f` exist, the project's notion is
  only defined under them.)
- `Γ_f` (Theorem 6.37) is "the" functor `PX → 𝒪_f`, `x ↦ Or^f_x`, with property (∗); as a
  definite description I read "`Γ_f([φ])` does not depend on `[φ]`" as: for EVERY functor `G`
  with property (∗) (`IsFunctorB ∧ IsStarB`, copied from `RoundTrip/Blind/V6_57.lean`, where they
  are explained; composition with the corrected p. 228 formula `ψ(β(s) − 1)`), `G` takes the same
  value on all paths from `x` to `y`.  Under Theorem 6.37 (existence and uniqueness) this is the
  same as "for the functor `Γ_f`".
- "For any two smooth points `x`, `y` in the same path component, … the class `[φ] : x → y`": for
  all smooth `x`, `y` and all sc-smooth paths `φ`, `ψ` from `x` to `y` (paths as in V6_48), the
  values agree.  The path-component condition is automatic when a class `x → y` exists, so it is
  not stated separately.
- Nothing looks false to me.
-/
namespace RoundTrip.V6_58
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

/-- **Definition 6.38**: `f` is orientable: `Γ_f([φ])` does not depend on the class `[φ] : x → y`
(for every functor `G` with property (∗), i.e. for `Γ_f`). -/
def IsOrientableB (f : X → Y) (hf : Bd.IsScFredholmSection f) : Prop :=
  ∀ G : GammaDataB PX f hf, IsFunctorB f hf G → IsStarB f hf G →
    ∀ (x y : X) (hx : x ∈ PX.smoothSet) (hy : y ∈ PX.smoothSet) (φ ψ : (Fin 1 → ℝ) → X)
      (hφ : IsPathB PX φ x y) (hψ : IsPathB PX ψ x y),
      G x y hx hy φ hφ = G x y hx hy ψ hψ

end

/-- Definition 6.38: the project's orientability of sc-Fredholm sections is the text's (stated
under the extra hypotheses the project's predicate needs as arguments). -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × (Fin n → ℝ) × X)]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]
    (Bd : StrongBundle PX P) (f : X → Y)
    (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hfT : Bd.IsScFredholmSectionTame f)
    (hsec : Bd.HasScPlusSectionsThrough),
    IsOrientableSection hX hbump hfT hsec ↔ IsOrientableB f hfT.toIsScFredholmSection

end RoundTrip.V6_58
