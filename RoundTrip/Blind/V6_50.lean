import Polyfold
/-! Blind formalization of V6_50 (the text's §6.5, the paragraph after Theorem 6.35 and
Definition 6.36, p. 227).

Text: fixing `o_x`, `o_y = φ_*o_x` for a path `φ` in `U` from `x` to `y` does not depend on the
path, and `ψ_*o_{y₁} = o_{y₂}` for paths in `U`.  An open contractible `U(x)` on which the local
propagation can be carried out is an orientable neighbourhood of `(f, x)`; a choice of orientations
of `DET(f, y)`, `y ∈ U_∞`, with the propagation property is a continuous orientation, and an
orientable neighbourhood has precisely two.

Choices:
- B is the conjunction of: (1) the two claims of the paragraph (independence of the path, and
  `ψ_*o_{y₁} = o_{y₂}`); (2) the definition of continuous orientations, stated as the
  equivalence of the project's `IsContinuousOrientation` (with `V = U`) with my reading
  `IsContOrB`; (3) "an orientable neighbourhood has precisely two" continuous orientations.  The
  definition of orientable neighbourhoods is my `IsOrNbhdB` (used in (1) and (3)); I do not
  compare it with the project's `IsOrientableNbhd`, which (checked with `#print`) has a different
  shape (a pair `V ⊆ U`, sc-smooth paths in `U` between smooth points of `V`, no
  contractibility).
- Setting: as in `RoundTrip/Blind/V6_48.lean` (`X Y : Type`, `Bd : StrongBundle PX P`,
  `PX.IsTame` — the setting of Theorem 6.35 —, `f` sc-Fredholm, `Bd.IsScFredholmSection f`; the
  paracompactness instance families only because the project's `HasLocalPropagation`/`IsPush`
  take them).  The DOUBT of V6_48 (no hypothesis guaranteeing sc⁺-sections) applies here too:
  (3) needs `Or_x^f` to have two elements, i.e. `Lin(f, x) ≠ ∅`.
- Paths as in V6_48 (sc-smooth `γ : ℝ¹ → X`, `γ([0, 1]) ⊆ U`); push-forwards `φ_*` are the
  project's `IsPush` in the chart `c` of `U`; orientations `o_y` of `DET(f, y)` are read in the
  chart `c` (`ChartPoint.Or f (chartPtOf c hc _ _) hf`, Definition 6.27).
- "Orientable neighbourhood of `(f, x)`" (`IsOrNbhdB`): `U` open, `x ∈ U`, sc-smoothly
  contractible (the text says "contractible" here; I read it as the sc-smooth contractibility of
  Theorem 6.35, whose `U(x)` this is), with the local propagation property in a strong bundle
  chart `c` (the project's `HasLocalPropagation`, checked, see V6_48).  `x` smooth.
- (1) is stated for every orientable neighbourhood `U` of `(f, x)` in a chart `c` and every
  `o_x`: (1a) any two push-forwards along any two paths in `U` from `x` to `y` map `o_x` to the
  same `o_y`; (1b) for paths `φ₁` from `x` to `y₁`, `φ₂` from `x` to `y₂` and `ψ` from `y₁` to
  `y₂` in `U`, with push-forwards `e₁`, `e₂`, `e`: `e(e₁ o_x) = e₂ o_x`, i.e. `ψ_*o_{y₁} = o_{y₂}`.
- "Continuous orientation" (`IsContOrB`): `o` assigns to every smooth `y ∈ U` an orientation of
  `DET(f, y)` (read in `c`) such that `e(o_{y₁}) = o_{y₂}` for every push-forward `e` along every
  sc-smooth path in `U` from `y₁` to `y₂` ("the propagation property").
- "Precisely two": there are `o₁ ≠ o₂` continuous orientations and every continuous orientation is
  one of them.
- Nothing looks false to me apart from the DOUBT.
-/
namespace RoundTrip.V6_50
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

/-- **Definition 6.36**: `U` is an orientable neighbourhood of `(f, x)` (in the chart `c`): open,
containing `x`, sc-smoothly contractible, with the local propagation property in `c`. -/
def IsOrNbhdB (f : X → Y) (hf : Bd.IsScFredholmSection f) (c : StrongBundleChart PX P)
    (hc : Bd.IsChart c) (U : Set X) (x : X) : Prop :=
  IsOpen U ∧ x ∈ U ∧ IsScContractibleB PX U ∧ HasLocalPropagation f hf c hc U

/-- **Definition 6.36**: `o` (orientations of `DET(f, y)` for the smooth `y ∈ U`, read in `c`) is a
continuous orientation: it is preserved by every push-forward along every sc-smooth path in `U`. -/
def IsContOrB (f : X → Y) (hf : Bd.IsScFredholmSection f) (c : StrongBundleChart PX P)
    (hc : Bd.IsChart c) (U : Set X) (hU : U ⊆ c.φ.source)
    (o : ∀ (y : X) (hy : y ∈ U) (hys : y ∈ PX.smoothSet),
      ChartPoint.Or f (chartPtOf c hc (hU hy) hys) hf) : Prop :=
  ∀ (γ : (Fin 1 → ℝ) → X), (rnPolyfold 1).IsScSmoothMap PX γ →
    ∀ (hγ : PathInB γ U) {y₁ y₂ : X} (hy₁ : y₁ ∈ U) (hy₂ : y₂ ∈ U)
      (hs₁ : y₁ ∈ PX.smoothSet) (hs₂ : y₂ ∈ PX.smoothSet)
      (h₀ : γ (pt1 0) = y₁) (h₁ : γ (pt1 1) = y₂)
      (e : ChartPoint.Or f (chartPtOf c hc (hU hy₁) hs₁) hf ≃
        ChartPoint.Or f (chartPtOf c hc (hU hy₂) hs₂) hf),
      IsPush f hf c hc γ (fun q hq => hU (hγ q hq)) h₀ h₁ (hU hy₁) (hU hy₂) hs₁ hs₂ e →
        e (o y₁ hy₁ hs₁) = o y₂ hy₂ hs₂

end

/-- The propagation `o_y = φ_*o_x` in an orientable neighbourhood does not depend on the path and
satisfies `ψ_*o_{y₁} = o_{y₂}`; continuous orientations (Definition 6.36) are the project's; an
orientable neighbourhood has precisely two continuous orientations. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f),
    PX.IsTame →
    -- (1) the paragraph after Theorem 6.35
    (∀ (c : StrongBundleChart PX P) (hc : Bd.IsChart c) (U : Set X) (x : X),
      IsOrNbhdB f hf c hc U x → ∀ (hU : U ⊆ c.φ.source) (hx : x ∈ PX.smoothSet)
        (hxc : x ∈ c.φ.source) (ox : ChartPoint.Or f (chartPtOf c hc hxc hx) hf),
        -- (1a) `φ_*o_x` does not depend on the path `φ` (nor on the push-forward)
        (∀ (y : X) (hy : y ∈ PX.smoothSet) (hyc : y ∈ c.φ.source) (φ φ' : (Fin 1 → ℝ) → X)
            (hφ : IsPathB PX φ x y) (hφ' : IsPathB PX φ' x y) (hφU : PathInB φ U)
            (hφ'U : PathInB φ' U)
            (e e' : ChartPoint.Or f (chartPtOf c hc hxc hx) hf ≃
              ChartPoint.Or f (chartPtOf c hc hyc hy) hf),
            IsPush f hf c hc φ (fun q hq => hU (hφU q hq)) hφ.2.1 hφ.2.2 hxc hyc hx hy e →
            IsPush f hf c hc φ' (fun q hq => hU (hφ'U q hq)) hφ'.2.1 hφ'.2.2 hxc hyc hx hy e' →
            e ox = e' ox) ∧
        -- (1b) `ψ_*o_{y₁} = o_{y₂}`
        (∀ (y₁ y₂ : X) (hy₁ : y₁ ∈ PX.smoothSet) (hy₂ : y₂ ∈ PX.smoothSet)
            (hy₁c : y₁ ∈ c.φ.source) (hy₂c : y₂ ∈ c.φ.source) (φ₁ φ₂ ψ : (Fin 1 → ℝ) → X)
            (hφ₁ : IsPathB PX φ₁ x y₁) (hφ₂ : IsPathB PX φ₂ x y₂) (hψ : IsPathB PX ψ y₁ y₂)
            (hφ₁U : PathInB φ₁ U) (hφ₂U : PathInB φ₂ U) (hψU : PathInB ψ U)
            (e₁ : ChartPoint.Or f (chartPtOf c hc hxc hx) hf ≃
              ChartPoint.Or f (chartPtOf c hc hy₁c hy₁) hf)
            (e₂ : ChartPoint.Or f (chartPtOf c hc hxc hx) hf ≃
              ChartPoint.Or f (chartPtOf c hc hy₂c hy₂) hf)
            (e : ChartPoint.Or f (chartPtOf c hc hy₁c hy₁) hf ≃
              ChartPoint.Or f (chartPtOf c hc hy₂c hy₂) hf),
            IsPush f hf c hc φ₁ (fun q hq => hU (hφ₁U q hq)) hφ₁.2.1 hφ₁.2.2 hxc hy₁c hx hy₁ e₁ →
            IsPush f hf c hc φ₂ (fun q hq => hU (hφ₂U q hq)) hφ₂.2.1 hφ₂.2.2 hxc hy₂c hx hy₂ e₂ →
            IsPush f hf c hc ψ (fun q hq => hU (hψU q hq)) hψ.2.1 hψ.2.2 hy₁c hy₂c hy₁ hy₂ e →
            e (e₁ ox) = e₂ ox)) ∧
    -- (2) Definition 6.36, continuous orientations: the project's notion (with `V = U`) is mine
    (∀ (c : StrongBundleChart PX P) (hc : Bd.IsChart c) (U : Set X) (hU : U ⊆ c.φ.source)
      (o : ∀ (y : X) (hy : y ∈ U) (hys : y ∈ PX.smoothSet),
        ChartPoint.Or f (chartPtOf c hc (hU hy) hys) hf),
      IsContinuousOrientation f hf c hc hU (Set.Subset.refl U) o ↔ IsContOrB f hf c hc U hU o) ∧
    -- (3) an orientable neighbourhood has precisely two continuous orientations
    (∀ (c : StrongBundleChart PX P) (hc : Bd.IsChart c) (U : Set X) (x : X)
      (hU : U ⊆ c.φ.source), IsOrNbhdB f hf c hc U x → x ∈ PX.smoothSet →
      ∃ o₁ o₂ : (∀ (y : X) (hy : y ∈ U) (hys : y ∈ PX.smoothSet),
          ChartPoint.Or f (chartPtOf c hc (hU hy) hys) hf),
        o₁ ≠ o₂ ∧ IsContOrB f hf c hc U hU o₁ ∧ IsContOrB f hf c hc U hU o₂ ∧
        ∀ o, IsContOrB f hf c hc U hU o → o = o₁ ∨ o = o₂)

end RoundTrip.V6_50
