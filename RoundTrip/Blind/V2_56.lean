import Polyfold
/-! Blind formalization of V2_56 (the text's §2.5, Definition 2.49, p. 50).

Text: a section of `p : K → O` is `f : O → K` with `p ∘ f = 1_O`; sc-smooth if it is sc-smooth
into `K[0]`, sc⁺-smooth if sc-smooth into `K[1]` (the text writes `K(0)`, `K(1)`);
`f(x) = (x, 𝐟(x))` with the principal part `𝐟`.

Choices:
- This item is a definition.  Setting: `E F : ScBanach` (levels in `Type`, forced by
  `ScBanach`), `U` relatively open in a partial quadrant `C ⊆ E`, `R` a strong bundle retraction
  on `U ◁ F` (my `IsStrongBundleRetractionB`, copied from `RoundTrip/Blind/V2_54.lean`, which
  states that the project's `IsStrongBundleRetraction` is this notion), `K = R(U ◁ F)` (`KB`),
  `O = r(U)` (`baseB`, `r(u)` the first component of `R(u, 0)`), `p(u, h) = u`, as in my
  `RoundTrip/Blind/V2_55.lean`.
- A section (`IsSectionB`): a map `f : O → K` (a total `f : E₀ → E₀ × F₀`, only its values on `O`
  matter) with `f(O) ⊆ K` and `p(f(x)) = x` for `x ∈ O`.
- sc-smooth section (`IsScSmoothSectionB`): a section which is sc-smooth as a map between the
  retracts `(O, C, E)` and `(K[0], C ◁ F, E ⊕ F)` (Definition 2.7: `f ∘ ρ` sc-smooth for a
  retraction `ρ` onto `O`, my `IsScSmoothRetractMapB`, as in `RoundTrip/Blind/V2_6.lean`).
- sc⁺-section (`IsScPlusSectionB`): a section which is sc-smooth into `K[1]`: `f` takes values in
  `K[1] = K ∩ (E₀ ⊕ F₁)` and the induced map `f₁ : O → K[1] ⊆ (E ⊕ F¹)₀` (fibre component lifted
  to `F₁`) is sc-smooth between `(O, C, E)` and `(K[1], C ◁ F¹, E ⊕ F¹)`.  I write it as: there is
  `f₁ : E₀ → E₀ × F₁` lifting `f` on `O`, sc-smooth into `K[1]`.
- Principal part: `𝐟(x)` is the second component of `f(x)`; B asserts `f(x) = (x, 𝐟(x))` on `O`
  for every section.
- B asserts that the project's `IsScSmoothSection` is `IsScSmoothSectionB`, and that the project's
  `IsScPlusSection` (stated for the lifted map `f₁ : E₀ → E₀ × F₁`, checked with `#print`) holds
  for a lift of `f` exactly when `f` is an sc⁺-section in my sense.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_56
open Polyfold

/-- `(U ◁ F)_{m,k} = U_m ⊕ F_k` (as in `V2_54`). -/
def doubleLevelB (E F : ScBanach) (U : Set (E.lvl 0)) (m k : ℕ) : Set (E.lvl m × F.lvl k) :=
  {q | E.toBase m q.1 ∈ U}

/-- Definition 2.47: a strong bundle map (as in `V2_54`). -/
def IsStrongBundleMapB {E F E' F' : ScBanach} (U : Set (E.lvl 0)) (U' : Set (E'.lvl 0))
    (Φ : E.lvl 0 × F.lvl 0 → E'.lvl 0 × F'.lvl 0) : Prop :=
  (∃ φ : E.lvl 0 → E'.lvl 0, ∀ u ∈ U, φ u ∈ U' ∧ ∀ h : F.lvl 0, (Φ (u, h)).1 = φ u) ∧
  (∀ u ∈ U, IsLinearMap ℝ (fun h : F.lvl 0 => (Φ (u, h)).2)) ∧
  (∀ m k : ℕ, k ≤ m + 1 → ∀ q ∈ doubleLevelB E F U m k,
    ∃ q' : E'.lvl m × F'.lvl k,
      Φ (E.toBase m q.1, F.toBase k q.2) = (E'.toBase m q'.1, F'.toBase k q'.2)) ∧
  IsScSmooth (E := E.prod F) (F := E'.prod F') (U ×ˢ Set.univ) Φ ∧
  (∃ Φ₁ : (E.prod F.shift).lvl 0 → (E'.prod F'.shift).lvl 0,
    (∀ u ∈ U, ∀ h : F.lvl 1,
      (Φ₁ (u, h)).1 = (Φ (u, F.toBase 1 h)).1 ∧
      F'.toBase 1 (Φ₁ (u, h)).2 = (Φ (u, F.toBase 1 h)).2) ∧
    IsScSmooth (E := E.prod F.shift) (F := E'.prod F'.shift) (U ×ˢ Set.univ) Φ₁)

/-- Definition 2.47: a strong bundle retraction (as in `V2_54`). -/
def IsStrongBundleRetractionB {E F : ScBanach} (U : Set (E.lvl 0))
    (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0) : Prop :=
  IsStrongBundleMapB U U R ∧ ∀ u ∈ U, ∀ h : F.lvl 0, R (R (u, h)) = R (u, h)

/-- Definition 2.7: `f : O → O'` is sc-smooth between retracts (as in `V2_6`). -/
def IsScSmoothRetractMapB (E : ScBanach) (C O : Set (E.lvl 0)) (E' : ScBanach)
    (O' : Set (E'.lvl 0)) (f : E.lvl 0 → E'.lvl 0) : Prop :=
  Set.MapsTo f O O' ∧ ∃ ρ : ScRetraction E C, ρ.retract = O ∧ IsScSmooth ρ.U (f ∘ ρ.toFun)

/-- `K = R(U ◁ F)`. -/
def KB {E F : ScBanach} (U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0) :
    Set (E.lvl 0 × F.lvl 0) :=
  R '' (U ×ˢ Set.univ)

/-- `O = r(U)`. -/
def baseB {E F : ScBanach} (U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0) :
    Set (E.lvl 0) :=
  (fun u => (R (u, 0)).1) '' U

/-- `K[1] = K_{0,1}` as a subset of `(E ⊕ F¹)₀ = E₀ × F₁`. -/
def KoneB {E F : ScBanach} (K : Set (E.lvl 0 × F.lvl 0)) : Set ((E.prod F.shift).lvl 0) :=
  {q | (q.1, F.toBase 1 q.2) ∈ K}

/-- **Definition 2.49**: a section `f : O → K` of `p`, `p ∘ f = 1_O`. -/
def IsSectionB {E F : ScBanach} (O : Set (E.lvl 0)) (K : Set (E.lvl 0 × F.lvl 0))
    (f : E.lvl 0 → E.lvl 0 × F.lvl 0) : Prop :=
  ∀ x ∈ O, f x ∈ K ∧ (f x).1 = x

/-- **Definition 2.49**: an sc-smooth section: sc-smooth into `K[0]`. -/
def IsScSmoothSectionB {E F : ScBanach} (C O : Set (E.lvl 0)) (K : Set (E.lvl 0 × F.lvl 0))
    (f : E.lvl 0 → E.lvl 0 × F.lvl 0) : Prop :=
  IsSectionB O K f ∧ IsScSmoothRetractMapB E C O (E.prod F) K f

/-- **Definition 2.49**: an sc⁺-section: sc-smooth into `K[1]`. -/
def IsScPlusSectionB {E F : ScBanach} (C O : Set (E.lvl 0)) (K : Set (E.lvl 0 × F.lvl 0))
    (f : E.lvl 0 → E.lvl 0 × F.lvl 0) : Prop :=
  IsSectionB O K f ∧
    ∃ f₁ : E.lvl 0 → (E.prod F.shift).lvl 0,
      (∀ x ∈ O, (f₁ x).1 = (f x).1 ∧ F.toBase 1 (f₁ x).2 = (f x).2) ∧
      IsScSmoothRetractMapB E C O (E.prod F.shift) (KoneB K) f₁

/-- The principal part `𝐟(x)` of a section, `f(x) = (x, 𝐟(x))`. -/
def principalPartB {E F : ScBanach} (f : E.lvl 0 → E.lvl 0 × F.lvl 0) (x : E.lvl 0) : F.lvl 0 :=
  (f x).2

/-- Definition 2.49: sections, sc-smooth sections, sc⁺-sections of `p : K → O` (the project's
notions are these) and the principal part, `f(x) = (x, 𝐟(x))`. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0),
    IsRelOpenInQuadrant E C U → IsStrongBundleRetractionB U R →
      -- sc-smooth sections (the project's notion is the text's)
      (∀ f : E.lvl 0 → E.lvl 0 × F.lvl 0,
        IsScSmoothSection C (baseB U R) (KB U R) f ↔
          IsScSmoothSectionB C (baseB U R) (KB U R) f) ∧
      -- sc⁺-sections (the project's notion, stated for the lift `f₁`, is the text's)
      (∀ f : E.lvl 0 → E.lvl 0 × F.lvl 0,
        IsScPlusSectionB C (baseB U R) (KB U R) f ↔
          ∃ f₁ : E.lvl 0 → E.lvl 0 × F.lvl 1, IsScPlusSection C (baseB U R) (KB U R) f₁ ∧
            ∀ x ∈ baseB U R, f x = ((f₁ x).1, F.toBase 1 (f₁ x).2)) ∧
      -- the principal part: `f(x) = (x, 𝐟(x))`
      (∀ f : E.lvl 0 → E.lvl 0 × F.lvl 0, IsSectionB (baseB U R) (KB U R) f →
        ∀ x ∈ baseB U R, f x = (x, principalPartB f x))

end RoundTrip.V2_56
