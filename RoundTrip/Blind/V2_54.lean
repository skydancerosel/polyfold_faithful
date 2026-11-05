import Polyfold
/-! Blind formalization of V2_54 (the text's §2.5, Definition 2.47, p. 48).

Text: `U ◁ F` is `U × F` with the double filtration `U_m ⊕ F_k`, `0 ≤ k ≤ m + 1`, and
`(U ◁ F)[i]` with levels `U_m ⊕ F_{m+i}`.  A strong bundle map `Φ(u, h) = (φ(u), Γ(u, h))`,
`Γ` linear in `h`, preserves the double filtration and is sc-smooth
`(U ◁ F)[i] → (U' ◁ F')[i]`, `i = 0, 1`; a strong bundle retraction is one with `R ∘ R = R`;
`R(u, h) = (r(u), Γ(u, h))` with `r` an sc-smooth retraction.

Choices:
- This item is a definition plus one property.  Setting: `E F E' F' : ScBanach` (levels in `Type`,
  forced by `ScBanach`), `U` relatively open in a partial quadrant `C ⊆ E` and `U'` in `C' ⊆ E'`
  (the project's `IsRelOpenInQuadrant`, Definition 1.11 setting).  Maps are total functions
  `E₀ × F₀ → E'₀ × F'₀`; only their values on `U × F` matter.
- `U ◁ F` and its levels: `(U ◁ F)_{m,k} = U_m ⊕ F_k` is my `doubleLevelB` (a subset of
  `E_m × F_k`: the `(a, b)` with `a ∈ U` in `E₀`).  `(U ◁ F)[i]` is the set `U × F^i`, i.e.
  `U ×ˢ univ` inside the sc-space `E ⊕ F^i` (`E.prod F` for `i = 0`, `E.prod F.shift` for
  `i = 1`); B checks that its level `m` is `U_m ⊕ F_{m+i}`.  B also checks that the project's
  `doubleLevel` is `doubleLevelB` for `k ≤ m + 1`.
- Strong bundle map (`IsStrongBundleMapB`): (1) `Φ(u, h) = (φ(u), Γ(u, h))` with `φ(U) ⊆ U'`
  (first component independent of `h`; "`Φ : U ◁ F → U' ◁ F'`"); (2) `h ↦ Γ(u, h)` is linear for
  `u ∈ U`; (3) preserves the double filtration: for `k ≤ m + 1`, `(u, h) ∈ U_m ⊕ F_k` is sent into
  `E'_m ⊕ F'_k` (i.e. into `U'_m ⊕ F'_k`, by (1)); (4) sc-smooth `(U ◁ F)[0] → (U' ◁ F')[0]`:
  `IsScSmooth` (Definition 1.15) of `Φ` on `U × F ⊆ E ⊕ F` into `E' ⊕ F'`; (5) sc-smooth
  `(U ◁ F)[1] → (U' ◁ F')[1]`: the map `Φ[1] : U ⊕ F¹ → U' ⊕ F'¹` induced by `Φ` (it exists by
  (3) with `m = 0, k = 1`) is sc-smooth; I write this as: there is `Φ₁ : E₀ × F₁ → E'₀ × F'₁`
  agreeing with `Φ` on `U × F₁` (fibre component lifted to `F'₁`) which is sc-smooth on `U × F₁`.
- Strong bundle retraction (`IsStrongBundleRetractionB`): a strong bundle map `U ◁ F → U ◁ F`
  with `R ∘ R = R` on `U × F`.
- The property: for such `R`, `r(u) := ` first component of `R(u, h)` (any `h`) is an sc-smooth
  retraction of `U` (the project's `ScRetraction E C`, checked with `#print`: an sc-smooth
  `r : U → U` with `r ∘ r = r`, `U` relatively open in `C`; it is the text's Definition 2.1).  The
  form `R(u, h) = (r(u), Γ(u, h))` with `Γ` linear is part of the definition.
- B also asserts that the project's `IsStrongBundleMap` and `IsStrongBundleRetraction` are
  equivalent to my definitions (for `U`, `U'` relatively open in partial quadrants).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_54
open Polyfold

/-- `(U ◁ F)_{m,k} = U_m ⊕ F_k`, as a subset of `E_m × F_k`. -/
def doubleLevelB (E F : ScBanach) (U : Set (E.lvl 0)) (m k : ℕ) : Set (E.lvl m × F.lvl k) :=
  {q | E.toBase m q.1 ∈ U}

/-- **Definition 2.47**: `Φ : U ◁ F → U' ◁ F'` is a strong bundle map. -/
def IsStrongBundleMapB {E F E' F' : ScBanach} (U : Set (E.lvl 0)) (U' : Set (E'.lvl 0))
    (Φ : E.lvl 0 × F.lvl 0 → E'.lvl 0 × F'.lvl 0) : Prop :=
  -- `Φ(u, h) = (φ(u), Γ(u, h))` with `φ(U) ⊆ U'`
  (∃ φ : E.lvl 0 → E'.lvl 0, ∀ u ∈ U, φ u ∈ U' ∧ ∀ h : F.lvl 0, (Φ (u, h)).1 = φ u) ∧
  -- `Γ` is linear in `h`
  (∀ u ∈ U, IsLinearMap ℝ (fun h : F.lvl 0 => (Φ (u, h)).2)) ∧
  -- `Φ` preserves the double filtration
  (∀ m k : ℕ, k ≤ m + 1 → ∀ q ∈ doubleLevelB E F U m k,
    ∃ q' : E'.lvl m × F'.lvl k,
      Φ (E.toBase m q.1, F.toBase k q.2) = (E'.toBase m q'.1, F'.toBase k q'.2)) ∧
  -- `Φ : (U ◁ F)[0] → (U' ◁ F')[0]` is sc-smooth
  IsScSmooth (E := E.prod F) (F := E'.prod F') (U ×ˢ Set.univ) Φ ∧
  -- `Φ : (U ◁ F)[1] → (U' ◁ F')[1]` is sc-smooth
  (∃ Φ₁ : (E.prod F.shift).lvl 0 → (E'.prod F'.shift).lvl 0,
    (∀ u ∈ U, ∀ h : F.lvl 1,
      (Φ₁ (u, h)).1 = (Φ (u, F.toBase 1 h)).1 ∧
      F'.toBase 1 (Φ₁ (u, h)).2 = (Φ (u, F.toBase 1 h)).2) ∧
    IsScSmooth (E := E.prod F.shift) (F := E'.prod F'.shift) (U ×ˢ Set.univ) Φ₁)

/-- **Definition 2.47**: a strong bundle retraction `R : U ◁ F → U ◁ F`, `R ∘ R = R`. -/
def IsStrongBundleRetractionB {E F : ScBanach} (U : Set (E.lvl 0))
    (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0) : Prop :=
  IsStrongBundleMapB U U R ∧ ∀ u ∈ U, ∀ h : F.lvl 0, R (R (u, h)) = R (u, h)

/-- Definition 2.47: the double filtration of `U ◁ F` and the levels of `(U ◁ F)[i]`; strong
bundle maps and retractions (the project's notions are these); and the base map of a strong
bundle retraction is an sc-smooth retraction. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)), IsRelOpenInQuadrant E C U →
    -- `(U ◁ F)_{m,k} = U_m ⊕ F_k`, `0 ≤ k ≤ m + 1`
    (∀ m k : ℕ, k ≤ m + 1 → doubleLevel E F U m k = doubleLevelB E F U m k) ∧
    -- `(U ◁ F)[0]` has levels `U_m ⊕ F_m`
    (∀ m : ℕ, (E.prod F).lvlSet (U ×ˢ (Set.univ : Set (F.lvl 0))) m = doubleLevelB E F U m m) ∧
    -- `(U ◁ F)[1]` has levels `U_m ⊕ F_{m+1}`
    (∀ m : ℕ, (E.prod F.shift).lvlSet (U ×ˢ (Set.univ : Set (F.lvl 1))) m =
      doubleLevelB E F U m (m + 1)) ∧
    -- strong bundle maps (the project's notion is the text's)
    (∀ (E' F' : ScBanach) (C' U' : Set (E'.lvl 0)), IsRelOpenInQuadrant E' C' U' →
      ∀ Φ : E.lvl 0 × F.lvl 0 → E'.lvl 0 × F'.lvl 0,
        IsStrongBundleMap U U' Φ ↔ IsStrongBundleMapB U U' Φ) ∧
    -- strong bundle retractions (the project's notion is the text's)
    (∀ R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0,
      IsStrongBundleRetraction U R ↔ IsStrongBundleRetractionB U R) ∧
    -- `R(u, h) = (r(u), Γ(u, h))` with `r` an sc-smooth retraction of `U`
    (∀ R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0, IsStrongBundleRetractionB U R →
      ∃ r : ScRetraction E C, r.U = U ∧ ∀ u ∈ U, ∀ h : F.lvl 0, (R (u, h)).1 = r.toFun u)

end RoundTrip.V2_54
