import Polyfold
/-! Blind formalization of V2_55 (the text's §2.5, Definition 2.48 and the remarks after it,
pp. 49–50).

Text: a local strong bundle retract is `K = R(U ◁ F)` for a strong bundle retraction, `p : K → O`;
`K_{m,k} = {(u, h) ∈ O_m ⊕ F_k : Γ(u, h) = h}`, `K[i] = K_{0,i}` with the filtration
`K_{m,m+i}`; the projections `p : K[i] → O` are sc-smooth.

Choices:
- This item is a definition plus properties.  Setting: `E F : ScBanach` (levels in `Type`, forced
  by `ScBanach`), `C ⊆ E` a partial quadrant, `U` relatively open in `C`.  Strong bundle
  retractions `R : U ◁ F → U ◁ F` are my `IsStrongBundleRetractionB` (copied from my
  `RoundTrip/Blind/V2_54.lean`, which states that the project's `IsStrongBundleRetraction` is the
  same notion): `R(u, h) = (r(u), Γ(u, h))`, `Γ` linear in `h`, double filtration preserved,
  sc-smooth on `(U ◁ F)[i]`, `i = 0, 1`, and `R ∘ R = R`.
- `K = R(U ◁ F) = R(U × F)` (`KB`), `O = r(U)` (`baseB`, with `r(u)` the first component of
  `R(u, 0)`), `p(u, h) = u`.  Local strong bundle retract (`IsLocalStrongBundleRetractB C K`): `K`
  is `R(U ◁ F)` for some such `U`, `R`.  B asserts that the project's `IsStrongBundleRetract`
  is this.
- "`p : K → O`": `p(K) ⊆ O`.
- `K_{m,k} = {(u, h) ∈ O_m ⊕ F_k : Γ(u, h) = h}`: I read the displayed formula as the text's
  description of the double filtration `K ∩ (E_m ⊕ F_k)` that `K` inherits from `U ◁ F`
  (`0 ≤ k ≤ m + 1`).  `KcapB K m k = {(a, b) ∈ E_m × F_k | (a, b) ∈ K}` is the inherited level,
  `KmkB U R m k` the formula (with `Γ(u, h)` the second component of `R(u, h)`); B asserts they
  agree, and that the project's `strongLevel` is `KmkB`.
- `K[i] = K_{0,i}` with the filtration `K_{m,m+i}`: `K[0] = K ⊆ E ⊕ F`, `K[1] = K_{0,1}` as a subset
  of `(E ⊕ F¹)₀ = E₀ × F₁` (`KoneB`).  B asserts: the level `m` of `K[i]` inside the sc-space
  `E ⊕ F^i` is `K_{m,m+i}` (`KmkB U R m (m + i)`); the project's `strongShiftOne` is `KoneB` and
  its `strongLevelShift K i` is `K_{m,m+i}` (`i = 0, 1`).
- "The projections `p : K[i] → O` are sc-smooth": sc-smooth between the retracts
  `(K[i], C ◁ F^i, E ⊕ F^i)` and `(O, C, E)` in the sense of Definition 2.7 (`p` maps `K[i]` into
  `O`, and `p ∘ ρ` is sc-smooth for a retraction `ρ` onto `K[i]`; my `IsScSmoothRetractMapB`, as
  in `RoundTrip/Blind/V2_6.lean`).  The partial quadrant of `K[i]` is `C × F^i` (`C ◁ F^i`).  The
  existential form also asserts that `K[i]` is an sc-smooth retract, which the claim presupposes.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_55
open Polyfold

/-- `(U ◁ F)_{m,k} = U_m ⊕ F_k`, as a subset of `E_m × F_k` (as in `V2_54`). -/
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

/-- `O = r(U)`, `r(u)` the first component of `R(u, 0)`. -/
def baseB {E F : ScBanach} (U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0) :
    Set (E.lvl 0) :=
  (fun u => (R (u, 0)).1) '' U

/-- **Definition 2.48**: a local strong bundle retract `K = R(U ◁ F)`. -/
def IsLocalStrongBundleRetractB {E F : ScBanach} (C : Set (E.lvl 0))
    (K : Set (E.lvl 0 × F.lvl 0)) : Prop :=
  ∃ (U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0),
    IsRelOpenInQuadrant E C U ∧ IsStrongBundleRetractionB U R ∧ K = KB U R

/-- The level `K ∩ (E_m ⊕ F_k)` inherited from `U ◁ F`, as a subset of `E_m × F_k`. -/
def KcapB {E F : ScBanach} (K : Set (E.lvl 0 × F.lvl 0)) (m k : ℕ) :
    Set (E.lvl m × F.lvl k) :=
  {q | (E.toBase m q.1, F.toBase k q.2) ∈ K}

/-- The text's formula `K_{m,k} = {(u, h) ∈ O_m ⊕ F_k : Γ(u, h) = h}`. -/
def KmkB {E F : ScBanach} (U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0)
    (m k : ℕ) : Set (E.lvl m × F.lvl k) :=
  {q | E.toBase m q.1 ∈ baseB U R ∧ (R (E.toBase m q.1, F.toBase k q.2)).2 = F.toBase k q.2}

/-- `K[1] = K_{0,1}`, as a subset of `(E ⊕ F¹)₀ = E₀ × F₁`. -/
def KoneB {E F : ScBanach} (K : Set (E.lvl 0 × F.lvl 0)) : Set ((E.prod F.shift).lvl 0) :=
  {q | (q.1, F.toBase 1 q.2) ∈ K}

/-- Definition 2.48 and the remarks after it: local strong bundle retracts (the project's notion
is the text's), `p : K → O`, the double filtration `K_{m,k}`, the spaces `K[i]` with filtration
`K_{m,m+i}`, and the sc-smoothness of `p : K[i] → O`. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C : Set (E.lvl 0)),
    -- local strong bundle retracts (the project's notion is the text's)
    (∀ K : Set (E.lvl 0 × F.lvl 0), IsStrongBundleRetract C K ↔ IsLocalStrongBundleRetractB C K) ∧
    ∀ (U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0),
      IsRelOpenInQuadrant E C U → IsStrongBundleRetractionB U R →
        -- `p : K → O`
        (∀ q ∈ KB U R, q.1 ∈ baseB U R) ∧
        -- `K_{m,k} = {(u, h) ∈ O_m ⊕ F_k : Γ(u, h) = h}`, `0 ≤ k ≤ m + 1`
        (∀ m k : ℕ, k ≤ m + 1 → KcapB (KB U R) m k = KmkB U R m k) ∧
        (∀ m k : ℕ, k ≤ m + 1 → strongLevel (KB U R) m k = KmkB U R m k) ∧
        -- `K[0] = K_{0,0}` with the filtration `K_{m,m}`
        (∀ m : ℕ, (E.prod F).lvlSet (KB U R) m = KmkB U R m m) ∧
        -- `K[1] = K_{0,1}` with the filtration `K_{m,m+1}`
        (∀ m : ℕ, (E.prod F.shift).lvlSet (KoneB (KB U R)) m = KmkB U R m (m + 1)) ∧
        strongShiftOne (KB U R) = KoneB (KB U R) ∧
        (∀ i m : ℕ, i ≤ 1 → strongLevelShift (KB U R) i m = KmkB U R m (m + i)) ∧
        -- `p : K[0] → O` is sc-smooth
        IsScSmoothRetractMapB (E.prod F) (C ×ˢ Set.univ) (KB U R) E (baseB U R)
          (fun q : E.lvl 0 × F.lvl 0 => q.1) ∧
        -- `p : K[1] → O` is sc-smooth
        IsScSmoothRetractMapB (E.prod F.shift) (C ×ˢ Set.univ) (KoneB (KB U R)) E (baseB U R)
          (fun q : E.lvl 0 × F.lvl 1 => q.1)

end RoundTrip.V2_55
