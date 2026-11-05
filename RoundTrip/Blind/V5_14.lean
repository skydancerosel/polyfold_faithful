import Polyfold
/-! Blind formalization of V5_14 (the text's §5.2, proof of Corollary 5.8, p. 173).

Text: "It is a priori clear that `f^i` is sc-Fredholm" (`f` an sc-Fredholm section of the strong
bundle `P : Y → X`, `f^i = f|X_i` the induced section of `P^i : Y^i → X^i`, `i ≥ 0`).

Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`; `f` an
  sc-Fredholm section, the project's `Bd.IsScFredholmSection f` (Definition 3.14, checked with
  `#print`: sc-smooth section, regularizing, an sc-Fredholm germ at every smooth point, the germ
  data in some compatible strong bundle chart centred at the point).
- Hypotheses: Corollary 5.8 assumes `X` tame and `f⁻¹(0)` compact, but those are used only for
  the compactness half (via Theorem 5.7); "a priori" says that `f^i` being sc-Fredholm needs
  neither.  So B assumes only that `f` is sc-Fredholm (no tameness, no compactness) — the
  sentence's own generality.  The claim is made for every `i ∈ ℕ`.
- `X^i`, `P^i : Y^i → X^i`, "`f^i` is an sc-Fredholm section of `P^i`": the project has no shifted
  strong bundle `P^i`, so I use the prelude of `RoundTrip/Blind/V5_13.lean` (same corollary)
  verbatim: `IsScFredholmSectionLvl Bd i f` unfolds Definition 3.14 for `P^i` in the level-`i`
  restrictions `Φ^i` of the strong bundle charts `Φ` of `Bd` (base model `E^i`, `(E^i)_m =
  E_{i+m}`, fibre model `F^i`, `C^i, O^i, U^i` the preimages under `E_i → E_0`,
  `K^i = K ∩ (E_i ⊕ F_i)`, `R^i = R` on `U_i ⊕ F_i`, principal part `f̂^i(z) = f̂(z)` lifted to
  `F_i`; lifts are `Function.invFun` of the injective inclusions, junk only off their ranges):
  * `f^i` is a section of `Y^i` (`f` a section with `f(X_i) ⊆ Y_{i,i}`);
  * (1) sc-smooth: in every chart `Φ^i`, `Φ` in the atlas of `Bd`, `z ↦ (z, f̂^i(z))` is an
    sc-smooth section of `K^i → O^i` (project's chart-level `IsScSmoothSection`, Definition 2.49);
  * (2) regularizing: `x ∈ X_{i+m}` and `f(x) ∈ Y_{i+m,i+m+1}` imply `x ∈ X_{i+m+1}`;
  * (3) at every smooth point an sc-Fredholm germ (Definition 3.11) in the level-`i` restriction
    `Φ^i` of a compatible strong bundle chart `Φ` centred at the point (project's
    `IsFilledVersion`, `IsConjugateToBasicGerm` applied to the shifted data).  Requiring the chart
    to be some `Φ^i` (rather than any chart of `P^i`) makes this clause slightly STRONGER than
    Definition 3.14 for `P^i`; it is the "level shift of the germ data" that makes the claim
    "a priori clear".
- Nothing looks false to me.
-/
namespace RoundTrip.V5_14
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The base model `E^i` of the level-`i` restriction of a strong bundle chart. -/
abbrev Ei (c : StrongBundleChart PX P) (i : ℕ) : ScBanach := c.φ.model.E.shiftAdd i

/-- The fibre model `F^i` of the level-`i` restriction of a strong bundle chart. -/
abbrev Fi (c : StrongBundleChart PX P) (i : ℕ) : ScBanach := c.F.shiftAdd i

/-- The inclusion `(E^i)_0 = E_i → E_0`. -/
def ιE (c : StrongBundleChart PX P) (i : ℕ) : (Ei c i).lvl 0 → c.φ.model.E.lvl 0 :=
  fun z => c.φ.model.E.toBase i z

/-- The inclusion `(F^i)_0 = F_i → F_0`. -/
def ιF (c : StrongBundleChart PX P) (i : ℕ) : (Fi c i).lvl 0 → c.F.lvl 0 :=
  fun h => c.F.toBase i h

/-- Lift `E_0 → E_i` (a left inverse of the inclusion; junk off its range). -/
noncomputable def liftE (c : StrongBundleChart PX P) (i : ℕ) :
    c.φ.model.E.lvl 0 → (Ei c i).lvl 0 :=
  Function.invFun (ιE c i)

/-- Lift `F_0 → F_i` (a left inverse of the inclusion; junk off its range). -/
noncomputable def liftF (c : StrongBundleChart PX P) (i : ℕ) : c.F.lvl 0 → (Fi c i).lvl 0 :=
  Function.invFun (ιF c i)

/-- `C^i = C ∩ E_i`. -/
def Ci (c : StrongBundleChart PX P) (i : ℕ) : Set ((Ei c i).lvl 0) :=
  ιE c i ⁻¹' c.φ.model.C

/-- `O^i = O_i`. -/
def Oi (c : StrongBundleChart PX P) (i : ℕ) : Set ((Ei c i).lvl 0) :=
  ιE c i ⁻¹' c.φ.model.O

/-- `U^i = U_i`. -/
def Ui (c : StrongBundleChart PX P) (i : ℕ) : Set ((Ei c i).lvl 0) :=
  ιE c i ⁻¹' c.U

/-- `K^i = K_{i,i}`, as a subset of `E_i × F_i`. -/
def Ki (c : StrongBundleChart PX P) (i : ℕ) : Set ((Ei c i).lvl 0 × (Fi c i).lvl 0) :=
  {p | (ιE c i p.1, ιF c i p.2) ∈ c.K}

/-- The strong bundle retraction `R^i = R|(U_i ⊕ F_i)`. -/
noncomputable def Ri (c : StrongBundleChart PX P) (i : ℕ) :
    (Ei c i).lvl 0 × (Fi c i).lvl 0 → (Ei c i).lvl 0 × (Fi c i).lvl 0 :=
  fun p => (liftE c i (c.R (ιE c i p.1, ιF c i p.2)).1,
    liftF c i (c.R (ιE c i p.1, ιF c i p.2)).2)

/-- The principal part `f̂^i : O_i → F_i` of `f^i` in the chart `Φ^i`. -/
noncomputable def principalLvl (c : StrongBundleChart PX P) (i : ℕ) (f : X → Y) :
    (Ei c i).lvl 0 → (Fi c i).lvl 0 :=
  fun z => liftF c i (c.principal f (ιE c i z))

/-- Definition 3.11 for `P^i`: `(f^i, x₀)` is an sc-Fredholm germ, in the level-`i` restriction
`Φ^i` of a strong bundle chart `Φ` of `P` centred at `x₀`. -/
def IsScFredholmGermLvl (Bd : StrongBundle PX P) (i : ℕ) (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
    ∃ c : StrongBundleChart PX P, Bd.IsChart c ∧ x₀ ∈ c.φ.source ∧
      c.φ.toPartialEquiv x₀ = 0 ∧
      ∃ (h0 : (0 : (Ei c i).lvl 0) ∈ Ui c i)
        (hU : IsRelOpenInQuadrant (Ei c i) (Ci c i) (Ui c i))
        (hR : IsStrongBundleRetraction (Ui c i) (Ri c i)),
        ∃ (g : (Ei c i).lvl 0 → (Fi c i).lvl 0) (s : (Ei c i).lvl 0 → (Fi c i).shift.lvl 0),
          IsFilledVersion hU hR h0 (principalLvl c i f) g ∧
          IsScSmooth (Ui c i) s ∧
          (Fi c i).toBase 1 (s 0) = g 0 ∧
          IsConjugateToBasicGerm (Ui c i) (fun u => g u - (Fi c i).toBase 1 (s u))

/-- Definition 3.14 for `P^i : Y^i → X^i`: `f^i = f|X_i` is an sc-Fredholm section. -/
def IsScFredholmSectionLvl (Bd : StrongBundle PX P) (i : ℕ) (f : X → Y) : Prop :=
  -- `f^i` is a section of `P^i : Y^i → X^i`
  (IsSection P f ∧ ∀ x ∈ PX.levelSet i, f x ∈ Bd.doubleLevel i i) ∧
  -- (1) sc-smooth, in the charts `Φ^i`
  (∀ c ∈ Bd.atlas.charts,
    IsScSmoothSection (Ci c i) (Oi c i) (Ki c i) (fun z => (z, principalLvl c i f z))) ∧
  -- (2) regularizing
  (∀ m : ℕ, ∀ x ∈ PX.levelSet (i + m),
    f x ∈ Bd.doubleLevel (i + m) (i + m + 1) → x ∈ PX.levelSet (i + m + 1)) ∧
  -- (3) sc-Fredholm germs at the smooth points
  (∀ x ∈ PX.smoothSet, IsScFredholmGermLvl Bd i f x)

end

/-- Corollary 5.8, the a priori part: for an sc-Fredholm section `f` and every `i`, the restriction
`f^i` is an sc-Fredholm section of `P^i : Y^i → X^i` (germ data shifted to level `i`). -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y),
    Bd.IsScFredholmSection f → ∀ i : ℕ, IsScFredholmSectionLvl Bd i f

end RoundTrip.V5_14
