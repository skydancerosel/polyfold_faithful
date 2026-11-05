import Polyfold
/-! Blind formalization of V3_82 (the text's §3.6, Theorem 3.54 (1), p. 111; proof p. 114).
Choices:
- Setting (Theorem 3.54): `X Y : Type` (universe 0; nothing depends on the universe).
  `PX : MPolyfold X`, `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`,
  `Bd : StrongBundle PX P` (Definition 2.51); hypotheses of Theorem 3.54: `Bd` tame, `f` an
  sc-Fredholm section, `f(x) = 0`, `(f, x)` in good position.  The quote ("at every zero `y` near
  `x`") presupposes this setting of Theorem 3.54 (1); I added exactly these hypotheses.
- "tame strong bundle": `IsTameStrongBundle` (defined here, as in the earlier blind files): tame
  base (`MPolyfold.IsTame`) and an *equivalent* strong bundle atlas all of whose charts have a tame
  base retraction (`ScRetraction.IsTame`).  A property of the given structure, not "every chart
  is tame".
- "sc-Fredholm section" (§3.6, tame bundle): `IsScFredholmSectionTame` (Definition 3.51).
  `f(x) = 0`: `IsZeroAt P f x`.
- "the sc-Fredholm germ `(f, y)` is in good position" (Definition 3.53): `IsGoodPositionGermSc`,
  defined here exactly as in my earlier blind files V3_94/V3_85: the data of Definition 3.11 in a
  *tame* strong bundle chart `c` centred at `y` (filled version `g` of `f̂`, sc⁺-section `s` with
  `s(0) = g(0)`, a conjugation of `g − s` to a basic germ) such that `f'(y) = Dg(0)|_{T₀O}` maps
  `T₀O` onto `K₀` ("`f'(y)` is surjective") and, if `d_X(y) ≥ 1`, its kernel `ker Dg(0) ∩ T₀O` is
  in good position (Definition 3.21 with the text's sc-complement, `IsInGoodPositionSc`) to the
  partial cone `C₀O = T₀O ∩ C` inside `T₀O` ("its kernel is in good position").  The case
  distinction `d_X(y) ≥ 1` is Definition 3.53's; at an interior point the kernel condition holds
  anyway.  The same notion is used for the hypothesis at `x`.
- "at every zero `y` near `x`": there is an open `V ∋ x` such that the claim holds at every
  `y ∈ V` with `f(y) = 0` (`zeroSetIn`).
- The item's title speaks of "the filler condition at the nearby zeros"; the quoted statement
  contains no such condition (it is not one of the text's hypotheses), so I did not add it.  If the
  text's claim needs it, `B` as stated may be false; I formalized the quote literally.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_82
open Polyfold

/-- Definition 3.21 inside the subspace `T`, with an sc-complement: `N ⊆ T`, `N ∩ C` has nonempty
interior in `N`, and `N` has an sc-complement `P` in `T` (`T_m = N_m ⊕ P_m` on every level) such
that `n ∈ C ⟺ n + p ∈ C` for `n ∈ N`, `p ∈ P`, `|p|₀ ≤ ε|n|₀`. -/
def IsInGoodPositionSc (E : ScBanach) (T : Submodule ℝ (E.lvl 0)) (C : Set (E.lvl 0))
    (N : Submodule ℝ (E.lvl 0)) : Prop :=
  N ≤ T ∧ (interior (Subtype.val ⁻¹' C : Set N)).Nonempty ∧
    ∃ Pc : Submodule ℝ (E.lvl 0), Pc ≤ T ∧ E.IsScSubspace Pc ∧
      (∀ m, E.levelSub N m ⊓ E.levelSub Pc m = ⊥ ∧
        E.levelSub N m ⊔ E.levelSub Pc m = E.levelSub T m) ∧
      ∃ ε > 0, ∀ n ∈ N, ∀ p ∈ Pc, ‖p‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + p ∈ C)

/-- `S(f, V) = {y ∈ V | f(y) = 0}`. -/
def zeroSetIn {X Y : Type} (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (f : X → Y)
    (V : Set X) : Set X :=
  {y | y ∈ V ∧ IsZeroAt P f y}

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A **tame strong bundle**: tame base, and an equivalent strong bundle atlas of charts whose base
retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

/-- The data of Definition 3.53 at `x` except the conjugation: a tame strong bundle chart `c`
centred at `x`, a filled version `g` of the principal part, an sc⁺-section `s` (values in `F₁`)
with `s(0) = g(0)`, such that `Dg(0)|_{T₀O}` maps onto `K₀` and, if `d_X(x) ≥ 1`, its kernel is in
good position to the partial cone `C₀O = T₀O ∩ C` inside `T₀O`. -/
def IsGoodPosData (Bd : StrongBundle PX P) (f : X → Y) (x : X) (c : StrongBundleChart PX P)
    (h0 : 0 ∈ c.U) (g : c.φ.model.E.lvl 0 → c.F.lvl 0)
    (s : c.φ.model.E.lvl 0 → c.F.shift.lvl 0) : Prop :=
  Bd.IsTameChart c ∧ x ∈ c.φ.source ∧ c.φ.toPartialEquiv x = 0 ∧
    IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g ∧
    @IsScSmooth _ c.F.shift c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    (∀ k : c.F.lvl 0, ((0 : c.φ.model.E.lvl 0), k) ∈ c.K →
      ∃ v ∈ rangeS (scDeriv c.U (StrongRetr.r c.R) 0), scDeriv c.U g 0 v = k) ∧
    (1 ≤ PX.degIndex x →
      IsInGoodPositionSc c.φ.model.E (rangeS (scDeriv c.U (StrongRetr.r c.R) 0))
        ((rangeS (scDeriv c.U (StrongRetr.r c.R) 0) : Set (c.φ.model.E.lvl 0)) ∩ c.φ.model.C)
        (LinearMap.ker (scDeriv c.U g 0 : c.φ.model.E.lvl 0 →ₗ[ℝ] c.F.lvl 0) ⊓
          rangeS (scDeriv c.U (StrongRetr.r c.R) 0)))

/-- Definition 3.53: `(f, x)` is an sc-Fredholm germ in good position (germ data of Definition 3.11
in a tame chart, including the conjugation of `g − s` to a basic germ, with the conditions of
`IsGoodPosData`). -/
def IsGoodPositionGermSc (Bd : StrongBundle PX P) (f : X → Y) (x : X) : Prop :=
  ∃ (c : StrongBundleChart PX P) (h0 : 0 ∈ c.U) (g : c.φ.model.E.lvl 0 → c.F.lvl 0)
    (s : c.φ.model.E.lvl 0 → c.F.shift.lvl 0),
    IsGoodPosData Bd f x c h0 g s ∧
      Nonempty (ConjugationData c.U (fun u => g u - c.F.toBase 1 (s u)))

end

/-- Theorem 3.54 (1): near a zero `x` with `(f, x)` in good position, there is an open `V ∋ x`
such that the sc-Fredholm germ `(f, y)` is in good position (`f'(y)` onto, kernel in good position)
at every zero `y ∈ V`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
    IsGoodPositionGermSc Bd f x →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ zeroSetIn P f V, IsGoodPositionGermSc Bd f y

end RoundTrip.V3_82
