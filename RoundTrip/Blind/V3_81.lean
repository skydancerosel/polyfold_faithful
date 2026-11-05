import Polyfold
/-! Blind formalization of V3_81 (the text's §3.6, Theorem 3.54 (1), the kernel, pp. 111, 114).
Choices:
- Setting (Theorem 3.54): `X Y : Type` (universe 0; nothing depends on the universe).
  `PX : MPolyfold X`, `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`,
  `Bd : StrongBundle PX P` (Definition 2.51); hypotheses of Theorem 3.54: `Bd` tame, `f` an
  sc-Fredholm section, `f(x) = 0`, `(f, x)` in good position.  The quote ("at every zero `y` near
  `x`") presupposes this setting; I added exactly these hypotheses.
- "tame strong bundle": `IsTameStrongBundle` (defined here, as in the earlier blind files): tame
  base (`MPolyfold.IsTame`) and an *equivalent* strong bundle atlas all of whose charts have a tame
  base retraction (`ScRetraction.IsTame`).  A property of the given structure, not "every chart
  is tame".
- "sc-Fredholm section" (§3.6, tame bundle): `IsScFredholmSectionTame` (Definition 3.51).
  `f(x) = 0`: `IsZeroAt P f x`.  "`(f, x)` in good position" (Definition 3.53): the hypothesis
  `IsGoodPositionGermSc`, defined here exactly as in my earlier blind files V3_94/V3_82 (germ data
  of Definition 3.11 in a tame chart centred at `x`, `f'(x)` onto, and if `d_X(x) ≥ 1` its kernel
  in good position to `C_xX`; Definition 3.21 with the text's sc-complement).
- "at every zero `y` near `x`": there is an open `V ∋ x` such that the claim holds at every
  `y ∈ V` with `f(y) = 0` (`zeroSetIn`).
- "`ker f'(y)` is in good position to the partial cone `C_yX`" (`KerGoodPosInChart`, defined
  here): `T_yX`, `C_yX`, `f'(y)` are intrinsic objects which the project does not provide, so they
  are read in a *tame* strong bundle chart `c` around `y` (`StrongBundle.IsTameChart`; the partial
  cone is defined through tame charts, Definitions 2.27/2.38): with `z = φ(y)` lifted to
  `z₁ ∈ E₁` (zeros are smooth points), `T_zO = range Dr(z₁)`, `f'(y) = D(f̂ ∘ r)(z₁)|_{T_zO}`
  (`f̂` the principal part), `ker f'(y) = ker D(f̂ ∘ r)(z₁) ∩ T_zO`, and `C_zO = T_zO ∩ C_z`, `C_z`
  the partial quadrant at `z` (Definition 2.33, `partialQuadrantAtWith`) for a presentation
  `T : E ≅ ℝⁿ ⊕ W` of `C`.  Good position is Definition 3.21 inside `T_zO` with the text's
  sc-complement (`IsInGoodPositionSc`).  Since this is a conclusion about intrinsic objects, it is
  stated in *every* tame strong bundle chart around `y` and for *every* presentation of `C` (the
  strong reading; `C_z` does not depend on the presentation, and good position is carried by the
  tangent maps of the transitions).
- The quote has no case distinction `d_X(y) ≥ 1` (unlike Definition 3.53), so none is made; at an
  interior point `C_z = E` and the condition is the existence of an sc-complement of the
  finite-dimensional smooth kernel in `T_zO`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_81
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

/-- In the tame strong bundle chart `c` around `y`: with `z = φ(y)` lifted to `z₁ ∈ E₁`, for
every presentation `T` of the partial quadrant `C`, the kernel `ker D(f̂ ∘ r)(z₁) ∩ T_zO` of
`f'(y)` is in good position to the partial cone `C_zO = T_zO ∩ C_z` inside `T_zO`. -/
def KerGoodPosInChart (c : StrongBundleChart PX P) (f : X → Y) (y : X) : Prop :=
  ∃ z₁ : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv y ∧
    ∀ (n : ℕ) (W : ScBanach) (Tp : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
      c.φ.model.C = (Tp.lvl 0) ⁻¹' quadrant n W 0 →
      IsInGoodPositionSc c.φ.model.E (rangeS (scDeriv c.U (StrongRetr.r c.R) z₁))
        ((rangeS (scDeriv c.U (StrongRetr.r c.R) z₁) : Set (c.φ.model.E.lvl 0)) ∩
          partialQuadrantAtWith Tp (c.φ.toPartialEquiv y))
        (LinearMap.ker
            (scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ :
              c.φ.model.E.lvl 0 →ₗ[ℝ] c.F.lvl 0) ⊓
          rangeS (scDeriv c.U (StrongRetr.r c.R) z₁))

end

/-- Theorem 3.54 (1), the kernel: near a zero `x` with `(f, x)` in good position, there is an open
`V ∋ x` such that at every zero `y ∈ V` the kernel of `f'(y)` is in good position to the partial
cone `C_yX` (in every tame strong bundle chart around `y`). -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
    IsGoodPositionGermSc Bd f x →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ zeroSetIn P f V, ∀ c : StrongBundleChart PX P, Bd.IsTameChart c →
          y ∈ c.φ.source → KerGoodPosInChart c f y

end RoundTrip.V3_81
