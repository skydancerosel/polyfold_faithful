import Polyfold
/-! Blind formalization of V3_100 (the text's §3.6, after Theorem 3.54, p. 111; Corollary 3.24,
p. 79).  `B` is the conjunction of (a) and (b).  Choices:
- Setting (§3.6): `X Y : Type` (universe 0; nothing depends on the universe).  `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`,
  `Bd : StrongBundle PX P` a *tame* strong bundle (`IsTameStrongBundle`, defined here as in the
  earlier blind files: tame base and an *equivalent* strong bundle atlas of charts with tame base
  retraction — a property of the given structure, not "every compatible chart is tame"), `f` an
  sc-Fredholm section in the sense of §3.6 (`IsScFredholmSectionTame`, Definition 3.51), `x` a
  zero of `f` (`IsZeroAt`; good position, Definition 3.53, is defined at zeros).
- "`(f, x)` in good position" (Definition 3.53): `IsGoodPositionGermSc`, copied from my V3_94: germ
  data of Definition 3.11 in a tame strong bundle chart centred at `x` (filled version `g`,
  sc⁺-section `s` with `s(0) = g(0)`, conjugation of `g − s` to a basic germ), with (1)
  `Dg(0)|_{T₀O} : T₀O → K₀` onto and (2) *if `d_X(x) ≥ 1`* the kernel in good position to the
  partial cone `C₀O = T₀O ∩ C` inside `T₀O` (Definition 3.21 with the text's sc-complement,
  `IsInGoodPositionSc`).  The case distinction in (2) is the text's (as the project's docstring of
  `IsGoodPositionAt` reports it).
- (a) "`∂X = ∅`": `PX.boundary = ∅` (Definition 2.25).  "`f'(x)` surjective":
  `StrongBundle.IsLinSurjAt` (in some strong bundle chart around `x`, at the level-`1` point over
  `φ(x)`, `D(f̂ ∘ r)(z)|_{T_zO}` maps onto `K_z`; chart independent).  (a) is the equivalence of the
  two.
- (b) "the kernel condition is an empty condition if `d_X(x) = 0`" (Corollary 3.24): the kernel
  condition of Definition 3.53 (2), stated without the case distinction, holds automatically at a
  zero `x` with `d_X(x) = 0` (`PX.degIndex x = 0`): in every *tame* strong bundle chart `c` around
  `x` (`IsTameChart`; the partial cone `C_xX` is defined through tame charts), at the level-`1`
  lift `z₁` of `z = φ(x)`, and for every presentation `T : E ≅ ℝⁿ ⊕ W` of the chart's partial
  quadrant `C`, the kernel `ker D(f̂ ∘ r)(z) ∩ T_zO` is in good position (`IsInGoodPositionSc`) to
  the partial cone `T_zO ∩ C_z` inside `T_zO` (`C_z` the partial quadrant at `z`,
  `partialQuadrantAtWith`, Definition 2.33).  Universal over charts and presentations: the strong
  reading of a conclusion about an intrinsic object.  It relies on `d_C(φ(x)) = d_X(x)` in tame
  charts, which I believe the text proves.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_100
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

/-- The kernel condition at `x`, in the chart `c` (at the level-`1` lift `z₁` of `φ(x)`), for the
presentation `T` of the chart's partial quadrant: `ker f'(x) = ker D(f̂ ∘ r)(z) ∩ T_zO` is in good
position to the partial cone `T_zO ∩ C_z` inside `T_zO`. -/
def KernelCondInChart (c : StrongBundleChart PX P) (f : X → Y) (x : X)
    (z₁ : c.φ.model.E.lvl 1) {n : ℕ} {W : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)) : Prop :=
  IsInGoodPositionSc c.φ.model.E (rangeS (scDeriv c.U (StrongRetr.r c.R) z₁))
    ((rangeS (scDeriv c.U (StrongRetr.r c.R) z₁) : Set (c.φ.model.E.lvl 0)) ∩
      partialQuadrantAtWith T (c.φ.toPartialEquiv x))
    (LinearMap.ker (scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ :
        c.φ.model.E.lvl 0 →ₗ[ℝ] c.F.lvl 0) ⊓
      rangeS (scDeriv c.U (StrongRetr.r c.R) z₁))

end

/-- (a) For `∂X = ∅`, `(f, x)` is in good position iff `f'(x)` is surjective; (b) (Corollary 3.24)
if `d_X(x) = 0`, the kernel of `f'(x)` is automatically in good position to `C_xX`. -/
def B : Prop :=
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → PX.boundary = ∅ →
    IsZeroAt P f x →
      (IsGoodPositionGermSc Bd f x ↔ Bd.IsLinSurjAt f x)) ∧
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
    PX.degIndex x = 0 →
      ∀ c : StrongBundleChart PX P, Bd.IsTameChart c → x ∈ c.φ.source →
        ∀ z₁ : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv x →
          ∀ (n : ℕ) (W : ScBanach) (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
            c.φ.model.C = (T.lvl 0) ⁻¹' quadrant n W 0 →
              KernelCondInChart c f x z₁ T)

end RoundTrip.V3_100
