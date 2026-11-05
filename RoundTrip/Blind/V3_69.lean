import Polyfold
/-! Blind formalization of V3_69 (the text's §3.1, Theorem 3.23, p. 77). Choices:
- Setting: `X Y : Type` (universe 0; nothing depends on the universe).  `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`, and
  `Bd : StrongBundle PX P` (Definition 2.51).
- "tame strong bundle": `IsTameStrongBundle` (defined here, as in the earlier blind files): tame
  base (`MPolyfold.IsTame`) and an *equivalent* strong bundle atlas all of whose charts have a tame
  base retraction (`ScRetraction.IsTame`).  A property of the given structure, not "every chart
  is tame".
- "sc-Fredholm section of a tame strong bundle": `IsScFredholmSectionTame` (Definition 3.14 with
  the germ data of Definition 3.11 in a tame strong bundle chart, as the text recalls it for tame
  strong bundles, Definitions 3.50/3.51).  For a tame bundle I read "strong bundle chart" as a
  chart of the tame structure; the variant `IsScFredholmSection` (any compatible chart) would be
  a weaker hypothesis.
- `f(x) = 0`: `IsZeroAt P f x`.
- "`f'(x)` surjective with kernel in good position to `C_xX`" (`IsSurjGoodPosAt`, defined here as
  in the earlier blind files), in *some* tame strong bundle chart around `x` (a hypothesis, so
  the existential is the weakest, intrinsic reading): with `z = φ(x)` lifted to `z₁ ∈ E₁`,
  `T_zO = range Dr(z)` and `L = D(f̂ ∘ r)(z)`: `L` maps `T_zO` onto `K_z = {k | (z, k) ∈ K}`, and
  `ker L ∩ T_zO` is in good position (Definition 3.21 inside `T_zO`, with the text's sc-complement,
  `IsInGoodPositionSc`) to the partial cone `C_zO = T_zO ∩ C_z` (Definition 2.27, `C_z` the
  partial quadrant at `z` for a presentation of `C`).  The project's `IsInGoodPositionIn`
  (algebraic complement only, by its docstring) was not used.
- `S(f, U) = {y ∈ U | f(y) = 0}`; "there is an open `U ∋ x`": an open set of `X` containing `x`.
- Conclusion: `S(f, U) ⊆ X_∞` ("consists of smooth points", `smoothSet`); a sub-M-polyfold
  (Definition 2.20; `S(f, U)` paracompact, an instance argument of `subPolyfold`, asserted as part
  of the claim, it is true); "tame sub-M-polyfold": the induced structure (Proposition 2.21,
  `subPolyfold`) is tame (`MPolyfold.IsTame`), the reading of "tame" for a sub-M-polyfold that
  the project's Definition 4.17 docstring also uses; "a smooth manifold with boundary with
  corners, the induced one of Proposition 2.21": the induced structure has an equivalent atlas of
  corner charts (`HasCornerStructure`, Definition 4.1); "uniquely determined": any two corner
  atlases equivalent to the induced structure are equivalent to each other
  (`CornerStructureUnique`, defined here).  This is my reading of "uniquely determined" (the
  manifold structure is determined by the induced M-polyfold structure); it is a weak addition.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_69
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

/-- The compatible manifold-with-corners structure of `QZ` is unique: any two atlases of corner
charts equivalent to the atlas of `QZ` are equivalent to each other. -/
def CornerStructureUnique {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (QZ : MPolyfold Z) : Prop :=
  ∀ A₁ A₂ : MAtlas Z, A₁.Equiv QZ.atlas → A₂.Equiv QZ.atlas →
    (∀ χ ∈ A₁.charts, χ.IsCornerChart) → (∀ χ ∈ A₂.charts, χ.IsCornerChart) → A₁.Equiv A₂

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A **tame strong bundle**: tame base, and an equivalent strong bundle atlas of charts whose base
retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

/-- `f'(x)` is surjective and its kernel is in good position to the partial cone `C_xX`, read in a
tame strong bundle chart around `x`. -/
def IsSurjGoodPosAt (Bd : StrongBundle PX P) (f : X → Y) (x : X) : Prop :=
  ∃ c : StrongBundleChart PX P, Bd.IsTameChart c ∧ x ∈ c.φ.source ∧
  ∃ z₁ : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv x ∧
    (∀ k : c.F.lvl 0, (c.φ.toPartialEquiv x, k) ∈ c.K →
      ∃ v ∈ rangeS (scDeriv c.U (StrongRetr.r c.R) z₁),
        scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ v = k) ∧
    ∃ (n : ℕ) (W : ScBanach) (Tp : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
      c.φ.model.C = (Tp.lvl 0) ⁻¹' quadrant n W 0 ∧
      IsInGoodPositionSc c.φ.model.E (rangeS (scDeriv c.U (StrongRetr.r c.R) z₁))
        ((rangeS (scDeriv c.U (StrongRetr.r c.R) z₁) : Set (c.φ.model.E.lvl 0)) ∩
          partialQuadrantAtWith Tp (c.φ.toPartialEquiv x))
        (LinearMap.ker
            (scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ :
              c.φ.model.E.lvl 0 →ₗ[ℝ] c.F.lvl 0) ⊓
          rangeS (scDeriv c.U (StrongRetr.r c.R) z₁))

end

/-- Theorem 3.23 (implicit function theorem, boundary case): near a zero `x` at which `f'(x)` is
onto with kernel in good position to `C_xX`, `S(f, U)` consists of smooth points and is a tame
sub-M-polyfold whose induced structure is a (uniquely determined) smooth manifold with boundary
with corners. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
    IsSurjGoodPosAt Bd f x →
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        {y | y ∈ U ∧ IsZeroAt P f y} ⊆ PX.smoothSet ∧
        ∃ (hS : PX.IsSubMPolyfold {y | y ∈ U ∧ IsZeroAt P f y})
          (_ : ParacompactSpace {y | y ∈ U ∧ IsZeroAt P f y}),
          (PX.subPolyfold hS).IsTame ∧ (PX.subPolyfold hS).HasCornerStructure ∧
          CornerStructureUnique (PX.subPolyfold hS)

end RoundTrip.V3_69
