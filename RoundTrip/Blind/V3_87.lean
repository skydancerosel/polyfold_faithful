import Polyfold
/-! Blind formalization of V3_87 (the text's §3.6, Theorem 3.57, p. 115). Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the fibrewise
  linear structure as instances on `P ⁻¹' {x}`, `Bd : StrongBundle PX P`.
- "tame strong bundle": `IsTameStrongBundle` (defined here): tame base (`MPolyfold.IsTame`) and an
  equivalent strong bundle atlas all of whose charts have a tame base retraction
  (`ScRetraction.IsTame`).  A property of the given structure, not "every chart is tame".
- "`f` an sc-Fredholm section": `StrongBundle.IsScFredholmSectionTame` (Definition 3.51, the §3.6
  recall of Definition 3.14 for a tame strong bundle: germ data of Definition 3.11 in a tame strong
  bundle chart, Definition 3.50).
- `S = {f = 0}`: `solutionSet P f`.
- "at every `x ∈ S` the linearization is surjective with kernel in good position to `C_xX`"
  (`IsSurjGoodPosAt`, defined here), stated in *some* tame strong bundle chart `c` around `x`
  (`StrongBundle.IsTameChart`; the partial cone `C_xX` is defined through tame charts, and an
  existential is what the text's intrinsic condition gives): with `z = φ(x)` lifted to `z₁ ∈ E₁`,
  `r` the base retraction, `T_zO = range Dr(z)`, `L = D(f̂ ∘ r)(z)` (`f̂` the principal part):
  (i) `L` maps `T_zO` onto the fibre `K_z = {k | (z, k) ∈ K}`;
  (ii) `ker L ∩ T_zO` is in good position (Definition 3.21, inside `T_zO`) to the partial cone
  `C_zO = T_zO ∩ C_z` (Definition 2.27), `C_z` the partial quadrant at `z`
  (`partialQuadrantAtWith`, for some presentation of `C`).
- Good position (Definition 3.21, `IsInGoodPositionSc`, defined here with the text's
  *sc-complement*): `N ⊆ T`, `N ∩ C` has nonempty interior in `N`, and there is an sc-subspace
  `P ⊆ T` with `T_m = N_m ⊕ P_m` on every level and `ε > 0` such that `n ∈ C ⟺ n + p ∈ C` whenever
  `|p|₀ ≤ ε|n|₀`.  (The project's `IsInGoodPositionIn` only asks for an algebraic complement; I did
  not use it, the text's definition asks for an sc-complement.)
- Conclusion: `S` is a sub-M-polyfold (`IsSubMPolyfold`, Definition 2.20), `S` is paracompact
  (needed to form the induced structure `subPolyfold`, asserted as part of the claim), the
  induced structure is tame (`MPolyfold.IsTame`) and equivalent to a manifold with boundary with
  corners (`MPolyfold.HasCornerStructure`, Definition 4.1).
- Nothing in the statement looks false to me.  (V3_70, Corollary 3.24, is the same claim; I
  formalized both the same way.)
-/
namespace RoundTrip.V3_87
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

/-- Theorem 3.57 (global implicit function theorem, boundary case): if at every zero of the
sc-Fredholm section `f` of a tame strong bundle the linearization is onto with kernel in good
position to `C_xX`, then `S = {f = 0}` is a sub-M-polyfold
whose induced structure is tame and that of a smooth manifold with boundary with corners. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f →
    (∀ x ∈ solutionSet P f, IsSurjGoodPosAt Bd f x) →
      ∃ (hS : PX.IsSubMPolyfold (solutionSet P f)) (_ : ParacompactSpace (solutionSet P f)),
        (PX.subPolyfold hS).IsTame ∧ (PX.subPolyfold hS).HasCornerStructure

end RoundTrip.V3_87
