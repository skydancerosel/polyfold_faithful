import Polyfold
/-! Blind formalization of V3_47 (the text's §3.6, Definition 3.53, p. 111). Choices:
- This item is a definition.  Following the convention of the earlier blind definition files,
  `B` states that the project's notion is the text's one: for a section `f` of a tame strong
  bundle and a zero `x` of `f`, the project's `StrongBundle.IsGoodPositionGermTame` (docstring:
  "Definition 3.53 in a tame chart") is equivalent to `IsGoodPositionB` below.
- Setting: `X Y : Type` (universe 0; nothing depends on it), `PX : MPolyfold X`, `P : Y → X` with
  the fibrewise linear structure as instances, `Bd : StrongBundle PX P`.  "Tame strong bundle":
  `IsTameStrongBundle` (as in the earlier blind files: tame base and an equivalent atlas of charts
  with tame base retractions; a property of the given structure).  `f(x) = 0`: `IsZeroAt P f x`
  (a hypothesis: the definition is made for zeros).
- "An sc-Fredholm germ `(f, x)`" of a tame strong bundle: the project's
  `StrongBundle.IsScFredholmGermTame` (Definition 3.50; it is examined separately in my V3_45, so
  here I take it as given and test only the good-position clauses).
- `f'(x) : T_xX → Y_x`, `T_xX`, `C_xX` (the text uses them intrinsically; they are read in a
  strong bundle chart `c` of the bundle (`Bd.IsChart c`) whose local strong bundle is tame (tame
  base retraction `r`, which is what makes `T_xX`, `C_xX` well defined, Definition 2.38), centred
  at `x` (`φ(x) = 0`, `0 ∈ U`)): `T_xX` is `T₀O = Dr(0)E` (`tangent0`), `Y_x` is the fibre
  `K₀ = {k | (0, k) ∈ K}` of the chart, `C_xX` is the partial cone `C₀O = T₀O ∩ C₀ = T₀O ∩ C`
  (at the vertex `0` the partial quadrant `C₀` of Definition 2.33 is `C`), and `f'(x)` is the
  linearization at `0` of `f̂ ∘ r` (`f̂` the principal part), restricted to `T₀O`: `D(0)|_{T₀O}` for
  a derivative family `D` of `f̂ ∘ r` as an sc¹-germ at `0` (unique at the smooth point `0`).
  Since these objects are chart-independent (Proposition 2.30), I read the definition with one
  such chart (existential).
- (1) "`f'(x)` surjective": every `k ∈ K₀` is `D(0)v` for some `v ∈ T₀O`.
  (2) "if `d_X(x) ≥ 1`" (`PX.degIndex x`): `ker f'(x) = ker D(0) ∩ T₀O` is in good position to
  `C₀O` in `T₀O` (Definition 3.21 inside the sc-subspace `T₀O`, `IsInGoodPositionSc` as in my
  earlier blind file V3_94: `ker f'(x) ∩ C` has nonempty interior in `ker f'(x)`, and there is an
  *sc-complement* `P ⊆ T₀O` of it in `T₀O` (level-wise `T_m = N_m ⊕ P_m`, `P` an sc-subspace) with
  `n ∈ C ⟺ n + p ∈ C` for `|p|₀ ≤ ε|n|₀`).
- Nothing in the text looks false to me.
-/
namespace RoundTrip.V3_47
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

/-- The tangent space `T₀O = Dr(0)E` of the chart's retract at `0`. -/
noncomputable def tangent0 (c : StrongBundleChart PX P) : Submodule ℝ (c.φ.model.E.lvl 0) :=
  LinearMap.range
    (scDeriv c.U (StrongRetr.r c.R) 0 : c.φ.model.E.lvl 0 →ₗ[ℝ] c.φ.model.E.lvl 0)

/-- **Definition 3.53**: the sc-Fredholm germ `(f, x)` (at a zero `x`) is in good position: in a
strong bundle chart centred at `x` with tame local bundle, (1) the linearization
`f'(x) = D(f̂ ∘ r)(0)|_{T₀O} : T₀O → K₀` is onto, and (2) if `d_X(x) ≥ 1`, its kernel is in good
position to the partial cone `C₀O = T₀O ∩ C` in `T₀O`. -/
def IsGoodPositionB (Bd : StrongBundle PX P) (f : X → Y) (x : X) : Prop :=
  Bd.IsScFredholmGermTame f x ∧
    ∃ c : StrongBundleChart PX P, Bd.IsChart c ∧
      (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame ∧
      x ∈ c.φ.source ∧ c.φ.toPartialEquiv x = 0 ∧ 0 ∈ c.U ∧
      ∃ (G : ScNbhdGerm c.φ.model.E c.φ.model.C)
        (D : c.φ.model.E.lvl 1 → c.φ.model.E.lvl 0 →L[ℝ] c.F.lvl 0),
        G.U 0 ⊆ c.U ∧ IsSc1GermWith G (c.principal f ∘ StrongRetr.r c.R) D ∧
        -- (1) `f'(x) : T_xX → Y_x` is surjective
        (∀ k : c.F.lvl 0, ((0 : c.φ.model.E.lvl 0), k) ∈ c.K →
          ∃ v ∈ tangent0 c, D 0 v = k) ∧
        -- (2) if `d_X(x) ≥ 1`, `ker f'(x)` is in good position to `C_xX` in `T_xX`
        (1 ≤ PX.degIndex x →
          IsInGoodPositionSc c.φ.model.E (tangent0 c)
            ((tangent0 c : Set (c.φ.model.E.lvl 0)) ∩ c.φ.model.C)
            (LinearMap.ker (D 0 : c.φ.model.E.lvl 0 →ₗ[ℝ] c.F.lvl 0) ⊓ tangent0 c))

end

/-- Definition 3.53: for a zero `x` of a section `f` of a tame strong bundle, the project's
`IsGoodPositionGermTame` is the text's notion "the sc-Fredholm germ `(f, x)` is in good
position". -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → IsZeroAt P f x →
      (Bd.IsGoodPositionGermTame f x ↔ IsGoodPositionB Bd f x)

end RoundTrip.V3_47
