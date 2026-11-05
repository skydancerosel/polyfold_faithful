import Polyfold
/-! Blind formalization of V3_96 (the text's §3.6, Proposition 3.52, p. 110, and §3.1, Theorem
3.19, p. 74). Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the fibrewise
  linear structure as instances on `P ⁻¹' {x}`, `Bd : StrongBundle PX P` (Definition 2.51).
- The quote's hypotheses: "`f` an sc-Fredholm section, `f(x) = 0`".  "sc-Fredholm section" is
  Definition 3.14, which the text states for a *tame* strong bundle (and recalls as Definition 3.51
  in §3.6), so the bundle is assumed tame (`IsTameStrongBundle`, defined here as in the earlier
  blind files: tame base and an *equivalent* strong bundle atlas of charts with tame base
  retractions; a property of the given structure).  I used the project's
  `StrongBundle.IsScFredholmSection` (Definition 3.14).  By its docstring the project's §3.6 notion
  `IsScFredholmSectionTame` (Definition 3.51) is `IsScFredholmSection` plus tame germ data, so this
  one statement covers both quoted sources (Proposition 3.52 for Definition 3.51, Theorem 3.19 for
  Definition 3.14).  Theorem 3.19's further hypotheses (`d_X ≡ 0`, see the blind file V3_68) are
  not part of the quoted claim and are not assumed.  `f(x) = 0`: `IsZeroAt P f x`.
- "`Tf(x) : T_xX → Y_x` (`f'(x₀)`) is an sc-Fredholm operator": the project has no intrinsic
  linear structure on `T_xX`, `Y_x`, so the operator is represented in a strong bundle chart `c`
  around `x` (any chart compatible with the bundle structure, `StrongBundle.IsChart`):
  `ChartLinScFredholm`, copied from my earlier blind file V3_46: with `z = φ(x)` lifted to
  `z₁ ∈ E₁`, `T_zO = range Dr(z₁)` and the fibre `K_z = {h | (z, h) ∈ K}` are sc-subspaces (induced
  sc-structures `ScBanach.ofSubspace`), `D(f̂ ∘ r)(z₁)` (`f̂` the principal part) maps `T_zO` into
  `K_z`, is an sc-operator there (`IsScOperator`) and is sc-Fredholm (Definition 1.8,
  `IsScFredholm`) of some index.  Since `Tf(x)` is intrinsic, this is claimed in *every* chart
  around `x` (the strong reading); the index is not part of the quoted claim, so it is only
  asserted to exist (in each chart).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_96
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A **tame strong bundle**: tame base, and an equivalent strong bundle atlas of charts whose base
retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

/-- In the strong bundle chart `c` around `x`, with `z = φ(x)` (lifted to `z₁ ∈ E₁`), the
linearization `D(f̂ ∘ r)(z)|_{T_zO} : T_zO → K_z` is an sc-Fredholm operator of index `i` between
the sc-subspaces `T_zO = Dr(z)E ⊆ E` and `K_z = {h | (z, h) ∈ K} ⊆ F` (induced sc-structures). -/
def ChartLinScFredholm (c : StrongBundleChart PX P) (f : X → Y) (x : X) (i : ℤ) : Prop :=
  ∃ z₁ : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv x ∧
  ∃ Kz : Submodule ℝ (c.F.lvl 0),
    (Kz : Set (c.F.lvl 0)) = {h | (c.φ.toPartialEquiv x, h) ∈ c.K} ∧
  ∃ (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (StrongRetr.r c.R) z₁)))
    (hK : c.F.IsScSubspace Kz)
    (L₀ : ↥(c.φ.model.E.levelSub (rangeS (scDeriv c.U (StrongRetr.r c.R) z₁)) 0) →L[ℝ]
      ↥(c.F.levelSub Kz 0)),
    (∀ v, (L₀ v : c.F.lvl 0) =
      scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ (v : c.φ.model.E.lvl 0)) ∧
    ∃ hL : @IsScOperator (c.φ.model.E.ofSubspace hT) (c.F.ofSubspace hK) L₀,
      IsScFredholm hL.toScOperator ∧ scIndex hL.toScOperator = i

end

/-- Proposition 3.52 / Theorem 3.19: at a zero `x` of an sc-Fredholm section of a tame strong
bundle, the linearization `Tf(x) : T_xX → Y_x` is an sc-Fredholm operator (in every strong bundle
chart around `x`). -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSection f → IsZeroAt P f x →
      ∀ c : StrongBundleChart PX P, Bd.IsChart c → x ∈ c.φ.source →
        ∃ i : ℤ, ChartLinScFredholm c f x i

end RoundTrip.V3_96
