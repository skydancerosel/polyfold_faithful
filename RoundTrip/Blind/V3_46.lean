import Polyfold
/-! Blind formalization of V3_46 (the text's §3.6, Proposition 3.52, p. 110). Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the fibrewise
  linear structure as instances on `P ⁻¹' {x}`, `Bd : StrongBundle PX P`.
- "tame strong bundle": `IsTameStrongBundle` (defined here): tame base (`MPolyfold.IsTame`) and an
  equivalent strong bundle atlas all of whose charts have a tame base retraction
  (`ScRetraction.IsTame`, Definition 2.34).  A property of the given structure (existential over
  atlases), not "every compatible chart is tame".
- "`f` an sc-Fredholm section of the tame strong bundle": `StrongBundle.IsScFredholmSectionTame`
  (Definition 3.51: Definition 3.14 with the germ data of Definition 3.11 in a tame strong bundle
  chart, the text's recall in §3.6).  `f(x) = 0`: `IsZeroAt P f x`.
- `Tf(x) : T_xX → Y_x` has no intrinsic linear structure in the project, so it is represented in a
  strong bundle chart `c` around `x` (any chart compatible with the bundle structure,
  `StrongBundle.IsChart`): with `z = φ(x)` lifted to `z₁ ∈ E₁`, `r` the base retraction of the
  strong bundle retraction `R`, `T_zO = range Dr(z)` and `K_z = {h | (z, h) ∈ K}` (the fibre of the
  chart over `z`, identified with `Y_x`), the linearization is `D(f̂ ∘ r)(z)` restricted to `T_zO`
  (`f̂` = principal part, `StrongBundleChart.principal`).  "sc-Fredholm" (Definition 1.8,
  `IsScFredholm`) needs sc-structures on `T_zO` and `K_z`: the claim asserts that both are
  sc-subspaces (`ScBanach.IsScSubspace`, induced structure `ScBanach.ofSubspace`), that the
  linearization maps `T_zO` into `K_z`, is an sc-operator there (`IsScOperator`) and is
  sc-Fredholm, with index `scIndex` (`dim ker − dim coker`).  This is `ChartLinScFredholm`.
  Since `Tf(x)` is intrinsic, the claim is stated in *every* chart around `x` (a conclusion, so
  this is the strong reading of "is sc-Fredholm").
- "of the index `n − N` of the basic germ": for *every* choice of the germ data of
  Definition 3.11 at `x` (tame chart centred at `x`, filled version `g` of `f̂`, sc⁺-section `s`
  with `s(0) = g(0)`, and a conjugation `D : ConjugationData` of `g − s` to a basic germ
  `O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W`, `C̃ ⊆ ℝⁿ`), the index in every chart is
  `n − N = dim D.Pn − dim D.Q`.  The first conjunct (sc-Fredholm in every chart, some index) is
  stated separately so that it does not depend on the germ data.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_46
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

/-- The germ data of Definition 3.11 at `x` in a tame strong bundle chart `c` centred at `x`: a
filled version `g` of the principal part and an sc⁺-section `s` (values in `F₁`) with
`s(0) = g(0)` (the conjugation of `g − s` to a basic germ is supplied separately). -/
def IsTameGermDataAt (Bd : StrongBundle PX P) (f : X → Y) (x : X) (c : StrongBundleChart PX P)
    (h0 : 0 ∈ c.U) (g : c.φ.model.E.lvl 0 → c.F.lvl 0)
    (s : c.φ.model.E.lvl 0 → c.F.shift.lvl 0) : Prop :=
  Bd.IsTameChart c ∧ x ∈ c.φ.source ∧ c.φ.toPartialEquiv x = 0 ∧
    IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g ∧
    @IsScSmooth _ c.F.shift c.U s ∧ c.F.toBase 1 (s 0) = g 0

end

/-- Proposition 3.52: at a zero `x` of an sc-Fredholm section of a tame strong bundle, the
linearization `Tf(x) : T_xX → Y_x` is sc-Fredholm, of index `n − N` (the dimensions of the basic
germ of the Fredholm germ data at `x`). -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
      (∀ c : StrongBundleChart PX P, Bd.IsChart c → x ∈ c.φ.source →
          ∃ i : ℤ, ChartLinScFredholm c f x i) ∧
      (∀ (c₀ : StrongBundleChart PX P) (h0 : 0 ∈ c₀.U) (g : c₀.φ.model.E.lvl 0 → c₀.F.lvl 0)
          (s : c₀.φ.model.E.lvl 0 → c₀.F.shift.lvl 0),
          IsTameGermDataAt Bd f x c₀ h0 g s →
          ∀ D : ConjugationData c₀.U (fun u => g u - c₀.F.toBase 1 (s u)),
          ∀ c : StrongBundleChart PX P, Bd.IsChart c → x ∈ c.φ.source →
            ChartLinScFredholm c f x
              ((Module.finrank ℝ D.Pn : ℤ) - (Module.finrank ℝ D.Q : ℤ)))

end RoundTrip.V3_46
