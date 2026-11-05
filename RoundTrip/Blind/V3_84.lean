import Polyfold
/-! Blind formalization of V3_84 (the text's §3.6, proof of Theorem 3.54, p. 115). Choices:
- Setting (Theorem 3.54): `X Y : Type` (universe 0; nothing depends on the universe).
  `PX : MPolyfold X`, `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`,
  `Bd : StrongBundle PX P` (Definition 2.51); hypotheses of Theorem 3.54: `Bd` tame, `f` an
  sc-Fredholm section, `f(x) = 0`, `(f, x)` in good position ("Consequently" refers to this
  setting; I added exactly these hypotheses).
- "tame strong bundle": `IsTameStrongBundle` (defined here, as in the earlier blind files): tame
  base (`MPolyfold.IsTame`) and an *equivalent* strong bundle atlas all of whose charts have a tame
  base retraction (`ScRetraction.IsTame`).  A property of the given structure, not "every chart
  is tame".
- "sc-Fredholm section" (§3.6, tame bundle): `IsScFredholmSectionTame` (Definition 3.51).
  `f(x) = 0`: `IsZeroAt P f x`.  "`(f, x)` in good position" (Definition 3.53):
  `IsGoodPositionGermSc`, defined here exactly as in my earlier blind files V3_94/V3_82.
- "the solution set `S ⊆ V`": there is an open `V ∋ x` (`V` is the neighbourhood of Theorem
  3.54) and `S = {y ∈ V | f(y) = 0}` (`zeroSetIn`).
- "`d = dim ker f'(x)`": `f'(x)` read in a strong bundle chart `c` around `x` (any chart
  compatible with the bundle structure, `StrongBundle.IsChart`): with `z = φ(x)` lifted to
  `z₁ ∈ E₁`, `ker f'(x) = ker D(f̂ ∘ r)(z₁) ∩ T_zO`, `T_zO = range Dr(z₁)` (`f̂` the principal part),
  and `d` its `Module.finrank`.  The claim is made for the `d` computed in *every* such chart
  (the strong reading; the dimension is chart independent).
- "the `d`-dimensional tangent germ property" (Definition 3.25): `HasTangentGermPropertyB`, copied
  from the blind file V3_22 (the blind formalization of Definition 3.25, with its good-complement
  notion `IsGoodComplementB` of Definition 3.21): `S ⊆ X_∞`, and at every point of `S` a chart onto
  a tame retract centred there, a `d`-dimensional smooth `N` in good position with good complement
  `Y`, a relatively open `V' ∋ 0` in `N ∩ C` and `δ : V' → Y` with `φ(S ∩ U) = {v + δ(v)}` and `δ`
  an sc^∞-germ with `δ(0) = 0`, `Dδ(0) = 0`.  I did not use the project's `HasTangentGermProperty`
  (its docstrings report an algebraic good complement and a `k`-dependent reading of
  "sc^∞-germ"), preferring the independent blind formalization.
- "and Theorem 3.27 applies": Theorem 3.27's hypotheses are `X` tame (part of the hypothesis
  `IsTameStrongBundle`) and the tangent germ property just claimed; I read the phrase as this
  remark and did not add Theorem 3.27's conclusion to `B`.
- The item's title ("at the centre: the data of Definition 3.25 at `x₀`") suggests a version with
  the data only at `x`; the quote claims the tangent germ property of all of `S`, which is what
  `B` states.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_84
open Polyfold

/-- **Definition 3.21**: `P` is a good complement of the finite-dimensional `N` with respect to
`C`: an sc-complement (topological complement if `N` is not smooth) with the `ε`-property. -/
def IsGoodComplementB (E : ScBanach) (C : Set (E.lvl 0)) (N P : Submodule ℝ (E.lvl 0)) : Prop :=
  (N ≤ E.smooth → E.IsScSplitting N P) ∧
  (¬ N ≤ E.smooth → IsCompl N P ∧ IsClosed (P : Set (E.lvl 0))) ∧
  ∃ ε > (0 : ℝ), ∀ n ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + p ∈ C)

/-- **Definition 3.25**: `M ⊆ X` has the `n`-dimensional tangent germ property. -/
def HasTangentGermPropertyB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (M : Set X) (n : ℕ) : Prop :=
  M ⊆ PX.smoothSet ∧
  ∀ x ∈ M, ∃ φ : MChart X, PX.IsChart φ ∧ x ∈ φ.source ∧ φ.toPartialEquiv x = 0 ∧
    IsTameRetract φ.model.E φ.model.C φ.model.O ∧
    ∃ (N Yc : Submodule ℝ (φ.model.E.lvl 0)) (_ : FiniteDimensional ℝ N),
      Module.finrank ℝ N = n ∧ N ≤ φ.model.E.smooth ∧
      (interior ((Subtype.val : N → φ.model.E.lvl 0) ⁻¹' φ.model.C)).Nonempty ∧
      IsGoodComplementB φ.model.E φ.model.C N Yc ∧
      ∃ V : Set N, (∃ O' : Set N, IsOpen O' ∧ V = O' ∩ (Subtype.val ⁻¹' φ.model.C)) ∧
        (0 : N) ∈ V ∧
      ∃ δ : N → φ.model.E.lvl 0, (∀ v ∈ V, δ v ∈ Yc) ∧ ContinuousOn δ V ∧
        -- (i)
        φ.toPartialEquiv '' (M ∩ φ.source) = (fun v : N => (v : φ.model.E.lvl 0) + δ v) '' V ∧
        -- (ii)
        δ 0 = 0 ∧
        ∃ G : ScNbhdGerm (ScBanach.const N) ((Subtype.val : N → φ.model.E.lvl 0) ⁻¹' φ.model.C),
          (∀ v ∈ G.U 0, v ∈ V) ∧ IsScSmoothGerm (F := φ.model.E) G δ ∧
          ∃ D : (ScBanach.const N).lvl 1 → (ScBanach.const N).lvl 0 →L[ℝ] φ.model.E.lvl 0,
            IsSc1GermWith G δ D ∧ D 0 = 0

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

/-- `ker f'(x)` read in the strong bundle chart `c` at the level-`1` lift `z₁` of `φ(x)`:
`ker D(f̂ ∘ r)(z₁) ∩ T_zO`. -/
noncomputable def kerLin (c : StrongBundleChart PX P) (f : X → Y) (z₁ : c.φ.model.E.lvl 1) :
    Submodule ℝ (c.φ.model.E.lvl 0) :=
  LinearMap.ker (scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ :
      c.φ.model.E.lvl 0 →ₗ[ℝ] c.F.lvl 0) ⊓
    rangeS (scDeriv c.U (StrongRetr.r c.R) z₁)

end

/-- Proof of Theorem 3.54: near a zero `x` with `(f, x)` in good position there is an open `V ∋ x`
such that `S = {y ∈ V | f(y) = 0}` has the `d`-dimensional tangent germ property,
`d = dim ker f'(x)` (so that Theorem 3.27 applies to `S` in the tame `X`). -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
    IsGoodPositionGermSc Bd f x →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
        ∀ (c : StrongBundleChart PX P), Bd.IsChart c → x ∈ c.φ.source →
          ∀ z₁ : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv x →
            HasTangentGermPropertyB PX (zeroSetIn P f V) (Module.finrank ℝ (kerLin c f z₁))

end RoundTrip.V3_84
