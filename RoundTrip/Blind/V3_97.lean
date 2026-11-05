import Polyfold
/-! Blind formalization of V3_97 (the text's §3.1, Theorem 3.19, p. 74; §3.6, proof of
Theorem 3.54, p. 115).  `B` is the conjunction of the two claims.  Choices:
- Setting: `X Y : Type` (universe 0; nothing depends on the universe).  `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`, and
  `Bd : StrongBundle PX P` (Definition 2.51).
- (3.19) The quote gives the conclusion only; the hypotheses are those of Theorem 3.19 (as in my
  blind files V3_68/V3_101): `d_X ≡ 0` (`MPolyfold.IsWithoutBoundary`), `f` an sc-Fredholm section
  (`StrongBundle.IsScFredholmSection`, Definition 3.14, germ data in some compatible chart; no
  tameness assumed), `f(x₀) = 0` (`IsZeroAt`), `f'(x₀)` surjective (`StrongBundle.IsLinSurjAt`:
  onto in some strong bundle chart; a hypothesis, so the weakest intrinsic reading).  Doubt: the
  project's docstring of `IsScFredholmSection` says the text states Definition 3.14 for tame
  strong bundles; if Theorem 3.19 tacitly presupposes tameness, this conjunct is stronger than the
  text.
- (3.19) conclusion: there is an open `U ∋ x₀` such that `S(f, U) = {y ∈ U | f(y) = 0}`
  (`zeroSetIn`) is a sub-M-polyfold (Definition 2.20; `S(f, U)` paracompact, an instance argument
  of `subPolyfold`, asserted — it is true) whose induced structure is a smooth manifold of
  dimension `d` (`HasManifoldStructureOfDim`, defined here: an equivalent atlas of charts onto open
  subsets of `d`-dimensional spaces with the constant sc-structure; without boundary as
  `d_X ≡ 0`), where `d` is the Fredholm index of `f'(x₀)`: in every strong bundle chart around
  `x₀`, `D(f̂ ∘ r)(z)|_{T_zO} : T_zO → K_z` is sc-Fredholm of index `d` (`ChartLinScFredholm`, as in
  V3_68; `z = φ(x₀)` lifted to level `1`).
- (3.54, proof) Setting of Theorem 3.54: a *tame* strong bundle (`IsTameStrongBundle`, defined here
  as in the earlier blind files: tame base and an *equivalent* strong bundle atlas of charts with
  tame base retraction — a property of the given structure, not "every compatible chart is
  tame"), `f` an sc-Fredholm section in the sense of §3.6 (`IsScFredholmSectionTame`,
  Definition 3.51), `x` a zero with `(f, x)` in good position (Definition 3.53,
  `IsGoodPositionGermSc`, copied from my V3_94: germ data in a tame chart centred at `x`, `f'(x)`
  onto, and if `d_X(x) ≥ 1` the kernel in good position to the partial cone with an
  sc-complement).
- `d = dim ker f'(x)`: in every strong bundle chart around `x` (with the level-`1` lift `z₁` of
  `φ(x)`), `ker D(f̂ ∘ r)(z) ∩ T_zO` is finite-dimensional of dimension `d` (`KerDimInChart`); the
  kernel is chart independent, so the strong ("every chart") reading is used for this conclusion.
- "the solution set": `S(f, V)` for some open `V ∋ x` (the neighbourhood of Theorem 3.54).
- "the `d`-dimensional tangent germ property" (Definition 3.25): written out as in my blind file
  V3_22 (`HasTangentGermPropertyB`, with `IsGoodComplementB`), not the project's
  `HasTangentGermProperty` (whose data add closedness of `Y` and a `k`-dependent germ reading).
  Its setting "`M ⊆ X` (tame)" holds: `X` is tame as part of `IsTameStrongBundle`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_97
open Polyfold

/-- The M-polyfold `QZ` has an equivalent atlas of charts onto open subsets of `d`-dimensional
spaces with the constant sc-structure: a compatible smooth `d`-manifold structure without
boundary. -/
def HasManifoldStructureOfDim {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (QZ : MPolyfold Z) (d : ℕ) : Prop :=
  ∃ A : MAtlas Z, A.Equiv QZ.atlas ∧ ∀ χ ∈ A.charts,
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V) (_ : FiniteDimensional ℝ V)
      (U : Set V) (hU : IsRelOpenInQuadrant (ScBanach.const V) Set.univ U),
      Module.finrank ℝ V = d ∧ χ.model = LocalModel.ofRelOpen hU

/-- `S(f, U) = {y ∈ U | f(y) = 0}`. -/
def zeroSetIn {X Y : Type} (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (f : X → Y)
    (U : Set X) : Set X :=
  {y | y ∈ U ∧ IsZeroAt P f y}

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

/-- The kernel `ker f'(x) = ker D(f̂ ∘ r)(z) ∩ T_zO` read in the chart `c` at the level-`1` point
`z₁`. -/
noncomputable def linKerB (c : StrongBundleChart PX P) (f : X → Y) (z₁ : c.φ.model.E.lvl 1) :
    Submodule ℝ (c.φ.model.E.lvl 0) :=
  LinearMap.ker (scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ :
      c.φ.model.E.lvl 0 →ₗ[ℝ] c.F.lvl 0) ⊓
    rangeS (scDeriv c.U (StrongRetr.r c.R) z₁)

/-- `dim ker f'(x) = d`, read in the strong bundle chart `c` around `x`. -/
def KerDimInChart (c : StrongBundleChart PX P) (f : X → Y) (x : X) (d : ℕ) : Prop :=
  ∃ z₁ : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv x ∧
    FiniteDimensional ℝ (linKerB c f z₁) ∧ Module.finrank ℝ (linKerB c f z₁) = d

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

/-- (3.19) For `d_X ≡ 0` and `f'(x₀)` onto at a zero `x₀`, the local solution set is a smooth
manifold whose dimension is the Fredholm index of `f'(x₀)`; (3.54, proof) near a zero `x` in good
position, the solution set has the `d`-dimensional tangent germ property, `d = dim ker f'(x)`. -/
def B : Prop :=
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X),
    PX.IsWithoutBoundary → Bd.IsScFredholmSection f → IsZeroAt P f x₀ →
    Bd.IsLinSurjAt f x₀ →
      ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
        ∃ (hS : PX.IsSubMPolyfold (zeroSetIn P f U)) (_ : ParacompactSpace (zeroSetIn P f U)),
          ∃ d : ℕ, HasManifoldStructureOfDim (PX.subPolyfold hS) d ∧
            ∀ c : StrongBundleChart PX P, Bd.IsChart c → x₀ ∈ c.φ.source →
              ChartLinScFredholm c f x₀ d) ∧
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
    IsGoodPositionGermSc Bd f x →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
        ∃ d : ℕ, (∀ c : StrongBundleChart PX P, Bd.IsChart c → x ∈ c.φ.source →
            KerDimInChart c f x d) ∧
          HasTangentGermPropertyB PX (zeroSetIn P f V) d)

end RoundTrip.V3_97
