import Polyfold
/-! Blind formalization of V3_74 (the text's §3.2, proof of Theorem 3.27, p. 84, and §3.6, proof of
Theorem 3.54, p. 115).  `B` is the conjunction of the two claims.  Choices:
- (1) Setting of Theorem 3.27: `X : Type` (universe 0) with an M-polyfold structure `PX`, `X` tame
  (`MPolyfold.IsTame`), `M ⊆ X` with the `n`-dimensional tangent germ property (Definition 3.25,
  written out as in my blind files V3_72/V3_73 and the earlier V3_22: `HasTangentGermPropertyB`,
  data `IsGermData`).  "`δ` is an sc^∞-germ near every point of `V`": for every data
  `(φ, N, Y, V, δ)` at every `x ∈ M` and every `v₀ ∈ V`, the germ of `δ` at `v₀` (`w ↦ δ(v₀ + w)`) is
  an sc-smooth germ (Definition 3.2) on a germ of neighbourhoods of `0` in `(N ∩ C) − v₀` inside
  `V − v₀` (`IsScInftyGermNear`, as in V3_73).  The parenthetical "so that the charts `πφ` are
  compatible" states the purpose and is not claimed separately (the charts are V3_72's claim).
- (2) Setting of Theorem 3.54 (as in the earlier blind file V3_94): `X Y : Type`, `PX`, `P : Y → X`
  with fibrewise linear structure, `Bd : StrongBundle PX P` tame (`IsTameStrongBundle`: tame base
  and an equivalent atlas of tame strong bundle charts), `f` an sc-Fredholm section
  (`IsScFredholmSectionTame`, Definition 3.51), `f(x) = 0`, `(f, x)` in good position
  (Definition 3.53, `IsGoodPositionGermSc` of V3_94, with the text's sc-complement).  "The proof of
  Theorem 3.54 constructs the data at every zero": there is an open `V ∋ x` such that
  `S = {y ∈ V | f(y) = 0}` has the data of Definition 3.25 at every one of its points, i.e. `S` has
  the `d`-dimensional tangent germ property for some `d` (`HasTangentGermPropertyB`; the dimension,
  `dim ker f'(x)`, is not specified by the quote).  Together with (1) these data then satisfy the
  regularity condition.
- **I believe claim (1) is false as quoted**: Definition 3.25 controls `δ` only near `0`.
  Counterexample (see my V3_73): `X = ℝ²`, `C = E`, `N = ℝ×0`, `Y = 0×ℝ`, `φ = id`, `V = (−1,1)×0`,
  `δ(v) = χ(v)∛(v − ½)` (`χ` smooth, `0` near `0`, `1` near `½`), `M = graph δ` (a smooth curve, so
  `M` has the tangent germ property); `δ` is not differentiable at `v₀ = ½`.  I formalized the claim
  literally anyway (it holds for `v₀` in a neighbourhood of `0`).  Claim (2) looks true to me.
-/
namespace RoundTrip.V3_74
open Polyfold

/-- **Definition 3.21**: `P` is a good complement of the finite-dimensional `N` with respect to
`C`: an sc-complement (topological complement if `N` is not smooth) with the `ε`-property. -/
def IsGoodComplementB (E : ScBanach) (C : Set (E.lvl 0)) (N P : Submodule ℝ (E.lvl 0)) : Prop :=
  (N ≤ E.smooth → E.IsScSplitting N P) ∧
  (¬ N ≤ E.smooth → IsCompl N P ∧ IsClosed (P : Set (E.lvl 0))) ∧
  ∃ ε > (0 : ℝ), ∀ n ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + p ∈ C)

/-- **Definition 3.25 (2)**: `(φ, N, Y, V, δ)` are data of the `n`-dimensional tangent germ property
of `M` at `x`. -/
def IsGermData {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (M : Set X) (n : ℕ) (x : X) (φ : MChart X)
    (N Yc : Submodule ℝ (φ.model.E.lvl 0)) [FiniteDimensional ℝ N] (V : Set N)
    (δ : N → φ.model.E.lvl 0) : Prop :=
  PX.IsChart φ ∧ x ∈ φ.source ∧ φ.toPartialEquiv x = 0 ∧
  IsTameRetract φ.model.E φ.model.C φ.model.O ∧
  Module.finrank ℝ N = n ∧ N ≤ φ.model.E.smooth ∧
  (interior ((Subtype.val : N → φ.model.E.lvl 0) ⁻¹' φ.model.C)).Nonempty ∧
  IsGoodComplementB φ.model.E φ.model.C N Yc ∧
  (∃ O' : Set N, IsOpen O' ∧ V = O' ∩ (Subtype.val ⁻¹' φ.model.C)) ∧ (0 : N) ∈ V ∧
  (∀ v ∈ V, δ v ∈ Yc) ∧ ContinuousOn δ V ∧
  -- (i)
  φ.toPartialEquiv '' (M ∩ φ.source) = (fun v : N => (v : φ.model.E.lvl 0) + δ v) '' V ∧
  -- (ii)
  δ 0 = 0 ∧
  ∃ G : ScNbhdGerm (ScBanach.const N) ((Subtype.val : N → φ.model.E.lvl 0) ⁻¹' φ.model.C),
    (∀ v ∈ G.U 0, v ∈ V) ∧ IsScSmoothGerm (F := φ.model.E) G δ ∧
    ∃ D : (ScBanach.const N).lvl 1 → (ScBanach.const N).lvl 0 →L[ℝ] φ.model.E.lvl 0,
      IsSc1GermWith G δ D ∧ D 0 = 0

/-- **Definition 3.25**: `M ⊆ X` has the `n`-dimensional tangent germ property. -/
def HasTangentGermPropertyB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (M : Set X) (n : ℕ) : Prop :=
  M ⊆ PX.smoothSet ∧
  ∀ x ∈ M, ∃ (φ : MChart X) (N Yc : Submodule ℝ (φ.model.E.lvl 0)) (_ : FiniteDimensional ℝ N)
    (V : Set N) (δ : N → φ.model.E.lvl 0), IsGermData PX M n x φ N Yc V δ

/-- `δ` is an sc^∞-germ near `v₀`: the translated germ `w ↦ δ(v₀ + w)` is an sc-smooth germ
(Definition 3.2) on a germ of neighbourhoods of `0` in `{w | v₀ + w ∈ N ∩ C}` inside `V − v₀`. -/
def IsScInftyGermNear (E : ScBanach) (N : Submodule ℝ (E.lvl 0)) [FiniteDimensional ℝ N]
    (C : Set (E.lvl 0)) (V : Set N) (δ : N → E.lvl 0) (v₀ : N) : Prop :=
  ∃ G : ScNbhdGerm (ScBanach.const N) {w : N | ((v₀ + w : N) : E.lvl 0) ∈ C},
    (∀ w : N, w ∈ G.U 0 → v₀ + w ∈ V) ∧
    IsScSmoothGerm (F := E) G (fun w : N => δ (v₀ + w))

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

/-- The proof of Theorem 3.27 shows that `δ` is an sc^∞-germ near every point of `V`; the proof of
Theorem 3.54 constructs the data of Definition 3.25 at every zero near `x`. -/
def B : Prop :=
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      (M : Set X) (n : ℕ),
      PX.IsTame → HasTangentGermPropertyB PX M n →
      ∀ (x : X) (φ : MChart X) (N Yc : Submodule ℝ (φ.model.E.lvl 0)) [FiniteDimensional ℝ N]
        (V : Set N) (δ : N → φ.model.E.lvl 0),
        IsGermData PX M n x φ N Yc V δ →
        ∀ v₀ ∈ V, IsScInftyGermNear φ.model.E N φ.model.C V δ v₀) ∧
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      (Bd : StrongBundle PX P) (f : X → Y) (x : X),
      IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
      IsGoodPositionGermSc Bd f x →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
        ∃ d : ℕ, HasTangentGermPropertyB PX (zeroSetIn P f V) d)

end RoundTrip.V3_74
