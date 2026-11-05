import Polyfold
/-! Blind formalization of V3_48 (the text's §3.6, Theorem 3.54, p. 111, with claim (3) from its
proof, pp. 111–115).  `B` is the conjunction of (1), (2), (3) for one `V`.  Choices:
- Setting: `X Y : Type` (universe 0; nothing depends on the universe).  `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`, and
  `Bd : StrongBundle PX P` (Definition 2.51).
- "tame strong bundle": `IsTameStrongBundle` (defined here, as in the earlier blind files): tame
  base (`MPolyfold.IsTame`) and an *equivalent* strong bundle atlas all of whose charts have a tame
  base retraction (`ScRetraction.IsTame`).  A property of the given structure, not "every chart
  is tame".
- "sc-Fredholm section of a tame strong bundle" (§3.6): `IsScFredholmSectionTame`
  (Definition 3.51).  `f(x) = 0`: `IsZeroAt P f x`.
- "`(f, x)` in good position" (Definition 3.53, known to me only through the project's docstrings
  of `IsGoodPositionGerm`/`IsGoodPositionAt`), exactly as in my blind file V3_94
  (`IsGoodPositionGermSc`): data of Definition 3.11 in a *tame* strong bundle chart `c` centred at
  `x` (filled version `g` of the principal part, sc⁺-section `s : U → F¹` with `s(0) = g(0)`,
  a conjugation `D` of `g − s` to a basic germ) such that `Dg(0)|_{T₀O}` maps onto `K₀` and, if
  `d_X(x) ≥ 1`, `ker Dg(0) ∩ T₀O` is in good position (Definition 3.21 with the text's
  sc-complement, `IsInGoodPositionSc`) to `C₀O = T₀O ∩ C` inside `T₀O`.  The project's
  `IsGoodPositionGermTame` (algebraic complement only) was not used.
- Claim (3) refers to the data `φ, Ψ, g` of the hypothesis, so `B` quantifies over *every* such
  data `(c, g, s, D)` at `x` (the proof works with whatever data the hypothesis provides); this
  is stronger than "for some data", and implies the version with the bare hypothesis
  "`(f, x)` in good position" for (1)–(2).
- "There is an open `V ∋ x`": an open subset of `X`, inside the chart domain (`V ⊆ dom φ`, so
  that `ψφ(S)` makes sense); `S = {y ∈ V | f(y) = 0}` (`zeroSetIn`).
- (1) `IsGoodPositionGermSc Bd f y` for all `y ∈ S`.  (2) `IsSubMPolyfold S`, `S` paracompact
  (instance argument of `subPolyfold`; asserted, it is true), and `HasCornerStructure` of the
  induced structure (Definition 4.1).
- (3) `ψ = base Ψ` (`IsStrongBundleMap.base D.Ψ`, the sc-diffeomorphism `U → U'` covered by the
  conjugation `Ψ`), `Ψ_*(g) = h + t` is the push-forward `pushforward D.Ψ D.Ψ' g` (the project's
  docstring identifies it with the text's `h + t`), defined on `U' ⊆ C' = C̃ ⊕ W ⊆ E' = ℝⁿ ⊕ W`,
  and `K = ker DΨ_*(g)(0)`.  I do not have the statement of Corollary 3.47, so for "the `σ` of
  Corollary 3.47" I require only what the shape of (3) needs: a good complement `Z` of `K` with
  respect to `C'` (Definition 3.21's complement: an sc-complement of `K` in `E'` with the `ε`
  property, `IsGoodComplementSc`), a relatively open neighbourhood `V'` of `0` in `K ∩ C'`, and a
  map `σ : V' → Z` with `σ(0) = 0`; then `ψ(φ(S)) = {v + σ(v) | v ∈ V'}` (`GraphForm`).  If
  Corollary 3.47 gives `σ` further properties (e.g. smoothness), they are not claimed here.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_48
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

/-- Definition 3.21, the complement: `Z` is a good complement of `N` in `E` with respect to `C`:
an sc-subspace with `E_m = N_m ⊕ Z_m` on every level and `ε > 0` such that `n ∈ C ⟺ n + p ∈ C`
for `n ∈ N`, `p ∈ Z`, `|p|₀ ≤ ε|n|₀`. -/
def IsGoodComplementSc (E : ScBanach) (C : Set (E.lvl 0)) (N Z : Submodule ℝ (E.lvl 0)) :
    Prop :=
  E.IsScSubspace Z ∧
    (∀ m, E.levelSub N m ⊓ E.levelSub Z m = ⊥ ∧ E.levelSub N m ⊔ E.levelSub Z m = ⊤) ∧
    ∃ ε > 0, ∀ n ∈ N, ∀ p ∈ Z, ‖p‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + p ∈ C)

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

/-- Claim (3): with `ψ = base Ψ` and `K = ker D(Ψ_*g)(0) ⊆ E' = ℝⁿ ⊕ W`, there are a good
complement `Z` of `K` (with respect to `C' = C̃ ⊕ W`), a relatively open neighbourhood `V'` of `0`
in `K ∩ C'` and `σ : V' → Z` with `σ(0) = 0` such that `ψφ(S) = {v + σ(v) | v ∈ V'}`. -/
def GraphForm (c : StrongBundleChart PX P) {k : c.φ.model.E.lvl 0 → c.F.lvl 0}
    (D : ConjugationData c.U k) (g : c.φ.model.E.lvl 0 → c.F.lvl 0) (S : Set X) : Prop :=
  ∃ (Z : Submodule ℝ ((ScBanach.paramProd D.Pn D.W).lvl 0))
    (V' : Set ((ScBanach.paramProd D.Pn D.W).lvl 0))
    (σ : (ScBanach.paramProd D.Pn D.W).lvl 0 → (ScBanach.paramProd D.Pn D.W).lvl 0),
    IsGoodComplementSc (ScBanach.paramProd D.Pn D.W) (D.Ct ×ˢ Set.univ)
      (LinearMap.ker (scDeriv D.U' (pushforward D.Ψ D.Ψ' g) 0 :
        (ScBanach.paramProd D.Pn D.W).lvl 0 →ₗ[ℝ] (ScBanach.paramProd D.Q D.W).lvl 0)) Z ∧
    0 ∈ V' ∧
    (∃ O : Set ((ScBanach.paramProd D.Pn D.W).lvl 0), IsOpen O ∧
      V' = O ∩ ((LinearMap.ker (scDeriv D.U' (pushforward D.Ψ D.Ψ' g) 0 :
        (ScBanach.paramProd D.Pn D.W).lvl 0 →ₗ[ℝ] (ScBanach.paramProd D.Q D.W).lvl 0) :
          Set ((ScBanach.paramProd D.Pn D.W).lvl 0)) ∩ (D.Ct ×ˢ Set.univ))) ∧
    (∀ v ∈ V', σ v ∈ Z) ∧ σ 0 = 0 ∧
    (fun y => IsStrongBundleMap.base D.Ψ (c.φ.toPartialEquiv y)) '' S =
      {e | ∃ v ∈ V', e = v + σ v}

end

/-- Theorem 3.54 with (3) of its proof: for every good-position data `(φ, g, s, Ψ)` at the zero
`x`, there is an open `V ∋ x` in the chart domain such that (1) `(f, y)` is in good position at
every zero `y ∈ V`, (2) `S = {y ∈ V | f(y) = 0}` is a sub-M-polyfold equivalent to a manifold with
boundary with corners, and (3) `ψφ(S) = {v + σ(v) | v ∈ V'}` is the graph of a map `σ` into a good
complement of `ker D(h + t)(0)`, `h + t = Ψ_*(g)`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
    ∀ (c : StrongBundleChart PX P) (h0 : 0 ∈ c.U) (g : c.φ.model.E.lvl 0 → c.F.lvl 0)
      (s : c.φ.model.E.lvl 0 → c.F.shift.lvl 0)
      (D : ConjugationData c.U (fun u => g u - c.F.toBase 1 (s u))),
      IsGoodPosData Bd f x c h0 g s →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ c.φ.source ∧
        (∀ y ∈ zeroSetIn P f V, IsGoodPositionGermSc Bd f y) ∧
        (∃ (hS : PX.IsSubMPolyfold (zeroSetIn P f V)) (_ : ParacompactSpace (zeroSetIn P f V)),
          (PX.subPolyfold hS).HasCornerStructure) ∧
        GraphForm c D g (zeroSetIn P f V)

end RoundTrip.V3_48
