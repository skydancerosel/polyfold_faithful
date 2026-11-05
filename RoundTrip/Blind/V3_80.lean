import Polyfold
/-! Blind formalization of V3_80 (the text's §3.6, proof of Theorem 3.54, property (4), and
Lemma 3.55, p. 114). Choices:
- Setting of Theorem 3.54 and its proof, as in my blind file V3_77 (c) and the earlier V3_48:
  `X Y : Type` (universe 0), `PX`, `P : Y → X` with fibrewise linear structure,
  `Bd : StrongBundle PX P` tame (`IsTameStrongBundle`), `f` an sc-Fredholm section
  (`IsScFredholmSectionTame`), `f(x₀) = 0`, and *every* good-position data at `x₀`
  (`IsGoodPosData`: a tame strong bundle chart `c` centred at `x₀`, a filled version `g`, an
  sc⁺-section `s` with `s(0) = g(0)`, surjectivity and good position of the linearization at `0`)
  with every conjugation `D` of `g − s` to a basic germ (`Ψ = D.Ψ`, `ψ = base Ψ`, `h + t = Ψ_*(g)`).
- "For every zero `y ∈ V`, with `ψφ(y) = v + σ(v)`": `V` is the open neighbourhood of `x₀` (in the
  chart domain) of the proof, `S = {y ∈ V | f(y) = 0}`, and `v, σ` come from step (3):
  `ψφ(S) = {v + σ(v) | v ∈ V'}` with `(Y, V', σ)` as in Corollary 3.47 for `h + t` over
  `K = ker D(h + t)(0)` (`GraphFormCor`, as in V3_77).  This context is asserted together with the
  claim (it is what gives `v`, `σ` a meaning; the claim itself is about every zero `y ∈ S`).
- "`f'(y)` is surjective and its kernel is in good position", read "in the chart at `x₀`" (the
  strong bundle chart `c`, which is not centred at `y`; `SurjGoodPosInChart`, as `IsSurjGoodPosAt`
  of the earlier blind file V3_70 but in the given chart): with `z = φ(y)` lifted to `z₁ ∈ E₁`,
  `r` the base retraction, `T_zO = range Dr(z)`, `L = D(f̂ ∘ r)(z)` (`f̂` the principal part,
  `scDeriv`): `L` maps `T_zO` onto `K_z = {k | (z, k) ∈ K}`, and `ker L ∩ T_zO` is in good position
  (Definition 3.21 inside `T_zO`, with an sc-complement, `IsInGoodPositionScIn`) to the partial cone
  `C_zO = T_zO ∩ C_z` (Definition 2.27; `C_z` the partial quadrant at `z`, `partialQuadrantAtWith`, for
  some presentation of `C`).  The quote does not restrict good position to `d_X(y) ≥ 1`, so it is
  claimed at every zero (at points with `C_z = E` it is automatic).
- "this follows from Corollary 3.41 and Lemma 3.55" names the proof and is not formalized.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_80
open Polyfold

/-- The kernel `ker L ⊆ E₀` of a bounded operator `L : E₀ → F₀`. -/
def kerOf {E F : ScBanach} (L : E.lvl 0 →L[ℝ] F.lvl 0) : Submodule ℝ (E.lvl 0) :=
  LinearMap.ker (L : E.lvl 0 →ₗ[ℝ] F.lvl 0)

/-- Definition 3.21 (complement): `Y` is a good complement of `N` with respect to `C`: an
sc-complement (`E_m = N_m ⊕ Y_m` on every level) with `n ∈ C ⟺ n + y ∈ C` for `|y|₀ ≤ ε|n|₀`. -/
def IsGoodComplementSc (E : ScBanach) (C : Set (E.lvl 0)) (N Y : Submodule ℝ (E.lvl 0)) :
    Prop :=
  E.IsScSplitting N Y ∧ ∃ ε > 0, ∀ x ∈ N, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖x‖ → (x ∈ C ↔ x + y ∈ C)

/-- The local solution data: `Y` a good complement of `N`, `V` a relatively open neighbourhood of
`0` in `N ∩ C`, `τ : V → Y₁` of class `C¹`, an sc-smooth germ into `E¹`, `τ(0) = 0`, `Dτ(0) = 0`. -/
def IsGraphSolution (E : ScBanach) (C : Set (E.lvl 0)) (N : Submodule ℝ (E.lvl 0))
    [FiniteDimensional ℝ N] (Y : Submodule ℝ (E.lvl 0)) (V : Set N) (τ : N → E.lvl 1) : Prop :=
  IsGoodComplementSc E C N Y ∧
  (∃ O : Set N, IsOpen O ∧ V = O ∩ (Subtype.val ⁻¹' C)) ∧ (0 : N) ∈ V ∧
  (∀ v ∈ V, E.toBase 1 (τ v) ∈ Y) ∧
  ContDiffOn ℝ 1 τ V ∧
  (∃ Vg : ScNbhdGerm (ScBanach.const N) (Subtype.val ⁻¹' C : Set N),
      Vg.U 0 ⊆ V ∧ IsScSmoothGerm (F := E.shift) Vg τ) ∧
  τ 0 = 0 ∧ HasFDerivWithinAt τ (0 : N →L[ℝ] E.lvl 1) V 0

/-- The graph `{v + τ(v) | v ∈ V} ⊆ E₀` of `τ : V → E₁` over `V ⊆ N`. -/
def graphSet (E : ScBanach) {N : Submodule ℝ (E.lvl 0)} (V : Set N) (τ : N → E.lvl 1) :
    Set (E.lvl 0) :=
  {x | ∃ v ∈ V, x = (v : E.lvl 0) + E.toBase 1 (τ v)}

/-- Definition 3.21 inside the subspace `T`, with an sc-complement: `N ⊆ T`, `N ∩ C` has nonempty
interior in `N`, and `N` has an sc-complement `P` in `T` (`T_m = N_m ⊕ P_m` on every level) such
that `n ∈ C ⟺ n + p ∈ C` for `n ∈ N`, `p ∈ P`, `|p|₀ ≤ ε|n|₀`. -/
def IsInGoodPositionScIn (E : ScBanach) (T : Submodule ℝ (E.lvl 0)) (C : Set (E.lvl 0))
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
      IsInGoodPositionScIn c.φ.model.E (rangeS (scDeriv c.U (StrongRetr.r c.R) 0))
        ((rangeS (scDeriv c.U (StrongRetr.r c.R) 0) : Set (c.φ.model.E.lvl 0)) ∩ c.φ.model.C)
        (LinearMap.ker (scDeriv c.U g 0 : c.φ.model.E.lvl 0 →ₗ[ℝ] c.F.lvl 0) ⊓
          rangeS (scDeriv c.U (StrongRetr.r c.R) 0)))

/-- Step (3) of the proof of Theorem 3.54: with `ψ = base Ψ` and `K = ker D(Ψ_*g)(0) ⊆ ℝⁿ ⊕ W`,
`ψφ(S) = {v + σ(v) | v ∈ V'}` for data `(Y, V', σ)` as in Corollary 3.47 (with respect to
`C' = C̃ ⊕ W`). -/
def GraphFormCor (c : StrongBundleChart PX P) {k : c.φ.model.E.lvl 0 → c.F.lvl 0}
    (D : ConjugationData c.U k) (g : c.φ.model.E.lvl 0 → c.F.lvl 0) (S : Set X) : Prop :=
  ∃ (_ : FiniteDimensional ℝ (kerOf (E := ScBanach.paramProd D.Pn D.W)
        (F := ScBanach.paramProd D.Q D.W) (scDeriv D.U' (pushforward D.Ψ D.Ψ' g) 0)))
    (Yg : Submodule ℝ ((ScBanach.paramProd D.Pn D.W).lvl 0))
    (V' : Set (kerOf (E := ScBanach.paramProd D.Pn D.W) (F := ScBanach.paramProd D.Q D.W)
      (scDeriv D.U' (pushforward D.Ψ D.Ψ' g) 0)))
    (σ : kerOf (E := ScBanach.paramProd D.Pn D.W) (F := ScBanach.paramProd D.Q D.W)
      (scDeriv D.U' (pushforward D.Ψ D.Ψ' g) 0) → (ScBanach.paramProd D.Pn D.W).lvl 1),
    IsGraphSolution (ScBanach.paramProd D.Pn D.W) (D.Ct ×ˢ Set.univ) _ Yg V' σ ∧
    (fun y => IsStrongBundleMap.base D.Ψ (c.φ.toPartialEquiv y)) '' S =
      graphSet (ScBanach.paramProd D.Pn D.W) V' σ

/-- `f'(y)` read in the strong bundle chart `c` (around `y`, not necessarily centred there): with
`z = φ(y)` lifted to `z₁ ∈ E₁`, `L = D(f̂ ∘ r)(z)` maps `T_zO = range Dr(z)` onto `K_z`, and
`ker L ∩ T_zO` is in good position to the partial cone `C_zO = T_zO ∩ C_z` inside `T_zO`. -/
def SurjGoodPosInChart (c : StrongBundleChart PX P) (f : X → Y) (y : X) : Prop :=
  ∃ z₁ : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv y ∧
    (∀ k : c.F.lvl 0, (c.φ.toPartialEquiv y, k) ∈ c.K →
      ∃ v ∈ rangeS (scDeriv c.U (StrongRetr.r c.R) z₁),
        scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ v = k) ∧
    ∃ (n : ℕ) (W : ScBanach) (Tp : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
      c.φ.model.C = (Tp.lvl 0) ⁻¹' quadrant n W 0 ∧
      IsInGoodPositionScIn c.φ.model.E (rangeS (scDeriv c.U (StrongRetr.r c.R) z₁))
        ((rangeS (scDeriv c.U (StrongRetr.r c.R) z₁) : Set (c.φ.model.E.lvl 0)) ∩
          partialQuadrantAtWith Tp (c.φ.toPartialEquiv y))
        (LinearMap.ker
            (scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ :
              c.φ.model.E.lvl 0 →ₗ[ℝ] c.F.lvl 0) ⊓
          rangeS (scDeriv c.U (StrongRetr.r c.R) z₁))

end

/-- Theorem 3.54, property (4), in the chart at `x₀`: near `x₀` the solution set is the graph
`ψφ(S) = {v + σ(v)}`, and at every zero `y ∈ S` the linearization `f'(y)` is surjective with kernel
in good position to the partial cone at `y`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x₀ →
    ∀ (c : StrongBundleChart PX P) (h0 : 0 ∈ c.U) (g : c.φ.model.E.lvl 0 → c.F.lvl 0)
      (s : c.φ.model.E.lvl 0 → c.F.shift.lvl 0)
      (D : ConjugationData c.U (fun u => g u - c.F.toBase 1 (s u))),
      IsGoodPosData Bd f x₀ c h0 g s →
      ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ c.φ.source ∧
        GraphFormCor c D g (zeroSetIn P f V) ∧
        ∀ y ∈ zeroSetIn P f V, SurjGoodPosInChart c f y

end RoundTrip.V3_80
