import Polyfold
/-! Blind formalization of V3_77 (the text's §3.5, Theorem 3.43, p. 102, and Corollary 3.47,
p. 106; §3.6, proof of Theorem 3.54, step (3), p. 114).  `B` is the conjunction of the three
claims.  Choices:
- (a) Theorem 3.43 and (b) Corollary 3.47 ("local solvability with a good complement `Y` of the
  kernel"): stated exactly as in the earlier blind files V3_38 and V3_42 (whose definitions are
  copied: `IsGoodComplementSc` with the text's *sc-complement*, `IsInGoodPositionSc`,
  `IsGraphSolution` (good complement `Y`, `V` relatively open in `K ∩ C`, `τ : V → Y₁` of class `C¹`,
  an sc-smooth germ into `E¹`, `τ(0) = 0`, `Dτ(0) = 0`), `graphSet`, `kerOf`, `IsRaisedBasic`,
  `Concl`, `LocalGraphRep`).  Setting: `E = ℝⁿ ⊕ W` (`ScBanach.paramProd`), `C = C̃ × W`,
  `f = h + s` with `h` basic and `s` an sc⁺-germ, `s(0) = 0`; `Df(0)` onto, `K = ker Df(0)` in good
  position; for (a) `g = Φ_*(f)` for every strong bundle isomorphism `Φ` as produced by
  Theorem 3.38.
- The md title speaks of "a closed good complement projecting into the quadrant".  The quoted
  claims only say "a good complement `Y` of the kernel": the text's good complement is an
  sc-complement, hence closed (included); that the projection along `Y` maps the quadrant into
  itself is not claimed by the quoted text and is *not* included.
- (c) Theorem 3.54, step (3): setting of Theorem 3.54 as in the earlier blind file V3_48 (tame
  strong bundle `IsTameStrongBundle`, sc-Fredholm section `IsScFredholmSectionTame`, `f(x) = 0`); for
  every good-position data at `x` (`IsGoodPosData`: tame strong bundle chart `c` centred at `x`,
  filled version `g`, sc⁺-section `s` with `s(0) = g(0)`, surjectivity and good position of the
  linearization) and every conjugation `D` of `g − s` to a basic germ (`Ψ = D.Ψ`, `ψ = base Ψ`,
  `h + t = Ψ_*(g)` = `pushforward D.Ψ D.Ψ' g` on `U' ⊆ C' = C̃ ⊕ W`), there is an open `V ∋ x` in the
  chart domain such that, with `S = {y ∈ V | f(y) = 0}` and `K = ker D(h + t)(0)` (`scDeriv` at `0`),
  `ψφ(S) = {v + σ(v) | v ∈ V'}` where `(Y, V', σ)` are as in Corollary 3.47 for `h + t`
  (`IsGraphSolution` with respect to `C'`; `K` finite-dimensional, asserted).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_77
open Polyfold

/-- Definition 3.21 (complement): `Y` is a good complement of `N` with respect to `C`: an
sc-complement (`E_m = N_m ⊕ Y_m` on every level) with `n ∈ C ⟺ n + y ∈ C` for `|y|₀ ≤ ε|n|₀`. -/
def IsGoodComplementSc (E : ScBanach) (C : Set (E.lvl 0)) (N Y : Submodule ℝ (E.lvl 0)) :
    Prop :=
  E.IsScSplitting N Y ∧ ∃ ε > 0, ∀ x ∈ N, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖x‖ → (x ∈ C ↔ x + y ∈ C)

/-- Definition 3.21: the (finite-dimensional) subspace `N` is in good position to `C`: `N ∩ C` has
nonempty interior in `N` and `N` has a good complement. -/
def IsInGoodPositionSc (E : ScBanach) (C : Set (E.lvl 0)) (N : Submodule ℝ (E.lvl 0)) : Prop :=
  (interior (Subtype.val ⁻¹' C : Set N)).Nonempty ∧ ∃ Y, IsGoodComplementSc E C N Y

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

/-- The kernel `ker L ⊆ E₀` of a bounded operator `L : E₀ → F₀`. -/
def kerOf {E F : ScBanach} (L : E.lvl 0 →L[ℝ] F.lvl 0) : Submodule ℝ (E.lvl 0) :=
  LinearMap.ker (L : E.lvl 0 →ₗ[ℝ] F.lvl 0)

/-- The level-raised germ `g¹` of `g : U' → ℝ^{N'} ⊕ W'` is a basic germ: some basic germ `g₁` on a
germ of neighbourhoods `G₁` of `0` in `C̃' ⊕ W'¹` agrees with `g` on level `1` inside `U'`. -/
def IsRaisedBasic {n' N' : ℕ} {W' : ScBanach} (Ct' : Set (Fin n' → ℝ))
    (U' : Set ((ScBanach.paramProd (Fin n' → ℝ) W').lvl 0))
    (g : (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0 →
      (ScBanach.paramProd (Fin N' → ℝ) W').lvl 0) : Prop :=
  ∃ (G₁ : ScNbhdGerm (ScBanach.paramProd (Fin n' → ℝ) W'.shift) (Ct' ×ˢ Set.univ))
    (g₁ : (Fin n' → ℝ) × W'.lvl 1 → (Fin N' → ℝ) × W'.lvl 1)
    (B₁ : (Fin n' → ℝ) × W'.lvl 1 → W'.lvl 1),
    IsBasicGerm Ct' G₁ g₁ B₁ ∧
      ∀ x ∈ G₁.U 0,
        (((x.1, W'.incl 0 x.2) : (Fin n' → ℝ) × W'.lvl 0) ∈ U') ∧
          g (x.1, W'.incl 0 x.2) = ((g₁ x).1, W'.incl 0 (g₁ x).2)

/-- The conclusion of Theorem 3.43 for `f : U → F`, the base map `φ : U → U'` and `g = Φ_*(f)`:
`K' = ker Dg(0)` is in good position to `C'`, there are `Y'`, `V`, `τ` as in `IsGraphSolution`, and
after shrinking `U` to `U₀`: `φ({f = 0}) = {g = 0} = {y + τ(y) | y ∈ V}`. -/
def Concl (E F E' F' : ScBanach) (C U : Set (E.lvl 0)) (C' U' : Set (E'.lvl 0))
    (f : E.lvl 0 → F.lvl 0) (φ : E.lvl 0 → E'.lvl 0) (g : E'.lvl 0 → F'.lvl 0) : Prop :=
  ∃ (G' : ScNbhdGerm E' C') (D' : E'.lvl 1 → E'.lvl 0 →L[ℝ] F'.lvl 0),
    G'.U 0 ⊆ U' ∧ IsSc1GermWith G' g D' ∧
    ∃ (_ : FiniteDimensional ℝ (kerOf (D' 0))),
      IsInGoodPositionSc E' C' (kerOf (D' 0)) ∧
      ∃ (Y' : Submodule ℝ (E'.lvl 0)) (V : Set (kerOf (D' 0))) (τ : kerOf (D' 0) → E'.lvl 1),
        IsGraphSolution E' C' (kerOf (D' 0)) Y' V τ ∧
        ∃ U₀ : Set (E.lvl 0), IsRelOpenInQuadrant E C U₀ ∧ 0 ∈ U₀ ∧ U₀ ⊆ U ∧
          φ '' {x | x ∈ U₀ ∧ f x = 0} = {x' | x' ∈ φ '' U₀ ∧ g x' = 0} ∧
          {x' | x' ∈ φ '' U₀ ∧ g x' = 0} = graphSet E' V τ

/-- The conclusion of Corollary 3.47 for `f` with domain `U ⊆ C` and `K`: a good complement `Y` and
`σ : V → Y₁` as in `IsGraphSolution`, and after shrinking `U` to a relatively open neighbourhood
`U₀` of `0` in `C`, `{x ∈ U₀ | f(x) = 0} = {v + σ(v) | v ∈ V}`. -/
def LocalGraphRep (E F : ScBanach) (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (K : Submodule ℝ (E.lvl 0)) [FiniteDimensional ℝ K] : Prop :=
  ∃ (Y : Submodule ℝ (E.lvl 0)) (V : Set K) (σ : K → E.lvl 1),
    IsGraphSolution E C K Y V σ ∧
    ∃ U₀ : Set (E.lvl 0), IsRelOpenInQuadrant E C U₀ ∧ 0 ∈ U₀ ∧ U₀ ⊆ U ∧
      {x | x ∈ U₀ ∧ f x = 0} = graphSet E V σ

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

end

/-- Theorem 3.43 and Corollary 3.47 (local solvability with a good complement of the kernel), and
step (3) of the proof of Theorem 3.54 (near `x` the solution set is, in the chart `ψφ`, the graph of
the `σ` of Corollary 3.47 over `ker D(h + t)(0) ∩ C'`). -/
def B : Prop :=
  -- (a) Theorem 3.43
  (∀ (n N : ℕ) (W : ScBanach) (Ct : Set (Fin n → ℝ))
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
    (h : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 → (ScBanach.paramProd (Fin N → ℝ) W).lvl 0)
    (Bh : (Fin n → ℝ) × W.lvl 0 → W.lvl 0)
    (s : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 →
      (ScBanach.paramProd (Fin N → ℝ) W).shift.lvl 0),
    IsPartialQuadrant (ScBanach.const (Fin n → ℝ)) Ct →
    IsBasicGerm Ct G h Bh →
    IsScSmoothGerm (F := (ScBanach.paramProd (Fin N → ℝ) W).shift) G s → s 0 = 0 →
    let f : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 → (ScBanach.paramProd (Fin N → ℝ) W).lvl 0 :=
      fun x => h x + (ScBanach.paramProd (Fin N → ℝ) W).toBase 1 (s x)
    ∀ D : (ScBanach.paramProd (Fin n → ℝ) W).lvl 1 →
        (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 →L[ℝ] (ScBanach.paramProd (Fin N → ℝ) W).lvl 0,
      IsSc1GermWith G f D → Function.Surjective (D 0) →
      ∀ [FiniteDimensional ℝ (kerOf (D 0))],
      IsInGoodPositionSc (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ) (kerOf (D 0)) →
      ∀ (n' N' : ℕ) (W' : ScBanach) (Ct' : Set (Fin n' → ℝ))
        (U : Set ((ScBanach.paramProd (Fin n → ℝ) W).lvl 0))
        (U' : Set ((ScBanach.paramProd (Fin n' → ℝ) W').lvl 0))
        (Φ : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 × (ScBanach.paramProd (Fin N → ℝ) W).lvl 0 →
          (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0 × (ScBanach.paramProd (Fin N' → ℝ) W').lvl 0)
        (Φ' : (ScBanach.paramProd (Fin n' → ℝ) W').lvl 0 ×
            (ScBanach.paramProd (Fin N' → ℝ) W').lvl 0 →
          (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 × (ScBanach.paramProd (Fin N → ℝ) W).lvl 0),
        IsPartialQuadrant (ScBanach.const (Fin n' → ℝ)) Ct' →
        IsRelOpenInQuadrant (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ) U → 0 ∈ U →
        U ⊆ G.U 0 →
        IsRelOpenInQuadrant (ScBanach.paramProd (Fin n' → ℝ) W') (Ct' ×ˢ Set.univ) U' →
        IsStrongBundleIso U U' Φ Φ' → IsStrongBundleMap.base Φ 0 = 0 →
        IsRaisedBasic Ct' U' (pushforward Φ Φ' f) →
        Concl (ScBanach.paramProd (Fin n → ℝ) W) (ScBanach.paramProd (Fin N → ℝ) W)
          (ScBanach.paramProd (Fin n' → ℝ) W') (ScBanach.paramProd (Fin N' → ℝ) W')
          (Ct ×ˢ Set.univ) U (Ct' ×ˢ Set.univ) U' f (IsStrongBundleMap.base Φ)
          (pushforward Φ Φ' f)) ∧
  -- (b) Corollary 3.47
  (∀ (n N : ℕ) (W : ScBanach) (Ct : Set (Fin n → ℝ))
    (G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ))
    (h : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 → (ScBanach.paramProd (Fin N → ℝ) W).lvl 0)
    (Bh : (Fin n → ℝ) × W.lvl 0 → W.lvl 0)
    (s : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 →
      (ScBanach.paramProd (Fin N → ℝ) W).shift.lvl 0),
    IsPartialQuadrant (ScBanach.const (Fin n → ℝ)) Ct →
    IsBasicGerm Ct G h Bh →
    IsScSmoothGerm (F := (ScBanach.paramProd (Fin N → ℝ) W).shift) G s → s 0 = 0 →
    let f : (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 → (ScBanach.paramProd (Fin N → ℝ) W).lvl 0 :=
      fun x => h x + (ScBanach.paramProd (Fin N → ℝ) W).toBase 1 (s x)
    ∀ D : (ScBanach.paramProd (Fin n → ℝ) W).lvl 1 →
        (ScBanach.paramProd (Fin n → ℝ) W).lvl 0 →L[ℝ] (ScBanach.paramProd (Fin N → ℝ) W).lvl 0,
      IsSc1GermWith G f D → Function.Surjective (D 0) →
      ∀ [FiniteDimensional ℝ (kerOf (D 0))],
      IsInGoodPositionSc (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ) (kerOf (D 0)) →
      LocalGraphRep (ScBanach.paramProd (Fin n → ℝ) W) (ScBanach.paramProd (Fin N → ℝ) W)
        (Ct ×ˢ Set.univ) (G.U 0) f (kerOf (D 0))) ∧
  -- (c) Theorem 3.54, step (3)
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
    ∀ (c : StrongBundleChart PX P) (h0 : 0 ∈ c.U) (g : c.φ.model.E.lvl 0 → c.F.lvl 0)
      (s : c.φ.model.E.lvl 0 → c.F.shift.lvl 0)
      (D : ConjugationData c.U (fun u => g u - c.F.toBase 1 (s u))),
      IsGoodPosData Bd f x c h0 g s →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ c.φ.source ∧
        GraphFormCor c D g (zeroSetIn P f V))

end RoundTrip.V3_77
