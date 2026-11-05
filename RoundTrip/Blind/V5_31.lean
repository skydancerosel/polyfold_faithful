import Polyfold
/-! Blind formalization of V5_31 (the text's §5.3, Definition 5.17, p. 177).

Text: `(f, x)`, `f(x) = 0`, is in general position if `f'(x) : T_xX → Y_x` is surjective and
`ker f'(x)` has an sc-complement contained in `T^R_xX`.

Choices:
- This item is a definition.  B says that at every zero `x` of a section `f`, the project's
  `Bd.IsGeneralPositionGerm f x` (Definition 5.17) is the text's notion
  `IsGeneralPositionB Bd f x` written below.  (The text defines the notion only at zeros, so B
  compares the two only there.)
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`, as in
  `RoundTrip/Blind/V5_38.lean`.  No hypothesis on `f` or on the bundle is put into B: the
  definition makes sense for any section; tameness enters through the chart (below).
- "in a tame chart" (the reduced tangent space `T^R_xX` of a tame M-polyfold is computed in a tame
  chart, Definitions 2.27, 2.38): `(f, x)` is in general position if there is a TAME strong bundle
  chart `Φ` of `P` around `x` — a strong bundle chart compatible with the atlas (`Bd.IsChart c`,
  Definition 2.50) whose base retraction `r` is tame (`ScRetraction.IsTame`, Definition 2.34) —
  in which the conditions hold.  (They are chart independent; "some tame chart" is the form in
  which the text computes them.)
- In the chart (as in `RoundTrip/Blind/V5_23.lean`): `φ(x)` lifts to `z ∈ E_1`;
  `T_xX ≅ T_zO = Dr(z)E` (`TO`), `r = StrongRetr.r R`; `Y_x ≅ K_{φ(x)} = {k | (φ(x), k) ∈ K}`;
  `f'(x) ≅ D(f̂ ∘ r)(z)|_{T_zO}` (`Dg`, `f̂` the principal part, `scDeriv` the derivative).
  "Surjective": every `k ∈ K_{φ(x)}` is `Dg(v)` for some `v ∈ T_zO`.
  `ker f'(x) = T_zO ∩ ker Dg` (`kerLin`).
- `T^R_xX ≅ T^R_zO = T_zO ∩ E_{φ(x)}`, where for a presentation `T : E ≅ ℝⁿ ⊕ W` of the partial
  quadrant `C` (`C = T⁻¹([0, ∞)ⁿ ⊕ W)`), `E_p` is the project's `minimalSubspaceWith T p`
  (vocabulary: the `v` with `(Tv)_i = 0` whenever `(Tp)_i = 0`, the text's `E_p`).  `E_p` does not
  depend on the presentation; I require the condition for EVERY presentation (equivalently for
  one).
- "`ker f'(x)` has an sc-complement in `T_xX` contained in `T^R_xX`": a subspace `B ⊆ T^R_zO` which
  is an sc-subspace of `E` (`ScBanach.IsScSubspace`, Definition 1.5: closed, with dense smooth
  points on every level) such that `T_zO = ker f'(x) ⊕ B` on every level `m`
  (`(T_zO)_m = (ker f'(x))_m ⊕ B_m`, levels `A_m = A ∩ E_m` via `ScBanach.levelSub`), i.e. an
  sc-splitting of the sc-space `T_zO`.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_31
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The tangent space `T_zO = Dr(z)E` of the retract `O = r(U)` at `z ∈ O_1`. -/
noncomputable def TO (c : StrongBundleChart PX P) (z : c.φ.model.E.lvl 1) :
    Submodule ℝ (c.φ.model.E.lvl 0) :=
  LinearMap.range (scDeriv c.U (StrongRetr.r c.R) z).toLinearMap

/-- `D(f̂ ∘ r)(z) : E → F`; on `T_zO` it is the linearization at a zero. -/
noncomputable def Dg (c : StrongBundleChart PX P) (g : X → Y) (z : c.φ.model.E.lvl 1) :
    c.φ.model.E.lvl 0 →L[ℝ] c.F.lvl 0 :=
  scDeriv c.U (c.principal g ∘ StrongRetr.r c.R) z

/-- `ker f'(x) = T_zO ∩ ker D(f̂ ∘ r)(z)`. -/
noncomputable def kerLin (c : StrongBundleChart PX P) (g : X → Y) (z : c.φ.model.E.lvl 1) :
    Submodule ℝ (c.φ.model.E.lvl 0) :=
  TO c z ⊓ LinearMap.ker (Dg c g z).toLinearMap

/-- A tame strong bundle chart of `P`: compatible with the atlas, with tame base retraction. -/
def IsTameChartB (Bd : StrongBundle PX P) (c : StrongBundleChart PX P) : Prop :=
  Bd.IsChart c ∧ (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

/-- **Definition 5.17**: `(f, x)` is in general position: in a tame strong bundle chart around
`x`, the linearization `T_zO → K_{φ(x)}` is onto and its kernel has an sc-complement in `T_zO`
contained in the reduced tangent space `T^R_zO = T_zO ∩ E_{φ(x)}`. -/
def IsGeneralPositionB (Bd : StrongBundle PX P) (f : X → Y) (x : X) : Prop :=
  ∃ c : StrongBundleChart PX P, IsTameChartB Bd c ∧ x ∈ c.φ.source ∧
    ∃ z : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z = c.φ.toPartialEquiv x ∧
      -- `f'(x)` is surjective
      (∀ k : c.F.lvl 0, (c.φ.toPartialEquiv x, k) ∈ c.K → ∃ v ∈ TO c z, Dg c f z v = k) ∧
      -- `ker f'(x)` has an sc-complement contained in `T^R_xX`
      ∀ {n : ℕ} {W : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
        c.φ.model.C = T.lvl 0 ⁻¹' quadrant n W 0 →
          ∃ Bc : Submodule ℝ (c.φ.model.E.lvl 0),
            Bc ≤ TO c z ⊓ minimalSubspaceWith T (c.φ.toPartialEquiv x) ∧
            c.φ.model.E.IsScSubspace Bc ∧
            ∀ m : ℕ,
              Disjoint (c.φ.model.E.levelSub (kerLin c f z) m) (c.φ.model.E.levelSub Bc m) ∧
              c.φ.model.E.levelSub (kerLin c f z) m ⊔ c.φ.model.E.levelSub Bc m =
                c.φ.model.E.levelSub (TO c z) m

end

/-- Definition 5.17: at the zeros of a section, the project's general position is the text's. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsZeroAt P f x → (Bd.IsGeneralPositionGerm f x ↔ IsGeneralPositionB Bd f x)

end RoundTrip.V5_31
