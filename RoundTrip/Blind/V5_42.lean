import Polyfold
/-! Blind formalization of V5_42 (the text's §5.3, Lemma 5.23, p. 182, in the setting of
Theorem 5.22).

Text: "Since `x` is a smooth point, we find a one-dimensional smooth linear sc-subspace
`Z ⊂ T_xX` such that `T_xX = Z ⊕ ker(dt(x))`."  For `τ ∈ T*_xS` there is a unique sc-operator
`b_τ : T_xS → Z` with `dt(x) ∘ b_τ = τ`, and `dt(x) ∘ (b_τ + a) = τ` for `a : T_xS → ker dt(x)`.

Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`, as in
  `RoundTrip/Blind/V5_38.lean`.  `f`: the sc-Fredholm section (the project's
  `Bd.IsScFredholmSection f`, Definition 3.14); `t : X → ℝ` sc-smooth
  (`PX.IsScSmoothMap realPolyfold t`, as in Definition 5.20); `S = S_f` its solution set and
  `x ∈ S` a smooth point (`x ∈ X_∞`, `PX.smoothSet`).  The claims are pointwise linear algebra, so
  I add none of the other hypotheses of the homotopy setting (no tameness, no compactness, no
  surjectivity of `t`).
- Everything is read in a strong bundle chart `Φ` of `P` around `x` (`Bd.IsChart c`), as in
  `RoundTrip/Blind/V5_23.lean`; B quantifies over all such charts.  `φ(x)` lifts to `z ∈ E_1`;
  `T_xX ≅ T_zO = Dr(z)E` (`TO`, `r = StrongRetr.r R` the base retraction);
  `dt(x) ≅ D(t ∘ φ⁻¹ ∘ r)(z)|_{T_zO}` (`Dt`, a continuous functional `E → ℝ`; `scDeriv` with
  target `realSc`, `ℝ` with the constant sc-structure); `ker dt(x) = T_zO ∩ ker Dt` (`KerT`).
- `T_xS`: the tangent space of the solution set, `T_xS = ker f'(x)` (the text's identification,
  proofs of Theorems 5.18, 5.25): `T_zO ∩ ker D(f̂ ∘ r)(z)` (`TS`, `f̂` the principal part).
  `T*_xS`: continuous linear functionals `T_xS → ℝ` (all linear functionals, `T_xS` being
  finite-dimensional).  "sc-operator `T_xS → Z`" between these (finite-dimensional, smooth)
  spaces: a continuous linear map; `b_τ + a` is the sum in `T_xX ⊆ E`.
- "one-dimensional smooth linear sc-subspace `Z ⊂ T_xX` with `T_xX = Z ⊕ ker dt(x)`"
  (`SplitsWith`): `dim Z = 1`, `Z ⊆ E_∞` (`ScScale.smooth`), `Z` an sc-subspace of `E`
  (Definition 1.5), `Z ⊆ T_zO`, and the sum is direct on every level:
  `(T_zO)_m = Z_m ⊕ (ker dt(x))_m` (`ScBanach.levelSub`).
- THE HIDDEN HYPOTHESIS: such a `Z` exists only if `dt(x) ≠ 0` on `T_xX`; "since `x` is a smooth
  point" does not provide it, and the text's hypotheses (Theorem 5.22) do not state it.  B encodes
  it as part (1): for a smooth point, `Z` exists IFF `dt(x) ≠ 0` (`dt(x)v ≠ 0` for some
  `v ∈ T_zO`).  Parts (2), (3) are stated for any such `Z` (whose existence forces `dt(x) ≠ 0`).
  `BLiteral` (NOT the item, only an aid) is the literal claim "`Z` exists at every smooth zero";
  I believe it is false (e.g. at a critical point of `t`).
- (2): for every `τ ∈ T*_xS` there is exactly one `b : T_xS → Z` with `dt(x)(b(v)) = τ(v)` for all
  `v`.  (3): for such `b` and every continuous linear `a : T_xS → ker dt(x)`,
  `dt(x)(b(v) + a(v)) = τ(v)`.
-/
namespace RoundTrip.V5_42
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The tangent space `T_zO = Dr(z)E` of the retract `O = r(U)` at `z ∈ O_1`. -/
noncomputable def TO (c : StrongBundleChart PX P) (z : c.φ.model.E.lvl 1) :
    Submodule ℝ (c.φ.model.E.lvl 0) :=
  LinearMap.range (scDeriv c.U (StrongRetr.r c.R) z).toLinearMap

/-- `D(f̂ ∘ r)(z) : E → F`; on `T_zO` it is the linearization `f'(x)` at a zero. -/
noncomputable def Dg (c : StrongBundleChart PX P) (g : X → Y) (z : c.φ.model.E.lvl 1) :
    c.φ.model.E.lvl 0 →L[ℝ] c.F.lvl 0 :=
  scDeriv c.U (c.principal g ∘ StrongRetr.r c.R) z

/-- `D(t ∘ φ⁻¹ ∘ r)(z) : E → ℝ`; on `T_zO` it is `dt(x)`. -/
noncomputable def Dt (c : StrongBundleChart PX P) (t : X → ℝ) (z : c.φ.model.E.lvl 1) :
    c.φ.model.E.lvl 0 →L[ℝ] ℝ :=
  scDeriv (F := realSc) c.U (fun u => t (c.φ.toPartialEquiv.symm (StrongRetr.r c.R u))) z

/-- `ker dt(x) = T_zO ∩ ker Dt`. -/
noncomputable def KerT (c : StrongBundleChart PX P) (t : X → ℝ) (z : c.φ.model.E.lvl 1) :
    Submodule ℝ (c.φ.model.E.lvl 0) :=
  TO c z ⊓ LinearMap.ker (Dt c t z).toLinearMap

/-- `T_xS = ker f'(x) = T_zO ∩ ker D(f̂ ∘ r)(z)`. -/
noncomputable def TS (c : StrongBundleChart PX P) (f : X → Y) (z : c.φ.model.E.lvl 1) :
    Submodule ℝ (c.φ.model.E.lvl 0) :=
  TO c z ⊓ LinearMap.ker (Dg c f z).toLinearMap

/-- `Z` is a one-dimensional smooth sc-subspace of `T_xX` with `T_xX = Z ⊕ ker dt(x)` on every
level. -/
def SplitsWith (c : StrongBundleChart PX P) (t : X → ℝ) (z : c.φ.model.E.lvl 1)
    (Z : Submodule ℝ (c.φ.model.E.lvl 0)) : Prop :=
  Module.finrank ℝ Z = 1 ∧ Z ≤ c.φ.model.E.toScScale.smooth ∧ c.φ.model.E.IsScSubspace Z ∧
    Z ≤ TO c z ∧
    ∀ m : ℕ, Disjoint (c.φ.model.E.levelSub Z m) (c.φ.model.E.levelSub (KerT c t z) m) ∧
      c.φ.model.E.levelSub Z m ⊔ c.φ.model.E.levelSub (KerT c t z) m =
        c.φ.model.E.levelSub (TO c z) m

end

/-- Lemma 5.23 with its hidden hypothesis: at a smooth zero `x`, a one-dimensional smooth
sc-complement `Z` of `ker dt(x)` in `T_xX` exists iff `dt(x) ≠ 0`; for such `Z` and `τ ∈ T*_xS`
there is a unique `b_τ : T_xS → Z` with `dt(x) ∘ b_τ = τ`, and `dt(x) ∘ (b_τ + a) = τ` for every
`a : T_xS → ker dt(x)`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (t : X → ℝ) (x : X),
    Bd.IsScFredholmSection f → PX.IsScSmoothMap realPolyfold t →
    x ∈ PX.smoothSet → IsZeroAt P f x →
    ∀ c : StrongBundleChart PX P, Bd.IsChart c → x ∈ c.φ.source →
    ∀ z : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z = c.φ.toPartialEquiv x →
      -- (1) `Z` exists iff `dt(x) ≠ 0` (the hidden hypothesis)
      ((∃ Z, SplitsWith c t z Z) ↔ ∃ v ∈ TO c z, Dt c t z v ≠ 0) ∧
      -- (2) existence and uniqueness of `b_τ`
      (∀ Z, SplitsWith c t z Z → ∀ τ : TS c f z →L[ℝ] ℝ,
        ∃! b : TS c f z →L[ℝ] Z, ∀ v, Dt c t z (b v) = τ v) ∧
      -- (3) `dt(x) ∘ (b_τ + a) = τ`
      (∀ Z, SplitsWith c t z Z → ∀ (τ : TS c f z →L[ℝ] ℝ) (b : TS c f z →L[ℝ] Z),
        (∀ v, Dt c t z (b v) = τ v) →
        ∀ (a : TS c f z →L[ℝ] KerT c t z) (v : TS c f z),
          Dt c t z ((b v : c.φ.model.E.lvl 0) + (a v : c.φ.model.E.lvl 0)) = τ v)

/-- Not the item: the literal first sentence, without the hidden hypothesis `dt(x) ≠ 0` (I
believe it is false). -/
def BLiteral : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (t : X → ℝ) (x : X),
    Bd.IsScFredholmSection f → PX.IsScSmoothMap realPolyfold t →
    x ∈ PX.smoothSet → IsZeroAt P f x →
    ∀ c : StrongBundleChart PX P, Bd.IsChart c → x ∈ c.φ.source →
    ∀ z : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z = c.φ.toPartialEquiv x →
      ∃ Z, SplitsWith c t z Z

end RoundTrip.V5_42
