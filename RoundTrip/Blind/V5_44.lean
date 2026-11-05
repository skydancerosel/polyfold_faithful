import Polyfold
/-! Blind formalization of V5_44 (the text's §5.3, Lemma 5.24, pp. 182–183).

Text: for `τ ∈ T*_xS` there is an sc⁺-section `s` with small support around `x`, `s(x) = 0` and
`f'(x) ∘ b_τ + (s'(x)|T_xS) = 0`.

Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`.  The objects
  `x`, `S`, `t`, `Z`, `b_τ` are those of Lemma 5.23 (`RoundTrip/Blind/V5_42.lean`, whose
  chart-level definitions I reuse): `f` sc-Fredholm, `t : X → ℝ` sc-smooth
  (`PX.IsScSmoothMap realPolyfold t`), `x` a smooth zero of `f`, `T_xS = ker f'(x)`,
  `Z ⊂ T_xX` a one-dimensional smooth sc-subspace with `T_xX = Z ⊕ ker dt(x)` on every level, and
  `b_τ : T_xS → Z` the (unique) continuous linear map with `dt(x) ∘ b_τ = τ`; B takes `Z`, `τ` and
  `b_τ` as given with these properties.  (The existence of `Z` needs `dt(x) ≠ 0`, the hidden
  hypothesis recorded in V5_42; it is implied by the hypothesis on `Z`.)
- Hypotheses for constructing sc⁺-sections (presupposed: the lemma builds `s` from a bump function
  and an sc⁺-section with a prescribed value at `x`, i.e. Lemma 5.11 / Proposition 5.10): a tame
  strong bundle, `IsTameStrongBundle Bd` (as in `RoundTrip/Blind/V5_38.lean`: `PX.IsTame` and an
  EQUIVALENT strong bundle atlas whose charts have tame base retractions — a property of the given
  structure), and sc-smooth bump functions, read literally as in V5_29 / V5_38: the project's
  `PX.AdmitsBumpFunctionsWeak` (Definitions 5.9/5.29, "`f ≠ 0`" = not identically zero; checked
  in earlier blind files), NOT `AdmitsBumpFunctions` (`f(x) ≠ 0`).  CAVEAT: the construction of
  `s` uses a bump function `β` with `β = 1` near `x` (Proposition 5.10), which the text derives
  from Definition 5.9; under the "not identically zero" reading that derivation is not evident, so
  with this reading B may be harder to prove (or fail) for a reason that lies in Definition 5.9,
  not in Lemma 5.24.  `f` sc-Fredholm in the tame sense, `Bd.IsScFredholmSectionTame f`
  (Definition 3.51), as in V5_38.
- Everything is read in a strong bundle chart `Φ` of `P` around `x` (`Bd.IsChart c`; B quantifies
  over all such charts), as in V5_42: `z ∈ E_1` the lift of `φ(x)`, `T_xX ≅ T_zO = Dr(z)E`,
  `f'(x) ≅ D(f̂ ∘ r)(z)|_{T_zO}`, `s'(x) ≅ D(ŝ ∘ r)(z)|_{T_zO}` (`Dg`; `s(x) = 0`, so `s'(x)` is the
  linearization at a zero), `dt(x) ≅ D(t ∘ φ⁻¹ ∘ r)(z)|_{T_zO}` (`Dt`).
- "sc⁺-section": `Bd.IsScPlusSection s` (Definition 2.52).  "with small support around `x`": for
  every open neighbourhood `V` of `x` there is such an `s` with `supp(s) = cl{s ≠ 0} ⊆ V`.
  `s(x) = 0`: `s x = 0_x`.
- "`f'(x) ∘ b_τ + (s'(x)|T_xS) = 0`": `f'(x)(b_τ(v)) + s'(x)(v) = 0` for every `v ∈ T_xS`.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_44
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

/-- The support `supp(s) = cl{x | s(x) ≠ 0_x}` of a section. -/
def suppB (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (s : X → Y) : Set X :=
  closure {x | s x ≠ ((0 : P ⁻¹' {x}) : Y)}

/-- The tangent space `T_zO = Dr(z)E` of the retract `O = r(U)` at `z ∈ O_1`. -/
noncomputable def TO (c : StrongBundleChart PX P) (z : c.φ.model.E.lvl 1) :
    Submodule ℝ (c.φ.model.E.lvl 0) :=
  LinearMap.range (scDeriv c.U (StrongRetr.r c.R) z).toLinearMap

/-- `D(ĝ ∘ r)(z) : E → F`; on `T_zO` it is the linearization `g'(x)` at a zero. -/
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

/-- Lemma 5.24: for `τ ∈ T*_xS`, with `b_τ : T_xS → Z` from Lemma 5.23, there are sc⁺-sections
`s` with support in any given neighbourhood of `x`, `s(x) = 0` and
`f'(x) ∘ b_τ + s'(x)|T_xS = 0`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (t : X → ℝ) (x : X),
    IsTameStrongBundle Bd → PX.AdmitsBumpFunctionsWeak →
    Bd.IsScFredholmSectionTame f → PX.IsScSmoothMap realPolyfold t →
    x ∈ PX.smoothSet → IsZeroAt P f x →
    ∀ c : StrongBundleChart PX P, Bd.IsChart c → x ∈ c.φ.source →
    ∀ z : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z = c.φ.toPartialEquiv x →
    ∀ Z : Submodule ℝ (c.φ.model.E.lvl 0), SplitsWith c t z Z →
    ∀ (τ : TS c f z →L[ℝ] ℝ) (b : TS c f z →L[ℝ] Z), (∀ v, Dt c t z (b v) = τ v) →
    ∀ V : Set X, IsOpen V → x ∈ V →
      ∃ s : X → Y, Bd.IsScPlusSection s ∧ suppB P s ⊆ V ∧ IsZeroAt P s x ∧
        ∀ v : TS c f z, Dg c f z (b v) + Dg c s z v = 0

end RoundTrip.V5_44
