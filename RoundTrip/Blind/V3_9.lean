import Polyfold
/-! Blind formalization of V3_9 (the text's §3.1, Definition 3.6, p. 66). Choices:
- This item is a definition (a section germ "has a filling"; "filled version"); no further
  property.  Setting (as in my `RoundTrip/Blind/V3_5.lean`): `X Y : Type`, `PX : MPolyfold X`,
  `P : Y → X` with fibre linear structures as instances, `Bd : StrongBundle PX P`.  The setting of
  the definition, "`(f, x₀)` an sc-smooth section germ", is my `IsScSmoothSectionGermB`
  (Definition 3.3, copied from V3_5), together with: `f` is a section on all of `X` (as the
  project's notions require).
- "a strong bundle chart with `φ(x₀) = 0`": a `StrongBundleChart PX P` of the bundle's (maximal)
  atlas with `x₀` in its domain and `φ(x₀) = 0`.  Since a filling (Definition 3.4) is only
  defined for a *tame* strong local bundle `K → O`, I require the chart to be tame: the project's
  `StrongBundle.IsTameChart` (compatible with the atlas, base retraction tame, Definition 2.34).
  This presupposition is recorded here; it is the reading needed to apply Definition 3.4.
  "In a strong bundle chart" is read existentially.
- "the section germ `Φ ∘ f ∘ φ⁻¹ : O → K` has a filling `g : U → U ◁ F` near `0`": Definition 3.4
  for the chart's local data (`C`, `U`, `R` of the chart; `r(0) = 0` holds as `0 = φ(x₀) ∈ O`) and
  the principal part `𝐟(z) = (Φ(f(φ⁻¹ z)))₂` (`principalB`).  `IsFillingB` is copied from my
  `RoundTrip/Blind/V3_7.lean` (conditions (1)–(3) near `0`, `(g, 0)` an sc-smooth section germ of
  `U ◁ F → U`, i.e. sc-smooth on some sc-germ of neighbourhoods `G` with `G₀ ⊆ U`).
  `IsFilledVersionB c f g`: `(g, 0)` is a filled version in the chart `c`; `HasFillingB`: there is
  a tame chart centred at `x₀` and a filled version in it.
- B: (a) in a tame chart centred at `x₀`, the project's `IsFilledVersion` (local data, `g`
  sc-smooth on the whole `U`) is: `g` sc-smooth on `U` (`IsScSmooth`) and a filled version in my
  sense; (b) `(f, x₀)` has a filling iff some tame chart centred at `x₀` carries a `g` with the
  project's `IsFilledVersion`.  (b) compares the text's germ notion with the project's
  whole-`U` notion.
- Nothing looks false to me.
-/
namespace RoundTrip.V3_9
open Polyfold Filter Topology

section Local
variable {E F : ScBanach}

/-- The base retraction `r(u) = (R(u, 0))₁`. -/
def rB (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0) (u : E.lvl 0) : E.lvl 0 :=
  (R (u, 0)).1

/-- The fibre part `ρ(u)h = (R(u, h))₂`. -/
def ρB (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0) (u : E.lvl 0) (h : F.lvl 0) : F.lvl 0 :=
  (R (u, h)).2

/-- `L : E₀ → F'₀` is the linearization at `0` of `k` on `U`: `|k(h) − k(0) − L h|₀ / |h|₁ → 0`
as `h → 0` in `E₁` with `h ∈ U`. -/
def IsLinAt0B {F' : ScBanach} (U : Set (E.lvl 0)) (k : E.lvl 0 → F'.lvl 0)
    (L : E.lvl 0 →L[ℝ] F'.lvl 0) : Prop :=
  Tendsto (fun h : E.lvl 1 => ‖k (E.toBase 1 h) - k 0 - L (E.toBase 1 h)‖ / ‖h‖)
    (𝓝[E.toBase 1 ⁻¹' U] 0) (𝓝 0)

/-- `y ↦ (y, g(y))` is an sc-smooth section germ of `U ◁ F → U` at `0`. -/
def IsSectionGermUB (C U : Set (E.lvl 0)) (g : E.lvl 0 → F.lvl 0) : Prop :=
  ∃ G : ScNbhdGerm E C, G.U 0 ⊆ U ∧ IsScSmoothGerm G g

/-- `k(y) = [1 − ρ(r(y))]g(y)`. -/
def kB (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0) (g : E.lvl 0 → F.lvl 0) (y : E.lvl 0) :
    F.lvl 0 :=
  g y - ρB R (rB R y) (g y)

/-- **Definition 3.4**: `(g, 0)` is a filling of the section germ `(f, 0)` (principal part `𝐟`). -/
def IsFillingB (C U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0)
    (fb g : E.lvl 0 → F.lvl 0) : Prop :=
  IsSectionGermUB C U g ∧
  (∀ᶠ x in 𝓝 (0 : E.lvl 0), x ∈ rB R '' U → fb x = g x) ∧
  (∀ᶠ y in 𝓝 (0 : E.lvl 0), y ∈ U → g y = ρB R (rB R y) (g y) → y ∈ rB R '' U) ∧
  ∃ (Lr : E.lvl 0 →L[ℝ] E.lvl 0) (Lk : E.lvl 0 →L[ℝ] F.lvl 0),
    IsLinAt0B U (rB R) Lr ∧ IsLinAt0B U (kB R g) Lk ∧
    Set.BijOn Lk {v | Lr v = 0} {w | ρB R 0 w = 0} ∧
    ∃ c : ℝ, ∀ v : E.lvl 0, Lr v = 0 → ‖v‖ ≤ c * ‖Lk v‖

end Local

section Bundle
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The base retraction `r(u) = (R(u, 0))₁` of the chart's strong bundle retraction. -/
def baseB (c : StrongBundleChart PX P) (u : c.φ.model.E.lvl 0) : c.φ.model.E.lvl 0 :=
  (c.R (u, 0)).1

/-- The principal part `𝐟` of `Φ ∘ f ∘ φ⁻¹ (z) = (z, 𝐟(z))`. -/
def principalB (c : StrongBundleChart PX P) (f : X → Y) (z : c.φ.model.E.lvl 0) : c.F.lvl 0 :=
  (c.toPartialEquiv (f (c.φ.toPartialEquiv.symm z))).2

/-- **Definition 3.3** (copied from V3_5): `(f, x₀)` is an sc-smooth section germ. -/
def IsScSmoothSectionGermB (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ (∀ x ∈ V, P (f x) = x) ∧ ContinuousOn f V ∧
    ∃ c : StrongBundleChart PX P, Bd.IsChart c ∧ x₀ ∈ c.φ.source ∧
      c.φ.toPartialEquiv x₀ = 0 ∧
      ∃ G : ScNbhdGerm c.φ.model.E c.φ.model.C,
        (∀ u ∈ G.U 0, u ∈ c.U ∧ c.φ.toPartialEquiv.symm (baseB c u) ∈ V) ∧
        IsScSmoothGerm G (principalB c f ∘ baseB c)

/-- **Definition 3.6**: in the chart `c`, `(g, 0)` is a filled version of `(f, x₀)`: a filling
(Definition 3.4) of the section germ `Φ ∘ f ∘ φ⁻¹ : O → K`. -/
def IsFilledVersionB (c : StrongBundleChart PX P) (f : X → Y)
    (g : c.φ.model.E.lvl 0 → c.F.lvl 0) : Prop :=
  IsFillingB c.φ.model.C c.U c.R (principalB c f) g

/-- **Definition 3.6**: `(f, x₀)` has a filling: in a (tame) strong bundle chart with `φ(x₀) = 0`
the section germ `Φ ∘ f ∘ φ⁻¹` has a filling. -/
def HasFillingB (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X) : Prop :=
  ∃ c : StrongBundleChart PX P, Bd.IsTameChart c ∧ x₀ ∈ c.φ.source ∧
    c.φ.toPartialEquiv x₀ = 0 ∧ ∃ g : c.φ.model.E.lvl 0 → c.F.lvl 0, IsFilledVersionB c f g

end Bundle

/-- Definition 3.6: the project's (local) filled versions are the text's for `g` sc-smooth on `U`,
and `(f, x₀)` has a filling iff some tame chart centred at `x₀` carries a project filled version. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X),
    (∀ x, P (f x) = x) → IsScSmoothSectionGermB Bd f x₀ →
      -- (a) filled versions in a tame chart centred at `x₀`
      (∀ c : StrongBundleChart PX P, Bd.IsTameChart c → x₀ ∈ c.φ.source →
        c.φ.toPartialEquiv x₀ = 0 →
        ∀ (h0 : (0 : c.φ.model.E.lvl 0) ∈ c.U) (g : c.φ.model.E.lvl 0 → c.F.lvl 0),
          (IsFilledVersion c.relOpen c.isRetraction h0 (principalB c f) g ↔
            IsScSmooth c.U g ∧ IsFilledVersionB c f g)) ∧
      -- (b) `(f, x₀)` has a filling
      (HasFillingB Bd f x₀ ↔
        ∃ c : StrongBundleChart PX P, Bd.IsTameChart c ∧ x₀ ∈ c.φ.source ∧
          c.φ.toPartialEquiv x₀ = 0 ∧
          ∃ (h0 : (0 : c.φ.model.E.lvl 0) ∈ c.U) (g : c.φ.model.E.lvl 0 → c.F.lvl 0),
            IsFilledVersion c.relOpen c.isRetraction h0 (principalB c f) g)

end RoundTrip.V3_9
