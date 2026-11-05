import Polyfold
/-! Blind formalization of V3_8 (the text's §3.1, the paragraph after Definition 3.4 and
Proposition 3.5, pp. 64–65). Choices:
- Setting and the notions of Definition 3.4 exactly as in my `RoundTrip/Blind/V3_7.lean` (copied
  here): `E F : ScBanach`, `U` relatively open in the partial quadrant `C`, `0 ∈ U`, a strong
  bundle retraction `R` (project's `IsStrongBundleRetraction`) with tame base retraction and
  `r(0) = 0`; `r = rB R`, `ρ(u) = ρB R u`; `(f, 0)` an sc-smooth section germ of `K → O` given by
  its principal part `𝐟` (`IsSectionGermKB`); "`f` has the filling `g`": my `IsFillingB`
  (Definition 3.4, including that `(g, 0)` is an sc-smooth section germ).  "`f(0) = 0`": `𝐟(0) = 0`.
- Linearizations at `0` (Definition 3.2's derivative at `0 ∈ U₁`, `IsLinAt0B`):
  `Lr = Dr(0) : E₀ → E₀`, `Lg = Dg(0) : E₀ → F₀`, `Lf = D(𝐟 ∘ r)(0) : E₀ → F₀`, and
  `ρ₀ = ρ(0) : F₀ → F₀` (a bounded operator with `ρ₀ w = (R(0, w))₂`).  B quantifies over all such
  operators (they exist and are unique).
- `Tf(0)`, the linearization of the section `f : O → K` at its zero `0`, is the map
  `T₀O = Dr(0)E → K₀ = ρ(0)F`, `v ↦ D(𝐟 ∘ r)(0)v` (the tangent map of a map on a retract is that of
  `𝐟 ∘ r` on `TO`, and `T₀O = Dr(0)E`).  As an operator between the Banach spaces
  `range Lr → range ρ₀` it is `restrictB Lf (range Lr) (range ρ₀) h`; B quantifies over the
  proof `h` that `Lf` maps `range Lr` into `range ρ₀`.
- "in the splittings `E = Dr(0)E ⊕ ker Dr(0)`, `F = ρ(0)F ⊕ ker ρ(0)`": these are splittings
  because `Dr(0)` and `ρ(0)` are projections (B asserts `Lr² = Lr`, `ρ₀² = ρ₀`, presupposed by the
  text).  "`Dg(0) = [[Tf(0), *], [0, C]]`": for `v ∈ Dr(0)E`, `Dg(0)v = Tf(0)v ∈ ρ(0)F` (left
  column); `C`, the `ker ρ(0)`-component of `Dg(0)` on `ker Dr(0)`, is `v ↦ (1 − ρ₀)Lg v`, and is a
  topological linear isomorphism `ker Dr(0) → ker ρ(0)` (bijective, bounded inverse).
- (1) "`Tf(0) : Dr(0)E → ρ(0)F` onto iff `Dg(0)` onto": `Lf(range Lr) ⊇ range ρ₀` iff `Lg` is
  surjective.  (2) "Fredholm" is the classical notion for bounded operators (`IsFredholmB`: finite
  dimensional kernel, closed range, finite dimensional cokernel), index `dim ker − dim coker`
  (`indexB`, an integer); "with equal index": if Fredholm, `ind A = ind Lg`.
- No project definition is used for the linear algebra.  Nothing looks false to me.
-/
namespace RoundTrip.V3_8
open Polyfold Filter Topology

section Fredholm
variable {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V']
  [NormedSpace ℝ V']

/-- The kernel of a bounded operator. -/
def kerB (A : V →L[ℝ] V') : Submodule ℝ V := LinearMap.ker (A : V →ₗ[ℝ] V')

/-- The range of a bounded operator. -/
def rangeB (A : V →L[ℝ] V') : Submodule ℝ V' := LinearMap.range (A : V →ₗ[ℝ] V')

/-- A bounded operator is **Fredholm**: finite dimensional kernel, closed range of finite
codimension. -/
def IsFredholmB (A : V →L[ℝ] V') : Prop :=
  FiniteDimensional ℝ (kerB A) ∧ IsClosed (rangeB A : Set V') ∧
    FiniteDimensional ℝ (V' ⧸ rangeB A)

/-- The index `dim ker A − dim coker A`. -/
noncomputable def indexB (A : V →L[ℝ] V') : ℤ :=
  (Module.finrank ℝ (kerB A) : ℤ) - (Module.finrank ℝ (V' ⧸ rangeB A) : ℤ)

/-- The operator `S → T`, `v ↦ A v`, induced by `A` on subspaces with `A(S) ⊆ T`. -/
def restrictB (A : V →L[ℝ] V') (S : Submodule ℝ V) (T : Submodule ℝ V')
    (h : ∀ v : S, A v ∈ T) : S →L[ℝ] T :=
  (A.comp S.subtypeL).codRestrict T h

end Fredholm

section
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

/-- `x ↦ (x, 𝐟(x))` is an sc-smooth section germ of `K → O` at `0`. -/
def IsSectionGermKB (C U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0)
    (fb : E.lvl 0 → F.lvl 0) : Prop :=
  (∀ᶠ x in 𝓝 (0 : E.lvl 0), x ∈ rB R '' U → ρB R x (fb x) = fb x) ∧
  ∃ G : ScNbhdGerm E C, G.U 0 ⊆ U ∧ IsScSmoothGerm G (fb ∘ rB R)

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

end

/-- Proposition 3.5: if `f(0) = 0` has the filling `g`, then in the splittings
`E = Dr(0)E ⊕ ker Dr(0)`, `F = ρ(0)F ⊕ ker ρ(0)` the operator `Dg(0)` is upper triangular with
diagonal `Tf(0)`, `C` (`C` an isomorphism); `Tf(0)` is onto iff `Dg(0)` is, and Fredholm iff
`Dg(0)` is, with the same index. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0)
    (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (_h0 : (0 : E.lvl 0) ∈ U),
    (IsStrongBundleRetraction.baseRetraction hU hR).IsTame → rB R 0 = 0 →
    ∀ fb g : E.lvl 0 → F.lvl 0, IsSectionGermKB C U R fb → IsFillingB C U R fb g → fb 0 = 0 →
    ∀ (Lr : E.lvl 0 →L[ℝ] E.lvl 0) (Lg Lf : E.lvl 0 →L[ℝ] F.lvl 0)
      (ρ₀ : F.lvl 0 →L[ℝ] F.lvl 0),
      IsLinAt0B U (rB R) Lr → IsLinAt0B U g Lg → IsLinAt0B U (fb ∘ rB R) Lf →
      (∀ w : F.lvl 0, ρ₀ w = ρB R 0 w) →
      -- the splittings: `Dr(0)` and `ρ(0)` are projections
      (Lr.comp Lr = Lr ∧ ρ₀.comp ρ₀ = ρ₀) ∧
      -- first column `(Tf(0), 0)`: on `Dr(0)E`, `Dg(0) = Tf(0)` with values in `ρ(0)F`
      (∀ v ∈ rangeB Lr, Lg v = Lf v ∧ Lg v ∈ rangeB ρ₀) ∧
      -- `C = (1 − ρ(0))Dg(0) : ker Dr(0) → ker ρ(0)` is a topological linear isomorphism
      (Set.BijOn (fun v => Lg v - ρ₀ (Lg v)) (kerB Lr : Set (E.lvl 0))
          (kerB ρ₀ : Set (F.lvl 0)) ∧
        ∃ c : ℝ, ∀ v ∈ kerB Lr, ‖v‖ ≤ c * ‖Lg v - ρ₀ (Lg v)‖) ∧
      -- (1) `Tf(0)` onto iff `Dg(0)` onto
      ((∀ w ∈ rangeB ρ₀, ∃ v ∈ rangeB Lr, Lf v = w) ↔ Function.Surjective Lg) ∧
      -- (2) `Tf(0)` Fredholm iff `Dg(0)` Fredholm, with the same index
      (∀ h : ∀ v : rangeB Lr, Lf v ∈ rangeB ρ₀,
        (IsFredholmB (restrictB Lf (rangeB Lr) (rangeB ρ₀) h) ↔ IsFredholmB Lg) ∧
        (IsFredholmB Lg → indexB (restrictB Lf (rangeB Lr) (rangeB ρ₀) h) = indexB Lg))

end RoundTrip.V3_8
