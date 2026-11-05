import Polyfold
/-! Blind formalization of V3_7 (the text's §3.1, Definition 3.4, p. 64). Choices:
- This item is a definition; the text asserts no further property.  Setting: `E F : ScBanach`,
  `U` relatively open in the partial quadrant `C ⊆ E` (`IsRelOpenInQuadrant E C U`), `0 ∈ U`,
  and a strong bundle retraction `R : U ◁ F → U ◁ F` (the project's `IsStrongBundleRetraction`,
  Definition 2.47, audited in V2_54), a total map `E₀ × F₀ → E₀ × F₀`.  `R(u, h) = (r(u), ρ(u)h)`:
  `r(u) = (R(u, 0))₁` (`rB`), `ρ(u)h = (R(u, h))₂` (`ρB`).  `O = r(U)`, `K = R(U ◁ F)`.
- "tame strong local bundle": the base retraction `r` is tame (the project's
  `ScRetraction.IsTame` of `IsStrongBundleRetraction.baseRetraction`, Definition 2.34); and
  `r(0) = 0`.  These are hypotheses of B (the setting of the definition).
- "`(f, 0)` an sc-smooth section germ of `K → O`" (setting; `IsSectionGermKB`): `f` is given by
  its principal part `𝐟 : E₀ → F₀`, `f(x) = (x, 𝐟(x))`; it is a section of `K` near `0`
  (`ρ(x)𝐟(x) = 𝐟(x)` for `x ∈ O` near `0`, i.e. `(x, 𝐟(x)) ∈ K`), and `𝐟 ∘ r` is an sc-smooth
  germ on some sc-germ of neighbourhoods `G` with `G₀ ⊆ U` (Definition 3.3 in the identity chart;
  `ScNbhdGerm`, `IsScSmoothGerm` are Definitions 3.1/3.2, audited in V3_1/V3_2).
- "`(g, 0)` an sc-smooth section germ of `U ◁ F → U`": `g : E₀ → F₀` (the section `y ↦ (y, g(y))`)
  is an sc-smooth germ on some `G` with `G₀ ⊆ U`.  This is part of my `IsFillingB`.
- (1) "`f = g` on `O` near `0`": `𝐟(x) = g(x)` for `x ∈ O` in a neighbourhood of `0` in `E₀`.
  (2) for `y ∈ U` near `0`, `g(y) = ρ(r(y))g(y)` implies `y ∈ O`.
  (3) the linearization at `0` of `k(y) = [1 − ρ(r(y))]g(y) = g(y) − ρ(r(y))g(y)`: a bounded
  `Lk : E₀ → F₀` with `|k(h) − k(0) − Lk h|₀ / |h|₁ → 0` for `h → 0` in `E₁`, `h ∈ U`
  (Definition 3.2's derivative at `0 ∈ U₁`; `IsLinAt0B`), likewise `Lr = Dr(0)`; "restricted to
  `ker Dr(0)`, a topological linear isomorphism onto `ker ρ(0)`": `Lk` maps `ker Lr` bijectively
  onto `ker ρ(0)` (`Set.BijOn`) with a bounded inverse (`|v| ≤ c|Lk v|` on `ker Lr`).  The
  derivatives are existential; they are unique (`U₁` relatively open in a partial quadrant
  containing `0`, `E₁` dense in `E₀`).
- B: given the setting, an sc-smooth section germ `𝐟` of `K → O` and `g` sc-smooth on `U` (the
  project's `IsScSmooth`, Definition 1.15; the project's `IsFillerOf` omits the smoothness of `g`
  and works on the whole `U`), the project's `IsFillerOf` is equivalent to my `IsFillingB`.
- Nothing looks false to me.
-/
namespace RoundTrip.V3_7
open Polyfold Filter Topology

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
  -- (1) `f = g` on `O` near `0`
  (∀ᶠ x in 𝓝 (0 : E.lvl 0), x ∈ rB R '' U → fb x = g x) ∧
  -- (2) `g(y) = ρ(r(y))g(y)` for `y ∈ U` near `0` forces `y ∈ O`
  (∀ᶠ y in 𝓝 (0 : E.lvl 0), y ∈ U → g y = ρB R (rB R y) (g y) → y ∈ rB R '' U) ∧
  -- (3) `D k(0) : ker Dr(0) → ker ρ(0)` is a topological linear isomorphism
  ∃ (Lr : E.lvl 0 →L[ℝ] E.lvl 0) (Lk : E.lvl 0 →L[ℝ] F.lvl 0),
    IsLinAt0B U (rB R) Lr ∧ IsLinAt0B U (kB R g) Lk ∧
    Set.BijOn Lk {v | Lr v = 0} {w | ρB R 0 w = 0} ∧
    ∃ c : ℝ, ∀ v : E.lvl 0, Lr v = 0 → ‖v‖ ≤ c * ‖Lk v‖

end

/-- Definition 3.4: for a tame strong local bundle with `r(0) = 0`, an sc-smooth section germ `𝐟`
and an sc-smooth `g`, the project's `IsFillerOf` is the text's filling. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0)
    (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E.lvl 0) ∈ U),
    (IsStrongBundleRetraction.baseRetraction hU hR).IsTame → rB R 0 = 0 →
    ∀ fb g : E.lvl 0 → F.lvl 0, IsSectionGermKB C U R fb → IsScSmooth U g →
      (IsFillerOf hU hR h0 fb g ↔ IsFillingB C U R fb g)

end RoundTrip.V3_7
