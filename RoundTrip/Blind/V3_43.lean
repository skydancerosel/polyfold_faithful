import Polyfold
/-! Blind formalization of V3_43 (the text's §3.6, Definition 3.48, p. 109: Definition 3.4, the
filling, restated for a tame strong local bundle `K → O`). Choices:
- This item is a definition.  Following the convention of the earlier blind definition files,
  `B` states that the project's notion is the text's one: the project's `IsFilledVersion`
  (whose docstring calls it the local data of Definition 3.6, "fills `f̂` in the sense of
  Definition 3.4") is equivalent to `IsFillingB` below, the text's definition written here.
- Setting: `E`, `F` sc-Banach spaces, `C ⊆ E₀` a partial quadrant, `U` relatively open in `C`
  (`IsRelOpenInQuadrant`), `R` a strong bundle retraction on `U ◁ F` (the project's
  `IsStrongBundleRetraction`, Definition 2.47), `R(u, h) = (r(u), ρ(u)h)` with `r = StrongRetr.r R`,
  `ρ = StrongRetr.ρ R` (project helpers, `(R(u, 0))₁` and `(R(u, h))₂`), `K = R(U ◁ F)`,
  `O = r(U)`.  "Tame strong local bundle": the base retraction `r` is tame
  (`ScRetraction.IsTame` of `baseRetraction`, Definition 2.34).  `0 ∈ U` and `r(0) = 0`.
  No universe choices arise.
- "`(f, 0)` an sc-smooth section germ" of `K → O` (Definition 3.3 in the local model): the
  principal part `f : O → F` (a function on `E₀`, values on `O` near `0` matter) is a section,
  `ρ(y)f(y) = f(y)` for `y ∈ O` near `0`, and `f ∘ r` is an sc-smooth germ (Definition 3.2,
  `IsScSmoothGerm` on some sc-germ of neighbourhoods inside `U`).  This is a hypothesis of `B`
  (the definition is made for such `f`).
- `IsFillingB f g` (Definition 3.4 = 3.48): `(g, 0)` is an sc-smooth section germ of
  `U ◁ F → U` — `g` is an sc-smooth germ on an sc-germ of neighbourhoods `G` of `0` in `C`
  (Definition 3.1: level-wise neighbourhoods `U_m`, which may shrink with `m`), `G₀ ⊆ U` — and
  (1) `f = g` on `O` near `0` (`∀ᶠ y in 𝓝 0`); (2) `y ∈ U` near `0` with `g(y) = ρ(r(y))g(y)` lies
  in `O`; (3) the linearization `Dk(0)` of `k(y) = [1 − ρ(r(y))]g(y)` (`fillDefect`, an sc¹-germ
  on the same `G` with derivative family `Dk`; the derivative at the smooth point `0` is unique),
  restricted to `ker Dr(0)`, is a topological linear isomorphism onto `ker ρ(0)`: there is a
  continuous linear equivalence `ker Dr(0) ≃ ker ρ(0)` agreeing with `Dk(0)`.  `Dr(0)` is the
  project's `scDeriv U r 0` (unique, `r` being sc-smooth); `ρ(0)` is `StrongRetr.ρCLM`.
  "Topological isomorphism" is read on level `0`.
- Doubt (recorded, not adjusted): the text's `(g, 0)` is a germ; I expect the project's
  `IsFilledVersion` (sc-smoothness of `g` on all of `U`) to be strictly stronger than
  `IsFillingB`, so the `←` direction of `B` may fail.
- Nothing in the text looks false to me.
-/
namespace RoundTrip.V3_43
open Polyfold

/-- The map `k(y) = [1 − ρ(r(y))]g(y)` of Definition 3.4 (3). -/
def fillDefect {E F : ScBanach} (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0)
    (g : E.lvl 0 → F.lvl 0) : E.lvl 0 → F.lvl 0 :=
  fun y => g y - StrongRetr.ρ R (StrongRetr.r R y) (g y)

/-- **Definition 3.4 / 3.48**: `(g, 0)` is a filling of the sc-smooth section germ `(f, 0)` of the
tame strong local bundle `K = R(U ◁ F) → O`: `g` is an sc-smooth germ at `0`, (1) `f = g` on `O`
near `0`, (2) zeros of `[1 − ρ(r(·))]g` near `0` lie in `O`, (3) `Dk(0)|_{ker Dr(0)}` is a
topological isomorphism onto `ker ρ(0)`. -/
def IsFillingB {E F : ScBanach} {C U : Set (E.lvl 0)} {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0}
    (_hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R) (h0 : 0 ∈ U)
    (f g : E.lvl 0 → F.lvl 0) : Prop :=
  ∃ G : ScNbhdGerm E C, G.U 0 ⊆ U ∧ IsScSmoothGerm G g ∧
    -- (1) `f = g` on `O` near `0`
    (∀ᶠ y in nhds (0 : E.lvl 0), y ∈ StrongRetr.r R '' U → f y = g y) ∧
    -- (2) `g(y) = ρ(r(y))g(y)` for `y ∈ U` near `0` forces `y ∈ O`
    (∀ᶠ y in nhds (0 : E.lvl 0),
      y ∈ U → g y = StrongRetr.ρ R (StrongRetr.r R y) (g y) → y ∈ StrongRetr.r R '' U) ∧
    -- (3) `Dk(0) : ker Dr(0) → ker ρ(0)` is a topological linear isomorphism
    ∃ Dk : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0, IsSc1GermWith G (fillDefect R g) Dk ∧
      ∃ e : LinearMap.ker (scDeriv U (StrongRetr.r R) 0 : E.lvl 0 →ₗ[ℝ] E.lvl 0) ≃L[ℝ]
          LinearMap.ker (StrongRetr.ρCLM hR h0 : F.lvl 0 →ₗ[ℝ] F.lvl 0),
        ∀ v, (e v : F.lvl 0) = Dk 0 (v : E.lvl 0)

/-- `(f, 0)` is an sc-smooth section germ of `K → O`: a section near `0` (`ρ(y)f(y) = f(y)` on `O`)
whose composite `f ∘ r` is an sc-smooth germ. -/
def IsSectionGermB {E F : ScBanach} {C U : Set (E.lvl 0)}
    (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0) (f : E.lvl 0 → F.lvl 0) : Prop :=
  (∀ᶠ y in nhds (0 : E.lvl 0), y ∈ StrongRetr.r R '' U → StrongRetr.ρ R y (f y) = f y) ∧
    ∃ G : ScNbhdGerm E C, G.U 0 ⊆ U ∧ IsScSmoothGerm G (f ∘ StrongRetr.r R)

/-- Definition 3.48 (= Definition 3.4 for a tame strong local bundle): the project's
`IsFilledVersion` is the text's filling `IsFillingB`, for every sc-smooth section germ `(f, 0)`. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0)
    (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R) (h0 : 0 ∈ U),
    (IsStrongBundleRetraction.baseRetraction hU hR).IsTame → StrongRetr.r R 0 = 0 →
    ∀ f g : E.lvl 0 → F.lvl 0, IsSectionGermB (C := C) (U := U) R f →
      (IsFilledVersion hU hR h0 f g ↔ IsFillingB hU hR h0 f g)

end RoundTrip.V3_43
