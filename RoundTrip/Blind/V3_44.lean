import Polyfold
/-! Blind formalization of V3_44 (the text's §3.6, Remark 3.49, p. 109). Choices:
- Setting and the notion of filling: exactly as in my V3_43 (Definition 3.48), whose
  definitions `fillDefect`, `IsFillingB`, `IsSectionGermB` are copied here: a tame strong local
  bundle `K = R(U ◁ F) → O` (`U` relatively open in the partial quadrant `C`, `R` a strong bundle
  retraction with tame base retraction `r`, `0 ∈ U`, `r(0) = 0`), an sc-smooth section germ
  `(f, 0)` of `K → O` (principal part `f`), and a filling `(g, 0)` in the text's germ sense
  (`IsFillingB`: conditions (1), (2) only near `0`).  No universe choices arise.
- "By replacing `O` by a smaller set": `O` is replaced by `O' = r(U')` for a smaller domain
  `U' ⊆ U` (relatively open in `C`, `0 ∈ U'`) on which `R` is again a strong bundle retraction
  (so `K' = R(U' ◁ F) → O'` is a strong local bundle, the restriction of `K → O`) whose base
  retraction is again tame — i.e. the smaller set is again a setting of Definition 3.48 — and
  `(g, 0)` is still a filling of `(f, 0)` there (`IsFillingB` for `U'`).  (`O' = O ∩ U'` is then a
  relatively open neighbourhood of `0` in `O`.)
- "one may assume ... that (1) holds on all of `O` and (2) for all `y ∈ U`": after the
  replacement, `f = g` on all of `O'`, and every `y ∈ U'` with `g(y) = ρ(r(y))g(y)` lies in `O'`.
- `B` asserts the existence of such a `U'` for every filling.  Nothing looks false to me.
-/
namespace RoundTrip.V3_44
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

/-- Remark 3.49: a filling `(g, 0)` of `(f, 0)` can be made global by shrinking: there is a smaller
tame strong local bundle `R(U' ◁ F) → O' = r(U')` on which `(g, 0)` is still a filling, `f = g` on
all of `O'`, and every `y ∈ U'` with `g(y) = ρ(r(y))g(y)` lies in `O'`. -/
def B : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0)
    (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R) (h0 : 0 ∈ U),
    (IsStrongBundleRetraction.baseRetraction hU hR).IsTame → StrongRetr.r R 0 = 0 →
    ∀ f g : E.lvl 0 → F.lvl 0, IsSectionGermB (C := C) (U := U) R f →
      IsFillingB hU hR h0 f g →
      ∃ U' : Set (E.lvl 0), U' ⊆ U ∧
        ∃ (hU' : IsRelOpenInQuadrant E C U') (hR' : IsStrongBundleRetraction U' R) (h0' : 0 ∈ U'),
          (IsStrongBundleRetraction.baseRetraction hU' hR').IsTame ∧
          IsFillingB hU' hR' h0' f g ∧
          -- (1) on all of `O' = r(U')`
          (∀ y ∈ StrongRetr.r R '' U', f y = g y) ∧
          -- (2) for all `y ∈ U'`
          (∀ y ∈ U', g y = StrongRetr.ρ R (StrongRetr.r R y) (g y) → y ∈ StrongRetr.r R '' U')

end RoundTrip.V3_44
