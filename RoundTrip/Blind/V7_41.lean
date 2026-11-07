import Polyfold
/-! Blind formalization of V7_41 (the text's §7.2, p. 244, and Definition 7.13, p. 244; the
2017 book, arXiv 1707.08941, Part II).

Text: for an ep-groupoid `X` and its reduced ep-groupoid `X_R` the object spaces are the same,
the morphism spaces differ; for `x ∈ X` the isotropy group of `x` in `X_R` is `G_x/T_x`.
Definition 7.13: `G_x/T_x` is the effective isotropy group `G^eff_x`.

Choices:
- Setting: an arbitrary ep-groupoid `X : EpGroupoid Obj Mor` (vocabulary, Definition 7.3),
  `Obj Mor : Type` (universe 0), and an object `x`.
- `G_x`: `X.Isotropy x` with its group structure (product = composition, `1 = 1_x`, inverse =
  `ι`; checked by `rfl`).  `T_x` ("defined before Definition 7.12"): the vocabulary's
  `X.trivialSubgroup x` (carrier `trivialSet x`, the `g` acting trivially, i.e. `Φ(g) = id` on
  `U` for a natural representation), trusted from its docstring and `#print`.
- The isotropy group of `x` in `X_R`: the isotropy group of `x` in the groupoid
  `X.reducedGroupoidStr` (objects `X`, morphisms `𝐗^R`, descended structure maps).  It only
  depends on the groupoid structure, so no Hausdorff/paracompact hypothesis on `𝐗^R` (needed for
  `X_R` as an ep-groupoid, see V7_40) is used here.
- "is `G_x/T_x`": read as the natural identification `g T_x ↦ [g]`.  The quotient group
  presupposes that `T_x` is normal (the text presupposes it); B states it.  B then says that
  `G_x → G^R_x`, `g ↦ [g]` (the vocabulary's `reducedIsotropyHom`, checked by `rfl`) is onto with
  kernel `T_x`, which is "`G^R_x ≅ G_x/T_x` via `g T_x ↦ [g]`".
- Definition 7.13 names this group `G^eff_x`.  The vocabulary's `EffIsotropy x` is
  `G_x ⧸ normalClosure(T_x)`; B adds that it is identified with the isotropy of `x` in `X_R` by
  the same natural map (so that the name refers to `G_x/T_x`).
- "the morphism spaces differ" is a comment, not a claim (for effective `X` they agree up to the
  identification `φ ↦ [φ]`); not formalized.  Nothing looks false to me.
-/
namespace RoundTrip.V7_41
open Polyfold

/-- The isotropy group of `x` in `X_R` is `G_x/T_x`: `T_x` is normal, and `g ↦ [g]` maps `G_x`
onto the isotropy of `x` in `(X, 𝐗^R)` with kernel `T_x`; the effective isotropy group `G^eff_x`
is identified with it through the same map. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (x : Obj),
    (X.trivialSubgroup x).Normal ∧
    Function.Surjective (X.reducedIsotropyHom x) ∧
    (X.reducedIsotropyHom x).ker = X.trivialSubgroup x ∧
    ∃ e : X.EffIsotropy x ≃* X.reducedGroupoidStr.Isotropy x,
      ∀ g : X.Isotropy x,
        e (QuotientGroup.mk g : X.EffIsotropy x) = X.reducedIsotropyHom x g

end RoundTrip.V7_41
