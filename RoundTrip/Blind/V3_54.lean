import Polyfold
/-! Blind formalization of V3_54 (the text's §3.7, Lemma 3.61, p. 118; quoted from [25,
Proposition 4.8]). Choices:
- Setting: `G : Type` a finite-dimensional real normed space with the constant sc-structure
  (`ScBanach.const G`), `C_G ⊆ G` a partial quadrant (`IsPartialQuadrant`), `V ⊆ G` relatively
  open in `C_G` (`IsRelOpenInQuadrant`); `E`, `F` arbitrary sc-Banach spaces.  Spaces in `Type`
  (the project's `ScBanach.paramProd` takes `P : Type`); nothing depends on the universe.
- "a family `v ↦ L(v)` of sc-isomorphisms `E → F`": `L : G → ScIso E F` (Definition 1.3, the
  project's `ScIso`: level-wise continuous linear equivalences compatible with the inclusions);
  only the values at `v ∈ V` enter.  (If `V` is nonempty the family on `V` extends to `G` by a
  junk value, so nothing is lost by taking a total family.)  `L(v)h = (L v).lvl 0 h`, and
  `L(v)⁻¹k = (L v).symm.lvl 0 k`.
- "`(v, h) ↦ L(v)h` sc-smooth": sc-smooth (`IsScSmooth`, Definition 1.15) on `V ⊕ E`, i.e. on the
  set `V × E₀` of `(G ⊕ E)₀ = G × E₀` (`ScBanach.paramProd G E`), into `F`.  The conclusion is
  the same for `(v, k) ↦ L(v)⁻¹k` on `V ⊕ F ⊆ G ⊕ F`, into `E`.
- "`|L(v)h|_m ≥ c_m|h|_m` for `v ∈ V`, `h ∈ E_m`": for every level `m` there is `c_m > 0` with
  this bound on level `m` (`(L v).lvl m`).  The remark "operator-norm continuity of `v ↦ L(v)` is
  not assumed" is a comment on the hypotheses (none is added), not a claim.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_54
open Polyfold

/-- Lemma 3.61: if `(v, h) ↦ L(v)h` is sc-smooth on `V ⊕ E` and the sc-isomorphisms `L(v)` satisfy
uniform lower bounds `|L(v)h|_m ≥ c_m|h|_m` on every level, then `(v, k) ↦ L(v)⁻¹k` is sc-smooth
on `V ⊕ F`. -/
def B : Prop :=
  ∀ (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (CG V : Set G) (E F : ScBanach) (L : G → ScIso E F),
    IsPartialQuadrant (ScBanach.const G) CG →
    IsRelOpenInQuadrant (ScBanach.const G) CG V →
    IsScSmooth (E := ScBanach.paramProd G E) (F := F) (V ×ˢ Set.univ)
      (fun p => (L p.1).lvl 0 p.2) →
    (∀ m : ℕ, ∃ c > 0, ∀ v ∈ V, ∀ h : E.lvl m, c * ‖h‖ ≤ ‖(L v).lvl m h‖) →
    IsScSmooth (E := ScBanach.paramProd G F) (F := E) (V ×ˢ Set.univ)
      (fun p => (L p.1).symm.lvl 0 p.2)

end RoundTrip.V3_54
