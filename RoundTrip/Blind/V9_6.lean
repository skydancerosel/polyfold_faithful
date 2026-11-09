import Polyfold
/-! Blind formalization of V9_6 (the Springer 2021 book, Part II, §9.1, Definition 9.1.6, p. 404;
2017: Definition 9.2, p. 293): closed and compact `Θ`.

Text: `Θ` is closed if `|supp(Θ)|` is closed in `|X|`, compact if `|supp(Θ)|` is a compact
subset of `|X|`.

Choices:
- This item is a definition.  B says that the project's `X.IsClosedBranched Θ` and
  `X.IsCompactBranched Θ` are these notions, for every ep-groupoid and every `Θ : Obj → ℚ` (the
  text defines them for branched ep⁺-subgroupoids; both sides make sense for any function, so I
  state the equivalences for all `Θ`).
- Setting: `Obj Mor : Type` (universe 0), the project's `X : EpGroupoid Obj Mor`.
- `supp(Θ) = {Θ > 0}` (my `suppB`), `|supp(Θ)| = π(supp Θ) ⊆ |X|`, `|X|` the project's
  `X.OrbitSpace` with Mathlib's quotient topology; "closed in `|X|`": `IsClosed`; "compact subset":
  `IsCompact`.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_6
open Polyfold

/-- `supp(Θ) = {x | Θ(x) > 0}`. -/
def suppB {Obj : Type} (Θ : Obj → ℚ) : Set Obj := {x | 0 < Θ x}

/-- Definition 9.1.6: `Θ` is closed iff `|supp Θ|` is closed in `|X|`, compact iff `|supp Θ|`
is compact. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ),
    (X.IsClosedBranched Θ ↔ IsClosed (X.π '' suppB Θ)) ∧
    (X.IsCompactBranched Θ ↔ IsCompact (X.π '' suppB Θ))

end RoundTrip.V9_6
