import Polyfold
/-! Blind formalization of V7_32 (the 2017 book's Part II, §7.1, Proposition 7.7 and the argument
before it, pp. 238–239).

Text: let `X` be an ep-groupoid and `A ⊆ X` a saturated subset of the object space which is also
a sub-M-polyfold.  Then the full subcategory associated with `A` has in a natural way the
structure of an ep-groupoid.  In particular `A` and `𝐀 = {φ ∈ 𝐗 | s(φ), t(φ) ∈ A}` are
sub-M-polyfolds of `X` and `𝐗`, and all the structure maps are the restrictions of those of `X`.

Choices:
- Setting: `Obj Mor : Type` (spaces in `Type`; the project's `EpGroupoid` is universe-polymorphic,
  this is `u = 0`), with their topologies, Hausdorff and paracompact, `X : EpGroupoid Obj Mor`
  (the project's Definition 7.3, checked with `#print`: groupoid laws on composable pairs,
  `PObj`, `PMor`, `s`, `t` local sc-diffeomorphisms, `u`, `ι` sc-smooth, properness, `m`
  sc-smooth on `𝐗 ₛ×ₜ 𝐗`), `A ⊆ Obj` with `X.IsSaturated A` (checked: `π⁻¹(π(A)) = A`) and
  `X.PObj.IsSubMPolyfold A` (Definition 2.20, checked with `#print`).
- `𝐀` is `X.morOn A` (checked: `{φ | s φ ∈ A ∧ t φ ∈ A}`); the full subcategory has objects `↥A`
  and morphisms `↥𝐀`, both with the subspace topologies.
- "has the structure of an ep-groupoid": some `Y : EpGroupoid ↥A ↥𝐀` (the project's structure is
  the text's Definition 7.3; paracompactness of `↥A`, `↥𝐀`, needed by its type, is asserted to
  exist, being part of "M-polyfold").
- "in a natural way ... `A` and `𝐀` are sub-M-polyfolds of `X` and `𝐗`": `A`, `𝐀` are
  sub-M-polyfolds (Definition 2.20) and the M-polyfold structures `Y.PObj`, `Y.PMor` are the
  induced ones, characterized by properties (1), (2) of Proposition 2.21 (`IsNaturalSubB`, copied
  from `IsNaturalSubStructureB` of `RoundTrip/Blind/V2_24.lean`: the inclusion is sc-smooth and an
  embedding, and `i⁻¹ ∘ r` is sc-smooth for every sc-smooth retraction `r : V → V` onto the
  subset; these determine the structure up to equivalence of atlases).
- "the structure maps are the restrictions": `s`, `t`, `u`, `ι` of `Y` are those of `X` on the
  underlying points, and so is `m` on composable pairs (`Y.src φ = Y.tgt ψ`; the project's
  `comp` is total, with laws only on composable pairs, so only these values carry meaning).
- Nothing looks false to me.
-/
namespace RoundTrip.V7_32
open Polyfold

/-- Properties (1) and (2) of Proposition 2.21 for the M-polyfold structure `Q` on the subset `A`
(as `IsNaturalSubStructureB` in `RoundTrip/Blind/V2_24.lean`). -/
def IsNaturalSubB {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (P : MPolyfold Z) (A : Set Z) [ParacompactSpace A] (Q : MPolyfold A) : Prop :=
  (Q.IsScSmoothMap P (Subtype.val : A → Z) ∧ Topology.IsEmbedding (Subtype.val : A → Z)) ∧
  (∀ (V : Set Z) (r : Z → Z), IsOpen V → Set.MapsTo r V V → P.IsScSmoothOn P r V →
    (∀ x ∈ V, r (r x) = r x) → r '' V = A ∩ V →
    ∀ g : Z → A, (∀ x ∈ V, (g x : Z) = r x) → P.IsScSmoothOn Q g V)

/-- Proposition 7.7: the full subcategory on a saturated sub-M-polyfold `A` is an ep-groupoid
with the induced sub-M-polyfold structures on `A` and `𝐀` and the restricted structure maps. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (A : Set Obj), X.IsSaturated A → X.PObj.IsSubMPolyfold A →
    -- `A` and `𝐀` are sub-M-polyfolds
    (X.PObj.IsSubMPolyfold A ∧ X.PMor.IsSubMPolyfold (X.morOn A)) ∧
    -- the ep-groupoid structure of the full subcategory
    ∃ (_ : ParacompactSpace A) (_ : ParacompactSpace (X.morOn A))
      (Y : EpGroupoid A (X.morOn A)),
      IsNaturalSubB X.PObj A Y.PObj ∧ IsNaturalSubB X.PMor (X.morOn A) Y.PMor ∧
      (∀ φ : X.morOn A, ((Y.src φ : A) : Obj) = X.src (φ : Mor)) ∧
      (∀ φ : X.morOn A, ((Y.tgt φ : A) : Obj) = X.tgt (φ : Mor)) ∧
      (∀ a : A, ((Y.unit a : X.morOn A) : Mor) = X.unit (a : Obj)) ∧
      (∀ φ : X.morOn A, ((Y.inv φ : X.morOn A) : Mor) = X.inv (φ : Mor)) ∧
      (∀ φ ψ : X.morOn A, Y.src φ = Y.tgt ψ →
        ((Y.comp φ ψ : X.morOn A) : Mor) = X.comp (φ : Mor) (ψ : Mor))

end RoundTrip.V7_32
