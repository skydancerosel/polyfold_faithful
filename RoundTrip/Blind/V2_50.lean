import Polyfold
/-! Blind formalization of V2_50 (the text's §2.4, Proposition 2.44, p. 46).

Text: in a tame M-polyfold every point `x` has `d_X(x)` local faces containing `x`; they are tame
M-polyfolds with `d_F(x) = d_X(x) − 1`.  The intersection `F^σ` of the local faces of
`σ ⊆ 𝓕_x` is a tame M-polyfold of codimension `#σ` with `d_{F^σ}(x) = d_X(x) − #σ` (stated
without proof).

Choices:
- Setting: `X : Type` (universe 0) with `[TopologicalSpace X] [T2Space X] [ParacompactSpace X]`,
  `P : MPolyfold X`, tame: `P.IsTame` (Definition 2.37, checked with `#print`: some atlas
  equivalent to `P.atlas` has all charts modelled on tame retracts — a property of the given
  structure), as in `RoundTrip/Blind/V2_48.lean`, `V2_51.lean`.
- "Local faces at `x`" (my reading of the text's notion): the faces containing `x` of a suitable
  open neighbourhood `V` of `x` (the neighbourhood of Proposition 2.42), with `V` carrying its
  induced M-polyfold structure.  B asserts the existence of one `V` for which all claims hold
  (local faces are germs at `x`; the text does not fix `V`).  `V`'s structure is the project's
  `P.subPolyfold hV` (an open set is a sub-M-polyfold with `r = id`; checked with `#print`: the
  sub-charts `φ|_{W ∩ V}`, i.e. restrictions of charts of `X` to open subsets of `V`), which needs
  `↥V` paracompact as an instance (asserted with `V`; true, `X` is metrizable).  Faces of `V`:
  `MPolyfold.IsFace` (Definition 2.39, checked: closures in `V` of connected components of
  `{d_V = 1}`).  `𝓕_x` is the set of faces of `V` containing `x`; "`x` has `d_X(x)` local faces":
  `𝓕_x.encard = d_X(x)` (`d_X = P.degIndex`, Definition 2.22).
- "They are tame M-polyfolds": a local face `G ⊆ V` is a sub-M-polyfold (Definition 2.20, the
  project's `IsSubMPolyfold`, checked: locally the image of an sc-smooth retraction of an open
  set), and with the induced structure `subPolyfold` (Proposition 2.21) it is tame.  I state this
  for `Subtype.val '' G ⊆ X`, as a sub-M-polyfold of `X` (Definition 2.20 is local and `V` is open,
  so this is the same as being one of `V`, with the same induced charts up to equivalence).  The
  instance `ParacompactSpace` of the subtype is asserted alongside (as in `V2_51.lean`).
- `d_F(x) = d_X(x) − 1` and `d_{F^σ}(x) = d_X(x) − #σ` are read AT THE POINT `x` (the text writes
  `x`, the base point; for `F^σ` there is no other point named) and written additively,
  `d_F(x) + 1 = d_X(x)`, `d_{F^σ}(x) + #σ = d_X(x)` (integer reading, no truncated subtraction).
  The point `x` of the subtype is any `y` with `y.1 = x`.
- `F^σ = ⋂_{F ∈ σ} F` for `σ ⊆ 𝓕_x` (`⋂₀ σ` in `V`; for `σ = ∅` it is `V`, which satisfies the
  claims trivially, so I do not exclude it).  `#σ` is `σ.ncard`; `σ` is finite because
  `𝓕_x.encard = d_X(x)` is asserted in the same conjunction.
- "Codimension `#σ`" is not defined in the text's statement.  My reading (`HasCodimAtB`):
  `F^σ` is cut out near `x` by a closed linear subspace of codimension `#σ` in some chart: there
  are a chart `φ` of `X` (`P.IsChart`, the maximal atlas) with model `(O, C, E)`, an open
  `W ∋ x` inside the domain of `φ` and a closed subspace `L ⊆ E₀` with `dim E₀/L = #σ`
  (`Module.rank`), such that `φ(F^σ ∩ W) = φ(W) ∩ L`.  (In a chart modelled on a tame retract,
  `L` is the intersection `f_σ` of the extended faces of the coordinates of `σ`.)  A tangent-space
  reading (`T_yF^σ` of codimension `#σ` in `T_yX`) would be an alternative.
- Nothing looks false to me.
-/
namespace RoundTrip.V2_50
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- `A ⊆ X` has codimension `k` at `x`: in some chart `φ : V → O ⊆ E` around `x`, near `x`, it is
cut out of `X` by a closed linear subspace `L ⊆ E₀` of codimension `k`. -/
def HasCodimAtB (P : MPolyfold X) (A : Set X) (x : X) (k : ℕ) : Prop :=
  ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ φ.source ∧
      ∃ L : Submodule ℝ (φ.model.E.lvl 0), IsClosed (L : Set (φ.model.E.lvl 0)) ∧
        Module.rank ℝ (φ.model.E.lvl 0 ⧸ L) = k ∧
        φ.toPartialEquiv '' (A ∩ W) = φ.toPartialEquiv '' W ∩ L

end

/-- Proposition 2.44: in a tame M-polyfold, `x` has exactly `d_X(x)` local faces (faces through
`x` of a neighbourhood `V`); each is a tame M-polyfold with `d_F(x) = d_X(x) − 1`; and the
intersection `F^σ` of `σ ⊆ 𝓕_x` is a tame M-polyfold of codimension `#σ` with
`d_{F^σ}(x) = d_X(x) − #σ`. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
    P.IsTame →
      ∀ x : X, ∃ (V : Set X) (_ : IsOpen V) (hxV : x ∈ V) (hV : P.IsSubMPolyfold V)
        (_ : ParacompactSpace V),
        -- `x` has `d_X(x)` local faces
        {G : Set V | (P.subPolyfold hV).IsFace G ∧ (⟨x, hxV⟩ : V) ∈ G}.encard =
            (P.degIndex x : ℕ∞) ∧
        -- each local face is a tame M-polyfold with `d_F(x) = d_X(x) − 1`
        (∀ G : Set V, (P.subPolyfold hV).IsFace G → (⟨x, hxV⟩ : V) ∈ G →
          ∃ (hG : P.IsSubMPolyfold (Subtype.val '' G))
            (_ : ParacompactSpace (Subtype.val '' G)),
            (P.subPolyfold hG).IsTame ∧
            ∀ y : Subtype.val '' G, y.1 = x → (P.subPolyfold hG).degIndex y + 1 = P.degIndex x) ∧
        -- `F^σ` is a tame M-polyfold of codimension `#σ` with `d_{F^σ}(x) = d_X(x) − #σ`
        (∀ σ : Set (Set V),
          σ ⊆ {G : Set V | (P.subPolyfold hV).IsFace G ∧ (⟨x, hxV⟩ : V) ∈ G} →
          ∃ (hA : P.IsSubMPolyfold (Subtype.val '' ⋂₀ σ))
            (_ : ParacompactSpace (Subtype.val '' ⋂₀ σ)),
            (P.subPolyfold hA).IsTame ∧
            HasCodimAtB P (Subtype.val '' ⋂₀ σ) x σ.ncard ∧
            ∀ y : Subtype.val '' ⋂₀ σ, y.1 = x →
              (P.subPolyfold hA).degIndex y + σ.ncard = P.degIndex x)

end RoundTrip.V2_50
