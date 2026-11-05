import Polyfold
/-! Blind formalization of V2_51 (the text's §2.4, Theorem 2.45, p. 46).

Text: the interior of a face `F` in a tame M-polyfold is an sc-smooth sub-M-polyfold of `X`.  If
`X` is face-structured, every face is a sub-M-polyfold, its induced structure is tame, and
`i : F → X` satisfies `d_X(i(x)) = d_F(x) + 1`.  Every point has a neighbourhood `U` in which each
`y` lies in exactly `d_X(y)` faces of `U`; if `X` is face-structured, each `x` lies in exactly
`d_X(x)` faces of `X` (stated without proof).

Choices:
- Setting: `X : Type` (universe 0, as asked) with `[TopologicalSpace X] [T2Space X]
  [ParacompactSpace X]` and an M-polyfold structure `P : MPolyfold X`; all four claims are made for
  a tame `X` (`P.IsTame`, Definition 2.37, checked with `#print`: an equivalent atlas all of whose
  charts are modelled on tame retracts — a property of the given structure, not "every compatible
  chart is tame").  B is the conjunction of the four claims.
- Faces: `P.IsFace` (Definition 2.39, checked: `F = closure (connectedComponentIn {d_X = 1} x)`
  for some `x` with `d_X(x) = 1`), `d_X = P.degIndex` (Definition 2.22, checked: the minimum of
  `d_C(φ(x))` over the charts compatible with the structure), `P.IsFaceStructured` (checked:
  `#{faces ∋ x} = d_X(x)`, counted with `Set.encard`, so an infinite count is not `0`).
- "The interior of a face `F`": I read it as `F̊ = F ∩ {d_X = 1}` (the points of `F` which are
  not corners of `X`; equivalently the connected component of `{d_X = 1}` whose closure is `F`,
  and, when `F` is an M-polyfold with `d_X = d_F + 1`, its interior `{d_F = 0}`).  This is my
  reading of an undefined phrase; the topological interior of `F` in `X` is empty in general, and
  the interior of `F` relative to `∂X` would make the claim false at a corner where a face meets
  itself.
- "sc-smooth sub-M-polyfold": `P.IsSubMPolyfold` (Definition 2.20, checked: locally the image of
  an sc-smooth retraction `r : V → V` of an open `V`).
- "its induced structure is tame" and `d_F`: the induced structure is the project's
  `P.subPolyfold hF` (Proposition 2.21, the sub-charts `φ|_{W ∩ F}`); it needs paracompactness of
  `F` as an instance, which B asserts together with the sub-M-polyfold property (`F` is closed in
  the metrizable `X`, so this is part of "`F` is an M-polyfold", not an extra claim of substance).
  `d_F` is `(P.subPolyfold hF).degIndex`, and `i` is the inclusion `Subtype.val`.
- "Every point has a neighbourhood `U`": an open `U ∋ x` (it must carry the induced M-polyfold
  structure).  "Faces of `U`" are the faces of the open M-polyfold `U`: closures in `U` of the
  connected components of `{y ∈ U | d_U(y) = 1}`.  I do not build the M-polyfold `U`; I use
  `d_U = d_X` on `U` (the charts of the open subset `U` are the charts of `X` with domain in `U`,
  so the minima agree) and the closure in `U`, `U ∩ closure`.  This is `IsFaceOfOpen` below.
  "Lies in exactly `d_X(y)` faces of `U`": `#{faces of U ∋ y} = d_X(y)` with `Set.encard`.
- The last claim is the definition of "face-structured" and is formalized as stated.
- Nothing looks false to me; the last claim is trivial by definition.
-/
namespace RoundTrip.V2_51
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- The interior `F̊ = F ∩ {d_X = 1}` of a face `F` (my reading). -/
def faceInterior (P : MPolyfold X) (F : Set X) : Set X :=
  F ∩ {x | P.degIndex x = 1}

/-- `G` is a face of the open subset `U` of `X` (with its induced M-polyfold structure, whose
degeneracy index is `d_X` restricted to `U`): the closure in `U` of a connected component of
`{y ∈ U | d_X(y) = 1}`. -/
def IsFaceOfOpen (P : MPolyfold X) (U G : Set X) : Prop :=
  ∃ x ∈ U, P.degIndex x = 1 ∧
    G = U ∩ closure (connectedComponentIn (U ∩ {y | P.degIndex y = 1}) x)

end

/-- Theorem 2.45: interiors of faces of a tame M-polyfold are sub-M-polyfolds; in a
face-structured tame M-polyfold faces are tame sub-M-polyfolds with `d_X = d_F + 1`; locally every
point `y` lies in exactly `d_X(y)` faces of a neighbourhood; in a face-structured `X` every `x`
lies in exactly `d_X(x)` faces. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
    P.IsTame →
      -- the interior of a face is an sc-smooth sub-M-polyfold
      (∀ F : Set X, P.IsFace F → P.IsSubMPolyfold (faceInterior P F)) ∧
      -- face-structured: faces are sub-M-polyfolds, tame, with `d_X(i(x)) = d_F(x) + 1`
      (P.IsFaceStructured → ∀ F : Set X, P.IsFace F →
        ∃ (hF : P.IsSubMPolyfold F) (_ : ParacompactSpace F),
          (P.subPolyfold hF).IsTame ∧
          ∀ x : F, P.degIndex (x : X) = (P.subPolyfold hF).degIndex x + 1) ∧
      -- local face count
      (∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, {G : Set X | IsFaceOfOpen P U G ∧ y ∈ G}.encard = (P.degIndex y : ℕ∞)) ∧
      -- face-structured: global face count
      (P.IsFaceStructured →
        ∀ x : X, {F : Set X | P.IsFace F ∧ x ∈ F}.encard = (P.degIndex x : ℕ∞))

end RoundTrip.V2_51
