import Polyfold
/-! Blind formalization of V4_50 (the text's §4.2, Theorem 4.22, p. 162).

Text: let `A` be a smooth submanifold of the tame `X`, in general position at `x`.  There is an
open `U ∋ x` with (1) precisely `d = d_X(x)` local faces `F_1, …, F_d` in `U`; (2)
`d_X(a) = d_A(a)` on `A ∩ U`; (3) general position on `A ∩ U`; (4) for `σ ⊆ {1, …, d}`, `F_σ` is
a tame M-polyfold and `A ∩ F_σ` a tame smooth submanifold of `F_σ` in general position in `F_σ`.

Choices:
- Setting: `X : Type` (universe 0, as in the other blind files of this chapter), Hausdorff,
  paracompact, `P : MPolyfold X` tame (`P.IsTame`, Definition 2.37: an equivalent atlas of charts
  on tame retracts — a property of the given structure).
- "smooth submanifold": the project's `IsSmoothSubmanifold` (Definition 4.13, checked with
  `#print`: every `a ∈ A` has an open `V ∋ a` and an sc⁺-retraction `s : V → V` with
  `s(V) = A ∩ V`).  "In general position at `x`" (Definition 4.21): the project's
  `IsGeneralPositionAt` (checked: in some chart, with some data of Definition 4.13, presentation
  and level-`1` lift, `T_xA` has in `T_xO` an sc-complement inside `T_xO ∩ E_x`); used both as
  the hypothesis at `x` and in (3), (4).
- (1) "precisely `d` local faces `F_1, …, F_d` in `U`": local faces at `x` are the faces of a small
  open neighbourhood of `x` (the faces of the M-polyfold `U`, all passing through `x`).  I read
  (1) as: the faces of `U` are exactly `d_X(x)` sets `F_1, …, F_d` (an injective enumeration
  `F : Fin d → Set X` of them), and every `F_i` contains `x`.  A face of the open set `U`
  (`IsFaceOfOpen`, copied from the blind file V2_51) is the closure in `U` of a connected
  component of `{y ∈ U | d_U(y) = 1}`, with `d_U = d_X` on `U` (the charts of the open
  M-polyfold `U` are the charts of `X` with domain in `U`); `d_X` is the project's `degIndex`
  (Definition 2.22).
- (2) `d_A`: the degeneracy index of `A` with its induced M-polyfold structure (Proposition 4.15:
  `A` is a sub-M-polyfold; the structure is the project's `subPolyfold`, Proposition 2.21).  B
  asserts that `A` is a sub-M-polyfold and paracompact (needed as an instance; true, `A` is
  locally closed in the metrizable `X`) and `d_X(a) = d_A(a)` for every `a ∈ A ∩ U`.
- (3) `A` is in general position at every `a ∈ A ∩ U`.
- (4) `F_σ = ⋂_{i ∈ σ} F_i` for `σ ⊆ {1, …, d}` (a `Finset (Fin d)`; for `σ = ∅` I take
  `F_∅ = U`, i.e. `F_σ = U ∩ ⋂_{i ∈ σ} F_i`).  "`F_σ` is a tame M-polyfold": `F_σ` is a
  sub-M-polyfold of `X` (Definition 2.20, the project's `IsSubMPolyfold`) whose induced structure
  (`subPolyfold`, paracompactness asserted) is tame.  "`A ∩ F_σ` a tame smooth submanifold of
  `F_σ`": the preimage `A' = {a ∈ F_σ | a ∈ A}` of `A` in the subtype `F_σ` satisfies the
  project's `IsTameSubmanifold` for the M-polyfold `F_σ` (Definition 4.17, checked: a smooth
  finite-dimensional submanifold whose induced structure is tame; paracompactness of `A'`
  asserted); "in general position in `F_σ`": `IsGeneralPositionAt` of `A'` in `F_σ` at each point
  of `A'`.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_50
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- `G` is a face of the open subset `U` of `X` (with its induced M-polyfold structure, whose
degeneracy index is `d_X` restricted to `U`): the closure in `U` of a connected component of
`{y ∈ U | d_X(y) = 1}`. -/
def IsFaceOfOpen (P : MPolyfold X) (U G : Set X) : Prop :=
  ∃ x ∈ U, P.degIndex x = 1 ∧
    G = U ∩ closure (connectedComponentIn (U ∩ {y | P.degIndex y = 1}) x)

/-- `F_σ = ⋂_{i ∈ σ} F_i`, inside `U` (`F_∅ = U`). -/
def faceInter {d : ℕ} (U : Set X) (F : Fin d → Set X) (σ : Finset (Fin d)) : Set X :=
  U ∩ ⋂ i ∈ σ, F i

end

/-- Theorem 4.22: near a point `x` at which the smooth submanifold `A` of the tame `X` is in
general position, `X` has exactly `d_X(x)` local faces, `d_X = d_A` on `A`, `A` is in general
position, and on every intersection `F_σ` of local faces (a tame M-polyfold) `A ∩ F_σ` is a tame
submanifold in general position. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X) (x : X),
    P.IsTame → P.IsSmoothSubmanifold A → x ∈ A → P.IsGeneralPositionAt A x →
    ∃ (U : Set X) (F : Fin (P.degIndex x) → Set X),
      IsOpen U ∧ x ∈ U ∧
      -- (1) the faces of `U` are exactly `F_1, …, F_d`, `d = d_X(x)`, all through `x`
      (∀ i, IsFaceOfOpen P U (F i) ∧ x ∈ F i) ∧ Function.Injective F ∧
      (∀ G : Set X, IsFaceOfOpen P U G → ∃ i, G = F i) ∧
      -- (2) `d_X(a) = d_A(a)` on `A ∩ U`
      (∃ (hA : P.IsSubMPolyfold A) (_ : ParacompactSpace A),
        ∀ a : A, a.1 ∈ U → P.degIndex a.1 = (P.subPolyfold hA).degIndex a) ∧
      -- (3) general position on `A ∩ U`
      (∀ a ∈ A ∩ U, P.IsGeneralPositionAt A a) ∧
      -- (4) `F_σ` tame, `A ∩ F_σ` a tame submanifold of `F_σ` in general position
      ∀ σ : Finset (Fin (P.degIndex x)),
        ∃ (hF : P.IsSubMPolyfold (faceInter U F σ)) (_ : ParacompactSpace (faceInter U F σ)),
          (P.subPolyfold hF).IsTame ∧
          (∃ _ : ParacompactSpace (Subtype.val ⁻¹' A : Set (faceInter U F σ)),
            (P.subPolyfold hF).IsTameSubmanifold (Subtype.val ⁻¹' A : Set (faceInter U F σ))) ∧
          ∀ a : faceInter U F σ, a.1 ∈ A →
            (P.subPolyfold hF).IsGeneralPositionAt (Subtype.val ⁻¹' A) a

end RoundTrip.V4_50
