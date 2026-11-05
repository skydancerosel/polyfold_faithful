import Polyfold
/-! Blind formalization of V4_49 (the text's §4.2, proof of Theorem 4.22, pp. 162–164).

Text: "In the tame chart with `x = 0`: `A` is the graph `{v + δ(v)}` over `V ⊆ T_0A ∩ C`
(Proposition 4.9); `d_A(a) = d_{T_0A ∩ C}(p(a)) = d_C(a) = d_O(a)`; and 'by means of the particular
form of the map `α`' `T_aA + W = E`, giving (3)."

Choices:
- Context (Theorem 4.22): `X` tame, `A ⊆ X` a smooth finite-dimensional submanifold in general
  position at `x ∈ A`; a tame chart `φ` (model `(O, C, E)` a tame retract) with `φ(x) = 0`.
  `E = ℝⁿ ⊕ W`, `C = [0,∞)ⁿ ⊕ W`: a presentation `T : E ≅ ℝⁿ ⊕ W'` of `C`
  (`C = T⁻¹([0,∞)ⁿ ⊕ W')`); the text's `W ⊆ E` is `T⁻¹({0} ⊕ W')`, the vectors all of whose
  half-line coordinates vanish, i.e. the project's `minimalSubspaceWith T 0` (the coordinates of
  `0` all vanish).  Since `φ(x) = 0`, `n = d_C(0)`.  As the text, I identify points of `A` near `x`
  with their images under `φ`.
- Setting: `X : Type` (universe 0, as in the other blind files of this chapter), Hausdorff,
  paracompact, `P : MPolyfold X`, `P.IsTame` (Definition 2.37).  `A`: the project's
  `IsSmoothSubmanifold` (Definition 4.13), with data `(V, s)` at `x` (`IsScPlusRetractionOn`,
  `s(V) = A ∩ V`) and `V` inside the domain of `φ`; `P.IsChart φ` and `IsTameRetract` for its model
  (Definition 2.34).  "General position at `x`": the project's `IsGeneralPositionAt`
  (Definition 4.21, some chart).  `T_0A = N`, a submodule with underlying set
  `T_0(φ(A ∩ V))` (`tangentSpace`, Definition 2.17, at the level-`1` point `0`).
- What is claimed, as a conjunction (all existentials chosen once):
  * Graph (Proposition 4.9): there are an sc-complement `Y` of `T_0A` with `Y ⊆ W` (the
    complement of the preceding step, item V4_46; it is the kernel of the projection `p` onto
    `T_0A`), an open `Ω ∋ 0` in `E`, a relatively open neighbourhood `Vg` of `0` in `T_0A ∩ C`
    (the text's `V`) and `δ : Vg → Y` with `φ(A ∩ V) ∩ Ω = {v + δ(v) | v ∈ Vg}`.  Smoothness of
    `δ` is not claimed by the item and not stated.
  * `d_A(a) = d_{T_0A ∩ C}(p(a)) = d_C(a) = d_O(a)` for every `a ∈ A ∩ V` with `φ(a) ∈ Ω`; writing
    `φ(a) = v + δ(v)` with `v ∈ Vg` we have `p(φ(a)) = v` (`δ(v) ∈ Y = ker p`), so I write `v` for
    `p(a)`.  `d_A`: degeneracy index of `A` with its induced structure (`subPolyfold`; B asserts
    `A` is a sub-M-polyfold and paracompact, Proposition 4.15).  `d_{T_0A ∩ C}`: the project's
    `degIndex` (Definition 1.23) of the partial quadrant `T_0A ∩ C` in the sc-space `T_0A`
    (`E.ofSubspace`, the induced structure; B asserts `T_0A` is an sc-subspace).  `d_C`: `degIndex`
    of `C` in `E`.  `d_O`: the degeneracy index (Definition 2.22) of the M-polyfold `O`
    (the project's `LocalModel.toMPolyfold`, the retract with its chart `id`).
  * "`T_aA + W = E`": for such `a` and the level-`1` lift `z` of `φ(a)`,
    `T_z(φ(A ∩ V)) + W = E₀` (as submodules, `⊔ = ⊤`); "giving (3)": `A` is in general position at
    `a` (`IsGeneralPositionAt`).  "The map `α`" is not defined in the item; I do not use it.
- Nothing looks false to me.
-/
namespace RoundTrip.V4_49
open Polyfold

/-- Theorem 4.22 in a tame chart centred at `x`: near `0`, `A` is a graph over `T_0A ∩ C` with
values in a complement `Y ⊆ W`; `d_A = d_{T_0A ∩ C} ∘ p = d_C = d_O` on it; `T_aA + W = E`, and `A`
is in general position at these points. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X) (x : X), P.IsTame → P.IsSmoothSubmanifold A → x ∈ A →
    P.IsGeneralPositionAt A x →
    ∀ (V : Set X) (s : X → X) (φ : MChart X) (n : ℕ) (Wq : ScBanach)
      (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
      (N : Submodule ℝ (φ.model.E.lvl 0)),
      P.IsScPlusRetractionOn s V → s '' V = A ∩ V → x ∈ V →
      P.IsChart φ → IsTameRetract φ.model.E φ.model.C φ.model.O →
      V ⊆ φ.toPartialEquiv.source → φ.model.C = T.lvl 0 ⁻¹' quadrant n Wq 0 →
      φ.toPartialEquiv x = 0 →
      -- `N = T_0A`
      (N : Set (φ.model.E.lvl 0)) =
        tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (A ∩ V)) 0 →
      ∃ (hN : φ.model.E.IsScSubspace N) (Y : Submodule ℝ (φ.model.E.lvl 0))
        (Ω Vg : Set (φ.model.E.lvl 0)) (δ : φ.model.E.lvl 0 → φ.model.E.lvl 0),
        -- `E = T_0A ⊕ Y`, `Y ⊆ W`
        φ.model.E.IsScSplitting N Y ∧ Y ≤ minimalSubspaceWith T 0 ∧
        IsOpen Ω ∧ (0 : φ.model.E.lvl 0) ∈ Ω ∧
        -- `Vg` is a relatively open neighbourhood of `0` in `T_0A ∩ C`
        (∃ G : Set (φ.model.E.lvl 0), IsOpen G ∧ Vg = G ∩ ((N : Set _) ∩ φ.model.C)) ∧
        (0 : φ.model.E.lvl 0) ∈ Vg ∧ (∀ v ∈ Vg, δ v ∈ Y) ∧
        -- `A` is the graph `{v + δ(v)}` over `Vg`
        φ.toPartialEquiv '' (A ∩ V) ∩ Ω = (fun v => v + δ v) '' Vg ∧
        ∃ (hA : P.IsSubMPolyfold A) (_ : ParacompactSpace A) (hO : φ.model.O.Nonempty),
          ∀ (a : A) (q : (φ.model.E.ofSubspace hN).lvl 0),
            a.1 ∈ V → φ.toPartialEquiv a.1 ∈ Ω → q.1 ∈ Vg →
            φ.toPartialEquiv a.1 = q.1 + δ q.1 →
              -- `d_A(a) = d_{T_0A ∩ C}(p(a)) = d_C(a) = d_O(a)`
              (P.subPolyfold hA).degIndex a =
                  degIndex (φ.model.E.ofSubspace hN)
                    {w : (φ.model.E.ofSubspace hN).lvl 0 | w.1 ∈ φ.model.C} q ∧
                degIndex (φ.model.E.ofSubspace hN)
                    {w : (φ.model.E.ofSubspace hN).lvl 0 | w.1 ∈ φ.model.C} q =
                  degIndex φ.model.E φ.model.C (φ.toPartialEquiv a.1) ∧
                (∀ o : φ.model.O, o.1 = φ.toPartialEquiv a.1 →
                  degIndex φ.model.E φ.model.C (φ.toPartialEquiv a.1) =
                    (φ.model.toMPolyfold hO).degIndex o) ∧
              -- `T_aA + W = E`
              (∀ (z : φ.model.E.lvl 1) (Na : Submodule ℝ (φ.model.E.lvl 0)),
                φ.model.E.toBase 1 z = φ.toPartialEquiv a.1 →
                (Na : Set (φ.model.E.lvl 0)) =
                  tangentSpace φ.model.E φ.model.C (φ.toPartialEquiv '' (A ∩ V)) z →
                Na ⊔ minimalSubspaceWith T 0 = ⊤) ∧
              -- giving (3): general position at `a`
              P.IsGeneralPositionAt A a

end RoundTrip.V4_49
