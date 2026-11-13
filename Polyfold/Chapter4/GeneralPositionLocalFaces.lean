import Polyfold.Chapter4.LocalStructure
import Polyfold.Chapter2.TameBoundary

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.2,
**Theorem 4.2.11 (1)** (p. 190; preprint Theorem 4.22 (1)), with (2) and (3) on the same
neighbourhood.

# Local faces in Theorem 4.2.11 (1)

## The text

Let `A` be a smooth submanifold of the tame M-polyfold `X`, in general position at `x ∈ A`.  Then
there is an open neighbourhood `U ⊆ X` of `x` on which: (1) there are precisely `d = d_X(x)` local
faces `F_1, …, F_d` contained in `U` and containing `x`; (2) `d_X(a) = d_A(a)` for `a ∈ A ∩ U`;
(3) `A` is in general position at every `a ∈ A ∩ U`.

The local faces at `x` are, as recalled before Proposition 2.5.16 (p. 62), the faces of a small
open `U ∋ x` containing `x`: the closures in `U` of the connected components of
`U ∩ {d_X = 1}` (Definition 2.5.10 for `U`).

## What is formalized

* `MPolyfold.theorem_4_2_11_one`: an open `U ∋ x` such that the faces of `U` through `x`
  (`TameBoundary.facesThrough P.degIndex U x`, the set `F_X(x, U)` of Definition 2.7.9) number
  exactly `d_X(x)`, each is contained in `U`, and (2), (3) hold on `U`.  In addition `U` is
  face-structured (Definition 2.7.6): every `y ∈ U` lies in exactly `d_X(y)` faces of `U`.

The proof takes the neighbourhood of `theorem_4_2_11_preprint` (which gives (1) for the faces of
the chart model only) and intersects it with an open `D ∋ x` all of whose open subsets are
face-structured (`TameBoundary.exists_nbhd_forall_isFaceStructuredOpen`, from the corner axioms of
`d_X`, `MPolyfold.isCornerIndex_degIndex`).  (2) and (3) are statements about points of `A ∩ U`,
so they survive the shrinking.

(4) of the theorem (intersections of the local faces `F_i` of `U`) is not addressed here; the
project's form of (4) uses faces of the chart (`theorem_4_2_11_preprint`).
-/

open Set

universe u

namespace Polyfold

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **2021 Theorem 4.2.11 (1)–(3)** (p. 190; preprint Theorem 4.22), with (1) in the text's
sense: the local faces at `x` are the faces of the open set `U` (closures in `U` of the
components of `U ∩ {d_X = 1}`), and exactly `d_X(x)` of them contain `x`; each is contained in
`U`.  Also, `U` is face-structured (2021 Definition 2.7.6).  (2): `d_A = d_X` on `A ∩ U`.
(3): `A` is in general position at every point of `A ∩ U`. -/
theorem theorem_4_2_11_one (hP : P.IsTame) {A : Set X} (hA : P.IsSmoothSubmanifold A)
    [ParacompactSpace A] {x : X} (hgp : P.IsGeneralPositionAt A x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      -- (1)
      (TameBoundary.facesThrough P.degIndex U x).encard = P.degIndex x ∧
      (∀ θ ∈ TameBoundary.facesThrough P.degIndex U x, θ ⊆ U) ∧
      (∀ y ∈ U, (TameBoundary.facesThrough P.degIndex U y).encard = P.degIndex y) ∧
      -- (2)
      (∀ a : A, (a : X) ∈ U → (subPolyfold hA.isSubMPolyfold).degIndex a = P.degIndex a) ∧
      -- (3)
      (∀ a ∈ U ∩ A, P.IsGeneralPositionAt A a) := by
  obtain ⟨_ψ, _hψ, _hx, _hψ0, _R, _n, _Wq, _T, _hR, _hC, _hT, U, hU, hxU, _hUs, _h1, _h1', h2, h3,
    _h4⟩ := theorem_4_2_11_preprint hP hA hgp
  obtain ⟨D, hD, hxD, hfs⟩ :=
    TameBoundary.exists_nbhd_forall_isFaceStructuredOpen (P.isCornerIndex_degIndex hP) x
  have hV : TameBoundary.IsFaceStructuredOpen P.degIndex (U ∩ D) :=
    hfs _ (hU.inter hD) inter_subset_right
  refine ⟨U ∩ D, hU.inter hD, ⟨hxU, hxD⟩, hV.2 x ⟨hxU, hxD⟩, ?_, hV.2,
    fun a ha => h2 a ha.1, fun a ha => h3 a ⟨ha.1.1, ha.2⟩⟩
  rintro θ ⟨⟨p, -, -, rfl⟩, -⟩
  exact inter_subset_left

end MPolyfold

end Polyfold
