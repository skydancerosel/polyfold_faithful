import Polyfold.Chapter4.Submanifolds
import Polyfold.Chapter9.Symmetric

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §4.2, **Remark 4.2.2**
(p. 184; preprint: Remark 4.14, p. 157): **the local form near `{d_X = 0}`**.  Closes gap G.33
and the narrowing of row V4.32 (Findings, Chapter 4, item 61).

# Remark 4.2.2 near the points with `d_X = 0`

## The text, paraphrased

(Remark 4.2.2; preprint Remark 4.14) A smooth finite-dimensional submanifold `A ⊆ X` is, near the
points `a ∈ A` with `d_X(a) = 0` (preprint), a smooth finite-dimensional manifold in the classical
sense.  The 2021 edition states it near the points with `d_A(a) = 0`, and adds a manifold with
boundary near `d_A(a) = 1`.

## What is formalized

* `MPolyfold.remark_4_2_2_interior`: for a smooth finite-dimensional submanifold `A`
  (Definition 4.2.1, `IsSmoothSubmanifold`), the open piece `A ∩ {d_X = 0}` is a smooth
  finite-dimensional submanifold, and its induced M-polyfold structure has a corner structure
  (Definition 4.1.1, `HasCornerStructure`).  No tameness of `X` is used.
* `MPolyfold.remark_4_2_2_near`: the pointwise form: every `a ∈ A` with `d_X(a) = 0` has an open
  neighbourhood `U` such that `A ∩ U` is a smooth finite-dimensional submanifold with a corner
  structure.

## What the text leaves implicit, and the choices made

* "Near `a`" is read as "on an open neighbourhood `U` of `a` in `X`, for `A ∩ U`"; the
  neighbourhood is `U = {d_X = 0}`, open because `d_X` is upper semicontinuous
  (`MPolyfold.isOpen_interior`).
* "A smooth manifold in the classical sense" is read, as in `hasCornerStructure_of_degIndex_eq_zero`
  (the global form, row V4.32), as the corner structure of Definition 4.1.1 on the induced
  structure: in charts recentred at the points of `A ∩ U`, the partial quadrant is the whole space.
* The 2021 wording with `d_A(a) = 0` in place of `d_X(a) = 0` (stronger, since `d_A ≤ d_X`) and the
  sentence on `d_A(a) = 1` are not covered here.
-/

open Set

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **2021 Remark 4.2.2, p. 184, on the open piece `A ∩ {d_X = 0}`** (preprint: Remark 4.14,
p. 157): for a smooth finite-dimensional submanifold `A` of an M-polyfold `X`, `A ∩ {d_X = 0}` is a
smooth finite-dimensional submanifold whose induced M-polyfold structure has a corner structure
(Definition 4.1.1).  From `IsSmoothSubmanifold.inter_isOpen` and
`hasCornerStructure_of_degIndex_eq_zero`; no tameness. -/
theorem remark_4_2_2_interior {A : Set X} (hA : P.IsSmoothSubmanifold A) :
    ∃ hA₀ : P.IsSmoothSubmanifold (A ∩ {x | P.degIndex x = 0}),
      haveI := P.paracompactSpace_subtype (A ∩ {x | P.degIndex x = 0})
      (subPolyfold hA₀.isSubMPolyfold).HasCornerStructure := by
  have hA₀ := hA.inter_isOpen P.isOpen_interior
  have := P.paracompactSpace_subtype (A ∩ {x | P.degIndex x = 0})
  exact ⟨hA₀, hasCornerStructure_of_degIndex_eq_zero hA₀ fun a ha => ha.2⟩

/-- **2021 Remark 4.2.2, p. 184, near a point with `d_X(a) = 0`** (preprint: Remark 4.14,
p. 157): every point `a` with `d_X(a) = 0` (in particular every such point of `A`) has an open
neighbourhood `U` such that `A ∩ U` is a smooth finite-dimensional submanifold with a corner
structure on its induced M-polyfold structure (`U = {d_X = 0}`). -/
theorem remark_4_2_2_near {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : X}
    (h0 : P.degIndex a = 0) :
    ∃ U : Set X, IsOpen U ∧ a ∈ U ∧ ∃ hAU : P.IsSmoothSubmanifold (A ∩ U),
      haveI := P.paracompactSpace_subtype (A ∩ U)
      (subPolyfold hAU.isSubMPolyfold).HasCornerStructure := by
  obtain ⟨hA₀, hC⟩ := remark_4_2_2_interior hA
  exact ⟨{x | P.degIndex x = 0}, P.isOpen_interior, h0, hA₀, hC⟩

end MPolyfold

end Polyfold
