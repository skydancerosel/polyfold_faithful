import Polyfold.Chapter2.LocalTopologyExample

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, Chapter 2, §2.1:
**Remark 2.1.6** (p. 23, new in the 2021 edition), in one statement.

# Remark 2.1.6 in book form

## The text, paraphrased

(Remark 2.1.6, p. 23) The condition `cl_X(V(x)) ⊆ W(x)` of Definition 2.1.5 is global.  Replacing
`cl_X(V(x))` by the closure `cl_{W(x)}(V(x))` of `V(x)` in `W(x)` would make the definition weaker,
since `cl_X(V(x)) ⊆ W(x)` implies `cl_{W(x)}(V(x)) = cl_X(V(x))`.

## What is formalized

* `remark_2_1_6_book`: the three statements together — the closure identity
  (`remark_2_1_6`), the implication "locally complete ⇒ the modified notion"
  (`IsLocallyComplete.isLocallyCompleteRel`), and its strictness among Hausdorff spaces
  (`remark_2_1_6_strict`, the real line with the K-topology).

## Comments

* The text does not say whether "weaker" is meant strictly; both readings are proved, so the
  statement is the remark with the strict reading added.
-/

open Set

namespace Polyfold

universe u

/-- **2021 Remark 2.1.6, p. 23** (new in the 2021 edition), in book form: (a) for `V, W ⊆ X` with
`cl_X(V) ⊆ W`, the closure of `V` in `W` is `cl_X(V)`; (b) hence a locally complete space
(Definition 2.1.5) satisfies the modified definition (closure of `V(x)` taken in `W(x)`); (c) the
modified definition is strictly weaker: some Hausdorff space satisfies it without being locally
complete.  Assembled from `remark_2_1_6`, `IsLocallyComplete.isLocallyCompleteRel` and
`remark_2_1_6_strict`. -/
theorem remark_2_1_6_book :
    (∀ (X : Type u) [TopologicalSpace X] (W V : Set X), closure V ⊆ W →
        Subtype.val '' closure (Subtype.val ⁻¹' V : Set W) = closure V) ∧
      (∀ (X : Type u) [TopologicalSpace X], IsLocallyComplete X → IsLocallyCompleteRel X) ∧
      ∃ (X : Type) (_ : TopologicalSpace X), T2Space X ∧ IsLocallyCompleteRel X ∧
        ¬ IsLocallyComplete X :=
  ⟨fun _ _ _ _ h => remark_2_1_6 h, fun _ _ h => h.isLocallyCompleteRel, remark_2_1_6_strict⟩

end Polyfold
