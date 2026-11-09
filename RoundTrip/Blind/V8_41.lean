import Polyfold
/-! Blind formalization of V8_41 (the 2017 book, arXiv 1707.08941, Part II, §8.5.1, Lemma 8.11 and
the paragraph before it, p. 287; 2021: Lemma 8.6.3).

Text: given a proper covering functor `F : Y → X` and isomorphic `x`, `x'`, with the
decompositions of `F⁻¹(x)` and `F⁻¹(x')` of Lemma 8.6.2: `#Θ_j = #Θ'_j` for every `j = 1, …, q`;
in particular `#F⁻¹(x) = Σ_j #Θ_j = Σ_j #Θ'_j = #F⁻¹(x')`.  Before the lemma: for `y₀ ∈ Θ_j` and
`y₀' ∈ Θ'_j`, `#G_{y₀} = #G_{y₀'}`, and `#G_x = #G_{x'}`; with the third claim of Lemma 8.6.1,
`#Θ_j = #G_x / #G_{y₀} = #G_{x'} / #G_{y₀'} = #Θ'_j`.

Choices:
- Setting as in my `RoundTrip/Blind/V8_38.lean`: spaces in `Type`, Hausdorff paracompact, the
  project's `EpGroupoid`, `EpFunctor`, `EpFunctor.IsProperCovering` (= Definition 8.5.1).
- "The decompositions of Lemma 8.6.2": `Θ : Fin q → Set`, `Θ' : Fin q → Set` decompositions of
  `F⁻¹(x)`, `F⁻¹(x')` into isomorphism classes (`IsIsoClassDecompB`, as in V8_38/V8_40) such that
  isomorphic `y ∈ F⁻¹(x)`, `y' ∈ F⁻¹(x')` lie in `Θ_j`, `Θ'_j` for a unique `j`; these are
  hypotheses (any such pair of decompositions).
- `#` is `Set.ncard`; `G_x` is the set `isoSetB` of morphisms `x → x`; the quotient
  `#G_x / #G_{y₀}` is natural-number division (exact here).
- B: the lemma (`#Θ_j = #Θ'_j`, `#F⁻¹(x) = #F⁻¹(x')`), the two sums of the "in particular"
  chain, and the three claims of the paragraph before it.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_41
open Polyfold

/-- `G_x` as a set of morphisms. -/
def isoSetB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (x : Obj) : Set Mor :=
  {g | G.src g = x ∧ G.tgt g = x}

/-- `y ≅ y'`: there is a morphism `y → y'`. -/
def IsoB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (y y' : Obj) : Prop :=
  ∃ φ : Mor, G.src φ = y ∧ G.tgt φ = y'

/-- `S = Θ₁ ⊔ ⋯ ⊔ Θ_q` is the decomposition of `S` into isomorphism classes. -/
def IsIsoClassDecompB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (S : Set Obj) {q : ℕ}
    (Θ : Fin q → Set Obj) : Prop :=
  (∀ j, (Θ j).Nonempty) ∧ (∀ j, Θ j ⊆ S) ∧ (⋃ j, Θ j) = S ∧
  Pairwise (fun i j => Disjoint (Θ i) (Θ j)) ∧
  ∀ j, ∀ y ∈ Θ j, ∀ y' ∈ S, (y' ∈ Θ j ↔ IsoB G y y')

/-- Lemma 8.6.3: with corresponding decompositions `Θ`, `Θ'` of `F⁻¹(x)`, `F⁻¹(x')` (`x ≅ x'`),
`#Θ_j = #Θ'_j` and `#F⁻¹(x) = Σ #Θ_j = Σ #Θ'_j = #F⁻¹(x')`; moreover `#G_{y₀} = #G_{y₀'}` for
`y₀ ∈ Θ_j`, `y₀' ∈ Θ'_j`, `#G_x = #G_{x'}` and `#Θ_j = #G_x / #G_{y₀}`. -/
def B : Prop :=
  ∀ (ObjY MorY ObjX MorX : Type)
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX) (F : EpFunctor Y X),
    F.IsProperCovering → ∀ x x' : ObjX, IsoB X.toGroupoidStr x x' →
      ∀ (q : ℕ) (Θ Θ' : Fin q → Set ObjY),
        IsIsoClassDecompB Y.toGroupoidStr (F.obj ⁻¹' {x}) Θ →
        IsIsoClassDecompB Y.toGroupoidStr (F.obj ⁻¹' {x'}) Θ' →
        (∀ y ∈ F.obj ⁻¹' {x}, ∀ y' ∈ F.obj ⁻¹' {x'}, IsoB Y.toGroupoidStr y y' →
          ∃! j : Fin q, y ∈ Θ j ∧ y' ∈ Θ' j) →
        -- the lemma
        (∀ j, (Θ j).ncard = (Θ' j).ncard) ∧
        (F.obj ⁻¹' {x}).ncard = ∑ j, (Θ j).ncard ∧
        ∑ j, (Θ' j).ncard = (F.obj ⁻¹' {x'}).ncard ∧
        (F.obj ⁻¹' {x}).ncard = (F.obj ⁻¹' {x'}).ncard ∧
        -- the paragraph before the lemma
        (∀ j, ∀ y₀ ∈ Θ j, ∀ y₀' ∈ Θ' j,
          (isoSetB Y.toGroupoidStr y₀).ncard = (isoSetB Y.toGroupoidStr y₀').ncard) ∧
        (isoSetB X.toGroupoidStr x).ncard = (isoSetB X.toGroupoidStr x').ncard ∧
        (∀ j, ∀ y₀ ∈ Θ j,
          (Θ j).ncard = (isoSetB X.toGroupoidStr x).ncard / (isoSetB Y.toGroupoidStr y₀).ncard)

end RoundTrip.V8_41
