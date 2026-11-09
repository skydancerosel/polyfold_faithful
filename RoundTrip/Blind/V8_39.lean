import Polyfold
/-! Blind formalization of V8_39 (the 2017 book, arXiv 1707.08941, Part II, §8.5.1, Lemma 8.9 and
its proof, pp. 286–287; 2021: Lemma 8.6.1, pp. 396–398).

Text: for every `j = 1, …, q`, `#G_x · #Θ_j = #{ψ ∈ mor(F⁻¹(x)) | s(ψ), t(ψ) ∈ Θ_j}`; moreover,
for every `j` and `y₀ ∈ Θ_j`, this set has `#G_{y₀} · (#Θ_j)²` elements and
`#G_x = #G_{y₀} · #Θ_j`.  Proof: the map (8.17) of the set to `G_x × Θ_j`, `ψ ↦ (F(ψ), s(ψ))`, is a
bijection by Definition 8.5.1 (3); the set is the disjoint union of the nonempty `mor(y, y')`,
`(y, y') ∈ Θ_j × Θ_j`, each in bijection with `mor(y₀, y₀)`.

Choices:
- Setting as in my `RoundTrip/Blind/V8_38.lean`: spaces in `Type`, Hausdorff paracompact, the
  project's `EpGroupoid`, `EpFunctor`, `EpFunctor.IsProperCovering` (= Definition 8.5.1, checked
  with `#print`).  The ambient hypotheses (a proper covering functor `F : Y → X`, `x ∈ X`,
  `F⁻¹(x) = Θ₁ ⊔ ⋯ ⊔ Θ_q` the isomorphism classes) are those of §8.6.1 (V8.38).
- "For every `j`" / "for every `j` and `y₀ ∈ Θ_j`": every isomorphism class of `F⁻¹(x)` is the
  class `Θ(y₀) = {y ∈ F⁻¹(x) | y₀ ≅ y}` of each of its points `y₀`, so I quantify over
  `y₀ ∈ F⁻¹(x)` and put `Θ_j := Θ(y₀)` (my `classB`); this is equivalent to quantifying over the
  classes and their points.
- `#` is `Set.ncard`; `G_x`, `G_{y₀}` are the sets `isoSetB` of morphisms `x → x`, `y₀ → y₀`;
  `mor(F⁻¹(x))` is `morOnB` (morphisms between points of `F⁻¹(x)`), `mor(y, y')` is `morB`.
- B contains the three claims of the lemma and the two claims of its proof: the bijection (8.17)
  (as `Set.BijOn`), and that every `mor(y, y')`, `y, y' ∈ Θ_j`, is nonempty with
  `#mor(y, y') = #mor(y₀, y₀)`.  The disjointness of the union is a set identity and is not stated.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_39
open Polyfold

/-- `G_x` as a set of morphisms. -/
def isoSetB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (x : Obj) : Set Mor :=
  {g | G.src g = x ∧ G.tgt g = x}

/-- `mor(y, y')`. -/
def morB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (y y' : Obj) : Set Mor :=
  {φ | G.src φ = y ∧ G.tgt φ = y'}

/-- The morphisms between points of `S`. -/
def morOnB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (S : Set Obj) : Set Mor :=
  {φ | G.src φ ∈ S ∧ G.tgt φ ∈ S}

/-- `y ≅ y'`: there is a morphism `y → y'`. -/
def IsoB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (y y' : Obj) : Prop :=
  ∃ φ : Mor, G.src φ = y ∧ G.tgt φ = y'

/-- The isomorphism class of `y₀` in `S`. -/
def classB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (S : Set Obj) (y₀ : Obj) : Set Obj :=
  {y | y ∈ S ∧ IsoB G y₀ y}

/-- Lemma 8.6.1: for the isomorphism class `Θ` of `y₀ ∈ F⁻¹(x)`, with
`M = {ψ ∈ mor(F⁻¹(x)) | s ψ, t ψ ∈ Θ}`: `#G_x · #Θ = #M`, `#M = #G_{y₀} · (#Θ)²`,
`#G_x = #G_{y₀} · #Θ`; (8.17) `M → G_x × Θ` is a bijection; each `mor(y, y')`, `y, y' ∈ Θ`, is
nonempty with `#G_{y₀}` elements. -/
def B : Prop :=
  ∀ (ObjY MorY ObjX MorX : Type)
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX) (F : EpFunctor Y X),
    F.IsProperCovering → ∀ (x : ObjX), ∀ y₀ ∈ F.obj ⁻¹' {x},
      let Θ := classB Y.toGroupoidStr (F.obj ⁻¹' {x}) y₀
      let M := {ψ : MorY | ψ ∈ morOnB Y.toGroupoidStr (F.obj ⁻¹' {x}) ∧
        Y.src ψ ∈ Θ ∧ Y.tgt ψ ∈ Θ}
      -- the lemma
      (isoSetB X.toGroupoidStr x).ncard * Θ.ncard = M.ncard ∧
      M.ncard = (isoSetB Y.toGroupoidStr y₀).ncard * Θ.ncard ^ 2 ∧
      (isoSetB X.toGroupoidStr x).ncard = (isoSetB Y.toGroupoidStr y₀).ncard * Θ.ncard ∧
      -- the proof: (8.17) is a bijection
      Set.BijOn (fun ψ : MorY => (F.mor ψ, Y.src ψ)) M (isoSetB X.toGroupoidStr x ×ˢ Θ) ∧
      -- the proof: every `mor(y, y')`, `y, y' ∈ Θ`, is nonempty and has `#mor(y₀, y₀)` elements
      (∀ y ∈ Θ, ∀ y' ∈ Θ, (morB Y.toGroupoidStr y y').Nonempty ∧
        (morB Y.toGroupoidStr y y').ncard = (morB Y.toGroupoidStr y₀ y₀).ncard)

end RoundTrip.V8_39
