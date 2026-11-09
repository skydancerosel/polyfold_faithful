import Polyfold
/-! Blind formalization of V10_49 (the text's Part II, §10.3, Definition 10.3.20, p. 494 of the
Springer 2021 book; new in the 2021 edition).

Text: `EP_reg` and `EP_reg(E⁻¹)` are the full subcategories of `EP` and of `EP(E⁻¹)` on the
ep-groupoids with (LR).

Choices:
- This item is a definition.  Setting: universe 0, the project's categories `EP.{0}` (objects the
  bundled ep-groupoids, morphisms the sc-smooth functors) and `EPLoc.{0}` (`EP(E⁻¹)`, 2021
  Definition 10.3.12: objects the ep-groupoids, morphisms the classes of diagrams); the categories
  `EPreg.{0}` and `EPLocReg.{0}` with the category instances Lean finds on them.
- "(LR)": the project's `EpGroupoid.IsLR` (2021 Definition 7.4.19, read with `#print`: inside every
  open `O ∋ x` a natural representation `U(x)` such that every sc-diffeomorphism `β` of `U(x)` with
  `|β(y)| = |y|` on `U(x)` is `Φ(g)` for some `g ∈ G_x`).  For an object of `EP(E⁻¹)`, (LR) of the
  underlying ep-groupoid (`toEP`).
- "`D` is the full subcategory of `C` on the objects with `p`" (`IsFullSubcatOnB`, mine): there is
  a functor `I : D ⥤ C`, full, faithful and injective on objects, whose objects in the image are
  exactly the objects with `p`.  This determines `D` up to isomorphism of categories, which is all
  a definition of a full subcategory can say.
- B is the conjunction for `EP_reg ⊆ EP` and `EP_reg(E⁻¹) ⊆ EP(E⁻¹)`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_49
open Polyfold CategoryTheory

/-- `D` is (isomorphic to) the full subcategory of `C` on the objects satisfying `p`: a full,
faithful functor `D ⥤ C`, injective on objects, with image the objects satisfying `p`. -/
def IsFullSubcatOnB.{v, w} (C : Type 1) [Category.{v} C] (D : Type 1) [Category.{w} D]
    (p : C → Prop) : Prop :=
  ∃ I : D ⥤ C, I.Full ∧ I.Faithful ∧ Function.Injective I.obj ∧
    ∀ c : C, (∃ d : D, I.obj d = c) ↔ p c

/-- Definition 10.3.20: `EP_reg` and `EP_reg(E⁻¹)` are the full subcategories of `EP` and
`EP(E⁻¹)` on the ep-groupoids with (LR). -/
def B : Prop :=
  IsFullSubcatOnB EP.{0} EPLocalization.EPreg.{0} (fun A => A.X.IsLR) ∧
  IsFullSubcatOnB EPLocalization.EPLoc.{0} EPLocalization.EPLocReg.{0}
    (fun A => A.toEP.X.IsLR)

end RoundTrip.V10_49
