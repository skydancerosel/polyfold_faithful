import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Groupoid.VertexGroup
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Algebra.Group.Action.Defs

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II, §7.1,
pp. 225–226: **Definition 7.1.1 (2017: 7.1)** (groupoid, `mor(x, y)`, orbit space `|X|`, `π`) and
**Definition 7.1.2 (2017: 7.2)** (isotropy group `G_x`), with the algebraic notions of Chapter 7 that need no
topology: the conjugation `G_x ≅ G_y` (p. 230), functors, full subcategories (pp. 231, 237),
saturated sets (pp. 237, 250), regular objects (Definition 7.2.1 (2017: 7.11), p. 307 (2017 p. 239)) and the translation
groupoid `G ⋉ U` (p. 232).  There is no 2014 preprint of Part II; numbers and pages are the 2017
text's.

# Groupoids as structures of maps

## The text, paraphrased

(Definition 7.1.1 (2017: 7.1)) A groupoid `X = (X, 𝐗)` is a small category with object set `X` and morphism set
`𝐗`, all morphisms invertible, given by five structure maps: source and target `s, t : 𝐗 → X`; the
associative multiplication `m : 𝐗 ₛ×ₜ 𝐗 → 𝐗`, `m(φ, ψ) = φ ∘ ψ`, on `𝐗 ₛ×ₜ 𝐗 = {(φ, ψ) | s(φ) =
t(ψ)}` (for `ψ : x → z`, `φ : z → y`, `φ ∘ ψ : x → y`); the unit map `u(x) = 1_x`, a two-sided
unit; the inverse map `ι(φ) = φ⁻¹`, a two-sided inverse.  `mor(x, y)` is the set of `φ` with
`s(φ) = x`, `t(φ) = y`.  The orbit space `|X| = X/∼` is the quotient by `x ∼ y ⟺` there is a
morphism `x → y`; `|x|` is the class, `π : X → |X|` the quotient map.  (Definition 7.1.2 (2017: 7.2)) The
isotropy group of `x` is `G_x = {φ ∈ 𝐗 | φ : x → x}`.  (p. 230) An isomorphism `φ : x → y` gives
`G_x → G_y`, `g ↦ φ ∘ g ∘ φ⁻¹`.

## What is formalized

* **Definition 7.1.1 (2017: 7.1)**: `GroupoidStr Obj Mor` (the five structure maps `src tgt comp unit inv`, the
  laws on composable pairs), `GroupoidStr.mor`, `GroupoidStr.morOn` (morphisms between points of
  a set: the text's `𝐔(x)`, `𝐀`), `GroupoidStr.Isomorphic`, `GroupoidStr.orbitSetoid`,
  `GroupoidStr.OrbitSpace`, `GroupoidStr.π`, `GroupoidStr.π_eq_π_iff`.
* Laws in the structure-of-maps form: `comp_unit_of_eq`, `unit_comp_of_eq`,
  `eq_inv_of_comp_eq_unit`, `eq_inv_of_comp_eq_unit'` (uniqueness of inverses), `inv_inv`,
  `inv_unit`, `inv_comp_cancel_left`, `comp_inv_cancel_right`, `comp_left_cancel`,
  `comp_right_cancel`, `inv_comp_rev`.
* **Definition 7.1.2 (2017: 7.2)**: `GroupoidStr.Isotropy G x` with its `Group` structure (`g * h = g ∘ h`);
  `isotropyConj` (`g ↦ φ ∘ g ∘ φ⁻¹`, a `MulEquiv`), `isotropyConj_val`.
* The bridge to Mathlib: `GroupoidStr.Ob G` (a type synonym of `Obj`) with
  `CategoryTheory.Groupoid` (`x ⟶ y` is `mor(x, y)`), `Ob.hom_ext`, `Ob.comp_val`, `Ob.id_val`,
  `Ob.inv_val`; `orbitSetoid_eq` (the orbit relation is `CategoryTheory.isIsomorphicSetoid`);
  `isotropyEquivVertexGroup : G_x ≃* (x ⟶ x)ᵐᵒᵖ` and `isotropyEquivAut : G_x ≃* Aut x`.
* Functors: `GroupoidFunctor G H` (maps on objects and morphisms commuting with `s, t, m, u`),
  `GroupoidFunctor.mor_inv`, `.id`, `.comp`, `.ext`, `GroupoidFunctor.toFunctor` (a Mathlib
  functor `G.Ob ⥤ H.Ob`, so `Functor.Full`/`Faithful` apply), `GroupoidFunctor.orbitMap`.
* Saturated sets (p. 237, Definition 7.1.21 (2017: 7.10) (2); p. 250): `GroupoidStr.saturation`,
  `GroupoidStr.IsSaturated` (`π⁻¹(π(A)) = A`), `isSaturated_iff` (closed under morphisms).
* Regular objects (Definition 7.2.1 (2017: 7.11), second half): `GroupoidStr.IsRegular`, `regularSet`,
  `isRegular_tgt_iff` (the text's "if `s(φ)` is regular, so is `t(φ)`").
* The full subcategory on `A ⊆ X` (pp. 231, 237): `GroupoidStr.fullSub G A`.
* The translation groupoid (p. 232): `GroupoidStr.translation K U` for a group `K` acting on `U`,
  `s(g, y) = y`, `t(g, y) = g y`, `(g, y) ∘ (h, z) = (gh, z)`; the trivial groupoid
  `GroupoidStr.trivial Obj` (`𝐗 = X`, `s = t = id`).

## Reading

* **A structure of maps** (PLAN II.3, P1).  The composition is a total map `comp : Mor → Mor →
  Mor` in the text's order, `comp φ ψ = φ ∘ ψ`, and the laws are asked on composable pairs
  `src φ = tgt ψ`, which is the fibred product `𝐗 ₛ×ₜ 𝐗` (`MPolyfold.fibredProduct src tgt`).
  Its values off `𝐗 ₛ×ₜ 𝐗` are not used.  "Small category": `Obj` and `Mor` are types of one
  universe (P2).  The two-sided unit and inverse laws are fields; `inv_inv`, `inv_unit` and the
  anti-multiplicativity of `ι` follow.
* **The isotropy group is a type of its own, with the text's order of multiplication** (a
  deviation from P1, which proposed Mathlib's `vertexGroup`).  Mathlib's `vertexGroup` on
  `x ⟶ x` multiplies in diagrammatic order (`a * b = a ≫ b`, i.e. the text's `b ∘ a`); with it the
  natural representation `Φ : G_x → Diff_sc(U)` of Theorem 7.1.13 (2017: 7.1), `Φ(g ∘ h) = Φ(g) ∘ Φ(h)`, would
  be an anti-homomorphism.  `GroupoidStr.Isotropy G x` (an element is a morphism `x → x`) has
  `g * h = g ∘ h`; it is `(x ⟶ x)ᵐᵒᵖ` as a group (`isotropyEquivVertexGroup`) and Mathlib's
  `Aut x` (`isotropyEquivAut`, whose multiplication is composition of maps).
* **The bridge** `GroupoidStr.Ob G` carries `CategoryTheory.Groupoid` with `x ⟶ y` the subtype
  `mor(x, y)` and `f ≫ g = g ∘ f`; it is used for Mathlib's notions (`Functor.Full`,
  `Functor.Faithful`, `isIsomorphicSetoid`, `vertexGroupIsomOfMap`), while the chapter's proofs
  work with the structure maps on `Mor`.
* A **functor** (Definition 7.1.7 (2017: 7.7); Propositions 7.1.15, 7.1.19 (2017: 7.5, 7.6); Definition 7.1.20 (2017: 7.9)) commutes with `s`, `t`,
  `m` (on composable pairs) and `u`; it then commutes with `ι` (`GroupoidFunctor.mor_inv`).
* **Saturated** is the text's literal `π⁻¹(π(A)) = A`; `isSaturated_iff` gives the form with
  morphisms used in proofs.
* The **full subcategory** on `A` has morphism set `morOn A = {φ | s(φ), t(φ) ∈ A}`; its total
  composition is `G.comp` on composable pairs and the first argument otherwise.
-/

open Set CategoryTheory

namespace Polyfold

universe u v w

/-- **Definition 7.1.1 (2017: 7.1) (groupoid)**: a small category with all morphisms invertible, given by its
five structure maps.  `comp φ ψ = φ ∘ ψ` (first `ψ`, then `φ`) is meant on the composable pairs
`src φ = tgt ψ` (the fibred product `𝐗 ₛ×ₜ 𝐗`); the laws are asked there. -/
structure GroupoidStr (Obj Mor : Type u) where
  /-- The source map `s`. -/
  src : Mor → Obj
  /-- The target map `t`. -/
  tgt : Mor → Obj
  /-- The multiplication `m(φ, ψ) = φ ∘ ψ`, meant for `src φ = tgt ψ`. -/
  comp : Mor → Mor → Mor
  /-- The unit map `u(x) = 1_x`. -/
  unit : Obj → Mor
  /-- The inverse map `ι(φ) = φ⁻¹`. -/
  inv : Mor → Mor
  src_comp : ∀ φ ψ, src φ = tgt ψ → src (comp φ ψ) = src ψ
  tgt_comp : ∀ φ ψ, src φ = tgt ψ → tgt (comp φ ψ) = tgt φ
  comp_assoc : ∀ φ ψ χ, src φ = tgt ψ → src ψ = tgt χ →
    comp (comp φ ψ) χ = comp φ (comp ψ χ)
  src_unit : ∀ x, src (unit x) = x
  tgt_unit : ∀ x, tgt (unit x) = x
  comp_unit : ∀ φ, comp φ (unit (src φ)) = φ
  unit_comp : ∀ φ, comp (unit (tgt φ)) φ = φ
  src_inv : ∀ φ, src (inv φ) = tgt φ
  tgt_inv : ∀ φ, tgt (inv φ) = src φ
  comp_inv : ∀ φ, comp φ (inv φ) = unit (tgt φ)
  inv_comp : ∀ φ, comp (inv φ) φ = unit (src φ)

namespace GroupoidStr

attribute [simp] src_unit tgt_unit src_inv tgt_inv comp_unit unit_comp comp_inv inv_comp

variable {Obj Mor : Type u} (G : GroupoidStr Obj Mor)

/-! ### The laws in the structure-of-maps form -/

variable {G}

theorem comp_unit_of_eq {φ : Mor} {x : Obj} (h : G.src φ = x) : G.comp φ (G.unit x) = φ := by
  subst h
  exact G.comp_unit φ

theorem unit_comp_of_eq {φ : Mor} {x : Obj} (h : G.tgt φ = x) : G.comp (G.unit x) φ = φ := by
  subst h
  exact G.unit_comp φ

/-- `φ⁻¹ ∘ (φ ∘ ψ) = ψ`. -/
theorem inv_comp_cancel_left {φ ψ : Mor} (h : G.src φ = G.tgt ψ) :
    G.comp (G.inv φ) (G.comp φ ψ) = ψ := by
  rw [← G.comp_assoc _ _ _ (G.src_inv φ) h, G.inv_comp, unit_comp_of_eq h.symm]

/-- `(ψ ∘ φ) ∘ φ⁻¹ = ψ`. -/
theorem comp_inv_cancel_right {φ ψ : Mor} (h : G.src ψ = G.tgt φ) :
    G.comp (G.comp ψ φ) (G.inv φ) = ψ := by
  rw [G.comp_assoc _ _ _ h (G.tgt_inv φ).symm, G.comp_inv, comp_unit_of_eq h]

theorem comp_left_cancel {φ ψ ψ' : Mor} (h : G.src φ = G.tgt ψ) (h' : G.src φ = G.tgt ψ')
    (he : G.comp φ ψ = G.comp φ ψ') : ψ = ψ' := by
  rw [← inv_comp_cancel_left h, he, inv_comp_cancel_left h']

theorem comp_right_cancel {φ ψ ψ' : Mor} (h : G.src ψ = G.tgt φ) (h' : G.src ψ' = G.tgt φ)
    (he : G.comp ψ φ = G.comp ψ' φ) : ψ = ψ' := by
  rw [← comp_inv_cancel_right h, he, comp_inv_cancel_right h']

/-- **Uniqueness of inverses**: a left inverse is the inverse. -/
theorem eq_inv_of_comp_eq_unit {φ ψ : Mor} (h : G.src ψ = G.tgt φ)
    (hψφ : G.comp ψ φ = G.unit (G.src φ)) : ψ = G.inv φ := by
  rw [← comp_inv_cancel_right (φ := φ) h, hψφ, unit_comp_of_eq (G.tgt_inv φ)]

/-- **Uniqueness of inverses**: a right inverse is the inverse. -/
theorem eq_inv_of_comp_eq_unit' {φ ψ : Mor} (h : G.src φ = G.tgt ψ)
    (hφψ : G.comp φ ψ = G.unit (G.tgt φ)) : ψ = G.inv φ := by
  rw [← inv_comp_cancel_left (φ := φ) h, hφψ, comp_unit_of_eq (G.src_inv φ)]

@[simp]
theorem inv_inv (φ : Mor) : G.inv (G.inv φ) = φ :=
  (eq_inv_of_comp_eq_unit (G.tgt_inv φ).symm (by rw [G.src_inv, G.comp_inv])).symm

@[simp]
theorem inv_unit (x : Obj) : G.inv (G.unit x) = G.unit x :=
  (eq_inv_of_comp_eq_unit (by simp) (by rw [G.src_unit, unit_comp_of_eq (G.tgt_unit x)])).symm

/-- `(φ ∘ ψ)⁻¹ = ψ⁻¹ ∘ φ⁻¹`. -/
theorem inv_comp_rev {φ ψ : Mor} (h : G.src φ = G.tgt ψ) :
    G.inv (G.comp φ ψ) = G.comp (G.inv ψ) (G.inv φ) := by
  have h1 : G.src (G.inv ψ) = G.tgt (G.inv φ) := by rw [G.src_inv, G.tgt_inv, h]
  refine (eq_inv_of_comp_eq_unit' ?_ ?_).symm
  · rw [G.src_comp _ _ h, G.tgt_comp _ _ h1, G.tgt_inv]
  · rw [G.comp_assoc _ _ _ h (by rw [G.tgt_comp _ _ h1, G.tgt_inv]),
      ← G.comp_assoc _ _ _ (G.tgt_inv ψ).symm h1, G.comp_inv,
      unit_comp_of_eq (by rw [G.tgt_inv, h]), G.comp_inv, G.tgt_comp _ _ h]

variable (G)

/-! ### Morphism sets and the orbit space -/

/-- `mor(x, y)`: the morphisms `φ : x → y`. -/
def mor (x y : Obj) : Set Mor := {φ | G.src φ = x ∧ G.tgt φ = y}

/-- The morphisms between points of `A` (the morphism set of the full subcategory on `A`: the
text's `𝐔(x)`, p. 231, and `𝐀`, p. 238). -/
def morOn (A : Set Obj) : Set Mor := {φ | G.src φ ∈ A ∧ G.tgt φ ∈ A}

/-- `x ∼ y`: there is a morphism `x → y` (Definition 7.1.1 (2017: 7.1)). -/
def Isomorphic (x y : Obj) : Prop := ∃ φ, G.src φ = x ∧ G.tgt φ = y

theorem isomorphic_refl (x : Obj) : G.Isomorphic x x := ⟨G.unit x, G.src_unit x, G.tgt_unit x⟩

variable {G} in
theorem Isomorphic.symm {x y : Obj} (h : G.Isomorphic x y) : G.Isomorphic y x := by
  obtain ⟨φ, rfl, rfl⟩ := h
  exact ⟨G.inv φ, G.src_inv φ, G.tgt_inv φ⟩

variable {G} in
theorem Isomorphic.trans {x y z : Obj} (h : G.Isomorphic x y) (h' : G.Isomorphic y z) :
    G.Isomorphic x z := by
  obtain ⟨φ, rfl, rfl⟩ := h
  obtain ⟨ψ, hψ, rfl⟩ := h'
  exact ⟨G.comp ψ φ, G.src_comp _ _ hψ, G.tgt_comp _ _ hψ⟩

/-- The equivalence relation `∼` of Definition 7.1.1 (2017: 7.1). -/
def orbitSetoid : Setoid Obj where
  r := G.Isomorphic
  iseqv := ⟨G.isomorphic_refl, Isomorphic.symm, Isomorphic.trans⟩

/-- **The orbit space** `|X| = X/∼` (Definition 7.1.1 (2017: 7.1)). -/
abbrev OrbitSpace : Type u := Quotient G.orbitSetoid

/-- **The quotient map** `π : X → |X|`, `x ↦ |x|`. -/
def π (x : Obj) : G.OrbitSpace := Quotient.mk G.orbitSetoid x

theorem π_eq_π_iff {x y : Obj} : G.π x = G.π y ↔ G.Isomorphic x y := Quotient.eq

theorem π_src_eq_π_tgt (φ : Mor) : G.π (G.src φ) = G.π (G.tgt φ) :=
  (G.π_eq_π_iff).2 ⟨φ, rfl, rfl⟩

theorem surjective_π : Function.Surjective G.π := Quotient.mk_surjective

/-! ### Saturated sets -/

/-- The saturation `π⁻¹(π(A))` of `A`. -/
def saturation (A : Set Obj) : Set Obj := G.π ⁻¹' (G.π '' A)

/-- `A` is **saturated**: `π⁻¹(π(A)) = A` (Definition 7.1.21 (2017: 7.10) (2); p. 250). -/
def IsSaturated (A : Set Obj) : Prop := G.π ⁻¹' (G.π '' A) = A

theorem subset_saturation (A : Set Obj) : A ⊆ G.saturation A := subset_preimage_image _ _

/-- A set is saturated if and only if it contains with `s(φ)` also `t(φ)`. -/
theorem isSaturated_iff {A : Set Obj} : G.IsSaturated A ↔ ∀ φ, G.src φ ∈ A → G.tgt φ ∈ A := by
  constructor
  · intro h φ hφ
    rw [← h]
    exact ⟨G.src φ, hφ, G.π_src_eq_π_tgt φ⟩
  · intro h
    refine subset_antisymm ?_ (G.subset_saturation A)
    rintro y ⟨a, ha, hay⟩
    obtain ⟨φ, rfl, rfl⟩ := (G.π_eq_π_iff).1 hay
    exact h φ ha

theorem isSaturated_univ : G.IsSaturated univ := G.isSaturated_iff.2 fun _ _ => mem_univ _

/-! ### Definition 7.1.2 (2017: 7.2): the isotropy group -/

/-- **Definition 7.1.2 (2017: 7.2)**: an element of the **isotropy group** `G_x`, a morphism `x → x`. -/
@[ext]
structure Isotropy (x : Obj) where
  /-- The morphism. -/
  val : Mor
  src_val : G.src val = x
  tgt_val : G.tgt val = x

namespace Isotropy

variable {G} {x : Obj}

instance : One (G.Isotropy x) := ⟨⟨G.unit x, G.src_unit x, G.tgt_unit x⟩⟩

/-- The product `g * h = g ∘ h` (the text's order). -/
instance : Mul (G.Isotropy x) :=
  ⟨fun g h => ⟨G.comp g.val h.val,
    (G.src_comp _ _ (g.src_val.trans h.tgt_val.symm)).trans h.src_val,
    (G.tgt_comp _ _ (g.src_val.trans h.tgt_val.symm)).trans g.tgt_val⟩⟩

instance : Inv (G.Isotropy x) :=
  ⟨fun g => ⟨G.inv g.val, (G.src_inv _).trans g.tgt_val, (G.tgt_inv _).trans g.src_val⟩⟩

@[simp] theorem val_one : (1 : G.Isotropy x).val = G.unit x := rfl

@[simp] theorem val_mul (g h : G.Isotropy x) : (g * h).val = G.comp g.val h.val := rfl

@[simp] theorem val_inv (g : G.Isotropy x) : g⁻¹.val = G.inv g.val := rfl

instance : Group (G.Isotropy x) where
  mul_assoc g h k := Isotropy.ext (G.comp_assoc _ _ _ (g.src_val.trans h.tgt_val.symm)
    (h.src_val.trans k.tgt_val.symm))
  one_mul g := Isotropy.ext (unit_comp_of_eq g.tgt_val)
  mul_one g := Isotropy.ext (comp_unit_of_eq g.src_val)
  inv_mul_cancel g := Isotropy.ext ((G.inv_comp g.val).trans (congrArg G.unit g.src_val))

theorem val_injective : Function.Injective (Isotropy.val : G.Isotropy x → Mor) :=
  fun _ _ h => Isotropy.ext h

theorem val_mem_mor (g : G.Isotropy x) : g.val ∈ G.mor x x := ⟨g.src_val, g.tgt_val⟩

end Isotropy

/-! ### The bridge to `CategoryTheory.Groupoid` -/

/-- The objects of `G`, as a type carrying Mathlib's groupoid structure (`x ⟶ y` is
`mor(x, y)`). -/
def Ob (_G : GroupoidStr Obj Mor) : Type u := Obj

/-- Mathlib's groupoid structure: `x ⟶ y` is `mor(x, y)`, `f ≫ g = g ∘ f`. -/
instance instGroupoid : Groupoid.{u} G.Ob where
  Hom x y := ↥(G.mor x y)
  id x := ⟨G.unit x, G.src_unit x, G.tgt_unit x⟩
  comp f g := ⟨G.comp g.1 f.1, (G.src_comp _ _ (g.2.1.trans f.2.2.symm)).trans f.2.1,
    (G.tgt_comp _ _ (g.2.1.trans f.2.2.symm)).trans g.2.2⟩
  id_comp f := Subtype.ext (comp_unit_of_eq f.2.1)
  comp_id f := Subtype.ext (unit_comp_of_eq f.2.2)
  assoc f g h := Subtype.ext (G.comp_assoc _ _ _ (h.2.1.trans g.2.2.symm)
    (g.2.1.trans f.2.2.symm)).symm
  inv f := ⟨G.inv f.1, (G.src_inv _).trans f.2.2, (G.tgt_inv _).trans f.2.1⟩
  inv_comp f := Subtype.ext ((G.comp_inv f.1).trans (congrArg G.unit f.2.2))
  comp_inv f := Subtype.ext ((G.inv_comp f.1).trans (congrArg G.unit f.2.1))

/-- An object of `G` as an object of the bridge. -/
def toOb (x : Obj) : G.Ob := x

/-- The morphism `x ⟶ y` of the bridge given by `φ ∈ mor(x, y)`. -/
def homMk {x y : Obj} (φ : Mor) (hx : G.src φ = x) (hy : G.tgt φ = y) : G.toOb x ⟶ G.toOb y :=
  ⟨φ, hx, hy⟩

namespace Ob

variable {G}

@[ext]
theorem hom_ext {x y : G.Ob} {f g : x ⟶ y} (h : f.1 = g.1) : f = g := Subtype.ext h

@[simp]
theorem comp_val {x y z : G.Ob} (f : x ⟶ y) (g : y ⟶ z) : (f ≫ g).1 = G.comp g.1 f.1 := rfl

@[simp]
theorem id_val (x : G.Ob) : (𝟙 x : x ⟶ x).1 = G.unit x := rfl

@[simp]
theorem inv_val {x y : G.Ob} (f : x ⟶ y) : (Groupoid.inv f).1 = G.inv f.1 := rfl

end Ob

@[simp]
theorem homMk_val {x y : Obj} (φ : Mor) (hx : G.src φ = x) (hy : G.tgt φ = y) :
    (G.homMk φ hx hy).1 = φ := rfl

/-- The orbit relation of Definition 7.1.1 (2017: 7.1) is Mathlib's "isomorphic" relation of the bridge. -/
theorem orbitSetoid_eq : G.orbitSetoid = isIsomorphicSetoid G.Ob := by
  refine Setoid.ext fun x y => ⟨?_, ?_⟩
  · rintro ⟨φ, hx, hy⟩
    exact ⟨(Groupoid.isoEquivHom (G.toOb x) (G.toOb y)).symm (G.homMk φ hx hy)⟩
  · rintro ⟨i⟩
    exact ⟨i.hom.1, i.hom.2.1, i.hom.2.2⟩

/-- `G_x` is the opposite of Mathlib's vertex group `x ⟶ x` (which multiplies in diagrammatic
order). -/
def isotropyEquivVertexGroup (x : Obj) : G.Isotropy x ≃* (G.toOb x ⟶ G.toOb x)ᵐᵒᵖ where
  toFun g := MulOpposite.op (G.homMk g.val g.src_val g.tgt_val)
  invFun f := ⟨f.unop.1, f.unop.2.1, f.unop.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- `G_x` is Mathlib's automorphism group `Aut x` of the bridge. -/
def isotropyEquivAut (x : Obj) : G.Isotropy x ≃* Aut (G.toOb x) where
  toFun g := (Groupoid.isoEquivHom (G.toOb x) (G.toOb x)).symm (G.homMk g.val g.src_val g.tgt_val)
  invFun i := ⟨i.hom.1, i.hom.2.1, i.hom.2.2⟩
  left_inv _ := rfl
  right_inv _ := Iso.ext rfl
  map_mul' _ _ := Iso.ext rfl

/-- **The conjugation** `G_x → G_y`, `g ↦ φ ∘ g ∘ φ⁻¹`, for `φ : x → y` (p. 230), through
Mathlib's `vertexGroupIsomOfMap`. -/
def isotropyConj {x y : Obj} (φ : Mor) (hx : G.src φ = x) (hy : G.tgt φ = y) :
    G.Isotropy x ≃* G.Isotropy y :=
  ((G.isotropyEquivVertexGroup x).trans
    (MulEquiv.op (Groupoid.vertexGroupIsomOfMap (G.homMk φ hx hy)))).trans
    (G.isotropyEquivVertexGroup y).symm

@[simp]
theorem isotropyConj_val {x y : Obj} (φ : Mor) (hx : G.src φ = x) (hy : G.tgt φ = y)
    (g : G.Isotropy x) :
    (G.isotropyConj φ hx hy g).val = G.comp (G.comp φ g.val) (G.inv φ) :=
  rfl

/-! ### Regular objects (Definition 7.2.1 (2017: 7.11), second half) -/

/-- An object `x` is **regular**: `G_x = {1_x}` (Definition 7.2.1 (2017: 7.11)). -/
def IsRegular (x : Obj) : Prop := ∀ g : G.Isotropy x, g = 1

/-- The **regular part** `X_reg = {x | G_x = {1_x}}` (p. 239). -/
def regularSet : Set Obj := {x | G.IsRegular x}

/-- If `s(φ)` is regular, so is `t(φ)`, and conversely (p. 239). -/
theorem isRegular_tgt_iff (φ : Mor) : G.IsRegular (G.tgt φ) ↔ G.IsRegular (G.src φ) := by
  set e := G.isotropyConj φ rfl rfl
  constructor
  · intro h g
    exact e.injective ((h _).trans (map_one e).symm)
  · intro h g
    rw [← e.apply_symm_apply g, h (e.symm g), map_one]

/-! ### The full subcategory on a set of objects -/

open scoped Classical in
/-- **The full subcategory on `A`** (pp. 231, 237): objects `A`, morphisms `morOn A`, the
structure maps restricted (the composition of a non-composable pair is the first argument). -/
noncomputable def fullSub (A : Set Obj) : GroupoidStr A (G.morOn A) where
  src φ := ⟨G.src φ.1, φ.2.1⟩
  tgt φ := ⟨G.tgt φ.1, φ.2.2⟩
  comp φ ψ := if h : G.src φ.1 = G.tgt ψ.1 then
    ⟨G.comp φ.1 ψ.1, by rw [G.src_comp _ _ h]; exact ψ.2.1, by rw [G.tgt_comp _ _ h]; exact φ.2.2⟩
    else φ
  unit x := ⟨G.unit x.1, by rw [G.src_unit]; exact x.2, by rw [G.tgt_unit]; exact x.2⟩
  inv φ := ⟨G.inv φ.1, by rw [G.src_inv]; exact φ.2.2, by rw [G.tgt_inv]; exact φ.2.1⟩
  src_comp φ ψ h := by
    have h' : G.src φ.1 = G.tgt ψ.1 := congrArg Subtype.val h
    simp only [dif_pos h']
    exact Subtype.ext (G.src_comp _ _ h')
  tgt_comp φ ψ h := by
    have h' : G.src φ.1 = G.tgt ψ.1 := congrArg Subtype.val h
    simp only [dif_pos h']
    exact Subtype.ext (G.tgt_comp _ _ h')
  comp_assoc φ ψ χ h₁ h₂ := by
    have h₁' : G.src φ.1 = G.tgt ψ.1 := congrArg Subtype.val h₁
    have h₂' : G.src ψ.1 = G.tgt χ.1 := congrArg Subtype.val h₂
    have h₃ : G.src (G.comp φ.1 ψ.1) = G.tgt χ.1 := by rw [G.src_comp _ _ h₁', h₂']
    have h₄ : G.src φ.1 = G.tgt (G.comp ψ.1 χ.1) := by rw [G.tgt_comp _ _ h₂', h₁']
    simp only [dif_pos h₁', dif_pos h₂', dif_pos h₃, dif_pos h₄]
    exact Subtype.ext (G.comp_assoc _ _ _ h₁' h₂')
  src_unit x := Subtype.ext (G.src_unit x.1)
  tgt_unit x := Subtype.ext (G.tgt_unit x.1)
  comp_unit φ := by
    simp only [G.tgt_unit, dif_pos]
    exact Subtype.ext (G.comp_unit φ.1)
  unit_comp φ := by
    simp only [G.src_unit, dif_pos]
    exact Subtype.ext (G.unit_comp φ.1)
  src_inv φ := Subtype.ext (G.src_inv φ.1)
  tgt_inv φ := Subtype.ext (G.tgt_inv φ.1)
  comp_inv φ := by
    simp only [G.tgt_inv, dif_pos]
    exact Subtype.ext (G.comp_inv φ.1)
  inv_comp φ := by
    simp only [G.src_inv, dif_pos]
    exact Subtype.ext (G.inv_comp φ.1)

/-! ### The translation groupoid and the trivial groupoid -/

/-- **The translation groupoid** `K ⋉ U` of a group acting on `U` (p. 232): objects `U`, morphisms
`K × U`, `s(g, y) = y`, `t(g, y) = g y`, `(g, y) ∘ (h, z) = (gh, z)`, `1_y = (1, y)`,
`(g, y)⁻¹ = (g⁻¹, g y)`. -/
def translation (K U : Type u) [Group K] [MulAction K U] : GroupoidStr U (K × U) where
  src p := p.2
  tgt p := p.1 • p.2
  comp p q := (p.1 * q.1, q.2)
  unit y := (1, y)
  inv p := (p.1⁻¹, p.1 • p.2)
  src_comp _ _ _ := rfl
  tgt_comp p q h := by
    change (p.1 * q.1) • q.2 = p.1 • p.2
    rw [mul_smul, h]
  comp_assoc p q r _ _ := by
    change (p.1 * q.1 * r.1, r.2) = (p.1 * (q.1 * r.1), r.2)
    rw [mul_assoc]
  src_unit _ := rfl
  tgt_unit y := one_smul K y
  comp_unit p := by
    change (p.1 * 1, p.2) = p
    rw [mul_one]
  unit_comp p := by
    change (1 * p.1, p.2) = p
    rw [one_mul]
  src_inv _ := rfl
  tgt_inv p := inv_smul_smul p.1 p.2
  comp_inv p := by
    change (p.1 * p.1⁻¹, p.1 • p.2) = (1, p.1 • p.2)
    rw [mul_inv_cancel]
  inv_comp p := by
    change (p.1⁻¹ * p.1, p.2) = (1, p.2)
    rw [inv_mul_cancel]

/-- **The trivial groupoid** of `Obj`: `Mor = Obj`, `s = t = u = ι = id`. -/
def trivial (Obj : Type u) : GroupoidStr Obj Obj where
  src := id
  tgt := id
  comp φ _ := φ
  unit := id
  inv := id
  src_comp _ _ h := h
  tgt_comp _ _ _ := rfl
  comp_assoc _ _ _ _ _ := rfl
  src_unit _ := rfl
  tgt_unit _ := rfl
  comp_unit _ := rfl
  unit_comp _ := rfl
  src_inv _ := rfl
  tgt_inv _ := rfl
  comp_inv _ := rfl
  inv_comp _ := rfl

theorem isSaturated_trivial (A : Set Obj) : (trivial Obj).IsSaturated A :=
  (trivial Obj).isSaturated_iff.2 fun _ h => h

theorem isRegular_trivial (x : Obj) : (trivial Obj).IsRegular x := fun g =>
  Isotropy.ext (g.src_val.trans (1 : (trivial Obj).Isotropy x).src_val.symm)

end GroupoidStr

/-! ### Functors -/

/-- **A functor** between groupoids: maps on objects and morphisms commuting with `s`, `t`, `m`
(on composable pairs) and `u` (Definition 7.1.7 (2017: 7.7); Propositions 7.1.15, 7.1.19 (2017: 7.5, 7.6); Definition 7.1.20 (2017: 7.9)). -/
structure GroupoidFunctor {Obj Mor : Type u} {Obj' Mor' : Type v} (G : GroupoidStr Obj Mor)
    (H : GroupoidStr Obj' Mor') where
  /-- The map on objects. -/
  obj : Obj → Obj'
  /-- The map on morphisms. -/
  mor : Mor → Mor'
  src_mor : ∀ φ, H.src (mor φ) = obj (G.src φ)
  tgt_mor : ∀ φ, H.tgt (mor φ) = obj (G.tgt φ)
  mor_comp : ∀ φ ψ, G.src φ = G.tgt ψ → mor (G.comp φ ψ) = H.comp (mor φ) (mor ψ)
  mor_unit : ∀ x, mor (G.unit x) = H.unit (obj x)

namespace GroupoidFunctor

variable {Obj Mor : Type u} {Obj' Mor' : Type v} {Obj'' Mor'' : Type w}
  {G : GroupoidStr Obj Mor} {H : GroupoidStr Obj' Mor'} {K : GroupoidStr Obj'' Mor''}

theorem ext {F F' : GroupoidFunctor G H} (h₁ : F.obj = F'.obj) (h₂ : F.mor = F'.mor) :
    F = F' := by
  cases F
  cases F'
  cases h₁
  cases h₂
  rfl

/-- A functor commutes with the inverse map. -/
theorem mor_inv (F : GroupoidFunctor G H) (φ : Mor) : F.mor (G.inv φ) = H.inv (F.mor φ) := by
  refine GroupoidStr.eq_inv_of_comp_eq_unit ?_ ?_
  · rw [F.src_mor, F.tgt_mor, G.src_inv]
  · rw [← F.mor_comp _ _ (G.src_inv φ), G.inv_comp, F.mor_unit, F.src_mor]

variable (G) in
/-- The identity functor. -/
def id : GroupoidFunctor G G where
  obj x := x
  mor φ := φ
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl

/-- The composition `F ∘ E`. -/
def comp (F : GroupoidFunctor H K) (E : GroupoidFunctor G H) : GroupoidFunctor G K where
  obj x := F.obj (E.obj x)
  mor φ := F.mor (E.mor φ)
  src_mor φ := by rw [F.src_mor, E.src_mor]
  tgt_mor φ := by rw [F.tgt_mor, E.tgt_mor]
  mor_comp φ ψ h := by
    rw [E.mor_comp _ _ h, F.mor_comp _ _ (by rw [E.src_mor, E.tgt_mor, h])]
  mor_unit x := by rw [E.mor_unit, F.mor_unit]

/-- The functor as a Mathlib functor between the bridges. -/
def toFunctor (F : GroupoidFunctor G H) : G.Ob ⥤ H.Ob where
  obj := F.obj
  map f := ⟨F.mor f.1, (F.src_mor _).trans (congrArg F.obj f.2.1),
    (F.tgt_mor _).trans (congrArg F.obj f.2.2)⟩
  map_id x := Subtype.ext (F.mor_unit x)
  map_comp f g := Subtype.ext (F.mor_comp g.1 f.1 (g.2.1.trans f.2.2.symm))

@[simp]
theorem toFunctor_map_val (F : GroupoidFunctor G H) {x y : G.Ob} (f : x ⟶ y) :
    (F.toFunctor.map f).1 = F.mor f.1 := rfl

/-- The induced map `|G| → |H|` of orbit spaces. -/
def orbitMap (F : GroupoidFunctor G H) : G.OrbitSpace → H.OrbitSpace :=
  Quotient.map F.obj fun x y ⟨φ, hx, hy⟩ =>
    ⟨F.mor φ, by rw [F.src_mor, hx], by rw [F.tgt_mor, hy]⟩

@[simp]
theorem orbitMap_π (F : GroupoidFunctor G H) (x : Obj) : F.orbitMap (G.π x) = H.π (F.obj x) :=
  rfl

end GroupoidFunctor

end Polyfold
