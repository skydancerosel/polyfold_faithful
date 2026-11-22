import Polyfold.Chapter10.Equivalence
import Polyfold.Chapter8.BundleOrbitParacompact

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 744–745): **Definition 17.1.1** (GCT) and **Definition 17.1.2** (the translation
groupoid `G ⋉ O` and the metrizability of `G\O`).  Numbers and pages are the 2021 text's.

# Groupoidal categories with topology

## The text, paraphrased

(Definition 17.1.1, p. 744) A GCT is a pair `(C, T)`: a category `C` such that (1) the orbit space
`|C|` (the isomorphism classes of objects) is a set, (2) every set of morphisms between two objects
is finite, (3) all morphisms are isomorphisms; and a metrizable topology `T` on `|C|`.
(Definition 17.1.2, p. 744) For an M-polyfold `O`, a finite group `G` and a homomorphism
`γ : G → Diff_sc(O)`, `g ∗ x = γ(g)(x)`, the translation groupoid `G ⋉ O` has objects `O`,
morphisms `G × O`, `s(g, x) = x`, `t(g, x) = g ∗ x`.  "One easily verifies" that it is an
ep-groupoid, and `G\O = |G ⋉ O|` is metrizable: average a metric `d₀` of `O` over `G` and take
`d̄([q], [q']) = min_{g, g'} d(g ∗ q, g' ∗ q')`.

## What is formalized (namespace `Polyfold`)

* `GroupoidalCategory` (**Definition 17.1.1 (1)–(3)**, without the topology; this is also
  Definition 19.1.1): object and morphism types of one universe, a `GroupoidStr` (all morphisms
  invertible), finite morphism sets; `GroupoidalCategory.OrbitSpace`, `GroupoidalCategory.π`.
* `GCT` (**Definition 17.1.1**): a groupoidal category with a metrizable topology on `|C|`
  (instances `GCT.top`, `GCT.metrizable`).
* **Definition 17.1.2**: the translation groupoid is `GroupoidStr.translation G O` (Chapter 7), its
  ep-groupoid `EpGroupoid.Examples.actionEpGroupoid` (Chapter 7, the text's "one easily verifies");
  `definition_17_1_2` (the ep-groupoid has the translation groupoid as underlying groupoid, and
  `G\O` is metrizable), `metrizableSpace_translation_orbitSpace`.
* `GroupoidalCategory.translation` (finite morphism sets of `G ⋉ O`), `GCT.translation` (the GCT of
  a translation groupoid, with the quotient topology on `|G ⋉ O|`), and the non-degenerate witness
  `GCT.reflection`: `ℤ/2 ⋉ ℝ` acting by reflection (positive dimension, `G_0 = ℤ/2`).

## Readings

* "The class of objects" is read as a type `Obj : Type u` (the universe of the M-polyfolds that
  appear later), so (1) "`|C|` is a set" holds automatically; the morphisms form a type
  `Mor : Type u` and the category is a `GroupoidStr` (structure maps `s, t, m, u, ι`), which is
  (3).
* The homomorphism `γ : G → Diff_sc(O)` of Definition 17.1.2 is a `MulAction G O` with every
  `g ∗ ·` sc-smooth; each `g ∗ ·` is then an sc-diffeomorphism with inverse `g⁻¹ ∗ ·`.  The finite
  group carries the discrete topology, as `G × O` is an M-polyfold.
* The metrizability of `G\O` is proved by the text's averaged metric
  (`metrizableSpace_orbitRel_quotient_finite`, Chapter 8), transported along
  `|G ⋉ O| ≃ₜ O/G` (`actionOrbitHomeomorph`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory TopologicalSpace

noncomputable section

namespace Polyfold

universe u

/-- **2021 Definition 17.1.1 (1)–(3), p. 744**: a **groupoidal category**: a category whose
objects and morphisms form types of one universe (so that the orbit space `|C|` is a set), all
of whose morphisms are isomorphisms (a `GroupoidStr`), and whose morphism sets `mor(α, β)` are
finite.  (Definition 19.1.1 is the same notion.) -/
structure GroupoidalCategory : Type (u + 1) where
  /-- The objects `obj(C)`. -/
  Obj : Type u
  /-- The morphisms `mor(C)`. -/
  Mor : Type u
  /-- (3) The category, all of whose morphisms are isomorphisms. -/
  toGroupoidStr : GroupoidStr Obj Mor
  /-- (2) Every set of morphisms between two objects is finite. -/
  finite_mor : ∀ α β : Obj, (toGroupoidStr.mor α β).Finite

namespace GroupoidalCategory

variable (C : GroupoidalCategory.{u})

/-- The orbit space `|C|`, the set of isomorphism classes of objects (Definition 17.1.1 (1)). -/
abbrev OrbitSpace : Type u := C.toGroupoidStr.OrbitSpace

/-- `α ↦ |α|`. -/
abbrev π (α : C.Obj) : C.OrbitSpace := C.toGroupoidStr.π α

theorem π_eq_π_iff {α β : C.Obj} : C.π α = C.π β ↔ C.toGroupoidStr.Isomorphic α β :=
  C.toGroupoidStr.π_eq_π_iff

/-- The translation groupoid `G ⋉ O` of a finite group, as a groupoidal category: `mor(x, y)` is
contained in `G × {x}`. -/
abbrev translation (G O : Type u) [Group G] [Finite G] [MulAction G O] :
    GroupoidalCategory.{u} where
  Obj := O
  Mor := G × O
  toGroupoidStr := GroupoidStr.translation G O
  finite_mor x _ := (Set.finite_univ.prod (Set.finite_singleton x)).subset fun _ hp =>
    ⟨mem_univ _, hp.1⟩

end GroupoidalCategory

/-- **2021 Definition 17.1.1, p. 744**: a **GCT** (groupoidal category with topology): a
groupoidal category `C` with a metrizable topology `T` on its orbit space `|C|`. -/
structure GCT : Type (u + 1) extends GroupoidalCategory.{u} where
  /-- The topology `T` on `|C|`. -/
  [top : TopologicalSpace toGroupoidStr.OrbitSpace]
  /-- `T` is metrizable. -/
  [metrizable : MetrizableSpace toGroupoidStr.OrbitSpace]

attribute [instance] GCT.top GCT.metrizable

/-! ### Definition 17.1.2: the translation groupoid -/

section Translation

open EpGroupoid.Examples

variable {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  {O : Type u} [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O]
  {P : MPolyfold O}

/-- **2021 Definition 17.1.2, p. 744, the metrizability of `G\O = |G ⋉ O|`** (by the text's
averaged metric). -/
theorem metrizableSpace_translation_orbitSpace (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y) :
    MetrizableSpace (GroupoidStr.translation G O).OrbitSpace := by
  have := P.metrizableSpace
  have := metrizableSpace_orbitRel_quotient_finite (G := G) (U := O)
    (action_continuous_smul hP)
  exact (actionOrbitHomeomorph hP).isEmbedding.metrizableSpace

/-- **2021 Definition 17.1.2, p. 744**: for a finite group `G` acting on the M-polyfold `O` by
sc-diffeomorphisms, the translation groupoid `G ⋉ O` (`GroupoidStr.translation`) is the
underlying groupoid of an ep-groupoid ("one easily verifies", `actionEpGroupoid`), and its orbit
space `G\O` is metrizable. -/
theorem definition_17_1_2 (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y) :
    (actionEpGroupoid hP).toGroupoidStr = GroupoidStr.translation G O ∧
      MetrizableSpace (GroupoidStr.translation G O).OrbitSpace :=
  ⟨rfl, metrizableSpace_translation_orbitSpace hP⟩

variable (G O) in
/-- The GCT of a translation groupoid `G ⋉ O`: `|G ⋉ O| = G\O` with the quotient topology,
metrizable by Definition 17.1.2. -/
abbrev GCT.translation (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y) : GCT.{u} where
  toGroupoidalCategory := GroupoidalCategory.translation G O
  top := (inferInstance : TopologicalSpace (GroupoidStr.translation G O).OrbitSpace)
  metrizable := metrizableSpace_translation_orbitSpace hP

@[simp]
theorem GCT.translation_toGroupoidStr (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y) :
    (GCT.translation G O hP).toGroupoidStr = GroupoidStr.translation G O := rfl

end Translation

/-- **The non-degenerate witness of Definition 17.1.1**: the GCT `ℤ/2 ⋉ ℝ`, `ℤ/2 = ℤˣ` acting on
`ℝ` by reflection (`EpGroupoid.Examples.reflectionEpGroupoid`); `|C| = ℝ/±1`. -/
abbrev GCT.reflection : GCT.{0} :=
  GCT.translation ℤˣ (Fin 1 → ℝ) EpGroupoid.Examples.isScSmoothMap_units_smul

/-- In `GCT.reflection`, the object `0` has the non-trivial automorphism `(−1, 0)`. -/
theorem GCT.reflection_exists_ne_unit :
    ∃ φ ∈ GCT.reflection.toGroupoidStr.mor 0 0, φ ≠ GCT.reflection.toGroupoidStr.unit 0 :=
  ⟨((-1 : ℤˣ), 0), ⟨rfl, smul_zero _⟩, fun h => absurd (congrArg Prod.fst h) (by decide)⟩

end Polyfold
