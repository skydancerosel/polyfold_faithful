import Polyfold.Chapter7.NaturalAction
import Polyfold.Chapter7.NaturalRep
import Polyfold.Chapter7.Basic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II, §7.1,
pp. 236–237: **Proposition 7.1.19 (2017: 7.6)** (the orbit space of `U(x)` is `G_x\U(x)`, pp. 236–237),
**Definition 7.1.20 (2017: 7.9)** (local uniformizer, p. 237) and the two claims after it ("there exists a local
uniformizer around every object", "a local uniformizer is injective on objects as well as
morphisms", p. 237).  There is no 2014 preprint of Part II; numbers and pages are the 2017 text's.
Definition 7.1.20 (2017: 7.9) itself is in `EpGroupoid.lean` (`LocalUniformizer`).

# Local uniformizers

## The text, paraphrased

(Proposition 7.1.19 (2017: 7.6)) Let `z = |x| ∈ |X|`, `G_x` the isotropy group of `x` and `U(x)` an open
neighbourhood with the natural `G_x`-action `g ∗ y = Φ(g)(y)`.  Then
`τ : G_x\U(x) → |U(x)| = π(U(x))`, `G_x ∗ y ↦ |y|`, is a homeomorphism.  In other words, the
functor `G_x ⋉ U(x) → X`, the inclusion on objects and `(g, y) ↦ Γ(g, y)` on morphisms, is fully
faithful and induces a homeomorphism `|U(x)|_{G_x ⋉ U(x)} = G_x\U(x) → |U(x)|`.  *Proof.* `τ` is
well defined and surjective; it is injective: for `φ : y → y'` Theorem 7.1.13 (2017: 7.1) (3) gives `g` with
`Γ(g, y) = φ`, so `y' = t(Γ(g, y)) = g ∗ y`.  `|U(x)|` is open by Proposition 7.1.8 (2017: 7.1); `τ ∘ σ = π|U(x)`
for the quotient map `σ : U(x) → G_x\U(x)`, which is open since `G_x` acts by sc-diffeomorphisms;
hence `τ` is continuous (quotient topology of `G_x\U(x)`) and open (quotient topology of `|X|`).
(Definition 7.1.20 (2017: 7.9)) A local uniformizer around `x` is a fully faithful embedding
`Ψ_x ◦ G_x ⋉ U(x) → X`, `U(x)` with the natural action, inducing a homeomorphism of
`|U(x)|_{G_x ⋉ U(x)}` onto the open neighbourhood `|U(x)| = π(U(x))` of `π(x)`.  (p. 237) There
exists a local uniformizer around every object, as Proposition 7.1.19 (2017: 7.6) shows; a local uniformizer is
injective on objects as well as morphisms.

## What is formalized (namespace `Polyfold.EpGroupoid`, `R : X.NaturalRep x`)

* The fibres of `π` on `U(x)`: `NaturalRep.π_eq_π_iff_exists_smul` (`|y| = |y'|` iff
  `y' = g ∗ y`; the injectivity step of the proof).
* **Proposition 7.1.19 (2017: 7.6)**: `NaturalRep.orbitQuotientMap` (`G_x ∗ y ↦ |y|` into `|X|`),
  `isOpenEmbedding_orbitQuotientMap`, `range_orbitQuotientMap` (`= π(U(x))`), and
  `proposition_7_1_19 R : G_x\U(x) ≃ₜ π(U(x))`, the text's `τ` (`proposition_7_1_19_apply_mk`).  The
  second form: `proposition_7_1_19_fullyFaithful` (the functor `NaturalRep.functor`,
  `NaturalAction.lean`, is fully faithful), `isOpenEmbedding_functor_orbitMap`,
  `range_functor_orbitMap`, `proposition_7_1_19_orbitMap : |U(x)|_{G_x ⋉ U(x)} ≃ₜ π(U(x))`, and
  `translationOrbitHomeomorph : |U(x)|_{G_x ⋉ U(x)} ≃ₜ G_x\U(x)` (the text's identification).
  The functor is an open embedding on objects and on morphisms: `isOpenEmbedding_functor_obj`,
  `isOpenEmbedding_functor_mor` (`G_x` discrete), with image `𝐔(x)` (`range_functor_mor`).
* **Definition 7.1.20 (2017: 7.9), existence** (p. 237): `NaturalRep.toLocalUniformizer` (every natural
  representation is a local uniformizer) and `exists_localUniformizer` (for every open `V ∋ x`
  there is a local uniformizer with `U(x) ⊆ V`).
* **Injectivity** (p. 237): `LocalUniformizer.injective_obj`, `LocalUniformizer.injective_mor`.
  Also `LocalUniformizer.isOpen_image` (`|U(x)|` is open), `LocalUniformizer.orbitHomeomorph`.

## Reading

* **`G_x\U(x)`** is Mathlib's `MulAction.orbitRel.Quotient (X.Isotropy x) R.U` with the quotient
  topology, for the action `g • y = Φ(g)(y)` of `EpGroupoid.lean`; `|U(x)| = π(U(x))` is the
  subspace `X.π '' R.U` of `|X|`.  "`U(x)` equipped with the natural `G_x`-action" is a
  `NaturalRep` datum (PLAN II.5, 6).
* **The proof** follows the text: injectivity by Theorem 7.1.13 (2017: 7.1) (3) (`existsUnique_Γ`), openness
  through Proposition 7.1.8 (2017: 7.1) (`proposition_7_1_8`).  The openness of `σ` is not needed: the image of an
  open `Q ⊆ G_x\U(x)` is `π(σ⁻¹(Q))`, and `σ⁻¹(Q)` is open in the open `U(x)`, so `τ` (into `|X|`)
  is a continuous injective open map, an open embedding with range `π(U(x))`.  The same argument
  gives the second form, for the orbit space of the translation groupoid `G_x ⋉ U(x)`
  (`NaturalRep.translationGroupoid`), whose classes are the same `G_x`-orbits.
* **"Fully faithful"** is Mathlib's `Functor.FullyFaithful` of `GroupoidFunctor.toFunctor` (the
  bridge `GroupoidStr.Ob`), from the instances `NaturalRep.full`, `NaturalRep.faithful` of
  `NaturalAction.lean` (Theorem 7.1.13 (2017: 7.1) (3)).
* **Definition 7.1.20 (2017: 7.9)** (`EpGroupoid.lean`): the text's "`Ψx ◦ Gx ⋉ U(x) → X`" is read as
  `Ψ_x : G_x ⋉ U(x) → X` (possible misprint).  "Embedding" is not a separate field of
  `LocalUniformizer`: the injectivity on objects and morphisms that the text notes afterwards
  follows from `Ψ_x` being the inclusion on objects and faithful (`injective_obj`,
  `injective_mor`).  Read topologically, it holds for the local uniformizers built from natural
  representations (`toLocalUniformizer`): `Ψ_x` is an open embedding on objects and on morphisms
  (`isOpenEmbedding_functor_obj`, `isOpenEmbedding_functor_mor`).
* **"There exists a local uniformizer around every object"** is proved in the stronger form
  inside every open `V ∋ x` (`exists_localUniformizer`), from Theorem 7.1.13 (2017: 7.1) (`theorem_7_1_13`).
* No hypothesis "for all …" is added.  No possible misprint other than Definition 7.1.20 (2017: 7.9)'s was found
  on pp. 236–237, apart from the doubled article in "a a local uniformizer" (p. 237).
-/

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {x : Obj}

namespace NaturalRep

variable (R : X.NaturalRep x)

/-! ### The fibres of `π` on `U(x)` are the `G_x`-orbits -/

/-- **`|y| = |z|` for `y, z ∈ U(x)` iff `z = g ∗ y` for some `g ∈ G_x`** (the injectivity step of
the proof of Proposition 7.1.19 (2017: 7.6), by Theorem 7.1.13 (2017: 7.1) (3)). -/
theorem π_eq_π_iff_exists_smul {y z : R.U} :
    X.π y = X.π z ↔ ∃ g : X.Isotropy x, g • y = z := by
  constructor
  · intro h
    obtain ⟨φ, hφs, hφt⟩ := (X.π_eq_π_iff).1 h
    obtain ⟨g, hg, -⟩ := R.existsUnique_Γ φ (by rw [hφs]; exact y.2) (by rw [hφt]; exact z.2)
    refine ⟨g, Subtype.ext ?_⟩
    rw [smul_val, ← R.tgt_Γ g y y.2, ← hφs, hg, hφt]
  · rintro ⟨g, rfl⟩
    exact (X.π_eq_π_iff).2 ⟨R.Γ g y, R.src_Γ g y y.2, R.tgt_Γ g y y.2⟩

/-- A quotient of `U(x)` whose classes are the fibres of `π|U(x)` maps by `[y] ↦ |y|` as an open
embedding into `|X|`. -/
private theorem isOpenEmbedding_quotient_lift {r : Setoid R.U}
    (hr : ∀ y z : R.U, r y z ↔ X.π y = X.π z) :
    IsOpenEmbedding (Quotient.lift (fun y : R.U => X.π y) fun y z h => (hr y z).1 h) := by
  refine .of_continuous_injective_isOpenMap
    ((X.continuous_π.comp continuous_subtype_val).quotient_lift _) (fun q q' h => ?_)
    fun S hS => ?_
  · induction q using Quotient.inductionOn with | h y => ?_
    induction q' using Quotient.inductionOn with | h z => ?_
    exact Quotient.sound ((hr y z).2 h)
  · have himage : Quotient.lift (fun y : R.U => X.π y) (fun y z h => (hr y z).1 h) '' S =
        X.π '' (Subtype.val '' (Quotient.mk r ⁻¹' S)) := by
      ext w
      constructor
      · rintro ⟨q, hq, rfl⟩
        induction q using Quotient.inductionOn with | h y => ?_
        exact ⟨y, ⟨y, hq, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨Quotient.mk r y, hy, rfl⟩
    rw [himage]
    exact X.proposition_7_1_8 _ (R.isOpen_U.isOpenMap_subtype_val _
      (hS.preimage continuous_quotient_mk'))

/-- The range of `[y] ↦ |y|` is `π(U(x))`. -/
private theorem range_quotient_lift {r : Setoid R.U}
    (hr : ∀ y z : R.U, r y z ↔ X.π y = X.π z) :
    range (Quotient.lift (fun y : R.U => X.π y) fun y z h => (hr y z).1 h) = X.π '' R.U := by
  ext w
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with | h y => ?_
    exact ⟨y, y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Quotient.mk r ⟨y, hy⟩, rfl⟩

/-- The relation of `G_x\U(x)` is the relation `|y| = |z|`. -/
private theorem orbitRel_iff (y z : R.U) :
    MulAction.orbitRel (X.Isotropy x) R.U y z ↔ X.π y = X.π z := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, eq_comm, R.π_eq_π_iff_exists_smul]

/-- The relation of the orbit space of `G_x ⋉ U(x)` is the relation `|y| = |z|`. -/
private theorem translation_orbitSetoid_iff (y z : R.U) :
    R.translationGroupoid.orbitSetoid y z ↔ X.π y = X.π z := by
  rw [R.π_eq_π_iff_exists_smul]
  constructor
  · rintro ⟨p, rfl, rfl⟩
    exact ⟨p.1, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨(g, y), rfl, rfl⟩

/-! ### Proposition 7.1.19 (2017: 7.6) -/

/-- **The map `τ` of Proposition 7.1.19 (2017: 7.6)**, into `|X|`: `G_x ∗ y ↦ |y|`. -/
def orbitQuotientMap : MulAction.orbitRel.Quotient (X.Isotropy x) R.U → X.OrbitSpace :=
  Quotient.lift (fun y : R.U => X.π y) fun y z h => (R.orbitRel_iff y z).1 h

@[simp]
theorem orbitQuotientMap_mk (y : R.U) :
    R.orbitQuotientMap (Quotient.mk _ y) = X.π y :=
  rfl

/-- `τ` is an open embedding into `|X|`. -/
theorem isOpenEmbedding_orbitQuotientMap : IsOpenEmbedding R.orbitQuotientMap :=
  R.isOpenEmbedding_quotient_lift R.orbitRel_iff

/-- The range of `τ` is `|U(x)| = π(U(x))`. -/
theorem range_orbitQuotientMap : range R.orbitQuotientMap = X.π '' R.U :=
  R.range_quotient_lift R.orbitRel_iff

/-! ### The functor `G_x ⋉ U(x) → X` on orbit spaces -/

theorem functor_orbitMap_eq :
    R.functor.orbitMap = Quotient.lift (fun y : R.U => X.π y)
      fun y z h => (R.translation_orbitSetoid_iff y z).1 h := by
  funext q
  induction q using Quotient.inductionOn with | h y => ?_
  rfl

/-- **The functor `G_x ⋉ U(x) → X` induces an open embedding of orbit spaces.** -/
theorem isOpenEmbedding_functor_orbitMap : IsOpenEmbedding R.functor.orbitMap := by
  rw [functor_orbitMap_eq]
  exact R.isOpenEmbedding_quotient_lift R.translation_orbitSetoid_iff

/-- The range of `|G_x ⋉ U(x)| → |X|` is `|U(x)| = π(U(x))`. -/
theorem range_functor_orbitMap : range R.functor.orbitMap = X.π '' R.U := by
  rw [functor_orbitMap_eq]
  exact R.range_quotient_lift R.translation_orbitSetoid_iff

/-! ### The functor `G_x ⋉ U(x) → X` is an embedding -/

/-- On objects, `G_x ⋉ U(x) → X` is the inclusion of the open `U(x)`, an open embedding. -/
theorem isOpenEmbedding_functor_obj : IsOpenEmbedding R.functor.obj :=
  R.isOpen_U.isOpenEmbedding_subtypeVal

open scoped Polyfold.EpGroupoid.NaturalRep in
/-- **On morphisms, `G_x ⋉ U(x) → X`, `(g, y) ↦ Γ(g, y)`, is an open embedding** (`G_x`
discrete): continuous on each sheet `{g} × U`, injective by Theorem 7.1.13 (2017: 7.1) (3), and the image of an
open `S` is `⋃_g Γ(g, U) ∩ s⁻¹(S_g)`, `S_g = {y | (g, y) ∈ S}`. -/
theorem isOpenEmbedding_functor_mor : IsOpenEmbedding R.functor.mor := by
  refine .of_continuous_injective_isOpenMap ?_ (fun p q h => ?_) fun S hS => ?_
  · exact continuous_prod_of_discrete_left.2 fun g =>
      (R.continuousOn_Γ g).comp_continuous continuous_subtype_val fun y => y.2
  · have h' : R.Γ p.1 p.2 = R.Γ q.1 q.2 := h
    have h2 : p.2 = q.2 := Subtype.ext (by
      rw [← R.src_Γ p.1 p.2 p.2.2, ← R.src_Γ q.1 q.2 q.2.2, h'])
    rw [h2] at h'
    exact Prod.ext ((R.Γ_inj q.2.2).1 h') h2
  · have himage : R.functor.mor '' S =
        ⋃ g, R.Γ g '' R.U ∩ X.src ⁻¹' (Subtype.val '' (Prod.mk g ⁻¹' S)) := by
      ext φ
      constructor
      · rintro ⟨p, hp, rfl⟩
        refine mem_iUnion.2 ⟨p.1, ⟨p.2, p.2.2, rfl⟩, p.2, hp, ?_⟩
        exact (R.src_Γ p.1 p.2 p.2.2).symm
      · intro hφ
        obtain ⟨g, ⟨y, hy, rfl⟩, y', hy', hy'y⟩ := mem_iUnion.1 hφ
        rw [R.src_Γ g y hy] at hy'y
        exact ⟨(g, y'), hy', by rw [functor_mor, hy'y]⟩
    rw [himage]
    exact isOpen_iUnion fun g => (R.isOpen_image_Γ g).inter
      ((R.isOpen_U.isOpenMap_subtype_val _
        (hS.preimage (continuous_const.prodMk continuous_id))).preimage X.continuous_src)

/-- The image of `G_x ⋉ U(x) → X` on morphisms is `𝐔(x)`, the morphisms between points of
`U(x)` (Theorem 7.1.13 (2017: 7.1) (3)). -/
theorem range_functor_mor : range R.functor.mor = X.morOn R.U := by
  ext φ
  constructor
  · rintro ⟨p, rfl⟩
    exact R.Γ_mem_morOn p.1 p.2.2
  · intro hφ
    obtain ⟨h, hh⟩ := R.exists_Γ_eq hφ
    exact ⟨(h, ⟨X.src φ, hφ.1⟩), hh⟩

end NaturalRep

/-- **Proposition 7.1.19 (2017: 7.6)**: `τ : G_x\U(x) → |U(x)| = π(U(x))`, `G_x ∗ y ↦ |y|`, is a
homeomorphism. -/
def proposition_7_1_19 (R : X.NaturalRep x) :
    MulAction.orbitRel.Quotient (X.Isotropy x) R.U ≃ₜ X.π '' R.U :=
  R.isOpenEmbedding_orbitQuotientMap.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr R.range_orbitQuotientMap)

@[simp]
theorem proposition_7_1_19_apply_mk (R : X.NaturalRep x) (y : R.U) :
    (proposition_7_1_19 R (Quotient.mk _ y) : X.OrbitSpace) = X.π y :=
  rfl

/-- **Proposition 7.1.19 (2017: 7.6), second form**: the functor `G_x ⋉ U(x) → X` (the inclusion on objects,
`(g, y) ↦ Γ(g, y)` on morphisms) is fully faithful. -/
def proposition_7_1_19_fullyFaithful (R : X.NaturalRep x) : R.functor.toFunctor.FullyFaithful :=
  .ofFullyFaithful _

/-- **Proposition 7.1.19 (2017: 7.6), second form**: the functor `G_x ⋉ U(x) → X` induces a homeomorphism
`|U(x)|_{G_x ⋉ U(x)} → |U(x)| = π(U(x))`. -/
def proposition_7_1_19_orbitMap (R : X.NaturalRep x) :
    R.translationGroupoid.OrbitSpace ≃ₜ X.π '' R.U :=
  R.isOpenEmbedding_functor_orbitMap.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr R.range_functor_orbitMap)

@[simp]
theorem proposition_7_1_19_orbitMap_apply (R : X.NaturalRep x) (y : R.U) :
    (proposition_7_1_19_orbitMap R (R.translationGroupoid.π y) : X.OrbitSpace) = X.π y :=
  rfl

/-- The text's identification `|U(x)|_{G_x ⋉ U(x)} = G_x\U(x)` (p. 236), `|y| ↦ G_x ∗ y`. -/
def translationOrbitHomeomorph (R : X.NaturalRep x) :
    R.translationGroupoid.OrbitSpace ≃ₜ MulAction.orbitRel.Quotient (X.Isotropy x) R.U :=
  (proposition_7_1_19_orbitMap R).trans (proposition_7_1_19 R).symm

@[simp]
theorem translationOrbitHomeomorph_apply (R : X.NaturalRep x) (y : R.U) :
    translationOrbitHomeomorph R (R.translationGroupoid.π y) = Quotient.mk _ y := by
  refine (proposition_7_1_19 R).injective ?_
  rw [translationOrbitHomeomorph, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  exact Subtype.ext rfl

/-! ### Definition 7.1.20 (2017: 7.9): existence of local uniformizers -/

/-- **A natural representation is a local uniformizer** (p. 237: "as Proposition 7.6 shows"),
with `Ψ_x` the functor `G_x ⋉ U(x) → X` of `NaturalAction.lean`. -/
def NaturalRep.toLocalUniformizer (R : X.NaturalRep x) : X.LocalUniformizer x where
  rep := R
  Ψ := R.functor
  obj_eq _ := rfl
  full := R.full
  faithful := R.faithful
  isEmbedding_orbitMap := R.isOpenEmbedding_functor_orbitMap.isEmbedding
  range_orbitMap := R.range_functor_orbitMap

@[simp]
theorem NaturalRep.toLocalUniformizer_rep (R : X.NaturalRep x) : R.toLocalUniformizer.rep = R :=
  rfl

variable (X) in
/-- **There exists a local uniformizer around every object** (p. 237), inside every open
neighbourhood `V` of `x`. -/
theorem exists_localUniformizer (x : Obj) {V : Set Obj} (hV : IsOpen V) (hx : x ∈ V) :
    ∃ L : X.LocalUniformizer x, L.rep.U ⊆ V := by
  obtain ⟨R, hRV⟩ := theorem_7_1_13 X x hV hx
  exact ⟨R.toLocalUniformizer, hRV⟩

/-! ### Local uniformizers are injective on objects and morphisms -/

namespace LocalUniformizer

variable (L : X.LocalUniformizer x)

/-- **A local uniformizer is injective on objects** (p. 237). -/
theorem injective_obj : Function.Injective L.Ψ.obj := fun y z h =>
  Subtype.ext (by rw [← L.obj_eq, ← L.obj_eq, h])

/-- **A local uniformizer is injective on morphisms** (p. 237): two morphisms with the same image
have the same source and target (injectivity on objects) and are equal by faithfulness. -/
theorem injective_mor : Function.Injective L.Ψ.mor := by
  intro p q h
  let G := L.rep.translationGroupoid
  have hs : G.src q = G.src p := L.injective_obj (by rw [← L.Ψ.src_mor, ← L.Ψ.src_mor, h])
  have ht : G.tgt q = G.tgt p := L.injective_obj (by rw [← L.Ψ.tgt_mor, ← L.Ψ.tgt_mor, h])
  have := L.faithful
  have he := L.Ψ.toFunctor.map_injective (X := G.toOb (G.src p)) (Y := G.toOb (G.tgt p))
    (a₁ := G.homMk p rfl rfl) (a₂ := G.homMk q hs ht) (Subtype.ext h)
  exact congrArg Subtype.val he

/-- `|U(x)| = π(U(x))` is an open neighbourhood of `π(x)` (Proposition 7.1.8 (2017: 7.1)). -/
theorem isOpen_image : IsOpen (X.π '' L.rep.U) :=
  X.proposition_7_1_8 _ L.rep.isOpen_U

theorem mem_image : X.π x ∈ X.π '' L.rep.U := mem_image_of_mem _ L.rep.mem_U

/-- The homeomorphism `|U(x)|_{G_x ⋉ U(x)} → |U(x)|` of Definition 7.1.20 (2017: 7.9) induced by `Ψ_x`. -/
def orbitHomeomorph : L.rep.translationGroupoid.OrbitSpace ≃ₜ X.π '' L.rep.U :=
  L.isEmbedding_orbitMap.toHomeomorph.trans (Homeomorph.setCongr L.range_orbitMap)

@[simp]
theorem orbitHomeomorph_apply (q : L.rep.translationGroupoid.OrbitSpace) :
    (L.orbitHomeomorph q : X.OrbitSpace) = L.Ψ.orbitMap q :=
  rfl

end LocalUniformizer

end EpGroupoid

end Polyfold
