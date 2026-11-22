import Polyfold.Chapter17.ProperCoveringModel

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8:
**Definition 17.8.3** (p. 829, `Diff*_sc`) and the construction of pp. 829–831, (17.93)–(17.98):
the ep-groupoid `E` and the functor `τ̂ : E → G_β ⋉ O_β` of data `A, B, τ` ("a trivial exercise").
Numbers and pages are the 2021 text's.

# Pointed geometric lifts and their proper covering models

## The text, paraphrased

(Definition 17.8.3) `Diff*_sc`: objects pairs `(O, o)`, `O` an M-polyfold and `o ∈ O`; morphisms
sc-diffeomorphisms preserving the distinguished points.  (pp. 829–830) The data: functors
`A : A_β → Diff*_sc`, `B : G_β ⋉ {β} → Diff*_sc` and a natural transformation `τ : A → B ∘ P_β`,
`P_β : A_β → G_β ⋉ {β}` the covering functor (17.93) of the full subcategory `A_β` on `P⁻¹(β)`.
`B` gives `G_β ⋉ O_β` with `g ∗ o_β = o_β`; `A` gives `(O_α, o_α)` and `φ ∗ : O_α → O_α'`.  (17.94)
`E = ⊔ O_α`, (17.95) `𝐄 = ⊔ {φ} × O_{s(φ)}`, `s(φ, o) = o`, `t(φ, o) = φ ∗ o`; "it is a trivial
exercise" that this is an ep-groupoid.  (17.96) `τ̂ : E → O_β`, `o ∈ O_α ↦ τ_α(o)`, a local
sc-diffeomorphism with `τ̂⁻¹(o_β) = {o_α}`; (17.97) `τ̂(φ, o) = (P_β(φ), τ̂(o))`; (17.98) `τ̂` is a
functor, and `(φ, o) ↦ ((P_β(φ), τ̂(o)), o)` is an sc-diffeomorphism `𝐄 → mor(G_β ⋉ O_β) ₛ×_τ̂ E`:
`τ̂` is a proper covering map of ep-groupoids, a geometric lift of `P_β`.

## What is formalized

* **Definition 17.8.3**: `PointedMPolyfoldCat` (objects `(O, o)`), `PointedScDiffeo`, the category
  instance, and the forgetful functor `PointedMPolyfoldCat.forget : Diff*_sc → Diff_sc`.
* **The data (i), (ii)**: `PointedGeometricLift f` for a functor `f : D → SingleObj G` (`D = A_β`,
  `G = G_β`): `A`, `B`, `τ`; `toGeometricLift` forgets the points (Definition 8.5.5).
  `basePt` (`o_β`), `smul_basePt` (`g ∗ o_β = o_β`), `τy_pt` (`τ_α(o_α) = o_β`).
* **(17.94)–(17.98) and the "trivial exercise"**: `E` and `τ̂` are Chapter 8's
  `geometricLiftSource` and `geometricLiftFunctor` (Proposition 8.5.7) of `toGeometricLift`.
  `pointedModel hf L`: **`τ̂` is a proper covering model** (Definition 17.8.4) with distinguished
  point `o_β` and `U(⟨α, o_α⟩) = O_α`; `pointedModel_fiber` (`τ̂⁻¹(o_β) = {o_α}`, (17.96));
  `pointed_isProperCovering` (`τ̂` is a proper covering functor of ep-groupoids, Definition 8.5.1).
* Witness: `pointedModel_reflection` (`reflectionPointedLift`): `A = B` the reflection of `ℝ`
  pointed at `0` over `𝟭 : ℤ/2 ⋉ {β} → ℤ/2 ⋉ {β}` (`isCoveringFunctor_id_units`), a nontrivial
  group action (`pointedModel_reflection_nondegenerate`).

## Readings

* `G_β ⋉ {β}` is `SingleObj G` (as in Definition 8.5.5); the covering functor `P_β` is
  `IsCoveringFunctor f`; "finitely many objects" are `[Fintype D] [∀ a b, Fintype (a ⟶ b)]`, `G`
  finite and discrete; `D` nonempty (`P⁻¹(β) ≠ ∅`, from the surjectivity of `P` in Definition
  17.8.1 (2)).  Chapter 8 lifts `G` to `ULift G` (its translation groupoid takes the group and the
  space in one universe), so the target of `τ̂` is `ULift G ⋉ O_β`.
* `𝐄 = ⊔ {φ} × O_{s(φ)}` is `Σ φ, O_{s φ}`; `t(φ, o) = φ ∗ o` is Chapter 8's `yTgt`.
-/

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

open EpGroupoid EpGroupoid.Examples GeometricLift

universe u

/-! ### Definition 17.8.3: `Diff*_sc` -/

/-- **Definition 17.8.3**: an object of `Diff*_sc`, an M-polyfold `O` with a distinguished point
`o ∈ O`. -/
structure PointedMPolyfoldCat : Type (u + 1) where
  /-- The M-polyfold `O`. -/
  obj : MPolyfoldCat.{u}
  /-- The distinguished point `o`. -/
  pt : obj.carrier

/-- **Definition 17.8.3**: a morphism `f : (O, o) → (O', o')` of `Diff*_sc`, an sc-diffeomorphism
with `f(o) = o'`. -/
structure PointedScDiffeo (A B : PointedMPolyfoldCat.{u}) where
  /-- The sc-diffeomorphism. -/
  toScDiffeo : ScDiffeo A.obj B.obj
  map_pt : toScDiffeo.toFun A.pt = B.pt

namespace PointedScDiffeo

theorem ext {A B : PointedMPolyfoldCat.{u}} {f g : PointedScDiffeo A B}
    (h : f.toScDiffeo.toFun = g.toScDiffeo.toFun) : f = g := by
  cases f; cases g
  cases ScDiffeo.ext h
  rfl

end PointedScDiffeo

/-- **`Diff*_sc`** (Definition 17.8.3): pointed M-polyfolds and point-preserving
sc-diffeomorphisms. -/
instance : Category PointedMPolyfoldCat.{u} where
  Hom A B := PointedScDiffeo A B
  id A := ⟨ScDiffeo.id A.obj, rfl⟩
  comp f g := ⟨ScDiffeo.comp f.toScDiffeo g.toScDiffeo, by
    change g.toScDiffeo.toFun (f.toScDiffeo.toFun _) = _
    rw [f.map_pt, g.map_pt]⟩
  id_comp _ := PointedScDiffeo.ext rfl
  comp_id _ := PointedScDiffeo.ext rfl
  assoc _ _ _ := PointedScDiffeo.ext rfl

/-- The forgetful functor `Diff*_sc → Diff_sc`. -/
def PointedMPolyfoldCat.forget : PointedMPolyfoldCat.{u} ⥤ MPolyfoldCat.{u} where
  obj A := A.obj
  map f := f.toScDiffeo

theorem PointedMPolyfoldCat.map_pt {A B : PointedMPolyfoldCat.{u}} (f : A ⟶ B) :
    f.toScDiffeo.toFun A.pt = B.pt := f.map_pt

/-! ### The data `A, B, τ` -/

variable {D : Type u} [Groupoid.{u} D] {G : Type u} [Group G]

/-- **The data (i), (ii) of p. 829**: functors `A : A_β → Diff*_sc`, `B : G_β ⋉ {β} → Diff*_sc`
and a natural transformation `τ : A → B ∘ P_β`, for `P_β = f : D → SingleObj G`. -/
structure PointedGeometricLift (f : D ⥤ SingleObj G) where
  /-- `A : α ↦ (O_α, o_α)`, `φ ↦ φ ∗`. -/
  A : D ⥤ PointedMPolyfoldCat.{u}
  /-- `B : β ↦ (O_β, o_β)`, `g ↦ g ∗`. -/
  B : SingleObj G ⥤ PointedMPolyfoldCat.{u}
  /-- `τ_α : (O_α, o_α) → (O_β, o_β)`. -/
  τ : A ⟶ f ⋙ B

namespace PointedGeometricLift

variable {f : D ⥤ SingleObj G} (L : PointedGeometricLift f)

/-- The geometric lift of Definition 8.5.5 obtained by forgetting the points. -/
def toGeometricLift : GeometricLift f where
  LD := L.A ⋙ PointedMPolyfoldCat.forget
  LC := L.B ⋙ PointedMPolyfoldCat.forget
  τ := Functor.whiskerRight L.τ PointedMPolyfoldCat.forget

/-- The distinguished point `o_β ∈ O_β`. -/
def basePt : L.toGeometricLift.Ux := (L.B.obj (SingleObj.star G)).pt

open GeometricLift in
/-- `g ∗ o_β = o_β`. -/
theorem smul_basePt (g : G) : g • L.basePt = L.basePt :=
  (L.B.map (g : SingleObj.star G ⟶ SingleObj.star G)).map_pt

/-- `τ_α(o_α) = o_β`. -/
theorem τy_pt (y : D) : L.toGeometricLift.τy y (L.A.obj y).pt = L.basePt :=
  (L.τ.app y).map_pt

theorem τy_injective (y : D) : Injective (L.toGeometricLift.τy y) := fun a b h => by
  rw [← L.toGeometricLift.τyInv_τy y a, h, L.toGeometricLift.τyInv_τy]

end PointedGeometricLift

/-! ### (17.94)–(17.98): the proper covering model -/

section Model

variable [Fintype D] [∀ a b : D, Fintype (a ⟶ b)] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] {f : D ⥤ SingleObj G} (L : PointedGeometricLift f)

namespace PointedGeometricLift

/-- A point of `E = ⊔ O_α` over `o_β` is a distinguished point `o_α`. -/
theorem eq_pt_of_mem {y : L.toGeometricLift.YObj}
    (hy : (geometricLiftFunctor L.toGeometricLift).obj y = L.basePt) :
    y = ⟨y.1, (L.A.obj y.1).pt⟩ := by
  obtain ⟨d, z⟩ := y
  have : z = (L.A.obj d).pt := L.τy_injective d (by
    rw [L.τy_pt]
    exact hy)
  rw [this]

open GeometricLift in
/-- `τ̂ = τ_α ∘ sigmaProj` is an sc-diffeomorphism `O_α → O_β` on the summand `O_α`. -/
theorem isScDiffeoOn_obj_summand (d : D) (z₀ : (L.toGeometricLift.LD.obj d).carrier) :
    (geometricLiftSource L.toGeometricLift).PObj.IsScDiffeoOn
      (geometricLiftTarget L.toGeometricLift).PObj
      (geometricLiftFunctor L.toGeometricLift).obj
      (fun o => (⟨d, L.toGeometricLift.τyInv d o⟩ : L.toGeometricLift.YObj))
      (range (Sigma.mk d)) univ := by
  have h1 := (MPolyfold.isScDiffeoOn_sigmaMk (fun y : D => (L.toGeometricLift.LD.obj y).P) d
    z₀).symm
  have h2 := L.toGeometricLift.isScDiffeoOn_τy d
  refine
    { isScSmoothOn := (MPolyfold.IsScSmoothOn.comp h2.isScSmoothOn h1.isScSmoothOn
        h1.mapsTo).congr fun p hp => ?_
      isScSmoothOn_inv := MPolyfold.IsScSmoothOn.comp h1.isScSmoothOn_inv h2.isScSmoothOn_inv
        h2.mapsTo_inv
      mapsTo := mapsTo_univ _ _
      mapsTo_inv := fun o _ => mem_range_self _
      left_inv := fun p hp => ?_
      right_inv := fun o _ => L.toGeometricLift.τy_τyInv d o }
  · obtain ⟨z, rfl⟩ := hp
    simp only [Function.comp_apply, sigmaProj_mk]
    rfl
  · obtain ⟨z, rfl⟩ := hp
    change (⟨d, L.toGeometricLift.τyInv d (L.toGeometricLift.τy d z)⟩ :
      L.toGeometricLift.YObj) = ⟨d, z⟩
    rw [L.toGeometricLift.τyInv_τy]

end PointedGeometricLift

/-- **The construction of pp. 829–831 is a proper covering model** (Definition 17.8.4): the functor
`τ̂ : E → G_β ⋉ O_β` of (17.98), `E = ⊔ O_α` (17.94), `𝐄 = ⊔ {φ} × O_{s φ}` (17.95), with
distinguished point `o_β` and `U(⟨α, o_α⟩) = O_α`.  That `E` is an ep-groupoid and `τ̂` an
sc-smooth functor with `Γ` an sc-diffeomorphism (the "trivial exercise") is Proposition 8.5.7
(`geometricLiftSource`, `geometricLiftFunctor_isScDiffeo_fibredMap`). -/
def pointedModel [Nonempty D] (hf : IsCoveringFunctor f) :
    ProperCoveringModel (hP := L.toGeometricLift.isScSmoothMap_smul)
      (geometricLiftFunctor L.toGeometricLift) where
  pt := L.basePt
  smul_pt g := L.smul_basePt g.down
  surjective := (proposition_8_5_7 hf L.toGeometricLift).surjective
  isLocalScDiffeo := (proposition_8_5_7 hf L.toGeometricLift).isLocalScDiffeo
  U y := range (Sigma.mk y.1)
  σ y o := ⟨y.1, L.toGeometricLift.τyInv y.1 o⟩
  mem_U y _ := ⟨y.2, rfl⟩
  pairwiseDisjoint_U y hy y' hy' hne := by
    refine disjoint_range_sigmaMk fun h => hne ?_
    rw [L.eq_pt_of_mem hy, L.eq_pt_of_mem hy']
    obtain ⟨d, z⟩ := y
    obtain ⟨d', z'⟩ := y'
    cases (h : d = d')
    rfl
  iUnion_U := by
    refine eq_univ_of_forall fun p => ?_
    simp only [mem_iUnion, exists_prop]
    exact ⟨⟨p.1, (L.A.obj p.1).pt⟩, L.τy_pt p.1, p.2, rfl⟩
  isScDiffeoOn_U y _ := L.isScDiffeoOn_obj_summand y.1 y.2
  isScDiffeo_fibredMap := geometricLiftFunctor_isScDiffeo_fibredMap L.toGeometricLift hf

/-- **(17.96)**: `τ̂⁻¹(o_β)` consists of the distinguished points `o_α`, `α ∈ A_β`. -/
theorem pointedModel_fiber [Nonempty D] (hf : IsCoveringFunctor f) :
    (pointedModel L hf).fiber =
      range fun d : D => (⟨d, (L.A.obj d).pt⟩ : L.toGeometricLift.YObj) := by
  ext y
  refine ⟨fun hy => ⟨y.1, (L.eq_pt_of_mem hy).symm⟩, ?_⟩
  rintro ⟨d, rfl⟩
  exact L.τy_pt d

/-- **`τ̂ : E → G_β ⋉ O_β` is a proper covering functor of ep-groupoids** (Definition 8.5.1),
p. 831: Proposition 8.5.7, or Remark 17.8.5 with the finite fibre `{o_α}`. -/
theorem pointed_isProperCovering [Nonempty D] (hf : IsCoveringFunctor f) :
    (geometricLiftFunctor L.toGeometricLift).IsProperCovering :=
  (pointedModel L hf).isProperCovering (by
    rw [pointedModel_fiber]
    exact finite_range _)

end Model

/-! ### Witness: `ℤ/2` acting on `ℝ` by the reflection -/

section Witness

/-- The reflection `y ↦ k • y` of `ℝ` as an sc-diffeomorphism. -/
def reflectionScDiffeo (k : ℤˣ) :
    ScDiffeo ⟨Fin 1 → ℝ, rnPolyfold 1⟩ ⟨Fin 1 → ℝ, rnPolyfold 1⟩ where
  toFun y := k • y
  invFun y := k⁻¹ • y
  isScDiffeoOn :=
    { isScSmoothOn := isScSmoothMap_units_smul k
      isScSmoothOn_inv := isScSmoothMap_units_smul k⁻¹
      mapsTo := mapsTo_univ _ _
      mapsTo_inv := mapsTo_univ _ _
      left_inv := fun y _ => inv_smul_smul k y
      right_inv := fun y _ => smul_inv_smul k y }

/-- `B : ℤ/2 ⋉ {β} → Diff*_sc`, `β ↦ (ℝ, 0)`, `k ↦ (y ↦ k y)`. -/
def reflectionPointed : SingleObj ℤˣ ⥤ PointedMPolyfoldCat.{0} where
  obj _ := ⟨⟨Fin 1 → ℝ, rnPolyfold 1⟩, 0⟩
  map {_ _} k := ⟨reflectionScDiffeo k, smul_zero (M := ℤˣ) (A := Fin 1 → ℝ) k⟩
  map_id _ := PointedScDiffeo.ext (funext fun y => one_smul ℤˣ y)
  map_comp {_ _ _} k l := PointedScDiffeo.ext (funext fun y =>
    mul_smul (α := ℤˣ) (β := Fin 1 → ℝ) l k y)

instance : Fintype (SingleObj ℤˣ) := inferInstanceAs (Fintype Unit)

instance (a b : SingleObj ℤˣ) : Fintype (a ⟶ b) := inferInstanceAs (Fintype ℤˣ)

/-- The identity is a covering functor `ℤ/2 ⋉ {β} → ℤ/2 ⋉ {β}`. -/
theorem isCoveringFunctor_id_units : IsCoveringFunctor (𝟭 (SingleObj ℤˣ)) := by
  refine ⟨fun ψ ψ' h => ?_, fun p => ⟨⟨SingleObj.star _, SingleObj.star _, p.1⟩, rfl⟩⟩
  obtain ⟨⟨⟩, ⟨⟩, g⟩ := ψ
  obtain ⟨⟨⟩, ⟨⟩, g'⟩ := ψ'
  have : g = g' := congrArg Prod.fst h
  rw [this]

/-- **A witness for the construction**: `A = B` the reflection of `ℝ` pointed at `0`, `τ = 1`, over
the covering functor `𝟭 : ℤ/2 ⋉ {β} → ℤ/2 ⋉ {β}` (nontrivial group, `ō = 0` with isotropy `ℤ/2`). -/
def reflectionPointedLift : PointedGeometricLift (𝟭 (SingleObj ℤˣ)) where
  A := reflectionPointed
  B := reflectionPointed
  τ := 𝟙 _

/-- The proper covering model of `reflectionPointedLift`; its fibre over `o_β = 0` is one point and
the group `ℤ/2` acts nontrivially on `O_β = ℝ`. -/
def pointedModel_reflection := pointedModel reflectionPointedLift isCoveringFunctor_id_units

theorem pointedModel_reflection_nondegenerate :
    pointedModel_reflection.pt = (0 : Fin 1 → ℝ) ∧
      ∃ (k : ULift.{0} ℤˣ) (y : Fin 1 → ℝ),
        (k • (y : reflectionPointedLift.toGeometricLift.Ux) : Fin 1 → ℝ) ≠ y := by
  refine ⟨rfl, ⟨-1⟩, (fun _ => (1 : ℝ)), fun h => ?_⟩
  have := congrFun h 0
  change ((-1 : ℤˣ) • (fun _ => (1 : ℝ)) : Fin 1 → ℝ) 0 = 1 at this
  rw [units_smul_rn_neg_one] at this
  norm_num at this

end Witness

end Polyfold
