import Polyfold.Chapter6.TransportOrientationSpace
import Polyfold.Chapter6.OrientationFunctor

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 6, §6.6 "Local
Orientation Propagation": **Theorem 6.6.13** (the functor `Γ_f`), pp. 273–274, and
**Definitions 6.6.14–6.6.16** (orientable sections, orientations), p. 274, for an arbitrary
family of fibres with local transport data.

# The functor of local transport data, orientability and orientations

## The text, paraphrased

(Theorem 6.6.13) For an sc-Fredholm section `f` of a strong bundle over a tame M-polyfold there
is a uniquely determined functor `Γ_f` from the category of smooth points and classes of
sc-smooth paths to the category of the two-element sets `Or_x^f`, which on the paths in the
neighbourhoods of Theorem 6.6.11 is the local propagation (property (∗)).

(Definitions 6.6.14–6.6.16) `f` is orientable if `Γ_f([φ])` depends only on the end points of
`φ`; equivalently there is a map `y ↦ o_y ∈ Or_y^f` which near every smooth point is a
continuous orientation; such a map is an orientation of `f`.

## What is formalized

The construction and the definitions use only the local transport data `L : LocalTransport PX O`
of a family `O` of sets over the smooth points (`PathTransport.lean`).  For every such `L`:

* `functorMap a : O x ≃ O y` for a morphism `a : x ⟶ y` of `PathCat PX`: the transport along a
  path of the class (`functorMap_mk`); `functorMap_id`, `functorMap_comp`; the functor
  `L.functor : PathCat PX ⥤ Type _`.
* `functorMap_hasStarProperty`: on a path in a good set, `functorMap` is the push-forward of the
  good set (property (∗)); `functorMap_unique`: a family of bijections on the morphisms which
  takes compositions to composites and has (∗) is `functorMap`;
  `existsUnique_functorMap`: **Theorem 6.6.13** for `L`.
* `IsOrientable` (Definition 6.6.14), `IsOrientation o` (Definition 6.6.16:
  `Γ([φ]) o_x = o_y` for all classes of paths), `isOrientation_iff_isContOn_univ`,
  `isOrientation_iff_forall_exists_isContOn` (Definition 6.6.15: near every smooth point `o` is
  carried along by the transport), `isOrientable_iff_exists_isOrientation`,
  `IsOrientation.apply_eq_iff`, `IsOrientation.exists_two` (on the path component of a point
  there are exactly two orientations).

The statements which count orientations assume that every `O x` has exactly two elements.
-/

set_option maxSynthPendingDepth 3

open Set CategoryTheory

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

namespace LocalTransport

variable {O : ∀ x : X, x ∈ PX.smoothSet → Type v} (L : LocalTransport PX O)

/-! ### The functor -/

/-- **The functor of local transport data on morphisms** (Theorem 6.6.13): for a class `[φ]` of
sc-smooth paths from `x` to `y`, the transport along `φ`, which depends only on the class
(`transport_eq_of_isScHomotopyRel`). -/
def functorMap {x y : PathCat PX} (a : x ⟶ y) : O x.pt x.smooth ≃ O y.pt y.smooth :=
  Quotient.lift (s := ScPath.setoid PX x.pt y.pt)
    (fun φ => L.transport φ.toFun φ.isScSmoothMap φ.source φ.target x.smooth y.smooth)
    (fun φ ψ h => by
      obtain ⟨Φ, hΦ⟩ := h
      exact L.transport_eq_of_isScHomotopyRel hΦ φ.isScSmoothMap ψ.isScSmoothMap φ.source
        φ.target x.smooth y.smooth)
    a

/-- On the class of a path `φ` the functor is the transport along `φ`. -/
theorem functorMap_mk {x y : PathCat PX} (φ : ScPath PX x.pt y.pt) :
    L.functorMap (PathCat.homMk φ) =
      L.transport φ.toFun φ.isScSmoothMap φ.source φ.target x.smooth y.smooth :=
  rfl

/-- **Identities go to identities** (`transport_const`). -/
theorem functorMap_id (x : PathCat PX) : L.functorMap (𝟙 x) = Equiv.refl _ :=
  L.transport_const _ (fun _ _ => rfl) _ _ x.smooth

/-- **Compositions go to composites** (`transport_concatPath`). -/
theorem functorMap_comp {x y z : PathCat PX} (a : x ⟶ y) (b : y ⟶ z) :
    L.functorMap (a ≫ b) = (L.functorMap a).trans (L.functorMap b) := by
  obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
  obtain ⟨ψ, rfl⟩ := PathCat.exists_eq_mk b
  exact L.transport_concatPath φ.isScSmoothMap ψ.isScSmoothMap φ.source φ.target ψ.source
    ψ.target x.smooth y.smooth z.smooth

/-- The functor on the inverse of a morphism is the inverse bijection. -/
theorem functorMap_inv {x y : PathCat PX} (a : x ⟶ y) :
    L.functorMap (Groupoid.inv a) = (L.functorMap a).symm := by
  have h : (L.functorMap a).trans (L.functorMap (Groupoid.inv a)) = Equiv.refl _ := by
    rw [← functorMap_comp, Groupoid.comp_inv, functorMap_id]
  refine Equiv.ext fun o => ?_
  have h' := DFunLike.congr_fun h ((L.functorMap a).symm o)
  rw [Equiv.trans_apply, Equiv.apply_symm_apply] at h'
  exact h'

/-- **The functor `Γ : PX → Sets`** of local transport data (Theorem 6.6.13): `x ↦ O x`,
`[φ] ↦` the transport along `φ`. -/
def functor : PathCat PX ⥤ Type v where
  obj x := O x.pt x.smooth
  map a := ↾(L.functorMap a)
  map_id x := by
    rw [functorMap_id]
    rfl
  map_comp a b := by
    rw [functorMap_comp]
    rfl

theorem functor_obj (x : PathCat PX) : L.functor.obj x = O x.pt x.smooth := rfl

theorem functor_map_apply {x y : PathCat PX} (a : x ⟶ y) (o : O x.pt x.smooth) :
    L.functor.map a o = L.functorMap a o :=
  rfl

/-! ### Property (∗) and uniqueness -/

/-- **Property (∗)** of a family of bijections on the morphisms of `PX`: on the class of an
sc-smooth path with `[0, 1]` in a good set `U` it is the push-forward of `U`. -/
def HasStarProperty
    (G : ∀ x y : PathCat PX, (x ⟶ y) → (O x.pt x.smooth ≃ O y.pt y.smooth)) : Prop :=
  ∀ {U : Set X} (hU : L.Good U) (x y : PathCat PX) (φ : ScPath PX x.pt y.pt)
    (hφ : ∀ t ∈ Icc (0 : ℝ) 1, φ.toFun (pt1 t) ∈ U),
    G x y (PathCat.homMk φ) =
      L.push hU φ.toFun φ.isScSmoothMap hφ φ.source φ.target x.smooth y.smooth

/-- **The functor has property (∗)** (`transport_eq_push`). -/
theorem functorMap_hasStarProperty : L.HasStarProperty fun _ _ a => L.functorMap a :=
  fun hU x y φ hφ =>
    L.transport_eq_push hU φ.isScSmoothMap hφ φ.source φ.target x.smooth y.smooth

/-- **Uniqueness of the functor** ("it is obvious that `Γ_f` is unique"): a family of bijections
on the morphisms of `PX` which takes compositions to composites and has property (∗) is the
functor (`transport_unique`; homotopy invariance holds on classes). -/
theorem functorMap_unique
    (G : ∀ x y : PathCat PX, (x ⟶ y) → (O x.pt x.smooth ≃ O y.pt y.smooth))
    (hG_comp : ∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
      G x z (a ≫ b) = (G x y a).trans (G y z b))
    (hG : L.HasStarProperty G) : G = fun _ _ a => L.functorMap a := by
  funext x y a
  obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
  refine L.transport_unique
    (fun γ hγ {x₀ x₁} h₀ h₁ hs₀ hs₁ => G ⟨x₀, hs₀⟩ ⟨x₁, hs₁⟩ (PathCat.homMk ⟨γ, hγ, h₀, h₁⟩))
    ?_ ?_ ?_ φ.isScSmoothMap φ.source φ.target x.smooth y.smooth
  · intro _ _ _ hΦ _ _ _ _ _ _ _ _
    exact congrArg (G _ _) (PathCat.mk_eq_mk_iff.2 ⟨_, hΦ⟩)
  · intro _ _ hγ₁ hγ₂ _ _ _ h₁₀ h₁₁ h₂₀ h₂₁ hs₀ hs₁ hs₂
    exact hG_comp ⟨_, hs₀⟩ ⟨_, hs₁⟩ ⟨_, hs₂⟩ (PathCat.homMk ⟨_, hγ₁, h₁₀, h₁₁⟩)
      (PathCat.homMk ⟨_, hγ₂, h₂₀, h₂₁⟩)
  · intro U hU γ hγ hγU x₀ x₁ h₀ h₁ hs₀ hs₁
    exact hG hU ⟨x₀, hs₀⟩ ⟨x₁, hs₁⟩ ⟨γ, hγ, h₀, h₁⟩ hγU

/-- **Theorem 6.6.13 for local transport data**: there is exactly one family of bijections
`Γ([φ]) : O x ≃ O y` on the morphisms `[φ] : x ⟶ y` of `PX` which takes identities to
identities, compositions to composites and has property (∗); it is `functorMap`. -/
theorem existsUnique_functorMap :
    ∃! G : ∀ x y : PathCat PX, (x ⟶ y) → (O x.pt x.smooth ≃ O y.pt y.smooth),
      (∀ x, G x x (𝟙 x) = Equiv.refl _) ∧
      (∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
        G x z (a ≫ b) = (G x y a).trans (G y z b)) ∧
      L.HasStarProperty G :=
  ⟨fun _ _ a => L.functorMap a,
    ⟨L.functorMap_id, fun _ _ _ => L.functorMap_comp, L.functorMap_hasStarProperty⟩,
    fun G ⟨_, hG_comp, hG⟩ => L.functorMap_unique G hG_comp hG⟩

/-! ### Orientability (Definitions 6.6.14, 6.6.15) and orientations (Definition 6.6.16) -/

/-- **Definition 6.6.14 for local transport data, orientability**: for any two morphisms
`[φ], [ψ] : x ⟶ y` of `PX`, `Γ([φ]) = Γ([ψ])`. -/
def IsOrientable : Prop :=
  ∀ (x y : PathCat PX) (a b : x ⟶ y), L.functorMap a = L.functorMap b

/-- **Definition 6.6.16 for local transport data, orientation**: a map `y ↦ o_y ∈ O y` with
`Γ([φ]) o_x = o_y` for every morphism `[φ] : x ⟶ y` of `PX`. -/
def IsOrientation (o : ∀ y (hy : y ∈ PX.smoothSet), O y hy) : Prop :=
  ∀ (x y : PathCat PX) (a : x ⟶ y), L.functorMap a (o x.pt x.smooth) = o y.pt y.smooth

variable {L}

/-- **An orientation is a map carried along by the transport along every sc-smooth path.** -/
theorem isOrientation_iff_isContOn_univ (o : ∀ y (hy : y ∈ PX.smoothSet), O y hy) :
    L.IsOrientation o ↔ L.IsContOn univ o := by
  constructor
  · intro h
    exact ⟨isOpen_univ, fun γ hγ _ x₀ x₁ h₀ h₁ hs₀ hs₁ =>
      h ⟨x₀, hs₀⟩ ⟨x₁, hs₁⟩ (PathCat.homMk ⟨γ, hγ, h₀, h₁⟩)⟩
  · intro h x y a
    obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
    exact h.2 φ.toFun φ.isScSmoothMap (fun _ _ => mem_univ _) φ.source φ.target x.smooth
      y.smooth

/-- **Definition 6.6.15 for local transport data**: `o` is an orientation iff every smooth point
has an open neighbourhood over which `o` is carried along by the transport (a continuous
orientation over the neighbourhood). -/
theorem isOrientation_iff_forall_exists_isContOn (o : ∀ y (hy : y ∈ PX.smoothSet), O y hy) :
    L.IsOrientation o ↔ ∀ x ∈ PX.smoothSet, ∃ V : Set X, x ∈ V ∧ L.IsContOn V o :=
  (isOrientation_iff_isContOn_univ o).trans
    ⟨fun h x _ => ⟨univ, mem_univ x, h⟩,
      fun h => isContOn_of_local isOpen_univ fun x _ hx => h x hx⟩

/-- **From orientability to an orientation**: in each class of smooth points joined by sc-smooth
paths a base point and an element of its fibre are chosen and carried along (the fibres are
assumed non-empty). -/
theorem IsOrientable.exists_isOrientation (h : L.IsOrientable)
    (hne : ∀ y (hy : y ∈ PX.smoothSet), Nonempty (O y hy)) :
    ∃ o : ∀ y (hy : y ∈ PX.smoothSet), O y hy, L.IsOrientation o := by
  let base : PathCat PX → PathCat PX := fun y => (Quotient.mk (scPathSetoid PX) y).out
  have hbase : ∀ y, Nonempty (base y ⟶ y) := fun y => Quotient.mk_out (s := scPathSetoid PX) y
  let ob : ∀ z : PathCat PX, O z.pt z.smooth := fun z => (hne z.pt z.smooth).some
  refine ⟨fun y hy => L.functorMap (hbase ⟨y, hy⟩).some (ob (base ⟨y, hy⟩)), fun x y a => ?_⟩
  have hb : base x = base y := congrArg Quotient.out (Quotient.sound (s := scPathSetoid PX) ⟨a⟩)
  have key : ∀ b₁ b₂ : PathCat PX, b₁ = b₂ → ∀ (p₁ : b₁ ⟶ x) (p₂ : b₂ ⟶ y),
      L.functorMap a (L.functorMap p₁ (ob b₁)) = L.functorMap p₂ (ob b₂) := by
    rintro b _ rfl p₁ p₂
    rw [← Equiv.trans_apply, ← functorMap_comp, h _ _ (p₁ ≫ a) p₂]
  exact key _ _ hb _ _

/-- **From an orientation to orientability**, when the fibres have exactly two elements: two
bijections onto a two-element set which agree at one point agree. -/
theorem IsOrientation.isOrientable {o : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (ho : L.IsOrientation o)
    (htwo : ∀ y (hy : y ∈ PX.smoothSet), ∃ a b : O y hy, a ≠ b ∧ ∀ c, c = a ∨ c = b) :
    L.IsOrientable := fun x y a b =>
  let ⟨_, _, _, hall⟩ := htwo y.pt y.smooth
  equiv_eq_of_apply_eq_of_two ((ho x y a).trans (ho x y b).symm) hall

/-- **Orientability means that there is an orientation** (Definitions 6.6.14 and 6.6.15 are
equivalent), when the fibres have exactly two elements. -/
theorem isOrientable_iff_exists_isOrientation
    (htwo : ∀ y (hy : y ∈ PX.smoothSet), ∃ a b : O y hy, a ≠ b ∧ ∀ c, c = a ∨ c = b) :
    L.IsOrientable ↔ ∃ o : ∀ y (hy : y ∈ PX.smoothSet), O y hy, L.IsOrientation o :=
  ⟨fun h => h.exists_isOrientation fun y hy => let ⟨a, _⟩ := htwo y hy; ⟨a⟩,
    fun ⟨_, ho⟩ => ho.isOrientable htwo⟩

/-- **Two orientations which agree at a point agree on its path component**: for a morphism
`[φ] : x ⟶ y`, `o_x = o'_x` iff `o_y = o'_y`. -/
theorem IsOrientation.apply_eq_iff {o o' : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (ho : L.IsOrientation o) (ho' : L.IsOrientation o') {x y : PathCat PX} (a : x ⟶ y) :
    o x.pt x.smooth = o' x.pt x.smooth ↔ o y.pt y.smooth = o' y.pt y.smooth := by
  rw [← ho x y a, ← ho' x y a]
  exact (L.functorMap a).apply_eq_iff_eq.symm

/-- **On the path component of a point there are exactly two orientations**, when the fibres
have exactly two elements: for an orientation `o` and a smooth point `x` there is an orientation
`o'` which differs from `o` at every point joined to `x` by an sc-smooth path and agrees with
`o` at the other points, and on the path component of `x` every orientation agrees with `o` or
with `o'`. -/
theorem IsOrientation.exists_two {o : ∀ y (hy : y ∈ PX.smoothSet), O y hy}
    (ho : L.IsOrientation o)
    (htwo : ∀ y (hy : y ∈ PX.smoothSet), ∃ a b : O y hy, a ≠ b ∧ ∀ c, c = a ∨ c = b)
    (x : PathCat PX) :
    ∃ o' : ∀ y (hy : y ∈ PX.smoothSet), O y hy, L.IsOrientation o' ∧
      (∀ y : PathCat PX, Nonempty (x ⟶ y) → o' y.pt y.smooth ≠ o y.pt y.smooth) ∧
      (∀ y : PathCat PX, IsEmpty (x ⟶ y) → o' y.pt y.smooth = o y.pt y.smooth) ∧
      ∀ o'' : ∀ y (hy : y ∈ PX.smoothSet), O y hy, L.IsOrientation o'' →
        (∀ y : PathCat PX, Nonempty (x ⟶ y) → o'' y.pt y.smooth = o y.pt y.smooth) ∨
        (∀ y : PathCat PX, Nonempty (x ⟶ y) → o'' y.pt y.smooth = o' y.pt y.smooth) := by
  classical
  have hne : ∀ y (hy : y ∈ PX.smoothSet) (p : O y hy), ∃ q, q ≠ p := fun y hy p =>
    let ⟨a₁, a₂, ha, _⟩ := htwo y hy
    if hp : p = a₁ then ⟨a₂, hp ▸ ha.symm⟩ else ⟨a₁, Ne.symm hp⟩
  let flip : ∀ y (hy : y ∈ PX.smoothSet), O y hy → O y hy := fun y hy p => (hne y hy p).choose
  have hflip : ∀ y hy p, flip y hy p ≠ p := fun y hy p => (hne y hy p).choose_spec
  have hother : ∀ y hy (p q : O y hy), q ≠ p → q = flip y hy p := fun y hy p q hq =>
    let ⟨_, _, _, hall⟩ := htwo y hy
    eq_of_ne_of_ne_of_two hall hq (hflip y hy p)
  let o' : ∀ y (hy : y ∈ PX.smoothSet), O y hy := fun y hy =>
    if Nonempty (x ⟶ ⟨y, hy⟩) then flip y hy (o y hy) else o y hy
  have e₁ : ∀ y : PathCat PX, Nonempty (x ⟶ y) →
      o' y.pt y.smooth = flip y.pt y.smooth (o y.pt y.smooth) := fun _ h => if_pos h
  have e₂ : ∀ y : PathCat PX, IsEmpty (x ⟶ y) → o' y.pt y.smooth = o y.pt y.smooth :=
    fun _ h => if_neg (not_nonempty_iff.2 h)
  have ho' : L.IsOrientation o' := by
    intro y z a
    by_cases hy : Nonempty (x ⟶ y)
    · rw [e₁ y hy, e₁ z ⟨hy.some ≫ a⟩]
      refine hother _ _ _ _ fun h => hflip _ _ (o y.pt y.smooth) ?_
      exact (L.functorMap a).injective (h.trans (ho y z a).symm)
    · have hz : IsEmpty (x ⟶ z) := not_nonempty_iff.1 fun ⟨b⟩ => hy ⟨b ≫ Groupoid.inv a⟩
      rw [e₂ y (not_nonempty_iff.1 hy), e₂ z hz]
      exact ho y z a
  refine ⟨o', ho', fun y hy => (e₁ y hy).symm ▸ hflip _ _ _, e₂, fun o'' ho'' => ?_⟩
  by_cases hx : o'' x.pt x.smooth = o x.pt x.smooth
  · exact Or.inl fun y ⟨a⟩ => (ho''.apply_eq_iff ho a).1 hx
  · have hx' : o'' x.pt x.smooth = o' x.pt x.smooth :=
      (hother _ _ _ _ hx).trans (e₁ x ⟨𝟙 x⟩).symm
    exact Or.inr fun y ⟨a⟩ => (ho''.apply_eq_iff ho' a).1 hx'

end LocalTransport

end Polyfold
