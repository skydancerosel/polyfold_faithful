import GWMemoir.Fibres
import Polyfold.Chapter17.VectorBundleGCT

/-!
# Labels by stable maps and fibre representations

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §1.2 (p. 7: the fibre of
`W` over a stable map) and §4.1 (p. 101: `F(α) = (α, ∂̄_J(α))`), with the fibre spaces of
`GWMemoir.Fibres`.

## What is formalized

* `StableMapLabel C`: a groupoidal category whose objects are labelled by stable maps and whose
  morphisms by isomorphisms of stable maps; `gwLabel` for the category of all stable maps
  (`gwCategory`).  A component (for instance the stable maps of a given energy, closed under
  isomorphism) is a full subcategory with the inclusion as label.
* `FibreRepresentation L V J k' δ'`: the identification of the fibre of `W` (memoir p. 7) with a
  Banach functor `V`, on the classes: linear maps `ι_a` from a submodule `dom a` of the forms
  along `L(a)` (those with representatives) to `V(a)`, `dom` closed under the pull-backs
  `ξ' ↦ ξ' ∘ Tφ`, natural (`V(φ) ι(φ^*ξ') = ι(ξ')`), and injective on the continuous fibre
  elements of class `(k', δ')`.
* `DbarInDom ι` (Theorem 4.6, regularity: `∂̄_J L(a)` has representatives) and
  `DbarRegularC L J k' δ'` (`∂̄_J L(a)` is a continuous fibre element): the named propositions
  on `∂̄_J`.
* `FibreRepresentation.dbar`: `a ↦ ι_a(∂̄_J L(a))`, natural (`dbar_natural`, chain rule) and
  vanishing exactly at the `J`-holomorphic labels (`dbar_eq_zero_iff`), the two facts Theorem
  1.11 uses.

## Readings

* Fibre elements (`IsFibreElement`) are functions on `S`, while the Sobolev norms of p. 7 do not
  see a change on a null set.  An identification injective on all fibre elements does not factor
  through the fibre spaces (`not_factor_of_injOn_fibreElements`, `GWMemoir.FibreInstance`), so
  the injectivity is asked on continuous forms (`∂̄_J u` is continuous for `u` of class
  `(3, δ₀)`), and `ι` is defined on the forms with representatives.
* Instances: `fibreRepresentation` (full subcategories of stable maps without nodes, given the
  change of coordinates `AllPullbackBounded`) and `constFibreRepresentation` (constant maps from
  the three-pointed sphere, no named proposition), in `GWMemoir.FibreInstance`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function
open scoped Manifold ContDiff

noncomputable section

namespace GWMemoir

open Polyfold

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-! ### Labels -/

section Label

variable {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ}

variable (om m k δ) in
/-- **A labelling of a groupoidal category by stable maps**: objects `a ↦ L(a)`, morphisms
`φ ↦ L(φ) : L(s φ) ≅ L(t φ)`. -/
structure StableMapLabel (C : GroupoidalCategory.{1}) where
  obj : C.Obj → StableMap om m k δ
  iso : ∀ φ : C.Mor, StableMap.Iso (obj (C.toGroupoidStr.src φ)) (obj (C.toGroupoidStr.tgt φ))

/-- The label of the category of all stable maps (witness): `L = id`. -/
def gwLabel (hfin : FiniteIsos' (om := om) m k δ) : StableMapLabel om m k δ (gwCategory hfin) where
  obj α := α
  iso φ := φ.2.2

end Label

/-! ### Fibre representations -/

section Representation

variable {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ} {C : GroupoidalCategory.{1}}

variable (om m k δ) in
/-- **The fibre of `W` and the Banach functor, on the classes** (memoir p. 7: the fibre over `α`
consists of the `(0,1)`-forms along `u` of class `(k + 2, δ_k)`): linear maps `ι_a` from a
submodule `dom a` of the forms along `L(a)` (those with representatives) to `V(a)`, `dom`
closed under the pull-backs `ξ' ↦ ξ' ∘ Tφ`, natural (`V(φ) ι(φ^*ξ') = ι(ξ')`), and injective on
the continuous fibre elements of class `(k', δ')`. -/
structure FibreRepresentation (L : StableMapLabel om m k δ C)
    (V : GroupoidalCategory.BanachFunctor C) (J : AlmostComplexStructure E Q) (k' : ℕ)
    (δ' : ℝ) where
  dom : ∀ a : C.Obj, Submodule ℝ (Form E (L.obj a).dom)
  ι : ∀ a, dom a →ₗ[ℝ] V.V a
  pullback_mem : ∀ (φ : C.Mor) (ξ' : Form E (L.obj (C.toGroupoidStr.tgt φ)).dom),
    ξ' ∈ dom _ → (L.iso φ).φ.pullbackForm ξ' ∈ dom (C.toGroupoidStr.src φ)
  natural : ∀ (φ : C.Mor) (ξ' : dom (C.toGroupoidStr.tgt φ)),
    V.map φ (ι _ ⟨_, pullback_mem φ ξ'.1 ξ'.2⟩) = ι _ ξ'
  injOn : ∀ a, InjOn (ι a)
    {ξ | IsFibreElement J (L.obj a) k' δ' ξ.1 ∧ IsContForm (L.obj a).u ξ.1}

variable {L : StableMapLabel om m k δ C} {V : GroupoidalCategory.BanachFunctor C}
  {J : AlmostComplexStructure E Q} {k' : ℕ} {δ' : ℝ}

/-- **Memoir Theorem 4.6, regularity, for the domain** (p. 101): `∂̄_J L(a)` has representatives
(it is of class `(2, δ₀)` in the charts of the fibre). -/
def DbarInDom (ι : FibreRepresentation om m k δ L V J k' δ') : Prop :=
  ∀ a, (L.obj a).dbar J ∈ ι.dom a

variable (L J k' δ') in
/-- **Memoir Theorem 4.6, regularity** (p. 101; memoir p. 7): `∂̄_J L(a)` is a continuous fibre
element of class `(k', δ')` (stable maps of class `(3, δ)` are `C¹`). -/
def DbarRegularC : Prop :=
  ∀ a, IsFibreElement J (L.obj a) k' δ' ((L.obj a).dbar J) ∧
    IsContForm (L.obj a).u ((L.obj a).dbar J)

/-- `a ↦ ι_a(∂̄_J L(a))`, the fibre part of `F(α) = (α, ∂̄_J(α))`. -/
def FibreRepresentation.dbar (ι : FibreRepresentation om m k δ L V J k' δ') (hd : DbarInDom ι)
    (a : C.Obj) : V.V a :=
  ι.ι a ⟨_, hd a⟩

/-- **`∂̄_J` is natural**: `V(φ) ι(∂̄_J L(s φ)) = ι(∂̄_J L(t φ))`, from the chain rule
(`StableMap.Iso.pullbackForm_dbar`). -/
theorem FibreRepresentation.dbar_natural (ι : FibreRepresentation om m k δ L V J k' δ')
    (hd : DbarInDom ι) (φ : C.Mor) :
    V.map φ (ι.dbar hd (C.toGroupoidStr.src φ)) = ι.dbar hd (C.toGroupoidStr.tgt φ) := by
  have h : (⟨_, ι.pullback_mem φ _ (hd _)⟩ : ι.dom (C.toGroupoidStr.src φ)) = ⟨_, hd _⟩ :=
    Subtype.ext ((L.iso φ).pullbackForm_dbar J)
  unfold FibreRepresentation.dbar
  rw [← h]
  exact ι.natural φ ⟨_, hd _⟩

lemma isContForm_zero {m' : ℕ} {X : NodalSurface m'} (u : X.S → Q) : IsContForm u (0 : Form E X) :=
  fun z => by
    have : formAt u z (0 : Form E X) = fun _ => 0 := funext (formAt_zero u z)
    rw [this]; exact continuousOn_const

/-- **The zeros of `∂̄_J` are the `J`-holomorphic labels.** -/
theorem FibreRepresentation.dbar_eq_zero_iff (ι : FibreRepresentation om m k δ L V J k' δ')
    (hd : DbarInDom ι) (hreg : DbarRegularC L J k' δ') (a : C.Obj) :
    ι.dbar hd a = 0 ↔ (L.obj a).IsHolomorphic J := by
  unfold FibreRepresentation.dbar StableMap.IsHolomorphic
  constructor
  · intro h x
    have h0 : (⟨_, hd a⟩ : ι.dom a) = 0 :=
      ι.injOn a (hreg a) ⟨isFibreElement_zero J (L.obj a) k' δ', isContForm_zero _⟩
        (by rw [h, map_zero])
    rw [show (L.obj a).dbar J = 0 from congrArg Subtype.val h0]
    rfl
  · intro h
    have h0 : (⟨_, hd a⟩ : ι.dom a) = 0 := Subtype.ext (funext h)
    rw [h0, map_zero]

end Representation

end GWMemoir
