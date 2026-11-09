import Polyfold.Chapter3.BasicClassComposition
import Polyfold.Chapter3.GermFillingChart
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2014 preprint), Part I,
§2.6 "Strong Bundles", **Definition 2.6.1, p. 65 (preprint: Definition 2.47, p. 48)** — strong
bundle maps, **strong bundle isomorphisms** and strong bundle retractions between the trivial
bundles `U ◁ F` — and **the category `SBR` of local strong bundle retracts with its forgetful
functors `forget[i]`, pp. 66–67 (preprint p. 50)**.  This closes gap G.14 (rows V2.47 and
V2.56: "the category `SBR` and the forgetful functors are not formalized").  Numbers and pages
are the 2021 text's, the preprint ones in parentheses.

# Strong bundle isomorphisms and the category `SBR`

## The text, paraphrased

(Definition 2.6.1) A strong bundle map `Φ : U ◁ F → U' ◁ F'` preserves the double filtration,
has the form `Φ(u, h) = (ϕ(u), Γ(u, h))` with `Γ` linear in `h`, and is sc-smooth
`(U ◁ F)[i] → (U' ◁ F')[i]` for `i = 0, 1`.  A strong bundle isomorphism is an invertible strong
bundle map whose inverse is a strong bundle map.  (pp. 66–67) The category `SBR` has as objects
the local strong bundle retracts `(K, C ◁ F, E ◁ F)` and as morphisms the maps `Φ : K → K'`
linear in the fibres, preserving the double filtrations, with `Φ[i] : K[i] → K'[i]` sc-smooth
for `i = 0, 1` (sc-smoothness of a map between retracts being that of `Φ ∘ R`).  The forgetful
functors `forget[i]` send `K` to `K[i]` and `Φ` to `Φ[i]`.

## What is formalized

* Strong bundle maps and isomorphisms between the `U ◁ F` are the project's
  `Polyfold.IsStrongBundleMap` (Chapter 2) and `Polyfold.IsStrongBundleIso` (Chapter 3, Definition
  3.1.16's "strong bundle isomorphism `Ψ : U ◁ F → U' ◁ F'`"); here: `IsStrongBundleIso.refl`,
  `symm`, `trans`, `exists_iso_iff` (**the text's wording**: an invertible strong bundle map
  with strong bundle inverse).
* `SBR` (**the category `SBR`**): objects `SBR.mk E F C K h`, morphisms `SBR.Hom`: maps `K → K'`
  admitting an extension `Φ : E ◁ F → E' ◁ F'` with `SBR.IsHom`: `Φ : K → K'` and
  `Φ[1] : K[1] → K'[1]` sc-smooth retract maps, fibrewise linear, preserving the double
  filtration; `IsHom.id`, `IsHom.comp`; the `Category` instance; `Hom.ofIsHom`,
  `Hom.isHom_choose`.
* `SBR.trivial hU F` (the object `U ◁ F`), `IsStrongBundleMap.isHom` (**a strong bundle map of
  Definition 2.6.1 is a morphism of `SBR`**), `IsStrongBundleIso.toIso` (**a strong bundle
  isomorphism is an isomorphism of `SBR`**), `SBR.isoOfInverse` (a morphism with a two-sided
  inverse morphism is an isomorphism).
* `ScRetr` (the category of sc-smooth retracts `(O, C, E)`, `LocalModel`, with sc-smooth maps,
  Definition 2.1.7's reading of maps between retracts) and the **forgetful functors**
  `SBR.forget0`, `SBR.forget1 : SBR ⥤ ScRetr`, `K ↦ K[i]`, `Φ ↦ Φ[i]`.
* Witnesses: the identity isomorphism `IsStrongBundleIso.refl`, and `SBR.id`/`isoOfInverse`.

## What the text leaves implicit, and the choices made

* A morphism `K → K'` is sc-smooth "if `Φ ∘ R` is": the project's `IsScSmoothRetractMap`, which
  is a property of a total map `E ◁ F → E' ◁ F'`; morphisms of `SBR` are the maps `K → K'` having
  such an extension, so that equality of morphisms is equality on `K` and the category laws are
  the laws of maps.
* `Φ[1] : K[1] → K'[1]` is `shiftFiber Φ` (the fibre component lifted to `F'₁`), meaningful on
  `K[1]` by the preservation of the double filtration.
* The text's `forget[i]` land in the category `BR` of sc-smooth bundle retracts (§2.1), not
  formalized (G.5); here they land in the category `ScRetr` of sc-smooth retracts, i.e. `K[i]` is
  recorded as the retract `(K[i], C ◁ F, E ◁ F^i)` without its bundle structure.
-/

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

/-! ### Definition 2.6.1: strong bundle isomorphisms between the `U ◁ F` -/

section LocalIso

variable {E F E' F' E'' F'' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {C'' : Set (E'' 0)}
  {U : Set (E 0)} {U' : Set (E' 0)} {U'' : Set (E'' 0)}
  {Ψ : E 0 × F 0 → E' 0 × F' 0} {Ψ' : E' 0 × F' 0 → E 0 × F 0}
  {Λ : E' 0 × F' 0 → E'' 0 × F'' 0} {Λ' : E'' 0 × F'' 0 → E' 0 × F' 0}

/-- **The identity** `U ◁ F → U ◁ F` is a strong bundle isomorphism (witness). -/
theorem IsStrongBundleIso.refl (hU : IsRelOpenInQuadrant E C U) :
    IsStrongBundleIso (F := F) (F' := F) U U id id :=
  ⟨(isStrongBundleRetraction_id_of_relOpen hU).toIsStrongBundleMap,
    (isStrongBundleRetraction_id_of_relOpen hU).toIsStrongBundleMap, fun _ _ => rfl, fun _ _ => rfl⟩

/-- The inverse of a strong bundle isomorphism is one. -/
theorem IsStrongBundleIso.symm (h : IsStrongBundleIso U U' Ψ Ψ') : IsStrongBundleIso U' U Ψ' Ψ :=
  ⟨h.invFun, h.toFun, h.right_inv, h.left_inv⟩

/-- **The composition of strong bundle isomorphisms** is a strong bundle isomorphism. -/
theorem IsStrongBundleIso.trans (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (hU'' : IsRelOpenInQuadrant E'' C'' U'') (h : IsStrongBundleIso U U' Ψ Ψ')
    (h' : IsStrongBundleIso U' U'' Λ Λ') : IsStrongBundleIso U U'' (Λ ∘ Ψ) (Ψ' ∘ Λ') where
  toFun := IsStrongBundleMap.comp hU hU' h.toFun h'.toFun
  invFun := IsStrongBundleMap.comp hU'' hU' h'.invFun h.invFun
  left_inv p hp := by
    change Ψ' (Λ' (Λ (Ψ p))) = p
    rw [h'.left_inv _ (h.toFun.mapsTo hp), h.left_inv p hp]
  right_inv p hp := by
    change Λ (Ψ (Ψ' (Λ' p))) = p
    rw [h.right_inv _ (h'.invFun.mapsTo hp), h'.right_inv p hp]

/-- **Definition 2.6.1, the text's wording**: `Ψ` is a strong bundle isomorphism (for some
inverse) iff it is a strong bundle map, invertible on `U ◁ F → U' ◁ F'`, whose inverse is a strong
bundle map. -/
theorem exists_isStrongBundleIso_iff :
    (∃ Ψ', IsStrongBundleIso U U' Ψ Ψ') ↔
      IsStrongBundleMap U U' Ψ ∧ ∃ Ψ' : E' 0 × F' 0 → E 0 × F 0, IsStrongBundleMap U' U Ψ' ∧
        InvOn Ψ' Ψ (U ×ˢ univ) (U' ×ˢ univ) :=
  ⟨fun ⟨Ψ', h⟩ => ⟨h.toFun, Ψ', h.invFun, h.left_inv, h.right_inv⟩,
    fun ⟨h, Ψ', h', hl, hr⟩ => ⟨Ψ', h, h', hl, hr⟩⟩

end LocalIso

/-! ### The category `SBR` -/

/-- **An object of `SBR`** (pp. 66–67): a local strong bundle retract `(K, C ◁ F, E ◁ F)`. -/
structure SBR : Type 1 where
  /-- The sc-Banach space `E` of the base. -/
  E : ScBanach
  /-- The sc-Banach space `F` of the fibre. -/
  F : ScBanach
  /-- The partial quadrant `C ⊆ E`. -/
  C : Set (E 0)
  /-- The local strong bundle retract `K ⊆ C ◁ F`. -/
  K : Set (E 0 × F 0)
  isStrongBundleRetract : IsStrongBundleRetract C K

namespace SBR

variable (A A' A'' : SBR)

/-- The sc-smooth retract `K[0] = (K, C ◁ F, E ◁ F)`. -/
def model0 : LocalModel := ⟨A.E.prod A.F, A.C ×ˢ univ, A.K, A.isStrongBundleRetract.isScRetract⟩

/-- The sc-smooth retract `K[1] = (K[1], C ◁ F, E ◁ F¹)`. -/
def model1 : LocalModel :=
  ⟨A.E.prod A.F.shift, A.C ×ˢ univ, strongShiftOne A.K, A.isStrongBundleRetract.isScRetract_one⟩

variable {A A' A''}

/-- **A morphism of `SBR`, as a property of a map `Φ : E ◁ F → E' ◁ F'`** (pp. 66–67):
`Φ : K → K'` and `Φ[1] : K[1] → K'[1]` are sc-smooth maps between retracts, `Φ` is linear in
the fibres of `K`, and preserves the double filtration. -/
structure IsHom (Φ : A.E 0 × A.F 0 → A'.E 0 × A'.F 0) : Prop where
  zero : IsScSmoothRetractMap (A.E.prod A.F) (A.C ×ˢ univ) A.K (A'.E.prod A'.F) (A'.C ×ˢ univ)
    A'.K Φ
  one : IsScSmoothRetractMap (A.E.prod A.F.shift) (A.C ×ˢ univ) (strongShiftOne A.K)
    (A'.E.prod A'.F.shift) (A'.C ×ˢ univ) (strongShiftOne A'.K) (shiftFiber Φ)
  fiber_linear : ∀ (u : A.E 0) (h h' : A.F 0) (a b : ℝ), (u, h) ∈ A.K → (u, h') ∈ A.K →
    Φ (u, a • h + b • h') = ((Φ (u, h)).1, a • (Φ (u, h)).2 + b • (Φ (u, h')).2)
  preserves_filtration : ∀ m k, k ≤ m + 1 → ∀ p ∈ A.K, p.1 ∈ range (A.E.toBase m) →
    p.2 ∈ range (A.F.toBase k) → (Φ p).1 ∈ range (A'.E.toBase m) ∧ (Φ p).2 ∈ range (A'.F.toBase k)

namespace IsHom

variable {Φ : A.E 0 × A.F 0 → A'.E 0 × A'.F 0} {Λ : A'.E 0 × A'.F 0 → A''.E 0 × A''.F 0}

/-- The base component does not depend on the fibre variable. -/
lemma fst_eq (hΦ : IsHom Φ) {u : A.E 0} {h h' : A.F 0} (hK : (u, h) ∈ A.K) (hK' : (u, h') ∈ A.K) :
    (Φ (u, h')).1 = (Φ (u, h)).1 := by
  have := hΦ.fiber_linear u h h' 0 1 hK hK'
  rw [zero_smul, one_smul, zero_add] at this
  rw [this]

/-- `Φ[1]` lifts `Φ` on `K[1]`. -/
lemma toBase_shiftFiber (hΦ : IsHom Φ) {p : (A.E.prod A.F.shift) 0} (hp : p ∈ strongShiftOne A.K) :
    ((shiftFiber Φ p).1, A'.F.toBase 1 (shiftFiber Φ p).2) = Φ (p.1, A.F.toBase 1 p.2) := by
  have h2 := (hΦ.preserves_filtration 0 1 (by norm_num) _ hp ⟨p.1, rfl⟩ ⟨p.2, rfl⟩).2
  exact Prod.ext rfl (Function.invFun_eq h2)

/-- The identity of `K`. -/
theorem id (A : SBR) : IsHom (A := A) (A' := A) _root_.id where
  zero := isScSmoothRetractMap_id (E := A.E.prod A.F) (C := A.C ×ˢ univ) A.K
  one := (isScSmoothRetractMap_id (E := A.E.prod A.F.shift) (C := A.C ×ˢ univ) _).congr fun p _ =>
    (Prod.ext rfl (Function.leftInverse_invFun (A.F.toBase_injective 1) p.2) :
      shiftFiber _root_.id p = p).symm
  fiber_linear _ _ _ _ _ _ _ := rfl
  preserves_filtration _ _ _ _ _ h1 h2 := ⟨h1, h2⟩

/-- **Morphisms compose.** -/
theorem comp (hΦ : IsHom Φ) (hΛ : IsHom Λ) : IsHom (Λ ∘ Φ) where
  zero := hΛ.zero.comp hΦ.zero A'.isStrongBundleRetract.isScRetract
  one := (hΛ.one.comp hΦ.one A'.isStrongBundleRetract.isScRetract_one).congr fun p hp => by
    change ((Λ ((shiftFiber Φ p).1, A'.F.toBase 1 (shiftFiber Φ p).2)).1,
      Function.invFun (A''.F.toBase 1)
        (Λ ((shiftFiber Φ p).1, A'.F.toBase 1 (shiftFiber Φ p).2)).2) = shiftFiber (Λ ∘ Φ) p
    rw [hΦ.toBase_shiftFiber hp]
    rfl
  fiber_linear u h h' a b hK hK' := by
    have h1 : Φ (u, h) ∈ A'.K := hΦ.zero.mapsTo hK
    have h2 : ((Φ (u, h)).1, (Φ (u, h')).2) ∈ A'.K := by
      rw [← hΦ.fst_eq hK hK']; exact hΦ.zero.mapsTo hK'
    have h3 : Φ (u, h') = ((Φ (u, h)).1, (Φ (u, h')).2) := Prod.ext (hΦ.fst_eq hK hK') rfl
    change Λ (Φ (u, a • h + b • h')) =
      ((Λ (Φ (u, h))).1, a • (Λ (Φ (u, h))).2 + b • (Λ (Φ (u, h'))).2)
    rw [hΦ.fiber_linear u h h' a b hK hK', h3, hΛ.fiber_linear _ _ _ a b h1 h2]
  preserves_filtration m k hk p hp h1 h2 := by
    obtain ⟨h1', h2'⟩ := hΦ.preserves_filtration m k hk p hp h1 h2
    exact hΛ.preserves_filtration m k hk _ (hΦ.zero.mapsTo hp) h1' h2'

end IsHom

/-- **A morphism of `SBR`**: a map `K → K'` admitting an extension `Φ : E ◁ F → E' ◁ F'` with
`IsHom`. -/
structure Hom (A A' : SBR) where
  /-- The map `K → K'`. -/
  toFun : A.K → A'.K
  exists_ext : ∃ Φ : A.E 0 × A.F 0 → A'.E 0 × A'.F 0, IsHom Φ ∧ ∀ p : A.K, (toFun p : _) = Φ p

theorem Hom.ext {f g : Hom A A'} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

/-- The morphism of `SBR` given by a map with `IsHom`. -/
def Hom.ofIsHom {Φ : A.E 0 × A.F 0 → A'.E 0 × A'.F 0} (hΦ : IsHom Φ) : Hom A A' :=
  ⟨fun p => ⟨Φ p, hΦ.zero.mapsTo p.2⟩, Φ, hΦ, fun _ => rfl⟩

/-- **The category `SBR`** (pp. 66–67). -/
instance : LargeCategory SBR where
  Hom := Hom
  id A := ⟨_root_.id, _root_.id, IsHom.id A, fun _ => rfl⟩
  comp f g := ⟨g.toFun ∘ f.toFun, by
    obtain ⟨Φ, hΦ, hf⟩ := f.exists_ext
    obtain ⟨Λ, hΛ, hg⟩ := g.exists_ext
    exact ⟨Λ ∘ Φ, hΦ.comp hΛ, fun p => by
      change (g.toFun (f.toFun p) : _) = Λ (Φ p)
      rw [hg, hf]⟩⟩
  id_comp _ := Hom.ext rfl
  comp_id _ := Hom.ext rfl
  assoc _ _ _ := Hom.ext rfl

/-- A chosen extension of a morphism, with `IsHom`. -/
theorem Hom.isHom_choose (f : A ⟶ A') :
    IsHom (Classical.choose f.exists_ext) ∧
      ∀ p : A.K, (f.toFun p : _) = Classical.choose f.exists_ext p :=
  Classical.choose_spec f.exists_ext

/-- A morphism with a two-sided inverse morphism is an isomorphism of `SBR`. -/
def isoOfInverse (f : A ⟶ A') (g : A' ⟶ A) (hl : ∀ p, g.toFun (f.toFun p) = p)
    (hr : ∀ p, f.toFun (g.toFun p) = p) : A ≅ A' where
  hom := f
  inv := g
  hom_inv_id := Hom.ext (funext hl)
  inv_hom_id := Hom.ext (funext hr)

/-! ### The trivial retracts `U ◁ F`: strong bundle maps are morphisms -/

variable {E F E' F' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)} {U' : Set (E' 0)}

/-- The object `U ◁ F` of `SBR` (`K = U ◁ F`, `R = id`). -/
abbrev trivial (hU : IsRelOpenInQuadrant E C U) (F : ScBanach) : SBR :=
  ⟨E, F, C, U ×ˢ univ, ⟨U, _root_.id, hU, isStrongBundleRetraction_id_of_relOpen hU,
    (image_id _).symm⟩⟩

lemma strongShiftOne_prod_univ (U : Set (E 0)) (F : ScBanach) :
    strongShiftOne (E := E) (F := F) (U ×ˢ univ) = U ×ˢ univ := by
  ext p; exact ⟨fun h => ⟨h.1, mem_univ _⟩, fun h => ⟨h.1, mem_univ _⟩⟩

/-- **A strong bundle map `U ◁ F → U' ◁ F'` (Definition 2.6.1) is a morphism of `SBR`.** -/
theorem _root_.Polyfold.IsStrongBundleMap.isHom (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') {Ψ : E 0 × F 0 → E' 0 × F' 0}
    (hΨ : IsStrongBundleMap U U' Ψ) : IsHom (A := trivial hU F) (A' := trivial hU' F') Ψ where
  zero := ⟨hΨ.mapsTo, fun R hR => by
    have hR' : R.retract = U ×ˢ univ := hR
    exact IsScSmooth.comp R.isScDomain (hU.prod_univ F).isScDomain hΨ.isScSmooth_zero
      R.isScSmooth (hR' ▸ R.mapsTo_retract)⟩
  one := by
    change IsScSmoothRetractMap _ _ (strongShiftOne (U ×ˢ univ)) _ _ (strongShiftOne (U' ×ˢ univ)) _
    rw [strongShiftOne_prod_univ, strongShiftOne_prod_univ]
    refine ⟨fun p hp => ⟨?_, mem_univ _⟩, fun R hR => IsScSmooth.comp R.isScDomain
      (hU.prod_univ F.shift).isScDomain hΨ.isScSmooth_one R.isScSmooth (hR ▸ R.mapsTo_retract)⟩
    exact (hΨ.mapsTo (show (p.1, F.toBase 1 p.2) ∈ U ×ˢ univ from ⟨hp.1, mem_univ _⟩)).1
  fiber_linear u h h' a b hK _ := by
    have hl := hΨ.fiber_linear u hK.1
    have h1 := hl.map_add (a • h) (b • h')
    have h2 := hl.map_smul a h
    have h3 := hl.map_smul b h'
    dsimp only at h1 h2 h3
    exact Prod.ext (hΨ.fst_independent u hK.1 _ _) (h1.trans (by rw [h2, h3]))
  preserves_filtration m k hk p hp h1 h2 := hΨ.preserves_filtration m k hk p.1 hp.1 h1 p.2 h2

/-- **A strong bundle isomorphism `U ◁ F → U' ◁ F'` (Definition 2.6.1) is an isomorphism of
`SBR`** between the trivial retracts. -/
def _root_.Polyfold.IsStrongBundleIso.toIso (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') {Ψ : E 0 × F 0 → E' 0 × F' 0}
    {Ψ' : E' 0 × F' 0 → E 0 × F 0} (h : IsStrongBundleIso U U' Ψ Ψ') :
    trivial hU F ≅ trivial hU' F' :=
  isoOfInverse (Hom.ofIsHom (h.toFun.isHom hU hU')) (Hom.ofIsHom (h.invFun.isHom hU' hU))
    (fun p => Subtype.ext (h.left_inv p p.2)) (fun p => Subtype.ext (h.right_inv p p.2))

end SBR

/-! ### The category of sc-smooth retracts and the forgetful functors -/

/-- **The category of sc-smooth retracts** `(O, C, E)` with sc-smooth maps (the maps between
retracts of Definition 2.1.7): the objects are the `LocalModel`s, the morphisms the maps `O → O'`
with an sc-smooth extension (`IsScSmoothRetractMap`). -/
structure ScRetr : Type 1 where
  /-- The retract. -/
  M : LocalModel

namespace ScRetr

/-- A morphism of `ScRetr`. -/
structure Hom (M M' : ScRetr) where
  /-- The map `O → O'`. -/
  toFun : M.M.O → M'.M.O
  exists_ext : ∃ f : M.M.E 0 → M'.M.E 0,
    IsScSmoothRetractMap M.M.E M.M.C M.M.O M'.M.E M'.M.C M'.M.O f ∧ ∀ p : M.M.O, (toFun p : _) = f p

theorem Hom.ext {M M' : ScRetr} {f g : Hom M M'} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

instance : LargeCategory ScRetr where
  Hom := Hom
  id M := ⟨_root_.id, _root_.id, isScSmoothRetractMap_id _, fun _ => rfl⟩
  comp := fun {_ M' _} f g => ⟨g.toFun ∘ f.toFun, by
    obtain ⟨φ, hφ, hf⟩ := f.exists_ext
    obtain ⟨ψ, hψ, hg⟩ := g.exists_ext
    exact ⟨ψ ∘ φ, hψ.comp hφ M'.M.isScRetract, fun p => by
      change (g.toFun (f.toFun p) : _) = ψ (φ p)
      rw [hg, hf]⟩⟩
  id_comp _ := Hom.ext rfl
  comp_id _ := Hom.ext rfl
  assoc _ _ _ := Hom.ext rfl

end ScRetr

namespace SBR

/-- **The forgetful functor `forget[0] : SBR → ScRetr`**, `K ↦ K[0]`, `Φ ↦ Φ[0] = Φ`. -/
def forget0 : SBR ⥤ ScRetr where
  obj A := ⟨A.model0⟩
  map f := ⟨f.toFun, by
    obtain ⟨Φ, hΦ, hf⟩ := f.exists_ext
    exact ⟨Φ, hΦ.zero, hf⟩⟩
  map_id _ := ScRetr.Hom.ext rfl
  map_comp _ _ := ScRetr.Hom.ext rfl

/-- The fibre component of `f(u, h)`, `(u, h) ∈ K[1]`, lies in `F'₁`. -/
lemma snd_mem_range {A A' : SBR} (f : A ⟶ A') (p : strongShiftOne A.K) :
    (f.toFun ⟨(p.1.1, A.F.toBase 1 p.1.2), p.2⟩).1.2 ∈ range (A'.F.toBase 1) := by
  obtain ⟨hΦ, hf⟩ := f.isHom_choose
  have h2 := (hΦ.preserves_filtration 0 1 (by norm_num) _ p.2 ⟨p.1.1, rfl⟩ ⟨p.1.2, rfl⟩).2
  rw [hf]; exact h2

/-- The map `K[1] → K'[1]` induced by a morphism `f : K → K'`: `(u, h) ↦ f(u, h)` with the fibre
component lifted to `F'₁`. -/
def mapOne {A A' : SBR} (f : A ⟶ A') (p : strongShiftOne A.K) : strongShiftOne A'.K :=
  ⟨((f.toFun ⟨(p.1.1, A.F.toBase 1 p.1.2), p.2⟩).1.1,
    Function.invFun (A'.F.toBase 1) (f.toFun ⟨(p.1.1, A.F.toBase 1 p.1.2), p.2⟩).1.2), by
    change ((f.toFun ⟨(p.1.1, A.F.toBase 1 p.1.2), p.2⟩).1.1, A'.F.toBase 1
      (Function.invFun (A'.F.toBase 1) (f.toFun ⟨(p.1.1, A.F.toBase 1 p.1.2), p.2⟩).1.2)) ∈ A'.K
    rw [Function.invFun_eq (snd_mem_range f p)]
    exact (f.toFun _).2⟩

lemma mapOne_val {A A' : SBR} (f : A ⟶ A') (p : strongShiftOne A.K) :
    ((mapOne f p).1.1, A'.F.toBase 1 (mapOne f p).1.2) =
      (f.toFun ⟨(p.1.1, A.F.toBase 1 p.1.2), p.2⟩).1 :=
  Prod.ext rfl (Function.invFun_eq (snd_mem_range f p))

/-- **The forgetful functor `forget[1] : SBR → ScRetr`**, `K ↦ K[1]`, `Φ ↦ Φ[1]`. -/
def forget1 : SBR ⥤ ScRetr where
  obj A := ⟨A.model1⟩
  map {A A'} f := ⟨mapOne f, by
    obtain ⟨hΦ, hf⟩ := f.isHom_choose
    refine ⟨shiftFiber (Classical.choose f.exists_ext), hΦ.one, fun p => ?_⟩
    change ((f.toFun ⟨(p.1.1, A.F.toBase 1 p.1.2), p.2⟩).1.1, Function.invFun (A'.F.toBase 1)
      (f.toFun ⟨(p.1.1, A.F.toBase 1 p.1.2), p.2⟩).1.2) = shiftFiber _ _
    rw [hf]; rfl⟩
  map_id A := ScRetr.Hom.ext (funext fun p => Subtype.ext
    (Prod.ext rfl (Function.leftInverse_invFun (A.F.toBase_injective 1) _)))
  map_comp {A A' A''} f g := ScRetr.Hom.ext (funext fun p => Subtype.ext (by
    have hq : (⟨((mapOne f p).1.1, A'.F.toBase 1 (mapOne f p).1.2), (mapOne f p).2⟩ : A'.K) =
        f.toFun ⟨(p.1.1, A.F.toBase 1 p.1.2), p.2⟩ := Subtype.ext (mapOne_val f p)
    change ((g.toFun (f.toFun ⟨(p.1.1, A.F.toBase 1 p.1.2), p.2⟩)).1.1,
        Function.invFun (A''.F.toBase 1)
          (g.toFun (f.toFun ⟨(p.1.1, A.F.toBase 1 p.1.2), p.2⟩)).1.2) =
      ((g.toFun ⟨((mapOne f p).1.1, A'.F.toBase 1 (mapOne f p).1.2), (mapOne f p).2⟩).1.1,
        Function.invFun (A''.F.toBase 1)
          (g.toFun ⟨((mapOne f p).1.1, A'.F.toBase 1 (mapOne f p).1.2), (mapOne f p).2⟩).1.2)
    rw [hq]))

end SBR

end Polyfold
