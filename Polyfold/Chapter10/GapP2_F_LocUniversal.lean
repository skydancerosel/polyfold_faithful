import Polyfold.Chapter10.LocalizationCategory

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 10,
§10.3, p. 483 (2017: p. 347) and Theorem 10.3.14, p. 491 (2017: Theorem 10.5, p. 354):
**the universal property of the localization** `i : EP → EP(E⁻¹)`.  The text introduces
`EP(E⁻¹)` as the localization of `EP` at the class `E` of equivalences, the category in which
the equivalences become invertible universally; Theorem 10.3.14 gives the functor `i`.

## What is formalized (namespace `Polyfold.EPLocalization`)

* `EpFunctor.NaturallyEquivalent` is identified by every functor inverting `E`
  (`map_eq_of_naturallyEquivalent`).  The cylinder is the weak fibred product
  `P = X ×_Y Y` of `F` and `1_Y`: a natural transformation `τ : F → F'` gives the sc-smooth
  section `secFunctor τ : X → P`, `x ↦ (x, τ(x), F'(x))`, with `π_X ∘ s_τ = 1_X` and
  `π_Y ∘ s_τ = F'`.  As `π_X` is an equivalence, `L(s_τ) = L(π_X)⁻¹ = L(s_{1_F})` for every `L`
  inverting `E`, so `L(F') = L(F)`.
* `EPLoc.lift L hL : EP(E⁻¹) ⥤ D`, `[X ←F A →Φ Y] ↦ L(F)⁻¹ ≫ L(Φ)`, well defined on classes
  (`liftMap_eq_of_isRefinement`, `liftMap_eq_of_equiv`) and a functor (`liftMap_comp`, through
  `Φ ∘ π_A ≃ G ∘ π_B` on the weak fibred product).
* `EPLoc.strictUniversalPropertyFixedTarget`: Mathlib's strict universal property for every
  target category, and **`EPLoc.isLocalization`**: `i` is a localization of `EP` at `E`
  (`Functor.IsLocalization`).  **`EPLoc.universal_property`**: for every functor `L : EP ⥤ D`
  inverting the equivalences there is a unique `L' : EP(E⁻¹) ⥤ D` with `i ⋙ L' = L`.

No hypothesis is added.
-/

set_option maxSynthPendingDepth 3

open CategoryTheory

noncomputable section

namespace Polyfold

universe u v₁ u₁

namespace EPLocalization

open WeakFibredProduct

variable {X Y : EP.{u}}

/-! ### The section `X → X ×_Y Y` of a natural transformation -/

section Section

variable {F F' : EpFunctor X.X Y.X}

/-- The weak fibred product of `F` and `1_Y` is admissible. -/
theorem admissible_id_right (F : EpFunctor X.X Y.X) : Admissible F (EpFunctor.id Y.X) :=
  .of_isEquivalence_right (EpFunctor.IsEquivalence.id _)

/-- `x ↦ (x, τ(x), F'(x))`. -/
def secObj (τ : EpNatTrans F F') (x : X.Obj) : Obj F (EpFunctor.id Y.X) :=
  Obj.mk F (EpFunctor.id Y.X) x (τ.app x) (F'.obj x) (τ.src_app x) (τ.tgt_app x)

/-- `h ↦ (h, τ(s(h)), F'(h))`. -/
def secMor (τ : EpNatTrans F F') (m : X.Mor) : Mor F (EpFunctor.id Y.X) :=
  Mor.mk F (EpFunctor.id Y.X) m (τ.app (X.X.src m)) (F'.mor m) (τ.src_app _)
    (by rw [τ.tgt_app]; exact (F'.src_mor m).symm)

theorem src_secMor (τ : EpNatTrans F F') (m : X.Mor) : src (secMor τ m) = secObj τ (X.X.src m) :=
  Obj.ext rfl rfl (F'.src_mor m)

theorem tgt_secMor (τ : EpNatTrans F F') (m : X.Mor) : tgt (secMor τ m) = secObj τ (X.X.tgt m) := by
  refine Obj.ext rfl ?_ (F'.tgt_mor m)
  change Y.X.comp (Y.X.comp (F'.mor m) (τ.app (X.X.src m))) (Y.X.inv (F.mor m)) =
    τ.app (X.X.tgt m)
  rw [← τ.naturality m]
  exact GroupoidStr.comp_inv_cancel_right (by rw [τ.src_app, F.tgt_mor])

/-- **The section** `s_τ : X → X ×_Y Y` of a natural transformation `τ : F → F'`. -/
def secFunctor (τ : EpNatTrans F F') :
    EpFunctor X.X (epGroupoid F (EpFunctor.id Y.X) (admissible_id_right F)) where
  obj := secObj τ
  mor := secMor τ
  src_mor := src_secMor τ
  tgt_mor := tgt_secMor τ
  mor_comp m m' hc := by
    have hc' : src (secMor τ m) = tgt (secMor τ m') := by
      rw [src_secMor, tgt_secMor, hc]
    change secMor τ (X.X.comp m m') = comp (secMor τ m) (secMor τ m')
    refine Mor.ext (h_comp hc').symm ?_ ?_
    · rw [φ_comp hc']
      change τ.app (X.X.src (X.X.comp m m')) = τ.app (X.X.src m')
      rw [X.X.src_comp _ _ hc]
    · rw [k_comp hc']
      exact F'.mor_comp m m' hc
  mor_unit x := by
    refine Mor.ext rfl ?_ (F'.mor_unit x)
    change τ.app (X.X.src (X.X.unit x)) = τ.app x
    rw [X.X.src_unit]
  isScSmoothMap_obj := isScSmoothOn_obj_of (admissible_id_right F) MPolyfold.isScSmoothMap_id
    τ.isScSmoothMap_app
    F'.isScSmoothMap_obj
  isScSmoothMap_mor := isScSmoothOn_mor_of (admissible_id_right F) MPolyfold.isScSmoothMap_id
    (τ.isScSmoothMap_app.comp X.X.isScSmoothMap_src) F'.isScSmoothMap_mor

theorem projLeft_comp_secFunctor (τ : EpNatTrans F F') :
    (projLeft F (EpFunctor.id Y.X) (admissible_id_right F)).comp (secFunctor τ) =
      EpFunctor.id X.X :=
  EpFunctor.ext (funext fun _ => rfl) (funext fun _ => rfl)

theorem projRight_comp_secFunctor (τ : EpNatTrans F F') :
    (projRight F (EpFunctor.id Y.X) (admissible_id_right F)).comp (secFunctor τ) = F' :=
  EpFunctor.ext (funext fun _ => rfl) (funext fun _ => rfl)

/-- The cylinder `X ×_Y Y` of `F` and `1_Y`, an object of `EP`. -/
abbrev cyl (F : EpFunctor X.X Y.X) : EP.{u} := wfp F (EpFunctor.id Y.X) (admissible_id_right F)

/-- `π_X : X ×_Y Y → X` as a morphism of `EP`. -/
abbrev cylLeft (F : EpFunctor X.X Y.X) : cyl F ⟶ X :=
  projLeft F (EpFunctor.id Y.X) (admissible_id_right F)

/-- `π_Y : X ×_Y Y → Y` as a morphism of `EP`. -/
abbrev cylRight (F : EpFunctor X.X Y.X) : cyl F ⟶ Y :=
  projRight F (EpFunctor.id Y.X) (admissible_id_right F)

/-- `s_τ` as a morphism of `EP`. -/
abbrev secHom (τ : EpNatTrans F F') : X ⟶ cyl F := secFunctor τ

theorem secHom_cylLeft (τ : EpNatTrans F F') : secHom τ ≫ cylLeft F = 𝟙 X :=
  projLeft_comp_secFunctor τ

theorem secHom_cylRight (τ : EpNatTrans F F') : secHom τ ≫ cylRight F = F' :=
  projRight_comp_secFunctor τ

end Section

/-! ### Functors inverting `E` identify naturally equivalent functors -/

variable {D : Type u₁} [Category.{v₁} D]

/-- A functor `L : EP → D` inverting the equivalences takes naturally equivalent sc-smooth
functors to the same morphism, through the cylinder `X ×_Y Y`. -/
theorem map_eq_of_naturallyEquivalent (L : EP.{u} ⥤ D) (hL : EP.equivalences.IsInvertedBy L)
    {F F' : X ⟶ Y} (h : EpFunctor.NaturallyEquivalent F F') : L.map F = L.map F' := by
  obtain ⟨τ⟩ := h
  have hπ : EpFunctor.IsEquivalence (cylLeft F) :=
    isEquivalence_projLeft (EpFunctor.IsEquivalence.id _) (admissible_id_right F)
  have := hL (cylLeft F) hπ
  have key : ∀ {F'' : X ⟶ Y} (σ : EpNatTrans F F''),
      L.map (secHom σ) = inv (L.map (cylLeft F)) := fun σ => by
    refine IsIso.eq_inv_of_inv_hom_id ?_
    rw [← L.map_comp, secHom_cylLeft, L.map_id]
  have e₁ : L.map F' = L.map (secHom τ) ≫ L.map (cylRight F) := by
    rw [← L.map_comp, secHom_cylRight]
  have e₂ : L.map F = L.map (secHom (EpNatTrans.refl F)) ≫ L.map (cylRight F) := by
    rw [← L.map_comp, secHom_cylRight]
  rw [e₁, e₂, key, key]

/-! ### The lift `EP(E⁻¹) → D` -/

namespace EPLoc

variable (L : EP.{u} ⥤ D) (hL : EP.equivalences.IsInvertedBy L)

/-- `[X ←F A →Φ Y] ↦ L(F)⁻¹ ≫ L(Φ)` on representatives. -/
def liftMap (d : Diagram X Y) : L.obj X ⟶ L.obj Y :=
  haveI := hL d.F d.isEquivalence_F
  inv (L.map (X := d.A) (Y := X) d.F) ≫ L.map (X := d.A) (Y := Y) d.Φ

theorem liftMap_eq_of_isRefinement {d d' : Diagram X Y} (h : d'.IsRefinement d) :
    liftMap L hL d' = liftMap L hL d := by
  obtain ⟨H, hH, hF, hΦ⟩ := h
  have := hL d.F d.isEquivalence_F
  have := hL d'.F d'.isEquivalence_F
  have := hL H hH
  have eF : L.map (X := d'.A) (Y := X) d'.F =
      L.map (X := d'.A) (Y := d.A) H ≫ L.map (X := d.A) (Y := X) d.F := by
    rw [← map_eq_of_naturallyEquivalent L hL hF]
    exact L.map_comp (X := d'.A) (Y := d.A) (Z := X) H d.F
  have eΦ : L.map (X := d'.A) (Y := Y) d'.Φ =
      L.map (X := d'.A) (Y := d.A) H ≫ L.map (X := d.A) (Y := Y) d.Φ := by
    rw [← map_eq_of_naturallyEquivalent L hL hΦ]
    exact L.map_comp (X := d'.A) (Y := d.A) (Z := Y) H d.Φ
  unfold liftMap
  simp only [eF, eΦ, IsIso.inv_comp, Category.assoc, IsIso.inv_hom_id_assoc]

theorem liftMap_eq_of_equiv {d d' : Diagram X Y} (h : Diagram.Equiv d d') :
    liftMap L hL d = liftMap L hL d' := by
  obtain ⟨d'', h₁, h₂⟩ := h
  rw [← liftMap_eq_of_isRefinement L hL h₁, liftMap_eq_of_isRefinement L hL h₂]

theorem liftMap_id (X : EP.{u}) : liftMap L hL (Diagram.id X) = 𝟙 _ := by
  have := hL (Diagram.id X).F (Diagram.id X).isEquivalence_F
  unfold liftMap
  exact IsIso.inv_hom_id _

theorem liftMap_comp {Z : EP.{u}} (d : Diagram X Y) (e : Diagram Y Z) :
    liftMap L hL (d.comp e) = liftMap L hL d ≫ liftMap L hL e := by
  let πA : (d.comp e).A ⟶ d.A := projLeft d.Φ e.F (d.admissible e)
  let πB : (d.comp e).A ⟶ e.A := projRight d.Φ e.F (d.admissible e)
  have := hL d.F d.isEquivalence_F
  have := hL e.F e.isEquivalence_F
  have := hL πA (isEquivalence_projLeft e.isEquivalence_F (d.admissible e))
  have := hL (d.comp e).F (d.comp e).isEquivalence_F
  have hsq : L.map πA ≫ L.map (X := d.A) (Y := Y) d.Φ =
      L.map πB ≫ L.map (X := e.A) (Y := Y) e.F := by
    rw [← L.map_comp, ← L.map_comp]
    exact map_eq_of_naturallyEquivalent L hL (naturallyEquivalent (d.admissible e))
  have hF : L.map (X := (d.comp e).A) (Y := X) (d.comp e).F =
      L.map πA ≫ L.map (X := d.A) (Y := X) d.F := L.map_comp πA (Y := d.A) (Z := X) d.F
  have hΨ : L.map (X := (d.comp e).A) (Y := Z) (d.comp e).Φ =
      L.map πB ≫ L.map (X := e.A) (Y := Z) e.Φ := L.map_comp πB (Y := e.A) (Z := Z) e.Φ
  have hsq' : inv (L.map πA) ≫ L.map πB =
      L.map (X := d.A) (Y := Y) d.Φ ≫ inv (L.map (X := e.A) (Y := Y) e.F) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hsq, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hinv : inv (L.map (X := (d.comp e).A) (Y := X) (d.comp e).F) =
      inv (L.map (X := d.A) (Y := X) d.F) ≫ inv (L.map πA) := by
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [hF]
    simp
  unfold liftMap
  rw [hinv, hΨ, Category.assoc, ← Category.assoc (inv (L.map πA)), hsq']
  simp only [Category.assoc]

/-- **The lift** `EP(E⁻¹) → D` of a functor `L : EP → D` inverting the equivalences:
`[X ←F A →Φ Y] ↦ L(F)⁻¹ ≫ L(Φ)`. -/
def lift : EPLoc.{u} ⥤ D where
  obj X := L.obj X.toEP
  map {X Y} f := Quotient.lift (s := Diagram.setoid X.toEP Y.toEP) (liftMap L hL)
    (fun _ _ h => liftMap_eq_of_equiv L hL h) f
  map_id X := liftMap_id L hL X.toEP
  map_comp {X Y Z} f g := Quotient.inductionOn₂ (motive := fun (f : X ⟶ Y) (g : Y ⟶ Z) =>
    Quotient.lift (s := Diagram.setoid X.toEP Z.toEP) (liftMap L hL)
      (fun _ _ h => liftMap_eq_of_equiv L hL h) (f ≫ g) =
    Quotient.lift (s := Diagram.setoid X.toEP Y.toEP) (liftMap L hL)
      (fun _ _ h => liftMap_eq_of_equiv L hL h) f ≫
    Quotient.lift (s := Diagram.setoid Y.toEP Z.toEP) (liftMap L hL)
      (fun _ _ h => liftMap_eq_of_equiv L hL h) g) f g fun d e => liftMap_comp L hL d e

theorem lift_map_homMk (d : Diagram X Y) : (lift L hL).map (homMk d) = liftMap L hL d := rfl

theorem fac : localizationFunctor ⋙ lift L hL = L := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) fun X Y Φ => heq_of_eq ?_
  change inv (L.map (𝟙 X)) ≫ L.map Φ = L.map Φ
  simp

/-- `F₁([X ←F A →Φ Y]) = F₁(i(F))⁻¹ ≫ F₁(i(Φ))` for every functor out of `EP(E⁻¹)`
(`homMk_eq`). -/
theorem map_homMk_eq (F₁ : EPLoc.{u} ⥤ D) {X Y : EP.{u}} (d : Diagram X Y) :
    F₁.map (homMk d) = liftMap (localizationFunctor ⋙ F₁)
      (isInvertedBy_localizationFunctor.of_comp _ _ F₁) d := by
  have := isInvertedBy_localizationFunctor d.F d.isEquivalence_F
  have e : homMk d = inv (localizationFunctor.map d.F) ≫ localizationFunctor.map d.Φ :=
    homMk_eq d
  rw [e]
  exact (F₁.map_comp _ _).trans (congrArg (· ≫ F₁.map (localizationFunctor.map d.Φ))
    (F₁.map_inv (localizationFunctor.map d.F)))

/-- Every functor out of `EP(E⁻¹)` is the lift of its composite with `i`. -/
theorem eq_lift (F₁ : EPLoc.{u} ⥤ D) :
    F₁ = lift (localizationFunctor ⋙ F₁) (isInvertedBy_localizationFunctor.of_comp _ _ F₁) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) fun X Y f => heq_of_eq ?_
  induction f using Quotient.inductionOn with
  | h d => exact map_homMk_eq F₁ d

/-- Two functors out of `EP(E⁻¹)` that agree after `i` are equal: every generalized map is
`i(Φ) ∘ i(F)⁻¹` (`homMk_eq`). -/
theorem uniq (F₁ F₂ : EPLoc.{u} ⥤ D) (h : localizationFunctor ⋙ F₁ = localizationFunctor ⋙ F₂) :
    F₁ = F₂ := by
  rw [eq_lift F₁, eq_lift F₂]
  congr 1

/-- **The strict universal property** of `i : EP → EP(E⁻¹)` for every target category. -/
def strictUniversalPropertyFixedTarget (E : Type u₁) [Category.{v₁} E] :
    Localization.StrictUniversalPropertyFixedTarget localizationFunctor EP.equivalences.{u} E where
  inverts := isInvertedBy_localizationFunctor
  lift L hL := lift L hL
  fac L hL := fac L hL
  uniq := uniq

/-- **2021 p. 483 and Theorem 10.3.14, p. 491 (2017: p. 347, Theorem 10.5, p. 354)**: the
functor `i : EP → EP(E⁻¹)` is a localization of `EP` at the class `E` of equivalences
(Mathlib's `Functor.IsLocalization`). -/
instance isLocalization : localizationFunctor.{u}.IsLocalization EP.equivalences.{u} :=
  Functor.IsLocalization.mk' _ _ (strictUniversalPropertyFixedTarget _)
    (strictUniversalPropertyFixedTarget _)

/-- **The universal property of the localization** (2021 p. 483, Theorem 10.3.14): every functor
`L : EP → D` inverting the equivalences factors uniquely as `L = L' ∘ i` through
`i : EP → EP(E⁻¹)`. -/
theorem universal_property (L : EP.{u} ⥤ D) (hL : EP.equivalences.IsInvertedBy L) :
    ∃! L' : EPLoc.{u} ⥤ D, localizationFunctor ⋙ L' = L :=
  ⟨lift L hL, fac L hL, fun L' hL' => uniq L' (lift L hL) (hL'.trans (fac L hL).symm)⟩

end EPLoc

end EPLocalization

end Polyfold
