import Polyfold.Chapter16.StrongPolyfoldBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.3 (pp. 723–726; 2017: §16.3): **Definitions 16.3.6, 16.3.7, 16.3.8**.  Numbers and pages are
the 2021 text's.

# The category `S_PBS` and sc-smooth strong polyfold bundle maps

## The text, paraphrased

(p. 723) The objects of `S_PBS` are tuples `S = ((P : W → X, μ), Γ, γ)` with homeomorphisms
`Γ : |W| → Y`, `γ : |X| → Z` (`X` with (ZHOU), `(P, μ)` locally regular); `p_S = γ ∘ |P| ∘ Γ⁻¹`.
(Definition 16.3.6) A morphism `S → S'` is `(A, a, 𝔄, 𝔞)`: continuous `A : Y → Y'`, `a : Z → Z'`
with `p_{S'} ∘ A = a ∘ p_S`, and a generalized strong bundle map `𝔄 : W → W'` covering the
generalized map `𝔞 : X → X'`, with `Γ' ∘ |𝔄| = A ∘ Γ` and `γ' ∘ |𝔞| = a ∘ γ`; composition is
componentwise; the morphism is invertible if `A`, `a` are homeomorphisms and `𝔄` is a generalized
strong bundle isomorphism.  The class `c̄` of `p` consists of the structures related by
isomorphisms `(𝔄, Id_Y)`.  (Definition 16.3.7) Morphisms `(𝔄₀, A₀) : S₀ → S₀'`,
`(𝔄₁, A₁) : S₁ → S₁'` (`S₀, S₁` for `p`, `S₀', S₁'` for `p'`) are equivalent if there are
isomorphisms `(ℌ, Id_Y) : S₀ → S₁`,
`(ℌ', Id_{Y'}) : S₀' → S₁'` with `(𝔄₁, A₁) ∘ (ℌ, Id_Y) = (ℌ', Id_{Y'}) ∘ (𝔄₀, A₀)`; then `A₁ = A₀`
and `a₁ = a₀`.  (Definition 16.3.8) An sc-smooth strong polyfold bundle map
`(p, c̄) → (p', c̄')` is an equivalence class of such morphisms.

## What is formalized

* `SPBS` (the objects, bundling `Y`, `Z`, `p` and a structure of Definition 16.3.1), `SPBS.Hom`
  (**Definition 16.3.6**; `𝔞` is `𝔄.base`), `Hom.p_comm` (`p' ∘ A = a ∘ p` follows from the two
  squares and `|P'| ∘ |𝔄| = |𝔞| ∘ |P|`), the `Category` instance (composition
  componentwise), `Hom.IsInvertible`, `isIso_iff_isInvertible` (the invertible morphisms are the
  isomorphisms of the category).
* `exists_isInvertible_iff_equiv`: an invertible `(𝔄, Id_Y)` exists iff the structures are
  equivalent in the sense of Definition 16.3.3 (the text's description of `c̄`); `Hom.f_eq_id`
  (`Id_Y` forces `a = Id_Z`).
* `MorEquiv` (**Definition 16.3.7**), `MorEquiv.F_eq`, `MorEquiv.f_eq` (`A₁ = A₀`, `a₁ = a₀`),
  `MorEquiv.refl/symm/trans`.
* `StrongPolyfoldBundleMap c c'` (**Definition 16.3.8**): the quotient of the morphisms between
  representatives of `c` and `c'` by `MorEquiv`, with the underlying maps `toFun : Y → Y'`,
  `baseFun : Z → Z'` (well defined).

## Readings

* The objects of `S_PBS` are taken to be the structures of Definition 16.3.1 (with paracompact
  `|X|`), as the text then calls `S` "a strong polyfold bundle structure on `p_S`".
* `p_S` is recorded with the object (the text: "`p` is, of course, redundant information").
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization SBLocalization

/-- **The objects of `S_PBS`** (2021 p. 723): a strong polyfold bundle structure `S` on a map
`p : Y → Z` (Definition 16.3.1), with `Y`, `Z`, `p` recorded. -/
structure SPBS : Type (u + 1) where
  /-- The total space `Y`. -/
  Y : Type u
  /-- The base `Z`. -/
  Z : Type u
  [instY : TopologicalSpace Y]
  [instZ : TopologicalSpace Z]
  /-- `p_S = γ ∘ |P| ∘ Γ⁻¹`. -/
  p : Y → Z
  /-- The structure `((P : W → X, μ), Γ, γ)`. -/
  S : StrongPolyfoldBundleStructure p

attribute [instance] SPBS.instY SPBS.instZ

namespace SPBS

/-- A structure for `p` as an object of `S_PBS`. -/
abbrev mk' {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    (S : StrongPolyfoldBundleStructure p) : SPBS.{u} := ⟨Y, Z, p, S⟩

/-- **2021 Definition 16.3.6, p. 724 (2017: Definition 16.20)**: a **morphism** `(A, a, 𝔄, 𝔞)`
of `S_PBS`: continuous `A : Y → Y'`, `a : Z → Z'` and a generalized strong bundle map
`𝔄 : W → W'` (covering `𝔞 = 𝔄.base`) with `Γ' ∘ |𝔄| = A ∘ Γ` and `γ' ∘ |𝔞| = a ∘ γ`. -/
@[ext]
structure Hom (T T' : SPBS.{u}) : Type (u + 1) where
  /-- `A : Y → Y'`. -/
  F : T.Y → T'.Y
  /-- `a : Z → Z'`. -/
  f : T.Z → T'.Z
  continuous_F : Continuous F
  continuous_f : Continuous f
  /-- The generalized strong bundle map `𝔄 : W → W'`. -/
  𝔄 : GenSBMap T.S.A T'.S.A
  Γ_comm : ⇑T'.S.Γ ∘ 𝔄.orbitMap = F ∘ ⇑T.S.Γ
  γ_comm : ⇑T'.S.γ ∘ EPLoc.orbitMap 𝔄.base = f ∘ ⇑T.S.γ

namespace Hom

variable {T T' : SPBS.{u}}

/-- **`p_{S'} ∘ A = a ∘ p_S`** (Definition 16.3.6): it follows from the two squares and
`|P'| ∘ |𝔄| = |𝔞| ∘ |P|` (2021 p. 505). -/
theorem p_comm (m : Hom T T') : T'.p ∘ m.F = m.f ∘ T.p := by
  funext y
  obtain ⟨q, rfl⟩ := T.S.Γ.surjective y
  have h1 := congrFun m.Γ_comm q
  have h2 := congrFun m.γ_comm (T.S.A.E.projFunctor.orbitMap q)
  have h3 := congrFun (GenSBMap.orbitMap_square m.𝔄) q
  simp only [Function.comp_apply] at h1 h2 h3 ⊢
  rw [← h1, T'.S.p_Γ, T.S.p_Γ, h3, h2]

/-- The identity morphism `(Id_Y, Id_Z, [1_W], [1_X])`. -/
def id (T : SPBS.{u}) : Hom T T where
  F := _root_.id
  f := _root_.id
  continuous_F := continuous_id
  continuous_f := continuous_id
  𝔄 := show GenSBMap T.S.A T.S.A from 𝟙 (SEPLoc.of T.S.A)
  Γ_comm := by rw [SEPLoc.orbitMap_id]; rfl
  γ_comm := by rw [SEPLoc.baseOrbitMap_id]; rfl

/-- The composition `(A', a', 𝔄', 𝔞') ∘ (A, a, 𝔄, 𝔞) = (A' ∘ A, a' ∘ a, 𝔄' ∘ 𝔄, 𝔞' ∘ 𝔞)`. -/
def comp {T'' : SPBS.{u}} (m : Hom T T') (m' : Hom T' T'') : Hom T T'' where
  F := m'.F ∘ m.F
  f := m'.f ∘ m.f
  continuous_F := m'.continuous_F.comp m.continuous_F
  continuous_f := m'.continuous_f.comp m.continuous_f
  𝔄 := m.𝔄.comp m'.𝔄
  Γ_comm := by
    rw [GenSBMap.orbitMap_comp, ← Function.comp_assoc, m'.Γ_comm, Function.comp_assoc,
      m.Γ_comm, Function.comp_assoc]
  γ_comm := by
    rw [GenSBMap.baseOrbitMap_comp, ← Function.comp_assoc, m'.γ_comm, Function.comp_assoc,
      m.γ_comm, Function.comp_assoc]

end Hom

/-- **Definition 16.3.6**: `S_PBS` is a category (composition componentwise). -/
instance category : Category.{u + 1} SPBS.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp m := Hom.ext rfl rfl (Category.id_comp
    (show SEPLoc.of _ ⟶ SEPLoc.of _ from (m : Hom _ _).𝔄))
  comp_id m := Hom.ext rfl rfl (Category.comp_id
    (show SEPLoc.of _ ⟶ SEPLoc.of _ from (m : Hom _ _).𝔄))
  assoc m m' m'' := Hom.ext rfl rfl (Category.assoc
    (show SEPLoc.of _ ⟶ SEPLoc.of _ from (m : Hom _ _).𝔄)
    (show SEPLoc.of _ ⟶ SEPLoc.of _ from (m' : Hom _ _).𝔄)
    (show SEPLoc.of _ ⟶ SEPLoc.of _ from (m'' : Hom _ _).𝔄))

variable {T T' T'' : SPBS.{u}}

@[simp] theorem id_F (T : SPBS.{u}) : (𝟙 T : Hom T T).F = _root_.id := rfl
@[simp] theorem id_f (T : SPBS.{u}) : (𝟙 T : Hom T T).f = _root_.id := rfl
@[simp] theorem comp_F (m : T ⟶ T') (m' : T' ⟶ T'') :
    (m ≫ m' : Hom T T'').F = (m' : Hom T' T'').F ∘ (m : Hom T T').F := rfl
@[simp] theorem comp_f (m : T ⟶ T') (m' : T' ⟶ T'') :
    (m ≫ m' : Hom T T'').f = (m' : Hom T' T'').f ∘ (m : Hom T T').f := rfl
theorem comp_𝔄 (m : T ⟶ T') (m' : T' ⟶ T'') :
    (show SEPLoc.of _ ⟶ SEPLoc.of _ from (m ≫ m' : Hom T T'').𝔄) =
      (show SEPLoc.of _ ⟶ SEPLoc.of _ from (m : Hom T T').𝔄) ≫
        (show SEPLoc.of _ ⟶ SEPLoc.of _ from (m' : Hom T' T'').𝔄) := rfl
theorem id_𝔄 (T : SPBS.{u}) :
    (show SEPLoc.of _ ⟶ SEPLoc.of _ from (𝟙 T : Hom T T).𝔄) = 𝟙 (SEPLoc.of T.S.A) := rfl

/-- **Definition 16.3.6**: the morphism `(A, a, 𝔄, 𝔞)` is **invertible** if `A`, `a` are
homeomorphisms and `𝔄` is a generalized strong bundle isomorphism. -/
def Hom.IsInvertible (m : Hom T T') : Prop :=
  IsHomeomorph m.F ∧ IsHomeomorph m.f ∧ m.𝔄.IsGeneralizedIso

/-- The two-sided inverse of an invertible morphism. -/
def Hom.inv (m : Hom T T') (hm : m.IsInvertible) : Hom T' T :=
  have := SEPLoc.isIso_of_isGeneralizedIso hm.2.2
  { F := (hm.1.homeomorph _).symm
    f := (hm.2.1.homeomorph _).symm
    continuous_F := (hm.1.homeomorph _).symm.continuous
    continuous_f := (hm.2.1.homeomorph _).symm.continuous
    𝔄 := show GenSBMap T'.S.A T.S.A from CategoryTheory.inv
      (show SEPLoc.of T.S.A ⟶ SEPLoc.of T'.S.A from m.𝔄)
    Γ_comm := by
      funext q
      apply (hm.1.homeomorph _).injective
      rw [Function.comp_apply, Function.comp_apply, Homeomorph.apply_symm_apply]
      change m.F (T.S.Γ _) = _
      rw [← Function.comp_apply (f := m.F), ← m.Γ_comm, Function.comp_apply]
      exact congrArg T'.S.Γ (congrFun (SEPLoc.orbitMap_comp_inv
        (show SEPLoc.of T.S.A ⟶ SEPLoc.of T'.S.A from m.𝔄)) q)
    γ_comm := by
      funext q
      apply (hm.2.1.homeomorph _).injective
      rw [Function.comp_apply, Function.comp_apply, Homeomorph.apply_symm_apply]
      change m.f (T.S.γ _) = _
      rw [← Function.comp_apply (f := m.f), ← m.γ_comm, Function.comp_apply]
      exact congrArg T'.S.γ (congrFun (SEPLoc.baseOrbitMap_comp_inv
        (show SEPLoc.of T.S.A ⟶ SEPLoc.of T'.S.A from m.𝔄)) q) }

theorem Hom.comp_inv (m : Hom T T') (hm : m.IsInvertible) :
    (m ≫ (m.inv hm : T' ⟶ T) : T ⟶ T) = 𝟙 T := by
  have := SEPLoc.isIso_of_isGeneralizedIso hm.2.2
  refine Hom.ext ?_ ?_ (IsIso.hom_inv_id (show SEPLoc.of T.S.A ⟶ SEPLoc.of T'.S.A from m.𝔄))
  · funext y; exact (hm.1.homeomorph _).symm_apply_apply y
  · funext z; exact (hm.2.1.homeomorph _).symm_apply_apply z

theorem Hom.inv_comp (m : Hom T T') (hm : m.IsInvertible) :
    ((m.inv hm : T' ⟶ T) ≫ (m : T ⟶ T') : T' ⟶ T') = 𝟙 T' := by
  have := SEPLoc.isIso_of_isGeneralizedIso hm.2.2
  refine Hom.ext ?_ ?_ (IsIso.inv_hom_id (show SEPLoc.of T.S.A ⟶ SEPLoc.of T'.S.A from m.𝔄))
  · funext y; exact (hm.1.homeomorph _).apply_symm_apply y
  · funext z; exact (hm.2.1.homeomorph _).apply_symm_apply z

/-- **The invertible morphisms of Definition 16.3.6 are the isomorphisms of `S_PBS`.** -/
theorem isIso_iff_isInvertible (m : T ⟶ T') : IsIso m ↔ (m : Hom T T').IsInvertible := by
  refine ⟨fun h => ?_, fun hm => ⟨⟨Hom.inv m hm, Hom.comp_inv m hm, Hom.inv_comp m hm⟩⟩⟩
  obtain ⟨n, h1, h2⟩ := h.out
  have e1F : (n : Hom T' T).F ∘ (m : Hom T T').F = _root_.id := congrArg Hom.F h1
  have e2F : (m : Hom T T').F ∘ (n : Hom T' T).F = _root_.id := congrArg Hom.F h2
  have e1f : (n : Hom T' T).f ∘ (m : Hom T T').f = _root_.id := congrArg Hom.f h1
  have e2f : (m : Hom T T').f ∘ (n : Hom T' T).f = _root_.id := congrArg Hom.f h2
  have hiso : IsIso (show SEPLoc.of T.S.A ⟶ SEPLoc.of T'.S.A from (m : Hom T T').𝔄) :=
    ⟨⟨show SEPLoc.of T'.S.A ⟶ SEPLoc.of T.S.A from (n : Hom T' T).𝔄,
      congrArg Hom.𝔄 h1, congrArg Hom.𝔄 h2⟩⟩
  refine ⟨?_, ?_, (SEPLoc.isIso_iff_isGeneralizedIso _).1 hiso⟩
  · exact (Homeomorph.mk ⟨(m : Hom T T').F, (n : Hom T' T).F, fun x => congrFun e1F x,
      fun y => congrFun e2F y⟩ (m : Hom T T').continuous_F (n : Hom T' T).continuous_F).isHomeomorph
  · exact (Homeomorph.mk ⟨(m : Hom T T').f, (n : Hom T' T).f, fun x => congrFun e1f x,
      fun y => congrFun e2f y⟩ (m : Hom T T').continuous_f (n : Hom T' T).continuous_f).isHomeomorph

/-! ### Isomorphisms `(𝔄, Id_Y)` and Definition 16.3.3 -/

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}

/-- A morphism `(𝔄, Id_Y)` between two structures for the same `p` has `a = Id_Z` (`p` is
surjective). -/
theorem Hom.f_eq_id {S S' : StrongPolyfoldBundleStructure p} (m : Hom (mk' S) (mk' S'))
    (hF : m.F = _root_.id) : m.f = _root_.id := by
  funext z
  obtain ⟨y, rfl⟩ := S.surjective_p z
  have h := congrFun m.p_comm y
  simp only [Function.comp_apply, hF] at h
  exact h.symm

/-- **The description of `c̄` (2021 p. 725)**: an invertible morphism `(𝔄, Id_Y) : S → S'` exists
iff `S` and `S'` are equivalent (Definition 16.3.3). -/
theorem exists_isInvertible_iff_equiv {S S' : StrongPolyfoldBundleStructure p} :
    (∃ m : Hom (mk' S) (mk' S'), m.IsInvertible ∧ m.F = _root_.id) ↔
      StrongPolyfoldBundleStructure.Equiv S S' := by
  constructor
  · rintro ⟨m, hm, hF⟩
    have hf := m.f_eq_id hF
    refine ⟨m.𝔄, hm.2.2, ?_, ?_⟩
    · have h := m.γ_comm
      rw [hf] at h
      exact h
    · have h := m.Γ_comm
      rw [hF] at h
      exact h
  · rintro ⟨F, hF, hγ, hΓ⟩
    refine ⟨⟨_root_.id, _root_.id, continuous_id, continuous_id, F, hΓ, hγ⟩,
      ⟨(Homeomorph.refl Y).isHomeomorph, (Homeomorph.refl Z).isHomeomorph, hF⟩, rfl⟩

/-- The inverse of an isomorphism `(ℌ, Id_Y)` is of the form `(ℌ⁻¹, Id_Y)`. -/
theorem inv_F_eq_id {S S' : StrongPolyfoldBundleStructure p} (K : mk' S ⟶ mk' S') [IsIso K]
    (hK : (K : Hom _ _).F = _root_.id) : (CategoryTheory.inv K : Hom _ _).F = _root_.id := by
  have h1 : (K : Hom _ _).F ∘ (CategoryTheory.inv K : Hom _ _).F = _root_.id :=
    congrArg Hom.F (IsIso.inv_hom_id K)
  rw [hK] at h1
  exact h1

/-! ### Definition 16.3.7 -/

variable {Y' Z' : Type u} [TopologicalSpace Y'] [TopologicalSpace Z'] {p' : Y' → Z'}

/-- **2021 Definition 16.3.7, p. 725 (2017: Definition 16.21)**: morphisms
`m₀ : S₀ → S₀'`, `m₁ : S₁ → S₁'` (`S₀, S₁` for `p`, `S₀', S₁'` for `p'`) are **equivalent** if
there are isomorphisms `(ℌ, Id_Y) : S₀ → S₁`, `(ℌ', Id_{Y'}) : S₀' → S₁'` with
`m₁ ∘ (ℌ, Id_Y) = (ℌ', Id_{Y'}) ∘ m₀`. -/
def MorEquiv {S₀ S₁ : StrongPolyfoldBundleStructure p} {S₀' S₁' : StrongPolyfoldBundleStructure p'}
    (m₀ : mk' S₀ ⟶ mk' S₀') (m₁ : mk' S₁ ⟶ mk' S₁') : Prop :=
  ∃ (H : mk' S₀ ⟶ mk' S₁) (H' : mk' S₀' ⟶ mk' S₁'),
    (H : Hom _ _).IsInvertible ∧ (H : Hom _ _).F = _root_.id ∧
    (H' : Hom _ _).IsInvertible ∧ (H' : Hom _ _).F = _root_.id ∧ H ≫ m₁ = m₀ ≫ H'

namespace MorEquiv

variable {S₀ S₁ S₂ : StrongPolyfoldBundleStructure p}
  {S₀' S₁' S₂' : StrongPolyfoldBundleStructure p'}
  {m₀ : mk' S₀ ⟶ mk' S₀'} {m₁ : mk' S₁ ⟶ mk' S₁'} {m₂ : mk' S₂ ⟶ mk' S₂'}

/-- **Definition 16.3.7**, "it follows that `A₁ = A₀`". -/
theorem F_eq (h : MorEquiv m₀ m₁) : (m₁ : Hom _ _).F = (m₀ : Hom _ _).F := by
  obtain ⟨H, H', -, hH, -, hH', e⟩ := h
  have := congrArg Hom.F e
  simp only [comp_F, hH, hH'] at this
  exact this

/-- **Definition 16.3.7**, "also `a₁ = a₀`". -/
theorem f_eq (h : MorEquiv m₀ m₁) : (m₁ : Hom _ _).f = (m₀ : Hom _ _).f := by
  obtain ⟨H, H', -, hH, -, hH', e⟩ := h
  have := congrArg Hom.f e
  simp only [comp_f, Hom.f_eq_id H hH, Hom.f_eq_id H' hH'] at this
  exact this

theorem refl (m₀ : mk' S₀ ⟶ mk' S₀') : MorEquiv m₀ m₀ :=
  ⟨𝟙 _, 𝟙 _, (isIso_iff_isInvertible _).1 inferInstance, rfl,
    (isIso_iff_isInvertible _).1 inferInstance, rfl, by rw [Category.id_comp, Category.comp_id]⟩

theorem symm (h : MorEquiv m₀ m₁) : MorEquiv m₁ m₀ := by
  obtain ⟨H, H', hHi, hH, hH'i, hH', e⟩ := h
  have : IsIso H := (isIso_iff_isInvertible _).2 hHi
  have : IsIso H' := (isIso_iff_isInvertible _).2 hH'i
  refine ⟨CategoryTheory.inv H, CategoryTheory.inv H',
    (isIso_iff_isInvertible _).1 inferInstance, inv_F_eq_id H hH,
    (isIso_iff_isInvertible _).1 inferInstance, inv_F_eq_id H' hH', ?_⟩
  rw [IsIso.inv_comp_eq, ← Category.assoc, e, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

theorem trans (h : MorEquiv m₀ m₁) (h' : MorEquiv m₁ m₂) : MorEquiv m₀ m₂ := by
  obtain ⟨H, H', hHi, hH, hH'i, hH', e⟩ := h
  obtain ⟨K, K', hKi, hK, hK'i, hK', e'⟩ := h'
  have : IsIso H := (isIso_iff_isInvertible _).2 hHi
  have : IsIso H' := (isIso_iff_isInvertible _).2 hH'i
  have : IsIso K := (isIso_iff_isInvertible _).2 hKi
  have : IsIso K' := (isIso_iff_isInvertible _).2 hK'i
  refine ⟨H ≫ K, H' ≫ K', (isIso_iff_isInvertible _).1 inferInstance, ?_,
    (isIso_iff_isInvertible _).1 inferInstance, ?_, ?_⟩
  · rw [comp_F, hH, hK]; rfl
  · rw [comp_F, hH', hK']; rfl
  · rw [Category.assoc, e', ← Category.assoc, e, Category.assoc]

end MorEquiv

/-! ### Definition 16.3.8 -/

/-- A morphism of `S_PBS` between representatives of `c` and `c'`. -/
structure MorRep (c : StrongPolyfoldBundle p) (c' : StrongPolyfoldBundle p') : Type (u + 1) where
  /-- The source structure, in `c`. -/
  S : StrongPolyfoldBundleStructure p
  hS : ⟦S⟧ = c
  /-- The target structure, in `c'`. -/
  S' : StrongPolyfoldBundleStructure p'
  hS' : ⟦S'⟧ = c'
  /-- The morphism. -/
  m : mk' S ⟶ mk' S'

/-- Definition 16.3.7 on representatives. -/
def MorRep.Rel {c : StrongPolyfoldBundle p} {c' : StrongPolyfoldBundle p'} (a b : MorRep c c') :
    Prop :=
  MorEquiv a.m b.m

instance MorRep.setoid (c : StrongPolyfoldBundle p) (c' : StrongPolyfoldBundle p') :
    Setoid (MorRep c c') where
  r := MorRep.Rel
  iseqv := ⟨fun a => MorEquiv.refl a.m, MorEquiv.symm, MorEquiv.trans⟩

/-- **2021 Definition 16.3.8, p. 726 (2017: Definition 16.22)**: an **sc-smooth strong polyfold
bundle map** `(p : Y → Z, c̄) → (p' : Y' → Z', c̄')` is an equivalence class (Definition 16.3.7) of
morphisms of `S_PBS` between representatives of `c̄` and `c̄'`. -/
abbrev StrongPolyfoldBundleMap (c : StrongPolyfoldBundle p) (c' : StrongPolyfoldBundle p') :
    Type (u + 1) :=
  Quotient (MorRep.setoid c c')

namespace StrongPolyfoldBundleMap

variable {c : StrongPolyfoldBundle p} {c' : StrongPolyfoldBundle p'}

/-- The underlying continuous map `A : Y → Y'` of an sc-smooth strong polyfold bundle map (well
defined by `MorEquiv.F_eq`). -/
def toFun (Fb : StrongPolyfoldBundleMap c c') : Y → Y' :=
  Quotient.lift (fun a : MorRep c c' => (a.m : Hom _ _).F)
    (fun _ _ h => (MorEquiv.F_eq h).symm) Fb

/-- The underlying continuous map `a : Z → Z'` (well defined by `MorEquiv.f_eq`). -/
def baseFun (Fb : StrongPolyfoldBundleMap c c') : Z → Z' :=
  Quotient.lift (fun a : MorRep c c' => (a.m : Hom _ _).f)
    (fun _ _ h => (MorEquiv.f_eq h).symm) Fb

theorem continuous_toFun (Fb : StrongPolyfoldBundleMap c c') : Continuous Fb.toFun :=
  Quotient.inductionOn (motive := fun Fb : StrongPolyfoldBundleMap c c' =>
    Continuous Fb.toFun) Fb fun a => (a.m : Hom _ _).continuous_F

/-- `p' ∘ A = a ∘ p` for an sc-smooth strong polyfold bundle map. -/
theorem p_comm (Fb : StrongPolyfoldBundleMap c c') : p' ∘ Fb.toFun = Fb.baseFun ∘ p :=
  Quotient.inductionOn (motive := fun Fb : StrongPolyfoldBundleMap c c' =>
    p' ∘ Fb.toFun = Fb.baseFun ∘ p) Fb fun a => (a.m : Hom _ _).p_comm

/-- The identity of a strong polyfold bundle, as an sc-smooth strong polyfold bundle map. -/
def id (c : StrongPolyfoldBundle p) : StrongPolyfoldBundleMap c c :=
  ⟦⟨c.out, Quotient.out_eq c, c.out, Quotient.out_eq c, 𝟙 _⟩⟧

theorem toFun_id (c : StrongPolyfoldBundle p) : (id c).toFun = _root_.id := rfl

end StrongPolyfoldBundleMap

end SPBS

end Polyfold
