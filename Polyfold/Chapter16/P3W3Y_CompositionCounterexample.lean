import Polyfold.Chapter16.P3W3Y_PolyfoldMaps

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.1, p. 711: the claim of **Definition 16.1.10** (2017: Definition 16.7) that the composition
of sc-smooth maps "does not depend on the choices involved".  Numbers and pages are the 2021
text's.

# The composition of sc-smooth maps of polyfolds depends on the representatives

## The text, paraphrased

(Definition 16.1.10) For `f̂ : (Z, c) → (W, d)` and `ĝ : (W, d) → (V, e)`,
`ĝ ∘ f̂ = [(g ∘ f, 𝔤 ∘ 𝔣)]` with representatives `(f, 𝔣) : (X, α) → (Y, β)`,
`(g, 𝔤) : (Y, β) → (U, γ)`; the definition does not depend on the choices.

## The check

Changing the representative of `f̂` by an isomorphism `(k, Id_W)` of the middle structure turns
`𝔤 ∘ 𝔣` into `𝔤 ∘ k ∘ 𝔣`.  When `k` is not determined by `Id_W` (the uniqueness after
Definition 16.1.2 does not hold as we read it, `not_uniqueness_16_1_2`), the two composites can
lie in different classes.  The example: `Z = W = V = ℝ`, `(X, α) = (U, γ)` the polyfold
structure `ℤ/3 × ℝ ⇉ ℝ` (trivial action, `z3PolyfoldStructure`), `(Y, β)` the polyfold
structure `(ℤ/3)² × ℝ ⇉ ℝ` (trivial action, `k2Structure`; (ZHOU), `|Y| ≅ ℝ`), all maps
`f = g = Id_ℝ`:
* `𝔣 = [ι]`, `ι(g) = (g, 1)`; `𝔣' = [ι] ≫ [σ]`, `σ(g, h) = (h, g)` (an automorphism of `Y` over
  `Id_ℝ`), so `(Id, 𝔣) ∼ (Id, 𝔣')` (Definition 16.1.6 with `h = 1`, `k = [σ]`);
* `𝔤 = [pr₁]`, `pr₁(g, h) = g`;
* `𝔤 ∘ 𝔣 = [pr₁ ∘ ι] = [1_X]`, while `𝔤 ∘ 𝔣' = [pr₁ ∘ σ ∘ ι] = [T]` with `T(g) = 1`.
`(Id, [1_X]) ∼ (Id, [T])` would make `[T] = h⁻¹ ≫ k` a generalized isomorphism, so `T` an
equivalence (Theorem 10.3.10), but `T` is not faithful.

* **`not_definition_16_1_10 : ¬ PSHom.Definition_16_1_10.{0}`**.
* **`not_exists_comp`**: no map `ScMap c d → ScMap d e → ScMap c e` agrees with
  `[(g ∘ f, 𝔤 ∘ 𝔣)]` on all representatives with a common middle structure.
* The strongest form we prove: Definition 16.1.10 for an effective middle polyfold
  (`PSHom.Equiv.comp_of_isEffective`, `ScMap.comp`, the category `EffPolyfold`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

namespace CompositionCounterexample

open EPLocalization EPLocalization.EPLoc EpGroupoid EpGroupoid.Examples
  LocalizationLRCounterexample

/-- The group `(ℤ/3)²`. -/
abbrev K2 : Type := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)

/-- The trivial action of `(ℤ/3)²` on `ℝ`. -/
instance instMulActionK2 : MulAction K2 (Fin 1 → ℝ) where
  smul _ y := y
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem isScSmoothMap_k2_smul (k : K2) :
    (rnPolyfold 1).IsScSmoothMap (rnPolyfold 1) fun y : Fin 1 → ℝ => k • y :=
  MPolyfold.isScSmoothMap_id

/-- **`(ℤ/3)² × ℝ ⇉ ℝ`**, the translation groupoid of the trivial action. -/
def k2EpGroupoid : EpGroupoid (Fin 1 → ℝ) (K2 × (Fin 1 → ℝ)) :=
  actionEpGroupoid isScSmoothMap_k2_smul

/-- `(ℤ/3)² × ℝ ⇉ ℝ` as an object of `EP`. -/
abbrev k2EP : EP.{0} := ⟨Fin 1 → ℝ, K2 × (Fin 1 → ℝ), k2EpGroupoid⟩

theorem isZhou_k2 : k2EpGroupoid.IsZhou :=
  isZhou_of_trivialSubgroup_eq_top _ fun _ => eq_top_iff.2 fun _ _ =>
    k2EpGroupoid.mem_trivialSet_iff_eventually.2 (Eventually.of_forall fun _ => rfl)

theorem injective_π_k2 : Function.Injective k2EpGroupoid.π := fun x y h => by
  obtain ⟨φ, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 h
  exact h1.symm.trans h2

theorem isHomeomorph_π_k2 : IsHomeomorph k2EpGroupoid.π :=
  ⟨k2EpGroupoid.continuous_π, k2EpGroupoid.proposition_7_1_8,
    ⟨injective_π_k2, k2EpGroupoid.surjective_π⟩⟩

/-- `|(ℤ/3)² × ℝ ⇉ ℝ| ≃ₜ ℝ`. -/
def k2OrbitHomeomorph : k2EpGroupoid.OrbitSpace ≃ₜ (Fin 1 → ℝ) :=
  (isHomeomorph_π_k2.homeomorph _).symm

/-- **The polyfold structure `(ℤ/3)² × ℝ ⇉ ℝ` on `ℝ`** (Definition 16.1.1). -/
def k2Structure : PolyfoldStructure (Fin 1 → ℝ) :=
  ⟨k2EP, k2OrbitHomeomorph.paracompactSpace_iff.2 inferInstance, isZhou_k2, k2OrbitHomeomorph⟩

theorem k2Structure_β_π (x : Fin 1 → ℝ) : k2Structure.β (k2Structure.X.X.π x) = x :=
  (isHomeomorph_π_k2.homeomorph _).symm_apply_apply x

theorem z3_β_π (x : Fin 1 → ℝ) :
    PolyfoldStructure.z3PolyfoldStructure.β
      (PolyfoldStructure.z3PolyfoldStructure.X.X.π x) = x :=
  (isHomeomorph_π_trivialZ3.homeomorph _).symm_apply_apply x

/-! ### The functors -/

/-- `ι : ℤ/3 → (ℤ/3)²`, `g ↦ (g, 1)`, on `… × ℝ`. -/
def ι : EpFunctor trivialZ3EpGroupoid k2EpGroupoid where
  obj := _root_.id
  mor p := ((p.1, 1), p.2)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp φ ψ _ := by
    change ((φ.1 * ψ.1, 1), ψ.2) = ((φ.1, 1) * (ψ.1, 1), ψ.2)
    rw [Prod.mk_mul_mk, mul_one]
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor := isScSmoothMap_prod_discrete_iff.2 fun k => isScSmoothMap_sheet (k, 1)

/-- `pr₁ : (ℤ/3)² → ℤ/3`, `(g, h) ↦ g`. -/
def pr₁ : EpFunctor k2EpGroupoid trivialZ3EpGroupoid where
  obj := _root_.id
  mor p := (p.1.1, p.2)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor := isScSmoothMap_prod_discrete_iff.2 fun k => isScSmoothMap_sheet k.1

/-- `σ : (ℤ/3)² → (ℤ/3)²`, `(g, h) ↦ (h, g)`. -/
def σ : EpFunctor k2EpGroupoid k2EpGroupoid where
  obj := _root_.id
  mor p := ((p.1.2, p.1.1), p.2)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor :=
    isScSmoothMap_prod_discrete_iff.2 fun k => isScSmoothMap_sheet (k.2, k.1)

/-- `T : ℤ/3 → ℤ/3`, `g ↦ 1`. -/
def T : EpFunctor trivialZ3EpGroupoid trivialZ3EpGroupoid where
  obj := _root_.id
  mor p := (1, p.2)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := Prod.ext (mul_one (1 : Multiplicative (ZMod 3))).symm rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor := isScSmoothMap_prod_discrete_iff.2 fun _ => isScSmoothMap_sheet 1

/-- The morphisms of `EP` between `z3EP` and `k2EP`. -/
abbrev ιE : z3EP ⟶ k2EP := ι
abbrev pr₁E : k2EP ⟶ z3EP := pr₁
abbrev σE : k2EP ⟶ k2EP := σ
abbrev TE : z3EP ⟶ z3EP := T

theorem ι_pr₁ : ιE ≫ pr₁E = 𝟙 z3EP := EpFunctor.ext rfl rfl
theorem ι_σ_pr₁ : ιE ≫ σE ≫ pr₁E = TE := EpFunctor.ext rfl rfl
theorem σ_σ : σE ≫ σE = 𝟙 k2EP := EpFunctor.ext rfl rfl

/-- `T` is not an equivalence: it is not faithful. -/
theorem not_isEquivalence_T : ¬ T.IsEquivalence := fun h => by
  have e := h.mor_injective (φ := (Multiplicative.ofAdd (1 : ZMod 3), 0))
    (φ' := (1, 0)) rfl rfl rfl
  exact absurd (congrArg Prod.fst e) (by decide)

/-- `[T]` is not a generalized isomorphism (Theorem 10.3.10). -/
theorem not_isIso_T : ¬ IsIso (localizationFunctor.map TE) := fun h =>
  not_isEquivalence_T ((isIso_homMk_iff (Diagram.ofFunctor TE)).1 h)

/-! ### The morphisms of `PS` -/

open PolyfoldStructure

/-- The orbit map of the generalized map of a functor which is the identity on objects. -/
theorem orbitMap_map_π {A B : EP.{0}} (Φ : A ⟶ B) (x : A.Obj) :
    orbitMap (localizationFunctor.map Φ) (A.X.π x) = B.X.π (Φ.obj x) := by
  have h := (Diagram.ofFunctor Φ).orbitMap_orbitMap_F (A.X.π x)
  change (Diagram.ofFunctor Φ).orbitMap ((EpFunctor.id A.X).orbitMap (A.X.π x)) =
    Φ.orbitMap (A.X.π x) at h
  rw [EpFunctor.orbitMap_id, GroupoidFunctor.orbitMap_π] at h
  exact h

/-- `(Id, 𝔣) : (X, α) → (Y, β)` for `𝔣 = [ι] ≫ k`, `k ∈ {1, [σ]}`. -/
def a (k : k2EP ⟶ k2EP) (hk : ∀ x, k.obj x = x) : PSHom z3PolyfoldStructure k2Structure :=
  ⟨_root_.id, localizationFunctor.map (ιE ≫ k), by
    funext z
    obtain ⟨x, rfl⟩ := z3PolyfoldStructure.X.X.surjective_π z
    have e := orbitMap_map_π (ιE ≫ k) x
    simp only [Function.comp_apply, id]
    erw [e]
    exact (z3_β_π x).trans ((k2Structure_β_π _).trans (hk x)).symm⟩

/-- `(Id, [pr₁]) : (Y, β) → (U, γ)`. -/
def b : PSHom k2Structure z3PolyfoldStructure :=
  ⟨_root_.id, localizationFunctor.map pr₁E, by
    funext z
    obtain ⟨x, rfl⟩ := k2Structure.X.X.surjective_π z
    have e := orbitMap_map_π pr₁E x
    simp only [Function.comp_apply, id]
    erw [e]
    exact (k2Structure_β_π x).trans (z3_β_π _).symm⟩

/-- `(Id, [σ]) : (Y, β) → (Y, β)`, an isomorphism over the identity. -/
def kσ : PSHom k2Structure k2Structure :=
  ⟨_root_.id, localizationFunctor.map σE, by
    funext z
    obtain ⟨x, rfl⟩ := k2Structure.X.X.surjective_π z
    have e := orbitMap_map_π σE x
    simp only [Function.comp_apply, id]
    erw [e]
    rfl⟩

theorem isGeneralizedIso_σ : IsGeneralizedIso (localizationFunctor.map σE) :=
  ⟨localizationFunctor.map σE,
    by rw [← CategoryTheory.Functor.map_comp, σ_σ, CategoryTheory.Functor.map_id],
    by rw [← CategoryTheory.Functor.map_comp, σ_σ, CategoryTheory.Functor.map_id]⟩

theorem kσ_isIdIso : kσ.IsIdIso := ⟨rfl, isGeneralizedIso_σ⟩

/-- `(Id, [ι]) ∼ (Id, [ι] ≫ [σ])` (Definition 16.1.6 with `h = 1`, `k = [σ]`). -/
theorem a_equiv : (a (𝟙 _) fun _ => rfl).Equiv (a σE fun _ => rfl) :=
  ⟨PSHom.id _, kσ, PSHom.isIdIso_id _, kσ_isIdIso, PSHom.ext (by
    change 𝟙 _ ≫ localizationFunctor.map (ιE ≫ σE) =
      localizationFunctor.map (ιE ≫ 𝟙 _) ≫ localizationFunctor.map σE
    rw [Category.id_comp, Category.comp_id, CategoryTheory.Functor.map_comp])⟩

theorem gen_comp_one :
    ((a (𝟙 _) fun _ => rfl).comp b).gen = 𝟙 (EPLoc.of z3PolyfoldStructure.X) := by
  change localizationFunctor.map (ιE ≫ 𝟙 _) ≫ localizationFunctor.map pr₁E = 𝟙 (EPLoc.of z3EP)
  rw [← CategoryTheory.Functor.map_comp, Category.comp_id, ι_pr₁,
    CategoryTheory.Functor.map_id]
  rfl

theorem gen_comp_σ : ((a σE fun _ => rfl).comp b).gen =
    (localizationFunctor.map TE : EPLoc.of z3PolyfoldStructure.X ⟶ _) := by
  change localizationFunctor.map (ιE ≫ σE) ≫ localizationFunctor.map pr₁E =
    localizationFunctor.map TE
  rw [← CategoryTheory.Functor.map_comp, Category.assoc, ι_σ_pr₁]

/-- **The two composites are not equivalent**: `(Id, [1_X]) ≁ (Id, [T])`. -/
theorem not_equiv_comp :
    ¬ ((a (𝟙 _) fun _ => rfl).comp b).Equiv ((a σE fun _ => rfl).comp b) := by
  rintro ⟨h, k, hh, hk, he⟩
  have hg : h.gen ≫ ((a σE fun _ => rfl).comp b).gen =
      ((a (𝟙 _) fun _ => rfl).comp b).gen ≫ k.gen := congrArg PSHom.gen he
  rw [gen_comp_σ, gen_comp_one, Category.id_comp] at hg
  have : IsIso h.gen := (isGeneralizedIso_iff_isIso _).1 hh.2
  have hk' : IsIso k.gen := (isGeneralizedIso_iff_isIso _).1 hk.2
  have hc : IsIso (h.gen ≫ (localizationFunctor.map TE : EPLoc.of z3PolyfoldStructure.X ⟶ _)) :=
    hg.symm ▸ hk'
  exact not_isIso_T (@IsIso.of_isIso_comp_left _ _ _ _ _ h.gen _ _ hc)

/-- **2021 Definition 16.1.10, p. 711 (2017: Definition 16.7): the claim that the composition does
not depend on the choices does not hold as we read it.**  `(Id, [ι]) ∼ (Id, [ι] ≫ [σ])` and
`(Id, [pr₁]) ∼ (Id, [pr₁])`, but the composites `(Id, [1_X])` and `(Id, [T])` are not
equivalent. -/
theorem not_definition_16_1_10 : ¬ PSHom.Definition_16_1_10.{0} := fun H =>
  not_equiv_comp (H _ _ _ _ _ _ _ _ _ _ _ b b a_equiv (PSHom.Equiv.refl b))

/-- **The class-level form**: for `c = e = [ℤ/3 × ℝ ⇉ ℝ]` and `d = [(ℤ/3)² × ℝ ⇉ ℝ]`, no map
`ScMap c d → ScMap d e → ScMap c e` is given by `[(g ∘ f, 𝔤 ∘ 𝔣)]` on all representatives with a
common middle structure. -/
theorem not_exists_comp :
    ¬ ∃ comp : PolyfoldClass.ScMap z3Polyfold ⟦k2Structure⟧ →
        PolyfoldClass.ScMap ⟦k2Structure⟧ z3Polyfold →
        PolyfoldClass.ScMap z3Polyfold z3Polyfold,
      ∀ (p : PolyfoldStructure (Fin 1 → ℝ)) (hp : (⟦p⟧ : PolyfoldClass _) = z3Polyfold)
        (q : PolyfoldStructure (Fin 1 → ℝ)) (hq : (⟦q⟧ : PolyfoldClass _) = ⟦k2Structure⟧)
        (r : PolyfoldStructure (Fin 1 → ℝ)) (hr : (⟦r⟧ : PolyfoldClass _) = z3Polyfold)
        (φ : PSHom p q) (ψ : PSHom q r),
        comp (PolyfoldClass.ScMap.mk p hp q hq φ) (PolyfoldClass.ScMap.mk q hq r hr ψ) =
          PolyfoldClass.ScMap.mk p hp r hr (φ.comp ψ) := by
  rintro ⟨comp, hcomp⟩
  have e1 := hcomp _ rfl _ rfl _ rfl (a (𝟙 _) fun _ => rfl) b
  have e2 := hcomp _ rfl _ rfl _ rfl (a σE fun _ => rfl) b
  have e3 : PolyfoldClass.ScMap.mk (c := z3Polyfold) (d := ⟦k2Structure⟧) _ rfl _ rfl
      (a (𝟙 _) fun _ => rfl) = PolyfoldClass.ScMap.mk _ rfl _ rfl (a σE fun _ => rfl) :=
    Quotient.sound a_equiv
  have e4 : PolyfoldClass.ScMap.mk (c := z3Polyfold) (d := z3Polyfold) _ rfl _ rfl
      ((a (𝟙 _) fun _ => rfl).comp b) =
      PolyfoldClass.ScMap.mk _ rfl _ rfl ((a σE fun _ => rfl).comp b) := by
    exact e1.symm.trans ((congrArg₂ comp e3 rfl).trans e2)
  exact not_equiv_comp (Quotient.exact e4)

/-- The middle structure of the counterexample is not effective (as required: for an effective
middle structure Definition 16.1.10 holds, `PSHom.Equiv.comp_of_isEffective`). -/
theorem not_isEffective_k2 : ¬ k2EpGroupoid.IsEffective := fun h => by
  have e := (EP.isEffective_iff_trivialSet k2EP).1 h 0
    ⟨((Multiplicative.ofAdd (1 : ZMod 3), 1), 0), rfl, rfl⟩
    (k2EpGroupoid.mem_trivialSet_iff_eventually.2 (Eventually.of_forall fun _ => rfl))
  exact absurd (congrArg (fun g : k2EpGroupoid.Isotropy 0 => g.val.1.1) e) (by decide)

end CompositionCounterexample

end Polyfold
