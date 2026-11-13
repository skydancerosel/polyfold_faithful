import Polyfold.Chapter16.P3H_TangentPolyfold
import Polyfold.Chapter10.EquivalenceReduced

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.1, pp. 709–711: the category `PS` of polyfold structures, **Definitions 16.1.6, 16.1.8,
16.1.10, 16.1.11** and **Remark 16.1.9** (2017: Definitions 16.5–16.8, Remark 16.2).  Numbers and
pages are the 2021 text's.

# Sc-smooth maps of polyfolds

## The text, paraphrased

(p. 709) The category `PS` has as objects the polyfold structures `(X, α)`, `α : |X| ≃ Z_α`, and
as morphisms the pairs `(f, 𝔣) : (X, α) → (Y, β)` of a continuous map `f : Z_α → Z_β` and a
generalized map `𝔣 : X → Y` with `f ∘ α = β ∘ |𝔣|`; composition is componentwise and
`1_{(X,α)} = ([1_X], Id)`.  (Definition 16.1.6) Two morphisms `(f, 𝔣) : (X, α) → (Y, β)` and
`(f', 𝔣') : (X', α') → (Y', β')` between structures of `c` and `d` are equivalent if
`(f', 𝔣') ∘ (h, Id_Z) = (k, Id_W) ∘ (f, 𝔣)` for isomorphisms `(h, Id_Z)`, `(k, Id_W)` of `PS`;
then `f = f'`.  (Definition 16.1.8) An sc-smooth map `(Z, c) → (W, d)` is a class of such
morphisms; (Remark 16.1.9) its continuous map `f` does not depend on the representative.
(Definition 16.1.10) The composition is `[(g ∘ f, 𝔤 ∘ 𝔣)]` for representatives with a common
middle structure; "the definition does not depend on the choices involved".  (Definition 16.1.11)
The polyfold category `P`: polyfolds and sc-smooth maps, `1_{(Z,c)} = [([1_X], Id_Z)]`.

## What is formalized

* `EpFunctor.IsEquivalence.isEffective_iff`, `EPLoc.isEffective_iff_of_isGeneralizedIso`:
  effectiveness is invariant under equivalences and generalized isomorphisms (Remark 10.1.12);
  `PolyfoldClass.IsEffective` (one, then every, structure of `c` effective).
* `PSHom p q` (the morphisms of `PS`), `PSHom.id`, `PSHom.comp`, `PSHom.f_eq`
  (`f = β ∘ |𝔣| ∘ α⁻¹`), `PSHom.continuous_f`, `PSHom.ext`; **`PSCat`, the category `PS`**
  (a Mathlib `Category`).
* **Definition 16.1.6**: `PSHom.Equiv` (literally `(h, Id) ≫ (f', 𝔣') = (f, 𝔣) ≫ (k, Id)` in
  `PS`), `Equiv.f_eq` (`f = f'`), `Equiv.refl/symm/trans`; `MapRep`, `MapRep.setoid`.
* **Definition 16.1.8**: `PolyfoldClass.ScMap c d`, the quotient; `ScMap.exists_rep` (every class
  has a representative between any two given structures of `c` and `d`, the remark after
  Definition 16.1.6); **Remark 16.1.9**: `ScMap.toFun` (`f`, well defined), `ScMap.remark_16_1_9`.
* **Definition 16.1.10**: `PSHom.Definition_16_1_10` (independence of the choices, as a `Prop`).
  It does not hold as we read it: `not_definition_16_1_10` in `P3W3Y_CompositionCounterexample`.
  It holds when the middle structure is effective: `PSHom.Equiv.comp_of_isEffective`
  (Theorem 10.3.19 for an effective target makes the isomorphism `k` unique).
* **Definitions 16.1.10–16.1.11 for effective polyfolds**: `ScMap.comp` (for an effective middle
  polyfold), `ScMap.id` (`id_eq`: the class of `([1_X], Id_Z)` for every `(X, α) ∈ c`, without
  effectiveness), and **`EffPolyfold`, the polyfold category on effective polyfolds** (a Mathlib
  `Category`), with the witness `EffPolyfold.point`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization EPLocalization.EPLoc

/-! ### Effectiveness is invariant under equivalences -/

/-- `X` is effective iff every element acting trivially is the unit (Definition 7.2.1 via
Lemma 7.2.3). -/
theorem EP.isEffective_iff_trivialSet (A : EP.{u}) :
    A.X.IsEffective ↔ ∀ x (g : A.X.Isotropy x), g ∈ A.X.trivialSet x → g = 1 := by
  rw [EpGroupoid.isEffective_iff_forall_naturalRep]
  exact ⟨fun h x g ⟨R, hR⟩ => h x R g hR, fun h x R g hR => h x g ⟨R, hR⟩⟩

/-- **Effectiveness is invariant under equivalences** (Remark 10.1.12: `G_x ≅ G_y` mapping `T_x`
onto `T_y` along `ψ : F(x) → y`). -/
theorem EpFunctor.IsEquivalence.isEffective_iff {A B : EP.{u}} {F : EpFunctor A.X B.X}
    (hF : F.IsEquivalence) : A.X.IsEffective ↔ B.X.IsEffective := by
  rw [EP.isEffective_iff_trivialSet, EP.isEffective_iff_trivialSet]
  constructor
  · intro hA y g hg
    obtain ⟨q, hq⟩ := hF.isHomeomorph_orbitMap.surjective (B.X.π y)
    obtain ⟨a, rfl⟩ := A.X.surjective_π q
    rw [GroupoidFunctor.orbitMap_π] at hq
    obtain ⟨ψ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hq
    obtain ⟨e, -, he⟩ := hF.remark_10_1_12 ψ hs ht
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [hA a g' ((he g').1 hg), map_one]
  · intro hB a g hg
    apply (hF.bijective_isotropyHom a).1
    rw [map_one]
    exact hB _ _ ((F.isotropyHom_mem_trivialSet_iff hF.isLocalScDiffeo_obj g).2 hg)

/-- Effectiveness is invariant under generalized isomorphisms. -/
theorem EPLoc.isEffective_iff_of_isGeneralizedIso {X Y : EP.{u}} {f : of X ⟶ of Y}
    (hf : IsGeneralizedIso f) : X.X.IsEffective ↔ Y.X.IsEffective :=
  iff_of_isGeneralizedIso (fun A => A.X.IsEffective) (fun _ hF => hF.isEffective_iff) hf

namespace PolyfoldClass

variable {Z : Type u} [TopologicalSpace Z]

/-- A polyfold `(Z, c)` is **effective** if some structure `(X, α) ∈ c` has `X` effective. -/
def IsEffective (c : PolyfoldClass Z) : Prop :=
  ∃ p : PolyfoldStructure Z, ⟦p⟧ = c ∧ p.X.X.IsEffective

/-- One structure of `c` is effective iff every structure of `c` is. -/
theorem isEffective_iff (c : PolyfoldClass Z) :
    c.IsEffective ↔ ∀ p : PolyfoldStructure Z, ⟦p⟧ = c → p.X.X.IsEffective := by
  refine ⟨fun ⟨p, hp, hX⟩ q hq => ?_, fun h => ?_⟩
  · obtain ⟨f, hf, -⟩ := ScForm.exists_iso hp hq
    exact (EPLoc.isEffective_iff_of_isGeneralizedIso hf).1 hX
  · obtain ⟨p, rfl⟩ := Quotient.exists_rep c
    exact ⟨p, rfl, h p rfl⟩

end PolyfoldClass

/-! ### The category `PS` of polyfold structures (p. 709) -/

variable {Z W V U : Type u} [TopologicalSpace Z] [TopologicalSpace W] [TopologicalSpace V]
  [TopologicalSpace U]

/-- **A morphism `(f, 𝔣) : (X, α) → (Y, β)` of the category `PS`** (2021 p. 709): a map
`f : Z_α → Z_β` and a generalized map `𝔣 : X → Y` with `f ∘ α = β ∘ |𝔣|` (`f` is then
continuous, `PSHom.continuous_f`). -/
structure PSHom (p : PolyfoldStructure Z) (q : PolyfoldStructure W) : Type (u + 1) where
  /-- The map `f : Z → W`. -/
  f : Z → W
  /-- The generalized map `𝔣 : X → Y`. -/
  gen : EPLoc.of p.X ⟶ EPLoc.of q.X
  comm : f ∘ ⇑p.β = ⇑q.β ∘ orbitMap gen

namespace PSHom

variable {p p' p'' : PolyfoldStructure Z} {q q' q'' : PolyfoldStructure W}
  {r r' : PolyfoldStructure V} {s : PolyfoldStructure U}

/-- `f = β ∘ |𝔣| ∘ α⁻¹`. -/
theorem f_eq (a : PSHom p q) : a.f = ⇑q.β ∘ orbitMap a.gen ∘ ⇑p.β.symm := by
  rw [← Function.comp_assoc, ← a.comm, Function.comp_assoc, p.β.self_comp_symm,
    Function.comp_id]

/-- `f` is continuous. -/
theorem continuous_f (a : PSHom p q) : Continuous a.f := by
  rw [f_eq]
  exact q.β.continuous.comp ((continuous_orbitMap _).comp p.β.symm.continuous)

/-- A morphism of `PS` is determined by its generalized map. -/
@[ext] theorem ext {a b : PSHom p q} (h : a.gen = b.gen) : a = b := by
  have hf : a.f = b.f := by rw [f_eq, f_eq, h]
  cases a
  cases b
  cases hf
  cases h
  rfl

/-- `1_{(X,α)} = (Id, [1_X])`. -/
def id (p : PolyfoldStructure Z) : PSHom p p :=
  ⟨_root_.id, 𝟙 _, by rw [orbitMap_id]; rfl⟩

/-- The composition `(g, 𝔤) ∘ (f, 𝔣) = (g ∘ f, 𝔤 ∘ 𝔣)` (in diagrammatic order). -/
def comp (a : PSHom p q) (b : PSHom q r) : PSHom p r :=
  ⟨b.f ∘ a.f, a.gen ≫ b.gen, by
    rw [proposition_10_3_11, Function.comp_assoc, a.comm, ← Function.comp_assoc, b.comm]
    rfl⟩

@[simp] theorem id_gen (p : PolyfoldStructure Z) : (id p).gen = 𝟙 _ := rfl
@[simp] theorem comp_gen (a : PSHom p q) (b : PSHom q r) : (a.comp b).gen = a.gen ≫ b.gen := rfl
@[simp] theorem id_f (p : PolyfoldStructure Z) : (id p).f = _root_.id := rfl
@[simp] theorem comp_f (a : PSHom p q) (b : PSHom q r) : (a.comp b).f = b.f ∘ a.f := rfl

@[simp] theorem id_comp (a : PSHom p q) : (id p).comp a = a := ext (Category.id_comp _)
@[simp] theorem comp_id (a : PSHom p q) : a.comp (id q) = a := ext (Category.comp_id _)
theorem comp_assoc (a : PSHom p q) (b : PSHom q r) (c : PSHom r s) :
    (a.comp b).comp c = a.comp (b.comp c) := ext (Category.assoc _ _ _)

/-- `(h, Id_Z) : (X, α) → (X', α')` is an **isomorphism over the identity** of `PS`. -/
def IsIdIso (h : PSHom p p') : Prop := h.f = _root_.id ∧ IsGeneralizedIso h.gen

/-- For `h` over the identity, `α = α' ∘ |𝔥|`. -/
theorem IsIdIso.β_eq {h : PSHom p p'} (hh : h.IsIdIso) : ⇑p.β = ⇑p'.β ∘ orbitMap h.gen := by
  rw [← h.comm, hh.1]
  rfl

theorem isIdIso_id (p : PolyfoldStructure Z) : (id p).IsIdIso :=
  ⟨rfl, isGeneralizedIso_id _⟩

theorem IsIdIso.comp {h : PSHom p p'} {h' : PSHom p' p''} (hh : h.IsIdIso) (hh' : h'.IsIdIso) :
    (h.comp h').IsIdIso :=
  ⟨by rw [comp_f, hh.1, hh'.1]; rfl, isGeneralizedIso_comp hh.2 hh'.2⟩

/-- The isomorphism `(𝔥, Id)` of an equivalence of polyfold structures (Definition 16.1.2). -/
def ofGen (h : EPLoc.of p.X ⟶ EPLoc.of p'.X) (hβ : ⇑p.β = ⇑p'.β ∘ orbitMap h) : PSHom p p' :=
  ⟨_root_.id, h, hβ⟩

theorem exists_isIdIso (h : PolyfoldStructure.Equiv p p') : ∃ H : PSHom p p', H.IsIdIso := by
  obtain ⟨f, hf, hβ⟩ := h
  exact ⟨ofGen f hβ, rfl, hf⟩

/-- The inverse of an isomorphism over the identity. -/
def IsIdIso.inv {h : PSHom p p'} (hh : h.IsIdIso) : PSHom p' p :=
  ofGen hh.2.choose (by
    have e := hh.β_eq
    rw [e, Function.comp_assoc, ← proposition_10_3_11, hh.2.choose_spec.2, orbitMap_id]
    rfl)

theorem IsIdIso.inv_isIdIso {h : PSHom p p'} (hh : h.IsIdIso) : hh.inv.IsIdIso :=
  ⟨rfl, ⟨h.gen, hh.2.choose_spec.2, hh.2.choose_spec.1⟩⟩

@[simp] theorem IsIdIso.comp_inv {h : PSHom p p'} (hh : h.IsIdIso) : h.comp hh.inv = id p :=
  ext hh.2.choose_spec.1

@[simp] theorem IsIdIso.inv_comp {h : PSHom p p'} (hh : h.IsIdIso) : hh.inv.comp h = id p' :=
  ext hh.2.choose_spec.2

/-! ### Definition 16.1.6 -/

/-- **2021 Definition 16.1.6, p. 710 (2017: Definition 16.5)**: `(f, 𝔣) : (X, α) → (Y, β)` and
`(f', 𝔣') : (X', α') → (Y', β')` are **equivalent** if there are isomorphisms
`(h, Id_Z) : (X, α) → (X', α')` and `(k, Id_W) : (Y, β) → (Y', β')` of `PS` with
`(f', 𝔣') ∘ (h, Id_Z) = (k, Id_W) ∘ (f, 𝔣)`. -/
def Equiv (a : PSHom p q) (b : PSHom p' q') : Prop :=
  ∃ (h : PSHom p p') (k : PSHom q q'), h.IsIdIso ∧ k.IsIdIso ∧ h.comp b = a.comp k

/-- **"An equivalent pair necessarily satisfies `f = f'`"** (2021 p. 710). -/
theorem Equiv.f_eq {a : PSHom p q} {b : PSHom p' q'} (hab : a.Equiv b) : a.f = b.f := by
  obtain ⟨h, k, hh, hk, he⟩ := hab
  have := congrArg PSHom.f he
  rw [comp_f, comp_f, hh.1, hk.1] at this
  exact this.symm

theorem Equiv.refl (a : PSHom p q) : a.Equiv a :=
  ⟨id p, id q, isIdIso_id p, isIdIso_id q, by rw [id_comp, comp_id]⟩

theorem Equiv.symm {a : PSHom p q} {b : PSHom p' q'} (hab : a.Equiv b) : b.Equiv a := by
  obtain ⟨h, k, hh, hk, he⟩ := hab
  refine ⟨hh.inv, hk.inv, hh.inv_isIdIso, hk.inv_isIdIso, ?_⟩
  calc hh.inv.comp a = hh.inv.comp ((a.comp k).comp hk.inv) := by
        rw [comp_assoc, hk.comp_inv, comp_id]
    _ = hh.inv.comp ((h.comp b).comp hk.inv) := by rw [he]
    _ = b.comp hk.inv := by rw [← comp_assoc, ← comp_assoc, hh.inv_comp, id_comp]

theorem Equiv.trans {a : PSHom p q} {b : PSHom p' q'} {c : PSHom p'' q''} (hab : a.Equiv b)
    (hbc : b.Equiv c) : a.Equiv c := by
  obtain ⟨h, k, hh, hk, he⟩ := hab
  obtain ⟨h', k', hh', hk', he'⟩ := hbc
  refine ⟨h.comp h', k.comp k', hh.comp hh', hk.comp hk', ?_⟩
  rw [comp_assoc, he', ← comp_assoc, he, comp_assoc]

/-- `(f, 𝔣) ∼ (h, Id) ∘ ... `: precomposing with an isomorphism over the identity gives an
equivalent morphism. -/
theorem equiv_comp_left {h : PSHom p' p} (hh : h.IsIdIso) (a : PSHom p q) :
    (h.comp a).Equiv a :=
  ⟨h, id q, hh, isIdIso_id q, by rw [comp_id]⟩

/-- Postcomposing with an isomorphism over the identity gives an equivalent morphism. -/
theorem equiv_comp_right {k : PSHom q q'} (hk : k.IsIdIso) (a : PSHom p q) :
    a.Equiv (a.comp k) :=
  ⟨id p, k, isIdIso_id p, hk, by rw [id_comp]⟩

/-! ### Definition 16.1.10: independence of the choices -/

/-- **The claim of 2021 Definition 16.1.10, p. 711 (2017: Definition 16.7)** that the composition
does not depend on the choices, in universe `u`: if `(f, 𝔣) ∼ (f', 𝔣')` and `(g, 𝔤) ∼ (g', 𝔤')`
with composable representatives, then `(g ∘ f, 𝔤 ∘ 𝔣) ∼ (g' ∘ f', 𝔤' ∘ 𝔣')`.  It does not
hold as we read it: `not_definition_16_1_10` (`P3W3Y_CompositionCounterexample`). -/
def Definition_16_1_10 : Prop :=
  ∀ (Z W V : Type u) [TopologicalSpace Z] [TopologicalSpace W] [TopologicalSpace V]
    (p p' : PolyfoldStructure Z) (q q' : PolyfoldStructure W) (r r' : PolyfoldStructure V)
    (a : PSHom p q) (a' : PSHom p' q') (b : PSHom q r) (b' : PSHom q' r'),
    a.Equiv a' → b.Equiv b' → (a.comp b).Equiv (a'.comp b')

/-- **Definition 16.1.10 for an effective middle structure**: the composition of equivalent
representatives is equivalent when `Y'` is effective (then the isomorphism `(k, Id_W)` is unique,
`uniqueness_16_1_2_of_isEffective`). -/
theorem Equiv.comp_of_isEffective (hq' : q'.X.X.IsEffective) {a : PSHom p q} {a' : PSHom p' q'}
    {b : PSHom q r} {b' : PSHom q' r'} (ha : a.Equiv a') (hb : b.Equiv b') :
    (a.comp b).Equiv (a'.comp b') := by
  obtain ⟨h, k, hh, hk, he⟩ := ha
  obtain ⟨k', l, hk', hl, he'⟩ := hb
  have hkk : k = k' := ext (PolyfoldStructure.uniqueness_16_1_2_of_isEffective hq' hk.2 hk'.2
    hk.β_eq hk'.β_eq)
  subst hkk
  refine ⟨h, l, hh, hl, ?_⟩
  rw [← comp_assoc, he, comp_assoc, he', comp_assoc]

end PSHom

/-! ### The category `PS` -/

/-- **The category `PS` of polyfold structures** (2021 p. 709): objects `(X, α)` with
`α : |X| ≃ Z_α`, morphisms `PSHom`. -/
structure PSCat : Type (u + 1) where
  /-- The space `Z_α`. -/
  Z : Type u
  [top : TopologicalSpace Z]
  /-- The polyfold structure `(X, α)`. -/
  p : PolyfoldStructure Z

attribute [instance] PSCat.top

instance : Category.{u + 1} PSCat.{u} where
  Hom A B := PSHom A.p B.p
  id A := PSHom.id A.p
  comp a b := a.comp b
  id_comp := PSHom.id_comp
  comp_id := PSHom.comp_id
  assoc := PSHom.comp_assoc

/-! ### Definition 16.1.8: sc-smooth maps of polyfolds -/

namespace PolyfoldClass

/-- A representative `(f, 𝔣) : (X, α) → (Y, β)` of an sc-smooth map `(Z, c) → (W, d)`:
`(X, α) ∈ c`, `(Y, β) ∈ d`. -/
structure MapRep (c : PolyfoldClass Z) (d : PolyfoldClass W) : Type (u + 1) where
  /-- The structure `(X, α) ∈ c`. -/
  p : PolyfoldStructure Z
  hp : (⟦p⟧ : PolyfoldClass Z) = c
  /-- The structure `(Y, β) ∈ d`. -/
  q : PolyfoldStructure W
  hq : (⟦q⟧ : PolyfoldClass W) = d
  /-- The morphism of `PS`. -/
  φ : PSHom p q

/-- **Definition 16.1.6** on representatives: an equivalence relation. -/
instance MapRep.setoid (c : PolyfoldClass Z) (d : PolyfoldClass W) : Setoid (MapRep c d) where
  r a b := a.φ.Equiv b.φ
  iseqv := ⟨fun a => PSHom.Equiv.refl a.φ, PSHom.Equiv.symm, PSHom.Equiv.trans⟩

/-- **2021 Definition 16.1.8, p. 711 (2017: Definition 16.6)**: the **sc-smooth maps**
`(Z, c) → (W, d)`, the classes `[(f, 𝔣)]` of morphisms of `PS` between structures of `c` and
`d`. -/
def ScMap (c : PolyfoldClass Z) (d : PolyfoldClass W) : Type (u + 1) :=
  Quotient (MapRep.setoid c d)

variable {c : PolyfoldClass Z} {d : PolyfoldClass W} {e : PolyfoldClass V}

namespace ScMap

/-- The class `[(f, 𝔣)]`. -/
def mk (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c) (q : PolyfoldStructure W)
    (hq : (⟦q⟧ : PolyfoldClass W) = d) (φ : PSHom p q) : ScMap c d :=
  Quotient.mk _ ⟨p, hp, q, hq, φ⟩

/-- The isomorphism `(𝔥, Id) : (X, α) → (X', α')` for two structures of one class. -/
theorem exists_isIdIso {p p' : PolyfoldStructure Z} (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (hp' : (⟦p'⟧ : PolyfoldClass Z) = c) : ∃ H : PSHom p p', H.IsIdIso :=
  PSHom.exists_isIdIso (Quotient.exact (hp.trans hp'.symm))

/-- **Every sc-smooth map has a representative between any two given structures**
`(X', α') ∈ c`, `(Y', β') ∈ d` (2021 p. 710: `(k⁻¹ ∘ 𝔣 ∘ h, f)`). -/
theorem exists_rep (F : ScMap c d) (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (q : PolyfoldStructure W) (hq : (⟦q⟧ : PolyfoldClass W) = d) :
    ∃ φ : PSHom p q, F = mk p hp q hq φ := by
  induction F using Quotient.inductionOn with | h a => ?_
  obtain ⟨H, hH⟩ := exists_isIdIso hp a.hp
  obtain ⟨K, hK⟩ := exists_isIdIso a.hq hq
  refine ⟨H.comp (a.φ.comp K), Quotient.sound ?_⟩
  change a.φ.Equiv (H.comp (a.φ.comp K))
  refine ⟨hH.inv, K, hH.inv_isIdIso, hK, ?_⟩
  rw [← PSHom.comp_assoc, hH.inv_comp, PSHom.id_comp]

/-- **2021 Remark 16.1.9, p. 711 (2017: Remark 16.2)**: the continuous map `f : Z → W` of an
sc-smooth map, independent of the representative (`PSHom.Equiv.f_eq`). -/
def toFun (F : ScMap c d) : Z → W :=
  Quotient.lift (fun a : MapRep c d => a.φ.f) (fun _ _ h => PSHom.Equiv.f_eq h) F

@[simp] theorem toFun_mk (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (q : PolyfoldStructure W) (hq : (⟦q⟧ : PolyfoldClass W) = d) (φ : PSHom p q) :
    toFun (mk p hp q hq φ) = φ.f := rfl

/-- **Remark 16.1.9**: `f = β ∘ |𝔣| ∘ α⁻¹` for every representative, and `f` is continuous. -/
theorem remark_16_1_9 (F : ScMap c d) :
    Continuous F.toFun ∧ ∀ (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c)
      (q : PolyfoldStructure W) (hq : (⟦q⟧ : PolyfoldClass W) = d) (φ : PSHom p q),
      F = mk p hp q hq φ → F.toFun = ⇑q.β ∘ orbitMap φ.gen ∘ ⇑p.β.symm := by
  induction F using Quotient.inductionOn with | h a => ?_
  exact ⟨a.φ.continuous_f, fun p hp q hq φ h => by rw [h, toFun_mk, φ.f_eq]⟩

/-- The identity `1_{(Z,c)} = [([1_X], Id_Z)]` for `(X, α) = c.out` (Definition 16.1.11). -/
def id (c : PolyfoldClass Z) : ScMap c c :=
  mk c.out (Quotient.out_eq c) c.out (Quotient.out_eq c) (PSHom.id _)

/-- **`1_{(Z,c)} = [([1_X], Id_Z)]` for every `(X, α) ∈ c`** (Definition 16.1.11: the class does
not depend on `(X, α)`). -/
theorem id_eq (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c) :
    id c = mk p hp p hp (PSHom.id p) := by
  obtain ⟨H, hH⟩ := exists_isIdIso (Quotient.out_eq c) hp
  exact Quotient.sound ⟨H, H, hH, hH, by rw [PSHom.comp_id, PSHom.id_comp]⟩

end ScMap

/-! ### Definition 16.1.10 for an effective middle polyfold -/

/-- The chosen isomorphism `(𝔥, Id)` between two structures of one class. -/
def transport {p p' : PolyfoldStructure Z} (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (hp' : (⟦p'⟧ : PolyfoldClass Z) = c) : PSHom p p' :=
  (ScMap.exists_isIdIso hp hp').choose

theorem transport_isIdIso {p p' : PolyfoldStructure Z} (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (hp' : (⟦p'⟧ : PolyfoldClass Z) = c) : (transport hp hp').IsIdIso :=
  (ScMap.exists_isIdIso hp hp').choose_spec

/-- The composite representative `(g ∘ f, 𝔤 ∘ (k, Id) ∘ 𝔣)`, with the chosen isomorphism
`(k, Id) : (Y, β) → (Y', β')` between the middle structures. -/
def MapRep.comp (a : MapRep c d) (b : MapRep d e) : MapRep c e :=
  ⟨a.p, a.hp, b.q, b.hq, a.φ.comp ((transport a.hq b.hp).comp b.φ)⟩

theorem MapRep.comp_equiv (hd : d.IsEffective) {a a' : MapRep c d} {b b' : MapRep d e}
    (ha : a ≈ a') (hb : b ≈ b') : a.comp b ≈ a'.comp b' := by
  have h1 : ((transport a.hq b.hp).comp b.φ).Equiv ((transport a'.hq b'.hp).comp b'.φ) :=
    ((PSHom.equiv_comp_left (transport_isIdIso _ _) _).trans hb).trans
      (PSHom.equiv_comp_left (transport_isIdIso _ _) _).symm
  exact PSHom.Equiv.comp_of_isEffective ((PolyfoldClass.isEffective_iff d).1 hd _ a'.hq) ha h1

namespace ScMap

/-- **2021 Definition 16.1.10, p. 711, for an effective middle polyfold**: the composition
`ĝ ∘ f̂ = [(g ∘ f, 𝔤 ∘ 𝔣)]` (diagrammatic order `f̂.comp ĝ`), well defined
(`MapRep.comp_equiv`). -/
def comp (hd : d.IsEffective) (F : ScMap c d) (G : ScMap d e) : ScMap c e :=
  Quotient.map₂ MapRep.comp (fun _ _ ha _ _ hb => MapRep.comp_equiv hd ha hb) F G

/-- **The composition on representatives with a common middle structure** (the text's formula). -/
theorem comp_mk (hd : d.IsEffective) (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (q : PolyfoldStructure W) (hq : (⟦q⟧ : PolyfoldClass W) = d) (r : PolyfoldStructure V)
    (hr : (⟦r⟧ : PolyfoldClass V) = e) (a : PSHom p q) (b : PSHom q r) :
    comp hd (mk p hp q hq a) (mk q hq r hr b) = mk p hp r hr (a.comp b) := by
  refine Quotient.sound ?_
  change (a.comp ((transport hq hq).comp b)).Equiv (a.comp b)
  exact PSHom.Equiv.comp_of_isEffective ((PolyfoldClass.isEffective_iff d).1 hd _ hq)
    (PSHom.Equiv.refl a) (PSHom.equiv_comp_left (transport_isIdIso _ _) b)

theorem id_comp (hc : c.IsEffective) (F : ScMap c d) : comp hc (id c) F = F := by
  induction F using Quotient.inductionOn with | h a => ?_
  refine Quotient.sound ?_
  change ((PSHom.id _).comp ((transport _ a.hp).comp a.φ)).Equiv a.φ
  rw [PSHom.id_comp]
  exact PSHom.equiv_comp_left (transport_isIdIso _ _) a.φ

theorem comp_id (hd : d.IsEffective) (F : ScMap c d) : comp hd F (id d) = F := by
  induction F using Quotient.inductionOn with | h a => ?_
  refine Quotient.sound ?_
  change (a.φ.comp ((transport a.hq _).comp (PSHom.id _))).Equiv a.φ
  rw [PSHom.comp_id]
  exact (PSHom.equiv_comp_right (transport_isIdIso _ _) a.φ).symm

theorem comp_assoc {T : Type u} [TopologicalSpace T] {e' : PolyfoldClass T} (hd : d.IsEffective)
    (he : e.IsEffective) (F : ScMap c d) (G : ScMap d e) (H : ScMap e e') :
    comp he (comp hd F G) H = comp hd F (comp he G H) := by
  induction F using Quotient.inductionOn with | h a => ?_
  induction G using Quotient.inductionOn with | h b => ?_
  induction H using Quotient.inductionOn with | h c => ?_
  refine Quotient.sound ?_
  change ((a.φ.comp ((transport a.hq b.hp).comp b.φ)).comp ((transport b.hq c.hp).comp c.φ)).Equiv
    (a.φ.comp ((transport a.hq b.hp).comp (b.φ.comp ((transport b.hq c.hp).comp c.φ))))
  simp only [PSHom.comp_assoc]
  exact PSHom.Equiv.refl _

end ScMap

end PolyfoldClass

/-! ### Definition 16.1.11: the polyfold category on effective polyfolds -/

/-- An **effective polyfold** `(Z, c)` (an object of the polyfold category on which the
composition of Definition 16.1.10 is well defined). -/
structure EffPolyfold : Type (u + 1) where
  /-- The space `Z`. -/
  Z : Type u
  [top : TopologicalSpace Z]
  /-- The class `c`. -/
  c : PolyfoldClass Z
  isEffective : c.IsEffective

attribute [instance] EffPolyfold.top

/-- **2021 Definition 16.1.11, p. 711 (2017: Definition 16.8), for effective polyfolds**: the
polyfold category, objects the (effective) polyfolds, morphisms the sc-smooth maps
(Definition 16.1.8), composition Definition 16.1.10, identities `[([1_X], Id_Z)]`. -/
instance : Category.{u + 1} EffPolyfold.{u} where
  Hom A B := PolyfoldClass.ScMap A.c B.c
  id A := PolyfoldClass.ScMap.id A.c
  comp {_ B _} F G := PolyfoldClass.ScMap.comp B.isEffective F G
  id_comp {A _} F := PolyfoldClass.ScMap.id_comp A.isEffective F
  comp_id {_ B} F := PolyfoldClass.ScMap.comp_id B.isEffective F
  assoc {_ B C _} F G H := PolyfoldClass.ScMap.comp_assoc B.isEffective C.isEffective F G H

/-! ### Witness: the point polyfold -/

namespace PolyfoldStructure

open EpGroupoid.Examples

instance : Unique pointEP.X.OrbitSpace where
  default := pointEP.X.π ()
  uniq z := Quotient.inductionOn z fun _ => rfl

/-- The point polyfold structure on `Unit`: the point ep-groupoid, `β : |pt| ≃ₜ Unit`. -/
def pointStructure : PolyfoldStructure Unit where
  X := pointEP
  paracompact := (Homeomorph.homeomorphOfUnique pointEP.X.OrbitSpace Unit).paracompactSpace_iff.2
    inferInstance
  isZhou := EpGroupoid.isZhou_of_subsingleton _ fun _ =>
    ⟨fun a b => GroupoidStr.Isotropy.ext (Subsingleton.elim (α := Unit) a.val b.val)⟩
  β := Homeomorph.homeomorphOfUnique _ _

end PolyfoldStructure

/-- **Witness**: the point is an effective polyfold, an object of `EffPolyfold`. -/
def EffPolyfold.point : EffPolyfold.{0} :=
  ⟨Unit, ⟦PolyfoldStructure.pointStructure⟧,
    ⟨_, rfl, EquivalenceLREffectiveExamples.isEffective_pointEP⟩⟩

end Polyfold
