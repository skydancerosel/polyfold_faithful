import Polyfold.Chapter16.P3Z_PolyfoldStructure
import Polyfold.Chapter16.P3H_FormsIndependence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.2, pp. 720–721: **Definition 16.2.5** (2017: Definition 16.15) and the de Rham part of
**Theorem 16.2.6** (2017: Theorem 16.2).  Numbers and pages are the 2021 text's.

# Sc-differential forms on polyfolds

## The text, paraphrased

(Definition 16.2.5) An sc-differential form on the polyfold `(Z, c)` is a class `[(ω, (X, α))]`,
`(X, α) ∈ c`, `ω ∈ Ω*_{ep,∞}(X)`; `(ω, (X, α)) ∼ (τ, (Y, β))` if a generalized isomorphism
`h : X → Y` has `β ∘ |h| = α` and `τ = h_*ω`.  `Ω*_sc(Z, c)` is a vector space with
`[(ω, (X, α))] + λ[(τ, (X, α))] = [(ω + λτ, (X, α))]`, and `d[(ω, (X, α))] = [(dω, (X, α))]`.
(Theorem 16.2.6, first part) `(Ω*_sc(Z, c), d)` is a de Rham complex.

## What is formalized

Namespace `Polyfold.PolyfoldClass`, for each degree `k`:
* `FormRep c k` (pairs `(p, ω)`, `p ∈ c`), `FormRep.Rel` (the relation of Definition 16.2.5),
  `FormRep.setoid` (an equivalence relation), **`ScForm c k = Ωᵏ_sc(Z, c)`** (the quotient),
  `ScForm.mk p hp ω = [(ω, p)]`.
* `ScForm.toStructure q hq : Ωᵏ_sc(Z, c) → Ωᵏ_{ep,∞}(q.X)` (the representative on `q`) with
  `toStructure_mk`, `mk_toStructure`, `mk_injective`: **for every `p ∈ c`, `ω ↦ [(ω, p)]` is a
  bijection `Ωᵏ_{ep,∞}(X) → Ωᵏ_sc(Z, c)`**.  This uses that `h_*` depends only on `|h|`
  (Proposition 11.2.9, `EPLoc.formsPush_eq_of_orbitMap_eq_or`, (ZHOU) ⇒ (LR)), the remark on p. 720.
* The vector space structure (transported from `c.out`), with **`mk_add`, `mk_smul`**, the text's
  formula for every representative `p`; `ScForm.toStructureₗ`, `ScForm.equivStructureₗ`
  (linear isomorphisms `Ωᵏ_sc(Z, c) ≃ Ωᵏ_{ep,∞}(X)`).
* **`ScForm.d`** (`d_mk`: `d[(ω, p)] = [(dω, p)]`, linear), **`d_comp_d`**: `d ∘ d = 0`;
  `theorem_16_2_6_complex`.  The pull-back by sc-smooth maps of polyfolds (the second part of
  Theorem 16.2.6) needs the morphisms of Definitions 16.1.8–16.1.11 and is not formalized here.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization EPLocalization.EPLoc

namespace EPLocalization.EPLoc

variable {X Y Z : EP.{u}}

/-- `1_* = 1`. -/
theorem formsPush_id (h : IsGeneralizedIso (𝟙 (of X))) (k : ℕ) :
    formsPush (𝟙 (of X)) h k = LinearMap.id := by
  have := (theorem_11_2_1_three _ h k).2.2
  rwa [formsPullback_id, LinearMap.id_comp] at this

/-- `f_* = g^*` for a two-sided inverse `g` of `f`. -/
theorem formsPush_eq_formsPullback {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {g : of Y ⟶ of X}
    (hfg : f ≫ g = 𝟙 _) (_hgf : g ≫ f = 𝟙 _) (k : ℕ) : formsPush f hf k = formsPullback g k := by
  have e : hf.choose = g := by
    calc hf.choose = hf.choose ≫ f ≫ g := by rw [hfg, Category.comp_id]
      _ = g := by rw [← Category.assoc, hf.choose_spec.2, Category.id_comp]
  rw [formsPush, e]

/-- `(f ≫ f')_* = f'_* ∘ f_*`. -/
theorem formsPush_comp {f : of X ⟶ of Y} {f' : of Y ⟶ of Z} (hf : IsGeneralizedIso f)
    (hf' : IsGeneralizedIso f') (hff' : IsGeneralizedIso (f ≫ f')) (k : ℕ) :
    formsPush (f ≫ f') hff' k = (formsPush f' hf' k).comp (formsPush f hf k) := by
  obtain ⟨g, hfg, hgf⟩ := id hf
  obtain ⟨g', hfg', hgf'⟩ := id hf'
  rw [formsPush_eq_formsPullback _ hfg hgf, formsPush_eq_formsPullback _ hfg' hgf',
    formsPush_eq_formsPullback (g := g' ≫ g) hff'
      (by rw [Category.assoc, ← Category.assoc f', hfg', Category.id_comp, hfg])
      (by rw [Category.assoc, ← Category.assoc g, hgf, Category.id_comp, hgf']),
    formsPullback_comp]

theorem isGeneralizedIso_comp {f : of X ⟶ of Y} {f' : of Y ⟶ of Z} (hf : IsGeneralizedIso f)
    (hf' : IsGeneralizedIso f') : IsGeneralizedIso (f ≫ f') := by
  rw [isGeneralizedIso_iff_isIso] at hf hf' ⊢
  infer_instance

theorem isGeneralizedIso_id (X : EP.{u}) : IsGeneralizedIso (𝟙 (of X)) :=
  ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩

end EPLocalization.EPLoc

namespace PolyfoldClass

variable {Z : Type u} [TopologicalSpace Z]

/-- A representative `(ω, (X, α))` of an sc-differential `k`-form on `(Z, c)`
(Definition 16.2.5): `(X, α) ∈ c` and `ω ∈ Ωᵏ_{ep,∞}(X)`. -/
structure FormRep (c : PolyfoldClass Z) (k : ℕ) : Type (u + 1) where
  /-- The polyfold structure `(X, α)`. -/
  p : PolyfoldStructure Z
  mem : (⟦p⟧ : PolyfoldClass Z) = c
  /-- The form `ω ∈ Ωᵏ_{ep,∞}(X)`. -/
  ω : p.X.epFormsInfty k

variable {c : PolyfoldClass Z} {k : ℕ}

namespace FormRep

/-- **The relation of Definition 16.2.5**: `(ω, (X, α)) ∼ (τ, (Y, β))` if a generalized
isomorphism `h : X → Y` has `β ∘ |h| = α` and `τ = h_*ω`. -/
def Rel (a b : FormRep c k) : Prop :=
  ∃ (h : EPLoc.of a.p.X ⟶ EPLoc.of b.p.X) (hh : IsGeneralizedIso h),
    ⇑a.p.β = ⇑b.p.β ∘ orbitMap h ∧ b.ω = formsPush h hh k a.ω

theorem Rel.refl (a : FormRep c k) : Rel a a :=
  ⟨𝟙 _, isGeneralizedIso_id _, by rw [orbitMap_id]; rfl, by rw [formsPush_id]; rfl⟩

theorem Rel.symm {a b : FormRep c k} (h : Rel a b) : Rel b a := by
  obtain ⟨h, hh, hβ, hω⟩ := h
  obtain ⟨g, hhg, hgh⟩ := id hh
  refine ⟨g, ⟨h, hgh, hhg⟩, ?_, ?_⟩
  · rw [hβ, Function.comp_assoc, ← proposition_10_3_11, hgh, orbitMap_id]
    rfl
  · rw [hω, formsPush_eq_formsPullback ⟨h, hgh, hhg⟩ hgh hhg]
    exact (LinearMap.congr_fun (theorem_11_2_1_three h hh k).2.2 a.ω).symm

theorem Rel.trans {a b e : FormRep c k} (h₁ : Rel a b) (h₂ : Rel b e) : Rel a e := by
  obtain ⟨h, hh, hβ, hω⟩ := h₁
  obtain ⟨h', hh', hβ', hω'⟩ := h₂
  refine ⟨h ≫ h', isGeneralizedIso_comp hh hh', ?_, ?_⟩
  · rw [hβ, hβ', proposition_10_3_11]
    rfl
  · rw [hω', hω, formsPush_comp hh hh' (isGeneralizedIso_comp hh hh')]
    rfl

/-- **Definition 16.2.5**: the relation is an equivalence relation. -/
instance setoid (c : PolyfoldClass Z) (k : ℕ) : Setoid (FormRep c k) where
  r := Rel
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

end FormRep

/-- **2021 Definition 16.2.5, p. 720 (2017: Definition 16.15)**: the sc-differential `k`-forms
`Ωᵏ_sc(Z, c)` on the polyfold `(Z, c)`, the classes `[(ω, (X, α))]`. -/
def ScForm (c : PolyfoldClass Z) (k : ℕ) : Type (u + 1) := Quotient (FormRep.setoid c k)

namespace ScForm

/-- The class `[(ω, p)]`. -/
def mk (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c) (ω : p.X.epFormsInfty k) :
    ScForm c k :=
  Quotient.mk _ ⟨p, hp, ω⟩

/-- Two structures of the same class are related by a generalized isomorphism `h` with
`α = β ∘ |h|` (Definition 16.1.2). -/
theorem exists_iso {p q : PolyfoldStructure Z} (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    ∃ h : EPLoc.of p.X ⟶ EPLoc.of q.X, IsGeneralizedIso h ∧ ⇑p.β = ⇑q.β ∘ orbitMap h :=
  Quotient.exact (hp.trans hq.symm)

/-- **The push-forward along `h : X → Y` with `α = β ∘ |h|` does not depend on `h`**
(2021 p. 720; (ZHOU) gives (LR), `EPLoc.formsPush_eq_of_orbitMap_eq_or`). -/
theorem formsPush_eq {p q : PolyfoldStructure Z} {h h' : EPLoc.of p.X ⟶ EPLoc.of q.X}
    (hh : IsGeneralizedIso h) (hh' : IsGeneralizedIso h') (hβ : ⇑p.β = ⇑q.β ∘ orbitMap h)
    (hβ' : ⇑p.β = ⇑q.β ∘ orbitMap h') : formsPush h hh k = formsPush h' hh' k :=
  formsPush_eq_of_orbitMap_eq_or (Or.inl p.isLR) hh hh'
    ((PolyfoldStructure.orbitMap_eq_of_equiv hβ).trans
      (PolyfoldStructure.orbitMap_eq_of_equiv hβ').symm) k

/-- The representative on a given structure: `b ↦ h_* b.ω` for any `h : b.p → q`. -/
def repOn (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) (b : FormRep c k) :
    q.X.epFormsInfty k :=
  formsPush (exists_iso b.mem hq).choose (exists_iso b.mem hq).choose_spec.1 k b.ω

theorem repOn_eq (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) (b : FormRep c k)
    {h : EPLoc.of b.p.X ⟶ EPLoc.of q.X} (hh : IsGeneralizedIso h)
    (hβ : ⇑b.p.β = ⇑q.β ∘ orbitMap h) : repOn q hq b = formsPush h hh k b.ω := by
  rw [repOn, formsPush_eq _ hh (exists_iso b.mem hq).choose_spec.2 hβ]

theorem repOn_rel (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c)
    {a b : FormRep c k} (hab : FormRep.Rel a b) : repOn q hq a = repOn q hq b := by
  obtain ⟨h, hh, hβ, hω⟩ := hab
  obtain ⟨h', hh', hβ'⟩ := exists_iso b.mem hq
  rw [repOn_eq q hq b hh' hβ', hω, repOn_eq q hq a (isGeneralizedIso_comp hh hh')
    (by rw [hβ, hβ', proposition_10_3_11]; rfl),
    formsPush_comp hh hh' (isGeneralizedIso_comp hh hh')]
  rfl

/-- The representative `Ωᵏ_sc(Z, c) → Ωᵏ_{ep,∞}(q.X)` on a structure `q ∈ c`. -/
def toStructure (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    ScForm c k → q.X.epFormsInfty k :=
  Quotient.lift (repOn q hq) fun _ _ h => repOn_rel q hq h

theorem toStructure_mk_of {p q : PolyfoldStructure Z} (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (hq : (⟦q⟧ : PolyfoldClass Z) = c) (ω : p.X.epFormsInfty k)
    {h : EPLoc.of p.X ⟶ EPLoc.of q.X} (hh : IsGeneralizedIso h) (hβ : ⇑p.β = ⇑q.β ∘ orbitMap h) :
    toStructure q hq (mk p hp ω) = formsPush h hh k ω :=
  repOn_eq q hq ⟨p, hp, ω⟩ hh hβ

/-- `[(ω, q)]` read on `q` is `ω`. -/
@[simp] theorem toStructure_mk (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c)
    (ω : q.X.epFormsInfty k) : toStructure q hq (mk q hq ω) = ω := by
  rw [toStructure_mk_of hq hq ω (isGeneralizedIso_id _) (by rw [orbitMap_id]; rfl),
    formsPush_id]
  rfl

/-- Every form is `[(ω, q)]` with `ω` its representative on `q`. -/
@[simp] theorem mk_toStructure (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c)
    (a : ScForm c k) : mk q hq (toStructure q hq a) = a := by
  induction a using Quotient.inductionOn with | h b => ?_
  obtain ⟨h, hh, hβ⟩ := exists_iso b.mem hq
  exact (Quotient.sound (show FormRep.Rel b ⟨q, hq, repOn q hq b⟩ from
    ⟨h, hh, hβ, repOn_eq q hq b hh hβ⟩)).symm

/-- **For every `(X, α) ∈ c`, `ω ↦ [(ω, (X, α))]` is a bijection `Ωᵏ_{ep,∞}(X) ≃ Ωᵏ_sc(Z, c)`.** -/
def equivStructure (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    ScForm c k ≃ q.X.epFormsInfty k where
  toFun := toStructure q hq
  invFun := mk q hq
  left_inv := mk_toStructure q hq
  right_inv := toStructure_mk q hq

theorem mk_injective (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    Function.Injective (mk (k := k) q hq) :=
  (equivStructure q hq).symm.injective

/-- `[(ω, p)] = [(h_*ω, q)]` for `h` with `α = β ∘ |h|`. -/
theorem mk_eq_mk_formsPush {p q : PolyfoldStructure Z} (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (hq : (⟦q⟧ : PolyfoldClass Z) = c) (ω : p.X.epFormsInfty k)
    {h : EPLoc.of p.X ⟶ EPLoc.of q.X} (hh : IsGeneralizedIso h) (hβ : ⇑p.β = ⇑q.β ∘ orbitMap h) :
    mk p hp ω = mk q hq (formsPush h hh k ω) :=
  Quotient.sound (show FormRep.Rel ⟨p, hp, ω⟩ ⟨q, hq, formsPush h hh k ω⟩ from ⟨h, hh, hβ, rfl⟩)

/-! ### The vector space structure -/

instance : AddCommGroup (ScForm c k) := (equivStructure c.out (Quotient.out_eq c)).addCommGroup

instance : Module ℝ (ScForm c k) := (equivStructure c.out (Quotient.out_eq c)).module ℝ

/-- The representative on `c.out` as a linear equivalence. -/
def outₗ : ScForm c k ≃ₗ[ℝ] c.out.X.epFormsInfty k :=
  (equivStructure c.out (Quotient.out_eq c)).linearEquiv ℝ

/-- Reading on `q` is `h_*` of reading on `c.out`. -/
theorem toStructure_eq_formsPush_out (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c)
    {h : EPLoc.of c.out.X ⟶ EPLoc.of q.X} (hh : IsGeneralizedIso h)
    (hβ : ⇑c.out.β = ⇑q.β ∘ orbitMap h) (a : ScForm c k) :
    toStructure q hq a = formsPush h hh k (outₗ a) := by
  conv_lhs => rw [← mk_toStructure c.out (Quotient.out_eq c) a]
  exact toStructure_mk_of _ hq _ hh hβ

/-- The representative on any `q ∈ c` is linear. -/
def toStructureₗ (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    ScForm c k →ₗ[ℝ] q.X.epFormsInfty k := by
  refine
    { toFun := toStructure q hq
      map_add' := fun a b => ?_
      map_smul' := fun r a => ?_ } <;>
  · obtain ⟨h, hh, hβ⟩ := exists_iso (Quotient.out_eq c) hq
    simp only [toStructure_eq_formsPush_out q hq hh hβ, map_add, map_smul, RingHom.id_apply]

/-- **For every `(X, α) ∈ c`, `Ωᵏ_sc(Z, c) ≃ Ωᵏ_{ep,∞}(X)` linearly** (the representative on
`(X, α)`). -/
def equivStructureₗ (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    ScForm c k ≃ₗ[ℝ] q.X.epFormsInfty k :=
  { toStructureₗ q hq with
    invFun := mk q hq
    left_inv := mk_toStructure q hq
    right_inv := toStructure_mk q hq }

/-- **The text's vector space operations** (2021 p. 720), for every representative `(X, α)`:
`[(ω, (X, α))] + [(τ, (X, α))] = [(ω + τ, (X, α))]`. -/
theorem mk_add (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c)
    (ω τ : q.X.epFormsInfty k) : mk q hq (ω + τ) = mk q hq ω + mk q hq τ :=
  map_add (equivStructureₗ q hq).symm ω τ

/-- `λ[(ω, (X, α))] = [(λω, (X, α))]` (2021 p. 720). -/
theorem mk_smul (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) (r : ℝ)
    (ω : q.X.epFormsInfty k) : mk q hq (r • ω) = r • mk q hq ω :=
  map_smul (equivStructureₗ q hq).symm r ω

/-- The formula of 2021 p. 720: `[(ω, (X, α))] + λ[(τ, (X, α))] = [(ω + λτ, (X, α))]`. -/
theorem mk_add_smul (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) (r : ℝ)
    (ω τ : q.X.epFormsInfty k) : mk q hq ω + r • mk q hq τ = mk q hq (ω + r • τ) := by
  rw [mk_add, mk_smul]

/-! ### The exterior derivative -/

theorem formsPush_d {X Y : EP.{u}} {h : EPLoc.of X ⟶ EPLoc.of Y} (hh : IsGeneralizedIso h)
    (ω : X.epFormsInfty k) :
    formsPush h hh (k + 1) (X.epFormsInftyD k ω) = Y.epFormsInftyD k (formsPush h hh k ω) :=
  LinearMap.congr_fun (theorem_11_2_1_three h hh k).1 ω

/-- `d` on representatives. -/
def dRep (b : FormRep c k) : FormRep c (k + 1) := ⟨b.p, b.mem, b.p.X.epFormsInftyD k b.ω⟩

theorem dRep_rel {a b : FormRep c k} (hab : FormRep.Rel a b) : FormRep.Rel (dRep a) (dRep b) := by
  obtain ⟨h, hh, hβ, hω⟩ := hab
  refine ⟨h, hh, hβ, ?_⟩
  change b.p.X.epFormsInftyD k b.ω = formsPush h hh (k + 1) (a.p.X.epFormsInftyD k a.ω)
  rw [formsPush_d, ← hω]

/-- **The exterior differential `d = d_Z` on `Ω*_sc(Z, c)`** (2021 p. 720):
`d[(ω, (X, α))] = [(dω, (X, α))]`. -/
def dFun : ScForm c k → ScForm c (k + 1) :=
  Quotient.map dRep fun _ _ h => dRep_rel h

@[simp] theorem dFun_mk (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c)
    (ω : q.X.epFormsInfty k) : dFun (mk q hq ω) = mk q hq (q.X.epFormsInftyD k ω) := rfl

theorem toStructure_dFun (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c)
    (a : ScForm c k) : toStructure q hq (dFun a) = q.X.epFormsInftyD k (toStructure q hq a) := by
  conv_lhs => rw [← mk_toStructure q hq a, dFun_mk, toStructure_mk]

/-- **`d : Ωᵏ_sc(Z, c) → Ωᵏ⁺¹_sc(Z, c)` is linear.** -/
def d : ScForm c k →ₗ[ℝ] ScForm c (k + 1) :=
  (equivStructureₗ c.out (Quotient.out_eq c)).symm.toLinearMap.comp
    ((c.out.X.epFormsInftyD k).comp (equivStructureₗ c.out (Quotient.out_eq c)).toLinearMap)

theorem d_apply (a : ScForm c k) : d a = dFun a := by
  change mk c.out _ (c.out.X.epFormsInftyD k (toStructure c.out _ a)) = dFun a
  rw [← toStructure_dFun, mk_toStructure]

/-- `d[(ω, (X, α))] = [(dω, (X, α))]` for every representative. -/
theorem d_mk (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c)
    (ω : q.X.epFormsInfty k) : d (mk q hq ω) = mk q hq (q.X.epFormsInftyD k ω) := by
  rw [d_apply, dFun_mk]

/-- **`d ∘ d = 0` on `Ω*_sc(Z, c)`.** -/
theorem d_d (a : ScForm c k) : d (d a) = 0 := by
  rw [← mk_toStructure c.out (Quotient.out_eq c) a, d_mk, d_mk,
    EP.epFormsInftyD_epFormsInftyD, ← (equivStructureₗ c.out (Quotient.out_eq c)).symm.map_zero]
  rfl

theorem d_comp_d : (d (c := c) (k := k + 1)).comp d = 0 :=
  LinearMap.ext fun a => d_d a

end ScForm

/-- **2021 Theorem 16.2.6, p. 721 (2017: Theorem 16.2), the de Rham complex**: for a polyfold
`(Z, c)` the forms `Ωᵏ_sc(Z, c)` (Definition 16.2.5) are real vector spaces with linear
`d : Ωᵏ_sc → Ωᵏ⁺¹_sc`, `d[(ω, (X, α))] = [(dω, (X, α))]` for every `(X, α) ∈ c`, and
`d ∘ d = 0`; for every `(X, α) ∈ c`, `ω ↦ [(ω, (X, α))]` is a linear isomorphism
`Ωᵏ_{ep,∞}(X) ≃ Ωᵏ_sc(Z, c)` commuting with `d`. -/
theorem theorem_16_2_6_complex (c : PolyfoldClass Z) (k : ℕ) :
    (∀ (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) (ω : q.X.epFormsInfty k),
      ScForm.d (ScForm.mk q hq ω) = ScForm.mk q hq (q.X.epFormsInftyD k ω)) ∧
    (ScForm.d (c := c) (k := k + 1)).comp ScForm.d = 0 ∧
    (∀ (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c),
      ⇑(ScForm.equivStructureₗ (k := k) q hq).symm = ScForm.mk q hq) :=
  ⟨ScForm.d_mk, ScForm.d_comp_d, fun _ _ => rfl⟩

end PolyfoldClass

end Polyfold
