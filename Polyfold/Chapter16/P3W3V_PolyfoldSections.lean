import Polyfold.Chapter16.P3W3V_StrongPolyfoldBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.3 (pp. 728–729; 2017: §16.3): **Definitions 16.3.18 and 16.3.19**, with the equivalence
relation before them.  Numbers and pages are the 2021 text's.

# sc-smooth and sc⁺-sections of strong polyfold bundles

## The text, paraphrased

(p. 728) In a structure `((P : W → X, μ), Γ, γ)` an sc-smooth section is a pair `(f, F)`: a
continuous section `f : Z → Y` of `p` and an sc-smooth section functor `F` of `P` with
`Γ ∘ |F| = f ∘ γ`; one writes `(f, Γ, W, F)`.  `(f, Γ, W, F) ∼ (f', Γ', W', F')` if `f = f'` and a
generalized strong bundle isomorphism `𝔄 : W → W'` has `Γ' ∘ |𝔄| = Γ` and `𝔄_* F = F'`; "this
defines an equivalence relation".  (Definition 16.3.18) An sc-smooth section of `p` is a class
`[(f, Γ, W, F)]`.  (Definition 16.3.19) An sc⁺-smooth section: the same with `F` an sc⁺-section
functor.

## What is formalized

* `Γ_base` (`γ' ∘ |𝔞| = γ` follows from `Γ' ∘ |𝔄| = Γ`) and `equiv_iff_exists_Γ`: Definition
  16.3.3 needs only the condition on `Γ`.
* `SectionRep c` (the tuples `(f, Γ, W, F)` with `(W, Γ) ∈ c̄`), `SectionRep.Rel` (the relation as
  printed), **`pushforward_eq_of_Γ`**: for representatives with the same `f` and any `𝔄` with
  `Γ' ∘ |𝔄| = Γ`, `𝔄_* F = F'` holds automatically (a section functor is determined by the orbits
  of its values, `eq_of_forall_π_eq`, and `|𝔄_* F|` is computed by `π_pushforward`);
  `rel_iff` (`∼` is "same `f` and equivalent structures"), hence `Rel.refl/symm/trans` (the text's
  claim that `∼` is an equivalence relation).
* `ScSection c` (**Definition 16.3.18**), `ScSection.toFun` (the section `f`, well defined),
  `ScSection.p_toFun`.
* `ScSection.IsScPlus`, `isScPlus_iff` (one representative sc⁺ iff all, Theorem 10.5.4),
  `ScPlusSection c` (**Definition 16.3.19**).

## Readings

* "Continuous section `f`" is kept as data with `p ∘ f = id`; for Definition 16.3.19 the
  continuity of `f` into `Y_{0,1}` (with the topology of `|W[1]|`) is not recorded separately: it
  is that of `F` into `W_{0,1}`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization SBLocalization

namespace StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}

/-- **`γ' ∘ |𝔞| = γ` follows from `Γ' ∘ |𝔄| = Γ`** (`|P'| ∘ |𝔄| = |𝔞| ∘ |P|`, `|P|` surjective). -/
theorem Γ_base {S S' : StrongPolyfoldBundleStructure p} {F : GenSBMap S.A S'.A}
    (hΓ : ⇑S'.Γ ∘ F.orbitMap = ⇑S.Γ) : ⇑S'.γ ∘ EPLoc.orbitMap F.base = ⇑S.γ := by
  funext ξ
  obtain ⟨q, rfl⟩ := S.A.E.surjective_orbitMap_projFunctor ξ
  have h := congrFun (GenSBMap.orbitMap_square F) q
  simp only [Function.comp_apply] at h ⊢
  rw [← h, ← S'.p_Γ, ← S.p_Γ]
  exact congrArg p (congrFun hΓ q)

/-- Definition 16.3.3 needs only `Γ' ∘ |F| = Γ`. -/
theorem equiv_iff_exists_Γ {S S' : StrongPolyfoldBundleStructure p} :
    Equiv S S' ↔ ∃ F : GenSBMap S.A S'.A, F.IsGeneralizedIso ∧ ⇑S'.Γ ∘ F.orbitMap = ⇑S.Γ :=
  ⟨fun ⟨F, hF, _, hΓ⟩ => ⟨F, hF, hΓ⟩, fun ⟨F, hF, hΓ⟩ => ⟨F, hF, Γ_base hΓ, hΓ⟩⟩

end StrongPolyfoldBundleStructure

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}

/-- **A representative `(f, Γ, W, F)` of an sc-smooth section** (2021 p. 728): a structure
`((P : W → X, μ), Γ, γ) ∈ c̄`, an sc-smooth section functor `F` of `P` (Definition 8.3.4), and a
continuous section `f` of `p` with `f ∘ γ = Γ ∘ |F|`. -/
structure SectionRep (c : StrongPolyfoldBundle p) : Type (u + 1) where
  /-- The structure `((P : W → X, μ), Γ, γ)`. -/
  S : StrongPolyfoldBundleStructure p
  hS : ⟦S⟧ = c
  /-- The sc-smooth section functor `F` of `P`. -/
  F : S.A.Obj → S.A.W
  hF : F ∈ S.A.E.sectionFunctors
  /-- The section `f : Z → Y`. -/
  f : Z → Y
  continuous_f : Continuous f
  isSection : ∀ z, p (f z) = z
  /-- `f ∘ γ = Γ ∘ |F|`. -/
  comm : ∀ x : S.A.Obj, f (S.γ (S.A.X.π x)) = S.Γ (S.A.E.toEpGroupoid.π (F x))

variable {c : StrongPolyfoldBundle p}

namespace SectionRep

/-- **The relation before Definition 16.3.18** (2021 pp. 728–729): `f = f'` and a generalized
strong bundle isomorphism `𝔄 : W → W'` has `Γ' ∘ |𝔄| = Γ` and `𝔄_* F = F'`. -/
def Rel (a b : SectionRep c) : Prop :=
  a.f = b.f ∧ ∃ (𝔄 : GenSBMap a.S.A b.S.A) (h𝔄 : 𝔄.IsGeneralizedIso),
    ⇑b.S.Γ ∘ 𝔄.orbitMap = ⇑a.S.Γ ∧ GenSBMap.pushforward h𝔄 a.F = b.F

/-- **`𝔄_* F = F'` is automatic**: for representatives with the same `f`, every generalized strong
bundle isomorphism `𝔄` with `Γ' ∘ |𝔄| = Γ` pushes `F` to `F'`. -/
theorem pushforward_eq_of_Γ (a b : SectionRep c) (hf : a.f = b.f) {𝔄 : GenSBMap a.S.A b.S.A}
    (h𝔄 : 𝔄.IsGeneralizedIso) (hΓ : ⇑b.S.Γ ∘ 𝔄.orbitMap = ⇑a.S.Γ) :
    GenSBMap.pushforward h𝔄 a.F = b.F := by
  set D := GenSBMap.rep h𝔄
  have hΨ := GenSBMap.isEquivalence_rep_Ψ h𝔄
  have hD : D.cls = 𝔄 := GenSBMap.cls_rep h𝔄
  obtain ⟨hpush, hpfun⟩ := (GenSBMap.theorem_10_5_4 h𝔄).2.1.1 a.hF
  obtain ⟨hbs, hbfun⟩ := b.hF
  refine EpStrongBundle.eq_of_forall_π_eq hpfun hbs.1 fun x' => ?_
  obtain ⟨ξ, hξ⟩ := (D.base.isHomeomorph_orbitMap (sbe hΨ).isEquivalence_base).surjective
    (b.S.A.X.π x')
  induction ξ using Quotient.inductionOn with | h x => ?_
  have hx : D.base.orbitMap (a.S.A.X.π x) = b.S.A.X.π x' := hξ
  have h1 := D.π_pushforward hΨ a.hF hx
  change b.S.A.E.toEpGroupoid.π (D.pushforward hΨ a.F x') = _ at h1
  apply b.S.Γ.injective
  change b.S.Γ (b.S.A.E.toEpGroupoid.π (D.pushforward hΨ a.F x')) = _
  rw [h1, ← b.comm x']
  have hγ := congrFun (Γ_base hΓ) (a.S.A.X.π x)
  have hbase : EPLoc.orbitMap 𝔄.base (a.S.A.X.π x) = b.S.A.X.π x' := by
    rw [← hD]; exact hx
  simp only [Function.comp_apply, hbase] at hγ
  rw [hγ, ← hf, a.comm x]
  have hΓx := congrFun hΓ (a.S.A.E.toEpGroupoid.π (a.F x))
  simp only [Function.comp_apply] at hΓx
  rw [← hΓx, ← hD]
  rfl

/-- **`∼` is "same `f` and equivalent structures"** (Definition 16.3.3). -/
theorem rel_iff (a b : SectionRep c) : Rel a b ↔ a.f = b.f ∧ Equiv a.S b.S := by
  refine ⟨fun ⟨hf, 𝔄, h𝔄, hΓ, _⟩ => ⟨hf, equiv_iff_exists_Γ.2 ⟨𝔄, h𝔄, hΓ⟩⟩,
    fun ⟨hf, h⟩ => ?_⟩
  obtain ⟨𝔄, h𝔄, hΓ⟩ := equiv_iff_exists_Γ.1 h
  exact ⟨hf, 𝔄, h𝔄, hΓ, pushforward_eq_of_Γ a b hf h𝔄 hΓ⟩

/-- Any two representatives on the same `f` are related (both structures lie in `c̄`). -/
theorem rel_of_f_eq (a b : SectionRep c) (hf : a.f = b.f) : Rel a b :=
  (rel_iff a b).2 ⟨hf, Quotient.exact (a.hS.trans b.hS.symm)⟩

theorem Rel.refl (a : SectionRep c) : Rel a a := rel_of_f_eq a a rfl

theorem Rel.symm {a b : SectionRep c} (h : Rel a b) : Rel b a := rel_of_f_eq b a h.1.symm

theorem Rel.trans {a b d : SectionRep c} (h : Rel a b) (h' : Rel b d) : Rel a d :=
  rel_of_f_eq a d (h.1.trans h'.1)

/-- **The text's claim (p. 729): `∼` is an equivalence relation.** -/
instance setoid (c : StrongPolyfoldBundle p) : Setoid (SectionRep c) where
  r := Rel
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

end SectionRep

/-- **2021 Definition 16.3.18, p. 729 (2017: Definition 16.27)**: an **sc-smooth section** of the
strong polyfold bundle `(p, c̄)`: a class `[(f, Γ, W, F)]`. -/
abbrev ScSection (c : StrongPolyfoldBundle p) : Type (u + 1) := Quotient (SectionRep.setoid c)

namespace ScSection

/-- The section `f : Z → Y` of an sc-smooth section (well defined). -/
def toFun (s : ScSection c) : Z → Y :=
  Quotient.lift SectionRep.f (fun a b h => (h : SectionRep.Rel a b).1) s

theorem p_toFun (s : ScSection c) (z : Z) : p (s.toFun z) = z :=
  Quotient.inductionOn (motive := fun s : ScSection c => p (s.toFun z) = z) s
    fun a => a.isSection z

theorem continuous_toFun (s : ScSection c) : Continuous s.toFun :=
  Quotient.inductionOn (motive := fun s : ScSection c => Continuous s.toFun) s
    fun a => a.continuous_f

/-- Two sc-smooth sections with the same `f` are equal. -/
theorem ext_toFun {s t : ScSection c} (h : s.toFun = t.toFun) : s = t := by
  induction s using Quotient.inductionOn with | h a => ?_
  induction t using Quotient.inductionOn with | h b => ?_
  exact Quotient.sound (SectionRep.rel_of_f_eq a b h)

/-- The sc-smooth section is **sc⁺** if a representative `F` is an sc⁺-section functor
(Definition 8.3.4 (2)). -/
def IsScPlus (s : ScSection c) : Prop :=
  ∃ a : SectionRep c, ⟦a⟧ = s ∧ a.F ∈ a.S.A.E.plusSectionFunctors

/-- One representative is sc⁺ iff all are (Theorem 10.5.4 for `Γ⁺`). -/
theorem isScPlus_iff (s : ScSection c) :
    s.IsScPlus ↔ ∀ a : SectionRep c, ⟦a⟧ = s → a.F ∈ a.S.A.E.plusSectionFunctors := by
  refine ⟨fun ⟨a, ha, hplus⟩ b hb => ?_, fun h => ?_⟩
  · obtain ⟨-, 𝔄, h𝔄, -, hpush⟩ := (Quotient.exact (ha.trans hb.symm) : SectionRep.Rel a b)
    rw [← hpush]
    exact (GenSBMap.theorem_10_5_4 h𝔄).2.2.2.1.1 hplus
  · obtain ⟨a, rfl⟩ := Quotient.exists_rep s
    exact ⟨a, rfl, h a rfl⟩

end ScSection

/-- **2021 Definition 16.3.19, p. 729 (2017: Definition 16.28)**: an **sc⁺-smooth section** of
`(p, c̄)`: a class `[(f, Γ, W, F)]` with `F` an sc⁺-section functor. -/
abbrev ScPlusSection (c : StrongPolyfoldBundle p) : Type (u + 1) :=
  {s : ScSection c // s.IsScPlus}

end StrongPolyfoldBundle

end Polyfold
