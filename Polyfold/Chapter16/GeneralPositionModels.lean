import Polyfold.Chapter16.PerturbedSuborbifold
import Polyfold.Chapter15.GeneralPositionEquivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.6, p. 739, **Theorem 16.6.6** (2017: Theorem 16.8), the hypothesis "`(f, λ)` is in general
position" for an sc-Fredholm section `f` of a strong polyfold bundle and an sc⁺-multisection
`λ`.  Numbers and pages are the 2021 text's.

# General position of `(f, λ)` does not depend on the model

## The text, paraphrased

(p. 739) The notions for `(f, λ)` on a strong polyfold bundle `p : Y → Z` are those of the
representatives `(F, Λ)` in a model `(P : W → X, Γ, γ)` (Definitions 15.2.1, 15.3.5); two models
differ by a generalized strong bundle isomorphism (Definition 16.3.3).

## What is formalized (namespace `Polyfold.StrongPolyfoldBundle`)

* **`isInGeneralPosition_rep_iff`**: for two representatives `a`, `b` of the same section `f`,
  with `F_a` sc-Fredholm, and sc⁺-multisection functors `Λ_a`, `Λ_b` on their models
  representing the same `λ`: `(F_a, Λ_a)` is in general position iff `(F_b, Λ_b)` is
  (`SBLocalization.SDiagram.isInGeneralPosition_iff` for a diagram of the generalized strong
  bundle isomorphism between the models).
* **`ScSection.isInGeneralPositionWith_iff_of_rep`**: `(f, λ)` is in general position
  (`ScSection.IsInGeneralPositionWith`, "in some model") iff the representatives in a given model
  are.
* **`FredholmSection.isInGeneralPositionWith_iff_forall`**: iff the representatives in every
  model are.
* `ScSection.isInGeneralPositionWith_iff_of_mem`: iff representatives over a prescribed
  structure `S ∈ c̄` are in general position (such representatives exist for every `S`).
* `exists_isPerturbedSuborbifold_of_generalPosition_hyp`: the form of
  `exists_isPerturbedSuborbifold_hyp` whose general position hypothesis is the polyfold notion.

## Reading

`(f, λ)` in general position is read at the level-`1` points of a model, as in Chapter 15's
`IsInGeneralPosition`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization SBLocalization

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- A functor `Λ` on a structure `S ∈ c̄` with `λ(Γ|w|) = Λ(w)` represents `λ`. -/
theorem mk_ofFunctor_eq (t : ScPlusMultisection c) {S : StrongPolyfoldBundleStructure p}
    (hS : ⟦S⟧ = c) {Λ : S.A.W → ℚ≥0} (hΛ : IsScPlusMultisection S.A Λ)
    (hl : ∀ w, t.toFun (S.Γ (S.A.E.toEpGroupoid.π w)) = Λ w) :
    (⟦ofFunctor S hS Λ hΛ⟧ : ScPlusMultisection c) = t := by
  refine ScPlusMultisection.ext_toFun (funext fun y => ?_)
  rw [ScPlusMultisection.toFun_mk]
  change Λ (S.Γ.symm y).out = t.toFun y
  rw [← hl, show S.A.E.toEpGroupoid.π (S.Γ.symm y).out = S.Γ.symm y from Quotient.out_eq _,
    Homeomorph.apply_symm_apply]

/-- Conversely, `λ(Γ|w|) = Λ(w)` for the sc⁺-multisection of a functor `Λ`. -/
theorem toFun_of_mk_ofFunctor_eq {t : ScPlusMultisection c}
    {S : StrongPolyfoldBundleStructure p} {hS : ⟦S⟧ = c} {Λ : S.A.W → ℚ≥0}
    {hΛ : IsScPlusMultisection S.A Λ} (h : (⟦ofFunctor S hS Λ hΛ⟧ : ScPlusMultisection c) = t)
    (w : S.A.W) : t.toFun (S.Γ (S.A.E.toEpGroupoid.π w)) = Λ w := by
  subst h
  exact (ofFunctor S hS Λ hΛ).comm w

/-- **General position does not depend on the model** (Theorem 16.6.6's hypothesis; Definition
15.3.5): for two representatives `a`, `b` of the same section of `p`, with `F_a` sc-Fredholm,
and sc⁺-multisection functors `Λ_a`, `Λ_b` on their models representing the same
sc⁺-multisection `λ`, `(F_a, Λ_a)` is in general position iff `(F_b, Λ_b)` is. -/
theorem isInGeneralPosition_rep_iff (a b : SectionRep c) (hab : a.f = b.f)
    (ha : a.F ∈ a.S.A.E.fredholmSectionFunctors) (t : ScPlusMultisection c)
    {Λa : a.S.A.W → ℚ≥0} (hΛa : IsScPlusMultisection a.S.A Λa)
    (hla : ∀ w, t.toFun (a.S.Γ (a.S.A.E.toEpGroupoid.π w)) = Λa w)
    {Λb : b.S.A.W → ℚ≥0} (hΛb : IsScPlusMultisection b.S.A Λb)
    (hlb : ∀ w, t.toFun (b.S.Γ (b.S.A.E.toEpGroupoid.π w)) = Λb w) :
    IsInGeneralPosition a.S.A a.F Λa ↔ IsInGeneralPosition b.S.A b.F Λb := by
  obtain ⟨-, 𝔄, h𝔄, hΓ, hpush⟩ := SectionRep.rel_of_f_eq a b hab
  have hΨ := GenSBMap.isEquivalence_rep_Ψ h𝔄
  have hD : (GenSBMap.rep h𝔄).cls = 𝔄 := GenSBMap.cls_rep h𝔄
  rw [← hpush]
  refine (GenSBMap.rep h𝔄).isInGeneralPosition_iff hΨ ha hΛa hΛb fun w w' h => ?_
  rw [← hla, ← hlb, ← h]
  have e := congrFun hΓ (a.S.A.E.toEpGroupoid.π w)
  simp only [Function.comp_apply] at e
  have e' : 𝔄.orbitMap = (GenSBMap.rep h𝔄).orbitMap :=
    (congrArg GenSBMap.orbitMap hD).symm
  rw [← e, e']

namespace ScSection

/-- **`(f, λ)` is in general position iff its representatives in a given model are**:
for an sc-Fredholm section `f`, a representative `a` of `f` and an sc⁺-multisection functor `Λ`
on the model of `a` with `λ(Γ|w|) = Λ(w)`. -/
theorem isInGeneralPositionWith_iff_of_rep (s : ScSection c) (hs : s.IsFredholm)
    (t : ScPlusMultisection c) (a : SectionRep c) (ha : ⟦a⟧ = s) {Λ : a.S.A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection a.S.A Λ)
    (hl : ∀ w, t.toFun (a.S.Γ (a.S.A.E.toEpGroupoid.π w)) = Λ w) :
    s.IsInGeneralPositionWith t ↔ IsInGeneralPosition a.S.A a.F Λ := by
  constructor
  · rintro ⟨b, Λb, hΛb, hb, hbt, hgp⟩
    have hba : b.f = a.f := (Quotient.exact (hb.trans ha.symm) : SectionRep.Rel b a).1
    exact (isInGeneralPosition_rep_iff b a hba ((s.isFredholm_iff.1 hs) b hb) t hΛb
      (toFun_of_mk_ofFunctor_eq hbt) hΛ hl).1 hgp
  · intro h
    exact ⟨a, Λ, hΛ, ha, mk_ofFunctor_eq t a.hS hΛ hl, h⟩

/-- **General position can be read in any prescribed structure `S ∈ c̄`**: `(f, λ)` is in
general position iff some (equivalently, by `isInGeneralPositionWith_iff_of_rep`, every) pair
of representatives over `S` is. -/
theorem isInGeneralPositionWith_iff_of_mem (s : ScSection c) (hs : s.IsFredholm)
    (t : ScPlusMultisection c) {S : StrongPolyfoldBundleStructure p} (hS : ⟦S⟧ = c) :
    s.IsInGeneralPositionWith t ↔
      ∃ (a : SectionRep c) (Λ : a.S.A.W → ℚ≥0) (hΛ : IsScPlusMultisection a.S.A Λ),
        ⟦a⟧ = s ∧ a.S = S ∧ ⟦ofFunctor a.S a.hS Λ hΛ⟧ = t ∧
          IsInGeneralPosition a.S.A a.F Λ := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := ScSection.exists_rep_of_mem s hS
    obtain ⟨Λ, hΛ, hl⟩ := exists_functor_rep t a.hS
    exact ⟨a, Λ, hΛ, ha, rfl, mk_ofFunctor_eq t a.hS hΛ hl,
      (isInGeneralPositionWith_iff_of_rep s hs t a ha hΛ hl).1 h⟩
  · rintro ⟨a, Λ, hΛ, ha, -, ht, h⟩
    exact ⟨a, Λ, hΛ, ha, ht, h⟩

end ScSection

/-- **`(f, λ)` is in general position iff its representatives in every model are**. -/
theorem FredholmSection.isInGeneralPositionWith_iff_forall (s : FredholmSection c)
    (t : ScPlusMultisection c) :
    s.1.IsInGeneralPositionWith t ↔ ∀ a : SectionRep c, ⟦a⟧ = s.1 →
      ∀ Λ : a.S.A.W → ℚ≥0, IsScPlusMultisection a.S.A Λ →
        (∀ w, t.toFun (a.S.Γ (a.S.A.E.toEpGroupoid.π w)) = Λ w) →
          IsInGeneralPosition a.S.A a.F Λ := by
  constructor
  · intro h a ha Λ hΛ hl
    exact (ScSection.isInGeneralPositionWith_iff_of_rep s.1 s.2 t a ha hΛ hl).1 h
  · intro h
    obtain ⟨a, ha⟩ := Quotient.exists_rep s.1
    obtain ⟨Λ, hΛ, hl⟩ := exists_functor_rep t a.hS
    exact (ScSection.isInGeneralPositionWith_iff_of_rep s.1 s.2 t a ha hΛ hl).2
      (h a ha Λ hΛ hl)

/-- **`λ ∘ f` is a compact branched suborbifold of `Z`** (2021 p. 739, the text before Theorem
16.6.6), with general position as the polyfold notion: the form of
`exists_isPerturbedSuborbifold_hyp` in which `(f, λ)` is in general position in some model,
not necessarily the model of `a` that carries the tame germ data of `F`. -/
theorem exists_isPerturbedSuborbifold_of_generalPosition_hyp
    (hbd : c.polyfold.boundary = ∅) (s : FredholmSection c) {n : Y → ℝ} (hn : c.IsAuxNorm n)
    {U : Set Z} (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U) (a : SectionRep c)
    (ha : ⟦a⟧ = s.1) (Λ : a.S.A.W → ℚ≥0) (hΛ : IsScPlusMultisection a.S.A Λ)
    (ht : ScPlusMultisection.IsControlledBy (c := c) ⟦ofFunctor a.S a.hS Λ hΛ⟧ n U)
    (hgp : s.1.IsInGeneralPositionWith ⟦ofFunctor a.S a.hS Λ hΛ⟧)
    (hft : a.S.A.B.IsScFredholmSectionTame a.F) :
    ∃ θ : BranchedSuborbifold c.polyfold,
      IsPerturbedSuborbifold s.1 ⟦ofFunctor a.S a.hS Λ hΛ⟧ θ ∧ θ.IsCompact :=
  exists_isPerturbedSuborbifold_hyp hbd s hn hU hcc a ha Λ hΛ ht
    ((ScSection.isInGeneralPositionWith_iff_of_rep s.1 s.2 _ a ha hΛ
      (toFun_of_mk_ofFunctor_eq rfl)).1 hgp) hft

end StrongPolyfoldBundle

end Polyfold
