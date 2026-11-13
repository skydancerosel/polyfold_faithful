import Polyfold.Chapter16.PolyfoldFredholmSections
import Polyfold.Chapter16.BranchedTame
import Polyfold.Chapter15.PerturbedStokesInvariants

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.6, p. 739, the text before **Theorem 16.6.6** (2017: before Theorem 16.8): for a generic
sc⁺-multisection `λ`, `θ = λ ∘ f : Z → ℚ⁺` **defines a branched suborbifold of `Z`**.  Numbers
and pages are the 2021 text's.

## The text, paraphrased

(p. 739) For an sc-Fredholm section `f` of `p : Y → Z` and a generic sc⁺-multisection `λ`, the map
`θ = λ ∘ f : Z → ℚ⁺` defines a branched suborbifold of `Z` (Definition 16.4.1); if `f` is oriented,
`θ` carries a natural orientation (Theorem 15.4.1, Definition 15.4.2).

## What is formalized

* **`PolyfoldClass.BranchedRep.rel_of_toFun_eq`, `BranchedSuborbifold.toFun_injective`**: a
  branched suborbifold of a polyfold is determined by its function `θ : Z → ℚ` (two
  representatives with the same `|Θ| ∘ α⁻¹` are related by any generalized isomorphism `h` with
  `α' ∘ |h| = α`, since `h^*Θ'` at `x` is `Θ'` at any `y` with `|h|(|x|) = |y|`).
* `StrongPolyfoldBundle.perturbedFun s t = λ ∘ f`, `IsPerturbedSuborbifold s t θ`
  (`θ.toFun = λ ∘ f`), `perturbedRep` (the representative `(Λ ∘ F, (X, γ))` in a model
  `S ∈ c̄`), **`perturbedRep_toFun`** (`|Λ ∘ F| ∘ γ⁻¹ = λ ∘ f` in every model),
  **`isPerturbedSuborbifold_iff`** (`θ = λ ∘ f` iff `θ` is the class of `(Λ ∘ F, (X, γ))` in a
  model; so the class does not depend on the model and is unique: `isPerturbedSuborbifold_unique`).
* `ScSection.IsInGeneralPositionWith s t`: `(f, λ)` is in general position (Definitions 15.2.1,
  15.3.4) in some model.
* **`exists_isPerturbedSuborbifold_hyp`**: for `∂Z = ∅`, `f` sc-Fredholm with compact solution
  set, `(n, U)` controlling compactness and `λ` controlled by `(n, U)` with `(f, λ)` in general
  position in a model whose `F` has tame germ data (inherited, G.140), `λ ∘ f` is a compact branched
  suborbifold of `Z` (TX's `theorem_15_4_3_isBranched_hyp`; good position at the boundary is void
  since `∂X = ∅`).

## Reading

* "(f, λ) in general position" for a polyfold section is read in one model (the ep-groupoid notion,
  Definition 15.3.4, for the representatives `F`, `Λ` in that model).  That the notion is the same
  in every model (invariance under generalized strong bundle isomorphisms) is not formalized.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization EPLocalization.EPLoc

namespace PolyfoldClass

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z}

namespace BranchedRep

/-- **Two representatives with the same function `θ` are related** (Definition 16.4.1): any
generalized isomorphism `h` with `α' ∘ |h| = α` has `h^*Θ' = Θ`. -/
theorem rel_of_toFun_eq {a b : BranchedRep c} (h : a.toFun = b.toFun) : Rel a b := by
  obtain ⟨f, hf, hβ⟩ := (Quotient.exact (a.mem.trans b.mem.symm) : PolyfoldStructure.Equiv a.p b.p)
  refine ⟨f, hf, hβ, funext fun x => ?_⟩
  obtain ⟨y, hy⟩ := b.p.X.X.surjective_π (orbitMap f (a.p.X.X.π x))
  rw [pullTheta_eq_of_orbitMap hf b.isBranched.isFunctorial hy.symm]
  have hz : b.p.β (b.p.X.X.π y) = a.p.β (a.p.X.X.π x) := by
    rw [hy, hβ]; rfl
  rw [← b.toFun_eq hz, ← h, a.toFun_eq rfl]

end BranchedRep

namespace BranchedSuborbifold

/-- **A branched suborbifold is determined by its function `θ = |Θ| ∘ α⁻¹ : Z → ℚ`**. -/
theorem toFun_injective : Function.Injective (toFun : BranchedSuborbifold c → Z → ℚ) := by
  intro θ θ' h
  induction θ using Quotient.inductionOn with | h a => ?_
  induction θ' using Quotient.inductionOn with | h b => ?_
  exact Quotient.sound (BranchedRep.rel_of_toFun_eq h)

theorem toFun_mk (a : BranchedRep c) : toFun (⟦a⟧ : BranchedSuborbifold c) = a.toFun := rfl

end BranchedSuborbifold

end PolyfoldClass

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- The polyfold structure `(X, γ)` of a model `S ∈ c̄` belongs to the polyfold `(Z, c)`. -/
theorem toPolyfoldStructure_mem {S : StrongPolyfoldBundleStructure p} (hS : ⟦S⟧ = c) :
    (⟦S.toPolyfoldStructure⟧ : PolyfoldClass Z) = c.polyfold := by
  rw [← hS]; rfl

/-- **`θ = λ ∘ f : Z → ℚ⁺`** (2021 p. 739). -/
def perturbedFun (s : ScSection c) (t : ScPlusMultisection c) (z : Z) : ℚ :=
  (t.toFun (s.toFun z) : ℚ)

/-- `θ` is **the branched suborbifold `λ ∘ f`** (2021 p. 739): its function is `λ ∘ f`. -/
def IsPerturbedSuborbifold (s : ScSection c) (t : ScPlusMultisection c)
    (θ : BranchedSuborbifold c.polyfold) : Prop :=
  θ.toFun = perturbedFun s t

/-- In a model, `λ(f(γ|x|)) = Λ(F(x))` for representatives `F` of `f` and `Λ` of `λ`. -/
theorem lam_f_eq {S : StrongPolyfoldBundleStructure p} {F : S.A.Obj → S.A.W} {f : Z → Y}
    (hf : ∀ x, f (S.γ (S.A.X.π x)) = S.Γ (S.A.E.toEpGroupoid.π (F x))) {Λ : S.A.W → ℚ≥0}
    {lam : Y → ℚ≥0} (hl : ∀ w, lam (S.Γ (S.A.E.toEpGroupoid.π w)) = Λ w) (x : S.A.Obj) :
    lam (f (S.γ (S.A.X.π x))) = Λ (F x) := by
  rw [hf, hl]

/-- **The representative `(Λ ∘ F, (X, γ))`** of `λ ∘ f` in a model `S ∈ c̄`, for `Λ ∘ F` a
branched ep⁺-subgroupoid. -/
def perturbedRep {S : StrongPolyfoldBundleStructure p} (hS : ⟦S⟧ = c) (F : S.A.Obj → S.A.W)
    (Λ : S.A.W → ℚ≥0)
    (hbr : S.A.X.IsBranchedEpSubgroupoid fun x => (Λ (F x) : ℚ)) : BranchedRep c.polyfold :=
  ⟨S.toPolyfoldStructure, toPolyfoldStructure_mem hS, fun x => (Λ (F x) : ℚ), hbr⟩

/-- **Every model carries a functor representing `λ`**: for `S ∈ c̄` an sc⁺-multisection functor
`Λ` on `S` with `λ(Γ|w|) = Λ(w)` (PB's `exists_rep_of_mem`, Proposition 11.5.3). -/
theorem exists_functor_rep (t : ScPlusMultisection c) {S : StrongPolyfoldBundleStructure p}
    (hS : ⟦S⟧ = c) :
    ∃ Λ : S.A.W → ℚ≥0, SBLocalization.IsScPlusMultisection S.A Λ ∧
      ∀ w, t.toFun (S.Γ (S.A.E.toEpGroupoid.π w)) = Λ w := by
  obtain ⟨b, hb, hbS⟩ := exists_rep_of_mem t hS
  subst hbS
  exact ⟨b.Λ, b.isScPlusMultisection, fun w => by rw [← hb]; exact b.comm w⟩

/-- **`|Λ ∘ F| ∘ γ⁻¹ = λ ∘ f` in every model**: for a representative `a` of `f` and a functor `Λ`
on the model of `a` representing `λ` (`λ(Γ|w|) = Λ(w)`). -/
theorem perturbedRep_toFun (a : SectionRep c) (t : ScPlusMultisection c) (Λ : a.S.A.W → ℚ≥0)
    (hl : ∀ w, t.toFun (a.S.Γ (a.S.A.E.toEpGroupoid.π w)) = Λ w)
    (hbr : a.S.A.X.IsBranchedEpSubgroupoid fun x => (Λ (a.F x) : ℚ)) :
    (perturbedRep a.hS a.F Λ hbr).toFun = perturbedFun (c := c) ⟦a⟧ t := by
  funext z
  obtain ⟨x, rfl⟩ := a.S.surjective_γπ z
  refine (BranchedRep.toFun_eq (perturbedRep a.hS a.F Λ hbr) (x := x) rfl).trans ?_
  change ((Λ (a.F x) : ℚ≥0) : ℚ) = ((t.toFun (a.f (a.S.γ (a.S.A.X.π x))) : ℚ≥0) : ℚ)
  rw [lam_f_eq a.comm hl x]

/-- The same, for the sc⁺-multisection `ofFunctor` of a functor `Λ` on the model of `a`. -/
theorem perturbedRep_toFun_ofFunctor (a : SectionRep c) (Λ : a.S.A.W → ℚ≥0)
    (hΛ : SBLocalization.IsScPlusMultisection a.S.A Λ)
    (hbr : a.S.A.X.IsBranchedEpSubgroupoid fun x => (Λ (a.F x) : ℚ)) :
    (perturbedRep a.hS a.F Λ hbr).toFun =
      perturbedFun (c := c) ⟦a⟧ ⟦ofFunctor a.S a.hS Λ hΛ⟧ :=
  perturbedRep_toFun a ⟦ofFunctor a.S a.hS Λ hΛ⟧ Λ (fun w => (ofFunctor a.S a.hS Λ hΛ).comm w) hbr

/-- **`θ = λ ∘ f` iff `θ` is the class of `(Λ ∘ F, (X, γ))`** for representatives in any model:
the branched suborbifold `λ ∘ f` does not depend on the model. -/
theorem isPerturbedSuborbifold_iff (a : SectionRep c) (t : ScPlusMultisection c)
    (Λ : a.S.A.W → ℚ≥0) (hl : ∀ w, t.toFun (a.S.Γ (a.S.A.E.toEpGroupoid.π w)) = Λ w)
    (hbr : a.S.A.X.IsBranchedEpSubgroupoid fun x => (Λ (a.F x) : ℚ))
    (θ : BranchedSuborbifold c.polyfold) :
    IsPerturbedSuborbifold (c := c) ⟦a⟧ t θ ↔
      θ = (⟦perturbedRep a.hS a.F Λ hbr⟧ : BranchedSuborbifold c.polyfold) := by
  refine ⟨fun h => BranchedSuborbifold.toFun_injective ?_, fun h => ?_⟩
  · rw [h, BranchedSuborbifold.toFun_mk, perturbedRep_toFun a t Λ hl]
  · change θ.toFun = _
    rw [h, BranchedSuborbifold.toFun_mk, perturbedRep_toFun a t Λ hl]

/-- **The branched suborbifold `λ ∘ f` is unique** (if it exists). -/
theorem isPerturbedSuborbifold_unique {s : ScSection c} {t : ScPlusMultisection c}
    {θ θ' : BranchedSuborbifold c.polyfold} (h : IsPerturbedSuborbifold s t θ)
    (h' : IsPerturbedSuborbifold s t θ') : θ = θ' :=
  BranchedSuborbifold.toFun_injective (h.trans h'.symm)

/-- **`(f, λ)` is in general position** (Theorem 16.6.6; Definitions 15.2.1, 15.3.4), read in a
model: some representative `F` of `f` and some sc⁺-multisection functor `Λ` on the same model
representing `λ` are in general position. -/
def ScSection.IsInGeneralPositionWith (s : ScSection c) (t : ScPlusMultisection c) : Prop :=
  ∃ (a : SectionRep c) (Λ : a.S.A.W → ℚ≥0) (hΛ : SBLocalization.IsScPlusMultisection a.S.A Λ),
    ⟦a⟧ = s ∧ ⟦ofFunctor a.S a.hS Λ hΛ⟧ = t ∧ SBLocalization.IsInGeneralPosition a.S.A a.F Λ

/-- **`λ ∘ f` is a compact branched suborbifold of `Z`** (2021 p. 739, the text before Theorem
16.6.6), with the inherited tame germ data of `F` (G.140): for `∂Z = ∅`, `f` sc-Fredholm with
compact solution set, `(n, U)` controlling compactness and `λ` controlled by `(n, U)` with
`(f, λ)` in general position in the model of `a`, the class of `(Λ ∘ F, (X, γ))` is a compact
branched suborbifold whose function is `λ ∘ f`.  (Compactness of the solution set is not
needed separately: `(n, U)` controlling compactness contains it.) -/
theorem exists_isPerturbedSuborbifold_hyp (hbd : c.polyfold.boundary = ∅)
    (s : FredholmSection c) {n : Y → ℝ} (hn : c.IsAuxNorm n)
    {U : Set Z} (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U) (a : SectionRep c)
    (ha : ⟦a⟧ = s.1) (Λ : a.S.A.W → ℚ≥0) (hΛ : SBLocalization.IsScPlusMultisection a.S.A Λ)
    (ht : ScPlusMultisection.IsControlledBy (c := c) ⟦ofFunctor a.S a.hS Λ hΛ⟧ n U)
    (hgp : SBLocalization.IsInGeneralPosition a.S.A a.F Λ)
    (hft : a.S.A.B.IsScFredholmSectionTame a.F) :
    ∃ θ : BranchedSuborbifold c.polyfold,
      IsPerturbedSuborbifold s.1 ⟦ofFunctor a.S a.hS Λ hΛ⟧ θ ∧ θ.IsCompact := by
  have hFa := (s.1.isFredholm_iff.1 s.2) a ha
  have hcca := (a.controlsCompactness_iff hn hU).1 (by rw [ha]; exact hcc)
  set b := ofFunctor a.S a.hS Λ hΛ
  have hN1 : ∀ x, SBLocalization.pointwiseNorm (a.S.normOf n) Λ x ≤ 1 := by
    intro x
    rw [← normLam_eq a.hS n Λ b.lam x fun w _ => b.comm w]
    exact ht.1 _
  have hdom : SBLocalization.domSupp Λ ⊆ a.g ⁻¹' U := by
    intro x hx
    apply ht.2
    rw [← remark_16_5_3 b]
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have htr := SBLocalization.IsInGeneralPosition.isTransversal hFa hΛ hgp
  have hgood : ∀ x ∈ a.S.A.X.PObj.boundary, 0 < Λ (a.F x) →
      SBLocalization.IsGoodPositionAt a.F Λ x := by
    intro x hx
    have := (mem_boundary_iff_obj a.hS x).2 hx
    rw [hbd] at this
    exact this.elim
  obtain ⟨hbr, hcpt⟩ :=
    SBLocalization.theorem_15_4_3_isBranched_hyp hFa hft hcca hΛ hdom hN1 htr hgood
  refine ⟨(⟦perturbedRep a.hS a.F Λ hbr⟧ : BranchedSuborbifold c.polyfold), ?_, ⟨_, rfl, hcpt⟩⟩
  exact (perturbedRep_toFun_ofFunctor a Λ hΛ hbr).trans (by rw [ha])

end StrongPolyfoldBundle

end Polyfold
