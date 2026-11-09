import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_32

/-! Round trip for V11_32 (2021 §11.5, Proposition 11.5.3, p. 548: multisection functors along
generalized strong bundle isomorphisms).

The item lists the definitions `GenSBMap.pushMult`, `GenSBMap.pullMult`, `SDiagram.pushMult`,
`SDiagram.pullMult` (vocabulary) and nine theorems; `A` is the conjunction of their types, all
universes at `0` (`α : Type`): `GenSBMap.proposition_11_5_3` (for functors `Λ : W → ℚ≥0`:
independence of the representative, functors go to functors, mutually inverse, same `|[D]|` gives
the same maps), and the diagram lemmas for functors into an arbitrary `α`: `SDiagram.pushMult_eq`,
`pullMult_eq`, `isWFunctor_pushMult`, `isWFunctor_pullMult`, `pullMult_pushMult`,
`pushMult_pullMult`, `pushMult_eq_of_orbitMap_eq`, `pullMult_eq_of_orbitMap_eq`.

`B` (for sc⁺-multisections `Λ : W → ℚ`, the blind author's `IsScPlusMultisectionB`: values `≥ 0`,
a functor, locally `∑_{i : sᵢ(P w) = w} σᵢ` for local sc⁺-sections): `[D]_*Λ`, `[D]^*Λ'` are
sc⁺-multisections and are computed by `Ψ_*Φ^*`, `Φ_*Ψ^*` on every representative; mutually
inverse; equal for `|f₁| = |f₂|`.

* `A → B` fails at one point only: that `[D]_*Λ` and `[D]^*Λ'` have local sc⁺-section
  structures.  `A` has nothing on local section structures (the project's header: not formalized,
  Definition 13.2.1 is not in the repository).  `A_to_BFunctorPart` proves everything else of `B`
  from `A` (for `ℚ`-valued `Λ`, through the diagram lemmas, which hold for every `α`): values
  `≥ 0`, functoriality, the formulas on every representative, the inverses, and the dependence on
  `|[D]|` only.
* `B → A` fails: `A`'s conjuncts are about arbitrary functors (`ℚ≥0`-valued in
  `proposition_11_5_3`, `α`-valued in the diagram lemmas); `B` speaks only about
  sc⁺-multisections into `ℚ`, which do not separate orbits.  Re-proving `A` outright would not
  use `B` (vacuous), so no `B_to_A` is given. -/

namespace RoundTrip.V11_32
open Polyfold Polyfold.SBLocalization CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.GenSBMap.proposition_11_5_3.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.pushMult_eq.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.pullMult_eq.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.isWFunctor_pushMult.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.isWFunctor_pullMult.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.pullMult_pushMult.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.pushMult_pullMult.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.pushMult_eq_of_orbitMap_eq.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.pullMult_eq_of_orbitMap_eq.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.GenSBMap.proposition_11_5_3.{0},
    @Polyfold.SBLocalization.SDiagram.pushMult_eq.{0, 0},
    @Polyfold.SBLocalization.SDiagram.pullMult_eq.{0, 0},
    @Polyfold.SBLocalization.SDiagram.isWFunctor_pushMult.{0, 0},
    @Polyfold.SBLocalization.SDiagram.isWFunctor_pullMult.{0, 0},
    @Polyfold.SBLocalization.SDiagram.pullMult_pushMult.{0, 0},
    @Polyfold.SBLocalization.SDiagram.pushMult_pullMult.{0, 0},
    @Polyfold.SBLocalization.SDiagram.pushMult_eq_of_orbitMap_eq.{0, 0},
    @Polyfold.SBLocalization.SDiagram.pullMult_eq_of_orbitMap_eq.{0, 0}⟩

/-! ### `A → B` without the local section structures -/

/-- `IsScPlusMultisectionB` without its local section structure. -/
def IsFunctorPartB (A : SEP.{0}) (Λ : A.W → ℚ) : Prop := (∀ w, 0 ≤ Λ w) ∧ IsWFunctor A Λ

/-- `B` with the conclusions "is an sc⁺-multisection" weakened to `IsFunctorPartB` (the
hypotheses are unchanged). -/
def BFunctorPart : Prop :=
  (∀ (A A' : SEP.{0}) (f : GenSBMap A A') (hf : f.IsGeneralizedIso),
    (∀ Λ : A.W → ℚ, IsScPlusMultisectionB A Λ →
      IsFunctorPartB A' (GenSBMap.pushMult hf Λ)) ∧
    (∀ Λ' : A'.W → ℚ, IsScPlusMultisectionB A' Λ' →
      IsFunctorPartB A (GenSBMap.pullMult hf Λ')) ∧
    ∀ (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ), D.cls = f →
      (∀ Λ : A.W → ℚ, IsScPlusMultisectionB A Λ →
        GenSBMap.pushMult hf Λ = pushMult D.Ψ hΨ (pullMult D.Φ Λ)) ∧
      (∀ Λ' : A'.W → ℚ, IsScPlusMultisectionB A' Λ' →
        GenSBMap.pullMult hf Λ' = pushMult D.Φ D.isEquivalence_Φ (pullMult D.Ψ Λ'))) ∧
  (∀ (A A' : SEP.{0}) (f : GenSBMap A A') (hf : f.IsGeneralizedIso),
    (∀ Λ : A.W → ℚ, IsScPlusMultisectionB A Λ →
      GenSBMap.pullMult hf (GenSBMap.pushMult hf Λ) = Λ) ∧
    (∀ Λ' : A'.W → ℚ, IsScPlusMultisectionB A' Λ' →
      GenSBMap.pushMult hf (GenSBMap.pullMult hf Λ') = Λ')) ∧
  (∀ (A A' : SEP.{0}) (f₁ f₂ : GenSBMap A A') (h₁ : f₁.IsGeneralizedIso)
    (h₂ : f₂.IsGeneralizedIso), f₁.orbitMap = f₂.orbitMap →
    (∀ Λ : A.W → ℚ, IsScPlusMultisectionB A Λ →
      GenSBMap.pushMult h₁ Λ = GenSBMap.pushMult h₂ Λ) ∧
    (∀ Λ' : A'.W → ℚ, IsScPlusMultisectionB A' Λ' →
      GenSBMap.pullMult h₁ Λ' = GenSBMap.pullMult h₂ Λ'))

theorem A_to_BFunctorPart : A → BFunctorPart := by
  rintro ⟨-, -, -, hfp, hfl, hpp, hpl, hpo, hlo⟩
  have ho : ∀ {A A' : SEP.{0}} {f : GenSBMap A A'} (hf : f.IsGeneralizedIso)
      {D : SDiagram A A'}, D.cls = f → (GenSBMap.rep hf).orbitMap = D.orbitMap :=
    fun hf D hD => by
      rw [← GenSBMap.orbitMap_cls, ← GenSBMap.orbitMap_cls, GenSBMap.cls_rep, hD]
  refine ⟨fun A A' f hf => ⟨fun Λ hΛ => ⟨fun w' => hΛ.1 _, hfp hΛ.2.1⟩,
      fun Λ' hΛ' => ⟨fun w => hΛ'.1 _, hfl hΛ'.2.1⟩,
      fun D hΨ hD => ⟨fun Λ hΛ => hpo _ hΨ (ho hf hD) hΛ.2.1,
        fun Λ' hΛ' => hlo _ hΨ (ho hf hD) hΛ'.2.1⟩⟩,
    fun A A' f hf => ⟨fun Λ hΛ => hpp hΛ.2.1, fun Λ' hΛ' => hpl hΛ'.2.1⟩,
    fun A A' f₁ f₂ h₁ h₂ h => ?_⟩
  have h' : (GenSBMap.rep h₁).orbitMap = (GenSBMap.rep h₂).orbitMap := by
    rw [← GenSBMap.orbitMap_cls, ← GenSBMap.orbitMap_cls, GenSBMap.cls_rep, GenSBMap.cls_rep, h]
  exact ⟨fun Λ hΛ => hpo _ _ h' hΛ.2.1, fun Λ' hΛ' => hlo _ _ h' hΛ'.2.1⟩

/-- `B` is exactly `BFunctorPart` plus: the conclusions `[D]_*Λ`, `[D]^*Λ'` are
sc⁺-multisections (so the only missing content is their local section structures). -/
theorem BFunctorPart_and_mult_iff_B :
    (BFunctorPart ∧ ∀ (A A' : SEP.{0}) (f : GenSBMap A A') (hf : f.IsGeneralizedIso),
      (∀ Λ : A.W → ℚ, IsScPlusMultisectionB A Λ →
        IsScPlusMultisectionB A' (GenSBMap.pushMult hf Λ)) ∧
      (∀ Λ' : A'.W → ℚ, IsScPlusMultisectionB A' Λ' →
        IsScPlusMultisectionB A (GenSBMap.pullMult hf Λ'))) ↔ B := by
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, hm⟩
    exact ⟨fun A A' f hf => ⟨(hm A A' f hf).1, (hm A A' f hf).2, (h1 A A' f hf).2.2⟩, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨fun A A' f hf => ⟨fun Λ hΛ => ?_, fun Λ' hΛ' => ?_, (h1 A A' f hf).2.2⟩, h2, h3⟩,
      fun A A' f hf => ⟨(h1 A A' f hf).1, (h1 A A' f hf).2.1⟩⟩
    · obtain ⟨a, b, -⟩ := (h1 A A' f hf).1 Λ hΛ
      exact ⟨a, b⟩
    · obtain ⟨a, b, -⟩ := (h1 A A' f hf).2.1 Λ' hΛ'
      exact ⟨a, b⟩

#rt_check RoundTrip.V11_32.A_to_BFunctorPart [
  Polyfold.SBLocalization.GenSBMap.proposition_11_5_3,
  Polyfold.SBLocalization.SDiagram.pushMult_eq, Polyfold.SBLocalization.SDiagram.pullMult_eq,
  Polyfold.SBLocalization.SDiagram.isWFunctor_pushMult,
  Polyfold.SBLocalization.SDiagram.isWFunctor_pullMult,
  Polyfold.SBLocalization.SDiagram.pullMult_pushMult,
  Polyfold.SBLocalization.SDiagram.pushMult_pullMult,
  Polyfold.SBLocalization.SDiagram.pushMult_eq_of_orbitMap_eq,
  Polyfold.SBLocalization.SDiagram.pullMult_eq_of_orbitMap_eq]
#rt_check RoundTrip.V11_32.BFunctorPart_and_mult_iff_B [
  Polyfold.SBLocalization.GenSBMap.proposition_11_5_3,
  Polyfold.SBLocalization.SDiagram.pushMult_eq, Polyfold.SBLocalization.SDiagram.pullMult_eq,
  Polyfold.SBLocalization.SDiagram.isWFunctor_pushMult,
  Polyfold.SBLocalization.SDiagram.isWFunctor_pullMult,
  Polyfold.SBLocalization.SDiagram.pullMult_pushMult,
  Polyfold.SBLocalization.SDiagram.pushMult_pullMult,
  Polyfold.SBLocalization.SDiagram.pushMult_eq_of_orbitMap_eq,
  Polyfold.SBLocalization.SDiagram.pullMult_eq_of_orbitMap_eq]

end RoundTrip.V11_32
