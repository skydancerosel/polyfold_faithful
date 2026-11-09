import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_8

/-! Round trip for V10_8 (2021 Remark 10.1.11, p. 470; 2017: Remark 10.1, p. 340: in
`ℤ/2 ⋉ ℝ²` with `F = id`, `G = -id`, the morphism `1_0 : F(0) → G(0)` lies in no sc-smooth local
family `α_z : F(z) → G(z)`).

The item lists the definitions `pointReflectionEpGroupoid`, `negFunctor` (vocabulary) and five
theorems (no universes); `A` is the conjunction of their types:
* `isEquivalence_negFunctor` (`G = -id` is an equivalence),
* `orbitMap_id_eq_negFunctor` (`|id| = |G|`),
* `remark_10_1_11_family` (`z ↦ (-1, z)` is an sc-smooth family `F(z) → G(z)` on all of `ℝ²`),
* `remark_10_1_11` (no family `α` merely *continuous at `0`*, with `α 0 = 1_0` and
  `s(α z) = F z`, `t(α z) = G z` eventually near `0`),
* `remark_10_1_11_scSmooth` (no family sc-smooth on an open `U ∋ 0` with the same properties on
  `U`; this is `B`'s claim, with the last two conjuncts in the other order).

`B` pins down the example (structure maps, unit, object M-polyfold `rnPolyfold 2`, `id`, `-id`)
and states the sc-smooth non-existence.

* `A_to_B`: the pinning equations are `rfl`; the claim is `remark_10_1_11_scSmooth` reordered.
* `B_to_A`: `remark_10_1_11_scSmooth` is `B`'s claim reordered.  `remark_10_1_11` (the
  "continuous at `0`" form) also follows from `B`: near `0` the first component of `α` is
  locally constant `= 1` (discreteness of `ℤˣ`), so on the open `U = interior {…}` the family `α`
  agrees with the unit section `z ↦ (1, z)`, which is sc-smooth; `B` applied to `α` on `U`
  gives the contradiction.  The three remaining conjuncts (`isEquivalence_negFunctor`,
  `orbitMap_id_eq_negFunctor`, `remark_10_1_11_family`) are side facts about the example that
  `B` does not mention; they are re-proved outright below (the project's proofs, copied, from
  non-item lemmas).
-/

namespace RoundTrip.V10_8
open Polyfold Polyfold.EpGroupoid.Examples Set Filter Topology

/-- The project's statement, one definition per theorem. -/
def A1 : Prop := type_of% @Polyfold.EpGroupoid.Examples.isEquivalence_negFunctor
def A2 : Prop := type_of% @Polyfold.EpGroupoid.Examples.orbitMap_id_eq_negFunctor
def A3 : Prop := type_of% @Polyfold.EpGroupoid.Examples.remark_10_1_11_family
def A4 : Prop := type_of% @Polyfold.EpGroupoid.Examples.remark_10_1_11
def A5 : Prop := type_of% @Polyfold.EpGroupoid.Examples.remark_10_1_11_scSmooth

/-- The project's statement. -/
def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5

theorem A_holds : A :=
  ⟨Polyfold.EpGroupoid.Examples.isEquivalence_negFunctor,
    Polyfold.EpGroupoid.Examples.orbitMap_id_eq_negFunctor,
    Polyfold.EpGroupoid.Examples.remark_10_1_11_family,
    Polyfold.EpGroupoid.Examples.remark_10_1_11,
    Polyfold.EpGroupoid.Examples.remark_10_1_11_scSmooth⟩

theorem A_to_B : A → B := by
  rintro ⟨-, -, -, -, h5⟩
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, ?_⟩
  rintro ⟨U, α, hU, h0U, hα, hst, h0⟩
  exact h5 ⟨U, α, hU, h0U, hα, h0, hst⟩

/-! ### The side facts, re-proved outright (the project's proofs) -/

theorem isEquivalence_negFunctor' : A1 :=
  negFunctor.lemma_10_1_2
    { faithful := (GroupoidFunctor.faithful_iff _).2 fun _ _ _ _ he => by
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        exact Prod.ext h1 (neg_injective h2)
      full := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => by
        have hs' : ψ.2 = -x := hs
        have ht' : ψ.1 • ψ.2 = -x' := ht
        refine ⟨(ψ.1, x), rfl, ?_, Prod.ext rfl hs'.symm⟩
        change ψ.1 • x = x'
        rw [hs', smul_neg] at ht'
        exact neg_injective ht'
      essSurj := (GroupoidFunctor.essSurj_iff _).2 fun y =>
        ⟨-y, pointReflectionEpGroupoid.unit y, (neg_neg y).symm, one_smul _ y⟩ }
    (isLocalScDiffeo_rn_neg 2)

theorem orbitMap_id_eq_negFunctor' : A2 := by
  funext q
  induction q using Quotient.inductionOn with | h z => ?_
  change pointReflectionEpGroupoid.π z = pointReflectionEpGroupoid.π (-z)
  exact pointReflectionEpGroupoid.π_eq_π_iff.2
    ⟨((-1 : ℤˣ), z), rfl, by
      change (-1 : ℤˣ) • z = -z
      rw [Units.neg_smul, one_smul]⟩

theorem remark_10_1_11_family' : A3 :=
  ⟨isScSmoothMap_sheet (-1), fun z => ⟨rfl, by
    change (-1 : ℤˣ) • z = -z
    rw [Units.neg_smul, one_smul]⟩⟩

theorem B_to_A : B → A := by
  intro hB
  have hB' := hB.2.2.2.2.2.2.2
  -- the sc-smooth form
  have h5 : A5 := by
    rintro ⟨U, α, hU, h0U, hα, h0, hst⟩
    exact hB' ⟨U, α, hU, h0U, hα, hst, h0⟩
  -- the "continuous at `0`" form, from `B`
  have h4 : A4 := by
    rintro ⟨α, hc, h0, hα⟩
    have h1 : ∀ᶠ z in 𝓝 (0 : Fin 2 → ℝ), (α z).1 = 1 := by
      have := ((continuous_fst.tendsto (α 0)).comp hc).eventually
        ((isOpen_discrete {(α 0).1}).mem_nhds (mem_singleton _))
      filter_upwards [this] with z hz
      have hz' : (α z).1 = (α 0).1 := hz
      rw [hz', h0]
      rfl
    set S : Set (Fin 2 → ℝ) := {z | (α z).1 = 1 ∧
      (pointReflectionEpGroupoid.src (α z) = (EpFunctor.id pointReflectionEpGroupoid).obj z ∧
        pointReflectionEpGroupoid.tgt (α z) = negFunctor.obj z)} with hS
    have hSn : S ∈ 𝓝 (0 : Fin 2 → ℝ) := h1.and hα
    -- on `S`, `α` is the unit section
    have hunit : EqOn (fun z => pointReflectionEpGroupoid.unit z) α (interior S) := by
      intro z hz
      obtain ⟨h1z, hsz, -⟩ := interior_subset hz
      have hs' : (α z).2 = z := hsz
      change ((1 : ℤˣ), z) = α z
      exact Prod.ext h1z.symm hs'.symm
    have hsm : pointReflectionEpGroupoid.PObj.IsScSmoothOn pointReflectionEpGroupoid.PMor α
        (interior S) :=
      (pointReflectionEpGroupoid.isScSmoothMap_unit.mono isOpen_interior
        (subset_univ _)).congr hunit
    exact hB' ⟨interior S, α, isOpen_interior, mem_interior_iff_mem_nhds.2 hSn, hsm,
      fun z hz => (interior_subset hz).2, h0⟩
  exact ⟨isEquivalence_negFunctor', orbitMap_id_eq_negFunctor', remark_10_1_11_family', h4, h5⟩

#rt_check RoundTrip.V10_8.A_to_B [Polyfold.EpGroupoid.Examples.isEquivalence_negFunctor,
  Polyfold.EpGroupoid.Examples.orbitMap_id_eq_negFunctor,
  Polyfold.EpGroupoid.Examples.remark_10_1_11_family,
  Polyfold.EpGroupoid.Examples.remark_10_1_11,
  Polyfold.EpGroupoid.Examples.remark_10_1_11_scSmooth]
#rt_check RoundTrip.V10_8.B_to_A [Polyfold.EpGroupoid.Examples.isEquivalence_negFunctor,
  Polyfold.EpGroupoid.Examples.orbitMap_id_eq_negFunctor,
  Polyfold.EpGroupoid.Examples.remark_10_1_11_family,
  Polyfold.EpGroupoid.Examples.remark_10_1_11,
  Polyfold.EpGroupoid.Examples.remark_10_1_11_scSmooth]
#rt_overlap RoundTrip.V10_8.B_to_A [Polyfold.EpGroupoid.Examples.isEquivalence_negFunctor,
  Polyfold.EpGroupoid.Examples.orbitMap_id_eq_negFunctor,
  Polyfold.EpGroupoid.Examples.remark_10_1_11_family,
  Polyfold.EpGroupoid.Examples.remark_10_1_11,
  Polyfold.EpGroupoid.Examples.remark_10_1_11_scSmooth]

end RoundTrip.V10_8
