import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V15_3

set_option maxSynthPendingDepth 3

/-! Round trip for V15_3 (2021 Remark 15.1.2, p. 684; 2017: Remark 15.1: with the empty sum `0`,
(1) of Theorem 15.1.1 follows from (2)).

`A` is the conjunction of the types of `linearization_eq_zero`, `remark_15_1_2`,
`remark_15_1_2_model` and `mem_support_linSumModel_iff`, the `SEP` lemmas at universe `0` (the
model lemmas have no universe parameter).

* `A_to_B`: (a) `linSumIntr c` is `T(f,Λ)(y)` (`linearization_eq`, not an item theorem, with the
  data `(O, s, σ, c)`), which is `0` by `linearization_eq_zero` (from `A`); (b) a `T` satisfying
  (2) agrees with `linSumIntr` of the data given by `nonempty_localLinData`, hence with
  `linearization f Λ y = 0`.
* `B_to_A`: `B` assumes `Λ` is an sc⁺-multisection functor, while `linearization_eq_zero` and
  `remark_15_1_2` only assume `f` sc-Fredholm (and `Λ` arbitrary); the model lemmas say nothing
  about `SEP`.  So `B` does not give `A`; the conjuncts are re-proved outright below (copies of the
  project's short proofs, from non-item lemmas), without using `B`.  The main conjunct
  `linearization_eq_zero` restricted to sc⁺-multisections (`main_B_to_A`) does follow from `B` (b)
  applied to `T := linearization f Λ` (property (2) of `T` by `linearization_eq`).
-/

namespace RoundTrip.V15_3
open Polyfold Polyfold.SBLocalization Polyfold.Linearization15 Polyfold.StrongRetr Polyfold.MPolyfold

def A : Prop :=
  (type_of% @Polyfold.SBLocalization.linearization_eq_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.remark_15_1_2.{0}) ∧
  (type_of% @Polyfold.Linearization15.remark_15_1_2_model) ∧
  (type_of% @Polyfold.Linearization15.mem_support_linSumModel_iff)

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.linearization_eq_zero.{0}, @Polyfold.SBLocalization.remark_15_1_2.{0},
    @Polyfold.Linearization15.remark_15_1_2_model,
    @Polyfold.Linearization15.mem_support_linSumModel_iff⟩

/-- The main conjunct alone. -/
def Amain : Prop := type_of% @Polyfold.SBLocalization.linearization_eq_zero.{0}

theorem main_A_to_B : Amain → B := by
  intro hz Asep f Λ hf hΛ
  refine ⟨fun O hO k s σ hrep c hc hsub y hy h0 => ?_, fun T hT y h0 => ?_⟩
  · have e := linearization_eq hf (⟨O, hO, k, s, σ, hrep, c, hc, hsub, hy⟩ : LocalLinData Asep Λ y)
    rw [← hz hf h0]
    exact e.symm
  · obtain ⟨d⟩ := nonempty_localLinData hΛ y
    rw [hT d.O d.isOpen d.k d.s d.σ d.rep d.c d.isChart d.sub y d.mem]
    rw [← hz hf h0]
    exact (linearization_eq hf d).symm

theorem A_to_B : A → B := fun h => main_A_to_B h.1

/-- `B ⇒ linearization_eq_zero` for sc⁺-multisections `Λ` (the setting of `B`). -/
theorem main_B_to_A_multisection : B → ∀ (Asep : SEP.{0}) (f : Asep.Obj → Asep.W)
    (Λ : Asep.W → ℚ≥0), Asep.E.IsScFredholmSectionFunctor f → IsScPlusMultisection Asep Λ →
    ∀ (x : Asep.X.PObj.Level 1), Λ (f (Asep.X.PObj.levelVal 1 x)) = 0 →
      linearization f Λ x = 0 := by
  intro hB Asep f Λ hf hΛ x h0
  refine (hB Asep f Λ hf hΛ).2 (linearization f Λ) ?_ x h0
  intro O hO k s σ hrep c hc hsub y hy
  exact linearization_eq hf ⟨O, hO, k, s, σ, hrep, c, hc, hsub, hy⟩

/-! ### The conjuncts of `A`, re-proved outright (the project's proofs, copied) -/

section Copies
variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open Classical in
theorem remark_model' (fh : E 0 → F 0) {k : ℕ} (sh : Fin k → E 0 → F 0)
    {σ : Fin k → ℚ≥0} (hσ : ∀ i, 0 < σ i) (z : E 1)
    (h0 : (∑ i, if sh i (E.toBase 1 z) = fh (E.toBase 1 z) then σ i else 0) = 0) :
    linSumModel U R fh sh σ z = 0 := by
  have hnone : ∀ i, sh i (E.toBase 1 z) ≠ fh (E.toBase 1 z) := fun i hi => by
    have := (Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ i)
    rw [if_pos hi] at this
    exact (hσ i).ne' this
  unfold linSumModel
  exact Finset.sum_eq_zero fun i _ => if_neg (hnone i)

open Classical in
theorem mem_support' (fh : E 0 → F 0) {k : ℕ} (sh : Fin k → E 0 → F 0)
    {σ : Fin k → ℚ≥0} (hσ : ∀ i, 0 < σ i) (z : E 1)
    (ℓ : ↥(rangeS (scDeriv U (r R) z)) →L[ℝ] F 0) :
    ℓ ∈ (linSumModel U R fh sh σ z).support ↔ ∃ i, sh i (E.toBase 1 z) = fh (E.toBase 1 z) ∧
      linAt U R (fun y => fh y - sh i y) z = ℓ := by
  rw [Finsupp.mem_support_iff, linSumModel_apply]
  constructor
  · intro h
    by_contra hne
    exact h (Finset.sum_eq_zero fun i _ => if_neg fun hi => hne ⟨i, hi⟩)
  · rintro ⟨i, hi⟩ h0
    have := (Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ i)
    rw [if_pos hi] at this
    exact (hσ i).ne' this

end Copies

section CopiesSEP
variable {Asep : SEP.{0}}

open Classical in
theorem remark_15_1_2' {f : Asep.Obj → Asep.W} (hf : Asep.E.IsScFredholmSectionFunctor f)
    {Λ : Asep.W → ℚ≥0} {c : StrongBundleChart Asep.X.PObj Asep.P}
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z ∈ c.φ.model.O)
    (h0 : Λ (f (c.φ.symm (c.φ.model.E.toBase 1 z))) = 0) :
    linearizationIn c f Λ z = 0 := by
  rw [linearizationIn]
  split_ifs with h
  · have hspec := h.choose_spec.choose_spec.choose_spec.choose_spec
    set y := c.φ.model.E.toBase 1 z
    have hsec : IsSection Asep.P f := hf.1.1.1
    have hK : (y, c.principal f y) ∈ c.K := c.principal_mem_K hsec hz
    have hw : c.toPartialEquiv.symm (y, c.principal f y) = f (c.φ.symm y) := by
      rw [← c.apply_section hsec hz]
      exact c.toPartialEquiv.left_inv (c.mem_source_of_proj (by
        rw [hsec]; exact c.φ.symm_mapsTo hz))
    refine remark_model' _ _ hspec.1.1 z ?_
    rw [hspec.1.count_eq hspec.2 hz, if_pos hK, hw, h0]
  · rfl

theorem linearization_eq_zero' {f : Asep.Obj → Asep.W} (hf : Asep.E.IsScFredholmSectionFunctor f)
    {Λ : Asep.W → ℚ≥0} {x : Asep.X.PObj.Level 1} (h0 : Λ (f (Asep.X.PObj.levelVal 1 x)) = 0) :
    linearization f Λ x = 0 := by
  classical
  rw [linearization]
  split_ifs with h
  · set d := h.some
    set y := Asep.X.PObj.levelVal 1 x
    have hsec : IsSection Asep.P f := hf.1.1.1
    have hyO : d.c.φ y ∈ d.c.φ.model.O := d.c.φ.mapsTo_model _ d.mem
    have ha : d.c.φ.model.E.toBase 1 (levelLift d.c.φ 1 y) = d.c.φ y :=
      Asep.X.PObj.toBase_levelLift d.c.isChart d.mem (levelVal_mem x)
    have hK : (d.c.φ y, d.c.principal f (d.c.φ y)) ∈ d.c.K := d.c.principal_mem_K hsec hyO
    have hw : d.c.toPartialEquiv.symm (d.c.φ y, d.c.principal f (d.c.φ y)) = f y := by
      rw [← d.c.apply_section' hsec d.mem]
      exact d.c.toPartialEquiv.left_inv (d.c.mem_source_of_proj (by rw [hsec]; exact d.mem))
    have hcount := d.rep.count_eq d.sub hyO (d.c.principal f (d.c.φ y))
    rw [if_pos hK, hw, h0] at hcount
    have hnone : ∀ i, d.c.principal (d.s i) (d.c.φ y) ≠ d.c.principal f (d.c.φ y) :=
      fun i hi => by
        have := (Finset.sum_eq_zero_iff.1 hcount) i (Finset.mem_univ i)
        rw [if_pos hi] at this
        exact (d.rep.1 i).ne' this
    change linSumModelMap _ _ _ _ _ _ _ = 0
    unfold linSumModelMap
    refine Finset.sum_eq_zero fun i _ => if_neg ?_
    rw [ha]; exact hnone i
  · rfl

end CopiesSEP

/-- `B ⇒ A`, by proving `A` outright (the hypothesis is not used: `A` covers arbitrary `Λ`). -/
theorem B_to_A : B → A := fun _ =>
  ⟨@linearization_eq_zero', @remark_15_1_2', @remark_model', @mem_support'⟩

#rt_check RoundTrip.V15_3.A_to_B [Polyfold.SBLocalization.linearization_eq_zero,
  Polyfold.SBLocalization.remark_15_1_2, Polyfold.Linearization15.remark_15_1_2_model,
  Polyfold.Linearization15.mem_support_linSumModel_iff]
#rt_check RoundTrip.V15_3.B_to_A [Polyfold.SBLocalization.linearization_eq_zero,
  Polyfold.SBLocalization.remark_15_1_2, Polyfold.Linearization15.remark_15_1_2_model,
  Polyfold.Linearization15.mem_support_linSumModel_iff]
#rt_check RoundTrip.V15_3.main_A_to_B [Polyfold.SBLocalization.linearization_eq_zero,
  Polyfold.SBLocalization.remark_15_1_2, Polyfold.Linearization15.remark_15_1_2_model,
  Polyfold.Linearization15.mem_support_linSumModel_iff]
#rt_check RoundTrip.V15_3.main_B_to_A_multisection [Polyfold.SBLocalization.linearization_eq_zero,
  Polyfold.SBLocalization.remark_15_1_2, Polyfold.Linearization15.remark_15_1_2_model,
  Polyfold.Linearization15.mem_support_linSumModel_iff]
#rt_overlap RoundTrip.V15_3.B_to_A [Polyfold.SBLocalization.linearization_eq_zero,
  Polyfold.SBLocalization.remark_15_1_2, Polyfold.Linearization15.remark_15_1_2_model,
  Polyfold.Linearization15.mem_support_linSumModel_iff]

end RoundTrip.V15_3
