import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V14_37

set_option maxSynthPendingDepth 3

/-! Round trip for V14_37 (2021 Proposition 14.5.4, pp. 673–677, the transport of the local
extensions; 2017: Proposition 14.8).

`A` is the conjunction of the types of the 22 listed theorems at universe `0` (the definitions
`SuppInSat`, `bsec`, `tsec` are vocabulary).  `B` is on `SEP.{0}`.

Blind exposure: the writer of `B` had `#print`ed the project's `proposition_14_5_4_statement`.

* `A_to_B`: from the data of `B` (`C`, cut-offs `β` with `C.BetaSpec β`, local extensions `sh`)
  we build a `TransportInput` over `C.toZData.toZSetup` (`transportInputOf`, the fields as in the
  project's `ZConcrete.transportInput`, with `B`'s `sh` in place of the chosen `localExt`), and
  `SuppInSat` from `tsupport β_a ⊆ saturation V̂_a`.  The sections are `T.tsec a`.  All six
  clauses of `B` come from conjuncts of `A`: sc⁺ (`isScPlusSectionOn_tsec`), equivariance
  (`tsec_equivariant`), (1) (`tsec_of_arc` on the trivial arc, `bsec_eq`), (2) (from (1),
  `sectionSmul_of_eq_zero` and `closure_support_β`), (3) (`tsec_boundary`), (4) (`tsec_compat`
  with `rel_of_sat`), (5) (`tsec_of_pairs`, `bsec_eq`), (6) (`tsec_of_not_reach`).
* `main_to_B5`: the main conjunct `TransportInput.proposition_14_5_4` alone gives clauses
  (1)–(5) of `B` (clause (5) from (1) and (4)), not (6).  Clause (6) (`s̃ = 0` at points of `V̂_b`
  not reached from `V̂_a`) is part of the text's statement ("are `0` where no such `φ` exists");
  in `A` it is the conjunct `tsec_of_not_reach` about the explicit `tsec`, while the main
  conjunct only asserts existence of some sections with (1)–(4).
* `B_to_A` is not proved: `A`'s statements are about an arbitrary `TransportInput` over an
  arbitrary `ZSetup` (any `β` with `SuppInSat`, any `ŝ`), while `B` only covers the data of
  §14.3 (`ZConcrete`) with `β` from Lemma 14.5.1 under tameness, paracompactness and partitions
  of unity; the helper conjuncts (`IndexCorr.*`, `sectionSmul_*`, `src_mem_boundary`, the `bsec`
  and `tsec` lemmas) are statements about the project's construction, not consequences of `B`.
-/

namespace RoundTrip.V14_37
open Polyfold Polyfold.SBLocalization

/-- The project's statement at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.IndexCorr.exists_pairs_left.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IndexCorr.sat_of_pairs.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IndexCorr.rel_of_sat.{0}) ∧
  (type_of% @Polyfold.SBLocalization.sectionSmul_congr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.sectionSmul_of_eq_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.src_mem_boundary.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.isSection_bsec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.bsec_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.bsec_of_eq_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.isScPlusSectionOn_bsec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.fibAct_bsec_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.tsec_of_arc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.tsec_of_not.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.arc_of_pairs.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.tsec_of_pairs.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.tsec_of_not_reach.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.isScPlusSectionOn_tsec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.tsec_equivariant.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.tsec_compat.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.tsec_boundary.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.proposition_14_5_4.{0}) ∧
  (type_of% @Polyfold.SBLocalization.TransportInput.suppInSat_of_zero.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.IndexCorr.exists_pairs_left.{0},
   @Polyfold.SBLocalization.IndexCorr.sat_of_pairs.{0},
   @Polyfold.SBLocalization.IndexCorr.rel_of_sat.{0},
   @Polyfold.SBLocalization.sectionSmul_congr.{0},
   @Polyfold.SBLocalization.sectionSmul_of_eq_zero.{0},
   @Polyfold.SBLocalization.src_mem_boundary.{0},
   @Polyfold.SBLocalization.TransportInput.isSection_bsec.{0},
   @Polyfold.SBLocalization.TransportInput.bsec_eq.{0},
   @Polyfold.SBLocalization.TransportInput.bsec_of_eq_zero.{0},
   @Polyfold.SBLocalization.TransportInput.isScPlusSectionOn_bsec.{0},
   @Polyfold.SBLocalization.TransportInput.fibAct_bsec_eq.{0},
   @Polyfold.SBLocalization.TransportInput.tsec_of_arc.{0},
   @Polyfold.SBLocalization.TransportInput.tsec_of_not.{0},
   @Polyfold.SBLocalization.TransportInput.arc_of_pairs.{0},
   @Polyfold.SBLocalization.TransportInput.tsec_of_pairs.{0},
   @Polyfold.SBLocalization.TransportInput.tsec_of_not_reach.{0},
   @Polyfold.SBLocalization.TransportInput.isScPlusSectionOn_tsec.{0},
   @Polyfold.SBLocalization.TransportInput.tsec_equivariant.{0},
   @Polyfold.SBLocalization.TransportInput.tsec_compat.{0},
   @Polyfold.SBLocalization.TransportInput.tsec_boundary.{0},
   @Polyfold.SBLocalization.TransportInput.proposition_14_5_4.{0},
   @Polyfold.SBLocalization.TransportInput.suppInSat_of_zero.{0}⟩

/-- `IndexCorr.sat_of_pairs`, re-proved (that lemma is a conjunct of `A`). -/
theorem sat_of_pairs' {α β : Type} {R : α → β → Prop} (τ : IndexCorr α β)
    (h : ∀ i j, τ.Pairs i j → R i j) : τ.Sat R :=
  IndexCorr.ind (p := fun τ => (∀ i j, τ.Pairs i j → R i j) → τ.Sat R)
    (fun _ h k => h _ _ ⟨k, rfl, rfl⟩) τ h

section Glue

variable {A : SEP.{0}} {T : BoundaryStructuredTuple A} {P : P5Nbhds T} {E : CorrExtension T P}
  {Q : P.P6Nbhds} (C : ZConcrete E Q) {β : A.Obj → A.Obj → ℝ} (hβ : C.BetaSpec β)
  (sh : (a : A.Obj) → C.toZData.I a → A.Obj → A.W)
  (hsh : ∀ a ∈ C.toZData.A, IsLocalExtension C a (sh a))

/-- The input of Proposition 14.5.4 from the data of `B` (as `ZConcrete.transportInput`, with
`B`'s local extensions). -/
noncomputable def transportInputOf : TransportInput A C.toZData.toZSetup where
  isOpen_V := C.isOpen_Vh
  proper a ha := ZConcrete.isProper a (C.A_subset ha)
  locallyConstant a ha b hb φ hφ :=
    (C.toZData.locallyConstant a ha b hb φ hφ.1 hφ.2).filter_mono nhdsWithin_le_nhds
  β := β
  isScSmooth_β := hβ.1
  β_tgt := hβ.2.1
  closure_support_β a ha :=
    closure_support_subset (Q.nbhdObj a) (C.toZData.V_subset a ha) (C.mapsTo_Vh a ha)
      (hβ.2.2.1 a ha)
  s0 := C.toZSections.s
  s0_compat a ha b hb φ hφ :=
    sat_of_pairs' _ fun i j hp =>
      C.toZSections.compat a ha b hb φ hφ.1 hφ.2.1 i j hp
  sh := sh
  isScPlusSectionOn_sh a ha i := (hsh a ha).1 i
  sh_equivariant a ha g i y hy := (hsh a ha).2.1 g i y hy
  sh_boundary a ha i y hy := (hsh a ha).2.2.1 i y hy
  sh_zRel a ha z hz i i' h := (hsh a ha).2.2.2 z hz i i' h

theorem suppInSat_transportInputOf : (transportInputOf C hβ sh hsh).SuppInSat :=
  fun a ha _ hy => exists_mor_of_ne_zero (hβ.2.2.1 a ha) hy

end Glue

theorem A_to_B (hA : A) : B := by
  obtain ⟨-, -, h2, -, h4, -, h6, h7, -, -, -, h11, -, -, h14, h15, h16, h17, h18, h19, -, -⟩ := hA
  intro A _ _ _ T P E Q C β hβ sh hsh a ha
  set TI := transportInputOf C hβ sh hsh with hTI
  have hS := suppInSat_transportInputOf C hβ sh hsh
  -- (1)
  have h1 : ∀ i, ∀ y ∈ C.toZData.V a,
      TI.tsec a a i y = Polyfold.sectionSmul A.P (β a) (sh a i) y := by
    intro i y hy
    have e := h11 TI (EpGroupoid.ZSetup.Arc.nil ha hy i)
    rw [A.X.tgt_unit, A.X.src_unit, SBLocalization.fibAct_unit (h6 TI a i y)] at e
    rw [e, h7 TI ha i hy]
    rfl
  refine ⟨TI.tsec a, fun b hb j => h16 TI ha hb j,
    fun b hb g j y hy => h17 TI hb g j hy, h1, fun i => ?_,
    fun b hb j y hy => h19 TI hS ha hb j hy,
    fun b hb b' hb' φ hφ j j' hp => h2 (h18 TI hb hb' hφ) hp,
    fun b hb φ hφ i j hp => ?_, fun b hb j y hy hn => h15 TI hn⟩
  · -- (2)
    refine (closure_mono ?_).trans (TI.closure_support_β a ha)
    rintro y ⟨hy, hne⟩
    refine ⟨C.toZData.V_subset a ha hy, fun h0 => hne ?_⟩
    rw [h1 i y hy]
    exact h4 ((hsh a ha).1 i |>.1 y hy) h0
  · -- (5)
    rw [h14 TI ha hb hφ.1 hφ.2 hp, h7 TI ha i hφ.1]
    rfl

/-- Clauses (1)–(5) of `B` (all but the vanishing clause (6)). -/
def IsTransport5 {A : SEP.{0}} {T : BoundaryStructuredTuple A} {P : P5Nbhds T}
    {E : CorrExtension T P} {Q : P.P6Nbhds} (C : ZConcrete E Q) (β : A.Obj → A.Obj → ℝ)
    (sh : (a : A.Obj) → C.toZData.I a → A.Obj → A.W) (a : A.Obj)
    (st : (b : A.Obj) → C.toZData.I b → A.Obj → A.W) : Prop :=
  (∀ b ∈ C.toZData.A, ∀ j, IsScPlusSectionOn A (st b j) (C.toZData.V b)) ∧
  (∀ b ∈ C.toZData.A, ∀ (g : A.X.Isotropy b) (j : C.toZData.I b), ∀ y ∈ C.toZData.V b,
    st b (g • j) ((C.toZData.nbhd b).rep.Φ g y) =
      fibAct ((C.toZData.nbhd b).rep.Γ g y) (st b j y)) ∧
  (∀ i, ∀ y ∈ C.toZData.V a, st a i y = sectionSmul A.P (β a) (sh a i) y) ∧
  (∀ i, closure {y | y ∈ C.toZData.V a ∧ st a i y ≠ fiberZero A.P y} ⊆ C.toZData.V a) ∧
  (∀ b ∈ C.toZData.A, ∀ j, ∀ y ∈ C.toZData.V b ∩ A.X.PObj.boundary,
    st b j y = sectionSmul A.P (β a) (C.toZSections.s b j) y) ∧
  (∀ b ∈ C.toZData.A, ∀ b' ∈ C.toZData.A,
    ∀ φ ∈ A.X.morBetween (C.toZData.V b) (C.toZData.V b'), ∀ j j',
      (C.toZData.τ b b' φ).Pairs j j' → st b' j' (A.X.tgt φ) = fibAct φ (st b j (A.X.src φ))) ∧
  (∀ b ∈ C.toZData.A, ∀ φ ∈ A.X.morBetween (C.toZData.V a) (C.toZData.V b), ∀ i j,
    (C.toZData.τ a b φ).Pairs i j →
      st b j (A.X.tgt φ) = fibAct φ (sectionSmul A.P (β a) (sh a i) (A.X.src φ)))

/-- `B` without the vanishing clause (6). -/
def B5 : Prop :=
  ∀ (A : SEP.{0}), A.X.IsTame → A.X.HasParacompactOrbitSpace →
    A.X.PObj.AdmitsScPartitionsOfUnity →
    ∀ (T : BoundaryStructuredTuple A) (P : P5Nbhds T) (E : CorrExtension T P) (Q : P.P6Nbhds)
      (C : ZConcrete E Q) (β : A.Obj → A.Obj → ℝ), C.BetaSpec β →
    ∀ sh : (a : A.Obj) → C.toZData.I a → A.Obj → A.W,
      (∀ a ∈ C.toZData.A, IsLocalExtension C a (sh a)) →
      ∀ a ∈ C.toZData.A, ∃ st : (b : A.Obj) → C.toZData.I b → A.Obj → A.W,
        IsTransport5 C β sh a st

/-- The main conjunct gives (1)–(5) of `B` (with `(4)` turned into pairs by
`IndexCorr.ind`, re-proved here, and (5) from (1) and (4)). -/
theorem main_to_B5
    (hM : type_of% @Polyfold.SBLocalization.TransportInput.proposition_14_5_4.{0}) : B5 := by
  intro A _ _ _ T P E Q C β hβ sh hsh a ha
  set TI := transportInputOf C hβ sh hsh
  obtain ⟨st, hsc, heq, h1, h2, h3, h4⟩ := hM TI (suppInSat_transportInputOf C hβ sh hsh) a ha
  have h4' : ∀ b ∈ C.toZData.A, ∀ b' ∈ C.toZData.A,
      ∀ φ ∈ A.X.morBetween (C.toZData.V b) (C.toZData.V b'), ∀ j j',
        (C.toZData.τ b b' φ).Pairs j j' →
          st b' j' (A.X.tgt φ) = fibAct φ (st b j (A.X.src φ)) := by
    intro b hb b' hb' φ hφ j j' hp
    have hs := h4 b hb b' hb' φ hφ
    exact IndexCorr.ind (p := fun τ => τ.Sat (fun j j' =>
        st b' j' (A.X.tgt φ) = fibAct φ (st b j (A.X.src φ))) → τ.Pairs j j' →
        st b' j' (A.X.tgt φ) = fibAct φ (st b j (A.X.src φ)))
      (fun _ h ⟨k, h1, h2⟩ => h1 ▸ h2 ▸ h k) _ hs hp
  refine ⟨st, hsc, heq, h1, fun i => ?_, h3, h4', fun b hb φ hφ i j hp => ?_⟩
  · obtain ⟨K, hK, hKV, hK0⟩ := h2 i
    refine (closure_minimal ?_ hK).trans hKV
    rintro y ⟨hy, hne⟩
    by_contra hyK
    exact hne (hK0 y hy hyK)
  · rw [h4' a ha b hb φ hφ i j hp, h1 i _ hφ.1]
    rfl

theorem A_to_B5 (hA : A) : B5 := main_to_B5 hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

#rt_check RoundTrip.V14_37.A_to_B [Polyfold.SBLocalization.IndexCorr.exists_pairs_left,
  Polyfold.SBLocalization.IndexCorr.sat_of_pairs,
  Polyfold.SBLocalization.IndexCorr.rel_of_sat,
  Polyfold.SBLocalization.sectionSmul_congr,
  Polyfold.SBLocalization.sectionSmul_of_eq_zero,
  Polyfold.SBLocalization.src_mem_boundary,
  Polyfold.SBLocalization.TransportInput.isSection_bsec,
  Polyfold.SBLocalization.TransportInput.bsec_eq,
  Polyfold.SBLocalization.TransportInput.bsec_of_eq_zero,
  Polyfold.SBLocalization.TransportInput.isScPlusSectionOn_bsec,
  Polyfold.SBLocalization.TransportInput.fibAct_bsec_eq,
  Polyfold.SBLocalization.TransportInput.tsec_of_arc,
  Polyfold.SBLocalization.TransportInput.tsec_of_not,
  Polyfold.SBLocalization.TransportInput.arc_of_pairs,
  Polyfold.SBLocalization.TransportInput.tsec_of_pairs,
  Polyfold.SBLocalization.TransportInput.tsec_of_not_reach,
  Polyfold.SBLocalization.TransportInput.isScPlusSectionOn_tsec,
  Polyfold.SBLocalization.TransportInput.tsec_equivariant,
  Polyfold.SBLocalization.TransportInput.tsec_compat,
  Polyfold.SBLocalization.TransportInput.tsec_boundary,
  Polyfold.SBLocalization.TransportInput.proposition_14_5_4,
  Polyfold.SBLocalization.TransportInput.suppInSat_of_zero]
#rt_check RoundTrip.V14_37.main_to_B5 [Polyfold.SBLocalization.IndexCorr.exists_pairs_left,
  Polyfold.SBLocalization.IndexCorr.sat_of_pairs,
  Polyfold.SBLocalization.IndexCorr.rel_of_sat,
  Polyfold.SBLocalization.sectionSmul_congr,
  Polyfold.SBLocalization.sectionSmul_of_eq_zero,
  Polyfold.SBLocalization.src_mem_boundary,
  Polyfold.SBLocalization.TransportInput.isSection_bsec,
  Polyfold.SBLocalization.TransportInput.bsec_eq,
  Polyfold.SBLocalization.TransportInput.bsec_of_eq_zero,
  Polyfold.SBLocalization.TransportInput.isScPlusSectionOn_bsec,
  Polyfold.SBLocalization.TransportInput.fibAct_bsec_eq,
  Polyfold.SBLocalization.TransportInput.tsec_of_arc,
  Polyfold.SBLocalization.TransportInput.tsec_of_not,
  Polyfold.SBLocalization.TransportInput.arc_of_pairs,
  Polyfold.SBLocalization.TransportInput.tsec_of_pairs,
  Polyfold.SBLocalization.TransportInput.tsec_of_not_reach,
  Polyfold.SBLocalization.TransportInput.isScPlusSectionOn_tsec,
  Polyfold.SBLocalization.TransportInput.tsec_equivariant,
  Polyfold.SBLocalization.TransportInput.tsec_compat,
  Polyfold.SBLocalization.TransportInput.tsec_boundary,
  Polyfold.SBLocalization.TransportInput.proposition_14_5_4,
  Polyfold.SBLocalization.TransportInput.suppInSat_of_zero]
#rt_overlap RoundTrip.V14_37.A_to_B [Polyfold.SBLocalization.IndexCorr.exists_pairs_left,
  Polyfold.SBLocalization.IndexCorr.sat_of_pairs,
  Polyfold.SBLocalization.IndexCorr.rel_of_sat,
  Polyfold.SBLocalization.sectionSmul_congr,
  Polyfold.SBLocalization.sectionSmul_of_eq_zero,
  Polyfold.SBLocalization.src_mem_boundary,
  Polyfold.SBLocalization.TransportInput.isSection_bsec,
  Polyfold.SBLocalization.TransportInput.bsec_eq,
  Polyfold.SBLocalization.TransportInput.bsec_of_eq_zero,
  Polyfold.SBLocalization.TransportInput.isScPlusSectionOn_bsec,
  Polyfold.SBLocalization.TransportInput.fibAct_bsec_eq,
  Polyfold.SBLocalization.TransportInput.tsec_of_arc,
  Polyfold.SBLocalization.TransportInput.tsec_of_not,
  Polyfold.SBLocalization.TransportInput.arc_of_pairs,
  Polyfold.SBLocalization.TransportInput.tsec_of_pairs,
  Polyfold.SBLocalization.TransportInput.tsec_of_not_reach,
  Polyfold.SBLocalization.TransportInput.isScPlusSectionOn_tsec,
  Polyfold.SBLocalization.TransportInput.tsec_equivariant,
  Polyfold.SBLocalization.TransportInput.tsec_compat,
  Polyfold.SBLocalization.TransportInput.tsec_boundary,
  Polyfold.SBLocalization.TransportInput.proposition_14_5_4,
  Polyfold.SBLocalization.TransportInput.suppInSat_of_zero]

end RoundTrip.V14_37
