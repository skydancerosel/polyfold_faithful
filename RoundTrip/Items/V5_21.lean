import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_21

/-!
Round trip for V5_21 (`Γ^{+,1}_U(P)`, the allowable sections, and the metric `ρ`, §5.3 p. 174).
Refreshed 2026-11-02: the comparison row now cites the metric `ρ` (`StrongBundle.allowableDist`,
`StrongBundle.allowableMetric`) and the (in)completeness results.

A = `StrongBundle.allowableDist_le_iff` ∧ `TrivialBundle.not_completeSpace_allowableSections` ∧
`StrongBundle.completeSpace_allowableSections_empty` ∧
`TrivialBundle.completeSpace_allowableSections_point` (universes at `0`); `allowableSections`,
`sectionDistAt`, `allowableDist`, `allowableMetric` are vocabulary.

* B (1): `allowableSections N U = Gamma1 Bd N U` — proved outright (`B1_holds`).
* The project's pointwise distance `sectionDistAt` is B's `fibDist` on sc⁺-sections
  (`sectionDistAt_eq_fibDist`), so B's `ρ` is the project's `allowableDist` (`rho_eq`), and B's
  "complete" is `CompleteSpace` of the project's metric space `AllowableSpace U hN`
  (`isRhoComplete_of_completeSpace`, `completeSpace_of_isRhoComplete`).
* B (2): `ρ` is a metric on `Γ^{+,1}_U(P)` for every auxiliary norm — proved outright
  (`B2_holds`).
* B (3) ("not complete in general") — proved from A's `not_completeSpace_allowableSections`
  (the trivial bundle `ℝ × ℝ → ℝ`, `N(x, v) = |v|`, `U = ℝ`).  So `A ⇒ B` holds now.
* A's two complete cases (`U = ∅`; `X` a point) refute the literal universal reading
  `BUniversal` (`not_BUniversal`), confirming the blind reading "not complete in general".
* `B ⇒ A` fails: B's (3) is existential, A's `not_completeSpace_allowableSections` names one
  bundle, norm and `U`; and the complete case over a point (`completeSpace_allowableSections_point`)
  is not in B.  Both need the project's constructions to be re-done.
-/

namespace RoundTrip.V5_21
open Polyfold

/-- The project's statement, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.StrongBundle.allowableDist_le_iff.{0, 0} ∧
  type_of% @Polyfold.TrivialBundle.not_completeSpace_allowableSections ∧
  type_of% @Polyfold.StrongBundle.completeSpace_allowableSections_empty.{0, 0} ∧
  type_of% @Polyfold.TrivialBundle.completeSpace_allowableSections_point

theorem A_holds : A :=
  ⟨@Polyfold.StrongBundle.allowableDist_le_iff.{0, 0},
    @Polyfold.TrivialBundle.not_completeSpace_allowableSections,
    @Polyfold.StrongBundle.completeSpace_allowableSections_empty.{0, 0},
    @Polyfold.TrivialBundle.completeSpace_allowableSections_point⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- B (1): the project's `Γ^{+,1}_U(P)` is B's. -/
theorem allowable_eq (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (U : Set X) :
    Bd.allowableSections N U = Gamma1 Bd N U := by
  ext s
  constructor
  · rintro ⟨hs, hsupp, hN⟩
    exact ⟨hs, hsupp, fun x => ⟨hs.mem_oneSet x, hN x _⟩⟩
  · rintro ⟨hs, hsupp, hN⟩
    refine ⟨hs, hsupp, fun x hx => ?_⟩
    obtain ⟨_, h⟩ := hN x
    exact h

/-- The project's pointwise distance is B's `fibDist` on sc⁺-sections. -/
theorem sectionDistAt_eq_fibDist {Bd : StrongBundle PX P} (N : Bd.One → ℝ) {s s' : X → Y}
    (hs : Bd.IsScPlusSection s) (hs' : Bd.IsScPlusSection s') (x : X) :
    fibDist Bd N s s' x = Bd.sectionDistAt N hs hs' x := by
  unfold fibDist
  rw [dif_pos ⟨⟨hs.1 x, hs'.1 x⟩, ⟨hs.mem_oneSet x, hs'.mem_oneSet x⟩⟩]
  rfl

/-- The value of an sc⁺-section as a vector of `(Y_{0,1})_x`. -/
def vec {Bd : StrongBundle PX P} {s : X → Y} (hs : Bd.IsScPlusSection s) (x : X) :
    Bd.oneFiber x :=
  ⟨⟨s x, hs.1 x⟩, hs.mem_oneSet x⟩

lemma fibDist_eq {Bd : StrongBundle PX P} (N : Bd.One → ℝ) {s s' : X → Y}
    (hs : Bd.IsScPlusSection s) (hs' : Bd.IsScPlusSection s') (x : X) :
    fibDist Bd N s s' x = N (Bd.toOne (vec hs x - vec hs' x)) :=
  sectionDistAt_eq_fibDist N hs hs' x

lemma fibNorm_sub_comm {Bd : StrongBundle PX P} {N : Bd.One → ℝ} (hN : Bd.IsAuxNorm N) {x : X}
    (v w : Bd.oneFiber x) : N (Bd.toOne (v - w)) = N (Bd.toOne (w - v)) := by
  rw [← neg_sub, ← neg_one_smul ℝ (w - v), (hN.fiber x).smul, abs_neg, abs_one, one_mul]

lemma fibNorm_sub_le {Bd : StrongBundle PX P} {N : Bd.One → ℝ} (hN : Bd.IsAuxNorm N) {x : X}
    (v w : Bd.oneFiber x) : N (Bd.toOne (v - w)) ≤ N (Bd.toOne v) + N (Bd.toOne w) := by
  have h := (hN.fiber x).add_le v (-w)
  rw [← sub_eq_add_neg] at h
  have h2 := (hN.fiber x).smul (-1) w
  rw [neg_one_smul, abs_neg, abs_one, one_mul] at h2
  rwa [h2] at h

lemma fibDist_nonneg {Bd : StrongBundle PX P} {N : Bd.One → ℝ} (hN : Bd.IsAuxNorm N)
    {s s' : X → Y} (hs : Bd.IsScPlusSection s) (hs' : Bd.IsScPlusSection s') (x : X) :
    0 ≤ fibDist Bd N s s' x := by
  rw [fibDist_eq N hs hs']; exact (hN.fiber x).nonneg _

lemma fibDist_le_two {Bd : StrongBundle PX P} {N : Bd.One → ℝ} (hN : Bd.IsAuxNorm N) {U : Set X}
    {s s' : X → Y} (h : s ∈ Gamma1 Bd N U) (h' : s' ∈ Gamma1 Bd N U) (x : X) :
    fibDist Bd N s s' x ≤ 2 := by
  rw [fibDist_eq N h.1 h'.1]
  refine (fibNorm_sub_le hN _ _).trans ?_
  obtain ⟨_, h1⟩ := h.2.2 x
  obtain ⟨_, h2⟩ := h'.2.2 x
  have e1 : N (Bd.toOne (vec h.1 x)) ≤ 1 := h1
  have e2 : N (Bd.toOne (vec h'.1 x)) ≤ 1 := h2
  linarith

/-- B (2): `ρ` is a metric on `Γ^{+,1}_U(P)`. -/
theorem isRhoMetric {Bd : StrongBundle PX P} {N : Bd.One → ℝ} (hN : Bd.IsAuxNorm N) (U : Set X) :
    IsRhoMetric Bd N U := by
  intro s hs s' hs' s'' hs''
  have bdd : ∀ {t t' : X → Y}, t ∈ Gamma1 Bd N U → t' ∈ Gamma1 Bd N U →
      BddAbove (Set.range (fibDist Bd N t t')) := fun ht ht' =>
    ⟨2, by rintro _ ⟨x, rfl⟩; exact fibDist_le_two hN ht ht' x⟩
  have nn : ∀ {t t' : X → Y}, t ∈ Gamma1 Bd N U → t' ∈ Gamma1 Bd N U →
      0 ≤ rho Bd N t t' := fun ht ht' =>
    Real.iSup_nonneg fun x => fibDist_nonneg hN ht.1 ht'.1 x
  refine ⟨bdd hs hs', nn hs hs', ?_, ?_, ?_, ?_⟩
  · refine le_antisymm (Real.iSup_nonpos fun x => ?_) (nn hs hs)
    rw [fibDist_eq N hs.1 hs.1, sub_self]
    exact ((hN.fiber x).map_zero).le
  · unfold rho
    congr 1
    funext x
    rw [fibDist_eq N hs.1 hs'.1, fibDist_eq N hs'.1 hs.1]
    exact fibNorm_sub_comm hN _ _
  · intro h0
    funext x
    have h1 : fibDist Bd N s s' x ≤ 0 := (le_ciSup (bdd hs hs') x).trans h0.le
    have h2 := fibDist_nonneg hN hs.1 hs'.1 x
    rw [fibDist_eq N hs.1 hs'.1] at h1 h2
    have h3 := (hN.fiber x).eq_zero _ (le_antisymm h1 h2)
    have h4 : vec hs.1 x = vec hs'.1 x := sub_eq_zero.1 h3
    exact congrArg (fun v : Bd.oneFiber x => ((v : P ⁻¹' {x}) : Y)) h4
  · refine Real.iSup_le (fun x => ?_) (add_nonneg (nn hs hs') (nn hs' hs''))
    have ht : fibDist Bd N s s'' x ≤ fibDist Bd N s s' x + fibDist Bd N s' s'' x := by
      rw [fibDist_eq N hs.1 hs''.1, fibDist_eq N hs.1 hs'.1, fibDist_eq N hs'.1 hs''.1]
      have := (hN.fiber x).add_le (vec hs.1 x - vec hs'.1 x) (vec hs'.1 x - vec hs''.1 x)
      rwa [sub_add_sub_cancel] at this
    exact ht.trans (add_le_add (le_ciSup (bdd hs hs') x) (le_ciSup (bdd hs' hs'') x))

/-- B's `ρ` is the project's `allowableDist` on allowable sections. -/
theorem rho_eq {Bd : StrongBundle PX P} (N : Bd.One → ℝ) {U : Set X}
    (s s' : Bd.allowableSections N U) :
    rho Bd N s.1 s'.1 = Bd.allowableDist N U s s' := by
  unfold rho StrongBundle.allowableDist
  congr 1
  funext x
  exact sectionDistAt_eq_fibDist N s.2.1 s'.2.1 x

lemma mem_allowable_iff {Bd : StrongBundle PX P} {N : Bd.One → ℝ} {U : Set X} {s : X → Y} :
    s ∈ Bd.allowableSections N U ↔ s ∈ Gamma1 Bd N U := by
  rw [allowable_eq]

/-- `CompleteSpace` of the project's `(Γ^{+,1}_U(P), ρ)` gives B's completeness. -/
theorem isRhoComplete_of_completeSpace {Bd : StrongBundle PX P} {N : Bd.One → ℝ}
    (hN : Bd.IsAuxNorm N) {U : Set X} (h : CompleteSpace (StrongBundle.AllowableSpace U hN)) :
    IsRhoComplete Bd N U := by
  intro u hu hcau
  have hu' : ∀ n, u n ∈ Bd.allowableSections N U := fun n => mem_allowable_iff.2 (hu n)
  let v : ℕ → StrongBundle.AllowableSpace U hN := fun n =>
    StrongBundle.AllowableSpace.mk hN ⟨u n, hu' n⟩
  have hv : CauchySeq v := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨K, hK⟩ := hcau ε hε
    refine ⟨K, fun m hm n hn => ?_⟩
    have e : dist (v m) (v n) = rho Bd N (u m) (u n) := (rho_eq N ⟨u m, hu' m⟩ ⟨u n, hu' n⟩).symm
    rw [e]; exact hK m hm n hn
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete hv
  refine ⟨s.sec.1, mem_allowable_iff.1 s.sec.2, fun ε hε => ?_⟩
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hs ε hε
  refine ⟨K, fun n hn => ?_⟩
  have e : dist (v n) s = rho Bd N (u n) s.sec.1 := (rho_eq N ⟨u n, hu' n⟩ s.sec).symm
  rw [← e]; exact hK n hn

/-- B's completeness gives `CompleteSpace` of the project's `(Γ^{+,1}_U(P), ρ)`. -/
theorem completeSpace_of_isRhoComplete {Bd : StrongBundle PX P} {N : Bd.One → ℝ}
    (hN : Bd.IsAuxNorm N) {U : Set X} (h : IsRhoComplete Bd N U) :
    CompleteSpace (StrongBundle.AllowableSpace U hN) := by
  refine Metric.complete_of_cauchySeq_tendsto fun v hv => ?_
  have hu : ∀ n, (v n).sec.1 ∈ Gamma1 Bd N U := fun n => mem_allowable_iff.1 (v n).sec.2
  have hcau : ∀ ε > 0, ∃ K : ℕ, ∀ m ≥ K, ∀ n ≥ K,
      rho Bd N (v m).sec.1 (v n).sec.1 < ε := by
    intro ε hε
    obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.1 hv ε hε
    refine ⟨K, fun m hm n hn => ?_⟩
    rw [rho_eq N (v m).sec (v n).sec]; exact hK m hm n hn
  obtain ⟨s, hs, hlim⟩ := h (fun n => (v n).sec.1) hu hcau
  have hs' : s ∈ Bd.allowableSections N U := mem_allowable_iff.2 hs
  refine ⟨StrongBundle.AllowableSpace.mk hN ⟨s, hs'⟩, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  obtain ⟨K, hK⟩ := hlim ε hε
  refine ⟨K, fun n hn => ?_⟩
  calc dist (v n) (StrongBundle.AllowableSpace.mk hN ⟨s, hs'⟩)
      = rho Bd N (v n).sec.1 s := (rho_eq N (v n).sec ⟨s, hs'⟩).symm
    _ < ε := hK n hn

end Glue

/-- B (1) holds. -/
theorem B1_holds : ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (U : Set X),
    Bd.allowableSections N U = Gamma1 Bd N U :=
  by intro X _ _ _ PX Y _ _ _ P _ _ Bd N U; exact allowable_eq Bd N U

/-- B (2) holds. -/
theorem B2_holds : ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (U : Set X),
    Bd.IsAuxNorm N → IsOpen U → IsRhoMetric Bd N U :=
  by intro X _ _ _ PX Y _ _ _ P _ _ Bd N U hN _; exact isRhoMetric hN U

/-- B (3) from A: on the trivial bundle `ℝ × ℝ → ℝ` with `N(x, v) = |v|` and `U = ℝ`,
`(Γ^{+,1}_U(P), ρ)` is not complete (A's `not_completeSpace_allowableSections`). -/
theorem B3_of_A (hA : A) :
    ¬ (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      (Bd : StrongBundle PX P) (N : Bd.One → ℝ) (U : Set X),
        Bd.IsAuxNorm N → IsOpen U → IsRhoComplete Bd N U) := by
  intro H
  exact hA.2.1 (completeSpace_of_isRhoComplete TrivialBundle.isAuxNorm_fibNorm
    (H _ _ (TrivialBundle.bundle 1 1) TrivialBundle.fibNorm Set.univ
      TrivialBundle.isAuxNorm_fibNorm isOpen_univ))

/-- **`A ⇒ B`**: clauses (1), (2) hold outright, clause (3) from A. -/
theorem A_to_B : A → B := fun hA => ⟨B1_holds, B2_holds, B3_of_A hA⟩

/-- A refutes the literal universal reading of "not complete" (the blind's `BUniversal`): for
`U = ∅` the space is a point (A's `completeSpace_allowableSections_empty`). -/
theorem not_BUniversal (hA : A) : ¬ BUniversal := fun H =>
  H _ _ (TrivialBundle.bundle 1 1) TrivialBundle.fibNorm ∅ TrivialBundle.isAuxNorm_fibNorm
    isOpen_empty (isRhoComplete_of_completeSpace TrivialBundle.isAuxNorm_fibNorm
      (hA.2.2.1 TrivialBundle.isAuxNorm_fibNorm))

/-! `B ⇒ A` is not proved: B's clause (3) only says that SOME `(Γ^{+,1}_U(P), ρ)` is not
complete, while A's `not_completeSpace_allowableSections` is about the trivial bundle `ℝ × ℝ → ℝ`,
`N(x, v) = |v|`, `U = ℝ` (the sequence of smooth graphs converging to `|x|/(2√(1+x²))`), and
`completeSpace_allowableSections_point` (complete over a point with finite-dimensional fibre) is
not in B.  `allowableDist_le_iff` and `completeSpace_allowableSections_empty` are elementary. -/

#rt_check RoundTrip.V5_21.A_to_B [Polyfold.StrongBundle.allowableDist_le_iff,
  Polyfold.TrivialBundle.not_completeSpace_allowableSections,
  Polyfold.StrongBundle.completeSpace_allowableSections_empty,
  Polyfold.TrivialBundle.completeSpace_allowableSections_point]
#rt_check RoundTrip.V5_21.B1_holds [Polyfold.StrongBundle.allowableDist_le_iff,
  Polyfold.TrivialBundle.not_completeSpace_allowableSections,
  Polyfold.StrongBundle.completeSpace_allowableSections_empty,
  Polyfold.TrivialBundle.completeSpace_allowableSections_point]
#rt_check RoundTrip.V5_21.B2_holds [Polyfold.StrongBundle.allowableDist_le_iff,
  Polyfold.TrivialBundle.not_completeSpace_allowableSections,
  Polyfold.StrongBundle.completeSpace_allowableSections_empty,
  Polyfold.TrivialBundle.completeSpace_allowableSections_point]
#rt_check RoundTrip.V5_21.not_BUniversal [Polyfold.StrongBundle.allowableDist_le_iff,
  Polyfold.TrivialBundle.not_completeSpace_allowableSections,
  Polyfold.StrongBundle.completeSpace_allowableSections_empty,
  Polyfold.TrivialBundle.completeSpace_allowableSections_point]

end RoundTrip.V5_21
