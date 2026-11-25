import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V12_32

/-! Round trip for V12_32 (2021 Theorem 12.2.11, p. 577: reflexive auxiliary norms).

The item lists `theorem_12_2_11` (the three clauses), its clauses `theorem_12_2_11_exists`,
`theorem_12_2_11_mul`, `theorem_12_2_11_sandwich`, and the proof's steps `mixedLscAt_avgNorm`,
`mixedLscAt_transNorm`, `mixedLscAt_glueNorm`, `isReflexiveAuxNorm_glueNorm`.  `A` is the
conjunction of their types at universe `0` (`.{0, 0}` for the gluing lemmas: index type in `Type`).

* `A_to_B`: `theorem_12_2_11` is `B` (hypotheses in the other order; `B`'s pullback instance
  unused).
* `B_to_A`: `theorem_12_2_11`, `_exists` and `_sandwich` from `B` (the pullback instance from
  `StrongBundle.paracompactSpace_pullback`).  `theorem_12_2_11_mul` carries neither reflexive
  fibres nor paracompactness, so it does not follow from `B`'s second clause; it is the non-item
  `remark_12_2_12_1`.  The four proof steps are re-proved outright by copying the project's
  proofs (non-item lemmas: `mixedLscAt_comp_actOne`, `mixedLscAt_finset_sum`,
  `MixedLscAt.mul_comp`, `transNorm_eq_of`, `isAuxNorm_glueNorm`, ...).
-/

namespace RoundTrip.V12_32
open Polyfold
open Set Filter Topology Function TopologicalSpace

universe u

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.theorem_12_2_11.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.theorem_12_2_11_exists.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.theorem_12_2_11_mul.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.theorem_12_2_11_sandwich.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.mixedLscAt_avgNorm.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.mixedLscAt_transNorm.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.mixedLscAt_glueNorm.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isReflexiveAuxNorm_glueNorm.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.theorem_12_2_11.{0}, @Polyfold.EpStrongBundle.theorem_12_2_11_exists.{0}, @Polyfold.EpStrongBundle.theorem_12_2_11_mul.{0}, @Polyfold.EpStrongBundle.theorem_12_2_11_sandwich.{0}, @Polyfold.EpStrongBundle.mixedLscAt_avgNorm.{0}, @Polyfold.EpStrongBundle.mixedLscAt_transNorm.{0}, @Polyfold.EpStrongBundle.mixedLscAt_glueNorm.{0, 0}, @Polyfold.EpStrongBundle.isReflexiveAuxNorm_glueNorm.{0, 0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h, -⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ E hB hX
  exact h E hX hB

/-! ### The proof's steps, re-proved outright (the project's proofs, copied) -/

section Glue
open Polyfold.EpStrongBundle

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

variable (E : EpStrongBundle X B)

theorem mixedLscAt_avgNorm' (hB : B.HasReflexiveFibers) {x : Obj} (R : X.NaturalRep x)
    {M : B.One → ℝ} (hM : ∀ y : B.One, P (B.oneVal y) ∈ R.U → B.MixedLscAt M y) {y : B.One}
    (hy : P (B.oneVal y) ∈ R.U) : B.MixedLscAt (E.avgNorm R M) y := by
  classical
  have := Fintype.ofFinite (X.Isotropy x)
  have hsum : ∀ w, E.avgNorm R M w =
      (Nat.card (X.Isotropy x) : ℝ)⁻¹ * ∑ g, M (E.actOne (R.Γ g) w) := fun w => by
    rw [avgNorm, finsum_eq_sum_of_fintype]
  have h : B.MixedLscAt
      (fun w => (Nat.card (X.Isotropy x) : ℝ)⁻¹ * ∑ g, M (E.actOne (R.Γ g) w)) y :=
    (StrongBundle.mixedLscAt_finset_sum (M := fun g w => M (E.actOne (R.Γ g) w)) Finset.univ
      fun g _ => E.mixedLscAt_comp_actOne hB R.isOpen_U (R.isScSmoothOn_Γ g)
        (fun z hz => R.src_Γ g z hz) hy (hM _ (E.actOne_Γ_mem R g hy))).const_mul
      (inv_nonneg.2 (Nat.cast_nonneg _))
  exact h.congr isOpen_univ (mem_univ _) fun w _ => (hsum w).symm

variable {E}

theorem mixedLscAt_transNorm' (hB : B.HasReflexiveFibers) {x : Obj} {R : X.NaturalRep x}
    {M : B.One → ℝ} (hinv : ∀ g w, P (B.oneVal w) ∈ R.U → M (E.actOne (R.Γ g) w) = M w)
    (hM : ∀ y : B.One, P (B.oneVal y) ∈ R.U → B.MixedLscAt M y) {y : B.One}
    (hy : P (B.oneVal y) ∈ X.satSet R.U) : B.MixedLscAt (E.transNorm R M) y := by
  have hφs := X.src_selMor R.U (P (B.oneVal y))
  have hφt := X.tgt_selMor_mem hy
  obtain ⟨T, Vs, ρ, hφT, hρ⟩ := X.isLocalScDiffeo_src (X.selMor R.U (P (B.oneVal y)))
  have hρs : ∀ z ∈ Vs, X.src (ρ z) = z := fun z hz => hρ.right_inv z hz
  set S := Vs ∩ (X.tgt ∘ ρ) ⁻¹' R.U with hS
  have hSo : IsOpen S := (X.continuous_tgt.comp_continuousOn
    hρ.isScSmoothOn_inv.continuousOn).isOpen_inter_preimage hρ.isOpen_target R.isOpen_U
  have hy0 : P (B.oneVal y) ∈ S := by
    have h1 := hρ.mapsTo hφT
    rw [hφs] at h1
    refine ⟨h1, ?_⟩
    change X.tgt (ρ (P (B.oneVal y))) ∈ R.U
    have h2 := hρ.left_inv _ hφT
    rw [hφs] at h2
    rw [h2]; exact hφt
  have hc : B.MixedLscAt (M ∘ E.actOne ρ) y :=
    E.mixedLscAt_comp_actOne hB hρ.isOpen_target hρ.isScSmoothOn_inv hρs hy0.1
      (hM _ (by rw [E.P_actOne (hρs _ hy0.1)]; exact hy0.2))
  exact hc.congr hSo hy0 fun w hw => (transNorm_eq_of hinv (hρs _ hw.1) hw.2).symm

end Glue

section Glue'
open Polyfold.EpStrongBundle

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  {E : EpStrongBundle X B}

theorem mixedLscAt_glueNorm' {ι : Type*} {U : ι → Set Obj}
    {β : PartitionOfUnity ι X.OrbitSpace univ} {T : ι → B.One → ℝ} (hU : ∀ i, IsOpen (U i))
    (hsat : ∀ i, X.IsSaturated (U i)) (hβ : β.IsSubordinate fun i => X.π '' U i)
    (hT : ∀ i, B.IsLocalAuxNorm (U i) (T i))
    (hlsc : ∀ i (y : B.One), P (B.oneVal y) ∈ U i → B.MixedLscAt (T i) y) (y : B.One) :
    B.MixedLscAt (glueNorm β T) y := by
  classical
  set z := X.π (P (B.oneVal y)) with hz
  obtain ⟨n, hn, hfin⟩ := β.locallyFinite z
  set is := hfin.toFinset with his
  set O : Set Obj := X.π ⁻¹' interior n with hO
  have hOo : IsOpen O := isOpen_interior.preimage X.continuous_π
  have hyO : P (B.oneVal y) ∈ O := mem_interior_iff_mem_nhds.2 hn
  have hsupp : ∀ w : B.One, P (B.oneVal w) ∈ O →
      (support fun i => β i (X.π (P (B.oneVal w))) * T i w) ⊆ is := by
    intro w hw i hi
    simp only [his, Set.Finite.coe_toFinset]
    exact ⟨_, left_ne_zero_of_mul hi, interior_subset hw⟩
  have heq : ∀ w : B.One, P (B.oneVal w) ∈ O →
      (fun w => ∑ i ∈ is, β i (X.π (P (B.oneVal w))) * T i w) w = glueNorm β T w :=
    fun w hw => (finsum_eq_sum_of_support_subset _ (hsupp w hw)).symm
  have hterm : ∀ i ∈ is, B.MixedLscAt (fun w => β i (X.π (P (B.oneVal w))) * T i w) y := by
    intro i _
    by_cases hyU : P (B.oneVal y) ∈ U i
    · exact (hlsc i y hyU).mul_comp (g := fun x => β i (X.π x))
        ((β i).continuous.comp X.continuous_π).continuousAt (fun x => β.nonneg i _) (hU i) hyU
        fun w hw => (hT i).nonneg hw
    · refine StrongBundle.mixedLscAt_of_nonpos ?_ fun w => glue_term_nonneg hsat hβ hT i w
      rw [partition_eq_zero_of_not_mem hsat hβ hyU, zero_mul]
  exact (StrongBundle.mixedLscAt_finset_sum is hterm).congr hOo hyO heq

theorem isReflexiveAuxNorm_glueNorm' {ι : Type*} {U : ι → Set Obj}
    {β : PartitionOfUnity ι X.OrbitSpace univ} {T : ι → B.One → ℝ} (hU : ∀ i, IsOpen (U i))
    (hsat : ∀ i, X.IsSaturated (U i)) (hβ : β.IsSubordinate fun i => X.π '' U i)
    (hT : ∀ i, B.IsLocalAuxNorm (U i) (T i))
    (hinv : ∀ i (h k : B.One) (ψ : Mor) (hk : P (B.oneVal k) = X.src ψ),
      P (B.oneVal k) ∈ U i → B.oneVal h = E.μ ⟨(ψ, B.oneVal k), hk⟩ → T i h = T i k)
    (hlsc : ∀ i (y : B.One), P (B.oneVal y) ∈ U i → B.MixedLscAt (T i) y) :
    E.IsReflexiveAuxNorm (glueNorm β T) :=
  isReflexiveAuxNorm_of_mixedLscAt (isAuxNorm_glueNorm hU hsat hβ hT hinv)
    (mixedLscAt_glueNorm' hU hsat hβ hT hlsc)

end Glue'

theorem B_to_A : B → A := by
  intro hB
  have hmain : type_of% @Polyfold.EpStrongBundle.theorem_12_2_11.{0} := by
    intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E hX hR
    have := B.paracompactSpace_pullback X.PMor X.src
    exact hB Obj Mor X W P B E hR hX
  refine ⟨hmain, fun E hX hR => (hmain E hX hR).1, ?_, ?_, @mixedLscAt_avgNorm'.{0},
    @mixedLscAt_transNorm'.{0}, @mixedLscAt_glueNorm'.{0, 0}, @isReflexiveAuxNorm_glueNorm'.{0, 0}⟩
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E N hN f hf hf0 hfun
    exact EpStrongBundle.remark_12_2_12_1 hN hf hf0 hfun
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E hX hR N' hN'
    exact (hmain E hX hR).2.2 N' hN'

#rt_check RoundTrip.V12_32.A_to_B [Polyfold.EpStrongBundle.theorem_12_2_11,
  Polyfold.EpStrongBundle.theorem_12_2_11_exists,
  Polyfold.EpStrongBundle.theorem_12_2_11_mul,
  Polyfold.EpStrongBundle.theorem_12_2_11_sandwich,
  Polyfold.EpStrongBundle.mixedLscAt_avgNorm,
  Polyfold.EpStrongBundle.mixedLscAt_transNorm,
  Polyfold.EpStrongBundle.mixedLscAt_glueNorm,
  Polyfold.EpStrongBundle.isReflexiveAuxNorm_glueNorm]
#rt_check RoundTrip.V12_32.B_to_A [Polyfold.EpStrongBundle.theorem_12_2_11,
  Polyfold.EpStrongBundle.theorem_12_2_11_exists,
  Polyfold.EpStrongBundle.theorem_12_2_11_mul,
  Polyfold.EpStrongBundle.theorem_12_2_11_sandwich,
  Polyfold.EpStrongBundle.mixedLscAt_avgNorm,
  Polyfold.EpStrongBundle.mixedLscAt_transNorm,
  Polyfold.EpStrongBundle.mixedLscAt_glueNorm,
  Polyfold.EpStrongBundle.isReflexiveAuxNorm_glueNorm]
#rt_overlap RoundTrip.V12_32.B_to_A [Polyfold.EpStrongBundle.theorem_12_2_11,
  Polyfold.EpStrongBundle.theorem_12_2_11_exists,
  Polyfold.EpStrongBundle.theorem_12_2_11_mul,
  Polyfold.EpStrongBundle.theorem_12_2_11_sandwich,
  Polyfold.EpStrongBundle.mixedLscAt_avgNorm,
  Polyfold.EpStrongBundle.mixedLscAt_transNorm,
  Polyfold.EpStrongBundle.mixedLscAt_glueNorm,
  Polyfold.EpStrongBundle.isReflexiveAuxNorm_glueNorm]

end RoundTrip.V12_32
