import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V12_4

/-! Round trip for V12_4 (2021 Theorem 12.2.2, p. 570: existence of auxiliary norms).

The item lists `theorem_12_2_2`, `SEP.theorem_12_2_2` and the proof's building blocks
`isLocalAuxNorm_avgNorm`, `avgNorm_actOne`, `isLocalAuxNorm_transNorm`, `transNorm_μ`,
`isAuxNorm_glueNorm` (with the definitions `avgNorm`, `transNorm`, `glueNorm` as vocabulary).
`A` is the conjunction of the seven theorem types, universes instantiated at `0`
(`isAuxNorm_glueNorm.{0, 0}`: the index type of the partition of unity in `Type`).

* `A_to_B`: `B`'s extra instance hypothesis `[ParacompactSpace (pullbackSpace P X.src)]` is unused;
  the first conjunct is `B`.
* `B_to_A`: the two forms of Theorem 12.2.2 from `B` (the pullback instance from
  `StrongBundle.paracompactSpace_pullback`; `SEP` unbundled).  The five building blocks are proof
  steps, not content of the theorem; they are re-proved outright here by copying the project's
  proofs, which use only non-item lemmas (`isFiberSeminorm_comp_actOne`, `continuousOn_transNorm`,
  `tendsto_transNorm`, `transNorm_eq_of`, `isAuxNorm_of_tendsto`, ...).
-/

namespace RoundTrip.V12_4
open Polyfold
open Polyfold.EpStrongBundle
open Set Filter Topology Function TopologicalSpace

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.theorem_12_2_2.{0}) ∧
  (type_of% @Polyfold.SEP.theorem_12_2_2.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isLocalAuxNorm_avgNorm.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.avgNorm_actOne.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isLocalAuxNorm_transNorm.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.transNorm_μ.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isAuxNorm_glueNorm.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.theorem_12_2_2.{0}, @Polyfold.SEP.theorem_12_2_2.{0},
    @Polyfold.EpStrongBundle.isLocalAuxNorm_avgNorm.{0},
    @Polyfold.EpStrongBundle.avgNorm_actOne.{0},
    @Polyfold.EpStrongBundle.isLocalAuxNorm_transNorm.{0},
    @Polyfold.EpStrongBundle.transNorm_μ.{0}, @Polyfold.EpStrongBundle.isAuxNorm_glueNorm.{0, 0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h, -⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ E hX
  exact h E hX

/-! ### The building blocks, re-proved outright (the project's proofs, copied) -/

section Local

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

variable (E : EpStrongBundle X B) {x : Obj} (R : X.NaturalRep x)

theorem avgNorm_actOne' (M : B.One → ℝ) (h : X.Isotropy x) {w : B.One}
    (hw : P (B.oneVal w) ∈ R.U) : E.avgNorm R M (E.actOne (R.Γ h) w) = E.avgNorm R M w := by
  unfold EpStrongBundle.avgNorm
  congr 1
  calc ∑ᶠ g : X.Isotropy x, M (E.actOne (R.Γ g) (E.actOne (R.Γ h) w))
      = ∑ᶠ g : X.Isotropy x, (fun g => M (E.actOne (R.Γ g) w)) (Equiv.mulRight h g) :=
        finsum_congr fun g => by
          simp only [Equiv.coe_mulRight]; rw [E.actOne_Γ_mul R g h hw]
    _ = _ := finsum_comp_equiv (Equiv.mulRight h) (f := fun g => M (E.actOne (R.Γ g) w))

/-- **The average of a local auxiliary norm on `U(x)` is one.** -/
theorem isLocalAuxNorm_avgNorm' {M : B.One → ℝ} (hM : B.IsLocalAuxNorm R.U M) :
    B.IsLocalAuxNorm R.U (E.avgNorm R M) := by
  classical
  have := Fintype.ofFinite (X.Isotropy x)
  have hsum : ∀ w, E.avgNorm R M w =
      (Nat.card (X.Isotropy x) : ℝ)⁻¹ * ∑ g, M (E.actOne (R.Γ g) w) := fun w => by
    rw [EpStrongBundle.avgNorm, finsum_eq_sum_of_fintype]
  have hterm : ∀ g, ContinuousOn (fun w => M (E.actOne (R.Γ g) w)) {w | P (B.oneVal w) ∈ R.U} :=
    fun g => hM.continuousOn.comp (E.continuousOn_actOne R.isOpen_U (R.isScSmoothOn_Γ g)
      fun y hy => R.src_Γ g y hy) fun w hw => E.actOne_Γ_mem R g hw
  refine ⟨?_, fun y hy => ?_, fun w y hy h1 h2 => ?_⟩
  · refine (continuousOn_const.mul (continuousOn_finsetSum _ fun g _ => hterm g)).congr
      fun w _ => hsum w
  · have hg : ∀ g ∈ (Finset.univ : Finset (X.Isotropy x)),
        B.IsFiberSeminorm (M ∘ E.actOne (R.Γ g)) y := fun g _ =>
      E.isFiberSeminorm_comp_actOne (R.Γ g) (R.src_Γ g y hy)
        (hM.seminorm _ (by rw [R.tgt_Γ g y hy]; exact R.mapsTo_Φ g hy))
    exact ((StrongBundle.IsFiberSeminorm.finset_sum Finset.univ hg).const_mul
      (inv_nonneg.2 (EpStrongBundle.card_isotropy_pos (X := X) (x := x)).le)).congr fun v => hsum _
  · have hc := EpStrongBundle.card_isotropy_pos (X := X) (x := x)
    have hev : ∀ᶠ k in atTop, P (B.oneVal (w k)) ∈ R.U := h1 (R.isOpen_U.mem_nhds hy)
    have h3 : Tendsto (fun k => (Nat.card (X.Isotropy x) : ℝ) * E.avgNorm R M (w k)) atTop
        (𝓝 0) := by
      have := h2.const_mul (Nat.card (X.Isotropy x) : ℝ)
      rwa [mul_zero] at this
    refine hM.tendsto w y hy h1 (squeeze_zero' (hev.mono fun k hk => hM.nonneg hk)
      (hev.mono fun k hk => ?_) h3)
    rw [hsum, mul_inv_cancel_left₀ hc.ne']
    calc M (w k) = M (E.actOne (R.Γ 1) (w k)) := by rw [E.actOne_Γ_one R hk]
      _ ≤ ∑ g, M (E.actOne (R.Γ g) (w k)) :=
        Finset.single_le_sum (f := fun g => M (E.actOne (R.Γ g) (w k)))
          (fun g _ => hM.nonneg (E.actOne_Γ_mem R g hk)) (Finset.mem_univ _)

open scoped Classical in

variable {E R}

theorem isLocalAuxNorm_transNorm' {M : B.One → ℝ} (hM : B.IsLocalAuxNorm R.U M)
    (hinv : ∀ g w, P (B.oneVal w) ∈ R.U → M (E.actOne (R.Γ g) w) = M w) :
    B.IsLocalAuxNorm (X.satSet R.U) (E.transNorm R M) :=
  ⟨continuousOn_transNorm hM hinv, fun _ hy => isFiberSeminorm_transNorm hM hy,
    fun w _ hy h1 h2 => tendsto_transNorm hM hinv w hy h1 h2⟩

/-- **The transport is invariant under all morphisms** (condition (3) of Definition 12.2.1):
`N''_x(μ(ψ, k)) = N''_x(k)`. -/
theorem transNorm_μ' {M : B.One → ℝ}
    (hinv : ∀ g w, P (B.oneVal w) ∈ R.U → M (E.actOne (R.Γ g) w) = M w) (h k : B.One) (ψ : Mor)
    (hk : P (B.oneVal k) = X.src ψ) (hh : B.oneVal h = E.μ ⟨(ψ, B.oneVal k), hk⟩) :
    E.transNorm R M h = E.transNorm R M k := by
  have hPh : P (B.oneVal h) = X.tgt ψ := by rw [hh, E.P_μ]
  by_cases hs : P (B.oneVal k) ∈ X.satSet R.U
  · have hφs := X.src_selMor R.U (P (B.oneVal k))
    have hφt := X.tgt_selMor_mem hs
    set φ := X.selMor R.U (P (B.oneVal k)) with hφ
    have hc1 : X.src φ = X.tgt (X.inv ψ) := by rw [X.tgt_inv, hφs, hk]
    have hs' : X.src ((fun _ : Obj => X.comp φ (X.inv ψ)) (P (B.oneVal h))) = P (B.oneVal h) := by
      change X.src (X.comp φ (X.inv ψ)) = _
      rw [X.src_comp _ _ hc1, X.src_inv, hPh]
    have ht' : X.tgt ((fun _ : Obj => X.comp φ (X.inv ψ)) (P (B.oneVal h))) ∈ R.U := by
      change X.tgt (X.comp φ (X.inv ψ)) ∈ R.U
      rw [X.tgt_comp _ _ hc1]; exact hφt
    rw [transNorm_eq_of hinv (α := fun _ => X.comp φ (X.inv ψ)) hs' ht', transNorm, if_pos hs]
    congr 1
    apply B.oneVal_injective
    have h2 : X.src (X.comp φ (X.inv ψ)) = X.tgt ψ := by rw [X.src_comp _ _ hc1, X.src_inv]
    have hcomp : X.comp (X.comp φ (X.inv ψ)) ψ = φ := by
      have := GroupoidStr.comp_inv_cancel_right (G := X.toGroupoidStr) (φ := X.inv ψ) (ψ := φ) hc1
      rwa [GroupoidStr.inv_inv] at this
    calc B.oneVal (E.actOne (fun _ => X.comp φ (X.inv ψ)) h)
        = E.μ ⟨(X.comp φ (X.inv ψ), B.oneVal h), hs'.symm⟩ := E.oneVal_actOne_of_eq hs'.symm
      _ = E.μ ⟨(X.comp φ (X.inv ψ), E.μ ⟨(ψ, B.oneVal k), hk⟩), (E.P_μ _).trans h2.symm⟩ :=
          E.μ_congr (Prod.ext rfl hh)
      _ = E.μ ⟨(X.comp (X.comp φ (X.inv ψ)) ψ, B.oneVal k),
            hk.trans (X.src_comp _ _ h2).symm⟩ := (E.μ_comp _ ψ (B.oneVal k) hk h2).symm
      _ = E.μ ⟨(φ, B.oneVal k), hφs.symm⟩ := E.μ_congr (Prod.ext hcomp rfl)
      _ = B.oneVal (E.actOne (X.selMor R.U) k) :=
          (E.oneVal_actOne_of_eq (α := X.selMor R.U) (w := k) hφs.symm).symm
  · have hs' : P (B.oneVal h) ∉ X.satSet R.U := by
      rintro ⟨χ, hχs, hχt⟩
      refine hs ⟨X.comp χ ψ, ?_, ?_⟩
      · rw [X.src_comp _ _ (hχs.trans hPh), hk]
      · rw [X.tgt_comp _ _ (hχs.trans hPh)]; exact hχt
    rw [transNorm, transNorm, if_neg hs, if_neg hs']

end Local

section Glue

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  {ι : Type} {E : EpStrongBundle X B}
  {U : ι → Set Obj} {β : PartitionOfUnity ι X.OrbitSpace univ} {T : ι → B.One → ℝ}

theorem isAuxNorm_glueNorm' (hU : ∀ i, IsOpen (U i)) (hsat : ∀ i, X.IsSaturated (U i))
    (hβ : β.IsSubordinate fun i => X.π '' U i) (hT : ∀ i, B.IsLocalAuxNorm (U i) (T i))
    (hinv : ∀ i (h k : B.One) (ψ : Mor) (hk : P (B.oneVal k) = X.src ψ),
      P (B.oneVal k) ∈ U i → B.oneVal h = E.μ ⟨(ψ, B.oneVal k), hk⟩ → T i h = T i k) :
    E.IsAuxNorm (glueNorm β T) := by
  have hP1 : Continuous fun w : B.One => P (B.oneVal w) := B.continuous.comp B.continuous_oneVal
  have hπP : Continuous fun w : B.One => X.π (P (B.oneVal w)) := X.continuous_π.comp hP1
  have hfin : ∀ y : Obj, ∃ s : Finset ι, (support fun i => β i (X.π y)) ⊆ s := fun y =>
    ⟨(β.locallyFinite.point_finite (X.π y)).toFinset, fun i hi =>
      (Set.Finite.mem_toFinset _).2 hi⟩
  have hsum : ∀ (y : Obj) (s : Finset ι), (support fun i => β i (X.π y)) ⊆ s → ∀ w : B.One,
      P (B.oneVal w) = y → glueNorm β T w = ∑ i ∈ s, β i (X.π y) * T i w := by
    intro y s hs w hw
    rw [glueNorm, hw]
    exact finsum_eq_sum_of_support_subset _ ((support_mul_subset_left _ _).trans hs)
  -- continuity
  have hcont : Continuous (glueNorm β T) := by
    apply continuous_finsum (f := fun i w => β i (X.π (P (B.oneVal w))) * T i w)
    · intro i
      have hc : ContinuousOn (fun w => β i (X.π (P (B.oneVal w))) * T i w)
          {w | P (B.oneVal w) ∈ U i} :=
        ((β i).continuous.comp hπP).continuousOn.mul (hT i).continuousOn
      refine hc.continuous_of_tsupport_subset ((hU i).preimage hP1) ?_
      refine tsupport_mul_subset_left.trans ?_
      exact (tsupport_comp_subset_preimage (β i) hπP).trans fun w hw =>
        EpGroupoid.mem_of_π_mem_image (hsat i) (hβ i hw)
    · exact (β.locallyFinite.preimage_continuous hπP).subset fun i =>
        support_mul_subset_left _ _
  -- the fibres
  have hsn : ∀ y, B.IsFiberSeminorm (glueNorm β T) y := by
    intro y
    obtain ⟨s, hs⟩ := hfin y
    have hterm : ∀ i ∈ s, B.IsFiberSeminorm (fun w => β i (X.π y) * T i w) y := by
      intro i _
      by_cases hy : y ∈ U i
      · exact ((hT i).seminorm y hy).const_mul (β.nonneg i _)
      · rw [partition_eq_zero_of_not_mem hsat hβ hy]
        exact ⟨fun t v => by simp, fun v w => by simp⟩
    exact (StrongBundle.IsFiberSeminorm.finset_sum s hterm).congr fun v =>
      hsum y s hs _ (B.proj_oneVal_toOne v)
  -- condition (2)
  have h2 : B.TendstoZeroOne (glueNorm β T) := by
    intro w y h1 h2
    obtain ⟨i, hi⟩ : ∃ i, β i (X.π y) ≠ 0 := by
      by_contra hall
      push Not at hall
      have h1 := β.sum_eq_one (mem_univ (X.π y))
      rw [finsum_eq_zero_of_forall_eq_zero hall] at h1
      exact zero_ne_one h1
    have hpos : 0 < β i (X.π y) := lt_of_le_of_ne (β.nonneg i _) (Ne.symm hi)
    have hyU : y ∈ U i := by
      by_contra hy; exact hi (partition_eq_zero_of_not_mem hsat hβ hy)
    have hβk : Tendsto (fun k => β i (X.π (P (B.oneVal (w k))))) atTop (𝓝 (β i (X.π y))) :=
      ((β i).continuous.comp X.continuous_π).continuousAt.tendsto.comp h1
    have hterm : Tendsto (fun k => β i (X.π (P (B.oneVal (w k)))) * T i (w k)) atTop (𝓝 0) := by
      refine squeeze_zero (fun k => glue_term_nonneg hsat hβ hT i (w k)) (fun k => ?_) h2
      refine single_le_finsum i ?_ fun j => glue_term_nonneg hsat hβ hT j (w k)
      exact (β.locallyFinite.point_finite (X.π (P (B.oneVal (w k))))).subset
        (support_mul_subset_left _ _)
    have hev : ∀ᶠ k in atTop, β i (X.π (P (B.oneVal (w k)))) ≠ 0 :=
      hβk.eventually (eventually_ne_nhds hpos.ne')
    have hT0 : Tendsto (fun k => T i (w k)) atTop (𝓝 0) := by
      have h3 := hterm.div hβk hpos.ne'
      rw [zero_div] at h3
      exact h3.congr' (hev.mono fun k hk => by
        change β i _ * T i (w k) / β i _ = T i (w k)
        exact mul_div_cancel_left₀ _ hk)
    exact (hT i).tendsto w y hyU h1 hT0
  refine ⟨StrongBundle.isAuxNorm_of_tendsto hcont hsn h2, fun h k ψ hk hh => ?_⟩
  -- condition (3)
  have hPh : P (B.oneVal h) = X.tgt ψ := by rw [hh, E.P_μ]
  have hπ : X.π (P (B.oneVal h)) = X.π (P (B.oneVal k)) := by
    rw [hPh, hk]; exact (X.π_src_eq_π_tgt ψ).symm
  refine finsum_congr fun i => ?_
  rw [hπ]
  by_cases hkU : P (B.oneVal k) ∈ U i
  · rw [hinv i h k ψ hk hkU hh]
  · rw [partition_eq_zero_of_not_mem hsat hβ hkU, zero_mul, zero_mul]

end Glue

theorem B_to_A : B → A := by
  intro hB
  have h1 : type_of% @Polyfold.EpStrongBundle.theorem_12_2_2.{0} := by
    intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E hX
    have := B.paracompactSpace_pullback X.PMor X.src
    exact hB Obj Mor X W P B E hX
  refine ⟨h1, fun A h => h1 A.E h, ?_, ?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ E x R M hM
    exact isLocalAuxNorm_avgNorm' E R hM
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ E x R M h w hw
    exact avgNorm_actOne' E R M h hw
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ E x R M hM hinv
    exact isLocalAuxNorm_transNorm' (E := E) (R := R) hM hinv
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ E x R M hinv
    exact transNorm_μ' (E := E) (R := R) hinv
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B E ι U β T hU hsat hβ hT hinv
    exact isAuxNorm_glueNorm' hU hsat hβ hT hinv

#rt_check RoundTrip.V12_4.A_to_B [Polyfold.EpStrongBundle.theorem_12_2_2,
  Polyfold.SEP.theorem_12_2_2,
  Polyfold.EpStrongBundle.isLocalAuxNorm_avgNorm,
  Polyfold.EpStrongBundle.avgNorm_actOne,
  Polyfold.EpStrongBundle.isLocalAuxNorm_transNorm,
  Polyfold.EpStrongBundle.transNorm_μ,
  Polyfold.EpStrongBundle.isAuxNorm_glueNorm]
#rt_check RoundTrip.V12_4.B_to_A [Polyfold.EpStrongBundle.theorem_12_2_2,
  Polyfold.SEP.theorem_12_2_2,
  Polyfold.EpStrongBundle.isLocalAuxNorm_avgNorm,
  Polyfold.EpStrongBundle.avgNorm_actOne,
  Polyfold.EpStrongBundle.isLocalAuxNorm_transNorm,
  Polyfold.EpStrongBundle.transNorm_μ,
  Polyfold.EpStrongBundle.isAuxNorm_glueNorm]
#rt_overlap RoundTrip.V12_4.B_to_A [Polyfold.EpStrongBundle.theorem_12_2_2,
  Polyfold.SEP.theorem_12_2_2,
  Polyfold.EpStrongBundle.isLocalAuxNorm_avgNorm,
  Polyfold.EpStrongBundle.avgNorm_actOne,
  Polyfold.EpStrongBundle.isLocalAuxNorm_transNorm,
  Polyfold.EpStrongBundle.transNorm_μ,
  Polyfold.EpStrongBundle.isAuxNorm_glueNorm]

end RoundTrip.V12_4
