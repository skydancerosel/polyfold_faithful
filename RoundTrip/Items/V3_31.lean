import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_31

/-!
Round trip for V3_31 (Corollary 3.34).  Refreshed 2026-11-02 against HEAD (new conjuncts: one germ
for all `k`).  `A` is the conjunction of the types of `Polyfold.corollary_3_3_7`,
`Polyfold.IsSckGerm.contDiffOn_levels`, and (new) `Polyfold.corollary_3_3_7_isScSmoothGerm`,
`Polyfold.isSckGerm_of_levels` (no universe parameters).

`A → B` is proved, now entirely from `A`:
* (1) `C^k` on `V_{m,k}`: A's `corollary_3_3_7` for the working form `h.toContractionGerm`
  (glue as in V3_30: sc-smoothness of `f = w − B` gives that of `B`; B's arbitrary solution germ
  `δ` agrees with `sol` near `0` by uniqueness in `O 0`), with `V_{m,k}` shrunk into `V₀` and the
  agreement region, and `δ_m = levelMap sol m`.
* (2) "in particular `δ` is sc-smooth" (one germ `V'` on which `δ` is sc^k for every `k`): at the
  audit this was not in A and was proved in this file from `theorem_3_3_6_smooth` with a diagonal
  germ and a locality lemma; both have moved into the project, and A now contains
  `corollary_3_3_7_isScSmoothGerm` (`sol` sc-smooth on one diagonal germ `germDiag t`).  Here:
  `V' = V ∩ germDiag t ∩ (u ∩ C̃)`, on which `δ = sol`.

`B → A` is not proved: A contains `IsSckGerm.contDiffOn_levels` (Proposition 1.18 for germs
between arbitrary sc-Banach spaces) and `isSckGerm_of_levels` (locality of sc^k in the levels, for
arbitrary germs), and `corollary_3_3_7(_isScSmoothGerm)` is for any quadrant-like `C̃` and the
working-form `ContractionGerm` (a `1/2`-contraction on explicit regions) with its specific `sol` and
germs, none of which follows from B.
-/

namespace RoundTrip.V3_31
open Polyfold

/-- The project's statement: Corollary 3.34 and Proposition 1.18 for germs. -/
def A : Prop :=
  type_of% @Polyfold.corollary_3_3_7 ∧ type_of% @Polyfold.IsSckGerm.contDiffOn_levels ∧
    type_of% @Polyfold.corollary_3_3_7_isScSmoothGerm ∧ type_of% @Polyfold.isSckGerm_of_levels

theorem A_holds : A :=
  ⟨@Polyfold.corollary_3_3_7, @Polyfold.IsSckGerm.contDiffOn_levels,
    @Polyfold.corollary_3_3_7_isScSmoothGerm, @Polyfold.isSckGerm_of_levels⟩

section Glue

/-- The sc-operator `W ⊕ W → W`, `(u, v) ↦ u − v`. -/
noncomputable def subOp (W : ScBanach) : ScOperator (W.prod W) W where
  lvl m := ContinuousLinearMap.fst ℝ (W m) (W m) - ContinuousLinearMap.snd ℝ (W m) (W m)
  incl_comm m x := by
    change W.incl m (x.1 - x.2) = W.incl m x.1 - W.incl m x.2
    exact map_sub _ _ _

/-- `B` is of class sc^k when `f = w − B(a, w)` is. -/
theorem isSckGerm_of_contractionMap {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {W : ScBanach} {Ct : Set P}
    {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ Set.univ)} {Bm : P × W.lvl 0 → W.lvl 0}
    {k : ℕ} (hCG : IsQuadrantLike (ScBanach.paramProd P W) (Ct ×ˢ Set.univ))
    (hk : IsSckGerm k G (contractionMap Bm)) : IsSckGerm k G Bm := by
  have h2 : IsSckGerm k G ((ScBanach.sndOp (ScBanach.const P) W) 0) :=
    ScOperator.isSckGerm k _ G hCG
  have h3 := (IsSckGerm.pair hCG h2 hk).operator_comp hCG (subOp W)
  refine IsSckGerm.congr hCG (fun p _ => ?_) h3
  change p.2 - (p.2 - Bm p) = Bm p
  abel

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P} {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ Set.univ)}
  {Bm : P × W.lvl 0 → W.lvl 0}

/-- The region `{δ ∈ O 0}` near `0` where a solution germ agrees with `sol`. -/
lemma exists_agree (h : IsSc0ContractionGerm Ct G Bm)
    {V : ScNbhdGerm (ScBanach.const P) Ct} {δ : P → W.lvl 0}
    (hsol : IsSolGerm G Bm V δ) :
    ∃ u : Set P, IsOpen u ∧ (0 : P) ∈ u ∧
      ∀ a ∈ V.U 0, a ∈ h.toContractionGerm.N 0 → a ∈ u → δ a = h.toContractionGerm.sol a := by
  set 𝒞 := h.toContractionGerm with h𝒞
  obtain ⟨hδ0, hδzero, hδsol⟩ := hsol
  have hcont : ContinuousOn δ (V.U 0) :=
    (hδ0.continuousOn 0).congr fun a _ => (levelMap_zero δ a).symm
  obtain ⟨u, hu, hueq⟩ := (continuousOn_iff'.1 hcont) (𝒞.O 0) (𝒞.O_open 0)
  have hu0 : (0 : P) ∈ u := by
    have : (0 : P) ∈ δ ⁻¹' 𝒞.O 0 ∩ V.U 0 :=
      ⟨by rw [Set.mem_preimage, hδzero]; exact 𝒞.zero_mem_O 0, V.zero_mem 0⟩
    rw [hueq] at this
    exact this.1
  refine ⟨u, hu, hu0, fun a haV haN hau => ?_⟩
  have haC : a ∈ Ct := by
    have := V.U_subset 0 haV
    rwa [ScBanach.const_lvlSet] at this
  have hO : δ a ∈ 𝒞.O 0 := by
    have : a ∈ u ∩ V.U 0 := ⟨hau, haV⟩
    rw [← hueq] at this
    exact this.1
  have hfix : 𝒞.B (a, δ a) = δ a := by
    have := (hδsol a haV).2
    change δ a - Bm (a, δ a) = 0 at this
    exact (sub_eq_zero.1 this).symm
  exact 𝒞.eq_sol ⟨haN, haC⟩ hO hfix

end Glue

theorem A_to_B : A → B := by
  intro hA P _ _ _ W Ct G Bm hPQ h hf V δ hsol
  have hC : IsQuadrantLike (ScBanach.const P) Ct := hPQ.isQuadrantLike
  have hCG : IsQuadrantLike (ScBanach.paramProd P W) (Ct ×ˢ Set.univ) := hC.paramProd W
  set 𝒞 := h.toContractionGerm with h𝒞
  have hB : IsScSmoothGerm 𝒞.G 𝒞.B := fun k => isSckGerm_of_contractionMap hCG (hf k)
  have hVC : ∀ (V : ScNbhdGerm (ScBanach.const P) Ct) m, ∀ a ∈ V.U m, a ∈ Ct :=
    fun V m a ha => by
      have := V.U_subset m ha
      rwa [ScBanach.const_lvlSet] at this
  obtain ⟨u, hu, hu0, hagree⟩ := exists_agree h hsol
  refine ⟨fun m k => ?_, ?_⟩
  · -- (1) from A's Corollary 3.34
    obtain ⟨V0, ⟨O, hO, rfl⟩, h0, hrange, hcd⟩ := hA.1 𝒞 hC hB m k
    obtain ⟨T, hT, hVT⟩ := V.relOpen 0
    rw [ScBanach.const_lvlSet] at hVT
    refine ⟨(O ∩ (T ∩ (𝒞.N 0 ∩ u))) ∩ Ct, ⟨O ∩ (T ∩ (𝒞.N 0 ∩ u)),
      hO.inter (hT.inter ((𝒞.N_open 0).inter hu)), rfl⟩, ?_, ?_,
      levelMap (E := ScBanach.const P) (F := W) 𝒞.sol m, fun v hv => ?_, hcd.mono ?_⟩
    · have h0V : (0 : P) ∈ V.U 0 := V.zero_mem 0
      rw [hVT] at h0V
      exact ⟨⟨h0.1, h0V.1, 𝒞.N_zero 0, hu0⟩, h0.2⟩
    · intro v hv
      rw [hVT]
      exact ⟨hv.1.2.1, hv.2⟩
    · have hvV : v ∈ V.U 0 := by rw [hVT]; exact ⟨hv.1.2.1, hv.2⟩
      have := toBase_levelMap (E := ScBanach.const P) (F := W) (f := 𝒞.sol) (m := m) (x := v)
        (by rw [ScBanach.const_toBase]; exact hrange v ⟨hv.1.1, hv.2⟩)
      rw [this, ScBanach.const_toBase]
      exact (hagree v hvV hv.1.2.2.1 hv.1.2.2.2).symm
    · intro v hv
      exact ⟨hv.1.1, hv.2⟩
  · -- (2) from A's `corollary_3_3_7_isScSmoothGerm` (one germ for all `k`)
    obtain ⟨t, ht, -, hsm⟩ := hA.2.2.1 𝒞 hC hB
    refine ⟨V.inter ((𝒞.germDiag hC t ht).inter (ScNbhdGerm.ofOpen hC hu hu0)),
      fun m a ha => ha.1, fun k => ?_⟩
    refine IsSckGerm.congr hC (fun a ha => ?_)
      (IsSckGerm.mono hC (fun m _ ha => ha.2.1) (hsm k))
    exact (hagree a ha.1 (𝒞.N_anti_le (by omega) ha.2.1.1) ha.2.2.1).symm

#rt_check RoundTrip.V3_31.A_to_B [Polyfold.corollary_3_3_7, Polyfold.IsSckGerm.contDiffOn_levels,
  Polyfold.corollary_3_3_7_isScSmoothGerm, Polyfold.isSckGerm_of_levels]

end RoundTrip.V3_31
