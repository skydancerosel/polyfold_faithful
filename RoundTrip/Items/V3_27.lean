import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_27

/-!
Round trip for V3_27 (Theorem 3.30).  `A` is the conjunction of the types of
`Polyfold.theorem_3_3_3`, `Polyfold.ContractionGerm.isSc1GermWith_sol`,
`Polyfold.ContractionGerm.hasFDerivWithinAt_sol`, `Polyfold.ContractionGerm.Lop_Aop` and
`Polyfold.ContractionGerm.continuousOn_Aop` (no universe parameters; `ContractionGerm.Aop` is a
definition).

Glue for `A → B` (as in V3_30, with `k = 1`):
* B's partial quadrant is quadrant-like.
* B assumes `f = w − B(a, w)` sc¹; then `B = pr₂ − f` is sc¹ (pairing, the sc-operator
  `(u, v) ↦ u − v`).
* `theorem_3_3_3` (in `A`) for the working form `h.toContractionGerm` gives `sol` sc¹ on `germ 1`;
  B's arbitrary solution germ `δ` agrees with `sol` near `0` (uniqueness of fixed points in `O 0`,
  `ContractionGerm.eq_sol`, which is not among the banned theorems of this item), so `δ` is sc¹ on
  `V' = V ∩ germ 1 ∩ {δ ∈ O 0}`.
-/

namespace RoundTrip.V3_27
open Polyfold

/-- The project's statement: Theorem 3.30 and the lemmas cited with it. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_3_3 ∧ type_of% @Polyfold.ContractionGerm.isSc1GermWith_sol ∧
    type_of% @Polyfold.ContractionGerm.hasFDerivWithinAt_sol ∧
    type_of% @Polyfold.ContractionGerm.Lop_Aop ∧ type_of% @Polyfold.ContractionGerm.continuousOn_Aop

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_3_3, @Polyfold.ContractionGerm.isSc1GermWith_sol,
    @Polyfold.ContractionGerm.hasFDerivWithinAt_sol, @Polyfold.ContractionGerm.Lop_Aop,
    @Polyfold.ContractionGerm.continuousOn_Aop⟩

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

end Glue

theorem A_to_B : A → B := by
  intro hA n W Ct G Bm hPQ h hf V δ hsol
  have hC : IsQuadrantLike (ScBanach.const (Fin n → ℝ)) Ct := hPQ.isQuadrantLike
  have hCG : IsQuadrantLike (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ) := hC.paramProd W
  have hf1 : IsSckGerm 1 G (contractionMap Bm) := ⟨hf, hf.tangentMapGerm_isSc0⟩
  have hB : IsSc1Germ G Bm := (isSckGerm_of_contractionMap hCG hf1).1
  set 𝒞 := h.toContractionGerm with h𝒞
  obtain ⟨-, hsA⟩ := hA.1 𝒞 hC hB
  obtain ⟨hδ0, hδzero, hδsol⟩ := hsol
  -- `{δ ∈ O 0}` is relatively open in `V₀`
  have hcont : ContinuousOn δ (V.U 0) := by
    have := hδ0.continuousOn 0
    exact this.congr fun a _ => (levelMap_zero δ a).symm
  obtain ⟨u, hu, hueq⟩ := (continuousOn_iff'.1 hcont) (𝒞.O 0) (𝒞.O_open 0)
  have hu0 : (0 : Fin n → ℝ) ∈ u := by
    have : (0 : Fin n → ℝ) ∈ δ ⁻¹' 𝒞.O 0 ∩ V.U 0 :=
      ⟨by rw [Set.mem_preimage, hδzero]; exact 𝒞.zero_mem_O 0, V.zero_mem 0⟩
    rw [hueq] at this
    exact this.1
  let V' : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct :=
    { U := fun m => V.U m ∩ (𝒞.N (m + 1) ∩ u)
      nested := fun m x hx => ⟨V.nested m x hx.1, 𝒞.N_anti_le (by omega) hx.2.1, hx.2.2⟩
      zero_mem := fun m => ⟨V.zero_mem m, 𝒞.N_zero _, hu0⟩
      relOpen := fun m => by
        obtain ⟨T, hT, hVm⟩ := V.relOpen m
        refine ⟨T ∩ (𝒞.N (m + 1) ∩ u), hT.inter ((𝒞.N_open _).inter hu), ?_⟩
        rw [hVm]
        ext a
        simp only [Set.mem_inter_iff]
        tauto }
  refine ⟨V', fun m a ha => ha.1, ?_⟩
  have hVC : ∀ m, ∀ a ∈ V.U m, a ∈ Ct := fun m a ha => by
    have := V.U_subset m ha
    rwa [ScBanach.const_lvlSet] at this
  have h1 : IsSckGerm 1 V' 𝒞.sol :=
    have hsub : ∀ m, V'.U m ⊆ (𝒞.germ hC 1).U m := fun m a ha => ⟨ha.2.1, hVC m a ha.1⟩
    IsSckGerm.mono hC hsub hsA
  refine (IsSckGerm.congr (k := 1) hC (fun a ha => ?_) h1).1
  have haN : a ∈ 𝒞.N 0 ∩ Ct := ⟨𝒞.N_anti_le (by omega) ha.2.1, hVC 0 a ha.1⟩
  have hO : δ a ∈ 𝒞.O 0 := by
    have : a ∈ u ∩ V.U 0 := ⟨ha.2.2, ha.1⟩
    rw [← hueq] at this
    exact this.1
  have hfix : 𝒞.B (a, δ a) = δ a := by
    have := (hδsol a ha.1).2
    change δ a - Bm (a, δ a) = 0 at this
    exact (sub_eq_zero.1 this).symm
  exact (𝒞.eq_sol haN hO hfix).symm

#rt_check RoundTrip.V3_27.A_to_B [Polyfold.theorem_3_3_3,
  Polyfold.ContractionGerm.isSc1GermWith_sol, Polyfold.ContractionGerm.hasFDerivWithinAt_sol,
  Polyfold.ContractionGerm.Lop_Aop, Polyfold.ContractionGerm.continuousOn_Aop]

end RoundTrip.V3_27
