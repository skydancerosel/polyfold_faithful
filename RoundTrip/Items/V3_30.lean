import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_30

/-!
Round trip for V3_30 (Theorem 3.33).  `A` is the conjunction of the types of
`Polyfold.theorem_3_3_6`, `Polyfold.theorem_3_3_6_smooth` and
`Polyfold.theorem_3_3_6_of_isSc0ContractionGerm` (no universe parameters).

Glue for `A → B`:
* B's partial quadrant is quadrant-like (`IsPartialQuadrant.isQuadrantLike`).
* B assumes `f = w − B(a, w)` of class sc^k, A assumes `B` of class sc^k: `B = pr₂ − f`, via
  pairing and the sc-operator `(u, v) ↦ u − v`.
* A's `theorem_3_3_6` for the working form `h.toContractionGerm` of the contraction germ gives
  `δ_A = sol` of class sc^k on `germ s`.  B's arbitrary solution germ `δ` agrees with `δ_A` near `0`
  by uniqueness of fixed points in `O 0` (`ContractionGerm.eq_sol`, continuity of `δ` and
  `δ(0) = 0`), so `δ` is sc^k on `V' = V ∩ germ s ∩ {δ ∈ O 0}`.
-/

namespace RoundTrip.V3_30
open Polyfold

/-- The project's statement: Theorem 3.33 in its three forms. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_3_6 ∧ type_of% @Polyfold.theorem_3_3_6_smooth ∧
    type_of% @Polyfold.theorem_3_3_6_of_isSc0ContractionGerm

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_3_6, @Polyfold.theorem_3_3_6_smooth,
    @Polyfold.theorem_3_3_6_of_isSc0ContractionGerm⟩

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
  intro hA n W Ct G Bm k hPQ h hk V δ hsol
  have hC : IsQuadrantLike (ScBanach.const (Fin n → ℝ)) Ct := hPQ.isQuadrantLike
  have hCG : IsQuadrantLike (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ) := hC.paramProd W
  have hB : IsSckGerm k G Bm := isSckGerm_of_contractionMap hCG hk
  set 𝒞 := h.toContractionGerm with h𝒞
  obtain ⟨s, -, hsA⟩ := hA.1 𝒞 hC (k := k) hB
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
    { U := fun m => V.U m ∩ (𝒞.N (m + s) ∩ u)
      nested := fun m x hx => ⟨V.nested m x hx.1, 𝒞.N_anti_le (by omega) hx.2.1, hx.2.2⟩
      zero_mem := fun m => ⟨V.zero_mem m, 𝒞.N_zero _, hu0⟩
      relOpen := fun m => by
        obtain ⟨T, hT, hVm⟩ := V.relOpen m
        refine ⟨T ∩ (𝒞.N (m + s) ∩ u), hT.inter ((𝒞.N_open _).inter hu), ?_⟩
        rw [hVm]
        ext a
        simp only [Set.mem_inter_iff]
        tauto }
  refine ⟨V', fun m a ha => ha.1, ?_⟩
  have hVC : ∀ m, ∀ a ∈ V.U m, a ∈ Ct := fun m a ha => by
    have := V.U_subset m ha
    rwa [ScBanach.const_lvlSet] at this
  have h1 : IsSckGerm k V' 𝒞.sol :=
    have hsub : ∀ m, V'.U m ⊆ (𝒞.germ hC s).U m := fun m a ha => ⟨ha.2.1, hVC m a ha.1⟩
    IsSckGerm.mono hC hsub hsA
  refine IsSckGerm.congr hC (fun a ha => ?_) h1
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

#rt_check RoundTrip.V3_30.A_to_B [Polyfold.theorem_3_3_6, Polyfold.theorem_3_3_6_smooth,
  Polyfold.theorem_3_3_6_of_isSc0ContractionGerm]

end RoundTrip.V3_30
