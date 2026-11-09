import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_32

/-!
Round trip for V3_32 (Theorem 3.35).  Refreshed 2026-11-02 against HEAD (new conjuncts: Theorem
3.35 on one germ, and in the text's form).  `A` is the conjunction of the types of
`Polyfold.theorem_3_35_preprint`, `Polyfold.theorem_3_35_smooth_preprint` and (new)
`Polyfold.theorem_3_35_isScSmoothGerm_preprint`, `Polyfold.theorem_3_35_of_isSc0ContractionGerm_preprint`,
`Polyfold.isSckGerm_contractionMap_iff` (no universe parameters).

`A → B` is proved twice:
* `A_to_B_text` (new): A's `theorem_3_35_of_isSc0ContractionGerm_preprint` is Theorem 3.35 in the text's
  form (Definition 3.28 contraction germ, any representative `(V, δ)` of the solution germ, sc^k on
  a smaller `V' ⊆ V`, sc-smooth on one smaller `V'`), for any quadrant-like `C̃ ⊆ P`; B is its
  special case `P = ℝⁿ`, `C̃` a partial quadrant.  (The audit's glue — locality lemma, diagonal
  germ, agreement with `sol` — has moved into the project.)
* `A_to_B` (the audit's proof, repaired for the new `A`): through the working-form conjuncts
  `theorem_3_35_preprint` and `theorem_3_35_smooth_preprint`, B's solution germ agreeing with `sol` near `0`
  (`ContractionGerm.eq_sol`), and for the sc-smooth part the diagonal germ
  `V'_m = V_m ∩ N(m + t_m) ∩ {δ ∈ O 0}`, `t_m = Σ_{j ≤ m} s_j`, with the locality lemma
  `isSckGerm_of_levels` proved in this file.

`B → A` is not proved: A's working-form theorems (`theorem_3_35_preprint`, `_smooth`, `_isScSmoothGerm`)
are about the `1/2`-contraction `ContractionGerm` (weaker than Definition 3.28) and the specific
`sol` on explicit germs, A's text-form theorem is for any finite-dimensional `P` and any
quadrant-like `C̃`, and `isSckGerm_contractionMap_iff` is not in B.
-/

namespace RoundTrip.V3_32
open Polyfold

/-- The project's statement: Theorem 3.35 in its two forms. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_35_preprint ∧ type_of% @Polyfold.theorem_3_35_smooth_preprint ∧
    type_of% @Polyfold.theorem_3_35_isScSmoothGerm_preprint ∧
    type_of% @Polyfold.theorem_3_35_of_isSc0ContractionGerm_preprint ∧
    type_of% @Polyfold.isSckGerm_contractionMap_iff

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_35_preprint, @Polyfold.theorem_3_35_smooth_preprint, @Polyfold.theorem_3_35_isScSmoothGerm_preprint,
    @Polyfold.theorem_3_35_of_isSc0ContractionGerm_preprint, @Polyfold.isSckGerm_contractionMap_iff⟩

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

/-- The intersection of two germs of neighbourhoods. -/
def germInter {E : ScBanach} {C : Set (E 0)} (G₁ G₂ : ScNbhdGerm E C) : ScNbhdGerm E C where
  U m := G₁.U m ∩ G₂.U m
  nested m x hx := ⟨G₁.nested m x hx.1, G₂.nested m x hx.2⟩
  zero_mem m := ⟨G₁.zero_mem m, G₂.zero_mem m⟩
  relOpen m := by
    obtain ⟨O₁, h₁, e₁⟩ := G₁.relOpen m
    obtain ⟨O₂, h₂, e₂⟩ := G₂.relOpen m
    refine ⟨O₁ ∩ O₂, h₁.inter h₂, ?_⟩
    rw [e₁, e₂]
    ext x
    simp only [Set.mem_inter_iff]
    tauto

/-- **Locality of sc^k in the levels**: `f` is sc^k on `G'` if for every `j` it is sc^j on some
germ `G_j` containing `G'` on the levels `≥ j`. -/
theorem isSckGerm_of_levels : ∀ (k : ℕ) {E F : ScBanach} {C : Set (E 0)},
    IsQuadrantLike E C → ∀ (G' : ScNbhdGerm E C) (f : E 0 → F 0),
    (∀ j : ℕ, ∃ Gj : ScNbhdGerm E C, (∀ m, G'.U (m + j) ⊆ Gj.U (m + j)) ∧ IsSckGerm j Gj f) →
    IsSckGerm k G' f
  | 0, _, _, _, _, G', f, hG => by
    obtain ⟨G0, hsub, h0⟩ := hG 0
    exact IsSc0Germ.mono (h0 : IsSc0Germ G0 f) fun m => hsub m
  | k + 1, E, F, C, hC, G', f, hG => by
    obtain ⟨G0, hsub0, h0⟩ := hG 0
    obtain ⟨G1, hsub1, h1⟩ := hG 1
    obtain ⟨D, hD⟩ := (h1 : IsSckGerm (0 + 1) G1 f).1
    have hsub1' : ∀ m, G'.U (m + 1) ⊆ G1.U (m + 1) := hsub1
    have hG'1 : IsSc1Germ G' f :=
      ⟨D, { isSc0 := IsSc0Germ.mono (h0 : IsSc0Germ G0 f) fun m => hsub0 m
            hasFDerivWithinAt := fun x hx =>
              (hD.hasFDerivWithinAt x (hsub1' 0 hx)).mono (hsub1' 0)
            tangent_isSc0 := hD.tangent_isSc0.mono fun m _ hp =>
              (ScNbhdGerm.mem_tangent_U _).2 (hsub1' m ((ScNbhdGerm.mem_tangent_U _).1 hp)) }⟩
    refine ⟨hG'1, isSckGerm_of_levels k hC.tangentSet G'.tangent (tangentMapGerm G' f)
      fun j => ?_⟩
    obtain ⟨Gj, hsubj, hj⟩ := hG (j + 1)
    let K := germInter Gj G'
    have hK : IsSckGerm (j + 1) K f := IsSckGerm.mono hC (fun m _ hx => hx.1) hj
    have hKG' : ∀ m, K.U m ⊆ G'.U m := fun m _ hx => hx.2
    refine ⟨K.tangent, fun m p hp => ?_, ?_⟩
    · exact (ScNbhdGerm.mem_tangent_U _).2
        ⟨hsubj m ((ScNbhdGerm.mem_tangent_U _).1 hp), (ScNbhdGerm.mem_tangent_U _).1 hp⟩
    · exact IsSckGerm.congr hC.tangentSet (hG'1.tangentMapGerm_mono hC hKG') hK.2

end Glue

section Common

variable {n : ℕ} {W : ScBanach} {Ct : Set (Fin n → ℝ)}
  {G : ScNbhdGerm (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ)}
  {Bm : (Fin n → ℝ) × W.lvl 0 → W.lvl 0}

/-- The region `{δ ∈ O 0}` near `0` where a solution germ agrees with `sol`. -/
lemma exists_agree (h : IsSc0ContractionGerm Ct G Bm)
    {V : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct} {δ : (Fin n → ℝ) → W.lvl 0}
    (hsol : IsSolGerm G Bm V δ) :
    ∃ u : Set (Fin n → ℝ), IsOpen u ∧ (0 : Fin n → ℝ) ∈ u ∧
      ∀ a ∈ V.U 0, a ∈ h.toContractionGerm.N 0 → a ∈ u → δ a = h.toContractionGerm.sol a := by
  set 𝒞 := h.toContractionGerm with h𝒞
  obtain ⟨hδ0, hδzero, hδsol⟩ := hsol
  have hcont : ContinuousOn δ (V.U 0) :=
    (hδ0.continuousOn 0).congr fun a _ => (levelMap_zero δ a).symm
  obtain ⟨u, hu, hueq⟩ := (continuousOn_iff'.1 hcont) (𝒞.O 0) (𝒞.O_open 0)
  have hu0 : (0 : Fin n → ℝ) ∈ u := by
    have : (0 : Fin n → ℝ) ∈ δ ⁻¹' 𝒞.O 0 ∩ V.U 0 :=
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

end Common

theorem A_to_B : A → B := by
  intro hA n W Ct G Bm hPQ h
  have hC : IsQuadrantLike (ScBanach.const (Fin n → ℝ)) Ct := hPQ.isQuadrantLike
  have hCG : IsQuadrantLike (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ) := hC.paramProd W
  set 𝒞 := h.toContractionGerm with h𝒞
  have hVC : ∀ (V : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct) m, ∀ a ∈ V.U m, a ∈ Ct :=
    fun V m a ha => by
      have := V.U_subset m ha
      rwa [ScBanach.const_lvlSet] at this
  refine ⟨fun k hk V δ hsol => ?_, fun hf V δ hsol => ?_⟩
  · -- sc^k
    have hB : IsSckGerm k G Bm := isSckGerm_of_contractionMap hCG hk
    obtain ⟨s, -, hsA⟩ := hA.1 𝒞 hPQ hB
    obtain ⟨u, hu, hu0, hagree⟩ := exists_agree h hsol
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
    have h1 : IsSckGerm k V' 𝒞.sol :=
      have hsub : ∀ m, V'.U m ⊆ (𝒞.germ hC s).U m := fun m a ha => ⟨ha.2.1, hVC V m a ha.1⟩
      IsSckGerm.mono hC hsub hsA
    refine IsSckGerm.congr hC (fun a ha => ?_) h1
    exact (hagree a ha.1 (𝒞.N_anti_le (by omega) ha.2.1) ha.2.2).symm
  · -- sc-smooth: one diagonal germ for all `k`
    have hB : IsScSmoothGerm G Bm := fun k => isSckGerm_of_contractionMap hCG (hf k)
    choose s hs using fun k => hA.2.1 𝒞 hPQ hB k
    obtain ⟨u, hu, hu0, hagree⟩ := exists_agree h hsol
    let t : ℕ → ℕ := fun m => ∑ j ∈ Finset.range (m + 1), s j
    have hst : ∀ j m, j ≤ m → s j ≤ t m := fun j m hjm =>
      Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hjm))
    have ht : ∀ m, t m ≤ t (m + 1) := fun m => by
      show ∑ j ∈ Finset.range (m + 1), s j ≤ ∑ j ∈ Finset.range (m + 1 + 1), s j
      rw [Finset.sum_range_succ _ (m + 1)]
      omega
    -- the germ where `δ = sol`
    let Vu : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct :=
      { U := fun m => V.U m ∩ (𝒞.N m ∩ u)
        nested := fun m x hx => ⟨V.nested m x hx.1, 𝒞.N_anti m hx.2.1, hx.2.2⟩
        zero_mem := fun m => ⟨V.zero_mem m, 𝒞.N_zero _, hu0⟩
        relOpen := fun m => by
          obtain ⟨T, hT, hVm⟩ := V.relOpen m
          refine ⟨T ∩ (𝒞.N m ∩ u), hT.inter ((𝒞.N_open _).inter hu), ?_⟩
          rw [hVm]
          ext a
          simp only [Set.mem_inter_iff]
          tauto }
    -- the diagonal germ
    let V' : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct :=
      { U := fun m => V.U m ∩ (𝒞.N (m + t m) ∩ u)
        nested := fun m x hx => ⟨V.nested m x hx.1,
          𝒞.N_anti_le (by have := ht m; omega) hx.2.1, hx.2.2⟩
        zero_mem := fun m => ⟨V.zero_mem m, 𝒞.N_zero _, hu0⟩
        relOpen := fun m => by
          obtain ⟨T, hT, hVm⟩ := V.relOpen m
          refine ⟨T ∩ (𝒞.N (m + t m) ∩ u), hT.inter ((𝒞.N_open _).inter hu), ?_⟩
          rw [hVm]
          ext a
          simp only [Set.mem_inter_iff]
          tauto }
    refine ⟨V', fun m a ha => ha.1, fun k => isSckGerm_of_levels k hC V' δ fun j => ?_⟩
    refine ⟨germInter Vu (𝒞.germ hC (s j)), fun m a ha => ?_, ?_⟩
    · have hN := ha.2.1
      have h1 : 𝒞.N (m + j + t (m + j)) ⊆ 𝒞.N (m + j) := 𝒞.N_anti_le (by omega)
      have h2 : 𝒞.N (m + j + t (m + j)) ⊆ 𝒞.N (m + j + s j) :=
        𝒞.N_anti_le (by have := hst j (m + j) (by omega); omega)
      exact ⟨⟨ha.1, h1 hN, ha.2.2⟩, h2 hN, hVC V _ a ha.1⟩
    · have h1 : IsSckGerm j (germInter Vu (𝒞.germ hC (s j))) 𝒞.sol :=
        IsSckGerm.mono hC (fun m _ hx => hx.2) (hs j).2
      refine IsSckGerm.congr hC (fun a ha => ?_) h1
      exact (hagree a ha.1.1 ha.1.2.1 ha.1.2.2).symm

/-- **A ⇒ B** directly through A's text-form `theorem_3_35_of_isSc0ContractionGerm_preprint`. -/
theorem A_to_B_text : A → B := by
  intro hA n W Ct G Bm hPQ h
  refine ⟨fun k hk V δ hsol => ?_, fun hf V δ hsol => ?_⟩
  · obtain ⟨hδ0, hδzero, hδsol⟩ := hsol
    exact (hA.2.2.2.1 hPQ.isQuadrantLike h hδ0 hδzero fun a ha => (hδsol a ha).2).1 k hk
  · obtain ⟨hδ0, hδzero, hδsol⟩ := hsol
    exact (hA.2.2.2.1 hPQ.isQuadrantLike h hδ0 hδzero fun a ha => (hδsol a ha).2).2 hf

#rt_check RoundTrip.V3_32.A_to_B [Polyfold.theorem_3_35_preprint, Polyfold.theorem_3_35_smooth_preprint,
  Polyfold.theorem_3_35_isScSmoothGerm_preprint, Polyfold.theorem_3_35_of_isSc0ContractionGerm_preprint,
  Polyfold.isSckGerm_contractionMap_iff]
#rt_check RoundTrip.V3_32.A_to_B_text [Polyfold.theorem_3_35_preprint, Polyfold.theorem_3_35_smooth_preprint,
  Polyfold.theorem_3_35_isScSmoothGerm_preprint, Polyfold.theorem_3_35_of_isSc0ContractionGerm_preprint,
  Polyfold.isSckGerm_contractionMap_iff]

end RoundTrip.V3_32
