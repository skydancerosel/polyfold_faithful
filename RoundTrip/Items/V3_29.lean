import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_29

/-!
Round trip for V3_29 (Lemma 3.32).  `A` is the conjunction of the types of
`Polyfold.ContractionGerm.sol_isSckGerm` and `Polyfold.ContractionGerm.isSckGerm_succ_of_next`
(no universe parameters).

`A → B`.  B only asks for *some* sc⁰-contraction germ `f⁽ʲ⁾` of class sc^{min(k−j,1)} with
solution germ `T^jδ`; it does not prescribe the iterate of Lemma 3.31.  So the trivial germ
`f⁽ʲ⁾(a, w) = w − T^jδ(a)` (`B_j(a, w) = T^jδ(a)`, a contraction with constant `0`) is a witness
as soon as `T^jδ` is sc^{min(k−j,1)}; B is therefore the regularity statement
"`T^jδ` is sc^{k−j} near `0`", which follows from `δ` being sc^k:
* A's `sol_isSckGerm` (with `j := k`) for the working form `h.toContractionGerm` gives `sol`
  sc^k on some `germ s`; B's solution germ `δ` agrees with `sol` near `0` (as in V3_30), so `δ`
  is sc^k on `V' = V ∩ germ s ∩ {δ ∈ O 0}`.
* `exists_iterTan`: if `δ` is sc^k on a germ in a finite-dimensional `C̃`, then `T^jδ`
  (B's `iterTan`, with `fderivWithin` and `lvlLift`) is sc^{k−j} on a germ in `T^jC̃`: B's
  `tanMap` is the project's tangent germ `Tδ` transported along `P × P = TP`
  (`constTangentOp`), its derivative being `fderivWithin` by uniqueness on the convex `C̃`.
-/

namespace RoundTrip.V3_29
open Polyfold

/-- The project's statement: Lemma 3.32 / Theorem 3.33 as one induction, and its step. -/
def A : Prop :=
  type_of% @Polyfold.ContractionGerm.sol_isSckGerm ∧
  type_of% @Polyfold.ContractionGerm.isSckGerm_succ_of_next

theorem A_holds : A :=
  ⟨@Polyfold.ContractionGerm.sol_isSckGerm, @Polyfold.ContractionGerm.isSckGerm_succ_of_next⟩

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

/-- `f = w − B(a, w)` is of class sc^k when `B` is. -/
theorem isSckGerm_contractionMap {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {W : ScBanach} {Ct : Set P}
    {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ Set.univ)} {Bm : P × W.lvl 0 → W.lvl 0}
    {k : ℕ} (hCG : IsQuadrantLike (ScBanach.paramProd P W) (Ct ×ˢ Set.univ))
    (hk : IsSckGerm k G Bm) : IsSckGerm k G (contractionMap Bm) := by
  have h2 : IsSckGerm k G ((ScBanach.sndOp (ScBanach.const P) W) 0) :=
    ScOperator.isSckGerm k _ G hCG
  have h3 := (IsSckGerm.pair hCG h2 hk).operator_comp hCG (subOp W)
  exact IsSckGerm.congr hCG (fun p _ => rfl) h3

lemma lvlLift_eq {W : ScBanach} {m : ℕ} {x : W.lvl 0} {y : W.lvl m} (h : W.toBase m y = x) :
    lvlLift W m x = y := by
  have hex : ∃ y : W.lvl m, W.toBase m y = x := ⟨y, h⟩
  unfold lvlLift
  rw [dif_pos hex]
  exact W.toBase_injective m (hex.choose_spec.trans h.symm)

lemma lvlLift_zero (W : ScBanach) (m : ℕ) : lvlLift W m 0 = 0 := lvlLift_eq (map_zero _)

lemma isQuadrantLike_iter : ∀ (j : ℕ) (X : PQ), IsQuadrantLike (ScBanach.const X.P) X.C →
    IsQuadrantLike (ScBanach.const (PQ.T^[j] X).P) (PQ.T^[j] X).C
  | 0, _, h => h
  | j + 1, X, h => isQuadrantLike_iter j X.T h.prod_univ_const

lemma iterTan_zero : ∀ (j : ℕ) (X : PQ) (W : ScBanach) (δ : X.P → W.lvl 0), δ 0 = 0 →
    iterTan j X W δ 0 = 0
  | 0, _, _, _, h => h
  | j + 1, X, W, δ, h => iterTan_zero j X.T W.tangent (tanMap X W δ) (by
      show ((lvlLift W 1 (δ 0), fderivWithin ℝ δ X.C 0 0) : W.lvl 1 × W.lvl 0) = 0
      rw [h, lvlLift_zero, map_zero]
      rfl)

/-- B's `tanMap` is the project's tangent germ: `δ(v) ∈ W₁` and `Dδ(v) = fderivWithin`. -/
lemma tanMap_eq {X : PQ} {W : ScBanach} {δ : X.P → W.lvl 0}
    {V : ScNbhdGerm (ScBanach.const X.P) X.C} (hC : IsQuadrantLike (ScBanach.const X.P) X.C)
    (h1 : IsSc1Germ (F := W) V δ) {q : X.P × X.P} (hq : q.1 ∈ V.U 1) :
    tangentMapGerm (F := W) V δ q = tanMap X W δ q := by
  have hD := h1.isSc1GermWith_scDerivGerm
  change ((levelMap (E := ScBanach.const X.P) (F := W) δ 1 q.1, scDerivGerm (F := W) V δ q.1 q.2) :
    W.lvl 1 × W.lvl 0) = (lvlLift W 1 (δ q.1), fderivWithin ℝ δ X.C q.1 q.2)
  refine Prod.ext ?_ ?_
  · refine (lvlLift_eq ?_).symm
    rw [hD.isSc0.toBase_levelMap hq, ScBanach.const_toBase]
  · have hd := hD.hasFDerivWithinAt q.1 hq
    have e : (ScBanach.const X.P).toBase 1 = ContinuousLinearMap.id ℝ X.P :=
      ContinuousLinearMap.ext fun x => ScBanach.const_toBase X.P 1 x
    rw [e, ContinuousLinearMap.comp_id] at hd
    simp only [ContinuousLinearMap.coe_id', Function.comp_id] at hd
    obtain ⟨O, hO, hU⟩ := V.relOpen 1
    rw [ScBanach.const_lvlSet] at hU
    have hqO : q.1 ∈ O := by have := hq; rw [hU] at this; exact this.1
    have hqC : q.1 ∈ X.C := by have := hq; rw [hU] at this; exact this.2
    rw [hU, Set.inter_comm] at hd
    have hd' := (hasFDerivWithinAt_inter (hO.mem_nhds hqO)).1 hd
    obtain ⟨-, hconv, hint⟩ := isQuadrantLike_const_iff.1 hC
    rw [hd'.fderivWithin (uniqueDiffWithinAt_convex hconv hint (subset_closure hqC))]

/-- **The iterated tangent**: if `δ` is sc^k on a germ in `C̃`, then `T^jδ` is sc^{k−j} on a germ
in `T^jC̃` (for `j ≤ k`). -/
theorem exists_iterTan : ∀ (j : ℕ) (X : PQ) (W : ScBanach) (δ : X.P → W.lvl 0)
    (V : ScNbhdGerm (ScBanach.const X.P) X.C) (k : ℕ),
    IsQuadrantLike (ScBanach.const X.P) X.C → j ≤ k → IsSckGerm (F := W) k V δ →
    ∃ Vj : ScNbhdGerm (ScBanach.const (PQ.T^[j] X).P) (PQ.T^[j] X).C,
      IsSckGerm (F := ScBanach.tangent^[j] W) (k - j) Vj (iterTan j X W δ)
  | 0, X, W, δ, V, k, _, _, h => ⟨V, h⟩
  | j + 1, X, W, δ, V, k, hC, hjk, h => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨h1, hT⟩ := isSckGerm_succ_iff.1 h
    let V1 : ScNbhdGerm (ScBanach.const (X.P × X.P)) (X.C ×ˢ Set.univ) :=
      { U := fun m => V.U (m + 1) ×ˢ Set.univ
        nested := fun m q hq => ⟨V.nested (m + 1) q.1 hq.1, Set.mem_univ _⟩
        zero_mem := fun m => ⟨V.zero_mem (m + 1), Set.mem_univ _⟩
        relOpen := fun m => by
          obtain ⟨O, hO, hU⟩ := V.relOpen (m + 1)
          rw [ScBanach.const_lvlSet] at hU
          refine ⟨O ×ˢ Set.univ, hO.prod isOpen_univ, ?_⟩
          rw [ScBanach.const_lvlSet, hU, Set.prod_inter_prod, Set.univ_inter] }
    have hC1 : IsQuadrantLike (ScBanach.const (X.P × X.P)) (X.C ×ˢ Set.univ) := hC.prod_univ_const
    have hmaps : V1.MapsToGerm V.tangent (constTangentOp X.P 0) := by
      intro m q hq
      rw [ScOperator.levelMap_eq, constTangentOp_apply]
      exact ⟨hq.1, Set.mem_univ _⟩
    have h2 : IsSckGerm (F := W.tangent) k' V1 (tangentMapGerm (F := W) V δ ∘ constTangentOp X.P 0) :=
      IsSckGerm.comp hC1 hC.tangentSet hT ((constTangentOp X.P).isSckGerm k' _ hC1) hmaps
    have h3 : IsSckGerm (F := W.tangent) k' V1 (tanMap X W δ) := by
      refine IsSckGerm.congr hC1 (fun q hq => ?_) h2
      rw [Function.comp_apply, constTangentOp_apply]
      exact tanMap_eq hC h1 hq.1
    obtain ⟨Vj, hVj⟩ := exists_iterTan j X.T W.tangent (tanMap X W δ) V1 k' hC1 (by omega) h3
    exact ⟨Vj, by rw [Nat.add_sub_add_right]; exact hVj⟩

/-- **The trivial contraction germ** `f(a, w) = w − δ(a)`: an sc⁰-contraction germ (constant `0`)
of the class of `δ`, with solution germ `δ`. -/
theorem exists_trivial_contraction (Y : PQ) (Wj : ScBanach) (δj : Y.P → Wj.lvl 0)
    (Vj : ScNbhdGerm (ScBanach.const Y.P) Y.C) (n' : ℕ)
    (hC : IsQuadrantLike (ScBanach.const Y.P) Y.C) (h : IsSckGerm (F := Wj) n' Vj δj)
    (h0 : δj 0 = 0) :
    ∃ (Gj : ScNbhdGerm (ScBanach.paramProd Y.P Wj) (Y.C ×ˢ Set.univ))
      (Bj : Y.P × Wj.lvl 0 → Wj.lvl 0),
      IsSc0ContractionGerm Y.C Gj Bj ∧ IsSckGerm (F := Wj) n' Gj (contractionMap Bj) ∧
        IsSolGerm Gj Bj Vj δj := by
  let Gj : ScNbhdGerm (ScBanach.paramProd Y.P Wj) (Y.C ×ˢ Set.univ) :=
    { U := fun m => {x | x.1 ∈ Vj.U m}
      nested := fun m x hx => Vj.nested m x.1 hx
      zero_mem := fun m => Vj.zero_mem m
      relOpen := fun m => by
        obtain ⟨O, hO, hU⟩ := Vj.relOpen m
        rw [ScBanach.const_lvlSet] at hU
        refine ⟨Prod.fst ⁻¹' O, hO.preimage continuous_fst, ?_⟩
        rw [ScBanach.paramProd_lvlSet]
        ext x
        simp only [Set.mem_ofPred_eq, hU, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
          Set.mem_univ, and_true] }
  have hCG : IsQuadrantLike (ScBanach.paramProd Y.P Wj) (Y.C ×ˢ Set.univ) := hC.paramProd Wj
  have hmaps : Gj.MapsToGerm Vj ((ScBanach.fstOp (ScBanach.const Y.P) Wj) 0) := by
    intro m x hx
    rw [ScOperator.levelMap_eq]
    exact hx
  have hBj : IsSckGerm (F := Wj) n' Gj (δj ∘ (ScBanach.fstOp (ScBanach.const Y.P) Wj) 0) :=
    IsSckGerm.comp hCG hC h ((ScBanach.fstOp _ _).isSckGerm n' Gj hCG) hmaps
  refine ⟨Gj, fun x => δj x.1, ⟨hBj.isSc0, h0, fun ε hε m => ?_⟩,
    isSckGerm_contractionMap hCG hBj, h.isSc0, h0, fun a ha => ⟨ha, sub_self _⟩⟩
  obtain ⟨O, hO, hU⟩ := Vj.relOpen m
  rw [ScBanach.const_lvlSet] at hU
  have h0O : (0 : Y.P) ∈ O := by have := Vj.zero_mem m; rw [hU] at this; exact this.1
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO _ h0O
  refine ⟨ρ, hρ, fun a ha har w w' _ _ => ⟨?_, ?_⟩⟩
  · show a ∈ Vj.U m
    rw [hU]
    exact ⟨hball (by rwa [Metric.mem_ball, dist_zero_right]), ha⟩
  · have e : ∀ w : Wj.lvl m, levelB (fun x : Y.P × Wj.lvl 0 => δj x.1) m (a, w) =
        Function.invFun (Wj.toBase m) (δj a) := fun w => by
      unfold levelB levelMap
      rw [ScBanach.paramProd_toBase]
    rw [e w, e w', sub_self, norm_zero]
    positivity

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
  intro hA P _ _ _ W Ct G Bm k j hPQ h hk hjk V δ hsol _
  have hC : IsQuadrantLike (ScBanach.const P) Ct := hPQ.isQuadrantLike
  have hCG : IsQuadrantLike (ScBanach.paramProd P W) (Ct ×ˢ Set.univ) := hC.paramProd W
  set 𝒞 := h.toContractionGerm with h𝒞
  have hB : IsSckGerm k 𝒞.G 𝒞.B := isSckGerm_of_contractionMap hCG hk
  -- A: the solution germ is sc^k on some `germ s`
  obtain ⟨s, hsA⟩ := hA.1 k 𝒞 hC le_rfl hB
  -- so is B's `δ`, near `0`
  obtain ⟨u, hu, hu0, hagree⟩ := exists_agree h hsol
  let V' : ScNbhdGerm (ScBanach.const P) Ct :=
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
  have hVC : ∀ m, ∀ a ∈ V.U m, a ∈ Ct := fun m a ha => by
    have := V.U_subset m ha
    rwa [ScBanach.const_lvlSet] at this
  have hδk : IsSckGerm (F := W) k V' δ := by
    have hsub : ∀ m, V'.U m ⊆ (𝒞.germ hC s).U m := fun m a ha => ⟨ha.2.1, hVC m a ha.1⟩
    refine IsSckGerm.congr hC (fun a ha => ?_) (IsSckGerm.mono hC hsub hsA)
    exact (hagree a ha.1 (𝒞.N_anti_le (by omega) ha.2.1) ha.2.2).symm
  -- the iterated tangent and the trivial contraction germ
  obtain ⟨Vj, hVj⟩ := exists_iterTan j ⟨P, Ct⟩ W δ V' k hC hjk hδk
  obtain ⟨Gj, Bj, h1, h2, h3⟩ := exists_trivial_contraction (PQ.T^[j] ⟨P, Ct⟩) _ _ Vj (k - j)
    (isQuadrantLike_iter j ⟨P, Ct⟩ hC) hVj (iterTan_zero j ⟨P, Ct⟩ W δ hsol.2.1)
  exact ⟨Gj, Bj, Vj, h1, h2.of_le (min_le_left _ _), h3⟩

#rt_check RoundTrip.V3_29.A_to_B [Polyfold.ContractionGerm.sol_isSckGerm,
  Polyfold.ContractionGerm.isSckGerm_succ_of_next]

end RoundTrip.V3_29
