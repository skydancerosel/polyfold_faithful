import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_28

/-!
Round trip for V3_28 (Lemma 3.31).  Refreshed 2026-11-02 against HEAD (new conjunct:
`f⁽¹⁾` is a Definition 3.28 contraction germ).  `A` is the conjunction of the types of
`Polyfold.ContractionGerm.lemma_3_31`, `Polyfold.ContractionGerm.nextB_isSckGerm`,
`Polyfold.ContractionGerm.next_sol` and (new) `Polyfold.ContractionGerm.isSc0ContractionGerm_next`
(no universe parameters; `next`, `nextB`, `tangentShuffle` are vocabulary).

Glue for `A → B` (from the conjuncts `lemma_3_31` and `isSc0ContractionGerm_next`):
* The working form: `h.toContractionGerm`, with its parameter regions `N m` shrunk
  (`shrinkN`) into `⋂_{i ≤ m} V_i` and into the region `{δ ∈ O 0}`, so that B's arbitrary
  solution germ `δ` is `sol` there and `δ` sc^j on `V` gives `sol` sc^j on `germ 0`.
* `G⁽¹⁾ := nextG 0`: B's `B⁽¹⁾` (written with `lvlLift` and B's arbitrary `DB`) agrees with the
  project's `nextB DB` on `U⁽¹⁾₀`; so regularity is `lemma_3_31` (and `w − B⁽¹⁾` is then sc^k).
* Definition 3.28 for `B⁽¹⁾` (every `ε`, every level): at the audit this was not in A and was
  re-proved here (Lemma 3.9 on level `m` with an arbitrary `ε`); A now contains it
  (`isSc0ContractionGerm_next`, the audit's glue moved into the project), and it is transported to
  B's `B⁽¹⁾` along the agreement on `U⁽¹⁾₀` (`IsSc0Germ.levelMap_congr`).
* Solution germ: `Tδ = (δ(v), Dδ(v)b)` is the solution `sol` of `next 0` on `(N 2 ∩ C̃) × P`
  (`lemma_3_31`), since B's arbitrary `Dδ` equals the project's `solDeriv` there (uniqueness of
  derivatives on the quadrant).

`B → A` is not proved: A covers every working-form `ContractionGerm` on a quadrant-like `C̃` and
speaks about the specific construction `next s` (its germ, regions, `nextB_isSckGerm`, the formula
of `next.sol`), none of which follows from B's existential `G⁽¹⁾`.

`#rt_check_soft`: A's `lemma_3_31` and `isSc0ContractionGerm_next` are stated in terms of the
definition `next`, whose proof field `isSc0` is proved with `nextB_isSckGerm`; that banned theorem is
reached only through this field.
-/

namespace RoundTrip.V3_28
open Polyfold Set Filter Topology

/-- The project's statement: Lemma 3.31 and its two parts. -/
def A : Prop :=
  type_of% @Polyfold.ContractionGerm.lemma_3_31 ∧
  type_of% @Polyfold.ContractionGerm.nextB_isSckGerm ∧
  type_of% @Polyfold.ContractionGerm.next_sol ∧
  type_of% @Polyfold.ContractionGerm.isSc0ContractionGerm_next

theorem A_holds : A :=
  ⟨@Polyfold.ContractionGerm.lemma_3_31, @Polyfold.ContractionGerm.nextB_isSckGerm,
    @Polyfold.ContractionGerm.next_sol, @Polyfold.ContractionGerm.isSc0ContractionGerm_next⟩

section Glue

/-- The sc-operator `W ⊕ W → W`, `(u, v) ↦ u − v`. -/
noncomputable def subOp (W : ScBanach) : ScOperator (W.prod W) W where
  lvl m := ContinuousLinearMap.fst ℝ (W m) (W m) - ContinuousLinearMap.snd ℝ (W m) (W m)
  incl_comm m x := by
    change W.incl m (x.1 - x.2) = W.incl m x.1 - W.incl m x.2
    exact map_sub _ _ _

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}

/-- `B` is of class sc^k when `f = w − B(a, w)` is. -/
theorem isSckGerm_of_contractionMap
    {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {Bm : P × W.lvl 0 → W.lvl 0}
    {k : ℕ} (hCG : IsQuadrantLike (ScBanach.paramProd P W) (Ct ×ˢ univ))
    (hk : IsSckGerm k G (contractionMap Bm)) : IsSckGerm k G Bm := by
  have h2 : IsSckGerm k G ((ScBanach.sndOp (ScBanach.const P) W) 0) :=
    ScOperator.isSckGerm k _ G hCG
  have h3 := (IsSckGerm.pair hCG h2 hk).operator_comp hCG (subOp W)
  refine IsSckGerm.congr hCG (fun p _ => ?_) h3
  change p.2 - (p.2 - Bm p) = Bm p
  abel

/-- `f = w − B(a, w)` is of class sc^k when `B` is. -/
theorem isSckGerm_contractionMap
    {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {Bm : P × W.lvl 0 → W.lvl 0}
    {k : ℕ} (hCG : IsQuadrantLike (ScBanach.paramProd P W) (Ct ×ˢ univ))
    (hk : IsSckGerm k G Bm) : IsSckGerm k G (contractionMap Bm) := by
  have h2 : IsSckGerm k G ((ScBanach.sndOp (ScBanach.const P) W) 0) :=
    ScOperator.isSckGerm k _ G hCG
  have h3 := (IsSckGerm.pair hCG h2 hk).operator_comp hCG (subOp W)
  exact IsSckGerm.congr hCG (fun p _ => rfl) h3

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma lvlLift_eq {m : ℕ} {x : W.lvl 0} {y : W.lvl m} (h : W.toBase m y = x) :
    lvlLift W m x = y := by
  have hex : ∃ y : W.lvl m, W.toBase m y = x := ⟨y, h⟩
  unfold lvlLift
  rw [dif_pos hex]
  exact W.toBase_injective m (hex.choose_spec.trans h.symm)

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
    simp only [mem_inter_iff]
    tauto

/-- A working-form contraction germ with smaller parameter regions `N' m ⊆ N m`. -/
def shrinkN (𝒞 : ContractionGerm P Ct W) (N' : ℕ → Set P) (hopen : ∀ m, IsOpen (N' m))
    (hzero : ∀ m, (0 : P) ∈ N' m) (hanti : ∀ m, N' (m + 1) ⊆ N' m) (hsub : ∀ m, N' m ⊆ 𝒞.N m) :
    ContractionGerm P Ct W where
  B := 𝒞.B
  G := 𝒞.G
  B_zero := 𝒞.B_zero
  isSc0 := 𝒞.isSc0
  N := N'
  N_open := hopen
  N_zero := hzero
  N_anti := hanti
  O := 𝒞.O
  K := 𝒞.K
  O_open := 𝒞.O_open
  K_closed := 𝒞.K_closed
  K_zero := 𝒞.K_zero
  K_sub := 𝒞.K_sub
  K_incl := 𝒞.K_incl
  mem_G m a ha := 𝒞.mem_G m a ⟨hsub m ha.1, ha.2⟩
  mapsTo m a ha := 𝒞.mapsTo m a ⟨hsub m ha.1, ha.2⟩
  contr m a ha := 𝒞.contr m a ⟨hsub m ha.1, ha.2⟩

end Glue

theorem A_to_B : A → B := by
  intro hA P _ _ _ W Ct G Bm k j hPQ h hk1 hk V δ hsol hj1 hj DB hDB Dδ hDδ
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hC : IsQuadrantLike (ScBanach.const P) Ct := hPQ.isQuadrantLike
  have hCG : IsQuadrantLike (ScBanach.paramProd P W) (Ct ×ˢ univ) := hC.paramProd W
  have hC' := ContractionGerm.isQuadrantLike_next hC W
  set 𝒞₀ := h.toContractionGerm with h𝒞₀
  obtain ⟨hδ0, hδzero, hδsol⟩ := hsol
  -- the region `{δ ∈ O 0}`
  have hcont : ContinuousOn δ (V.U 0) :=
    (hδ0.continuousOn 0).congr fun a _ => (levelMap_zero δ a).symm
  obtain ⟨u, hu, hueq⟩ := (continuousOn_iff'.1 hcont) (𝒞₀.O 0) (𝒞₀.O_open 0)
  have hu0 : (0 : P) ∈ u := by
    have : (0 : P) ∈ δ ⁻¹' 𝒞₀.O 0 ∩ V.U 0 :=
      ⟨by rw [mem_preimage, hδzero]; exact 𝒞₀.zero_mem_O 0, V.zero_mem 0⟩
    rw [hueq] at this
    exact this.1
  -- the open sets of `V`
  choose OV hOV hVO using V.relOpen
  have hVO' : ∀ i, V.U i = (OV i : Set P) ∩ Ct := fun i => by
    rw [hVO i, ScBanach.const_lvlSet]
  let N' : ℕ → Set P := fun m => 𝒞₀.N m ∩ ((⋂ i ∈ Finset.range (m + 1), (OV i : Set P)) ∩ u)
  have hN'V : ∀ m, ∀ i ≤ m, ∀ a ∈ N' m, a ∈ Ct → a ∈ V.U i := fun m i hi a ha haC => by
    rw [hVO']
    exact ⟨mem_iInter₂.1 ha.2.1 i (Finset.mem_range.2 (by omega)), haC⟩
  have hN'open : ∀ m, IsOpen (N' m) := fun m =>
    (𝒞₀.N_open m).inter ((isOpen_biInter_finset fun i _ => hOV i).inter hu)
  have hN'zero : ∀ m, (0 : P) ∈ N' m := fun m => by
    refine ⟨𝒞₀.N_zero m, mem_iInter₂.2 fun i _ => ?_, hu0⟩
    have := V.zero_mem i
    rw [hVO'] at this
    exact this.1
  have hN'anti : ∀ m, N' (m + 1) ⊆ N' m := fun m a ha =>
    ⟨𝒞₀.N_anti m ha.1, mem_iInter₂.2 fun i hi => mem_iInter₂.1 ha.2.1 i
      (Finset.mem_range.2 (by have := Finset.mem_range.1 hi; omega)), ha.2.2⟩
  set 𝒞 := shrinkN 𝒞₀ N' hN'open hN'zero hN'anti (fun m _ ha => ha.1) with h𝒞
  have hDB' : IsSc1GermWith 𝒞.G 𝒞.B DB := hDB
  -- `δ = sol` on `N' 0 ∩ C̃`
  have hagree : ∀ a ∈ 𝒞.N 0 ∩ Ct, δ a = 𝒞.sol a := fun a ha => by
    have haV : a ∈ V.U 0 := hN'V 0 0 le_rfl a ha.1 ha.2
    have hO : δ a ∈ 𝒞.O 0 := by
      have : a ∈ u ∩ V.U 0 := ⟨ha.1.2.2, haV⟩
      rw [← hueq] at this
      exact this.1
    have hfix : 𝒞.B (a, δ a) = δ a := by
      have := (hδsol a haV).2
      change δ a - Bm (a, δ a) = 0 at this
      exact (sub_eq_zero.1 this).symm
    exact 𝒞.eq_sol ha hO hfix
  have hagree1 : ∀ v ∈ 𝒞.N 1 ∩ Ct, lvlLift W 1 (δ v) = 𝒞.fixLvl 1 v := fun v hv =>
    lvlLift_eq (by rw [𝒞.toBase_fixLvl 1 hv, hagree v ⟨𝒞.N_anti 0 hv.1, hv.2⟩])
  -- the hypotheses of Lemma 3.31
  have hs : IsSckGerm j (𝒞.germ hC 0) 𝒞.sol := by
    have hsub : ∀ m, (𝒞.germ hC 0).U m ⊆ V.U m := fun m a ha =>
      hN'V m m le_rfl a ha.1 ha.2
    refine IsSckGerm.congr hC (fun a ha => hagree a ha) (IsSckGerm.mono hC hsub hj)
  have hk' : IsSckGerm (k' + 1) 𝒞.G 𝒞.B := isSckGerm_of_contractionMap hCG hk
  obtain ⟨hreg, hsolA⟩ := hA.1 𝒞 hC hDB' (k := k') (j := j) (s := 0) hk' hs
  -- B's `B⁽¹⁾` is the project's `nextB` on `U⁽¹⁾₀`
  have hEq : EqOn (𝒞.nextB DB) (B1 Bm DB δ) ((𝒞.nextG 0).U 0) := by
    rintro ⟨⟨v, b⟩, ⟨u', w⟩⟩ hq
    have hv1 : v ∈ 𝒞.N 1 ∩ Ct := ⟨hq.2, 𝒞.mem_Ct_of_mem_nextG hq⟩
    rw [ContractionGerm.nextB_apply]
    refine Prod.ext ?_ ?_
    · show levelB 𝒞.B 1 (v, u') = lvlLift W 1 (Bm (v, W.toBase 1 u'))
      have hvu : ((v, u') : (ScBanach.paramProd P W) 1) ∈ 𝒞.G.U 1 := hq.1
      refine (lvlLift_eq ?_).symm
      rw [𝒞.isSc0.toBase_levelMap hvu, ScBanach.paramProd_toBase]
      rfl
    · show DB (v, levelMap (E := ScBanach.const P) (F := W) 𝒞.sol 1 v) (b, w) =
        DB (v, lvlLift W 1 (δ v)) (b, w)
      rw [𝒞.levelMap_sol 1 hv1, hagree1 v hv1]
  have hreg' : IsSckGerm (min k' j) (𝒞.nextG 0) (B1 Bm DB δ) := IsSckGerm.congr hC' hEq hreg
  refine ⟨𝒞.nextG 0, fun m v b u' w hq => ⟨hq.1, ?_⟩, ⟨hreg'.isSc0, ?_, fun ε hε m => ?_⟩, ?_, ?_⟩
  · exact hN'V (m + 1 + 0) (m + 1) (by omega) v hq.2 (𝒞.mem_Ct_of_mem_nextG hq)
  · -- `B⁽¹⁾(0) = 0`
    have e0 := hEq ((𝒞.nextG 0).zero_mem 0)
    change 𝒞.nextB DB ((0 : P × P), (0 : W.tangent.lvl 0)) =
      B1 Bm DB δ ((0 : P × P), (0 : W.tangent.lvl 0)) at e0
    show B1 Bm DB δ ((0 : P × P), (0 : W.tangent.lvl 0)) = 0
    rw [← e0]
    exact 𝒞.nextB_zero
  · -- Definition 3.28 for `B⁽¹⁾`: A's `isSc0ContractionGerm_next`, transported along `hEq`
    have hc := (hA.2.2.2 𝒞 hC hDB' (h : IsSc0ContractionGerm Ct 𝒞.G 𝒞.B) 0).contraction ε hε m
    obtain ⟨r, hr, H⟩ := hc
    refine ⟨r, hr, fun a ha har w₁ w₂ hw₁ hw₂ => ?_⟩
    obtain ⟨hmem₁, hest⟩ := H a ha har w₁ w₂ hw₁ hw₂
    obtain ⟨hmem₂, -⟩ := H a ha har w₂ w₁ hw₂ hw₁
    refine ⟨hmem₁, ?_⟩
    have e₁ : levelB (B1 Bm DB δ) m (a, w₁) = levelB (𝒞.nextB DB) m (a, w₁) :=
      (IsSc0Germ.levelMap_congr hEq hmem₁).symm
    have e₂ : levelB (B1 Bm DB δ) m (a, w₂) = levelB (𝒞.nextB DB) m (a, w₂) :=
      (IsSc0Germ.levelMap_congr hEq hmem₂).symm
    rw [e₁, e₂]
    exact hest
  · rw [Nat.add_sub_cancel]
    exact isSckGerm_contractionMap hC' hreg'
  · -- the solution germ `Tδ`
    set 𝒩 := 𝒞.next hC hDB' 0 with h𝒩
    have hCP : IsQuadrantLike (ScBanach.const (P × P)) (Ct ×ˢ univ) := hC.prod_univ_const
    have hsolN := 𝒩.isSolutionGerm_germ hCP 0
    have hsolC1 := 𝒞.isSc1GermWith_sol hC hDB'
    -- B's `Dδ` is the project's `solDeriv` on `N 2 ∩ C̃`
    have hDeq : ∀ v ∈ 𝒞.N 2 ∩ Ct, Dδ v = 𝒞.solDeriv (D := DB) v := fun v hv => by
      let K := germInter V (𝒞.germ hC 1)
      have h1 : IsSc1GermWith K δ Dδ := hDδ.mono fun m _ hx => hx.1
      have h2 : IsSc1GermWith K δ (𝒞.solDeriv (D := DB)) :=
        (hsolC1.mono (G₁' := K) fun m _ hx => hx.2).congr fun a ha =>
          (hagree a ⟨𝒞.N_anti 0 ha.2.1, ha.2.2⟩).symm
      have hvK : v ∈ K.U 1 := ⟨hN'V 2 1 (by omega) v hv.1 hv.2, hv.1, hv.2⟩
      exact h1.eq_of_uniqueDiffWithinAt h2 hvK (K.uniqueDiffWithinAt hC 1 hvK)
    have hTδ : EqOn (Tδ δ Dδ) 𝒩.sol ((𝒩.germ hCP 0).U 0) := by
      rintro ⟨v, b⟩ hq
      have hv : v ∈ 𝒞.N 2 ∩ Ct := ⟨hq.1.1, hq.2.1⟩
      rw [hsolA (v, b) hv]
      show ((lvlLift W 1 (δ v), Dδ v b) : W.lvl 1 × W.lvl 0) =
        (levelMap (E := ScBanach.const P) (F := W) 𝒞.sol 1 v, 𝒞.solDeriv (D := DB) v b)
      have hv1 : v ∈ 𝒞.N 1 ∩ Ct := ⟨𝒞.N_anti 1 hv.1, hv.2⟩
      rw [𝒞.levelMap_sol 1 hv1, hagree1 v hv1, hDeq v hv]
    refine ⟨𝒩.germ hCP 0, fun m q hq =>
      ⟨hN'V (m + 0 + 2 + 0) (m + 1) (by omega) q.1 hq.1.1 hq.2.1, mem_univ _⟩, ?_, ?_,
      fun a ha => ?_⟩
    · exact hsolN.isSc0.congr fun q hq => (hTδ hq).symm
    · show ((lvlLift W 1 (δ 0), Dδ 0 0) : W.lvl 1 × W.lvl 0) = 0
      rw [hδzero, map_zero, lvlLift_eq (map_zero _)]
      rfl
    · have hmem : ((a, 𝒩.sol a) : (P × P) × W.tangent.lvl 0) ∈ (𝒞.nextG 0).U 0 := by
        have := hsolN.mem_G 0 a ha
        rwa [levelMap_zero] at this
      rw [hTδ ha]
      refine ⟨hmem, ?_⟩
      show 𝒩.sol a - B1 Bm DB δ (a, 𝒩.sol a) = 0
      rw [← hEq hmem]
      exact sub_eq_zero.2 (hsolN.fixed a ha).symm

#rt_check_soft RoundTrip.V3_28.A_to_B [Polyfold.ContractionGerm.lemma_3_31,
  Polyfold.ContractionGerm.nextB_isSckGerm, Polyfold.ContractionGerm.next_sol,
  Polyfold.ContractionGerm.isSc0ContractionGerm_next]

end RoundTrip.V3_28
