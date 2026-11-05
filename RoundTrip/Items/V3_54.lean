import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_54

open Set Filter Topology Function

noncomputable section

namespace RoundTrip.V3_54
open Polyfold

/-- The project's statement: `lemma_3_61` and the theorems of its proof listed with it
(`famInv_isSc0Germ`, `famInv_isSc1GermWith`, `famInv_hasFDerivWithinAt`, `famInv_isSckGerm`,
`exists_forall_norm_le_of_isCompact`); all already in `Type`, no universe parameters. -/
def A : Prop :=
  type_of% @Polyfold.lemma_3_61 ∧ type_of% @Polyfold.famInv_isSc0Germ ∧
    type_of% @Polyfold.famInv_isSc1GermWith ∧ type_of% @Polyfold.famInv_hasFDerivWithinAt ∧
    type_of% @Polyfold.famInv_isSckGerm ∧ type_of% @Polyfold.exists_forall_norm_le_of_isCompact

theorem A_holds : A :=
  ⟨@Polyfold.lemma_3_61, @Polyfold.famInv_isSc0Germ, @Polyfold.famInv_isSc1GermWith,
    @Polyfold.famInv_hasFDerivWithinAt, @Polyfold.famInv_isSckGerm,
    @Polyfold.exists_forall_norm_le_of_isCompact⟩

/-- `(e, 0)` is a smooth point of `G ⊕ E`. -/
lemma param_mem_smooth {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (E : ScBanach) (e : G) :
    ((e, 0) : (ScBanach.paramProd G E).lvl 0) ∈ (ScBanach.paramProd G E).smooth := by
  rw [ScScale.mem_smooth_iff]
  intro m
  exact ⟨((e, 0) : G × E.lvl m), by rw [ScBanach.paramProd_toBase, map_zero]⟩

/-- Lemma 3.61 in set form on `(Vo ∩ C̃) ⊕ X`, `0 ∈ Vo` (the germ `ofSet`), from the hypothesis
`h361` (the argument of the project's `famInv_isScSmooth_of`, re-done with the hypothesis). -/
theorem famInv_set (h361 : type_of% @Polyfold.lemma_3_61) {P : Type} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] {Ct : Set P} {X Y : ScBanach}
    (hC : IsPartialQuadrant (ScBanach.const P) Ct) {Vo : Set P}
    (hVo : IsOpen Vo) (hVo0 : (0 : P) ∈ Vo) {L : P → ScIso X Y}
    (hL : IsScSmooth (E := ScBanach.paramProd P X) (F := Y) ((Vo ∩ Ct) ×ˢ univ) (famMap L))
    (hc : ∀ m, ∃ c > 0, ∀ b ∈ Vo ∩ Ct, ∀ h : X m, c * ‖h‖ ≤ ‖L b m h‖) :
    IsScSmooth (E := ScBanach.paramProd P Y) (F := X) ((Vo ∩ Ct) ×ˢ univ) (famInv L) := by
  have hCq : IsQuadrantLike (ScBanach.const P) Ct := hC.isQuadrantLike
  have hOrel : ∃ O' : Set ((ScBanach.const P) 0), IsOpen O' ∧ Vo ∩ Ct = O' ∩ Ct := ⟨Vo, hVo, rfl⟩
  have h0O : (0 : (ScBanach.const P) 0) ∈ Vo ∩ Ct := ⟨hVo0, hCq.zero_mem⟩
  set Gv : ScNbhdGerm (ScBanach.const P) Ct := ScNbhdGerm.ofSet hOrel h0O with hGv
  have hUX := isRelOpenInQuadrant_param hC hVo X
  have hUY := isRelOpenInQuadrant_param hC hVo Y
  have hCX : IsQuadrantLike (ScBanach.paramProd P X) (Ct ×ˢ univ) :=
    (hC.prod_univ X).isQuadrantLike
  have hCY : IsQuadrantLike (ScBanach.paramProd P Y) (Ct ×ˢ univ) :=
    (hC.prod_univ Y).isQuadrantLike
  have h0X : (0 : (ScBanach.paramProd P X) 0) ∈ (Vo ∩ Ct) ×ˢ univ := ⟨h0O, mem_univ _⟩
  have h0Y : (0 : (ScBanach.paramProd P Y) 0) ∈ (Vo ∩ Ct) ×ˢ univ := ⟨h0O, mem_univ _⟩
  have hGvU : ∀ m, Gv.U m = Vo ∩ Ct := fun m => by
    rw [hGv, ScNbhdGerm.ofSet_U, ScBanach.const_lvlSet]
  have hG : IsScSmoothGerm (Gv.prodFull X) (famMap L) := fun k =>
    IsSckGerm.of_U_eq hCX (fun m => by rw [ScNbhdGerm.ofSet_U, ScBanach.paramProd_lvlSet,
      ScNbhdGerm.prodFull_U, hGvU]) ((hL.isScSmoothGerm hCX hUX.relOpen h0X) k)
  have hc' : ∀ m, ∃ c > 0, ∀ v ∈ Gv.U 0, ∀ h : X m, c * ‖h‖ ≤ ‖L v m h‖ := by
    rw [hGvU]; exact hc
  have h1 := h361 hC hG hc'
  have h2 : IsScSmoothGerm (ScNbhdGerm.ofSet hUY.relOpen h0Y) (famInv L) := fun k =>
    IsSckGerm.of_U_eq hCY (fun m => by rw [ScNbhdGerm.ofSet_U, ScBanach.paramProd_lvlSet,
      ScNbhdGerm.prodFull_U, hGvU]) (h1 k)
  exact h2.isScSmooth_ofSet hCY hUY.relOpen h0Y

/-- A ⇒ B: `lemma_3_61` is for germs at `0`; B's `V` is an arbitrary relatively open subset of
`C_G`.  sc-smoothness is local (`IsScSmooth.of_locally`); near a point `(e, k)` of `V ⊕ F` the
family is re-centred, `L'(u) = L(u + e)` on `(V − e) ∩ G(e)`, a relatively open neighbourhood of
`0` in the partial quadrant `C_e` (Definition 2.33; `recentreNbhd`, `isPartialQuadrant_partialQuadrantAtWith`),
Lemma 3.61 is applied there and the result is translated back by `(u, k) ↦ (u − e, k)`. -/
theorem A_to_B : A → B := by
  rintro ⟨h361, -⟩
  intro G _ _ _ CG V E F L hCG hV hΦ hc
  obtain ⟨O, hO, hVeq⟩ := hV.relOpen
  have hVdF : IsScDomain (ScBanach.paramProd G F) (V ×ˢ univ) := by
    rw [hVeq]; exact (isRelOpenInQuadrant_param hCG hO F).isScDomain
  have hVdE : IsScDomain (ScBanach.paramProd G E) (V ×ˢ univ) := by
    rw [hVeq]; exact (isRelOpenInQuadrant_param hCG hO E).isScDomain
  have hfun : (fun p : (ScBanach.paramProd G F).lvl 0 => (L p.1).symm.lvl 0 p.2) = famInv L := rfl
  rw [hfun]
  refine IsScSmooth.of_locally hVdF fun p hp => ?_
  obtain ⟨n, Wq, T, hT⟩ := hCG
  set e : G := p.1 with he
  have heV : e ∈ V := hp.1
  have heO : e ∈ O := by rw [hVeq] at heV; exact heV.1
  have heC : e ∈ CG := by rw [hVeq] at heV; exact heV.2
  set N : Set G := O ∩ recentreNbhd T e with hN
  have hNo : IsOpen N := hO.inter (isOpen_recentreNbhd T e)
  have heN : e ∈ N := ⟨heO, mem_recentreNbhd hT heC⟩
  refine ⟨N ×ˢ univ, hNo.prod isOpen_univ, ⟨heN, mem_univ _⟩, ?_⟩
  have hset : V ×ˢ (univ : Set (F.lvl 0)) ∩ N ×ˢ univ = (N ∩ CG) ×ˢ univ := by
    ext q
    simp only [mem_inter_iff, mem_prod, mem_univ, and_true]
    rw [hVeq]
    constructor
    · rintro ⟨⟨_, hC⟩, hNq⟩; exact ⟨hNq, hC⟩
    · rintro ⟨hNq, hC⟩; exact ⟨⟨hNq.1, hC⟩, hNq⟩
  rw [hset]
  -- the re-centred data
  set Ce : Set G := partialQuadrantAtWith T e with hCedef
  have hCe : IsPartialQuadrant (ScBanach.const G) Ce := isPartialQuadrant_partialQuadrantAtWith T e
  set O' : Set G := (fun u => u + e) ⁻¹' N with hO'def
  have hO' : IsOpen O' := hNo.preimage (continuous_id.add continuous_const)
  have h0O' : (0 : G) ∈ O' := by show 0 + e ∈ N; rw [zero_add]; exact heN
  have hrc := recentreNbhd_inter_eq (E := ScBanach.const G) hT e
  have hmem : ∀ u : G, u ∈ O' ∩ Ce ↔ u + e ∈ N ∩ CG := by
    intro u
    constructor
    · rintro ⟨hu, hCe'⟩
      refine ⟨hu, ?_⟩
      have : u + e ∈ recentreNbhd T e ∩ partialQuadrantAtWith T e :=
        ⟨hu.2, (add_mem_partialQuadrantAtWith_iff T e u).2 hCe'⟩
      rw [← hrc] at this; exact this.2
    · rintro ⟨hu, hC⟩
      refine ⟨hu, ?_⟩
      have : u + e ∈ recentreNbhd T e ∩ CG := ⟨hu.2, hC⟩
      rw [hrc] at this; exact (add_mem_partialQuadrantAtWith_iff T e u).1 this.2
  have hmemV : ∀ u : G, u ∈ O' ∩ Ce → u + e ∈ V := fun u hu => by
    have := (hmem u).1 hu; rw [hVeq]; exact ⟨this.1.1, this.2⟩
  set L' : G → ScIso E F := fun u => L (u + e) with hL'
  have hsmE := param_mem_smooth E e
  have hsmF := param_mem_smooth F e
  have hdE : IsScDomain (ScBanach.paramProd G E) ((O' ∩ Ce) ×ˢ univ) :=
    (isRelOpenInQuadrant_param hCe hO' E).isScDomain
  have hdF' : IsScDomain (ScBanach.paramProd G F) ((O' ∩ Ce) ×ˢ univ) :=
    (isRelOpenInQuadrant_param hCe hO' F).isScDomain
  have hdF : IsScDomain (ScBanach.paramProd G F) ((N ∩ CG) ×ˢ univ) :=
    (isRelOpenInQuadrant_param ⟨n, Wq, T, hT⟩ hNo F).isScDomain
  -- `(u, h) ↦ L'(u)h` is sc-smooth on `(O' ∩ C_e) ⊕ E`
  have hmapsE : MapsTo (fun q : (ScBanach.paramProd G E).lvl 0 =>
      q + ((e, 0) : (ScBanach.paramProd G E).lvl 0)) ((O' ∩ Ce) ×ˢ univ) (V ×ˢ univ) :=
    fun q hq => ⟨hmemV q.1 hq.1, mem_univ _⟩
  have hΦ' : IsScSmooth (E := ScBanach.paramProd G E) (F := F) ((O' ∩ Ce) ×ˢ univ)
      (famMap L') := by
    refine (IsScSmooth.comp hdE hVdE hΦ (isScSmooth_add_const hsmE hdE) hmapsE).congr hdE
      fun q _ => ?_
    simp only [Function.comp_apply, famMap, hL', Prod.fst_add, Prod.snd_add, add_zero]
  have hc' : ∀ m, ∃ c > 0, ∀ b ∈ O' ∩ Ce, ∀ h : E.lvl m, c * ‖h‖ ≤ ‖L' b m h‖ := by
    intro m
    obtain ⟨c, hc0, hcb⟩ := hc m
    exact ⟨c, hc0, fun b hb h => hcb (b + e) (hmemV b hb) h⟩
  have hinv' := famInv_set h361 hCe hO' h0O' hΦ' hc'
  -- translate back by `(u, k) ↦ (u − e, k)`
  have hmapsF : MapsTo (fun q : (ScBanach.paramProd G F).lvl 0 =>
      q - ((e, 0) : (ScBanach.paramProd G F).lvl 0)) ((N ∩ CG) ×ˢ univ) ((O' ∩ Ce) ×ˢ univ) := by
    intro q hq
    refine ⟨(hmem _).2 ?_, mem_univ _⟩
    show q.1 - e + e ∈ N ∩ CG
    rw [sub_add_cancel]; exact hq.1
  refine (IsScSmooth.comp hdF hdF' hinv' (isScSmooth_sub_const hsmF hdF) hmapsF).congr hdF
    fun q _ => ?_
  simp only [Function.comp_apply, famInv, hL', Prod.fst_sub, Prod.snd_sub, sub_zero,
    sub_add_cancel]

#rt_check RoundTrip.V3_54.A_to_B [Polyfold.lemma_3_61, Polyfold.famInv_isSc0Germ,
  Polyfold.famInv_isSc1GermWith, Polyfold.famInv_hasFDerivWithinAt, Polyfold.famInv_isSckGerm,
  Polyfold.exists_forall_norm_le_of_isCompact]
#rt_overlap RoundTrip.V3_54.A_to_B [Polyfold.lemma_3_61, Polyfold.famInv_isSc0Germ,
  Polyfold.famInv_isSc1GermWith, Polyfold.famInv_hasFDerivWithinAt, Polyfold.famInv_isSckGerm,
  Polyfold.exists_forall_norm_le_of_isCompact]

end RoundTrip.V3_54

end
