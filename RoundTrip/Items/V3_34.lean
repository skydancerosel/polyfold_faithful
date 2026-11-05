import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_34

/-!
Round trip for V3_34 (Theorem 3.38).  `A` is the conjunction of the types of
`Polyfold.theorem_3_38`, `Polyfold.StabilityData.exists_of_scPlus`,
`Polyfold.StabilityData.pushB_isSc0ContractionGerm`, `Polyfold.scPlusRemainder_contraction`,
`Polyfold.StabilityData.pushMap_eq_zero_iff` and `Polyfold.StabilityData.finrank_Cs_eq_finrank_Zs`
(no universe parameters; `StabilityData`, `split`, `fiber`, `pushMap` are definitions).

Glue for `A → B`:
* B's sc⁺-germ `s` has an `ℝᴺ`-component; it is absorbed into the basic germ,
  `f' = f + (s_ℝᴺ, 0)` (still basic with the same `B`), so `f + s = fsum f'` with the `W`-part
  `s_W` of `s`; `exists_of_scPlus` (in `A`) gives the data `𝒮` of Theorem 3.38 for `s_W`.
* `theorem_3_38` (in `A`): `𝒮.pushMap f'` is a basic germ on `𝒮.pushGerm` over
  `(ℝⁿ × C) ⊕ X¹` with target `(ℝᴺ × Z) ⊕ X¹`.  B wants literally `ℝ^{n'}` and `ℝ^{N'}`: transport
  along linear isomorphisms `ℝⁿ × C ≃ ℝ^{n + dim C}`, `ℝᴺ × Z ≃ ℝ^{N + dim Z}` (generic lemma
  `IsBasicGerm.transport`, with the partial quadrant `C̃ × C` transported too).
* B's strong bundle isomorphism is the level-`0` coordinate change `(ψ, Ψ) = (split₀, fiber₀)`
  followed by these isomorphisms, on `U = G₀` (`ScOperator.isStrongBundleIso_prodMap`); its
  push-forward of `f + s`, read on level `1`, is the transported `pushMap f'`
  (`pushMap_eq_levelMap_pushMap₀`).
* `n − N = n' − N'` is `finrank_Cs_eq_finrank_Zs` (in `A`).
-/

namespace RoundTrip.V3_34
open Polyfold

/-- The project's statement: Theorem 3.38 and the lemmas cited with it. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_38 ∧ type_of% @Polyfold.StabilityData.exists_of_scPlus ∧
    type_of% @Polyfold.StabilityData.pushB_isSc0ContractionGerm ∧
    type_of% @Polyfold.scPlusRemainder_contraction ∧
    type_of% @Polyfold.StabilityData.pushMap_eq_zero_iff ∧
    type_of% @Polyfold.StabilityData.finrank_Cs_eq_finrank_Zs

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_38, @Polyfold.StabilityData.exists_of_scPlus,
    @Polyfold.StabilityData.pushB_isSc0ContractionGerm, @Polyfold.scPlusRemainder_contraction,
    @Polyfold.StabilityData.pushMap_eq_zero_iff, @Polyfold.StabilityData.finrank_Cs_eq_finrank_Zs⟩

/-! ### Transport of basic germs along linear isomorphisms of the finite-dimensional factors -/

section Transport

variable {P₁ P₂ Q₁ Q₂ : Type} [NormedAddCommGroup P₁] [NormedSpace ℝ P₁] [FiniteDimensional ℝ P₁]
  [NormedAddCommGroup P₂] [NormedSpace ℝ P₂] [FiniteDimensional ℝ P₂]
  [NormedAddCommGroup Q₁] [NormedSpace ℝ Q₁] [FiniteDimensional ℝ Q₁]
  [NormedAddCommGroup Q₂] [NormedSpace ℝ Q₂] [FiniteDimensional ℝ Q₂]

/-- `e × id : P₁ ⊕ X → P₂ ⊕ X` as an sc-operator. -/
noncomputable def parOp (e : P₁ →L[ℝ] P₂) (X : ScBanach) :
    ScOperator (ScBanach.paramProd P₁ X) (ScBanach.paramProd P₂ X) where
  lvl m := e.prodMap (ContinuousLinearMap.id ℝ (X m))
  incl_comm _ _ := rfl

@[simp] lemma parOp_apply (e : P₁ →L[ℝ] P₂) (X : ScBanach) (m : ℕ)
    (p : (ScBanach.paramProd P₁ X) m) : parOp e X m p = ((e p.1, p.2) : P₂ × X m) := rfl

lemma parOp_symm_parOp (e : P₁ ≃L[ℝ] P₂) (X : ScBanach) (m : ℕ) (p : (ScBanach.paramProd P₁ X) m) :
    parOp (e.symm : P₂ →L[ℝ] P₁) X m (parOp (e : P₁ →L[ℝ] P₂) X m p) = p :=
  Prod.ext (e.symm_apply_apply p.1) rfl

lemma parOp_parOp_symm (e : P₁ ≃L[ℝ] P₂) (X : ScBanach) (m : ℕ) (p : (ScBanach.paramProd P₂ X) m) :
    parOp (e : P₁ →L[ℝ] P₂) X m (parOp (e.symm : P₂ →L[ℝ] P₁) X m p) = p :=
  Prod.ext (e.apply_symm_apply p.1) rfl

/-- `levelMap (g ∘ S) = levelMap g ∘ S_m` for an sc-operator `S`. -/
lemma levelMap_comp_op {E F G : ScBanach} (g : F 0 → G 0) (S : ScOperator E F) (m : ℕ) (x : E m) :
    levelMap (g ∘ S 0) m x = levelMap g m (S m x) := by
  unfold levelMap
  rw [Function.comp_apply, S.toBase_comm]

/-- A partial quadrant transported along a linear isomorphism. -/
lemma isPartialQuadrant_preimage (e : P₁ ≃L[ℝ] P₂) {Ct : Set P₁}
    (h : IsPartialQuadrant (ScBanach.const P₁) Ct) :
    IsPartialQuadrant (ScBanach.const P₂) (e.symm ⁻¹' Ct) := by
  obtain ⟨k, W₀, T, hT⟩ := h
  let I : ScIso (ScBanach.const P₂) (ScBanach.const P₁) :=
    { lvl := fun _ => e.symm
      incl_comm := fun _ _ => rfl }
  exact ⟨k, W₀, I.trans T, by rw [hT]; rfl⟩

/-- The germ `G` transported along `e × id`. -/
noncomputable def germT (e : P₁ ≃L[ℝ] P₂) {X : ScBanach} {Ct : Set P₁}
    (G : ScNbhdGerm (ScBanach.paramProd P₁ X) (Ct ×ˢ Set.univ)) :
    ScNbhdGerm (ScBanach.paramProd P₂ X) ((e.symm ⁻¹' Ct) ×ˢ Set.univ) where
  U m := parOp (e.symm : P₂ →L[ℝ] P₁) X m ⁻¹' G.U m
  nested m y hy := by
    show parOp (e.symm : P₂ →L[ℝ] P₁) X m ((ScBanach.paramProd P₂ X).incl m y) ∈ G.U m
    rw [← (parOp (e.symm : P₂ →L[ℝ] P₁) X).incl_comm]
    exact G.nested m _ hy
  zero_mem m := by
    show parOp (e.symm : P₂ →L[ℝ] P₁) X m 0 ∈ G.U m
    rw [map_zero]; exact G.zero_mem m
  relOpen m := by
    obtain ⟨O, hO, hU⟩ := G.relOpen m
    refine ⟨parOp (e.symm : P₂ →L[ℝ] P₁) X m ⁻¹' O,
      hO.preimage (parOp (e.symm : P₂ →L[ℝ] P₁) X m).continuous, ?_⟩
    rw [ScBanach.paramProd_lvlSet] at hU ⊢
    rw [hU]
    ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true]
    exact Iff.rfl

lemma germT_mapsTo (e : P₁ ≃L[ℝ] P₂) {X : ScBanach} {Ct : Set P₁}
    (G : ScNbhdGerm (ScBanach.paramProd P₁ X) (Ct ×ˢ Set.univ)) :
    (germT e G).MapsToGerm G (parOp (e.symm : P₂ →L[ℝ] P₁) X 0) := by
  intro m y hy
  rw [ScOperator.levelMap_eq]
  exact hy

/-- **Basic germs transport along linear isomorphisms** of the parameter space and of the
finite-dimensional part of the target. -/
theorem IsBasicGerm.transport (eP : P₁ ≃L[ℝ] P₂) (eQ : Q₁ ≃L[ℝ] Q₂) {X : ScBanach} {Ct : Set P₁}
    (hC : IsPartialQuadrant (ScBanach.const P₁) Ct)
    {G : ScNbhdGerm (ScBanach.paramProd P₁ X) (Ct ×ˢ Set.univ)} {g : P₁ × X 0 → Q₁ × X 0}
    {B : P₁ × X 0 → X 0} (h : IsBasicGerm Ct G g B) :
    IsBasicGerm (eP.symm ⁻¹' Ct) (germT eP G)
      (parOp (eQ : Q₁ →L[ℝ] Q₂) X 0 ∘ g ∘ parOp (eP.symm : P₂ →L[ℝ] P₁) X 0)
      (B ∘ parOp (eP.symm : P₂ →L[ℝ] P₁) X 0) := by
  have hQL1 : IsQuadrantLike (ScBanach.paramProd P₁ X) (Ct ×ˢ Set.univ) :=
    hC.isQuadrantLike.paramProd X
  have hQL2 : IsQuadrantLike (ScBanach.paramProd P₂ X) ((eP.symm ⁻¹' Ct) ×ˢ Set.univ) :=
    (isPartialQuadrant_preimage eP hC).isQuadrantLike.paramProd X
  have h00 : parOp (eP.symm : P₂ →L[ℝ] P₁) X 0 ((0 : P₂), (0 : X 0)) = ((0 : P₁), (0 : X 0)) := by
    rw [parOp_apply, map_zero]
  refine ⟨fun k => ?_, ?_, fun y hy => ?_, ?_⟩
  · exact IsSckGerm.operator_comp hQL2 (parOp (eQ : Q₁ →L[ℝ] Q₂) X)
      (IsSckGerm.comp hQL2 hQL1 (h.isScSmooth k) ((parOp _ X).isSckGerm k _ hQL2)
        (germT_mapsTo eP G))
  · show parOp (eQ : Q₁ →L[ℝ] Q₂) X 0 (g (parOp (eP.symm : P₂ →L[ℝ] P₁) X 0 0)) = 0
    rw [map_zero, h.f_zero, map_zero]
  · exact h.snd_eq _ hy
  · refine ⟨IsSc0Germ.comp h.contraction.isSc0 ((parOp _ X).isSc0Germ _) (germT_mapsTo eP G), ?_,
      fun ε hε m => ?_⟩
    · show B (parOp (eP.symm : P₂ →L[ℝ] P₁) X 0 ((0 : P₂), (0 : X 0))) = 0
      rw [h00]; exact h.contraction.B_zero
    · obtain ⟨r, hr, hrB⟩ := h.contraction.contraction ε hε m
      set c := ‖(eP.symm : P₂ →L[ℝ] P₁)‖ with hcdef
      have hc : 0 ≤ c := norm_nonneg _
      refine ⟨r / (c + 1), by positivity, fun a ha har w w' hw hw' => ?_⟩
      have hr' : r / (c + 1) ≤ r := div_le_self hr.le (by linarith)
      have hea : ‖eP.symm a‖ < r := by
        have h1 : ‖eP.symm a‖ ≤ c * ‖a‖ := (eP.symm : P₂ →L[ℝ] P₁).le_opNorm a
        have h2 : c * ‖a‖ ≤ c * (r / (c + 1)) := mul_le_mul_of_nonneg_left har.le hc
        have h3 : c * (r / (c + 1)) < r := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
        linarith
      obtain ⟨hmem, hest⟩ := hrB (eP.symm a) ha hea w w' (hw.trans_le hr') (hw'.trans_le hr')
      refine ⟨hmem, ?_⟩
      have e1 : levelB (B ∘ parOp (eP.symm : P₂ →L[ℝ] P₁) X 0) m (a, w) =
          levelB B m (eP.symm a, w) :=
        levelMap_comp_op (E := ScBanach.paramProd P₂ X) B (parOp _ X) m (a, w)
      have e2 : levelB (B ∘ parOp (eP.symm : P₂ →L[ℝ] P₁) X 0) m (a, w') =
          levelB B m (eP.symm a, w') :=
        levelMap_comp_op (E := ScBanach.paramProd P₂ X) B (parOp _ X) m (a, w')
      rw [e1, e2]
      exact hest

end Transport

theorem A_to_B : A → B := by
  intro hA n N W Ct G f Bf s hPQ hf hs hs0
  obtain ⟨h338, hex, -, -, -, hfin⟩ := hA
  have hC : IsQuadrantLike (ScBanach.const (Fin n → ℝ)) Ct := hPQ.isQuadrantLike
  have hCG : IsQuadrantLike (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ) := hC.paramProd W
  -- the `W`-part of `s`, and the data `𝒮` of Theorem 3.38 for it
  have hsW : IsScSmoothGerm (E := ScBanach.paramProd (Fin n → ℝ) W) (F := W.shift) G
      (fun x => (s x).2) := fun k =>
    (IsSckGerm.operator_comp hCG (ScBanach.wPartOp (Fin N → ℝ) W) (hs k)).congr hCG
      fun _ _ => rfl
  have hsW0 : ((s 0).2 : W.lvl 1) = 0 := by rw [hs0]; rfl
  obtain ⟨𝒮, h𝒮G, h𝒮s⟩ := hex hsW hsW0
  -- the basic germ `f' = f + (s_ℝᴺ, 0)`
  let f' : (Fin n → ℝ) × W.lvl 0 → (Fin N → ℝ) × W.lvl 0 :=
    fun x => f x + ScBanach.qPartOp (Fin N → ℝ) W 0 (s x)
  have hf'G : IsBasicGerm Ct G f' Bf :=
    { isScSmooth := by
        have hq : IsScSmoothGerm (E := ScBanach.paramProd (Fin n → ℝ) W)
            (F := ScBanach.paramProd (Fin N → ℝ) W) G (ScBanach.qPartOp (Fin N → ℝ) W 0 ∘ s) :=
          fun k => IsSckGerm.operator_comp hCG (ScBanach.qPartOp (Fin N → ℝ) W) (hs k)
        have hp := IsScSmoothGerm.pair (F := ScBanach.paramProd (Fin N → ℝ) W)
          (G := ScBanach.paramProd (Fin N → ℝ) W) hCG hf.isScSmooth hq
        intro k
        exact (IsSckGerm.operator_comp hCG (ScBanach.paramProd (Fin N → ℝ) W).addOp
          (hp k)).congr hCG fun x _ => rfl
      f_zero := by
        change f 0 + ScBanach.qPartOp (Fin N → ℝ) W 0 (s 0) = 0
        rw [hf.f_zero, hs0, map_zero, add_zero]
      snd_eq := fun x hx => by
        change (f x + ScBanach.qPartOp (Fin N → ℝ) W 0 (s x)).2 = x.2 - Bf x
        rw [Prod.snd_add, hf.snd_eq x hx, ScBanach.qPartOp_apply, add_zero]
      contraction := hf.contraction }
  have hf' : IsBasicGerm Ct 𝒮.G f' Bf := by rw [h𝒮G]; exact hf'G
  have hbasic := h338 𝒮 hC hf'
  -- `f + s = fsum f'`
  have hfsum : ∀ x, f x + (ScBanach.paramProd (Fin N → ℝ) W).toBase 1 (s x) = 𝒮.fsum f' x := by
    intro x
    rw [StabilityData.fsum_apply, h𝒮s, ScBanach.paramProd_toBase]
    change f x + ((s x).1, W.toBase 1 (s x).2) =
      f x + ((s x).1, (0 : W.lvl 0)) + ((0 : Fin N → ℝ), W.toBase 1 (s x).2)
    rw [add_assoc]
    congr 1
    ext <;> simp
  -- the finite-dimensional factors as `ℝ^{n'}`, `ℝ^{N'}`
  obtain ⟨eP⟩ : Nonempty (((Fin n → ℝ) × 𝒮.Cs) ≃L[ℝ]
      (Fin (n + Module.finrank ℝ 𝒮.Cs) → ℝ)) :=
    ⟨ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])⟩
  obtain ⟨eQ⟩ : Nonempty (((Fin N → ℝ) × 𝒮.Zs) ≃L[ℝ]
      (Fin (N + Module.finrank ℝ 𝒮.Zs) → ℝ)) :=
    ⟨ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])⟩
  have hPQ' : IsPartialQuadrant (ScBanach.const (Fin (n + Module.finrank ℝ 𝒮.Cs) → ℝ))
      (eP.symm ⁻¹' (Ct ×ˢ Set.univ)) :=
    isPartialQuadrant_preimage eP (hPQ.const_prod_univ 𝒮.Cs)
  -- the linear coordinate changes
  let S := (parOp (eP : ((Fin n → ℝ) × 𝒮.Cs) →L[ℝ] (Fin (n + Module.finrank ℝ 𝒮.Cs) → ℝ)) 𝒮.XB).comp 𝒮.split₀
  let S' := 𝒮.glue₀.comp (parOp (eP.symm : (Fin (n + Module.finrank ℝ 𝒮.Cs) → ℝ) →L[ℝ] ((Fin n → ℝ) × 𝒮.Cs)) 𝒮.XB)
  let T := (parOp (eQ : ((Fin N → ℝ) × 𝒮.Zs) →L[ℝ] (Fin (N + Module.finrank ℝ 𝒮.Zs) → ℝ)) 𝒮.XB).comp (𝒮.fiber₀ (Q := Fin N → ℝ))
  let T' := (𝒮.fiberInv₀ (Q := Fin N → ℝ)).comp (parOp (eQ.symm : (Fin (N + Module.finrank ℝ 𝒮.Zs) → ℝ) →L[ℝ] ((Fin N → ℝ) × 𝒮.Zs)) 𝒮.XB)
  obtain ⟨OG, hOG, hGU⟩ := G.relOpen 0
  rw [ScBanach.paramProd_lvlSet] at hGU
  have hU : IsRelOpenInQuadrant (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ) (G.U 0) :=
    ⟨hPQ.prod_univ W, OG, hOG, hGU⟩
  have hS'fst : ∀ y : (ScBanach.paramProd (Fin (n + Module.finrank ℝ 𝒮.Cs) → ℝ) 𝒮.XB) 0,
      (S' 0 y).1 = (eP.symm y.1).1 := fun _ => rfl
  have hU' : IsRelOpenInQuadrant (ScBanach.paramProd (Fin (n + Module.finrank ℝ 𝒮.Cs) → ℝ) 𝒮.XB)
      ((eP.symm ⁻¹' (Ct ×ˢ Set.univ)) ×ˢ Set.univ) (S' 0 ⁻¹' G.U 0) := by
    refine ⟨hPQ'.prod_univ 𝒮.XB, S' 0 ⁻¹' OG, hOG.preimage (S' 0).continuous, ?_⟩
    rw [hGU]
    ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true]
    rw [hS'fst]
  have hS'S : ∀ u, S' 0 (S 0 u) = u := fun u => by
    show 𝒮.glue₀ 0 (parOp (eP.symm : (Fin (n + Module.finrank ℝ 𝒮.Cs) → ℝ) →L[ℝ] ((Fin n → ℝ) × 𝒮.Cs)) 𝒮.XB 0
      (parOp (eP : ((Fin n → ℝ) × 𝒮.Cs) →L[ℝ] (Fin (n + Module.finrank ℝ 𝒮.Cs) → ℝ)) 𝒮.XB 0 (𝒮.split₀ 0 u))) = u
    rw [parOp_symm_parOp, 𝒮.glue₀_split₀]
  have hSS' : ∀ u', S 0 (S' 0 u') = u' := fun u' => by
    show parOp (eP : ((Fin n → ℝ) × 𝒮.Cs) →L[ℝ] (Fin (n + Module.finrank ℝ 𝒮.Cs) → ℝ)) 𝒮.XB 0 (𝒮.split₀ 0 (𝒮.glue₀ 0
      (parOp (eP.symm : (Fin (n + Module.finrank ℝ 𝒮.Cs) → ℝ) →L[ℝ] ((Fin n → ℝ) × 𝒮.Cs)) 𝒮.XB 0 u'))) = u'
    rw [𝒮.split₀_glue₀, parOp_parOp_symm]
  have hT'T : ∀ k, T' 0 (T 0 k) = k := fun k => by
    show 𝒮.fiberInv₀ 0 (parOp (eQ.symm : (Fin (N + Module.finrank ℝ 𝒮.Zs) → ℝ) →L[ℝ] ((Fin N → ℝ) × 𝒮.Zs)) 𝒮.XB 0
      (parOp (eQ : ((Fin N → ℝ) × 𝒮.Zs) →L[ℝ] (Fin (N + Module.finrank ℝ 𝒮.Zs) → ℝ)) 𝒮.XB 0 (𝒮.fiber₀ 0 k))) = k
    rw [parOp_symm_parOp, 𝒮.fiberInv₀_fiber₀]
  have hTT' : ∀ k', T 0 (T' 0 k') = k' := fun k' => by
    show parOp (eQ : ((Fin N → ℝ) × 𝒮.Zs) →L[ℝ] (Fin (N + Module.finrank ℝ 𝒮.Zs) → ℝ)) 𝒮.XB 0 (𝒮.fiber₀ 0 (𝒮.fiberInv₀ 0
      (parOp (eQ.symm : (Fin (N + Module.finrank ℝ 𝒮.Zs) → ℝ) →L[ℝ] ((Fin N → ℝ) × 𝒮.Zs)) 𝒮.XB 0 k'))) = k'
    rw [𝒮.fiber₀_fiberInv₀, parOp_parOp_symm]
  have hiso := ScOperator.isStrongBundleIso_prodMap hU hU' S S' T T'
    (fun u hu => by show S' 0 (S 0 u) ∈ G.U 0; rw [hS'S]; exact hu)
    (fun _ hu' => hu') (fun u _ => hS'S u) (fun u' _ => hSS' u') hT'T hTT'
  -- the level-raised push-forward
  have hf'sc : IsScSmoothGerm (E := ScBanach.paramProd (Fin n → ℝ) W)
      (F := ScBanach.paramProd (Fin N → ℝ) W) 𝒮.G f' := hf'.isScSmooth
  have hP0 : IsSc0Germ 𝒮.pushGerm₀ (𝒮.pushMap₀ f') := 𝒮.pushMap₀_isScSmoothGerm hC hf'sc 0
  refine ⟨n + Module.finrank ℝ 𝒮.Cs, N + Module.finrank ℝ 𝒮.Zs, 𝒮.XB,
    eP.symm ⁻¹' (Ct ×ˢ Set.univ), G.U 0, S' 0 ⁻¹' G.U 0,
    fun p => (S 0 p.1, T 0 p.2), fun p => (S' 0 p.1, T' 0 p.2),
    hPQ', hU, G.zero_mem 0, subset_rfl, hU', hiso, map_zero (S 0), ?_, ?_⟩
  · refine ⟨germT eP 𝒮.pushGerm,
      parOp (eQ : ((Fin N → ℝ) × 𝒮.Zs) →L[ℝ] (Fin (N + Module.finrank ℝ 𝒮.Zs) → ℝ)) 𝒮.XB.shift 0 ∘ 𝒮.pushMap f' ∘ parOp (eP.symm : (Fin (n + Module.finrank ℝ 𝒮.Cs) → ℝ) →L[ℝ] ((Fin n → ℝ) × 𝒮.Cs)) 𝒮.XB.shift 0,
      𝒮.pushB Bf ∘ parOp (eP.symm : (Fin (n + Module.finrank ℝ 𝒮.Cs) → ℝ) →L[ℝ] ((Fin n → ℝ) × 𝒮.Cs)) 𝒮.XB.shift 0,
      IsBasicGerm.transport eP eQ (hPQ.const_prod_univ 𝒮.Cs) hbasic, fun x hx => ?_⟩
    set y : 𝒮.E' 0 := parOp (eP.symm : (Fin (n + Module.finrank ℝ 𝒮.Cs) → ℝ) →L[ℝ] ((Fin n → ℝ) × 𝒮.Cs)) 𝒮.XB.shift 0 x with hydef
    have hy : 𝒮.glue 0 y ∈ 𝒮.G.U 1 := hx
    have hinc : S' 0 (x.1, 𝒮.XB.incl 0 x.2) =
        (ScBanach.paramProd (Fin n → ℝ) W).incl 0 (𝒮.glue 0 y) := by
      show 𝒮.glue₀ 0 (𝒮.E₀'.incl 0 y) = _
      rw [← 𝒮.glue₀.incl_comm]
      rfl
    refine ⟨?_, ?_⟩
    · show S' 0 (x.1, 𝒮.XB.incl 0 x.2) ∈ G.U 0
      rw [hinc, ← h𝒮G]
      exact 𝒮.G.nested 0 _ hy
    · have key : 𝒮.pushMap₀ f' (𝒮.E₀'.toBase 1 y) =
          (𝒮.F₀' (Fin N → ℝ)).toBase 1 (𝒮.pushMap f' y) := by
        rw [𝒮.pushMap_eq_levelMap_pushMap₀ hf'sc hx,
          hP0.toBase_levelMap (show y ∈ 𝒮.pushGerm₀.U 1 from hx)]
      have hS'x : S' 0 (x.1, 𝒮.XB.incl 0 x.2) = 𝒮.glue₀ 0 (𝒮.E₀'.toBase 1 y) := by
        rw [ScBanach.paramProd_toBase]
        rfl
      show T 0 (f (S' 0 (x.1, 𝒮.XB.incl 0 x.2)) +
          (ScBanach.paramProd (Fin N → ℝ) W).toBase 1 (s (S' 0 (x.1, 𝒮.XB.incl 0 x.2)))) = _
      rw [hfsum, hS'x]
      change parOp (eQ : ((Fin N → ℝ) × 𝒮.Zs) →L[ℝ] (Fin (N + Module.finrank ℝ 𝒮.Zs) → ℝ)) 𝒮.XB 0 (𝒮.pushMap₀ f' (𝒮.E₀'.toBase 1 y)) = _
      rw [key, ScBanach.paramProd_toBase]
      rfl
  · rw [← hfin 𝒮]
    push_cast
    ring

#rt_check RoundTrip.V3_34.A_to_B [Polyfold.theorem_3_38, Polyfold.StabilityData.exists_of_scPlus,
  Polyfold.StabilityData.pushB_isSc0ContractionGerm, Polyfold.scPlusRemainder_contraction,
  Polyfold.StabilityData.pushMap_eq_zero_iff, Polyfold.StabilityData.finrank_Cs_eq_finrank_Zs]

end RoundTrip.V3_34
