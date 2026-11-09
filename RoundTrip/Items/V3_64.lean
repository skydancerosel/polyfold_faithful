import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_64

/-! Round trip for V3_64 (Lemma 3.79: the contraction region).

`A` is the conjunction of the types of `Polyfold.ContractionData.exists_radii`,
`Polyfold.Radii.norm_sub_le` and `Polyfold.Radii.eq_τ` (no universe parameters).

`A → B`: the blind setting (with the given right inverse `Linv : ℝᴺ → Y` of `L`) is the project's
`ContractionData` for `Cp = {(k, y) | k + y ∈ C}`, `Up = {(k, y) | k + y ∈ U}` and
`B(k, y) = y − Linv f(k + y)` (glue copied from the proof of `theorem_3_8_22`, as in V3_65).
`exists_radii` gives radii `a, b`; the region claim is `Radii.region_sub`; `norm_sub_le` on the
region `R` gives `‖B(k, y) − B(k, y')‖ ≤ c₀‖y − y'‖ ≤ ½‖y − y'‖`; the injectivity
`f(k + y) = f(k + y') ⇒ y = y'` follows from the contraction.  `eq_τ` is not needed.

`B → A` is not proved: `A` is about abstract normalized data (`exists_radii` produces radii with
the full derivative bound `‖DB‖ ≤ ε/(2(1+ε))` on the region, `norm_sub_le` is the Lipschitz bound
in both variables for every admissible `Radii`, `eq_τ` is uniqueness against the project's `τ`),
while `B` gives only some small radii and the contraction in `y`. -/

open Set Filter Topology Function Module
open scoped ContDiff NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace RoundTrip.V3_64
open Polyfold

/-- The project's statement (no universe parameters). -/
def A : Prop :=
  (type_of% @Polyfold.ContractionData.exists_radii) ∧ (type_of% @Polyfold.Radii.norm_sub_le) ∧
    (type_of% @Polyfold.Radii.eq_τ)

theorem A_holds : A :=
  ⟨@Polyfold.ContractionData.exists_radii, @Polyfold.Radii.norm_sub_le, @Polyfold.Radii.eq_τ⟩

/-! ### Concrete glue: the blind setting is a `ContractionData` -/

section Glue

variable {n q N : ℕ} {L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)} {Y : Submodule ℝ (Fin n → ℝ)}

lemma quadC_convex (n q : ℕ) : Convex ℝ (quadC n q) := by
  intro x hx y hy s t hs ht _ i hi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg hs (hx i hi)) (mul_nonneg ht (hy i hi))

lemma quadC_interior_nonempty (n q : ℕ) : (interior (quadC n q)).Nonempty := by
  refine ⟨fun _ => 1, mem_interior.2 ⟨Metric.ball (fun _ => 1) 1, fun x hx i _ => ?_,
    Metric.isOpen_ball, Metric.mem_ball_self one_pos⟩⟩
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have := (norm_le_pi_norm (x - fun _ => (1 : ℝ)) i).trans_lt hx
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_lt] at this
  linarith [this.1]

/-- `K × Y ≅ ℝⁿ`, `(k, y) ↦ k + y`. -/
def addE (hKY : IsCompl (kerCLM L) Y) : (kerCLM L × Y) ≃L[ℝ] (Fin n → ℝ) :=
  (Submodule.prodEquivOfIsCompl _ _ hKY).toContinuousLinearEquiv

lemma addE_apply (hKY : IsCompl (kerCLM L) Y) (p : kerCLM L × Y) :
    addE hKY p = (p.1 : Fin n → ℝ) + p.2 := by
  change (Submodule.prodEquivOfIsCompl _ _ hKY).toContinuousLinearEquiv p = _
  rw [LinearEquiv.coe_toContinuousLinearEquiv', Submodule.coe_prodEquivOfIsCompl']

lemma L_ker (k : kerCLM L) : L k = 0 := LinearMap.mem_ker.1 k.2

lemma eq_of_L_eq (hKY : IsCompl (kerCLM L) Y) {y y' : Y} (h : L y = L y') : y = y' := by
  have h1 : L ((y : Fin n → ℝ) - y') = 0 := by rw [map_sub]; exact sub_eq_zero.2 h
  have h2 : ((y : Fin n → ℝ) - y') ∈ kerCLM L := LinearMap.mem_ker.2 h1
  have h3 : ((y : Fin n → ℝ) - y') ∈ Y := Y.sub_mem y.2 y'.2
  have h4 : ((y : Fin n → ℝ) - y') = 0 := by
    have := hKY.disjoint.le_bot ⟨h2, h3⟩
    simpa using this
  exact Subtype.ext (sub_eq_zero.1 h4)

/-- The domain `{(k, y) ∈ K × Y | k + y ∈ U}` of `B`. -/
def domB (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ)) (U : Set (Fin n → ℝ)) :
    Set (kerCLM L × Y) :=
  {p | (p.1 : Fin n → ℝ) + (p.2 : Fin n → ℝ) ∈ U}

/-- `Cp = {(k, y) | k + y ∈ C}`. -/
def Cp (q : ℕ) (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ)) :
    Set (kerCLM L × Y) :=
  {p | (p.1 : Fin n → ℝ) + (p.2 : Fin n → ℝ) ∈ quadC n q}

/-- `B(k, y) = y − Li f(k + y)` for a right inverse `Li : ℝᴺ → Y` of `L`. -/
def Bn (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (f : (Fin n → ℝ) → (Fin N → ℝ))
    (Li : (Fin N → ℝ) →L[ℝ] Y) (p : kerCLM L × Y) : Y :=
  p.2 - Li (f ((p.1 : Fin n → ℝ) + (p.2 : Fin n → ℝ)))

lemma mem_Cp_iff (p : kerCLM L × Y) :
    p ∈ Cp q L Y ↔ (p.1 : Fin n → ℝ) + (p.2 : Fin n → ℝ) ∈ quadC n q := Iff.rfl

/-- The blind setting gives the project's `ContractionData` (as in the proof of
`theorem_3_8_22`). -/
theorem contractionData {j : ℕ} {U : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → (Fin N → ℝ)}
    (hj : 1 ≤ j) (hU : ∃ O : Set (Fin n → ℝ), IsOpen O ∧ U = O ∩ quadC n q)
    (h0 : (0 : Fin n → ℝ) ∈ U) (hf : ContDiffOn ℝ j f U) (hf0 : f 0 = 0)
    (hL : HasFDerivWithinAt f L U 0)
    (hint : (interior (Subtype.val ⁻¹' quadC n q : Set (kerCLM L))).Nonempty)
    (hKY : IsCompl (kerCLM L) Y) (Li : (Fin N → ℝ) →L[ℝ] Y) (hLi : ∀ z, L (Li z) = z)
    {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ v ∈ kerCLM L, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖v‖ → (v ∈ quadC n q ↔ v + y ∈ quadC n q)) :
    ContractionData (Cp q L Y) (domB L Y U) (Bn L f Li) j := by
  set add := addE hKY with hadd_def
  have hadd : ∀ p : kerCLM L × Y, add p = (p.1 : Fin n → ℝ) + p.2 := addE_apply hKY
  have hadd' : ∀ p : kerCLM L × Y, (add : kerCLM L × Y →L[ℝ] Fin n → ℝ) p = (p.1 : Fin n → ℝ) + p.2 :=
    fun p => hadd p
  have hLiL : ∀ y : Y, Li (L y) = y := fun y => eq_of_L_eq hKY (hLi _)
  have hCp : Cp q L Y = add ⁻¹' quadC n q := by
    ext p; rw [mem_preimage, hadd]; rfl
  have hUp : domB L Y U = add ⁻¹' U := by
    ext p; rw [mem_preimage, hadd]; rfl
  have hB : Bn L f Li = fun p => p.2 - Li (f (add p)) := by
    funext p; simp only [Bn, hadd]
  rw [hCp, hUp, hB]
  obtain ⟨O, hO, hUO⟩ := hU
  have hCpconv : Convex ℝ (add ⁻¹' quadC n q) :=
    (quadC_convex n q).linear_preimage (add : kerCLM L × Y →ₗ[ℝ] Fin n → ℝ)
  have hCpint : (interior (add ⁻¹' quadC n q)).Nonempty := by
    have hpre : (add : kerCLM L × Y → Fin n → ℝ) ⁻¹' interior (quadC n q) =
        interior (add ⁻¹' quadC n q) := by
      simpa using add.toHomeomorph.preimage_interior (quadC n q)
    rw [← hpre]
    exact (quadC_interior_nonempty n q).preimage add.surjective
  have hUpeq : add ⁻¹' U = add ⁻¹' O ∩ add ⁻¹' quadC n q := by rw [hUO, preimage_inter]
  have h0Up : (0 : kerCLM L × Y) ∈ add ⁻¹' U := by
    show add 0 ∈ U; rw [map_zero]; exact h0
  have hUpUD : UniqueDiffWithinAt ℝ (add ⁻¹' U) 0 := by
    rw [hUpeq, inter_comm]
    refine (uniqueDiffWithinAt_convex hCpconv hCpint (subset_closure ?_)).inter
      ((hO.preimage add.continuous).mem_nhds ?_)
    · have := h0Up; rw [hUpeq] at this; exact this.2
    · have := h0Up; rw [hUpeq] at this; exact this.1
  have hBcd : ContDiffOn ℝ j (fun p : kerCLM L × Y => p.2 - Li (f (add p))) (add ⁻¹' U) := by
    have h1 : ContDiffOn ℝ j (f ∘ add) (add ⁻¹' U) :=
      hf.comp (add : kerCLM L × Y →L[ℝ] Fin n → ℝ).contDiff.contDiffOn fun p hp => hp
    exact contDiff_snd.contDiffOn.sub (h1.continuousLinearMap_comp Li)
  have hLf : HasFDerivWithinAt f L U (add 0) := by rw [map_zero]; exact hL
  have hBderiv : HasFDerivWithinAt (fun p : kerCLM L × Y => p.2 - Li (f (add p)))
      (ContinuousLinearMap.snd ℝ (kerCLM L) Y -
        Li.comp (L.comp (add : kerCLM L × Y →L[ℝ] Fin n → ℝ))) (add ⁻¹' U) 0 := by
    refine hasFDerivWithinAt_snd.sub ?_
    exact Li.hasFDerivAt.comp_hasFDerivWithinAt (x := (0 : kerCLM L × Y))
      (hLf.comp (0 : kerCLM L × Y) (add : kerCLM L × Y →L[ℝ] Fin n → ℝ).hasFDerivWithinAt
        fun p hp => hp)
  have hBderiv0 : ContinuousLinearMap.snd ℝ (kerCLM L) Y -
      Li.comp (L.comp (add : kerCLM L × Y →L[ℝ] Fin n → ℝ)) = 0 := by
    refine ContinuousLinearMap.ext fun p => ?_
    simp only [sub_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.comp_apply, zero_apply]
    rw [hadd', map_add, L_ker, zero_add, hLiL, sub_self]
  exact
    { convex := hCpconv
      interior_nonempty := hCpint
      relOpen := ⟨add ⁻¹' O, hO.preimage add.continuous, hUpeq⟩
      zero_mem_U := h0Up
      one_le := hj
      contDiffOn := hBcd
      B_zero := by
        change (0 : kerCLM L × Y).2 - Li (f (add 0)) = 0
        rw [map_zero, hf0, map_zero]; simp
      deriv_zero := by rw [hBderiv.fderivWithin hUpUD, hBderiv0]
      good := ⟨ε, hε, fun k y hy => by
        have := hgood k k.2 y y.2 hy
        rw [mem_preimage, mem_preimage, hadd, hadd]
        simpa using this⟩
      interior_K_nonempty := by
        have : {k : kerCLM L | ((k, 0) : kerCLM L × Y) ∈ add ⁻¹' quadC n q} =
            Subtype.val ⁻¹' quadC n q := by
          ext k
          rw [mem_ofPred_eq, mem_preimage, hadd]
          simp
        rw [this]; exact hint }

lemma good_abstract {ε : ℝ}
    (hgood : ∀ v ∈ kerCLM L, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖v‖ → (v ∈ quadC n q ↔ v + y ∈ quadC n q)) :
    ∀ (k : kerCLM L) (y : Y), ‖y‖ ≤ ε * ‖k‖ → ((k, 0) ∈ Cp q L Y ↔ (k, y) ∈ Cp q L Y) :=
  fun k y hy => by
    rw [mem_Cp_iff, mem_Cp_iff]
    simpa using hgood k k.2 y y.2 hy

lemma mem_V₀_iff {U : Set (Fin n → ℝ)} {B : kerCLM L × Y → Y}
    (S : Radii (Cp q L Y) (domB L Y U) B) (k : kerCLM L) :
    k ∈ S.V₀ ↔ (k : Fin n → ℝ) ∈ quadC n q ∧ ‖k‖ < S.a := by
  change ‖k‖ < S.a ∧ (k : Fin n → ℝ) + ((0 : Y) : Fin n → ℝ) ∈ quadC n q ↔ _
  simp [and_comm]

end Glue

/-! ### `A → B` -/

/-- `A` without its third conjunct `eq_τ` (whose statement mentions the definition `Radii.τ`). -/
def A' : Prop :=
  (type_of% @Polyfold.ContractionData.exists_radii) ∧ (type_of% @Polyfold.Radii.norm_sub_le)

theorem A'_to_B : A' → B := by
  intro hA n q N j U f L Y _ hj hU h0 hf hf0 hL _ hint hgood Linv hLinvY hLinv
  obtain ⟨hKY, ε, hε, hgood'⟩ := hgood
  set Li : (Fin N → ℝ) →L[ℝ] Y := Linv.codRestrict Y hLinvY with hLi_def
  have hLi : ∀ z, L (Li z) = z := fun z => hLinv z
  have h := contractionData (U := U) hj hU h0 hf hf0 hL hint hKY Li hLi hε hgood'
  obtain ⟨S⟩ := hA.1 h
  have hc := S.c₀_le_half
  refine ⟨S.a, S.a_pos, S.b, S.b_pos, fun v hv y hy hva hyb hC => ?_,
    fun v hv hva y hy y' hy' hyb hy'b hC hC' => ?_⟩
  · exact S.region_sub (⟨v, hv⟩, ⟨y, hy⟩) hva.le hyb.le hC
  · have hp : ((⟨v, hv⟩, ⟨y, hy⟩) : kerCLM L × Y) ∈ S.R := ⟨hva.le, hyb.le, hC⟩
    have hp' : ((⟨v, hv⟩, ⟨y', hy'⟩) : kerCLM L × Y) ∈ S.R := ⟨hva.le, hy'b.le, hC'⟩
    have key := hA.2 S h hp' hp
    have hn : ‖((⟨v, hv⟩, ⟨y, hy⟩) : kerCLM L × Y) - (⟨v, hv⟩, ⟨y', hy'⟩)‖ = ‖y - y'‖ := by
      rw [Prod.mk_sub_mk, sub_self, Prod.norm_def]
      simp only [norm_zero]
      rw [max_eq_right (norm_nonneg _)]
      rfl
    have hB : ‖(y - Linv (f (v + y))) - (y' - Linv (f (v + y')))‖ =
        ‖Bn L f Li (⟨v, hv⟩, ⟨y, hy⟩) - Bn L f Li (⟨v, hv⟩, ⟨y', hy'⟩)‖ := rfl
    have hcon : ‖(y - Linv (f (v + y))) - (y' - Linv (f (v + y')))‖ ≤ 1 / 2 * ‖y - y'‖ := by
      rw [hB]
      rw [hn] at key
      nlinarith [norm_nonneg (y - y')]
    refine ⟨hcon, fun hfeq => ?_⟩
    rw [hfeq, sub_sub_sub_cancel_right] at hcon
    have : ‖y - y'‖ ≤ 0 := by linarith [norm_nonneg (y - y')]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem A_to_B : A → B := fun hA => A'_to_B ⟨hA.1, hA.2.1⟩

/-- `#rt_check_except_defs T [d₁, …] [n₁, …]`: the harness traversal `rtCollect` with the bodies of
the definitions `dᵢ` not unfolded; fails if the proof of `T` reaches some `nᵢ` elsewhere (as in
items V1_32, V2_24). -/
elab "#rt_check_except_defs " t:ident " [" ds:ident,* "]" " [" bs:ident,* "]" : command => do
  let env ← Lean.getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let seen := ds.getElems.foldl (fun s d => s.insert d.getId) Lean.NameSet.empty
  let used := rtCollect env roots.toList seen
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do throwError "FAIL: {t.getId} uses {bad} outside the bodies of the definitions"
  Lean.logInfo m!"OK: {t.getId} reaches the banned declarations only through the bodies of the definitions {ds.getElems.toList.map (·.getId)}"

#rt_check RoundTrip.V3_64.A'_to_B [Polyfold.ContractionData.exists_radii,
  Polyfold.Radii.norm_sub_le, Polyfold.Radii.eq_τ]
-- `A_to_B` itself cannot pass `#rt_check`/`#rt_check_soft`: its binder type `A` contains the
-- statement of `eq_τ`, which mentions the definition `Radii.τ`, whose body
-- `if hk : k ∈ S.V₀ then (Radii.exists_fixed S h hk).choose else 0` applies `exists_fixed` directly
-- (not abstracted into a `_proof_N`); `exists_fixed` is proved with `norm_B_sub_le_snd`, i.e. with
-- the banned `Radii.norm_sub_le`.  The traversal with the body of `Radii.τ` not unfolded passes:
#rt_check_except_defs RoundTrip.V3_64.A_to_B [Polyfold.Radii.τ]
  [Polyfold.ContractionData.exists_radii, Polyfold.Radii.norm_sub_le, Polyfold.Radii.eq_τ]
/-- error: rt_check_soft FAIL: RoundTrip.V3_64.A_to_B uses [Polyfold.Radii.norm_sub_le] -/
#guard_msgs in
#rt_check_soft RoundTrip.V3_64.A_to_B [Polyfold.ContractionData.exists_radii,
  Polyfold.Radii.norm_sub_le, Polyfold.Radii.eq_τ]
#rt_overlap RoundTrip.V3_64.A'_to_B [Polyfold.ContractionData.exists_radii,
  Polyfold.Radii.norm_sub_le, Polyfold.Radii.eq_τ]

end RoundTrip.V3_64

end
