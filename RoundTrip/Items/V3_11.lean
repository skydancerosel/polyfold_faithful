import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_11

/-! Round trip for V3_11 (Lemma 3.9: the fibre derivative of `B` is small).
Refreshed 2026-11-02 against HEAD (new conjunct: Lemma 3.9 on level `m` with level-`m` smallness).

`A` is the conjunction of the types of the four listed theorems (no universe parameters; all
in `Type`):
* `ContractionGerm.norm_levelDeriv_snd_le`: on level `m`, `|D₂B(a, w)ζ|_m ≤ ½|ζ|_m` on the
  contraction regions of a `ContractionGerm` (working form);
* `IsSc0ContractionGerm.deriv_zero_snd`: `D₂B(0, 0) = 0`;
* `IsSc0ContractionGerm.exists_norm_deriv_snd_le`: arbitrary `ε`, level `0`, `x` small on level `1`;
* `IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le` (new): arbitrary `ε`, every level `m`,
  `|D₂B(x)ζ|_m ≤ ε|ζ|_m` for `x ∈ U_{m+1}` small **on level `m`** — the text's statement.
All four are for a general sc⁰-contraction germ `B` (Definition 3.28) with an sc¹ derivative
family `DB`, on a general finite-dimensional `P ⊇ C̃` (quadrant-like `C̃`).

B (the text): for an sc-smooth basic germ `f` on `ℝⁿ ⊕ W`, every `ε`, every `m`, the level-`m`
operator `D₂B(x)` has norm `≤ ε` for `x ∈ U_{m+1}` small on level `m`, and `D₂B(0,0) = 0`.

* `A → B`: PROVED from A (`A_to_B`, uses the new conjunct and `deriv_zero_snd`).  Glue: for B's
  basic germ `f`, the map `B(a, w) = w − P_W f(a, w)` is an sc¹-germ with derivative family
  `DBB D = pr_W − pr_W ∘ D` (germ arithmetic: `ScOperator.isSc1GermWith`, `operator_comp`, `sub`)
  and an sc⁰-contraction germ in the sense of Definition 3.28 (B's contraction estimate between
  lifts, on a ball inside `U_m`); then `levelDeriv (DBB D) m x (0, ζ)` is the lift `η` B asks for.
  B is also proved outright (`B_holds`, the audit's proof, kept): it re-proves the level-`m`
  estimate by the argument the project now uses for `exists_norm_levelDeriv_snd_le`.
* `B → A`: not proved; genuine difference of scope (B only speaks about sc-smooth basic germs on
  `ℝⁿ` with `C̃ = [0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ`, A about sc⁰-contraction germs with sc¹ `B` on any `P` and any
  quadrant-like `C̃`, and A's working-form theorem about arbitrary contraction regions with the
  fixed constant ½).
-/

namespace RoundTrip.V3_11
open Polyfold Set Filter Topology

/-- The project's statement (no universe parameters). -/
def A : Prop :=
  (type_of% @Polyfold.ContractionGerm.norm_levelDeriv_snd_le) ∧
  (type_of% @Polyfold.IsSc0ContractionGerm.deriv_zero_snd) ∧
  (type_of% @Polyfold.IsSc0ContractionGerm.exists_norm_deriv_snd_le) ∧
  (type_of% @Polyfold.IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le)

theorem A_holds : A :=
  ⟨@Polyfold.ContractionGerm.norm_levelDeriv_snd_le, @Polyfold.IsSc0ContractionGerm.deriv_zero_snd,
    @Polyfold.IsSc0ContractionGerm.exists_norm_deriv_snd_le,
    @Polyfold.IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le⟩

/-- `C̃ = [0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ` is quadrant-like. -/
lemma isQuadrantLike_CtB (n k : ℕ) : IsQuadrantLike (ScBanach.const (Fin n → ℝ)) (CtB n k) := by
  refine isQuadrantLike_const_iff.2 ⟨fun i _ => by simp, ?_, ?_⟩
  · intro a ha b hb s t hs ht _ i hi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hs (ha i hi)) (mul_nonneg ht (hb i hi))
  · refine ⟨fun _ => 1, mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨1, one_pos, ?_⟩)⟩
    intro a ha i _
    have h1 : dist (a i) 1 < 1 := (dist_le_pi_dist a (fun _ => 1) i).trans_lt ha
    rw [Real.dist_eq] at h1
    have := (abs_lt.1 h1).1
    linarith

section Glue
variable {n k N : ℕ} {W : ScBanach} {G : ScNbhdGerm (EB n W) (CtB n k ×ˢ Set.univ)}
  {f : (Fin n → ℝ) × W.lvl 0 → (Fin N → ℝ) × W.lvl 0}
  {D : (EB n W).lvl 1 → (EB n W).lvl 0 →L[ℝ] (EB N W).lvl 0}

lemma fst_mem {m : ℕ} {a : Fin n → ℝ} {w : W.lvl m} (h : ((a, w) : (EB n W).lvl m) ∈ G.U m) :
    a ∈ CtB n k := by
  have := G.U_subset m h
  rw [ScBanach.paramProd_lvlSet] at this
  exact this.1

/-- Level-`m` value of `BB f` for an sc⁰-germ `f`. -/
lemma toBase_BB (hf : IsSc0Germ (F := EB N W) G f) {m : ℕ} {x : (EB n W).lvl m}
    (hx : x ∈ G.U m) :
    W.toBase m (x.2 - (levelMap (E := EB n W) (F := EB N W) f m x).2) =
      BB f ((EB n W).toBase m x) := by
  have h1 := hf.toBase_levelMap hx
  rw [ScBanach.paramProd_toBase, ScBanach.paramProd_toBase] at h1
  rw [ScBanach.paramProd_toBase, BB, map_sub, ← h1]

/-- **Lemma 3.9 on level `m`, smallness on level `m`** (re-proved; the project's
`norm_levelDeriv_snd_le` argument with B's contraction balls in place of the regions `O`). -/
theorem level_bound (hb : IsBasicGermB n k N W G f) (hD : IsSc1GermWith (F := EB N W) G f D)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ δ > 0, ∀ x : (EB n W).lvl (m + 1), x ∈ G.U (m + 1) → ‖(EB n W).incl m x‖ < δ →
      ∀ ζ : W.lvl m, ‖ζ - (levelDeriv D m x ((0 : Fin n → ℝ), ζ)).2‖ ≤ ε * ‖ζ‖ := by
  obtain ⟨δ, hδ, hc⟩ := hb.2.2.2 ε hε m
  have hf0 : IsSc0Germ (F := EB N W) G f := hD.isSc0
  have hC : IsQuadrantLike (EB n W) (CtB n k ×ˢ univ) := (isQuadrantLike_CtB n k).paramProd W
  refine ⟨δ, hδ, ?_⟩
  rintro ⟨a, w⟩ hx hxδ ζ
  set E := EB n W with hE
  set L : W.lvl m →L[ℝ] W.lvl m := ContinuousLinearMap.id ℝ _ -
    (ContinuousLinearMap.snd ℝ (Fin N → ℝ) (W.lvl m)).comp
      ((levelDeriv D m ((a, w) : E.lvl (m + 1))).comp
        (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (W.lvl m))) with hL
  change ‖L ζ‖ ≤ ε * ‖ζ‖
  have hclosed : IsClosed {ζ : W.lvl m | ‖L ζ‖ ≤ ε * ‖ζ‖} :=
    isClosed_le L.continuous.norm (continuous_const.mul continuous_norm)
  refine (W.denseRange_incl m).induction_on ζ hclosed fun ζ' => ?_
  have haC : a ∈ CtB n k := fst_mem hx
  have hincl : E.incl m ((a, w) : E.lvl (m + 1)) = ((a, W.incl m w) : E.lvl m) := rfl
  rw [hincl, Prod.norm_mk] at hxδ
  have haδ : ‖a‖ < δ := (le_max_left _ _).trans_lt hxδ
  have hwδ : ‖W.incl m w‖ < δ := (le_max_right _ _).trans_lt hxδ
  -- the curve `t ↦ (a, w + t ζ')` in `U_{m+1}`
  obtain ⟨O, hO, hUO⟩ := G.relOpen (m + 1)
  have hxO : ((a, w) : E.lvl (m + 1)) ∈ O := by rw [hUO] at hx; exact hx.1
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.isOpen_iff.1 hO _ hxO
  set η : ℝ := min (r₁ / (‖ζ'‖ + 1)) ((δ - ‖W.incl m w‖) / (‖W.incl m ζ'‖ + 1)) with hη
  have hη0 : 0 < η := lt_min (by positivity) (div_pos (by linarith) (by positivity))
  have hmem₁ : ∀ t ∈ Ico (0 : ℝ) η, ((a, w + t • ζ') : E.lvl (m + 1)) ∈ G.U (m + 1) := by
    intro t ht
    rw [hUO]
    refine ⟨hr₁' ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have : ((a, w + t • ζ') : E.lvl (m + 1)) - (a, w) = ((0 : Fin n → ℝ), t • ζ') := by
        ext <;> simp
      rw [this, Prod.norm_mk, norm_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      refine max_lt hr₁ ?_
      calc t * ‖ζ'‖ ≤ (r₁ / (‖ζ'‖ + 1)) * ‖ζ'‖ :=
            mul_le_mul_of_nonneg_right (ht.2.le.trans (min_le_left _ _)) (norm_nonneg _)
        _ < r₁ := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg ζ']
    · rw [ScBanach.paramProd_lvlSet]; exact ⟨haC, mem_univ _⟩
  have hmemδ : ∀ t ∈ Ico (0 : ℝ) η, ‖W.incl m w + t • W.incl m ζ'‖ < δ := by
    intro t ht
    calc ‖W.incl m w + t • W.incl m ζ'‖ ≤ ‖W.incl m w‖ + ‖t • W.incl m ζ'‖ := norm_add_le _ _
      _ = ‖W.incl m w‖ + t * ‖W.incl m ζ'‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ ‖W.incl m w‖ + ((δ - ‖W.incl m w‖) / (‖W.incl m ζ'‖ + 1)) * ‖W.incl m ζ'‖ := by
          gcongr; exact ht.2.le.trans (min_le_right _ _)
      _ < ‖W.incl m w‖ + (δ - ‖W.incl m w‖) := by
          gcongr
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg (W.incl m ζ')]
      _ = δ := by ring
  set γ : ℝ → E.lvl (m + 1) := fun t => ((a, w) : E.lvl (m + 1)) + t • ((0 : Fin n → ℝ), ζ')
    with hγ
  have hγeq : ∀ t, γ t = ((a, w + t • ζ') : E.lvl (m + 1)) := fun t => by
    simp only [hγ, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero]
  have hγmem : ∀ t ∈ Ico (0 : ℝ) η, γ t ∈ G.U (m + 1) := fun t ht => by
    rw [hγeq]; exact hmem₁ t ht
  have hγd : HasDerivWithinAt γ ((0 : Fin n → ℝ), ζ') (Ico 0 η) 0 := by
    simpa [hγ] using ((hasDerivAt_id (0 : ℝ)).smul_const
      (((0 : Fin n → ℝ), ζ') : E.lvl (m + 1))).const_add ((a, w) : E.lvl (m + 1))
      |>.hasDerivWithinAt
  -- `φ = f_m ∘ ι ∘ γ` and `ψ = (ι γ)₂ − φ₂ = B_m(a, ιw + t ιζ')`
  set φ : ℝ → (EB N W).lvl m := fun t => levelMap (E := EB n W) (F := EB N W) f m (E.incl m (γ t))
    with hφ
  have hφd : HasDerivWithinAt φ
      ((levelDeriv D m ((a, w) : E.lvl (m + 1))) (E.incl m ((0 : Fin n → ℝ), ζ'))) (Ico 0 η) 0 := by
    have h0 : γ 0 = ((a, w) : E.lvl (m + 1)) := by simp [hγ]
    have hF : HasFDerivWithinAt (levelMap (E := EB n W) (F := EB N W) f m ∘ E.incl m)
        ((levelDeriv D m ((a, w) : E.lvl (m + 1))).comp (E.incl m)) (G.U (m + 1)) (γ 0) := by
      rw [h0]; exact hD.hasFDerivWithinAt_level hC hx
    exact hF.comp_hasDerivWithinAt (0 : ℝ) hγd hγmem
  set ψ : ℝ → W.lvl m := fun t => (W.incl m w + t • W.incl m ζ') - (φ t).2 with hψ
  have hψd : HasDerivWithinAt ψ (L (W.incl m ζ')) (Ico 0 η) 0 := by
    have h1 : HasDerivWithinAt (fun t : ℝ => W.incl m w + t • W.incl m ζ') (W.incl m ζ')
        (Ico 0 η) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (W.incl m ζ')).const_add (W.incl m w)
        |>.hasDerivWithinAt
    have h2 := (ContinuousLinearMap.snd ℝ (Fin N → ℝ) (W.lvl m)).hasFDerivAt.comp_hasDerivWithinAt
      (0 : ℝ) hφd
    convert h1.sub h2 using 1
    · rfl
    · rw [hL]; rfl
  -- the slope bound from B's contraction on level `m`
  have hβ : ∀ v : W.lvl m, ((a, v) : E.lvl m) ∈ G.U m → ∀ b : W.lvl m,
      W.toBase m b = BB f (a, W.toBase m v) →
      v - (levelMap (E := EB n W) (F := EB N W) f m ((a, v) : E.lvl m)).2 = b := by
    intro v hv b hb'
    apply W.toBase_injective m
    rw [toBase_BB hf0 hv, ScBanach.paramProd_toBase, hb']
  have hslope : ∀ t ∈ Ico (0 : ℝ) η \ {0}, ‖slope ψ 0 t‖ ≤ ε * ‖W.incl m ζ'‖ := by
    rintro t ⟨ht, ht0⟩
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm (by simpa using ht0))
    have hγt : E.incl m (γ t) = ((a, W.incl m w + t • W.incl m ζ') : E.lvl m) := by
      rw [hγeq]; change ((a, W.incl m (w + t • ζ')) : E.lvl m) = _; rw [map_add, map_smul]
    have hmt : ((a, W.incl m w + t • W.incl m ζ') : E.lvl m) ∈ G.U m := by
      rw [← hγt]; exact G.nested m _ (hγmem t ht)
    have hm0 : ((a, W.incl m w) : E.lvl m) ∈ G.U m := by
      rw [← hincl]; exact G.nested m _ hx
    obtain ⟨b, b', hb, hb', hest⟩ := hc a _ _ hmt hm0 haδ (hmemδ t ht) hwδ
    have hψt : ψ t = b := by
      rw [← hβ _ hmt b hb]
      simp only [hψ, hφ, hγt]
    have hψ0 : ψ 0 = b' := by
      rw [← hβ _ hm0 b' hb']
      simp only [hψ, hφ, zero_smul, add_zero]
      rw [hγeq, zero_smul, add_zero, hincl]
    rw [slope_def_module, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos htpos, hψt,
      hψ0]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos] at hest
    rw [inv_mul_le_iff₀ htpos]
    linarith
  have hne : (𝓝[Ico (0 : ℝ) η \ {0}] 0).NeBot := by
    rw [Ico_sdiff_left]
    exact mem_closure_iff_nhdsWithin_neBot.1 (by
      rw [closure_Ioo hη0.ne]; exact left_mem_Icc.2 hη0.le)
  have hlim : Tendsto (fun t => ‖slope ψ 0 t‖) (𝓝[Ico (0 : ℝ) η \ {0}] 0)
      (𝓝 ‖L (W.incl m ζ')‖) :=
    (hasDerivWithinAt_iff_tendsto_slope.1 hψd).norm
  exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall hslope)

/-- B's first clause, from `level_bound`. -/
theorem B_level (hb : IsBasicGermB n k N W G f) (hD : IsSc1GermWith (F := EB N W) G f D)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ δ > (0 : ℝ), ∀ (x : (EB n W).lvl (m + 1)) (x₁ : (EB n W).lvl 1),
      (EB n W).toBase (m + 1) x = (EB n W).toBase 1 x₁ → x ∈ G.U (m + 1) →
      ‖(EB n W).incl m x‖ < δ →
      ∀ ζ : W.lvl m, ∃ η : W.lvl m, W.toBase m η = D2B D x₁ (W.toBase m ζ) ∧ ‖η‖ ≤ ε * ‖ζ‖ := by
  obtain ⟨δ, hδ, h⟩ := level_bound hb hD hε m
  refine ⟨δ, hδ, fun x x₁ hxx₁ hx hxδ ζ => ⟨_, ?_, h x hx hxδ ζ⟩⟩
  have hx₁ : (EB n W).shift.toBase m x = x₁ :=
    (EB n W).toBase_injective 1 (by rw [← ScBanach.shift_toBase]; exact hxx₁)
  have h1 := hD.toBase_levelDeriv hx ((0 : Fin n → ℝ), ζ)
  rw [ScBanach.paramProd_toBase, ScBanach.paramProd_toBase, hx₁] at h1
  rw [map_sub, D2B, ← congrArg Prod.snd h1]

theorem B_holds : B := by
  intro n k N W _ G f hb D hD
  refine ⟨fun ε hε m => B_level hb hD hε m, fun ζ => ?_⟩
  have H : ∀ ε > (0 : ℝ), ‖D2B D 0 ζ‖ ≤ ε * ‖ζ‖ := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := B_level hb hD hε 0
    obtain ⟨η, hη, hηle⟩ := h 0 0 rfl (G.zero_mem 1) (by rw [map_zero, norm_zero]; exact hδ) ζ
    rw [ScScale.toBase_zero, ScScale.toBase_zero] at hη
    rw [← hη]; exact hηle
  by_contra hv
  have hpos : 0 < ‖D2B D 0 ζ‖ := norm_pos_iff.2 hv
  have := H (‖D2B D 0 ζ‖ / (2 * (‖ζ‖ + 1))) (by positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
  nlinarith [norm_nonneg ζ]

end Glue

/-! ### A ⇒ B through A's level-`m` Lemma 3.9 -/

section AGlue
variable {n k N : ℕ} {W : ScBanach} {G : ScNbhdGerm (EB n W) (CtB n k ×ˢ Set.univ)}
  {f : (Fin n → ℝ) × W.lvl 0 → (Fin N → ℝ) × W.lvl 0}
  {D : (EB n W).lvl 1 → (EB n W).lvl 0 →L[ℝ] (EB N W).lvl 0}

/-- The derivative family `pr_W − pr_W ∘ Df` of `B = w − P_W f`. -/
def DBB (D : (EB n W).lvl 1 → (EB n W).lvl 0 →L[ℝ] (EB N W).lvl 0) (x : (EB n W).lvl 1) :
    (EB n W).lvl 0 →L[ℝ] W.lvl 0 :=
  ContinuousLinearMap.snd ℝ (Fin n → ℝ) (W.lvl 0) -
    (ContinuousLinearMap.snd ℝ (Fin N → ℝ) (W.lvl 0)).comp (D x)

/-- `B = w − P_W f` is an sc¹-germ with derivative family `DBB D`. -/
lemma isSc1GermWith_BB (hD : IsSc1GermWith (F := EB N W) G f D) :
    IsSc1GermWith (F := W) G (BB f) (DBB D) := by
  have h1 := (ScBanach.sndOp (ScBanach.const (Fin n → ℝ)) W).isSc1GermWith G
  have h2 := hD.operator_comp (ScBanach.sndOp (ScBanach.const (Fin N → ℝ)) W)
  exact ((h1.sub h2).congr fun x _ => rfl).congr_deriv fun x _ => rfl

/-- B's basic germ gives an sc⁰-contraction germ `B = w − P_W f` (Definition 3.28). -/
lemma isSc0ContractionGerm_BB (hb : IsBasicGermB n k N W G f)
    (hD : IsSc1GermWith (F := EB N W) G f D) : IsSc0ContractionGerm (CtB n k) G (BB f) := by
  have hB0 := (isSc1GermWith_BB hD).isSc0
  refine ⟨hB0, hb.2.2.1, fun ε hε m => ?_⟩
  obtain ⟨δ, hδ, hc⟩ := hb.2.2.2 ε hε m
  obtain ⟨O, hO, hUO⟩ := G.relOpen m
  have h0O : (0 : (EB n W).lvl m) ∈ O := by
    have := G.zero_mem m; rw [hUO] at this; exact this.1
  obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hO _ h0O
  refine ⟨min δ r₁, lt_min hδ hr₁, fun a ha har w w' hw hw' => ?_⟩
  have hmem : ∀ v : W.lvl m, ‖v‖ < min δ r₁ → ((a, v) : (EB n W).lvl m) ∈ G.U m := by
    intro v hv
    rw [hUO]
    refine ⟨hball ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk]
      exact max_lt (har.trans_le (min_le_right _ _)) (hv.trans_le (min_le_right _ _))
    · rw [ScBanach.paramProd_lvlSet]; exact ⟨ha, mem_univ _⟩
  have hw0 := hmem w hw
  have hw0' := hmem w' hw'
  refine ⟨hw0, ?_⟩
  obtain ⟨b, b', hb1, hb2, hest⟩ := hc a w w' hw0 hw0' (har.trans_le (min_le_left _ _))
    (hw.trans_le (min_le_left _ _)) (hw'.trans_le (min_le_left _ _))
  have e1 : levelB (BB f) m (a, w) = b := W.toBase_injective m (by
    rw [hB0.toBase_levelMap hw0, ScBanach.paramProd_toBase, hb1])
  have e2 : levelB (BB f) m (a, w') = b' := W.toBase_injective m (by
    rw [hB0.toBase_levelMap hw0', ScBanach.paramProd_toBase, hb2])
  rw [e1, e2]; exact hest

end AGlue

/-- **A ⇒ B**, through A's `exists_norm_levelDeriv_snd_le` (level `m`, smallness on level `m`)
and `deriv_zero_snd`. -/
theorem A_to_B : A → B := by
  rintro ⟨-, hzero, -, hlev⟩ n k N W _ G f hb D hD
  have hC := isQuadrantLike_CtB n k
  have hBc := isSc1GermWith_BB hD
  have hBC := isSc0ContractionGerm_BB hb hD
  refine ⟨fun ε hε m => ?_, fun ζ => ?_⟩
  · obtain ⟨r, hr, h⟩ := hlev hC hBC hBc hε m
    refine ⟨r, hr, fun x x₁ hxx₁ hx hxr ζ =>
      ⟨levelDeriv (DBB D) m x ((0 : Fin n → ℝ), ζ), ?_, h x hx hxr ζ⟩⟩
    have hx₁ : (EB n W).shift.toBase m x = x₁ :=
      (EB n W).toBase_injective 1 (by rw [← ScBanach.shift_toBase]; exact hxx₁)
    rw [hBc.toBase_levelDeriv hx, hx₁, ScBanach.paramProd_toBase]
    rfl
  · exact hzero hBC (hBc.hasFDerivWithinAt 0 (G.zero_mem 1)) ζ

#rt_check RoundTrip.V3_11.A_to_B [Polyfold.ContractionGerm.norm_levelDeriv_snd_le,
  Polyfold.IsSc0ContractionGerm.deriv_zero_snd, Polyfold.IsSc0ContractionGerm.exists_norm_deriv_snd_le,
  Polyfold.IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le]
#rt_check RoundTrip.V3_11.B_holds [Polyfold.ContractionGerm.norm_levelDeriv_snd_le,
  Polyfold.IsSc0ContractionGerm.deriv_zero_snd, Polyfold.IsSc0ContractionGerm.exists_norm_deriv_snd_le,
  Polyfold.IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le]
#rt_overlap RoundTrip.V3_11.B_holds [Polyfold.ContractionGerm.norm_levelDeriv_snd_le,
  Polyfold.IsSc0ContractionGerm.deriv_zero_snd, Polyfold.IsSc0ContractionGerm.exists_norm_deriv_snd_le,
  Polyfold.IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le]

end RoundTrip.V3_11
