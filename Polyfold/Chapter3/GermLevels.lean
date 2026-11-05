import Polyfold.Chapter3.Germ
import Polyfold.Chapter1.Levels

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §1.2,
Propositions 1.16 (⇒) and 1.17, for the sc^k-germs of §3.1 (Definition 3.2).

# Level operators and the level shift for germs

## The text, paraphrased

The proofs of §3.3 use, for a germ `f : O(C, 0) → F`, that `f : U_{m+1} → F_m` is `C¹` with
derivative the level-`m` operator `Df(x) : E_m → F_m` (Proposition 1.16), and that the shifted germ
`f : O(C, 0)¹ → F¹` is again sc^k (Proposition 1.17, "recalling Proposition 1.17" in the proof of
Lemma 3.9 and in Lemma 3.31).  Both propositions are stated in §1.2 for relatively open sets; the
germ versions are not stated.

## What is formalized

* `IsSc1GermWith.exists_levelDeriv`, `toBase_levelDeriv`, `levelMap_tangentMapWith`,
  `continuousOn_levelDeriv`, `continuousOn_levelDeriv_clm`: the level operators `levelDeriv D m x`
  of a derivative family at `x ∈ U_{m+1}` and their continuity (Proposition 1.16 (2)).
* `IsSc1GermWith.hasFDerivWithinAt_level` (**Proposition 1.16 (⇒)** for germs): `f : U_{m+1} → F_m`
  is differentiable at every point of `U_{m+1}` with derivative `Df(x)|_{E_{m+1}}`.
* `ScNbhdGerm.shift` (the germ `O(C, 0)¹ = (U_{m+1})_m` in `E¹`), `IsSc0Germ.shift`,
  `IsSc1GermWith.shift`, `IsSckGerm.shift` (**Proposition 1.17** for germs).
* `IsSckGerm.of_U_eq`: sc^k depends on a germ only through its sets `U_m`.

## What the text leaves implicit

The proofs are those of `Levels.lean` with `U ∩ E_m` replaced by `U_m`; nothing new.
-/

open Set Filter Topology Function Asymptotics MeasureTheory

noncomputable section

namespace Polyfold

variable {E F : ScBanach} {C : Set (E 0)} {G₁ : ScNbhdGerm E C} {f : E 0 → F 0}
  {D : E 1 → E 0 →L[ℝ] F 0}

/-! ### Transport along equal families of sets -/

lemma IsSc0Germ.of_U_eq {C' : Set (E 0)} {G₂ : ScNbhdGerm E C'} (h : ∀ m, G₁.U m = G₂.U m)
    (hf : IsSc0Germ G₁ f) : IsSc0Germ G₂ f :=
  ⟨fun m => h m ▸ hf.mem_range m, fun m => h m ▸ hf.continuousOn m⟩

lemma ScNbhdGerm.tangent_U_eq {C' : Set (E 0)} {G₂ : ScNbhdGerm E C'} (h : ∀ m, G₁.U m = G₂.U m)
    (m : ℕ) : G₁.tangent.U m = G₂.tangent.U m := by
  simp only [ScNbhdGerm.tangent_U, h]

lemma IsSc1GermWith.of_U_eq {C' : Set (E 0)} {G₂ : ScNbhdGerm E C'} (h : ∀ m, G₁.U m = G₂.U m)
    (hf : IsSc1GermWith G₁ f D) : IsSc1GermWith G₂ f D where
  isSc0 := hf.isSc0.of_U_eq h
  hasFDerivWithinAt x hx := h 1 ▸ hf.hasFDerivWithinAt x (h 1 ▸ hx)
  tangent_isSc0 := hf.tangent_isSc0.of_U_eq (ScNbhdGerm.tangent_U_eq h)

lemma ScNbhdGerm.uniqueDiffWithinAt_of_U_eq {C' : Set (E 0)} {G₂ : ScNbhdGerm E C'}
    (hC : IsQuadrantLike E C) (h : ∀ m, G₁.U m = G₂.U m) (m : ℕ) {x : E m} (hx : x ∈ G₂.U m) :
    UniqueDiffWithinAt ℝ (G₂.U m) x := h m ▸ G₁.uniqueDiffWithinAt hC m (h m ▸ hx)

theorem IsSckGerm.of_U_eq : ∀ {k : ℕ} {E F : ScBanach} {C C' : Set (E 0)} {G₁ : ScNbhdGerm E C}
    {G₂ : ScNbhdGerm E C'} {f : E 0 → F 0}, IsQuadrantLike E C → (∀ m, G₁.U m = G₂.U m) →
    IsSckGerm k G₁ f → IsSckGerm k G₂ f
  | 0, _, _, _, _, _, _, _, _, h, hf => IsSc0Germ.of_U_eq h hf
  | k + 1, E, F, C, C', G₁, G₂, f, hC, h, hf => by
    have h1 : IsSc1GermWith G₂ f (scDerivGerm G₁ f) := hf.1.isSc1GermWith_scDerivGerm.of_U_eq h
    refine ⟨h1.isSc1Germ, ?_⟩
    have h2 : EqOn (tangentMapGerm G₂ f) (tangentMapGerm G₁ f) (G₂.tangent.U 0) := by
      intro p hp
      change (levelMap f 1 p.1, scDerivGerm G₂ f p.1 p.2) = (levelMap f 1 p.1, scDerivGerm G₁ f p.1 p.2)
      have := h1.isSc1Germ.isSc1GermWith_scDerivGerm.eq_of_uniqueDiffWithinAt h1
        (G₂.mem_tangent_U.1 hp) (ScNbhdGerm.uniqueDiffWithinAt_of_U_eq hC h 1 (G₂.mem_tangent_U.1 hp))
      rw [this]
    have h3 := IsSckGerm.of_U_eq (k := k) hC.tangentSet (ScNbhdGerm.tangent_U_eq h) hf.2
    -- `congr` on `G₂.tangent` needs unique differentiability there, which comes from `G₁`
    have hC' : IsQuadrantLike E.tangent (E.tangentSet C) := hC.tangentSet
    -- transport back to `G₁.tangent`, apply `congr` there, transport again
    have h4 : IsSckGerm k G₁.tangent (tangentMapGerm G₂ f) := by
      refine IsSckGerm.congr hC' ?_ hf.2
      intro p hp
      exact (h2 (ScNbhdGerm.tangent_U_eq h 0 ▸ hp)).symm
    exact IsSckGerm.of_U_eq (k := k) hC' (ScNbhdGerm.tangent_U_eq h) h4

/-! ### The level operators of an sc¹-germ (Proposition 1.16 (2)) -/

namespace IsSc1GermWith

theorem exists_levelDeriv (h : IsSc1GermWith G₁ f D) {m : ℕ} {x : E (m + 1)}
    (hx : x ∈ G₁.U (m + 1)) :
    ∃ T : E m →L[ℝ] F m, ∀ v, F.toBase m (T v) = D (E.shift.toBase m x) (E.toBase m v) := by
  have hmem : ∀ v : E m, ((x, v) : E.tangent m) ∈ G₁.tangent.U m := fun v => ⟨hx, mem_univ _⟩
  set Tm : E m → F m := fun v => (levelMap (tangentMapWith f D) m ((x, v) : E.tangent m)).2 with hTm
  have hTm' : ∀ v, F.toBase m (Tm v) = D (E.shift.toBase m x) (E.toBase m v) := by
    intro v
    have := congrArg Prod.snd (h.tangent_isSc0.toBase_levelMap (hmem v))
    rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase] at this
    exact this
  have hcont : Continuous Tm := by
    have := (h.tangent_isSc0.continuousOn m).comp_continuous
      (f := fun v : E m => ((x, v) : E.tangent m)) (by fun_prop) hmem
    exact continuous_snd.comp this
  exact ⟨{ toFun := Tm
           map_add' := fun v w => F.toBase_injective m (by
             rw [map_add, hTm', hTm', hTm', map_add, map_add])
           map_smul' := fun a v => F.toBase_injective m (by
             rw [map_smul, hTm', hTm', map_smul, map_smul]; rfl)
           cont := hcont }, hTm'⟩

theorem toBase_levelDeriv (h : IsSc1GermWith G₁ f D) {m : ℕ} {x : E (m + 1)}
    (hx : x ∈ G₁.U (m + 1)) (v : E m) :
    F.toBase m (levelDeriv D m x v) = D (E.shift.toBase m x) (E.toBase m v) :=
  Polyfold.toBase_levelDeriv (h.exists_levelDeriv hx) v

/-- `levelMap f 1 ∘ ι = ι ∘ levelMap f (m+1)` on `U_{m+1}` (the shifted level maps). -/
lemma levelMap_shift_toBase (hf : IsSc0Germ G₁ f) {m : ℕ} {x : E (m + 1)} (hx : x ∈ G₁.U (m + 1)) :
    levelMap f 1 (E.shift.toBase m x) = F.shift.toBase m (levelMap f (m + 1) x) := by
  apply F.toBase_injective 1
  rw [← F.shift_toBase, hf.toBase_levelMap hx, hf.toBase_levelMap (G₁.shift_toBase_mem hx),
    E.shift_toBase m x]

theorem levelMap_tangentMapWith (h : IsSc1GermWith G₁ f D) {m : ℕ} {p : E.tangent m}
    (hp : p ∈ G₁.tangent.U m) :
    levelMap (tangentMapWith f D) m p =
      ((levelMap f (m + 1) p.1, levelDeriv D m p.1 p.2) : F.tangent m) := by
  have hp1 : p.1 ∈ G₁.U (m + 1) := hp.1
  apply levelMap_eq_of_toBase_eq
  rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase]
  change ((F.shift.toBase m (levelMap f (m + 1) p.1), F.toBase m (levelDeriv D m p.1 p.2)) :
    F.tangent 0) = (levelMap f 1 (E.shift.toBase m p.1), D (E.shift.toBase m p.1) (E.toBase m p.2))
  exact Prod.ext (levelMap_shift_toBase h.isSc0 hp1).symm (h.toBase_levelDeriv hp1 p.2)

theorem continuousOn_levelDeriv (h : IsSc1GermWith G₁ f D) (m : ℕ) :
    ContinuousOn (fun p : E (m + 1) × E m => levelDeriv D m p.1 p.2) (G₁.U (m + 1) ×ˢ univ) := by
  have := h.tangent_isSc0.continuousOn m
  refine (continuous_snd.comp_continuousOn this).congr fun p hp => ?_
  rw [Function.comp_apply, h.levelMap_tangentMapWith hp]

theorem continuousOn_levelDeriv_clm (h : IsSc1GermWith G₁ f D) (m : ℕ) :
    ContinuousOn (fun x => (levelDeriv D m x).comp (E.incl m)) (G₁.U (m + 1)) :=
  continuousOn_clm_comp_of_isCompactOperator (A := levelDeriv D m) (h.continuousOn_levelDeriv m)
    (E.incl_isCompactOperator m)

/-- **Proposition 1.16 (⇒) for germs**: `f : U_{m+1} → F_m` is differentiable at every
`x ∈ U_{m+1}` within `U_{m+1}`, with derivative `Df(x)|_{E_{m+1}}` (the integral representation
`f(x+k) − f(x) = ∫₀¹ Df(x+τk)k dτ` in `F_m`). -/
theorem hasFDerivWithinAt_level (hC : IsQuadrantLike E C) (h : IsSc1GermWith G₁ f D) {m : ℕ}
    {x : E (m + 1)} (hx : x ∈ G₁.U (m + 1)) :
    HasFDerivWithinAt (levelMap f m ∘ E.incl m) ((levelDeriv D m x).comp (E.incl m))
      (G₁.U (m + 1)) x := by
  obtain ⟨O, K, hO, hK, hUOC⟩ := G₁.relOpenConvex hC (m + 1)
  have hxO : x ∈ O := (hUOC ▸ hx).1
  obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO x hxO
  have hcont := h.continuousOn_levelDeriv_clm m x hx
  rw [Metric.continuousWithinAt_iff] at hcont
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hδ'⟩ := hcont c hc
  have ev1 : ∀ᶠ z in 𝓝[G₁.U (m + 1)] x, z ∈ G₁.U (m + 1) := self_mem_nhdsWithin
  have ev2 : ∀ᶠ z in 𝓝[G₁.U (m + 1)] x, dist z x < min ρ δ :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (lt_min hρ hδ))
  filter_upwards [ev1, ev2] with z hz hzd
  set k := z - x with hk
  have hkρ : ‖k‖ < ρ := by rw [hk, ← dist_eq_norm]; exact lt_of_lt_of_le hzd (min_le_left _ _)
  have hkδ : ‖k‖ < δ := by rw [hk, ← dist_eq_norm]; exact lt_of_lt_of_le hzd (min_le_right _ _)
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • k ∈ G₁.U (m + 1) := by
    intro τ hτ
    rw [hUOC]
    refine ⟨hρO ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hτ.1]
      calc τ * ‖k‖ ≤ 1 * ‖k‖ := mul_le_mul_of_nonneg_right hτ.2 (norm_nonneg _)
        _ < ρ := by rw [one_mul]; exact hkρ
    · have := hK.add_smul_sub_mem (hUOC ▸ hx).2 (hUOC ▸ hz).2 hτ
      rwa [hk]
  have hsegδ : ∀ τ ∈ Icc (0 : ℝ) 1, dist (x + τ • k) x < δ := by
    intro τ hτ
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
    calc τ * ‖k‖ ≤ 1 * ‖k‖ := mul_le_mul_of_nonneg_right hτ.2 (norm_nonneg _)
      _ < δ := by rw [one_mul]; exact hkδ
  have hseg₁ : ∀ τ ∈ Icc (0 : ℝ) 1,
      E.shift.toBase m x + τ • E.shift.toBase m k ∈ G₁.U 1 := fun τ hτ => by
    rw [← map_smul, ← map_add]; exact G₁.shift_toBase_mem (hseg τ hτ)
  set g : ℝ → F m := fun τ => levelDeriv D m (x + τ • k) (E.incl m k) with hg
  have hgc : ContinuousOn g (Icc 0 1) :=
    (h.continuousOn_levelDeriv m).comp (f := fun τ : ℝ => (x + τ • k, E.incl m k))
      (Continuous.continuousOn (by fun_prop)) fun τ hτ => mk_mem_prod (hseg τ hτ) (mem_univ _)
  have hgi : IntervalIntegrable g volume 0 1 := hgc.intervalIntegrable_of_Icc zero_le_one
  set φ : ℝ → F 0 := fun τ => f (E.toBase 1 (E.shift.toBase m x + τ • E.shift.toBase m k)) with hφ
  have hγ : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => E.shift.toBase m x + τ • E.shift.toBase m k)
      (E.shift.toBase m k) τ := fun τ => by
    simpa using ((hasDerivAt_id τ).smul_const (E.shift.toBase m k)).const_add (E.shift.toBase m x)
  have hφd : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ
      (D (E.shift.toBase m x + τ • E.shift.toBase m k) (E.toBase 1 (E.shift.toBase m k)))
      (Icc 0 1) τ := fun τ hτ =>
    HasFDerivWithinAt.comp_hasDerivWithinAt (l := f ∘ E.toBase 1)
      (f := fun τ : ℝ => E.shift.toBase m x + τ • E.shift.toBase m k) τ
      (h.hasFDerivWithinAt _ (hseg₁ τ hτ)) (hγ τ).hasDerivWithinAt hseg₁
  have hφ'i : IntervalIntegrable
      (fun τ => D (E.shift.toBase m x + τ • E.shift.toBase m k) (E.toBase 1 (E.shift.toBase m k)))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
    exact h.continuousOn_deriv.comp
      (f := fun τ : ℝ => (E.shift.toBase m x + τ • E.shift.toBase m k, E.toBase 1 (E.shift.toBase m k)))
      (Continuous.continuousOn (by fun_prop)) fun τ hτ => ⟨hseg₁ τ hτ, mem_univ _⟩
  have hFTC : ∫ τ in (0 : ℝ)..1,
      D (E.shift.toBase m x + τ • E.shift.toBase m k) (E.toBase 1 (E.shift.toBase m k)) =
        φ 1 - φ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (fun τ hτ => (hφd τ hτ).continuousWithinAt)
      (fun τ hτ => (hφd τ (Ioo_subset_Icc_self hτ)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)) hφ'i
  have e1 : φ 1 = f (E.toBase m (E.incl m z)) := by
    simp only [hφ, one_smul, ← map_add, hk, add_sub_cancel, ← E.shift_toBase]; rfl
  have e0 : φ 0 = f (E.toBase m (E.incl m x)) := by
    simp only [hφ, zero_smul, add_zero, ← E.shift_toBase]; rfl
  have hint : levelMap f m (E.incl m z) - levelMap f m (E.incl m x) = ∫ τ in (0 : ℝ)..1, g τ := by
    apply F.toBase_injective m
    rw [map_sub, h.isSc0.toBase_levelMap (m := m) (x := E.incl m z) (G₁.nested m z hz),
      h.isSc0.toBase_levelMap (m := m) (x := E.incl m x) (G₁.nested m x hx),
      ← (F.toBase m).intervalIntegral_comp_comm hgi,
      intervalIntegral.integral_congr (g := fun τ =>
        D (E.shift.toBase m x + τ • E.shift.toBase m k) (E.toBase 1 (E.shift.toBase m k))) ?_,
      hFTC, e1, e0]
    intro τ hτ
    rw [uIcc_of_le zero_le_one] at hτ
    simp only [hg]
    rw [h.toBase_levelDeriv (hseg τ hτ), map_add, map_smul, ← E.shift_toBase]
    rfl
  have hconst : ((levelDeriv D m x).comp (E.incl m)) k =
      ∫ τ in (0 : ℝ)..1, levelDeriv D m x (E.incl m k) := by
    rw [intervalIntegral.integral_const, sub_zero, one_smul]; rfl
  change ‖levelMap f m (E.incl m z) - levelMap f m (E.incl m x) - _‖ ≤ _
  rw [hint, hconst, ← intervalIntegral.integral_sub hgi intervalIntegrable_const]
  have hbd : ∀ τ ∈ Set.uIoc (0 : ℝ) 1, ‖g τ - levelDeriv D m x (E.incl m k)‖ ≤ c * ‖k‖ := by
    intro τ hτ
    rw [uIoc_of_le zero_le_one] at hτ
    have hτ' : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1.le, hτ.2⟩
    have h1 := hδ' (hseg τ hτ') (hsegδ τ hτ')
    rw [dist_eq_norm] at h1
    calc ‖g τ - levelDeriv D m x (E.incl m k)‖
        = ‖((levelDeriv D m (x + τ • k)).comp (E.incl m) -
            (levelDeriv D m x).comp (E.incl m)) k‖ := rfl
      _ ≤ ‖(levelDeriv D m (x + τ • k)).comp (E.incl m) -
            (levelDeriv D m x).comp (E.incl m)‖ * ‖k‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖k‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  simpa using this

end IsSc1GermWith

/-! ### Proposition 1.17 for germs: the level shift -/

namespace ScNbhdGerm

/-- The shifted germ `O(C, 0)¹ = (U_{m+1})_m`, a germ in `E¹` around `0 ∈ C¹ = C_1`. -/
def shift (G₁ : ScNbhdGerm E C) : ScNbhdGerm E.shift (E.lvlSet C 1) where
  U m := G₁.U (m + 1)
  nested m x hx := G₁.nested (m + 1) x hx
  zero_mem m := G₁.zero_mem (m + 1)
  relOpen m := by
    obtain ⟨O, hO, h⟩ := G₁.relOpen (m + 1)
    exact ⟨O, hO, by rw [E.shift_lvlSet]; exact h⟩

@[simp] lemma shift_U (G₁ : ScNbhdGerm E C) (m : ℕ) : G₁.shift.U m = G₁.U (m + 1) := rfl

lemma shift_tangent_U_eq (G₁ : ScNbhdGerm E C) (m : ℕ) :
    G₁.shift.tangent.U m = G₁.tangent.shift.U m := rfl

end ScNbhdGerm

lemma IsQuadrantLike.shift (hC : IsQuadrantLike E C) : IsQuadrantLike E.shift (E.lvlSet C 1) where
  zero_mem := by rw [ScBanach.mem_lvlSet, map_zero]; exact hC.zero_mem
  convex m := by rw [E.shift_lvlSet]; exact hC.convex (m + 1)
  interior_nonempty m := by rw [E.shift_lvlSet]; exact hC.interior_nonempty (m + 1)

lemma IsSc0Germ.levelMap_shift (hf : IsSc0Germ G₁ f) {m : ℕ} {x : E (m + 1)}
    (hx : x ∈ G₁.U (m + 1)) :
    levelMap (E := E.shift) (F := F.shift) (levelMap f 1) m x = levelMap f (m + 1) x := by
  apply levelMap_eq_of_toBase_eq
  apply F.toBase_injective 1
  rw [← F.shift_toBase, hf.toBase_levelMap hx,
    hf.toBase_levelMap (G₁.shift_toBase_mem hx), E.shift_toBase m x]

/-- **Proposition 1.17 for sc⁰-germs.** -/
theorem IsSc0Germ.shift (hf : IsSc0Germ G₁ f) :
    IsSc0Germ G₁.shift (E := E.shift) (F := F.shift) (levelMap f 1) where
  mem_range m x hx := by
    refine ⟨levelMap f (m + 1) x, ?_⟩
    apply F.toBase_injective 1
    rw [← F.shift_toBase, hf.toBase_levelMap hx, hf.toBase_levelMap (G₁.shift_toBase_mem hx),
      E.shift_toBase m x]
  continuousOn m := (hf.continuousOn (m + 1)).congr fun x hx => hf.levelMap_shift hx

/-- **Proposition 1.17 for sc¹-germs.** -/
theorem IsSc1GermWith.shift (hC : IsQuadrantLike E C) (h : IsSc1GermWith G₁ f D) :
    IsSc1GermWith G₁.shift (E := E.shift) (F := F.shift) (levelMap f 1) (levelDeriv D 1) where
  isSc0 := h.isSc0.shift
  hasFDerivWithinAt x hx := h.hasFDerivWithinAt_level hC (m := 1) hx
  tangent_isSc0 := by
    have := h.tangent_isSc0.shift
    refine (this.of_U_eq fun m => (G₁.shift_tangent_U_eq m).symm).congr fun p hp => ?_
    have hp' : p ∈ G₁.tangent.U 1 := hp
    rw [h.levelMap_tangentMapWith hp']
    change ((levelMap f 2 p.1, levelDeriv D 1 p.1 p.2) : F.tangent 1) =
      (levelMap (levelMap f 1) 1 p.1, levelDeriv D 1 p.1 p.2)
    rw [h.isSc0.levelMap_shift hp'.1]

/-- **Proposition 1.17 for sc^k-germs**: if `f` is an sc^k-germ on `O(C, 0)` then `f : O(C,0)¹ → F¹`
is an sc^k-germ on the shifted germ. -/
theorem IsSckGerm.shift : ∀ {k : ℕ} {E F : ScBanach} {C : Set (E 0)} {G₁ : ScNbhdGerm E C}
    {f : E 0 → F 0}, IsQuadrantLike E C → IsSckGerm k G₁ f →
    IsSckGerm k G₁.shift (E := E.shift) (F := F.shift) (levelMap f 1)
  | 0, _, _, _, _, _, _, hf => IsSc0Germ.shift hf
  | k + 1, E, F, C, G₁, f, hC, hf => by
    have h1 : IsSc1GermWith G₁.shift (E := E.shift) (F := F.shift) (levelMap f 1)
        (levelDeriv (scDerivGerm G₁ f) 1) := hf.1.isSc1GermWith_scDerivGerm.shift hC
    refine ⟨h1.isSc1Germ, ?_⟩
    have := IsSckGerm.shift (k := k) hC.tangentSet hf.2
    have h2 := IsSckGerm.of_U_eq hC.tangentSet.shift (fun m => (G₁.shift_tangent_U_eq m).symm) this
    refine IsSckGerm.congr hC.shift.tangentSet (fun p hp => ?_) h2
    have hp' : p ∈ G₁.tangent.U 1 := hp
    show levelMap (tangentMapWith f (scDerivGerm G₁ f)) 1 p =
      ((levelMap (E := E.shift) (F := F.shift) (levelMap f 1) 1 p.1,
        scDerivGerm G₁.shift (levelMap f 1) p.1 p.2) : F.shift.tangent 0)
    rw [hf.1.isSc1GermWith_scDerivGerm.levelMap_tangentMapWith hp']
    change ((levelMap f 2 p.1, levelDeriv (scDerivGerm G₁ f) 1 p.1 p.2) : F.tangent 1) = _
    rw [hf.1.isSc0.levelMap_shift hp'.1, IsSc1Germ.scDerivGerm_eqOn hC.shift h1 hp.1]

/-! ### Proposition 1.18 for germs: `f : U_{m+k} → F_m` is `C^k` -/

namespace ScNbhdGerm

/-- The inclusion `E_{m+k+1} → E_{m+1}` maps `U_{m+k+1}` into `U_{m+1}`. -/
lemma shift_inclK_mem (G₁ : ScNbhdGerm E C) {m k : ℕ} {x : E (m + k + 1)}
    (hx : x ∈ G₁.U (m + k + 1)) : E.shift.inclK m k x ∈ G₁.U (m + 1) :=
  G₁.shift.inclK_mem (m := m) (k := k) hx

lemma uniqueDiffOn (G₁ : ScNbhdGerm E C) (hC : IsQuadrantLike E C) (m : ℕ) :
    UniqueDiffOn ℝ (G₁.U m) := fun _ hx => G₁.uniqueDiffWithinAt hC m hx

end ScNbhdGerm

/-- **Proposition 1.18 for germs**, with the inclusion `E_n → E_m`, `n = m + k`, as a parameter:
if `f` is an sc^k-germ on `O(C, 0)` then `f_m ∘ ρ : U_n → F_m` is `C^k`.  The proof of
`IsSck.contDiffOn_levels'` with `U_m` in place of `U ∩ E_m`. -/
theorem IsSckGerm.contDiffOn_levels' : ∀ {k : ℕ} {E F : ScBanach} {C : Set (E 0)}
    {G₁ : ScNbhdGerm E C} {f : E 0 → F 0}, IsQuadrantLike E C → IsSckGerm k G₁ f →
    ∀ {m n : ℕ}, n = m + k → ∀ (ρ : E n →L[ℝ] E m),
      (∀ x, E.toBase m (ρ x) = E.toBase n x) → ContDiffOn ℝ k (levelMap f m ∘ ρ) (G₁.U n)
  | 0, E, F, C, G₁, f, _, hf, m, n, hn, ρ, hρ => by
    subst n
    rw [Nat.cast_zero, contDiffOn_zero]
    have hρ' : ∀ x, ρ x = x := fun x => E.toBase_injective m (hρ x)
    exact (hf.continuousOn m).congr fun x _ => by rw [Function.comp_apply, hρ']
  | k + 1, E, F, C, G₁, f, hC, hf, m, n, hn, ρ, hρ => by
    subst hn
    have hD := hf.1.isSc1GermWith_scDerivGerm
    have hρ' : ∀ x, E.incl m (E.shift.inclK m k x) = ρ x := fun x =>
      E.toBase_injective m (by rw [E.incl_shift_inclK, E.toBase_inclK, hρ])
    have hder : ∀ x ∈ G₁.U (m + (k + 1)), HasFDerivWithinAt (levelMap f m ∘ ρ)
        ((levelDeriv (scDerivGerm G₁ f) m (E.shift.inclK m k x)).comp ρ) (G₁.U (m + (k + 1))) x := by
      intro x hx
      have h1 := hD.hasFDerivWithinAt_level hC (G₁.shift_inclK_mem hx)
      have h2 := h1.comp x (E.shift.inclK m k).hasFDerivWithinAt
        fun y hy => G₁.shift_inclK_mem hy
      have e1 : (levelMap f m ∘ E.incl m) ∘ E.shift.inclK m k = levelMap f m ∘ ρ :=
        funext fun y => congrArg (levelMap f m) (hρ' y)
      have e2 : ((levelDeriv (scDerivGerm G₁ f) m (E.shift.inclK m k x)).comp (E.incl m)).comp
          (E.shift.inclK m k) = (levelDeriv (scDerivGerm G₁ f) m (E.shift.inclK m k x)).comp ρ :=
        ContinuousLinearMap.ext fun y => congrArg _ (hρ' y)
      rwa [e1, e2] at h2
    have hT := IsSckGerm.contDiffOn_levels' (k := k) hC.tangentSet hf.2 rfl (E.tangent.inclK m k)
      (E.tangent.toBase_inclK m k)
    rw [ScNbhdGerm.tangent_U] at hT
    unfold tangentMapGerm at hT
    have hΦ : ContDiffOn ℝ k (fun p : E (m + k + 1) × E (m + k) =>
        levelDeriv (scDerivGerm G₁ f) m (E.shift.inclK m k p.1) (E.inclK m k p.2))
        (G₁.U (m + k + 1) ×ˢ univ) := by
      refine (contDiff_snd.comp_contDiffOn hT).congr fun p hp => ?_
      have hmem : ((E.shift.inclK m k p.1, E.inclK m k p.2) : E.tangent m) ∈ G₁.tangent.U m :=
        ⟨G₁.shift_inclK_mem hp.1, mem_univ _⟩
      rw [Function.comp_apply, Function.comp_apply, E.tangent_inclK,
        hD.levelMap_tangentMapWith hmem]
    have hA := contDiffOn_clm_comp_of_isCompactOperator (G₁.relOpenConvex hC (m + k + 1))
      (G₁.uniqueDiffOn hC (m + k + 1)) (E.incl_isCompactOperator (m + k))
      (A := fun x => (levelDeriv (scDerivGerm G₁ f) m (E.shift.inclK m k x)).comp (E.inclK m k)) hΦ
    rw [Nat.cast_succ,
      contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (G₁.uniqueDiffOn hC (m + (k + 1)))]
    refine ⟨fun h0 => absurd h0 (by simp), _, ?_, hder⟩
    refine hA.congr fun x _ => ?_
    ext y
    exact congrArg (levelDeriv (scDerivGerm G₁ f) m (E.shift.inclK m k x))
      ((hρ' y).symm.trans (E.incl_shift_inclK m k y))

/-- **Proposition 1.18 for germs**: if `f` is an sc^k-germ on `O(C, 0)` then `f : U_{m+k} → F_m`
is `C^k` for every `m`. -/
theorem IsSckGerm.contDiffOn_levels {k : ℕ} (hC : IsQuadrantLike E C) (hf : IsSckGerm k G₁ f)
    (m : ℕ) : ContDiffOn ℝ k (levelMap f m ∘ E.inclK m k) (G₁.U (m + k)) :=
  hf.contDiffOn_levels' hC rfl (E.inclK m k) (E.toBase_inclK m k)

/-- **Proposition 1.18 for germs**, on the base level: `f : U_k → F_0` is `C^k`. -/
theorem IsSckGerm.contDiffOn_base {k : ℕ} (hC : IsQuadrantLike E C) (hf : IsSckGerm k G₁ f) :
    ContDiffOn ℝ k (f ∘ E.toBase k) (G₁.U k) := by
  have := hf.contDiffOn_levels' hC (Nat.zero_add k).symm (E.toBase k) fun _ => rfl
  rwa [funext (levelMap_zero f)] at this

end Polyfold
