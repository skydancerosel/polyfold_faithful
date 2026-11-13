import Polyfold.Chapter3.UntamedJump
import Polyfold.Chapter3.Book2021Germs
import Polyfold.Chapter3.TameGermTransfer

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §3.6:
**Theorem 3.6.8** (p. 136; 2017: Theorem 3.13; preprint: Theorem 3.54) and the sc-Fredholm germs of
**Definitions 3.1.4, 3.6.1, 3.6.3** (pp. 91, 134, 135), whose filling asks only for an sc-smooth
retraction (2017 and preprint: a tame one).  Gap G.79.

# Theorem 3.6.8 with untamed germ data: an example where the solution set is a half-line

## The text, paraphrased

(Definition 3.6.3, p. 135) `(f, x)` is an sc-Fredholm germ if in some strong bundle chart around
`x` the local section has a filling `g` (Definition 3.6.1: `r` an sc-smooth retraction, no
tameness in the 2021 text) and an sc⁺-section `s` with `s(0) = g(0)` such that `g − s` is
conjugated to a basic germ.  (Definition 3.6.6, p. 136) `(f, x)`, `f(x) = 0`, is in good position
if `f'(x)` is onto and, if `d_X(x) ≥ 1`, `ker f'(x)` is in good position to `C_xX`.
(Theorem 3.6.8, p. 136) For an sc-Fredholm section of a tame strong bundle, `f(x) = 0` and
`(f, x)` in good position: near `x` the solution set `S` is a sub-M-polyfold with a structure of
manifold with boundary with corners, and good position holds on `S`.  The proof (p. 137) takes the
chart of the germ data to cover a **tame** retraction.

## What is formalized

The local model `Polyfold.UntamedCorner`: `E = ℝ² ⊕ X ∋ ((a, t), w)` (`X` the weighted sequence
space), `C = [0, ∞) × ℝ × X`, `U = C ∩ {t < 1}`, `F = ℝ ⊕ X`, the strong bundle retraction
`R(((a, t), w), (x, h)) = (((0, t), 0), (0, π_t h))` with the moving rank-one projection `π_t` of
`UntamedJump.lean` (`π_t = 0` for `t ≤ 0`), and `g((a, t), w) = (a + ν(w)², w + π_t v)`
(`ν` a functional positive on the unit vectors, `v` a smooth vector positive at the positions).

* `isStrongBundleRetraction_R`: `R` is a strong bundle retraction of `U ◁ F` (2021 Definition
  2.6.1); it covers `r((a, t), w) = ((0, t), 0)`, with retract `O = {((0, t), 0) | t < 1} ≅ ℝ`
  (`mem_O`).  The fibre of `K = R(U ◁ F)` over `t` is `0` for `t ≤ 0` and a line for `0 < t < 1`.
  `not_isTame_baseRetr`: `r` is not tame.
* `isFilling2021_g`: `g` is a 2021 filling of the section `g|_O` of `K → O` (conditions (1)–(3)
  of Definition 3.6.1; (2) is `mem_O_of_fixed`, where the boundary `a ≥ 0` of `C` is used; (3)
  is `kerEquiv`, `Dk(0)((a, 0), w) = (a, w)`).  `isConjugateToBasicGerm_g`: `g` is a basic germ
  (`B = −π_t v`); `isScPlusGerm_zero`: the sc⁺-germ `s = 0`.  So the germ at `0` has the data of
  Definition 3.6.3.
* `isGoodPositionAtGerm_g`, `surjective_scDeriv_g`: the germ is in good position in the chart
  (`Dg(0)((a, t), w) = (a, w)` is onto, its kernel is `T₀O`, the `t`-axis).
* `solutionSet_eq`: **the solution set `{x ∈ O | g(x) = 0}` is the closed half-line
  `S = {((0, t), 0) | t ≤ 0}`**.
* `not_exists_retraction`: `S` is not the image of an sc¹ retraction of a neighbourhood of `0` in
  `O`; `not_isSubMPolyfold_solutionSet`: **`S` is not a sub-M-polyfold of the M-polyfold `O`**
  (`polyO`, the retract with its one chart; 2021 Definition 2.3.18).
* `isTame_polyO`, `degIndex_polyO`: `O` is a tame M-polyfold with `d_X = 0` everywhere (the
  chart `t : O → {t < 1} ⊆ ℝ¹`, `chartT`, is a chart of the structure);
  `chartDegIndex_selfChart_ne_zero`: in the chart of the germ data `d_C(φ(x)) ≠ 0`.
* `theorem_3_6_8_untamed_local` and `theorem_3_6_8_untamed_polyfold` collect these.

## What this says about the text, and what is not formalized

* **For the 2021 definitions as printed, with germ data in an untamed chart, conclusion (2) of
  Theorem 3.6.8 does not hold as we read it**: in this model `X = O ≅ ℝ` has no boundary
  (`d_X = 0`), `f'(x) : T_xX → K_x = 0` is onto, and the solution set is a half-line ending at
  `x`.  With germ data in a tame chart (the 2017 and preprint wording, and the chart taken in the
  proof on p. 137) the theorem is `theorem_3_6_8'` (`GlobalIFTNearbyOntoG.lean`).  So the reading
  "germ data in a tame chart" of V3.85/V3.103 is needed, also when `d_X(x) = 0` (Remark 3.6.7).
* In `E` the kernel of `Dg(0)` (the `t`-axis) is not in good position to `C`, as in the corner
  example of `Book2021Germs.lean` (`theorem_3_6_8_tame_step`); here the zero set of `g` continued
  to `a < 0` is the curve `a = −ν(π_t v)²`, `w = −π_t v`, which leaves `C` for `t > 0`.
* The strong bundle `K → O` as a `StrongBundle` over `polyO`, and the germ data at the other
  points, are formalized in `UntamedBundle*.lean` (`UntamedCorner.bundle`,
  `UntamedCorner.isScFredholmSection2021_sec`, `UntamedCorner.theorem_3_6_8_untamed_not`).  The
  statement proved in this file is the local one, for the germ at `0`.
* The example needs a fibre which jumps at `x`: if `ρ` is continuous in the operator norm and
  everything is of class `C¹` on one level, the classical implicit function theorem in a tame
  chart gives the conclusion.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace UntamedCorner

open ScOneExample Jump StrongRetr

/-! ### A functional positive on the unit vectors, and a smooth vector positive at the positions -/

lemma summable_nu (y : c0) : Summable fun k => (1 / 2 : ℝ) ^ k * y k := by
  refine Summable.of_norm_bounded (g := fun k => (1 / 2 : ℝ) ^ k * ‖y‖)
    (summable_geometric_two.mul_right ‖y‖) fun k => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (abs_apply_le_norm y k) (by positivity)

/-- The functional `ν(y) = Σ_k 2^{-k} y_k` on `c₀`. -/
def nu : c0 →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun y => ∑' k, (1 / 2 : ℝ) ^ k * y k
      map_add' := fun y z => by
        rw [← (summable_nu y).tsum_add (summable_nu z)]
        exact tsum_congr fun k => by simp [mul_add]
      map_smul' := fun r y => by
        rw [RingHom.id_apply, smul_eq_mul, ← tsum_mul_left]
        exact tsum_congr fun k => by simp; ring }
    2 (fun y => by
      change ‖∑' k, (1 / 2 : ℝ) ^ k * y k‖ ≤ 2 * ‖y‖
      have h1 : Summable fun k => ‖(1 / 2 : ℝ) ^ k * y k‖ := (summable_nu y).norm
      have h2 : Summable fun k => (1 / 2 : ℝ) ^ k * ‖y‖ := summable_geometric_two.mul_right ‖y‖
      calc ‖∑' k, (1 / 2 : ℝ) ^ k * y k‖ ≤ ∑' k, ‖(1 / 2 : ℝ) ^ k * y k‖ :=
            norm_tsum_le_tsum_norm h1
        _ ≤ ∑' k, (1 / 2 : ℝ) ^ k * ‖y‖ := h1.tsum_le_tsum (fun k => by
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_left (abs_apply_le_norm y k) (by positivity)) h2
        _ = 2 * ‖y‖ := by rw [tsum_mul_right, tsum_geometric_two])

lemma nu_apply (y : c0) : nu y = ∑' k, (1 / 2 : ℝ) ^ k * y k := rfl

lemma nu_unitVec (j : ℕ) : nu (unitVec j) = (1 / 2 : ℝ) ^ j := by
  rw [nu_apply, tsum_eq_single j fun k hk => by rw [unitVec_apply, if_neg hk, mul_zero],
    unitVec_apply, if_pos rfl, mul_one]

lemma nu_unitVec_pos (j : ℕ) : 0 < nu (unitVec j) := by rw [nu_unitVec]; positivity

/-- The level-`m` coordinates `16^{im} 16^{-i²}` of the smooth vector at the positions. -/
def vseq (m : ℕ) : c0 :=
  mkC0 (fun i => (16 : ℝ) ^ (i * m) * (1 / 16 : ℝ) ^ (i * i)) (by
    refine squeeze_zero' (Eventually.of_forall fun i => by positivity) ?_
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 16 : ℝ)) (by norm_num) (by norm_num))
    filter_upwards [eventually_ge_atTop (m + 1)] with i hi
    have h1 : i * m + i ≤ i * i := by nlinarith
    have h2 : (16 : ℝ) ^ (i * m) * 16 ^ i ≤ 16 ^ (i * i) := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) h1
    rw [one_div_pow, one_div_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity),
      one_mul]
    exact h2)

lemma vseq_apply (m i : ℕ) : vseq m i = (16 : ℝ) ^ (i * m) * (1 / 16 : ℝ) ^ (i * i) := rfl

/-- The smooth vector on level `m`. -/
def vlvl (m : ℕ) : X m := emb (vseq m)

/-- The smooth vector `v ∈ X_∞`, with `v_{K_i} = 16^{-i²}`. -/
def v : X 0 := vlvl 0

lemma X_toBase_vlvl (m : ℕ) : X.toBase m (vlvl m) = v := by
  refine c0_ext_pos (fun i => ?_) fun k hk => ?_
  · rw [X_toBase_apply]
    change w (pos i) ^ m * emb (vseq m) (pos i) = emb (vseq 0) (pos i)
    rw [emb_apply_pos, emb_apply_pos, vseq_apply, vseq_apply, w_pos_eq, mul_zero, pow_zero,
      one_mul, ← mul_assoc, ← pow_mul, ← mul_pow]
    norm_num
  · rw [X_toBase_apply]
    change w k ^ m * emb (vseq m) k = emb (vseq 0) k
    rw [emb_apply_of_not _ hk, emb_apply_of_not _ hk, mul_zero]

lemma v_mem_smooth : v ∈ X.smooth := X.mem_smooth_iff.2 fun m => ⟨vlvl m, X_toBase_vlvl m⟩

lemma v_pos (i : ℕ) : 0 < (v : c0) (pos i) := by
  change 0 < emb (vseq 0) (pos i)
  rw [emb_apply_pos, vseq_apply]; positivity

/-! ### The local model -/

/-- The chart space `E = ℝ² ⊕ X ∋ ((a, t), w)`. -/
abbrev E : ScBanach := ScBanach.paramProd (ℝ × ℝ) X

/-- The fibre `F = ℝ ⊕ X ∋ (x, h)`. -/
abbrev F : ScBanach := ScBanach.paramProd ℝ X

/-- The partial quadrant `[0, ∞) × ℝ` of `ℝ²`. -/
def Ct : Set (ℝ × ℝ) := {p | 0 ≤ p.1}

/-- The partial quadrant `C = [0, ∞) × ℝ × X` of `E`. -/
abbrev C : Set (E 0) := Ct ×ˢ (univ : Set (X 0))

/-- The domain `U = C ∩ {t < 1}`. -/
def U : Set (E 0) := {p | 0 ≤ p.1.1 ∧ p.1.2 < 1}

/-- `ℝ² ≅ ℝ¹ ⊕ ℝ`. -/
def isoCt :
    ScIso (ScBanach.const (ℝ × ℝ)) ((ScBanach.const (Fin 1 → ℝ)).prod (ScBanach.const ℝ)) where
  lvl _ := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.prodCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)
  incl_comm _ _ := rfl

lemma isPartialQuadrant_Ct : IsPartialQuadrant (ScBanach.const (ℝ × ℝ)) Ct := by
  refine ⟨1, ScBanach.const ℝ, isoCt, ?_⟩
  ext p
  change 0 ≤ p.1 ↔ ∀ i : Fin 1, 0 ≤ p.1
  exact ⟨fun h _ => h, fun h => h 0⟩

lemma isPartialQuadrant_C : IsPartialQuadrant E C := isPartialQuadrant_Ct.prod_univ X

lemma relOpen_U : IsRelOpenInQuadrant E C U :=
  ⟨isPartialQuadrant_C, {p | p.1.2 < 1},
    isOpen_lt (continuous_snd.comp continuous_fst) continuous_const, by
      ext p; exact ⟨fun h => ⟨h.2, h.1, mem_univ _⟩, fun h => ⟨h.2.1, h.1⟩⟩⟩

lemma zero_mem_U : (0 : E 0) ∈ U := ⟨le_rfl, zero_lt_one⟩

/-! ### Coordinates as sc-operators -/

/-- `((a, t), w) ↦ a`. -/
def aOp : ScOperator E (ScBanach.const ℝ) where
  lvl m := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (X m))
  incl_comm _ _ := rfl

/-- `((a, t), w) ↦ t`. -/
def tOp : ScOperator E (ScBanach.const ℝ) where
  lvl m := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (X m))
  incl_comm _ _ := rfl

/-- `((a, t), w) ↦ ν(w)`. -/
def nuOp : ScOperator E (ScBanach.const ℝ) where
  lvl m := (nu.comp (X.toBase m)).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (X m))
  incl_comm _ _ := rfl

/-- `((a, t), w) ↦ ((0, t), 0)`: the base retraction `r`. -/
def rOp : ScOperator E E where
  lvl m := ((0 : (ℝ × ℝ) × X m →L[ℝ] ℝ).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (X m)))).prod
    (0 : (ℝ × ℝ) × X m →L[ℝ] X m)
  incl_comm m _ := Prod.ext rfl (map_zero (X.incl m))

lemma rOp_apply (p : E 0) : rOp 0 p = ((0, p.1.2), 0) := rfl

section Fibre

variable (V : ScBanach)

/-- `(((a, t), w), (x, h)) ↦ ((0, t), 0)` on `E ⊕ (ℝ ⊕ V)`. -/
def baseOp : ScOperator (E.prod ((ScBanach.const ℝ).prod V)) E where
  lvl m := (rOp m).comp (ContinuousLinearMap.fst ℝ (E m) (ℝ × V m))
  incl_comm m x := rOp.incl_comm m x.1

/-- `(((a, t), w), (x, h)) ↦ (t, h)` on `E ⊕ (ℝ ⊕ V)`. -/
def tfOp : ScOperator (E.prod ((ScBanach.const ℝ).prod V)) ((ScBanach.const ℝ).prod V) where
  lvl m := ((tOp m).comp (ContinuousLinearMap.fst ℝ (E m) (ℝ × V m))).prod
    ((ContinuousLinearMap.snd ℝ ℝ (V m)).comp (ContinuousLinearMap.snd ℝ (E m) (ℝ × V m)))
  incl_comm _ _ := rfl

variable {V}

/-- The strong bundle retraction built from a jump family `J` on the fibre scale `V`:
`(((a, t), w), (x, h)) ↦ (((0, t), 0), (0, A(t)h))`. -/
def RG (J : Family V) (q : (E.prod ((ScBanach.const ℝ).prod V)) 0) :
    (E.prod ((ScBanach.const ℝ).prod V)) 0 :=
  (((0, q.1.1.2), 0), (0, J.A 0 q.1.1.2 q.2.2))

theorem isScSmooth_RG (J : Family V) :
    IsScSmooth (E := E.prod ((ScBanach.const ℝ).prod V)) (F := E.prod ((ScBanach.const ℝ).prod V))
      univ (RG J) := by
  have hU := isScDomain_univ (E.prod ((ScBanach.const ℝ).prod V))
  have h1 := (baseOp V).isScSmooth hU
  have h2 :=
    (ScOperator.zeroOp (E.prod ((ScBanach.const ℝ).prod V)) (ScBanach.const ℝ)).isScSmooth hU
  have h3 := IsScSmooth.comp hU (isScDomain_univ _) J.isScSmooth_map ((tfOp V).isScSmooth hU)
    (mapsTo_univ _ _)
  exact (h1.scPair hU (h2.scPair hU h3)).congr hU fun q _ => rfl

end Fibre

/-! ### The strong bundle retraction and the filling -/

/-- A constant map with a smooth value is sc-smooth. -/
theorem isScSmooth_const {G H : ScBanach} {V : Set (G 0)} (hV : IsScDomain G V) {k : H 0}
    (hk : k ∈ H.smooth) : IsScSmooth (E := G) (F := H) V fun _ => k := by
  refine IsScSmooth.of_contDiffOn_levels hV (fun m _ _ => H.mem_smooth_iff.1 hk m) fun m => ?_
  obtain ⟨y, hy⟩ := H.mem_smooth_iff.1 hk m
  have : ∀ z ∈ G.lvlSet V m, levelMap (E := G) (F := H) (fun _ => k) m z = y :=
    fun z _ => levelMap_eq_of_toBase_eq hy
  exact contDiffOn_const.congr this

/-- **The strong bundle retraction** `R(((a, t), w), (x, h)) = (((0, t), 0), (0, π_t h))`. -/
def R : E 0 × F 0 → E 0 × F 0 := RG family

lemma R_apply (q : E 0 × F 0) : R q = (((0, q.1.1.2), 0), (0, proj q.1.1.2 q.2.2)) := rfl

/-- **The filling** `g((a, t), w) = (a + ν(w)², w + π_t v)`. -/
def g : E 0 → F 0 := fun p => (p.1.1 + nu p.2 ^ 2, p.2 + proj p.1.2 v)

theorem isScSmooth_g_univ : IsScSmooth (E := E) (F := F) univ g := by
  have hU := isScDomain_univ E
  have ha := aOp.isScSmooth hU
  have hν := nuOp.isScSmooth hU
  have h1 : IsScSmooth (E := E) (F := ScBanach.const ℝ) univ
      (fun p => aOp 0 p + nuOp 0 p • nuOp 0 p) := ha.add hU (IsScSmooth.smul hU hν hν)
  have hpair : IsScSmooth (E := E) (F := (ScBanach.const ℝ).prod X) univ
      (scPair (tOp 0) fun _ => v) :=
    (tOp.isScSmooth hU).scPair hU (isScSmooth_const hU v_mem_smooth)
  have h2 : IsScSmooth (E := E) (F := X) univ
      (fun p => (ScBanach.const (ℝ × ℝ)).prodSndOp X 0 p +
        (family.map ∘ scPair (tOp 0) fun _ => v) p) :=
    (((ScBanach.const (ℝ × ℝ)).prodSndOp X).isScSmooth hU).add hU
      (IsScSmooth.comp hU (isScDomain_univ _) family.isScSmooth_map hpair (mapsTo_univ _ _))
  refine (h1.scPair hU h2).congr hU fun p _ => ?_
  refine Prod.ext ?_ rfl
  change p.1.1 + nu p.2 * nu p.2 = p.1.1 + nu p.2 ^ 2
  rw [sq]

theorem isScSmooth_g : IsScSmooth U g :=
  isScSmooth_g_univ.of_subset relOpen_U.isScDomain (subset_univ _)

lemma F_toBase (k : ℕ) (h : F k) : F.toBase k h = ((h.1, X.toBase k h.2) : F 0) :=
  ScBanach.paramProd_toBase X k h

lemma E_toBase (m : ℕ) (p : E m) : E.toBase m p = ((p.1, X.toBase m p.2) : E 0) :=
  ScBanach.paramProd_toBase X m p

/-- `R` is a strong bundle retraction of `U ◁ F`. -/
theorem isStrongBundleRetraction_R : IsStrongBundleRetraction (E := E) (F := F) U R where
  mapsTo q hq := ⟨⟨le_rfl, hq.1.2⟩, mem_univ _⟩
  fst_independent _ _ _ _ := rfl
  fiber_linear u _ :=
    ⟨fun h h' => Prod.ext (add_zero (0 : ℝ)).symm (map_add (proj u.1.2) h.2 h'.2),
      fun c h => Prod.ext (smul_zero c).symm (map_smul (proj u.1.2) c h.2)⟩
  preserves_filtration m k _ u _ hu h hh := by
    obtain ⟨u', rfl⟩ := hu
    obtain ⟨h', rfl⟩ := hh
    refine ⟨⟨((0, u'.1.2), 0), ?_⟩, ⟨(0, family.A k u'.1.2 h'.2), ?_⟩⟩
    · rw [E_toBase, E_toBase, map_zero]; rfl
    · rw [F_toBase, F_toBase, family.toBase_A, E_toBase]; rfl
  isScSmooth_zero :=
    (isScSmooth_RG family).of_subset (relOpen_U.prod_univ F).isScDomain (subset_univ _)
  isScSmooth_one := by
    have hdom := (relOpen_U.prod_univ F.shift).isScDomain
    refine ((isScSmooth_RG family.shift).of_subset hdom (subset_univ _)).congr hdom fun q _ => ?_
    refine Prod.ext rfl ?_
    change ((0 : ℝ), family.A 1 q.1.1.2 q.2.2) =
      invFun (F.toBase 1) (0, proj q.1.1.2 (X.toBase 1 q.2.2))
    have h : F.toBase 1 ((0 : ℝ), family.A 1 q.1.1.2 q.2.2) =
        (0, proj q.1.1.2 (X.toBase 1 q.2.2)) := by
      rw [F_toBase, family.toBase_A]; rfl
    rw [← h, leftInverse_invFun (F.toBase_injective 1)]
  idem q hq := by
    rw [R_apply, R_apply]
    exact Prod.ext rfl (Prod.ext rfl (proj_proj hq.1.2 q.2.2))

/-! ### The retract, the solution set, the conditions (1) and (2) of the filling -/

lemma r_R (u : E 0) : r R u = ((0, u.1.2), 0) := rfl

lemma ρ_R (u : E 0) (h : F 0) : ρ R u h = (0, proj u.1.2 h.2) := rfl

/-- The retract `O = r(U) = {((0, t), 0) | t < 1}`. -/
lemma mem_O {x : E 0} : x ∈ r R '' U ↔ x.1.1 = 0 ∧ x.1.2 < 1 ∧ x.2 = 0 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨rfl, hu.2, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨x, ⟨h1.ge, h2⟩, Prod.ext (Prod.ext h1.symm rfl) h3.symm⟩

lemma zero_mem_O : (0 : E 0) ∈ r R '' U := mem_O.2 ⟨rfl, zero_lt_one, rfl⟩

lemma g_zero : g 0 = 0 := by
  change (((0 : ℝ) + nu (0 : c0) ^ 2, (0 : c0) + proj 0 v) : F 0) = 0
  rw [map_zero, proj_of_nonpos le_rfl]; simp

/-- `g` is a section of `K → O`: `(x, g(x)) ∈ K = R(U ◁ F)` for `x ∈ O`. -/
lemma g_section : ∀ x ∈ r R '' U, (x, g x) ∈ R '' (U ×ˢ (univ : Set (F 0))) := by
  intro x hx
  obtain ⟨h1, h2, h3⟩ := mem_O.1 hx
  refine ⟨(x, ((0 : ℝ), v)), ⟨⟨h1.ge, h2⟩, mem_univ _⟩, ?_⟩
  rw [R_apply]
  refine Prod.ext (Prod.ext (Prod.ext h1.symm rfl) h3.symm) (Prod.ext ?_ ?_)
  · change (0 : ℝ) = x.1.1 + nu x.2 ^ 2
    rw [h1, h3, map_zero]; simp
  · change proj x.1.2 v = x.2 + proj x.1.2 v
    rw [h3, zero_add]

/-- Condition (2) of the filling: `g(y) = ρ(r(y))g(y)` forces `y ∈ O`.  **The boundary `a ≥ 0` of
the chart is used here.** -/
lemma mem_O_of_fixed {y : E 0} (hy : y ∈ U) (h : g y = ρ R (r R y) (g y)) : y ∈ r R '' U := by
  have h1 : y.1.1 + nu y.2 ^ 2 = 0 := congrArg Prod.fst h
  have h2 : y.2 + proj y.1.2 v = proj y.1.2 (y.2 + proj y.1.2 v) := congrArg Prod.snd h
  rw [map_add, proj_proj hy.2] at h2
  have h3 : proj y.1.2 y.2 = y.2 := (add_right_cancel h2).symm
  have ha : y.1.1 = 0 := by nlinarith [hy.1, sq_nonneg (nu y.2)]
  have hν : nu y.2 = 0 := by
    have : nu y.2 ^ 2 = 0 := by nlinarith [hy.1, sq_nonneg (nu y.2)]
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  exact mem_O.2 ⟨ha, hy.2, eq_zero_of_proj_eq hy.2 (fun i => nu_unitVec_pos (pos i)) h3 hν⟩

/-- **The solution set**: for `x ∈ U`, `g(x) = 0` iff `x = ((0, t), 0)` with `t ≤ 0`. -/
theorem g_eq_zero_iff {x : E 0} (hx : x ∈ U) : g x = 0 ↔ x.1.1 = 0 ∧ x.1.2 ≤ 0 ∧ x.2 = 0 := by
  constructor
  · intro h
    have hfix : g x = ρ R (r R x) (g x) := by
      rw [h, ρ_R]; exact Prod.ext rfl (map_zero _).symm
    obtain ⟨h1, h2, h3⟩ := mem_O.1 (mem_O_of_fixed hx hfix)
    refine ⟨h1, ?_, h3⟩
    by_contra hlt
    have hv : proj x.1.2 v = 0 := by
      have := congrArg Prod.snd h
      change x.2 + proj x.1.2 v = 0 at this
      rwa [h3, zero_add] at this
    exact proj_ne_zero (not_le.1 hlt) h2 v_pos hv
  · rintro ⟨h1, h2, h3⟩
    change ((x.1.1 + nu x.2 ^ 2, x.2 + proj x.1.2 v) : F 0) = 0
    rw [h1, h3, map_zero, proj_of_nonpos h2]; simp

/-- The solution set of the section `g|_O`: the closed half-line `{((0, t), 0) | t ≤ 0}`. -/
def S : Set (E 0) := {x | x.1.1 = 0 ∧ x.1.2 ≤ 0 ∧ x.2 = 0}

theorem solutionSet_eq : {x | x ∈ r R '' U ∧ g x = 0} = S := by
  ext x
  constructor
  · rintro ⟨hx, hg⟩
    obtain ⟨u, hu, rfl⟩ := hx
    exact (g_eq_zero_iff (isStrongBundleRetraction_R.mapsTo (x := (u, 0)) ⟨hu, mem_univ _⟩).1).1 hg
  · rintro ⟨h1, h2, h3⟩
    have hx : x ∈ r R '' U := mem_O.2 ⟨h1, lt_of_le_of_lt h2 zero_lt_one, h3⟩
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨⟨u, hu, rfl⟩, ?_⟩
    exact (g_eq_zero_iff (isStrongBundleRetraction_R.mapsTo (x := (u, 0)) ⟨hu, mem_univ _⟩).1).2
      ⟨h1, h2, h3⟩

/-! ### The linearizations at `0` -/

/-- The sc-derivative at `0` from the derivative of the level-`1` form within `U₁`. -/
theorem scDeriv_zero_eq_of_lvlOne {E' F' : ScBanach} {C' U' : Set (E' 0)}
    (hU : IsRelOpenInQuadrant E' C' U') {f : E' 0 → F' 0} (hf : IsSc1 U' f)
    (h0 : (0 : E' 0) ∈ U') {D : E' 0 →L[ℝ] F' 0}
    (hD : HasFDerivWithinAt (f ∘ E'.toBase 1) (D.comp (E'.toBase 1)) (E'.lvlSet U' 1) 0) :
    scDeriv U' f 0 = D := by
  have hz : (0 : E' 1) ∈ E'.lvlSet U' 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  exact ContinuousLinearMap.ext_of_comp_toBase_one (E := E')
    ((hU.isScDomain.uniqueDiffWithinAt 1 0 hz).eq (hf.isSc1With_scDeriv.hasFDerivWithinAt 0 hz) hD)

/-- `Dg(0) = Dk(0)`: `((a, t), w) ↦ (a, w)`. -/
def Lg : E 0 →L[ℝ] F 0 :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (X 0))).prod
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (X 0))

lemma Lg_apply (p : E 0) : Lg p = (p.1.1, p.2) := rfl

lemma E_toBase_one (x : E 1) : E.toBase 1 x = ((x.1, X.toBase 1 x.2) : E 0) := E_toBase 1 x

/-- `(t, w) ↦ π_t(ι w)` has derivative `0` at `0` on level `1`. -/
lemma hasFDerivAt_proj_toBase :
    HasFDerivAt (fun x : E 1 => proj x.1.2 (X.toBase 1 x.2)) (0 : E 1 →L[ℝ] X 0) 0 := by
  let L : E 1 →L[ℝ] ((ScBanach.const ℝ).prod X) 1 :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (X 1))).prod
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (X 1))
  have h := (family.hasFDerivAt_map (L 0)).comp (0 : E 1) L.hasFDerivAt
  have hL : L 0 = 0 := map_zero L
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => rfl)
  refine ContinuousLinearMap.ext fun q => ?_
  rw [hL]
  change family.D (0 : ((ScBanach.const ℝ).prod X) 1)
    (((ScBanach.const ℝ).prod X).toBase 1 (L q)) = 0
  rw [Family.D_apply]
  change (((ScBanach.const ℝ).prod X).toBase 1 (L q)).1 • T 1 1 0 0 (0 : X 1) +
    proj 0 (((ScBanach.const ℝ).prod X).toBase 1 (L q)).2 = 0
  rw [map_zero, smul_zero, proj_of_nonpos le_rfl, add_zero]

/-- `t ↦ π_t v` has derivative `0` at `0` on level `1` (as a function of `((a, t), w)`). -/
lemma hasFDerivAt_proj_v :
    HasFDerivAt (fun x : E 1 => proj x.1.2 v) (0 : E 1 →L[ℝ] X 0) 0 := by
  let L : E 1 →L[ℝ] ((ScBanach.const ℝ).prod X) 1 :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (X 1))).prod
      (0 : E 1 →L[ℝ] X 1)
  have hd : HasFDerivAt (fun x : E 1 => L x + (0, vlvl 1)) L 0 := L.hasFDerivAt.add_const _
  have h := (family.hasFDerivAt_map (L 0 + (0, vlvl 1))).comp (0 : E 1) hd
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  · refine ContinuousLinearMap.ext fun q => ?_
    have hL : L 0 + ((0 : ℝ), vlvl 1) = ((0 : ℝ), vlvl 1) := by rw [map_zero, zero_add]
    rw [hL]
    change family.D (((0 : ℝ), vlvl 1) : ((ScBanach.const ℝ).prod X) 1)
      (((ScBanach.const ℝ).prod X).toBase 1 (L q)) = 0
    rw [Family.D_apply]
    change (((ScBanach.const ℝ).prod X).toBase 1 (L q)).1 • T 1 1 0 0 (vlvl 1) +
      proj 0 (((ScBanach.const ℝ).prod X).toBase 1 (L q)).2 = 0
    rw [T_one_one_of_nonpos le_rfl, proj_of_nonpos le_rfl]; simp
  · change proj x.1.2 v = proj (x.1.2 + 0) (X.toBase 1 ((0 : X 1) + vlvl 1))
    rw [add_zero, zero_add, X_toBase_vlvl 1]

/-- `ν(ι w)²` has derivative `0` at `0`. -/
lemma hasFDerivAt_nu_sq :
    HasFDerivAt (fun x : E 1 => nu (X.toBase 1 x.2) ^ 2) (0 : E 1 →L[ℝ] ℝ) 0 := by
  have hl : HasFDerivAt (fun x : E 1 => nu (X.toBase 1 x.2))
      ((nu.comp (X.toBase 1)).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (X 1))) 0 :=
    ((nu.comp (X.toBase 1)).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (X 1))).hasFDerivAt
  refine (hl.pow 2).congr_fderiv ?_
  change (2 • nu (X.toBase 1 (0 : E 1).2) ^ (2 - 1)) • _ = (0 : E 1 →L[ℝ] ℝ)
  rw [show ((0 : E 1).2) = (0 : X 1) from rfl, map_zero, map_zero]; simp

lemma hasFDerivAt_a : HasFDerivAt (fun x : E 1 => x.1.1)
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (X 1))) 0 :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (X 1))).hasFDerivAt

lemma hasFDerivAt_w : HasFDerivAt (fun x : E 1 => X.toBase 1 x.2)
    ((X.toBase 1).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (X 1))) 0 :=
  ((X.toBase 1).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (X 1))).hasFDerivAt

/-- The level-`1` form of `g` is differentiable at `0`, with derivative `Lg`. -/
lemma hasFDerivAt_g : HasFDerivAt (g ∘ E.toBase 1) (Lg.comp (E.toBase 1)) 0 := by
  have h1 := hasFDerivAt_a.add hasFDerivAt_nu_sq
  have h2 := hasFDerivAt_w.add hasFDerivAt_proj_v
  refine ((h1.prodMk h2).congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  · refine ContinuousLinearMap.ext fun q => ?_
    change ((q.1.1 + (0 : ℝ), X.toBase 1 q.2 + (0 : X 0)) : F 0) = Lg (E.toBase 1 q)
    rw [E_toBase_one, Lg_apply, add_zero, add_zero]
  · rw [Function.comp_apply, E_toBase_one]; rfl

lemma fillDefect_apply {y : E 0} (hy : y.1.2 < 1) :
    fillDefect R g y = (y.1.1 + nu y.2 ^ 2, y.2 - proj y.1.2 y.2) := by
  change g y - ρ R (r R y) (g y) = _
  rw [ρ_R, r_R]
  refine Prod.ext ?_ ?_
  · change y.1.1 + nu y.2 ^ 2 - 0 = _
    rw [sub_zero]
  · change y.2 + proj y.1.2 v - proj y.1.2 (y.2 + proj y.1.2 v) = y.2 - proj y.1.2 y.2
    rw [map_add, proj_proj hy]; abel

/-- The level-`1` form of `k = [1 − ρ(r)]g` is differentiable at `0` within `U₁`, with derivative
`Lg`. -/
lemma hasFDerivWithinAt_fillDefect :
    HasFDerivWithinAt (fillDefect R g ∘ E.toBase 1) (Lg.comp (E.toBase 1)) (E.lvlSet U 1) 0 := by
  have h1 := hasFDerivAt_a.add hasFDerivAt_nu_sq
  have h2 := hasFDerivAt_w.sub hasFDerivAt_proj_toBase
  have he : ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (X 1)) +
        (0 : E 1 →L[ℝ] ℝ)).prod
      ((X.toBase 1).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (X 1)) - (0 : E 1 →L[ℝ] X 0)) =
      Lg.comp (E.toBase 1) := by
    refine ContinuousLinearMap.ext fun q => ?_
    change ((q.1.1 + (0 : ℝ), X.toBase 1 q.2 - (0 : X 0)) : F 0) = Lg (E.toBase 1 q)
    rw [E_toBase_one, Lg_apply, add_zero, sub_zero]
  have h := ((h1.prodMk h2).congr_fderiv he).hasFDerivWithinAt (s := E.lvlSet U 1)
  refine h.congr (fun x hx => ?_) ?_
  · rw [Function.comp_apply, fillDefect_apply (y := E.toBase 1 x) hx.2, E_toBase_one]; rfl
  · rw [Function.comp_apply, map_zero, fillDefect_apply (y := (0 : E 0)) zero_lt_one]
    change _ = ((0 : ℝ) + nu (X.toBase 1 (0 : X 1)) ^ 2,
      X.toBase 1 (0 : X 1) - proj 0 (X.toBase 1 (0 : X 1)))
    rw [map_zero]; rfl

lemma scDeriv_g : scDeriv U g (0 : E 1) = Lg :=
  scDeriv_zero_eq_of_lvlOne relOpen_U isScSmooth_g.isSc1 zero_mem_U
    hasFDerivAt_g.hasFDerivWithinAt

lemma isScSmooth_fillDefect : IsScSmooth U (fillDefect R g) :=
  fillDefect_isScSmooth relOpen_U isStrongBundleRetraction_R isScSmooth_g

lemma scDeriv_fillDefect : scDeriv U (fillDefect R g) (0 : E 1) = Lg :=
  scDeriv_zero_eq_of_lvlOne relOpen_U isScSmooth_fillDefect.isSc1 zero_mem_U
    hasFDerivWithinAt_fillDefect

lemma scDeriv_r : scDeriv U (r R) (0 : E 1) = rOp 0 :=
  scDeriv_zero_eq_of_hasFDerivAt relOpen_U
    ((isStrongBundleRetraction_R.baseRetraction relOpen_U).isScSmooth.isSc1) zero_mem_U
    (rOp 0).hasFDerivAt

/-! ### The filling (2021 Definitions 3.1.4 and 3.6.1) -/

lemma mem_ker_scDeriv_r {x : E 0} :
    x ∈ LinearMap.ker ((scDeriv U (r R) (0 : E 1) : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0) ↔
      x.1.2 = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, scDeriv_r, rOp_apply]
  constructor
  · intro h; exact congrArg (fun p : E 0 => p.1.2) h
  · intro h; rw [h]; rfl

lemma ρCLM_zero (h : F 0) : ρCLM isStrongBundleRetraction_R zero_mem_U h = 0 := by
  rw [ρCLM_apply, ρ_R]
  exact Prod.ext rfl (proj_of_nonpos le_rfl h.2)

/-- `Dk(0) : ker Dr(0) = {t = 0} → ker ρ(0) = F`, `((a, 0), w) ↦ (a, w)`. -/
def kerEquiv :
    LinearMap.ker ((scDeriv U (r R) (0 : E 1) : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0) ≃L[ℝ]
      LinearMap.ker ((ρCLM isStrongBundleRetraction_R zero_mem_U : F 0 →L[ℝ] F 0) :
        F 0 →ₗ[ℝ] F 0) where
  toFun x := ⟨Lg x, LinearMap.mem_ker.2 (ρCLM_zero _)⟩
  map_add' x y := Subtype.ext (map_add Lg (x : E 0) y)
  map_smul' c x := Subtype.ext (map_smul Lg c (x : E 0))
  invFun y := ⟨((((y : F 0).1, 0), (y : F 0).2) : E 0), mem_ker_scDeriv_r.2 rfl⟩
  left_inv x := Subtype.ext (Prod.ext (Prod.ext rfl (mem_ker_scDeriv_r.1 x.2).symm) rfl)
  right_inv _ := Subtype.ext rfl
  continuous_toFun := (Lg.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := Continuous.subtype_mk
    (((continuous_fst.comp continuous_subtype_val).prodMk continuous_const).prodMk
      (continuous_snd.comp continuous_subtype_val)) _

/-- `g` is a filled version (whole-chart) of the section `g|_O` of `K → O`. -/
theorem isFilledVersion_g :
    IsFilledVersion relOpen_U isStrongBundleRetraction_R zero_mem_U g g :=
  ⟨isScSmooth_g, ⟨Eventually.of_forall fun _ _ => rfl,
    Eventually.of_forall fun _ hy h => mem_O_of_fixed hy h, isScSmooth_fillDefect.isSc1,
    ⟨kerEquiv, fun x => by
      change Lg (x : E 0) = scDeriv U (fillDefect R g) 0 (x : E 0)
      rw [scDeriv_fillDefect]⟩⟩⟩

/-- **`g` is a 2021 filling** of the section `g|_O` of the strong local bundle `K → O` (2021
Definitions 3.1.4 and 3.6.1; the base retraction `r((a, t), w) = ((0, t), 0)` is not tame). -/
theorem isFilling2021_g :
    IsFilling2021 relOpen_U isStrongBundleRetraction_R zero_mem_U g g :=
  isFilledVersion_g.isFilling2021 zero_mem_O

/-! ### `g` is a basic germ -/

/-- The sc⁰-contraction germ `B((a, t), w) = −π_t v` (constant in `w`). -/
def Bc : (ℝ × ℝ) × X 0 → X 0 := fun p => -proj p.1.2 v

lemma isScSmooth_Bc : IsScSmooth (E := E) (F := X) U Bc := by
  have hU := relOpen_U.isScDomain
  have hpair : IsScSmooth (E := E) (F := (ScBanach.const ℝ).prod X) U
      (scPair (tOp 0) fun _ => v) :=
    (tOp.isScSmooth hU).scPair hU (isScSmooth_const hU v_mem_smooth)
  exact ((IsScSmooth.comp hU (isScDomain_univ _) family.isScSmooth_map hpair
    (mapsTo_univ _ _)).neg hU).congr hU fun _ _ => rfl

theorem isBasicGerm_g :
    IsBasicGerm (Q := ℝ) Ct (ScNbhdGerm.ofSet relOpen_U.relOpen zero_mem_U) g Bc where
  isScSmooth := IsScSmooth.isScSmoothGerm isPartialQuadrant_C.isQuadrantLike relOpen_U.relOpen
    zero_mem_U isScSmooth_g
  f_zero := g_zero
  snd_eq x _ := (sub_neg_eq_add x.2 (proj x.1.2 v)).symm
  contraction :=
    { isSc0 := IsSc0.isSc0Germ relOpen_U.relOpen zero_mem_U (isScSmooth_Bc 0)
      B_zero := by
        change -proj 0 v = 0
        rw [proj_of_nonpos le_rfl, neg_zero]
      contraction := fun ε hε m => ⟨1, one_pos, fun a ha har w w' _ _ => ⟨by
        change E.toBase m (a, w) ∈ U
        rw [E_toBase]
        exact ⟨ha, lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt (norm_snd_le a) har)⟩, by
        have h : levelB Bc m (a, w) = levelB Bc m (a, w') := by
          change invFun (X.toBase m) (Bc (E.toBase m (a, w))) =
            invFun (X.toBase m) (Bc (E.toBase m (a, w')))
          rw [E_toBase, E_toBase]; rfl
        rw [h, sub_self, norm_zero]
        exact mul_nonneg hε.le (norm_nonneg _)⟩⟩ }

/-- **`g` is conjugated to a basic germ** (it is one; the conjugation is the identity). -/
theorem isConjugateToBasicGerm_g : IsConjugateToBasicGerm (E := E) (F := F) U g := by
  have hid := isStrongBundleRetraction_id_of_relOpen (F := F) relOpen_U
  exact ⟨ℝ × ℝ, ℝ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, X, Ct, U, id, id, ScNbhdGerm.ofSet relOpen_U.relOpen zero_mem_U, g, Bc,
    isPartialQuadrant_Ct, relOpen_U,
    ⟨hid.toIsStrongBundleMap, hid.toIsStrongBundleMap, fun _ _ => rfl, fun _ _ => rfl⟩, rfl,
    fun _ hx => hx, isBasicGerm_g, Eventually.of_forall fun _ _ => rfl⟩

/-- The sc⁺-germ `s = 0` of 2021 Definition 3.6.3: `s(0) = g(0)` and `g − s = g`. -/
theorem isScPlusGerm_zero : IsScPlusGerm (E := E) (F := F) C U (fun _ => (0 : F 1)) := by
  refine ⟨ScNbhdGerm.ofSet relOpen_U.relOpen zero_mem_U, fun _ hx => hx, ?_⟩
  exact IsScSmooth.isScSmoothGerm isPartialQuadrant_C.isQuadrantLike relOpen_U.relOpen zero_mem_U
    ((ScOperator.zeroOp E F.shift).isScSmooth relOpen_U.isScDomain)

theorem isConjugateToBasicGerm_g_sub :
    IsConjugateToBasicGerm (E := E) (F := F) U (fun u => g u - F.toBase 1 (0 : F 1)) :=
  isConjugateToBasicGerm_g.congr fun u _ => by rw [map_zero, sub_zero]

/-! ### Good position (2021 Definition 3.6.6, in the chart) -/

lemma ker_Lg_eq_range_rOp :
    LinearMap.ker (Lg : E 0 →ₗ[ℝ] F 0) =
      LinearMap.range ((rOp 0 : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0) := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hx
    have h1 : x.1.1 = 0 := congrArg Prod.fst hx
    have h2 : x.2 = 0 := congrArg Prod.snd hx
    exact ⟨x, Prod.ext (Prod.ext h1.symm rfl) h2.symm⟩
  · rintro ⟨u, rfl⟩; rfl

/-- **The germ is in good position in the chart**: `Tf̃(0) : T₀O → K₀ = 0` is onto and its kernel
`T₀O` (the `t`-axis) is in good position to `T₀O ∩ C = T₀O` in `T₀O`. -/
theorem isGoodPositionAtGerm_g :
    IsGoodPositionAtGerm relOpen_U isStrongBundleRetraction_R zero_mem_U
      (scDeriv U g (0 : E 1)) := by
  rw [scDeriv_g]
  refine ⟨fun y hy => ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := hy
    exact ⟨0, Submodule.zero_mem _, by rw [map_zero]; exact (ρCLM_zero z).symm⟩
  · rw [scDeriv_r]
    have hsub : ∀ x : LinearMap.ker (Lg : E 0 →ₗ[ℝ] F 0), (x : E 0) ∈ C := fun x => by
      have h1 : (x : E 0).1.1 = 0 := congrArg Prod.fst (LinearMap.mem_ker.1 x.2)
      exact ⟨h1.ge, mem_univ _⟩
    refine ⟨ker_Lg_eq_range_rOp.le, ⟨0, ?_⟩, ⊥, bot_le, inf_bot_eq _, ?_, 1, one_pos,
      fun x _ p hp _ => ?_⟩
    · have : (Subtype.val ⁻¹' C : Set (LinearMap.ker (Lg : E 0 →ₗ[ℝ] F 0))) = univ :=
        eq_univ_of_forall hsub
      rw [this, interior_univ]; exact mem_univ _
    · rw [sup_bot_eq, ker_Lg_eq_range_rOp]
    · rw [(Submodule.mem_bot ℝ).1 hp, add_zero]

theorem surjective_scDeriv_g : Surjective (scDeriv U g (0 : E 1)) := by
  rw [scDeriv_g]
  intro y
  exact ⟨((y.1, 0), y.2), rfl⟩

/-! ### The solution set is not a retract of a neighbourhood of `0` in `O` -/

/-- The curve `s ↦ ((0, s), 0)` on level `1`. -/
def curveL : ℝ →L[ℝ] E 1 :=
  ((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)).prod (0 : ℝ →L[ℝ] X 1)

lemma toBase_curveL (s : ℝ) : E.toBase 1 (curveL s) = (((0, s), 0) : E 0) := by
  rw [E_toBase_one]; exact Prod.ext rfl (map_zero _)

/-- A function on `ℝ` which is the identity on `(-δ, 0]` and non-positive on `[0, δ)` is not
differentiable at `0`. -/
lemma not_hasDerivAt_of_halfLine {h : ℝ → ℝ} {d δ : ℝ} (hδ : 0 < δ)
    (hneg : ∀ s, -δ < s → s ≤ 0 → h s = s) (hpos : ∀ s, 0 ≤ s → s < δ → h s ≤ 0) :
    ¬ HasDerivAt h d 0 := by
  intro hd
  have hlo := (hasDerivAt_iff_isLittleO.1 hd).def (show (0 : ℝ) < 1 / 4 by norm_num)
  obtain ⟨δ', hδ', hb⟩ := Metric.eventually_nhds_iff.1 hlo
  have h0 : h 0 = 0 := hneg 0 (by linarith) le_rfl
  set η := min δ δ' / 2 with hη
  have hη0 : 0 < η := by rw [hη]; exact half_pos (lt_min hδ hδ')
  have hη1 : η < δ := by rw [hη]; linarith [min_le_left δ δ']
  have hη2 : η < δ' := by rw [hη]; linarith [min_le_right δ δ']
  have e1 := hb (y := -η) (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hη0]; exact hη2)
  have e2 := hb (y := η) (by rw [Real.dist_eq, sub_zero, abs_of_pos hη0]; exact hη2)
  rw [h0, hneg (-η) (by linarith) (by linarith)] at e1
  simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, abs_neg, abs_of_pos hη0] at e1
  rw [abs_le] at e1
  rw [h0] at e2
  simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, abs_of_pos hη0] at e2
  rw [abs_le] at e2
  have h3 := hpos η hη0.le hη1
  nlinarith [e1.1, e1.2, e2.1, e2.2]

/-- **The solution set `S` is not a retract of a neighbourhood of `0` in `O`**: there are no open
`W ∋ 0` and map `ϱ` with `ϱ ∘ r` sc¹ on `U ∩ r⁻¹(W)` (i.e. `ϱ` sc¹ on the retract `O ∩ W`),
`ϱ(O ∩ W) ⊆ S` and `ϱ = id` on `S ∩ W`.  In the coordinate `t` of `O ≅ ℝ`, `ϱ` would be a
differentiable map which is the identity on `(-δ, 0]` and non-positive on `[0, δ)`. -/
theorem not_exists_retraction :
    ¬ ∃ (W : Set (E 0)) (ϱ : E 0 → E 0), IsOpen W ∧ (0 : E 0) ∈ W ∧
      IsSc1 (U ∩ r R ⁻¹' W) (ϱ ∘ r R) ∧ (∀ x ∈ r R '' U ∩ W, ϱ x ∈ S) ∧
      ∀ x ∈ S ∩ W, ϱ x = x := by
  rintro ⟨W, ϱ, hW, h0W, hsc, hmaps, hfix⟩
  have hz : (0 : E 1) ∈ E.lvlSet (U ∩ r R ⁻¹' W) 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact ⟨zero_mem_U, h0W⟩
  have hD := hsc.isSc1With_scDeriv.hasFDerivWithinAt 0 hz
  have hcont : Continuous fun s : ℝ => (((0, s), 0) : E 0) :=
    (continuous_const.prodMk continuous_id).prodMk continuous_const
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), (((0, s), 0) : E 0) ∈ W ∧ s < 1 :=
    ((hcont.tendsto 0).eventually (hW.mem_nhds h0W)).and (eventually_lt_nhds zero_lt_one)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hmem : ∀ s, dist s 0 < δ → curveL s ∈ E.lvlSet (U ∩ r R ⁻¹' W) 1 := fun s hs => by
    rw [ScBanach.mem_lvlSet, toBase_curveL]
    exact ⟨⟨le_rfl, (hball hs).2⟩, (hball hs).1⟩
  have hnhds : curveL ⁻¹' E.lvlSet (U ∩ r R ⁻¹' W) 1 ∈ 𝓝 (0 : ℝ) :=
    Metric.mem_nhds_iff.2 ⟨δ, hδ, fun s hs => hmem s hs⟩
  have hD' : HasFDerivWithinAt ((ϱ ∘ r R) ∘ E.toBase 1)
      ((scDeriv (U ∩ r R ⁻¹' W) (ϱ ∘ r R) 0).comp (E.toBase 1))
      (E.lvlSet (U ∩ r R ⁻¹' W) 1) (curveL 0) := by rw [map_zero]; exact hD
  have h1 := hD'.comp 0 curveL.hasFDerivAt.hasFDerivWithinAt (mapsTo_preimage _ _)
  have h2 := ((tOp 0).hasFDerivAt.comp_hasFDerivWithinAt 0 h1).hasFDerivAt hnhds
  have hfun : (tOp 0 ∘ ((ϱ ∘ r R) ∘ E.toBase 1) ∘ curveL) = fun s : ℝ => (ϱ ((0, s), 0)).1.2 := by
    funext s
    change (ϱ (r R (E.toBase 1 (curveL s)))).1.2 = _
    rw [toBase_curveL]; rfl
  rw [hfun] at h2
  refine not_hasDerivAt_of_halfLine (h := fun s : ℝ => (ϱ ((0, s), 0)).1.2) hδ (fun s hs hs0 => ?_)
    (fun s hs0 hs => ?_) h2.hasDerivAt
  · have hd : dist s 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_nonpos hs0]; linarith
    change (ϱ ((0, s), 0)).1.2 = s
    rw [hfix ((0, s), 0) ⟨⟨rfl, hs0, rfl⟩, (hball hd).1⟩]
  · have hd : dist s 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hs0]; exact hs
    exact (hmaps ((0, s), 0) ⟨mem_O.2 ⟨rfl, (hball hd).2, rfl⟩, (hball hd).1⟩).2.1

/-! ### The same on the M-polyfold `O` -/

/-- The base retraction `r` as an sc-smooth retraction. -/
def baseRetr : ScRetraction E C := isStrongBundleRetraction_R.baseRetraction relOpen_U

/-- The local model `(O, C, E)`. -/
def modelO : LocalModel := ⟨E, C, r R '' U, ⟨baseRetr, rfl⟩⟩

/-- **The M-polyfold `O = r(U) ≅ ℝ`**, with its one chart (the untamed one). -/
def polyO : MPolyfold (r R '' U) := modelO.toMPolyfold ⟨0, zero_mem_O⟩

/-- The restriction of `r` to `U ∩ r⁻¹(W)`, `W` open. -/
def baseRetrOn {W : Set (E 0)} (hW : IsOpen W) : ScRetraction E C where
  U := U ∩ r R ⁻¹' W
  toFun := r R
  relOpen := by
    obtain ⟨Oo, hOo, hUO⟩ := relOpen_U.relOpen
    refine ⟨isPartialQuadrant_C, Oo ∩ r R ⁻¹' W, hOo.inter (hW.preimage (rOp 0).continuous), ?_⟩
    rw [hUO]; ext x; simp only [mem_inter_iff]; tauto
  mapsTo u hu := ⟨baseRetr.mapsTo hu.1, by
    have he : r R (r R u) = r R u := baseRetr.idem u hu.1
    change r R (r R u) ∈ W
    rw [he]; exact hu.2⟩
  isScSmooth := by
    obtain ⟨Oo, hOo, hUO⟩ := relOpen_U.relOpen
    have hrel : IsRelOpenInQuadrant E C (U ∩ r R ⁻¹' W) :=
      ⟨isPartialQuadrant_C, Oo ∩ r R ⁻¹' W, hOo.inter (hW.preimage (rOp 0).continuous), by
        rw [hUO]; ext x; simp only [mem_inter_iff]; tauto⟩
    exact baseRetr.isScSmooth.of_subset hrel.isScDomain inter_subset_left
  idem u hu := baseRetr.idem u hu.1

lemma baseRetrOn_retract {W : Set (E 0)} (hW : IsOpen W) :
    (baseRetrOn hW).retract = r R '' U ∩ W := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu.1, rfl⟩, hu.2⟩
  · rintro ⟨⟨u, hu, rfl⟩, hxW⟩
    have he : r R (r R u) = r R u := baseRetr.idem u hu
    exact ⟨r R u, ⟨baseRetr.mapsTo hu, by change r R (r R u) ∈ W; rw [he]; exact hxW⟩, he⟩

/-- **The solution set is not a sub-M-polyfold of `O`** (2021 Definition 2.3.18): conclusion (2)
of 2021 Theorem 3.6.8 does not hold for the M-polyfold `O`, the section `g|_O` and the zero
`0`. -/
theorem not_isSubMPolyfold_solutionSet :
    ¬ polyO.IsSubMPolyfold {x : r R '' U | (x : E 0) ∈ S} := by
  intro h
  obtain ⟨V, hVo, h0V, ϱ, hmaps, hsm, hidem, himg⟩ :=
    h ⟨0, zero_mem_O⟩ (show ((0 : E 0)) ∈ S from ⟨rfl, le_rfl, rfl⟩)
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hVo
  let φ : MChart (r R '' U) := modelO.selfChart ⟨0, zero_mem_O⟩
  have hφ : polyO.IsChart φ := polyO.isChart_of_mem (mem_singleton _)
  have hsymm : ∀ z (hz : z ∈ r R '' U), φ.symm z = ⟨z, hz⟩ := fun z hz =>
    Subtype.ext (φ.toPartialEquiv.right_inv (show z ∈ φ.toPartialEquiv.target from hz))
  have himgφ : φ '' (Subtype.val ⁻¹' W) = r R '' U ∩ W := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
    · rintro ⟨hz, hzW⟩; exact ⟨⟨z, hz⟩, hzW, rfl⟩
  have hret := hsm.smooth φ φ hφ hφ (Subtype.val ⁻¹' W) hVo
    (fun y hy => ⟨hy, mem_univ _⟩) (fun y _ => mem_univ _)
  have hsc := hret.comp_isScSmooth (baseRetrOn hW) ((baseRetrOn_retract hW).trans himgφ.symm)
  refine not_exists_retraction ⟨W, fun z => ((ϱ (φ.symm z) : r R '' U) : E 0), hW, h0V,
    hsc.isSc1, ?_, ?_⟩
  · rintro x ⟨hxO, hxW⟩
    have hx : (⟨x, hxO⟩ : r R '' U) ∈ Subtype.val ⁻¹' W := hxW
    have h1 : ϱ ⟨x, hxO⟩ ∈ ϱ '' (Subtype.val ⁻¹' W) := ⟨_, hx, rfl⟩
    rw [himg] at h1
    change ((ϱ (φ.symm x) : r R '' U) : E 0) ∈ S
    rw [hsymm x hxO]; exact h1.1
  · rintro x ⟨hxS, hxW⟩
    have hxO : x ∈ r R '' U := mem_O.2 ⟨hxS.1, lt_of_le_of_lt hxS.2.1 zero_lt_one, hxS.2.2⟩
    have h1 : (⟨x, hxO⟩ : r R '' U) ∈ {x : r R '' U | (x : E 0) ∈ S} ∩ Subtype.val ⁻¹' W :=
      ⟨hxS, hxW⟩
    rw [← himg] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    change ((ϱ (φ.symm x) : r R '' U) : E 0) = x
    rw [hsymm x hxO, ← hyx, hidem y hy, hyx]

/-! ### The base retraction is not tame -/

lemma U_subset_C : U ⊆ C := fun _ hp => ⟨hp.1, mem_univ _⟩

lemma zero_not_mem_interior_C : (0 : E 0) ∉ interior C := by
  intro h
  have hcont : Continuous fun s : ℝ => (((s, 0), 0) : E 0) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hn : (fun s : ℝ => (((s, 0), 0) : E 0)) ⁻¹' C ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.1 h)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hn
  have hm : (-(ε / 2) : ℝ) ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have : (0 : ℝ) ≤ -(ε / 2) := (hball hm).1
  linarith

/-- **The base retraction `r((a, t), w) = ((0, t), 0)` is not tame**: 2021 Definition 2.5.2 (1)
does not hold for it, as `((1, 0), 0)` is an interior point of `C` (`d_C = 0`) and
`r((1, 0), 0) = 0` is not. -/
theorem not_isTame_baseRetr : ¬ baseRetr.IsTame := by
  intro h
  obtain ⟨n, W, T, hT⟩ := isPartialQuadrant_C
  have hx : (((1, 0), 0) : E 0) ∈ U := ⟨zero_le_one, zero_lt_one⟩
  have hd := (h n W T hT).degIndex_apply _ hx
  have hint : (((1, 0), 0) : E 0) ∈ interior C :=
    mem_interior.2 ⟨{p : E 0 | 0 < p.1.1}, fun p (hp : 0 < p.1.1) => (⟨hp.le, mem_univ _⟩ : p ∈ C),
      isOpen_lt continuous_const (continuous_fst.comp continuous_fst),
      show (0 : ℝ) < 1 from zero_lt_one⟩
  have h1 := (mem_interior_iff_degIndex_eq_zero isPartialQuadrant_C (interior_subset hint)).1 hint
  rw [h1] at hd
  exact zero_not_mem_interior_C
    ((mem_interior_iff_degIndex_eq_zero isPartialQuadrant_C (U_subset_C zero_mem_U)).2 hd)

/-! ### `O` is a tame M-polyfold without boundary: the chart `t` -/

/-- The domain `{t < 1}` of `ℝ¹`. -/
def Ut : Set ((rnSc 1) 0) := {p | p 0 < 1}

lemma relOpen_Ut : IsRelOpenInQuadrant (rnSc 1) univ Ut :=
  ⟨(rn_relOpen_univ 1).isPartialQuadrant, Ut,
    isOpen_lt (continuous_apply 0) continuous_const, (inter_univ _).symm⟩

/-- The local model `({t < 1}, ℝ¹, ℝ¹)`. -/
def modelT : LocalModel := LocalModel.ofRelOpen relOpen_Ut

/-- `t ↦ ((0, t), 0)` as an sc-operator `ℝ¹ → E`. -/
def sigmaOp : ScOperator (rnSc 1) E where
  lvl m := ((0 : (Fin 1 → ℝ) →L[ℝ] ℝ).prod
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).prod
    (0 : (Fin 1 → ℝ) →L[ℝ] X m)
  incl_comm m _ := Prod.ext rfl (map_zero (X.incl m))

lemma sigmaOp_apply (p : Fin 1 → ℝ) : sigmaOp 0 p = (((0, p 0), 0) : E 0) := rfl

/-- `((a, t), w) ↦ t` as an sc-operator `E → ℝ¹`. -/
def tauOp : ScOperator E (rnSc 1) where
  lvl m := ContinuousLinearMap.pi fun _ => tOp m
  incl_comm _ _ := rfl

lemma tauOp_apply (p : E 0) : tauOp 0 p = fun _ => p.1.2 := rfl

open scoped Classical in
/-- The chart `t : O → {t < 1} ⊆ ℝ¹`. -/
def chartT : MChart (r R '' U) where
  model := modelT
  toPartialEquiv :=
    { toFun := fun x => tauOp 0 (x : E 0)
      invFun := fun p => if h : p 0 < 1 then ⟨sigmaOp 0 p, mem_O.2 ⟨rfl, h, rfl⟩⟩
        else ⟨0, zero_mem_O⟩
      source := univ
      target := Ut
      map_source' := fun x _ => (mem_O.1 x.2).2.1
      map_target' := fun _ _ => mem_univ _
      left_inv' := fun x _ => by
        obtain ⟨h1, h2, h3⟩ := mem_O.1 x.2
        rw [dif_pos (show (tauOp 0 (x : E 0)) 0 < 1 from h2)]
        exact Subtype.ext (Prod.ext (Prod.ext h1.symm rfl) h3.symm)
      right_inv' := fun p hp => by
        rw [dif_pos (show p 0 < 1 from hp)]
        funext i
        rw [Subsingleton.elim i 0]; rfl }
  isOpen_source := isOpen_univ
  target_eq := rfl
  continuousOn_toFun := ((tauOp 0).continuous.comp continuous_subtype_val).continuousOn
  continuousOn_invFun := by
    refine continuousOn_iff_continuous_domRestrict.2 ?_
    have : (fun p : Ut => if h : (p : Fin 1 → ℝ) 0 < 1 then
        (⟨sigmaOp 0 (p : Fin 1 → ℝ), mem_O.2 ⟨rfl, h, rfl⟩⟩ : r R '' U) else ⟨0, zero_mem_O⟩) =
        fun p : Ut => ⟨sigmaOp 0 (p : Fin 1 → ℝ), mem_O.2 ⟨rfl, p.2, rfl⟩⟩ :=
      funext fun p => dif_pos p.2
    change Continuous (fun p : Ut => if h : (p : Fin 1 → ℝ) 0 < 1 then
        (⟨sigmaOp 0 (p : Fin 1 → ℝ), mem_O.2 ⟨rfl, h, rfl⟩⟩ : r R '' U) else ⟨0, zero_mem_O⟩)
    rw [this]
    exact ((sigmaOp 0).continuous.comp continuous_subtype_val).subtype_mk _

/-- The chart `t` is compatible with the chart of `polyO`. -/
theorem isChart_chartT : polyO.IsChart chartT := by
  intro ψ hψ
  rw [mem_singleton_iff.1 hψ]
  have hsymmT : ∀ p : Fin 1 → ℝ, p 0 < 1 →
      ((chartT.symm p : r R '' U) : E 0) = sigmaOp 0 p := fun p hp => by
    change ((if h : p 0 < 1 then (⟨sigmaOp 0 p, mem_O.2 ⟨rfl, h, rfl⟩⟩ : r R '' U)
      else ⟨0, zero_mem_O⟩ : r R '' U) : E 0) = _
    rw [dif_pos hp]
  have hsymmS : ∀ z (hz : z ∈ r R '' U),
      (modelO.selfChart ⟨0, zero_mem_O⟩).symm z = ⟨z, hz⟩ := fun z hz =>
    Subtype.ext ((modelO.selfChart ⟨0, zero_mem_O⟩).toPartialEquiv.right_inv
      (show z ∈ (modelO.selfChart ⟨0, zero_mem_O⟩).toPartialEquiv.target from hz))
  constructor
  · refine ⟨?_, fun Rr hRr => ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact ⟨x, ⟨mem_univ _, mem_univ _⟩,
        (chartT.transition_apply _ (mem_univ x)).symm⟩
    · have hUr := Rr.relOpen.isScDomain
      refine (IsScSmooth.comp hUr (isScDomain_univ _) (sigmaOp.isScSmooth (isScDomain_univ _))
        Rr.isScSmooth (mapsTo_univ _ _)).congr hUr fun p hp => ?_
      have hmem : Rr p ∈ Rr.retract := Rr.apply_mem_retract hp
      rw [hRr] at hmem
      obtain ⟨x, -, hx⟩ := hmem
      have hlt : (Rr p) 0 < 1 := by rw [← hx]; exact (mem_O.1 x.2).2.1
      exact (hsymmT (Rr p) hlt).symm
  · refine ⟨?_, fun Rr hRr => ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact ⟨x, ⟨mem_univ _, mem_univ _⟩,
        ((modelO.selfChart ⟨0, zero_mem_O⟩).transition_apply _ (mem_univ x)).symm⟩
    · have hUr := Rr.relOpen.isScDomain
      refine (IsScSmooth.comp hUr (isScDomain_univ _) (tauOp.isScSmooth (isScDomain_univ _))
        Rr.isScSmooth (mapsTo_univ _ _)).congr hUr fun p hp => ?_
      have hmem : Rr p ∈ Rr.retract := Rr.apply_mem_retract hp
      rw [hRr] at hmem
      obtain ⟨x, -, hx⟩ := hmem
      have hO : Rr p ∈ r R '' U := by rw [← hx]; exact x.2
      change tauOp 0 (Rr p) = chartT ((modelO.selfChart ⟨0, zero_mem_O⟩).symm (Rr p))
      rw [hsymmS _ hO]; rfl

/-- **`O` is a tame M-polyfold** (2021 Definition 2.5.7): the chart `t` onto the open subset
`{t < 1}` of `ℝ¹` is a chart of the structure, with a tame (identity) retraction. -/
theorem isTame_polyO : polyO.IsTame :=
  MPolyfold.isTame_of_forall_exists_chart polyO fun x =>
    ⟨chartT, isChart_chartT, mem_univ x,
      ScRetraction.id relOpen_Ut, image_id Ut, ScRetraction.id_isTame relOpen_Ut⟩

/-- **`O` has no boundary**: `d_X(x) = 0` at every point (2021 Definition 2.4.1), seen in the
chart `t`. -/
theorem degIndex_polyO (x : r R '' U) : polyO.degIndex x = 0 := by
  have h := polyO.degIndex_le isChart_chartT (mem_univ x)
  have h0 : MPolyfold.chartDegIndex chartT x = 0 :=
    (mem_interior_iff_degIndex_eq_zero (rn_relOpen_univ 1).isPartialQuadrant (mem_univ _)).1
      (by rw [interior_univ]; exact mem_univ _)
  omega

/-- In the chart of the germ data, every point of `O` lies on the boundary of `C`:
`d_C(φ(x)) ≠ 0`. -/
theorem chartDegIndex_selfChart_ne_zero (x : r R '' U) :
    MPolyfold.chartDegIndex (modelO.selfChart ⟨0, zero_mem_O⟩) x ≠ 0 := by
  intro h
  have hxC : (x : E 0) ∈ C := U_subset_C (baseRetr.retract_subset x.2)
  have hint : (x : E 0) ∈ interior C :=
    (mem_interior_iff_degIndex_eq_zero isPartialQuadrant_C hxC).2 h
  have hcont : Continuous fun s : ℝ => (((s, (x : E 0).1.2), 0) : E 0) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hx0 : (((0, (x : E 0).1.2), 0) : E 0) = x := by
    obtain ⟨h1, -, h3⟩ := mem_O.1 x.2
    exact Prod.ext (Prod.ext h1.symm rfl) h3.symm
  have hn : (fun s : ℝ => (((s, (x : E 0).1.2), 0) : E 0)) ⁻¹' C ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by
      change C ∈ 𝓝 (((0, (x : E 0).1.2), 0) : E 0)
      rw [hx0]; exact mem_interior_iff_mem_nhds.1 hint)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hn
  have hm : (-(ε / 2) : ℝ) ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have : (0 : ℝ) ≤ -(ε / 2) := (hball hm).1
  linarith

/-! ### The statement -/

/-- **2021 Theorem 3.6.8, p. 136, does not hold as we read it for untamed germ data** (the local
statement).  On `E = ℝ² ⊕ X ∋ ((a, t), w)`, `C = [0, ∞) × ℝ × X`, `U = C ∩ {t < 1}`, `F = ℝ ⊕ X`,
with the strong bundle retraction `R(((a, t), w), (x, h)) = (((0, t), 0), (0, π_t h))` (`π_t` the
moving rank-one projection of `Jump.family`, `π_t = 0` for `t ≤ 0`) and
`g((a, t), w) = (a + ν(w)², w + π_t v)`:

* `g` is a 2021 filling (Definitions 3.1.4/3.6.1) of the section `g|_O` of `K = R(U ◁ F) → O`,
  `O = r(U) = {((0, t), 0)} ≅ ℝ`;
* `g(0) = 0`, the sc⁺-germ `s = 0` has `s(0) = g(0)` and `g − s` is conjugated to a basic germ
  (Definition 3.6.3: the germ at `0` is an sc-Fredholm germ with these data);
* the germ is in good position in the chart (Definition 3.6.6) and `Dg(0)` is onto;
* the solution set `{x ∈ O | g(x) = 0}` is the closed half-line `S = {((0, t), 0) | t ≤ 0}`;
* `S` is not a retract of a neighbourhood of `0` in `O` for any sc¹ retraction: it is not a
  sub-M-polyfold of `O ≅ ℝ` at `0`, so conclusion (2) of Theorem 3.6.8 does not hold here.

The base retraction `r((a, t), w) = ((0, t), 0)` is not tame; with tame germ data the theorem is
`theorem_3_6_8'`. -/
theorem theorem_3_6_8_untamed_local :
    IsFilling2021 relOpen_U isStrongBundleRetraction_R zero_mem_U g g ∧
    (0 : E 0) ∈ r R '' U ∧ g 0 = 0 ∧
    (∀ x ∈ r R '' U, (x, g x) ∈ R '' (U ×ˢ (univ : Set (F 0)))) ∧
    IsScPlusGerm (E := E) (F := F) C U (fun _ => (0 : F 1)) ∧ F.toBase 1 (0 : F 1) = g 0 ∧
    IsConjugateToBasicGerm (E := E) (F := F) U (fun u => g u - F.toBase 1 (0 : F 1)) ∧
    IsGoodPositionAtGerm relOpen_U isStrongBundleRetraction_R zero_mem_U
      (scDeriv U g (0 : E 1)) ∧
    Surjective (scDeriv U g (0 : E 1)) ∧
    {x | x ∈ r R '' U ∧ g x = 0} = S ∧
    ¬ ∃ (W : Set (E 0)) (ϱ : E 0 → E 0), IsOpen W ∧ (0 : E 0) ∈ W ∧
      IsSc1 (U ∩ r R ⁻¹' W) (ϱ ∘ r R) ∧ (∀ x ∈ r R '' U ∩ W, ϱ x ∈ S) ∧
      ∀ x ∈ S ∩ W, ϱ x = x :=
  ⟨isFilling2021_g, zero_mem_O, g_zero, g_section, isScPlusGerm_zero,
    by rw [map_zero, g_zero], isConjugateToBasicGerm_g_sub, isGoodPositionAtGerm_g,
    surjective_scDeriv_g, solutionSet_eq, not_exists_retraction⟩

/-- **The same on the M-polyfold `O`** (2021 Theorem 3.6.8, p. 136, conclusion (2), with untamed
germ data).  `O = r(U)` with its one chart is a tame M-polyfold without boundary (`d_X = 0`
everywhere; in the chart of the germ data every point has `d_C ≠ 0` and the retraction is not
tame), and the solution set of the section `g|_O` — whose germ at `0` has the data of
Definition 3.6.3 and is in good position, `theorem_3_6_8_untamed_local` — is not a
sub-M-polyfold. -/
theorem theorem_3_6_8_untamed_polyfold :
    polyO.IsTame ∧ (∀ x, polyO.degIndex x = 0) ∧
    (∀ x, MPolyfold.chartDegIndex (modelO.selfChart ⟨0, zero_mem_O⟩) x ≠ 0) ∧
    ¬ baseRetr.IsTame ∧ ¬ polyO.IsSubMPolyfold {x : r R '' U | (x : E 0) ∈ S} :=
  ⟨isTame_polyO, degIndex_polyO, chartDegIndex_selfChart_ne_zero, not_isTame_baseRetr,
    not_isSubMPolyfold_solutionSet⟩

end UntamedCorner
end Polyfold
