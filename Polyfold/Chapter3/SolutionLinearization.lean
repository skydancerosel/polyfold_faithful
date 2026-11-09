import Polyfold.Chapter3.LocalSolvability
import Polyfold.Chapter3.FredholmGermLinearization
import Polyfold.Chapter1.FredholmPerturbation

/-!
# The linearization at nearby solutions (Corollary 3.5.3 (preprint 3.41))

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I*, §3.5, **Corollary 3.5.3 (preprint 3.41)**: for
`f = h + s : U → ℝᴺ ⊕ W` with `h` a basic germ and `s` an sc⁺-germ, `s(0) = 0`, and `Df(0)`
surjective, the zeros `x` of `f` close to `0` on level `0` lie on level `1`, and `Df(x) : E₀ → F₀`
is a surjective Fredholm operator of index `n − N`.

The proof follows the text: `Df(x) − Df(0)` is the sum of an operator of norm `≤ ε` (the fibre
derivative `D₂B(x)`, Lemma 3.1.9 (preprint 3.9) on level `0` for `x` small on level `1`) and a compact operator
(the finite-rank parts through `ℝⁿ` and `ℝᴺ`, and `ι ∘ Ds(x)` through the compact inclusion
`W₁ → W₀`), so `Df(x)` is Fredholm of index `n − N` by the stability of the index; the kernel of
`Df(x)` meets a closed complement `N` of `ker Df(0)` trivially for solutions `x` near `0`, by the
compactness argument of the text (sequences, the boundedness of `Ds(x)h` in `W₁`), and then
`dim ker Df(x) ≤ dim ker Df(0) = n − N = ind Df(x)` forces `coker Df(x) = 0`.

## Main results

* `Polyfold.isFredholm_add_of_norm_lt`: a perturbation of a Fredholm operator by an operator of
  small norm is Fredholm (with the same index, `Polyfold.fredholmIndex_add_of_norm_lt`).
* `Polyfold.HasFiniteIndex.surjective_of_finrank_ker_le`: an operator of finite index with
  `dim ker ≤ ind` is surjective.
* `Polyfold.IsSc0ContractionGerm.exists_norm_deriv_snd_le` (**Lemma 3.1.9 (preprint 3.9) on level `0`**, with an
  arbitrary `ε`): `|D₂B(x)ζ|₀ ≤ ε|ζ|₀` for `x ∈ U₁` small on level `1` (the form used for
  Corollary 3.5.3 (preprint 3.41)).
* `Polyfold.IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le` (**Lemma 3.1.9 (preprint 3.9) as stated**: on
  level `m`, `|D₂B(x)ζ|_m ≤ ε|ζ|_m` for `x ∈ U_{m+1}` small on level `m`) and
  `IsSc0ContractionGerm.exists_norm_deriv_snd_le_base` (level `0`, `x ∈ U₁` small on level `0`,
  without the quadrant hypothesis); round-trip item V3.11.
* `Polyfold.StabilityData.corollary_3_5_3` (**Corollary 3.5.3 (preprint 3.41)**).

## Remark on Lemma 3.1.9 (preprint 3.9)

Smallness of `x` on level `m + 1` is not needed for the level-`m` estimate (an earlier version of
this file said that it was, for `m = 0`).  The difference quotients are taken along
`t ↦ x + t(0, ζ')` with `ζ' ∈ W_{m+1}`; this curve stays in `U_{m+1}` for small `t ≥ 0` because
`U_{m+1}` is relatively open in `C̃ ⊕ W_{m+1}`, however large `x` is on level `m + 1`.  The
contraction estimate of Definition 3.3.1 (preprint 3.28) is applied on level `m`, at the points
`(a, ιw + tιζ')`, which are small on level `m` when `x` is.
-/

open Set Filter Topology Function Asymptotics Metric ContinuousLinearMap
open scoped LinearMap.FiniteRangeSetoid

noncomputable section

namespace Polyfold

/-! ### Fredholm operators: small perturbations -/

section Banach

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

open LinearMap.FiniteRangeSetoid in
/-- **A small perturbation of a Fredholm operator is Fredholm.**  If `v` is a quasi-inverse of `u`
and `‖v‖ ‖s‖ < 1`, then `u + s` has the quasi-inverse `(1 + v s)⁻¹ v` (Neumann series), so it is
Fredholm. -/
theorem isFredholm_add_of_norm_lt {u : E →L[ℝ] F} {v : F →L[ℝ] E} (hvu : v.IsQuasiInverse u)
    {s : E →L[ℝ] F} (hs : ‖v‖ * ‖s‖ < 1) : IsFredholm (u + s) := by
  have hvs : ‖v ∘L s‖ < 1 := lt_of_le_of_lt (opNorm_comp_le v s) hs
  have hsv : ‖s ∘L v‖ < 1 := lt_of_le_of_lt (opNorm_comp_le s v) (by rwa [mul_comm])
  -- the units `a = 1 + v s` and `a' = 1 + s v`
  have ha : IsUnit (1 - (-(v ∘L s)) : E →L[ℝ] E) := isUnit_one_sub_of_norm_lt_one (by rwa [norm_neg])
  have ha' : IsUnit (1 - (-(s ∘L v)) : F →L[ℝ] F) := isUnit_one_sub_of_norm_lt_one (by rwa [norm_neg])
  rw [sub_neg_eq_add] at ha ha'
  obtain ⟨a, ha⟩ := ha
  obtain ⟨a', ha'⟩ := ha'
  -- finite-rank parts of `v u − 1` and `u v − 1`
  have h₁ : ((v ∘L u : E →L[ℝ] E) : E →ₗ[ℝ] E) - LinearMap.id |>.HasFiniteRange :=
    equiv_iff_hasFiniteRange.1 hvu.1
  have h₂ : ((u ∘L v : F →L[ℝ] F) : F →ₗ[ℝ] F) - LinearMap.id |>.HasFiniteRange :=
    equiv_iff_hasFiniteRange.1 hvu.2
  -- the left quasi-inverse `w = a⁻¹ v` and the right quasi-inverse `w' = v a'⁻¹`
  set w : F →L[ℝ] E := (↑a⁻¹ : E →L[ℝ] E) ∘L v with hw
  set w' : F →L[ℝ] E := v ∘L (↑a'⁻¹ : F →L[ℝ] F) with hw'
  have hleft : ((w ∘L (u + s) : E →L[ℝ] E) : E →ₗ[ℝ] E) - LinearMap.id =
      ((↑a⁻¹ : E →L[ℝ] E) : E →ₗ[ℝ] E) ∘ₗ (((v ∘L u : E →L[ℝ] E) : E →ₗ[ℝ] E) - LinearMap.id) := by
    have hinv : (↑a⁻¹ : E →L[ℝ] E) ∘L (↑a : E →L[ℝ] E) = 1 := a.inv_mul
    rw [ha] at hinv
    ext x
    have hx := DFunLike.congr_fun hinv x
    simp only [ContinuousLinearMap.comp_apply, add_apply, map_add] at hx
    have hx' : (↑a⁻¹ : E →L[ℝ] E) (v (s x)) = x - (↑a⁻¹ : E →L[ℝ] E) x :=
      eq_sub_of_add_eq (by rw [add_comm]; exact hx)
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, coe_coe, LinearMap.id_apply, hw,
      ContinuousLinearMap.comp_apply, add_apply, map_add, map_sub, hx']
    abel
  have hright : (((u + s) ∘L w' : F →L[ℝ] F) : F →ₗ[ℝ] F) - LinearMap.id =
      (((u ∘L v : F →L[ℝ] F) : F →ₗ[ℝ] F) - LinearMap.id) ∘ₗ ((↑a'⁻¹ : F →L[ℝ] F) : F →ₗ[ℝ] F) := by
    have hinv : (↑a' : F →L[ℝ] F) ∘L (↑a'⁻¹ : F →L[ℝ] F) = 1 := a'.mul_inv
    rw [ha'] at hinv
    ext y
    have hy := DFunLike.congr_fun hinv y
    simp only [ContinuousLinearMap.comp_apply, add_apply] at hy
    have hy' : s (v ((↑a'⁻¹ : F →L[ℝ] F) y)) = y - (↑a'⁻¹ : F →L[ℝ] F) y :=
      eq_sub_of_add_eq (by rw [add_comm]; exact hy)
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, coe_coe, LinearMap.id_apply, hw',
      ContinuousLinearMap.comp_apply, add_apply, hy']
    abel
  have hL : ((w ∘L (u + s) : E →L[ℝ] E) : E →ₗ[ℝ] E) ≈ LinearMap.id := by
    rw [equiv_iff_hasFiniteRange, hleft]; exact h₁.comp_left _
  have hR : (((u + s) ∘L w' : F →L[ℝ] F) : F →ₗ[ℝ] F) ≈ LinearMap.id := by
    rw [equiv_iff_hasFiniteRange, hright]; exact h₂.comp_right _
  -- `w ≈ w'`, hence `w` is a two-sided quasi-inverse
  have hww' : (w : F →ₗ[ℝ] E) ≈ (w' : F →ₗ[ℝ] E) := by
    rw [equiv_iff_hasFiniteRange]
    have e : (w : F →ₗ[ℝ] E) - (w' : F →ₗ[ℝ] E) =
        (((w ∘L (u + s) : E →L[ℝ] E) : E →ₗ[ℝ] E) - LinearMap.id) ∘ₗ (w' : F →ₗ[ℝ] E) -
          (w : F →ₗ[ℝ] E) ∘ₗ ((((u + s) ∘L w' : F →L[ℝ] F) : F →ₗ[ℝ] F) - LinearMap.id) := by
      ext y
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, coe_coe, LinearMap.id_apply,
        ContinuousLinearMap.comp_apply, map_sub]
      abel
    rw [e]
    have hfin₁ := (equiv_iff_hasFiniteRange.1 hL).comp_right (w' : F →ₗ[ℝ] E)
    have hfin₂ := (equiv_iff_hasFiniteRange.1 hR).comp_left (w : F →ₗ[ℝ] E)
    rw [LinearMap.HasFiniteRange, Submodule.fg_iff_finiteDimensional] at hfin₁ hfin₂ ⊢
    refine Submodule.finiteDimensional_of_le
      (S₂ := LinearMap.range ((((w ∘L (u + s) : E →L[ℝ] E) : E →ₗ[ℝ] E) - LinearMap.id) ∘ₗ
          (w' : F →ₗ[ℝ] E)) ⊔
        LinearMap.range ((w : F →ₗ[ℝ] E) ∘ₗ
          ((((u + s) ∘L w' : F →L[ℝ] F) : F →ₗ[ℝ] F) - LinearMap.id))) ?_
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.sub_apply]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (LinearMap.mem_range_self _ y))
      (Submodule.mem_sup_right (LinearMap.mem_range_self _ y))
  have hR' : (((u + s) ∘L w : F →L[ℝ] F) : F →ₗ[ℝ] F) ≈ LinearMap.id := by
    have e1 : (((u + s) ∘L w : F →L[ℝ] F) : F →ₗ[ℝ] F) =
        ((u + s : E →L[ℝ] F) : E →ₗ[ℝ] F) ∘ₗ (w : F →ₗ[ℝ] E) := rfl
    have e2 : (((u + s) ∘L w' : F →L[ℝ] F) : F →ₗ[ℝ] F) =
        ((u + s : E →L[ℝ] F) : E →ₗ[ℝ] F) ∘ₗ (w' : F →ₗ[ℝ] E) := rfl
    rw [e1]
    rw [e2] at hR
    exact Setoid.trans (equiv_comp_left (u' := ((u + s : E →L[ℝ] F) : E →ₗ[ℝ] F)) hww') hR
  exact IsFredholm.of_isQuasiInverse (v := w) ⟨hL, hR'⟩

/-- **Stability of Fredholm operators and their index under small perturbations**: if `u` is
Fredholm and `‖s‖` is small (in terms of a quasi-inverse `v` of `u`), then `u + s` is Fredholm with
`ind(u + s) = ind(u)`. -/
theorem isFredholm_fredholmIndex_add_of_norm_lt {u : E →L[ℝ] F} {v : F →L[ℝ] E}
    (hvu : v.IsQuasiInverse u) {s : E →L[ℝ] F} (hs : ‖v‖ * ‖s‖ < 1) :
    IsFredholm (u + s) ∧ fredholmIndex (u + s) = fredholmIndex u :=
  ⟨isFredholm_add_of_norm_lt hvu hs, (fredholmIndex_add_of_norm_lt hvu hs).2⟩

end Banach

/-- An operator of finite index whose kernel has dimension at most the index is surjective
(its cokernel has dimension `dim ker − ind ≤ 0`). -/
theorem HasFiniteIndex.surjective_of_finrank_ker_le {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {u : E →ₗ[ℝ] F} (hu : HasFiniteIndex u)
    (h : (Module.finrank ℝ (LinearMap.ker u) : ℤ) ≤ linIndex u) : Surjective u := by
  have := hu.finite_coker
  have hcoker : Module.finrank ℝ (F ⧸ LinearMap.range u) = 0 := by
    unfold linIndex at h; omega
  rw [Module.finrank_zero_iff] at hcoker
  intro y
  have : (Submodule.Quotient.mk y : F ⧸ LinearMap.range u) = 0 := Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero _).1 this

/-! ### Lemma 3.1.9 (preprint 3.9) on level `0` with an arbitrary constant -/

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}

/-- **Lemma 3.1.9 (preprint 3.9) on level `0`** ("`‖D₂B(a, w)‖ ≤ ε` for every `ε > 0` if `(a, w)` is sufficiently
small"): for every `ε > 0` there is `r > 0` such that `|D₂B(x)ζ|₀ ≤ ε|ζ|₀` for all `x ∈ U₁` with
`|x|₁ < r` and all `ζ ∈ W₀`.  Proof: for `ζ ∈ W₁` the difference quotient of `t ↦ B(a, w + tζ)`
is bounded by `ε|ζ|₀` through the contraction estimate of Definition 3.3.1 (preprint 3.28) on level `0`, and
`B : U₁ → W₀` is differentiable at `x` within `U₁`; then density of `W₁` in `W₀`.  The curve
`t ↦ x + t(0, ζ)` has to stay in `U₁`, where `B` is differentiable, but smallness on level `1` is
not needed for that (`U₁` is relatively open): the same estimate holds for `x ∈ U₁` small on level
`0` (`exists_norm_deriv_snd_le_base`), and on every level `m` (`exists_norm_levelDeriv_snd_le`).
This level-`1` form is the one used for Corollary 3.5.3 (preprint 3.41). -/
theorem IsSc0ContractionGerm.exists_norm_deriv_snd_le
    {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {B : P × W 0 → W 0}
    (hB : IsSc0ContractionGerm Ct G B)
    {DB : (ScBanach.paramProd P W) 1 → (ScBanach.paramProd P W) 0 →L[ℝ] W 0}
    (hD : IsSc1GermWith (F := W) G B DB) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ G.U 1, ‖x‖ < r → ∀ ζ : W 0, ‖DB x ((0 : P), ζ)‖ ≤ ε * ‖ζ‖ := by
  obtain ⟨r₀, hr₀, hcontr⟩ := hB.contraction ε hε 0
  set c : ℝ := ‖W.toBase 1‖ + 1 with hc
  have hcpos : 0 < c := by positivity
  refine ⟨min r₀ (r₀ / c), by positivity, ?_⟩
  rintro ⟨a, w⟩ hx hxr ζ
  have ha : ‖a‖ < r₀ := (norm_fst_le ((a, w) : (ScBanach.paramProd P W) 1)).trans_lt (hxr.trans_le (min_le_left _ _))
  have hw1 : ‖w‖ < r₀ / c := (norm_snd_le ((a, w) : (ScBanach.paramProd P W) 1)).trans_lt (hxr.trans_le (min_le_right _ _))
  set w₀ : W 0 := W.toBase 1 w with hw₀
  have hw0 : ‖w₀‖ < r₀ := by
    calc ‖w₀‖ ≤ ‖W.toBase 1‖ * ‖w‖ := (W.toBase 1).le_opNorm w
      _ ≤ c * ‖w‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < c * (r₀ / c) := mul_lt_mul_of_pos_left hw1 hcpos
      _ = r₀ := mul_div_cancel₀ _ hcpos.ne'
  have haC : a ∈ Ct := by
    have := G.U_subset 1 hx
    rw [ScBanach.paramProd_lvlSet] at this
    exact this.1
  set L : W 0 →L[ℝ] W 0 := (DB (a, w)).comp (ContinuousLinearMap.inr ℝ P (W 0)) with hL
  change ‖L ζ‖ ≤ ε * ‖ζ‖
  have hclosed : IsClosed {ζ : W 0 | ‖L ζ‖ ≤ ε * ‖ζ‖} :=
    isClosed_le L.continuous.norm (continuous_const.mul continuous_norm)
  refine (W.denseRange_incl 0).induction_on ζ hclosed fun ζ' => ?_
  -- the curve `t ↦ (a, w + t ζ')` in `U₁`
  obtain ⟨O, hO, hUO⟩ := G.relOpen 1
  have hxO : ((a, w) : (ScBanach.paramProd P W) 1) ∈ O := by rw [hUO] at hx; exact hx.1
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.isOpen_iff.1 hO _ hxO
  set η : ℝ := min (r₁ / (‖ζ'‖ + 1)) ((r₀ - ‖w₀‖) / (‖W.incl 0 ζ'‖ + 1)) with hη
  have hη0 : 0 < η := lt_min (by positivity) (div_pos (by linarith) (by positivity))
  have hmem₁ : ∀ t ∈ Ico (0 : ℝ) η, ((a, w + t • ζ') : (ScBanach.paramProd P W) 1) ∈ G.U 1 := by
    intro t ht
    rw [hUO]
    refine ⟨hr₁' ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have : ((a, w + t • ζ') : (ScBanach.paramProd P W) 1) - (a, w) = ((0 : P), t • ζ') := by
        ext <;> simp
      rw [this, Prod.norm_mk, norm_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      refine max_lt hr₁ ?_
      calc t * ‖ζ'‖ ≤ (r₁ / (‖ζ'‖ + 1)) * ‖ζ'‖ :=
            mul_le_mul_of_nonneg_right (ht.2.le.trans (min_le_left _ _)) (norm_nonneg _)
        _ < r₁ := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg ζ']
    · rw [ScBanach.paramProd_lvlSet]; exact ⟨haC, mem_univ _⟩
  have hmem₀ : ∀ t ∈ Ico (0 : ℝ) η, ‖w₀ + t • W.incl 0 ζ'‖ < r₀ := by
    intro t ht
    calc ‖w₀ + t • W.incl 0 ζ'‖ ≤ ‖w₀‖ + ‖t • W.incl 0 ζ'‖ := norm_add_le _ _
      _ = ‖w₀‖ + t * ‖W.incl 0 ζ'‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ ‖w₀‖ + ((r₀ - ‖w₀‖) / (‖W.incl 0 ζ'‖ + 1)) * ‖W.incl 0 ζ'‖ := by
          gcongr; exact ht.2.le.trans (min_le_right _ _)
      _ < ‖w₀‖ + (r₀ - ‖w₀‖) := by
          gcongr
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg (W.incl 0 ζ')]
      _ = r₀ := by ring
  set γ : ℝ → (ScBanach.paramProd P W) 1 := fun t => ((a, w) : (ScBanach.paramProd P W) 1) + t • ((0 : P), ζ') with hγ
  have hγeq : ∀ t, γ t = ((a, w + t • ζ') : (ScBanach.paramProd P W) 1) := fun t => by
    simp only [hγ, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero]
  have hγmem : ∀ t ∈ Ico (0 : ℝ) η, γ t ∈ G.U 1 := fun t ht => by rw [hγeq]; exact hmem₁ t ht
  have hγd : HasDerivWithinAt γ ((0 : P), ζ') (Ico 0 η) 0 := by
    simpa [hγ] using ((hasDerivAt_id (0 : ℝ)).smul_const (((0 : P), ζ') : (ScBanach.paramProd P W) 1)).const_add
      ((a, w) : (ScBanach.paramProd P W) 1) |>.hasDerivWithinAt
  -- the derivative of `φ = B ∘ ι ∘ γ` at `0`
  set φ : ℝ → W 0 := fun t => B ((ScBanach.paramProd P W).toBase 1 (γ t)) with hφ
  have hφd : HasDerivWithinAt φ (L (W.incl 0 ζ')) (Ico 0 η) 0 := by
    have h0 : γ 0 = ((a, w) : (ScBanach.paramProd P W) 1) := by simp [hγ]
    have hF : HasFDerivWithinAt (B ∘ (ScBanach.paramProd P W).toBase 1) ((DB (a, w)).comp ((ScBanach.paramProd P W).toBase 1)) (G.U 1) (γ 0) := by
      rw [h0]; exact hD.hasFDerivWithinAt _ hx
    have := hF.comp_hasDerivWithinAt (0 : ℝ) hγd hγmem
    have e : ((DB (a, w)).comp ((ScBanach.paramProd P W).toBase 1)) ((0 : P), ζ') =
        L (W.incl 0 ζ') := by
      rw [hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inr_apply, ScBanach.paramProd_toBase]
      rfl
    rw [e] at this
    exact this
  -- the slope bound
  have hslope : ∀ t ∈ Ico (0 : ℝ) η \ {0}, ‖slope φ 0 t‖ ≤ ε * ‖W.incl 0 ζ'‖ := by
    rintro t ⟨ht, ht0⟩
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm (by simpa using ht0))
    have hφt : φ t = B (a, w₀ + t • W.incl 0 ζ') := by
      show B ((ScBanach.paramProd P W).toBase 1 (γ t)) = _
      rw [hγeq, ScBanach.paramProd_toBase, map_add, map_smul]
      rfl
    have hφ0 : φ 0 = B (a, w₀) := by
      show B ((ScBanach.paramProd P W).toBase 1 (γ 0)) = _
      rw [hγeq, zero_smul, add_zero, ScBanach.paramProd_toBase]
    have hc := (hcontr a haC ha _ w₀ (hmem₀ t ht) hw0).2
    rw [levelB_zero, levelB_zero] at hc
    rw [slope_def_module, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos htpos, hφt,
      hφ0]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos] at hc
    rw [inv_mul_le_iff₀ htpos]
    linarith
  have hne : (𝓝[Ico (0 : ℝ) η \ {0}] 0).NeBot := by
    rw [Ico_sdiff_left]
    exact mem_closure_iff_nhdsWithin_neBot.1 (by
      rw [closure_Ioo hη0.ne]; exact left_mem_Icc.2 hη0.le)
  have hlim : Tendsto (fun t => ‖slope φ 0 t‖) (𝓝[Ico (0 : ℝ) η \ {0}] 0)
      (𝓝 ‖L (W.incl 0 ζ')‖) :=
    (hasDerivWithinAt_iff_tendsto_slope.1 hφd).norm
  exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall hslope)

/-! ### Lemma 3.1.9 (preprint 3.9) with smallness on the level of the estimate -/

/-- **Lemma 3.1.9 (preprint 3.9) on level `0`, with smallness on level `0`** (round-trip item V3.11): for every
`ε > 0` there is `r > 0` such that `|D₂B(x)ζ|₀ ≤ ε|ζ|₀` for all `x ∈ U₁` with `|ιx|₀ < r` and all
`ζ ∈ W₀`.  The proof of `exists_norm_deriv_snd_le` with `r` the radius of the level-`0`
contraction estimate: the curve `t ↦ x + t(0, ζ')`, `ζ' ∈ W₁`, stays in `U₁` for small `t ≥ 0`
because `U₁` is relatively open, whatever `|x|₁` is. -/
theorem IsSc0ContractionGerm.exists_norm_deriv_snd_le_base
    {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {B : P × W 0 → W 0}
    (hB : IsSc0ContractionGerm Ct G B)
    {DB : (ScBanach.paramProd P W) 1 → (ScBanach.paramProd P W) 0 →L[ℝ] W 0}
    (hD : IsSc1GermWith (F := W) G B DB) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ G.U 1, ‖(ScBanach.paramProd P W).toBase 1 x‖ < r → ∀ ζ : W 0,
      ‖DB x ((0 : P), ζ)‖ ≤ ε * ‖ζ‖ := by
  obtain ⟨r₀, hr₀, hcontr⟩ := hB.contraction ε hε 0
  refine ⟨r₀, hr₀, ?_⟩
  rintro ⟨a, w⟩ hx hxr ζ
  set w₀ : W 0 := W.toBase 1 w with hw₀
  rw [ScBanach.paramProd_toBase, Prod.norm_mk] at hxr
  have ha : ‖a‖ < r₀ := (le_max_left _ _).trans_lt hxr
  have hw0 : ‖w₀‖ < r₀ := (le_max_right _ _).trans_lt hxr
  have haC : a ∈ Ct := by
    have := G.U_subset 1 hx
    rw [ScBanach.paramProd_lvlSet] at this
    exact this.1
  set L : W 0 →L[ℝ] W 0 := (DB (a, w)).comp (ContinuousLinearMap.inr ℝ P (W 0)) with hL
  change ‖L ζ‖ ≤ ε * ‖ζ‖
  have hclosed : IsClosed {ζ : W 0 | ‖L ζ‖ ≤ ε * ‖ζ‖} :=
    isClosed_le L.continuous.norm (continuous_const.mul continuous_norm)
  refine (W.denseRange_incl 0).induction_on ζ hclosed fun ζ' => ?_
  -- the curve `t ↦ (a, w + t ζ')` in `U₁`
  obtain ⟨O, hO, hUO⟩ := G.relOpen 1
  have hxO : ((a, w) : (ScBanach.paramProd P W) 1) ∈ O := by rw [hUO] at hx; exact hx.1
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.isOpen_iff.1 hO _ hxO
  set η : ℝ := min (r₁ / (‖ζ'‖ + 1)) ((r₀ - ‖w₀‖) / (‖W.incl 0 ζ'‖ + 1)) with hη
  have hη0 : 0 < η := lt_min (by positivity) (div_pos (by linarith) (by positivity))
  have hmem₁ : ∀ t ∈ Ico (0 : ℝ) η, ((a, w + t • ζ') : (ScBanach.paramProd P W) 1) ∈ G.U 1 := by
    intro t ht
    rw [hUO]
    refine ⟨hr₁' ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have : ((a, w + t • ζ') : (ScBanach.paramProd P W) 1) - (a, w) = ((0 : P), t • ζ') := by
        ext <;> simp
      rw [this, Prod.norm_mk, norm_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      refine max_lt hr₁ ?_
      calc t * ‖ζ'‖ ≤ (r₁ / (‖ζ'‖ + 1)) * ‖ζ'‖ :=
            mul_le_mul_of_nonneg_right (ht.2.le.trans (min_le_left _ _)) (norm_nonneg _)
        _ < r₁ := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg ζ']
    · rw [ScBanach.paramProd_lvlSet]; exact ⟨haC, mem_univ _⟩
  have hmem₀ : ∀ t ∈ Ico (0 : ℝ) η, ‖w₀ + t • W.incl 0 ζ'‖ < r₀ := by
    intro t ht
    calc ‖w₀ + t • W.incl 0 ζ'‖ ≤ ‖w₀‖ + ‖t • W.incl 0 ζ'‖ := norm_add_le _ _
      _ = ‖w₀‖ + t * ‖W.incl 0 ζ'‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ ‖w₀‖ + ((r₀ - ‖w₀‖) / (‖W.incl 0 ζ'‖ + 1)) * ‖W.incl 0 ζ'‖ := by
          gcongr; exact ht.2.le.trans (min_le_right _ _)
      _ < ‖w₀‖ + (r₀ - ‖w₀‖) := by
          gcongr
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg (W.incl 0 ζ')]
      _ = r₀ := by ring
  set γ : ℝ → (ScBanach.paramProd P W) 1 :=
    fun t => ((a, w) : (ScBanach.paramProd P W) 1) + t • ((0 : P), ζ') with hγ
  have hγeq : ∀ t, γ t = ((a, w + t • ζ') : (ScBanach.paramProd P W) 1) := fun t => by
    simp only [hγ, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero]
  have hγmem : ∀ t ∈ Ico (0 : ℝ) η, γ t ∈ G.U 1 := fun t ht => by rw [hγeq]; exact hmem₁ t ht
  have hγd : HasDerivWithinAt γ ((0 : P), ζ') (Ico 0 η) 0 := by
    simpa [hγ] using ((hasDerivAt_id (0 : ℝ)).smul_const
      (((0 : P), ζ') : (ScBanach.paramProd P W) 1)).const_add
      ((a, w) : (ScBanach.paramProd P W) 1) |>.hasDerivWithinAt
  -- the derivative of `φ = B ∘ ι ∘ γ` at `0`
  set φ : ℝ → W 0 := fun t => B ((ScBanach.paramProd P W).toBase 1 (γ t)) with hφ
  have hφd : HasDerivWithinAt φ (L (W.incl 0 ζ')) (Ico 0 η) 0 := by
    have h0 : γ 0 = ((a, w) : (ScBanach.paramProd P W) 1) := by simp [hγ]
    have hF : HasFDerivWithinAt (B ∘ (ScBanach.paramProd P W).toBase 1)
        ((DB (a, w)).comp ((ScBanach.paramProd P W).toBase 1)) (G.U 1) (γ 0) := by
      rw [h0]; exact hD.hasFDerivWithinAt _ hx
    have := hF.comp_hasDerivWithinAt (0 : ℝ) hγd hγmem
    have e : ((DB (a, w)).comp ((ScBanach.paramProd P W).toBase 1)) ((0 : P), ζ') =
        L (W.incl 0 ζ') := by
      rw [hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inr_apply, ScBanach.paramProd_toBase]
      rfl
    rw [e] at this
    exact this
  -- the slope bound from the contraction estimate on level `0`
  have hslope : ∀ t ∈ Ico (0 : ℝ) η \ {0}, ‖slope φ 0 t‖ ≤ ε * ‖W.incl 0 ζ'‖ := by
    rintro t ⟨ht, ht0⟩
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm (by simpa using ht0))
    have hφt : φ t = B (a, w₀ + t • W.incl 0 ζ') := by
      change B ((ScBanach.paramProd P W).toBase 1 (γ t)) = _
      rw [hγeq, ScBanach.paramProd_toBase, map_add, map_smul]
      rfl
    have hφ0 : φ 0 = B (a, w₀) := by
      change B ((ScBanach.paramProd P W).toBase 1 (γ 0)) = _
      rw [hγeq, zero_smul, add_zero, ScBanach.paramProd_toBase]
    have hc := (hcontr a haC ha _ w₀ (hmem₀ t ht) hw0).2
    rw [levelB_zero, levelB_zero] at hc
    rw [slope_def_module, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos htpos, hφt,
      hφ0]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos] at hc
    rw [inv_mul_le_iff₀ htpos]
    linarith
  have hne : (𝓝[Ico (0 : ℝ) η \ {0}] 0).NeBot := by
    rw [Ico_sdiff_left]
    exact mem_closure_iff_nhdsWithin_neBot.1 (by
      rw [closure_Ioo hη0.ne]; exact left_mem_Icc.2 hη0.le)
  have hlim : Tendsto (fun t => ‖slope φ 0 t‖) (𝓝[Ico (0 : ℝ) η \ {0}] 0)
      (𝓝 ‖L (W.incl 0 ζ')‖) :=
    (hasDerivWithinAt_iff_tendsto_slope.1 hφd).norm
  exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall hslope)

/-- **Lemma 3.1.9 (preprint 3.9) on level `m`** (the text's statement, round-trip item V3.11): for every `ε > 0`
and `m` there is `r > 0` such that `|D₂B(x)ζ|_m ≤ ε|ζ|_m` for all `x ∈ U_{m+1}` with `|ιx|_m < r`
(small on level `m`) and all `ζ ∈ W_m`; here `D₂B(x)ζ` is the level-`m` operator of `DB(x)`
(`levelDeriv`) applied to `(0, ζ)`.  Proof: for `ζ' ∈ W_{m+1}` the curve `t ↦ x + t(0, ζ')` stays
in `U_{m+1}` for small `t ≥ 0` (`U_{m+1}` is relatively open); `B : U_{m+1} → W_m` is
differentiable within `U_{m+1}` (Proposition 1.2.1 (preprint 1.16), `IsSc1GermWith.hasFDerivWithinAt_level`), and
the difference quotients of `t ↦ B_m(a, ιw + tιζ')` are bounded by `ε|ιζ'|_m` through the
contraction estimate of Definition 3.3.1 (preprint 3.28) on level `m`; then density of `W_{m+1}` in `W_m`.  The
working-form estimate `ContractionGerm.norm_levelDeriv_snd_le` has the constant `1/2` and needs
`w` in the contraction regions. -/
theorem IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le
    (hC : IsQuadrantLike (ScBanach.const P) Ct)
    {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {B : P × W 0 → W 0}
    (hB : IsSc0ContractionGerm Ct G B)
    {DB : (ScBanach.paramProd P W) 1 → (ScBanach.paramProd P W) 0 →L[ℝ] W 0}
    (hD : IsSc1GermWith (F := W) G B DB) {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ r > 0, ∀ x ∈ G.U (m + 1), ‖(ScBanach.paramProd P W).incl m x‖ < r → ∀ ζ : W m,
      ‖levelDeriv DB m x ((0 : P), ζ)‖ ≤ ε * ‖ζ‖ := by
  obtain ⟨r₀, hr₀, hcontr⟩ := hB.contraction ε hε m
  refine ⟨r₀, hr₀, ?_⟩
  rintro ⟨a, w⟩ hx hxr ζ
  set E := ScBanach.paramProd P W with hE
  have hincl : E.incl m ((a, w) : E (m + 1)) = ((a, W.incl m w) : E m) := rfl
  rw [hincl, Prod.norm_mk] at hxr
  have ha : ‖a‖ < r₀ := (le_max_left _ _).trans_lt hxr
  have hw0 : ‖W.incl m w‖ < r₀ := (le_max_right _ _).trans_lt hxr
  have haC : a ∈ Ct := by
    have := G.U_subset (m + 1) hx
    rw [ScBanach.paramProd_lvlSet] at this
    exact this.1
  set L : W m →L[ℝ] W m :=
    (levelDeriv DB m ((a, w) : E (m + 1))).comp (ContinuousLinearMap.inr ℝ P (W m)) with hL
  change ‖L ζ‖ ≤ ε * ‖ζ‖
  have hclosed : IsClosed {ζ : W m | ‖L ζ‖ ≤ ε * ‖ζ‖} :=
    isClosed_le L.continuous.norm (continuous_const.mul continuous_norm)
  refine (W.denseRange_incl m).induction_on ζ hclosed fun ζ' => ?_
  -- the curve `t ↦ (a, w + t ζ')` in `U_{m+1}`
  obtain ⟨O, hO, hUO⟩ := G.relOpen (m + 1)
  have hxO : ((a, w) : E (m + 1)) ∈ O := by rw [hUO] at hx; exact hx.1
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.isOpen_iff.1 hO _ hxO
  set η : ℝ := min (r₁ / (‖ζ'‖ + 1)) ((r₀ - ‖W.incl m w‖) / (‖W.incl m ζ'‖ + 1)) with hη
  have hη0 : 0 < η := lt_min (by positivity) (div_pos (by linarith) (by positivity))
  have hmem₁ : ∀ t ∈ Ico (0 : ℝ) η, ((a, w + t • ζ') : E (m + 1)) ∈ G.U (m + 1) := by
    intro t ht
    rw [hUO]
    refine ⟨hr₁' ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have : ((a, w + t • ζ') : E (m + 1)) - (a, w) = ((0 : P), t • ζ') := by
        ext <;> simp
      rw [this, Prod.norm_mk, norm_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      refine max_lt hr₁ ?_
      calc t * ‖ζ'‖ ≤ (r₁ / (‖ζ'‖ + 1)) * ‖ζ'‖ :=
            mul_le_mul_of_nonneg_right (ht.2.le.trans (min_le_left _ _)) (norm_nonneg _)
        _ < r₁ := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg ζ']
    · rw [ScBanach.paramProd_lvlSet]; exact ⟨haC, mem_univ _⟩
  have hmemr : ∀ t ∈ Ico (0 : ℝ) η, ‖W.incl m w + t • W.incl m ζ'‖ < r₀ := by
    intro t ht
    calc ‖W.incl m w + t • W.incl m ζ'‖ ≤ ‖W.incl m w‖ + ‖t • W.incl m ζ'‖ := norm_add_le _ _
      _ = ‖W.incl m w‖ + t * ‖W.incl m ζ'‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ ‖W.incl m w‖ + ((r₀ - ‖W.incl m w‖) / (‖W.incl m ζ'‖ + 1)) * ‖W.incl m ζ'‖ := by
          gcongr; exact ht.2.le.trans (min_le_right _ _)
      _ < ‖W.incl m w‖ + (r₀ - ‖W.incl m w‖) := by
          gcongr
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg (W.incl m ζ')]
      _ = r₀ := by ring
  set γ : ℝ → E (m + 1) := fun t => ((a, w) : E (m + 1)) + t • ((0 : P), ζ') with hγ
  have hγeq : ∀ t, γ t = ((a, w + t • ζ') : E (m + 1)) := fun t => by
    simp only [hγ, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero]
  have hγmem : ∀ t ∈ Ico (0 : ℝ) η, γ t ∈ G.U (m + 1) := fun t ht => by
    rw [hγeq]; exact hmem₁ t ht
  have hγd : HasDerivWithinAt γ ((0 : P), ζ') (Ico 0 η) 0 := by
    simpa [hγ] using ((hasDerivAt_id (0 : ℝ)).smul_const (((0 : P), ζ') : E (m + 1))).const_add
      ((a, w) : E (m + 1)) |>.hasDerivWithinAt
  -- the derivative of `φ = B_m ∘ ι ∘ γ` at `0` (Proposition 1.2.1 (preprint 1.16))
  set φ : ℝ → W m := fun t => levelMap B m (E.incl m (γ t)) with hφ
  have hφd : HasDerivWithinAt φ (L (W.incl m ζ')) (Ico 0 η) 0 := by
    have h0 : γ 0 = ((a, w) : E (m + 1)) := by simp [hγ]
    have hF : HasFDerivWithinAt (levelMap B m ∘ E.incl m)
        ((levelDeriv DB m ((a, w) : E (m + 1))).comp (E.incl m)) (G.U (m + 1)) (γ 0) := by
      rw [h0]; exact hD.hasFDerivWithinAt_level (hC.paramProd W) hx
    exact hF.comp_hasDerivWithinAt (0 : ℝ) hγd hγmem
  -- the slope bound from the contraction estimate on level `m`
  have hslope : ∀ t ∈ Ico (0 : ℝ) η \ {0}, ‖slope φ 0 t‖ ≤ ε * ‖W.incl m ζ'‖ := by
    rintro t ⟨ht, ht0⟩
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm (by simpa using ht0))
    have hφt : φ t = levelB B m (a, W.incl m w + t • W.incl m ζ') := by
      simp only [hφ, hγ, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero]
      change levelB B m (a, W.incl m (w + t • ζ')) = _
      rw [map_add, map_smul]
    have hφ0 : φ 0 = levelB B m (a, W.incl m w) := by
      simp only [hφ, hγ, zero_smul, add_zero]; rfl
    have hc := (hcontr a haC ha _ _ (hmemr t ht) hw0).2
    rw [slope_def_module, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos htpos, hφt,
      hφ0]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos] at hc
    rw [inv_mul_le_iff₀ htpos]
    linarith
  have hne : (𝓝[Ico (0 : ℝ) η \ {0}] 0).NeBot := by
    rw [Ico_sdiff_left]
    exact mem_closure_iff_nhdsWithin_neBot.1 (by
      rw [closure_Ioo hη0.ne]; exact left_mem_Icc.2 hη0.le)
  have hlim : Tendsto (fun t => ‖slope φ 0 t‖) (𝓝[Ico (0 : ℝ) η \ {0}] 0)
      (𝓝 ‖L (W.incl m ζ')‖) :=
    (hasDerivWithinAt_iff_tendsto_slope.1 hφd).norm
  have := le_of_tendsto hlim (eventually_nhdsWithin_of_forall hslope)
  change ‖L (W.incl m ζ')‖ ≤ ε * ‖W.incl m ζ'‖
  exact this

/-! ### The derivative of `f + s` at points of `U₁` -/

namespace StabilityData

variable (𝒮 : StabilityData Ct W) {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [FiniteDimensional ℝ Q] {f : P × W 0 → Q × W 0} {B : P × W 0 → W 0}

/-- The derivative family of `f + s` on `U₁` (`𝒮.Dfs f` is its value at `0`). -/
abbrev Dfs' (f : P × W 0 → Q × W 0) :
    (ScBanach.paramProd P W) 1 → (ScBanach.paramProd P W) 0 →L[ℝ] Q × W 0 :=
  scDerivGerm (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒮.G (𝒮.fsum f)

/-- The derivative family of `s` (sc⁺: with values in `W₁`). -/
abbrev Ds : (ScBanach.paramProd P W) 1 → (ScBanach.paramProd P W) 0 →L[ℝ] W 1 :=
  scDerivGerm (E := ScBanach.paramProd P W) (F := W.shift) 𝒮.G 𝒮.s

omit 𝒮 in
/-- The derivative family of the basic germ `f`. -/
abbrev Df (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)) (f : P × W 0 → Q × W 0) :
    (ScBanach.paramProd P W) 1 → (ScBanach.paramProd P W) 0 →L[ℝ] Q × W 0 :=
  scDerivGerm (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) G f

omit 𝒮 in
/-- The derivative family of the contraction map `B`. -/
abbrev DB (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)) (B : P × W 0 → W 0) :
    (ScBanach.paramProd P W) 1 → (ScBanach.paramProd P W) 0 →L[ℝ] W 0 :=
  scDerivGerm (E := ScBanach.paramProd P W) (F := W) G B

lemma Dfs'_zero (f : P × W 0 → Q × W 0) : 𝒮.Dfs' f 0 = 𝒮.Dfs f := rfl

lemma isSc1GermWith_Dfs' (hC : IsQuadrantLike (ScBanach.const P) Ct)
    (hf : IsScSmoothGerm (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W) 𝒮.G f) :
    IsSc1GermWith (F := ScBanach.paramProd Q W) 𝒮.G (𝒮.fsum f) (𝒮.Dfs' f) :=
  ((𝒮.fsum_isScSmoothGerm hC hf) 1).1.isSc1GermWith_scDerivGerm

lemma isSc1GermWith_Ds : IsSc1GermWith (F := W.shift) 𝒮.G 𝒮.s 𝒮.Ds :=
  ((𝒮.isScSmooth) 1).1.isSc1GermWith_scDerivGerm

omit 𝒮 in
lemma isSc1GermWith_Df {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)}
    (hf : IsBasicGerm Ct G f B) : IsSc1GermWith (F := ScBanach.paramProd Q W) G f (Df G f) :=
  (hf.isScSmooth 1).1.isSc1GermWith_scDerivGerm

omit 𝒮 in
lemma isSc1GermWith_DB (hC : IsQuadrantLike (ScBanach.const P) Ct)
    {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} (hf : IsBasicGerm Ct G f B) :
    IsSc1GermWith (F := W) G B (DB G B) :=
  ((hf.B_isScSmoothGerm hC) 1).1.isSc1GermWith_scDerivGerm

variable (hC : IsPartialQuadrant (ScBanach.const P) Ct) (hf : IsBasicGerm Ct 𝒮.G f B)
include hC hf

/-- `D(f + s)(x) = Df(x) + ι ∘ Ds(x)` for `x ∈ U₁` (uniqueness of the derivative within `U₁`,
then density of `E₁` in `E₀`). -/
theorem Dfs'_eq {x : (ScBanach.paramProd P W) 1} (hx : x ∈ 𝒮.G.U 1) :
    𝒮.Dfs' f x = Df 𝒮.G f x +
      (ContinuousLinearMap.inr ℝ Q (W 0)).comp ((W.toBase 1).comp (𝒮.Ds x)) := by
  have hCq : IsQuadrantLike (ScBanach.paramProd P W) (Ct ×ˢ univ) := (hC.prod_univ W).isQuadrantLike
  have h1 := (𝒮.isSc1GermWith_Dfs' hC.isQuadrantLike hf.isScSmooth).hasFDerivWithinAt x hx
  have h2 : HasFDerivWithinAt (𝒮.fsum f ∘ (ScBanach.paramProd P W).toBase 1)
      ((Df 𝒮.G f x).comp ((ScBanach.paramProd P W).toBase 1) +
        ((ContinuousLinearMap.inr ℝ Q (W 0)).comp (W.toBase 1)).comp ((𝒮.Ds x).comp ((ScBanach.paramProd P W).toBase 1)))
      (𝒮.G.U 1) x := by
    have ha := (isSc1GermWith_Df hf).hasFDerivWithinAt x hx
    have hb := ((ContinuousLinearMap.inr ℝ Q (W 0)).comp (W.toBase 1)).hasFDerivAt.comp_hasFDerivWithinAt
      x (𝒮.isSc1GermWith_Ds.hasFDerivWithinAt x hx)
    refine (ha.add hb).congr (fun y _ => ?_) ?_
    · simp only [Function.comp, fsum_apply]
      rfl
    · simp only [Function.comp, fsum_apply]
      rfl
  have heq := (𝒮.G.uniqueDiffWithinAt hCq 1 hx).eq h1 h2
  have key : (𝒮.Dfs' f x).comp ((ScBanach.paramProd P W).toBase 1) =
      (Df 𝒮.G f x + (ContinuousLinearMap.inr ℝ Q (W 0)).comp ((W.toBase 1).comp (𝒮.Ds x))).comp
        ((ScBanach.paramProd P W).toBase 1) := by
    rw [heq]
    ext y <;> simp [ContinuousLinearMap.comp_apply]
  exact ContinuousLinearMap.ext_of_comp_toBase_one key

/-- The `W`-component of `Df(x)` for `x ∈ U₁`: `pr_W Df(x) = pr_W − DB(x)` (from
`pr_W ∘ f = pr_W − B` on `U₀`, Definition 3.1.7 (preprint 3.7)). -/
theorem snd_Df_eq {x : (ScBanach.paramProd P W) 1} (hx : x ∈ 𝒮.G.U 1) :
    (ContinuousLinearMap.snd ℝ Q (W 0)).comp (Df 𝒮.G f x) =
      ContinuousLinearMap.snd ℝ P (W 0) - DB 𝒮.G B x := by
  have hCq : IsQuadrantLike (ScBanach.paramProd P W) (Ct ×ˢ univ) := (hC.prod_univ W).isQuadrantLike
  have h1 := ((isSc1GermWith_Df hf).hasFDerivWithinAt x hx).snd
  have h2 : HasFDerivWithinAt (fun y : (ScBanach.paramProd P W) 1 => (f ((ScBanach.paramProd P W).toBase 1 y)).2)
      ((ContinuousLinearMap.snd ℝ P (W 0)).comp ((ScBanach.paramProd P W).toBase 1) - (DB 𝒮.G B x).comp ((ScBanach.paramProd P W).toBase 1))
      (𝒮.G.U 1) x := by
    have ha : HasFDerivWithinAt (fun y : (ScBanach.paramProd P W) 1 => ((ScBanach.paramProd P W).toBase 1 y).2)
        ((ContinuousLinearMap.snd ℝ P (W 0)).comp ((ScBanach.paramProd P W).toBase 1)) (𝒮.G.U 1) x :=
      ((ContinuousLinearMap.snd ℝ P (W 0)).comp ((ScBanach.paramProd P W).toBase 1)).hasFDerivAt.hasFDerivWithinAt
    have hb := (isSc1GermWith_DB hC.isQuadrantLike hf).hasFDerivWithinAt x hx
    refine (ha.sub hb).congr (fun y hy => ?_) ?_
    · show (f _).2 = ((ScBanach.paramProd P W).toBase 1 y).2 - B ((ScBanach.paramProd P W).toBase 1 y)
      exact hf.snd_eq _ (𝒮.G.toBase_mem hy)
    · show (f _).2 = ((ScBanach.paramProd P W).toBase 1 x).2 - B ((ScBanach.paramProd P W).toBase 1 x)
      exact hf.snd_eq _ (𝒮.G.toBase_mem hx)
  have heq := (𝒮.G.uniqueDiffWithinAt hCq 1 hx).eq h1 h2
  have key : ((ContinuousLinearMap.snd ℝ Q (W 0)).comp (Df 𝒮.G f x)).comp
        ((ScBanach.paramProd P W).toBase 1) =
      (ContinuousLinearMap.snd ℝ P (W 0) - DB 𝒮.G B x).comp ((ScBanach.paramProd P W).toBase 1) := by
    rw [ContinuousLinearMap.comp_assoc, heq, ContinuousLinearMap.sub_comp]
  exact ContinuousLinearMap.ext_of_comp_toBase_one key

/-- `D₂B(0) = 0` (Lemma 3.1.9 (preprint 3.9) at `0`). -/
theorem DB_zero_snd (ζ : W 0) : DB 𝒮.G B 0 ((0 : P), ζ) = 0 :=
  hf.contraction.deriv_zero_snd
    ((isSc1GermWith_DB hC.isQuadrantLike hf).hasFDerivWithinAt 0 (𝒮.G.zero_mem 1)) ζ

/-! ### The decomposition `D(f + s)(x) = D(f + s)(0) + S(x) + K(x)`, `‖S(x)‖ ≤ ε`, `K(x)` compact -/

omit hC hf in
/-- The small part `S(x)(α, ζ) = (0, −D₂B(x)ζ)` of `D(f + s)(x) − D(f + s)(0)`. -/
def Sop (B : P × W 0 → W 0) (x : (ScBanach.paramProd P W) 1) :
    (ScBanach.paramProd P W) 0 →L[ℝ] Q × W 0 :=
  -((ContinuousLinearMap.inr ℝ Q (W 0)).comp
    (((DB 𝒮.G B x).comp (ContinuousLinearMap.inr ℝ P (W 0))).comp
      (ContinuousLinearMap.snd ℝ P (W 0))))

omit hC hf in
lemma Sop_apply (B : P × W 0 → W 0) (x : (ScBanach.paramProd P W) 1)
    (y : (ScBanach.paramProd P W) 0) :
    𝒮.Sop (Q := Q) B x y = ((0 : Q), -(DB 𝒮.G B x ((0 : P), y.2))) := by
  simp only [Sop, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_snd', Prod.neg_mk, neg_zero]

omit hC hf in
/-- The compact part `K(x) = D(f + s)(x) − D(f + s)(0) − S(x)`. -/
def Kop (f : P × W 0 → Q × W 0) (B : P × W 0 → W 0) (x : (ScBanach.paramProd P W) 1) :
    (ScBanach.paramProd P W) 0 →L[ℝ] Q × W 0 :=
  𝒮.Dfs' f x - 𝒮.Dfs' f 0 - 𝒮.Sop B x

omit hC hf in
lemma Dfs'_eq_add (f : P × W 0 → Q × W 0) (B : P × W 0 → W 0) (x : (ScBanach.paramProd P W) 1) :
    𝒮.Dfs' f x = 𝒮.Dfs f + 𝒮.Sop B x + 𝒮.Kop f B x := by
  simp only [Kop, Dfs'_zero]; abel

omit hC hf in
/-- `‖S(x)‖ ≤ ε` for `x ∈ U₁` small on level `1` (Lemma 3.1.9 (preprint 3.9)). -/
theorem exists_norm_Sop_le (hC : IsQuadrantLike (ScBanach.const P) Ct)
    (hf : IsBasicGerm Ct 𝒮.G f B) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ 𝒮.G.U 1, ‖x‖ < r → ‖𝒮.Sop (Q := Q) B x‖ ≤ ε := by
  obtain ⟨r, hr, h⟩ := hf.contraction.exists_norm_deriv_snd_le (isSc1GermWith_DB hC hf) hε
  refine ⟨r, hr, fun x hx hxr => ContinuousLinearMap.opNorm_le_bound _ hε.le fun y => ?_⟩
  rw [Sop_apply, Prod.norm_mk, norm_zero, norm_neg]
  exact max_le (by positivity)
    ((h x hx hxr y.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le y) hε.le))

/-- `K(x)` is compact: it is the sum of the finite-rank operators
`(α, ζ) ↦ (pr_{ℝᴺ}(Df(x) − Df(0))(α, ζ), 0)` and `(α, ζ) ↦ (0, (DB(0) − DB(x))(α, 0))` and of
`(α, ζ) ↦ (0, ι(Ds(x) − Ds(0))(α, ζ))` through the compact inclusion `ι : W₁ → W₀`. -/
theorem Kop_isCompactOperator {x : (ScBanach.paramProd P W) 1} (hx : x ∈ 𝒮.G.U 1) :
    IsCompactOperator (𝒮.Kop f B x) := by
  have h0 : (0 : (ScBanach.paramProd P W) 1) ∈ 𝒮.G.U 1 := 𝒮.G.zero_mem 1
  set C₁ : (ScBanach.paramProd P W) 0 →L[ℝ] Q × W 0 :=
    (ContinuousLinearMap.inl ℝ Q (W 0)).comp
      ((ContinuousLinearMap.fst ℝ Q (W 0)).comp (Df 𝒮.G f x - Df 𝒮.G f 0)) with hC₁
  set C₂ : (ScBanach.paramProd P W) 0 →L[ℝ] Q × W 0 :=
    (ContinuousLinearMap.inr ℝ Q (W 0)).comp
      (((DB 𝒮.G B 0 - DB 𝒮.G B x).comp (ContinuousLinearMap.inl ℝ P (W 0))).comp
        (ContinuousLinearMap.fst ℝ P (W 0))) with hC₂
  set C₃ : (ScBanach.paramProd P W) 0 →L[ℝ] Q × W 0 :=
    ((ContinuousLinearMap.inr ℝ Q (W 0)).comp (W.toBase 1)).comp (𝒮.Ds x - 𝒮.Ds 0) with hC₃
  have hK : 𝒮.Kop f B x = C₁ + C₂ + C₃ := by
    have e1 := 𝒮.Dfs'_eq hC hf hx
    have e0 := 𝒮.Dfs'_eq hC hf h0
    refine ContinuousLinearMap.ext fun y => ?_
    obtain ⟨α, ζ⟩ := y
    have s1 := DFunLike.congr_fun (𝒮.snd_Df_eq hC hf hx) (α, ζ)
    have s0 := DFunLike.congr_fun (𝒮.snd_Df_eq hC hf h0) (α, ζ)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', sub_apply] at s1 s0
    have z := 𝒮.DB_zero_snd hC hf ζ
    have lin_x : DB 𝒮.G B x (α, ζ) = DB 𝒮.G B x (α, 0) + DB 𝒮.G B x (0, ζ) := by
      rw [← map_add]; simp
    have lin_0 : DB 𝒮.G B 0 (α, ζ) = DB 𝒮.G B 0 (α, 0) + DB 𝒮.G B 0 (0, ζ) := by
      rw [← map_add]; simp
    have hS := 𝒮.Sop_apply (Q := Q) B x (α, ζ)
    simp only [Kop, hC₁, hC₂, hC₃, e1, e0, hS, sub_apply,
      add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', map_sub]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.snd_add, Prod.snd_sub, Prod.snd_neg, Prod.snd_zero, s1, s0,
        lin_x, lin_0, z, add_zero]
      abel
  have hC₁c : IsCompactOperator C₁ := by
    have : FiniteDimensional ℝ (LinearMap.range (C₁ : (ScBanach.paramProd P W) 0 →ₗ[ℝ] Q × W 0)) := by
      refine Submodule.finiteDimensional_of_le
        (S₂ := LinearMap.range ((ContinuousLinearMap.inl ℝ Q (W 0) : Q →L[ℝ] Q × W 0) :
          Q →ₗ[ℝ] Q × W 0)) ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨((ContinuousLinearMap.fst ℝ Q (W 0)).comp (Df 𝒮.G f x - Df 𝒮.G f 0)) y, rfl⟩
    exact isCompactOperator_of_finiteDimensional_range C₁
  have hC₂c : IsCompactOperator C₂ := by
    have : FiniteDimensional ℝ (LinearMap.range (C₂ : (ScBanach.paramProd P W) 0 →ₗ[ℝ] Q × W 0)) := by
      refine Submodule.finiteDimensional_of_le
        (S₂ := LinearMap.range (((ContinuousLinearMap.inr ℝ Q (W 0)).comp
          ((DB 𝒮.G B 0 - DB 𝒮.G B x).comp (ContinuousLinearMap.inl ℝ P (W 0))) : P →L[ℝ] Q × W 0) :
          P →ₗ[ℝ] Q × W 0)) ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨y.1, rfl⟩
    exact isCompactOperator_of_finiteDimensional_range C₂
  have hC₃c : IsCompactOperator C₃ :=
    ((W.toBase_succ_isCompactOperator 0).clm_comp (ContinuousLinearMap.inr ℝ Q (W 0))).comp_clm
      (𝒮.Ds x - 𝒮.Ds 0)
  rw [hK]
  exact (hC₁c.add hC₂c).add hC₃c

/-! ### `D(f + s)(x)` is Fredholm of index `n − N` for `x ∈ U₁` small -/

/-- `D(f + s)(0)` is Fredholm: `Df(0)` is (Proposition 3.1.10 (preprint 3.10)) and `ι ∘ Ds(0)` is compact. -/
theorem isFredholm_Dfs : IsFredholm (𝒮.Dfs f) ∧
    fredholmIndex (𝒮.Dfs f) = Module.finrank ℝ P - Module.finrank ℝ Q := by
  obtain ⟨hF0, hI0⟩ := proposition_3_1_10_basic_level_zero hC hf
  have hDfs0 : 𝒮.Dfs f = Df 𝒮.G f 0 +
      (ContinuousLinearMap.inr ℝ Q (W 0)).comp ((W.toBase 1).comp (𝒮.Ds 0)) :=
    𝒮.Dfs'_eq hC hf (𝒮.G.zero_mem 1)
  have hcpt : IsCompactOperator
      ((ContinuousLinearMap.inr ℝ Q (W 0)).comp ((W.toBase 1).comp (𝒮.Ds 0))) :=
    ((W.toBase_succ_isCompactOperator 0).clm_comp (ContinuousLinearMap.inr ℝ Q (W 0))).comp_clm
      (𝒮.Ds 0)
  rw [hDfs0]
  exact ⟨isFredholm_add_isCompactOperator hF0 hcpt,
    by rw [fredholmIndex_add_isCompactOperator hF0 hcpt, hI0]⟩

/-- **Corollary 3.5.3 (preprint 3.41), the Fredholm part**: `D(f + s)(x) : E₀ → F₀` is a Fredholm operator of index
`n − N` for every `x ∈ U₁` sufficiently small on level `1` (not only for solutions). -/
theorem exists_isFredholm_Dfs' : ∃ r > 0, ∀ x ∈ 𝒮.G.U 1, ‖x‖ < r →
    IsFredholm (𝒮.Dfs' f x) ∧
      fredholmIndex (𝒮.Dfs' f x) = Module.finrank ℝ P - Module.finrank ℝ Q := by
  obtain ⟨hF0, hI0⟩ := 𝒮.isFredholm_Dfs hC hf
  obtain ⟨v, hv⟩ := hF0.exists_isQuasiInverse
  obtain ⟨r, hr, hS⟩ := 𝒮.exists_norm_Sop_le hC.isQuadrantLike hf (ε := 1 / (‖v‖ + 1))
    (by positivity)
  refine ⟨r, hr, fun x hx hxr => ?_⟩
  have hsmall : ‖v‖ * ‖𝒮.Sop (Q := Q) B x‖ < 1 := by
    calc ‖v‖ * ‖𝒮.Sop (Q := Q) B x‖ ≤ ‖v‖ * (1 / (‖v‖ + 1)) :=
          mul_le_mul_of_nonneg_left (hS x hx hxr) (norm_nonneg _)
      _ < 1 := by
          rw [mul_one_div, div_lt_one (by positivity)]; linarith
  obtain ⟨hF1, hI1⟩ := isFredholm_fredholmIndex_add_of_norm_lt hv hsmall
  have hK := 𝒮.Kop_isCompactOperator hC hf hx
  rw [𝒮.Dfs'_eq_add f B x]
  exact ⟨isFredholm_add_isCompactOperator hF1 hK,
    by rw [fredholmIndex_add_isCompactOperator hF1 hK, hI1, hI0]⟩

end StabilityData

/-! ### Joint continuity of the tangent map, in sequences -/

section Tangent

variable {E F : ScBanach} {C : Set (E 0)} {G : ScNbhdGerm E C} {g : E 0 → F 0}
  {D : E 1 → E 0 →L[ℝ] F 0}

/-- The tangent map `(x, h) ↦ Dg(x)h` of an sc¹-germ is jointly continuous on `U₁ × E₀`, in
sequences: `x_k → x₀` in `E₁` (all in `U₁`) and `h_k → h₀` in `E₀` give `Dg(x_k)h_k → Dg(x₀)h₀`. -/
theorem IsSc1GermWith.tendsto_deriv (hD : IsSc1GermWith G g D) {x : ℕ → E 1} {h : ℕ → E 0}
    {x₀ : E 1} {h₀ : E 0} (hx : ∀ k, x k ∈ G.U 1) (hx₀ : x₀ ∈ G.U 1)
    (hxt : Tendsto x atTop (𝓝 x₀)) (hht : Tendsto h atTop (𝓝 h₀)) :
    Tendsto (fun k => D (x k) (h k)) atTop (𝓝 (D x₀ h₀)) := by
  have hcont : ContinuousOn (fun p : E 1 × E 0 => D p.1 p.2) (G.U 1 ×ˢ univ) := by
    have := (hD.tangent_isSc0.continuousOn 0).congr
      (fun p _ => (levelMap_zero (E := E.tangent) (F := F.tangent) (tangentMapWith g D) p).symm)
    exact this.snd
  have hmem : (x₀, h₀) ∈ G.U 1 ×ˢ (univ : Set (E 0)) := ⟨hx₀, mem_univ _⟩
  exact ((hcont _ hmem).tendsto).comp
    (tendsto_nhdsWithin_iff.2 ⟨hxt.prodMk_nhds hht, Eventually.of_forall fun k => ⟨hx k, mem_univ _⟩⟩)

/-- The derivatives `Dg(x)`, `x ∈ U₁` near `0`, are uniformly bounded (from the continuity of the
tangent map at `(0, 0)` and homogeneity in `h`). -/
theorem IsSc1GermWith.exists_norm_deriv_le (hD : IsSc1GermWith G g D) :
    ∃ ρ > 0, ∃ c : ℝ, ∀ x ∈ G.U 1, ‖x‖ < ρ → ∀ h : E 0, ‖D x h‖ ≤ c * ‖h‖ := by
  have hcont : ContinuousOn (fun p : E 1 × E 0 => D p.1 p.2) (G.U 1 ×ˢ univ) := by
    have := (hD.tangent_isSc0.continuousOn 0).congr
      (fun p _ => (levelMap_zero (E := E.tangent) (F := F.tangent) (tangentMapWith g D) p).symm)
    exact this.snd
  have h00 : ((0 : E 1), (0 : E 0)) ∈ G.U 1 ×ˢ (univ : Set (E 0)) := ⟨G.zero_mem 1, mem_univ _⟩
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 (hcont _ h00) 1 one_pos
  refine ⟨δ / 2, by positivity, 2 / δ, fun x hx hxρ h => ?_⟩
  by_cases hh : h = 0
  · simp [hh]
  have hhn : 0 < ‖h‖ := norm_pos_iff.2 hh
  set h' : E 0 := (δ / 2 / ‖h‖) • h with hh'
  have hh'n : ‖h'‖ = δ / 2 := by
    rw [hh', norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_cancel₀ _ hhn.ne']
  have hdist : dist ((x, h') : E 1 × E 0) (0, 0) < δ := by
    rw [Prod.dist_eq]
    show max (dist x 0) (dist h' 0) < δ
    rw [dist_zero_right, dist_zero_right, hh'n]
    exact max_lt (by linarith) (by linarith)
  have hlt := hδ' ⟨hx, mem_univ _⟩ hdist
  simp only [map_zero, dist_zero_right] at hlt
  have hD' : D x h = (‖h‖ / (δ / 2)) • D x h' := by
    rw [hh', map_smul, smul_smul, show ‖h‖ / (δ / 2) * (δ / 2 / ‖h‖) = 1 by field_simp, one_smul]
  rw [hD', norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖h‖ / (δ / 2) * ‖D x h'‖ ≤ ‖h‖ / (δ / 2) * 1 :=
        mul_le_mul_of_nonneg_left hlt.le (by positivity)
    _ = 2 / δ * ‖h‖ := by field_simp

end Tangent

namespace StabilityData

variable (𝒮 : StabilityData Ct W) {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [FiniteDimensional ℝ Q] {f : P × W 0 → Q × W 0} {B : P × W 0 → W 0}
  (hC : IsPartialQuadrant (ScBanach.const P) Ct) (hf : IsBasicGerm Ct 𝒮.G f B)
include hC hf

/-! ### The kernel of `D(f + s)(x)` meets a complement of `ker D(f + s)(0)` trivially -/

/-- **The compactness argument of Corollary 3.5.3 (preprint 3.41)**: if `N` is a closed complement of
`ker D(f + s)(0)`, then `ker D(f + s)(x) ∩ N = {0}` for all `x ∈ U₁` sufficiently small on level
`1`.  Proof by contradiction with sequences `x_k → 0` in `E₁` and unit vectors
`(α_k, ζ_k) ∈ N ∩ ker D(f + s)(x_k)`: the `W`-component of the equation reads
`ζ_k = D₁B(x_k)α_k + D₂B(x_k)ζ_k − ι Ds(x_k)(α_k, ζ_k)`; `α_k` has a convergent subsequence,
`Ds(x_k)(α_k, ζ_k)` is bounded in `W₁` so `ι Ds(x_k)(α_k, ζ_k)` has a convergent subsequence
in `W₀`, `D₁B(x_k)α_k → D₁B(0)α` by the continuity of the tangent map, and
`‖D₂B(x_k)‖ → 0` (Lemma 3.1.9 (preprint 3.9)); so `(α_k, ζ_k) → (α, z₀) ∈ N`, `|(α, z₀)| = 1` and
`D(f + s)(0)(α, z₀) = 0`, a contradiction. -/
theorem exists_ker_Dfs'_inf_eq_bot {N : Submodule ℝ (P × W 0)} (hNc : IsClosed (N : Set (P × W 0)))
    (hN : Disjoint (LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) N) :
    ∃ r > 0, ∀ x ∈ 𝒮.G.U 1, ‖x‖ < r → ∀ y ∈ N, 𝒮.Dfs' f x y = 0 → y = 0 := by
  have hCq := hC.isQuadrantLike
  have hDB := isSc1GermWith_DB hCq hf
  have hDs := 𝒮.isSc1GermWith_Ds
  have hDfs := 𝒮.isSc1GermWith_Dfs' hCq hf.isScSmooth
  -- the uniform bound for `Ds(x)`
  obtain ⟨ρ, hρ, c, hc⟩ := hDs.exists_norm_deriv_le
  -- the radii of Lemma 3.1.9 (preprint 3.9) for `ε = 1/(k+1)`
  have hL39 : ∀ k : ℕ, ∃ r > 0, ∀ x ∈ 𝒮.G.U 1, ‖x‖ < r →
      ∀ ζ : W 0, ‖DB 𝒮.G B x ((0 : P), ζ)‖ ≤ 1 / ((k : ℝ) + 1) * ‖ζ‖ := fun k =>
    hf.contraction.exists_norm_deriv_snd_le hDB (by positivity)
  choose r39 hr39 h39 using hL39
  by_contra hcon
  push_neg at hcon
  -- the sequences
  have hseq : ∀ k : ℕ, ∃ x ∈ 𝒮.G.U 1, ‖x‖ < min (1 / ((k : ℝ) + 1)) (min ρ (r39 k)) ∧
      ∃ y ∈ N, 𝒮.Dfs' f x y = 0 ∧ y ≠ 0 := fun k =>
    hcon _ (lt_min (by positivity) (lt_min hρ (hr39 k)))
  choose x hxU hxr y hyN hyD hy0 using hseq
  set u : ℕ → P × W 0 := fun k => (‖y k‖⁻¹ : ℝ) • y k with hu
  have hun : ∀ k, ‖u k‖ = 1 := fun k => by
    rw [hu]; simp only [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (hy0 k))
  have huN : ∀ k, u k ∈ N := fun k => N.smul_mem _ (hyN k)
  have huD : ∀ k, 𝒮.Dfs' f (x k) (u k) = 0 := fun k => by rw [hu]; simp [hyD k]
  -- `x_k → 0` in `E₁`
  have hx0 : Tendsto x atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => (hxr k).le.trans (min_le_left _ _)) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- the parameters `α_k` have a convergent subsequence
  have hα_mem : ∀ k, (u k).1 ∈ Metric.closedBall (0 : P) 1 := fun k => by
    rw [Metric.mem_closedBall, dist_zero_right]; exact (norm_fst_le (u k)).trans (hun k).le
  obtain ⟨α, -, φ₁, hφ₁, hα⟩ := (isCompact_closedBall (0 : P) 1).tendsto_subseq hα_mem
  -- the `W₁`-parts `Ds(x_k)u_k` are bounded, so `ι Ds(x_k)u_k` has a convergent subsequence
  have hDs_bdd : ∀ k, 𝒮.Ds (x k) (u k) ∈ Metric.closedBall (0 : W 1) c := fun k => by
    rw [Metric.mem_closedBall, dist_zero_right]
    have := hc (x k) (hxU k) ((hxr k).trans_le ((min_le_right _ _).trans (min_le_left _ _))) (u k)
    rwa [hun k, mul_one] at this
  obtain ⟨K, hK, hKsub⟩ := (W.toBase_succ_isCompactOperator 0).image_closedBall_subset_compact c
  have hw_mem : ∀ k, W.toBase 1 (𝒮.Ds (x (φ₁ k)) (u (φ₁ k))) ∈ K := fun k =>
    hKsub ⟨_, hDs_bdd (φ₁ k), rfl⟩
  obtain ⟨w₀, -, φ₂, hφ₂, hw⟩ := hK.tendsto_subseq hw_mem
  -- the combined subsequence
  set ψ : ℕ → ℕ := φ₁ ∘ φ₂ with hψ
  have hψm : StrictMono ψ := hφ₁.comp hφ₂
  have hxψ : Tendsto (x ∘ ψ) atTop (𝓝 0) := hx0.comp hψm.tendsto_atTop
  have hαψ : Tendsto (fun k => (u (ψ k)).1) atTop (𝓝 α) := hα.comp hφ₂.tendsto_atTop
  have hwψ : Tendsto (fun k => W.toBase 1 (𝒮.Ds (x (ψ k)) (u (ψ k)))) atTop (𝓝 w₀) := hw
  -- the equation for `ζ_k`
  have heq : ∀ k, (u k).2 = DB 𝒮.G B (x k) ((u k).1, 0) + DB 𝒮.G B (x k) (0, (u k).2) -
      W.toBase 1 (𝒮.Ds (x k) (u k)) := fun k => by
    have h1 := congrArg Prod.snd (huD k)
    rw [𝒮.Dfs'_eq hC hf (hxU k), add_apply, Prod.snd_add, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, Prod.snd_zero] at h1
    have h2 := DFunLike.congr_fun (𝒮.snd_Df_eq hC hf (hxU k)) (u k)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', sub_apply] at h2
    rw [h2] at h1
    have h3 : DB 𝒮.G B (x k) (u k) = DB 𝒮.G B (x k) ((u k).1, 0) + DB 𝒮.G B (x k) (0, (u k).2) := by
      rw [← map_add]; simp
    rw [h3, sub_add_eq_add_sub, sub_eq_zero] at h1
    exact eq_sub_of_add_eq h1
  -- `D₂B(x_k)ζ_k → 0`
  have hsmall : Tendsto (fun k => DB 𝒮.G B (x (ψ k)) (0, (u (ψ k)).2)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun k => 1 / ((ψ k : ℝ) + 1)) (fun k => ?_) ?_
    · have := h39 (ψ k) (x (ψ k)) (hxU (ψ k))
        ((hxr (ψ k)).trans_le ((min_le_right _ _).trans (min_le_right _ _))) (u (ψ k)).2
      refine this.trans ?_
      rw [mul_le_iff_le_one_right (by positivity)]
      exact (norm_snd_le (u (ψ k))).trans (hun (ψ k)).le
    · exact tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_natCast_atTop_atTop.comp
        hψm.tendsto_atTop)
  -- `D₁B(x_k)α_k → D₁B(0)α`
  have hD1 : Tendsto (fun k => DB 𝒮.G B (x (ψ k)) ((u (ψ k)).1, 0)) atTop (𝓝 (DB 𝒮.G B 0 (α, 0))) :=
    hDB.tendsto_deriv (fun k => hxU (ψ k)) (𝒮.G.zero_mem 1) hxψ (hαψ.prodMk_nhds tendsto_const_nhds)
  -- `ζ_k → z₀`
  set z₀ : W 0 := DB 𝒮.G B 0 (α, 0) - w₀ with hz₀
  have hζ : Tendsto (fun k => (u (ψ k)).2) atTop (𝓝 z₀) := by
    have : (fun k => (u (ψ k)).2) = fun k => DB 𝒮.G B (x (ψ k)) ((u (ψ k)).1, 0) +
        DB 𝒮.G B (x (ψ k)) (0, (u (ψ k)).2) - W.toBase 1 (𝒮.Ds (x (ψ k)) (u (ψ k))) :=
      funext fun k => heq (ψ k)
    rw [this]
    have := (hD1.add hsmall).sub hwψ
    rwa [add_zero] at this
  -- the limit `(α, z₀)`
  have huψ : Tendsto (u ∘ ψ) atTop (𝓝 (α, z₀)) := hαψ.prodMk_nhds hζ
  have hlimN : (α, z₀) ∈ N := hNc.mem_of_tendsto huψ (Eventually.of_forall fun k => huN (ψ k))
  have hlimn : ‖((α, z₀) : P × W 0)‖ = 1 := by
    have h1 : Tendsto (fun k => ‖u (ψ k)‖) atTop (𝓝 ‖((α, z₀) : P × W 0)‖) :=
      (continuous_norm.tendsto _).comp huψ
    have h2 : Tendsto (fun k => ‖u (ψ k)‖) atTop (𝓝 1) := by
      simp only [hun]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have hlimD : 𝒮.Dfs f (α, z₀) = 0 := by
    have h1 : Tendsto (fun k => 𝒮.Dfs' f (x (ψ k)) (u (ψ k))) atTop (𝓝 (𝒮.Dfs' f 0 (α, z₀))) :=
      hDfs.tendsto_deriv (fun k => hxU (ψ k)) (𝒮.G.zero_mem 1) hxψ huψ
    have h2 : Tendsto (fun k => 𝒮.Dfs' f (x (ψ k)) (u (ψ k))) atTop (𝓝 0) := by
      simp only [huD]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have hker : ((α, z₀) : P × W 0) ∈ LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) := hlimD
  have : ((α, z₀) : P × W 0) = 0 := (Submodule.disjoint_def.1 hN) _ hker hlimN
  rw [this, norm_zero] at hlimn
  exact zero_ne_one hlimn

/-! ### Corollary 3.5.3 (preprint 3.41) -/

/-- **Corollary 3.5.3 (preprint 3.41)**: let `f = h + s : U → ℝᴺ ⊕ W` with `h` a basic germ and `s` an sc⁺-germ,
`s(0) = 0` (the data `𝒮` of Theorem 3.4.2 (preprint 3.38) with `f := h`), and assume `D(h + s)(0)` is surjective.
Then there is `r > 0` such that every zero `x` of `h + s` in `U` with `|x|₀ < r` (1) lies on
level `1`, `x = ι(x₁)` with `x₁ ∈ U₁`, and (2) `D(h + s)(x₁) : E₀ → F₀` is a surjective Fredholm
operator of index `n − N`. -/
theorem corollary_3_5_3 (hsurj : Surjective (𝒮.Dfs f)) :
    ∃ r > 0, ∀ x ∈ 𝒮.G.U 0, ‖x‖ < r → 𝒮.fsum f x = 0 →
      ∃ x₁ : (ScBanach.paramProd P W) 1, (ScBanach.paramProd P W).toBase 1 x₁ = x ∧
        x₁ ∈ 𝒮.G.U 1 ∧ IsFredholm (𝒮.Dfs' f x₁) ∧
        fredholmIndex (𝒮.Dfs' f x₁) = Module.finrank ℝ P - Module.finrank ℝ Q ∧
        Surjective (𝒮.Dfs' f x₁) := by
  obtain ⟨hF0, hI0⟩ := 𝒮.isFredholm_Dfs hC hf
  -- the kernel `K₀ = ker D(f+s)(0)`, finite-dimensional with `dim K₀ = n − N`, and a closed
  -- complement `N`
  set K₀ := LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) with hK₀
  have hK₀fin : FiniteDimensional ℝ K₀ := hF0.finite_ker
  have hcoker : Module.finrank ℝ ((Q × W 0) ⧸ LinearMap.range (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) = 0 := by
    haveI : Subsingleton ((Q × W 0) ⧸ LinearMap.range (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0)) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      rw [(Submodule.Quotient.mk_eq_zero _).2 (hsurj a), (Submodule.Quotient.mk_eq_zero _).2 (hsurj b)]
    exact Module.finrank_zero_of_subsingleton
  have hdimK₀ : (Module.finrank ℝ K₀ : ℤ) = Module.finrank ℝ P - Module.finrank ℝ Q := by
    rw [← hI0]; unfold fredholmIndex linIndex; rw [hcoker]
    simp only [Nat.cast_zero, sub_zero]
    rfl
  obtain ⟨N, hNc, hN⟩ := (Submodule.ClosedComplemented.of_finiteDimensional K₀).exists_isClosed_isCompl
  -- the level-`1` radii
  obtain ⟨r₁, hr₁, hFred⟩ := 𝒮.exists_isFredholm_Dfs' hC hf
  obtain ⟨r₂, hr₂, hker⟩ := 𝒮.exists_ker_Dfs'_inf_eq_bot hC hf hNc hN.disjoint
  -- the lifts of Theorem 3.5.1 (preprint 3.40) (continuous at `0`)
  obtain ⟨τ, hτ, -, L, hL, hLc⟩ := hf.contraction.exists_lift hC.isClosed (𝒮.isScSmooth 0)
    𝒮.s_zero 1
  have h0sol : (0 : (ScBanach.paramProd P W) 0) ∈ solSet Ct B 𝒮.s τ :=
    hf.contraction.zero_mem_solSet 𝒮.s_zero hτ.le
  have hL0 : L 0 = 0 := (ScBanach.paramProd P W).toBase_injective 1 (by rw [(hL 0 h0sol).1, map_zero])
  have hcont := hLc 0 h0sol
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨r₀, hr₀, hr₀'⟩ := hcont (min r₁ r₂) (lt_min hr₁ hr₂)
  refine ⟨min r₀ τ, lt_min hr₀ hτ, fun x hxU hxr hx0 => ?_⟩
  -- `x` is a solution of `w = B(a, w) − s(a, w)`
  have hsol : x ∈ solSet Ct B 𝒮.s τ := by
    refine ⟨?_, (norm_fst_le x).trans (hxr.le.trans (min_le_right _ _)),
      (norm_snd_le x).trans (hxr.le.trans (min_le_right _ _)), ?_⟩
    · have := 𝒮.G.U_subset 0 hxU
      rw [ScBanach.paramProd_lvlSet] at this
      exact this.1
    · have h2 := congrArg Prod.snd hx0
      rw [fsum_apply, Prod.snd_add, hf.snd_eq _ hxU] at h2
      change x.2 - B x + W.toBase 1 (𝒮.s x) = 0 at h2
      rw [sub_add_eq_add_sub, sub_eq_zero] at h2
      exact eq_sub_of_add_eq h2
  obtain ⟨hLx, hLU, -⟩ := hL x hsol
  have hLsmall := hr₀' hsol (by rw [dist_zero_right]; exact hxr.trans_le (min_le_left _ _))
  rw [hL0, dist_zero_right] at hLsmall
  obtain ⟨hF1, hI1⟩ := hFred (L x) hLU (hLsmall.trans_le (min_le_left _ _))
  have hinj := hker (L x) hLU (hLsmall.trans_le (min_le_right _ _))
  refine ⟨L x, hLx, hLU, hF1, hI1, ?_⟩
  -- surjectivity: `dim ker D(f+s)(x) ≤ dim K₀ = n − N = ind D(f+s)(x)`
  have hdim : Module.finrank ℝ (LinearMap.ker (𝒮.Dfs' f (L x) : P × W 0 →ₗ[ℝ] Q × W 0)) ≤
      Module.finrank ℝ K₀ := by
    have hinj' : Injective ((K₀.projectionOnto N hN).comp
        (LinearMap.ker (𝒮.Dfs' f (L x) : P × W 0 →ₗ[ℝ] Q × W 0)).subtype) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_projectionOnto]
      rw [Submodule.eq_bot_iff]
      rintro ⟨y, hy⟩ hyN
      have hyN' : y ∈ N := hyN
      exact Subtype.ext (hinj y hyN' hy)
    exact LinearMap.finrank_le_finrank_of_injective hinj'
  have hfin : HasFiniteIndex (𝒮.Dfs' f (L x) : P × W 0 →ₗ[ℝ] Q × W 0) :=
    IsFredholm.hasFiniteIndex hF1
  have hle : (Module.finrank ℝ (LinearMap.ker (𝒮.Dfs' f (L x) : P × W 0 →ₗ[ℝ] Q × W 0)) : ℤ) ≤
      linIndex (𝒮.Dfs' f (L x) : P × W 0 →ₗ[ℝ] Q × W 0) := by
    have : linIndex (𝒮.Dfs' f (L x) : P × W 0 →ₗ[ℝ] Q × W 0) = fredholmIndex (𝒮.Dfs' f (L x)) := rfl
    rw [this, hI1, ← hdimK₀]
    exact_mod_cast hdim
  exact hfin.surjective_of_finrank_ker_le hle

end StabilityData

end Polyfold
