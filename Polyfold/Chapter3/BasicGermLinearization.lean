import Polyfold.Chapter3.StrongBundleSections
import Polyfold.Chapter1.FredholmIndex
import Polyfold.Chapter1.ExpositionLemmas

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
**Lemma 3.1.9 (preprint 3.9)** (at the base point) and **Proposition 3.1.10 (preprint 3.10)** (the linearization at `0` of a basic
germ plus an sc⁺-germ is an sc-Fredholm operator of index `n − N`).

# The linearization of a basic germ

## The text, paraphrased

(Lemma 3.1.9 (preprint 3.9)) For `B` as in Definition 3.1.7 (preprint 3.7) and every `ε > 0`, `m ≥ 0`: `|D₂B(a, w)ζ|_m ≤ ε|ζ|_m` for
`ζ ∈ W_m` and `(a, w) ∈ E_{m+1}` close to `(0, 0)` in `E_m`; in particular `D₂B(0, 0) = 0`.
(Proposition 3.1.10 (preprint 3.10)) Let `f : [0,∞)^k ⊕ ℝ^{n−k} ⊕ W → ℝᴺ ⊕ W` be an sc-smooth germ around `f(0) = 0`
of the form `f = h + s`, `h` a basic germ and `s` an sc⁺-germ.  Then `Df(0) : ℝⁿ ⊕ W → ℝᴺ ⊕ W` is
an sc-Fredholm operator of index `n − N`.  Moreover `Df(a, w) : ℝⁿ ⊕ W_m → ℝᴺ ⊕ W_m` is Fredholm of
index `n − N` for `(a, w) ∈ E_{m+1}` small in `E_m`.  Proof: `Df(0)(δa, δw) = δw − D₂B(0)δw −
D₁B(0)δa + (1 − P)Df(0)(δa, δw) + Ds(0)(δa, δw)`, `D₂B(0) = 0`, so `Df(0)` is an sc⁺-perturbation
of `(δa, δw) ↦ (0, δw)`, which is sc-Fredholm of index `n − N`; Proposition 1.1.11 (preprint 1.10).

## What is formalized

* `Polyfold.IsSc1GermWith.isScOperator_deriv_zero`: the derivative of an sc¹-germ at the smooth
  point `0` is an sc-operator (the remark after Proposition 1.2.1 (preprint 1.16), for germs).
* `Polyfold.IsSc0ContractionGerm.deriv_zero_snd` (**Lemma 3.1.9 (preprint 3.9) at `(0, 0)`**): `D₂B(0, 0) = 0`, by
  the difference quotient along `t ↦ (0, tζ)` and the density of `W₁` in `W₀`.
* `Polyfold.ScBanach.projWOp` (the operator `(δa, δw) ↦ (0, δw)` of (32)),
  `Polyfold.ScBanach.projWSplitting` (its sc-Fredholm splitting: kernel `ℝⁿ ⊕ 0`, cokernel
  `ℝᴺ ⊕ 0`), `Polyfold.ScBanach.scIndex_projWOp` (index `n − N`).
* `Polyfold.proposition_3_1_10` (**Proposition 3.1.10 (preprint 3.10), first statement**): for a basic germ `h`, an
  sc⁺-germ `s` (sc¹ into `(ℝᴺ ⊕ W)¹`) and `f = h + s` sc¹ with derivative `Df`, `Df(0)` is an
  sc-operator which is sc-Fredholm of index `dim ℝⁿ − dim ℝᴺ`.  The sc⁺-operator `S = Df(0) − T₀`
  is constructed level by level (`proposition_3_1_10_scPlus`).

## What the text leaves implicit, and the choices made (the findings)

* **The second statement of Proposition 3.1.10 (preprint 3.10)** (`Df(a, w)` Fredholm of index `n − N` on level
  `m` for `(a, w) ∈ E_{m+1}` small in `E_m`) is not in this file: it is proved, on every level
  `m`, in `BasicGermLinearizationLevel.lean` (`Polyfold.proposition_3_1_10_level`; both statements
  together: `Polyfold.proposition_3_1_10_full`; round-trip item V3.12).  It needs Lemma 3.1.9 (preprint 3.9) at
  points other than `(0, 0)`, on level `m` with an arbitrary `ε`
  (`IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le`, `SolutionLinearization.lean`).  The
  level-`0` case for points of `U₁` small on level `1` was proved earlier for the germs of
  Theorem 3.4.2 (preprint 3.38) (`StabilityData.exists_isFredholm_Dfs'`, used for Corollary 3.41).
* **`Df(0) − T₀` is sc⁺.**  The text says "`Df(0)` is an sc⁺-perturbation of (32)".  The
  verification: the `ℝᴺ`-component of `Df(0)` is sc⁺ because `ℝᴺ` has all levels equal; `D₁B(0)`
  is sc⁺ because `D₁B(0)δa = DB(0)(δa, 0)` with `(δa, 0)` a smooth point and `DB(0)` an sc-operator
  (so `D₁B(0)` takes values in `W_∞`); its level maps `E_m → W_{m+1}` are continuous because they
  factor through the continuous `DB(0)_{m+1} : E_{m+1} → W_{m+1}` and `δa ↦ (δa, 0)` (no finite
  dimensionality of `ℝⁿ` is needed for this); `Ds(0)` is sc⁺ because `s` is sc¹ into `W¹`, so
  `Ds(0)` is an sc-operator `E → (ℝᴺ ⊕ W)¹`; and `D₂B(0) = 0` by Lemma 3.1.9 (preprint 3.9).
* **The identity `Df(0) = (pr_{ℝᴺ} ∘ Df(0), δw − DB(0)(δa, δw)) + ι Ds(0)`** uses the uniqueness of
  derivatives at `0` within `U₁` (`U₁` is relatively open in the convex `C₁` with nonempty
  interior) and the density of `E₁` in `E₀`; the `W`-component of `h` is `w − B(a, w)` only on
  `U₀` (Definition 3.1.7 (preprint 3.7)), which is what `HasFDerivWithinAt.congr` needs.
* `f = h + s` is taken sc¹ with a given derivative family (the text: "an sc-smooth germ of the
  form `f = h + s`"); `s` is taken sc¹ into `(ℝᴺ ⊕ W)¹` (an sc⁺-germ is sc-smooth into `F¹`).
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

/-! ### The derivative of an sc¹-germ at `0` is an sc-operator -/

/-- The derivative `Df(0) : E₀ → F₀` of an sc¹-germ at the smooth point `0` is an sc-operator
(the remark after Proposition 1.2.1 (preprint 1.16), for germs): its level-`m` map is the fibre component of the
level-`m` tangent map at `(0, ·)`. -/
theorem IsSc1GermWith.isScOperator_deriv_zero {C : Set (E 0)} {G : ScNbhdGerm E C} {f : E 0 → F 0}
    {D : E 1 → E 0 →L[ℝ] F 0} (h : IsSc1GermWith G f D) : IsScOperator (D 0) := by
  intro m
  have hmem : ∀ v : E m, ((0, v) : E.tangent m) ∈ G.tangent.U m := fun v =>
    ⟨G.zero_mem (m + 1), mem_univ _⟩
  set Tm : E m → F m := fun v => (levelMap (tangentMapWith f D) m ((0, v) : E.tangent m)).2
    with hTm
  have hTm' : ∀ v, F.toBase m (Tm v) = D 0 (E.toBase m v) := by
    intro v
    have := congrArg Prod.snd (h.tangent_isSc0.toBase_levelMap (hmem v))
    rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase] at this
    change F.toBase m (Tm v) = D (E.shift.toBase m 0) (E.toBase m v) at this
    rw [this, map_zero]
  have hcont : Continuous Tm := by
    have := (h.tangent_isSc0.continuousOn m).comp_continuous
      (f := fun v : E m => ((0, v) : E.tangent m)) (by fun_prop) hmem
    exact continuous_snd.comp this
  refine ⟨{ toFun := Tm
            map_add' := fun v w => F.toBase_injective m (by
              rw [map_add, hTm', hTm', hTm', map_add, map_add])
            map_smul' := fun a v => F.toBase_injective m (by
              rw [map_smul, hTm', hTm', map_smul, map_smul]; rfl)
            cont := hcont }, hTm'⟩

/-! ### Lemma 3.1.9 (preprint 3.9) at the base point -/

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {W : ScBanach}
  {Ct : Set P} {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)}

/-- **Lemma 3.1.9 (preprint 3.9) at `(0, 0)`**: for an sc⁰-contraction germ `B` (Definition 3.1.7 (preprint 3.7)/3.28) which is sc¹
with derivative `DB`, `D₂B(0, 0) = 0`: the difference quotient of `t ↦ B(0, tζ)` is bounded by
`ε|ζ|` for every `ε`, first for `ζ ∈ W₁`, then by density for `ζ ∈ W₀`. -/
theorem IsSc0ContractionGerm.deriv_zero_snd {Bc : P × W 0 → W 0} (hB : IsSc0ContractionGerm Ct G Bc)
    {L₀ : (ScBanach.paramProd P W) 0 →L[ℝ] W 0}
    (hD : HasFDerivWithinAt (Bc ∘ (ScBanach.paramProd P W).toBase 1)
      (L₀.comp ((ScBanach.paramProd P W).toBase 1)) (G.U 1) 0) (ζ : W 0) : L₀ ((0 : P), ζ) = 0 := by
  set L : W 0 →L[ℝ] W 0 := L₀.comp (ContinuousLinearMap.inr ℝ P (W 0)) with hL
  have h0Ct : (0 : P) ∈ Ct := (G.U_subset 0 (G.zero_mem 0)).1
  -- the claim on the dense subspace `W₁`
  have hL1 : ∀ ζ₁ : W 1, L (W.toBase 1 ζ₁) = 0 := by
    intro ζ₁
    set ζ := W.toBase 1 ζ₁ with hζ
    -- the curve `γ(t) = (0, tζ₁)` in `E₁`
    set γ : ℝ → (ScBanach.paramProd P W) 1 := fun t => ((0 : P), t • ζ₁) with hγ
    have hγd : HasDerivAt γ ((0 : P), ζ₁) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • ζ₁) ((1 : ℝ) • ζ₁) 0 := (hasDerivAt_id' 0).smul_const ζ₁
      rw [one_smul] at h1
      exact (hasDerivAt_const (0 : ℝ) (0 : P)).prodMk h1
    obtain ⟨O, hO, hOeq⟩ := G.relOpen 1
    have hγc : Continuous γ := by fun_prop
    set s : Set ℝ := γ ⁻¹' O with hs
    have hs_open : IsOpen s := hO.preimage hγc
    have h0s : (0 : ℝ) ∈ s := by
      change γ 0 ∈ O
      have : γ 0 = 0 := by simp [hγ]
      rw [this]
      have := G.zero_mem 1
      rw [hOeq] at this; exact this.1
    have hmaps : MapsTo γ s (G.U 1) := by
      intro t ht
      rw [hOeq]
      refine ⟨ht, ?_⟩
      rw [ScBanach.mem_lvlSet, ScBanach.paramProd_toBase]
      exact ⟨h0Ct, mem_univ _⟩
    -- the derivative of `t ↦ B(0, tζ)` at `0` is `D₂B(0, 0)ζ`
    have hcomp : HasDerivWithinAt (fun t => Bc ((ScBanach.paramProd P W).toBase 1 (γ t)))
        ((L₀.comp ((ScBanach.paramProd P W).toBase 1)) ((0 : P), ζ₁)) s 0 := by
      refine hD.comp_hasDerivWithinAt_of_eq 0 hγd.hasDerivWithinAt hmaps ?_
      simp [hγ, Prod.mk_zero_zero]
    have hval0 : ((ScBanach.paramProd P W).toBase 1) ((0 : P), ζ₁) = ((0 : P), ζ) := by
      rw [ScBanach.paramProd_toBase]
    have hval : (L₀.comp ((ScBanach.paramProd P W).toBase 1)) ((0 : P), ζ₁) = L ζ := by
      rw [ContinuousLinearMap.comp_apply, hval0]; rfl
    rw [hval] at hcomp
    -- the slope is bounded by `ε|ζ|`
    have hbound : ∀ ε > 0, ‖L ζ‖ ≤ ε * ‖ζ‖ := by
      intro ε hε
      obtain ⟨r, hr, hcontr⟩ := hB.contraction ε hε 0
      have hlim := hasDerivWithinAt_iff_tendsto_slope.1 hcomp
      -- `𝓝[s \ {0}] 0` is the punctured neighbourhood filter, nontrivial
      have hsnhds : s ∈ 𝓝 (0 : ℝ) := hs_open.mem_nhds h0s
      have hfilt : 𝓝[s \ {0}] (0 : ℝ) = 𝓝[≠] 0 := by
        rw [Set.sdiff_eq, inter_comm, nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hsnhds)]
      have : NeBot (𝓝[s \ {0}] (0 : ℝ)) := by rw [hfilt]; exact NormedField.nhdsNE_neBot 0
      refine le_of_tendsto hlim.norm ?_
      have hev : ∀ᶠ t in 𝓝[s \ {0}] (0 : ℝ), ‖t‖ * ‖ζ‖ < r := by
        have : Tendsto (fun t : ℝ => ‖t‖ * ‖ζ‖) (𝓝[s \ {0}] 0) (𝓝 (‖(0 : ℝ)‖ * ‖ζ‖)) :=
          ((continuous_norm.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
        rw [norm_zero, zero_mul] at this
        exact this.eventually (gt_mem_nhds hr)
      filter_upwards [hev, self_mem_nhdsWithin] with t ht hts
      have ht0 : t ≠ 0 := hts.2
      -- `|B(0, tζ) − B(0, 0)| ≤ ε|tζ|`
      have hB1 := hcontr 0 h0Ct (by rw [norm_zero]; exact hr) (t • ζ) 0
        (by rw [norm_smul]; exact ht) (by rw [norm_zero]; exact hr)
      rw [levelB_zero, levelB_zero, sub_zero, norm_smul] at hB1
      have hγ0 : (ScBanach.paramProd P W).toBase 1 (γ 0) = ((0 : P), (0 : W 0)) := by
        rw [ScBanach.paramProd_toBase]; simp [hγ]
      have hγt : (ScBanach.paramProd P W).toBase 1 (γ t) = ((0 : P), t • ζ) := by
        rw [ScBanach.paramProd_toBase]; simp [hγ, hζ]
      rw [slope_def_module, sub_zero, hγ0, hγt, norm_smul, norm_inv]
      have hB2 : ‖Bc ((0 : P), t • ζ) - Bc ((0 : P), (0 : W 0))‖ ≤ ε * (‖t‖ * ‖ζ‖) := hB1.2
      have hpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
      calc ‖t‖⁻¹ * ‖Bc ((0 : P), t • ζ) - Bc ((0 : P), (0 : W 0))‖
          ≤ ‖t‖⁻¹ * (ε * (‖t‖ * ‖ζ‖)) := by gcongr
        _ = ε * ‖ζ‖ := by field_simp
    -- hence `L ζ = 0`
    by_contra hne
    have hpos : 0 < ‖L ζ‖ := norm_pos_iff.2 hne
    have := hbound (‖L ζ‖ / (2 * (‖ζ‖ + 1))) (by positivity)
    have h2 : ‖L ζ‖ / (2 * (‖ζ‖ + 1)) * ‖ζ‖ < ‖L ζ‖ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg ζ]
    linarith
  -- density of `W₁`
  have hdense : DenseRange (W.toBase 1) := W.denseRange_incl 0
  have hLz : (⇑L : W 0 → W 0) = fun _ => 0 := by
    refine hdense.equalizer L.continuous continuous_zero (funext fun ζ₁ => ?_)
    simp only [Function.comp_apply]
    exact hL1 ζ₁
  have : L ζ = 0 := congrFun hLz ζ
  simpa [hL] using this

/-! ### The operator `(δa, δw) ↦ (0, δw)` and its sc-Fredholm splitting -/

namespace ScBanach

variable (P) (W) {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

variable (Q) in
/-- The operator (32) of the text, `(δa, δw) ↦ (0, δw) : ℝⁿ ⊕ W → ℝᴺ ⊕ W`, as an sc-operator. -/
def projWOp : ScOperator (paramProd P W) (paramProd Q W) where
  lvl m := (ContinuousLinearMap.inr ℝ Q (W m)).comp (ContinuousLinearMap.snd ℝ P (W m))
  incl_comm m x := by
    change (paramProd Q W).incl m ((0 : Q), x.2) = ((0 : Q), ((paramProd P W).incl m x).2)
    rw [paramProd_incl, paramProd_incl]

variable (Q) in
@[simp] lemma projWOp_apply (m : ℕ) (x : (paramProd P W) m) :
    projWOp P W Q m x = ((0 : Q), x.2) := rfl

/-- The projection `(a, w) ↦ (a, 0)` of `ℝⁿ ⊕ W`, an idempotent sc-operator. -/
def projParamOp : ScOperator (paramProd P W) (paramProd P W) where
  lvl m := (ContinuousLinearMap.inl ℝ P (W m)).comp (ContinuousLinearMap.fst ℝ P (W m))
  incl_comm m x := by
    change (paramProd P W).incl m (x.1, (0 : W (m + 1))) = (((paramProd P W).incl m x).1, (0 : W m))
    rw [paramProd_incl, paramProd_incl, map_zero]

@[simp] lemma projParamOp_apply (m : ℕ) (x : (paramProd P W) m) :
    projParamOp P W m x = (x.1, (0 : W m)) := rfl

lemma projParamOp_idem (x : (paramProd P W) 0) :
    projParamOp P W 0 (projParamOp P W 0 x) = projParamOp P W 0 x := rfl

/-- The kernel `ℝⁿ ⊕ 0` of (32) is the range of `inl : ℝⁿ → ℝⁿ ⊕ W`, finite-dimensional. -/
lemma range_projParamOp :
    LinearMap.range (projParamOp P W 0 : (paramProd P W) 0 →ₗ[ℝ] (paramProd P W) 0) =
      LinearMap.range (LinearMap.inl ℝ P (W 0)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y.1, rfl⟩
  · rintro ⟨a, rfl⟩; exact ⟨(a, 0), rfl⟩

variable (Q) in
/-- **The sc-Fredholm splitting of (32)**: `K = ℝⁿ ⊕ 0`, `X = 0 ⊕ W`, `C = ℝᴺ ⊕ 0`, `Y = 0 ⊕ W`. -/
def projWSplitting : ScFredholmSplitting (projWOp P W Q) where
  K := LinearMap.range (projParamOp P W 0 : (paramProd P W) 0 →ₗ[ℝ] (paramProd P W) 0)
  X := LinearMap.ker (projParamOp P W 0 : (paramProd P W) 0 →ₗ[ℝ] (paramProd P W) 0)
  C := LinearMap.range (projParamOp Q W 0 : (paramProd Q W) 0 →ₗ[ℝ] (paramProd Q W) 0)
  Y := LinearMap.ker (projParamOp Q W 0 : (paramProd Q W) 0 →ₗ[ℝ] (paramProd Q W) 0)
  splitE := isScSplitting_of_idem (projParamOp P W) (projParamOp_idem P W)
  splitF := isScSplitting_of_idem (projParamOp Q W) (projParamOp_idem Q W)
  ker_eq := by
    ext x
    simp only [LinearMap.mem_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨y, hy⟩
      rw [← hy]; rfl
    · intro h
      exact ⟨x, Prod.ext rfl (congrArg Prod.snd h).symm⟩
  finite_K := by
    rw [range_projParamOp]
    exact LinearMap.finiteDimensional_range _
  finite_C := by
    rw [range_projParamOp]
    exact LinearMap.finiteDimensional_range _
  range_eq := by
    ext y
    simp only [LinearMap.mem_ker, LinearMap.mem_range, ContinuousLinearMap.coe_coe]
    constructor
    · intro h
      exact ⟨((0 : P), y.2), Prod.ext (congrArg Prod.fst h).symm rfl⟩
    · rintro ⟨x, hx⟩
      rw [← hx]; rfl
  bijOn m := by
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
    · change projParamOp Q W 0 ((paramProd Q W).toBase m _) = 0
      rw [← (projParamOp Q W).toBase_comm, projWOp_apply, projParamOp_apply]
      exact map_zero _
    · have hx0 : x.1 = 0 := by
        have : projParamOp P W 0 ((paramProd P W).toBase m x) = 0 := hx
        rw [← (projParamOp P W).toBase_comm, projParamOp_apply, paramProd_toBase] at this
        exact (Prod.mk.inj this).1
      have hy0 : y.1 = 0 := by
        have : projParamOp P W 0 ((paramProd P W).toBase m y) = 0 := hy
        rw [← (projParamOp P W).toBase_comm, projParamOp_apply, paramProd_toBase] at this
        exact (Prod.mk.inj this).1
      have h2 : x.2 = y.2 := (Prod.mk.inj hxy).2
      exact Prod.ext (hx0.trans hy0.symm) h2
    · have hy0 : y.1 = 0 := by
        have : projParamOp Q W 0 ((paramProd Q W).toBase m y) = 0 := hy
        rw [← (projParamOp Q W).toBase_comm, projParamOp_apply, paramProd_toBase] at this
        exact (Prod.mk.inj this).1
      refine ⟨((0 : P), y.2), ?_, Prod.ext hy0.symm rfl⟩
      change projParamOp P W 0 ((paramProd P W).toBase m ((0 : P), y.2)) = 0
      rw [← (projParamOp P W).toBase_comm, projParamOp_apply]
      exact map_zero _

variable (Q) in
/-- (32) is sc-Fredholm. -/
theorem isScFredholm_projWOp : IsScFredholm (projWOp P W Q) := ⟨projWSplitting P W Q⟩

variable (Q) in
/-- **The index of (32) is `n − N`**: `dim(ℝⁿ ⊕ 0) − dim(ℝᴺ ⊕ 0)`. -/
theorem scIndex_projWOp : scIndex (projWOp P W Q) = finrank ℝ P - finrank ℝ Q := by
  rw [← (projWSplitting P W Q).index_eq]
  have hK : (projWSplitting P W Q).K =
      LinearMap.range (projParamOp P W 0 : (paramProd P W) 0 →ₗ[ℝ] (paramProd P W) 0) := rfl
  have hC : (projWSplitting P W Q).C =
      LinearMap.range (projParamOp Q W 0 : (paramProd Q W) 0 →ₗ[ℝ] (paramProd Q W) 0) := rfl
  unfold ScFredholmSplitting.index
  rw [hK, hC, range_projParamOp, range_projParamOp,
    LinearMap.finrank_range_of_inj LinearMap.inl_injective,
    LinearMap.finrank_range_of_inj LinearMap.inl_injective]

end ScBanach

/-! ### Proposition 3.1.10 (preprint 3.10) -/

section Prop310

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

local notation "E'" => ScBanach.paramProd P W
local notation "F'" => ScBanach.paramProd Q W

/-- **The sc⁺-operator `S = Df(0) − T₀` of the proof of Proposition 3.1.10 (preprint 3.10)**, constructed level by
level from the sc-operators `Df(0)`, `Dh(0)` and `Ds(0)`: `S(δa, δw) = (pr_{ℝᴺ} Df(0)(δa, δw),
pr_W Dh(0)(δa, 0) + pr_W ι Ds(0)(δa, δw))` (where `pr_W Dh(0)(δa, 0) = −D₁B(0)δa`).  Returned with
its defining identity on level `0`. -/
theorem proposition_3_1_10_scPlus {DF : (E') 1 → (E') 0 →L[ℝ] (F') 0} (hDF : IsScOperator (DF 0))
    {Dh : (E') 1 → (E') 0 →L[ℝ] (F') 0} (hDh : IsScOperator (Dh 0))
    {Ds : (E') 1 → (E') 0 →L[ℝ] (F').shift 0} (hDs : IsScOperator (Ds 0)) :
    ∃ S : ScPlus (E') (F'), ∀ x : (E') 0,
      (F').toBase 1 (S 0 x) = ((DF 0 x).1, (Dh 0 (x.1, (0 : W 0))).2 + ((F').toBase 1 (Ds 0 x)).2) := by
  set DFop := hDF.toScOperator with hDFop
  set Dhop := hDh.toScOperator with hDhop
  set Dsop := hDs.toScOperator with hDsop
  -- the `ℝᴺ`-component
  let A₁ : ScOperator (E') (ScBanach.const Q) :=
    { lvl := fun m => (ContinuousLinearMap.fst ℝ Q (W m)).comp (DFop m)
      incl_comm := fun m x => by
        change (DFop (m + 1) x).1 = (DFop m ((E').incl m x)).1
        rw [← DFop.incl_comm m x]; rfl }
  -- the `W`-component, into `W¹`
  let A₂ : ScOperator (E') W.shift :=
    { lvl := fun m => (ContinuousLinearMap.snd ℝ Q (W (m + 1))).comp ((Dhop (m + 1)).comp
          ((ContinuousLinearMap.inl ℝ P (W (m + 1))).comp (ContinuousLinearMap.fst ℝ P (W m)))) +
          (ContinuousLinearMap.snd ℝ Q (W (m + 1))).comp (Dsop m)
      incl_comm := fun m x => by
        change W.incl (m + 1) ((Dhop (m + 2) (x.1, 0)).2 + (Dsop (m + 1) x).2) =
          (Dhop (m + 1) (x.1, 0)).2 + (Dsop m ((E').incl m x)).2
        rw [map_add, ← Dsop.incl_comm m]
        have h1 : W.incl (m + 1) (Dhop (m + 2) (x.1, 0)).2 = (Dhop (m + 1) (x.1, 0)).2 := by
          have := congrArg Prod.snd (Dhop.incl_comm (m + 1) (x.1, 0))
          rw [ScBanach.paramProd_incl, ScBanach.paramProd_incl, map_zero] at this
          exact this
        rw [h1]; rfl }
  refine ⟨{ lvl := fun m => (A₁ m).prod (A₂ m)
            incl_comm := fun m x => Prod.ext (A₁.incl_comm m x) (A₂.incl_comm m x) }, fun x => ?_⟩
  change ((F').toBase 1 (A₁ 0 x, A₂ 0 x)) = _
  rw [ScBanach.paramProd_toBase]
  refine Prod.ext ?_ ?_
  · change (DFop 0 x).1 = (DF 0 x).1
    rw [hDFop, hDF.toScOperator_zero]
  · change W.toBase 1 ((Dhop 1 (x.1, 0)).2 + (Dsop 0 x).2) = _
    rw [map_add, hDsop, hDs.toScOperator_zero]
    have h1 : W.toBase 1 (Dhop 1 (x.1, 0)).2 = (Dh 0 (x.1, (0 : W 0))).2 := by
      have := congrArg Prod.snd (Dhop.toBase_comm 1 (x.1, 0))
      rw [ScBanach.paramProd_toBase, ScBanach.paramProd_toBase, map_zero, hDhop,
        hDh.toScOperator_zero] at this
      exact this
    rw [h1, ScBanach.paramProd_toBase]

/-- Two bounded operators on `E₀` agreeing on the dense subspace `E₁` are equal. -/
theorem ContinuousLinearMap.ext_of_comp_toBase_one {F₀ : ScBanach} {A B : E 0 →L[ℝ] F₀ 0}
    (h : A.comp (E.toBase 1) = B.comp (E.toBase 1)) : A = B := by
  refine ContinuousLinearMap.ext fun y => congrFun ?_ y
  refine (E.denseRange_incl 0).equalizer A.continuous B.continuous (funext fun x => ?_)
  exact congrArg (fun T : E 1 →L[ℝ] F₀ 0 => T x) h

/-- **Proposition 3.1.10 (preprint 3.10), first statement**: let `h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W` be a basic germ
(Definition 3.1.7 (preprint 3.7)), `s` an sc⁺-germ (sc¹ into `(ℝᴺ ⊕ W)¹`, derivative `Ds`) and `f = h + s` sc¹
with derivative `Df`.  Then `Df(0) : ℝⁿ ⊕ W → ℝᴺ ⊕ W` is an sc-operator which is sc-Fredholm of
index `n − N = dim ℝⁿ − dim ℝᴺ`: it is the sc⁺-perturbation `T₀ + S` of `T₀(δa, δw) = (0, δw)`
(Lemma 3.1.9 (preprint 3.9), `D₂B(0) = 0`), and Proposition 1.1.11 (preprint 1.10) applies. -/
theorem proposition_3_1_10 (hC : IsPartialQuadrant (ScBanach.const P) Ct) {h : P × W 0 → Q × W 0}
    {Bc : P × W 0 → W 0} (hh : IsBasicGerm Ct G h Bc) {s : P × W 0 → Q × W 1}
    {Ds : (E') 1 → (E') 0 →L[ℝ] (F').shift 0} (hs : IsSc1GermWith (F := (F').shift) G s Ds)
    {DF : (E') 1 → (E') 0 →L[ℝ] (F') 0}
    (hF : IsSc1GermWith G (fun x => h x + (F').toBase 1 (s x)) DF) :
    ∃ hop : IsScOperator (DF 0), IsScFredholm hop.toScOperator ∧
      scIndex hop.toScOperator = finrank ℝ P - finrank ℝ Q := by
  have hCq : IsQuadrantLike (E') (Ct ×ˢ univ) := (hC.prod_univ W).isQuadrantLike
  have hop : IsScOperator (DF 0) := hF.isScOperator_deriv_zero
  have h01 : (0 : (E') 1) ∈ G.U 1 := G.zero_mem 1
  have huniq := G.uniqueDiffWithinAt hCq 1 h01
  -- the derivative of `h` at `0`
  have hh1 : IsSc1GermWith (F := F') G h (scDerivGerm (F := F') G h) :=
    (hh.isScSmooth 1).1.isSc1GermWith_scDerivGerm
  set Dh := scDerivGerm (F := F') G h with hDh
  have hDhop : IsScOperator (Dh 0) := hh1.isScOperator_deriv_zero
  have hDsop : IsScOperator (Ds 0) := hs.isScOperator_deriv_zero
  set ι : (F') 1 →L[ℝ] (F') 0 := (F').toBase 1 with hι
  -- `Df(0) = Dh(0) + ι Ds(0)`
  have hsum : DF 0 = Dh 0 + ι.comp (Ds 0) := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one
    have h1 := hh1.hasFDerivWithinAt 0 h01
    have h2 := ι.hasFDerivAt.comp_hasFDerivWithinAt (0 : (E') 1) (hs.hasFDerivWithinAt 0 h01)
    have h3 := h1.add h2
    have h4 := hF.hasFDerivWithinAt 0 h01
    have := huniq.eq h4 h3
    rw [this]; rfl
  -- Lemma 3.1.9 (preprint 3.9): `(Dh(0)(0, ζ))₂ = ζ`
  have hDh2 : ∀ ζ : W 0, (Dh 0 ((0 : P), ζ)).2 = ζ := by
    intro ζ
    set DB₀ : (E') 0 →L[ℝ] W 0 :=
      ContinuousLinearMap.snd ℝ P (W 0) - (ContinuousLinearMap.snd ℝ Q (W 0)).comp (Dh 0) with hDB₀
    have hderiv : HasFDerivWithinAt (Bc ∘ (E').toBase 1) (DB₀.comp ((E').toBase 1)) (G.U 1) 0 := by
      have h1 := (ContinuousLinearMap.snd ℝ Q (W 0)).hasFDerivAt.comp_hasFDerivWithinAt
        (0 : (E') 1) (hh1.hasFDerivWithinAt 0 h01)
      have h2 : HasFDerivWithinAt (fun x : (E') 1 => ((E').toBase 1 x).2)
          ((ContinuousLinearMap.snd ℝ P (W 0)).comp ((E').toBase 1)) (G.U 1) 0 :=
        ((ContinuousLinearMap.snd ℝ P (W 0)).comp ((E').toBase 1)).hasFDerivAt.hasFDerivWithinAt
      have h3 := h2.sub h1
      refine (h3.congr ?_ ?_)
      · intro x hx
        have := hh.snd_eq _ (G.toBase_mem hx)
        show Bc ((E').toBase 1 x) = ((E').toBase 1 x).2 - (h ((E').toBase 1 x)).2
        rw [this]; abel
      · have := hh.snd_eq _ (G.toBase_mem h01)
        show Bc ((E').toBase 1 0) = ((E').toBase 1 0).2 - (h ((E').toBase 1 0)).2
        rw [this]; abel
    have := hh.contraction.deriv_zero_snd hderiv ζ
    have h' : ζ - (Dh 0 ((0 : P), ζ)).2 = 0 := this
    exact (sub_eq_zero.1 h').symm
  -- the sc⁺-operator `S` and the identity `Df(0) = T₀ + S`
  obtain ⟨S, hS⟩ := proposition_3_1_10_scPlus (P := P) (W := W) hop hDhop hDsop
  have hTS : hop.toScOperator = ScBanach.projWOp P W Q + S.toScOperator := by
    apply ScOperator.ext_base
    refine ContinuousLinearMap.ext fun x => ?_
    rw [hop.toScOperator_zero, ScOperator.add_apply, ScPlus.toScOperator_apply,
      ScBanach.projWOp_apply]
    change DF 0 x = ((0 : Q), x.2) + (F').toBase 1 (S 0 x)
    rw [hS x, hsum]
    have hDhx : (Dh 0 x).2 = (Dh 0 (x.1, (0 : W 0))).2 + x.2 := by
      have hx : x = (x.1, (0 : W 0)) + ((0 : P), x.2) := by ext <;> simp
      conv_lhs => rw [hx]
      rw [map_add, Prod.snd_add, hDh2]
    refine Prod.ext ?_ ?_
    · show ((Dh 0 + ι.comp (Ds 0)) x).1 = (0 : Q) + ((Dh 0 + ι.comp (Ds 0)) x).1
      rw [zero_add]
    · show ((Dh 0 + ι.comp (Ds 0)) x).2 =
        x.2 + ((Dh 0 (x.1, (0 : W 0))).2 + (ι (Ds 0 x)).2)
      rw [add_apply, Prod.snd_add, hDhx]
      change (Dh 0 (x.1, (0 : W 0))).2 + x.2 + (ι (Ds 0 x)).2 = _
      abel
  refine ⟨hop, ?_, ?_⟩
  · rw [hTS]; exact proposition_1_1_11_preprint (ScBanach.isScFredholm_projWOp P W Q) S
  · rw [hTS, proposition_1_1_11_index (ScBanach.isScFredholm_projWOp P W Q) S,
      ScBanach.scIndex_projWOp]

end Prop310

end Polyfold
