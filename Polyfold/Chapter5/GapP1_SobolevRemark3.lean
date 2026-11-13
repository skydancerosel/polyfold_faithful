import Polyfold.Chapter5.GapP1_SobolevRemark2
import Polyfold.Chapter1.GapP1_Sobolev13
import Polyfold.Chapter5.BumpWeakPointwise

/-!
# The remark after Theorem 5.5.5 (2021, pp. 230–231): consequences for sc-structures

Hofer–Wysocki–Zehnder, 2021 §5.5, the remark after Theorem 5.5.5 (preprint pp. 193–194), its last
part: "if `Ω` is a bounded domain in `ℝⁿ` and `E = W^{1,4}(Ω)` is equipped with the sc-structure
`E_m = W^{1+m,4}(Ω)`, then `E` admits sc-smooth bump functions"; for `E = W^{1,3/2}(Ω)` with
`E_m = W^{1+m,3/2}(Ω)` the straightforward bump function is sc¹.  The closing question (is there an
sc-smooth bump on `W^{1,3/2}(Ω)`?) is a question, not a claim.

## What is formalized

* `scPolyfold_admitsBumpFunctions`: an sc-Banach space `E` (as the M-polyfold `scPolyfold E`) whose
  `0`-level has a `C^∞` bump admits sc-smooth bump functions.
* **The Hilbert case `p = 2`: Example 1.1.3.**  Every level `H^{m,δ}(ℝ × S¹)` of the sc-structure
  of Example 1.1.3 has the norm `‖u‖² = ∑_{a+b ≤ m} ‖e^{δ|s|}∂^a_s∂^b_t u‖²_{L²}`, which is `C^∞`
  (`contDiff_norm_sq_H`), and every local model on `example_1_1_3` has the sc-smooth bump function
  property (`example_1_1_3_hasBumpProperty`); M-polyfold forms `example_1_1_3_scPolyfold`
  and `example_1_1_3_admitsBumpFunctions`.
* **`W^{1,p}(Ω)` with `E_m = W^{1+m,p}(Ω)`**, `p` even, in particular `p = 4`
  (`remark_5_5_5_W14`): every sc-Banach space `E` with `E₀ ≅ W^{1,p}(Ω)` (any continuous linear
  isomorphism; the higher levels are arbitrary) admits sc-smooth bump functions, its local models
  have the sc-smooth bump property, and M-polyfolds modelled on such spaces admit sc-smooth bump
  functions.
* **`W^{1,3/2}(Ω)`** (`remark_5_5_5_W1_3_2`): for every sc-Banach space `E` with
  `E₀ ≅ W^{1,3/2}(Ω)`, `β(‖x‖^{3/2})` is an sc¹ function on `E`, not identically zero, with bounded
  support in `E₀`.
* **The sc-structure `E_m = W^{1+m,p}(Ω)` itself** (`sobolevSc`): built from the inclusions
  `inclW` given the two analytic facts that make it an sc-structure, the compactness of
  `W^{m+2,p}(Ω) → W^{m+1,p}(Ω)` (Rellich–Kondrachov) and the density of `E_∞`; its `0`-level is
  `W^{1,p}(Ω)` by definition (`sobolevSc_admitsBumpFunctions`, `sobolevSc_hasBumpProperty`,
  `sobolevSc_exists_sc1_bump`).
  These two facts are not formalized for a general bounded domain; they hold trivially for
  `Ω = ∅` (`sobolevSc_hyps_empty`), which shows the hypotheses consistent, and they are where the
  boundedness and regularity of `Ω` enter.  They are proved for the open unit cube `(0,1)` in
  `ℝ¹` and every `p > 1` in `GapP1_SobolevCube1–5.lean` (`SobolevCube.cubeSc`,
  `SobolevCube.remark_5_5_5_W14_cube`); cubes in `ℝⁿ`, `n ≥ 2`, and other bounded domains are not
  done.  The bump statements do not need them: they use only `E₀`.
-/

open MeasureTheory Set Function
open scoped ENNReal ContDiff

noncomputable section

namespace Polyfold

namespace SobolevRemark

/-- **An sc-Banach space whose `0`-level has a `C^∞` bump admits sc-smooth bump functions**, as an
M-polyfold (`scPolyfold E`, Definition 5.3.1). -/
theorem scPolyfold_admitsBumpFunctions (E : ScBanach) (h : HasContDiffBump (E 0) ⊤) :
    (scPolyfold E).AdmitsBumpFunctions :=
  MPolyfold.admitsBumpFunctions_of_hasContDiffBump fun _ =>
    ⟨scChart E, isChart_scChart E, mem_univ _, h⟩

/-! ### Example 1.1.3, the Hilbert case `p = 2` -/

section Example113

open GapP1Sobolev

/-- **The norm of every level `H^{m,δ}(ℝ × S¹)` of Example 1.1.3 is smooth**:
`‖u‖² = ∑_{a+b ≤ m} ‖e^{δ|s|}∂^a_s∂^b_t u‖²_{L²}` is `C^∞` (the case `p = 2` of the remark). -/
theorem contDiff_norm_sq_H (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ContDiff ℝ ∞ (fun u : H m hδ => ‖u‖ ^ 2) := by
  have e : (fun u : H m hδ => ‖u‖ ^ 2) = fun u => ∑ q : idx m, ‖wdvCLM m hδ q u‖ ^ 2 :=
    funext fun u => norm_sq_H u
  rw [e]
  exact ContDiff.sum fun q _ => (contDiff_norm_sq ℝ).comp (wdvCLM m hδ q).contDiff

/-- Every level `H^{m,δ}(ℝ × S¹)` admits a `C^∞`-bump function. -/
theorem hasContDiffBump_H (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : HasContDiffBump (H m hδ) ⊤ := by
  refine hasContDiffBump_of_rpow two_pos ?_
  have e : (fun u : H m hδ => ‖u‖ ^ (2 : ℝ)) = fun u => ‖u‖ ^ 2 :=
    funext fun u => Real.rpow_two _
  rw [e]
  exact contDiff_norm_sq_H m hδ

/-- **Example 1.1.3 admits sc-smooth bump functions**: every local model `(O, C, E)` with
`E = example_1_1_3 δ` (the sc-structure `E_m = H^{m,δ_m}(ℝ × S¹)`) has the sc-smooth bump
function property (Definition 5.5.6). -/
theorem example_1_1_3_hasBumpProperty (δ : ℕ → ℝ) (h0 : δ 0 = 0) (hmono : StrictMono δ)
    (M : LocalModel) (hM : M.E = example_1_1_3 δ h0 hmono) : M.HasBumpProperty := by
  obtain ⟨E, C, O, hR⟩ := M
  subst hM
  exact LocalModel.hasBumpProperty_of_hasContDiffBump _
    (hasContDiffBump_H 0 (nonneg_of_strictMono h0 hmono 0))

/-- **The sc-Banach space of Example 1.1.3 admits sc-smooth bump functions** (as an M-polyfold). -/
theorem example_1_1_3_scPolyfold (δ : ℕ → ℝ) (h0 : δ 0 = 0) (hmono : StrictMono δ) :
    (scPolyfold (example_1_1_3 δ h0 hmono)).AdmitsBumpFunctions :=
  scPolyfold_admitsBumpFunctions _ (hasContDiffBump_H 0 (nonneg_of_strictMono h0 hmono 0))

/-- **M-polyfolds modelled on Example 1.1.3 admit sc-smooth bump functions.** -/
theorem example_1_1_3_admitsBumpFunctions {X : Type*} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {PX : MPolyfold X}
    (h : ∀ x, ∃ φ : MChart X, PX.IsChart φ ∧ x ∈ φ.source ∧
      ∃ (δ : ℕ → ℝ) (h0 : δ 0 = 0) (hmono : StrictMono δ), φ.model.E = example_1_1_3 δ h0 hmono) :
    PX.AdmitsBumpFunctions := by
  refine MPolyfold.admitsBumpFunctions_of_hasContDiffBump fun x => ?_
  obtain ⟨φ, hφ, hx, δ, h0, hmono, hE⟩ := h x
  refine ⟨φ, hφ, hx, ?_⟩
  obtain ⟨⟨E, C, O, hR⟩, src⟩ := φ
  simp only at hE
  subst hE
  exact hasContDiffBump_H 0 (nonneg_of_strictMono h0 hmono 0)

end Example113

/-! ### `W^{1,4}(Ω)` and `W^{1,3/2}(Ω)` -/

section W1p

variable {n : ℕ} {Ω : Set (Fin n → ℝ)}

/-- **2021, p. 231 (preprint p. 194): `W^{1,p}(Ω)`, `p` even (e.g. `W^{1,4}(Ω)`), with an
sc-structure, admits sc-smooth bump functions.**  For every sc-Banach space `E` whose `0`-level is
isomorphic to `W^{1,p}(Ω)`, every local model on `E` has the sc-smooth bump function property:
`β(‖x‖ᵖ_{W^{1,p}})` is `C^∞` on `E₀` by Theorem 5.5.5 (1), hence sc-smooth. -/
theorem remark_5_5_5_W1p_even {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : ∃ j : ℕ, p = 2 * j)
    (M : LocalModel) (e : M.E 0 ≃L[ℝ] W n 1 p Ω) : M.HasBumpProperty :=
  M.hasBumpProperty_of_hasContDiffBump ((remark_5_5_5_sobolev_bump.1 hp).of_equiv e)

instance fact_one_le_four : Fact (1 ≤ ENNReal.ofReal 4) := ⟨by simp⟩

instance fact_one_le_three_halves : Fact (1 ≤ ENNReal.ofReal (3 / 2)) := ⟨by norm_num⟩

/-- **2021, p. 231: `W^{1,4}(Ω)` with the sc-structure `E_m = W^{1+m,4}(Ω)` admits sc-smooth bump
functions**, stated for every sc-Banach space `E` with `E₀ ≅ W^{1,4}(Ω)`: (0) `E` as an M-polyfold
admits sc-smooth bump functions; (1) every local model on `E` has the sc-smooth bump function
property; (2) an M-polyfold whose charts are modelled on such spaces admits sc-smooth bump
functions. -/
theorem remark_5_5_5_W14 :
    (∀ (E : ScBanach), (E 0 ≃L[ℝ] W n 1 4 Ω) → (scPolyfold E).AdmitsBumpFunctions) ∧
    (∀ (M : LocalModel), (M.E 0 ≃L[ℝ] W n 1 4 Ω) → M.HasBumpProperty) ∧
      ∀ {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X},
        (∀ x, ∃ φ : MChart X, PX.IsChart φ ∧ x ∈ φ.source ∧
          Nonempty (φ.model.E 0 ≃L[ℝ] W n 1 4 Ω)) → PX.AdmitsBumpFunctions := by
  have h4 : ∃ j : ℕ, (4 : ℝ) = 2 * j := ⟨2, by norm_num⟩
  refine ⟨fun E e => scPolyfold_admitsBumpFunctions E
    ((remark_5_5_5_sobolev_bump.1 h4).of_equiv e), fun M e => remark_5_5_5_W1p_even h4 M e,
    fun {X} _ _ _ {PX} h => ?_⟩
  refine MPolyfold.admitsBumpFunctions_of_hasContDiffBump fun x => ?_
  obtain ⟨φ, hφ, hx, ⟨e⟩⟩ := h x
  exact ⟨φ, hφ, hx, (remark_5_5_5_sobolev_bump.1 h4).of_equiv e⟩

lemma floor_three_halves : ⌊(3 / 2 : ℝ)⌋₊ = 1 := by
  rw [Nat.floor_eq_iff (by norm_num)]; norm_num

lemma three_halves_ne_nat : ∀ j : ℕ, (3 / 2 : ℝ) ≠ j := by
  intro j hj
  rcases Nat.lt_or_ge j 2 with h | h
  · interval_cases j <;> norm_num at hj
  · have : (2 : ℝ) ≤ j := by exact_mod_cast h
    linarith

/-- **2021, p. 231 (preprint p. 194): on `W^{1,3/2}(Ω)` with an sc-structure, the straightforward
bump function is sc¹.**  For every sc-Banach space `E` with `E₀ ≅ W^{1,3/2}(Ω)`, the function
`β(‖x‖^{3/2})` (Theorem 5.5.5 (3): `C^{[3/2]} = C¹`) is sc¹ on `E`, not identically zero, with
bounded support in `E₀`. -/
theorem remark_5_5_5_W1_3_2 (E : ScBanach) (e : E 0 ≃L[ℝ] W n 1 (3 / 2) Ω) :
    ∃ f : E 0 → ℝ, IsSck 1 E realSc univ f ∧ f ≠ 0 ∧ Bornology.IsBounded (support f) := by
  have h := (remark_5_5_5_sobolev_bump (n := n) (k := 1) (p := 3 / 2) (Ω := Ω)).2.2
    three_halves_ne_nat
  rw [floor_three_halves] at h
  exact exists_isSck_bump E (k := 0) (h.of_equiv e)

end W1p

/-! ### The sc-structure `E_m = W^{1+m,p}(Ω)` -/

section SobolevSc

variable (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (Ω : Set (Fin n → ℝ))

/-- The scale `E_m = W^{1+m,p}(Ω)` with the inclusions `inclW`, given that they are compact
(Rellich–Kondrachov; `Ω` open). -/
def sobolevScale (hΩ : IsOpen Ω)
    (hc : ∀ m, IsCompactOperator (inclW (n := n) (k := m + 1) (p := p) (Ω := Ω))) : ScScale where
  lvl m := W n (m + 1) p Ω
  incl _ := inclW
  incl_injective _ := inclW_injective hΩ
  incl_isCompactOperator m := hc m

/-- **The sc-structure `E_m = W^{1+m,p}(Ω)`** on `W^{1,p}(Ω)`, given the compactness of the
inclusions and the density of `E_∞` in every level. -/
def sobolevSc (hΩ : IsOpen Ω)
    (hc : ∀ m, IsCompactOperator (inclW (n := n) (k := m + 1) (p := p) (Ω := Ω)))
    (hd : ∀ m, Dense ((sobolevScale n p Ω hΩ hc).smoothLvl m)) : ScBanach where
  toScScale := sobolevScale n p Ω hΩ hc
  dense_smooth := hd

/-- Its `0`-level is `W^{1,p}(Ω)`. -/
lemma sobolevSc_zero (hΩ : IsOpen Ω)
    (hc : ∀ m, IsCompactOperator (inclW (n := n) (k := m + 1) (p := p) (Ω := Ω)))
    (hd : ∀ m, Dense ((sobolevScale n p Ω hΩ hc).smoothLvl m)) :
    (sobolevSc n p Ω hΩ hc hd).lvl 0 = W n 1 p Ω := rfl

/-- **`W^{1,p}(Ω)`, `p` even, with the sc-structure `E_m = W^{1+m,p}(Ω)`: every local model has
the sc-smooth bump function property** (2021, p. 231, for `p = 4`). -/
theorem sobolevSc_hasBumpProperty (hp : ∃ j : ℕ, p = 2 * j) (hΩ : IsOpen Ω)
    (hc : ∀ m, IsCompactOperator (inclW (n := n) (k := m + 1) (p := p) (Ω := Ω)))
    (hd : ∀ m, Dense ((sobolevScale n p Ω hΩ hc).smoothLvl m))
    (M : LocalModel) (hM : M.E = sobolevSc n p Ω hΩ hc hd) : M.HasBumpProperty := by
  obtain ⟨E, C, O, hR⟩ := M
  subst hM
  exact LocalModel.hasBumpProperty_of_hasContDiffBump _
    ((remark_5_5_5_sobolev_bump (n := n) (k := 1) (p := p) (Ω := Ω)).1 hp)

/-- **`W^{1,p}(Ω)`, `p` even, with the sc-structure `E_m = W^{1+m,p}(Ω)` admits sc-smooth bump
functions** (as an M-polyfold; 2021, p. 231, for `p = 4`). -/
theorem sobolevSc_admitsBumpFunctions (hp : ∃ j : ℕ, p = 2 * j) (hΩ : IsOpen Ω)
    (hc : ∀ m, IsCompactOperator (inclW (n := n) (k := m + 1) (p := p) (Ω := Ω)))
    (hd : ∀ m, Dense ((sobolevScale n p Ω hΩ hc).smoothLvl m)) :
    (scPolyfold (sobolevSc n p Ω hΩ hc hd)).AdmitsBumpFunctions :=
  scPolyfold_admitsBumpFunctions _
    ((remark_5_5_5_sobolev_bump (n := n) (k := 1) (p := p) (Ω := Ω)).1 hp)

/-- **`W^{1,3/2}(Ω)` with `E_m = W^{1+m,3/2}(Ω)`: `β(‖x‖^{3/2})` is sc¹** (2021, p. 231). -/
theorem sobolevSc_exists_sc1_bump (hΩ : IsOpen Ω)
    (hc : ∀ m, IsCompactOperator (inclW (n := n) (k := m + 1) (p := 3 / 2) (Ω := Ω)))
    (hd : ∀ m, Dense ((sobolevScale n (3 / 2) Ω hΩ hc).smoothLvl m)) :
    ∃ f : W n 1 (3 / 2) Ω → ℝ, IsSck 1 (sobolevSc n (3 / 2) Ω hΩ hc hd) realSc univ f ∧
      f ≠ 0 ∧ Bornology.IsBounded (support f) :=
  remark_5_5_5_W1_3_2 (sobolevSc n (3 / 2) Ω hΩ hc hd) (ContinuousLinearEquiv.refl ℝ _)

/-- `W^{k,p}(∅) = 0`. -/
instance subsingleton_W_empty (k : ℕ) : Subsingleton (W n k p (∅ : Set (Fin n → ℝ))) := by
  refine ⟨fun u v => Subtype.ext (PiLp.ext fun a => ?_)⟩
  rw [← sub_eq_zero, Lp.eq_zero_iff_ae_eq_zero]
  simp only [Measure.restrict_empty, ae_zero]
  exact Filter.eventually_bot

/-- **The hypotheses of `sobolevSc` are consistent**: for `Ω = ∅` the inclusions are compact
and `E_∞` is dense.  (A non-trivial instance: the unit interval `(0,1) ⊂ ℝ¹`, every `p > 1`,
`SobolevCube.cubeSc` in `GapP1_SobolevCube5.lean`.) -/
theorem sobolevSc_hyps_empty :
    ∃ hc : ∀ m, IsCompactOperator (inclW (n := n) (k := m + 1) (p := p)
        (Ω := (∅ : Set (Fin n → ℝ)))),
      ∀ m, Dense ((sobolevScale n p ∅ isOpen_empty hc).smoothLvl m) := by
  have hc : ∀ m, IsCompactOperator (inclW (n := n) (k := m + 1) (p := p)
      (Ω := (∅ : Set (Fin n → ℝ)))) := fun m =>
    ⟨{0}, isCompact_singleton, Filter.mem_of_superset Filter.univ_mem
      fun x _ => Subsingleton.elim _ _⟩
  refine ⟨hc, fun m => ?_⟩
  have : Subsingleton ((sobolevScale n p ∅ isOpen_empty hc).lvl m) :=
    subsingleton_W_empty n p (m + 1)
  have : (sobolevScale n p ∅ isOpen_empty hc).smoothLvl m = univ :=
    eq_univ_of_forall fun x => by
      rw [Subsingleton.elim x 0]
      exact (sobolevScale n p ∅ isOpen_empty hc).mem_smoothLvl_iff.2 fun j => ⟨0, by simp⟩
  rw [this]; exact dense_univ

end SobolevSc

end SobolevRemark

end Polyfold
