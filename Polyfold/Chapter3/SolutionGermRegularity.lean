import Polyfold.Chapter3.SolutionLinearization
import Polyfold.Chapter3.TangentGerm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.5–3.6: two
regularity facts about the solution germ of Theorem 3.5.11 (preprint 3.47) needed for Definition 3.2.1 (preprint 3.25) (2) at the
zero `x₀` (the proof of Theorem 3.6.8 (preprint 3.54) (2)).

# Regularity of the solution germ

* `Polyfold.isScInftyGermAt_of_lifts`: the level-wise `C^k`-lifts `σ_k : V_k → E_k` of Theorem
  3.47 (1) (`theorem_3_5_11_sc_smooth`) give the sc^∞-germ property of Definition 3.2.1 (preprint 3.25) (ii) in the
  `k`-dependent reading `IsScInftyGermAt` (Finding 80): on `V_j`, `j = max(m, k) + 1`, `σ` takes
  values in `E_m` and is `C^k` into `E_m`.
* `Polyfold.StabilityData.ker_Dfs_le_smooth`: the kernel `N' = ker D(h + s)(0)` of the
  linearization of `h + s` (basic germ plus sc⁺-germ) consists of smooth points, `N' ⊆ E'_∞`
  (Definition 3.2.1 (preprint 3.25) (2) asks for a smooth subspace `N`; the text does not comment).  Bootstrap along
  the `W`-component of the kernel equation `w = D₁B(0)a − ι Ds(0)(a, w)` (Lemma 3.1.9 (preprint 3.9),
  `D₂B(0) = 0`): `D₁B(0)a ∈ W_∞` since `DB(0)` is an sc-operator and `a` is smooth, and `Ds(0)`
  raises the level by one.
-/

open Set Filter Topology Function Module Metric ContinuousLinearMap

noncomputable section

namespace Polyfold

/-! ### The sc^∞-germ property from the `C^k`-lifts of Theorem 3.5.11 (preprint 3.47) (1) -/

section Lifts

variable {E : ScBanach}

/-- The inclusion `E_j → E_m`, `m ≤ j`, as a continuous linear map compatible with the
inclusions into `E₀`. -/
theorem exists_clm_toBase_eq {m j : ℕ} (h : m ≤ j) :
    ∃ L : E j →L[ℝ] E m, ∀ x, E.toBase m (L x) = E.toBase j x := by
  induction j, h using Nat.le_induction with
  | base => exact ⟨ContinuousLinearMap.id ℝ (E m), fun _ => rfl⟩
  | succ j _ ih =>
    obtain ⟨L, hL⟩ := ih
    exact ⟨L.comp (E.incl j), fun x => by rw [ContinuousLinearMap.comp_apply, hL]; rfl⟩

variable {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]

/-- **The sc^∞-germ property of Definition 3.2.1 (preprint 3.25) (ii) from the level-wise `C^k`-lifts of Theorem
3.47 (1)**: if for every `k ≥ 1` the map `σ : N ⊇ D → E₀` lifts on a relatively open neighbourhood
`V_k` of `0` in `D` to a `C^k`-map `σ_k : V_k → E_k`, then `σ` is an sc^∞-germ at `0` in the
`k`-dependent sense (`IsScInftyGermAt`): on `V_j`, `j = max(m, k) + 1`, `σ` takes values in `E_m`
and is `C^k` into `E_m` (compose `σ_j` with the inclusion `E_j → E_m`). -/
theorem isScInftyGermAt_of_lifts {D : Set N} {σ : N → E 0}
    (hlift : ∀ k : ℕ, 1 ≤ k → ∃ Vk : Set N, (∃ O : Set N, IsOpen O ∧ Vk = O ∩ D) ∧ (0 : N) ∈ Vk ∧
      ∃ σk : N → E k, ContDiffOn ℝ k σk Vk ∧ ∀ y ∈ Vk, E.toBase k (σk y) = σ y) :
    IsScInftyGermAt D σ := by
  intro m k
  obtain ⟨Vj, hVj, h0, σj, hσj, hσjeq⟩ := hlift (max m k + 1) (by omega)
  obtain ⟨L, hL⟩ := exists_clm_toBase_eq (E := E) (m := m) (j := max m k + 1) (by omega)
  refine ⟨Vj, hVj, h0, fun v hv => ⟨L (σj v), by rw [hL, hσjeq v hv]⟩, ?_⟩
  have hkj : ((k : ℕ) : WithTop ℕ∞) ≤ ((max m k + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by omega : k ≤ max m k + 1)
  have h1 : ContDiffOn ℝ k (fun v => L (σj v)) Vj :=
    L.contDiff.comp_contDiffOn (hσj.of_le hkj)
  refine h1.congr fun v hv => ?_
  apply levelMap_eq_of_toBase_eq
  rw [hL, hσjeq v hv, ScBanach.const_toBase]

end Lifts

/-! ### The kernel of `D(h + s)(0)` consists of smooth points -/

section KernelSmooth

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}
  {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  (𝒮 : StabilityData Ct W) {f : P × W 0 → Q × W 0} {B : P × W 0 → W 0}

/-- **The kernel `N' = ker D(h + s)(0)` is a smooth subspace** (`N' ⊆ E'_∞`; the text takes the
kernel of an sc-Fredholm operator to be smooth without comment, Definition 3.2.1 (preprint 3.25) (2) asks for a
smooth subspace).  Proof by bootstrapping along the `W`-component of the kernel equation:
`w = D₁B(0)a − ι Ds(0)(a, w)` (Lemma 3.1.9 (preprint 3.9): `D₂B(0) = 0`), where `D₁B(0)a ∈ W_∞` for the smooth
`a ∈ ℝⁿ` (`DB(0)` is an sc-operator) and `Ds(0)` raises the level by one (sc⁺): `w ∈ W_m` gives
`w ∈ W_{m+1}`. -/
theorem StabilityData.ker_Dfs_le_smooth (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (hf : IsBasicGerm Ct 𝒮.G f B) :
    LinearMap.ker (𝒮.Dfs f : P × W 0 →ₗ[ℝ] Q × W 0) ≤ (ScBanach.paramProd P W).smooth := by
  intro x hx
  have hCq := hC.isQuadrantLike
  have h0 : (0 : (ScBanach.paramProd P W) 1) ∈ 𝒮.G.U 1 := 𝒮.G.zero_mem 1
  have hx0 : 𝒮.Dfs f x = 0 := hx
  -- the `W`-component of the kernel equation
  have hDfs : 𝒮.Dfs f = Df 𝒮.G f 0 + (inr ℝ Q (W 0)).comp ((W.toBase 1).comp (𝒮.Ds 0)) := by
    rw [← 𝒮.Dfs'_zero f]; exact 𝒮.Dfs'_eq hC hf h0
  have hsnd := DFunLike.congr_fun (𝒮.snd_Df_eq hC hf h0) x
  have hDB2 : DB 𝒮.G B 0 ((0 : P), x.2) = 0 :=
    hf.contraction.deriv_zero_snd ((isSc1GermWith_DB hCq hf).hasFDerivWithinAt 0 h0) x.2
  have hdec : x = ((x.1, 0) : P × W 0) + ((0 : P), x.2) := by ext <;> simp
  have hw : x.2 = DB 𝒮.G B 0 ((x.1, 0) : P × W 0) - W.toBase 1 (𝒮.Ds 0 x) := by
    have h1 := congrArg Prod.snd hx0
    rw [hDfs, add_apply, Prod.snd_add] at h1
    have h2 : (Df 𝒮.G f 0 x).2 = x.2 - DB 𝒮.G B 0 x := by simpa using hsnd
    have h3 : (((inr ℝ Q (W 0)).comp ((W.toBase 1).comp (𝒮.Ds 0))) x).2 =
        W.toBase 1 (𝒮.Ds 0 x) := rfl
    rw [h2, h3] at h1
    have h4 : DB 𝒮.G B 0 x = DB 𝒮.G B 0 ((x.1, 0) : P × W 0) := by
      conv_lhs => rw [hdec]
      rw [map_add, hDB2, add_zero]
    rw [h4, sub_add_eq_add_sub, Prod.snd_zero, sub_eq_zero] at h1
    exact eq_sub_of_add_eq h1
  -- the sc-operator properties of `DB(0)` and `Ds(0)`
  have hDBop := (isSc1GermWith_DB hCq hf).isScOperator_deriv_zero
  have hDsop := 𝒮.isSc1GermWith_Ds.isScOperator_deriv_zero
  -- bootstrap: `w ∈ W_m` for every `m`
  have key : ∀ m, ∃ y : W m, W.toBase m y = x.2 := by
    intro m
    induction m with
    | zero => exact ⟨x.2, rfl⟩
    | succ m ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨TB, hTB⟩ := hDBop (m + 1)
      obtain ⟨TS, hTS⟩ := hDsop m
      have e1 : (ScBanach.paramProd P W).toBase (m + 1)
          ((x.1, (0 : W (m + 1))) : P × W (m + 1)) = ((x.1, 0) : P × W 0) := by
        rw [ScBanach.paramProd_toBase, map_zero]
      have e2 : (ScBanach.paramProd P W).toBase m ((x.1, y) : P × W m) = x := by
        rw [ScBanach.paramProd_toBase, hy]
      refine ⟨TB ((x.1, (0 : W (m + 1))) : P × W (m + 1)) - TS ((x.1, y) : P × W m), ?_⟩
      rw [map_sub, hTB, e1, hw]
      congr 1
      rw [W.shift_toBase m, hTS, e2]
  rw [ScScale.mem_smooth_iff]
  intro m
  obtain ⟨y, hy⟩ := key m
  exact ⟨((x.1, y) : P × W m), by rw [ScBanach.paramProd_toBase, hy]⟩

end KernelSmooth

end Polyfold
