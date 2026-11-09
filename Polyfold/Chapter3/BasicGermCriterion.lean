import Polyfold.Chapter3.InverseFamily

/-!
# Towards the basic germ criterion (§3.7): Lemmas 3.7.2 and 3.7.3 (preprint 3.59 and 3.60)

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I*, §3.7.  In the proof of Theorem 3.7.1 (preprint 3.58) the
family `L(b) = P ∘ Df(b)|X : X → Y` is shown to consist of injective operators for `b` near `0`
(**Lemma 3.7.2 (preprint 3.59)**) and to satisfy uniform lower bounds `|L(b)h|_m ≥ c_m |h|_m` on a compact
neighbourhood of `0` (**Lemma 3.7.3 (preprint 3.60)**), the hypotheses of Lemma 3.7.4 (preprint 3.61).  Both proofs are sequence
arguments using the compactness property (2) of Theorem 3.7.1 (preprint 3.58) for `Df` together with the
finite dimensionality of `A = ker P`; what they use of (2) is the following property of the
family `L` itself: if `b_j → b` in `B ∩ C`, `(h_j)` is bounded in `X_m` and `L(b_j)h_j → 0` in
`Y_m`, then `(h_j)` has a convergent subsequence in `X_m` (`Polyfold.FamilyCompactness`).  The
two lemmas are formalized in this abstract form, for an arbitrary family of sc-operators
`b ↦ L(b)` whose level maps are jointly continuous in `(b, h)` (as they are for
`(b, x) ↦ P ∘ Df(b)x` sc-smooth).

## Main results

* `Polyfold.lemma_3_7_2`: `L(b)` is injective on `X₀` for `b ∈ B ∩ C` close to `0` if `L(0)` is.
* `Polyfold.lemma_3_7_3`: on a compact `K ⊆ B ∩ C` on which every `L(b)_m` is injective there is
  `c_m > 0` with `|L(b)h|_m ≥ c_m |h|_m` for all `b ∈ K`, `h ∈ X_m`.
-/

open Set Filter Topology Function Metric

noncomputable section

namespace Polyfold

variable {Bf : Type} [NormedAddCommGroup Bf] [NormedSpace ℝ Bf] [FiniteDimensional ℝ Bf]
  {X Y : ScBanach}

/-- **The compactness property (2) of Theorem 3.7.1 (preprint 3.58), for the family `L(b) = P ∘ Df(b)|X`**: if
`b_j → b` in `O ⊆ B ∩ C`, `(h_j)` is bounded in `X_m` and `L(b_j)h_j → 0` in `Y_m`, then `(h_j)`
has a convergent subsequence in `X_m`.  (For `L = P ∘ Df|X` this follows from (2): `Df(b_j)h_j`
differs from `L(b_j)h_j` by `(1 − P)Df(b_j)h_j ∈ A`, bounded on every level because `A` is a
finite-dimensional smooth subspace.) -/
def FamilyCompactness (O : Set Bf) (L : Bf → ScOperator X Y) (m : ℕ) : Prop :=
  ∀ (b : ℕ → Bf) (b₀ : Bf) (h : ℕ → X m), (∀ j, b j ∈ O) → b₀ ∈ O → Tendsto b atTop (𝓝 b₀) →
    (∃ M : ℝ, ∀ j, ‖h j‖ ≤ M) → Tendsto (fun j => L (b j) m (h j)) atTop (𝓝 0) →
    ∃ h₀ : X m, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (h ∘ φ) atTop (𝓝 h₀)

/-- **Lemma 3.7.2 (preprint 3.59)** (abstract form): let `b ↦ L(b)` be a family of sc-operators `X → Y` with
`(b, h) ↦ L(b)h` continuous on `O × X₀` (`O ⊆ B ∩ C` a neighbourhood of `0`), `L(0)` injective on
`X₀`, and the compactness property on level `0`.  Then `L(b)` is injective on `X₀` for all `b ∈ O`
close to `0`.  Proof: otherwise there are `b_j → 0` and unit vectors `h_j` with `L(b_j)h_j = 0`;
a subsequence `h_j → h` has `|h| = 1` and `L(0)h = 0`. -/
theorem lemma_3_7_2 {O : Set Bf} (h0 : (0 : Bf) ∈ O) (L : Bf → ScOperator X Y)
    (hcont : ContinuousOn (fun p : Bf × X 0 => L p.1 0 p.2) (O ×ˢ univ))
    (hinj : Injective (L 0 0)) (hcpt : FamilyCompactness O L 0) :
    ∃ r > 0, ∀ b ∈ O, ‖b‖ < r → Injective (L b 0) := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ j : ℕ, ∃ b ∈ O, ‖b‖ < 1 / ((j : ℝ) + 1) ∧ ∃ h : X 0, L b 0 h = 0 ∧ h ≠ 0 := by
    intro j
    obtain ⟨b, hb, hbr, hni⟩ := hcon _ (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1))
    rw [injective_iff_map_eq_zero] at hni
    push_neg at hni
    obtain ⟨h, hh, hh0⟩ := hni
    exact ⟨b, hb, hbr, h, hh, hh0⟩
  choose b hbO hbr h hh hh0 using hseq
  set u : ℕ → X 0 := fun j => (‖h j‖⁻¹ : ℝ) • h j with hu
  have hun : ∀ j, ‖u j‖ = 1 := fun j => by
    rw [hu]; simp only [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (hh0 j))
  have huL : ∀ j, L (b j) 0 (u j) = 0 := fun j => by rw [hu, map_smul, hh j, smul_zero]
  have hb0 : Tendsto b atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => (hbr j).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨u₀, φ, hφ, hu₀⟩ := hcpt b 0 u hbO h0 hb0 ⟨1, fun j => (hun j).le⟩
    (by simp only [huL]; exact tendsto_const_nhds)
  have hbφ : Tendsto (b ∘ φ) atTop (𝓝 0) := hb0.comp hφ.tendsto_atTop
  have hlim : Tendsto (fun j => L (b (φ j)) 0 (u (φ j))) atTop (𝓝 (L 0 0 u₀)) :=
    ((hcont (0, u₀) ⟨h0, mem_univ _⟩).tendsto).comp
      (tendsto_nhdsWithin_iff.2 ⟨hbφ.prodMk_nhds hu₀, Eventually.of_forall fun j => ⟨hbO _, mem_univ _⟩⟩)
  have hL0 : L 0 0 u₀ = 0 := by
    refine tendsto_nhds_unique hlim ?_
    simp only [huL]; exact tendsto_const_nhds
  have hu₀0 : u₀ = 0 := hinj (by rw [hL0, map_zero])
  have hn : Tendsto (fun j => ‖u (φ j)‖) atTop (𝓝 ‖u₀‖) := (continuous_norm.tendsto _).comp hu₀
  rw [hu₀0, norm_zero] at hn
  have hn1 : Tendsto (fun j => ‖u (φ j)‖) atTop (𝓝 1) := by
    simp only [hun]; exact tendsto_const_nhds
  exact zero_ne_one (tendsto_nhds_unique hn hn1)

/-- **Lemma 3.7.3 (preprint 3.60)** (abstract form): let `K ⊆ B ∩ C` be compact (the closure of the neighbourhood
`Õ` of the text), `b ↦ L(b)` a family of sc-operators with `(b, h) ↦ L(b)_m h` continuous on
`K × X_m`, every `L(b)_m`, `b ∈ K`, injective, and the compactness property on level `m`.  Then
there is `c_m > 0` with `|L(b)h|_m ≥ c_m |h|_m` for all `b ∈ K` and `h ∈ X_m`.  Proof: otherwise
there are `b_j ∈ K` and unit vectors `h_j ∈ X_m` with `|L(b_j)h_j|_m → 0`; after passing to
subsequences `b_j → b ∈ K` and `h_j → h` with `|h|_m = 1`, and `L(b)h = 0` by continuity. -/
theorem lemma_3_7_3 {K : Set Bf} (hK : IsCompact K) (L : Bf → ScOperator X Y) (m : ℕ)
    (hcont : ContinuousOn (fun p : Bf × X m => L p.1 m p.2) (K ×ˢ univ))
    (hinj : ∀ b ∈ K, Injective (L b m)) (hcpt : FamilyCompactness K L m) :
    ∃ c > 0, ∀ b ∈ K, ∀ h : X m, c * ‖h‖ ≤ ‖L b m h‖ := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ j : ℕ, ∃ b ∈ K, ∃ h : X m, ‖L b m h‖ < 1 / ((j : ℝ) + 1) * ‖h‖ := by
    intro j
    obtain ⟨b, hb, h, hh⟩ := hcon _ (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1))
    exact ⟨b, hb, h, hh⟩
  choose b hbK h hh using hseq
  have hh0 : ∀ j, h j ≠ 0 := fun j hj => by
    have := hh j
    rw [hj, map_zero, norm_zero, norm_zero, mul_zero] at this
    exact lt_irrefl _ this
  set u : ℕ → X m := fun j => (‖h j‖⁻¹ : ℝ) • h j with hu
  have hun : ∀ j, ‖u j‖ = 1 := fun j => by
    rw [hu]; simp only [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (hh0 j))
  have huL : ∀ j, ‖L (b j) m (u j)‖ < 1 / ((j : ℝ) + 1) := fun j => by
    have hpos : 0 < ‖h j‖ := norm_pos_iff.2 (hh0 j)
    rw [hu, map_smul, norm_smul, norm_inv, norm_norm, inv_mul_lt_iff₀ hpos, mul_comm]
    exact hh j
  -- a convergent subsequence of `b_j` in the compact `K`
  obtain ⟨b₀, hb₀, φ₁, hφ₁, hb⟩ := hK.tendsto_subseq hbK
  have hLφ : Tendsto (fun j => L (b (φ₁ j)) m (u (φ₁ j))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => (huL (φ₁ j)).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_natCast_atTop_atTop.comp
      hφ₁.tendsto_atTop)
  -- a convergent subsequence of `u_j` from the compactness property
  obtain ⟨u₀, φ₂, hφ₂, hu₀⟩ := hcpt (b ∘ φ₁) b₀ (u ∘ φ₁) (fun j => hbK _) hb₀ hb
    ⟨1, fun j => (hun _).le⟩ hLφ
  set ψ : ℕ → ℕ := φ₁ ∘ φ₂ with hψ
  have hbψ : Tendsto (b ∘ ψ) atTop (𝓝 b₀) := hb.comp hφ₂.tendsto_atTop
  have hlim : Tendsto (fun j => L (b (ψ j)) m (u (ψ j))) atTop (𝓝 (L b₀ m u₀)) :=
    ((hcont (b₀, u₀) ⟨hb₀, mem_univ _⟩).tendsto).comp
      (tendsto_nhdsWithin_iff.2 ⟨hbψ.prodMk_nhds hu₀, Eventually.of_forall fun j => ⟨hbK _, mem_univ _⟩⟩)
  have hlim0 : Tendsto (fun j => L (b (ψ j)) m (u (ψ j))) atTop (𝓝 0) :=
    hLφ.comp hφ₂.tendsto_atTop
  have hL0 : L b₀ m u₀ = 0 := tendsto_nhds_unique hlim hlim0
  have hu₀0 : u₀ = 0 := hinj b₀ hb₀ (by rw [hL0, map_zero])
  have hn : Tendsto (fun j => ‖u (ψ j)‖) atTop (𝓝 ‖u₀‖) := (continuous_norm.tendsto _).comp hu₀
  rw [hu₀0, norm_zero] at hn
  have hn1 : Tendsto (fun j => ‖u (ψ j)‖) atTop (𝓝 1) := by
    simp only [hun]; exact tendsto_const_nhds
  exact zero_ne_one (tendsto_nhds_unique hn hn1)

end Polyfold
