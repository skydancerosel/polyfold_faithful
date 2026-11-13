import Polyfold.Chapter15.TransversalExtension
import Polyfold.Chapter15.CubeAuxNorm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, p. 699:
**Corollary 15.3.10 (1) and (3)** (2017: Corollary 15.1), regular perturbations and their
cobordisms over `[0, 1] × X`, as reductions to Theorems 15.3.7 and 15.3.9.

# Regular perturbations

## The text, paraphrased

For a strong bundle over an ep-groupoid with `d_X ≡ 0` and paracompact `|X|`, and `f`
sc-Fredholm with compact `|S_f|`:
(1) for every `(N, U)` controlling compactness there is a structurable `Λ` with dom-supp in `U`,
`N(Λ) < 1`, and `T(f, Λ)` onto on `supp(Λ ∘ f)`; then `Θ = Λ ∘ f` is a tame branched
ep⁺-subgroupoid with compact `|supp Θ|`; `(N, U, Λ)` is a *structurable regular perturbation*.
(2) (P's `corollary_15_3_10_2`) the interpolated `(Ñ, Ũ)` on `W̃ → [0, 1] × X` controls the
compactness of `f̃(t, x) = (t, f(x))`.
(3) there is a structurable regular perturbation `(Ñ, Ũ, Λ̃)` of `f̃` with `Λ̃ = Λⁱ` over
`{i} × X`, `i = 0, 1` (proof: Theorem 15.3.9 on `[0, 1] × X`).

## What is formalized (namespace `Polyfold.SBLocalization`)

* `IsRegularPerturbation A f N U Λ`: `(N, U)` controls compactness, `Λ` structurable, dom-supp in
  `U`, `N(Λ) < 1`, `(f, Λ)` transversal.
* **`corollary_15_3_10_1_hyp`**: (1) from `theorem_15_3_7_statement A` (G's statement, not yet
  proved), with the hypotheses Theorem 15.3.7 needs and the corollary does not state: `X` tame,
  sc-smooth bump functions (Remark 15.3.2), tame germ data of `f` (inherited Part I hypothesis).
  The perturbation is moreover in general position, and `Θ` is a compact branched ep⁺-subgroupoid.
* `isScFredholmSectionTame_cubeLiftEp`: `f̃` carries tame germ data if `f` does.
* **`corollary_15_3_10_3_hyp`**: (3) from `theorem_15_3_9_statement` for `W̃ → [0, 1] × X`, for
  boundary data `Λ_∂` on `W̃|∂([0, 1] × X)` that restrict to `Λ⁰`, `Λ¹` over `{0} × X`, `{1} × X`
  and satisfy the hypotheses of Theorem 15.3.9 there (structurable over the boundary, dom-supp in
  `Ũ`, `Ñ(Λ_∂) < 1`, the face condition); `∂([0, 1] × X) = {0, 1} × X` for `d_X ≡ 0` (P's
  `degIndex_cubeProd_one_of_degIndex_eq_zero`).  The text derives these properties of `Λ_∂` from
  `(Nⁱ, Uⁱ, Λⁱ)` being structurable regular perturbations; that derivation, and paracompactness
  and partitions of unity of `[0, 1] × X`, are hypotheses here.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

variable (A) in
/-- **Corollary 15.3.10 (1), p. 699**: `(N, U, Λ)` is a **structurable regular perturbation** of
`f`: `(N, U)` controls the compactness of `f` (Definition 15.3.1), `Λ` is structurable
(Definition 13.3.6) with dom-supp in `U` and `N(Λ) < 1`, and `T(f, Λ)` is onto on
`supp(Λ ∘ f)` (Definition 15.2.1). -/
def IsRegularPerturbation (f : A.Obj → A.W) (N : A.B.One → ℝ) (U : Set A.Obj)
    (Λ : A.W → ℚ≥0) : Prop :=
  ControlsCompactness A f N U ∧ IsStructurable A Λ ∧ domSupp Λ ⊆ U ∧
    (∀ x, pointwiseNorm N Λ x < 1) ∧ IsTransversal f Λ

/-- **Corollary 15.3.10 (1) (2017: Corollary 15.1 (1)), p. 699, from Theorem 15.3.7**: if the
statement of Theorem 15.3.7 holds for `A`, then for `d_X ≡ 0`, paracompact `|X|`, `f` sc-Fredholm
with compact `|S_f|`, and `(N, U)` controlling compactness, there is a structurable regular
perturbation `(N, U, Λ)`; it is in general position, and `Θ = Λ ∘ f` is a compact branched
ep⁺-subgroupoid.  Added (needed by Theorem 15.3.7, not stated in the corollary): `X` tame,
sc-smooth bump functions, tame germ data of `f`.  `d_X ≡ 0` and paracompactness are the
corollary's hypotheses; given Theorem 15.3.7 they are not used for (1). -/
theorem corollary_15_3_10_1_hyp (h157 : theorem_15_3_7_statement A)
    (_hd : ∀ x, A.X.PObj.degIndex x = 0) (_hpara : A.X.HasParacompactOrbitSpace)
    (hX : A.X.IsTame) (hbump : A.X.AdmitsBumpFunctionsPointwise) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) :
    ∃ Λ : A.W → ℚ≥0, IsRegularPerturbation A f N U Λ ∧ IsInGeneralPosition A f Λ ∧
      A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) := by
  obtain ⟨Λ, hΛ, hN, hdom, htr, hgp⟩ := h157 hX hbump f hf hft hS N U hcc (fun _ => 1)
    continuous_const (fun _ => rfl) (fun _ => ⟨one_pos, le_rfl⟩)
  obtain ⟨hbr, hcpt⟩ :=
    theorem_15_3_7_in_particular_hyp hf hft hcc hΛ.1 (fun x => (hN x).le) hdom hgp
  exact ⟨Λ, ⟨hcc, hΛ, hdom, hN, htr⟩, hgp, hbr, hcpt⟩

/-- `f̃(q, x) = ((q, x), f(x))` carries tame germ data if `f` does (Part I's
`IsScFredholmSectionTame.paramCube`, K4). -/
theorem isScFredholmSectionTame_cubeLiftEp {n : ℕ} {f : A.Obj → A.W}
    (hft : A.B.IsScFredholmSectionTame f) :
    (A.cubeSEP n).B.IsScFredholmSectionTame (cubeLiftEp (n := n) f hft.isScSmooth.1) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold n) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold n).prod A.X.PObj)
    (Prod.snd : (Fin n → unitInterval) × A.Obj → A.Obj)
  exact StrongBundle.IsScFredholmSectionTame.paramCube (n := n) hft

/-- `∂([0, 1] × X) = {0, 1} × X` for tame `X` with `d_X ≡ 0`. -/
theorem mem_boundary_cubeSEP_iff (hX : A.X.IsTame) (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (z : (A.cubeSEP 1).Obj) :
    z ∈ (A.cubeSEP 1).X.PObj.boundary ↔ (z.1 0 : ℝ) = 0 ∨ (z.1 0 : ℝ) = 1 := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have h := A.X.degIndex_cubeProd_one_of_degIndex_eq_zero hX hd z.1 z.2
  change 1 ≤ (A.X.cubeProd 1).PObj.degIndex (z.1, z.2) ↔ _
  rw [h]
  split_ifs with hz
  · exact iff_of_true le_rfl hz
  · exact iff_of_false (by norm_num) hz

/-- **Corollary 15.3.10 (3) (2017: Corollary 15.1 (3)), p. 699, from Theorem 15.3.9 on
`[0, 1] × X`**.  Let `X` be tame with `d_X ≡ 0`, `f` sc-Fredholm with tame germ data and compact
`|S_f|`, `(Nⁱ, Uⁱ)` controlling compactness (`i = 0, 1`), and `(Ñ, Ũ)` the interpolated pair of
(2).  Let `Λ_∂` be a multisection over `∂([0, 1] × X) = {0, 1} × X` that agrees with `Λⁱ` over
`{i} × X` and satisfies the hypotheses of Theorem 15.3.9 for `f̃` there.  If Theorem 15.3.9 holds
for `W̃ → [0, 1] × X` (with paracompact orbit space and partitions of unity, assumed), there is a
structurable regular perturbation `(Ñ, Ũ, Λ̃)` of `f̃` with `Λ̃ = Λⁱ` over `{i} × X`, and
`Λ̃ ∘ f̃` is a compact branched ep⁺-subgroupoid: the compact cobordism `Θ̃` of the text. -/
theorem corollary_15_3_10_3_hyp (h159 : theorem_15_3_9_statement (A.cubeSEP 1))
    (hX : A.X.IsTame) (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hparaC : (A.cubeSEP 1).X.HasParacompactOrbitSpace)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (h₀ : ControlsCompactness A f N₀ U₀) (h₁ : ControlsCompactness A f N₁ U₁)
    {Λ₀ Λ₁ : A.W → ℚ≥0} (Λb : (A.cubeSEP 1).W → ℚ≥0)
    (hb₀ : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λb w = Λ₀ (cubeVal w).2)
    (hb₁ : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λb w = Λ₁ (cubeVal w).2)
    (hbs : IsBoundaryStructurable (A.cubeSEP 1) Λb)
    (hbdom : boundaryDomSupp Λb ⊆ interpSet A U₀ U₁)
    (hbN : ∀ z ∈ (A.cubeSEP 1).X.PObj.boundary, pointwiseNorm (interpAuxNorm A N₀ N₁) Λb z < 1)
    (hbonto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) Λb) :
    ∃ Λ' : (A.cubeSEP 1).W → ℚ≥0,
      IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
        (interpAuxNorm A N₀ N₁) (interpSet A U₀ U₁) Λ' ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2) ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2) ∧
      (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ∧
      (A.cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hcc := corollary_15_3_10_2 hf.1.1.1 h₀ h₁
  have hft' : (A.cubeSEP 1).B.IsScFredholmSectionTame (cubeLiftEp (n := 1) f hf.1.1.1) :=
    isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  obtain ⟨Λ', hΛ', hbd', hdom', hN', -, htr', hbr, hcpt⟩ :=
    h159 hXC hparaC hPUC _ (isScFredholmSectionFunctor_cubeLiftEp hf hft) hft'
      (hasCompactSolutionSetEp_cubeLiftEp hf.1.1.1 hS) _ _ hcc Λb hbs hbdom
      (fun z hz => (hbN z hz).le) (fun _ => 1) continuous_const (fun _ => rfl)
      (fun _ => ⟨one_pos, le_rfl⟩) hbN hbonto
  have hbdry : ∀ w : (A.cubeSEP 1).W, ((cubeVal w).1.1 0 : ℝ) = 0 ∨ ((cubeVal w).1.1 0 : ℝ) = 1 →
      (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary := fun w hw =>
    (mem_boundary_cubeSEP_iff hX hd _).2 hw
  exact ⟨Λ', ⟨hcc, hΛ', hdom', hN', htr'⟩,
    fun w hw => (hbd' w (hbdry w (Or.inl hw))).trans (hb₀ w hw),
    fun w hw => (hbd' w (hbdry w (Or.inr hw))).trans (hb₁ w hw), hbr, hcpt⟩

end SBLocalization

end Polyfold
