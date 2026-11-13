import Polyfold.Chapter16.StrongPolyfoldBundle
import Polyfold.Chapter11.AuxiliaryNormTransport2021
import Polyfold.Chapter12.AuxNormLocalExtension
import Polyfold.Chapter12.ReflexiveAuxNormExtension
import Polyfold.Chapter12.ReflexiveCompactnessEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.3 (pp. 726–728; 2017: §16.3): **Definition 16.3.9, Proposition 16.3.10, Definitions
16.3.12–16.3.14, Theorem 16.3.15, Proposition 16.3.16, Theorem 16.3.17**.  Numbers and pages are
the 2021 text's.

# Auxiliary norms on strong polyfold bundles

## The text, paraphrased

(Definition 16.3.9) An auxiliary norm of `(p : Y → Z, c̄)` is a continuous `n : Y_{0,1} → [0, ∞)`
such that for every structure `m = ((P, μ), Γ, γ) ∈ c̄` there is an auxiliary norm `N` of `W` with
`n(Γ(|e|)) = N(e)` on `W_{0,1}`; `Y_{0,1} = Γ(|W_{0,1}|)`.  By Theorem 11.5.1 (`N = [D]^*N'`) it
suffices that one structure has one.  (Proposition 16.3.10) Over a paracompact polyfold an auxiliary
norm exists.  (Definitions 16.3.12–16.3.14) Reflexive `1`-fibres: in some structure; reflexive
auxiliary norm: an auxiliary norm with `N` reflexive in some model; mixed convergence: the
representatives are mixed convergent in a model with a reflexive auxiliary norm.  (Theorem 16.3.15)
With reflexive `1`-fibres: (1) a reflexive auxiliary norm exists; (2) every auxiliary norm lies
between two reflexive ones.  (Proposition 16.3.16) For a reflexive auxiliary norm: (1) `p(y_k) → z`,
`n(y_k) → 0` give `y_k → 0_z` in `Y_{0,1}`; (2) `n(y) ≤ liminf n(y_k)` for `y_k` mixed convergent
to `y`.  (Theorem 16.3.17) Over a tame polyfold an auxiliary norm of `Y_{0,1}|∂Z` extends to an
auxiliary norm of `Y_{0,1}`, reflexive if the given one is.

## What is formalized (namespaces `StrongPolyfoldBundleStructure`, `StrongPolyfoldBundle`)

* `oneToY` (`e ↦ Γ(|e|)`), `Y01`, `normOf n` (`e ↦ n(Γ(|e|))`), `IsAuxNormFor`;
  `oneToY_pull`, `normOf_pull` (`n ∘ Γ ∘ |·| = [D]^*(n ∘ Γ' ∘ |·|)`), `isAuxNormFor_of_equiv`,
  `Y01_eq_of_equiv` (the independence of the structure); `descend` (`N` read on `Y`),
  `normOf_descend`; `continuous_normOrbit` (the continuity of `n` on `Y_{0,1}` with the topology
  of `|W[1]|`).
* `StrongPolyfoldBundle.IsAuxNorm` (**Definition 16.3.9**: for every structure),
  **`definition_16_3_9`** (one structure suffices), `Y01`, `Y01_eq`, `IsAuxNorm.nonneg`.
* **`proposition_16_3_10`**.
* `HasReflexiveFibers`, `IsReflexiveAuxNorm`, `MixedTendsto`, `MixedTendstoIn`
  (**Definitions 16.3.12, 16.3.13, 16.3.14**).
* **`theorem_16_3_15_one`, `theorem_16_3_15_two`**.
* **`proposition_16_3_16_one`** (for every auxiliary norm, in the topology of `|W[1]|`);
  **`proposition_16_3_16_two_of_mem`** (mixed convergence read in the model of the reflexive norm).
* `IsAuxNormBoundary`, **`theorem_16_3_17_one`** (as printed); **`theorem_16_3_17_two_hyp`**
  (with the reflexive local step of Theorem 12.2.13 as hypothesis, no tameness needed),
  `theorem_16_3_17_two_hyp_witness`.

## Readings and what is not formalized

* `n` is a function `Y → ℝ`; only its values on `Y_{0,1}` matter.  Its continuity on `Y_{0,1}`,
  which carries the topology of `|W[1]|` through `Γ` (not the topology of `Y`), follows from that
  of `N` (`continuous_normOrbit`).
* "`y_k → 0_z` in `Y_{0,1}`" in Proposition 16.3.16 (1) is read in `|W[1]|`.
* The parenthetical claim of Definition 16.3.12 (equivalent structures also have reflexive
  `1`-fibres) and the comparison of mixed convergence and of reflexive auxiliary norms between two
  equivalent structures are not formalized: Proposition 16.3.16 (2) is proved for mixed convergence
  in a structure in which `n` is reflexive (`proposition_16_3_16_two_of_mem`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization SBLocalization

namespace StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}

/-! ### `Y_{0,1}` and functions on it, read in a structure -/

variable (S : StrongPolyfoldBundleStructure p)

/-- `e ↦ Γ(|e|)` for `e ∈ W_{0,1}`. -/
def oneToY (e : S.A.B.One) : Y := S.Γ (S.A.E.toEpGroupoid.π (S.A.B.oneVal e))

/-- **`Y_{0,1} = Γ(|W_{0,1}|)`** (Definition 16.3.9). -/
def Y01 : Set Y := range S.oneToY

/-- A function `n` on `Y` read on `W_{0,1}`: `e ↦ n(Γ(|e|))`. -/
def normOf (n : Y → ℝ) : S.A.B.One → ℝ := fun e => n (S.oneToY e)

/-- `n` is represented in `S` by an auxiliary norm (Definitions 12.2.1, 8.3.5):
`e ↦ n(Γ(|e|))` is one. -/
def IsAuxNormFor (n : Y → ℝ) : Prop := S.A.E.IsAuxNorm (S.normOf n)

/-- `n ∘ Γ` read on `|W[1]|`. -/
def normOrbit (n : Y → ℝ) : S.A.E.OneOrbitSpace → ℝ := fun q => n (S.Γ (oneToOrbit S.A q))

/-- **The continuity of `n` in Definition 16.3.9**, for the topology `Y_{0,1}` gets from `|W[1]|`
through `Γ`: it follows from the continuity of `N`. -/
theorem continuous_normOrbit {n : Y → ℝ} (hn : S.IsAuxNormFor n) : Continuous (S.normOrbit n) := by
  have e : S.normOrbit n = Quotient.lift (S.normOf n) (fun _ _ h =>
      congrArg (fun q => n (S.Γ (oneToOrbit S.A q))) (Quotient.sound h)) := by
    funext q
    induction q using Quotient.inductionOn
    rfl
  rw [e]
  exact hn.isAuxNorm.continuous.quotient_lift _

/-- `n` read in `S` is invariant (it factors through `|W|`). -/
theorem isOneInvariant_normOf (n : Y → ℝ) : IsOneInvariant S.A (S.normOf n) := fun _ _ h =>
  congrArg (fun q => n (S.Γ q)) h

/-- `N` on `W_{0,1}` read as a function on `Y` (`0` off `Y_{0,1}`). -/
def descend (N : S.A.B.One → ℝ) : Y → ℝ := by
  classical
  exact fun y => if h : y ∈ S.Y01 then N h.choose else 0

/-- `descend N` reads back as `N` for an invariant `N`. -/
theorem normOf_descend {N : S.A.B.One → ℝ} (hN : IsOneInvariant S.A N) :
    S.normOf (S.descend N) = N := by
  funext e
  have h : S.oneToY e ∈ S.Y01 := ⟨e, rfl⟩
  simp only [normOf, descend, dif_pos h]
  exact hN _ _ (S.Γ.injective h.choose_spec)

theorem descend_oneToY {N : S.A.B.One → ℝ} (hN : IsOneInvariant S.A N) (e : S.A.B.One) :
    S.descend N (S.oneToY e) = N e :=
  congrFun (S.normOf_descend hN) e

/-! ### Independence of the structure -/

variable {S}

/-- For `F : W → W'` with `Γ' ∘ |F| = Γ`, the point `e' ∈ W'_{0,1}` representing `|F|(|e|)` has
`Γ'(|e'|) = Γ(|e|)`. -/
theorem oneToY_pull {S' : StrongPolyfoldBundleStructure p} {F : GenSBMap S.A S'.A}
    (hF : F.IsGeneralizedIso) (hΓ : ⇑S'.Γ ∘ F.orbitMap = ⇑S.Γ) (e : S.A.B.One) :
    S'.oneToY ((GenSBMap.rep hF).oneOrbitMap (Quotient.mk _ e)).out = S.oneToY e := by
  have h1 : S'.A.E.toEpGroupoid.π
      (S'.A.B.oneVal ((GenSBMap.rep hF).oneOrbitMap (Quotient.mk _ e)).out) =
      F.orbitMap (S.A.E.toEpGroupoid.π (S.A.B.oneVal e)) :=
    calc _ = oneToOrbit S'.A (Quotient.mk _
          ((GenSBMap.rep hF).oneOrbitMap (Quotient.mk _ e)).out) := rfl
      _ = oneToOrbit S'.A ((GenSBMap.rep hF).oneOrbitMap (Quotient.mk _ e)) :=
          congrArg _ (Quotient.out_eq _)
      _ = (GenSBMap.rep hF).orbitMap (oneToOrbit S.A (Quotient.mk _ e)) :=
          SDiagram.oneToOrbit_oneOrbitMap _ _
      _ = F.orbitMap (S.A.E.toEpGroupoid.π (S.A.B.oneVal e)) :=
          congrFun (congrArg GenSBMap.orbitMap (GenSBMap.cls_rep hF)) _
  unfold oneToY
  rw [h1]
  exact congrFun hΓ _

/-- **2021 p. 726, (16.7)**: `n ∘ Γ ∘ |·| = [D]^*(n ∘ Γ' ∘ |·|)` for the generalized strong
bundle isomorphism `[D]` of an equivalence. -/
theorem normOf_pull {S' : StrongPolyfoldBundleStructure p} {F : GenSBMap S.A S'.A}
    (hF : F.IsGeneralizedIso) (hΓ : ⇑S'.Γ ∘ F.orbitMap = ⇑S.Γ) (n : Y → ℝ) :
    S.normOf n = GenSBMap.pullNorm hF (S'.normOf n) := by
  funext e
  change n (S.oneToY e) = n (S'.oneToY ((GenSBMap.rep hF).oneOrbitMap (Quotient.mk _ e)).out)
  rw [oneToY_pull hF hΓ]

/-- **Definition 16.3.9, "independent of the structure"** (via Theorem 11.5.1): if `n` is
represented by an auxiliary norm in `S'`, it is in every equivalent `S`. -/
theorem isAuxNormFor_of_equiv {S' : StrongPolyfoldBundleStructure p} (h : Equiv S S')
    {n : Y → ℝ} (hn : S'.IsAuxNormFor n) : S.IsAuxNormFor n := by
  obtain ⟨F, hF, -, hΓ⟩ := h
  unfold IsAuxNormFor
  rw [normOf_pull hF hΓ]
  exact GenSBMap.isAuxNorm_pullNorm hF hn

theorem Y01_subset_of_equiv {S' : StrongPolyfoldBundleStructure p} (h : Equiv S S') :
    S.Y01 ⊆ S'.Y01 := by
  obtain ⟨F, hF, -, hΓ⟩ := h
  rintro _ ⟨e, rfl⟩
  exact ⟨_, oneToY_pull hF hΓ e⟩

/-- **`Y_{0,1}` does not depend on the structure** (Definition 16.3.9). -/
theorem Y01_eq_of_equiv {S' : StrongPolyfoldBundleStructure p} (h : Equiv S S') :
    S.Y01 = S'.Y01 :=
  (Y01_subset_of_equiv h).antisymm (Y01_subset_of_equiv h.symm)

end StrongPolyfoldBundleStructure

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  (c : StrongPolyfoldBundle p)

/-! ### Definition 16.3.9 and Proposition 16.3.10 -/

/-- **`Y_{0,1}`** of a strong polyfold bundle (any representative, `Y01_eq`). -/
def Y01 : Set Y := c.out.Y01

theorem Y01_eq {S : StrongPolyfoldBundleStructure p} (hS : ⟦S⟧ = c) : c.Y01 = S.Y01 :=
  Y01_eq_of_equiv (Quotient.exact (show ⟦c.out⟧ = ⟦S⟧ by rw [Quotient.out_eq, hS]))

/-- **2021 Definition 16.3.9, p. 726 (2017: Definition 16.23)**: `n : Y → ℝ` is an **auxiliary
norm** of `(p, c̄)` if for every structure `((P, μ), Γ, γ) ∈ c̄`, `e ↦ n(Γ(|e|))` is an auxiliary
norm of `(P, μ)` (Definition 12.2.1); only the values on `Y_{0,1}` matter. -/
def IsAuxNorm (n : Y → ℝ) : Prop :=
  ∀ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c → S.IsAuxNormFor n

variable {c}

/-- **Definition 16.3.9, the paragraph after it (p. 726)**: by Theorem 11.5.1 it suffices that
one structure of `c̄` represents `n` by an auxiliary norm. -/
theorem definition_16_3_9 {n : Y → ℝ} :
    c.IsAuxNorm n ↔ ∃ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c ∧ S.IsAuxNormFor n := by
  refine ⟨fun h => ?_, fun ⟨S₀, hS₀, hn⟩ S hS => ?_⟩
  · obtain ⟨S, hS⟩ := Quotient.exists_rep c
    exact ⟨S, hS, h S hS⟩
  · exact isAuxNormFor_of_equiv (Quotient.exact (hS.trans hS₀.symm)) hn

/-- An auxiliary norm is `≥ 0` on `Y_{0,1}`. -/
theorem IsAuxNorm.nonneg {n : Y → ℝ} (hn : c.IsAuxNorm n) {y : Y} (hy : y ∈ c.Y01) : 0 ≤ n y := by
  obtain ⟨S, hS⟩ := Quotient.exists_rep c
  rw [c.Y01_eq hS] at hy
  obtain ⟨e, rfl⟩ := hy
  exact (hn S hS).isAuxNorm.nonneg e

/-- The auxiliary norm `N` of a structure `S ∈ c̄`, read on `Y`, is an auxiliary norm of `c̄`. -/
theorem isAuxNorm_descend {S : StrongPolyfoldBundleStructure p} (hS : ⟦S⟧ = c)
    {N : S.A.B.One → ℝ} (hN : S.A.E.IsAuxNorm N) : c.IsAuxNorm (S.descend N) := by
  refine definition_16_3_9.2 ⟨S, hS, ?_⟩
  unfold IsAuxNormFor
  rw [S.normOf_descend hN.isOneInvariant]
  exact hN

variable (c)

/-- **2021 Proposition 16.3.10, p. 726 (2017: Proposition 16.4)**: a strong polyfold bundle over a
(paracompact) polyfold has an auxiliary norm (Theorem 12.2.2 in one structure; `|X|` is
paracompact by Definition 16.3.1). -/
theorem proposition_16_3_10 : ∃ n : Y → ℝ, c.IsAuxNorm n := by
  obtain ⟨S, hS⟩ := Quotient.exists_rep c
  obtain ⟨N, hN⟩ := S.A.E.theorem_12_2_2 S.paracompact
  exact ⟨_, isAuxNorm_descend hS hN⟩

/-! ### Definitions 16.3.12–16.3.14 -/

/-- **2021 Definition 16.3.12, p. 727 (2017: Definition 16.24)**: `(p, c̄)` has **reflexive
`1`-fibres** if some structure in `c̄` has (Part I Definition 5.1.4 for its object bundle). -/
def HasReflexiveFibers : Prop :=
  ∃ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c ∧ S.A.E.HasReflexiveFibers

/-- **2021 Definition 16.3.13, p. 727 (2017: Definition 16.25)**: a **reflexive auxiliary norm**:
an auxiliary norm `n` represented in some model `m ∈ c̄` by a reflexive auxiliary norm
(Definition 12.2.10). -/
def IsReflexiveAuxNorm (n : Y → ℝ) : Prop :=
  c.IsAuxNorm n ∧ ∃ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c ∧
    S.A.E.IsReflexiveAuxNorm (S.normOf n)

/-- Mixed convergence read in one structure `S`: `y_k = Γ(|w_k|)`, `y = Γ(|w|)` with
`w_k →ᵐ w` in `W_{0,1}` (Definition 12.2.8). -/
def MixedTendstoIn (S : StrongPolyfoldBundleStructure p) (y : ℕ → Y) (y₀ : Y) : Prop :=
  ∃ (w : ℕ → S.A.B.One) (w₀ : S.A.B.One), (∀ k, S.oneToY (w k) = y k) ∧ S.oneToY w₀ = y₀ ∧
    S.A.E.MixedTendsto w w₀

/-- **2021 Definition 16.3.14, p. 727 (2017: Definition 16.26)**: `y_k ∈ Y_{0,1}` is **mixed
convergent** to `y` if, in a model `m ∈ c̄` with reflexive `1`-fibres and a reflexive auxiliary
norm, the representatives are mixed convergent. -/
def MixedTendsto (y : ℕ → Y) (y₀ : Y) : Prop :=
  ∃ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c ∧ S.A.E.HasReflexiveFibers ∧
    (∃ N : S.A.B.One → ℝ, S.A.E.IsReflexiveAuxNorm N) ∧ MixedTendstoIn S y y₀

/-! ### Theorem 16.3.15 -/

variable {c}

/-- **2021 Theorem 16.3.15 (1), p. 727 (2017: Theorem 16.3)**: with reflexive `1`-fibres there is a
reflexive auxiliary norm (Theorem 12.2.11 in a structure with reflexive `1`-fibres). -/
theorem theorem_16_3_15_one (hc : c.HasReflexiveFibers) : ∃ n : Y → ℝ, c.IsReflexiveAuxNorm n := by
  obtain ⟨S, hS, hB⟩ := hc
  obtain ⟨N, hN⟩ := S.A.E.theorem_12_2_11_exists S.paracompact hB
  refine ⟨S.descend N, isAuxNorm_descend hS hN.toIsAuxNorm, S, hS, ?_⟩
  rw [S.normOf_descend hN.toIsAuxNorm.isOneInvariant]
  exact hN

/-- **2021 Theorem 16.3.15 (2), p. 727**: with reflexive `1`-fibres, every auxiliary norm `n` lies
between two reflexive auxiliary norms on `Y_{0,1}` (the sandwich of Theorem 12.2.11). -/
theorem theorem_16_3_15_two (hc : c.HasReflexiveFibers) {n : Y → ℝ} (hn : c.IsAuxNorm n) :
    ∃ n₁ n₂ : Y → ℝ, c.IsReflexiveAuxNorm n₁ ∧ c.IsReflexiveAuxNorm n₂ ∧
      ∀ y ∈ c.Y01, n₁ y ≤ n y ∧ n y ≤ n₂ y := by
  obtain ⟨S, hS, hB⟩ := hc
  obtain ⟨N₁, N₂, h₁, h₂, hle⟩ := S.A.E.theorem_12_2_11_sandwich S.paracompact hB (hn S hS)
  refine ⟨S.descend N₁, S.descend N₂, ⟨isAuxNorm_descend hS h₁.toIsAuxNorm, S, hS, ?_⟩,
    ⟨isAuxNorm_descend hS h₂.toIsAuxNorm, S, hS, ?_⟩, ?_⟩
  · rw [S.normOf_descend h₁.toIsAuxNorm.isOneInvariant]; exact h₁
  · rw [S.normOf_descend h₂.toIsAuxNorm.isOneInvariant]; exact h₂
  · intro y hy
    rw [c.Y01_eq hS] at hy
    obtain ⟨e, rfl⟩ := hy
    rw [S.descend_oneToY h₁.toIsAuxNorm.isOneInvariant,
      S.descend_oneToY h₂.toIsAuxNorm.isOneInvariant]
    exact hle e

/-! ### Proposition 16.3.16 -/

/-- **2021 Proposition 16.3.16 (1), p. 727 (2017: Proposition 16.5)**, for every auxiliary norm
(reflexivity is not needed): if `y_k = Γ(q_k)` with `q_k ∈ |W[1]|`, `p(y_k) → z = γ(|x|)` and
`n(y_k) → 0`, then `q_k → |0_x|` in `|W[1]|` (that is, `y_k → 0_z` in `Y_{0,1}`). -/
theorem proposition_16_3_16_one {n : Y → ℝ} (hn : c.IsAuxNorm n)
    {S : StrongPolyfoldBundleStructure p} (hS : ⟦S⟧ = c) {q : ℕ → S.A.E.OneOrbitSpace}
    {x : S.A.Obj} (hp : Tendsto (fun k => p (S.Γ (oneToOrbit S.A (q k)))) atTop
      (𝓝 (S.γ (S.A.X.π x))))
    (h0 : Tendsto (fun k => n (S.Γ (oneToOrbit S.A (q k)))) atTop (𝓝 0)) :
    Tendsto q atTop (𝓝 (Quotient.mk _ (S.A.B.zeroOne x))) := by
  classical
  have hN := hn S hS
  set a : ℕ → S.A.B.One := fun k => (q k).out with ha_def
  have ha : ∀ k, (Quotient.mk _ (a k) : S.A.E.OneOrbitSpace) = q k := fun k => Quotient.out_eq _
  have hpa : ∀ k, p (S.Γ (oneToOrbit S.A (q k))) =
      S.γ (S.A.X.π (S.A.P (S.A.B.oneVal (a k)))) := fun k => by
    rw [← ha k, oneToOrbit_mk, S.p_Γ]
    rfl
  have h1 : Tendsto (fun k => S.A.X.π (S.A.P (S.A.B.oneVal (a k)))) atTop (𝓝 (S.A.X.π x)) := by
    have := (S.γ.symm.continuous.tendsto _).comp hp
    simp only [Function.comp_def, hpa, Homeomorph.symm_apply_apply] at this
    exact this
  obtain ⟨v, hv, hvx⟩ := EpGroupoid.exists_lift_tendsto (X := S.A.X) h1
  have hφ : ∀ k, ∃ φ : S.A.Mor, S.A.X.src φ = S.A.P (S.A.B.oneVal (a k)) ∧
      S.A.X.tgt φ = v k := fun k => (GroupoidStr.π_eq_π_iff _).1 (hv k).symm
  choose φ hφs hφt using hφ
  have hb := fun k => S.A.E.exists_oneVal_eq_μ (a k) (φ k) (hφs k).symm
  choose b hb using hb
  have hπb : ∀ k, S.A.E.toEpGroupoid.π (S.A.B.oneVal (b k)) =
      S.A.E.toEpGroupoid.π (S.A.B.oneVal (a k)) := fun k => by
    rw [hb k, EpStrongBundle.π_μ]
  have hPb : ∀ k, S.A.P (S.A.B.oneVal (b k)) = v k := fun k => by
    rw [hb k, EpStrongBundle.P_μ (E := S.A.E)]
    exact hφt k
  have hNb : ∀ k, S.normOf n (b k) = n (S.Γ (oneToOrbit S.A (q k))) := fun k => by
    change n (S.Γ _) = _
    rw [hπb k, ← ha k, oneToOrbit_mk]
  have hbt : Tendsto b atTop (𝓝 (S.A.B.zeroOne x)) := by
    refine hN.isAuxNorm.tendsto_zeroOne b x ?_ ?_
    · simp only [hPb]; exact hvx
    · simp only [hNb]; exact h0
  have hq : ∀ k, (Quotient.mk _ (b k) : S.A.E.OneOrbitSpace) = q k := fun k =>
    (mk_eq_mk_of_π_eq (hπb k)).trans (ha k)
  have e : q = fun k => (Quotient.mk _ (b k) : S.A.E.OneOrbitSpace) :=
    funext fun k => (hq k).symm
  rw [e]
  exact (continuous_quotient_mk'.tendsto _).comp hbt

/-- **2021 Proposition 16.3.16 (2), p. 728**, with the mixed convergence read in a model `S ∈ c̄`
in which `n` is represented by a reflexive auxiliary norm: `n(y) ≤ liminf n(y_k)`. -/
theorem proposition_16_3_16_two_of_mem {n : Y → ℝ} {S : StrongPolyfoldBundleStructure p}
    (hN : S.A.E.IsReflexiveAuxNorm (S.normOf n)) {y : ℕ → Y} {y₀ : Y}
    (hm : MixedTendstoIn S y y₀) :
    (n y₀ : EReal) ≤ liminf (fun k => (n (y k) : EReal)) atTop := by
  obtain ⟨w, w₀, hw, hw₀, hm⟩ := hm
  have h := hN.le_liminf w w₀ hm
  simp only [normOf, hw, hw₀] at h
  exact h

/-! ### Theorem 16.3.17 -/

variable (c)

/-- An **auxiliary norm of `Y_{0,1}|∂Z`** (Theorem 16.3.17, in the form of Definition 16.3.9): in
every structure, `e ↦ n(Γ(|e|))` is an auxiliary norm over `∂X` (`IsAuxNormOn`, Theorem
12.2.7). -/
def IsAuxNormBoundary (n : Y → ℝ) : Prop :=
  ∀ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c →
    S.A.E.IsAuxNormOn S.A.X.PObj.boundary (S.normOf n)

variable {c}

/-- The points of `Y_{0,1}` over `∂Z` are those `Γ(|e|)` with `P(e) ∈ ∂X`. -/
theorem mem_boundary_iff {S : StrongPolyfoldBundleStructure p} (hS : ⟦S⟧ = c) (e : S.A.B.One) :
    p (S.oneToY e) ∈ c.polyfold.boundary ↔ S.A.P (S.A.B.oneVal e) ∈ S.A.X.PObj.boundary := by
  rw [← hS]
  exact PolyfoldClass.mem_boundary_iff _ S.toPolyfoldStructure rfl
    (S.p_Γ (S.A.E.toEpGroupoid.π (S.A.B.oneVal e))).symm

/-- **2021 Theorem 16.3.17 (1), p. 728 (2017: Theorem 16.4)**: over a tame polyfold, an auxiliary
norm `n` of `Y_{0,1}|∂Z` extends to an auxiliary norm `ñ` of `(p, c̄)` (Theorem 12.2.7 in one
structure, then Theorem 11.5.1). -/
theorem theorem_16_3_17_one (hc : c.IsTame) {n : Y → ℝ} (hn : c.IsAuxNormBoundary n) :
    ∃ ñ : Y → ℝ, c.IsAuxNorm ñ ∧ ∀ y ∈ c.Y01, p y ∈ c.polyfold.boundary → ñ y = n y := by
  obtain ⟨S, hS⟩ := Quotient.exists_rep c
  have hX := (c.isTame_iff.1 hc) S hS
  obtain ⟨Ñ, hÑ, hÑn⟩ := S.A.E.theorem_12_2_7 hX S.paracompact (hn S hS)
  refine ⟨S.descend Ñ, isAuxNorm_descend hS hÑ, fun y hy hb => ?_⟩
  rw [c.Y01_eq hS] at hy
  obtain ⟨e, rfl⟩ := hy
  rw [S.descend_oneToY hÑ.isOneInvariant]
  exact hÑn e ((mem_boundary_iff hS e).1 hb)

/-- **2021 Theorem 16.3.17 (2), p. 728, with the reflexive local step as a hypothesis** (that of
`theorem_12_2_13_hyp`): if `n` is an auxiliary norm of `Y_{0,1}|∂Z` represented in a structure
`S ∈ c̄` with reflexive `1`-fibres by a reflexive auxiliary norm over `∂X` with reflexive local
extensions, it extends to a reflexive auxiliary norm of `(p, c̄)`.  Tameness is not needed. -/
theorem theorem_16_3_17_two_hyp {n : Y → ℝ} (hn : c.IsAuxNormBoundary n)
    {S : StrongPolyfoldBundleStructure p} (hS : ⟦S⟧ = c) (hB : S.A.E.HasReflexiveFibers)
    (hr : S.A.E.IsReflexiveAuxNormOn S.A.X.PObj.boundary (S.normOf n))
    (hloc : EpStrongBundle.HasReflexiveLocalExtensions S.A.X S.A.B (S.normOf n)) :
    ∃ ñ : Y → ℝ, c.IsReflexiveAuxNorm ñ ∧ ∀ y ∈ c.Y01, p y ∈ c.polyfold.boundary → ñ y = n y := by
  have _ := hn
  obtain ⟨Ñ, hÑ, hÑn⟩ := EpStrongBundle.theorem_12_2_13_hyp S.paracompact hB hr hloc
  refine ⟨S.descend Ñ, ⟨isAuxNorm_descend hS hÑ.toIsAuxNorm, S, hS, ?_⟩, fun y hy hb => ?_⟩
  · rw [S.normOf_descend hÑ.toIsAuxNorm.isOneInvariant]; exact hÑ
  · rw [c.Y01_eq hS] at hy
    obtain ⟨e, rfl⟩ := hy
    rw [S.descend_oneToY hÑ.toIsAuxNorm.isOneInvariant]
    exact hÑn e ((mem_boundary_iff hS e).1 hb)

/-- **Satisfiability of the hypotheses of `theorem_16_3_17_two_hyp`**: with reflexive `1`-fibres
there are `n` and `S ∈ c̄` meeting all of them (`n` a reflexive auxiliary norm of Theorem
16.3.15 (1), restricted to `∂Z`). -/
theorem theorem_16_3_17_two_hyp_witness (hc : c.HasReflexiveFibers) :
    ∃ (n : Y → ℝ) (S : StrongPolyfoldBundleStructure p), c.IsAuxNormBoundary n ∧ ⟦S⟧ = c ∧
      S.A.E.HasReflexiveFibers ∧
      S.A.E.IsReflexiveAuxNormOn S.A.X.PObj.boundary (S.normOf n) ∧
      EpStrongBundle.HasReflexiveLocalExtensions S.A.X S.A.B (S.normOf n) := by
  obtain ⟨S, hS, hB⟩ := hc
  obtain ⟨N, hN⟩ := S.A.E.theorem_12_2_11_exists S.paracompact hB
  have hn := isAuxNorm_descend hS hN.toIsAuxNorm
  have e : S.normOf (S.descend N) = N := S.normOf_descend hN.toIsAuxNorm.isOneInvariant
  refine ⟨S.descend N, S, fun S' hS' => (hn S' hS').isAuxNormOn _, hS, hB, ?_, ?_⟩
  · rw [e]; exact hN.isReflexiveAuxNormOn _
  · rw [e]; exact EpStrongBundle.hasReflexiveLocalExtensions_of_isReflexiveAuxNorm hN

end StrongPolyfoldBundle

end Polyfold
