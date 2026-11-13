import Polyfold.Chapter12.P3S_BumpEp
import Polyfold.Chapter10.StrongBundleEquivalence
import Polyfold.Chapter8.Book2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §12.3,
pp. 581–584: **Theorem 12.3.3** (2017: Theorem 12.5), **Remark 12.3.4** and **Remark 12.3.5**
(2017: Remarks 12.4, 12.5).

# Functorial sc⁺-sections through prescribed values

## The text, paraphrased

(Theorem 12.3.3) Let `(P : W → X, μ)` be a strong bundle over an ep-groupoid admitting sc-smooth
bump functions, with `|X|` paracompact, and `N` an auxiliary norm.  For a smooth object `x`, a
smooth `e ∈ W_x` fixed by `G_x` (`μ(g, e) = e`), an open `Ô ∋ |x|` in `|X|` and `ε > 0` there is an
sc⁺-section functor `σ` with (1) `supp σ ⊆ π⁻¹(Ô)`, (2) `σ(t φ) = μ(φ, σ(s φ))`, (3) `σ(x) = e`,
(4) `N(σ(y)) ≤ N(e) + ε` for all `y`.  *Proof*: in a strong bundle chart on `U(x)` (natural
action) take the constant section through `e`; average its `G_x`-translates
`h_g(y) = μ(Γ(g, g⁻¹ ∗ y), h(g⁻¹ ∗ y))` to a `G_x`-equivariant `σ''` with `σ''(x) = e`; cut off by
an invariant bump function; extend to the saturation by the morphisms.
(Remark 12.3.4) Functoriality and transversality compete; without the `G_x`-invariance of `e`
no such `σ` exists.  (Remark 12.3.5) A `G_x`-equivariant local sc⁺-section near `x`, cut off by an
invariant function, extends to all of `X` in a controlled way; any finite-dimensional idea of a
perturbation can be implemented.

## What is formalized (namespace `Polyfold.EpStrongBundle`)

* `secAct hσ φ = μ(φ, σ(s φ))` and `secAct_comp` (`μ(ψ, secAct φ) = secAct(ψ ∘ φ)`).
* **The transport lemma** `exists_isScSmoothOn_one_secAct`: for an sc⁺-section `σ` and `τ : X → 𝐗`
  sc-smooth on an open `N`, `y ↦ μ(τ(y), σ(s τ(y)))` is sc-smooth into `W[1]` on `N` (the
  universal property of the pull-back at level `[1]` and `μ[1]`); `isScPlusSection_of_locally`.
* **The average** `exists_equivariant_average` (the text's `σ''`): from an sc⁺-section `s`
  supported in an invariant `V`, `cl V ⊆ U(x)`, an sc⁺-section `σ''` with
  `σ''(t ψ) = μ(ψ, σ''(s ψ))` for morphisms `ψ` between points of `U(x)`, support in `cl V`,
  `σ''(x) = e` if `s(x) = e` is `G_x`-fixed, and the bound `N(σ'') ≤ b` if `N(s) ≤ b`.
* **Remark 12.3.5 / the extension** `remark_12_3_5` (the extension `natExtension`): an
  sc⁺-section `σ''`, `G_x`-equivariant on `U(x)` and supported in a proper `cl V ⊆ U(x)`, extends
  to an sc⁺-section functor `σ` with `σ = σ''` on `U(x)`, support in the saturation of
  `supp σ''`, and `N(σ) ≤ b` if `N(σ'') ≤ b` (the "controlled" extension).
* **Theorem 12.3.3**: `theorem_12_3_3`.
* **Remark 12.3.4**, its checkable claim: `remark_12_3_4` (a section functor's value at `x` is
  fixed by `G_x`, so the invariance hypothesis on `e` is necessary).

## Reading

* **Bump functions** are taken in the pointwise reading (`AdmitsBumpFunctionsPointwise`,
  `P3S_BumpEp.lean`), which is what the text's use of Proposition 5.5.3 needs; by Theorem 12.3.2
  (1) it is the object M-polyfold's `AdmitsBumpFunctions`, the hypothesis of Part I's Lemma 5.3.3.
* **The local section through `e`** is Part I's Lemma 5.3.3 (`lemma_5_3_3`: an sc⁺-section `s`
  with `s(x) = e`, support in `V(x)` and `N(s) < N(e) + ε`), in place of the text's constant section
  `R(m, e₀)` in a chart followed by a cut-off: the cut-off is built into Lemma 5.3.3 and the bound
  (4) comes from it, which is what "choosing `V(x)` small enough" achieves in the text.  The
  separate cut-off `β · σ''` is then not needed (it would only shrink the support again).
* **Paracompactness of `|X|`** is kept as in the text and not used: the text uses it only for the
  existence of `N`, which is a hypothesis here.
* **"Auxiliary norm"** is Definition 8.3.5 (`EpStrongBundle.IsAuxNorm`, `μ`-invariant).
  The bound (4) is stated on `W_{0,1}`, where `σ` takes its values.
* "`supp σ`" is Part I's `sectionSupport` (closure of `{σ ≠ 0}`).
-/

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u v

/-! ### Sc⁺-sections from local data -/

section Local

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → Z}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PZ P}

namespace StrongBundle

/-- **Sc⁺ is local**: a section which near every point agrees with an sc-smooth map into `Y[1]`
is an sc⁺-section. -/
theorem isScPlusSection_of_locally {σ : Z → Y} (hσ : IsSection P σ)
    (h : ∀ y₀, ∃ N : Set Z, IsOpen N ∧ y₀ ∈ N ∧ ∃ G : Z → B.One,
      PZ.IsScSmoothOn B.toMPolyfold1 G N ∧ ∀ y ∈ N, B.oneVal (G y) = σ y) :
    B.IsScPlusSection σ := by
  choose N hN hyN G hG hGeq using h
  have hmem : ∀ z, σ z ∈ B.oneSet := fun z => hGeq z z (hyN z) ▸ B.oneVal_mem (G z z)
  refine (B.isScPlusSection_iff _).2 ⟨hσ, fun z => B.oneMk _ (hmem z),
    funext fun z => B.oneVal_oneMk _ (hmem z), ?_⟩
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x _ =>
    ⟨N x, hN x, hyN x, subset_univ _, (hG x).congr fun z hz => ?_⟩
  apply B.oneVal_injective
  rw [hGeq x z hz, B.oneVal_oneMk]

/-- An sc⁺-section gives local data on every open set. -/
theorem IsScPlusSection.exists_one {σ : Z → Y} (hσ : B.IsScPlusSection σ) :
    ∃ G : Z → B.One, PZ.IsScSmoothMap B.toMPolyfold1 G ∧ ∀ y, B.oneVal (G y) = σ y := by
  obtain ⟨-, G, hGf, hG⟩ := (B.isScPlusSection_iff σ).1 hσ
  exact ⟨G, hG, fun y => congrFun hGf y⟩

/-- An sc⁺-section is an sc-smooth section. -/
theorem IsScPlusSection.isScSmoothSection' {σ : Z → Y} (hσ : B.IsScPlusSection σ) :
    B.IsScSmoothSection σ := by
  obtain ⟨hs, G, hGf, hG⟩ := (B.isScPlusSection_iff σ).1 hσ
  refine ⟨hs, ?_⟩
  rw [← hGf]
  exact MPolyfold.IsScSmoothMap.comp B.isScSmoothMap_oneVal hG

omit [T2Space Z] [ParacompactSpace Z] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- A section vanishes off its support. -/
theorem eq_fiberZero_of_notMem_sectionSupport {σ : Z → Y} {y : Z}
    (hy : y ∉ sectionSupport P σ) : σ y = fiberZero P y := by
  by_contra h
  exact hy (subset_closure h)

end StrongBundle

end Local

/-! ### Transport along morphisms -/

section Transport

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable (E : EpStrongBundle X B)

/-- `μ(φ, σ(s φ)) ∈ W_{t(φ)}` for a section `σ`. -/
def secAct {σ : Obj → W} (hσ : IsSection P σ) (φ : Mor) : W :=
  E.μ ⟨(φ, σ (X.src φ)), hσ _⟩

variable {E}

/-- Congruence for `μ` on pairs. -/
theorem μ_pair_congr {φ φ' : Mor} {w w' : W} (hφ : φ = φ') (hw : w = w') (h : P w = X.src φ)
    (h' : P w' = X.src φ') : E.μ ⟨(φ, w), h⟩ = E.μ ⟨(φ', w'), h'⟩ := by
  subst hφ hw; rfl

theorem P_secAct {σ : Obj → W} (hσ : IsSection P σ) (φ : Mor) : P (E.secAct hσ φ) = X.tgt φ :=
  E.P_μ _

/-- `μ(ψ, μ(φ, σ(s φ))) = μ(ψ ∘ φ, σ(s(ψ ∘ φ)))`. -/
theorem secAct_comp {σ : Obj → W} (hσ : IsSection P σ) {ψ φ : Mor} (h : X.src ψ = X.tgt φ) :
    E.μ ⟨(ψ, E.secAct hσ φ), (E.P_secAct hσ φ).trans h.symm⟩ = E.secAct hσ (X.comp ψ φ) := by
  exact (E.μ_comp ψ φ (σ (X.src φ)) (hσ _) h).symm.trans
    (E.μ_pair_congr rfl (by rw [X.src_comp ψ φ h]) _ _)

/-- `secAct` of a functorial section is the section at the target. -/
theorem secAct_eq_of_isFunctorialSection {σ : Obj → W} (hσ : IsSection P σ)
    (hfun : E.IsFunctorialSection hσ) (φ : Mor) : E.secAct hσ φ = σ (X.tgt φ) :=
  (hfun φ).symm

/-- `secAct` of the unit. -/
theorem secAct_unit {σ : Obj → W} (hσ : IsSection P σ) (y : Obj) :
    E.secAct hσ (X.unit y) = σ y := by
  unfold secAct
  refine (E.μ_congr ?_).trans (E.μ_unit (σ y))
  change (X.unit y, σ (X.src (X.unit y))) = (X.unit (P (σ y)), σ y)
  rw [X.src_unit, hσ y]

/-- `secAct` of the zero section is zero. -/
theorem secAct_fiberZero (φ : Mor) :
    E.secAct (isSection_fiberZero (P := P)) φ = fiberZero P (X.tgt φ) := by
  have h0 := congrArg Subtype.val ((E.fiberMor φ).map_zero)
  rw [fiberMor_apply] at h0
  exact h0

/-- **The transport lemma**: for an sc⁺-section `σ` and `τ : X → 𝐗` sc-smooth on an open `N`,
`y ↦ μ(τ(y), σ(s τ(y)))` is sc-smooth into `W[1]` on `N`. -/
theorem exists_isScSmoothOn_one_secAct {σ : Obj → W} (hσ : B.IsScPlusSection σ) {τ : Obj → Mor}
    {N : Set Obj} (hτ : X.PObj.IsScSmoothOn X.PMor τ N) :
    ∃ G : Obj → B.One, X.PObj.IsScSmoothOn B.toMPolyfold1 G N ∧
      ∀ y, B.oneVal (G y) = E.secAct hσ.1 (τ y) := by
  classical
  have := B.paracompactSpace_pullback X.PMor X.src
  obtain ⟨Gs, hGs, hGsf⟩ := hσ.exists_one
  have hsmem : ∀ z, σ z ∈ B.oneSet := fun z => hGsf z ▸ B.oneVal_mem (Gs z)
  let ι : Obj → pullbackSpace P X.src := fun y => ⟨(τ y, σ (X.src (τ y))), hσ.1 _⟩
  have hι1 : ∀ y, ι y ∈ (B.pullback X.isScSmoothMap_src).oneSet := fun y =>
    (B.mem_oneSet_pullback_iff X.isScSmoothMap_src _).2 (hsmem _)
  let ι₁ : Obj → (B.pullback X.isScSmoothMap_src).One := fun y =>
    (B.pullback X.isScSmoothMap_src).oneMk (ι y) (hι1 y)
  have ha : X.PObj.IsScSmoothOn X.PMor
      (pullbackProj P X.src ∘ (B.pullback X.isScSmoothMap_src).oneVal ∘ ι₁) N :=
    hτ.congr fun y _ => rfl
  have hb : X.PObj.IsScSmoothOn B.toMPolyfold1
      (B.pullbackProj'One X.isScSmoothMap_src ∘ ι₁) N := by
    refine (MPolyfold.IsScSmoothOn.comp hGs (MPolyfold.IsScSmoothOn.comp X.isScSmoothMap_src hτ
      (mapsTo_univ _ _)) (mapsTo_univ _ _)).congr fun y _ => B.oneVal_injective ?_
    change B.oneVal (Gs (X.src (τ y))) = σ (X.src (τ y))
    exact hGsf _
  have hι₁N := B.isScSmoothOn_to_pullback_one X.isScSmoothMap_src ha hb
  exact ⟨_, MPolyfold.IsScSmoothOn.comp E.isStrongBundleMap.isScSmoothMap_one hι₁N
    (mapsTo_univ _ _), fun y => rfl⟩

/-! #### Fibrewise sums and multiples commute with `μ(ψ, ·)` -/

omit [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj] [TopologicalSpace W] [T2Space W]
  [ParacompactSpace W] [∀ x, Module ℝ (P ⁻¹' {x})] in
theorem isSection_sectionSum {ι : Type*} {I : Finset ι} {s : ι → Obj → W}
    (hs : ∀ i, IsSection P (s i)) : IsSection P (sectionSum P I s) := fun y => by
  rw [sectionSum_apply hs]
  exact (∑ i ∈ I, (⟨s i y, hs i y⟩ : P ⁻¹' {y})).2

omit [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj] [TopologicalSpace W] [T2Space W]
  [ParacompactSpace W] in
theorem isSection_sectionSmul {f : Obj → ℝ} {s : Obj → W} (hs : IsSection P s) :
    IsSection P (sectionSmul P f s) := fun y => by
  rw [sectionSmul_apply hs]
  exact (f y • (⟨s y, hs y⟩ : P ⁻¹' {y})).2

/-- `∑_i s_i(t ψ) = μ(ψ, ∑_i s_i(s ψ))` when `s_{e i}(t ψ) = μ(ψ, s_i(s ψ))` for a
permutation `e`. -/
theorem sectionSum_tgt {ι : Type*} [Fintype ι] {s : ι → Obj → W} (hs : ∀ i, IsSection P (s i))
    (ψ : Mor) (e : ι ≃ ι) (h : ∀ i, s (e i) (X.tgt ψ) = E.secAct (hs i) ψ) :
    sectionSum P Finset.univ s (X.tgt ψ) =
      E.secAct (isSection_sectionSum (I := Finset.univ) hs) ψ := by
  have h1 : (∑ i, (⟨s i (X.tgt ψ), hs i _⟩ : P ⁻¹' {X.tgt ψ})) =
      ∑ i, E.fiberMor ψ ⟨s i (X.src ψ), hs i _⟩ := by
    rw [← Equiv.sum_comp e]
    exact Finset.sum_congr rfl fun i _ => Subtype.ext (by rw [fiberMor_apply]; exact h i)
  rw [sectionSum_apply hs (X.tgt ψ), h1, ← map_sum, fiberMor_apply]
  exact E.μ_pair_congr rfl (sectionSum_apply hs (X.src ψ)).symm _ _

/-- `c · σ(t ψ) = μ(ψ, c · σ(s ψ))` for a constant `c` and `σ(t ψ) = μ(ψ, σ(s ψ))`. -/
theorem sectionSmul_tgt {σ : Obj → W} (hσ : IsSection P σ) (c : ℝ) (ψ : Mor)
    (h : σ (X.tgt ψ) = E.secAct hσ ψ) :
    sectionSmul P (fun _ => c) σ (X.tgt ψ) =
      E.secAct (isSection_sectionSmul (f := fun _ => c) hσ) ψ := by
  have h1 : (⟨σ (X.tgt ψ), hσ _⟩ : P ⁻¹' {X.tgt ψ}) = E.fiberMor ψ ⟨σ (X.src ψ), hσ _⟩ :=
    Subtype.ext (by rw [fiberMor_apply]; exact h)
  rw [sectionSmul_apply hσ (X.tgt ψ), h1, ← map_smul, fiberMor_apply]
  exact E.μ_pair_congr rfl (sectionSmul_apply (f := fun _ => c) hσ (X.src ψ)).symm _ _

end EpStrongBundle

end Transport

/-! ### Auxiliary norms on fibrewise sums -/

section NormBounds

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → Z}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PZ P}

namespace StrongBundle

/-- `N(∑_i v_i) ≤ ∑_i N(v_i)` in a fibre `(Y_{0,1})_y`. -/
theorem IsCompleteFiberNorm.sum_le {N : B.One → ℝ} {y : Z} (hN : B.IsCompleteFiberNorm N y)
    {ι : Type*} (I : Finset ι) (v : ι → B.oneFiber y) :
    N (B.toOne (∑ i ∈ I, v i)) ≤ ∑ i ∈ I, N (B.toOne (v i)) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have h0 := hN.smul 0 0
    rw [zero_smul, abs_zero, zero_mul] at h0
    exact h0.le
  | insert a I ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hN.add_le _ _).trans (add_le_add le_rfl ih)

end StrongBundle

end NormBounds

/-! ### The average and the extension -/

section Construction

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable {E : EpStrongBundle X B}

/-- `N(σ(y)) ≤ b` for every `y` (a bound on `W_{0,1}`; `N = +∞` elsewhere is not attained by
sc⁺-sections). -/
def NormBound (N : B.One → ℝ) (σ : Obj → W) (b : ℝ) : Prop :=
  ∀ y (hy : σ y ∈ B.oneSet), N (B.oneMk (σ y) hy) ≤ b

/-- `N(μ(φ, w)) = N(w)` for an auxiliary norm of Definition 8.3.5. -/
theorem IsAuxNorm.secAct_eq {N : B.One → ℝ} (hN : E.IsAuxNorm N) {σ : Obj → W}
    (hσ : IsSection P σ) (φ : Mor) (h1 : σ (X.src φ) ∈ B.oneSet)
    (h2 : E.secAct hσ φ ∈ B.oneSet) :
    N (B.oneMk (E.secAct hσ φ) h2) = N (B.oneMk (σ (X.src φ)) h1) :=
  hN.map_μ _ (B.oneMk _ h1) φ (hσ _) rfl

open scoped Classical in
/-- The `k`-th translate `h_k(y) = μ(Γ(k, Φ(k⁻¹) y), s(Φ(k⁻¹) y))` on `U(x)`, `0` off `U(x)`. -/
def natTerm (E : EpStrongBundle X B) {x : Obj} (R : X.NaturalRep x) {s : Obj → W}
    (hs : IsSection P s) (k : X.Isotropy x) (y : Obj) : W :=
  if y ∈ R.U then E.secAct hs (R.Γ k (R.Φ k⁻¹ y)) else fiberZero P y

section NatTerm

variable {x : Obj} (R : X.NaturalRep x) {s : Obj → W} (hs : IsSection P s)

theorem natTerm_of_mem (k : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) :
    natTerm E R hs k y = E.secAct hs (R.Γ k (R.Φ k⁻¹ y)) := if_pos hy

theorem natTerm_of_notMem (k : X.Isotropy x) {y : Obj} (hy : y ∉ R.U) :
    natTerm E R hs k y = fiberZero P y := if_neg hy

theorem tgt_Γ_Φ_inv (k : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) :
    X.tgt (R.Γ k (R.Φ k⁻¹ y)) = y := by
  rw [R.tgt_Γ k _ (R.mapsTo_Φ k⁻¹ hy), R.Φ_Φ_inv k hy]

theorem isSection_natTerm (k : X.Isotropy x) : IsSection P (natTerm E R hs k) := fun y => by
  by_cases hy : y ∈ R.U
  · rw [natTerm_of_mem R hs k hy]; exact (P_secAct (E := E) hs _).trans (tgt_Γ_Φ_inv R k hy)
  · rw [natTerm_of_notMem R hs k hy]; exact proj_fiberZero P y

/-- `h_k = 0` off an invariant `V ⊆ U(x)` containing the support of `s`. -/
theorem natTerm_eq_zero {V : Set Obj} (_hVU : V ⊆ R.U) (hVinv : ∀ k, MapsTo (R.Φ k) V V)
    (hsV : sectionSupport P s ⊆ V) (k : X.Isotropy x) {y : Obj} (hy : y ∉ V) :
    natTerm E R hs k y = fiberZero P y := by
  by_cases hyR : y ∈ R.U
  · rw [natTerm_of_mem R hs k hyR]
    have hz : R.Φ k⁻¹ y ∉ V := fun h => hy (by
      have := hVinv k h; rwa [R.Φ_Φ_inv k hyR] at this)
    have hs0 : s (R.Φ k⁻¹ y) = fiberZero P (R.Φ k⁻¹ y) :=
      StrongBundle.eq_fiberZero_of_notMem_sectionSupport fun h => hz (hsV h)
    have hsrc : X.src (R.Γ k (R.Φ k⁻¹ y)) = R.Φ k⁻¹ y := R.src_Γ k _ (R.mapsTo_Φ k⁻¹ hyR)
    unfold secAct
    have e1 := E.secAct_fiberZero (P := P) (R.Γ k (R.Φ k⁻¹ y))
    rw [tgt_Γ_Φ_inv R k hyR] at e1
    refine (E.μ_congr ?_).trans e1
    change (R.Γ k (R.Φ k⁻¹ y), s (X.src (R.Γ k (R.Φ k⁻¹ y)))) =
      (R.Γ k (R.Φ k⁻¹ y), fiberZero P (X.src (R.Γ k (R.Φ k⁻¹ y))))
    rw [hsrc, hs0]
  · exact natTerm_of_notMem R hs k hyR

/-- `h_k` is an sc⁺-section if `s` is one and `supp s ⊆ V`, `cl V ⊆ U(x)`. -/
theorem isScPlusSection_natTerm {V : Set Obj} (hVinv : ∀ k, MapsTo (R.Φ k) V V)
    (hVcl : closure V ⊆ R.U) {s : Obj → W} (hs : B.IsScPlusSection s)
    (hsV : sectionSupport P s ⊆ V) (k : X.Isotropy x) :
    B.IsScPlusSection (natTerm E R hs.1 k) := by
  obtain ⟨G₀, hG₀, hG₀f⟩ := (StrongBundle.isScPlusSection_fiberZero (B := B)).exists_one
  refine StrongBundle.isScPlusSection_of_locally (isSection_natTerm R hs.1 k) fun y₀ => ?_
  by_cases hy₀ : y₀ ∈ R.U
  · have hτ : X.PObj.IsScSmoothOn X.PMor (fun y => R.Γ k (R.Φ k⁻¹ y)) R.U :=
      MPolyfold.IsScSmoothOn.comp (R.isScSmoothOn_Γ k) (R.isScDiffeoOn_Φ k⁻¹).isScSmoothOn
        (R.mapsTo_Φ k⁻¹)
    obtain ⟨G, hG, hGeq⟩ := exists_isScSmoothOn_one_secAct (E := E) hs hτ
    exact ⟨R.U, R.isOpen_U, hy₀, G, hG, fun y hy => by rw [hGeq, natTerm_of_mem R hs.1 k hy]⟩
  · refine ⟨(closure V)ᶜ, isClosed_closure.isOpen_compl, fun h => hy₀ (hVcl h), G₀,
      hG₀.mono isClosed_closure.isOpen_compl (subset_univ _), fun y hy => ?_⟩
    rw [hG₀f, natTerm_eq_zero R hs.1 (subset_closure.trans hVcl) hVinv hsV k
      (fun h => hy (subset_closure h))]

/-- **The equivariance of the translates** (the computation (12.4)–(12.5)): for a morphism `ψ`
between points of `U(x)`, `h_{γ k}(t ψ) = μ(ψ, h_k(s ψ))` with `γ` the index of `ψ`. -/
theorem natTerm_tgt {ψ : Mor} (hψ : ψ ∈ X.morOn R.U) (k : X.Isotropy x) :
    natTerm E R hs (R.index ψ * k) (X.tgt ψ) = E.secAct (isSection_natTerm (E := E) R hs k) ψ := by
  set γ := R.index ψ
  set y := X.src ψ
  have hy : y ∈ R.U := hψ.1
  have hz : R.Φ k⁻¹ y ∈ R.U := R.mapsTo_Φ k⁻¹ hy
  have hψeq : R.Γ γ y = ψ := R.Γ_index hψ
  have hty : X.tgt ψ = R.Φ γ y := R.tgt_eq_Φ_index hψ
  -- the left side: `Φ((γk)⁻¹)(Φ(γ) y) = Φ(k⁻¹) y`
  have hΦ : R.Φ (γ * k)⁻¹ (X.tgt ψ) = R.Φ k⁻¹ y := by
    rw [hty, mul_inv_rev, R.Φ_mul _ _ _ (R.mapsTo_Φ γ hy), R.Φ_inv_Φ γ hy]
  rw [natTerm_of_mem R hs _ hψ.2, hΦ]
  -- the right side: `μ(ψ, μ(Γ(k, z), s z)) = μ(ψ ∘ Γ(k, z), s z)`, `ψ ∘ Γ(k, z) = Γ(γk, z)`
  have hc : X.src ψ = X.tgt (R.Γ k (R.Φ k⁻¹ y)) := (tgt_Γ_Φ_inv R k hy).symm
  have e1 : E.secAct (isSection_natTerm (E := E) R hs k) ψ =
      E.μ ⟨(ψ, E.secAct hs (R.Γ k (R.Φ k⁻¹ y))), (E.P_secAct hs _).trans hc.symm⟩ :=
    E.μ_congr (by
      change (ψ, natTerm E R hs k (X.src ψ)) = (ψ, E.secAct hs (R.Γ k (R.Φ k⁻¹ y)))
      rw [natTerm_of_mem R hs k hy])
  rw [e1, secAct_comp hs hc]
  congr 1
  have hk : R.Φ k (R.Φ k⁻¹ y) = y := R.Φ_Φ_inv k hy
  rw [← hψeq, ← R.Γ_mul γ k hz, hk]

end NatTerm

/-- **The average `σ''`** (proof of Theorem 12.3.3, (12.3) and (12.6)): from an sc⁺-section `s`
supported in an open invariant `V`, `cl V ⊆ U(x)`, the sc⁺-section
`σ'' = |G_x|⁻¹ ∑_k h_k` is `G_x`-equivariant on `U(x)` (`σ''(t ψ) = μ(ψ, σ''(s ψ))` for morphisms
between points of `U(x)`), supported in `cl V`; if `s(x) = e` with `μ(g, e) = e` for `g ∈ G_x`
then `σ''(x) = e`; and `N(σ'') ≤ b` if `N(s) ≤ b`, `b ≥ 0`. -/
theorem exists_equivariant_average {x : Obj} (R : X.NaturalRep x) {V : Set Obj}
    (hVinv : ∀ k, MapsTo (R.Φ k) V V) (hVcl : closure V ⊆ R.U) {s : Obj → W}
    (hs : B.IsScPlusSection s) (hsV : sectionSupport P s ⊆ V) :
    ∃ σ : Obj → W, ∃ hσ : B.IsScPlusSection σ,
      (∀ ψ ∈ X.morOn R.U, σ (X.tgt ψ) = E.secAct hσ.1 ψ) ∧ sectionSupport P σ ⊆ closure V ∧
      ((∀ g : X.Isotropy x, E.μ ⟨(g.val, s x), (hs.1 x).trans g.src_val.symm⟩ = s x) →
        σ x = s x) ∧
      (∀ {N : B.One → ℝ}, E.IsAuxNorm N → ∀ {b : ℝ}, 0 ≤ b → NormBound N s b →
        NormBound N σ b) := by
  classical
  have := Fintype.ofFinite (X.Isotropy x)
  set c : ℝ := (Fintype.card (X.Isotropy x) : ℝ)⁻¹ with hc
  have hcard : (0 : ℝ) < Fintype.card (X.Isotropy x) := Nat.cast_pos.2 Fintype.card_pos
  have hc0 : 0 ≤ c := inv_nonneg.2 hcard.le
  set h := natTerm E R hs.1 with hh
  have hsec : ∀ k, IsSection P (h k) := isSection_natTerm R hs.1
  have hplus : ∀ k, B.IsScPlusSection (h k) := isScPlusSection_natTerm R hVinv hVcl hs hsV
  set S := sectionSum P Finset.univ h with hS
  have hSsec : IsSection P S := isSection_sectionSum hsec
  set σ := sectionSmul P (fun _ => c) S with hσdef
  have hσ : B.IsScPlusSection σ :=
    (StrongBundle.isScPlusSection_sectionSum Finset.univ hplus).smul_left
      (isScSmoothMap_real_const c)
  have hσsec : IsSection P σ := hσ.1
  refine ⟨σ, hσ, fun ψ hψ => ?_, ?_, fun hsx => ?_, fun {N} hN {b} hb hsb => ?_⟩
  · -- equivariance
    have h1 : S (X.tgt ψ) = E.secAct hSsec ψ :=
      sectionSum_tgt hsec ψ (Equiv.mulLeft (R.index ψ)) fun k => natTerm_tgt R hs.1 hψ k
    exact (sectionSmul_tgt hSsec c ψ h1).trans rfl
  · -- support
    refine closure_minimal (fun y hy => ?_) isClosed_closure
    by_contra hyV
    have hyV' : y ∉ V := fun h' => hyV (subset_closure h')
    apply hy
    have hS0 : S y = fiberZero P y := by
      rw [hS, sectionSum_apply hsec]
      have h0 : (∑ k, (⟨h k y, hsec k y⟩ : P ⁻¹' {y})) = 0 := Finset.sum_eq_zero fun k _ =>
        Subtype.ext (natTerm_eq_zero R hs.1 (subset_closure.trans hVcl) hVinv hsV k hyV')
      rw [h0]
      rfl
    have hv0 : (⟨S y, hSsec y⟩ : P ⁻¹' {y}) = 0 := Subtype.ext hS0
    rw [hσdef, sectionSmul_apply hSsec, hv0, smul_zero]
    rfl
  · -- `σ(x) = e`
    have hk : ∀ k, (⟨h k x, hsec k x⟩ : P ⁻¹' {x}) = ⟨s x, hs.1 x⟩ := fun k => Subtype.ext (by
      change natTerm E R hs.1 k x = s x
      rw [natTerm_of_mem R hs.1 k R.mem_U, R.Φ_self, R.Γ_self]
      unfold secAct
      refine (E.μ_congr ?_).trans (hsx k)
      change (k.val, s (X.src k.val)) = (k.val, s x)
      rw [k.src_val])
    have hSx : (⟨S x, hSsec x⟩ : P ⁻¹' {x}) =
        (Fintype.card (X.Isotropy x) : ℝ) • (⟨s x, hs.1 x⟩ : P ⁻¹' {x}) := by
      apply Subtype.ext
      change S x = _
      rw [hS, sectionSum_apply hsec]
      simp only [hk, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul ℝ]
    rw [hσdef, sectionSmul_apply hSsec, hSx, smul_smul, hc, inv_mul_cancel₀ hcard.ne', one_smul]
  · -- the bound
    intro y hy
    have hN1 := hN.isAuxNorm.fiber y
    -- each translate has `N ≤ b`
    have hmem : ∀ k, h k y ∈ B.oneSet := fun k => (hplus k).mem_oneSet y
    have hkb : ∀ k, N (B.oneMk (h k y) (hmem k)) ≤ b := fun k => by
      by_cases hyR : y ∈ R.U
      · have e1 : h k y = E.secAct hs.1 (R.Γ k (R.Φ k⁻¹ y)) := natTerm_of_mem R hs.1 k hyR
        have hm2 : E.secAct hs.1 (R.Γ k (R.Φ k⁻¹ y)) ∈ B.oneSet := e1 ▸ hmem k
        have e2 : B.oneMk (h k y) (hmem k) = B.oneMk _ hm2 := B.oneVal_injective e1
        rw [e2, IsAuxNorm.secAct_eq hN hs.1 _ (hs.mem_oneSet _) hm2]
        exact hsb _ _
      · have e1 : h k y = fiberZero P y := natTerm_of_notMem R hs.1 k hyR
        have e2 : B.oneMk (h k y) (hmem k) = B.zeroOne y :=
          B.oneVal_injective (by rw [B.oneVal_oneMk, B.oneVal_zeroOne, e1])
        rw [e2, (hN1).map_zero]
        exact hb
    -- `σ(y) = c • ∑_k v_k` in `(W_{0,1})_y`
    let v : X.Isotropy x → B.oneFiber y := fun k => ⟨⟨h k y, hsec k y⟩, hmem k⟩
    have hSy : (⟨S y, hSsec y⟩ : P ⁻¹' {y}) = ((∑ k, v k : B.oneFiber y) : P ⁻¹' {y}) := by
      apply Subtype.ext
      change S y = _
      rw [hS, sectionSum_apply hsec, Submodule.coe_sum]
    have hval : σ y = (((c • ∑ k, v k : B.oneFiber y) : P ⁻¹' {y}) : W) := by
      rw [hσdef, sectionSmul_apply hSsec, hSy, Submodule.coe_smul]
    have e3 : B.oneMk (σ y) hy = B.toOne (c • ∑ k, v k) := B.oneVal_injective hval
    rw [e3, hN1.smul, abs_of_nonneg hc0]
    calc c * N (B.toOne (∑ k, v k)) ≤ c * ∑ k, N (B.toOne (v k)) :=
          mul_le_mul_of_nonneg_left (StrongBundle.IsCompleteFiberNorm.sum_le hN1 _ v) hc0
      _ ≤ c * ∑ _k : X.Isotropy x, b :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hkb k) hc0
      _ = b := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hc,
            inv_mul_cancel₀ hcard.ne', one_mul]

open scoped Classical in
/-- The extension of a section on `U(x)` to the saturation: `σ(y) = μ(φ, σ''(s φ))` for some
`φ : z → y` with `z ∈ U(x)`, `0` if there is none. -/
def natExtension (E : EpStrongBundle X B) {x : Obj} (R : X.NaturalRep x) {σ : Obj → W}
    (hσ : IsSection P σ) (y : Obj) : W :=
  if h : ∃ φ : Mor, X.tgt φ = y ∧ X.src φ ∈ R.U then E.secAct hσ h.choose else fiberZero P y

section Extension

variable {x : Obj} (R : X.NaturalRep x) {σ : Obj → W} (hσ : IsSection P σ)

theorem isSection_natExtension : IsSection P (natExtension E R hσ) := fun y => by
  unfold natExtension
  split_ifs with h
  · exact (P_secAct (E := E) hσ _).trans h.choose_spec.1
  · exact proj_fiberZero P y

/-- **Well-definedness** (the morphisms between points of `U(x)` are the `Γ(g, ·)`): for every
`φ : z → y` with `z ∈ U(x)`, `σ(y) = μ(φ, σ''(z))`. -/
theorem natExtension_eq (hequiv : ∀ ψ ∈ X.morOn R.U, σ (X.tgt ψ) = E.secAct hσ ψ) {φ : Mor}
    (hφ : X.src φ ∈ R.U) : natExtension E R hσ (X.tgt φ) = E.secAct hσ φ := by
  have hex : ∃ φ' : Mor, X.tgt φ' = X.tgt φ ∧ X.src φ' ∈ R.U := ⟨φ, rfl, hφ⟩
  unfold natExtension
  rw [dif_pos hex]
  obtain ⟨ht₀, hs₀⟩ := hex.choose_spec
  set φ₀ := hex.choose
  -- `ψ = φ⁻¹ ∘ φ₀ : s φ₀ → s φ` lies between points of `U(x)`
  have hc : X.src (X.inv φ) = X.tgt φ₀ := by rw [X.src_inv, ht₀]
  set ψ := X.comp (X.inv φ) φ₀
  have hψs : X.src ψ = X.src φ₀ := X.src_comp _ _ hc
  have hψt : X.tgt ψ = X.src φ := by rw [X.tgt_comp _ _ hc, X.tgt_inv]
  have hψ : ψ ∈ X.morOn R.U := ⟨hψs ▸ hs₀, hψt ▸ hφ⟩
  have hφψ : X.src φ = X.tgt ψ := hψt.symm
  have e1 : E.secAct hσ φ = E.μ ⟨(φ, E.secAct hσ ψ), (E.P_secAct hσ ψ).trans hφψ.symm⟩ :=
    E.μ_congr (by
      change (φ, σ (X.src φ)) = (φ, E.secAct hσ ψ)
      rw [← hequiv ψ hψ, hψt])
  rw [e1, secAct_comp hσ hφψ]
  congr 1
  have h2 := GroupoidStr.inv_comp_cancel_left (G := X.toGroupoidStr) (φ := X.inv φ) (ψ := φ₀) hc
  rw [GroupoidStr.inv_inv] at h2
  exact h2.symm

/-- On `U(x)` the extension is `σ''`. -/
theorem natExtension_of_mem (hequiv : ∀ ψ ∈ X.morOn R.U, σ (X.tgt ψ) = E.secAct hσ ψ) {y : Obj}
    (hy : y ∈ R.U) : natExtension E R hσ y = σ y := by
  have := natExtension_eq R hσ hequiv (φ := X.unit y) (by rw [X.src_unit]; exact hy)
  rw [X.tgt_unit, secAct_unit] at this
  exact this

/-- Off the saturation of `U(x)` the extension is `0`. -/
theorem natExtension_of_not_exists {y : Obj} (h : ¬ ∃ φ : Mor, X.tgt φ = y ∧ X.src φ ∈ R.U) :
    natExtension E R hσ y = fiberZero P y := dif_neg h

/-- **The extension is functorial**: `σ(t ψ) = μ(ψ, σ(s ψ))` for every morphism `ψ`. -/
theorem natExtension_isFunctorial (hequiv : ∀ ψ ∈ X.morOn R.U, σ (X.tgt ψ) = E.secAct hσ ψ) :
    E.IsFunctorialSection (isSection_natExtension (E := E) R hσ) := by
  intro ψ
  change natExtension E R hσ (X.tgt ψ) = E.secAct (isSection_natExtension (E := E) R hσ) ψ
  by_cases h : ∃ φ : Mor, X.tgt φ = X.src ψ ∧ X.src φ ∈ R.U
  · obtain ⟨φ, hφt, hφs⟩ := h
    have hc : X.src ψ = X.tgt φ := hφt.symm
    have e1 : E.secAct (isSection_natExtension (E := E) R hσ) ψ =
        E.μ ⟨(ψ, E.secAct hσ φ), (E.P_secAct hσ φ).trans hc.symm⟩ :=
      E.μ_congr (by
        change (ψ, natExtension E R hσ (X.src ψ)) = (ψ, E.secAct hσ φ)
        rw [← natExtension_eq R hσ hequiv hφs, hφt])
    rw [e1, secAct_comp hσ hc, ← natExtension_eq R hσ hequiv (φ := X.comp ψ φ)
      (by rw [X.src_comp _ _ hc]; exact hφs), X.tgt_comp _ _ hc]
  · have h' : ¬ ∃ φ : Mor, X.tgt φ = X.tgt ψ ∧ X.src φ ∈ R.U := by
      rintro ⟨φ, hφt, hφs⟩
      have hc : X.src (X.inv ψ) = X.tgt φ := by rw [X.src_inv, hφt]
      exact h ⟨X.comp (X.inv ψ) φ, by rw [X.tgt_comp _ _ hc, X.tgt_inv],
        by rw [X.src_comp _ _ hc]; exact hφs⟩
    rw [natExtension_of_not_exists R hσ h']
    have e1 : E.secAct (isSection_natExtension (E := E) R hσ) ψ =
        E.secAct (isSection_fiberZero (P := P)) ψ :=
      E.μ_congr (by
        change (ψ, natExtension E R hσ (X.src ψ)) = (ψ, fiberZero P (X.src ψ))
        rw [natExtension_of_not_exists R hσ h])
    rw [e1, secAct_fiberZero]

/-- The extension vanishes off the saturation of `supp σ''`. -/
theorem natExtension_eq_zero (hequiv : ∀ ψ ∈ X.morOn R.U, σ (X.tgt ψ) = E.secAct hσ ψ) {y : Obj}
    (hy : y ∉ X.saturation (sectionSupport P σ)) : natExtension E R hσ y = fiberZero P y := by
  by_cases h : ∃ φ : Mor, X.tgt φ = y ∧ X.src φ ∈ R.U
  · obtain ⟨φ, hφt, hφs⟩ := h
    have hz : X.src φ ∉ sectionSupport P σ := fun hz =>
      hy ⟨X.src φ, hz, by rw [X.π_src_eq_π_tgt, hφt]⟩
    rw [← hφt, natExtension_eq R hσ hequiv hφs]
    have e1 : E.secAct hσ φ = E.secAct (isSection_fiberZero (P := P)) φ :=
      E.μ_congr (by
        change (φ, σ (X.src φ)) = (φ, fiberZero P (X.src φ))
        rw [StrongBundle.eq_fiberZero_of_notMem_sectionSupport hz])
    rw [e1, secAct_fiberZero]
  · exact natExtension_of_not_exists R hσ h

end Extension

/-- **Remark 12.3.5, p. 584** (2017: Remark 12.5), the extension: an sc⁺-section `σ''` of the
object bundle, `G_x`-equivariant on `U(x)` (natural action) and supported in `cl V ⊆ U(x)` with
`cl V` proper, extends to an **sc⁺-section functor** `σ` with `σ = σ''` on `U(x)`, support in the
saturation of `supp σ''`, entirely determined by `σ''`, and `N(σ) ≤ b` whenever `N(σ'') ≤ b`,
`b ≥ 0` (the extension is controlled by `N`). -/
theorem remark_12_3_5 {x : Obj} (R : X.NaturalRep x) {V : Set Obj} (hVcl : closure V ⊆ R.U)
    (hVprop : X.IsProperSubset (closure V)) {σ : Obj → W} (hσ : B.IsScPlusSection σ)
    (hequiv : ∀ ψ ∈ X.morOn R.U, σ (X.tgt ψ) = E.secAct hσ.1 ψ)
    (hsupp : sectionSupport P σ ⊆ closure V) :
    E.IsScPlusSectionFunctor (natExtension E R hσ.1) ∧
      (∀ y ∈ R.U, natExtension E R hσ.1 y = σ y) ∧
      sectionSupport P (natExtension E R hσ.1) ⊆ X.saturation (sectionSupport P σ) ∧
      (∀ {N : B.One → ℝ}, E.IsAuxNorm N → ∀ {b : ℝ}, 0 ≤ b → NormBound N σ b →
        NormBound N (natExtension E R hσ.1) b) := by
  classical
  set σe := natExtension E R hσ.1
  have hsec : IsSection P σe := isSection_natExtension (E := E) R hσ.1
  have hprop : X.IsProperSubset (sectionSupport P σ) :=
    hVprop.of_subset hsupp isClosed_closure
  have hcl : IsClosed (X.saturation (sectionSupport P σ)) :=
    X.isClosed_saturation_of_isProperSubset hprop
  have hzero : ∀ {y}, y ∉ X.saturation (sectionSupport P σ) → σe y = fiberZero P y :=
    fun hy => natExtension_eq_zero R hσ.1 hequiv hy
  -- sc⁺
  have hplus : B.IsScPlusSection σe := by
    obtain ⟨G₀, hG₀, hG₀f⟩ := (StrongBundle.isScPlusSection_fiberZero (B := B)).exists_one
    refine StrongBundle.isScPlusSection_of_locally hsec fun y₀ => ?_
    by_cases hy₀ : y₀ ∈ X.saturation (sectionSupport P σ)
    · -- near `y₀ ≅ z₀ ∈ supp σ''`: `σ = μ(τ(y), σ''(s τ(y)))` on a sheet `τ` of `t`
      obtain ⟨z₀, hz₀, hzy⟩ := hy₀
      obtain ⟨φ₀, hφs, hφt⟩ := X.π_eq_π_iff.1 hzy
      obtain ⟨T, V₂, τ, hφT, hd⟩ := X.isLocalScDiffeo_tgt φ₀
      have hcont : ContinuousOn (X.src ∘ τ) V₂ :=
        X.continuous_src.comp_continuousOn hd.isScSmoothOn_inv.continuousOn
      have hNo : IsOpen (V₂ ∩ (X.src ∘ τ) ⁻¹' R.U) :=
        hcont.isOpen_inter_preimage hd.isScSmoothOn_inv.isOpen R.isOpen_U
      have hτN : X.PObj.IsScSmoothOn X.PMor τ (V₂ ∩ (X.src ∘ τ) ⁻¹' R.U) :=
        hd.isScSmoothOn_inv.mono hNo inter_subset_left
      obtain ⟨G, hG, hGeq⟩ := exists_isScSmoothOn_one_secAct (E := E) hσ hτN
      refine ⟨V₂ ∩ (X.src ∘ τ) ⁻¹' R.U, hNo, ⟨?_, ?_⟩, G, hG, fun y hy => ?_⟩
      · rw [← hφt]; exact hd.mapsTo hφT
      · change X.src (τ y₀) ∈ R.U
        rw [← hφt, hd.left_inv φ₀ hφT, hφs]
        exact hVcl (hsupp hz₀)
      · rw [hGeq]
        have h1 : X.tgt (τ y) = y := hd.right_inv y hy.1
        have h2 := natExtension_eq (E := E) R hσ.1 hequiv (φ := τ y) hy.2
        rw [h1] at h2
        exact h2.symm
    · exact ⟨(X.saturation (sectionSupport P σ))ᶜ, hcl.isOpen_compl, hy₀, G₀,
        hG₀.mono hcl.isOpen_compl (subset_univ _), fun y hy => by rw [hG₀f, hzero hy]⟩
  refine ⟨⟨⟨StrongBundle.IsScPlusSection.isScSmoothSection' hplus,
    natExtension_isFunctorial R hσ.1 hequiv⟩, hplus⟩,
    fun y hy => natExtension_of_mem R hσ.1 hequiv hy, ?_, fun {N} hN {b} hb hσb => ?_⟩
  · refine closure_minimal (fun y hy => ?_) hcl
    by_contra hy'
    exact hy (hzero hy')
  · intro y hy
    by_cases h : ∃ φ : Mor, X.tgt φ = y ∧ X.src φ ∈ R.U
    · obtain ⟨φ, hφt, hφs⟩ := h
      subst hφt
      have e1 : σe (X.tgt φ) = E.secAct hσ.1 φ := natExtension_eq R hσ.1 hequiv hφs
      have hm2 : E.secAct hσ.1 φ ∈ B.oneSet := e1 ▸ hy
      have e2 : B.oneMk (σe (X.tgt φ)) hy = B.oneMk _ hm2 := B.oneVal_injective e1
      rw [e2, IsAuxNorm.secAct_eq hN hσ.1 φ (hσ.mem_oneSet _) hm2]
      exact hσb _ _
    · have e1 : σe y = fiberZero P y := natExtension_of_not_exists R hσ.1 h
      have e2 : B.oneMk (σe y) hy = B.zeroOne y :=
        B.oneVal_injective (by rw [B.oneVal_oneMk, B.oneVal_zeroOne, e1])
      rw [e2, (hN.isAuxNorm.fiber y).map_zero]
      exact hb

/-- **Theorem 12.3.3, p. 581** (2017: Theorem 12.5): let `X` admit sc-smooth bump functions
(pointwise reading), `|X|` be paracompact and `N` an auxiliary norm (Definition 8.3.5).  For a
smooth object `x`, a smooth `e ∈ W_x` with `μ(g, e) = e` for all `g ∈ G_x`, an open `Ô ∋ |x|` in
`|X|` and `ε > 0` there is an sc⁺-section functor `σ` (so (2) `σ(t φ) = μ(φ, σ(s φ))`) with
(1) `supp σ ⊆ π⁻¹(Ô)`, (3) `σ(x) = e`, (4) `N(σ(y)) ≤ N(e) + ε` for all `y`. -/
theorem theorem_12_3_3 (hbump : X.AdmitsBumpFunctionsPointwise)
    (_hpara : X.HasParacompactOrbitSpace) {N : B.One → ℝ} (hN : E.IsAuxNorm N) {x : Obj}
    (hx : x ∈ X.PObj.smoothSet) {e : W} (he : e ∈ B.toMPolyfold0.smoothSet) (hex : P e = x)
    (hinv : ∀ g : X.Isotropy x, E.μ ⟨(g.val, e), hex.trans g.src_val.symm⟩ = e)
    {O : Set X.OrbitSpace} (hO : IsOpen O) (hxO : X.π x ∈ O) {ε : ℝ} (hε : 0 < ε) :
    ∃ he1 : e ∈ B.oneSet, ∃ σ : Obj → W, E.IsScPlusSectionFunctor σ ∧
      sectionSupport P σ ⊆ X.π ⁻¹' O ∧ σ x = e ∧
      ∀ y (hy : σ y ∈ B.oneSet), N (B.oneMk (σ y) hy) ≤ N (B.oneMk e he1) + ε := by
  obtain ⟨R, V, hVo, hxV, hVinv, hVcl, hRU, hprop⟩ :=
    X.exists_invariant_nhds_of_isOpen x (hO.preimage X.continuous_π) hxO
  obtain ⟨he1, s, hs, hsx, hsV, hsN⟩ :=
    lemma_5_3_3 (EpGroupoid.theorem_12_3_2_1.1 hbump) hN.isAuxNorm hx he hex hε hVo hxV
  have hb : 0 ≤ N (B.oneMk e he1) + ε := add_nonneg (hN.isAuxNorm.nonneg _) hε.le
  obtain ⟨σ, hσ, hequiv, hσV, hσx, hσN⟩ :=
    exists_equivariant_average (E := E) R hVinv hVcl hs hsV
  obtain ⟨hfun, hon, hsupp, hbound⟩ := remark_12_3_5 (E := E) R hVcl hprop hσ hequiv hσV
  have hsx' : ∀ g : X.Isotropy x, E.μ ⟨(g.val, s x), (hs.1 x).trans g.src_val.symm⟩ = s x :=
    fun g => (E.μ_pair_congr rfl hsx _ _).trans ((hinv g).trans hsx.symm)
  refine ⟨he1, natExtension E R hσ.1, hfun, hsupp.trans ?_, ?_, ?_⟩
  · rintro y ⟨z, hz, hzy⟩
    rw [mem_preimage, ← hzy]
    exact hRU (hVcl (hσV hz))
  · rw [hon x R.mem_U, hσx hsx', hsx]
  · exact hbound hN hb (hσN hN hb fun y hy => (hsN y hy).le)

/-- **Remark 12.3.4, p. 584** (2017: Remark 12.4), its checkable claim: the value at `x` of any
section functor is fixed by `G_x`, `μ(g, σ(x)) = σ(x)`; so without the invariance of `e` there
would be no section functor `σ` with `σ(x) = e`.  (The rest of the remark is commentary.) -/
theorem remark_12_3_4 {σ : Obj → W} (hσ : IsSection P σ) (hfun : E.IsFunctorialSection hσ)
    {x : Obj} (g : X.Isotropy x) :
    E.μ ⟨(g.val, σ x), (hσ x).trans g.src_val.symm⟩ = σ x := by
  have h := hfun g.val
  rw [g.tgt_val] at h
  refine Eq.trans ?_ h.symm
  exact E.μ_congr (by
    change (g.val, σ x) = (g.val, σ (X.src g.val))
    rw [g.src_val])

end EpStrongBundle

end Construction

end Polyfold
