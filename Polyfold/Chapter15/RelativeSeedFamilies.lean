import Polyfold.Chapter15.RelativeParametric
import Polyfold.Chapter15.LocalFamilies
import Polyfold.Chapter14.NormControl

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9** (Transversal Extension Theorem; 2017: Theorem 15.5), steps (c)–(d),
pp. 698–699: the atomic parameter families of the local constructions, relative to `Λ₀`.

# The local families relative to `Λ₀`, from seeds

## The text, paraphrased

Away from `∂X` the proof "argues as in Theorem 15.3.7": at a point `x` of `supp(Λ₀ ∘ f)` it takes
sc⁺-sections supported near `x`, away from `∂X`, which together with the images of the operators
of `T(f, Λ₀)(x)` on `T^R_xX` span `W_x`, forms the symmetric atomic family `Λ^x_t`, and uses
that the surjectivity persists at the points of `supp(Λ₀ ∘ f)` near `x` and, by equivariance, on
a saturated open neighbourhood.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `IsParamOntoVecRel f Λ₀ x v`: (15.1) relative to `Λ₀` at `x` for vectors `v_j ∈ W_x`: for every
  operator `L` of `T(f, Λ₀)(x)`, `(u, τ) ↦ L u + Σ_j τ_j v_j` maps `T^R_xX × ℝ^ℓ` onto `W_x`.
* `isParamOntoAtRel_iff_vec`, `IsParamOntoVecRel.of_mor`, `IsParamOntoAtRel.of_mor`: the relative
  (15.1) is the vector form for every branch, and it is carried along morphisms (Theorem 15.1.1
  for `T(f, Λ₀)`).
* `RelGPFamily.saturate`: a relative family on `V` is one on the saturation of `V`.
* `SeedData.isParamOntoAtRel`, `SeedData.relGPFamily`: the atomic family of seeds is a relative
  family on `Q₀ = ⋂_g (U(x) ∩ Φ_g⁻¹ W)` when the relative (15.1) holds with the seeds on
  `supp(Λ₀ ∘ f) ∩ W`.
* `HasLocalParamSeedsRel A f Λ₀ N`: the analytic input: at every `x ∈ supp(Λ₀ ∘ f)`, inside every
  open `O ∋ x` and below every `ε > 0`, finitely many sc⁺-sections supported in `O` with
  `N ≤ ε` and the relative (15.1) at the points of `supp(Λ₀ ∘ f)` near `x`.
* **`exists_relGPFamily_of_seeds`**: at every `x ∈ supp(Λ₀ ∘ f) ∖ ∂X` there is a saturated open
  `Q ∋ x` with a relative family with domain support in `U ∖ ∂X` and `N(Λ_t) ≤ |t|₁ (h − N(Λ₀))`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold Linearization15

variable {A : SEP.{u}}

/-! ### (15.1) relative to `Λ₀` for vectors -/

/-- **(15.1) relative to `Λ₀` at `x` for vectors `v_j ∈ W_x`**: for every operator `L` of
`T(f, Λ₀)(x)` (Definition 15.1.7) and every chart presentation of `T^R_xX` (Definition 2.5.8),
`(u, τ) ↦ L u + Σ_j τ_j v_j` maps `T^R_xX × ℝ^ℓ` onto `W_x`. -/
def IsParamOntoVecRel (f : A.Obj → A.W) (Λ₀ : A.W → ℚ≥0) (x : A.X.PObj.Level 1) {ℓ : ℕ}
    (v : Fin ℓ → A.P ⁻¹' {A.X.PObj.levelVal 1 x}) : Prop :=
  ∀ L ∈ (linearization f Λ₀ x).support, ∀ (φ : MChart A.Obj)
    (hφ : A.X.PObj.IsChart φ) (hx : A.X.PObj.levelVal 1 x ∈ φ.source) (m : ℕ)
    (V : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin m → ℝ)).prod V)),
    φ.model.C = T 0 ⁻¹' quadrant m V 0 →
      ∀ w : A.P ⁻¹' {A.X.PObj.levelVal 1 x}, ∃ u ∈ reducedTangentFiber hφ hx T,
        ∃ τ : Fin ℓ → ℝ, L u + ∑ j, τ j • v j = w

/-- **`IsParamOntoAtRel` is `IsParamOntoVecRel` for every branch** of a linear representation. -/
theorem isParamOntoAtRel_iff_vec {f : A.Obj → A.W} {Λ₀ : A.W → ℚ≥0} {ℓ : ℕ}
    {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0} {x : A.X.PObj.Level 1} :
    IsParamOntoAtRel f Λ₀ Λ x ↔
      ∃ (O : Set A.Obj) (k : ℕ) (s : Fin k → Fin ℓ → A.Obj → A.W) (σ : Fin k → ℚ≥0)
        (hs : ∀ i j, IsSection A.P (s i j)), IsOpen O ∧ A.X.PObj.levelVal 1 x ∈ O ∧
        (∀ t, IsLocalRepOn A (Λ t) O (fun i => paramSec (s i) t) σ) ∧
        ∀ i, IsParamOntoVecRel f Λ₀ x (fun j => ⟨s i j (A.X.PObj.levelVal 1 x), hs i j _⟩) := by
  constructor
  · rintro ⟨O, k, s, σ, hs, hO, hx, hr, hon⟩
    exact ⟨O, k, s, σ, hs, hO, hx, hr, fun i L hL φ hφ hxφ m V T hT w =>
      hon L hL φ hφ hxφ m V T hT i w⟩
  · rintro ⟨O, k, s, σ, hs, hO, hx, hr, hon⟩
    exact ⟨O, k, s, σ, hs, hO, hx, hr, fun L hL φ hφ hxφ m V T hT i w =>
      hon i L hL φ hφ hxφ m V T hT w⟩

/-- `Λ₀ ∘ f` is constant along morphisms, for a section functor `f` and a functor `Λ₀`. -/
theorem comp_tgt_eq_src {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ₀ : A.W → ℚ≥0} (hΛ₀ : IsScPlusMultisection A Λ₀) (φ : A.Mor) :
    Λ₀ (f (A.X.tgt φ)) = Λ₀ (f (A.X.src φ)) := by
  rw [hf.1.2 φ]
  exact hΛ₀.1 _

/-- **(15.1) relative to `Λ₀` is carried along morphisms**: for an sc-Fredholm section functor
`f`, an sc⁺-multisection `Λ₀` and a morphism `φ : x → y` of level-`1` points, the relative (15.1)
at `x` with vectors `v_j` gives it at `y` with the vectors `μ(φ, v_j)` (Theorem 15.1.1:
`T(f, Λ₀)(y)` is the push-forward of `T(f, Λ₀)(x)`). -/
theorem IsParamOntoVecRel.of_mor {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ₀ : A.W → ℚ≥0} (hΛ₀ : IsScPlusMultisection A Λ₀)
    (φ : A.Mor) {x y : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x = A.X.src φ)
    (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ) {ℓ : ℕ}
    {v : Fin ℓ → A.P ⁻¹' {A.X.PObj.levelVal 1 x}} (H : IsParamOntoVecRel f Λ₀ x v) :
    IsParamOntoVecRel f Λ₀ y (fun j => muLin φ hx.symm hy.symm (v j)) := by
  classical
  intro L' hL' ψ hψ hyψ m' V' T' hT' w
  set hφ := mem_levelSet_one_of_src hx
  rw [theorem_15_1_1_functor hf hΛ₀ φ hx hy, grfPush] at hL'
  obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hL')
  obtain ⟨d⟩ := nonempty_localLinData (isScPlusMultisection_zeroMultisection A) x
  set Lφ := A.E.morIso φ
  have hso : IsOpen (d.c.φ.source ∩ (A.X.sheetAt φ).srcSet) :=
    d.c.φ.isOpen_source.inter Lφ.isOpen_U'
  set c := d.c.restrict inter_subset_left hso
  have hsub : c.φ.source ⊆ (A.X.sheetAt φ).srcSet := fun z hz => hz.2
  have hx' : A.X.PObj.levelVal 1 x ∈ c.φ.source :=
    ⟨d.mem, by rw [hx]; exact A.X.src_mem_sheetAt φ⟩
  have hy' : A.X.PObj.levelVal 1 y ∈ (Lφ.transportChart c hsub).φ.source := by
    refine ⟨by rw [hy]; exact A.X.tgt_mem_sheetAt φ, ?_⟩
    change Lφ.ϕ (A.X.PObj.levelVal 1 y) ∈ c.φ.source
    rw [hy, EpStrongBundle.morIso_ϕ_tgt, ← hx]; exact hx'
  obtain ⟨R₀, -⟩ := c.φ.model.isScRetract
  obtain ⟨m₀, V₀, T₀, hT₀⟩ := R₀.relOpen.isPartialQuadrant
  obtain ⟨w₀, rfl⟩ := muLin_surjective φ hx.symm hy.symm w
  obtain ⟨u, hu, τ, hτ⟩ := H L hL c.φ c.isChart hx' m₀ V₀ T₀ hT₀ w₀
  refine ⟨A.X.tangentMorCLE hφ hx hy u, ?_, τ, ?_⟩
  · have e := reducedTangentFiber_eq hψ hyψ T' (Lφ.transportChart c hsub).isChart hy' T₀ hT' hT₀
    rw [e]
    exact tangentMorCLE_mem_reducedTangentFiber_transport hφ hx hy hsub hx' hy' T₀ hu
  · rw [conjOp_apply, ContinuousLinearEquiv.symm_apply_apply, ← hτ, map_add, map_sum]
    simp only [map_smul]

/-- **The relative (15.1) of a family is carried along morphisms** (with the linear
representation carried along `φ`). -/
theorem IsParamOntoAtRel.of_mor {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ₀ : A.W → ℚ≥0} (hΛ₀ : IsScPlusMultisection A Λ₀) {ℓ : ℕ}
    {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0} (hΛ : ∀ t, IsWFunctor A (Λ t)) (φ : A.Mor)
    {x y : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x = A.X.src φ)
    (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ) (H : IsParamOntoAtRel f Λ₀ Λ x) :
    IsParamOntoAtRel f Λ₀ Λ y := by
  obtain ⟨O, k, s, σ, hs, hO, hxO, hr, hon⟩ := isParamOntoAtRel_iff_vec.1 H
  obtain ⟨O', s', hO', hyO', hs', hr', hval⟩ :=
    exists_linearRep_of_mor hΛ φ hO (hx ▸ hxO) hs hr
  refine isParamOntoAtRel_iff_vec.2 ⟨O', k, s', σ, hs', hO', hy ▸ hyO', hr', fun i => ?_⟩
  have h := IsParamOntoVecRel.of_mor hf hΛ₀ φ hx hy (hon i)
  have hv : (fun j => (⟨s' i j (A.X.PObj.levelVal 1 y), hs' i j _⟩ :
      A.P ⁻¹' {A.X.PObj.levelVal 1 y})) = fun j =>
        muLin φ hx.symm hy.symm ⟨s i j (A.X.PObj.levelVal 1 x), hs i j _⟩ := by
    funext j
    refine Subtype.ext ?_
    change s' i j (A.X.PObj.levelVal 1 y) = _
    rw [muLin_apply, hy, hval i j]
    exact A.E.μ_congr (Prod.ext rfl (congrArg (s i j) hx.symm))
  rw [hv]
  exact h

/-! ### From neighbourhoods to saturated sets -/

variable {f : A.Obj → A.W} {Λ₀ : A.W → ℚ≥0} {N : A.B.One → ℝ} {U : Set A.Obj} {g : A.Obj → ℝ}

/-- **A relative family on `V` is a relative family on the saturation of `V`** (the step "by
equivariance"): the relative (15.1) is carried along morphisms, and so is `supp(Λ₀ ∘ f)`. -/
def RelGPFamily.saturate (hf : A.E.IsScFredholmSectionFunctor f)
    (hΛ₀ : IsScPlusMultisection A Λ₀) {V : Set A.Obj} (F : RelGPFamily A f Λ₀ N U g V) :
    RelGPFamily A f Λ₀ N U g (A.X.saturation V) where
  ℓ := F.ℓ
  Λ := F.Λ
  isStructurable := F.isStructurable
  isLinear := F.isLinear
  norm_le := F.norm_le
  domSupp_subset := F.domSupp_subset
  paramOnto z hz hpos := by
    obtain ⟨a, haV, ha⟩ := hz
    obtain ⟨φ, hφs, hφt⟩ := A.X.π_eq_π_iff.1 ha
    have h1 := src_mem_levelSet_one (z := z) hφt.symm
    have hpa : 0 < Λ₀ (f (A.X.src φ)) := by
      rw [← comp_tgt_eq_src hf hΛ₀ φ, hφt]; exact hpos
    have H := F.paramOnto (A.X.PObj.levelMk 1 (A.X.src φ) h1)
      (by rw [A.X.PObj.levelVal_levelMk, hφs]; exact haV)
      (by rw [A.X.PObj.levelVal_levelMk]; exact hpa)
    exact H.of_mor hf hΛ₀ (fun t => (F.isStructurable t).1.1) φ
      (A.X.PObj.levelVal_levelMk _ _ _) hφt.symm

/-! ### The atomic family of seeds, relative to `Λ₀` -/

namespace SeedData

variable (S : SeedData A)

/-- **The relative (15.1) on `Q₀ = ⋂_g (U(x) ∩ Φ_g⁻¹ W)`**: if it holds with the vectors `s_j(y)`
at the points `y ∈ supp(Λ₀ ∘ f) ∩ W`, then `IsParamOntoAtRel f Λ₀ Λ^x y` holds at the points
`y ∈ supp(Λ₀ ∘ f) ∩ Q₀` (the branch `g` at `y` is `μ(Γ(g, g⁻¹ ∗ y), s_j(g⁻¹ ∗ y))`). -/
theorem isParamOntoAtRel (hf : A.E.IsScFredholmSectionFunctor f)
    (hΛ₀ : IsScPlusMultisection A Λ₀) {W : Set A.Obj}
    (hW : ∀ y : A.X.PObj.Level 1, A.X.PObj.levelVal 1 y ∈ W →
      0 < Λ₀ (f (A.X.PObj.levelVal 1 y)) →
        IsParamOntoVecRel f Λ₀ y
          (fun j => ⟨S.s j (A.X.PObj.levelVal 1 y), (S.isScPlusSection j).1 _⟩))
    (y : A.X.PObj.Level 1) (hyQ : A.X.PObj.levelVal 1 y ∈ ⋂ g, S.R.U ∩ S.R.Φ g ⁻¹' W)
    (hyS : 0 < Λ₀ (f (A.X.PObj.levelVal 1 y))) : IsParamOntoAtRel f Λ₀ S.Λ y := by
  have hyU : A.X.PObj.levelVal 1 y ∈ S.R.U := (mem_iInter.1 hyQ 1).1
  refine isParamOntoAtRel_iff_vec.2 ⟨S.R.U, _, S.branch, _, S.isSection_branch, S.R.isOpen_U,
    hyU, S.isLocalRepOn_branch, fun i => ?_⟩
  set k := (@Fintype.equivFin (A.X.Isotropy S.x) (Fintype.ofFinite _)).symm i
  set m := S.R.Γ k (S.R.Φ k⁻¹ (A.X.PObj.levelVal 1 y))
  have hsrc : A.X.src m = S.R.Φ k⁻¹ (A.X.PObj.levelVal 1 y) :=
    S.R.src_Γ k _ (S.R.mapsTo_Φ k⁻¹ hyU)
  have htgt : A.X.tgt m = A.X.PObj.levelVal 1 y :=
    EpStrongBundle.tgt_Γ_Φ_inv S.R k hyU
  have h1 := src_mem_levelSet_one (z := y) htgt.symm
  have hmS : 0 < Λ₀ (f (A.X.src m)) := by
    rw [← comp_tgt_eq_src hf hΛ₀ m, htgt]; exact hyS
  have hmW : A.X.src m ∈ W := by rw [hsrc]; exact (mem_iInter.1 hyQ k⁻¹).2
  have H := hW (A.X.PObj.levelMk 1 (A.X.src m) h1) (by rwa [A.X.PObj.levelVal_levelMk])
    (by rwa [A.X.PObj.levelVal_levelMk])
  have H' := IsParamOntoVecRel.of_mor hf hΛ₀ m (A.X.PObj.levelVal_levelMk _ _ _) htgt.symm H
  have hv : (fun j => (⟨S.branch i j (A.X.PObj.levelVal 1 y), S.isSection_branch i j _⟩ :
      A.P ⁻¹' {A.X.PObj.levelVal 1 y})) = fun j =>
        muLin m (A.X.PObj.levelVal_levelMk _ _ _).symm htgt
          ⟨S.s j (A.X.PObj.levelVal 1 (A.X.PObj.levelMk 1 (A.X.src m) h1)),
            (S.isScPlusSection j).1 _⟩ := by
    funext j
    refine Subtype.ext ?_
    change EpStrongBundle.natTerm A.E S.R (S.isScPlusSection j).1 k (A.X.PObj.levelVal 1 y) = _
    rw [EpStrongBundle.natTerm_of_mem (E := A.E) S.R _ k hyU, muLin_apply]
    rfl
  rw [hv]
  exact H'

/-- **The atomic family of seeds as a relative family on `Q₀`.** -/
def relGPFamily (h𝒰 : Nonempty A.X.GoodSystem) (hf : A.E.IsScFredholmSectionFunctor f)
    (hΛ₀ : IsScPlusMultisection A Λ₀) (hN : A.E.IsAuxNorm N) {c : ℝ} (hc : 0 ≤ c)
    (hsN : ∀ j y, normW N (S.s j y) ≤ c) (hch : ∀ y ∈ A.X.saturation S.R.U, c ≤ g y)
    (hg0 : ∀ y, 0 ≤ g y) (hUsat : A.X.saturation S.R.U ⊆ U) {W : Set A.Obj}
    (hW : ∀ y : A.X.PObj.Level 1, A.X.PObj.levelVal 1 y ∈ W →
      0 < Λ₀ (f (A.X.PObj.levelVal 1 y)) →
        IsParamOntoVecRel f Λ₀ y
          (fun j => ⟨S.s j (A.X.PObj.levelVal 1 y), (S.isScPlusSection j).1 _⟩)) :
    RelGPFamily A f Λ₀ N U g (⋂ k, S.R.U ∩ S.R.Φ k ⁻¹' W) where
  ℓ := S.ℓ
  Λ := S.Λ
  isStructurable := S.isStructurable_Λ h𝒰
  isLinear := S.isLinearFamily
  norm_le := S.norm_le hN hc hsN hch hg0
  domSupp_subset t := (S.domSupp_Λ_subset t).trans hUsat
  paramOnto := S.isParamOntoAtRel hf hΛ₀ hW

end SeedData

/-! ### The analytic input and the interior local families -/

variable (A) in
/-- **The analytic input of the local constructions relative to `Λ₀`** (steps (c)–(d) of the
proof of Theorem 15.3.9, "argue as in Theorem 15.3.7"), on the object M-polyfold: at every
`x ∈ supp(Λ₀ ∘ f)`, inside every open `O ∋ x` and below every `ε > 0` there are finitely many
sc⁺-sections `s_j` of `W → X` supported in `O` with `N(s_j) ≤ ε`, and an open `W ∋ x` such that
the relative (15.1) holds with the vectors `s_j(y)` at every `y ∈ supp(Λ₀ ∘ f) ∩ W`. -/
def HasLocalParamSeedsRel (f : A.Obj → A.W) (Λ₀ : A.W → ℚ≥0) (N : A.B.One → ℝ) : Prop :=
  ∀ x, 0 < Λ₀ (f x) → ∀ O : Set A.Obj, IsOpen O → x ∈ O → ∀ ε > 0,
    ∃ (ℓ : ℕ) (s : Fin ℓ → A.Obj → A.W) (hs : ∀ j, A.B.IsScPlusSection (s j)),
      (∀ j, sectionSupport A.P (s j) ⊆ O) ∧ (∀ j y, normW N (s j y) ≤ ε) ∧
      ∃ W : Set A.Obj, IsOpen W ∧ x ∈ W ∧ ∀ y : A.X.PObj.Level 1,
        A.X.PObj.levelVal 1 y ∈ W → 0 < Λ₀ (f (A.X.PObj.levelVal 1 y)) →
          IsParamOntoVecRel f Λ₀ y (fun j => ⟨s j (A.X.PObj.levelVal 1 y), (hs j).1 _⟩)

/-- `U ∖ ∂X` is saturated for a saturated `U`. -/
theorem isSaturated_inter_boundary_compl (hU : A.X.IsSaturated U) :
    A.X.IsSaturated (U ∩ A.X.PObj.boundaryᶜ) :=
  A.X.isSaturated_iff.2 fun φ h => ⟨A.X.isSaturated_iff.1 hU φ h.1, fun ht => h.2 (by
    have := A.X.isSaturated_iff.1 isSaturated_boundary (A.X.inv φ)
      (by rw [A.X.src_inv]; exact ht)
    rwa [A.X.tgt_inv] at this)⟩

/-- **The relative local families at the points of `supp(Λ₀ ∘ f) ∖ ∂X`** (steps (c)–(d) of the
proof of Theorem 15.3.9): for a good system, an sc-Fredholm section functor `f`, `(N, U)`
controlling compactness, an sc⁺-multisection `Λ₀` with `dom-supp(Λ₀) ⊆ U` and `N(Λ₀) < h ≤ 1` for
a continuous functor `h`, the relative seeds give at every `x ∈ supp(Λ₀ ∘ f) ∖ ∂X` a saturated
open `Q ∋ x` with a relative family whose domain support lies in `U ∖ ∂X` and whose size is
`N(Λ_t) ≤ |t|₁ (h − N(Λ₀))`. -/
theorem exists_relGPFamily_of_seeds (h𝒰 : Nonempty A.X.GoodSystem)
    (hf : A.E.IsScFredholmSectionFunctor f) (hcc : ControlsCompactness A f N U)
    (hΛ₀ : IsScPlusMultisection A Λ₀) (hdom₀ : domSupp Λ₀ ⊆ U) {h : A.Obj → ℝ}
    (hhc : Continuous h) (hhφ : ∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) (hh1 : ∀ x, h x ≤ 1)
    (hN₀ : ∀ x, pointwiseNorm N Λ₀ x < h x) (H : HasLocalParamSeedsRel A f Λ₀ N) :
    ∀ x ∉ A.X.PObj.boundary, 0 < Λ₀ (f x) → ∃ Q : Set A.Obj, IsOpen Q ∧
      A.X.IsSaturated Q ∧ x ∈ Q ∧ Nonempty (RelGPFamily A f Λ₀ N (U ∩ A.X.PObj.boundaryᶜ)
        (fun y => h y - pointwiseNorm N Λ₀ y) Q) := by
  intro x hxb hx
  have hNB : A.B.IsAuxNorm N := hcc.1.isAuxNorm
  have hxU : x ∈ U := (auxLe_of_pos hf.1.1.1 hΛ₀ hcc.2.2.2.1
    (fun y => (hN₀ y).le.trans (hh1 y)) hdom₀ hx).1
  set c : ℝ := (h x - pointwiseNorm N Λ₀ x) / 4 with hcdef
  set r : ℝ := (h x + pointwiseNorm N Λ₀ x) / 2 with hrdef
  have hc : 0 < c := by have := hN₀ x; rw [hcdef]; linarith
  set W₁ : Set A.Obj := (U ∩ A.X.PObj.boundaryᶜ) ∩
    ({y | pointwiseNorm N Λ₀ y < r} ∩ {y | r + c < h y}) with hW₁def
  have hW₁ : IsOpen W₁ := (hcc.2.1.inter A.X.PObj.isClosed_boundary.isOpen_compl).inter
    ((isOpen_pointwiseNorm_lt hNB hΛ₀ continuous_const).inter (isOpen_lt continuous_const hhc))
  have hxW₁ : x ∈ W₁ := by
    refine ⟨⟨hxU, hxb⟩, ?_, ?_⟩
    · change pointwiseNorm N Λ₀ x < r
      have := hN₀ x; rw [hrdef]; linarith
    · change r + c < h x
      have := hN₀ x; rw [hrdef, hcdef]; linarith
  obtain ⟨R, V, hprop, hRU, hVo, hxV, hVinv, hVcl⟩ := exists_atomicNbhd x hW₁ hxW₁
  obtain ⟨ℓ, s, hs, hsV, hsN, W, hWo, hxW, hW⟩ := H x hx V hVo hxV c hc
  let S : SeedData A := ⟨x, R, hprop, V, hVo, hxV, hVinv, hVcl, ℓ, s, hs, hsV⟩
  have hch : ∀ y ∈ A.X.saturation S.R.U, c ≤ h y - pointwiseNorm N Λ₀ y := by
    rintro y ⟨a, haU, hay⟩
    obtain ⟨φ, hφs, hφt⟩ := A.X.π_eq_π_iff.1 hay
    have e1 : h y = h a := by rw [← hφt, ← hφs, hhφ φ]
    have e2 : pointwiseNorm N Λ₀ y = pointwiseNorm N Λ₀ a := by
      rw [← hφt, ← hφs]; exact pointwiseNorm_tgt hcc.1 hΛ₀ φ
    rw [e1, e2]
    have h1 : pointwiseNorm N Λ₀ a < r := (hRU haU).2.1
    have h2 : r + c < h a := (hRU haU).2.2
    linarith
  have hUsat : A.X.saturation S.R.U ⊆ U ∩ A.X.PObj.boundaryᶜ :=
    EpGroupoid.saturation_subset_of_isSaturated (X := A.X)
      (isSaturated_inter_boundary_compl hcc.2.2.1) (hRU.trans inter_subset_left)
  have hQo : IsOpen (⋂ k, S.R.U ∩ S.R.Φ k ⁻¹' W) := isOpen_iInter_of_finite fun k =>
    (S.R.continuousOn_Φ k).isOpen_inter_preimage S.R.isOpen_U hWo
  have hxQ : x ∈ ⋂ k, S.R.U ∩ S.R.Φ k ⁻¹' W :=
    mem_iInter.2 fun k => ⟨S.R.mem_U, by rw [mem_preimage, S.R.Φ_self]; exact hxW⟩
  exact ⟨A.X.saturation (⋂ k, S.R.U ∩ S.R.Φ k ⁻¹' W),
    EpGroupoid.isOpen_saturation_of_isOpen A.X hQo, EpGroupoid.isSaturated_saturation A.X _,
    A.X.subset_saturation _ hxQ,
    ⟨(S.relGPFamily h𝒰 hf hΛ₀ hcc.1 hc.le hsN hch (fun y => (sub_pos.2 (hN₀ y)).le) hUsat
      hW).saturate hf hΛ₀⟩⟩

end SBLocalization

end Polyfold
