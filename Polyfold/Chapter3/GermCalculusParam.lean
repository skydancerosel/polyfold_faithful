import Polyfold.Chapter3.GermCalculus
import Polyfold.Chapter3.ParamPerturbation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1 and
§3.2, Definitions 3.1.4, 3.1.6, 3.1.11 (preprint 3.4, 3.6, 3.11) and Theorem 3.1.21 (preprint 3.18): **the germ calculus in the strong bundle
charts** — the derivative identities at `0` in the form the linearization files use, the
push-forward by a strong bundle isomorphism, and the product germ `ℝⁿ × G` of Theorem 3.1.21 (preprint 3.18)
(phase 2; Findings, Chapter 3, items 272–274).

# The germ calculus in strong bundle charts

## What is formalized

* **The derivative of the fill defect at `0` in the form of `FillerLinearization.lean`**:
  `fillDefectDeriv_zero_eq` (`Dk(0) = (1 − ρ(0))Dg(0)`, for `g(0) = 0` and `0 ∈ O`),
  `fillDefect_deriv_zero_eq_rho` (every derivative family of the sc¹-germ `[1 − ρ(r(·))]g` has
  this value at `0`: the germ analogue of `IsFillerOf.scDeriv_sub_eq`),
  `IsFillingGerm.exists_kerEquiv` (condition (3) of a filling germ in terms of `Dg(0)`: the germ
  analogue of `IsFillerOf.exists_kerEquiv`), `IsFillingGerm.deriv_comp_r_eq_zero`
  (`(1 − ρ(0))Dg(0)Dr(0) = 0`), `IsFillingGerm.ρ_deriv_comp_r` and
  `IsFillingGerm.proposition_3_1_5` (**Proposition 3.1.5 (preprint 3.5) for a filling germ**: `Dg(0)|_{Dr(0)E}` is
  surjective, Fredholm, iff `Dg(0)` is, with the same index).
* **The push-forward by a strong bundle isomorphism** `Ψ : U ◁ F → U' ◁ F'` with inverse `Ψ'`,
  `ψ(0) = 0`: `IsStrongBundleIso.pullGerm` (the germ `ψ'⁻¹(G) ⊆ U'`),
  `IsStrongBundleIso.pushforward_isScSmoothGerm` (`Ψ_*(k) = (Ψ(ψ'(·), k(ψ'(·))))₂`, the
  `pushforward` of `GoodPositionGerm.lean`, is an sc-smooth germ on `ψ'⁻¹(G)` when `k` is one on
  `G ⊆ U`), `pushforward_isSc1GermWith` (derivative family `pushforwardDeriv`),
  `fiberCompDeriv_zero_eq`, `pushforwardDeriv_zero_eq`, `IsStrongBundleIso.pushforwardDeriv_zero`
  (`D(Ψ_*k)(0) = Γ(0) ∘ Dk(0) ∘ Dψ'(0)` with `Γ(0) = fiberCLM`, the form of
  `IsStrongBundleIso.pushforward_linearization_wholeChart`, whose `S.symm` is `Dψ'(0) = scDeriv U' ψ' 0`).
* **The product germ of Theorem 3.1.21 (preprint 3.18)**: `ScNbhdGerm.univProd` (the germ `Λ × G` in `Λ ⊕ E` with
  quadrant `Λ × C`), `IsQuadrantLike.univ_prod`, `IsSckGerm.univProd`, `IsScSmoothGerm.univProd`
  (`(a, u) ↦ g(u)` is an sc-smooth germ on `Λ × G`), `IsSc1GermWith.univProd` (derivative family
  `Dg(u) ∘ pr₂`), and `PullbackChartData.ofProd_isFillingGerm` (the germ analogue of
  `ofProd_isFillerOf`: a filling germ of `f̂` in a chart `c` gives the filling germ
  `(a, u) ↦ g(u)` of `(a, u) ↦ f̂(u)` in the product chart `(r ↦ r − r₀) × φ`).

## What the text leaves implicit, and the choices made

* The identities at `0` are those of `FillerLinearization.lean` and `FredholmGermLinearization.lean`
  with the whole-chart derivative `scDeriv U g 0` replaced by the value `Dg(0)` of any derivative
  family of the germ `g`; the uniqueness of `Dg(0)` on the germ (`eq_of_uniqueDiffWithinAt`) is
  what makes them well defined.
* In `ofProd_isFillingGerm` the filling germ of `(a, u) ↦ f̂(u)` lives on `ℝⁿ × G` where `G` is
  the germ of the filling of `f̂`; its derivative family is `Dk(u) ∘ pr₂`, so condition (3) is
  the one of `ofProd_isFillerOf` (`ker D(1 × r)(0) = 0 × ker Dr(0)`, `ρ'(0) = ρ(0)`) without any
  uniqueness argument.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

/-! ### The product germ `Λ × G` of Theorem 3.1.21 (preprint 3.18) -/

section UnivProd

variable {E F : ScBanach} {C : Set (E 0)} (Λ : Type) [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
  [FiniteDimensional ℝ Λ]

lemma ScBanach.mem_lvlSet_univ_prod {m : ℕ} (C : Set (E 0)) (p : ((ScBanach.const Λ).prod E) m) :
    p ∈ ((ScBanach.const Λ).prod E).lvlSet (univ ×ˢ C) m ↔ p.2 ∈ E.lvlSet C m := by
  rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase]
  simp [ScBanach.mem_lvlSet]

/-- `Λ × C` is quadrant-like when `C` is. -/
lemma IsQuadrantLike.univ_prod (hC : IsQuadrantLike E C) :
    IsQuadrantLike ((ScBanach.const Λ).prod E) (univ ×ˢ C) where
  zero_mem := ⟨mem_univ _, hC.zero_mem⟩
  convex m := by
    have : ((ScBanach.const Λ).prod E).lvlSet (univ ×ˢ C) m = univ ×ˢ E.lvlSet C m := by
      ext p; rw [ScBanach.mem_lvlSet_univ_prod]; simp
    rw [this]; exact convex_univ.prod (hC.convex m)
  interior_nonempty m := by
    have : ((ScBanach.const Λ).prod E).lvlSet (univ ×ˢ C) m = univ ×ˢ E.lvlSet C m := by
      ext p; rw [ScBanach.mem_lvlSet_univ_prod]; simp
    rw [this, interior_prod_eq, interior_univ]; exact univ_nonempty.prod (hC.interior_nonempty m)

/-- **The product germ `Λ × G`** in `Λ ⊕ E` (constant structure on the finite-dimensional `Λ`),
with levels `Λ × U_m`, around `0 ∈ Λ × C` (the germ of Theorem 3.1.21 (preprint 3.18), `Λ = ℝⁿ`). -/
def ScNbhdGerm.univProd (G₁ : ScNbhdGerm E C) : ScNbhdGerm ((ScBanach.const Λ).prod E) (univ ×ˢ C)
    where
  U m := univ ×ˢ G₁.U m
  nested m x hx := ⟨mem_univ _, G₁.nested m x.2 hx.2⟩
  zero_mem m := ⟨mem_univ _, G₁.zero_mem m⟩
  relOpen m := by
    obtain ⟨O, hO, h⟩ := G₁.relOpen m
    refine ⟨univ ×ˢ O, isOpen_univ.prod hO, ?_⟩
    ext p
    rw [mem_inter_iff, ScBanach.mem_lvlSet_univ_prod, mem_prod, mem_prod, h]
    simp [mem_inter_iff]

@[simp] lemma ScNbhdGerm.univProd_U (G₁ : ScNbhdGerm E C) (m : ℕ) :
    (G₁.univProd Λ).U m = univ ×ˢ G₁.U m := rfl

lemma ScNbhdGerm.univProd_mapsToGerm_snd (G₁ : ScNbhdGerm E C) :
    (G₁.univProd Λ).MapsToGerm G₁ (ScBanach.prodSndOp (ScBanach.const Λ) E 0) := by
  intro m x hx
  rw [ScOperator.levelMap_eq]
  exact hx.2

variable {Λ}

/-- `(a, u) ↦ g(u)` is an sc^k-germ on `Λ × G` when `g` is one on `G`. -/
theorem IsSckGerm.univProd {k : ℕ} (hC : IsQuadrantLike E C) {G₁ : ScNbhdGerm E C}
    {g : E 0 → F 0} (hg : IsSckGerm k G₁ g) :
    IsSckGerm k (G₁.univProd Λ) fun w : ((ScBanach.const Λ).prod E) 0 => g w.2 :=
  IsSckGerm.comp (hC.univ_prod Λ) hC hg
    ((ScBanach.prodSndOp (ScBanach.const Λ) E).isSckGerm k _ (hC.univ_prod Λ))
    (G₁.univProd_mapsToGerm_snd Λ)

/-- `(a, u) ↦ g(u)` is an sc-smooth germ on `Λ × G` when `g` is one on `G`. -/
theorem IsScSmoothGerm.univProd (hC : IsQuadrantLike E C) {G₁ : ScNbhdGerm E C} {g : E 0 → F 0}
    (hg : IsScSmoothGerm G₁ g) :
    IsScSmoothGerm (G₁.univProd Λ) fun w : ((ScBanach.const Λ).prod E) 0 => g w.2 :=
  fun k => (hg k).univProd hC

/-- `(a, u) ↦ g(u)` is an sc¹-germ on `Λ × G` with the derivative family `Dg(u) ∘ pr₂`. -/
theorem IsSc1GermWith.univProd (hC : IsQuadrantLike E C) {G₁ : ScNbhdGerm E C} {g : E 0 → F 0}
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg) :
    IsSc1GermWith (G₁.univProd Λ) (fun w : ((ScBanach.const Λ).prod E) 0 => g w.2)
      fun x => (Dg x.2).comp (ContinuousLinearMap.snd ℝ Λ (E 0)) := by
  have := hg.comp (G₁.relOpenConvex hC 1)
    ((ScBanach.prodSndOp (ScBanach.const Λ) E).isSc1GermWith (G₁.univProd Λ))
    (G₁.univProd_mapsToGerm_snd Λ)
  refine (this.congr fun _ _ => rfl).congr_deriv fun x _ => ?_
  rw [ScOperator.levelMap_eq]
  rfl

end UnivProd

/-! ### Theorem 3.1.21 (preprint 3.18): the filling germ in the product chart -/

section Param

universe u v

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

namespace PullbackChartData

variable (c : StrongBundleChart PX P) (r₀ : Fin n → ℝ)

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- **The filling germ in the product chart (Theorem 3.1.21 (preprint 3.18), the germ reading of
`ofProd_isFillerOf`)**: if the germ `g` on `G` fills `f̂` in the chart `c`, then `(a, u) ↦ g(u)`,
an sc-smooth germ on `ℝⁿ × G`, fills `(a, u) ↦ f̂(u)` in the product chart `(r ↦ r − r₀) × φ`:
`[1 − ρ(r(a, u))]g(u) = [1 − ρ(r(u))]g(u)` does not depend on `a`, so its derivative family
is `Dk(u) ∘ pr₂`, `ker D(1 × r)(0) = 0 × ker Dr(0)` and `ρ'(0) = ρ(0)`. -/
theorem ofProd_isFillingGerm (q₀ : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (h0U : (0 : c.φ.model.E 0) ∈ c.U) (h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O)
    {fb g : c.φ.model.E 0 → c.F 0} (hfill : IsFillingGerm c.relOpen c.isRetraction h0U fb g) :
    IsFillingGerm ((ofProd c r₀).toChart q₀).relOpen ((ofProd c r₀).toChart q₀).isRetraction
      (show (0 : (ofProd c r₀).ψ.model.E 0) ∈ ((ofProd c r₀).toChart q₀).U from ⟨mem_univ _, h0U⟩)
      (fun w => fb w.2) (fun w => g w.2) := by
  have h0U' : (0 : ((ofProd c r₀).toChart q₀).φ.model.E 0) ∈ ((ofProd c r₀).toChart q₀).U :=
    ⟨mem_univ _, h0U⟩
  set c' := (ofProd c r₀).toChart q₀ with hc'
  have hQ := c.relOpen.isPartialQuadrant.isQuadrantLike
  have hU' : IsRelOpenInQuadrant (rnSc n |>.prod c.φ.model.E) (univ ×ˢ c.φ.model.C)
      (univ ×ˢ c.U) := c.relOpen.univ_prod (Fin n → ℝ)
  have ht : Tendsto (fun w : (rnSc n |>.prod c.φ.model.E) 0 => w.2) (𝓝 0) (𝓝 0) :=
    continuous_snd.tendsto' _ _ rfl
  have hrr : ∀ u ∈ c.U, StrongRetr.r c.R (StrongRetr.r c.R u) = StrongRetr.r c.R u :=
    fun u hu => StrongRetr.r_r c.isRetraction hu
  let g' : c'.φ.model.E 0 → c'.F 0 := fun w => g w.2
  -- the fill defect in the product chart is the pull-back of the fill defect along `pr₂`
  have heq : EqOn (fillDefect c.R g ∘ (ScBanach.prodSndOp (rnSc n) c.φ.model.E 0))
      (fillDefect c'.R g') (univ ×ˢ c.U) := by
    intro y hy
    change g y.2 - (c.R (StrongRetr.r c.R y.2, g y.2)).2 =
      g y.2 - (c.R (c.φ (c.φ.symm (StrongRetr.r c.R (StrongRetr.r c.R y.2))), g y.2)).2
    rw [hrr y.2 hy.2, c.φ.apply_symm_apply (c.r_mem_O hy.2)]
  have h0' : (0 : (rnSc n |>.prod c.φ.model.E) 1) ∈
      (rnSc n |>.prod c.φ.model.E).lvlSet (univ ×ˢ c.U) 1 := by
    change (rnSc n |>.prod c.φ.model.E).toBase 1 0 ∈ univ ×ˢ c.U
    rw [map_zero]
    exact ⟨mem_univ _, h0U⟩
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [ht.eventually hfill.eq_on] with w hw hwO
    obtain ⟨v, hv, rfl⟩ := hwO
    exact hw ⟨v.2, hv.2, rfl⟩
  · filter_upwards [ht.eventually hfill.mem_of_fixed] with y hy hyU hfix
    change g y.2 = (c.R (c.φ (c.φ.symm (StrongRetr.r c.R (StrongRetr.r c.R y.2))), g y.2)).2
      at hfix
    rw [hrr y.2 hyU.2, c.φ.apply_symm_apply (c.r_mem_O hyU.2)] at hfix
    obtain ⟨u, hu, hru⟩ := hy hyU.2 hfix
    exact ⟨(y.1, u), ⟨mem_univ _, hu⟩, Prod.ext rfl hru⟩
  · obtain ⟨G, hGU, hg, Dk, hDk, hΦex⟩ := hfill.germ
    -- the germ `ℝⁿ × G`, the germ `(a, u) ↦ g(u)` and the derivative family `Dk(u) ∘ pr₂`
    refine ⟨G.univProd (Fin n → ℝ), fun w hw => ⟨mem_univ _, hGU hw.2⟩, hg.univProd hQ,
      fun x => (Dk x.2).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (c.φ.model.E 0)), ?_, ?_⟩
    · exact (hDk.univProd hQ).congr fun w hw => heq ⟨mem_univ _, hGU hw.2⟩
    set D := scDeriv c.U (StrongRetr.r c.R) (0 : c.φ.model.E 1) with hDdef
    -- `D(1 × r)(0) = 1 × Dr(0)`
    let D' : (Fin n → ℝ) × c.φ.model.E 0 →L[ℝ] (Fin n → ℝ) × c.φ.model.E 0 :=
      scDeriv c'.U (StrongRetr.r c'.R) (0 : c'.φ.model.E 1)
    have hDv : ∀ v : (Fin n → ℝ) × c.φ.model.E 0, D' v = (v.1, D v.2) := by
      intro v
      have h1 := scDeriv_prodMap (F := rnSc n) (F' := c.φ.model.E) (rn_relOpen_univ n) c.relOpen
        (isScSmooth_id (isScDomain_univ (rnSc n)))
        (c.isRetraction.baseRetraction c.relOpen).isScSmooth h0'
      have e := congrArg (fun L : (rnSc n |>.prod c.φ.model.E) 0 →L[ℝ]
        (rnSc n |>.prod c.φ.model.E) 0 => L v) h1
      have h2 : scDeriv (E := rnSc n) (F := rnSc n) univ id (0 : (rnSc n) 1) =
          ContinuousLinearMap.id ℝ (Fin n → ℝ) :=
        IsSc1.scDeriv_eqOn (isSc1With_id univ) ((rn_relOpen_univ n).isScDomain.uniqueDiffWithinAt 1)
          (by rw [ScBanach.mem_lvlSet]; exact mem_univ _)
      refine e.trans (Prod.ext ?_ rfl)
      exact congrArg (fun L : (rnSc n) 0 →L[ℝ] (rnSc n) 0 => L v.1) h2
    -- `ρ'(0) = ρ(0)`
    have hr0 : StrongRetr.r c.R 0 = 0 := StrongRetr.r_eq_self c.isRetraction (c.r_image ▸ h0O)
    let ρ' : c.F 0 →L[ℝ] c.F 0 := StrongRetr.ρCLM c'.isRetraction h0U'
    have hρ0 : ∀ h : c.F 0, ρ' h = StrongRetr.ρCLM c.isRetraction h0U h := by
      intro h
      change (c.R (c.φ (c.φ.symm (StrongRetr.r c.R 0)), h)).2 = (c.R (0, h)).2
      rw [hr0, c.φ.apply_symm_apply h0O]
    -- the kernel `ker (1 × Dr(0)) = 0 × ker Dr(0)`, and `ker ρ'(0) = ker ρ(0)`
    let e₁ : LinearMap.ker (D' : (Fin n → ℝ) × c.φ.model.E 0 →ₗ[ℝ] (Fin n → ℝ) × c.φ.model.E 0)
        ≃L[ℝ] LinearMap.ker (D : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) :=
      { toFun := fun v => ⟨(v : (Fin n → ℝ) × c.φ.model.E 0).2, by
          have h : D' (v : (Fin n → ℝ) × c.φ.model.E 0) = 0 := LinearMap.mem_ker.1 v.2
          rw [hDv] at h
          exact LinearMap.mem_ker.2 (congrArg Prod.snd h)⟩
        invFun := fun u => ⟨((0 : Fin n → ℝ), (u : c.φ.model.E 0)), by
          refine LinearMap.mem_ker.2 ?_
          change D' ((0 : Fin n → ℝ), (u : c.φ.model.E 0)) = 0
          rw [hDv]
          exact Prod.ext rfl (LinearMap.mem_ker.1 u.2)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun v => by
          have h : D' (v : (Fin n → ℝ) × c.φ.model.E 0) = 0 := LinearMap.mem_ker.1 v.2
          rw [hDv] at h
          exact Subtype.ext (Prod.ext (congrArg Prod.fst h).symm rfl)
        right_inv := fun _ => rfl
        continuous_toFun := continuous_induced_rng.2 (continuous_snd.comp continuous_subtype_val)
        continuous_invFun :=
          continuous_induced_rng.2 (continuous_const.prodMk continuous_subtype_val) }
    let e₂ : LinearMap.ker ((StrongRetr.ρCLM c.isRetraction h0U : c.F 0 →L[ℝ] c.F 0) :
          c.F 0 →ₗ[ℝ] c.F 0) ≃L[ℝ] LinearMap.ker (ρ' : c.F 0 →ₗ[ℝ] c.F 0) :=
      { toFun := fun u => ⟨(u : c.F 0), by
          refine LinearMap.mem_ker.2 ?_
          exact (hρ0 u).trans (LinearMap.mem_ker.1 u.2)⟩
        invFun := fun u => ⟨(u : c.F 0), by
          refine LinearMap.mem_ker.2 ?_
          exact (hρ0 u).symm.trans (LinearMap.mem_ker.1 u.2)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := continuous_induced_rng.2 continuous_subtype_val
        continuous_invFun := continuous_induced_rng.2 continuous_subtype_val }
    obtain ⟨Φ, hΦ⟩ := hΦex
    refine ⟨e₁.trans (Φ.trans e₂), fun v => ?_⟩
    exact (hΦ (e₁ v)).trans rfl

end PullbackChartData

end Param

end Polyfold
