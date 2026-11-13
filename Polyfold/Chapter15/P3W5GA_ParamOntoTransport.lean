import Polyfold.Chapter15.P3W4GP_GeneralPosition
import Polyfold.Chapter15.P3W3K_LinearizationFunctor

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.7** (General Position; 2017: Theorem 15.4), pp. 694–696: the parametrized
reduced surjectivity (15.1) is carried along morphisms.

# (15.1) along morphisms

## The text, paraphrased

At `x ∈ S_f` the proof makes `(v, τ) ↦ f'(x) v + Σ_j τ_j s^g_j(x)` onto `W_x` on `T^R_xX × ℝ^ℓ`,
first for the points of a neighbourhood `V(x)` and then, by the equivariance
`f(g ∗ y) = μ(Γ(g, y), f(y))`, for the points of the saturated set `Q(x)`.  The text uses the
equivariance without comment.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`IsParamOntoVec f x v`**: (15.1) at `x` for given vectors `v_j ∈ W_x`: for every operator `L`
  of `T(f, Λ₀)(x)` and every chart presentation of `T^R_xX`,
  `(u, τ) ↦ L u + Σ_j τ_j v_j` maps `T^R_xX × ℝ^ℓ` onto `W_x`.  `isParamOntoAt_iff_vec`:
  GP's `IsParamOntoAt` is `IsParamOntoVec` for every branch of a linear representation.
* **`IsParamOntoVec.of_mor`**: for a morphism `φ : x → y` and an sc-Fredholm section functor `f`,
  (15.1) at `x` with vectors `v_j` gives (15.1) at `y` with `μ(φ, v_j)`.  Ingredients: the
  functor property of `T(f, Λ₀)` (`theorem_15_1_1_functor`), `T^R_yX = Tφ(T^R_xX)` read in the
  chart transported along `φ` (`chartVec_transport`) with the chart independence of `T^R`
  (`reducedTangentFiber_eq`), and the surjectivity of `μ(φ, ·)` (`muLin_surjective`).
* `transSec_eq_muLin`, `paramSec_transSec_eqOn`: the carried branches of a linear family are
  again linear in `t` (`μ(φ, ·)` is linear on the fibres); `IsLocalRepOn.congr_eqOn`.
* **`IsParamOntoAt.of_mor`**: GP's `IsParamOntoAt f Λ` is carried from `s(φ)` to `t(φ)` for a
  family of functors `Λ_t`; **`IsParamOntoAt.of_mor_inv`** in the other direction.
* `exists_linearRep_of_mor`: a linear representation of `t ↦ Λ_t` around `s(φ)` is carried to
  one around `t(φ)` (only `IsWFunctor` of every `Λ_t` is used).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold

variable {A : SEP.{u}}

/-! ### (15.1) for given vectors -/

/-- **(15.1) at `x` for vectors `v_j ∈ W_x`** (proof of Theorem 15.3.7, p. 696): for every operator
`L` of `T(f, Λ₀)(x)` (the linearization `f'(x)`, Definition 15.1.7 for the trivial multisection)
and every chart presentation of `T^R_xX` (Definition 2.5.8), `(u, τ) ↦ L u + Σ_j τ_j v_j` maps
`T^R_xX × ℝ^ℓ` onto `W_x`. -/
def IsParamOntoVec (f : A.Obj → A.W) (x : A.X.PObj.Level 1) {ℓ : ℕ}
    (v : Fin ℓ → A.P ⁻¹' {A.X.PObj.levelVal 1 x}) : Prop :=
  ∀ L ∈ (linearization f (zeroMultisection A) x).support, ∀ (φ : MChart A.Obj)
    (hφ : A.X.PObj.IsChart φ) (hx : A.X.PObj.levelVal 1 x ∈ φ.source) (m : ℕ)
    (V : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin m → ℝ)).prod V)),
    φ.model.C = T 0 ⁻¹' quadrant m V 0 →
      ∀ w : A.P ⁻¹' {A.X.PObj.levelVal 1 x}, ∃ u ∈ reducedTangentFiber hφ hx T,
        ∃ τ : Fin ℓ → ℝ, L u + ∑ j, τ j • v j = w

/-- **GP's `IsParamOntoAt` is `IsParamOntoVec` for every branch** of a linear representation. -/
theorem isParamOntoAt_iff_vec {f : A.Obj → A.W} {ℓ : ℕ} {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0}
    {x : A.X.PObj.Level 1} :
    IsParamOntoAt f Λ x ↔
      ∃ (O : Set A.Obj) (k : ℕ) (s : Fin k → Fin ℓ → A.Obj → A.W) (σ : Fin k → ℚ≥0)
        (hs : ∀ i j, IsSection A.P (s i j)), IsOpen O ∧ A.X.PObj.levelVal 1 x ∈ O ∧
        (∀ t, IsLocalRepOn A (Λ t) O (fun i => paramSec (s i) t) σ) ∧
        ∀ i, IsParamOntoVec f x (fun j => ⟨s i j (A.X.PObj.levelVal 1 x), hs i j _⟩) := by
  constructor
  · rintro ⟨O, k, s, σ, hs, hO, hx, hr, hon⟩
    exact ⟨O, k, s, σ, hs, hO, hx, hr, fun i L hL φ hφ hxφ m V T hT w =>
      hon L hL φ hφ hxφ m V T hT i w⟩
  · rintro ⟨O, k, s, σ, hs, hO, hx, hr, hon⟩
    exact ⟨O, k, s, σ, hs, hO, hx, hr, fun L hL φ hφ hxφ m V T hT i w =>
      hon i L hL φ hφ hxφ m V T hT w⟩

/-! ### `μ(φ, ·)` is onto -/

/-- **`μ(φ, ·) : W_x → W_y` is onto** (with inverse `μ(φ⁻¹, ·)`). -/
theorem muLin_surjective (φ : A.Mor) {x y : A.Obj} (hx : A.X.src φ = x) (hy : A.X.tgt φ = y) :
    Surjective (muLin φ hx hy) := by
  intro w
  have hw : A.P w = y := w.2
  have h1 : A.P (w : A.W) = A.X.src (A.X.inv φ) := by rw [hw, A.X.src_inv, hy]
  have h2 : A.P (A.E.μ ⟨(A.X.inv φ, (w : A.W)), h1⟩) = x := by
    rw [A.E.P_μ, A.X.tgt_inv, hx]
  refine ⟨⟨A.E.μ ⟨(A.X.inv φ, (w : A.W)), h1⟩, h2⟩, Subtype.ext ?_⟩
  rw [muLin_apply]
  exact A.E.μ_μ_inv φ w h1 _

/-! ### The reduced tangent space along a morphism -/

/-- **`Tφ(T^R_xX) ⊆ T^R_yX`**, read in a chart `c` at `x` and the chart transported along `φ` at
`y` (with the same presentation of the partial quadrant). -/
theorem tangentMorCLE_mem_reducedTangentFiber_transport {φ : A.Mor}
    (hφ : φ ∈ A.X.PMor.levelSet 1) {x y : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x = A.X.src φ) (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ)
    {c : StrongBundleChart A.X.PObj A.P} (hsub : c.φ.source ⊆ (A.X.sheetAt φ).srcSet)
    (hx' : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hy' : A.X.PObj.levelVal 1 y ∈ ((A.E.morIso φ).transportChart c hsub).φ.source)
    {m : ℕ} {V : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin m → ℝ)).prod V))
    {u : A.X.PObj.tangentFiber x} (hu : u ∈ reducedTangentFiber c.isChart hx' T) :
    A.X.tangentMorCLE hφ hx hy u ∈
      reducedTangentFiber ((A.E.morIso φ).transportChart c hsub).isChart hy' T := by
  simp only [reducedTangentFiber, Submodule.mem_comap] at hu ⊢
  rw [fiberCoord_eq_coe] at hu ⊢
  rw [chartVec_transport hφ hx hy hsub hx' hy' u]
  have e : ((A.E.morIso φ).transportChart c hsub).φ (A.X.PObj.levelVal 1 y) =
      c.φ (A.X.PObj.levelVal 1 x) := by
    rw [LocalIso.transportChart_φ_apply, hy, EpStrongBundle.morIso_ϕ_tgt, hx]
  rw [e]
  exact hu

/-! ### (15.1) along a morphism -/

/-- **(15.1) is carried along morphisms**: for an sc-Fredholm section functor `f` and a morphism
`φ : x → y` of level-`1` points, (15.1) at `x` with vectors `v_j` gives (15.1) at `y` with the
vectors `μ(φ, v_j)` (the equivariance step of the proof of Theorem 15.3.7). -/
theorem IsParamOntoVec.of_mor {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (φ : A.Mor) {x y : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x = A.X.src φ)
    (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ) {ℓ : ℕ}
    {v : Fin ℓ → A.P ⁻¹' {A.X.PObj.levelVal 1 x}} (H : IsParamOntoVec f x v) :
    IsParamOntoVec f y (fun j => muLin φ hx.symm hy.symm (v j)) := by
  classical
  intro L' hL' ψ hψ hyψ m' V' T' hT' w
  set hφ := mem_levelSet_one_of_src hx
  -- `L' = μ(φ, ·) ∘ L ∘ (Tφ)⁻¹` for an operator `L` of `T(f, Λ₀)(x)`
  rw [theorem_15_1_1_functor hf (isScPlusMultisection_zeroMultisection A) φ hx hy, grfPush]
    at hL'
  obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hL')
  -- a chart at `x` inside the sheet of `φ`, and its transport to `y`
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
  -- solve at `x`
  obtain ⟨w₀, rfl⟩ := muLin_surjective φ hx.symm hy.symm w
  obtain ⟨u, hu, τ, hτ⟩ := H L hL c.φ c.isChart hx' m₀ V₀ T₀ hT₀ w₀
  refine ⟨A.X.tangentMorCLE hφ hx hy u, ?_, τ, ?_⟩
  · have e := reducedTangentFiber_eq hψ hyψ T' (Lφ.transportChart c hsub).isChart hy' T₀ hT' hT₀
    rw [e]
    exact tangentMorCLE_mem_reducedTangentFiber_transport hφ hx hy hsub hx' hy' T₀ hu
  · rw [conjOp_apply, ContinuousLinearEquiv.symm_apply_apply, ← hτ, map_add, map_sum]
    simp only [map_smul]

/-! ### Carried branches of a linear family -/

/-- On the domain of the carried section, `transSec φ s z = μ(m, s(ϕ z))` with the morphism
`m = (s|sheet)⁻¹(ϕ z) : ϕ z → z`. -/
theorem transSec_eq_muLin {φ : A.Mor} {O : Set A.Obj} (hOs : O ⊆ (A.X.sheetAt φ).srcSet)
    {z : A.Obj} (hz : z ∈ transSet φ O) {s : A.Obj → A.W}
    (hs : A.P (s ((A.E.morIso φ).ϕ z)) = (A.E.morIso φ).ϕ z) :
    ∃ (hsrc : A.X.src ((A.X.sheetAt φ).srcInv ((A.E.morIso φ).ϕ z)) = (A.E.morIso φ).ϕ z)
      (htgt : A.X.tgt ((A.X.sheetAt φ).srcInv ((A.E.morIso φ).ϕ z)) = z),
      transSec φ s z = (muLin ((A.X.sheetAt φ).srcInv ((A.E.morIso φ).ϕ z)) hsrc htgt
        ⟨s ((A.E.morIso φ).ϕ z), hs⟩ : A.W) := by
  set p := (A.E.morIso φ).ϕ z
  have hp : p ∈ (A.X.sheetAt φ).srcSet := hOs hz.2
  have hsrc : A.X.src ((A.X.sheetAt φ).srcInv p) = p :=
    (A.X.sheetAt φ).isScDiffeoOn_src.right_inv p hp
  have hμ : transSec φ s z = A.E.μ ⟨((A.X.sheetAt φ).srcInv p, s p), hs.trans hsrc.symm⟩ := by
    change (A.E.morIso φ).Ψ (s p) = _
    rw [EpStrongBundle.morIso_Ψ, A.E.sectionAct_of_eq _ (by rw [hs]; exact hsrc.symm)]
    exact A.E.μ_congr (Prod.ext (show (A.X.sheetAt φ).srcInv (A.P (s p)) =
      (A.X.sheetAt φ).srcInv p from congrArg _ hs) rfl)
  have htgt : A.X.tgt ((A.X.sheetAt φ).srcInv p) = z := by
    have h1 : A.P (transSec φ s z) = z := by
      have hsec : ∀ y ∈ ({p} : Set A.Obj), A.P (s y) = y := fun y hy => by
        rw [mem_singleton_iff.1 hy]; exact hs
      refine P_transSec (O := {p}) hsec (singleton_subset_iff.2 hp) ⟨hz.1, rfl⟩
    rw [hμ, A.E.P_μ] at h1
    exact h1
  exact ⟨hsrc, htgt, by rw [hμ, muLin_apply]⟩

/-- **The carried branches of a linear family are linear in `t`**: on the domain of the carried
sections, `Σ_j t_j (transSec φ s_j)` (with the carried sections extended by `0`) is the carried
section of `Σ_j t_j s_j`. -/
theorem paramSec_transSec_eqOn {φ : A.Mor} {O : Set A.Obj} (hOs : O ⊆ (A.X.sheetAt φ).srcSet)
    {ℓ : ℕ} {s : Fin ℓ → A.Obj → A.W} (hs : ∀ j, IsSection A.P (s j)) (t : Fin ℓ → ℝ) :
    EqOn (paramSec (fun j => extendZero (transSet φ O) (transSec φ (s j))) t)
      (transSec φ (paramSec s t)) (transSet φ O) := by
  intro z hz
  set p := (A.E.morIso φ).ϕ z
  obtain ⟨hsrc, htgt, e⟩ := transSec_eq_muLin hOs hz (isSection_paramSec s t p)
  rw [e, paramSec_apply (fun j => isSection_extendZero _ _)]
  congr 1
  rw [paramFib hs t p, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  congr 1
  obtain ⟨hsrc', htgt', e'⟩ := transSec_eq_muLin hOs hz (hs j p)
  refine Subtype.ext ?_
  have hsec : ∀ y ∈ transSet φ O, A.P (transSec φ (s j) y) = y := fun y hy => by
    obtain ⟨_, _, e''⟩ := transSec_eq_muLin hOs hy (hs j _)
    rw [e'']
    exact (muLin _ _ _ _).2
  change extendZero (transSet φ O) (transSec φ (s j)) z = _
  rw [← extendZero_eqOn hsec hz, e']

/-- **The carried section at `t(φ)`**: `transSec φ s (t φ) = μ(φ, s(s φ))`. -/
theorem transSec_of_eq_tgt {φ : A.Mor} {z : A.Obj} (hz : z = A.X.tgt φ) {s : A.Obj → A.W}
    (hs : A.P (s (A.X.src φ)) = A.X.src φ) :
    transSec φ s z = A.E.μ ⟨(φ, s (A.X.src φ)), hs⟩ := by
  subst hz
  change (A.E.morIso φ).Ψ (s ((A.E.morIso φ).ϕ (A.X.tgt φ))) = _
  rw [EpStrongBundle.morIso_ϕ_tgt, EpStrongBundle.morIso_Ψ,
    A.E.sectionAct_of_eq _ (by
      rw [hs]; exact ((A.X.sheetAt φ).isScDiffeoOn_src.right_inv _
        (A.X.src_mem_sheetAt φ)).symm)]
  refine A.E.μ_congr (Prod.ext ?_ rfl)
  change (A.X.sheetAt φ).srcInv (A.P (s (A.X.src φ))) = φ
  rw [hs]; exact (A.X.sheetAt φ).isScDiffeoOn_src.left_inv φ (A.X.mem_sheetAt φ)

/-- A local representation is unchanged when its sections are changed off its domain. -/
theorem IsLocalRepOn.congr_eqOn {Λ : A.W → ℚ≥0} {O : Set A.Obj} {k : ℕ}
    {s s' : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (h : IsLocalRepOn A Λ O s σ)
    (hss' : ∀ i, EqOn (s i) (s' i) O) : IsLocalRepOn A Λ O s' σ := by
  refine ⟨h.1, fun i => (h.2.1 i).congr (hss' i), h.2.2.1, fun w hw => ?_⟩
  rw [h.2.2.2 w hw]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hss' i hw]

/-! ### Linear representations and GP's `IsParamOntoAt` along a morphism -/

/-- **A linear representation is carried along a morphism**: if the sections
`Σ_j t_j s_{ij}` with weights `σ_i` represent the functors `Λ_t` on an open `O ∋ s(φ)` for every
`t`, then the carried sections `s'_{ij}` (extended by `0`) represent them on an open
`O' ∋ t(φ)`, again linearly in `t`, with `s'_{ij}(t φ) = μ(φ, s_{ij}(s φ))`. -/
theorem exists_linearRep_of_mor {ℓ : ℕ} {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0}
    (hΛ : ∀ t, IsWFunctor A (Λ t)) (φ : A.Mor) {O : Set A.Obj} (hO : IsOpen O)
    (hxO : A.X.src φ ∈ O) {k : ℕ} {s : Fin k → Fin ℓ → A.Obj → A.W} {σ : Fin k → ℚ≥0}
    (hs : ∀ i j, IsSection A.P (s i j))
    (hr : ∀ t, IsLocalRepOn A (Λ t) O (fun i => paramSec (s i) t) σ) :
    ∃ (O' : Set A.Obj) (s' : Fin k → Fin ℓ → A.Obj → A.W), IsOpen O' ∧ A.X.tgt φ ∈ O' ∧
      (∀ i j, IsSection A.P (s' i j)) ∧
      (∀ t, IsLocalRepOn A (Λ t) O' (fun i => paramSec (s' i) t) σ) ∧
      ∀ i j, s' i j (A.X.tgt φ) = A.E.μ ⟨(φ, s i j (A.X.src φ)), hs i j _⟩ := by
  set Lφ := A.E.morIso φ
  set O₁ := O ∩ (A.X.sheetAt φ).srcSet
  have hO₁ : IsOpen O₁ := hO.inter Lφ.isOpen_U'
  have hO₁s : O₁ ⊆ (A.X.sheetAt φ).srcSet := inter_subset_right
  have hyO : A.X.tgt φ ∈ transSet φ O₁ := by
    refine ⟨A.X.tgt_mem_sheetAt φ, ?_⟩
    change Lφ.ϕ (A.X.tgt φ) ∈ O₁
    rw [EpStrongBundle.morIso_ϕ_tgt]
    exact ⟨hxO, A.X.src_mem_sheetAt φ⟩
  refine ⟨transSet φ O₁, fun i j => extendZero (transSet φ O₁) (transSec φ (s i j)),
    isOpen_transSet φ hO₁, hyO, fun i j => isSection_extendZero _ _, fun t => ?_,
    fun i j => ?_⟩
  · refine (isLocalRepOn_transSec (hΛ t) hO₁ hO₁s ((hr t).mono hO₁ inter_subset_left)).congr_eqOn
      fun i => ?_
    exact (paramSec_transSec_eqOn hO₁s (hs i) t).symm
  · have hsec : ∀ z ∈ O₁, A.P (s i j z) = z := fun z _ => hs i j z
    change extendZero (transSet φ O₁) (transSec φ (s i j)) (A.X.tgt φ) = _
    rw [← extendZero_eqOn (fun z hz => P_transSec hsec hO₁s hz) hyO]
    exact transSec_of_eq_tgt rfl (hs i j _)

/-- **GP's (15.1) is carried along morphisms**: for an sc-Fredholm section functor `f`, a family
`t ↦ Λ_t` of functors and a morphism `φ : x → y` of level-`1` points, `IsParamOntoAt f Λ x`
gives `IsParamOntoAt f Λ y` (with the linear representation carried along `φ`). -/
theorem IsParamOntoAt.of_mor {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f) {ℓ : ℕ}
    {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0} (hΛ : ∀ t, IsWFunctor A (Λ t)) (φ : A.Mor)
    {x y : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x = A.X.src φ)
    (hy : A.X.PObj.levelVal 1 y = A.X.tgt φ) (H : IsParamOntoAt f Λ x) :
    IsParamOntoAt f Λ y := by
  obtain ⟨O, k, s, σ, hs, hO, hxO, hr, hon⟩ := isParamOntoAt_iff_vec.1 H
  obtain ⟨O', s', hO', hyO', hs', hr', hval⟩ :=
    exists_linearRep_of_mor hΛ φ hO (hx ▸ hxO) hs hr
  refine isParamOntoAt_iff_vec.2 ⟨O', k, s', σ, hs', hO', hy ▸ hyO', hr', fun i => ?_⟩
  have h := IsParamOntoVec.of_mor hf φ hx hy (hon i)
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

/-- **GP's (15.1) along a morphism `φ : y → x`**, from the target to the source (through
`φ⁻¹`). -/
theorem IsParamOntoAt.of_mor_inv {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {ℓ : ℕ} {Λ : (Fin ℓ → ℝ) → A.W → ℚ≥0} (hΛ : ∀ t, IsWFunctor A (Λ t)) (φ : A.Mor)
    {x y : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x = A.X.tgt φ)
    (hy : A.X.PObj.levelVal 1 y = A.X.src φ) (H : IsParamOntoAt f Λ x) :
    IsParamOntoAt f Λ y :=
  H.of_mor hf hΛ (A.X.inv φ) (hx.trans (A.X.src_inv φ).symm) (hy.trans (A.X.tgt_inv φ).symm)

end SBLocalization

end Polyfold
