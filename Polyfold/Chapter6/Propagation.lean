import Polyfold.Chapter6.LinOrientation
import Polyfold.Chapter6.AddSections
import Polyfold.Chapter6.StabilizationContinuity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 221–226: the **push-forward of orientations** `o ↦ φ_* o` along stabilized kernels, defined
after Lemma 6.6.6 (preprint 6.31), and the two facts behind Proposition 6.6.7 (preprint 6.32) and Lemmas 6.33–6.34: adding sections
and deforming the data over a square do not change it *(book 2017: Lemma 6.14 and after,
Proposition 6.13, Lemmas 6.15–6.16; see `BookConcordance.md`)*.

# The push-forward along stabilized kernels

## The text, paraphrased

Along an sc-smooth path `φ`, with an sc⁺-section `s(·, t)` through `f(φ(t))` and sc⁺-sections
`s₁, …, s_k` with property (P), the tangent spaces `L_t = ker F_t'(φ(t), 0)` form a vector bundle
over `[0, 1]`.  The exact sequence (96) gives `det((f − s(·, t))'(φ(t))) ≅ λ(L_t) ⊗ λ*(ℝᵏ)`; an
orientation `o₀` of `DET(f, φ(0))` gives an orientation of `λ(L₀) ⊗ λ*(ℝᵏ)`, continuation gives one
of `λ(L₁) ⊗ λ*(ℝᵏ)`, and `Φ_{E₁}⁻¹` gives `o₁ = φ_* o₀`.

## What is formalized

* `ChartPoint.stabT`, `ChartPoint.stabPhi`: the operators `T = (f + S)'(x) : T_zO → K_z` and
  `φ(λ) = Σ λᵢ ŝᵢ(x)` in a chart point; `stabT_mem_linSet`; `stabPhi_finAppend` (`φ` of
  `s₁, …, s_k, s̄₁, …, s̄_d` is `appendStab`).
* Auxiliary facts: `stabSign_inv`, `toPerm_stabSign_symm` (`α(T)` is an involution of the rays),
  `rayMap_units_smul`, `stabRayEquiv_trans`, `stabRayEquiv_units_smul`, `rayMap_smul_stabRayEquiv`,
  `equiv_trans_push_aux`, `equiv_trans_congr_mid_aux`, `isFredholm_stabCoprod` (a surjective
  `T ⊕ φ` is Fredholm), `continuous_clm_codRestrict` (corestriction is norm-continuous),
  `propagate_append_of_eq` (`propagate_append` for `φ' = (φ, ψ)`).
* `IsStabKernels f c hc y hy S s Λ`: `Λ` is a continuous family, over a parameter space `Q`, of the
  stabilized kernels `ker(T_q ⊕ φ_q) ⊆ E₀ × ℝᵏ` at the points `y(q)`, read in the chart `c`.
* `IsStabKernels.push`: **the push-forward** `Or_{x₀}^f ≃ Or_{x₁}^f` from `a` to `b`
  (`orEquivRay`, the sign `stabSign`, `propagate`, the sign again, then `orEquivRay⁻¹`).
* `IsStabKernels.orRay`: `o ↦ Φ_{E_q}(α(T_q) o(T_q))`, the orientation read in `λ(Λ_q)`;
  `push_eq_orRay`: `φ_* = orRay_b⁻¹ ∘ cont_{a b} ∘ orRay_a`.
* `IsStabKernels.cont_orRay_path`: along a path with a fixed point and continuously varying data,
  continuation maps `orRay_q o` to `orRay_{q'} o` (from `isLineOrientation_stabRay`).
* `IsStabKernels.comp`, `push_comp`: pulling back along `g : Q' → Q`.
* `IsStabKernels.push_congr`: the push-forward depends only on the data.
* `IsStabKernels.push_trans`: it is compatible with concatenation (`propagate_trans`).
* `IsStabKernels.push_append`: **adding sections** `s̄₁, …, s̄_d` does not change it (Lemma 6.6.8 (preprint 6.33),
  from `propagate_append`).
* `IsStabKernels.push_square`: **the push-forward is unchanged by a deformation** with fixed end
  points `x₀`, `x₁`, along which the end-point operators vary continuously (Lemmas 6.33–6.34 and the
  homotopy argument before Theorem 6.6.11 (preprint 6.35)).

## Reading

The text uses only the data along the path; so does `IsStabKernels`: sections are given pointwise
(`S q`, `s i q` are sections of `P`), and the continuity in `q` is the continuity of the family `Λ`
(which Lemma 6.6.5 (preprint 6.30) provides).  The end points are fixed points `x₀ = y(a)`, `x₁ = y(b)` with chart
points of the chart `c`, so that push-forwards along different families have the same type.  The
text's `f − s` is `f + S` here.  The isomorphism `Φ_E` of formula (94) does not vary continuously
in the topology of `DET` where `dim coker T` jumps, as we read it (`StabilizationContinuity.lean`);
the push-forward uses `α(T) Φ_E` with `α(T) = (−1)^{dim coker T}` (`stabSign`) at both end points,
which does.  For given end-point operators the two differ by the sign `α(T_a) α(T_b)`.
-/

open Module Bundle Topology Set

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- The chart point of the chart `c` at `x` with the level-`1` lift `z` of `φ(x)`. -/
abbrev chartPt (c : StrongBundleChart PX P) (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source)
    (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x) : ChartPoint B x :=
  ⟨c, hc, hx, z, hz⟩

namespace ChartPoint

variable {x : X} (p : ChartPoint B x)

/-- **`T = (f + S)'(x) : T_zO → K_z`** in the chart point, for an sc⁺-section `S` with
`(f + S)(x) = 0` (the text's `(f − s(·, t))'(φ(t))`). -/
def stabT (hf : B.IsScFredholmSection f) {S : X → Y} (hS : B.IsScPlusSection S)
    (hx : IsZeroAt P (sectionAdd P f S) x) : ↥p.T →L[ℝ] ↥p.K :=
  (linAt p.c.U p.c.R (p.c.principal (sectionAdd P f S)) p.z).codRestrict p.K
    fun v => p.scDeriv_mem_K (hf.isScSmooth.sectionAdd hS) hx v

theorem coe_stabT (hf : B.IsScFredholmSection f) {S : X → Y} (hS : B.IsScPlusSection S)
    (hx : IsZeroAt P (sectionAdd P f S) x) (v : ↥p.T) :
    (p.stabT hf hS hx v : p.c.F 0) =
      linAt p.c.U p.c.R (p.c.principal (sectionAdd P f S)) p.z v :=
  rfl

/-- `(f + S)'(x) ∈ Lin(f, x)` at a smooth point. -/
theorem stabT_mem_linSet (hf : B.IsScFredholmSection f) {S : X → Y} (hS : B.IsScPlusSection S)
    (hx : IsZeroAt P (sectionAdd P f S) x) (hxs : x ∈ PX.smoothSet) :
    p.stabT hf hS hx ∈ p.linSet f :=
  ⟨S, hS, hx, 0, p.isScPlusOp_zero hxs, fun v => by simp [coe_stabT]⟩

/-- The principal part of a section at `φ(x)` lies in `K_z`. -/
theorem principal_mem_K {g : X → Y} (hg : IsSection P g) :
    p.c.principal g (p.c.φ x) ∈ p.K := by
  have hO : p.c.φ.model.E.toBase 1 p.z ∈ p.c.φ.model.O := by
    rw [p.toBase_z]; exact p.c.φ.mapsTo_model x p.mem_source
  rw [← p.toBase_z]
  exact (mem_rangeS_ρCLM_iff p.c.isRetraction p.mem_O p.mem_U).2 (p.c.principal_mem_K hg hO)

/-- **`φ(λ) = Σ λᵢ ŝᵢ(x)`** in the chart point, for sections `s₁, …, s_k` (the text's
`λ ↦ Σ λᵢ sᵢ(φ(t), t)`). -/
def stabPhi {k : ℕ} (s : Fin k → X → Y) (hs : ∀ i, IsSection P (s i)) :
    (Fin k → ℝ) →L[ℝ] ↥p.K :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight
    (⟨p.c.principal (s i) (p.c.φ x), p.principal_mem_K (hs i)⟩ : ↥p.K)

theorem coe_stabPhi {k : ℕ} (s : Fin k → X → Y) (hs : ∀ i, IsSection P (s i))
    (μ : Fin k → ℝ) :
    (p.stabPhi s hs μ : p.c.F 0) = ∑ i, μ i • p.c.principal (s i) (p.c.φ x) := by
  simp [stabPhi]

/-- **Appending sections**: `φ` of `s₁, …, s_k, s̄₁, …, s̄_d` is `(φ_s, φ_s̄)` (`appendStab`). -/
theorem stabPhi_finAppend {Q : Type*} {k d : ℕ} (s : Fin k → Q → X → Y) (sbar : Fin d → Q → X → Y)
    (q : Q) (h : ∀ i, IsSection P (Fin.append s sbar i q)) :
    p.stabPhi (fun i => Fin.append s sbar i q) h =
      appendStab (p.stabPhi (fun i => s i q) fun i => by simpa using h (Fin.castAdd d i))
        (p.stabPhi (fun j => sbar j q) fun j => by simpa using h (Fin.natAdd k j)) := by
  refine ContinuousLinearMap.ext fun μ => Subtype.ext ?_
  simp only [appendStab, add_apply, ContinuousLinearMap.comp_apply,
    Submodule.coe_add, coe_stabPhi, restrictCastAdd_apply, restrictNatAdd_apply, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right]

end ChartPoint

/-! ### Auxiliary facts -/

section Aux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- `α(T)⁻¹ = α(T)`. -/
theorem stabSign_inv (T : E →L[ℝ] F) : (stabSign T)⁻¹ = stabSign T := by
  rw [stabSign, ← inv_pow, inv_neg_one]

/-- The action of `α(T)` on rays is an involution. -/
theorem toPerm_stabSign_symm (T : E →L[ℝ] F) {M : Type*} [AddCommMonoid M] [Module ℝ M] :
    (MulAction.toPerm (stabSign T) : Equiv.Perm (Module.Ray ℝ M)).symm =
      MulAction.toPerm (stabSign T) :=
  Equiv.ext fun x => by
    change (stabSign T)⁻¹ • x = stabSign T • x
    rw [stabSign_inv]

/-- `Module.Ray.map` commutes with the action of units. -/
theorem rayMap_units_smul {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] (e : M ≃ₗ[ℝ] N) (u : ℝˣ) (r : Module.Ray ℝ M) :
    Module.Ray.map e (u • r) = u • Module.Ray.map e r := by
  induction r using Module.Ray.ind with | h v hv => ?_
  rw [smul_rayOfNeZero, Module.Ray.map_apply, Module.Ray.map_apply, smul_rayOfNeZero]
  exact rayOfNeZero_eq_of_eq _ _ (by rw [Units.smul_def, Units.smul_def, map_smul])

/-- Regrouping five equivalences (the shape of `push`). -/
theorem equiv_trans_push_aux {A RA LA LB RB B' : Type*} (oa : A ≃ RA) (ua : Equiv.Perm RA)
    (Ra : RA ≃ LA) (c' : LA ≃ LB) (Rb : RB ≃ LB) (ub : Equiv.Perm RB) (ob : B' ≃ RB)
    (hub : ub.symm = ub) :
    (((oa.trans ua).trans ((Ra.trans c').trans Rb.symm)).trans ub).trans ob.symm =
      ((oa.trans ua).trans Ra).trans (c'.trans ((ob.trans ub).trans Rb).symm) := by
  ext x
  simp only [Equiv.trans_apply, Equiv.symm_trans_apply, hub]

/-- Replacing the middle one of five equivalences (the shape of `push`). -/
theorem equiv_trans_congr_mid_aux {A RA RB B' : Type*} (oa : A ≃ RA) (ua : Equiv.Perm RA)
    {P P' : RA ≃ RB} (h : P = P') (ub : Equiv.Perm RB) (ob : B' ≃ RB) :
    (((oa.trans ua).trans P).trans ub).trans ob.symm =
      (((oa.trans ua).trans P').trans ub).trans ob.symm := by
  rw [h]

variable [CompleteSpace E] [CompleteSpace F] {k : ℕ}

/-- A surjective stabilization `T ⊕ φ` of a Fredholm operator is Fredholm. -/
theorem isFredholm_stabCoprod {T : E →L[ℝ] F} {φ : (Fin k → ℝ) →L[ℝ] F}
    (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ)) : (T.coprod φ).IsFredholm := by
  have := hT.finite_ker
  have hr : LinearMap.range ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F) = ⊤ := LinearMap.range_eq_top.2 hφ
  refine isFredholm_of_banach _ finiteDimensional_ker_coprod ?_ ?_
  · change IsClosed (LinearMap.range ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F) : Set F)
    rw [hr, Submodule.top_coe]
    exact isClosed_univ
  · change (LinearMap.range ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F)).CoFG
    rw [hr]
    exact Submodule.CoFG.top

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Corestriction is continuous**: for a family of operators continuous in norm with values in a
subspace `K`, the corestricted family is continuous in norm. -/
theorem continuous_clm_codRestrict {Z M : Type*} [TopologicalSpace Z] [NormedAddCommGroup M]
    [NormedSpace ℝ M] (K : Submodule ℝ F) (A : Z → M →L[ℝ] F) (hA : Continuous A)
    (h : ∀ z v, A z v ∈ K) : Continuous fun z => (A z).codRestrict K (h z) := by
  have heq : (⇑(LinearIsometry.postcomp (E := M) K.subtypeₗᵢ) ∘
      fun z => (A z).codRestrict K (h z)) = A := by
    funext z
    ext v
    rfl
  refine ((LinearIsometry.postcomp (E := M) K.subtypeₗᵢ).isometry.isEmbedding.continuous_iff).2 ?_
  rw [heq]
  exact hA

omit [CompleteSpace E] [CompleteSpace F] in
/-- `λ(e) ∘ Φ_ι = Φ_{e ∘ ι}` on rays. -/
theorem stabRayEquiv_trans {T : E →L[ℝ] F} {φ : (Fin k → ℝ) →L[ℝ] F} (hT : T.IsFredholm)
    (hφ : Function.Surjective (T.coprod φ)) {W W' : Type*} [AddCommGroup W] [Module ℝ W]
    [AddCommGroup W'] [Module ℝ W'] {L : Submodule ℝ W} {L' : Submodule ℝ W'}
    [FiniteDimensional ℝ L] [FiniteDimensional ℝ L']
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] L) (e : L ≃ₗ[ℝ] L') (r : Module.Ray ℝ (fredholmDet T)) :
    stabRayEquiv hT hφ (ι.trans e) r = Module.Ray.map (maxPowEquiv e) (stabRayEquiv hT hφ ι r) := by
  have := hT.finite_ker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  have hm : maxPowEquiv (ι.trans e) = (maxPowEquiv ι).trans (maxPowEquiv e) := by
    apply LinearEquiv.toLinearMap_injective
    rw [LinearEquiv.coe_trans, coe_maxPowEquiv, coe_maxPowEquiv, coe_maxPowEquiv,
      ← maxPowMap_comp]
    rfl
  simp only [stabRayEquiv, Equiv.trans_apply, hm]
  induction r using Module.Ray.ind with | h v hv => ?_
  simp only [Module.Ray.map_apply]
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- `Φ_ι` commutes with the action of units on rays. -/
theorem stabRayEquiv_units_smul {T : E →L[ℝ] F} {φ : (Fin k → ℝ) →L[ℝ] F} (hT : T.IsFredholm)
    (hφ : Function.Surjective (T.coprod φ)) {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Submodule ℝ W} [FiniteDimensional ℝ L]
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] L) (u : ℝˣ) (r : Module.Ray ℝ (fredholmDet T)) :
    stabRayEquiv hT hφ ι (u • r) = u • stabRayEquiv hT hφ ι r := by
  simp only [stabRayEquiv, Equiv.trans_apply, rayMap_units_smul]

omit [CompleteSpace E] [CompleteSpace F] in
/-- `λ(e)(u Φ_ι r) = u Φ_{ι'} r` for `ι' = e ∘ ι`. -/
theorem rayMap_smul_stabRayEquiv {T : E →L[ℝ] F} {φ : (Fin k → ℝ) →L[ℝ] F} (hT : T.IsFredholm)
    (hφ : Function.Surjective (T.coprod φ)) {W W' : Type*} [AddCommGroup W] [Module ℝ W]
    [AddCommGroup W'] [Module ℝ W'] {L : Submodule ℝ W} {L' : Submodule ℝ W'}
    [FiniteDimensional ℝ L] [FiniteDimensional ℝ L']
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] L) (e : L ≃ₗ[ℝ] L')
    (ι' : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] L') (h : ∀ v, ι' v = e (ι v)) (u : ℝˣ) (r : Module.Ray ℝ (fredholmDet T)) :
    Module.Ray.map (maxPowEquiv e) (u • stabRayEquiv hT hφ ι r) =
      stabRayEquiv hT hφ ι' (u • r) := by
  obtain rfl : ι' = ι.trans e := LinearEquiv.ext h
  rw [rayMap_units_smul, ← stabRayEquiv_trans, stabRayEquiv_units_smul]

end Aux

section AppendEq

variable {Q : Type*} [TopologicalSpace Q] [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k d : ℕ}
  {E₀ F₀ E₁ F₁ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [CompleteSpace F₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [CompleteSpace F₁]

omit [CompleteSpace E₀] [CompleteSpace F₀] [CompleteSpace E₁] [CompleteSpace F₁] in
/-- `propagate_append` for stabilizations `φᵢ'` equal to `(φᵢ, ψᵢ)`. -/
theorem propagate_append_of_eq (Λ : SubspaceFamily Q (V × (Fin k → ℝ)))
    (Λ' : SubspaceFamily Q (V × (Fin (k + d) → ℝ)))
    (hM : ∀ q, ∀ v ∈ Λ.L q, ((v.1, Fin.append v.2 0) : V × (Fin (k + d) → ℝ)) ∈ Λ'.L q)
    (hp : ∀ q, (Λ'.L q).map (((restrictNatAdd k d).comp
      (ContinuousLinearMap.snd ℝ V (Fin (k + d) → ℝ)) : V × (Fin (k + d) → ℝ) →L[ℝ] Fin d → ℝ) :
        V × (Fin (k + d) → ℝ) →ₗ[ℝ] Fin d → ℝ) = ⊤)
    (hn : Λ.n + d = Λ'.n) (q₀ q₁ : Q)
    {T₀ : E₀ →L[ℝ] F₀} {φ₀ : (Fin k → ℝ) →L[ℝ] F₀} {ψ₀ : (Fin d → ℝ) →L[ℝ] F₀}
    (hT₀ : T₀.IsFredholm) (hφ₀ : Function.Surjective (T₀.coprod φ₀))
    (j₀ : E₀ →L[ℝ] V) (hj₀ : Function.Injective j₀)
    (hΛ₀ : Λ.L q₀ = (LinearMap.ker ((T₀.coprod φ₀ : E₀ × (Fin k → ℝ) →L[ℝ] F₀) :
      E₀ × (Fin k → ℝ) →ₗ[ℝ] F₀)).map ((j₀.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        E₀ × (Fin k → ℝ) →L[ℝ] V × (Fin k → ℝ)) : E₀ × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ)))
    {φ₀' : (Fin (k + d) → ℝ) →L[ℝ] F₀} (he₀ : φ₀' = appendStab φ₀ ψ₀)
    (hφ₀' : Function.Surjective (T₀.coprod φ₀'))
    (hΛ'₀ : Λ'.L q₀ = (LinearMap.ker ((T₀.coprod φ₀' :
      E₀ × (Fin (k + d) → ℝ) →L[ℝ] F₀) : E₀ × (Fin (k + d) → ℝ) →ₗ[ℝ] F₀)).map
        ((j₀.prodMap (ContinuousLinearMap.id ℝ (Fin (k + d) → ℝ)) :
          E₀ × (Fin (k + d) → ℝ) →L[ℝ] V × (Fin (k + d) → ℝ)) :
            E₀ × (Fin (k + d) → ℝ) →ₗ[ℝ] V × (Fin (k + d) → ℝ)))
    {T₁ : E₁ →L[ℝ] F₁} {φ₁ : (Fin k → ℝ) →L[ℝ] F₁} {ψ₁ : (Fin d → ℝ) →L[ℝ] F₁}
    (hT₁ : T₁.IsFredholm) (hφ₁ : Function.Surjective (T₁.coprod φ₁))
    (j₁ : E₁ →L[ℝ] V) (hj₁ : Function.Injective j₁)
    (hΛ₁ : Λ.L q₁ = (LinearMap.ker ((T₁.coprod φ₁ : E₁ × (Fin k → ℝ) →L[ℝ] F₁) :
      E₁ × (Fin k → ℝ) →ₗ[ℝ] F₁)).map ((j₁.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        E₁ × (Fin k → ℝ) →L[ℝ] V × (Fin k → ℝ)) : E₁ × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ)))
    {φ₁' : (Fin (k + d) → ℝ) →L[ℝ] F₁} (he₁ : φ₁' = appendStab φ₁ ψ₁)
    (hφ₁' : Function.Surjective (T₁.coprod φ₁'))
    (hΛ'₁ : Λ'.L q₁ = (LinearMap.ker ((T₁.coprod φ₁' :
      E₁ × (Fin (k + d) → ℝ) →L[ℝ] F₁) : E₁ × (Fin (k + d) → ℝ) →ₗ[ℝ] F₁)).map
        ((j₁.prodMap (ContinuousLinearMap.id ℝ (Fin (k + d) → ℝ)) :
          E₁ × (Fin (k + d) → ℝ) →L[ℝ] V × (Fin (k + d) → ℝ)) :
            E₁ × (Fin (k + d) → ℝ) →ₗ[ℝ] V × (Fin (k + d) → ℝ)))
    (r : Module.Ray ℝ (fredholmDet T₀)) :
    propagate Λ' q₀ q₁ hT₀ hφ₀' (kerEquivMap j₀ hj₀ hΛ'₀) hT₁ hφ₁' (kerEquivMap j₁ hj₁ hΛ'₁) r =
      propagate Λ q₀ q₁ hT₀ hφ₀ (kerEquivMap j₀ hj₀ hΛ₀) hT₁ hφ₁ (kerEquivMap j₁ hj₁ hΛ₁) r := by
  subst he₀ he₁
  exact propagate_append Λ Λ' hM hp hn q₀ q₁ hT₀ hφ₀ j₀ hj₀ hΛ₀ hΛ'₀ hT₁ hφ₁ j₁ hj₁ hΛ₁ hΛ'₁ r

end AppendEq

/-! ### Stabilized kernels along a family -/

section StabKernels

variable {Q : Type*} [TopologicalSpace Q]

variable (f) in
/-- **The stabilized kernels along a family** (pp. 221–223): for points `y(q)` in the domain of the
chart `c`, sc⁺-sections `S_q` with `(f + S_q)(y(q)) = 0` and sections `s₁(q), …, s_k(q)`, `Λ` is a
continuous family of the subspaces `(v, λ) ∈ E₀ × ℝᵏ` with `v ∈ T_zO` and `T_q v + φ_q λ = 0`, for
`T_q = (f + S_q)'(y(q))` and `φ_q(λ) = Σ λᵢ ŝᵢ(q)(y(q))`, and `T_q ⊕ φ_q` is onto. -/
structure IsStabKernels (c : StrongBundleChart PX P) (hc : B.IsChart c) (y : Q → X)
    (hy : ∀ q, y q ∈ c.φ.source) (S : Q → X → Y) {k : ℕ} (s : Fin k → Q → X → Y)
    (Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))) : Prop where
  isScPlusSection : ∀ q, B.IsScPlusSection (S q)
  zero : ∀ q, IsZeroAt P (sectionAdd P f (S q)) (y q)
  isSection : ∀ i q, IsSection P (s i q)
  exists_lift : ∀ q, ∃ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ (y q)
  spec : ∀ q {x : X} (_ : y q = x) (hxc : x ∈ c.φ.source) (z : c.φ.model.E 1)
    (hz : c.φ.model.E.toBase 1 z = c.φ x)
    (T : ↥(chartPt c hc hxc z hz).T →L[ℝ] ↥(chartPt c hc hxc z hz).K),
    (∀ v, (T v : c.F 0) = linAt c.U c.R (c.principal (sectionAdd P f (S q))) z v) →
    ∀ φ : (Fin k → ℝ) →L[ℝ] ↥(chartPt c hc hxc z hz).K,
    (∀ μ, (φ μ : c.F 0) = ∑ i, μ i • c.principal (s i q) (c.φ x)) →
      Function.Surjective (T.coprod φ) ∧
      Λ.L q = (LinearMap.ker ((T.coprod φ : _ →L[ℝ] ↥(chartPt c hc hxc z hz).K) :
          ↥(chartPt c hc hxc z hz).T × (Fin k → ℝ) →ₗ[ℝ] ↥(chartPt c hc hxc z hz).K)).map
        ((((chartPt c hc hxc z hz).T.subtypeL.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ))) :
          ↥(chartPt c hc hxc z hz).T × (Fin k → ℝ) →L[ℝ] c.φ.model.E 0 × (Fin k → ℝ)) :
            ↥(chartPt c hc hxc z hz).T × (Fin k → ℝ) →ₗ[ℝ] c.φ.model.E 0 × (Fin k → ℝ))

namespace IsStabKernels

variable {c : StrongBundleChart PX P} {hc : B.IsChart c} {y : Q → X} {hy : ∀ q, y q ∈ c.φ.source}
  {S : Q → X → Y} {k : ℕ} {s : Fin k → Q → X → Y}
  {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}

/-- **Pulling back along `g : Q' → Q`**. -/
theorem comp (hΛ : IsStabKernels f c hc y hy S s Λ) {Q' : Type*} [TopologicalSpace Q']
    (g : C(Q', Q)) :
    IsStabKernels f c hc (y ∘ g) (fun q => hy (g q)) (S ∘ g) (fun i => s i ∘ g) (Λ.comp g) where
  isScPlusSection q := hΛ.isScPlusSection (g q)
  zero q := hΛ.zero (g q)
  isSection i q := hΛ.isSection i (g q)
  exists_lift q := hΛ.exists_lift (g q)
  spec q _ hq hxc z hz T hT φ hφ := hΛ.spec (g q) hq hxc z hz T hT φ hφ

variable [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]

/-- **The push-forward `o ↦ φ_* o`** (p. 224) from `a` to `b` along stabilized kernels, between the
orientations of `DET(f, x₀)` and `DET(f, x₁)` for `x₀ = y(a)`, `x₁ = y(b)` smooth, read in the chart
points of `c` with lifts `z₀`, `z₁`: `o₀ ↦ o₀(T_a)`, then the sign `α(T_a) = (−1)^{dim coker T_a}`
(`stabSign`), then `propagate` (`Φ_{E_a}`, continuation in `λ(Λ)`, `Φ_{E_b}⁻¹`), then `α(T_b)`,
then the orientation through the ray at `T_b`. -/
def push (hΛ : IsStabKernels f c hc y hy S s Λ) (hf : B.IsScFredholmSection f) (a b : Q)
    {x₀ x₁ : X} (ha : y a = x₀) (hb : y b = x₁) (hx₀ : x₀ ∈ PX.smoothSet)
    (hx₁ : x₁ ∈ PX.smoothSet) (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x₀)
    (z₁ : c.φ.model.E 1) (hz₁ : c.φ.model.E.toBase 1 z₁ = c.φ x₁) :
    (chartPt c hc (ha ▸ hy a) z₀ hz₀).Or f hf ≃ (chartPt c hc (hb ▸ hy b) z₁ hz₁).Or f hf :=
  have h0a : IsZeroAt P (sectionAdd P f (S a)) x₀ := ha ▸ hΛ.zero a
  have h0b : IsZeroAt P (sectionAdd P f (S b)) x₁ := hb ▸ hΛ.zero b
  have hTa := (chartPt c hc (ha ▸ hy a) z₀ hz₀).stabT_mem_linSet hf (hΛ.isScPlusSection a) h0a hx₀
  have hTb := (chartPt c hc (hb ▸ hy b) z₁ hz₁).stabT_mem_linSet hf (hΛ.isScPlusSection b) h0b hx₁
  have hsa := hΛ.spec a ha (ha ▸ hy a) z₀ hz₀
    ((chartPt c hc (ha ▸ hy a) z₀ hz₀).stabT hf (hΛ.isScPlusSection a) h0a) (fun _ => rfl)
    ((chartPt c hc (ha ▸ hy a) z₀ hz₀).stabPhi (fun i => s i a) (fun i => hΛ.isSection i a))
    (fun μ => ChartPoint.coe_stabPhi _ _ _ μ)
  have hsb := hΛ.spec b hb (hb ▸ hy b) z₁ hz₁
    ((chartPt c hc (hb ▸ hy b) z₁ hz₁).stabT hf (hΛ.isScPlusSection b) h0b) (fun _ => rfl)
    ((chartPt c hc (hb ▸ hy b) z₁ hz₁).stabPhi (fun i => s i b) (fun i => hΛ.isSection i b))
    (fun μ => ChartPoint.coe_stabPhi _ _ _ μ)
  ((((ChartPoint.orEquivRay _ hf hTa).trans (MulAction.toPerm (stabSign
      ((chartPt c hc (ha ▸ hy a) z₀ hz₀).stabT hf (hΛ.isScPlusSection a) h0a)))).trans
    (propagate Λ a b (ChartPoint.isFredholm_of_mem_linSet _ hf _ hTa) hsa.1
      (kerEquivMap (chartPt c hc (ha ▸ hy a) z₀ hz₀).T.subtypeL Subtype.val_injective hsa.2)
      (ChartPoint.isFredholm_of_mem_linSet _ hf _ hTb) hsb.1
      (kerEquivMap (chartPt c hc (hb ▸ hy b) z₁ hz₁).T.subtypeL Subtype.val_injective
        hsb.2))).trans (MulAction.toPerm (stabSign
      ((chartPt c hc (hb ▸ hy b) z₁ hz₁).stabT hf (hΛ.isScPlusSection b) h0b)))).trans
    (ChartPoint.orEquivRay _ hf hTb).symm

/-- **The push-forward depends only on the data**: two families of stabilized kernels with the
same points and sections give the same push-forward (the subspaces are determined by the data). -/
theorem push_congr (hΛ : IsStabKernels f c hc y hy S s Λ)
    {Λ' : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}
    (hΛ' : IsStabKernels f c hc y hy S s Λ')
    (hf : B.IsScFredholmSection f) (a b : Q) {x₀ x₁ : X} (ha : y a = x₀) (hb : y b = x₁)
    (hx₀ : x₀ ∈ PX.smoothSet) (hx₁ : x₁ ∈ PX.smoothSet)
    (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x₀)
    (z₁ : c.φ.model.E 1) (hz₁ : c.φ.model.E.toBase 1 z₁ = c.φ x₁) :
    hΛ.push hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ = hΛ'.push hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ := by
  have hL : ∀ q, Λ.L q = Λ'.L q := fun q => by
    obtain ⟨z, hz⟩ := hΛ.exists_lift q
    have hφ := fun μ => ChartPoint.coe_stabPhi (chartPt c hc (hy q) z hz) (fun i => s i q)
      (fun i => hΛ.isSection i q) μ
    exact (hΛ.spec q rfl (hy q) z hz
        ((chartPt c hc (hy q) z hz).stabT hf (hΛ.isScPlusSection q) (hΛ.zero q)) (fun _ => rfl)
        _ hφ).2.trans
      (hΛ'.spec q rfl (hy q) z hz
        ((chartPt c hc (hy q) z hz).stabT hf (hΛ.isScPlusSection q) (hΛ.zero q)) (fun _ => rfl)
        _ hφ).2.symm
  have hn : Λ.n = Λ'.n := by rw [← Λ.finrank_eq a, ← Λ'.finrank_eq a, hL]
  obtain rfl : Λ = Λ' := by
    cases Λ; cases Λ'; dsimp only at hL hn; subst hn; congr; exact funext hL
  rfl

/-- **The orientation at `q` read in `λ(Λ_q)`**: `o ↦ Φ_{E_q}(α(T_q) o(T_q))`, the first three
steps of `push`. -/
def orRay (hΛ : IsStabKernels f c hc y hy S s Λ) (hf : B.IsScFredholmSection f) (q : Q) {x : X}
    (hq : y q = x) (hx : x ∈ PX.smoothSet) (z : c.φ.model.E 1)
    (hz : c.φ.model.E.toBase 1 z = c.φ x) :
    (chartPt c hc (hq ▸ hy q) z hz).Or f hf ≃ Module.Ray ℝ (Λ.det q) :=
  have h0 : IsZeroAt P (sectionAdd P f (S q)) x := hq ▸ hΛ.zero q
  have hT := (chartPt c hc (hq ▸ hy q) z hz).stabT_mem_linSet hf (hΛ.isScPlusSection q) h0 hx
  have hsq := hΛ.spec q hq (hq ▸ hy q) z hz
    ((chartPt c hc (hq ▸ hy q) z hz).stabT hf (hΛ.isScPlusSection q) h0) (fun _ => rfl)
    ((chartPt c hc (hq ▸ hy q) z hz).stabPhi (fun i => s i q) (fun i => hΛ.isSection i q))
    (fun μ => ChartPoint.coe_stabPhi _ _ _ μ)
  ((ChartPoint.orEquivRay _ hf hT).trans (MulAction.toPerm (stabSign
      ((chartPt c hc (hq ▸ hy q) z hz).stabT hf (hΛ.isScPlusSection q) h0)))).trans
    (stabRayEquiv (ChartPoint.isFredholm_of_mem_linSet _ hf _ hT) hsq.1
      (kerEquivMap (chartPt c hc (hq ▸ hy q) z hz).T.subtypeL Subtype.val_injective hsq.2))

/-- **The push-forward is continuation between the orientations read in `λ(Λ)`**:
`φ_* = orRay_b⁻¹ ∘ cont_{a b} ∘ orRay_a` (`α(T_b)⁻¹ = α(T_b)`). -/
theorem push_eq_orRay (hΛ : IsStabKernels f c hc y hy S s Λ) (hf : B.IsScFredholmSection f)
    (a b : Q) {x₀ x₁ : X} (ha : y a = x₀) (hb : y b = x₁) (hx₀ : x₀ ∈ PX.smoothSet)
    (hx₁ : x₁ ∈ PX.smoothSet) (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x₀)
    (z₁ : c.φ.model.E 1) (hz₁ : c.φ.model.E.toBase 1 z₁ = c.φ x₁) :
    hΛ.push hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ = (hΛ.orRay hf a ha hx₀ z₀ hz₀).trans
      ((Λ.contEquiv a b).trans (hΛ.orRay hf b hb hx₁ z₁ hz₁).symm) :=
  equiv_trans_push_aux _ _ _ _ _ _ _ (toPerm_stabSign_symm _)

open unitInterval in
/-- **Along a path with a fixed point the orientations read in `λ(Λ)` are continued into each
other**: for a path `γ` from `q` to `q'` along which `y` stays at `x` and the operators
`(f + S_τ)'(x)` and the values `ŝᵢ(τ)(x)` vary continuously, continuation in `Λ` maps
`orRay_q o` to `orRay_{q'} o` (`isLineOrientation_stabRay`). -/
theorem cont_orRay_path (hΛ : IsStabKernels f c hc y hy S s Λ) (hf : B.IsScFredholmSection f)
    (γ : C(I, Q)) {q q' : Q} (hq : γ 0 = q) (hq' : γ 1 = q') {x : X} (hγ : ∀ τ, y (γ τ) = x)
    (hyq : y q = x) (hyq' : y q' = x) (hx : x ∈ PX.smoothSet) (z : c.φ.model.E 1)
    (hz : c.φ.model.E.toBase 1 z = c.φ x)
    (hT : Continuous fun τ => linAt c.U c.R (c.principal (sectionAdd P f (S (γ τ)))) z)
    (hs : ∀ i, Continuous fun τ => c.principal (s i (γ τ)) (c.φ x))
    (o : (chartPt c hc (hyq ▸ hy q) z hz).Or f hf) :
    Λ.cont q q' (hΛ.orRay hf q hyq hx z hz o) = hΛ.orRay hf q' hyq' hx z hz o := by
  subst hq hq'
  have : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, left_mem_Icc.2 zero_le_one⟩
  have : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  have hx' : x ∈ c.φ.source := hyq ▸ hy (γ 0)
  have : CompleteSpace ↥(chartPt c hc hx' z hz).T :=
    (fun p : ChartPoint B x => (inferInstance : CompleteSpace ↥p.T)) _
  have : CompleteSpace ↥(chartPt c hc hx' z hz).K :=
    (fun p : ChartPoint B x => (inferInstance : CompleteSpace ↥p.K)) _
  -- the operators `T_τ` and the stabilizations `φ_τ` along `γ`, in the chart point at `x`
  let Tf : I → ↥(chartPt c hc hx' z hz).T →L[ℝ] ↥(chartPt c hc hx' z hz).K := fun τ =>
    (chartPt c hc hx' z hz).stabT hf (hΛ.isScPlusSection (γ τ)) ((hγ τ) ▸ hΛ.zero (γ τ))
  let φf : I → (Fin k → ℝ) →L[ℝ] ↥(chartPt c hc hx' z hz).K := fun τ =>
    (chartPt c hc hx' z hz).stabPhi (fun i => s i (γ τ)) (fun i => hΛ.isSection i (γ τ))
  have hTC : ∀ τ, Tf τ ∈ (chartPt c hc hx' z hz).linSet f := fun τ =>
    (chartPt c hc hx' z hz).stabT_mem_linSet hf (hΛ.isScPlusSection (γ τ))
      ((hγ τ) ▸ hΛ.zero (γ τ)) hx
  have hsp := fun τ => hΛ.spec (γ τ) (hγ τ) hx' z hz (Tf τ) (fun _ => rfl) (φf τ)
    (fun μ => ChartPoint.coe_stabPhi _ _ _ μ)
  have hTc : Continuous Tf :=
    continuous_clm_codRestrict (chartPt c hc hx' z hz).K _ hT fun τ v => (Tf τ v).2
  have hφc : Continuous φf := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) ↥(chartPt c hc hx' z hz).K
      (ContinuousLinearMap.proj i)).continuous.comp ((hs i).subtype_mk _)
  have hA : Continuous fun τ => (Tf τ).coprod (φf τ) :=
    (ContinuousLinearMap.coprodEquivL (S := ℝ)).continuous.comp (hTc.prodMk hφc)
  have hF : ∀ τ, ((Tf τ).coprod (φf τ)).IsFredholm := fun τ =>
    isFredholm_stabCoprod ((chartPt c hc hx' z hz).isFredholm_of_mem_linSet hf _ (hTC τ))
      (hsp τ).1
  -- the kernels `ker(T_τ ⊕ φ_τ)` and their orientations `α(T_τ) Φ(o(T_τ))`
  obtain ⟨ΛE, hΛE⟩ := exists_subspaceFamily_ker (fun τ => (Tf τ).coprod (φf τ)) hA hF
    fun τ => (hsp τ).1
  have hor := isLineOrientation_stabRay (C := (chartPt c hc hx' z hz).linSet f)
    (hC := (chartPt c hc hx' z hz).isFredholm_of_mem_linSet hf) o Tf hTc hTC φf hφc
    (fun τ => (hsp τ).1) ΛE hΛE
  -- carried to `Λ ∘ γ` by `j × 1`
  let e : ∀ τ, ΛE.L τ ≃ₗ[ℝ] (Λ.comp γ).L τ := fun τ =>
    (LinearEquiv.ofEq _ _ (hΛE τ)).trans
      (kerEquivMap (chartPt c hc hx' z hz).T.subtypeL Subtype.val_injective (hsp τ).2)
  have hor2 := ΛE.isLineOrientation_map
    (fun _ => (chartPt c hc hx' z hz).T.subtypeL.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)))
    (((chartPt c hc hx' z hz).T.subtypeL.prodMap
      (ContinuousLinearMap.id ℝ (Fin k → ℝ))).continuous.comp continuous_snd)
    (Λ.comp γ) e (fun τ v => rfl) ⟨_, hor⟩
  have hρ := fun τ => rayMap_smul_stabRayEquiv
    ((chartPt c hc hx' z hz).isFredholm_of_mem_linSet hf _ (hTC τ)) (hsp τ).1
    (LinearEquiv.ofEq _ _ (hΛE τ).symm) (e τ)
    (kerEquivMap _ Subtype.val_injective (hsp τ).2) (fun v => rfl) (stabSign (Tf τ))
    (o ⟨Tf τ, hTC τ⟩)
  have hc := (Λ.cont_comp γ 0 1 _).symm.trans ((Λ.comp γ).cont_eq ⟨_, hor2⟩ 0 1)
  exact (congrArg (Λ.cont (γ 0) (γ 1)) (hρ 0)).symm.trans (hc.trans (hρ 1))

/-- **The push-forward and pull-back**: along `Λ ∘ g` it is the push-forward along `Λ` between the
images. -/
theorem push_comp (hΛ : IsStabKernels f c hc y hy S s Λ) {Q' : Type*} [TopologicalSpace Q']
    [SimplyConnectedSpace Q'] [LocallyPathConnectedSpace Q'] (g : C(Q', Q))
    (hf : B.IsScFredholmSection f) (a b : Q') {x₀ x₁ : X} (ha : y (g a) = x₀)
    (hb : y (g b) = x₁) (hx₀ : x₀ ∈ PX.smoothSet) (hx₁ : x₁ ∈ PX.smoothSet)
    (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x₀)
    (z₁ : c.φ.model.E 1) (hz₁ : c.φ.model.E.toBase 1 z₁ = c.φ x₁) :
    (hΛ.comp g).push hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ =
      hΛ.push hf (g a) (g b) ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ := by
  rw [push_eq_orRay, push_eq_orRay]
  exact Equiv.ext fun o =>
    congrArg ((hΛ.comp g).orRay hf b hb hx₁ z₁ hz₁).symm (Λ.cont_comp g a b _)

/-- **The push-forward is compatible with concatenation**: from `a` to `d` it is the
push-forward from `a` to `b` followed by the one from `b` to `d` (`propagate_trans`). -/
theorem push_trans (hΛ : IsStabKernels f c hc y hy S s Λ) (hf : B.IsScFredholmSection f)
    (a b d : Q) {x₀ x₁ x₂ : X} (ha : y a = x₀) (hb : y b = x₁) (hd : y d = x₂)
    (hx₀ : x₀ ∈ PX.smoothSet) (hx₁ : x₁ ∈ PX.smoothSet) (hx₂ : x₂ ∈ PX.smoothSet)
    (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x₀)
    (z₁ : c.φ.model.E 1) (hz₁ : c.φ.model.E.toBase 1 z₁ = c.φ x₁)
    (z₂ : c.φ.model.E 1) (hz₂ : c.φ.model.E.toBase 1 z₂ = c.φ x₂) :
    hΛ.push hf a d ha hd hx₀ hx₂ z₀ hz₀ z₂ hz₂ =
      (hΛ.push hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁).trans
        (hΛ.push hf b d hb hd hx₁ hx₂ z₁ hz₁ z₂ hz₂) := by
  rw [push_eq_orRay, push_eq_orRay, push_eq_orRay]
  refine Equiv.ext fun o => ?_
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply, SubspaceFamily.contEquiv_apply,
    SubspaceFamily.cont_trans]

/-- **Lemma 6.6.8 (preprint 6.33), the core: adding sections does not change the push-forward.** For the same
points and sections `S_q`, the kernels of `s₁, …, s_k` and of `s₁, …, s_k, s̄₁, …, s̄_d` give the
same push-forward (`propagate_append`). -/
theorem push_append (hΛ : IsStabKernels f c hc y hy S s Λ) [Nonempty Q] {d : ℕ}
    {sbar : Fin d → Q → X → Y} {Λ' : SubspaceFamily Q (c.φ.model.E 0 × (Fin (k + d) → ℝ))}
    (hΛ' : IsStabKernels f c hc y hy S (Fin.append s sbar) Λ') (hf : B.IsScFredholmSection f)
    (a b : Q) {x₀ x₁ : X} (ha : y a = x₀) (hb : y b = x₁) (hx₀ : x₀ ∈ PX.smoothSet)
    (hx₁ : x₁ ∈ PX.smoothSet) (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x₀)
    (z₁ : c.φ.model.E 1) (hz₁ : c.φ.model.E.toBase 1 z₁ = c.φ x₁) :
    hΛ'.push hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ = hΛ.push hf a b ha hb hx₀ hx₁ z₀ hz₀ z₁ hz₁ := by
  -- the two kernels at `q`, read with any lift `z`
  have hspec := fun q (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ (y q)) =>
    And.intro (hΛ.spec q rfl (hy q) z hz
      ((chartPt c hc (hy q) z hz).stabT hf (hΛ.isScPlusSection q) (hΛ.zero q)) (fun _ => rfl)
      ((chartPt c hc (hy q) z hz).stabPhi (fun i => s i q) (fun i => hΛ.isSection i q))
      (fun μ => ChartPoint.coe_stabPhi _ _ _ μ))
    (hΛ'.spec q rfl (hy q) z hz
      ((chartPt c hc (hy q) z hz).stabT hf (hΛ.isScPlusSection q) (hΛ.zero q)) (fun _ => rfl)
      ((chartPt c hc (hy q) z hz).stabPhi (fun i => Fin.append s sbar i q)
        (fun i => hΛ'.isSection i q))
      (fun μ => ChartPoint.coe_stabPhi _ _ _ μ))
  -- `(v, λ) ↦ (v, λ ++ 0)` maps `Λ` into `Λ'`
  have hM : ∀ q, ∀ v ∈ Λ.L q,
      ((v.1, Fin.append v.2 0) : c.φ.model.E 0 × (Fin (k + d) → ℝ)) ∈ Λ'.L q := by
    intro q v hv
    obtain ⟨z, hz⟩ := hΛ.exists_lift q
    obtain ⟨h1, h2⟩ := hspec q z hz
    rw [h1.2] at hv
    rw [h2.2, ChartPoint.stabPhi_finAppend]
    obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨(w.1, Fin.append w.2 0), ?_, rfl⟩
    rw [SetLike.mem_coe, mem_ker_coprod] at hw ⊢
    rw [appendStab_append, map_zero, add_zero]
    exact hw
  have hp : ∀ q, (Λ'.L q).map (((restrictNatAdd k d).comp
      (ContinuousLinearMap.snd ℝ (c.φ.model.E 0) (Fin (k + d) → ℝ)) :
        c.φ.model.E 0 × (Fin (k + d) → ℝ) →L[ℝ] Fin d → ℝ) :
          c.φ.model.E 0 × (Fin (k + d) → ℝ) →ₗ[ℝ] Fin d → ℝ) = ⊤ := by
    -- `Λ'` projects onto `ℝᵈ`, since `T ⊕ φ` is onto
    intro q
    obtain ⟨z, hz⟩ := hΛ.exists_lift q
    obtain ⟨h1, h2⟩ := hspec q z hz
    rw [eq_top_iff]
    rintro μ -
    obtain ⟨w, hw⟩ := h1.1 (-((chartPt c hc (hy q) z hz).stabPhi (fun j => sbar j q)
      (fun j => by simpa using hΛ'.isSection (Fin.natAdd k j) q) μ))
    rw [h2.2, ChartPoint.stabPhi_finAppend]
    refine ⟨((w.1 : c.φ.model.E 0), Fin.append w.2 μ), ⟨(w.1, Fin.append w.2 μ), ?_, rfl⟩, ?_⟩
    · rw [SetLike.mem_coe, mem_ker_coprod, appendStab_append, ← add_assoc]
      rw [ContinuousLinearMap.coprod_apply] at hw
      rw [hw, neg_add_cancel]
    · simp
  have h1a := hΛ.spec a ha (ha ▸ hy a) z₀ hz₀
    ((chartPt c hc (ha ▸ hy a) z₀ hz₀).stabT hf (hΛ.isScPlusSection a) (ha ▸ hΛ.zero a))
    (fun _ => rfl)
    ((chartPt c hc (ha ▸ hy a) z₀ hz₀).stabPhi (fun i => s i a) (fun i => hΛ.isSection i a))
    (fun μ => ChartPoint.coe_stabPhi _ _ _ μ)
  have h2a := hΛ'.spec a ha (ha ▸ hy a) z₀ hz₀
    ((chartPt c hc (ha ▸ hy a) z₀ hz₀).stabT hf (hΛ.isScPlusSection a) (ha ▸ hΛ.zero a))
    (fun _ => rfl)
    ((chartPt c hc (ha ▸ hy a) z₀ hz₀).stabPhi (fun i => Fin.append s sbar i a)
      (fun i => hΛ'.isSection i a))
    (fun μ => ChartPoint.coe_stabPhi _ _ _ μ)
  have hTa := (chartPt c hc (ha ▸ hy a) z₀ hz₀).stabT_mem_linSet hf (hΛ.isScPlusSection a)
    (ha ▸ hΛ.zero a) hx₀
  -- the dimensions, at the smooth point `x₀`
  have hn : Λ.n + d = Λ'.n := by
    have e1 := (kerEquivMap _ Subtype.val_injective h1a.2).finrank_eq
    have e2 := (kerEquivMap _ Subtype.val_injective h2a.2).finrank_eq
    rw [ChartPoint.stabPhi_finAppend] at e2
    rw [← Λ.finrank_eq a, ← Λ'.finrank_eq a, ← e1, ← e2]
    exact finrank_ker_appendStab (ChartPoint.isFredholm_of_mem_linSet _ hf _ hTa) h1a.1
  have h1b := hΛ.spec b hb (hb ▸ hy b) z₁ hz₁
    ((chartPt c hc (hb ▸ hy b) z₁ hz₁).stabT hf (hΛ.isScPlusSection b) (hb ▸ hΛ.zero b))
    (fun _ => rfl)
    ((chartPt c hc (hb ▸ hy b) z₁ hz₁).stabPhi (fun i => s i b) (fun i => hΛ.isSection i b))
    (fun μ => ChartPoint.coe_stabPhi _ _ _ μ)
  have h2b := hΛ'.spec b hb (hb ▸ hy b) z₁ hz₁
    ((chartPt c hc (hb ▸ hy b) z₁ hz₁).stabT hf (hΛ.isScPlusSection b) (hb ▸ hΛ.zero b))
    (fun _ => rfl)
    ((chartPt c hc (hb ▸ hy b) z₁ hz₁).stabPhi (fun i => Fin.append s sbar i b)
      (fun i => hΛ'.isSection i b))
    (fun μ => ChartPoint.coe_stabPhi _ _ _ μ)
  have hTb := (chartPt c hc (hb ▸ hy b) z₁ hz₁).stabT_mem_linSet hf (hΛ.isScPlusSection b)
    (hb ▸ hΛ.zero b) hx₁
  have key := fun r => propagate_append_of_eq Λ Λ' hM hp hn a b
    (ChartPoint.isFredholm_of_mem_linSet _ hf _ hTa) h1a.1 _ Subtype.val_injective h1a.2
    (ChartPoint.stabPhi_finAppend (chartPt c hc (ha ▸ hy a) z₀ hz₀) s sbar a
      (fun i => hΛ'.isSection i a)) h2a.1 h2a.2
    (ChartPoint.isFredholm_of_mem_linSet _ hf _ hTb) h1b.1 _ Subtype.val_injective h1b.2
    (ChartPoint.stabPhi_finAppend (chartPt c hc (hb ▸ hy b) z₁ hz₁) s sbar b
      (fun i => hΛ'.isSection i b)) h2b.1 h2b.2 r
  exact equiv_trans_congr_mid_aux _ _ (Equiv.ext key) _ _

/-- **The push-forward is unchanged by a deformation with fixed end points** (the argument of
Lemmas 6.33–6.34 and before Theorem 6.6.11 (preprint 6.35)): for paths `γ₀` from `a` to `a'` and `γ₁` from `b` to `b'`
in `Q` along which the points stay at `x₀`, resp. `x₁`, and along which the operators
`(f + S_q)'(xᵢ)` and the values `ŝᵢ(q)(xᵢ)` vary continuously, the push-forwards from `a` to `b`
and from `a'` to `b'` agree.  (In `Q` simply connected, continuation from `a` to `b'` through `b`
and through `a'` agree, and on the two edges the continued orientation is `α(T_q) Φ_E(o(T_q))`
by `isLineOrientation_stabRay`, `cont_orRay_path`.) -/
theorem push_square (hΛ : IsStabKernels f c hc y hy S s Λ) (hf : B.IsScFredholmSection f)
    {a a' b b' : Q} (γ₀ : Path a a') (γ₁ : Path b b') {x₀ x₁ : X}
    (hγ₀ : ∀ τ, y (γ₀ τ) = x₀) (hγ₁ : ∀ τ, y (γ₁ τ) = x₁)
    (hx₀ : x₀ ∈ PX.smoothSet) (hx₁ : x₁ ∈ PX.smoothSet)
    (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x₀)
    (z₁ : c.φ.model.E 1) (hz₁ : c.φ.model.E.toBase 1 z₁ = c.φ x₁)
    (hT₀ : Continuous fun τ => linAt c.U c.R (c.principal (sectionAdd P f (S (γ₀ τ)))) z₀)
    (hT₁ : Continuous fun τ => linAt c.U c.R (c.principal (sectionAdd P f (S (γ₁ τ)))) z₁)
    (hs₀ : ∀ i, Continuous fun τ => c.principal (s i (γ₀ τ)) (c.φ x₀))
    (hs₁ : ∀ i, Continuous fun τ => c.principal (s i (γ₁ τ)) (c.φ x₁)) :
    hΛ.push hf a b (by simpa using hγ₀ 0) (by simpa using hγ₁ 0) hx₀ hx₁ z₀ hz₀ z₁ hz₁ =
      hΛ.push hf a' b' (by simpa using hγ₀ 1) (by simpa using hγ₁ 1) hx₀ hx₁ z₀ hz₀ z₁ hz₁ := by
  have ha : y a = x₀ := by simpa using hγ₀ 0
  have ha' : y a' = x₀ := by simpa using hγ₀ 1
  have hb : y b = x₁ := by simpa using hγ₁ 0
  have hb' : y b' = x₁ := by simpa using hγ₁ 1
  rw [push_eq_orRay, push_eq_orRay]
  refine Equiv.ext fun o => ?_
  -- on the edge `γ₀`: `cont_{a a'} (orRay_a o) = orRay_{a'} o`
  have e0 := hΛ.cont_orRay_path hf γ₀.toContinuousMap γ₀.source γ₀.target hγ₀ ha ha' hx₀ z₀ hz₀
    hT₀ hs₀ o
  -- on the edge `γ₁`, for `o' = φ_* o` from `a` to `b`
  have e1 := hΛ.cont_orRay_path hf γ₁.toContinuousMap γ₁.source γ₁.target hγ₁ hb hb' hx₁ z₁ hz₁
    hT₁ hs₁ ((hΛ.orRay hf b hb hx₁ z₁ hz₁).symm (Λ.cont a b (hΛ.orRay hf a ha hx₀ z₀ hz₀ o)))
  rw [Equiv.apply_symm_apply] at e1
  change _ = (hΛ.orRay hf b' hb' hx₁ z₁ hz₁).symm
    (Λ.cont a' b' (hΛ.orRay hf a' ha' hx₀ z₀ hz₀ o))
  rw [← e0, Λ.cont_trans, ← Λ.cont_trans a b b', e1, Equiv.symm_apply_apply]
  rfl

end IsStabKernels

end StabKernels

end Polyfold
