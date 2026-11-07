import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_41

/-! Round trip for V6_41 (the push-forward `o₁ = φ_* o₀` along stabilized kernels, p. 224).

A (universes at `0`): the project's lemmas on its push-forward — `stabT_mem_linSet`,
`stabPhi_finAppend`, `stabSign_inv`, `toPerm_stabSign_symm`, `isFredholm_stabCoprod`,
`IsStabKernels.comp`, `push_congr`, `push_eq_orRay`, `cont_orRay_path`, `push_comp`,
`push_trans` — about the definition `IsStabKernels.push`, which composes the text's chain
`o₀ ↦ o₀(T_0)`, `Φ_{E_0}`, continuation, `Φ_{E_1}⁻¹`, `o₁` WITH the sign
`α(T) = stabSign T = (−1)^{dim coker T}` inserted at both end points.

B: `hΛ.push = F.push`, the project's push-forward equals the text's literal one (no sign), for all
choices with (P) read in a chart.

`push_eq_iff` (below, proved; only non-item lemmas, `#rt_check_soft`): for every datum of B,
`hΛ.push = F.push ↔ stabSign T_0 = stabSign T_1`, i.e. `dim coker T_0 ≡ dim coker T_1 (mod 2)`.
So B holds iff the parity of `dim coker T_t` is the same at the two end points of every path with
choices satisfying (P); the two maps differ exactly by `α(T_0) α(T_1)`.  The parity does change in
general (in finite dimensions, `X = ℝ`, `Y = ℝ × ℝ`, `f(x) = x²`, `φ(t) = t`, `s(y, t) = t²`,
`s₁ = 1`: `T_0 = 0` with `dim coker = 1`, `T_1 = 2` with `dim coker = 0`), so B is believed false;
`not_B` is NOT proved: it needs that instance inside the M-polyfold framework (a strong bundle,
sc-Fredholm `f`, the pulled-back bundles over `ℝᵏ × ℝ × X`, general position germs there, a
`Reading`, `Facts` and an `IsStabKernels` datum), which is beyond this audit's budget.

`A ⇒ B`: not proved (believed false: A is true, B false).  `B ⇒ A`: not proved (A is about the
project's signed `push`; from B one would still have to re-prove A's lemmas).
-/

namespace RoundTrip.V6_41
open Polyfold Set

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.ChartPoint.stabT_mem_linSet.{0, 0} ∧
  type_of% @Polyfold.ChartPoint.stabPhi_finAppend.{0, 0, 0} ∧
  type_of% @Polyfold.stabSign_inv.{0, 0} ∧
  type_of% @Polyfold.toPerm_stabSign_symm.{0, 0, 0} ∧
  type_of% @Polyfold.isFredholm_stabCoprod.{0, 0} ∧
  type_of% @Polyfold.IsStabKernels.comp.{0, 0, 0, 0} ∧
  type_of% @Polyfold.IsStabKernels.push_congr.{0, 0, 0} ∧
  type_of% @Polyfold.IsStabKernels.push_eq_orRay.{0, 0, 0} ∧
  type_of% @Polyfold.IsStabKernels.cont_orRay_path.{0, 0, 0} ∧
  type_of% @Polyfold.IsStabKernels.push_comp.{0, 0, 0, 0} ∧
  type_of% @Polyfold.IsStabKernels.push_trans.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.ChartPoint.stabT_mem_linSet.{0, 0}, @Polyfold.ChartPoint.stabPhi_finAppend.{0, 0, 0},
    @Polyfold.stabSign_inv.{0, 0}, @Polyfold.toPerm_stabSign_symm.{0, 0, 0},
    @Polyfold.isFredholm_stabCoprod.{0, 0}, @Polyfold.IsStabKernels.comp.{0, 0, 0, 0},
    @Polyfold.IsStabKernels.push_congr.{0, 0, 0}, @Polyfold.IsStabKernels.push_eq_orRay.{0, 0, 0},
    @Polyfold.IsStabKernels.cont_orRay_path.{0, 0, 0}, @Polyfold.IsStabKernels.push_comp.{0, 0, 0, 0},
    @Polyfold.IsStabKernels.push_trans.{0, 0, 0}⟩

/-! ### The push-forward commutes with signs -/

section Signs

variable {Q : Type} [TopologicalSpace Q] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- `u • o` is an orientation of `λ(L)` when `o` is. -/
theorem isLineOrientation_units_smul (Λ : SubspaceFamily Q W) (o : LineOrientation Λ.det)
    (u : ℝˣ) : IsLineOrientation Λ.det fun b => u • o b := by
  intro b₀
  obtain ⟨U, hU, σ, hσ, hσo⟩ := o.2 b₀
  refine ⟨U, hU, fun b => u • σ b, fun b hb => ?_, fun b hb => ?_⟩
  · have hfr := Λ.mem_frameAt b
    refine (Λ.continuousWithinAt_section_iff (Λ.frameAt b) hfr).2 ?_
    have h1 := ((Λ.continuousWithinAt_section_iff (Λ.frameAt b) hfr).1 (hσ b hb)).const_mul
      (u : ℝ)
    refine h1.congr (fun b' _ => ?_) ?_ <;>
      simp only [Units.smul_def, LinearMap.map_smul, smul_eq_mul]
  · obtain ⟨h, hr⟩ := hσo b hb
    refine ⟨(smul_ne_zero_iff_ne _).2 h, ?_⟩
    change u • o.1 b = _
    rw [hr]
    rfl

/-- **Continuation commutes with signs**. -/
theorem cont_units_smul [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]
    (Λ : SubspaceFamily Q W) (q₀ q₁ : Q) (u : ℝˣ) (r : Module.Ray ℝ (Λ.det q₀)) :
    Λ.cont q₀ q₁ (u • r) = u • Λ.cont q₀ q₁ r := by
  obtain ⟨o, rfl⟩ := exists_lineOrientation_apply_eq (L := Λ.det) q₀ r
  rw [Λ.cont_eq o q₀ q₁]
  exact Λ.cont_eq ⟨fun b => u • o b, isLineOrientation_units_smul Λ o u⟩ q₀ q₁

/-- The inverse of a sign-equivariant bijection of rays is sign-equivariant. -/
theorem symm_units_smul {M N : Type} [AddCommMonoid M] [Module ℝ M] [AddCommMonoid N]
    [Module ℝ N] (e : Module.Ray ℝ M ≃ Module.Ray ℝ N) (he : ∀ (u : ℝˣ) r, e (u • r) = u • e r)
    (u : ℝˣ) (r : Module.Ray ℝ N) : e.symm (u • r) = u • e.symm r :=
  e.injective (by rw [e.apply_symm_apply, he, e.apply_symm_apply])

/-- `Module.Ray.map` commutes with signs (for modules over `ℝ` that are only monoids). -/
theorem rayMap_units_smul' {M N : Type} [AddCommMonoid M] [Module ℝ M] [AddCommMonoid N]
    [Module ℝ N] (e : M ≃ₗ[ℝ] N) (u : ℝˣ) (r : Module.Ray ℝ M) :
    Module.Ray.map e (u • r) = u • Module.Ray.map e r := by
  induction r using Module.Ray.ind with | h v hv => ?_
  rw [smul_rayOfNeZero, Module.Ray.map_apply, Module.Ray.map_apply, smul_rayOfNeZero]
  exact rayOfNeZero_eq_of_eq _ _ (by rw [Units.smul_def, Units.smul_def, map_smul])

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- `Φ_E` on rays commutes with signs. -/
theorem stabRayEquiv_units_smul {k : ℕ} {T : E →L[ℝ] F} {φ : (Fin k → ℝ) →L[ℝ] F}
    (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ))
    {V : Type} [AddCommGroup V] [Module ℝ V] {L : Submodule ℝ V} [FiniteDimensional ℝ L]
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] L) (u : ℝˣ) (r : Module.Ray ℝ (fredholmDet T)) :
    stabRayEquiv hT hφ ι (u • r) = u • stabRayEquiv hT hφ ι r := by
  change Module.Ray.map (maxPowEquiv ι) (Module.Ray.map (detEquivOfSurjective hφ)
      (Module.Ray.map (LinearEquiv.ofBijective (stabIota hT hφ) (stabIota_bijective hT hφ))
        (u • r))) = _
  rw [rayMap_units_smul', rayMap_units_smul', rayMap_units_smul']
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The push-forward `propagate` commutes with signs**. -/
theorem propagate_units_smul [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]
    (Λ : SubspaceFamily Q W) {E₁ F₁ : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [CompleteSpace E₁] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [CompleteSpace F₁]
    {k k₁ : ℕ} {T : E →L[ℝ] F} {φ : (Fin k → ℝ) →L[ℝ] F} {T₁ : E₁ →L[ℝ] F₁}
    {φ₁ : (Fin k₁ → ℝ) →L[ℝ] F₁} (q₀ q₁ : Q) (hT : T.IsFredholm)
    (hφ : Function.Surjective (T.coprod φ))
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] Λ.L q₀)
    (hT₁ : T₁.IsFredholm) (hφ₁ : Function.Surjective (T₁.coprod φ₁))
    (ι₁ : LinearMap.ker ((T₁.coprod φ₁ : E₁ × (Fin k₁ → ℝ) →L[ℝ] F₁) :
      E₁ × (Fin k₁ → ℝ) →ₗ[ℝ] F₁) ≃ₗ[ℝ] Λ.L q₁) (u : ℝˣ) (r : Module.Ray ℝ (fredholmDet T)) :
    propagate Λ q₀ q₁ hT hφ ι hT₁ hφ₁ ι₁ (u • r) = u • propagate Λ q₀ q₁ hT hφ ι hT₁ hφ₁ ι₁ r := by
  change (stabRayEquiv hT₁ hφ₁ ι₁).symm (Λ.cont q₀ q₁ (stabRayEquiv hT hφ ι (u • r))) =
    u • (stabRayEquiv hT₁ hφ₁ ι₁).symm (Λ.cont q₀ q₁ (stabRayEquiv hT hφ ι r))
  have h1 : Λ.cont q₀ q₁ (stabRayEquiv hT hφ ι (u • r)) =
      u • Λ.cont q₀ q₁ (stabRayEquiv hT hφ ι r) :=
    (congrArg (Λ.cont q₀ q₁) (stabRayEquiv_units_smul hT hφ ι u r)).trans
      (cont_units_smul Λ q₀ q₁ u _)
  rw [h1]
  exact symm_units_smul _ (stabRayEquiv_units_smul hT₁ hφ₁ ι₁) u _

end Signs

/-- `(−1) • x ≠ x` for a ray `x` (of a module that is only a monoid). -/
theorem neg_one_smul_ne {M : Type} [AddCommMonoid M] [Module ℝ M] (x : Module.Ray ℝ M) :
    (-1 : ℝˣ) • x ≠ x := by
  induction x using Module.Ray.ind with | h v hv => ?_
  intro h
  rw [smul_rayOfNeZero, ray_eq_iff] at h
  have hn : ((-1 : ℝˣ) • v) = (-1 : ℝ) • v := Units.smul_def _ _
  rcases h with h0 | h0 | ⟨a, b, ha, hb, hab⟩
  · rw [hn] at h0
    have : v = (-1 : ℝ) • ((-1 : ℝ) • v) := by rw [smul_smul]; norm_num
    exact hv (by rw [this, h0, smul_zero])
  · exact hv h0
  · rw [hn, smul_smul] at hab
    have h1 : (b + a) • v = 0 := by
      rw [add_smul, ← hab, ← add_smul]; norm_num
    have : v = (b + a)⁻¹ • ((b + a) • v) := by
      rw [smul_smul, inv_mul_cancel₀ (by linarith), one_smul]
    exact hv (by rw [this, h1, smul_zero])

/-- **Two signs at the ends of a sign-equivariant bijection cancel iff they are equal.** -/
theorem signs_iff {A₀ A₁ M₀ M₁ : Type} [AddCommMonoid M₀] [Module ℝ M₀] [AddCommMonoid M₁]
    [Module ℝ M₁] (oa : A₀ ≃ Module.Ray ℝ M₀) (ob : A₁ ≃ Module.Ray ℝ M₁)
    (Pr : Module.Ray ℝ M₀ ≃ Module.Ray ℝ M₁) (hP : ∀ (u : ℝˣ) r, Pr (u • r) = u • Pr r)
    (u₀ u₁ : ℝˣ) (n₀ n₁ : ℕ) (hu₀ : u₀ = (-1) ^ n₀) (hu₁ : u₁ = (-1) ^ n₁)
    (r₀ : Module.Ray ℝ M₀) :
    (((oa.trans (MulAction.toPerm u₀)).trans Pr).trans (MulAction.toPerm u₁)).trans ob.symm =
        (oa.trans Pr).trans ob.symm ↔ u₀ = u₁ := by
  subst hu₀ hu₁
  constructor
  · intro h
    have h1 := congrArg (fun e => e (oa.symm r₀)) h
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, MulAction.toPerm_apply] at h1
    have h2 := ob.symm.injective h1
    rw [hP, smul_smul] at h2
    rcases Nat.even_or_odd n₀ with h₀ | h₀ <;> rcases Nat.even_or_odd n₁ with h₁ | h₁
    · rw [h₀.neg_one_pow, h₁.neg_one_pow]
    · rw [h₀.neg_one_pow, h₁.neg_one_pow, mul_one] at h2
      exact absurd h2 (neg_one_smul_ne _)
    · rw [h₀.neg_one_pow, h₁.neg_one_pow, one_mul] at h2
      exact absurd h2 (neg_one_smul_ne _)
    · rw [h₀.neg_one_pow, h₁.neg_one_pow]
  · intro h
    refine Equiv.ext fun r => ?_
    simp only [Equiv.trans_apply, MulAction.toPerm_apply]
    rw [hP, smul_smul, ← h, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

/-- **Replacing the end-point data by equal data** does not change the unsigned push-forward. -/
theorem unsigned_congr {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {B : StrongBundle PX P} {f : X → Y} (hf : B.IsScFredholmSection f) {x₀ x₁ : X}
    (p₀ : ChartPoint B x₀) (p₁ : ChartPoint B x₁) {Q : Type} [TopologicalSpace Q]
    [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q] {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {k : ℕ} (Λ : SubspaceFamily Q (V × (Fin k → ℝ))) (a b : Q)
    (j₀ : ↥p₀.T →L[ℝ] V) (hj₀ : Function.Injective j₀)
    (j₁ : ↥p₁.T →L[ℝ] V) (hj₁ : Function.Injective j₁)
    {T₀ T₀' : ↥p₀.T →L[ℝ] ↥p₀.K} (eT₀ : T₀ = T₀') {φ₀ φ₀' : (Fin k → ℝ) →L[ℝ] ↥p₀.K}
    (eφ₀ : φ₀ = φ₀') {T₁ T₁' : ↥p₁.T →L[ℝ] ↥p₁.K} (eT₁ : T₁ = T₁')
    {φ₁ φ₁' : (Fin k → ℝ) →L[ℝ] ↥p₁.K} (eφ₁ : φ₁ = φ₁')
    (hT₀ : T₀ ∈ p₀.linSet f) (hT₀' : T₀' ∈ p₀.linSet f)
    (hT₁ : T₁ ∈ p₁.linSet f) (hT₁' : T₁' ∈ p₁.linSet f)
    (hF₀ : T₀.IsFredholm) (hF₀' : T₀'.IsFredholm) (hF₁ : T₁.IsFredholm) (hF₁' : T₁'.IsFredholm)
    (hs₀ : Function.Surjective (T₀.coprod φ₀)) (hs₀' : Function.Surjective (T₀'.coprod φ₀'))
    (hs₁ : Function.Surjective (T₁.coprod φ₁)) (hs₁' : Function.Surjective (T₁'.coprod φ₁'))
    (hL₀ : Λ.L a = (LinearMap.ker ((T₀.coprod φ₀ : _ →L[ℝ] ↥p₀.K) :
      ↥p₀.T × (Fin k → ℝ) →ₗ[ℝ] ↥p₀.K)).map ((j₀.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        ↥p₀.T × (Fin k → ℝ) →L[ℝ] V × (Fin k → ℝ)) : ↥p₀.T × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ)))
    (hL₀' : Λ.L a = (LinearMap.ker ((T₀'.coprod φ₀' : _ →L[ℝ] ↥p₀.K) :
      ↥p₀.T × (Fin k → ℝ) →ₗ[ℝ] ↥p₀.K)).map ((j₀.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        ↥p₀.T × (Fin k → ℝ) →L[ℝ] V × (Fin k → ℝ)) : ↥p₀.T × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ)))
    (hL₁ : Λ.L b = (LinearMap.ker ((T₁.coprod φ₁ : _ →L[ℝ] ↥p₁.K) :
      ↥p₁.T × (Fin k → ℝ) →ₗ[ℝ] ↥p₁.K)).map ((j₁.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        ↥p₁.T × (Fin k → ℝ) →L[ℝ] V × (Fin k → ℝ)) : ↥p₁.T × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ)))
    (hL₁' : Λ.L b = (LinearMap.ker ((T₁'.coprod φ₁' : _ →L[ℝ] ↥p₁.K) :
      ↥p₁.T × (Fin k → ℝ) →ₗ[ℝ] ↥p₁.K)).map ((j₁.prodMap (ContinuousLinearMap.id ℝ (Fin k → ℝ)) :
        ↥p₁.T × (Fin k → ℝ) →L[ℝ] V × (Fin k → ℝ)) : ↥p₁.T × (Fin k → ℝ) →ₗ[ℝ] V × (Fin k → ℝ))) :
    ((p₀.orEquivRay hf hT₀).trans (propagate Λ a b hF₀ hs₀ (kerEquivMap j₀ hj₀ hL₀) hF₁ hs₁
        (kerEquivMap j₁ hj₁ hL₁))).trans (p₁.orEquivRay hf hT₁).symm =
      ((p₀.orEquivRay hf hT₀').trans (propagate Λ a b hF₀' hs₀' (kerEquivMap j₀ hj₀ hL₀') hF₁'
        hs₁' (kerEquivMap j₁ hj₁ hL₁'))).trans (p₁.orEquivRay hf hT₁').symm := by
  subst eT₀ eφ₀ eT₁ eφ₁
  rfl

/-- **The diagnosis, formally**: for every datum of B, the project's push-forward is the text's
literal one iff `stabSign T_0 = stabSign T_1`, i.e. iff `dim coker T_0 ≡ dim coker T_1 (mod 2)`. -/
theorem push_eq_iff {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    {B : StrongBundle PX P} {hπ : SndSmooth PX} {f : X → Y} (hf : B.IsScFredholmSection f)
    {γ : (Fin 1 → ℝ) → X} {c : StrongBundleChart PX P} {hc : B.IsChart c}
    {hγ : ∀ t : J, γ t ∈ c.φ.source} {z : J → c.φ.model.E.lvl 1}
    {hz : ∀ t, c.φ.model.E.toBase 1 (z t) = c.φ.toPartialEquiv (γ t)}
    {k : ℕ} {D : Choices B hπ f γ k} (R : Reading c hc hγ z hz D) (F : Facts c hc hγ z hz R)
    (hΛ : IsStabKernels f c hc (fun q : J => γ q) hγ
      (fun q : J => negSec (P := P) (pullbackSlice D.s q))
      (fun i (q : J) => pullbackSlice (D.σ i) q) F.Λ)
    (h₀ : γ iccZero ∈ PX.smoothSet) (h₁ : γ iccOne ∈ PX.smoothSet) :
    hΛ.push hf iccZero iccOne rfl rfl h₀ h₁ (z iccZero) (hz iccZero) (z iccOne) (hz iccOne) =
        F.push hf ↔
      stabSign (R.T iccZero) = stabSign (R.T iccOne) := by
  -- the reading's operators are the project's `stabT`, `stabPhi`
  have eT : ∀ t, R.T t = (cp c hc hγ z hz t).stabT hf (hΛ.isScPlusSection t) (hΛ.zero t) :=
    fun t => ContinuousLinearMap.ext fun v => Subtype.ext (R.hT t v)
  have eΦ : ∀ t, R.Φ t = (cp c hc hγ z hz t).stabPhi (fun i => pullbackSlice (D.σ i) t)
      (fun i => hΛ.isSection i t) :=
    fun t => ContinuousLinearMap.ext fun μ =>
      Subtype.ext ((R.hΦ t μ).trans (ChartPoint.coe_stabPhi (cp c hc hγ z hz t)
        (fun i => pullbackSlice (D.σ i) t) (fun i => hΛ.isSection i t) μ).symm)
  have hTa := eT iccZero ▸ F.lin0
  have hTb := eT iccOne ▸ F.lin1
  have hFa := eT iccZero ▸ F.fred iccZero
  have hFb := eT iccOne ▸ F.fred iccOne
  have hsa := hΛ.spec iccZero rfl (hγ iccZero) (z iccZero) (hz iccZero)
    ((cp c hc hγ z hz iccZero).stabT hf (hΛ.isScPlusSection iccZero) (hΛ.zero iccZero)) (fun _ => rfl)
    ((cp c hc hγ z hz iccZero).stabPhi (fun i => pullbackSlice (D.σ i) iccZero)
      (fun i => hΛ.isSection i iccZero)) (fun μ => ChartPoint.coe_stabPhi _ _ _ μ)
  have hsb := hΛ.spec iccOne rfl (hγ iccOne) (z iccOne) (hz iccOne)
    ((cp c hc hγ z hz iccOne).stabT hf (hΛ.isScPlusSection iccOne) (hΛ.zero iccOne)) (fun _ => rfl)
    ((cp c hc hγ z hz iccOne).stabPhi (fun i => pullbackSlice (D.σ i) iccOne)
      (fun i => hΛ.isSection i iccOne)) (fun μ => ChartPoint.coe_stabPhi _ _ _ μ)
  have e2 := unsigned_congr hf (cp c hc hγ z hz iccZero) (cp c hc hγ z hz iccOne) F.Λ iccZero
    iccOne _ Subtype.val_injective _ Subtype.val_injective (eT iccZero) (eΦ iccZero) (eT iccOne)
    (eΦ iccOne) F.lin0 hTa F.lin1 hTb (F.fred _) hFa (F.fred _) hFb (F.surj _) hsa.1 (F.surj _)
    hsb.1 (F.hΛ _) hsa.2 (F.hΛ _) hsb.2
  -- the complete spaces of the chart points (as in the project's `cont_orRay_path`)
  have : CompleteSpace ↥(cp c hc hγ z hz iccZero).T :=
    (fun p : ChartPoint B (γ iccZero) => (inferInstance : CompleteSpace ↥p.T)) _
  have : CompleteSpace ↥(cp c hc hγ z hz iccZero).K :=
    (fun p : ChartPoint B (γ iccZero) => (inferInstance : CompleteSpace ↥p.K)) _
  have : CompleteSpace ↥(cp c hc hγ z hz iccOne).T :=
    (fun p : ChartPoint B (γ iccOne) => (inferInstance : CompleteSpace ↥p.T)) _
  have : CompleteSpace ↥(cp c hc hγ z hz iccOne).K :=
    (fun p : ChartPoint B (γ iccOne) => (inferInstance : CompleteSpace ↥p.K)) _
  -- a ray of `det T_0`
  have : Nontrivial (fredholmDet ((cp c hc hγ z hz iccZero).stabT hf
      (hΛ.isScPlusSection iccZero) (hΛ.zero iccZero))) :=
    Module.nontrivial_of_finrank_eq_succ (finrank_fredholmDet hFa)
  obtain ⟨v, hv⟩ := exists_ne (0 : fredholmDet ((cp c hc hγ z hz iccZero).stabT hf
      (hΛ.isScPlusSection iccZero) (hΛ.zero iccZero)))
  have key := signs_iff (M₀ := fredholmDet ((cp c hc hγ z hz iccZero).stabT hf
      (hΛ.isScPlusSection iccZero) (hΛ.zero iccZero)))
    (M₁ := fredholmDet ((cp c hc hγ z hz iccOne).stabT hf
      (hΛ.isScPlusSection iccOne) (hΛ.zero iccOne)))
    ((cp c hc hγ z hz iccZero).orEquivRay hf hTa)
    ((cp c hc hγ z hz iccOne).orEquivRay hf hTb)
    (propagate F.Λ iccZero iccOne hFa hsa.1
      (kerEquivMap (cp c hc hγ z hz iccZero).T.subtypeL Subtype.val_injective hsa.2) hFb hsb.1
      (kerEquivMap (cp c hc hγ z hz iccOne).T.subtypeL Subtype.val_injective hsb.2))
    (propagate_units_smul _ _ _ _ _ _ _ _ _)
    (stabSign ((cp c hc hγ z hz iccZero).stabT hf (hΛ.isScPlusSection iccZero) (hΛ.zero iccZero)))
    (stabSign ((cp c hc hγ z hz iccOne).stabT hf (hΛ.isScPlusSection iccOne) (hΛ.zero iccOne)))
    _ _ rfl rfl (rayOfNeZero ℝ v hv)
  rw [show F.push hf = _ from e2]
  exact key.trans (by rw [eT iccZero, eT iccOne])

#rt_check_soft RoundTrip.V6_41.push_eq_iff [Polyfold.ChartPoint.stabT_mem_linSet,
  Polyfold.ChartPoint.stabPhi_finAppend, Polyfold.stabSign_inv, Polyfold.toPerm_stabSign_symm,
  Polyfold.isFredholm_stabCoprod, Polyfold.IsStabKernels.comp, Polyfold.IsStabKernels.push_congr,
  Polyfold.IsStabKernels.push_eq_orRay, Polyfold.IsStabKernels.cont_orRay_path,
  Polyfold.IsStabKernels.push_comp, Polyfold.IsStabKernels.push_trans]

end RoundTrip.V6_41
