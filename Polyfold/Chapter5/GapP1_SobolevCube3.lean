import Polyfold.Chapter5.GapP1_SobolevCube2

/-!
# The sc-structure `W^{1+m,p}` on a cube, part 3: `W^{k,p}` of the cube `(0,1)¹`

Continuation of `GapP1_SobolevCube1–2` (2021 §5.5, the remark after Theorem 5.5.5, pp. 230–231).
The Sobolev spaces `W n k p Ω` of `GapP1_SobolevRemark2` live on `Ω ⊆ ℝⁿ = (Fin n → ℝ)`; here
`n = 1` and `Ω = Ω1 = (0,1)¹`, the open unit cube.  We identify `Fin 1 → ℝ` with `ℝ`:

* `emb t = (fun _ => t)`, measure preserving `μI → μΩ Ω1`, and `T : Lᵖ(Ω1) →ₗᵢ Lᵖ(I)`,
  `T g = g ∘ emb`;
* test functions on `Ω1` are the `ψ ∘ (· 0)` with `ψ` a test function on `I`, and
  `∂^α (ψ ∘ (· 0)) = ψ^{(α₀)} ∘ (· 0)` (`Dm_comp`);
* `comp u j = T (D^j u)`, `j ≤ k`, for `u ∈ W^{k,p}(Ω1)`, and **`comp_eq_cst_add_V`**: consecutive
  components are related by `comp u j = c + V (comp u (j+1))`;
* `ofSmooth f k ∈ W^{k,p}(Ω1)` for smooth `f : ℝ → ℝ`, the tuple `(f^{(j)} ∘ (· 0))_{j ≤ k}`, with
  `inclW (ofSmooth f (k+1)) = ofSmooth f k`.
-/

open MeasureTheory Set Function Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Polyfold

namespace SobolevCube

open SobolevRemark

/-! ### The cube and the identification `Fin 1 → ℝ ≅ ℝ` -/

/-- The open unit cube `(0,1)¹ ⊆ ℝ¹`. -/
abbrev Ω1 : Set (Fin 1 → ℝ) := univ.pi fun _ => I

lemma isOpen_Ω1 : IsOpen Ω1 := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

/-- `ℝ → ℝ¹`, `t ↦ (t)`. -/
def emb : ℝ → (Fin 1 → ℝ) := (MeasurableEquiv.funUnique (Fin 1) ℝ).symm

lemma emb_apply (t : ℝ) (i : Fin 1) : emb t i = t := rfl

lemma emb_eval (x : Fin 1 → ℝ) : emb (x 0) = x := by
  funext i; rw [emb_apply, Subsingleton.elim i 0]

lemma continuous_emb : Continuous emb := continuous_pi fun _ => continuous_id

lemma mem_Ω1 {x : Fin 1 → ℝ} : x ∈ Ω1 ↔ x 0 ∈ I := by
  constructor
  · intro h; exact h 0 (mem_univ _)
  · intro h i _; rwa [Subsingleton.elim i 0]

lemma emb_preimage : emb ⁻¹' Ω1 = I := by
  ext t; simp [emb_apply]

lemma eval_preimage : (fun x : Fin 1 → ℝ => x 0) ⁻¹' I = Ω1 := by
  ext x; simp

lemma mp_emb : MeasurePreserving emb μI (μΩ Ω1) := by
  have h := ((volume_preserving_funUnique (Fin 1) ℝ).symm _).restrict_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding Ω1
  rwa [show ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm : ℝ → Fin 1 → ℝ) ⁻¹' Ω1 = I from
    emb_preimage] at h

lemma mp_eval : MeasurePreserving (fun x : Fin 1 → ℝ => x 0) (μΩ Ω1) μI := by
  have h := (volume_preserving_funUnique (Fin 1) ℝ).restrict_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding I
  have e1 : ((MeasurableEquiv.funUnique (Fin 1) ℝ) : (Fin 1 → ℝ) → ℝ) = fun x => x 0 := rfl
  rw [e1, eval_preimage] at h
  exact h
lemma contDiff_emb : ContDiff ℝ ∞ emb := contDiff_pi.2 fun _ => contDiff_id

variable {p : ℝ} [hP : Fact (1 ≤ ENNReal.ofReal p)]

/-- `T : Lᵖ(Ω1) → Lᵖ(I)`, `g ↦ g ∘ emb`, a linear isometry. -/
def T : Lp ℝ (ENNReal.ofReal p) (μΩ Ω1) →ₗᵢ[ℝ] L p :=
  Lp.compMeasurePreservingₗᵢ ℝ emb mp_emb

lemma coeFn_T (g : Lp ℝ (ENNReal.ofReal p) (μΩ Ω1)) : (T g : ℝ → ℝ) =ᵐ[μI] g ∘ emb :=
  Lp.coeFn_compMeasurePreserving g mp_emb

omit hP in
lemma integral_Ω1 (F : (Fin 1 → ℝ) → ℝ) : ∫ x, F x ∂(μΩ Ω1) = ∫ t, F (emb t) ∂μI :=
  (mp_emb.integral_comp' (f := (MeasurableEquiv.funUnique (Fin 1) ℝ).symm) F).symm

omit hP in
lemma ae_comp_emb {g g' : (Fin 1 → ℝ) → ℝ} (h : g =ᵐ[μΩ Ω1] g') :
    (fun t => g (emb t)) =ᵐ[μI] fun t => g' (emb t) :=
  mp_emb.quasiMeasurePreserving.ae_eq_comp h

/-! ### Test functions -/

omit hP in
lemma tsupport_subset_of {α : Type*} [TopologicalSpace α] {f : α → ℝ} {K : Set α}
    (hK : IsClosed K) (h : ∀ x, x ∉ K → f x = 0) : tsupport f ⊆ K :=
  closure_minimal (fun x hx => by by_contra h'; exact hx (h x h')) hK

omit hP in
/-- A test function `ψ` on `I` gives the test function `ψ ∘ (· 0)` on `Ω1`. -/
lemma IsTestI.comp_eval {ψ : ℝ → ℝ} (hψ : IsTestI ψ) :
    IsTestOn Ω1 (fun x : Fin 1 → ℝ => ψ (x 0)) := by
  have hK : IsCompact (emb '' tsupport ψ) := hψ.2.1.isCompact.image continuous_emb
  have hz : ∀ x : Fin 1 → ℝ, x ∉ emb '' tsupport ψ → ψ (x 0) = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx ⟨x 0, h, emb_eval x⟩
  refine ⟨hψ.1.comp (contDiff_apply ℝ ℝ 0), HasCompactSupport.intro hK hz, ?_⟩
  refine (tsupport_subset_of hK.isClosed hz).trans ?_
  rintro _ ⟨t, ht, rfl⟩
  exact mem_Ω1.2 (hψ.2.2 ht)

omit hP in
/-- A test function `φ` on `Ω1` gives the test function `φ ∘ emb` on `I`. -/
lemma IsTestOn.comp_emb {φ : (Fin 1 → ℝ) → ℝ} (hφ : IsTestOn Ω1 φ) :
    IsTestI (fun t => φ (emb t)) := by
  have hK : IsCompact ((fun x : Fin 1 → ℝ => x 0) '' tsupport φ) :=
    hφ.2.1.isCompact.image (continuous_apply 0)
  have hz : ∀ t, t ∉ (fun x : Fin 1 → ℝ => x 0) '' tsupport φ → φ (emb t) = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h => ht ⟨emb t, h, rfl⟩
  refine ⟨hφ.1.comp contDiff_emb, HasCompactSupport.intro hK hz, ?_⟩
  refine (tsupport_subset_of hK.isClosed hz).trans ?_
  rintro _ ⟨x, hx, rfl⟩
  exact mem_Ω1.1 (hφ.2.2 hx)

omit hP in
lemma eq_comp_eval (φ : (Fin 1 → ℝ) → ℝ) : φ = fun x => (fun t => φ (emb t)) (x 0) :=
  funext fun x => by simp only [emb_eval]

/-! ### Partial derivatives on `ℝ¹` -/

omit hP in
lemma Dm_one (a : Fin 1 → ℕ) (φ : (Fin 1 → ℝ) → ℝ) : Dm a φ = (pd 0)^[a 0] φ := rfl

omit hP in
lemma pd_comp_eval {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ) :
    pd 0 (fun x : Fin 1 → ℝ => ψ (x 0)) = fun x => deriv ψ (x 0) := by
  funext x
  have h : HasFDerivAt (fun x : Fin 1 → ℝ => ψ (x 0))
      ((fderiv ℝ ψ (x 0)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0))
      x :=
    (hψ (x 0)).hasFDerivAt.comp x
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  rw [pd, h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    Pi.single_eq_same]
  rfl

omit hP in
lemma contDiff_iter {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv j f) := by
  rw [iteratedDeriv_eq_iterate]; exact hf.iterate_deriv j

omit hP in
lemma cont_iter {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) : Continuous (iteratedDeriv j f) :=
  (contDiff_iter hf j).continuous

omit hP in
lemma iterate_pd_comp_eval {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : ℕ) :
    (pd 0)^[j] (fun x : Fin 1 → ℝ => ψ (x 0)) = fun x => iteratedDeriv j ψ (x 0) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iterate_succ_apply', ih, pd_comp_eval ((contDiff_iter hψ j).differentiable (by simp)),
      iteratedDeriv_succ]

omit hP in
/-- `∂^α (ψ ∘ (· 0)) = ψ^{(α₀)} ∘ (· 0)`. -/
lemma Dm_comp_eval {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (a : Fin 1 → ℕ) :
    Dm a (fun x : Fin 1 → ℝ => ψ (x 0)) = fun x => iteratedDeriv (a 0) ψ (x 0) := by
  rw [Dm_one, iterate_pd_comp_eval hψ]

/-! ### Multi-indices on `ℝ¹` -/

/-- The multi-index `(j)` of order `j ≤ k`. -/
def midx (k : ℕ) (j : Fin (k + 1)) : MIdx 1 k :=
  ⟨fun _ => j, by simpa using Nat.lt_succ_iff.1 j.2⟩

omit hP in
lemma MIdx.ord_one {k : ℕ} (a : MIdx 1 k) : a.ord = a.1 0 := by
  simp [MIdx.ord]

omit hP in
lemma midx_ord (k : ℕ) (j : Fin (k + 1)) : (midx k j).ord = j := by
  rw [MIdx.ord_one]; rfl

omit hP in
lemma eq_midx {k : ℕ} (a : MIdx 1 k) : a = midx k (a.1 0) :=
  Subtype.ext (funext fun i => by rw [Subsingleton.elim i 0]; rfl)

/-! ### The components of `u ∈ W^{k,p}(Ω1)` -/

/-- The component `comp u j = T (D^j u) ∈ Lᵖ(I)`. -/
def comp {k : ℕ} (u : W 1 k p Ω1) (j : Fin (k + 1)) : L p := T (Dop (midx k j) u)

lemma norm_Dop_le {k : ℕ} (u : W 1 k p Ω1) (a : MIdx 1 k) : ‖Dop a u‖ ≤ ‖u‖ :=
  PiLp.norm_apply_le (u : Amb 1 k p Ω1) a

lemma norm_comp {k : ℕ} (u : W 1 k p Ω1) (j : Fin (k + 1)) :
    ‖comp u j‖ = ‖Dop (midx k j) u‖ := T.norm_map _

lemma norm_comp_le {k : ℕ} (u : W 1 k p Ω1) (j : Fin (k + 1)) : ‖comp u j‖ ≤ ‖u‖ := by
  rw [norm_comp]; exact norm_Dop_le u _

lemma integral_comp_eq {k : ℕ} (u : W 1 k p Ω1) (a : MIdx 1 k) (F : ℝ → ℝ) :
    ∫ t, F t * comp u (a.1 0) t ∂μI = ∫ t, F (emb t 0) * (u : Amb 1 k p Ω1).ofLp a (emb t) ∂μI := by
  refine integral_congr_ae ?_
  filter_upwards [coeFn_T (Dop (midx k (a.1 0)) u)] with t ht
  rw [comp, ht, ← eq_midx]; rfl

/-- The weak-derivative identities of `u ∈ W^{k,p}(Ω1)`, transported to `I`:
`∫_I ψ^{(j)} u₀ = (−1)^j ∫_I ψ u_j`. -/
lemma wcond {k : ℕ} (u : W 1 k p Ω1) (j : Fin (k + 1)) {ψ : ℝ → ℝ} (hψ : IsTestI ψ) :
    ∫ t, iteratedDeriv j ψ t * comp u 0 t ∂μI =
      (-1) ^ (j : ℕ) * ∫ t, ψ t * comp u j t ∂μI := by
  have h := u.2 (midx k j) _ hψ.comp_eval
  rw [wk_apply, sub_eq_zero, Dm_comp_eval hψ.1, midx_ord, integral_Ω1, integral_Ω1] at h
  have e1 := integral_comp_eq u (MIdx.zero 1 k) (iteratedDeriv j ψ)
  have e2 := integral_comp_eq u (midx k j) ψ
  exact e1.trans (h.trans (congrArg (fun z => (-1 : ℝ) ^ (j : ℕ) * z) e2.symm))

/-- **Consecutive components**: `comp u (j+1)` is the weak derivative of `comp u j` on `I`. -/
lemma weakDeriv_comp {k : ℕ} (u : W 1 k p Ω1) (j : Fin k) {ψ : ℝ → ℝ} (hψ : IsTestI ψ) :
    ∫ t, deriv ψ t * comp u j.castSucc t ∂μI = -∫ t, ψ t * comp u j.succ t ∂μI := by
  have h1 := wcond u j.castSucc hψ.deriv
  have h2 := wcond u j.succ hψ
  rw [Fin.val_succ, iteratedDeriv_succ'] at h2
  rw [Fin.val_castSucc] at h1
  rw [h1, pow_succ] at h2
  have hne : ((-1 : ℝ) ^ (j : ℕ)) ≠ 0 := pow_ne_zero _ (by norm_num)
  set X := ∫ t, deriv ψ t * comp u j.castSucc t ∂μI
  set Y := ∫ t, ψ t * comp u j.succ t ∂μI
  have h3 : (-1 : ℝ) ^ (j : ℕ) * X = (-1 : ℝ) ^ (j : ℕ) * (-Y) := by rw [h2]; ring
  exact mul_left_cancel₀ hne h3

/-- **`comp u j = c + V (comp u (j+1))`** for `u ∈ W^{k,p}(Ω1)`, `j < k`. -/
theorem comp_eq_cst_add_V {k : ℕ} (u : W 1 k p Ω1) (j : Fin k) :
    ∃ c : ℝ, comp u j.castSucc = cst c + V (comp u j.succ) :=
  eq_cst_add_V _ _ fun _ hψ => weakDeriv_comp u j hψ

/-! ### Smooth functions as elements of `W^{k,p}(Ω1)` -/

omit hP in
lemma memLp_comp_eval {f : ℝ → ℝ} (hf : Continuous f) :
    MemLp (fun x : Fin 1 → ℝ => f (x 0)) (ENNReal.ofReal p) (μΩ Ω1) :=
  (memLp_of_continuous hf _).comp_measurePreserving mp_eval

/-- The tuple `(f^{(j)} ∘ (· 0))_{j ≤ k}` in `∏ Lᵖ(Ω1)`. -/
def ofSmoothVec (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (k : ℕ) : Amb 1 k p Ω1 :=
  WithLp.toLp _ fun a => (memLp_comp_eval (p := p) (cont_iter hf (a.1 0))).toLp _

omit hP in
lemma ofSmoothVec_apply (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (k : ℕ) (a : MIdx 1 k) :
    (ofSmoothVec (p := p) f hf k).ofLp a =
      (memLp_comp_eval (p := p) (cont_iter hf (a.1 0))).toLp _ := rfl

lemma ofSmoothVec_mem (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ofSmoothVec (p := p) f hf k ∈ Wsub 1 k p Ω1 := by
  intro a φ hφ
  have hψ := IsTestOn.comp_emb hφ
  rw [wk_apply, sub_eq_zero, eq_comp_eval φ, Dm_comp_eval hψ.1, integral_Ω1, integral_Ω1,
    MIdx.ord_one]
  have e1 : ∫ t, (fun x : Fin 1 → ℝ => iteratedDeriv (a.toFun 0) (fun t => φ (emb t)) (x 0))
        (emb t) * ((ofSmoothVec (p := p) f hf k).ofLp (MIdx.zero 1 k) : _ → ℝ) (emb t) ∂μI =
      ∫ t, iteratedDeriv (a.1 0) (fun t => φ (emb t)) t * f t ∂μI := by
    refine integral_congr_ae ?_
    filter_upwards [ae_comp_emb (MemLp.coeFn_toLp
      (memLp_comp_eval (p := p) (cont_iter hf ((MIdx.zero 1 k).1 0))))] with t ht
    rw [ofSmoothVec_apply, ht]
    rfl
  have e2 : ∫ t, (fun x : Fin 1 → ℝ => φ (emb (x 0))) (emb t) *
        ((ofSmoothVec (p := p) f hf k).ofLp a : _ → ℝ) (emb t) ∂μI =
      ∫ t, φ (emb t) * iteratedDeriv (a.1 0) f t ∂μI := by
    refine integral_congr_ae ?_
    filter_upwards [ae_comp_emb (MemLp.coeFn_toLp
      (memLp_comp_eval (p := p) (cont_iter hf (a.1 0))))] with t ht
    rw [ofSmoothVec_apply, ht]
    rfl
  rw [e1, e2]
  exact integral_iteratedDeriv_mul hf _ hψ

/-- **A smooth function `f : ℝ → ℝ` as an element of `W^{k,p}(Ω1)`**: `u(x) = f(x₀)`, with
weak derivatives `D^j u = f^{(j)}(x₀)`. -/
def ofSmooth (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (k : ℕ) : W 1 k p Ω1 :=
  ⟨ofSmoothVec f hf k, ofSmoothVec_mem f hf k⟩

lemma comp_ofSmooth (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (k : ℕ) (j : Fin (k + 1)) :
    comp (ofSmooth (p := p) f hf k) j = toLpS (iteratedDeriv j f) (cont_iter hf j) := by
  rw [comp, toLpS]
  change T ((memLp_comp_eval (p := p) (cont_iter hf j)).toLp _) = _
  change Lp.compMeasurePreserving emb mp_emb (MemLp.toLp _ _) = _
  rw [Lp.toLp_compMeasurePreserving]
  rfl

lemma inclW_ofSmooth (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    inclW (ofSmooth (p := p) f hf (k + 1)) = ofSmooth f hf k :=
  Subtype.ext (PiLp.ext fun _ => rfl)

end SobolevCube

end Polyfold
