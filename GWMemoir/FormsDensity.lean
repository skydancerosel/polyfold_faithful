import GWMemoir.ChartChangeDensity

/-!
# Density of the smooth forms for the constant maps from `sphere3`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §1.2 (p. 7) and §2.4
(p. 51): the fibre of `W` over `u`, the forms of class `(2, δ₀)` anti-linear off the nodes, is an
sc-subspace of the block space (`FormsDense`, reduced by `formsDense_iff`).

* `jMat z y = T_{y→z} ∘ j(y) ∘ T_{z→y}`: the matrix of `j` read in the chart at `z`.
  **`contMDiffAt_jMat`**: it is smooth on the chart domain.  `AlmostComplexStructure.smooth`
  gives smoothness in tangent coordinates at the base point only; the base point is moved with
  the trivialization of the bundle `Hom(TS, TS)` at `z` (`contMDiffAt_hom_bundle`,
  `Trivialization.contMDiffAt_iff`).  `contDiff_jMat`: read in a disc chart, it is smooth on the
  strip when the charts are onto `ℝ²`.
* `projF J₀ ξ = ½ (ξ + J₀ ∘ ξ ∘ j)`: the projection to the anti-linear forms (`projF_mem`,
  `projF_of_mem`).  In a disc chart it acts on representatives by `½ (v + ∑ J_{kk'} χ j_{d'd}
  v_{d',k'})` (`formDiscRep_twist`), a sum of `ChartChange.op`s with `ψ = id` (`idCC`).
* `fOp`: block operators `v ↦ ∑_t a_t · (v_{src t} ∘ ψ_t)` on the fibre blocks, at every level,
  commuting with the inclusions (`toBase_fOp`).
* `testForm`: the form of a tuple of test functions in one disc chart.
* **`formsDense_const`**: on a surface without nodes whose charts are onto `ℝ²`, for a constant
  map, any `J` and any atlas, `FormsDense`.  The operator `Φ = ½ (G + P' G)`, with `G` the change
  of charts glued by a partition of unity (`coef`, `piece_sum_eq`) and `P'` the projection, is
  the identity on the representatives of anti-linear forms and maps test tuples to
  representatives of anti-linear forms.
* `sphere3_formsDense`: the instance on the constant maps from `sphere3`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory Bundle
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

section JMat

variable {m : ℕ} {X : NodalSurface m}

/-- `j(y)` read in the chart at `z`: `T_{y→z} ∘ j(y) ∘ T_{z→y}`. -/
def jMat (z y : X.S) : E2 →L[ℝ] E2 :=
  (tangentCoordChange 𝓘(ℝ, E2) y z y).comp
    ((X.j.J y).comp (tangentCoordChange 𝓘(ℝ, E2) z y y))

lemma jMat_eq_inTangentCoordinates {z y : X.S} (hy : y ∈ (extChartAt 𝓘(ℝ, E2) z).source) :
    jMat z y = inTangentCoordinates 𝓘(ℝ, E2) 𝓘(ℝ, E2) id id X.j.J z y := by
  rw [inTangentCoordinates_eq _ _ _ (by simpa using hy) (by simpa using hy)]
  rfl

/-- **`j` read in the chart at `z` is smooth on the chart domain.** -/
theorem contMDiffAt_jMat {z y₁ : X.S} (hy : y₁ ∈ (extChartAt 𝓘(ℝ, E2) z).source) :
    ContMDiffAt 𝓘(ℝ, E2) 𝓘(ℝ, E2 →L[ℝ] E2) ∞ (jMat z) y₁ := by
  let F : X.S → TotalSpace (E2 →L[ℝ] E2)
      (fun x : X.S => TangentSpace 𝓘(ℝ, E2) x →L[ℝ] TangentSpace 𝓘(ℝ, E2) x) :=
    fun x => ⟨x, X.j.J x⟩
  have hF : ContMDiffAt 𝓘(ℝ, E2) (𝓘(ℝ, E2).prod 𝓘(ℝ, E2 →L[ℝ] E2)) ∞ F y₁ :=
    (contMDiffAt_hom_bundle F).2 ⟨contMDiffAt_id, X.j.smooth y₁⟩
  let e := trivializationAt (E2 →L[ℝ] E2)
      (fun x : X.S => TangentSpace 𝓘(ℝ, E2) x →L[ℝ] TangentSpace 𝓘(ℝ, E2) x) z
  have he : F y₁ ∈ e.source := by
    simp only [e, hom_trivializationAt_source]
    exact ⟨by simpa using hy, by simpa using hy⟩
  refine ((e.contMDiffAt_iff he).1 hF).2.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source z).mem_nhds hy] with x hx
  rw [jMat_eq_inTangentCoordinates hx]
  rfl

variable (hT : ChartsOnto X)

include hT in
/-- The matrix of `j` read in a disc chart is smooth on the whole strip. -/
theorem contDiff_jMat (z : X.S) (ε : ℝ) : ContDiff ℝ ∞ fun p => jMat z (X.discPt z ε p) :=
  contMDiff_iff_contDiff.1 fun p =>
    (contMDiffAt_jMat (discPt_mem_source hT z ε p)).comp p (contMDiff_discPt hT z ε p)

lemma tcc_jMat {z y : X.S} (hy : y ∈ (extChartAt 𝓘(ℝ, E2) z).source) (v : E2) :
    tangentCoordChange 𝓘(ℝ, E2) z y y (jMat z y v) =
      X.j.J y (tangentCoordChange 𝓘(ℝ, E2) z y y v) := by
  simp only [jMat, ContinuousLinearMap.comp_apply]
  rw [tangentCoordChange_comp ⟨⟨mem_extChartAt_source _, hy⟩, mem_extChartAt_source _⟩,
    tangentCoordChange_self (mem_extChartAt_source _)]

end JMat

/-! ## 2. A cut-off and the identity change of charts -/

section Cut

/-- A cut-off equal to `1` on the closed disc `r² ≤ 1/8`, supported in `r² ≤ 3/16`. -/
def chiP (p : ℝ × ℝ) : ℝ := Real.smoothTransition (3 - 16 * (p.1 ^ 2 + (p.2 - 1 / 2) ^ 2))

/-- The disc `r² ≤ 3/16` of the strip. -/
def KP : Set (ℝ × ℝ) := {p | p.1 ^ 2 + (p.2 - 1 / 2) ^ 2 ≤ 3 / 16}

lemma contDiff_chiP : ContDiff ℝ ∞ chiP := by
  unfold chiP; exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma isClosed_KP : IsClosed KP := isClosed_le (by fun_prop) continuous_const

lemma isCompact_KP : IsCompact KP := by
  refine (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 2))
    |>.of_isClosed_subset isClosed_KP fun p hp => ?_
  simp only [KP, mem_ofPred_eq] at hp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg p.1, sq_nonneg (p.2 - 1 / 2)]

lemma KP_sub : KP ⊆ openStrip := by
  intro p hp
  simp only [KP, mem_ofPred_eq] at hp
  refine ⟨mem_univ _, ?_, ?_⟩ <;> nlinarith [sq_nonneg p.1, sq_nonneg (p.2 - 1 / 2)]

lemma tsupport_chiP : tsupport chiP ⊆ KP := by
  refine closure_minimal (fun p hp => ?_) isClosed_KP
  simp only [KP, mem_ofPred_eq]
  by_contra h
  exact hp (Real.smoothTransition.zero_of_nonpos (by push Not at h; linarith))

lemma discCut_mul_chiP (p : ℝ × ℝ) : discCut p * chiP p = discCut p := by
  by_cases hp : p ∈ closedDisc
  · have : chiP p = 1 := Real.smoothTransition.one_of_one_le (by
      simp only [closedDisc, mem_ofPred_eq] at hp; linarith)
    rw [this, mul_one]
  · rw [discCut_eq_zero hp, zero_mul]

/-- The identity as a change of disc charts, on `KP`. -/
def idCC : ChartChange where
  K := KP
  ψ := id
  isCompact := isCompact_KP
  sub := KP_sub
  smooth := contDiff_id
  injOn := injOn_id _
  det_ne := fun _ _ => by
    rw [fderiv_id, ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
    exact one_ne_zero
  mapsTo := fun _ hx => KP_sub hx

end Cut

/-! ## 3. The projection to the anti-linear forms -/

section Projection

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m}

/-- The matrix of `J₀` in the basis of `E`. -/
def Jc (J₀ : E →L[ℝ] E) (k k' : Fin (Module.finrank ℝ E)) : ℝ :=
  crd k (J₀ (Module.finBasis ℝ E k'))

lemma sum_Jc (J₀ : E →L[ℝ] E) (k : Fin (Module.finrank ℝ E)) (w : E) :
    ∑ k', Jc J₀ k k' * crd k' w = crd k (J₀ w) := by
  conv_rhs => rw [← (Module.finBasis ℝ E).sum_repr w]
  simp only [map_sum, map_smul, smul_eq_mul, Jc, crd, Module.Basis.coord_apply]
  exact Finset.sum_congr rfl fun k' _ => mul_comm _ _

/-- `ξ ↦ J₀ ∘ ξ ∘ j`. -/
def twist (J₀ : E →L[ℝ] E) (ξ : Form E X) : Form E X := fun y => J₀.comp ((ξ y).comp (X.j.J y))

/-- The projection `ξ ↦ ½ (ξ + J₀ ∘ ξ ∘ j)` to the anti-linear forms. -/
def projF (J₀ : E →L[ℝ] E) (ξ : Form E X) : Form E X := (1 / 2 : ℝ) • (ξ + twist J₀ ξ)

lemma projF_mem (J : AlmostComplexStructure E Q) (q : Q) (ξ : Form E X) (y : X.S) :
    projF (J.J q) ξ y ∈ X.antiLinearForms J q y := by
  rw [NodalSurface.mem_antiLinearForms]
  intro v
  simp only [projF, twist, Pi.smul_apply, Pi.add_apply, smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, map_smul, map_add, J.J_J, X.j.J_J, map_neg]
  module

lemma projF_of_mem {J : AlmostComplexStructure E Q} {q : Q} {ξ : Form E X} {y : X.S}
    (h : ξ y ∈ X.antiLinearForms J q y) : projF (J.J q) ξ y = ξ y := by
  rw [NodalSurface.mem_antiLinearForms] at h
  ext v
  have h1 := h (X.j.J y v)
  simp only [projF, twist, Pi.smul_apply, Pi.add_apply, smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, h1, X.j.J_J, map_neg, neg_neg]
  module

/-- The coefficient of the projection in a disc chart: `J_{kk'} · χ · j_{d'd}`. -/
def aP (J₀ : E →L[ℝ] E) (z : X.S) (ε : ℝ) (d d' : Fin 2) (k k' : Fin (Module.finrank ℝ E))
    (p : ℝ × ℝ) : ℝ :=
  Jc J₀ k k' * (chiP p * (jMat z (X.discPt z ε p) (EuclideanSpace.single d 1)) d')

variable (hT : ChartsOnto X)

include hT in
lemma contDiff_aP (J₀ : E →L[ℝ] E) (z : X.S) (ε : ℝ) (d d' : Fin 2)
    (k k' : Fin (Module.finrank ℝ E)) : ContDiff ℝ ∞ (aP J₀ z ε d d' k k') :=
  contDiff_const.mul (contDiff_chiP.mul ((EuclideanSpace.proj d' : E2 →L[ℝ] ℝ).contDiff.comp
    ((contDiff_jMat hT z ε).clm_apply contDiff_const)))

lemma tsupport_aP (J₀ : E →L[ℝ] E) (z : X.S) (ε : ℝ) (d d' : Fin 2)
    (k k' : Fin (Module.finrank ℝ E)) : tsupport (aP J₀ z ε d d' k k') ⊆ idCC.K := by
  refine closure_minimal (fun p hp => tsupport_chiP (subset_tsupport _ fun h => hp ?_))
    isClosed_KP
  simp [aP, h]

variable {q : Q} {u : X.S → Q} (hu : ∀ x, u x = q) (A : SectionAtlas (E := E) X u)

include hT hu in
/-- The representative of `J₀ ∘ ξ ∘ j` is `∑ J_{kk'} χ j_{d'd} ·` the representative of `ξ`. -/
lemma formDiscRep_twist (J₀ : E →L[ℝ] E) (ξ : Form E X) (i : Fin A.nd) (d : Fin 2)
    (k : Fin (Module.finrank ℝ E)) (x : ℝ × ℝ) :
    formDiscRep A i d k (twist J₀ ξ) x = ∑ t : Fin 2 × Fin (Module.finrank ℝ E),
      aP J₀ (A.center i) (A.ε i) d t.1 k t.2 x * formDiscRep A i t.1 t.2 ξ x := by
  have hy := discPt_mem_source hT (A.center i) (A.ε i) x
  have e1 : ∀ k', ∑ d' : Fin 2,
      (jMat (A.center i) (X.discPt (A.center i) (A.ε i) x) (EuclideanSpace.single d 1)) d' *
        crd k' (ξ (X.discPt (A.center i) (A.ε i) x) (tangentCoordChange 𝓘(ℝ, E2) (A.center i)
          (X.discPt (A.center i) (A.ε i) x) (X.discPt (A.center i) (A.ε i) x)
          (EuclideanSpace.single d' 1))) =
      crd k' (ξ (X.discPt (A.center i) (A.ε i) x) (X.j.J (X.discPt (A.center i) (A.ε i) x)
        (tangentCoordChange 𝓘(ℝ, E2) (A.center i) (X.discPt (A.center i) (A.ε i) x)
          (X.discPt (A.center i) (A.ε i) x) (EuclideanSpace.single d 1)))) := fun k' => by
    have := sum_fin2_coord
      (jMat (A.center i) (X.discPt (A.center i) (A.ε i) x) (EuclideanSpace.single d 1))
      ((crd k').toContinuousLinearMap.comp ((ξ (X.discPt (A.center i) (A.ε i) x)).comp
        (tangentCoordChange 𝓘(ℝ, E2) (A.center i) (X.discPt (A.center i) (A.ε i) x)
          (X.discPt (A.center i) (A.ε i) x))))
    simp only [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap'] at this
    rw [this, tcc_jMat hy]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [formDiscRep, formAt_of_const hu, twist, ContinuousLinearMap.comp_apply, aP]
  rw [← sum_Jc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [← e1 k', Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d' _ => ?_
  have := discCut_mul_chiP x
  linear_combination -(Jc J₀ k k' * (jMat (A.center i) (X.discPt (A.center i) (A.ε i) x)
    (EuclideanSpace.single d 1)) d' * crd k' (ξ (X.discPt (A.center i) (A.ε i) x)
      (tangentCoordChange 𝓘(ℝ, E2) (A.center i) (X.discPt (A.center i) (A.ε i) x)
        (X.discPt (A.center i) (A.ε i) x) (EuclideanSpace.single d' 1)))) * this

end Projection

/-! ## 4. Block operators on the fibre blocks, at every level -/

section Operator

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {u : X.S → Q} {A : SectionAtlas (E := E) X u}
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

/-- The indices `(disc, direction, coordinate)` of the disc blocks. -/
abbrev Ix (A : SectionAtlas (E := E) X u) := Fin A.nd × Fin 2 × Fin (Module.finrank ℝ E)

variable {T : Type} [Fintype T] (D : Ix A → T → ChartChange) (a : Ix A → T → ℝ × ℝ → ℝ)
  (hc : ∀ o t, ContDiff ℝ ∞ (a o t)) (hs : ∀ o t, tsupport (a o t) ⊆ (D o t).K)
  (src : Ix A → T → Ix A)

variable (δ h0 hmono) in
/-- The disc block `o` of `fOp`. -/
def fBlock (n : ℕ) (o : Ix A) :
    (fibreBlocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  ∑ t, ((D o t).op (2 + n) (Neck.δ_nonneg δ h0 hmono n) (hc o t) (hs o t)
      (Neck.δ_nonneg δ h0 hmono n)).comp
        ((ContinuousLinearMap.proj (src o t)).comp (ContinuousLinearMap.fst ℝ _ _))

variable (δ h0 hmono) in
/-- `(Φv)_o = ∑_t a_{o,t} · (v_{src(o,t)} ∘ ψ_{o,t})` on the disc blocks, `0` on the neck blocks. -/
def fOp (n : ℕ) : (fibreBlocks A δ h0 hmono) n →L[ℝ] (fibreBlocks A δ h0 hmono) n :=
  (ContinuousLinearMap.pi fun o => fBlock δ h0 hmono D a hc hs src n o).prod 0

lemma val_fOp (n : ℕ) (v : (fibreBlocks A δ h0 hmono) n) (o : Ix A) :
    H.val ((fOp δ h0 hmono D a hc hs src n v).1 o) =
      ∑ t, (D o t).compMul (a o t) (H.val (v.1 (src o t))) := by
  have e1 : (fOp δ h0 hmono D a hc hs src n v).1 o = ∑ t, (D o t).op (2 + n)
      (Neck.δ_nonneg δ h0 hmono n) (hc o t) (hs o t) (Neck.δ_nonneg δ h0 hmono n)
        (v.1 (src o t)) := by
    change fBlock δ h0 hmono D a hc hs src n o v = _
    rw [fBlock, _root_.sum_apply]
    rfl
  rw [e1]
  refine (map_sum (valCLM (2 + n) (Neck.δ_nonneg δ h0 hmono n)) _ _).trans
    (Finset.sum_congr rfl fun t _ => ?_)
  exact ChartChange.val_op (hc o t) (hs o t) (Neck.δ_nonneg δ h0 hmono n) _

lemma val_fibre_toBase (n : ℕ) (w : (fibreBlocks A δ h0 hmono) n) (o : Ix A) :
    H.val (((fibreBlocks A δ h0 hmono).toBase n w).1 o) = H.val (w.1 o) := by
  have e1 := ScBanach.prod_toBase
    (finPiSc fun _ : Ix A => Neck.scCylOff 2 δ h0 hmono)
    (finPiSc fun _ : Fin A.nn × Fin (Module.finrank ℝ E) => Neck.scCylOff 2 δ h0 hmono) n w
  have e2 := finPiScale_toBase
    (fun _ : Ix A => (Neck.scCylOff 2 δ h0 hmono).toScScale) n w.1
  have e3 : ((fibreBlocks A δ h0 hmono).toBase n w).1 o =
      (Neck.scCylOff 2 δ h0 hmono).toBase n (w.1 o) := by
    change (((finPiSc _).prod (finPiSc _)).toBase n w).1 o = _
    rw [e1]
    exact congrFun e2 o
  rw [e3]
  exact Neck.val_toBaseOff 2 δ h0 hmono n (w.1 o)

lemma toBase_fOp (hnn : IsEmpty (Fin A.nn)) (n : ℕ) (v : (fibreBlocks A δ h0 hmono) n) :
    (fibreBlocks A δ h0 hmono).toBase n (fOp δ h0 hmono D a hc hs src n v) =
      fOp δ h0 hmono D a hc hs src 0 ((fibreBlocks A δ h0 hmono).toBase n v) := by
  refine Prod.ext (funext fun o => ?_) (funext fun jk => isEmptyElim jk.1)
  apply valCLM_injective (m := 2) (hδ := Neck.δ_nonneg δ h0 hmono 0)
  refine ((val_fibre_toBase n _ o).trans ?_).trans (val_fOp D a hc hs src 0 _ o).symm
  rw [val_fOp]
  exact Finset.sum_congr rfl fun t _ => by rw [val_fibre_toBase]

lemma coeFn_fOp (v : (fibreBlocks A δ h0 hmono) 0) (o : Ix A) :
    (H.val ((fOp δ h0 hmono D a hc hs src 0 v).1 o) : ℝ × ℝ → ℝ) =ᵐ[cyl]
      fun x => ∑ t, a o t x * H.val (v.1 (src o t)) ((D o t).ψ x) := by
  rw [val_fOp]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      fun t => (D o t).compMul (a o t) (H.val (v.1 (src o t))),
    ae_all_iff.2 fun t => (D o t).coeFn_compMul (hc o t).continuous (hs o t)
      (H.val (v.1 (src o t)))] with x h1 h2
  rw [h1]
  exact Finset.sum_congr rfl fun t _ => h2 t

end Operator

/-! ## 5. Forms from test functions, and the change of charts on representatives -/

section TestForms

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} (hT : ChartsOnto X) {q : Q} {u : X.S → Q}
  (hu : ∀ x, u x = q) (A : SectionAtlas (E := E) X u)

lemma crd_symm (k : Fin (Module.finrank ℝ E)) (f : Fin (Module.finrank ℝ E) → ℝ) :
    crd k ((Module.finBasis ℝ E).equivFun.symm f) = f k := by
  rw [crd, Module.Basis.coord_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

/-- The form of the test functions `φ_{j,·,·}` in the disc chart `j`:
`y ↦ discCut(p_j y)⁻¹ · ∑_k (∑_{d'} φ_{j,d',k}(p_j y) · (T_{y→z_j} ·)_{d'}) e_k`. -/
def testForm (φ : Ix A → ℝ × ℝ → ℝ) (j : Fin A.nd) : Form E X := fun y =>
  (discCut (stripPt (A.center j) (A.ε j) y))⁻¹ •
    (LinearMap.toContinuousLinearMap (Module.finBasis ℝ E).equivFun.symm.toLinearMap).comp
      (ContinuousLinearMap.pi fun k => ∑ d' : Fin 2,
        φ (j, d', k) (stripPt (A.center j) (A.ε j) y) •
          (EuclideanSpace.proj d' : E2 →L[ℝ] ℝ).comp
            (tangentCoordChange 𝓘(ℝ, E2) y (A.center j) y))

include hT hu in
/-- Where the cut-off does not vanish, the representative of `testForm` is the test function. -/
lemma formDiscRep_testForm (φ : Ix A → ℝ × ℝ → ℝ) (j : Fin A.nd) (d' : Fin 2)
    (k : Fin (Module.finrank ℝ E)) {x : ℝ × ℝ} (hx : discCut x ≠ 0) :
    formDiscRep A j d' k (testForm A φ j) x = φ (j, d', k) x := by
  have hy := discPt_mem_source hT (A.center j) (A.ε j) x
  have hs : stripPt (A.center j) (A.ε j) (X.discPt (A.center j) (A.ε j) x) = x := by
    rw [stripPt, extChartAt_discPt hT, placeInv_place _ (A.ε_pos j).ne']
  have hT2 : ∀ w, tangentCoordChange 𝓘(ℝ, E2) (X.discPt (A.center j) (A.ε j) x) (A.center j)
      (X.discPt (A.center j) (A.ε j) x) (tangentCoordChange 𝓘(ℝ, E2) (A.center j)
        (X.discPt (A.center j) (A.ε j) x) (X.discPt (A.center j) (A.ε j) x) w) = w := fun w => by
    rw [tangentCoordChange_comp ⟨⟨hy, mem_extChartAt_source _⟩, hy⟩, tangentCoordChange_self hy]
  simp only [formDiscRep, formAt_of_const hu, testForm, hs, ContinuousLinearMap.comp_apply,
    smul_apply, LinearMap.coe_toContinuousLinearMap', map_smul,
    LinearEquiv.coe_coe, crd_symm, ContinuousLinearMap.pi_apply, FunLike.coe_sum,
    Finset.sum_apply, hT2, smul_eq_mul]
  simp
  field_simp

include hu in
lemma formDiscRep_sum (ρ : Fin A.nd → X.S → ℝ) (ξs : Fin A.nd → Form E X) (i : Fin A.nd)
    (d : Fin 2) (k : Fin (Module.finrank ℝ E)) (x : ℝ × ℝ) :
    formDiscRep A i d k (fun y => ∑ j, ρ j y • ξs j y) x =
      ∑ j, ρ j (X.discPt (A.center i) (A.ε i) x) * formDiscRep A i d k (ξs j) x := by
  simp only [formDiscRep, formAt_of_const hu, ContinuousLinearMap.comp_apply,
    FunLike.coe_sum, Finset.sum_apply, smul_apply, map_sum,
    map_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The coefficients of the change of charts (`coef`), indexed for `fOp`. -/
def aG (ρ : Fin A.nd → X.S → ℝ) (o : Ix A) (t : Fin A.nd × Fin 2) : ℝ × ℝ → ℝ :=
  coef (ρ t.1) (A.center o.1) (A.ε o.1) (A.center t.1) (A.ε t.1) o.2.1 t.2

/-- The source block of a term of the change of charts. -/
def srcG (o : Ix A) (t : Fin A.nd × Fin 2) : Ix A := (t.1, t.2, o.2.2)

/-- The coefficients of the projection (`aP`), indexed for `fOp`. -/
def aPI (J₀ : E →L[ℝ] E) (o : Ix A) (t : Fin 2 × Fin (Module.finrank ℝ E)) : ℝ × ℝ → ℝ :=
  aP J₀ (A.center o.1) (A.ε o.1) o.2.1 t.1 o.2.2 t.2

/-- The source block of a term of the projection. -/
def srcP (o : Ix A) (t : Fin 2 × Fin (Module.finrank ℝ E)) : Ix A := (o.1, t.1, t.2)

variable {A} {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}
  {ρ : Fin A.nd → X.S → ℝ} (hρ : ∀ j, tsupport (ρ j) ⊆ discSet (A.center j) (A.ε j))
  {D : Fin A.nd → Fin A.nd → ChartChange}
  (hDK : ∀ i j, (D i j).K = pieceK (ρ j) (A.center i) (A.ε i))
  (hDψ : ∀ i j, ∀ p ∈ (D i j).K,
    (D i j).ψ p = dtrans (A.center i) (A.ε i) (A.center j) (A.ε j) p)
  (hcG : ∀ o t, ContDiff ℝ ∞ (aG A ρ o t)) (hsG : ∀ o t, tsupport (aG A ρ o t) ⊆ (D o.1 t.1).K)

include hT hu hρ hDK hDψ in
/-- The change of charts applied to a tuple that agrees, on each piece, with the representatives
of forms `ξ_j`: the result is `∑_j ρ_j · ` (representative of `ξ_j`). -/
lemma G_ae {v : (fibreBlocks A δ h0 hmono) 0} (ξs : Fin A.nd → Form E X)
    (hv : ∀ o t, (fun x => aG A ρ o t x * H.val (v.1 (srcG A o t)) ((D o.1 t.1).ψ x)) =ᵐ[cyl]
      fun x => aG A ρ o t x * formDiscRep A t.1 t.2 o.2.2 (ξs t.1) ((D o.1 t.1).ψ x))
    (o : Ix A) :
    (H.val ((fOp δ h0 hmono (fun o t => D o.1 t.1) (aG A ρ) hcG hsG (srcG A) 0 v).1 o) :
      ℝ × ℝ → ℝ) =ᵐ[cyl] fun x => ∑ j, ρ j (X.discPt (A.center o.1) (A.ε o.1) x) *
        formDiscRep A o.1 o.2.1 o.2.2 (ξs j) x := by
  filter_upwards [coeFn_fOp _ _ hcG hsG _ v o, ae_all_iff.2 (hv o)] with x h1 h2
  rw [h1, Finset.sum_congr rfl fun t _ => h2 t, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun j _ =>
    piece_sum_eq hT hu (hρ j) (hDK o.1 j) (hDψ o.1 j) o.2.1 o.2.2 (ξs j) x

include hT hu in
/-- The projection operator applied to a representative of `ξ` is the representative of
`J₀ ∘ ξ ∘ j`. -/
lemma P_rep (hnn : IsEmpty (Fin A.nn)) (J₀ : E →L[ℝ] E) (hcP : ∀ o t, ContDiff ℝ ∞ (aPI A J₀ o t))
    (hsP : ∀ o t, tsupport (aPI A J₀ o t) ⊆ ((fun _ _ => idCC) o t : ChartChange).K)
    {ξ : Form E X} {v : (fibreBlocks A δ h0 hmono) 0} (hv : IsFormRep ξ v) :
    IsFormRep (twist J₀ ξ) (fOp δ h0 hmono (fun _ _ => idCC) (aPI A J₀) hcP hsP (srcP A) 0 v) := by
  refine ⟨fun i d k => ?_, fun j => isEmptyElim j⟩
  filter_upwards [coeFn_fOp _ _ hcP hsP _ v (i, d, k),
    ae_all_iff.2 fun t : Fin 2 × Fin (Module.finrank ℝ E) => hv.1 i t.1 t.2] with x h1 h2
  refine h1.trans ?_
  rw [formDiscRep_twist hT hu A]
  exact Finset.sum_congr rfl fun t _ => congrArg (aPI A J₀ (i, d, k) t x * ·) (h2 t)

end TestForms

/-! ## 6. Density of the smooth forms -/

section Dense

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m}

/-- **The smooth forms are dense** (Memoir p. 51, the fibre `H^{2,δ₀}` of `W` over `u` is an
sc-subspace of the block space): on a surface without nodes whose charts are onto `ℝ²`, for a
constant map, any almost complex structure and any atlas, `FormsDense`. -/
theorem formsDense_const (hX : X.nodes = ∅) (hT : ChartsOnto X) {q : Q} {u : X.S → Q}
    (hu : ∀ x, u x = q) (J : AlmostComplexStructure E Q) (A : SectionAtlas (E := E) X u)
    (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) : FormsDense J A δ h0 hmono := by
  obtain ⟨ρ, hρ⟩ := exists_partition hX hT A
  have hρ' : ∀ j, tsupport (ρ j) ⊆ discSet (A.center j) (A.ε j) := hρ
  choose D hDK hDψ using fun i j : Fin A.nd =>
    exists_chartChange hT (ρ := ρ j) (z := A.center i) (A.ε_pos i).ne' (A.ε_pos j).ne' (hρ' j)
  have hcG : ∀ o t, ContDiff ℝ ∞ (aG A (fun j => ρ j) o t) :=
    fun o t => contDiff_coef hT (ρ t.1) _ _ _ _ (hρ' t.1) _ _
  have hsG : ∀ o t, tsupport (aG A (fun j => ρ j) o t) ⊆ (D o.1 t.1).K :=
    fun o t => by
      rw [hDK o.1 t.1]
      exact tsupport_coef_sub hT _ _ _ _ _ _ _
  have hcP : ∀ o t, ContDiff ℝ ∞ (aPI A (J.J q) o t) := fun o t => contDiff_aP hT _ _ _ _ _ _ _
  have hsP : ∀ o t, tsupport (aPI A (J.J q) o t) ⊆ ((fun _ _ => idCC) o t : ChartChange).K :=
    fun o t => tsupport_aP _ _ _ _ _ _ _
  have hnn := isEmpty_neck_of_nodes_empty hX A
  set G := fOp δ h0 hmono (fun o t => D o.1 t.1) (aG A (fun j => ρ j)) hcG hsG (srcG A) with hG
  set P := fOp δ h0 hmono (fun _ _ => idCC) (aPI A (J.J q)) hcP hsP (srcP A) with hP
  set Φ : ∀ n, (fibreBlocks A δ h0 hmono) n →L[ℝ] (fibreBlocks A δ h0 hmono) n :=
    fun n => (1 / 2 : ℝ) • (G n + (P n).comp (G n)) with hΦ
  have hΦb : ∀ n v, (fibreBlocks A δ h0 hmono).toBase n (Φ n v) =
      Φ 0 ((fibreBlocks A δ h0 hmono).toBase n v) := by
    intro n v
    simp only [hΦ, smul_apply, add_apply, ContinuousLinearMap.comp_apply,
      map_smul, map_add, hG, hP, toBase_fOp _ _ _ _ _ hnn]
  -- the change of charts reproduces representatives
  have hGrep : ∀ ξ v, IsFormRep ξ v → IsFormRep ξ (G 0 v) := by
    intro ξ v hv
    refine ⟨fun i d k => ?_, fun j => isEmptyElim j⟩
    refine (G_ae hT hu hρ' hDK hDψ hcG hsG (fun _ => ξ)
      (fun o t => ChartChange.comp_congr (hsG o t) (hv.1 t.1 t.2 o.2.2)) (i, d, k)).trans
      (Eventually.of_forall fun x => ?_)
    change ∑ j, ρ j _ * _ = _
    rw [← Finset.sum_mul]
    have h := ρ.sum_eq_one (x := X.discPt (A.center i) (A.ε i) x) (mem_univ _)
    rw [finsum_eq_sum_of_fintype] at h
    rw [h, one_mul]
  -- `Φ` maps a representative of `G`-output to the representative of the projection
  have hrep : ∀ ξ v, IsFormRep ξ (G 0 v) → IsFormRep (projF (J.J q) ξ) (Φ 0 v) := fun ξ v hv =>
    (hv.add (P_rep hT hu hnn (J.J q) hcP hsP hv)).smul (1 / 2 : ℝ)
  have hfix : ∀ v ∈ formsSub J A δ h0 hmono, Φ 0 v = v := by
    rintro v ⟨ξ, ha, hv⟩
    have hp : projF (J.J q) ξ = ξ := funext fun y => projF_of_mem (by
      have := ha y (by rw [hX]; simp)
      rwa [hu y] at this)
    have h := hrep ξ v (hGrep ξ v hv)
    rw [hp] at h
    exact h.unique hv
  have htest : ∀ w : (fibreBlocks A δ h0 hmono) 0,
      (∀ o, ∃ φ, ∃ hφ : IsTest φ, w.1 o = toH (2 + 0) (Neck.δ_nonneg δ h0 hmono 0) hφ) →
        Φ 0 w ∈ formsSub J A δ h0 hmono := by
    intro w hw
    choose φ hφ hwφ using hw
    have hG' : IsFormRep (fun y => ∑ j, ρ j y • testForm A φ j y) (G 0 w) := by
      refine ⟨fun i d k => ?_, fun j => isEmptyElim j⟩
      refine (G_ae hT hu hρ' hDK hDψ hcG hsG (fun j => testForm A φ j) (fun o t => ?_)
        (i, d, k)).trans (Eventually.of_forall fun x =>
          (formDiscRep_sum hu A (fun j => ρ j) _ i d k x).symm)
      refine (ChartChange.comp_congr (hsG o t) (f' := φ (srcG A o t)) (by
        rw [hwφ (srcG A o t)]; exact MemLp.coeFn_toLp ((hφ _).memLp 2))).trans
        (Eventually.of_forall fun x => ?_)
      change aG A (fun j => ρ j) o t x * φ (srcG A o t) ((D o.1 t.1).ψ x) =
        aG A (fun j => ρ j) o t x * formDiscRep A t.1 t.2 o.2.2 (testForm A φ t.1) ((D o.1 t.1).ψ x)
      by_cases hx : aG A (fun j => ρ j) o t x = 0
      · rw [hx, zero_mul, zero_mul]
      have hxK : x ∈ pieceK (ρ t.1) (A.center o.1) (A.ε o.1) :=
        tsupport_coef_sub hT _ _ _ _ _ _ _ (subset_tsupport _ hx)
      have hxD := pieceK_sub (hρ' t.1) hxK
      rw [hDψ o.1 t.1 x ((hDK o.1 t.1).symm ▸ hxK),
        formDiscRep_testForm hT hu A φ t.1 t.2 o.2.2 (discCut_pos (pieceDom_sub hxD).2).ne']
      rfl
    refine ⟨projF (J.J q) _, fun y _ => ?_, hrep _ w hG'⟩
    rw [hu y]; exact projF_mem J q _ y
  -- density
  let T : Set ((fibreBlocks A δ h0 hmono) 0) :=
    (univ.pi fun _ => {g : (Neck.scCylOff 2 δ h0 hmono) 0 |
      ∃ φ, ∃ hφ : IsTest φ, g = toH (2 + 0) (Neck.δ_nonneg δ h0 hmono 0) hφ}) ×ˢ univ
  have hd : Dense T :=
    (dense_pi univ fun _ _ => dense_test (2 + 0) (Neck.δ_nonneg δ h0 hmono 0)).prod dense_univ
  have hmem : ∀ w, Φ 0 w ∈ fibreSpace J A δ h0 hmono := by
    intro w
    have h1 : Φ 0 w ∈ closure (Φ 0 '' T) :=
      image_closure_subset_closure_image (Φ 0).continuous ⟨w, hd w, rfl⟩
    refine closure_minimal (image_subset_iff.2 fun w hw => ?_)
      (isClosed_fibreSpace J A δ h0 hmono) h1
    exact formsSub_le J A δ h0 hmono (htest w fun o => hw.1 o (mem_univ _))
  have hfixF : ∀ v ∈ (fibreSpace J A δ h0 hmono : Set ((fibreBlocks A δ h0 hmono) 0)),
      Φ 0 v = v := by
    intro v hv
    rw [fibreSpace, Submodule.topologicalClosure_coe] at hv
    exact (show EqOn (Φ 0) id (formsSub J A δ h0 hmono : Set _) from fun v hv => hfix v hv).closure
      (Φ 0).continuous continuous_id hv
  refine (formsDense_iff A δ h0 hmono J).2 fun k x hx => ?_
  have hx' : (fibreBlocks A δ h0 hmono).toBase k x ∈ fibreSpace J A δ h0 hmono := hx
  have hfx : Φ k x = x :=
    (fibreBlocks A δ h0 hmono).toBase_injective k (by rw [hΦb, hfixF _ hx'])
  have hsm : (fibreBlocks A δ h0 hmono).smoothLvl k ⊆ Φ k ⁻¹'
      ((fibreBlocks A δ h0 hmono).levelSub (fibreSpace J A δ h0 hmono) k ∩
        (fibreBlocks A δ h0 hmono).smoothLvl k) := fun y hy => by
    refine ⟨?_, (fibreBlocks A δ h0 hmono).mem_smoothLvl_iff.2 fun j => ?_⟩
    · change (fibreBlocks A δ h0 hmono).toBase k (Φ k y) ∈ fibreSpace J A δ h0 hmono
      rw [hΦb]; exact hmem _
    · obtain ⟨y', hy'⟩ := (fibreBlocks A δ h0 hmono).mem_smoothLvl_iff.1 hy j
      exact ⟨Φ j y', by rw [hΦb, hΦb, hy']⟩
  rw [← hfx]
  exact closure_mono (image_subset_iff.2 hsm) (image_closure_subset_closure_image
    (Φ k).continuous ⟨x, (fibreBlocks A δ h0 hmono).dense_smooth k x, rfl⟩)

/-- **Instance**: the constant maps from the three-pointed sphere, any almost complex structure,
any atlas. -/
theorem sphere3_formsDense (J : AlmostComplexStructure E Q) (q : Q)
    (A : SectionAtlas (E := E) sphere3 (fun _ => q)) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0)
    (hmono : StrictMono δ) : FormsDense J A δ h0 hmono :=
  formsDense_const rfl sphere3_chartsOnto (fun _ => rfl) J A δ h0 hmono

end Dense

end GWMemoir
