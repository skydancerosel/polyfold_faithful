import Polyfold.Chapter17.TangentVectors
import Polyfold.Chapter2.TangentConeQuadrant
import Polyfold.Chapter17.BranchedOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
Remark 17.2.18, p. 784, used in Theorem 18.1.5 (p. 846): **the partial cone `C_αC ⊆ T_αC` and the
reduced tangent space `T^R_αC` of a polyfold, independent of the uniformizer.**

# The partial cone of a polyfold at an object

## The text, paraphrased

(Remark 17.2.18) For a polyfold `C` and a smooth object `α`, `T_αC` is sc-Banachable; the partial
cone `C_αC ⊆ T_αC` and the reduced tangent space `T^R_αC` are defined following Definition 2.5.8
(2017: 2.4.7) in an sc-smooth model and pushed forward along the tangent of the equivalence; for
tame `C` the partial cone is a partial quadrant, and one can speak of a finite-dimensional
subspace in good position to `C_αC`.  Theorem 18.1.5 asks that `ker f'(α)` be in good position to
the boundary in this sense.

## What is formalized

* M-polyfolds: `MPolyfold.fiberCoord_tangentMapOnCLM_transportChart` (in the chart `ψ ∘ f`
  transported along an sc-diffeomorphism `f`, `Tf` is the identity of the model space), and
  **`MPolyfold.mem_partialConeFiber_tangentMapOnCLM_iff`**,
  **`MPolyfold.mem_reducedTangentFiber_tangentMapOnCLM_iff`**: the tangent map of an
  sc-diffeomorphism maps `C_xX` onto `C_{f(x)}Y` and `T^R_xX` onto `T^R_{f(x)}Y`, read in any
  charts and presentations of their partial quadrants (Proposition 2.4.10 through
  `partialConeFiber_eq`).
* `MPolyfold.tangentPartialCone x`, `MPolyfold.tangentReducedSpace x`: `C_xX` and `T^R_xX` in a
  chosen chart and presentation (`fiberChartPresentation`); `tangentPartialCone_eq`,
  `tangentReducedSpace_eq`: every chart and presentation gives them;
  `finrank_quotient_tangentReducedSpace_eq_degIndex`: `dim(T_xX / T^R_xX) = d_X(x)` for tame `X`.
* Polyfolds (namespace `GCT.PolyfoldConstruction`): `mem_partialConeFiber_transTangent_iff`
  (the `Tσ(q)` of an element of a transition set preserve partial cones);
  **`PolyfoldConstruction.partialCone α : Set (T_αC)`** and
  **`PolyfoldConstruction.reducedTangent α : Submodule ℝ (T_αC)`** (`C_αC`, `T^R_αC`), and
  **`partialCone_eq`**, **`reducedTangent_eq`**: for every `Ψ ∈ F(α)`, every chart of `O` around
  the point `q` over `α` and every presentation of its partial quadrant,
  `C_αC = S_Ψ⁻¹(C_qO)` and `T^R_αC = S_Ψ⁻¹(T^R_qO)` (independence of `Ψ`, Remark 17.2.18);
  `mem_reducedTangent_iff_lineality` (`T^R_αC = C_αC ∩ −C_αC`),
  `reducedTangent_subset_partialCone`;
  **`finrank_quotient_reducedTangent_eq_degIndex`** (`dim(T_αC / T^R_αC) = d_C(α)` for tame `C`
  and smooth `α`) and `partialCone_ne_univ` (`C_αC ≠ T_αC` on `∂C`).  The witness is at the corner
  of `ℤ/2 ⋉ [0, ∞) × ℝ` (`TangentPartialConeExamples.lean`).

## Readings

* `T_αC` is the space of Definition 17.2.3 with the charts `S_Ψ : T_αC ≅ T_qO` of
  Proposition 17.2.4; "defined in a model and pushed forward via `TΓ`" is read through these
  charts: `C_αC` is the preimage of `C_qO` (Definition 2.5.8) under `S_Ψ`.  The independence of
  the choice of `Ψ` is the content of the remark that is formalized here.
* "Good position of a finite-dimensional subspace to `C_αC`" is not a separate notion in this
  file; `GoodPositionIntrinsic.lean` formalizes it for `ker f'(α)` (`IsKernelInGoodPosition`) and
  proves it equivalent to Part I's good position of the local representative in a strong bundle
  uniformizer, the reading of `theorem_18_1_5_model` (`ImplicitFunctionTheorem.lean`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u v

/-! ### The tangent of an sc-diffeomorphism and the partial cones -/

section Transport

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
variable {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y} (h : P.IsScDiffeoOn Q f g U V)
  {ψ : MChart Y} (hψ : Q.IsChart ψ) {x : P.Level 1} {y : Q.Level 1}
  (hxU : P.levelVal 1 x ∈ U) (hxy : f (P.levelVal 1 x) = Q.levelVal 1 y)
  (hyψ : Q.levelVal 1 y ∈ ψ.source)

include hxU hxy hyψ in
theorem mem_transportChart_source :
    P.levelVal 1 x ∈ (transportChart h ψ).source :=
  ⟨hxU, by change f _ ∈ ψ.source; rw [hxy]; exact hyψ⟩

/-- **In the transported chart `ψ ∘ f`, `Tf` is the identity of the model space**:
`Tψ(f(x)) ∘ Tf(x) = T(ψ ∘ f)(x)` on `T_xX`. -/
theorem fiberCoord_tangentMapOnCLM_transportChart (α : P.tangentFiber x) :
    fiberCoord hψ hyψ (tangentMapOnCLM h.isScSmoothOn hxU hxy α) =
      fiberCoord (transportChart_isChart h hψ) (mem_transportChart_source h hxU hxy hyψ) α := by
  set χ := transportChart h ψ
  have hχ : P.IsChart χ := transportChart_isChart h hψ
  have hxχ : P.levelVal 1 x ∈ χ.source := mem_transportChart_source h hxU hxy hyψ
  have hf := h.isScSmoothOn
  rw [fiberCoord_apply, fiberCoord_apply, tangentMapOnCLM_apply]
  have hVo : IsOpen (TangentPre.fdomOn U χ f ψ) := TangentPre.isOpen_fdomOn hf χ ψ
  have hVφ : TangentPre.fdomOn U χ f ψ ⊆ χ.source := TangentPre.fdomOn_subset _ _ _ _
  have hxV : P.levelVal 1 x ∈ TangentPre.fdomOn U χ f ψ := by
    refine ⟨⟨hxU, hxχ⟩, ?_⟩
    change f (P.levelVal 1 x) ∈ ψ.source
    rw [hxy]; exact hyψ
  have hmem : α.1 ∈ P.tangentPreimage (TangentPre.fdomOn U χ f ψ) := by
    rw [mem_tangentPreimage, tangentProj_eq_of_mem_fiber α.2]; exact hxV
  have hαV : tangentChartMap hχ α.1 ∈ retractTangent χ.model.E χ.model.C
      (χ '' TangentPre.fdomOn U χ f ψ) := by
    refine (TangentPre.mem_retractTangent_image_iff hVφ hVo ?_).2
      (tangentChartMap_mem hχ (mem_tangentChartSet_of_mem_fiber hxχ α.2))
    rw [tangentChartMap_fst_of_mem_fiber hχ hxχ α.2, P.toBase_levelLift hχ hxχ (levelVal_mem x)]
    exact ⟨_, hxV, rfl⟩
  rw [tangentChartMap_tangentMapOn hf hχ hψ hmem]
  have hO := χ.isScRetract_image hVφ hVo
  have hid : EqOn (ψ ∘ f ∘ χ.symm) id (χ '' TangentPre.fdomOn U χ f ψ) := by
    rintro _ ⟨w, hw, rfl⟩
    change ψ (f (χ.symm (χ w))) = χ w
    rw [χ.symm_apply_apply (hVφ hw)]
    rfl
  exact congrArg Prod.snd (retractTangentMap_id hO hid hαV)

variable {φ : MChart X} (hφ : P.IsChart φ) (hxφ : P.levelVal 1 x ∈ φ.source)
  {n : ℕ} {W : ScBanach} (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
  (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0)
  {n' : ℕ} {W' : ScBanach} (T' : ScIso ψ.model.E ((ScBanach.const (Fin n' → ℝ)).prod W'))
  (hT' : ψ.model.C = T' 0 ⁻¹' quadrant n' W' 0)

include hT hT' in
/-- **The tangent of an sc-diffeomorphism preserves partial cones** (Proposition 2.4.10 with
Definition 2.5.8): `Tf(x)α ∈ C_{f(x)}Y` iff `α ∈ C_xX`, read in any charts `φ` around `x`, `ψ`
around `f(x)` and any presentations of their partial quadrants. -/
theorem mem_partialConeFiber_tangentMapOnCLM_iff (α : P.tangentFiber x) :
    tangentMapOnCLM h.isScSmoothOn hxU hxy α ∈ partialConeFiber hψ hyψ T' ↔
      α ∈ partialConeFiber hφ hxφ T := by
  have hχ := transportChart_isChart h hψ
  have hxχ := mem_transportChart_source h hxU hxy hyψ
  rw [partialConeFiber_eq hφ hxφ T hχ hxχ T' hT hT']
  change fiberCoord hψ hyψ _ ∈ partialQuadrantAtWith T' (ψ (Q.levelVal 1 y)) ↔
    fiberCoord hχ hxχ α ∈ partialQuadrantAtWith T' (ψ (f (P.levelVal 1 x)))
  rw [fiberCoord_tangentMapOnCLM_transportChart h hψ hxU hxy hyψ α, hxy]
  exact Iff.rfl

include hT hT' in
/-- **The tangent of an sc-diffeomorphism preserves reduced tangent spaces**: `Tf(x)α ∈ T^R_{f(x)}Y`
iff `α ∈ T^R_xX`, in any charts and presentations. -/
theorem mem_reducedTangentFiber_tangentMapOnCLM_iff (α : P.tangentFiber x) :
    tangentMapOnCLM h.isScSmoothOn hxU hxy α ∈ reducedTangentFiber hψ hyψ T' ↔
      α ∈ reducedTangentFiber hφ hxφ T := by
  rw [mem_reducedTangentFiber_iff_lineality, mem_reducedTangentFiber_iff_lineality, ← map_neg,
    mem_partialConeFiber_tangentMapOnCLM_iff h hψ hxU hxy hyψ hφ hxφ T hT T' hT',
    mem_partialConeFiber_tangentMapOnCLM_iff h hψ hxU hxy hyψ hφ hxφ T hT T' hT']

end Transport

/-! ### `C_xX` and `T^R_xX` in a chosen chart -/

section Chosen

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

variable (P) in
/-- The number of corner coordinates of the chosen presentation of the partial quadrant of the
chart `fiberChart x`. -/
def fiberChartDim (x : P.Level 1) : ℕ := (P.fiberChart x).model.isPartialQuadrant.choose

variable (P) in
/-- The complement of the corner coordinates in the chosen presentation. -/
def fiberChartComplement (x : P.Level 1) : ScBanach :=
  (P.fiberChart x).model.isPartialQuadrant.choose_spec.choose

variable (P) in
/-- The chosen presentation `T : E ≅ ℝⁿ ⊕ W` of the partial quadrant of `fiberChart x`. -/
def fiberChartPresentation (x : P.Level 1) :
    ScIso (P.fiberChart x).model.E
      ((ScBanach.const (Fin (P.fiberChartDim x) → ℝ)).prod (P.fiberChartComplement x)) :=
  (P.fiberChart x).model.isPartialQuadrant.choose_spec.choose_spec.choose

theorem fiberChartPresentation_spec (x : P.Level 1) :
    (P.fiberChart x).model.C =
      P.fiberChartPresentation x 0 ⁻¹' quadrant (P.fiberChartDim x) (P.fiberChartComplement x) 0 :=
  (P.fiberChart x).model.isPartialQuadrant.choose_spec.choose_spec.choose_spec

variable (P) in
/-- **The partial cone `C_xX ⊆ T_xX`** (Definition 2.5.8, 2021 p. 57), in the chosen chart; every
chart and presentation gives the same set (`tangentPartialCone_eq`). -/
def tangentPartialCone (x : P.Level 1) : Set (P.tangentFiber x) :=
  partialConeFiber (P.isChart_fiberChart x) (P.mem_fiberChart_source x) (P.fiberChartPresentation x)

variable (P) in
/-- **The reduced tangent space `T^R_xX ⊆ T_xX`** (Definition 2.5.8), in the chosen chart; every
chart and presentation gives the same subspace (`tangentReducedSpace_eq`). -/
def tangentReducedSpace (x : P.Level 1) : Submodule ℝ (P.tangentFiber x) :=
  reducedTangentFiber (P.isChart_fiberChart x) (P.mem_fiberChart_source x)
    (P.fiberChartPresentation x)

variable {φ : MChart X} {x : P.Level 1} (hφ : P.IsChart φ) (hxφ : P.levelVal 1 x ∈ φ.source)
  {n : ℕ} {W : ScBanach} (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
  (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0)

include hT in
theorem tangentPartialCone_eq : P.tangentPartialCone x = partialConeFiber hφ hxφ T :=
  partialConeFiber_eq _ _ _ hφ hxφ T (fiberChartPresentation_spec x) hT

include hT in
theorem tangentReducedSpace_eq : P.tangentReducedSpace x = reducedTangentFiber hφ hxφ T :=
  reducedTangentFiber_eq _ _ _ hφ hxφ T (fiberChartPresentation_spec x) hT

omit hφ hxφ in
/-- **`dim(T_xX / T^R_xX) = d_X(x)`** for a tame `X` and a smooth `x` (Definition 2.5.8 with
Proposition 2.5.6 (13)), in the chosen chart. -/
theorem finrank_quotient_tangentReducedSpace_eq_degIndex (hP : P.IsTame)
    (hs : P.levelVal 1 x ∈ P.smoothSet) :
    Module.finrank ℝ (P.tangentFiber x ⧸ P.tangentReducedSpace x) =
      P.degIndex (P.levelVal 1 x) := by
  obtain ⟨φ, hφ, hxφ, R, hR, htame⟩ := IsTame.exists_chart P hP (P.levelVal 1 x)
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  rw [tangentReducedSpace_eq hφ hxφ T hT]
  exact finrank_quotient_reducedTangentFiber_eq_degIndex hφ hxφ T R hR hT (htame n W T hT) hs

end Chosen

end MPolyfold

/-! ### Polyfolds -/

namespace GCT.PolyfoldConstruction

universe u

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-- **The `Tσ(q)` of an element `a = (q, φ, q')` of a transition set preserve partial cones**: for
charts around `q` and `q'` and presentations of their partial quadrants,
`Tσ(q)v ∈ C_{q'}O'` iff `v ∈ C_qO`. -/
theorem mem_partialConeFiber_transTangent_iff {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ')
    {x : Ψ.1.P.Level 1} {y : Ψ'.1.P.Level 1} (hx : Ψ.1.P.levelVal 1 x = a.src)
    (hy : Ψ'.1.P.levelVal 1 y = a.tgt)
    {φ : MChart Ψ.1.O} (hφ : Ψ.1.P.IsChart φ) (hxφ : Ψ.1.P.levelVal 1 x ∈ φ.source)
    {n : ℕ} {W : ScBanach} (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0)
    {ψ : MChart Ψ'.1.O} (hψ : Ψ'.1.P.IsChart ψ) (hyψ : Ψ'.1.P.levelVal 1 y ∈ ψ.source)
    {n' : ℕ} {W' : ScBanach} (T' : ScIso ψ.model.E ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hT' : ψ.model.C = T' 0 ⁻¹' quadrant n' W' 0) (v : Ψ.1.P.tangentFiber x) :
    S.transTangent a hx hy v ∈ MPolyfold.partialConeFiber hψ hyψ T' ↔
      v ∈ MPolyfold.partialConeFiber hφ hxφ T :=
  MPolyfold.mem_partialConeFiber_tangentMapOnCLM_iff (S.triple a).isScDiffeoOn_sigma hψ
    (show Ψ.1.P.levelVal 1 x ∈ (S.triple a).srcSet by rw [hx]; exact (S.triple a).src_mem)
    (by rw [hx, (S.triple a).sigma_src, hy]) hyψ hφ hxφ T hT T' hT' v

section Cone

variable (α : C.Obj) [hα : Fact (S.TangentObj α)]

variable (S) in
/-- **The partial cone `C_αC ⊆ T_αC`** (Remark 17.2.18, 2021 p. 784): the preimage of the partial
cone `C_{q_α}O_α` (Definition 2.5.8) under the reference chart `S_{Ψ_α}`.  It is the preimage of
`C_qO` under `S_Ψ` for every `Ψ ∈ F(α)` (`partialCone_eq`). -/
def partialCone : Set (S.TangentSpaceAt α) :=
  S.refChartCLE α ⁻¹' (S.refUnif hα.out).1.P.tangentPartialCone (S.refPoint hα.out)

variable (S) in
/-- **The reduced tangent space `T^R_αC ⊆ T_αC`** (Remark 17.2.18, 2021 p. 784): the preimage of
`T^R_{q_α}O_α` under `S_{Ψ_α}`; the preimage of `T^R_qO` under every `S_Ψ` (`reducedTangent_eq`). -/
def reducedTangent : Submodule ℝ (S.TangentSpaceAt α) :=
  ((S.refUnif hα.out).1.P.tangentReducedSpace (S.refPoint hα.out)).comap
    (S.refChartCLE α : S.TangentSpaceAt α →ₗ[ℝ] _)

/-- `S_Ψ = Tσ(q_α) ∘ S_{Ψ_α}` for `σ` of `(q_α, 1_α, q)`. -/
theorem tangentChartCLE_apply (Ψ : S.Unif) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) (e : S.TangentSpaceAt α) :
    S.tangentChartCLE α Ψ x hx e =
      S.transTangent (S.unitTr _ _ (obj_refPoint hα.out) hx) rfl rfl (S.refChartCLE α e) := rfl

/-- **Remark 17.2.18, the independence of the partial cone** (2021 p. 784): for every
`Ψ ∈ F(α)`, the point `q` with `Ψ(q) = α`, every chart `φ` of `O` around `q` and every
presentation `T` of its partial quadrant, `C_αC = S_Ψ⁻¹(C_qO)`. -/
theorem partialCone_eq (Ψ : S.Unif) (x : Ψ.1.P.Level 1) (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α)
    {φ : MChart Ψ.1.O} (hφ : Ψ.1.P.IsChart φ) (hxφ : Ψ.1.P.levelVal 1 x ∈ φ.source)
    {n : ℕ} {W : ScBanach} (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) :
    S.partialCone α = S.tangentChartCLE α Ψ x hx ⁻¹' MPolyfold.partialConeFiber hφ hxφ T := by
  ext e
  exact (mem_partialConeFiber_transTangent_iff (S.unitTr _ _ (obj_refPoint hα.out) hx) rfl rfl
    (MPolyfold.isChart_fiberChart _ _) (MPolyfold.mem_fiberChart_source _ _)
    (MPolyfold.fiberChartPresentation _ _) (MPolyfold.fiberChartPresentation_spec _) hφ hxφ T hT
    (S.refChartCLE α e)).symm

/-- `T^R_αC = C_αC ∩ −C_αC`. -/
theorem mem_reducedTangent_iff_lineality (e : S.TangentSpaceAt α) :
    e ∈ S.reducedTangent α ↔ e ∈ S.partialCone α ∧ -e ∈ S.partialCone α := by
  change S.refChartCLE α e ∈ (S.refUnif hα.out).1.P.tangentReducedSpace (S.refPoint hα.out) ↔
    S.refChartCLE α e ∈ (S.refUnif hα.out).1.P.tangentPartialCone (S.refPoint hα.out) ∧
      S.refChartCLE α (-e) ∈ (S.refUnif hα.out).1.P.tangentPartialCone (S.refPoint hα.out)
  rw [map_neg]
  exact MPolyfold.mem_reducedTangentFiber_iff_lineality _ _ _ _

/-- **Remark 17.2.18, the independence of the reduced tangent space** (2021 p. 784): for every
`Ψ ∈ F(α)`, chart `φ` around the point over `α` and presentation `T`,
`T^R_αC = S_Ψ⁻¹(T^R_qO)`. -/
theorem reducedTangent_eq (Ψ : S.Unif) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α)
    {φ : MChart Ψ.1.O} (hφ : Ψ.1.P.IsChart φ) (hxφ : Ψ.1.P.levelVal 1 x ∈ φ.source)
    {n : ℕ} {W : ScBanach} (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) (e : S.TangentSpaceAt α) :
    e ∈ S.reducedTangent α ↔
      S.tangentChartCLE α Ψ x hx e ∈ MPolyfold.reducedTangentFiber hφ hxφ T := by
  rw [mem_reducedTangent_iff_lineality, MPolyfold.mem_reducedTangentFiber_iff_lineality,
    partialCone_eq α Ψ x hx hφ hxφ T hT, mem_preimage, mem_preimage, map_neg]

/-- **`dim(T_αC / T^R_αC) = d_C(α)`** for a tame polyfold `C` and a smooth object `α` (Remark
17.2.18 with Definitions 2.5.8 and 17.1.30): the reduced tangent space has codimension the
degeneracy index. -/
theorem finrank_quotient_reducedTangent_eq_degIndex (htame : S.IsTame) (hs : S.IsSmoothObj α) :
    Module.finrank ℝ (S.TangentSpaceAt α ⧸ S.reducedTangent α) = S.degIndex α := by
  set Ψ := S.refUnif hα.out
  set x := S.refPoint hα.out
  have hmap : (S.reducedTangent α).map ((S.refChartCLE α).toLinearEquiv :
      S.TangentSpaceAt α →ₗ[ℝ] Ψ.1.P.tangentFiber x) = Ψ.1.P.tangentReducedSpace x :=
    Submodule.map_comap_eq_of_surjective (S.refChartCLE α).surjective _
  have hsx : Ψ.1.P.levelVal 1 x ∈ Ψ.1.P.smoothSet :=
    (isSmoothObj_obj_iff Ψ _).1 (by rw [obj_refPoint hα.out]; exact hs)
  rw [(Submodule.Quotient.equiv _ _ (S.refChartCLE α).toLinearEquiv hmap).finrank_eq,
    MPolyfold.finrank_quotient_tangentReducedSpace_eq_degIndex
      (htame _ _ (refUnif_mem hα.out)) hsx,
    definition_17_1_30 (refUnif_mem hα.out) (obj_refPoint hα.out)]

/-- **On the boundary the partial cone is a proper cone**: for a tame `C` and a smooth `α ∈ ∂C`
(`d_C(α) ≥ 1`), `C_αC ≠ T_αC`. -/
theorem partialCone_ne_univ (htame : S.IsTame) (hs : S.IsSmoothObj α)
    (hb : 1 ≤ S.degIndex α) : S.partialCone α ≠ univ := by
  intro h
  have htop : S.reducedTangent α = ⊤ := eq_top_iff.2 fun e _ =>
    (mem_reducedTangent_iff_lineality α e).2 ⟨h ▸ mem_univ e, h ▸ mem_univ (-e)⟩
  have h0 := finrank_quotient_reducedTangent_eq_degIndex α htame hs
  rw [htop] at h0
  have : Subsingleton (S.TangentSpaceAt α ⧸ (⊤ : Submodule ℝ (S.TangentSpaceAt α))) :=
    Submodule.Quotient.subsingleton_iff.2 rfl
  rw [Module.finrank_zero_of_subsingleton] at h0
  omega

/-- `0 ∈ C_αC` and `T^R_αC ⊆ C_αC`. -/
theorem reducedTangent_subset_partialCone :
    (S.reducedTangent α : Set (S.TangentSpaceAt α)) ⊆ S.partialCone α :=
  fun e he => ((mem_reducedTangent_iff_lineality α e).1 he).1

end Cone

end GCT.PolyfoldConstruction

end Polyfold
