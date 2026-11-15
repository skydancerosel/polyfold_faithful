import Polyfold.Chapter15.CylinderPointFrames
import Polyfold.Chapter15.CylinderEndCanonical
import Polyfold.Chapter11.BoundaryMeasureEquivalenceDimOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2) for Fredholm index `0`, with Definition 9.3.8
(p. 427), Theorems 9.5.4, 9.5.15 for `n = 0`, `n = 1`, and Remark 6.6.19.

# The ends of a `1`-dimensional cobordism between weighted signed points

## The text, paraphrased

For index `0` the perturbed solution sets `Θᵢ = Λᵢ ∘ f` are finite sets of weighted points with
signs, and `Θ̃ = Λ̃ ∘ f̃` on `[0, 1] × X` is a `1`-dimensional compact oriented cobordism:
`∂Θ̃ = Θ₁ ⊔ −Θ₀`.  Near `(i, x)` a sheet of `Θ̃` is a curve `M̃ = {f̃ = s̃}` ending at `(i, x)`,
oriented by the generator `ν` of `ker (f̃ − s̃)'` with `dt(ν) = ±1`, the sign that of the point
`x` of `Θᵢ`; the boundary orientation of the end point (outward vector first, Definition 9.3.8)
is then the sign of `x` at `t = 1` and the opposite sign at `t = 0`.

## What is formalized

Namespace `Polyfold.MPolyfold`:
* `not_isInwardVec_of_cubeTimeComponent_neg`, `isInwardVec_of_cubeTimeComponent_neg`: a vector
  with `dt(w) < 0` points out of `[0, 1] × X` at `t = 0` and into it at `t = 1`.
* `exists_isOpen_inter_subset_singleton_of_dim_zero`: a `0`-dimensional submanifold with a tame
  induced structure is discrete.

Namespace `Polyfold.SBLocalization`:
* **`frameSign_boundaryOrient_of_generator`**: for a sheet `M̃` of dimension `1` of the cylinder
  with a boundary point `(q, y)`, `q ∈ {0, 1}`, and a positive tangent vector `w` with
  `dt(w) = s = ±1`: the sign of the boundary orientation of the point is `(−1)^{q+1} s`.
* `ArePointMatchedAt`: structures `C` of `Θ` at `x` (dimension `0`) and `C̃` of `Θ̃` at `(q, x)`
  (dimension `1`) match with sign `ε`: the boundary sheets of `C̃` are the slices of the sheets
  of `C`, with the same weights, and the signs of the boundary points are `ε` times the signs
  of the points.
* **`sheetSum_boundaryFamily_cubeFace_point`**: for matched structures with point sheets the
  boundary sheet sum of `pr^*ω` (Theorem 9.5.15, `n = 1`) is `ε` times the sheet sum of `ω`
  (Theorem 9.5.4, `n = 0`).
* **`boundaryBranchedMeasureDim1_cylEnd_of_pointMatched`** and its effective form
  `boundaryBranchedMeasureEffDim1_cylEnd_of_pointMatched`: if every point of `supp Θ` has
  matched structures with sign `ε` on the end `i`, the boundary measure of `pr^*ω` on the end
  `i` of `|supp ∂Θ̃|` is `ε · ∫_Θ̂ ω`.
* **`exists_arePointMatchedAt_of_kernelCanonical`**: for `d_X ≡ 0`, `(f, o)` oriented, `T` and
  `T̃` given by the formula of Theorem 15.4.1 for `(f, o)` and `(f̃, e ∧ o)`, every point of
  `supp Θ` has structures matched with sign `(−1)^{i+1}` on the end `i`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u v

namespace MPolyfold

section Time

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]

/-- **At `t = 0` a vector with `dt(w) < 0` points out of `[0, 1] × X`.** -/
theorem not_isInwardVec_of_cubeTimeComponent_neg {q : Fin 1 → unitInterval}
    (hq : (q 0 : ℝ) = 0) {y : X} {w : ((cubePolyfold 1).prod P).TangentSpace}
    (hw : ((cubePolyfold 1).prod P).levelVal 1 (((cubePolyfold 1).prod P).tangentProj w) =
      (q, y)) (hneg : cubeTimeComponent q w < 0) :
    ¬ ((cubePolyfold 1).prod P).IsInwardVec (q, y) w := by
  obtain ⟨c⟩ := P.nonempty_presentedChart y
  rw [cubeTimeComponent_eq q c hw, cubeTimeSign_of_eq_zero hq, one_mul] at hneg
  exact not_isInwardVec_of_coord_neg _ (cubeTimeIndex _ _ c)
    (cubePresentedChart_coord_base (Or.inl hq) c) hneg

/-- **At `t = 1` a vector of `T_{(1, y)}M̃` with `dt(w) < 0` points into `[0, 1] × X`** and is
not tangent to the boundary, in the situation of Definition 9.3.8. -/
theorem isInwardVec_of_cubeTimeComponent_neg {q : Fin 1 → unitInterval}
    (hq : (q 0 : ℝ) = 1) {y : X} {g : OrTangent ((cubePolyfold 1).prod P)}
    (hO : ((cubePolyfold 1).prod P).IsOrientedAt (q, y) g)
    (hadm : ((cubePolyfold 1).prod P).IsBoundaryAdmissible (q, y) g)
    {w : ((cubePolyfold 1).prod P).TangentSpace} (hw : w ∈ g.carrier)
    (hneg : cubeTimeComponent q w < 0) :
    ((cubePolyfold 1).prod P).IsInwardVec (q, y) w ∧
      ¬ ((cubePolyfold 1).prod P).IsReducedVec (q, y) w := by
  obtain ⟨c⟩ := P.nonempty_presentedChart y
  rw [cubeTimeComponent_eq q c (hO.1 w hw), cubeTimeSign_of_eq_one hq] at hneg
  exact isInwardVec_of_coord_pos hO hadm _ (cubeTimeIndex _ _ c)
    (cubePresentedChart_coord_base (Or.inr hq) c) hw (by linarith)

end Time

section Discrete

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **A `0`-dimensional submanifold with a tame induced structure is discrete**: every point
`x` of it has an open neighbourhood `V` in `X` meeting it only in `x` (its corner charts take
values in `ℝ⁰`). -/
theorem exists_isOpen_inter_subset_singleton_of_dim_zero {N : Set X}
    (hN : P.IsSubmanifoldOfDim N 0) (ht : P.HasTameInducedStructure N) {x : X} (hx : x ∈ N) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ N ∩ V ⊆ {x} := by
  let _ := P.paracompactSpace_subtype N
  have h := hN.hasCornerStructureOfDim_of_hasTameInducedStructure ht
  obtain ⟨κ, hκ⟩ := h.exists_cornerCoords ⟨x, hx⟩
  obtain ⟨V, hV, hVs⟩ := isOpen_induced_iff.1 κ.isOpen_s
  refine ⟨V, hV, ?_, ?_⟩
  · have h' : (⟨x, hx⟩ : N) ∈ Subtype.val ⁻¹' V := by rw [hVs]; exact hκ
    exact h'
  · rintro y ⟨hyM, hyV⟩
    have hy : (⟨y, hyM⟩ : N) ∈ κ.s := by
      rw [← hVs]; exact hyV
    have e : κ.coord ⟨y, hyM⟩ = κ.coord ⟨x, hx⟩ := Subsingleton.elim _ _
    have e' := congrArg κ.coordInv e
    rw [κ.coordInv_coord hy, κ.coordInv_coord hκ] at e'
    exact congrArg Subtype.val e'

end Discrete

end MPolyfold

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

/-! ### The sign of the boundary point of a curve of the cylinder -/

/-- **The sign of the end point of a curve of the cylinder** (Definition 9.3.8, outward vector
first).  Let `M̃` be a sheet of an oriented tame structure of dimension `1` of `[0, 1] × X`,
`(q, y)` a point of its boundary stratum, `q ∈ {0, 1}`, `ε = (−1)^{q+1}`, and `w ∈ T_{(q, y)}M̃`
a positive vector with `dt(w) = s = ±1`.  Then the boundary orientation of the point `(q, y)`
has the sign `ε · s`: `w` points out of `[0, 1] × X` iff `ε · s = 1`. -/
theorem frameSign_boundaryOrient_of_generator {Θ' : (A.cubeSEP 1).Obj → ℚ}
    {z : (A.cubeSEP 1).Obj} (C' : (A.cubeSEP 1).X.OrientedTameStructure (0 + 1) Θ' z) (j : C'.ι)
    {q : Fin 1 → unitInterval} {y : A.Obj}
    (hzB : ((q, y) : (A.cubeSEP 1).Obj) ∈ C'.boundarySheet j)
    {w : (A.cubeSEP 1).X.PObj.TangentSpace}
    (hw : w ∈ (A.cubeSEP 1).X.PObj.submanifoldTangent (C'.M j) (q, y))
    (hfr : (fun _ : Fin (0 + 1) => w) ∈ (C'.orient j).frames (q, y)) {ε s : ℝ}
    (hq : ((q 0 : ℝ) = 0 ∧ ε = -1) ∨ ((q 0 : ℝ) = 1 ∧ ε = 1)) (hs : s = 1 ∨ s = -1)
    (hτ : cylTimeComponent A q w = s) :
    EpGroupoid.frameSign (X := (A.cubeSEP 1).X)
      ((C'.boundaryOrient j).tangent ((q, y) : (A.cubeSEP 1).Obj)) = ε * s := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have hO := (C'.orient j).isOrientedAt (q, y) hzB.1
  have hadm := (C'.orient j).isBoundaryAdmissible_tangent (C'.isSubmanifoldOfDim j).1 hzB
  let a : Fin 0 → (A.cubeSEP 1).X.PObj.TangentSpace := Fin.elim0
  have hcons : (Fin.cons w a : Fin (0 + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) ∈
      (C'.orient j).frames (q, y) := by
    have e : (Fin.cons w a : Fin (0 + 1) → (A.cubeSEP 1).X.PObj.TangentSpace) = fun _ => w :=
      funext fun k => by rw [Fin.fin_one_eq_zero k]; rfl
    rw [e]
    exact hfr
  have haK : ∀ i, a i ∈ (A.cubeSEP 1).X.PObj.boundaryCarrier
      ((A.cubeSEP 1).X.PObj.submanifoldTangent (C'.M j) (q, y)) := fun i => i.elim0
  have hout : ¬ (A.cubeSEP 1).X.PObj.IsInwardVec (q, y) w →
      EpGroupoid.frameSign (X := (A.cubeSEP 1).X)
        ((C'.boundaryOrient j).tangent ((q, y) : (A.cubeSEP 1).Obj)) = 1 := fun heo => by
    have hmem : a ∈ (C'.boundaryOrient j).frames (q, y) :=
      MPolyfold.mem_boundaryOp_frames_of_outward hO hadm hw heo haK hcons
    unfold EpGroupoid.frameSign
    exact if_pos ⟨a, hmem⟩
  have hin : (A.cubeSEP 1).X.PObj.IsInwardVec (q, y) w ∧
      ¬ (A.cubeSEP 1).X.PObj.IsReducedVec (q, y) w →
      EpGroupoid.frameSign (X := (A.cubeSEP 1).X)
        ((C'.boundaryOrient j).tangent ((q, y) : (A.cubeSEP 1).Obj)) = -1 := fun h => by
    have hnot : a ∉ (C'.boundaryOrient j).frames (q, y) :=
      MPolyfold.notMem_boundaryOp_frames_of_inward hO hadm hw h.1 h.2 haK hcons
    unfold EpGroupoid.frameSign
    refine if_neg fun hne => ?_
    obtain ⟨b, hb⟩ : ((C'.boundaryOrient j).frames (q, y)).Nonempty := hne
    exact hnot (Subsingleton.elim b a ▸ hb)
  have hτ' : MPolyfold.cubeTimeComponent (P := A.X.PObj) q w = s := hτ
  rcases hq with ⟨hq, rfl⟩ | ⟨hq, rfl⟩ <;> rcases hs with rfl | rfl
  · rw [hin (MPolyfold.isInwardVec_of_cubeTimeComponent_pos hq hO hadm hw
      (by rw [hτ']; exact one_pos))]
    norm_num
  · rw [hout (MPolyfold.not_isInwardVec_of_cubeTimeComponent_neg hq hw.1
      (by rw [hτ']; norm_num))]
    norm_num
  · rw [hout (MPolyfold.not_isInwardVec_of_cubeTimeComponent_pos hq hw.1
      (by rw [hτ']; exact one_pos))]
    norm_num
  · rw [hin (MPolyfold.isInwardVec_of_cubeTimeComponent_neg hq hO hadm hw
      (by rw [hτ']; norm_num))]
    norm_num

/-! ### Matched structures with point sheets -/

/-- **Structures of `Θ` at `x` (dimension `0`) and of `Θ̃` at `(q, x)` (dimension `1`) that match
with sign `ε`** (proof of Corollary 15.4.4 for index `0`): through an injection `e` of the index
set of the nonempty boundary sheets of `C̃` into the index set of `C` that misses only empty
sheets, the boundary sheet `∂₁M̃ⱼ` is the slice `{q} × M_{e j}`, the weights agree,
`{q} × U(x) ⊆ Ũ(q, x)`, and the sign of the boundary orientation (Definition 9.3.8) of the point
`(q, y)` of `∂₁M̃ⱼ` is `ε` times the sign of the point `y` of `M_{e j}`. -/
def ArePointMatchedAt {Θ : A.Obj → ℚ} {x : A.Obj} (q : Fin 1 → unitInterval)
    (C : A.X.OrientedTameStructure 0 Θ x) {Θ' : (A.cubeSEP 1).Obj → ℚ}
    {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (C' : (A.cubeSEP 1).X.OrientedTameStructure (0 + 1) Θ' (q, x))
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ') (hCT' : C'.Represents T') (ε : ℝ) :
    Prop :=
  ∃ e : (C'.boundaryFamily hΘ' hCT').nonemptyPart.ι → C.ι,
    Injective e ∧ (∀ i, i ∉ range e → C.M i = ∅) ∧ (∀ j, C'.σ j.1 = C.σ (e j)) ∧
    (∀ j, C'.boundarySheet j.1 = (cubeFaceIncl A q).obj '' C.M (e j)) ∧
    (∀ y ∈ C.U, (q, y) ∈ C'.U) ∧
    ∀ j, ∀ y ∈ C.M (e j),
      EpGroupoid.frameSign (X := (A.cubeSEP 1).X)
          ((C'.boundaryOrient j.1).tangent ((q, y) : (A.cubeSEP 1).Obj)) =
        ε * EpGroupoid.frameSign (X := A.X) ((C.orient (e j)).tangent y)

/-- **The boundary sheet sum of a curve structure over a face of the cylinder, for point
sheets.**  Let `C` be an oriented tame structure of dimension `0` of `X` with point sheets and
`C̃` one of dimension `1` of the cylinder whose nonempty boundary sheets are, through an
injection `e` of the index sets that misses only empty sheets of `C`, the faces `ι_q(M_{e j})`,
with the weights of `C`, and whose boundary points have `ε` times the signs of the points of
`C`.  If `A' ∩ ι_q(Mᵢ) = ι_q(A₀ ∩ Mᵢ)`, the boundary sheet sum of `pr^*ω` for `C̃` over `A'` is
`ε` times the sheet sum of `ω` for `C` over `A₀`. -/
theorem sheetSum_boundaryFamily_cubeFace_point (q : Fin 1 → unitInterval) {Θ : A.Obj → ℚ}
    {x : A.Obj} (C : A.X.OrientedTameStructure 0 Θ x) {Θ' : (A.cubeSEP 1).Obj → ℚ}
    {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ} {z : (A.cubeSEP 1).Obj}
    (C' : (A.cubeSEP 1).X.OrientedTameStructure (0 + 1) Θ' z)
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ') (hCT' : C'.Represents T')
    (hS : ∀ i, C.M i ∈ EpGroupoid.pointSheets A.X)
    (e : (C'.boundaryFamily hΘ' hCT').nonemptyPart.ι → C.ι) (he : Injective e)
    (hrange : ∀ i, i ∉ range e → C.M i = ∅) (hσ : ∀ j, C'.σ j.1 = C.σ (e j))
    (hM : ∀ j, C'.boundarySheet j.1 = (cubeFaceIncl A q).obj '' C.M (e j))
    {A₀ : Set A.Obj} {A' : Set (A.cubeSEP 1).Obj}
    (hA : ∀ i, A' ∩ (cubeFaceIncl A q).obj '' C.M i = (cubeFaceIncl A q).obj '' (A₀ ∩ C.M i))
    {ε : ℝ}
    (hε : ∀ j, ∀ y ∈ C.M (e j),
      EpGroupoid.frameSign (X := (A.cubeSEP 1).X)
          ((C'.boundaryOrient j.1).tangent ((q, y) : (A.cubeSEP 1).Obj)) =
        ε * EpGroupoid.frameSign (X := A.X) ((C.orient (e j)).tangent y))
    (ω : A.baseEP.epFormsInfty 0) :
    (C'.boundaryFamily hΘ' hCT').nonemptyPart.sheetSum (A.cubeSEP 1).baseEP.zeroFormIntegration
        (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
          0 ω) A' =
      ε * C.sheetSum A.baseEP.zeroFormIntegration ω A₀ := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  unfold EpGroupoid.OrientedSheetFamily.sheetSum EpGroupoid.OrientedTameStructure.sheetSum
  rw [Finset.mul_sum]
  refine Fintype.sum_of_injective e he _ _ (fun i hi => ?_) (fun j => ?_)
  · change ε * (_ * A.baseEP.zeroFormIntegration.integ _ _ _ _) = 0
    rw [A.baseEP.zeroFormIntegration_integ_of_empty _ _ (by rw [hrange i hi, inter_empty]),
      mul_zero, mul_zero]
  · have hset : A' ∩ C'.boundarySheet j.1 = (cubeFaceIncl A q).obj '' (A₀ ∩ C.M (e j)) := by
      rw [hM j, hA]
    change (C'.σ j.1 : ℝ) * (A.cubeSEP 1).baseEP.zeroFormIntegration.integ _
        (C'.boundarySheet j.1) (C'.boundaryOrient j.1).tangent (A' ∩ C'.boundarySheet j.1) =
      ε * ((C.σ (e j) : ℝ) * A.baseEP.zeroFormIntegration.integ ω (C.M (e j))
        (C.orient (e j)).tangent (A₀ ∩ C.M (e j)))
    rw [hσ j, EP.zeroFormIntegration_integ, EP.zeroFormIntegration_integ]
    obtain ⟨p, hps, hp⟩ : ∃ p ∈ A.X.PObj.smoothSet, C.M (e j) = {p} := by
      rcases hS (e j) with h | h
      · exfalso
        obtain ⟨w, hw⟩ : (C'.boundarySheet j.1).Nonempty := j.2
        rw [hM j, h, image_empty] at hw
        exact hw
      · exact h
    have hpM : p ∈ C.M (e j) := by rw [hp]; rfl
    have hsub : (C'.boundarySheet j.1).Subsingleton := by
      rw [hM j, hp, image_singleton]
      exact subsingleton_singleton
    have hsub₀ : (C.M (e j)).Subsingleton := by rw [hp]; exact subsingleton_singleton
    by_cases hpA : p ∈ A₀
    · have h1 : ((q, p) : (A.cubeSEP 1).Obj) ∈ A' ∩ C'.boundarySheet j.1 := by
        rw [hset]
        exact ⟨p, ⟨hpA, hpM⟩, rfl⟩
      have hsm : ((q, p) : (A.cubeSEP 1).Obj) ∈ (A.cubeSEP 1).X.PObj.smoothSet :=
        prod_cube_mem_smoothSet_iff.2 hps
      rw [EpGroupoid.pointInteg_of_mem hsub
          (show ((q, p) : (A.cubeSEP 1).Obj) ∈ (A' ∩ C'.boundarySheet j.1) ∩ C'.boundarySheet j.1
            from ⟨h1, h1.2⟩),
        EpGroupoid.pointInteg_of_mem hsub₀
          (show p ∈ (A₀ ∩ C.M (e j)) ∩ C.M (e j) from ⟨⟨hpA, hpM⟩, hpM⟩), hε j p hpM,
        EP.zeroFormEval_epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP)
          (A.X.cubeProj 1) ω hsm hps]
      change (C.σ (e j) : ℝ) * (ε * _ * A.baseEP.zeroFormEval ω p) = _
      ring
    · have hE₀ : (A₀ ∩ C.M (e j)) ∩ C.M (e j) = ∅ :=
        eq_empty_of_forall_notMem fun y hy => hpA ((hsub₀ hy.2 hpM) ▸ hy.1.1)
      have hE : (A' ∩ C'.boundarySheet j.1) ∩ C'.boundarySheet j.1 = ∅ :=
        eq_empty_of_forall_notMem fun w hw => by
          have hw' := hw.1
          rw [hset] at hw'
          obtain ⟨y, hy, -⟩ := hw'
          exact hpA ((hsub₀ hy.2 hpM) ▸ hy.1)
      rw [EpGroupoid.pointInteg_of_empty hE, EpGroupoid.pointInteg_of_empty hE₀]
      ring

set_option maxHeartbeats 1600000 in
-- the statement unfolds the cylinder's ep-groupoid in several places
/-- **The local data of an end from matched structures with point sheets**: for `x ∈ supp Θ`
and structures `C` of `Θ` at `x` (point sheets) and `C̃` of `Θ̃` at `(i, x)` matched with sign
`ε`: `(i, x) ∈ supp ∂Θ̃`, the nonempty boundary sheets of `C̃` are smooth points, the end `i` of
`|supp ∂Θ̃|` over `|U(x)|` lies in `|Ũ(i, x)|`, and for every `K ⊆ |supp Θ|` the boundary sheet
sum of `pr^*ω` over the part of the end over `K` is `ε` times the sheet sum of `ω` over `K`. -/
theorem pointMatched_local {Θ : A.Obj → ℚ} {Θ' : (A.cubeSEP 1).Obj → ℚ}
    {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ') {i ε : ℝ} {q : Fin 1 → unitInterval}
    (hqi : (q 0 : ℝ) = i)
    (hover : ∀ p : cylEnd (X := A.X) Θ' i, cylEndMap p ∈ A.X.orbitSupp Θ)
    {x : A.Obj} (hx : x ∈ EpGroupoid.supp Θ) (C : A.X.OrientedTameStructure 0 Θ x)
    (C' : (A.cubeSEP 1).X.OrientedTameStructure (0 + 1) Θ' (q, x))
    (hCT' : C'.Represents T') (hS : ∀ j, C.M j ∈ EpGroupoid.pointSheets A.X)
    (hm : ArePointMatchedAt q C C' hΘ' hCT' ε) :
    ((q, x) : (A.cubeSEP 1).Obj) ∈
        EpGroupoid.supp ((A.cubeSEP 1).X.boundaryTheta Θ') ∧
      (∀ j, (C'.boundarySheet j).Nonempty →
        C'.boundarySheet j ∈ EpGroupoid.pointSheets (A.cubeSEP 1).X) ∧
      (∀ K : Set (A.X.orbitSupp Θ), Subtype.val '' K ⊆ A.X.π '' C.U →
        Subtype.val '' (Subtype.val '' (cylEndProj hover ⁻¹' K)) ⊆
          (A.cubeSEP 1).X.π '' C'.U) ∧
      ∀ (ω : A.baseEP.epFormsInfty 0) (K : Set (A.X.orbitSupp Θ)),
        (C'.boundaryFamily hΘ' hCT').nonemptyPart.sheetSum
            (A.cubeSEP 1).baseEP.zeroFormIntegration
            (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP)
              (A.X.cubeProj 1) 0 ω)
            ((A.cubeSEP 1).X.π ⁻¹'
              (Subtype.val '' (Subtype.val '' (cylEndProj hover ⁻¹' K)))) =
          ε * C.sheetSum A.baseEP.zeroFormIntegration ω (A.X.π ⁻¹' (Subtype.val '' K)) := by
  classical
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  obtain ⟨e, he, hrange, hσ, hM, hU, hε⟩ := hm
  have hsupp : ∀ j : (C'.boundaryFamily hΘ' hCT').nonemptyPart.ι, ∀ y ∈ C.M (e j),
      ((q, y) : (A.cubeSEP 1).Obj) ∈ EpGroupoid.supp ((A.cubeSEP 1).X.boundaryTheta Θ') :=
    fun j y hy => C'.boundarySheet_subset_supp_boundaryTheta j.1 (by
      rw [hM j]
      exact ⟨y, hy, rfl⟩)
  have hrg : ∀ j₀ : C.ι, ∀ y ∈ C.M j₀, ∃ j, e j = j₀ := fun j₀ y hy => by
    by_contra hne
    have := hrange j₀ (fun ⟨j, hj⟩ => hne ⟨j, hj⟩)
    rw [this] at hy
    exact hy
  refine ⟨?_, fun j hj => ?_, fun K hKN => ?_, fun ω K => ?_⟩
  · obtain ⟨j₀, hj₀⟩ := (C.toLocalBranchingStructure.mem_supp_iff C.mem_U).1 hx
    obtain ⟨j, rfl⟩ := hrg j₀ x hj₀
    exact hsupp j x hj₀
  · have h1 : C'.boundarySheet j = (cubeFaceIncl A q).obj '' C.M (e ⟨j, hj⟩) := hM ⟨j, hj⟩
    rcases hS (e ⟨j, hj⟩) with h0 | ⟨p, hps, hp⟩
    · exfalso
      obtain ⟨w, hw⟩ := hj
      rw [h1, h0, image_empty] at hw
      exact hw
    · refine Or.inr ⟨(q, p), prod_cube_mem_smoothSet_iff.2 hps, ?_⟩
      rw [h1, hp, image_singleton]
      rfl
  · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    obtain ⟨z, -, hzp⟩ := p.1.2
    obtain ⟨y, hyU, hy⟩ := hKN ⟨_, hp, rfl⟩
    have hy' : A.X.π y = cylEndMap p := hy
    rw [A.X.cylEndMap_π p z hzp] at hy'
    have ht : (z.1 0 : ℝ) = i := by
      have h2 : A.X.cylOrbitTime p.1.1 = i := p.2
      rwa [← hzp, cylOrbitTime_π] at h2
    have hz1 : z.1 = q := funext fun a => by
      have : a = 0 := Subsingleton.elim _ _
      subst this
      exact Subtype.ext (ht.trans hqi.symm)
    refine ⟨(q, y), hU y hyU, ?_⟩
    rw [← hzp]
    exact ((A.X.cubeProd_π_eq_π_iff 1 (q, y) z).2 ⟨hz1.symm, hy'⟩)
  · have hA : ∀ j₀, (A.cubeSEP 1).X.π ⁻¹'
          (Subtype.val '' (Subtype.val '' (cylEndProj hover ⁻¹' K))) ∩
          (cubeFaceIncl A q).obj '' C.M j₀ =
        (cubeFaceIncl A q).obj '' (A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M j₀) := by
      intro j₀
      ext w
      constructor
      · rintro ⟨hw, y, hy, rfl⟩
        refine ⟨y, ⟨?_, hy⟩, rfl⟩
        obtain ⟨_, ⟨p, hpK, rfl⟩, hpw⟩ := hw
        have := A.X.cylEndMap_π p (q, y) hpw.symm
        exact ⟨cylEndProj hover p, hpK, this⟩
      · rintro ⟨y, ⟨⟨s, hsK, hsy⟩, hy⟩, rfl⟩
        refine ⟨?_, y, hy, rfl⟩
        obtain ⟨j, rfl⟩ := hrg j₀ y hy
        let p : cylEnd (X := A.X) Θ' i :=
          ⟨⟨(A.X.cubeProd 1).π (q, y), (q, y), hsupp j y hy, rfl⟩, by
            change A.X.cylOrbitTime ((A.X.cubeProd 1).π (q, y)) = i
            rw [cylOrbitTime_π]
            exact hqi⟩
        have hp : cylEndProj hover p = s := Subtype.ext (by
          change cylEndMap p = s.1
          rw [A.X.cylEndMap_π p (q, y) rfl]
          exact hsy.symm)
        exact ⟨_, ⟨p, by change cylEndProj hover p ∈ K; rw [hp]; exact hsK, rfl⟩, rfl⟩
    exact sheetSum_boundaryFamily_cubeFace_point q C C' hΘ' hCT' hS e he hrange hσ hM hA hε ω

set_option maxHeartbeats 1600000 in
-- the statement unfolds the cylinder's ep-groupoid in several places
/-- **The end identity from matched structures with point sheets** (proof of Corollary 15.4.4
for index `0`, p. 703): let `Θ̂ = (Θ, T)` be compact, oriented and tame of dimension `0` on `X`
and `Θ̃` compact, oriented and tame of dimension `1` on `[0, 1] × X`, the end `i` of `|supp ∂Θ̃|`
lying over `|supp Θ|`.  If every `x ∈ supp Θ` has structures `C` of `Θ` at `x` (point sheets,
describing `T`) and `C̃` of `Θ̃` at `(i, x)` (describing `T̃`) matched with sign `ε`, then the
boundary measure of `pr^*ω` (Theorem 9.5.15 for `n = 1`) on the end `i` is `ε · ∫_Θ̂ ω`
(Definition 9.5.6 for `n = 0`), for every `0`-form `ω`. -/
theorem boundaryBranchedMeasureDim1_cylEnd_of_pointMatched {Θ : A.Obj → ℚ}
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ EpGroupoid.supp Θ, ∃ C : A.X.OrientedTameStructure 0 Θ x,
      (∀ i, C.M i ∈ EpGroupoid.pointSheets A.X) ∧ C.Represents T)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (0 + 1) Θ' x, C.Represents T')
    {i ε : ℝ} {q : Fin 1 → unitInterval} (hqi : (q 0 : ℝ) = i)
    (hover : ∀ p : cylEnd (X := A.X) Θ' i, cylEndMap p ∈ A.X.orbitSupp Θ)
    (h : ∀ x ∈ EpGroupoid.supp Θ, ∃ (C : A.X.OrientedTameStructure 0 Θ x)
        (C' : (A.cubeSEP 1).X.OrientedTameStructure (0 + 1) Θ' (q, x)) (hCT' : C'.Represents T'),
        (∀ j, C.M j ∈ EpGroupoid.pointSheets A.X) ∧ C.Represents T ∧
          ArePointMatchedAt q C C' hΘ' hCT' ε)
    (ω : A.baseEP.epFormsInfty 0) :
    (A.cubeSEP 1).baseEP.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc'
        (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
          0 ω) (cylEnd (X := A.X) Θ' i) =
      ε * EpGroupoid.branchedIntegral A.baseEP.zeroFormIntegration hΘ hcpt hT hloc ω := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have : CompactSpace (A.X.orbitSupp Θ) := isCompact_iff_compactSpace.1 hcpt
  change _ = ε * (EpGroupoid.branchedMeasure A.baseEP.zeroFormIntegration hΘ hcpt hT hloc ω)
    univ
  refine signedMeasure_closed_eq_of_local (borel_le_borelNullSigma _)
    ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (0 + 1) Θ') _ _
    (A.X.isClosed_cylEnd Θ' i) (cylEndProj hover) (continuous_cylEndProj hover) ε fun s => ?_
  obtain ⟨x, hx, hxs⟩ := s.2
  obtain ⟨C, C', hCT', hS, hCT, hm⟩ := h x hx
  obtain ⟨hz, hS', hKU, hsum⟩ := pointMatched_local hΘ' hqi hover hx C C' hCT' hS hm
  have hNo : IsOpen (A.X.π '' C.U) := A.X.proposition_7_1_8 _ C.isOpen_U
  refine ⟨Subtype.val ⁻¹' (A.X.π '' C.U), hNo.preimage continuous_subtype_val, by
    change s.1 ∈ A.X.π '' C.U
    rw [← hxs]
    exact ⟨x, C.mem_U, rfl⟩, fun K hK hKN => ?_⟩
  have hKN' : Subtype.val '' K ⊆ A.X.π '' C.U := image_subset_iff.2 hKN
  have hm' := measurableSet_image_preimage_borel (A.X.isClosed_cylEnd Θ' i)
    (continuous_cylEndProj hover) hK
  have e1 := (A.cubeSEP 1).baseEP.boundaryBranchedMeasureDim1_spec hΘ' hcpt' hT' hloc'
    (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1) 0 ω)
    (q, x) C' hCT' hz hS' (Subtype.val '' (cylEndProj hover ⁻¹' K))
    ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (0 + 1) Θ' _ hm') (hKU K hKN')
  have e2 : EpGroupoid.branchedMeasure A.baseEP.zeroFormIntegration hΘ hcpt hT hloc ω K =
      C.localMeasure A.baseEP.zeroFormIntegration ω (Subtype.val '' K) :=
    EpGroupoid.branchedMeasure_apply _ hΘ hcpt hT hloc ω C hS hCT
      (borel_le_borelNullSigma _ _ hK) hKN'
  have hcard : Nat.card ((A.cubeSEP 1).X.Isotropy ((q, x) : (A.cubeSEP 1).Obj)) =
      Nat.card (A.X.Isotropy x) := A.X.card_isotropy_cubeProd 1 (q, x)
  have e3 : (Nat.card ((A.cubeSEP 1).X.Isotropy ((q, x) : (A.cubeSEP 1).Obj)) : ℝ)⁻¹ *
      (C'.boundaryFamily hΘ' hCT').nonemptyPart.sheetSum (A.cubeSEP 1).baseEP.zeroFormIntegration
        (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
          0 ω)
        ((A.cubeSEP 1).X.π ⁻¹' (Subtype.val '' (Subtype.val '' (cylEndProj hover ⁻¹' K)))) =
      ε * C.localMeasure A.baseEP.zeroFormIntegration ω (Subtype.val '' K) := by
    rw [hsum ω K, hcard]
    change _ = ε * ((Nat.card (A.X.Isotropy x) : ℝ)⁻¹ * _)
    ring
  rw [e2]
  exact e1.trans e3

set_option maxHeartbeats 1600000 in
-- the statement unfolds the cylinder's ep-groupoid in several places
/-- **The effective end identity from matched structures with point sheets**: the effective form
of `boundaryBranchedMeasureDim1_cylEnd_of_pointMatched` (Theorems 9.5.5, 9.5.16 for `n = 0`,
`n = 1`, with `♯G^eff_{(i, x)} = ♯G^eff_x`), for `X` and `[0, 1] × X` with the local unique
continuation property. -/
theorem boundaryBranchedMeasureEffDim1_cylEnd_of_pointMatched (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) {Θ : A.Obj → ℚ}
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ EpGroupoid.supp Θ, ∃ C : A.X.OrientedTameStructure 0 Θ x,
      (∀ i, C.M i ∈ EpGroupoid.pointSheets A.X) ∧ C.Represents T ∧ C.rep.HasLUC)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (0 + 1) Θ' x, C.Represents T' ∧ C.rep.HasLUC)
    {i ε : ℝ} {q : Fin 1 → unitInterval} (hqi : (q 0 : ℝ) = i)
    (hover : ∀ p : cylEnd (X := A.X) Θ' i, cylEndMap p ∈ A.X.orbitSupp Θ)
    (h : ∀ x ∈ EpGroupoid.supp Θ, ∃ (C : A.X.OrientedTameStructure 0 Θ x)
        (C' : (A.cubeSEP 1).X.OrientedTameStructure (0 + 1) Θ' (q, x)) (hCT' : C'.Represents T'),
        (∀ j, C.M j ∈ EpGroupoid.pointSheets A.X) ∧ C.Represents T ∧
          ArePointMatchedAt q C C' hΘ' hCT' ε)
    (ω : A.baseEP.epFormsInfty 0) :
    (A.cubeSEP 1).baseEP.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT' hloc'
        (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
          0 ω) (cylEnd (X := A.X) Θ' i) =
      ε * EpGroupoid.branchedIntegralEff A.baseEP.zeroFormIntegration hΘ hcpt hT hloc ω := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have : CompactSpace (A.X.orbitSupp Θ) := isCompact_iff_compactSpace.1 hcpt
  change _ = ε * (EpGroupoid.branchedMeasureEff A.baseEP.zeroFormIntegration hΘ hcpt hT hloc ω)
    univ
  refine signedMeasure_closed_eq_of_local (borel_le_borelNullSigma _)
    ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (0 + 1) Θ') _ _
    (A.X.isClosed_cylEnd Θ' i) (cylEndProj hover) (continuous_cylEndProj hover) ε fun s => ?_
  obtain ⟨x, hx, hxs⟩ := s.2
  obtain ⟨C, C', hCT', hS, hCT, hm⟩ := h x hx
  obtain ⟨hz, hS', hKU, hsum⟩ := pointMatched_local hΘ' hqi hover hx C C' hCT' hS hm
  have hNo : IsOpen (A.X.π '' C.U) := A.X.proposition_7_1_8 _ C.isOpen_U
  refine ⟨Subtype.val ⁻¹' (A.X.π '' C.U), hNo.preimage continuous_subtype_val, by
    change s.1 ∈ A.X.π '' C.U
    rw [← hxs]
    exact ⟨x, C.mem_U, rfl⟩, fun K hK hKN => ?_⟩
  have hKN' : Subtype.val '' K ⊆ A.X.π '' C.U := image_subset_iff.2 hKN
  have hm' := measurableSet_image_preimage_borel (A.X.isClosed_cylEnd Θ' i)
    (continuous_cylEndProj hover) hK
  have e1 := (A.cubeSEP 1).baseEP.boundaryBranchedMeasureEffDim1_spec hΘ' hcpt' hT' hloc'
    (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1) 0 ω)
    (q, x) C' hCT' hz hS' ((A.cubeSEP 1).X.isLUC_iff_forall_naturalRep.1 hLUCC _ C'.rep)
    (Subtype.val '' (cylEndProj hover ⁻¹' K))
    ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (0 + 1) Θ' _ hm') (hKU K hKN')
  have e2 : EpGroupoid.branchedMeasureEff A.baseEP.zeroFormIntegration hΘ hcpt hT hloc ω K =
      C.localMeasureEff A.baseEP.zeroFormIntegration ω (Subtype.val '' K) :=
    EpGroupoid.branchedMeasureEff_apply _ hΘ hcpt hT hloc ω C hS hCT
      (A.X.isLUC_iff_forall_naturalRep.1 hLUC x C.rep) (borel_le_borelNullSigma _ _ hK) hKN'
  have hcard : Nat.card ((A.cubeSEP 1).X.EffIsotropy ((q, x) : (A.cubeSEP 1).Obj)) =
      Nat.card (A.X.EffIsotropy x) := A.X.card_effIsotropy_cubeProd 1 (q, x)
  have e3 : (Nat.card ((A.cubeSEP 1).X.EffIsotropy ((q, x) : (A.cubeSEP 1).Obj)) : ℝ)⁻¹ *
      (C'.boundaryFamily hΘ' hCT').nonemptyPart.sheetSum (A.cubeSEP 1).baseEP.zeroFormIntegration
        (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
          0 ω)
        ((A.cubeSEP 1).X.π ⁻¹' (Subtype.val '' (Subtype.val '' (cylEndProj hover ⁻¹' K)))) =
      ε * C.localMeasureEff A.baseEP.zeroFormIntegration ω (Subtype.val '' K) := by
    rw [hsum ω K, hcard]
    change _ = ε * ((Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹ * _)
    ring
  rw [e2]
  exact e1.trans e3

/-! ### Matched structures from the canonical orientations -/

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
/-- **Matched structures with point sheets at the points of `supp Θᵢ`, for the canonical
orientations** (proof of Corollary 15.4.4 for Fredholm index `0`, p. 703; Remark 6.6.19).  Let
`d_X ≡ 0`, `X` with sc-smooth bump functions, `f` sc-Fredholm with tame germ data, `Λ` an
sc⁺-multisection such that `Θ = Λ ∘ f` has an orientation `T` described by oriented tame
structures of dimension `0`, `Λ̃` an sc⁺-multisection on `[0, 1] × X` with `Λ̃ = Λⁱ` over `t = i`,
`Λ̃ = Λ` over the end `i ∈ {0, 1}`, the face condition of Theorem 15.3.9 for the glued data, and
`ε = (−1)^{i+1}`.  If `T` is given by the formula of Theorem 15.4.1 for `(f, o)` and `T̃` by that
formula for `(f̃, e ∧ o)`, in every local structure described by kernels, then every
`x ∈ supp Θ` has oriented tame structures `C` of `Θ` at `x`, with point sheets and describing
`T`, and `C̃` of `Θ̃` at `(i, x)` of dimension `1` describing `T̃`, matched with sign `ε`: the
curve `M̃ⱼ` through `(i, x)` is oriented by a vector `w` with `dt(w)` the sign of the point `x`
(`exists_signed_generator_cubeOrientation`), and `w` points out of `[0, 1] × X` iff
`ε · dt(w) = 1` (`frameSign_boundaryOrient_of_generator`). -/
theorem exists_arePointMatchedAt_of_kernelCanonical (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hbump : A.X.PObj.AdmitsBumpFunctions) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}
    (hloc : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      ∃ C : A.X.OrientedTameStructure 0 (fun z => (Λ (f z) : ℚ)) x, C.Represents T)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁))
    {i : unitInterval} {ε : ℝ} (hi : ((i : ℝ) = 0 ∧ ε = -1) ∨ ((i : ℝ) = 1 ∧ ε = 1))
    (hΛi : ∀ w, ((cubeVal w).1.1 0 : ℝ) = i → Λ' w = Λ (cubeVal w).2)
    {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
      (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)))
    {hsec : A.B.HasScPlusSectionsThrough}
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy}
    {hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough}
    (hP : IsKernelCanonical Λ hf.2 hsec o T)
    (hT' : IsKernelCanonical Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2
      hsec' (cubeOrientation hf hft hsec o) T') :
    ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      ∃ (C : A.X.OrientedTameStructure 0 (fun z => (Λ (f z) : ℚ)) x)
        (C' : (A.cubeSEP 1).X.OrientedTameStructure (0 + 1)
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ((fun _ => i), x))
        (hCT' : C'.Represents T'),
        (∀ j, C.M j ∈ EpGroupoid.pointSheets A.X) ∧ C.Represents T ∧
          ArePointMatchedAt (fun _ => i) C C' hΘ' hCT' ε := by
  classical
  intro x hx
  have hpos : 0 < Λ (f x) := by
    have h : (0 : ℚ) < (Λ (f x) : ℚ) := hx
    exact_mod_cast h
  have hi' : (i : ℝ) = 0 ∨ (i : ℝ) = 1 := hi.imp (fun h => h.1) (fun h => h.1)
  -- the class of sheets: in dimension `0`, the smooth points
  let S : ℕ → Set (Set A.Obj) := fun d => {N | d = 0 → N ∈ EpGroupoid.pointSheets A.X}
  have hS₁ : ∀ d N, A.X.PObj.IsSubmanifoldOfDim N d → x ∈ N →
      ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ N ∩ V ∈ S d := fun d N hN hxN => by
    by_cases hd0 : d = 0
    · subst hd0
      obtain ⟨V, hV, hxV, hNV⟩ := MPolyfold.exists_isOpen_inter_subset_singleton_of_dim_zero hN
        (MPolyfold.hasTameInducedStructure_of_degIndex_eq_zero hN.1 fun a _ => hd a) hxN
      exact ⟨V, hV, hxV, fun _ => Or.inr ⟨x, hN.1.subset_smoothSet hxN,
        Subset.antisymm hNV (singleton_subset_iff.2 ⟨hxN, hxV⟩)⟩⟩
    · exact ⟨univ, isOpen_univ, mem_univ _, fun h => absurd h hd0⟩
  have hS₂ : ∀ d N V, N ∈ S d → IsOpen V → N ∩ V ∈ S d := fun d N V hN _ hd0 => by
    rcases hN hd0 with rfl | ⟨p, hp, rfl⟩
    · exact Or.inl (empty_inter V)
    · by_cases hpV : p ∈ V
      · exact Or.inr ⟨p, hp, inter_eq_left.2 (singleton_subset_iff.2 hpV)⟩
      · exact Or.inl (singleton_inter_eq_empty.2 hpV)
  obtain ⟨K', K, e, hσ, hU, -, hM, hstr, hKd, hKs, hcls⟩ :=
    exists_matched_kernel_branching_of_class hd hf hft hΛ' h0 h1 honto hi' hΛi hpos S hS₁ hS₂
  obtain ⟨C₀, hC₀⟩ := hloc x hx
  have hn : ∀ j, K.dim j = 0 := fun j => by
    have hxs : x ∈ A.X.PObj.smoothSet := K.smooth j x (K.mem_M j)
    exact K.dim_eq_of_represents hf.2 hsec o (hP.2 x K x K.mem_U hxs) C₀ hC₀ hxs j
  have hn' : ∀ j, K'.dim j = 0 + 1 := fun j => by rw [hKd j, hn]
  have hc := hP.1 x K
  have hc' := hT'.1 _ K'
  have hCT' : (K'.toOrientedTame hc' hn').Represents T' :=
    K'.represents_toOrientedTame hc' hn' (hT'.2 _ K')
  have hCT : (K.toOrientedTame hc hn).Represents T :=
    K.represents_toOrientedTame hc hn (hP.2 x K)
  have hSh : ∀ j, (K.toOrientedTame hc hn).M j ∈ EpGroupoid.pointSheets A.X := fun j => by
    obtain ⟨j', rfl⟩ := e.surjective j
    exact hcls j' (hn (e j'))
  have hbs : ∀ j, (K'.toOrientedTame hc' hn').boundarySheet j =
      (cubeFaceIncl A (fun _ => i)).obj '' K.M (e j) := hstr
  refine ⟨K.toOrientedTame hc hn, K'.toOrientedTame hc' hn', hCT', hSh, hCT,
    fun j => e j.1, fun a b h => Subtype.ext (e.injective h), fun i' hi' => ?_,
    fun j => hσ j.1, fun j => hbs j.1, fun y hy => (hU y).1 hy, fun j y hy => ?_⟩
  · refine absurd ⟨⟨e.symm i', ?_⟩, e.apply_symm_apply i'⟩ hi'
    exact Eq.mpr (congrArg Set.Nonempty (hbs (e.symm i'))) ⟨_, x, K.mem_M _, rfl⟩
  · have hyK : y ∈ K.M (e j.1) := hy
    have hy' : (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈ K'.M j.1 := by
      have h := hyK
      rw [hM j.1] at h
      exact h
    obtain ⟨s, w, hsF, hwT, hτ, hfr⟩ := exists_signed_generator_cubeOrientation hbump hf hft
      hsec hsec' o (fun _ => i) K K' (e j.1) j.1 (hn _) (hn' _) (hKs j.1) hyK hy'
    have hzB : (((fun _ => i), y) : (A.cubeSEP 1).Obj) ∈
        (K'.toOrientedTame hc' hn').boundarySheet j.1 :=
      (Set.ext_iff.1 (hbs j.1) _).2 ⟨y, hyK, rfl⟩
    have hfr' : (fun _ : Fin (0 + 1) => w) ∈
        ((K'.toOrientedTame hc' hn').orient j.1).frames ((fun _ => i), y) :=
      (mem_frames_cast_iff (A := A.cubeSEP 1) (hn' j.1) (K'.orient hc' j.1) ((fun _ => i), y)
        _).2 hfr
    have hfs : EpGroupoid.frameSign (X := A.X)
        (((K.toOrientedTame hc hn).orient (e j.1)).tangent y) = s := by
      change EpGroupoid.frameSign (X := A.X) ((hn (e j.1) ▸ K.orient hc (e j.1)).tangent y) = s
      rw [KernelBranching.tangent_cast_aux]
      unfold EpGroupoid.frameSign
      rcases hsF with ⟨rfl, hne⟩ | ⟨rfl, hne⟩
      · exact if_pos hne
      · exact if_neg hne
    rw [hfs]
    exact frameSign_boundaryOrient_of_generator (K'.toOrientedTame hc' hn') j.1 hzB hwT hfr' hi
      (hsF.imp And.left And.left) hτ

end SBLocalization

end Polyfold
