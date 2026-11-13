import Polyfold.Chapter11.BoundaryMeasureEquivalence
import Polyfold.Chapter11.FormEvalPullbackEquivalence
import Polyfold.Chapter9.StokesDimOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4, **Theorems 11.4.4 and 11.4.5 for `n = 1`** (p. 545, new in the 2021
edition), gap G.131.  Numbers and pages are the 2021 text's.

# The boundary measures of a `1`-dimensional `Θ̂` along an equivalence

For `n = 1` the boundary measures of Theorems 9.5.15/9.5.16 are those of
`EP.boundaryBranchedMeasureDim1`, `EP.boundaryBranchedMeasureEffDim1` (`StokesDimOne`),
built on the integral of `0`-forms over oriented points (`EP.zeroFormIntegration`).  H4's
`measure_pull_core_bd` is stated for E4's integration of `m`-forms, `m ≥ 1`; here is its version
for `m = 0`.

* `EP.zeroFormEval_epFormsInftyPullback`: `(Φ^*ω')(p) = ω'(Φ(p))` for a `0`-form.
* `EpFunctor.TransportChart.zeroFormEval_pull_Q`: `(Φ^*ω')(u) = ω'(Q(u))` on a transport chart.
* `OrientedTameStructure.boundarySheetSum_move_dim1`: (11.12) = (11.13) for oriented boundary
  points.
* **`EpFunctor.measure_pull_core_bd_dim1`**: the gluing argument for `n = 1`.
* **`theorem_11_4_4_pull_equiv_dim1`**, **`theorem_11_4_4_push_equiv_dim1`**,
  **`theorem_11_4_5_pull_equiv_dim1`**, **`theorem_11_4_5_push_equiv_dim1`**: Theorems 11.4.4 and
  11.4.5 for an equivalence between ep-groupoids of EPs, `n = 1`, with only the text's hypotheses
  (an oriented tame structure describing `T̂` at every point; for 11.4.5 the ep-groupoids have
  the local unique continuation property).
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

/-! ### `0`-forms along a functor -/

namespace EP

variable {A B : EP.{u}}

/-- `Bⁱ`'s base point of `Fⁱ(z)` is `F` of the base point of `z`. -/
theorem levelBase_liftFunctor (F : EpFunctor A.X B.X) :
    ∀ (i : ℕ) (z : (A.lift i).Obj),
      B.levelBase i ((liftFunctor F i).obj z) = F.obj (A.levelBase i z)
  | 0, _ => rfl
  | i + 1, z => levelBase_liftFunctor F i ((A.lift i).X.PObj.levelVal 1 z)

/-- **The pull-back of a `0`-form is the composition**: `(F^*ω')(p) = ω'(F(p))` at the smooth
points `p` with `F(p)` smooth. -/
theorem zeroFormEval_epFormsInftyPullback (F : EpFunctor A.X B.X) (b : B.epFormsInfty 0)
    {p : A.Obj} (hp : p ∈ A.X.PObj.smoothSet) (hFp : F.obj p ∈ B.X.PObj.smoothSet) :
    A.zeroFormEval (epFormsInftyPullback F 0 b) p = B.zeroFormEval b (F.obj p) := by
  obtain ⟨i, ω, rfl⟩ := B.exists_epFormsInftyOf_eq 0 b
  rw [epFormsInftyPullback_of, A.zeroFormEval_of, B.zeroFormEval_of,
    A.zeroLevelEval_eq i _ hp (fun j => Fin.elim0 j),
    B.zeroLevelEval_eq i ω hFp (fun j => Fin.elim0 j), coe_epFormsPullback,
    MPolyfold.formPullback_apply]
  have h0 : ∀ (Y Y' : (B.lift i).X.PObj.Level 1) (h : Y = Y')
      (a : Fin 0 → (B.lift i).X.PObj.tangentFiber Y)
      (a' : Fin 0 → (B.lift i).X.PObj.tangentFiber Y'), ω.1 Y a = ω.1 Y' a' := by
    intro Y Y' h a a'; subst h; exact congrArg _ (funext fun j => j.elim0)
  refine h0 _ _ (MPolyfold.level_ext ?_) _ _
  refine B.levelBase_injective i ?_
  rw [MPolyfold.levelVal_levelMk]
  change B.levelBase i ((liftFunctor F i).obj _) = _
  rw [levelBase_liftFunctor, MPolyfold.levelVal_levelMk, (A.liftPt i p hp).2.2,
    (B.liftPt i (F.obj p) hFp).2.2]

end EP

namespace EpFunctor

namespace TransportChart

variable {A B : EP.{u}} {Φ : EpFunctor A.X B.X}

/-- **On a transport chart, `(Φ^*ω')(u) = ω'(Q(u))`** for a `0`-form `ω'` (`Q(u)` and `Φ(u)` are
joined by the morphism `ψ_u`, and `0`-forms are constant on orbits). -/
theorem zeroFormEval_pull_Q {x : A.Obj} {y : B.Obj} (hΦ : Φ.IsEquivalence)
    (Tc : Φ.TransportChart x y) (ω' : B.epFormsInfty 0) {u : A.Obj} (hu : u ∈ Tc.W) :
    A.zeroFormEval (EP.epFormsInftyPullback Φ 0 ω') u = B.zeroFormEval ω' (Tc.Q u) := by
  by_cases hs : u ∈ A.X.PObj.smoothSet
  · have hFs : Φ.obj u ∈ B.X.PObj.smoothSet := (hΦ.isLocalScDiffeo_obj.mem_smoothSet_iff u).2 hs
    rw [EP.zeroFormEval_epFormsInftyPullback Φ ω' hs hFs, ← Tc.src_ψ u hu, ← Tc.tgt_ψ u hu,
      B.zeroFormEval_src_eq_tgt]
  · have hQs : Tc.Q u ∉ B.X.PObj.smoothSet := fun h =>
      hs ((Tc.mem_smoothSet_iff hΦ.isLocalScDiffeo_obj hu).1 h)
    rw [A.zeroFormEval_of_not_mem _ hs, B.zeroFormEval_of_not_mem _ hQs]

end TransportChart

end EpFunctor

/-! ### Moving oriented boundary points -/

namespace EpGroupoid

namespace OrientedTameStructure

open MPolyfold

variable {S T : EP.{u}} {Θ : S.Obj → ℚ} {Θ' : T.Obj → ℚ} {x : S.Obj}
  (C : S.X.OrientedTameStructure (0 + 1) Θ x)
  {f : S.Obj → T.Obj} {g : T.Obj → S.Obj} {W : Set S.Obj} {W' : Set T.Obj}
  {TS : S.Obj → S.X.PObj.OrTangent →₀ ℚ} {TT : T.Obj → T.X.PObj.OrTangent →₀ ℚ}

open scoped Classical in
/-- **(11.12) = (11.13) for oriented boundary points** (`n = 1`): for a structure `C` with
boundary sheets of at most one point and its moved structure,
`∑_{∂₁f(Mᵢ) ≠ ∅} σᵢ ∫_{B ∩ ∂₁f(Mᵢ)} ω_T = ∑_{∂₁Mᵢ ≠ ∅} σᵢ ∫_{A ∩ ∂₁Mᵢ} ω_S` whenever `B` meets
`f(∂₁Mᵢ)` in `f(A ∩ ∂₁Mᵢ)` and `ω_T ∘ f = ω_S` on `W`. -/
theorem boundarySheetSum_move_dim1 (hf : S.X.PObj.IsScDiffeoOn T.X.PObj f g W W')
    (hUW : C.U ⊆ W) {y : T.Obj} (hxy : f x = y) (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u)
    (R' : T.X.NaturalRep y) (hR' : R'.U = f '' C.U) (hP : T.X.HasPropernessProperty (f '' C.U))
    (hΘX : S.X.IsBranchedEpSubgroupoid Θ) (hCT : C.Represents TS)
    (hΘY : T.X.IsBranchedEpSubgroupoid Θ')
    (hCT' : (C.move hf hUW hxy hΘ R' hR' hP).Represents TT)
    (hs : ∀ i, (C.boundarySheet i).Subsingleton)
    {ωS : S.epFormsInfty 0} {ωT : T.epFormsInfty 0}
    (hω : ∀ u ∈ W, T.zeroFormEval ωT (f u) = S.zeroFormEval ωS u)
    {A : Set S.Obj} {B : Set T.Obj}
    (hB : ∀ i, B ∩ f '' C.boundarySheet i = f '' (A ∩ C.boundarySheet i)) :
    ((C.move hf hUW hxy hΘ R' hR' hP).boundaryFamily hΘY hCT').nonemptyPart.sheetSum
        T.zeroFormIntegration ωT B =
      (C.boundaryFamily hΘX hCT).nonemptyPart.sheetSum S.zeroFormIntegration ωS A := by
  rw [OrientedSheetFamily.sheetSum_nonemptyPart, OrientedSheetFamily.sheetSum_nonemptyPart]
  refine Finset.sum_congr rfl fun i _ => ?_
  set C' := C.move hf hUW hxy hΘ R' hR' hP
  have hbs : C'.boundarySheet i = f '' C.boundarySheet i :=
    C.boundarySheet_move hf hUW hxy hΘ R' hR' hP i
  change (if (C'.boundarySheet i).Nonempty then (C'.σ i : ℝ) *
      T.zeroFormIntegration.integ ωT (C'.boundarySheet i) (C'.boundaryOrient i).tangent
        (B ∩ C'.boundarySheet i) else 0) =
    if (C.boundarySheet i).Nonempty then (C.σ i : ℝ) *
      S.zeroFormIntegration.integ ωS (C.boundarySheet i) (C.boundaryOrient i).tangent
        (A ∩ C.boundarySheet i) else 0
  by_cases hne : (C.boundarySheet i).Nonempty
  · have hne' : (C'.boundarySheet i).Nonempty := by rw [hbs]; exact hne.image f
    rw [if_pos hne, if_pos hne']
    congr 1
    obtain ⟨p, hp⟩ := hne
    have hs' : (C'.boundarySheet i).Subsingleton := by rw [hbs]; exact (hs i).image f
    have hfp : f p ∈ C'.boundarySheet i := by rw [hbs]; exact mem_image_of_mem f hp
    rw [EP.zeroFormIntegration_integ, EP.zeroFormIntegration_integ]
    by_cases hpA : p ∈ A
    · have hfB : f p ∈ B := by
        have : f p ∈ B ∩ f '' C.boundarySheet i := by
          rw [hB i]; exact mem_image_of_mem f ⟨hpA, hp⟩
        exact this.1
      rw [pointInteg_of_mem (hs i) (show p ∈ (A ∩ C.boundarySheet i) ∩ C.boundarySheet i from
          ⟨⟨hpA, hp⟩, hp⟩),
        pointInteg_of_mem hs' (show f p ∈ (B ∩ C'.boundarySheet i) ∩ C'.boundarySheet i from
          ⟨⟨hfB, hfp⟩, hfp⟩),
        hω p (C.boundarySheet_subset_W hUW i hp),
        C.boundaryOrient_move_tangent hf hUW hxy hΘ R' hR' hP i hp]
      congr 1
      unfold frameSign
      have hiff : (((C.boundaryOrient i).tangent p).map
          (tangentMapOn hf.isScSmoothOn)).frames.Nonempty ↔
          ((C.boundaryOrient i).tangent p).frames.Nonempty := by
        change ((fun v => tangentMapOn hf.isScSmoothOn ∘ v) ''
          ((C.boundaryOrient i).tangent p).frames).Nonempty ↔ _
        exact image_nonempty
      by_cases h : ((C.boundaryOrient i).tangent p).frames.Nonempty
      · rw [if_pos h, if_pos (hiff.2 h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]
    · rw [pointInteg_of_empty (eq_empty_of_forall_notMem fun q hq => hpA ((hs i hq.2 hp) ▸ hq.1.1)),
        pointInteg_of_empty (eq_empty_of_forall_notMem fun z hz => ?_)]
      have hz' : z ∈ B ∩ f '' C.boundarySheet i := ⟨hz.1.1, hbs ▸ hz.2⟩
      rw [hB i] at hz'
      obtain ⟨q, hq, -⟩ := hz'
      exact hpA ((hs i hq.2 hp) ▸ hq.1)
  · have hne' : ¬ (C'.boundarySheet i).Nonempty := by
      rw [hbs]; exact fun h => hne (image_nonempty.1 h)
    rw [if_neg hne, if_neg hne']

end OrientedTameStructure

end EpGroupoid

/-! ### The local formulas of the `n = 1` boundary measures -/

namespace EP

open EpGroupoid

variable (A : EP.{u}) {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- The local formula of `boundaryBranchedMeasureDim1` (Theorem 9.5.15, `n = 1`). -/
theorem boundaryBranchedMeasureDim1_spec (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty 0) (x : A.Obj) (C : A.X.OrientedTameStructure (0 + 1) Θ x)
    (hCT : C.Represents T) (hx : x ∈ supp (A.X.boundaryTheta Θ))
    (hS : ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ pointSheets A.X)
    (K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)))
    (hK : MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K)
    (hKU : Subtype.val '' K ⊆ A.X.π '' C.U) :
    A.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc ω K = (Nat.card (A.X.Isotropy x) : ℝ)⁻¹ *
      (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum A.zeroFormIntegration ω
        (A.X.π ⁻¹' (Subtype.val '' K)) :=
  (A.theorem_9_5_15_dim1 hΘ hcpt hT hloc).exists.choose_spec ω x C hCT hx hS K hK hKU

/-- The local formula of `boundaryBranchedMeasureEffDim1` (Theorem 9.5.16, `n = 1`). -/
theorem boundaryBranchedMeasureEffDim1_spec (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x,
      C.Represents T ∧ C.rep.HasLUC)
    (ω : A.epFormsInfty 0) (x : A.Obj) (C : A.X.OrientedTameStructure (0 + 1) Θ x)
    (hCT : C.Represents T) (hx : x ∈ supp (A.X.boundaryTheta Θ))
    (hS : ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ pointSheets A.X)
    (hL : C.rep.HasLUC) (K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)))
    (hK : MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K)
    (hKU : Subtype.val '' K ⊆ A.X.π '' C.U) :
    A.boundaryBranchedMeasureEffDim1 hΘ hcpt hT hloc ω K =
      (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹ *
        (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum A.zeroFormIntegration ω
          (A.X.π ⁻¹' (Subtype.val '' K)) :=
  (A.theorem_9_5_16_dim1 hΘ hcpt hT hloc).exists.choose_spec ω x C hCT hx hS hL K hK hKU

end EP

/-! ### The gluing for `n = 1` -/

namespace EpFunctor

open EpGroupoid OrientedTameStructure MPolyfold

variable {A B : EP.{u}} {Φ : EpFunctor A.X B.X}
  {Θ' : B.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} {T' : B.Obj → B.X.PObj.OrTangent →₀ ℚ}

/-- **The pulled-back structures for the boundary, `n = 1`**: H4's `IsBPulled` with boundary
sheets of at most one point in place of E4's class `msheets`. -/
def IsBPulledDim1 (Φ : EpFunctor A.X B.X) (hΘ' : B.X.IsFunctorial Θ')
    (T' : B.Obj → B.X.PObj.OrTangent →₀ ℚ) {x : A.Obj}
    (C : A.X.OrientedTameStructure (0 + 1) (Φ.pullbackTheta Θ') x) : Prop :=
  ∃ (y : B.Obj) (Tc : Φ.TransportChart x y) (D : B.X.OrientedTameStructure (0 + 1) Θ' y)
    (_ : x ∈ supp (A.X.boundaryTheta (Φ.pullbackTheta Θ')))
    (_ : y ∈ supp (B.X.boundaryTheta Θ')) (_ : D.Represents T')
    (_ : ∀ i, (D.boundarySheet i).Subsingleton)
    (R : A.X.NaturalRep x) (R' : B.X.NaturalRep y)
    (h1 : R'.U ⊆ D.U) (h2 : R.U ⊆ Tc.W) (h3 : R'.U = Tc.Q '' R.U)
    (h4 : A.X.HasPropernessProperty R.U),
    C = pullStructure Tc (Tc.pullbackTheta_Q hΘ') D R R' h1 h2 h3 h4

/-- Every point of `supp ∂(Φ^*Θ')` carries a pulled-back structure (`n = 1`). -/
theorem exists_isBPulledDim1 (hΦ : Φ.IsEquivalence) (hΘ' : B.X.IsBranchedEpSubgroupoid Θ')
    (hcov' : ∀ y ∈ supp (B.X.boundaryTheta Θ'), ∃ D : B.X.OrientedTameStructure (0 + 1) Θ' y,
      D.Represents T' ∧ ∀ i, (D.boundarySheet i).Subsingleton)
    {x : A.Obj} (hx : x ∈ supp (A.X.boundaryTheta (Φ.pullbackTheta Θ'))) :
    ∃ C : A.X.OrientedTameStructure (0 + 1) (Φ.pullbackTheta Θ') x,
      IsBPulledDim1 Φ hΘ'.isFunctorial T' C := by
  obtain ⟨Tc⟩ := TransportChart.nonempty hΦ x
  have hx' := (mem_supp_boundaryTheta_pull hΦ hΘ').1 hx
  obtain ⟨D, hDT, hDS⟩ := hcov' _ hx'
  obtain ⟨R, R', h1, h2, h3, h4⟩ := exists_pullData hΦ Tc D
  exact ⟨_, _, Tc, D, hx, hx', hDT, hDS, R, R', h1, h2, h3, h4, rfl⟩

theorem IsBPulledDim1.subsingleton {hΘ' : B.X.IsFunctorial Θ'} {x : A.Obj}
    {C : A.X.OrientedTameStructure (0 + 1) (Φ.pullbackTheta Θ') x}
    (hC : IsBPulledDim1 Φ hΘ' T' C) : ∀ i, (C.boundarySheet i).Subsingleton := by
  obtain ⟨y, Tc, D, -, -, -, hDS, R, R', h1, h2, h3, h4, rfl⟩ := hC
  unfold pullStructure
  intro i
  erw [boundarySheet_move]
  exact ((hDS i).anti ((D.boundarySheet_restrictRep R' h1 i).subset.trans
    inter_subset_left)).image _

theorem IsBPulledDim1.represents (hΦ : Φ.IsEquivalence) {hΘ' : B.X.IsFunctorial Θ'} {x : A.Obj}
    (hT : A.X.IsGrHatSection T) (hTT : Φ.IsTransported T T')
    {C : A.X.OrientedTameStructure (0 + 1) (Φ.pullbackTheta Θ') x}
    (hC : IsBPulledDim1 Φ hΘ' T' C) : C.Represents T := by
  obtain ⟨y, Tc, D, -, -, hDT, -, R, R', h1, h2, h3, h4, rfl⟩ := hC
  exact represents_pullStructure Tc _ D R R' h1 h2 h3 h4 hΦ hT (hTT Tc) hDT

/-- **The core of Theorems 11.4.4 and 11.4.5 for `n = 1`** (H4's `measure_pull_core_bd` for
`m = 0`): for an equivalence `Φ`, `Θ = Φ^*Θ'`, `T̂'` the orientation `T̂` moved by the transport
charts, two signed measures `µ₁` on `(∂S, L(∂S))` and `µ'` on `(∂S', L(∂S'))` given by the local
formulas of Theorem 9.5.15 for `n = 1` (integrals over oriented points of `Φ^*ω'` and `ω'`) with
normalizations `c`, `c'` that agree along transport charts satisfy `µ₁(K) = µ'(|Φ|(K))`, and
`|Φ|(K) ∈ L(∂S')`. -/
theorem measure_pull_core_bd_dim1 (hΦ : Φ.IsEquivalence)
    (hΘ' : B.X.IsBranchedEpSubgroupoid Θ')
    (hcov' : ∀ y ∈ supp (B.X.boundaryTheta Θ'), ∃ D : B.X.OrientedTameStructure (0 + 1) Θ' y,
      D.Represents T' ∧ ∀ i, (D.boundarySheet i).Subsingleton)
    {Θ : A.Obj → ℚ} (hΘeq : Φ.pullbackTheta Θ' = Θ) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T) (hTT : Φ.IsTransported T T')
    (c : A.Obj → ℝ) (c' : B.Obj → ℝ)
    (hc : ∀ {x : A.Obj} {y : B.Obj} (Tc : Φ.TransportChart x y) (R : A.X.NaturalRep x)
      (R' : B.X.NaturalRep y), R.U ⊆ Tc.W → R'.U = Tc.Q '' R.U → c x = c' y)
    (ω' : B.epFormsInfty 0)
    (μ₁ : @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
      (A.X.lebesgueSigmaBoundaryH (0 + 1) Θ))
    (μ' : @SignedMeasure (B.X.orbitSupp (B.X.boundaryTheta Θ'))
      (B.X.lebesgueSigmaBoundaryH (0 + 1) Θ'))
    (hμ₁ : ∀ (x : A.Obj) (C : A.X.OrientedTameStructure (0 + 1) Θ x) (hCT : C.Represents T),
      x ∈ supp (A.X.boundaryTheta Θ) →
      (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ pointSheets A.X) →
      ∀ K, MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        μ₁ K = c x * (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum A.zeroFormIntegration
          (EP.epFormsInftyPullback Φ 0 ω') (A.X.π ⁻¹' (Subtype.val '' K)))
    (hμ' : ∀ (y : B.Obj) (D : B.X.OrientedTameStructure (0 + 1) Θ' y) (hDT : D.Represents T'),
      y ∈ supp (B.X.boundaryTheta Θ') →
      (∀ i, (D.boundarySheet i).Nonempty → D.boundarySheet i ∈ pointSheets B.X) →
      ∀ K, MeasurableSet[B.X.lebesgueSigmaBoundaryH (0 + 1) Θ'] K →
        Subtype.val '' K ⊆ B.X.π '' D.U →
        μ' K = c' y * (D.boundaryFamily hΘ' hDT).nonemptyPart.sheetSum B.zeroFormIntegration
          ω' (B.X.π ⁻¹' (Subtype.val '' K)))
    {K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ))}
    (hK : MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K) :
    MeasurableSet[B.X.lebesgueSigmaBoundaryH (0 + 1) Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      μ₁ K = μ' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := by
  subst hΘeq
  have hΘf := hΘ'.isFunctorial
  have hsupp := orbitSupp_boundaryTheta_pull hΦ hΘ'
  have hcovX : ∀ x ∈ supp (A.X.boundaryTheta (Φ.pullbackTheta Θ')),
      Nonempty (A.X.OrientedTameStructure (0 + 1) (Φ.pullbackTheta Θ') x) := fun x hx => by
    obtain ⟨C, -⟩ := exists_isBPulledDim1 hΦ hΘ' hcov' hx
    exact ⟨C⟩
  have hm' := measurable_bsuppInv hΦ hΘ' hcovX
  have hmeas : ∀ K : Set (A.X.orbitSupp (A.X.boundaryTheta (Φ.pullbackTheta Θ'))),
      MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) (Φ.pullbackTheta Θ')] K →
      MeasurableSet[B.X.lebesgueSigmaBoundaryH (0 + 1) Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := fun K hK => by
    rw [← preimage_bsuppInv hΦ hsupp K]; exact hm' hK
  refine ⟨hmeas K hK, ?_⟩
  let _ : MeasurableSpace (A.X.orbitSupp (A.X.boundaryTheta (Φ.pullbackTheta Θ'))) :=
    A.X.lebesgueSigmaBoundaryH (0 + 1) (Φ.pullbackTheta Θ')
  let _ : MeasurableSpace (B.X.orbitSupp (B.X.boundaryTheta Θ')) :=
    B.X.lebesgueSigmaBoundaryH (0 + 1) Θ'
  have : CompactSpace (A.X.orbitSupp (A.X.boundaryTheta (Φ.pullbackTheta Θ'))) :=
    isCompact_iff_compactSpace.1
      (isCompact_orbitSupp_boundaryTheta hΘ (hasIndependentTangentSums (X := A.X) _) hcpt)
  set μ₂ : SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta (Φ.pullbackTheta Θ'))) :=
    μ'.map (bsuppInv hΦ hsupp)
  have hμ₂ : ∀ K, MeasurableSet K →
      μ₂ K = μ' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := fun K hK => by
    rw [VectorMeasure.map_apply _ hm' hK, preimage_bsuppInv]
  -- the local agreement on a pulled-back structure
  have hloc : ∀ {x : A.Obj} (C : A.X.OrientedTameStructure (0 + 1) (Φ.pullbackTheta Θ') x),
      IsBPulledDim1 Φ hΘf T' C → ∀ K, MeasurableSet K → Subtype.val '' K ⊆ A.X.π '' C.U →
      μ₂ K = μ₁ K := by
    intro x C hC K hK hKU
    have hs := hC.subsingleton
    have hS : ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ pointSheets A.X :=
      fun i hne => C.boundarySheet_mem_pointSheets hΘ i (hs i) hne
    have hR := hC.represents hΦ hT.isGrHatSection hTT
    obtain ⟨y, Tc, D, hx, hy, hDT, hDs, R, R', h1, h2, h3, h4, rfl⟩ := hC
    set D₁ := D.restrictRep R' h1
    have hval := val_image_preimage hsupp.subset K
    have hD₁s : ∀ i, (D₁.boundarySheet i).Subsingleton := fun i =>
      (hDs i).anti ((D.boundarySheet_restrictRep R' h1 i).subset.trans inter_subset_left)
    have hD₁S : ∀ i, (D₁.boundarySheet i).Nonempty → D₁.boundarySheet i ∈ pointSheets B.X :=
      fun i hne => D₁.boundarySheet_mem_pointSheets hΘ' i (hD₁s i) hne
    have hD₁T := D.represents_restrictRep R' h1 hDT
    have hK' := hmeas K hK
    have hKU' : Subtype.val '' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K)) :
        Set (B.X.orbitSupp (B.X.boundaryTheta Θ'))) ⊆ B.X.π '' D₁.U := by
      rw [hval, restrictRep_U, h3]
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨u, hu, hπ⟩ := hKU hp
      rw [pullStructure_U] at hu
      exact ⟨Tc.Q u, mem_image_of_mem _ hu, by rw [Tc.π_Q (h2 hu), ← Φ.orbitMap_π, hπ]⟩
    have hW' : ∀ {z}, z ∈ D₁.U → z ∈ Tc.W' := fun hz =>
      restrictRep_U_subset_W' Tc D R R' h1 h2 h3 hz
    have hbW' : ∀ i, D₁.boundarySheet i ⊆ Tc.W' := fun i z hz =>
      hW' (D₁.subset_U i (D₁.boundarySheet_subset i hz))
    have hB : ∀ i, A.X.π ⁻¹' (Subtype.val '' K) ∩ Tc.Qinv '' D₁.boundarySheet i =
        Tc.Qinv '' (B.X.π ⁻¹' (Subtype.val '' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K)) :
          Set (B.X.orbitSupp (B.X.boundaryTheta Θ')))) ∩ D₁.boundarySheet i) := by
      intro i
      ext u
      constructor
      · rintro ⟨hu, z, hz, rfl⟩
        have hzW' := hbW' i hz
        refine ⟨z, ⟨?_, hz⟩, rfl⟩
        rw [mem_preimage, hval]
        refine ⟨_, hu, ?_⟩
        rw [Φ.orbitMap_π, ← Tc.π_Q (Tc.isScDiffeoOn_Q.mapsTo_inv hzW'),
          Tc.isScDiffeoOn_Q.right_inv z hzW']
      · rintro ⟨z, ⟨hzA, hz⟩, rfl⟩
        have hzW' := hbW' i hz
        refine ⟨?_, z, hz, rfl⟩
        rw [mem_preimage, hval] at hzA
        obtain ⟨p, hp, he⟩ := hzA
        rw [← Tc.isScDiffeoOn_Q.right_inv z hzW', Tc.π_Q (Tc.isScDiffeoOn_Q.mapsTo_inv hzW'),
          ← Φ.orbitMap_π] at he
        rw [mem_preimage, ← Φ.injective_orbitMap_of_full hΦ.full he]
        exact hp
    have hω : ∀ z ∈ Tc.W', A.zeroFormEval (EP.epFormsInftyPullback Φ 0 ω') (Tc.Qinv z) =
        B.zeroFormEval ω' z := fun z hz => by
      rw [Tc.zeroFormEval_pull_Q hΦ ω' (Tc.isScDiffeoOn_Q.mapsTo_inv hz),
        Tc.isScDiffeoOn_Q.right_inv z hz]
    have e := D₁.boundarySheetSum_move_dim1 Tc.isScDiffeoOn_Q.symm _ _ _ R _ _ hΘ' hD₁T hΘ hR
      hD₁s hω hB
    rw [hμ₂ K hK, hμ' y D₁ hD₁T hy hD₁S _ hK' hKU', hμ₁ x _ hR hx hS K hK hKU,
      hc Tc R R' h2 h3]
    exact congrArg _ e.symm
  -- gluing over the pulled-back structures
  let J := {j : Σ x, A.X.OrientedTameStructure (0 + 1) (Φ.pullbackTheta Θ') x //
    IsBPulledDim1 Φ hΘf T' j.2}
  let O : J → Set (A.X.orbitSupp (A.X.boundaryTheta (Φ.pullbackTheta Θ'))) :=
    fun j => Subtype.val ⁻¹' (A.X.π '' j.1.2.U)
  have hO : ∀ j, IsOpen (O j) := fun j =>
    (A.X.proposition_7_1_8 _ j.1.2.isOpen_U).preimage continuous_subtype_val
  have hcovO : ⋃ j, O j = univ := eq_univ_of_forall fun q => by
    obtain ⟨x, hx, hxq⟩ := q.2
    obtain ⟨C, hC⟩ := exists_isBPulledDim1 hΦ hΘ' hcov' hx
    exact mem_iUnion.2 ⟨⟨⟨x, C⟩, hC⟩, x, C.mem_U, hxq⟩
  obtain ⟨Ψ, -, huniq⟩ := existsUnique_linearMap_signedMeasure_of_openCover (V := ℝ)
    (borel_le_borelNullSigma _) O hO hcovO (fun _ => LinearMap.toSpanSingleton ℝ _ μ₁)
    (fun _ _ _ _ _ _ => rfl)
  have e1 := huniq (LinearMap.toSpanSingleton ℝ _ μ₁) fun _ _ _ _ _ => rfl
  have e2 := huniq (LinearMap.toSpanSingleton ℝ _ μ₂) fun j t K hK hKO => by
    change (t • μ₂) K = (t • μ₁) K
    change t • μ₂ K = t • μ₁ K
    rw [hloc j.1.2 j.2 K hK (by rintro _ ⟨q, hq, rfl⟩; exact hKO hq)]
  have e3 := congrArg (fun L : ℝ →ₗ[ℝ] SignedMeasure
      (A.X.orbitSupp (A.X.boundaryTheta (Φ.pullbackTheta Θ'))) => L 1) (e2.trans e1.symm)
  simp only [LinearMap.toSpanSingleton_apply, one_smul] at e3
  rw [← hμ₂ K hK, e3]

/-! ### Theorems 11.4.4 and 11.4.5 for an equivalence, `n = 1` -/

/-- The oriented tame structures of `Θ̂'` give boundary sheets with at most one point at every
point of `supp ∂Θ'` (`exists_boundarySheet_subsingleton`). -/
theorem hcov_subsingleton_of_loc {Y : EP.{u}} {Θ' : Y.Obj → ℚ}
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hloc' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure (0 + 1) Θ' y, D.Represents T') :
    ∀ y ∈ supp (Y.X.boundaryTheta Θ'), ∃ D : Y.X.OrientedTameStructure (0 + 1) Θ' y,
      D.Represents T' ∧ ∀ i, (D.boundarySheet i).Subsingleton := fun y hy => by
  obtain ⟨D₀, hD₀⟩ := hloc' y (Y.X.supp_boundaryTheta_subset Θ' hy).2
  obtain ⟨D, hDT, hs, -⟩ := D₀.exists_boundarySheet_subsingleton hD₀
  exact ⟨D, hDT, hs⟩

/-- `Φ^*Θ̂'` is oriented and tame when `Θ̂'` is (H4's `hcov_pull`, sheets dropped). -/
theorem hloc_pull_dim1 (hΦ : Φ.IsEquivalence) (hΘ' : B.X.IsFunctorial Θ')
    (hT : A.X.IsGrHatSection T) (hTT : Φ.IsTransported T T')
    (hloc' : ∀ y ∈ supp Θ', ∃ D : B.X.OrientedTameStructure (0 + 1) Θ' y, D.Represents T') :
    ∀ x ∈ supp (Φ.pullbackTheta Θ'),
      ∃ C : A.X.OrientedTameStructure (0 + 1) (Φ.pullbackTheta Θ') x, C.Represents T :=
  fun x hx => (hcov_pull hΦ (EP.epFormsInftyEval_isPullback hΦ (0 + 1)) hΘ' hT hTT
    ((B.epFormsInftyEval (0 + 1)).hcov_of_loc hloc') x hx).imp fun _ h => h.2

/-- `Φ_*Θ̂` is oriented and tame when `Θ̂` is (H4's `hcov_push`, sheets dropped). -/
theorem hloc_push_dim1 (hΦ : Φ.IsEquivalence) {Θ : A.Obj → ℚ} (hΘ : A.X.IsFunctorial Θ)
    (hTT : Φ.IsTransported T T')
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T) :
    ∀ y ∈ supp (Φ.pushforwardTheta Θ),
      ∃ D : B.X.OrientedTameStructure (0 + 1) (Φ.pushforwardTheta Θ) y, D.Represents T' :=
  fun y hy => (hcov_push hΦ (EP.epFormsInftyEval_isPullback hΦ (0 + 1)) hΘ hTT
    ((A.epFormsInftyEval (0 + 1)).hcov_of_loc hloc) y hy).imp fun _ h => h.2

/-- **Theorem 11.4.4, 2021 p. 545 (new in the 2021 edition), second identity, for an equivalence
`Φ : X → Y` and `n = 1`**: for `Θ̂'` on `Y` oriented, tame (an oriented tame structure describing
`T̂'` at every point), compact, `1`-dimensional, a `0`-form `ω'`, and
`K ∈ L(|supp ∂(Φ^*Θ')|)`: `|Φ|(K) ∈ L(|supp ∂Θ'|)` and
`µ^{∂Φ^*Θ̂'}_{Φ^*ω'}(K) = µ^{∂Θ̂'}_{ω'}(|Φ|(K))`, for the boundary measures of Theorem 9.5.15
(`EP.boundaryBranchedMeasureDim1`). -/
theorem theorem_11_4_4_pull_equiv_dim1 (hΦ : Φ.IsEquivalence)
    (hΘ' : B.X.IsBranchedEpSubgroupoid Θ') (hcpt' : B.X.IsCompactBranched Θ')
    (hT' : B.X.IsOrientation Θ' T')
    (hloc' : ∀ y ∈ supp Θ', ∃ D : B.X.OrientedTameStructure (0 + 1) Θ' y, D.Represents T')
    (ω' : B.epFormsInfty 0) {K : Set (A.X.orbitSupp (A.X.boundaryTheta (Φ.pullbackTheta Θ')))}
    (hK : MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) (Φ.pullbackTheta Θ')] K) :
    MeasurableSet[B.X.lebesgueSigmaBoundaryH (0 + 1) Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      A.boundaryBranchedMeasureDim1 (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
        (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
        (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := B.X) Θ') hT')
        (hloc_pull_dim1 hΦ hΘ'.isFunctorial
          (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := B.X) Θ') hT').isGrHatSection
          (isTransported_pull hΦ hT'.isGrHatSection) hloc')
        (EP.epFormsInftyPullback Φ 0 ω') K =
        B.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc' ω'
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) :=
  measure_pull_core_bd_dim1 hΦ hΘ'
    (hcov_subsingleton_of_loc hloc') rfl (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
    (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
    (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := B.X) Θ') hT')
    (isTransported_pull hΦ hT'.isGrHatSection) (fun x => (Nat.card (A.X.Isotropy x) : ℝ)⁻¹)
    (fun y => (Nat.card (B.X.Isotropy y) : ℝ)⁻¹)
    (fun Tc _ _ _ _ => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj hΦ)))) ω' _ _
    (fun x C hCT hx hS K hK hKU => A.boundaryBranchedMeasureDim1_spec _ _ _ _ _ x C hCT hx hS K hK hKU)
    (fun y D hDT hy hS K hK hKU => B.boundaryBranchedMeasureDim1_spec _ _ _ _ _ y D hDT hy hS K hK hKU) hK

/-- **Theorem 11.4.4, 2021 p. 545 (new in the 2021 edition), first identity, for an equivalence
`Φ : X → Y` and `n = 1`**: for `Θ̂` on `X` oriented, tame, compact, `1`-dimensional,
`K ∈ L(|supp ∂Θ|)` and `Φ^*ω' = ω`: `|Φ|(K) ∈ L(|supp ∂Φ_*Θ|)` and
`µ^{∂Θ̂}_ω(K) = µ^{∂Φ_*Θ̂}_{ω'}(|Φ|(K))`. -/
theorem theorem_11_4_4_push_equiv_dim1 (hΦ : Φ.IsEquivalence) {Θ : A.Obj → ℚ}
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    {ω : A.epFormsInfty 0} {ω' : B.epFormsInfty 0} (hω : EP.epFormsInftyPullback Φ 0 ω' = ω)
    {K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ))}
    (hK : MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K) :
    MeasurableSet[B.X.lebesgueSigmaBoundaryH (0 + 1) (Φ.pushforwardTheta Θ)]
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      A.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc ω K =
        B.boundaryBranchedMeasureDim1 (isBranchedEpSubgroupoid_pushforwardTheta hΦ hΘ)
          (isCompactBranched_pushforwardTheta Φ hΦ.full hΘ.isFunctorial hcpt)
          (isOrientation_pushSection hΦ hΘ (hasIndependentTangentSums (X := A.X) Θ) hT)
          (hloc_push_dim1 hΦ hΘ.isFunctorial (isTransported_push hΦ hT.isGrHatSection) hloc) ω'
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := by
  subst hω
  have hloc' := hloc_push_dim1 hΦ hΘ.isFunctorial (isTransported_push hΦ hT.isGrHatSection) hloc
  exact measure_pull_core_bd_dim1 hΦ (isBranchedEpSubgroupoid_pushforwardTheta hΦ hΘ)
    (hcov_subsingleton_of_loc hloc')
    (pullbackTheta_pushforwardTheta hΦ.full hΘ.isFunctorial)
    hΘ hcpt hT (isTransported_push hΦ hT.isGrHatSection) (fun x => (Nat.card (A.X.Isotropy x) : ℝ)⁻¹)
    (fun y => (Nat.card (B.X.Isotropy y) : ℝ)⁻¹)
    (fun Tc _ _ _ _ => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj hΦ)))) ω' _ _
    (fun x C hCT hx hS K hK hKU => A.boundaryBranchedMeasureDim1_spec _ _ _ _ _ x C hCT hx hS K hK hKU)
    (fun y D hDT hy hS K hK hKU => B.boundaryBranchedMeasureDim1_spec _ _ _ _ _ y D hDT hy hS K hK hKU) hK

/-- The hypothesis of Theorem 9.5.16 (`n = 1`) for an ep-groupoid with the local unique
continuation property: every natural representation has LUC. -/
theorem hlocEff_of_isLUC {Y : EP.{u}} {Θ' : Y.Obj → ℚ} {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hL : Y.X.IsLUC)
    (hloc' : ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure (0 + 1) Θ' y, D.Represents T') :
    ∀ y ∈ supp Θ', ∃ D : Y.X.OrientedTameStructure (0 + 1) Θ' y,
      D.Represents T' ∧ D.rep.HasLUC :=
  fun y hy => (hloc' y hy).imp fun D h => ⟨h, Y.X.isLUC_iff_forall_naturalRep.1 hL _ D.rep⟩

/-- **Theorem 11.4.5, 2021 p. 545, second identity, for an equivalence and `n = 1`**: as
`theorem_11_4_4_pull_equiv_dim1` for the effective boundary measures of Theorem 9.5.16, between
ep-groupoids with the local unique continuation property. -/
theorem theorem_11_4_5_pull_equiv_dim1 (hΦ : Φ.IsEquivalence) (hLY : B.X.IsLUC)
    (hΘ' : B.X.IsBranchedEpSubgroupoid Θ') (hcpt' : B.X.IsCompactBranched Θ')
    (hT' : B.X.IsOrientation Θ' T')
    (hloc' : ∀ y ∈ supp Θ', ∃ D : B.X.OrientedTameStructure (0 + 1) Θ' y, D.Represents T')
    (ω' : B.epFormsInfty 0) {K : Set (A.X.orbitSupp (A.X.boundaryTheta (Φ.pullbackTheta Θ')))}
    (hK : MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) (Φ.pullbackTheta Θ')] K) :
    MeasurableSet[B.X.lebesgueSigmaBoundaryH (0 + 1) Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      A.boundaryBranchedMeasureEffDim1 (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
        (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
        (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := B.X) Θ') hT')
        (hlocEff_of_isLUC ((proposition_10_1_16 hΦ).2 hLY) (hloc_pull_dim1 hΦ hΘ'.isFunctorial
          (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := B.X) Θ') hT').isGrHatSection
          (isTransported_pull hΦ hT'.isGrHatSection) hloc'))
        (EP.epFormsInftyPullback Φ 0 ω') K =
        B.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT' (hlocEff_of_isLUC hLY hloc') ω'
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := by
  have hLX := (proposition_10_1_16 hΦ).2 hLY
  exact measure_pull_core_bd_dim1 hΦ hΘ'
    (hcov_subsingleton_of_loc hloc') rfl (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
    (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
    (isOrientation_pullSection hΦ (hasIndependentTangentSums (X := B.X) Θ') hT')
    (isTransported_pull hΦ hT'.isGrHatSection) (fun x => (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹)
    (fun y => (Nat.card (B.X.EffIsotropy y) : ℝ)⁻¹)
    (fun Tc R R' hRW hR' => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Tc.card_effIsotropy_eq hΦ R R' hRW hR' (A.X.isLUC_iff_forall_naturalRep.1 hLX _ R)
        (B.X.isLUC_iff_forall_naturalRep.1 hLY _ R'))) ω' _ _
    (fun x C hCT hx hS K hK hKU => A.boundaryBranchedMeasureEffDim1_spec _ _ _ _ _ x C hCT hx hS (A.X.isLUC_iff_forall_naturalRep.1 hLX _ C.rep) K hK hKU)
    (fun y D hDT hy hS K hK hKU => B.boundaryBranchedMeasureEffDim1_spec _ _ _ _ _ y D hDT hy hS (B.X.isLUC_iff_forall_naturalRep.1 hLY _ D.rep) K hK hKU) hK

/-- **Theorem 11.4.5, 2021 p. 545, first identity, for an equivalence and `n = 1`**: as
`theorem_11_4_4_push_equiv_dim1` for the effective boundary measures of Theorem 9.5.16, between
ep-groupoids with the local unique continuation property. -/
theorem theorem_11_4_5_push_equiv_dim1 (hΦ : Φ.IsEquivalence) (hLX : A.X.IsLUC) {Θ : A.Obj → ℚ}
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    {ω : A.epFormsInfty 0} {ω' : B.epFormsInfty 0} (hω : EP.epFormsInftyPullback Φ 0 ω' = ω)
    {K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ))}
    (hK : MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K) :
    MeasurableSet[B.X.lebesgueSigmaBoundaryH (0 + 1) (Φ.pushforwardTheta Θ)]
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      A.boundaryBranchedMeasureEffDim1 hΘ hcpt hT (hlocEff_of_isLUC hLX hloc) ω K =
        B.boundaryBranchedMeasureEffDim1 (isBranchedEpSubgroupoid_pushforwardTheta hΦ hΘ)
          (isCompactBranched_pushforwardTheta Φ hΦ.full hΘ.isFunctorial hcpt)
          (isOrientation_pushSection hΦ hΘ (hasIndependentTangentSums (X := A.X) Θ) hT)
          (hlocEff_of_isLUC ((proposition_10_1_16 hΦ).1 hLX)
            (hloc_push_dim1 hΦ hΘ.isFunctorial (isTransported_push hΦ hT.isGrHatSection) hloc))
          ω' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := by
  subst hω
  have hLY := (proposition_10_1_16 hΦ).1 hLX
  have hloc' := hloc_push_dim1 hΦ hΘ.isFunctorial (isTransported_push hΦ hT.isGrHatSection) hloc
  exact measure_pull_core_bd_dim1 hΦ (isBranchedEpSubgroupoid_pushforwardTheta hΦ hΘ)
    (hcov_subsingleton_of_loc hloc')
    (pullbackTheta_pushforwardTheta hΦ.full hΘ.isFunctorial)
    hΘ hcpt hT (isTransported_push hΦ hT.isGrHatSection)
    (fun x => (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹) (fun y => (Nat.card (B.X.EffIsotropy y) : ℝ)⁻¹)
    (fun Tc R R' hRW hR' => congrArg (fun k : ℕ => (k : ℝ)⁻¹)
      (Tc.card_effIsotropy_eq hΦ R R' hRW hR' (A.X.isLUC_iff_forall_naturalRep.1 hLX _ R)
        (B.X.isLUC_iff_forall_naturalRep.1 hLY _ R'))) ω' _ _
    (fun x C hCT hx hS K hK hKU => A.boundaryBranchedMeasureEffDim1_spec _ _ _ _ _ x C hCT hx hS (A.X.isLUC_iff_forall_naturalRep.1 hLX _ C.rep) K hK hKU)
    (fun y D hDT hy hS K hK hKU => B.boundaryBranchedMeasureEffDim1_spec _ _ _ _ _ y D hDT hy hS (B.X.isLUC_iff_forall_naturalRep.1 hLY _ D.rep) K hK hKU) hK

end EpFunctor

end Polyfold
