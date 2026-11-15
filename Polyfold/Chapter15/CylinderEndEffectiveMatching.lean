import Polyfold.Chapter15.CylinderEndCorollary
import Polyfold.Chapter15.CylinderEndEffective

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703,
**Corollary 15.4.4** (2017: Corollary 15.2), for the effective measures of Theorems 9.5.5 and
9.5.16 (Definition 7.2.15).

# The effective end identities of the cylinder from matched structures

## The text, paraphrased

The integrals of §9.5 come in two forms, with the weights `1/♯G_x` and `1/♯G_x^eff`.  The
isotropy group of `(t, x)` in `[0, 1] × X` is that of `x`, and an element acts trivially near
`(t, x)` iff it acts trivially near `x`; so `♯G^eff_{(t, x)} = ♯G^eff_x`, and the argument for
`∂Θ̃ = Θ₁ ⊔ −Θ₀` is the same for both forms.

## What is formalized

* `EpGroupoid.cubeIsotropyHom_mem_trivialSet_iff`, **`EpGroupoid.card_effIsotropy_cubeProd`**:
  `T_{(q, x)} = T_x` under `G_{(q, x)} ≅ G_x`, and `♯G^eff_{(q, x)} = ♯G^eff_x`.
* **`SBLocalization.isLocalEndIdentityEff_of_matched`**,
  **`SBLocalization.isCylinderBoundaryEffOf_of_matched`**: the effective forms of
  `isLocalEndIdentity_of_matched`, `isCylinderBoundaryOf_of_matched`.
* `SBLocalization.cylinderLocalEndsEffStatement_of_matchedOrientations`,
  **`SBLocalization.corollary_15_4_4_eff_of_matchedOrientations`**: the effective Corollary
  15.4.4 with step (c) of its proof in the form `CylinderMatchedOrientationsStatement`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory Filter

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  (X : EpGroupoid Obj Mor) (n : ℕ)
  [ParacompactSpace ((Fin n → unitInterval) × Obj)]
  [ParacompactSpace ((Fin n → unitInterval) × Mor)]

/-- **`T_{(q, x)} = T_x`**: an element `(q, g)` of the isotropy group of `(q, x)` in
`[0, 1]ⁿ × X` acts trivially iff `g` acts trivially (`s = t` near `(q, g)` iff `s = t` near
`g`). -/
theorem cubeIsotropyHom_mem_trivialSet_iff (z : (Fin n → unitInterval) × Obj)
    (g : (X.cubeProd n).Isotropy z) :
    X.cubeIsotropyHom n z g ∈ X.trivialSet z.2 ↔ g ∈ (X.cubeProd n).trivialSet z := by
  rw [X.mem_trivialSet_iff_eventually, (X.cubeProd n).mem_trivialSet_iff_eventually]
  constructor
  · intro h
    have hc : ContinuousAt (Prod.snd : (Fin n → unitInterval) × Mor → Mor) g.val :=
      continuous_snd.continuousAt
    filter_upwards [hc.eventually h] with ψ hψ
    rw [cubeProd_src, cubeProd_tgt]
    exact Prod.ext rfl hψ
  · intro h
    have hc : ContinuousAt (fun ψ : Mor => ((g.val.1, ψ) : (Fin n → unitInterval) × Mor))
        (X.cubeIsotropyHom n z g).val := (continuous_const.prodMk continuous_id).continuousAt
    have h' : ∀ᶠ ψ in 𝓝 ((g.val.1, (X.cubeIsotropyHom n z g).val) :
        (Fin n → unitInterval) × Mor), (X.cubeProd n).src ψ = (X.cubeProd n).tgt ψ := h
    filter_upwards [hc.eventually h'] with ψ hψ
    rw [cubeProd_src, cubeProd_tgt] at hψ
    exact congrArg Prod.snd hψ

/-- **`♯G^eff_{(q, x)} = ♯G^eff_x`** for the ep-groupoid `[0, 1]ⁿ × X` (Definition 7.2.15). -/
theorem card_effIsotropy_cubeProd (z : (Fin n → unitInterval) × Obj) :
    Nat.card ((X.cubeProd n).EffIsotropy z) = Nat.card (X.EffIsotropy z.2) := by
  set e : (X.cubeProd n).Isotropy z ≃* X.Isotropy z.2 :=
    MulEquiv.ofBijective (X.cubeIsotropyHom n z) (X.bijective_cubeIsotropyHom n z) with he
  have himg : (e : (X.cubeProd n).Isotropy z →* X.Isotropy z.2) ''
      (X.cubeProd n).trivialSet z = X.trivialSet z.2 := by
    ext k
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (X.cubeIsotropyHom_mem_trivialSet_iff n z g).2 hg
    · intro hk
      obtain ⟨g, rfl⟩ := e.surjective k
      exact ⟨g, (X.cubeIsotropyHom_mem_trivialSet_iff n z g).1 hk, rfl⟩
  have hmap : (Subgroup.normalClosure ((X.cubeProd n).trivialSet z)).map
      (e : (X.cubeProd n).Isotropy z →* X.Isotropy z.2) =
      Subgroup.normalClosure (X.trivialSet z.2) := by
    have h := Subgroup.map_normalClosure ((X.cubeProd n).trivialSet z)
      (e : (X.cubeProd n).Isotropy z →* X.Isotropy z.2) e.surjective
    rw [h, himg]
  exact Nat.card_congr (QuotientGroup.congr _ _ e hmap).toEquiv

end EpGroupoid

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

set_option maxHeartbeats 1600000 in
-- the statement unfolds the cylinder's ep-groupoid in several places
/-- **The effective local end identity from matched structures** (proof of Corollary 15.4.4,
p. 703, for the measures of Theorems 9.5.5 and 9.5.16): let every `x ∈ supp Θ` have an oriented
tame structure `C` of `Θ` at `x` (sheets in the class of the integration, describing the
orientation of `P`) and one `C̃` of `Θ̃` at `(i, x)` describing `T̃` that match with sign `ε`.
Then the effective boundary measure of `pr^*ω` on the end `i` is locally `ε` times the effective
measure of `ω` on `|supp Θ|`: the sheet sums agree up to `ε`, and
`♯G^eff_{(i, x)} = ♯G^eff_x`. -/
theorem isLocalEndIdentityEff_of_matched {f : A.Obj → A.W} {m : ℕ} (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) (P : OrientedRegularPerturbation A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    {i : unitInterval} {ε : ℝ}
    (hover : ∀ p : cylEnd (X := A.X) Θ' (i : ℝ),
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))
    (h : ∀ x ∈ EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)),
      ∃ (C : A.X.OrientedTameStructure (m + 1) (fun z => (P.Λ (f z) : ℚ)) x)
        (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' ((fun _ => i), x))
        (hCT' : C'.Represents T') (hS : ∀ j, C.M j ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets),
        C.Represents P.T ∧ AreMatchedAt (fun _ => i) C C' hΘ' hCT' hS ε) :
    IsLocalEndIdentityEff hLUC hLUCC P hΘ' hcpt' hT' hloc' (i : ℝ) ε hover := by
  classical
  set q : Fin 1 → unitInterval := fun _ => i with hq
  refine isLocalEndIdentityEff_of_structures hLUC hLUCC P hΘ' hcpt' hT' hloc' hover
    fun x hx => ?_
  obtain ⟨C, C', hCT', hS, hCT, e, he, hrange, hσ, hM, hU, hε⟩ := h x hx
  -- the point `(i, x)` lies in `supp ∂Θ̃`
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
  have hz : ((q, x) : (A.cubeSEP 1).Obj) ∈
      EpGroupoid.supp ((A.cubeSEP 1).X.boundaryTheta Θ') := by
    obtain ⟨j₀, hj₀⟩ := (C.toLocalBranchingStructure.mem_supp_iff C.mem_U).1 hx
    obtain ⟨j, rfl⟩ := hrg j₀ x hj₀
    exact hsupp j x hj₀
  have hS' : ∀ j, (C'.boundarySheet j).Nonempty →
      C'.boundarySheet j ∈ ((A.cubeSEP 1).baseEP.epFormsInftyEval (m + 1)).msheets :=
    fun j hj => by
      have := hM ⟨j, hj⟩
      rw [this]
      exact cubeFace_mem_msheets q (hS _)
  have hNo : IsOpen (A.X.π '' C.U) := A.X.proposition_7_1_8 _ C.isOpen_U
  refine ⟨C, (q, x), C', hCT', A.X.π '' C.U, hS, hCT, hz, hS', hNo, ⟨x, C.mem_U, rfl⟩,
    Subset.rfl, ?_, ?_⟩
  · -- the end over `|U(x)|` lies in `|Ũ(i, x)|`
    intro p hp
    obtain ⟨z, -, hzp⟩ := p.1.2
    obtain ⟨y, hyU, hy⟩ := hp
    rw [A.X.cylEndMap_π p z hzp] at hy
    have ht : (z.1 0 : ℝ) = i := by
      have h2 : A.X.cylOrbitTime p.1.1 = i := p.2
      rwa [← hzp, cylOrbitTime_π] at h2
    have hz1 : z.1 = q := funext fun a => by
      have : a = 0 := Subsingleton.elim _ _
      subst this
      exact Subtype.ext ht
    refine ⟨(q, y), hU y hyU, ?_⟩
    rw [← hzp]
    exact ((A.X.cubeProd_π_eq_π_iff 1 (q, y) z).2 ⟨hz1.symm, hy⟩)
  · intro ω K hK hKN
    have hcl : IsClosed (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))) := P.isCompact.isClosed
    have hKb : MeasurableSet[borel A.X.OrbitSpace] (Subtype.val '' K) := by
      let _ : MeasurableSpace A.X.OrbitSpace := borel _
      have : BorelSpace A.X.OrbitSpace := ⟨rfl⟩
      have : BorelSpace (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))) := Subtype.borelSpace _
      exact hcl.measurableSet.subtype_image (by
        rw [BorelSpace.measurable_eq (α := A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))]
        exact hK)
    have hA₀ : MeasurableSet[borel A.Obj] (A.X.π ⁻¹' (Subtype.val '' K)) := by
      let _ : MeasurableSpace A.X.OrbitSpace := borel _
      have : BorelSpace A.X.OrbitSpace := ⟨rfl⟩
      let _ : MeasurableSpace A.Obj := borel _
      have : BorelSpace A.Obj := ⟨rfl⟩
      exact A.X.continuous_π.measurable hKb
    have hA : ∀ j₀, (A.cubeSEP 1).X.π ⁻¹'
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
        let p : cylEnd (X := A.X) Θ' (i : ℝ) :=
          ⟨⟨(A.X.cubeProd 1).π (q, y), (q, y), hsupp j y hy, rfl⟩, by
            change A.X.cylOrbitTime ((A.X.cubeProd 1).π (q, y)) = i
            rw [cylOrbitTime_π]⟩
        have hp : cylEndProj hover p = s := Subtype.ext (by
          change cylEndMap p = s.1
          rw [A.X.cylEndMap_π p (q, y) rfl]
          exact hsy.symm)
        exact ⟨_, ⟨p, by change cylEndProj hover p ∈ K; rw [hp]; exact hsK, rfl⟩, rfl⟩
    have hAm : ∀ j₀, (A.baseEP.epFormsInftyEval (m + 1)).sheetNull.IsMeasIn (C.M j₀)
        (A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M j₀) := fun j₀ =>
      SheetNullSets.isMeasIn_inter_iff.2 (SheetNullSets.isMeasIn_of_borel hA₀)
    have hε' : (ε = 1 ∧ ∀ j, ∀ y ∈ A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M (e j),
          (C'.boundaryOrient j.1).tangent ((cubeFaceIncl A q).obj y) =
            (faceOrient q (C.orient (e j)) (hS (e j)).1.1).tangent
              ((cubeFaceIncl A q).obj y)) ∨
        (ε = -1 ∧ ∀ j, ∀ y ∈ A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M (e j),
          (C'.boundaryOrient j.1).tangent ((cubeFaceIncl A q).obj y) ≠
            (faceOrient q (C.orient (e j)) (hS (e j)).1.1).tangent
              ((cubeFaceIncl A q).obj y)) :=
      hε.imp (fun h => ⟨h.1, fun j y hy => h.2 j y hy.2⟩)
        (fun h => ⟨h.1, fun j y hy => h.2 j y hy.2⟩)
    have key := sheetSum_boundaryFamily_cubeFace q C C' hΘ' hCT' hS e he hrange hσ hM hA hAm
      hε' ω
    have hcard : Nat.card ((A.cubeSEP 1).X.EffIsotropy ((q, x) : (A.cubeSEP 1).Obj)) =
        Nat.card (A.X.EffIsotropy x) := A.X.card_effIsotropy_cubeProd 1 (q, x)
    rw [key, hcard]
    change _ = ε * ((Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹ * _)
    ring

/-- **`∂Θ̃ = Θ₁ ⊔ −Θ₀` for the effective measures from matched structures** (proof of Corollary
15.4.4, p. 703): the effective form of `isCylinderBoundaryOf_of_matched`. -/
theorem isCylinderBoundaryEffOf_of_matched {f : A.Obj → A.W} {m : ℕ} (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) (P₀ P₁ : OrientedRegularPerturbation A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    (hover₀ : ∀ p : cylEnd (X := A.X) Θ' 0,
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P₀.Λ (f z) : ℚ)))
    (hover₁ : ∀ p : cylEnd (X := A.X) Θ' 1,
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P₁.Λ (f z) : ℚ)))
    (h₀ : ∀ x ∈ EpGroupoid.supp (fun z => (P₀.Λ (f z) : ℚ)),
      ∃ (C : A.X.OrientedTameStructure (m + 1) (fun z => (P₀.Λ (f z) : ℚ)) x)
        (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' ((fun _ => 0), x))
        (hCT' : C'.Represents T') (hS : ∀ j, C.M j ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets),
        C.Represents P₀.T ∧ AreMatchedAt (fun _ => 0) C C' hΘ' hCT' hS (-1))
    (h₁ : ∀ x ∈ EpGroupoid.supp (fun z => (P₁.Λ (f z) : ℚ)),
      ∃ (C : A.X.OrientedTameStructure (m + 1) (fun z => (P₁.Λ (f z) : ℚ)) x)
        (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' ((fun _ => 1), x))
        (hCT' : C'.Represents T') (hS : ∀ j, C.M j ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets),
        C.Represents P₁.T ∧ AreMatchedAt (fun _ => 1) C C' hΘ' hCT' hS 1) :
    IsCylinderBoundaryEffOf hLUC hLUCC P₀ P₁ hΘ' hcpt' hT' hloc' :=
  isCylinderBoundaryEffOf_of_local hLUC hLUCC P₀ P₁ hΘ' hcpt' hT' hloc' hover₀ hover₁
    (isLocalEndIdentityEff_of_matched hLUC hLUCC P₀ hΘ' hcpt' hT' hloc' (i := 0) hover₀ h₀)
    (isLocalEndIdentityEff_of_matched hLUC hLUCC P₁ hΘ' hcpt' hT' hloc' (i := 1) hover₁ h₁)

/-! ### The effective Corollary 15.4.4 from the orientations of the matched structures -/

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
/-- **The effective local end identities from the orientations of the matched structures**:
for `d_X ≡ 0`, `f` sc-Fredholm with tame germ data and the face condition of Theorem 15.3.9 for
the glued data, `CylinderMatchedOrientationsStatement` gives `CylinderLocalEndsEffStatement`. -/
theorem cylinderLocalEndsEffStatement_of_matchedOrientations
    (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f) {m : ℕ}
    (hLUC : A.X.IsLUC) (hLUCC : (A.cubeSEP 1).X.IsLUC)
    {P₀ P₁ : OrientedRegularPerturbation A f m}
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (h : CylinderMatchedOrientationsStatement hf.1.1.1 P₀ P₁) :
    CylinderLocalEndsEffStatement hf.1.1.1 hLUC hLUCC P₀ P₁ := by
  intro Λ' hreg e0 e1 hΘ' hcpt'
  obtain ⟨T', hT', hloc', hor₀, hor₁⟩ := h Λ' hreg e0 e1 hΘ' hcpt'
  have hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ' := hreg.2.1.1
  have z0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  have z1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  refine ⟨T', hT', hloc', fun p => cylEndMap_mem_orbitSupp_zero hd hf.1.1.1 e0 e1 p,
    fun p => cylEndMap_mem_orbitSupp_one hd hf.1.1.1 e0 e1 p, ?_, ?_⟩
  · exact isLocalEndIdentityEff_of_matched hLUC hLUCC P₀ hΘ' hcpt' hT' hloc' (i := 0) _
      (exists_areMatchedAt_of_orientations hd hf hft P₀ hΛ' e0 e1 honto (i := 0)
        (Or.inl ⟨z0, rfl⟩) e0 hΘ' hor₀)
  · exact isLocalEndIdentityEff_of_matched hLUC hLUCC P₁ hΘ' hcpt' hT' hloc' (i := 1) _
      (exists_areMatchedAt_of_orientations hd hf hft P₁ hΛ' e0 e1 honto (i := 1)
        (Or.inr ⟨z1, rfl⟩) e1 hΘ' hor₁)

/-- **Corollary 15.4.4, effective version (p. 703), from the orientations of the matched
structures**: `corollary_15_4_4_eff_of_local_ends` with step (c) reduced to
`CylinderMatchedOrientationsStatement`. -/
theorem corollary_15_4_4_eff_of_matchedOrientations
    (hrelC : theorem_15_3_7_relative_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity) (hLUCC : (A.cubeSEP 1).X.IsLUC)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    (Can : OrientedRegularPerturbation A f m → Prop)
    (hglue : ∀ P₀ P₁, Can P₀ → Can P₁ →
      IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue P₀.Λ P₁.Λ) ∧
        IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (hor : ∀ P₀ P₁, Can P₀ → Can P₁ →
      CylinderMatchedOrientationsStatement hf.1.1.1 P₀ P₁) :
    corollary_15_4_4_eff_statement A f m hLUC Can :=
  corollary_15_4_4_eff_of_local_ends hrelC hd hpara hPU hLUC hPUC hLUCC hf hft hS Can hglue
    fun P₀ P₁ h₀ h₁ => cylinderLocalEndsEffStatement_of_matchedOrientations hd hf hft hLUC hLUCC
      (hglue P₀ P₁ h₀ h₁).2 (hor P₀ P₁ h₀ h₁)

end SBLocalization

end Polyfold
