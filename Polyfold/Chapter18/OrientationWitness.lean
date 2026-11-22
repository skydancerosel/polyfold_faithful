import Polyfold.Chapter18.OrientationsExamples
import Polyfold.Chapter12.OrientationGeneralizedIsoOriented

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.5, pp. 856–859: **an orientation of the diagonal section of the reflection bundle**
(Definition 18.5.4, Proposition 18.5.6 (1)), with the isotropy `g = (−1, 0)` of `0` acting by
`g_* = Id` on the two orientations of `DET(f, 0)` (p. 857).  Numbers and pages are the 2021
text's.

# The diagonal section of `ℤ/2 ⋉ (ℝ × ℝ) → ℤ/2 ⋉ ℝ` is orientable

`C = ℤ/2 ⋉ ℝ`, `E = ℝ × ℝ` with `−1` acting by `(x, v) ↦ (−x, −v)`, and `f(x) = (x, x)`
(`reflDiag`).  The isotropy `−1` of `0` acts on the fibre `μ(0) = ℝ` by `v ↦ −v`; it acts on
`T_0ℝ = ℝ` by `−1` as well, and the linearization `f'(0) = id` commutes with both, so `g_*` is
the identity on `det(f'(0)) = λ(0) ⊗ λ*(0)`.

## Readings

* **`g_*` on `Or_0`.**  We read the action of an isotropy morphism `σ` on the orientations of
  `DET(f, x)` as Definition 12.5.2 (`orMor`): the conjugation of `Lin(f, x)` by `Tσ` and
  `μ(σ, ·)`.  At a zero `x` with an isomorphism `f'(x)`, `f'(x)` is a member of `Lin(f, x)` fixed
  by this conjugation (`zeroLin_morTx`), and the conjugation is the identity on
  `det(f'(x)) = λ(0) ⊗ λ*(0)` (`conjDet_eq_refl_of_bijective`); so `σ_* = Id`
  (`orMor_eq_self_of_bijective`).  No sign computation in a chart is needed.
* **The orientation.**  We build it in the strong bundle model of one copy of `Ψ̄`
  (`reflSingleModel`, objects `Σ _ : Unit, ℝ`): a continuous orientation over all of `X_Ψ̄` exists
  because paths in `ℝ` with the same end points are homotopic (Theorem 6.6.17,
  `exists_continuous_orSec_of_hom_eq`); its invariance is locally constant along the morphisms
  (`eventually_isOrInvariantAt_iff`, from Theorem 12.5.3), every sheet `{(q, (g, q), g q)}` of
  morphisms is connected and meets the isotropy of `0`, where the invariance holds by the first
  reading.  Proposition 18.5.6 (1) carries it to `f`.

## What is formalized

* `conjDet_eq_refl_of_bijective`, `ChartPoint.zeroLin`, `ChartPoint.zeroLin_mem_linSet`,
  `ChartPoint.zeroLin_transferT`, `ChartPoint.bijective_zeroLin_of_bijective`,
  `EpStrongBundle.zeroLin_morTx`, **`EpStrongBundle.orMor_eq_self_of_bijective`**: an isotropy
  morphism at a zero with an isomorphism `f'(x)` acts trivially on the orientations.
* `EpStrongBundle.IsOrInvariantAt`, `EpStrongBundle.isOrInvariantAt_of_bijective`,
  **`EpStrongBundle.eventually_isOrInvariantAt_iff`**: for a continuous orientation over all
  of `X`, the invariance clause at a morphism is locally constant in the morphism.
* `bijective_zeroLin_reflSingleModel_zero`, `exists_isModelContOrOn_reflDiag`,
  `isModelInvariant_reflDiag`, `exists_isModelOrientation_reflDiag`.
* **`reflDiag_isOrientable`**, **`reflDiag_exists_two_orientations`** (the two orientations
  `o ≠ −o` of `reflDiag_two_orientations`, with no hypothesis), and
  **`reflDiag_orPush_isotropy_eq`**: `g_* = Id` on `{(DET(f, 0), o), (DET(f, 0), −o)}`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v

open StrongRetr


section ConjBij

open TensorProduct

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The determinant isomorphism of a self-conjugation of an isomorphism is the identity**:
for a bijective `S` with `S ∘ A = Γ ∘ S`, `det(S) = λ(0) ⊗ λ*(0)` and `conjDet A Γ` is the
identity (the kernel and the cokernel are zero). -/
theorem conjDet_eq_refl_of_bijective (A : E ≃L[ℝ] E) (Γ : F ≃L[ℝ] F) {S : E →L[ℝ] F}
    (hS : Bijective S) (h : ∀ v, S (A v) = Γ (S v)) :
    conjDet A Γ h = LinearEquiv.refl ℝ _ := by
  have hker : Subsingleton (LinearMap.ker (S : E →ₗ[ℝ] F)) := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    have ha : S a = 0 := a.2
    have hb : S b = 0 := b.2
    exact hS.1 (ha.trans hb.symm)
  have hcok : Subsingleton (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) := by
    exact Submodule.Quotient.subsingleton_iff.2
      (LinearMap.range_eq_top.2 (show Surjective (S : E →ₗ[ℝ] F) from hS.2))
  have h1 : conjKerEquiv A Γ h = LinearEquiv.refl ℝ _ :=
    LinearEquiv.ext fun _ => Subsingleton.elim _ _
  have h2 : (conjCokerEquiv A Γ h).symm = LinearEquiv.refl ℝ _ :=
    LinearEquiv.ext fun _ => Subsingleton.elim _ _
  rw [conjDet, h1, h2, maxPowEquiv_refl, maxPowDualEquiv_refl, TensorProduct.congr_refl_refl]

/-- `conjDet` of a self-conjugation of an isomorphism fixes every ray of `det(S)`. -/
theorem ray_map_conjDet_of_bijective (A : E ≃L[ℝ] E) (Γ : F ≃L[ℝ] F) {S : E →L[ℝ] F}
    (hS : Bijective S) (h : ∀ v, S (A v) = Γ (S v)) (r : Module.Ray ℝ (fredholmDet S)) :
    Module.Ray.map (conjDet A Γ h) r = r := by
  rw [conjDet_eq_refl_of_bijective A Γ hS h, Module.Ray.map_refl]
  rfl

end ConjBij

section ChartLin

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x)

/-- **The linearization of a section at a zero, read in a chart point**:
`D(f̂ ∘ r)(z) : T_zO → K_z`. -/
def zeroLin (hg : B.IsScSmoothSection f) (hz : IsZeroAt P f x) : ↥p.T →L[ℝ] ↥p.K :=
  ((scDeriv p.c.U (p.c.principal f ∘ r p.c.R) p.z).comp p.T.subtypeL).codRestrict p.K
    fun v => p.scDeriv_mem_K hg hz v

/-- `zeroLin` is `D(f̂ ∘ r)(z)` on `T_zO`. -/
theorem coe_zeroLin_apply (hg : B.IsScSmoothSection f) (hz : IsZeroAt P f x) (v : ↥p.T) :
    (p.zeroLin hg hz v : p.c.F 0) = scDeriv p.c.U (p.c.principal f ∘ r p.c.R) p.z v := rfl

/-- **The linearization at a zero is a member of `Lin(f, x)`** (`s = 0`, `a = 0`). -/
theorem zeroLin_mem_linSet (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    (hz : IsZeroAt P f x) : p.zeroLin hf.isScSmooth hz ∈ p.linSet f := by
  have he := sectionAdd_fiberZero (P := P) hf.isScSmooth.1
  refine ⟨fiberZero P, StrongBundle.isScPlusSection_fiberZero, by rw [he]; exact hz, 0,
    p.isScPlusOp_zero hx,
    fun v => ?_⟩
  rw [coe_zeroLin_apply, linAt_apply, he]
  simp

variable {p} (p' : ChartPoint B x)

/-- **The linearizations at a zero in two chart points are conjugate** by the identifications
`transferT`, `transferK`. -/
theorem zeroLin_transferT (hg : B.IsScSmoothSection f) (hz : IsZeroAt P f x) (v : ↥p.T) :
    p'.zeroLin hg hz (p.transferT p' v) = p.transferK p' (p.zeroLin hg hz v) :=
  Subtype.ext (p.scDeriv_principal_baseDeriv p' hg hz v)

/-- **Bijectivity of the linearization at a zero does not depend on the chart point.** -/
theorem bijective_zeroLin_of_bijective (hg : B.IsScSmoothSection f) (hz : IsZeroAt P f x)
    (h : Bijective (p.zeroLin hg hz)) : Bijective (p'.zeroLin hg hz) := by
  have e : ⇑(p'.zeroLin hg hz) =
      ⇑(p.transferK p') ∘ ⇑(p.zeroLin hg hz) ∘ ⇑(p.transferT p').symm := by
    funext w
    have := zeroLin_transferT p' hg hz ((p.transferT p').symm w)
    rw [ContinuousLinearEquiv.apply_symm_apply] at this
    exact this
  rw [e]
  exact (p.transferK p').bijective.comp (h.comp (p.transferT p').symm.bijective)

end ChartPoint

namespace StrongBundle.LocalIso

variable {U U' : Set X} (L : LocalIso B B U U') {x x' : X} (a : ChartPoint B x)
  (ha : a.c.φ.source ⊆ U') (hx' : x' ∈ U) (hϕ : L.ϕ x' = x)

/-- **The linearization at a zero in a carried chart point is the one in the original chart
point**, for `f = Ψ ∘ f ∘ ϕ` on `U` (the principal parts agree, `principal_transportChart`). -/
theorem coe_zeroLin_pullPt (hfL : EqOn f (L.Ψ ∘ f ∘ L.ϕ) U) (hg : B.IsScSmoothSection f)
    (hz : IsZeroAt P f x) (hz' : IsZeroAt P f x') (w : ↥a.T) :
    ((L.pullPt a ha hx' hϕ).zeroLin hg hz' w).1 = (a.zeroLin hg hz w).1 := by
  change scDeriv a.c.U ((L.transportChart a.c ha).principal f ∘ r a.c.R) a.z w =
    scDeriv a.c.U (a.c.principal f ∘ r a.c.R) a.z w
  have h := scDeriv_congr a.c.relOpen.isScDomain (hg.isSc1_principal_comp_r a.isChart)
    (f' := (L.transportChart a.c ha).principal f ∘ r a.c.R)
    (fun u hu => (L.principal_transportChart a.c ha hfL hg.1 (a.c.r_mem_O hu)).symm) a.mem_U
  exact congrArg (fun T => T (w : a.c.φ.model.E 0)) h

end StrongBundle.LocalIso

end ChartLin

section Mor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

variable [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B) {f : Obj → W}
  (hF : E.IsScFredholmSectionFunctor f) (hsec : B.HasScPlusSectionsThrough)

include hF in
/-- **The linearization at a zero is equivariant**: for a morphism `σ : x → x'` between zeros of
an sc-Fredholm section functor, `f'(x') ∘ Tσ = μ(σ, ·) ∘ f'(x)` in the chosen chart points. -/
theorem zeroLin_morTx (σ : Mor) {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
    (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet) (hz : IsZeroAt P f x)
    (hz' : IsZeroAt P f x') (v : ↥(orPt B x hs).T) :
    (orPt B x' hs').zeroLin hF.2.isScSmooth hz' (E.morTx σ hx hx' hs hs' v) =
      E.morKx σ hx hx' hs hs' ((orPt B x hs).zeroLin hF.2.isScSmooth hz v) := by
  set a := restrPt B x (isOpen_srcSet σ) (mem_srcSet hx) hs
  set c' := (E.morIso σ).pullPt a (restrPt_sub _ _ _ _) (mem_tgtSet hx') (E.morIso_ϕ_eq hx hx')
  have hg := hF.2.isScSmooth
  change (orPt B x' hs').zeroLin hg hz' (c'.transferT (orPt B x' hs')
      ((orPt B x hs).transferT a v)) =
    c'.transferK (orPt B x' hs') ((orPt B x hs).transferK a ((orPt B x hs).zeroLin hg hz v))
  refine (ChartPoint.zeroLin_transferT (p := c') (orPt B x' hs') hg hz'
    ((orPt B x hs).transferT a v)).trans ?_
  congr 1
  refine Subtype.ext (((E.morIso σ).coe_zeroLin_pullPt a _ _ _ (E.eqOn_morIso_of_functor hF σ) hg
    hz hz' _).trans ?_)
  exact congrArg Subtype.val (ChartPoint.zeroLin_transferT (p := orPt B x hs) a hg hz v)

include hF in
/-- **An isotropy morphism at a transversal zero acts trivially on `Or_x^f`**: if `f(x) = 0`
and the linearization `f'(x)` is an isomorphism, every `σ : x → x` fixes both orientations of
`DET(f, x)`: `σ_*` is the conjugation by `Tσ`, `μ(σ, ·)` (`orMor_apply`), `f'(x)` is fixed by it
(`zeroLin_morTx`), and on `det(f'(x)) = λ(0) ⊗ λ*(0)` it is the identity. -/
theorem orMor_eq_self_of_bijective (σ : Mor) {x : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x)
    (hs : x ∈ X.PObj.smoothSet) (hz : IsZeroAt P f x)
    (hbij : Bijective ((orPt B x hs).zeroLin hF.2.isScSmooth hz)) (o : Orx f hF.2 x hs) :
    E.orMor hF hsec σ hx hx' hs hs o = o := by
  refine (E.orMor_apply hF hsec σ hx hx' hs hs o).trans ?_
  have hL := (orPt B x hs).zeroLin_mem_linSet hF.2 hs hz
  have h := fun v => E.zeroLin_morTx hF σ hx hx' hs hs hz hz v
  have : ContractibleSpace ((orPt B x hs).linSet f) :=
    ((orPt B x hs).convex_linSet hF.2).contractibleSpace ⟨_, hL⟩
  refine LineOrientation.eq_of_apply_eq ⟨_, hL⟩ ?_
  have hc := LineOrientation.conj_apply (hC := (orPt B x hs).isFredholm_of_mem_linSet hF.2)
    (hC' := (orPt B x hs).isFredholm_of_mem_linSet hF.2) (E.morTx σ hx hx' hs hs)
    (E.morKx σ hx hx' hs hs) (E.morTx_mem hF hsec σ hx hx' hs hs) o hL hL h
  exact hc.trans (ray_map_conjDet_of_bijective (E.morTx σ hx hx' hs hs)
    (E.morKx σ hx hx' hs hs) hbij h _)

end EpStrongBundle

end Mor

section Inv

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

namespace EpStrongBundle

variable (E : EpStrongBundle X B) {f : Obj → W} (hF : E.IsScFredholmSectionFunctor f)
  (hsec : B.HasScPlusSectionsThrough)

/-- **The invariance clause of Definition 12.5.4 at one morphism**: `σ_* o_{s(σ)} = o_{t(σ)}`. -/
def IsOrInvariantAt (o : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy) (σ : Mor) : Prop :=
  ∀ (hs : X.src σ ∈ X.PObj.smoothSet) (hs' : X.tgt σ ∈ X.PObj.smoothSet),
    E.orMor hF hsec σ rfl rfl hs hs' (o _ hs) = o _ hs'

/-- The invariance clause of Definition 12.5.4 holds iff it holds at every morphism. -/
theorem isOrInvariant_iff_forall_isOrInvariantAt
    {o : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy} :
    E.IsOrInvariant hF hsec o ↔ ∀ σ, E.IsOrInvariantAt hF hsec o σ := by
  refine ⟨fun h σ hs hs' => h σ rfl rfl hs hs', fun h σ x x' hx hx' hs hs' => ?_⟩
  subst hx hx'
  exact h σ hs hs'

/-- `IsOrInvariantAt` with arbitrary names for the source and the target. -/
theorem isOrInvariantAt_iff' {o : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy} {σ : Mor} :
    E.IsOrInvariantAt hF hsec o σ ↔ ∀ {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x')
      (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet),
      E.orMor hF hsec σ hx hx' hs hs' (o x hs) = o x' hs' := by
  refine ⟨fun h x x' hx hx' hs hs' => ?_, fun h hs hs' => h rfl rfl hs hs'⟩
  subst hx hx'
  exact h hs hs'

include hF in
/-- **An isotropy morphism at a transversal zero satisfies the invariance clause** for every
section `o` (`orMor_eq_self_of_bijective`). -/
theorem isOrInvariantAt_of_bijective (o : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy)
    (σ : Mor) {x : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x) (hs : x ∈ X.PObj.smoothSet)
    (hz : IsZeroAt P f x) (hbij : Bijective ((orPt B x hs).zeroLin hF.2.isScSmooth hz)) :
    E.IsOrInvariantAt hF hsec o σ := by
  refine (E.isOrInvariantAt_iff' hF hsec).2 fun hy hy' hs₁ hs₂ => ?_
  obtain rfl := hy.symm.trans hx
  obtain rfl := hy'.symm.trans hx'
  exact E.orMor_eq_self_of_bijective hF hsec σ hy hy' hs₁ hz hbij _

variable (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions)
  (hfT : B.IsScFredholmSectionTame f)
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]

/-- **The invariance at a morphism is locally constant in the morphism**, for a continuous
orientation `o` over all of `X` when every object is smooth: near `σ`, the morphisms are those of
the sheet of `σ`, and `σ'_* o_{s(σ')}` is the section carried by the local isomorphism of `σ`
(`pullOrx_morIso_eq_orMor`), a continuous orientation near `t(σ)` (Theorem 12.5.3); two continuous
orientations agree along a path iff they agree at one end. -/
theorem eventually_isOrInvariantAt_iff (hall : ∀ x, x ∈ X.PObj.smoothSet)
    {o : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy}
    (ho : IsContOrOn (orLocalTransport hX hbump hfT hsec) univ o) (σ : Mor) :
    ∀ᶠ σ' in 𝓝 σ, (E.IsOrInvariantAt hF hsec o σ' ↔ E.IsOrInvariantAt hF hsec o σ) := by
  have hiff : ∀ τ, E.IsOrInvariantAt hF hsec o τ ↔
      E.orMor hF hsec τ rfl rfl (hall _) (hall _) (o _ (hall _)) = o _ (hall _) :=
    fun τ => ⟨fun h => h _ _, fun h _ _ => h⟩
  obtain ⟨hC, -, hval⟩ := E.theorem_12_5_3_push_hyp hF hsec hX hbump hfT σ rfl rfl (hall _)
    (hall _) ho
  obtain ⟨V, hVo, hxV, hVN, hpath⟩ := exists_nhds_scPath_of_isOpen B hC.1
    (x := X.tgt σ) ⟨X.tgt_mem_sheetAt σ, mem_univ _⟩
  have hM : IsOpen ((X.sheetAt σ).carrier ∩ X.tgt ⁻¹' V) :=
    (X.sheetAt σ).isScDiffeoOn_tgt.isScSmoothOn.isOpen.inter (hVo.preimage X.continuous_tgt)
  filter_upwards [hM.mem_nhds ⟨X.mem_sheetAt σ, hxV⟩] with σ' hσ'
  obtain ⟨γ, hγ, h₀, h₁, hγN⟩ := hpath _ hxV _ hσ'.2 (hall _) (hall _)
  have e1 := hC.2 γ hγ (fun _ _ => hγN _) h₀ h₁ (hall _) (hall _)
  have e2 := ho.2 γ hγ (fun _ _ => mem_univ _) h₀ h₁ (hall _) (hall _)
  have hinv : (X.sheetAt σ).tgtInv (X.tgt σ') = σ' :=
    (X.sheetAt σ).isScDiffeoOn_tgt.left_inv σ' hσ'.1
  have k1 := E.pullOrx_morIso_eq_orMor hF hsec σ (hVN hσ'.2).1 (hall _) (hall _) o
  have key : ∀ (τ : Mor) (_ : τ = σ') {z : Obj} (hx : X.src τ = z)
      (hx' : X.tgt τ = X.tgt σ') (hs : z ∈ X.PObj.smoothSet)
      (hs' : X.tgt σ' ∈ X.PObj.smoothSet),
      E.orMor hF hsec τ hx hx' hs hs' (o z hs) =
        E.orMor hF hsec σ' rfl rfl (hall _) (hall _) (o _ (hall _)) := by
    rintro τ rfl z rfl hx' hs hs'
    rfl
  have T := ((orLocalTransport hX hbump hfT hsec).transport γ hγ h₀ h₁ (hall _)
    (hall _)).apply_eq_iff_eq (x := (E.morIso σ).pullOrx hF.2 hF.2 (E.eqOn_morIso_of_functor hF σ)
      hsec hsec o (X.tgt σ) (hall _)) (y := o _ (hall _))
  rw [e1, e2] at T
  have hB := k1.trans (key _ hinv (z := (E.morIso σ).ϕ (X.tgt σ')) rfl
    ((X.sheetAt σ).isScDiffeoOn_tgt.right_inv _ (hVN hσ'.2).1) (hall _) (hall _))
  refine (hiff σ').trans ((Iff.trans ?_ T).trans ?_)
  · rw [hB]
  · rw [hval]
    exact (hiff σ).symm

end EpStrongBundle

end Inv


namespace GCT.VectorBundle.ReflectionBundle

open GroupoidalCategory StrongPolyfoldBundleConstruction PolyfoldConstruction TrivialBundle
  EpGroupoid.Examples

/-- **The strong bundle model `W_Ψ̄ → X_Ψ` of one copy of `Ψ̄`**: `Σ _ : Unit, ℝ × ℝ` over
`Σ _ : Unit, ℝ`, with the morphisms `(q, (g, q), g q)`, `g = ±1`. -/
abbrev reflSingleModel : SEP.{0} := reflQ.modelSEP reflSingle.Ψ

example : reflSingleModel.B = StrongBundle.sigma (fun _ : Unit => TrivialBundle.bundle 1 1) := rfl

/-- **The translation chart `(x, v) ↦ (x − q, v)` at `(·, q)`**, pushed into the model, as a
chart point with `z = 0`. -/
def reflSingleChartPt (q : Fin 1 → ℝ) :
    ChartPoint reflSingleModel.B (⟨(), q⟩ : reflSingleModel.Obj) where
  c := StrongBundleChart.sigmaPush (PX := fun _ : Unit => rnPolyfold 1) (p := fun _ => proj 1 1)
    (i := ()) (TrivialBundle.chart (n := 1) (k := 1) q) (TrivialBundle.bundle 1 1).continuous
  isChart := StrongBundle.isChart_of_mem (B := reflSingleModel.B)
    (StrongBundle.sigmaPush_mem_sigma_atlas (B := fun _ : Unit => TrivialBundle.bundle 1 1)
      (i := ()) (mem_range_self q))
  mem_source := ⟨q, mem_univ _, rfl⟩
  z := 0
  toBase_z := by
    rw [map_zero]
    exact (sub_self q).symm.trans
      (MPolyfold.sigmaChart_apply (X := fun _ : Unit => Fin 1 → ℝ) () (rnChart 1 q) q).symm

/-- `T_0O = ℝ` in the translation chart point. -/
theorem reflSingleChartPt_T (q : Fin 1 → ℝ) : (reflSingleChartPt q).T = ⊤ := by
  change rangeS (scDeriv (TrivialBundle.chart (n := 1) (k := 1) q).U
    (r (TrivialBundle.chart (n := 1) (k := 1) q).R) 0) = ⊤
  rw [rangeS, scDeriv_r]
  exact LinearMap.range_id

/-- `K_0 = ℝ` in the translation chart point. -/
theorem reflSingleChartPt_K (q : Fin 1 → ℝ) : (reflSingleChartPt q).K = ⊤ :=
  eq_top_iff.2 fun h _ => ⟨h, rfl⟩

/-- **The principal part of `f^Ψ̄` in the translation chart at `q`** is `u ↦ u + q`
(`f_Ψ̄` is the graph section of the identity, `localRep_reflDiag`). -/
theorem principal_reflSingleChartPt (q : Fin 1 → ℝ) :
    (reflSingleChartPt q).c.principal (reflQ.modelSection reflSingle.Ψ reflDiag) =
      (fun u : Fin 1 → ℝ => u + q) := by
  funext u
  have h1 : (reflSingleChartPt q).c.φ.symm u =
      (⟨(), @id (Fin 1 → ℝ) u + q⟩ : reflSingleModel.Obj) := rfl
  have h2 : ∀ y : Fin 1 → ℝ, reflQ.modelSection reflSingle.Ψ reflDiag ⟨(), y⟩ =
      ⟨(), (y, y)⟩ := fun y => by
    change (⟨(), reflUnifData.localRep reflDiag y⟩ : reflSingleModel.W) = _
    rw [localRep_reflDiag]
    rfl
  have h3 : ∀ k : K, (reflSingleChartPt q).c ⟨(), k⟩ = (k.1 - q, k.2) := fun k =>
    StrongBundleChart.sigmaPush_apply (PX := fun _ : Unit => rnPolyfold 1)
      (p := fun _ => proj 1 1) (i := ()) _ _ k
  unfold StrongBundleChart.principal
  rw [h1, h2, h3]
  rfl

/-- `D(f̂ ∘ r)(0) = id` in the translation chart point. -/
theorem scDeriv_principal_reflSingleChartPt (q : Fin 1 → ℝ) :
    scDeriv (reflSingleChartPt q).c.U ((reflSingleChartPt q).c.principal
      (reflQ.modelSection reflSingle.Ψ reflDiag) ∘ r (reflSingleChartPt q).c.R) 0 =
      ContinuousLinearMap.id ℝ _ := by
  have e : (reflSingleChartPt q).c.principal (reflQ.modelSection reflSingle.Ψ reflDiag) ∘
      r (reflSingleChartPt q).c.R = (fun u : Fin 1 → ℝ => u + q) :=
    principal_reflSingleChartPt q
  rw [e]
  have := scDeriv_univ_const (V := Fin 1 → ℝ) (V' := Fin 1 → ℝ)
    (contDiff_id.add (contDiff_const (c := q))) 0
  rw [fderiv_add_const, fderiv_id] at this
  exact this

/-- `f^Ψ̄(·, 0) = 0`. -/
theorem isZeroAt_reflSingleModel_zero :
    IsZeroAt reflSingleModel.P (reflQ.modelSection reflSingle.Ψ reflDiag)
      (⟨(), (0 : Fin 1 → ℝ)⟩ : reflSingleModel.Obj) :=
  (reflQ.isZeroAt_modelSection_iff reflSingle.Ψ reflDiag _).2 rfl

/-- The linearization of `f^Ψ̄` at the zero `(·, 0)`, in the translation chart point, is the
identity of `ℝ`. -/
theorem zeroLin_reflSingleChartPt_apply (v : ↥(reflSingleChartPt 0).T) :
    ((reflSingleChartPt 0).zeroLin
      (reflQ.modelFred reflSingle.Ψ isScFredholmSectionFunctor_reflDiag).2.isScSmooth
      isZeroAt_reflSingleModel_zero v).1 = v.1 := by
  change scDeriv (reflSingleChartPt 0).c.U ((reflSingleChartPt 0).c.principal
      (reflQ.modelSection reflSingle.Ψ reflDiag) ∘ r (reflSingleChartPt 0).c.R) 0 v.1 = v.1
  rw [scDeriv_principal_reflSingleChartPt]
  rfl

/-- **The linearization of `f^Ψ̄` at its zero is an isomorphism** (translation chart point). -/
theorem bijective_zeroLin_reflSingleChartPt :
    Bijective ((reflSingleChartPt 0).zeroLin
      (reflQ.modelFred reflSingle.Ψ isScFredholmSectionFunctor_reflDiag).2.isScSmooth
      isZeroAt_reflSingleModel_zero) := by
  refine ⟨fun v w h => Subtype.ext ?_, fun k => ⟨⟨k.1, ?_⟩, Subtype.ext ?_⟩⟩
  · have := congrArg Subtype.val h
    rwa [zeroLin_reflSingleChartPt_apply, zeroLin_reflSingleChartPt_apply] at this
  · rw [reflSingleChartPt_T]; exact Submodule.mem_top
  · exact zeroLin_reflSingleChartPt_apply _

/-- Every object of the model is smooth. -/
theorem reflSingleModel_mem_smoothSet (x : reflSingleModel.Obj) :
    x ∈ reflSingleModel.X.PObj.smoothSet :=
  (reflQ.mem_smoothSet_model_iff' reflSingle x).2 (reflection_isSmoothObj _)


/-- **Two sc-smooth paths in `Σ _ : Unit, ℝ` with the same end points are sc-smoothly homotopic
with end points fixed** (the straight-line homotopy of `ℝ`, `scHomotopic_rn`). -/
theorem scHomotopic_reflSingleModel {γ₀ γ₁ : (Fin 1 → ℝ) → reflSingleModel.Obj}
    (h₀ : (rnPolyfold 1).IsScSmoothMap reflSingleModel.X.PObj γ₀)
    (h₁ : (rnPolyfold 1).IsScSmoothMap reflSingleModel.X.PObj γ₁) (hs : γ₀ (pt1 0) = γ₁ (pt1 0))
    (ht : γ₀ (pt1 1) = γ₁ (pt1 1)) : ScHomotopic reflSingleModel.X.PObj γ₀ γ₁ := by
  have g₀ : (rnPolyfold 1).IsScSmoothMap (rnPolyfold 1) fun t => (γ₀ t).2 :=
    (MPolyfold.isScSmoothMap_sigmaMk_comp_iff (fun _ : Unit => rnPolyfold 1) (i := ())
      (g := fun t => (γ₀ t).2)).1 h₀
  have g₁ : (rnPolyfold 1).IsScSmoothMap (rnPolyfold 1) fun t => (γ₁ t).2 :=
    (MPolyfold.isScSmoothMap_sigmaMk_comp_iff (fun _ : Unit => rnPolyfold 1) (i := ())
      (g := fun t => (γ₁ t).2)).1 h₁
  obtain ⟨Φ, hΦ⟩ := scHomotopic_rn g₀ g₁ (congrArg Sigma.snd hs) (congrArg Sigma.snd ht)
  exact ⟨Sigma.mk () ∘ Φ,
    ⟨(MPolyfold.isScSmoothMap_sigmaMk_comp_iff (fun _ : Unit => rnPolyfold 1)).2 hΦ.isScSmoothMap,
      fun t ht => congrArg (Sigma.mk ()) (hΦ.zero t ht),
      fun t ht => congrArg (Sigma.mk ()) (hΦ.one t ht),
      fun τ hτ => congrArg (Sigma.mk ()) (hΦ.start τ hτ),
      fun τ hτ => congrArg (Sigma.mk ()) (hΦ.finish τ hτ)⟩⟩

/-- **The path category of `Σ _ : Unit, ℝ` has at most one morphism between two points.** -/
theorem pathCat_hom_eq_reflSingleModel {x y : PathCat reflSingleModel.X.PObj} (a b : x ⟶ y) :
    a = b := by
  obtain ⟨φ, rfl⟩ := PathCat.exists_eq_mk a
  obtain ⟨ψ, rfl⟩ := PathCat.exists_eq_mk b
  exact PathCat.mk_eq_mk_iff.2 (scHomotopic_reflSingleModel φ.isScSmoothMap ψ.isScSmoothMap
    (φ.source.trans ψ.source.symm) (φ.target.trans ψ.target.symm))

/-- **The model section `f^Ψ̄` has a continuous orientation over all of `X_Ψ̄`**
(Theorem 6.6.17 and Definition 6.6.16: two paths of `X_Ψ̄` with the same end points are
homotopic, `exists_continuous_orSec_of_hom_eq`). -/
theorem exists_isModelContOrOn_reflDiag :
    ∃ o, reflQ.IsModelContOrOn isScFredholmSectionFunctor_reflDiag
      reflection_admitsModelBumpFunctions reflectionConstruction_isTame
      isScFredholmSectionFunctorTame_reflDiag reflSingle univ o := by
  have := paracompactSpace_rn_prod reflSingleModel.X.PObj
  have := paracompactSpace_rn_pullback reflSingleModel.B
  have := paracompactSpace_rn_rn_prod reflSingleModel.X.PObj
  have := paracompactSpace_rn_rn_pullback reflSingleModel.B
  obtain ⟨o, -, ho⟩ := exists_continuous_orSec_of_hom_eq
    (reflQ.modelTame reflSingle.Ψ reflectionConstruction_isTame)
    (reflQ.modelBump reflection_admitsModelBumpFunctions reflSingle)
    (reflQ.modelFredTame reflSingle.Ψ isScFredholmSectionFunctorTame_reflDiag)
    (reflQ.modelSec reflection_admitsModelBumpFunctions reflSingle) pathCat_hom_eq_reflSingleModel
  exact ⟨o, isContOrOn_univ_of_continuous_orSec
    (fun _ hy => exists_two_orx _ hy
      (reflQ.modelSec reflection_admitsModelBumpFunctions reflSingle))
    reflSingleModel.X.PObj.hasConnectedSmoothNbhds ho⟩

/-- The morphism `(q, (g, q), g q)` of `X_Ψ̄` (one copy of `Ψ̄`). -/
def reflMor (g : ℤˣ) (q : Fin 1 → ℝ) : reflSingleModel.Mor :=
  ⟨((), ()), twistHomeomorph isScSmoothMap_units_smul (TranslationTwist.refl ℤˣ (Fin 1 → ℝ))
    (g, q)⟩

/-- `q ↦ (q, (g, q), g q)` is continuous. -/
theorem continuous_reflMor (g : ℤˣ) : Continuous (reflMor g) :=
  continuous_sigmaMk.comp ((twistHomeomorph isScSmoothMap_units_smul
    (TranslationTwist.refl ℤˣ (Fin 1 → ℝ))).continuous.comp
      (continuous_const.prodMk continuous_id))

/-- The source of `(q, (g, q), g q)` is `q`. -/
theorem src_reflMor (g : ℤˣ) (q : Fin 1 → ℝ) : reflSingleModel.X.src (reflMor g q) = ⟨(), q⟩ := rfl

/-- The target of `(q, (g, q), g q)` is `g q`. -/
theorem tgt_reflMor (g : ℤˣ) (q : Fin 1 → ℝ) :
    reflSingleModel.X.tgt (reflMor g q) = ⟨(), g • q⟩ := rfl

/-- Every morphism of the model is `(q, (g, q), g q)`. -/
theorem eq_reflMor (m : reflSingleModel.Mor) : m = reflMor m.2.mor.1 m.2.mor.2 := by
  obtain ⟨⟨⟨⟩, ⟨⟩⟩, a⟩ := m
  exact congrArg (Sigma.mk ((), ())) ((twistHomeomorph isScSmoothMap_units_smul
    (TranslationTwist.refl ℤˣ (Fin 1 → ℝ))).apply_symm_apply a).symm

/-- **The linearization of `f^Ψ̄` at its zero is an isomorphism** in the chart point of
`Or_0` (`orPt`); bijectivity passes between chart points (`bijective_zeroLin_of_bijective`). -/
theorem bijective_zeroLin_reflSingleModel_zero
    (hs : (⟨(), (0 : Fin 1 → ℝ)⟩ : reflSingleModel.Obj) ∈ reflSingleModel.X.PObj.smoothSet) :
    Bijective ((orPt reflSingleModel.B _ hs).zeroLin
      (reflQ.modelFred reflSingle.Ψ isScFredholmSectionFunctor_reflDiag).2.isScSmooth
      isZeroAt_reflSingleModel_zero) :=
  (reflSingleChartPt 0).bijective_zeroLin_of_bijective _ _ _ bijective_zeroLin_reflSingleChartPt

/-- **Every continuous orientation of the model of `f` over all of `X_Ψ̄` is invariant.** -/
theorem isModelInvariant_reflDiag {o : reflQ.ModelOr isScFredholmSectionFunctor_reflDiag reflSingle}
    (ho : reflQ.IsModelContOrOn isScFredholmSectionFunctor_reflDiag
      reflection_admitsModelBumpFunctions reflectionConstruction_isTame
      isScFredholmSectionFunctorTame_reflDiag reflSingle univ o) :
    reflQ.IsModelInvariant isScFredholmSectionFunctor_reflDiag
      reflection_admitsModelBumpFunctions reflSingle o := by
  have := paracompactSpace_rn_prod reflSingleModel.X.PObj
  have := paracompactSpace_rn_pullback reflSingleModel.B
  have := paracompactSpace_rn_rn_prod reflSingleModel.X.PObj
  have := paracompactSpace_rn_rn_pullback reflSingleModel.B
  set hF := reflQ.modelFred reflSingle.Ψ isScFredholmSectionFunctor_reflDiag
  set hsec := reflQ.modelSec reflection_admitsModelBumpFunctions reflSingle
  refine (reflSingleModel.E.isOrInvariant_iff_forall_isOrInvariantAt hF hsec).2 fun m => ?_
  have hloc : ∀ g : ℤˣ, IsLocallyConstant fun q => reflSingleModel.E.IsOrInvariantAt hF hsec o
      (reflMor g q) := fun g => (IsLocallyConstant.iff_eventually_eq _).2 fun q => by
    have h := reflSingleModel.E.eventually_isOrInvariantAt_iff hF hsec
      (reflQ.modelTame reflSingle.Ψ reflectionConstruction_isTame)
      (reflQ.modelBump reflection_admitsModelBumpFunctions reflSingle)
      (reflQ.modelFredTame reflSingle.Ψ isScFredholmSectionFunctorTame_reflDiag)
      reflSingleModel_mem_smoothSet ho (reflMor g q)
    filter_upwards [(continuous_reflMor g).continuousAt.eventually h] with q' hq'
    exact propext hq'
  have h0 : ∀ g : ℤˣ, reflSingleModel.E.IsOrInvariantAt hF hsec o (reflMor g 0) := fun g =>
    reflSingleModel.E.isOrInvariantAt_of_bijective hF hsec o (reflMor g 0) (src_reflMor g 0)
      ((tgt_reflMor g 0).trans (by rw [smul_zero])) (reflSingleModel_mem_smoothSet _)
      isZeroAt_reflSingleModel_zero (bijective_zeroLin_reflSingleModel_zero _)
  rw [eq_reflMor m]
  have e := (hloc m.2.mor.1).apply_eq_of_preconnectedSpace m.2.mor.2 0
  exact e ▸ h0 m.2.mor.1

/-- **An orientation of the model section `f^Ψ̄`** (Definition 12.5.4 in the form of
`IsModelOrientation`). -/
theorem exists_isModelOrientation_reflDiag :
    ∃ o, reflQ.IsModelOrientation isScFredholmSectionFunctor_reflDiag
      reflection_admitsModelBumpFunctions reflectionConstruction_isTame
      isScFredholmSectionFunctorTame_reflDiag reflSingle o :=
  let ⟨o, ho⟩ := exists_isModelContOrOn_reflDiag
  ⟨o, isModelInvariant_reflDiag ho, ho⟩

/-- **The diagonal section `f(x) = (x, x)` of the reflection bundle is orientable**
(Definition 18.5.4, by Proposition 18.5.6 (1) in the model of one copy of `Ψ̄`), although the
isotropy `−1` of `0` acts on the fibre `μ(0) = ℝ` by `v ↦ −v`. -/
theorem reflDiag_isOrientable :
    reflQ.IsOrientable isScFredholmSectionFunctor_reflDiag reflection_admitsModelBumpFunctions
      reflectionConstruction_isTame isScFredholmSectionFunctorTame_reflDiag
      reflQ_hasStrongBundleUniformizers :=
  (reflQ.proposition_18_5_6_one_hyp _ _ _ _ _ reflSingle).2 exists_isModelOrientation_reflDiag

/-- **`f` has the two orientations `o` and `−o`** (p. 857), different over `0`. -/
theorem reflDiag_exists_two_orientations :
    ∃ o₁ o₂, reflQ.IsOrientation isScFredholmSectionFunctor_reflDiag
        reflection_admitsModelBumpFunctions reflectionConstruction_isTame
        isScFredholmSectionFunctorTame_reflDiag reflQ_hasStrongBundleUniformizers o₁ ∧
      reflQ.IsOrientation isScFredholmSectionFunctor_reflDiag
        reflection_admitsModelBumpFunctions reflectionConstruction_isTame
        isScFredholmSectionFunctorTame_reflDiag reflQ_hasStrongBundleUniformizers o₂ ∧
      o₁ 0 (reflection_isSmoothObj 0) ≠ o₂ 0 (reflection_isSmoothObj 0) :=
  reflDiag_two_orientations reflDiag_isOrientable

/-- **`g_* = Id` on `{(DET(f, 0), o), (DET(f, 0), −o)}`** for the isotropy `g = (−1, 0)` of `0`
(p. 857). -/
theorem reflDiag_orPush_isotropy_eq (ω : reflQ.DetOr isScFredholmSectionFunctor_reflDiag
    reflQ_hasStrongBundleUniformizers 0 (reflection_isSmoothObj 0)) :
    reflQ.orPush isScFredholmSectionFunctor_reflDiag reflection_admitsModelBumpFunctions
      reflQ_hasStrongBundleUniformizers (((-1 : ℤˣ), (0 : Fin 1 → ℝ)) : GCT.reflection.Mor) rfl
      (smul_zero _) (reflection_isSmoothObj 0) (reflection_isSmoothObj 0) ω = ω := by
  obtain ⟨o, ho⟩ := reflDiag_isOrientable
  set g := reflQ.orPush isScFredholmSectionFunctor_reflDiag reflection_admitsModelBumpFunctions
    reflQ_hasStrongBundleUniformizers (((-1 : ℤˣ), (0 : Fin 1 → ℝ)) : GCT.reflection.Mor) rfl
    (smul_zero _) (reflection_isSmoothObj 0) (reflection_isSmoothObj 0)
  have hfix : g (o 0 (reflection_isSmoothObj 0)) = o 0 (reflection_isSmoothObj 0) :=
    ho.1 _ rfl (smul_zero _) _ _
  obtain ⟨o₁, o₂, hne, hall⟩ := reflDiag_orPush_isotropy.1
  have two : ∀ u v t : reflQ.DetOr isScFredholmSectionFunctor_reflDiag
      reflQ_hasStrongBundleUniformizers 0 (reflection_isSmoothObj 0), u ≠ v → t = u ∨ t = v := by
    intro u v t huv
    rcases hall u with h1 | h1 <;> rcases hall v with h2 | h2 <;> rcases hall t with h3 | h3 <;>
      simp_all
  by_cases hω : ω = o 0 (reflection_isSmoothObj 0)
  · rw [hω, hfix]
  · have h1 : g ω ≠ o 0 (reflection_isSmoothObj 0) := fun h =>
      hω (g.injective (h.trans hfix.symm))
    exact (two (o 0 (reflection_isSmoothObj 0)) ω _ (Ne.symm hω)).resolve_left h1

end GCT.VectorBundle.ReflectionBundle

end Polyfold
