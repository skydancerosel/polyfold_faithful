import Polyfold.Chapter15.CylinderProductOrientation
import Polyfold.Chapter15.CanonicalOrientationStokes
import Polyfold.Chapter15.RelativeLocalFamilies
import Polyfold.Chapter15.CubeLiftScPlus
import Polyfold.Chapter6.IntervalProductIndex

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, pp. 701–703:
**Theorem 15.4.1** on the cylinder `[0, 1] × X` and **Corollary 15.4.4** (2017: Theorem 15.6,
Corollary 15.2).

# Corollary 15.4.4 for the canonical orientations

## The text, paraphrased

(p. 703) Let `(f, o)` be an oriented sc-Fredholm section functor and `Λ₀`, `Λ₁` regular
perturbations; `Θᵢ = Λᵢ ∘ f` carry their canonical orientations.  The regular perturbation `Λ̃`
of `f̃` on `[0, 1] × X` restricting to `Λᵢ` on the ends (Corollary 15.3.10 (3)) gives the
branched ep⁺-subgroupoid `Θ̃ = Λ̃ ∘ f̃`, which is canonically oriented by `(f̃, õ)`, `õ` the
orientation "`[0, 1]` first, then `o`", and `∂Θ̃ = Θ₁ ⊔ −Θ₀`; Stokes on `Θ̃` gives the
invariance of the integrals.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `isIndexAt_cubeLiftEp`: `f̃` has index `n + 1` at `(t, x)` if `f` has index `n` at `x`.
* `isOrInvariant_of_forall_unit`, `isOrInvariant_cubeOrientation_of_forall_unit`: the
  invariance of `õ` under the morphisms of the cylinder when all morphisms of `X` are units.
* **`theorem_15_4_1_cylinder`**: Theorem 15.4.1 for `(f̃, õ)` and a transversal sc⁺-multisection
  `Λ̃` on `[0, 1] × X` restricting to `Λ₀`, `Λ₁` on the ends, with the face condition of Theorem
  15.3.9 for the glued data: `canonicalOrientation Λ̃ õ` is the canonical orientation of
  `Θ̃ = Λ̃ ∘ f̃`, of dimension `m + 2`.
* `cylinderKernelFrameConvention_of_isIndexAt`: the frame convention on both ends for `õ`.
* **`corollary_15_4_4_cubeOrientation`**, **`corollary_15_4_4_eff_cubeOrientation`**: Corollary
  15.4.4 and its effective form with `Can = IsCanonicalPerturbation` (Definition 15.4.2), the
  hypotheses `hcont`, `hcont'`, `hcyl`, `hconv₀`, `hconv₁` of `corollary_15_4_4_of_canonical`
  being theorems.
* **`corollary_15_4_4_canonicalOrientation`**, **`corollary_15_4_4_eff_canonicalOrientation`**:
  the same with the relative step on the cylinder, the structurability of the glued boundary
  data and the face condition discharged.

## Reading

The index of `f` is `m + 1` at every smooth point (the text fixes the index of `f`; the forms
integrated have degree `m` and `m + 1`).  The invariance of `õ` under the morphisms
`(t, φ)` of the cylinder (the second clause of Definition 12.5.4 for `õ`) is the hypothesis
`hinvC`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP UnitCube

variable {A : SEP.{u}} {f : A.Obj → A.W}

/-! ### The index of `f̃` -/

/-- **The index of `f̃` on the cylinder**: if `f` has index `n` at the smooth point `x`, then
`f̃(t, x) = (t, f(x))` has index `n + 1` at `(t, x)`. -/
theorem isIndexAt_cubeLiftEp (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hsec : A.B.HasScPlusSectionsThrough) {x : A.Obj}
    (hxs : x ∈ A.X.PObj.smoothSet) {n : ℕ} (hi : A.B.IsIndexAt f x n)
    (t : Fin 1 → unitInterval) :
    (A.cubeSEP 1).B.IsIndexAt (cubeLiftEp (n := 1) f hf.1.1.1) (t, x) ((n + 1 : ℕ) : ℤ) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
    (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)
  have h := isIndexAt_cubeLift_interval hf.2 (hft.paramCube (n := 1)).toIsScFredholmSection hxs
    hsec hi t
  have e : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  rw [e]
  exact h

/-! ### The invariance of `õ` when all morphisms are units -/

/-- **Every family of orientations is invariant when all morphisms are units** (the second
clause of Definition 12.5.4 for an ep-groupoid with trivial morphisms, `1_*x = id`,
`orMor_unit`). -/
theorem isOrInvariant_of_forall_unit {g : A.Obj → A.W} (hF : A.E.IsScFredholmSectionFunctor g)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx g hF.2 y hy)
    (hunit : ∀ φ : A.Mor, φ = A.X.unit (A.X.src φ)) : A.E.IsOrInvariant hF hsec o := by
  intro φ x x' hx hx' hs hs'
  have hφ : φ = A.X.unit x := (hunit φ).trans (congrArg A.X.unit hx)
  subst hφ
  have hxx' : x = x' := (A.X.tgt_unit x).symm.trans hx'
  subst hxx'
  exact DFunLike.congr_fun (A.E.orMor_unit hF hsec rfl hx hx' hs) (o x hs)

/-- **`õ = e ∧ o` is invariant under the morphisms of the cylinder when all morphisms of `X` are
units** (for instance for the ep-groupoid of an M-polyfold). -/
theorem isOrInvariant_cubeOrientation_of_forall_unit (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hsec : A.B.HasScPlusSectionsThrough)
    (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (hunit : ∀ φ : A.Mor, φ = A.X.unit (A.X.src φ)) :
    (A.cubeSEP 1).E.IsOrInvariant (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft) hsec'
      (cubeOrientation hf hft hsec o) :=
  isOrInvariant_of_forall_unit _ hsec' _ fun φ => Prod.ext rfl (hunit φ.2)

/-! ### Theorem 15.4.1 on the cylinder -/

section Cylinder

variable (hd : ∀ x, A.X.PObj.degIndex x = 0) (hbump : A.X.PObj.AdmitsBumpFunctions)
  (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
  (ho : haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    IsSectionOrientation f hf.2 o)
  (hinvC : (A.cubeSEP 1).E.IsOrInvariant (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft)
    hsec' (cubeOrientation hf hft hsec o))
  {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))

include hd hbump ho hinvC hidx in
/-- **Theorem 15.4.1 (2021 p. 702; 2017: Theorem 15.6) for the cobordism** (2021 p. 703): let
`d_X ≡ 0`, `X` with sc-smooth bump functions, `(f, o)` an oriented sc-Fredholm section functor
with tame germ data of index `m + 1`, and `õ = e ∧ o` invariant under the morphisms of the
cylinder.  For a transversal sc⁺-multisection `Λ̃` on `[0, 1] × X` with `Λ̃ = Λᵢ` over `t = i` and
the face condition of Theorem 15.3.9 for the glued data, the formula of Theorem 15.4.1 for
`(f̃, õ)` defines the canonical orientation of `Θ̃ = Λ̃ ∘ f̃`, of dimension `m + 2`. -/
theorem theorem_15_4_1_cylinder {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (htr : IsTransversal (cubeLiftEp (n := 1) f hf.1.1.1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁)) :
    IsCanonicalFor Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
      (cubeOrientation hf hft hsec o) (m + 1 + 1)
      (canonicalOrientation Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
        (cubeOrientation hf hft hsec o)) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hbumpC : (A.cubeSEP 1).X.PObj.AdmitsBumpFunctions := admitsBumpFunctions_prod_cube hbump
  have hfC := isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  have hbd : ∀ w : (A.cubeSEP 1).W, (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary →
      Λ' w = cubeGlue Λ₀ Λ₁ w := fun w hw => by
    rcases (mem_boundary_cubeSEP_iff hX hd _).1 hw with h | h
    · exact (h0 w h).trans (cubeGlue_of_zero h).symm
    · exact (h1 w h).trans (cubeGlue_of_one h).symm
  have hgood : ∀ z ∈ (A.cubeSEP 1).X.PObj.boundary,
      0 < Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) →
        IsGoodPositionAt (cubeLiftEp (n := 1) f hf.1.1.1) Λ' z := fun z hz hpos =>
    isGoodPositionAt_of_isInGeneralPositionAt hfC hftC hΛ' hpos
      (isInGeneralPositionAt_of_isBoundaryFaceOnto hfC hftC hΛ' hbd honto hz hpos)
  have hidxC : ∀ z ∈ EpGroupoid.supp
      (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)),
      (A.cubeSEP 1).B.IsIndexAt (cubeLiftEp (n := 1) f hf.1.1.1) z ((m + 1 + 1 : ℕ) : ℤ) :=
    fun z hz => by
    have hpos : 0 < Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) := by exact_mod_cast hz
    have hzs : z ∈ (A.cubeSEP 1).X.PObj.smoothSet := mem_smoothSet_of_pos hftC hΛ' hpos
    have hxs : z.2 ∈ A.X.PObj.smoothSet := prod_cube_mem_smoothSet_iff.1 hzs
    exact isIndexAt_cubeLiftEp hf hft hsec hxs (hidx z.2 hxs) z.1
  exact theorem_15_4_1 hXC hbumpC hfC hftC hΛ' hsec' (cubeOrientation hf hft hsec o) hinvC
    (isSectionOrientation_cubeOrientation hX hbump hf hft ho)
    (isGoodPositionAt_of_transversal hfC hftC hΛ' htr hgood) hidxC

include hidx in
/-- **The frame convention of the canonical orientations holds for `õ = e ∧ o`** on every end,
when `f` has index `m + 1 ≥ 1` at every smooth point: the sheets of the local branching
structures described by kernels then have dimension `m + 1`
(`KernelBranching.dim_eq_of_isIndexAt`). -/
theorem cylinderKernelFrameConvention_of_isIndexAt (hbump : A.X.PObj.AdmitsBumpFunctions)
    (q : Fin 1 → unitInterval) :
    CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
      (cubeOrientation hf hft hsec o) q :=
  cylinderKernelFrameConvention_cubeOrientation hbump hf hft hsec hsec' o
    (fun _ x K i => by
      have hxs : x ∈ A.X.PObj.smoothSet := K.smooth i x (K.mem_M i)
      rw [K.dim_eq_of_isIndexAt hf.2 hsec (hidx x hxs) i]
      exact Nat.succ_pos m) q

/-! ### Corollary 15.4.4 -/

include hd hbump ho hinvC hidx in
/-- **Corollary 15.4.4 (2021 p. 703; 2017: Corollary 15.2) for the canonical orientations of
Definition 15.4.2.**  Let `d_X ≡ 0`, `|X|` paracompact, `X` with sc-smooth bump functions and
partitions of unity (also on `[0, 1] × X`; Stokes), `(f, o)` an oriented sc-Fredholm section
functor with compact solution set, tame germ data and index `m + 1`, and let the relative step
of Theorem 15.3.9 hold on the cylinder and the glued boundary data of two canonically oriented
regular perturbations be structurable with the face condition (`hglue`).  Then exact forms
integrate to `0` over every regular perturbation with the canonical orientation of `(f, o)`,
and a closed form has the same integral over any two of them.  The orientation of the cobordism
is the canonical one of `(f̃, õ)`, `õ = e ∧ o` (`theorem_15_4_1_cylinder`), the orientations of
the kernels are continuous along the sheets (`canonContinuous`), and the signs on the ends come
from `exists_timeFirst_frame_cubeOrientation`. -/
theorem corollary_15_4_4_cubeOrientation
    (hrelC : theorem_15_3_7_relative_statement (A.cubeSEP 1))
    (hpara : A.X.HasParacompactOrbitSpace) (hPU : A.X.HasScPartitionsOfUnity)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity)
    (hS : A.E.HasCompactSolutionSetEp f)
    (hglue : ∀ P₀ P₁ : OrientedRegularPerturbation A f m,
      IsCanonicalPerturbation hf.2 hsec o P₀ → IsCanonicalPerturbation hf.2 hsec o P₁ →
      IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue P₀.Λ P₁.Λ) ∧
        IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ)) :
    corollary_15_4_4_statement A f m (IsCanonicalPerturbation hf.2 hsec o) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hbumpC : (A.cubeSEP 1).X.PObj.AdmitsBumpFunctions := admitsBumpFunctions_prod_cube hbump
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  exact corollary_15_4_4_of_canonical (hf := hf) (hft := hft) (hsec' := hsec')
    (o' := cubeOrientation hf hft hsec o) hrelC hd hpara hPU hPUC hS hglue
    (fun Λ => canonContinuous Λ hX hbump hft hsec o ho)
    (fun Λ' => canonContinuous Λ' hXC hbumpC hftC hsec' (cubeOrientation hf hft hsec o)
      (isSectionOrientation_cubeOrientation hX hbump hf hft ho))
    (fun P₀ P₁ h₀ h₁ Λ' hreg e0 e1 => ⟨_, theorem_15_4_1_cylinder hd hbump hf hft hsec hsec' o ho
      hinvC hidx hreg.2.1.1 hreg.2.2.2.2 e0 e1 (hglue P₀ P₁ h₀ h₁).2⟩)
    (cylinderKernelFrameConvention_of_isIndexAt hf hft hsec hsec' o hidx hbump _)
    (cylinderKernelFrameConvention_of_isIndexAt hf hft hsec hsec' o hidx hbump _)

include hd hbump ho hinvC hidx in
/-- **Corollary 15.4.4, effective version (p. 703), for the canonical orientations of
Definition 15.4.2**: the effective form of `corollary_15_4_4_cubeOrientation`, with the local
unique continuation property on `X` and on `[0, 1] × X`. -/
theorem corollary_15_4_4_eff_cubeOrientation
    (hrelC : theorem_15_3_7_relative_statement (A.cubeSEP 1))
    (hpara : A.X.HasParacompactOrbitSpace) (hPU : A.X.HasScPartitionsOfUnity)
    (hLUC : A.X.IsLUC) (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) (hS : A.E.HasCompactSolutionSetEp f)
    (hglue : ∀ P₀ P₁ : OrientedRegularPerturbation A f m,
      IsCanonicalPerturbation hf.2 hsec o P₀ → IsCanonicalPerturbation hf.2 hsec o P₁ →
      IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue P₀.Λ P₁.Λ) ∧
        IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ)) :
    corollary_15_4_4_eff_statement A f m hLUC (IsCanonicalPerturbation hf.2 hsec o) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hbumpC : (A.cubeSEP 1).X.PObj.AdmitsBumpFunctions := admitsBumpFunctions_prod_cube hbump
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  exact corollary_15_4_4_eff_of_canonical (hf := hf) (hft := hft) (hsec' := hsec')
    (o' := cubeOrientation hf hft hsec o) hrelC hd hpara hPU hLUC hPUC hLUCC hS hglue
    (fun Λ => canonContinuous Λ hX hbump hft hsec o ho)
    (fun Λ' => canonContinuous Λ' hXC hbumpC hftC hsec' (cubeOrientation hf hft hsec o)
      (isSectionOrientation_cubeOrientation hX hbump hf hft ho))
    (fun P₀ P₁ h₀ h₁ Λ' hreg e0 e1 => ⟨_, theorem_15_4_1_cylinder hd hbump hf hft hsec hsec' o ho
      hinvC hidx hreg.2.1.1 hreg.2.2.2.2 e0 e1 (hglue P₀ P₁ h₀ h₁).2⟩)
    (cylinderKernelFrameConvention_of_isIndexAt hf hft hsec hsec' o hidx hbump _)
    (cylinderKernelFrameConvention_of_isIndexAt hf hft hsec hsec' o hidx hbump _)

include hd ho hinvC hidx in
/-- **Corollary 15.4.4 (2021 p. 703; 2017: Corollary 15.2).**  Let `d_X ≡ 0`, `|X|` paracompact,
`X` with sc-smooth partitions of unity (also on `[0, 1] × X`; they are used for Stokes), and let
`(f, o)` be an oriented sc-Fredholm section functor with compact solution set, tame germ data
and index `m + 1`, with `õ = e ∧ o` invariant under the morphisms of the cylinder.  Then exact
forms integrate to `0` over every regular perturbation with the canonical orientation of
`(f, o)` (Definition 15.4.2), and a closed form has the same integral over any two of them.
The relative step of Theorem 15.3.9 on the cylinder is `theorem_15_3_7_relative`, the glued
boundary data are structurable (`isBoundaryStructurable_cubeGlue`) and satisfy the face
condition (`isBoundaryFaceOnto_cubeGlue`), and the bump functions come from the partitions of
unity. -/
theorem corollary_15_4_4_canonicalOrientation (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity)
    (hS : A.E.HasCompactSolutionSetEp f) :
    corollary_15_4_4_statement A f m (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_cubeOrientation hd
    (A.X.theorem_12_3_2_1.1 (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPU))
    hf hft hsec hsec' o ho hinvC hidx theorem_15_3_7_relative hpara hPU hPUC hS fun P₀ P₁ _ _ =>
      ⟨isBoundaryStructurable_cubeGlue hd hpara P₀.isRegular.2.1 P₁.isRegular.2.1,
        isBoundaryFaceOnto_cubeGlue hd hf hft P₀.isRegular.2.2.2.2 P₁.isRegular.2.2.2.2⟩

include hd ho hinvC hidx in
/-- **Corollary 15.4.4, effective version (p. 703)**: the effective form of
`corollary_15_4_4_canonicalOrientation`, with the local unique continuation property on `X` and
on `[0, 1] × X`. -/
theorem corollary_15_4_4_eff_canonicalOrientation (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity) (hLUCC : (A.cubeSEP 1).X.IsLUC)
    (hS : A.E.HasCompactSolutionSetEp f) :
    corollary_15_4_4_eff_statement A f m hLUC (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_eff_cubeOrientation hd
    (A.X.theorem_12_3_2_1.1 (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPU))
    hf hft hsec hsec' o ho hinvC hidx theorem_15_3_7_relative hpara hPU hLUC hPUC hLUCC hS
    fun P₀ P₁ _ _ =>
      ⟨isBoundaryStructurable_cubeGlue hd hpara P₀.isRegular.2.1 P₁.isRegular.2.1,
        isBoundaryFaceOnto_cubeGlue hd hf hft P₀.isRegular.2.2.2.2 P₁.isRegular.2.2.2.2⟩

end Cylinder

end SBLocalization

end Polyfold
