import Polyfold.Chapter15.CylinderEnds
import Polyfold.Chapter15.ChargedExtensionCylinder
import Polyfold.Chapter9.EffectiveDimOneLUC

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2) through the cylinder cobordism of
**Corollary 15.3.10 (3)** (p. 699), in the order of the text's argument, and its effective
version (gap TX-6, in part).

# Corollary 15.4.4 from the cylinder `[0, 1] × X`

## The text's argument, paraphrased (proof "left to the reader")

(a) Two regular perturbations `(Nⁱ, Uⁱ, Λⁱ)` of `f` with `Θᵢ = Λⁱ ∘ f` (Corollary 15.3.10 (1)).
(b) Theorem 15.3.9 on `[0, 1] × X` gives `Λ̃` with `Λ̃ = Λⁱ` over `{i} × X`, and `Θ̃ = Λ̃ ∘ f̃` is
    a compact branched cobordism between `Θ₀` and `Θ₁` (Corollary 15.3.10 (3)).
(c) `Θ̃` carries the canonical orientation from `(f̃, õ)` (Theorem 15.4.1 on the cylinder), and
    with the induced boundary orientation (Definition 9.3.10) `∂Θ̃ = Θ₁ ⊔ −Θ₀`.
(d) Stokes (Theorem 15.4.3) on `Θ̃` for `pr^*ω`, `ω` closed: `∫_{Θ₁} ω − ∫_{Θ₀} ω = 0`; exact
    forms integrate to `0` over each `Θᵢ` since `∂Θᵢ = 0` (`d_X ≡ 0`).

## What is formalized (namespace `Polyfold.SBLocalization`)

* (b): `corollary_15_3_10_3_charged` (`ChargedExtensionCylinder`; Theorem 15.3.9 on the cylinder
  in its charged form as `h159`, since TX's uncharged form fails there for nonempty `X`; TY-2's
  two hypotheses on the glued data and TY-3's partitions of unity remain).  The restriction of `Θ̃`
  to the ends and `∂X̃ ∩ supp Θ̃ = {0} × supp Θ₀ ∪ {1} × supp Θ₁` are proved in
  `CylinderEnds`.
* (c), the boundary identification: `μ^{∂Θ̃}(∂S) = μ^{∂Θ̃}(end 0) + μ^{∂Θ̃}(end 1)` is proved
  (`boundaryMeasure_cyl_univ`); what is left is **`IsCylinderBoundaryOf`**: on the end `1` the
  boundary measure of `pr^*ω` is `∫_{Θ₁} ω`, on the end `0` it is `−∫_{Θ₀} ω`.
  **`CylinderOrientationStatement`** asks for an orientation of `Θ̃` (Theorem 15.4.1 on the
  cylinder) with this property, for every `Λ̃` that (b) can produce.
* **`hasOrientedCobordism_of_cylinder`**: (c) gives TX's `HasOrientedCobordism` with `Y` the
  cylinder and `F` the projection.  **`hasOrientedCobordism_cylinder_hyp`**: (b) + (c).
* **`corollary_15_4_4_cylinder_hyp`**: Corollary 15.4.4 from (b) and (c), through TX's
  `corollary_15_4_4_hyp` (step (d)).
* The effective version (p. 703): `OrientedRegularPerturbation.integralEff`,
  `HasOrientedCobordismEff`, `integralEff_eq_of_cobordism` (Theorem 9.5.18 on `Y`),
  `hasOrientedCobordismEff_refl`, **`corollary_15_4_4_eff_statement`**,
  **`corollary_15_4_4_eff_hyp`**, `IsCylinderBoundaryEffOf`, `hasOrientedCobordismEff_of_cylinder`,
  **`corollary_15_4_4_eff_cylinder_hyp`**.

## Reading

* `Φ_{(f,o)}` on `H*_dR(X)` is read degree-wise as in TX (exact forms give `0`, closed forms have
  equal integrals), in the degree `m + 1 = dim Θ`, `m + 1 ≥ 1`.
* "`∂Θ̃ = Θ₁ ⊔ −Θ₀`" is read on the level of the boundary measure of Theorem 9.5.15, which is
  what Stokes uses: the end identities of `IsCylinderBoundaryOf`.
* The canonical orientation is a parameter `Can` (as in TX); `CylinderOrientationStatement`
  asks only for the properties of the canonical orientation of `Θ̃` that the argument uses.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

/-! ### Step (c): the oriented boundary identification, as a proposition -/

/-- **`∂Θ̃ = Θ₁ ⊔ −Θ₀` on the level of the boundary measure** (proof of Corollary 15.4.4,
pp. 700, 703): for `Θ̃` compact, branched, oriented and tame of dimension `m + 2` on
`[0, 1] × X`, the boundary measure (Theorem 9.5.15) of `pr^*ω` is `∫_{P₁} ω` on the end
`t = 1` and `−∫_{P₀} ω` on the end `t = 0` (outward normal `+∂_t` at `t = 1`, `−∂_t` at
`t = 0`, Definition 9.3.10). -/
def IsCylinderBoundaryOf {f : A.Obj → A.W} {m : ℕ} (P₀ P₁ : OrientedRegularPerturbation A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T') : Prop :=
  ∀ ω : A.baseEP.epFormsInfty (m + 1),
    (A.cubeSEP 1).baseEP.boundaryMeasure (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
        (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω) (cylEnd (X := A.X) Θ' 1) =
      P₁.integral ω ∧
    (A.cubeSEP 1).baseEP.boundaryMeasure (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
        (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω) (cylEnd (X := A.X) Θ' 0) =
      -P₀.integral ω

/-- **Step (c) gives TX's cobordism**: for `d_X ≡ 0` and `[0, 1] × X` with sc-smooth partitions
of unity, a compact oriented tame `Θ̃` of dimension `m + 2` on the cylinder with the end
identities joins `P₀` and `P₁` (`Y = [0, 1] × X`, `F = pr`); the boundary measure splits over
the two ends (`boundaryMeasure_cyl_univ`). -/
theorem hasOrientedCobordism_of_cylinder (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hPUC : (A.cubeSEP 1).X.HasScPartitionsOfUnity) {f : A.Obj → A.W} {m : ℕ}
    {P₀ P₁ : OrientedRegularPerturbation A f m}
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    (hends : IsCylinderBoundaryOf P₀ P₁ hΘ' hcpt' hT' hloc') :
    P₀.HasOrientedCobordism P₁ := by
  refine ⟨(A.cubeSEP 1).baseEP, A.X.cubeProj 1, hPUC, Θ', T', hΘ', hcpt', hT', hloc',
    fun ω => ?_⟩
  rw [boundaryMeasure_cyl_univ hd (Nat.succ_pos m) hΘ' hcpt' hT' hloc', (hends ω).1,
    (hends ω).2]
  ring

/-- **Step (c) as a proposition about the perturbations step (b) produces**: every structurable
regular perturbation `(Ñ, Ũ, Λ̃)` of `f̃` on `[0, 1] × X` (with `Ñ`, `Ũ` TY's interpolations)
with `Λ̃ = Λⁱ` over `{i} × X` and `Θ̃ = Λ̃ ∘ f̃` compact and branched carries an orientation
`T̃` (in the text: the canonical one from `(f̃, õ)`, Theorem 15.4.1), described by oriented tame
structures of dimension `m + 2`, with the end identities `IsCylinderBoundaryOf`. -/
def CylinderOrientationStatement {f : A.Obj → A.W} (hf : IsSection A.P f) {m : ℕ}
    (P₀ P₁ : OrientedRegularPerturbation A f m) : Prop :=
  ∀ Λ' : (A.cubeSEP 1).W → ℚ≥0,
    IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf)
      (interpAuxNorm A P₀.N P₁.N) (interpSet A P₀.U P₁.U) Λ' →
    (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = P₀.Λ (cubeVal w).2) →
    (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = P₁.Λ (cubeVal w).2) →
    ∀ (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)))
      (hcpt' : (A.cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ))),
    ∃ (T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ)
      (hT' : (A.cubeSEP 1).X.IsOrientation (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) T')
      (hloc' : ∀ x ∈ EpGroupoid.supp (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)),
        ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1)
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) x, C.Represents T'),
      IsCylinderBoundaryOf P₀ P₁ hΘ' hcpt' hT' hloc'

/-- `[0, 1] × X` has sc-smooth partitions of unity in the sense of Definition 7.5.5 if its
object M-polyfold admits them and `|X|` is paracompact (Theorem 7.5.7, with TY's
`hasParacompactOrbitSpace_cubeProd`). -/
theorem hasScPartitionsOfUnity_cyl (hpara : A.X.HasParacompactOrbitSpace)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity) :
    (A.cubeSEP 1).X.HasScPartitionsOfUnity :=
  (A.cubeSEP 1).X.theorem_7_5_7 (A.X.hasParacompactOrbitSpace_cubeProd 1 hpara) hPUC

/-- **Steps (b) and (c): the cobordism between two oriented regular perturbations**
(Corollary 15.3.10 (3), Corollary 15.4.4).  For `d_X ≡ 0`, `|X|` paracompact, `f` sc-Fredholm
with tame germ data and compact `|S_f|`: if Theorem 15.3.9 (charged form) holds on `[0, 1] × X`
(`h159`, R6's form; `theorem_15_3_9_charged_hyp` gives it from TX-2) with tame strong bundle
charts there (`hBC`), the
cylinder's object M-polyfold has sc-smooth partitions of unity (`hPUC`; TY-3), the glued data
are structurable and satisfy the face condition (`hbs`, `hbonto`; TY-2), and step (c) holds
(`hor`), then `P₀` and `P₁` are joined by an oriented compact cobordism. -/
theorem hasOrientedCobordism_cylinder_hyp
    (h159 : theorem_15_3_9_charged_statement (A.cubeSEP 1))
    (hBC : ∀ x : (A.cubeSEP 1).Obj,
      ∃ c : StrongBundleChart (A.cubeSEP 1).X.PObj (A.cubeSEP 1).P,
        (A.cubeSEP 1).B.IsTameChart c ∧ x ∈ c.φ.source)
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ} (P₀ P₁ : OrientedRegularPerturbation A f m)
    (hbs : IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue P₀.Λ P₁.Λ))
    (hbonto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (hor : CylinderOrientationStatement hf.1.1.1 P₀ P₁) :
    P₀.HasOrientedCobordism P₁ := by
  obtain ⟨Λ', hreg, h0, h1, hΘ', hcpt'⟩ := corollary_15_3_10_3_charged h159 hBC hd hpara hPUC hf
    hft hS P₀.isRegular P₁.isRegular hbs hbonto
  obtain ⟨T', hT', hloc', hends⟩ := hor Λ' hreg h0 h1 hΘ' hcpt'
  exact hasOrientedCobordism_of_cylinder hd (hasScPartitionsOfUnity_cyl hpara hPUC) hΘ' hcpt' hT'
    hloc' hends

/-- **Corollary 15.4.4 (2017: Corollary 15.2), p. 703, along the text's argument**: for
`d_X ≡ 0`, `|X|` paracompact, `X` with sc-smooth partitions of unity (Stokes), `f` sc-Fredholm
with tame germ data and compact `|S_f|`, and a predicate `Can` (the canonical orientation from
`(f, o)`), `Φ_{(f,o)}` is well defined in degree `m + 1` if Theorem 15.3.9 holds on
`[0, 1] × X`, the cylinder has partitions of unity, and for any two `Can`-perturbations the
glued boundary data satisfy TY-2's two conditions and step (c) holds. -/
theorem corollary_15_4_4_cylinder_hyp
    (h159 : theorem_15_3_9_charged_statement (A.cubeSEP 1))
    (hBC : ∀ x : (A.cubeSEP 1).Obj,
      ∃ c : StrongBundleChart (A.cubeSEP 1).X.PObj (A.cubeSEP 1).P,
        (A.cubeSEP 1).B.IsTameChart c ∧ x ∈ c.φ.source)
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity)
    {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    (Can : OrientedRegularPerturbation A f m → Prop)
    (hglue : ∀ P₀ P₁, Can P₀ → Can P₁ →
      IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue P₀.Λ P₁.Λ) ∧
        IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (hor : ∀ P₀ P₁, Can P₀ → Can P₁ → CylinderOrientationStatement hf.1.1.1 P₀ P₁) :
    corollary_15_4_4_statement A f m Can :=
  corollary_15_4_4_hyp hPU hd Can fun P₀ P₁ h₀ h₁ =>
    hasOrientedCobordism_cylinder_hyp h159 hBC hd hpara hPUC hf hft hS P₀ P₁
      (hglue P₀ P₁ h₀ h₁).1 (hglue P₀ P₁ h₀ h₁).2 (hor P₀ P₁ h₀ h₁)

/-- **Corollary 15.4.4 with Theorem 15.3.9 on the cylinder reduced** (R6's
`theorem_15_3_9_charged_hyp`):
what is left is tame strong bundle charts on `[0, 1] × X` (`hBC`), the relative general position
step there (`hrelC`, TX-2), partitions of unity on the cylinder (`hPUC`, TY-3), the two
conditions on the glued data (`hglue`, TY-2) and step (c) (`hor`). -/
theorem corollary_15_4_4_cylinder_of_rel
    (hBC : ∀ x : (A.cubeSEP 1).Obj,
      ∃ c : StrongBundleChart (A.cubeSEP 1).X.PObj (A.cubeSEP 1).P,
        (A.cubeSEP 1).B.IsTameChart c ∧ x ∈ c.φ.source)
    (hrelC : theorem_15_3_7_relative_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    (Can : OrientedRegularPerturbation A f m → Prop)
    (hglue : ∀ P₀ P₁, Can P₀ → Can P₁ →
      IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue P₀.Λ P₁.Λ) ∧
        IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (hor : ∀ P₀ P₁, Can P₀ → Can P₁ → CylinderOrientationStatement hf.1.1.1 P₀ P₁) :
    corollary_15_4_4_statement A f m Can :=
  corollary_15_4_4_cylinder_hyp (theorem_15_3_9_charged_hyp hrelC) hBC hd hpara hPU hPUC hf hft
    hS Can hglue hor

/-! ### The effective version (p. 703) -/

/-- The effective branched integral of the zero form is `0`. -/
theorem tameBranchedIntegralEff_zero {B : EP.{u}} {n : ℕ} (hn : 0 < n) {Θ : B.Obj → ℚ}
    {T : B.Obj → B.X.PObj.OrTangent →₀ ℚ} (hΘ : B.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : B.X.IsCompactBranched Θ) (hT : B.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ EpGroupoid.supp Θ,
      ∃ C : B.X.OrientedTameStructure n Θ x, C.Represents T ∧ C.rep.HasLUC) :
    (B.epFormsInftyEval n).tameBranchedIntegralEff hn hΘ hcpt hT hloc 0 = 0 := by
  simp only [FormEval.tameBranchedIntegralEff, FormEval.concreteBranchedIntegralEff,
    branchedIntegralEff, map_zero]
  rfl

/-- **The effective cobordism argument** (Corollary 15.4.4, effective version): as TX's
`integral_eq_of_cobordism`, with `Y` having the local unique continuation property and the
effective boundary measure (Theorems 9.5.16, 9.5.18). -/
theorem integralEff_eq_of_cobordism {X Y : EP.{u}} (F : EpFunctor Y.X X.X) {m : ℕ}
    (hPU : Y.X.HasScPartitionsOfUnity) (hLUC : Y.X.IsLUC) {Θ' : Y.Obj → ℚ}
    {T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    (I₀ I₁ : X.epFormsInfty (m + 1) → ℝ)
    (hbd : ∀ ω, Y.boundaryMeasureEff (Nat.succ_pos m) hLUC hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F (m + 1) ω) univ = I₁ ω - I₀ ω)
    (ω : X.epFormsInfty (m + 1)) (hω : X.epFormsInftyD (m + 1) ω = 0) : I₀ ω = I₁ ω := by
  have hS := Y.theorem_9_5_18 (Nat.succ_pos m) hPU hLUC hΘ' hcpt' hT' hloc'
    (EP.epFormsInftyPullback F (m + 1) ω)
  have hd : Y.epFormsInftyD (m + 1) (EP.epFormsInftyPullback F (m + 1) ω) = 0 := by
    have := LinearMap.congr_fun (EP.epFormsInftyD_comp_epFormsInftyPullback F (m + 1)) ω
    simp only [LinearMap.comp_apply] at this
    rw [this, hω, map_zero]
  rw [hd, tameBranchedIntegralEff_zero, hbd] at hS
  linarith

namespace OrientedRegularPerturbation

variable {f : A.Obj → A.W} {m : ℕ}

/-- `∮_{(Λ ∘ f, o)} ω` for `ω ∈ Ω^{m+1}_{ep,∞}(X)`, `X` with the local unique continuation
property (Definition 9.5.6 (2)). -/
def integralEff (hLUC : A.X.IsLUC) (P : OrientedRegularPerturbation A f m)
    (ω : A.baseEP.epFormsInfty (m + 1)) : ℝ :=
  (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) P.isBranched
    P.isCompact P.isOrientation (A.baseEP.hloc_hasLUC hLUC P.loc) ω

/-- `P₀` and `P₁` are joined by an **oriented compact cobordism for the effective integral**:
as `HasOrientedCobordism`, with `Y` having the local unique continuation property and the
effective boundary measure. -/
def HasOrientedCobordismEff (hLUC : A.X.IsLUC) (P₀ P₁ : OrientedRegularPerturbation A f m) :
    Prop :=
  ∃ (Y : EP.{u}) (F : EpFunctor Y.X A.baseEP.X) (_ : Y.X.HasScPartitionsOfUnity)
    (hLUCY : Y.X.IsLUC) (Θ' : Y.Obj → ℚ) (T' : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ)
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.X.IsCompactBranched Θ')
    (hT' : Y.X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : Y.X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T'),
    ∀ ω, Y.boundaryMeasureEff (Nat.succ_pos m) hLUCY hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback F (m + 1) ω) univ = P₁.integralEff hLUC ω - P₀.integralEff hLUC ω

/-- **The effective cobordism hypothesis is satisfiable**: every oriented regular perturbation
is cobordant to itself (`Y = X`, `F = id`, `Θ̃ = 0`), for `X` with partitions of unity and the
local unique continuation property. -/
theorem hasOrientedCobordismEff_refl (hPU : A.X.HasScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    (P : OrientedRegularPerturbation A f m) : HasOrientedCobordismEff hLUC P P := by
  have hemp : ∀ x, x ∉ A.X.PObj.boundary ∩ EpGroupoid.supp (0 : A.Obj → ℚ) := fun x hx =>
    lt_irrefl (0 : ℚ) hx.2
  have hcpt0 : A.X.IsCompactBranched (0 : A.Obj → ℚ) := by
    have : A.X.orbitSupp (0 : A.Obj → ℚ) = ∅ := by
      rw [orbitSupp, image_eq_empty, eq_empty_iff_forall_notMem]
      exact fun x hx => lt_irrefl (0 : ℚ) hx
    rw [IsCompactBranched, this]; exact isCompact_empty
  have hloc0 : ∀ x ∈ EpGroupoid.supp (0 : A.Obj → ℚ),
      ∃ C : A.X.OrientedTameStructure (m + 1 + 1) 0 x, C.Represents fun _ => 0 :=
    fun x hx => absurd hx (lt_irrefl (0 : ℚ))
  refine ⟨A.baseEP, EpFunctor.id _, hPU, hLUC, 0, fun _ => 0, A.X.isBranchedEpSubgroupoid_zero,
    hcpt0, A.X.isOrientation_zero, hloc0, fun ω => ?_⟩
  rw [sub_self]
  exact signedMeasure_univ_eq_zero_of_boundary hemp _

end OrientedRegularPerturbation

variable (A) in
/-- **Corollary 15.4.4, effective version, p. 703**, as a proposition, degree-wise in degree
`m + 1`, for `X` with the local unique continuation property:
`Φ^eff_{(f,o)}([ω]) = ∮_{(Λ ∘ f, o)} ω` is well defined: exact forms give `0` over every
`Can`-perturbation, closed forms have the same effective integral over any two. -/
def corollary_15_4_4_eff_statement (f : A.Obj → A.W) (m : ℕ) (hLUC : A.X.IsLUC)
    (Can : OrientedRegularPerturbation A f m → Prop) : Prop :=
  (∀ P, Can P → ∀ η : A.baseEP.epFormsInfty m,
    P.integralEff hLUC (A.baseEP.epFormsInftyD m η) = 0) ∧
  ∀ P₀ P₁, Can P₀ → Can P₁ → ∀ ω : A.baseEP.epFormsInfty (m + 1),
    A.baseEP.epFormsInftyD (m + 1) ω = 0 → P₀.integralEff hLUC ω = P₁.integralEff hLUC ω

/-- For `d_X ≡ 0` and the local unique continuation property, exact forms have effective
integral `0` over every oriented regular perturbation (Theorem 9.5.18 and its dimension-1 form;
`∂Θ = 0`). -/
theorem integralEff_d_eq_zero_of_degIndex_eq_zero (hPU : A.X.HasScPartitionsOfUnity)
    (hLUC : A.X.IsLUC) (hd : ∀ x, A.X.PObj.degIndex x = 0) {f : A.Obj → A.W} {m : ℕ}
    (P : OrientedRegularPerturbation A f m) (η : A.baseEP.epFormsInfty m) :
    P.integralEff hLUC (A.baseEP.epFormsInftyD m η) = 0 := by
  have hemp : ∀ x, x ∉ A.X.PObj.boundary ∩ EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)) :=
    fun x hx => by
      have h1 : 1 ≤ A.X.PObj.degIndex x := hx.1
      rw [hd x] at h1
      exact absurd h1 (by norm_num)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have e := A.baseEP.theorem_9_5_18_dim1_isLUC hPU hLUC P.isBranched P.isCompact
      P.isOrientation P.loc η
    refine e.trans ?_
    exact signedMeasure_univ_eq_zero_of_boundary hemp _
  · have e := A.baseEP.theorem_9_5_18 hm hPU hLUC P.isBranched P.isCompact P.isOrientation
      P.loc η
    refine e.trans ?_
    exact signedMeasure_univ_eq_zero_of_boundary hemp _

/-- **Corollary 15.4.4, effective version, from the effective cobordism**: for `d_X ≡ 0`, `X`
with partitions of unity and the local unique continuation property, the statement holds for
every `Can` whose perturbations are pairwise joined by `HasOrientedCobordismEff`. -/
theorem corollary_15_4_4_eff_hyp {f : A.Obj → A.W} {m : ℕ}
    (hPU : A.X.HasScPartitionsOfUnity) (hLUC : A.X.IsLUC) (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (Can : OrientedRegularPerturbation A f m → Prop)
    (hcob : ∀ P₀ P₁, Can P₀ → Can P₁ → P₀.HasOrientedCobordismEff hLUC P₁) :
    corollary_15_4_4_eff_statement A f m hLUC Can := by
  refine ⟨fun P _ η => integralEff_d_eq_zero_of_degIndex_eq_zero hPU hLUC hd P η,
    fun P₀ P₁ h₀ h₁ ω hω => ?_⟩
  obtain ⟨Y, F, hPUY, hLUCY, Θ', T', hΘ', hcpt', hT', hloc', hbd⟩ := hcob P₀ P₁ h₀ h₁
  exact integralEff_eq_of_cobordism F hPUY hLUCY hΘ' hcpt' hT' hloc' (P₀.integralEff hLUC)
    (P₁.integralEff hLUC) hbd ω hω

/-- **Step (c), effective form**: the effective boundary measure (Theorem 9.5.16) of `pr^*ω` is
`∮_{P₁} ω` on the end `t = 1` and `−∮_{P₀} ω` on the end `t = 0`. -/
def IsCylinderBoundaryEffOf {f : A.Obj → A.W} {m : ℕ} (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) (P₀ P₁ : OrientedRegularPerturbation A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T') : Prop :=
  ∀ ω : A.baseEP.epFormsInfty (m + 1),
    (A.cubeSEP 1).baseEP.boundaryMeasureEff (Nat.succ_pos m) hLUCC hΘ' hcpt' hT' hloc'
        (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω) (cylEnd (X := A.X) Θ' 1) =
      P₁.integralEff hLUC ω ∧
    (A.cubeSEP 1).baseEP.boundaryMeasureEff (Nat.succ_pos m) hLUCC hΘ' hcpt' hT' hloc'
        (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω) (cylEnd (X := A.X) Θ' 0) =
      -P₀.integralEff hLUC ω

/-- **Step (c), effective form, gives the effective cobordism** (`Y = [0, 1] × X`, `F = pr`). -/
theorem hasOrientedCobordismEff_of_cylinder (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hLUC : A.X.IsLUC) (hPUC : (A.cubeSEP 1).X.HasScPartitionsOfUnity)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) {f : A.Obj → A.W} {m : ℕ}
    {P₀ P₁ : OrientedRegularPerturbation A f m}
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    (hends : IsCylinderBoundaryEffOf hLUC hLUCC P₀ P₁ hΘ' hcpt' hT' hloc') :
    P₀.HasOrientedCobordismEff hLUC P₁ := by
  refine ⟨(A.cubeSEP 1).baseEP, A.X.cubeProj 1, hPUC, hLUCC, Θ', T', hΘ', hcpt', hT', hloc',
    fun ω => ?_⟩
  rw [boundaryMeasureEff_cyl_univ hd (Nat.succ_pos m) hLUCC hΘ' hcpt' hT' hloc', (hends ω).1,
    (hends ω).2]
  ring

/-- **Step (c), effective form, for the perturbations step (b) produces** (as
`CylinderOrientationStatement`). -/
def CylinderOrientationEffStatement {f : A.Obj → A.W} (hf : IsSection A.P f) {m : ℕ}
    (hLUC : A.X.IsLUC) (hLUCC : (A.cubeSEP 1).X.IsLUC)
    (P₀ P₁ : OrientedRegularPerturbation A f m) : Prop :=
  ∀ Λ' : (A.cubeSEP 1).W → ℚ≥0,
    IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf)
      (interpAuxNorm A P₀.N P₁.N) (interpSet A P₀.U P₁.U) Λ' →
    (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = P₀.Λ (cubeVal w).2) →
    (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = P₁.Λ (cubeVal w).2) →
    ∀ (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)))
      (hcpt' : (A.cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ))),
    ∃ (T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ)
      (hT' : (A.cubeSEP 1).X.IsOrientation (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) T')
      (hloc' : ∀ x ∈ EpGroupoid.supp (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)),
        ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1)
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) x, C.Represents T'),
      IsCylinderBoundaryEffOf hLUC hLUCC P₀ P₁ hΘ' hcpt' hT' hloc'

/-- **Corollary 15.4.4, effective version, p. 703, along the text's argument**: as
`corollary_15_4_4_cylinder_hyp`, for `X` and `[0, 1] × X` with the local unique continuation
property and the effective form of step (c). -/
theorem corollary_15_4_4_eff_cylinder_hyp
    (h159 : theorem_15_3_9_charged_statement (A.cubeSEP 1))
    (hBC : ∀ x : (A.cubeSEP 1).Obj,
      ∃ c : StrongBundleChart (A.cubeSEP 1).X.PObj (A.cubeSEP 1).P,
        (A.cubeSEP 1).B.IsTameChart c ∧ x ∈ c.φ.source)
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
      CylinderOrientationEffStatement hf.1.1.1 hLUC hLUCC P₀ P₁) :
    corollary_15_4_4_eff_statement A f m hLUC Can := by
  refine corollary_15_4_4_eff_hyp hPU hLUC hd Can fun P₀ P₁ h₀ h₁ => ?_
  obtain ⟨Λ', hreg, e0, e1, hΘ', hcpt'⟩ := corollary_15_3_10_3_charged h159 hBC hd hpara hPUC hf
    hft hS P₀.isRegular P₁.isRegular (hglue P₀ P₁ h₀ h₁).1 (hglue P₀ P₁ h₀ h₁).2
  obtain ⟨T', hT', hloc', hends⟩ := hor P₀ P₁ h₀ h₁ Λ' hreg e0 e1 hΘ' hcpt'
  exact hasOrientedCobordismEff_of_cylinder hd hLUC (hasScPartitionsOfUnity_cyl hpara hPUC) hLUCC
    hΘ' hcpt' hT' hloc' hends

end SBLocalization

end Polyfold
