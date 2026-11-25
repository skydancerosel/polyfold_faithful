import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V15_34

set_option maxSynthPendingDepth 3

/-! Round trip for V15_34 (2021 Corollary 15.3.10 (3), pp. 699–700; 2017: Corollary 15.1 (3)):
regular perturbations are cobordant.

`A` is the conjunction of the types of the 34 theorems of the item (definitions such as
`cylExtension`, `cubeGlue`, `collarAuxNorm`, `cubeOrbitHomeomorph` are vocabulary), at universe
`0` (the `TrivialBundle` examples have no universe parameter).  The main conjunct is
`corollary_15_3_10_3_regular` (Corollary 15.3.10 (3) with `Ñ = interpAuxNorm N₀ N₁`,
`Ũ = interpSet U₀ U₁`); `corollary_15_3_10_3_collar` is the same with bump functions in place of
partitions of unity and the collar norm.

* `A_to_B`: not proved.  The main conjunct assumes, besides `B`'s hypotheses, the tame-germ
  hypothesis `A.B.IsScFredholmSectionTame f` and sc-smooth partitions of unity on the object
  M-polyfold (`corollary_15_3_10_3_collar`: pointwise bump functions instead); `B` has neither
  (its comment flags the missing bump/partition hypothesis).  With them added (`Bplus`):
  - `main_to_Bcore` (passes `#rt_check`): the main conjunct gives `Ñ, Ũ, Λ̃` with `(Ñ, Ũ, Λ̃)` a
    structurable regular perturbation of `f̃ = cubeLiftSec f` (`= cubeLiftEp f`), `Λ̃ = Λⁱ` over
    `{i} × X`, `Λ̃ ∘ f̃` branched and compact.
  - `main_to_Bplus` (all of `Bplus`, including "tame" and `∂Θ̃(i, x) = Θᵢ(x)`): proved with the
    project's cylinder lemmas `isBoundaryFaceOnto_cubeGlue`, `boundaryTheta_cyl_zero/one`, whose
    proofs use theorems of this item (`mem_boundary_cubeSEP_iff`, `P_cubeVal_snd`,
    `isScFredholmSectionTame_cubeLiftEp`, `cubeGlue_of_zero/one`); so it does not pass
    `#rt_check` and is recorded only as evidence that the main conjunct and project lemmas give
    `Bplus`.  The main conjunct itself states neither "tame" nor the boundary identity.
* `B_to_A`: not proved.  `B` gives some pair `(Ñ, Ũ)` only, while the main conjunct asserts the
  regular perturbation for the specific pair `(interpAuxNorm N₀ N₁, interpSet U₀ U₁)` (and
  `corollary_15_3_10_3_bump` a pair restricting to `(Nⁱ, Uⁱ)` over `{i} × X`); `B` says nothing
  about `Ñ, Ũ` over the ends.  The other conjuncts are proof steps (gluing, collars, orbit spaces
  of `[0, 1] × X`) and examples, not stated by `B`.
-/

namespace RoundTrip.V15_34
open Set Function Polyfold Polyfold.SBLocalization

def A : Prop :=
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_collar.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isStructurable_cylExtension.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isStructurable_cubePullMult.{0}) ∧
  (type_of% @Polyfold.SEP.isAuxNorm_collarAuxNorm.{0}) ∧
  (type_of% @Polyfold.SEP.controlsCompactness_collar.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_regular.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_of_onto.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_of_rel_onto.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_of_rel.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_struct_charged.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_charged.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isScFredholmSectionTame_cubeLiftEp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.mem_boundary_cubeSEP_iff.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_hyp.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.injective_cubeOrbitMap.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.surjective_cubeOrbitMap.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isOpenMap_cubeOrbitMap.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.hasParacompactOrbitSpace_cubeProd.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_of_theorem_15_3_9.{0}) ∧
  (type_of% @Polyfold.SBLocalization.cubeGlue_of_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.cubeGlue_of_one.{0}) ∧
  (type_of% @Polyfold.SBLocalization.P_cubeVal_snd.{0}) ∧
  (type_of% @Polyfold.SBLocalization.cubeVal_fiberZero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.cubeVal_snd_ne_fiberZero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.boundaryDomSupp_cubeGlue_subset.{0}) ∧
  (type_of% @Polyfold.SBLocalization.normW_interpAuxNorm_le.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointwiseNorm_cubeGlue_le_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointwiseNorm_cubeGlue_le_one.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_glue_hyp.{0}) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_3_10_3_collar_epSEP_nonempty) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_3_10_3_collar_epSEP) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_3_10_3_regular_epSEP_nonempty) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_3_10_3_regular_epSEP)

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.corollary_15_3_10_3_bump.{0},
    @Polyfold.SBLocalization.corollary_15_3_10_3_collar.{0},
    @Polyfold.SBLocalization.isStructurable_cylExtension.{0},
    @Polyfold.SBLocalization.isStructurable_cubePullMult.{0},
    @Polyfold.SEP.isAuxNorm_collarAuxNorm.{0},
    @Polyfold.SEP.controlsCompactness_collar.{0},
    @Polyfold.SBLocalization.corollary_15_3_10_3_regular.{0},
    @Polyfold.SBLocalization.corollary_15_3_10_3_of_onto.{0},
    @Polyfold.SBLocalization.corollary_15_3_10_3_of_rel_onto.{0},
    @Polyfold.SBLocalization.corollary_15_3_10_3_of_rel.{0},
    @Polyfold.SBLocalization.corollary_15_3_10_3_struct_charged.{0},
    @Polyfold.SBLocalization.corollary_15_3_10_3_charged.{0},
    @Polyfold.SBLocalization.isScFredholmSectionTame_cubeLiftEp.{0},
    @Polyfold.SBLocalization.mem_boundary_cubeSEP_iff.{0},
    @Polyfold.SBLocalization.corollary_15_3_10_3_hyp.{0},
    @Polyfold.EpGroupoid.injective_cubeOrbitMap.{0},
    @Polyfold.EpGroupoid.surjective_cubeOrbitMap.{0},
    @Polyfold.EpGroupoid.isOpenMap_cubeOrbitMap.{0},
    @Polyfold.EpGroupoid.hasParacompactOrbitSpace_cubeProd.{0},
    @Polyfold.SBLocalization.corollary_15_3_10_3_of_theorem_15_3_9.{0},
    @Polyfold.SBLocalization.cubeGlue_of_zero.{0},
    @Polyfold.SBLocalization.cubeGlue_of_one.{0},
    @Polyfold.SBLocalization.P_cubeVal_snd.{0},
    @Polyfold.SBLocalization.cubeVal_fiberZero.{0},
    @Polyfold.SBLocalization.cubeVal_snd_ne_fiberZero.{0},
    @Polyfold.SBLocalization.boundaryDomSupp_cubeGlue_subset.{0},
    @Polyfold.SBLocalization.normW_interpAuxNorm_le.{0},
    @Polyfold.SBLocalization.pointwiseNorm_cubeGlue_le_zero.{0},
    @Polyfold.SBLocalization.pointwiseNorm_cubeGlue_le_one.{0},
    @Polyfold.SBLocalization.corollary_15_3_10_3_glue_hyp.{0},
    @Polyfold.TrivialBundle.corollary_15_3_10_3_collar_epSEP_nonempty,
    @Polyfold.TrivialBundle.corollary_15_3_10_3_collar_epSEP,
    @Polyfold.TrivialBundle.corollary_15_3_10_3_regular_epSEP_nonempty,
    @Polyfold.TrivialBundle.corollary_15_3_10_3_regular_epSEP⟩

/-- `f̃ = cubeLiftSec f` is the project's `cubeLiftEp f` for a section `f`. -/
theorem cubeLiftSec_eq {A : SEP.{0}} {f : A.Obj → A.W} (hsec : IsSection A.P f) :
    cubeLiftSec f = SEP.cubeLiftEp (n := 1) f hsec := by
  have e : fixSec f = f := funext fun y => fixSec_of (hsec y)
  have key : ∀ (g : A.Obj → A.W) (hg : IsSection A.P g), g = f →
      SEP.cubeLiftEp (n := 1) g hg = SEP.cubeLiftEp (n := 1) f hsec := by
    rintro g hg rfl; rfl
  exact key _ _ e

theorem tPt_coe {q : Fin 1 → unitInterval} {i : unitInterval} (h : q = tPt i) : (q 0 : ℝ) = i := by
  subst h; rfl

/-- `B`'s hypotheses with tame germ data and partitions of unity added, and `B`'s conclusion. -/
def Bplus : Prop :=
  ∀ (A : SEP.{0}), (∀ x : A.Obj, A.X.PObj.degIndex x = 0) → A.X.HasParacompactOrbitSpace →
    A.X.PObj.AdmitsScPartitionsOfUnity →
    ∀ (f : A.Obj → A.W), A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
    A.E.HasCompactSolutionSetEp f →
    ∀ (N₀ N₁ : A.B.One → ℝ) (U₀ U₁ : Set A.Obj) (Λ₀ Λ₁ : A.W → ℚ≥0),
      IsRegularPerturbation A f N₀ U₀ Λ₀ → IsRegularPerturbation A f N₁ U₁ Λ₁ →
      ∃ (Nt : (A.cubeSEP 1).B.One → ℝ) (Ut : Set (A.cubeSEP 1).Obj)
        (Λt : (A.cubeSEP 1).W → ℚ≥0),
        IsRegularPerturbation (A.cubeSEP 1) (cubeLiftSec f) Nt Ut Λt ∧
        (∀ w : (A.cubeSEP 1).W, (SEP.cubeVal w).1.1 = tPt 0 → Λt w = Λ₀ (SEP.cubeVal w).2) ∧
        (∀ w : (A.cubeSEP 1).W, (SEP.cubeVal w).1.1 = tPt 1 → Λt w = Λ₁ (SEP.cubeVal w).2) ∧
        (A.cubeSEP 1).X.IsBranchedEpSubgroupoid (comp Λt (cubeLiftSec f)) ∧
        (A.cubeSEP 1).X.IsCompactBranched (comp Λt (cubeLiftSec f)) ∧
        (A.cubeSEP 1).X.IsTameBranched (comp Λt (cubeLiftSec f)) ∧
        (∀ x : A.Obj,
          (A.cubeSEP 1).X.boundaryTheta (comp Λt (cubeLiftSec f)) (tPt 0, x) = comp Λ₀ f x ∧
          (A.cubeSEP 1).X.boundaryTheta (comp Λt (cubeLiftSec f)) (tPt 1, x) = comp Λ₁ f x)

/-- `Bplus` without "tame" and the boundary identity. -/
def Bcore : Prop :=
  ∀ (A : SEP.{0}), (∀ x : A.Obj, A.X.PObj.degIndex x = 0) → A.X.HasParacompactOrbitSpace →
    A.X.PObj.AdmitsScPartitionsOfUnity →
    ∀ (f : A.Obj → A.W), A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
    A.E.HasCompactSolutionSetEp f →
    ∀ (N₀ N₁ : A.B.One → ℝ) (U₀ U₁ : Set A.Obj) (Λ₀ Λ₁ : A.W → ℚ≥0),
      IsRegularPerturbation A f N₀ U₀ Λ₀ → IsRegularPerturbation A f N₁ U₁ Λ₁ →
      ∃ (Nt : (A.cubeSEP 1).B.One → ℝ) (Ut : Set (A.cubeSEP 1).Obj)
        (Λt : (A.cubeSEP 1).W → ℚ≥0),
        IsRegularPerturbation (A.cubeSEP 1) (cubeLiftSec f) Nt Ut Λt ∧
        (∀ w : (A.cubeSEP 1).W, (SEP.cubeVal w).1.1 = tPt 0 → Λt w = Λ₀ (SEP.cubeVal w).2) ∧
        (∀ w : (A.cubeSEP 1).W, (SEP.cubeVal w).1.1 = tPt 1 → Λt w = Λ₁ (SEP.cubeVal w).2) ∧
        (A.cubeSEP 1).X.IsBranchedEpSubgroupoid (comp Λt (cubeLiftSec f)) ∧
        (A.cubeSEP 1).X.IsCompactBranched (comp Λt (cubeLiftSec f))

/-- **The main conjunct ⇒ `Bcore`.** -/
theorem main_to_Bcore :
    (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_regular.{0}) → Bcore := by
  intro H A hd hpara hPU f hf hft hS N₀ N₁ U₀ U₁ Λ₀ Λ₁ hr₀ hr₁
  obtain ⟨Λ', hreg, h0, h1, hbr, hK⟩ := H hd hpara hPU hf hft hS hr₀ hr₁
  have e := cubeLiftSec_eq (A := A) hf.1.1.1
  refine ⟨_, _, Λ', by rw [e]; exact hreg, fun w hw => h0 w ?_, fun w hw => h1 w ?_, ?_, ?_⟩
  · rw [tPt_coe hw]; rfl
  · rw [tPt_coe hw]; rfl
  · unfold comp; rw [e]; exact hbr
  · unfold comp; rw [e]; exact hK

theorem A_to_Bcore : A → Bcore := fun hA => main_to_Bcore hA.2.2.2.2.2.2.1

/-- At a point with `d_X(x) = 0`, `T^R_xX = T_xX` in every chart and presentation. -/
theorem reducedTangentFiber_eq_top_of_deg0 {A : SEP.{0}} {x : A.X.PObj.Level 1}
    (hd : A.X.PObj.degIndex (A.X.PObj.levelVal 1 x) = 0) {φ : MChart A.Obj}
    (hφ : A.X.PObj.IsChart φ) (hxφ : A.X.PObj.levelVal 1 x ∈ φ.source) {k : ℕ} {V : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin k → ℝ)).prod V)) (hT : φ.model.C = T 0 ⁻¹' quadrant k V 0) :
    MPolyfold.reducedTangentFiber hφ hxφ T = ⊤ := by
  obtain ⟨χ, hχ, haχ, hdχ⟩ := A.X.PObj.exists_isChart_degIndex_eq (A.X.PObj.levelVal 1 x)
  obtain ⟨n', W', Tχ, hTχ⟩ := χ.model.isPartialQuadrant
  have h0 : degIndex χ.model.E χ.model.C (χ (A.X.PObj.levelVal 1 x)) = 0 := by
    have := hd; rw [hdχ] at this; exact this
  have hint : χ (A.X.PObj.levelVal 1 x) ∈ interior χ.model.C :=
    (degIndex_eq_zero_iff χ.model.isPartialQuadrant (χ.apply_mem_C haχ)).1 h0
  have htop : MPolyfold.reducedTangentFiber hχ haχ Tχ = ⊤ := by
    change (minimalSubspaceWith Tχ (χ _)).comap _ = ⊤
    rw [minimalSubspaceWith_eq_top_of_mem_interior Tχ hTχ hint, Submodule.comap_top]
  rw [MPolyfold.reducedTangentFiber_eq hφ hxφ T hχ haχ Tχ hT hTχ, htop]

/-- **The main conjunct (with project lemmas) ⇒ `Bplus`.**  Not `#rt_check`-clean: the cylinder
lemmas used for "tame" and `∂Θ̃` go through theorems of this item. -/
theorem main_to_Bplus :
    (type_of% @Polyfold.SBLocalization.corollary_15_3_10_3_regular.{0}) → Bplus := by
  intro H A hd hpara hPU f hf hft hS N₀ N₁ U₀ U₁ Λ₀ Λ₁ hr₀ hr₁
  obtain ⟨Λ', hreg, h0, h1, hbr, hK⟩ := H hd hpara hPU hf hft hS hr₀ hr₁
  have e := cubeLiftSec_eq (A := A) hf.1.1.1
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hfC := SEP.isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  have hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ' := hreg.2.1.1
  have honto := isBoundaryFaceOnto_cubeGlue hd hf hft hr₀.2.2.2.2 hr₁.2.2.2.2
  have hbd : ∀ w : (A.cubeSEP 1).W, (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary →
      Λ' w = cubeGlue Λ₀ Λ₁ w := fun w hw => by
    rcases (mem_boundary_cubeSEP_iff hX hd _).1 hw with h | h
    · exact (h0 w h).trans (cubeGlue_of_zero h).symm
    · exact (h1 w h).trans (cubeGlue_of_one h).symm
  have hgp : IsInGeneralPosition (A.cubeSEP 1) (SEP.cubeLiftEp (n := 1) f hf.1.1.1) Λ' := by
    refine (isInGeneralPosition_iff_forall_at hfC hΛ').2 fun y hpos => ?_
    by_cases hyb : y ∈ (A.cubeSEP 1).X.PObj.boundary
    · exact isInGeneralPositionAt_of_isBoundaryFaceOnto hfC hftC hΛ' hbd honto hyb hpos
    · have hdy : (A.cubeSEP 1).X.PObj.degIndex y = 0 := by
        simp only [MPolyfold.boundary, mem_ofPred_eq, not_le, Nat.lt_one_iff] at hyb
        exact hyb
      obtain ⟨-, hy1, hon⟩ := hreg.2.2.2.2 y hpos
      refine ⟨hy1, fun L hL φ hφ hxφ k V T hT => ?_⟩
      have hLs : Surjective L := hon L hL
      have heq := reducedTangentFiber_eq_top_of_deg0 (x := (A.cubeSEP 1).X.PObj.levelMk 1 y hy1)
        hdy hφ hxφ T hT
      intro w
      obtain ⟨v, rfl⟩ := hLs w
      exact ⟨⟨v, by rw [heq]; trivial⟩, rfl⟩
  obtain ⟨-, -, hTB⟩ := theorem_15_3_7_in_particular_tame_hyp hfC hftC hreg.1 hΛ'
    (fun x => (hreg.2.2.2.1 x).le) hreg.2.2.1 hgp
  refine ⟨_, _, Λ', by rw [e]; exact hreg, fun w hw => h0 w ?_, fun w hw => h1 w ?_, ?_, ?_, ?_,
    fun x => ⟨?_, ?_⟩⟩
  · rw [tPt_coe hw]; rfl
  · rw [tPt_coe hw]; rfl
  · unfold comp; rw [e]; exact hbr
  · unfold comp; rw [e]; exact hK
  · unfold comp; rw [e]; exact hTB
  · unfold comp; rw [e]
    exact boundaryTheta_cyl_zero hd hf hft hΛ' h0 h1 honto (z := (tPt 0, x)) rfl
  · unfold comp; rw [e]
    exact boundaryTheta_cyl_one hd hf hft hΛ' h0 h1 honto (z := (tPt 1, x)) rfl

/-- `Bplus` is `B` with two more hypotheses. -/
theorem B_to_Bplus : B → Bplus := fun hB A hd hpara _ f hf _ hS N₀ N₁ U₀ U₁ Λ₀ Λ₁ hr₀ hr₁ =>
  hB A hd hpara f hf hS N₀ N₁ U₀ U₁ Λ₀ Λ₁ hr₀ hr₁

#rt_check RoundTrip.V15_34.main_to_Bcore [Polyfold.SBLocalization.corollary_15_3_10_3_bump, Polyfold.SBLocalization.corollary_15_3_10_3_collar, Polyfold.SBLocalization.isStructurable_cylExtension, Polyfold.SBLocalization.isStructurable_cubePullMult, Polyfold.SEP.isAuxNorm_collarAuxNorm, Polyfold.SEP.controlsCompactness_collar, Polyfold.SBLocalization.corollary_15_3_10_3_regular, Polyfold.SBLocalization.corollary_15_3_10_3_of_onto, Polyfold.SBLocalization.corollary_15_3_10_3_of_rel_onto, Polyfold.SBLocalization.corollary_15_3_10_3_of_rel, Polyfold.SBLocalization.corollary_15_3_10_3_struct_charged, Polyfold.SBLocalization.corollary_15_3_10_3_charged, Polyfold.SBLocalization.isScFredholmSectionTame_cubeLiftEp, Polyfold.SBLocalization.mem_boundary_cubeSEP_iff, Polyfold.SBLocalization.corollary_15_3_10_3_hyp, Polyfold.EpGroupoid.injective_cubeOrbitMap, Polyfold.EpGroupoid.surjective_cubeOrbitMap, Polyfold.EpGroupoid.isOpenMap_cubeOrbitMap, Polyfold.EpGroupoid.hasParacompactOrbitSpace_cubeProd, Polyfold.SBLocalization.corollary_15_3_10_3_of_theorem_15_3_9, Polyfold.SBLocalization.cubeGlue_of_zero, Polyfold.SBLocalization.cubeGlue_of_one, Polyfold.SBLocalization.P_cubeVal_snd, Polyfold.SBLocalization.cubeVal_fiberZero, Polyfold.SBLocalization.cubeVal_snd_ne_fiberZero, Polyfold.SBLocalization.boundaryDomSupp_cubeGlue_subset, Polyfold.SBLocalization.normW_interpAuxNorm_le, Polyfold.SBLocalization.pointwiseNorm_cubeGlue_le_zero, Polyfold.SBLocalization.pointwiseNorm_cubeGlue_le_one, Polyfold.SBLocalization.corollary_15_3_10_3_glue_hyp, Polyfold.TrivialBundle.corollary_15_3_10_3_collar_epSEP_nonempty, Polyfold.TrivialBundle.corollary_15_3_10_3_collar_epSEP, Polyfold.TrivialBundle.corollary_15_3_10_3_regular_epSEP_nonempty, Polyfold.TrivialBundle.corollary_15_3_10_3_regular_epSEP]
#rt_check RoundTrip.V15_34.A_to_Bcore [Polyfold.SBLocalization.corollary_15_3_10_3_bump, Polyfold.SBLocalization.corollary_15_3_10_3_collar, Polyfold.SBLocalization.isStructurable_cylExtension, Polyfold.SBLocalization.isStructurable_cubePullMult, Polyfold.SEP.isAuxNorm_collarAuxNorm, Polyfold.SEP.controlsCompactness_collar, Polyfold.SBLocalization.corollary_15_3_10_3_regular, Polyfold.SBLocalization.corollary_15_3_10_3_of_onto, Polyfold.SBLocalization.corollary_15_3_10_3_of_rel_onto, Polyfold.SBLocalization.corollary_15_3_10_3_of_rel, Polyfold.SBLocalization.corollary_15_3_10_3_struct_charged, Polyfold.SBLocalization.corollary_15_3_10_3_charged, Polyfold.SBLocalization.isScFredholmSectionTame_cubeLiftEp, Polyfold.SBLocalization.mem_boundary_cubeSEP_iff, Polyfold.SBLocalization.corollary_15_3_10_3_hyp, Polyfold.EpGroupoid.injective_cubeOrbitMap, Polyfold.EpGroupoid.surjective_cubeOrbitMap, Polyfold.EpGroupoid.isOpenMap_cubeOrbitMap, Polyfold.EpGroupoid.hasParacompactOrbitSpace_cubeProd, Polyfold.SBLocalization.corollary_15_3_10_3_of_theorem_15_3_9, Polyfold.SBLocalization.cubeGlue_of_zero, Polyfold.SBLocalization.cubeGlue_of_one, Polyfold.SBLocalization.P_cubeVal_snd, Polyfold.SBLocalization.cubeVal_fiberZero, Polyfold.SBLocalization.cubeVal_snd_ne_fiberZero, Polyfold.SBLocalization.boundaryDomSupp_cubeGlue_subset, Polyfold.SBLocalization.normW_interpAuxNorm_le, Polyfold.SBLocalization.pointwiseNorm_cubeGlue_le_zero, Polyfold.SBLocalization.pointwiseNorm_cubeGlue_le_one, Polyfold.SBLocalization.corollary_15_3_10_3_glue_hyp, Polyfold.TrivialBundle.corollary_15_3_10_3_collar_epSEP_nonempty, Polyfold.TrivialBundle.corollary_15_3_10_3_collar_epSEP, Polyfold.TrivialBundle.corollary_15_3_10_3_regular_epSEP_nonempty, Polyfold.TrivialBundle.corollary_15_3_10_3_regular_epSEP]
/- `#rt_check RoundTrip.V15_34.main_to_Bplus [...]` reports that the proof reaches the item's
theorems `isScFredholmSectionTame_cubeLiftEp`, `mem_boundary_cubeSEP_iff`, `cubeGlue_of_zero`,
`cubeGlue_of_one` (used directly, all conjuncts of `A`) and `P_cubeVal_snd` (inside the project's
`isBoundaryFaceOnto_cubeGlue`); it is therefore not counted as a round-trip direction. -/

end RoundTrip.V15_34
