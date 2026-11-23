import Polyfold.Chapter15.AdmissibleCylinderExtension
import Polyfold.Chapter15.TransversalityEquivalence
import Polyfold.Chapter15.CubeAuxNorm
import Polyfold.Chapter9.LocalFormsSub

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3 (pp. 691–700):
the data of the perturbation theory (Definitions 15.2.1, 15.3.1, 15.3.3) on the restriction of a
strong bundle over an ep-groupoid to a saturated open subset of the object space
(Proposition 7.1.22, p. 250).

# The restriction `W|U → X|U` of a strong bundle to a saturated open set

## The text, paraphrased

(Definition 15.3.1) `(N, U)` controls the compactness of `f` if the orbit space of
`{x ∈ U | N(f(x)) ≤ 1}` has compact closure.  All perturbations of §15.3 are supported in `U`, so
the constructions take place over a saturated open neighbourhood of that set.

## What is formalized (namespaces `Polyfold.SEP`, `Polyfold.SBLocalization`)

For `A : SEP`, `V ⊆ X` an ep-subgroupoid (`hV`), open (`hVo`):

* `SEP.restr`: the pull-back of `W` along the inclusion `X|V → X`; `SEP.restrHom`,
  `SEP.restrIso` (the inclusion as a local strong bundle isomorphism over all of `V`).
* `SEP.restrSec f`, `isScFredholmSectionFunctor_restrSec`, `isScFredholmSectionTame_restrSec`.
* `restrMult Λ`, `isScPlusMultisection_restrMult`, `domSupp_restrMult_subset`,
  `pointwiseNorm_restrMult`.
* `SEP.restrNorm N`, `isAuxNorm_restrNorm`, `auxLe_restrNorm_iff`.
* `isTransversal_restr`: `(f|V, Λ|V)` is transversal if `(f, Λ)` is.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SEP

open StrongBundle MPolyfold

variable (A : SEP.{u}) {V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V)

/-- **The restriction `W|V → X|V`** of the strong bundle `A` to an ep-subgroupoid `V` of the
base (Proposition 7.1.22): the pull-back of `W` along the inclusion `X|V → X`. -/
def restr : SEP.{u} := A.pullbackAlong (A.baseEP.sub hV) (A.baseEP.subFunctor hV)

/-- The inclusion `W|V → W`, a morphism of `SEP` covering `X|V → X`. -/
def restrHom : A.restr hV ⟶ A := A.pullbackHom (A.baseEP.sub hV) (A.baseEP.subFunctor hV)

variable {A}

/-- The base point in `X` of an object of `X|V`. -/
def restrBase (a : (A.restr hV).Obj) : A.Obj := (A.baseEP.subFunctor hV).obj a

theorem restrBase_mem (a : (A.restr hV).Obj) : restrBase hV a ∈ V :=
  A.baseEP.subFunctor_obj_mem hV a

theorem continuous_restrBase : Continuous (restrBase hV) :=
  continuousOn_univ.1 (A.baseEP.subFunctor hV).isScSmoothMap_obj.continuousOn

theorem restrBase_injective : Injective (restrBase hV) := A.baseEP.subFunctor_obj_injective hV

/-- The `W`-component of a point of `W|V`. -/
def restrFib (w : (A.restr hV).W) : A.W := (Hom.Φ (A.restrHom hV)).obj w

theorem P_restrFib (w : (A.restr hV).W) : A.P (restrFib hV w) = restrBase hV ((A.restr hV).P w) :=
  (show pullbackSpace A.P (A.baseEP.subFunctor hV).obj from w).2

/-- A point of `W|V` is determined by its base point and its `W`-component. -/
theorem restr_ext {w w' : (A.restr hV).W} (hP : (A.restr hV).P w = (A.restr hV).P w')
    (h : restrFib hV w = restrFib hV w') : w = w' :=
  Subtype.ext (Prod.ext hP h)

/-- **`f|V`**: the restriction of a section, `a ↦ (a, f(a))`. -/
def restrSec (f : A.Obj → A.W) (hf : IsSection A.P f) : (A.restr hV).Obj → (A.restr hV).W :=
  pullbackLift (A.baseEP.subFunctor hV).obj (f ∘ (A.baseEP.subFunctor hV).obj)
    fun z => hf ((A.baseEP.subFunctor hV).obj z)

theorem restrFib_restrSec {f : A.Obj → A.W} (hf : IsSection A.P f) (a : (A.restr hV).Obj) :
    restrFib hV (restrSec hV f hf a) = f (restrBase hV a) := rfl

theorem isSection_restrSec {f : A.Obj → A.W} (hf : IsSection A.P f) :
    IsSection (A.restr hV).P (restrSec hV f hf) :=
  isSection_pullbackLift _

/-- `f|V` is functorial if `f` is. -/
theorem isFunctorialSection_restrSec {f : A.Obj → A.W} (hf : IsSection A.P f)
    (hfun : A.E.IsFunctorialSection hf) :
    (A.restr hV).E.IsFunctorialSection (isSection_restrSec hV hf) := by
  intro φ
  apply Subtype.ext
  refine Prod.ext rfl ?_
  exact hfun ((A.baseEP.subFunctor hV).mor φ)

/-- **`f|V` is an sc-smooth section functor** if `f` is. -/
theorem isScSmoothSectionFunctor_restrSec {f : A.Obj → A.W}
    (hf : A.E.IsScSmoothSectionFunctor f) :
    (A.restr hV).E.IsScSmoothSectionFunctor (restrSec hV f hf.1.1) := by
  have := A.B.paracompactSpace_pullback (A.baseEP.sub hV).X.PObj (A.baseEP.subFunctor hV).obj
  obtain ⟨hsm, hfun⟩ := hf
  exact ⟨hsm.pullback (A.baseEP.subFunctor hV).isScSmoothMap_obj,
    isFunctorialSection_restrSec hV hsm.1 hfun⟩

variable (hVo : IsOpen V)

/-- **The inclusion `W|V → W` as a local strong bundle isomorphism** from `W|V` (over all of
`X|V`) onto `W` over `V`. -/
def restrIso (a : (A.restr hV).Obj) : StrongBundle.LocalIso (A.restr hV).B A.B univ V :=
  haveI := A.B.paracompactSpace_pullback (A.baseEP.sub hV).X.PObj (A.baseEP.subFunctor hV).obj
  (A.B.isStrongBundleIsoOn_pullbackProj' (A.baseEP.subFunctor hV).isScSmoothMap_obj
    (A.baseEP.isScDiffeoOn_subRetract hV hVo a).symm a).toLocalIso

@[simp] theorem restrIso_ϕ (a : (A.restr hV).Obj) : (restrIso hV hVo a).ϕ = restrBase hV := rfl

@[simp] theorem restrIso_Φ (a : (A.restr hV).Obj) : (restrIso hV hVo a).Φ = restrFib hV := rfl

/-- `f|V = Ψ ∘ f ∘ ϕ` for the inclusion `(ϕ, Φ)` with inverse `Ψ`. -/
theorem eqOn_restrSec {f : A.Obj → A.W} (hf : IsSection A.P f) (a : (A.restr hV).Obj) :
    EqOn (restrSec hV f hf) ((restrIso hV hVo a).Ψ ∘ f ∘ (restrIso hV hVo a).ϕ) univ :=
  fun z _ => ((restrIso hV hVo a).zero.left_inv (restrSec hV f hf z) (mem_univ _)).symm

/-- **`f|V` is an sc-Fredholm section functor** if `f` is (Definition 3.1.18 is local and
invariant under local strong bundle isomorphisms). -/
theorem isScFredholmSectionFunctor_restrSec (hVo : IsOpen V) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) :
    (A.restr hV).E.IsScFredholmSectionFunctor (restrSec hV f hf.1.1.1) :=
  ⟨isScSmoothSectionFunctor_restrSec hV hf.1,
    StrongBundle.isScFredholmSection_of_forall (isScSmoothSectionFunctor_restrSec hV hf.1).1
      fun a => ⟨univ, V, restrIso hV hVo a, f, mem_univ _, eqOn_restrSec hV hVo hf.1.1.1 a,
        hf.2⟩⟩

/-- **`f|V` has tame germ data** if `f` has (Definition 3.6.5). -/
theorem isScFredholmSectionTame_restrSec (hVo : IsOpen V) {f : A.Obj → A.W}
    (hf : A.E.IsScSmoothSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f) :
    (A.restr hV).B.IsScFredholmSectionTame (restrSec hV f hf.1.1) :=
  StrongBundle.isScFredholmSectionTame_of_forall (isScSmoothSectionFunctor_restrSec hV hf).1
    fun a => ⟨univ, V, restrIso hV hVo a, f, mem_univ _, eqOn_restrSec hV hVo hf.1.1 a, hft⟩

/-- **`S_{f|V} = S_f ∩ V`.** -/
theorem solutionSet_restrSec {f : A.Obj → A.W} (hf : IsSection A.P f) :
    solutionSet (A.restr hV).P (restrSec hV f hf) = restrBase hV ⁻¹' solutionSet A.P f := by
  ext z
  constructor
  · intro h
    exact congrArg (restrFib hV) h
  · intro h
    exact Subtype.ext (Prod.ext rfl h)

/-! ### The auxiliary norm -/

/-- **`N|V`**: `(a, h) ↦ N(h)` on `(W|V)_{0,1}`. -/
def restrNorm (N : A.B.One → ℝ) : (A.restr hV).B.One → ℝ :=
  haveI := A.B.paracompactSpace_pullback (A.baseEP.sub hV).X.PObj (A.baseEP.subFunctor hV).obj
  A.B.pullbackAuxNorm (A.baseEP.subFunctor hV).isScSmoothMap_obj N

/-- A point of `W|V` lies in `(W|V)_{0,1}` iff its `W`-component lies in `W_{0,1}`. -/
theorem mem_oneSet_restr_iff (w : (A.restr hV).W) :
    w ∈ (A.restr hV).B.oneSet ↔ restrFib hV w ∈ A.B.oneSet := by
  have := A.B.paracompactSpace_pullback (A.baseEP.sub hV).X.PObj (A.baseEP.subFunctor hV).obj
  exact A.B.mem_oneSet_pullback_iff (A.baseEP.subFunctor hV).isScSmoothMap_obj w

/-- `N|V(w) = N(k)` when `k` is the `W`-component of `w`. -/
theorem restrNorm_eq {N : A.B.One → ℝ} (w : (A.restr hV).B.One) (k : A.B.One)
    (hk : A.B.oneVal k = restrFib hV ((A.restr hV).B.oneVal w)) : restrNorm hV N w = N k :=
  congrArg N (A.B.oneVal_injective hk.symm)

/-- `AuxLe` for `N|V` at `w` is `AuxLe` for `N` at the `W`-component of `w`. -/
theorem auxLe_restrNorm_iff {N : A.B.One → ℝ} (w : (A.restr hV).W) {r : ℝ} :
    (A.restr hV).B.AuxLe (restrNorm hV N) w r ↔ A.B.AuxLe N (restrFib hV w) r := by
  have := A.B.paracompactSpace_pullback (A.baseEP.sub hV).X.PObj (A.baseEP.subFunctor hV).obj
  exact StrongBundle.auxLe_pullbackAuxNorm_iff (A.baseEP.subFunctor hV).isScSmoothMap_obj

/-- `N|V` is an auxiliary norm of the strong bundle `W|V → X|V` (Definition 5.1.1). -/
theorem isAuxNorm_restrNorm' {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) :
    (A.restr hV).B.IsAuxNorm (restrNorm hV N) := by
  have := A.B.paracompactSpace_pullback (A.baseEP.sub hV).X.PObj (A.baseEP.subFunctor hV).obj
  exact hN.pullback (A.baseEP.subFunctor hV).isScSmoothMap_obj

/-- **`N|V` is an auxiliary norm of `(W|V, μ)`** (Definition 8.3.5, p. 379). -/
theorem isAuxNorm_restrNorm {N : A.B.One → ℝ} (hN : A.E.IsAuxNorm N) :
    (A.restr hV).E.IsAuxNorm (restrNorm hV N) := by
  refine ⟨isAuxNorm_restrNorm' hV hN.isAuxNorm, fun h k φ hk hh => ?_⟩
  have := A.B.paracompactSpace_pullback (A.baseEP.sub hV).X.PObj (A.baseEP.subFunctor hV).obj
  have hk' : A.P (restrFib hV ((A.restr hV).B.oneVal k)) =
      A.X.src ((A.baseEP.subFunctor hV).mor φ) := by
    rw [P_restrFib, hk]; rfl
  exact hN.map_μ
    (StrongBundle.pullbackOneMap (A.baseEP.subFunctor hV).isScSmoothMap_obj h)
    (StrongBundle.pullbackOneMap (A.baseEP.subFunctor hV).isScSmoothMap_obj k)
    ((A.baseEP.subFunctor hV).mor φ) hk' (congrArg (restrFib hV) hh)

end SEP

namespace SBLocalization

open StrongBundle MPolyfold SEP

variable {A : SEP.{u}} {V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V)

/-! ### Multisections -/

/-- **`Λ|V`**: `(a, h) ↦ Λ(h)`. -/
def restrMult (Λ : A.W → ℚ≥0) : (A.restr hV).W → ℚ≥0 := pullMult (A.restrHom hV) Λ

theorem restrMult_apply (Λ : A.W → ℚ≥0) (w : (A.restr hV).W) :
    restrMult hV Λ w = Λ (restrFib hV w) := rfl

/-- **`Λ|V` is an sc⁺-multisection** of `W|V` if `Λ` is one of `W` (Definition 13.2.1): the
local sections are the restrictions of those of `Λ`. -/
theorem isScPlusMultisection_restrMult (hVo : IsOpen V) {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) :
    IsScPlusMultisection (A.restr hV) (restrMult hV Λ) := by
  refine ⟨hΛ.1.pullMult (A.restrHom hV), fun a => ?_⟩
  obtain ⟨O, k, s, σ, hO, hx, h⟩ := hΛ.exists_isLocalRepOn (restrBase hV a)
  set L := restrIso hV hVo a
  have hO' : IsOpen (O ∩ V) := hO.inter hVo
  have hrep := isLocalRepOn_isoSec L (Λ := restrMult hV Λ) (fun _ _ => rfl) hO'
    inter_subset_right (h.mono hO' inter_subset_left)
  exact hasLocalSectionStructure_of_isLocalRepOn (isOpen_isoSet L hO')
    ⟨mem_univ _, hx, restrBase_mem hV a⟩ hrep

/-- The zero of the fibre of `W|V` over `a` has `W`-component `0_a`. -/
theorem restrFib_fiberZero (a : (A.restr hV).Obj) :
    restrFib hV (fiberZero (A.restr hV).P a) = fiberZero A.P (restrBase hV a) := rfl

/-- **`dom-supp(Λ|V) ⊆ U ∩ V`** if `dom-supp(Λ) ⊆ U`. -/
theorem domSupp_restrMult_subset {Λ : A.W → ℚ≥0} {U : Set A.Obj} (h : domSupp Λ ⊆ U) :
    domSupp (restrMult hV Λ) ⊆ restrBase hV ⁻¹' U := by
  have hcl : IsClosed (restrBase hV ⁻¹' domSupp Λ) :=
    isClosed_closure.preimage (continuous_restrBase hV)
  refine (closure_minimal ?_ hcl).trans (preimage_mono h)
  rintro a ⟨w, hw, hw0, hpos⟩
  refine subset_closure ⟨restrFib hV w, ?_, ?_, hpos⟩
  · rw [P_restrFib, hw]
  · intro e
    refine hw0 (restr_ext hV ?_ ?_)
    · rw [hw]; exact (proj_fiberZero _ a).symm
    · rw [e, restrFib_fiberZero]

/-- `supp(Λ|V)(a)` is `supp(Λ)(a)`. -/
theorem image_restrFib_suppAt (Λ : A.W → ℚ≥0) (a : (A.restr hV).Obj) :
    restrFib hV '' suppAt (restrMult hV Λ) a = suppAt Λ (restrBase hV a) := by
  ext v
  constructor
  · rintro ⟨w, ⟨hw, hpos⟩, rfl⟩
    exact ⟨by rw [P_restrFib, hw], hpos⟩
  · rintro ⟨hv, hpos⟩
    exact ⟨⟨(a, v), hv⟩, ⟨rfl, hpos⟩, rfl⟩

/-- `N|V` read on `W|V` is `N` read on the `W`-component. -/
theorem normW_restrNorm (N : A.B.One → ℝ) (w : (A.restr hV).W) :
    normW (restrNorm hV N) w = normW N (restrFib hV w) := by
  by_cases hw : w ∈ (A.restr hV).B.oneSet
  · have hw' := (mem_oneSet_restr_iff hV w).1 hw
    rw [normW_of_mem _ hw, normW_of_mem _ hw']
    exact restrNorm_eq hV _ _ rfl
  · have hw' : restrFib hV w ∉ A.B.oneSet := fun h => hw ((mem_oneSet_restr_iff hV w).2 h)
    unfold normW
    rw [dif_neg hw, dif_neg hw']

/-- **`(N|V)(Λ|V)(a) = N(Λ)(a)`** (Definition 13.2.3). -/
theorem pointwiseNorm_restrMult (N : A.B.One → ℝ) (Λ : A.W → ℚ≥0) (a : (A.restr hV).Obj) :
    pointwiseNorm (restrNorm hV N) (restrMult hV Λ) a = pointwiseNorm N Λ (restrBase hV a) := by
  unfold pointwiseNorm
  rw [← image_restrFib_suppAt hV Λ a, image_image]
  exact congrArg sSup (image_congr fun w _ => normW_restrNorm hV N w)

/-! ### Transversality -/

/-- **`(f|V, Λ|V)` is transversal if `(f, Λ)` is** (Definition 15.2.1, p. 688): the operators of
`T(f|V, Λ|V)(a)` are those of `T(f, Λ)(a)` read through the inclusion. -/
theorem isTransversal_restr (hVo : IsOpen V) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (H : IsTransversal f Λ) :
    IsTransversal (restrSec hV f hf.1.1.1) (restrMult hV Λ) := by
  intro a hpos
  have hfr := isScFredholmSectionFunctor_restrSec hV hVo hf
  have hΛr := isScPlusMultisection_restrMult hV hVo hΛ
  have ha1 : a ∈ (A.restr hV).X.PObj.levelSet 1 := mem_levelSet_one_of_pos hfr hΛr hpos
  have hpos' : 0 < Λ (f (restrBase hV a)) := hpos
  obtain ⟨-, hx1, h1⟩ := H _ hpos'
  refine ⟨hpos, ha1, ?_⟩
  exact (isOntoAtLevel_localIso_iff (restrIso hV hVo a) hfr hf hΛ
    (eqOn_restrSec hV hVo hf.1.1.1 a) (fun _ _ => rfl)
    (by rw [(A.restr hV).X.PObj.levelVal_levelMk 1 _ ha1]; exact mem_univ _)
    (by
      rw [(A.restr hV).X.PObj.levelVal_levelMk 1 _ ha1, A.X.PObj.levelVal_levelMk 1 _ hx1]
      rfl)).2 h1

end SBLocalization

end Polyfold
