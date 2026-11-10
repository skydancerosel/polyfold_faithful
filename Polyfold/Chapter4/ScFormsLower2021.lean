import Polyfold.Chapter4.ScFormsSquare2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4, pp. 197–198
(2017 p. 150 and Definition 4.10; preprint: before Definition 4.27 and Definition 4.27): `d`
commutes with the inclusion `X¹ → X`, `d` on `Ω*_∞(X)` with `d² = 0`, and Definition 4.4.6,
the sc-de Rham cohomology.

# `d` on the direct limit and the sc-de Rham cohomology

## What is proved

* `retractWhitneyMap_shiftIncl`: on a retract, `⊕ₖ T(O¹ → O)` is the sc-operator `whitneyIncl`.
* `extD_formLower`: `d(ι^*ω) = ι^*(dω)` for `ω ∈ Ωᵏ(X)` and `ι : X¹ → X` (the commutative
  square of p. 197).
* `BundledMPolyfold.formsD`: `d : Ωᵏ(Xⁱ) → Ωᵏ⁺¹(Xⁱ⁺¹)`; `formsD_formsMap`: it commutes with the
  maps of the directed system (4.4).
* `formsInftyD : Ωᵏ_∞(X) → Ωᵏ⁺¹_∞(X)`, the limit map ("passing to the limit", p. 197), with
  `formsInftyD_comp_formsInftyD` (`d² = 0`); `formsInftyGradedD` on `Ω*_∞(X) = ⊕ₖ Ωᵏ_∞(X)`, with
  `formsInftyGradedD_comp_self`.
* `scDeRham A k = ker d / im d` in degree `k` (Definition 4.4.6), `scDeRhamMk`,
  `scDeRhamMk_eq_iff`.

## Not formalized

The wedge product (so `Ω*_∞(X)` as a graded differential algebra), the pull-back `f^*` along
sc-smooth maps between M-polyfolds and `f^* ∘ d = d ∘ f^*` (p. 198), forms on `∂X`, the relative
complex `Ω*_∞(X, ∂X)`, and the restriction of sc-forms to finite-dimensional sub-M-polyfolds.
-/

open Set Function

noncomputable section

namespace Polyfold

variable {E F : ScBanach} {C O : Set (E 0)} {k : ℕ}

/-! ### The inclusion `E¹ → E` on retracts -/

lemma mapsTo_shiftIncl : MapsTo (E.shiftIncl 0) (E.lvlSet O 1) O := fun _ hx => hx

/-- The inclusion `O¹ → O` is sc-smooth between the retracts. -/
theorem isScSmoothRetractMap_shiftIncl (hO : IsScRetract E C O) :
    IsScSmoothRetractMap E.shift (E.lvlSet C 1) (E.lvlSet O 1) E C O (E.shiftIncl 0) :=
  E.shiftIncl.isScSmoothRetractMap hO.shift mapsTo_shiftIncl

/-- **The tangent map of an sc-operator on a retract** is the operator on both components:
`T(T|_O)(x, h) = (T x, T h)` on `TO`. -/
theorem retractTangentMap_scOperator (T : ScOperator E F) (hO : IsScRetract E C O)
    {O' : Set (F 0)} (hmaps : MapsTo (T 0) O O') {p : E.tangent 0}
    (hp : p ∈ retractTangent E C O) :
    retractTangentMap E C O (T 0) p = (T 1 p.1, T 0 p.2) := by
  obtain ⟨R, hR⟩ := hO
  have hf : IsScSmoothRetractMap E C O F univ O' (T 0) := T.isScSmoothRetractMap ⟨R, hR⟩ hmaps
  have hp1 : p.1 ∈ E.lvlSet R.U 1 := by
    have h := hp
    rw [← hR, retractTangent_eq] at h
    exact R.tangent_subset h
  have hpO : p.1 ∈ E.lvlSet O 1 := retractTangent_fst_mem ⟨R, hR⟩ hp
  have hid := retractTangentMap_id ⟨R, hR⟩ (f := _root_.id) (fun _ _ => rfl) hp
  rw [retractTangentMap_eqOn (isScSmoothRetractMap_id O) R hR hp] at hid
  rw [retractTangentMap_eqOn hf R hR hp]
  refine Prod.ext ?_ ?_
  · refine levelMap_eq_of_toBase_eq ?_
    rw [T.toBase_comm 1 p.1, Function.comp_apply, R.apply_eq_self_of_mem_retract (hR ▸ hpO)]
  · change scDeriv R.U (T 0 ∘ R) p.1 p.2 = T 0 p.2
    rw [scDeriv_comp R.isScDomain (isScDomain_univ _) R.isSc1
      ((T.isScSmooth (isScDomain_univ _)) 1).1 (mapsTo_univ _ _) hp1,
      ScOperator.scDeriv_eq _ (isScDomain_univ _) (mem_univ _)]
    exact congrArg (T 0) (congrArg Prod.snd hid)

/-- `⊕ₖ T(T|_O)(x, h₁, …, h_k) = (T x, T h₁, …, T h_k)` on `⊕ₖ TO`. -/
theorem retractWhitneyMap_scOperator (T : ScOperator E F) (hO : IsScRetract E C O)
    {O' : Set (F 0)} (hmaps : MapsTo (T 0) O O') {q : (E.whitney k) 0}
    (hq : q ∈ retractWhitney E C O k) :
    retractWhitneyMap E C O (T 0) k q =
      ScBanach.whitneyMk (T 1 q.1) fun i => T 0 (ScBanach.whitneyVec q i) := by
  unfold retractWhitneyMap
  rw [ScOperator.levelMap_eq]
  exact congrArg _ (funext fun i => congrArg Prod.snd
    (retractTangentMap_scOperator T hO hmaps (hq.2 i)))

/-- On `⊕ₖ T(O¹)`, `⊕ₖ T(O¹ → O)` is the inclusion `whitneyIncl`. -/
theorem retractWhitneyMap_shiftIncl (hO : IsScRetract E C O) {q : (E.shift.whitney k) 0}
    (hq : q ∈ retractWhitney E.shift (E.lvlSet C 1) (E.lvlSet O 1) k) :
    retractWhitneyMap E.shift (E.lvlSet C 1) (E.lvlSet O 1) (E.shiftIncl 0) k q =
      E.whitneyIncl k 0 q := by
  rw [retractWhitneyMap_scOperator E.shiftIncl hO.shift mapsTo_shiftIncl hq,
    ← whitneyMk_fst_vec (E.whitneyIncl k 0 q)]
  refine congrArg₂ ScBanach.whitneyMk rfl (funext fun i => ?_)
  rw [ScBanach.whitneyVec_whitneyIncl]
  rfl

/-! ### The local statement -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {φ : MChart X} {ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ}

/-- In a level chart `φ¹`, `d((ι^*ω)_{φ¹}) = d(ω_φ) ∘ (⊕_{k+1} T(O²) → ⊕_{k+1} T(O¹))`. -/
theorem chartD_formLower (hφ : P.IsChart φ) (hω : P.IsScForm k ω) (y₀ : P.Level 1)
    {q : (φ.model.E.shift.shift.whitney (k + 1)) 0}
    (hq : q ∈ retractWhitney φ.model.E.shift.shift
      (φ.model.E.shift.lvlSet (φ.model.E.lvlSet φ.model.C 1) 1)
      (φ.model.E.shift.lvlSet (φ.model.E.lvlSet φ.model.O 1) 1) (k + 1)) :
    chartD (P.shift_isChart hφ y₀) (formLower ω) q =
      chartD hφ ω (φ.model.E.shift.whitneyIncl (k + 1) 0 q) := by
  have hχ := P.shift_isChart hφ y₀
  have hO := φ.model.isScRetract
  have hR := chartRetraction_retract φ
  have hωφ := hω.isRetractScForm hφ
  have hlω : P.shift.IsScForm k (formLower ω) := formLower_mem_scForms hω
  have hlωχ := hlω.isRetractScForm hχ
  have key : ∀ R' : ScRetraction φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1),
      R'.retract = φ.model.E.lvlSet φ.model.O 1 →
      retractD R' (chartForm hχ (formLower ω)) q =
        retractD (chartRetraction φ) (chartForm hφ ω)
          (φ.model.E.shift.whitneyIncl (k + 1) 0 q) := by
    intro R' hR'
    have hσ : IsRetractScForm φ.model.E.shift (φ.model.E.lvlSet φ.model.C 1) R'.retract k
        (chartForm hχ (formLower ω)) := by
      rw [hR']; exact hlωχ
    have hq' : q ∈ retractWhitney φ.model.E.shift.shift
        (φ.model.E.shift.lvlSet (φ.model.E.lvlSet φ.model.C 1) 1)
        (φ.model.E.shift.lvlSet R'.retract 1) (k + 1) := by
      rw [hR']; exact hq
    have h1 : retractD R' (chartForm hφ ω ∘ retractWhitneyMap φ.model.E.shift
        (φ.model.E.lvlSet φ.model.C 1) (φ.model.E.lvlSet φ.model.O 1) (φ.model.E.shiftIncl 0) k) q =
        retractD R' (chartForm hχ (formLower ω)) q :=
      retractD_congr R' hσ (fun p hp => by
        rw [hR'] at hp
        rw [Function.comp_apply, retractWhitneyMap_shiftIncl hO hp]
        exact chartForm_formLower hφ ω y₀ hp) (R'.mem_whitneySet_of_mem hq')
    rw [← h1, retractD_comp_retractWhitneyMap R' hR' (chartRetraction φ) hR
      (isScSmoothRetractMap_shiftIncl hO) hωφ hq]
    congr 1
    have h2 : levelMap (φ.model.E.shiftIncl 0) 1 = φ.model.E.shift.shiftIncl 0 :=
      funext fun z => ScOperator.levelMap_eq _ 1 z
    rw [h2]
    exact retractWhitneyMap_shiftIncl hO.shift hq
  exact key (chartRetraction (levelChart hφ y₀)) (chartRetraction_retract _)

/-- **2021 p. 197: the exterior derivative commutes with the inclusion `X¹ → X`** (2017 p. 150;
preprint: before Definition 4.27) of the directed system (4.4): `d(ι^*ω) = ι^*(dω)` for `ω ∈ Ωᵏ(X)`,
as `(k + 1)`-forms on `X²` (`formLower` is the pull-back `ι^*`). -/
theorem extD_formLower (hω : ω ∈ P.scForms k) : extD (formLower ω) = formLower (extD ω) := by
  have hlω := formLower_mem_scForms hω
  funext x
  ext α
  set x₁ := P.shift.shift.levelVal 1 x
  have hφ := dChart_isChart x₁
  have hχ := P.shift_isChart hφ (P.shift.levelVal 1 x₁)
  have hx : P.shift.shift.levelVal 1 x ∈ (levelChart hχ x₁).source := mem_dLevelChart_source x₁
  have hx₁ : P.shift.levelVal 1 x₁ ∈ (levelChart hφ (P.shift.levelVal 1 x₁)).source :=
    mem_dLevelChart_source x₁
  rw [extD_apply hχ hlω x₁ hx α, formLower_apply,
    extD_apply hφ (mem_scForms.1 hω) (P.shift.levelVal 1 x₁) hx₁,
    chartD_formLower hφ (mem_scForms.1 hω) _ (whitneyMk_tangentChartMap_mem hχ x₁ hx α)]
  refine congrArg (chartD hφ ω) ?_
  refine (whitneyMk_fst_vec ((dChart x₁).model.E.shift.whitneyIncl (k + 1) 0 _)).symm.trans ?_
  refine congrArg₂ (ScBanach.whitneyMk (E := (dChart x₁).model.E.shift)) ?_ (funext fun i => ?_)
  · exact (ScBanach.whitneyIncl_fst _).trans
      (P.shift.shift.toBase_levelLift (P.shift.shift_isChart hχ x₁) hx (levelVal_mem x))
  · refine (ScBanach.whitneyVec_whitneyIncl _ i).trans ?_
    refine (congrArg _ (congrFun (ScBanach.whitneyVec_mk _ _) i)).trans ?_
    refine Eq.trans ?_
      (congrArg (fun β => (tangentChartMap hχ β).2) (coe_lowerFiberCLM_apply (α i))).symm
    exact (tangentChartMap_tangentLower_snd hχ (α i) hx x₁).symm

end MPolyfold

/-! ### `d` on `Ω*_∞(X)` -/

namespace BundledMPolyfold

universe v

variable (A : BundledMPolyfold.{v}) (k : ℕ)

/-- `Ωᵏ(Xⁱ)` is an additive group (stated directly: the generic search times out). -/
instance addCommGroup_forms (j i : ℕ) : AddCommGroup (A.forms j i) :=
  Submodule.addCommGroup _

/-- `Ωᵏ_∞(X)` is an additive group (stated directly: the generic search times out). -/
instance addCommGroup_formsInfty (j : ℕ) : AddCommGroup (A.formsInfty j) :=
  Module.DirectLimit.addCommGroup _ _

/-- `d : Ωᵏ(Xⁱ) → Ωᵏ⁺¹(Xⁱ⁺¹)` on the lifts of a bundled M-polyfold. -/
def formsD (i : ℕ) : A.forms k i →ₗ[ℝ] A.forms (k + 1) (i + 1) :=
  MPolyfold.extDₗ (A.lift i).P k

lemma coe_formsD (i : ℕ) (ω : A.forms k i) : (A.formsD k i ω).1 = MPolyfold.extD ω.1 := rfl

/-- `d` commutes with the steps `Ωᵏ(Xⁱ) → Ωᵏ(Xⁱ⁺¹)` of the directed system (4.4). -/
theorem formsD_formsStep (i : ℕ) (ω : A.forms k i) :
    A.formsD k (i + 1) (A.formsStep k i ω) = A.formsStep (k + 1) (i + 1) (A.formsD k i ω) :=
  Subtype.ext (MPolyfold.extD_formLower ω.2)

/-- `d` commutes with the maps `Ωᵏ(Xⁱ) → Ωᵏ(Xʲ)` of the directed system (4.4). -/
theorem formsD_formsMap {i j : ℕ} (h : i ≤ j) (ω : A.forms k i) :
    A.formsD k j (A.formsMap k i j h ω) =
      A.formsMap (k + 1) (i + 1) (j + 1) (Nat.succ_le_succ h) (A.formsD k i ω) := by
  induction j, h using Nat.le_induction with
  | base => rw [formsMap_self, formsMap_self]; rfl
  | succ j hij ih =>
    rw [formsMap_succ A k hij, LinearMap.comp_apply, formsD_formsStep, ih,
      formsMap_succ A (k + 1) (Nat.succ_le_succ hij), LinearMap.comp_apply]

/-- **2021 pp. 197–198: `d : Ωᵏ_∞(X) → Ωᵏ⁺¹_∞(X)`** (2017 p. 150; preprint: before Definition 4.27),
"passing to the limit": the map induced on the direct limits by `d : Ωᵏ(Xⁱ) → Ωᵏ⁺¹(Xⁱ⁺¹)`
(`formsD_formsMap`). -/
def formsInftyD : A.formsInfty k →ₗ[ℝ] A.formsInfty (k + 1) :=
  Module.DirectLimit.lift ℝ ℕ (fun i => ↥(A.forms k i)) (A.formsMap k)
    (fun i => (A.formsInftyOf (k + 1) (i + 1)).comp (A.formsD k i)) fun i j h ω => by
      simp only [LinearMap.comp_apply]
      rw [formsD_formsMap, formsInftyOf_formsMap]

theorem formsInftyD_of (i : ℕ) (ω : A.forms k i) :
    A.formsInftyD k (A.formsInftyOf k i ω) = A.formsInftyOf (k + 1) (i + 1) (A.formsD k i ω) :=
  Module.DirectLimit.lift_of _ _ _

/-- **2021 p. 198: `d² = 0` on `Ωᵏ_∞(X)`** (2017 p. 150; preprint: before Definition 4.27). -/
theorem formsInftyD_comp_formsInftyD :
    (A.formsInftyD (k + 1)).comp (A.formsInftyD k) = 0 := by
  refine Module.DirectLimit.hom_ext fun i => LinearMap.ext fun ω => ?_
  have h : A.formsD (k + 1) (i + 1) (A.formsD k i ω) = 0 := Subtype.ext (MPolyfold.extD_extD ω.2)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [formsInftyD_of, formsInftyD_of, h]
  exact LinearMap.map_zero _


/-- **2021 pp. 197–198: `d : Ω*_∞(X) → Ω*_∞(X)`** on the graded space `Ω*_∞(X) = ⊕ₖ Ωᵏ_∞(X)`, of
degree `+1`: `d` of `formsInftyD` in each degree. -/
def formsInftyGradedD : A.formsInftyGraded →ₗ[ℝ] A.formsInftyGraded :=
  DirectSum.toModule ℝ ℕ _ fun j =>
    (DirectSum.lof ℝ ℕ (fun j => A.formsInfty j) (j + 1)).comp (A.formsInftyD j)

theorem formsInftyGradedD_lof (j : ℕ) (ω : A.formsInfty j) :
    A.formsInftyGradedD (DirectSum.lof ℝ ℕ (fun j => A.formsInfty j) j ω) =
      DirectSum.lof ℝ ℕ (fun j => A.formsInfty j) (j + 1) (A.formsInftyD j ω) :=
  DirectSum.toModule_lof ℝ _ _

/-- **2021 p. 198: `d² = 0` on `Ω*_∞(X)`** (2017 p. 150; preprint: before Definition 4.27). -/
theorem formsInftyGradedD_comp_self : A.formsInftyGradedD.comp A.formsInftyGradedD = 0 := by
  refine DirectSum.linearMap_ext ℝ fun j => LinearMap.ext fun ω => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  have h : A.formsInftyD (j + 1) (A.formsInftyD j ω) = 0 :=
    LinearMap.congr_fun (A.formsInftyD_comp_formsInftyD j) ω
  rw [formsInftyGradedD_lof, formsInftyGradedD_lof, h]
  exact LinearMap.map_zero _

/-! ### The sc-de Rham cohomology (Definition 4.4.6) -/

/-- `d(Ωᵏ⁻¹_∞(X)) ⊆ Ωᵏ_∞(X)`, the image of `d` in degree `k` (`0` in degree `0`). -/
def formsInftyDRange : ∀ j : ℕ, Submodule ℝ (A.formsInfty j)
  | 0 => ⊥
  | j + 1 => LinearMap.range (A.formsInftyD j)

/-- `im d ⊆ ker d` (from `d² = 0`). -/
theorem formsInftyDRange_le_ker : ∀ j : ℕ, A.formsInftyDRange j ≤ LinearMap.ker (A.formsInftyD j)
  | 0 => bot_le
  | j + 1 => by
    rintro _ ⟨ω, rfl⟩
    exact LinearMap.congr_fun (A.formsInftyD_comp_formsInftyD j) ω

/-- **2021 Definition 4.4.6 (p. 198)** (2017: Definition 4.10; preprint: Definition 4.27): the
sc-de Rham cohomology `Hᵏ_sc(X) = ker d / im d` of the M-polyfold `X`, in degree `k`, a real
vector space.  The book writes `H*_sc(X)` for all degrees at once; it is read degree-wise. -/
abbrev scDeRham : Type _ :=
  LinearMap.ker (A.formsInftyD k) ⧸
    (A.formsInftyDRange k).comap (LinearMap.ker (A.formsInftyD k)).subtype

/-- The class in `Hᵏ_sc(X)` of a closed form `ω ∈ Ωᵏ_∞(X)`, `dω = 0`. -/
abbrev scDeRhamMk : LinearMap.ker (A.formsInftyD k) →ₗ[ℝ] A.scDeRham k :=
  Submodule.mkQ _

/-- Two closed forms have the same class iff they differ by an exact form. -/
theorem scDeRhamMk_eq_iff (ω τ : LinearMap.ker (A.formsInftyD k)) :
    A.scDeRhamMk k ω = A.scDeRhamMk k τ ↔
      (ω : A.formsInfty k) - (τ : A.formsInfty k) ∈ A.formsInftyDRange k :=
  Submodule.Quotient.eq _

end BundledMPolyfold

end Polyfold
