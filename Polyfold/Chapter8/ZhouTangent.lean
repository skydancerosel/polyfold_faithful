import Polyfold.Chapter7.Zhou
import Polyfold.Chapter8.TangentOrbit

/-!
# The Zhou property and tangent maps

The results on the Zhou property that use tangent maps of ep-groupoids: the natural representation
fixes the points and tangent vectors it should (`NaturalRep`), Lemma 7.4.6, Propositions 7.4.8,
7.4.10 and 7.4.22, Corollary 7.4.11, Theorems 7.4.13 and 7.4.24, Corollary 7.6.8, and the examples
built on them. The Zhou property is in `Chapter7/Zhou.lean`.
-/

set_option maxSynthPendingDepth 3
open Set Function Topology Filter
noncomputable section
namespace Polyfold
universe u
namespace EpGroupoid
variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
namespace NaturalRep
variable {X} {x : Obj} (R : X.NaturalRep x)

/-- **`T Γ(g, y) = TΦ(g)` on `T_yX`** (2021 p. 331 and Proposition 8.1.16's "by definition
`Tg = Tĝ(x)`"): Chapter 7's `tangentMor` (Definition 7.1.6, `Tt ∘ (Ts|T_φ𝐗)⁻¹`) of the morphism
`Γ(g, y)` is the tangent map of `Φ(g)` at `y`. -/
theorem tangentMor_Γ (g : X.Isotropy x) {v : X.PObj.TangentSpace} (hv : v ∈ R.tangentU) :
    X.tangentMor (R.Γ g (X.PObj.levelVal 1 (X.PObj.tangentProj v))) v = R.tΦ g v := by
  have h1 := X.tangentMor_tSrc (R.tΓ g v)
  rwa [R.tSrc_tΓ g hv, R.tBase_tΓ g hv, R.tTgt_tΓ g hv] at h1

/-- `Tg = TΦ(g)(x)` on `T_xX`. -/
theorem tangentMor_eq_tΦ (g : X.Isotropy x) {x₁ : X.PObj.Level 1}
    (hx₁ : X.PObj.levelVal 1 x₁ = x) {v : X.PObj.TangentSpace}
    (hv : v ∈ X.PObj.tangentFiber x₁) : X.tangentMor g.val v = R.tΦ g v := by
  have hpv : X.PObj.levelVal 1 (X.PObj.tangentProj v) = x := by
    rw [show X.PObj.tangentProj v = x₁ from hv, hx₁]
  have hvU : v ∈ R.tangentU := by
    change X.PObj.levelVal 1 (X.PObj.tangentProj v) ∈ R.U
    rw [hpv]; exact R.mem_U
  have h1 := R.tangentMor_Γ g hvU
  rwa [hpv, R.Γ_self] at h1

/-- **The encoding does not depend on the natural representation**: `TΦ(g)` on `T_xX` is the same
for all natural representations (it is `Tg`, defined without charts). -/
theorem tΦ_eq_tΦ (R' : X.NaturalRep x) (g : X.Isotropy x) {x₁ : X.PObj.Level 1}
    (hx₁ : X.PObj.levelVal 1 x₁ = x) {v : X.PObj.TangentSpace}
    (hv : v ∈ X.PObj.tangentFiber x₁) : R.tΦ g v = R'.tΦ g v :=
  (R.tangentMor_eq_tΦ g hx₁ hv).symm.trans (R'.tangentMor_eq_tΦ g hx₁ hv)

/-- `T Γ(g, z) = TΦ(g)` on `T_zX` for a smooth fixed point `z`. -/
theorem tangentMor_isoΓ (g : X.Isotropy x) {z : X.PObj.SmoothLevel}
    (hz : X.PObj.smoothVal z ∈ R.U) (hfix : R.Φ g (X.PObj.smoothVal z) = X.PObj.smoothVal z)
    {v : X.PObj.TangentSpace} (hv : v ∈ X.PObj.tangentFiber (X.PObj.smoothIncl z 1)) :
    X.tangentMor (R.isoΓ g hz hfix).val v = R.tΦ g v := by
  have hpv : X.PObj.levelVal 1 (X.PObj.tangentProj v) = X.PObj.smoothVal z := by
    rw [show X.PObj.tangentProj v = X.PObj.smoothIncl z 1 from hv]; rfl
  have hvU : v ∈ R.tangentU := by
    change X.PObj.levelVal 1 (X.PObj.tangentProj v) ∈ R.U
    rw [hpv]; exact hz
  have h1 := R.tangentMor_Γ g hvU
  rw [hpv] at h1
  exact h1

/-- `T_zX ⊆ TU(x)` for `z ∈ U(x)`. -/
theorem mem_tangentU_of_fiber {z : X.PObj.SmoothLevel} (hz : X.PObj.smoothVal z ∈ R.U)
    {v : X.PObj.TangentSpace} (hv : v ∈ X.PObj.tangentFiber (X.PObj.smoothIncl z 1)) :
    v ∈ R.tangentU := by
  change X.PObj.levelVal 1 (X.PObj.tangentProj v) ∈ R.U
  rw [show X.PObj.tangentProj v = X.PObj.smoothIncl z 1 from hv]; exact hz

/-- If `Φ(g)` is the identity on an open set `N ⊆ U(x)`, then `TΦ(g)` is the identity over `N`. -/
theorem tΦ_eq_self_of_eqOn {g : X.Isotropy x} {N : Set Obj} (hN : IsOpen N) (hNU : N ⊆ R.U)
    (hid : ∀ y ∈ N, R.Φ g y = y) {v : X.PObj.TangentSpace}
    (hv : v ∈ X.PObj.tangentPreimage N) : R.tΦ g v = v := by
  have hf := (R.isScDiffeoOn_Φ g).isScSmoothOn
  have h1 := MPolyfold.tangentMapOn_congr hf (hf.mono hN hNU) hN hNU subset_rfl
    (fun _ _ => rfl) hv
  change MPolyfold.tangentMapOn hf v = v
  rw [h1]
  exact MPolyfold.tangentMapOn_eqOn_id (hf.mono hN hNU) (fun y hy => hid y hy) hv

/-- **The closure step** shared by the proofs of 2021 Propositions 7.4.8 and 7.4.10: if `Φ(g)`
fixes the points over `S ⊆ X_∞` and `TΦ(g)` is the identity on their tangent spaces, the same holds
at every `z ∈ U(x)_∞` in the closure of `S` (with `p : TX → X¹` open). -/
theorem fix_and_tangent_of_mem_closure (hp : IsOpenMap X.PObj.tangentProj) (g : X.Isotropy x)
    {S : Set X.PObj.SmoothLevel}
    (hS : ∀ a ∈ S, X.PObj.smoothVal a ∈ R.U ∧ R.Φ g (X.PObj.smoothVal a) = X.PObj.smoothVal a ∧
      ∀ v ∈ X.PObj.tangentFiber (X.PObj.smoothIncl a 1), R.tΦ g v = v)
    {z : X.PObj.SmoothLevel} (hzU : X.PObj.smoothVal z ∈ R.U) (hz : z ∈ closure S) :
    R.Φ g (X.PObj.smoothVal z) = X.PObj.smoothVal z ∧
      ∀ v ∈ X.PObj.tangentFiber (X.PObj.smoothIncl z 1), R.tΦ g v = v := by
  refine ⟨eq_of_mem_closure_of_continuousAt (f := fun a => R.Φ g (X.PObj.smoothVal a))
    (((R.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn.continuousAt
      (R.isOpen_U.mem_nhds hzU)).comp X.PObj.continuous_smoothVal.continuousAt)
    X.PObj.continuous_smoothVal.continuousAt (fun a ha => (hS a ha).2.1) hz, ?_⟩
  intro v hv
  exact MPolyfold.eqOn_tangentFiber_of_mem_closure hp R.isOpen_tangentU
    (MPolyfold.continuousOn_tangentMapOn _) continuousOn_id hz
    (fun a ha w hw _ => (hS a ha).2.2 w hw) hv
    (R.mem_tangentU_of_fiber hzU hv)

/-- The tangent version of `eq_self_of_smooth_clopen`: the closure step is supplied by a statement
about `Γ(g, z)` with `T Γ(g, z) = id`. -/
theorem eq_self_of_smooth_tangent (hd : X.PObj.DenseSmooth) (hc : X.PObj.SmoothConnected)
    (hp : IsOpenMap X.PObj.tangentProj) (g : X.Isotropy x) {S : Set X.PObj.SmoothLevel}
    (hSo : IsOpen S) (hSne : S.Nonempty)
    (hS : ∀ a ∈ S, X.PObj.smoothVal a ∈ R.U ∧ R.Φ g (X.PObj.smoothVal a) = X.PObj.smoothVal a ∧
      ∀ v ∈ X.PObj.tangentFiber (X.PObj.smoothIncl a 1), R.tΦ g v = v)
    (hstep : ∀ z (hz : X.PObj.smoothVal z ∈ R.U)
      (hfix : R.Φ g (X.PObj.smoothVal z) = X.PObj.smoothVal z),
      (∀ v ∈ X.PObj.tangentFiber (X.PObj.smoothIncl z 1), X.tangentMor (R.isoΓ g hz hfix).val v = v)
        → z ∈ S) :
    ∀ y ∈ R.U, R.Φ g y = y :=
  R.eq_self_of_smooth_clopen hd hc g hSo hSne (fun a ha => ⟨(hS a ha).1, (hS a ha).2.1⟩)
    fun z hzU hz => by
      obtain ⟨hfix, htan⟩ := R.fix_and_tangent_of_mem_closure hp g hS hzU hz
      exact hstep z hzU hfix fun v hv => (R.tangentMor_isoΓ g hzU hfix hv).trans (htan v hv)

end NaturalRep

/-- **2021 Lemma 7.4.6, p. 331 (new in the 2021 edition)**: under (ZHOU), `Tg = id` on `(T_xX)_∞`
gives `g ∈ T_x^∞`, i.e. (ZHOU) ⇒ (ZHOU'), with the density of `(T_xX)_∞` in `T_xX`. -/
theorem lemma_7_4_6 (hZ : X.IsZhou) (hdt : X.PObj.DenseSmoothTangent) : X.IsZhou' := by
  intro y g hg
  refine X.trivialSubgroup_le_trivialSubgroupInf y (hZ y g fun v hv => ?_)
  obtain ⟨R, -⟩ := X.theorem_7_1_13 (X.PObj.smoothVal y) isOpen_univ (mem_univ _)
  have hx₁ : X.PObj.levelVal 1 (X.PObj.smoothIncl y 1) = X.PObj.smoothVal y := rfl
  have hvU : v ∈ R.tangentU := R.mem_tangentU_of_fiber R.mem_U hv
  rw [R.tangentMor_eq_tΦ g hx₁ hv]
  refine eq_of_mem_closure_of_continuousAt
    ((MPolyfold.continuousOn_tangentMapOn _).continuousAt (R.isOpen_tangentU.mem_nhds hvU))
    continuousAt_id (s := X.PObj.tangentFiber (X.PObj.smoothIncl y 1) ∩
      X.PObj.tangentPolyfold.smoothSet) (fun w hw => ?_) (hdt y hv)
  exact (R.tangentMor_eq_tΦ g hx₁ hw.1).symm.trans (hg w hw)

/-- **2021 Proposition 7.4.8, (ZHOU') ⇒ (ZHOU)**: the set of smooth `y ∈ U(x)` near which `ĝ = id`
in `X_∞` is open, nonempty and closed in the connected `U(x)_∞`. -/
theorem isZhou_of_isZhou' (hreg : X.PObj.SmoothRegular) (hZ : X.IsZhou') : X.IsZhou := by
  intro y g hg
  obtain ⟨R, -⟩ := X.theorem_7_1_13 (X.PObj.smoothVal y) isOpen_univ (mem_univ _)
  have hgi : g ∈ X.trivialSubgroupInf y := hZ y g fun v hv => hg v hv.1
  set S := {z : X.PObj.SmoothLevel | ∀ᶠ w in 𝓝 z,
    X.PObj.smoothVal w ∈ R.U ∧ R.Φ g (X.PObj.smoothVal w) = X.PObj.smoothVal w}
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hUo : IsOpen (X.PObj.smoothVal ⁻¹' R.U) := R.isOpen_U.preimage X.PObj.continuous_smoothVal
  have hall := R.eq_self_of_smooth_tangent hreg.denseSmooth hreg.smoothConnected
    hreg.isOpenMap_tangentProj g hSo ⟨y, ?_⟩ (fun a ha => ?_) (fun z hz hfix htan => ?_)
  · exact R.actsTrivially_iff.2 (Filter.mem_of_superset (R.isOpen_U.mem_nhds R.mem_U) hall)
  · exact Filter.Eventually.and (hUo.mem_nhds R.mem_U) ((X.mem_trivialSubgroupInf_iff R).1 hgi)
  · refine ⟨ha.self_of_nhds.1, ha.self_of_nhds.2, fun v hv => ?_⟩
    exact hreg.tangentDeterminedSmooth.eq_self (R.isScDiffeoOn_Φ g).isScSmoothOn a
      ha.self_of_nhds.1 (ha.mono fun w hw => hw.2) hv
  · obtain ⟨R', -⟩ := X.theorem_7_1_13 (X.PObj.smoothVal z) isOpen_univ (mem_univ _)
    have hh := (X.mem_trivialSubgroupInf_iff R').1
      (hZ z (R.isoΓ g hz hfix) fun v hv => htan v hv.1)
    filter_upwards [hh, X.PObj.continuous_smoothVal.continuousAt.eventually
      (R.eventually_Φ_eq_Γ R' hz g (R.isoΓ g hz hfix) rfl)] with w hw1 hw2
    exact ⟨hw2.1, hw2.2.2 ▸ hw1⟩

/-- **2021 Proposition 7.4.8, p. 332 (new in the 2021 edition)**: (ZHOU) ⇔ (ZHOU'), given the
Part I facts. -/
theorem proposition_7_4_8 (hreg : X.PObj.SmoothRegular) (hdt : X.PObj.DenseSmoothTangent) :
    X.IsZhou ↔ X.IsZhou' :=
  ⟨fun h => X.lemma_7_4_6 h hdt, X.isZhou_of_isZhou' hreg⟩

/-- **2021 Proposition 7.4.10, p. 333 (new in the 2021 edition)**: (ZHOU) ⇒ (LUC). -/
theorem proposition_7_4_10 (hreg : X.PObj.SmoothRegular) (hZ : X.IsZhou) : X.IsLUC := by
  rw [isLUC_iff_forall_naturalRep]
  intro x R g V hVo hVne hVU hV
  set S := X.PObj.smoothVal ⁻¹' {w : Obj | ∀ᶠ w' in 𝓝 w, w' ∈ R.U ∧ R.Φ g w' = w'}
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhds.preimage X.PObj.continuous_smoothVal
  obtain ⟨w, hwV, hws⟩ := hreg.denseSmooth.dense.inter_open_nonempty V hVo hVne
  refine R.eq_self_of_smooth_tangent hreg.denseSmooth hreg.smoothConnected
    hreg.isOpenMap_tangentProj g hSo ⟨X.PObj.smoothMk w hws, ?_⟩ (fun a ha => ?_)
    (fun z hz hfix htan => ?_)
  · filter_upwards [hVo.mem_nhds hwV] with w' hw' using ⟨hVU hw', hV w' hw'⟩
  · obtain ⟨N, hNs, hNo, haN⟩ := mem_nhds_iff.1 ha
    refine ⟨(hNs haN).1, (hNs haN).2, fun v hv => R.tΦ_eq_self_of_eqOn hNo (fun y hy => (hNs hy).1)
      (fun y hy => (hNs hy).2) ?_⟩
    change X.PObj.levelVal 1 (X.PObj.tangentProj v) ∈ N
    rw [show X.PObj.tangentProj v = X.PObj.smoothIncl a 1 from hv]; exact haN
  · have hh := (R.isoΓ_mem_trivialSubgroup_iff g hz hfix).1 (hZ z _ htan)
    exact Filter.Eventually.and (R.isOpen_U.mem_nhds hz) hh

/-- (ZHOU) gives unique continuation through `X_∞` (the proof of 2021 Proposition 7.4.10 started
from an `X_∞`-open set). -/
theorem isSmoothUC_of_isZhou (hreg : X.PObj.SmoothRegular) (hZ : X.IsZhou) : X.IsSmoothUC := by
  intro x R g W hWo hWne hW
  set S := {z : X.PObj.SmoothLevel | ∀ᶠ w in 𝓝 z,
    X.PObj.smoothVal w ∈ R.U ∧ R.Φ g (X.PObj.smoothVal w) = X.PObj.smoothVal w}
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hUo : IsOpen (X.PObj.smoothVal ⁻¹' R.U) := R.isOpen_U.preimage X.PObj.continuous_smoothVal
  obtain ⟨w₀, hw₀⟩ := hWne
  refine R.eq_self_of_smooth_tangent hreg.denseSmooth hreg.smoothConnected
    hreg.isOpenMap_tangentProj g hSo ⟨w₀, ?_⟩ (fun a ha => ?_) (fun z hz hfix htan => ?_)
  · filter_upwards [hWo.mem_nhds hw₀] with w hw using hW w hw
  · refine ⟨ha.self_of_nhds.1, ha.self_of_nhds.2, fun v hv => ?_⟩
    exact hreg.tangentDeterminedSmooth.eq_self (R.isScDiffeoOn_Φ g).isScSmoothOn a
      ha.self_of_nhds.1 (ha.mono fun w hw => hw.2) hv
  · have hh := (R.isoΓ_mem_trivialSubgroup_iff g hz hfix).1 (hZ z _ htan)
    exact Filter.Eventually.and (hUo.mem_nhds hz)
      (X.PObj.continuous_smoothVal.continuousAt.eventually hh)

/-- **2021 Corollary 7.4.11, p. 334 (new in the 2021 edition), for `X⁰` and `X¹`**: (ZHOU) gives
(LUC) for `X` and for `X¹`. -/
theorem corollary_7_4_11 (hreg : X.PObj.SmoothRegular) (hZ : X.IsZhou) :
    X.IsLUC ∧ X.liftOne.IsLUC :=
  ⟨X.proposition_7_4_10 hreg hZ,
    X.isLUC_liftOne_of_isSmoothUC hreg.denseSmooth (X.isSmoothUC_of_isZhou hreg hZ)⟩

/-- **2021 Corollary 7.4.11 for all `i`**, with (ZHOU) for every `Xⁱ` (the conclusion of
Proposition 7.4.9, `EP.proposition_7_4_9_of_isZhou` in `SmoothRegularAssembly.lean`) as a
hypothesis. -/
theorem corollary_7_4_11_lift (A : EP.{u}) (hZ : ∀ i, (A.lift i).X.IsZhou)
    (hreg : ∀ i, (A.lift i).X.PObj.SmoothRegular) (i : ℕ) : (A.lift i).X.IsLUC :=
  (A.lift i).X.proposition_7_4_10 (hreg i) (hZ i)

/-- **2021 Theorem 7.4.13, p. 334 (new in the 2021 edition)**: (ZHOU) ⇒ (SLUC), with (ZHOU) for
every `Xⁱ` (Proposition 7.4.9) as a hypothesis. -/
theorem theorem_7_4_13 (A : EP.{u}) (hZ : ∀ i, (A.lift i).X.IsZhou)
    (hreg : ∀ i, (A.lift i).X.PObj.SmoothRegular) : A.IsSLUC :=
  corollary_7_4_11_lift A hZ hreg

/-- (ZHOU) ⇒ (VSLUC). -/
theorem isVSLUC_of_isZhou (hreg : X.PObj.SmoothRegular) (hZ : X.IsZhou) : X.IsVSLUC :=
  X.isVSLUC_of_isSmoothUC (X.isSmoothUC_of_isZhou hreg hZ)

/-- **2021 Corollary 7.6.8, p. 351**, with its hypothesis "(ZHOU) ⇒ (LUC) for `X¹`" discharged by
Corollary 7.4.11 (`corollary_7_4_11`). -/
theorem corollary_7_6_8_of_isZhou (hZ : X.IsZhou) (hreg : X.PObj.SmoothRegular)
    (hR : X.HasConnectedDenseLevelOneReps) :
    ∃ hT : X.liftOne.nonEffectivePart = X.PMor.levelVal 1 ⁻¹' X.nonEffectivePart,
      (∀ φ, X.reducedLevelOneMap hT (X.liftOne.reducedπ φ) = X.reducedπ (X.PMor.levelVal 1 φ)) ∧
      Injective (X.reducedLevelOneMap hT) ∧ Continuous (X.reducedLevelOneMap hT) ∧
      range (X.reducedLevelOneMap hT) = X.reducedπ '' X.PMor.levelSet 1 :=
  X.corollary_7_6_8 hZ (fun h => (X.corollary_7_4_11 hreg h).2) hR

end EpGroupoid

namespace EpGroupoid.Examples

/-- The hypotheses of `theorem_7_4_13` are satisfiable. -/
theorem theorem_7_4_13_pointEP : pointEP.IsSLUC :=
  theorem_7_4_13 pointEP isZhou_lift_pointEP smoothRegular_lift_pointEP

end EpGroupoid.Examples

namespace EpGroupoid.Examples.JumpingRetract

/-- **2021 p. 331**: the ep-groupoid of Appendix 7.6.3 (our `JumpingRetract.X`) does not satisfy
(ZHOU), given the Part I facts for its object M-polyfold: it does not have (LUC)
(`JumpingRetract.not_isLUC`), and (ZHOU) ⇒ (LUC). -/
theorem not_isZhou (hreg : X.PObj.SmoothRegular) : ¬ X.IsZhou := fun h =>
  not_isLUC (X.proposition_7_4_10 hreg h)

end EpGroupoid.Examples.JumpingRetract

namespace EpGroupoid
variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
namespace NaturalRep
variable {X} {x : Obj} (R : X.NaturalRep x)

/-- Under (ZHOU) and (LUC), `ĝ` and `ĝ'` agree on `U(x)` as soon as they agree to first order at a
smooth point. -/
theorem eqOn_Φ_of_tangent (hZ : X.IsZhou) (hL : R.HasLUC) {g g' : X.Isotropy x}
    {z : X.PObj.SmoothLevel} (hz : X.PObj.smoothVal z ∈ R.U)
    (hzz : R.Φ g (X.PObj.smoothVal z) = R.Φ g' (X.PObj.smoothVal z))
    (ht : ∀ v ∈ X.PObj.tangentFiber (X.PObj.smoothIncl z 1), R.tΦ g v = R.tΦ g' v) :
    ∀ y ∈ R.U, R.Φ g y = R.Φ g' y := by
  have hfix : R.Φ (g'⁻¹ * g) (X.PObj.smoothVal z) = X.PObj.smoothVal z := by
    rw [R.Φ_mul _ _ _ hz, hzz, R.Φ_inv_Φ g' hz]
  have htan : ∀ v ∈ X.PObj.tangentFiber (X.PObj.smoothIncl z 1),
      X.tangentMor (R.isoΓ (g'⁻¹ * g) hz hfix).val v = v := by
    intro v hv
    have hvU := R.mem_tangentU_of_fiber hz hv
    rw [R.tangentMor_isoΓ _ hz hfix hv, R.tΦ_mul _ _ hvU, ht v hv, ← R.tΦ_mul _ _ hvU,
      inv_mul_cancel, R.tΦ_one hvU]
  have hev := (R.isoΓ_mem_trivialSubgroup_iff _ hz hfix).1 (hZ z _ htan)
  obtain ⟨N, hNs, hNo, hzN⟩ := mem_nhds_iff.1 (Filter.inter_mem hev (R.isOpen_U.mem_nhds hz))
  have hid := hL (g'⁻¹ * g) N hNo ⟨_, hzN⟩ (fun y hy => (hNs hy).2) (fun y hy => (hNs hy).1)
  intro y hy
  rw [← mul_inv_cancel_left g' g, R.Φ_mul _ _ _ hy, hid y hy]

/-- The proof of 2021 Proposition 7.4.22: under (ZHOU), every sc-diffeomorphism `β` of `U(x)` with
`|β(y)| = |y|` is some `ĝ`. -/
theorem exists_eq_Φ_of_isZhou (hreg : X.PObj.SmoothRegular) (hZ : X.IsZhou)
    {β β' : Obj → Obj} (hβ : X.PObj.IsScDiffeoOn X.PObj β β' R.U R.U)
    (hπ : ∀ y ∈ R.U, X.π (β y) = X.π y) : ∃ g : X.Isotropy x, ∀ y ∈ R.U, β y = R.Φ g y := by
  classical
  have : Fintype (X.Isotropy x) := Fintype.ofFinite _
  have hL : R.HasLUC := X.isLUC_iff_forall_naturalRep.1 (X.proposition_7_4_10 hreg hZ) x R
  have hβc : ContinuousOn β R.U := hβ.isScSmoothOn.continuousOn
  have hsv : Continuous X.PObj.smoothVal := X.PObj.continuous_smoothVal
  have hZo : IsOpen (X.PObj.smoothVal ⁻¹' R.U) := R.isOpen_U.preimage hsv
  set Z := X.PObj.smoothVal ⁻¹' R.U with hZdef
  let Sg : X.Isotropy x → Set X.PObj.SmoothLevel := fun g => {z | ∀ᶠ w in 𝓝 z,
    X.PObj.smoothVal w ∈ R.U ∧ β (X.PObj.smoothVal w) = R.Φ g (X.PObj.smoothVal w)}
  have hcβ : ∀ z ∈ Z, ContinuousAt (fun w => β (X.PObj.smoothVal w)) z := fun z hz =>
    (hβc.continuousAt (R.isOpen_U.mem_nhds hz)).comp hsv.continuousAt
  have hcΦ : ∀ g, ∀ z ∈ Z, ContinuousAt (fun w => R.Φ g (X.PObj.smoothVal w)) z := fun g z hz =>
    ((R.continuousOn_Φ g).continuousAt (R.isOpen_U.mem_nhds hz)).comp hsv.continuousAt
  -- at a point of `cl Σ_g`, `β = Φ(g)` to first order
  have hL2 : ∀ g, ∀ z ∈ Z, z ∈ closure (Sg g) →
      β (X.PObj.smoothVal z) = R.Φ g (X.PObj.smoothVal z) ∧
      ∀ v ∈ X.PObj.tangentFiber (X.PObj.smoothIncl z 1),
        MPolyfold.tangentMapOn hβ.isScSmoothOn v = R.tΦ g v := by
    intro g z hz hzc
    refine ⟨eq_of_mem_closure_of_continuousAt (f := fun w => β (X.PObj.smoothVal w))
      (g := fun w => R.Φ g (X.PObj.smoothVal w)) (hcβ z hz) (hcΦ g z hz)
      (fun a ha => ha.self_of_nhds.2) hzc, fun v hv => ?_⟩
    exact MPolyfold.eqOn_tangentFiber_of_mem_closure hreg.isOpenMap_tangentProj R.isOpen_tangentU
      (MPolyfold.continuousOn_tangentMapOn _) (MPolyfold.continuousOn_tangentMapOn _) hzc
      (fun a ha w hw _ => hreg.tangentDeterminedSmooth β (R.Φ g) R.U R.U hβ.isScSmoothOn
        (R.isScDiffeoOn_Φ g).isScSmoothOn a ha.self_of_nhds.1 ha.self_of_nhds.1
        (ha.mono fun w hw => hw.2) w hw) hv (R.mem_tangentU_of_fiber hz hv)
  have hL3 : ∀ g g', ∀ z ∈ Z, z ∈ closure (Sg g) → z ∈ closure (Sg g') →
      ∀ y ∈ R.U, R.Φ g y = R.Φ g' y := by
    intro g g' z hz hg hg'
    obtain ⟨h1, h2⟩ := hL2 g z hz hg
    obtain ⟨h1', h2'⟩ := hL2 g' z hz hg'
    exact R.eqOn_Φ_of_tangent hZ hL hz (h1.symm.trans h1')
      fun v hv => (h2 v hv).symm.trans (h2' v hv)
  have hcov : ∀ y ∈ R.U, ∃ g, β y = R.Φ g y := fun y hy =>
    R.exists_Φ_eq_of_π_eq hy (hβ.mapsTo hy) (hπ y hy)
  -- a finite closed cover has a member with nonempty interior in every nonempty open set
  have hL5 : ∀ S : Finset (X.Isotropy x), ∀ N : Set X.PObj.SmoothLevel, IsOpen N →
      N.Nonempty → N ⊆ Z → (∀ w ∈ N, ∃ g ∈ S, β (X.PObj.smoothVal w) = R.Φ g (X.PObj.smoothVal w))
      → ∃ g, ∃ N₁ : Set X.PObj.SmoothLevel, IsOpen N₁ ∧ N₁.Nonempty ∧ N₁ ⊆ N ∧
        ∀ w ∈ N₁, β (X.PObj.smoothVal w) = R.Φ g (X.PObj.smoothVal w) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rintro N - ⟨w, hw⟩ - hN
      obtain ⟨g, hg, -⟩ := hN w hw
      exact absurd hg (Finset.notMem_empty g)
    | insert g S hgS ih =>
      intro N hNo hNne hNZ hN
      by_cases hall : ∀ w ∈ N, β (X.PObj.smoothVal w) = R.Φ g (X.PObj.smoothVal w)
      · exact ⟨g, N, hNo, hNne, subset_rfl, hall⟩
      push Not at hall
      obtain ⟨w₀, hw₀N, hw₀⟩ := hall
      have hN₂o : IsOpen (N ∩ (fun w => (β (X.PObj.smoothVal w), R.Φ g (X.PObj.smoothVal w))) ⁻¹'
          (diagonal Obj)ᶜ) :=
        ContinuousOn.isOpen_inter_preimage (fun w hw =>
          ((hcβ w (hNZ hw)).prodMk (hcΦ g w (hNZ hw))).continuousWithinAt) hNo
          isClosed_diagonal.isOpen_compl
      obtain ⟨g', N₁, h1, h2, h3, h4⟩ := ih _ hN₂o ⟨w₀, hw₀N, hw₀⟩ (fun w hw => hNZ hw.1)
        (fun w hw => by
          obtain ⟨g'', hg'', heq⟩ := hN w hw.1
          rcases Finset.mem_insert.1 hg'' with rfl | hS
          · exact absurd heq hw.2
          · exact ⟨g'', hS, heq⟩)
      exact ⟨g', N₁, h1, h2, h3.trans inter_subset_left, h4⟩
  have hdense : Z ⊆ closure (⋃ g, Sg g) := by
    intro z hz
    refine mem_closure_iff.2 fun N hNo hzN => ?_
    obtain ⟨g, N₁, h1, ⟨w, hw⟩, h3, h4⟩ := hL5 Finset.univ (N ∩ Z) (hNo.inter hZo)
      ⟨z, hzN, hz⟩ inter_subset_right
      (fun w hw => let ⟨g, hg⟩ := hcov _ hw.2; ⟨g, Finset.mem_univ g, hg⟩)
    refine ⟨w, (h3 hw).1, mem_iUnion.2 ⟨g, ?_⟩⟩
    filter_upwards [h1.mem_nhds hw] with w' hw' using ⟨(h3 hw').2, h4 w' hw'⟩
  obtain ⟨y₀, hy₀U, hy₀s⟩ :=
    hreg.denseSmooth.dense.inter_open_nonempty R.U R.isOpen_U ⟨x, R.mem_U⟩
  have hz₀ : X.PObj.smoothMk y₀ hy₀s ∈ Z := hy₀U
  obtain ⟨w₀, hw₀Z, hw₀S⟩ := mem_closure_iff.1 (hdense hz₀) Z hZo hz₀
  obtain ⟨g₀, hg₀⟩ := mem_iUnion.1 hw₀S
  let K : Set (X.Isotropy x) := {g | ∀ y ∈ R.U, R.Φ g y = R.Φ g₀ y}
  have hclK : IsClosed (⋃ g ∈ K, closure (Sg g)) :=
    (Set.toFinite K).isClosed_biUnion fun g _ => isClosed_closure
  have hclK' : IsClosed (⋃ g ∈ Kᶜ, closure (Sg g)) :=
    (Set.toFinite Kᶜ).isClosed_biUnion fun g _ => isClosed_closure
  have hZcov : Z ⊆ (⋃ g ∈ K, closure (Sg g)) ∪ ⋃ g ∈ Kᶜ, closure (Sg g) := by
    intro z hz
    have h := hdense hz
    rw [closure_iUnion_of_finite] at h
    obtain ⟨g, hg⟩ := mem_iUnion.1 h
    by_cases hgK : g ∈ K
    · exact Or.inl (mem_biUnion hgK hg)
    · exact Or.inr (mem_biUnion hgK hg)
  have hZK' : ∀ z ∈ Z, z ∉ ⋃ g ∈ Kᶜ, closure (Sg g) := by
    intro z hz hz'
    obtain ⟨z', hz'Z, hz'K, hz'K'⟩ := isPreconnected_closed_iff.1
      (hreg.smoothConnected R.U R.isOpen_U R.isConnected_U) _ _ hclK hclK' hZcov
      ⟨w₀, hw₀Z, mem_biUnion (show g₀ ∈ K from fun _ _ => rfl) (subset_closure hg₀)⟩ ⟨z, hz, hz'⟩
    obtain ⟨g, hgK, hg⟩ := mem_iUnion₂.1 hz'K
    obtain ⟨g', hg'K, hg'⟩ := mem_iUnion₂.1 hz'K'
    exact hg'K fun y hy => (hL3 g g' z' hz'Z hg hg' y hy).symm.trans (hgK y hy)
  refine ⟨g₀, ?_⟩
  have hsm : EqOn β (R.Φ g₀) (R.U ∩ X.PObj.smoothSet) := by
    intro y hy
    have hz : X.PObj.smoothMk y hy.2 ∈ Z := hy.1
    rcases hZcov hz with h | h
    · obtain ⟨g, hgK, hg⟩ := mem_iUnion₂.1 h
      exact (hL2 g _ hz hg).1.trans (hgK y hy.1)
    · exact absurd h (hZK' _ hz)
  have hall : EqOn β (R.Φ g₀) R.U := hsm.of_subset_closure hβc (R.continuousOn_Φ g₀)
    inter_subset_left (hreg.denseSmooth.subset_closure_inter R.isOpen_U)
  exact fun y hy => hall hy

end NaturalRep

/-- **2021 Proposition 7.4.22, p. 338 (new in the 2021 edition)**: (ZHOU) ⇒ (LR). -/
theorem proposition_7_4_22 (hreg : X.PObj.SmoothRegular) (hZ : X.IsZhou) : X.IsLR := by
  intro x O hO hxO
  obtain ⟨R, hRO⟩ := X.theorem_7_1_13 x hO hxO
  exact ⟨R, hRO, fun β β' hβ hπ => R.exists_eq_Φ_of_isZhou hreg hZ hβ hπ⟩

end EpGroupoid

namespace EpGroupoid

/-- **2021 Theorem 7.4.24, p. 340 (new in the 2021 edition)**: (ZHOU) ⇒ (SLR), with (ZHOU) for
every `Xⁱ` (Proposition 7.4.9) as a hypothesis. -/
theorem theorem_7_4_24 (A : EP.{u}) (hZ : ∀ i, (A.lift i).X.IsZhou)
    (hreg : ∀ i, (A.lift i).X.PObj.SmoothRegular) : A.IsSLR := fun i =>
  (A.lift i).X.proposition_7_4_22 (hreg i) (hZ i)

/-- **Witness** for (SLR) and (LR): the point ep-groupoid. -/
theorem Examples.isSLR_pointEP : Examples.pointEP.IsSLR :=
  theorem_7_4_24 _ Examples.isZhou_lift_pointEP Examples.smoothRegular_lift_pointEP

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
namespace Examples

/-- The hypotheses of `proposition_7_4_8` are satisfiable. -/
theorem proposition_7_4_8_point : pointEpGroupoid.IsZhou ↔ pointEpGroupoid.IsZhou' :=
  pointEpGroupoid.proposition_7_4_8 MPolyfold.smoothRegular_discrete_unit
    MPolyfold.denseSmoothTangent_discrete_unit

/-- The hypotheses of `corollary_7_6_8_of_isZhou` are satisfiable. -/
theorem corollary_7_6_8_of_isZhou_point :
    ∃ hT : pointEpGroupoid.liftOne.nonEffectivePart =
        pointEpGroupoid.PMor.levelVal 1 ⁻¹' pointEpGroupoid.nonEffectivePart,
      Injective (pointEpGroupoid.reducedLevelOneMap hT) := by
  obtain ⟨hT, -, hinj, -⟩ := pointEpGroupoid.corollary_7_6_8_of_isZhou
    (isZhou_trivial _) MPolyfold.smoothRegular_discrete_unit hasConnectedDenseLevelOneReps_point
  exact ⟨hT, hinj⟩

end Examples
end EpGroupoid
end Polyfold
end
