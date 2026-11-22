import Polyfold.Chapter18.HalfSpaceWitnesses
import Polyfold.Chapter18.AuxiliaryNormsDirect
import Polyfold.Chapter15.TransversalExtensionBoundaryDatum

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18:
**boundary data with non-empty domain support** on the strong polyfold bundle construction
`ℤ/2 ⋉ (H × ℝ) → ℤ/2 ⋉ H` of `HalfSpaceBundleConstruction.lean`, for Theorem 18.4.4 (p. 855),
Theorem 15.3.9 in the polyfold context (§18.6, p. 861), and Theorem 18.1.12 (3) (p. 848).
Numbers and pages are the 2021 text's.

# The constant boundary datum `(α, −3/4)` on `ℤ/2 ⋉ [0, ∞) × ℝ`

`C = ℤ/2 ⋉ H`, `H = [0, ∞) × ℝ`, `−1` acting by `(a, y) ↦ (a, −y)` and trivially on the fibres
`ℝ`; `∂C = {(0, y)}`, the corner `(0, 0) ∈ ∂C` has isotropy `ℤ/2`.  Since the fibre action is
trivial, the constant section `α ↦ (α, v)` is equivariant and its multisection functor
`Λ_v(α, w) = 1_{w = v}` (`constFunctor`) is a functor.

## What is formalized

* General (namespace `SBLocalization`): if the multisection `Λ_s` of an sc⁺-section `s` is a
  functor, then `s` is equivariant (`fibAct_eq_of_isWFunctor_sectionMulti`), `Λ_s` is an
  sc⁺-multisection (`isScPlusMultisection_sectionMulti_of_isWFunctor`) and is structurable over
  `∂X` (Definition 14.1.7, `isBoundaryStructurable_sectionMulti_of_isWFunctor`: `I_x = {∗}`,
  `s_∗ = s`, `τ ≡ [{∗} ← {∗} → {∗}]`).  An auxiliary norm over `∂X` depends only on its values over
  `∂X` (`isAuxNormOn_boundary_congr`), and so does an auxiliary norm on `E|∂C` in the sense of
  Theorem 18.1.12 (3) (`IsBoundaryAuxNormIn.congr_boundary`,
  `IsReflexiveBoundaryAuxNormIn.congr_boundary`).
* The model section `modelConstSec v` (sc⁺, `isScPlusSection_modelConstSec`), with
  `Γ̄^*Λ_v = Λ_{modelConstSec v}` (`bundlePull_constFunctor`); `Λ_v` is structurable over `∂C`
  (`isBoundaryStructurableFunctor_constFunctor`); for `v ≠ 0`,
  `|dom-supp(Λ_v|∂C)| = cl |∂C|` (`orbitBoundaryDomSupp_constFunctor`), containing the corner;
  `N(Λ_v)(α) = N(α, v)`.
* The auxiliary norm `N(α, w) = |w|` (`halfNorm`, `isAuxNormFunctor_halfNorm`): every auxiliary
  norm is `N₀(α, w) = |w| N₀(α, 1)` (the fibres are `ℝ`), and `|w| = N₀(α, w) / N₀(α, 1)` with a
  continuous positive weight; `(N, |C|)` controls the compactness of
  `f(a, y) = ((a, y), a² + y² − 1)` (`halfF_controlsCompactness_halfNorm`).
* **`theorem_18_4_4_modelFree_witness_constDatum`**: Theorem 18.4.4 for `Λ_v`, `v = −3/4`,
  `N = |·|`, `U = |C|`, `β = 1`: `N(Λ_v) = 3/4 < 1` on the non-empty `|dom-supp(Λ_v|∂C)|`, and the
  extension `Λ'` charges `(α, −3/4)` at every `α ∈ ∂C`.
* `isBoundaryFaceOnto_model_constFunctor`, `isBoundaryFaceOntoFunctor_constFunctor`: the boundary
  hypothesis of Theorem 15.3.9 for `(f, Λ_v)`, checked at the boundary points `(0, ±1/2)` where
  `f(x) = (x, −3/4)`, through the local strong bundle isomorphism of the model piece and
  Chapter 15's `isReducedOntoAtPt_halfDisc_constMulti`.
* **`theorem_15_3_9_categorical_witness_constDatum`**: Theorem 15.3.9 in the polyfold context for
  `f`, `Λ_v`, `N = |·|`, `U = |C|`, `h = 1`, with `Λ_v ∘ f > 0` at `(0, 1/2) ∈ ∂C`.
* **`theorem_18_1_12_three_witness_boundary`**,
  **`theorem_18_1_12_three_reflexive_witness_boundary`**:
  Theorem 18.1.12 (3) for `N` over `∂C` and `+∞` elsewhere (`boundaryOnly`), an auxiliary norm on
  `E|∂C` which is not an auxiliary norm of `P` (`not_isAuxNormFunctor_boundaryOnly`); the extension
  `Ñ` agrees with `N` on the non-empty `E|∂C` (for `N = |·|`: `Ñ(α, w) = |w|` at every `α ∈ ∂C`).

## Readings

* The boundary datum `Λ : E|∂C → ℚ⁺` of Theorems 18.4.4 and 15.3.9 is read as in
  `PerturbationModelIndependence.lean` (`IsBoundaryStructurableFunctor`); `Λ_v` is given on all
  of `E`, and only its values over `∂C` enter.
* The auxiliary norm on `E|∂C` of Theorem 18.1.12 (3) is read as in `AuxiliaryNormsDirect.lean`
  (`IsBoundaryAuxNormIn`, in the covering model `halfSingle`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace Filter
open scoped ContDiff ENNReal

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-- If `Λ_s` is a functor, `s` is equivariant: `μ(ψ, s(s(ψ))) = s(t(ψ))`. -/
theorem fibAct_eq_of_isWFunctor_sectionMulti {s : A.Obj → A.W} (hs : IsSection A.P s)
    (hW : IsWFunctor A (sectionMulti s)) (ψ : A.Mor) :
    fibAct ψ (s (A.X.src ψ)) = s (A.X.tgt ψ) := by
  have hP : A.P (s (A.X.src ψ)) = A.X.src ψ := hs _
  have h := hW ⟨(ψ, s (A.X.src ψ)), hP⟩
  rw [← fibAct_of hP] at h
  have hpos : 0 < sectionMulti s (fibAct ψ (s (A.X.src ψ))) := by
    rw [h]
    change 0 < sectionMulti s (s (A.X.src ψ))
    rw [sectionMulti_apply_self hs]
    exact one_pos
  exact ((sectionMulti_pos_iff s _).1 hpos).trans (congrArg s (P_fibAct hP))

variable {s : A.Obj → A.W} (hs : A.B.IsScPlusSection s) (hW : IsWFunctor A (sectionMulti s))

include hs hW in
/-- The structure `I_x = {∗}`, `s_∗ = s` of `Λ_s` over `∂X` on a natural neighbourhood. -/
def equivariantBoundaryStructure {x : A.Obj} (V : A.X.NatNbhd x) :
    BoundarySymmetricStructure A (sectionMulti s) V where
  I := PUnit.{u + 1}
  s _ := s
  isFaceScPlus _ :=
    isFaceScPlusSectionOn_of_isScPlusSectionOn
      (IsScPlusSectionOn.of_isScPlusSection hs isOpen_univ) _
  equivariant g _ y hy := by
    have h := fibAct_eq_of_isWFunctor_sectionMulti hs.1 hW (V.rep.Γ g y)
    rw [V.src_Γ g hy.1, V.tgt_Γ g hy.1] at h
    exact h.symm
  rep w _ := by
    classical
    by_cases h : w = s (A.P w)
    · have e : (Finset.univ.filter fun _ : PUnit.{u + 1} => s (A.P w) = w) = Finset.univ :=
        Finset.filter_true_of_mem fun _ _ => h.symm
      rw [e]
      simp [sectionMulti, if_pos h]
    · have e : (Finset.univ.filter fun _ : PUnit.{u + 1} => s (A.P w) = w) = ∅ :=
        Finset.filter_false_of_mem fun _ _ e => h e.symm
      rw [e]
      simp [sectionMulti, if_neg h]

/-- `τ ≡ [{∗} ← {∗} → {∗}]` for `Λ_s` on a good system for `∂X`. -/
def equivariantBoundaryTau (𝒰 : A.X.BoundaryGoodSystem) :
    (⟨𝒰, fun x => equivariantBoundaryStructure hs hW (𝒰.nbhd x)⟩ :
      BoundaryDecoration A (sectionMulti s)).Tau where
  τ _ _ _ := IndexCorr.ofEquiv (_root_.Equiv.refl PUnit.{u + 1})
  locallyConstant _ _ _ _ := Eventually.of_forall fun _ => rfl
  finite _ _ := (finite_singleton (IndexCorr.ofEquiv (_root_.Equiv.refl PUnit.{u + 1}))).subset
    (by rintro _ ⟨_, _, rfl⟩; rfl)
  swap _ _ _ _ := (IndexCorr.swap_ofEquiv_of_subsingleton (α := PUnit.{u + 1}) _).symm
  diag _ _ _ _ := IndexCorr.ofEquiv_eq_of_subsingleton (α := PUnit.{u + 1}) _ _
  biact _ _ _ _ g' g := (IndexCorr.example_13_3_3 g' _ g).symm
  compat _ _ φ _ := IndexCorr.sat_of_forall
    (fun _ _ => (fibAct_eq_of_isWFunctor_sectionMulti hs.1 hW φ).symm) _

include hs hW in
/-- **The multisection of an sc⁺-section is structurable over `∂X`** (Definition 14.1.7) when
it is a functor. -/
theorem isBoundaryStructurable_sectionMulti_of_isWFunctor (hX : A.X.IsTame)
    (hpara : A.X.HasParacompactOrbitSpace) : IsBoundaryStructurable A (sectionMulti s) := by
  obtain ⟨𝒰, -⟩ := A.X.theorem_14_1_6_hyp hX hpara (fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => mem_univ _)
  refine ⟨⟨fun q _ => hW q, fun x hx => ?_⟩, _, ⟨equivariantBoundaryTau hs hW 𝒰⟩⟩
  obtain ⟨V, -, hV⟩ := A.X.exists_isGoodBoundaryNbhd hX hx isOpen_univ (mem_univ x)
  exact ⟨V, hV, ⟨equivariantBoundaryStructure hs hW V⟩⟩

include hs hW in
/-- **The multisection of an sc⁺-section is an sc⁺-multisection** when it is a functor. -/
theorem isScPlusMultisection_sectionMulti_of_isWFunctor :
    IsScPlusMultisection A (sectionMulti s) :=
  ⟨hW, fun x₀ => hasLocalSectionStructure_of_isLocalRepOn isOpen_univ (mem_univ x₀)
    (isLocalRepOn_sectionMulti hs isOpen_univ)⟩


/-- **An auxiliary norm over `∂X` depends only on its values over `∂X`.** -/
theorem isAuxNormOn_boundary_congr {N N' : A.B.One → ℝ}
    (hN : A.E.IsAuxNormOn A.X.PObj.boundary N)
    (h : ∀ w, A.P (A.B.oneVal w) ∈ A.X.PObj.boundary → N' w = N w) :
    A.E.IsAuxNormOn A.X.PObj.boundary N' where
  continuousOn := hN.continuousOn.congr fun w hw => h w hw
  fiber y hy := by
    have e : ∀ v : A.B.oneFiber y, N' (A.B.toOne v) = N (A.B.toOne v) := fun v =>
      h _ (by rw [proj_oneVal_toOne A.B v]; exact hy)
    have hf := hN.fiber y hy
    exact ⟨fun v hv => hf.eq_zero v (by rw [← e]; exact hv),
      fun t v => by rw [e, e]; exact hf.smul t v,
      fun v w => by rw [e, e, e]; exact hf.add_le v w,
      fun u hu => by simp only [e] at hu ⊢; exact hf.complete u hu⟩
  tendsto_zeroOne w y hy hw hP h0 :=
    hN.tendsto_zeroOne w y hy hw hP (h0.congr fun k => h _ (hw k))
  map_μ k₁ k φ hk hkb he := by
    have hb : A.P (A.B.oneVal k₁) ∈ A.X.PObj.boundary := by
      rw [he, A.E.P_μ]
      exact (A.X.tgt_mem_boundary_iff φ).2 (hk ▸ hkb)
    rw [h k₁ hb, h k hkb]
    exact hN.map_μ k₁ k φ hk hkb he

end SBLocalization

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory GroupoidalCategory.BanachFunctor PolyfoldConstruction SBLocalization

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  {Q : V.StrongPolyfoldBundleConstruction S}

/-- `∂C` is closed under the morphisms of `E`: `P(t(a)) ∈ ∂C` if `P(s(a)) ∈ ∂C`. -/
theorem base_tgt_mem_boundarySet (a : V.EMor) (ha : V.base (V.groupoid.src a) ∈ S.boundarySet) :
    V.base (V.groupoid.tgt a) ∈ S.boundarySet := by
  rw [← S.isSaturated_boundarySet]
  have hπ : V.groupoid.π (V.groupoid.src a) = V.groupoid.π (V.groupoid.tgt a) :=
    (GroupoidStr.π_eq_π_iff _).2 ⟨a, rfl, rfl⟩
  exact ⟨_, ha, congrArg V.proj.orbitMap hπ⟩

/-- **An auxiliary norm on `E|∂C` depends only on its values over `∂C`.** -/
theorem IsBoundaryAuxNormIn.congr_boundary {c : Q.BundleCoveringFamily} {N N' : V.EObj → ℝ≥0∞}
    (hN : Q.IsBoundaryAuxNormIn c N) (h : ∀ e, V.base e ∈ S.boundarySet → N' e = N e) :
    Q.IsBoundaryAuxNormIn c N' := by
  have hw : ∀ w : Q.ModelW c.Ψ, (Q.modelSEP c.Ψ).P w ∈ (Q.modelSEP c.Ψ).X.PObj.boundary →
      Q.bundlePull c.Ψ N' w = Q.bundlePull c.Ψ N w :=
    fun w hw => h _ ((mem_boundary_model_iff_obj c _).1 hw)
  refine ⟨fun a ha => ?_, fun w hb hw1 => (hw w hb).trans (hN.eq_top w hb hw1),
    fun w hb hw1 => (hw w hb).trans_ne (hN.ne_top w hb hw1),
    isAuxNormOn_boundary_congr hN.isAuxNormOn fun k hk => congrArg ENNReal.toReal (hw _ hk)⟩
  rw [h _ (base_tgt_mem_boundarySet a ha), h _ ha]
  exact hN.isMorInvariant a ha

/-- **A reflexive auxiliary norm on `E|∂C` depends only on its values over `∂C`.** -/
theorem IsReflexiveBoundaryAuxNormIn.congr_boundary {c : Q.BundleCoveringFamily}
    {N N' : V.EObj → ℝ≥0∞} (hN : Q.IsReflexiveBoundaryAuxNormIn c N)
    (h : ∀ e, V.base e ∈ S.boundarySet → N' e = N e) : Q.IsReflexiveBoundaryAuxNormIn c N' := by
  have hk : ∀ k : (Q.modelSEP c.Ψ).B.One,
      (Q.modelSEP c.Ψ).P ((Q.modelSEP c.Ψ).B.oneVal k) ∈ (Q.modelSEP c.Ψ).X.PObj.boundary →
        Q.modelNorm c.Ψ N' k = Q.modelNorm c.Ψ N k :=
    fun k hk => congrArg ENNReal.toReal (h _ ((mem_boundary_model_iff_obj c _).1 hk))
  refine ⟨hN.toIsBoundaryAuxNormIn.congr_boundary h, fun w y hw hy hm => ?_⟩
  rw [hk y hy, show (fun k => (Q.modelNorm c.Ψ N' (w k) : EReal)) =
    fun k => (Q.modelNorm c.Ψ N (w k) : EReal) from funext fun k => by rw [hk _ (hw k)]]
  exact hN.le_liminf w y hw hy hm

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

namespace GCT.VectorBundle.HalfSpaceReflection

open GroupoidalCategory GroupoidalCategory.BanachFunctor HalfSpaceBundle StrongBundle
  StrongBundleUniformizerConstruction StrongBundleUniformizerData StrongPolyfoldBundleConstruction
  PolyfoldConstruction SBLocalization

/-- The section `(i, x) ↦ (i, (x, v))` of the model `⊔_{Unit} (H × ℝ) → ⊔_{Unit} H`. -/
def modelConstSec (v : Fin 1 → ℝ) :
    (halfQ.modelSEP halfSingle.Ψ).Obj → (halfQ.modelSEP halfSingle.Ψ).W :=
  sigmaSection fun _ : Unit => constSec (m := 1) v

theorem isScPlusSection_modelConstSec (v : Fin 1 → ℝ) :
    (halfQ.modelSEP halfSingle.Ψ).B.IsScPlusSection (modelConstSec v) := by
  obtain ⟨hsec, g₀, hg₀, hg₀s⟩ :=
    ((halfSEP 1 1).B.isScPlusSection_iff _).1 (isScPlusSection_constSec (m := 1) v)
  refine ((halfQ.modelSEP halfSingle.Ψ).B.isScPlusSection_iff _).2
    ⟨fun _ => rfl, (sigmaOneEquiv (fun _ : Unit => bundle 1 1)).symm ∘
      Sigma.map id (fun _ => g₀), ?_, ?_⟩
  · funext x
    obtain ⟨⟨⟩, x⟩ := x
    change (⟨(), (bundle 1 1).oneVal (g₀ x)⟩ : Σ _ : Unit, K) = ⟨(), constSec v x⟩
    rw [← hg₀]
    rfl
  · exact (isScSmoothMap_sigmaOneEquiv_symm _).comp
      (MPolyfold.isScSmoothMap_sigmaMap _ fun _ => hg₀s)


theorem objMk_eq_objMk_iff (α : H 1) (w v : Fin 1 → ℝ) :
    halfV.objMk α w = halfV.objMk α v ↔ w = v :=
  ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.1 h).2, fun h => by rw [h]⟩

open scoped Classical in
/-- **The multisection functor of the constant section** `α ↦ (α, v)`:
`Λ_v(α, w) = 1` if `w = v`, else `0`. -/
def constFunctor (v : Fin 1 → ℝ) : halfV.EObj → ℚ≥0 :=
  fun e => if e = halfV.objMk (halfV.base e) v then 1 else 0

theorem constFunctor_objMk (v : Fin 1 → ℝ) (α : H 1) (w : Fin 1 → ℝ) :
    constFunctor v (halfV.objMk α w) = if w = v then 1 else 0 := by
  classical
  unfold constFunctor
  exact if_congr (objMk_eq_objMk_iff α w v) rfl rfl

theorem constFunctor_pos_iff (v : Fin 1 → ℝ) (α : H 1) (w : Fin 1 → ℝ) :
    0 < constFunctor v (halfV.objMk α w) ↔ w = v := by
  rw [constFunctor_objMk]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => one_pos⟩
  · exact ⟨fun h' => absurd h' (lt_irrefl 0), fun h' => absurd h' h⟩

/-- **`Λ_v` is a functor** (`ℤ/2` acts trivially on the fibres). -/
theorem isMorInvariant_constFunctor (v : Fin 1 → ℝ) : IsMorInvariant (constFunctor v) :=
  isMorInvariant_iff.2 fun φ w =>
    (constFunctor_objMk v (halfC.toGroupoidStr.tgt φ) w).trans
      (constFunctor_objMk v (halfC.toGroupoidStr.src φ) w).symm

theorem sectionMulti_modelConstSec_mk (v : Fin 1 → ℝ) (y : K) :
    sectionMulti (modelConstSec v) (⟨(), y⟩ : halfQ.ModelW halfSingle.Ψ) =
      constMulti (m := 1) v y := by
  classical
  unfold sectionMulti constMulti
  have e : modelConstSec v ((halfQ.modelSEP halfSingle.Ψ).P ⟨(), y⟩) =
      (⟨(), constSec (m := 1) v ((halfSEP 1 1).P y)⟩ : halfQ.ModelW halfSingle.Ψ) := rfl
  rw [e]
  exact if_congr ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.1 h).2,
    fun h => congrArg (fun z : K => (⟨(), z⟩ : halfQ.ModelW halfSingle.Ψ)) h⟩ rfl rfl

/-- **`Λ_v` in the model** is the multisection of the constant section `modelConstSec v`. -/
theorem bundlePull_constFunctor (v : Fin 1 → ℝ) :
    halfQ.bundlePull halfSingle.Ψ (constFunctor v) = sectionMulti (modelConstSec v) := by
  classical
  funext w
  rcases w with ⟨i, y⟩
  refine (constFunctor_objMk v y.1 y.2).trans
    (Eq.trans ?_ (sectionMulti_modelConstSec_mk v y).symm)
  unfold constMulti
  refine if_congr ⟨fun h => Prod.ext rfl h, fun h => congrArg Prod.snd h⟩ rfl rfl

/-- **`Λ_v` is structurable over `∂C`** (Theorem 18.4.4's boundary datum, in the model
`halfSingle` by `isBoundaryStructurable_sectionMulti_of_isWFunctor`). -/
theorem isBoundaryStructurableFunctor_constFunctor (v : Fin 1 → ℝ) :
    halfQ.IsBoundaryStructurableFunctor (constFunctor v) := by
  refine ⟨isMorInvariant_constFunctor v, halfSingle, ?_⟩
  change IsBoundaryStructurable (halfQ.modelSEP halfSingle.Ψ)
    (halfQ.bundlePull halfSingle.Ψ (constFunctor v))
  have hW := halfQ.isWFunctor_bundlePull halfSingle.Ψ (isMorInvariant_constFunctor v)
  rw [bundlePull_constFunctor] at hW ⊢
  exact isBoundaryStructurable_sectionMulti_of_isWFunctor (isScPlusSection_modelConstSec v) hW
    (halfS.isTame_modelEpGroupoid (Ψ := halfQ.modelBase halfSingle.Ψ) halfS_isTame)
    (halfQ.hasParacompactOrbitSpace_model halfSingle)

/-- `Λ_v` is an sc⁺-multisection functor in the model. -/
theorem isScPlusMultisection_model_constFunctor (v : Fin 1 → ℝ) :
    IsScPlusMultisection (halfQ.modelSEP halfSingle.Ψ) (sectionMulti (modelConstSec v)) := by
  have hW := halfQ.isWFunctor_bundlePull halfSingle.Ψ (isMorInvariant_constFunctor v)
  rw [bundlePull_constFunctor] at hW
  exact isScPlusMultisection_sectionMulti_of_isWFunctor (isScPlusSection_modelConstSec v) hW

/-- **`|dom-supp(Λ_v|∂C)| = cl |∂C|`** for `v ≠ 0`: `Λ_v` charges `(α, v) ≠ 0` at every
`α ∈ ∂C`. -/
theorem orbitBoundaryDomSupp_constFunctor {v : Fin 1 → ℝ} (hv : v ≠ 0) :
    orbitBoundaryDomSupp halfS (constFunctor v) =
      closure (halfC.toGroupoidStr.π '' halfS.boundarySet) := by
  unfold orbitBoundaryDomSupp
  congr 2
  ext α
  refine ⟨fun h => h.1, fun h => ⟨h, v, hv, (constFunctor_pos_iff v α v).2 rfl⟩⟩

/-- `|dom-supp(Λ_v|∂C)| ∋ |(0, 0)|`, the corner with isotropy `ℤ/2`. -/
theorem corner_mem_orbitBoundaryDomSupp {v : Fin 1 → ℝ} (hv : v ≠ 0) :
    halfC.toGroupoidStr.π corner ∈ orbitBoundaryDomSupp halfS (constFunctor v) := by
  rw [orbitBoundaryDomSupp_constFunctor hv]
  exact subset_closure ⟨corner, corner_mem_boundarySet, rfl⟩

/-- `N(Λ_v)(α) = N(α, v)`. -/
theorem pointwiseNormFunctor_constFunctor (N : halfV.EObj → ℝ≥0∞) (v : Fin 1 → ℝ) (α : H 1) :
    pointwiseNormFunctor N (constFunctor v) α = N (halfV.objMk α v) := by
  unfold pointwiseNormFunctor
  have : (fun w : halfV.V α => N (halfV.objMk α w)) ''
      {w | 0 < constFunctor v (halfV.objMk α w)} = {N (halfV.objMk α v)} := by
    ext t
    simp only [mem_image, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [(constFunctor_pos_iff v α w).1 hw]
    · rintro rfl
      exact ⟨v, (constFunctor_pos_iff v α v).2 rfl, rfl⟩
  rw [this, sSup_singleton]


/-! ### The auxiliary norm `N(α, w) = |w|` -/

theorem norm_fin_one (w : Fin 1 → ℝ) : ‖w‖ = |w 0| := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => ?_) ?_
  · rw [Subsingleton.elim i 0, Real.norm_eq_abs]
  · rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm w 0

/-- The unit vector `1 ∈ ℝ`. -/
def unitVec : Fin 1 → ℝ := fun _ => 1

theorem unitVec_ne_zero : unitVec ≠ 0 := fun h => one_ne_zero (congrFun h 0)

theorem eq_smul_unitVec (w : Fin 1 → ℝ) : w = w 0 • unitVec := by
  funext i
  rw [Subsingleton.elim i 0]
  simp [unitVec]

/-- **The fibre norm** `N(α, w) = |w|` on `E`. -/
def halfNorm : halfV.EObj → ℝ≥0∞ := fun e => ENNReal.ofReal ‖(e.2 : Fin 1 → ℝ)‖

theorem halfNorm_objMk (α : H 1) (w : Fin 1 → ℝ) :
    halfNorm (halfV.objMk α w) = ENNReal.ofReal ‖w‖ := rfl

theorem isMorInvariant_halfNorm : IsMorInvariant halfNorm :=
  isMorInvariant_iff.2 fun _ _ => rfl

/-- Every point of the model lies in `W_{0,1}`. -/
theorem mem_oneSet_model (w : halfQ.ModelW halfSingle.Ψ) :
    w ∈ (halfQ.modelSEP halfSingle.Ψ).B.oneSet := by
  obtain ⟨i, y⟩ := w
  exact (mem_oneSet_sigma_iff (B := fun _ : Unit => bundle 1 1) (i := ()) y).2
    (mem_oneSet_bundle _)

/-- Every point of `E` lies in `E_{0,1}`. -/
theorem isOneObj_objMk (α : H 1) (w : Fin 1 → ℝ) : halfQ.IsOneObj (halfV.objMk α w) :=
  ⟨halfSingle, ⟨(), (α, w)⟩, mem_oneSet_model _, rfl⟩

/-- **An auxiliary norm on `E` is `N(α, w) = |w| · N(α, 1)`** (the fibres are `ℝ`). -/
theorem auxNorm_objMk_eq {N₀ : halfV.EObj → ℝ≥0∞} (hN₀ : halfQ.IsAuxNormIn halfSingle.Ψ N₀)
    (α : H 1) (w : Fin 1 → ℝ) :
    N₀ (halfV.objMk α w) = ENNReal.ofReal ‖w‖ * N₀ (halfV.objMk α unitVec) := by
  have hf := hN₀.isAuxNormBook.fiber α
  rw [norm_fin_one]
  exact (congrArg (fun z => N₀ (halfV.objMk α z)) (eq_smul_unitVec w)).trans
    (hf.smul (w 0) unitVec (isOneObj_objMk α unitVec))

theorem auxNorm_unitVec_ne_zero {N₀ : halfV.EObj → ℝ≥0∞}
    (hN₀ : halfQ.IsAuxNormIn halfSingle.Ψ N₀) (α : H 1) :
    N₀ (halfV.objMk α unitVec) ≠ 0 := fun h =>
  unitVec_ne_zero ((hN₀.isAuxNormBook.fiber α).eq_zero unitVec (isOneObj_objMk α unitVec) h)

theorem auxNorm_unitVec_ne_top {N₀ : halfV.EObj → ℝ≥0∞}
    (hN₀ : halfQ.IsAuxNormIn halfSingle.Ψ N₀) (α : H 1) :
    N₀ (halfV.objMk α unitVec) ≠ ⊤ :=
  (hN₀.isAuxNormBook.fiber α).ne_top unitVec (isOneObj_objMk α unitVec)

/-- **`N(α, w) = |w|` is an auxiliary norm in the model `halfSingle`**: it is
`N₀(α, w) / N₀(α, 1)` for any auxiliary norm `N₀` (one exists), the weight `1 / N₀(α, 1)`
being continuous (the constant section `α ↦ (α, 1)` is sc⁺) and positive. -/
theorem isAuxNormIn_halfNorm : halfQ.IsAuxNormIn halfSingle.Ψ halfNorm := by
  obtain ⟨N₀, hN₀f⟩ := halfQ.exists_isAuxNormFunctor halfQ_hasStrongBundleUniformizers
  have hN₀ := hN₀f halfSingle
  let c : (halfQ.modelSEP halfSingle.Ψ).Obj → ℝ := fun x => (N₀ (halfV.objMk x.2 unitVec)).toReal
  have hc_eq : c = fun x => normW (halfQ.modelNorm halfSingle.Ψ N₀) (modelConstSec unitVec x) := by
    funext x
    exact (normW_of_mem (A := halfQ.modelSEP halfSingle.Ψ) (halfQ.modelNorm halfSingle.Ψ N₀)
      (mem_oneSet_model (modelConstSec unitVec x))).symm
  have hcc : Continuous c := by
    rw [hc_eq]
    exact continuousOn_univ.1 ((IsScPlusSectionOn.of_isScPlusSection
      (isScPlusSection_modelConstSec unitVec) isOpen_univ).continuousOn_normW
        hN₀.isAuxNorm.isAuxNorm)
  have hc0 : ∀ x, 0 < c x := fun x =>
    ENNReal.toReal_pos (auxNorm_unitVec_ne_zero hN₀ x.2) (auxNorm_unitVec_ne_top hN₀ x.2)
  have key : halfQ.modelNorm halfSingle.Ψ halfNorm =
      fun k => (c ((halfQ.modelSEP halfSingle.Ψ).P ((halfQ.modelSEP halfSingle.Ψ).B.oneVal k)))⁻¹ *
        halfQ.modelNorm halfSingle.Ψ N₀ k := by
    funext k
    unfold StrongPolyfoldBundleConstruction.modelNorm
    rcases hw : (halfQ.modelSEP halfSingle.Ψ).B.oneVal k with ⟨i, y⟩
    change (halfNorm (halfV.objMk y.1 y.2)).toReal =
      (N₀ (halfV.objMk y.1 unitVec)).toReal⁻¹ * (N₀ (halfV.objMk y.1 y.2)).toReal
    have hpos := hc0 ⟨i, y.1⟩
    change 0 < (N₀ (halfV.objMk y.1 unitVec)).toReal at hpos
    rw [auxNorm_objMk_eq hN₀ y.1 y.2, ENNReal.toReal_mul, halfNorm_objMk,
      ENNReal.toReal_ofReal (norm_nonneg _)]
    field_simp
  refine ⟨isMorInvariant_halfNorm, fun w hw => absurd (mem_oneSet_model w) hw,
    fun _ _ => ENNReal.ofReal_ne_top, ⟨?_, ?_⟩⟩
  · rw [key]
    exact hN₀.isAuxNorm.isAuxNorm.comp_mul (hcc.inv₀ fun x => (hc0 x).ne')
      fun x => inv_pos.2 (hc0 x)
  · intro h k φ hk he
    unfold StrongPolyfoldBundleConstruction.modelNorm
    exact congrArg ENNReal.toReal ((congrArg (halfQ.bundlePull halfSingle.Ψ halfNorm) he).trans
      (halfQ.bundlePull_μ halfSingle.Ψ isMorInvariant_halfNorm _))

/-- **`N(α, w) = |w|` is an auxiliary norm** (Definition 18.1.7, read through Lemma 18.1.8). -/
theorem isAuxNormFunctor_halfNorm : halfQ.IsAuxNormFunctor halfNorm :=
  (halfQ.isAuxNormFunctor_iff_model halfSingle).2 isAuxNormIn_halfNorm

/-- `|φ(p)| ≤ 1` for `φ(a, y) = a² + y² − 1` gives `|p| ≤ 2`. -/
theorem norm_le_two_of_norm_halfDiscMap_le_one {p : Pm 1} (h : ‖halfDiscMap p‖ ≤ 1) :
    ‖p‖ ≤ 2 := by
  have h1 : ‖halfDiscMap p 0‖ ≤ 1 := (norm_le_pi_norm (halfDiscMap p) 0).trans h
  change ‖p.1 0 ^ 2 + p.2 0 ^ 2 - 1‖ ≤ 1 at h1
  rw [Real.norm_eq_abs, abs_le] at h1
  rw [norm_prod_le_iff]
  refine ⟨(pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_,
    (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_⟩
  · rw [Subsingleton.elim i 0, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [h1.2, sq_nonneg (p.2 0), sq_nonneg (p.1 0 - 2),
      sq_nonneg (p.1 0 + 2)]
  · rw [Subsingleton.elim i 0, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [h1.2, sq_nonneg (p.1 0), sq_nonneg (p.2 0 - 2),
      sq_nonneg (p.2 0 + 2)]

/-- **`(N, |C|)` controls the compactness of `f`** (Definition 18.2.3): `|N| ∘ |f| ≤ 1` means
`|a² + y² − 1| ≤ 1`, so `|(a, y)| ≤ 2`. -/
theorem halfF_controlsCompactness_halfNorm : halfF.ControlsCompactness halfNorm univ := by
  refine ⟨isOpen_univ, subset_univ _, isCompact_closedBallH.closure_of_subset ?_⟩
  rintro _ ⟨-, α, hα, rfl⟩
  refine ⟨α, norm_le_two_of_norm_halfDiscMap_le_one ?_, rfl⟩
  have h : ENNReal.ofReal ‖halfDiscMap (α : Pm 1)‖ ≤ 1 := hα
  exact ENNReal.ofReal_le_one.1 h


/-! ### Theorem 18.4.4 with the boundary datum `Λ_v`, `v = −3/4` -/

theorem norm_constDatum : ‖constDatum‖ = 3 / 4 := by
  rw [norm_fin_one]
  norm_num [constDatum]

/-- `N(Λ_v) = 3/4` for `N(α, w) = |w|` and `v = −3/4`. -/
theorem pointwiseNormFunctor_halfNorm_constDatum (α : H 1) :
    pointwiseNormFunctor halfNorm (constFunctor constDatum) α = ENNReal.ofReal (3 / 4) := by
  rw [pointwiseNormFunctor_constFunctor, halfNorm_objMk, norm_constDatum]

theorem ofReal_three_quarters_lt_one : ENNReal.ofReal (3 / 4) < ENNReal.ofReal 1 :=
  (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by norm_num)

/-- **Theorem 18.4.4 on `ℤ/2 ⋉ H` with a boundary datum whose domain support is `|∂C|`**: for
`N(α, w) = |w|`, the multisection functor `Λ_v` of the constant section `α ↦ (α, −3/4)` over `∂C`
(structurable over `∂C`, with `|dom-supp(Λ_v|∂C)| = cl |∂C|` containing the corner with isotropy
`ℤ/2`, and `N(Λ_v) = 3/4`), `U = |C|` and `β = 1`, every hypothesis holds, and the theorem gives a
structurable `Λ'` with `N(Λ') ≤ 1` and `Λ' = Λ_v` over `∂C`; in particular `Λ'(α, −3/4) = 1` at
every `α ∈ ∂C`. -/
theorem theorem_18_4_4_modelFree_witness_constDatum :
    halfQ.HasModelMPolyfoldPartitionsOfUnity ∧ halfQ.IsAuxNormFunctor halfNorm ∧
      halfQ.IsBoundaryStructurableFunctor (constFunctor constDatum) ∧
      orbitBoundaryDomSupp halfS (constFunctor constDatum) =
        closure (halfC.toGroupoidStr.π '' halfS.boundarySet) ∧
      halfC.toGroupoidStr.π corner ∈ orbitBoundaryDomSupp halfS (constFunctor constDatum) ∧
      (∃ φ ∈ halfC.toGroupoidStr.mor corner corner, φ ≠ halfC.toGroupoidStr.unit corner) ∧
      (∀ α, pointwiseNormFunctor halfNorm (constFunctor constDatum) α = ENNReal.ofReal (3 / 4)) ∧
      halfS.IsContinuousFunctionFunctor (fun _ => (1 : ℝ)) ∧
      ∃ Λ' : halfV.EObj → ℚ≥0, halfQ.IsStructurableFunctor Λ' ∧
        (∀ α, pointwiseNormFunctor halfNorm Λ' α ≤ ENNReal.ofReal 1) ∧ orbitDomSupp Λ' ⊆ univ ∧
        (∀ e : halfV.EObj, halfV.base e ∈ halfS.boundarySet → Λ' e = constFunctor constDatum e) ∧
        ∀ α ∈ halfS.boundarySet, Λ' (halfV.objMk α constDatum) = 1 := by
  obtain ⟨Λ', h1, h2, h3, h4⟩ := theorem_18_4_4_modelFree halfS_isTame
    halfQ_hasModelMPolyfoldPartitionsOfUnity isAuxNormFunctor_halfNorm
    (isBoundaryStructurableFunctor_constFunctor constDatum) isOpen_univ (subset_univ _)
    halfS_isContinuousFunctionFunctor_one (fun _ => zero_le_one) (subset_univ _)
    (fun α _ => by
      rw [pointwiseNormFunctor_halfNorm_constDatum]
      exact ofReal_three_quarters_lt_one)
  refine ⟨halfQ_hasModelMPolyfoldPartitionsOfUnity, isAuxNormFunctor_halfNorm,
    isBoundaryStructurableFunctor_constFunctor constDatum,
    orbitBoundaryDomSupp_constFunctor constDatum_ne_zero,
    corner_mem_orbitBoundaryDomSupp constDatum_ne_zero, exists_ne_unit_corner,
    pointwiseNormFunctor_halfNorm_constDatum, halfS_isContinuousFunctionFunctor_one,
    Λ', h1, h2, h3, h4, fun α hα => ?_⟩
  rw [h4 _ hα, constFunctor_objMk, if_pos rfl]

/-! ### The boundary hypothesis of Theorem 15.3.9 for `(f, Λ_v)` -/

/-- **The boundary hypothesis of Theorem 15.3.9 in the model for `(f, Λ_v)`**: at a boundary
point `q = (0, ±1/2)` where `f(q) = (q, −3/4)`, the reduced linearization in the model is carried
by the local strong bundle isomorphism `⊔_{Unit} (H × ℝ) ⊇ range(mk ()) ≅ H × ℝ`
(`isReducedOntoAtLevel_localIso_iff`) to that of `(graph φ, Λ_v)` on `H × ℝ → H`, onto by
`isReducedOntoAtPt_halfDisc_constMulti` (Chapter 15). -/
theorem isBoundaryFaceOnto_model_constFunctor :
    IsBoundaryFaceOnto (A := halfQ.modelSEP halfSingle.Ψ) (halfQ.modelSection halfSingle.Ψ halfF)
      (halfQ.bundlePull halfSingle.Ψ (constFunctor constDatum)) := by
  classical
  set A := halfQ.modelSEP halfSingle.Ψ with hA
  have hf : A.E.IsScFredholmSectionFunctor (halfQ.modelSection halfSingle.Ψ halfF) :=
    (halfQ.remark_18_1_2_a_model halfF halfSingle).2 isScFredholmSectionFunctor_halfF
  have hft : A.B.IsScFredholmSectionTame (halfQ.modelSection halfSingle.Ψ halfF) :=
    (halfQ.remark_18_1_2_a_model_tame halfF halfSingle).2 isScFredholmSectionFunctorTame_halfF
  rw [bundlePull_constFunctor]
  refine (isBoundaryFaceOnto_iff hf hft (isScPlusMultisection_model_constFunctor constDatum)
    fun _ _ => rfl).2 ?_
  intro x hxb _ hpos
  rcases hyq : A.X.PObj.levelVal 1 x with ⟨u, q⟩
  cases u
  have hq1 : (show (halfSEP 1 1).Obj from q) ∈ (halfSEP 1 1).X.PObj.levelSet 1 := by
    change q ∈ (basePoly 1).levelSet 1
    rw [levelSet_eq_univ]; exact mem_univ _
  set x' := (halfSEP 1 1).X.PObj.levelMk 1 q hq1 with hx'
  have hx'v : (halfSEP 1 1).X.PObj.levelVal 1 x' = q :=
    (halfSEP 1 1).X.PObj.levelVal_levelMk _ _ _
  set L := (sigmaMkLocalIso (fun _ : Unit => bundle 1 1) () q).symm with hL
  have hfL : EqOn (halfQ.modelSection halfSingle.Ψ halfF) (L.Ψ ∘ graphSection halfDiscMap ∘ L.ϕ)
      (range (Sigma.mk ())) := by
    rw [modelSection_halfF]
    exact eqOn_sigmaSection (fun _ : Unit => bundle 1 1) (fun _ => graphSection halfDiscMap) () q
  have hΛL : ∀ w : A.W, A.P w ∈ range (Sigma.mk ()) →
      sectionMulti (modelConstSec constDatum) w = constMulti constDatum (L.Φ w) := by
    rintro ⟨⟨⟩, y⟩ -
    exact (sectionMulti_modelConstSec_mk constDatum y).trans (congrArg (constMulti constDatum)
      (sigmaMkLocalIso_Ψ_mk (fun _ : Unit => bundle 1 1) () q y).symm)
  have hxU : A.X.PObj.levelVal 1 x ∈ range (Sigma.mk ()) := ⟨q, hyq.symm⟩
  have hϕ : L.ϕ (A.X.PObj.levelVal 1 x) = (halfSEP 1 1).X.PObj.levelVal 1 x' := by
    rw [hyq, hx'v]
    exact sigmaMkLocalIso_g_mk (fun _ : Unit => bundle 1 1) () q q
  have key := isReducedOntoAtLevel_localIso_iff (A := A) (A' := halfSEP 1 1) L hf
    (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap)
    (isScPlusMultisection_constMulti constDatum) hfL hΛL hxU hϕ
  have hqb : ((show H 1 from q) : Pm 1).1 0 = 0 := by
    have h := (halfQ.mem_boundary_model_iff_obj halfSingle (A.X.PObj.levelVal 1 x)).1 hxb
    rw [hyq] at h
    exact (mem_boundarySet_iff q).1 h
  have hxb' : (halfSEP 1 1).X.PObj.levelVal 1 x' ∈ (halfSEP 1 1).X.PObj.boundary := by
    rw [hx'v]; exact (mem_boundary_halfSEP_iff 1 1 q).2 hqb
  have hpos' : 0 < constMulti constDatum
      (halfDiscSection ((halfSEP 1 1).X.PObj.levelVal 1 x')) := by
    rw [hx'v]
    rw [hyq, modelSection_halfF] at hpos
    exact (sectionMulti_modelConstSec_mk constDatum _).symm.trans_gt hpos
  exact key.2 (isReducedOntoAtPt_halfDisc_constMulti x' hxb' hpos')

/-- **The boundary hypothesis of Theorem 15.3.9 holds model-free** for `f` and `Λ_v`. -/
theorem isBoundaryFaceOntoFunctor_constFunctor :
    halfQ.IsBoundaryFaceOntoFunctor halfF (constFunctor constDatum) :=
  ⟨halfSingle, isBoundaryFaceOnto_model_constFunctor⟩

/-- `f(0, 1/2) = ((0, 1/2), −3/4)`: `supp(Λ_v ∘ f)` meets `∂C`. -/
theorem constFunctor_halfF_constDatumPoint :
    0 < constFunctor constDatum (halfF.toFun constDatumPoint) := by
  refine (constFunctor_pos_iff _ _ _).2 (funext fun i => ?_)
  change (0 : ℝ) ^ 2 + (1 / 2) ^ 2 - 1 = -(3 / 4)
  norm_num

theorem constDatumPoint_mem_boundarySet : constDatumPoint ∈ halfS.boundarySet :=
  (mem_boundarySet_iff constDatumPoint).2 rfl

/-! ### Theorem 15.3.9 in the polyfold context with the boundary datum `Λ_v` -/

/-- **Theorem 15.3.9 in the polyfold context on `ℤ/2 ⋉ H` with a boundary datum whose domain
support is `|∂C|`**: for `f(a, y) = ((a, y), a² + y² − 1)`, `N(α, w) = |w|`, `U = |C|`, the
multisection functor `Λ_v` of `α ↦ (α, −3/4)` over `∂C` (`N(Λ_v) = 3/4 < 1 = h`, the boundary
hypothesis checked at the boundary points `(0, ±1/2)` where `Λ_v ∘ f > 0`), every hypothesis
holds, and the theorem gives a structurable, transversal `Λ'` agreeing with `Λ_v` over `∂C` (so
`Λ'(α, −3/4) = 1` at every `α ∈ ∂C`), with `N(Λ') < 1` and `Λ' ∘ f` a compact branched
ep⁺-subcategory. -/
theorem theorem_15_3_9_categorical_witness_constDatum :
    constDatumPoint ∈ halfS.boundarySet ∧
      0 < constFunctor constDatum (halfF.toFun constDatumPoint) ∧
      halfC.toGroupoidStr.π corner ∈ orbitBoundaryDomSupp halfS (constFunctor constDatum) ∧
      (∃ φ ∈ halfC.toGroupoidStr.mor corner corner, φ ≠ halfC.toGroupoidStr.unit corner) ∧
      halfQ.IsAuxNormFunctor halfNorm ∧ halfF.ControlsCompactness halfNorm univ ∧
      halfQ.IsBoundaryStructurableFunctor (constFunctor constDatum) ∧
      (∀ α, pointwiseNormFunctor halfNorm (constFunctor constDatum) α = ENNReal.ofReal (3 / 4)) ∧
      halfQ.IsBoundaryFaceOntoFunctor halfF (constFunctor constDatum) ∧
      ∃ Λ' : halfV.EObj → ℚ≥0, halfQ.IsStructurableFunctor Λ' ∧
        (∀ e : halfV.EObj, halfV.base e ∈ halfS.boundarySet → Λ' e = constFunctor constDatum e) ∧
        (∀ α ∈ halfS.boundarySet, Λ' (halfV.objMk α constDatum) = 1) ∧
        orbitDomSupp Λ' ⊆ univ ∧
        (∀ α, pointwiseNormFunctor halfNorm Λ' α < ENNReal.ofReal 1) ∧
        halfQ.IsTransversalFunctor halfF Λ' ∧
        halfS.IsBranchedSubcategory (fun α => (Λ' (halfF.toFun α) : ℚ)) ∧
        halfC.IsCompactBranched (fun α => (Λ' (halfF.toFun α) : ℚ)) := by
  obtain ⟨Λ', h1, h2, h3, h4, h5, h6, h7⟩ := theorem_15_3_9_categorical halfS_isTame
    halfQ_hasModelMPolyfoldPartitionsOfUnity isScFredholmSectionFunctor_halfF
    isScFredholmSectionFunctorTame_halfF halfF_hasCompactModuliSpace isAuxNormFunctor_halfNorm
    halfF_controlsCompactness_halfNorm (isBoundaryStructurableFunctor_constFunctor constDatum)
    (subset_univ _)
    (fun α _ => by
      rw [pointwiseNormFunctor_halfNorm_constDatum]
      exact ENNReal.ofReal_le_one.2 (by norm_num))
    halfS_isContinuousFunctionFunctor_one (fun _ => ⟨one_pos, le_rfl⟩)
    (fun α _ => by
      rw [pointwiseNormFunctor_halfNorm_constDatum]
      exact ofReal_three_quarters_lt_one)
    isBoundaryFaceOntoFunctor_constFunctor
  refine ⟨constDatumPoint_mem_boundarySet, constFunctor_halfF_constDatumPoint,
    corner_mem_orbitBoundaryDomSupp constDatum_ne_zero, exists_ne_unit_corner,
    isAuxNormFunctor_halfNorm, halfF_controlsCompactness_halfNorm,
    isBoundaryStructurableFunctor_constFunctor constDatum, pointwiseNormFunctor_halfNorm_constDatum,
    isBoundaryFaceOntoFunctor_constFunctor, Λ', h1, h2, fun α hα => ?_, h3, h4, h5, h6, h7⟩
  rw [h2 _ hα, constFunctor_objMk, if_pos rfl]

/-! ### Theorem 18.1.12 (3) with `∂C ≠ ∅` -/

open scoped Classical in
/-- **`N` over `∂C` only**: `N(e)` over `∂C`, `+∞` elsewhere. -/
def boundaryOnly (N : halfV.EObj → ℝ≥0∞) : halfV.EObj → ℝ≥0∞ :=
  fun e => if halfV.base e ∈ halfS.boundarySet then N e else ⊤

theorem boundaryOnly_of_mem (N : halfV.EObj → ℝ≥0∞) {e : halfV.EObj}
    (he : halfV.base e ∈ halfS.boundarySet) : boundaryOnly N e = N e := by
  classical
  exact if_pos he

/-- The point `(1, 0)` of `H`, off `∂C`. -/
def interiorPoint : H 1 := ⟨(fun _ => 1, 0), fun _ => zero_le_one⟩

theorem interiorPoint_not_mem_boundarySet : interiorPoint ∉ halfS.boundarySet := fun h =>
  one_ne_zero ((mem_boundarySet_iff interiorPoint).1 h)

/-- **`N` over `∂C` only is not an auxiliary norm of `P`**: it is `+∞` on `(1, 0) ∈ E_{0,1}`. -/
theorem not_isAuxNormFunctor_boundaryOnly (N : halfV.EObj → ℝ≥0∞) :
    ¬ halfQ.IsAuxNormFunctor (boundaryOnly N) := by
  classical
  intro h
  apply (h halfSingle).ne_top ⟨(), (interiorPoint, 0)⟩ (mem_oneSet_model _)
  change (if interiorPoint ∈ halfS.boundarySet then N (halfV.objMk interiorPoint 0) else ⊤) = ⊤
  exact if_neg interiorPoint_not_mem_boundarySet

/-- **Theorem 18.1.12 (3), first part, on `ℤ/2 ⋉ H` with `∂C ≠ ∅`**: `N(α, w) = |w|` over `∂C`
and `+∞` elsewhere is an auxiliary norm on `E|∂C` (in the covering model `halfSingle`) which is
not an auxiliary norm of `P`; the theorem extends it to an auxiliary norm `Ñ` of `P` with
`Ñ = N` over `∂C`, so `Ñ(α, w) = |w|` at every `α ∈ ∂C` (the corner among them). -/
theorem theorem_18_1_12_three_witness_boundary :
    halfS.IsTame ∧ corner ∈ halfS.boundarySet ∧
      halfQ.IsBoundaryAuxNormIn halfSingle (boundaryOnly halfNorm) ∧
      ¬ halfQ.IsAuxNormFunctor (boundaryOnly halfNorm) ∧
      ∃ Ñ : halfV.EObj → ℝ≥0∞, halfQ.IsAuxNormFunctor Ñ ∧
        (∀ e, halfV.base e ∈ halfS.boundarySet → Ñ e = boundaryOnly halfNorm e) ∧
        ∀ α ∈ halfS.boundarySet, ∀ w : Fin 1 → ℝ, Ñ (halfV.objMk α w) = ENNReal.ofReal ‖w‖ := by
  have hb : halfQ.IsBoundaryAuxNormIn halfSingle (boundaryOnly halfNorm) :=
    isAuxNormIn_halfNorm.isBoundaryAuxNormIn.congr_boundary fun e he => boundaryOnly_of_mem _ he
  obtain ⟨Ñ, hÑ, hÑe⟩ := halfQ.theorem_18_1_12_three halfSingle halfS_isTame hb
  refine ⟨halfS_isTame, corner_mem_boundarySet, hb, not_isAuxNormFunctor_boundaryOnly _, Ñ, hÑ,
    hÑe, fun α hα w => ?_⟩
  rw [hÑe _ hα, boundaryOnly_of_mem _ hα, halfNorm_objMk]

/-- **Theorem 18.1.12 (3), second part, on `ℤ/2 ⋉ H` with `∂C ≠ ∅`** (reflexive fibres): for a
reflexive auxiliary norm `N`, `N` over `∂C` and `+∞` elsewhere is a reflexive auxiliary norm on
`E|∂C` which is not an auxiliary norm of `P`; it extends to a reflexive auxiliary norm `Ñ` of `P`
with `Ñ = N` over `∂C`. -/
theorem theorem_18_1_12_three_reflexive_witness_boundary :
    halfS.IsTame ∧ halfQ.HasReflexiveFibers ∧ corner ∈ halfS.boundarySet ∧
      ∃ N : halfV.EObj → ℝ≥0∞, halfQ.IsReflexiveAuxNormFunctor N ∧
        halfQ.IsReflexiveBoundaryAuxNormIn halfSingle (boundaryOnly N) ∧
        ¬ halfQ.IsAuxNormFunctor (boundaryOnly N) ∧
        ∃ Ñ : halfV.EObj → ℝ≥0∞, halfQ.IsReflexiveAuxNormFunctor Ñ ∧
          ∀ e, halfV.base e ∈ halfS.boundarySet → Ñ e = boundaryOnly N e := by
  obtain ⟨N, hN⟩ := halfQ.exists_isReflexiveAuxNormFunctor halfQ_hasStrongBundleUniformizers
    halfQ_hasReflexiveFibers
  have hb : halfQ.IsReflexiveBoundaryAuxNormIn halfSingle (boundaryOnly N) :=
    (hN halfSingle).isReflexiveBoundaryAuxNormIn.congr_boundary fun e he =>
      boundaryOnly_of_mem _ he
  exact ⟨halfS_isTame, halfQ_hasReflexiveFibers, corner_mem_boundarySet, N, hN, hb,
    not_isAuxNormFunctor_boundaryOnly _, halfQ.theorem_18_1_12_three_reflexive halfSingle
      halfS_isTame halfQ_hasReflexiveFibers hb⟩

end GCT.VectorBundle.HalfSpaceReflection

end Polyfold
