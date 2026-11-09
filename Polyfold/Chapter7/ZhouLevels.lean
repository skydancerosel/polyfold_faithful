import Polyfold.Chapter7.Zhou
import Polyfold.Chapter2.TangentLiftAll

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §7.4 "Regularity Assumptions and the Zhou Condition" (pp. 327–341, new in the 2021
edition): the statements about **all lifts `X^i`**.  Numbers and pages are the 2021 text's.  The
statements for `X` and `X¹`, and the versions taking a property of every `X^i` as a hypothesis,
are in `Polyfold/Chapter7/Zhou.lean`.

# The Zhou condition and (VSLUC) under index lifting; (VSLUC) ⇔ (SLUC)

## The text, paraphrased

* (Proposition 7.4.9, p. 333) (ZHOU) for `X` gives (ZHOU) for every `X^i`: (ZHOU') is the same for
  `X` and `X^i`.
* (Corollary 7.4.11 and Theorem 7.4.13, p. 334) Hence every `X^i` has (LUC), i.e. (ZHOU) ⇒ (SLUC).
* (Proposition 7.4.16, p. 336) (VSLUC) for `X` gives (VSLUC), hence (LUC), for every `X^i`, since
  (VSLUC) is phrased in terms of `X_∞ = X^i_∞`.  (Proposition 7.4.17) (VSLUC) ⇒ (SLUC).
* (Proposition 7.4.18, p. 336) (VSLUC) ⇔ (SLUC).  *Proof of ⇐*: for smooth `x` take `U(x)`
  invariant with every `U(x) ∩ X_i` connected and `V(x) = U(x) ∩ X_∞`; if `ĝ = id` on a
  nonempty open `W ⊆ V(x)`, then `W ⊇ W' ∩ X_∞` for a nonempty open `W' ⊆ X_N`, `ĝ = id` on
  `W'` by density and continuity, and (LUC) for `X^N` gives `ĝ = id` on `U(x) ∩ X_N`.
* (Theorem 7.4.24, p. 340) (ZHOU) ⇒ (SLR), by Proposition 7.4.9 and Proposition 7.4.22.

## What is formalized

* `MPolyfold.shiftSmoothHomeomorph`: **`(X¹)_∞ ≅ X_∞`** as topological spaces
  (`continuous_levelDown`: `X_{m+1} → X_m` is continuous); `MPolyfold.DenseSmooth.shift`.
* `EpGroupoid.levelVal_Φ_liftOne` (a natural representation of `X¹` inside `U(x) ∩ X_1` acts by
  the action of `X`) and `EpGroupoid.tangentLower_tangentMor_liftOne` (the tangent action of `X¹`
  is that of `X` under `T(X¹) → TX`, with `MPolyfold.tangentLower_tangentMap`).
* `EpGroupoid.isZhou'_liftOne`, `EP.isZhou'_lift` and **`EP.proposition_7_4_9`**;
  **`EP.corollary_7_4_11_all`**, **`EP.theorem_7_4_13_all`**,
  **`EP.theorem_7_4_24_all`**: the hypothesis "(ZHOU) for every `X^i`" of
  `corollary_7_4_11_lift`, `theorem_7_4_13`, `theorem_7_4_24` is removed.
* `EpGroupoid.isVSLUC_liftOne`, `EP.isVSLUC_lift`, **`EP.proposition_7_4_16_all`** and
  **`EP.proposition_7_4_17_all`**: the hypothesis "(VSLUC) for every `X^i`" of
  `proposition_7_4_17` is removed, and density is needed for `X` only.
* For Proposition 7.4.18: `MPolyfold.exists_level_nhds_smooth` (the sets `O ∩ X_∞`, `O` open in
  some `X_{N+1}`, form a neighbourhood basis of `X_∞`), `EpGroupoid.NaturalRep.liftOneRep` (**a
  natural representation of `x` restricts to one of `x` in `X¹`** when `U(x) ∩ X_1` is connected;
  `isotropyLevelMk` identifies `G_x` in `X` and in `X¹`), `EP.eqOn_of_level_smooth`,
  `EP.isVSLUC_of_isSLUC` and **`EP.proposition_7_4_18`** ((VSLUC) ⇔ (SLUC)).
* Witnesses (the point ep-groupoid `pointEP` and all its lifts):
  `Examples.proposition_7_4_9_pointEP`, `Examples.theorem_7_4_13_all_pointEP`,
  `Examples.theorem_7_4_24_all_pointEP`, `Examples.proposition_7_4_17_all_pointEP`,
  `Examples.levelConnected_pointEP`, `Examples.proposition_7_4_18_pointEP`.

## What the text leaves implicit, and the choices made

* "(ZHOU') is the same for `X` and `X^i`" is proved in the direction used: (ZHOU') for `X` gives
  (ZHOU') for `X¹`, through `(X¹)_∞ ≅ X_∞`, the smooth tangent vectors (2021 Proposition 2.3.17
  for `i = 1`) and the comparison of natural representations; then by induction.  (ZHOU') for
  `X` comes from (ZHOU), and (ZHOU) for `X^i` from (ZHOU') for `X^i`, through Lemma 7.4.6 and
  Proposition 7.4.8 (`lemma_7_4_6`,
  `isZhou_of_isZhou'`), which need `DenseSmoothTangent` for `X` and the Part I facts
  `SmoothRegular` (density of `X_∞` (G.73), connectedness of `U ∩ X_∞`, openness of `p` (G.8),
  `TangentDeterminedSmooth`) **for every `X^i`**; these stay hypotheses (satisfiable:
  `smoothRegular_lift_pointEP`).
* Proposition 7.4.16 needs nothing beyond (VSLUC) for `X`; its "in particular (LUC)" uses Lemma
  7.4.15, with `DenseSmooth` for `X` (transported to every `X^i`) and `SmoothConnected` for
  every `X^i` as hypotheses.
* In Proposition 7.4.18, "by construction every `U(x) ∩ X_i` is connected" is the hypothesis
  `NaturalRep.LevelConnected` on one natural representation per smooth point (a property of the
  choice of `U(x)`, not derived here); density of `X_∞` (G.73) is the hypothesis `DenseSmooth`
  for `X`.  (LUC) for `X^N` is applied to the restriction of `U(x)` to `X^N`, built one level at
  a time by `liftOneRep`.  The direction ⇒ (Proposition 7.4.17) needs `SmoothConnected` for
  every `X^i`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- The inclusion `X_{m+1} → X_m` is continuous. -/
theorem continuous_levelDown (m : ℕ) :
    Continuous (fun x : P.Level (m + 1) => P.levelMk m (P.levelVal (m + 1) x)
      (P.levelSet_succ_subset m (P.levelVal_mem x))) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨φ, hφ, W, hW, rfl⟩
  have : (fun x : P.Level (m + 1) => P.levelMk m (P.levelVal (m + 1) x)
      (P.levelSet_succ_subset m (P.levelVal_mem x))) ⁻¹'
        {x : P.levelSet m | (x : X) ∈ φ.source ∧ levelLift φ m (x : X) ∈ W} =
      {x : P.Level (m + 1) | P.levelVal (m + 1) x ∈ φ.source ∧
        levelLift φ (m + 1) (P.levelVal (m + 1) x) ∈ φ.model.E.incl m ⁻¹' W} := by
    ext x
    change P.levelVal (m + 1) x ∈ φ.source ∧ levelLift φ m (P.levelVal (m + 1) x) ∈ W ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [mem_preimage, ← P.levelLift_eq_incl hφ h1 (P.levelVal_mem x)]
      exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [P.levelLift_eq_incl hφ h1 (P.levelVal_mem x)]
      exact h2
  exact (congrArg IsOpen this).mpr
    (P.isOpen_level_basic hφ (hW.preimage (φ.model.E.incl m).continuous))

/-- `(X¹)_∞ → X_∞`. -/
def shiftSmoothMap (y : P.shift.SmoothLevel) : P.SmoothLevel :=
  P.smoothMk (P.levelVal 1 (P.shift.smoothVal y))
    ((mem_shift_smoothSet_iff _).1 (P.shift.smoothVal_mem y))

/-- `X_∞ → (X¹)_∞`. -/
def shiftSmoothInv (z : P.SmoothLevel) : P.shift.SmoothLevel :=
  P.shift.smoothMk (P.levelMk 1 (P.smoothVal z) (mem_iInter.1 (P.smoothVal_mem z) 1))
    ((mem_shift_smoothSet_iff _).2 (P.smoothVal_mem z))

/-- `(X¹)_∞ → X_∞` is continuous. -/
theorem continuous_shiftSmoothMap : Continuous P.shiftSmoothMap := by
  refine continuous_induced_rng.2 (continuous_pi fun m => ?_)
  exact (P.continuous_levelDown m).comp ((continuous_shiftLevelMap (P := P) m).comp
    (P.shift.continuous_smoothIncl m))

/-- `X_∞ → (X¹)_∞` is continuous. -/
theorem continuous_shiftSmoothInv : Continuous P.shiftSmoothInv := by
  refine continuous_induced_rng.2 (continuous_pi fun m => ?_)
  exact (continuous_shiftLevelInv (P := P) m).comp (P.continuous_smoothIncl (m + 1))

/-- **`(X¹)_∞ = X_∞`** ("`X_∞ = X^i_∞`", 2021 p. 336), as a homeomorphism. -/
def shiftSmoothHomeomorph : P.shift.SmoothLevel ≃ₜ P.SmoothLevel where
  toFun := P.shiftSmoothMap
  invFun := P.shiftSmoothInv
  left_inv _ := Subtype.ext (P.level_ext rfl)
  right_inv _ := rfl
  continuous_toFun := P.continuous_shiftSmoothMap
  continuous_invFun := P.continuous_shiftSmoothInv

@[simp] lemma smoothVal_shiftSmoothMap (y : P.shift.SmoothLevel) :
    P.smoothVal (P.shiftSmoothMap y) = P.levelVal 1 (P.shift.smoothVal y) := rfl

variable {P} in
/-- Density of `X_∞` in every `X_m` passes from `X` to `X¹`. -/
theorem DenseSmooth.shift (h : P.DenseSmooth) : P.shift.DenseSmooth := fun m => by
  have : {y : P.shift.Level m | P.shift.levelVal m y ∈ P.shift.smoothSet} =
      P.shiftLevelMap m ⁻¹' {z : P.Level (m + 1) | P.levelVal (m + 1) z ∈ P.smoothSet} := by
    ext y; exact mem_shift_smoothSet_iff _
  rw [this]
  exact (h (m + 1)).preimage (P.shiftLevelHomeomorph m).isOpenMap

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- The isotropy element of `X` underlying one of `X¹`. -/
def isotropyLevelVal {x₁ : X.PObj.Level 1} (g : X.liftOne.Isotropy x₁) :
    X.Isotropy (X.PObj.levelVal 1 x₁) :=
  ⟨X.PMor.levelVal 1 g.val, congrArg (X.PObj.levelVal 1) g.src_val,
    congrArg (X.PObj.levelVal 1) g.tgt_val⟩

@[simp] lemma isotropyLevelVal_val {x₁ : X.PObj.Level 1} (g : X.liftOne.Isotropy x₁) :
    (X.isotropyLevelVal g).val = X.PMor.levelVal 1 g.val := rfl

variable {X}

/-- A natural representation `U'(x₁)` of `X¹` inside `U(x) ∩ X_1`, `x = x₁`, acts on `U'(x₁)` by
the natural action of `X` on `U(x)`. -/
theorem levelVal_Φ_liftOne {x₁ : X.PObj.Level 1} (R' : X.liftOne.NaturalRep x₁)
    (R : X.NaturalRep (X.PObj.levelVal 1 x₁)) (hU : R'.U ⊆ X.PObj.levelVal 1 ⁻¹' R.U)
    (g : X.liftOne.Isotropy x₁) :
    ∀ z ∈ R'.U,
      X.PObj.levelVal 1 (R'.Φ g z) = R.Φ (X.isotropyLevelVal g) (X.PObj.levelVal 1 z) := by
  have hEq : EqOn (fun z => X.PMor.levelVal 1 (R'.Γ g z))
      (fun z => R.Γ (X.isotropyLevelVal g) (X.PObj.levelVal 1 z)) R'.U :=
    (T2Space.isSeparatedMap X.src).eqOn_of_comp_eqOn X.isLocalScDiffeo_src.isLocallyInjective
      R'.isConnected_U.isPreconnected
      ((MPolyfold.continuous_levelVal 1).comp_continuousOn (R'.continuousOn_Γ g))
      ((R.continuousOn_Γ _).comp (MPolyfold.continuous_levelVal 1).continuousOn
        fun z hz => hU hz)
      (fun z hz => by
        change X.src (X.PMor.levelVal 1 (R'.Γ g z)) =
          X.src (R.Γ (X.isotropyLevelVal g) (X.PObj.levelVal 1 z))
        rw [R.src_Γ _ _ (hU hz)]
        exact congrArg (X.PObj.levelVal 1) (R'.src_Γ g z hz))
      R'.mem_U (by
        rw [R'.Γ_self, R.Γ_self]; rfl)
  intro z hz
  rw [← R'.tgt_Γ g z hz, ← R.tgt_Γ _ _ (hU hz)]
  exact congrArg X.tgt (hEq hz)

/-- The tangent action of `𝐗¹` is that of `𝐗` under the inclusion `T(X¹) → TX`. -/
theorem tangentLower_tangentMor_liftOne {φ : X.PMor.Level 1} (hφ : φ ∈ X.liftOne.PMor.levelSet 1)
    {v : X.PObj.shift.TangentSpace}
    (hv : X.PObj.shift.levelVal 1 (X.PObj.shift.tangentProj v) = X.liftOne.src φ) :
    MPolyfold.tangentLower (X.liftOne.tangentMor φ v) =
      X.tangentMor (X.PMor.levelVal 1 φ) (MPolyfold.tangentLower v) := by
  obtain ⟨u, hu1, rfl⟩ := X.liftOne.exists_tSrc_eq' hφ hv
  subst hu1
  rw [X.liftOne.tangentMor_tSrc]
  have h1 : MPolyfold.tangentLower (X.liftOne.tTgt u) = X.tTgt (MPolyfold.tangentLower u) :=
    MPolyfold.tangentLower_tangentMap X.isScSmoothMap_tgt (f₁ := X.liftOne.tgt) (fun _ => rfl) u
  have h2 : MPolyfold.tangentLower (X.liftOne.tSrc u) = X.tSrc (MPolyfold.tangentLower u) :=
    MPolyfold.tangentLower_tangentMap X.isScSmoothMap_src (f₁ := X.liftOne.src) (fun _ => rfl) u
  have h3 : X.tBase (MPolyfold.tangentLower u) = X.PMor.levelVal 1 (X.liftOne.tBase u) := by
    exact congrArg (X.PMor.levelVal 1)
      (MPolyfold.tangentProj_tangentLower (P := X.PMor) u)
  rw [h1, h2, ← h3, X.tangentMor_tSrc]

variable (X)

/-- **(ZHOU') for `X` gives (ZHOU') for `X¹`** (the proof of 2021 Proposition 7.4.9). -/
theorem isZhou'_liftOne (hZ : X.IsZhou') : X.liftOne.IsZhou' := by
  intro y g hg
  set y₀ := X.PObj.shiftSmoothMap y with hy₀
  have hg₀ : X.isotropyLevelVal g ∈ X.trivialSubgroupInf y₀ := by
    refine hZ y₀ (X.isotropyLevelVal g) fun w hw => ?_
    have hw1 : w ∈ X.PObj.tangentPolyfold.levelSet 1 := mem_iInter.1 hw.2 1
    set β := X.PObj.tangentPolyfold.levelMk 1 w hw1 with hβ
    set v := (MPolyfold.tangentShiftEquiv (P := X.PObj)).symm β with hv
    have hlow : MPolyfold.tangentLower v = w := by
      have := congrArg (X.PObj.tangentPolyfold.levelVal 1) (MPolyfold.tangentShiftMap_symm β)
      exact this
    have hvs : v ∈ X.PObj.shift.tangentPolyfold.smoothSet := mem_iInter.2 fun m =>
      MPolyfold.tangentShiftEquiv_symm_isScSmooth.mapsTo_levelSet m
        ((MPolyfold.mem_shift_levelSet_iff β).2 (mem_iInter.1 hw.2 (m + 1)))
    have hvb : X.PObj.shift.levelVal 1 (X.PObj.shift.tangentProj v) = X.PObj.shift.smoothVal y := by
      apply MPolyfold.level_ext
      rw [← MPolyfold.tangentProj_tangentLower, hlow]
      have : X.PObj.tangentProj w = X.PObj.smoothIncl y₀ 1 := hw.1
      rw [this]; rfl
    have hvf : v ∈ X.liftOne.PObj.tangentFiber (X.liftOne.PObj.smoothIncl y 1) := by
      change X.PObj.shift.tangentProj v = X.PObj.shift.smoothIncl y 1
      exact MPolyfold.level_ext hvb
    have hφ : g.val ∈ X.liftOne.PMor.levelSet 1 := by
      rw [← X.liftOne.mem_levelSet_src_iff, g.src_val]
      exact mem_iInter.1 (X.liftOne.PObj.smoothVal_mem y) 1
    have h := tangentLower_tangentMor_liftOne hφ (hvb.trans g.src_val.symm)
    rw [hg v ⟨hvf, hvs⟩, hlow] at h
    exact h.symm
  obtain ⟨R, -⟩ := X.theorem_7_1_13 (X.PObj.smoothVal y₀) isOpen_univ (mem_univ _)
  obtain ⟨R', hR'⟩ := X.liftOne.theorem_7_1_13 (X.liftOne.PObj.smoothVal y)
    (R.isOpen_U.preimage (MPolyfold.continuous_levelVal 1)) R.mem_U
  rw [X.liftOne.mem_trivialSubgroupInf_iff R']
  have h1 := X.PObj.continuous_shiftSmoothMap.continuousAt.eventually
    ((X.mem_trivialSubgroupInf_iff R).1 hg₀)
  have h2 := X.liftOne.PObj.continuous_smoothVal.continuousAt.eventually
    (R'.isOpen_U.mem_nhds R'.mem_U)
  filter_upwards [h1, h2] with z hz1 hz2
  apply MPolyfold.level_ext
  exact (levelVal_Φ_liftOne R' R hR' g _ hz2).trans hz1

/-- **(VSLUC) for `X` gives (VSLUC) for `X¹`** (the proof of 2021 Proposition 7.4.16), with
`V'(x) = V(x) ∩ U'(x)` under `(X¹)_∞ = X_∞`. -/
theorem isVSLUC_liftOne (h : X.IsVSLUC) : X.liftOne.IsVSLUC := by
  intro y
  set θ := X.PObj.shiftSmoothHomeomorph
  obtain ⟨R, V, hVo, hyV, hVU, hVinv, hVL⟩ := h (θ y)
  obtain ⟨R', hR'⟩ := X.liftOne.theorem_7_1_13 (X.liftOne.PObj.smoothVal y)
    (R.isOpen_U.preimage (MPolyfold.continuous_levelVal 1)) (hVU _ hyV)
  have hΦ := levelVal_Φ_liftOne R' R hR'
  refine ⟨R', θ ⁻¹' V ∩ X.liftOne.PObj.smoothVal ⁻¹' R'.U,
    (hVo.preimage θ.continuous).inter (R'.isOpen_U.preimage X.liftOne.PObj.continuous_smoothVal),
    ⟨hyV, R'.mem_U⟩, fun v hv => hv.2, fun g v hv v' hv' => ?_,
    fun g W hWo hWne hWV hW v hv => ?_⟩
  · refine ⟨hVinv (X.isotropyLevelVal g) (θ v) hv.1 (θ v') ?_, ?_⟩
    · change X.PObj.levelVal 1 (X.liftOne.PObj.smoothVal v') =
        R.Φ _ (X.PObj.levelVal 1 (X.liftOne.PObj.smoothVal v))
      rw [hv']; exact hΦ g _ hv.2
    · change X.liftOne.PObj.smoothVal v' ∈ R'.U
      rw [hv']; exact R'.mapsTo_Φ g hv.2
  · have hfix := hVL (X.isotropyLevelVal g) (θ '' W) (θ.isOpenMap W hWo) (hWne.image θ)
      (image_subset_iff.2 fun w hw => (hWV hw).1) ?_ (θ v) hv.1
    · apply MPolyfold.level_ext
      exact (hΦ g _ hv.2).trans hfix
    · rintro _ ⟨w, hw, rfl⟩
      exact (hΦ g _ (hWV hw).2).symm.trans (congrArg (X.PObj.levelVal 1) (hW w hw))

end EpGroupoid

namespace EP

open EpGroupoid

/-- (ZHOU') for `X` gives (ZHOU') for every `X^i`. -/
theorem isZhou'_lift (A : EP.{u}) (h : A.X.IsZhou') : ∀ i, (A.lift i).X.IsZhou'
  | 0 => h
  | i + 1 => (A.lift i).X.isZhou'_liftOne (isZhou'_lift A h i)

/-- **2021 Proposition 7.4.9, p. 333 (new in the 2021 edition)**: (ZHOU) for `X` gives (ZHOU) for
every `X^i`.  Hypotheses: `DenseSmoothTangent` for `X` (Lemma 7.4.6) and the Part I facts
`SmoothRegular` for every `X^i` (Proposition 7.4.8 for `X^i`). -/
theorem proposition_7_4_9 (A : EP.{u}) (hZ : A.X.IsZhou) (hdt : A.X.PObj.DenseSmoothTangent)
    (hreg : ∀ i, (A.lift i).X.PObj.SmoothRegular) (i : ℕ) : (A.lift i).X.IsZhou :=
  (A.lift i).X.isZhou_of_isZhou' (hreg i) (A.isZhou'_lift (A.X.lemma_7_4_6 hZ hdt) i)

/-- Density of `X_∞` in every level passes to every `X^i`. -/
theorem denseSmooth_lift (A : EP.{u}) (h : A.X.PObj.DenseSmooth) :
    ∀ i, (A.lift i).X.PObj.DenseSmooth
  | 0 => h
  | i + 1 => (denseSmooth_lift A h i).shift

/-- (VSLUC) for `X` gives (VSLUC) for every `X^i`. -/
theorem isVSLUC_lift (A : EP.{u}) (h : A.X.IsVSLUC) : ∀ i, (A.lift i).X.IsVSLUC
  | 0 => h
  | i + 1 => (A.lift i).X.isVSLUC_liftOne (isVSLUC_lift A h i)

/-- **2021 Corollary 7.4.11, p. 334 (new in the 2021 edition)**: under (ZHOU) every `X^i` has
(LUC); (ZHOU) is assumed for `X` only. -/
theorem corollary_7_4_11_all (A : EP.{u}) (hZ : A.X.IsZhou)
    (hdt : A.X.PObj.DenseSmoothTangent) (hreg : ∀ i, (A.lift i).X.PObj.SmoothRegular) (i : ℕ) :
    (A.lift i).X.IsLUC :=
  corollary_7_4_11_lift A (A.proposition_7_4_9 hZ hdt hreg) hreg i

/-- **2021 Theorem 7.4.13, p. 334 (new in the 2021 edition)**: (ZHOU) ⇒ (SLUC); (ZHOU) is
assumed for `X` only. -/
theorem theorem_7_4_13_all (A : EP.{u}) (hZ : A.X.IsZhou)
    (hdt : A.X.PObj.DenseSmoothTangent) (hreg : ∀ i, (A.lift i).X.PObj.SmoothRegular) :
    A.IsSLUC :=
  theorem_7_4_13 A (A.proposition_7_4_9 hZ hdt hreg) hreg

/-- **2021 Proposition 7.4.16, p. 336 (new in the 2021 edition)**: (VSLUC) for `X` gives (VSLUC)
and (LUC) for every `X^i`. -/
theorem proposition_7_4_16_all (A : EP.{u}) (h : A.X.IsVSLUC)
    (hd : A.X.PObj.DenseSmooth) (hc : ∀ i, (A.lift i).X.PObj.SmoothConnected) (i : ℕ) :
    (A.lift i).X.IsVSLUC ∧ (A.lift i).X.IsLUC :=
  ⟨A.isVSLUC_lift h i,
    (A.lift i).X.lemma_7_4_15 (A.denseSmooth_lift hd i) (hc i) (A.isVSLUC_lift h i)⟩

/-- **2021 Proposition 7.4.17, p. 336 (new in the 2021 edition)**: (VSLUC) ⇒ (SLUC); (VSLUC) is
assumed for `X` only. -/
theorem proposition_7_4_17_all (A : EP.{u}) (h : A.X.IsVSLUC)
    (hd : A.X.PObj.DenseSmooth) (hc : ∀ i, (A.lift i).X.PObj.SmoothConnected) : A.IsSLUC :=
  fun i => (A.proposition_7_4_16_all h hd hc i).2

/-- **2021 Theorem 7.4.24, p. 340 (new in the 2021 edition)**: (ZHOU) ⇒ (SLR); (ZHOU) is assumed
for `X` only. -/
theorem theorem_7_4_24_all (A : EP.{u}) (hZ : A.X.IsZhou)
    (hdt : A.X.PObj.DenseSmoothTangent) (hreg : ∀ i, (A.lift i).X.PObj.SmoothRegular) :
    A.IsSLR :=
  theorem_7_4_24 A (A.proposition_7_4_9 hZ hdt hreg) hreg

end EP

/-! ### Proposition 7.4.18 -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- `X_M → X_a` for `a ≤ M`. -/
def levelDownTo {a M : ℕ} (h : a ≤ M) (y : P.Level M) : P.Level a :=
  P.levelMk a (P.levelVal M y) (P.levelSet_antitone h (P.levelVal_mem y))

/-- `X_M → X_a` is continuous. -/
theorem continuous_levelDownTo {a : ℕ} : ∀ {M : ℕ} (h : a ≤ M), Continuous (P.levelDownTo h)
  | 0, h => by
    obtain rfl : a = 0 := by omega
    exact continuous_id.congr fun y => P.level_ext rfl
  | M + 1, h => by
    rcases Nat.lt_or_ge a (M + 1) with h' | h'
    · exact ((continuous_levelDownTo (M := M) (by omega)).comp (P.continuous_levelDown M)).congr
        fun y => P.level_ext rfl
    · obtain rfl : a = M + 1 := by omega
      exact continuous_id.congr fun y => P.level_ext rfl

/-- The open sets `{z ∈ X_∞ | z ∈ O}`, `O ⊆ X_{N+1}` open, form a neighbourhood basis of `X_∞`. -/
theorem exists_level_nhds_smooth {W : Set P.SmoothLevel} (hW : IsOpen W) {w₀ : P.SmoothLevel}
    (hw₀ : w₀ ∈ W) : ∃ (N : ℕ) (O : Set (P.Level (N + 1))), IsOpen O ∧
      P.smoothIncl w₀ (N + 1) ∈ O ∧ ∀ z, P.smoothIncl z (N + 1) ∈ O → z ∈ W := by
  obtain ⟨t, ht, rfl⟩ := isOpen_induced_iff.1 hW
  obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.1 ht _ hw₀
  have hle : ∀ a ∈ I, a ≤ I.sup id + 1 := fun a ha =>
    (Finset.le_sup (f := id) ha).trans (Nat.le_succ _)
  refine ⟨I.sup id, ⋂ a : I, P.levelDownTo (hle a a.2) ⁻¹' u a,
    isOpen_iInter_of_finite fun a => (hu a a.2).1.preimage (P.continuous_levelDownTo _),
    mem_iInter.2 fun a => (hu a a.2).2, fun z hz => hIu fun a ha => mem_iInter.1 hz ⟨a, ha⟩⟩

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- An isotropy element of `X` at a point of `X_1`, as one of `X¹`. -/
def isotropyLevelMk {x₁ : X.PObj.Level 1} (g : X.Isotropy (X.PObj.levelVal 1 x₁)) :
    X.liftOne.Isotropy x₁ :=
  ⟨X.PMor.levelMk 1 g.val ((X.mem_levelSet_src_iff _ 1).1
      (by rw [g.src_val]; exact MPolyfold.levelVal_mem x₁)),
    MPolyfold.level_ext g.src_val, MPolyfold.level_ext g.tgt_val⟩

/-- `G_x` in `X¹` and in `X` agree. -/
theorem isotropyLevelMk_levelVal {x₁ : X.PObj.Level 1} (g : X.liftOne.Isotropy x₁) :
    isotropyLevelMk (X.isotropyLevelVal g) = g :=
  GroupoidStr.Isotropy.ext (MPolyfold.level_ext rfl)

/-- `G_x` in `X¹` → `G_x` in `X` is multiplicative. -/
theorem isotropyLevelVal_mul {x₁ : X.PObj.Level 1} (g h : X.liftOne.Isotropy x₁) :
    X.isotropyLevelVal (g * h) = X.isotropyLevelVal g * X.isotropyLevelVal h :=
  GroupoidStr.Isotropy.ext (X.liftOne_comp_val (g.src_val.trans h.tgt_val.symm))

/-- `G_x` in `X¹` → `G_x` in `X` commutes with inverses. -/
theorem isotropyLevelVal_inv {x₁ : X.PObj.Level 1} (g : X.liftOne.Isotropy x₁) :
    X.isotropyLevelVal g⁻¹ = (X.isotropyLevelVal g)⁻¹ :=
  GroupoidStr.Isotropy.ext rfl

namespace NaturalRep

variable {x₁ : X.PObj.Level 1} (R : X.NaturalRep (X.PObj.levelVal 1 x₁))

open Classical in
/-- `Φ(g)` on `U(x)₁ ⊆ X¹`. -/
def liftOneΦ (g : X.Isotropy (X.PObj.levelVal 1 x₁)) (z : X.PObj.Level 1) : X.PObj.Level 1 :=
  if hz : X.PObj.levelVal 1 z ∈ R.U then
    X.PObj.levelMk 1 (R.Φ g (X.PObj.levelVal 1 z))
      (R.Φ_mem_levelSet g hz (MPolyfold.levelVal_mem z))
  else z

/-- `liftOneΦ` lifts `Φ(g)` on `U(x)₁`. -/
theorem levelVal_liftOneΦ (g : X.Isotropy (X.PObj.levelVal 1 x₁)) {z : X.PObj.Level 1}
    (hz : z ∈ R.liftU) : X.PObj.levelVal 1 (R.liftOneΦ g z) = R.Φ g (X.PObj.levelVal 1 z) := by
  simp only [liftOneΦ, dif_pos (show X.PObj.levelVal 1 z ∈ R.U from hz),
    MPolyfold.levelVal_levelMk]

/-- `liftOneΦ` maps `U(x)₁` to itself. -/
theorem mapsTo_liftOneΦ (g : X.Isotropy (X.PObj.levelVal 1 x₁)) :
    MapsTo (R.liftOneΦ g) R.liftU R.liftU := fun z hz => by
  change X.PObj.levelVal 1 (R.liftOneΦ g z) ∈ R.U
  rw [R.levelVal_liftOneΦ g hz]; exact R.mapsTo_Φ g hz

/-- `Φ(g)` on `U(x)₁` is an sc-diffeomorphism of `X¹`. -/
theorem isScDiffeoOn_liftOneΦ (g : X.Isotropy (X.PObj.levelVal 1 x₁)) :
    X.PObj.shift.IsScDiffeoOn X.PObj.shift (R.liftOneΦ g) (R.liftOneΦ g⁻¹) R.liftU R.liftU := by
  have hd := R.isScDiffeoOn_Φ g
  refine ⟨hd.isScSmoothOn.levelOne fun z hz => R.levelVal_liftOneΦ g hz,
    hd.isScSmoothOn_inv.levelOne fun z hz => R.levelVal_liftOneΦ g⁻¹ hz,
    R.mapsTo_liftOneΦ g, R.mapsTo_liftOneΦ g⁻¹, fun z hz => ?_, fun z hz => ?_⟩
  · refine MPolyfold.level_ext ?_
    rw [R.levelVal_liftOneΦ g⁻¹ (R.mapsTo_liftOneΦ g hz), R.levelVal_liftOneΦ g hz]
    exact hd.left_inv _ hz
  · refine MPolyfold.level_ext ?_
    rw [R.levelVal_liftOneΦ g (R.mapsTo_liftOneΦ g⁻¹ hz), R.levelVal_liftOneΦ g⁻¹ hz]
    exact hd.right_inv _ hz

/-- **The restriction of a natural representation to `X¹`**: if `U(x)₁ = U(x) ∩ X_1` is connected
in `X¹`, it is a natural representation of `x` in `X¹`. -/
def liftOneRep (hc : IsConnected R.liftU) : X.liftOne.NaturalRep x₁ where
  U := R.liftU
  isOpen_U := R.isOpen_liftU
  isConnected_U := hc
  mem_U := R.mem_U
  Φ g := R.liftOneΦ (X.isotropyLevelVal g)
  Γ g := R.levelOneΓ (X.isotropyLevelVal g)
  isScDiffeoOn_Φ g := by
    have := R.isScDiffeoOn_liftOneΦ (X.isotropyLevelVal g)
    rw [← isotropyLevelVal_inv] at this
    exact this
  Φ_mul g h y hy := by
    refine MPolyfold.level_ext ?_
    rw [R.levelVal_liftOneΦ _ hy, R.levelVal_liftOneΦ _ (R.mapsTo_liftOneΦ _ hy),
      R.levelVal_liftOneΦ _ hy, isotropyLevelVal_mul, R.Φ_mul _ _ _ hy]
  isScSmoothOn_Γ g := (R.isScSmoothOn_Γ _).levelOne fun _ hy => R.levelVal_levelOneΓ _ hy
  Γ_self g := MPolyfold.level_ext ((R.levelVal_levelOneΓ _ R.mem_U).trans (R.Γ_self _))
  src_Γ g y hy := R.liftOne_src_levelOneΓ _ hy
  tgt_Γ g y hy := MPolyfold.level_ext <| by
    rw [R.levelVal_liftOneΦ _ hy, ← R.tgt_Γ _ _ hy, ← R.levelVal_levelOneΓ _ hy]
    rfl
  existsUnique_Γ φ hs ht := by
    obtain ⟨g₀, hg₀, huniq⟩ := R.existsUnique_Γ (X.PMor.levelVal 1 φ) hs ht
    refine ⟨isotropyLevelMk g₀, MPolyfold.level_ext ((R.levelVal_levelOneΓ _ hs).trans hg₀),
      fun g' hg' => ?_⟩
    have := huniq (X.isotropyLevelVal g')
      ((R.levelVal_levelOneΓ _ hs).symm.trans (congrArg (X.PMor.levelVal 1) hg'))
    rw [← this]
    exact (isotropyLevelMk_levelVal g').symm

/-- If `ĝ` is the identity on `U(x)₁` in `X¹`, it is the identity on `U(x)` (`X_∞` is dense). -/
theorem eqOn_of_liftOneRep (hd : X.PObj.DenseSmooth) (hc : IsConnected R.liftU)
    (g : X.Isotropy (X.PObj.levelVal 1 x₁))
    (h : ∀ w ∈ R.liftU, (R.liftOneRep hc).Φ (isotropyLevelMk g) w = w) :
    ∀ y ∈ R.U, R.Φ g y = y := by
  have hlev : EqOn (R.Φ g) id (R.U ∩ X.PObj.levelSet 1) := fun y hy =>
    (R.levelVal_liftOneΦ g (z := X.PObj.levelMk 1 y hy.2) hy.1).symm.trans
      (congrArg (X.PObj.levelVal 1) (h (X.PObj.levelMk 1 y hy.2) hy.1))
  have hdense : R.U ⊆ closure (R.U ∩ X.PObj.levelSet 1) :=
    (hd.subset_closure_inter R.isOpen_U).trans
      (closure_mono (inter_subset_inter_right _ fun z hz => mem_iInter.1 hz 1))
  have hall := hlev.of_subset_closure (R.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn
    continuousOn_id inter_subset_left hdense
  exact fun y hy => hall hy

end NaturalRep

/-- The choice of `U(x)` in the proof of 2021 Proposition 7.4.18: `U(x) ∩ X_m` is connected in
`X_m` for every `m ≥ 1`. -/
def NaturalRep.LevelConnected {x : Obj} (R : X.NaturalRep x) : Prop :=
  ∀ m, IsPreconnected {z : X.PObj.Level (m + 1) | X.PObj.levelVal (m + 1) z ∈ R.U}

/-- The level connectedness passes to the restriction to `X¹`. -/
theorem NaturalRep.levelConnected_liftOneRep {x₁ : X.PObj.Level 1}
    {R : X.NaturalRep (X.PObj.levelVal 1 x₁)} (hR : R.LevelConnected) (hc : IsConnected R.liftU) :
    (R.liftOneRep hc).LevelConnected := fun m => by
  have : {z : X.liftOne.PObj.Level (m + 1) |
      X.liftOne.PObj.levelVal (m + 1) z ∈ (R.liftOneRep hc).U} =
      X.PObj.shiftLevelHomeomorph (m + 1) ⁻¹'
        {z : X.PObj.Level (m + 2) | X.PObj.levelVal (m + 2) z ∈ R.U} := rfl
  rw [this, ← Homeomorph.image_symm]
  exact (hR (m + 1)).image _ (X.PObj.shiftLevelHomeomorph (m + 1)).symm.continuous.continuousOn

end EpGroupoid

namespace EP

open EpGroupoid

/-- The core of the proof of 2021 Proposition 7.4.18: under (LUC) for `X^{N+1}`, if `ĝ` is the
identity on the smooth points of a nonempty open subset of `U(x) ∩ X_{N+1}` (open in `X_{N+1}`),
then `ĝ = id` on `U(x)`. -/
theorem eqOn_of_level_smooth : ∀ (N : ℕ) (A : EP.{u}), (A.lift (N + 1)).X.IsLUC →
    A.X.PObj.DenseSmooth → ∀ (y : A.X.PObj.SmoothLevel)
    (R : A.X.NaturalRep (A.X.PObj.smoothVal y)), R.LevelConnected →
    ∀ (g : A.X.Isotropy (A.X.PObj.smoothVal y)) (O : Set (A.X.PObj.Level (N + 1))), IsOpen O →
    (∃ z : A.X.PObj.SmoothLevel, A.X.PObj.smoothIncl z (N + 1) ∈ O ∧ A.X.PObj.smoothVal z ∈ R.U) →
    (∀ z : A.X.PObj.SmoothLevel, A.X.PObj.smoothIncl z (N + 1) ∈ O →
      A.X.PObj.smoothVal z ∈ R.U → R.Φ g (A.X.PObj.smoothVal z) = A.X.PObj.smoothVal z) →
    ∀ y' ∈ R.U, R.Φ g y' = y'
  | 0, A, hLUC, hd, y, R, hRc, g, O, hO, ⟨z₀, hz₀O, hz₀U⟩, hid => by
    have hc : IsConnected R.liftU := ⟨⟨A.X.PObj.smoothIncl y 1, R.mem_U⟩, hRc 0⟩
    set R₁ := R.liftOneRep (x₁ := A.X.PObj.smoothIncl y 1) hc
    refine R.eqOn_of_liftOneRep (x₁ := A.X.PObj.smoothIncl y 1) hd hc g ?_
    have hL : R₁.HasLUC := A.X.liftOne.isLUC_iff_forall_naturalRep.1 hLUC _ R₁
    refine hL (isotropyLevelMk g) (O ∩ R.liftU) (hO.inter R.isOpen_liftU)
      ⟨A.X.PObj.smoothIncl z₀ 1, hz₀O, hz₀U⟩ inter_subset_right ?_
    have hsm : EqOn (R₁.Φ (isotropyLevelMk g)) id ((O ∩ R.liftU) ∩ A.X.PObj.shift.smoothSet) :=
      fun w hw => by
        refine MPolyfold.level_ext
          ((R.levelVal_liftOneΦ (x₁ := A.X.PObj.smoothIncl y 1) g hw.1.2).trans ?_)
        exact hid (A.X.PObj.smoothMk _ ((MPolyfold.mem_shift_smoothSet_iff w).1 hw.2)) hw.1.1 hw.1.2
    have := hsm.of_subset_closure
      ((R₁.isScDiffeoOn_Φ _).isScSmoothOn.continuousOn.mono inter_subset_right)
      continuousOn_id inter_subset_left
      (hd.shift.dense.open_subset_closure_inter (hO.inter R.isOpen_liftU))
    exact fun w hw => this hw
  | N + 1, A, hLUC, hd, y, R, hRc, g, O, hO, ⟨z₀, hz₀O, hz₀U⟩, hid => by
    have hc : IsConnected R.liftU := ⟨⟨A.X.PObj.smoothIncl y 1, R.mem_U⟩, hRc 0⟩
    set R₁ := R.liftOneRep (x₁ := A.X.PObj.smoothIncl y 1) hc
    refine R.eqOn_of_liftOneRep (x₁ := A.X.PObj.smoothIncl y 1) hd hc g ?_
    have hLUC' : (A.liftOne.lift (N + 1)).X.IsLUC := by rw [← lift_succ']; exact hLUC
    exact eqOn_of_level_smooth N A.liftOne hLUC' hd.shift (A.X.PObj.shiftSmoothInv y) R₁
      (NaturalRep.levelConnected_liftOneRep hRc hc) (isotropyLevelMk g)
      (A.X.PObj.shiftLevelMap (N + 1) ⁻¹' O) (hO.preimage (A.X.PObj.continuous_shiftLevelMap _))
      ⟨A.X.PObj.shiftSmoothInv z₀, hz₀O, hz₀U⟩
      (fun z hzO hzU => MPolyfold.level_ext
        ((R.levelVal_liftOneΦ (x₁ := A.X.PObj.smoothIncl y 1) g hzU).trans
        (hid (A.X.PObj.shiftSmoothMap z) hzO hzU)))

/-- (SLUC) ⇒ (VSLUC), the new direction of 2021 Proposition 7.4.18. -/
theorem isVSLUC_of_isSLUC (A : EP.{u}) (h : A.IsSLUC) (hd : A.X.PObj.DenseSmooth)
    (hR : ∀ y : A.X.PObj.SmoothLevel, ∃ R : A.X.NaturalRep (A.X.PObj.smoothVal y),
      R.LevelConnected) : A.X.IsVSLUC := by
  intro y
  obtain ⟨R, hRc⟩ := hR y
  refine ⟨R, A.X.PObj.smoothVal ⁻¹' R.U, R.isOpen_U.preimage A.X.PObj.continuous_smoothVal,
    R.mem_U, fun v hv => hv, fun g v hv v' hv' => ?_, fun g W hWo hWne hWV hW v hv => ?_⟩
  · change A.X.PObj.smoothVal v' ∈ R.U
    rw [hv']; exact R.mapsTo_Φ g hv
  · obtain ⟨w₀, hw₀⟩ := hWne
    obtain ⟨N, O, hO, hw₀O, hOW⟩ := A.X.PObj.exists_level_nhds_smooth hWo hw₀
    exact eqOn_of_level_smooth N A (h (N + 1)) hd y R hRc g O hO ⟨w₀, hw₀O, hWV hw₀⟩
      (fun z hz _ => hW z (hOW z hz)) _ hv

/-- **2021 Proposition 7.4.18, p. 336 (new in the 2021 edition)**: (VSLUC) ⇔ (SLUC).  Hypotheses:
density of `X_∞` (G.73) for `X`, `SmoothConnected` for every `X^i` (for ⇒, Lemma 7.4.15), and one
natural representation `U(x)` per smooth `x` with every `U(x) ∩ X_m` connected (for ⇐, the
text's choice of `U(x)`). -/
theorem proposition_7_4_18 (A : EP.{u}) (hd : A.X.PObj.DenseSmooth)
    (hc : ∀ i, (A.lift i).X.PObj.SmoothConnected)
    (hR : ∀ y : A.X.PObj.SmoothLevel, ∃ R : A.X.NaturalRep (A.X.PObj.smoothVal y),
      R.LevelConnected) : A.X.IsVSLUC ↔ A.IsSLUC :=
  ⟨fun h => A.proposition_7_4_17_all h hd hc, fun h => A.isVSLUC_of_isSLUC h hd hR⟩

end EP

namespace EpGroupoid.Examples

/-- **Witness**: the point ep-groupoid has (VSLUC). -/
theorem isVSLUC_pointEP : pointEP.X.IsVSLUC :=
  haveI : Subsingleton pointEP.Mor := inferInstanceAs (Subsingleton Unit)
  pointEP.X.isVSLUC_of_subsingleton fun _ =>
    ⟨fun a b => GroupoidStr.Isotropy.ext (Subsingleton.elim a.val b.val)⟩

/-- **Witness**: the hypotheses of `EP.proposition_7_4_9` hold for the point ep-groupoid. -/
theorem proposition_7_4_9_pointEP (i : ℕ) : (pointEP.lift i).X.IsZhou :=
  pointEP.proposition_7_4_9 (isZhou_lift_pointEP 0) MPolyfold.denseSmoothTangent_discrete_unit
    smoothRegular_lift_pointEP i

/-- **Witness** for `EP.theorem_7_4_13_all`. -/
theorem theorem_7_4_13_all_pointEP : pointEP.IsSLUC :=
  pointEP.theorem_7_4_13_all (isZhou_lift_pointEP 0)
    MPolyfold.denseSmoothTangent_discrete_unit smoothRegular_lift_pointEP

/-- **Witness** for `EP.theorem_7_4_24_all`. -/
theorem theorem_7_4_24_all_pointEP : pointEP.IsSLR :=
  pointEP.theorem_7_4_24_all (isZhou_lift_pointEP 0)
    MPolyfold.denseSmoothTangent_discrete_unit smoothRegular_lift_pointEP

/-- **Witness** for `EP.proposition_7_4_16_all` and `EP.proposition_7_4_17_all`. -/
theorem proposition_7_4_17_all_pointEP : pointEP.IsSLUC :=
  pointEP.proposition_7_4_17_all isVSLUC_pointEP (smoothRegular_lift_pointEP 0).denseSmooth
    fun i => (smoothRegular_lift_pointEP i).smoothConnected

/-- **Witness**: the hypothesis `NaturalRep.LevelConnected` of `EP.proposition_7_4_18` holds
for the point ep-groupoid. -/
theorem levelConnected_pointEP (y : pointEP.X.PObj.SmoothLevel) :
    ∃ R : pointEP.X.NaturalRep (pointEP.X.PObj.smoothVal y), R.LevelConnected := by
  obtain ⟨R, -⟩ := pointEP.X.theorem_7_1_13 (pointEP.X.PObj.smoothVal y) isOpen_univ (mem_univ _)
  refine ⟨R, fun m => ?_⟩
  have : Subsingleton (pointEP.X.PObj.Level (m + 1)) :=
    ⟨fun a b => MPolyfold.level_ext (Subsingleton.elim (α := Unit) _ _)⟩
  exact Set.subsingleton_of_subsingleton.isPreconnected

/-- **Witness** for `EP.proposition_7_4_18` (both sides hold: `isVSLUC_pointEP`,
`isSLUC_pointEP`). -/
theorem proposition_7_4_18_pointEP : pointEP.X.IsVSLUC ↔ pointEP.IsSLUC :=
  pointEP.proposition_7_4_18 (smoothRegular_lift_pointEP 0).denseSmooth
    (fun i => (smoothRegular_lift_pointEP i).smoothConnected) levelConnected_pointEP

end EpGroupoid.Examples

end Polyfold
