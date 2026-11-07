import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_40

-- the instances of `c₀ →L[ℝ] c₀` used in section `NotB` need a deeper instance search
set_option maxSynthPendingDepth 3

/-!
Round trip for V7_40 (the reduced ep-groupoid `X_R`, p. 243, and Proposition 7.10).

The item lists the definitions `reducedSrc`, `reducedTgt`, `reducedUnit`, `reducedInv`,
`reducedComp`, `reducedGroupoidStr`, `reducedEpGroupoid`, `reductionFunctor`, `reductionIso`
(vocabulary) and eight theorems.  `A` is the conjunction of the types of the theorems, universes
at `0` (`Obj Mor : Type`): the six conditions of Definition 7.3 for `(X, 𝐗^R)`
(`isLocalScDiffeo_reducedSrc/Tgt`, `isScSmoothMap_reducedUnit/Inv`, `exists_isProperMap_reduced`,
`isScSmoothCompSheet_reduced`), `isEffective_reducedEpGroupoid` and `proposition_7_10`.  All of
them except `exists_isProperMap_reduced` take `[T2Space X.ReducedMor]
[ParacompactSpace X.ReducedMor]` as hypotheses (the project's reading: Proposition 7.9's proof
gives neither property of `𝐗^R`; the hypotheses are satisfiable, e.g. for every effective `X`,
`t2Space_reducedMor_of_isEffective`, `paracompactSpace_reducedMor_of_isEffective`).

`B` asserts, for every ep-groupoid `X`, that `𝐗^R` **is** Hausdorff and paracompact and carries
an effective ep-groupoid structure with the reduced groupoid, `X.PObj` and `X.reducedPolyfold`.

* `B ⇒ A` (`B_to_A`): every conjunct of `A` is read off the ep-groupoid `Y` that `B` provides
  (its fields, after identifying its data with the reduced data; the instances are Props, so
  `X.reducedPolyfold` does not depend on which proofs of them are used).  The isotropy and
  functor conjuncts of `proposition_7_10` are the project constructions
  `quotientTrivialSubgroupEquiv` and `reductionFunctor`, which do not involve the banned
  theorems.
* `A ⇒ B` is false: `A` gives nothing when `𝐗^R` is not Hausdorff or not paracompact, while `B`
  claims these properties for every `X`, and **`B` does not hold** (`not_B`): for the translation
  ep-groupoid `ℤ/2 ⋉ O` of the dimension-jumping retract `O` of Remark 4.3 (Part I), `𝐗^R` is not
  Hausdorff (section `NotB` below).  With Hausdorff and paracompact `𝐗^R` as an extra hypothesis,
  `A ⇒ B` holds (`A_to_B_of_hyp`), so this is the only difference.

**Harness note.**  `A`'s statement mentions `reducedEpGroupoid`, whose Prop fields are the banned
theorems themselves, passed as plain applications (`#print` shows they are not abstracted into
`reducedEpGroupoid._proof_N`, except the last).  So every term mentioning `A` reaches them, and
both `#rt_check` and `#rt_check_soft` fail (recorded with `#guard_msgs`).  As in V1_32, we run
`#rt_check_except_defs`, the harness traversal `rtCollect` with the body of `reducedEpGroupoid`
not unfolded: it shows that our proofs reach the banned theorems only through that body (they
never use the fields of `reducedEpGroupoid`; they use those of B's `Y`, resp. `A`'s conjuncts).
-/

namespace RoundTrip.V7_40
open Polyfold

open Lean Elab Command in
/-- `#rt_check_except_defs T`: the proof of `T` reaches the banned theorems of V7_40 only through
the body of the definition `EpGroupoid.reducedEpGroupoid`. -/
elab "#rt_check_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let used := rtCollect env roots.toList
    (NameSet.empty.insert ``Polyfold.EpGroupoid.reducedEpGroupoid)
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do
    throwError "FAIL: {t.getId} uses {bad} outside the body of reducedEpGroupoid"
  logInfo m!"OK: {t.getId} reaches the banned theorems only through the body of reducedEpGroupoid"

open Lean Elab Command in
/-- `#rt_overlap_except_defs T [nᵢ]`: as `#rt_overlap`, with the body of `reducedEpGroupoid` not
unfolded on the side of `T` (the shared theorems reached by the proof of `T` otherwise). -/
elab "#rt_overlap_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let used := rtCollect env (((rtValue? ci).map (·.getUsedConstants)).getD #[]).toList
    (NameSet.empty.insert ``Polyfold.EpGroupoid.reducedEpGroupoid)
  let mut roots : Array Name := #[]
  for b in bs.getElems do
    if let some c := env.find? b.getId then
      roots := roots ++ (((rtValue? c).map (·.getUsedConstants)).getD #[])
  let closure := rtCollect env roots.toList {}
  let shared := used.toList.filter fun n =>
    closure.contains n && (match env.find? n with | some (.thmInfo _) => true | _ => false) &&
      (`Polyfold).isPrefixOf n && !n.isInternal
  logInfo m!"rt_overlap_except_defs {t.getId}: {shared.length} shared non-internal project theorems {shared}"

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_reducedSrc.{0} ∧
  type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_reducedTgt.{0} ∧
  type_of% @Polyfold.EpGroupoid.isScSmoothMap_reducedUnit.{0} ∧
  type_of% @Polyfold.EpGroupoid.isScSmoothMap_reducedInv.{0} ∧
  type_of% @Polyfold.EpGroupoid.exists_isProperMap_reduced.{0} ∧
  type_of% @Polyfold.EpGroupoid.isScSmoothCompSheet_reduced.{0} ∧
  type_of% @Polyfold.EpGroupoid.isEffective_reducedEpGroupoid.{0} ∧
  type_of% @Polyfold.EpGroupoid.proposition_7_10.{0}

theorem A_holds : A :=
  ⟨@EpGroupoid.isLocalScDiffeo_reducedSrc, @EpGroupoid.isLocalScDiffeo_reducedTgt,
    @EpGroupoid.isScSmoothMap_reducedUnit, @EpGroupoid.isScSmoothMap_reducedInv,
    @EpGroupoid.exists_isProperMap_reduced, @EpGroupoid.isScSmoothCompSheet_reduced,
    @EpGroupoid.isEffective_reducedEpGroupoid, @EpGroupoid.proposition_7_10⟩

/-- `A ⇒ B` under the extra hypothesis that every `𝐗^R` is Hausdorff and paracompact: `Y` is
assembled from `A`'s conjuncts (not from `reducedEpGroupoid`'s fields). -/
theorem A_to_B_of_hyp (hA : A)
    (hT : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
      T2Space X.ReducedMor ∧ ParacompactSpace X.ReducedMor) : B := by
  intro Obj Mor _ _ _ _ _ _ X
  obtain ⟨h6, h7⟩ := hT Obj Mor X
  obtain ⟨hs, ht, hu, hi, hp, hc, he, -⟩ := hA
  exact ⟨h6, h7,
    { toGroupoidStr := X.reducedGroupoidStr, PObj := X.PObj, PMor := X.reducedPolyfold,
      isLocalScDiffeo_src := hs X, isLocalScDiffeo_tgt := ht X, isScSmoothMap_unit := hu X,
      isScSmoothMap_inv := hi X, exists_isProperMap := hp X,
      isScSmoothComp := (isScSmoothComp_iff_sheet _ _).2 (hc X) }, rfl, rfl, rfl, he X⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X _ _
    obtain ⟨_, _, ⟨G, PO, PM, h1, h2, h3, h4, h5, h6⟩, hG, hO, hM, -⟩ := hB Obj Mor X
    dsimp only at hG hO hM
    subst hG hO hM
    exact h1
  · intro Obj Mor _ _ _ _ _ _ X _ _
    obtain ⟨_, _, ⟨G, PO, PM, h1, h2, h3, h4, h5, h6⟩, hG, hO, hM, -⟩ := hB Obj Mor X
    dsimp only at hG hO hM
    subst hG hO hM
    exact h2
  · intro Obj Mor _ _ _ _ _ _ X _ _
    obtain ⟨_, _, ⟨G, PO, PM, h1, h2, h3, h4, h5, h6⟩, hG, hO, hM, -⟩ := hB Obj Mor X
    dsimp only at hG hO hM
    subst hG hO hM
    exact h3
  · intro Obj Mor _ _ _ _ _ _ X _ _
    obtain ⟨_, _, ⟨G, PO, PM, h1, h2, h3, h4, h5, h6⟩, hG, hO, hM, -⟩ := hB Obj Mor X
    dsimp only at hG hO hM
    subst hG hO hM
    exact h4
  · intro Obj Mor _ _ _ _ _ _ X
    obtain ⟨_, _, ⟨G, PO, PM, h1, h2, h3, h4, h5, h6⟩, hG, hO, hM, -⟩ := hB Obj Mor X
    dsimp only at hG hO hM
    subst hG hO hM
    exact h5
  · intro Obj Mor _ _ _ _ _ _ X _ _
    obtain ⟨_, _, ⟨G, PO, PM, h1, h2, h3, h4, h5, h6⟩, hG, hO, hM, -⟩ := hB Obj Mor X
    dsimp only at hG hO hM
    subst hG hO hM
    exact (isScSmoothComp_iff_sheet h1 h2.isScSmoothMap).1 h6
  · intro Obj Mor _ _ _ _ _ _ X _ _
    obtain ⟨_, _, ⟨G, PO, PM, h1, h2, h3, h4, h5, h6⟩, hG, hO, hM, hE⟩ := hB Obj Mor X
    dsimp only at hG hO hM
    subst hG hO hM
    exact hE
  · intro Obj Mor _ _ _ _ _ _ X _ _
    obtain ⟨_, _, ⟨G, PO, PM, h1, h2, h3, h4, h5, h6⟩, hG, hO, hM, hE⟩ := hB Obj Mor X
    dsimp only at hG hO hM
    subst hG hO hM
    exact ⟨rfl, rfl, rfl, hE, fun x => ⟨X.quotientTrivialSubgroupEquiv x⟩, ⟨X.reductionFunctor⟩⟩

/-! ### `¬ B`: an ep-groupoid whose `𝐗^R` is not Hausdorff

`O ⊆ ℝ ⊕ X` is the sc-retract of Remark 4.3's moving rank-one projections
(`RemarkFourThree.fam`, Part I, Chapter 4): `O = {(t, z) | L(t) z = z}`, which is `{(t, 0)}` for
`t ≤ 0` (`fam_of_nonpos`) and `{t} × line` for `t > 0` — a dimension-jumping retract.  As
M-polyfold it carries its one chart (`retractPolyfold`).  `ℤ/2 = ℤˣ` acts by `(t, z) ↦ (t, ±z)`,
the restriction of an sc-operator, hence sc-smoothly; `X = ℤ/2 ⋉ O` is the project's translation
ep-groupoid (`EpGroupoid.Examples.actionEpGroupoid`).  Near `(−1, (t, 0))`, `t < 0`, every
morphism has `s = t`, so `(−1, y_n) ∈ 𝐗^T` for `y_n = (−1/(n+1), 0)`, and `[(−1, y_n)] = [(1, y_n)]`
in `𝐗^R`; but `(−1, 0) ∉ 𝐗^T` (the points `o_k = (1/(k+1), (1/(k+1)) e_{n_k}) → 0` of `O` are
moved by `−1`), so `[(−1, 0)] ≠ [(1, 0)]`.  The sequence `[(±1, y_n)]` converges to both, so
`𝐗^R` is not Hausdorff, and `B` (which claims `T2Space 𝐗^R` for every ep-groupoid) fails. -/

namespace NotB
open Polyfold.RemarkFourThree Set Filter Topology

noncomputable section

abbrev E : ScBanach := (ScBanach.const ℝ).prod ScOneExample.X

def Rt : ScRetraction E univ := isLossFamily_fam.retraction fun t y => fam_idem t y

abbrev O : Set (E 0) := Rt.retract

lemma Rt_apply (q : E 0) : Rt q = (q.1, fam q.1 0 q.2) := rfl

lemma mem_O_iff (q : E 0) : q ∈ O ↔ fam q.1 0 q.2 = q.2 := by
  constructor
  · rintro ⟨p, -, rfl⟩
    exact fam_idem p.1 p.2
  · intro h
    exact ⟨q, mem_univ _, Prod.ext rfl h⟩

example : T2Space O := inferInstance
example : ParacompactSpace O := inferInstance

/-- `±1` as a real number. -/
def c (k : ℤˣ) : ℝ := ((k : ℤ) : ℝ)

lemma smul_mem (k : ℤˣ) (y : O) : ((y.1.1, c k • y.1.2) : E 0) ∈ O := by
  rw [mem_O_iff]
  change fam y.1.1 0 (c k • y.1.2) = c k • y.1.2
  rw [map_smul, (mem_O_iff _).1 y.2]

/-- `k • (t, z) = (t, ±z)`. -/
def smulO (k : ℤˣ) (y : O) : O := ⟨(y.1.1, c k • y.1.2), smul_mem k y⟩

instance : MulAction ℤˣ O where
  smul := smulO
  one_smul y := Subtype.ext (Prod.ext rfl (show c 1 • y.1.2 = y.1.2 by simp [c]))
  mul_smul k l y := Subtype.ext (Prod.ext rfl
    (show c (k * l) • y.1.2 = c k • c l • y.1.2 by simp [c, mul_smul]))

lemma smul_val (k : ℤˣ) (y : O) : ((k • y : O) : E 0) = (y.1.1, c k • y.1.2) := rfl

lemma zero_mem : (0 : E 0) ∈ O := by rw [mem_O_iff]; exact map_zero _

def o₀ : O := ⟨0, zero_mem⟩

def P : MPolyfold O := retractPolyfold Rt.isScRetract o₀

/-- `(t, z) ↦ (t, c z)` on `E`. -/
def scaleOp (r : ℝ) : ScOperator E E :=
  ScOperator.prodMap (ScOperator.id _)
    { lvl := fun m => r • ContinuousLinearMap.id ℝ _
      incl_comm := fun m x => by simp }

example (r : ℝ) (q : E 0) : scaleOp r 0 q = (q.1, r • q.2) := rfl

lemma continuous_smulO (k : ℤˣ) : Continuous fun y : O => k • y := by
  show Continuous fun y : O => (⟨(y.1.1, c k • y.1.2), smul_mem k y⟩ : O)
  exact Continuous.subtype_mk ((continuous_subtype_val (p := (· ∈ O))).fst.prodMk
    ((continuous_subtype_val (p := (· ∈ O))).snd.const_smul (c k))) _

theorem isScSmoothMap_smul (k : ℤˣ) : P.IsScSmoothMap P fun y : O => k • y := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ (continuous_smulO k).continuousOn
    fun y _ => ⟨retractChart Rt.isScRetract o₀, retractChart Rt.isScRetract o₀, univ,
      isChart_retractChart _ _, isChart_retractChart _ _, isOpen_univ, mem_univ _,
      fun z _ => ⟨mem_univ _, mem_univ _⟩, fun z _ => mem_univ _, ?_⟩
  have himg : ⇑(retractChart Rt.isScRetract o₀) '' univ = O := by
    ext q; constructor
    · rintro ⟨z, -, rfl⟩; exact z.2
    · intro hq; exact ⟨⟨q, hq⟩, mem_univ _, rfl⟩
  have key : IsScSmoothRetractMap E univ O E univ O (scaleOp (c k) 0) :=
    (scaleOp (c k)).isScSmoothRetractMap Rt.isScRetract (fun q hq => smul_mem k ⟨q, hq⟩)
  have heq : EqOn (scaleOp (c k) 0) (⇑(retractChart Rt.isScRetract o₀) ∘ (fun y : O => k • y) ∘
      (retractChart Rt.isScRetract o₀).symm) O := by
    intro q hq
    have hs : (retractChart Rt.isScRetract o₀).symm q = ⟨q, hq⟩ := by
      classical
      change (if h : q ∈ O then (⟨q, h⟩ : O) else o₀) = ⟨q, hq⟩
      rw [dif_pos hq]
    change (q.1, c k • q.2) = ((k • (retractChart Rt.isScRetract o₀).symm q : O) : E 0)
    rw [hs]
    rfl
  have h2 : IsScSmoothRetractMap E univ (Subtype.val '' (univ : Set O)) E univ O
      (⇑(retractChart Rt.isScRetract o₀) ∘ (fun y : O => k • y) ∘
        (retractChart Rt.isScRetract o₀).symm) := by
    rw [Subtype.coe_image_univ]
    exact key.congr heq
  exact h2

/-- `ℤ/2 = ℤˣ` acting on the retract `O` by `(t, z) ↦ (t, ±z)`: an ep-groupoid. -/
abbrev Xg : EpGroupoid O (ℤˣ × O) :=
  EpGroupoid.Examples.actionEpGroupoid (P := P) isScSmoothMap_smul

/-- Over `t ≤ 0` the retract is `{(t, 0)}`, where `±1` act trivially. -/
lemma smul_eq_self_of_nonpos (k : ℤˣ) (p : O) (hp : p.1.1 ≤ 0) : k • p = p := by
  have h2 : p.1.2 = 0 := by
    rw [← (mem_O_iff _).1 p.2, fam_of_nonpos hp]
    rfl
  apply Subtype.ext
  refine Prod.ext rfl ?_
  show c k • p.1.2 = p.1.2
  rw [h2, smul_zero]

/-- The points `y_n = (−1/(n+1), 0)` of `O`. -/
def yn (n : ℕ) : O := ⟨(-(node n), 0), by rw [mem_O_iff]; exact map_zero _⟩

lemma tendsto_yn : Tendsto yn atTop (𝓝 o₀) := by
  rw [tendsto_subtype_rng]
  have hnode : Tendsto node atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have := hnode.neg.prodMk_nhds (tendsto_const_nhds (x := (0 : ScOneExample.X 0)))
  rw [neg_zero] at this
  exact this

/-- `(−1, y_n) ∈ 𝐗^T`: `s = t` near it. -/
lemma mem_nonEff (n : ℕ) : ((-1 : ℤˣ), yn n) ∈ Xg.nonEffectivePart := by
  rw [EpGroupoid.mem_nonEffectivePart_iff]
  have ho : IsOpen {q : ℤˣ × O | q.2.1.1 < 0} :=
    isOpen_lt (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)) continuous_const
  filter_upwards [ho.mem_nhds (show (yn n).1.1 < 0 from neg_neg_of_pos (node_pos n))] with q hq
  exact (smul_eq_self_of_nonpos q.1 q.2 (le_of_lt hq)).symm

/-- `(−1, 0) ∉ 𝐗^T`: the points `o_k = (1/(k+1), (1/(k+1)) e_{n_k}) ∈ O` tend to `0`, and `−1`
moves them. -/
lemma not_mem_nonEff : ((-1 : ℤˣ), o₀) ∉ Xg.nonEffectivePart := by
  rw [EpGroupoid.mem_nonEffectivePart_iff]
  intro h
  have hmem : ∀ k, pt k ∈ O := fun k =>
    ⟨pt k, mem_univ _, Prod.ext rfl (fam_node_smul_δv k (node k))⟩
  have hnode : Tendsto node atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hpt : Tendsto (fun k => (⟨pt k, hmem k⟩ : O)) atTop (𝓝 o₀) := by
    rw [tendsto_subtype_rng]
    refine (hnode.prodMk_nhds ?_)
    refine tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
      (fun k => ?_) hnode)
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (node_pos k)]
    exact mul_le_of_le_one_right (node_pos k).le (norm_δv_le _)
  have h2 : Tendsto (fun k => ((-1 : ℤˣ), (⟨pt k, hmem k⟩ : O))) atTop
      (𝓝 ((-1 : ℤˣ), o₀)) := tendsto_const_nhds.prodMk_nhds hpt
  obtain ⟨k, hk⟩ := (h2.eventually h).exists
  have hk' : (pt k).2 = c (-1) • (pt k).2 := congrArg (fun p : O => p.1.2) hk
  have hv := congrArg (fun z : ScOneExample.c0 => z (nk k)) hk'
  simp only [pt, c, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_smul, one_smul,
    ZeroAtInftyContinuousMap.coe_neg, ZeroAtInftyContinuousMap.coe_smul, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, δv_apply] at hv
  simp only [ite_true, mul_one] at hv
  have := node_pos k
  linarith

lemma reducedπ_eq (n : ℕ) :
    Xg.reducedπ ((-1 : ℤˣ), yn n) = Xg.reducedπ ((1 : ℤˣ), yn n) := by
  rw [EpGroupoid.reducedπ_eq_iff, EpGroupoid.reducedRel_iff]
  refine ⟨((-1 : ℤˣ), yn n), mem_nonEff n, ?_, ?_⟩
  · show yn n = (-1 : ℤˣ) • yn n
    exact (smul_eq_self_of_nonpos _ _ (neg_nonpos.2 (node_pos n).le)).symm
  · show ((-1 : ℤˣ), yn n) = ((1 : ℤˣ) * (-1), yn n)
    rw [one_mul]

lemma reducedπ_ne : Xg.reducedπ ((-1 : ℤˣ), o₀) ≠ Xg.reducedπ ((1 : ℤˣ), o₀) := by
  rw [Ne, EpGroupoid.reducedπ_eq_iff, EpGroupoid.reducedRel_iff]
  rintro ⟨k, hk, -, he⟩
  have he' : ((-1 : ℤˣ), o₀) = ((1 : ℤˣ) * k.1, k.2) := he
  rw [one_mul] at he'
  have hk' : k = ((-1 : ℤˣ), o₀) := he'.symm
  exact not_mem_nonEff (hk' ▸ hk)

/-- **`𝐗^R` is not Hausdorff** for `ℤ/2 ⋉ O`. -/
theorem not_t2 : ¬ T2Space Xg.ReducedMor := by
  intro _
  have h1 : Tendsto (fun n => Xg.reducedπ ((-1 : ℤˣ), yn n)) atTop
      (𝓝 (Xg.reducedπ ((-1 : ℤˣ), o₀))) :=
    (Xg.continuous_reducedπ.tendsto _).comp (tendsto_const_nhds.prodMk_nhds tendsto_yn)
  have h2 : Tendsto (fun n => Xg.reducedπ ((1 : ℤˣ), yn n)) atTop
      (𝓝 (Xg.reducedπ ((1 : ℤˣ), o₀))) :=
    (Xg.continuous_reducedπ.tendsto _).comp (tendsto_const_nhds.prodMk_nhds tendsto_yn)
  have h1' : Tendsto (fun n => Xg.reducedπ ((1 : ℤˣ), yn n)) atTop
      (𝓝 (Xg.reducedπ ((-1 : ℤˣ), o₀))) := h1.congr fun n => reducedπ_eq n
  exact reducedπ_ne (tendsto_nhds_unique h1' h2)

end

end NotB

/-- **`B` does not hold**: for `ℤ/2 ⋉ O` (`NotB.Xg`), `𝐗^R` is not Hausdorff. -/
theorem not_B : ¬ B := fun hB => by
  obtain ⟨h, -, -⟩ := hB NotB.O (ℤˣ × NotB.O) NotB.Xg
  exact NotB.not_t2 h

/-- Hence `A ⇒ B` is false (`A` holds). -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/--
error: rt_check FAIL: RoundTrip.V7_40.B_to_A uses [Polyfold.EpGroupoid.isLocalScDiffeo_reducedSrc,
 Polyfold.EpGroupoid.isLocalScDiffeo_reducedTgt,
 Polyfold.EpGroupoid.isScSmoothMap_reducedUnit,
 Polyfold.EpGroupoid.isScSmoothMap_reducedInv,
 Polyfold.EpGroupoid.exists_isProperMap_reduced,
 Polyfold.EpGroupoid.isScSmoothCompSheet_reduced]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V7_40.B_to_A [Polyfold.EpGroupoid.isLocalScDiffeo_reducedSrc,
  Polyfold.EpGroupoid.isLocalScDiffeo_reducedTgt, Polyfold.EpGroupoid.isScSmoothMap_reducedUnit,
  Polyfold.EpGroupoid.isScSmoothMap_reducedInv, Polyfold.EpGroupoid.exists_isProperMap_reduced,
  Polyfold.EpGroupoid.isScSmoothCompSheet_reduced,
  Polyfold.EpGroupoid.isEffective_reducedEpGroupoid, Polyfold.EpGroupoid.proposition_7_10]

/--
error: rt_check_soft FAIL: RoundTrip.V7_40.B_to_A uses [Polyfold.EpGroupoid.isLocalScDiffeo_reducedSrc,
 Polyfold.EpGroupoid.isLocalScDiffeo_reducedTgt,
 Polyfold.EpGroupoid.isScSmoothMap_reducedUnit,
 Polyfold.EpGroupoid.isScSmoothMap_reducedInv,
 Polyfold.EpGroupoid.exists_isProperMap_reduced]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V7_40.B_to_A [Polyfold.EpGroupoid.isLocalScDiffeo_reducedSrc,
  Polyfold.EpGroupoid.isLocalScDiffeo_reducedTgt, Polyfold.EpGroupoid.isScSmoothMap_reducedUnit,
  Polyfold.EpGroupoid.isScSmoothMap_reducedInv, Polyfold.EpGroupoid.exists_isProperMap_reduced,
  Polyfold.EpGroupoid.isScSmoothCompSheet_reduced,
  Polyfold.EpGroupoid.isEffective_reducedEpGroupoid, Polyfold.EpGroupoid.proposition_7_10]

#rt_check_except_defs RoundTrip.V7_40.B_to_A [Polyfold.EpGroupoid.isLocalScDiffeo_reducedSrc,
  Polyfold.EpGroupoid.isLocalScDiffeo_reducedTgt, Polyfold.EpGroupoid.isScSmoothMap_reducedUnit,
  Polyfold.EpGroupoid.isScSmoothMap_reducedInv, Polyfold.EpGroupoid.exists_isProperMap_reduced,
  Polyfold.EpGroupoid.isScSmoothCompSheet_reduced,
  Polyfold.EpGroupoid.isEffective_reducedEpGroupoid, Polyfold.EpGroupoid.proposition_7_10]
#rt_check_except_defs RoundTrip.V7_40.A_to_B_of_hyp [Polyfold.EpGroupoid.isLocalScDiffeo_reducedSrc,
  Polyfold.EpGroupoid.isLocalScDiffeo_reducedTgt, Polyfold.EpGroupoid.isScSmoothMap_reducedUnit,
  Polyfold.EpGroupoid.isScSmoothMap_reducedInv, Polyfold.EpGroupoid.exists_isProperMap_reduced,
  Polyfold.EpGroupoid.isScSmoothCompSheet_reduced,
  Polyfold.EpGroupoid.isEffective_reducedEpGroupoid, Polyfold.EpGroupoid.proposition_7_10]

#rt_overlap RoundTrip.V7_40.B_to_A [Polyfold.EpGroupoid.isLocalScDiffeo_reducedSrc,
  Polyfold.EpGroupoid.isLocalScDiffeo_reducedTgt, Polyfold.EpGroupoid.isScSmoothMap_reducedUnit,
  Polyfold.EpGroupoid.isScSmoothMap_reducedInv, Polyfold.EpGroupoid.exists_isProperMap_reduced,
  Polyfold.EpGroupoid.isScSmoothCompSheet_reduced,
  Polyfold.EpGroupoid.isEffective_reducedEpGroupoid, Polyfold.EpGroupoid.proposition_7_10]

#rt_check RoundTrip.V7_40.not_B [Polyfold.EpGroupoid.isLocalScDiffeo_reducedSrc,
  Polyfold.EpGroupoid.isLocalScDiffeo_reducedTgt, Polyfold.EpGroupoid.isScSmoothMap_reducedUnit,
  Polyfold.EpGroupoid.isScSmoothMap_reducedInv, Polyfold.EpGroupoid.exists_isProperMap_reduced,
  Polyfold.EpGroupoid.isScSmoothCompSheet_reduced,
  Polyfold.EpGroupoid.isEffective_reducedEpGroupoid, Polyfold.EpGroupoid.proposition_7_10]
#print axioms RoundTrip.V7_40.not_B

#rt_overlap_except_defs RoundTrip.V7_40.B_to_A [Polyfold.EpGroupoid.isLocalScDiffeo_reducedSrc,
  Polyfold.EpGroupoid.isLocalScDiffeo_reducedTgt, Polyfold.EpGroupoid.isScSmoothMap_reducedUnit,
  Polyfold.EpGroupoid.isScSmoothMap_reducedInv, Polyfold.EpGroupoid.exists_isProperMap_reduced,
  Polyfold.EpGroupoid.isScSmoothCompSheet_reduced,
  Polyfold.EpGroupoid.isEffective_reducedEpGroupoid, Polyfold.EpGroupoid.proposition_7_10]

end RoundTrip.V7_40
