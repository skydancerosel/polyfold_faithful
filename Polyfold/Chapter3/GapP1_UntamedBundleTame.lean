import Polyfold.Chapter3.GapP1_UntamedBundle
import Polyfold.Chapter3.TameGerms
import Polyfold.Chapter2.StrongBundlePullback

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §2.6 and §3.6:
the phrase "tame strong bundle `Y → X`" of **Definition 3.6.6** and **Theorem 3.6.8** (p. 136) and
"a tame strong bundle retraction is one for which the retraction `r` is tame" (p. 66), for the
untamed example of `GapP1_UntamedBundle.lean`.  Gap G.79.

# The strong bundle of the untamed example is tame

## The text, paraphrased

(p. 66) A tame strong bundle retraction is a strong bundle retraction `R(u, h) = (r(u), Γ(u, h))`
whose `r` is tame.  (p. 136) "`P : Y → X` is a strong bundle over a tame M-polyfold"; Definition
3.6.6 and Theorem 3.6.8 speak of "a tame strong bundle `Y → X`", which the text does not define
separately.

## What is formalized

Both readings of "tame strong bundle" hold for the bundle `K → O` of `GapP1_UntamedBundle.lean`:
the base `O` is a tame M-polyfold (`isTame_polyO`), and

* `chartTame`: the strong bundle chart `Φ(((0, t), 0), (0, h)) = (t, (0, h))` of `K → O`, defined
  on all of `K`, over the chart `t : O → {t < 1} ⊆ ℝ¹`, onto the local strong bundle
  `R'(U' ◁ F)`, `U' = {t < 1} ⊆ ℝ¹`, `R'(t, (x, h)) = (t, (0, π_t h))`
  (`isStrongBundleRetraction_RT`), which covers the identity retraction of `U'`;
* `compatible_chart0_chartTame`, `isChart_chartTame`: it is compatible with the chart `chart0` of
  the bundle (the transition maps are restrictions of sc-operators);
* `isTameChart_chartTame`, `exists_isTameChart`: **`K → O` has a strong bundle chart with a tame
  base retraction around every point**, i.e. an equivalent atlas of tame strong bundle charts.

In this tame chart the germ of the section at `x₀` has no germ data
(`not_isScFredholmGermTame_sec_zero` in `GapP1_UntamedBundleTheorem.lean`); its germ data live in
the chart `chart0`, whose retraction is not tame.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace UntamedCorner

open ScOneExample Jump StrongRetr

/-! ### The tame strong bundle retraction `R'(t, (x, h)) = (t, (0, π_t h))` -/

section Fibre

variable (V : ScBanach)

/-- `(t, (x, h)) ↦ (t, h)` on `ℝ¹ ⊕ (ℝ ⊕ V)`. -/
def tfT : ScOperator ((rnSc 1).prod ((ScBanach.const ℝ).prod V)) ((ScBanach.const ℝ).prod V) where
  lvl m := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
      (ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) (ℝ × V m))).prod
    ((ContinuousLinearMap.snd ℝ ℝ (V m)).comp (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) (ℝ × V m)))
  incl_comm _ _ := rfl

variable {V}

/-- The strong bundle retraction over `ℝ¹` built from a jump family `J` on the fibre scale `V`:
`(t, (x, h)) ↦ (t, (0, A(t)h))`. -/
def RTG (J : Family V) (q : ((rnSc 1).prod ((ScBanach.const ℝ).prod V)) 0) :
    ((rnSc 1).prod ((ScBanach.const ℝ).prod V)) 0 :=
  (q.1, (0, J.A 0 (q.1 0) q.2.2))

theorem isScSmooth_RTG (J : Family V) :
    IsScSmooth (E := (rnSc 1).prod ((ScBanach.const ℝ).prod V))
      (F := (rnSc 1).prod ((ScBanach.const ℝ).prod V)) univ (RTG J) := by
  have hU := isScDomain_univ ((rnSc 1).prod ((ScBanach.const ℝ).prod V))
  have h1 := ((rnSc 1).prodFstOp ((ScBanach.const ℝ).prod V)).isScSmooth hU
  have h2 := (ScOperator.zeroOp ((rnSc 1).prod ((ScBanach.const ℝ).prod V))
    (ScBanach.const ℝ)).isScSmooth hU
  have h3 := IsScSmooth.comp hU (isScDomain_univ _) J.isScSmooth_map ((tfT V).isScSmooth hU)
    (mapsTo_univ _ _)
  exact (h1.scPair hU (h2.scPair hU h3)).congr hU fun q _ => rfl

end Fibre

/-- **The tame strong bundle retraction** `R'(t, (x, h)) = (t, (0, π_t h))` on `{t < 1} ◁ F`. -/
def RT : (Fin 1 → ℝ) × F 0 → (Fin 1 → ℝ) × F 0 := RTG family

lemma RT_apply (q : (Fin 1 → ℝ) × F 0) : RT q = (q.1, (0, proj (q.1 0) q.2.2)) := rfl

/-- `R'` is a strong bundle retraction of `{t < 1} ◁ F`; it covers the identity of `{t < 1}`. -/
theorem isStrongBundleRetraction_RT : IsStrongBundleRetraction (E := rnSc 1) (F := F) Ut RT where
  mapsTo q hq := ⟨hq.1, mem_univ _⟩
  fst_independent _ _ _ _ := rfl
  fiber_linear u _ :=
    ⟨fun h h' => Prod.ext (add_zero (0 : ℝ)).symm (map_add (proj (u 0)) h.2 h'.2),
      fun c h => Prod.ext (smul_zero c).symm (map_smul (proj (u 0)) c h.2)⟩
  preserves_filtration m k _ u _ hu h hh := by
    obtain ⟨h', rfl⟩ := hh
    refine ⟨hu, ⟨(0, family.A k (u 0) h'.2), ?_⟩⟩
    rw [F_toBase, F_toBase, family.toBase_A]; rfl
  isScSmooth_zero :=
    (isScSmooth_RTG family).of_subset (relOpen_Ut.prod_univ F).isScDomain (subset_univ _)
  isScSmooth_one := by
    have hdom := (relOpen_Ut.prod_univ F.shift).isScDomain
    refine ((isScSmooth_RTG family.shift).of_subset hdom (subset_univ _)).congr hdom fun q _ => ?_
    refine Prod.ext rfl ?_
    change ((0 : ℝ), family.A 1 (q.1 0) q.2.2) =
      invFun (F.toBase 1) (0, proj (q.1 0) (X.toBase 1 q.2.2))
    have h : F.toBase 1 ((0 : ℝ), family.A 1 (q.1 0) q.2.2) =
        (0, proj (q.1 0) (X.toBase 1 q.2.2)) := by
      rw [F_toBase, family.toBase_A]; rfl
    rw [← h, leftInverse_invFun (F.toBase_injective 1)]
  idem q hq := by
    rw [RT_apply, RT_apply]
    exact Prod.ext rfl (Prod.ext rfl (proj_proj hq.1 q.2.2))

lemma mem_KT {q : (Fin 1 → ℝ) × F 0} :
    q ∈ RT '' (Ut ×ˢ (univ : Set (F 0))) ↔
      q.1 0 < 1 ∧ q.2.1 = 0 ∧ proj (q.1 0) q.2.2 = q.2.2 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [RT_apply]
    exact ⟨hp.1, rfl, proj_proj hp.1 _⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨q, ⟨h1, mem_univ _⟩, ?_⟩
    rw [RT_apply]
    exact Prod.ext rfl (Prod.ext h2.symm h3)

/-! ### The tame strong bundle chart -/

/-- The chart map `Φ(((0, t), 0), (0, h)) = (t, (0, h))`. -/
def fwdT (y : Kt) : (Fin 1 → ℝ) × F 0 := (fun _ => tco (kproj y), (y : E 0 × F 0).2)

/-- The inverse `(t, k) ↦ (((0, t), 0), k)`, as a map into `E₀ × F₀`. -/
def bwdT (q : (Fin 1 → ℝ) × F 0) : E 0 × F 0 := (((0, q.1 0), 0), q.2)

lemma fwdT_mem_KT (y : Kt) : fwdT y ∈ RT '' (Ut ×ˢ (univ : Set (F 0))) := by
  obtain ⟨h1, h2, h3⟩ := mem_K.1 y.2
  exact mem_KT.2 ⟨(mem_O.1 h1).2.1, h2, h3⟩

lemma bwdT_mem_K {q : (Fin 1 → ℝ) × F 0} (hq : q ∈ RT '' (Ut ×ˢ (univ : Set (F 0)))) :
    bwdT q ∈ R '' (U ×ˢ (univ : Set (F 0))) := by
  obtain ⟨h1, h2, h3⟩ := mem_KT.1 hq
  exact mem_K.2 ⟨mem_O.2 ⟨rfl, h1, rfl⟩, h2, h3⟩

lemma bwdT_fwdT (y : Kt) : bwdT (fwdT y) = (y : E 0 × F 0) := by
  obtain ⟨h1, -, -⟩ := mem_K.1 y.2
  obtain ⟨ha, -, hw⟩ := mem_O.1 h1
  exact Prod.ext (Prod.ext (Prod.ext ha.symm rfl) hw.symm) rfl

lemma fwdT_bwdT (q : (Fin 1 → ℝ) × F 0) (y : Kt) (hy : (y : E 0 × F 0) = bwdT q) :
    fwdT y = q := by
  have ht : tco (kproj y) = q.1 0 := by
    change (y : E 0 × F 0).1.1.2 = _
    rw [hy]; rfl
  refine Prod.ext (funext fun i => by rw [Subsingleton.elim i 0]; exact ht) ?_
  change (y : E 0 × F 0).2 = q.2
  rw [hy]; rfl

open scoped Classical in
/-- The tame bundle chart as a partial equivalence. -/
def chartTamePE : PartialEquiv Kt ((Fin 1 → ℝ) × F 0) where
  toFun := fwdT
  invFun q := if h : q ∈ RT '' (Ut ×ˢ (univ : Set (F 0))) then ⟨bwdT q, bwdT_mem_K h⟩
    else ⟨0, zero_mem_K⟩
  source := univ
  target := RT '' (Ut ×ˢ (univ : Set (F 0)))
  map_source' y _ := fwdT_mem_KT y
  map_target' _ _ := mem_univ _
  left_inv' y _ := by
    dsimp only
    rw [dif_pos (fwdT_mem_KT y)]
    exact Subtype.ext (bwdT_fwdT y)
  right_inv' q hq := by
    dsimp only
    rw [dif_pos hq]
    exact fwdT_bwdT q _ rfl

lemma continuous_fwdT : Continuous fwdT :=
  (continuous_pi fun _ => continuous_tco.comp bundle.continuous).prodMk
    (continuous_snd.comp continuous_subtype_val)

lemma continuous_bwdT : Continuous bwdT :=
  ((continuous_const.prodMk ((continuous_apply 0).comp continuous_fst)).prodMk
    continuous_const).prodMk continuous_snd

/-- **The tame strong bundle chart of `K → O`**: over the chart `t` of `O`, onto the local strong
bundle `R'({t < 1} ◁ F)`; its base retraction is the identity. -/
def chartTame : StrongBundleChart polyO kproj where
  φ := chartT
  isChart := isChart_chartT
  F := F
  U := Ut
  R := RT
  relOpen := relOpen_Ut
  isRetraction := isStrongBundleRetraction_RT
  base_retract := by
    change (fun u => u) '' Ut = Ut
    exact image_id' _
  toPartialEquiv := chartTamePE
  source_eq := preimage_univ.symm
  target_eq := rfl
  continuousOn_toFun := continuous_fwdT.continuousOn
  continuousOn_invFun := by
    classical
    change ContinuousOn (fun q : (Fin 1 → ℝ) × F 0 =>
      if h : q ∈ RT '' (Ut ×ˢ (univ : Set (F 0))) then (⟨bwdT q, bwdT_mem_K h⟩ : Kt)
      else ⟨0, zero_mem_K⟩) (RT '' (Ut ×ˢ (univ : Set (F 0))))
    rw [continuousOn_iff_continuous_domRestrict]
    have e : (RT '' (Ut ×ˢ (univ : Set (F 0)))).domRestrict
        (fun q : (Fin 1 → ℝ) × F 0 =>
          if h : q ∈ RT '' (Ut ×ˢ (univ : Set (F 0))) then (⟨bwdT q, bwdT_mem_K h⟩ : Kt)
          else ⟨0, zero_mem_K⟩) =
        fun q => ⟨bwdT q.1, bwdT_mem_K q.2⟩ := by
      funext q
      change (if h : (q : (Fin 1 → ℝ) × F 0) ∈ RT '' (Ut ×ˢ (univ : Set (F 0))) then
        (⟨bwdT q, bwdT_mem_K h⟩ : Kt) else ⟨0, zero_mem_K⟩) = _
      rw [dif_pos q.2]
    rw [e]
    exact (continuous_bwdT.comp continuous_subtype_val).subtype_mk _
  covers _ _ := rfl
  fiber_linear x _ := isLinearMap_fibEquiv x

/-! ### Compatibility with the chart `chart0` -/

section Ops

variable (G : ScBanach)

/-- `(((a, t), w), k) ↦ (t, k)` as an sc-operator `E ⊕ G → ℝ¹ ⊕ G`. -/
def opA : ScOperator (E.prod G) ((rnSc 1).prod G) where
  lvl m := ((tauOp m).comp (ContinuousLinearMap.fst ℝ (E m) (G m))).prod
    (ContinuousLinearMap.snd ℝ (E m) (G m))
  incl_comm m x := Prod.ext (tauOp.incl_comm m x.1) rfl

/-- `(t, k) ↦ (((0, t), 0), k)` as an sc-operator `ℝ¹ ⊕ G → E ⊕ G`. -/
def opB : ScOperator ((rnSc 1).prod G) (E.prod G) where
  lvl m := ((sigmaOp m).comp (ContinuousLinearMap.fst ℝ ((rnSc 1) m) (G m))).prod
    (ContinuousLinearMap.snd ℝ ((rnSc 1) m) (G m))
  incl_comm m x := Prod.ext (sigmaOp.incl_comm m x.1) rfl

end Ops

lemma overlap0T : chart0.overlap chartTame = R '' (U ×ˢ (univ : Set (F 0))) := by
  ext p
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hp
    exact ⟨⟨p, hp⟩, ⟨mem_univ _, mem_univ _⟩, rfl⟩

lemma overlapT0 : chartTame.overlap chart0 = RT '' (Ut ×ˢ (univ : Set (F 0))) := by
  ext q
  constructor
  · rintro ⟨y, -, rfl⟩
    exact fwdT_mem_KT y
  · intro hq
    exact ⟨⟨bwdT q, bwdT_mem_K hq⟩, ⟨mem_univ _, mem_univ _⟩, fwdT_bwdT q _ rfl⟩

lemma transition0T {p : E 0 × F 0} (hp : p ∈ R '' (U ×ˢ (univ : Set (F 0)))) :
    chart0.transition chartTame p = opA F 0 p := by
  change chartTame (chart0.toPartialEquiv.symm p) = _
  have h : chart0.toPartialEquiv.symm p = ⟨p, hp⟩ :=
    Subtype.ext (chart0.toPartialEquiv.right_inv (show p ∈ chart0.toPartialEquiv.target from hp))
  rw [h]; rfl

lemma transitionT0 {q : (Fin 1 → ℝ) × F 0} (hq : q ∈ RT '' (Ut ×ˢ (univ : Set (F 0)))) :
    chartTame.transition chart0 q = opB F 0 q := by
  change chart0 (chartTame.toPartialEquiv.symm q) = _
  have h : chartTame.toPartialEquiv.symm q = ⟨bwdT q, bwdT_mem_K hq⟩ := by
    classical
    change (if h : q ∈ RT '' (Ut ×ˢ (univ : Set (F 0))) then (⟨bwdT q, bwdT_mem_K h⟩ : Kt)
      else ⟨0, zero_mem_K⟩) = _
    rw [dif_pos hq]
  rw [h]; rfl

lemma opA_mem {p : E 0 × F 0} (hp : p ∈ R '' (U ×ˢ (univ : Set (F 0)))) :
    opA F 0 p ∈ RT '' (Ut ×ˢ (univ : Set (F 0))) :=
  fwdT_mem_KT ⟨p, hp⟩

lemma opB_mem {q : (Fin 1 → ℝ) × F 0} (hq : q ∈ RT '' (Ut ×ˢ (univ : Set (F 0)))) :
    opB F 0 q ∈ R '' (U ×ˢ (univ : Set (F 0))) :=
  bwdT_mem_K hq

/-- The transition `chart0 → chartTame` on `[1]`. -/
lemma shiftFiber_transition0T {p : E 0 × F 1}
    (hp : (p.1, F.toBase 1 p.2) ∈ R '' (U ×ˢ (univ : Set (F 0)))) :
    shiftFiber (chart0.transition chartTame) p = opA F.shift 0 p := by
  have h := transition0T hp
  refine Prod.ext ?_ ?_
  · have h1 : (chart0.transition chartTame (p.1, F.toBase 1 p.2)).1 =
        (opA F 0 (p.1, F.toBase 1 p.2)).1 := congrArg Prod.fst h
    exact h1
  · change invFun (F.toBase 1) (chart0.transition chartTame (p.1, F.toBase 1 p.2)).2 = p.2
    have h2 : (chart0.transition chartTame (p.1, F.toBase 1 p.2)).2 = F.toBase 1 p.2 :=
      congrArg Prod.snd h
    exact (congrArg (invFun (F.toBase 1)) h2).trans
      (leftInverse_invFun (F.toBase_injective 1) p.2)

/-- The transition `chartTame → chart0` on `[1]`. -/
lemma shiftFiber_transitionT0 {q : (Fin 1 → ℝ) × F 1}
    (hq : (q.1, F.toBase 1 q.2) ∈ RT '' (Ut ×ˢ (univ : Set (F 0)))) :
    shiftFiber (chartTame.transition chart0) q = opB F.shift 0 q := by
  have h := transitionT0 hq
  refine Prod.ext ?_ ?_
  · have h1 : (chartTame.transition chart0 (q.1, F.toBase 1 q.2)).1 =
        (opB F 0 (q.1, F.toBase 1 q.2)).1 := congrArg Prod.fst h
    exact h1
  · change invFun (F.toBase 1) (chartTame.transition chart0 (q.1, F.toBase 1 q.2)).2 = q.2
    have h2 : (chartTame.transition chart0 (q.1, F.toBase 1 q.2)).2 = F.toBase 1 q.2 :=
      congrArg Prod.snd h
    exact (congrArg (invFun (F.toBase 1)) h2).trans
      (leftInverse_invFun (F.toBase_injective 1) q.2)

/-- **The tame chart is compatible with the chart `chart0` of the bundle** (2021 Definition
2.6.4): the transition maps `(((0, t), 0), k) ↦ (t, k)` and `(t, k) ↦ (((0, t), 0), k)` are
restrictions of sc-operators, on `[0]` and on `[1]`. -/
theorem compatible_chart0_chartTame : chart0.Compatible chartTame := by
  have hK0 : IsScRetract (E.prod F) (C ×ˢ univ) (chart0.overlap chartTame) := by
    rw [overlap0T]; exact chart0.isScRetract
  have hKT : IsScRetract ((rnSc 1).prod F) (univ ×ˢ univ) (chartTame.overlap chart0) := by
    rw [overlapT0]; exact chartTame.isScRetract
  have hK01 : IsScRetract (E.prod F.shift) (C ×ˢ univ)
      (strongShiftOne (chart0.overlap chartTame)) := by
    rw [overlap0T]; exact chart0.isScRetract_one
  have hKT1 : IsScRetract ((rnSc 1).prod F.shift) (univ ×ˢ univ)
      (strongShiftOne (chartTame.overlap chart0)) := by
    rw [overlapT0]; exact chartTame.isScRetract_one
  refine ⟨?_, ?_, ?_, ?_, fun x hx h => ?_, fun x hx h => ?_⟩
  · refine ((opA F).isScSmoothRetractMap hK0 fun p hp => ?_).congr fun p hp => ?_
    · rw [overlap0T] at hp; rw [overlapT0]; exact opA_mem hp
    · rw [overlap0T] at hp; exact (transition0T hp).symm
  · refine ((opB F).isScSmoothRetractMap hKT fun q hq => ?_).congr fun q hq => ?_
    · rw [overlapT0] at hq; rw [overlap0T]; exact opB_mem hq
    · rw [overlapT0] at hq; exact (transitionT0 hq).symm
  · refine ((opA F.shift).isScSmoothRetractMap hK01 fun p hp => ?_).congr fun p hp => ?_
    · rw [overlap0T] at hp; rw [overlapT0]
      have hp' : (p.1, F.toBase 1 p.2) ∈ R '' (U ×ˢ (univ : Set (F 0))) := hp
      exact opA_mem hp'
    · rw [overlap0T] at hp
      have hp' : (p.1, F.toBase 1 p.2) ∈ R '' (U ×ˢ (univ : Set (F 0))) := hp
      exact (shiftFiber_transition0T hp').symm
  · refine ((opB F.shift).isScSmoothRetractMap hKT1 fun q hq => ?_).congr fun q hq => ?_
    · rw [overlapT0] at hq; rw [overlap0T]
      have hq' : (q.1, F.toBase 1 q.2) ∈ RT '' (Ut ×ˢ (univ : Set (F 0))) := hq
      exact opB_mem hq'
    · rw [overlapT0] at hq
      have hq' : (q.1, F.toBase 1 q.2) ∈ RT '' (Ut ×ˢ (univ : Set (F 0))) := hq
      exact (shiftFiber_transitionT0 hq').symm
  · rw [overlap0T] at hx
    have e : (chart0.transition chartTame x).2 = x.2 := congrArg Prod.snd (transition0T hx)
    exact Set.mem_of_eq_of_mem e h
  · rw [overlapT0] at hx
    have e : (chartTame.transition chart0 x).2 = x.2 := congrArg Prod.snd (transitionT0 hx)
    exact Set.mem_of_eq_of_mem e h

/-- The tame chart is a strong bundle chart of `bundle`. -/
theorem isChart_chartTame : bundle.IsChart chartTame := fun c hc => by
  rw [mem_singleton_iff.1 hc]
  exact compatible_chart0_chartTame.symm

/-- **The tame chart is a tame strong bundle chart** (its base retraction is the identity of
`{t < 1} ⊆ ℝ¹`). -/
theorem isTameChart_chartTame : bundle.IsTameChart chartTame :=
  StrongBundle.isTameChart_of_eqOn_id isChart_chartTame fun _ _ => rfl

/-- **`K → O` is a tame strong bundle**: every point of `O` lies in a strong bundle chart of the
structure whose base retraction is tame (2021 p. 66), namely the one chart `chartTame`. -/
theorem exists_isTameChart (x : Ob) :
    ∃ c : StrongBundleChart polyO kproj, bundle.IsTameChart c ∧ x ∈ c.φ.source :=
  ⟨chartTame, isTameChart_chartTame, mem_univ x⟩

end UntamedCorner

end Polyfold
