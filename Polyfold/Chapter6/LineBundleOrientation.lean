import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.LinearAlgebra.Ray

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5, p. 219:
the topological fact behind **Proposition 6.6.1 (preprint 6.26)** ("consequently has two possible orientations since
the base space is contractible") *(book 2017: Proposition 6.11; see `BookConcordance.md`)*.

# Orientations of line bundles

## The text, paraphrased

A topological line bundle over a contractible base has exactly two orientations: the orientation of
one fibre determines a natural orientation of all the other fibres.

## What is formalized

For a topological vector bundle `L → B` with model fibre `ℝ` (Mathlib's `FiberBundle ℝ L` and
`VectorBundle ℝ ℝ L`):

* `Polyfold.IsLineOrientation o`: a choice `o b` of a ray of every fibre `L b` is an orientation if
  near every point it is given by a continuous section that vanishes nowhere;
  `Polyfold.LineOrientation L`, the orientations.
* `LineOrientation.eq_of_apply_eq`: over a preconnected base, two orientations that agree on one
  fibre agree everywhere.
* `exists_lineOrientation_apply_eq`: over a simply connected, locally path-connected base, every
  orientation of one fibre extends to an orientation of the bundle.
* `exists_two_lineOrientation`: over a nonempty simply connected, locally path-connected base there
  are exactly two orientations.  A nonempty convex subset of a locally convex real space is such a
  base (`Convex.contractibleSpace`, `SimplyConnectedSpace.ofContractible`,
  `Convex.locallyPathConnectedSpace`).

## Reading

The text cites contractibility without the theorem it needs (that a line bundle over a contractible
base is orientable).  The proof here is the standard one: the rays of the fibres form a two-sheeted
covering of `B` (the orientation double cover, `Polyfold.OrCover`, a fibre bundle with discrete
fibre `Bool` built from the linear trivializations of `L`), an orientation is a continuous section
of it, and Mathlib's lifting criterion (`IsCoveringMap.existsUnique_continuousMap_lifts`)
applies to the identity of a simply connected, locally path-connected base.  "Contractible" is
replaced by these two hypotheses, which a contractible locally path-connected space has.
-/

open Bundle Topology Set

noncomputable section

namespace Polyfold

variable {B : Type*} [TopologicalSpace B] {L : B → Type*} [∀ b, AddCommMonoid (L b)]
  [∀ b, Module ℝ (L b)] [TopologicalSpace (TotalSpace ℝ L)]

variable (L) in
/-- **An orientation of a line bundle**: a choice of ray `o b` of every fibre `L b` such that near
every point `b₀` there is a continuous section `σ`, vanishing nowhere, with `o b` the ray of
`σ b`. -/
def IsLineOrientation (o : ∀ b, Module.Ray ℝ (L b)) : Prop :=
  ∀ b₀ : B, ∃ U ∈ 𝓝 b₀, ∃ σ : ∀ b, L b,
    ContinuousOn (fun b => TotalSpace.mk' ℝ b (σ b)) U ∧
      ∀ b ∈ U, ∃ h : σ b ≠ 0, o b = rayOfNeZero ℝ (σ b) h

variable (L) in
/-- The orientations of the line bundle `L`. -/
def LineOrientation : Type _ := {o : ∀ b, Module.Ray ℝ (L b) // IsLineOrientation L o}

/-! ### Rays of a fibre read in a linear trivialization -/

section Rays

/-- Two nonzero reals lie on the same ray iff their product is positive. -/
theorem sameRay_real_iff {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : SameRay ℝ x y ↔ 0 < x * y := by
  have hy' : (y / x) • x = y := by rw [smul_eq_mul, div_mul_cancel₀ _ hx]
  have := sameRay_smul_right_iff_of_ne (R := ℝ) hx (div_ne_zero hy hx)
  rw [hy'] at this
  rw [this, div_pos_iff, mul_pos_iff]
  tauto

/-- For nonzero reals, `0 < x y` iff `x` and `y` have the same sign. -/
theorem mul_pos_iff_of_ne {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    0 < x * y ↔ (0 < x ↔ 0 < y) := by
  rcases hx.lt_or_gt with hx | hx <;> rcases hy.lt_or_gt with hy | hy
  · exact iff_of_true (mul_pos_of_neg_of_neg hx hy) (iff_of_false hx.not_gt hy.not_gt)
  · exact iff_of_false (mul_neg_of_neg_of_pos hx hy).not_gt fun h => hx.not_gt (h.2 hy)
  · exact iff_of_false (mul_neg_of_pos_of_neg hx hy).not_gt fun h => hy.not_gt (h.1 hx)
  · exact iff_of_true (mul_pos hx hy) (iff_of_true hx hy)

/-- A real function tending to `a ≠ 0` eventually has the sign of `a`. -/
theorem eventually_pos_iff_of_tendsto {α : Type*} {l : Filter α} {g : α → ℝ} {a : ℝ}
    (hg : Filter.Tendsto g l (𝓝 a)) (ha : a ≠ 0) : ∀ᶠ x in l, (0 < g x ↔ 0 < a) := by
  rcases ha.lt_or_gt with ha | ha
  · filter_upwards [hg.eventually (gt_mem_nhds ha)] with x hx
    exact iff_of_false (not_lt.2 hx.le) (not_lt.2 ha.le)
  · filter_upwards [hg.eventually (lt_mem_nhds ha)] with x hx
    exact iff_of_true hx ha

/-- The sign of a continuous real function that vanishes nowhere on `s` is continuous on `s`. -/
theorem continuousOn_decide_pos {X : Type*} [TopologicalSpace X] {g : X → ℝ} {s : Set X}
    (hg : ContinuousOn g s) (h0 : ∀ x ∈ s, g x ≠ 0) :
    ContinuousOn (fun x => decide (0 < g x)) s := by
  intro x hx
  refine continuousWithinAt_const.congr_of_eventuallyEq
    ((eventually_pos_iff_of_tendsto (hg x hx) (h0 x hx)).mono fun y hy => ?_) rfl
  exact decide_eq_decide.2 hy

/-- The ray `r` of `L b` is positive for the trivialization `e`: it is the ray of a vector with
positive `e`-coordinate. -/
def PosRay (e : Trivialization ℝ (π ℝ L)) (b : B) (r : Module.Ray ℝ (L b)) : Prop :=
  ∃ (v : L b) (hv : v ≠ 0), r = rayOfNeZero ℝ v hv ∧ 0 < (e ⟨b, v⟩).2

variable (e : Trivialization ℝ (π ℝ L)) [e.IsLinear ℝ]

/-- Over the base set, a linear trivialization sends nonzero vectors to nonzero coordinates. -/
theorem coord_ne_zero {b : B} (hb : b ∈ e.baseSet) {v : L b} (hv : v ≠ 0) :
    (e ⟨b, v⟩).2 ≠ 0 :=
  (e.linearEquivAt ℝ b hb).map_ne_zero_iff.2 hv

/-- Two nonzero vectors of a fibre have the same ray iff their coordinates have the same sign. -/
theorem ray_eq_ray_iff {b : B} (hb : b ∈ e.baseSet) {v w : L b} (hv : v ≠ 0) (hw : w ≠ 0) :
    rayOfNeZero ℝ v hv = rayOfNeZero ℝ w hw ↔ 0 < (e ⟨b, v⟩).2 * (e ⟨b, w⟩).2 := by
  rw [ray_eq_iff, ← SameRay.sameRay_map_iff (e.linearEquivAt ℝ b hb)]
  exact sameRay_real_iff (coord_ne_zero e hb hv) (coord_ne_zero e hb hw)

/-- The ray of `v` is positive iff the coordinate of `v` is. -/
theorem posRay_ray_iff {b : B} (hb : b ∈ e.baseSet) {v : L b} (hv : v ≠ 0) :
    PosRay e b (rayOfNeZero ℝ v hv) ↔ 0 < (e ⟨b, v⟩).2 := by
  constructor
  · rintro ⟨w, hw, hvw, hpos⟩
    exact (pos_iff_pos_of_mul_pos ((ray_eq_ray_iff e hb hv hw).1 hvw)).2 hpos
  · exact fun h => ⟨v, hv, rfl, h⟩

/-- A fibre is a line: a ray of it is determined by whether it is positive. -/
theorem eq_iff_posRay_iff {b : B} (hb : b ∈ e.baseSet) (r r' : Module.Ray ℝ (L b)) :
    r = r' ↔ (PosRay e b r ↔ PosRay e b r') := by
  induction r using Module.Ray.ind with | h v hv => ?_
  induction r' using Module.Ray.ind with | h w hw => ?_
  rw [posRay_ray_iff e hb, posRay_ray_iff e hb, ray_eq_ray_iff e hb]
  exact mul_pos_iff_of_ne (coord_ne_zero e hb hv) (coord_ne_zero e hb hw)

/-- Near a point of the base set, whether an orientation is positive for `e` does not change. -/
theorem IsLineOrientation.eventually_posRay_iff {o : ∀ b, Module.Ray ℝ (L b)}
    (ho : IsLineOrientation L o) {b₀ : B} (hb₀ : b₀ ∈ e.baseSet) :
    ∀ᶠ b in 𝓝 b₀, (PosRay e b (o b) ↔ PosRay e b₀ (o b₀)) := by
  obtain ⟨U, hU, σ, hσ, hσo⟩ := ho b₀
  have hg : ContinuousAt (fun b => (e ⟨b, σ b⟩).2) b₀ := by
    have h1 : ContinuousAt (fun b => TotalSpace.mk' ℝ b (σ b)) b₀ := hσ.continuousAt hU
    have h2 := e.continuousOn.continuousAt
      (e.open_source.mem_nhds (e.mem_source (x := TotalSpace.mk' ℝ b₀ (σ b₀)) |>.2 hb₀))
    exact continuous_snd.continuousAt.comp
      (ContinuousAt.comp (f := fun b => TotalSpace.mk' ℝ b (σ b)) h2 h1)
  obtain ⟨hσ₀, ho₀⟩ := hσo b₀ (mem_of_mem_nhds hU)
  filter_upwards [hU, e.open_baseSet.mem_nhds hb₀,
    eventually_pos_iff_of_tendsto hg (coord_ne_zero e hb₀ hσ₀)] with b hbU hb hgb
  obtain ⟨hσb, hob⟩ := hσo b hbU
  rw [hob, ho₀, posRay_ray_iff e hb, posRay_ray_iff e hb₀]
  exact hgb

end Rays

namespace LineOrientation

instance : CoeFun (LineOrientation L) (fun _ => ∀ b, Module.Ray ℝ (L b)) := ⟨Subtype.val⟩

@[ext] theorem ext {o o' : LineOrientation L} (h : ∀ b, o b = o' b) : o = o' :=
  Subtype.ext (funext h)

variable [∀ b, TopologicalSpace (L b)] [FiberBundle ℝ L] [VectorBundle ℝ ℝ L]

/-- Over a preconnected base, two orientations that agree on one fibre are equal. -/
theorem eq_of_apply_eq [PreconnectedSpace B] {o o' : LineOrientation L} (b : B)
    (h : o b = o' b) : o = o' := by
  have hloc : ∀ b₀, ∀ᶠ b in 𝓝 b₀, (o b = o' b ↔ o b₀ = o' b₀) := by
    intro b₀
    have hb₀ := FiberBundle.mem_baseSet_trivializationAt ℝ L b₀
    filter_upwards [o.2.eventually_posRay_iff _ hb₀, o'.2.eventually_posRay_iff _ hb₀,
      (trivializationAt ℝ L b₀).open_baseSet.mem_nhds hb₀] with b h1 h2 hb
    exact (eq_iff_posRay_iff _ hb _ _).trans
      ((iff_congr h1 h2).trans (eq_iff_posRay_iff _ hb₀ _ _).symm)
  have hA : IsClopen {b | o b = o' b} :=
    ⟨isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun b₀ hb₀ =>
        (hloc b₀).mono fun _ hb hb' => hb₀ (hb.1 hb')),
      isOpen_iff_mem_nhds.2 fun b₀ hb₀ => (hloc b₀).mono fun _ hb => hb.2 hb₀⟩
  ext b'
  exact eq_univ_iff_forall.1 (hA.eq_univ ⟨b, h⟩) b'

end LineOrientation

variable [∀ b, TopologicalSpace (L b)] [FiberBundle ℝ L] [VectorBundle ℝ ℝ L]

/-! ### The orientation double cover -/

section OrCover

attribute [local instance] Classical.propDecidable

omit [VectorBundle ℝ ℝ L] in
/-- Every fibre of a line bundle is nontrivial. -/
theorem nontrivial_fiber [VectorBundle ℝ ℝ L] (b : B) : Nontrivial (L b) :=
  ((trivializationAt ℝ L b).linearEquivAt ℝ b
    (FiberBundle.mem_baseSet_trivializationAt ℝ L b)).toEquiv.nontrivial

/-- The sign `±1` named by a Boolean. -/
def signOf : Bool → ℝ
  | true => 1
  | false => -1

/-- `±1 ≠ 0`. -/
theorem signOf_ne_zero (s : Bool) : signOf s ≠ 0 := by cases s <;> norm_num [signOf]

/-- `signOf s` is positive iff `s` is `true`. -/
theorem signOf_pos_iff (s : Bool) : 0 < signOf s ↔ s = true := by
  cases s <;> norm_num [signOf]

/-- The ray of `e.symm b t` (an arbitrary ray when that vector vanishes). -/
def rayAt (e : Trivialization ℝ (π ℝ L)) (b : B) (t : ℝ) : Module.Ray ℝ (L b) :=
  if h : e.symm b t ≠ 0 then rayOfNeZero ℝ _ h else
    haveI := nontrivial_fiber (L := L) b; Classical.arbitrary _

variable (e : Trivialization ℝ (π ℝ L)) [e.IsLinear ℝ]

omit [∀ b, TopologicalSpace (L b)] [FiberBundle ℝ L] [VectorBundle ℝ ℝ L] in
/-- Over the base set, `e.symm b` sends nonzero reals to nonzero vectors. -/
theorem symm_ne_zero {b : B} (hb : b ∈ e.baseSet) {t : ℝ} (ht : t ≠ 0) : e.symm b t ≠ 0 :=
  (e.linearEquivAt ℝ b hb).symm.map_ne_zero_iff.2 ht

/-- Over the base set, `rayAt e b t` is the ray of `e.symm b t` for `t ≠ 0`. -/
theorem rayAt_eq {b : B} (hb : b ∈ e.baseSet) {t : ℝ} (ht : t ≠ 0) :
    rayAt e b t = rayOfNeZero ℝ (e.symm b t) (symm_ne_zero e hb ht) :=
  dif_pos _

/-- `rayAt e b t` is positive for `e` iff `t > 0`. -/
theorem posRay_rayAt_iff {b : B} (hb : b ∈ e.baseSet) {t : ℝ} (ht : t ≠ 0) :
    PosRay e b (rayAt e b t) ↔ 0 < t := by
  rw [rayAt_eq e hb ht, posRay_ray_iff e hb, e.apply_mk_symm hb]

/-- The sign of `rayAt e b (±1)` is the Boolean naming `±1`. -/
theorem decide_posRay_rayAt {b : B} (hb : b ∈ e.baseSet) (s : Bool) :
    decide (PosRay e b (rayAt e b (signOf s))) = s := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, posRay_rayAt_iff e hb (signOf_ne_zero s),
    signOf_pos_iff]

/-- Every ray of `L b` is `rayAt e b (±1)`, the sign being whether it is positive. -/
theorem rayAt_signOf_decide {b : B} (hb : b ∈ e.baseSet) (r : Module.Ray ℝ (L b)) :
    rayAt e b (signOf (decide (PosRay e b r))) = r := by
  rw [eq_iff_posRay_iff e hb, posRay_rayAt_iff e hb (signOf_ne_zero _), signOf_pos_iff,
    decide_eq_true_iff]

variable (L) in
/-- The fibre of the orientation double cover over `b`: the (two) rays of `L b`, discrete. -/
def OrFiber (b : B) : Type _ := Module.Ray ℝ (L b)

instance (b : B) : TopologicalSpace (OrFiber L b) := ⊥

instance (b : B) : DiscreteTopology (OrFiber L b) := ⟨rfl⟩

/-- The trivialization of the orientation double cover over `e.baseSet` given by a linear
trivialization `e` of `L`: a ray goes to its base point and to whether it is positive for `e`. -/
def orPretriv : Pretrivialization Bool (π Bool (OrFiber L)) where
  toFun x := (x.proj, decide (PosRay e x.proj x.2))
  invFun p := ⟨p.1, rayAt e p.1 (signOf p.2)⟩
  source := π Bool (OrFiber L) ⁻¹' e.baseSet
  target := e.baseSet ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' _ hp := hp.1
  left_inv' := by
    rintro ⟨b, r⟩ (hb : b ∈ e.baseSet)
    exact congrArg (TotalSpace.mk b) (rayAt_signOf_decide e hb r)
  right_inv' := by
    rintro ⟨b, s⟩ ⟨hb, -⟩
    exact Prod.ext rfl (decide_posRay_rayAt e hb s)
  open_target := e.open_baseSet.prod isOpen_univ
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- On the fibre over a point of the base set, `orPretriv e` is an embedding of the (discrete)
fibre into `B × Bool`. -/
theorem isInducing_orPretriv_mk {b : B} (hb : b ∈ e.baseSet) :
    IsInducing (orPretriv e ∘ TotalSpace.mk b) := by
  refine ⟨(eq_bot_of_singletons_open (t := TopologicalSpace.induced _ _) fun r => ?_).symm⟩
  refine isOpen_induced_iff.2
    ⟨univ ×ˢ {decide (PosRay e b r)}, isOpen_univ.prod (isOpen_discrete _), ?_⟩
  ext r'
  simp only [mem_preimage, mem_prod, mem_univ, true_and, mem_singleton_iff, Function.comp_apply]
  change decide (PosRay e b r') = decide (PosRay e b r) ↔ r' = r
  exact decide_eq_decide.trans (eq_iff_posRay_iff (r := r') (r' := r) e hb).symm

/-- The transition maps of the orientation double cover are continuous: they are
`(b, s) ↦ (b, sign of the coordinate change applied to ±1)`. -/
theorem continuousOn_orPretriv_trans (e' : Trivialization ℝ (π ℝ L)) [MemTrivializationAtlas e]
    [MemTrivializationAtlas e'] :
    ContinuousOn (orPretriv e ∘ (orPretriv e').toPartialEquiv.symm)
      ((orPretriv e').target ∩ (orPretriv e').toPartialEquiv.symm ⁻¹' (orPretriv e).source) := by
  rw [Pretrivialization.target_inter_preimage_symm_source_eq]
  have hcc : ContinuousOn
      (fun p : B × Bool => Trivialization.coordChangeL ℝ e' e p.1 (signOf p.2))
      ((e.baseSet ∩ e'.baseSet) ×ˢ univ) :=
    ((continuousOn_coordChange ℝ e' e).comp continuousOn_fst
        fun p hp => ⟨hp.1.2, hp.1.1⟩).clm_apply
      ((continuous_of_discreteTopology (f := signOf)).comp continuous_snd).continuousOn
  refine (continuousOn_fst.prodMk (continuousOn_decide_pos hcc ?_)).congr ?_
  · rintro ⟨b, s⟩ ⟨hb, -⟩
    rw [Trivialization.coordChangeL_apply e' e ⟨hb.2, hb.1⟩]
    exact coord_ne_zero e hb.1 (symm_ne_zero e' hb.2 (signOf_ne_zero s))
  · rintro ⟨b, s⟩ ⟨hb, -⟩
    refine Prod.ext rfl (decide_eq_decide.2 ?_)
    change PosRay e b (rayAt e' b (signOf s)) ↔ _
    rw [Trivialization.coordChangeL_apply e' e ⟨hb.2, hb.1⟩,
      rayAt_eq e' hb.2 (signOf_ne_zero s), posRay_ray_iff e hb.1]

variable (L) in
/-- The orientation double cover as a fibre prebundle with discrete fibre `Bool`, one
pretrivialization `orPretriv` for each trivialization `trivializationAt ℝ L b` of `L`. -/
def orPrebundle : FiberPrebundle Bool (OrFiber L) where
  pretrivializationAtlas := range fun b : B => orPretriv (trivializationAt ℝ L b)
  pretrivializationAt b := orPretriv (trivializationAt ℝ L b)
  mem_base_pretrivializationAt b := FiberBundle.mem_baseSet_trivializationAt ℝ L b
  pretrivialization_mem_atlas b := ⟨b, rfl⟩
  continuous_trivChange := by
    rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    exact continuousOn_orPretriv_trans _ _
  totalSpaceMk_isInducing b :=
    isInducing_orPretriv_mk _ (FiberBundle.mem_baseSet_trivializationAt ℝ L b)

variable (L) in
/-- **The orientation double cover** of the line bundle `L`: the rays of all the fibres. -/
abbrev OrCover : Type _ := TotalSpace Bool (OrFiber L)

instance : TopologicalSpace (OrCover L) := (orPrebundle L).totalSpaceTopology

instance : FiberBundle Bool (OrFiber L) := (orPrebundle L).toFiberBundle

/-- The orientation double cover is a covering map. -/
theorem isCoveringMap_orCover : IsCoveringMap (π Bool (OrFiber L)) :=
  IsCoveringMap.mk _ (fun _ => Bool) (fun b => trivializationAt Bool (OrFiber L) b)
    (fun b => FiberBundle.mem_baseSet_trivializationAt Bool (OrFiber L) b)

omit [TopologicalSpace B] [TopologicalSpace (TotalSpace ℝ L)] [∀ b, TopologicalSpace (L b)]
  [FiberBundle ℝ L] [VectorBundle ℝ ℝ L] in
/-- A point of the orientation double cover over `b` is a ray of `L b`. -/
theorem exists_eq_mk_of_proj_eq {x : OrCover L} {b : B} (h : x.proj = b) :
    ∃ r : Module.Ray ℝ (L b), x = ⟨b, r⟩ := by
  subst h; exact ⟨x.2, rfl⟩

/-- Over a simply connected, locally path-connected base, every orientation of one fibre `L b`
extends to an orientation of the bundle. -/
theorem exists_lineOrientation_apply_eq [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
    (b : B) (r : Module.Ray ℝ (L b)) : ∃ o : LineOrientation L, o b = r := by
  obtain ⟨F, ⟨hF0, hFp⟩, -⟩ := (isCoveringMap_orCover (L := L)).existsUnique_continuousMap_lifts
    (ContinuousMap.id B) b (⟨b, r⟩ : OrCover L) rfl
  choose o ho using fun b' => exists_eq_mk_of_proj_eq (L := L) (b := b') (congrFun hFp b')
  refine ⟨⟨o, fun b₀ => ?_⟩, ?_⟩
  · set T := trivializationAt ℝ L b₀
    have hb₀ : b₀ ∈ T.baseSet := FiberBundle.mem_baseSet_trivializationAt ℝ L b₀
    let e₀ := (orPrebundle L).trivializationOfMemPretrivializationAtlas ⟨b₀, rfl⟩
    have hsrc : F b₀ ∈ e₀.source := by
      change (F b₀).proj ∈ T.baseSet
      rw [ho b₀]; exact hb₀
    have hcont : ContinuousAt (fun b => (e₀ (F b)).2) b₀ :=
      continuous_snd.continuousAt.comp ((e₀.continuousOn.continuousAt
        (e₀.open_source.mem_nhds hsrc)).comp F.continuous.continuousAt)
    have hU := hcont.preimage_mem_nhds ((isOpen_discrete {(e₀ (F b₀)).2}).mem_nhds rfl)
    refine ⟨T.baseSet ∩ (fun b => (e₀ (F b)).2) ⁻¹' {(e₀ (F b₀)).2},
      Filter.inter_mem (T.open_baseSet.mem_nhds hb₀) hU,
      fun b => T.symm b (signOf (e₀ (F b₀)).2), ?_, ?_⟩
    · exact (T.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
        fun b hb => ⟨hb, mem_univ _⟩).mono inter_subset_left
    · rintro b ⟨hb, hbs⟩
      refine ⟨symm_ne_zero T hb (signOf_ne_zero _), ?_⟩
      have : decide (PosRay T b (o b)) = (e₀ (F b₀)).2 := by
        rw [← (mem_singleton_iff.1 hbs : (e₀ (F b)).2 = _), ho b]; rfl
      rw [← rayAt_eq T hb (signOf_ne_zero _), ← this, rayAt_signOf_decide T hb]
  · exact (TotalSpace.mk_inj.1 (hF0.symm.trans (ho b))).symm

/-- **A line bundle over a nonempty simply connected, locally path-connected base has exactly two
orientations**: there are two different ones, and every orientation is one of them. -/
theorem exists_two_lineOrientation [Nonempty B] [SimplyConnectedSpace B]
    [LocallyPathConnectedSpace B] :
    ∃ o₁ o₂ : LineOrientation L, o₁ ≠ o₂ ∧ ∀ o : LineOrientation L, o = o₁ ∨ o = o₂ := by
  obtain ⟨b₀⟩ := ‹Nonempty B›
  set T := trivializationAt ℝ L b₀
  have hb₀ : b₀ ∈ T.baseSet := FiberBundle.mem_baseSet_trivializationAt ℝ L b₀
  obtain ⟨o₁, h₁⟩ := exists_lineOrientation_apply_eq b₀ (rayAt T b₀ (signOf true))
  obtain ⟨o₂, h₂⟩ := exists_lineOrientation_apply_eq b₀ (rayAt T b₀ (signOf false))
  refine ⟨o₁, o₂, fun h => ?_, fun o => ?_⟩
  · have h' : rayAt T b₀ (signOf true) = rayAt T b₀ (signOf false) :=
      h₁.symm.trans ((congrArg (fun o : LineOrientation L => o b₀) h).trans h₂)
    have := congrArg (fun r => decide (PosRay T b₀ r)) h'
    simp only [decide_posRay_rayAt T hb₀] at this
    exact Bool.noConfusion this
  · have hr := rayAt_signOf_decide T hb₀ (o b₀)
    cases hd : decide (PosRay T b₀ (o b₀))
    · rw [hd] at hr
      exact Or.inr (LineOrientation.eq_of_apply_eq b₀ (hr.symm.trans h₂.symm))
    · rw [hd] at hr
      exact Or.inl (LineOrientation.eq_of_apply_eq b₀ (hr.symm.trans h₁.symm))

end OrCover

end Polyfold
