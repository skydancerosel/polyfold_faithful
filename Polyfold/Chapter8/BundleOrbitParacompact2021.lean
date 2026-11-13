import Polyfold.Chapter8.Book2021
import Polyfold.Chapter8.TangentZhou
import Polyfold.Chapter7.NaturalAction
import Polyfold.Chapter7.OrbitTopology

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 8,
§8.4, **Proposition 8.4.1** (p. 380, new in the 2021 edition), (1) ⇔ (2).

# `|X|` is paracompact iff `|W[0]|` is

## The text, paraphrased

(Proposition 8.4.1) For a strong bundle `(P : W → X, μ)` over an ep-groupoid, `|X|`, `|W[0]|`
and `|W[1]|` are paracompact together.  The proof of (1) ⇒ (2), (3) follows Theorem 8.1.15:
over a neighbourhood `U(x)` with the natural `G_x`-action, `G_x` acts on `W[i]|U(x)`; averaging
metrics shows that the orbit space of `W[i]|U(x)` is metrizable, and a locally finite closed cover
of `|X|` subordinate to the `|U(x)|` gives a locally finite closed cover of `|W[i]|` by
paracompact sets (Proposition 2.7.4).

## What is formalized

* `EpStrongBundle.bundleU R`, `W|U(x) = P⁻¹(U(x))`, with the action `g ∗ w = μ(Γ(g, P w), w)` of
  `G_x` (`bundleMulAction`, the text's lift on p. 382, Chapter 8's `natLift`) by homeomorphisms.
* `EpStrongBundle.π_eq_π_iff_exists_smul`: two points of `W|U(x)` have the same orbit in `|W|`
  iff they are `G_x`-related, so `G_x\(W|U(x)) → |W|` is an open embedding onto
  `|W|U(x)| = |P|⁻¹(|U(x)|)`, and `|P|⁻¹(|U(x)|)` is metrizable.
* `EpStrongBundle.metrizableSpace_orbitSpace`: if `|X|` is paracompact, `|W[0]|` is metrizable.
* **`EpStrongBundle.proposition_8_4_1_one_imp_two`** ((1) ⇒ (2)) and
  **`EpStrongBundle.proposition_8_4_1_one_iff_two`** ((1) ⇔ (2), with `Book2021.lean`'s
  `proposition_8_4_1_two_imp_one`).  No hypothesis beyond the text's.

## The proof, and how it relates to the text's

As for `TX` in `TangentOrbit.lean`: `|X|` is metrizable (Theorem 7.3.1), and Smirnov's theorem
pulled back along `|P| : |W| → |X|` (`metrizableSpace_of_pullback`) applies, since
`|P|⁻¹(|U(x)|) ≅ G_x\(W|U(x))` is metrizable (`W` is metrizable as an M-polyfold, and the
quotient of a metrizable space by a finite group of homeomorphisms is metrizable by the metric
`ρ̂` of Lemma 7.3.2).  This replaces the text's closed cover and Proposition 2.7.4 by the
partition-of-unity form of Smirnov's theorem; no bundle charts are needed, only the continuity of
`μ`.  `W[1]` is not built as an ep-groupoid in the project; (3), with `|W[1]|` the orbit space
of the groupoid `(W[1], 𝐗 ₛ×_P W[1])`, is `GapP2_CProp841W1.lean` (`proposition_8_4_1`, the
three conditions equivalent; gap G.86 closed, 2026-11-12).
-/

open Set Function Topology TopologicalSpace Filter

noncomputable section

namespace Polyfold

universe u

/-! ### The text's metrics `ρ` and `ρ̂` (Lemma 7.3.2), for a finite group

Repeated from `TangentOrbit.lean`, `OrbitTopology.lean` and `Lift.lean`, where they are private.
-/

section QuotientMetric

variable (G : Type*) {U : Type*} [Group G] [Fintype G] [MulAction G U] [PseudoMetricSpace U]

/-- `ρ(y, z) = max_g d(g y, g z)` (Lemma 7.3.2 (2017: 7.4)). -/
private def bqMaxDist (y z : U) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun g : G => dist (g • y) (g • z)

variable {G}

private theorem dist_smul_le_bqMaxDist (g : G) (y z : U) :
    dist (g • y) (g • z) ≤ bqMaxDist G y z :=
  Finset.le_sup' (fun g : G => dist (g • y) (g • z)) (Finset.mem_univ g)

private theorem dist_le_bqMaxDist (y z : U) : dist y z ≤ bqMaxDist G y z := by
  simpa only [one_smul] using dist_smul_le_bqMaxDist (1 : G) y z

private theorem bqMaxDist_lt_iff {y z : U} {ε : ℝ} :
    bqMaxDist G y z < ε ↔ ∀ g : G, dist (g • y) (g • z) < ε := by
  simp only [bqMaxDist, Finset.sup'_lt_iff, Finset.mem_univ, forall_const]

private theorem bqMaxDist_self (y : U) : bqMaxDist G y y = 0 :=
  le_antisymm (Finset.sup'_le _ _ fun _ _ => (dist_self _).le)
    (dist_nonneg.trans (dist_le_bqMaxDist y y))

private theorem bqMaxDist_comm (y z : U) : bqMaxDist G y z = bqMaxDist G z y := by
  simp only [bqMaxDist, dist_comm]

private theorem bqMaxDist_triangle (y z w : U) :
    bqMaxDist G y w ≤ bqMaxDist G y z + bqMaxDist G z w :=
  Finset.sup'_le _ _ fun g _ => (dist_triangle _ (g • z) _).trans
    (add_le_add (dist_smul_le_bqMaxDist g y z) (dist_smul_le_bqMaxDist g z w))

/-- **`ρ` is invariant** (Lemma 7.3.2 (2017: 7.4)): `ρ(h y, h z) = ρ(y, z)`. -/
private theorem bqMaxDist_smul (h : G) (y z : U) :
    bqMaxDist G (h • y) (h • z) = bqMaxDist G y z := by
  refine le_antisymm (Finset.sup'_le _ _ fun g _ => ?_) (Finset.sup'_le _ _ fun g _ => ?_)
  · rw [smul_smul, smul_smul]
    exact dist_smul_le_bqMaxDist (g * h) y z
  · have := dist_smul_le_bqMaxDist (g * h⁻¹) (h • y) (h • z)
    rwa [smul_smul, smul_smul, inv_mul_cancel_right] at this

variable (G) in
/-- `min_h ρ(y, h z)`, the quotient distance before passing to the quotient. -/
private def bqQuotDistAux (y z : U) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun h : G => bqMaxDist G y (h • z)

private theorem bqQuotDistAux_le (h : G) (y z : U) : bqQuotDistAux G y z ≤ bqMaxDist G y (h • z) :=
  Finset.inf'_le (fun h : G => bqMaxDist G y (h • z)) (Finset.mem_univ h)

private theorem exists_bqQuotDistAux_eq (y z : U) :
    ∃ h : G, bqQuotDistAux G y z = bqMaxDist G y (h • z) := by
  obtain ⟨h, -, hh⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := G))
    fun h : G => bqMaxDist G y (h • z)
  exact ⟨h, hh⟩

private theorem bqQuotDistAux_smul_right (k : G) (y z : U) :
    bqQuotDistAux G y (k • z) = bqQuotDistAux G y z := by
  refine le_antisymm (Finset.le_inf' _ _ fun h _ => ?_) (Finset.le_inf' _ _ fun h _ => ?_)
  · have := bqQuotDistAux_le (h * k⁻¹) y (k • z)
    rwa [smul_smul, inv_mul_cancel_right] at this
  · rw [smul_smul]
    exact bqQuotDistAux_le (h * k) y z

private theorem bqQuotDistAux_smul_left (k : G) (y z : U) :
    bqQuotDistAux G (k • y) z = bqQuotDistAux G y z := by
  refine le_antisymm (Finset.le_inf' _ _ fun h _ => ?_) (Finset.le_inf' _ _ fun h _ => ?_)
  · rw [← bqMaxDist_smul k, smul_smul]
    exact bqQuotDistAux_le (k * h) (k • y) z
  · have := bqQuotDistAux_le (k⁻¹ * h) y z
    rwa [← bqMaxDist_smul k, smul_smul, mul_inv_cancel_left] at this

private theorem bqQuotDistAux_comm_le (y z : U) : bqQuotDistAux G y z ≤ bqQuotDistAux G z y := by
  refine Finset.le_inf' _ _ fun h _ => ?_
  have := bqQuotDistAux_le h⁻¹ y z
  rwa [← bqMaxDist_smul h, smul_inv_smul, bqMaxDist_comm] at this

private theorem bqQuotDistAux_comm (y z : U) : bqQuotDistAux G y z = bqQuotDistAux G z y :=
  le_antisymm (bqQuotDistAux_comm_le y z) (bqQuotDistAux_comm_le z y)

private theorem bqQuotDistAux_triangle (y z w : U) :
    bqQuotDistAux G y w ≤ bqQuotDistAux G y z + bqQuotDistAux G z w := by
  obtain ⟨h, hh⟩ := exists_bqQuotDistAux_eq (G := G) y z
  obtain ⟨k, hk⟩ := exists_bqQuotDistAux_eq (G := G) z w
  rw [hh, hk, ← bqMaxDist_smul h z, smul_smul]
  exact (bqQuotDistAux_le (h * k) y w).trans (bqMaxDist_triangle _ _ _)

variable (G U) in
/-- **The quotient distance** `ρ̂([y], [z]) = min_{g, h} ρ(g y, h z) = min_h ρ(y, h z)` on `G\U`
(Lemma 7.3.2 (2017: 7.4)). -/
private def bqQuotDist :
    MulAction.orbitRel.Quotient G U → MulAction.orbitRel.Quotient G U → ℝ :=
  Quotient.lift₂ (bqQuotDistAux G) <| by
    rintro a₁ b₁ a₂ b₂ ⟨g, rfl⟩ ⟨h, rfl⟩
    exact (bqQuotDistAux_smul_left g _ _).trans (bqQuotDistAux_smul_right h _ _)

private theorem bqQuotDist_mk (y z : U) :
    bqQuotDist G U (Quotient.mk _ y) (Quotient.mk _ z) = bqQuotDistAux G y z := rfl

end QuotientMetric

/-- **The quotient of a metrizable space by a finite group of homeomorphisms is metrizable**, by
the text's metric `ρ̂` (the argument of Lemma 7.3.2 (2017: 7.4)). -/
theorem metrizableSpace_orbitRel_quotient_finite {G U : Type*} [Group G] [Finite G]
    [MulAction G U] [TopologicalSpace U] [MetrizableSpace U]
    (hc : ∀ g : G, Continuous fun y : U => g • y) :
    MetrizableSpace (MulAction.orbitRel.Quotient G U) := by
  let _ := Fintype.ofFinite G
  let _ := metrizableSpaceMetric U
  have hmk : ∀ q : MulAction.orbitRel.Quotient G U, ∃ y : U, Quotient.mk _ y = q :=
    Quotient.exists_rep
  -- `ρ̂` defines the quotient topology.
  have hH : ∀ s : Set (MulAction.orbitRel.Quotient G U), IsOpen s ↔
      ∀ q ∈ s, ∃ ε > 0, ∀ q', bqQuotDist G U q q' < ε → q' ∈ s := by
    intro s
    rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
    constructor
    · intro hs q hq
      obtain ⟨y, rfl⟩ := hmk q
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hs y hq
      refine ⟨ε, hε, fun q' hq' => ?_⟩
      obtain ⟨z, rfl⟩ := hmk q'
      obtain ⟨h, hh⟩ := exists_bqQuotDistAux_eq (G := G) y z
      rw [bqQuotDist_mk, hh] at hq'
      have hmem : h • z ∈ Quotient.mk (MulAction.orbitRel G U) ⁻¹' s :=
        hball (lt_of_le_of_lt (by rw [dist_comm]; exact dist_le_bqMaxDist _ _) hq')
      have hq : Quotient.mk (MulAction.orbitRel G U) (h • z) = Quotient.mk _ z :=
        Quotient.sound ⟨h, rfl⟩
      rwa [mem_preimage, hq] at hmem
    · intro hs
      refine isOpen_iff_mem_nhds.2 fun y hy => ?_
      obtain ⟨ε, hε, hball⟩ := hs _ hy
      have hN : (⋂ g : G, (fun z => g • z) ⁻¹' Metric.ball (g • y) ε) ∈ 𝓝 y :=
        (isOpen_iInter_of_finite fun g => Metric.isOpen_ball.preimage (hc g)).mem_nhds
          (mem_iInter.2 fun g => Metric.mem_ball_self hε)
      refine mem_of_superset hN fun z hz => hball _ ?_
      have hz' : bqMaxDist G y z < ε := bqMaxDist_lt_iff.2 fun g => by
        rw [dist_comm]
        exact mem_iInter.1 hz g
      have := bqQuotDistAux_le (1 : G) y z
      rw [one_smul] at this
      exact lt_of_le_of_lt this hz'
  let _ : MetricSpace (MulAction.orbitRel.Quotient G U) :=
    MetricSpace.ofDistTopology (bqQuotDist G U) (fun q => ?_) (fun q q' => ?_)
      (fun q q' q'' => ?_) hH fun q q' hqq' => ?_
  · infer_instance
  · obtain ⟨y, rfl⟩ := hmk q
    refine le_antisymm ?_ ?_
    · have := bqQuotDistAux_le (1 : G) y y
      rwa [one_smul, bqMaxDist_self] at this
    · obtain ⟨h, hh⟩ := exists_bqQuotDistAux_eq (G := G) y y
      rw [bqQuotDist_mk, hh]
      exact dist_nonneg.trans (dist_le_bqMaxDist _ _)
  · obtain ⟨y, rfl⟩ := hmk q
    obtain ⟨z, rfl⟩ := hmk q'
    exact bqQuotDistAux_comm y z
  · obtain ⟨y, rfl⟩ := hmk q
    obtain ⟨z, rfl⟩ := hmk q'
    obtain ⟨w, rfl⟩ := hmk q''
    exact bqQuotDistAux_triangle y z w
  · obtain ⟨y, rfl⟩ := hmk q
    obtain ⟨z, rfl⟩ := hmk q'
    obtain ⟨h, hh⟩ := exists_bqQuotDistAux_eq (G := G) y z
    rw [bqQuotDist_mk, hh] at hqq'
    have h0 : dist y (h • z) = 0 :=
      le_antisymm (hqq' ▸ dist_le_bqMaxDist _ _) dist_nonneg
    rw [dist_eq_zero] at h0
    rw [h0]
    exact Quotient.sound ⟨h, rfl⟩

/-! ### The lifted action of `G_x` on `W|U(x)` -/

section Prop841

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B)

namespace EpStrongBundle

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- `μ(φ, w)` depends only on `φ` (for fixed `w`), not on the proof of `P w = s φ`. -/
theorem μ_congr_fst {φ φ' : Mor} {w : W} (h : P w = X.src φ) (hφ : φ = φ') :
    E.μ ⟨(φ, w), h⟩ = E.μ ⟨(φ', w), h.trans (congrArg X.src hφ)⟩ := by
  subst hφ; rfl

/-- **`|P|⁻¹(|U|) = |W|U|`**: the preimage of `π(U)` under `|P| : |W| → |X|` is
`π_W(P⁻¹(U))` (a `w` with `P(w) ≅ y ∈ U` is isomorphic to `μ(φ, w) ∈ W_y`). -/
theorem preimage_orbitMap_projFunctor_image (U : Set Obj) :
    E.projFunctor.orbitMap ⁻¹' (X.π '' U) = E.toEpGroupoid.π '' (P ⁻¹' U) := by
  ext c
  induction c using Quotient.inductionOn with | h w => ?_
  constructor
  · rintro ⟨y, hy, hyw⟩
    have hyw' : X.π (P w) = X.π y := hyw.symm
    obtain ⟨w', hww', hw'⟩ := E.exists_isomorphic_of_isomorphic ((X.π_eq_π_iff).1 hyw')
    exact ⟨w', by rw [mem_preimage, hw']; exact hy, ((E.toEpGroupoid.π_eq_π_iff).2 hww').symm⟩
  · rintro ⟨w', hw', hw'w⟩
    exact ⟨P w', hw', by rw [← hw'w]; rfl⟩

variable {x : Obj} (R : X.NaturalRep x)

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- `P(g ∗ w) = g ∗ P(w)`: the lift covers the natural action. -/
theorem P_natLift (g : X.Isotropy x) (w : W) (hw : P w ∈ R.U) :
    P (E.natLift R g w hw) = R.Φ g (P w) :=
  (E.P_μ _).trans (R.tgt_Γ g (P w) hw)

omit [ParacompactSpace (pullbackSpace P X.src)] in
theorem natLift_mem (g : X.Isotropy x) (w : W) (hw : P w ∈ R.U) :
    P (E.natLift R g w hw) ∈ R.U := by
  rw [E.P_natLift]
  exact R.mapsTo_Φ g hw

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- `1 ∗ w = w` (`Γ(1, y) = 1_y` and `μ(1_y, w) = w`). -/
theorem natLift_one (w : W) (hw : P w ∈ R.U) : E.natLift R 1 w hw = w :=
  (E.μ_congr_fst (R.src_Γ 1 (P w) hw).symm (R.Γ_one hw)).trans (E.μ_unit w)

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- `(g h) ∗ w = g ∗ (h ∗ w)` (`Γ(g h, y) = Γ(g, h ∗ y) ∘ Γ(h, y)` and the composition law of
`μ`). -/
theorem natLift_mul (g h : X.Isotropy x) (w : W) (hw : P w ∈ R.U) :
    E.natLift R (g * h) w hw = E.natLift R g (E.natLift R h w hw) (E.natLift_mem R h w hw) := by
  have h₂ : X.src (R.Γ g (R.Φ h (P w))) = X.tgt (R.Γ h (P w)) := by
    rw [R.src_Γ g _ (R.mapsTo_Φ h hw), R.tgt_Γ h _ hw]
  refine (E.μ_congr_fst (R.src_Γ (g * h) (P w) hw).symm (R.Γ_mul g h hw).symm).trans
    ((E.μ_comp _ _ w (R.src_Γ h (P w) hw).symm h₂).trans ?_)
  exact E.μ_congr_fst _ (congrArg (R.Γ g) (E.P_natLift R h w hw).symm)

/-- **`W|U(x) = P⁻¹(U(x))`**, the restriction of the bundle to `U(x)`. -/
def bundleU : Set W := E.projFunctor.obj ⁻¹' R.U

theorem isOpen_bundleU : IsOpen (E.bundleU R) := R.isOpen_U.preimage B.continuous

/-- **The lift of the natural action to `W|U(x)`** (2021 p. 382),
`g ∗ w = μ(Γ(g, P(w)), w)`. -/
instance bundleMulAction : MulAction (X.Isotropy x) (E.bundleU R) where
  smul g w := ⟨E.natLift R g w.1 w.2, E.natLift_mem R g w.1 w.2⟩
  one_smul w := Subtype.ext (E.natLift_one R w.1 w.2)
  mul_smul g h w := Subtype.ext (E.natLift_mul R g h w.1 w.2)

@[simp]
theorem bundleSmul_val (g : X.Isotropy x) (w : E.bundleU R) :
    (g • w : E.bundleU R).1 = E.natLift R g w.1 w.2 := rfl

/-- `G_x` acts on `W|U(x)` by homeomorphisms (`μ`, `Γ(g, ·)` and `P` are continuous). -/
theorem continuous_bundleSmul (g : X.Isotropy x) :
    Continuous fun w : E.bundleU R => g • w := by
  refine continuous_induced_rng.2 (E.continuous_μ.comp (continuous_induced_rng.2 ?_))
  exact ((R.continuousOn_Γ g).comp_continuous (B.continuous.comp continuous_subtype_val)
    fun w => w.2).prodMk continuous_subtype_val

/-- **`|v| = |w|` in `|W|` for `v, w ∈ W|U(x)` iff `w = g ∗ v`**: a morphism `(φ, v) : v → w`
of `W` lies over `φ : P(v) → P(w)` between points of `U(x)`, so `φ = Γ(g, P v)` for a unique
`g` (Theorem 7.1.13 (3)) and `w = μ(φ, v) = g ∗ v`. -/
theorem π_eq_π_iff_exists_smul {v w : E.bundleU R} :
    E.toEpGroupoid.π v.1 = E.toEpGroupoid.π w.1 ↔ ∃ g : X.Isotropy x, g • v = w := by
  constructor
  · intro h
    obtain ⟨q, hqs, hqt⟩ := (E.toEpGroupoid.π_eq_π_iff).1 h
    have hqs' : (q : Mor × W).2 = v.1 := hqs
    have hqt' : E.μ q = w.1 := hqt
    have hs : X.src (q : Mor × W).1 = P v.1 := q.2.symm.trans (congrArg P hqs')
    have ht : X.tgt (q : Mor × W).1 = P w.1 := (E.P_μ q).symm.trans (congrArg P hqt')
    have hv : P v.1 ∈ R.U := v.2
    have hw : P w.1 ∈ R.U := w.2
    obtain ⟨g, hg, -⟩ := R.existsUnique_Γ (q : Mor × W).1 (hs ▸ hv) (ht ▸ hw)
    refine ⟨g, Subtype.ext ?_⟩
    rw [bundleSmul_val, ← hqt']
    obtain ⟨⟨φ, w'⟩, hq⟩ := q
    change w' = v.1 at hqs'
    change X.src φ = P v.1 at hs
    change R.Γ g (X.src φ) = φ at hg
    subst hqs'
    exact E.μ_congr_fst _ (by rw [← hs]; exact hg)
  · rintro ⟨g, rfl⟩
    exact (E.toEpGroupoid.π_eq_π_iff).2
      ⟨⟨(R.Γ g (P v.1), v.1), (R.src_Γ g (P v.1) v.2).symm⟩, rfl, rfl⟩

private theorem bundleOrbitRel_iff (v w : E.bundleU R) :
    MulAction.orbitRel (X.Isotropy x) (E.bundleU R) v w ↔
      E.toEpGroupoid.π v.1 = E.toEpGroupoid.π w.1 := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, eq_comm, E.π_eq_π_iff_exists_smul]

/-- `G_x\(W|U(x)) → |W|`, `G_x ∗ w ↦ |w|`. -/
def bundleOrbitQuotientMap :
    MulAction.orbitRel.Quotient (X.Isotropy x) (E.bundleU R) → E.toEpGroupoid.OrbitSpace :=
  Quotient.lift (fun v : E.bundleU R => E.toEpGroupoid.π v.1) fun v w h =>
    (E.bundleOrbitRel_iff R v w).1 h

/-- **`G_x\(W|U(x)) → |W|` is an open embedding** (the argument of Proposition 7.1.19, with the
lifted action on `W|U(x)`). -/
theorem isOpenEmbedding_bundleOrbitQuotientMap : IsOpenEmbedding (E.bundleOrbitQuotientMap R) := by
  refine .of_continuous_injective_isOpenMap
    ((E.toEpGroupoid.continuous_π.comp continuous_subtype_val).quotient_lift _)
    (fun q q' h => ?_) fun S hS => ?_
  · induction q using Quotient.inductionOn with | h v => ?_
    induction q' using Quotient.inductionOn with | h w => ?_
    exact Quotient.sound ((E.bundleOrbitRel_iff R v w).2 h)
  · have himage : E.bundleOrbitQuotientMap R '' S =
        E.toEpGroupoid.π '' (Subtype.val '' (Quotient.mk _ ⁻¹' S)) := by
      ext c
      constructor
      · rintro ⟨q, hq, rfl⟩
        induction q using Quotient.inductionOn with | h v => ?_
        exact ⟨v, ⟨v, hq, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨Quotient.mk _ v, hv, rfl⟩
    rw [himage]
    exact E.toEpGroupoid.proposition_7_1_8 _ ((E.isOpen_bundleU R).isOpenMap_subtype_val _
      (hS.preimage continuous_quotient_mk'))

/-- The range of `G_x\(W|U(x)) → |W|` is `|P|⁻¹(|U(x)|)`. -/
theorem range_bundleOrbitQuotientMap :
    range (E.bundleOrbitQuotientMap R) = E.projFunctor.orbitMap ⁻¹' (X.π '' R.U) := by
  rw [E.preimage_orbitMap_projFunctor_image]
  ext c
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with | h v => ?_
    exact ⟨v.1, v.2, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Quotient.mk _ ⟨v, hv⟩, rfl⟩

/-- **`|P|⁻¹(|U(x)|)` is metrizable** (the text's "the orbit space of `W[0]|U(x)` is
paracompact"): `W|U(x)` is metrizable as an open subset of the M-polyfold `W[0]`, so is its
quotient by the finite group `G_x` acting by homeomorphisms (the metric `ρ̂` of Lemma 7.3.2), and
`G_x\(W|U(x)) → |W|` is an open embedding onto `|P|⁻¹(|U(x)|)`. -/
theorem metrizableSpace_preimage_orbitMap_projFunctor :
    MetrizableSpace (E.projFunctor.orbitMap ⁻¹' (X.π '' R.U)) := by
  have := E.toEpGroupoid.PObj.metrizableSpace
  have := metrizableSpace_orbitRel_quotient_finite (E.continuous_bundleSmul R)
  exact ((E.isOpenEmbedding_bundleOrbitQuotientMap R).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (E.range_bundleOrbitQuotientMap R))).symm.isEmbedding.metrizableSpace

/-! ### Proposition 8.4.1, (1) ⇒ (2) -/

/-- **`|W[0]|` is metrizable if `|X|` is paracompact**: `|X|` is metrizable (Theorem 7.3.1),
hence paracompact and Hausdorff, and Smirnov's theorem pulled back along `|P| : |W| → |X|`
(`metrizableSpace_of_pullback`) applies, the preimages `|P|⁻¹(|U(x)|)` being metrizable. -/
theorem metrizableSpace_orbitSpace (h : X.HasParacompactOrbitSpace) :
    MetrizableSpace E.toEpGroupoid.OrbitSpace := by
  have := X.theorem_7_3_1_metrizable h
  have : ParacompactSpace X.OrbitSpace := h
  refine metrizableSpace_of_pullback E.projFunctor.orbitMap E.continuous_orbitMap_projFunctor
    fun z => ?_
  obtain ⟨y, rfl⟩ := X.surjective_π z
  obtain ⟨R, -⟩ := X.theorem_7_1_13 y isOpen_univ (mem_univ _)
  exact ⟨X.π '' R.U, X.proposition_7_1_8 _ R.isOpen_U, mem_image_of_mem _ R.mem_U,
    E.metrizableSpace_preimage_orbitMap_projFunctor R⟩

/-- **2021 Proposition 8.4.1, (1) ⇒ (2)**, p. 380 (new in the 2021 edition): if `|X|` is
paracompact, so is the orbit space `|W[0]|` of the ep-groupoid `(W, 𝐖)`.  Proved via
metrizability (`metrizableSpace_orbitSpace`) instead of the text's closed cover. -/
theorem proposition_8_4_1_one_imp_two (h : X.HasParacompactOrbitSpace) :
    E.toEpGroupoid.HasParacompactOrbitSpace :=
  have := E.metrizableSpace_orbitSpace h
  paracompactSpace_of_metrizableSpace _

/-- **2021 Proposition 8.4.1, (1) ⇔ (2)**, p. 380: `|X|` is paracompact iff `|W[0]|` is. -/
theorem proposition_8_4_1_one_iff_two :
    X.HasParacompactOrbitSpace ↔ E.toEpGroupoid.HasParacompactOrbitSpace :=
  ⟨E.proposition_8_4_1_one_imp_two, E.proposition_8_4_1_two_imp_one⟩

end EpStrongBundle

end Prop841

end Polyfold
