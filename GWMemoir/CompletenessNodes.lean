import GWMemoir.CompletenessForms

/-!
# `SectionsClosed` and `ConstraintsClosed` with nodes (Memoir pp. 66–68)

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §3.1, pp. 66–68.

The memoir states that a suitable finite choice of the semi-norms of p. 66 defines a complete norm
on `H^{3,δ₀}_c(S, u*TQ)`, and that `E_u` (p. 68) is closed.  `GWMemoir.CompletenessForms` proves
the two named propositions `SectionsClosed` and `ConstraintsClosed` for surfaces without nodes.
Here they are proved for every continuous `u`, every atlas, nodes included.

* `abs_le_of_ae_eq_half`: the Sobolev bound `|h| ≤ 3 ‖w‖` on a half-cylinder `s > a`, for `h`
  continuous there and `1`-periodic in `t`; `exists_abs_lt_of_ae_eq_half`: such an `h` tends to
  `0` as `s → ∞`, uniformly in `t` (density of the test functions, `dense_test`).
* The polar coordinates: `expPolar` is an open map (`isOpenMap_expPolar`) onto `ℂ \ {0}`
  (`exists_expPolar_eq`), and `σ` is continuous on `s ≥ s₀` because the atlas asks
  `e^{-2π(s+it)} ∈ φ.target` there.  The neck representatives of a continuous section are
  continuous on `s > 0` (`continuousOn_neckRep`) and `1`-periodic in `t` (`neckRep_add_one`).
* **`exists_limit_section_nodal`**: if `v n → w` in the block space and `v n` represents the
  continuous section `η n`, then `η n` converges at every point to a continuous section represented
  by `w`.  On the discs and on the necks the representatives converge uniformly (the Sobolev
  bound); at a nodal point the coordinates of `η n` are the asymptotic constants, which converge
  in `ℝ`.  Continuity of the limit: on a neck it is read through the open map `expPolar`
  (`continuousAt_of_neck`); at the nodal point it is the decay of the neck block as `s → ∞`
  (`continuousAt_node`).
* **`sectionsClosed`**, **`constraintsClosed`**, `sectionSpace_eq_sectionsSub`: the memoir's
  completeness statements, for every continuous map and every atlas.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open Set Filter Topology MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

/-! ## 1. The Sobolev bound on a half-cylinder -/

section HalfCylinder

variable {δ : ℝ} {hδ : 0 ≤ δ}

/-- **The sup bound on a half-cylinder**: if `w ∈ H^{3,δ}` agrees a.e. with `h`, continuous on
`s > a` and `1`-periodic in `t`, then `|h| ≤ 3 ‖w‖` on `s > a`. -/
theorem abs_le_of_ae_eq_half (w : H 3 hδ) {h : ℝ × ℝ → ℝ} {a : ℝ}
    (hh : ContinuousOn h (Ioi a ×ˢ univ)) (hper : ∀ s t, h (s, t + 1) = h (s, t))
    (hw : (H.val w : ℝ × ℝ → ℝ) =ᵐ[cyl] h) {p : ℝ × ℝ} (hp : a < p.1) : |h p| ≤ 3 * ‖w‖ := by
  set U : Set (ℝ × ℝ) := Ioi a ×ˢ Ioo 0 1
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_Ioo
  have hb := abs_le_of_ae_eq_three w hU (prod_mono (subset_univ _) le_rfl)
    (hh.mono (prod_mono le_rfl (subset_univ _))) hw
  have hP : Function.Periodic (fun t => h (p.1, t)) 1 := fun t => hper p.1 t
  have e : h p = h (p.1, Int.fract p.2) := by
    have := hP.sub_int_mul_eq (x := p.2) ⌊p.2⌋
    simp only [mul_one] at this
    rw [Int.fract, this]
  rw [e]
  set q : ℝ × ℝ := (p.1, Int.fract p.2)
  have hq : q ∈ closure U := by
    rw [closure_prod_eq, closure_Ioi, closure_Ioo zero_ne_one]
    exact ⟨le_of_lt hp, Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hne : (𝓝[U] q).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hq
  have hc : ContinuousAt h q :=
    hh.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)
  exact le_of_tendsto ((hc.tendsto.mono_left nhdsWithin_le_nhds).abs)
    (eventually_nhdsWithin_of_forall hb)

/-- **Decay on a half-cylinder**: such an `h` tends to `0` as `s → ∞`, uniformly in `t`. -/
theorem exists_abs_lt_of_ae_eq_half (w : H 3 hδ) {h : ℝ × ℝ → ℝ} {a : ℝ}
    (hh : ContinuousOn h (Ioi a ×ˢ univ)) (hper : ∀ s t, h (s, t + 1) = h (s, t))
    (hw : (H.val w : ℝ × ℝ → ℝ) =ᵐ[cyl] h) {ε : ℝ} (hε : 0 < ε) :
    ∃ R, ∀ p : ℝ × ℝ, R < p.1 → |h p| < ε := by
  obtain ⟨_, hball, φ, hφ, rfl⟩ := Metric.dense_iff.1 (dense_test 3 hδ) w (ε / 4) (by positivity)
  obtain ⟨R, hR⟩ := hφ.bddSupp
  refine ⟨max a R, fun p hp => ?_⟩
  have hpa : a < p.1 := (le_max_left a R).trans_lt hp
  have hpR : R < |p.1| := ((le_max_right a R).trans_lt hp).trans_le (le_abs_self _)
  have hφ0 : φ p = 0 := hR p.1 p.2 hpR
  have hb := abs_le_of_ae_eq_half (w - toH 3 hδ hφ) (h := fun x => h x - φ x) (a := a)
    (hh.sub hφ.smooth.continuous.continuousOn) (fun s t => by simp only [hper, hφ.periodic])
    (by
      filter_upwards [val_sub_ae w (toH 3 hδ hφ), hw,
        (MemLp.coeFn_toLp (hφ.memLp 2) : _ =ᵐ[cyl] φ)] with x h1 h2 h3
      rw [h1, h2]
      exact congrArg (h x - ·) h3)
    hpa
  have hd : ‖w - toH 3 hδ hφ‖ < ε / 4 := by
    rw [← dist_eq_norm, dist_comm]; exact hball
  simp only [hφ0, sub_zero] at hb
  linarith

end HalfCylinder

/-! ## 2. The exponential coordinate -/

section ExpPolar

lemma norm_expPolar (p : ℝ × ℝ) : ‖expPolar p‖ = Real.exp (-2 * Real.pi * p.1) := by
  rw [expPolar, Complex.norm_exp]
  congr 1
  simp

/-- Every `ζ ≠ 0` is `e^{-2π(s+it)}` with `s = -log|ζ| / 2π`. -/
lemma exists_expPolar_eq {ζ : ℂ} (hζ : ζ ≠ 0) :
    ∃ p : ℝ × ℝ, expPolar p = ζ ∧ p.1 = -Real.log ‖ζ‖ / (2 * Real.pi) := by
  refine ⟨(-Real.log ‖ζ‖ / (2 * Real.pi), -Complex.arg ζ / (2 * Real.pi)), ?_, rfl⟩
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have e : -2 * Real.pi * (((-Real.log ‖ζ‖ / (2 * Real.pi) : ℝ) : ℂ) +
      ((-Complex.arg ζ / (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = Complex.log ζ := by
    rw [Complex.log]
    push_cast
    field_simp
    ring
  rw [expPolar]
  simp only
  rw [e, Complex.exp_log hζ]

lemma isOpenMap_expPolar : IsOpenMap expPolar := by
  have hπ : (-2 * Real.pi : ℂ) ≠ 0 := by
    have := Real.pi_ne_zero
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.2 this)
  have e : expPolar = Complex.exp ∘ (fun z => (-2 * Real.pi : ℂ) * z) ∘
      Complex.equivRealProdCLM.symm := by
    funext p
    simp [expPolar, Complex.equivRealProdCLM_symm_apply]
  rw [e]
  exact Complex.isOpenMap_exp.comp ((Homeomorph.mulLeft₀ _ hπ).isOpenMap.comp
    Complex.equivRealProdCLM.symm.toHomeomorph.isOpenMap)

/-- Continuity through an open map: if `g ∘ f` is continuous at `a`, `g` is continuous at
`f a`. -/
lemma continuousAt_of_comp_isOpenMap {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] {f : α → β} {g : β → γ} (hf : IsOpenMap f) {a : α}
    (h : ContinuousAt (g ∘ f) a) : ContinuousAt g (f a) :=
  calc map g (𝓝 (f a)) ≤ map g (map f (𝓝 a)) := map_mono (hf.nhds_le a)
    _ = map (g ∘ f) (𝓝 a) := map_map
    _ ≤ 𝓝 (g (f a)) := h

end ExpPolar

/-! ## 3. The neck representatives -/

section Neck

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {u : X.S → Q} (A : SectionAtlas (E := E) X u)

lemma neckRep_add_one (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) (η : Section E X) (s t : ℝ) :
    neckRep A j k η (s, t + 1) = neckRep A j k η (s, t) := by
  simp only [neckRep, NodalSurface.polar_add_one]

/-- `σ_j(s + s₀, t)` is continuous on `s > 0`. -/
lemma continuousAt_polar_shift (j : Fin A.nn) {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContinuousAt (fun p : ℝ × ℝ => X.polar (A.hol j) (p.1 + A.s0 j, p.2)) p := by
  have hsh : Continuous fun p : ℝ × ℝ => (p.1 + A.s0 j, p.2) := by fun_prop
  refine ContinuousAt.comp (g := X.polar (A.hol j)) ?_ hsh.continuousAt
  refine (A.continuousOn_polar j).continuousAt ?_
  refine mem_of_superset ((isOpen_lt continuous_const continuous_fst).mem_nhds ?_)
    fun q (hq : A.s0 j < q.1) => (le_of_lt hq : A.s0 j ≤ q.1)
  change A.s0 j < p.1 + A.s0 j
  linarith

/-- The neck representatives of a continuous section are continuous on `s > 0`. -/
lemma continuousOn_neckRep (hu : Continuous u) {η : Section E X} (hη : IsContSection u η)
    (j : Fin A.nn) (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn (neckRep A j k η) (Ioi 0 ×ˢ univ) := by
  intro p hp
  have hp1 : 0 < p.1 := hp.1
  refine ContinuousAt.continuousWithinAt ?_
  have hs : A.s0 j ≤ p.1 + A.s0 j := by linarith
  have h1 : ContinuousAt (fun y => tangentCoordChange 𝓘(ℝ, E) (u y) (u (A.node j)) (u y) (η y))
      (X.polar (A.hol j) (p.1 + A.s0 j, p.2)) :=
    continuousAt_coord_transfer hu (mem_extChartAt_source _)
      (A.neck_chart j (p.1 + A.s0 j, p.2) hs).2 (hη _)
  have h2 := ContinuousAt.comp (f := fun p : ℝ × ℝ => X.polar (A.hol j) (p.1 + A.s0 j, p.2))
    (x := p) h1 (continuousAt_polar_shift A j hp1)
  exact (Real.smoothTransition.continuous.continuousAt.comp continuous_fst.continuousAt).mul
    (((crd k).continuous_of_finiteDimensional.continuousAt.comp h2).sub continuousAt_const)

lemma crd_basis_sum (v : E) : ∑ k, crd k v • Module.finBasis ℝ E k = v := by
  conv_rhs => rw [← (Module.finBasis ℝ E).sum_repr v]
  rfl

/-- **Continuity on a neck**: if the neck representatives of `η'` are continuous on `s > 0`, then
`η'` is continuous at every point `σ_j(p₀)` with `p₀.1 > s₀`.  The section is read through the
open map `expPolar`. -/
lemma continuousAt_of_neck (hu : Continuous u) {η' : Section E X} (j : Fin A.nn)
    (hcont : ∀ k, ContinuousOn (neckRep A j k η') (Ioi 0 ×ˢ univ)) {p0 : ℝ × ℝ}
    (hp0 : A.s0 j < p0.1) :
    ContinuousAt (fun y => tangentCoordChange 𝓘(ℝ, E) (u y) (u (X.polar (A.hol j) p0)) (u y)
      (η' y)) (X.polar (A.hol j) p0) := by
  set φ := A.hol j
  set b := u (A.node j)
  set W : Set (ℝ × ℝ) := Ioi (A.s0 j) ×ˢ univ
  set K : ℝ × ℝ → E := fun q =>
    tangentCoordChange 𝓘(ℝ, E) (u (X.polar φ q)) b (u (X.polar φ q)) (η' (X.polar φ q))
  have hK : ContinuousOn K W := by
    have hk : ∀ k, ContinuousOn (fun q => crd k (K q)) W := by
      intro k
      have hsh : ContinuousOn (fun q : ℝ × ℝ => (q.1 - A.s0 j, q.2)) W := by fun_prop
      have hmaps : MapsTo (fun q : ℝ × ℝ => (q.1 - A.s0 j, q.2)) W (Ioi 0 ×ˢ univ) :=
        fun q hq => ⟨show 0 < q.1 - A.s0 j from sub_pos.2 hq.1, mem_univ _⟩
      have h1 := (hcont k).comp hsh hmaps
      have h2 : ContinuousOn (fun q : ℝ × ℝ => Real.smoothTransition (q.1 - A.s0 j)) W :=
        (Real.smoothTransition.continuous.comp (by fun_prop)).continuousOn
      refine ((h1.div h2 fun q hq => (Real.smoothTransition.pos_of_pos
        (sub_pos.2 hq.1)).ne').add (continuousOn_const (c := neckConst A j k η'))).congr
        fun q hq => ?_
      have hpos := (Real.smoothTransition.pos_of_pos (sub_pos.2 hq.1)).ne'
      simp only [Function.comp, Pi.div_apply, Pi.add_apply, neckRep, sub_add_cancel, K]
      rw [mul_div_cancel_left₀ _ hpos, sub_add_cancel]
    rw [show K = fun q => ∑ k, crd k (K q) • Module.finBasis ℝ E k from
      funext fun q => (crd_basis_sum _).symm]
    exact continuousOn_finsetSum _ fun k _ => (hk k).smul continuousOn_const
  set G : ℂ → E := fun ζ =>
    tangentCoordChange 𝓘(ℝ, E) (u (φ.symm ζ)) b (u (φ.symm ζ)) (η' (φ.symm ζ))
  have hW : IsOpen W := isOpen_Ioi.prod isOpen_univ
  have hKc : ContinuousAt K p0 := hK.continuousAt (hW.mem_nhds ⟨hp0, mem_univ _⟩)
  have hGc : ContinuousAt G (expPolar p0) :=
    continuousAt_of_comp_isOpenMap isOpenMap_expPolar (show ContinuousAt (G ∘ expPolar) p0 from hKc)
  have htgt : expPolar p0 ∈ φ.target := (A.neck_chart j p0 hp0.le).1
  have hx : X.polar φ p0 ∈ φ.source := φ.map_target htgt
  have hφx : φ (X.polar φ p0) = expPolar p0 := φ.right_inv htgt
  have h1 : ContinuousAt (G ∘ φ) (X.polar φ p0) :=
    ContinuousAt.comp_of_eq hGc (φ.continuousAt hx) hφx
  have hev : G ∘ φ =ᶠ[𝓝 (X.polar φ p0)]
      fun y => tangentCoordChange 𝓘(ℝ, E) (u y) b (u y) (η' y) := by
    filter_upwards [φ.open_source.mem_nhds hx] with y hy
    simp only [Function.comp, G, φ.left_inv hy]
  exact continuousAt_coord_transfer hu (A.neck_chart j p0 hp0.le).2 (mem_extChartAt_source _)
    (h1.congr hev)

/-- **Continuity at a nodal point**: if the neck representatives of `η'` are continuous on
`s > 0` and lie in `H^{3,δ}`, then `η'` is continuous at the nodal point; its value there has
the coordinates of the asymptotic constant, and the remainders decay as `s → ∞`. -/
lemma continuousAt_node {δ : ℝ} {hδ : 0 ≤ δ} {η' : Section E X} (j : Fin A.nn)
    (hcont : ∀ k, ContinuousOn (neckRep A j k η') (Ioi 0 ×ˢ univ))
    (hae : ∀ k, ∃ r : H 3 hδ, (H.val r : ℝ × ℝ → ℝ) =ᵐ[cyl] neckRep A j k η') :
    ContinuousAt (fun y => tangentCoordChange 𝓘(ℝ, E) (u y) (u (A.node j)) (u y) (η' y))
      (A.node j) := by
  set φ := A.hol j
  set x := A.node j
  set F : X.S → E := fun y => tangentCoordChange 𝓘(ℝ, E) (u y) (u x) (u y) (η' y)
  have hFx : F x = η' x := tangentCoordChange_self (mem_extChartAt_source _)
  obtain ⟨hxs, hφ0, -⟩ := A.isHol j
  suffices h : ∀ k, Tendsto (fun y => crd k (F y)) (𝓝 x) (𝓝 (crd k (F x))) by
    have := tendsto_finsetSum Finset.univ fun k _ => (h k).smul_const (Module.finBasis ℝ E k)
    exact (by simpa only [crd_basis_sum] using this : Tendsto F (𝓝 x) (𝓝 (F x)))
  intro k
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨r, hr⟩ := hae k
  obtain ⟨R, hR⟩ := exists_abs_lt_of_ae_eq_half r (hcont k) (neckRep_add_one A j k η') hr hε
  set T := A.s0 j + max R 1 + 1
  have hT : 0 < Real.exp (-2 * Real.pi * T) := Real.exp_pos _
  have hball : φ ⁻¹' Metric.ball 0 (Real.exp (-2 * Real.pi * T)) ∈ 𝓝 x :=
    (φ.continuousAt hxs).preimage_mem_nhds (by rw [hφ0]; exact Metric.ball_mem_nhds _ hT)
  filter_upwards [hball, φ.open_source.mem_nhds hxs] with z hz hzs
  by_cases hzx : z = x
  · rw [hzx, dist_self]; exact hε
  have hφz : φ z ≠ 0 := fun h => hzx (φ.injOn hzs hxs (h.trans hφ0.symm))
  obtain ⟨q, hq, hq1⟩ := exists_expPolar_eq hφz
  have hqT : T < q.1 := by
    rw [mem_preimage, Metric.mem_ball, dist_zero_right] at hz
    have hlog : Real.log ‖φ z‖ < -2 * Real.pi * T :=
      (Real.log_lt_iff_lt_exp (norm_pos_iff.2 hφz)).2 hz
    rw [hq1, lt_div_iff₀ (by positivity)]
    linarith
  have hzq : z = X.polar φ q := by
    rw [NodalSurface.polar_eq, hq, φ.left_inv hzs]
  have hq' : 1 ≤ q.1 - A.s0 j := by linarith [le_max_right R 1]
  have hqR : R < q.1 - A.s0 j := by linarith [le_max_left R 1]
  have hb := hR (q.1 - A.s0 j, q.2) hqR
  simp only [neckRep, Real.smoothTransition.one_of_one_le hq', one_mul, sub_add_cancel,
    Prod.mk.eta, neckConst] at hb
  rw [Real.dist_eq, hFx, hzq]
  exact hb

end Neck

/-! ## 4. The limit of representatives, nodes included -/

section Limit

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {u : X.S → Q} (A : SectionAtlas (E := E) X u)

/-- **Continuity on a disc**: if the disc representatives of `η'` are continuous on the disc,
`η'` is continuous at every point of its core. -/
lemma continuousAt_of_disc (hu : Continuous u) {η' : Section E X} (i : Fin A.nd)
    (hcontF : ∀ k, ContinuousOn (discRep A i k η') discD) {p0 : ℝ × ℝ} (hp0D : p0 ∈ discD) :
    ContinuousAt (fun y => tangentCoordChange 𝓘(ℝ, E) (u y)
      (u (X.discPt (A.center i) (A.ε i) p0)) (u y) (η' y)) (X.discPt (A.center i) (A.ε i) p0) := by
  set c := A.center i
  set ε := A.ε i
  have hεne : ε ≠ 0 := (A.ε_pos i).ne'
  set K : ℝ × ℝ → E := fun p => tangentCoordChange 𝓘(ℝ, E) (u (X.discPt c ε p)) (u c)
    (u (X.discPt c ε p)) (η' (X.discPt c ε p))
  have hK : ContinuousOn K discD := by
    have hk : ∀ k, ContinuousOn (fun p => crd k (K p)) discD := by
      intro k
      refine ((hcontF k).div continuous_discCut.continuousOn
        fun p hp => (discCut_pos hp).ne').congr fun p hp => ?_
      rw [Pi.div_apply, eq_div_iff (discCut_pos hp).ne']
      simp only [discRep, K]
      ring
    rw [show K = fun p => ∑ k, crd k (K p) • Module.finBasis ℝ E k from
      funext fun p => (crd_basis_sum _).symm]
    exact continuousOn_finsetSum _ fun k _ => (hk k).smul continuousOn_const
  set ψ : X.S → ℝ × ℝ := fun y => placeInv c ε (extChartAt 𝓘(ℝ, E2) c y)
  have htgt := (A.disc_chart i p0 hp0D).1
  have hxs : X.discPt c ε p0 ∈ (extChartAt 𝓘(ℝ, E2) c).source :=
    (extChartAt 𝓘(ℝ, E2) c).map_target htgt
  have hψx : ψ (X.discPt c ε p0) = p0 := by
    simp only [ψ, NodalSurface.discPt]
    rw [(extChartAt 𝓘(ℝ, E2) c).right_inv htgt, placeInv_place c hεne]
  have hψc : ContinuousAt ψ (X.discPt c ε p0) :=
    (continuous_placeInv c ε).continuousAt.comp (continuousAt_extChartAt' hxs)
  have hKψ : ContinuousAt (K ∘ ψ) (X.discPt c ε p0) :=
    ContinuousAt.comp_of_eq (hK.continuousAt (isOpen_discD.mem_nhds (hψx ▸ hp0D))) hψc hψx
  have hev : (K ∘ ψ) =ᶠ[𝓝 (X.discPt c ε p0)]
      fun y => tangentCoordChange 𝓘(ℝ, E) (u y) (u c) (u y) (η' y) := by
    filter_upwards [(isOpen_extChartAt_source c).mem_nhds hxs] with y hy
    have : X.discPt c ε (ψ y) = y := by
      simp only [ψ, NodalSurface.discPt]
      rw [place_placeInv c hεne, (extChartAt 𝓘(ℝ, E2) c).left_inv hy]
    simp only [Function.comp, K, this]
  exact continuousAt_coord_transfer hu (A.disc_chart i p0 hp0D).2 (mem_extChartAt_source _)
    (hKψ.congr hev)

/-- Uniform limits on a set: if `|f n - f n'| ≤ C ‖b n - b n'‖` on `D`, `b n → b`, and `f n → f`
pointwise, then `f n → f` uniformly on `D`. -/
lemma tendstoUniformlyOn_of_bound {F : Type*} [NormedAddCommGroup F] {D : Set (ℝ × ℝ)}
    {f : ℕ → ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℝ} {b : ℕ → F} {b' : F} (hb : Tendsto b atTop (𝓝 b'))
    (hF : ∀ n n', ∀ p ∈ D, |f n p - f n' p| ≤ 3 * ‖b n - b n'‖)
    (hfg : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (g p))) :
    TendstoUniformlyOn f g atTop D := by
  have hbd : ∀ n, ∀ p ∈ D, |f n p - g p| ≤ 3 * ‖b n - b'‖ := by
    intro n p hp
    have h1 : Tendsto (fun n' => |f n p - f n' p|) atTop (𝓝 |f n p - g p|) :=
      (tendsto_const_nhds.sub (hfg p)).abs
    have h2 : Tendsto (fun n' => 3 * ‖b n - b n'‖) atTop (𝓝 (3 * ‖b n - b'‖)) :=
      ((tendsto_const_nhds.sub hb).norm).const_mul 3
    exact le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun n' => hF n n' p hp)
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  have h3 : Tendsto (fun n => 3 * ‖b n - b'‖) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hb).const_mul 3
    simpa using this
  filter_upwards [(h3.eventually (gt_mem_nhds he))] with n hn p hp
  rw [dist_comm, Real.dist_eq]
  exact (hbd n p hp).trans_lt hn

lemma cauchySeq_of_bound {F : Type*} [NormedAddCommGroup F] {x : ℕ → ℝ} {b : ℕ → F} {b' : F}
    (hb : Tendsto b atTop (𝓝 b')) (hF : ∀ n n', |x n - x n'| ≤ 3 * ‖b n - b n'‖) :
    CauchySeq x := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hb.cauchySeq (ε / 4) (by positivity)
  refine ⟨N, fun n hn n' hn' => ?_⟩
  rw [Real.dist_eq]
  have := hN n hn n' hn'
  rw [dist_eq_norm] at this
  linarith [hF n n']

/-- **The limit of representatives**, nodes included: if `v n → w` in the block space and `v n`
represents the continuous section `η n`, then `η n` converges at every point to a continuous
section represented by `w`. -/
theorem exists_limit_section_nodal (hu : Continuous u) {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0}
    {hmono : StrictMono δ} {v : ℕ → (blocks A δ h0 hmono) 0} {w : (blocks A δ h0 hmono) 0}
    (hv : Tendsto v atTop (𝓝 w)) {η : ℕ → Section E X} (hc : ∀ n, IsContSection u (η n))
    (hr : ∀ n, IsRep (η n) (v n)) :
    ∃ η' : Section E X, IsContSection u η' ∧ IsRep η' w ∧
      ∀ y, Tendsto (fun n => η n y) atTop (𝓝 (η' y)) := by
  set hd := Neck.δ_nonneg δ h0 hmono 0
  have hb : ∀ i k, Tendsto (fun n => discBlock (v n) i k) atTop (𝓝 (discBlock w i k)) :=
    fun i k => (((continuous_apply (i, k)).comp continuous_fst).tendsto w).comp hv
  have hbn : ∀ j k, Tendsto (fun n => neckBlock (v n) j k) atTop (𝓝 (neckBlock w j k)) :=
    fun j k => (((continuous_apply (j, k)).comp continuous_snd).tendsto w).comp hv
  have hbc : ∀ j k, Tendsto (fun n => (neckBlock (v n) j k).1) atTop
      (𝓝 (neckBlock w j k).1) := fun j k => (continuous_fst.tendsto _).comp (hbn j k)
  have hbr : ∀ j k, Tendsto (fun n => (neckBlock (v n) j k).2) atTop
      (𝓝 (neckBlock w j k).2) := fun j k => (continuous_snd.tendsto _).comp (hbn j k)
  have hconst : ∀ n j k, (neckBlock (v n) j k).1 = neckConst A j k (η n) :=
    fun n j k => ((hr n).2 j k).1
  -- the sup bounds
  have hF : ∀ n n' i k, ∀ p ∈ discD, |discRep A i k (η n) p - discRep A i k (η n') p| ≤
      3 * ‖discBlock (v n) i k - discBlock (v n') i k‖ := by
    intro n n' i k p hp
    refine abs_le_of_ae_eq_three (hδ := hd) _ isOpen_discD discD_sub
      ((continuousOn_discRep A hu (hc n) i k).sub (continuousOn_discRep A hu (hc n') i k)) ?_ p hp
    filter_upwards [val_sub_ae (discBlock (v n) i k) (discBlock (v n') i k), (hr n).1 i k,
      (hr n').1 i k] with x h1 h2 h3
    rw [h1, h2, h3]; rfl
  have hFn : ∀ n n' j k, ∀ p ∈ (Ioi (0 : ℝ) ×ˢ univ : Set (ℝ × ℝ)),
      |neckRep A j k (η n) p - neckRep A j k (η n') p| ≤
        3 * ‖(neckBlock (v n) j k).2 - (neckBlock (v n') j k).2‖ := by
    intro n n' j k p hp
    refine abs_le_of_ae_eq_half (hδ := hd) _ (h := fun p => neckRep A j k (η n) p -
      neckRep A j k (η n') p) ((continuousOn_neckRep A hu (hc n) j k).sub
        (continuousOn_neckRep A hu (hc n') j k)) (fun s t => by simp only [neckRep_add_one])
      ?_ hp.1
    filter_upwards [val_sub_ae (neckBlock (v n) j k).2 (neckBlock (v n') j k).2,
      ((hr n).2 j k).2, ((hr n').2 j k).2] with x h1 h2 h3
    rw [h1, h2, h3]
  -- pointwise convergence of the sections
  have hconv : ∀ y, ∃ L, Tendsto (fun n => η n y) atTop (𝓝 L) := by
    intro y
    rcases A.cover y with ⟨i, p, hp, rfl⟩ | ⟨j, rfl | ⟨p, hp, rfl⟩⟩
    · have hpD := mem_discD_of_core hp
      set z := X.discPt (A.center i) (A.ε i) p
      have hk : ∀ k, ∃ c, Tendsto (fun n => crd k (tangentCoordChange 𝓘(ℝ, E) (u z)
          (u (A.center i)) (u z) (η n z))) atTop (𝓝 c) := by
        intro k
        obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete
          (cauchySeq_of_bound (hb i k) fun n n' => hF n n' i k p hpD)
        refine ⟨c, hc.congr fun n => ?_⟩
        simp only [discRep, discCut_eq_one hp, one_mul]; rfl
      choose c hc using hk
      have h1 := ((tangentCoordChange 𝓘(ℝ, E) (u (A.center i)) (u z) (u z)).continuous.tendsto
        _).comp (tendsto_of_crd hc)
      exact ⟨_, h1.congr fun n => tcc_inv (A.disc_chart i p hpD).2 _⟩
    · exact ⟨_, tendsto_of_crd fun k => (hbc j k).congr fun n => hconst n j k⟩
    · set y := X.polar (A.hol j) p
      have hp' : (1 : ℝ) ≤ p.1 - A.s0 j := by linarith
      have hk : ∀ k, ∃ c, Tendsto (fun n => crd k (tangentCoordChange 𝓘(ℝ, E) (u y)
          (u (A.node j)) (u y) (η n y))) atTop (𝓝 c) := by
        intro k
        obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_bound (hbr j k)
          fun n n' => hFn n n' j k (p.1 - A.s0 j, p.2) ⟨by change (0 : ℝ) < p.1 - A.s0 j; linarith,
            mem_univ _⟩)
        refine ⟨c + (neckBlock w j k).1, (hc.add (hbc j k)).congr fun n => ?_⟩
        rw [hconst]
        simp only [neckRep, Real.smoothTransition.one_of_one_le hp', one_mul, sub_add_cancel,
          y]
      choose c hc using hk
      have h1 := ((tangentCoordChange 𝓘(ℝ, E) (u (A.node j)) (u y) (u y)).continuous.tendsto
        _).comp (tendsto_of_crd hc)
      exact ⟨_, h1.congr fun n => tcc_inv (A.neck_chart j p (by linarith)).2 _⟩
  choose η' hη' using hconv
  -- the representatives converge pointwise
  have hrep : ∀ i k p, Tendsto (fun n => discRep A i k (η n) p) atTop
      (𝓝 (discRep A i k η' p)) := fun i k p =>
    tendsto_const_nhds.mul (((crd k).continuous_of_finiteDimensional.tendsto _).comp
      (((tangentCoordChange 𝓘(ℝ, E) _ _ _).continuous.tendsto _).comp (hη' _)))
  have hcn : ∀ j k, Tendsto (fun n => neckConst A j k (η n)) atTop
      (𝓝 (neckConst A j k η')) := fun j k =>
    ((crd k).continuous_of_finiteDimensional.tendsto _).comp (hη' _)
  have hrepn : ∀ j k p, Tendsto (fun n => neckRep A j k (η n) p) atTop
      (𝓝 (neckRep A j k η' p)) := fun j k p =>
    tendsto_const_nhds.mul ((((crd k).continuous_of_finiteDimensional.tendsto _).comp
      (((tangentCoordChange 𝓘(ℝ, E) _ _ _).continuous.tendsto _).comp (hη' _))).sub (hcn j k))
  have hneck : ∀ j k, (H.val (neckBlock w j k).2 : ℝ × ℝ → ℝ) =ᵐ[cyl] neckRep A j k η' :=
    fun j k => ae_eq_of_tendsto_Lp (f := fun n => valCLM 3 hd (neckBlock (v n) j k).2)
      (((valCLM 3 hd).continuous.tendsto _).comp (hbr j k)) (fun n => ((hr n).2 j k).2)
      (ae_of_all _ fun p => hrepn j k p)
  have hIsRep : IsRep η' w := by
    refine ⟨fun i k => ?_, fun j k => ⟨?_, hneck j k⟩⟩
    · exact ae_eq_of_tendsto_Lp (f := fun n => valCLM 3 hd (discBlock (v n) i k))
        (((valCLM 3 hd).continuous.tendsto _).comp (hb i k)) (fun n => (hr n).1 i k)
        (ae_of_all _ fun p => hrep i k p)
    · exact tendsto_nhds_unique (hbc j k) ((hcn j k).congr fun n => (hconst n j k).symm)
  refine ⟨η', fun x => ?_, hIsRep, hη'⟩
  -- continuity of the limit at `x`
  have hcontn : ∀ j k, ContinuousOn (neckRep A j k η') (Ioi 0 ×ˢ univ) := fun j k =>
    (tendstoUniformlyOn_of_bound (hbr j k) (fun n n' p hp => hFn n n' j k p hp)
      (hrepn j k)).continuousOn
      (Frequently.of_forall fun n => continuousOn_neckRep A hu (hc n) j k)
  rcases A.cover x with ⟨i, p0, hp0, rfl⟩ | ⟨j, rfl | ⟨p0, hp0, rfl⟩⟩
  · have hcontF : ∀ k, ContinuousOn (discRep A i k η') discD := fun k =>
      (tendstoUniformlyOn_of_bound (hb i k) (fun n n' p hp => hF n n' i k p hp)
        (hrep i k)).continuousOn
        (Frequently.of_forall fun n => continuousOn_discRep A hu (hc n) i k)
    exact continuousAt_of_disc A hu i hcontF (mem_discD_of_core hp0)
  · exact continuousAt_node A j (hcontn j) fun k => ⟨_, hneck j k⟩
  · exact continuousAt_of_neck A hu j (hcontn j) (by linarith)

end Limit

/-! ## 5. `SectionsClosed` and `ConstraintsClosed` -/

section Closed

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {m : ℕ} {X : NodalSurface m} {u : X.S → Q}

/-- **`SectionsClosed`** (Memoir p. 66, the completeness of the norm) for every continuous map
`u` and every atlas, nodes included. -/
theorem sectionsClosed (hu : Continuous u) (A : SectionAtlas (E := E) X u) (δ : ℕ → ℝ)
    (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) : SectionsClosed A δ h0 hmono := by
  refine isClosed_of_closure_subset fun w hw => ?_
  obtain ⟨v, hvS, hv⟩ := mem_closure_iff_seq_limit.1 hw
  have hvS' : ∀ n, ∃ η : Section E X, IsContSection u η ∧ IsMatchingSection X η ∧
      IsRep η (v n) := hvS
  choose η hc hm hr using hvS'
  obtain ⟨η', hc', hr', hlim⟩ := exists_limit_section_nodal A hu hv hc hr
  exact ⟨η', hc', fun x y hxy => tendsto_nhds_unique (hlim x)
    ((hlim y).congr fun n => (hm n x y hxy).symm), hr'⟩

/-- **`ConstraintsClosed`** (Memoir p. 68) for every continuous map and every atlas, nodes
included. -/
theorem constraintsClosed (hu : Continuous u) (A : SectionAtlas (E := E) X u) (δ : ℕ → ℝ)
    (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (C : LinearConstraints X E) :
    ConstraintsClosed A δ h0 hmono C := by
  refine isClosed_of_closure_subset fun w hw => ?_
  obtain ⟨v, hvS, hv⟩ := mem_closure_iff_seq_limit.1 hw
  have hvS' : ∀ n, ∃ η : Section E X, IsContSection u η ∧ IsMatchingSection X η ∧
      IsRep η (v n) ∧ ∀ l, (η (C.pt l) : E) ∈ C.H l := hvS
  choose η hc hm hr hH using hvS'
  obtain ⟨η', hc', hr', hlim⟩ := exists_limit_section_nodal A hu hv hc hr
  refine ⟨η', hc', fun x y hxy => tendsto_nhds_unique (hlim x)
    ((hlim y).congr fun n => (hm n x y hxy).symm), hr', fun l => ?_⟩
  exact (C.H l).closed_of_finiteDimensional.mem_of_tendsto (hlim (C.pt l))
    (Eventually.of_forall fun n => hH n l)

/-- `H^{3,δ₀}_c(S, u*TQ)` is the set of representatives itself. -/
theorem sectionSpace_eq_sectionsSub (hu : Continuous u) (A : SectionAtlas (E := E) X u)
    (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) :
    sectionSpace A δ h0 hmono = sectionsSub A δ h0 hmono :=
  sectionSpace_eq A δ h0 hmono (sectionsClosed hu A δ h0 hmono)

/-- `E_u` is the set of representatives of the sections satisfying the constraints. -/
theorem uSpace_eq_constraintsSub (hu : Continuous u) (A : SectionAtlas (E := E) X u)
    (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) (C : LinearConstraints X E) :
    uSpace A δ h0 hmono C = constraintsSub A δ h0 hmono C :=
  uSpace_eq A δ h0 hmono C (constraintsClosed hu A δ h0 hmono C)

end Closed

end GWMemoir
