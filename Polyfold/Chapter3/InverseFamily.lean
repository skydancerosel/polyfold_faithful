import Polyfold.Chapter3.LocalSolvability

/-!
# The inverse of a family of sc-isomorphisms (Lemma 3.61)

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I*, §3.7, **Lemma 3.61** (quoted from
[25, Proposition 4.8] without proof): let `V` be a relatively open subset of a partial quadrant in
a finite-dimensional space `G`, `E`, `F` sc-Banach spaces and `v ↦ L(v)` a family of linear
operators such that (i) every `L(v) : E → F` is an sc-isomorphism, (ii) `(v, h) ↦ L(v)h` is
sc-smooth on `V ⊕ E`, and (iii) for every level `m` there is `c_m > 0` with
`|L(v)h|_m ≥ c_m |h|_m` for all `v ∈ V`, `h ∈ E_m`.  Then `(v, k) ↦ L(v)⁻¹k` is sc-smooth on
`V ⊕ F`.  "It is not assumed that the operators `v ↦ L(v)` depend continuously on `v`" in the
operator norm.

The statement is formalized for germs: `V` is a germ `Gv` of relatively open neighbourhoods of `0`
in the partial quadrant `C̃ ⊆ G`, and `V ⊕ E` is the product germ `Gv.prodFull E`
(`Polyfold.ScNbhdGerm.prodFull`).

## Main results

* `Polyfold.famInv_isSc0Germ`: `Λ(v, k) = L(v)⁻¹k` is an sc⁰-germ.
* `Polyfold.famInv_isSc1GermWith`: `Λ` is an sc¹-germ with derivative
  `DΛ(v, k)(δv, δk) = L(v)⁻¹(δk − D₁Φ(v, L(v)⁻¹k)δv)`, `Φ(v, h) = L(v)h`.
* `Polyfold.lemma_3_61`: `Λ` is sc-smooth.
-/

open Set Filter Topology Function Asymptotics Metric

noncomputable section

namespace Polyfold

variable {G₀ : Type} [NormedAddCommGroup G₀] [NormedSpace ℝ G₀] [FiniteDimensional ℝ G₀]
  {Cg : Set G₀} {E F : ScBanach}

/-! ### The product germ `V ⊕ E` -/

/-- The germ `V ⊕ E` of neighbourhoods of `0` in `C̃ ⊕ E` with levels `V_m × E_m`, for a germ
`V = (V_m)` of relatively open neighbourhoods of `0` in the partial quadrant `C̃` of the
finite-dimensional space `G` (all `V_m ⊆ G`). -/
def ScNbhdGerm.prodFull (Gv : ScNbhdGerm (ScBanach.const G₀) Cg) (E : ScBanach) :
    ScNbhdGerm (ScBanach.paramProd G₀ E) (Cg ×ˢ (univ : Set (E 0))) where
  U m := Gv.U m ×ˢ univ
  nested m x hx := ⟨Gv.nested m x.1 hx.1, mem_univ _⟩
  zero_mem m := ⟨Gv.zero_mem m, mem_univ _⟩
  relOpen m := by
    obtain ⟨O, hO, hU⟩ := Gv.relOpen m
    refine ⟨O ×ˢ univ, hO.prod isOpen_univ, ?_⟩
    rw [ScBanach.paramProd_lvlSet, hU, ScBanach.const_lvlSet]
    ext p
    simp only [mem_prod, mem_univ, and_true, mem_inter_iff]

@[simp] lemma ScNbhdGerm.prodFull_U (Gv : ScNbhdGerm (ScBanach.const G₀) Cg) (E : ScBanach)
    (m : ℕ) : (Gv.prodFull E).U m = Gv.U m ×ˢ univ := rfl

/-- The level-`m` neighbourhood of `V` is contained in the level-`0` one (all levels of `G` are
`G`). -/
lemma ScNbhdGerm.const_U_subset (Gv : ScNbhdGerm (ScBanach.const G₀) Cg) (m : ℕ) :
    Gv.U m ⊆ Gv.U 0 := fun v hv => by
  have := Gv.toBase_mem hv
  rwa [ScBanach.const_toBase] at this

/-- The level-`(m+1)` neighbourhood of `V` is contained in the level-`m` one. -/
lemma ScNbhdGerm.const_U_succ_subset (Gv : ScNbhdGerm (ScBanach.const G₀) Cg) (m : ℕ) :
    Gv.U (m + 1) ⊆ Gv.U m := fun v hv => Gv.nested m v hv

/-! ### The family and its inverse -/

variable (L : G₀ → ScIso E F)

/-- `Φ(v, h) = L(v)h` on level `0`. -/
def famMap : G₀ × E 0 → F 0 := fun p => L p.1 0 p.2

/-- `Λ(v, k) = L(v)⁻¹k` on level `0`. -/
def famInv : G₀ × F 0 → E 0 := fun p => (L p.1 0).symm p.2

lemma famMap_apply (p : G₀ × E 0) : famMap L p = L p.1 0 p.2 := rfl

lemma famInv_apply (p : G₀ × F 0) : famInv L p = (L p.1 0).symm p.2 := rfl

/-- The level-`m` map of `Φ` is `(v, h) ↦ L(v)_m h`. -/
lemma levelMap_famMap (m : ℕ) (p : (ScBanach.paramProd G₀ E) m) :
    levelMap (E := ScBanach.paramProd G₀ E) (F := F) (famMap L) m p = L p.1 m p.2 := by
  apply levelMap_eq_of_toBase_eq
  rw [ScBanach.paramProd_toBase]
  exact (L p.1).toBase_comm m p.2

/-- The level-`m` map of `Λ` is `(v, k) ↦ L(v)_m⁻¹ k`. -/
lemma levelMap_famInv (m : ℕ) (p : (ScBanach.paramProd G₀ F) m) :
    levelMap (E := ScBanach.paramProd G₀ F) (F := E) (famInv L) m p = (L p.1 m).symm p.2 := by
  apply levelMap_eq_of_toBase_eq
  rw [ScBanach.paramProd_toBase]
  exact (L p.1).symm.toBase_comm m p.2

variable {L}

/-- **Lemma 3.61, the sc⁰ part**: `Λ(v, k) = L(v)⁻¹k` is an sc⁰-germ on `V ⊕ F`.  Proof: on level
`m`, `|L(v)⁻¹k − L(v₀)⁻¹k₀|_m ≤ c_m⁻¹(|k − k₀|_m + |L(v₀)h₀ − L(v)h₀|_m)` with
`h₀ = L(v₀)⁻¹k₀`, and `v ↦ L(v)h₀` is continuous by (ii). -/
theorem famInv_isSc0Germ {Gv : ScNbhdGerm (ScBanach.const G₀) Cg}
    (hΦ : IsSc0Germ (E := ScBanach.paramProd G₀ E) (F := F) (Gv.prodFull E) (famMap L))
    (hc : ∀ m, ∃ c > 0, ∀ v ∈ Gv.U 0, ∀ h : E m, c * ‖h‖ ≤ ‖L v m h‖) :
    IsSc0Germ (E := ScBanach.paramProd G₀ F) (F := E) (Gv.prodFull F) (famInv L) where
  mem_range m p _ := ⟨(L p.1 m).symm p.2, by
    rw [ScBanach.paramProd_toBase]; exact (L p.1).symm.toBase_comm m p.2⟩
  continuousOn m := by
    refine ContinuousOn.congr (f := fun p : (ScBanach.paramProd G₀ F) m => (L p.1 m).symm p.2) ?_
      fun p _ => levelMap_famInv L m p
    intro p₀ hp₀
    obtain ⟨c, hc0, hcm⟩ := hc m
    set h₀ : E m := (L p₀.1 m).symm p₀.2 with hh₀
    have hg : ContinuousWithinAt
        (fun p : (ScBanach.paramProd G₀ F) m => ((p.1, h₀) : (ScBanach.paramProd G₀ E) m))
        (Gv.U m ×ˢ univ) p₀ :=
      (continuous_fst.prodMk continuous_const).continuousWithinAt
    have hmaps : MapsTo (fun p : (ScBanach.paramProd G₀ F) m => ((p.1, h₀) : (ScBanach.paramProd G₀ E) m))
        (Gv.U m ×ˢ univ) (Gv.U m ×ˢ univ) := fun p hp => ⟨hp.1, mem_univ _⟩
    have hΦc : ContinuousWithinAt
        (fun p : (ScBanach.paramProd G₀ F) m =>
          levelMap (E := ScBanach.paramProd G₀ E) (F := F) (famMap L) m (p.1, h₀))
        (Gv.U m ×ˢ univ) p₀ :=
      ContinuousWithinAt.comp
        (f := fun p : (ScBanach.paramProd G₀ F) m => ((p.1, h₀) : (ScBanach.paramProd G₀ E) m))
        (x := p₀) ((hΦ.continuousOn m) (p₀.1, h₀) ⟨hp₀.1, mem_univ _⟩) hg hmaps
    rw [Metric.continuousWithinAt_iff] at hΦc ⊢
    intro ε hε
    obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hΦc (c * ε / 2) (by positivity)
    refine ⟨min δ₁ (c * ε / 2), by positivity, fun p hp hpd => ?_⟩
    have hp1 : p.1 ∈ Gv.U 0 := Gv.const_U_subset m hp.1
    have hk : ‖p.2 - p₀.2‖ < c * ε / 2 := by
      calc ‖p.2 - p₀.2‖ = dist p.2 p₀.2 := (dist_eq_norm _ _).symm
        _ ≤ dist p p₀ := by rw [Prod.dist_eq]; exact le_max_right _ _
        _ < c * ε / 2 := hpd.trans_le (min_le_right _ _)
    have hΦ' := hδ₁' hp (hpd.trans_le (min_le_left _ _))
    rw [dist_eq_norm, levelMap_famMap, levelMap_famMap] at hΦ'
    simp only at hΦ'
    rw [dist_eq_norm]
    have hL := hcm p.1 hp1 ((L p.1 m).symm p.2 - h₀)
    rw [map_sub, ContinuousLinearEquiv.apply_symm_apply] at hL
    have hk₀ : L p₀.1 m h₀ = p₀.2 := by rw [hh₀, ContinuousLinearEquiv.apply_symm_apply]
    have e : p.2 - L p.1 m h₀ = (p.2 - p₀.2) + (L p₀.1 m h₀ - L p.1 m h₀) := by rw [hk₀]; abel
    have hbound : ‖(L p.1 m).symm p.2 - h₀‖ ≤ c⁻¹ * (‖p.2 - p₀.2‖ + ‖L p₀.1 m h₀ - L p.1 m h₀‖) := by
      rw [le_inv_mul_iff₀ hc0]
      exact hL.trans (by rw [e]; exact norm_add_le _ _)
    calc ‖(L p.1 m).symm p.2 - h₀‖
        ≤ c⁻¹ * (‖p.2 - p₀.2‖ + ‖L p₀.1 m h₀ - L p.1 m h₀‖) := hbound
      _ < c⁻¹ * (c * ε / 2 + c * ε / 2) := by
          gcongr
          rwa [norm_sub_rev] at hΦ'
      _ = ε := by field_simp; ring

/-! ### A tube lemma -/

/-- **Uniformity on compact sets of a jointly continuous function vanishing on `{x₀} × K`**: if
`Ψ : X × Y → Z` is continuous on `s × Y`, `K ⊆ Y` is compact and `Ψ(x₀, u) = 0` for `u ∈ K`,
then `‖Ψ(x, u)‖ ≤ ε` for all `u ∈ K` and all `x ∈ s` close to `x₀`.  (Proof by contradiction
with sequences.) -/
theorem exists_forall_norm_le_of_isCompact {X Y Z : Type} [MetricSpace X] [MetricSpace Y]
    [NormedAddCommGroup Z] {s : Set X} {x₀ : X} (hx₀ : x₀ ∈ s) {K : Set Y} (hK : IsCompact K)
    {Ψ : X → Y → Z} (hΨ : ContinuousOn (fun q : X × Y => Ψ q.1 q.2) (s ×ˢ univ))
    (h0 : ∀ u ∈ K, Ψ x₀ u = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ s, dist x x₀ < δ → ∀ u ∈ K, ‖Ψ x u‖ ≤ ε := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ n : ℕ, ∃ x ∈ s, dist x x₀ < 1 / ((n : ℝ) + 1) ∧ ∃ u ∈ K, ε < ‖Ψ x u‖ :=
    fun n => hcon _ (by positivity)
  choose x hxs hxd u huK hεu using hseq
  have hx : Tendsto x atTop (𝓝 x₀) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
    refine ⟨N, fun n hn => (hxd n).trans (lt_of_le_of_lt ?_ hN)⟩
    gcongr
  obtain ⟨u₀, hu₀, φ, hφ, hu⟩ := hK.tendsto_subseq huK
  have hxφ : Tendsto (x ∘ φ) atTop (𝓝 x₀) := hx.comp hφ.tendsto_atTop
  have hlim : Tendsto (fun n => Ψ (x (φ n)) (u (φ n))) atTop (𝓝 (Ψ x₀ u₀)) :=
    ((hΨ (x₀, u₀) ⟨hx₀, mem_univ _⟩).tendsto).comp
      (tendsto_nhdsWithin_iff.2 ⟨hxφ.prodMk_nhds hu, Eventually.of_forall fun n => ⟨hxs _, mem_univ _⟩⟩)
  rw [h0 u₀ hu₀] at hlim
  have hnorm : Tendsto (fun n => ‖Ψ (x (φ n)) (u (φ n))‖) atTop (𝓝 0) := by
    simpa using hlim.norm
  obtain ⟨n, hn⟩ := (hnorm.eventually (gt_mem_nhds hε)).exists
  exact absurd (hεu (φ n)) (not_lt.2 hn.le)

/-! ### The derivative of `Λ` -/

/-- `L(v)⁻¹` commutes with the shifted base maps. -/
lemma ScIso.symm_shift_toBase (T : ScIso E F) (m : ℕ) (y : F (m + 1)) :
    E.shift.toBase m (T.symm (m + 1) y) = T.symm 1 (F.shift.toBase m y) := by
  apply E.toBase_injective 1
  rw [← E.shift_toBase, T.symm.toBase_comm, T.symm.toBase_comm, ← F.shift_toBase]

variable (L) in
/-- The candidate derivative `DΛ(v, k)(δv, δk) = L(v)⁻¹(δk − D₁Φ(v, L(v)⁻¹k)δv)` of
`Λ(v, k) = L(v)⁻¹k` at a point `(v, k)` of level `1`, for a derivative family `DΦ` of
`Φ(v, h) = L(v)h`. -/
def famInvDeriv (DΦ : (ScBanach.paramProd G₀ E) 1 → (ScBanach.paramProd G₀ E) 0 →L[ℝ] F 0)
    (p : (ScBanach.paramProd G₀ F) 1) : (ScBanach.paramProd G₀ F) 0 →L[ℝ] E 0 :=
  ((L p.1 0).symm : F 0 →L[ℝ] E 0).comp
    (ContinuousLinearMap.snd ℝ G₀ (F 0) -
      ((DΦ (p.1, (L p.1 1).symm p.2)).comp (ContinuousLinearMap.inl ℝ G₀ (E 0))).comp
        (ContinuousLinearMap.fst ℝ G₀ (F 0)))

lemma famInvDeriv_apply (DΦ : (ScBanach.paramProd G₀ E) 1 → (ScBanach.paramProd G₀ E) 0 →L[ℝ] F 0)
    (p : (ScBanach.paramProd G₀ F) 1) (q : (ScBanach.paramProd G₀ F) 0) :
    famInvDeriv L DΦ p q = (L p.1 0).symm (q.2 - DΦ (p.1, (L p.1 1).symm p.2) (q.1, 0)) := by
  simp only [famInvDeriv, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.inl_apply,
    ContinuousLinearEquiv.coe_coe]

/-- **Lemma 3.61, differentiability of `Λ`**: at a point `p = (v, k)` of level `1`, `Λ` (as a map
`(V ⊕ F)₁ → E₀`) is differentiable within `(V ⊕ F)₁` with derivative `DΛ(p)`.  Proof: with
`h = L(v)⁻¹k`, `w = DΛ(p)(δv, δk)` and the remainder `r = Φ(v', h) − Φ(v, h) − D₁Φ(v, h)δv` of
`Φ` along `(δv, 0)`,
`Λ(v', k') − Λ(v, k) − w = L(v')⁻¹[(L(v) − L(v'))w] − L(v')⁻¹r`;
`|r|₀ = o(|δv|)` by the differentiability of `Φ`, and `|(L(v) − L(v'))w|₀ = o(|(δv, δk)|₁)` because
`w/|(δv, δk)|₁` lies in the compact set `DΛ(p)(ι(B₁))` (`ι : F₁ → F₀` is compact) and
`(L(v) − L(v'))u → 0` uniformly for `u` in a compact set (`exists_forall_norm_le_of_isCompact`). -/
theorem famInv_hasFDerivWithinAt {Gv : ScNbhdGerm (ScBanach.const G₀) Cg}
    {DΦ : (ScBanach.paramProd G₀ E) 1 → (ScBanach.paramProd G₀ E) 0 →L[ℝ] F 0}
    (hΦ1 : IsSc1GermWith (E := ScBanach.paramProd G₀ E) (F := F) (Gv.prodFull E) (famMap L) DΦ)
    (hc : ∀ m, ∃ c > 0, ∀ v ∈ Gv.U 0, ∀ h : E m, c * ‖h‖ ≤ ‖L v m h‖)
    {p : (ScBanach.paramProd G₀ F) 1} (hp : p ∈ (Gv.prodFull F).U 1) :
    HasFDerivWithinAt (famInv L ∘ (ScBanach.paramProd G₀ F).toBase 1)
      ((famInvDeriv L DΦ p).comp ((ScBanach.paramProd G₀ F).toBase 1)) ((Gv.prodFull F).U 1) p := by
  obtain ⟨c, hc0, hcm⟩ := hc 0
  set v : G₀ := p.1 with hv
  set k : F 1 := p.2 with hk
  set h : E 1 := (L v 1).symm k with hh
  set h₀ : E 0 := E.toBase 1 h with hh₀
  set k₀ : F 0 := F.toBase 1 k with hk₀
  have hvU : v ∈ Gv.U 1 := hp.1
  have hvh : ((v, h) : (ScBanach.paramProd G₀ E) 1) ∈ (Gv.prodFull E).U 1 := ⟨hvU, mem_univ _⟩
  have hΛp : famInv L ((ScBanach.paramProd G₀ F).toBase 1 p) = h₀ := by
    rw [ScBanach.paramProd_toBase, famInv_apply, hh₀, hh]
    exact ((L v).symm.toBase_comm 1 k).symm
  have hΦvh : famMap L ((ScBanach.paramProd G₀ E).toBase 1 (v, h)) = k₀ := by
    rw [ScBanach.paramProd_toBase, famMap_apply, hk₀, hh]
    change L v 0 (E.toBase 1 ((L v).symm 1 k)) = _
    rw [(L v).symm.toBase_comm 1 k]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  have hLh₀ : ∀ v' : G₀, famMap L ((ScBanach.paramProd G₀ E).toBase 1 (v', h)) = L v' 0 h₀ := fun v' => by
    rw [ScBanach.paramProd_toBase, famMap_apply]
  -- the compact set `K = DΛ(p)(ι(B₁))`
  obtain ⟨K₀, hK₀, hK₀sub⟩ :=
    ((ScBanach.paramProd G₀ F).toBase_succ_isCompactOperator 0).image_closedBall_subset_compact 1
  set K : Set (E 0) := famInvDeriv L DΦ p '' K₀ with hK
  have hKc : IsCompact K := hK₀.image (famInvDeriv L DΦ p).continuous
  -- the function `Ψ(v', u) = L(v')u − L(v)u`, continuous on `V₀ × E₀`, zero on `{v} × E₀`
  have hΨ : ContinuousOn (fun q : G₀ × E 0 => famMap L (q.1, q.2) - famMap L (v, q.2))
      (Gv.U 0 ×ˢ univ) := by
    have h1 : ContinuousOn (famMap L) (Gv.U 0 ×ˢ univ) := hΦ1.isSc0.continuousOn_base
    refine ContinuousOn.sub (h1.congr fun q _ => rfl) (h1.comp
      (continuous_const.prodMk continuous_snd).continuousOn fun q hq => ⟨Gv.const_U_subset 1 hvU, mem_univ _⟩)
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  set ε' : ℝ := c * ε / 2 with hε'
  have hε'0 : 0 < ε' := by positivity
  -- (A) the remainder of `Φ` along `(δv, 0)`
  have hA := Asymptotics.isLittleO_iff.1 (hasFDerivWithinAt_iff_isLittleO.1
    (hΦ1.hasFDerivWithinAt (v, h) hvh)) hε'0
  have hσ : Tendsto (fun p' : (ScBanach.paramProd G₀ F) 1 => ((p'.1, h) : (ScBanach.paramProd G₀ E) 1))
      (𝓝[(Gv.prodFull F).U 1] p) (𝓝[(Gv.prodFull E).U 1] (v, h)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun p' hp' => ⟨hp'.1, mem_univ _⟩⟩
    exact ((continuous_fst.prodMk continuous_const).tendsto p).mono_left nhdsWithin_le_nhds
  have hA' := hσ.eventually hA
  -- (B) the uniform smallness of `(L(v) − L(v'))u` on `K`
  obtain ⟨δ, hδ, hδ'⟩ := exists_forall_norm_le_of_isCompact
    (Ψ := fun v' u => famMap L (v', u) - famMap L (v, u)) (Gv.const_U_subset 1 hvU) hKc hΨ
    (fun u _ => sub_self _) hε'0
  have hB : ∀ᶠ p' in 𝓝[(Gv.prodFull F).U 1] p, dist p' p < δ :=
    eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds p hδ)
  filter_upwards [hA', hB, eventually_mem_nhdsWithin] with p' hA hB hp'
  -- notation
  set v' : G₀ := p'.1 with hv'
  have hv'U : v' ∈ Gv.U 0 := Gv.const_U_subset 1 hp'.1
  set t : ℝ := ‖p' - p‖ with ht
  set Λ' : E 0 := famInv L ((ScBanach.paramProd G₀ F).toBase 1 p') with hΛ'
  set w : E 0 := famInvDeriv L DΦ p ((ScBanach.paramProd G₀ F).toBase 1 (p' - p)) with hw
  set δv : G₀ := v' - v with hδv
  set r : F 0 := famMap L ((ScBanach.paramProd G₀ E).toBase 1 (v', h)) -
    famMap L ((ScBanach.paramProd G₀ E).toBase 1 (v, h)) -
    DΦ (v, h) ((ScBanach.paramProd G₀ E).toBase 1 (((v', h) : (ScBanach.paramProd G₀ E) 1) - (v, h)))
    with hr
  have hsub : (((v', h) : (ScBanach.paramProd G₀ E) 1) - (v, h)) = (δv, 0) := by
    ext <;> simp [hδv]
  have hsubB : (ScBanach.paramProd G₀ E).toBase 1 (((v', h) : (ScBanach.paramProd G₀ E) 1) - (v, h)) =
      ((δv, 0) : (ScBanach.paramProd G₀ E) 0) := by
    rw [hsub, ScBanach.paramProd_toBase, map_zero]
  -- the bound on `r`
  have hr_le : ‖r‖ ≤ ε' * t := by
    refine hA.trans ?_
    rw [hsub, Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
    gcongr
    exact (norm_fst_le (p' - p)).trans_eq (by rfl)
  -- the identity for `w`
  have hpB : (ScBanach.paramProd G₀ F).toBase 1 (p' - p) =
      ((δv, F.toBase 1 p'.2 - k₀) : (ScBanach.paramProd G₀ F) 0) := by
    rw [ScBanach.paramProd_toBase, Prod.fst_sub, Prod.snd_sub, map_sub]
  have hLw : L v 0 w = (F.toBase 1 p'.2 - k₀) - DΦ (v, h) (δv, 0) := by
    rw [hw, hpB, famInvDeriv_apply]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  -- the key identity
  have hkey : Λ' - h₀ - w = (L v' 0).symm (L v 0 w - L v' 0 w) - (L v' 0).symm r := by
    apply (L v' 0).injective
    rw [map_sub, map_sub, map_sub, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply]
    have e1 : L v' 0 Λ' = F.toBase 1 p'.2 := by
      rw [hΛ', ScBanach.paramProd_toBase, famInv_apply]
      exact ContinuousLinearEquiv.apply_symm_apply _ _
    have e2 : L v' 0 h₀ = r + k₀ + DΦ (v, h) (δv, 0) := by
      rw [hr, hsubB, hLh₀, hΦvh]; abel
    rw [e1, e2, hLw]
    abel
  -- the bounds through `c`
  have hinv : ∀ z : F 0, ‖(L v' 0).symm z‖ ≤ c⁻¹ * ‖z‖ := fun z => by
    rw [le_inv_mul_iff₀ hc0]
    have := hcm v' hv'U ((L v' 0).symm z)
    rwa [ContinuousLinearEquiv.apply_symm_apply] at this
  -- `(L(v) − L(v'))w` is small
  have hΨw : ‖L v 0 w - L v' 0 w‖ ≤ ε' * t := by
    by_cases ht0 : t = 0
    · have : p' - p = 0 := norm_eq_zero.1 ht0
      have hw0 : w = 0 := by rw [hw, this, map_zero, map_zero]
      rw [hw0, map_zero, map_zero, sub_zero, norm_zero, ht0, mul_zero]
    have htpos : 0 < t := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ht0)
    set u : E 0 := t⁻¹ • w with hu
    have huK : u ∈ K := by
      refine ⟨(ScBanach.paramProd G₀ F).toBase 1 (t⁻¹ • (p' - p)), hK₀sub ⟨t⁻¹ • (p' - p), ?_, rfl⟩, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
          abs_of_pos htpos, inv_mul_cancel₀ htpos.ne']
      · rw [hu, hw, map_smul, map_smul]
    have hv'd : dist v' v < δ := by
      rw [hv', dist_eq_norm]
      refine (norm_fst_le (p' - p)).trans_lt ?_
      rw [← dist_eq_norm]; exact hB
    have hΨu := hδ' v' hv'U hv'd u huK
    simp only [famMap_apply] at hΨu
    have e : L v 0 w - L v' 0 w = -(t • (L v' 0 u - L v 0 u)) := by
      rw [hu, map_smul, map_smul, ← smul_sub, smul_smul, mul_inv_cancel₀ htpos.ne', one_smul,
        neg_sub]
    rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos, mul_comm]
    exact mul_le_mul_of_nonneg_right hΨu htpos.le
  -- conclusion
  have hfinal : ‖Λ' - h₀ - w‖ ≤ ε * t := by
    calc ‖Λ' - h₀ - w‖ ≤ ‖(L v' 0).symm (L v 0 w - L v' 0 w)‖ + ‖(L v' 0).symm r‖ := by
          rw [hkey]; exact norm_sub_le _ _
      _ ≤ c⁻¹ * ‖L v 0 w - L v' 0 w‖ + c⁻¹ * ‖r‖ := add_le_add (hinv _) (hinv _)
      _ ≤ c⁻¹ * (ε' * t) + c⁻¹ * (ε' * t) := by gcongr
      _ = ε * t := by rw [hε']; field_simp; ring
  change ‖famInv L ((ScBanach.paramProd G₀ F).toBase 1 p') -
    famInv L ((ScBanach.paramProd G₀ F).toBase 1 p) -
    famInvDeriv L DΦ p ((ScBanach.paramProd G₀ F).toBase 1 (p' - p))‖ ≤ ε * ‖p' - p‖
  rw [hΛp]
  exact hfinal

/-! ### The tangent map of `Λ` is sc⁰ -/

/-- `L(v)⁻¹` commutes with the base maps. -/
lemma ScIso.toBase_symm_apply (T : ScIso E F) (m : ℕ) (y : F m) :
    E.toBase m ((T m).symm y) = (T 0).symm (F.toBase m y) := T.symm.toBase_comm m y

section Tangent

variable {Gv : ScNbhdGerm (ScBanach.const G₀) Cg}
  {DΦ : (ScBanach.paramProd G₀ E) 1 → (ScBanach.paramProd G₀ E) 0 →L[ℝ] F 0}
  (hΦ1 : IsSc1GermWith (E := ScBanach.paramProd G₀ E) (F := F) (Gv.prodFull E) (famMap L) DΦ)
include hΦ1

variable (L) in
/-- The level-`m` value of the tangent map `TΛ` at `((v, k), (δv, δk))`:
`(Λ_{m+1}(v, k), Λ_m(v, δk − (TΦ)_m((v, Λ_{m+1}(v, k)), (δv, 0))₂))`. -/
def tangentFamInvValue (m : ℕ) (pq : (ScBanach.paramProd G₀ F).tangent m) : E.tangent m :=
  (levelMap (E := ScBanach.paramProd G₀ F) (F := E) (famInv L) (m + 1) pq.1,
    levelMap (E := ScBanach.paramProd G₀ F) (F := E) (famInv L) m
      ((pq.1.1, pq.2.2 -
        (levelMap (E := (ScBanach.paramProd G₀ E).tangent) (F := F.tangent)
          (tangentMapWith (famMap L) DΦ) m
          ((((pq.1.1, levelMap (E := ScBanach.paramProd G₀ F) (F := E) (famInv L) (m + 1) pq.1) :
            (ScBanach.paramProd G₀ E) (m + 1)),
            ((pq.2.1, 0) : (ScBanach.paramProd G₀ E) m)) : (ScBanach.paramProd G₀ E).tangent m)).2) :
        (ScBanach.paramProd G₀ F) m))

lemma toBase_tangentFamInvValue (hc : ∀ m, ∃ c > 0, ∀ v ∈ Gv.U 0, ∀ h : E m, c * ‖h‖ ≤ ‖L v m h‖)
    (m : ℕ) {pq : (ScBanach.paramProd G₀ F).tangent m} (hpq : pq ∈ (Gv.prodFull F).tangent.U m) :
    E.tangent.toBase m (tangentFamInvValue L (DΦ := DΦ) m pq) =
      tangentMapWith (famInv L) (famInvDeriv L DΦ) ((ScBanach.paramProd G₀ F).tangent.toBase m pq) := by
  have hΛ0 := famInv_isSc0Germ hΦ1.isSc0 hc
  have hp1 : pq.1 ∈ (Gv.prodFull F).U (m + 1) := hpq.1
  set hm : E (m + 1) := levelMap (E := ScBanach.paramProd G₀ F) (F := E) (famInv L) (m + 1) pq.1
    with hhm
  have hY : ((((pq.1.1, hm) : (ScBanach.paramProd G₀ E) (m + 1)),
      ((pq.2.1, 0) : (ScBanach.paramProd G₀ E) m)) : (ScBanach.paramProd G₀ E).tangent m) ∈
      (Gv.prodFull E).tangent.U m := ⟨⟨hpq.1.1, mem_univ _⟩, mem_univ _⟩
  have hX := hΦ1.tangent_isSc0.toBase_levelMap hY
  rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase] at hX
  simp only [tangentMapWith] at hX
  have hX2 := congrArg Prod.snd hX
  simp only at hX2
  rw [ScBanach.paramProd_shift_toBase, ScBanach.paramProd_toBase, map_zero] at hX2
  -- the shifted base map of `Λ_{m+1}`
  have hshift : E.shift.toBase m hm = (L pq.1.1 1).symm (F.shift.toBase m pq.1.2) := by
    rw [hhm, ← IsSc1GermWith.levelMap_shift_toBase hΛ0 hp1, levelMap_famInv, ScBanach.paramProd_shift_toBase]
  have hz : ((pq.1.1, pq.2.2 - (levelMap (E := (ScBanach.paramProd G₀ E).tangent) (F := F.tangent)
      (tangentMapWith (famMap L) DΦ) m
      ((((pq.1.1, hm) : (ScBanach.paramProd G₀ E) (m + 1)),
        ((pq.2.1, 0) : (ScBanach.paramProd G₀ E) m)) : (ScBanach.paramProd G₀ E).tangent m)).2) :
      (ScBanach.paramProd G₀ F) m) ∈ (Gv.prodFull F).U m :=
    ⟨Gv.const_U_succ_subset m hpq.1.1, mem_univ _⟩
  rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase]
  simp only [tangentFamInvValue, tangentMapWith]
  refine Prod.ext ?_ ?_
  · exact (IsSc1GermWith.levelMap_shift_toBase hΛ0 hp1).symm
  · show E.toBase m (levelMap (E := ScBanach.paramProd G₀ F) (F := E) (famInv L) m _) = _
    rw [hΛ0.toBase_levelMap hz, ScBanach.paramProd_toBase, famInv_apply, famInvDeriv_apply,
      ScBanach.paramProd_shift_toBase, ScBanach.paramProd_toBase]
    simp only
    rw [map_sub, hX2, hshift]

/-- The level-`m` map of `TΛ` on the tangent germ. -/
lemma levelMap_tangentMapWith_famInv
    (hc : ∀ m, ∃ c > 0, ∀ v ∈ Gv.U 0, ∀ h : E m, c * ‖h‖ ≤ ‖L v m h‖) (m : ℕ)
    {pq : (ScBanach.paramProd G₀ F).tangent m} (hpq : pq ∈ (Gv.prodFull F).tangent.U m) :
    levelMap (E := (ScBanach.paramProd G₀ F).tangent) (F := E.tangent)
      (tangentMapWith (famInv L) (famInvDeriv L DΦ)) m pq = tangentFamInvValue L (DΦ := DΦ) m pq :=
  levelMap_eq_of_toBase_eq (toBase_tangentFamInvValue hΦ1 hc m hpq)

/-- The tangent map `TΛ((v, k), (δv, δk)) = (Λ(v, k), DΛ(v, k)(δv, δk))` is an sc⁰-germ on the
tangent germ of `V ⊕ F`: on level `m` it is
`(Λ_{m+1}(v, k), Λ_m(v, δk − (TΦ)_m((v, Λ_{m+1}(v, k)), (δv, 0))₂))`, a composition of the
continuous level maps of `Λ` and `TΦ`. -/
theorem famInv_tangent_isSc0 (hc : ∀ m, ∃ c > 0, ∀ v ∈ Gv.U 0, ∀ h : E m, c * ‖h‖ ≤ ‖L v m h‖) :
    IsSc0Germ (E := (ScBanach.paramProd G₀ F).tangent) (F := E.tangent) (Gv.prodFull F).tangent
      (tangentMapWith (famInv L) (famInvDeriv L DΦ)) := by
  have hΛ0 := famInv_isSc0Germ hΦ1.isSc0 hc
  refine ⟨fun m pq hpq => ⟨_, toBase_tangentFamInvValue hΦ1 hc m hpq⟩, fun m => ?_⟩
  refine ContinuousOn.congr (f := fun pq => tangentFamInvValue L (DΦ := DΦ) m pq) ?_
    fun pq hpq => levelMap_tangentMapWith_famInv hΦ1 hc m hpq
  have hY : ContinuousOn (fun pq : (ScBanach.paramProd G₀ F).tangent m =>
      ((((pq.1.1, levelMap (E := ScBanach.paramProd G₀ F) (F := E) (famInv L) (m + 1) pq.1) :
        (ScBanach.paramProd G₀ E) (m + 1)),
        ((pq.2.1, 0) : (ScBanach.paramProd G₀ E) m)) : (ScBanach.paramProd G₀ E).tangent m))
      ((Gv.prodFull F).tangent.U m) := by
    refine ContinuousOn.prodMk (ContinuousOn.prodMk (continuous_fst.fst.continuousOn) ?_)
      (continuous_snd.fst.prodMk continuous_const).continuousOn
    exact (hΛ0.continuousOn (m + 1)).comp continuous_fst.continuousOn fun pq hpq => hpq.1
  have hYmaps : MapsTo (fun pq : (ScBanach.paramProd G₀ F).tangent m =>
      ((((pq.1.1, levelMap (E := ScBanach.paramProd G₀ F) (F := E) (famInv L) (m + 1) pq.1) :
        (ScBanach.paramProd G₀ E) (m + 1)),
        ((pq.2.1, 0) : (ScBanach.paramProd G₀ E) m)) : (ScBanach.paramProd G₀ E).tangent m))
      ((Gv.prodFull F).tangent.U m) ((Gv.prodFull E).tangent.U m) :=
    fun pq hpq => ⟨⟨hpq.1.1, mem_univ _⟩, mem_univ _⟩
  have hTΦ := ((hΦ1.tangent_isSc0.continuousOn m).comp hY hYmaps).snd
  refine ContinuousOn.prodMk ?_ ?_
  · exact (hΛ0.continuousOn (m + 1)).comp continuous_fst.continuousOn fun pq hpq => hpq.1
  · exact (hΛ0.continuousOn m).comp (ContinuousOn.prodMk continuous_fst.fst.continuousOn
      (continuous_snd.snd.continuousOn.sub hTΦ))
      fun pq hpq => ⟨Gv.const_U_succ_subset m hpq.1.1, mem_univ _⟩

end Tangent

/-- **Lemma 3.61, the sc¹ part**: `Λ(v, k) = L(v)⁻¹k` is an sc¹-germ on `V ⊕ F` with the
derivative family `DΛ(v, k)(δv, δk) = L(v)⁻¹(δk − D₁Φ(v, L(v)⁻¹k)δv)`. -/
theorem famInv_isSc1GermWith {Gv : ScNbhdGerm (ScBanach.const G₀) Cg}
    {DΦ : (ScBanach.paramProd G₀ E) 1 → (ScBanach.paramProd G₀ E) 0 →L[ℝ] F 0}
    (hΦ1 : IsSc1GermWith (E := ScBanach.paramProd G₀ E) (F := F) (Gv.prodFull E) (famMap L) DΦ)
    (hc : ∀ m, ∃ c > 0, ∀ v ∈ Gv.U 0, ∀ h : E m, c * ‖h‖ ≤ ‖L v m h‖) :
    IsSc1GermWith (E := ScBanach.paramProd G₀ F) (F := E) (Gv.prodFull F) (famInv L)
      (famInvDeriv L DΦ) where
  isSc0 := famInv_isSc0Germ hΦ1.isSc0 hc
  hasFDerivWithinAt _ hp := famInv_hasFDerivWithinAt hΦ1 hc hp
  tangent_isSc0 := famInv_tangent_isSc0 hΦ1 hc

/-! ### Lemma 3.61: `Λ` is sc-smooth -/

section Induction

variable (G₀) in
/-- `((v, k), (δv, δk)) ↦ v` as an sc-operator `T(V ⊕ X) → G`. -/
def tangentBaseOp (X : ScBanach) :
    ScOperator (ScBanach.paramProd G₀ X).tangent (ScBanach.const G₀) where
  lvl m := (ContinuousLinearMap.fst ℝ G₀ (X (m + 1))).comp
    (ContinuousLinearMap.fst ℝ ((ScBanach.paramProd G₀ X) (m + 1)) ((ScBanach.paramProd G₀ X) m))
  incl_comm _ _ := rfl

variable (G₀) in
/-- `((v, k), (δv, δk)) ↦ (δv, 0)` as an sc-operator `T(V ⊕ X) → V ⊕ Y`. -/
def tangentInlOp (X Y : ScBanach) :
    ScOperator (ScBanach.paramProd G₀ X).tangent (ScBanach.paramProd G₀ Y) where
  lvl m := (ContinuousLinearMap.inl ℝ G₀ (Y m)).comp ((ContinuousLinearMap.fst ℝ G₀ (X m)).comp
    (ContinuousLinearMap.snd ℝ ((ScBanach.paramProd G₀ X) (m + 1)) ((ScBanach.paramProd G₀ X) m)))
  incl_comm m x := by
    change ((x.2.1, Y.incl m 0) : (ScBanach.paramProd G₀ Y) m) = (x.2.1, 0)
    rw [map_zero]

variable (G₀) in
/-- `((v, k), (δv, δk)) ↦ δk` as an sc-operator `T(V ⊕ X) → X`. -/
def tangentFiberOp (X : ScBanach) : ScOperator (ScBanach.paramProd G₀ X).tangent X where
  lvl m := (ContinuousLinearMap.snd ℝ G₀ (X m)).comp
    (ContinuousLinearMap.snd ℝ ((ScBanach.paramProd G₀ X) (m + 1)) ((ScBanach.paramProd G₀ X) m))
  incl_comm _ _ := rfl

/-- Subtraction `Y ⊕ Y → Y` as an sc-operator. -/
def ScBanach.subOp (Y : ScBanach) : ScOperator (Y.prod Y) Y where
  lvl m := ContinuousLinearMap.fst ℝ (Y m) (Y m) - ContinuousLinearMap.snd ℝ (Y m) (Y m)
  incl_comm m x := by
    change Y.incl m (x.1 - x.2) = Y.incl m x.1 - Y.incl m x.2
    exact map_sub _ _ _

variable (hC : IsPartialQuadrant (ScBanach.const G₀) Cg)
include hC

/-- **Lemma 3.61 by induction on `k`**: if `Φ(v, h) = L(v)h` is an sc^k-germ on `V ⊕ E`, then
`Λ(v, k) = L(v)⁻¹k` is an sc^k-germ on `V ⊕ F`.  The induction step: `Λ` is sc¹ with derivative
`DΛ`, and its tangent map `TΛ((v, k), (δv, δk)) = (Λ(v, k), L(v)⁻¹(δk − D₁Φ(v, Λ(v, k))δv))` is
the pair of `Λ¹ ∘ pr₁` and `Λ ∘ Θ`, `Θ((v, k), (δv, δk)) = (v, δk − (TΦ((v, Λ(v, k)), (δv, 0)))₂)`,
a composition of `Λ` (sc^k by induction), `TΦ` (sc^k) and sc-operators. -/
theorem famInv_isSckGerm {Gv : ScNbhdGerm (ScBanach.const G₀) Cg}
    (hc : ∀ m, ∃ c > 0, ∀ v ∈ Gv.U 0, ∀ h : E m, c * ‖h‖ ≤ ‖L v m h‖) :
    ∀ k, IsSckGerm k (E := ScBanach.paramProd G₀ E) (F := F) (Gv.prodFull E) (famMap L) →
      IsSckGerm k (E := ScBanach.paramProd G₀ F) (F := E) (Gv.prodFull F) (famInv L)
  | 0, hΦ => famInv_isSc0Germ hΦ hc
  | k + 1, hΦ => by
    have hCE : IsQuadrantLike (ScBanach.paramProd G₀ E) (Cg ×ˢ univ) :=
      (hC.prod_univ E).isQuadrantLike
    have hCF : IsQuadrantLike (ScBanach.paramProd G₀ F) (Cg ×ˢ univ) :=
      (hC.prod_univ F).isQuadrantLike
    have hCEt := hCE.tangentSet
    have hCFt := hCF.tangentSet
    have hCFs := hCF.shift
    set DΦ := scDerivGerm (E := ScBanach.paramProd G₀ E) (F := F) (Gv.prodFull E) (famMap L)
      with hDΦ
    have hΦ1 : IsSc1GermWith (E := ScBanach.paramProd G₀ E) (F := F) (Gv.prodFull E) (famMap L) DΦ :=
      hΦ.1.isSc1GermWith_scDerivGerm
    have hTΦ : IsSckGerm k (E := (ScBanach.paramProd G₀ E).tangent) (F := F.tangent)
        (Gv.prodFull E).tangent (tangentMapWith (famMap L) DΦ) := hΦ.2
    have hΛk := famInv_isSckGerm hc k hΦ.of_succ
    have hΛ1 := famInv_isSc1GermWith hΦ1 hc
    refine ⟨hΛ1.isSc1Germ, ?_⟩
    -- the projection `T(V ⊕ F) → (V ⊕ F)¹`
    have hfst : (Gv.prodFull F).tangent.MapsToGerm (Gv.prodFull F).shift
        ((ScBanach.fstOp (ScBanach.paramProd G₀ F).shift (ScBanach.paramProd G₀ F)) 0) :=
      fun m pq hpq => by rw [ScOperator.levelMap_eq]; exact hpq.1
    -- `f = Λ¹ ∘ pr₁`
    have hf : IsSckGerm k (E := (ScBanach.paramProd G₀ F).tangent) (F := E.shift)
        (Gv.prodFull F).tangent
        (levelMap (E := ScBanach.paramProd G₀ F) (F := E) (famInv L) 1 ∘
          (ScBanach.fstOp (ScBanach.paramProd G₀ F).shift (ScBanach.paramProd G₀ F)) 0) :=
      IsSckGerm.comp hCFt hCFs (hΛk.shift hCF) ((ScBanach.fstOp _ _).isSckGerm k _ hCFt) hfst
    -- `ξ₁ = (pr₁, Λ)¹ ∘ pr₁ : T(V ⊕ F) → (V ⊕ E)¹`
    have hpair : IsSckGerm k (E := ScBanach.paramProd G₀ F) (F := ScBanach.paramProd G₀ E)
        (Gv.prodFull F) (pairMap ((ScBanach.fstOp (ScBanach.const G₀) F) 0) (famInv L)) :=
      IsSckGerm.pair hCF ((ScBanach.fstOp _ _).isSckGerm k _ hCF) hΛk
    have hξ₁ : IsSckGerm k (E := (ScBanach.paramProd G₀ F).tangent)
        (F := (ScBanach.paramProd G₀ E).shift) (Gv.prodFull F).tangent
        (levelMap (E := ScBanach.paramProd G₀ F) (F := ScBanach.paramProd G₀ E)
          (pairMap ((ScBanach.fstOp (ScBanach.const G₀) F) 0) (famInv L)) 1 ∘
          (ScBanach.fstOp (ScBanach.paramProd G₀ F).shift (ScBanach.paramProd G₀ F)) 0) :=
      IsSckGerm.comp hCFt hCFs (hpair.shift hCF) ((ScBanach.fstOp _ _).isSckGerm k _ hCFt) hfst
    -- `Ξ = (ξ₁, (δv, 0)) : T(V ⊕ F) → T(V ⊕ E)`
    set Ξ : (ScBanach.paramProd G₀ F).tangent 0 → (ScBanach.paramProd G₀ E).tangent 0 :=
      pairMap (E := (ScBanach.paramProd G₀ F).tangent) (F := (ScBanach.paramProd G₀ E).shift)
        (G := ScBanach.paramProd G₀ E)
        (levelMap (E := ScBanach.paramProd G₀ F) (F := ScBanach.paramProd G₀ E)
          (pairMap ((ScBanach.fstOp (ScBanach.const G₀) F) 0) (famInv L)) 1 ∘
          (ScBanach.fstOp (ScBanach.paramProd G₀ F).shift (ScBanach.paramProd G₀ F)) 0)
        ((tangentInlOp G₀ F E) 0) with hΞ
    have hΞk : IsSckGerm k (E := (ScBanach.paramProd G₀ F).tangent)
        (F := (ScBanach.paramProd G₀ E).tangent) (Gv.prodFull F).tangent Ξ :=
      IsSckGerm.pair hCFt hξ₁ ((tangentInlOp G₀ F E).isSckGerm k _ hCFt)
    have hξ₁val : ∀ pq ∈ (Gv.prodFull F).tangent.U 0,
        levelMap (E := ScBanach.paramProd G₀ F) (F := ScBanach.paramProd G₀ E)
          (pairMap ((ScBanach.fstOp (ScBanach.const G₀) F) 0) (famInv L)) 1 pq.1 =
          ((pq.1.1, levelMap (E := ScBanach.paramProd G₀ F) (F := E) (famInv L) 1 pq.1) :
            (ScBanach.paramProd G₀ E) 1) := fun pq hpq => by
      rw [IsSc0Germ.levelMap_pair ((ScBanach.fstOp _ _).isSc0Germ _) hΛ1.isSc0 hpq.1,
        ScOperator.levelMap_eq]
      rfl
    have hΞmaps : (Gv.prodFull F).tangent.MapsToGerm (Gv.prodFull E).tangent Ξ := by
      intro m pq hpq
      rw [hΞ, IsSc0Germ.levelMap_pair hξ₁.isSc0 ((tangentInlOp G₀ F E).isSc0Germ _) hpq,
        ScNbhdGerm.mem_tangent_U]
      have h1 := IsSc0Germ.levelMap_comp (hpair.shift hCF).isSc0 ((ScBanach.fstOp _ _).isSc0Germ _)
        hfst hpq
      dsimp only
      rw [h1, ScOperator.levelMap_eq, ScBanach.fstOp_apply, IsSc0Germ.levelMap_shift hpair.isSc0 hpq.1,
        IsSc0Germ.levelMap_pair ((ScBanach.fstOp _ _).isSc0Germ _) hΛ1.isSc0 hpq.1,
        ScOperator.levelMap_eq]
      exact ⟨hpq.1.1, mem_univ _⟩
    -- `θ₂ = δk − (TΦ ∘ Ξ)₂`
    set θ₂ : (ScBanach.paramProd G₀ F).tangent 0 → F 0 :=
      F.subOp 0 ∘ pairMap (E := (ScBanach.paramProd G₀ F).tangent) (F := F) (G := F)
        ((tangentFiberOp G₀ F) 0)
        ((ScBanach.sndOp F.shift F) 0 ∘ (tangentMapWith (famMap L) DΦ ∘ Ξ)) with hθ₂
    have hθ₂k : IsSckGerm k (E := (ScBanach.paramProd G₀ F).tangent) (F := F)
        (Gv.prodFull F).tangent θ₂ :=
      IsSckGerm.operator_comp hCFt _ (IsSckGerm.pair hCFt ((tangentFiberOp G₀ F).isSckGerm k _ hCFt)
        (IsSckGerm.operator_comp hCFt _ (IsSckGerm.comp hCFt hCEt hTΦ hΞk hΞmaps)))
    -- `Θ = (v, θ₂) : T(V ⊕ F) → V ⊕ F`
    set Θ : (ScBanach.paramProd G₀ F).tangent 0 → (ScBanach.paramProd G₀ F) 0 :=
      pairMap (E := (ScBanach.paramProd G₀ F).tangent) (F := ScBanach.const G₀) (G := F)
        ((tangentBaseOp G₀ F) 0) θ₂ with hΘ
    have hΘk : IsSckGerm k (E := (ScBanach.paramProd G₀ F).tangent) (F := ScBanach.paramProd G₀ F)
        (Gv.prodFull F).tangent Θ :=
      IsSckGerm.pair hCFt ((tangentBaseOp G₀ F).isSckGerm k _ hCFt) hθ₂k
    have hΘmaps : (Gv.prodFull F).tangent.MapsToGerm (Gv.prodFull F) Θ := fun m pq hpq => by
      rw [hΘ, IsSc0Germ.levelMap_pair ((tangentBaseOp G₀ F).isSc0Germ _) hθ₂k.isSc0 hpq]
      refine ⟨?_, mem_univ _⟩
      rw [ScOperator.levelMap_eq]
      exact Gv.const_U_succ_subset m hpq.1.1
    -- `g = Λ ∘ Θ`
    have hg : IsSckGerm k (E := (ScBanach.paramProd G₀ F).tangent) (F := E)
        (Gv.prodFull F).tangent (famInv L ∘ Θ) :=
      IsSckGerm.comp hCFt hCF hΛk hΘk hΘmaps
    -- `TΛ = (f, g)` on the tangent germ
    have hT : IsSckGerm k (E := (ScBanach.paramProd G₀ F).tangent) (F := E.tangent)
        (Gv.prodFull F).tangent
        (pairMap (E := (ScBanach.paramProd G₀ F).tangent) (F := E.shift) (G := E)
          (levelMap (E := ScBanach.paramProd G₀ F) (F := E) (famInv L) 1 ∘
            (ScBanach.fstOp (ScBanach.paramProd G₀ F).shift (ScBanach.paramProd G₀ F)) 0)
          (famInv L ∘ Θ)) :=
      IsSckGerm.pair hCFt hf hg
    refine IsSckGerm.congr hCFt ?_ hT
    intro pq hpq
    rw [IsSc1Germ.tangentMapGerm_eqOn hCF hΛ1 hpq]
    show (levelMap (E := ScBanach.paramProd G₀ F) (F := E) (famInv L) 1 pq.1, famInv L (Θ pq)) =
      (levelMap (E := ScBanach.paramProd G₀ F) (F := E) (famInv L) 1 pq.1,
        famInvDeriv L DΦ pq.1 pq.2)
    congr 1
    rw [famInvDeriv_apply]
    show (L pq.1.1 0).symm (pq.2.2 - (tangentMapWith (famMap L) DΦ (Ξ pq)).2) = _
    rw [hΞ]
    show (L pq.1.1 0).symm (pq.2.2 - DΦ (levelMap (E := ScBanach.paramProd G₀ F)
      (F := ScBanach.paramProd G₀ E) (pairMap ((ScBanach.fstOp (ScBanach.const G₀) F) 0) (famInv L)) 1
        pq.1) (pq.2.1, 0)) = _
    rw [hξ₁val pq hpq, levelMap_famInv]

/-- **Lemma 3.61** ([25, Proposition 4.8]): let `V` be a germ of relatively open neighbourhoods of
`0` in a partial quadrant `C̃` of the finite-dimensional space `G`, and `v ↦ L(v)` a family of
sc-isomorphisms `E → F` such that (ii) `(v, h) ↦ L(v)h` is sc-smooth on `V ⊕ E` and (iii) for
every `m` there is `c_m > 0` with `|L(v)h|_m ≥ c_m |h|_m` for `v ∈ V`, `h ∈ E_m`.  Then
`(v, k) ↦ L(v)⁻¹k` is sc-smooth on `V ⊕ F`.  (The operators `v ↦ L(v)` need not depend
continuously on `v` in the operator norm.) -/
theorem lemma_3_61 {Gv : ScNbhdGerm (ScBanach.const G₀) Cg}
    (hΦ : IsScSmoothGerm (E := ScBanach.paramProd G₀ E) (F := F) (Gv.prodFull E) (famMap L))
    (hc : ∀ m, ∃ c > 0, ∀ v ∈ Gv.U 0, ∀ h : E m, c * ‖h‖ ≤ ‖L v m h‖) :
    IsScSmoothGerm (E := ScBanach.paramProd G₀ F) (F := E) (Gv.prodFull F) (famInv L) :=
  fun k => famInv_isSckGerm hC hc k (hΦ k)

end Induction

end Polyfold
