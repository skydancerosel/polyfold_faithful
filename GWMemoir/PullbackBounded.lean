import GWMemoir.FibreInstance

/-!
# The change of coordinates for the fibres of `W`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §1.2 (p. 7) and §2.4
(p. 51), with the fibre spaces of `GWMemoir.Fibres` and the named proposition `PullbackBounded`
of `GWMemoir.FibreInstance`: for an isomorphism `f : α → β` and atlases `A` of `α`, `B` of `β`,
`ξ ↦ f^* ξ` is bounded between the fibre spaces.  It changes the charts of `S` and the
trivializations of `u*TQ` in `H^{2,δ₀}`.

## What is formalized

* `SectionAtlas.toConst`: an atlas for one map is an atlas for every constant map (the condition
  on the map is `u(y)` in the chart of `Q` at `u(zᵢ)`); `atConst B q`.
* **The change of the trivialization of `u*TQ`** in the blocks: `blockOp B L`, `L : E → E`
  applied to the `E`-coordinates of every block, with `blockOp_comp`, `blockOp_id`, linear and
  continuous in `L` (`continuous_blockOpAt`).  `isFormRep_mapForm`: for one atlas read at two
  constant maps, the representatives of `L ∘ ξ` are `blockOp L` of those of `ξ`.
  `blockOp_mem_fibreSpace`: an `L` with `L J(q) = J(q') L` maps the fibre at `q` into the fibre at
  `q'`.
* **`pullbackBounded_of_blockMap`**: `PullbackBounded` reduces to a bounded operator between the
  block spaces mapping the representatives of the anti-linear forms in `B` to those of their
  pull-backs in `A`.
## Readings

* For two atlases of one map from `sphere3`, `PullbackBounded J δs h0 hmono A B (Iso.refl _)`
  needs, besides `blockOp` for the change of trivialization, the invariance of `H^{2,δ}` under
  the change of disc charts: `v ↦ c · (v ∘ ψ)` bounded for `ψ` a diffeomorphism near the compact
  support of a smooth `c`, with a smooth partition of unity on `S²` subordinate to the discs of
  `B` and the smoothness of the stereographic transitions.  This part is not formalized.
* For a general surface without nodes, a `SectionAtlas` asks the disc charts on the open discs
  `r² < 1/8` only.  The representatives `β · (ξ in the chart)` of a smooth form are in `H^2` when
  the chart extends over the closed disc, which holds on `sphere3` (the chart targets are `ℝ²`);
  an atlas whose discs fill the chart targets may
  give representatives outside `H^2`, so `AllPullbackBounded` for arbitrary atlases needs this
  extension as a hypothesis.
* The fibre functor on the constant maps does not need a change of atlas: the atlas `constAt` of
  `GWMemoir.ConstantBundle` is one atlas of `sphere3` read at every constant map.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-! ## 1. Atlases of constant maps -/

section Atlas

variable {m : ℕ} {X : NodalSurface m}

/-- An atlas for a map `u` is an atlas for every constant map: the conditions on the map ask
`u(y)` in the chart of `Q` at `u(zᵢ)`, which holds for a constant map. -/
def SectionAtlas.toConst {u : X.S → Q} (A : SectionAtlas (E := E) X u) (u' : X.S → Q)
    (hu' : ∀ x y, u' x = u' y) : SectionAtlas (E := E) X u' where
  nd := A.nd
  center := A.center
  ε := A.ε
  ε_pos := A.ε_pos
  disc_chart i p hp := ⟨(A.disc_chart i p hp).1, by
    rw [hu' (X.discPt (A.center i) (A.ε i) p) (A.center i)]
    exact mem_extChartAt_source (I := 𝓘(ℝ, E)) _⟩
  disc_avoid := A.disc_avoid
  nn := A.nn
  node := A.node
  hol := A.hol
  s0 := A.s0
  isHol := A.isHol
  neck_chart j p hp := ⟨(A.neck_chart j p hp).1, by
    rw [hu' (X.polar (A.hol j) p) (A.node j)]
    exact mem_extChartAt_source (I := 𝓘(ℝ, E)) _⟩
  node_nodal := A.node_nodal
  nodal_node := A.nodal_node
  cover := A.cover

/-- For a constant map the chart of `Q` does not move: `formAt` is `ξ(y) ∘ T_{z,y}`. -/
lemma formAt_const (q : Q) (z : X.S) (ξ : Form E X) (y : X.S) :
    formAt (fun _ : X.S => q) z ξ y = (ξ y).comp (tangentCoordChange 𝓘(ℝ, E2) z y y) := by
  ext v
  simp only [formAt, ContinuousLinearMap.comp_apply]
  exact tangentCoordChange_self (mem_extChartAt_source q)

end Atlas

/-! ## 2. Mixing the coordinates of `E` in the blocks -/

section Mix

/-- The matrix of `L` in the fixed basis of `E`. -/
def mat (L : E →L[ℝ] E) (k k' : Fin (Module.finrank ℝ E)) : ℝ :=
  crd k (L (Module.finBasis ℝ E k'))

lemma crd_apply_clm (L : E →L[ℝ] E) (k : Fin (Module.finrank ℝ E)) (w : E) :
    crd k (L w) = ∑ k', mat L k k' * crd k' w := by
  conv_lhs => rw [← (Module.finBasis ℝ E).sum_repr w]
  simp only [map_sum, map_smul, smul_eq_mul, mat, crd, Module.Basis.coord_apply]
  exact Finset.sum_congr rfl fun k' _ => mul_comm _ _

lemma mat_comp (L L' : E →L[ℝ] E) (k k'' : Fin (Module.finrank ℝ E)) :
    mat (L.comp L') k k'' = ∑ k', mat L k k' * mat L' k' k'' := by
  rw [mat, ContinuousLinearMap.comp_apply, crd_apply_clm]; rfl

lemma mat_id (k k' : Fin (Module.finrank ℝ E)) :
    mat (ContinuousLinearMap.id ℝ E) k k' = if k = k' then 1 else 0 := by
  simp only [mat, ContinuousLinearMap.id_apply, crd, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : k = k' <;> simp [h, eq_comm]

lemma mat_add (L L' : E →L[ℝ] E) (k k') : mat (L + L') k k' = mat L k k' + mat L' k k' := by
  simp [mat]

lemma mat_smul (c : ℝ) (L : E →L[ℝ] E) (k k') : mat (c • L) k k' = c * mat L k k' := by
  simp [mat]

variable {ι : Type} {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `L` acting on the last index: `(w_{p,k})_k ↦ (∑_{k'} L_{kk'} w_{p,k'})_k`. -/
def mixLast (L : E →L[ℝ] E) :
    (ι × Fin (Module.finrank ℝ E) → G) →L[ℝ] (ι × Fin (Module.finrank ℝ E) → G) :=
  ContinuousLinearMap.pi fun p => ∑ k', mat L p.2 k' • ContinuousLinearMap.proj (p.1, k')

lemma mixLast_apply (L : E →L[ℝ] E) (w : ι × Fin (Module.finrank ℝ E) → G) (p) :
    mixLast L w p = ∑ k', mat L p.2 k' • w (p.1, k') := by
  simp [mixLast]

lemma mixLast_comp (L L' : E →L[ℝ] E) (w : ι × Fin (Module.finrank ℝ E) → G) :
    mixLast (L.comp L') w = mixLast L (mixLast L' w) := by
  funext p
  simp only [mixLast_apply, mat_comp, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

lemma mixLast_id (w : ι × Fin (Module.finrank ℝ E) → G) :
    mixLast (ContinuousLinearMap.id ℝ E) w = w := by
  funext p
  simp only [mixLast_apply, mat_id, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

lemma mixLast_add (L L' : E →L[ℝ] E) (w : ι × Fin (Module.finrank ℝ E) → G) :
    mixLast (L + L') w = mixLast L w + mixLast L' w := by
  funext p
  simp only [mixLast_apply, mat_add, add_smul, Finset.sum_add_distrib, Pi.add_apply]

lemma mixLast_smul (c : ℝ) (L : E →L[ℝ] E) (w : ι × Fin (Module.finrank ℝ E) → G) :
    mixLast (c • L) w = c • mixLast L w := by
  funext p
  simp only [mixLast_apply, mat_smul, Pi.smul_apply, Finset.smul_sum, smul_smul]

/-- `L` acting on the last index of a disc block:
`(w_{i,d,k})_k ↦ (∑_{k'} L_{kk'} w_{i,d,k'})_k`. -/
def mixDisc (L : E →L[ℝ] E) :
    (ι × Fin 2 × Fin (Module.finrank ℝ E) → G) →L[ℝ] (ι × Fin 2 × Fin (Module.finrank ℝ E) → G) :=
  ContinuousLinearMap.pi fun p => ∑ k', mat L p.2.2 k' • ContinuousLinearMap.proj (p.1, p.2.1, k')

lemma mixDisc_apply (L : E →L[ℝ] E) (w : ι × Fin 2 × Fin (Module.finrank ℝ E) → G) (p) :
    mixDisc L w p = ∑ k', mat L p.2.2 k' • w (p.1, p.2.1, k') := by
  simp [mixDisc]

lemma mixDisc_comp (L L' : E →L[ℝ] E) (w : ι × Fin 2 × Fin (Module.finrank ℝ E) → G) :
    mixDisc (L.comp L') w = mixDisc L (mixDisc L' w) := by
  funext p
  simp only [mixDisc_apply, mat_comp, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

lemma mixDisc_id (w : ι × Fin 2 × Fin (Module.finrank ℝ E) → G) :
    mixDisc (ContinuousLinearMap.id ℝ E) w = w := by
  funext p
  simp only [mixDisc_apply, mat_id, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

lemma mixDisc_add (L L' : E →L[ℝ] E) (w : ι × Fin 2 × Fin (Module.finrank ℝ E) → G) :
    mixDisc (L + L') w = mixDisc L w + mixDisc L' w := by
  funext p
  simp only [mixDisc_apply, mat_add, add_smul, Finset.sum_add_distrib, Pi.add_apply]

lemma mixDisc_smul (c : ℝ) (L : E →L[ℝ] E) (w : ι × Fin 2 × Fin (Module.finrank ℝ E) → G) :
    mixDisc (c • L) w = c • mixDisc L w := by
  funext p
  simp only [mixDisc_apply, mat_smul, Pi.smul_apply, Finset.smul_sum, smul_smul]

end Mix

section Blocks

variable {m : ℕ} {X : NodalSurface m} {u : X.S → Q} (A : SectionAtlas (E := E) X u)
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

/-- **The block operator of `L : E → E`**: `L` applied to the `E`-coordinates of every block. -/
def blockOp (L : E →L[ℝ] E) :
    (fibreBlocks A δ h0 hmono) 0 →L[ℝ] (fibreBlocks A δ h0 hmono) 0 :=
  ContinuousLinearMap.prodMap
    (mixDisc (ι := Fin A.nd) (G := H 2 (Neck.δ_nonneg δ h0 hmono 0)) L)
    (mixLast (ι := Fin A.nn) (G := H 2 (Neck.δ_nonneg δ h0 hmono 0)) L)

variable {A}

lemma fDiscBlock_blockOp (L : E →L[ℝ] E) (v : (fibreBlocks A δ h0 hmono) 0) (i d k) :
    fDiscBlock (blockOp A L v) i d k = ∑ k', mat L k k' • fDiscBlock v i d k' :=
  mixDisc_apply L v.1 (i, d, k)

lemma blockOp_comp (L L' : E →L[ℝ] E) (v : (fibreBlocks A δ h0 hmono) 0) :
    blockOp A (L.comp L') v = blockOp A L (blockOp A L' v) :=
  Prod.ext (mixDisc_comp L L' v.1) (mixLast_comp L L' v.2)

lemma blockOp_id (v : (fibreBlocks A δ h0 hmono) 0) :
    blockOp A (ContinuousLinearMap.id ℝ E) v = v :=
  Prod.ext (mixDisc_id v.1) (mixLast_id v.2)

variable (A) in
/-- `L ↦ blockOp L v`, a linear map on the finite-dimensional `E →L E`, hence continuous. -/
def blockOpAt (v : (fibreBlocks A δ h0 hmono) 0) :
    (E →L[ℝ] E) →ₗ[ℝ] (fibreBlocks A δ h0 hmono) 0 where
  toFun L := blockOp A L v
  map_add' L L' := Prod.ext (mixDisc_add L L' v.1) (mixLast_add L L' v.2)
  map_smul' c L := Prod.ext (mixDisc_smul c L v.1) (mixLast_smul c L v.2)

lemma continuous_blockOpAt (v : (fibreBlocks A δ h0 hmono) 0) :
    Continuous fun L : E →L[ℝ] E => blockOp A L v :=
  (blockOpAt A v).continuous_of_finiteDimensional

lemma blockOp_smul (c : ℝ) (L : E →L[ℝ] E) (v : (fibreBlocks A δ h0 hmono) 0) :
    blockOp A (c • L) v = c • blockOp A L v :=
  (blockOpAt A v).map_smul c L

end Blocks

/-! ## 3. Representatives under a change of the frame of `E` -/

section Rep

lemma val_sum_smul_ae {k : ℕ} {d : ℝ} {hd : 0 ≤ d} {ι : Type} (s : Finset ι) (c : ι → ℝ)
    (a : ι → H k hd) :
    (H.val (∑ i ∈ s, c i • a i) : ℝ × ℝ → ℝ) =ᵐ[cyl] fun x => ∑ i ∈ s, c i * H.val (a i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact val_zero_ae (k := k) (hd := hd)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    filter_upwards [val_add_ae (c j • a j) (∑ i ∈ s, c i • a i), val_smul_ae (c j) (a j), ih]
      with x h1 h2 h3
    rw [h1, h2, h3, Finset.sum_insert hj, smul_eq_mul]

variable {m : ℕ} {X : NodalSurface m} {u₀ : X.S → Q} (B : SectionAtlas (E := E) X u₀)
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}

/-- The atlas `B` for the constant map at `q`. -/
abbrev atConst (q : Q) : SectionAtlas (E := E) X (fun _ => q) :=
  B.toConst (fun _ => q) fun _ _ => rfl

/-- `L ∘ ξ`: the form `ξ` with `L` applied to its values. -/
def mapForm (L : E →L[ℝ] E) (ξ : Form E X) : Form E X := fun x => L.comp (ξ x)

/-- **The representatives of `L ∘ ξ` are `L` applied to those of `ξ`**, for one atlas read at two
constant maps. -/
theorem isFormRep_mapForm (hX : X.nodes = ∅) {q q' : Q} (L : E →L[ℝ] E) {ξ : Form E X}
    {v : (fibreBlocks B δ h0 hmono) 0}
    (h : IsFormRep (A := atConst B q) (δ := δ) (h0 := h0) (hmono := hmono) ξ v) :
    IsFormRep (A := atConst B q') (δ := δ) (h0 := h0) (hmono := hmono) (mapForm L ξ)
      (blockOp B L v) := by
  refine ⟨fun i d k => ?_, fun j k => ?_⟩
  · have hall : ∀ᵐ x ∂cyl, ∀ k', (H.val (fDiscBlock v i d k') : ℝ × ℝ → ℝ) x =
        formDiscRep (atConst B q) i d k' ξ x := ae_all_iff.2 fun k' => h.1 i d k'
    refine (EventuallyEq.of_eq (congrArg (fun a => ((H.val a : Lp ℝ 2 cyl) : ℝ × ℝ → ℝ))
      (fDiscBlock_blockOp (A := B) L v i d k))).trans ?_
    filter_upwards [val_sum_smul_ae Finset.univ (fun k' => mat L k k')
      (fun k' => fDiscBlock v i d k'), hall] with x h1 h2
    rw [h1]
    simp only [h2]
    simp only [formDiscRep, formAt_const, mapForm, ContinuousLinearMap.comp_apply]
    rw [crd_apply_clm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k' _ => by ring_nf; rfl
  · obtain ⟨p, hp, -⟩ := B.node_nodal j
    rw [hX] at hp
    exact absurd hp (notMem_empty p)

variable (J : AlmostComplexStructure E Q)

/-- An operator `L` with `L ∘ J(q) = J(q') ∘ L` maps the forms anti-linear for `J(q)` to forms
anti-linear for `J(q')`. -/
lemma IsAntiOff.mapForm {q q' : Q} {L : E →L[ℝ] E} (hL : L.comp (J.J q) = (J.J q').comp L)
    {ξ : Form E X} (h : IsAntiOff J X (fun _ => q) ξ) :
    IsAntiOff J X (fun _ => q') (mapForm L ξ) := by
  intro x hx
  have h1 := (NodalSurface.mem_antiLinearForms J X).1 (h x hx)
  refine (NodalSurface.mem_antiLinearForms J X).2 fun w => ?_
  have h2 := congrArg (fun T : E →L[ℝ] E => T (ξ x w)) hL
  simp only [ContinuousLinearMap.comp_apply] at h2
  change J.J q' (L (ξ x w)) = -(L (ξ x (X.j.J x w)))
  rw [← h2]
  exact (congrArg L (h1 w)).trans (map_neg L _)

variable {B J}

theorem blockOp_mem_formsSub (hX : X.nodes = ∅) {q q' : Q} {L : E →L[ℝ] E}
    (hL : L.comp (J.J q) = (J.J q').comp L) {v : (fibreBlocks B δ h0 hmono) 0}
    (hv : v ∈ formsSub J (atConst B q) δ h0 hmono) :
    blockOp B L v ∈ formsSub J (atConst B q') δ h0 hmono := by
  obtain ⟨ξ, ha, hr⟩ := hv
  exact ⟨mapForm L ξ, ha.mapForm J hL, isFormRep_mapForm B hX L hr⟩

/-- **An intertwining operator maps the fibre at `q` into the fibre at `q'`.** -/
theorem blockOp_mem_fibreSpace (hX : X.nodes = ∅) {q q' : Q} {L : E →L[ℝ] E}
    (hL : L.comp (J.J q) = (J.J q').comp L) {v : (fibreBlocks B δ h0 hmono) 0}
    (hv : v ∈ fibreSpace J (atConst B q) δ h0 hmono) :
    blockOp B L v ∈ fibreSpace J (atConst B q') δ h0 hmono := by
  have hc : IsClosed {w : (fibreBlocks (atConst B q) δ h0 hmono) 0 |
      blockOp B L w ∈ fibreSpace J (atConst B q') δ h0 hmono} :=
    (isClosed_fibreSpace J (atConst B q') δ h0 hmono).preimage (blockOp B L).continuous
  have hs : (formsSub J (atConst B q) δ h0 hmono : Set ((fibreBlocks (atConst B q) δ h0 hmono) 0))
      ⊆ {w | blockOp B L w ∈ fibreSpace J (atConst B q') δ h0 hmono} := fun w hw =>
    formsSub_le J _ δ h0 hmono (blockOp_mem_formsSub hX hL hw)
  have hv' : v ∈ closure (formsSub J (atConst B q) δ h0 hmono :
      Set ((fibreBlocks (atConst B q) δ h0 hmono) 0)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hv
  exact closure_minimal hs hc hv'

end Rep

/-! ## 4. Reduction of `PullbackBounded` to the blocks -/

section Reduction

variable (J : AlmostComplexStructure E Q) {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ}
  {δs : ℕ → ℝ} {h0 : 0 ≤ δs 0} {hmono : StrictMono δs}

/-- **`PullbackBounded` from a bounded operator on the blocks**: if `R` maps the representatives
in `B` of every form anti-linear off the nodes to the representatives in `A` of its pull-back,
then `R` restricts to the bounded operator `T` between the fibre spaces asked by
`PullbackBounded`. -/
theorem pullbackBounded_of_blockMap {α β : StableMap om m k δ}
    {A : SectionAtlas (E := E) α.dom α.u} {B : SectionAtlas (E := E) β.dom β.u} (f : α.Iso β)
    (R : (fibreBlocks B δs h0 hmono) 0 →L[ℝ] (fibreBlocks A δs h0 hmono) 0)
    (hR : ∀ (ξ : Form E β.dom) (v : (fibreBlocks B δs h0 hmono) 0), IsAntiOff J β.dom β.u ξ →
      IsFormRep (A := B) (δ := δs) (h0 := h0) (hmono := hmono) ξ v →
        IsFormRep (A := A) (δ := δs) (h0 := h0) (hmono := hmono) (f.φ.pullbackForm ξ) (R v)) :
    PullbackBounded J δs h0 hmono A B f := by
  have hsub : ∀ v ∈ formsSub J B δs h0 hmono, R v ∈ formsSub J A δs h0 hmono := by
    rintro v ⟨ξ, ha, hr⟩
    exact ⟨_, ha.pullback J f, hR ξ v ha hr⟩
  have hmem : ∀ v ∈ fibreSpace J B δs h0 hmono, R v ∈ fibreSpace J A δs h0 hmono := by
    intro v hv
    have hc : IsClosed {w : (fibreBlocks B δs h0 hmono) 0 | R w ∈ fibreSpace J A δs h0 hmono} :=
      (isClosed_fibreSpace J A δs h0 hmono).preimage R.continuous
    have hv' : v ∈ closure (formsSub J B δs h0 hmono : Set ((fibreBlocks B δs h0 hmono) 0)) := by
      rw [← Submodule.topologicalClosure_coe]; exact hv
    exact closure_minimal (fun w hw => show R w ∈ fibreSpace J A δs h0 hmono from
      formsSub_le J A δs h0 hmono (hsub w hw)) hc hv'
  refine ⟨(R.comp (fibreSpace J B δs h0 hmono).subtypeL).codRestrict _ fun v => hmem v v.2,
    fun ξ => ?_⟩
  exact hR ξ.1 _ ξ.2.1 (isFormRep_formRep ξ)

end Reduction

end GWMemoir
