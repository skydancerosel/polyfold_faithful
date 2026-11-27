import GWMemoir.ConstantInstance
import GWMemoir.PullbackBounded

/-!
# The vector bundle GCT of the fibres of `W` on the constant maps

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §1.2 (p. 7), with the
vector bundle GCT of HWZ 2021 Definition 17.7.1 (p. 825), on the category `constCat` of the
constant maps from the three-pointed sphere (`GWMemoir.ConstantBase`).

## What is formalized

* `constAt`: one atlas of `sphere3` read at every constant map, so the fibres of all objects are
  closed subspaces of one block space.  `constAt_pullbackBounded`: `AllPullbackBounded` for it
  (every isomorphism of `constCat` is a unit), and the fibre functor `constμ`.
* The topology on `|E| = ⨆_q E_q`: induced by the injective map
  `(q, v) ↦ (q, (ρₙ(q) · blockOp(T_{xₙ→q}) v)ₙ)` for a countable family of charts of `Q` with a
  subordinate partition of unity (`Frames`, `frameOrbit`).
* The local frames `Kmat J q₀ q = T_{q₀→q} ∘ ½(1 − J̃(q) J(q₀))`, which intertwine `J(q₀)` and
  `J(q)` near `q₀` (`Kmat_comp_J`), give the openness of `|P|` (`isOpenMap_constProj`).
* **`constVectorBundle`**: the vector bundle GCT, with no named proposition, and the Theorems 1.10
  and 1.11 of the memoir on the constant maps with it (`memoir_theorem_1_10_const_bundle`,
  `memoir_theorem_1_11_const_bundle`).

## Readings

* Definition 17.7.1 asks for a metrizable topology on `|E|` with continuous fibre inclusions and
  `|P|` surjective, continuous and open; no local triviality is asked, and none is used.
* The strong bundle uniformizers `Fb` with Proposition 3.39 stay hypotheses, as in
  `GWMemoir.ConstantInstance`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir

open Polyfold.GroupoidalCategory

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-! ## 4. The atlases of the constant maps and the fibre functor -/

section ConstAtlas

variable [Nonempty Q] {om : SymplecticForm E Q} {k : ℕ} {δ : ℝ}

variable (E) in
/-- A fixed atlas of a surface without nodes, for the constant map at a fixed point of `Q`. -/
def baseAtlas {m : ℕ} (X : NodalSurface m) (hX : X.nodes = ∅) :
    SectionAtlas (E := E) X (fun _ => Classical.arbitrary Q) :=
  (exists_sectionAtlas (E := E) X _ continuous_const hX).some

lemma constOb_u_const {α : StableMap om 3 k δ} (h : α ∈ constOb om k δ) :
    ∀ x y, α.u x = α.u y := by
  obtain ⟨q, rfl⟩ := h
  intro x y; rfl

/-- **One atlas for all constant maps**: the atlas of the object `α` is the fixed atlas of its
domain (`baseAtlas`), read for the constant map `α.u`.  At `const q` it is `atConst A₀ q` for the
fixed atlas `A₀` of `sphere3` (`constAt_constObj`), so the fibres of all objects are subspaces of
one block space. -/
def constAt (a : (constCat om k δ).Obj) : SectionAtlas (E := E) a.1.dom a.1.u :=
  (baseAtlas E a.1.dom (constOb_noNodes a.1 a.2)).toConst a.1.u (constOb_u_const a.2)

variable (E Q) in
/-- The fixed atlas of `sphere3`. -/
abbrev sphereAtlas : SectionAtlas (E := E) sphere3 (fun _ => Classical.arbitrary Q) :=
  baseAtlas E sphere3 rfl

theorem constAt_constObj (q : Q) :
    constAt (om := om) (k := k) (δ := δ) (constObj q) = atConst (sphereAtlas E Q) q := rfl

variable (J : AlmostComplexStructure E Q) (δs : ℕ → ℝ) (h0 : 0 ≤ δs 0) (hmono : StrictMono δs)

/-- **The change of coordinates holds for `constAt`** (no named proposition): every isomorphism of
constant maps from the three-pointed sphere is the identity. -/
theorem constAt_pullbackBounded :
    AllPullbackBounded J δs h0 hmono (constOb_finite (om := om) (k := k) (δ := δ)) constAt := by
  rintro ⟨⟨α, β, f⟩, hφ⟩
  have hφ' : α ∈ constOb om k δ ∧ β ∈ constOb om k δ := hφ
  obtain ⟨⟨q, rfl⟩, ⟨q', rfl⟩⟩ := hφ'
  obtain rfl := eq_of_iso_const f
  exact pullbackBounded_of_id J δs h0 hmono _ f (fun x => sphere3_iso_apply f.φ x)

/-- **The fibre functor of the constant maps** `μ(α) = ` the fibre of `W` over `α` in the atlas
`constAt α`. -/
abbrev constμ : BanachFunctor (constCat om k δ) :=
  fibreFunctor (constAt_pullbackBounded (om := om) (k := k) (δ := δ) J δs h0 hmono)

end ConstAtlas

/-! ## 5. Frames of `TQ` and the complex structure in a chart -/

section Frames

variable (E Q) in
/-- **A countable family of chart frames of `TQ`**: points `xₙ` and continuous functions `ρₙ`
supported in the chart at `xₙ`, not all zero at any point. -/
structure Frames where
  x : ℕ → Q
  ρ : ℕ → C(Q, ℝ)
  supp : ∀ n, tsupport (ρ n) ⊆ (extChartAt 𝓘(ℝ, E) (x n)).source
  pos : ∀ q, ∃ n, ρ n q ≠ 0

theorem frames_nonempty [T2Space Q] [ParacompactSpace Q] [SecondCountableTopology Q]
    [Nonempty Q] : Nonempty (Frames E Q) := by
  obtain ⟨s, hs, hcov⟩ := TopologicalSpace.countable_cover_nhds
    (f := fun x : Q => (extChartAt 𝓘(ℝ, E) x).source) fun x => extChartAt_source_mem_nhds x
  have hne : s.Nonempty := by
    obtain ⟨q⟩ := ‹Nonempty Q›
    have : q ∈ ⋃ x ∈ s, (extChartAt 𝓘(ℝ, E) x).source := hcov ▸ mem_univ q
    obtain ⟨x, hx, -⟩ := mem_iUnion₂.1 this
    exact ⟨x, hx⟩
  obtain ⟨x, rfl⟩ := hs.exists_eq_range hne
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun n => (extChartAt 𝓘(ℝ, E) (x n)).source) (fun n => isOpen_extChartAt_source _)
    (fun q _ => by
      have : q ∈ ⋃ y ∈ range x, (extChartAt 𝓘(ℝ, E) y).source := hcov ▸ mem_univ q
      obtain ⟨y, ⟨n, rfl⟩, hy⟩ := mem_iUnion₂.1 this
      exact mem_iUnion.2 ⟨n, hy⟩)
  refine ⟨⟨x, fun n => f n, hf, fun q => ?_⟩⟩
  by_contra h
  push Not at h
  have h1 := f.sum_eq_one (mem_univ q)
  rw [finsum_eq_zero_of_forall_eq_zero h] at h1
  exact zero_ne_one h1

variable (J : AlmostComplexStructure E Q)

/-- `J` read in the chart at `q₀`: `J̃(q) = T_{q → q₀} J(q) T_{q₀ → q}`. -/
def Jt (q₀ q : Q) : E →L[ℝ] E := inTangentCoordinates 𝓘(ℝ, E) 𝓘(ℝ, E) id id J.J q₀ q

lemma Jt_eq {q₀ q : Q} (hq : q ∈ (extChartAt 𝓘(ℝ, E) q₀).source) :
    Jt J q₀ q = (tangentCoordChange 𝓘(ℝ, E) q q₀ q).comp
      ((J.J q).comp (tangentCoordChange 𝓘(ℝ, E) q₀ q q)) := by
  rw [extChartAt_source] at hq
  exact inTangentCoordinates_eq _ _ _ hq hq

lemma tcc_inv_bundle {x y q : Q} (hx : q ∈ (extChartAt 𝓘(ℝ, E) x).source)
    (hy : q ∈ (extChartAt 𝓘(ℝ, E) y).source) (w : E) :
    tangentCoordChange 𝓘(ℝ, E) y x q (tangentCoordChange 𝓘(ℝ, E) x y q w) = w := by
  rw [tangentCoordChange_comp ⟨⟨hx, hy⟩, hx⟩, tangentCoordChange_self hx]

lemma Jt_self (q₀ : Q) : Jt J q₀ q₀ = J.J q₀ := by
  rw [Jt_eq J (mem_extChartAt_source q₀)]
  ext w
  simp only [ContinuousLinearMap.comp_apply]
  rw [tangentCoordChange_self (mem_extChartAt_source q₀),
    tangentCoordChange_self (mem_extChartAt_source q₀)]

lemma continuousAt_Jt (q₀ : Q) : ContinuousAt (Jt J q₀) q₀ :=
  (J.smooth q₀).continuousAt

lemma J_J (q : Q) (w : E) : J.J q (J.J q w) = -w := by
  have := congrArg (fun T : E →L[ℝ] E => T w) (J.sq q)
  simpa using this

/-- `T_{q₀ → q} J̃(q) = J(q) T_{q₀ → q}`. -/
lemma tcc_Jt {q₀ q : Q} (hq : q ∈ (extChartAt 𝓘(ℝ, E) q₀).source) (w : E) :
    tangentCoordChange 𝓘(ℝ, E) q₀ q q (Jt J q₀ q w) =
      J.J q (tangentCoordChange 𝓘(ℝ, E) q₀ q q w) := by
  rw [Jt_eq J hq]
  simp only [ContinuousLinearMap.comp_apply]
  exact tcc_inv_bundle (mem_extChartAt_source q) hq _

/-- `A(q) = ½ (1 - J̃(q) J(q₀))`, `A(q₀) = 1`, `A(q) J(q₀) = J̃(q) A(q)`. -/
def Amat (q₀ q : Q) : E →L[ℝ] E :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ E - (Jt J q₀ q).comp (J.J q₀))

/-- **The local frame**: `K(q) = T_{q₀ → q} A(q)` maps the forms anti-linear for `J(q₀)` to the
forms anti-linear for `J(q)` (`Kmat_comp_J`), `K(q₀) = 1` (`Kmat_self`). -/
def Kmat (q₀ q : Q) : E →L[ℝ] E := (tangentCoordChange 𝓘(ℝ, E) q₀ q q).comp (Amat J q₀ q)

lemma Amat_self (q₀ : Q) : Amat J q₀ q₀ = ContinuousLinearMap.id ℝ E := by
  ext w
  simp only [Amat, Jt_self, smul_apply, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, J_J]
  module

lemma Kmat_self (q₀ : Q) : Kmat J q₀ q₀ = ContinuousLinearMap.id ℝ E := by
  ext w
  simp only [Kmat, Amat_self, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  exact tangentCoordChange_self (mem_extChartAt_source q₀)

lemma Kmat_comp_J {q₀ q : Q} (hq : q ∈ (extChartAt 𝓘(ℝ, E) q₀).source) :
    (Kmat J q₀ q).comp (J.J q₀) = (J.J q).comp (Kmat J q₀ q) := by
  ext w
  simp only [Kmat, Amat, ContinuousLinearMap.comp_apply, smul_apply,
    sub_apply, ContinuousLinearMap.id_apply, map_smul, map_sub, J_J,
    map_neg, sub_neg_eq_add, tcc_Jt J hq]
  rw [map_add, tcc_Jt J hq, add_comm]

lemma continuousAt_Amat (q₀ : Q) : ContinuousAt (Amat J q₀) q₀ :=
  show ContinuousAt (fun q => (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ E - (Jt J q₀ q).comp
    (J.J q₀))) q₀ from
    ((continuousAt_const (y := ContinuousLinearMap.id ℝ E)).sub
      ((continuousAt_Jt J q₀).clm_comp (continuousAt_const (y := J.J q₀)))).const_smul (1 / 2 : ℝ)

end Frames

/-! ## 6. The topology on `|E|` and the vector bundle GCT -/

section Bundle

variable [T2Space Q] [ParacompactSpace Q] [SecondCountableTopology Q] [Nonempty Q]
  {om : SymplecticForm E Q} {k : ℕ} {δ : ℝ}
  (J : AlmostComplexStructure E Q) (δs : ℕ → ℝ) (h0 : 0 ≤ δs 0) (hmono : StrictMono δs)

variable (E Q) in
/-- A fixed choice of chart frames. -/
def constFrames : Frames E Q := frames_nonempty.some

/-- **The fibre at `q` read in the chart frames**: `w ↦ (q, (ρₙ(q) T_{q → xₙ} w)ₙ)`, with
`T_{q → xₙ}` acting on the `E`-coordinates of the blocks. -/
def frameMap (q : Q) (w : fibreSpace J (atConst (sphereAtlas E Q) q) δs h0 hmono) :
    Q × (ℕ → (fibreBlocks (sphereAtlas E Q) δs h0 hmono) 0) :=
  (q, fun n => (constFrames E Q).ρ n q • blockOp (sphereAtlas E Q)
    (tangentCoordChange 𝓘(ℝ, E) q ((constFrames E Q).x n) q) w.1)

theorem frameMap_injective (q : Q) : Injective (frameMap J δs h0 hmono q) := by
  intro w w' h
  obtain ⟨n, hn⟩ := (constFrames E Q).pos q
  have hq : q ∈ (extChartAt 𝓘(ℝ, E) ((constFrames E Q).x n)).source :=
    (constFrames E Q).supp n (subset_tsupport _ hn)
  have h2 := smul_right_injective _ hn (congrFun (congrArg Prod.snd h) n)
  have h3 := congrArg (blockOp (sphereAtlas E Q)
    (tangentCoordChange 𝓘(ℝ, E) ((constFrames E Q).x n) q q)) h2
  have hid : (tangentCoordChange 𝓘(ℝ, E) ((constFrames E Q).x n) q q).comp
      (tangentCoordChange 𝓘(ℝ, E) q ((constFrames E Q).x n) q) = ContinuousLinearMap.id ℝ E := by
    ext v; exact tcc_inv_bundle (mem_extChartAt_source q) hq v
  have key : ∀ v : (fibreBlocks (sphereAtlas E Q) δs h0 hmono) 0,
      blockOp (sphereAtlas E Q) (tangentCoordChange 𝓘(ℝ, E) ((constFrames E Q).x n) q q)
        (blockOp (sphereAtlas E Q) (tangentCoordChange 𝓘(ℝ, E) q ((constFrames E Q).x n) q) v)
        = v := fun v => by rw [← blockOp_comp, hid, blockOp_id]
  exact Subtype.ext ((key w.1).symm.trans (h3.trans (key w'.1)))

theorem continuous_frameMap (q : Q) : Continuous (frameMap J δs h0 hmono q) :=
  continuous_const.prodMk (continuous_pi fun _ =>
    (continuous_const_smul _).comp ((blockOp (sphereAtlas E Q) _).continuous.comp
      continuous_subtype_val))

/-- The point of `Q` of an object: the value of its (constant) map. -/
def qOf (a : (constCat om k δ).Obj) : Q := a.1.u (a.1.dom.marked 0)

theorem eq_constObj_qOf (a : (constCat om k δ).Obj) : a = constObj (qOf a) := by
  obtain ⟨α, q, rfl⟩ := a
  rfl

/-- The objects of `E` read in the chart frames. -/
def frameObj (e : (constμ (om := om) (k := k) (δ := δ) J δs h0 hmono).EObj) :
    Q × (ℕ → (fibreBlocks (sphereAtlas E Q) δs h0 hmono) 0) :=
  frameMap J δs h0 hmono (qOf e.1)
    (cast (congrArg (constμ (om := om) (k := k) (δ := δ) J δs h0 hmono).V
      (eq_constObj_qOf e.1)) e.2).down

theorem frameObj_constObj (q : Q)
    (v : (constμ (om := om) (k := k) (δ := δ) J δs h0 hmono).V (constObj q)) :
    frameObj J δs h0 hmono ⟨constObj q, v⟩ = frameMap J δs h0 hmono q v.down := rfl

theorem eq_of_isomorphic {e e' : (constμ (om := om) (k := k) (δ := δ) J δs h0 hmono).EObj}
    (h : (constμ (om := om) (k := k) (δ := δ) J δs h0 hmono).groupoid.Isomorphic e e') :
    e = e' := by
  obtain ⟨φ, rfl, rfl⟩ := h
  have hu := constCat_mor_eq_unit φ.φ
  exact ((BanachFunctor.act_congr hu rfl φ.2 (φ.2.trans (congrArg _ hu))).trans
    (BanachFunctor.act_unit' _ _)).symm

/-- The orbit space `|E|` read in the chart frames. -/
def frameOrbit : (constμ (om := om) (k := k) (δ := δ) J δs h0 hmono).groupoid.OrbitSpace →
    Q × (ℕ → (fibreBlocks (sphereAtlas E Q) δs h0 hmono) 0) :=
  Quotient.lift (frameObj J δs h0 hmono) fun _ _ h => congrArg _ (eq_of_isomorphic J δs h0 hmono h)

theorem frameOrbit_injective :
    Injective (frameOrbit (om := om) (k := k) (δ := δ) J δs h0 hmono) := by
  intro z z'
  induction z using Quotient.inductionOn with | h e => ?_
  induction z' using Quotient.inductionOn with | h e' => ?_
  intro h
  change frameObj J δs h0 hmono e = frameObj J δs h0 hmono e' at h
  obtain ⟨a, v⟩ := e
  obtain ⟨a', v'⟩ := e'
  obtain ⟨q, rfl⟩ := exists_constObj a
  obtain ⟨q', rfl⟩ := exists_constObj a'
  rw [frameObj_constObj, frameObj_constObj] at h
  have hq : q = q' := congrArg Prod.fst h
  subst hq
  have := frameMap_injective J δs h0 hmono q h
  rw [show v = v' from ULift.ext _ _ this]

variable {J δs h0 hmono}

/-- **The fibres near `q₀` through `v₀`**: `q ↦ K(q) v₀` in the chart at `q₀`, an element of the
fibre at `q` (`Kmat_comp_J`). -/
def fibrePath (q₀ : Q) (v₀ : fibreSpace J (atConst (sphereAtlas E Q) q₀) δs h0 hmono) (q : Q) :
    fibreSpace J (atConst (sphereAtlas E Q) q) δs h0 hmono := by
  classical
  exact if hq : q ∈ (extChartAt 𝓘(ℝ, E) q₀).source then
    ⟨blockOp (sphereAtlas E Q) (Kmat J q₀ q) v₀.1,
      blockOp_mem_fibreSpace (B := sphereAtlas E Q) rfl (Kmat_comp_J J hq) v₀.2⟩ else 0

theorem fibrePath_self (q₀ : Q) (v₀ : fibreSpace J (atConst (sphereAtlas E Q) q₀) δs h0 hmono) :
    fibrePath q₀ v₀ q₀ = v₀ := by
  unfold fibrePath
  rw [dif_pos (mem_extChartAt_source q₀)]
  apply Subtype.ext
  change blockOp (sphereAtlas E Q) (Kmat J q₀ q₀) v₀.1 = v₀.1
  rw [Kmat_self]
  exact blockOp_id (A := sphereAtlas E Q) v₀.1

/-- **The path is continuous in the chart frames at `q₀`**: in every frame `n`, `ρₙ(q) T_{q → xₙ}
K(q) = ρₙ(q) T_{q₀ → xₙ}(q) A(q)` near `q₀`, continuous since `J` is continuous in the chart at
`q₀`. -/
theorem continuousAt_fibrePath (q₀ : Q)
    (v₀ : fibreSpace J (atConst (sphereAtlas E Q) q₀) δs h0 hmono) :
    ContinuousAt (fun q => frameMap J δs h0 hmono q (fibrePath q₀ v₀ q)) q₀ := by
  refine continuousAt_id.prodMk (continuousAt_pi.2 fun n => ?_)
  set F := constFrames E Q
  have hev : ∀ᶠ q in 𝓝 q₀, blockOp (sphereAtlas E Q)
      (F.ρ n q • (tangentCoordChange 𝓘(ℝ, E) q (F.x n) q).comp (Kmat J q₀ q)) v₀.1 =
        (frameMap J δs h0 hmono q (fibrePath q₀ v₀ q)).2 n := by
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) q₀] with q hq
    simp only [frameMap, fibrePath, dif_pos hq]
    exact (blockOp_smul (A := sphereAtlas E Q) _ _ v₀.1).trans
      (congrArg _ (blockOp_comp (A := sphereAtlas E Q) _ _ v₀.1))
  refine ContinuousAt.congr ?_ hev
  refine (continuous_blockOpAt (A := sphereAtlas E Q) v₀.1).continuousAt.comp
    (f := fun q => F.ρ n q • (tangentCoordChange 𝓘(ℝ, E) q (F.x n) q).comp (Kmat J q₀ q)) ?_
  by_cases hx : q₀ ∈ (extChartAt 𝓘(ℝ, E) (F.x n)).source
  · have hN : (extChartAt 𝓘(ℝ, E) q₀).source ∩ (extChartAt 𝓘(ℝ, E) (F.x n)).source ∈ 𝓝 q₀ :=
      inter_mem (extChartAt_source_mem_nhds q₀) ((isOpen_extChartAt_source _).mem_nhds hx)
    have heq : (fun q => F.ρ n q • (tangentCoordChange 𝓘(ℝ, E) q₀ (F.x n) q).comp
        (Amat J q₀ q)) =ᶠ[𝓝 q₀]
          fun q => F.ρ n q • (tangentCoordChange 𝓘(ℝ, E) q (F.x n) q).comp (Kmat J q₀ q) := by
      filter_upwards [hN] with q hq
      congr 1
      ext w
      simp only [Kmat, ContinuousLinearMap.comp_apply]
      exact (tangentCoordChange_comp ⟨⟨hq.1, mem_extChartAt_source q⟩, hq.2⟩).symm
    refine ContinuousAt.congr ?_ heq
    exact (F.ρ n).continuous.continuousAt.smul
      (((continuousOn_tangentCoordChange q₀ (F.x n)).continuousAt hN).clm_comp
        (continuousAt_Amat J q₀))
  · have hz : (F.ρ n : Q → ℝ) =ᶠ[𝓝 q₀] 0 :=
      notMem_tsupport_iff_eventuallyEq.1 fun h => hx (F.supp n h)
    refine ContinuousAt.congr (continuousAt_const (y := (0 : E →L[ℝ] E))) ?_
    filter_upwards [hz] with q hq
    simp only [Pi.zero_apply] at hq
    rw [hq, zero_smul]

variable (J δs h0 hmono)

/-- **The topology `T` on `|E|`** (Definition 17.7.1): induced by the chart frames, `|E| → Q ×
∏ₙ (blocks)`, `|(α, v)| ↦ (q, (ρₙ(q) T_{q → xₙ} v)ₙ)`. -/
@[instance_reducible] def constTopE : TopologicalSpace
    (constμ (om := om) (k := k) (δ := δ) J δs h0 hmono).groupoid.OrbitSpace :=
  TopologicalSpace.induced (frameOrbit J δs h0 hmono) inferInstance

theorem constπ_injective : Injective fun q : Q => (constCat om k δ).π (constObj q) :=
  fun q q' h => congrArg ULift.down (injective_constπ (om := om) (k := k) (δ := δ)
    (a₁ := ULift.up q) (a₂ := ULift.up q') h)

theorem continuous_constπ' :
    Continuous[_, (constGCT om k δ).top] fun q : Q => (constCat om k δ).π (constObj q) :=
  letI := constTop (constT om k δ)
  (constOrbitHomeomorph (constT om k δ)).continuous

theorem constProj_eq :
    (constμ (om := om) (k := k) (δ := δ) J δs h0 hmono).proj.orbitMap =
      (fun q : Q => (constCat om k δ).π (constObj q)) ∘ Prod.fst ∘ frameOrbit J δs h0 hmono := by
  funext z
  induction z using Quotient.inductionOn with | h e => ?_
  obtain ⟨a, v⟩ := e
  obtain ⟨q, rfl⟩ := exists_constObj a
  rfl

theorem isOpenMap_constProj :
    @IsOpenMap _ _ (constTopE (om := om) (k := k) (δ := δ) J δs h0 hmono) (constGCT om k δ).top
      (constμ (om := om) (k := k) (δ := δ) J δs h0 hmono).proj.orbitMap := by
  intro W hW
  obtain ⟨W', hW', rfl⟩ := isOpen_induced_iff.1 hW
  let := constTop (constT om k δ)
  refine ((constOrbitHomeomorph (constT om k δ)).isOpen_preimage).1 ?_
  rw [isOpen_iff_mem_nhds]
  intro q₀ hq₀
  obtain ⟨z, hz, hzq⟩ := hq₀
  induction z using Quotient.inductionOn with | h e => ?_
  obtain ⟨a, v⟩ := e
  obtain ⟨q, rfl⟩ := exists_constObj a
  obtain rfl : q = q₀ := constπ_injective hzq
  have hmem : frameMap J δs h0 hmono q (fibrePath q v.down q) ∈ W' :=
    (congrArg (· ∈ W') (congrArg (frameMap J δs h0 hmono q) (fibrePath_self q v.down))).mpr hz
  filter_upwards [(continuousAt_fibrePath q v.down).preimage_mem_nhds (hW'.mem_nhds hmem)]
    with q' hq'
  exact ⟨(constμ (om := om) (k := k) (δ := δ) J δs h0 hmono).groupoid.π
    ⟨constObj q', ULift.up (fibrePath q v.down q')⟩, hq', rfl⟩

theorem continuous_constFiber (α : (constCat om k δ).Obj) :
    Continuous[_, constTopE J δs h0 hmono] fun v : (constμ J δs h0 hmono).V α =>
      (constμ J δs h0 hmono).groupoid.π ((constμ J δs h0 hmono).objMk α v) := by
  obtain ⟨q, rfl⟩ := exists_constObj α
  rw [constTopE, continuous_induced_rng]
  exact (continuous_frameMap J δs h0 hmono q).comp
    (ContinuousLinearEquiv.ulift (R₁ := ℝ)).continuous

theorem continuous_constProj :
    @Continuous _ _ (constTopE (om := om) (k := k) (δ := δ) J δs h0 hmono) (constGCT om k δ).top
      (constμ (om := om) (k := k) (δ := δ) J δs h0 hmono).proj.orbitMap := by
  let := constTopE (om := om) (k := k) (δ := δ) J δs h0 hmono
  rw [constProj_eq]
  exact continuous_constπ'.comp (continuous_fst.comp continuous_induced_dom)

theorem surjective_constProj :
    Surjective (constμ (om := om) (k := k) (δ := δ) J δs h0 hmono).proj.orbitMap := by
  intro z
  induction z using Quotient.inductionOn with | h a => ?_
  exact ⟨(constμ J δs h0 hmono).groupoid.π (BanachFunctor.objMk _ a 0), rfl⟩

theorem metrizableSpace_constTopE :
    @TopologicalSpace.MetrizableSpace _ (constTopE (om := om) (k := k) (δ := δ) J δs h0 hmono) :=
  letI := constTopE (om := om) (k := k) (δ := δ) J δs h0 hmono
  Topology.IsEmbedding.metrizableSpace ⟨⟨rfl⟩, frameOrbit_injective J δs h0 hmono⟩

/-- **Memoir p. 7, the bundle `p : W → Z` on the constant maps from the three-pointed sphere, as a
vector bundle GCT** (2021 Definition 17.7.1, p. 825): `μ` the fibre functor (`constμ`), the
topology induced by the chart frames of `TQ`, metrizable; the fibre inclusions are continuous and
`|P| : |E| → |Z|` is surjective, continuous and open.  No named proposition. -/
def constVectorBundle : (constGCT om k δ).VectorBundle where
  toBanachFunctor := constμ J δs h0 hmono
  topE := constTopE J δs h0 hmono
  metrizableE := metrizableSpace_constTopE J δs h0 hmono
  continuous_fiber := continuous_constFiber J δs h0 hmono
  surjective_orbitProj := surjective_constProj J δs h0 hmono
  continuous_orbitProj := continuous_constProj J δs h0 hmono
  isOpenMap_orbitProj := isOpenMap_constProj J δs h0 hmono

theorem constVectorBundle_toBanachFunctor :
    (constVectorBundle (om := om) (k := k) (δ := δ) J δs h0 hmono).toBanachFunctor =
      fibreFunctor (constAt_pullbackBounded J δs h0 hmono) := rfl

end Bundle

/-! ## 7. Theorems 1.10 and 1.11 on the constant maps with the bundle -/

section Theorems

open Polyfold.GroupoidalCategory.BasicConstruction
  Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction

variable [T2Space Q] [ParacompactSpace Q] [SecondCountableTopology Q] [Nonempty Q]
  {om : SymplecticForm E Q} {k : ℕ} {δ : ℝ}
  (J : AlmostComplexStructure E Q) (δs : ℕ → ℝ) (h0 : 0 ≤ δs 0) (hmono : StrictMono δs)

/-- **Memoir Theorem 1.10 on the constant maps from the three-pointed sphere, with the vector
bundle GCT built** (p. 7; 2021 Definitions 17.7.1, 17.7.4, 16.3.1): the base hypotheses hold
(`GWMemoir.ConstantBase`) and `V = constVectorBundle` is the vector bundle GCT of the fibres of `W`
(no named proposition).  For strong bundle uniformizers of `V` with Proposition 3.39 and
`HasBundleUniformizers` there is the strong polyfold bundle `W → Z`, the same for every covering
family.

This category has no nodes and no gluing: the statement tests the wiring, not the analysis. -/
theorem memoir_theorem_1_10_const_bundle
    (Fb : Polyfold.GCT.VectorBundle.StrongBundleUniformizerConstruction
      (constVectorBundle (om := om) (k := k) (δ := δ) J δs h0 hmono)
      (constPC om k δ))
    (h339 : Proposition_3_39 Fb) (hF : HasBundleUniformizers Fb) :
    ∃ (hZ : (constPC om k δ).IsZhou)
      (W : StrongPolyfoldBundle
        (constVectorBundle (om := om) (k := k) (δ := δ) J δs h0 hmono).proj.orbitMap),
      W.polyfold = (constPC om k δ).polyfoldClass hZ ∧
      ∀ c : (ofProposition_3_39 Fb h339).BundleCoveringFamily,
        W = bundleOf hZ (isEffective_toPolyfoldConstruction _ constU_locallyFaithful) _ c :=
  memoir_theorem_1_10_const Fb h339 hF

/-- The fibre representation of the GW data on the constant maps, for the atlases `constAt`. -/
def constBundleFibreRep (k' : ℕ) (δ' : ℝ) :=
  fibreRepresentation (constAt_pullbackBounded (om := om) (k := k) (δ := δ) J δs h0 hmono)
    constOb_noNodes k' δ'

theorem constBundleFibreRep_dbarInDom (k' : ℕ) (δ' : ℝ) :
    DbarInDom (constBundleFibreRep (om := om) (k := k) (δ := δ) J δs h0 hmono k' δ') := by
  rintro ⟨_, ⟨q, rfl⟩⟩
  change (constStableMap om q k δ).dom.dbar J (fun _ => q) ∈ formsDom J _ δs h0 hmono
  rw [dbar_const_eq_zero]
  exact Submodule.zero_mem _

/-- **Memoir Theorem 1.11 = Theorem 4.6 on the constant maps from the three-pointed sphere, with
the vector bundle GCT built** (pp. 8, 101).  Discharged: the base, the vector bundle GCT
`constVectorBundle`, the fibre representation, `DbarInDom` and `DbarRegularC`.  Kept: the strong
bundle uniformizers `Fb` with Proposition 3.39, and `CRProps`.

`CRProps` has no instance here as we read it (finite-dimensional base, infinite-dimensional fibre;
`GWMemoir.ConstantInstance`), so the conclusion checks only that the hypotheses fit. -/
theorem memoir_theorem_1_11_const_bundle (k' : ℕ) (δ' : ℝ)
    (Fb : Polyfold.GCT.VectorBundle.StrongBundleUniformizerConstruction
      (constVectorBundle (om := om) (k := k) (δ := δ) J δs h0 hmono)
      (constPC om k δ))
    (h339 : Proposition_3_39 Fb) (c : (ofProposition_3_39 Fb h339).BundleCoveringFamily)
    (h : CRProps Fb h339 (constBundleFibreRep J δs h0 hmono k' δ')
      (constBundleFibreRep_dbarInDom J δs h0 hmono k' δ') c) :
    ((ofProposition_3_39 Fb h339).modelSEP c.Ψ).B.IsScFredholmSectionTame
        (dbarFunctor Fb h339 _ (constBundleFibreRep_dbarInDom J δs h0 hmono k' δ') c) ∧
      (dbarSection constU_tangentFaithful constU_locallyFaithful Fb h339 _
          (constBundleFibreRep_dbarInDom J δs h0 hmono k' δ') c h).1.solutionSet =
        (fun x => (gwStructure constU_tangentFaithful constU_locallyFaithful Fb h339 c).γ
            ((gwStructure constU_tangentFaithful constU_locallyFaithful Fb h339 c).A.X.π x)) ''
          {x | ((subLabel (constOb om k δ) constOb_finite).obj
            (((constPC om k δ).modelFunctor
              ((ofProposition_3_39 Fb h339).modelBase c.Ψ)).obj x)).IsHolomorphic J} := by
  have H := memoir_theorem_1_11 constU_tangentFaithful constU_locallyFaithful Fb h339 _
    (constBundleFibreRep_dbarInDom J δs h0 hmono k' δ') c h
  exact ⟨H.1, H.2 (const_dbarRegularC J om k δ k' δ')⟩

end Theorems

end GWMemoir
