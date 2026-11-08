import Polyfold.Chapter2.TameBoundaryStructure
import Polyfold.Chapter2.TameBoundaryExample

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, Appendix §2.7.4:
**Proposition 2.7.12** (p. 83) and the characterization closing **Theorem 2.7.13** (p. 84), both
new in the 2021 edition, for representatives `(x, V, θ)` whose neighbourhood `V` is **not**
centred at `x`.  The centred case is `Polyfold/Chapter2/TameBoundaryStructure.lean`
(`phi_isScDiffeoOn`, `proposition_2_7_12_scDiffeo_2021`, `theorem_2_7_13_structure_2021`).

# `Φ_{(x,V,θ)}` for arbitrary representatives

## The text, paraphrased

(Before Proposition 2.7.12) If `U(x, V, θ)` and `U(x', V', θ')` share a class `[y, U, σ]`, then
near `y` the face `σ` sits in `θ` and `θ'` by open sc-embeddings, so the transition map
`Φ_{(x',V',θ')} ∘ Φ_{(x,V,θ)}⁻¹` is sc-smooth near every point of its domain, in both directions.
(Proposition 2.7.12) For any two such maps the sets `Φ_{(x,V,θ)}(U ∩ U')`,
`Φ_{(x',V',θ')}(U ∩ U')` are open in `θ`, `θ'`, and the transition map between them is an
sc-diffeomorphism.  (After Theorem 2.7.13) For every class and **every representative**
`(x, V, θ)`, `U(x, V, θ)` is open and `Φ_{(x,V,θ)} : U(x, V, θ) → θ` is a homeomorphism and an
sc-diffeomorphism, `θ` carrying the structure induced from `V`; this characterizes the topology
and the M-polyfold structure of `bX`.

## What is formalized

* `TameBoundary.BTriple.exists_centred_subset`: every triple `s` has an equivalent centred triple
  `s'` with `U(s') ⊆ U(s)`; `TameBoundary.phiInv` (the inverse of `Φ_{(x,V,θ)}` on its image
  `θ ∩ V^x`, as a total map), `phiInv_eq`, `phiInv_spec`, `phiInv_bMap`.
* `MPolyfold.phiTot_isScSmoothOn` (`Φ` is sc-smooth on `U(x, V, θ)`: `B` is sc-smooth and `θ` is a
  sub-M-polyfold), `MPolyfold.phiInv_isScSmoothOn` (`Φ⁻¹` is sc-smooth on `θ ∩ V^x`: near each
  point it is `Φ_{s'}⁻¹` of a centred `s'` composed with the inclusion of an open piece of `θ`
  into the face `θ_{s'}`).
* **The characterization, all representatives**: `MPolyfold.phi_isScDiffeoOn_nonCentred_2021`
  (`Φ_{(x,V,θ)}` is an sc-diffeomorphism of `U(x, V, θ)` onto the open subset `θ ∩ V^x` of `θ`;
  it is a homeomorphism onto it by `isOpenEmbedding_phi`), with
  `MPolyfold.reachSet_eq_univ_of_isCenteredAt` (for centred `V` the image is `θ`) and the
  uniqueness `MPolyfold.tameBoundaryPolyfold_unique_allReps_2021` together with its
  satisfiability witness `MPolyfold.tameBoundaryPolyfold_satisfies_allReps_2021`.
* **Proposition 2.7.12, all representatives**:
  `MPolyfold.proposition_2_7_12_scDiffeo_nonCentred_2021` (the transition map
  `Φ_{(x',V',θ')} ∘ Φ_{(x,V,θ)}⁻¹` is an sc-diffeomorphism between `Φ(U ∩ U')` and `Φ'(U ∩ U')`,
  both open, and it is the identity on the underlying points of `X`).
* `MPolyfold.not_surjOn_phiTot_2021`: in `[0,∞)³` the map `Φ_{(x,V,θ)}` of the triple of
  `TameBoundaryExample.lean` does not map `U(x, V, θ)` onto `θ`.

## What the text leaves implicit, and the choices made

* **"`Φ_{(x,V,θ)}` is an sc-diffeomorphism onto `θ`" does not hold as we read it for every
  representative**: its image is `θ ∩ V^x` (`TameBoundary.bMap_image_uSet`), a proper subset of
  `θ` for some `V ∈ N_{X,x}` (`not_surjOn_phiTot_2021`, from `phi_not_surjective_2021`).  The
  strongest correct version is proved: an sc-diffeomorphism onto the open subset `θ ∩ V^x`; for
  centred `V` this is the printed statement.  Proposition 2.7.12 holds as printed for all
  representatives (its domains are images of `U ∩ U'`, which lie in `θ ∩ V^x`).
* The proof follows the text's diagram locally, with the centred refinement `(y, V'^y, σ)` of a
  representative of the class at hand in place of `(y, U, σ)`, and the sub-M-polyfold calculus
  (a map into a sub-M-polyfold is sc-smooth as soon as it is sc-smooth into `X`) in place of the
  open sc-embeddings `σ → θ`.
* "Uniquely characterized" with all representatives is read as for centred ones: an M-polyfold
  structure on `bX` with the property for every representative is equivalent to ours (it has the
  property for the centred ones, `tameBoundaryPolyfold_unique`).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace TameBoundary

universe u

variable {X : Type u} [TopologicalSpace X] {d : X → ℕ} (hd : IsCornerIndex d)

/-- Every triple `s = (x, V, θ)` has an equivalent triple `s' = (x, V^x, θ')`, centred at `x`, with
`U(s') ⊆ U(s)` (there is a morphism `(x, V^x) → (x, V)` sending `θ'` to `θ`). -/
theorem BTriple.exists_centred_subset (s : BTriple hd) :
    ∃ s' : BTriple hd, s'.cls = s.cls ∧ IsCenteredAt d s'.x s'.V ∧ uSet hd s' ⊆ uSet hd s := by
  have hV' := reach_mem_faceStructuredNbhdsAt hd s.mem
  obtain ⟨θ', hθ', he⟩ := exists_face_restrict hd s.mem hV'.1.1.1 hV'.2.1 (reach_subset _ _)
    s.mem_faces
  let s' : BTriple hd := ⟨⟨s.x, reach d s.V s.x, hV', s.one_le⟩, θ', hθ'⟩
  refine ⟨s', ?_, isCenteredAt_reach hd s.mem.1.1.1 s.mem.2.1,
    uSet_subset hd (s := s') (t := s) (isMor_of_subset (reach_subset _ _) s.mem) he⟩
  rw [BTriple.cls_eq_cls]
  exact ⟨rfl, reach d s.V s.x, hV', fun z hz => ⟨hz, reach_subset _ _ hz⟩, θ', hθ',
    faceExt_self hd hV'.1.1.1 hθ'.1, he⟩

open scoped Classical in
/-- The inverse `Φ_{(x,V,θ)}⁻¹ : θ ∩ V^x → U(x, V, θ)` of 2021 Definition 2.7.11, as a total map
`θ → bX` (with the junk value `[x, V, θ]` off the image `θ ∩ V^x` of `Φ`). -/
def phiInv (t : BTriple hd) (y : t.θ) : BSpace hd :=
  if h : ∃ p ∈ uSet hd t, bMap hd p = y then h.choose else t.cls

/-- `Φ⁻¹(B(p)) = p` for `p ∈ U(x, V, θ)` (`Φ` is injective). -/
lemma phiInv_eq (t : BTriple hd) {y : t.θ} {p : BSpace hd} (hp : p ∈ uSet hd t)
    (hpy : bMap hd p = y) : phiInv hd t y = p := by
  have h : ∃ p ∈ uSet hd t, bMap hd p = y := ⟨p, hp, hpy⟩
  rw [phiInv, dif_pos h]
  exact bMap_injOn_uSet hd t h.choose_spec.1 hp (h.choose_spec.2.trans hpy.symm)

/-- On `θ ∩ V^x`, `Φ⁻¹` lands in `U(x, V, θ)` and `Φ ∘ Φ⁻¹ = id`. -/
lemma phiInv_spec (t : BTriple hd) {y : t.θ} (hy : (y : X) ∈ reach d t.V t.x) :
    phiInv hd t y ∈ uSet hd t ∧ bMap hd (phiInv hd t y) = y := by
  have : (y : X) ∈ bMap hd '' uSet hd t := by rw [bMap_image_uSet hd]; exact ⟨y.2, hy⟩
  obtain ⟨p, hp, hpy⟩ := this
  rw [phiInv_eq hd t hp hpy]
  exact ⟨hp, hpy⟩

lemma phiInv_bMap (t : BTriple hd) {p : BSpace hd} (hp : p ∈ uSet hd t) :
    phiInv hd t ⟨bMap hd p, bMap_mem_of_mem_uSet hd hp⟩ = p :=
  phiInv_eq hd t hp rfl

/-- `B(U(x, V, θ)) ⊆ V^x`. -/
lemma bMap_mem_reach (t : BTriple hd) {p : BSpace hd} (hp : p ∈ uSet hd t) :
    bMap hd p ∈ reach d t.V t.x := by
  have : bMap hd p ∈ bMap hd '' uSet hd t := ⟨p, hp, rfl⟩
  rw [bMap_image_uSet hd] at this
  exact this.2

end TameBoundary

namespace MPolyfold

open TameBoundary

universe u v

section Helpers

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- Sc-smoothness on an open set is local (as `IsScSmoothOn.of_locally` of
`Polyfold/Chapter7/Discrete.lean`, restated to keep the imports of Chapter 2). -/
private theorem isScSmoothOn_of_locally_nc {f : X → Y} {U : Set X} (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ U' : Set X, IsOpen U' ∧ x ∈ U' ∧ U' ⊆ U ∧ P.IsScSmoothOn Q f U') :
    P.IsScSmoothOn Q f U := by
  have hcont : ContinuousOn f U := fun x hx => by
    obtain ⟨U', hU', hxU', -, hf⟩ := h x hx
    exact (hf.continuousOn.continuousAt (hU'.mem_nhds hxU')).continuousWithinAt
  refine IsScSmoothOn.of_exists_charts hU hcont fun x hx => ?_
  obtain ⟨U', hU', hxU', hU'U, hf⟩ := h x hx
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f x)
  set V := (U' ∩ φ.source) ∩ f ⁻¹' ψ.source with hV
  have hVo : IsOpen V := (hf.continuousOn.mono inter_subset_left).isOpen_inter_preimage
    (hU'.inter φ.isOpen_source) ψ.isOpen_source
  exact ⟨φ, ψ, V, hφ, hψ, hVo, ⟨⟨hxU', hxφ⟩, hfx⟩, fun y hy => ⟨hU'U hy.1.1, hy.1.2⟩,
    fun y hy => hy.2, hf.smooth φ ψ hφ hψ V hVo (fun y hy => hy.1) fun y hy => hy.2⟩

/-- A map into a sub-M-polyfold `A ⊆ Y` is sc-smooth into `A` as soon as it is sc-smooth into `Y`
(near `x`, `f = (i⁻¹ ∘ r) ∘ i ∘ f` for a retraction `r` onto `A`, Proposition 2.21 (2); as the
private `isScSmoothOn_subPolyfold_of_val` of `Polyfold/Chapter7/SubGroupoid.lean`). -/
private theorem isScSmoothOn_subPolyfold_of_val_nc {A : Set Y} (hA : Q.IsSubMPolyfold A)
    [ParacompactSpace A] {f : X → A} {U : Set X}
    (hf : P.IsScSmoothOn Q (fun x => (f x : Y)) U) :
    P.IsScSmoothOn (subPolyfold hA) f U := by
  refine isScSmoothOn_of_locally_nc hf.isOpen fun x hx => ?_
  set d := hA.data (f x).2
  have hU' : IsOpen (U ∩ (fun x => (f x : Y)) ⁻¹' d.V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen d.isOpen
  refine ⟨_, hU', ⟨hx, hA.mem_data_V (f x).2⟩, inter_subset_left, ?_⟩
  refine (IsScSmoothOn.comp (subPolyfold_retraction_isScSmooth hA d (f x))
    (hf.mono hU' inter_subset_left) fun y hy => hy.2).congr fun y hy => Subtype.ext ?_
  simp only [Function.comp_apply]
  rw [d.retractInto_val (f x) hy.2]
  exact d.apply_eq_self ⟨(f y).2, hy.2⟩

end Helpers

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- The image `θ ∩ V^x` of `Φ_{(x,V,θ)}`, as a subset of the face `θ`. -/
def reachSet (hP : P.IsTame) (t : BTriple (P.isCornerIndex_degIndex hP)) : Set t.θ :=
  {y | (y : X) ∈ reach P.degIndex t.V t.x}

theorem isOpen_reachSet (hP : P.IsTame) (t : BTriple (P.isCornerIndex_degIndex hP)) :
    IsOpen (P.reachSet hP t) :=
  (isOpen_reach (P.isCornerIndex_degIndex hP) t.mem.1.1.1 t.x).preimage continuous_subtype_val

/-- For `V` centred at `x` the image of `Φ_{(x,V,θ)}` is all of `θ`. -/
theorem reachSet_eq_univ_of_isCenteredAt (hP : P.IsTame)
    {t : BTriple (P.isCornerIndex_degIndex hP)} (ht : IsCenteredAt P.degIndex t.x t.V) :
    P.reachSet hP t = univ := by
  refine eq_univ_of_forall fun y => ?_
  change (y : X) ∈ reach P.degIndex t.V t.x
  rw [reach_eq_self_of_isCenteredAt ht]
  exact t.mem_faces.1.subset y.2

/-- `Φ_{(x,V,θ)}` is sc-smooth on `U(x, V, θ)` (any representative): `B` is sc-smooth
(Theorem 2.7.13 (3)) and `θ` is a sub-M-polyfold of `X`. -/
theorem phiTot_isScSmoothOn (hP : P.IsTame) (t : BTriple (P.isCornerIndex_degIndex hP)) :
    letI := P.paracompactSpace_subtype t.θ
    (P.tameBoundaryPolyfold hP).IsScSmoothOn (P.facePolyfold hP t.mem.1.1 t.mem_faces.1)
      (P.phiTot hP t) (uSet _ t) := by
  let _ := P.paracompactSpace_subtype t.θ
  refine isScSmoothOn_subPolyfold_of_val_nc
    (P.isSubMPolyfold_of_isFaceIn hP t.mem.1.1 t.mem_faces.1) ?_
  refine ((P.tameBoundaryMap_isScSmooth hP).mono (isOpen_uSet _ t) (subset_univ _)).congr
    fun p hp => ?_
  rw [P.phiTot_of_mem hp]
  rfl

/-- `Φ_{(x,V,θ)}⁻¹` is sc-smooth on the open set `θ ∩ V^x` of the face `θ` (any representative):
near `y₀ = B(p₀)` it is `Φ_{s'}⁻¹ ∘ j` for a centred triple `s'` with `p₀ ∈ U(s') ⊆ U(x, V, θ)`,
where `j` is the inclusion of the open piece `θ_{s'} = θ ∩ N` of `θ` into the face `θ_{s'}` (an
sc-smooth map, both faces being sub-M-polyfolds of `X`). -/
theorem phiInv_isScSmoothOn (hP : P.IsTame) (t : BTriple (P.isCornerIndex_degIndex hP)) :
    letI := P.paracompactSpace_subtype t.θ
    (P.facePolyfold hP t.mem.1.1 t.mem_faces.1).IsScSmoothOn (P.tameBoundaryPolyfold hP)
      (phiInv _ t) (P.reachSet hP t) := by
  classical
  let _ := P.paracompactSpace_subtype t.θ
  refine isScSmoothOn_of_locally_nc (P.isOpen_reachSet hP t) fun y₀ hy₀ => ?_
  obtain ⟨hp₀, hp₀y⟩ := phiInv_spec _ t hy₀
  obtain ⟨s, hs, hsU⟩ := (isOpen_iff_forall_uSet _).1 (isOpen_uSet _ t) _ hp₀
  obtain ⟨s', hs', hs'c, hs's⟩ := BTriple.exists_centred_subset _ s
  have hsub : uSet _ s' ⊆ uSet _ t := hs's.trans hsU
  obtain ⟨N, hN, hNe⟩ := exists_isOpen_bMap_image _ t (isOpen_uSet _ s')
  have hθ' : s'.θ = N ∩ t.θ := by
    rw [← bMap_image_uSet_of_isCenteredAt _ hs'c, ← hNe, inter_eq_left.2 hsub]
  have hp₀s' : phiInv _ t y₀ ∈ uSet _ s' := by
    rw [← hs, ← hs']; exact cls_mem_uSet _ s'
  set O : Set t.θ := {y | (y : X) ∈ N} with hOdef
  have hOo : IsOpen O := hN.preimage continuous_subtype_val
  have hOθ : ∀ y ∈ O, (y : X) ∈ s'.θ := fun y hy => by rw [hθ']; exact ⟨hy, y.2⟩
  have hy₀O : y₀ ∈ O := by
    have : (y₀ : X) ∈ s'.θ := by rw [← hp₀y]; exact bMap_mem_of_mem_uSet _ hp₀s'
    rw [hθ'] at this; exact this.1
  have hOR : O ⊆ P.reachSet hP t := by
    intro y hy
    have h1 : (y : X) ∈ bMap _ '' uSet _ s' := by
      rw [bMap_image_uSet_of_isCenteredAt _ hs'c]; exact hOθ y hy
    obtain ⟨q, hq, hqy⟩ := h1
    change (y : X) ∈ reach P.degIndex t.V t.x
    rw [← hqy]
    exact bMap_mem_reach _ t (hsub hq)
  refine ⟨O, hOo, hy₀O, hOR, ?_⟩
  let _ := P.paracompactSpace_subtype s'.θ
  -- the inclusion `j : θ ∩ N → θ_{s'}`
  let j : t.θ → s'.θ := fun y => if h : (y : X) ∈ s'.θ then ⟨y, h⟩ else ⟨s'.x, s'.mem_faces.2⟩
  have hj : ∀ y ∈ O, ((j y : s'.θ) : X) = y := fun y hy => by
    simp only [j, dif_pos (hOθ y hy)]
  have hjs : (P.facePolyfold hP t.mem.1.1 t.mem_faces.1).IsScSmoothOn
      (P.facePolyfold hP s'.mem.1.1 s'.mem_faces.1) j O := by
    refine isScSmoothOn_subPolyfold_of_val_nc
      (P.isSubMPolyfold_of_isFaceIn hP s'.mem.1.1 s'.mem_faces.1) ?_
    exact ((subPolyfold_inclusion_isScSmooth
      (P.isSubMPolyfold_of_isFaceIn hP t.mem.1.1 t.mem_faces.1)).mono hOo
      (subset_univ _)).congr fun y hy => (hj y hy).symm
  have hg := (P.phi_isScDiffeoOn hP s' hs'c).isScSmoothOn_inv
  refine (hg.comp hjs (mapsTo_univ _ _)).congr fun y hy => ?_
  symm
  refine phiInv_eq _ t (hsub (phiHomeomorph_symm_mem _ _)) ?_
  change bMap _ ((phiHomeomorph _ hs'c).symm (j y) : P.TameBoundarySpace hP) = y
  rw [bMap_phiHomeomorph_symm, hj y hy]

/-- **The characterization in 2021 Theorem 2.7.13, for every representative** (the strongest
version that holds as we read it): `Φ_{(x,V,θ)}` is an sc-diffeomorphism of the open set
`U(x, V, θ)` of `bX` onto the open subset `θ ∩ V^x` of the face `θ` with its natural structure,
with inverse `Φ⁻¹` (`phiInv`).  For `V` centred at `x`, `θ ∩ V^x = θ`
(`reachSet_eq_univ_of_isCenteredAt`) and this is `phi_isScDiffeoOn`; for other `V` the image can
be a proper subset of `θ` (`not_surjOn_phiTot_2021`). -/
theorem phi_isScDiffeoOn_nonCentred_2021 (hP : P.IsTame)
    (t : BTriple (P.isCornerIndex_degIndex hP)) :
    letI := P.paracompactSpace_subtype t.θ
    (P.tameBoundaryPolyfold hP).IsScDiffeoOn (P.facePolyfold hP t.mem.1.1 t.mem_faces.1)
      (P.phiTot hP t) (phiInv _ t) (uSet _ t) (P.reachSet hP t) := by
  let _ := P.paracompactSpace_subtype t.θ
  refine ⟨P.phiTot_isScSmoothOn hP t, P.phiInv_isScSmoothOn hP t, fun p hp => ?_,
    fun y hy => (phiInv_spec _ t hy).1, fun p hp => ?_, fun y hy => ?_⟩
  · change ((P.phiTot hP t p : t.θ) : X) ∈ reach P.degIndex t.V t.x
    rw [P.phiTot_of_mem hp]
    exact bMap_mem_reach _ t hp
  · rw [P.phiTot_of_mem hp]
    exact phiInv_bMap _ t hp
  · obtain ⟨h1, h2⟩ := phiInv_spec _ t hy
    rw [P.phiTot_of_mem h1]
    exact Subtype.ext h2

/-- For centred `V`, `phiInv` is `Φ⁻¹ = (phiHomeomorph)⁻¹`. -/
theorem phiInv_eq_phiHomeomorph_symm (hP : P.IsTame) {t : BTriple (P.isCornerIndex_degIndex hP)}
    (ht : IsCenteredAt P.degIndex t.x t.V) (y : t.θ) :
    phiInv _ t y = ((phiHomeomorph _ ht).symm y : P.TameBoundarySpace hP) :=
  phiInv_eq _ t (phiHomeomorph_symm_mem _ y) (bMap_phiHomeomorph_symm _ y)

/-- **The uniqueness in 2021 Theorem 2.7.13, with every representative**: an M-polyfold structure
`Q'` on `bX` for which, for every triple `(x, V, θ)`, `Φ_{(x,V,θ)}` is an sc-diffeomorphism of
`U(x, V, θ)` onto `θ ∩ V^x` is equivalent to `tameBoundaryPolyfold` (it has the property for the
centred triples, `tameBoundaryPolyfold_unique`).  The hypothesis is satisfiable
(`tameBoundaryPolyfold_satisfies_allReps_2021`). -/
theorem tameBoundaryPolyfold_unique_allReps_2021 (hP : P.IsTame)
    (Q' : MPolyfold (P.TameBoundarySpace hP))
    (h : ∀ t : BTriple (P.isCornerIndex_degIndex hP),
      letI := P.paracompactSpace_subtype t.θ
      Q'.IsScDiffeoOn (P.facePolyfold hP t.mem.1.1 t.mem_faces.1) (P.phiTot hP t) (phiInv _ t)
        (uSet _ t) (P.reachSet hP t)) :
    Q'.atlas.Equiv (P.tameBoundaryPolyfold hP).atlas := by
  refine P.tameBoundaryPolyfold_unique hP Q' fun t ht => ?_
  let _ := P.paracompactSpace_subtype t.θ
  have h1 := h t
  have hR : ∀ y, y ∈ P.reachSet hP t := fun y => by
    rw [P.reachSet_eq_univ_of_isCenteredAt hP ht]; exact mem_univ y
  have hg : ∀ y, phiInv _ t y = ((phiHomeomorph _ ht).symm y : P.TameBoundarySpace hP) :=
    P.phiInv_eq_phiHomeomorph_symm hP ht
  refine ⟨h1.isScSmoothOn, ?_, mapsTo_univ _ _, fun y _ => phiHomeomorph_symm_mem _ y,
    fun p hp => ?_, fun y _ => ?_⟩
  · exact (h1.isScSmoothOn_inv.congr fun y _ => hg y).mono isOpen_univ fun y _ => hR y
  · rw [← hg]; exact h1.left_inv p hp
  · rw [← hg]; exact h1.right_inv y (hR y)

/-- **Satisfiability of the hypothesis of `tameBoundaryPolyfold_unique_allReps_2021`**: the
structure `tameBoundaryPolyfold` itself satisfies it (`phi_isScDiffeoOn_nonCentred_2021`). -/
theorem tameBoundaryPolyfold_satisfies_allReps_2021 (hP : P.IsTame) :
    ∀ t : BTriple (P.isCornerIndex_degIndex hP),
      letI := P.paracompactSpace_subtype t.θ
      (P.tameBoundaryPolyfold hP).IsScDiffeoOn (P.facePolyfold hP t.mem.1.1 t.mem_faces.1)
        (P.phiTot hP t) (phiInv _ t) (uSet _ t) (P.reachSet hP t) :=
  P.phi_isScDiffeoOn_nonCentred_2021 hP

/-- **2021 Proposition 2.7.12, p. 83, for every pair of representatives** (centred or not): the
sets `Φ_{(x,V,θ)}(U ∩ U')` and `Φ_{(x',V',θ')}(U ∩ U')` are open in `θ`, `θ'` (with
`proposition_2_7_12_2021`), and the transition map `Φ_{(x',V',θ')} ∘ Φ_{(x,V,θ)}⁻¹` between them
is an sc-diffeomorphism (the faces with their natural structures), with inverse
`Φ_{(x,V,θ)} ∘ Φ_{(x',V',θ')}⁻¹`; on underlying points of `X` it is the identity. -/
theorem proposition_2_7_12_scDiffeo_nonCentred_2021 (hP : P.IsTame)
    (t t' : BTriple (P.isCornerIndex_degIndex hP)) :
    letI := P.paracompactSpace_subtype t.θ
    letI := P.paracompactSpace_subtype t'.θ
    IsOpen {y : t.θ | (y : X) ∈ bMap _ '' (uSet _ t ∩ uSet _ t')} ∧
      IsOpen {y : t'.θ | (y : X) ∈ bMap _ '' (uSet _ t ∩ uSet _ t')} ∧
      (P.facePolyfold hP t.mem.1.1 t.mem_faces.1).IsScDiffeoOn
        (P.facePolyfold hP t'.mem.1.1 t'.mem_faces.1)
        (P.phiTot hP t' ∘ phiInv _ t) (P.phiTot hP t ∘ phiInv _ t')
        {y : t.θ | (y : X) ∈ bMap _ '' (uSet _ t ∩ uSet _ t')}
        {y : t'.θ | (y : X) ∈ bMap _ '' (uSet _ t ∩ uSet _ t')} ∧
      ∀ y : t.θ, (y : X) ∈ bMap _ '' (uSet _ t ∩ uSet _ t') →
        ((P.phiTot hP t' (phiInv _ t y) : t'.θ) : X) = y := by
  let _ := P.paracompactSpace_subtype t.θ
  let _ := P.paracompactSpace_subtype t'.θ
  have h := P.phi_isScDiffeoOn_nonCentred_2021 hP t
  have h' := P.phi_isScDiffeoOn_nonCentred_2021 hP t'
  obtain ⟨⟨N, hN, hNe⟩, ⟨N', hN', hN'e⟩, -⟩ := P.proposition_2_7_12_2021 hP t t'
  set S := bMap (P.isCornerIndex_degIndex hP) '' (uSet _ t ∩ uSet _ t') with hSdef
  have hA : IsOpen {y : t.θ | (y : X) ∈ S} := by
    have : {y : t.θ | (y : X) ∈ S} = Subtype.val ⁻¹' N := by
      ext y
      change (y : X) ∈ S ↔ (y : X) ∈ N
      rw [hNe]; exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
    rw [this]; exact hN.preimage continuous_subtype_val
  have hA' : IsOpen {y : t'.θ | (y : X) ∈ S} := by
    have : {y : t'.θ | (y : X) ∈ S} = Subtype.val ⁻¹' N' := by
      ext y
      change (y : X) ∈ S ↔ (y : X) ∈ N'
      rw [hN'e]; exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
    rw [this]; exact hN'.preimage continuous_subtype_val
  -- the class over a point of `S`
  have hcls : ∀ (s : BTriple (P.isCornerIndex_degIndex hP)) (y : s.θ), (y : X) ∈ S →
      (s = t ∨ s = t') → ∃ p ∈ uSet _ t ∩ uSet _ t', phiInv _ s y = p ∧ bMap _ p = y := by
    rintro s y ⟨p, hp, hpy⟩ hs
    refine ⟨p, hp, phiInv_eq _ s ?_ hpy, hpy⟩
    rcases hs with rfl | rfl
    · exact hp.1
    · exact hp.2
  have hAR : {y : t.θ | (y : X) ∈ S} ⊆ P.reachSet hP t := by
    intro y hy
    obtain ⟨p, hp, -, hpy⟩ := hcls t y hy (Or.inl rfl)
    change (y : X) ∈ reach P.degIndex t.V t.x
    rw [← hpy]; exact bMap_mem_reach _ t hp.1
  have hA'R : {y : t'.θ | (y : X) ∈ S} ⊆ P.reachSet hP t' := by
    intro y hy
    obtain ⟨p, hp, -, hpy⟩ := hcls t' y hy (Or.inr rfl)
    change (y : X) ∈ reach P.degIndex t'.V t'.x
    rw [← hpy]; exact bMap_mem_reach _ t' hp.2
  -- the transition is the identity on points
  have hpt : ∀ y : t.θ, (y : X) ∈ S → ((P.phiTot hP t' (phiInv _ t y) : t'.θ) : X) = y := by
    intro y hy
    obtain ⟨p, hp, hpe, hpy⟩ := hcls t y hy (Or.inl rfl)
    rw [hpe, P.phiTot_of_mem hp.2]; exact hpy
  have hpt' : ∀ y : t'.θ, (y : X) ∈ S → ((P.phiTot hP t (phiInv _ t' y) : t.θ) : X) = y := by
    intro y hy
    obtain ⟨p, hp, hpe, hpy⟩ := hcls t' y hy (Or.inr rfl)
    rw [hpe, P.phiTot_of_mem hp.1]; exact hpy
  have hmem : ∀ y : t.θ, (y : X) ∈ S → phiInv _ t y ∈ uSet _ t' := by
    intro y hy
    obtain ⟨p, hp, hpe, -⟩ := hcls t y hy (Or.inl rfl)
    rw [hpe]; exact hp.2
  have hmem' : ∀ y : t'.θ, (y : X) ∈ S → phiInv _ t' y ∈ uSet _ t := by
    intro y hy
    obtain ⟨p, hp, hpe, -⟩ := hcls t' y hy (Or.inr rfl)
    rw [hpe]; exact hp.1
  refine ⟨hA, hA', ⟨?_, ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩, hpt⟩
  · exact IsScSmoothOn.comp h'.isScSmoothOn (h.isScSmoothOn_inv.mono hA hAR) hmem
  · exact IsScSmoothOn.comp h.isScSmoothOn (h'.isScSmoothOn_inv.mono hA' hA'R) hmem'
  · change (((P.phiTot hP t' (phiInv _ t y)) : t'.θ) : X) ∈ S
    rw [hpt y hy]; exact hy
  · change (((P.phiTot hP t (phiInv _ t' y)) : t.θ) : X) ∈ S
    rw [hpt' y hy]; exact hy
  · obtain ⟨p, hp, hpe, hpy⟩ := hcls t y hy (Or.inl rfl)
    change P.phiTot hP t (phiInv _ t' (P.phiTot hP t' (phiInv _ t y))) = y
    rw [hpe, P.phiTot_of_mem hp.2, phiInv_bMap _ t' hp.2, P.phiTot_of_mem hp.1]
    exact Subtype.ext hpy
  · obtain ⟨p, hp, hpe, hpy⟩ := hcls t' y hy (Or.inr rfl)
    change P.phiTot hP t' (phiInv _ t (P.phiTot hP t (phiInv _ t' y))) = y
    rw [hpe, P.phiTot_of_mem hp.1, phiInv_bMap _ t hp.1, P.phiTot_of_mem hp.2]
    exact Subtype.ext hpy

open TameBoundaryExample in
/-- **The characterization of 2021 Theorem 2.7.13 is not onto `θ` for every representative**, as
we read it: for the triple `(x, V, θ)` of `[0,∞)³` (`counterTriple`, `TameBoundaryExample.lean`),
`Φ_{(x,V,θ)}` does not map `U(x, V, θ)` onto `θ`; so it is an sc-diffeomorphism onto the proper
open subset `θ ∩ V^x` only (`phi_isScDiffeoOn_nonCentred_2021`). -/
theorem not_surjOn_phiTot_2021 (W : ScBanach) :
    ¬ SurjOn ((quadrantPolyfold 3 W).phiTot (quadrantPolyfold_isTame 3 W) (counterTriple W))
      (uSet _ (counterTriple W)) univ := by
  intro h
  have hyθ : pt W 0 1 0 ∈ (counterTriple W).θ := by
    rw [← seg_one]; exact seg_mem_slabFace W ⟨zero_le_one, le_rfl⟩
  obtain ⟨p, hp, hpy⟩ := h (mem_univ ⟨_, hyθ⟩)
  refine pt_010_not_mem_image W ⟨p, hp, ?_⟩
  rw [(quadrantPolyfold 3 W).phiTot_of_mem hp] at hpy
  exact congrArg Subtype.val hpy

end MPolyfold

end Polyfold
