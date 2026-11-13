import Polyfold.Chapter11.GapP2_H2FaceMeet

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.1: **Proposition 11.1.6** (2021 p. 524; 2017: Proposition 11.2, p. 378),
the intersection clause in corrected form.

# Two faces meet in a union of faces of each

## The text, paraphrased

(Proposition 11.1.6) For a face structured tame ep-groupoid `X`: if the intersection of two
faces `F` and `G` is nonempty, it is a face in `F` as well as in `G`.  As printed this does not
hold as we read it (`FaceMeetExample.not_facesMeetInFaces`, `GapP2_H2FaceMeet.lean`): the
intersection can have several components.

## What is formalized

* `MPolyfold.mem_closure_inter_faces`: in a tame M-polyfold, a point `x` of two distinct faces
  `F₁ ≠ F₂` is a limit of points of `F₁ ∩ F₂` with `d_X = 2`.  In a tame chart around `x`, with
  `o` the image of `x`, the faces are those of the components `F̂_i`, `F̂_j` of Lemma 4.C
  (`local_face_structure`) for two distinct indices `i ≠ j ∈ I(o)`, and the points
  `r(o + t y)`, `y` with `λ_i(y) = λ_j(y) = 0` and `λ_l(y) = 1` for the other `l ∈ I(o)`, have
  index `2` (tameness (1)) and lie in the closures of `F̂_i` and `F̂_j`.
* `EpGroupoid.IsEpFaceStructured.exists_nhds_degIndex_two`: near a point `y ∈ X_θ'` with
  `d_X(y) = 2`, every point with `d_X = 2` lies in `X_θ'` (it lies on the same two faces as `y`).
* **The corrected clause**: `EpGroupoid.IsEpFaceStructured.faceObj_inter_eq_sUnion` — for
  distinct faces `θ ≠ θ'` of `|X|`, `X_θ ∩ X_θ'` is the union of the faces of the ep-groupoid
  `X_θ` (Definition 11.1.3 for `faceEpGroupoid`) which it contains; `facesMeetInUnions` (both
  ways, `EpGroupoid.FacesMeetInUnionsOfFaces`).  The proof: a point `x ∈ X_θ ∩ X_θ'` is a limit
  of points with `d_X = 2` of `X_θ ∩ X_θ'`, which lie in a local piece of `{d_{X_θ} = 1}` at `x`;
  the face of `X_θ` through that piece contains `x`, and it lies in `X_θ'` because
  `X_θ' ∩ {d_{X_θ} = 1}` is open and closed in `{d_{X_θ} = 1}`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

open TameBoundary

universe u

/-! ### Points of index 2 on the intersection of two faces -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **The intersection of two distinct faces is the closure of its points of index 2** (near
each of its points): in a tame M-polyfold, a point `x` of two faces `F₁ ≠ F₂` is a limit of
points `v ∈ F₁ ∩ F₂` with `d_X(v) = 2`. -/
theorem mem_closure_inter_faces (hP : P.IsTame) {F₁ F₂ : Set X} (h₁ : P.IsFace F₁)
    (h₂ : P.IsFace F₂) (hne : F₁ ≠ F₂) {x : X} (hx₁ : x ∈ F₁) (hx₂ : x ∈ F₂) :
    x ∈ closure {v | v ∈ F₁ ∧ v ∈ F₂ ∧ P.degIndex v = 2} := by
  classical
  obtain ⟨φ, hφ, hx, htame⟩ := IsTame.exists_chart P hP x
  obtain ⟨R, hRO, hRt⟩ := htame
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hR := hRt n W T hT
  have hdeg : ∀ y ∈ φ.source, P.degIndex y = degIndexWith T (φ y) := fun y hy => by
    rw [P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hy, chartDegIndex,
      degIndex_eq T hT (φ.apply_mem_C hy)]
  set o := φ x with ho
  have hoO : o ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model x hx
  -- Lemma 4.C at `o`
  have key : ∀ i : Fin n, (T 0 o).1 i = 0 → ∃ p ∈ R.faceStratum,
      (∀ᶠ z in 𝓝 o, z ∈ φ.model.C → zeroSet T z = {i} →
        R z ∈ connectedComponentIn R.faceStratum p) ∧
      (∀ᶠ z in 𝓝 o, z ∈ φ.model.C → (T 0 z).1 i = 0 →
        R z ∈ closure (connectedComponentIn R.faceStratum p)) := by
    intro i hi
    obtain ⟨ε, hε, p, hpS, -, -, -, -, hB, hcl⟩ := local_face_structure hT hR hoO hi
    exact ⟨p, hpS, Filter.mem_of_superset (Metric.ball_mem_nhds o hε) fun z hz hzC hzI =>
      hB z ⟨hz, hzC⟩ hzI, Filter.mem_of_superset (Metric.ball_mem_nhds o hε) fun z hz hzC hzi =>
      hcl z ⟨hz, hzC⟩ hzi⟩
  choose! p hpS hpA hpcl using key
  have hev : ∀ᶠ z in 𝓝 o, zeroSet T z ⊆ zeroSet T o ∧ ∀ i ∈ zeroSet T o, z ∈ φ.model.C →
      zeroSet T z = {i} → R z ∈ connectedComponentIn R.faceStratum (p i) := by
    refine (eventually_zeroSet_subset T o).and ?_
    exact (Filter.eventually_all_finset _).2 fun i hi => hpA i ((mem_zeroSet T).1 hi)
  have hφc : ContinuousAt φ x := φ.continuousOn_toFun.continuousAt (φ.isOpen_source.mem_nhds hx)
  have hevx : ∀ᶠ y in 𝓝 x, y ∈ φ.source ∧ (zeroSet T (φ y) ⊆ zeroSet T o ∧
      ∀ i ∈ zeroSet T o, φ y ∈ φ.model.C → zeroSet T (φ y) = {i} →
        R (φ y) ∈ connectedComponentIn R.faceStratum (p i)) :=
    (show ∀ᶠ y in 𝓝 x, y ∈ φ.source from φ.isOpen_source.mem_nhds hx).and (hφc.eventually hev)
  have hsubO : ∀ i, connectedComponentIn R.faceStratum (p i) ⊆ φ.model.O := fun i z hz => by
    rw [← hRO]; exact (connectedComponentIn_subset _ _ hz).1
  -- the preconnected sets `φ⁻¹(F̂_i)` lie in `{d_X = 1}`
  have hK : ∀ i, IsPreconnected (φ.symm '' connectedComponentIn R.faceStratum (p i)) ∧
      φ.symm '' connectedComponentIn R.faceStratum (p i) ⊆ {y | P.degIndex y = 1} := by
    intro i
    refine ⟨isPreconnected_connectedComponentIn.image _ (φ.continuousOn_invFun.mono (hsubO i)),
      ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hzS := connectedComponentIn_subset _ _ hz
    have hy := φ.symm_mapsTo (hsubO i hz)
    change P.degIndex (φ.symm z) = 1
    rw [hdeg _ hy, φ.apply_symm_apply (hsubO i hz)]
    exact faceStratum_degIndexWith hT hzS
  have hKcc : ∀ i, (T 0 o).1 i = 0 → φ.symm '' connectedComponentIn R.faceStratum (p i) ⊆
      connectedComponentIn {y | P.degIndex y = 1} (φ.symm (p i)) := fun i hi =>
    (hK i).1.subset_connectedComponentIn ⟨p i, mem_connectedComponentIn (hpS i hi), rfl⟩ (hK i).2
  -- every face through `x` is the face of one `F̂_i`
  have hlabel : ∀ F, P.IsFace F → x ∈ F → ∃ i ∈ zeroSet T o,
      F = closure (connectedComponentIn {y | P.degIndex y = 1} (φ.symm (p i))) := by
    rintro F ⟨y₀, -, rfl⟩ hxF
    obtain ⟨y, hyN, hyG⟩ := mem_closure_iff_nhds.1 hxF _ hevx
    obtain ⟨hyV, hysub, hyB⟩ := hyN
    have hy1 := connectedComponentIn_subset {y | P.degIndex y = 1} y₀ hyG
    change P.degIndex y = 1 at hy1
    have hyC : φ y ∈ φ.model.C := φ.apply_mem_C hyV
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1
      ((degIndexWith_eq_card_zeroSet T _).symm.trans ((hdeg y hyV).symm.trans hy1))
    have hio : i ∈ zeroSet T o := hysub (by rw [hi]; exact Finset.mem_singleton_self i)
    have hRy := hyB i hio hyC hi
    have hφyO : φ y ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model y hyV
    rw [R.apply_eq_self_of_mem_retract hφyO] at hRy
    have hyK : y ∈ φ.symm '' connectedComponentIn R.faceStratum (p i) :=
      ⟨φ y, hRy, φ.symm_apply_apply hyV⟩
    have hsub := (hK i).1.subset_connectedComponentIn hyK (hK i).2
    have hpmem : φ.symm (p i) ∈ φ.symm '' connectedComponentIn R.faceStratum (p i) :=
      ⟨p i, mem_connectedComponentIn (hpS i ((mem_zeroSet T).1 hio)), rfl⟩
    refine ⟨i, hio, ?_⟩
    rw [connectedComponentIn_eq hyG, connectedComponentIn_eq (hsub hpmem)]
  obtain ⟨i₁, hi₁, hF₁⟩ := hlabel F₁ h₁ hx₁
  obtain ⟨i₂, hi₂, hF₂⟩ := hlabel F₂ h₂ hx₂
  have hi : i₁ ≠ i₂ := fun h => hne (by rw [hF₁, hF₂, h])
  -- the ray `o + t y`, `λ_{i₁}(y) = λ_{i₂}(y) = 0`, `λ_l(y) = 1` on the rest of `I(o)`
  set b : Fin n → ℝ := fun l => if l ∈ zeroSet T o ∧ l ≠ i₁ ∧ l ≠ i₂ then 1 else 0 with hb
  set y := coordVec T b with hy
  have hlin : ∀ (t : ℝ) l, (T 0 (o + t • y)).1 l = (T 0 o).1 l + t * b l := fun t l => by
    simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hy]
    rw [coord_coordVec]
  have hoC : o ∈ φ.model.C := φ.apply_mem_C hx
  have hb0 : ∀ l, 0 ≤ b l := fun l => by simp only [hb]; split_ifs <;> norm_num
  have hzC : ∀ t : ℝ, 0 ≤ t → o + t • y ∈ φ.model.C := by
    intro t ht
    rw [hT]
    intro l
    rw [hlin]
    exact add_nonneg (coord_nonneg hT hoC l) (mul_nonneg ht (hb0 l))
  have hzI : ∀ t : ℝ, 0 < t → zeroSet T (o + t • y) = {i₁, i₂} := by
    intro t ht
    ext l
    rw [mem_zeroSet, hlin, Finset.mem_insert, Finset.mem_singleton]
    by_cases hl : l ∈ zeroSet T o
    · rw [(mem_zeroSet T).1 hl, zero_add]
      by_cases h1 : l = i₁
      · rw [h1]; simp [hb]
      by_cases h2 : l = i₂
      · rw [h2]; simp [hb]
      · simp [hb, hl, h1, h2, ht.ne']
    · have hpos : 0 < (T 0 o).1 l := lt_of_le_of_ne (coord_nonneg hT hoC l)
        (Ne.symm fun h => hl ((mem_zeroSet T).2 h))
      have hbl : b l = 0 := by simp [hb, hl]
      rw [hbl, mul_zero, add_zero]
      constructor
      · intro h; exact absurd h hpos.ne'
      · rintro (rfl | rfl)
        exacts [absurd hi₁ hl, absurd hi₂ hl]
  have hzt : Tendsto (fun t : ℝ => o + t • y) (𝓝[>] 0) (𝓝 o) := by
    have : Continuous fun t : ℝ => o + t • y := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨V₀, hV₀, hUV⟩ := R.relOpen.relOpen
  have hoU : o ∈ R.U := R.retract_subset hoO
  have hoV₀ : o ∈ V₀ := (hUV ▸ hoU).1
  have hzU : ∀ᶠ t in 𝓝[>] (0 : ℝ), o + t • y ∈ R.U := by
    filter_upwards [self_mem_nhdsWithin, hzt.eventually (hV₀.mem_nhds hoV₀)] with t ht htV
    rw [hUV]
    exact ⟨htV, hzC t (le_of_lt ht)⟩
  have hRo : R o = o := R.apply_eq_self_of_mem_retract hoO
  have hRz : Tendsto (fun t : ℝ => R (o + t • y)) (𝓝[>] 0) (𝓝 o) := by
    have hc := (R.isSc1.isSc0.continuousOn_base o hoU).tendsto
    rw [hRo] at hc
    exact hc.comp (tendsto_nhdsWithin_iff.2 ⟨hzt, hzU⟩)
  have hRzO : ∀ᶠ t in 𝓝[>] (0 : ℝ), R (o + t • y) ∈ φ.model.O :=
    hzU.mono fun t ht => by rw [← hRO]; exact R.apply_mem_retract ht
  have hoO' : o ∈ φ.model.O := by rw [← hRO]; exact hoO
  have hv : Tendsto (fun t : ℝ => φ.symm (R (o + t • y))) (𝓝[>] 0) (𝓝 x) := by
    have hc := (φ.continuousOn_invFun o hoO').tendsto
    have e : φ.toPartialEquiv.symm o = x := φ.symm_apply_apply hx
    rw [e] at hc
    exact hc.comp (tendsto_nhdsWithin_iff.2 ⟨hRz, hRzO⟩)
  -- the points `φ⁻¹(r(o + t y))` lie on `F₁ ∩ F₂` and have index `2`
  have hmemF : ∀ i, (T 0 o).1 i = 0 → ∀ q ∈ φ.model.O,
      q ∈ closure (connectedComponentIn R.faceStratum (p i)) →
        φ.symm q ∈ closure (connectedComponentIn {y | P.degIndex y = 1} (φ.symm (p i))) :=
    fun i hi q hq hqcl => closure_mono (hKcc i hi)
      (((φ.continuousOn_invFun q hq).mono (hsubO i)).mem_closure_image hqcl)
  have hi₁o := (mem_zeroSet T).1 hi₁
  have hi₂o := (mem_zeroSet T).1 hi₂
  refine mem_closure_of_tendsto hv ?_
  filter_upwards [self_mem_nhdsWithin, hzU, hRzO, hzt.eventually (hpcl i₁ hi₁o),
    hzt.eventually (hpcl i₂ hi₂o)] with t ht htU htO hc₁ hc₂
  have htC := hzC t (le_of_lt ht)
  have hI := hzI t ht
  have hz₁ : (T 0 (o + t • y)).1 i₁ = 0 := by
    rw [← mem_zeroSet T, hI]; exact Finset.mem_insert_self _ _
  have hz₂ : (T 0 (o + t • y)).1 i₂ = 0 := by
    rw [← mem_zeroSet T, hI]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  refine ⟨?_, ?_, ?_⟩
  · rw [hF₁]; exact hmemF i₁ hi₁o _ htO (hc₁ htC hz₁)
  · rw [hF₂]; exact hmemF i₂ hi₂o _ htO (hc₂ htC hz₂)
  · rw [hdeg _ (φ.symm_mapsTo htO), φ.apply_symm_apply htO,
      ← degIndex_eq T hT (R.U_subset_C (R.mapsTo htU)), hR.degIndex_apply _ htU,
      degIndex_eq T hT (R.U_subset_C htU), degIndexWith_eq_card_zeroSet, hI, Finset.card_pair hi]

end MPolyfold

/-! ### The corrected intersection clause -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- Near a point `y ∈ X_θ'` with `d_X(y) = 2`, every point with `d_X = 2` lies in `X_θ'`: it lies
on exactly two faces of the object M-polyfold, which are among the two through `y`. -/
theorem IsEpFaceStructured.exists_nhds_degIndex_two (hX : X.IsEpFaceStructured)
    {θ' : Set X.OrbitSpace} (hθ' : X.IsOrbitFace θ') {y : Obj} (hy : y ∈ X.faceObj θ')
    (hy2 : X.PObj.degIndex y = 2) :
    ∃ B, IsOpen B ∧ y ∈ B ∧ ∀ u ∈ B, X.PObj.degIndex u = 2 → u ∈ X.faceObj θ' := by
  have hd := MPolyfold.isCornerIndex_degIndex X.PObj hX.1
  obtain ⟨L⟩ := hd.exists_localPieces (univ_mem : (univ : Set Obj) ∈ 𝓝 y)
  obtain ⟨F, hF, hyF, hFθ, -⟩ := hX.existsUnique_face_subset hθ' hy
  have hws : ∀ z, (facesThrough X.PObj.degIndex univ z).encard = X.PObj.degIndex z := by
    intro z
    have he : {F : Set Obj | X.PObj.IsFace F ∧ z ∈ F} = facesThrough X.PObj.degIndex univ z := by
      ext F
      exact and_congr_left' X.PObj.isFaceIn_univ_iff.symm
    rw [← he]
    exact hX.isWeaklyFaceStructured.2 z
  refine ⟨L.B, L.isOpen_B, L.mem_B, fun u hu hu2 => hFθ ?_⟩
  have hsub := L.facesThrough_subset (mem_univ y) hu
  have hfin : (facesThrough X.PObj.degIndex univ u).Finite :=
    finite_of_encard_eq_coe (by rw [hws u, hu2])
  have heq := hfin.eq_of_subset_of_encard_le hsub (by rw [hws u, hws y, hu2, hy2])
  have hmem : F ∈ facesThrough X.PObj.degIndex univ y := ⟨hF, hyF⟩
  rw [← heq] at hmem
  exact hmem.2

/-- Two distinct faces `X_θ ≠ X_θ'` contain distinct faces of the object M-polyfold. -/
theorem IsEpFaceStructured.face_ne_of_subset (hX : X.IsEpFaceStructured)
    {θ θ' : Set X.OrbitSpace} (hθ : X.IsOrbitFace θ) (hθ' : X.IsOrbitFace θ') (hne : θ ≠ θ')
    {F : Set Obj} (hF : IsFaceIn X.PObj.degIndex univ F) (hFθ : F ⊆ X.faceObj θ)
    (hFθ' : F ⊆ X.faceObj θ') : False := by
  have hd := MPolyfold.isCornerIndex_degIndex X.PObj hX.1
  obtain ⟨p, -, hp1, rfl⟩ := hF
  have hpF := mem_faceAt_self (mem_univ p) hp1
  have hq : X.degIndexOrbit (X.π p) = 1 := hp1
  have key : ∀ {θ}, X.IsOrbitFace θ → X.π p ∈ θ → θ = faceAt X.degIndexOrbit univ (X.π p) := by
    intro θ hθ hpθ
    obtain ⟨w, -, -, rfl⟩ := isOrbitFace_iff_isFaceIn.1 hθ
    exact faceAt_orbit_eq_of_mem hd hq hpθ
  exact hne ((key hθ (hFθ hpF)).trans (key hθ' (hFθ' hpF)).symm)

/-- **Corrected form of the intersection clause of 2021 Proposition 11.1.6, p. 524 (2017:
Proposition 11.2, p. 378)**: for distinct faces `θ ≠ θ'` of `|X|`, `X_θ ∩ X_θ'` is the union of
the faces of the ep-groupoid `X_θ` which it contains. -/
theorem IsEpFaceStructured.faceObj_inter_eq_sUnion (hX : X.IsEpFaceStructured)
    {θ θ' : Set X.OrbitSpace} (hθ : X.IsOrbitFace θ) (hθ' : X.IsOrbitFace θ') (hne : θ ≠ θ') :
    (Subtype.val ⁻¹' X.faceObj θ' : Set (X.faceObj θ)) =
      ⋃₀ {A | (faceEpGroupoid hX hθ).IsEpFace A ∧ A ⊆ Subtype.val ⁻¹' X.faceObj θ'} := by
  refine Subset.antisymm (fun x hx => ?_) (sUnion_subset fun A hA => hA.2)
  set G := faceEpGroupoid hX hθ with hGdef
  have hA := isEpSubgroupoid_faceObj hX hθ
  have hdeg : ∀ v : X.faceObj θ, X.PObj.degIndex v = G.PObj.degIndex v + 1 :=
    degIndex_faceEpGroupoid hX hθ
  -- the faces of the object M-polyfold through `x` in `X_θ` and in `X_θ'`
  obtain ⟨F₁, hF₁, hxF₁, hF₁θ, -⟩ := hX.existsUnique_face_subset hθ x.2
  obtain ⟨F₂, hF₂, hxF₂, hF₂θ', -⟩ := hX.existsUnique_face_subset hθ' hx
  have hF₁₂ : F₁ ≠ F₂ := fun h =>
    hX.face_ne_of_subset hθ hθ' hne hF₁ hF₁θ (h ▸ hF₂θ')
  have hcl := MPolyfold.mem_closure_inter_faces X.PObj hX.1 (X.PObj.isFaceIn_univ_iff.1 hF₁)
    (X.PObj.isFaceIn_univ_iff.1 hF₂) hF₁₂ hxF₁ hxF₂
  -- a local piece of `{d_{X_θ} = 1}` at `x` meeting `X_θ'`
  have hdG := MPolyfold.isCornerIndex_degIndex G.PObj (isTame_faceEpGroupoid hX hθ)
  obtain ⟨L⟩ := hdG.exists_localPieces (univ_mem : (univ : Set (X.faceObj θ)) ∈ 𝓝 x)
  obtain ⟨B', hB'o, hB'⟩ := isOpen_induced_iff.1 L.isOpen_B
  have hxB' : (x : Obj) ∈ B' := by
    have := L.mem_B; rw [← hB'] at this; exact this
  obtain ⟨v, hvB', hvF₁, hvF₂, hv2⟩ := mem_closure_iff.1 hcl B' hB'o hxB'
  set v' : X.faceObj θ := ⟨v, hF₁θ hvF₁⟩
  have hv'1 : G.PObj.degIndex v' = 1 := by
    have h := hdeg v'
    change X.PObj.degIndex v = _ at h
    omega
  have hv'B : v' ∈ L.B := by rw [← hB']; exact hvB'
  obtain ⟨i, hvi⟩ := mem_iUnion.1 (L.cover ⟨hv'B, hv'1⟩)
  -- the face of `X_θ` through that piece
  set w := G.π (L.pt i)
  set η := faceAt G.degIndexOrbit univ w
  have hη : G.IsOrbitFace η := isOrbitFace_iff_isFaceIn.2 (isFaceIn_faceAt (mem_univ _)
    (degIndex_pt L i))
  refine ⟨G.faceObj η, ⟨⟨η, hη, rfl⟩, ?_⟩, mem_orbitFaceAt_pt L i⟩
  -- it lies in `X_θ'`: `X_θ' ∩ {d_{X_θ} = 1}` is open and closed in `{d_{X_θ} = 1}`
  set g := (subEpFunctor hA).orbitMap
  have hg : Continuous g := EpFunctor.continuous_orbitMap _
  have hgπ : ∀ y : X.faceObj θ, g (G.π y) = X.π y := fun _ => rfl
  have hθ'c : IsClosed θ' := by obtain ⟨z, -, rfl⟩ := hθ'; exact isClosed_closure
  set S := univ ∩ {z | G.degIndexOrbit z = 1}
  have hcc : connectedComponentIn S w ⊆ S ∩ g ⁻¹' θ' := by
    have hsub : G.π '' L.piece i ⊆ connectedComponentIn S w :=
      ((L.isPreconnected i).image _ G.continuous_π.continuousOn).subset_connectedComponentIn
        (mem_image_of_mem _ (L.pt_mem i)) (by
          rintro _ ⟨z, hz, rfl⟩
          exact ⟨mem_univ _, (L.piece_subset i hz).2⟩)
    refine subset_of_relClopen_of_isPreconnected isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _) (hθ'c.preimage hg) rfl ?_
      (hsub (mem_image_of_mem _ hvi)) ⟨⟨mem_univ _, hv'1⟩, hF₂θ' hvF₂⟩
    rintro e ⟨⟨-, he1⟩, heθ'⟩
    obtain ⟨y, rfl⟩ := G.surjective_π e
    have hy2 : X.PObj.degIndex y = 2 := by
      have h := hdeg y
      have h1 : G.PObj.degIndex y = 1 := he1
      omega
    obtain ⟨B, hBo, hyB, hB⟩ := hX.exists_nhds_degIndex_two hθ' (y := y) heθ' hy2
    refine ⟨G.π '' (Subtype.val ⁻¹' B),
      (G.proposition_7_1_8 _ (hBo.preimage continuous_subtype_val)).mem_nhds
        (mem_image_of_mem _ hyB), ?_⟩
    rintro _ ⟨⟨-, hz1⟩, ⟨u, huB, rfl⟩⟩
    refine ⟨⟨mem_univ _, hz1⟩, ?_⟩
    have hu2 : X.PObj.degIndex u = 2 := by
      have h := hdeg u
      have h1 : G.PObj.degIndex u = 1 := hz1
      omega
    exact hB u huB hu2
  intro y hy
  change X.π y ∈ θ'
  rw [← hgπ]
  have hη' : η ⊆ g ⁻¹' θ' := fun z hz =>
    closure_minimal (fun z hz => (hcc hz).2) (hθ'c.preimage hg) hz.2
  exact hη' hy

/-- The corrected clause of Proposition 11.1.6: for distinct faces `X_θ ≠ X_θ'` of `X`,
`X_θ ∩ X_θ'` is a union of faces of the ep-groupoid `X_θ` and a union of faces of `X_θ'`. -/
def FacesMeetInUnionsOfFaces (X : EpGroupoid Obj Mor) (hX : X.IsEpFaceStructured) : Prop :=
  ∀ (θ θ' : Set X.OrbitSpace) (hθ : X.IsOrbitFace θ) (hθ' : X.IsOrbitFace θ'), θ ≠ θ' →
    (Subtype.val ⁻¹' X.faceObj θ' : Set (X.faceObj θ)) =
        ⋃₀ {A | (faceEpGroupoid hX hθ).IsEpFace A ∧ A ⊆ Subtype.val ⁻¹' X.faceObj θ'} ∧
      (Subtype.val ⁻¹' X.faceObj θ : Set (X.faceObj θ')) =
        ⋃₀ {A | (faceEpGroupoid hX hθ').IsEpFace A ∧ A ⊆ Subtype.val ⁻¹' X.faceObj θ}

/-- **2021 Proposition 11.1.6, p. 524 (2017: Proposition 11.2, p. 378), the intersection clause
in corrected form**: in a face structured tame ep-groupoid two distinct faces meet in a union of
faces of each.  (As printed, "a face of each", the clause does not hold as we read it:
`FaceMeetExample.not_facesMeetInFaces`.) -/
theorem IsEpFaceStructured.facesMeetInUnions (hX : X.IsEpFaceStructured) :
    FacesMeetInUnionsOfFaces X hX := fun _ _ hθ hθ' hne =>
  ⟨hX.faceObj_inter_eq_sUnion hθ hθ' hne, hX.faceObj_inter_eq_sUnion hθ' hθ (Ne.symm hne)⟩

end EpGroupoid

end Polyfold
