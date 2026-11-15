import Polyfold.Chapter9.StokesFaceSum
import Polyfold.Chapter6.CornerSmoothMaps

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4,
**Theorem 4.4.7** (Stokes, p. 199) and the proof of **Theorem 6.7.1** (p. 278): the boundary
integral of a manifold with corners whose boundary contains embedded copies of other manifolds
(the ends `\{i\} × S_{F_i}` of the cobordism `S_F ⊆ [0, 1] × X`).

# The boundary integral with ends

`Z` is an M-polyfold with a corner structure of dimension `n + 1`, face-structured
(Definition 2.5.10, the reading of Theorem 4.4.7's "boundary a union of smooth faces"), and
`j i : A i → Z` (`i` in a finite type) are embeddings of M-polyfolds with corner structures of
dimension `n` such that

* `d_Z(j_i x) = d_{A_i}(x) + 1` (for the ends of a cobordism: `degIndex_interval_cobordism_end`),
* `range j_i` is closed and, among the points of `Z` of degeneracy index `1`, relatively open,
* the ranges are pairwise disjoint, and the inverse of `j_i` on every face contained in
  `range j_i` is smooth.

## What is formalized

* `face_subset_range_of_degIndex_eq_one`: a face of `Z` through a point of `range j` of
  degeneracy index `1` lies in `range j`.
* `exists_isPreconnected_end`: near a point of `range j`, the points of `range j` of degeneracy
  index `1` form a preconnected set accumulating at the point (the interior points of a corner
  chart of `A`).
* `exists_face_end`, `face_eq_of_subset_range`, `range_inter_goodSet_subset`: near every
  `x₀ ∈ Z`, `range j` meets the good region of `x₀` (`goodSet`) in exactly one face through `x₀`.
* `endFaceChartPair`: for that face, the face chart pair of the face (`FaceData.pair`) composed
  with `j` is a face chart pair of `j` (`FaceChartPair`), in the same chart of `Z`, with the same
  coordinate.
* `endGoodRegion`: the good regions of `Z` for the family consisting of the maps `j_i` and the
  faces of `Z` contained in no `range j_i` (the lateral faces).
* **`boundaryIntegral_eq_sum_ends_add_lateral`**: for a `C¹` `n`-form `ω` on compact `Z`,
  `∫_{∂Z} ω = ∑ᵢ ∫_{A i} j_i^*ω + ∑_F ∫_F ω|_F`, the second sum over the lateral faces, every
  `A i` and every face with the induced orientation (outward vector first);
  `exists_isInducedOrientation_end`: the induced orientation of `A i` exists and is continuous.
-/

open Set Filter Topology Manifold Module

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Mathlib's model with corners `[0,∞)ⁿ ⊆ ℝⁿ`. -/
local notation "𝓠" => modelWithCornersEuclideanQuadrant

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}
  {n : ℕ} {A : Type u} [TopologicalSpace A] [T2Space A] [ParacompactSpace A] {PA : MPolyfold A}
  {j : A → Z}

/-! ### The faces through the ends -/

section Ends

omit [TopologicalSpace A] [T2Space A] [ParacompactSpace A] in
/-- **A face through a point of `range j` of degeneracy index `1` lies in `range j`**, if
`range j` is closed and relatively open in `\{d_Z = 1\}`: the component of `\{d_Z = 1\}` of the
point lies in `range j`, and so does its closure. -/
theorem face_subset_range_of_degIndex_eq_one (hfs : Q.IsFaceStructured)
    (hjc : IsClosed (range j))
    (hE1 : ∀ p ∈ range j, Q.degIndex p = 1 → ∀ᶠ z in 𝓝 p, Q.degIndex z = 1 → z ∈ range j)
    {F : Set Z} (hF : Q.IsFace F) {p : Z} (hpF : p ∈ F) (hpj : p ∈ range j)
    (hp1 : Q.degIndex p = 1) : F ⊆ range j := by
  set D := {y | Q.degIndex y = 1}
  have hpD : p ∈ D := hp1
  have hFp : F = closure (connectedComponentIn D p) :=
    face_eq_of_degIndex_eq_one hfs hp1 hF ⟨p, hp1, rfl⟩ hpF
      (subset_closure (mem_connectedComponentIn hpD))
  set O := {z | ∀ᶠ w in 𝓝 z, w ∈ D → w ∈ range j}
  have hO : IsOpen O := isOpen_setOfPred_eventually_nhds
  have hOD : ∀ z ∈ O, z ∈ D → z ∈ range j := fun z hz hzD => hz.self_of_nhds hzD
  have hsub : connectedComponentIn D p ⊆ O ∪ (range j)ᶜ := fun z hz => by
    by_cases hzj : z ∈ range j
    · exact Or.inl (hE1 z hzj (connectedComponentIn_subset D p hz))
    · exact Or.inr hzj
  have hdisj : connectedComponentIn D p ∩ (O ∩ (range j)ᶜ) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and, not_not]
    exact fun hz hzO => hOD z hzO (connectedComponentIn_subset D p hz)
  rcases isPreconnected_iff_subset_of_disjoint.1 isPreconnected_connectedComponentIn O
      (range j)ᶜ hO hjc.isOpen_compl hsub hdisj with h | h
  · rw [hFp]
    exact closure_minimal (fun z hz => hOD z (h hz) (connectedComponentIn_subset D p hz)) hjc
  · exact absurd hpj (h (mem_connectedComponentIn hpD))

/-- **Near a point of `range j`, the points of `range j` of degeneracy index `1` are
preconnected and accumulate at the point**: in a corner chart of `A` at `j⁻¹(p)` they are the
images of the points of a small ball with all coordinates positive (`d_A = 0`, so `d_Z = 1`). -/
theorem exists_isPreconnected_end (hj : IsEmbedding j) (hcsA : PA.HasCornerStructureOfDim n)
    (hd : ∀ x, Q.degIndex (j x) = PA.degIndex x + 1) {p : Z} (hp : p ∈ range j) {G : Set Z}
    (hG : IsOpen G) (hpG : p ∈ G) :
    ∃ O, IsOpen O ∧ p ∈ O ∧ O ⊆ G ∧
      IsPreconnected (range j ∩ O ∩ {z | Q.degIndex z = 1}) ∧
      p ∈ closure (range j ∩ O ∩ {z | Q.degIndex z = 1}) := by
  obtain ⟨x, rfl⟩ := hp
  obtain ⟨κ, hxκ⟩ := hcsA.exists_cornerCoords x
  set y₀ := κ.coord x
  set K := κ.W ∩ {y : Fin n → ℝ | ∀ i, 0 ≤ y i}
  have hy₀K : y₀ ∈ K := ⟨κ.coord_mem_W hxκ, κ.coord_nonneg hxκ⟩
  have hinv : κ.coordInv y₀ = x := κ.coordInv_coord hxκ
  have hcont : ContinuousWithinAt κ.coordInv K y₀ := κ.continuousOn_coordInv y₀ hy₀K
  have hφ : ContinuousWithinAt (j ∘ κ.coordInv) K y₀ :=
    hj.continuous.continuousAt.comp_continuousWithinAt hcont
  have h1 : ∀ᶠ y in 𝓝[K] y₀, (j ∘ κ.coordInv) y ∈ G :=
    hφ.preimage_mem_nhdsWithin (hG.mem_nhds (by simpa [hinv] using hpG))
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.mem_nhdsWithin_iff.1 h1
  obtain ⟨r₂, hr₂, hr₂'⟩ := Metric.isOpen_iff.1 κ.isOpen_W y₀ hy₀K.1
  set ρ := min r₁ r₂
  have hρ : 0 < ρ := lt_min hr₁ hr₂
  have hballW : Metric.ball y₀ ρ ⊆ κ.W :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans hr₂'
  have hballG : ∀ y ∈ Metric.ball y₀ ρ, (∀ i, 0 ≤ y i) → j (κ.coordInv y) ∈ G := fun y hy hy0 =>
    hr₁' ⟨Metric.ball_subset_ball (min_le_left _ _) hy, hballW hy, hy0⟩
  set U' := κ.s ∩ κ.coord ⁻¹' Metric.ball y₀ ρ
  have hU'o : IsOpen U' := κ.isOpen_inter_preimage_coord Metric.isOpen_ball
  obtain ⟨T, hTo, hTU⟩ := hj.isInducing.isOpen_iff.1 hU'o
  have hxT : x ∈ j ⁻¹' T := by rw [hTU]; exact ⟨hxκ, Metric.mem_ball_self hρ⟩
  set Pos := Metric.ball y₀ ρ ∩ {y : Fin n → ℝ | ∀ i, 0 < y i}
  have hEq : range j ∩ (T ∩ G) ∩ {z | Q.degIndex z = 1} = (j ∘ κ.coordInv) '' Pos := by
    ext z
    constructor
    · rintro ⟨⟨⟨w, rfl⟩, hwT, -⟩, hw1⟩
      have hwU : w ∈ U' := by rw [← hTU]; exact hwT
      have hd0 : PA.degIndex w = 0 := by
        have h := hd w
        rw [show Q.degIndex (j w) = 1 from hw1] at h
        omega
      rw [κ.degIndex_eq_card hwU.1, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hd0
      refine ⟨κ.coord w, ⟨hwU.2, fun i => lt_of_le_of_ne (κ.coord_nonneg hwU.1 i)
        (Ne.symm (hd0 (Finset.mem_univ i)))⟩, ?_⟩
      simp only [Function.comp_apply, κ.coordInv_coord hwU.1]
    · rintro ⟨y, ⟨hyb, hyp⟩, rfl⟩
      have hy0 : ∀ i, 0 ≤ y i := fun i => (hyp i).le
      have hmem := κ.coordInv_mem (hballW hyb) hy0
      have hcy := κ.coord_coordInv (hballW hyb) hy0
      refine ⟨⟨⟨_, rfl⟩, ?_, hballG y hyb hy0⟩, ?_⟩
      · change κ.coordInv y ∈ j ⁻¹' T
        rw [hTU]
        exact ⟨hmem, by rw [mem_preimage, hcy]; exact hyb⟩
      · change Q.degIndex (j (κ.coordInv y)) = 1
        rw [hd, κ.degIndex_eq_card hmem, hcy, Finset.card_eq_zero.2]
        exact Finset.filter_eq_empty_iff.2 fun i _ => (hyp i).ne'
  have hKPos : Pos ⊆ K := fun y hy => ⟨hballW hy.1, fun i => (hy.2 i).le⟩
  have hconv : Convex ℝ Pos := by
    refine (convex_ball _ _).inter ?_
    intro y hy y' hy' a b ha hb hab i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      subst hab
      simpa using hy' i
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hy i)) (mul_nonneg hb (hy' i).le)
  refine ⟨T ∩ G, hTo.inter hG, ⟨hxT, hpG⟩, inter_subset_right, ?_, ?_⟩
  · rw [hEq]
    exact hconv.isPreconnected.image _
      (hj.continuous.comp_continuousOn (κ.continuousOn_coordInv.mono hKPos))
  · rw [hEq, mem_closure_iff_nhds]
    intro t ht
    have ht' : (j ∘ κ.coordInv) ⁻¹' t ∈ 𝓝[K] y₀ :=
      hφ.preimage_mem_nhdsWithin (by simpa [hinv] using ht)
    obtain ⟨r₃, hr₃, hr₃'⟩ := Metric.mem_nhdsWithin_iff.1 ht'
    set ε := min r₃ ρ / 2
    have hε : 0 < ε := by positivity
    have hεlt : ε < min r₃ ρ := by
      have : 0 < min r₃ ρ := lt_min hr₃ hρ
      simp only [ε]
      linarith
    set y : Fin n → ℝ := y₀ + fun _ => ε
    have hdist : dist y y₀ < min r₃ ρ := by
      refine lt_of_le_of_lt ((dist_pi_le_iff hε.le).2 fun i => ?_) hεlt
      simp [y, abs_of_pos hε]
    have hpos : ∀ i, 0 < y i := fun i => by
      have := hy₀K.2 i
      simp only [y, Pi.add_apply]
      linarith
    have hyb : y ∈ Metric.ball y₀ ρ := lt_of_lt_of_le hdist (min_le_right _ _)
    exact ⟨(j ∘ κ.coordInv) y, hr₃' ⟨lt_of_lt_of_le hdist (min_le_left _ _), hballW hyb,
      fun i => (hpos i).le⟩, y, ⟨hyb, hpos⟩, rfl⟩

end Ends

/-! ### The ends in the good regions -/

section Good

variable (hcs : Q.HasCornerStructureOfDim (n + 1)) (hfs : Q.IsFaceStructured)
  [inst : ChartedSpace (EuclideanQuadrant (n + 1)) Z]
  (o : TangentOrientation (𝓠 (n + 1)) Z (n + 1))

omit [TopologicalSpace A] [T2Space A] [ParacompactSpace A] in
include hfs in
/-- A face meeting the good region of `x₀` passes through `x₀`. -/
theorem mem_facesAt_of_mem_goodSet {x₀ : Z} (a : Faces Q) {p : Z} (hpa : p ∈ a.1)
    (hpG : p ∈ goodSet hcs hfs o x₀) : a ∈ facesAt hcs x₀ :=
  (mem_facesAt hcs).2 ((exists_nbhdFaces hcs x₀).choose_spec.2.2.2 a.1
    ((Q.isFaceIn_univ_iff).2 a.2) p hpG.1.2 hpa)

omit [TopologicalSpace A] [T2Space A] [ParacompactSpace A] in
/-- A face through `x₀` has points of degeneracy index `1` in every open `O ∋ x₀` inside the
good region of `x₀` (its coordinate face in the chart at `x₀`). -/
theorem exists_mem_face_degIndex_eq_one {x₀ : Z} (a : Faces Q) (ha : a ∈ facesAt hcs x₀)
    {O : Set Z} (hO : IsOpen O) (hx₀ : x₀ ∈ O) (hOG : O ⊆ goodSet hcs hfs o x₀) :
    ∃ y ∈ O, y ∈ a.1 ∧ Q.degIndex y = 1 := by
  have ha' := (mem_facesAt hcs).1 ha
  set κ := hcs.coords x₀
  obtain ⟨y, hyO, hys, hyi, hyl⟩ := κ.exists_coord_one_zero hO hx₀ (hcs.mem_coords x₀)
    (faceDataAt_coord hcs hfs x₀ a ha')
  have hyV : y ∈ (faceDataAt hcs hfs x₀ a ha').V₁ :=
    (mem_V₁At_iff hcs hfs ha').1 (mem_iInter₂.1 (hOG hyO).2 a ha')
  exact ⟨y, hyO, (faceDataAt hcs hfs x₀ a ha').mem_of_coord_eq_zero hyV hyi,
    κ.degIndex_eq_one hys hyi fun l hl => (hyl l hl).ne'⟩

variable (hj : IsEmbedding j) (hjc : IsClosed (range j)) (hcsA : PA.HasCornerStructureOfDim n)
  (hd : ∀ x, Q.degIndex (j x) = PA.degIndex x + 1)
  (hE1 : ∀ p ∈ range j, Q.degIndex p = 1 → ∀ᶠ z in 𝓝 p, Q.degIndex z = 1 → z ∈ range j)
include hj hjc hcsA hd hE1

/-- **Near a point of `range j` in the good region of `x₀`, `range j` lies in one face through
`x₀`**: the points of degeneracy index `1` of `range j` near `p` are preconnected
(`exists_isPreconnected_end`), each lies on exactly one face, a face through `x₀`, and the
finitely many faces through `x₀` are disjoint at these points. -/
theorem exists_face_end {x₀ : Z} (hG : IsOpen (goodSet hcs hfs o x₀)) {p : Z}
    (hp : p ∈ range j) (hpG : p ∈ goodSet hcs hfs o x₀) :
    ∃ O, IsOpen O ∧ p ∈ O ∧ O ⊆ goodSet hcs hfs o x₀ ∧ ∃ c : Faces Q, c ∈ facesAt hcs x₀ ∧
      c.1 ⊆ range j ∧ range j ∩ O ∩ {z | Q.degIndex z = 1} ⊆ c.1 ∧ p ∈ c.1 := by
  obtain ⟨O, hO, hpO, hOG, hpc, hcl⟩ := exists_isPreconnected_end hj hcsA hd hp hG hpG
  set S := range j ∩ O ∩ {z | Q.degIndex z = 1} with hSdef
  obtain ⟨z₀, hz₀⟩ : S.Nonempty := by
    obtain ⟨z, -, hz⟩ := mem_closure_iff_nhds.1 hcl univ univ_mem
    exact ⟨z, hz⟩
  obtain ⟨F₀, hF₀, hz₀F⟩ := exists_face_of_degIndex_eq_one hfs hz₀.2
  set c : Faces Q := ⟨F₀, hF₀⟩
  have hcx : c ∈ facesAt hcs x₀ := mem_facesAt_of_mem_goodSet hcs hfs o c hz₀F (hOG hz₀.1.2)
  set Oth := ⋃ b ∈ (facesAt hcs x₀).erase c, b.1
  have hOth : IsClosed Oth := isClosed_biUnion_finset fun b _ => IsFace.isClosed Q b.2
  have hface : ∀ z ∈ S, ∃ b : Faces Q, b ∈ facesAt hcs x₀ ∧ z ∈ b.1 := fun z hz => by
    obtain ⟨F, hF, hzF⟩ := exists_face_of_degIndex_eq_one hfs hz.2
    exact ⟨⟨F, hF⟩, mem_facesAt_of_mem_goodSet hcs hfs o ⟨F, hF⟩ hzF (hOG hz.1.2), hzF⟩
  have hsub : S ⊆ Othᶜ ∪ c.1ᶜ := by
    intro z hz
    by_cases hzc : z ∈ c.1
    · left
      intro hzO
      simp only [Oth, mem_iUnion] at hzO
      obtain ⟨b, hb, hzb⟩ := hzO
      exact (Finset.ne_of_mem_erase hb)
        (Subtype.ext (face_eq_of_degIndex_eq_one hfs hz.2 b.2 c.2 hzb hzc))
    · exact Or.inr hzc
  have hdisj : S ∩ (Othᶜ ∩ c.1ᶜ) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and, not_not]
    intro hz hzO
    by_contra hzc
    obtain ⟨b, hb, hzb⟩ := hface z hz
    have hne : b ≠ c := fun h => hzc (h ▸ hzb)
    exact hzO (mem_biUnion (Finset.mem_erase.2 ⟨hne, hb⟩) hzb)
  have hS : S ⊆ c.1 := by
    rcases isPreconnected_iff_subset_of_disjoint.1 hpc _ _ hOth.isOpen_compl
        (IsFace.isClosed Q hF₀).isOpen_compl hsub hdisj with h | h
    · intro z hz
      by_contra hzc
      obtain ⟨b, hb, hzb⟩ := hface z hz
      have hne : b ≠ c := fun h => hzc (h ▸ hzb)
      exact h hz (mem_biUnion (Finset.mem_erase.2 ⟨hne, hb⟩) hzb)
    · exact absurd hz₀F (h hz₀)
  exact ⟨O, hO, hpO, hOG, c, hcx,
    face_subset_range_of_degIndex_eq_one hfs hjc hE1 hF₀ hz₀F hz₀.1.1 hz₀.2, hS,
    closure_minimal hS (IsFace.isClosed Q hF₀) hcl⟩

/-- **At most one face through `x₀` lies in `range j`.** -/
theorem face_eq_of_subset_range {x₀ : Z} (hG : IsOpen (goodSet hcs hfs o x₀)) {a b : Faces Q}
    (ha : a ∈ facesAt hcs x₀) (hb : b ∈ facesAt hcs x₀) (haj : a.1 ⊆ range j)
    (hbj : b.1 ⊆ range j) : a = b := by
  have hx₀ : x₀ ∈ range j := haj ((mem_facesAt hcs).1 ha)
  obtain ⟨O, hO, hx₀O, hOG, c, -, -, hSc, -⟩ :=
    exists_face_end hcs hfs o hj hjc hcsA hd hE1 hG hx₀ (mem_goodSet hcs hfs o x₀)
  have key : ∀ a' : Faces Q, a' ∈ facesAt hcs x₀ → a'.1 ⊆ range j → a' = c := fun a' ha' haj' => by
    obtain ⟨y, hyO, hya, hy1⟩ := exists_mem_face_degIndex_eq_one hcs hfs o a' ha' hO hx₀O hOG
    exact Subtype.ext (face_eq_of_degIndex_eq_one hfs hy1 a'.2 c.2 hya (hSc ⟨⟨haj' hya, hyO⟩, hy1⟩))
  rw [key a ha haj, key b hb hbj]

/-- **`range j` meets the good region of `x₀` only in the face through `x₀` contained in
`range j`.** -/
theorem range_inter_goodSet_subset {x₀ : Z} (hG : IsOpen (goodSet hcs hfs o x₀)) {a : Faces Q}
    (ha : a ∈ facesAt hcs x₀) (haj : a.1 ⊆ range j) :
    range j ∩ goodSet hcs hfs o x₀ ⊆ a.1 := by
  rintro p ⟨hp, hpG⟩
  obtain ⟨-, -, -, -, c, hc, hcj, -, hpc⟩ := exists_face_end hcs hfs o hj hjc hcsA hd hE1 hG hp hpG
  rwa [face_eq_of_subset_range hcs hfs o hj hjc hcsA hd hE1 hG ha hc haj hcj]

end Good

/-! ### Face chart pairs of the ends -/

section Pair

omit [T2Space A] [ParacompactSpace A] in
open Classical in
/-- **The ends as faces, as a partial homeomorphism**: if `range j ∩ G ⊆ F`, `j` is the
homeomorphism of `j⁻¹(G)` onto `F ∩ G` with inverse `g` (`j ∘ g = id` on `F`). -/
def endPiece (hj : IsEmbedding j) {G : Set Z} (hG : IsOpen G) (F : Set Z) (hne : F.Nonempty)
    (hK : range j ∩ G ⊆ F) (g : F → A) (hgc : Continuous g) (hjg : ∀ p, j (g p) = p) :
    OpenPartialHomeomorph A F where
  toFun x := if h : j x ∈ F then ⟨j x, h⟩ else ⟨hne.some, hne.some_mem⟩
  invFun := g
  source := j ⁻¹' G
  target := Subtype.val ⁻¹' G
  map_source' x hx := by
    change ((if h : j x ∈ F then (⟨j x, h⟩ : F) else ⟨hne.some, hne.some_mem⟩ : F) : Z) ∈ G
    rw [dif_pos (hK ⟨⟨x, rfl⟩, hx⟩)]
    exact hx
  map_target' y hy := by
    change j (g y) ∈ G
    rw [hjg]
    exact hy
  left_inv' x hx := by
    rw [dif_pos (hK ⟨⟨x, rfl⟩, hx⟩)]
    exact hj.injective (hjg _)
  right_inv' y _ := by
    change (if h : j (g y) ∈ F then (⟨j (g y), h⟩ : F) else ⟨hne.some, hne.some_mem⟩) = y
    rw [dif_pos (by rw [hjg]; exact y.2)]
    exact Subtype.ext (hjg y)
  open_source := hG.preimage hj.continuous
  open_target := hG.preimage continuous_subtype_val
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (j ⁻¹' G).domRestrict (fun x => if h : j x ∈ F then (⟨j x, h⟩ : F) else
        ⟨hne.some, hne.some_mem⟩) = fun x => ⟨j x.1, hK ⟨⟨x.1, rfl⟩, x.2⟩⟩ := by
      funext x
      simp only [domRestrict_apply]
      rw [dif_pos]
    rw [this]
    exact (hj.continuous.comp continuous_subtype_val).subtype_mk _
  continuousOn_invFun := hgc.continuousOn

omit [T2Space Z] [ParacompactSpace Z] [T2Space A] [ParacompactSpace A] in
open Classical in
theorem endPiece_val (hj : IsEmbedding j) {G : Set Z} (hG : IsOpen G) (F : Set Z)
    (hne : F.Nonempty) (hK : range j ∩ G ⊆ F) (g : F → A) (hgc : Continuous g)
    (hjg : ∀ p, j (g p) = p) {x : A} (hx : j x ∈ G) :
    ((endPiece hj hG F hne hK g hgc hjg x : F) : Z) = j x := by
  change ((if h : j x ∈ F then (⟨j x, h⟩ : F) else ⟨hne.some, hne.some_mem⟩ : F) : Z) = j x
  rw [dif_pos (hK ⟨⟨x, rfl⟩, hx⟩)]

omit [T2Space Z] [ParacompactSpace Z] [T2Space A] [ParacompactSpace A] in
/-- **The composite chart is a chart of `A`**: for a face chart pair `(e_F, e, i)` of a face
`F ⊆ Z` whose source contains `F ∩ G`, `e_F ∘ j` on `j⁻¹(G)` is in the maximal atlas of `A`; its
expression is `π_i ∘ e ∘ j` (smooth since `j` is) and its inverse is `g ∘ e_F⁻¹` (smooth since
`g` is). -/
theorem endPiece_trans_mem_maximalAtlas [ChartedSpace (EuclideanQuadrant (n + 1)) Z]
    [IsManifold (𝓠 (n + 1)) ∞ Z] [ChartedSpace (EuclideanQuadrant n) A] [IsManifold (𝓠 n) ∞ A]
    (hj : IsEmbedding j) (hjs : ContMDiff (𝓠 n) (𝓠 (n + 1)) ∞ j) {G : Set Z} (hG : IsOpen G)
    (F : Set Z) [ChartedSpace (EuclideanQuadrant n) F] [IsManifold (𝓠 n) ∞ F]
    (hne : F.Nonempty) (hK : range j ∩ G ⊆ F) (g : F → A) (hgs : ContMDiff (𝓠 n) (𝓠 n) ∞ g)
    (hjg : ∀ p, j (g p) = p) (P : FaceChartPair n (Subtype.val : F → Z)) :
    (endPiece hj hG F hne hK g hgs.continuous hjg).trans P.eN ∈
      IsManifold.maximalAtlas (𝓠 n) ∞ A := by
  set π := endPiece hj hG F hne hK g hgs.continuous hjg
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · rw [contMDiffOn_iff_target]
    refine ⟨(π.trans P.eN).continuousOn, fun y => ?_⟩
    rw [extChartAt_self_eq]
    have hsm : ContMDiffOn (𝓠 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (fun x => faceProjection P.i (P.e.extend (𝓠 (n + 1)) (j x))) (j ⁻¹' P.e.source) :=
      (faceProjection P.i).contMDiff.comp_contMDiffOn
        ((P.e.contMDiffOn_extend P.mem_M).comp hjs.contMDiffOn fun x hx => hx)
    refine (hsm.mono fun x hx => ?_).congr fun x hx => ?_
    · have hv : ((π.symm.symm x : F) : Z) = j x :=
        endPiece_val hj hG F hne hK g hgs.continuous hjg hx.1.1
      have h := P.mapsTo _ hx.1.2
      rwa [hv] at h
    · have hv : ((π.symm.symm x : F) : Z) = j x :=
        endPiece_val hj hG F hne hK g hgs.continuous hjg hx.1.1
      have h := P.extend_eq _ hx.1.2
      rw [hv] at h
      rw [h, faceProjection_faceEmbedding]
      rfl
  · exact hgs.comp_contMDiffOn ((contMDiffOn_symm_of_mem_maximalAtlas P.mem_N).mono
      fun z hz => hz.1)

variable (hcs : Q.HasCornerStructureOfDim (n + 1)) (hfs : Q.IsFaceStructured)
  [inst : ChartedSpace (EuclideanQuadrant (n + 1)) Z]
  (o : TangentOrientation (𝓠 (n + 1)) Z (n + 1)) (hch : inst = Q.cornerChartedSpace hcs)
  [instA : ChartedSpace (EuclideanQuadrant n) A] [IsManifold (𝓠 n) ∞ A]

omit [T2Space A] [ParacompactSpace A] in
/-- **The face chart pair of an end** at `x₀`: if `a` is the face through `x₀` with
`range j ∩ G ⊆ a` (`G` the good region of `x₀`), its face chart pair at `x₀` composed with `j`
(`endPiece`) is a face chart pair of `j`, in the chart `chartAt x₀` of `Z` and with the same
coordinate. -/
def endFaceChartPair {x₀ : Z} (hG : IsOpen (goodSet hcs hfs o x₀)) (hj : IsEmbedding j)
    (hjs : ContMDiff (𝓠 n) (𝓠 (n + 1)) ∞ j) (a : Faces Q) (ha : x₀ ∈ a.1)
    (hK : range j ∩ goodSet hcs hfs o x₀ ⊆ a.1) (g : a.1 → A)
    (hgs : letI := faceChartedSpace hcs hfs a.2; ContMDiff (𝓠 n) (𝓠 n) ∞ g)
    (hjg : ∀ p, j (g p) = p) : FaceChartPair n j :=
  letI := faceChartedSpace hcs hfs a.2
  haveI := isManifold_faceChartedSpace hcs hfs a.2
  haveI := isManifold_of_eq hcs hch
  { eN := (endPiece hj hG a.1 (IsFace.nonempty a.2) hK g hgs.continuous hjg).trans
      ((faceDataAt hcs hfs x₀ a ha).pair hcs hfs hch a.2 ⟨x₀, ha⟩).eN
    e := (hcs.coords x₀).toQuadrantChart
    i := (faceDataAt hcs hfs x₀ a ha).i
    mem_N := endPiece_trans_mem_maximalAtlas hj hjs hG a.1 _ hK g hgs hjg _
    mem_M := mem_maximalAtlas_of_eq hcs hch _
    mapsTo := fun _ hp => hp.1.1.1.1
    extend_eq := fun p hp => by
      have hv : (((endPiece hj hG a.1 (IsFace.nonempty a.2) hK g hgs.continuous hjg).symm.symm
          p : a.1) : Z) = j p := endPiece_val hj hG a.1 _ hK g hgs.continuous hjg hp.1
      have h := ((faceDataAt hcs hfs x₀ a ha).pair hcs hfs hch a.2 ⟨x₀, ha⟩).extend_eq _ hp.2
      rw [hv] at h
      exact h }

omit [T2Space A] [ParacompactSpace A] in
theorem endFaceChartPair_e {x₀ : Z} (hG : IsOpen (goodSet hcs hfs o x₀)) (hj : IsEmbedding j)
    (hjs : ContMDiff (𝓠 n) (𝓠 (n + 1)) ∞ j) (a : Faces Q) (ha : x₀ ∈ a.1)
    (hK : range j ∩ goodSet hcs hfs o x₀ ⊆ a.1) (g : a.1 → A)
    (hgs : letI := faceChartedSpace hcs hfs a.2; ContMDiff (𝓠 n) (𝓠 n) ∞ g)
    (hjg : ∀ p, j (g p) = p) :
    (endFaceChartPair hcs hfs o hch hG hj hjs a ha hK g hgs hjg).e =
      (hcs.coords x₀).toQuadrantChart := rfl

omit [T2Space A] [ParacompactSpace A] in
theorem endFaceChartPair_i {x₀ : Z} (hG : IsOpen (goodSet hcs hfs o x₀)) (hj : IsEmbedding j)
    (hjs : ContMDiff (𝓠 n) (𝓠 (n + 1)) ∞ j) (a : Faces Q) (ha : x₀ ∈ a.1)
    (hK : range j ∩ goodSet hcs hfs o x₀ ⊆ a.1) (g : a.1 → A)
    (hgs : letI := faceChartedSpace hcs hfs a.2; ContMDiff (𝓠 n) (𝓠 n) ∞ g)
    (hjg : ∀ p, j (g p) = p) :
    (endFaceChartPair hcs hfs o hch hG hj hjs a ha hK g hgs hjg).i =
      (faceDataAt hcs hfs x₀ a ha).i := rfl

omit [T2Space A] [ParacompactSpace A] in
theorem mem_endFaceChartPair_source {x₀ : Z} (hG : IsOpen (goodSet hcs hfs o x₀))
    (hj : IsEmbedding j) (hjs : ContMDiff (𝓠 n) (𝓠 (n + 1)) ∞ j) (a : Faces Q) (ha : x₀ ∈ a.1)
    (hK : range j ∩ goodSet hcs hfs o x₀ ⊆ a.1) (g : a.1 → A)
    (hgs : letI := faceChartedSpace hcs hfs a.2; ContMDiff (𝓠 n) (𝓠 n) ∞ g)
    (hjg : ∀ p, j (g p) = p) {p : A} (hp : j p ∈ goodSet hcs hfs o x₀) :
    p ∈ (endFaceChartPair hcs hfs o hch hG hj hjs a ha hK g hgs hjg).eN.source := by
  let _ := faceChartedSpace hcs hfs a.2
  refine ⟨hp, ?_⟩
  change (endPiece hj hG a.1 (IsFace.nonempty a.2) hK g hgs.continuous hjg p : Z) ∈
    (faceDataAt hcs hfs x₀ a ha).V₁
  rw [endPiece_val hj hG a.1 _ hK g hgs.continuous hjg hp]
  exact (mem_V₁At_iff hcs hfs ha).1 (mem_iInter₂.1 hp.2 a ha)

end Pair

/-! ### The family of the ends and the lateral faces -/

section Family

variable {ι : Type*} {Y : ι → Type u}

variable (Q) in
/-- **The lateral faces**: the faces of `Z` contained in no `range J i`. -/
abbrev LateralFace (J : ∀ i, Y i → Z) : Type u :=
  {a : Faces Q // ∀ i, ¬ a.1 ⊆ range (J i)}

variable (Q) in
/-- The members of the family: the ends `Y i` and the lateral faces of `Z`. -/
def EndFam (J : ∀ i, Y i → Z) : ι ⊕ LateralFace Q J → Type u
  | .inl i => Y i
  | .inr a => a.1.1

variable (Q) in
/-- The maps of the family: `J i` on the ends, the inclusions on the lateral faces. -/
def endFamMap (J : ∀ i, Y i → Z) : ∀ b, EndFam Q J b → Z
  | .inl i => J i
  | .inr _ => Subtype.val

variable [∀ i, TopologicalSpace (Y i)] {J : ∀ i, Y i → Z}

instance endFamTop : ∀ b, TopologicalSpace (EndFam Q J b)
  | .inl i => (inferInstance : TopologicalSpace (Y i))
  | .inr a => (inferInstance : TopologicalSpace a.1.1)

instance endFamT2 [∀ i, T2Space (Y i)] : ∀ b, T2Space (EndFam Q J b)
  | .inl i => (inferInstance : T2Space (Y i))
  | .inr a => (inferInstance : T2Space a.1.1)

theorem endFamCompact [CompactSpace Z] [∀ i, CompactSpace (Y i)] :
    ∀ b, CompactSpace (EndFam Q J b)
  | .inl i => (inferInstance : CompactSpace (Y i))
  | .inr a => isCompact_iff_compactSpace.1 (IsFace.isClosed Q a.1.2).isCompact

theorem continuous_endFamMap (hJ : ∀ i, Continuous (J i)) : ∀ b, Continuous (endFamMap Q J b)
  | .inl i => hJ i
  | .inr _ => continuous_subtype_val

variable (hcs : Q.HasCornerStructureOfDim (n + 1)) (hfs : Q.IsFaceStructured)
  [instY : ∀ i, ChartedSpace (EuclideanQuadrant n) (Y i)]

/-- The charted spaces of the family (the face charts on the lateral faces). -/
@[instance_reducible]
def endFamCS : ∀ b, ChartedSpace (EuclideanQuadrant n) (EndFam Q J b)
  | .inl i => instY i
  | .inr a => faceChartedSpace hcs hfs a.1.2

theorem endFamIsManifold [∀ i, IsManifold (𝓠 n) ∞ (Y i)] :
    letI := endFamCS (J := J) hcs hfs
    ∀ b, IsManifold (𝓠 n) ∞ (EndFam Q J b)
  | .inl i => (inferInstance : IsManifold (𝓠 n) ∞ (Y i))
  | .inr a => isManifold_faceChartedSpace hcs hfs a.1.2

variable [Fintype ι] (J)

open Classical in
/-- The members of the family meeting the good region of `x₀`: the ends `i` such that a face
through `x₀` lies in `range J i`, and the lateral faces through `x₀`. -/
def endFaces (x₀ : Z) : Finset (ι ⊕ LateralFace Q J) :=
  (Finset.univ.filter fun i => ∃ a ∈ facesAt hcs x₀, a.1 ⊆ range (J i)).map
      Function.Embedding.inl ∪
    ((facesAt hcs x₀).subtype fun a => ∀ i, ¬ a.1 ⊆ range (J i)).map Function.Embedding.inr

omit [∀ i, TopologicalSpace (Y i)] instY in
theorem mem_endFaces_inl {x₀ : Z} {i : ι} :
    Sum.inl i ∈ endFaces J hcs x₀ ↔ ∃ a ∈ facesAt hcs x₀, a.1 ⊆ range (J i) := by
  simp [endFaces]

omit [∀ i, TopologicalSpace (Y i)] instY in
theorem mem_endFaces_inr {x₀ : Z} {a : LateralFace Q J} :
    Sum.inr a ∈ endFaces J hcs x₀ ↔ a.1 ∈ facesAt hcs x₀ := by
  simp [endFaces]

variable [inst : ChartedSpace (EuclideanQuadrant (n + 1)) Z]
  (o : TangentOrientation (𝓠 (n + 1)) Z (n + 1)) (hch : inst = Q.cornerChartedSpace hcs)
  (ho : o.IsContinuous (𝓠 (n + 1)) ∞)
  [∀ i, T2Space (Y i)] [∀ i, ParacompactSpace (Y i)] [∀ i, IsManifold (𝓠 n) ∞ (Y i)]
  {PY : ∀ i, MPolyfold (Y i)} (hcsY : ∀ i, (PY i).HasCornerStructureOfDim n)
  (hJ : ∀ i, IsEmbedding (J i)) (hJc : ∀ i, IsClosed (range (J i)))
  (hJs : ∀ i, ContMDiff (𝓠 n) (𝓠 (n + 1)) ∞ (J i))
  (hd : ∀ i x, Q.degIndex (J i x) = (PY i).degIndex x + 1)
  (hE1 : ∀ i, ∀ p ∈ range (J i), Q.degIndex p = 1 →
    ∀ᶠ z in 𝓝 p, Q.degIndex z = 1 → z ∈ range (J i))
  (hdisj : Pairwise fun i i' => Disjoint (range (J i)) (range (J i')))
  (hq : ∀ i (a : Faces Q), a.1 ⊆ range (J i) → ∃ g : a.1 → Y i,
    (letI := faceChartedSpace hcs hfs a.2; ContMDiff (𝓠 n) (𝓠 n) ∞ g) ∧ ∀ p, J i (g p) = p)

/-- **The face chart pairs of the family at `x₀`**: `endFaceChartPair` for the ends, the face
chart pairs of `FaceData.pair` for the lateral faces. -/
def endFamPair (x₀ : Z) :
    letI := endFamCS (J := J) hcs hfs
    ∀ b, b ∈ endFaces J hcs x₀ → FaceChartPair n (endFamMap Q J b) :=
  letI := endFamCS (J := J) hcs hfs
  fun b h => match b, h with
  | .inl i, h =>
    have hex := (mem_endFaces_inl J hcs).1 h
    endFaceChartPair (A := Y i) (j := J i) hcs hfs o hch (isOpen_goodSet hcs hfs o hch ho x₀)
      (hJ i) (hJs i)
      hex.choose ((mem_facesAt hcs).1 hex.choose_spec.1)
      (range_inter_goodSet_subset hcs hfs o (hJ i) (hJc i) (hcsY i) (hd i) (hE1 i)
        (isOpen_goodSet hcs hfs o hch ho x₀) hex.choose_spec.1 hex.choose_spec.2)
      (hq i _ hex.choose_spec.2).choose (hq i _ hex.choose_spec.2).choose_spec.1
      (hq i _ hex.choose_spec.2).choose_spec.2
  | .inr a, h =>
    (faceDataAt hcs hfs x₀ a.1 ((mem_facesAt hcs).1 ((mem_endFaces_inr J hcs).1 h))).pair hcs
      hfs hch a.1.2 ⟨x₀, (mem_facesAt hcs).1 ((mem_endFaces_inr J hcs).1 h)⟩

/-- **The good region of `x₀` for the ends and the lateral faces** (`GoodRegion`): the region
`goodSet x₀` in the chart `chartAt x₀`, with the face chart pairs `endFamPair`.  The ends meeting
it are those with a face through `x₀` inside their range (`exists_face_end`); distinct members
have distinct coordinates since the faces through `x₀` do (`goodRegion`) and a face lies in at
most one range. -/
def endGoodRegion (x₀ : Z) :
    letI := endFamCS (J := J) hcs hfs
    GoodRegion o (endFamMap Q J) (hcs.coords x₀).toQuadrantChart (goodSet hcs hfs o x₀) :=
  letI := endFamCS (J := J) hcs hfs
  letI : ∀ a : Faces Q, ChartedSpace (EuclideanQuadrant n) a.1 :=
    fun a => faceChartedSpace hcs hfs a.2
  haveI hG := isOpen_goodSet hcs hfs o hch ho x₀
  { sign := (goodRegion hcs hfs o hch ho x₀).sign
    orientationIn_eq := (goodRegion hcs hfs o hch ho x₀).orientationIn_eq
    subset_source := (goodRegion hcs hfs o hch ho x₀).subset_source
    faces := endFaces J hcs x₀
    pair := endFamPair J hcs hfs o hch ho hcsY hJ hJc hJs hd hE1 hq x₀
    pair_e := fun b h => by
      rcases b with i | a <;> rfl
    src := fun b h p hp => by
      rcases b with i | a
      · have hex := (mem_endFaces_inl J hcs).1 h
        exact mem_endFaceChartPair_source (A := Y i) (j := J i) hcs hfs o hch hG (hJ i) (hJs i)
          hex.choose ((mem_facesAt hcs).1 hex.choose_spec.1)
          (range_inter_goodSet_subset hcs hfs o (hJ i) (hJc i) (hcsY i) (hd i) (hE1 i) hG
            hex.choose_spec.1 hex.choose_spec.2)
          _ (hq i _ hex.choose_spec.2).choose_spec.1 (hq i _ hex.choose_spec.2).choose_spec.2 hp
      · exact FaceData.mem_pair_source hcs hfs hch a.1.2 _ _
          ((mem_V₁At_iff hcs hfs ((mem_facesAt hcs).1 ((mem_endFaces_inr J hcs).1 h))).1
            (mem_iInter₂.1 hp.2 a.1 ((mem_facesAt hcs).1 ((mem_endFaces_inr J hcs).1 h))))
    miss := fun b h p hp => by
      rcases b with i | a
      · obtain ⟨-, -, -, -, c, hc, hcj, -, -⟩ := exists_face_end hcs hfs o (hJ i) (hJc i)
          (hcsY i) (hd i) (hE1 i) hG (mem_range_self p) hp
        exact h ((mem_endFaces_inl J hcs).2 ⟨c, hc, hcj⟩)
      · exact h ((mem_endFaces_inr J hcs).2 (mem_facesAt_of_mem_goodSet hcs hfs o a.1 p.2 hp))
    inj := fun b h b' h' hi => by
      have hinj := (goodRegion hcs hfs o hch ho x₀).inj
      rcases b with i | a <;> rcases b' with i' | a'
      · have hex := (mem_endFaces_inl J hcs).1 h
        have hex' := (mem_endFaces_inl J hcs).1 h'
        have he : hex.choose = hex'.choose := hinj _ hex.choose_spec.1 _ hex'.choose_spec.1 hi
        by_contra hne
        obtain ⟨y, hy⟩ := IsFace.nonempty hex.choose.2
        exact (hdisj (fun h => hne (congrArg Sum.inl h))).le_bot
          ⟨hex.choose_spec.2 hy, hex'.choose_spec.2 (he ▸ hy)⟩
      · have hex := (mem_endFaces_inl J hcs).1 h
        have he : hex.choose = a'.1 :=
          hinj _ hex.choose_spec.1 _ ((mem_endFaces_inr J hcs).1 h') hi
        exact absurd (he ▸ hex.choose_spec.2) (a'.2 i)
      · have hex' := (mem_endFaces_inl J hcs).1 h'
        have he : a.1 = hex'.choose :=
          hinj _ ((mem_endFaces_inr J hcs).1 h) _ hex'.choose_spec.1 hi
        exact absurd (he ▸ hex'.choose_spec.2) (a.2 i')
      · exact congrArg Sum.inr (Subtype.ext
          (hinj _ ((mem_endFaces_inr J hcs).1 h) _ ((mem_endFaces_inr J hcs).1 h') hi))
    cover := fun x hx i hi hl => by
      obtain ⟨a, p, rfl⟩ := (goodRegion hcs hfs o hch ho x₀).cover x hx i hi hl
      by_cases hlat : ∀ i, ¬ a.1 ⊆ range (J i)
      · exact ⟨Sum.inr ⟨a, hlat⟩, p, rfl⟩
      · push Not at hlat
        obtain ⟨i', hi'⟩ := hlat
        obtain ⟨y, hy⟩ := hi' p.2
        exact ⟨Sum.inl i', y, hy⟩ }

omit [Fintype ι] in
include hcs hfs hch ho hcsY hJ hJc hJs hd hE1 hdisj hq in
/-- **Every point of an end lies in a face chart pair** (of the good region at its image). -/
theorem exists_faceChartPair_end [Finite ι] (i : ι) (x : Y i) :
    ∃ P : FaceChartPair n (J i), x ∈ P.eN.source := by
  let _ := Fintype.ofFinite ι
  subst hch
  let _ := Q.cornerChartedSpace hcs
  let _ := endFamCS (J := J) hcs hfs
  exact exists_faceChartPair_of_goodRegion o (endFamMap Q J) (mem_goodSet hcs hfs o)
    (endGoodRegion J hcs hfs o rfl ho hcsY hJ hJc hJs hd hE1 hdisj hq) (Sum.inl i) x

omit [Fintype ι] in
include hcs hfs hch ho hcsY hJ hJc hJs hd hE1 hdisj hq in
/-- **The induced orientation of an end exists and is continuous** (`inducedOrientation`,
outward vector first). -/
theorem exists_isInducedOrientation_end [Finite ι] (i : ι) :
    ∃ oN : TangentOrientation (𝓠 n) (Y i) n, IsInducedOrientation (J i) o oN ∧
      oN.IsContinuous (𝓠 n) ∞ := by
  have := isManifold_of_eq hcs hch
  exact ⟨inducedOrientation o (exists_faceChartPair_end J hcs hfs o hch ho hcsY hJ hJc hJs hd
      hE1 hdisj hq i),
    isInducedOrientation_inducedOrientation o _,
    isContinuous_inducedOrientation o _ ho (hJ i).continuous⟩

include hcs hfs hch ho hcsY hJ hJc hJs hd hE1 hdisj hq in
/-- **The boundary integral with ends** (2021 Theorem 4.4.7, p. 199, with the ends of the
proof of Theorem 6.7.1, p. 278): for compact `Z` and a `C¹` `n`-form `ω`,
`∫_{∂Z} ω = ∑ᵢ ∫_{Y i} J_i^*ω + ∑_F ∫_F ω|_F`, the second sum over the lateral faces `F` (the
faces of `Z` in no `range J i`); each `Y i` carries an induced orientation `oN i`
(`exists_isInducedOrientation_end`) and each face its induced orientation
(`faceOrientation`). -/
theorem boundaryIntegral_eq_sum_ends_add_lateral [CompactSpace Z] [∀ i, CompactSpace (Y i)]
    (oN : ∀ i, TangentOrientation (𝓠 n) (Y i) n) (hoN : ∀ i, IsInducedOrientation (J i) o (oN i))
    (hoNc : ∀ i, (oN i).IsContinuous (𝓠 n) ∞) {ω : ManifoldForm (𝓠 (n + 1)) Z n}
    (hω : ManifoldForm.ContMDiffForm (𝓠 (n + 1)) 1 ω) :
    haveI := isManifold_of_eq hcs hch
    haveI : Finite (Faces Q) := finite_faces hcs
    letI : Fintype (LateralFace Q J) := Fintype.ofFinite _
    letI : ∀ a : Faces Q, ChartedSpace (EuclideanQuadrant n) a.1 :=
      fun a => faceChartedSpace hcs hfs a.2
    ManifoldForm.boundaryIntegral o ω =
      ∑ i, ManifoldForm.integral (oN i) (restrictForm (J i) ω) +
        ∑ a : LateralFace Q J, ManifoldForm.integral (faceOrientation hcs hfs o hch a.1)
          (restrictForm (Subtype.val : a.1.1 → Z) ω) := by
  subst hch
  let _ := Q.cornerChartedSpace hcs
  have := isManifold_of_eq hcs rfl
  have : Finite (Faces Q) := finite_faces hcs
  let _ : Fintype (LateralFace Q J) := Fintype.ofFinite _
  let _ := endFamCS (J := J) hcs hfs
  let _ : ∀ a : Faces Q, ChartedSpace (EuclideanQuadrant n) a.1 :=
    fun a => faceChartedSpace hcs hfs a.2
  have := endFamIsManifold (J := J) hcs hfs
  have := endFamCompact (Q := Q) (J := J)
  let oF : ∀ b, TangentOrientation (𝓠 n) (EndFam Q J b) n := fun b => match b with
    | .inl i => oN i
    | .inr a => faceOrientation hcs hfs o rfl a.1
  have hoF : ∀ b, IsInducedOrientation (endFamMap Q J b) o (oF b) := fun b => match b with
    | .inl i => hoN i
    | .inr a => isInducedOrientation_faceOrientation hcs hfs o rfl a.1
  have hoFc : ∀ b, (oF b).IsContinuous (𝓠 n) ∞ := fun b => match b with
    | .inl i => hoNc i
    | .inr a => isContinuous_faceOrientation hcs hfs o rfl ho a.1
  have h := sum_integral_restrictForm_eq_boundaryIntegral o (endFamMap Q J) ho
    (continuous_endFamMap fun i => (hJ i).continuous) hoF hoFc (goodSet hcs hfs o)
    (isOpen_goodSet hcs hfs o rfl ho) (mem_goodSet hcs hfs o)
    (endGoodRegion J hcs hfs o rfl ho hcsY hJ hJc hJs hd hE1 hdisj hq) hω
    isClosed_closure.isCompact
  rw [← h, Fintype.sum_sum_type]
  rfl

end Family

end MPolyfold

end Polyfold
