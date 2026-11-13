import Polyfold.Chapter2.TameBoundaryStructure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4,
**Theorem 4.4.7** (Stokes, p. 199; preprint Theorem 4.28): the sum `∑_F ∫_F ω` over the faces `F`
of the compact tame submanifold `N`.

# The faces of a compact tame M-polyfold are finitely many

The text sums over the faces of `∂N` without comment.  The sum is finite:

* `MPolyfold.finite_setOf_isFace`: a compact tame M-polyfold has finitely many faces
  (2021 Definition 2.5.10: closures of the connected components of `{d = 1}`).
* `MPolyfold.finite_setOf_isFace_mem`: in a tame M-polyfold a point lies in finitely many faces
  (at most `d(x)`).

*Proof.*  Every `x` has an open neighbourhood `U(x)` such that every face meeting `U(x)` contains
`x` (2021 Proposition 2.7.5 (3), `exists_nbhd_faces_mem`), and `x` lies in at most `d(x)` faces
(`encard_facesThrough_le`).  Finitely many `U(x_j)` cover, and a face is nonempty.

This is one of the steps towards the text's statement of Theorem 4.4.7 with the faces as manifolds
in their own right (gap G.40); the integral over a face and the identity with the boundary
integral of `ManifoldStokes2021` are not formalized.
-/

open Set Function

namespace Polyfold

namespace MPolyfold

open TameBoundary

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- In a tame M-polyfold a point lies in finitely many faces. -/
theorem finite_setOf_isFace_mem (hP : P.IsTame) (x : X) : {F | P.IsFace F ∧ x ∈ F}.Finite := by
  have h := encard_facesThrough_le (P.isCornerIndex_degIndex hP) isOpen_univ (mem_univ x)
  have h2 : {F | P.IsFace F ∧ x ∈ F} = facesThrough P.degIndex univ x := by
    ext F
    exact ⟨fun hF => ⟨P.isFaceIn_univ_iff.2 hF.1, hF.2⟩,
      fun hF => ⟨P.isFaceIn_univ_iff.1 hF.1, hF.2⟩⟩
  rw [h2]
  exact Set.finite_of_encard_le_coe h

/-- A face is nonempty. -/
theorem IsFace.nonempty {F : Set X} (hF : P.IsFace F) : F.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := hF
  exact ⟨x, subset_closure (mem_connectedComponentIn hx)⟩

/-- **A compact tame M-polyfold has finitely many faces** (the sum over the faces `F` in
2021 Theorem 4.4.7 is finite). -/
theorem finite_setOf_isFace [CompactSpace X] (hP : P.IsTame) : {F | P.IsFace F}.Finite := by
  have hd := P.isCornerIndex_degIndex hP
  choose U hUo hxU _ hU using fun x : X => exists_nbhd_faces_mem hd isOpen_univ (mem_univ x)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun x _ => mem_iUnion.2 ⟨x, hxU x⟩)
  refine (t.finite_toSet.biUnion fun x _ => finite_setOf_isFace_mem hP x).subset ?_
  intro F hF
  obtain ⟨y, hy⟩ := IsFace.nonempty hF
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht (mem_univ y))
  exact mem_iUnion₂.2 ⟨x, hxt, hF, hU x F (P.isFaceIn_univ_iff.2 hF) y hyx hy⟩

/-- **A face in a prescribed tame chart is a coordinate face near each of its points**: let `X`
be tame and face-structured, `F` a face, `x ∈ F`, and `φ` any chart around `x` modelled on a tame
retract `O = r(U)` with coordinates `T`.  Then there are a coordinate `i` with `λ_i(φ(x)) = 0` and
an open `B ∋ φ(x)` with `φ(F) ∩ B = O ∩ {λ_i = 0} ∩ B`.  (For a corner chart of a
finite-dimensional `N` this identifies the faces of `N` of 2021 Theorem 4.4.7 with the faces of
the chart.) -/
theorem exists_face_eq_coordHyper (hfs : P.IsFaceStructured) {F : Set X}
    (hF : P.IsFace F) {x : X} (hx : x ∈ F) {φ : MChart X} (hφ : P.IsChart φ) (hxφ : x ∈ φ.source)
    (R : ScRetraction φ.model.E φ.model.C) (hRO : R.retract = φ.model.O) {n : ℕ} {W : ScBanach}
    {T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)}
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) :
    ∃ i : Fin n, (T 0 (φ x)).1 i = 0 ∧ ∃ B : Set (φ.model.E 0), IsOpen B ∧ φ x ∈ B ∧
      φ '' (F ∩ φ.source) ∩ B = coordHyper T i ∩ φ.model.O ∩ B := by
  have hset : {G | P.IsFace G ∧ x ∈ G} = facesThrough P.degIndex univ x := by
    ext G
    exact ⟨fun hG => ⟨P.isFaceIn_univ_iff.2 hG.1, hG.2⟩,
      fun hG => ⟨P.isFaceIn_univ_iff.1 hG.1, hG.2⟩⟩
  have hfx : (facesThrough P.degIndex univ x).encard = P.degIndex x := hset ▸ hfs x
  obtain ⟨Floc, hFloc, B₁, hB₁, hxB₁, hEq⟩ := P.exists_localFace_of_faceIn hfx
    ⟨P.isFaceIn_univ_iff.2 hF, hx⟩ hφ hxφ (subset_univ _) R hRO hT hR
  obtain ⟨i, e, -, -, hFe⟩ := (lemma_2_5_12 hT hR Floc).1 hFloc
  have hxF : φ x ∈ Floc := by
    have : φ x ∈ φ '' (F ∩ φ.source) ∩ B₁ := ⟨⟨x, ⟨hx, hxφ⟩, rfl⟩, hxB₁⟩
    rw [hEq] at this; exact this.1
  have hxH : φ x ∈ coordHyper T i ∩ R.retract := by
    rw [hFe] at hxF; exact connectedComponentIn_subset _ _ hxF
  have hFx : Floc = connectedComponentIn (coordHyper T i ∩ R.retract) (φ x) := by
    rw [hFe] at hxF ⊢; exact connectedComponentIn_eq hxF
  obtain ⟨ε, hε, p, hpS, hpi, -, -, -, -, hcl⟩ := local_face_structure hT hR hxH.2 hxH.1
  have hcc := closure_connectedComponentIn_faceStratum hT hR hpS hpi
  have hmem : ∀ z ∈ coordHyper T i ∩ R.retract, z ∈ Metric.ball (φ x) ε →
      z ∈ connectedComponentIn (coordHyper T i ∩ R.retract) p := fun z hz hzb => by
    have h := hcl z ⟨hzb, R.retract_subset_C hz.2⟩ hz.1
    rw [R.apply_eq_self_of_mem_retract hz.2] at h
    rw [← hcc]; exact ⟨h, hz.2⟩
  have hFp : Floc = connectedComponentIn (coordHyper T i ∩ R.retract) p := by
    rw [hFx]; exact (connectedComponentIn_eq (hmem _ hxH (Metric.mem_ball_self hε))).symm
  refine ⟨i, hxH.1, B₁ ∩ Metric.ball (φ x) ε, hB₁.inter Metric.isOpen_ball,
    ⟨hxB₁, Metric.mem_ball_self hε⟩, ?_⟩
  rw [← hRO]
  ext z
  constructor
  · rintro ⟨hzF, hzB₁, hzb⟩
    have hz : z ∈ Floc ∩ B₁ := hEq ▸ (⟨hzF, hzB₁⟩ : z ∈ φ '' (F ∩ φ.source) ∩ B₁)
    have hz1 : z ∈ connectedComponentIn (coordHyper T i ∩ R.retract) (φ x) := hFx ▸ hz.1
    exact ⟨connectedComponentIn_subset _ _ hz1, hzB₁, hzb⟩
  · rintro ⟨hzH, hzB₁, hzb⟩
    have hz : z ∈ Floc ∩ B₁ := ⟨hFp ▸ hmem z hzH hzb, hzB₁⟩
    rw [← hEq] at hz
    exact ⟨hz.1, hzB₁, hzb⟩

end MPolyfold

end Polyfold
