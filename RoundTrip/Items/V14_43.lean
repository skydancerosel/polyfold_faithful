import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V14_43

set_option maxSynthPendingDepth 3

/-! Round trip for V14_43 (2021 Theorem 14.6.3, p. 682, assembling the faces; 2017: Theorem 14.4).

`A` is the conjunction of the types of the 36 listed theorems at universe `0`
(`continuousOn_snd_comp_of_isFaceScPlusSectionOn` at `.{0}`; the corner example has no universe
parameter).  `B` is on `SEP.{0}`.

Blind exposure: the writer of `B` took the hypotheses of the extension part (Theorem 14.1.9)
from the project's `theorem_14_1_9_statement`.

**`B` does not hold as we read it.**  `B`'s first part is Theorem 14.6.3 for a compatible
assignment of *classes* (`IsCompatibleAssignment`, Definition 14.6.2 with the equivalence of
Definition 13.3.8, which does not compare sections), asking for a structured `Λ̃` over `∂X` with
`Λ|F = Λ_F`.  The project's corner example (`FaceCorner`, `W = X × ℝ² → X = [0, ∞)² × ℝ`)
is tame and face-structured, carries a compatible assignment `Λt`, and no functor agreeing with
the `Λ_F` over the faces is an sc⁺-multisection over `∂X`.

* `A_to_notB` (uses `A`): `A`'s conjunct `not_theorem_14_6_3_class_statement` refutes `B` at
  `FaceCorner.A` (tameness is part of `IsEpFaceStructured`; `L.forget` is the functor of a
  representative, an sc⁺-multisection over `∂X`; `faceFun` is `(Quotient.out _).2.Λ`).
* `not_B`: the same refutation, re-proved without the item's theorems: the banned lemmas used
  by the project's counterexample (`isEpFaceStructured_A`, `QuadrantBundle.isEpFace_subset_coord`,
  `QuadrantBundle.continuousOn_snd_comp_of_isFaceScPlusSectionOn`, `isCompatibleAssignment_Λt`,
  `not_isBoundaryScPlusMultisection_of_eq_on_faces`) are copied below as primed lemmas from
  non-item lemmas.
* `not_A_to_B : ¬ (A → B)`; `B_to_A` only ex falso.
* Main conjunct: `IsSecCompatibleAssignment.theorem_14_6_3`, the project's Theorem 14.6.3 for
  assignments of classes modulo the equivalence *with sections* (`FaceSecMultisection`): it is a
  different hypothesis from `B`'s; it holds, `B` does not.
-/

namespace RoundTrip.V14_43Corner

open Set Function Filter Topology
open scoped ContDiff Classical
open Polyfold Polyfold.FaceCorner Polyfold.SBLocalization Polyfold.StrongBundle
  Polyfold.EpGroupoid Polyfold.MPolyfold Polyfold.TameBoundaryExample Polyfold.QuadrantBundle

noncomputable section

theorem isEpFaceStructured_A' : FaceCorner.A.X.IsEpFaceStructured :=
  (EpGroupoid.Examples.example_11_1_4 (rnSc 1)).1

variable {n m k : ℕ}

/-- Copy of `QuadrantBundle.continuousOn_snd_comp_of_isFaceScPlusSectionOn`. -/
theorem continuousOn_snd_comp'
    {s : (quadSEP n m k).Obj → (quadSEP n m k).W} {U : Set (quadSEP n m k).Obj}
    (hs : IsFaceScPlusSectionOn (quadSEP n m k) s U) {α : Type*} [TopologicalSpace α]
    {γ : α → Q n m} (hγ : Continuous γ) {S : Set α} (i : Fin n)
    (hγU : ∀ a ∈ S, γ a ∈ U ∧ coord i (γ a) = 0) :
    ContinuousOn (fun a => (show Q n m × (Fin k → ℝ) from s (γ a)).2) S := by
  have hι : ∀ w : Fin k → ℝ, Function.invFun ((rnSc k).toBase 1) w = w := fun w =>
    leftInverse_invFun ((rnSc k).toBase_injective 1) w
  intro a ha
  set c : StrongBundleChart (quadSEP n m k).X.PObj (quadSEP n m k).P := chart₀ with hcdef
  have hi : i ∈ zeroSet (ScIso.refl (ESc n m)) (c.φ (γ a)) :=
    (mem_zeroSet _).2 (hγU a ha).2
  obtain ⟨V, hV, hxV, hret, hsec⟩ := hs.2 c isTameChart_chart₀ n (rnSc m) (ScIso.refl (ESc n m)) hT₀
    (γ a) ⟨(hγU a ha).1, mem_univ _⟩ i hi
  have hg := hsec.isScSmooth.continuousOn hret
  set h : α → (ESc n m) 0 := fun a => ((γ a : Q n m) : (ESc n m) 0) with hh
  have hhc : Continuous h := continuous_subtype_val.comp hγ
  have hmaps : MapsTo h (S ∩ h ⁻¹' V)
      (c.φ.model.O ∩ V ∩ coordHyper (ScIso.refl (ESc n m)) i) := fun b hb =>
    ⟨⟨(γ b).2, hb.2⟩, (hγU b hb.1).2⟩
  have h1 : ContinuousWithinAt (localRepOne c s ∘ h) (S ∩ h ⁻¹' V) a :=
    (hg (h a) (hmaps ⟨ha, hxV⟩)).comp hhc.continuousWithinAt hmaps
  have h2 : ContinuousWithinAt (fun b => (localRepOne c s (h b)).2) (S ∩ h ⁻¹' V) a :=
    continuous_snd.continuousAt.comp_continuousWithinAt h1
  have hsymm : ∀ b, (baseChart n m).symm (h b) = γ b := fun b =>
    Subtype.ext (baseChart_symm_val (γ b).2)
  have heq : ∀ b, (localRepOne c s (h b)).2 = (show Q n m × (Fin k → ℝ) from s (γ b)).2 :=
    fun b => by
      change Function.invFun ((rnSc k).toBase 1)
        (show Q n m × (Fin k → ℝ) from s ((baseChart n m).symm (h b))).2 = _
      rw [hsymm, hι]
  have h3 : ContinuousWithinAt (fun b => (show Q n m × (Fin k → ℝ) from s (γ b)).2)
      (S ∩ h ⁻¹' V) a := h2.congr (fun b _ => (heq b).symm) (heq a).symm
  exact h3.mono_of_mem_nhdsWithin (inter_mem_nhdsWithin S ((hV.preimage hhc).mem_nhds hxV))

/-- Copy of `QuadrantBundle.isEpFace_subset_coord`. -/
theorem isEpFace_subset_coord' {F : Set (quadSEP n m k).Obj}
    (hF : (quadSEP n m k).X.IsEpFace F) : ∃ i : Fin n, F ⊆ {p : Q n m | coord i p = 0} := by
  obtain ⟨θ, hθ, rfl⟩ := hF
  have h := TameBoundary.exists_isFaceIn_univ_preimage (dS := dq n (rnSc m))
    (EpGroupoid.Examples.isHomeomorph_π_trivial (basePoly n m)) (fun _ => rfl)
    (EpGroupoid.isOrbitFace_iff_isFaceIn.1 hθ)
  obtain ⟨p, -, hp1, hp⟩ := h
  obtain ⟨i, hi⟩ := dq_eq_one_iff.1 hp1
  refine ⟨i, ?_⟩
  change (EpGroupoid.trivial (basePoly n m)).π ⁻¹' θ ⊆ _
  rw [hp]
  exact faceAt_subset_coord_eq_zero univ hi

/-- Copy of `QuadrantBundle.exists_isEpFace_mem_of_part` (through `isEpFace_subset_coord'`). -/
theorem exists_isEpFace_mem_of_part' {p : Q n m} {i : Fin n} (hp : p ∈ part i) :
    ∃ F : Set (quadSEP n m k).Obj, (quadSEP n m k).X.IsEpFace F ∧ p ∈ F ∧
      F ⊆ {q : Q n m | coord i q = 0} := by
  have hd : (EpGroupoid.trivial (basePoly n m)).degIndexOrbit
      ((EpGroupoid.trivial (basePoly n m)).π p) = 1 := dq_eq_one_iff.2 ⟨i, hp⟩
  have hF : (quadSEP n m k).X.IsEpFace ((EpGroupoid.trivial (basePoly n m)).faceObj
      (closure (connectedComponentIn {w | (EpGroupoid.trivial (basePoly n m)).degIndexOrbit w = 1}
        ((EpGroupoid.trivial (basePoly n m)).π p)))) := ⟨_, ⟨_, hd, rfl⟩, rfl⟩
  have hpF : p ∈ (EpGroupoid.trivial (basePoly n m)).faceObj
      (closure (connectedComponentIn {w | (EpGroupoid.trivial (basePoly n m)).degIndexOrbit w = 1}
        ((EpGroupoid.trivial (basePoly n m)).π p))) :=
    subset_closure (mem_connectedComponentIn hd)
  refine ⟨_, hF, hpF, ?_⟩
  obtain ⟨j, hj⟩ := isEpFace_subset_coord' hF
  have hji : j = i := by
    by_contra hne
    exact (hp.2 j hne).ne' (hj hpF)
  rw [← hji]; exact hj

/-- Copy of `FaceCorner.subset_Z_one` (through the copied `isEpFace_subset_coord'`). -/
theorem subset_Z_one' {F : Set FaceCorner.A.Obj} (hF : FaceCorner.A.X.IsEpFace F)
    (h : ¬ F ⊆ Z 0) : F ⊆ Z 1 := by
  obtain ⟨i, hi⟩ := isEpFace_subset_coord' hF
  fin_cases i
  · exact absurd hi h
  · exact hi

/-- Copy of `FaceCorner.isCompatibleAssignment_Λt`. -/
theorem isCompatibleAssignment_Λt' : IsCompatibleAssignment Λt := by
  intro F hF F' hF'
  refine Quotient.sound ⟨fun w hw => ?_,
    fun x => ((signTuple (contDiff_germMap F) F).nbhd ⟨x, x.2.1⟩).U ∩
      ((signTuple (contDiff_germMap F') F').nbhd ⟨x, x.2.2⟩).U,
    fun x => ((signTuple (contDiff_germMap F) F).nbhd _).isOpen_U.inter
      ((signTuple (contDiff_germMap F') F').nbhd _).isOpen_U,
    fun x => ⟨((signTuple (contDiff_germMap F) F).nbhd _).mem_U,
      ((signTuple (contDiff_germMap F') F').nbhd _).mem_U⟩,
    fun x y hy => ⟨⟨hy.1.1, hy.2⟩, ⟨hy.1.2, hy.2⟩⟩, fun _ => rfl,
    fun _ _ _ _ => (IndexCorr.map_cast_rfl _).symm⟩
  change signMulti (germMap F) w = signMulti (germMap F') w
  refine signMulti_congr w ?_
  unfold germMap
  by_cases h : F ⊆ Z 0 <;> by_cases h' : F' ⊆ Z 0
  · rw [if_pos h, if_pos h']; exact Or.inl rfl
  · rw [if_pos h, if_neg h']
    exact φ₁_eq_or (h hw.1) (subset_Z_one' hF' h' hw.2)
  · rw [if_neg h, if_pos h']
    rcases φ₁_eq_or (h' hw.2) (subset_Z_one' hF h hw.1) with e | e
    · exact Or.inl e.symm
    · exact Or.inr (neg_eq_iff_eq_neg.2 e).symm
  · rw [if_neg h, if_neg h']; exact Or.inl rfl

/-- Copy of `FaceCorner.not_isBoundaryScPlusMultisection_of_eq_on_faces`. -/
theorem not_isBoundaryScPlusMultisection' {Λ : FaceCorner.A.W → ℚ≥0}
    (hΛF : ∀ F (_ : FaceCorner.A.X.IsEpFace F) w, FaceCorner.A.P w ∈ F →
      Λ w = signMulti (germMap F) w) :
    ¬ IsBoundaryScPlusMultisection FaceCorner.A Λ := by
  intro hΛ
  have hx0 : (show FaceCorner.A.Obj from pt 0 0 0) ∈ FaceCorner.A.X.PObj.boundary :=
    mem_boundary_of_coord (i := 0) (max_self 0)
  obtain ⟨V, -, ⟨S⟩⟩ := hΛ.2 _ hx0
  have hopen : IsOpen (show Set (Q 2 1) from V.U) := V.isOpen_U
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen (pt 0 0 0) V.mem_U
  obtain ⟨i⟩ := S.nonempty
  have hr : 0 < ρ / 2 := half_pos hρ
  have hrρ : ρ / 2 < ρ := half_lt_self hρ
  set r := ρ / 2 with hrdef
  have hU₁ : ∀ u ∈ Icc (-1 : ℝ) 1, path₁ r u ∈ V.bdry ∧ coord 0 (path₁ r u) = 0 := fun u hu =>
    ⟨⟨hball (Metric.mem_ball.2 (dist_path₁_lt hr hrρ hu)),
      mem_boundary_of_coord (coord_zero_path₁ r u)⟩, coord_zero_path₁ r u⟩
  have hU₂ : ∀ u ∈ Icc (-1 : ℝ) 1, path₂ r u ∈ V.bdry ∧ coord 1 (path₂ r u) = 0 := fun u hu =>
    ⟨⟨hball (Metric.mem_ball.2 (dist_path₂_lt hr hrρ hu)),
      mem_boundary_of_coord (coord_one_path₂ r u)⟩, coord_one_path₂ r u⟩
  set v : Q 2 1 → Fin 2 → ℝ := fun p => (show Q 2 1 × (Fin 2 → ℝ) from S.s i p).2 with hvdef
  have hv₁ : ContinuousOn (fun u => v (path₁ r u)) (Icc (-1) 1) :=
    continuousOn_snd_comp' (S.isFaceScPlus i) (continuous_path₁ r) 0 hU₁
  have hv₂ : ContinuousOn (fun u => v (path₂ r u)) (Icc (-1) 1) :=
    continuousOn_snd_comp' (S.isFaceScPlus i) (continuous_path₂ r) 1 hU₂
  have hval : ∀ y : Q 2 1, y ∈ V.bdry → ∀ F, FaceCorner.A.X.IsEpFace F → y ∈ F →
      ∃ b : Bool, v y = sgn b • germMap F (y : E₀) := by
    intro y hy F hF hyF
    have hP : FaceCorner.A.P (S.s i y) = y := S.P_s i hy
    have hne : Λ (S.s i y) ≠ 0 := by
      rw [S.rep (S.s i y) (by rw [hP]; exact hy), hP]
      refine mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) ?_
      exact Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, by simp⟩)
    rw [hΛF F hF _ (by rw [hP]; exact hyF)] at hne
    obtain ⟨b, hb⟩ := exists_sign_of_signMulti_ne_zero hne
    have hP' : (show Q 2 1 × (Fin 2 → ℝ) from S.s i y).1 = y := hP
    exact ⟨b, hb.trans (congrArg (fun z : Q 2 1 => sgn b • germMap F (z : E₀)) hP')⟩
  have hpart₁ : ∀ u ∈ Ioo (-1 : ℝ) 1, ∃ b : Bool,
      v (path₁ r u) = sgn b • φ₁ (path₁ r u : E₀) := by
    intro u hu
    obtain ⟨F, hF, hyF, hFZ⟩ := exists_isEpFace_mem_of_part' (k := 2) (path₁_mem_part hr hu)
    obtain ⟨b, hb⟩ := hval _ (hU₁ u (Ioo_subset_Icc_self hu)).1 F hF hyF
    have hF0 : F ⊆ Z 0 := hFZ
    rw [germMap, if_pos hF0] at hb
    exact ⟨b, hb⟩
  have hpart₂ : ∀ u ∈ Ioo (-1 : ℝ) 1, ∃ b : Bool,
      v (path₂ r u) = sgn b • φ₂ (path₂ r u : E₀) := by
    intro u hu
    have hp := path₂_mem_part hr hu
    obtain ⟨F, hF, hyF, -⟩ := exists_isEpFace_mem_of_part' (k := 2) hp
    obtain ⟨b, hb⟩ := hval _ (hU₂ u (Ioo_subset_Icc_self hu)).1 F hF hyF
    have hF0 : ¬ F ⊆ Z 0 := fun h0 => (hp.2 0 (by decide)).ne' (h0 hyF)
    rw [germMap, if_neg hF0] at hb
    exact ⟨b, hb⟩
  have hφ₁c : ContinuousOn (fun u => φ₁ (path₁ r u : E₀)) (Icc (-1) 1) :=
    (contDiff_φ₁.continuous.comp (continuous_subtype_val.comp (continuous_path₁ r))).continuousOn
  have hφ₂c : ContinuousOn (fun u => φ₂ (path₂ r u : E₀)) (Icc (-1) 1) :=
    (contDiff_φ₂.continuous.comp (continuous_subtype_val.comp (continuous_path₂ r))).continuousOn
  obtain ⟨b₁, hm₁, hp₁⟩ := exists_sign_endpoints hv₁ hφ₁c (fun _ _ => φ₁_path₁_ne_zero hr) hpart₁
  obtain ⟨b₂, hm₂, hp₂⟩ := exists_sign_endpoints hv₂ hφ₂c (fun _ _ => φ₂_path₂_ne_zero hr) hpart₂
  have he := expNegInvGlue.pos_of_pos hr
  have a1 : v (path₁ r 1) 0 = sgn b₁ * hfun (r * 1) := congrFun hp₁ 0
  have a2 : v (path₂ r 1) 0 = sgn b₂ * gfun (r * 1) := congrFun hp₂ 0
  have a3 : v (path₁ r (-1)) 0 = sgn b₁ * hfun (r * -1) := congrFun hm₁ 0
  have a4 : v (path₂ r (-1)) 0 = sgn b₂ * gfun (r * -1) := congrFun hm₂ 0
  rw [path₁_one, mul_one, hfun_of_nonneg hr.le] at a1
  rw [path₂_one, mul_one, gfun_of_nonneg hr.le] at a2
  rw [path₁_neg_one, mul_neg_one, hfun_of_nonpos (neg_nonpos.2 hr.le), neg_neg] at a3
  rw [path₂_neg_one, mul_neg_one, gfun_of_nonpos (neg_nonpos.2 hr.le), neg_neg] at a4
  have h1 : sgn b₁ * expNegInvGlue r = sgn b₂ * expNegInvGlue r := a1.symm.trans a2
  have h2 : sgn b₁ * expNegInvGlue r = sgn b₂ * -expNegInvGlue r := a3.symm.trans a4
  have h3 : sgn b₁ * expNegInvGlue r = 0 := by linarith
  exact mul_ne_zero (sgn_ne_zero b₁) he.ne' h3

end

end RoundTrip.V14_43Corner

namespace RoundTrip.V14_43
open Polyfold Polyfold.SBLocalization

/-- The project's statement at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.isCompatibleAssignment.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.Λg_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.faceSel_spec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.exists_adapted.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.sg_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.mem_mor_face.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.τg_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.Φ_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.isBoundaryScPlusMultisection.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.glue_Λ.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.glue_U_inter_subset.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.glue_s.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.glue_τ.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.zero_Λg.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_charged.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3_extension.{0}) ∧
  (type_of% @Polyfold.FaceCorner.not_exists_sectionCompatibleFaceData) ∧
  (type_of% @Polyfold.FaceCorner.isCompatibleAssignment_Λt) ∧
  (type_of% @Polyfold.FaceCorner.not_isBoundaryScPlusMultisection_of_eq_on_faces) ∧
  (type_of% @Polyfold.FaceCorner.not_theorem_14_6_3_class_statement) ∧
  (type_of% @Polyfold.FaceCorner.not_exists_compatibleFaceData) ∧
  (type_of% @Polyfold.FaceCorner.theorem_14_6_3_corner_witness) ∧
  (type_of% @Polyfold.FaceCorner.isEpFaceStructured_A) ∧
  (type_of% @Polyfold.QuadrantBundle.continuousOn_snd_comp_of_isFaceScPlusSectionOn.{0}) ∧
  (type_of% @Polyfold.QuadrantBundle.isEpFace_subset_coord) ∧
  (type_of% @Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3_extension.{0}) ∧
  (type_of% @Polyfold.SBLocalization.RelTuple.Equiv.cast_smul.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsSecCompatibleAssignment.theorem_14_6_3.{0}) ∧
  (type_of% @Polyfold.FaceCorner.theorem_14_6_3_families_witness) ∧
  (type_of% @Polyfold.FaceCorner.card_familiesWitness_ne) ∧
  (type_of% @Polyfold.FaceCorner.theorem_14_6_3_extension_corner)

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.CompatibleFaceData.isCompatibleAssignment.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.Λg_eq.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.faceSel_spec.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.exists_adapted.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.sg_eq.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.mem_mor_face.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.τg_eq.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.Φ_eq.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.isBoundaryScPlusMultisection.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.glue_Λ.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.glue_U_inter_subset.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.glue_s.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.glue_τ.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_hyp.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_hyp.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.zero_Λg.{0},
   @Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_charged.{0},
   @Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3.{0},
   @Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3_extension.{0},
   @Polyfold.FaceCorner.not_exists_sectionCompatibleFaceData,
   @Polyfold.FaceCorner.isCompatibleAssignment_Λt,
   @Polyfold.FaceCorner.not_isBoundaryScPlusMultisection_of_eq_on_faces,
   @Polyfold.FaceCorner.not_theorem_14_6_3_class_statement,
   @Polyfold.FaceCorner.not_exists_compatibleFaceData,
   @Polyfold.FaceCorner.theorem_14_6_3_corner_witness,
   @Polyfold.FaceCorner.isEpFaceStructured_A,
   @Polyfold.QuadrantBundle.continuousOn_snd_comp_of_isFaceScPlusSectionOn.{0},
   @Polyfold.QuadrantBundle.isEpFace_subset_coord,
   @Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension.{0},
   @Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3.{0},
   @Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3_extension.{0},
   @Polyfold.SBLocalization.RelTuple.Equiv.cast_smul.{0},
   @Polyfold.SBLocalization.IsSecCompatibleAssignment.theorem_14_6_3.{0},
   @Polyfold.FaceCorner.theorem_14_6_3_families_witness,
   @Polyfold.FaceCorner.card_familiesWitness_ne,
   @Polyfold.FaceCorner.theorem_14_6_3_extension_corner⟩

/-- `B` does not hold at the corner, given the facts of the project's counterexample. -/
theorem refute (hstr : FaceCorner.A.X.IsEpFaceStructured)
    (hcomp : IsCompatibleAssignment FaceCorner.Λt)
    (hkey : ¬ ∃ Λ : FaceCorner.A.W → ℚ≥0, IsBoundaryScPlusMultisection FaceCorner.A Λ ∧
      ∀ F (hF : FaceCorner.A.X.IsEpFace F) w, FaceCorner.A.P w ∈ F →
        Λ w = (Quotient.out (FaceCorner.Λt F hF)).2.Λ w) : ¬ B := by
  intro hB
  obtain ⟨L, hL, -⟩ := hB FaceCorner.A hstr.1 hstr FaceCorner.Λt hcomp
  exact hkey ⟨L.forget, (Quotient.out L).isBoundaryScPlusMultisection, hL⟩

/-- The conjunct `not_theorem_14_6_3_class_statement` of `A` refutes `B`. -/
theorem classStatement_to_notB
    (h : type_of% @Polyfold.FaceCorner.not_theorem_14_6_3_class_statement) : ¬ B :=
  refute h.1 h.2.2.2.1 h.2.2.2.2.1

/-- `A` refutes `B` (through `classStatement_to_notB`). -/
theorem A_to_notB (hA : A) : ¬ B :=
  classStatement_to_notB hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `B` does not hold, without the item's theorems. -/
theorem not_B : ¬ B := by
  refine refute RoundTrip.V14_43Corner.isEpFaceStructured_A'
    RoundTrip.V14_43Corner.isCompatibleAssignment_Λt' ?_
  rintro ⟨Λ, hΛ, hF⟩
  exact RoundTrip.V14_43Corner.not_isBoundaryScPlusMultisection'
    (fun F hF' w hw => (hF F hF' w hw).trans
      ((Quotient.exact (Quotient.out_eq (FaceCorner.Λt F hF'))).1 w hw)) hΛ

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

theorem B_to_A : B → A := fun h => absurd h not_B

/-- The main conjunct, from `B` (ex falso). -/
theorem B_to_main : B → type_of% @Polyfold.SBLocalization.IsSecCompatibleAssignment.theorem_14_6_3.{0} :=
  fun h => absurd h not_B

#rt_check RoundTrip.V14_43.not_B [Polyfold.SBLocalization.CompatibleFaceData.isCompatibleAssignment,
  Polyfold.SBLocalization.CompatibleFaceData.Λg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.faceSel_spec,
  Polyfold.SBLocalization.CompatibleFaceData.exists_adapted,
  Polyfold.SBLocalization.CompatibleFaceData.sg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.mem_mor_face,
  Polyfold.SBLocalization.CompatibleFaceData.τg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.Φ_eq,
  Polyfold.SBLocalization.CompatibleFaceData.isBoundaryScPlusMultisection,
  Polyfold.SBLocalization.CompatibleFaceData.glue_Λ,
  Polyfold.SBLocalization.CompatibleFaceData.glue_U_inter_subset,
  Polyfold.SBLocalization.CompatibleFaceData.glue_s,
  Polyfold.SBLocalization.CompatibleFaceData.glue_τ,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_hyp,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_hyp,
  Polyfold.SBLocalization.CompatibleFaceData.zero_Λg,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_charged,
  Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3,
  Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3_extension,
  Polyfold.FaceCorner.not_exists_sectionCompatibleFaceData,
  Polyfold.FaceCorner.isCompatibleAssignment_Λt,
  Polyfold.FaceCorner.not_isBoundaryScPlusMultisection_of_eq_on_faces,
  Polyfold.FaceCorner.not_theorem_14_6_3_class_statement,
  Polyfold.FaceCorner.not_exists_compatibleFaceData,
  Polyfold.FaceCorner.theorem_14_6_3_corner_witness,
  Polyfold.FaceCorner.isEpFaceStructured_A,
  Polyfold.QuadrantBundle.continuousOn_snd_comp_of_isFaceScPlusSectionOn,
  Polyfold.QuadrantBundle.isEpFace_subset_coord,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension,
  Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3,
  Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3_extension,
  Polyfold.SBLocalization.RelTuple.Equiv.cast_smul,
  Polyfold.SBLocalization.IsSecCompatibleAssignment.theorem_14_6_3,
  Polyfold.FaceCorner.theorem_14_6_3_families_witness,
  Polyfold.FaceCorner.card_familiesWitness_ne,
  Polyfold.FaceCorner.theorem_14_6_3_extension_corner
]
#rt_check RoundTrip.V14_43.B_to_main [Polyfold.SBLocalization.CompatibleFaceData.isCompatibleAssignment,
  Polyfold.SBLocalization.CompatibleFaceData.Λg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.faceSel_spec,
  Polyfold.SBLocalization.CompatibleFaceData.exists_adapted,
  Polyfold.SBLocalization.CompatibleFaceData.sg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.mem_mor_face,
  Polyfold.SBLocalization.CompatibleFaceData.τg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.Φ_eq,
  Polyfold.SBLocalization.CompatibleFaceData.isBoundaryScPlusMultisection,
  Polyfold.SBLocalization.CompatibleFaceData.glue_Λ,
  Polyfold.SBLocalization.CompatibleFaceData.glue_U_inter_subset,
  Polyfold.SBLocalization.CompatibleFaceData.glue_s,
  Polyfold.SBLocalization.CompatibleFaceData.glue_τ,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_hyp,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_hyp,
  Polyfold.SBLocalization.CompatibleFaceData.zero_Λg,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_charged,
  Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3,
  Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3_extension,
  Polyfold.FaceCorner.not_exists_sectionCompatibleFaceData,
  Polyfold.FaceCorner.isCompatibleAssignment_Λt,
  Polyfold.FaceCorner.not_isBoundaryScPlusMultisection_of_eq_on_faces,
  Polyfold.FaceCorner.not_theorem_14_6_3_class_statement,
  Polyfold.FaceCorner.not_exists_compatibleFaceData,
  Polyfold.FaceCorner.theorem_14_6_3_corner_witness,
  Polyfold.FaceCorner.isEpFaceStructured_A,
  Polyfold.QuadrantBundle.continuousOn_snd_comp_of_isFaceScPlusSectionOn,
  Polyfold.QuadrantBundle.isEpFace_subset_coord,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension,
  Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3,
  Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3_extension,
  Polyfold.SBLocalization.RelTuple.Equiv.cast_smul,
  Polyfold.SBLocalization.IsSecCompatibleAssignment.theorem_14_6_3,
  Polyfold.FaceCorner.theorem_14_6_3_families_witness,
  Polyfold.FaceCorner.card_familiesWitness_ne,
  Polyfold.FaceCorner.theorem_14_6_3_extension_corner
]
#rt_check RoundTrip.V14_43.classStatement_to_notB [Polyfold.SBLocalization.CompatibleFaceData.isCompatibleAssignment,
  Polyfold.SBLocalization.CompatibleFaceData.Λg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.faceSel_spec,
  Polyfold.SBLocalization.CompatibleFaceData.exists_adapted,
  Polyfold.SBLocalization.CompatibleFaceData.sg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.mem_mor_face,
  Polyfold.SBLocalization.CompatibleFaceData.τg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.Φ_eq,
  Polyfold.SBLocalization.CompatibleFaceData.isBoundaryScPlusMultisection,
  Polyfold.SBLocalization.CompatibleFaceData.glue_Λ,
  Polyfold.SBLocalization.CompatibleFaceData.glue_U_inter_subset,
  Polyfold.SBLocalization.CompatibleFaceData.glue_s,
  Polyfold.SBLocalization.CompatibleFaceData.glue_τ,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_hyp,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_hyp,
  Polyfold.SBLocalization.CompatibleFaceData.zero_Λg,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_charged,
  Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3,
  Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3_extension,
  Polyfold.FaceCorner.not_exists_sectionCompatibleFaceData,
  Polyfold.FaceCorner.isCompatibleAssignment_Λt,
  Polyfold.FaceCorner.not_isBoundaryScPlusMultisection_of_eq_on_faces,
  Polyfold.FaceCorner.not_theorem_14_6_3_class_statement,
  Polyfold.FaceCorner.not_exists_compatibleFaceData,
  Polyfold.FaceCorner.theorem_14_6_3_corner_witness,
  Polyfold.FaceCorner.isEpFaceStructured_A,
  Polyfold.QuadrantBundle.continuousOn_snd_comp_of_isFaceScPlusSectionOn,
  Polyfold.QuadrantBundle.isEpFace_subset_coord,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension,
  Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3,
  Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3_extension,
  Polyfold.SBLocalization.RelTuple.Equiv.cast_smul,
  Polyfold.SBLocalization.IsSecCompatibleAssignment.theorem_14_6_3,
  Polyfold.FaceCorner.theorem_14_6_3_families_witness,
  Polyfold.FaceCorner.card_familiesWitness_ne,
  Polyfold.FaceCorner.theorem_14_6_3_extension_corner
]

/-! Every term mentioning `A` reaches `CompatibleFaceData.Λg_eq`, `τg_eq`, `Φ_eq` and
`RelTuple.Equiv.cast_smul` through the bodies of the vocabulary definitions `CompatibleFaceData.S`
and `CompatibleFaceData.tau` (used directly in their structure fields, not as abstracted
`_proof_` terms), so neither `#rt_check` nor `#rt_check_soft` can pass on `B_to_A` or
`A_to_notB`; the checks are recorded as failing below.  The content of `A_to_notB` is
`classStatement_to_notB` (rt_check OK), and `B_to_A` is ex falso from `not_B` (rt_check OK). -/
#guard_msgs (drop error) in
#rt_check_soft RoundTrip.V14_43.B_to_A [Polyfold.SBLocalization.CompatibleFaceData.isCompatibleAssignment,
  Polyfold.SBLocalization.CompatibleFaceData.Λg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.faceSel_spec,
  Polyfold.SBLocalization.CompatibleFaceData.exists_adapted,
  Polyfold.SBLocalization.CompatibleFaceData.sg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.mem_mor_face,
  Polyfold.SBLocalization.CompatibleFaceData.τg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.Φ_eq,
  Polyfold.SBLocalization.CompatibleFaceData.isBoundaryScPlusMultisection,
  Polyfold.SBLocalization.CompatibleFaceData.glue_Λ,
  Polyfold.SBLocalization.CompatibleFaceData.glue_U_inter_subset,
  Polyfold.SBLocalization.CompatibleFaceData.glue_s,
  Polyfold.SBLocalization.CompatibleFaceData.glue_τ,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_hyp,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_hyp,
  Polyfold.SBLocalization.CompatibleFaceData.zero_Λg,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_charged,
  Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3,
  Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3_extension,
  Polyfold.FaceCorner.not_exists_sectionCompatibleFaceData,
  Polyfold.FaceCorner.isCompatibleAssignment_Λt,
  Polyfold.FaceCorner.not_isBoundaryScPlusMultisection_of_eq_on_faces,
  Polyfold.FaceCorner.not_theorem_14_6_3_class_statement,
  Polyfold.FaceCorner.not_exists_compatibleFaceData,
  Polyfold.FaceCorner.theorem_14_6_3_corner_witness,
  Polyfold.FaceCorner.isEpFaceStructured_A,
  Polyfold.QuadrantBundle.continuousOn_snd_comp_of_isFaceScPlusSectionOn,
  Polyfold.QuadrantBundle.isEpFace_subset_coord,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension,
  Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3,
  Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3_extension,
  Polyfold.SBLocalization.RelTuple.Equiv.cast_smul,
  Polyfold.SBLocalization.IsSecCompatibleAssignment.theorem_14_6_3,
  Polyfold.FaceCorner.theorem_14_6_3_families_witness,
  Polyfold.FaceCorner.card_familiesWitness_ne,
  Polyfold.FaceCorner.theorem_14_6_3_extension_corner
]
#guard_msgs (drop error) in
#rt_check_soft RoundTrip.V14_43.A_to_notB [Polyfold.SBLocalization.CompatibleFaceData.isCompatibleAssignment,
  Polyfold.SBLocalization.CompatibleFaceData.Λg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.faceSel_spec,
  Polyfold.SBLocalization.CompatibleFaceData.exists_adapted,
  Polyfold.SBLocalization.CompatibleFaceData.sg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.mem_mor_face,
  Polyfold.SBLocalization.CompatibleFaceData.τg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.Φ_eq,
  Polyfold.SBLocalization.CompatibleFaceData.isBoundaryScPlusMultisection,
  Polyfold.SBLocalization.CompatibleFaceData.glue_Λ,
  Polyfold.SBLocalization.CompatibleFaceData.glue_U_inter_subset,
  Polyfold.SBLocalization.CompatibleFaceData.glue_s,
  Polyfold.SBLocalization.CompatibleFaceData.glue_τ,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_hyp,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_hyp,
  Polyfold.SBLocalization.CompatibleFaceData.zero_Λg,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_charged,
  Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3,
  Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3_extension,
  Polyfold.FaceCorner.not_exists_sectionCompatibleFaceData,
  Polyfold.FaceCorner.isCompatibleAssignment_Λt,
  Polyfold.FaceCorner.not_isBoundaryScPlusMultisection_of_eq_on_faces,
  Polyfold.FaceCorner.not_theorem_14_6_3_class_statement,
  Polyfold.FaceCorner.not_exists_compatibleFaceData,
  Polyfold.FaceCorner.theorem_14_6_3_corner_witness,
  Polyfold.FaceCorner.isEpFaceStructured_A,
  Polyfold.QuadrantBundle.continuousOn_snd_comp_of_isFaceScPlusSectionOn,
  Polyfold.QuadrantBundle.isEpFace_subset_coord,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension,
  Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3,
  Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3_extension,
  Polyfold.SBLocalization.RelTuple.Equiv.cast_smul,
  Polyfold.SBLocalization.IsSecCompatibleAssignment.theorem_14_6_3,
  Polyfold.FaceCorner.theorem_14_6_3_families_witness,
  Polyfold.FaceCorner.card_familiesWitness_ne,
  Polyfold.FaceCorner.theorem_14_6_3_extension_corner
]
#rt_overlap RoundTrip.V14_43.not_B [Polyfold.SBLocalization.CompatibleFaceData.isCompatibleAssignment,
  Polyfold.SBLocalization.CompatibleFaceData.Λg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.faceSel_spec,
  Polyfold.SBLocalization.CompatibleFaceData.exists_adapted,
  Polyfold.SBLocalization.CompatibleFaceData.sg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.mem_mor_face,
  Polyfold.SBLocalization.CompatibleFaceData.τg_eq,
  Polyfold.SBLocalization.CompatibleFaceData.Φ_eq,
  Polyfold.SBLocalization.CompatibleFaceData.isBoundaryScPlusMultisection,
  Polyfold.SBLocalization.CompatibleFaceData.glue_Λ,
  Polyfold.SBLocalization.CompatibleFaceData.glue_U_inter_subset,
  Polyfold.SBLocalization.CompatibleFaceData.glue_s,
  Polyfold.SBLocalization.CompatibleFaceData.glue_τ,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_hyp,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_hyp,
  Polyfold.SBLocalization.CompatibleFaceData.zero_Λg,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension_charged,
  Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3,
  Polyfold.SBLocalization.SectionCompatibleFaceData.theorem_14_6_3_extension,
  Polyfold.FaceCorner.not_exists_sectionCompatibleFaceData,
  Polyfold.FaceCorner.isCompatibleAssignment_Λt,
  Polyfold.FaceCorner.not_isBoundaryScPlusMultisection_of_eq_on_faces,
  Polyfold.FaceCorner.not_theorem_14_6_3_class_statement,
  Polyfold.FaceCorner.not_exists_compatibleFaceData,
  Polyfold.FaceCorner.theorem_14_6_3_corner_witness,
  Polyfold.FaceCorner.isEpFaceStructured_A,
  Polyfold.QuadrantBundle.continuousOn_snd_comp_of_isFaceScPlusSectionOn,
  Polyfold.QuadrantBundle.isEpFace_subset_coord,
  Polyfold.SBLocalization.CompatibleFaceData.theorem_14_6_3_extension,
  Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3,
  Polyfold.SBLocalization.SectionCompatibleFaceFamilies.theorem_14_6_3_extension,
  Polyfold.SBLocalization.RelTuple.Equiv.cast_smul,
  Polyfold.SBLocalization.IsSecCompatibleAssignment.theorem_14_6_3,
  Polyfold.FaceCorner.theorem_14_6_3_families_witness,
  Polyfold.FaceCorner.card_familiesWitness_ne,
  Polyfold.FaceCorner.theorem_14_6_3_extension_corner
]
#print axioms RoundTrip.V14_43.not_B

end RoundTrip.V14_43
