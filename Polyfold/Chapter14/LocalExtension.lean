import Polyfold.Chapter14.GoodStructured
import Polyfold.Chapter12.ScPlusExtension

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.1, p. 642:
**Proposition 14.1.4** (Local Extension Result; 2017: Remark 14.2), the step the text calls "a
partition of unity argument": the non-equivariant extension of face-wise sc⁺ data from
`U(x) = V(x) ∩ ∂X` to an open set of `X`.

# Extension of face-wise sc⁺ data from `V ∩ ∂X`

## The text, paraphrased

(Proof of Proposition 14.1.4) Each `sᵢ`, given on `U(x)` with sc⁺ restrictions to the faces,
extends to an sc⁺-section `s̄⁰ᵢ` on `V(x)` with `s̄⁰ᵢ|U(x) = sᵢ` (Proposition 12.3.7 and an
sc-smooth partition of unity); then the `s̄⁰ᵢ` are averaged.

## What is formalized

* `StrongBundle.exists_local_extension_of_face`: Part I's local step (`exists_local_extension`,
  Proposition 12.3.7 in a tame chart, cut off by a bump function) with the hypothesis on `s` made
  local: the face condition only at the point `x`, and `P(s(y)) = y`, `s(y) ∈ W_{0,1}` only on
  `G ∩ ∂X` for an open `G ∋ x`.
* `SBLocalization.exists_scPlusSection_extension_of_face`: for `s` face-wise sc⁺ on `V ∩ ∂X`
  (`V` open) and an open `G` with `cl G ⊆ V` there is a (global) sc⁺-section `σ` of `P` with
  `σ = s` on `G ∩ ∂X`: the local extensions at the points of `V ∩ ∂X`, the zero section off `∂X`
  and off `cl G`, glued by an sc-smooth partition of unity of the object M-polyfold.
* **Proposition 14.1.4** in two forms:
  * `proposition_14_1_4_of_closure`: for every `V' ≤ V(x)` (same action) with `cl V' ⊆ V(x)` the
    restricted structure extends equivariantly to `V'` (no hypothesis on the extensions; this
    discharges the hypothesis of B1's `proposition_14_1_4_hyp` on `V'`);
  * `proposition_14_1_4`: for a good `V(x)` there is a good `V'(x) ≤ V(x)` with
    `cl V'(x) ⊆ V(x)` on which the structure extends.

## Reading

* "`X` admits sc-smooth partitions of unity" is Definition 5.5.1 for the object M-polyfold
  (`A.X.PObj.AdmitsScPartitionsOfUnity`), as in B1's `theorem_14_1_9_statement`.
* "A strong bundle over a tame ep-groupoid" provides the tame strong bundle charts; as in the
  cores of Theorem 12.3.9 (`exists_extension_of_tameCharts`) it is the hypothesis that every
  object lies in a tame strong bundle chart.
* This file gives the extension on every `V'` with `cl V' ⊆ V(x)`: a partition of unity of `X`
  subordinate to a cover by subsets of `V(x)` must also cover the frontier of `V(x)`.  The
  extension on `V(x)` itself (`OpenExtension.lean`, `proposition_14_1_4_full`) uses in
  addition an exhaustion of `V(x)` by the sets `cl G_n ⊆ G_{n+1}` of the metrizable object space.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u v

/-! ### The local step with local hypotheses -/

section LocalStep

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundle

variable {B : StrongBundle PX P}

/-- **The local step of Proposition 14.1.4** (Part I's `exists_local_extension` with local
hypotheses): let `x` lie in a tame strong bundle chart, let `s` be a section with values in
`W_{0,1}` on `G ∩ ∂X` for an open `G ∋ x`, sc⁺ on every local face germ at `x` (for `x ∉ ∂X`
there are none).  Then there are an
open `U` with `x ∈ U ⊆ G` and an sc⁺-section `σ` of `P` with `σ = s` on `U ∩ ∂X`. -/
theorem exists_local_extension_of_face (hbump : PX.AdmitsBumpFunctions)
    {c : StrongBundleChart PX P} (hc : B.IsTameChart c) {x : X} (hx : x ∈ c.φ.source)
    {s : X → Y} {G : Set X} (hG : IsOpen G) (hxG : x ∈ G)
    (hsG : ∀ y ∈ G ∩ PX.boundary, P (s y) = y ∧ s y ∈ B.oneSet)
    (hface : ∀ (n : ℕ) (W : ScBanach)
      (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
      c.φ.model.C = T 0 ⁻¹' quadrant n W 0 → ∀ i ∈ zeroSet T (c.φ x),
        IsScPlusOnFaceNear T c.φ.model.C c.φ.model.O c.K (localRepOne c s) (c.φ x) i) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ G ∧ ∃ σ : X → Y, B.IsScPlusSection σ ∧
      ∀ y ∈ U ∩ PX.boundary, σ y = s y := by
  classical
  obtain ⟨n, W, T, hT⟩ := c.φ.model.isPartialQuadrant
  have htame := hc.2 n W T hT
  have hx₀ : c.φ x ∈ (c.isRetraction.baseRetraction c.relOpen).retract := by
    rw [c.base_retract]; exact c.φ.mapsTo_model x hx
  obtain ⟨V, hV, hxV, -, hext, hagree⟩ := proposition_12_3_7_of_faces_at T hT c.relOpen
    c.isRetraction htame hx₀ (s := localRepOne c s) (by
      intro i hi; rw [c.base_retract]; exact hface n W T hT i hi)
  rw [c.base_retract] at hext hagree
  set e := boundaryExtension T c.R (zeroSet T (c.φ x)) (localRepOne c s) with he
  set S := c.φ.source ∩ c.φ ⁻¹' V with hSdef
  have hSo : IsOpen S := c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source hV
  have hSs : S ⊆ c.φ.source := inter_subset_left
  set c' := c.restrict hSs hSo with hc'def
  have hc' : B.IsChart c' := fun c'' hc'' => (hc.1 c'' hc'').restrict_left hSs hSo
  have hO' : c.φ '' S = c.φ.model.O ∩ V := by
    rw [hSdef, Set.image_inter_preimage, c.φ.image_source]
  have hτ : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O
      (c'.φ.model.E.prod c'.F.shift) (c'.φ.model.C ×ˢ univ) (strongShiftOne c'.K)
      (fun z => (z, (e z).2)) := by
    change IsScSmoothRetractMap c.φ.model.E c.φ.model.C (c.φ '' S)
      (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ) (strongShiftOne c'.K)
      (fun z => (z, (e z).2))
    rw [hO']
    refine (hext.isScSmooth.congr (f' := fun z => (z, (e z).2))
      fun z hz => Prod.ext (hext.fst_eq z hz) rfl).mono_target
      fun z hz => ?_
    change (z, c.F.toBase 1 (e z).2) ∈ c'.K
    rw [c.restrict_K hSs hSo]
    refine ⟨?_, by rw [hO']; exact hz⟩
    have := hext.mem hz
    rwa [hext.fst_eq z hz] at this
  obtain ⟨β, hβ, -, -, hβS, hβev⟩ := proposition_5_5_3 hbump hSo ⟨hx, hxV⟩
  refine ⟨interior {y | β y = 1} ∩ S ∩ G, (isOpen_interior.inter hSo).inter hG,
    ⟨⟨mem_interior_iff_mem_nhds.2 hβev, hx, hxV⟩, hxG⟩, inter_subset_right,
    cutoffSection c' β (fun z => (e z).2),
    isScPlusSection_cutoffSection_of_isChart hc' hβ hβS hτ, ?_⟩
  rintro y ⟨⟨⟨hy1, hyS⟩, hyG⟩, hyb⟩
  have hβy : β y = 1 := interior_subset (s := {y | β y = 1}) hy1
  have hsy := hsG y ⟨hyG, hyb⟩
  have hys : s y ∈ c.toPartialEquiv.source := by
    rw [c.source_eq, mem_preimage, hsy.1]; exact hyS.1
  have hcut := cutoffSection_mem_source (β := β) hτ.mapsTo hyS
  have hcut' : cutoffSection c' β (fun z => (e z).2) y ∈ c.toPartialEquiv.source := by
    rw [c.source_eq]; exact hSs hcut
  refine c.toPartialEquiv.injOn hcut' hys ?_
  have h1 := apply_cutoffSection (β := β) hτ.mapsTo hyS
  change c (cutoffSection c' β (fun z => (e z).2) y) = c (s y)
  rw [show c (cutoffSection c' β (fun z => (e z).2) y) =
    c' (cutoffSection c' β (fun z => (e z).2) y) from rfl, h1, hβy]
  have hφy : c.φ y ∈ retractBoundary c.φ.model.E c.φ.model.C c.φ.model.O ∩ V :=
    ⟨⟨c.φ.mapsTo_model y hyS.1, degIndex_ne_zero_of_mem_boundary hc hyS.1 hyb⟩, hyS.2⟩
  have hey := hagree _ hφy
  refine Prod.ext ?_ ?_
  · change c.φ y = (c (s y)).1
    rw [c.covers _ hys, hsy.1]
  · change c.F.toBase 1 ((1 : ℝ) • (e (c.φ y)).2) = (c (s y)).2
    rw [one_smul, hey]
    change c.F.toBase 1 (Function.invFun (c.F.toBase 1) (c (s (c.φ.symm (c.φ y)))).2) = _
    rw [c.φ.symm_apply_apply hyS.1]
    exact Function.invFun_eq ((mem_oneSet_iff_of_isChart hc.1 hys).1 hsy.2)

end StrongBundle

end LocalStep

/-! ### Extension from `V ∩ ∂X` to an open `G` with `cl G ⊆ V` -/

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-- **The partition of unity step of Proposition 14.1.4**: let every object lie in a tame strong
bundle chart and let the object M-polyfold admit sc-smooth partitions of unity.  If `s` is
face-wise sc⁺ on `V ∩ ∂X` (`V` open, Definition 14.1.3 (1)) and `G` is a set with `cl G ⊆ V`,
then there is an sc⁺-section `σ` of `P` with `σ = s` on `G ∩ ∂X`.  (The local extensions of
`exists_local_extension_of_face` at the points of `V ∩ ∂X`, the zero section on `X ∖ ∂X` and on
`X ∖ cl G`, glued by a subordinate sc-smooth partition of unity.) -/
theorem exists_scPlusSection_extension_of_face
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) {s : A.Obj → A.W} {V G : Set A.Obj}
    (hV : IsOpen V) (hs : IsFaceScPlusSectionOn A s (V ∩ A.X.PObj.boundary))
    (hG : closure G ⊆ V) :
    ∃ σ : A.Obj → A.W, A.B.IsScPlusSection σ ∧ ∀ y ∈ G ∩ A.X.PObj.boundary, σ y = s y := by
  classical
  have hbump : A.X.PObj.AdmitsBumpFunctions := hpu.admitsBumpFunctions
  have hloc : ∀ y : A.Obj, ∃ U : Set A.Obj, IsOpen U ∧ y ∈ U ∧ ∃ σ : A.Obj → A.W,
      A.B.IsScPlusSection σ ∧ ∀ z ∈ U ∩ A.X.PObj.boundary, z ∈ G → σ z = s z := by
    intro y
    by_cases hyb : y ∈ A.X.PObj.boundary
    · by_cases hyV : y ∈ V
      · obtain ⟨c, hc, hyc⟩ := hB y
        obtain ⟨U, hU, hyU, -, σ, hσ, hσs⟩ := exists_local_extension_of_face hbump hc hyc
          hV hyV (fun z hz => hs.1 z hz)
          (fun n W T hT i hi => hs.2 c hc n W T hT y ⟨⟨hyV, hyb⟩, hyc⟩ i hi)
        exact ⟨U, hU, hyU, σ, hσ, fun z hz _ => hσs z hz⟩
      · refine ⟨(closure G)ᶜ, isClosed_closure.isOpen_compl, fun h => hyV (hG h),
          fiberZero A.P, isScPlusSection_fiberZero, fun z hz hzG => ?_⟩
        exact absurd (subset_closure hzG) hz.1
    · exact ⟨A.X.PObj.boundaryᶜ, A.X.PObj.isClosed_boundary.isOpen_compl, hyb, fiberZero A.P,
        isScPlusSection_fiberZero, fun z hz _ => absurd hz.2 hz.1⟩
  choose U hU hyU σ hσ hσs using hloc
  obtain ⟨ρ, hρsub, hρsm⟩ := hpu A.Obj U hU (iUnion_eq_univ_iff.2 fun y => ⟨y, hyU y⟩)
  have hsec : ∀ i, IsSection A.P (σ i) := fun i => (hσ i).1
  refine ⟨glueSection A.P ρ σ, isScPlusSection_glueSection (X := A.X) hρsm hσ, ?_⟩
  rintro y ⟨hyG, hyb⟩
  exact glueSection_eq_of hsec (hs.1 y ⟨hG (subset_closure hyG), hyb⟩).1
    fun i hi => hσs i y ⟨hρsub i hi, hyb⟩ hyG

/-! ### Proposition 14.1.4 -/

/-- **2021 Proposition 14.1.4, p. 642 (2017: Remark 14.2)**, on a smaller neighbourhood: let every
object lie in a tame strong bundle chart and let the object M-polyfold admit sc-smooth partitions
of unity.  For a symmetric sc⁺-section structure `(sᵢ)` on `U(x) = V(x) ∩ ∂X` (Definition 14.1.3)
and every `V' ≤ V(x)` with the same action and `cl V' ⊆ V(x)` there are sc⁺-sections `s̄ᵢ` on `V'`
with `s̄ᵢ = sᵢ` on `V' ∩ ∂X` and `s̄_{g(i)}(g ∗ y) = μ(Γ(g, y), s̄ᵢ(y))` for `y ∈ V'`
(Definition 13.2.5 (1)).  This discharges the hypothesis of `proposition_14_1_4_hyp` on `V'`. -/
theorem proposition_14_1_4_of_closure
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) {Λ : A.W → ℚ≥0} {x : A.Obj}
    {V : A.X.NatNbhd x} (S : BoundarySymmetricStructure A Λ V) {V' : A.X.NatNbhd x}
    (hle : V'.Le V) (hcl : closure V'.U ⊆ V.U) :
    ∃ sb : S.I → A.Obj → A.W, (∀ i, IsScPlusSectionOn A (sb i) V'.U) ∧
      (∀ i, ∀ y ∈ V'.bdry, sb i y = S.s i y) ∧
      ∀ (g : A.X.Isotropy x) i, ∀ y ∈ V'.U,
        sb (g • i) (V'.rep.Φ g y) = fibAct (V'.rep.Γ g y) (sb i y) := by
  choose s₀ hs₀ hs₀b using fun i => exists_scPlusSection_extension_of_face hB hpu V.isOpen_U
    (S.isFaceScPlus i) hcl
  exact proposition_14_1_4_hyp (S.restrict hle) s₀
    (fun i => IsScPlusSectionOn.of_isScPlusSection (hs₀ i) V'.isOpen_U)
    (fun i y hy => hs₀b i y hy)

/-- **2021 Proposition 14.1.4, p. 642**, for a good neighbourhood: for tame `X` (with the tame
strong bundle charts and the partitions of unity of `proposition_14_1_4_of_closure`), a good
`V(x)` and a symmetric sc⁺-section structure on `U(x) = V(x) ∩ ∂X`, there is a good
`V'(x) ≤ V(x)` with `cl V'(x) ⊆ V(x)` such that the structure restricted to `U'(x) = V'(x) ∩ ∂X`
extends to sc⁺-sections `s̄ᵢ` on `V'(x)` with the symmetry of Definition 13.2.5. -/
theorem proposition_14_1_4 (hX : A.X.IsTame)
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) {Λ : A.W → ℚ≥0} {x : A.Obj}
    (hx : x ∈ A.X.PObj.boundary) {V : A.X.NatNbhd x} (hV : A.X.IsGoodBoundaryNbhd V)
    (S : BoundarySymmetricStructure A Λ V) :
    ∃ V' : A.X.NatNbhd x, ∃ hle : V'.Le V, A.X.IsGoodBoundaryNbhd V' ∧ closure V'.U ⊆ V.U ∧
      ∃ sb : S.I → A.Obj → A.W, (∀ i, IsScPlusSectionOn A (sb i) V'.U) ∧
        (∀ i, ∀ y ∈ V'.bdry, sb i y = (S.restrict hle).s i y) ∧
        ∀ (g : A.X.Isotropy x) i, ∀ y ∈ V'.U,
          sb (g • i) (V'.rep.Φ g y) = fibAct (V'.rep.Γ g y) (sb i y) := by
  obtain ⟨V', hle, hgood, hcl, -⟩ := A.X.lemma_14_2_1 hX hx V hV
  exact ⟨V', hle, hgood, hcl, proposition_14_1_4_of_closure hB hpu S hle hcl⟩

end SBLocalization

end Polyfold
