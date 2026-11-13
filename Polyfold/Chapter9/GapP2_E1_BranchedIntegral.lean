import Polyfold.Chapter9.GapP2_E1_LocalMeasure
import Polyfold.Chapter9.GapP2_E2MeasureGlue

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5 "Integration and Stokes": **Theorem 9.5.4** (p. 438; 2017: Theorem 9.2),
**Theorem 9.5.5** (p. 438; 2017: Theorem 9.3), **Definition 9.5.6** (p. 439), the identity after
Theorem 9.5.5 and **Proposition 9.5.13 (1)** (p. 446, new in the 2021 edition).  Numbers and pages
are the 2021 text's.

# The branched integral and the effective branched integral

## The text, paraphrased

(Theorems 9.5.4, 9.5.5) For an oriented, tame, compact branched ep⁺-subgroupoid `Θ̂` of
dimension `n` there is a linear map `ω ↦ μ_ω` from the sc-differential `n`-forms to the finite
signed measures on `(S, L(S))`, `S = |supp Θ|`, characterized by
`μ_ω(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` for every oriented local branching structure on a
`U(x)` with the natural `G_x`-action and every measurable `K ⊆ S` in `|U(x)|`; under the local
unique continuation property the same with `♯G_x^eff`, for the `U(x)` with the property of
Definition 7.2.18.  The proof covers `S` by finitely many `|M_{U_p}|`, cuts `K` into pieces
`K_p ⊆ |M_{U_p}|` and sums the local measures; independence of the choices is Lemmas 9.5.7,
9.5.9–9.5.11.  (Definition 9.5.6) `∫_Θ̂ ω = μ_ω(S)`, `∮_Θ̂ ω = μ_ω^eff(S)`.  (Proposition 9.5.13 (1))
For effective `X` the two integrals agree.

## What is formalized

For a `SheetIntegration` `𝓘` (`GapP2_E1_SheetIntegration.lean`) on a class `S` of sheets, and
`Θ` oriented by `T`, compact, with an oriented tame structure with sheets in `S` describing `T` at
every point of `supp Θ`:

* `isMorTangentOn_hat`: the local sc-diffeomorphism `φ̂ = t ∘ (s|U(φ))⁻¹` has the tangent maps of
  the morphisms of its sheet.
* `isMeas_preimage`: the preimage of `K ∈ L(S)` has measurable traces on the sheets (Lemma 9.5.2).
* `exists_slice_pair`, `exists_local_agreement`: near two points `z ∈ U`, `z' ∈ U'` over one point
  of `|X|` the two families of local integrals agree (Lemmas 9.5.9 and 9.5.11 combined), and
  `overlap`: two structures give the same normalized sum on every measurable
  `K ⊆ |M_U| ∩ |M_{U'}|` (the sheets being Lindelöf, countably many such neighbourhoods suffice).
* `localSignedMeasure`: `K ↦ c · ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` as a signed measure on `(S, L(S))`, linear
  in `ω`.
* **`theorem_9_5_4`**, **`theorem_9_5_5`** (existence and uniqueness of `ω ↦ μ_ω`, `ω ↦ μ_ω^eff`),
  `branchedMeasure`, `branchedMeasureEff`, **Definition 9.5.6** `branchedIntegral`,
  `branchedIntegralEff`, `localMeasureEff_eq` (the identity `μ^eff = (♯G_x/♯G_x^eff) μ` after
  Theorem 9.5.5, for the local measures), **`proposition_9_5_13_1`**.

## The choices made

* The gluing of the local measures is agent E2's `existsUnique_linearMap_signedMeasure_of_openCover`
  (`GapP2_E2MeasureGlue.lean`).
* The characterizing property is asked for the oriented tame structures with sheets in `S`
  describing `T̂Θ` (in Theorem 9.5.5: whose `U(x)` has the property of Definition 7.2.18,
  `NaturalRep.HasLUC`); the existence of such a structure at every point of `supp Θ` is the
  hypothesis `hcov` (the text's "oriented, tame, of dimension `n`", with the class `S`; in Theorem
  9.5.5 it follows from the local unique continuation property only after shrinking the `U(x)`).
* Proposition 9.5.13 (2) (the reduced ep-groupoid) is not in this file: it needs the natural
  representations of `X_R` built from those of `X`; the normalizing factors are in
  `MeasureEffective.lean` (`card_effIsotropy_eq_reduced`).  (2026-11-13) It is in
  `GapP2_E4_ReducedRep.lean` and `GapP2_E4_ReducedIntegral.lean` (`proposition_9_5_13_2`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory
open scoped symmDiff

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid Obj Mor} {S : Set (Set Obj)} {G : SheetNullSets S} {Ω : Type*}
  [AddCommGroup Ω] [Module ℝ Ω] (𝓘 : X.SheetIntegration G Ω) {n : ℕ} {Θ : Obj → ℚ}

/-- **`Tψ = Tφ̂` along the sheet of `φ`**: the local sc-diffeomorphism `φ̂ = t ∘ (s|U(φ))⁻¹`
(Definition 7.1.4) has, at every `w ∈ U(x)`, the tangent map of the morphism
`ψ = (s|U(φ))⁻¹(w) : w → φ̂(w)`. -/
theorem isMorTangentOn_hat (φ : Mor) :
    X.IsMorTangentOn (X.isScDiffeoOn_hat φ) (X.sheetAt φ).srcSet := by
  intro w hw
  have hd := (X.sheetAt φ).isScDiffeoOn_src
  have hψS : (X.sheetAt φ).srcInv w ∈ (X.sheetAt φ).carrier := hd.symm.mapsTo hw
  have hsrcψ : X.src ((X.sheetAt φ).srcInv w) = w := hd.right_inv w hw
  refine ⟨(X.sheetAt φ).srcInv w, hsrcψ, rfl, fun α hα => ?_⟩
  have hψ1 : (X.sheetAt φ).srcInv w ∈ X.PMor.levelSet 1 :=
    (X.mem_levelSet_src_iff _ 1).1 (by rw [hsrcψ, ← hα]; exact MPolyfold.levelVal_mem _)
  obtain ⟨v, hv, rfl⟩ := X.exists_tSrc_eq' hψ1 (hα.trans hsrcψ.symm)
  have hvS : X.tBase v ∈ (X.sheetAt φ).carrier := by rw [hv]; exact hψS
  have hαS : X.tSrc v ∈ X.PObj.tangentPreimage (X.sheetAt φ).srcSet := by
    change X.PObj.levelVal 1 (X.PObj.tangentProj (X.tSrc v)) ∈ (X.sheetAt φ).srcSet
    rw [hα]; exact hw
  have key : X.tangentMor (X.tBase v) (X.tSrc v) = X.tTgt v := X.tangentMor_tSrc v
  rw [hv] at key
  rw [key]
  have h1 := MPolyfold.tangentMap_tangentMapOn X.isScSmoothMap_tgt hd.isScSmoothOn_inv hαS
  rw [tangentMapOn_srcInv_tSrc hd hvS] at h1
  change MPolyfold.tangentMap X.isScSmoothMap_tgt v = _
  rw [h1]
  exact MPolyfold.tangentMapOn_congr _ _ hd.isScSmoothOn_inv.isOpen subset_rfl subset_rfl
    (fun _ _ => rfl) hαS

namespace OrientedTameStructure

/-- **The preimage of `K ∈ L(S)` is measurable in the sheets** (Definition 9.5.3 and Lemma
9.5.2): for a structure with sheets in the class `S`, the traces of `π⁻¹(K)` on the sheets are
Borel sets modified by null sets. -/
theorem isMeas_preimage (hTS : X.HasTameSheetsIn S Θ) {x : Obj}
    (C : X.OrientedTameStructure n Θ x) (hS : ∀ i, C.M i ∈ S) {K : Set (X.orbitSupp Θ)}
    (hK : MeasurableSet[X.lebesgueSigma G Θ] K) :
    C.IsMeas G (X.π ⁻¹' (Subtype.val '' K)) := by
  obtain ⟨B, hB, hnull⟩ := (remark_9_5_3 G hTS K).1 hK
  obtain ⟨B₀, hB₀, rfl⟩ : ∃ B₀, MeasurableSet[borel X.OrbitSpace] B₀ ∧ Subtype.val ⁻¹' B₀ = B := by
    have h := hB
    rw [show borel (X.orbitSupp Θ) = (borel X.OrbitSpace).comap Subtype.val from borel_comap] at h
    exact h
  intro i
  have hall := (lemma_9_5_2 G hTS _).2.1 ((lemma_9_5_2 G hTS _).1.1 hnull)
  have hx : x ∈ supp Θ := (C.mem_supp_iff C.mem_U).2 ⟨i, C.mem_M i⟩
  have hn := hall x hx C.toLocalBranchingStructure hS i
  refine ⟨X.π ⁻¹' B₀, X.continuous_π.borel_measurable hB₀, G.isNull_mono hn ?_⟩
  intro y hy
  rw [Set.mem_symmDiff] at hy
  have hyM : y ∈ C.M i := by rcases hy with h | h <;> exact h.1.2
  have hys : X.π y ∈ X.orbitSupp Θ :=
    ⟨y, (C.mem_supp_iff (C.subset_U i hyM)).2 ⟨i, hyM⟩, rfl⟩
  refine ⟨hyM, ⟨⟨X.π y, hys⟩, ?_, rfl⟩⟩
  rw [Set.mem_symmDiff]
  rcases hy with ⟨⟨⟨q, hqK, hq⟩, -⟩, hn'⟩ | ⟨⟨hyB, -⟩, hn'⟩
  · refine Or.inl ⟨?_, fun hc => hn' ⟨hc, hyM⟩⟩
    have : q = ⟨X.π y, hys⟩ := Subtype.ext hq
    rw [← this]; exact hqK
  · exact Or.inr ⟨hyB, fun hc => hn' ⟨⟨_, hc, rfl⟩, hyM⟩⟩

/-! ### The overlap of two structures -/

section Overlap

variable {x x' : Obj} (C : X.OrientedTameStructure n Θ x) (C' : X.OrientedTameStructure n Θ x')

theorem MU_subset_rep (C : X.OrientedTameStructure n Θ x) : C.MU ⊆ C.rep.U := fun z hz => by
  rw [LocalBranchingStructure.MU_eq, C.U_eq] at hz; exact hz.2

/-- **Matching neighbourhoods of two points over one point of `|X|`** (the neighbourhoods `V` of
the proof of Lemma 9.5.9 for both structures, matched by the local sc-diffeomorphism of a morphism
`z → z'`, Lemma 9.5.11). -/
theorem exists_slice_pair (a : C.rep.U) (a' : C'.rep.U)
    (hπ : X.π (a : Obj) = X.π (a' : Obj)) :
    ∃ (φ : Mor) (V : Set Obj), IsOpen V ∧ (a : Obj) ∈ V ∧ V ⊆ C.rep.U ∧
      V ⊆ (X.sheetAt φ).srcSet ∧ X.hat φ '' V ⊆ C'.rep.U ∧
      (∀ g ∈ MulAction.stabilizer (X.Isotropy x) a, C.rep.Φ g '' V = V) ∧
      (∀ g ∉ MulAction.stabilizer (X.Isotropy x) a, Disjoint (C.rep.Φ g '' V) V) ∧
      (∀ g ∈ MulAction.stabilizer (X.Isotropy x') a', C'.rep.Φ g '' (X.hat φ '' V) = X.hat φ '' V) ∧
      (∀ g ∉ MulAction.stabilizer (X.Isotropy x') a',
        Disjoint (C'.rep.Φ g '' (X.hat φ '' V)) (X.hat φ '' V)) ∧
      X.src φ = a ∧ X.tgt φ = a' := by
  obtain ⟨φ, hsrc, htgt⟩ := (X.π_eq_π_iff).1 hπ
  have hf := X.isScDiffeoOn_hat φ
  have hmor := X.isMorTangentOn_hat φ
  have hzS : (a : Obj) ∈ (X.sheetAt φ).srcSet := hsrc ▸ X.src_mem_sheetAt φ
  have hfz : X.hat φ a = a' := by rw [← hsrc, X.hat_src, htgt]
  have hπf : ∀ w ∈ (X.sheetAt φ).srcSet, X.π (X.hat φ w) = X.π w := fun w hw => by
    obtain ⟨ψ, h1, h2, -⟩ := hmor w hw
    exact ((X.π_eq_π_iff).2 ⟨ψ, h1, h2⟩).symm
  obtain ⟨V₀, hV₀o, haV₀, hV₀U, hV₀W, hV₀H, hV₀d⟩ :=
    C.rep.exists_slice a hf.isScSmoothOn.isOpen hzS
  have hfV₀o : IsOpen (X.hat φ '' V₀) := hf.isOpen_image_of_subset hV₀o hV₀W
  obtain ⟨V₀', hV₀'o, ha'V₀', hV₀'U, hV₀'W, hV₀'H, hV₀'d⟩ :=
    C'.rep.exists_slice a' hfV₀o ⟨a, haV₀, hfz⟩
  have hWo : IsOpen (V₀ ∩ ((X.sheetAt φ).srcSet ∩ X.hat φ ⁻¹' V₀')) :=
    hV₀o.inter (hf.isScSmoothOn.continuousOn.isOpen_inter_preimage hf.isScSmoothOn.isOpen hV₀'o)
  obtain ⟨V, hVo, haV, hVU, hVW, hVH, hVd⟩ :=
    C.rep.exists_slice a hWo ⟨haV₀, hzS, by rw [mem_preimage, hfz]; exact ha'V₀'⟩
  have hVS : V ⊆ (X.sheetAt φ).srcSet := fun w hw => (hVW hw).2.1
  have hV'sub : X.hat φ '' V ⊆ V₀' := by
    rintro _ ⟨w, hw, rfl⟩; exact (hVW hw).2.2
  -- `f(V)` is invariant under the stabilizer of `z'`
  have hsub : ∀ g ∈ MulAction.stabilizer (X.Isotropy x') a',
      C'.rep.Φ g '' (X.hat φ '' V) ⊆ X.hat φ '' V := by
    rintro g hg _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hu : C'.rep.Φ g (X.hat φ w) ∈ V₀' := by
      rw [← hV₀'H g hg]; exact ⟨_, hV'sub ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨w₂, hw₂, hw₂u⟩ := hV₀'W hu
    have hπw : X.π w = X.π w₂ := by
      rw [← hπf w₂ (hV₀W hw₂), hw₂u, C'.rep.π_Φ g (hV₀'U (hV'sub ⟨w, hw, rfl⟩)),
        hπf w (hVS hw)]
    obtain ⟨h, hh⟩ := (C.rep.π_eq_π_iff_exists_smul (y := ⟨w, hVU hw⟩)
      (z := ⟨w₂, hV₀U hw₂⟩)).1 hπw
    have hh' : C.rep.Φ h w = w₂ := congrArg Subtype.val hh
    have hhH : h ∈ MulAction.stabilizer (X.Isotropy x) a := by
      by_contra hn
      exact Set.disjoint_left.1 (hV₀d h hn) ⟨w, (hVW hw).1, hh'⟩ hw₂
    have hw₂V : w₂ ∈ V := by rw [← hVH h hhH]; exact ⟨w, hw, hh'⟩
    exact ⟨w₂, hw₂V, hw₂u⟩
  refine ⟨φ, V, hVo, haV, hVU, hVS, hV'sub.trans hV₀'U, hVH, hVd, fun g hg => ?_,
    fun g hg => (hV₀'d g hg).mono (image_mono hV'sub) hV'sub, hsrc, htgt⟩
  refine Subset.antisymm (hsub g hg) fun v hv => ?_
  have hvU : v ∈ C'.rep.U := hV₀'U (hV'sub hv)
  exact ⟨C'.rep.Φ g⁻¹ v, hsub g⁻¹ (inv_mem hg) ⟨v, hv, rfl⟩, C'.rep.Φ_Φ_inv g hvU⟩

/-- **Local agreement (Lemmas 9.5.9 and 9.5.11 combined)**: for `z ∈ M_U` and `z' ∈ M_{U'}` over
one point of `|X|`, with stabilizers `H`, `H'`, there is a neighbourhood `V` of `z` such that for
all measurable `K ⊆ |M_U ∩ V|` the sums of the two structures are `♯(G_x/H) · s` and
`♯(G_{x'}/H') · s` for one number `s`. -/
theorem exists_local_agreement (hΘ : X.IsBranchedEpSubgroupoid Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T) (hS : ∀ i, C.M i ∈ S)
    (hS' : ∀ i, C'.M i ∈ S) (hCT : C.Represents T) (hC'T : C'.Represents T)
    (a : C.rep.U) (a' : C'.rep.U) (hπ : X.π (a : Obj) = X.π (a' : Obj)) :
    ∃ V : Set Obj, IsOpen V ∧ (a : Obj) ∈ V ∧ V ⊆ C.U ∧ ∀ (ω : Ω) (K : Set X.OrbitSpace),
      K ⊆ X.π '' (C.MU ∩ V) → C.IsMeas G (X.π ⁻¹' K) → ∃ s : ℝ,
        C.sheetSum 𝓘 ω (X.π ⁻¹' K) =
          (Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) : ℝ) * s ∧
        C'.sheetSum 𝓘 ω (X.π ⁻¹' K) =
          (Nat.card (X.Isotropy x' ⧸ MulAction.stabilizer (X.Isotropy x') a') : ℝ) * s := by
  obtain ⟨φ, V, hVo, haV, hVU, hVS, hV'U, hVH, hVd, hV'H, hV'd, -, -⟩ :=
    C.exists_slice_pair C' a a' hπ
  have hf := X.isScDiffeoOn_hat φ
  have hmor := X.isMorTangentOn_hat φ
  refine ⟨V, hVo, haV, C.U_eq ▸ hVU, fun ω K hK hKm => ?_⟩
  have hrel : ∀ w ∈ (X.sheetAt φ).srcSet, Θ (X.hat φ w) = Θ w ∧ X.π (X.hat φ w) = X.π w :=
    fun w hw => by
      obtain ⟨ψ, h1, h2, -⟩ := hmor w hw
      have h3 := hΘ.isFunctorial ψ
      rw [h1, h2] at h3
      exact ⟨h3.symm, ((X.π_eq_π_iff).2 ⟨ψ, h1, h2⟩).symm⟩
  set Kt : Set Obj := C.MU ∩ V ∩ X.π ⁻¹' K with hKt
  have hKtm : C.IsMeas G Kt := fun i => by
    have h1 : G.IsMeasIn (C.M i) (V ∩ X.π ⁻¹' K) :=
      (SheetNullSets.isMeasIn_of_borel (MeasurableSpace.measurableSet_generateFrom hVo)).inter
        (hKm i)
    refine h1.congr_inter ?_
    rw [hKt, inter_assoc C.MU V, C.MU_inter_inter]
  have hKtU : Kt ⊆ C.MU ∩ (X.sheetAt φ).srcSet := fun w hw => ⟨hw.1.1, hVS hw.1.2⟩
  -- the image of `K̃` is the corresponding set of `C'`
  have himg : X.hat φ '' Kt = C'.MU ∩ X.hat φ '' V ∩ X.π ⁻¹' K := by
    ext u
    constructor
    · rintro ⟨w, ⟨⟨hwM, hwV⟩, hwK⟩, rfl⟩
      obtain ⟨h1, h2⟩ := hrel w (hVS hwV)
      rw [LocalBranchingStructure.MU_eq] at hwM ⊢
      refine ⟨⟨⟨?_, C'.U_eq ▸ hV'U ⟨w, hwV, rfl⟩⟩, ⟨w, hwV, rfl⟩⟩, ?_⟩
      · change 0 < Θ (X.hat φ w); rw [h1]; exact hwM.1
      · rw [mem_preimage, h2]; exact hwK
    · rintro ⟨⟨huM, ⟨w, hwV, rfl⟩⟩, huK⟩
      obtain ⟨h1, h2⟩ := hrel w (hVS hwV)
      rw [LocalBranchingStructure.MU_eq] at huM
      have hwM : w ∈ C.MU := by
        rw [LocalBranchingStructure.MU_eq]
        exact ⟨by change 0 < Θ w; rw [← h1]; exact huM.1, C.U_eq ▸ hVU hwV⟩
      exact ⟨w, ⟨⟨hwM, hwV⟩, by rw [mem_preimage, ← h2]; exact huK⟩, rfl⟩
  have hK' : K ⊆ X.π '' (C'.MU ∩ X.hat φ '' V) := by
    intro q hq
    obtain ⟨w, ⟨hwM, hwV⟩, rfl⟩ := hK hq
    have hmem : X.hat φ w ∈ X.hat φ '' Kt := ⟨w, ⟨⟨hwM, hwV⟩, hq⟩, rfl⟩
    rw [himg] at hmem
    exact ⟨_, hmem.1, (hrel w (hVS hwV)).2⟩
  have hKt'm : C'.IsMeas G (C'.MU ∩ X.hat φ '' V ∩ X.π ⁻¹' K) := by
    rw [← himg]
    exact hKtm.image 𝓘 C C' hS hS' hf hmor hKtU
  have e1 := C.sheetSum_preimage_eq_card_mul_slice 𝓘 hΘ hT hS hCT a hVU hVH hVd ω hK hKtm
  have e2 := C'.sheetSum_preimage_eq_card_mul_slice 𝓘 hΘ hT hS' hC'T a' hV'U hV'H hV'd ω hK'
    hKt'm
  have e3 : C'.sheetSum 𝓘 ω (C'.MU ∩ X.hat φ '' V ∩ X.π ⁻¹' K) = C.sheetSum 𝓘 ω Kt := by
    rw [← himg]
    exact C.sheetSum_image 𝓘 C' hΘ hT hS hS' hCT hC'T hf hmor ω hKtU hKtm
      (by rw [himg]; exact fun u hu => hu.1.1)
  exact ⟨C.sheetSum 𝓘 ω Kt, e1, by rw [e2, e3]⟩

/-- **The local measures agree on overlaps** (the step "this definition does not depend on the
choices involved, due to Lemmata 9.5.7, 9.5.10, and 9.5.11" of the proof of Theorems 9.5.4 and
9.5.5, 2021 p. 446): let `c` be a normalizing factor invariant under morphisms with
`c(x) · ♯(G_x/H_y) = c(y)` on `U(x)` and `U(x')` (`c = 1/♯G` or `c = 1/♯G^eff`).  Then for every
measurable `K ⊆ |M_U| ∩ |M_{U'}|`, `c(x) ∑ σᵢ ∫_{Kᵢ} ω|Mᵢ = c(x') ∑ σ'ⱼ ∫_{K'ⱼ} ω|M'ⱼ`. -/
theorem overlap (hΘ : X.IsBranchedEpSubgroupoid Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T) (hS : ∀ i, C.M i ∈ S)
    (hS' : ∀ i, C'.M i ∈ S) (hCT : C.Represents T) (hC'T : C'.Represents T) (c : Obj → ℝ)
    (hc : ∀ φ : Mor, c (X.src φ) = c (X.tgt φ))
    (hcx : ∀ a : C.rep.U, c x *
      (Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) : ℝ) = c a)
    (hcx' : ∀ a : C'.rep.U, c x' *
      (Nat.card (X.Isotropy x' ⧸ MulAction.stabilizer (X.Isotropy x') a) : ℝ) = c a)
    (ω : Ω) {K : Set X.OrbitSpace} (hK : K ⊆ X.π '' C.MU) (hK' : K ⊆ X.π '' C'.MU)
    (hKm : C.IsMeas G (X.π ⁻¹' K)) (hKm' : C'.IsMeas G (X.π ⁻¹' K)) :
    c x * C.sheetSum 𝓘 ω (X.π ⁻¹' K) = c x' * C'.sheetSum 𝓘 ω (X.π ⁻¹' K) := by
  classical
  -- the local statement
  have hloc : ∀ z ∈ C.MU ∩ X.π ⁻¹' K, ∃ V : Set Obj, IsOpen V ∧ z ∈ V ∧ V ⊆ C.U ∧
      ∀ K₁ : Set X.OrbitSpace, K₁ ⊆ X.π '' (C.MU ∩ V) → C.IsMeas G (X.π ⁻¹' K₁) →
        c x * C.sheetSum 𝓘 ω (X.π ⁻¹' K₁) = c x' * C'.sheetSum 𝓘 ω (X.π ⁻¹' K₁) := by
    intro z hz
    obtain ⟨z', hz', hzz'⟩ := hK' hz.2
    obtain ⟨V, hVo, hzV, hVsub, hV⟩ := C.exists_local_agreement 𝓘 C' hΘ hT hS hS' hCT hC'T
      ⟨z, C.MU_subset_rep hz.1⟩ ⟨z', C'.MU_subset_rep hz'⟩ hzz'.symm
    refine ⟨V, hVo, hzV, hVsub, fun K₁ hK₁ hK₁m => ?_⟩
    obtain ⟨s, e1, e2⟩ := hV ω K₁ hK₁ hK₁m
    obtain ⟨φ, hφs, hφt⟩ := (X.π_eq_π_iff).1 hzz'.symm
    have hcz : c z = c z' := by have := hc φ; rwa [hφs, hφt] at this
    rw [e1, e2, ← mul_assoc, ← mul_assoc, hcx ⟨z, C.MU_subset_rep hz.1⟩,
      hcx' ⟨z', C'.MU_subset_rep hz'⟩]
    exact congrArg (· * s) hcz
  rcases (C.MU ∩ X.π ⁻¹' K).eq_empty_or_nonempty with hempty | hne
  · -- `K = ∅`
    have hK0 : K = ∅ := eq_empty_of_forall_notMem fun q hq => by
      obtain ⟨w, hw, rfl⟩ := hK hq
      exact (hempty ▸ (⟨hw, hq⟩ : w ∈ C.MU ∩ X.π ⁻¹' K) : w ∈ (∅ : Set Obj))
    rw [hK0, preimage_empty, C.sheetSum_empty 𝓘 hS, C'.sheetSum_empty 𝓘 hS', mul_zero, mul_zero]
  -- countably many neighbourhoods cover the preimage of `K` in `M_U`
  set At : Set Obj := C.MU ∩ X.π ⁻¹' K with hAt
  have : Nonempty At := hne.to_subtype
  choose! V hVo hzV hVsub hVP using hloc
  have hcount : ∀ i : C.ι, ∃ r : Set At, r.Countable ∧
      At ∩ C.M i ⊆ ⋃ z ∈ r, V (z : Obj) := by
    intro i
    have := 𝓘.lindelof _ (hS i)
    have hL : IsLindelof (Subtype.val ⁻¹' At : Set (C.M i)) :=
      HereditarilyLindelofSpace.isLindelof _
    obtain ⟨r, hr, hsub⟩ := hL.elim_countable_subcover
      (fun z : At => (Subtype.val ⁻¹' V (z : Obj) : Set (C.M i)))
      (fun z => (hVo z z.2).preimage continuous_subtype_val)
      (fun y hy => mem_iUnion.2 ⟨⟨(y : Obj), hy⟩, hzV _ hy⟩)
    refine ⟨r, hr, fun y hy => ?_⟩
    have := hsub (show (⟨y, hy.2⟩ : C.M i) ∈ (Subtype.val ⁻¹' At : Set (C.M i)) from hy.1)
    simpa only [mem_iUnion, mem_preimage] using this
  choose r hr hrsub using hcount
  have hrc : (⋃ i, r i).Countable := countable_iUnion hr
  obtain ⟨e, he⟩ := (Set.countable_iff_exists_subset_range.1 hrc)
  have hcovAt : At ⊆ ⋃ k, V (e k : Obj) := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.1 hy.1
    obtain ⟨z, hz⟩ := mem_iUnion.1 (hrsub i ⟨hy, hi⟩)
    obtain ⟨hzr, hyV⟩ := mem_iUnion.1 hz
    obtain ⟨k, rfl⟩ := he (mem_iUnion.2 ⟨i, hzr⟩)
    exact mem_iUnion.2 ⟨k, hyV⟩
  -- the pieces of `K`
  set Q : ℕ → Set X.OrbitSpace := fun k => X.π '' V (e k : Obj) with hQ
  have hQo : ∀ k, IsOpen (Q k) := fun k => X.proposition_7_1_8 _ (hVo _ (e k).2)
  set Kp : ℕ → Set X.OrbitSpace := fun k => (K ∩ Q k) \ ⋃ l, ⋃ (_ : l < k), Q l with hKp
  have hKpd : Pairwise (Function.onFun Disjoint Kp) := by
    intro k l hkl
    rcases lt_or_gt_of_ne hkl with h | h
    · exact disjoint_left.2 fun q hq hq' =>
        hq'.2 (mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨h, hq.1.2⟩⟩)
    · exact disjoint_left.2 fun q hq hq' =>
        hq.2 (mem_iUnion.2 ⟨l, mem_iUnion.2 ⟨h, hq'.1.2⟩⟩)
  have hKpU : ⋃ k, Kp k = K := by
    refine Subset.antisymm (iUnion_subset fun k q hq => hq.1.1) fun q hq => ?_
    obtain ⟨w, hw, rfl⟩ := hK hq
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hcovAt ⟨hw, hq⟩)
    have hex : ∃ k, X.π w ∈ Q k := ⟨k, w, hk, rfl⟩
    refine mem_iUnion.2 ⟨Nat.find hex, ⟨hq, Nat.find_spec hex⟩, fun hc => ?_⟩
    obtain ⟨l, hl⟩ := mem_iUnion.1 hc
    obtain ⟨hlt, hl'⟩ := mem_iUnion.1 hl
    exact Nat.find_min hex hlt hl'
  have hborel : ∀ (N : Set Obj) (k : ℕ),
      G.IsMeasIn N (X.π ⁻¹' ((Q k) \ ⋃ l, ⋃ (_ : l < k), Q l)) := fun N k =>
    SheetNullSets.isMeasIn_of_borel (X.continuous_π.borel_measurable
      (MeasurableSet.diff (MeasurableSpace.measurableSet_generateFrom (hQo k))
        (MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun _ =>
          MeasurableSpace.measurableSet_generateFrom (hQo l))))
  have hpre : ∀ k, X.π ⁻¹' Kp k = X.π ⁻¹' K ∩ X.π ⁻¹' ((Q k) \ ⋃ l, ⋃ (_ : l < k), Q l) := by
    intro k
    rw [← preimage_inter]
    congr 1
    ext q
    simp only [hKp, Set.mem_sdiff, mem_inter_iff]
    tauto
  have hKpm : ∀ k, C.IsMeas G (X.π ⁻¹' Kp k) := fun k i => by
    rw [hpre k]; exact (hKm i).inter (hborel _ k)
  have hKpm' : ∀ k, C'.IsMeas G (X.π ⁻¹' Kp k) := fun k i => by
    rw [hpre k]; exact (hKm' i).inter (hborel _ k)
  have hpd : Pairwise (Function.onFun Disjoint fun k => X.π ⁻¹' Kp k) := fun k l hkl =>
    (hKpd hkl).preimage _
  have hpU : ⋃ k, X.π ⁻¹' Kp k = X.π ⁻¹' K := by rw [← preimage_iUnion, hKpU]
  have h1 := (C.sheetSum_hasSum 𝓘 hS ω _ hKpm hpd).mul_left (c x)
  have h2 := (C'.sheetSum_hasSum 𝓘 hS' ω _ hKpm' hpd).mul_left (c x')
  rw [hpU] at h1 h2
  have hterm : ∀ k, c x * C.sheetSum 𝓘 ω (X.π ⁻¹' Kp k) =
      c x' * C'.sheetSum 𝓘 ω (X.π ⁻¹' Kp k) := fun k => by
    refine hVP _ (e k).2 (Kp k) (fun q hq => ?_) (hKpm k)
    obtain ⟨v, hv, rfl⟩ := hq.1.2
    obtain ⟨w, hw, hwq⟩ := hK hq.1.1
    have hvs : v ∈ supp Θ := by
      have hws : w ∈ supp Θ := by
        rw [LocalBranchingStructure.MU_eq] at hw; exact hw.1
      obtain ⟨ψ, h1, h2⟩ := (X.π_eq_π_iff).1 hwq
      have h3 := hΘ.isFunctorial ψ
      rw [h1, h2] at h3
      change 0 < Θ v; rw [← h3]; exact hws
    have hvU : v ∈ C.U := hVsub _ (e k).2 hv
    rw [LocalBranchingStructure.MU_eq]
    exact ⟨v, ⟨⟨hvs, hvU⟩, hv⟩, rfl⟩
  exact h1.unique (by simpa only [hterm] using h2)

end Overlap

/-! ### The local measures as signed measures on `(S, L(S))` -/

section LocalSigned

open scoped Classical

variable {x : Obj} (C : X.OrientedTameStructure n Θ x)

/-- If `K ⊆ S` lies in `|U(x)|`, it lies in `|M_U|`. -/
theorem image_val_subset_MU (hΘ : X.IsFunctorial Θ) {K : Set (X.orbitSupp Θ)}
    (h : Subtype.val '' K ⊆ X.π '' C.U) : Subtype.val '' K ⊆ X.π '' C.MU := by
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨v, hvU, hv⟩ := h ⟨q, hq, rfl⟩
  have hvs : v ∈ supp Θ := by
    rw [← preimage_π_orbitSupp hΘ, mem_preimage, hv]; exact q.2
  exact ⟨v, by rw [LocalBranchingStructure.MU_eq]; exact ⟨hvs, hvU⟩, hv⟩

/-- **(9.21) as a signed measure**: `K ↦ c · ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` on `(S, L(S))`, linear in
`ω` (`c = 1/♯G_x` for `μ_ω^{U(x)}`, `c = 1/♯G_x^eff` for `μ_ω^{eff,U(x)}`). -/
def localSignedMeasure (hTS : X.HasTameSheetsIn S Θ) (hS : ∀ i, C.M i ∈ S) (c : ℝ) :
    Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma G Θ) :=
  letI : MeasurableSpace (X.orbitSupp Θ) := X.lebesgueSigma G Θ
  { toFun := fun ω =>
      { measureOf' := fun K =>
          if MeasurableSet K then c * C.sheetSum 𝓘 ω (X.π ⁻¹' (Subtype.val '' K)) else 0
        empty' := by
          rw [if_pos MeasurableSet.empty, image_empty, preimage_empty, C.sheetSum_empty 𝓘 hS,
            mul_zero]
        not_measurable' := fun K hK => if_neg hK
        m_iUnion' := fun A hA hd => by
          rw [if_pos (MeasurableSet.iUnion hA)]
          simp only [if_pos (hA _)]
          rw [image_iUnion, preimage_iUnion]
          exact (C.sheetSum_hasSum 𝓘 hS ω _ (fun k => C.isMeas_preimage hTS hS (hA k))
            fun k l hkl => ((Set.disjoint_image_iff Subtype.val_injective).2
              (hd hkl)).preimage _).mul_left c }
    map_add' := fun ω τ => VectorMeasure.ext fun K hK => by
      have e1 : (if MeasurableSet K then
          c * C.sheetSum 𝓘 (ω + τ) (X.π ⁻¹' (Subtype.val '' K)) else (0 : ℝ)) =
          (if MeasurableSet K then c * C.sheetSum 𝓘 ω (X.π ⁻¹' (Subtype.val '' K)) else (0 : ℝ)) +
          (if MeasurableSet K then c * C.sheetSum 𝓘 τ (X.π ⁻¹' (Subtype.val '' K)) else (0 : ℝ)) := by
        rw [if_pos hK, if_pos hK, if_pos hK, C.sheetSum_add, mul_add]
      exact e1
    map_smul' := fun r ω => VectorMeasure.ext fun K hK => by
      have e1 : (if MeasurableSet K then
          c * C.sheetSum 𝓘 (r • ω) (X.π ⁻¹' (Subtype.val '' K)) else (0 : ℝ)) =
          r • (if MeasurableSet K then
            c * C.sheetSum 𝓘 ω (X.π ⁻¹' (Subtype.val '' K)) else (0 : ℝ)) := by
        rw [if_pos hK, if_pos hK, C.sheetSum_smul, smul_eq_mul]
        ring
      exact e1 }

theorem localSignedMeasure_apply (hTS : X.HasTameSheetsIn S Θ) (hS : ∀ i, C.M i ∈ S) (c : ℝ)
    (ω : Ω) {K : Set (X.orbitSupp Θ)} (hK : MeasurableSet[X.lebesgueSigma G Θ] K) :
    C.localSignedMeasure 𝓘 hTS hS c ω K = c * C.sheetSum 𝓘 ω (X.π ⁻¹' (Subtype.val '' K)) :=
  if_pos hK

end LocalSigned

end OrientedTameStructure

/-! ### Theorems 9.5.4 and 9.5.5 -/

section Global

open OrientedTameStructure

/-- **Theorems 9.5.4 and 9.5.5 for a normalizing factor `c`**: let `Θ` be compact and oriented
by `T`, `c : X → ℝ` invariant under morphisms, and `Good` a class of oriented tame structures with
sheets in `S` describing `T`, with `c(x) · ♯(G_x/H_y) = c(y)` on their domains, one at every point
of `supp Θ`.  Then there is exactly one linear map `ω ↦ μ_ω` into the signed measures on
`(S, L(S))` with `μ_ω(K) = c(x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` for every structure of the class and every
measurable `K ⊆ S` in `|U(x)|`. -/
theorem existsUnique_branchedMeasure (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsOrientation Θ T) (c : Obj → ℝ) (hc : ∀ φ : Mor, c (X.src φ) = c (X.tgt φ))
    (Good : ∀ x, X.OrientedTameStructure n Θ x → Prop)
    (hGS : ∀ x C, Good x C → ∀ i, C.M i ∈ S) (hGT : ∀ x C, Good x C → C.Represents T)
    (hGc : ∀ x C, Good x C → ∀ a : C.rep.U, c x *
      (Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) : ℝ) = c a)
    (hcov : ∀ x ∈ supp Θ, ∃ C, Good x C) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma G Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x), Good x C →
        ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma G Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = c x * C.sheetSum 𝓘 ω (X.π ⁻¹' (Subtype.val '' K)) := by
  let _ : MeasurableSpace (X.orbitSupp Θ) := X.lebesgueSigma G Θ
  have : CompactSpace (X.orbitSupp Θ) := isCompact_iff_compactSpace.1 hcpt
  have hTS : X.HasTameSheetsIn S Θ := fun x hx => by
    obtain ⟨C, hC⟩ := hcov x hx
    exact ⟨C.toTameBranchingStructure, hGS x C hC⟩
  let J := {j : Σ x, X.OrientedTameStructure n Θ x // Good j.1 j.2}
  let O : J → Set (X.orbitSupp Θ) := fun j => Subtype.val ⁻¹' (X.π '' j.1.2.U)
  have hO : ∀ j, IsOpen (O j) := fun j =>
    (X.proposition_7_1_8 _ j.1.2.isOpen_U).preimage continuous_subtype_val
  have hcovO : ⋃ j, O j = univ := eq_univ_of_forall fun q => by
    obtain ⟨y, hy, hyq⟩ := q.2
    obtain ⟨C, hC⟩ := hcov y hy
    exact mem_iUnion.2 ⟨⟨⟨y, C⟩, hC⟩, y, C.mem_U, hyq⟩
  let μ : J → Ω →ₗ[ℝ] SignedMeasure (X.orbitSupp Θ) := fun j =>
    j.1.2.localSignedMeasure 𝓘 hTS (hGS _ _ j.2) (c j.1.1)
  have hsub : ∀ (j : J) {K : Set (X.orbitSupp Θ)}, K ⊆ O j →
      Subtype.val '' K ⊆ X.π '' j.1.2.U := by
    rintro j K hK _ ⟨q, hq, rfl⟩
    exact hK hq
  have hcompat : ∀ j l ω K, MeasurableSet K → K ⊆ O j ∩ O l → μ j ω K = μ l ω K := by
    intro j l ω K hK hKO
    change j.1.2.localSignedMeasure 𝓘 hTS (hGS _ _ j.2) (c j.1.1) ω K =
      l.1.2.localSignedMeasure 𝓘 hTS (hGS _ _ l.2) (c l.1.1) ω K
    rw [localSignedMeasure_apply _ _ _ _ _ _ hK, localSignedMeasure_apply _ _ _ _ _ _ hK]
    exact j.1.2.overlap 𝓘 l.1.2 hΘ hT (hGS _ _ j.2) (hGS _ _ l.2) (hGT _ _ j.2) (hGT _ _ l.2)
      c hc (hGc _ _ j.2) (hGc _ _ l.2) ω
      (j.1.2.image_val_subset_MU hΘ.isFunctorial (hsub j (hKO.trans inter_subset_left)))
      (l.1.2.image_val_subset_MU hΘ.isFunctorial (hsub l (hKO.trans inter_subset_right)))
      (j.1.2.isMeas_preimage hTS (hGS _ _ j.2) hK) (l.1.2.isMeas_preimage hTS (hGS _ _ l.2) hK)
  obtain ⟨Φ, hΦ, huniq⟩ := existsUnique_linearMap_signedMeasure_of_openCover
    (borel_le_borelNullSigma _) O hO hcovO μ hcompat
  refine ⟨Φ, fun ω x C hC K hK hKU => ?_, fun Ψ hΨ => huniq Ψ fun j ω K hK hKO => ?_⟩
  · rw [hΦ ⟨⟨x, C⟩, hC⟩ ω K hK fun q hq => hKU ⟨q, hq, rfl⟩]
    exact localSignedMeasure_apply _ _ _ _ _ _ hK
  · rw [hΨ ω _ _ j.2 K hK (hsub j hKO)]
    exact (localSignedMeasure_apply _ _ _ _ _ _ hK).symm

theorem inv_mul_eq_inv_of_mul_eq {a b c : ℕ} (h : a * b = c) (hb : 0 < b) (hc : 0 < c) :
    (c : ℝ)⁻¹ * (a : ℝ) = (b : ℝ)⁻¹ := by
  have := OrientedTameStructure.inv_mul_mul_eq h hb hc 1
  rwa [mul_one, mul_one] at this

/-- **Theorem 9.5.4, 2021 p. 438 (2017: Theorem 9.2)**: let `Θ̂ = (Θ, T̂Θ)` be an oriented,
tame, compact branched ep⁺-subgroupoid of dimension `n`, with an oriented tame structure with
sheets in `S` describing `T̂Θ` at every point of `supp Θ`.  There is a linear map
`Φ : ω ↦ μ_ω` from the forms to the finite signed measures on `(S, L(S))`, `S = |supp Θ|`,
characterized uniquely by: for every `x`, every oriented tame local branching structure
`(Mᵢ, oᵢ)`, `(σᵢ)` on `U(x)` (with the natural `G_x`-action) with sheets in `S` describing `T̂Θ`,
and every measurable `K ⊆ S` contained in `|U(x)|`,
`μ_ω(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)`. -/
theorem theorem_9_5_4 (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma G Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x),
        ((∀ i, C.M i ∈ S) ∧ C.Represents T) →
        ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma G Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U → Φ ω K = C.localMeasure 𝓘 ω (Subtype.val '' K) :=
  existsUnique_branchedMeasure 𝓘 hΘ hcpt hT (fun x => (Nat.card (X.Isotropy x) : ℝ)⁻¹)
    (fun φ => by rw [card_isotropy_eq_of_mor φ rfl rfl])
    (fun x C => (∀ i, C.M i ∈ S) ∧ C.Represents T) (fun _ _ h => h.1) (fun _ _ h => h.2)
    (fun x C _ a => by
      have : Finite (X.Isotropy x) := NatRepConstruction.finite_isotropy X x
      have : Finite (X.Isotropy (a : Obj)) := NatRepConstruction.finite_isotropy X _
      exact inv_mul_eq_inv_of_mul_eq (C.rep.card_quotient_stabilizer_mul_card_isotropy a)
        Nat.card_pos Nat.card_pos)
    hcov

theorem finite_effIsotropy (z : Obj) : Finite (X.EffIsotropy z) :=
  haveI : Finite (X.Isotropy z) := NatRepConstruction.finite_isotropy X z
  Finite.of_equiv _ (X.effIsotropyEquiv z).toEquiv.symm

/-- **Theorem 9.5.5, 2021 p. 438 (2017: Theorem 9.3)**: in the situation of Theorem 9.5.4, if
every point of `supp Θ` has such a structure whose `U(x)` has the property of Definition 7.2.18
(the local unique continuation property), there is a linear map `ω ↦ μ_ω^eff` into the signed
measures on `(S, L(S))` characterized uniquely by
`μ_ω^eff(K) = (1/♯G_x^eff) ∑ σᵢ ∫_{Kᵢ} ω|(Mᵢ, oᵢ)` for these structures and the measurable
`K ⊆ S` contained in `|U(x)|`. -/
theorem theorem_9_5_5 (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T ∧ C.rep.HasLUC) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma G Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure n Θ x),
        ((∀ i, C.M i ∈ S) ∧ C.Represents T ∧ C.rep.HasLUC) →
        ∀ K : Set (X.orbitSupp Θ), MeasurableSet[X.lebesgueSigma G Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U → Φ ω K = C.localMeasureEff 𝓘 ω (Subtype.val '' K) :=
  existsUnique_branchedMeasure 𝓘 hΘ hcpt hT (fun x => (Nat.card (X.EffIsotropy x) : ℝ)⁻¹)
    (fun φ => by rw [card_effIsotropy_eq_of_mor φ rfl rfl])
    (fun x C => (∀ i, C.M i ∈ S) ∧ C.Represents T ∧ C.rep.HasLUC) (fun _ _ h => h.1)
    (fun _ _ h => h.2.1)
    (fun x C h a => by
      have := finite_effIsotropy (X := X) x
      have := finite_effIsotropy (X := X) (a : Obj)
      exact inv_mul_eq_inv_of_mul_eq
        (C.rep.card_quotient_stabilizer_mul_card_effIsotropy h.2.2 a) Nat.card_pos Nat.card_pos)
    hcov

/-- **The measure `μ_ω^Θ̂` of Theorem 9.5.4.** -/
def branchedMeasure (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T) :
    Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma G Θ) :=
  (theorem_9_5_4 𝓘 hΘ hcpt hT hcov).exists.choose

/-- **The measure `μ_ω^{Θ̂,eff}` of Theorem 9.5.5.** -/
def branchedMeasureEff (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T ∧ C.rep.HasLUC) :
    Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ) (X.lebesgueSigma G Θ) :=
  (theorem_9_5_5 𝓘 hΘ hcpt hT hcov).exists.choose

theorem branchedMeasure_apply (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T) (ω : Ω) {x : Obj}
    (C : X.OrientedTameStructure n Θ x) (hS : ∀ i, C.M i ∈ S) (hCT : C.Represents T)
    {K : Set (X.orbitSupp Θ)} (hK : MeasurableSet[X.lebesgueSigma G Θ] K)
    (hKU : Subtype.val '' K ⊆ X.π '' C.U) :
    branchedMeasure 𝓘 hΘ hcpt hT hcov ω K = C.localMeasure 𝓘 ω (Subtype.val '' K) :=
  (theorem_9_5_4 𝓘 hΘ hcpt hT hcov).exists.choose_spec ω x C ⟨hS, hCT⟩ K hK hKU

theorem branchedMeasureEff_apply (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T ∧ C.rep.HasLUC) (ω : Ω) {x : Obj}
    (C : X.OrientedTameStructure n Θ x) (hS : ∀ i, C.M i ∈ S) (hCT : C.Represents T)
    (hL : C.rep.HasLUC) {K : Set (X.orbitSupp Θ)} (hK : MeasurableSet[X.lebesgueSigma G Θ] K)
    (hKU : Subtype.val '' K ⊆ X.π '' C.U) :
    branchedMeasureEff 𝓘 hΘ hcpt hT hcov ω K = C.localMeasureEff 𝓘 ω (Subtype.val '' K) :=
  (theorem_9_5_5 𝓘 hΘ hcpt hT hcov).exists.choose_spec ω x C ⟨hS, hCT, hL⟩ K hK hKU

/-- **Definition 9.5.6 (1), 2021 p. 439: the branched integral** `∫_Θ̂ ω = μ_ω^Θ̂(|supp Θ|)`. -/
def branchedIntegral (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T) (ω : Ω) : ℝ :=
  branchedMeasure 𝓘 hΘ hcpt hT hcov ω univ

/-- **Definition 9.5.6 (2), 2021 p. 439: the effective branched integral**
`∮_Θ̂ ω = μ_ω^{Θ̂,eff}(|supp Θ|)`. -/
def branchedIntegralEff (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T ∧ C.rep.HasLUC) (ω : Ω) : ℝ :=
  branchedMeasureEff 𝓘 hΘ hcpt hT hcov ω univ

/-- **The identity after Theorem 9.5.5, 2021 p. 439**:
`μ_ω^{eff,U(x)}(K) = (♯G_x/♯G_x^eff) · μ_ω^{U(x)}(K)`. -/
theorem OrientedTameStructure.localMeasureEff_eq {x : Obj} (C : X.OrientedTameStructure n Θ x)
    (ω : Ω) (K : Set X.OrbitSpace) :
    C.localMeasureEff 𝓘 ω K =
      (Nat.card (X.Isotropy x) : ℝ) / (Nat.card (X.EffIsotropy x) : ℝ) *
        C.localMeasure 𝓘 ω K := by
  have : Finite (X.Isotropy x) := NatRepConstruction.finite_isotropy X x
  have h : (Nat.card (X.Isotropy x) : ℝ) ≠ 0 := by exact_mod_cast (Nat.card_pos).ne'
  rw [localMeasureEff, localMeasure]
  field_simp

/-- **Proposition 9.5.13 (1), 2021 p. 446 (new in the 2021 edition)**: if `X` is effective, the
measures of Theorems 9.5.4 and 9.5.5 coincide, and so do the branched integral and the effective
branched integral: `∫_Θ̂ ω = ∮_Θ̂ ω` (`G_x^eff = G_x`, so the normalizing factors agree). -/
theorem proposition_9_5_13_1 (hX : X.IsEffective) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T)
    (hcovL : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T ∧ C.rep.HasLUC) :
    branchedMeasure 𝓘 hΘ hcpt hT hcov = branchedMeasureEff 𝓘 hΘ hcpt hT hcovL ∧
      ∀ ω : Ω, branchedIntegral 𝓘 hΘ hcpt hT hcov ω = branchedIntegralEff 𝓘 hΘ hcpt hT hcovL ω := by
  have h : branchedMeasure 𝓘 hΘ hcpt hT hcov = branchedMeasureEff 𝓘 hΘ hcpt hT hcovL := by
    refine (theorem_9_5_5 𝓘 hΘ hcpt hT hcovL).unique (fun ω x C hC K hK hKU => ?_)
      (fun ω x C hC K hK hKU => branchedMeasureEff_apply 𝓘 hΘ hcpt hT hcovL ω C hC.1 hC.2.1
        hC.2.2 hK hKU)
    rw [branchedMeasure_apply 𝓘 hΘ hcpt hT hcov ω C hC.1 hC.2.1 hK hKU, localMeasure,
      localMeasureEff, card_effIsotropy_eq_of_isEffective hX x]
  exact ⟨h, fun ω => by rw [branchedIntegral, branchedIntegralEff, h]⟩

/-- **Locality in the form**: `μ_ω^Θ̂` only depends on the integrals of `ω` over the sheets of
the class `S`; if they all vanish, `μ_ω^Θ̂ = 0`. -/
theorem branchedMeasure_eq_zero (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T) (ω : Ω)
    (hω : ∀ N ∈ S, ∀ (g : Obj → X.PObj.OrTangent) (A : Set Obj), 𝓘.integ ω N g A = 0) :
    branchedMeasure 𝓘 hΘ hcpt hT hcov ω = 0 := by
  let _ : MeasurableSpace (X.orbitSupp Θ) := X.lebesgueSigma G Θ
  have : CompactSpace (X.orbitSupp Θ) := isCompact_iff_compactSpace.1 hcpt
  let J := {j : Σ x, X.OrientedTameStructure n Θ x // (∀ i, j.2.M i ∈ S) ∧ j.2.Represents T}
  let O : J → Set (X.orbitSupp Θ) := fun j => Subtype.val ⁻¹' (X.π '' j.1.2.U)
  have hO : ∀ j, IsOpen (O j) := fun j =>
    (X.proposition_7_1_8 _ j.1.2.isOpen_U).preimage continuous_subtype_val
  have hcovO : ⋃ j, O j = univ := eq_univ_of_forall fun q => by
    obtain ⟨y, hy, hyq⟩ := q.2
    obtain ⟨C, hC⟩ := hcov y hy
    exact mem_iUnion.2 ⟨⟨⟨y, C⟩, hC⟩, y, C.mem_U, hyq⟩
  obtain ⟨Φ, -, huniq⟩ := existsUnique_linearMap_signedMeasure_of_openCover (V := ℝ)
    (borel_le_borelNullSigma _) O hO hcovO (fun _ => 0) (fun _ _ _ _ _ _ => rfl)
  have h1 := huniq (LinearMap.toSpanSingleton ℝ _ (branchedMeasure 𝓘 hΘ hcpt hT hcov ω))
    fun j t K hK hKO => by
      have hval : branchedMeasure 𝓘 hΘ hcpt hT hcov ω K = 0 := by
        rw [branchedMeasure_apply 𝓘 hΘ hcpt hT hcov ω j.1.2 j.2.1 j.2.2 hK
          (by rintro _ ⟨q, hq, rfl⟩; exact hKO hq), localMeasure, sheetSum,
          Finset.sum_eq_zero fun i _ => by rw [hω _ (j.2.1 i), mul_zero], mul_zero]
      change (t • branchedMeasure 𝓘 hΘ hcpt hT hcov ω) K = 0
      change t • (branchedMeasure 𝓘 hΘ hcpt hT hcov ω K) = 0
      rw [hval, smul_zero]
  have h2 := huniq 0 fun j t K hK hKO => rfl
  have h3 := congrArg (fun L : ℝ →ₗ[ℝ] SignedMeasure (X.orbitSupp Θ) => L 1) (h1.trans h2.symm)
  simpa using h3

end Global

end EpGroupoid

end Polyfold
