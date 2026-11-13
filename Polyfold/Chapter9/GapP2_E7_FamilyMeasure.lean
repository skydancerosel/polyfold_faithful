import Polyfold.Chapter9.GapP2_E7_SheetFamily

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5: the gluing step of the proofs of **Theorems 9.5.4, 9.5.5** (p. 446)
and, "using the same techniques" (p. 449), of **Theorems 9.5.15, 9.5.16**, for an arbitrary
oriented sheet family (`GapP2_E7_SheetFamily.lean`).  Numbers and pages are the 2021 text's.

# The measure glued from the local expressions of oriented sheet families

* `NaturalRep.exists_slice_pair`: matching neighbourhoods of two points over one point of `|X|`
  for two natural representations.
* `OrientedSheetFamily.exists_local_agreement`, `OrientedSheetFamily.overlap`: two families
  describing a natural `T'` give the same normalized sums on every measurable `K` in
  `|U(x)| ∩ |U(x')|` (`overlap_of_subset_U`: only the part of `K` in `|D|` matters).
* `OrientedSheetFamily.localSignedMeasure`: the local expression as a signed measure on
  `(|supp Θ'|, L)` for any σ-algebra `L` whose sets have measurable traces on the sheets.
* **`existsUnique_familyMeasure`**: existence and uniqueness of the linear map `ω ↦ μ_ω` into the
  signed measures on `(|supp Θ'|, L)` characterized by the local formula for a class of families
  covering `supp Θ'`.  E1's `existsUnique_branchedMeasure` is the instance `D = supp Θ`,
  `Θ' = Θ`; the boundary measures of Theorems 9.5.15, 9.5.16 are the instance of
  `GapP2_E7_BoundaryMeasure.lean`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {X : EpGroupoid Obj Mor} {S : Set (Set Obj)} {G : SheetNullSets S} {Ω : Type*}
  [AddCommGroup Ω] [Module ℝ Ω] (𝓘 : X.SheetIntegration G Ω) {D : Set Obj} {m : ℕ}

/-- **Matching neighbourhoods of two points over one point of `|X|`**, for two natural
representations (E1's `exists_slice_pair`, stated for the representations only). -/
theorem NaturalRep.exists_slice_pair {x x' : Obj} (R : X.NaturalRep x) (R' : X.NaturalRep x')
    (a : R.U) (a' : R'.U) (hπ : X.π (a : Obj) = X.π (a' : Obj)) :
    ∃ (φ : Mor) (V : Set Obj), IsOpen V ∧ (a : Obj) ∈ V ∧ V ⊆ R.U ∧
      V ⊆ (X.sheetAt φ).srcSet ∧ X.hat φ '' V ⊆ R'.U ∧
      (∀ g ∈ MulAction.stabilizer (X.Isotropy x) a, R.Φ g '' V = V) ∧
      (∀ g ∉ MulAction.stabilizer (X.Isotropy x) a, Disjoint (R.Φ g '' V) V) ∧
      (∀ g ∈ MulAction.stabilizer (X.Isotropy x') a', R'.Φ g '' (X.hat φ '' V) = X.hat φ '' V) ∧
      (∀ g ∉ MulAction.stabilizer (X.Isotropy x') a',
        Disjoint (R'.Φ g '' (X.hat φ '' V)) (X.hat φ '' V)) ∧
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
    R.exists_slice a hf.isScSmoothOn.isOpen hzS
  have hfV₀o : IsOpen (X.hat φ '' V₀) := hf.isOpen_image_of_subset hV₀o hV₀W
  obtain ⟨V₀', hV₀'o, ha'V₀', hV₀'U, hV₀'W, hV₀'H, hV₀'d⟩ :=
    R'.exists_slice a' hfV₀o ⟨a, haV₀, hfz⟩
  have hWo : IsOpen (V₀ ∩ ((X.sheetAt φ).srcSet ∩ X.hat φ ⁻¹' V₀')) :=
    hV₀o.inter (hf.isScSmoothOn.continuousOn.isOpen_inter_preimage hf.isScSmoothOn.isOpen hV₀'o)
  obtain ⟨V, hVo, haV, hVU, hVW, hVH, hVd⟩ :=
    R.exists_slice a hWo ⟨haV₀, hzS, by rw [mem_preimage, hfz]; exact ha'V₀'⟩
  have hVS : V ⊆ (X.sheetAt φ).srcSet := fun w hw => (hVW hw).2.1
  have hV'sub : X.hat φ '' V ⊆ V₀' := by
    rintro _ ⟨w, hw, rfl⟩; exact (hVW hw).2.2
  have hsub : ∀ g ∈ MulAction.stabilizer (X.Isotropy x') a',
      R'.Φ g '' (X.hat φ '' V) ⊆ X.hat φ '' V := by
    rintro g hg _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hu : R'.Φ g (X.hat φ w) ∈ V₀' := by
      rw [← hV₀'H g hg]; exact ⟨_, hV'sub ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨w₂, hw₂, hw₂u⟩ := hV₀'W hu
    have hπw : X.π w = X.π w₂ := by
      rw [← hπf w₂ (hV₀W hw₂), hw₂u, R'.π_Φ g (hV₀'U (hV'sub ⟨w, hw, rfl⟩)),
        hπf w (hVS hw)]
    obtain ⟨h, hh⟩ := (R.π_eq_π_iff_exists_smul (y := ⟨w, hVU hw⟩)
      (z := ⟨w₂, hV₀U hw₂⟩)).1 hπw
    have hh' : R.Φ h w = w₂ := congrArg Subtype.val hh
    have hhH : h ∈ MulAction.stabilizer (X.Isotropy x) a := by
      by_contra hn
      exact Set.disjoint_left.1 (hV₀d h hn) ⟨w, (hVW hw).1, hh'⟩ hw₂
    have hw₂V : w₂ ∈ V := by rw [← hVH h hhH]; exact ⟨w, hw, hh'⟩
    exact ⟨w₂, hw₂V, hw₂u⟩
  refine ⟨φ, V, hVo, haV, hVU, hVS, hV'sub.trans hV₀'U, hVH, hVd, fun g hg => ?_,
    fun g hg => (hV₀'d g hg).mono (image_mono hV'sub) hV'sub, hsrc, htgt⟩
  refine Subset.antisymm (hsub g hg) fun v hv => ?_
  have hvU : v ∈ R'.U := hV₀'U (hV'sub hv)
  exact ⟨R'.Φ g⁻¹ v, hsub g⁻¹ (inv_mem hg) ⟨v, hv, rfl⟩, R'.Φ_Φ_inv g hvU⟩

namespace OrientedSheetFamily

section Overlap

variable {x x' : Obj} (F : X.OrientedSheetFamily D m x) (F' : X.OrientedSheetFamily D m x')

/-- **Local agreement (Lemmas 9.5.9 and 9.5.11 combined), for families.** -/
theorem exists_local_agreement (hD : X.IsMorSaturated D) {T' : Obj → X.PObj.OrTangent →₀ ℚ}
    (hnat : X.IsNaturalOn T' D) (hS : ∀ i, F.N i ∈ S)
    (hS' : ∀ i, F'.N i ∈ S) (hFT : F.Represents T') (hF'T : F'.Represents T')
    (a : F.rep.U) (a' : F'.rep.U) (hπ : X.π (a : Obj) = X.π (a' : Obj)) :
    ∃ V : Set Obj, IsOpen V ∧ (a : Obj) ∈ V ∧ V ⊆ F.rep.U ∧ ∀ (ω : Ω) (K : Set X.OrbitSpace),
      K ⊆ X.π '' (F.MU ∩ V) → F.IsMeas G (X.π ⁻¹' K) → ∃ s : ℝ,
        F.sheetSum 𝓘 ω (X.π ⁻¹' K) =
          (Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) : ℝ) * s ∧
        F'.sheetSum 𝓘 ω (X.π ⁻¹' K) =
          (Nat.card (X.Isotropy x' ⧸ MulAction.stabilizer (X.Isotropy x') a') : ℝ) * s := by
  obtain ⟨φ, V, hVo, haV, hVU, hVS, hV'U, hVH, hVd, hV'H, hV'd, -, -⟩ :=
    F.rep.exists_slice_pair F'.rep a a' hπ
  have hf := X.isScDiffeoOn_hat φ
  have hmor := X.isMorTangentOn_hat φ
  refine ⟨V, hVo, haV, hVU, fun ω K hK hKm => ?_⟩
  have hrel : ∀ w ∈ (X.sheetAt φ).srcSet, (X.hat φ w ∈ D ↔ w ∈ D) ∧
      X.π (X.hat φ w) = X.π w := fun w hw => by
    obtain ⟨ψ, h1, h2, -⟩ := hmor w hw
    have h3 := hD ψ
    rw [h1, h2] at h3
    exact ⟨h3.symm, ((X.π_eq_π_iff).2 ⟨ψ, h1, h2⟩).symm⟩
  set Kt : Set Obj := F.MU ∩ V ∩ X.π ⁻¹' K with hKt
  have hKtm : F.IsMeas G Kt := fun i => by
    have h1 : G.IsMeasIn (F.N i) (V ∩ X.π ⁻¹' K) :=
      (SheetNullSets.isMeasIn_of_borel (MeasurableSpace.measurableSet_generateFrom hVo)).inter
        (hKm i)
    refine h1.congr_inter ?_
    rw [hKt, inter_assoc F.MU V, F.MU_inter_inter]
  have hKtU : Kt ⊆ F.MU ∩ (X.sheetAt φ).srcSet := fun w hw => ⟨hw.1.1, hVS hw.1.2⟩
  have himg : X.hat φ '' Kt = F'.MU ∩ X.hat φ '' V ∩ X.π ⁻¹' K := by
    ext u
    constructor
    · rintro ⟨w, ⟨⟨hwM, hwV⟩, hwK⟩, rfl⟩
      obtain ⟨h1, h2⟩ := hrel w (hVS hwV)
      rw [MU_eq] at hwM ⊢
      exact ⟨⟨⟨h1.2 hwM.1, hV'U ⟨w, hwV, rfl⟩⟩, ⟨w, hwV, rfl⟩⟩,
        by rw [mem_preimage, h2]; exact hwK⟩
    · rintro ⟨⟨huM, ⟨w, hwV, rfl⟩⟩, huK⟩
      obtain ⟨h1, h2⟩ := hrel w (hVS hwV)
      rw [MU_eq] at huM
      have hwM : w ∈ F.MU := by
        rw [MU_eq]
        exact ⟨h1.1 huM.1, hVU hwV⟩
      exact ⟨w, ⟨⟨hwM, hwV⟩, by rw [mem_preimage, ← h2]; exact huK⟩, rfl⟩
  have hK' : K ⊆ X.π '' (F'.MU ∩ X.hat φ '' V) := by
    intro q hq
    obtain ⟨w, ⟨hwM, hwV⟩, rfl⟩ := hK hq
    have hmem : X.hat φ w ∈ X.hat φ '' Kt := ⟨w, ⟨⟨hwM, hwV⟩, hq⟩, rfl⟩
    rw [himg] at hmem
    exact ⟨_, hmem.1, (hrel w (hVS hwV)).2⟩
  have hKt'm : F'.IsMeas G (F'.MU ∩ X.hat φ '' V ∩ X.π ⁻¹' K) := by
    rw [← himg]
    exact hKtm.image 𝓘 F F' hS hS' hf hmor hKtU
  have e1 := F.sheetSum_preimage_eq_card_mul_slice 𝓘 hD hnat hS hFT a hVU hVH hVd ω hK hKtm
  have e2 := F'.sheetSum_preimage_eq_card_mul_slice 𝓘 hD hnat hS' hF'T a' hV'U hV'H hV'd ω hK'
    hKt'm
  have e3 : F'.sheetSum 𝓘 ω (F'.MU ∩ X.hat φ '' V ∩ X.π ⁻¹' K) = F.sheetSum 𝓘 ω Kt := by
    rw [← himg]
    exact F.sheetSum_image 𝓘 F' hnat hS hS' hFT hF'T hf hmor ω hKtU hKtm
      (by rw [himg]; exact fun u hu => hu.1.1)
  exact ⟨F.sheetSum 𝓘 ω Kt, e1, by rw [e2, e3]⟩

/-- **The local expressions agree on overlaps, for families** (2021 p. 446, "this definition
does not depend on the choices involved"): for a normalizing factor `c` invariant under morphisms
with `c(x) · ♯(G_x/H_y) = c(y)`, and a measurable `K ⊆ |M_U| ∩ |M_{U'}|`. -/
theorem overlap (hD : X.IsMorSaturated D) {T' : Obj → X.PObj.OrTangent →₀ ℚ}
    (hnat : X.IsNaturalOn T' D) (hS : ∀ i, F.N i ∈ S)
    (hS' : ∀ i, F'.N i ∈ S) (hFT : F.Represents T') (hF'T : F'.Represents T') (c : Obj → ℝ)
    (hc : ∀ φ : Mor, c (X.src φ) = c (X.tgt φ))
    (hcx : ∀ a : F.rep.U, c x *
      (Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) : ℝ) = c a)
    (hcx' : ∀ a : F'.rep.U, c x' *
      (Nat.card (X.Isotropy x' ⧸ MulAction.stabilizer (X.Isotropy x') a) : ℝ) = c a)
    (ω : Ω) {K : Set X.OrbitSpace} (hK : K ⊆ X.π '' F.MU) (hK' : K ⊆ X.π '' F'.MU)
    (hKm : F.IsMeas G (X.π ⁻¹' K)) (hKm' : F'.IsMeas G (X.π ⁻¹' K)) :
    c x * F.sheetSum 𝓘 ω (X.π ⁻¹' K) = c x' * F'.sheetSum 𝓘 ω (X.π ⁻¹' K) := by
  classical
  have hloc : ∀ z ∈ F.MU ∩ X.π ⁻¹' K, ∃ V : Set Obj, IsOpen V ∧ z ∈ V ∧ V ⊆ F.rep.U ∧
      ∀ K₁ : Set X.OrbitSpace, K₁ ⊆ X.π '' (F.MU ∩ V) → F.IsMeas G (X.π ⁻¹' K₁) →
        c x * F.sheetSum 𝓘 ω (X.π ⁻¹' K₁) = c x' * F'.sheetSum 𝓘 ω (X.π ⁻¹' K₁) := by
    intro z hz
    obtain ⟨z', hz', hzz'⟩ := hK' hz.2
    obtain ⟨V, hVo, hzV, hVsub, hV⟩ := F.exists_local_agreement 𝓘 F' hD hnat hS hS' hFT hF'T
      ⟨z, F.MU_subset_U hz.1⟩ ⟨z', F'.MU_subset_U hz'⟩ hzz'.symm
    refine ⟨V, hVo, hzV, hVsub, fun K₁ hK₁ hK₁m => ?_⟩
    obtain ⟨s, e1, e2⟩ := hV ω K₁ hK₁ hK₁m
    obtain ⟨φ, hφs, hφt⟩ := (X.π_eq_π_iff).1 hzz'.symm
    have hcz : c z = c z' := by have := hc φ; rwa [hφs, hφt] at this
    rw [e1, e2, ← mul_assoc, ← mul_assoc, hcx ⟨z, F.MU_subset_U hz.1⟩,
      hcx' ⟨z', F'.MU_subset_U hz'⟩]
    exact congrArg (· * s) hcz
  rcases (F.MU ∩ X.π ⁻¹' K).eq_empty_or_nonempty with hempty | hne
  · have hK0 : K = ∅ := eq_empty_of_forall_notMem fun q hq => by
      obtain ⟨w, hw, rfl⟩ := hK hq
      exact (hempty ▸ (⟨hw, hq⟩ : w ∈ F.MU ∩ X.π ⁻¹' K) : w ∈ (∅ : Set Obj))
    rw [hK0, preimage_empty, F.sheetSum_empty 𝓘 hS, F'.sheetSum_empty 𝓘 hS', mul_zero, mul_zero]
  set At : Set Obj := F.MU ∩ X.π ⁻¹' K with hAt
  have : Nonempty At := hne.to_subtype
  choose! V hVo hzV hVsub hVP using hloc
  have hcount : ∀ i : F.ι, ∃ r : Set At, r.Countable ∧
      At ∩ F.N i ⊆ ⋃ z ∈ r, V (z : Obj) := by
    intro i
    have := 𝓘.lindelof _ (hS i)
    have hL : IsLindelof (Subtype.val ⁻¹' At : Set (F.N i)) :=
      HereditarilyLindelofSpace.isLindelof _
    obtain ⟨r, hr, hsub⟩ := hL.elim_countable_subcover
      (fun z : At => (Subtype.val ⁻¹' V (z : Obj) : Set (F.N i)))
      (fun z => (hVo z z.2).preimage continuous_subtype_val)
      (fun y hy => mem_iUnion.2 ⟨⟨(y : Obj), hy⟩, hzV _ hy⟩)
    refine ⟨r, hr, fun y hy => ?_⟩
    have := hsub (show (⟨y, hy.2⟩ : F.N i) ∈ (Subtype.val ⁻¹' At : Set (F.N i)) from hy.1)
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
  have hKpm : ∀ k, F.IsMeas G (X.π ⁻¹' Kp k) := fun k i => by
    rw [hpre k]; exact (hKm i).inter (hborel _ k)
  have hKpm' : ∀ k, F'.IsMeas G (X.π ⁻¹' Kp k) := fun k i => by
    rw [hpre k]; exact (hKm' i).inter (hborel _ k)
  have hpd : Pairwise (Function.onFun Disjoint fun k => X.π ⁻¹' Kp k) := fun k l hkl =>
    (hKpd hkl).preimage _
  have hpU : ⋃ k, X.π ⁻¹' Kp k = X.π ⁻¹' K := by rw [← preimage_iUnion, hKpU]
  have h1 := (F.sheetSum_hasSum 𝓘 hS ω _ hKpm hpd).mul_left (c x)
  have h2 := (F'.sheetSum_hasSum 𝓘 hS' ω _ hKpm' hpd).mul_left (c x')
  rw [hpU] at h1 h2
  have hterm : ∀ k, c x * F.sheetSum 𝓘 ω (X.π ⁻¹' Kp k) =
      c x' * F'.sheetSum 𝓘 ω (X.π ⁻¹' Kp k) := fun k => by
    refine hVP _ (e k).2 (Kp k) (fun q hq => ?_) (hKpm k)
    obtain ⟨v, hv, rfl⟩ := hq.1.2
    obtain ⟨w, hw, hwq⟩ := hK hq.1.1
    have hvs : v ∈ D := by
      obtain ⟨ψ, h1, h2⟩ := (X.π_eq_π_iff).1 hwq
      have h3 := hD ψ
      rw [h1, h2] at h3
      exact h3.1 (F.MU_subset_D hw)
    have hvU : v ∈ F.rep.U := hVsub _ (e k).2 hv
    exact ⟨v, ⟨by rw [MU_eq]; exact ⟨hvs, hvU⟩, hv⟩, rfl⟩
  exact h1.unique (by simpa only [hterm] using h2)

/-- **Only the part of `K` in `|D|` matters**: the sums over `π⁻¹(K)` and `π⁻¹(K ∩ |D|)` agree. -/
theorem sheetSum_preimage_inter_D (ω : Ω) (K : Set X.OrbitSpace) :
    F.sheetSum 𝓘 ω (X.π ⁻¹' (K ∩ X.π '' D)) = F.sheetSum 𝓘 ω (X.π ⁻¹' K) :=
  F.sheetSum_congr 𝓘 ω fun i => by
    ext y
    simp only [mem_inter_iff, mem_preimage]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, y, F.MU_subset_D (F.subset_MU i h.2), rfl⟩,
      h.2⟩⟩

theorem image_inter_D_subset (hD : X.IsMorSaturated D) {K : Set X.OrbitSpace}
    (hK : K ⊆ X.π '' F.rep.U) : K ∩ X.π '' D ⊆ X.π '' F.MU := by
  rintro q ⟨hqU, ⟨d, hd, rfl⟩⟩
  obtain ⟨u, hu, hud⟩ := hK hqU
  obtain ⟨ψ, h1, h2⟩ := (X.π_eq_π_iff).1 hud.symm
  have h3 := hD ψ
  rw [h1, h2] at h3
  exact ⟨u, by rw [MU_eq]; exact ⟨h3.1 hd, hu⟩, hud⟩

/-- **The overlap statement for every measurable `K ⊆ |U(x)| ∩ |U(x')|`.** -/
theorem overlap_of_subset_U (hD : X.IsMorSaturated D) {T' : Obj → X.PObj.OrTangent →₀ ℚ}
    (hnat : X.IsNaturalOn T' D) (hS : ∀ i, F.N i ∈ S)
    (hS' : ∀ i, F'.N i ∈ S) (hFT : F.Represents T') (hF'T : F'.Represents T') (c : Obj → ℝ)
    (hc : ∀ φ : Mor, c (X.src φ) = c (X.tgt φ))
    (hcx : ∀ a : F.rep.U, c x *
      (Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) : ℝ) = c a)
    (hcx' : ∀ a : F'.rep.U, c x' *
      (Nat.card (X.Isotropy x' ⧸ MulAction.stabilizer (X.Isotropy x') a) : ℝ) = c a)
    (ω : Ω) {K : Set X.OrbitSpace} (hK : K ⊆ X.π '' F.rep.U) (hK' : K ⊆ X.π '' F'.rep.U)
    (hKm : F.IsMeas G (X.π ⁻¹' K)) (hKm' : F'.IsMeas G (X.π ⁻¹' K)) :
    c x * F.sheetSum 𝓘 ω (X.π ⁻¹' K) = c x' * F'.sheetSum 𝓘 ω (X.π ⁻¹' K) := by
  have e : ∀ {x₀ : Obj} (F₀ : X.OrientedSheetFamily D m x₀) (i : F₀.ι),
      X.π ⁻¹' K ∩ F₀.N i = X.π ⁻¹' (K ∩ X.π '' D) ∩ F₀.N i := fun F₀ i => by
    ext y
    simp only [mem_inter_iff, mem_preimage]
    exact ⟨fun h => ⟨⟨h.1, y, F₀.MU_subset_D (F₀.subset_MU i h.2), rfl⟩, h.2⟩,
      fun h => ⟨h.1.1, h.2⟩⟩
  rw [← F.sheetSum_preimage_inter_D, ← F'.sheetSum_preimage_inter_D]
  exact F.overlap 𝓘 F' hD hnat hS hS' hFT hF'T c hc hcx hcx' ω (F.image_inter_D_subset hD hK)
    (F'.image_inter_D_subset hD hK') (fun i => (hKm i).congr_inter (e F i))
    (fun i => (hKm' i).congr_inter (e F' i))

end Overlap

/-! ### The local expressions as signed measures -/

section LocalSigned

open scoped Classical

variable {x : Obj} (F : X.OrientedSheetFamily D m x) {Θ' : Obj → ℚ}
  (L : MeasurableSpace (X.orbitSupp Θ'))

/-- **The local expression as a signed measure**: `K ↦ c · ∑ σᵢ ∫_{Kᵢ} ω|(Nᵢ, oᵢ)` on
`(|supp Θ'|, L)`, for a σ-algebra `L` whose sets have measurable traces on the sheets. -/
def localSignedMeasure (hS : ∀ i, F.N i ∈ S)
    (hmeas : ∀ K, MeasurableSet[L] K → F.IsMeas G (X.π ⁻¹' (Subtype.val '' K))) (c : ℝ) :
    Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ') L :=
  letI : MeasurableSpace (X.orbitSupp Θ') := L
  { toFun := fun ω =>
      { measureOf' := fun K =>
          if MeasurableSet K then c * F.sheetSum 𝓘 ω (X.π ⁻¹' (Subtype.val '' K)) else 0
        empty' := by
          rw [if_pos MeasurableSet.empty, image_empty, preimage_empty, F.sheetSum_empty 𝓘 hS,
            mul_zero]
        not_measurable' := fun K hK => if_neg hK
        m_iUnion' := fun A hA hd => by
          rw [if_pos (MeasurableSet.iUnion hA)]
          simp only [if_pos (hA _)]
          rw [image_iUnion, preimage_iUnion]
          exact (F.sheetSum_hasSum 𝓘 hS ω _ (fun k => hmeas _ (hA k))
            fun k l hkl => ((Set.disjoint_image_iff Subtype.val_injective).2
              (hd hkl)).preimage _).mul_left c }
    map_add' := fun ω τ => VectorMeasure.ext fun K hK => by
      have e1 : (if MeasurableSet K then
          c * F.sheetSum 𝓘 (ω + τ) (X.π ⁻¹' (Subtype.val '' K)) else (0 : ℝ)) =
          (if MeasurableSet K then c * F.sheetSum 𝓘 ω (X.π ⁻¹' (Subtype.val '' K)) else (0 : ℝ)) +
          (if MeasurableSet K then c * F.sheetSum 𝓘 τ (X.π ⁻¹' (Subtype.val '' K)) else (0 : ℝ)) := by
        rw [if_pos hK, if_pos hK, if_pos hK, F.sheetSum_add, mul_add]
      exact e1
    map_smul' := fun r ω => VectorMeasure.ext fun K hK => by
      have e1 : (if MeasurableSet K then
          c * F.sheetSum 𝓘 (r • ω) (X.π ⁻¹' (Subtype.val '' K)) else (0 : ℝ)) =
          r • (if MeasurableSet K then
            c * F.sheetSum 𝓘 ω (X.π ⁻¹' (Subtype.val '' K)) else (0 : ℝ)) := by
        rw [if_pos hK, if_pos hK, F.sheetSum_smul, smul_eq_mul]
        ring
      exact e1 }

theorem localSignedMeasure_apply (hS : ∀ i, F.N i ∈ S)
    (hmeas : ∀ K, MeasurableSet[L] K → F.IsMeas G (X.π ⁻¹' (Subtype.val '' K))) (c : ℝ)
    (ω : Ω) {K : Set (X.orbitSupp Θ')} (hK : MeasurableSet[L] K) :
    F.localSignedMeasure 𝓘 L hS hmeas c ω K =
      c * F.sheetSum 𝓘 ω (X.π ⁻¹' (Subtype.val '' K)) :=
  if_pos hK

end LocalSigned

end OrientedSheetFamily

/-! ### Existence and uniqueness of the glued measure -/

section Global

open OrientedSheetFamily

/-- **Theorems 9.5.4, 9.5.5 / 9.5.15, 9.5.16 for oriented sheet families**: let `D` be saturated,
`T'` natural on `D`, `|supp Θ'|` compact with a σ-algebra `L ⊇ B(|supp Θ'|)`, `c` a normalizing
factor (`c(x) · ♯(G_x/H_y) = c(y)`), and `Good` a class of families with sheets in `S`
describing `T'`, whose sets of `L` have measurable traces, one at every point of `supp Θ'`.
There is exactly one linear `ω ↦ μ_ω` into the signed measures on `(|supp Θ'|, L)` with
`μ_ω(K) = c(x) ∑ σᵢ ∫_{Kᵢ} ω|(Nᵢ, oᵢ)` for every family of the class and every measurable
`K ⊆ |U(x)|`. -/
theorem existsUnique_familyMeasure (hD : X.IsMorSaturated D) {T' : Obj → X.PObj.OrTangent →₀ ℚ}
    (hnat : X.IsNaturalOn T' D) {Θ' : Obj → ℚ} (hcpt : IsCompact (X.orbitSupp Θ'))
    (L : MeasurableSpace (X.orbitSupp Θ')) (hL : borel (X.orbitSupp Θ') ≤ L)
    (c : Obj → ℝ) (hc : ∀ φ : Mor, c (X.src φ) = c (X.tgt φ))
    (Good : ∀ x, X.OrientedSheetFamily D m x → Prop)
    (hGS : ∀ x F, Good x F → ∀ i, F.N i ∈ S) (hGT : ∀ x F, Good x F → F.Represents T')
    (hGc : ∀ x F, Good x F → ∀ a : F.rep.U, c x *
      (Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) : ℝ) = c a)
    (hGm : ∀ x F, Good x F → ∀ K, MeasurableSet[L] K → F.IsMeas G (X.π ⁻¹' (Subtype.val '' K)))
    (hcov : ∀ x ∈ supp Θ', ∃ F, Good x F) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp Θ') L,
      ∀ (ω : Ω) (x : Obj) (F : X.OrientedSheetFamily D m x), Good x F →
        ∀ K : Set (X.orbitSupp Θ'), MeasurableSet[L] K →
          Subtype.val '' K ⊆ X.π '' F.rep.U →
          Φ ω K = c x * F.sheetSum 𝓘 ω (X.π ⁻¹' (Subtype.val '' K)) := by
  let _ : MeasurableSpace (X.orbitSupp Θ') := L
  have : CompactSpace (X.orbitSupp Θ') := isCompact_iff_compactSpace.1 hcpt
  let J := {j : Σ x, X.OrientedSheetFamily D m x // Good j.1 j.2}
  let O : J → Set (X.orbitSupp Θ') := fun j => Subtype.val ⁻¹' (X.π '' j.1.2.rep.U)
  have hO : ∀ j, IsOpen (O j) := fun j =>
    (X.proposition_7_1_8 _ j.1.2.rep.isOpen_U).preimage continuous_subtype_val
  have hcovO : ⋃ j, O j = univ := eq_univ_of_forall fun q => by
    obtain ⟨y, hy, hyq⟩ := q.2
    obtain ⟨F, hF⟩ := hcov y hy
    exact mem_iUnion.2 ⟨⟨⟨y, F⟩, hF⟩, y, F.rep.mem_U, hyq⟩
  let μ : J → Ω →ₗ[ℝ] SignedMeasure (X.orbitSupp Θ') := fun j =>
    j.1.2.localSignedMeasure 𝓘 L (hGS _ _ j.2) (hGm _ _ j.2) (c j.1.1)
  have hsub : ∀ (j : J) {K : Set (X.orbitSupp Θ')}, K ⊆ O j →
      Subtype.val '' K ⊆ X.π '' j.1.2.rep.U := by
    rintro j K hK _ ⟨q, hq, rfl⟩
    exact hK hq
  have hcompat : ∀ j l ω K, MeasurableSet K → K ⊆ O j ∩ O l → μ j ω K = μ l ω K := by
    intro j l ω K hK hKO
    change j.1.2.localSignedMeasure 𝓘 L (hGS _ _ j.2) (hGm _ _ j.2) (c j.1.1) ω K =
      l.1.2.localSignedMeasure 𝓘 L (hGS _ _ l.2) (hGm _ _ l.2) (c l.1.1) ω K
    rw [localSignedMeasure_apply _ _ _ _ _ _ _ hK, localSignedMeasure_apply _ _ _ _ _ _ _ hK]
    exact j.1.2.overlap_of_subset_U 𝓘 l.1.2 hD hnat (hGS _ _ j.2) (hGS _ _ l.2) (hGT _ _ j.2)
      (hGT _ _ l.2) c hc (hGc _ _ j.2) (hGc _ _ l.2) ω
      (hsub j (hKO.trans inter_subset_left)) (hsub l (hKO.trans inter_subset_right))
      (hGm _ _ j.2 K hK) (hGm _ _ l.2 K hK)
  obtain ⟨Φ, hΦ, huniq⟩ := existsUnique_linearMap_signedMeasure_of_openCover hL O hO hcovO μ
    hcompat
  refine ⟨Φ, fun ω x F hF K hK hKU => ?_, fun Ψ hΨ => huniq Ψ fun j ω K hK hKO => ?_⟩
  · rw [hΦ ⟨⟨x, F⟩, hF⟩ ω K hK fun q hq => hKU ⟨q, hq, rfl⟩]
    exact localSignedMeasure_apply _ _ _ _ _ _ _ hK
  · rw [hΨ ω _ _ j.2 K hK (hsub j hKO)]
    exact (localSignedMeasure_apply _ _ _ _ _ _ _ hK).symm

/-- The normalizing factor `1/♯G_x` satisfies the hypotheses of `existsUnique_familyMeasure`. -/
theorem card_isotropy_normalizing {x : Obj} (R : X.NaturalRep x) (a : R.U) :
    (Nat.card (X.Isotropy x) : ℝ)⁻¹ *
      (Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) : ℝ) =
      (Nat.card (X.Isotropy (a : Obj)) : ℝ)⁻¹ := by
  have : Finite (X.Isotropy x) := NatRepConstruction.finite_isotropy X x
  have : Finite (X.Isotropy (a : Obj)) := NatRepConstruction.finite_isotropy X _
  exact inv_mul_eq_inv_of_mul_eq (R.card_quotient_stabilizer_mul_card_isotropy a)
    Nat.card_pos Nat.card_pos

/-- The normalizing factor `1/♯G_x^eff` satisfies them on a `U(x)` with the property of
Definition 7.2.18. -/
theorem card_effIsotropy_normalizing {x : Obj} (R : X.NaturalRep x) (hL : R.HasLUC) (a : R.U) :
    (Nat.card (X.EffIsotropy x) : ℝ)⁻¹ *
      (Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) : ℝ) =
      (Nat.card (X.EffIsotropy (a : Obj)) : ℝ)⁻¹ := by
  have := finite_effIsotropy (X := X) x
  have := finite_effIsotropy (X := X) (a : Obj)
  exact inv_mul_eq_inv_of_mul_eq (R.card_quotient_stabilizer_mul_card_effIsotropy hL a)
    Nat.card_pos Nat.card_pos

end Global

end EpGroupoid

end Polyfold
