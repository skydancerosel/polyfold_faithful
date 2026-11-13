import Polyfold.Chapter14.P3W6A6_EmptyIndex
import Polyfold.Chapter14.P3W5T9_Assembly
import Polyfold.Chapter14.P3W5Z5_Instance

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 14,
§§14.3–14.5, pp. 656–677: the data of §§14.3–14.5 (T9's `AssemblyInput`) from the objects of
§14.3 (Z5's `ZConcrete`), Proposition 14.4.14 and Lemma 14.5.1.

# The instance of `AssemblyInput`

## What is formalized

* `tgt_mem_of_closure_a6`: for a natural neighbourhood `Ũ(a)` and an invariant `V ⊆ Ũ(a)`, a
  morphism from `V` to a point of `cl Ũ(a)` ends in `V` (the points near `φ` with both ends in
  `Ũ(a)` are `Γ(g, ·)`; `G_a` is finite and `Mor` is Hausdorff).
* `closure_support_subset_a6`: hence `tsupport β ⊆ π⁻¹(π(V))` gives
  `cl{y ∈ Ũ(a) | β(y) ≠ 0} ⊆ V`, i.e. (14.53) for the `β_a` of Lemma 14.5.1 with the `V̂_a`
  themselves (no shrinking of the cover is needed).
* `ZConcrete.BetaSpec`, `ZConcrete.exists_betaSpec`: Lemma 14.5.1 with `A`, `B = ∂X`, the `V̂_a`
  of Proposition 14.3.8.
* `ZConcrete.transportInput_a6`: GL's `TransportInput` (with `ŝᵃ` from Z5's
  `ZConcrete.proposition_14_4_14`); `ZConcrete.assemblyInput_a6`: T9's `AssemblyInput`.
* **`exists_assemblyInput_a6`**: under the hypotheses of Theorem 14.1.9 (tame `X`, paracompact
  `|X|`, partitions of unity), tame strong bundle charts (the text's standing assumption, as in
  LX and Z5) and `ChargesBoundary Λ` (`I_x ≠ ∅`, see `P3W6A6_EmptyIndex`), every structurable
  `Λ` over `∂X` has an `AssemblyInput`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### Morphisms from an invariant set to the closure of a natural neighbourhood -/

/-- A morphism `φ` from an invariant `V ⊆ Ũ(x)` to a point of `cl Ũ(x)` ends in `V`: `φ` is a
limit of morphisms with both ends in `Ũ(x)`, i.e. of `Γ(g_ψ, s(ψ))`; `G_x` is finite, so `φ` is
in the closure of `{ψ | Γ(g, s(ψ)) = ψ}` for one `g`, a closed condition near `φ`. -/
theorem tgt_mem_of_closure_a6 {x : A.Obj} (N : A.X.NatNbhd x) {V : Set A.Obj} (hV : V ⊆ N.U)
    (hinv : ∀ g, MapsTo (N.rep.Φ g) V V) {φ : A.Mor} (hs : A.X.src φ ∈ V)
    (ht : A.X.tgt φ ∈ closure N.U) : A.X.tgt φ ∈ V := by
  have hsU : A.X.src φ ∈ N.U := hV hs
  have hsR : A.X.src φ ∈ N.rep.U := N.U_subset hsU
  set E : Set A.Mor := {ψ | A.X.src ψ ∈ N.U ∧ A.X.tgt ψ ∈ N.U} with hE
  have hφE : φ ∈ closure E := by
    rw [mem_closure_iff_nhds]
    intro M hM
    have hM' : M ∩ A.X.src ⁻¹' N.U ∈ 𝓝 φ :=
      inter_mem hM (A.X.continuous_src.continuousAt.preimage_mem_nhds
        (N.isOpen_U.mem_nhds hsU))
    have himg := A.X.isLocalScDiffeo_tgt.isOpenMap.image_mem_nhds hM'
    obtain ⟨z, ⟨ψ, hψ, rfl⟩, hzU⟩ := mem_closure_iff_nhds.1 ht _ himg
    exact ⟨ψ, hψ.1, hψ.2, hzU⟩
  have hEsub : E ⊆ ⋃ g : A.X.Isotropy x, {ψ | N.rep.Γ g (A.X.src ψ) = ψ} := by
    rintro ψ ⟨h1, h2⟩
    obtain ⟨g, hg, -⟩ := N.rep.existsUnique_Γ ψ (N.U_subset h1) (N.U_subset h2)
    exact mem_iUnion.2 ⟨g, hg⟩
  have hcl := closure_mono hEsub hφE
  rw [closure_iUnion_of_finite] at hcl
  obtain ⟨g, hg⟩ := mem_iUnion.1 hcl
  have hcont : ContinuousAt (fun ψ => N.rep.Γ g (A.X.src ψ)) φ :=
    ((N.rep.isScSmoothOn_Γ g).continuousOn.continuousAt (N.rep.isOpen_U.mem_nhds hsR)).comp
      A.X.continuous_src.continuousAt
  have heq : N.rep.Γ g (A.X.src φ) = φ := by
    have : (𝓝[{ψ | N.rep.Γ g (A.X.src ψ) = ψ}] φ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hg
    have h1 : Tendsto (fun ψ => N.rep.Γ g (A.X.src ψ))
        (𝓝[{ψ | N.rep.Γ g (A.X.src ψ) = ψ}] φ) (𝓝 (N.rep.Γ g (A.X.src φ))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun ψ => N.rep.Γ g (A.X.src ψ))
        (𝓝[{ψ | N.rep.Γ g (A.X.src ψ) = ψ}] φ) (𝓝 φ) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
        (eventually_nhdsWithin_of_forall fun ψ hψ => hψ.symm)
    exact tendsto_nhds_unique h1 h2
  rw [← heq, N.rep.tgt_Γ g _ hsR]
  exact hinv g hs

/-- **(14.53) from Lemma 14.5.1 (1)**: if `tsupport β ⊆ π⁻¹(π(V))` for an invariant open
`V ⊆ Ũ(x)`, then `cl{y ∈ Ũ(x) | β(y) ≠ 0} ⊆ V`. -/
theorem closure_support_subset_a6 {x : A.Obj} (N : A.X.NatNbhd x) {V : Set A.Obj}
    (hV : V ⊆ N.U) (hinv : ∀ g, MapsTo (N.rep.Φ g) V V) {β : A.Obj → ℝ}
    (hβ : tsupport β ⊆ A.X.saturation V) : closure {y ∈ N.U | β y ≠ 0} ⊆ V := by
  intro z hz
  have hzU : z ∈ closure N.U := closure_mono (sep_subset _ _) hz
  have hzβ : z ∈ tsupport β := closure_mono (fun y hy => hy.2) hz
  obtain ⟨w, hw, hwz⟩ := hβ hzβ
  obtain ⟨φ, hs, ht⟩ := A.X.π_eq_π_iff.1 hwz
  subst hs ht
  exact tgt_mem_of_closure_a6 N hV hinv hw hzU

/-- Lemma 14.5.1 (1): `β ≠ 0` only on the saturation of `V`. -/
theorem exists_mor_of_ne_zero_a6 {V : Set A.Obj} {β : A.Obj → ℝ}
    (hβ : tsupport β ⊆ A.X.saturation V) {y : A.Obj} (hy : β y ≠ 0) :
    ∃ φ, A.X.src φ ∈ V ∧ A.X.tgt φ = y := by
  obtain ⟨w, hw, hwy⟩ := hβ (subset_tsupport _ hy)
  obtain ⟨φ, hs, ht⟩ := A.X.π_eq_π_iff.1 hwy
  exact ⟨φ, hs ▸ hw, ht⟩

/-! ### The data of §14.5 for the objects of §14.3 -/

variable {T : BoundaryStructuredTuple A} {P : P5Nbhds T} {E : CorrExtension T P}
  {Q : P5Nbhds.P6Nbhds P}

namespace ZConcrete

variable (C : ZConcrete E Q)

/-- The properties of the cut-offs `β_a` of Lemma 14.5.1 for the `V̂_a` of Proposition 14.3.8,
with `B = ∂X`. -/
def BetaSpec (β : A.Obj → A.Obj → ℝ) : Prop :=
  (∀ a, A.X.PObj.IsScSmoothMap realPolyfold (β a)) ∧
  (∀ a (φ : A.Mor), β a (A.X.tgt φ) = β a (A.X.src φ)) ∧
  (∀ a ∈ C.Aset, tsupport (β a) ⊆ A.X.saturation (C.Vh a)) ∧
  (∀ y, ∃ O : Set A.Obj, IsOpen O ∧ y ∈ O ∧ A.X.IsSaturated O ∧
    {a | a ∈ C.Aset ∧ ∃ z ∈ O, β a z ≠ 0}.Finite) ∧
  (∀ y ∈ A.X.PObj.boundary, ∑ᶠ a ∈ C.Aset, β a y = 1)

/-- **Lemma 14.5.1** for the cover `(V̂_a)_{a ∈ A}` of `∂X` (Proposition 14.3.8); `β_a = 0` for
`a ∉ A`. -/
theorem exists_betaSpec (hpu : A.X.HasScPartitionsOfUnity) : ∃ β, C.BetaSpec β := by
  classical
  have hcov : A.X.PObj.boundary ⊆ ⋃ a ∈ C.Aset, A.X.saturation (C.Vh a) := by
    intro y hy
    obtain ⟨a, ha, hya⟩ := mem_iUnion₂.1 (C.cover (mem_image_of_mem _ hy))
    exact mem_iUnion₂.2 ⟨a, ha, hya⟩
  obtain ⟨β, hsm, -, hinv, hsupp, hlf, hsum⟩ := A.X.lemma_14_5_1 hpu A.X.PObj.isClosed_boundary
    isSaturated_boundary_gl C.A_subset C.isOpen_Vh hcov
  refine ⟨fun a => if a ∈ C.Aset then β a else fun _ => 0, fun a => ?_, fun a φ => ?_,
    fun a ha => ?_, fun y => ?_, fun y hy => ?_⟩
  · by_cases ha : a ∈ C.Aset
    · simp only [if_pos ha]; exact hsm a ha
    · simp only [if_neg ha]; exact isScSmoothMap_real_const 0
  · by_cases ha : a ∈ C.Aset
    · simp only [if_pos ha]; exact (hinv a φ).symm
    · simp only [if_neg ha]
  · simp only [if_pos ha]; exact hsupp a ha
  · obtain ⟨O, hOo, hOs, hyO, hfin⟩ := hlf y
    refine ⟨O, hOo, hyO, hOs, hfin.subset ?_⟩
    rintro a ⟨ha, z, hz, hne⟩
    simp only [if_pos ha] at hne
    exact ⟨ha, z, hz, hne⟩
  · rw [← hsum y hy]
    refine finsum_mem_congr rfl fun a ha => ?_
    simp only [if_pos ha]

variable (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧
    x ∈ c.φ.source) (hpu : A.X.PObj.AdmitsScPartitionsOfUnity)

include hB hpu in
open scoped Classical in
/-- The local extensions `ŝᵃ` of Proposition 14.4.14 (zero for `a ∉ A`). -/
def shA6 (a : A.Obj) : C.toZData.I a → A.Obj → A.W :=
  if ha : a ∈ C.Aset then (C.proposition_14_4_14 hB hpu ha).choose else fun _ => fiberZero A.P

include hB hpu in
theorem shA6_spec {a : A.Obj} (ha : a ∈ C.Aset) :
    C.shA6 hB hpu a = (C.proposition_14_4_14 hB hpu ha).choose := by
  classical
  unfold shA6
  exact dif_pos ha

variable {β : A.Obj → A.Obj → ℝ} (hβ : C.BetaSpec β)

/-- **GL's `TransportInput`** for the objects of §14.3: `Ũ(a)`, `V̂_a`, `τ̂` (Z5's `toZData`),
the boundary sections of `T`, the cut-offs of Lemma 14.5.1, and `ŝᵃ` of Proposition 14.4.14. -/
def transportInput_a6 : TransportInput A C.toZData.toZSetup where
  isOpen_V := C.isOpen_Vh
  proper a ha := isProper a (C.A_subset ha)
  locallyConstant a ha b hb φ hφ :=
    (C.toZData.locallyConstant a ha b hb φ hφ.1 hφ.2).filter_mono nhdsWithin_le_nhds
  β := β
  isScSmooth_β := hβ.1
  β_tgt := hβ.2.1
  closure_support_β a ha :=
    closure_support_subset_a6 (Q.nbhdObj a) (C.toZData.V_subset a ha) (C.mapsTo_Vh a ha)
      (hβ.2.2.1 a ha)
  s0 := C.toZSections.s
  s0_compat a ha b hb φ hφ :=
    IndexCorr.sat_of_pairs_t9 _ fun i j hp =>
      C.toZSections.compat a ha b hb φ hφ.1 hφ.2.1 i j hp
  sh := C.shA6 hB hpu
  isScPlusSectionOn_sh a ha i := by
    rw [C.shA6_spec hB hpu ha]
    exact (C.proposition_14_4_14 hB hpu ha).choose_spec.1 i
  sh_equivariant a ha g i y hy := by
    rw [C.shA6_spec hB hpu ha]
    exact (C.proposition_14_4_14 hB hpu ha).choose_spec.2.1 g i y hy
  sh_boundary a ha i y hy := by
    rw [C.shA6_spec hB hpu ha]
    exact (C.proposition_14_4_14 hB hpu ha).choose_spec.2.2.1 i y hy
  sh_zRel a ha z hz i i' h := by
    rw [C.shA6_spec hB hpu ha]
    exact (C.proposition_14_4_14 hB hpu ha).choose_spec.2.2.2 z hz i i' h

/-! #### The bi-action -/

theorem Γ_eq_a6 {a : A.Obj} (ha : a ∈ A.X.PObj.boundary) (g : A.X.Isotropy a) (w : A.Obj) :
    (Q.nbhdObj a).rep.Γ g w =
      (P.nbhd (bdryRetr_z5 C.x₀ a)).rep.Γ (isoRetr_z5 C.x₀ a g) w := by
  rw [(rep_isoRetr_z5 C.x₀ P.nbhd ha g w).1, Q.nbhdObj_of_mem ha, Q.rep_eq]

theorem Φ_eq_a6 {a : A.Obj} (ha : a ∈ A.X.PObj.boundary) (g : A.X.Isotropy a) (w : A.Obj) :
    (Q.nbhdObj a).rep.Φ g w =
      (P.nbhd (bdryRetr_z5 C.x₀ a)).rep.Φ (isoRetr_z5 C.x₀ a g) w := by
  rw [(rep_isoRetr_z5 C.x₀ P.nbhd ha g w).2, Q.nbhdObj_of_mem ha, Q.rep_eq]

theorem biact_eq_a6 {b b' : A.Obj} (hb : b ∈ A.X.PObj.boundary) (hb' : b' ∈ A.X.PObj.boundary)
    (g' : A.X.Isotropy b') (φ : A.Mor) (g : A.X.Isotropy b) :
    EpGroupoid.biact (Q.nbhdObj b) (Q.nbhdObj b') g' φ g =
      P.biact (bdryRetr_z5 C.x₀ b) (bdryRetr_z5 C.x₀ b') (isoRetr_z5 C.x₀ b' g') φ
        (isoRetr_z5 C.x₀ b g) := by
  change EpGroupoid.biact _ _ _ _ _ = EpGroupoid.biact _ _ _ _ _
  unfold EpGroupoid.biact
  rw [C.Γ_eq_a6 hb', C.Γ_eq_a6 hb, C.Φ_eq_a6 hb, map_inv]

theorem biact_τ_a6 {b b' : A.Obj} (hb : b ∈ C.Aset) (hb' : b' ∈ C.Aset) {φ : A.Mor}
    (hφ : φ ∈ A.X.morBetween (C.Vh b) (C.Vh b')) (g' : A.X.Isotropy b') (g : A.X.Isotropy b) :
    C.toZData.τ b b' (EpGroupoid.biact (C.toZData.nbhd b) (C.toZData.nbhd b') g' φ g) =
      IndexCorr.biact g' (C.toZData.τ b b' φ) g := by
  have hO : φ ∈ E.Ot (bdryRetr_z5 C.x₀ b) (bdryRetr_z5 C.x₀ b') :=
    E.Ohat_subset_Ot _ _ (C.morBetween_subset_Ohat hb hb' hφ)
  have e₁ := C.biact_eq_a6 (C.A_subset hb) (C.A_subset hb') g' φ g
  have e₂ := E.tauHat_biact hO (isoRetr_z5 C.x₀ b' g') (isoRetr_z5 C.x₀ b g)
  have e₃ := IndexCorr.biact_compHom_gl (isoRetr_z5 C.x₀ b) (isoRetr_z5 C.x₀ b')
    (E.tauHat (bdryRetr_z5 C.x₀ b) (bdryRetr_z5 C.x₀ b') φ) g' g
  change E.tauHat _ _ (EpGroupoid.biact (Q.nbhdObj b) (Q.nbhdObj b') g' φ g) = _
  rw [e₁, e₂]
  exact e₃.symm

/-- **T9's `AssemblyInput`** for the objects of §14.3, the tuple `T` and the cut-offs `β`, when
`T.Λ` charges every fibre over `∂X`. -/
def assemblyInput_a6 (hch : ChargesBoundary T.Λ) : AssemblyInput A T.Λ where
  S := C.toZData.toZSetup
  T := C.transportInput_a6 hB hpu hβ
  suppInSat a ha y hy := exists_mor_of_ne_zero_a6 (hβ.2.2.1 a ha) hy
  locFin := hβ.2.2.2.1
  sum_one := hβ.2.2.2.2
  nonempty_I b _ := T.nonempty_I_a6 hch _
  finite_τ b hb b' hb' :=
    (E.finite_tauHat _ _).subset (image_mono (C.morBetween_subset_Ohat hb hb'))
  biact_τ b hb b' hb' φ hφ g' g := C.biact_τ_a6 hb hb' hφ g' g
  rep b hb w hw := by
    have hmem : A.P w ∈ (T.dec.𝒰.nbhd (bdryRetr_z5 C.x₀ b)).bdry :=
      C.mem_bdry hb ⟨C.toZData.V_subset b hb hw.1, hw.2⟩
    rw [(T.dec.S (bdryRetr_z5 C.x₀ b)).rep w hmem]
    rfl
  functor φ w hw hs := by
    rw [fibAct_of hw]
    exact T.isBoundaryScPlusMultisection.1 ⟨(φ, w), hw⟩ hs

end ZConcrete

/-- **The data of §§14.3–14.5 exist** for a structurable `Λ` over `∂X` that charges every
boundary fibre: the tuple with (P4) (Proposition 14.2.3), the objects of Proposition 14.3.8
(Z5's `exists_zConcrete_of_hasP4`), Proposition 14.4.14 (Z5) and Lemma 14.5.1 (B2) give T9's
`AssemblyInput`.  For `∂X = ∅`, T9's `emptyAssemblyInput`. -/
theorem exists_assemblyInput_a6 (hX : A.X.IsTame) (hpara : A.X.HasParacompactOrbitSpace)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity)
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧
      x ∈ c.φ.source)
    {Λ : A.W → ℚ≥0} (hΛ : IsBoundaryStructurable A Λ) (hch : ChargesBoundary Λ) :
    Nonempty (AssemblyInput A Λ) := by
  rcases eq_empty_or_nonempty A.X.PObj.boundary with hb | ⟨x₀, hx₀⟩
  · exact ⟨emptyAssemblyInput hb Λ⟩
  obtain ⟨T₀, rfl⟩ := isBoundaryStructurable_iff.1 hΛ
  obtain ⟨T, -, hTΛ, -, hT⟩ := BoundaryStructuredTuple.proposition_14_2_3 hX T₀
  obtain ⟨P, E, Q, ⟨C⟩⟩ := exists_zConcrete_of_hasP4 hT hpara ⟨x₀, hx₀⟩
  obtain ⟨β, hβ⟩ := C.exists_betaSpec (A.X.theorem_7_5_7 hpara hpu)
  rw [← hTΛ] at hch ⊢
  exact ⟨C.assemblyInput_a6 hB hpu hβ hch⟩

end SBLocalization

end Polyfold
