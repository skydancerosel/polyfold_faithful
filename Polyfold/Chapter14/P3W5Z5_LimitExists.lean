import Polyfold.Chapter14.P3W5Z5_LimitLoops

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 14,
§14.4, pp. 661–667: **Proposition 14.4.6 (2)** (2017 text: Proposition 14.5 (2)) and its
consequences **Lemma 14.4.9 (3)**, **Proposition 14.4.10**, the existence of coherent
neighbourhood systems (Definition 14.4.11) and **Proposition 14.4.14** for the data of §14.4,
without the hypothesis `HasThetaLocalEq`.

## What is formalized

* `ZLimitSetting.exists_limitRep`: the finite natural representation of the proof of
  Proposition 14.4.6 (2) at every `z₀ ∈ cl_X(V̂_a) ∩ ∂X` (the text's steps: local finiteness gives
  the finite `o`; `⋃_{b ∈ o} cl_X(V̂_b)` is proper, so finitely many of its objects are isomorphic
  to `z₀` (Lemma 7.1.11); Lemma 14.4.7 on them, with the `O(y)` small; properness gives the
  neighbourhood `W` of `z₀`).
* **Proposition 14.4.6 (2)**: `sections_eq_of_theta_closure` (for every `z₀ ∈ cl_X(V̂_a) ∩ ∂X`),
  `hasThetaLocalEq_of_limit`, `proposition_14_4_6_2_of_limit` (as printed).
* Unconditional forms of Z4's and LX's results: `lemma_14_4_9_3_of_limit`,
  `proposition_14_4_10_of_limit`, `exists_zCoherentNbhdSystem_of_limit`,
  `coherentNbhdSystem_of_limit`, `proposition_14_4_14_of_limit`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}} {S : A.X.ZData}

namespace ZLimitSetting

variable (L : ZLimitSetting S)

/-- At a boundary point `y ∈ cl_X(V̂_b)`: a neighbourhood inside `Ũ(b)` all of whose morphisms
into `cl_X(Ũ(c))` lie in `Ô_{b,c}` (properness of `cl_X(Ũ(c))`). -/
theorem exists_nbhd_near {y b c : A.Obj} (hb : b ∈ S.A) (hc : c ∈ S.A)
    (hyb : y ∈ A.X.PObj.boundary) (hy : y ∈ closure (S.V b)) :
    ∃ O : Set A.Obj, IsOpen O ∧ y ∈ O ∧ O ⊆ (S.nbhd b).U ∧
      ∀ φ, A.X.src φ ∈ O → A.X.tgt φ ∈ closure (S.nbhd c).U → φ ∈ L.M b c := by
  have hyU : y ∈ (S.nbhd b).U := S.closure_V_subset b hb hy
  obtain ⟨W, hWo, hyW, hW⟩ := EpGroupoid.exists_nhds_of_isProperSubset (X := A.X)
    (L.isProper c hc) (L.isOpen_M b hb c hc) (y := y) fun φ hφs hφt =>
      L.boundary_mem_M b hb c hc φ ⟨by rw [hφs]; exact hyU, by rw [hφs]; exact hyb⟩
        ⟨hφt, (tgt_mem_boundary_iff_z4 φ).2 (by rw [hφs]; exact hyb)⟩
  exact ⟨W ∩ (S.nbhd b).U, hWo.inter (S.nbhd b).isOpen_U, ⟨hyW, hyU⟩, inter_subset_right,
    fun φ hφ hφt => hW φ hφ.1 hφt⟩

/-- The neighbourhoods `O(y, b, c)` used to shrink Lemma 14.4.7's `O(y)`. -/
theorem exists_nbhd_yb (y b c : A.Obj) : ∃ O : Set A.Obj, IsOpen O ∧ y ∈ O ∧
    (b ∈ S.A → c ∈ S.A → y ∈ A.X.PObj.boundary → y ∈ closure (S.V b) →
      O ⊆ (S.nbhd b).U ∧ ∀ φ, A.X.src φ ∈ O → A.X.tgt φ ∈ closure (S.nbhd c).U → φ ∈ L.M b c) ∧
    (y ∉ closure (S.V b) → Disjoint O (closure (S.V b))) := by
  by_cases h : b ∈ S.A ∧ c ∈ S.A ∧ y ∈ A.X.PObj.boundary ∧ y ∈ closure (S.V b)
  · obtain ⟨O, hOo, hyO, hOU, hOM⟩ := L.exists_nbhd_near h.1 h.2.1 h.2.2.1 h.2.2.2
    exact ⟨O, hOo, hyO, fun _ _ _ _ => ⟨hOU, hOM⟩, fun hn => absurd h.2.2.2 hn⟩
  · by_cases hy : y ∈ closure (S.V b)
    · exact ⟨univ, isOpen_univ, mem_univ _, fun hb hc hyb hy' => absurd ⟨hb, hc, hyb, hy'⟩ h,
        fun hn => absurd hy hn⟩
    · exact ⟨(closure (S.V b))ᶜ, isClosed_closure.isOpen_compl, hy,
        fun _ _ _ hy' => absurd hy' hy, fun _ => disjoint_compl_left⟩

/-- **The finite natural representation of the proof of Proposition 14.4.6 (2) exists** at
every `z₀ ∈ cl_X(V̂_a) ∩ ∂X`. -/
theorem exists_limitRep {z₀ : A.Obj} (hz₀b : z₀ ∈ A.X.PObj.boundary) {a : A.Obj}
    (ha : a ∈ S.A) (hz₀ : z₀ ∈ closure (S.V a)) : Nonempty (ZLimitRep L z₀) := by
  classical
  -- the finite set `o` (local finiteness)
  obtain ⟨𝒩, h𝒩, hfin⟩ := L.locallyFinite (A.X.π z₀)
  obtain ⟨𝒪, h𝒪𝒩, h𝒪o, hz𝒪⟩ := mem_nhds_iff.1 h𝒩
  let o : Set A.Obj := Subtype.val '' {b : S.A | (A.X.π '' S.V b ∩ 𝒩).Nonempty}
  have ho_fin : o.Finite := hfin.image _
  have hoA : o ⊆ S.A := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hmem_o : ∀ c ∈ S.A, ∀ x ∈ S.V c, A.X.π x ∈ 𝒪 → c ∈ o := fun c hc x hx hx𝒪 =>
    ⟨⟨c, hc⟩, ⟨A.X.π x, ⟨x, hx, rfl⟩, h𝒪𝒩 hx𝒪⟩, rfl⟩
  have h𝒪' : A.X.π ⁻¹' 𝒪 ∈ 𝓝 z₀ := (h𝒪o.preimage A.X.continuous_π).mem_nhds hz𝒪
  have hao : a ∈ o := by
    obtain ⟨x, hx𝒪, hxV⟩ := mem_closure_iff_nhds.1 hz₀ _ h𝒪'
    exact hmem_o a ha x hxV hx𝒪
  -- the proper set `K = ⋃_{b ∈ o} cl_X(V̂_b)`
  let K : Set A.Obj := ⋃ b ∈ o, closure (S.V b)
  have hKprop : A.X.IsProperSubset K := EpGroupoid.isProperSubset_biUnion (X := A.X) ho_fin
    fun b hb => (L.isProper b (hoA hb)).of_subset (closure_mono (S.V_subset b (hoA hb)))
      isClosed_closure
  have hKcl : IsClosed K := hKprop.isClosed
  -- the finite set `Y` of objects of `K` isomorphic to `z₀` (Lemma 7.1.11)
  have hMfin : {ψ | A.X.src ψ = z₀ ∧ A.X.tgt ψ ∈ K}.Finite := by
    have hK' : IsProperMap ((A.X.src ⁻¹' closure K).domRestrict A.X.tgt) := by
      rw [hKcl.closure_eq]; exact hKprop
    have := A.X.lemma_7_1_11_of_isProperMap hK' z₀
    rwa [hKcl.closure_eq] at this
  let Y : Finset A.Obj := (hMfin.image A.X.tgt).toFinset
  have hmemY : ∀ y, y ∈ Y ↔ ∃ ψ, (A.X.src ψ = z₀ ∧ A.X.tgt ψ ∈ K) ∧ A.X.tgt ψ = y :=
    fun y => by simp only [Y, Set.Finite.mem_toFinset]; rfl
  have hz₀Y : z₀ ∈ Y := (hmemY z₀).2 ⟨A.X.unit z₀,
    ⟨A.X.src_unit z₀, by rw [A.X.tgt_unit]; exact mem_biUnion hao hz₀⟩, A.X.tgt_unit z₀⟩
  have hYb : ∀ y ∈ Y, y ∈ A.X.PObj.boundary := by
    intro y hy
    obtain ⟨ψ, ⟨hψs, -⟩, rfl⟩ := (hmemY y).1 hy
    exact (tgt_mem_boundary_iff_z4 ψ).2 (by rw [hψs]; exact hz₀b)
  have hYiso : ∀ y ∈ Y, ∀ y' ∈ Y, A.X.Isomorphic y y' := by
    intro y hy y' hy'
    obtain ⟨ψ, ⟨hψs, -⟩, rfl⟩ := (hmemY y).1 hy
    obtain ⟨ψ', ⟨hψ's, -⟩, rfl⟩ := (hmemY y').1 hy'
    have h : A.X.src ψ' = A.X.tgt (A.X.inv ψ) := by rw [A.X.tgt_inv, hψs, hψ's]
    exact ⟨A.X.comp ψ' (A.X.inv ψ), by rw [A.X.src_comp _ _ h, A.X.src_inv],
      A.X.tgt_comp _ _ h⟩
  -- the neighbourhoods `Q(y)` and Lemma 14.4.7
  choose On hOno hOnm hOnear hOfar using L.exists_nbhd_yb
  let Q : A.Obj → Set A.Obj := fun y => ⋂ b ∈ o, ⋂ c ∈ o, On y b c
  have hQo : ∀ y ∈ Y, IsOpen (Q y) := fun y _ =>
    ho_fin.isOpen_biInter fun b _ => ho_fin.isOpen_biInter fun c _ => hOno y b c
  have hQm : ∀ y ∈ Y, y ∈ Q y := fun y _ =>
    mem_iInter₂.2 fun b _ => mem_iInter₂.2 fun c _ => hOnm y b c
  have hQsub : ∀ y b c, b ∈ o → c ∈ o → Q y ⊆ On y b c := fun y b c hb hc x hx =>
    mem_iInter₂.1 (mem_iInter₂.1 hx b hb) c hc
  obtain ⟨N, hNQ, -⟩ := A.X.exists_naturalRepFinite_subset Y hYiso Q hQo hQm
  -- the neighbourhood `W` of `z₀` (properness of `K`)
  have hSo : IsOpen (A.X.tgt ⁻¹' ⋃ y ∈ Y, N.U y) :=
    (isOpen_biUnion fun y hy => N.isOpen_U y hy).preimage A.X.continuous_tgt
  obtain ⟨W₁, hW₁o, hz₀W₁, hW₁⟩ := EpGroupoid.exists_nhds_of_isProperSubset (X := A.X) hKprop
    hSo (y := z₀) fun φ hφs hφt =>
      mem_biUnion ((hmemY _).2 ⟨φ, ⟨hφs, hφt⟩, rfl⟩) (N.mem_U _ ((hmemY _).2 ⟨φ, ⟨hφs, hφt⟩, rfl⟩))
  have hWtgt : ∀ φ, A.X.src φ ∈ W₁ ∩ A.X.π ⁻¹' 𝒪 ∩ N.U z₀ → ∀ c ∈ S.A, A.X.tgt φ ∈ S.V c →
      c ∈ o ∧ A.X.tgt φ ∈ ⋃ y ∈ Y, N.U y := by
    intro φ hφ c hc hφc
    have hco : c ∈ o := hmem_o c hc _ hφc (by rw [← A.X.π_src_eq_π_tgt]; exact hφ.1.2)
    exact ⟨hco, hW₁ φ hφ.1.1 (mem_biUnion hco (subset_closure hφc))⟩
  exact ⟨ZLimitRep.mk o hoA Y hz₀Y hYb (⋃ y ∈ Y, Q y) N (W₁ ∩ A.X.π ⁻¹' 𝒪 ∩ N.U z₀)
    (inter_mem (inter_mem (hW₁o.mem_nhds hz₀W₁) h𝒪')
      ((N.isOpen_U z₀ hz₀Y).mem_nhds (N.mem_U z₀ hz₀Y)))
    (fun _ h => h.2) hWtgt
    (fun y hy b hb hn => (hOfar y b b hn).mono_left ((hNQ y hy).trans (hQsub y b b hb hb)))
    (fun y hy b hb hyb => ⟨((hNQ y hy).trans (hQsub y b b hb hb)).trans
        (hOnear y b b (hoA hb) (hoA hb) (hYb y hy) hyb).1,
      fun c hc φ hφ hφt => (hOnear y b c (hoA hb) (hoA hc) (hYb y hy) hyb).2 φ
        ((hQsub y b c hb hc) ((hNQ y hy) hφ)) hφt⟩)⟩

end ZLimitSetting

/-! ### Proposition 14.4.6 (2) -/

variable (D : ZSections A S)

/-- **Proposition 14.4.6 (2), p. 661 (2017: Proposition 14.5 (2)), for every
`z₀ ∈ cl_X(V̂_a) ∩ ∂X`**: if `(i, i') ∈ Θ_{z₀}` (there are `z_k ∈ V̂_a`, `z_k → z₀`, with
`i ∼_{z_k} i'`), then `s^{0a}_i = s^{0a}_{i'}` on a neighbourhood of `z₀` in `∂X`. -/
theorem sections_eq_of_theta_closure (L : ZLimitSetting S) (hD : D.CompatNbhd) {a : A.Obj}
    (ha : a ∈ S.A) {z₀ : A.Obj}
    (hz₀ : z₀ ∈ closure (S.V a) ∩ A.X.PObj.boundary) {i i' : S.I a} (h : S.Theta a z₀ i i') :
    ∀ᶠ y in 𝓝 z₀, y ∈ A.X.PObj.boundary → D.s a i y = D.s a i' y := by
  obtain ⟨R⟩ := L.exists_limitRep hz₀.2 ha hz₀.1
  filter_upwards [(R.N.isOpen_U z₀ R.mem_Y).mem_nhds (R.N.mem_U z₀ R.mem_Y)] with y hy hyb
  exact R.sections_eq D hD ha hz₀.1 h y ⟨hy, hyb⟩

/-- **Proposition 14.4.6 (2) in the form `HasThetaLocalEq`** (`z_k ∈ V̂_a`, the form
Lemma 14.4.9 (3) uses), from the facts of §14.3 (`ZLimitSetting`) and Definition 14.1.7 (4)
(`CompatNbhd`). -/
theorem hasThetaLocalEq_of_limit (L : ZLimitSetting S) (hD : D.CompatNbhd) :
    HasThetaLocalEq D := by
  intro a ha z₀ hz₀ i i' h
  have hz₀' : z₀ ∈ closure (S.V a) ∩ A.X.PObj.boundary :=
    ⟨closure_mono inter_subset_left hz₀,
      closure_minimal inter_subset_right A.X.PObj.isClosed_boundary hz₀⟩
  filter_upwards [sections_eq_of_theta_closure D L hD ha hz₀' h] with y hy hy'
  exact hy hy'.2

/-- **Proposition 14.4.6 (2), p. 661 (2017: Proposition 14.5 (2)), as printed**. -/
theorem proposition_14_4_6_2_of_limit (L : ZLimitSetting S) (hD : D.CompatNbhd) :
    proposition_14_4_6_2_statement D :=
  (hasThetaLocalEq_of_limit D L hD).proposition_14_4_6_2

/-- **Lemma 14.4.9 (3), p. 663 (2017: Lemma 14.8 (3))**: for `z ∈ cl_X(V̂_a) ∩ ∂X` (in particular
for `z ∈ cl_X(V_a)`) and `i ≈_z i'`, `s^{0a}_i = s^{0a}_{i'}` on a neighbourhood of `z` in `∂X`. -/
theorem lemma_14_4_9_3_of_limit (L : ZLimitSetting S) (hD : D.CompatNbhd) {a z : A.Obj}
    (ha : a ∈ S.A)
    (hz : z ∈ closure (S.V a) ∩ A.X.PObj.boundary) {i i' : S.I a} (h : S.Approx a z i i') :
    ∀ᶠ y in 𝓝 z, y ∈ A.X.PObj.boundary → D.s a i y = D.s a i' y := by
  induction h with
  | refl => exact Eventually.of_forall fun _ _ => rfl
  | tail _ hbc ih =>
    filter_upwards [ih, sections_eq_of_theta_closure D L hD ha hz hbc] with y h₁ h₂ hy using
      (h₁ hy).trans (h₂ hy)

/-- **Proposition 14.4.10, p. 664 (2017: Proposition 14.6)**, for the data of §14.4 (no added
hypothesis beyond the facts of §14.3 and Definition 14.1.7 (4)). -/
theorem proposition_14_4_10_of_limit (L : ZLimitSetting S) (hD : D.CompatNbhd) {a : A.Obj}
    (ha : a ∈ S.A) :
    ∃ O : A.Obj → Set A.Obj, ∀ z ∈ closure (S.V a), IsOpen (O z) ∧ z ∈ O z ∧
      O z ⊆ (S.nbhd a).U ∧
      (∀ g, O ((S.nbhd a).rep.Φ g z) = (S.nbhd a).rep.Φ g '' O z) ∧
      (∀ g, (S.nbhd a).rep.Φ g z ≠ z → Disjoint (O z) (O ((S.nbhd a).rep.Φ g z))) ∧
      (∀ i, ∀ y ∈ O z ∩ S.V a, S.zClass a y i ⊆ S.approxClass a z i) ∧
      (z ∈ closure (S.V a ∩ A.X.PObj.boundary) → ∀ i i', S.Approx a z i i' →
        ∀ y ∈ O z ∩ ((S.nbhd a).U ∩ A.X.PObj.boundary), D.s a i y = D.s a i' y) :=
  proposition_14_4_10_hyp D (hasThetaLocalEq_of_limit D L hD) ha

/-- **Coherent neighbourhood systems exist** (Definition 14.4.11, p. 664, "in view of
Proposition 14.4.10"). -/
theorem exists_zCoherentNbhdSystem_of_limit (L : ZLimitSetting S) (hD : D.CompatNbhd) {a : A.Obj}
    (ha : a ∈ S.A) :
    Nonempty (ZCoherentNbhdSystem D a) :=
  exists_zCoherentNbhdSystem_hyp D (hasThetaLocalEq_of_limit D L hD) ha

/-- **A coherent neighbourhood system in LX's form** (for Proposition 14.4.14). -/
theorem coherentNbhdSystem_of_limit (L : ZLimitSetting S) (hD : D.CompatNbhd) {a : A.Obj}
    (ha : a ∈ S.A)
    (hface : ∀ i, IsFaceScPlusSectionOn A (D.s a i) (S.nbhd a).bdry) :
    ∃ C : CoherentNbhdSystem (D.toLocalExtensionBase ha hface), C.IsEquivariant :=
  coherentNbhdSystem_hyp D (hasThetaLocalEq_of_limit D L hD) ha hface

/-- **Proposition 14.4.14, pp. 667–671 (2017: Proposition 14.7)**, for the data of §14.4, without
`HasThetaLocalEq`: sc⁺-sections `ŝᵃᵢ` on `V̂_a`, symmetric, equal to `s⁰ᵃᵢ` on `V_a`, and
equal for `i ∼_z i'`. -/
theorem proposition_14_4_14_of_limit (L : ZLimitSetting S)
    (hB : ∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source)
    (hpu : A.X.PObj.AdmitsScPartitionsOfUnity) (hD : D.CompatNbhd) {a : A.Obj} (ha : a ∈ S.A)
    (hface : ∀ i, IsFaceScPlusSectionOn A (D.s a i) (S.nbhd a).bdry) :
    ∃ sh : S.I a → A.Obj → A.W, (∀ i, IsScPlusSectionOn A (sh i) (S.V a)) ∧
      (∀ (g : A.X.Isotropy a) i, ∀ y ∈ S.V a,
        sh (g • i) ((S.nbhd a).rep.Φ g y) = fibAct ((S.nbhd a).rep.Γ g y) (sh i y)) ∧
      (∀ i, ∀ y ∈ S.V a ∩ A.X.PObj.boundary, sh i y = D.s a i y) ∧
      ∀ y ∈ S.V a, ∀ i i', S.ZRel a y i i' → sh i y = sh i' y :=
  proposition_14_4_14_of_hyp hB hpu D (hasThetaLocalEq_of_limit D L hD) ha hface

end SBLocalization

end Polyfold
