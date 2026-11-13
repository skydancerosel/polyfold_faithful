import Polyfold.Chapter14.P3W4Z4_Theta
import Polyfold.Chapter14.P3W3B1_BoundaryMultisection

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 14,
§14.4, pp. 661–667: **Proposition 14.4.6 (2)**, **Lemma 14.4.9 (3)**, **Proposition 14.4.10**,
**Definition 14.4.11** (coherent neighbourhood systems) and **Lemma 14.4.13**
(2017 text: Proposition 14.5 (2), Lemma 14.8 (3), Proposition 14.6, Definition 14.9,
Lemma 14.9).

# The boundary sections along z-loops, and coherent neighbourhood systems

## The text, paraphrased

The boundary data are the sections `s^{0a}_i` of `W|U'(a)`, `i ∈ I_a`, with (14.45)
`s^a_{g(i)}(g ∗ y) = μ(Γ(g, y), s^a_i(y))`, related along boundary morphisms by the
correspondences (Definition 14.1.7 (4)), which `τ̂` extends.
(Proposition 14.4.6 (2)) If `z_k ∈ V_a = V̂_a ∩ ∂X`, `z_k → z₀ ∈ cl_X(V_a)` and `i ∼_{z_k} i'`,
then `s^{0a}_i = s^{0a}_{i'}` on a neighbourhood of `z₀` in `∂X`.
(Lemma 14.4.9 (3)) If `z ∈ cl_X(V_a)` and `i ≈_z i'`, then `s^{0a}_i = s^{0a}_{i'}` near `z`.
(Proposition 14.4.10) Every `z ∈ cl_X(V̂_a)` has an open `Õ(z)` with (1) `Õ(z) ⊆ Ũ(a)`,
(2) `Õ(g ∗ z) = g ∗ Õ(z)` and `Õ(z) ∩ Õ(g ∗ z) = ∅` if `z ≠ g ∗ z`, (3) `[i]_{∼_y} ⊆ [i]_{≈_z}`
for `y ∈ Õ(z) ∩ V̂_a`, (4) for `z ∈ cl_X(V_a)`, `s^{0a}_i = s^{0a}_{i'}` on `Õ(z) ∩ U(a)` when
`i ≈_z i'`.  (Definition 14.4.11) A coherent neighbourhood system is such a family (with (3)
asked for `z ∈ V̂_a`).  (Lemma 14.4.13) For `z' ∈ cl_X(V̂_a) ∩ ∂X`: (1) the stabiliser
`G_a(z')` permutes the `≈_{z'}`-classes; (2), (3) the sections satisfy the equivariance identity
on `Õ(z') ∩ ∂X`; (4) the sections over `Õ(z'') ∩ ∂X`, `z'' ∈ [z']`, are determined by those over
`Õ(z') ∩ ∂X`.

## What is formalized

* `ZSections A S`: the sections `s^{0a}_i : Obj → W` over a `ZData` on the base of a strong
  bundle `A`, with `P ∘ s^{0a}_i = id`, (14.45) on `U(a) = Ũ(a) ∩ ∂X`, and Definition 14.1.7 (4)
  for `τ̂` along the morphisms of `V̂_{a,a'}` with source in `∂X` (there `τ̂ = τ⁰`).
  Witness: `ZSections.zero` (zero sections over `ZData.trivial`).
* `ZSections.arc_transport`: along a chain with an arc starting in `∂X`,
  `s^b_j(t(φ)) = μ(φ, s^a_i(s(φ)))` for the composite `φ`.  Hence `i ∼_z i'` gives
  `s^{0a}_i(z) = s^{0a}_{i'}(z)` for `z ∈ V_a` (`zRel_sections_eq`) and, with Proposition
  14.4.6 (1), on a neighbourhood of `z` in `∂X` (`proposition_14_4_6_2_of_mem`).
* Proposition 14.4.6 (2) in general (`z₀` in the closure, outside `V̂_a`) is stated as the `Prop`
  `proposition_14_4_6_2_statement` (the printed form, `z_k ∈ V_a`) and `HasThetaLocalEq` (the form
  with `z_k ∈ V̂_a`, which Lemma 14.4.9 (3) uses); `HasThetaLocalEq` implies the printed form.
  Their proof (the limit loop through the closures, Lemma 14.4.7 and properness) is the gap.
* `lemma_14_4_9_3_hyp`, `proposition_14_4_10_hyp` (from `HasThetaLocalEq`),
  `ZCoherentNbhdSystem` (Definition 14.4.11), `exists_zCoherentNbhdSystem_hyp`, and
  `lemma_14_4_13_1`, `lemma_14_4_13_2`, `lemma_14_4_13_3`, `lemma_14_4_13_4`,
  `ZCoherentNbhdSystem.disjoint_orbit` (the disjoint union `Õ([z])`) on any coherent system.
  `hasThetaLocalEq_zero` shows the hypothesis is satisfiable.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-- `∂X` is saturated: `t(φ) ∈ ∂X` iff `s(φ) ∈ ∂X` (the degeneracy index is invariant). -/
theorem tgt_mem_boundary_iff_z4 (φ : A.Mor) :
    A.X.tgt φ ∈ A.X.PObj.boundary ↔ A.X.src φ ∈ A.X.PObj.boundary := by
  change 1 ≤ A.X.PObj.degIndex (A.X.tgt φ) ↔ 1 ≤ A.X.PObj.degIndex (A.X.src φ)
  rw [← A.X.degIndex_tgt, A.X.degIndex_src]

/-- **The boundary data of §14.4** (p. 665): sections `s^{0a}_i`, `i ∈ I_a`, with
`P(s^{0a}_i(y)) = y` and (14.45) on `U(a) = Ũ(a) ∩ ∂X`, and Definition 14.1.7 (4) for the
extension `τ̂`: `s^{a'}_j(t(φ)) = μ(φ, s^a_i(s(φ)))` when `(i, j)` is a pair of
`τ̂_{a,a'}(φ)` and `φ ∈ V̂_{a,a'}` has source in `∂X` (there `τ̂ = τ⁰`, `V̂_{a,a'} ∩ 𝐗|∂X ⊆
U⁰(a, a')`). -/
structure ZSections (A : SEP.{u}) (S : A.X.ZData) where
  /-- The sections `s^{0a}_i`. -/
  s : ∀ a, S.I a → A.Obj → A.W
  P_s : ∀ a ∈ S.A, ∀ i, ∀ y ∈ (S.nbhd a).U ∩ A.X.PObj.boundary, A.P (s a i y) = y
  /-- (14.45) -/
  equivariant : ∀ a ∈ S.A, ∀ (g : A.X.Isotropy a) (i : S.I a),
    ∀ y ∈ (S.nbhd a).U ∩ A.X.PObj.boundary,
      s a (g • i) ((S.nbhd a).rep.Φ g y) = fibAct ((S.nbhd a).rep.Γ g y) (s a i y)
  /-- Definition 14.1.7 (4), for `τ̂`. -/
  compat : ∀ a ∈ S.A, ∀ a' ∈ S.A, ∀ φ, A.X.src φ ∈ S.V a ∩ A.X.PObj.boundary →
    A.X.tgt φ ∈ S.V a' → ∀ i j, (S.τ a a' φ).Pairs i j →
      s a' j (A.X.tgt φ) = fibAct φ (s a i (A.X.src φ))

namespace ZSections

variable {S : A.X.ZData} (D : ZSections A S)

/-- **Transport along chains**: for a chain with an arc from `i ∈ I_a` to `j ∈ I_b` whose
composite `φ` starts in `∂X`, `s^b_j(t(φ)) = μ(φ, s^a_i(s(φ)))`. -/
theorem arc_transport {a b : A.Obj} {i : S.I a} {j : S.I b} {φ : A.Mor}
    (h : S.Arc a b i j φ) (hφ : A.X.src φ ∈ A.X.PObj.boundary) :
    D.s b j (A.X.tgt φ) = fibAct φ (D.s a i (A.X.src φ)) := by
  induction h with
  | @nil ha z hz i =>
    rw [A.X.src_unit] at hφ ⊢
    rw [A.X.tgt_unit]
    exact (fibAct_unit_p3w3 (D.P_s a ha i z ⟨S.V_subset a ha hz, hφ⟩)).symm
  | @snoc b c i j k φ ψ h hc hs ht hp ih =>
    have hsφ : A.X.src φ ∈ A.X.PObj.boundary := by rwa [A.X.src_comp _ _ hs] at hφ
    have hpr := h.props
    have htφ : A.X.tgt φ ∈ A.X.PObj.boundary := (tgt_mem_boundary_iff_z4 φ).2 hsφ
    have e₁ := ih hsφ
    have e₂ := D.compat b hpr.2.1 c hc ψ ⟨by rw [hs]; exact hpr.2.2.2, by rw [hs]; exact htφ⟩
      ht j k hp
    rw [A.X.tgt_comp _ _ hs, A.X.src_comp _ _ hs, e₂, hs, e₁,
      fibAct_comp_p3w3 (D.P_s a hpr.1 i _ ⟨S.V_subset a hpr.1 hpr.2.2.1, hsφ⟩) hs]

/-- `i ∼_z i'` with `z ∈ V_a = V̂_a ∩ ∂X` gives `s^{0a}_i(z) = s^{0a}_{i'}(z)`. -/
theorem zRel_sections_eq {a z : A.Obj} {i i' : S.I a} (h : S.ZRel a z i i')
    (hz : z ∈ A.X.PObj.boundary) : D.s a i z = D.s a i' z := by
  have e := D.arc_transport h (by rw [A.X.src_unit]; exact hz)
  rw [A.X.tgt_unit, A.X.src_unit] at e
  have ha := (ZSetup.Arc.props h).1
  rw [e, fibAct_unit_p3w3 (D.P_s a ha i z ⟨S.V_subset a ha h.mem_V, hz⟩)]

/-- **Proposition 14.4.6 (2) at points of `V_a`, p. 661**: if `z₀ ∈ V_a = V̂_a ∩ ∂X` and
`i ∼_{z₀} i'`, then `s^{0a}_i = s^{0a}_{i'}` on a neighbourhood of `z₀` in `∂X` (by
Proposition 14.4.6 (1) and transport along the loops). -/
theorem proposition_14_4_6_2_of_mem {a z₀ : A.Obj} {i i' : S.I a} (h : S.ZRel a z₀ i i') :
    ∀ᶠ y in 𝓝 z₀, y ∈ A.X.PObj.boundary → D.s a i y = D.s a i' y := by
  filter_upwards [S.proposition_14_4_6_1 h] with y hy hyb using D.zRel_sections_eq hy hyb

end ZSections

/-! ### Proposition 14.4.6 (2) and Lemma 14.4.9 (3) -/

/-- **Proposition 14.4.6 (2), p. 661 (2017: Proposition 14.5 (2)), as printed**: for
`z_k ∈ V_a = V̂_a ∩ ∂X` with `i ∼_{z_k} i'` and `z_k → z₀ ∈ cl_X(V_a)` (read as
`z₀ ∈ cl{y ∈ V_a | i ∼_y i'}`), `s^{0a}_i = s^{0a}_{i'}` on a neighbourhood of `z₀` in `U(a)`. -/
def proposition_14_4_6_2_statement {S : A.X.ZData} (D : ZSections A S) : Prop :=
  ∀ a ∈ S.A, ∀ (z₀ : A.Obj) (i i' : S.I a),
    z₀ ∈ closure {y | y ∈ A.X.PObj.boundary ∧ S.ZRel a y i i'} →
      ∀ᶠ y in 𝓝 z₀, y ∈ (S.nbhd a).U ∩ A.X.PObj.boundary → D.s a i y = D.s a i' y

/-- **Proposition 14.4.6 (2) with `z_k ∈ V̂_a`**, the form used by Lemma 14.4.9 (3) (whose
`Θ_z` takes `z_k ∈ V̂_a`): for `(i, i') ∈ Θ_{z₀}` with `z₀ ∈ cl_X(V_a)`, `s^{0a}_i = s^{0a}_{i'}`
near `z₀` in `U(a)`.  The text's proof of (2) (the limit `z₀`-loop) applies to this form. -/
def HasThetaLocalEq {S : A.X.ZData} (D : ZSections A S) : Prop :=
  ∀ a ∈ S.A, ∀ z₀ ∈ closure (S.V a ∩ A.X.PObj.boundary), ∀ (i i' : S.I a), S.Theta a z₀ i i' →
    ∀ᶠ y in 𝓝 z₀, y ∈ (S.nbhd a).U ∩ A.X.PObj.boundary → D.s a i y = D.s a i' y

/-- The form with `z_k ∈ V̂_a` implies the printed form. -/
theorem HasThetaLocalEq.proposition_14_4_6_2 {S : A.X.ZData} {D : ZSections A S}
    (h : HasThetaLocalEq D) : proposition_14_4_6_2_statement D := by
  intro a ha z₀ i i' hz₀
  refine h a ha z₀ (closure_mono (t := S.V a ∩ A.X.PObj.boundary)
    (fun _ hy => ⟨ZSetup.ZRel.mem_V hy.2, hy.1⟩) hz₀) i i'
    (closure_mono (t := {y | S.ZRel a y i i'}) (fun _ hy => hy.2) hz₀)

/-- **Lemma 14.4.9 (3), p. 663 (2017: Lemma 14.8 (3))**, from Proposition 14.4.6 (2) in the form
`HasThetaLocalEq`: if `z ∈ cl_X(V_a)` and `i ≈_z i'`, then `s^{0a}_i = s^{0a}_{i'}` on `U(a)` near
`z`. -/
theorem lemma_14_4_9_3_hyp {S : A.X.ZData} {D : ZSections A S} (hP : HasThetaLocalEq D)
    {a z : A.Obj} (ha : a ∈ S.A) (hz : z ∈ closure (S.V a ∩ A.X.PObj.boundary)) {i i' : S.I a}
    (h : S.Approx a z i i') :
    ∀ᶠ y in 𝓝 z, y ∈ (S.nbhd a).U ∩ A.X.PObj.boundary → D.s a i y = D.s a i' y := by
  induction h with
  | refl => exact Eventually.of_forall fun _ _ => rfl
  | tail _ hbc ih =>
    filter_upwards [ih, hP a ha z hz _ _ hbc] with y h₁ h₂ hy using (h₁ hy).trans (h₂ hy)

/-! ### Proposition 14.4.10 -/

section Coherent

variable {S : A.X.ZData} (D : ZSections A S)

theorem Φ_mem_boundary_z4 {a : A.Obj} (g : A.X.Isotropy a) {y : A.Obj}
    (hy : y ∈ (S.nbhd a).U) (hyb : y ∈ A.X.PObj.boundary) :
    (S.nbhd a).rep.Φ g y ∈ A.X.PObj.boundary := by
  rw [← (S.nbhd a).tgt_Γ g hy, tgt_mem_boundary_iff_z4, (S.nbhd a).src_Γ g hy]
  exact hyb

theorem mem_boundary_of_Φ_z4 {a : A.Obj} (g : A.X.Isotropy a) {y : A.Obj}
    (hy : y ∈ (S.nbhd a).U) (hyb : (S.nbhd a).rep.Φ g y ∈ A.X.PObj.boundary) :
    y ∈ A.X.PObj.boundary := by
  have := Φ_mem_boundary_z4 (S := S) g⁻¹ ((S.nbhd a).mapsTo_Φ g hy) hyb
  rwa [(S.nbhd a).Φ_inv_Φ g hy] at this

/-- The natural action maps `cl_X(V̂_a)` and `cl_X(V_a)` into themselves. -/
theorem mapsTo_Φ_closure_z4 {a : A.Obj} (ha : a ∈ S.A) (g : A.X.Isotropy a) {E : Set A.Obj}
    (hE : E ⊆ S.V a) (hEg : MapsTo ((S.nbhd a).rep.Φ g) E E) :
    MapsTo ((S.nbhd a).rep.Φ g) (closure E) (closure E) := fun _ hz =>
  closure_mono hEg.image_subset (mem_closure_image ((S.nbhd a).continuousAt_Φ g
    (S.closure_V_subset a ha (closure_mono hE hz))) hz)

theorem mapsTo_Φ_Vb_z4 {a : A.Obj} (ha : a ∈ S.A) (g : A.X.Isotropy a) :
    MapsTo ((S.nbhd a).rep.Φ g) (S.V a ∩ A.X.PObj.boundary) (S.V a ∩ A.X.PObj.boundary) :=
  fun _ hy => ⟨S.mapsTo_V a ha g hy.1, Φ_mem_boundary_z4 g (S.V_subset a ha hy.1) hy.2⟩

/-- **Proposition 14.4.10, p. 664 (2017: Proposition 14.6)**, from Proposition 14.4.6 (2) in the
form `HasThetaLocalEq`: for `a ∈ A` there are open `Õ(z) ∋ z`, `z ∈ cl_X(V̂_a)`, with
(1) `Õ(z) ⊆ Ũ(a)`; (2) `Õ(g ∗ z) = g ∗ Õ(z)`, and `Õ(z) ∩ Õ(g ∗ z) = ∅` if `g ∗ z ≠ z`;
(3) `[i]_{∼_y} ⊆ [i]_{≈_z}` for `y ∈ Õ(z) ∩ V̂_a`; (4) for `z ∈ cl_X(V_a)` and `i ≈_z i'`,
`s^{0a}_i = s^{0a}_{i'}` on `Õ(z) ∩ U(a)`. -/
theorem proposition_14_4_10_hyp (hP : HasThetaLocalEq D) {a : A.Obj} (ha : a ∈ S.A) :
    ∃ O : A.Obj → Set A.Obj, ∀ z ∈ closure (S.V a), IsOpen (O z) ∧ z ∈ O z ∧
      O z ⊆ (S.nbhd a).U ∧
      (∀ g, O ((S.nbhd a).rep.Φ g z) = (S.nbhd a).rep.Φ g '' O z) ∧
      (∀ g, (S.nbhd a).rep.Φ g z ≠ z → Disjoint (O z) (O ((S.nbhd a).rep.Φ g z))) ∧
      (∀ i, ∀ y ∈ O z ∩ S.V a, S.zClass a y i ⊆ S.approxClass a z i) ∧
      (z ∈ closure (S.V a ∩ A.X.PObj.boundary) → ∀ i i', S.Approx a z i i' →
        ∀ y ∈ O z ∩ ((S.nbhd a).U ∩ A.X.PObj.boundary), D.s a i y = D.s a i' y) := by
  set N := S.nbhd a
  let P : A.Obj → Set A.Obj → Prop := fun z O =>
    (∀ i, ∀ y ∈ O ∩ S.V a, S.zClass a y i ⊆ S.approxClass a z i) ∧
    (z ∈ closure (S.V a ∩ A.X.PObj.boundary) → ∀ i i', S.Approx a z i i' →
      ∀ y ∈ O ∩ (N.U ∩ A.X.PObj.boundary), D.s a i y = D.s a i' y)
  have hmono : ∀ z O O', P z O → O' ⊆ O → P z O' := fun z O O' h hO =>
    ⟨fun i y hy => h.1 i y ⟨hO hy.1, hy.2⟩,
      fun hz i i' hii y hy => h.2 hz i i' hii y ⟨hO hy.1, hy.2⟩⟩
  have hequiv : ∀ g z O, z ∈ closure (S.V a) → O ⊆ N.U → P z O →
      P (N.rep.Φ g z) (N.rep.Φ g '' O) := by
    intro g z O hzC hOU h
    have hzU : z ∈ N.U := S.closure_V_subset a ha hzC
    refine ⟨?_, ?_⟩
    · rintro i _ ⟨⟨y, hyO, rfl⟩, hyV'⟩ i'' hi''
      have hyU := hOU hyO
      have hyV : y ∈ S.V a := by
        have := S.mapsTo_V a ha g⁻¹ hyV'
        rwa [N.Φ_inv_Φ g hyU] at this
      have h₁ : S.ZRel a y (g⁻¹ • i'') (g⁻¹ • i) := by
        rw [S.lemma_14_4_5 ha hyV g, smul_inv_smul, smul_inv_smul]
        exact hi''
      have h₂ := ZData.lemma_14_4_9_2 (h.1 (g⁻¹ • i) y ⟨hyO, hyV⟩ h₁) g
      rwa [smul_inv_smul, smul_inv_smul] at h₂
    · rintro hgz i i' happ _ ⟨⟨y, hyO, rfl⟩, -, hyb'⟩
      have hyU := hOU hyO
      have hyb := mem_boundary_of_Φ_z4 (S := S) g hyU hyb'
      have hz : z ∈ closure (S.V a ∩ A.X.PObj.boundary) := by
        have := mapsTo_Φ_closure_z4 ha g⁻¹ inter_subset_left (mapsTo_Φ_Vb_z4 ha g⁻¹) hgz
        rwa [N.Φ_inv_Φ g hzU] at this
      have happ' : S.Approx a z (g⁻¹ • i) (g⁻¹ • i') := by
        have := ZData.lemma_14_4_9_2 happ g⁻¹
        rwa [N.Φ_inv_Φ g hzU] at this
      have heq := h.2 hz _ _ happ' y ⟨hyO, hyU, hyb⟩
      calc D.s a i (N.rep.Φ g y) = D.s a (g • g⁻¹ • i) (N.rep.Φ g y) := by rw [smul_inv_smul]
        _ = fibAct (N.rep.Γ g y) (D.s a (g⁻¹ • i) y) := D.equivariant a ha g _ y ⟨hyU, hyb⟩
        _ = fibAct (N.rep.Γ g y) (D.s a (g⁻¹ • i') y) := by rw [heq]
        _ = D.s a i' (N.rep.Φ g y) := by
          rw [← D.equivariant a ha g _ y ⟨hyU, hyb⟩, smul_inv_smul]
  have hex : ∀ z ∈ closure (S.V a), ∃ O, IsOpen O ∧ z ∈ O ∧ P z O := by
    intro z hzC
    obtain ⟨Q, hQo, hzQ, -, hQ⟩ := ZData.lemma_14_4_9_4_all ha hzC
    have h4 : ∀ᶠ y in 𝓝 z, z ∈ closure (S.V a ∩ A.X.PObj.boundary) → ∀ i i',
        S.Approx a z i i' → y ∈ N.U ∩ A.X.PObj.boundary → D.s a i y = D.s a i' y := by
      by_cases hz : z ∈ closure (S.V a ∩ A.X.PObj.boundary)
      · have : ∀ i i', ∀ᶠ y in 𝓝 z, S.Approx a z i i' →
            y ∈ N.U ∩ A.X.PObj.boundary → D.s a i y = D.s a i' y := by
          intro i i'
          by_cases happ : S.Approx a z i i'
          · filter_upwards [lemma_14_4_9_3_hyp hP ha hz happ] with y hy using fun _ => hy
          · exact Eventually.of_forall fun _ h => absurd h happ
        filter_upwards [eventually_all.2 fun i => eventually_all.2 (this i)] with y hy
        exact fun _ i i' => hy i i'
      · exact Eventually.of_forall fun _ h => absurd h hz
    obtain ⟨Q', hQ'sub, hQ'o, hzQ'⟩ := mem_nhds_iff.1 h4
    exact ⟨Q ∩ Q', hQo.inter hQ'o, ⟨hzQ, hzQ'⟩, fun i y hy => hQ y ⟨hy.2, hy.1.1⟩ i,
      fun hz i i' happ y hy => hQ'sub hy.1.2 hz i i' happ hy.2⟩
  obtain ⟨O, hO⟩ := N.exists_equivariant_nbhds (S.closure_V_subset a ha)
    (fun g => mapsTo_Φ_closure_z4 ha g subset_rfl (S.mapsTo_V a ha g)) P hmono hequiv hex
  refine ⟨O, fun z hz => ?_⟩
  obtain ⟨h₁, h₂, h₃, ⟨h₄, h₅⟩, h₆, h₇⟩ := hO z hz
  exact ⟨h₁, h₂, h₃, h₆, h₇, h₄, h₅⟩

/-! ### Definition 14.4.11 -/

/-- **Definition 14.4.11, p. 664 (2017: Definition 14.9)**: a coherent neighbourhood system for
`cl_X(V̂_a) ⊆ Ũ(a)`: open `Õ(z) ∋ z`, `z ∈ cl_X(V̂_a)`, with (1) `Õ(z) ⊆ Ũ(a)`;
(2) `Õ(g ∗ z) = g ∗ Õ(z)` and `Õ(z) ∩ Õ(g ∗ z) = ∅` if `z ≠ g ∗ z`; (3) for `z ∈ V̂_a`,
`[i]_{∼_y} ⊆ [i]_{≈_z}` for `y ∈ Õ(z) ∩ V̂_a`; (4) for `z ∈ cl_X(V_a)`,
`s^{0a}_i = s^{0a}_{i'}` on `Õ(z) ∩ U(a)` when `i ≈_z i'`. -/
structure ZCoherentNbhdSystem (a : A.Obj) where
  /-- The neighbourhoods `Õ(z)`. -/
  O : A.Obj → Set A.Obj
  isOpen : ∀ z ∈ closure (S.V a), IsOpen (O z)
  mem : ∀ z ∈ closure (S.V a), z ∈ O z
  /-- (1) -/
  subset : ∀ z ∈ closure (S.V a), O z ⊆ (S.nbhd a).U
  /-- (2) -/
  equivariant : ∀ z ∈ closure (S.V a), ∀ g,
    O ((S.nbhd a).rep.Φ g z) = (S.nbhd a).rep.Φ g '' O z
  /-- (2) -/
  disjoint : ∀ z ∈ closure (S.V a), ∀ g, (S.nbhd a).rep.Φ g z ≠ z →
    Disjoint (O z) (O ((S.nbhd a).rep.Φ g z))
  /-- (3) -/
  zClass_subset : ∀ z ∈ S.V a, ∀ i, ∀ y ∈ O z ∩ S.V a, S.zClass a y i ⊆ S.approxClass a z i
  /-- (4) -/
  sections_eq : ∀ z ∈ closure (S.V a ∩ A.X.PObj.boundary), ∀ i i', S.Approx a z i i' →
    ∀ y ∈ O z ∩ ((S.nbhd a).U ∩ A.X.PObj.boundary), D.s a i y = D.s a i' y

/-- **Existence of coherent neighbourhood systems** (p. 665, "in view of Proposition 14.4.10"),
from Proposition 14.4.6 (2) in the form `HasThetaLocalEq`. -/
theorem exists_zCoherentNbhdSystem_hyp (hP : HasThetaLocalEq D) {a : A.Obj} (ha : a ∈ S.A) :
    Nonempty (ZCoherentNbhdSystem D a) := by
  obtain ⟨O, hO⟩ := proposition_14_4_10_hyp D hP ha
  exact ⟨⟨O, fun z hz => (hO z hz).1, fun z hz => (hO z hz).2.1, fun z hz => (hO z hz).2.2.1,
    fun z hz => (hO z hz).2.2.2.1, fun z hz => (hO z hz).2.2.2.2.1,
    fun z hz => (hO z (subset_closure hz)).2.2.2.2.2.1,
    fun z hz => (hO z (closure_mono inter_subset_left hz)).2.2.2.2.2.2 hz⟩⟩

/-! ### Lemma 14.4.13 -/

/-- The `≈_z`-classes partition `I_a`: two classes are equal or disjoint. -/
theorem approxClass_eq_or_disjoint {a z : A.Obj} (i j : S.I a) :
    S.approxClass a z i = S.approxClass a z j ∨
      Disjoint (S.approxClass a z i) (S.approxClass a z j) := by
  have E := ZData.approx_equivalence (S := S) (a := a) (z := z)
  by_cases h : S.Approx a z i j
  · left
    ext k
    exact ⟨fun hk => E.trans hk h, fun hk => E.trans hk (E.symm h)⟩
  · right
    rw [Set.disjoint_left]
    exact fun k hki hkj => h (E.trans (E.symm hki) hkj)

/-- **Lemma 14.4.13 (1), p. 666 (2017: Lemma 14.9 (1))**: an element `g` of the stabiliser
`G_a(z')` maps the class `[i]_{≈_{z'}}` onto `[g(i)]_{≈_{z'}}`, so it permutes the classes (which
are equal or disjoint, `approxClass_eq_or_disjoint`). -/
theorem lemma_14_4_13_1 {a z' : A.Obj} (ha : a ∈ S.A) (hz' : z' ∈ closure (S.V a))
    {g : A.X.Isotropy a} (hg : (S.nbhd a).rep.Φ g z' = z') (i : S.I a) :
    (g • ·) '' S.approxClass a z' i = S.approxClass a z' (g • i) := by
  have := ZData.lemma_14_4_9_2_class ha hz' g i
  rw [hg] at this
  exact this.symm

variable {D}

/-- **Lemma 14.4.13 (2), p. 666**: for `z' ∈ cl_X(V_a)` and `g ∈ G_a(z')` fixing the class
`[i]_{≈_{z'}}`, `s^{0a}_i(g ∗ y) = μ(Γ(g, y), s^{0a}_i(y))` for `y ∈ Õ(z') ∩ ∂X`. -/
theorem lemma_14_4_13_2 (C : ZCoherentNbhdSystem D a) (ha : a ∈ S.A)
    {z' : A.Obj} (hz' : z' ∈ closure (S.V a ∩ A.X.PObj.boundary))
    {g : A.X.Isotropy a} (hg : (S.nbhd a).rep.Φ g z' = z') {i : S.I a}
    (hgi : (g • ·) '' S.approxClass a z' i = S.approxClass a z' i) :
    ∀ y ∈ C.O z' ∩ A.X.PObj.boundary,
      D.s a i ((S.nbhd a).rep.Φ g y) = fibAct ((S.nbhd a).rep.Γ g y) (D.s a i y) := by
  intro y ⟨hyO, hyb⟩
  have hz'C : z' ∈ closure (S.V a) := closure_mono inter_subset_left hz'
  have hyU := C.subset z' hz'C hyO
  have hgy : (S.nbhd a).rep.Φ g y ∈ C.O z' := by
    have := C.equivariant z' hz'C g
    rw [hg] at this
    rw [this]
    exact ⟨y, hyO, rfl⟩
  have hgi' : S.Approx a z' (g • i) i := by
    have : g • i ∈ (g • ·) '' S.approxClass a z' i :=
      ⟨i, Relation.ReflTransGen.refl, rfl⟩
    rw [hgi] at this
    exact this
  have e := C.sections_eq z' hz' _ _ hgi' _ ⟨hgy, (S.nbhd a).mapsTo_Φ g hyU,
    Φ_mem_boundary_z4 g hyU hyb⟩
  rw [← e]
  exact D.equivariant a ha g i y ⟨hyU, hyb⟩

/-- **Lemma 14.4.13 (3), p. 666**: for `g ∈ G_a(z')` and every `i`,
`s^{0a}_{g(i)}(g ∗ y) = μ(Γ(g, y), s^{0a}_i(y))` for `y ∈ Õ(z') ∩ ∂X` (this is (14.45) on
`Õ(z') ∩ ∂X ⊆ U(a)`; it relates the class `[i]` to `g([i]) = [g(i)]` when they differ). -/
theorem lemma_14_4_13_3 (C : ZCoherentNbhdSystem D a) (ha : a ∈ S.A)
    {z' : A.Obj} (hz' : z' ∈ closure (S.V a)) (g : A.X.Isotropy a) (i : S.I a) :
    ∀ y ∈ C.O z' ∩ A.X.PObj.boundary,
      D.s a (g • i) ((S.nbhd a).rep.Φ g y) = fibAct ((S.nbhd a).rep.Γ g y) (D.s a i y) :=
  fun y hy => D.equivariant a ha g i y ⟨C.subset z' hz' hy.1, hy.2⟩

/-- **The sections `s^{z'}_j` of the proof of Lemma 14.4.13 (4)**: on `Õ(z') ∩ ∂X`,
`z' ∈ cl_X(V_a)`, the section `s^{0a}_{i'}` does not depend on `i'` in a `≈_{z'}`-class. -/
theorem lemma_14_4_13_classSection (C : ZCoherentNbhdSystem D a)
    {z' : A.Obj} (hz' : z' ∈ closure (S.V a ∩ A.X.PObj.boundary)) {i i' : S.I a}
    (hi : i' ∈ S.approxClass a z' i) :
    ∀ y ∈ C.O z' ∩ A.X.PObj.boundary, D.s a i' y = D.s a i y := fun y hy =>
  C.sections_eq z' hz' i' i hi y ⟨hy.1,
    C.subset z' (closure_mono inter_subset_left hz') hy.1, hy.2⟩

/-- **Lemma 14.4.13 (4), p. 666**: for `z'' = g ∗ z'` the sections over `Õ(z'') ∩ ∂X` are
determined by those over `Õ(z') ∩ ∂X`: every point of `Õ(z'') ∩ ∂X` is `g ∗ y` with
`y ∈ Õ(z') ∩ ∂X`, and there `s^{0a}_{g(i)}(g ∗ y) = μ(Γ(g, y), s^{0a}_i(y))`. -/
theorem lemma_14_4_13_4 (C : ZCoherentNbhdSystem D a) (ha : a ∈ S.A)
    {z' : A.Obj} (hz' : z' ∈ closure (S.V a)) (g : A.X.Isotropy a) :
    ∀ y'' ∈ C.O ((S.nbhd a).rep.Φ g z') ∩ A.X.PObj.boundary,
      ∃ y ∈ C.O z' ∩ A.X.PObj.boundary, y'' = (S.nbhd a).rep.Φ g y ∧
        ∀ i, D.s a (g • i) y'' = fibAct ((S.nbhd a).rep.Γ g y) (D.s a i y) := by
  rintro y'' ⟨hy'', hb''⟩
  rw [C.equivariant z' hz' g] at hy''
  obtain ⟨y, hyO, rfl⟩ := hy''
  have hyU := C.subset z' hz' hyO
  have hyb := mem_boundary_of_Φ_z4 (S := S) g hyU hb''
  exact ⟨y, ⟨hyO, hyb⟩, rfl, fun i => lemma_14_4_13_3 C ha hz' g i y ⟨hyO, hyb⟩⟩

/-- **`Õ([z])` is a disjoint union** (Lemma 14.4.13, display): `Õ(z₁) ∩ Õ(z₂) = ∅` for distinct
points `z₁, z₂ = g ∗ z₁` of one `G_a`-orbit. -/
theorem ZCoherentNbhdSystem.disjoint_orbit (C : ZCoherentNbhdSystem D a) {z : A.Obj}
    (hz : z ∈ closure (S.V a)) (g : A.X.Isotropy a) (hne : (S.nbhd a).rep.Φ g z ≠ z) :
    Disjoint (C.O z) (C.O ((S.nbhd a).rep.Φ g z)) :=
  C.disjoint z hz g hne

end Coherent

/-! ### Satisfiability -/

/-- **The boundary data are satisfiable**: zero sections over `ZData.trivial`. -/
def ZSections.zero (A : SEP.{u}) : ZSections A (ZData.trivial A.X) where
  s _ _ y := fiberZero A.P y
  P_s _ _ _ _ _ := proj_fiberZero A.P _
  equivariant a _ g _ _ hy :=
    (fibAct_fiberZero (((ZData.trivial A.X).nbhd a).src_Γ g hy.1)
      (((ZData.trivial A.X).nbhd a).tgt_Γ g hy.1)).symm
  compat _ _ _ _ _ _ _ _ _ _ := (fibAct_fiberZero rfl rfl).symm

/-- `HasThetaLocalEq` holds for the zero data (so the hypothesis of `proposition_14_4_10_hyp`
and `exists_zCoherentNbhdSystem_hyp` is satisfiable); there a coherent system exists. -/
theorem hasThetaLocalEq_zero (A : SEP.{u}) : HasThetaLocalEq (ZSections.zero A) :=
  fun _ _ _ _ _ _ _ => Eventually.of_forall fun _ _ => rfl

theorem exists_zCoherentNbhdSystem_zero (A : SEP.{u}) (a : A.Obj) :
    Nonempty (ZCoherentNbhdSystem (ZSections.zero A) a) :=
  exists_zCoherentNbhdSystem_hyp _ (hasThetaLocalEq_zero A) (mem_univ a)

end SBLocalization

end Polyfold
