import Polyfold.Chapter14.P3W4GL_Transport
import Polyfold.Chapter14.P3W4GL_Criterion
import Polyfold.Chapter13.P3W3Q_Commensurable

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.5, pp. 672–677:
**Proposition 14.5.4** (the transport of the local extensions) (2017: Proposition 14.8), proved.

# The transported section structures

## The text, paraphrased

Fix `a ∈ A`.  The sections `β_a·ŝᵃᵢ` on `V̂_a` (Proposition 14.4.14 and Lemma 14.5.1) are carried
along the morphisms from `V̂_a` to every `V̂_b`: for `y ∈ V̂_b` and `φ : x → y` with `x ∈ V̂_a`, and
`i` paired with `j` by `τ̂_{a,b}(φ)`, `s̃ᵃ_{b,j}(y) = μ(φ, β_a(x)·ŝᵃᵢ(x))`, and `0` if no such `φ`
exists.  Well defined by the z-loops of §14.4 and Proposition 14.4.14 (2); sc⁺ by the properness of
`cl(Ũ(a))` and (14.53).

## What is formalized (namespace `Polyfold.SBLocalization.TransportInput`)

* `TransportInput.SuppInSat T`: Lemma 14.5.1 (1) for the cut-offs of `T`, `β_a ≠ 0` only on
  `π⁻¹(π(V̂_a))` (GL's `TransportInput` records (14.53) but not this part of Lemma 14.5.1).
* `tsec a b j`: the transported section `s̃ᵃ_{b,j}`, defined through the chains with arcs of
  Definitions 14.4.2–14.4.3 (`ZSetup.Arc`), which makes the equivariance and (4) immediate:
  `tsec a b j (t φ) = μ(φ, β_a·ŝᵃᵢ(s φ))` for every `Arc a b i j φ` (`tsec_of_arc`; the
  independence of the arc is `fibAct_bsec_eq`, the text's z-loop argument), `0` if there is none.
* **`proposition_14_5_4`**: `proposition_14_5_4_statement T` (GL's statement) from `SuppInSat`.
* `suppInSat_of_zero`: the hypothesis `SuppInSat` holds for `β ≡ 0` (witness).

## Reading

* The arc form of the definition agrees with the text's one-step form (`tsec_of_pairs`): every
  `φ` from `V̂_a` to `V̂_b` with `(i, j)` a pair of `τ̂_{a,b}(φ)` is a chain of length one.
* sc⁺ near a point `y₀` that is the target of a morphism from `V̂_a`: a local inverse `τ` of `t`
  near such a morphism `φ₀`, `τ̂_{a,b}` constant near `φ₀`, so the section is
  `z ↦ μ(τ(z), β_a·ŝᵃᵢ(s τ(z)))` (C's `transportSection`).  Near the other points the section
  vanishes, since `t(s⁻¹(K))`, `K = cl{β_a ≠ 0} ∩ …`, is closed (properness) and avoids them.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid EpGroupoid.ZSetup

variable {A : SEP.{u}}

/-! ### Pairs of correspondences -/

namespace IndexCorr

variable {α β : Type u}

/-- Every `j` has a partner: the right leg of a representative is surjective. -/
theorem exists_pairs_left_t9 (τ : IndexCorr α β) (j : β) : ∃ i, τ.Pairs i j :=
  ind (p := fun τ => ∃ i, τ.Pairs i j) (fun d => by
    obtain ⟨k, hk⟩ := d.surjective_b j
    exact ⟨d.a k, k, rfl, hk⟩) τ

/-- A relation holding on all pairs holds for the correspondence. -/
theorem sat_of_pairs_t9 {R : α → β → Prop} (τ : IndexCorr α β)
    (h : ∀ i j, τ.Pairs i j → R i j) : τ.Sat R :=
  ind (p := fun τ => (∀ i j, τ.Pairs i j → R i j) → τ.Sat R)
    (fun _ h k => h _ _ ⟨k, rfl, rfl⟩) τ h

/-- A relation satisfied by the correspondence holds on its pairs. -/
theorem rel_of_sat_t9 {R : α → β → Prop} {τ : IndexCorr α β} (h : τ.Sat R) {i : α} {j : β}
    (hp : τ.Pairs i j) : R i j :=
  ind (p := fun τ => τ.Sat R → τ.Pairs i j → R i j)
    (fun _ h ⟨k, h1, h2⟩ => h1 ▸ h2 ▸ h k) τ h hp

end IndexCorr

/-! ### Pointwise facts on `β·s` -/

theorem sectionSmul_congr_t9 {c : A.Obj → ℝ} {f f' : A.Obj → A.W} {y : A.Obj}
    (h : f y = f' y) :
    Polyfold.sectionSmul A.P c f y = Polyfold.sectionSmul A.P c f' y := by
  unfold Polyfold.sectionSmul
  by_cases hP : A.P (f y) = y
  · have hP' : A.P (f' y) = y := h ▸ hP
    rw [dif_pos hP, dif_pos hP']
    have e : (⟨f y, hP⟩ : A.P ⁻¹' {y}) = ⟨f' y, hP'⟩ := Subtype.ext h
    rw [e]
  · have hP' : ¬ A.P (f' y) = y := h ▸ hP
    rw [dif_neg hP, dif_neg hP', h]

theorem sectionSmul_of_eq_zero_t9 {c : A.Obj → ℝ} {f : A.Obj → A.W} {y : A.Obj}
    (hf : A.P (f y) = y) (hc : c y = 0) :
    Polyfold.sectionSmul A.P c f y = fiberZero A.P y := by
  unfold Polyfold.sectionSmul
  rw [dif_pos hf, hc, zero_smul]
  rfl

/-- `∂X` is saturated (the degree index is invariant along morphisms). -/
theorem src_mem_boundary_t9 {φ : A.Mor} (h : A.X.tgt φ ∈ A.X.PObj.boundary) :
    A.X.src φ ∈ A.X.PObj.boundary := by
  change 1 ≤ A.X.PObj.degIndex (A.X.tgt φ) at h
  change 1 ≤ A.X.PObj.degIndex (A.X.src φ)
  rw [← A.X.degIndex_src]
  rwa [← A.X.degIndex_tgt] at h

namespace TransportInput

variable {S : A.X.ZSetup} (T : TransportInput A S)

/-- **Lemma 14.5.1 (1) for the cut-offs of `T`**: `β_a(y) ≠ 0` only if `y` is isomorphic to a
point of `V̂_a` (`supp β_a ⊆ π⁻¹(π(V̂_a))`). -/
def SuppInSat : Prop :=
  ∀ a ∈ S.A, ∀ y, T.β a y ≠ 0 → ∃ φ, A.X.src φ ∈ S.V a ∧ A.X.tgt φ = y

/-! ### The sections `β_a·ŝᵃᵢ` -/

/-- `β_a·ŝᵃᵢ`, as a global section (`ŝᵃᵢ` extended by `0` off `V̂_a`). -/
def bsec (a : A.Obj) (i : S.I a) : A.Obj → A.W :=
  Polyfold.sectionSmul A.P (T.β a) (extendZero (S.V a) (T.sh a i))

theorem isSection_bsec (a : A.Obj) (i : S.I a) : IsSection A.P (T.bsec a i) :=
  (isSection_extendZero _ _).sectionSmul

theorem bsec_eq {a : A.Obj} (ha : a ∈ S.A) (i : S.I a) {y : A.Obj} (hy : y ∈ S.V a) :
    T.bsec a i y = Polyfold.sectionSmul A.P (T.β a) (T.sh a i) y :=
  sectionSmul_congr_t9 (extendZero_eqOn (T.isScPlusSectionOn_sh a ha i).1 hy).symm

theorem bsec_of_eq_zero (a : A.Obj) (i : S.I a) {y : A.Obj} (h : T.β a y = 0) :
    T.bsec a i y = fiberZero A.P y :=
  sectionSmul_of_eq_zero_t9 (isSection_extendZero _ _ y) h

theorem isScPlusSectionOn_bsec {a : A.Obj} (ha : a ∈ S.A) (i : S.I a) :
    IsScPlusSectionOn A (T.bsec a i) (S.V a) :=
  (T.isScPlusSectionOn_sh a ha i).extendZero.sectionSmul (T.isOpen_V a ha)
    (isSection_extendZero _ _) (T.isScSmooth_β a)

/-! ### Independence of the arc (the z-loop argument) -/

/-- **Well-definedness** (the text's z-loop argument): two arcs from `V̂_a` ending at the same
`(y, j)` give the same transported value.  The arcs close up, after a step `Γ(g⁻¹, ·)` inside
`V̂_a`, to a z-loop, so Proposition 14.4.14 (2) and the equivariance of `ŝᵃ` apply. -/
theorem fibAct_bsec_eq {a b : A.Obj} {i i' : S.I a} {j : S.I b} {φ φ' : A.Mor}
    (h₁ : S.Arc a b i j φ) (h₂ : S.Arc a b i' j φ') (e : A.X.tgt φ' = A.X.tgt φ) :
    fibAct φ' (T.bsec a i' (A.X.src φ')) = fibAct φ (T.bsec a i (A.X.src φ)) := by
  obtain ⟨ha, -, hs₁, -⟩ := h₁.props
  obtain ⟨-, -, hs₂, -⟩ := h₂.props
  have hc : A.X.src (A.X.inv φ) = A.X.tgt φ' := by rw [A.X.src_inv, e]
  have h₃ := h₂.trans h₁.symm hc
  have hsψ : A.X.src (A.X.comp (A.X.inv φ) φ') = A.X.src φ' := A.X.src_comp _ _ hc
  have htψ : A.X.tgt (A.X.comp (A.X.inv φ) φ') = A.X.src φ := by
    rw [A.X.tgt_comp _ _ hc, A.X.tgt_inv]
  have hzU : A.X.src φ' ∈ (S.nbhd a).U := S.V_subset a ha hs₂
  have hwU : A.X.src φ ∈ (S.nbhd a).U := S.V_subset a ha hs₁
  obtain ⟨g, hg⟩ := (S.nbhd a).exists_Γ_eq (by rw [hsψ]; exact hzU) (by rw [htψ]; exact hwU)
  rw [hsψ] at hg
  have hΦ : (S.nbhd a).rep.Φ g (A.X.src φ') = A.X.src φ := by
    rw [← (S.nbhd a).tgt_Γ g hzU, hg, htψ]
  -- the step `Γ(g⁻¹, s φ) : s φ → s φ'` closes the chain to a z-loop at `s φ'`
  have hp : (S.τ a a ((S.nbhd a).rep.Γ g⁻¹ (A.X.src φ))).Pairs i (g⁻¹ • i) := by
    rw [S.diag a ha g⁻¹ _ hs₁, IndexCorr.pairs_ofPerm]
  have h₄ := Arc.snoc h₃ ha (by rw [(S.nbhd a).src_Γ g⁻¹ hwU, htψ])
    (by rw [(S.nbhd a).tgt_Γ g⁻¹ hwU, ← hΦ, (S.nbhd a).Φ_inv_Φ g hzU]; exact hs₂) hp
  have hcomp : A.X.comp ((S.nbhd a).rep.Γ g⁻¹ (A.X.src φ)) (A.X.comp (A.X.inv φ) φ') =
      A.X.unit (A.X.src φ') := by
    rw [← hg, ← hΦ, (S.nbhd a).Γ_mul g⁻¹ g hzU, inv_mul_cancel, (S.nbhd a).Γ_one hzU]
  rw [hcomp] at h₄
  have hrel : T.sh a i' (A.X.src φ') = T.sh a (g⁻¹ • i) (A.X.src φ') :=
    T.sh_zRel a ha _ hs₂ i' (g⁻¹ • i) h₄
  have heq := T.sh_equivariant a ha g (g⁻¹ • i) _ hs₂
  rw [smul_inv_smul, hΦ, hg, ← hrel] at heq
  have hbs : fibAct (A.X.comp (A.X.inv φ) φ') (T.bsec a i' (A.X.src φ')) =
      T.bsec a i (A.X.src φ) := by
    refine fibAct_sectionSmul (isSection_extendZero _ _) (isSection_extendZero _ _) hsψ htψ
      ?_ ?_
    · have := T.β_tgt a (A.X.comp (A.X.inv φ) φ')
      rwa [htψ, hsψ] at this
    · rw [← extendZero_eqOn (T.isScPlusSectionOn_sh a ha i).1 hs₁,
        ← extendZero_eqOn (T.isScPlusSectionOn_sh a ha i').1 hs₂]
      exact heq
  have hP : A.P (T.bsec a i' (A.X.src φ')) = A.X.src (A.X.comp (A.X.inv φ) φ') := by
    rw [T.isSection_bsec, hsψ]
  rw [← hbs, ← AtomicStructData.fibAct_comp hP htψ.symm, AtomicStructData.comp_inv_comp e]

/-! ### The transported sections -/

/-- **The sections `s̃ᵃ_{b,j}` of Proposition 14.5.4**: `μ(φ, β_a·ŝᵃᵢ(s φ))` for an arc from
`(s φ, i)`, `s φ ∈ V̂_a`, to `(y, j)` with composite `φ`, `t φ = y`; `0` if there is none. -/
def tsec (a b : A.Obj) (j : S.I b) (y : A.Obj) : A.W :=
  if h : ∃ p : S.I a × A.Mor, S.Arc a b p.1 j p.2 ∧ A.X.tgt p.2 = y then
    fibAct h.choose.2 (T.bsec a h.choose.1 (A.X.src h.choose.2))
  else fiberZero A.P y

theorem tsec_of_arc {a b : A.Obj} {i : S.I a} {j : S.I b} {φ : A.Mor} (h : S.Arc a b i j φ) :
    T.tsec a b j (A.X.tgt φ) = fibAct φ (T.bsec a i (A.X.src φ)) := by
  have hex : ∃ p : S.I a × A.Mor, S.Arc a b p.1 j p.2 ∧ A.X.tgt p.2 = A.X.tgt φ :=
    ⟨(i, φ), h, rfl⟩
  unfold tsec
  rw [dif_pos hex]
  exact T.fibAct_bsec_eq h hex.choose_spec.1 hex.choose_spec.2

theorem tsec_of_not {a b : A.Obj} {j : S.I b} {y : A.Obj}
    (h : ¬ ∃ p : S.I a × A.Mor, S.Arc a b p.1 j p.2 ∧ A.X.tgt p.2 = y) :
    T.tsec a b j y = fiberZero A.P y := by
  unfold tsec
  rw [dif_neg h]

/-- A morphism from `V̂_a` to `V̂_b` with a pair `(i, j)` is a chain of length one. -/
theorem arc_of_pairs {a b : A.Obj} (ha : a ∈ S.A) (hb : b ∈ S.A) {φ : A.Mor}
    (hs : A.X.src φ ∈ S.V a) (ht : A.X.tgt φ ∈ S.V b) {i : S.I a} {j : S.I b}
    (hp : (S.τ a b φ).Pairs i j) : S.Arc a b i j φ := by
  have := Arc.snoc (Arc.nil ha hs i) hb (A.X.tgt_unit _).symm ht hp
  rwa [GroupoidStr.comp_unit_of_eq rfl] at this

/-- **The text's form of the definition**: `s̃ᵃ_{b,j}(t φ) = μ(φ, β_a·ŝᵃᵢ(s φ))` when `(i, j)` is a
pair of `τ̂_{a,b}(φ)`, `s φ ∈ V̂_a`, `t φ ∈ V̂_b`. -/
theorem tsec_of_pairs {a b : A.Obj} (ha : a ∈ S.A) (hb : b ∈ S.A) {φ : A.Mor}
    (hs : A.X.src φ ∈ S.V a) (ht : A.X.tgt φ ∈ S.V b) {i : S.I a} {j : S.I b}
    (hp : (S.τ a b φ).Pairs i j) :
    T.tsec a b j (A.X.tgt φ) = fibAct φ (T.bsec a i (A.X.src φ)) :=
  T.tsec_of_arc (arc_of_pairs ha hb hs ht hp)

/-- `s̃ᵃ_{b,j}` vanishes at the points of `V̂_b` that are not targets of morphisms from `V̂_a`. -/
theorem tsec_of_not_reach {a b : A.Obj} {j : S.I b} {y : A.Obj}
    (h : ¬ ∃ φ, A.X.src φ ∈ S.V a ∧ A.X.tgt φ = y) : T.tsec a b j y = fiberZero A.P y :=
  T.tsec_of_not fun ⟨_, hp, e⟩ => h ⟨_, hp.props.2.2.1, e⟩

/-! ### sc⁺ on `V̂_b` -/

/-- **`s̃ᵃ_{b,j}` is an sc⁺-section on `V̂_b`.** -/
theorem isScPlusSectionOn_tsec {a b : A.Obj} (ha : a ∈ S.A) (hb : b ∈ S.A) (j : S.I b) :
    IsScPlusSectionOn A (T.tsec a b j) (S.V b) := by
  refine IsScPlusSectionOn.of_locally (T.isOpen_V b hb) fun y₀ hy₀ => ?_
  by_cases hR : ∃ φ, A.X.src φ ∈ S.V a ∧ A.X.tgt φ = y₀
  · obtain ⟨φ₀, hs₀, ht₀⟩ := hR
    obtain ⟨Tm, V₂, τ, hT, hτ⟩ := A.X.isLocalScDiffeo_tgt φ₀
    have hτy : τ y₀ = φ₀ := by
      have := hτ.left_inv φ₀ hT
      rwa [ht₀] at this
    have hy₀V₂ : y₀ ∈ V₂ := by
      have := hτ.mapsTo hT
      rwa [ht₀] at this
    have hV₂ : IsOpen V₂ := hτ.isScSmoothOn_inv.isOpen
    have hτc : ContinuousAt τ y₀ :=
      hτ.isScSmoothOn_inv.continuousOn.continuousAt (hV₂.mem_nhds hy₀V₂)
    obtain ⟨i, hi⟩ := IndexCorr.exists_pairs_left_t9 (S.τ a b φ₀) j
    have hsrc : ∀ᶠ z in 𝓝 y₀, A.X.src (τ z) ∈ S.V a := by
      have hc : ContinuousAt (A.X.src ∘ τ) y₀ := A.X.continuous_src.continuousAt.comp hτc
      refine hc.preimage_mem_nhds ((T.isOpen_V a ha).mem_nhds ?_)
      change A.X.src (τ y₀) ∈ S.V a
      rw [hτy]; exact hs₀
    have hV₂ev : ∀ᶠ z in 𝓝 y₀, z ∈ V₂ := hV₂.mem_nhds hy₀V₂
    have hVb : ∀ᶠ z in 𝓝 y₀, z ∈ S.V b := (T.isOpen_V b hb).mem_nhds hy₀
    have hmor : ∀ᶠ z in 𝓝 y₀, τ z ∈ A.X.morBetween (S.V a) (S.V b) := by
      filter_upwards [hsrc, hV₂ev, hVb] with z h1 h2 h3
      exact ⟨h1, by rw [hτ.right_inv z h2]; exact h3⟩
    have htend : Tendsto τ (𝓝 y₀) (𝓝[A.X.morBetween (S.V a) (S.V b)] φ₀) :=
      tendsto_nhdsWithin_iff.2 ⟨hτy ▸ hτc, hmor⟩
    have hloc := htend.eventually
      (T.locallyConstant a ha b hb φ₀ ⟨hs₀, by rw [ht₀]; exact hy₀⟩)
    obtain ⟨O, hOsub, hO, hy₀O⟩ := mem_nhds_iff.1 (hsrc.and (hV₂ev.and (hVb.and hloc)))
    refine ⟨O, hO, hy₀O, fun z hz => (hOsub hz).2.2.1, ?_⟩
    have hval : ∀ z ∈ O, transportSection τ (fun z => T.bsec a i (A.X.src (τ z))) z =
        T.tsec a b j z := by
      intro z hz
      obtain ⟨h1, h2, h3, h4⟩ := hOsub hz
      have hp : (S.τ a b (τ z)).Pairs i j := by
        change S.τ a b (τ z) = S.τ a b φ₀ at h4
        rw [h4]; exact hi
      have e := T.tsec_of_pairs ha hb h1 (by rw [hτ.right_inv z h2]; exact h3) hp
      rw [hτ.right_inv z h2] at e
      rw [e, AtomicStructData.transportSection_eq_fibAct (T.isSection_bsec a i _)]
    obtain ⟨-, G, hG, hGs⟩ := T.isScPlusSectionOn_bsec ha i
    have hτO : A.X.PObj.IsScSmoothOn A.X.PMor τ O :=
      hτ.isScSmoothOn_inv.mono hO fun z hz => (hOsub hz).2.1
    have hsτ : A.X.PObj.IsScSmoothOn A.X.PObj (A.X.src ∘ τ) O :=
      MPolyfold.IsScSmoothOn.comp A.X.isScSmoothMap_src hτO (mapsTo_univ _ _)
    exact (isScPlusSectionOn_transportSection hτO (G := G ∘ (A.X.src ∘ τ))
      (fun z hz => hG _ (hOsub hz).1)
      (MPolyfold.IsScSmoothOn.comp hGs hsτ fun z hz => (hOsub hz).1)
      (fun z _ => T.isSection_bsec a i _) (fun z hz => hτ.right_inv z (hOsub hz).2.1)).congr
      hval
  · -- away from `t(s⁻¹(K))`, `K = cl{y ∈ Ũ(a) | β_a(y) ≠ 0} ⊆ V̂_a`, the section vanishes
    have hKV : closure {y ∈ (S.nbhd a).U | T.β a y ≠ 0} ⊆ S.V a := T.closure_support_β a ha
    have hKcl : closure {y ∈ (S.nbhd a).U | T.β a y ≠ 0} ⊆ closure (S.nbhd a).U :=
      closure_mono (sep_subset _ _)
    have hC : IsClosed (A.X.tgt '' (A.X.src ⁻¹' closure {y ∈ (S.nbhd a).U | T.β a y ≠ 0})) :=
      isClosed_image_preimage_of_isProperMap_domRestrict (T.proper a ha) hKcl
        (isClosed_closure.preimage A.X.continuous_src)
    have hy₀C : y₀ ∉ A.X.tgt '' (A.X.src ⁻¹' closure {y ∈ (S.nbhd a).U | T.β a y ≠ 0}) :=
      fun ⟨φ, hφ, ht⟩ => hR ⟨φ, hKV hφ, ht⟩
    have hO := hC.isOpen_compl.inter (T.isOpen_V b hb)
    refine ⟨_, hO, ⟨hy₀C, hy₀⟩, inter_subset_right,
      (isScPlusSectionOn_fiberZero hO).congr fun z hz => ?_⟩
    symm
    by_cases hz' : ∃ p : S.I a × A.Mor, S.Arc a b p.1 j p.2 ∧ A.X.tgt p.2 = z
    · obtain ⟨⟨i, φ⟩, h, rfl⟩ := hz'
      have hs := h.props.2.2.1
      have hβ0 : T.β a (A.X.src φ) = 0 := by
        by_contra hne
        exact hz.1 ⟨φ, subset_closure ⟨S.V_subset a ha hs, hne⟩, rfl⟩
      rw [T.tsec_of_arc h, T.bsec_of_eq_zero a i hβ0, fibAct_fiberZero rfl rfl]
    · exact T.tsec_of_not hz'

/-! ### Equivariance and (4) -/

/-- **`G_b`-equivariance of `(s̃ᵃ_{b,j})_j` on `V̂_b`.** -/
theorem tsec_equivariant {a b : A.Obj} (hb : b ∈ S.A) (g : A.X.Isotropy b) (j : S.I b)
    {y : A.Obj} (hy : y ∈ S.V b) :
    T.tsec a b (g • j) ((S.nbhd b).rep.Φ g y) =
      fibAct ((S.nbhd b).rep.Γ g y) (T.tsec a b j y) := by
  have hyU := S.V_subset b hb hy
  by_cases hR : ∃ p : S.I a × A.Mor, S.Arc a b p.1 j p.2 ∧ A.X.tgt p.2 = y
  · obtain ⟨⟨i, φ⟩, h, rfl⟩ := hR
    have hp : (S.τ b b ((S.nbhd b).rep.Γ g (A.X.tgt φ))).Pairs j (g • j) := by
      rw [S.diag b hb g _ hy, IndexCorr.pairs_ofPerm]
    have h' := Arc.snoc h hb ((S.nbhd b).src_Γ g hyU)
      (by rw [(S.nbhd b).tgt_Γ g hyU]; exact S.mapsTo_V b hb g hy) hp
    have e1 := T.tsec_of_arc h'
    rw [A.X.tgt_comp _ _ ((S.nbhd b).src_Γ g hyU), (S.nbhd b).tgt_Γ g hyU,
      A.X.src_comp _ _ ((S.nbhd b).src_Γ g hyU)] at e1
    rw [e1, T.tsec_of_arc h,
      AtomicStructData.fibAct_comp (T.isSection_bsec a i _) ((S.nbhd b).src_Γ g hyU)]
  · have hw : (S.nbhd b).rep.Φ g y ∈ S.V b := S.mapsTo_V b hb g hy
    have hwU := S.V_subset b hb hw
    have hR' : ¬ ∃ p : S.I a × A.Mor,
        S.Arc a b p.1 (g • j) p.2 ∧ A.X.tgt p.2 = (S.nbhd b).rep.Φ g y := by
      rintro ⟨⟨i, φ⟩, h, e⟩
      apply hR
      have hp : (S.τ b b ((S.nbhd b).rep.Γ g⁻¹ ((S.nbhd b).rep.Φ g y))).Pairs (g • j) j := by
        rw [S.diag b hb g⁻¹ _ hw, IndexCorr.pairs_ofPerm, inv_smul_smul]
      have hsrc : A.X.src ((S.nbhd b).rep.Γ g⁻¹ ((S.nbhd b).rep.Φ g y)) = A.X.tgt φ := by
        rw [(S.nbhd b).src_Γ g⁻¹ hwU, e]
      have h' := Arc.snoc h hb hsrc
        (by rw [(S.nbhd b).tgt_Γ g⁻¹ hwU, (S.nbhd b).Φ_inv_Φ g hyU]; exact hy) hp
      refine ⟨⟨i, A.X.comp ((S.nbhd b).rep.Γ g⁻¹ ((S.nbhd b).rep.Φ g y)) φ⟩, h', ?_⟩
      change A.X.tgt (A.X.comp _ φ) = y
      rw [A.X.tgt_comp _ _ hsrc, (S.nbhd b).tgt_Γ g⁻¹ hwU, (S.nbhd b).Φ_inv_Φ g hyU]
    rw [T.tsec_of_not hR, T.tsec_of_not hR',
      fibAct_fiberZero ((S.nbhd b).src_Γ g hyU) ((S.nbhd b).tgt_Γ g hyU)]

/-- **(4)**: `s̃ᵃ_{b',j'}(t φ) = μ(φ, s̃ᵃ_{b,j}(s φ))` for every pair `(j, j')` of `τ̂_{b,b'}(φ)`,
`φ ∈ V̂_{b,b'}`. -/
theorem tsec_compat {a b b' : A.Obj} (hb : b ∈ S.A) (hb' : b' ∈ S.A) {φ : A.Mor}
    (hφ : φ ∈ A.X.morBetween (S.V b) (S.V b')) :
    (S.τ b b' φ).Sat fun j j' =>
      T.tsec a b' j' (A.X.tgt φ) = fibAct φ (T.tsec a b j (A.X.src φ)) := by
  refine IndexCorr.sat_of_pairs_t9 _ fun j j' hp => ?_
  by_cases hR : ∃ p : S.I a × A.Mor, S.Arc a b p.1 j p.2 ∧ A.X.tgt p.2 = A.X.src φ
  · obtain ⟨⟨i, ψ⟩, h, e⟩ := hR
    have h' := Arc.snoc h hb' e.symm hφ.2 hp
    have e1 := T.tsec_of_arc h'
    rw [A.X.tgt_comp _ _ e.symm, A.X.src_comp _ _ e.symm] at e1
    rw [e1, ← e, T.tsec_of_arc h, AtomicStructData.fibAct_comp (T.isSection_bsec a i _) e.symm]
  · have hR' : ¬ ∃ p : S.I a × A.Mor, S.Arc a b' p.1 j' p.2 ∧ A.X.tgt p.2 = A.X.tgt φ := by
      rintro ⟨⟨i, ψ⟩, h, e⟩
      apply hR
      have hp' : (S.τ b' b (A.X.inv φ)).Pairs j' j := by
        rw [S.swap b hb b' hb' (A.X.inv φ) (by rw [A.X.src_inv]; exact hφ.2)
          (by rw [A.X.tgt_inv]; exact hφ.1), GroupoidStr.inv_inv, IndexCorr.pairs_swap]
        exact hp
      have hsrc : A.X.src (A.X.inv φ) = A.X.tgt ψ := by rw [A.X.src_inv, e]
      have h' := Arc.snoc h hb hsrc (by rw [A.X.tgt_inv]; exact hφ.1) hp'
      refine ⟨⟨i, A.X.comp (A.X.inv φ) ψ⟩, h', ?_⟩
      change A.X.tgt (A.X.comp _ ψ) = A.X.src φ
      rw [A.X.tgt_comp _ _ hsrc, A.X.tgt_inv]
    rw [T.tsec_of_not hR, T.tsec_of_not hR', fibAct_fiberZero rfl rfl]

/-! ### (3): the values over `∂X` -/

/-- **(3)**: `s̃ᵃ_{b,j} = β_a·s⁰ᵇⱼ` on `V̂_b ∩ ∂X` (from Definition 14.1.7 (4) for `τ̂` over
`∂X`, Proposition 14.4.14 (1), and Lemma 14.5.1 (1) where `V̂_a` does not reach). -/
theorem tsec_boundary (hβ : T.SuppInSat) {a b : A.Obj} (ha : a ∈ S.A) (hb : b ∈ S.A)
    (j : S.I b) {y : A.Obj} (hy : y ∈ S.V b ∩ A.X.PObj.boundary) :
    T.tsec a b j y = Polyfold.sectionSmul A.P (T.β a) (T.s0 b j) y := by
  have hPs0 : A.P (T.s0 b j y) = y := by
    rw [← T.sh_boundary b hb j y hy]
    exact (T.isScPlusSectionOn_sh b hb j).1 y hy.1
  by_cases hR : ∃ φ, A.X.src φ ∈ S.V a ∧ A.X.tgt φ = y
  · obtain ⟨φ, hs, rfl⟩ := hR
    have hsb : A.X.src φ ∈ A.X.PObj.boundary := src_mem_boundary_t9 hy.2
    obtain ⟨i, hi⟩ := IndexCorr.exists_pairs_left_t9 (S.τ a b φ) j
    rw [T.tsec_of_pairs ha hb hs hy.1 hi]
    have hc := IndexCorr.rel_of_sat_t9 (T.s0_compat a ha b hb φ ⟨⟨hs, hsb⟩, hy⟩) hi
    have e₁ : T.s0 b j (A.X.tgt φ) = extendZero (S.V b) (T.sh b j) (A.X.tgt φ) := by
      rw [← extendZero_eqOn (T.isScPlusSectionOn_sh b hb j).1 hy.1, T.sh_boundary b hb j _ hy]
    rw [sectionSmul_congr_t9 e₁]
    refine fibAct_sectionSmul (isSection_extendZero _ _) (isSection_extendZero _ _) rfl rfl
      (T.β_tgt a φ) ?_
    rw [← e₁, ← extendZero_eqOn (T.isScPlusSectionOn_sh a ha i).1 hs,
      T.sh_boundary a ha i _ ⟨hs, hsb⟩]
    exact hc
  · rw [T.tsec_of_not_reach hR,
      sectionSmul_of_eq_zero_t9 hPs0 (by by_contra h; exact hR (hβ a ha y h))]

/-! ### Proposition 14.5.4 -/

/-- **2021 Proposition 14.5.4, p. 673 (2017: Proposition 14.8)**, proved: for the data of
§§14.3–14.4 (`T : TransportInput A S`) whose cut-offs satisfy Lemma 14.5.1 (1), every `a ∈ A`
has sections `s̃ᵃ_{b,j}`, sc⁺ and `G_b`-equivariant on every `V̂_b`, with (1)–(4)
(GL's `proposition_14_5_4_statement`). -/
theorem proposition_14_5_4 (hβ : T.SuppInSat) : proposition_14_5_4_statement T := by
  intro a ha
  refine ⟨T.tsec a, fun b hb j => T.isScPlusSectionOn_tsec ha hb j,
    fun b hb g j y hy => T.tsec_equivariant hb g j hy, fun i y hy => ?_, fun i => ?_,
    fun b hb j y hy => T.tsec_boundary hβ ha hb j hy,
    fun b hb b' hb' φ hφ => T.tsec_compat hb hb' hφ⟩
  · have e := T.tsec_of_arc (Arc.nil ha hy i)
    rw [A.X.tgt_unit, A.X.src_unit, AtomicStructData.fibAct_unit (T.isSection_bsec a i y)] at e
    rw [e, T.bsec_eq ha i hy]
  · refine ⟨closure {y ∈ (S.nbhd a).U | T.β a y ≠ 0}, isClosed_closure,
      T.closure_support_β a ha, fun y hy hyK => ?_⟩
    have e := T.tsec_of_arc (Arc.nil ha hy i)
    rw [A.X.tgt_unit, A.X.src_unit, AtomicStructData.fibAct_unit (T.isSection_bsec a i y)] at e
    have hβ0 : T.β a y = 0 := by
      by_contra hne
      exact hyK (subset_closure ⟨S.V_subset a ha hy, hne⟩)
    rw [e, T.bsec_of_eq_zero a i hβ0]

/-- **The hypothesis `SuppInSat` is satisfiable**: it holds for `β ≡ 0`. -/
theorem suppInSat_of_zero (hβ : ∀ a y, T.β a y = 0) : T.SuppInSat :=
  fun _ _ y h => absurd (hβ _ y) h

end TransportInput

end SBLocalization

end Polyfold
