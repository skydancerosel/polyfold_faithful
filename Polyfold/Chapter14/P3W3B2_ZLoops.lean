import Polyfold.Chapter13.P3G_GoodSystem
import Polyfold.Chapter13.P3D_Correspondence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 14,
§14.4, pp. 659–660: **Definition 14.4.2** (z-loops), **Definition 14.4.3** (z-arcs),
**Definition 14.4.4** (z-equivalence `∼_z`) and **Lemma 14.4.5** (equivariance of `∼_z`)
(2017 text: Definitions 14.5–14.7, Lemma 14.6).

# z-loops, z-arcs and the relations `∼_z`

## The text, paraphrased

Fix `a ∈ A` and `z ∈ V̂_a`.  (Definition 14.4.2) A z-loop is a sequence `a = a₀, …, a_n = a` in
`A` with morphisms `φ₀, …, φ_{n-1}`, `t(φ_j) = s(φ_{j+1})`, `s(φ₀) = z = t(φ_{n-1})`,
`s(φ_j) ∈ V̂_{a_j}`, `t(φ_j) ∈ V̂_{a_{j+1}}` and `φ_{n-1} ∘ ⋯ ∘ φ₀ = 1_z`; each `φ_j` lies in
`V̂_{a_j, a_{j+1}}`, where the correspondence `τ̂_{a_j, a_{j+1}}(φ_j)` is represented by
`I_{a_j} ←α_j I_j →β_j I_{a_{j+1}}`.  (Definition 14.4.3) A z-arc along the loop is a sequence
of indices `i_j ∈ I_{a_j}` with `(i_j, i_{j+1}) = (α_j(k_j), β_j(k_j))` for some `k_j ∈ I_j`.
(Definition 14.4.4) `i ∼_z i'` if a z-arc with `i₀ = i`, `i_n = i'` exists; `[i]_{∼_z}` is the
class.  (Lemma 14.4.5) `i ∼_z i'` if and only if `g(i) ∼_{g∗z} g(i')`, and
`[g(i)]_{∼_{g∗z}} = g([i]_{∼_z})`.  (Proof) Prepend `Γ(g⁻¹, g ∗ z)` and append `Γ(g, z)`.

## What is formalized

The setting is abstract, so that the objects of §14.3 instantiate it (namespace
`Polyfold.EpGroupoid`): `ZSetup X` carries the index set `A`, for every `a` an open neighbourhood
`Ũ(a)` with the natural `G_a`-action (`nbhd a`, a `NatNbhd`), the `G_a`-invariant sets
`V̂_a ⊆ Ũ(a)`, the finite index sets `I_a` with their `G_a`-actions, and maps
`τ̂_{a,a'} : Mor → J(a, a')` (`IndexCorr`, Definition 13.3.1), with the two properties the
equivariance needs: `τ̂_{a,a}(Γ(g, w)) = [I_a ←id I_a →g I_a]` on `V̂_a` (as Definition 13.3.6 (1))
and `τ̂_{a',a}(φ) = τ̂_{a,a'}(φ⁻¹)♯` (as Definition 13.3.6 (2)).

* `IndexCorr.Pairs τ i j`: some (equivalently every) representative `α, β` of `τ` has
  `(i, j) = (α(k), β(k))` for some `k` (namespace `Polyfold.SBLocalization`); `pairs_swap`,
  `pairs_ofPerm`.
* **Definitions 14.4.2 and 14.4.3** together: `ZSetup.Arc S a b i j φ` is the inductive predicate
  "there are a chain of morphisms `φ₀, …, φ_{m-1}` through the `V̂_{a_j}` from `V̂_a` to `V̂_b` with
  composite `φ` and a z-arc of indices from `i ∈ I_a` to `j ∈ I_b` along it"; a z-loop with a z-arc
  is an `Arc S a a i i' (1_z)` (the composite is `1_z`, which also fixes `s(φ₀) = z`).
  Closure under
  concatenation (`Arc.trans`) and reversal (`Arc.symm`).
* **Definition 14.4.4**: `ZSetup.ZRel S a z i i'` (`i ∼_z i'`), `ZSetup.zClass` (`[i]_{∼_z}`);
  `ZSetup.zRel_equivalence` (`∼_z` is an equivalence relation, as the text calls it).
* **Lemma 14.4.5**: `ZSetup.lemma_14_4_5` and `ZSetup.lemma_14_4_5_class`.
* Satisfiability of the setting: `ZSetup.trivialSetup` (on every ep-groupoid).

The chain may have length `0` (the empty composite `1_z`); this adds nothing, since by
`τ̂_{a,a}(Γ(1, z)) = [id]` the one-step loop `1_z` relates exactly the same indices
(`ZSetup.zRel_iff_unit_step`).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

namespace IndexCorr

variable {α β : Type u}

/-- `(i, j) = (α(k), β(k))` for some `k`, for a representative `I_x ←α I →β I_{x'}`; well
defined on correspondences. -/
def Pairs (τ : IndexCorr α β) (i : α) (j : β) : Prop :=
  Quotient.lift (fun d : IndexDiagram α β => ∃ k, d.a k = i ∧ d.b k = j)
    (fun d d' h => by
      obtain ⟨c, hc⟩ := h
      refine propext ⟨fun ⟨k, h1, h2⟩ => ⟨c k, (hc k).1.trans h1, (hc k).2.trans h2⟩,
        fun ⟨k, h1, h2⟩ => ⟨c.symm k, ?_, ?_⟩⟩
      · have := (hc (c.symm k)).1
        rw [Equiv.apply_symm_apply] at this
        exact this.symm.trans h1
      · have := (hc (c.symm k)).2
        rw [Equiv.apply_symm_apply] at this
        exact this.symm.trans h2) τ

@[simp] theorem pairs_mk (d : IndexDiagram α β) (i : α) (j : β) :
    (mk d).Pairs i j ↔ ∃ k, d.a k = i ∧ d.b k = j := Iff.rfl

/-- The pseudo-inverse reverses the pairs. -/
theorem pairs_swap (τ : IndexCorr α β) (i : α) (j : β) : τ.swap.Pairs j i ↔ τ.Pairs i j := by
  induction τ using ind with
  | h d => exact ⟨fun ⟨k, h1, h2⟩ => ⟨k, h2, h1⟩, fun ⟨k, h1, h2⟩ => ⟨k, h2, h1⟩⟩

/-- The pairs of `[I_x ←id I_x →g I_x]` are `(i, g • i)`. -/
theorem pairs_ofPerm {G : Type*} [Group G] [Fintype α] [MulAction G α] (g : G) (i j : α) :
    (ofPerm g : IndexCorr α α).Pairs i j ↔ j = g • i := by
  constructor
  · rintro ⟨k, h1, h2⟩
    subst h1
    exact h2.symm
  · rintro rfl
    exact ⟨i, rfl, rfl⟩

end IndexCorr

end SBLocalization

open SBLocalization

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **The setting of Definitions 14.4.2–14.4.4** (pp. 659–660): an index set `A ⊆ X`, for every
`a` an open neighbourhood `Ũ(a)` with the natural `G_a`-action, `G_a`-invariant sets
`V̂_a ⊆ Ũ(a)`, finite index sets `I_a` with `G_a`-actions, and maps `τ̂_{a,a'}` from morphisms to
correspondences `J(a, a')` with `τ̂_{a,a}(Γ(g, w)) = [id, g]` for `w ∈ V̂_a` and
`τ̂_{a',a}(φ) = τ̂_{a,a'}(φ⁻¹)♯` on `V̂_{a',a}`. -/
structure ZSetup where
  /-- The index set `A`. -/
  A : Set Obj
  /-- `Ũ(a)` with the natural `G_a`-action. -/
  nbhd : ∀ a : Obj, X.NatNbhd a
  /-- The sets `V̂_a`. -/
  V : Obj → Set Obj
  V_subset : ∀ a ∈ A, V a ⊆ (nbhd a).U
  mapsTo_V : ∀ a ∈ A, ∀ g, MapsTo ((nbhd a).rep.Φ g) (V a) (V a)
  /-- The index sets `I_a`. -/
  I : Obj → Type u
  [fintype : ∀ a, Fintype (I a)]
  [mulAction : ∀ a, MulAction (X.Isotropy a) (I a)]
  /-- The correspondences `τ̂_{a,a'}`. -/
  τ : ∀ a a' : Obj, Mor → IndexCorr (I a) (I a')
  diag : ∀ a ∈ A, ∀ (g : X.Isotropy a), ∀ w ∈ V a,
    τ a a ((nbhd a).rep.Γ g w) = IndexCorr.ofPerm g
  swap : ∀ a ∈ A, ∀ a' ∈ A, ∀ φ, X.src φ ∈ V a' → X.tgt φ ∈ V a →
    τ a' a φ = (τ a a' (X.inv φ)).swap

attribute [instance] ZSetup.fintype ZSetup.mulAction

namespace ZSetup

variable {X} (S : X.ZSetup)

/-- **Definitions 14.4.2 and 14.4.3 (2017: 14.5, 14.6)** (z-loops and z-arcs, pp. 659–660), as one
inductive
predicate: `Arc a b i j φ` says that there are `a = a₀, …, a_m = b` in `A`, composable morphisms
`φ₀, …, φ_{m-1}` with `s(φ_j) ∈ V̂_{a_j}`, `t(φ_j) ∈ V̂_{a_{j+1}}` and composite
`φ_{m-1} ∘ ⋯ ∘ φ₀ = φ` (`φ = 1_z` for `m = 0`, `z ∈ V̂_a`), and indices `i = i₀, …, i_m = j`,
`i_j ∈ I_{a_j}`, with `(i_j, i_{j+1})` a pair of `τ̂_{a_j, a_{j+1}}(φ_j)`.  A z-loop with a z-arc
from `i` to `i'` is an `Arc a a i i' 1_z`. -/
inductive Arc : (a b : Obj) → S.I a → S.I b → Mor → Prop
  | nil {a : Obj} (ha : a ∈ S.A) {z : Obj} (hz : z ∈ S.V a) (i : S.I a) :
      Arc a a i i (X.unit z)
  | snoc {a b c : Obj} {i : S.I a} {j : S.I b} {k : S.I c} {φ ψ : Mor} :
      Arc a b i j φ → c ∈ S.A → X.src ψ = X.tgt φ → X.tgt ψ ∈ S.V c →
      (S.τ b c ψ).Pairs j k → Arc a c i k (X.comp ψ φ)

variable {S}

theorem Arc.props {a b : Obj} {i : S.I a} {j : S.I b} {φ : Mor} (h : S.Arc a b i j φ) :
    a ∈ S.A ∧ b ∈ S.A ∧ X.src φ ∈ S.V a ∧ X.tgt φ ∈ S.V b := by
  induction h with
  | nil ha hz i => exact ⟨ha, ha, by rw [X.src_unit]; exact hz, by rw [X.tgt_unit]; exact hz⟩
  | snoc _ hc hs ht _ ih =>
    exact ⟨ih.1, hc, by rw [X.src_comp _ _ hs]; exact ih.2.2.1, by rw [X.tgt_comp _ _ hs]; exact ht⟩

/-- **Concatenation** of chains with arcs. -/
theorem Arc.trans {a b c : Obj} {i : S.I a} {j : S.I b} {k : S.I c} {φ ψ : Mor}
    (h₁ : S.Arc a b i j φ) (h₂ : S.Arc b c j k ψ) (h : X.src ψ = X.tgt φ) :
    S.Arc a c i k (X.comp ψ φ) := by
  induction h₂ with
  | nil hb hz j =>
    rw [X.src_unit] at h
    rw [GroupoidStr.unit_comp_of_eq h.symm]
    exact h₁
  | @snoc c' d' j' k' l' χ ψ' _ hc hs ht hp ih =>
    have hχ : X.src χ = X.tgt φ := by rw [← h, X.src_comp _ _ hs]
    have e := Arc.snoc (ih h₁ hχ) hc (by rw [X.tgt_comp _ _ hχ]; exact hs) ht hp
    rwa [← X.comp_assoc _ _ _ hs hχ] at e

/-- **Reversal**: the inverse morphisms with the reversed arc
(by `τ̂_{a',a}(φ⁻¹) = τ̂_{a,a'}(φ)♯`). -/
theorem Arc.symm {a b : Obj} {i : S.I a} {j : S.I b} {φ : Mor} (h : S.Arc a b i j φ) :
    S.Arc b a j i (X.inv φ) := by
  induction h with
  | nil ha hz i =>
    rw [GroupoidStr.inv_unit]
    exact Arc.nil ha hz i
  | @snoc b c i j k φ ψ h hc hs ht hp ih =>
    have hb := h.props.2.1
    have hφt := h.props.2.2.2
    have hpair : (S.τ c b (X.inv ψ)).Pairs k j := by
      rw [S.swap b hb c hc (X.inv ψ) (by rw [X.src_inv]; exact ht)
        (by rw [X.tgt_inv, hs]; exact hφt), GroupoidStr.inv_inv, IndexCorr.pairs_swap]
      exact hp
    have e₁ := Arc.snoc (Arc.nil hc ht k) hb (by rw [X.src_inv, X.tgt_unit])
      (by rw [X.tgt_inv, hs]; exact hφt) hpair
    rw [GroupoidStr.comp_unit_of_eq (X.src_inv ψ)] at e₁
    have e₂ := e₁.trans ih (by rw [X.src_inv, X.tgt_inv, hs])
    rwa [← GroupoidStr.inv_comp_rev hs] at e₂

/-- **Definition 14.4.4, p. 660 (2017: Definition 14.7)**: `i ∼_z i'` (for `a`) if there are a
z-loop for `a` and a z-arc
along it from `i` to `i'`. -/
def ZRel (S : X.ZSetup) (a z : Obj) (i i' : S.I a) : Prop := S.Arc a a i i' (X.unit z)

/-- **(14.43)**: the class `[i]_{∼_z} = {i' ∈ I_a | i' ∼_z i}`. -/
def zClass (S : X.ZSetup) (a z : Obj) (i : S.I a) : Set (S.I a) := {i' | S.ZRel a z i' i}

theorem ZRel.mem_V {a z : Obj} {i i' : S.I a} (h : S.ZRel a z i i') : z ∈ S.V a := by
  have := (Arc.props h).2.2.1
  rwa [X.src_unit] at this

/-- **`∼_z` is an equivalence relation** on `I_a` (as the text calls it, after
Definition 14.4.4). -/
theorem zRel_equivalence {a z : Obj} (ha : a ∈ S.A) (hz : z ∈ S.V a) :
    Equivalence (S.ZRel a z) where
  refl i := Arc.nil ha hz i
  symm h := by
    have := Arc.symm h
    rwa [GroupoidStr.inv_unit] at this
  trans h₁ h₂ := by
    have := Arc.trans h₁ h₂ (by rw [X.src_unit, X.tgt_unit])
    rwa [GroupoidStr.unit_comp_of_eq (X.tgt_unit z)] at this

/-- Loops of length `0` add nothing: `i ∼_z i'` iff a z-loop of length at least one relates them
(append the step `1_z = Γ(1, z)`, whose correspondence is `[id]`). -/
theorem zRel_iff_unit_step {a z : Obj} {i i' : S.I a} :
    S.ZRel a z i i' ↔ ∃ (b : Obj) (j : S.I b) (φ ψ : Mor), S.Arc a b i j φ ∧ a ∈ S.A ∧
      X.src ψ = X.tgt φ ∧ X.tgt ψ ∈ S.V a ∧ (S.τ b a ψ).Pairs j i' ∧ X.comp ψ φ = X.unit z := by
  constructor
  · intro h
    have ha := (Arc.props h).1
    have hz := h.mem_V
    have hzU : z ∈ (S.nbhd a).U := S.V_subset a ha hz
    refine ⟨a, i', X.unit z, X.unit z, h, ha, by rw [X.src_unit, X.tgt_unit],
      by rw [X.tgt_unit]; exact hz, ?_, GroupoidStr.unit_comp_of_eq (X.tgt_unit z)⟩
    rw [← (S.nbhd a).Γ_one hzU, S.diag a ha 1 z hz, IndexCorr.pairs_ofPerm, one_smul]
  · rintro ⟨b, j, φ, ψ, h, ha, hs, ht, hp, he⟩
    have := Arc.snoc h ha hs ht hp
    rwa [he] at this

/-- The forward implication of Lemma 14.4.5. -/
theorem zRel_smul {a z : Obj} {i i' : S.I a} (h : S.ZRel a z i i') (g : X.Isotropy a) :
    S.ZRel a ((S.nbhd a).rep.Φ g z) (g • i) (g • i') := by
  have ha := (Arc.props h).1
  have hz := h.mem_V
  set N := S.nbhd a
  have hzU : z ∈ N.U := S.V_subset a ha hz
  set w := N.rep.Φ g z with hw_def
  have hw : w ∈ S.V a := S.mapsTo_V a ha g hz
  have hwU : w ∈ N.U := S.V_subset a ha hw
  have hgw : N.rep.Φ g⁻¹ w = z := N.Φ_inv_Φ g hzU
  -- the step `Γ(g⁻¹, w) : w → z`
  have hp₁ : (S.τ a a (N.rep.Γ g⁻¹ w)).Pairs (g • i) i := by
    rw [S.diag a ha g⁻¹ w hw, IndexCorr.pairs_ofPerm, inv_smul_smul]
  have e₁ := Arc.snoc (Arc.nil ha hw (g • i)) ha (by rw [N.src_Γ g⁻¹ hwU, X.tgt_unit])
    (by rw [N.tgt_Γ g⁻¹ hwU, hgw]; exact hz) hp₁
  have ht₁ : X.tgt (X.comp (N.rep.Γ g⁻¹ w) (X.unit w)) = z := by
    rw [X.tgt_comp _ _ (by rw [N.src_Γ g⁻¹ hwU, X.tgt_unit]), N.tgt_Γ g⁻¹ hwU, hgw]
  have e₂ := e₁.trans h (by rw [X.src_unit, ht₁])
  -- the step `Γ(g, z) : z → w`
  have hp₂ : (S.τ a a (N.rep.Γ g z)).Pairs i' (g • i') := by
    rw [S.diag a ha g z hz, IndexCorr.pairs_ofPerm]
  have ht₂ : X.tgt (X.comp (X.unit z) (X.comp (N.rep.Γ g⁻¹ w) (X.unit w))) = z := by
    rw [X.tgt_comp _ _ (by rw [X.src_unit, ht₁]), X.tgt_unit]
  have e₃ := Arc.snoc e₂ ha (by rw [N.src_Γ g hzU, ht₂]) (by rw [N.tgt_Γ g hzU]; exact hw) hp₂
  have hcomp : X.comp (N.rep.Γ g z) (X.comp (X.unit z) (X.comp (N.rep.Γ g⁻¹ w) (X.unit w))) =
      X.unit w := by
    rw [GroupoidStr.unit_comp_of_eq ht₁,
      GroupoidStr.comp_unit_of_eq (N.src_Γ g⁻¹ hwU), ← hgw, N.Γ_mul g g⁻¹ hwU, mul_inv_cancel,
      N.Γ_one hwU]
  rw [hcomp] at e₃
  exact e₃

/-- **Lemma 14.4.5, p. 660 (2017: Lemma 14.6)**: for `a ∈ A`, `z ∈ V̂_a`, `i, i' ∈ I_a` and `g ∈
G_a`:
`i ∼_z i'` if and only if `g(i) ∼_{g∗z} g(i')`. -/
theorem lemma_14_4_5 {a z : Obj} (ha : a ∈ S.A) (hz : z ∈ S.V a) (g : X.Isotropy a)
    (i i' : S.I a) :
    S.ZRel a z i i' ↔ S.ZRel a ((S.nbhd a).rep.Φ g z) (g • i) (g • i') := by
  refine ⟨fun h => zRel_smul h g, fun h => ?_⟩
  have := zRel_smul h g⁻¹
  rwa [(S.nbhd a).Φ_inv_Φ g (S.V_subset a ha hz), inv_smul_smul, inv_smul_smul] at this

/-- **Lemma 14.4.5, p. 660, the classes**: `[g(i)]_{∼_{g∗z}} = g([i]_{∼_z})`. -/
theorem lemma_14_4_5_class {a z : Obj} (ha : a ∈ S.A) (hz : z ∈ S.V a) (g : X.Isotropy a)
    (i : S.I a) :
    S.zClass a ((S.nbhd a).rep.Φ g z) (g • i) = (g • ·) '' S.zClass a z i := by
  ext j
  constructor
  · intro hj
    refine ⟨g⁻¹ • j, ?_, smul_inv_smul g j⟩
    change S.ZRel a z (g⁻¹ • j) i
    rw [S.lemma_14_4_5 ha hz g, smul_inv_smul]
    exact hj
  · rintro ⟨j', hj', rfl⟩
    exact (S.lemma_14_4_5 ha hz g j' i).1 hj'

/-! ### Satisfiability of the setting -/

variable (X) in
/-- **The setting is satisfiable** on every ep-groupoid: `A = X`, `V̂_a = Ũ(a)` an open
neighbourhood with the natural `G_a`-action (Theorem 7.1.13), one-point index sets and
`τ̂ ≡ [{∗} ← {∗} → {∗}]`. -/
def trivialSetup : X.ZSetup where
  A := univ
  nbhd a := Classical.choose (X.exists_natNbhd_isProperSubset a isOpen_univ (mem_univ a))
  V a := (Classical.choose (X.exists_natNbhd_isProperSubset a isOpen_univ (mem_univ a))).U
  V_subset _ _ := subset_rfl
  mapsTo_V a _ g :=
    (Classical.choose (X.exists_natNbhd_isProperSubset a isOpen_univ (mem_univ a))).mapsTo_Φ g
  I _ := PUnit.{u + 1}
  τ _ _ _ := IndexCorr.ofEquiv (Equiv.refl PUnit.{u + 1})
  diag _ _ _ _ _ :=
    IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _, fun _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  swap _ _ _ _ _ _ _ :=
    IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _, fun _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

variable (X) in
/-- In the trivial setting every `z ∈ X` gives a (reflexive) relation `∼_z`. -/
theorem trivialSetup_zRel (a z : Obj) (hz : z ∈ (trivialSetup X).V a) (i : (trivialSetup X).I a) :
    (trivialSetup X).ZRel a z i i :=
  Arc.nil (mem_univ a) hz i

end ZSetup

end EpGroupoid

end Polyfold
