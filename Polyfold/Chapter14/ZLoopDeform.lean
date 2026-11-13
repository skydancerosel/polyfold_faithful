import Polyfold.Chapter14.ZLoops

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 14,
§14.4, pp. 661–662: **Proposition 14.4.6 (1)** (the relations `∼_z` persist under small moves of
`z`) (2017 text: Proposition 14.5 (1)).

# Deforming z-loops

## The text, paraphrased

(Proposition 14.4.6 (1)) If `z₀ ∈ V̂_a` and `i ∼_{z₀} i'`, then `i ∼_z i'` for all `z ∈ V̂_a`
close to `z₀`.  (Proof) Near `z₀` the morphisms of a `z₀`-loop can be moved along with `z`
(Lemma 14.4.7), the moved morphisms compose to `1_z`, and since the `τ̂_{a,a'}` are locally
constant the same indices are related.

## What is formalized

* `ZData X`: B2's setting `ZSetup X` (Definitions 14.4.2–14.4.4) together with the three facts of
  §14.3 that §14.4 uses: the `V̂_a` are open, `cl_X(V̂_a) ⊆ Ũ(a)` ((14.33)), and every
  `τ̂_{a,a'}` is locally constant at the morphisms of `V̂_{a,a'}` (Proposition 14.3.4 with
  Proposition 14.3.8 (4): `V̂_{a,a'} ⊆ Ô_{a,a'}` and `τ̂_{a,a'}` is locally constant on the open
  set `Ô_{a,a'}`).  `ZData.trivial` shows the setting is satisfiable on every ep-groupoid.
* `ZData.Arc.eventually_srcInv`: a chain with an arc (B2's `ZSetup.Arc`) through `φ` deforms
  along any sheet `𝐔 ∋ φ`: for `z` near `s(φ)`, the morphism `(s|𝐔)⁻¹(z)` carries a chain with
  the same arc.  The proof moves one morphism at a time with the local inverses of `s` (sheets,
  Definition 7.1.4) and continuity of the multiplication; it does not need the finite
  natural representation of Lemma 14.4.7, which the text invokes for this step.
* **Proposition 14.4.6 (1)**: `ZData.proposition_14_4_6_1` (`∀ᶠ z in 𝓝 z₀, i ∼_z i'`), with the
  class form `ZData.eventually_zClass_subset` (`[i]_{∼_{z₀}} ⊆ [i]_{∼_z}` for `z` near `z₀`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

open SBLocalization

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- Composition is continuous along composable pairs (eventually composable suffices). -/
theorem tendsto_comp_of_eventually {X : EpGroupoid Obj Mor} {α : Type*} {l : Filter α}
    {a b : α → Mor} {a₀ b₀ : Mor} (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀))
    (hab : ∀ᶠ n in l, X.src (a n) = X.tgt (b n)) (h₀ : X.src a₀ = X.tgt b₀) :
    Tendsto (fun n => X.comp (a n) (b n)) l (𝓝 (X.comp a₀ b₀)) := by
  have hS : ContinuousOn (fun q : Mor × Mor => X.comp q.1 q.2)
      (MPolyfold.fibredProduct X.src X.tgt) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact X.continuous_comp_fibredProduct
  exact ((hS (a₀, b₀) h₀).tendsto).comp
    (tendsto_nhdsWithin_iff.2 ⟨ha.prodMk_nhds hb, hab⟩)

/-! ### Sheets: the local inverses of `s` -/

namespace Sheet

variable {X : EpGroupoid Obj Mor} (T : X.Sheet)

theorem isOpen_carrier : IsOpen T.carrier := T.isScDiffeoOn_src.isScSmoothOn.isOpen

theorem isOpen_srcSet : IsOpen T.srcSet := T.isScDiffeoOn_src.isScSmoothOn_inv.isOpen

theorem continuousAt_srcInv {z : Obj} (hz : z ∈ T.srcSet) : ContinuousAt T.srcInv z :=
  T.isScDiffeoOn_src.isScSmoothOn_inv.continuousOn.continuousAt (T.isOpen_srcSet.mem_nhds hz)

theorem srcInv_src {φ : Mor} (hφ : φ ∈ T.carrier) : T.srcInv (X.src φ) = φ :=
  T.isScDiffeoOn_src.left_inv φ hφ

theorem src_srcInv {z : Obj} (hz : z ∈ T.srcSet) : X.src (T.srcInv z) = z :=
  T.isScDiffeoOn_src.right_inv z hz

theorem src_mem {φ : Mor} (hφ : φ ∈ T.carrier) : X.src φ ∈ T.srcSet :=
  T.isScDiffeoOn_src.mapsTo hφ

/-- `(s|𝐔)⁻¹(z) → φ` as `z → s(φ)`. -/
theorem tendsto_srcInv {φ : Mor} (hφ : φ ∈ T.carrier) :
    Tendsto T.srcInv (𝓝 (X.src φ)) (𝓝 φ) := by
  have := T.continuousAt_srcInv (T.src_mem hφ)
  rwa [ContinuousAt, T.srcInv_src hφ] at this

/-- Near `s(φ)`, `(s|𝐔)⁻¹(z)` is the only morphism of `𝐔` with source `z`; in particular it is
`1_z` near `x` when `1_x ∈ 𝐔`. -/
theorem eventually_srcInv_eq_unit {x : Obj} (hx : X.unit x ∈ T.carrier) :
    ∀ᶠ z in 𝓝 x, T.srcInv z = X.unit z := by
  have h : ∀ᶠ z in 𝓝 x, X.unit z ∈ T.carrier :=
    X.continuous_unit.continuousAt.preimage_mem_nhds (T.isOpen_carrier.mem_nhds hx)
  filter_upwards [h] with z hz
  have := T.srcInv_src hz
  rwa [X.src_unit] at this

end Sheet

/-! ### The setting -/

/-- **The setting of §14.4** (pp. 657–664): B2's `ZSetup` (the index set `A ⊆ ∂X`, `Ũ(a)` with
the natural `G_a`-action, the `G_a`-invariant `V̂_a ⊆ Ũ(a)`, the index sets `I_a` and the
extended correspondences `τ̂_{a,a'}` with Definition 13.3.6 (1), (2)), together with the facts of
§14.3 that §14.4 uses:
* the `V̂_a` are open (Proposition 14.3.8 (1));
* `cl_X(V̂_a) ⊆ Ũ(a)` ((14.33), from Lemma 14.3.6 (1) and Lemma 13.1.1);
* `τ̂_{a,a'}` is locally constant at every morphism of `V̂_{a,a'}` (Proposition 14.3.4, through
  `V̂_{a,a'} ⊆ Ô_{a,a'}`, Proposition 14.3.8 (4)). -/
structure ZData (X : EpGroupoid Obj Mor) extends X.ZSetup where
  isOpen_V : ∀ a ∈ A, IsOpen (V a)
  closure_V_subset : ∀ a ∈ A, closure (V a) ⊆ (nbhd a).U
  locallyConstant : ∀ a ∈ A, ∀ a' ∈ A, ∀ φ, X.src φ ∈ V a → X.tgt φ ∈ V a' →
    ∀ᶠ ψ in 𝓝 φ, τ a a' ψ = τ a a' φ

namespace ZData

variable {X : EpGroupoid Obj Mor} (S : X.ZData)

/-- **Deformation of chains** (the step of the proof of Proposition 14.4.6 (1) that the text
draws from Lemma 14.4.7): if a chain with an arc from `i ∈ I_a` to `j ∈ I_b` has composite `φ`,
and `𝐔 ∋ φ` is a sheet, then for all `z` near `s(φ)` the morphism `(s|𝐔)⁻¹(z)` is the composite
of a chain with an arc from `i` to `j` (through the same `a_j` and the same index steps). -/
theorem Arc.eventually_srcInv {a b : Obj} {i : S.I a} {j : S.I b} {φ : Mor}
    (h : S.Arc a b i j φ) : ∀ T : X.Sheet, φ ∈ T.carrier →
      ∀ᶠ z in 𝓝 (X.src φ), S.Arc a b i j (T.srcInv z) := by
  induction h with
  | @nil ha z₀ hz i =>
    intro T hT
    rw [X.src_unit]
    have hV : ∀ᶠ z in 𝓝 z₀, z ∈ S.V a := (S.isOpen_V a ha).mem_nhds hz
    filter_upwards [hV, T.eventually_srcInv_eq_unit hT] with z hzV hzT
    rw [hzT]
    exact ZSetup.Arc.nil ha hzV i
  | @snoc b c i j k φ ψ h hc hs ht hp ih =>
    intro T hT
    rw [X.src_comp _ _ hs]
    have hb := h.props.2.1
    have hφt := h.props.2.2.2
    set T₁ := X.sheetAt φ
    set T₂ := X.sheetAt ψ
    have h₁ : Tendsto T₁.srcInv (𝓝 (X.src φ)) (𝓝 φ) := T₁.tendsto_srcInv (X.mem_sheetAt φ)
    -- the second morphism, moved along the target of the first
    have h₂ : Tendsto (fun z => T₂.srcInv (X.tgt (T₁.srcInv z))) (𝓝 (X.src φ)) (𝓝 ψ) := by
      have hc₂ := T₂.tendsto_srcInv (X.mem_sheetAt ψ)
      rw [hs] at hc₂
      exact hc₂.comp ((X.continuous_tgt.tendsto φ).comp h₁)
    have hE₁ : ∀ᶠ z in 𝓝 (X.src φ), z ∈ T₁.srcSet :=
      T₁.isOpen_srcSet.mem_nhds (X.src_mem_sheetAt φ)
    have hE₂ : ∀ᶠ z in 𝓝 (X.src φ), X.tgt (T₁.srcInv z) ∈ T₂.srcSet := by
      have : T₂.srcSet ∈ 𝓝 (X.tgt φ) := by
        rw [← hs]; exact T₂.isOpen_srcSet.mem_nhds (X.src_mem_sheetAt ψ)
      exact ((X.continuous_tgt.tendsto φ).comp h₁) this
    have hE₃ : ∀ᶠ z in 𝓝 (X.src φ), X.tgt (T₂.srcInv (X.tgt (T₁.srcInv z))) ∈ S.V c :=
      ((X.continuous_tgt.tendsto ψ).comp h₂) ((S.isOpen_V c hc).mem_nhds ht)
    have hE₄ : ∀ᶠ z in 𝓝 (X.src φ),
        S.τ b c (T₂.srcInv (X.tgt (T₁.srcInv z))) = S.τ b c ψ :=
      h₂ (S.locallyConstant b hb c hc ψ (by rw [hs]; exact hφt) ht)
    have hcomp : Tendsto (fun z => X.comp (T₂.srcInv (X.tgt (T₁.srcInv z))) (T₁.srcInv z))
        (𝓝 (X.src φ)) (𝓝 (X.comp ψ φ)) :=
      tendsto_comp_of_eventually h₂ h₁ (by
        filter_upwards [hE₂] with z hz using T₂.src_srcInv hz) hs
    have hE₅ : ∀ᶠ z in 𝓝 (X.src φ),
        X.comp (T₂.srcInv (X.tgt (T₁.srcInv z))) (T₁.srcInv z) ∈ T.carrier :=
      hcomp (T.isOpen_carrier.mem_nhds hT)
    have hE₀ := ih T₁ (X.mem_sheetAt φ)
    filter_upwards [hE₀, hE₁, hE₂, hE₃, hE₄, hE₅] with z h₀ h₁ h₂ h₃ h₄ h₅
    have hsrc : X.src (T₂.srcInv (X.tgt (T₁.srcInv z))) = X.tgt (T₁.srcInv z) :=
      T₂.src_srcInv h₂
    have e := ZSetup.Arc.snoc h₀ hc hsrc h₃ (by rw [h₄]; exact hp)
    have hz : X.src (X.comp (T₂.srcInv (X.tgt (T₁.srcInv z))) (T₁.srcInv z)) = z := by
      rw [X.src_comp _ _ hsrc, T₁.src_srcInv h₁]
    have := T.srcInv_src h₅
    rw [hz] at this
    rw [this]
    exact e

/-- **Proposition 14.4.6 (1), p. 661 (2017: Proposition 14.5 (1))**: if `i ∼_{z₀} i'` (so
`z₀ ∈ V̂_a`), then `i ∼_z i'` for all `z` near `z₀` (all of them lie in `V̂_a`, `ZRel.mem_V`). -/
theorem proposition_14_4_6_1 {a z₀ : Obj} {i i' : S.I a} (h : S.ZRel a z₀ i i') :
    ∀ᶠ z in 𝓝 z₀, S.ZRel a z i i' := by
  set T := X.sheetAt (X.unit z₀)
  have h₁ := Arc.eventually_srcInv S h T (X.mem_sheetAt _)
  rw [X.src_unit] at h₁
  filter_upwards [h₁, T.eventually_srcInv_eq_unit (X.mem_sheetAt _)] with z hz hT
  rw [hT] at hz
  exact hz

/-- Proposition 14.4.6 (1) in open-set form: an open `O ∋ z₀`, `O ⊆ V̂_a`, on which
`i ∼_z i'`. -/
theorem proposition_14_4_6_1_open {a z₀ : Obj} {i i' : S.I a} (h : S.ZRel a z₀ i i') :
    ∃ O : Set Obj, IsOpen O ∧ z₀ ∈ O ∧ O ⊆ S.V a ∧ ∀ z ∈ O, S.ZRel a z i i' := by
  obtain ⟨O, hO, hOo, hzO⟩ := mem_nhds_iff.1 (S.proposition_14_4_6_1 h)
  exact ⟨O, hOo, hzO, fun z hz => (hO hz).mem_V, fun z hz => hO hz⟩

/-- Proposition 14.4.6 (1), the classes: `[i]_{∼_{z₀}} ⊆ [i]_{∼_z}` for `z` near `z₀`
(`I_a` is finite). -/
theorem eventually_zClass_subset {a z₀ : Obj} (i : S.I a) :
    ∀ᶠ z in 𝓝 z₀, S.zClass a z₀ i ⊆ S.zClass a z i := by
  have : ∀ i' : S.I a, ∀ᶠ z in 𝓝 z₀, S.ZRel a z₀ i' i → S.ZRel a z i' i := by
    intro i'
    by_cases h : S.ZRel a z₀ i' i
    · filter_upwards [S.proposition_14_4_6_1 h] with z hz using fun _ => hz
    · exact Eventually.of_forall fun _ h' => absurd h' h
  filter_upwards [eventually_all.2 this] with z hz i' hi' using hz i' hi'

/-! ### Satisfiability -/

theorem exists_closure_subset_natNbhd (a : Obj) : ∃ N N' : X.NatNbhd a,
    N'.rep = N.rep ∧ N'.U ⊆ N.U ∧ closure N'.U ⊆ N.U := by
  obtain ⟨N, -, -⟩ := X.exists_natNbhd_isProperSubset a isOpen_univ (mem_univ a)
  obtain ⟨W, hWo, haW, hWcl⟩ : ∃ W : Set Obj, IsOpen W ∧ a ∈ W ∧ closure W ⊆ N.U := by
    obtain ⟨W, ⟨hW, hWo⟩, hWcl⟩ :=
      (closed_nhds_basis a).mem_iff.1 (N.isOpen_U.mem_nhds N.mem_U)
    obtain ⟨O, hOW, hOo, haO⟩ := mem_nhds_iff.1 hW
    exact ⟨O, hOo, haO, (closure_minimal hOW hWo).trans hWcl⟩
  obtain ⟨N', hrep, hsub⟩ := N.exists_restrict_subset hWo haW
  exact ⟨N, N', hrep, fun y hy => (hsub hy).1,
    (closure_mono fun y hy => (hsub hy).2).trans hWcl⟩

variable (X) in
/-- **The setting is satisfiable** on every ep-groupoid, with `A = X`: `Ũ(a)` an open
neighbourhood with the natural `G_a`-action, `V̂_a` a smaller one with the same action and
`cl_X(V̂_a) ⊆ Ũ(a)`, one-point index sets and constant `τ̂` (B2's `trivialSetup` with smaller
`V̂_a`). -/
def trivial : X.ZData where
  A := univ
  nbhd a := (exists_closure_subset_natNbhd (X := X) a).choose
  V a := (exists_closure_subset_natNbhd (X := X) a).choose_spec.choose.U
  V_subset a _ := (exists_closure_subset_natNbhd (X := X) a).choose_spec.choose_spec.2.1
  mapsTo_V a _ g := by
    have h := (exists_closure_subset_natNbhd (X := X) a).choose_spec.choose_spec.1
    have := (exists_closure_subset_natNbhd (X := X) a).choose_spec.choose.mapsTo_Φ g
    rwa [h] at this
  I _ := PUnit.{u + 1}
  τ _ _ _ := IndexCorr.ofEquiv (Equiv.refl PUnit.{u + 1})
  diag _ _ _ _ _ :=
    IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _, fun _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  swap _ _ _ _ _ _ _ :=
    IndexCorr.mk_eq_mk.2 ⟨Equiv.refl _, fun _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  isOpen_V a _ := (exists_closure_subset_natNbhd (X := X) a).choose_spec.choose.isOpen_U
  closure_V_subset a _ := (exists_closure_subset_natNbhd (X := X) a).choose_spec.choose_spec.2.2
  locallyConstant _ _ _ _ _ _ _ := Eventually.of_forall fun _ => rfl

/-- The trivial setting is nonempty: every `a` lies in its `V̂_a`, and `i ∼_a i`. -/
theorem trivial_zRel (a : Obj) (i : (trivial X).I a) : (trivial X).ZRel a a i i :=
  ZSetup.Arc.nil (mem_univ a) (exists_closure_subset_natNbhd (X := X) a).choose_spec.choose.mem_U i

end ZData

end EpGroupoid

end Polyfold
