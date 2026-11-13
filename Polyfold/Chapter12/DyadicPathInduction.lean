import Polyfold.Chapter6.OrientationSpace

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
p. 594: a tool for the proof of the last sentence of **Theorem 12.5.3** (2017: Theorem 12.11).

# Induction along dyadic pieces of an sc-smooth path

Part I's transport of orientations along a path (`LocalTransport.transport`, Theorem 6.6.13) is
the composite of the push-forwards along the dyadic pieces of the path.  A property `R` of paths
which holds for paths in suitable small open sets (`hloc`) and passes from the two halves of a
path to the path (`hR`) holds for every sc-smooth path (`scPath_induction_or`): a Lebesgue number
of the covering of `[0, 1]` by the preimages of the small sets gives a level at which all dyadic
pieces are small.  A side condition `Q` (for instance "the path lies in `U`") is carried to the
halves.

* `scPath_induction_or`: the induction principle.
* `smoothTransPath_or_mem`: the reparametrization `s ↦ γ(χ(s))` by the smooth transition
  function `χ : ℝ → [0, 1]` takes its values in `γ([0, 1])`.
* `isContOrOn_of_local_or`: **continuity of an orientation (Part I's `IsContOrOn`) is local**;
  `IsContOrOn.mono_or`, `IsContOrOn.congr_or`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u v

section PathInduction

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **Induction along the dyadic pieces of a path.**  Let `Q` be a property of paths carried to
both halves, and `R` a property of paths which passes from the two halves to the path.  If every
point `γ(t)` of a path with `Q` has an open neighbourhood `V` such that every path with `Q` on
whose `[0, 1]` lies in `V` has `R`, then every sc-smooth path with `Q` has `R`. -/
theorem scPath_induction_or (Q R : ((Fin 1 → ℝ) → X) → Prop)
    (hQl : ∀ γ, (rnPolyfold 1).IsScSmoothMap PX γ → Q γ → Q (leftHalf γ))
    (hQr : ∀ γ, (rnPolyfold 1).IsScSmoothMap PX γ → Q γ → Q (rightHalf γ))
    (hR : ∀ γ, (rnPolyfold 1).IsScSmoothMap PX γ → Q γ → R (leftHalf γ) → R (rightHalf γ) →
      R γ)
    (hloc : ∀ γ, (rnPolyfold 1).IsScSmoothMap PX γ → Q γ → ∀ t ∈ Icc (0 : ℝ) 1,
      ∃ V : Set X, IsOpen V ∧ γ (pt1 t) ∈ V ∧ ∀ γ', (rnPolyfold 1).IsScSmoothMap PX γ' →
        Q γ' → (∀ s ∈ Icc (0 : ℝ) 1, γ' (pt1 s) ∈ V) → R γ')
    {γ : (Fin 1 → ℝ) → X} (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) (hQ : Q γ) : R γ := by
  let G : Set X → Prop := fun V => ∀ γ', (rnPolyfold 1).IsScSmoothMap PX γ' → Q γ' →
    (∀ s ∈ Icc (0 : ℝ) 1, γ' (pt1 s) ∈ V) → R γ'
  let Leb : ℝ → ((Fin 1 → ℝ) → X) → Prop := fun δ γ' => ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    b - a < δ → ∃ V, G V ∧ ∀ t ∈ Icc a b, γ' (pt1 t) ∈ V
  have key : ∀ N : ℕ, ∀ δ : ℝ, ∀ γ', (rnPolyfold 1).IsScSmoothMap PX γ' → Q γ' → Leb δ γ' →
      1 < 2 ^ N * δ → R γ' := by
    intro N
    induction N with
    | zero =>
      intro δ γ' hγ' hQ' hL hN
      rw [pow_zero, one_mul] at hN
      obtain ⟨V, hV, hγV⟩ := hL 0 1 le_rfl zero_le_one le_rfl (by linarith)
      exact hV γ' hγ' hQ' hγV
    | succ N ih =>
      intro δ γ' hγ' hQ' hL hN
      have hN' : 1 < 2 ^ N * (2 * δ) := by rw [pow_succ, mul_assoc] at hN; exact hN
      refine hR γ' hγ' hQ' (ih (2 * δ) _ (isScSmoothMap_leftHalf hγ') (hQl γ' hγ' hQ') ?_ hN')
        (ih (2 * δ) _ (isScSmoothMap_rightHalf hγ') (hQr γ' hγ' hQ') ?_ hN')
      · intro a b ha hab hb hba
        obtain ⟨V, hV, hγV⟩ := hL (a / 2) (b / 2) (by linarith) (by linarith) (by linarith)
          (by linarith)
        exact ⟨V, hV, fun t ht => hγV (t / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
      · intro a b ha hab hb hba
        obtain ⟨V, hV, hγV⟩ := hL ((1 + a) / 2) ((1 + b) / 2) (by linarith) (by linarith)
          (by linarith) (by linarith)
        exact ⟨V, hV, fun t ht => hγV ((1 + t) / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hc : Continuous fun t : ℝ => γ (pt1 t) :=
    (continuousOn_univ.1 hγ.continuousOn).comp (continuous_pi fun _ => continuous_id)
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (c := fun V : {V : Set X // IsOpen V ∧ G V} => (fun t : ℝ => γ (pt1 t)) ⁻¹' V.1)
    isCompact_Icc (fun V => V.2.1.preimage hc) (fun t ht => by
      obtain ⟨V, hVo, htV, hV⟩ := hloc γ hγ hQ t ht
      exact mem_iUnion.2 ⟨⟨V, hVo, hV⟩, htV⟩)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (1 / δ) (one_lt_two : (1 : ℝ) < 2)
  refine key N δ γ hγ hQ (fun a b ha hab hb hba => ?_) ((div_lt_iff₀ hδ).1 hN)
  obtain ⟨i, hsub⟩ := hball a ⟨ha, hab.trans hb⟩
  refine ⟨i.1, i.2.2, fun t ht => @hsub t ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-- The reparametrization of `γ` by the smooth transition function `χ` (`χ(0) = 0`, `χ(1) = 1`,
`0 ≤ χ ≤ 1`). -/
def smoothTransPath_or (γ : (Fin 1 → ℝ) → X) : (Fin 1 → ℝ) → X :=
  fun s => γ (pt1 (Real.smoothTransition (s 0)))

theorem isScSmoothMap_smoothTransPath_or {γ : (Fin 1 → ℝ) → X}
    (hγ : (rnPolyfold 1).IsScSmoothMap PX γ) :
    (rnPolyfold 1).IsScSmoothMap PX (smoothTransPath_or γ) :=
  isScSmoothMap_reparam hγ Real.smoothTransition.contDiff

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
/-- **The reparametrized path takes all its values in `γ([0, 1])`.** -/
theorem smoothTransPath_or_mem {γ : (Fin 1 → ℝ) → X} {V : Set X}
    (hγV : ∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ V) (q : Fin 1 → ℝ) : smoothTransPath_or γ q ∈ V :=
  hγV _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

end PathInduction

section Locality

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {hf : B.IsScFredholmSection f} {L : LocalTransport PX fun x hs => Orx f hf x hs}

/-- A continuous orientation over `U` is one over every open `V ⊆ U`. -/
theorem IsContOrOn.mono_or {U V : Set X} {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    (h : IsContOrOn L U o) (hV : IsOpen V) (hVU : V ⊆ U) : IsContOrOn L V o :=
  ⟨hV, fun γ hγ hγV => h.2 γ hγ fun s hs => hVU (hγV s hs)⟩

/-- A section agreeing over `U` with a continuous orientation over `U` is one. -/
theorem IsContOrOn.congr_or {U : Set X} {o o' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    (h : IsContOrOn L U o) (heq : ∀ y ∈ U, ∀ hs : y ∈ PX.smoothSet, o y hs = o' y hs) :
    IsContOrOn L U o' := by
  refine ⟨h.1, fun γ hγ hγU x₀ x₁ h₀ h₁ hs₀ hs₁ => ?_⟩
  rw [← heq x₀ (h₀ ▸ hγU 0 ⟨le_rfl, zero_le_one⟩) hs₀,
    ← heq x₁ (h₁ ▸ hγU 1 ⟨zero_le_one, le_rfl⟩) hs₁]
  exact h.2 γ hγ hγU h₀ h₁ hs₀ hs₁

/-- **Continuity of an orientation is local** (the locality lemma for Part I's `IsContOrOn`):
a section which is a continuous orientation over an open neighbourhood of every smooth point of
an open `U` is one over `U`.  The transport along a path in `U` is the composite of the
transports along small dyadic pieces (`scPath_induction_or`, `transport_halves`). -/
theorem isContOrOn_of_local_or {U : Set X} (hU : IsOpen U)
    {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    (h : ∀ x ∈ U, x ∈ PX.smoothSet → ∃ V : Set X, x ∈ V ∧ IsContOrOn L V o) :
    IsContOrOn L U o := by
  let R : ((Fin 1 → ℝ) → X) → Prop := fun γ => ∀ (hγ : (rnPolyfold 1).IsScSmoothMap PX γ)
    {x₀ x₁ : X} (h₀ : γ (pt1 0) = x₀) (h₁ : γ (pt1 1) = x₁) (hs₀ : x₀ ∈ PX.smoothSet)
    (hs₁ : x₁ ∈ PX.smoothSet), L.transport γ hγ h₀ h₁ hs₀ hs₁ (o x₀ hs₀) = o x₁ hs₁
  have key : ∀ γ, (rnPolyfold 1).IsScSmoothMap PX γ → (∀ q, γ q ∈ U) → R γ := by
    intro γ hγ hQ
    refine scPath_induction_or (fun γ => ∀ q, γ q ∈ U) R (fun γ _ hQ q => hQ _)
      (fun γ _ hQ q => hQ _) ?_ ?_ hγ hQ
    · intro γ _ _ hl hr hγ x₀ x₁ h₀ h₁ hs₀ hs₁
      have hsm := mem_smoothSet_of_isScSmoothMap hγ (pt1 (1 / 2))
      rw [L.transport_halves hγ h₀ h₁ rfl hs₀ hs₁ hsm, Equiv.trans_apply,
        hl (isScSmoothMap_leftHalf hγ) (leftHalf_zero.trans h₀) (leftHalf_one.trans rfl) hs₀ hsm,
        hr (isScSmoothMap_rightHalf hγ) (rightHalf_zero.trans rfl) (rightHalf_one.trans h₁) hsm
          hs₁]
    · intro γ hγ hQ t _
      obtain ⟨V, hxV, hV⟩ := h _ (hQ _) (mem_smoothSet_of_isScSmoothMap hγ (pt1 t))
      exact ⟨V, hV.1, hxV, fun γ' _ _ hγ'V hγ'' x₀ x₁ h₀ h₁ hs₀ hs₁ =>
        hV.2 γ' hγ'' hγ'V h₀ h₁ hs₀ hs₁⟩
  refine ⟨hU, fun γ hγ hγU x₀ x₁ h₀ h₁ hs₀ hs₁ => ?_⟩
  rw [← L.transport_reparam hγ Real.smoothTransition.contDiff Real.smoothTransition.zero
    Real.smoothTransition.one h₀ h₁ hs₀ hs₁]
  exact key (smoothTransPath_or γ) (isScSmoothMap_smoothTransPath_or hγ)
    (smoothTransPath_or_mem hγU) _ _ _ _ _

end Locality

end Polyfold
