import Polyfold.Chapter18.OrientationWitness

/-!
# The invariance of a continuous orientation along the morphisms, at smooth points

For Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Definition 12.5.4
(p. 594) and Theorem 12.5.3 (p. 594).

## What is formalized (namespace `Polyfold.EpStrongBundle`)

* **`eventually_isOrInvariantAt_iff_of_smooth`**: for a continuous orientation `o` over all of
  `X` and a morphism `σ` with smooth source and target, the invariance clause
  `σ'_* o_{s(σ')} = o_{t(σ')}` at the morphisms `σ'` near `σ` with smooth source and target holds
  iff it holds at `σ`.  This is `eventually_isOrInvariantAt_iff` without the hypothesis that
  every object is smooth.
* **`isOrInvariantAt_iff_of_continuous`**: along a continuous family `γ : T → 𝐗` of morphisms
  with smooth sources and targets, `T` preconnected, the invariance clause holds at one member
  iff it holds at every other.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

open StrongRetr

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

namespace EpStrongBundle

variable (E : EpStrongBundle X B) {f : Obj → W} (hF : E.IsScFredholmSectionFunctor f)
  (hsec : B.HasScPlusSectionsThrough)
  (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions)
  (hfT : B.IsScFredholmSectionTame f)
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]

/-- **The invariance at a morphism is locally constant among the morphisms with smooth source
and target**, for a continuous orientation `o` over all of `X` (Theorem 12.5.3): near a morphism
`σ` with smooth source and target, the invariance clause at `σ'` (with smooth source and target)
holds iff it holds at `σ`. -/
theorem eventually_isOrInvariantAt_iff_of_smooth
    {o : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy}
    (ho : IsContOrOn (orLocalTransport hX hbump hfT hsec) univ o) (σ : Mor)
    (hs : X.src σ ∈ X.PObj.smoothSet) (hs' : X.tgt σ ∈ X.PObj.smoothSet) :
    ∀ᶠ σ' in 𝓝 σ, X.src σ' ∈ X.PObj.smoothSet → X.tgt σ' ∈ X.PObj.smoothSet →
      (E.IsOrInvariantAt hF hsec o σ' ↔ E.IsOrInvariantAt hF hsec o σ) := by
  have hiff : ∀ τ (h₁ : X.src τ ∈ X.PObj.smoothSet) (h₂ : X.tgt τ ∈ X.PObj.smoothSet),
      E.IsOrInvariantAt hF hsec o τ ↔
        E.orMor hF hsec τ rfl rfl h₁ h₂ (o _ h₁) = o _ h₂ :=
    fun τ h₁ h₂ => ⟨fun h => h _ _, fun h _ _ => h⟩
  obtain ⟨hC, -, hval⟩ := E.theorem_12_5_3_push_hyp hF hsec hX hbump hfT σ rfl rfl hs hs' ho
  obtain ⟨V, hVo, hxV, hVN, hpath⟩ := exists_nhds_scPath_of_isOpen B hC.1
    (x := X.tgt σ) ⟨X.tgt_mem_sheetAt σ, mem_univ _⟩
  have hM : IsOpen ((X.sheetAt σ).carrier ∩ X.tgt ⁻¹' V) :=
    (X.sheetAt σ).isScDiffeoOn_tgt.isScSmoothOn.isOpen.inter (hVo.preimage X.continuous_tgt)
  filter_upwards [hM.mem_nhds ⟨X.mem_sheetAt σ, hxV⟩] with σ' hσ' hs₁ ht₁
  obtain ⟨γ, hγ, h₀, h₁, hγN⟩ := hpath _ hxV _ hσ'.2 hs' ht₁
  have e1 := hC.2 γ hγ (fun _ _ => hγN _) h₀ h₁ hs' ht₁
  have e2 := ho.2 γ hγ (fun _ _ => mem_univ _) h₀ h₁ hs' ht₁
  have hinv : (X.sheetAt σ).tgtInv (X.tgt σ') = σ' :=
    (X.sheetAt σ).isScDiffeoOn_tgt.left_inv σ' hσ'.1
  have hsϕ : (E.morIso σ).ϕ (X.tgt σ') ∈ X.PObj.smoothSet := by
    have h : X.src ((X.sheetAt σ).tgtInv (X.tgt σ')) ∈ X.PObj.smoothSet := by
      rw [hinv]; exact hs₁
    exact h
  have k1 := E.pullOrx_morIso_eq_orMor hF hsec σ (hVN hσ'.2).1 hsϕ ht₁ o
  have key : ∀ (τ : Mor) (_ : τ = σ') {z : Obj} (hx : X.src τ = z)
      (hx' : X.tgt τ = X.tgt σ') (hz : z ∈ X.PObj.smoothSet)
      (hz' : X.tgt σ' ∈ X.PObj.smoothSet),
      E.orMor hF hsec τ hx hx' hz hz' (o z hz) =
        E.orMor hF hsec σ' rfl rfl hs₁ ht₁ (o _ hs₁) := by
    rintro τ rfl z rfl hx' hz hz'
    rfl
  have T := ((orLocalTransport hX hbump hfT hsec).transport γ hγ h₀ h₁ hs'
    ht₁).apply_eq_iff_eq (x := (E.morIso σ).pullOrx hF.2 hF.2 (E.eqOn_morIso_of_functor hF σ)
      hsec hsec o (X.tgt σ) hs') (y := o _ hs')
  rw [e1, e2] at T
  have hB := k1.trans (key _ hinv (z := (E.morIso σ).ϕ (X.tgt σ')) rfl
    ((X.sheetAt σ).isScDiffeoOn_tgt.right_inv _ (hVN hσ'.2).1) hsϕ ht₁)
  refine (hiff σ' hs₁ ht₁).trans ((Iff.trans ?_ T).trans ?_)
  · rw [hB]
  · rw [hval]
    exact (hiff σ hs hs').symm

/-- **The invariance clause is constant along a connected family of morphisms with smooth
sources and targets**, for a continuous orientation `o` over all of `X`. -/
theorem isOrInvariantAt_iff_of_continuous
    {o : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy}
    (ho : IsContOrOn (orLocalTransport hX hbump hfT hsec) univ o)
    {T : Type*} [TopologicalSpace T] [PreconnectedSpace T] {γ : T → Mor} (hγ : Continuous γ)
    (hs : ∀ t, X.src (γ t) ∈ X.PObj.smoothSet) (hs' : ∀ t, X.tgt (γ t) ∈ X.PObj.smoothSet)
    (a b : T) :
    E.IsOrInvariantAt hF hsec o (γ a) ↔ E.IsOrInvariantAt hF hsec o (γ b) := by
  have hloc : IsLocallyConstant fun t : T => E.IsOrInvariantAt hF hsec o (γ t) :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun t => by
      have h := E.eventually_isOrInvariantAt_iff_of_smooth hF hsec hX hbump hfT ho (γ t)
        (hs t) (hs' t)
      filter_upwards [hγ.continuousAt.eventually h] with t' ht'
      exact propext (ht' (hs t') (hs' t'))
  exact (hloc.apply_eq_of_preconnectedSpace a b) ▸ Iff.rfl

end EpStrongBundle

end Polyfold
