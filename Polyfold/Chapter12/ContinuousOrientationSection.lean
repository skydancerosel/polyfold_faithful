import Polyfold.Chapter12.DyadicPathInduction
import Polyfold.Chapter6.OrientationMainClean

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6 and §12.5:
**a continuous section of `O_f` is a continuous orientation** (2021 Theorem 6.6.17 and
Definition 12.5.4, pp. 274–276 and p. 594; Theorem 6.6.17 is new in 2021; 2017: Definition 12.12).

# `Continuous (orSec o)` gives `IsContOrOn L univ o`

Part I's continuity of an orientation `o` over an open `U` is `IsContOrOn L U o`: `o` is carried
along by the transport along every sc-smooth path in `U`.  The text's "continuous section"
(Definition 12.5.4) is `Continuous (orSec o)` for the topology of `O_f`.  `continuousOn_orSec`
(Part I) gives the first ⇒ the second.  Here: the converse (gap G.158, part (b), of the wave-5
note of block OR).

* **`isContOrOn_univ_of_continuous_orSec`**: for any `LocalTransport L` of `Or^f` with two
  orientations at every smooth point, on an M-polyfold with `HasConnectedSmoothNbhds`, a section
  `o` with `Continuous (orSec o)` for `orTopology L` is `IsContOrOn L univ o`.  Near a smooth
  `x`, a continuous orientation `o₁` over `V ∋ x` with `o₁(x) = o(x)` exists
  (`exists_isContOrOn`); on a neighbourhood `U ⊆ V` with preconnected smooth part, the set where
  `o = o₁` is open and closed (the other orientation `o₁'` is continuous too), so it is all of
  `U ∩ X_∞`; then `isContOrOn_of_local_or`.
* **`isContOrOn_univ_iff_continuous`**: with Part I's hypotheses (tame, bump functions, tame
  Fredholm, sc⁺-sections through points), for **every** topology `t` with the properties of
  Theorem 6.6.17 (`IsOrientationTopology`), `Continuous[t] (orSec o) ↔ IsContOrOn L univ o`
  (`t = orTopology L` by `eq_orTopology_of`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

section General

variable {hf : B.IsScFredholmSection f} {L : LocalTransport PX fun x hs => Orx f hf x hs}

/-- The set where a section `o` with `Continuous (orSec o)` agrees with a continuous orientation
`o''` over `V ⊇ U` is open in `U ∩ X_∞`. -/
theorem isOpen_setOf_orSec_eq {o o'' : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    (ho : @Continuous _ _ _ (orTopology L) (orSec o)) {U V : Set X} (hUV : U ⊆ V)
    (h : IsContOrOn L V o'') :
    IsOpen {y : PX.smoothVal ⁻¹' U | orSec o (y : PX.SmoothLevel) = orSec o'' y} := by
  let := orTopology L
  have hσc : Continuous fun y : PX.smoothVal ⁻¹' U => orSec o (y : PX.SmoothLevel) :=
    ho.comp continuous_subtype_val
  refine isOpen_iff_mem_nhds.2 fun y hy => ?_
  have hmem : orSec o (y : PX.SmoothLevel) ∈ orBasic V o'' := by
    rw [show orSec o (y : PX.SmoothLevel) = orSec o'' y from hy]
    exact orSec_mem_orBasic (hUV y.2)
  filter_upwards [hσc.continuousAt.preimage_mem_nhds ((isOpen_orBasic h).mem_nhds hmem)]
    with z hz
  exact eq_orSec_of_mem_orBasic hz

/-- **A section `o` of `O_f` continuous for `orTopology L` is a continuous orientation over all
of `X`** (gap G.158 (b)), for a transport `L` of `Or^f` with two orientations at every smooth
point, on an M-polyfold whose smooth points have neighbourhoods with preconnected smooth part. -/
theorem isContOrOn_univ_of_continuous_orSec
    (htwo : ∀ y (hy : y ∈ PX.smoothSet), ∃ a b : Orx f hf y hy, a ≠ b ∧ ∀ c, c = a ∨ c = b)
    (hC : PX.HasConnectedSmoothNbhds) {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy}
    (ho : @Continuous _ _ _ (orTopology L) (orSec o)) : IsContOrOn L univ o := by
  classical
  refine isContOrOn_of_local_or isOpen_univ fun x _ hxs => ?_
  set xs : PX.SmoothLevel := ⟨x, hxs⟩
  obtain ⟨V, o₁, ho₁, -, hp⟩ := exists_isContOrOn L ⟨xs, o x hxs⟩
  obtain ⟨U, hUo, hxU, hUV, hconn⟩ := hC xs V ho₁.1 hp.1
  have hne : ∀ y (hy : y ∈ PX.smoothSet), ∃ c : Orx f hf y hy, c ≠ o₁ y hy := fun y hy =>
    let ⟨a₁, a₂, ha, _⟩ := htwo y hy
    if h : o₁ y hy = a₁ then ⟨a₂, h ▸ ha.symm⟩ else ⟨a₁, Ne.symm h⟩
  choose o₁' ho₁' using hne
  have hother : ∀ y hy (c : Orx f hf y hy), c ≠ o₁ y hy → c = o₁' y hy := fun y hy c hc =>
    let ⟨_, _, _, hall⟩ := htwo y hy
    eq_of_ne_of_ne_of_two hall hc (ho₁' y hy)
  have hco' : IsContOrOn L V o₁' := ⟨ho₁.1, fun γ hγ hγV x₀ x₁ h₀ h₁ hs₀ hs₁ =>
    hother _ _ _ fun e => ho₁' x₀ hs₀ ((L.transport γ hγ h₀ h₁ hs₀ hs₁).injective
      (e.trans (ho₁.2 γ hγ hγV h₀ h₁ hs₀ hs₁).symm))⟩
  have hoo' : ∀ y : PX.SmoothLevel, orSec o₁ y ≠ orSec o₁' y := fun y e =>
    ho₁' _ _ (eq_of_heq (Sigma.mk.inj_iff.1 e).2).symm
  set S := {y : PX.smoothVal ⁻¹' U | orSec o (y : PX.SmoothLevel) = orSec o₁ y}
  have hA : IsClopen S := by
    refine ⟨isOpen_compl_iff.1 ?_, isOpen_setOf_orSec_eq ho hUV ho₁⟩
    convert isOpen_setOf_orSec_eq ho hUV hco' using 1
    ext y
    change ¬ (orSec o (y : PX.SmoothLevel) = orSec o₁ y) ↔
      orSec o (y : PX.SmoothLevel) = orSec o₁' y
    rcases eq_orSec_or_eq_orSec hother (p := orSec o (y : PX.SmoothLevel)) rfl with h | h
    · rw [h]
      exact ⟨fun h' => (h' rfl).elim, fun e => (hoo' _ e).elim⟩
    · rw [h]
      exact ⟨fun _ => rfl, fun _ e => hoo' _ e.symm⟩
  have : PreconnectedSpace (PX.smoothVal ⁻¹' U) := Subtype.preconnectedSpace hconn
  have hxS : (⟨xs, hxU⟩ : PX.smoothVal ⁻¹' U) ∈ S := by
    change orSec o xs = orSec o₁ xs
    exact eq_orSec_of_mem_orBasic hp
  have hS : S = univ := (isClopen_iff.1 hA).resolve_left (Set.nonempty_iff_ne_empty.1 ⟨_, hxS⟩)
  refine ⟨U, hxU, (ho₁.mono_or hUo hUV).congr_or fun y hyU hys => ?_⟩
  have hy : (⟨⟨y, hys⟩, hyU⟩ : PX.smoothVal ⁻¹' U) ∈ S := hS ▸ mem_univ _
  exact (eq_of_heq (Sigma.mk.inj_iff.1 hy).2).symm

end General

section PartI

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

/-- **2021 Theorem 6.6.17 and Definition 12.5.4 (2017: Definition 12.12): the two
readings of "continuous orientation" agree.**  With Part I's hypotheses, for every topology `t`
on `O_f` with the properties of Theorem 6.6.17, `Continuous[t] (orSec o)` iff `o` is a continuous
orientation over `X` in Part I's sense (`IsContOrOn` for `orLocalTransport`). -/
theorem isContOrOn_univ_iff_continuous (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough)
    {t : TopologicalSpace (OrSpace f hf.toIsScFredholmSection)}
    (ht : IsOrientationTopology f hf.toIsScFredholmSection t)
    {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy} :
    @Continuous _ _ _ t (orSec o) ↔ IsContOrOn (orLocalTransport hX hbump hf hsec) univ o := by
  obtain rfl := eq_orTopology_of hX hbump hf hsec ht.isLocalHomeomorph ht.propagation
  refine ⟨isContOrOn_univ_of_continuous_orSec
    (fun _ hy => exists_two_orx _ hy hsec) PX.hasConnectedSmoothNbhds, fun h => ?_⟩
  let := orTopology (orLocalTransport hX hbump hf hsec)
  have h' := continuousOn_orSec h
  rw [preimage_univ] at h'
  exact continuousOn_univ.1 h'

end PartI

end Polyfold
