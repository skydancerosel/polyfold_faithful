import Polyfold.Chapter19.CoveringTopology

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19, §19.7
"Covering Constructions", pp. 916–922: **Definition 19.7.16**, **Lemma 19.7.17**,
**Proposition 19.7.18** (the natural topology `T_{|A|}` and the map `|P| : |A| → |B|`) and
**Lemma 19.7.21**.  Numbers and pages are the 2021 text's.

## The text, paraphrased

(Definition 19.7.16) `W ⊂ |A|` belongs to `T_{|A|}` if every `z̄ ∈ W` has a representative `β`
of `|P|(z̄)`, a `Ψ̂ ∈ F̂(β)`, `Ψ̂ : E → A`, and an open `V ⊂ E` with `z̄ ∈ |Ψ̂(V)| ⊂ W`.
(Lemma 19.7.17) (1) `T_{|A|}` is a locally metrizable topology; (2) every `|Ψ̂(V)|` is open and
`|Ψ̂| : |E| → |Ψ̂(E)|` is a homeomorphism onto an open subset.  (Proposition 19.7.18) `|P|` is a
surjective local homeomorphism; the proof shows `P⁻¹(Ψ(O_β)) = Ψ̂(E)` and (19.34)
`|P|⁻¹(|Ψ(O_β)|) = |Ψ̂(E)|`.

## What is formalized

* `CoveringBasicConstruction.NatOpenA` (**Definition 19.7.16**, literally).
* The step of the proof of Lemma 19.7.17 (1): `exists_nbhd_hat` (for `ĥ ∈ M(Ψ̂, Ψ̂')` and an open
  `V' ∋ t(ĥ)` there is an open `N ∋ s(ĥ)` with `|Ψ̂(N)| ⊂ |Ψ̂'(V')|`), under `IsCompatible`.
* **Lemma 19.7.17**, under `IsCompatible` and `HasClassUniformizers`: `natTopA` (the topology),
  `lemma_19_7_17_one_hyp` (closure properties and local metrizability), `isOpen_image_hat`,
  `continuous_π_hat`, `lemma_19_7_17_two_hyp` (`|Ψ̂|` is an open embedding of `|E|`).
* **Proposition 19.7.18**, the parts that hold as we read them: `preimage_range_obj` and
  `preimage_range_orbitMap` (`P⁻¹(Ψ(O_β)) = Ψ̂(E)` and (19.34)), `surjective_orbitMap`,
  `finite_fiber_orbitMap`, `continuous_orbitMap`, `isOpenMap_orbitMap`, collected in
  `proposition_19_7_18_hyp`.  That `|P|` is a local homeomorphism does not hold as we read it
  (`not_proposition_19_7_18`, `CoveringCounterexamples.lean`); it holds where `|τ̂|` is one
  (`isLocalHomeomorphOn_orbitMap_of_τ_hyp`, through (19.35), `orbitMap_hat_comm`), in particular
  where the isotropy criterion `isLocalHomeomorphOn_orbitMap_of_isotropy_surjective` applies.
* **Lemma 19.7.21** (`lemma_19_7_21`), from Propositions 19.4.4, 19.4.5, Theorem 19.4.6 and
  Proposition 19.7.13.

## Readings

* Lemma 19.7.17 (1) uses, in the proof of closure under intersections, that the top target maps
  `t̂` are continuous (through Proposition 19.7.15 (2)); we assume `IsCompatible`.  "`∅` and `|A|`
  belong to `T`" needs that every class of `B` has a representative `β` with `F̂(β) ≠ ∅`
  (`HasClassUniformizers`, as in Theorem 19.2.2).  "Locally metrizable" is read through
  (2): every point has the open neighbourhood `|Ψ̂(E)| ≅ |E|`, and `|E|` is locally metrizable
  (Theorem 7.3.1).  Both hypotheses hold in `absBasic` (`CoveringCounterexamples.lean`:
  `absBasic_isCompatible`, `absBasic_hasClassUniformizers`), where `natTopA` is the orbit-space
  topology of `|A| ≅ ℝ`.
* The proof of Proposition 19.7.18 infers from "`|τ̂|` is a surjective local homeomorphism" that
  `|P|` is one on `Ŵ`; `|τ̂| : |E| → |G ⋉ O|` is continuous, open, surjective with finite
  fibres, but it is a local homeomorphism only where the isotropy maps onto `G` (Chapter 19's
  `isLocalHomeomorphOn_orbitMap_of_isotropy_surjective`); we state the properties that the argument
  gives.
-/

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

universe u

namespace GroupoidalCategory

open GroupoidStr (TransitionSet)
open EpGroupoid EpGroupoid.Examples

variable {A B : GroupoidalCategory.{u}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}

namespace CoveringBasicConstruction

variable (Bh : CoveringBasicConstruction P)

/-! ### Definition 19.7.16 -/

/-- **2021 Definition 19.7.16, p. 916**: the collection `T_{|A|}`: `W ⊂ |A|` belongs to it if every
`z̄ ∈ W` has a representative `β` of `|P|(z̄)`, a `Ψ̂ ∈ F̂(β)`, `Ψ̂ : E → A`, an `e ∈ E` with
`|Ψ̂(e)| = z̄` and an open `V ∋ e` of `E` with `|Ψ̂(V)| ⊂ W`. -/
def NatOpenA (W : Set A.OrbitSpace) : Prop :=
  ∀ z ∈ W, ∃ β, B.π β = P.orbitMap z ∧ ∃ Ψh ∈ Bh.hatU.F β, ∃ e : Ψh.ObjE,
    A.π (Ψh.hat.obj e) = z ∧ ∃ V : Set Ψh.ObjE, IsOpen V ∧ e ∈ V ∧
      (fun d => A.π (Ψh.hat.obj d)) '' V ⊆ W

theorem natOpenA_empty : Bh.NatOpenA ∅ := fun _ hz => absurd hz (notMem_empty _)

theorem natOpenA_sUnion {S : Set (Set A.OrbitSpace)} (hS : ∀ W ∈ S, Bh.NatOpenA W) :
    Bh.NatOpenA (⋃₀ S) := by
  rintro z ⟨W, hW, hz⟩
  obtain ⟨β, hβ, Ψh, hΨh, e, he, V, hV, heV, hsub⟩ := hS W hW z hz
  exact ⟨β, hβ, Ψh, hΨh, e, he, V, hV, heV, hsub.trans (subset_sUnion_of_mem hW)⟩

/-! ### Lifting points through `Ψ̂` -/

/-- `|Ψ̂(e)| ∈ |P|⁻¹(|Ψ(τ̂(e))|)`. -/
theorem orbitMap_π_hat {β : B.Obj} (Ψh : CoveringUniformizer P β) (e : Ψh.ObjE) :
    P.orbitMap (A.π (Ψh.hat.obj e)) = B.π (Ψh.Ψ.obj (Ψh.τ.obj e)) := by
  rw [GroupoidFunctor.orbitMap_π, Ψh.obj_comm]

/-- **Points over `|Ψ(o)|` lie in `|Ψ̂(τ̂⁻¹(o))|`** (the cartesian property with Definition 19.7.1):
if `|P|(z̄) = |Ψ(o)|` then `z̄ = |Ψ̂(e)|` for some `e` with `τ̂(e) = o`. -/
theorem exists_hat_of_orbitMap_eq (hP : IsFiniteToOneCovering P) {β : B.Obj}
    (Ψh : CoveringUniformizer P β) (o : Ψh.Ψ.O) {z : A.OrbitSpace}
    (hz : B.π (Ψh.Ψ.obj o) = P.orbitMap z) :
    ∃ e, Ψh.τ.obj e = o ∧ A.π (Ψh.hat.obj e) = z := by
  induction z using Quotient.inductionOn with
  | h α =>
  obtain ⟨φ, hφs, hφt⟩ := (B.π_eq_π_iff).1 (hz.symm.trans rfl :
    B.π (P.obj α) = B.π (Ψh.Ψ.obj o))
  let φh := hP.lift φ α hφs
  have hα' : P.obj (A.toGroupoidStr.tgt φh) = Ψh.Ψ.obj o := by
    rw [← P.tgt_mor, hP.P_lift, hφt]
  obtain ⟨e, he, hea⟩ := Ψh.cartesian_obj o _ hα'
  refine ⟨e, he, ?_⟩
  rw [hea]
  exact (A.π_eq_π_iff).2 ⟨φh, hP.src_lift φ α hφs, rfl⟩ |>.symm

/-- Every `z̄` over `|β|` is `|Ψ̂(e)|` for some `e`, for `Ψ̂ ∈ F̂(β)`. -/
theorem exists_hat_of_orbitMap_eq_pt (hP : IsFiniteToOneCovering P) {β : B.Obj}
    (Ψh : CoveringUniformizer P β) {z : A.OrbitSpace} (hz : B.π β = P.orbitMap z) :
    ∃ e, A.π (Ψh.hat.obj e) = z := by
  obtain ⟨e, -, he⟩ := exists_hat_of_orbitMap_eq hP Ψh Ψh.model.pt (by rw [Ψh.obj_pt]; exact hz)
  exact ⟨e, he⟩

/-- An isomorphism `Ψ̂(e) ≅ Ψ̂'(e')` gives an element of `M(Ψ̂, Ψ̂')` from `e` to `e'`. -/
theorem exists_trans_of_π_eq {β β' : B.Obj} {Ψh : CoveringUniformizer P β}
    {Ψh' : CoveringUniformizer P β'} {e : Ψh.ObjE} {e' : Ψh'.ObjE}
    (h : A.π (Ψh.hat.obj e) = A.π (Ψh'.hat.obj e')) :
    ∃ a : Ψh.Trans Ψh', a.src = e ∧ a.tgt = e' := by
  obtain ⟨φ, hφs, hφt⟩ := (A.π_eq_π_iff).1 h
  exact ⟨⟨e, φ, e', hφs, hφt⟩, rfl, rfl⟩

/-! ### The step of Lemma 19.7.17 -/

/-- **The step of the proof of Lemma 19.7.17 (1), p. 917**, under `IsCompatible`: for
`ĥ ∈ M(Ψ̂, Ψ̂')` and an open `V' ∋ t(ĥ)` the open set `N = ŝ(t̂⁻¹(V')) ∋ s(ĥ)` satisfies
`|Ψ̂(N)| ⊂ |Ψ̂'(V')|`. -/
theorem exists_nbhd_hat (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (x y : Bh.hatU.Unif) (a : x.Ψh.Trans y.Ψh) {V' : Set y.Ψh.ObjE} (hV' : IsOpen V')
    (ha : a.tgt ∈ V') :
    ∃ N : Set x.Ψh.ObjE, IsOpen N ∧ a.src ∈ N ∧
      ∀ d ∈ N, ∃ d' ∈ V', A.π (x.Ψh.hat.obj d) = A.π (y.Ψh.hat.obj d') := by
  refine ⟨Bh.srcHat x y '' (Bh.tgtHat x y ⁻¹' V'),
    (Bh.isLocalHomeomorph_srcHat hP x y).isOpenMap _ (hV'.preimage (hC x y)),
    ⟨toMHat a, ha, rfl⟩, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨Bh.tgtHat x y b, hb, (A.π_eq_π_iff).2
    ⟨(b : x.Ψh.Trans y.Ψh).mor, (b : x.Ψh.Trans y.Ψh).src_mor,
      (b : x.Ψh.Trans y.Ψh).tgt_mor⟩⟩

/-! ### Lemma 19.7.17 -/

/-- `|A| ∈ T_{|A|}` (Lemma 19.7.17 (1)), when every class of `B` has a representative `β` with
`F̂(β) ≠ ∅`. -/
theorem natOpenA_univ (hP : IsFiniteToOneCovering P) (hU : Bh.HasClassUniformizers) :
    Bh.NatOpenA univ := by
  intro z _
  obtain ⟨β, hβ, Ψh, hΨh⟩ := hU (P.orbitMap z)
  obtain ⟨e, he⟩ := exists_hat_of_orbitMap_eq_pt hP Ψh hβ
  exact ⟨β, hβ, Ψh, hΨh, e, he, univ, isOpen_univ, mem_univ _, subset_univ _⟩

/-- `T_{|A|}` is closed under finite intersections (Lemma 19.7.17 (1)), under `IsCompatible`. -/
theorem natOpenA_inter (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    {W₁ W₂ : Set A.OrbitSpace} (h₁ : Bh.NatOpenA W₁) (h₂ : Bh.NatOpenA W₂) :
    Bh.NatOpenA (W₁ ∩ W₂) := by
  rintro z ⟨hz₁, hz₂⟩
  obtain ⟨β₁, hβ₁, Ψ₁, hΨ₁, e₁, he₁, V₁, hV₁, heV₁, hsub₁⟩ := h₁ z hz₁
  obtain ⟨β₂, -, Ψ₂, hΨ₂, e₂, he₂, V₂, hV₂, heV₂, hsub₂⟩ := h₂ z hz₂
  obtain ⟨a, ha₁, ha₂⟩ := exists_trans_of_π_eq (he₁.trans he₂.symm)
  obtain ⟨N, hN, haN, hNf⟩ := Bh.exists_nbhd_hat hP hC ⟨β₁, Ψ₁, hΨ₁⟩ ⟨β₂, Ψ₂, hΨ₂⟩ a hV₂
    (ha₂ ▸ heV₂)
  refine ⟨β₁, hβ₁, Ψ₁, hΨ₁, e₁, he₁, N ∩ V₁, hN.inter hV₁, ⟨ha₁ ▸ haN, heV₁⟩, ?_⟩
  rintro _ ⟨d, ⟨hdN, hdV⟩, rfl⟩
  obtain ⟨d', hd', hdd'⟩ := hNf d hdN
  refine ⟨hsub₁ ⟨d, hdV, rfl⟩, ?_⟩
  change A.π (Ψ₁.hat.obj d) ∈ W₂
  rw [show A.π (Ψ₁.hat.obj d) = A.π (Ψ₂.hat.obj d') from hdd']
  exact hsub₂ ⟨d', hd', rfl⟩

/-- **The natural topology `T_{|A|}`** (Definition 19.7.16, Lemma 19.7.17 (1)), under
`IsCompatible` and `HasClassUniformizers`. -/
abbrev natTopA (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) : TopologicalSpace A.OrbitSpace where
  IsOpen := Bh.NatOpenA
  isOpen_univ := Bh.natOpenA_univ hP hU
  isOpen_inter _ _ := Bh.natOpenA_inter hP hC
  isOpen_sUnion _ := Bh.natOpenA_sUnion

/-- **2021 Lemma 19.7.17 (2), p. 916, openness**, under `IsCompatible` and
`HasClassUniformizers`: for `Ψ̂ ∈ F̂(β)` and an open `V ⊂ E`, `|Ψ̂(V)| ∈ T_{|A|}`. -/
theorem isOpen_image_hat (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) (x : Bh.hatU.Unif) {V : Set x.Ψh.ObjE} (hV : IsOpen V) :
    Bh.NatOpenA ((fun d => A.π (x.Ψh.hat.obj d)) '' V) := by
  rintro _ ⟨d, hdV, rfl⟩
  obtain ⟨β', hβ', Ψ', hΨ'⟩ := hU (P.orbitMap (A.π (x.Ψh.hat.obj d)))
  obtain ⟨e', he'⟩ := exists_hat_of_orbitMap_eq_pt hP Ψ' hβ'
  obtain ⟨a, ha₁, ha₂⟩ := exists_trans_of_π_eq he'
  obtain ⟨N, hN, haN, hNf⟩ := Bh.exists_nbhd_hat hP hC ⟨β', Ψ', hΨ'⟩ x a hV (ha₂ ▸ hdV)
  refine ⟨β', hβ', Ψ', hΨ', e', he', N, hN, ha₁ ▸ haN, ?_⟩
  rintro _ ⟨d'', hd'', rfl⟩
  obtain ⟨d''', hd''', h⟩ := hNf d'' hd''
  exact ⟨d''', hd''', h.symm⟩

/-- **2021 Lemma 19.7.17 (2), p. 916, continuity**, under `IsCompatible`: `e ↦ |Ψ̂(e)|` is
continuous `E → (|A|, T_{|A|})`. -/
theorem continuous_π_hat (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) (x : Bh.hatU.Unif) :
    Continuous[_, Bh.natTopA hP hC hU] fun d : x.Ψh.ObjE => A.π (x.Ψh.hat.obj d) := by
  let _inst := Bh.natTopA hP hC hU
  refine continuous_def.2 fun W hW => isOpen_iff_forall_mem_open.2 fun d hd => ?_
  obtain ⟨β', -, Ψ', hΨ', e', he', V', hV', heV', hsub'⟩ := hW _ hd
  obtain ⟨a, ha₁, ha₂⟩ := exists_trans_of_π_eq (he'.symm : A.π (x.Ψh.hat.obj d) = _)
  obtain ⟨N, hN, haN, hNf⟩ := Bh.exists_nbhd_hat hP hC x ⟨β', Ψ', hΨ'⟩ a hV' (ha₂ ▸ heV')
  refine ⟨N, fun d'' hd'' => ?_, hN, ha₁ ▸ haN⟩
  obtain ⟨d''', hd''', h⟩ := hNf d'' hd''
  change A.π (x.Ψh.hat.obj d'') ∈ W
  rw [h]
  exact hsub' ⟨d''', hd''', rfl⟩

/-- `|Ψ̂| : |E| → |A|` is injective (`Ψ̂` is full). -/
theorem injective_orbitMap_hat {β : B.Obj} (Ψh : CoveringUniformizer P β) :
    Injective Ψh.hat.orbitMap := by
  intro z z' h
  induction z using Quotient.inductionOn with
  | h e =>
  induction z' using Quotient.inductionOn with
  | h e' =>
  obtain ⟨φ, hφs, hφt⟩ := (A.π_eq_π_iff).1 h
  obtain ⟨ψ, hψs, hψt, -⟩ := (GroupoidFunctor.full_iff _).1 Ψh.full_hat e e' φ hφs hφt
  exact (GroupoidStr.π_eq_π_iff _).2 ⟨ψ, hψs, hψt⟩

/-- **2021 Lemma 19.7.17 (2), p. 916**, under `IsCompatible` and `HasClassUniformizers`:
`|Ψ̂| : |E| → |A|` is a homeomorphism onto the open subset `|Ψ̂(E)|` of `(|A|, T_{|A|})`. -/
theorem lemma_19_7_17_two_hyp (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) (x : Bh.hatU.Unif) :
    @IsOpenEmbedding _ _ _ (Bh.natTopA hP hC hU) x.Ψh.hat.orbitMap := by
  let _inst := Bh.natTopA hP hC hU
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ (injective_orbitMap_hat x.Ψh) ?_
  · exact continuous_quot_lift _ (Bh.continuous_π_hat hP hC hU x)
  · intro W hW
    have : x.Ψh.hat.orbitMap '' W =
        (fun d => A.π (x.Ψh.hat.obj d)) '' (x.Ψh.E.π ⁻¹' W) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        induction w using Quotient.inductionOn with
        | h e => exact ⟨e, hw, rfl⟩
      · rintro ⟨e, he, rfl⟩
        exact ⟨_, he, rfl⟩
    rw [this]
    exact Bh.isOpen_image_hat hP hC hU x (hW.preimage x.Ψh.E.continuous_π)

/-- **2021 Lemma 19.7.17 (1), p. 916**, under `IsCompatible` and `HasClassUniformizers`:
`T_{|A|}` contains `∅` and `|A|`, is closed under finite intersections and arbitrary unions, and
every point has an open neighbourhood homeomorphic to the locally metrizable `|E|`
(Theorem 7.3.1). -/
theorem lemma_19_7_17_one_hyp (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) :
    (Bh.NatOpenA ∅ ∧ Bh.NatOpenA univ ∧
      (∀ W₁ W₂, Bh.NatOpenA W₁ → Bh.NatOpenA W₂ → Bh.NatOpenA (W₁ ∩ W₂)) ∧
      ∀ S : Set (Set A.OrbitSpace), (∀ W ∈ S, Bh.NatOpenA W) → Bh.NatOpenA (⋃₀ S)) ∧
    ∀ z : A.OrbitSpace, ∃ x : Bh.hatU.Unif, z ∈ range x.Ψh.hat.orbitMap ∧
      @IsOpenEmbedding _ _ _ (Bh.natTopA hP hC hU) x.Ψh.hat.orbitMap := by
  refine ⟨⟨Bh.natOpenA_empty, Bh.natOpenA_univ hP hU, fun _ _ => Bh.natOpenA_inter hP hC,
    fun _ => Bh.natOpenA_sUnion⟩, fun z => ?_⟩
  obtain ⟨β, hβ, Ψh, hΨh⟩ := hU (P.orbitMap z)
  obtain ⟨e, he⟩ := exists_hat_of_orbitMap_eq_pt hP Ψh hβ
  exact ⟨⟨β, Ψh, hΨh⟩, ⟨Ψh.E.toGroupoidStr.π e, he⟩,
    Bh.lemma_19_7_17_two_hyp hP hC hU ⟨β, Ψh, hΨh⟩⟩

/-! ### Proposition 19.7.18 -/

/-- **The proof of Proposition 19.7.18, p. 919**: `P⁻¹(Ψ(O_β)) = Ψ̂(E)`. -/
theorem preimage_range_obj {β : B.Obj} (Ψh : CoveringUniformizer P β) :
    P.obj ⁻¹' range Ψh.Ψ.obj = range Ψh.hat.obj := by
  ext a
  constructor
  · rintro ⟨o, ho⟩
    obtain ⟨e, -, he⟩ := Ψh.cartesian_obj o a ho.symm
    exact ⟨e, he⟩
  · rintro ⟨e, rfl⟩
    exact ⟨Ψh.τ.obj e, (Ψh.obj_comm e).symm⟩

/-- **(19.34)**: `|P|⁻¹(|Ψ(O_β)|) = |Ψ̂(E)|`. -/
theorem preimage_range_orbitMap (hP : IsFiniteToOneCovering P) {β : B.Obj}
    (Ψh : CoveringUniformizer P β) :
    P.orbitMap ⁻¹' range (fun o => B.π (Ψh.Ψ.obj o)) = range fun e => A.π (Ψh.hat.obj e) := by
  ext z
  constructor
  · rintro ⟨o, ho⟩
    obtain ⟨e, -, he⟩ := exists_hat_of_orbitMap_eq hP Ψh o ho
    exact ⟨e, he⟩
  · rintro ⟨e, rfl⟩
    exact ⟨Ψh.τ.obj e, (orbitMap_π_hat Ψh e).symm⟩

/-- `|P|` is surjective (Proposition 19.7.18). -/
theorem surjective_orbitMap (hP : IsFiniteToOneCovering P) : Surjective P.orbitMap := by
  intro w
  induction w using Quotient.inductionOn with
  | h β =>
  obtain ⟨α, rfl⟩ := hP.surjective β
  exact ⟨A.π α, rfl⟩

/-- The fibres of `|P|` are finite: `|P|⁻¹(|β|) ⊂ |P⁻¹(β)|`. -/
theorem finite_fiber_orbitMap (hP : IsFiniteToOneCovering P) (w : B.OrbitSpace) :
    (P.orbitMap ⁻¹' {w}).Finite := by
  induction w using Quotient.inductionOn with
  | h β =>
  refine ((hP.finite_fiber β).image A.π).subset fun z hz => ?_
  induction z using Quotient.inductionOn with
  | h α =>
  obtain ⟨φ, hφs, hφt⟩ := (B.π_eq_π_iff).1 (hz : B.π (P.obj α) = B.π β)
  refine ⟨A.toGroupoidStr.tgt (hP.lift φ α hφs), ?_, ?_⟩
  · change P.obj _ = β
    rw [← P.tgt_mor, hP.P_lift, hφt]
  · exact ((A.π_eq_π_iff).2 ⟨_, hP.src_lift φ α hφs, rfl⟩).symm

/-- `|P| : (|A|, T_{|A|}) → (|B|, T_{|B|})` is continuous (Proposition 19.7.18). -/
theorem continuous_orbitMap (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) :
    Continuous[Bh.natTopA hP hC hU, Bh.toBasic.natTop hU.toBasic] P.orbitMap := by
  let _ := Bh.natTopA hP hC hU
  let _ := Bh.toBasic.natTop hU.toBasic
  refine continuous_def.2 fun W hW z hz => ?_
  obtain ⟨β, hβ, Ψh, hΨh⟩ := hU (P.orbitMap z)
  obtain ⟨e, he⟩ := exists_hat_of_orbitMap_eq_pt hP Ψh hβ
  have hΨ : Ψh.Ψ ∈ Bh.toBasic.U.F β := ⟨Ψh, hΨh, rfl⟩
  have hc : Continuous fun d : Ψh.ObjE => B.π (Ψh.Ψ.obj (Ψh.τ.obj d)) :=
    (Bh.toBasic.continuous_π_obj hU.toBasic hΨ).comp
      (Bh.isLocalHomeomorph_τ ⟨β, Ψh, hΨh⟩).continuous
  refine ⟨β, hβ, Ψh, hΨh, e, he, _, hW.preimage hc, ?_, ?_⟩
  · change B.π (Ψh.Ψ.obj (Ψh.τ.obj e)) ∈ W
    rw [← orbitMap_π_hat, he]
    exact hz
  · rintro _ ⟨d, hd, rfl⟩
    change P.orbitMap (A.π (Ψh.hat.obj d)) ∈ W
    rw [orbitMap_π_hat]
    exact hd

/-- `|P| : (|A|, T_{|A|}) → (|B|, T_{|B|})` is open (Proposition 19.7.18). -/
theorem isOpenMap_orbitMap (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) :
    @IsOpenMap _ _ (Bh.natTopA hP hC hU) (Bh.toBasic.natTop hU.toBasic) P.orbitMap := by
  let _ := Bh.natTopA hP hC hU
  let _ := Bh.toBasic.natTop hU.toBasic
  intro W hW
  refine isOpen_iff_forall_mem_open.2 ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨β, -, Ψh, hΨh, e, he, V, hV, heV, hsub⟩ := hW z hz
  have hΨ : Ψh.Ψ ∈ Bh.toBasic.U.F β := ⟨Ψh, hΨh, rfl⟩
  refine ⟨_, ?_, Bh.toBasic.theorem_19_2_2_two hU.toBasic hΨ
    ((Bh.isLocalHomeomorph_τ ⟨β, Ψh, hΨh⟩).isOpenMap V hV), ⟨Ψh.τ.obj e, ⟨e, heV, rfl⟩, ?_⟩⟩
  · rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨_, hsub ⟨d, hd, rfl⟩, orbitMap_π_hat Ψh d⟩
  · change B.π (Ψh.Ψ.obj (Ψh.τ.obj e)) = P.orbitMap z
    rw [← orbitMap_π_hat, he]

/-- **2021 Proposition 19.7.18, p. 919**, the parts that hold as we read them (under
`IsCompatible` and `HasClassUniformizers`): `|P| : (|A|, T_{|A|}) → (|B|, T_{|B|})` is continuous,
open and surjective with finite fibres, `P⁻¹(Ψ(O_β)) = Ψ̂(E)` and (19.34)
`|P|⁻¹(|Ψ(O_β)|) = |Ψ̂(E)|` for every `Ψ̂ ∈ F̂(β)`.  That `|P|` is a local homeomorphism does not
hold as we read it (`not_proposition_19_7_18`). -/
theorem proposition_19_7_18_hyp (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) :
    Continuous[Bh.natTopA hP hC hU, Bh.toBasic.natTop hU.toBasic] P.orbitMap ∧
      @IsOpenMap _ _ (Bh.natTopA hP hC hU) (Bh.toBasic.natTop hU.toBasic) P.orbitMap ∧
      Surjective P.orbitMap ∧ (∀ w, (P.orbitMap ⁻¹' {w}).Finite) ∧
      ∀ β, ∀ Ψh ∈ Bh.hatU.F β, P.obj ⁻¹' range Ψh.Ψ.obj = range Ψh.hat.obj ∧
        P.orbitMap ⁻¹' range (fun o => B.π (Ψh.Ψ.obj o)) = range fun e => A.π (Ψh.hat.obj e) :=
  ⟨Bh.continuous_orbitMap hP hC hU, Bh.isOpenMap_orbitMap hP hC hU, surjective_orbitMap hP,
    finite_fiber_orbitMap hP, fun _ Ψh _ => ⟨preimage_range_obj Ψh, preimage_range_orbitMap hP Ψh⟩⟩

/-- `|P| ∘ |Ψ̂| = |Ψ| ∘ |τ̂|` on `|E|` (the diagram (19.35)). -/
theorem orbitMap_hat_comm {β : B.Obj} (Ψh : CoveringUniformizer P β) (w : Ψh.E.OrbitSpace) :
    P.orbitMap (Ψh.hat.orbitMap w) = Ψh.Ψ.functor.orbitMap (Ψh.τ.orbitMap w) := by
  induction w using Quotient.inductionOn with
  | h e => exact orbitMap_π_hat Ψh e

/-- **The local form of Proposition 19.7.18, p. 919** (the "if" direction of the isotropy
criterion, transported by (19.35)), under `IsCompatible` and `HasClassUniformizers`: where
`|τ̂| : |E| → |G ⋉ O|` is a local homeomorphism, `|P|` is one on the image under `|Ψ̂|`.  For a
model whose `E` is a translation groupoid (the sheet models of Definition 17.8.4), Chapter 19's
`isLocalHomeomorphOn_orbitMap_of_isotropy_surjective` gives the hypothesis at `|e|` whenever
`τ̂` maps `Aut(e)` onto `Aut(τ̂ e)`. -/
theorem isLocalHomeomorphOn_orbitMap_of_τ_hyp (hP : IsFiniteToOneCovering P)
    (hC : Bh.IsCompatible) (hU : Bh.HasClassUniformizers) (x : Bh.hatU.Unif)
    {S : Set x.Ψh.E.OrbitSpace} (hS : IsLocalHomeomorphOn x.Ψh.τ.orbitMap S) :
    @IsLocalHomeomorphOn _ _ (Bh.natTopA hP hC hU) (Bh.toBasic.natTop hU.toBasic) P.orbitMap
      (x.Ψh.hat.orbitMap '' S) := by
  let _ := Bh.natTopA hP hC hU
  let _ := Bh.toBasic.natTop hU.toBasic
  have hj := Bh.lemma_19_7_17_two_hyp hP hC hU x
  have hΨ : x.Ψh.Ψ ∈ Bh.toBasic.U.F x.β := ⟨x.Ψh, x.mem, rfl⟩
  have hk := (Bh.toBasic.theorem_19_2_2_three hU.toBasic hΨ).1
  rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨N, hN, hemb⟩ := (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).1 hS w hw
  obtain ⟨N', hN'N, hN'o, hwN'⟩ := mem_nhds_iff.1 hN
  have hinjN : InjOn x.Ψh.τ.orbitMap N' :=
    (injOn_iff_injective.2 hemb.injective).mono hN'N
  have hopen : IsOpen (x.Ψh.hat.orbitMap '' N') := hj.isOpenMap _ hN'o
  refine ⟨_, hopen.mem_nhds ⟨w, hwN', rfl⟩, ?_⟩
  refine isOpenEmbedding_iff_continuous_injective_isOpenMap.2 ⟨?_, ?_, ?_⟩
  · exact (Bh.continuous_orbitMap hP hC hU).comp continuous_subtype_val
  · rintro ⟨_, ⟨v, hv, rfl⟩⟩ ⟨_, ⟨v', hv', rfl⟩⟩ h
    have h' : P.orbitMap (x.Ψh.hat.orbitMap v) = P.orbitMap (x.Ψh.hat.orbitMap v') := h
    rw [orbitMap_hat_comm, orbitMap_hat_comm] at h'
    have hvv : v = v' := hinjN hv hv' (hk.injective h')
    subst hvv
    rfl
  · exact (Bh.isOpenMap_orbitMap hP hC hU).comp hopen.isOpenMap_subtype_val

/-! ### Lemma 19.7.21 -/

/-- **2021 Lemma 19.7.21, p. 922**, under `HasClassUniformizers` (`F(α) ≠ ∅`, the standing reading
of §17.1): (1) if `(F, 𝓕)` satisfies the properness condition, `T_{|B|}` is regular, Hausdorff and
locally metrizable; (2) every `M(Ψ, Ψ')` and `M(Ψ̂, Ψ̂')` is metrizable (with or without the
properness condition); (3) if `(F, 𝓕)` satisfies the properness condition and `T_{|B|}` is
paracompact, `T_{|B|}` is metrizable. -/
theorem lemma_19_7_21 (hP : IsFiniteToOneCovering P) (hU : Bh.HasClassUniformizers) :
    (Bh.toBasic.PropernessV2 hU.toBasic →
      @RegularSpace _ (Bh.toBasic.natTop hU.toBasic) ∧ @T2Space _ (Bh.toBasic.natTop hU.toBasic) ∧
        ∀ z : B.OrbitSpace, ∃ W : Set B.OrbitSpace, IsOpen[Bh.toBasic.natTop hU.toBasic] W ∧
          z ∈ W ∧ @MetrizableSpace W (@instTopologicalSpaceSubtype _ _
            (Bh.toBasic.natTop hU.toBasic))) ∧
      (∀ x y : Bh.hatU.Unif, MetrizableSpace (Bh.MB x y) ∧ MetrizableSpace (Bh.MHat x y)) ∧
      (Bh.toBasic.PropernessV2 hU.toBasic → @ParacompactSpace _ (Bh.toBasic.natTop hU.toBasic) →
        @MetrizableSpace _ (Bh.toBasic.natTop hU.toBasic)) := by
  refine ⟨fun hv => ?_, fun x y => ⟨Bh.toBasic.metrizableSpace_M x.toUnif y.toUnif,
    Bh.metrizableSpace_MHat hP x y⟩, fun hv hpc => Bh.toBasic.theorem_19_4_6_two hU.toBasic hv hpc⟩
  let _ := Bh.toBasic.natTop hU.toBasic
  obtain ⟨h2, hcr⟩ := Bh.toBasic.proposition_19_4_5 hU.toBasic hv
  exact ⟨inferInstance, h2, Bh.toBasic.theorem_19_2_2_five hU.toBasic⟩

end CoveringBasicConstruction

end GroupoidalCategory

end Polyfold
