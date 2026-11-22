import Polyfold.Chapter19.CoveringOrbitTopology
import Polyfold.Chapter17.ProperCoveringModelRestrict

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19, §19.7
"Covering Constructions", pp. 920–922: **Lemma 19.7.19** (p. 920) and **Corollary 19.7.20 (1),
(2)** (pp. 921–922), the local structure of `|P| : |A| → |B|`.  Numbers and pages are the 2021
text's.

# The local structure of `|P|`

## The text, paraphrased

(p. 920) For a connected proper covering model `τ̂ : E → G ⋉ O` with `E = ⊔_{y ∈ τ̂⁻¹(ō)} U(y)`,
`y ∼ y'` on `τ̂⁻¹(ō)` means that there is a morphism `y → y'`.  (Lemma 19.7.19) `y ∼ y'` if and
only if `|U(y)| = |U(y')|`.  *Proof*: for `ĝ : y → y'` the set `Σ_y` of morphisms with source in
`U(y)` and group element `g` is homeomorphic to the connected `U(y)` by `s`, so `t(Σ_y)` is a
connected set containing `y'` and lies in `U(y')`; conversely a morphism from `U(y)` to `U(y')` is
joined inside `Σ_y` by a path to one with source `y`, whose target stays in `U(y')` and is `y'`.
(p. 921) The number `k` of classes divides `ℓ = #τ̂⁻¹(ō)`.
(Corollary 19.7.20) For `z ∈ |B|`, open neighbourhoods `U(z)` of `z` and `Û` of
`|P|⁻¹(z) = {z̄₁, …, z̄ₖ}`, `β` with `|β| = z` and `Ψ̂ ∈ F̂(β)`, there is a small connected
`G`-invariant open neighbourhood `O'` of `ō` such that `E' = τ̂⁻¹(O')` is the disjoint union of
connected open `V(y)`, `y ∈ τ̂⁻¹(ō)`, the restriction `τ̂' : E' → G ⋉ O'` is a connected proper
covering model, and (1) `W(z) := |Ψ(O')| ⊂ U(z)`; (2) there are mutually inequivalent
`a₁, …, aₖ ∈ τ̂⁻¹(ō)` whose classes exhaust `τ̂⁻¹(ō)`, every `V(aᵢ)` is `G_{aᵢ}`-invariant, the
`W(z̄ᵢ) := |Ψ̂(V(aᵢ))|` are mutually disjoint and (19.38) `|P|⁻¹(W(z)) = ⊔ W(z̄ᵢ) ⊂ Û`;
(3) `|P| : W(z̄ᵢ) → W(z)` is a homeomorphism.

## What is formalized

* `ProperCoveringModel.cutSheet O' y` (`V(y) = U(y) ∩ τ̂⁻¹(O')`) and the key step of the proof of
  Lemma 19.7.19 for any preconnected `S ∋ ō` in place of `O`: `sheetIndex_tgt_liftMor_σ` (on
  `o ∈ S`, the sheet of `t(Γ⁻¹((g, o), τ_y⁻¹(o)))` is that of its value at `ō`), and its two
  consequences `liftMor_mem_cutSheet` (a morphism `y → y'` moves `V(y)` into `V(y')`, for `S`
  invariant) and `liftMor_of_mem_cutSheet` (a morphism from `V(y)` to `V(y')` gives one `y → y'`).
* **Lemma 19.7.19**: `ProperCoveringModel.lemma_19_7_19`.
* The remark "`k` divides `ℓ`" after Lemma 19.7.19 does not hold as we read it:
  `not_remark_19_7_19_divides` (Chapter 19's `CoveringLocalExamples.lean`, a sheet model with
  `ℓ = 3`, `k = 2`).
* `GroupoidStr.exists_reprs`: a set of mutually inequivalent representatives of the classes met by
  a set of objects.
* `CoveringUniformizer.imageB` (`|Ψ(O')|`), `CoveringUniformizer.imageA` (`|Ψ̂(V)|`).
* **Corollary 19.7.20 (1), (2)**: `CoveringBasicConstruction.corollary_19_7_20_hyp`, under
  `IsCompatible` and `HasClassUniformizers` (the hypotheses of `natTopA`, Lemma 19.7.17): the
  `O'` of Proposition 17.8.6 with its connected model, the `V(y)`, (1) and (2) with (19.38) and
  `|P|⁻¹(z) = {|Ψ̂(a)| : a ∈ S}`.  Corollary 19.7.20 (3) does not hold as we read it
  (`not_corollary_19_7_20_three`, Chapter 19's `CoveringCounterexamples.lean`).
* Consequences: `exists_isOpen_preimage_subset` (every open `Û ⊇ |P|⁻¹(z)` contains some
  `|P|⁻¹(W)`, `W ∋ z` open), `isClosedMap_orbitMap` (`|P|` is a closed map), and
  `evenlyCovered_orbitMap` (Theorem 19.7.25 (4a), Definition 17.8.1 (3)).

## Readings

* Lemma 19.7.19: "`τ̂ : E → G ⋉ O` a connected local ep-groupoid covering model" is a connected
  proper covering model (Definition 17.8.4, `ProperCoveringModel.Connected`); `|U(y)|` is the image
  `π(U(y))` in `|E|`.  The text's path inside `Σ_y` is replaced by the connected set
  `o ↦ Γ⁻¹((g, o), τ_y⁻¹(o))`, `o ∈ O` (as in Lemma 17.8.8, Chapter 17), on which
  `ψ ↦ y_{t ψ}` (Lemma 17.8.7) is constant.
* Corollary 19.7.20: `V(y) = U(y) ∩ τ̂⁻¹(O')` (the sheets of the restricted model); "`V(aᵢ)` is
  invariant under the `G_{aᵢ}`-action": for every `φ : aᵢ → aᵢ` and `e ∈ V(aᵢ)` the morphism with
  source `e` and group element `g_φ` ends in `V(aᵢ)`.  The `z̄ᵢ` are the `|Ψ̂(aᵢ)|`, `aᵢ ∈ S`;
  "mutually not equivalent" is: no morphism `aᵢ → aⱼ` for `aᵢ ≠ aⱼ`.  The neighbourhoods `U(z)`,
  `Û` are open in `T_{|B|}`, `T_{|A|}`.  The text's proof only needs `O'` small enough that
  `|Ψ̂(V(aᵢ))| ⊂ Û` and `|Ψ(O')| ⊂ U(z)`; we take `O'` from Proposition 17.8.6 inside
  `⋂_{a ∈ τ̂⁻¹(ō)} τ̂(U(a) ∩ |Ψ̂|⁻¹(Û)) ∩ |Ψ|⁻¹(U(z))`.
-/

open Set Function Topology

noncomputable section

namespace Polyfold

open EpGroupoid EpGroupoid.Examples

universe u v

/-! ### Lemma 19.7.19 -/

namespace ProperCoveringModel

variable {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  {O : Type u} [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O]
  {P : MPolyfold O} {hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y}
  {ObjE MorE : Type v} [TopologicalSpace ObjE] [T2Space ObjE] [ParacompactSpace ObjE]
  [TopologicalSpace MorE] [T2Space MorE] [ParacompactSpace MorE] {E : EpGroupoid ObjE MorE}
  {τ : EpFunctor E (actionEpGroupoid hP)} (M : ProperCoveringModel τ)

/-- **The sheet `V(y) = U(y) ∩ τ̂⁻¹(O')`** of the restriction of the model to `O'`
(Corollary 19.7.20, Proposition 17.8.6). -/
def cutSheet (O' : Set O) (y : ObjE) : Set ObjE := M.U y ∩ τ.obj ⁻¹' O'

theorem cutSheet_univ (y : ObjE) : M.cutSheet univ y = M.U y := by
  rw [cutSheet, preimage_univ, inter_univ]

/-- The morphism with source `y ∈ τ̂⁻¹(ō)` and group element `g` ends in `τ̂⁻¹(ō)`. -/
theorem tgt_liftMor_mem_fiber (g : G) {y : ObjE} (hy : y ∈ M.fiber) :
    E.tgt (M.liftMor g y) ∈ M.fiber := by
  change τ.obj _ = M.pt
  rw [M.obj_tgt, M.src_liftMor, M.groupIndex_liftMor, show τ.obj y = M.pt from hy, M.smul_pt]

/-- **The key step of the proof of Lemma 19.7.19**: on a preconnected `S ∋ ō`, the sheet of
`t(Γ⁻¹((g, o), τ_y⁻¹(o)))` is constant, equal to `t(Γ⁻¹((g, ō), y))`. -/
theorem sheetIndex_tgt_liftMor_σ {S : Set O} (hS : IsPreconnected S) (hpt : M.pt ∈ S) (g : G)
    {y : ObjE} (hy : y ∈ M.fiber) {o : O} (ho : o ∈ S) :
    M.sheetIndex (E.tgt (M.liftMor g (M.σ y o))) = E.tgt (M.liftMor g y) := by
  have hlc : IsLocallyConstant fun o : O => M.sheetIndex (E.tgt (M.liftMor g (M.σ y o))) :=
    (M.lemma_17_8_7.comp Prod.snd).comp_continuous (M.continuous_liftMor_σ g hy)
  have h := hlc.apply_eq_of_isPreconnected hS ho hpt
  refine h.trans ?_
  rw [M.σ_pt hy, M.sheetIndex_of_mem_fiber (M.tgt_liftMor_mem_fiber g hy)]

/-- **A morphism `φ : y → y'` of `τ̂⁻¹(ō)` moves `V(y)` into `V(y')`** (the first half of the proof
of Lemma 19.7.19): for `e ∈ V(y)` the morphism with source `e` and group element `g_φ` ends in
`V(y')`, for `S ∋ ō` preconnected and `G`-invariant. -/
theorem liftMor_mem_cutSheet {S : Set O} (hS : IsPreconnected S) (hpt : M.pt ∈ S)
    (hinv : ∀ (g : G) (o : O), o ∈ S → g • o ∈ S) {φ : MorE} (hφ : E.src φ ∈ M.fiber)
    {e : ObjE} (he : e ∈ M.cutSheet S (E.src φ)) :
    E.src (M.liftMor (M.groupIndex φ) e) = e ∧
      E.tgt (M.liftMor (M.groupIndex φ) e) ∈ M.cutSheet S (E.tgt φ) := by
  refine ⟨M.src_liftMor _ _, ?_, ?_⟩
  · have h1 := M.sheetIndex_tgt_liftMor_σ hS hpt (M.groupIndex φ) hφ he.2
    rw [M.σ_obj hφ he.1, M.liftMor_eq] at h1
    exact h1 ▸ M.mem_U_sheetIndex _
  · change τ.obj _ ∈ S
    rw [M.obj_tgt, M.src_liftMor, M.groupIndex_liftMor]
    exact hinv _ _ he.2

/-- **A morphism from `V(y)` to `V(y')` gives a morphism `y → y'`** (the second half of the proof
of Lemma 19.7.19), for `S ∋ ō` preconnected: the morphism with source `y` and the same group
element. -/
theorem liftMor_of_mem_cutSheet {S : Set O} (hS : IsPreconnected S) (hpt : M.pt ∈ S)
    {y y' : ObjE} (hy : y ∈ M.fiber) (hy' : y' ∈ M.fiber) {ψ : MorE}
    (hs : E.src ψ ∈ M.cutSheet S y) (ht : E.tgt ψ ∈ M.cutSheet S y') :
    E.src (M.liftMor (M.groupIndex ψ) y) = y ∧ E.tgt (M.liftMor (M.groupIndex ψ) y) = y' := by
  refine ⟨M.src_liftMor _ _, ?_⟩
  have h1 := M.sheetIndex_tgt_liftMor_σ hS hpt (M.groupIndex ψ) hy hs.2
  rw [M.σ_obj hy hs.1, M.liftMor_eq, M.sheetIndex_eq hy' ht.1] at h1
  exact h1.symm

/-- `|V(y)| ⊂ |V(y')|` for a morphism `y → y'` (`S` preconnected, `G`-invariant, `ō ∈ S`). -/
theorem image_π_cutSheet_subset {S : Set O} (hS : IsPreconnected S) (hpt : M.pt ∈ S)
    (hinv : ∀ (g : G) (o : O), o ∈ S → g • o ∈ S) {φ : MorE} (hφ : E.src φ ∈ M.fiber) :
    E.π '' M.cutSheet S (E.src φ) ⊆ E.π '' M.cutSheet S (E.tgt φ) := by
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨h1, h2⟩ := M.liftMor_mem_cutSheet hS hpt hinv hφ he
  exact ⟨_, h2, (E.π_src_eq_π_tgt (M.liftMor (M.groupIndex φ) e)).symm.trans (by rw [h1])⟩

/-- `|V(y)| = |V(y')|` for `y ∼ y'`. -/
theorem image_π_cutSheet_eq {S : Set O} (hS : IsPreconnected S) (hpt : M.pt ∈ S)
    (hinv : ∀ (g : G) (o : O), o ∈ S → g • o ∈ S) {y y' : ObjE} (hy : y ∈ M.fiber)
    (h : E.Isomorphic y y') : E.π '' M.cutSheet S y = E.π '' M.cutSheet S y' := by
  obtain ⟨φ, rfl, rfl⟩ := h
  refine (M.image_π_cutSheet_subset hS hpt hinv hy).antisymm ?_
  have h' := M.image_π_cutSheet_subset hS hpt hinv (φ := E.inv φ) (by
    rw [E.src_inv]
    exact M.mem_fiber_iff.2 (by
      rw [M.obj_tgt, show τ.obj (E.src φ) = M.pt from hy, M.smul_pt]))
  rwa [E.src_inv, E.tgt_inv] at h'

/-- If `|V(y)|` and `|V(y')|` meet, then `y ∼ y'` (`S` preconnected, `ō ∈ S`). -/
theorem isomorphic_of_mem_cutSheet {S : Set O} (hS : IsPreconnected S) (hpt : M.pt ∈ S)
    {y y' : ObjE} (hy : y ∈ M.fiber) (hy' : y' ∈ M.fiber) {e e' : ObjE}
    (he : e ∈ M.cutSheet S y) (he' : e' ∈ M.cutSheet S y') (h : E.π e = E.π e') :
    E.Isomorphic y y' := by
  obtain ⟨ψ, hψs, hψt⟩ := (E.π_eq_π_iff).1 h
  obtain ⟨h1, h2⟩ := M.liftMor_of_mem_cutSheet hS hpt hy hy' (hψs ▸ he) (hψt ▸ he')
  exact ⟨_, h1, h2⟩

/-- **2021 Lemma 19.7.19, p. 920**: for a connected proper covering model `τ̂ : E → G ⋉ O`
(Definition 17.8.4) and `y, y' ∈ τ̂⁻¹(ō)`, `y ∼ y'` (there is a morphism `y → y'`) if and only if
`|U(y)| = |U(y')|` in `|E|`. -/
theorem lemma_19_7_19 (hO : M.Connected) {y y' : ObjE} (hy : y ∈ M.fiber)
    (hy' : y' ∈ M.fiber) : E.Isomorphic y y' ↔ E.π '' M.U y = E.π '' M.U y' := by
  have : ConnectedSpace O := hO
  have hS : IsPreconnected (univ : Set O) := isPreconnected_univ
  have hinv : ∀ (g : G) (o : O), o ∈ (univ : Set O) → g • o ∈ (univ : Set O) :=
    fun _ _ _ => mem_univ _
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := M.image_π_cutSheet_eq hS (mem_univ _) hinv hy h
    rwa [M.cutSheet_univ, M.cutSheet_univ] at h'
  · have hmem : E.π y ∈ E.π '' M.U y' := h ▸ ⟨y, M.mem_U y hy, rfl⟩
    obtain ⟨e', he', heq⟩ := hmem
    refine M.isomorphic_of_mem_cutSheet hS (mem_univ _) hy hy'
      (e := y) (e' := e') ?_ ?_ heq.symm
    · rw [M.cutSheet_univ]
      exact M.mem_U y hy
    · rwa [M.cutSheet_univ]

/-- `V(y) = τ_y⁻¹(O')` for `y ∈ τ̂⁻¹(ō)`. -/
theorem cutSheet_eq_image {y : ObjE} (hy : y ∈ M.fiber) (O' : Set O) :
    M.cutSheet O' y = M.σ y '' O' := by
  ext e
  constructor
  · rintro ⟨he, heO⟩
    exact ⟨τ.obj e, heO, M.σ_obj hy he⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨M.σ_mem_U hy o, by
      change τ.obj (M.σ y o) ∈ O'
      rw [M.obj_σ hy]
      exact ho⟩

theorem isOpen_cutSheet {y : ObjE} (hy : y ∈ M.fiber) {O' : Set O} (hO' : IsOpen O') :
    IsOpen (M.cutSheet O' y) :=
  (M.isOpen_U hy).inter (hO'.preimage (continuousOn_univ.1 τ.isScSmoothMap_obj.continuousOn))

theorem isConnected_cutSheet {y : ObjE} (hy : y ∈ M.fiber) {O' : Set O} (hO' : IsConnected O') :
    IsConnected (M.cutSheet O' y) := by
  rw [M.cutSheet_eq_image hy]
  exact hO'.image _ (M.continuous_σ hy).continuousOn

theorem mem_cutSheet_self {y : ObjE} (hy : y ∈ M.fiber) {O' : Set O} (hpt : M.pt ∈ O') :
    y ∈ M.cutSheet O' y :=
  ⟨M.mem_U y hy, by
    change τ.obj y ∈ O'
    rw [show τ.obj y = M.pt from hy]
    exact hpt⟩

theorem pairwiseDisjoint_cutSheet (O' : Set O) : M.fiber.PairwiseDisjoint (M.cutSheet O') :=
  fun _ hy _ hy' hne => (M.pairwiseDisjoint_U hy hy' hne).mono inter_subset_left inter_subset_left

theorem iUnion_cutSheet (O' : Set O) : (⋃ y ∈ M.fiber, M.cutSheet O' y) = τ.obj ⁻¹' O' := by
  ext e
  simp only [mem_iUnion, exists_prop]
  exact ⟨fun ⟨_, _, he⟩ => he.2, fun he =>
    ⟨M.sheetIndex e, M.sheetIndex_mem e, M.mem_U_sheetIndex e, he⟩⟩

end ProperCoveringModel

/-! ### Representatives of classes -/

namespace GroupoidStr

variable {Obj Mor : Type u} (X : GroupoidStr Obj Mor)

/-- **Mutually inequivalent representatives** (Corollary 19.7.20 (2)): every set `F` of objects
contains a set `S` of mutually inequivalent objects meeting the class of every member of `F`. -/
theorem exists_reprs (F : Set Obj) :
    ∃ S ⊆ F, (∀ a ∈ S, ∀ a' ∈ S, X.Isomorphic a a' → a = a') ∧
      ∀ y ∈ F, ∃ a ∈ S, X.Isomorphic a y := by
  classical
  let r : Obj → Obj := fun y => @Classical.epsilon Obj ⟨y⟩ fun a => a ∈ F ∧ X.π a = X.π y
  have hr : ∀ y ∈ F, r y ∈ F ∧ X.π (r y) = X.π y := fun y hy =>
    @Classical.epsilon_spec Obj (fun a => a ∈ F ∧ X.π a = X.π y) ⟨y, hy, rfl⟩
  have hr' : ∀ y y', X.π y = X.π y' → r y = r y' := fun y y' h => by
    simp only [r]
    rw [h]
  refine ⟨r '' F, ?_, ?_, fun y hy => ⟨r y, ⟨y, hy, rfl⟩, (X.π_eq_π_iff).1 (hr y hy).2⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (hr y hy).1
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ h
    refine hr' y y' ?_
    rw [← (hr y hy).2, ← (hr y' hy').2]
    exact (X.π_eq_π_iff).2 h

end GroupoidStr

/-! ### Corollary 19.7.20 -/

namespace GroupoidalCategory

variable {A B : GroupoidalCategory.{u}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}

namespace CoveringUniformizer

variable {β : B.Obj} (Ψh : CoveringUniformizer P β)

/-- `|Ψ(O')| ⊂ |B|`. -/
def imageB (O' : Set Ψh.Ψ.O) : Set B.OrbitSpace := (fun o => B.π (Ψh.Ψ.obj o)) '' O'

/-- `|Ψ̂(V)| ⊂ |A|`. -/
def imageA (V : Set Ψh.ObjE) : Set A.OrbitSpace := (fun e => A.π (Ψh.hat.obj e)) '' V

/-- `|Ψ̂(e)| = |Ψ̂(e')|` if and only if `e ∼ e'` in `E` (`Ψ̂` is full). -/
theorem π_hat_eq_iff {e e' : Ψh.ObjE} :
    A.π (Ψh.hat.obj e) = A.π (Ψh.hat.obj e') ↔ Ψh.E.π e = Ψh.E.π e' := by
  refine ⟨fun h => CoveringBasicConstruction.injective_orbitMap_hat Ψh ?_, fun h => ?_⟩
  · rwa [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π]
  · have h' := congrArg Ψh.hat.orbitMap h
    rwa [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π] at h'

end CoveringUniformizer

namespace CoveringBasicConstruction

variable (Bh : CoveringBasicConstruction P)

/-- **The shrinking step of Corollary 19.7.20**: an open `O₀ ∋ ō` with `|Ψ(O₀)| ⊂ U(z)` and
`|Ψ̂(e)| ∈ Û` whenever `τ̂(e) ∈ O₀`: `O₀ = ⋂_{a ∈ τ̂⁻¹(ō)} τ̂(U(a) ∩ |Ψ̂|⁻¹(Û)) ∩ |Ψ|⁻¹(U(z))`
(`τ̂⁻¹(ō)` is finite and `τ̂` is open and injective on each `U(a)`). -/
theorem exists_open_pt_subset (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) (x : Bh.hatU.Unif) {Uz : Set B.OrbitSpace}
    (hUz : IsOpen[Bh.toBasic.natTop hU.toBasic] Uz) (hzU : B.π x.β ∈ Uz)
    {Uh : Set A.OrbitSpace} (hUh : IsOpen[Bh.natTopA hP hC hU] Uh)
    (hfib : P.orbitMap ⁻¹' {B.π x.β} ⊆ Uh) :
    ∃ O₀ : Set x.Ψh.Ψ.O, IsOpen O₀ ∧ x.Ψh.model.pt ∈ O₀ ∧ x.Ψh.imageB O₀ ⊆ Uz ∧
      ∀ e, x.Ψh.τ.obj e ∈ O₀ → A.π (x.Ψh.hat.obj e) ∈ Uh := by
  let _ := Bh.natTopA hP hC hU
  let _ := Bh.toBasic.natTop hU.toBasic
  set M := x.Ψh.model
  have hfin : M.fiber.Finite := x.Ψh.finite_fiber_τ hP M.pt
  set N : Set x.Ψh.ObjE := (fun e => A.π (x.Ψh.hat.obj e)) ⁻¹' Uh
  have hN : IsOpen N := hUh.preimage (Bh.continuous_π_hat hP hC hU x)
  have hτo : IsOpenMap x.Ψh.τ.obj := M.isLocalScDiffeo.isLocalHomeomorph.isOpenMap
  have hΨ : x.Ψh.Ψ ∈ Bh.toBasic.U.F x.β := ⟨x.Ψh, x.mem, rfl⟩
  have hfibN : ∀ a ∈ M.fiber, a ∈ N := fun a ha => hfib (by
    change P.orbitMap (A.π (x.Ψh.hat.obj a)) = B.π x.β
    rw [orbitMap_π_hat, show x.Ψh.τ.obj a = M.pt from ha, x.Ψh.obj_pt])
  refine ⟨(⋂ a ∈ M.fiber, x.Ψh.τ.obj '' (N ∩ M.U a)) ∩
      (fun o => B.π (x.Ψh.Ψ.obj o)) ⁻¹' Uz, ?_, ?_, ?_, ?_⟩
  · exact (hfin.isOpen_biInter fun a ha => hτo _ (hN.inter (M.isOpen_U ha))).inter
      (hUz.preimage (Bh.toBasic.continuous_π_obj hU.toBasic hΨ))
  · refine ⟨mem_iInter₂.2 fun a ha => ⟨a, ⟨hfibN a ha, M.mem_U a ha⟩, ha⟩, ?_⟩
    change B.π (x.Ψh.Ψ.obj M.pt) ∈ Uz
    rw [x.Ψh.obj_pt]
    exact hzU
  · rintro _ ⟨o, ho, rfl⟩
    exact ho.2
  · intro e he
    obtain ⟨e', ⟨he'N, he'U⟩, he'τ⟩ := mem_iInter₂.1 he.1 (M.sheetIndex e) (M.sheetIndex_mem e)
    have hee' : e = e' := M.eq_of_obj_eq (M.sheetIndex_eq (M.sheetIndex_mem e) he'U).symm he'τ.symm
    rw [hee']
    exact he'N

/-- **2021 Corollary 19.7.20 (1), (2), pp. 921–922**, under `IsCompatible` and
`HasClassUniformizers`: for `z = |β| ∈ |B|`, `Ψ̂ ∈ F̂(β)` (`x`), open neighbourhoods `U(z)` of `z`
(in `T_{|B|}`) and `Û` of `|P|⁻¹(z)` (in `T_{|A|}`), there is a connected `G`-invariant open
neighbourhood `O'` of `ō` such that the restriction `τ̂' : τ̂⁻¹(O') → G ⋉ O'` is a connected proper
covering model (Proposition 17.8.6), `τ̂⁻¹(O')` is the disjoint union of the connected open
`V(y) = U(y) ∩ τ̂⁻¹(O') ∋ y`, `y ∈ τ̂⁻¹(ō)`, and
(1) `W(z) = |Ψ(O')|` is an open neighbourhood of `z` contained in `U(z)`;
(2) there is a set `S ⊂ τ̂⁻¹(ō)` of mutually inequivalent points whose classes exhaust `τ̂⁻¹(ō)`,
every `V(a)`, `a ∈ S`, is `G_a`-invariant, the `W(z̄_a) = |Ψ̂(V(a))|` are open neighbourhoods of
`z̄_a = |Ψ̂(a)|`, mutually disjoint, (19.38) `|P|⁻¹(W(z)) = ⋃_{a ∈ S} W(z̄_a) ⊂ Û`, and
`a ↦ z̄_a` is a bijection `S → |P|⁻¹(z)`. -/
theorem corollary_19_7_20_hyp (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) (x : Bh.hatU.Unif) {Uz : Set B.OrbitSpace}
    (hUz : IsOpen[Bh.toBasic.natTop hU.toBasic] Uz) (hzU : B.π x.β ∈ Uz)
    {Uh : Set A.OrbitSpace} (hUh : IsOpen[Bh.natTopA hP hC hU] Uh)
    (hfib : P.orbitMap ⁻¹' {B.π x.β} ⊆ Uh) :
    ∃ (O' : SubMulAction x.Ψh.Ψ.G x.Ψh.Ψ.O) (hO' : IsOpen (O' : Set x.Ψh.Ψ.O))
      (hpt : x.Ψh.model.pt ∈ O'), IsConnected (O' : Set x.Ψh.Ψ.O) ∧
      (∀ [ParacompactSpace O'] [ParacompactSpace (x.Ψh.τ.obj ⁻¹' (O' : Set x.Ψh.Ψ.O))],
        ∃ M' : ProperCoveringModel (x.Ψh.model.restrictFunctor O' hO'),
          M'.pt = ⟨x.Ψh.model.pt, hpt⟩ ∧ M'.Connected) ∧
      (∀ y ∈ x.Ψh.model.fiber, IsOpen (x.Ψh.model.cutSheet O' y) ∧
        IsConnected (x.Ψh.model.cutSheet O' y) ∧ y ∈ x.Ψh.model.cutSheet O' y) ∧
      x.Ψh.model.fiber.PairwiseDisjoint (x.Ψh.model.cutSheet O') ∧
      (⋃ y ∈ x.Ψh.model.fiber, x.Ψh.model.cutSheet O' y) = x.Ψh.τ.obj ⁻¹' O' ∧
      (IsOpen[Bh.toBasic.natTop hU.toBasic] (x.Ψh.imageB O') ∧ B.π x.β ∈ x.Ψh.imageB O' ∧
        x.Ψh.imageB O' ⊆ Uz) ∧
      ∃ S ⊆ x.Ψh.model.fiber, (∀ a ∈ S, ∀ a' ∈ S, x.Ψh.E.Isomorphic a a' → a = a') ∧
        (∀ y ∈ x.Ψh.model.fiber, ∃ a ∈ S, x.Ψh.E.Isomorphic a y) ∧
        (∀ a ∈ S, ∀ φ, x.Ψh.E.src φ = a → x.Ψh.E.tgt φ = a → ∀ e ∈ x.Ψh.model.cutSheet O' a,
          x.Ψh.E.tgt (x.Ψh.model.liftMor (x.Ψh.model.groupIndex φ) e) ∈
            x.Ψh.model.cutSheet O' a) ∧
        (∀ a ∈ S, IsOpen[Bh.natTopA hP hC hU] (x.Ψh.imageA (x.Ψh.model.cutSheet O' a)) ∧
          A.π (x.Ψh.hat.obj a) ∈ x.Ψh.imageA (x.Ψh.model.cutSheet O' a)) ∧
        S.PairwiseDisjoint (fun a => x.Ψh.imageA (x.Ψh.model.cutSheet O' a)) ∧
        P.orbitMap ⁻¹' x.Ψh.imageB O' = ⋃ a ∈ S, x.Ψh.imageA (x.Ψh.model.cutSheet O' a) ∧
        (⋃ a ∈ S, x.Ψh.imageA (x.Ψh.model.cutSheet O' a)) ⊆ Uh ∧
        BijOn (fun a => A.π (x.Ψh.hat.obj a)) S (P.orbitMap ⁻¹' {B.π x.β}) := by
  let _ := Bh.natTopA hP hC hU
  let _ := Bh.toBasic.natTop hU.toBasic
  set M := x.Ψh.model
  obtain ⟨O₀, hO₀, hpt₀, hO₀B, hO₀A⟩ := Bh.exists_open_pt_subset hP hC hU x hUz hzU hUh hfib
  obtain ⟨O', hO', hpt, hsub, hconn, hmodel⟩ := proposition_17_8_6 M hO₀ hpt₀
  have hinv : ∀ (g : x.Ψh.Ψ.G) (o : x.Ψh.Ψ.O), o ∈ (O' : Set x.Ψh.Ψ.O) →
      g • o ∈ (O' : Set x.Ψh.Ψ.O) := fun g _ ho => O'.smul_mem g ho
  have hS : IsPreconnected (O' : Set x.Ψh.Ψ.O) := hconn.isPreconnected
  have hptO : M.pt ∈ (O' : Set x.Ψh.Ψ.O) := hpt
  have hΨ : x.Ψh.Ψ ∈ Bh.toBasic.U.F x.β := ⟨x.Ψh, x.mem, rfl⟩
  obtain ⟨S, hSF, hSinj, hScov⟩ := x.Ψh.E.toGroupoidStr.exists_reprs M.fiber
  have hfibpt : ∀ a ∈ M.fiber, P.orbitMap (A.π (x.Ψh.hat.obj a)) = B.π x.β := fun a ha => by
    rw [orbitMap_π_hat, show x.Ψh.τ.obj a = M.pt from ha, x.Ψh.obj_pt]
  refine ⟨O', hO', hpt, hconn, hmodel, fun y hy => ⟨M.isOpen_cutSheet hy hO',
    M.isConnected_cutSheet hy hconn, M.mem_cutSheet_self hy hptO⟩, M.pairwiseDisjoint_cutSheet _,
    M.iUnion_cutSheet _, ⟨Bh.toBasic.theorem_19_2_2_two hU.toBasic hΨ hO',
    ⟨M.pt, hptO, congrArg B.π x.Ψh.obj_pt⟩, (image_mono hsub).trans hO₀B⟩, S, hSF, hSinj,
    hScov, ?_, fun a ha => ⟨Bh.isOpen_image_hat hP hC hU x (M.isOpen_cutSheet (hSF ha) hO'),
    a, M.mem_cutSheet_self (hSF ha) hptO, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro a ha φ hφs hφt e he
    have h := (M.liftMor_mem_cutSheet hS hptO hinv (φ := φ) (hφs ▸ hSF ha) (hφs ▸ he)).2
    rwa [hφt] at h
  · intro a ha a' ha' hne
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨e, he, rfl⟩ ⟨e', he', heq⟩
    exact hne (hSinj a ha a' ha' (M.isomorphic_of_mem_cutSheet hS hptO (hSF ha) (hSF ha') he he'
      ((x.Ψh.π_hat_eq_iff).1 heq.symm)))
  · ext z
    simp only [mem_preimage, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨o, ho, hzo⟩
      obtain ⟨e, heo, rfl⟩ := exists_hat_of_orbitMap_eq hP x.Ψh o hzo
      have hey : e ∈ M.cutSheet O' (M.sheetIndex e) :=
        ⟨M.mem_U_sheetIndex e, show x.Ψh.τ.obj e ∈ (O' : Set x.Ψh.Ψ.O) from heo ▸ ho⟩
      obtain ⟨a, haS, hay⟩ := hScov _ (M.sheetIndex_mem e)
      have himg := M.image_π_cutSheet_eq hS hptO hinv (hSF haS) hay
      obtain ⟨e', he', heq⟩ : x.Ψh.E.π e ∈ x.Ψh.E.π '' M.cutSheet O' a := himg ▸ ⟨e, hey, rfl⟩
      exact ⟨a, haS, e', he', (x.Ψh.π_hat_eq_iff).2 heq⟩
    · rintro ⟨a, -, e, he, rfl⟩
      exact ⟨x.Ψh.τ.obj e, he.2, (orbitMap_π_hat x.Ψh e).symm⟩
  · simp only [iUnion_subset_iff]
    rintro a - _ ⟨e, he, rfl⟩
    exact hO₀A e (hsub he.2)
  · refine ⟨fun a ha => hfibpt a (hSF ha), fun a ha a' ha' h => hSinj a ha a' ha'
      ((x.Ψh.E.π_eq_π_iff).1 ((x.Ψh.π_hat_eq_iff).1 h)), fun z hz => ?_⟩
    obtain ⟨e, he, rfl⟩ := exists_hat_of_orbitMap_eq hP x.Ψh M.pt
      (by rw [x.Ψh.obj_pt]; exact (hz : P.orbitMap z = B.π x.β).symm)
    obtain ⟨a, haS, hae⟩ := hScov e he
    exact ⟨a, haS, (x.Ψh.π_hat_eq_iff).2 ((x.Ψh.E.π_eq_π_iff).2 hae)⟩

/-- **Every open neighbourhood `Û` of `|P|⁻¹(z)` contains `|P|⁻¹(W)` for an open `W ∋ z`**
(Corollary 19.7.20 (2), (19.38), with `U(z) = |B|`), under `IsCompatible` and
`HasClassUniformizers`. -/
theorem exists_isOpen_preimage_subset (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) (z : B.OrbitSpace) {Uh : Set A.OrbitSpace}
    (hUh : IsOpen[Bh.natTopA hP hC hU] Uh) (hfib : P.orbitMap ⁻¹' {z} ⊆ Uh) :
    ∃ W : Set B.OrbitSpace, IsOpen[Bh.toBasic.natTop hU.toBasic] W ∧ z ∈ W ∧
      P.orbitMap ⁻¹' W ⊆ Uh := by
  let _ := Bh.toBasic.natTop hU.toBasic
  obtain ⟨β, rfl, Ψh, hΨh⟩ := hU z
  obtain ⟨O', -, -, -, -, -, -, -, ⟨hW, hzW, -⟩, S, -, -, -, -, -, -, hpre, hsub, -⟩ :=
    Bh.corollary_19_7_20_hyp hP hC hU ⟨β, Ψh, hΨh⟩ (Uz := univ) isOpen_univ (mem_univ _) hUh hfib
  refine ⟨_, hW, hzW, ?_⟩
  rw [hpre]
  exact hsub

/-- **`|P| : (|A|, T_{|A|}) → (|B|, T_{|B|})` is a closed map** (from
`exists_isOpen_preimage_subset`), under `IsCompatible` and `HasClassUniformizers`. -/
theorem isClosedMap_orbitMap (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) :
    @IsClosedMap _ _ (Bh.natTopA hP hC hU) (Bh.toBasic.natTop hU.toBasic) P.orbitMap := by
  let _ := Bh.natTopA hP hC hU
  let _ := Bh.toBasic.natTop hU.toBasic
  intro C hCc
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  have hfib : P.orbitMap ⁻¹' {z} ⊆ Cᶜ := fun w hw hwC => hz ⟨w, hwC, hw⟩
  obtain ⟨W, hW, hzW, hsub⟩ := Bh.exists_isOpen_preimage_subset hP hC hU z hCc.isOpen_compl hfib
  refine ⟨W, ?_, hW, hzW⟩
  rintro w hw ⟨v, hvC, rfl⟩
  exact hsub hw hvC

/-- **`|P|` is evenly covered** (Corollary 19.7.20 (2) with `U(z) = |B|`, `Û = |A|`; the form
of Theorem 19.7.25 (4a) and Definition 17.8.1 (3)), under `IsCompatible` and
`HasClassUniformizers`: `|P|⁻¹(z)` is finite, and there are an open `U(z) ∋ z` and mutually
disjoint open neighbourhoods `U(z̄)` of the `z̄ ∈ |P|⁻¹(z)` with `|P|⁻¹(U(z)) = ⋃ U(z̄)`. -/
theorem evenlyCovered_orbitMap (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) (z : B.OrbitSpace) :
    (P.orbitMap ⁻¹' {z}).Finite ∧
      ∃ (Uz : Set B.OrbitSpace) (V : A.OrbitSpace → Set A.OrbitSpace),
        IsOpen[Bh.toBasic.natTop hU.toBasic] Uz ∧ z ∈ Uz ∧
        (∀ y ∈ P.orbitMap ⁻¹' {z}, IsOpen[Bh.natTopA hP hC hU] (V y) ∧ y ∈ V y) ∧
        (P.orbitMap ⁻¹' {z}).PairwiseDisjoint V ∧
        P.orbitMap ⁻¹' Uz = ⋃ y ∈ P.orbitMap ⁻¹' {z}, V y := by
  let _ := Bh.natTopA hP hC hU
  let _ := Bh.toBasic.natTop hU.toBasic
  refine ⟨finite_fiber_orbitMap hP z, ?_⟩
  obtain ⟨β, rfl, Ψh, hΨh⟩ := hU z
  set x : Bh.hatU.Unif := ⟨β, Ψh, hΨh⟩
  obtain ⟨O', -, -, -, -, -, -, -, ⟨hW, hzW, -⟩, S, -, -, -, -, hopen, hdisj, hpre, -, hbij⟩ :=
    Bh.corollary_19_7_20_hyp hP hC hU x (Uz := univ) isOpen_univ (mem_univ _) (Uh := univ)
      isOpen_univ (subset_univ _)
  have : Nonempty x.Ψh.ObjE := ⟨(x.Ψh.model.surjective x.Ψh.model.pt).choose⟩
  set f : x.Ψh.ObjE → A.OrbitSpace := fun a => A.π (x.Ψh.hat.obj a)
  set r := Function.invFunOn f S
  have hr : ∀ y ∈ P.orbitMap ⁻¹' {B.π x.β}, r y ∈ S ∧ f (r y) = y := fun y hy =>
    ⟨Function.invFunOn_mem (hbij.surjOn hy), Function.invFunOn_eq (hbij.surjOn hy)⟩
  refine ⟨_, fun y => x.Ψh.imageA (x.Ψh.model.cutSheet O' (r y)), hW, hzW, fun y hy => ?_,
    fun y hy y' hy' hne => hdisj (hr y hy).1 (hr y' hy').1 fun h => hne ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hopen _ (hr y hy).1
    refine ⟨h1, ?_⟩
    have e : A.π (x.Ψh.hat.obj (r y)) = y := (hr y hy).2
    change y ∈ x.Ψh.imageA (x.Ψh.model.cutSheet O' (r y))
    rwa [e] at h2
  · rw [← (hr y hy).2, ← (hr y' hy').2, h]
  · rw [hpre]
    ext w
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨a, haS, hw⟩
      refine ⟨f a, hbij.mapsTo haS, ?_⟩
      rwa [show r (f a) = a from hbij.injOn.leftInvOn_invFunOn haS]
    · rintro ⟨y, hy, hw⟩
      exact ⟨r y, (hr y hy).1, hw⟩

end CoveringBasicConstruction

end GroupoidalCategory

end Polyfold
