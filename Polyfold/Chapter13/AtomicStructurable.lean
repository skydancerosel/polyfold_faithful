import Polyfold.Chapter13.AtomicStructurableLocal
import Polyfold.Chapter13.StructurableMultisection

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.5, **Theorem 13.5.3** (p. 630; 2017: Theorem 13.6) and the last sentence of **Theorem
13.5.5** (p. 633).

# Atomic sc⁺-multisections are structurable

## The text, paraphrased

(Theorem 13.5.3) An atomic sc⁺-multisection functor is structurable (Definition 13.3.6).
*Proof*: over the points joined to `cl V(x₀)` the atomic structure is pulled back along local
sc-diffeomorphisms of morphisms into `U(x₀)`, `G_x` acting on `I_{x₀}` through a homomorphism
`γ_x : G_x → G_{x₀}`; elsewhere `Λ` is trivial.  The correspondences are the bijections of
`I_{x₀}` given by the elements of `G_{x₀}` relating the pulled back structures, and the full
correspondences between points over `|cl V(x₀)|` and points away from it.

## What is formalized (namespace `Polyfold.SBLocalization.AtomicStructData`)

`Z = π⁻¹(π(cl V(x₀)))` (closed and saturated).  An `AtomicStructData Λ` bundles the atomic data
`D`, a good system `𝒰₀` and, for `y ∈ Z`, an open `O(y) ∋ y` and a sc-smooth `τ_y : O(y) → 𝐗`
with `t(τ_y(z)) = z`, `s(τ_y(z)) ∈ U(x₀)` (`AtomicData.exists_isLocalRepOn_transport`); every atomic
`Λ` with a good system has one (`exists_atomicStructData`).

* `H y y' ψ ∈ G_{x₀}`: the unique `h` with `Γ(h, s(τ_y(s ψ))) = τ_{y'}(t ψ)⁻¹ ∘ ψ ∘ τ_y(s ψ)` for
  `y, y' ∈ Z` (and `1` otherwise).  It is functorial (`H_comp`), locally constant
  (`H_eventually`), and `γ_y(g) = H y y (Γ(g, y))` is a homomorphism `G_y →* G_{x₀}`.
* The good system `𝒰 ⊆ 𝒰₀` (same natural actions) on which `H y y (Γ(g, z)) = γ_y(g)`
  (`z ∈ U(y)`, `y ∈ Z`) and `U(y) ∩ Z = ∅` (`y ∉ Z`).
* The symmetric structures `S y` (index set `I_{x₀}` for every `y`, sections pulled back by
  `τ_y`, resp. zero), the correspondences `corr y y' φ` (`[I ←id I →H(φ) I]` when `y, y'` are
  both in `Z` or both outside, the full correspondence `[I ← I × I → I]` otherwise), and
  **`AtomicStructData.isStructurable`**.
* **`theorem_13_5_3_of_goodSystem`**, **`theorem_13_5_3`** (`IsStructurable A Λ ↔ Nonempty
  A.X.GoodSystem` for atomic `Λ`), **`theorem_13_5_3_of_paracompact`**, and
  **`theorem_13_5_5_structurable`**.

## Reading

* Structurability includes a good system (Definition 13.3.6); the text takes one for granted
  (Theorem 13.1.8, `|X|` paracompact).  We state the theorem with `Nonempty A.X.GoodSystem`,
  and show the hypothesis is also necessary (`theorem_13_5_3`).
* The index set is `I_{x₀}` at every point (also where `Λ` is trivial, with zero sections) and
  the correspondences between `Z` and its complement are the full ones; the text uses `{∗}` there.
  Both are structures in the sense of Definition 13.3.6.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

/-! ### Generic lemmas -/

namespace IndexDiagram

variable {α β : Type u}

theorem card_fst_fiber (i : α) : Nat.card {k : α × β // k.1 = i} = Nat.card β :=
  Nat.card_congr ⟨fun k => k.1.2, fun j => ⟨(i, j), rfl⟩,
    fun ⟨⟨_, _⟩, h⟩ => by subst h; rfl, fun _ => rfl⟩

theorem card_snd_fiber (j : β) : Nat.card {k : α × β // k.2 = j} = Nat.card α :=
  Nat.card_congr ⟨fun k => k.1.1, fun i => ⟨(i, j), rfl⟩,
    fun ⟨⟨_, _⟩, h⟩ => by subst h; rfl, fun _ => rfl⟩

/-- The full diagram `I_x ← I_x × I_{x'} → I_{x'}`. -/
def full (α β : Type u) [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] :
    IndexDiagram α β where
  I := α × β
  a := Prod.fst
  b := Prod.snd
  surjective_a := Prod.fst_surjective
  surjective_b := Prod.snd_surjective
  uniform_a i i' := by rw [card_fst_fiber, card_fst_fiber]
  uniform_b j j' := by rw [card_snd_fiber, card_snd_fiber]

end IndexDiagram

namespace IndexCorr

variable {α β : Type u}

/-- The full correspondence `[I_x ← I_x × I_{x'} → I_{x'}]`. -/
def full (α β : Type u) [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] : IndexCorr α β :=
  mk (IndexDiagram.full α β)

theorem swap_full [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] :
    (full α β).swap = full β α :=
  mk_eq_mk.2 ⟨Equiv.prodComm α β, fun _ => ⟨rfl, rfl⟩⟩

theorem biact_full {G G' : Type*} [Group G] [Group G'] [MulAction G α] [MulAction G' β]
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (g' : G') (g : G) :
    biact g' (full α β) g = full α β :=
  mk_eq_mk.2
    ⟨Equiv.prodCongr (MulAction.toPerm g⁻¹) (MulAction.toPerm g'), fun _ => ⟨rfl, rfl⟩⟩

theorem biact_ofEquiv {G G' : Type*} [Group G] [Group G'] [MulAction G α] [MulAction G' β]
    [Fintype α] (g' : G') (e : α ≃ β) (g : G) :
    biact g' (ofEquiv e) g =
      ofEquiv ((MulAction.toPerm g).trans (e.trans (MulAction.toPerm g'))) :=
  mk_eq_mk.2 ⟨(MulAction.toPerm g⁻¹ : Equiv.Perm α), fun k => ⟨rfl, by
    show g' • e (g • g⁻¹ • (show α from k)) = g' • e (show α from k)
    rw [smul_inv_smul]⟩⟩

theorem swap_ofEquiv [Fintype α] [Fintype β] (e : α ≃ β) :
    (ofEquiv e).swap = ofEquiv e.symm :=
  mk_eq_mk.2 ⟨e, fun k => ⟨rfl, e.symm_apply_apply k⟩⟩

theorem sat_ofEquiv [Fintype α] {R : α → β → Prop} (e : α ≃ β) (h : ∀ i, R i (e i)) :
    (ofEquiv e).Sat R :=
  fun k => h k

end IndexCorr

/-- **Locally constant choice**: if `gs h z = f z` for exactly one `h` of a finite type, on an open
`S`, with `f`, `gs h` continuous into a Hausdorff space, then the chosen `h` is locally constant. -/
theorem eventually_eq_of_existsUnique {T M G : Type*} [TopologicalSpace T] [TopologicalSpace M]
    [T2Space M] [Finite G] {S : Set T} (hS : IsOpen S) {f : T → M} {gs : G → T → M}
    (hf : ContinuousOn f S) (hg : ∀ h, ContinuousOn (gs h) S)
    (hu : ∀ z ∈ S, ∃! h, gs h z = f z) {z₀ : T} (hz₀ : z₀ ∈ S) {h : G}
    (hh : gs h z₀ = f z₀) : ∀ᶠ z in 𝓝 z₀, z ∈ S ∧ gs h z = f z := by
  have hall : ∀ᶠ z in 𝓝 z₀, ∀ h', h' ≠ h → gs h' z ≠ f z := by
    rw [eventually_all]
    intro h'
    by_cases e : h' = h
    · exact .of_forall fun _ e' => absurd e e'
    · have hne : gs h' z₀ ≠ f z₀ := fun e' => e ((hu z₀ hz₀).unique e' hh)
      exact (((hg h').continuousAt (hS.mem_nhds hz₀)).ne_iff_eventually_ne
        (hf.continuousAt (hS.mem_nhds hz₀))).1 hne |>.mono fun _ hz _ => hz
  filter_upwards [hS.mem_nhds hz₀, hall] with z hz hz'
  obtain ⟨h'', e, -⟩ := hu z hz
  by_cases eh : h'' = h
  · exact ⟨hz, eh ▸ e⟩
  · exact absurd e (hz' h'' eh)

/-- A locally constant function on an open set is constant on its connected components. -/
theorem eq_of_mem_connectedComponentIn {T G : Type*} [TopologicalSpace T] {S : Set T}
    (hS : IsOpen S) {H : T → G} (hH : ∀ φ ∈ S, ∀ᶠ ψ in 𝓝 φ, H ψ = H φ) {φ ψ : T} (hφ : φ ∈ S)
    (hψ : ψ ∈ connectedComponentIn S φ) : H ψ = H φ := by
  have hopen : ∀ c : G, IsOpen {ψ | ψ ∈ S ∧ H ψ = c} := fun c => by
    refine isOpen_iff_mem_nhds.2 fun ψ ⟨hψS, hψc⟩ => ?_
    filter_upwards [hS.mem_nhds hψS, hH ψ hψS] with ψ' h1 h2 using ⟨h1, h2.trans hψc⟩
  have hopen' : IsOpen {ψ | ψ ∈ S ∧ H ψ ≠ H φ} := by
    refine isOpen_iff_mem_nhds.2 fun ψ ⟨hψS, hψc⟩ => ?_
    filter_upwards [hS.mem_nhds hψS, hH ψ hψS] with ψ' h1 h2 using ⟨h1, h2 ▸ hψc⟩
  have hsub := (isPreconnected_connectedComponentIn (F := S) (x := φ)).subset_left_of_subset_union
    (hopen (H φ)) hopen' (Set.disjoint_left.2 fun _ h1 h2 => h2.2 h1.2)
    (fun ψ' h' => by
      have := connectedComponentIn_subset S φ h'
      by_cases e : H ψ' = H φ
      · exact Or.inl ⟨this, e⟩
      · exact Or.inr ⟨this, e⟩)
    ⟨φ, mem_connectedComponentIn hφ, hφ, rfl⟩
  exact (hsub hψ).2

variable {A : SEP.{u}}

namespace AtomicStructData

/-! ### The fibre maps -/

theorem fibAct_comp {ψ χ : A.Mor} {v : A.W} (hv : A.P v = A.X.src χ)
    (h : A.X.src ψ = A.X.tgt χ) : fibAct (A.X.comp ψ χ) v = fibAct ψ (fibAct χ v) := by
  rw [fibAct_of (hv.trans (A.X.src_comp ψ χ h).symm), fibAct_of hv,
    fibAct_of ((A.E.P_μ _).trans h.symm)]
  exact A.E.μ_comp ψ χ v hv h

theorem fibAct_unit {y : A.Obj} {v : A.W} (hv : A.P v = y) : fibAct (A.X.unit y) v = v := by
  subst hv
  rw [fibAct_of (A.X.src_unit _).symm]
  exact (A.E.μ_congr rfl).trans (A.E.μ_unit v)

theorem fibAct_inv_fibAct {ψ : A.Mor} {v : A.W} (hv : A.P v = A.X.src ψ) :
    fibAct (A.X.inv ψ) (fibAct ψ v) = v := by
  rw [← fibAct_comp hv (A.X.src_inv ψ), A.X.inv_comp, fibAct_unit hv]

theorem fibAct_fibAct_inv {ψ : A.Mor} {v : A.W} (hv : A.P v = A.X.tgt ψ) :
    fibAct ψ (fibAct (A.X.inv ψ) v) = v := by
  rw [← fibAct_comp (hv.trans (A.X.src_inv ψ).symm) (A.X.tgt_inv ψ).symm, A.X.comp_inv,
    fibAct_unit hv]

theorem transportSection_eq_fibAct {τ : A.Obj → A.Mor} {b : A.Obj → A.W} {z : A.Obj}
    (h : A.P (b z) = A.X.src (τ z)) : transportSection τ b z = fibAct (τ z) (b z) := by
  rw [transportSection_of_mem h, fibAct_of h]

/-- `φ ∘ (φ⁻¹ ∘ χ) = χ`. -/
theorem comp_inv_comp {φ χ : A.Mor} (h : A.X.tgt χ = A.X.tgt φ) :
    A.X.comp φ (A.X.comp (A.X.inv φ) χ) = χ := by
  have := GroupoidStr.inv_comp_cancel_left (G := A.X.toGroupoidStr) (φ := A.X.inv φ) (ψ := χ)
    (by rw [A.X.src_inv]; exact h.symm)
  rwa [GroupoidStr.inv_inv] at this

end AtomicStructData

/-! ### The data -/

/-- **The data of the proof of Theorem 13.5.3**: atomic data `D` related to `Λ`, a good system
`𝒰₀`, and for every `y ∈ Z = π⁻¹(π(cl V(x₀)))` an open `O(y) ∋ y` with a sc-smooth
`τ_y : O(y) → 𝐗`, `t(τ_y(z)) = z`, `s(τ_y(z)) ∈ U(x₀)`, along which the atomic sections pull back
to sc⁺-sections. -/
structure AtomicStructData (Λ : A.W → ℚ≥0) where
  /-- The atomic data. -/
  D : AtomicData A
  [nonempty : Nonempty D.I]
  hΛ : IsScPlusMultisection A Λ
  hD : D.IsRelated Λ
  /-- A good system. -/
  𝒰₀ : A.X.GoodSystem
  /-- The open sets `O(y)`. -/
  O : A.Obj → Set A.Obj
  /-- The local sc-diffeomorphisms `τ_y`. -/
  τ : A.Obj → A.Obj → A.Mor
  isOpen_O : ∀ y ∈ A.X.saturation (closure D.V), IsOpen (O y)
  mem_O : ∀ y ∈ A.X.saturation (closure D.V), y ∈ O y
  isScSmoothOn_τ : ∀ y ∈ A.X.saturation (closure D.V), A.X.PObj.IsScSmoothOn A.X.PMor (τ y) (O y)
  tgt_τ : ∀ y ∈ A.X.saturation (closure D.V), ∀ z ∈ O y, A.X.tgt (τ y z) = z
  src_τ : ∀ y ∈ A.X.saturation (closure D.V), ∀ z ∈ O y, A.X.src (τ y z) ∈ D.R.U
  isScPlusSectionOn : ∀ y ∈ A.X.saturation (closure D.V), ∀ i,
    IsScPlusSectionOn A (transportSection (τ y) fun z => D.s i (A.X.src (τ y z))) (O y)

attribute [instance] AtomicStructData.nonempty

/-- Every atomic `Λ` with atomic data `D` and a good system has the data of the proof. -/
theorem exists_atomicStructData {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (D : AtomicData A) (hD : D.IsRelated Λ) (𝒰₀ : A.X.GoodSystem) :
    ∃ P : AtomicStructData Λ, P.D = D := by
  have := AtomicData.IsRelated.nonempty D hΛ hD
  have key : ∀ y, ∃ (O : Set A.Obj) (τ : A.Obj → A.Mor), y ∈ A.X.saturation (closure D.V) →
      IsOpen O ∧ y ∈ O ∧ A.X.PObj.IsScSmoothOn A.X.PMor τ O ∧
      (∀ z ∈ O, A.X.tgt (τ z) = z ∧ A.X.src (τ z) ∈ D.R.U) ∧
      ∀ i, IsScPlusSectionOn A (transportSection τ fun z => D.s i (A.X.src (τ z))) O := by
    intro y
    by_cases hy : y ∈ A.X.saturation (closure D.V)
    · have hr : D.Reach y := (D.reach_iff_mem_saturation y).2 (D.saturation_closure_V_subset hy)
      obtain ⟨O, τ, hO, hyO, hτ, hτp, hrep⟩ := D.exists_isLocalRepOn_transport hr
      refine ⟨O, τ, fun _ => ⟨hO, hyO, hτ, hτp, fun i => ?_⟩⟩
      have := hrep.2.1 (Fintype.equivFin D.I i)
      simpa only [Equiv.symm_apply_apply] using this
    · exact ⟨∅, fun _ => A.X.unit y, fun h => absurd h hy⟩
  choose O τ h using key
  exact ⟨⟨D, hΛ, hD, 𝒰₀, O, τ, fun y hy => (h y hy).1, fun y hy => (h y hy).2.1,
    fun y hy => (h y hy).2.2.1, fun y hy z hz => ((h y hy).2.2.2.1 z hz).1,
    fun y hy z hz => ((h y hy).2.2.2.1 z hz).2, fun y hy => (h y hy).2.2.2.2⟩, rfl⟩

namespace AtomicStructData

variable {Λ : A.W → ℚ≥0} (P : AtomicStructData Λ)

/-- `Z = π⁻¹(π(cl V(x₀)))`. -/
def Z : Set A.Obj := A.X.saturation (closure P.D.V)

theorem isClosed_Z : IsClosed P.Z := P.D.isClosed_saturation_closure_V

theorem mem_Z_iff_of_mor (ψ : A.Mor) : A.X.src ψ ∈ P.Z ↔ A.X.tgt ψ ∈ P.Z := by
  show A.X.π (A.X.src ψ) ∈ A.X.π '' closure P.D.V ↔ A.X.π (A.X.tgt ψ) ∈ A.X.π '' closure P.D.V
  rw [A.X.π_src_eq_π_tgt]

/-- `σ_y(z) = s(τ_y(z)) ∈ U(x₀)`. -/
def σ (y z : A.Obj) : A.Obj := A.X.src (P.τ y z)

/-- The morphisms between `O(y)` and `O(y')`. -/
def Dom (y y' : A.Obj) : Set A.Mor := A.X.morBetween (P.O y) (P.O y')

/-- `τ_{y'}(t ψ)⁻¹ ∘ ψ ∘ τ_y(s ψ) : σ_y(s ψ) → σ_{y'}(t ψ)`. -/
def conj (y y' : A.Obj) (ψ : A.Mor) : A.Mor :=
  A.X.comp (A.X.inv (P.τ y' (A.X.tgt ψ))) (A.X.comp ψ (P.τ y (A.X.src ψ)))

variable {P}

section Near

variable {y y' : A.Obj} (hy : y ∈ P.Z) (hy' : y' ∈ P.Z)

include hy in
theorem σ_mem {z : A.Obj} (hz : z ∈ P.O y) : P.σ y z ∈ P.D.R.U := P.src_τ y hy z hz

include hy hy' in
theorem isOpen_Dom : IsOpen (P.Dom y y') :=
  A.X.isOpen_morBetween (P.isOpen_O y hy) (P.isOpen_O y' hy')

include hy hy' in
theorem src_conj {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') :
    A.X.src (P.conj y y' ψ) = P.σ y (A.X.src ψ) := by
  have h1 : A.X.src ψ = A.X.tgt (P.τ y (A.X.src ψ)) := (P.tgt_τ y hy _ hψ.1).symm
  unfold conj
  rw [A.X.src_comp _ _ (by rw [A.X.src_inv, P.tgt_τ y' hy' _ hψ.2, A.X.tgt_comp _ _ h1]),
    A.X.src_comp _ _ h1]
  rfl

include hy hy' in
theorem tgt_conj {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') :
    A.X.tgt (P.conj y y' ψ) = P.σ y' (A.X.tgt ψ) := by
  have h1 : A.X.src ψ = A.X.tgt (P.τ y (A.X.src ψ)) := (P.tgt_τ y hy _ hψ.1).symm
  unfold conj
  rw [A.X.tgt_comp _ _ (by rw [A.X.src_inv, P.tgt_τ y' hy' _ hψ.2, A.X.tgt_comp _ _ h1]),
    A.X.tgt_inv]
  rfl

include hy hy' in
theorem existsUnique_rel {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') :
    ∃! h, P.D.R.Γ h (P.σ y (A.X.src ψ)) = P.conj y y' ψ := by
  have := P.D.R.existsUnique_Γ (P.conj y y' ψ)
    (by rw [src_conj hy hy' hψ]; exact σ_mem hy hψ.1)
    (by rw [tgt_conj hy hy' hψ]; exact σ_mem hy' hψ.2)
  rwa [src_conj hy hy' hψ] at this

end Near

/-- **The element `H(ψ) ∈ G_{x₀}`** relating the pulled back structures along `ψ` (`1` unless
`y, y' ∈ Z` and `ψ ∈ Dom y y'`). -/
def H (y y' : A.Obj) (ψ : A.Mor) : A.X.Isotropy P.D.x :=
  if h : y ∈ P.Z ∧ y' ∈ P.Z ∧ ψ ∈ P.Dom y y' then (existsUnique_rel h.1 h.2.1 h.2.2).exists.choose
  else 1

section Near

variable {y y' y'' : A.Obj} (hy : y ∈ P.Z) (hy' : y' ∈ P.Z) (hy'' : y'' ∈ P.Z)

theorem H_far {ψ : A.Mor} (h : ¬ (y ∈ P.Z ∧ y' ∈ P.Z)) : P.H y y' ψ = 1 :=
  dif_neg fun h' => h ⟨h'.1, h'.2.1⟩

include hy hy' in
theorem H_spec {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') :
    P.D.R.Γ (P.H y y' ψ) (P.σ y (A.X.src ψ)) = P.conj y y' ψ := by
  unfold H
  rw [dif_pos ⟨hy, hy', hψ⟩]
  exact (existsUnique_rel hy hy' hψ).exists.choose_spec

include hy hy' in
theorem H_eq_of_rel {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') {h : A.X.Isotropy P.D.x}
    (e : P.D.R.Γ h (P.σ y (A.X.src ψ)) = P.conj y y' ψ) : P.H y y' ψ = h :=
  (existsUnique_rel hy hy' hψ).unique (H_spec hy hy' hψ) e

include hy hy' in
theorem H_tgt {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') :
    P.D.R.Φ (P.H y y' ψ) (P.σ y (A.X.src ψ)) = P.σ y' (A.X.tgt ψ) := by
  rw [← P.D.R.tgt_Γ _ _ (σ_mem hy hψ.1), H_spec hy hy' hψ, tgt_conj hy hy' hψ]

include hy hy' in
theorem H_spec' {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') :
    A.X.comp (P.τ y' (A.X.tgt ψ)) (P.D.R.Γ (P.H y y' ψ) (P.σ y (A.X.src ψ))) =
      A.X.comp ψ (P.τ y (A.X.src ψ)) := by
  rw [H_spec hy hy' hψ]
  unfold conj
  refine AtomicStructData.comp_inv_comp ?_
  rw [A.X.tgt_comp _ _ (P.tgt_τ y hy _ hψ.1).symm, P.tgt_τ y' hy' _ hψ.2]

include hy hy' in
theorem H_unique {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') {h : A.X.Isotropy P.D.x}
    (htgt : P.D.R.Φ h (P.σ y (A.X.src ψ)) = P.σ y' (A.X.tgt ψ))
    (e : A.X.comp (P.τ y' (A.X.tgt ψ)) (P.D.R.Γ h (P.σ y (A.X.src ψ))) =
      A.X.comp ψ (P.τ y (A.X.src ψ))) : P.H y y' ψ = h := by
  refine H_eq_of_rel hy hy' hψ ?_
  unfold conj
  rw [← e, GroupoidStr.inv_comp_cancel_left (G := A.X.toGroupoidStr)]
  rw [P.D.R.tgt_Γ _ _ (σ_mem hy hψ.1), htgt]
  rfl

include hy hy' hy'' in
/-- **Functoriality**: `H(ψ₁ ∘ ψ₂) = H(ψ₁) H(ψ₂)`. -/
theorem H_comp {ψ₁ ψ₂ : A.Mor} (h₁ : ψ₁ ∈ P.Dom y' y'') (h₂ : ψ₂ ∈ P.Dom y y')
    (h : A.X.src ψ₁ = A.X.tgt ψ₂) :
    P.H y y'' (A.X.comp ψ₁ ψ₂) = P.H y' y'' ψ₁ * P.H y y' ψ₂ := by
  have hs : A.X.src (A.X.comp ψ₁ ψ₂) = A.X.src ψ₂ := A.X.src_comp _ _ h
  have ht : A.X.tgt (A.X.comp ψ₁ ψ₂) = A.X.tgt ψ₁ := A.X.tgt_comp _ _ h
  have hd : A.X.comp ψ₁ ψ₂ ∈ P.Dom y y'' := ⟨hs ▸ h₂.1, ht ▸ h₁.2⟩
  have hσ := σ_mem hy h₂.1
  have hΦ₂ : P.D.R.Φ (P.H y y' ψ₂) (P.σ y (A.X.src ψ₂)) = P.σ y' (A.X.src ψ₁) := by
    rw [H_tgt hy hy' h₂, h]
  refine H_unique hy hy'' hd ?_ ?_
  · rw [hs, ht, P.D.R.Φ_mul _ _ _ hσ, hΦ₂, H_tgt hy' hy'' h₁]
  · rw [hs, ht, ← P.D.R.Γ_mul _ _ hσ, hΦ₂]
    have c1 : A.X.src (P.τ y'' (A.X.tgt ψ₁)) =
        A.X.tgt (P.D.R.Γ (P.H y' y'' ψ₁) (P.σ y' (A.X.src ψ₁))) := by
      rw [P.D.R.tgt_Γ _ _ (σ_mem hy' h₁.1), H_tgt hy' hy'' h₁]; rfl
    have c2 : A.X.src (P.D.R.Γ (P.H y' y'' ψ₁) (P.σ y' (A.X.src ψ₁))) =
        A.X.tgt (P.D.R.Γ (P.H y y' ψ₂) (P.σ y (A.X.src ψ₂))) := by
      rw [P.D.R.src_Γ _ _ (σ_mem hy' h₁.1), P.D.R.tgt_Γ _ _ hσ, hΦ₂]
    have c3 : A.X.src ψ₁ = A.X.tgt (P.τ y' (A.X.src ψ₁)) := (P.tgt_τ y' hy' _ h₁.1).symm
    have c4 : A.X.src (P.τ y' (A.X.src ψ₁)) =
        A.X.tgt (P.D.R.Γ (P.H y y' ψ₂) (P.σ y (A.X.src ψ₂))) := by
      rw [P.D.R.tgt_Γ _ _ hσ, hΦ₂]; rfl
    have c5 : A.X.src ψ₂ = A.X.tgt (P.τ y (A.X.src ψ₂)) := (P.tgt_τ y hy _ h₂.1).symm
    have e2 : A.X.comp (P.τ y' (A.X.src ψ₁)) (P.D.R.Γ (P.H y y' ψ₂) (P.σ y (A.X.src ψ₂))) =
        A.X.comp ψ₂ (P.τ y (A.X.src ψ₂)) := by
      rw [h]; exact H_spec' hy hy' h₂
    rw [← A.X.comp_assoc _ _ _ c1 c2, H_spec' hy' hy'' h₁, A.X.comp_assoc _ _ _ c3 c4, e2,
      ← A.X.comp_assoc _ _ _ h c5]

include hy in
theorem H_unit {z : A.Obj} (hz : z ∈ P.O y) : P.H y y (A.X.unit z) = 1 := by
  have hd : A.X.unit z ∈ P.Dom y y :=
    ⟨by rw [A.X.src_unit]; exact hz, by rw [A.X.tgt_unit]; exact hz⟩
  have := H_comp hy hy hy hd hd (by rw [A.X.src_unit, A.X.tgt_unit])
  rw [GroupoidStr.comp_unit_of_eq (G := A.X.toGroupoidStr) (A.X.src_unit z)] at this
  exact left_eq_mul.1 this |>.symm ▸ rfl

include hy hy' in
theorem H_inv {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') : P.H y' y (A.X.inv ψ) = (P.H y y' ψ)⁻¹ := by
  have hd : A.X.inv ψ ∈ P.Dom y' y := ⟨by rw [A.X.src_inv]; exact hψ.2,
    by rw [A.X.tgt_inv]; exact hψ.1⟩
  have := H_comp hy hy' hy hd hψ (by rw [A.X.src_inv])
  rw [A.X.inv_comp, H_unit hy hψ.1] at this
  exact eq_inv_of_mul_eq_one_left this.symm

end Near

/-! ### Local constancy -/

section Near

variable {y y' : A.Obj} (hy : y ∈ P.Z) (hy' : y' ∈ P.Z)

include hy hy' in
theorem continuousOn_conj : ContinuousOn (P.conj y y') (P.Dom y y') := by
  have hτ' : ContinuousOn (fun ψ => P.τ y' (A.X.tgt ψ)) (P.Dom y y') :=
    (P.isScSmoothOn_τ y' hy').continuousOn.comp A.X.continuous_tgt.continuousOn fun _ h => h.2
  have hτ : ContinuousOn (fun ψ => P.τ y (A.X.src ψ)) (P.Dom y y') :=
    (P.isScSmoothOn_τ y hy).continuousOn.comp A.X.continuous_src.continuousOn fun _ h => h.1
  have hin : ContinuousOn (fun ψ => A.X.comp ψ (P.τ y (A.X.src ψ))) (P.Dom y y') :=
    continuousOn_comp_of_continuousOn continuousOn_id hτ fun ψ h => (P.tgt_τ y hy _ h.1).symm
  exact continuousOn_comp_of_continuousOn (A.X.continuous_inv.comp_continuousOn hτ') hin
    fun ψ h => by
      rw [A.X.src_inv, P.tgt_τ y' hy' _ h.2, A.X.tgt_comp _ _ (P.tgt_τ y hy _ h.1).symm]

include hy hy' in
/-- **`H` is locally constant** on the morphisms between `O(y)` and `O(y')`. -/
theorem H_eventually {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') :
    ∀ᶠ ψ' in 𝓝 ψ, P.H y y' ψ' = P.H y y' ψ := by
  have hσ : ContinuousOn (fun ψ => P.σ y (A.X.src ψ)) (P.Dom y y') :=
    A.X.continuous_src.comp_continuousOn
      ((P.isScSmoothOn_τ y hy).continuousOn.comp A.X.continuous_src.continuousOn fun _ h => h.1)
  have hev := eventually_eq_of_existsUnique (isOpen_Dom hy hy') (continuousOn_conj hy hy')
    (gs := fun h ψ => P.D.R.Γ h (P.σ y (A.X.src ψ)))
    (fun h => (P.D.R.isScSmoothOn_Γ h).continuousOn.comp hσ fun _ h' => σ_mem hy h'.1)
    (fun _ h => existsUnique_rel hy hy' h) hψ (H_spec hy hy' hψ)
  exact hev.mono fun _ h => H_eq_of_rel hy hy' h.1 h.2

end Near

/-! ### The homomorphisms `γ_y : G_y → G_{x₀}` -/

theorem Γ₀_mem_Dom {y : A.Obj} (hy : y ∈ P.Z) (g : A.X.Isotropy y) :
    (P.𝒰₀.nbhd y).rep.Γ g y ∈ P.Dom y y := by
  have hU := (P.𝒰₀.nbhd y).rep.mem_U
  refine ⟨?_, ?_⟩
  · rw [(P.𝒰₀.nbhd y).rep.src_Γ g y hU]; exact P.mem_O y hy
  · rw [(P.𝒰₀.nbhd y).rep.tgt_Γ g y hU, (P.𝒰₀.nbhd y).rep.Φ_self]; exact P.mem_O y hy

variable (P) in
/-- **`γ_y(g) = H(Γ(g, y))`**, a homomorphism `G_y → G_{x₀}` (trivial for `y ∉ Z`). -/
def γ (y : A.Obj) : A.X.Isotropy y →* A.X.Isotropy P.D.x where
  toFun g := P.H y y ((P.𝒰₀.nbhd y).rep.Γ g y)
  map_one' := by
    rw [(P.𝒰₀.nbhd y).Γ_one (P.𝒰₀.nbhd y).mem_U]
    by_cases hy : y ∈ P.Z
    · exact H_unit hy (P.mem_O y hy)
    · exact H_far fun h => hy h.1
  map_mul' g h := by
    by_cases hy : y ∈ P.Z
    · have hU := (P.𝒰₀.nbhd y).rep.mem_U
      rw [← (P.𝒰₀.nbhd y).Γ_mul g h (P.𝒰₀.nbhd y).mem_U, (P.𝒰₀.nbhd y).rep.Φ_self h]
      exact H_comp hy hy hy (Γ₀_mem_Dom hy g) (Γ₀_mem_Dom hy h)
        (by rw [(P.𝒰₀.nbhd y).rep.src_Γ g y hU, (P.𝒰₀.nbhd y).rep.tgt_Γ h y hU,
          (P.𝒰₀.nbhd y).rep.Φ_self])
    · rw [H_far (fun h' => hy h'.1), H_far (fun h' => hy h'.1), H_far (fun h' => hy h'.1),
        mul_one]

theorem γ_apply (y : A.Obj) (g : A.X.Isotropy y) :
    P.γ y g = P.H y y ((P.𝒰₀.nbhd y).rep.Γ g y) := rfl

theorem γ_far {y : A.Obj} (hy : y ∉ P.Z) (g : A.X.Isotropy y) : P.γ y g = 1 :=
  H_far fun h => hy h.1

/-! ### The good system -/

variable (P) in
/-- Where the pulled back structure at `y ∈ Z` is equivariant through `γ_y`. -/
def Wn (y : A.Obj) : Set A.Obj :=
  {z | z ∈ (P.𝒰₀.nbhd y).U ∧ z ∈ P.O y ∧ ∀ g, (P.𝒰₀.nbhd y).rep.Φ g z ∈ P.O y ∧
    P.H y y ((P.𝒰₀.nbhd y).rep.Γ g z) = P.γ y g}

theorem eventually_Wn {y : A.Obj} (hy : y ∈ P.Z) : ∀ᶠ z in 𝓝 y, z ∈ P.Wn y := by
  set N := P.𝒰₀.nbhd y
  have hUn : N.rep.U ∈ 𝓝 y := N.rep.isOpen_U.mem_nhds N.rep.mem_U
  have hg : ∀ g, ∀ᶠ z in 𝓝 y, N.rep.Φ g z ∈ P.O y ∧ P.H y y (N.rep.Γ g z) = P.γ y g := by
    intro g
    have h1 : ∀ᶠ z in 𝓝 y, N.rep.Φ g z ∈ P.O y := by
      have hc := ((N.rep.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn).continuousAt hUn
      have : N.rep.Φ g y ∈ P.O y := by rw [N.rep.Φ_self]; exact P.mem_O y hy
      exact hc.preimage_mem_nhds ((P.isOpen_O y hy).mem_nhds this)
    have h2 : ∀ᶠ z in 𝓝 y, P.H y y (N.rep.Γ g z) = P.γ y g := by
      have hc := ((N.rep.isScSmoothOn_Γ g).continuousOn).continuousAt hUn
      exact hc.eventually (H_eventually hy hy (Γ₀_mem_Dom hy g))
    exact h1.and h2
  filter_upwards [N.isOpen_U.mem_nhds N.mem_U, (P.isOpen_O y hy).mem_nhds (P.mem_O y hy),
    eventually_all.2 hg] with z h1 h2 h3 using ⟨h1, h2, h3⟩

variable (P) in
/-- `W(y)`: the interior of `Wn y` for `y ∈ Z`, the complement of `Z` otherwise. -/
def W (y : A.Obj) : Set A.Obj := if y ∈ P.Z then interior (P.Wn y) else P.Zᶜ

theorem isOpen_W (y : A.Obj) : IsOpen (P.W y) := by
  unfold W
  split_ifs
  · exact isOpen_interior
  · exact P.isClosed_Z.isOpen_compl

theorem mem_W (y : A.Obj) : y ∈ P.W y := by
  unfold W
  split_ifs with hy
  · exact mem_interior_iff_mem_nhds.2 (eventually_Wn hy)
  · exact hy

variable (P) in
/-- The neighbourhoods `U(y) ⊆ U₀(y) ∩ W(y)` with the natural actions of `𝒰₀`. -/
def M (y : A.Obj) : A.X.NatNbhd y :=
  (P.𝒰₀.nbhd y).restrict _ ((P.𝒰₀.nbhd y).isOpen_invariantCore (P.isOpen_W y))
    ((P.𝒰₀.nbhd y).mem_invariantCore (P.mem_W y))
    (fun _ hz => ((P.𝒰₀.nbhd y).invariantCore_subset _ hz).1)
    ((P.𝒰₀.nbhd y).mapsTo_Φ_invariantCore _)

variable (P) in
/-- **The good system of the proof.** -/
def 𝒰 : A.X.GoodSystem :=
  P.𝒰₀.ofSubset P.M fun y _ hz => ((P.𝒰₀.nbhd y).invariantCore_subset _ hz).1

theorem U_subset_W (y : A.Obj) : P.𝒰.U y ⊆ P.W y :=
  fun _ hz => ((P.𝒰₀.nbhd y).invariantCore_subset _ hz).2

theorem mem_Wn {y z : A.Obj} (hy : y ∈ P.Z) (hz : z ∈ P.𝒰.U y) : z ∈ P.Wn y := by
  have := P.U_subset_W y hz
  unfold W at this
  rw [if_pos hy] at this
  exact interior_subset this

theorem U_subset_O {y : A.Obj} (hy : y ∈ P.Z) : P.𝒰.U y ⊆ P.O y :=
  fun _ hz => (mem_Wn hy hz).2.1

theorem not_mem_Z {y z : A.Obj} (hy : y ∉ P.Z) (hz : z ∈ P.𝒰.U y) : z ∉ P.Z := by
  have := P.U_subset_W y hz
  unfold W at this
  rwa [if_neg hy] at this

theorem W_cond {y z : A.Obj} (hy : y ∈ P.Z) (hz : z ∈ P.𝒰.U y) (g : A.X.Isotropy y) :
    P.H y y ((P.𝒰.nbhd y).rep.Γ g z) = P.γ y g :=
  ((mem_Wn hy hz).2.2 g).2

theorem mor_subset_Dom {y y' : A.Obj} (hy : y ∈ P.Z) (hy' : y' ∈ P.Z) :
    P.𝒰.mor y y' ⊆ P.Dom y y' :=
  fun _ h => ⟨U_subset_O hy h.1, U_subset_O hy' h.2⟩

/-! ### The symmetric structures -/

variable (P) in
/-- The sections at `y`: the atomic sections pulled back by `τ_y` (`y ∈ Z`), zero otherwise. -/
def sec (y : A.Obj) (i : P.D.I) : A.Obj → A.W :=
  if y ∈ P.Z then transportSection (P.τ y) (fun z => P.D.s i (P.σ y z)) else fiberZero A.P

theorem sec_of_mem {y : A.Obj} (hy : y ∈ P.Z) (i : P.D.I) :
    P.sec y i = transportSection (P.τ y) (fun z => P.D.s i (P.σ y z)) := if_pos hy

theorem sec_of_not_mem {y : A.Obj} (hy : y ∉ P.Z) (i : P.D.I) : P.sec y i = fiberZero A.P :=
  if_neg hy

theorem P_s_σ {y z : A.Obj} (hy : y ∈ P.Z) (hz : z ∈ P.O y) (i : P.D.I) :
    A.P (P.D.s i (P.σ y z)) = P.σ y z :=
  (P.D.isScPlusSectionOn i).1 _ (σ_mem hy hz)

theorem sec_apply {y z : A.Obj} (hy : y ∈ P.Z) (hz : z ∈ P.O y) (i : P.D.I) :
    P.sec y i z = fibAct (P.τ y z) (P.D.s i (P.σ y z)) := by
  rw [sec_of_mem hy]
  exact transportSection_eq_fibAct (P_s_σ hy hz i)

/-- **The pulled back sections are related by `H`**:
`s^{y'}_{H(ψ) i}(t ψ) = μ(ψ, s^y_i(s ψ))`. -/
theorem sec_compat {y y' : A.Obj} (hy : y ∈ P.Z) (hy' : y' ∈ P.Z) {ψ : A.Mor}
    (hψ : ψ ∈ P.Dom y y') (i : P.D.I) :
    P.sec y' (P.H y y' ψ • i) (A.X.tgt ψ) = fibAct ψ (P.sec y i (A.X.src ψ)) := by
  have hσ := σ_mem hy hψ.1
  have hsi := P_s_σ hy hψ.1 i
  have hsi' : A.P (P.D.s i (P.σ y (A.X.src ψ))) =
      A.X.src (P.D.R.Γ (P.H y y' ψ) (P.σ y (A.X.src ψ))) := by
    rw [hsi, P.D.R.src_Γ _ _ hσ]
  have c : A.X.src (P.τ y' (A.X.tgt ψ)) = A.X.tgt (P.D.R.Γ (P.H y y' ψ) (P.σ y (A.X.src ψ))) := by
    rw [P.D.R.tgt_Γ _ _ hσ, H_tgt hy hy' hψ]; rfl
  rw [sec_apply hy' hψ.2, sec_apply hy hψ.1, ← H_tgt hy hy' hψ, P.D.equivariant _ i _ hσ,
    ← fibAct_of, ← fibAct_comp hsi' c, H_spec' hy hy' hψ,
    fibAct_comp hsi (P.tgt_τ y hy _ hψ.1).symm]

theorem sec_eq_zero {y z : A.Obj} (hz : z ∈ P.𝒰.U y) (hzZ : z ∉ P.Z) (i : P.D.I) :
    P.sec y i z = fiberZero A.P z := by
  by_cases hy : y ∈ P.Z
  · have hzO := U_subset_O hy hz
    have hV : P.σ y z ∉ P.D.V := fun hV => by
      have h1 : A.X.src (P.τ y z) ∈ P.Z := ⟨_, subset_closure hV, rfl⟩
      rw [mem_Z_iff_of_mor, P.tgt_τ y hy z hzO] at h1
      exact hzZ h1
    rw [sec_apply hy hzO, P.D.vanish i _ (σ_mem hy hzO) hV]
    exact fibAct_fiberZero rfl (P.tgt_τ y hy z hzO)
  · rw [sec_of_not_mem hy]

variable (P) in
/-- **The symmetric structure at `y`**: index set `I_{x₀}`, `G_y` acting through `γ_y`. -/
@[reducible] def S (y : A.Obj) : SymmetricStructureOn A Λ (P.𝒰.nbhd y) where
  I := P.D.I
  mulAction := MulAction.compHom P.D.I (P.γ y)
  s := P.sec y
  isScPlusSectionOn i := by
    by_cases hy : y ∈ P.Z
    · rw [sec_of_mem hy]
      exact (P.isScPlusSectionOn y hy i).mono (P.𝒰.isOpen_U y) (U_subset_O hy)
    · rw [sec_of_not_mem hy]
      exact isScPlusSectionOn_fiberZero (P.𝒰.isOpen_U y)
  equivariant g i z hz := by
    by_cases hy : y ∈ P.Z
    · have hd : (P.𝒰.nbhd y).rep.Γ g z ∈ P.Dom y y :=
        ⟨by rw [(P.𝒰.nbhd y).src_Γ g hz]; exact U_subset_O hy hz,
          by rw [(P.𝒰.nbhd y).tgt_Γ g hz]; exact U_subset_O hy ((P.𝒰.nbhd y).Φ_mem g hz)⟩
      have := sec_compat hy hy hd i
      rw [W_cond hy hz g, (P.𝒰.nbhd y).tgt_Γ g hz, (P.𝒰.nbhd y).src_Γ g hz] at this
      exact this
    · rw [sec_of_not_mem hy, sec_of_not_mem hy]
      exact (fibAct_fiberZero ((P.𝒰.nbhd y).src_Γ g hz) ((P.𝒰.nbhd y).tgt_Γ g hz)).symm
  rep w hw := by
    by_cases hy : y ∈ P.Z
    · have hz : A.P w ∈ P.O y := U_subset_O hy hw
      have hs : A.P w = A.X.src (A.X.inv (P.τ y (A.P w))) := by
        rw [A.X.src_inv, P.tgt_τ y hy _ hz]
      have ht : A.X.tgt (A.X.inv (P.τ y (A.P w))) ∈ P.D.R.U := by
        rw [A.X.tgt_inv]; exact σ_mem hy hz
      have hPv : A.P (A.E.μ ⟨(A.X.inv (P.τ y (A.P w)), w), hs⟩) = P.σ y (A.P w) := by
        rw [A.E.P_μ]; exact A.X.tgt_inv _
      rw [P.hD.1 w _ hs ht]
      unfold AtomicData.count
      rw [hPv, ← fibAct_of hs]
      congr 3
      refine Finset.filter_congr fun i _ => ?_
      rw [sec_apply hy hz]
      have hw' : A.P w = A.X.tgt (P.τ y (A.P w)) := (P.tgt_τ y hy _ hz).symm
      constructor
      · intro e; rw [e]; exact fibAct_fibAct_inv hw'
      · intro e
        exact (fibAct_inv_fibAct (P_s_σ hy hz i)).symm.trans (congrArg _ e)
    · have hwZ : A.P w ∉ P.Z := not_mem_Z hy hw
      rw [congrFun P.hD.eq_mult w, P.D.mult_eq_zeroMultisection hwZ]
      simp only [sec_of_not_mem hy]
      unfold zeroMultisection
      by_cases h0 : w = fiberZero A.P (A.P w)
      · rw [if_pos h0, Finset.filter_true_of_mem fun i _ => h0.symm, Finset.card_univ,
          inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]
      · rw [if_neg h0, Finset.filter_false_of_mem fun i _ e => h0 e.symm, Finset.card_empty,
          Nat.cast_zero, mul_zero]

variable (P) in
/-- The decoration `(𝒰, S)`. -/
abbrev dec : Decoration A Λ := ⟨P.𝒰, P.S⟩

/-! ### The correspondences -/

variable (P) in
/-- **The correspondences**: `[I ←id I →H(φ) I]` if `y, y'` both lie in `Z` or both outside,
the full correspondence otherwise. -/
def corr (y y' : A.Obj) (φ : A.Mor) : IndexCorr P.D.I P.D.I :=
  if y ∈ P.Z ↔ y' ∈ P.Z then IndexCorr.ofEquiv (MulAction.toPerm (P.H y y' φ))
  else IndexCorr.full _ _

theorem corr_of_iff {y y' : A.Obj} (h : y ∈ P.Z ↔ y' ∈ P.Z) (φ : A.Mor) :
    P.corr y y' φ = IndexCorr.ofEquiv (MulAction.toPerm (P.H y y' φ)) := if_pos h

theorem corr_of_not_iff {y y' : A.Obj} (h : ¬ (y ∈ P.Z ↔ y' ∈ P.Z)) (φ : A.Mor) :
    P.corr y y' φ = IndexCorr.full _ _ := if_neg h

theorem H_eventually' {y y' : A.Obj} (h : y ∈ P.Z ↔ y' ∈ P.Z) {φ : A.Mor}
    (hφ : φ ∈ P.𝒰.mor y y') : ∀ᶠ ψ in 𝓝 φ, P.H y y' ψ = P.H y y' φ := by
  by_cases hy : y ∈ P.Z
  · exact H_eventually hy (h.1 hy) (mor_subset_Dom hy (h.1 hy) hφ)
  · have hy' : y' ∉ P.Z := fun h' => hy (h.2 h')
    exact .of_forall fun ψ => by rw [H_far (fun h' => hy h'.1), H_far (fun h' => hy h'.1)]

theorem H_biact {y y' : A.Obj} (h : y ∈ P.Z ↔ y' ∈ P.Z) {φ : A.Mor} (hφ : φ ∈ P.𝒰.mor y y')
    (g' : A.X.Isotropy y') (g : A.X.Isotropy y) :
    P.H y y' (P.𝒰.biact y y' g' φ g) = P.γ y' g' * P.H y y' φ * P.γ y g := by
  by_cases hy : y ∈ P.Z
  · have hy' := h.1 hy
    set N := P.𝒰.nbhd y
    set N' := P.𝒰.nbhd y'
    have hz : N.rep.Φ g⁻¹ (A.X.src φ) ∈ N.U := N.Φ_mem g⁻¹ hφ.1
    have hA : N'.rep.Γ g' (A.X.tgt φ) ∈ P.Dom y' y' :=
      ⟨by rw [N'.src_Γ g' hφ.2]; exact U_subset_O hy' hφ.2,
        by rw [N'.tgt_Γ g' hφ.2]; exact U_subset_O hy' (N'.Φ_mem g' hφ.2)⟩
    have hB : N.rep.Γ g (N.rep.Φ g⁻¹ (A.X.src φ)) ∈ P.Dom y y :=
      ⟨by rw [N.src_Γ g hz]; exact U_subset_O hy hz,
        by rw [N.tgt_Γ g hz, N.Φ_Φ_inv g hφ.1]; exact U_subset_O hy hφ.1⟩
    have hφd := mor_subset_Dom hy hy' hφ
    have hBc : A.X.src φ = A.X.tgt (N.rep.Γ g (N.rep.Φ g⁻¹ (A.X.src φ))) := by
      rw [N.tgt_Γ g hz, N.Φ_Φ_inv g hφ.1]
    have hφB : A.X.comp φ (N.rep.Γ g (N.rep.Φ g⁻¹ (A.X.src φ))) ∈ P.Dom y y' :=
      ⟨by rw [A.X.src_comp _ _ hBc]; exact hB.1, by rw [A.X.tgt_comp _ _ hBc]; exact hφd.2⟩
    show P.H y y' (A.X.comp (N'.rep.Γ g' (A.X.tgt φ))
      (A.X.comp φ (N.rep.Γ g (N.rep.Φ g⁻¹ (A.X.src φ))))) = _
    rw [H_comp hy hy' hy' hA hφB (by rw [N'.src_Γ g' hφ.2, A.X.tgt_comp _ _ hBc]),
      H_comp hy hy hy' hφd hB hBc, W_cond hy' hφ.2 g', W_cond hy hz g, mul_assoc]
  · have hy' : y' ∉ P.Z := fun h' => hy (h.2 h')
    rw [H_far (fun h' => hy h'.1), H_far (fun h' => hy h'.1), γ_far hy, γ_far hy', one_mul,
      one_mul]

/-- **Definition 13.3.4 for `corr`.** -/
theorem isCorrespondence (y y' : A.Obj) : P.dec.IsCorrespondence y y' (P.corr y y') where
  locallyConstant φ hφ := by
    by_cases h : y ∈ P.Z ↔ y' ∈ P.Z
    · exact (H_eventually' h hφ).mono fun ψ hψ => by rw [corr_of_iff h, corr_of_iff h, hψ]
    · exact .of_forall fun ψ => by rw [corr_of_not_iff h, corr_of_not_iff h]
  finite := by
    by_cases h : y ∈ P.Z ↔ y' ∈ P.Z
    · refine (Set.finite_range fun k : A.X.Isotropy P.D.x =>
        (IndexCorr.ofEquiv (MulAction.toPerm k) : IndexCorr P.D.I P.D.I)).subset ?_
      rintro _ ⟨φ, -, rfl⟩
      exact ⟨_, (corr_of_iff h φ).symm⟩
    · refine (Set.finite_singleton (IndexCorr.full P.D.I P.D.I)).subset ?_
      rintro _ ⟨φ, -, rfl⟩
      exact corr_of_not_iff h φ
  biact φ hφ g' g := by
    by_cases h : y ∈ P.Z ↔ y' ∈ P.Z
    · rw [corr_of_iff h, corr_of_iff h, H_biact h hφ]
      rw [@IndexCorr.biact_ofEquiv _ _ _ _ _ _ (P.S y).mulAction (P.S y').mulAction _ g' _ g]
      refine congrArg IndexCorr.ofEquiv (Equiv.ext fun i => ?_)
      show (P.γ y' g' * P.H y y' φ * P.γ y g) • i = P.γ y' g' • (P.H y y' φ • (P.γ y g • i))
      rw [mul_smul, mul_smul]
    · rw [corr_of_not_iff h, corr_of_not_iff h]
      rw [@IndexCorr.biact_full _ _ _ _ _ _ (P.S y).mulAction (P.S y').mulAction _ _ _ _ g' g]
  compat φ hφ := by
    by_cases hn : y ∈ P.Z ∧ y' ∈ P.Z
    · rw [corr_of_iff (iff_of_true hn.1 hn.2)]
      refine IndexCorr.sat_ofEquiv _ fun i ψ hψ => ?_
      have hψm : ψ ∈ P.𝒰.mor y y' := connectedComponentIn_subset _ _ hψ
      have e : P.H y y' ψ = P.H y y' φ :=
        eq_of_mem_connectedComponentIn (P.𝒰.isOpen_mor y y')
          (fun _ h' => H_eventually' (iff_of_true hn.1 hn.2) h') hφ hψ
      show P.sec y' (P.H y y' φ • i) (A.X.tgt ψ) = fibAct ψ (P.sec y i (A.X.src ψ))
      rw [← e]
      exact sec_compat hn.1 hn.2 (mor_subset_Dom hn.1 hn.2 hψm) i
    · refine IndexCorr.sat_of_forall (fun i j ψ hψ => ?_) _
      have hψm : ψ ∈ P.𝒰.mor y y' := connectedComponentIn_subset _ _ hψ
      have hs : A.X.src ψ ∉ P.Z ∧ A.X.tgt ψ ∉ P.Z := by
        by_cases hy : y ∈ P.Z
        · have ht : A.X.tgt ψ ∉ P.Z := not_mem_Z (fun hy' => hn ⟨hy, hy'⟩) hψm.2
          exact ⟨fun h' => ht ((P.mem_Z_iff_of_mor ψ).1 h'), ht⟩
        · have hs : A.X.src ψ ∉ P.Z := not_mem_Z hy hψm.1
          exact ⟨hs, fun h' => hs ((P.mem_Z_iff_of_mor ψ).2 h')⟩
      show P.sec y' j (A.X.tgt ψ) = fibAct ψ (P.sec y i (A.X.src ψ))
      rw [sec_eq_zero hψm.2 hs.2, sec_eq_zero hψm.1 hs.1]
      exact (fibAct_fiberZero rfl rfl).symm

variable (P) in
/-- **The correspondences `τ` of Definition 13.3.6.** -/
def tau : P.dec.Tau where
  τ := P.corr
  isCorrespondence := P.isCorrespondence
  diag y g z hz := by
    refine (corr_of_iff Iff.rfl _).trans (congrArg IndexCorr.ofEquiv (Equiv.ext fun i => ?_))
    show P.H y y _ • i = P.γ y g • i
    by_cases hy : y ∈ P.Z
    · rw [W_cond hy hz g]
    · rw [H_far (fun h' => hy h'.1), γ_far hy]
  swap y y' φ hφ := by
    by_cases h : y ∈ P.Z ↔ y' ∈ P.Z
    · rw [corr_of_iff h.symm, corr_of_iff h, IndexCorr.swap_ofEquiv]
      refine congrArg IndexCorr.ofEquiv (Equiv.ext fun i => ?_)
      show P.H y' y φ • i = (P.H y y' (A.X.inv φ))⁻¹ • i
      by_cases hy : y ∈ P.Z
      · have hy' := h.1 hy
        have hd : A.X.inv φ ∈ P.Dom y y' :=
          ⟨by rw [A.X.src_inv]; exact U_subset_O hy hφ.2,
            by rw [A.X.tgt_inv]; exact U_subset_O hy' hφ.1⟩
        rw [← H_inv hy hy' hd, GroupoidStr.inv_inv]
      · rw [H_far (fun h' => hy h'.2), H_far (fun h' => hy h'.1), inv_one]
    · rw [corr_of_not_iff (fun h' => h h'.symm), corr_of_not_iff h, IndexCorr.swap_full]

end AtomicStructData

/-- **The proof of Theorem 13.5.3**: `Λ` is structurable, with the decoration `dec` and the
correspondences `tau`. -/
theorem AtomicStructData.isStructurable {Λ : A.W → ℚ≥0} (P : AtomicStructData Λ) :
    IsStructurable A Λ :=
  ⟨P.hΛ, P.dec, ⟨P.tau⟩⟩

/-- **2021 Theorem 13.5.3, p. 630 (2017: Theorem 13.6), given a good system**: an atomic
sc⁺-multisection functor is structurable. -/
theorem theorem_13_5_3_of_goodSystem (h𝒰 : Nonempty A.X.GoodSystem) {Λ : A.W → ℚ≥0}
    (hΛ : IsAtomic A Λ) : IsStructurable A Λ := by
  obtain ⟨hΛm, D, hD⟩ := hΛ
  obtain ⟨P, -⟩ := exists_atomicStructData hΛm D hD h𝒰.some
  exact P.isStructurable

/-- **2021 Theorem 13.5.3, p. 630 (2017: Theorem 13.6)**: an atomic sc⁺-multisection functor is
structurable exactly when a good system exists (structurability includes one, Definition
13.3.6; the text assumes one, Theorem 13.1.8). -/
theorem theorem_13_5_3 {Λ : A.W → ℚ≥0} (hΛ : IsAtomic A Λ) :
    IsStructurable A Λ ↔ Nonempty A.X.GoodSystem :=
  ⟨fun h => ⟨h.2.choose.𝒰⟩, fun h => theorem_13_5_3_of_goodSystem h hΛ⟩

/-- **Theorem 13.5.3 for paracompact `|X|`** (good systems exist, Theorem 13.1.8). -/
theorem theorem_13_5_3_of_paracompact (hX : A.X.HasParacompactOrbitSpace) {Λ : A.W → ℚ≥0}
    (hΛ : IsAtomic A Λ) : IsStructurable A Λ :=
  theorem_13_5_3_of_goodSystem
    ⟨(A.X.theorem_13_1_8 hX (fun _ => univ) (fun _ => isOpen_univ) fun _ => mem_univ _).choose⟩
    hΛ

/-- **The last sentence of 2021 Theorem 13.5.5, p. 633**: the atomic `Λ` of Construction II is
structurable (given a good system), from Theorem 13.5.3 as in the text. -/
theorem theorem_13_5_5_structurable (h𝒰 : Nonempty A.X.GoodSystem)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) {x : A.Obj}
    (hx : x ∈ A.X.PObj.smoothSet) (R : A.X.NaturalRep x) (hprop : A.X.HasPropernessProperty R.U)
    (F : SymmetricFamily A R) [Nonempty F.I] :
    ∃ Λ : A.W → ℚ≥0, IsAtomic A Λ ∧
      (∀ w, A.P w ∉ A.X.saturation R.U → Λ w = zeroMultisection A w) ∧
      (∀ w, A.P w ∈ R.U → Λ w = (Fintype.card F.I : ℚ≥0)⁻¹ *
        ((Finset.univ.filter fun i => F.s i (A.P w) = w).card : ℚ≥0)) ∧ IsStructurable A Λ :=
  theorem_13_5_5_structurable_hyp (fun _ hΛ => theorem_13_5_3_of_goodSystem h𝒰 hΛ) hbump hx R
    hprop F

end SBLocalization

end Polyfold
