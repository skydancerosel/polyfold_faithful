import Polyfold.Chapter13.AtomicStructurable

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.5,
**Theorem 14.5.5** (p. 678; 2017: Theorem 14.3), the structurability criterion.

# A structurability criterion

## The text, paraphrased

(Theorem 14.5.5) Let `P : W → X` be a strong bundle over an ep-groupoid with paracompact `|X|`
and `Λ : W → ℚ⁺` an sc⁺-multisection functor.  Assume there are `A ⊆ X` and, for `a ∈ A`, open
`U(a)` and `V_a ⊆ U(a)` with (a) `U(a)` `G_a`-invariant and `t` proper on `s⁻¹(cl U(a))`,
(b) `V_a` `G_a`-invariant with `cl|V_a| ⊆ |U(a)|`, (c) `⋃ |V_a| = |X|`, (d) symmetric
sc⁺-section structures `(sᵃᵢ)_{i ∈ I_a}` on `V_a` representing `Λ`, and (e) locally constant
correspondences `τ_{a,a'}` on `V(a, a') = {φ | s(φ) ∈ V_a, t(φ) ∈ V_{a'}}` with finitely many
values relating `sᵃ` and `sᵃ'`.  Then `Λ` is structurable.  *Proof*: restrict to `V = ⋃ V_a`
(an equivalence, Theorem 13.4.3), choose `a_x` with `x ∈ V_{a_x}` and small `Q(x) ⊆ V_{a_x}`,
restrict the data, `G_x` acting on `I_{a_x}` through `g ↦ h_g` with `Γ(h_g, x) = g`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `CriterionData A Λ`: the data (a)–(e), indexed by a type `ι` with points `pt a`.
  The correspondences are read as in Definitions 13.3.4 and 13.3.6: locally constant, finitely
  many values, equivariant for the bi-actions of the `U(a)`, relating the sections pointwise on
  `V(a, a')`, `τ_{a,a}(Γ(g, y)) = [I_a ←id I_a →g I_a]` and `τ_{a',a}(φ) = τ_{a,a'}(φ⁻¹)♯`.
* `CriterionData.Transport`: for every object `y` an index `a_y`, an open `O(y) ∋ y` and an
  sc-smooth `τ_y : O(y) → 𝐗` with `t(τ_y(z)) = z` and `s(τ_y(z)) ∈ V_{a_y}` (from (c)), and a good
  system `𝒰₀` (`exists_transport`).
* **`theorem_14_5_5`**: `Λ` is structurable.  The structure at `y` is the one of `V_{a_y}`
  pulled back by `τ_y` (so the proof does not pass through the restriction to `V` and
  Theorem 13.4.3); `G_y` acts on `I_{a_y}` through `γ_y : G_y →* G_{a_y}`, and
  `τ̄_{y,y'}(φ) = τ_{a_y,a_{y'}}(τ_{y'}(t φ)⁻¹ ∘ φ ∘ τ_y(s φ))`.

## Reading

* The properness in (a) and the closure condition in (b) are not used: the good system comes
  from Theorem 13.1.8 (`|X|` paracompact), and the transported structures are defined on all of
  the neighbourhoods `O(y)`.
* "Correspondence" in (e) includes the conditions of Definitions 13.3.4 (2) and 13.3.6 (1)–(2)
  for the `τ_{a,a'}`; the proof in the text uses (1) of Definition 13.3.6 for `τ_{a_x,a_x}`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### Correspondences under a change of the acting groups -/

namespace IndexCorr

variable {α β : Type u} {G G' H H' : Type*} [Group G] [Group G'] [Group H] [Group H']
  [MulAction G α] [MulAction G' β]

/-- The bi-action for actions pulled back along homomorphisms `γ : H → G`, `γ' : H' → G'`. -/
theorem biact_compHom_gl (γ : H →* G) (γ' : H' →* G') (τ : IndexCorr α β) (h' : H') (h : H) :
    @biact α β H H' _ _ (MulAction.compHom α γ) (MulAction.compHom β γ') h' τ h =
      biact (γ' h') τ (γ h) := by
  refine ind (fun d => mk_eq_mk.2 ⟨_root_.Equiv.refl _, fun k => ⟨?_, rfl⟩⟩) τ
  change (γ h)⁻¹ • d.a k = γ h⁻¹ • d.a k
  rw [map_inv]

/-- A condition holding for every member of a family holds for the conjunction. -/
theorem sat_forall {γ : Type*} {S : Set γ} {R : γ → α → β → Prop} {τ : IndexCorr α β}
    (h : ∀ c ∈ S, τ.Sat (R c)) : τ.Sat fun i j => ∀ c ∈ S, R c i j := by
  revert h
  exact ind (fun d h k c hc => h c hc k) τ

theorem ofPerm_compHom_gl [Fintype α] (γ : H →* G) (h : H) :
    @ofPerm α H _ _ (MulAction.compHom α γ) h = ofPerm (γ h) := rfl

end IndexCorr

/-! ### The data of Theorem 14.5.5 -/

/-- **The hypotheses (a)–(e) of Theorem 14.5.5**: indices `a : ι` with points `pt a`,
neighbourhoods `U(a)` with the natural `G_a`-action, invariant open `V_a ⊆ U(a)` with
`⋃ |V_a| = |X|`, symmetric sc⁺-section structures on the `V_a` representing `Λ`, and
correspondences `τ_{a,a'}` on `V(a, a')`. -/
structure CriterionData (A : SEP.{u}) (Λ : A.W → ℚ≥0) where
  /-- The index set `A`. -/
  ι : Type u
  /-- The point `a ∈ X` of an index. -/
  pt : ι → A.Obj
  /-- (a) `U(a)` with the natural `G_a`-action. -/
  N : ∀ a, A.X.NatNbhd (pt a)
  /-- (b) The open sets `V_a`. -/
  V : ι → Set A.Obj
  isOpen_V : ∀ a, IsOpen (V a)
  V_subset : ∀ a, V a ⊆ (N a).U
  mapsTo_V : ∀ a g, MapsTo ((N a).rep.Φ g) (V a) (V a)
  /-- (c) `⋃ |V_a| = |X|`. -/
  cover : ∀ x, ∃ a, x ∈ A.X.saturation (V a)
  /-- (d) The index sets `I_a`. -/
  I : ι → Type u
  [fintype : ∀ a, Fintype (I a)]
  [mulAction : ∀ a, MulAction (A.X.Isotropy (pt a)) (I a)]
  /-- (d) The sections `sᵃᵢ` on `V_a`. -/
  s : ∀ a, I a → A.Obj → A.W
  isScPlusSectionOn : ∀ a i, IsScPlusSectionOn A (s a i) (V a)
  equivariant : ∀ a (g : A.X.Isotropy (pt a)) i, ∀ y ∈ V a,
    s a (g • i) ((N a).rep.Φ g y) = fibAct ((N a).rep.Γ g y) (s a i y)
  rep : ∀ a w, A.P w ∈ V a →
    Λ w = (Fintype.card (I a) : ℚ≥0)⁻¹ *
      ((Finset.univ.filter fun i => s a i (A.P w) = w).card : ℚ≥0)
  /-- (e) The correspondences `τ_{a,a'}` (their values off `V(a, a')` do not matter). -/
  τ : ∀ a a', A.Mor → IndexCorr (I a) (I a')
  locallyConstant : ∀ a a', ∀ φ ∈ A.X.morBetween (V a) (V a'), ∀ᶠ ψ in 𝓝 φ, τ a a' ψ = τ a a' φ
  finite : ∀ a a', (τ a a' '' A.X.morBetween (V a) (V a')).Finite
  biact : ∀ a a', ∀ φ ∈ A.X.morBetween (V a) (V a'), ∀ g' g,
    τ a a' (EpGroupoid.biact (N a) (N a') g' φ g) = IndexCorr.biact g' (τ a a' φ) g
  compat : ∀ a a', ∀ φ ∈ A.X.morBetween (V a) (V a'),
    (τ a a' φ).Sat fun i j => s a' j (A.X.tgt φ) = fibAct φ (s a i (A.X.src φ))
  diag : ∀ a (g : A.X.Isotropy (pt a)), ∀ y ∈ V a,
    τ a a ((N a).rep.Γ g y) = IndexCorr.ofPerm (α := I a) g
  swap : ∀ a a', ∀ φ ∈ A.X.morBetween (V a') (V a), τ a' a φ = (τ a a' (A.X.inv φ)).swap

attribute [instance] CriterionData.fintype CriterionData.mulAction

namespace CriterionData

variable {Λ : A.W → ℚ≥0} (D : CriterionData A Λ)

/-- **Transport into the `V_a`**: every object `y` has an index `a`, an open `O ∋ y` and an
sc-smooth `τ : O → 𝐗` with `t(τ(z)) = z` and `s(τ(z)) ∈ V_a` (from (c), `t` being a local
sc-diffeomorphism). -/
theorem exists_transport (y : A.Obj) :
    ∃ (a : D.ι) (O : Set A.Obj) (τ : A.Obj → A.Mor), IsOpen O ∧ y ∈ O ∧
      A.X.PObj.IsScSmoothOn A.X.PMor τ O ∧ ∀ z ∈ O, A.X.tgt (τ z) = z ∧ A.X.src (τ z) ∈ D.V a := by
  obtain ⟨a, v, hv, hπ⟩ := D.cover y
  obtain ⟨φ₀, hs₀, ht₀⟩ := (GroupoidStr.π_eq_π_iff _).1 hπ
  obtain ⟨T, V₂, τ, hT, hτ⟩ := A.X.isLocalScDiffeo_tgt φ₀
  have hcont : ContinuousOn (A.X.src ∘ τ) V₂ :=
    A.X.continuous_src.comp_continuousOn hτ.isScSmoothOn_inv.continuousOn
  have hO : IsOpen (V₂ ∩ (A.X.src ∘ τ) ⁻¹' D.V a) :=
    hcont.isOpen_inter_preimage hτ.isScSmoothOn_inv.isOpen (D.isOpen_V a)
  have hτy : τ y = φ₀ := by
    have := hτ.left_inv φ₀ hT
    rwa [ht₀] at this
  refine ⟨a, _, τ, hO, ⟨?_, ?_⟩, hτ.isScSmoothOn_inv.mono hO inter_subset_left,
    fun z hz => ⟨hτ.right_inv z hz.1, hz.2⟩⟩
  · have := hτ.mapsTo hT
    rwa [ht₀] at this
  · change A.X.src (τ y) ∈ D.V a
    rw [hτy, hs₀]; exact hv

/-- **The data of the proof**: for every `y` an index `a_y`, an open `O(y) ∋ y`, a sc-smooth
`τ_y : O(y) → 𝐗` into the morphisms from `V_{a_y}` with `t(τ_y(z)) = z`, and a good system
`𝒰₀`. -/
structure Transport (D : CriterionData A Λ) where
  /-- The index `a_y`. -/
  a : A.Obj → D.ι
  /-- `O(y)`. -/
  O : A.Obj → Set A.Obj
  /-- `τ_y`. -/
  τ : A.Obj → A.Obj → A.Mor
  isOpen_O : ∀ y, IsOpen (O y)
  mem_O : ∀ y, y ∈ O y
  isScSmoothOn_τ : ∀ y, A.X.PObj.IsScSmoothOn A.X.PMor (τ y) (O y)
  tgt_τ : ∀ y, ∀ z ∈ O y, A.X.tgt (τ y z) = z
  src_τ : ∀ y, ∀ z ∈ O y, A.X.src (τ y z) ∈ D.V (a y)
  /-- A good system. -/
  𝒰₀ : A.X.GoodSystem
  /-- `Λ` is an sc⁺-multisection functor. -/
  hΛ : IsScPlusMultisection A Λ

/-- The data of the proof exist once a good system exists. -/
theorem nonempty_transport (𝒰₀ : A.X.GoodSystem) (hΛ : IsScPlusMultisection A Λ) :
    Nonempty D.Transport := by
  choose a O τ hO hyO hτ h using D.exists_transport
  exact ⟨⟨a, O, τ, hO, hyO, hτ, fun y z hz => (h y z hz).1, fun y z hz => (h y z hz).2, 𝒰₀,
    hΛ⟩⟩

end CriterionData

namespace CriterionData.Transport

variable {Λ : A.W → ℚ≥0} {D : CriterionData A Λ} (P : D.Transport)

/-- `σ_y(z) = s(τ_y(z)) ∈ V_{a_y}`. -/
def σ (y z : A.Obj) : A.Obj := A.X.src (P.τ y z)

/-- The morphisms between `O(y)` and `O(y')`. -/
def Dom (y y' : A.Obj) : Set A.Mor := A.X.morBetween (P.O y) (P.O y')

/-- `τ_{y'}(t ψ)⁻¹ ∘ ψ ∘ τ_y(s ψ) : σ_y(s ψ) → σ_{y'}(t ψ)`. -/
def conj (y y' : A.Obj) (ψ : A.Mor) : A.Mor :=
  A.X.comp (A.X.inv (P.τ y' (A.X.tgt ψ))) (A.X.comp ψ (P.τ y (A.X.src ψ)))

variable {P}

theorem σ_mem {y z : A.Obj} (hz : z ∈ P.O y) : P.σ y z ∈ D.V (P.a y) := P.src_τ y z hz

theorem σ_mem_N {y z : A.Obj} (hz : z ∈ P.O y) : P.σ y z ∈ (D.N (P.a y)).U :=
  D.V_subset _ (σ_mem hz)

theorem isOpen_Dom (y y' : A.Obj) : IsOpen (P.Dom y y') :=
  A.X.isOpen_morBetween (P.isOpen_O y) (P.isOpen_O y')

theorem tgt_τ_src {y : A.Obj} {ψ : A.Mor} (hψ : A.X.src ψ ∈ P.O y) :
    A.X.src ψ = A.X.tgt (P.τ y (A.X.src ψ)) := (P.tgt_τ y _ hψ).symm

theorem src_conj {y y' : A.Obj} {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') :
    A.X.src (P.conj y y' ψ) = P.σ y (A.X.src ψ) := by
  have h1 := tgt_τ_src hψ.1
  unfold conj
  rw [A.X.src_comp _ _ (by rw [A.X.src_inv, P.tgt_τ y' _ hψ.2, A.X.tgt_comp _ _ h1]),
    A.X.src_comp _ _ h1]
  rfl

theorem tgt_conj {y y' : A.Obj} {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') :
    A.X.tgt (P.conj y y' ψ) = P.σ y' (A.X.tgt ψ) := by
  have h1 := tgt_τ_src hψ.1
  unfold conj
  rw [A.X.tgt_comp _ _ (by rw [A.X.src_inv, P.tgt_τ y' _ hψ.2, A.X.tgt_comp _ _ h1]),
    A.X.tgt_inv]
  rfl

theorem conj_mem {y y' : A.Obj} {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') :
    P.conj y y' ψ ∈ A.X.morBetween (D.V (P.a y)) (D.V (P.a y')) :=
  ⟨by rw [src_conj hψ]; exact σ_mem hψ.1, by rw [tgt_conj hψ]; exact σ_mem hψ.2⟩

/-- `τ_{y'}(t ψ) ∘ conj(ψ) = ψ ∘ τ_y(s ψ)`. -/
theorem conj_spec {y y' : A.Obj} {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') :
    A.X.comp (P.τ y' (A.X.tgt ψ)) (P.conj y y' ψ) = A.X.comp ψ (P.τ y (A.X.src ψ)) := by
  unfold conj
  refine AtomicStructData.comp_inv_comp ?_
  rw [A.X.tgt_comp _ _ (tgt_τ_src hψ.1), P.tgt_τ y' _ hψ.2]

/-- `conj(ψ)` is determined by `conj_spec`. -/
theorem eq_conj {y y' : A.Obj} {ψ χ : A.Mor} (hψ : ψ ∈ P.Dom y y')
    (ht : A.X.tgt χ = P.σ y' (A.X.tgt ψ))
    (e : A.X.comp (P.τ y' (A.X.tgt ψ)) χ = A.X.comp ψ (P.τ y (A.X.src ψ))) :
    χ = P.conj y y' ψ := by
  refine GroupoidStr.comp_left_cancel (G := A.X.toGroupoidStr) (φ := P.τ y' (A.X.tgt ψ))
    ht.symm ?_ (e.trans (conj_spec hψ).symm)
  rw [tgt_conj hψ]; rfl

/-- **Functoriality of `conj`**: `conj(ψ₁ ∘ ψ₂) = conj(ψ₁) ∘ conj(ψ₂)`. -/
theorem conj_comp {y y' y'' : A.Obj} {ψ₁ ψ₂ : A.Mor} (h₁ : ψ₁ ∈ P.Dom y' y'')
    (h₂ : ψ₂ ∈ P.Dom y y') (h : A.X.src ψ₁ = A.X.tgt ψ₂) :
    P.conj y y'' (A.X.comp ψ₁ ψ₂) = A.X.comp (P.conj y' y'' ψ₁) (P.conj y y' ψ₂) := by
  have hs : A.X.src (A.X.comp ψ₁ ψ₂) = A.X.src ψ₂ := A.X.src_comp _ _ h
  have ht : A.X.tgt (A.X.comp ψ₁ ψ₂) = A.X.tgt ψ₁ := A.X.tgt_comp _ _ h
  have hd : A.X.comp ψ₁ ψ₂ ∈ P.Dom y y'' := ⟨hs ▸ h₂.1, ht ▸ h₁.2⟩
  have c0 : A.X.src (P.conj y' y'' ψ₁) = A.X.tgt (P.conj y y' ψ₂) := by
    rw [src_conj h₁, tgt_conj h₂, h]
  symm
  refine eq_conj hd ?_ ?_
  · rw [A.X.tgt_comp _ _ c0, tgt_conj h₁, ht]
  · rw [hs, ht]
    have c1 : A.X.src (P.τ y'' (A.X.tgt ψ₁)) = A.X.tgt (P.conj y' y'' ψ₁) := by
      rw [tgt_conj h₁]; rfl
    have c2 : A.X.src ψ₁ = A.X.tgt (P.τ y' (A.X.src ψ₁)) := tgt_τ_src h₁.1
    have c3 : A.X.src (P.τ y' (A.X.src ψ₁)) = A.X.tgt (P.conj y y' ψ₂) := by
      rw [tgt_conj h₂, h]; rfl
    have c4 : A.X.src ψ₂ = A.X.tgt (P.τ y (A.X.src ψ₂)) := tgt_τ_src h₂.1
    have e2 : A.X.comp (P.τ y' (A.X.src ψ₁)) (P.conj y y' ψ₂) =
        A.X.comp ψ₂ (P.τ y (A.X.src ψ₂)) := by
      rw [h]; exact conj_spec h₂
    rw [← A.X.comp_assoc _ _ _ c1 c0, conj_spec h₁, A.X.comp_assoc _ _ _ c2 c3, e2,
      ← A.X.comp_assoc _ _ _ h c4]

theorem conj_unit {y z : A.Obj} (hz : z ∈ P.O y) :
    P.conj y y (A.X.unit z) = A.X.unit (P.σ y z) := by
  unfold conj
  rw [A.X.src_unit, A.X.tgt_unit,
    GroupoidStr.unit_comp_of_eq (G := A.X.toGroupoidStr) (P.tgt_τ y z hz), A.X.inv_comp]
  rfl

theorem unit_mem_Dom {y z : A.Obj} (hz : z ∈ P.O y) : A.X.unit z ∈ P.Dom y y :=
  ⟨by rw [A.X.src_unit]; exact hz, by rw [A.X.tgt_unit]; exact hz⟩

theorem inv_mem_Dom {y y' : A.Obj} {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') :
    A.X.inv ψ ∈ P.Dom y' y :=
  ⟨by rw [A.X.src_inv]; exact hψ.2, by rw [A.X.tgt_inv]; exact hψ.1⟩

theorem conj_inv {y y' : A.Obj} {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') :
    P.conj y' y (A.X.inv ψ) = A.X.inv (P.conj y y' ψ) := by
  have := conj_comp (inv_mem_Dom hψ) hψ (A.X.src_inv ψ)
  rw [A.X.inv_comp, conj_unit hψ.1] at this
  refine GroupoidStr.eq_inv_of_comp_eq_unit (G := A.X.toGroupoidStr) ?_ ?_
  · rw [src_conj (inv_mem_Dom hψ), tgt_conj hψ, A.X.src_inv]
  · rw [← this, src_conj hψ]

theorem continuousOn_conj (y y' : A.Obj) : ContinuousOn (P.conj y y') (P.Dom y y') := by
  have hτ' : ContinuousOn (fun ψ => P.τ y' (A.X.tgt ψ)) (P.Dom y y') :=
    (P.isScSmoothOn_τ y').continuousOn.comp A.X.continuous_tgt.continuousOn fun _ h => h.2
  have hτ : ContinuousOn (fun ψ => P.τ y (A.X.src ψ)) (P.Dom y y') :=
    (P.isScSmoothOn_τ y).continuousOn.comp A.X.continuous_src.continuousOn fun _ h => h.1
  have hin : ContinuousOn (fun ψ => A.X.comp ψ (P.τ y (A.X.src ψ))) (P.Dom y y') :=
    continuousOn_comp_of_continuousOn continuousOn_id hτ fun ψ h => tgt_τ_src h.1
  exact continuousOn_comp_of_continuousOn (A.X.continuous_inv.comp_continuousOn hτ') hin
    fun ψ h => by rw [A.X.src_inv, P.tgt_τ y' _ h.2, A.X.tgt_comp _ _ (tgt_τ_src h.1)]

/-! ### The elements `H(ψ) ∈ G_{a_y}` -/

theorem existsUnique_rel {y : A.Obj} {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y) :
    ∃! h, (D.N (P.a y)).rep.Γ h (P.σ y (A.X.src ψ)) = P.conj y y ψ := by
  have := (D.N (P.a y)).rep.existsUnique_Γ (P.conj y y ψ)
    (by rw [src_conj hψ]; exact (D.N _).U_subset (σ_mem_N hψ.1))
    (by rw [tgt_conj hψ]; exact (D.N _).U_subset (σ_mem_N hψ.2))
  rwa [src_conj hψ] at this

variable (P) in
/-- **`H(ψ) ∈ G_{a_y}`** with `Γ(H(ψ), σ_y(s ψ)) = conj(ψ)` for `ψ` between points of `O(y)`
(`1` otherwise). -/
def H (y : A.Obj) (ψ : A.Mor) : A.X.Isotropy (D.pt (P.a y)) :=
  if h : ψ ∈ P.Dom y y then (existsUnique_rel h).exists.choose else 1

theorem H_spec {y : A.Obj} {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y) :
    (D.N (P.a y)).rep.Γ (P.H y ψ) (P.σ y (A.X.src ψ)) = P.conj y y ψ := by
  unfold H
  rw [dif_pos hψ]
  exact (existsUnique_rel hψ).exists.choose_spec

theorem H_eq_of_rel {y : A.Obj} {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y) {h}
    (e : (D.N (P.a y)).rep.Γ h (P.σ y (A.X.src ψ)) = P.conj y y ψ) : P.H y ψ = h :=
  (existsUnique_rel hψ).unique (H_spec hψ) e

theorem H_tgt {y : A.Obj} {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y) :
    (D.N (P.a y)).rep.Φ (P.H y ψ) (P.σ y (A.X.src ψ)) = P.σ y (A.X.tgt ψ) := by
  rw [← (D.N _).tgt_Γ _ (σ_mem_N hψ.1), H_spec hψ, tgt_conj hψ]

/-- **Functoriality**: `H(ψ₁ ∘ ψ₂) = H(ψ₁) H(ψ₂)`. -/
theorem H_comp {y : A.Obj} {ψ₁ ψ₂ : A.Mor} (h₁ : ψ₁ ∈ P.Dom y y) (h₂ : ψ₂ ∈ P.Dom y y)
    (h : A.X.src ψ₁ = A.X.tgt ψ₂) :
    P.H y (A.X.comp ψ₁ ψ₂) = P.H y ψ₁ * P.H y ψ₂ := by
  have hs : A.X.src (A.X.comp ψ₁ ψ₂) = A.X.src ψ₂ := A.X.src_comp _ _ h
  have hd : A.X.comp ψ₁ ψ₂ ∈ P.Dom y y := ⟨hs ▸ h₂.1, (A.X.tgt_comp _ _ h) ▸ h₁.2⟩
  refine H_eq_of_rel hd ?_
  rw [hs, ← (D.N _).Γ_mul _ _ (σ_mem_N h₂.1), H_tgt h₂, ← h, H_spec h₁, H_spec h₂,
    conj_comp h₁ h₂ h]

theorem H_unit {y z : A.Obj} (hz : z ∈ P.O y) : P.H y (A.X.unit z) = 1 := by
  refine H_eq_of_rel (unit_mem_Dom hz) ?_
  rw [A.X.src_unit, (D.N _).Γ_one (σ_mem_N hz), conj_unit hz]

theorem H_eventually {y : A.Obj} {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y) :
    ∀ᶠ ψ' in 𝓝 ψ, P.H y ψ' = P.H y ψ := by
  have hσ : ContinuousOn (fun ψ => P.σ y (A.X.src ψ)) (P.Dom y y) :=
    A.X.continuous_src.comp_continuousOn
      ((P.isScSmoothOn_τ y).continuousOn.comp A.X.continuous_src.continuousOn fun _ h => h.1)
  have hev := eventually_eq_of_existsUnique (isOpen_Dom y y) (continuousOn_conj y y)
    (gs := fun h ψ => (D.N (P.a y)).rep.Γ h (P.σ y (A.X.src ψ)))
    (fun h => ((D.N _).rep.isScSmoothOn_Γ h).continuousOn.comp hσ
      fun _ h' => (D.N _).U_subset (σ_mem_N h'.1))
    (fun _ h => existsUnique_rel h) hψ (H_spec hψ)
  exact hev.mono fun _ h => H_eq_of_rel h.1 h.2

/-! ### The homomorphisms `γ_y : G_y → G_{a_y}` -/

theorem Γ₀_mem_Dom (y : A.Obj) (g : A.X.Isotropy y) : (P.𝒰₀.nbhd y).rep.Γ g y ∈ P.Dom y y := by
  have hU := (P.𝒰₀.nbhd y).rep.mem_U
  refine ⟨?_, ?_⟩
  · rw [(P.𝒰₀.nbhd y).rep.src_Γ g y hU]; exact P.mem_O y
  · rw [(P.𝒰₀.nbhd y).rep.tgt_Γ g y hU, (P.𝒰₀.nbhd y).rep.Φ_self]; exact P.mem_O y

variable (P) in
/-- **`γ_y(g) = H(Γ(g, y))`**, a homomorphism `G_y → G_{a_y}`. -/
def γ (y : A.Obj) : A.X.Isotropy y →* A.X.Isotropy (D.pt (P.a y)) where
  toFun g := P.H y ((P.𝒰₀.nbhd y).rep.Γ g y)
  map_one' := by
    rw [(P.𝒰₀.nbhd y).Γ_one (P.𝒰₀.nbhd y).mem_U]
    exact H_unit (P.mem_O y)
  map_mul' g h := by
    have hU := (P.𝒰₀.nbhd y).rep.mem_U
    rw [← (P.𝒰₀.nbhd y).Γ_mul g h (P.𝒰₀.nbhd y).mem_U, (P.𝒰₀.nbhd y).rep.Φ_self h]
    exact H_comp (Γ₀_mem_Dom y g) (Γ₀_mem_Dom y h)
      (by rw [(P.𝒰₀.nbhd y).rep.src_Γ g y hU, (P.𝒰₀.nbhd y).rep.tgt_Γ h y hU,
        (P.𝒰₀.nbhd y).rep.Φ_self])

theorem γ_apply (y : A.Obj) (g : A.X.Isotropy y) :
    P.γ y g = P.H y ((P.𝒰₀.nbhd y).rep.Γ g y) := rfl

/-! ### The good system -/

variable (P) in
/-- Where the pulled back structure at `y` is equivariant through `γ_y`. -/
def Wn (y : A.Obj) : Set A.Obj :=
  {z | z ∈ (P.𝒰₀.nbhd y).U ∧ z ∈ P.O y ∧ ∀ g, (P.𝒰₀.nbhd y).rep.Φ g z ∈ P.O y ∧
    P.H y ((P.𝒰₀.nbhd y).rep.Γ g z) = P.γ y g}

theorem eventually_Wn (y : A.Obj) : ∀ᶠ z in 𝓝 y, z ∈ P.Wn y := by
  set N := P.𝒰₀.nbhd y
  have hUn : N.rep.U ∈ 𝓝 y := N.rep.isOpen_U.mem_nhds N.rep.mem_U
  have hg : ∀ g, ∀ᶠ z in 𝓝 y, N.rep.Φ g z ∈ P.O y ∧ P.H y (N.rep.Γ g z) = P.γ y g := by
    intro g
    have h1 : ∀ᶠ z in 𝓝 y, N.rep.Φ g z ∈ P.O y := by
      have hc := ((N.rep.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn).continuousAt hUn
      have : N.rep.Φ g y ∈ P.O y := by rw [N.rep.Φ_self]; exact P.mem_O y
      exact hc.preimage_mem_nhds ((P.isOpen_O y).mem_nhds this)
    have h2 : ∀ᶠ z in 𝓝 y, P.H y (N.rep.Γ g z) = P.γ y g := by
      have hc := ((N.rep.isScSmoothOn_Γ g).continuousOn).continuousAt hUn
      exact hc.eventually (H_eventually (Γ₀_mem_Dom y g))
    exact h1.and h2
  filter_upwards [N.isOpen_U.mem_nhds N.mem_U, (P.isOpen_O y).mem_nhds (P.mem_O y),
    eventually_all.2 hg] with z h1 h2 h3 using ⟨h1, h2, h3⟩

variable (P) in
/-- The neighbourhoods `U(y) ⊆ U₀(y) ∩ int Wn(y)` with the natural actions of `𝒰₀`. -/
def M (y : A.Obj) : A.X.NatNbhd y :=
  (P.𝒰₀.nbhd y).restrict ((P.𝒰₀.nbhd y).invariantCore (interior (P.Wn y)))
    ((P.𝒰₀.nbhd y).isOpen_invariantCore isOpen_interior)
    ((P.𝒰₀.nbhd y).mem_invariantCore (mem_interior_iff_mem_nhds.2 (eventually_Wn (P := P) y)))
    (fun _ hz => ((P.𝒰₀.nbhd y).invariantCore_subset _ hz).1)
    ((P.𝒰₀.nbhd y).mapsTo_Φ_invariantCore _)

variable (P) in
/-- **The good system of the proof.** -/
def 𝒰 : A.X.GoodSystem :=
  P.𝒰₀.ofSubset P.M fun y _ hz => ((P.𝒰₀.nbhd y).invariantCore_subset _ hz).1

theorem mem_Wn {y z : A.Obj} (hz : z ∈ P.𝒰.U y) : z ∈ P.Wn y :=
  interior_subset ((P.𝒰₀.nbhd y).invariantCore_subset _ hz).2

theorem U_subset_O (y : A.Obj) : P.𝒰.U y ⊆ P.O y := fun _ hz => (mem_Wn hz).2.1

theorem W_cond {y z : A.Obj} (hz : z ∈ P.𝒰.U y) (g : A.X.Isotropy y) :
    P.H y ((P.𝒰.nbhd y).rep.Γ g z) = P.γ y g :=
  ((mem_Wn hz).2.2 g).2

theorem mor_subset_Dom (y y' : A.Obj) : P.𝒰.mor y y' ⊆ P.Dom y y' :=
  fun _ h => ⟨U_subset_O y h.1, U_subset_O y' h.2⟩

theorem Γ_mem_Dom {y z : A.Obj} (hz : z ∈ P.𝒰.U y) (g : A.X.Isotropy y) :
    (P.𝒰.nbhd y).rep.Γ g z ∈ P.Dom y y :=
  ⟨by rw [(P.𝒰.nbhd y).src_Γ g hz]; exact U_subset_O y hz,
    by rw [(P.𝒰.nbhd y).tgt_Γ g hz]; exact U_subset_O y ((P.𝒰.nbhd y).Φ_mem g hz)⟩

/-- `conj(Γ(g, z)) = Γ_{a_y}(γ_y(g), σ_y(z))` on `U(y)`. -/
theorem conj_Γ {y z : A.Obj} (hz : z ∈ P.𝒰.U y) (g : A.X.Isotropy y) :
    P.conj y y ((P.𝒰.nbhd y).rep.Γ g z) = (D.N (P.a y)).rep.Γ (P.γ y g) (P.σ y z) := by
  rw [← H_spec (Γ_mem_Dom hz g), W_cond hz g, (P.𝒰.nbhd y).src_Γ g hz]

/-- `σ_y(g ∗ z) = γ_y(g) ∗ σ_y(z)` on `U(y)`. -/
theorem σ_Φ {y z : A.Obj} (hz : z ∈ P.𝒰.U y) (g : A.X.Isotropy y) :
    P.σ y ((P.𝒰.nbhd y).rep.Φ g z) = (D.N (P.a y)).rep.Φ (P.γ y g) (P.σ y z) := by
  have := H_tgt (Γ_mem_Dom hz g)
  rw [W_cond hz g, (P.𝒰.nbhd y).src_Γ g hz, (P.𝒰.nbhd y).tgt_Γ g hz] at this
  exact this.symm

/-! ### The symmetric structures -/

variable (P) in
/-- The sections at `y`: the sections of `V_{a_y}` pulled back by `τ_y`. -/
def sec (y : A.Obj) (i : D.I (P.a y)) : A.Obj → A.W :=
  transportSection (P.τ y) (fun z => D.s (P.a y) i (P.σ y z))

theorem P_s_σ {y z : A.Obj} (hz : z ∈ P.O y) (i : D.I (P.a y)) :
    A.P (D.s (P.a y) i (P.σ y z)) = P.σ y z :=
  (D.isScPlusSectionOn _ i).1 _ (σ_mem hz)

theorem sec_apply {y z : A.Obj} (hz : z ∈ P.O y) (i : D.I (P.a y)) :
    P.sec y i z = fibAct (P.τ y z) (D.s (P.a y) i (P.σ y z)) :=
  AtomicStructData.transportSection_eq_fibAct (P_s_σ hz i)

/-- **Relating the pulled back sections**: if `sᵃ'_j(t χ) = μ(χ, sᵃᵢ(s χ))` for
`χ = conj(ψ)`, then `s^{y'}_j(t ψ) = μ(ψ, s^yᵢ(s ψ))`. -/
theorem sec_rel {y y' : A.Obj} {ψ : A.Mor} (hψ : ψ ∈ P.Dom y y') (i : D.I (P.a y))
    (j : D.I (P.a y'))
    (h : D.s (P.a y') j (A.X.tgt (P.conj y y' ψ)) =
      fibAct (P.conj y y' ψ) (D.s (P.a y) i (A.X.src (P.conj y y' ψ)))) :
    P.sec y' j (A.X.tgt ψ) = fibAct ψ (P.sec y i (A.X.src ψ)) := by
  rw [src_conj hψ, tgt_conj hψ] at h
  have hsi := P_s_σ hψ.1 i
  have hsi' : A.P (D.s (P.a y) i (P.σ y (A.X.src ψ))) = A.X.src (P.conj y y' ψ) := by
    rw [hsi, src_conj hψ]
  have c : A.X.src (P.τ y' (A.X.tgt ψ)) = A.X.tgt (P.conj y y' ψ) := by
    rw [tgt_conj hψ]; rfl
  rw [sec_apply hψ.2, sec_apply hψ.1, h, ← AtomicStructData.fibAct_comp hsi' c, conj_spec hψ,
    AtomicStructData.fibAct_comp hsi (tgt_τ_src hψ.1)]

variable (P) in
/-- **The symmetric structure at `y`**: index set `I_{a_y}`, `G_y` acting through `γ_y`. -/
@[reducible] def S (y : A.Obj) : SymmetricStructureOn A Λ (P.𝒰.nbhd y) where
  I := D.I (P.a y)
  mulAction := MulAction.compHom (D.I (P.a y)) (P.γ y)
  s := P.sec y
  isScPlusSectionOn i := by
    obtain ⟨-, G, hG, hGs⟩ := D.isScPlusSectionOn (P.a y) i
    have hsτ : A.X.PObj.IsScSmoothOn A.X.PObj (A.X.src ∘ P.τ y) (P.O y) :=
      MPolyfold.IsScSmoothOn.comp A.X.isScSmoothMap_src (P.isScSmoothOn_τ y) (mapsTo_univ _ _)
    exact (isScPlusSectionOn_transportSection (P.isScSmoothOn_τ y)
      (G := G ∘ (A.X.src ∘ P.τ y)) (fun z hz => hG _ (σ_mem hz))
      (MPolyfold.IsScSmoothOn.comp hGs hsτ fun z hz => σ_mem hz)
      (fun z hz => P_s_σ hz i) (P.tgt_τ y)).mono (P.𝒰.isOpen_U y) (U_subset_O y)
  equivariant g i z hz := by
    have hd := Γ_mem_Dom hz g
    have := sec_rel hd i (P.γ y g • i) (by
      rw [conj_Γ hz g, (D.N _).src_Γ _ (σ_mem_N (U_subset_O y hz)),
        (D.N _).tgt_Γ _ (σ_mem_N (U_subset_O y hz))]
      exact D.equivariant _ _ i _ (σ_mem (U_subset_O y hz)))
    rw [(P.𝒰.nbhd y).tgt_Γ g hz, (P.𝒰.nbhd y).src_Γ g hz] at this
    exact this
  rep w hw := by
    have hz : A.P w ∈ P.O y := U_subset_O y hw
    have hs : A.P w = A.X.src (A.X.inv (P.τ y (A.P w))) := by
      rw [A.X.src_inv, P.tgt_τ y _ hz]
    have hPv : A.P (A.E.μ ⟨(A.X.inv (P.τ y (A.P w)), w), hs⟩) = P.σ y (A.P w) := by
      rw [A.E.P_μ]; exact A.X.tgt_inv _
    have hfun : Λ (A.E.μ ⟨(A.X.inv (P.τ y (A.P w)), w), hs⟩) = Λ w :=
      P.hΛ.1 ⟨(A.X.inv (P.τ y (A.P w)), w), hs⟩
    rw [← hfun, D.rep (P.a y) _ (by rw [hPv]; exact σ_mem hz), hPv, ← fibAct_of hs]
    congr 3
    refine Finset.filter_congr fun i _ => ?_
    rw [sec_apply hz]
    have hw' : A.P w = A.X.tgt (P.τ y (A.P w)) := (P.tgt_τ y _ hz).symm
    constructor
    · intro e; rw [e]; exact AtomicStructData.fibAct_fibAct_inv hw'
    · intro e
      exact (AtomicStructData.fibAct_inv_fibAct (P_s_σ hz i)).symm.trans (congrArg _ e)

variable (P) in
/-- The decoration `(𝒰, S)`. -/
abbrev dec : Decoration A Λ := ⟨P.𝒰, P.S⟩

/-! ### The correspondences -/

variable (P) in
/-- **The correspondences** `τ̄_{y,y'}(φ) = τ_{a_y,a_{y'}}(conj(φ))`. -/
def corr (y y' : A.Obj) (φ : A.Mor) : IndexCorr (D.I (P.a y)) (D.I (P.a y')) :=
  D.τ (P.a y) (P.a y') (P.conj y y' φ)

theorem corr_eventually {y y' : A.Obj} {φ : A.Mor} (hφ : φ ∈ P.Dom y y') :
    ∀ᶠ ψ in 𝓝 φ, P.corr y y' ψ = P.corr y y' φ := by
  have hc := (continuousOn_conj y y').continuousAt ((isOpen_Dom y y').mem_nhds hφ)
  exact hc.eventually (D.locallyConstant _ _ _ (conj_mem hφ))

/-- `conj` of the bi-action is the bi-action of `conj`. -/
theorem conj_biact {y y' : A.Obj} {φ : A.Mor} (hφ : φ ∈ P.𝒰.mor y y') (g' : A.X.Isotropy y')
    (g : A.X.Isotropy y) :
    P.conj y y' (P.𝒰.biact y y' g' φ g) =
      EpGroupoid.biact (D.N (P.a y)) (D.N (P.a y')) (P.γ y' g') (P.conj y y' φ) (P.γ y g) := by
  set N := P.𝒰.nbhd y
  set N' := P.𝒰.nbhd y'
  have hz : N.rep.Φ g⁻¹ (A.X.src φ) ∈ N.U := N.Φ_mem g⁻¹ hφ.1
  have hA : N'.rep.Γ g' (A.X.tgt φ) ∈ P.Dom y' y' := Γ_mem_Dom hφ.2 g'
  have hB : N.rep.Γ g (N.rep.Φ g⁻¹ (A.X.src φ)) ∈ P.Dom y y := Γ_mem_Dom hz g
  have hφd := mor_subset_Dom y y' hφ
  have hBc : A.X.src φ = A.X.tgt (N.rep.Γ g (N.rep.Φ g⁻¹ (A.X.src φ))) := by
    rw [N.tgt_Γ g hz, N.Φ_Φ_inv g hφ.1]
  have hφB : A.X.comp φ (N.rep.Γ g (N.rep.Φ g⁻¹ (A.X.src φ))) ∈ P.Dom y y' :=
    ⟨by rw [A.X.src_comp _ _ hBc]; exact hB.1, by rw [A.X.tgt_comp _ _ hBc]; exact hφd.2⟩
  have hσ : P.σ y (N.rep.Φ g⁻¹ (A.X.src φ)) =
      (D.N (P.a y)).rep.Φ (P.γ y g)⁻¹ (P.σ y (A.X.src φ)) := by
    rw [σ_Φ hφ.1 g⁻¹, map_inv]
  show P.conj y y' (A.X.comp (N'.rep.Γ g' (A.X.tgt φ))
    (A.X.comp φ (N.rep.Γ g (N.rep.Φ g⁻¹ (A.X.src φ))))) = _
  rw [conj_comp hA hφB (by rw [N'.src_Γ g' hφ.2, A.X.tgt_comp _ _ hBc]),
    conj_comp hφd hB hBc, conj_Γ hφ.2 g', conj_Γ hz g, EpGroupoid.biact, tgt_conj hφd,
    src_conj hφd, hσ]

/-- **Definition 13.3.4 for `corr`.** -/
theorem isCorrespondence (y y' : A.Obj) : P.dec.IsCorrespondence y y' (P.corr y y') where
  locallyConstant φ hφ := corr_eventually (mor_subset_Dom y y' hφ)
  finite := (D.finite (P.a y) (P.a y')).subset (by
    rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨_, conj_mem (mor_subset_Dom y y' hφ), rfl⟩)
  biact φ hφ g' g := by
    show D.τ _ _ (P.conj y y' (P.𝒰.biact y y' g' φ g)) = _
    rw [conj_biact hφ, D.biact _ _ _ (conj_mem (mor_subset_Dom y y' hφ))]
    exact (IndexCorr.biact_compHom_gl (P.γ y) (P.γ y') _ g' g).symm
  compat φ hφ := by
    refine IndexCorr.sat_forall fun ψ hψ => ?_
    have hψm : ψ ∈ P.𝒰.mor y y' := connectedComponentIn_subset _ _ hψ
    have e : P.corr y y' ψ = P.corr y y' φ :=
      eq_of_mem_connectedComponentIn (P.𝒰.isOpen_mor y y')
        (fun _ h' => corr_eventually (mor_subset_Dom y y' h')) hφ hψ
    change (P.corr y y' φ).Sat _
    rw [← e]
    exact IndexCorr.sat_mono (fun i j H => sec_rel (mor_subset_Dom y y' hψm) i j H)
      (D.compat _ _ _ (conj_mem (mor_subset_Dom y y' hψm)))

variable (P) in
/-- **The correspondences `τ̄` of Definition 13.3.6.** -/
def tau : P.dec.Tau where
  τ := P.corr
  isCorrespondence := P.isCorrespondence
  diag y g z hz := by
    show D.τ _ _ (P.conj y y ((P.𝒰.nbhd y).rep.Γ g z)) = _
    rw [conj_Γ hz g, D.diag _ _ _ (σ_mem (U_subset_O y hz))]
    exact (IndexCorr.ofPerm_compHom_gl (P.γ y) g).symm
  swap y y' φ hφ := by
    show D.τ _ _ (P.conj y' y φ) = (D.τ _ _ (P.conj y y' (A.X.inv φ))).swap
    have hd : A.X.inv φ ∈ P.Dom y y' := inv_mem_Dom (mor_subset_Dom y' y hφ)
    have e : P.conj y' y φ = A.X.inv (P.conj y y' (A.X.inv φ)) := by
      rw [← conj_inv hd, GroupoidStr.inv_inv]
    have hm : A.X.inv (P.conj y y' (A.X.inv φ)) ∈
        A.X.morBetween (D.V (P.a y')) (D.V (P.a y)) := by
      rw [← e]; exact conj_mem (mor_subset_Dom y' y hφ)
    rw [e, D.swap _ _ _ hm, GroupoidStr.inv_inv]

end CriterionData.Transport

/-- **The proof of Theorem 14.5.5**: the data of the proof give a structure. -/
theorem CriterionData.Transport.isStructurable {Λ : A.W → ℚ≥0} {D : CriterionData A Λ}
    (P : D.Transport) : IsStructurable A Λ :=
  ⟨P.hΛ, P.dec, ⟨P.tau⟩⟩

/-- **2021 Theorem 14.5.5, p. 678 (2017: Theorem 14.3), given a good system**: an
sc⁺-multisection functor with the data (a)–(e) (`CriterionData`) is structurable. -/
theorem theorem_14_5_5_of_goodSystem (h𝒰 : Nonempty A.X.GoodSystem) {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) (D : CriterionData A Λ) : IsStructurable A Λ :=
  (D.nonempty_transport h𝒰.some hΛ).some.isStructurable

/-- **2021 Theorem 14.5.5, p. 678 (2017: Theorem 14.3)**: over an ep-groupoid with paracompact
orbit space, an sc⁺-multisection functor `Λ` with the data (a)–(e) of the theorem
(`CriterionData`: invariant open `V_a ⊆ U(a)` with `⋃ |V_a| = |X|`, symmetric sc⁺-section
structures on the `V_a` representing `Λ`, and correspondences `τ_{a,a'}` relating them) is
structurable. -/
theorem theorem_14_5_5 (hX : A.X.HasParacompactOrbitSpace) {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) (D : CriterionData A Λ) : IsStructurable A Λ :=
  theorem_14_5_5_of_goodSystem
    ⟨(A.X.theorem_13_1_8 hX (fun _ => univ) (fun _ => isOpen_univ) fun _ => mem_univ _).choose⟩
    hΛ D

end SBLocalization

end Polyfold
