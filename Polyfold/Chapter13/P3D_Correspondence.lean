import Polyfold.Chapter13.P3D_SymmetricOn

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.3, pp. 613–614: the diagrams (13.5), **Definition 13.3.1** (correspondences `J(x, x')`),
**Definition 13.3.2** (pseudo-inverse and bi-action), **Example 13.3.3**, and the
representative-independence of **Remark 13.3.5** (2017: §13.3, Definitions 13.14, 13.15,
Example 13.1, Remark 13.1).

# Correspondences between index sets

## The text, paraphrased

(13.5) A diagram `d : I_x ←a I →b I_{x'}` with `a`, `b` surjective and all fibres of `a` (and all
fibres of `b`) of the same size.  (Definition 13.3.1) Two diagrams are equivalent if a bijection
`c : I → I'` makes both triangles commute; a class `[d]` is a correspondence, and `J(x, x')` is the
set of correspondences.  (Definition 13.3.2) The pseudo-inverse `[I_x ← I → I_{x'}]♯ =
[I_{x'} ← I → I_x]` is a bijection `J(x, x') → J(x', x)`; the bi-action is
`g' ∗ [a, b] ∗ g = [g⁻¹ ∘ a, g' ∘ b]`.  (Example 13.3.3) For `I_x = {∗}`, `g' ∗ [d] ∗ g = [d]`.
(Remark 13.3.5) Property (3) of Definition 13.3.4 does not depend on the representative.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `IndexDiagram α β` (13.5), with the fibre conditions stated with `Nat.card`.
* **Definition 13.3.1**: `IndexDiagram.Equiv`, `IndexDiagram.setoid`, `IndexCorr α β` (the set
  `J(x, x')` for `α = I_x`, `β = I_{x'}`).
* **Definition 13.3.2**: `IndexCorr.swap` (`♯`), `IndexCorr.swapEquiv` (a bijection),
  `IndexCorr.biact` with `biact_one_one`, `biact_biact` (an action of `G_{x'} × G_xᵐᵒᵖ`).
* **Example 13.3.3**: `example_13_3_3`.
* **Remark 13.3.5** in general form: for a relation `R : α → β → Prop`, `IndexDiagram.Sat R d`
  (`R (a k) (b k)` for all `k`) is invariant under equivalence (`sat_iff_of_equiv`), so
  `IndexCorr.Sat R` is defined on correspondences (`IndexCorr.sat_iff`).
* Constructions used in §13.3: `IndexCorr.map` (relabel along bijections), `ofEquiv`, `ofPerm`
  (`[I_x ←id I_x →g I_x]`), `toUnit`/`fromUnit` (`[{∗} ← I →id I]`), and products `prod`, with
  the laws `prod_swap`, `prod_biact`, `prod_ofPerm`, `sat_prod`.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

/-! ### Diagrams (13.5) -/

/-- **The diagrams (13.5), p. 613**: `I_x ←a I →b I_{x'}` with `I` finite, `a` and `b`
surjective, and all fibres of `a` (respectively `b`) of the same cardinality. -/
structure IndexDiagram (α β : Type u) where
  /-- The middle set `I`. -/
  I : Type u
  [fintype : Fintype I]
  /-- `a : I → I_x`. -/
  a : I → α
  /-- `b : I → I_{x'}`. -/
  b : I → β
  surjective_a : Surjective a
  surjective_b : Surjective b
  uniform_a : ∀ i i', Nat.card {k // a k = i} = Nat.card {k // a k = i'}
  uniform_b : ∀ j j', Nat.card {k // b k = j} = Nat.card {k // b k = j'}

attribute [instance] IndexDiagram.fintype

namespace IndexDiagram

variable {α β α' β' : Type u}

/-- **2021 Definition 13.3.1, p. 613 (2017: Definition 13.14)**:
`d ~ d'` if there is a bijection `c : I → I'` with
`a' ∘ c = a` and `b' ∘ c = b`. -/
def Equiv (d d' : IndexDiagram α β) : Prop :=
  ∃ c : d.I ≃ d'.I, ∀ k, d'.a (c k) = d.a k ∧ d'.b (c k) = d.b k

theorem equivalence : _root_.Equivalence (Equiv (α := α) (β := β)) where
  refl d := ⟨_root_.Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩
  symm := by
    rintro d d' ⟨c, hc⟩
    refine ⟨c.symm, fun k => ?_⟩
    have := hc (c.symm k)
    rw [_root_.Equiv.apply_symm_apply] at this
    exact ⟨this.1.symm, this.2.symm⟩
  trans := by
    rintro d d' d'' ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨c.trans c', fun k => ⟨(hc' (c k)).1.trans (hc k).1, (hc' (c k)).2.trans (hc k).2⟩⟩

instance setoid (α β : Type u) : Setoid (IndexDiagram α β) := ⟨Equiv, equivalence⟩

/-! #### Fibre counts -/

theorem card_fiber_comp_equiv {I : Type u} (f : I → α) (e : α ≃ α') (i : α') :
    Nat.card {k // e (f k) = i} = Nat.card {k // f k = e.symm i} :=
  Nat.card_congr (_root_.Equiv.subtypeEquivRight fun _ => e.eq_symm_apply.symm)

theorem card_fiber_of_bijective {I : Type u} {f : I → α} (hf : Bijective f) (i : α) :
    Nat.card {k // f k = i} = 1 := by
  obtain ⟨k₀, hk₀⟩ := hf.2 i
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun p q => Subtype.ext (hf.1 (p.2.trans q.2.symm))⟩, ⟨⟨k₀, hk₀⟩⟩⟩

/-! #### Relabelling, pseudo-inverse, bi-action -/

/-- Relabel the ends along bijections: `[e ∘ a, e' ∘ b]`. -/
def map (e : α ≃ α') (e' : β ≃ β') (d : IndexDiagram α β) : IndexDiagram α' β' where
  I := d.I
  a := e ∘ d.a
  b := e' ∘ d.b
  surjective_a := e.surjective.comp d.surjective_a
  surjective_b := e'.surjective.comp d.surjective_b
  uniform_a i i' := by
    simp only [comp_apply, card_fiber_comp_equiv]; exact d.uniform_a _ _
  uniform_b j j' := by
    simp only [comp_apply, card_fiber_comp_equiv]; exact d.uniform_b _ _

/-- **Definition 13.3.2**: the reversed diagram `I_{x'} ←b I →a I_x`. -/
def swap (d : IndexDiagram α β) : IndexDiagram β α :=
  ⟨d.I, d.b, d.a, d.surjective_b, d.surjective_a, d.uniform_b, d.uniform_a⟩

/-- The diagram `I_x ←id I_x →e I_{x'}` of a bijection. -/
def ofEquiv [Fintype α] (e : α ≃ β) : IndexDiagram α β where
  I := α
  a := id
  b := e
  surjective_a := surjective_id
  surjective_b := e.surjective
  uniform_a i i' := by
    rw [card_fiber_of_bijective bijective_id, card_fiber_of_bijective bijective_id]
  uniform_b j j' := by
    rw [card_fiber_of_bijective e.bijective, card_fiber_of_bijective e.bijective]

/-- The diagram `{∗} ← I →id I` (for `I ≠ ∅`). -/
def toUnit (β : Type u) [Fintype β] [Nonempty β] : IndexDiagram PUnit.{u + 1} β where
  I := β
  a _ := PUnit.unit
  b := id
  surjective_a _ := ⟨Classical.arbitrary β, rfl⟩
  surjective_b := surjective_id
  uniform_a i i' := by rw [Subsingleton.elim i i']
  uniform_b j j' := by
    rw [card_fiber_of_bijective bijective_id, card_fiber_of_bijective bijective_id]

theorem card_fiber_prodMap {α₂ : Type u} {I J : Type u} (f : I → α) (g : J → α₂) (p : α × α₂) :
    Nat.card {k // Prod.map f g k = p} = Nat.card {k // f k = p.1} * Nat.card {k // g k = p.2} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr ((_root_.Equiv.subtypeEquivRight fun _ => Prod.ext_iff).trans
    (_root_.Equiv.subtypeProdEquivProd (p := fun a => f a = p.1) (q := fun b => g b = p.2)))

/-- The product of two diagrams, `I¹_x × I²_x ← I¹ × I² → I¹_{x'} × I²_{x'}`. -/
def prod {α₂ β₂ : Type u} (d : IndexDiagram α β) (d₂ : IndexDiagram α₂ β₂) :
    IndexDiagram (α × α₂) (β × β₂) where
  I := d.I × d₂.I
  a := Prod.map d.a d₂.a
  b := Prod.map d.b d₂.b
  surjective_a := d.surjective_a.prodMap d₂.surjective_a
  surjective_b := d.surjective_b.prodMap d₂.surjective_b
  uniform_a i i' := by
    rw [card_fiber_prodMap, card_fiber_prodMap, d.uniform_a i.1 i'.1, d₂.uniform_a i.2 i'.2]
  uniform_b j j' := by
    rw [card_fiber_prodMap, card_fiber_prodMap, d.uniform_b j.1 j'.1, d₂.uniform_b j.2 j'.2]

theorem map_equiv (e : α ≃ α') (e' : β ≃ β') {d d' : IndexDiagram α β} (h : d ≈ d') :
    d.map e e' ≈ d'.map e e' := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun k => ⟨congrArg e (hc k).1, congrArg e' (hc k).2⟩⟩

theorem swap_equiv {d d' : IndexDiagram α β} (h : d ≈ d') : d.swap ≈ d'.swap := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun k => ⟨(hc k).2, (hc k).1⟩⟩

theorem prod_equiv {α₂ β₂ : Type u} {d d' : IndexDiagram α β} {d₂ d₂' : IndexDiagram α₂ β₂}
    (h : d ≈ d') (h₂ : d₂ ≈ d₂') : d.prod d₂ ≈ d'.prod d₂' := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c₂, hc₂⟩ := h₂
  exact ⟨c.prodCongr c₂, fun k => ⟨Prod.ext (hc k.1).1 (hc₂ k.2).1,
    Prod.ext (hc k.1).2 (hc₂ k.2).2⟩⟩

/-! #### Remark 13.3.5: conditions on the pairs `(a(k), b(k))` -/

/-- `R (a k) (b k)` for all `k ∈ I` (property (3) of Definition 13.3.4 is of this form). -/
def Sat (R : α → β → Prop) (d : IndexDiagram α β) : Prop := ∀ k, R (d.a k) (d.b k)

/-- **2021 Remark 13.3.5, p. 615 (2017: Remark 13.1)**: the condition does not depend on the
representative. -/
theorem sat_iff_of_equiv (R : α → β → Prop) {d d' : IndexDiagram α β} (h : d ≈ d') :
    d.Sat R ↔ d'.Sat R := by
  obtain ⟨c, hc⟩ := h
  constructor
  · intro hd k
    have := hd (c.symm k)
    rwa [← (hc (c.symm k)).1, ← (hc (c.symm k)).2, _root_.Equiv.apply_symm_apply] at this
  · intro hd k
    have := hd (c k)
    rwa [(hc k).1, (hc k).2] at this

end IndexDiagram

/-! ### Correspondences (Definition 13.3.1) -/

/-- **Definition 13.3.1, p. 613**: a correspondence `[d] : I_x → I_{x'}`; `IndexCorr I_x I_{x'}`
is the set `J(x, x')`. -/
def IndexCorr (α β : Type u) : Type (u + 1) := Quotient (IndexDiagram.setoid α β)

namespace IndexCorr

variable {α β α' β' α'' β'' : Type u}

/-- The class of a diagram. -/
def mk (d : IndexDiagram α β) : IndexCorr α β := Quotient.mk _ d

theorem mk_eq_mk {d d' : IndexDiagram α β} : mk d = mk d' ↔ d ≈ d' := Quotient.eq

@[elab_as_elim]
theorem ind {p : IndexCorr α β → Prop} (h : ∀ d, p (mk d)) (τ : IndexCorr α β) : p τ :=
  Quotient.inductionOn τ h

/-- Relabel along bijections of the ends. -/
def map (e : α ≃ α') (e' : β ≃ β') : IndexCorr α β → IndexCorr α' β' :=
  Quotient.map (IndexDiagram.map e e') fun _ _ h => IndexDiagram.map_equiv e e' h

@[simp] theorem map_mk (e : α ≃ α') (e' : β ≃ β') (d : IndexDiagram α β) :
    map e e' (mk d) = mk (d.map e e') := rfl

theorem map_refl (τ : IndexCorr α β) : τ.map (Equiv.refl α) (Equiv.refl β) = τ :=
  ind (fun _ => mk_eq_mk.2 ⟨Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩) τ

theorem map_map (e₁ : α ≃ α') (e₁' : β ≃ β') (e₂ : α' ≃ α'') (e₂' : β' ≃ β'')
    (τ : IndexCorr α β) : (τ.map e₁ e₁').map e₂ e₂' = τ.map (e₁.trans e₂) (e₁'.trans e₂') :=
  ind (fun _ => mk_eq_mk.2 ⟨Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩) τ

/-- **2021 Definition 13.3.2, p. 614 (2017: Definition 13.15): the pseudo-inverse**
`♯ : J(x, x') → J(x', x)`. -/
def swap : IndexCorr α β → IndexCorr β α :=
  Quotient.map IndexDiagram.swap fun _ _ h => IndexDiagram.swap_equiv h

@[simp] theorem swap_mk (d : IndexDiagram α β) : swap (mk d) = mk d.swap := rfl

theorem swap_swap (τ : IndexCorr α β) : τ.swap.swap = τ := ind (fun _ => rfl) τ

/-- **Definition 13.3.2**: `♯` is a bijection `J(x, x') → J(x', x)`. -/
def swapEquiv : IndexCorr α β ≃ IndexCorr β α :=
  ⟨swap, swap, swap_swap, swap_swap⟩

section BiAction

variable {G G' : Type*} [Group G] [Group G'] [MulAction G α] [MulAction G' β]

/-- **Definition 13.3.2: the bi-action** `g' ∗ [I_x ←a I →b I_{x'}] ∗ g =
[I_x ←(g⁻¹ ∘ a) I →(g' ∘ b) I_{x'}]`. -/
def biact (g' : G') (τ : IndexCorr α β) (g : G) : IndexCorr α β :=
  τ.map (MulAction.toPerm g⁻¹) (MulAction.toPerm g')

theorem biact_one_one (τ : IndexCorr α β) : biact (1 : G') τ (1 : G) = τ := by
  refine ind (fun d => mk_eq_mk.2 ⟨Equiv.refl _, fun k => ⟨?_, ?_⟩⟩) τ
  · change d.a k = (1 : G)⁻¹ • d.a k; rw [inv_one, one_smul]
  · change d.b k = (1 : G') • d.b k; rw [one_smul]

/-- The bi-action is an action of `G_{x'} × G_xᵐᵒᵖ`: `g' ∗ (h' ∗ τ ∗ h) ∗ g = (g'h') ∗ τ ∗ (hg)`
(the law of `EpGroupoid.biact_biact`). -/
theorem biact_biact (g' h' : G') (h g : G) (τ : IndexCorr α β) :
    biact g' (biact h' τ h) g = biact (g' * h') τ (h * g) := by
  refine ind (fun d => mk_eq_mk.2 ⟨Equiv.refl _, fun k => ⟨?_, ?_⟩⟩) τ
  · change (h * g)⁻¹ • d.a k = g⁻¹ • h⁻¹ • d.a k; rw [mul_inv_rev, mul_smul]
  · change (g' * h') • d.b k = g' • h' • d.b k; rw [mul_smul]

end BiAction

/-- **2021 Example 13.3.3, p. 614 (2017: Example 13.1)**:
for `I_x = {∗}`, `g' ∗ [d] ∗ g = [d]` for all `g ∈ G_x`,
`g' ∈ G_{x'}` (a bijection `c : I → I` with `b ∘ c = g'⁻¹ ∘ b` exists since all fibres of `b` have
the same size). -/
theorem example_13_3_3 {G G' : Type*} [Group G] [Group G'] [MulAction G PUnit.{u + 1}]
    [MulAction G' β] (g' : G') (τ : IndexCorr PUnit.{u + 1} β) (g : G) : biact g' τ g = τ := by
  refine ind (fun d => ?_) τ
  refine mk_eq_mk.2 (Setoid.symm ?_)
  have hfib : ∀ j : β, Nonempty ({k // g'⁻¹ • d.b k = j} ≃ {k // d.b k = j}) := fun j => by
    refine Finite.card_eq.1 ?_
    rw [Nat.card_congr (_root_.Equiv.subtypeEquivRight fun _ => inv_smul_eq_iff)]
    exact d.uniform_b _ _
  let e := fun j => (hfib j).some
  refine ⟨Equiv.ofFiberEquiv e, fun k => ⟨Subsingleton.elim _ _, ?_⟩⟩
  change g' • d.b (Equiv.ofFiberEquiv e k) = d.b k
  rw [Equiv.ofFiberEquiv_map (f := fun k => g'⁻¹ • d.b k) (g := d.b) e k, smul_inv_smul]

/-! ### Special correspondences -/

/-- `[I_x ←id I_x →e I_{x'}]`. -/
def ofEquiv [Fintype α] (e : α ≃ β) : IndexCorr α β := mk (IndexDiagram.ofEquiv e)

/-- **`[I_x ←id I_x →g I_x]`** (Definition 13.3.6 (1)). -/
def ofPerm {G : Type*} [Group G] [Fintype α] [MulAction G α] (g : G) : IndexCorr α α :=
  ofEquiv (MulAction.toPerm g)

/-- `[{∗} ← I →id I]`. -/
def toUnit (β : Type u) [Fintype β] [Nonempty β] : IndexCorr PUnit.{u + 1} β :=
  mk (IndexDiagram.toUnit β)

/-- `[I ←id I → {∗}]`. -/
def fromUnit (α : Type u) [Fintype α] [Nonempty α] : IndexCorr α PUnit.{u + 1} :=
  (toUnit α).swap

/-! ### Products -/

/-- The product of correspondences (proof of Proposition 13.3.12):
`[a₁, b₁] × [a₂, b₂] = [a₁ × a₂, b₁ × b₂]`. -/
def prod {α₂ β₂ : Type u} : IndexCorr α β → IndexCorr α₂ β₂ → IndexCorr (α × α₂) (β × β₂) :=
  Quotient.map₂ IndexDiagram.prod fun _ _ h _ _ h₂ => IndexDiagram.prod_equiv h h₂

@[simp] theorem prod_mk {α₂ β₂ : Type u} (d : IndexDiagram α β) (d₂ : IndexDiagram α₂ β₂) :
    prod (mk d) (mk d₂) = mk (d.prod d₂) := rfl

theorem prod_swap {α₂ β₂ : Type u} (τ : IndexCorr α β) (τ₂ : IndexCorr α₂ β₂) :
    (τ.prod τ₂).swap = τ.swap.prod τ₂.swap :=
  ind (fun _ => ind (fun _ => rfl) τ₂) τ

theorem prod_biact {α₂ β₂ : Type u} {G G' : Type*} [Group G] [Group G'] [MulAction G α]
    [MulAction G' β] [MulAction G α₂] [MulAction G' β₂] (g' : G') (g : G) (τ : IndexCorr α β)
    (τ₂ : IndexCorr α₂ β₂) : (biact g' τ g).prod (biact g' τ₂ g) = biact g' (τ.prod τ₂) g :=
  ind (fun _ => ind (fun _ => mk_eq_mk.2 ⟨Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩) τ₂) τ

theorem prod_ofPerm {α₂ : Type u} {G : Type*} [Group G] [Fintype α] [Fintype α₂] [MulAction G α]
    [MulAction G α₂] (g : G) : (ofPerm g : IndexCorr α α).prod (ofPerm g : IndexCorr α₂ α₂) =
      ofPerm g :=
  mk_eq_mk.2 ⟨Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩

/-! ### Remark 13.3.5 on correspondences -/

/-- A condition `R (a k) (b k)` on the representatives of a correspondence (well defined by
`IndexDiagram.sat_iff_of_equiv`, Remark 13.3.5). -/
def Sat (R : α → β → Prop) : IndexCorr α β → Prop :=
  Quotient.lift (IndexDiagram.Sat R) fun _ _ h => propext (IndexDiagram.sat_iff_of_equiv R h)

@[simp] theorem sat_mk (R : α → β → Prop) (d : IndexDiagram α β) :
    (mk d).Sat R ↔ d.Sat R := Iff.rfl

/-- **Remark 13.3.5**: `τ` satisfies `R` iff one (equivalently every) representative does. -/
theorem sat_iff (R : α → β → Prop) (τ : IndexCorr α β) :
    τ.Sat R ↔ ∀ d, mk d = τ → d.Sat R := by
  refine ind (fun d => ⟨fun h d' hd' => ?_, fun h => h d rfl⟩) τ
  exact (IndexDiagram.sat_iff_of_equiv R (mk_eq_mk.1 hd')).2 h

theorem sat_prod {α₂ β₂ : Type u} {R : α → β → Prop} {R₂ : α₂ → β₂ → Prop}
    {R' : α × α₂ → β × β₂ → Prop} (hR : ∀ i j i₂ j₂, R i j → R₂ i₂ j₂ → R' (i, i₂) (j, j₂))
    {τ : IndexCorr α β} {τ₂ : IndexCorr α₂ β₂} (h : τ.Sat R) (h₂ : τ₂.Sat R₂) :
    (τ.prod τ₂).Sat R' := by
  revert h h₂
  refine ind (fun d => ind (fun d₂ => fun h h₂ k => hR _ _ _ _ (h k.1) (h₂ k.2)) τ₂) τ

theorem sat_map {R : α → β → Prop} {R' : α' → β' → Prop} (e : α ≃ α') (e' : β ≃ β')
    (hR : ∀ i j, R i j → R' (e i) (e' j)) {τ : IndexCorr α β} (h : τ.Sat R) :
    (τ.map e e').Sat R' := by
  revert h
  exact ind (fun d h k => hR _ _ (h k)) τ

theorem sat_swap {R : α → β → Prop} {τ : IndexCorr α β} (h : τ.Sat R) :
    τ.swap.Sat (fun j i => R i j) := by
  revert h
  exact ind (fun d h k => h k) τ

theorem sat_mono {R R' : α → β → Prop} (hR : ∀ i j, R i j → R' i j) {τ : IndexCorr α β}
    (h : τ.Sat R) : τ.Sat R' := by
  revert h
  exact ind (fun d h k => hR _ _ (h k)) τ

/-- Every correspondence satisfies a condition that holds for all pairs. -/
theorem sat_of_forall {R : α → β → Prop} (hR : ∀ i j, R i j) (τ : IndexCorr α β) : τ.Sat R :=
  ind (fun _ _ => hR _ _) τ

end IndexCorr

end SBLocalization

end Polyfold
