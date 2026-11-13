import Polyfold.Chapter13.P3D_SymmetricOn
import Polyfold.Chapter13.P3G_GoodSystemExistence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.2, pp. 610–612: **Definitions 13.2.7, 13.2.8** (decorated sc⁺-multisections) and the
decorated forms of **Definitions 13.2.9, 13.2.10** and **Lemmas 13.2.11, 13.2.13**
(2017: Definitions 13.9–13.12, Lemmas 13.4, 13.5).

# Decorated sc⁺-multisections

## The text, paraphrased

(Definition 13.2.7) An sc⁺-multisection with a system of symmetric section structures is
`(Λ, 𝒰, S)`: `Λ` an sc⁺-multisection, `𝒰` a good system, and for every `x` a symmetric
structure `sˣ = (sˣᵢ)_{i ∈ I_x}` on `U(x)` with `Λ(w) = |I_x|⁻¹·#{i | sˣᵢ(P(w)) = w}`.
(Definition 13.2.8) `(Λ, 𝒰, S)` and `(Λ', 𝒰', S')` are equivalent if `Λ = Λ'` and there are a
good system `𝒰''` with `U''(x) ⊆ U(x) ∩ U'(x)` and equivariant bijections `b_x : I_x → I'_x`
with `s'_{b_x(i)} = sᵢ` on `U''(x)`; a class `[Λ, 𝒰, S]` is a decorated sc⁺-multisection.
(Definition 13.2.9) The sum is decorated by `U(x) = U'(x) ∩ U''(x)`, `I_x = I'_x × I''_x`,
`s_{(i, i')} = s'_i + s''_{i'}`; it is associative and commutative.  (Definition 13.2.10) `aΛ` is
decorated by `(a·sᵢ)`.  (Lemma 13.2.11) `β ⊙ Λ` is decorated.  (Lemma 13.2.13) The sum of a
locally finite family is decorated by `U(x) = O(x) ∩ ⋂_{j ∈ J_x} U_j(x)`, `I_x = ∏_{j ∈ J_x} I^j_x`,
`sˣ_{(i_j)} = ∑_j s^{j,x}_{i_j}`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `GoodSystem.ofSubset`: neighbourhoods with the natural action inside those of a good system form
  a good system (Proposition 13.1.3 without the requirement of keeping the actions).
* **Definition 13.2.7**: `Decoration A Λ` (a good system and a `SymmetricStructureOn` on every
  `U(x)`), `DecoratedTuple A` (`(Λ, 𝒰, S)` with `Λ` an sc⁺-multisection).
* **Definition 13.2.8**: `Decoration.Rel`, `DecoratedTuple.Equiv` (an equivalence relation,
  `DecoratedTuple.equivalence`), `DecoratedMultisection A` (the quotient) and `forget`.
* `exists_decoration`: for paracompact `|X|` every sc⁺-multisection has a decoration (Lemma
  13.2.6 together with Theorem 13.1.8); this is the satisfiability witness of Definition 13.2.7.
* **Definition 13.2.9 (2)–(3)**: `Decoration.add`, `definition_13_2_9_decorated`, compatible with
  the equivalence (`Decoration.add_rel`), hence `DecoratedMultisection.add`;
  commutativity and associativity on classes `DecoratedMultisection.add_comm`,
  `DecoratedMultisection.add_assoc`.
* **Definition 13.2.10**: `Decoration.smul`, `definition_13_2_10_decorated`.
* **Lemma 13.2.11**: `Decoration.smulFun`, `lemma_13_2_11_decorated`.
* **Lemma 13.2.13**: `Decoration.lfSum`, `lemma_13_2_13_decorated`.

## Readings

* (13.2.9 (2), 13.2.13) `U(x) = U'(x) ∩ U''(x)` is replaced by an open `G_x`-invariant
  neighbourhood of `x` inside the intersection on which the natural actions of `U'(x)` and
  `U''(x)` agree (`NatNbhd.exists_le_of_finite`).  The intersection itself need not carry one
  natural action for which both structures are symmetric; the decorated class does not depend on
  the choice (Definition 13.2.8 allows shrinking).
* (13.2.13) When no `Λ_j` is non-trivial near `x`, the text leaves the natural action on `O(x)`
  open; we take it from a given good system `𝒰₀` (any `𝒰_j` when `J` is not empty).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

namespace GoodSystem

/-- **Shrinking a good system** to neighbourhoods `M(x) ⊆ U(x)` with the natural action (their
actions need not be those of `U(x)`): conditions (1) and (3) of Definition 13.1.2 pass to
subsets. -/
def ofSubset (𝒰 : X.GoodSystem) (M : ∀ x, X.NatNbhd x) (hM : ∀ x, (M x).U ⊆ 𝒰.U x) :
    X.GoodSystem where
  nbhd := M
  isProperSubset_closure x :=
    isProperMap_domRestrict_of_subset_of_isClosed X.continuous_src
      (𝒰.isProperSubset_closure x) (closure_mono (hM x)) isClosed_closure
  isDiffeoComponent x x' _ hφ :=
    𝒰.isDiffeoComponent_of_subset (M x).isOpen_U (M x').isOpen_U (hM x) (hM x') hφ

@[simp] theorem ofSubset_nbhd (𝒰 : X.GoodSystem) (M : ∀ x, X.NatNbhd x)
    (hM : ∀ x, (M x).U ⊆ 𝒰.U x) : (𝒰.ofSubset M hM).nbhd = M := rfl

/-- A common refinement of a good system inside open neighbourhoods `V(x)`. -/
theorem exists_subset_inter (𝒰 : X.GoodSystem) (V : Obj → Set Obj) (hV : ∀ x, IsOpen (V x))
    (hxV : ∀ x, x ∈ V x) : ∃ 𝒲 : X.GoodSystem, ∀ x, 𝒲.U x ⊆ 𝒰.U x ∩ V x := by
  obtain ⟨𝒲, -, h, -⟩ := 𝒰.exists_refinement_subset V hV hxV
  exact ⟨𝒲, h⟩

end GoodSystem

end EpGroupoid

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### Definition 13.2.7 -/

/-- **2021 Definition 13.2.7, p. 610 (2017: Definition 13.9)**: a system of symmetric section
structures for `Λ`: a good system `𝒰` and, for every `x`, a symmetric sc⁺-section structure
`sˣ = (sˣᵢ)_{i ∈ I_x}` on `U(x)` (with `Λ(w) = |I_x|⁻¹·#{i | sˣᵢ(P(w)) = w}` over `U(x)`). -/
structure Decoration (A : SEP.{u}) (Λ : A.W → ℚ≥0) where
  /-- The good system `𝒰`. -/
  𝒰 : A.X.GoodSystem
  /-- The symmetric structures `sˣ` on `U(x)`. -/
  S : ∀ x, SymmetricStructureOn A Λ (𝒰.nbhd x)

/-- **Definition 13.2.7**: an sc⁺-multisection with a system of symmetric section structures,
the tuple `(Λ, 𝒰, S)`. -/
structure DecoratedTuple (A : SEP.{u}) where
  /-- The sc⁺-multisection `Λ`. -/
  Λ : A.W → ℚ≥0
  isScPlusMultisection : IsScPlusMultisection A Λ
  /-- `(𝒰, S)`. -/
  dec : Decoration A Λ

/-! ### Definition 13.2.8 -/

/-- **Definition 13.2.8, conditions (1)–(2)**: a good system `𝒰''` with `U''(x) ⊆ U(x) ∩ U'(x)`
and, for every `x`, an equivariant bijection `b_x : I_x → I'_x` with `s'_{b_x(i)} = sᵢ` on
`U''(x)`.  (Stated for decorations of possibly different functors; Definition 13.2.8 adds
`Λ = Λ'`.) -/
def Decoration.Rel {Λ Λ' : A.W → ℚ≥0} (D : Decoration A Λ) (D' : Decoration A Λ') : Prop :=
  ∃ 𝒰'' : A.X.GoodSystem, (∀ x, 𝒰''.U x ⊆ D.𝒰.U x ∩ D'.𝒰.U x) ∧
    ∀ x, ∃ b : (D.S x).I ≃ (D'.S x).I, (∀ (g : A.X.Isotropy x) i, b (g • i) = g • b i) ∧
      ∀ i, ∀ y ∈ 𝒰''.U x, (D'.S x).s (b i) y = (D.S x).s i y

namespace Decoration

variable {Λ Λ' Λ'' : A.W → ℚ≥0}

theorem Rel.refl (D : Decoration A Λ) : D.Rel D :=
  ⟨D.𝒰, fun _ => subset_inter subset_rfl subset_rfl, fun _ =>
    ⟨Equiv.refl _, fun _ _ => rfl, fun _ _ _ => rfl⟩⟩

theorem Rel.symm {D : Decoration A Λ} {D' : Decoration A Λ'} (h : D.Rel D') : D'.Rel D := by
  obtain ⟨𝒰'', hsub, hb⟩ := h
  refine ⟨𝒰'', fun x y hy => ⟨(hsub x hy).2, (hsub x hy).1⟩, fun x => ?_⟩
  obtain ⟨b, hbg, hbs⟩ := hb x
  refine ⟨b.symm, fun g i => b.injective ?_, fun i y hy => ?_⟩
  · rw [hbg, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · have := hbs (b.symm i) y hy
    rw [Equiv.apply_symm_apply] at this
    exact this.symm

theorem Rel.trans {D : Decoration A Λ} {D' : Decoration A Λ'} {D'' : Decoration A Λ''}
    (h₁ : D.Rel D') (h₂ : D'.Rel D'') : D.Rel D'' := by
  obtain ⟨𝒰₁, hsub₁, hb₁⟩ := h₁
  obtain ⟨𝒰₂, hsub₂, hb₂⟩ := h₂
  obtain ⟨𝒲, h𝒲⟩ := 𝒰₁.exists_subset_inter 𝒰₂.U 𝒰₂.isOpen_U 𝒰₂.mem_U
  refine ⟨𝒲, fun x y hy => ⟨(hsub₁ x (h𝒲 x hy).1).1, (hsub₂ x (h𝒲 x hy).2).2⟩, fun x => ?_⟩
  obtain ⟨b₁, hbg₁, hbs₁⟩ := hb₁ x
  obtain ⟨b₂, hbg₂, hbs₂⟩ := hb₂ x
  refine ⟨b₁.trans b₂, fun g i => by simp [hbg₁, hbg₂], fun i y hy => ?_⟩
  rw [Equiv.trans_apply, hbs₂ _ y (h𝒲 x hy).2, hbs₁ _ y (h𝒲 x hy).1]

end Decoration

namespace DecoratedTuple

/-- **2021 Definition 13.2.8, p. 611 (2017: Definition 13.10)**: equivalence of sc⁺-multisections
with systems of symmetric section structures: `Λ = Λ'` and conditions (1)–(2). -/
def Equiv (T T' : DecoratedTuple A) : Prop := T.Λ = T'.Λ ∧ T.dec.Rel T'.dec

theorem equivalence : _root_.Equivalence (Equiv (A := A)) :=
  ⟨fun _ => ⟨rfl, Decoration.Rel.refl _⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
    fun h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩⟩

instance setoid (A : SEP.{u}) : Setoid (DecoratedTuple A) := ⟨Equiv, equivalence⟩

end DecoratedTuple

/-- **Definition 13.2.8: a decorated sc⁺-multisection** `[Λ, 𝒰, S]`, an equivalence class. -/
def DecoratedMultisection (A : SEP.{u}) : Type (u + 1) :=
  Quotient (DecoratedTuple.setoid A)

/-- The underlying sc⁺-multisection `Λ ≡ [Λ, 𝒰, S]`. -/
def DecoratedMultisection.forget : DecoratedMultisection A → (A.W → ℚ≥0) :=
  Quotient.lift (fun T : DecoratedTuple A => T.Λ) fun _ _ h => h.1

theorem DecoratedMultisection.isScPlusMultisection_forget (Λ : DecoratedMultisection A) :
    IsScPlusMultisection A Λ.forget :=
  Quotient.inductionOn Λ fun T => T.isScPlusMultisection

/-! ### Existence of decorations -/

/-- **Every sc⁺-multisection has a decoration** when `|X|` is paracompact (Lemma 13.2.6 at every
point, then a good system inside the domains, Theorem 13.1.8, shrunk to where the natural
actions agree).  This shows that Definition 13.2.7 is satisfiable. -/
theorem exists_decoration (hX : A.X.HasParacompactOrbitSpace) {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) : Nonempty (Decoration A Λ) := by
  choose N S using fun x => exists_symmetricStructureOn hΛ x
  obtain ⟨𝒰, h𝒰⟩ := A.X.theorem_13_1_8 hX (fun x => (N x).U) (fun x => (N x).isOpen_U)
    fun x => (N x).mem_U
  choose M hrep hMV hM₀ hM using fun x =>
    NatNbhd.exists_le_of_finite (𝒰.nbhd x) (fun _ : Unit => N x) isOpen_univ (mem_univ x)
  exact ⟨⟨𝒰.ofSubset M fun x => (hM₀ x).subset, fun x => (S x).some.restrict (hM x ())⟩⟩

/-! ### Definition 13.2.9 (2)–(3): the decorated sum -/

namespace Decoration

variable {Λ' Λ'' : A.W → ℚ≥0}

/-- The common neighbourhoods used for the sum: inside `U'(x) ∩ U''(x)`, with the action of
`U'(x)`, on which the actions of `U'(x)` and `U''(x)` agree. -/
theorem exists_common (D' : Decoration A Λ') (D'' : Decoration A Λ'') (x : A.Obj) :
    ∃ M : A.X.NatNbhd x, M.Le (D'.𝒰.nbhd x) ∧ M.Le (D''.𝒰.nbhd x) := by
  obtain ⟨M, -, -, h', h''⟩ := NatNbhd.exists_le_of_finite (D'.𝒰.nbhd x)
    (fun _ : Unit => D''.𝒰.nbhd x) isOpen_univ (mem_univ x)
  exact ⟨M, h', h'' ()⟩

/-- **2021 Definition 13.2.9 (2)–(3), p. 611**: the decoration of `Λ' ⊕ Λ''`: `U(x) ⊆ U'(x) ∩
U''(x)` (a common neighbourhood with the natural action), `I_x = I'_x × I''_x` and
`s_{(i, i')} = s'_i + s''_{i'}`. -/
def add (D' : Decoration A Λ') (D'' : Decoration A Λ'') :
    Decoration A (multisectionAdd Λ' Λ'') :=
  let M := fun x => (D'.exists_common D'' x).choose
  have hM := fun x => (D'.exists_common D'' x).choose_spec
  ⟨D'.𝒰.ofSubset M fun x => (hM x).1.subset, fun x =>
    ((D'.S x).restrict (hM x).1).add ((D''.S x).restrict (hM x).2)⟩

theorem add_U_subset (D' : Decoration A Λ') (D'' : Decoration A Λ'') (x : A.Obj) :
    (D'.add D'').𝒰.U x ⊆ D'.𝒰.U x ∩ D''.𝒰.U x := fun _ hy =>
  ⟨((D'.exists_common D'' x).choose_spec.1.subset hy),
    ((D'.exists_common D'' x).choose_spec.2.subset hy)⟩

theorem add_I (D' : Decoration A Λ') (D'' : Decoration A Λ'') (x : A.Obj) :
    ((D'.add D'').S x).I = ((D'.S x).I × (D''.S x).I) := rfl

theorem add_s_apply (D' : Decoration A Λ') (D'' : Decoration A Λ'') {x y : A.Obj}
    (hy : y ∈ (D'.add D'').𝒰.U x) (κ : ((D'.add D'').S x).I) :
    ((D'.add D'').S x).s κ y =
      ((⟨(D'.S x).s κ.1 y, (D'.S x).P_s κ.1 (D'.add_U_subset D'' x hy).1⟩ +
        ⟨(D''.S x).s κ.2 y, (D''.S x).P_s κ.2 (D'.add_U_subset D'' x hy).2⟩ :
          A.P ⁻¹' {y}) : A.W) :=
  SymmetricStructureOn.addSection_apply hy _ _

/-- **The decorated sum respects Definition 13.2.8**: equivalent summands give equivalent sums
(`b = b' × b''`). -/
theorem add_rel {Λ'₁ Λ'₂ Λ''₁ Λ''₂ : A.W → ℚ≥0} {D'₁ : Decoration A Λ'₁}
    {D'₂ : Decoration A Λ'₂} {D''₁ : Decoration A Λ''₁} {D''₂ : Decoration A Λ''₂}
    (h' : D'₁.Rel D'₂) (h'' : D''₁.Rel D''₂) : (D'₁.add D''₁).Rel (D'₂.add D''₂) := by
  obtain ⟨𝒰', hsub', hb'⟩ := h'
  obtain ⟨𝒰'', hsub'', hb''⟩ := h''
  obtain ⟨𝒲, h𝒲⟩ := (D'₁.add D''₁).𝒰.exists_subset_inter
    (fun x => (D'₂.add D''₂).𝒰.U x ∩ (𝒰'.U x ∩ 𝒰''.U x))
    (fun x => ((D'₂.add D''₂).𝒰.isOpen_U x).inter ((𝒰'.isOpen_U x).inter (𝒰''.isOpen_U x)))
    fun x => ⟨(D'₂.add D''₂).𝒰.mem_U x, 𝒰'.mem_U x, 𝒰''.mem_U x⟩
  refine ⟨𝒲, fun x y hy => ⟨(h𝒲 x hy).1, (h𝒲 x hy).2.1⟩, fun x => ?_⟩
  obtain ⟨b', hbg', hbs'⟩ := hb' x
  obtain ⟨b'', hbg'', hbs''⟩ := hb'' x
  refine ⟨b'.prodCongr b'', fun g κ => ?_, fun κ y hy => ?_⟩
  · exact Prod.ext (hbg' g κ.1) (hbg'' g κ.2)
  · have hy₁ := (h𝒲 x hy).1
    have hy₂ := (h𝒲 x hy).2.1
    have hy' := (h𝒲 x hy).2.2.1
    have hy'' := (h𝒲 x hy).2.2.2
    rw [add_s_apply D'₂ D''₂ hy₂, add_s_apply D'₁ D''₁ hy₁]
    congr 2
    · exact Subtype.ext (hbs' κ.1 y hy')
    · exact Subtype.ext (hbs'' κ.2 y hy'')

/-- **Definition 13.2.9 is symmetric up to Definition 13.2.8** ("commutative"): the decorations of
`Λ' ⊕ Λ''` and `Λ'' ⊕ Λ'` correspond under `(i, i') ↦ (i', i)`. -/
theorem add_comm_rel (D' : Decoration A Λ') (D'' : Decoration A Λ'') :
    (D'.add D'').Rel (D''.add D') := by
  obtain ⟨𝒲, h𝒲⟩ := (D'.add D'').𝒰.exists_subset_inter (D''.add D').𝒰.U
    (D''.add D').𝒰.isOpen_U (D''.add D').𝒰.mem_U
  refine ⟨𝒲, h𝒲, fun x => ⟨_root_.Equiv.prodComm _ _, fun g κ => rfl, fun κ y hy => ?_⟩⟩
  rw [add_s_apply D'' D' (h𝒲 x hy).2, add_s_apply D' D'' (h𝒲 x hy).1]
  exact congrArg Subtype.val (add_comm _ _)

/-- **Definition 13.2.9 is associative up to Definition 13.2.8**: the decorations of
`(Λ₁ ⊕ Λ₂) ⊕ Λ₃` and `Λ₁ ⊕ (Λ₂ ⊕ Λ₃)` correspond under `((i, j), k) ↦ (i, (j, k))`. -/
theorem add_assoc_rel {Λ₁ Λ₂ Λ₃ : A.W → ℚ≥0} (D₁ : Decoration A Λ₁) (D₂ : Decoration A Λ₂)
    (D₃ : Decoration A Λ₃) : ((D₁.add D₂).add D₃).Rel (D₁.add (D₂.add D₃)) := by
  obtain ⟨𝒲, h𝒲⟩ := ((D₁.add D₂).add D₃).𝒰.exists_subset_inter (D₁.add (D₂.add D₃)).𝒰.U
    (D₁.add (D₂.add D₃)).𝒰.isOpen_U (D₁.add (D₂.add D₃)).𝒰.mem_U
  refine ⟨𝒲, h𝒲, fun x => ⟨_root_.Equiv.prodAssoc _ _ _, fun g κ => rfl, fun κ y hy => ?_⟩⟩
  have hL := (h𝒲 x hy).1
  have hR := (h𝒲 x hy).2
  have hL₁₂ := ((D₁.add D₂).add_U_subset D₃ x hL).1
  have hR₂₃ := (D₁.add_U_subset (D₂.add D₃) x hR).2
  rw [add_s_apply D₁ (D₂.add D₃) hR, add_s_apply (D₁.add D₂) D₃ hL]
  have e₁₂ := add_s_apply D₁ D₂ hL₁₂ κ.1
  have e₂₃ := add_s_apply D₂ D₃ hR₂₃ (κ.1.2, κ.2)
  refine congrArg Subtype.val ?_
  calc _ = (⟨(D₁.S x).s κ.1.1 y, (D₁.S x).P_s κ.1.1 (D₁.add_U_subset D₂ x hL₁₂).1⟩ +
        (⟨(D₂.S x).s κ.1.2 y, (D₂.S x).P_s κ.1.2 (D₂.add_U_subset D₃ x hR₂₃).1⟩ +
          ⟨(D₃.S x).s κ.2 y, (D₃.S x).P_s κ.2 (D₂.add_U_subset D₃ x hR₂₃).2⟩) :
            A.P ⁻¹' {y}) := congrArg₂ (· + ·) rfl (Subtype.ext e₂₃)
    _ = (⟨(D₁.S x).s κ.1.1 y, (D₁.S x).P_s κ.1.1 (D₁.add_U_subset D₂ x hL₁₂).1⟩ +
          ⟨(D₂.S x).s κ.1.2 y, (D₂.S x).P_s κ.1.2 (D₂.add_U_subset D₃ x hR₂₃).1⟩) +
          ⟨(D₃.S x).s κ.2 y, (D₃.S x).P_s κ.2 (D₂.add_U_subset D₃ x hR₂₃).2⟩ :=
            (add_assoc _ _ _).symm
    _ = _ := congrArg₂ (· + ·) (Subtype.ext e₁₂).symm rfl

end Decoration

/-- **2021 Definition 13.2.9, p. 611 (2017: Definition 13.11), decorated**: the sum of two
sc⁺-multisections with systems of symmetric structures is one, with `U(x) ⊆ U'(x) ∩ U''(x)`,
`I_x = I'_x × I''_x` and `s_{(i, i')} = s'_i + s''_{i'}`. -/
def definition_13_2_9_decorated (T' T'' : DecoratedTuple A) : DecoratedTuple A :=
  ⟨multisectionAdd T'.Λ T''.Λ, definition_13_2_9 T'.isScPlusMultisection T''.isScPlusMultisection,
    T'.dec.add T''.dec⟩

theorem definition_13_2_9_decorated_equiv {T'₁ T'₂ T''₁ T''₂ : DecoratedTuple A}
    (h' : T'₁ ≈ T'₂) (h'' : T''₁ ≈ T''₂) :
    definition_13_2_9_decorated T'₁ T''₁ ≈ definition_13_2_9_decorated T'₂ T''₂ :=
  ⟨by change multisectionAdd _ _ = multisectionAdd _ _; rw [h'.1, h''.1],
    Decoration.add_rel h'.2 h''.2⟩

/-- **The sum of decorated sc⁺-multisections** `[Λ', 𝒰', S'] ⊕ [Λ'', 𝒰'', S'']` (Definition
13.2.9 on classes; well defined by `Decoration.add_rel`). -/
def DecoratedMultisection.add : DecoratedMultisection A → DecoratedMultisection A →
    DecoratedMultisection A :=
  Quotient.map₂ definition_13_2_9_decorated fun _ _ h' _ _ h'' =>
    definition_13_2_9_decorated_equiv h' h''

theorem DecoratedMultisection.forget_add (Λ' Λ'' : DecoratedMultisection A) :
    (Λ'.add Λ'').forget = multisectionAdd Λ'.forget Λ''.forget :=
  Quotient.inductionOn₂ Λ' Λ'' fun _ _ => rfl

/-- **Definition 13.2.9, "commutative"**, for decorated sc⁺-multisections. -/
theorem DecoratedMultisection.add_comm (Λ' Λ'' : DecoratedMultisection A) :
    Λ'.add Λ'' = Λ''.add Λ' :=
  Quotient.inductionOn₂ Λ' Λ'' fun T' T'' => Quotient.sound
    ⟨multisectionAdd_comm _ _, Decoration.add_comm_rel T'.dec T''.dec⟩

/-- **Definition 13.2.9, "associative"**, for decorated sc⁺-multisections. -/
theorem DecoratedMultisection.add_assoc (Λ₁ Λ₂ Λ₃ : DecoratedMultisection A) :
    (Λ₁.add Λ₂).add Λ₃ = Λ₁.add (Λ₂.add Λ₃) :=
  Quotient.inductionOn₃ Λ₁ Λ₂ Λ₃ fun T₁ T₂ T₃ => Quotient.sound
    ⟨multisectionAdd_assoc T₁.isScPlusMultisection T₂.isScPlusMultisection
      T₃.isScPlusMultisection, Decoration.add_assoc_rel T₁.dec T₂.dec T₃.dec⟩

/-! ### Definition 13.2.10 and Lemma 13.2.11 -/

namespace Decoration

variable {Λ : A.W → ℚ≥0}

/-- **Lemma 13.2.11, decorated**: `β ⊙ Λ` is decorated by `(𝒰, (β·sˣᵢ))`. -/
def smulFun (D : Decoration A Λ) (hΛ : IsScPlusMultisection A Λ) {β : A.Obj → ℝ}
    (hβ : ∀ φ : A.Mor, β (A.X.tgt φ) = β (A.X.src φ))
    (hβs : A.X.PObj.IsScSmoothMap realPolyfold β) : Decoration A (multisectionSmulFun β Λ) :=
  ⟨D.𝒰, fun x => (D.S x).smulFun hΛ hβ hβs⟩

/-- **Definition 13.2.10, decorated**: `aΛ` is decorated by `(𝒰, (a·sˣᵢ))`. -/
def smul (D : Decoration A Λ) (hΛ : IsScPlusMultisection A Λ) (a : ℝ) :
    Decoration A (multisectionSmul a Λ) :=
  ⟨D.𝒰, fun x => (D.S x).smul hΛ a⟩

theorem smulFun_rel {D D' : Decoration A Λ} (h : D.Rel D') (hΛ : IsScPlusMultisection A Λ)
    {β : A.Obj → ℝ} (hβ : ∀ φ : A.Mor, β (A.X.tgt φ) = β (A.X.src φ))
    (hβs : A.X.PObj.IsScSmoothMap realPolyfold β) :
    (D.smulFun hΛ hβ hβs).Rel (D'.smulFun hΛ hβ hβs) := by
  obtain ⟨𝒰'', hsub, hb⟩ := h
  refine ⟨𝒰'', hsub, fun x => ?_⟩
  obtain ⟨b, hbg, hbs⟩ := hb x
  refine ⟨b, hbg, fun (i : (D.S x).I) y hy => ?_⟩
  change SymmetricStructureOn.smulSection _ β ((D'.S x).s (b i)) y =
    SymmetricStructureOn.smulSection _ β ((D.S x).s i) y
  rw [SymmetricStructureOn.smulSection_apply (U := (D'.𝒰.nbhd x).U) (hsub x hy).2
      ((D'.S x).P_s _ (hsub x hy).2),
    SymmetricStructureOn.smulSection_apply (U := (D.𝒰.nbhd x).U) (hsub x hy).1
      ((D.S x).P_s _ (hsub x hy).1)]
  congr 2
  exact Subtype.ext (hbs i y hy)

end Decoration

/-- **2021 Definition 13.2.10, p. 611 (2017: Definition 13.12), decorated**: `aΛ` with the
decoration `(𝒰, (a·sˣᵢ))`. -/
def definition_13_2_10_decorated (T : DecoratedTuple A) (a : ℝ) : DecoratedTuple A :=
  ⟨multisectionSmul a T.Λ, definition_13_2_10 T.isScPlusMultisection a,
    T.dec.smul T.isScPlusMultisection a⟩

/-- **2021 Lemma 13.2.11, p. 612 (2017: Lemma 13.4), decorated**: for an sc-smooth functor
`β : X → ℝ`, `β ⊙ Λ` with the decoration `(𝒰, (β·sˣᵢ))`. -/
def lemma_13_2_11_decorated (T : DecoratedTuple A) {β : A.Obj → ℝ}
    (hβ : ∀ φ : A.Mor, β (A.X.tgt φ) = β (A.X.src φ))
    (hβs : A.X.PObj.IsScSmoothMap realPolyfold β) : DecoratedTuple A :=
  ⟨multisectionSmulFun β T.Λ, lemma_13_2_11 hβ hβs T.isScPlusMultisection,
    T.dec.smulFun T.isScPlusMultisection hβ hβs⟩

/-- The scalar multiple `aΛ` is well defined on decorated sc⁺-multisections. -/
def DecoratedMultisection.smul (a : ℝ) : DecoratedMultisection A → DecoratedMultisection A :=
  Quotient.map (fun T => definition_13_2_10_decorated T a) fun T T' h => by
    refine ⟨by change multisectionSmul _ _ = multisectionSmul _ _; rw [h.1], ?_⟩
    obtain ⟨hΛ, hrel⟩ := h
    obtain ⟨T, hT, D⟩ := T
    obtain ⟨T', hT', D'⟩ := T'
    change T = T' at hΛ
    subst hΛ
    exact Decoration.smulFun_rel hrel hT (β := fun _ => a) (fun _ => rfl)
      (isScSmoothMap_real_const a)

/-! ### Lemma 13.2.13: locally finite sums -/

section LocallyFinite

variable {J : Type*} {Λ : J → A.W → ℚ≥0}

/-- **A symmetric structure transfers to a functor agreeing over `U`.** -/
def SymmetricStructureOn.congr {Λ₁ Λ₂ : A.W → ℚ≥0} {x : A.Obj} {N : A.X.NatNbhd x}
    (S : SymmetricStructureOn A Λ₁ N) (h : ∀ w, A.P w ∈ N.U → Λ₂ w = Λ₁ w) :
    SymmetricStructureOn A Λ₂ N where
  I := S.I
  s := S.s
  isScPlusSectionOn := S.isScPlusSectionOn
  equivariant := S.equivariant
  rep w hw := (h w hw).trans (S.rep w hw)

/-- The data at `x` of the decoration of `⊕_j Λ_j`: the neighbourhood `O(x)` of Definition
13.2.12 and the finite set `J_x`. -/
theorem exists_lfData (hlf : IsLocallyFiniteFamily Λ) (x : A.Obj) :
    ∃ O : Set A.Obj, IsOpen O ∧ x ∈ O ∧ (nontrivIdx Λ O).Finite := by
  obtain ⟨O, hO, -, hx, hfin⟩ := hlf x
  exact ⟨O, hO, hx, hfin⟩

/-- **Lemma 13.2.13 at one point**: on a neighbourhood `M ≤ U_j(x)` (`j ∈ J_x`) inside `O(x)`, the
product structure `(∑_{j ∈ J_x} s^j_{i_j})_{(i_j) ∈ ∏_{j ∈ J_x} I^j_x}` is a symmetric structure
for `⊕_{j ∈ J} Λ_j`. -/
def lfSumStructure (hΛ : ∀ j, IsScPlusMultisection A (Λ j)) {O : Set A.Obj}
    (hfin : (nontrivIdx Λ O).Finite) {x : A.Obj} {M : A.X.NatNbhd x} (hMO : M.U ⊆ O)
    (S : ∀ j : hfin.toFinset, SymmetricStructureOn A (Λ j) M) :
    SymmetricStructureOn A (lfSum Λ) M :=
  let e := (Fintype.equivFin hfin.toFinset).symm
  SymmetricStructureOn.congr (SymmetricStructureOn.pi fun m => S (e m)) fun w hw => by
    rw [lfSum_eq_conv_of_mem hΛ hfin (hMO hw), conv, conv,
      ← convAt_comp_equiv e (fun j : hfin.toFinset => Λ j)]

/-- **2021 Lemma 13.2.13, p. 612 (2017: Lemma 13.5), decorated**: the decoration of the sum of a
locally finite family of decorated sc⁺-multisections: `U(x) ⊆ O(x) ∩ ⋂_{j ∈ J_x} U_j(x)` (a
common neighbourhood with the natural action, taken from the good system `𝒰₀`), the index set
`∏_{j ∈ J_x} I^j_x` and the sections `∑_{j ∈ J_x} s^{j,x}_{i_j}`. -/
def Decoration.lfSum (hΛ : ∀ j, IsScPlusMultisection A (Λ j)) (hlf : IsLocallyFiniteFamily Λ)
    (D : ∀ j, Decoration A (Λ j)) (𝒰₀ : A.X.GoodSystem) :
    Decoration A (SBLocalization.lfSum Λ) :=
  have hO := fun x => (exists_lfData hlf x).choose_spec
  have hM := fun x => NatNbhd.exists_le_of_finite (𝒰₀.nbhd x)
    (fun j : (hO x).2.2.toFinset => (D j).𝒰.nbhd x) (hO x).1 (hO x).2.1
  let M := fun x => (hM x).choose
  have hMs := fun x => (hM x).choose_spec
  ⟨𝒰₀.ofSubset M fun x => (hMs x).2.2.1.subset, fun x =>
    lfSumStructure hΛ (hO x).2.2 (hMs x).2.1 fun j => ((D j).S x).restrict ((hMs x).2.2.2 j)⟩

/-- **Lemma 13.2.13, decorated, as a tuple** (for a non-empty index set the good system `𝒰₀` is
taken from one of the members). -/
def lemma_13_2_13_decorated (T : J → DecoratedTuple A)
    (hlf : IsLocallyFiniteFamily fun j => (T j).Λ) (𝒰₀ : A.X.GoodSystem) : DecoratedTuple A :=
  ⟨SBLocalization.lfSum fun j => (T j).Λ, lemma_13_2_13 (fun j => (T j).isScPlusMultisection) hlf,
    Decoration.lfSum (fun j => (T j).isScPlusMultisection) hlf (fun j => (T j).dec) 𝒰₀⟩

end LocallyFinite

end SBLocalization

end Polyfold
