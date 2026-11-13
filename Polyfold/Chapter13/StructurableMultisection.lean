import Polyfold.Chapter13.DecoratedMultisection
import Polyfold.Chapter13.Correspondence
import Polyfold.Chapter13.BiAction

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.3, pp. 614–618: **Definition 13.3.4** (correspondences between local section structures),
**Definition 13.3.6** (structurable), **Definition 13.3.8** (equivalence of structured tuples),
**Definition 13.3.10** (structured sc⁺-multisections), **Definition 13.3.11** (`Γ⁺_m`, `Γ⁺_s`,
`Γ⁺_st`, `forget`), **Proposition 13.3.12** (sums), **Lemma 13.3.14** (scalar multiples)
(2017: §13.3, Definitions 13.16–13.20, Proposition 13.3, Lemma 13.6).

# Structurable sc⁺-multisections

## The text, paraphrased

(13.3.4) For local symmetric structures `(U(x), sˣ)` and `(U(x'), sˣ')`, a correspondence is a map
`τ_{x,x'} : 𝒰(x, x') → J(x, x')` which is (1) locally constant with finitely many values,
(2) equivariant for the bi-actions, and (3) for every representative `I_x ←a I →b I_{x'}` of
`τ_{x,x'}(φ)`: `sˣ'_{b(k)}(t(ψ)) = μ(ψ, sˣ_{a(k)}(s(ψ)))` for all `k` and all `ψ` in the
component of `φ`.  (13.3.6) `Λ = [Λ, 𝒰, S]` is structurable if a representative carries
correspondences `τ_{x,x'}` for all `x, x'` with (1) `τ_{x,x}(Γ(g, y)) = [I_x ←id I_x →g I_x]`
and (2) `τ_{x',x}(φ) = τ_{x,x'}(φ⁻¹)♯`.  (13.3.8) `(Λ, 𝒰, S, τ) ~ (Λ', 𝒰', S', τ')` if `Λ = Λ'`,
a good system `𝒰'' ⊆ 𝒰 ∩ 𝒰'` exists, `I_x = I'_x`, and `τ = τ'` on `𝒰''(x, x')`.  (13.3.10)
Classes are structured sc⁺-multisections.  (13.3.11) `Γ⁺_m(P)`, `Γ⁺_s(P)`, `Γ⁺_st(P)` and
`forget : Γ⁺_st(P) → Γ⁺_s(P)`.  (13.3.12) Sums of structurable (structured) sc⁺-multisections are
structurable (structured) with `I_x = I¹_x × I²_x` and `τ = τ¹ × τ²`.  (13.3.14) `rΛ` and `βΛ` are
structurable for structurable `Λ`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **Definition 13.3.4**: `Decoration.IsCorrespondence D x x' τ`, with condition (3) as
  `IndexCorr.Sat` (independent of the representative by Remark 13.3.5,
  `IndexCorr.sat_iff`).
* **Definition 13.3.6**: `Decoration.Tau D` (the correspondences `τ` with (1)–(2)),
  `StructuredTuple` (Remark 13.3.7: `(Λ, 𝒰, S, τ)`), `IsStructurable A Λ`, and
  `DecoratedMultisection.IsStructurable` (for the class `[Λ, 𝒰, S]`), `isStructurable_iff`.
* **Definition 13.3.8**: `StructuredTuple.Equiv` (with `I_x = I'_x` an equality of types and
  `τ'` compared to `τ` after `Equiv.cast`), `StructuredTuple.setoid`.
* **Definition 13.3.10**: `StructuredMultisection A`.
* **Definition 13.3.11**: `Γm`, `Γs`, `Γst`, `StructuredMultisection.forget`, `forget_mem_Γs`,
  `range_forget` (every structurable `Λ` lifts), `Γs_subset_Γm`.
* Restriction of `τ` to a smaller good system with the same actions: `Decoration.restrictTo`,
  `Decoration.Tau.restrict` (the bi-action does not change: `GoodSystem.biact_congr_of_le`).
* **Proposition 13.3.12**: `Decoration.Tau.prod`, `Decoration.Tau.add`, `StructuredTuple.add`,
  `proposition_13_3_12`.
* **Lemma 13.3.14**: `Decoration.Tau.smulFun`, `Decoration.Tau.smul`, `lemma_13_3_14`,
  `lemma_13_3_14_fun`.
* Satisfiability of the hypothesis "structurable": `isStructurable_zeroMultisection` (the zero
  multisection, on an ep-groupoid with paracompact orbit space).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- The bi-action only depends on the actions near `s(φ)` and `t(φ)`. -/
theorem biact_congr_of_le {x x' : Obj} {M N : X.NatNbhd x} {M' N' : X.NatNbhd x'}
    (h : M.Le N) (h' : M'.Le N') {φ : Mor} (hφ : φ ∈ X.morBetween M.U M'.U)
    (g' : X.Isotropy x') (g : X.Isotropy x) : biact M M' g' φ g = biact N N' g' φ g := by
  unfold biact
  rw [h'.Γ_eq g' _ hφ.2, h.Γ_eq g _ (M.Φ_mem g⁻¹ hφ.1), h.Φ_eq g⁻¹ hφ.1]

namespace GoodSystem

variable {𝒲 𝒰 : X.GoodSystem}

theorem mor_mono (h : ∀ x, 𝒲.U x ⊆ 𝒰.U x) (x x' : Obj) : 𝒲.mor x x' ⊆ 𝒰.mor x x' :=
  X.morBetween_mono (h x) (h x')

theorem comp_mono (h : ∀ x, 𝒲.U x ⊆ 𝒰.U x) (x x' : Obj) (φ : Mor) :
    𝒲.comp x x' φ ⊆ 𝒰.comp x x' φ :=
  connectedComponentIn_mono φ (mor_mono h x x')

theorem biact_congr_of_le (h : ∀ x, (𝒲.nbhd x).Le (𝒰.nbhd x)) {x x' : Obj} {φ : Mor}
    (hφ : φ ∈ 𝒲.mor x x') (g' : X.Isotropy x') (g : X.Isotropy x) :
    𝒲.biact x x' g' φ g = 𝒰.biact x x' g' φ g :=
  EpGroupoid.biact_congr_of_le (h x) (h x') hφ g' g

end GoodSystem

end EpGroupoid

namespace SBLocalization

namespace IndexCorr

variable {α β α' β' α'' β'' : Type u}

theorem map_cast_rfl (τ : IndexCorr α β) :
    τ.map (_root_.Equiv.cast rfl) (_root_.Equiv.cast rfl) = τ :=
  ind (fun _ => mk_eq_mk.2 ⟨_root_.Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩) τ

theorem map_cast_symm (h : α = α') (h' : β = β') (τ : IndexCorr α β) :
    (τ.map (_root_.Equiv.cast h) (_root_.Equiv.cast h')).map (_root_.Equiv.cast h.symm)
      (_root_.Equiv.cast h'.symm) = τ := by
  subst h h'
  exact ind (fun _ => mk_eq_mk.2 ⟨_root_.Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩) τ

theorem map_cast_trans (h₁ : α = α') (h₁' : β = β') (h₂ : α' = α'') (h₂' : β' = β'')
    (τ : IndexCorr α β) :
    (τ.map (_root_.Equiv.cast h₁) (_root_.Equiv.cast h₁')).map (_root_.Equiv.cast h₂)
      (_root_.Equiv.cast h₂') = τ.map (_root_.Equiv.cast (h₁.trans h₂))
        (_root_.Equiv.cast (h₁'.trans h₂')) := by
  subst h₁ h₁' h₂ h₂'
  exact ind (fun _ => mk_eq_mk.2 ⟨_root_.Equiv.refl _, fun _ => ⟨rfl, rfl⟩⟩) τ

end IndexCorr

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

namespace Decoration

variable {Λ : A.W → ℚ≥0}

/-! ### Definition 13.3.4 -/

/-- The identity of Definition 13.3.4 (3) for the indices `i ∈ I_x`, `j ∈ I_{x'}` along `ψ`:
`sˣ'_j(t(ψ)) = μ(ψ, sˣᵢ(s(ψ)))`. -/
def Compat (D : Decoration A Λ) {x x' : A.Obj} (ψ : A.Mor) (i : (D.S x).I) (j : (D.S x').I) :
    Prop :=
  (D.S x').s j (A.X.tgt ψ) = fibAct ψ ((D.S x).s i (A.X.src ψ))

/-- **2021 Definition 13.3.4, p. 614 (2017: Definition 13.16)**: a correspondence between the
local symmetric structures at `x` and `x'` is a map `τ : 𝒰(x, x') → J(x, x')` with (1) `τ` locally
constant with finitely many values, (2) `τ(g' ∗ φ ∗ g) = g' ∗ τ(φ) ∗ g`, (3) for every
representative `I_x ←a I →b I_{x'}` of `τ(φ)`, `sˣ'_{b(k)}(t(ψ)) = μ(ψ, sˣ_{a(k)}(s(ψ)))` for all
`k` and all `ψ` in the component of `φ` (`IndexCorr.Sat`, Remark 13.3.5). -/
structure IsCorrespondence (D : Decoration A Λ) (x x' : A.Obj)
    (τ : A.Mor → IndexCorr (D.S x).I (D.S x').I) : Prop where
  locallyConstant : ∀ φ ∈ D.𝒰.mor x x', ∀ᶠ ψ in 𝓝 φ, τ ψ = τ φ
  finite : (τ '' D.𝒰.mor x x').Finite
  biact : ∀ φ ∈ D.𝒰.mor x x', ∀ (g' : A.X.Isotropy x') (g : A.X.Isotropy x),
    τ (D.𝒰.biact x x' g' φ g) = IndexCorr.biact g' (τ φ) g
  compat : ∀ φ ∈ D.𝒰.mor x x', (τ φ).Sat fun i j => ∀ ψ ∈ D.𝒰.comp x x' φ, D.Compat ψ i j

/-! ### Definition 13.3.6 -/

/-- **2021 Definition 13.3.6, p. 615 (2017: Definition 13.17)**: correspondences `τ_{x,x'}` for
all `x, x' ∈ X` with (1) `τ_{x,x}(Γ(g, y)) = [I_x ←id I_x →g I_x]` and
(2) `τ_{x',x}(φ) = τ_{x,x'}(φ⁻¹)♯` for `φ ∈ 𝒰(x', x)`. -/
structure Tau (D : Decoration A Λ) where
  /-- The correspondences `τ_{x,x'}` (only their values on `𝒰(x, x')` matter). -/
  τ : ∀ x x' : A.Obj, A.Mor → IndexCorr (D.S x).I (D.S x').I
  isCorrespondence : ∀ x x', D.IsCorrespondence x x' (τ x x')
  diag : ∀ x (g : A.X.Isotropy x), ∀ y ∈ D.𝒰.U x,
    τ x x ((D.𝒰.nbhd x).rep.Γ g y) = IndexCorr.ofPerm (α := (D.S x).I) g
  swap : ∀ x x', ∀ φ ∈ D.𝒰.mor x' x, τ x' x φ = (τ x x' (A.X.inv φ)).swap

/-! ### Restriction to a smaller good system -/

/-- The decoration restricted to a good system `𝒲` with `W(x) ⊆ U(x)` and the same actions. -/
def restrictTo (D : Decoration A Λ) (𝒲 : A.X.GoodSystem)
    (h : ∀ x, (𝒲.nbhd x).Le (D.𝒰.nbhd x)) : Decoration A Λ :=
  ⟨𝒲, fun x => (D.S x).restrict (h x)⟩

/-- **Restriction of correspondences** to a smaller good system with the same actions ("we can
take the sets in `𝒰` as small as we wish", proof of Theorem 13.4.1). -/
def Tau.restrict {D : Decoration A Λ} (t : D.Tau) (𝒲 : A.X.GoodSystem)
    (h : ∀ x, (𝒲.nbhd x).Le (D.𝒰.nbhd x)) : (D.restrictTo 𝒲 h).Tau where
  τ := t.τ
  isCorrespondence x x' :=
    have hsub : ∀ x, 𝒲.U x ⊆ D.𝒰.U x := fun x => (h x).subset
    { locallyConstant := fun φ hφ =>
        (t.isCorrespondence x x').locallyConstant φ (GoodSystem.mor_mono hsub x x' hφ)
      finite := (t.isCorrespondence x x').finite.subset
        (image_mono (GoodSystem.mor_mono hsub x x'))
      biact := fun φ hφ g' g => by
        change t.τ x x' (𝒲.biact x x' g' φ g) = _
        rw [GoodSystem.biact_congr_of_le h hφ]
        exact (t.isCorrespondence x x').biact φ (GoodSystem.mor_mono hsub x x' hφ) g' g
      compat := fun φ hφ => IndexCorr.sat_mono
        (fun _ _ H ψ hψ => H ψ (GoodSystem.comp_mono hsub x x' φ hψ))
        ((t.isCorrespondence x x').compat φ (GoodSystem.mor_mono hsub x x' hφ)) }
  diag x g y hy := by
    change t.τ x x ((𝒲.nbhd x).rep.Γ g y) = _
    rw [(h x).Γ_eq g y hy]
    exact t.diag x g y ((h x).subset hy)
  swap x x' φ hφ := t.swap x x' φ (GoodSystem.mor_mono (fun x => (h x).subset) x' x hφ)

end Decoration

/-! ### Remark 13.3.7, Definitions 13.3.6, 13.3.8, 13.3.10 -/

/-- **2021 Remark 13.3.7, p. 616 (2017: Remark 13.2)**: the tuple `(Λ, 𝒰, S, τ)`. -/
structure StructuredTuple (A : SEP.{u}) extends DecoratedTuple A where
  /-- The correspondences `τ`. -/
  tau : dec.Tau

/-- **Definition 13.3.6, for sc⁺-multisection functors**: `Λ` is structurable if it has a system of
symmetric structures `(𝒰, S)` carrying correspondences `τ` as in Definition 13.3.6. -/
def IsStructurable (A : SEP.{u}) (Λ : A.W → ℚ≥0) : Prop :=
  IsScPlusMultisection A Λ ∧ ∃ D : Decoration A Λ, Nonempty D.Tau

/-- **2021 Definition 13.3.6, p. 615 (2017: Definition 13.17)**: a decorated sc⁺-multisection
`[Λ, 𝒰, S]` is structurable if some representative carries correspondences `τ`. -/
def DecoratedMultisection.IsStructurable (Λ : DecoratedMultisection A) : Prop :=
  ∃ T : DecoratedTuple A, (Quotient.mk _ T : DecoratedMultisection A) = Λ ∧ Nonempty T.dec.Tau

theorem isStructurable_iff {Λ : A.W → ℚ≥0} :
    IsStructurable A Λ ↔ ∃ L : DecoratedMultisection A, L.forget = Λ ∧ L.IsStructurable := by
  constructor
  · rintro ⟨hΛ, D, ⟨t⟩⟩
    exact ⟨Quotient.mk _ ⟨Λ, hΛ, D⟩, rfl, ⟨Λ, hΛ, D⟩, rfl, ⟨t⟩⟩
  · rintro ⟨L, rfl, T, rfl, ⟨t⟩⟩
    exact ⟨T.isScPlusMultisection, T.dec, ⟨t⟩⟩

namespace StructuredTuple

/-- **2021 Definition 13.3.8, p. 616 (2017: Definition 13.18)**: `(Λ, 𝒰, S, τ)` and
`(Λ', 𝒰', S', τ')` are equivalent if (1) `Λ = Λ'`, (2) there is a good system `𝒰''` with
`U''(x) ⊆ U(x) ∩ U'(x)`, (3) `I_x = I'_x` for all `x`, and (4) `τ_{x,x'} = τ'_{x,x'}` on
`𝒰''(x, x')`.  (Condition (3) is an equality of types; (4) compares `τ'` with `τ` transported
along it.  The text places no condition on the sections `sˣ`, `s'ˣ` here.) -/
def Equiv (T T' : StructuredTuple A) : Prop :=
  T.Λ = T'.Λ ∧ ∃ 𝒰'' : A.X.GoodSystem, (∀ x, 𝒰''.U x ⊆ T.dec.𝒰.U x ∩ T'.dec.𝒰.U x) ∧
    ∃ hI : ∀ x, (T.dec.S x).I = (T'.dec.S x).I, ∀ x x', ∀ φ ∈ 𝒰''.mor x x',
      T'.tau.τ x x' φ = (T.tau.τ x x' φ).map (_root_.Equiv.cast (hI x))
        (_root_.Equiv.cast (hI x'))

theorem equivalence : _root_.Equivalence (Equiv (A := A)) where
  refl T := ⟨rfl, T.dec.𝒰, fun _ => subset_inter subset_rfl subset_rfl, fun _ => rfl,
    fun x x' φ _ => (IndexCorr.map_cast_rfl _).symm⟩
  symm := by
    rintro T T' ⟨hΛ, 𝒰'', hsub, hI, hτ⟩
    refine ⟨hΛ.symm, 𝒰'', fun x y hy => ⟨(hsub x hy).2, (hsub x hy).1⟩, fun x => (hI x).symm,
      fun x x' φ hφ => ?_⟩
    rw [hτ x x' φ hφ, IndexCorr.map_cast_symm]
  trans := by
    rintro T T' T'' ⟨hΛ₁, 𝒰₁, hsub₁, hI₁, hτ₁⟩ ⟨hΛ₂, 𝒰₂, hsub₂, hI₂, hτ₂⟩
    obtain ⟨𝒲, h𝒲⟩ := 𝒰₁.exists_subset_inter 𝒰₂.U 𝒰₂.isOpen_U 𝒰₂.mem_U
    refine ⟨hΛ₁.trans hΛ₂, 𝒲,
      fun x y hy => ⟨(hsub₁ x (h𝒲 x hy).1).1, (hsub₂ x (h𝒲 x hy).2).2⟩,
      fun x => (hI₁ x).trans (hI₂ x), fun x x' φ hφ => ?_⟩
    have h₁ : φ ∈ 𝒰₁.mor x x' :=
      GoodSystem.mor_mono (fun x _ hy => (h𝒲 x hy).1) x x' hφ
    have h₂ : φ ∈ 𝒰₂.mor x x' :=
      GoodSystem.mor_mono (fun x _ hy => (h𝒲 x hy).2) x x' hφ
    rw [hτ₂ x x' φ h₂, hτ₁ x x' φ h₁, IndexCorr.map_cast_trans]

instance setoid (A : SEP.{u}) : Setoid (StructuredTuple A) := ⟨Equiv, equivalence⟩

end StructuredTuple

/-- **2021 Definition 13.3.10, p. 616 (2017: Definition 13.19)**: a structured sc⁺-multisection
`[Λ, 𝒰, S, τ]`. -/
def StructuredMultisection (A : SEP.{u}) : Type (u + 1) :=
  Quotient (StructuredTuple.setoid A)

/-- The underlying functor `Λ` of `[Λ, 𝒰, S, τ]`. -/
def StructuredMultisection.forget : StructuredMultisection A → (A.W → ℚ≥0) :=
  Quotient.lift (fun T : StructuredTuple A => T.Λ) fun _ _ h => h.1

/-! ### Definition 13.3.11 -/

/-- **2021 Definition 13.3.11 (1), p. 617 (2017: Definition 13.20)**: `Γ⁺_m(P)`, the
sc⁺-multisection functors. -/
def Γm (A : SEP.{u}) : Set (A.W → ℚ≥0) := {Λ | IsScPlusMultisection A Λ}

/-- **Definition 13.3.11 (2)**: `Γ⁺_s(P)`, the structurable sc⁺-multisection functors. -/
def Γs (A : SEP.{u}) : Set (A.W → ℚ≥0) := {Λ | IsStructurable A Λ}

/-- **Definition 13.3.11 (3)**: `Γ⁺_st(P)`, the structured sc⁺-multisections. -/
abbrev Γst (A : SEP.{u}) : Type (u + 1) := StructuredMultisection A

theorem Γs_subset_Γm : Γs A ⊆ Γm A := fun _ h => h.1

/-- **Definition 13.3.11: `forget : Γ⁺_st(P) → Γ⁺_s(P)`** lands in `Γ⁺_s(P)`. -/
theorem StructuredMultisection.forget_mem_Γs (Λ : Γst A) : Λ.forget ∈ Γs A :=
  Quotient.inductionOn Λ fun T => ⟨T.isScPlusMultisection, T.dec, ⟨T.tau⟩⟩

/-- **Definition 13.3.11, p. 617**: every structurable `Λ` lifts to a structured one:
`forget` maps `Γ⁺_st(P)` onto `Γ⁺_s(P)`. -/
theorem StructuredMultisection.range_forget : range (forget (A := A)) = Γs A := by
  refine (range_subset_iff.2 forget_mem_Γs).antisymm ?_
  rintro Λ ⟨hΛ, D, ⟨t⟩⟩
  exact ⟨Quotient.mk _ ⟨⟨Λ, hΛ, D⟩, t⟩, rfl⟩

/-! ### Proposition 13.3.12 -/

namespace Decoration

variable {Λ₁ Λ₂ : A.W → ℚ≥0}

/-- **Proposition 13.3.12, proof**: on a common good system, `τ = τ¹ × τ²` is a structure for the
symmetric structures `s_{(i,j)} = s¹ᵢ + s²ⱼ` on `I_x = I¹_x × I²_x`. -/
def Tau.prod {𝒰 : A.X.GoodSystem} {S₁ : ∀ x, SymmetricStructureOn A Λ₁ (𝒰.nbhd x)}
    {S₂ : ∀ x, SymmetricStructureOn A Λ₂ (𝒰.nbhd x)} (t₁ : (⟨𝒰, S₁⟩ : Decoration A Λ₁).Tau)
    (t₂ : (⟨𝒰, S₂⟩ : Decoration A Λ₂).Tau) :
    (⟨𝒰, fun x => (S₁ x).add (S₂ x)⟩ : Decoration A (multisectionAdd Λ₁ Λ₂)).Tau where
  τ x x' φ := (t₁.τ x x' φ).prod (t₂.τ x x' φ)
  isCorrespondence x x' :=
    { locallyConstant := fun φ hφ =>
        ((t₁.isCorrespondence x x').locallyConstant φ hφ).and
          ((t₂.isCorrespondence x x').locallyConstant φ hφ) |>.mono fun ψ h => by
            dsimp only; rw [h.1, h.2]
      finite := (((t₁.isCorrespondence x x').finite.image2 IndexCorr.prod
          (t₂.isCorrespondence x x').finite)).subset (by
        rintro _ ⟨φ, hφ, rfl⟩
        exact mem_image2_of_mem (mem_image_of_mem _ hφ) (mem_image_of_mem _ hφ))
      biact := fun φ hφ g' g => by
        dsimp only
        rw [(t₁.isCorrespondence x x').biact φ hφ, (t₂.isCorrespondence x x').biact φ hφ]
        exact IndexCorr.prod_biact g' g _ _
      compat := fun φ hφ => IndexCorr.sat_prod (fun i j i₂ j₂ H₁ H₂ ψ hψ => by
          have hψ' := 𝒰.comp_subset x x' φ hψ
          have e₁ := H₁ ψ hψ
          have e₂ := H₂ ψ hψ
          change SymmetricStructureOn.addSection _ _ _ _ =
            fibAct ψ (SymmetricStructureOn.addSection _ _ _ _)
          refine (fibAct_sectionAdd (isSection_extendZero _ _) (isSection_extendZero _ _)
            (isSection_extendZero _ _) (isSection_extendZero _ _) rfl rfl ?_ ?_).symm
          · rw [← extendZero_eqOn ((S₁ x').isScPlusSectionOn j).1 hψ'.2,
              ← extendZero_eqOn ((S₁ x).isScPlusSectionOn i).1 hψ'.1]
            exact e₁
          · rw [← extendZero_eqOn ((S₂ x').isScPlusSectionOn j₂).1 hψ'.2,
              ← extendZero_eqOn ((S₂ x).isScPlusSectionOn i₂).1 hψ'.1]
            exact e₂)
        ((t₁.isCorrespondence x x').compat φ hφ) ((t₂.isCorrespondence x x').compat φ hφ) }
  diag x g y hy := by
    dsimp only
    rw [t₁.diag x g y hy, t₂.diag x g y hy]
    exact IndexCorr.prod_ofPerm g
  swap x x' φ hφ := by
    dsimp only
    rw [t₁.swap x x' φ hφ, t₂.swap x x' φ hφ]
    exact (IndexCorr.prod_swap _ _).symm

variable {Λ' Λ'' : A.W → ℚ≥0}

theorem le_add_left (D' : Decoration A Λ') (D'' : Decoration A Λ'') (x : A.Obj) :
    ((D'.add D'').𝒰.nbhd x).Le (D'.𝒰.nbhd x) :=
  (D'.exists_common D'' x).choose_spec.1

theorem le_add_right (D' : Decoration A Λ') (D'' : Decoration A Λ'') (x : A.Obj) :
    ((D'.add D'').𝒰.nbhd x).Le (D''.𝒰.nbhd x) :=
  (D'.exists_common D'' x).choose_spec.2

/-- **Proposition 13.3.12**: correspondences for `Λ'` and `Λ''` give correspondences
`τ' × τ''` for the decorated sum `Λ' ⊕ Λ''` (Definition 13.2.9). -/
def Tau.add {D' : Decoration A Λ'} {D'' : Decoration A Λ''} (t' : D'.Tau) (t'' : D''.Tau) :
    (D'.add D'').Tau :=
  Tau.prod (t'.restrict (D'.add D'').𝒰 (le_add_left D' D''))
    (t''.restrict (D'.add D'').𝒰 (le_add_right D' D''))

end Decoration

/-- **Proposition 13.3.12, structured form**: `(Λ', 𝒰', S', τ') ⊕ (Λ'', 𝒰'', S'', τ'')`. -/
def StructuredTuple.add (T' T'' : StructuredTuple A) : StructuredTuple A :=
  ⟨definition_13_2_9_decorated T'.toDecoratedTuple T''.toDecoratedTuple, T'.tau.add T''.tau⟩

theorem StructuredTuple.add_Λ (T' T'' : StructuredTuple A) :
    (T'.add T'').Λ = multisectionAdd T'.Λ T''.Λ := rfl

/-- **2021 Proposition 13.3.12, p. 617 (2017: Proposition 13.3)**: the sum of structurable
sc⁺-multisection functors is structurable. -/
theorem proposition_13_3_12 {Λ' Λ'' : A.W → ℚ≥0} (h' : IsStructurable A Λ')
    (h'' : IsStructurable A Λ'') : IsStructurable A (multisectionAdd Λ' Λ'') := by
  obtain ⟨hΛ', D', ⟨t'⟩⟩ := h'
  obtain ⟨hΛ'', D'', ⟨t''⟩⟩ := h''
  exact ⟨definition_13_2_9 hΛ' hΛ'', D'.add D'', ⟨t'.add t''⟩⟩

/-! ### Lemma 13.3.14 -/

namespace Decoration

variable {Λ : A.W → ℚ≥0}

/-- **Lemma 13.3.14, `βΛ`**: the correspondences of `Λ` serve for `(β·sˣᵢ)` (same index sets). -/
def Tau.smulFun {D : Decoration A Λ} (t : D.Tau) (hΛ : IsScPlusMultisection A Λ)
    {β : A.Obj → ℝ} (hβ : ∀ φ : A.Mor, β (A.X.tgt φ) = β (A.X.src φ))
    (hβs : A.X.PObj.IsScSmoothMap realPolyfold β) : (D.smulFun hΛ hβ hβs).Tau where
  τ := t.τ
  isCorrespondence x x' :=
    { locallyConstant := (t.isCorrespondence x x').locallyConstant
      finite := (t.isCorrespondence x x').finite
      biact := (t.isCorrespondence x x').biact
      compat := fun φ hφ => IndexCorr.sat_mono (fun i j H ψ hψ => by
          have hψ' := D.𝒰.comp_subset x x' φ hψ
          change SymmetricStructureOn.smulSection _ _ _ _ =
            fibAct ψ (SymmetricStructureOn.smulSection _ _ _ _)
          refine (fibAct_sectionSmul (isSection_extendZero _ _) (isSection_extendZero _ _)
            rfl rfl (hβ ψ) ?_).symm
          rw [← extendZero_eqOn (((D.S x').isScPlusSectionOn j)).1 hψ'.2,
            ← extendZero_eqOn ((D.S x).isScPlusSectionOn i).1 hψ'.1]
          exact H ψ hψ)
        ((t.isCorrespondence x x').compat φ hφ) }
  diag := t.diag
  swap := t.swap

/-- **Lemma 13.3.14, `rΛ`**: the correspondences of `Λ` serve for `(r·sˣᵢ)`. -/
def Tau.smul {D : Decoration A Λ} (t : D.Tau) (hΛ : IsScPlusMultisection A Λ) (a : ℝ) :
    (D.smul hΛ a).Tau :=
  t.smulFun hΛ (β := fun _ => a) (fun _ => rfl) (isScSmoothMap_real_const a)

end Decoration

/-- **2021 Lemma 13.3.14, p. 618 (2017: Lemma 13.6)**: `rΛ` is structurable for structurable `Λ`
and `r ∈ ℝ`. -/
theorem lemma_13_3_14 {Λ : A.W → ℚ≥0} (h : IsStructurable A Λ) (a : ℝ) :
    IsStructurable A (multisectionSmul a Λ) := by
  obtain ⟨hΛ, D, ⟨t⟩⟩ := h
  exact ⟨definition_13_2_10 hΛ a, D.smul hΛ a, ⟨t.smul hΛ a⟩⟩

/-- **Lemma 13.3.14, second part**: `βΛ` is structurable for structurable `Λ` and an sc-smooth
functor `β : X → ℝ`. -/
theorem lemma_13_3_14_fun {Λ : A.W → ℚ≥0} (h : IsStructurable A Λ) {β : A.Obj → ℝ}
    (hβ : ∀ φ : A.Mor, β (A.X.tgt φ) = β (A.X.src φ))
    (hβs : A.X.PObj.IsScSmoothMap realPolyfold β) :
    IsStructurable A (multisectionSmulFun β Λ) := by
  obtain ⟨hΛ, D, ⟨t⟩⟩ := h
  exact ⟨lemma_13_2_11 hβ hβs hΛ, D.smulFun hΛ hβ hβs, ⟨t.smulFun hΛ hβ hβs⟩⟩

/-! ### The hypothesis "structurable" is satisfiable -/

namespace IndexCorr

/-- On a one-point index set, `[{∗} ←id {∗} →g {∗}] = [{∗} ←id {∗} →id {∗}]`. -/
theorem ofEquiv_eq_of_subsingleton {α : Type u} [Fintype α] [Subsingleton α] (e e' : α ≃ α) :
    ofEquiv e = ofEquiv e' :=
  mk_eq_mk.2 ⟨_root_.Equiv.refl _, fun _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

theorem swap_ofEquiv_of_subsingleton {α : Type u} [Fintype α] [Subsingleton α] (e : α ≃ α) :
    (ofEquiv e).swap = ofEquiv e :=
  mk_eq_mk.2 ⟨_root_.Equiv.refl _, fun _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

end IndexCorr

/-- The structure of the zero multisection on a good system: the single zero section at every
point, `τ ≡ [{∗} ← {∗} → {∗}]`. -/
def Decoration.zeroTau (𝒰 : A.X.GoodSystem) :
    (⟨𝒰, fun _ => SymmetricStructureOn.ofTrivial (isScPlusMultisection_zeroMultisection A)
      (fun y _ => isTrivialOn_zeroMultisection A y (mem_univ y))⟩ :
        Decoration A (zeroMultisection A)).Tau where
  τ _ _ _ := IndexCorr.ofEquiv (_root_.Equiv.refl PUnit.{u + 1})
  isCorrespondence x x' :=
    { locallyConstant := fun _ _ => Eventually.of_forall fun _ => rfl
      finite := (finite_singleton (IndexCorr.ofEquiv (_root_.Equiv.refl PUnit.{u + 1}))).subset
        (by rintro _ ⟨_, _, rfl⟩; rfl)
      biact := fun _ _ g' g => (IndexCorr.example_13_3_3 g' _ g).symm
      compat := fun _ _ => IndexCorr.sat_of_forall (fun _ _ ψ _ =>
        (fibAct_fiberZero rfl rfl).symm) _ }
  diag _ _ _ _ := IndexCorr.ofEquiv_eq_of_subsingleton (α := PUnit.{u + 1}) _ _
  swap _ _ _ _ := (IndexCorr.swap_ofEquiv_of_subsingleton (α := PUnit.{u + 1}) _).symm

/-- **The hypothesis "structurable" is satisfiable**: the zero multisection is structurable on
an ep-groupoid with paracompact orbit space (a good system exists by Theorem 13.1.8). -/
theorem isStructurable_zeroMultisection (hX : A.X.HasParacompactOrbitSpace) :
    IsStructurable A (zeroMultisection A) := by
  obtain ⟨𝒰, -⟩ := A.X.theorem_13_1_8 hX (fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => mem_univ _)
  exact ⟨isScPlusMultisection_zeroMultisection A, _, ⟨Decoration.zeroTau 𝒰⟩⟩

end SBLocalization

end Polyfold
