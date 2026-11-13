import Polyfold.Chapter14.BoundaryStructured

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.2, pp. 646–649:
**Lemma 14.2.1**, **Lemma 14.2.2**, **Proposition 14.2.3** (good structured version)
(2017: §14.2, the text before Lemma 14.1, Lemma 14.1, Proposition 14.2).

# A good structured version of `Λ`

## The text, paraphrased

Fix a representative `(Λ, 𝒰⁰, S⁰, τ⁰)` of a structured lift of `Λ` (requirements (P1)–(P3)).
(Lemma 14.2.1) Every `x ∈ ∂X` has an open connected `G_x`-invariant neighbourhood `U(x)` in
`∂X`, the union of the faces containing `x`, with `cl_{|∂X|}(|U(x)|) ⊆ |U⁰(x)|` (14.15); then
`cl_X(U(x)) ⊆ U⁰(x)` and `U(x)` inherits properness.  (Lemma 14.2.2) For
`𝒰(x, x') = {φ | s(φ) ∈ U(x), t(φ) ∈ U(x')}` the closures in `𝐗` of the preimages under
`τ⁰_{x,x'}|𝒰(x, x')` of two different values are disjoint (`τ⁰` is locally constant on
`𝒰⁰(x, x')`, which contains the limit points).  (Proposition 14.2.3) Hence the representative
can be chosen with, besides (P1)–(P3), (P4): for `[d] ≠ [d']` the closures of `τ⁰⁻¹([d])` and
`τ⁰⁻¹([d'])` in `𝐗` are disjoint; (P4) persists under shrinking.

## What is formalized

* **Lemma 14.2.1**: `lemma_14_2_1` (for one `x`: a good neighbourhood `V ≤ V⁰(x)` with
  `cl V ⊆ V⁰(x)`, `cl_X U(x) ⊆ U⁰(x)` and `cl_{|X|}|U(x)| ⊆ |U⁰(x)|`; the faces, connectedness
  and invariance are those of Definition 14.1.2) and `lemma_14_2_1_system` (a whole good system
  for `∂X` with these properties).  Needs `X` tame (Proposition 14.1.1).
* **Lemma 14.2.2**: `lemma_14_2_2` (abstract: for any good system `𝒰` with
  `cl_X U(x) ⊆ U⁰(x)`).
* Restriction of the data to a smaller good system with the same actions:
  `BoundaryDecoration.restrictTo`, `BoundaryDecoration.Tau.restrict`,
  `BoundaryStructuredTuple.restrict`, `equiv_restrict`.
* **Proposition 14.2.3**: `BoundaryStructuredTuple.HasP4`, `HasP4.restrict` ("it persists when
  we replace these sets by even smaller ones"), `proposition_14_2_3` (an equivalent
  representative with (P4)) and `proposition_14_2_3_class` (for structured sc⁺-multisections
  over `∂X`).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

/-! ### Lemma 14.2.1 -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- **2021 Lemma 14.2.1, p. 648 (2017: the text before Lemma 14.1)**: for a good neighbourhood `V⁰(x)` of
`x ∈ ∂X` (`U⁰(x) = V⁰(x) ∩ ∂X`) there is a good neighbourhood `V ≤ V⁰(x)` (same natural action,
connected, `U(x) = V ∩ ∂X` connected and the union of the faces through `x`) with
`cl_X(V) ⊆ V⁰(x)`, `cl_X(U(x)) ⊆ U⁰(x)` and `cl_{|X|}(|U(x)|) ⊆ |U⁰(x)|` (14.15).  (`|∂X|` is
closed in `|X|`, so the closure in `|∂X|` is the closure in `|X|`.) -/
theorem lemma_14_2_1 (hX : X.IsTame) {x : Obj} (hx : x ∈ X.PObj.boundary) (V₀ : X.NatNbhd x)
    (hV₀ : X.IsGoodBoundaryNbhd V₀) :
    ∃ V : X.NatNbhd x, V.Le V₀ ∧ X.IsGoodBoundaryNbhd V ∧ closure V.U ⊆ V₀.U ∧
      closure V.bdry ⊆ V₀.bdry ∧ closure (X.π '' V.bdry) ⊆ X.π '' V₀.bdry := by
  obtain ⟨C, hCn, hCc, hCU⟩ := exists_mem_nhds_isClosed_subset (V₀.isOpen_U.mem_nhds V₀.mem_U)
  obtain ⟨V, hrep, hsub, hgood⟩ := X.exists_isGoodBoundaryNbhd_le hX hx V₀
    hV₀.isProperSubset_closure isOpen_interior (mem_interior_iff_mem_nhds.2 hCn)
  have hVU : V.U ⊆ V₀.U := fun y hy => (hsub hy).1
  have hcl : closure V.U ⊆ V₀.U :=
    (closure_minimal (fun y hy => interior_subset (hsub hy).2) hCc).trans hCU
  have hclb : closure V.bdry ⊆ V₀.bdry := fun y hy =>
    ⟨hcl (closure_mono inter_subset_left hy),
      closure_minimal inter_subset_right X.PObj.isClosed_boundary hy⟩
  refine ⟨V, NatNbhd.le_of_rep_eq hrep hVU, hgood, hcl, hclb, ?_⟩
  rw [← X.proposition_7_1_10_of_isProperMap hV₀.isProperSubset_closure
    ((NatNbhd.bdry_subset V).trans (hVU.trans subset_closure))]
  exact image_mono hclb

/-- **Lemma 14.2.1 for all `x ∈ ∂X` at once**: a good system `𝒰 ≤ 𝒰⁰` for `∂X` with (14.15),
`cl_X(V(x)) ⊆ V⁰(x)` and `cl_X(U(x)) ⊆ U⁰(x)`. -/
theorem lemma_14_2_1_system (hX : X.IsTame) (𝒰₀ : X.BoundaryGoodSystem) :
    ∃ 𝒰 : X.BoundaryGoodSystem, ∀ x, (𝒰.nbhd x).Le (𝒰₀.nbhd x) ∧
      closure (𝒰.nbhd x).U ⊆ (𝒰₀.nbhd x).U ∧ closure (𝒰.U x) ⊆ 𝒰₀.U x ∧
      closure (X.π '' 𝒰.U x) ⊆ X.π '' 𝒰₀.U x := by
  choose V hle hgood hcl hclb hπ using fun x : X.PObj.boundary =>
    lemma_14_2_1 hX x.2 (𝒰₀.nbhd x) (𝒰₀.isGood x)
  exact ⟨⟨V, hgood, fun x x' φ hφ => 𝒰₀.isDiffeoComponent_of_subset (V x).isOpen_U
    (V x').isOpen_U (hle x).subset (hle x').subset hφ⟩,
    fun x => ⟨hle x, hcl x, hclb x, hπ x⟩⟩

end EpGroupoid

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-! ### Lemma 14.2.2 -/

/-- `cl_𝐗(𝒰(x, x')) ⊆ 𝒰⁰(x, x')` when `cl_X U(x) ⊆ U⁰(x)` for all `x`. -/
theorem closure_mor_subset {𝒰 𝒰₀ : A.X.BoundaryGoodSystem}
    (hcl : ∀ x, closure (𝒰.U x) ⊆ 𝒰₀.U x) (x x' : A.X.PObj.boundary) :
    closure (𝒰.mor x x') ⊆ 𝒰₀.mor x x' := fun _ hφ =>
  ⟨hcl x (map_mem_closure A.X.continuous_src hφ fun _ hψ => hψ.1),
    hcl x' (map_mem_closure A.X.continuous_tgt hφ fun _ hψ => hψ.2)⟩

/-- **2021 Lemma 14.2.2, p. 648 (2017: Lemma 14.1)**: let `τ` be locally constant on
`𝒰⁰(x, x')` (Definition 14.1.7 (2)) and let `𝒰` be a good system for `∂X` with
`cl_X(U(x)) ⊆ U⁰(x)` (Lemma 14.2.1).  Then for `[d] ≠ [d']` the closures in `𝐗` of
`τ⁻¹([d]) ∩ 𝒰(x, x')` and `τ⁻¹([d']) ∩ 𝒰(x, x')` are disjoint.  (The text defines
`𝒰(x, x')` with `t(φ) ∈ U(x)`; presumably `t(φ) ∈ U(x')` is meant, as in (P3).) -/
theorem lemma_14_2_2 {𝒰 𝒰₀ : A.X.BoundaryGoodSystem} (hcl : ∀ x, closure (𝒰.U x) ⊆ 𝒰₀.U x)
    {x x' : A.X.PObj.boundary} {β : Type*} {τ : A.Mor → β}
    (hτ : ∀ φ ∈ 𝒰₀.mor x x', ∀ᶠ ψ in 𝓝[𝒰₀.mor x x'] φ, τ ψ = τ φ) {d d' : β} (hd : d ≠ d') :
    closure (τ ⁻¹' {d} ∩ 𝒰.mor x x') ∩ closure (τ ⁻¹' {d'} ∩ 𝒰.mor x x') = ∅ := by
  have hsub : 𝒰.mor x x' ⊆ 𝒰₀.mor x x' := subset_closure.trans (closure_mor_subset hcl x x')
  have key : ∀ {e : β} {φ : A.Mor}, φ ∈ closure (τ ⁻¹' {e} ∩ 𝒰.mor x x') → τ φ = e := by
    intro e φ hφ
    have hφ₀ : φ ∈ 𝒰₀.mor x x' := closure_mor_subset hcl x x' (closure_mono inter_subset_right hφ)
    have hfr : ∃ᶠ ψ in 𝓝[𝒰₀.mor x x'] φ, ψ ∈ τ ⁻¹' {e} ∩ 𝒰.mor x x' :=
      frequently_nhdsWithin_iff.2 ((mem_closure_iff_frequently.1 hφ).mono fun ψ hψ =>
        ⟨hψ, hsub hψ.2⟩)
    obtain ⟨ψ, hψ, hψe⟩ := ((hτ φ hφ₀).and_frequently hfr).exists
    exact hψ.symm.trans hψe.1
  rw [eq_empty_iff_forall_notMem]
  rintro φ ⟨h₁, h₂⟩
  exact hd ((key h₁).symm.trans (key h₂))

/-! ### Restriction to a smaller good system -/

namespace BoundaryDecoration

variable {Λ : A.W → ℚ≥0}

/-- The decoration restricted to a good system `𝒲` for `∂X` with `V_𝒲(x) ≤ V(x)`. -/
def restrictTo (D : BoundaryDecoration A Λ) (𝒲 : A.X.BoundaryGoodSystem)
    (h : ∀ x, (𝒲.nbhd x).Le (D.𝒰.nbhd x)) : BoundaryDecoration A Λ :=
  ⟨𝒲, fun x => (D.S x).restrict (h x)⟩

theorem mor_mono {𝒲 𝒰 : A.X.BoundaryGoodSystem} (h : ∀ x, (𝒲.nbhd x).Le (𝒰.nbhd x))
    (x x' : A.X.PObj.boundary) : 𝒲.mor x x' ⊆ 𝒰.mor x x' :=
  EpGroupoid.morBetween_mono (NatNbhd.bdry_mono (h x).subset)
    (NatNbhd.bdry_mono (h x').subset)

/-- **Restriction of the correspondences** to a smaller good system with the same actions. -/
def Tau.restrict {D : BoundaryDecoration A Λ} (t : D.Tau) (𝒲 : A.X.BoundaryGoodSystem)
    (h : ∀ x, (𝒲.nbhd x).Le (D.𝒰.nbhd x)) : (D.restrictTo 𝒲 h).Tau where
  τ := t.τ
  locallyConstant x x' φ hφ :=
    (t.locallyConstant x x' φ (mor_mono h x x' hφ)).filter_mono
      (nhdsWithin_mono _ (mor_mono h x x'))
  finite x x' := (t.finite x x').subset (image_mono (mor_mono h x x'))
  swap x x' φ hφ := t.swap x x' φ (mor_mono h x x' hφ)
  diag x g z hz := by
    change t.τ x x ((𝒲.nbhd x).rep.Γ g z) = _
    rw [(h x).Γ_eq g z hz.1]
    exact t.diag x g z (NatNbhd.bdry_mono (h x).subset hz)
  biact x x' φ hφ g' g := by
    change t.τ x x' (EpGroupoid.biact (𝒲.nbhd x) (𝒲.nbhd x') g' φ g) = _
    rw [EpGroupoid.biact_congr_of_le (h x) (h x') (𝒲.mor_subset x x' hφ)]
    exact t.biact x x' φ (mor_mono h x x' hφ) g' g
  compat x x' φ hφ := t.compat x x' φ (mor_mono h x x' hφ)

end BoundaryDecoration

namespace BoundaryStructuredTuple

/-- The tuple restricted to a smaller good system for `∂X` with the same actions. -/
def restrict (T : BoundaryStructuredTuple A) (𝒲 : A.X.BoundaryGoodSystem)
    (h : ∀ x, (𝒲.nbhd x).Le (T.dec.𝒰.nbhd x)) : BoundaryStructuredTuple A :=
  ⟨T.Λ, T.isBoundaryScPlusMultisection, T.dec.restrictTo 𝒲 h, T.tau.restrict 𝒲 h⟩

/-- The restriction is equivalent to the tuple. -/
theorem equiv_restrict (T : BoundaryStructuredTuple A) (𝒲 : A.X.BoundaryGoodSystem)
    (h : ∀ x, (𝒲.nbhd x).Le (T.dec.𝒰.nbhd x)) : Equiv T (T.restrict 𝒲 h) :=
  ⟨fun _ _ => rfl, fun x => (𝒲.nbhd x).U, fun x => (𝒲.nbhd x).isOpen_U,
    fun x => (𝒲.nbhd x).mem_U, fun x _ hy => ⟨NatNbhd.bdry_mono (h x).subset hy, hy⟩,
    fun _ => rfl, fun _ _ _ _ => (IndexCorr.map_cast_rfl _).symm⟩

/-! ### Proposition 14.2.3 -/

/-- **(P4)** (Proposition 14.2.3): for `[d] ≠ [d']` the closures in `𝐗` of `τ_{x,x'}⁻¹([d])` and
`τ_{x,x'}⁻¹([d'])` (preimages in `𝒰(x, x')`) are disjoint. -/
def HasP4 (T : BoundaryStructuredTuple A) : Prop :=
  ∀ (x x' : A.X.PObj.boundary) (d d' : IndexCorr (T.dec.S x).I (T.dec.S x').I), d ≠ d' →
    closure (T.tau.τ x x' ⁻¹' {d} ∩ T.dec.𝒰.mor x x') ∩
      closure (T.tau.τ x x' ⁻¹' {d'} ∩ T.dec.𝒰.mor x x') = ∅

/-- **(P4) persists under shrinking** ("It will persist when we replace these sets by even
smaller ones"). -/
theorem HasP4.restrict {T : BoundaryStructuredTuple A} (hT : T.HasP4)
    (𝒲 : A.X.BoundaryGoodSystem) (h : ∀ x, (𝒲.nbhd x).Le (T.dec.𝒰.nbhd x)) :
    (T.restrict 𝒲 h).HasP4 := fun x x' d d' hd =>
  subset_empty_iff.1 ((inter_subset_inter
    (closure_mono (inter_subset_inter_right _ (BoundaryDecoration.mor_mono h x x')))
    (closure_mono (inter_subset_inter_right _ (BoundaryDecoration.mor_mono h x x')))).trans
    (hT x x' d d' hd).subset)

/-- **2021 Proposition 14.2.3 (Good Structured Version), p. 649 (2017: Proposition 14.2)**: for
tame `X`, every representative `(Λ, 𝒰, S, τ)` of a structured sc⁺-multisection over `∂X` is
equivalent to a representative with the same `Λ`, the same index sets and the same `τ` on a
smaller good system (natural actions restricted), which besides (P1)–(P3) has (P4). -/
theorem proposition_14_2_3 (hX : A.X.IsTame) (T : BoundaryStructuredTuple A) :
    ∃ T' : BoundaryStructuredTuple A, Equiv T T' ∧ T'.Λ = T.Λ ∧
      (∀ x, (T'.dec.𝒰.nbhd x).Le (T.dec.𝒰.nbhd x)) ∧ T'.HasP4 := by
  obtain ⟨𝒲, h𝒲⟩ := lemma_14_2_1_system hX T.dec.𝒰
  refine ⟨T.restrict 𝒲 fun x => (h𝒲 x).1, equiv_restrict T 𝒲 _, rfl, fun x => (h𝒲 x).1,
    fun x x' d d' hd => ?_⟩
  exact lemma_14_2_2 (fun x => (h𝒲 x).2.2.1) (T.tau.locallyConstant x x') hd

/-- **Proposition 14.2.3 for classes**: every structured sc⁺-multisection over `∂X` (tame `X`)
has a representative with (P4). -/
theorem proposition_14_2_3_class (hX : A.X.IsTame) (L : BoundaryStructuredMultisection A) :
    ∃ T : BoundaryStructuredTuple A, (Quotient.mk _ T : BoundaryStructuredMultisection A) = L ∧
      T.HasP4 := by
  induction L using Quotient.inductionOn with
  | h T =>
    obtain ⟨T', hTT', -, -, hP4⟩ := proposition_14_2_3 hX T
    exact ⟨T', Quotient.sound (Setoid.symm hTT'), hP4⟩

end BoundaryStructuredTuple

end SBLocalization

end Polyfold
