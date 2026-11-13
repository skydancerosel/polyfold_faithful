import Polyfold.Chapter16.P3Z_PolyfoldBump
import Polyfold.Chapter7.PartitionsOfUnity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.1: **Proposition 16.1.4 (2)** (p. 708; 2017: Proposition 16.2 (2)) and **Definition
16.1.5 (2)** (p. 708; 2017: Definition 16.4 (2)).  Numbers and pages are the 2021 text's.

# Sc-smooth partitions of unity on polyfolds

## The text, paraphrased

(Proposition 16.1.4 (2)) For equivalent polyfold structures `(X, α)`, `(Y, β)`, `X` admits
sc-smooth partitions of unity (as ep-groupoid, Definition 7.5.5) iff `Y` does.  *Proof*: for a
cover `(U_λ)` of `Y` by saturated open sets take `(V_λ)` with `|f|(|V_λ|) = |U_λ|`, a subordinate
partition `(σ_λ)` on `X`, and `τ_λ(y) = σ_λ(x)` for `|f|(|x|) = |y|`; "an easy exercise" shows
that `(τ_λ)` is an sc-smooth partition of unity subordinate to `(U_λ)`.  (Definition 16.1.5 (2))
A polyfold admits sc-smooth partitions of unity if one (then every) model does.

## What is formalized

* `EpGroupoid.HasOrbitScPartitionsOfUnity` and `hasScPartitionsOfUnity_iff_orbit`: Definition
  7.5.5 is equivalent to: every open cover of `|X|` has a subordinate partition of unity `(σ_λ)`
  of `|X|` with every `σ_λ ∘ π` sc-smooth (the functions of Definition 7.5.5 descend to `|X|`,
  and `σ ∘ π` satisfies all its clauses, `orbitPullback`).
* `EpFunctor.IsEquivalence.isScSmoothMap_comp_π_of_comp_obj`: an orbit-invariant function on `X`
  whose pull-back along an equivalence `F : A → X` is sc-smooth is sc-smooth (local inverses of
  `F` and `ψ̂`) — the text's "easy exercise".
* `EpFunctor.IsEquivalence.hasScPartitionsOfUnity_iff`: invariance under equivalences.
* `PolyfoldStructure.proposition_16_1_4_two` (**Proposition 16.1.4 (2)**),
  `PolyfoldClass.AdmitsScPartitionsOfUnity`, `PolyfoldClass.definition_16_1_5_two`
  (**Definition 16.1.5 (2)**).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v

/-- The pull-back `σ ∘ e` of a partition of unity along a continuous map. -/
def PartitionOfUnity.comapP3Z {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {ι : Type*}
    (e : C(α, β)) (σ : PartitionOfUnity ι β) : PartitionOfUnity ι α where
  toFun i := (σ i).comp e
  locallyFinite' := σ.locallyFinite.preimage_continuous e.continuous
  nonneg' i y := σ.nonneg i (e y)
  sum_eq_one' y _ := σ.sum_eq_one (mem_univ (e y))
  sum_le_one' y := σ.sum_le_one (e y)

theorem PartitionOfUnity.comapP3Z_apply {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {ι : Type*} (e : C(α, β)) (σ : PartitionOfUnity ι β) (i : ι) (y : α) :
    PartitionOfUnity.comapP3Z e σ i y = σ i (e y) := rfl

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- Sc-smooth partitions of unity read on the orbit space: every open cover `(O_λ)` of `|X|` has a
subordinate partition of unity `(σ_λ)` of `|X|` with every `σ_λ ∘ π` sc-smooth. -/
def HasOrbitScPartitionsOfUnity : Prop :=
  ∀ (ι : Type u) (O : ι → Set X.OrbitSpace), (∀ i, IsOpen (O i)) → ⋃ i, O i = univ →
    ∃ σ : PartitionOfUnity ι X.OrbitSpace, σ.IsSubordinate O ∧
      ∀ i, X.PObj.IsScSmoothMap realPolyfold (σ i ∘ X.π)

variable {X}

/-- An invariant continuous function descends to a continuous function on `|X|`. -/
def descendP3Z (f : C(Obj, ℝ)) (hf : ∀ φ, f (X.src φ) = f (X.tgt φ)) : C(X.OrbitSpace, ℝ) where
  toFun := Quotient.lift f fun _ _ ⟨φ, h1, h2⟩ => by rw [← h1, ← h2]; exact hf φ
  continuous_toFun := X.proposition_7_1_8_isOpenQuotientMap.isQuotientMap.continuous_iff.2
    f.continuous

@[simp] theorem descendP3Z_π (f : C(Obj, ℝ)) (hf : ∀ φ, f (X.src φ) = f (X.tgt φ)) (x : Obj) :
    descendP3Z f hf (X.π x) = f x := rfl

/-- `π⁻¹(cl S) = cl(π⁻¹ S)` (`π` is open and continuous). -/
theorem preimage_closure_π (S : Set X.OrbitSpace) : X.π ⁻¹' closure S = closure (X.π ⁻¹' S) :=
  X.proposition_7_1_8.preimage_closure_eq_closure_preimage X.continuous_π S

/-- **Definition 7.5.5 read on the orbit space**: `X` has sc-smooth partitions of unity iff every
open cover of `|X|` has a subordinate partition of unity `(σ_λ)` with all `σ_λ ∘ π` sc-smooth. -/
theorem hasScPartitionsOfUnity_iff_orbit :
    X.HasScPartitionsOfUnity ↔ X.HasOrbitScPartitionsOfUnity := by
  constructor
  · intro h ι O hO hcov
    have hcovU : ⋃ i, X.π ⁻¹' O i = univ := by rw [← preimage_iUnion, hcov, preimage_univ]
    obtain ⟨β, hsub, hsm, hfin, hinv⟩ := h ι (fun i => X.π ⁻¹' O i)
      (fun i => (hO i).preimage X.continuous_π)
      (fun i => by
        change X.π ⁻¹' (X.π '' (X.π ⁻¹' O i)) = X.π ⁻¹' O i
        rw [image_preimage_eq _ X.surjective_π]) hcovU
    let σf : ι → C(X.OrbitSpace, ℝ) := fun i => descendP3Z (β i) (hinv i)
    have hsupp : ∀ i, X.π ⁻¹' support (σf i) = support (β i) := fun i => rfl
    refine ⟨{ toFun := σf
              locallyFinite' := fun q => ?_
              nonneg' := fun i q => ?_
              sum_eq_one' := fun q _ => ?_
              sum_le_one' := fun q => ?_ }, fun i => ?_, fun i => hsm i⟩
    · obtain ⟨x, rfl⟩ := X.surjective_π q
      obtain ⟨W, hWo, -, hxW, hWfin⟩ := hfin x
      refine ⟨X.π '' W, (X.proposition_7_1_8 W hWo).mem_nhds ⟨x, hxW, rfl⟩,
        hWfin.subset fun i hi => ?_⟩
      obtain ⟨_, hs, ⟨w, hwW, rfl⟩⟩ := hi
      exact ⟨w, hwW, subset_tsupport _ hs⟩
    · obtain ⟨x, rfl⟩ := X.surjective_π q
      exact β.nonneg i x
    · obtain ⟨x, rfl⟩ := X.surjective_π q
      exact β.sum_eq_one (mem_univ x)
    · obtain ⟨x, rfl⟩ := X.surjective_π q
      exact β.sum_le_one x
    · intro q hq
      obtain ⟨x, rfl⟩ := X.surjective_π q
      have hx : x ∈ X.π ⁻¹' closure (support (σf i)) := hq
      rw [preimage_closure_π, hsupp] at hx
      exact hsub i hx
  · intro h ι U hUo hUs hcov
    have hcovO : ⋃ i, X.π '' U i = univ := by
      rw [← image_iUnion, hcov, image_univ_of_surjective X.surjective_π]
    obtain ⟨σ, hσ, hsm⟩ := h ι (fun i => X.π '' U i) (fun i => X.proposition_7_1_8 _ (hUo i))
      hcovO
    exact ⟨X.orbitPullback σ, X.orbitPullback_isSubordinate hσ hUs, hsm,
      X.exists_isSaturated_nhds_finite_orbitPullback σ, X.orbitPullback_src σ⟩

end EpGroupoid

namespace EpFunctor.IsEquivalence

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {A : EpGroupoid Obj Mor} {X : EpGroupoid Obj' Mor'} {F : EpFunctor A X}

/-- **The "easy exercise" of the proof of Proposition 16.1.4 (2)**: for an equivalence
`F : A → X` and `g : |X| → ℝ`, if `g ∘ π_X ∘ F` is sc-smooth then so is `g ∘ π_X` (near `F(a)`
through a local inverse of `F`; near `y ≅ F(a)` through `ψ̂`). -/
theorem isScSmoothMap_comp_π_of_comp_obj (hF : F.IsEquivalence) {g : X.OrbitSpace → ℝ}
    (hg : A.PObj.IsScSmoothMap realPolyfold (g ∘ X.π ∘ F.obj)) :
    X.PObj.IsScSmoothMap realPolyfold (g ∘ X.π) := by
  refine MPolyfold.isScSmoothMap_real_of_locally fun y => ?_
  obtain ⟨a, ψ, hs, ht⟩ := hF.exists_iso y
  obtain ⟨U, V, k, haU, hd⟩ := hF.isLocalScDiffeo_obj a
  -- near `F a`: `g ∘ π = (g ∘ π ∘ F) ∘ k`
  have hV : X.PObj.IsScSmoothOn realPolyfold (g ∘ X.π) V := by
    refine (MPolyfold.IsScSmoothOn.comp hg hd.isScSmoothOn_inv (mapsTo_univ _ _)).congr
      fun v hv => ?_
    simp only [Function.comp_apply, hd.right_inv v hv]
  -- near `y = t ψ`: `g ∘ π = (g ∘ π) ∘ (s ∘ gt)`
  obtain ⟨W, Vs, Vt, gs, gt, hψW, hsd, htd, hhat, -⟩ :=
    X.isLocalScDiffeo_src.exists_isScDiffeoOn_hat X.isLocalScDiffeo_tgt ψ
  have hinv := hhat.symm
  set O := Vt ∩ (X.src ∘ gt) ⁻¹' V with hO
  have hOo : IsOpen O :=
    hinv.isScSmoothOn.continuousOn.isOpen_inter_preimage hinv.isOpen_source hd.isOpen_target
  have hyO : y ∈ O := by
    refine ⟨ht ▸ htd.mapsTo hψW, ?_⟩
    rw [← ht, mem_preimage, Function.comp_apply, htd.left_inv ψ hψW, hs]
    exact hd.mapsTo haU
  refine ⟨O, hOo, hyO, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp hV (hinv.isScSmoothOn.mono hOo inter_subset_left)
    fun z hz => hz.2).congr fun z hz => ?_
  simp only [Function.comp_apply]
  rw [X.π_src_eq_π_tgt, htd.right_inv z hz.1]

/-- **Sc-smooth partitions of unity along an equivalence** (the proof of Proposition 16.1.4
(2)): for an equivalence `F : A → X` of ep-groupoids in one universe, `A` has sc-smooth partitions
of unity (Definition 7.5.5) iff `X` has. -/
theorem hasScPartitionsOfUnity_iff {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj]
    [T2Space Obj] [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor]
    [ParacompactSpace Mor] [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {A : EpGroupoid Obj Mor}
    {X : EpGroupoid Obj' Mor'} {F : EpFunctor A X} (hF : F.IsEquivalence) :
    A.HasScPartitionsOfUnity ↔ X.HasScPartitionsOfUnity := by
  rw [EpGroupoid.hasScPartitionsOfUnity_iff_orbit, EpGroupoid.hasScPartitionsOfUnity_iff_orbit]
  set e : A.OrbitSpace ≃ₜ X.OrbitSpace := hF.isHomeomorph_orbitMap.homeomorph _ with he
  have heπ : ∀ a, e (A.π a) = X.π (F.obj a) := fun a => GroupoidFunctor.orbitMap_π _ a
  -- the two smoothness conditions correspond
  have hsm : ∀ g : X.OrbitSpace → ℝ, A.PObj.IsScSmoothMap realPolyfold (g ∘ e ∘ A.π) ↔
      X.PObj.IsScSmoothMap realPolyfold (g ∘ X.π) := fun g => by
    have h1 : g ∘ e ∘ A.π = g ∘ X.π ∘ F.obj := funext fun a => by
      simp only [Function.comp_apply, heπ]
    rw [h1]
    exact ⟨hF.isScSmoothMap_comp_π_of_comp_obj, fun h =>
      MPolyfold.IsScSmoothMap.comp (g := g ∘ X.π) h F.isScSmoothMap_obj⟩
  constructor
  · intro h ι O hO hcov
    have hcov' : ⋃ i, e ⁻¹' O i = univ := by rw [← preimage_iUnion, hcov, preimage_univ]
    obtain ⟨σ', hσ', hsm'⟩ := h ι (fun i => e ⁻¹' O i) (fun i => (hO i).preimage e.continuous)
      hcov'
    refine ⟨PartitionOfUnity.comapP3Z ⟨⇑e.symm, e.symm.continuous⟩ σ', fun i => ?_, fun i => ?_⟩
    · refine (tsupport_comp_subset_preimage (σ' i) e.symm.continuous).trans fun q hq => ?_
      have := hσ' i hq
      rwa [mem_preimage, Homeomorph.apply_symm_apply] at this
    · refine (hsm _).1 ?_
      have e1 : (⇑(PartitionOfUnity.comapP3Z ⟨⇑e.symm, e.symm.continuous⟩ σ' i) ∘ ⇑e ∘ A.π) =
          σ' i ∘ A.π := funext fun a => by
        simp only [Function.comp_apply, PartitionOfUnity.comapP3Z_apply,
          ContinuousMap.coe_mk, Homeomorph.symm_apply_apply]
      rw [e1]
      exact hsm' i
  · intro h ι O hO hcov
    have hcov' : ⋃ i, e.symm ⁻¹' O i = univ := by rw [← preimage_iUnion, hcov, preimage_univ]
    obtain ⟨σ, hσ, hsmX⟩ := h ι (fun i => e.symm ⁻¹' O i)
      (fun i => (hO i).preimage e.symm.continuous) hcov'
    refine ⟨PartitionOfUnity.comapP3Z ⟨⇑e, e.continuous⟩ σ, fun i => ?_, fun i => ?_⟩
    · refine (tsupport_comp_subset_preimage (σ i) e.continuous).trans fun q hq => ?_
      have := hσ i hq
      rwa [mem_preimage, Homeomorph.symm_apply_apply] at this
    · exact (hsm (σ i)).2 (hsmX i)

end EpFunctor.IsEquivalence

namespace PolyfoldStructure

variable {Z : Type u} [TopologicalSpace Z]

/-- **2021 Proposition 16.1.4 (2), p. 708 (2017: Proposition 16.2 (2))**: for equivalent polyfold
structures `(X, α)`, `(Y, β)`, `X` admits sc-smooth partitions of unity as an ep-groupoid
(Definition 7.5.5) iff `Y` does. -/
theorem proposition_16_1_4_two {p q : PolyfoldStructure Z} (h : Equiv p q) :
    p.X.X.HasScPartitionsOfUnity ↔ q.X.X.HasScPartitionsOfUnity := by
  obtain ⟨f, hf, -⟩ := h
  exact EPLocalization.EPLoc.iff_of_isGeneralizedIso (fun B => B.X.HasScPartitionsOfUnity)
    (fun _ hF => EpFunctor.IsEquivalence.hasScPartitionsOfUnity_iff hF) hf

/-- **2021 Proposition 16.1.4, p. 708**, both parts. -/
theorem proposition_16_1_4 {p q : PolyfoldStructure Z} (h : Equiv p q) :
    (p.X.X.PObj.AdmitsBumpFunctions ↔ q.X.X.PObj.AdmitsBumpFunctions) ∧
      (p.X.X.HasScPartitionsOfUnity ↔ q.X.X.HasScPartitionsOfUnity) :=
  ⟨proposition_16_1_4_one h, proposition_16_1_4_two h⟩

end PolyfoldStructure

namespace PolyfoldClass

variable {Z : Type u} [TopologicalSpace Z]

/-- **2021 Definition 16.1.5 (2), p. 708 (2017: Definition 16.4 (2))**: the polyfold `(Z, c)`
**admits sc-smooth partitions of unity** if some model `(X, α) ∈ c` does (Definition 7.5.5). -/
def AdmitsScPartitionsOfUnity (c : PolyfoldClass Z) : Prop :=
  ∃ p : PolyfoldStructure Z, ⟦p⟧ = c ∧ p.X.X.HasScPartitionsOfUnity

/-- **Definition 16.1.5 (2)**, "then this is true for the other models in `c` as well"
(Proposition 16.1.4 (2)). -/
theorem definition_16_1_5_two (c : PolyfoldClass Z) :
    c.AdmitsScPartitionsOfUnity ↔
      ∀ p : PolyfoldStructure Z, ⟦p⟧ = c → p.X.X.HasScPartitionsOfUnity := by
  refine ⟨fun ⟨p, hp, hX⟩ q hq => ?_, fun h => ?_⟩
  · exact (PolyfoldStructure.proposition_16_1_4_two (Quotient.exact (hp.trans hq.symm))).1 hX
  · obtain ⟨p, rfl⟩ := Quotient.exists_rep c
    exact ⟨p, rfl, h p rfl⟩

end PolyfoldClass

end Polyfold
