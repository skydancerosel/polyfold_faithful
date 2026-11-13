import Polyfold.Chapter16.PolyfoldStructure
import Polyfold.Chapter5.BumpWeakPointwise

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.1: **Proposition 16.1.4 (1)** (p. 708; 2017: Proposition 16.2 (1)) and **Definition
16.1.5 (1)** (p. 708; 2017: Definition 16.4 (1)).  Numbers and pages are the 2021 text's.

# Sc-smooth bump functions on polyfolds

## The text, paraphrased

(Proposition 16.1.4 (1)) For equivalent polyfold structures `(X, α)`, `(Y, β)`, `X` admits
sc-smooth bump functions iff `Y` does.  *Proof*: represent the generalized isomorphism by
`X ←F A →G Y`; `F` is a local sc-diffeomorphism, so `A` has bump functions; so does `G(A)`; at
`y ∉ G(A)` use a morphism `ψ : G(a) → y` and its local sc-diffeomorphism `ψ̂`.
(Definition 16.1.5 (1)) The polyfold `(Z, c)` admits sc-smooth bump functions if some `(X, α) ∈ c`
does; then every structure in `c` does.

## What is formalized

* `MPolyfold.IsScDiffeoOn.hasBumpAt`: a bump point is carried back along an sc-diffeomorphism of
  open sets (cut-off and extension by zero).
* `EpFunctor.IsEquivalence.admitsBumpFunctions_iff`: for an equivalence `F : A → X` the object
  M-polyfolds of `A` and `X` admit sc-smooth bump functions together (`F` local sc-diffeomorphism;
  essential surjectivity and `ψ̂`).
* `PolyfoldStructure.proposition_16_1_4_one` (**Proposition 16.1.4 (1)**) and
  `PolyfoldClass.AdmitsBumpFunctions`, `PolyfoldClass.definition_16_1_5_one`
  (**Definition 16.1.5 (1)**, "then also the others").

## Reading

* "`X` admits sc-smooth bump functions" is read for the object M-polyfold (Definition 5.3.1,
  `MPolyfold.AdmitsBumpFunctions`, the reading `f(x) ≠ 0`), which is what the proof uses ("an
  sc-smooth bump function in every open set").  The ep-groupoid notion of Definition 12.3.1 is
  equivalent to it by Theorem 12.3.2 (1) (wave-1 block S).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- Sc-smoothness of a real function is local. -/
theorem isScSmoothMap_real_of_locally {f : X → ℝ}
    (h : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ P.IsScSmoothOn realPolyfold f U) :
    P.IsScSmoothMap realPolyfold f := by
  have hcont : ContinuousOn f univ := fun x _ => by
    obtain ⟨U', hU', hxU', hf⟩ := h x
    exact (hf.continuousOn.continuousAt (hU'.mem_nhds hxU')).continuousWithinAt
  refine IsScSmoothOn.of_exists_charts isOpen_univ hcont fun x _ => ?_
  obtain ⟨U', hU', hxU', hf⟩ := h x
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  obtain ⟨ψ, hψ, hfx⟩ := realPolyfold.exists_isChart_mem_source (f x)
  set V := (U' ∩ φ.source) ∩ f ⁻¹' ψ.source with hV
  have hVo : IsOpen V := (hf.continuousOn.mono inter_subset_left).isOpen_inter_preimage
    (hU'.inter φ.isOpen_source) ψ.isOpen_source
  exact ⟨φ, ψ, V, hφ, hψ, hVo, ⟨⟨hxU', hxφ⟩, hfx⟩, fun y hy => ⟨mem_univ _, hy.1.2⟩,
    fun y hy => hy.2, hf.smooth φ ψ hφ hψ V hVo (fun y hy => hy.1) fun y hy => hy.2⟩

/-- **A bump point is carried back along an sc-diffeomorphism of open sets**: if
`φ : V → W` is an sc-diffeomorphism, `x ∈ V`, and `φ(x)` is a bump point of `Y`, then `x` is a
bump point of `X` (the bump `g ∘ φ` on a small neighbourhood, extended by `0`). -/
theorem IsScDiffeoOn.hasBumpAt {φ : X → Y} {ψ : Y → X} {V : Set X} {W : Set Y}
    (hd : P.IsScDiffeoOn Q φ ψ V W) {x : X} (hx : x ∈ V) (hb : Q.HasBumpAt (φ x)) :
    P.HasBumpAt x := by
  intro U hU hxU
  obtain ⟨t, ht, htc, htsub⟩ :=
    exists_mem_nhds_isClosed_subset ((hU.inter hd.isOpen_source).mem_nhds ⟨hxU, hx⟩)
  set N := interior t with hNdef
  have hxN : x ∈ N := mem_interior_iff_mem_nhds.2 ht
  have hNcl : closure N ⊆ U ∩ V := (closure_minimal interior_subset htc).trans htsub
  have hNV : N ⊆ V := subset_closure.trans (hNcl.trans inter_subset_right)
  have hdN := hd.restrict _root_.isOpen_interior hNV
  have hφN : IsOpen (φ '' N) := by rw [hdN.image_eq]; exact hdN.isOpen_target
  obtain ⟨g, hg, hgx, hgsupp⟩ := hb (φ '' N) hφN ⟨x, hxN, rfl⟩
  set f : X → ℝ := V.indicator (g ∘ φ) with hfdef
  have hsupp : support f ⊆ N := by
    intro y hy
    have hyV : y ∈ V := by
      by_contra hyV; exact hy (indicator_of_notMem hyV _)
    have hgy : g (φ y) ≠ 0 := by
      have := mem_support.1 hy; rwa [hfdef, indicator_of_mem hyV] at this
    obtain ⟨n, hn, hny⟩ := hgsupp (subset_tsupport g (mem_support.2 hgy))
    rwa [hd.injOn (hNV hn) hyV hny] at hn
  have htsupp : tsupport f ⊆ U ∩ V := (closure_mono hsupp).trans hNcl
  refine ⟨f, isScSmoothMap_real_of_locally fun y => ?_, ?_, htsupp.trans inter_subset_left⟩
  · by_cases hy : y ∈ V
    · refine ⟨V, hd.isOpen_source, hy, ?_⟩
      refine (IsScSmoothOn.comp hg hd.isScSmoothOn (mapsTo_univ _ _)).congr fun z hz => ?_
      simp only [hfdef, indicator_of_mem hz]
    · have hyt : y ∉ tsupport f := fun h => hy (htsupp h).2
      refine ⟨(tsupport f)ᶜ, (isClosed_tsupport f).isOpen_compl, hyt, ?_⟩
      refine ((isScSmoothMap_real_const (PX := P) 0).mono (isClosed_tsupport f).isOpen_compl
        (subset_univ _)).congr fun z hz => ?_
      exact (image_eq_zero_of_notMem_tsupport hz).symm
  · simp only [hfdef, indicator_of_mem hx, Function.comp_apply]
    exact hgx

end MPolyfold

namespace EpFunctor.IsEquivalence

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {A : EpGroupoid Obj Mor} {X : EpGroupoid Obj' Mor'} {F : EpFunctor A X}

/-- Bump points pass from `F(a)` to `a` (`F` is a local sc-diffeomorphism on objects). -/
theorem hasBumpAt_of_hasBumpAt_obj (hF : F.IsEquivalence) (a : Obj)
    (h : X.PObj.HasBumpAt (F.obj a)) : A.PObj.HasBumpAt a := by
  obtain ⟨U, V, g, haU, hd⟩ := hF.isLocalScDiffeo_obj a
  exact hd.hasBumpAt haU h

/-- Bump points pass from `a` to `F(a)`. -/
theorem hasBumpAt_obj_of_hasBumpAt (hF : F.IsEquivalence) (a : Obj)
    (h : A.PObj.HasBumpAt a) : X.PObj.HasBumpAt (F.obj a) := by
  obtain ⟨U, V, g, haU, hd⟩ := hF.isLocalScDiffeo_obj a
  have hFa : F.obj a ∈ V := hd.mapsTo haU
  refine hd.symm.hasBumpAt hFa ?_
  rwa [hd.left_inv a haU]

/-- Bump points of `X` are invariant under isomorphism (`ψ̂ = t ∘ (s|U(ψ))⁻¹`). -/
theorem _root_.Polyfold.EpGroupoid.hasBumpAt_tgt (X : EpGroupoid Obj' Mor') (ψ : Mor')
    (h : X.PObj.HasBumpAt (X.src ψ)) : X.PObj.HasBumpAt (X.tgt ψ) := by
  obtain ⟨U, Vs, Vt, gs, gt, hψU, hs, ht, hhat, hval⟩ :=
    X.isLocalScDiffeo_src.exists_isScDiffeoOn_hat X.isLocalScDiffeo_tgt ψ
  have hmem : X.tgt ψ ∈ Vt := ht.mapsTo hψU
  refine hhat.symm.hasBumpAt hmem ?_
  have e : (X.src ∘ gt) (X.tgt ψ) = X.src ψ := by
    simp only [Function.comp_apply, ht.left_inv ψ hψU]
  rwa [e]

/-- **Bump functions along an equivalence**: for an equivalence `F : A → X` of ep-groupoids, the
object M-polyfold of `A` admits sc-smooth bump functions iff that of `X` does (the proof of
Proposition 16.1.4 (1)). -/
theorem admitsBumpFunctions_iff (hF : F.IsEquivalence) :
    A.PObj.AdmitsBumpFunctions ↔ X.PObj.AdmitsBumpFunctions := by
  rw [MPolyfold.admitsBumpFunctions_iff_forall_hasBumpAt,
    MPolyfold.admitsBumpFunctions_iff_forall_hasBumpAt]
  refine ⟨fun h x => ?_, fun h a => hF.hasBumpAt_of_hasBumpAt_obj a (h _)⟩
  obtain ⟨a, ψ, hs, ht⟩ := hF.exists_iso x
  have h1 := hF.hasBumpAt_obj_of_hasBumpAt a (h a)
  rw [← hs] at h1
  have h2 := X.hasBumpAt_tgt ψ h1
  rwa [ht] at h2

end EpFunctor.IsEquivalence

namespace PolyfoldStructure

variable {Z : Type u} [TopologicalSpace Z]

/-- **2021 Proposition 16.1.4 (1), p. 708 (2017: Proposition 16.2 (1))**: for equivalent polyfold
structures `(X, α)`, `(Y, β)`, `X` admits sc-smooth bump functions iff `Y` does (object
M-polyfolds, Definition 5.3.1). -/
theorem proposition_16_1_4_one {p q : PolyfoldStructure Z} (h : Equiv p q) :
    p.X.X.PObj.AdmitsBumpFunctions ↔ q.X.X.PObj.AdmitsBumpFunctions := by
  obtain ⟨f, hf, -⟩ := h
  exact EPLocalization.EPLoc.iff_of_isGeneralizedIso (fun B => B.X.PObj.AdmitsBumpFunctions)
    (fun _ hF => hF.admitsBumpFunctions_iff) hf

end PolyfoldStructure

namespace PolyfoldClass

variable {Z : Type u} [TopologicalSpace Z]

/-- **2021 Definition 16.1.5 (1), p. 708 (2017: Definition 16.4 (1))**: the polyfold `(Z, c)`
**admits sc-smooth bump functions** if some structure `(X, α) ∈ c` does. -/
def AdmitsBumpFunctions (c : PolyfoldClass Z) : Prop :=
  ∃ p : PolyfoldStructure Z, ⟦p⟧ = c ∧ p.X.X.PObj.AdmitsBumpFunctions

/-- **Definition 16.1.5 (1)**, "the equivalent polyfold structures will also have this property"
(Proposition 16.1.4 (1)). -/
theorem definition_16_1_5_one (c : PolyfoldClass Z) :
    c.AdmitsBumpFunctions ↔
      ∀ p : PolyfoldStructure Z, ⟦p⟧ = c → p.X.X.PObj.AdmitsBumpFunctions := by
  refine ⟨fun ⟨p, hp, hX⟩ q hq => ?_, fun h => ?_⟩
  · exact (PolyfoldStructure.proposition_16_1_4_one (Quotient.exact (hp.trans hq.symm))).1 hX
  · obtain ⟨p, rfl⟩ := Quotient.exists_rep c
    exact ⟨p, rfl, h p rfl⟩

end PolyfoldClass

end Polyfold
