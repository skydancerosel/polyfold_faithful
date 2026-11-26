import GWMemoir.Skeleton
import Polyfold.Chapter12.RestrictionLocalIso
import Polyfold.Chapter8.TangentLocal

/-!
# Memoir Theorem 3.13 gives transition data

Hofer–Wysocki–Zehnder, *Applications of Polyfold Theory I: The Polyfolds of Gromov–Witten
Theory*, §3.2 (pp. 73–79), read against the Properties (19.3) (A)–(F) of the 2021 book
(`UniformizerConstruction.TransitionData`).

`GWMemoir.Skeleton` states Theorem 3.13 (existence and uniqueness of the germ `Φ` of a transition
through a morphism `h`) as `Theorem_3_13 U CS`, and the reduction as `Reduction_3_13 U CS`:
`Theorem_3_13 U CS → Nonempty U.TransitionData`.

## What is proved

* `GWMemoir.reduction_3_13`: Theorem 3.13 together with three conditions on the data gives
  transition data.  The conditions are
  - `CSClosed U CS`: the core-smoothness predicate `CS` holds for the maps `q ↦ Ψ̂(g, q)`, and is
    stable under translation by `G'`, inversion and composition of germs;
  - `PointFinite U`: for every `Ψ` and `o ∈ O`, only finitely many `Ψ'` in the family carry a
    morphism out of `Ψ(o)`.
  The M-polyfolds `O` are metrizable (Theorem 2.3.10), so no paracompactness hypothesis is needed
  beyond the one in the definition of a uniformizer.
* `GWMemoir.reduction_3_13_skeleton`: the same conclusion for `Theorem_3_13 U CS` of
  `GWMemoir.Skeleton` (universe `1`).
* The construction follows the memoir: for each pair `Ψ, Ψ'` a locally finite family of closed
  sets `K_i` inside the domains `V_i` of chosen germs (precise refinement and shrinking in the
  open set of sources); `F_h` is the chart through `s(h)` translated by the unique `g' ∈ G'`
  hitting `h` (Proposition 3.12); `V(o)` is the interior of the set where the finitely many
  relevant germs agree (uniqueness in Theorem 3.13).

## Readings

* The form in `GWMemoir.Skeleton` quantifies over an arbitrary predicate `CS`.  The properties
  (B)–(E) compare germs obtained by translating, inverting and composing germs; uniqueness in
  Theorem 3.13 applies to them only when they again satisfy `CS`.  The memoir uses that inverses
  and composites of core-smooth families of isomorphisms are core-smooth; this is `CSClosed`.
* (E) is required on the whole set `W(o) ∩ V̂(o)`, for all `Ψ''`.  Agreement of germs is a
  statement near `o`, so `V(o)` is cut down by the condition for every `h' : Ψ'(f_h(o)) → Ψ''(·)`;
  there are finitely many such `h'` for each `Ψ''` (2021 p. 749), and `PointFinite` makes the
  `Ψ''` finitely many.  It holds for the translation-groupoid witness
  (`GWMemoir.pointFinite_translationUnif`); for the GW family it asks that the family of
  uniformizers be chosen locally finite.
* (F) needs no separation property of `Z`: two morphisms with the same source are translates of
  each other by an element `g' ≠ 1` (Proposition 3.12, `Uniformizer.fiberEquiv`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter
open Polyfold Polyfold.GroupoidalCategory

noncomputable section

namespace GWMemoir

universe u

open GroupoidStr (TransitionSet)

variable {C : GroupoidalCategory.{u}} (U : C.UniformizerConstruction)

/-- The type of core-smoothness predicates `CS Ψ Ψ' Φ V` (Skeleton's `CS`). -/
abbrev CSPred : Type (u + 1) :=
  ∀ Ψ Ψ' : U.Unif, (Ψ.1.O → Ψ.1.Trans Ψ'.1) → Set Ψ.1.O → Prop

/-- `Φ : V → M(Ψ, Ψ')` is a transition germ at `h` (Skeleton's `IsTransGerm`, at any universe). -/
def TransGerm (CS : CSPred U) (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) (V : Set Ψ.1.O)
    (Φ : Ψ.1.O → Ψ.1.Trans Ψ'.1) : Prop :=
  IsOpen V ∧ h.src ∈ V ∧ Φ h.src = h ∧ (∀ q ∈ V, (Φ q).src = q) ∧
    (∃ g, Ψ.1.P.IsScDiffeoOn Ψ'.1.P (fun q => (Φ q).tgt) g V ((fun q => (Φ q).tgt) '' V)) ∧
    CS Ψ Ψ' Φ V

/-- **Memoir Theorem 3.13, p. 70** (Skeleton's `Theorem_3_13`, at any universe). -/
def Thm313 (CS : CSPred U) : Prop :=
  ∀ (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1),
    (∃ V Φ, TransGerm U CS Ψ Ψ' h V Φ) ∧
    ∀ V₁ Φ₁ V₂ Φ₂, TransGerm U CS Ψ Ψ' h V₁ Φ₁ → TransGerm U CS Ψ Ψ' h V₂ Φ₂ →
      ∃ W : Set Ψ.1.O, IsOpen W ∧ h.src ∈ W ∧ W ⊆ V₁ ∩ V₂ ∧ EqOn Φ₁ Φ₂ W

theorem theorem_3_13_iff {C : GroupoidalCategory.{1}} (U : C.UniformizerConstruction)
    (CS : CSPred U) : Theorem_3_13 U CS ↔ Thm313 U CS := Iff.rfl

/-! ### Translation by `G'` (Proposition 3.12) -/

section Transl

variable {C' : GroupoidalCategory.{u}} {Ψ Ψ' : C'.Uniformizer}

/-- `(q, φ, q') ↦ (q, Ψ'(g', q') ∘ φ, g' ∗ q')`. -/
def transl (g : Ψ'.G) (a : Ψ.Trans Ψ') : Ψ.Trans Ψ' := ((Ψ.fiberEquiv a) g).1

@[simp] theorem transl_src (g : Ψ'.G) (a : Ψ.Trans Ψ') : (transl g a).src = a.src := rfl

@[simp] theorem transl_tgt (g : Ψ'.G) (a : Ψ.Trans Ψ') : (transl g a).tgt = g • a.tgt := rfl

theorem transl_injective (a : Ψ.Trans Ψ') : Injective fun g : Ψ'.G => transl g a :=
  fun _ _ h => (Ψ.fiberEquiv a).injective (Subtype.ext h)

theorem exists_transl {a b : Ψ.Trans Ψ'} (h : b.src = a.src) : ∃ g, transl g a = b :=
  let ⟨g, hg⟩ := (Ψ.fiberEquiv a).surjective ⟨b, h⟩
  ⟨g, congrArg Subtype.val hg⟩

theorem transl_one (a : Ψ.Trans Ψ') : transl 1 a = a := by
  refine GroupoidStr.TransitionSet.ext (x := transl 1 a) (y := a) rfl ?_ (one_smul _ _)
  change C'.toGroupoidStr.comp (Ψ'.mor (1, a.tgt)) a.mor = a.mor
  have e : Ψ'.mor (1, a.tgt) = C'.toGroupoidStr.unit (Ψ'.obj a.tgt) :=
    congrArg GroupoidStr.TransitionSet.mor (Ψ'.hat_one a.tgt)
  rw [e]
  exact GroupoidStr.unit_comp_of_eq a.tgt_mor

end Transl

/-- The composite germ `q ↦ Φ'(f(q)) ∘ Φ(q)` (with a junk value where it is not composable). -/
def compGerm {Ψ Ψ' Ψ'' : U.Unif} (Φ' : Ψ'.1.O → Ψ'.1.Trans Ψ''.1) (Φ : Ψ.1.O → Ψ.1.Trans Ψ'.1)
    (d : Ψ.1.Trans Ψ''.1) (q : Ψ.1.O) : Ψ.1.Trans Ψ''.1 := by
  classical
  exact if hc : C.toGroupoidStr.src (Φ' (Φ q).tgt).mor = C.toGroupoidStr.tgt (Φ q).mor then
    TransitionSet.comp (Φ' (Φ q).tgt) (Φ q) hc else d

theorem compGerm_eq {Ψ Ψ' Ψ'' : U.Unif} (Φ' : Ψ'.1.O → Ψ'.1.Trans Ψ''.1)
    (Φ : Ψ.1.O → Ψ.1.Trans Ψ'.1) (d : Ψ.1.Trans Ψ''.1) (q : Ψ.1.O)
    (hc : C.toGroupoidStr.src (Φ' (Φ q).tgt).mor = C.toGroupoidStr.tgt (Φ q).mor) :
    compGerm U Φ' Φ d q = TransitionSet.comp (Φ' (Φ q).tgt) (Φ q) hc := by
  simp only [compGerm, dif_pos hc]

/-- The inverse germ `p ↦ Φ(f⁻¹(p))⁻¹`. -/
def invGerm {Ψ Ψ' : U.Unif} (Φ : Ψ.1.O → Ψ.1.Trans Ψ'.1) (ginv : Ψ'.1.O → Ψ.1.O) (p : Ψ'.1.O) :
    Ψ'.1.Trans Ψ.1 := (Φ (ginv p)).inv

/-- **Closure properties of core-smoothness** used with the uniqueness of Theorem 3.13: the
families `q ↦ Ψ̂(g, q)` are core-smooth, and core-smoothness is stable under translation by `G'`
(Proposition 3.12), inversion and composition. -/
structure CSClosed (CS : CSPred U) : Prop where
  hat : ∀ (Ψ : U.Unif) (g : Ψ.1.G), CS Ψ Ψ (fun q => Ψ.1.hat (g, q)) univ
  transl : ∀ (Ψ Ψ' : U.Unif) (Φ : Ψ.1.O → Ψ.1.Trans Ψ'.1) (V : Set Ψ.1.O) (g : Ψ'.1.G),
    CS Ψ Ψ' Φ V → CS Ψ Ψ' (fun q => transl g (Φ q)) V
  inv : ∀ (Ψ Ψ' : U.Unif) (Φ : Ψ.1.O → Ψ.1.Trans Ψ'.1) (V : Set Ψ.1.O) (ginv : Ψ'.1.O → Ψ.1.O),
    CS Ψ Ψ' Φ V → IsOpen V → (∀ q ∈ V, (Φ q).src = q) →
    Ψ.1.P.IsScDiffeoOn Ψ'.1.P (fun q => (Φ q).tgt) ginv V ((fun q => (Φ q).tgt) '' V) →
    CS Ψ' Ψ (invGerm U Φ ginv) ((fun q => (Φ q).tgt) '' V)
  comp : ∀ (Ψ Ψ' Ψ'' : U.Unif) (Φ : Ψ.1.O → Ψ.1.Trans Ψ'.1) (Φ' : Ψ'.1.O → Ψ'.1.Trans Ψ''.1)
    (V : Set Ψ.1.O) (V' : Set Ψ'.1.O) (d : Ψ.1.Trans Ψ''.1),
    CS Ψ Ψ' Φ V → CS Ψ' Ψ'' Φ' V' → IsOpen V → IsOpen V' → (∀ q ∈ V, (Φ q).src = q) →
    (∀ q ∈ V', (Φ' q).src = q) → ContinuousOn (fun q => (Φ q).tgt) V →
    CS Ψ Ψ'' (compGerm U Φ' Φ d) (V ∩ (fun q => (Φ q).tgt) ⁻¹' V')

/-- **Point-finiteness of the family**: for every `Ψ` and `o ∈ O`, only finitely many `Ψ'`
carry a morphism out of `Ψ(o)`. -/
def PointFinite : Prop :=
  ∀ (Ψ : U.Unif) (o : Ψ.1.O), {Ψ' : U.Unif | ∃ e : Ψ.1.Trans Ψ'.1, e.src = o}.Finite

variable {U}

/-! ### Operations on germs -/

section Germs

variable {CS : CSPred U}

theorem TransGerm.isOpen {Ψ Ψ' : U.Unif} {h : Ψ.1.Trans Ψ'.1} {V Φ}
    (hg : TransGerm U CS Ψ Ψ' h V Φ) : IsOpen V := hg.1

/-- A germ at `h` is a germ at each of its values. -/
theorem TransGerm.atPt {Ψ Ψ' : U.Unif} {h : Ψ.1.Trans Ψ'.1} {V Φ}
    (hg : TransGerm U CS Ψ Ψ' h V Φ) {q : Ψ.1.O} (hq : q ∈ V) :
    TransGerm U CS Ψ Ψ' (Φ q) V Φ := by
  obtain ⟨h1, -, -, h4, h5, h6⟩ := hg
  refine ⟨h1, ?_, ?_, h4, h5, h6⟩
  · rw [h4 q hq]; exact hq
  · rw [h4 q hq]

theorem TransGerm.continuousOn {Ψ Ψ' : U.Unif} {h : Ψ.1.Trans Ψ'.1} {V Φ}
    (hg : TransGerm U CS Ψ Ψ' h V Φ) : ContinuousOn (fun q => (Φ q).tgt) V :=
  hg.2.2.2.2.1.choose_spec.isScSmoothOn.continuousOn

theorem TransGerm.translate (hCS : CSClosed U CS) {Ψ Ψ' : U.Unif} {h : Ψ.1.Trans Ψ'.1} {V Φ}
    (hg : TransGerm U CS Ψ Ψ' h V Φ) (g : Ψ'.1.G) :
    TransGerm U CS Ψ Ψ' (transl g h) V (fun q => transl g (Φ q)) := by
  obtain ⟨h1, h2, h3, h4, ⟨k, hk⟩, h6⟩ := hg
  refine ⟨h1, h2, by simp only [transl_src, h3], fun q hq => h4 q hq, ?_,
    hCS.transl _ _ _ _ g h6⟩
  have hs : Ψ'.1.P.IsScDiffeoOn Ψ'.1.P (fun y => g • y) (fun y => g⁻¹ • y) univ univ :=
    ⟨Ψ'.1.smooth_smul g, Ψ'.1.smooth_smul g⁻¹, mapsTo_univ _ _, mapsTo_univ _ _,
      fun y _ => inv_smul_smul g y, fun y _ => smul_inv_smul g y⟩
  have hs' := hs.restrict hk.isOpen_target (subset_univ _)
  have hc := hs'.comp hk
  refine ⟨k ∘ fun y => g⁻¹ • y, ?_⟩
  have he : (fun q => (transl g (Φ q)).tgt) = (fun y => g • y) ∘ fun q => (Φ q).tgt := rfl
  rw [he]
  rw [← hc.image_eq] at hc
  exact hc

theorem TransGerm.inv (hCS : CSClosed U CS) {Ψ Ψ' : U.Unif} {h : Ψ.1.Trans Ψ'.1} {V Φ}
    (hg : TransGerm U CS Ψ Ψ' h V Φ) :
    ∃ ginv, TransGerm U CS Ψ' Ψ h.inv ((fun q => (Φ q).tgt) '' V) (invGerm U Φ ginv) ∧
      ∀ q ∈ V, ginv (Φ q).tgt = q := by
  obtain ⟨h1, h2, h3, h4, ⟨k, hk⟩, h6⟩ := hg
  have hsrc : ∀ p ∈ (fun q => (Φ q).tgt) '' V, (invGerm U Φ k p).src = p := fun p hp =>
    hk.right_inv p hp
  have htgt : ∀ p ∈ (fun q => (Φ q).tgt) '' V, (invGerm U Φ k p).tgt = k p := fun p hp =>
    h4 _ (hk.mapsTo_inv hp)
  have hkh : k h.tgt = h.src := by
    have := hk.left_inv h.src h2
    simp only [h3] at this
    exact this
  refine ⟨k, ⟨hk.isOpen_target, ⟨h.src, h2, show (Φ h.src).tgt = h.tgt by rw [h3]⟩, ?_, hsrc, ?_,
    hCS.inv _ _ _ _ k h6 h1 h4 hk⟩, fun q hq => hk.left_inv q hq⟩
  · change (Φ (k h.tgt)).inv = h.inv
    rw [hkh, h3]
  · refine ⟨fun q => (Φ q).tgt, ?_⟩
    have hs := hk.symm.congr_left (f' := fun p => (invGerm U Φ k p).tgt)
      (fun p hp => (htgt p hp).symm)
    have hi : (fun p => (invGerm U Φ k p).tgt) '' ((fun q => (Φ q).tgt) '' V) = V := hs.image_eq
    rw [hi]
    exact hs

theorem TransGerm.comp (hCS : CSClosed U CS) {Ψ Ψ' Ψ'' : U.Unif} {h : Ψ.1.Trans Ψ'.1}
    {h' : Ψ'.1.Trans Ψ''.1} (hh : h'.src = h.tgt) {V V' Φ Φ'}
    (hg : TransGerm U CS Ψ Ψ' h V Φ) (hg' : TransGerm U CS Ψ' Ψ'' h' V' Φ')
    (d : Ψ.1.Trans Ψ''.1) :
    TransGerm U CS Ψ Ψ'' (TransitionSet.comp h' h (TransitionSet.mor_composable_of_src_eq_tgt hh))
      (V ∩ (fun q => (Φ q).tgt) ⁻¹' V') (compGerm U Φ' Φ d) := by
  have hcont := hg.continuousOn
  obtain ⟨h1, h2, h3, h4, ⟨k, hk⟩, h6⟩ := hg
  obtain ⟨h1', h2', h3', h4', ⟨k', hk'⟩, h6'⟩ := hg'
  have hcomp : ∀ q ∈ V ∩ (fun q => (Φ q).tgt) ⁻¹' V',
      C.toGroupoidStr.src (Φ' (Φ q).tgt).mor = C.toGroupoidStr.tgt (Φ q).mor := fun q hq =>
    TransitionSet.mor_composable_of_src_eq_tgt (h4' _ hq.2)
  have hW : IsOpen (V ∩ (fun q => (Φ q).tgt) ⁻¹' V') := hcont.isOpen_inter_preimage h1 h1'
  have hq : h.src ∈ V ∩ (fun q => (Φ q).tgt) ⁻¹' V' :=
    ⟨h2, by simp only [mem_preimage, h3]; rw [← hh]; exact h2'⟩
  refine ⟨hW, hq, ?_, ?_, ?_, hCS.comp _ _ _ _ _ _ _ d h6 h6' h1 h1' h4 h4' hcont⟩
  · change compGerm U Φ' Φ d h.src = _
    rw [compGerm_eq U _ _ _ _ (hcomp _ hq)]
    refine GroupoidStr.TransitionSet.ext ?_ ?_ ?_
    · simp only [TransitionSet.src_comp, h3]
    · simp only [TransitionSet.mor_comp, h3]
      rw [show (h.tgt) = h'.src from hh.symm, h3']
    · simp only [TransitionSet.tgt_comp, h3]
      rw [show (h.tgt) = h'.src from hh.symm, h3']
  · intro q hq
    rw [compGerm_eq U _ _ _ _ (hcomp _ hq), TransitionSet.src_comp, h4 q hq.1]
  · have hc := hk.comp_inter hk'
    have heq : EqOn ((fun p => (Φ' p).tgt) ∘ fun q => (Φ q).tgt)
        (fun q => (compGerm U Φ' Φ d q).tgt) (V ∩ (fun q => (Φ q).tgt) ⁻¹' V') := by
      intro q hq
      simp only [Function.comp_apply, compGerm_eq U _ _ _ _ (hcomp _ hq),
        TransitionSet.tgt_comp]
    have hc' := hc.congr_left heq
    refine ⟨k ∘ k', ?_⟩
    rw [← hc'.image_eq] at hc'
    exact hc'

/-- The germ `q ↦ Ψ̂(g, q)` through `Ψ̂(g, o)`. -/
theorem hatGerm (hCS : CSClosed U CS) (Ψ : U.Unif) (g : Ψ.1.G) (o : Ψ.1.O) :
    TransGerm U CS Ψ Ψ (Ψ.1.hat (g, o)) univ (fun q => Ψ.1.hat (g, q)) := by
  refine ⟨isOpen_univ, mem_univ _, rfl, fun q _ => rfl, ⟨fun y => g⁻¹ • y, ?_⟩, hCS.hat Ψ g⟩
  have hs : Ψ.1.P.IsScDiffeoOn Ψ.1.P (fun y => g • y) (fun y => g⁻¹ • y) univ univ :=
    ⟨Ψ.1.smooth_smul g, Ψ.1.smooth_smul g⁻¹, mapsTo_univ _ _, mapsTo_univ _ _,
      fun y _ => inv_smul_smul g y, fun y _ => smul_inv_smul g y⟩
  have e : (fun q => (Ψ.1.hat (g, q)).tgt) '' univ = univ := hs.image_eq
  rw [e]
  exact hs

/-- Two germs through `h` agree near `s(h)`. -/
theorem Thm313.eventuallyEq (H : Thm313 U CS) {Ψ Ψ' : U.Unif} {h : Ψ.1.Trans Ψ'.1}
    {V₁ V₂ Φ₁ Φ₂} (h₁ : TransGerm U CS Ψ Ψ' h V₁ Φ₁) (h₂ : TransGerm U CS Ψ Ψ' h V₂ Φ₂) :
    ∀ᶠ q in 𝓝 h.src, Φ₁ q = Φ₂ q := by
  obtain ⟨W, hWo, hW, -, hEq⟩ := (H Ψ Ψ' h).2 V₁ Φ₁ V₂ Φ₂ h₁ h₂
  exact Filter.mem_of_superset (hWo.mem_nhds hW) fun q hq => hEq hq

end Germs

/-! ### A locally finite system of germs for each pair `Ψ, Ψ'` -/

/-- The sources of morphisms `Ψ → Ψ'`, an open subset of `O` (by Theorem 3.13). -/
def TDom (Ψ Ψ' : U.Unif) : Set Ψ.1.O := {o | ∃ e : Ψ.1.Trans Ψ'.1, e.src = o}

section Charts

variable {CS : CSPred U}

theorem isOpen_tDom (H : Thm313 U CS) (Ψ Ψ' : U.Unif) : IsOpen (TDom Ψ Ψ') := by
  rw [isOpen_iff_forall_mem_open]
  rintro o ⟨e, rfl⟩
  obtain ⟨V, Φ, hg⟩ := (H Ψ Ψ' e).1
  exact ⟨V, fun q hq => ⟨Φ q, hg.2.2.2.1 q hq⟩, hg.1, hg.2.1⟩

variable (CS) in
/-- Germs `Φ_i` on `V_i`, indexed by the sources `i ∈ TDom Ψ Ψ'`, with a locally finite family of
sets `K_i ⊆ V_i` covering `TDom Ψ Ψ'`. -/
structure ChartSystem (Ψ Ψ' : U.Unif) where
  V : TDom Ψ Ψ' → Set Ψ.1.O
  Φ : TDom Ψ Ψ' → Ψ.1.O → Ψ.1.Trans Ψ'.1
  germ : ∀ i, TransGerm U CS Ψ Ψ' (Φ i i.1) (V i) (Φ i)
  K : TDom Ψ Ψ' → Set Ψ.1.O
  K_sub : ∀ i, K i ⊆ V i
  finite : ∀ o, {i | o ∈ K i}.Finite
  locfin : ∀ o ∈ TDom Ψ Ψ', ∀ᶠ q in 𝓝 o, ∀ i, o ∉ K i → q ∉ K i
  cover : ∀ o ∈ TDom Ψ Ψ', ∃ i, o ∈ K i

/-- Chart systems exist: precise refinement and shrinking in the metrizable open set
`TDom Ψ Ψ'` (Theorem 2.3.10). -/
theorem exists_chartSystem (H : Thm313 U CS) (Ψ Ψ' : U.Unif) :
    Nonempty (ChartSystem CS Ψ Ψ') := by
  classical
  have hD : IsOpen (TDom Ψ Ψ') := isOpen_tDom H Ψ Ψ'
  have hg : ∀ i : TDom Ψ Ψ', ∃ V Φ, TransGerm U CS Ψ Ψ' i.2.choose V Φ := fun i =>
    (H Ψ Ψ' _).1
  choose V Φ hVΦ using hg
  have hmem : ∀ i : TDom Ψ Ψ', i.1 ∈ V i := fun i => by
    have := (hVΦ i).2.1
    rwa [i.2.choose_spec] at this
  have : TopologicalSpace.MetrizableSpace Ψ.1.O := Ψ.1.P.metrizableSpace
  let _ := TopologicalSpace.metrizableSpaceMetric (TDom Ψ Ψ')
  obtain ⟨v, hvo, hvU, hvlf, hvsub⟩ := precise_refinement
    (fun i : TDom Ψ Ψ' => (Subtype.val ⁻¹' V i : Set (TDom Ψ Ψ')))
    (fun i => (hVΦ i).1.preimage continuous_subtype_val)
    (eq_univ_of_forall fun x => mem_iUnion.2 ⟨x, hmem x⟩)
  obtain ⟨w, hwU, -, hwsub⟩ :=
    exists_iUnion_eq_closure_subset hvo (fun x => hvlf.point_finite x) hvU
  have hlf : LocallyFinite fun i => closure (w i) := hvlf.subset hwsub
  have hKD : ∀ i o, o ∈ Subtype.val '' closure (w i) → ∀ ho : o ∈ TDom Ψ Ψ',
      (⟨o, ho⟩ : TDom Ψ Ψ') ∈ closure (w i) := by
    rintro i _ ⟨x, hx, rfl⟩ _
    exact hx
  refine ⟨⟨V, Φ, fun i => (hVΦ i).atPt (hmem i), fun i => Subtype.val '' closure (w i),
    ?_, ?_, ?_, ?_⟩⟩
  · rintro i _ ⟨x, hx, rfl⟩
    exact hvsub i (hwsub i hx)
  · intro o
    by_cases ho : o ∈ TDom Ψ Ψ'
    · exact (hlf.point_finite ⟨o, ho⟩).subset fun i hi => hKD i o hi ho
    · convert Set.finite_empty
      refine eq_empty_of_forall_notMem fun i hi => ho ?_
      obtain ⟨x, -, rfl⟩ := hi
      exact x.2
  · intro o ho
    have hN := hD.isOpenMap_subtype_val.image_mem_nhds
      (hlf.iInter_compl_mem_nhds (fun _ => isClosed_closure) ⟨o, ho⟩)
    refine Filter.mem_of_superset hN ?_
    rintro _ ⟨x, hxN, rfl⟩ i hoi ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    subst hyx'
    have hoi' : (⟨o, ho⟩ : TDom Ψ Ψ') ∉ closure (w i) := fun h' => hoi ⟨_, h', rfl⟩
    exact (mem_iInter₂.1 hxN i hoi') hy
  · intro o ho
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hwU.symm ▸ mem_univ (⟨o, ho⟩ : TDom Ψ Ψ'))
    exact ⟨i, ⟨o, ho⟩, subset_closure hi, rfl⟩

end Charts

/-! ### The transition data -/

section Construction

variable {CS : CSPred U} (cs : ∀ Ψ Ψ' : U.Unif, ChartSystem CS Ψ Ψ')

/-- The chart through `o`. -/
def idxAt {Ψ Ψ' : U.Unif} (o : Ψ.1.O) (ho : o ∈ TDom Ψ Ψ') : TDom Ψ Ψ' :=
  ((cs Ψ Ψ').cover o ho).choose

theorem mem_K_idxAt {Ψ Ψ' : U.Unif} (o : Ψ.1.O) (ho : o ∈ TDom Ψ Ψ') :
    o ∈ (cs Ψ Ψ').K (idxAt cs o ho) :=
  ((cs Ψ Ψ').cover o ho).choose_spec

theorem idxAt_congr {Ψ Ψ' : U.Unif} {o o' : Ψ.1.O} (e : o = o') (ho : o ∈ TDom Ψ Ψ')
    (ho' : o' ∈ TDom Ψ Ψ') : idxAt cs o ho = idxAt cs o' ho' := by
  subst e; rfl

/-- The chart through `s(h)`. -/
def idx {Ψ Ψ' : U.Unif} (h : Ψ.1.Trans Ψ'.1) : TDom Ψ Ψ' := idxAt cs h.src ⟨h, rfl⟩

theorem idx_congr {Ψ Ψ' : U.Unif} {h h' : Ψ.1.Trans Ψ'.1} (e : h.src = h'.src) :
    idx cs h = idx cs h' := idxAt_congr cs e _ _

theorem mem_K_idx {Ψ Ψ' : U.Unif} (h : Ψ.1.Trans Ψ'.1) : h.src ∈ (cs Ψ Ψ').K (idx cs h) :=
  mem_K_idxAt cs _ _

theorem mem_V_idx {Ψ Ψ' : U.Unif} (h : Ψ.1.Trans Ψ'.1) : h.src ∈ (cs Ψ Ψ').V (idx cs h) :=
  (cs Ψ Ψ').K_sub _ (mem_K_idx cs h)

theorem chart_src {Ψ Ψ' : U.Unif} (i : TDom Ψ Ψ') {q : Ψ.1.O} (hq : q ∈ (cs Ψ Ψ').V i) :
    ((cs Ψ Ψ').Φ i q).src = q :=
  ((cs Ψ Ψ').germ i).2.2.2.1 q hq

/-- The element `g' ∈ G'` moving the chart value at `s(h)` to `h` (Proposition 3.12). -/
def gsel {Ψ Ψ' : U.Unif} (h : Ψ.1.Trans Ψ'.1) : Ψ'.1.G :=
  (exists_transl (a := (cs Ψ Ψ').Φ (idx cs h) h.src) (b := h)
    (chart_src cs _ (mem_V_idx cs h)).symm).choose

/-- `F_h(q)`: the chart through `s(h)`, translated so that it passes through `h`. -/
def mapS {Ψ Ψ' : U.Unif} (h : Ψ.1.Trans Ψ'.1) (q : Ψ.1.O) : Ψ.1.Trans Ψ'.1 :=
  transl (gsel cs h) ((cs Ψ Ψ').Φ (idx cs h) q)

theorem mapS_src_pt {Ψ Ψ' : U.Unif} (h : Ψ.1.Trans Ψ'.1) : mapS cs h h.src = h :=
  (exists_transl (a := (cs Ψ Ψ').Φ (idx cs h) h.src) (b := h)
    (chart_src cs _ (mem_V_idx cs h)).symm).choose_spec

theorem mapS_germ (hCS : CSClosed U CS) {Ψ Ψ' : U.Unif} (h : Ψ.1.Trans Ψ'.1) :
    TransGerm U CS Ψ Ψ' h ((cs Ψ Ψ').V (idx cs h)) (mapS cs h) := by
  have := (((cs Ψ Ψ').germ (idx cs h)).atPt (mem_V_idx cs h)).translate hCS (gsel cs h)
  have e : transl (gsel cs h) ((cs Ψ Ψ').Φ (idx cs h) h.src) = h := mapS_src_pt cs h
  rw [e] at this
  exact this

/-- The cast `M(Ψ, Ψ) → M(Ψ, Ψ')` along `Ψ = Ψ'`. -/
def castT {Ψ Ψ' : U.Unif} (e : Ψ = Ψ') : Ψ.1.Trans Ψ.1 → Ψ.1.Trans Ψ'.1 :=
  cast (congrArg (fun X : U.Unif => Ψ.1.Trans X.1) e)

/-- The conditions defining `V(o)`: the finitely many germs relevant at `o` agree with `F_h`. -/
def Req (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) (q : Ψ.1.O) : Prop :=
  q ∈ (cs Ψ Ψ').V (idx cs h) ∧
  (∀ i, h.src ∉ (cs Ψ Ψ').K i → q ∉ (cs Ψ Ψ').K i) ∧
  (∀ i, h.src ∈ (cs Ψ Ψ').K i → ∀ g : Ψ'.1.G, transl g ((cs Ψ Ψ').Φ i h.src) = h →
    transl g ((cs Ψ Ψ').Φ i q) = mapS cs h q) ∧
  (∀ (e : Ψ = Ψ') (g : Ψ.1.G), h = castT e (Ψ.1.hat (g, h.src)) →
    mapS cs h q = castT e (Ψ.1.hat (g, q))) ∧
  mapS cs h.inv (mapS cs h q).tgt = (mapS cs h q).inv ∧
  (∀ (Ψ'' : U.Unif) (h' : Ψ'.1.Trans Ψ''.1) (hh : h'.src = h.tgt) hc,
    TransitionSet.comp (mapS cs h' (mapS cs h q).tgt) (mapS cs h q) hc =
      mapS cs (TransitionSet.comp h' h (TransitionSet.mor_composable_of_src_eq_tgt hh)) q)

theorem req_eventually (H : Thm313 U CS) (hCS : CSClosed U CS) (hPF : PointFinite U)
    (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) : ∀ᶠ q in 𝓝 h.src, Req cs Ψ Ψ' h q := by
  have hG := mapS_germ cs hCS h
  have hV : ∀ᶠ q in 𝓝 h.src, q ∈ (cs Ψ Ψ').V (idx cs h) := hG.1.mem_nhds hG.2.1
  refine hV.and ((cs Ψ Ψ').locfin _ ⟨h, rfl⟩) |>.and ?_ |>.and ?_ |>.and ?_ |>.and ?_ |>.mono
    fun q hq => ⟨hq.1.1.1.1.1, hq.1.1.1.1.2, hq.1.1.1.2, hq.1.1.2, hq.1.2, hq.2⟩
  · -- the charts whose `K` contains `s(h)`
    have hfin := (cs Ψ Ψ').finite h.src
    suffices hs : ∀ i ∈ {i | h.src ∈ (cs Ψ Ψ').K i}, ∀ g : Ψ'.1.G,
        ∀ᶠ q in 𝓝 h.src, transl g ((cs Ψ Ψ').Φ i h.src) = h →
          transl g ((cs Ψ Ψ').Φ i q) = mapS cs h q by
      exact ((Filter.eventually_all_finite hfin).2 fun i hi =>
        Filter.eventually_all.2 (hs i hi)).mono fun q hq i hi => hq i hi
    intro i hi g
    by_cases hg : transl g ((cs Ψ Ψ').Φ i h.src) = h
    · have hgi := (((cs Ψ Ψ').germ i).atPt ((cs Ψ Ψ').K_sub i hi)).translate hCS g
      rw [hg] at hgi
      exact (Thm313.eventuallyEq H hgi hG).mono fun q hq _ => hq
    · exact Filter.Eventually.of_forall fun q h' => absurd h' hg
  · -- the maps `Ψ̂(g, ·)`
    by_cases e : Ψ = Ψ'
    · subst e
      suffices hs : ∀ g : Ψ.1.G, ∀ᶠ q in 𝓝 h.src, h = Ψ.1.hat (g, h.src) →
          mapS cs h q = Ψ.1.hat (g, q) by
        exact (Filter.eventually_all.2 hs).mono fun q hq e g => hq g
      intro g
      by_cases hg : h = Ψ.1.hat (g, h.src)
      · have hh := hatGerm hCS Ψ g h.src
        rw [← hg] at hh
        exact (Thm313.eventuallyEq H hG hh).mono fun q hq _ => hq
      · exact Filter.Eventually.of_forall fun q h' => absurd h' hg
    · exact Filter.Eventually.of_forall fun q e' => absurd e' e
  · -- inversion
    obtain ⟨ginv, hI, hginv⟩ := hG.inv hCS
    have hE := Thm313.eventuallyEq H hI (mapS_germ cs hCS h.inv)
    have hc : ContinuousAt (fun q => (mapS cs h q).tgt) h.src :=
      hG.continuousOn.continuousAt (hG.1.mem_nhds hG.2.1)
    have ht : Tendsto (fun q => (mapS cs h q).tgt) (𝓝 h.src) (𝓝 h.inv.src) := by
      have := hc.tendsto
      rwa [mapS_src_pt] at this
    filter_upwards [ht.eventually hE, hV] with q hq hqV
    rw [← hq]
    change (mapS cs h (ginv (mapS cs h q).tgt)).inv = _
    rw [hginv q hqV]
  · -- multiplication
    have hfin := hPF Ψ' h.tgt
    have key : ∀ Ψ'' ∈ {Ψ'' : U.Unif | ∃ e : Ψ'.1.Trans Ψ''.1, e.src = h.tgt},
        ∀ᶠ q in 𝓝 h.src, ∀ h' ∈ {a : Ψ'.1.Trans Ψ''.1 | a.src = h.tgt},
          ∀ (hh : h'.src = h.tgt) hc,
            TransitionSet.comp (mapS cs h' (mapS cs h q).tgt) (mapS cs h q) hc =
              mapS cs (TransitionSet.comp h' h
                (TransitionSet.mor_composable_of_src_eq_tgt hh)) q := by
      intro Ψ'' _
      refine (Filter.eventually_all_finite (Ψ'.1.finite_fiber (Ψ' := Ψ''.1) h.tgt)).2
        fun h' hh => ?_
      have hC := hG.comp hCS hh (mapS_germ cs hCS h')
        (TransitionSet.comp h' h (TransitionSet.mor_composable_of_src_eq_tgt hh))
      have hE := Thm313.eventuallyEq H hC (mapS_germ cs hCS _)
      filter_upwards [hE, hC.1.mem_nhds hC.2.1] with q hq hqW hh' hc
      rw [← hq, compGerm_eq U _ _ _ _ hc]
    filter_upwards [(Filter.eventually_all_finite hfin).2 key] with q hq Ψ'' h' hh hc
    exact hq Ψ'' ⟨h', hh⟩ h' hh hh hc

theorem req_of_mem {Ψ Ψ' : U.Unif} {h : Ψ.1.Trans Ψ'.1} {q : Ψ.1.O}
    (hq : q ∈ interior {q | Req cs Ψ Ψ' h q}) : Req cs Ψ Ψ' h q :=
  interior_subset (s := {q | Req cs Ψ Ψ' h q}) hq

/-- The transition data built from chart systems: `V(o)` is the interior of `{q | Req h q}` and
`F_h = mapS h`. -/
def transitionDataOf (H : Thm313 U CS) (hCS : CSClosed U CS) (hPF : PointFinite U) :
    U.TransitionData where
  dom Ψ Ψ' h := interior {q | Req cs Ψ Ψ' h q}
  map Ψ Ψ' h := mapS cs h
  isOpen_dom _ _ _ := isOpen_interior
  mem_dom Ψ Ψ' h := mem_interior_iff_mem_nhds.2 (req_eventually cs H hCS hPF Ψ Ψ' h)
  map_src _ _ h := mapS_src_pt cs h
  src_map Ψ Ψ' h q hq := chart_src cs _ (req_of_mem cs hq).1
  diffeo Ψ Ψ' h := by
    obtain ⟨k, hk⟩ := (mapS_germ cs hCS h).2.2.2.2.1
    have hk' := hk.restrict isOpen_interior fun q hq =>
      (req_of_mem cs hq).1
    rw [← hk'.image_eq] at hk'
    exact ⟨k, hk'⟩
  map_hat Ψ p q hq := (req_of_mem cs hq).2.2.2.1 rfl p.1 rfl
  stability Ψ Ψ' h q hq p hp := by
    have hq' := req_of_mem cs hq
    have hp' := req_of_mem cs hp.2
    set k := mapS cs h q with hk
    have hks : k.src = q := chart_src cs _ hq'.1
    set j := idx cs k
    have hqj : q ∈ (cs Ψ Ψ').K j := hks ▸ mem_K_idx cs k
    have hoj : h.src ∈ (cs Ψ Ψ').K j := by
      by_contra hn
      exact hq'.2.1 j hn hqj
    obtain ⟨g', hg'⟩ := exists_transl (a := (cs Ψ Ψ').Φ j h.src) (b := h)
      (chart_src cs j ((cs Ψ Ψ').K_sub j hoj)).symm
    have h1 : transl g' ((cs Ψ Ψ').Φ j q) = k := hq'.2.2.1 j hoj g' hg'
    have h2 : transl (gsel cs k) ((cs Ψ Ψ').Φ j q) = k := by
      have := mapS_src_pt cs k
      rw [hks] at this
      exact this
    have hg : gsel cs k = g' := transl_injective _ (h2.trans h1.symm)
    change transl (gsel cs k) ((cs Ψ Ψ').Φ j p) = mapS cs h p
    rw [hg]
    exact hp'.2.2.1 j hoj g' hg'
  identity Ψ o q hq := by
    have hq' : q ∈ interior {q | Req cs Ψ Ψ (Ψ.1.hat (1, o)) q} := by rwa [Ψ.1.hat_one]
    have := (req_of_mem cs hq').2.2.2.1 rfl 1 rfl
    rw [Ψ.1.hat_one, Ψ.1.hat_one] at this
    exact this
  inversion Ψ Ψ' h q hq _ := (req_of_mem cs hq).2.2.2.2.1
  multiplication Ψ Ψ' Ψ'' h h' hh q hq _ _ := (req_of_mem cs hq).2.2.2.2.2 Ψ'' h' hh _
  hausdorff Ψ Ψ' h₁ h₂ hne hs := by
    refine ⟨interior {q | Req cs Ψ Ψ' h₁ q} ∩ interior {q | Req cs Ψ Ψ' h₂ q},
      isOpen_interior.inter isOpen_interior,
      ⟨mem_interior_iff_mem_nhds.2 (req_eventually cs H hCS hPF Ψ Ψ' h₁),
        hs ▸ mem_interior_iff_mem_nhds.2 (req_eventually cs H hCS hPF Ψ Ψ' h₂)⟩,
      subset_rfl, ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ ⟨p', hp', he⟩
    have hpp : p' = p := by
      have e1 := congrArg TransitionSet.src he
      rwa [show (mapS cs h₂ p').src = p' from chart_src cs _ (req_of_mem cs hp'.2).1,
        show (mapS cs h₁ p).src = p from chart_src cs _ (req_of_mem cs hp.1).1] at e1
    subst hpp
    have hi : idx cs h₂ = idx cs h₁ := idx_congr cs hs.symm
    have he' : transl (gsel cs h₂) ((cs Ψ Ψ').Φ (idx cs h₁) p') =
        transl (gsel cs h₁) ((cs Ψ Ψ').Φ (idx cs h₁) p') := by
      have : mapS cs h₂ p' = transl (gsel cs h₂) ((cs Ψ Ψ').Φ (idx cs h₂) p') := rfl
      rw [this, hi] at he
      exact he
    have hg := transl_injective _ he'
    apply hne
    rw [← mapS_src_pt cs h₁, ← mapS_src_pt cs h₂]
    change transl (gsel cs h₁) ((cs Ψ Ψ').Φ (idx cs h₁) h₁.src) =
      transl (gsel cs h₂) ((cs Ψ Ψ').Φ (idx cs h₂) h₂.src)
    rw [hi, hg, hs]

end Construction

/-- **Memoir Theorem 3.13 ⇒ Properties (19.3) (A)–(F)** (memoir §3.2, pp. 73–79; 2021 book
pp. 865–867): uniqueness of the germs of Theorem 3.13 gives transition data, when core-smoothness
is closed under the operations on germs (`CSClosed`) and the family is point-finite. -/
theorem reduction_3_13 {CS : CSPred U} (H : Thm313 U CS) (hCS : CSClosed U CS)
    (hPF : PointFinite U) : Nonempty U.TransitionData :=
  ⟨transitionDataOf (fun Ψ Ψ' => (exists_chartSystem H Ψ Ψ').some) H hCS hPF⟩

/-- `Reduction_3_13` of `GWMemoir.Skeleton`, under `CSClosed` and `PointFinite`. -/
theorem reduction_3_13_skeleton {C : GroupoidalCategory.{1}} {U : C.UniformizerConstruction}
    {CS : CSPred U} (hCS : CSClosed U CS) (hPF : PointFinite U) : Reduction_3_13 U CS :=
  fun H => reduction_3_13 ((theorem_3_13_iff U CS).1 H) hCS hPF

end GWMemoir
