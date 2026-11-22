import Polyfold.Chapter17.PolyfoldLevels
import Polyfold.Chapter17.AdmissibleTripleBasic
import Polyfold.Chapter14.FaceTame

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.4 (pp. 787–791): the local sc-diffeomorphisms `f = t ∘ (s|W(h))⁻¹` of the elements `h` of
the transition sets and the correspondence of faces under them, used in **(17.58)**,
**Definition 17.4.3 (2)** and the notation `θ' = f_*^{Ψ,Ψ'} θ` (p. 790).  Numbers and pages are
the 2021 text's.

# Face germs transported by transition elements

## The text, paraphrased

(p. 789) For `h = (ō, φ, ō') ∈ M(Ψ, Ψ')` take open neighbourhoods `W(h)`, `W(ō)`, `W'(ō')` with
`s : W(h) → W(ō)` and `t : W(h) → W'(ō')` sc-diffeomorphisms, and `f = t ∘ (s|W(h))⁻¹`.  A face
`θ` of a good neighbourhood of `ō` and a face `θ'` of one of `ō'` **correspond** if
`f(θ ∩ W(ō)) = θ' ∩ W'(ō')`, "i.e. are identical up to `f` near `ō` and `ō'`".  The face `θ'` is
uniquely determined by `θ` (p. 790), written `θ' = f_*θ`; "the germ of `f` is uniquely
determined by `φ` and the knowledge of `Ψ` and `Ψ'`".

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `AdmissibleTriple.germMap` (`f = t ∘ (s|W(h))⁻¹`), an sc-diffeomorphism of `W(ō)` onto
  `W'(ō')` (`isScDiffeoOn_germMap`), hence an index-preserving homeomorphism
  (`isDHomeoOn_germMap`).
* The germ of `f` at `ō` depends only on `h` (`germMap_eventuallyEq`), and at the points `s(b)`,
  `b ∈ W(h)`, it is the germ of `b` (`germMap_eventuallyEq_of_mem`).  The laws: the germ of
  `(q, 1, q)` is the identity (`germMap_unit_eventuallyEq`, continuity of `u`), that of `h⁻¹` is
  inverse to that of `h` (`germMap_inv_comp_eventuallyEq`, continuity of `ι`), and the germ of
  `h' ∘ h` is the composite (`germMap_comp_eventuallyEq`, continuity of `m`, Definition 17.1.8).
* `S.bO hT Ψ`: the tame boundary `bO = BSpace` of the domain `O` of `Ψ` (Part I, Definition
  2.7.10), whose points over `x ∈ ∂O` are the face germs at `x`.
* `GermLift h p p'`: `h` carries the face germ `p` at `s(h)` to the face germ `p'` at `t(h)`
  (Part II's `IsLiftOf` along `f`); `germLift_unique`, `exists_germLift`, `germLift_iff_forall`
  (for every choice of `W(h)`), `germLift_unit`, `germLift_inv`, `germLift_comp`,
  `germLift_of_mem_carrier`.  The push-forward `germPush h p` is `f_*`.

## Readings

* "`θ` and `θ'` correspond under `f`" (the condition `f(θ ∩ W(ō)) = θ' ∩ W'(ō')` for suitable
  small neighbourhoods, "identical up to `f` near `ō` and `ō'`") is read on the level of face
  germs: the class `[ō, V, θ]` of Part I's tame boundary `bO` (Definition 2.7.10, which is
  exactly the equality of faces near `ō`) is carried by `f` to `[ō', V', θ']` (Part II's
  `IsLiftOf`, the recipe of (7.25)).  This does not depend on the choice of `W(h)`
  (`germLift_iff_forall`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

universe u

namespace Polyfold

open TameBoundary

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-! ### The local sc-diffeomorphism `f = t ∘ (s|W(h))⁻¹` -/

section GermMap

variable {Ψ Ψ' Ψ'' : S.Unif}

namespace AdmissibleTriple

variable {a : S.Tr Ψ Ψ'} (T : S.AdmissibleTriple a)

/-- **The local sc-diffeomorphism `f = t ∘ (s|W(h))⁻¹ : W(ō) → W'(ō')`** of an admissible triple
of `h` (2021 p. 789). -/
def germMap : Ψ.1.O → Ψ'.1.O := fun x => (T.srcInv x).tgt

/-- `f` is an sc-diffeomorphism of `W(ō)` onto `W'(ō')`. -/
theorem isScDiffeoOn_germMap :
    Ψ.1.P.IsScDiffeoOn Ψ'.1.P T.germMap (fun y => (T.tgtInv y).src) T.srcSet T.tgtSet :=
  MPolyfold.IsScDiffeoOn.comp T.isScDiffeoOn_tgt T.isScDiffeoOn_src.symm

/-- `f` is an index-preserving homeomorphism of `W(ō)` onto an open set. -/
theorem isDHomeoOn_germMap :
    IsDHomeoOn Ψ.1.P.degIndex Ψ'.1.P.degIndex T.germMap T.srcSet :=
  T.isScDiffeoOn_germMap.isDHomeoOn

theorem germMap_eq {b : S.Tr Ψ Ψ'} (hb : b ∈ T.carrier) : T.germMap b.src = b.tgt := by
  rw [germMap, T.srcInv_eq hb]

theorem germMap_src : T.germMap a.src = a.tgt := T.germMap_eq T.mem_carrier

theorem continuousOn_srcInv : ContinuousOn T.srcInv T.srcSet :=
  T.isScDiffeoOn_src.isScSmoothOn_inv.continuousOn

/-- **A continuous local section of `s` through a point of `W(h)` is `(s|W(h))⁻¹` near its base
point.** -/
theorem eventuallyEq_srcInv {F : Ψ.1.O → S.Tr Ψ Ψ'} {N : Set Ψ.1.O} (hN : IsOpen N)
    {x₀ : Ψ.1.O} (hx₀ : x₀ ∈ N) (hF : ContinuousOn F N) (hFs : ∀ x ∈ N, (F x).src = x)
    (hF₀ : F x₀ ∈ T.carrier) : F =ᶠ[𝓝 x₀] T.srcInv := by
  have h1 : ∀ᶠ x in 𝓝 x₀, F x ∈ T.carrier :=
    (hF.continuousAt (hN.mem_nhds hx₀)).preimage_mem_nhds (T.isOpen_carrier.mem_nhds hF₀)
  filter_upwards [h1, hN.mem_nhds hx₀] with x hx hxN
  rw [← T.srcInv_eq hx, hFs x hxN]

end AdmissibleTriple

/-- **The germ of `f` at `s(b)` for `b ∈ W(h)` is the germ of `b`**: for admissible triples `T`
of `a` and `T'` of `b` with `b ∈ W(a)`, `f_T = f_{T'}` near `s(b)`.  For `b = a` this is the
text's "the germ of `f` is uniquely determined by `φ`, `Ψ` and `Ψ'`" (p. 790). -/
theorem germMap_eventuallyEq_of_mem {a b : S.Tr Ψ Ψ'} (T : S.AdmissibleTriple a)
    (T' : S.AdmissibleTriple b) (hb : b ∈ T.carrier) :
    T.germMap =ᶠ[𝓝 b.src] T'.germMap := by
  have h := T.eventuallyEq_srcInv T'.isOpen_srcSet T'.src_mem T'.continuousOn_srcInv
    (fun x hx => T'.src_srcInv hx) (by rw [T'.srcInv_eq T'.mem_carrier]; exact hb)
  filter_upwards [h] with x hx
  change (T.srcInv x).tgt = (T'.srcInv x).tgt
  rw [hx]

theorem germMap_eventuallyEq {a : S.Tr Ψ Ψ'} (T T' : S.AdmissibleTriple a) :
    T.germMap =ᶠ[𝓝 a.src] T'.germMap :=
  germMap_eventuallyEq_of_mem T T' T.mem_carrier

/-- **The germ of `(q, 1, q)` is the identity** (continuity of the unit map `u`, Definition
17.1.8 (b)). -/
theorem germMap_unit_eventuallyEq (q : Ψ.1.O)
    (T : S.AdmissibleTriple (S.toTr (GroupoidStr.TransitionSet.unit q) : S.Tr Ψ Ψ)) :
    T.germMap =ᶠ[𝓝 q] id := by
  have hu : Continuous fun x => (S.toTr (GroupoidStr.TransitionSet.unit x) : S.Tr Ψ Ψ) :=
    continuousOn_univ.1 (S.isScSmoothMap_trUnit Ψ).continuousOn
  have h := T.eventuallyEq_srcInv isOpen_univ (mem_univ q) hu.continuousOn
    (fun x _ => GroupoidStr.TransitionSet.src_unit x) T.mem_carrier
  filter_upwards [h] with x hx
  change (T.srcInv x).tgt = x
  rw [← hx]
  exact GroupoidStr.TransitionSet.tgt_unit x

/-- **The germ of `h⁻¹` is inverse to the germ of `h`** (continuity of `ι`, Definition 17.1.8
(b)). -/
theorem germMap_inv_comp_eventuallyEq {a : S.Tr Ψ Ψ'} (T : S.AdmissibleTriple a)
    (T' : S.AdmissibleTriple (S.toTr (GroupoidStr.TransitionSet.inv a) : S.Tr Ψ' Ψ)) :
    T'.germMap ∘ T.germMap =ᶠ[𝓝 a.src] id := by
  have hι : Continuous fun b : S.Tr Ψ Ψ' =>
      (S.toTr (GroupoidStr.TransitionSet.inv b) : S.Tr Ψ' Ψ) :=
    continuousOn_univ.1 (S.isScSmoothMap_trInv Ψ Ψ').continuousOn
  have h1 : ∀ᶠ x in 𝓝 a.src, (S.toTr (GroupoidStr.TransitionSet.inv (T.srcInv x)) :
      S.Tr Ψ' Ψ) ∈ T'.carrier := by
    have hc : ContinuousAt (fun x => (S.toTr (GroupoidStr.TransitionSet.inv (T.srcInv x)) :
        S.Tr Ψ' Ψ)) a.src :=
      hι.continuousAt.comp (T.continuousOn_srcInv.continuousAt
        (T.isOpen_srcSet.mem_nhds T.src_mem))
    refine hc.preimage_mem_nhds (T'.isOpen_carrier.mem_nhds ?_)
    rw [T.srcInv_eq T.mem_carrier]
    exact T'.mem_carrier
  filter_upwards [h1, T.isOpen_srcSet.mem_nhds T.src_mem] with x hx hxs
  change (T'.srcInv (T.srcInv x).tgt).tgt = x
  have he := T'.srcInv_eq hx
  have hs : (S.toTr (GroupoidStr.TransitionSet.inv (T.srcInv x)) : S.Tr Ψ' Ψ).src =
      (T.srcInv x).tgt := GroupoidStr.TransitionSet.src_inv _
  rw [hs] at he
  rw [he]
  exact (GroupoidStr.TransitionSet.tgt_inv _).trans (T.src_srcInv hxs)

/-- **The germ of `h' ∘ h` is the composite of the germs** (continuity of the multiplication
`m`, Definition 17.1.8 (c)): `p ↦ m((s|W(h'))⁻¹(f_h p), (s|W(h))⁻¹ p)` is a continuous local
section of `s` through `h' ∘ h`. -/
theorem germMap_comp_eventuallyEq (a : S.Tr Ψ' Ψ'') (b : S.Tr Ψ Ψ')
    (hab : C.toGroupoidStr.src a.mor = C.toGroupoidStr.tgt b.mor) (hs : a.src = b.tgt)
    (Ta : S.AdmissibleTriple a) (Tb : S.AdmissibleTriple b)
    (Tab : S.AdmissibleTriple (S.toTr (GroupoidStr.TransitionSet.comp a b hab) : S.Tr Ψ Ψ'')) :
    Tab.germMap =ᶠ[𝓝 b.src] Ta.germMap ∘ Tb.germMap := by
  let _ := MPolyfold.paracompactSpace_prod (S.transPolyfold Ψ' Ψ'') (S.transPolyfold Ψ Ψ')
  set d := MPolyfold.fibredSubDataL Ta.isScDiffeoOn_src
    (S.isLocalScDiffeo_trTgt Ψ Ψ').isScSmoothMap
  let a₀ : MPolyfold.fibredProduct (fun x : S.Tr Ψ' Ψ'' => x.src)
      (fun y : S.Tr Ψ Ψ' => y.tgt) := ⟨(a, b), hs⟩
  have hm := (S.isScSmoothMap_trMul Ψ Ψ' Ψ'').isScSmoothOn_sheet Ta.isScDiffeoOn_src a₀
  set F : S.Tr Ψ Ψ' → S.Tr Ψ Ψ'' := fun y =>
    S.toTr (GroupoidStr.TransitionSet.mul (d.retractInto a₀ (Ta.srcInv y.tgt, y))) with hFdef
  have hFc : ContinuousOn F ((fun y : S.Tr Ψ Ψ' => y.tgt) ⁻¹' Ta.srcSet) :=
    (show (S.transPolyfold Ψ Ψ').IsScSmoothOn (S.transPolyfold Ψ Ψ'') F _ from hm).continuousOn
  have hFval : ∀ y : S.Tr Ψ Ψ', ∀ hy : y.tgt ∈ Ta.srcSet,
      F y = S.toTr (GroupoidStr.TransitionSet.comp (Ta.srcInv y.tgt) y
        (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt (Ta.src_srcInv hy))) := by
    intro y hy
    have hv := d.retractInto_val a₀ (x := (Ta.srcInv y.tgt, y)) ⟨Ta.srcInv_mem hy, hy⟩
    refine GroupoidStr.TransitionSet.ext ?_ ?_ ?_
    · exact congrArg (fun p : S.Tr Ψ' Ψ'' × S.Tr Ψ Ψ' => p.2.src) hv
    · exact congrArg (fun p : S.Tr Ψ' Ψ'' × S.Tr Ψ Ψ' =>
        C.toGroupoidStr.comp p.1.mor p.2.mor) hv
    · exact congrArg (fun p : S.Tr Ψ' Ψ'' × S.Tr Ψ Ψ' => p.1.tgt) hv
  set N : Set Ψ.1.O := Tb.srcSet ∩ Tb.srcInv ⁻¹' ((fun y : S.Tr Ψ Ψ' => y.tgt) ⁻¹' Ta.srcSet)
  have hNo : IsOpen N := Tb.continuousOn_srcInv.isOpen_inter_preimage Tb.isOpen_srcSet
    (Ta.isOpen_srcSet.preimage (S.continuous_trTgt Ψ Ψ'))
  have hbN : b.src ∈ N := by
    refine ⟨Tb.src_mem, ?_⟩
    change (Tb.srcInv b.src).tgt ∈ Ta.srcSet
    rw [Tb.srcInv_eq Tb.mem_carrier, ← hs]
    exact Ta.src_mem
  have hGc : ContinuousOn (F ∘ Tb.srcInv) N :=
    hFc.comp (Tb.continuousOn_srcInv.mono inter_subset_left) fun p hp => hp.2
  have hGval : ∀ p (hp : p ∈ N), (F ∘ Tb.srcInv) p = S.toTr (GroupoidStr.TransitionSet.comp
      (Ta.srcInv (Tb.srcInv p).tgt) (Tb.srcInv p)
      (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt (Ta.src_srcInv hp.2))) :=
    fun p hp => hFval _ hp.2
  have hGs : ∀ p ∈ N, ((F ∘ Tb.srcInv) p).src = p := fun p hp => by
    rw [hGval p hp]; exact Tb.src_srcInv hp.1
  have hGab : (F ∘ Tb.srcInv) b.src ∈ Tab.carrier := by
    rw [hGval _ hbN]
    have hb : Tb.srcInv b.src = b := Tb.srcInv_eq Tb.mem_carrier
    have ha : Ta.srcInv b.tgt = a := by rw [← hs]; exact Ta.srcInv_eq Ta.mem_carrier
    have he : (S.toTr (GroupoidStr.TransitionSet.comp (Ta.srcInv (Tb.srcInv b.src).tgt)
        (Tb.srcInv b.src) (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt
          (Ta.src_srcInv hbN.2))) : S.Tr Ψ Ψ'') =
        S.toTr (GroupoidStr.TransitionSet.comp a b hab) := by
      refine GroupoidStr.TransitionSet.ext ?_ ?_ ?_
      · exact congrArg (fun y : S.Tr Ψ Ψ' => y.src) hb
      · change C.toGroupoidStr.comp (Ta.srcInv (Tb.srcInv b.src).tgt).mor (Tb.srcInv b.src).mor =
          C.toGroupoidStr.comp a.mor b.mor
        rw [hb, ha]
      · change (Ta.srcInv (Tb.srcInv b.src).tgt).tgt = a.tgt
        rw [hb, ha]
    rw [he]
    exact Tab.mem_carrier
  have hG := Tab.eventuallyEq_srcInv hNo hbN hGc hGs hGab
  filter_upwards [hG, hNo.mem_nhds hbN] with x hx hxN
  change (Tab.srcInv x).tgt = (Ta.srcInv (Tb.srcInv x).tgt).tgt
  rw [← hx, hGval x hxN]
  rfl

end GermMap

/-! ### Face germs and their transport -/

section Germs

variable (S)

/-- The degeneracy index of the domain of a uniformizer of a tame polyfold structure satisfies
Part I's corner axioms (`MPolyfold.isCornerIndex_degIndex`). -/
theorem isTame_unif (hT : S.IsTame) (Ψ : S.Unif) : Ψ.1.P.IsTame :=
  hT _ _ Ψ.2.choose_spec

/-- The corner index of `O` for a uniformizer `Ψ` of a tame polyfold structure. -/
abbrev hdU (hT : S.IsTame) (Ψ : S.Unif) : IsCornerIndex Ψ.1.P.degIndex :=
  Ψ.1.P.isCornerIndex_degIndex (S.isTame_unif hT Ψ)

/-- **The face germs of `O`**: Part I's tame boundary `bO` (2021 Definition 2.7.10) of the domain
`O` of `Ψ`; its points over `x ∈ ∂O` are the classes `[x, V, θ]` of faces through `x`, two
being equal iff the faces agree near `x`. -/
abbrev bO (hT : S.IsTame) (Ψ : S.Unif) : Type u := BSpace (S.hdU hT Ψ)

variable {S} (hT : S.IsTame) {Ψ Ψ' Ψ'' : S.Unif}

/-- **`h` carries the face germ `p` at `s(h)` to the face germ `p'` at `t(h)`**: for an admissible
triple of `h`, the class `p'` is the image of `p` under `f = t ∘ (s|W(h))⁻¹` (2021 (17.58),
Definition 17.4.3 (2): `θ' = f_*^{Ψ,Ψ'} θ`). -/
def GermLift (h : S.Tr Ψ Ψ') (p : S.bO hT Ψ) (p' : S.bO hT Ψ') : Prop :=
  bMap (S.hdU hT Ψ) p = h.src ∧
    ∃ T : S.AdmissibleTriple h, IsLiftOf (S.hdU hT Ψ) (S.hdU hT Ψ') T.germMap p p'

variable {hT}

theorem GermLift.bMap_src {h : S.Tr Ψ Ψ'} {p : S.bO hT Ψ} {p' : S.bO hT Ψ'}
    (hl : S.GermLift hT h p p') : bMap (S.hdU hT Ψ) p = h.src := hl.1

theorem GermLift.bMap_tgt {h : S.Tr Ψ Ψ'} {p : S.bO hT Ψ} {p' : S.bO hT Ψ'}
    (hl : S.GermLift hT h p p') : bMap (S.hdU hT Ψ') p' = h.tgt := by
  obtain ⟨h1, T, hT'⟩ := hl
  rw [hT'.bMap_eq, h1]
  exact T.germMap_src

/-- **For every choice of `W(h)`**: the condition does not depend on the admissible triple. -/
theorem germLift_iff_forall {h : S.Tr Ψ Ψ'} {p : S.bO hT Ψ} {p' : S.bO hT Ψ'} :
    S.GermLift hT h p p' ↔ bMap (S.hdU hT Ψ) p = h.src ∧
      ∀ T : S.AdmissibleTriple h, IsLiftOf (S.hdU hT Ψ) (S.hdU hT Ψ') T.germMap p p' := by
  refine ⟨fun ⟨h1, T, hl⟩ => ⟨h1, fun T' => ?_⟩, fun ⟨h1, hl⟩ =>
    ⟨h1, (S.exists_admissibleTriple h).some, hl _⟩⟩
  obtain ⟨q, hq⟩ := exists_isLiftOf (S.hdU hT Ψ) (S.hdU hT Ψ') T'.isDHomeoOn_germMap
    (p := p) (by rw [h1]; exact T'.src_mem)
  have he : p' = q := hl.unique hq (by rw [h1]; exact germMap_eventuallyEq T T')
  rwa [he]

/-- **`θ'` is uniquely determined by `θ`** (2021 p. 790). -/
theorem germLift_unique {h : S.Tr Ψ Ψ'} {p : S.bO hT Ψ} {p₁ p₂ : S.bO hT Ψ'}
    (h₁ : S.GermLift hT h p p₁) (h₂ : S.GermLift hT h p p₂) : p₁ = p₂ := by
  obtain ⟨hb, T, hl₁⟩ := h₁
  exact hl₁.unique ((germLift_iff_forall.1 h₂).2 T) EventuallyEq.rfl

/-- **Existence of `f_*θ`**: every face germ at `s(h)` is carried by `h` to a face germ at
`t(h)`. -/
theorem exists_germLift (h : S.Tr Ψ Ψ') {p : S.bO hT Ψ} (hp : bMap (S.hdU hT Ψ) p = h.src) :
    ∃ p', S.GermLift hT h p p' := by
  let T := (S.exists_admissibleTriple h).some
  obtain ⟨q, hq⟩ := exists_isLiftOf (S.hdU hT Ψ) (S.hdU hT Ψ') T.isDHomeoOn_germMap
    (p := p) (by rw [hp]; exact T.src_mem)
  exact ⟨q, hp, T, hq⟩

/-- **The germ of `(q, 1, q)`** fixes every face germ at `q`. -/
theorem germLift_unit {q : Ψ.1.O} {p : S.bO hT Ψ} (hp : bMap (S.hdU hT Ψ) p = q) :
    S.GermLift hT (S.toTr (GroupoidStr.TransitionSet.unit q) : S.Tr Ψ Ψ) p p := by
  let T := (S.exists_admissibleTriple
    (S.toTr (GroupoidStr.TransitionSet.unit q) : S.Tr Ψ Ψ)).some
  obtain ⟨p', hp'⟩ := exists_isLiftOf (S.hdU hT Ψ) (S.hdU hT Ψ) T.isDHomeoOn_germMap
    (p := p) (by rw [hp]; exact T.src_mem)
  have he : p' = p := hp'.unique (isLiftOf_id (S.hdU hT Ψ) p)
    (by rw [hp]; exact germMap_unit_eventuallyEq q T)
  exact ⟨hp, T, he ▸ hp'⟩

/-- **`h⁻¹` carries `f_*θ` back to `θ`.** -/
theorem germLift_inv {h : S.Tr Ψ Ψ'} {p : S.bO hT Ψ} {p' : S.bO hT Ψ'}
    (hl : S.GermLift hT h p p') :
    S.GermLift hT (S.toTr (GroupoidStr.TransitionSet.inv h) : S.Tr Ψ' Ψ) p' p := by
  obtain ⟨h1, T, hTl⟩ := hl
  have h2 := GermLift.bMap_tgt ⟨h1, T, hTl⟩
  let T' := (S.exists_admissibleTriple
    (S.toTr (GroupoidStr.TransitionSet.inv h) : S.Tr Ψ' Ψ)).some
  obtain ⟨q, hq⟩ := exists_isLiftOf (S.hdU hT Ψ') (S.hdU hT Ψ) T'.isDHomeoOn_germMap
    (p := p') (by rw [h2]; exact T'.src_mem)
  have hcomp := hTl.comp hq
  have he : q = p := hcomp.unique (isLiftOf_id (S.hdU hT Ψ) p)
    (by rw [h1]; exact germMap_inv_comp_eventuallyEq T T')
  exact ⟨h2.trans (GroupoidStr.TransitionSet.src_inv h).symm, T', he ▸ hq⟩

/-- **The face germs compose**: `(h' ∘ h)_* = h'_* ∘ h_*`. -/
theorem germLift_comp {a : S.Tr Ψ' Ψ''} {b : S.Tr Ψ Ψ'}
    (hab : C.toGroupoidStr.src a.mor = C.toGroupoidStr.tgt b.mor) (hs : a.src = b.tgt)
    {p : S.bO hT Ψ} {p' : S.bO hT Ψ'} {p'' : S.bO hT Ψ''}
    (hb : S.GermLift hT b p p') (ha : S.GermLift hT a p' p'') :
    S.GermLift hT (S.toTr (GroupoidStr.TransitionSet.comp a b hab) : S.Tr Ψ Ψ'') p p'' := by
  obtain ⟨hb1, Tb, hbl⟩ := hb
  obtain ⟨ha1, Ta, hal⟩ := ha
  let Tab := (S.exists_admissibleTriple
    (S.toTr (GroupoidStr.TransitionSet.comp a b hab) : S.Tr Ψ Ψ'')).some
  obtain ⟨q, hq⟩ := exists_isLiftOf (S.hdU hT Ψ) (S.hdU hT Ψ'') Tab.isDHomeoOn_germMap
    (p := p) (by rw [hb1]; exact Tab.src_mem)
  have he : q = p'' := hq.unique (hbl.comp hal)
    (by rw [hb1]; exact germMap_comp_eventuallyEq a b hab hs Ta Tb Tab)
  exact ⟨hb1, Tab, he ▸ hq⟩

/-- **Germs at nearby points**: if `b` lies in `W(h)` and `f_h` carries the face germ `q` at
`s(b)` to `q'`, then `b` carries `q` to `q'`. -/
theorem germLift_of_mem_carrier {h b : S.Tr Ψ Ψ'} (T : S.AdmissibleTriple h)
    (hb : b ∈ T.carrier) {q : S.bO hT Ψ} {q' : S.bO hT Ψ'}
    (hq : bMap (S.hdU hT Ψ) q = b.src)
    (hl : IsLiftOf (S.hdU hT Ψ) (S.hdU hT Ψ') T.germMap q q') : S.GermLift hT b q q' := by
  let Tb := (S.exists_admissibleTriple b).some
  obtain ⟨r, hr⟩ := exists_isLiftOf (S.hdU hT Ψ) (S.hdU hT Ψ') Tb.isDHomeoOn_germMap
    (p := q) (by rw [hq]; exact Tb.src_mem)
  have he : r = q' := hr.unique hl (by rw [hq]; exact (germMap_eventuallyEq_of_mem T Tb hb).symm)
  exact ⟨hq, Tb, he ▸ hr⟩

/-- **The push-forward `f_*`** of a face germ at `s(h)` (2021 p. 790, `θ' = f_*^{Ψ,Ψ'}θ`). -/
def germPush (h : S.Tr Ψ Ψ') (p : S.bO hT Ψ) (hp : bMap (S.hdU hT Ψ) p = h.src) :
    S.bO hT Ψ' :=
  (exists_germLift h hp).choose

theorem germLift_germPush (h : S.Tr Ψ Ψ') (p : S.bO hT Ψ) (hp : bMap (S.hdU hT Ψ) p = h.src) :
    S.GermLift hT h p (germPush h p hp) :=
  (exists_germLift h hp).choose_spec

theorem germPush_eq {h : S.Tr Ψ Ψ'} {p : S.bO hT Ψ} {p' : S.bO hT Ψ'}
    (hl : S.GermLift hT h p p') : germPush h p hl.1 = p' :=
  germLift_unique (germLift_germPush h p hl.1) hl

end Germs

end GCT.PolyfoldConstruction

end Polyfold
