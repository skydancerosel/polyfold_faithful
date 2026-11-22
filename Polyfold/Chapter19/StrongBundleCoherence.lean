import Polyfold.Chapter19.StrongBundleAlternative
import Polyfold.Chapter19.StrongBundleTransport
import Polyfold.Chapter19.StrongBundleExamples
import Polyfold.Chapter10.StrongBundleLocalRegularity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.6 "A Strong Bundle Version", **"Alternative Approach"** (pp. 901–902): coherence
(**Definition 19.6.15**) for the lift of bundle transition data, the map `A` of (19.18) and the
equivalence "`C` is a strong bundle isomorphism covering `Id` iff `A ∘ C` is one covering `ι`".
Numbers and pages are the 2021 text's.

# Coherence of `(F̄, F)` and the map `A`

## The text, paraphrased

(Definition 19.6.15, p. 902) `(F̄, F)` is coherent if every `C = H'⁻¹ ∘ H :
M(Ψ, Ψ') ₛ×ₚ K → M(Ψ, Ψ') ₜ×ₚ' K'` is a strong bundle isomorphism.  (p. 902) The map
`A((q, φ, q'), k') = ((q', φ⁻¹, q), k')`, `A : M(Ψ, Ψ') ₜ×ₚ' K' → M(Ψ', Ψ) ₛ×ₚ' K'` (19.18), is a
strong bundle isomorphism covering the inversion `ι`, and `C` is a strong bundle isomorphism
covering `Id` iff `A ∘ C` is a strong bundle isomorphism covering `ι`.

## What is formalized (namespace `Polyfold.GroupoidalCategory.StrongBundleUniformizerConstruction`)

* `mem_image_map`, `altH_eq_mapBar`: over the sheet `F_h(V(o))` of `M(Ψ, Ψ')`, `H` is the lift
  `F̄_h ∘ π_K`, so `t ∘ H = f̄_h ∘ π_K`.
* `isLocalIso₂_altTheta`, `isStrongBundleMap_altTheta`, `isStrongBundleMap_altC`,
  `isLocalIso₂_altC`, `altCinv` (`C⁻¹ = H⁻¹ ∘ H'`), `altCinv_altC`, `altC_altCinv`, and
  **`isCoherent_of_bundleTransitionData`**: for bundle transition data `F̄` (Definition 19.6.4,
  requirement (A)), the data `(F̄, F)` are coherent.
* `trInv` (`ι : M(Ψ, Ψ') → M(Ψ', Ψ)`), `altA`, `altAinv`, **`isStrongBundleIso_altA`** (`A` is a
  strong bundle isomorphism covering `ι`, p. 902), **`altC_iso_iff_altA_comp`** (`C` is a strong
  bundle isomorphism covering `Id` iff `A ∘ C` is one covering `ι`).
* `reflBan_isCoherent`: the reflection bundle of `StrongBundleExamples` is coherent; its
  uniformizer set is non-empty (`reflΨ`), so the statement is not vacuous.

## Readings

* As in `StrongBundleAlternative`, the fibred products are the pull-backs of Definition 2.6.7 and
  "`C` is a strong bundle isomorphism" is read as: `C` is a strong bundle map covering `Id` and a
  strong bundle isomorphism over all of `M(Ψ, Ψ')`.
* "`A` is a strong bundle isomorphism covering `ι`" is read globally (`IsStrongBundleIso`, with
  the inverse `A⁻¹((q', φ⁻¹, q), k') = ((q, φ, q'), k')` covering `ι⁻¹ = ι`); "`A ∘ C` is a strong
  bundle isomorphism covering `ι`" is read as for `C`, over all of `M(Ψ, Ψ')`.
* The text treats coherence as an assumption of the alternative approach; we read the
  alternative approach as starting from transition data `F` alone, and show that when `F` is the
  underlying data of bundle transition data `F̄` (the first approach), coherence holds.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

namespace GroupoidalCategory

universe u

variable {C : GroupoidalCategory.{u}}

open GroupoidStr (TransitionSet)

namespace StrongBundleUniformizerConstruction

variable {μ : C.BanFunctor} {Fb : StrongBundleUniformizerConstruction μ}

/-! ### `H` over a sheet of `M(Ψ, Ψ')` -/

section Sheet

variable {F : Fb.base.TransitionData} {Ψ Ψ' : Fb.Unif}

/-- A point `h` of the sheet `F_k(V(o))` has `s(h) ∈ V(o)` and `F_k(s(h)) = h`. -/
theorem mem_image_map {k h : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1}
    (hh : h ∈ F.map _ _ k '' F.dom _ _ k) : h.src ∈ F.dom _ _ k ∧ F.map _ _ k h.src = h := by
  obtain ⟨q, hq, rfl⟩ := hh
  rw [F.src_map _ _ k q hq]
  exact ⟨hq, rfl⟩

/-- `h` lies on its own sheet `F_h(V(s(h)))`. -/
theorem mem_image_map_self (h : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1) :
    h ∈ F.map _ _ h '' F.dom _ _ h :=
  ⟨h.src, F.mem_dom _ _ h, F.map_src _ _ h⟩

/-- **Over the sheet `F_k(V(o))`, `H = F̄_k ∘ π_K`**: `H((h, a)) = F̄_k(a)`. -/
theorem altH_eq_mapBar {k : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1} (x : SrcPB F Ψ Ψ')
    (hx : (x.1.1 : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1) ∈ F.map _ _ k '' F.dom _ _ k) :
    altH F Ψ Ψ' x = Fb.mapBar F Ψ Ψ' k x.1.2 := by
  obtain ⟨h1, h2⟩ := mem_image_map hx
  have hp : (Fb.strU Ψ).p x.1.2 = (x.1.1 : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1).src :=
    x.2
  have hq : (Fb.strU Ψ).p x.1.2 ∈ F.dom _ _ k := by rw [hp]; exact h1
  refine ((mapBar_eq_iff hq).2 ⟨rfl, ?_⟩).symm
  rw [proj_altH, hp, h2]

variable (F Ψ Ψ')

theorem srcBundle_eq :
    srcBundle F Ψ Ψ' = (Fb.strU Ψ).B.pullback (isScSmoothMap_trSrc F Ψ Ψ') := rfl

theorem tgtBundle_eq :
    tgtBundle F Ψ Ψ' = (Fb.strU Ψ').B.pullback (isScSmoothMap_trTgt F Ψ Ψ') := rfl

/-- **`π_K` is a local strong bundle isomorphism over the sheet `F_k(V(o))`** covering
`s : F_k(V(o)) → V(o)` (p. 903). -/
theorem exists_isLocalIso₂_pullbackProj'_src (k : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1) :
    ∃ (g : (Fb.strU Ψ).O → F.Tr (Fb.baseUnif Ψ) (Fb.baseUnif Ψ')) (Ψπ : Ψ.1.O → SrcPB F Ψ Ψ'),
      (srcBundle F Ψ Ψ').IsLocalIso₂ (Fb.strU Ψ).B (trSrc F Ψ Ψ') g
        (pullbackProj' (Fb.strU Ψ).p (trSrc F Ψ Ψ')) Ψπ (F.map _ _ k '' F.dom _ _ k)
        (F.dom _ _ k) :=
  StrongBundle.IsStrongBundleIsoOn.exists_isLocalIso₂
    (StrongBundle.isStrongBundleIsoOn_pullbackProj' (Fb.strU Ψ).B (isScSmoothMap_trSrc F Ψ Ψ')
      (F.isScDiffeoOn_map (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') k).symm (F.toTr k))

end Sheet

/-! ### Coherence of the lift of bundle transition data -/

section Coherence

variable (Fbar : Fb.BundleTransitionData) (Ψ Ψ' : Fb.Unif)

/-- **`Θ = t ∘ H : M(Ψ, Ψ') ₛ×ₚ K → K'` is, over the sheet `F_k(V(o))`, a local strong bundle
isomorphism covering `t`**: there it is `f̄_k ∘ π_K` (Definition 19.6.4 (A)). -/
theorem isLocalIso₂_altTheta (k : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1) :
    ∃ (g : (Fb.strU Ψ').O → Fbar.toTD.Tr (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
      (Ψinv : Ψ'.1.O → SrcPB Fbar.toTD Ψ Ψ'),
      (srcBundle Fbar.toTD Ψ Ψ').IsLocalIso₂ (Fb.strU Ψ').B (trTgt Fbar.toTD Ψ Ψ') g
        (fun x => (altH Fbar.toTD Ψ Ψ' x).tgt) Ψinv
        (Fbar.toTD.map _ _ k '' Fbar.toTD.dom _ _ k)
        (Fbar.toTD.fmap _ _ k '' Fbar.toTD.dom _ _ k) := by
  obtain ⟨g, Ψπ, hπ⟩ := exists_isLocalIso₂_pullbackProj'_src Fbar.toTD Ψ Ψ' k
  obtain ⟨g₁, Φinv, hA⟩ := Fbar.diffeo_bar Ψ Ψ' k
  refine ⟨g ∘ g₁, Ψπ ∘ Φinv,
    ((hA.comp hπ).congr_base (fun x hx => ?_) fun _ _ => rfl).congr (fun w hw => ?_)
      fun _ _ => rfl⟩
  · obtain ⟨-, h2⟩ := mem_image_map hx
    change (x : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1).tgt =
      (Fbar.toTD.map _ _ k (x : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1).src).tgt
    rw [h2]
  · change (altH Fbar.toTD Ψ Ψ' w).tgt = (Fb.mapBar Fbar.toTD Ψ Ψ' k w.1.2).tgt
    rw [altH_eq_mapBar w hw]

/-- **`Θ = t ∘ H` is a strong bundle map covering `t`.** -/
theorem isStrongBundleMap_altTheta :
    (srcBundle Fbar.toTD Ψ Ψ').IsStrongBundleMap (Fb.strU Ψ').B (trTgt Fbar.toTD Ψ Ψ')
      (fun x => (altH Fbar.toTD Ψ Ψ' x).tgt) :=
  StrongBundle.IsStrongBundleMap.of_isLocalIso₂
    (fun _ => (Fb.strU Ψ).p_lift_tgt (Fb.strU Ψ') _ _ _) fun h₀ => by
      obtain ⟨g, Ψinv, hl⟩ := isLocalIso₂_altTheta Fbar Ψ Ψ' h₀
      exact ⟨_, _, g, Ψinv, mem_image_map_self h₀, hl⟩

/-- **`C = (π, t ∘ H)` is a strong bundle map covering the identity** of `M(Ψ, Ψ')`. -/
theorem isStrongBundleMap_altC :
    (srcBundle Fbar.toTD Ψ Ψ').IsStrongBundleMap (tgtBundle Fbar.toTD Ψ Ψ') id
      (altC Fbar.toTD Ψ Ψ') :=
  StrongBundle.isStrongBundleMap_pullbackPair (Fb.strU Ψ').B
    (isScSmoothMap_trTgt Fbar.toTD Ψ Ψ') (l := id) MPolyfold.isScSmoothMap_id
    (isStrongBundleMap_altTheta Fbar Ψ Ψ')

/-- **`C` is, over every sheet `F_k(V(o))`, a local strong bundle isomorphism covering `Id`.** -/
theorem isLocalIso₂_altC (k : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1) :
    ∃ Ψinv : TgtPB Fbar.toTD Ψ Ψ' → SrcPB Fbar.toTD Ψ Ψ',
      (srcBundle Fbar.toTD Ψ Ψ').IsLocalIso₂ (tgtBundle Fbar.toTD Ψ Ψ') id id
        (altC Fbar.toTD Ψ Ψ') Ψinv (Fbar.toTD.map _ _ k '' Fbar.toTD.dom _ _ k)
        (Fbar.toTD.map _ _ k '' Fbar.toTD.dom _ _ k) := by
  obtain ⟨g, Ψinv, hΘ⟩ := isLocalIso₂_altTheta Fbar Ψ Ψ' k
  obtain ⟨g', Ψt, hπt⟩ : ∃ (g' : (Fb.strU Ψ').O → Fbar.toTD.Tr (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
      (Ψt : Ψ'.1.O → TgtPB Fbar.toTD Ψ Ψ'),
      (tgtBundle Fbar.toTD Ψ Ψ').IsLocalIso₂ (Fb.strU Ψ').B (trTgt Fbar.toTD Ψ Ψ') g'
        (pullbackProj' (Fb.strU Ψ').p (trTgt Fbar.toTD Ψ Ψ')) Ψt
        (Fbar.toTD.map _ _ k '' Fbar.toTD.dom _ _ k)
        (Fbar.toTD.fmap _ _ k '' Fbar.toTD.dom _ _ k) :=
    StrongBundle.IsStrongBundleIsoOn.exists_isLocalIso₂
      (StrongBundle.isStrongBundleIsoOn_pullbackProj' (Fb.strU Ψ').B
        (isScSmoothMap_trTgt Fbar.toTD Ψ Ψ') hΘ.base (Fbar.toTD.toTr k))
  refine ⟨Ψinv ∘ pullbackProj' (Fb.strU Ψ').p (trTgt Fbar.toTD Ψ Ψ'),
    ((hπt.symm.comp hΘ).congr_base (fun x hx => (hπt.base.left_inv x hx).symm)
      fun y hy => (hΘ.base.left_inv y hy).symm).congr (fun w hw => ?_) fun _ _ => rfl⟩
  exact (hπt.left_inv (w := altC Fbar.toTD Ψ Ψ' w) hw).symm

end Coherence

section Inverse

variable (F : Fb.base.TransitionData) (Ψ Ψ' : Fb.Unif)

/-- **`C⁻¹ = H⁻¹ ∘ H'`**: `C⁻¹((q, φ, q'), k') = ((q, φ, q'), s(H'((q, φ, q'), k')))`. -/
def altCinv (y : TgtPB F Ψ Ψ') : SrcPB F Ψ Ψ' :=
  ⟨(y.1.1, (altH' F Ψ Ψ' y).src), congrArg TransitionSet.src (proj_altH' F Ψ Ψ' y)⟩

theorem altCinv_altC (x : SrcPB F Ψ Ψ') : altCinv F Ψ Ψ' (altC F Ψ Ψ' x) = x :=
  Subtype.ext (Prod.ext rfl (congrArg TransitionSet.src (altH'_altC F Ψ Ψ' x)))

theorem altH_altCinv (y : TgtPB F Ψ Ψ') : altH F Ψ Ψ' (altCinv F Ψ Ψ' y) = altH' F Ψ Ψ' y :=
  (Fb.strU Ψ).eq_of_proj (Fb.strU Ψ') rfl
    ((proj_altH F Ψ Ψ' _).trans (proj_altH' F Ψ Ψ' y).symm)

theorem altC_altCinv (y : TgtPB F Ψ Ψ') : altC F Ψ Ψ' (altCinv F Ψ Ψ' y) = y :=
  Subtype.ext (Prod.ext rfl
    ((congrArg TransitionSet.tgt (altH_altCinv F Ψ Ψ' y)).trans (tgt_altH' F Ψ Ψ' y)))

end Inverse

/-- **The lift of bundle transition data is coherent** (Definition 19.6.15): for bundle
transition data `F̄` (Definition 19.6.4), every `C = H'⁻¹ ∘ H` is a strong bundle isomorphism
covering the identity of `M(Ψ, Ψ')`. -/
theorem isCoherent_of_bundleTransitionData (Fbar : Fb.BundleTransitionData) :
    IsCoherent Fbar.toTD := fun Ψ Ψ' =>
  ⟨isStrongBundleMap_altC Fbar Ψ Ψ',
    StrongBundle.isStrongBundleIsoOn_univ_of_local (isStrongBundleMap_altC Fbar Ψ Ψ')
      (altCinv Fbar.toTD Ψ Ψ') (altCinv_altC Fbar.toTD Ψ Ψ') (altC_altCinv Fbar.toTD Ψ Ψ')
      fun h₀ => by
        obtain ⟨Ψinv, hl⟩ := isLocalIso₂_altC Fbar Ψ Ψ' h₀
        exact ⟨_, mem_image_map_self h₀,
          hl.isStrongBundleIsoOn (isStrongBundleMap_altC Fbar Ψ Ψ')⟩⟩

/-! ### The map `A` of (19.18) -/

section MapA

variable (F : Fb.base.TransitionData) (Ψ Ψ' : Fb.Unif)

/-- The inversion `ι : M(Ψ, Ψ') → M(Ψ', Ψ)`. -/
abbrev trInv : F.Tr (Fb.baseUnif Ψ) (Fb.baseUnif Ψ') → F.Tr (Fb.baseUnif Ψ') (Fb.baseUnif Ψ) :=
  fun a => F.toTr (a : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1).inv

theorem trInv_trInv (a : F.Tr (Fb.baseUnif Ψ) (Fb.baseUnif Ψ')) :
    trInv F Ψ' Ψ (trInv F Ψ Ψ' a) = a :=
  TransitionSet.inv_inv (a : (Fb.baseUnif Ψ).1.Trans (Fb.baseUnif Ψ').1)

/-- **2021 (19.18), p. 902: `A((q, φ, q'), k') = ((q', φ⁻¹, q), k')`**,
`A : M(Ψ, Ψ') ₜ×ₚ' K' → M(Ψ', Ψ) ₛ×ₚ' K'`. -/
def altA (x : TgtPB F Ψ Ψ') : SrcPB F Ψ' Ψ := ⟨(trInv F Ψ Ψ' x.1.1, x.1.2), x.2⟩

/-- `A⁻¹((q', φ⁻¹, q), k') = ((q, φ, q'), k')`. -/
def altAinv (y : SrcPB F Ψ' Ψ) : TgtPB F Ψ Ψ' := ⟨(trInv F Ψ' Ψ y.1.1, y.1.2), y.2⟩

theorem altAinv_altA (x : TgtPB F Ψ Ψ') : altAinv F Ψ Ψ' (altA F Ψ Ψ' x) = x :=
  Subtype.ext (Prod.ext (trInv_trInv F Ψ Ψ' x.1.1) rfl)

theorem altA_altAinv (y : SrcPB F Ψ' Ψ) : altA F Ψ Ψ' (altAinv F Ψ Ψ' y) = y :=
  Subtype.ext (Prod.ext (trInv_trInv F Ψ' Ψ y.1.1) rfl)

/-- **`A` is a strong bundle map covering `ι`.** -/
theorem isStrongBundleMap_altA :
    (tgtBundle F Ψ Ψ').IsStrongBundleMap (srcBundle F Ψ' Ψ) (trInv F Ψ Ψ') (altA F Ψ Ψ') :=
  StrongBundle.isStrongBundleMap_pullbackPair (Fb.strU Ψ').B (isScSmoothMap_trSrc F Ψ' Ψ)
    (l := trInv F Ψ Ψ') (F.isScSmoothMap_inv (Fb.baseUnif Ψ) (Fb.baseUnif Ψ'))
    ((Fb.strU Ψ').B.isStrongBundleMap_pullbackProj' (isScSmoothMap_trTgt F Ψ Ψ'))

/-- **`A⁻¹` is a strong bundle map covering `ι`.** -/
theorem isStrongBundleMap_altAinv :
    (srcBundle F Ψ' Ψ).IsStrongBundleMap (tgtBundle F Ψ Ψ') (trInv F Ψ' Ψ) (altAinv F Ψ Ψ') :=
  StrongBundle.isStrongBundleMap_pullbackPair (Fb.strU Ψ').B (isScSmoothMap_trTgt F Ψ Ψ')
    (l := trInv F Ψ' Ψ) (F.isScSmoothMap_inv (Fb.baseUnif Ψ') (Fb.baseUnif Ψ))
    ((Fb.strU Ψ').B.isStrongBundleMap_pullbackProj' (isScSmoothMap_trSrc F Ψ' Ψ))

/-- **2021 p. 902: `A` is a strong bundle isomorphism covering `ι`** (with inverse `A⁻¹`
covering `ι⁻¹ = ι`). -/
theorem isStrongBundleIso_altA :
    (tgtBundle F Ψ Ψ').IsStrongBundleIso (srcBundle F Ψ' Ψ) (trInv F Ψ Ψ') (altA F Ψ Ψ')
      (trInv F Ψ' Ψ) (altAinv F Ψ Ψ') :=
  ⟨isStrongBundleMap_altA F Ψ Ψ', isStrongBundleMap_altAinv F Ψ Ψ', altAinv_altA F Ψ Ψ',
    altA_altAinv F Ψ Ψ'⟩

/-- **2021 p. 902: `C` is a strong bundle isomorphism covering `Id` iff `A ∘ C` is a strong
bundle isomorphism covering `ι`.** -/
theorem altC_iso_iff_altA_comp :
    (∃ h : (srcBundle F Ψ Ψ').IsStrongBundleMap (tgtBundle F Ψ Ψ') id (altC F Ψ Ψ'),
      (srcBundle F Ψ Ψ').IsStrongBundleIsoOn (tgtBundle F Ψ Ψ') h univ univ) ↔
    (∃ h : (srcBundle F Ψ Ψ').IsStrongBundleMap (srcBundle F Ψ' Ψ) (trInv F Ψ Ψ')
        (altA F Ψ Ψ' ∘ altC F Ψ Ψ'),
      (srcBundle F Ψ Ψ').IsStrongBundleIsoOn (srcBundle F Ψ' Ψ) h univ univ) := by
  have hA := isStrongBundleIso_altA F Ψ Ψ'
  constructor
  · rintro ⟨hC, hCi⟩
    exact ⟨hA.toMap.comp hC, hA.isStrongBundleIsoOn_univ.comp hCi⟩
  · rintro ⟨hAC, hACi⟩
    have hcomp := hA.symm.isStrongBundleIsoOn_univ.comp hACi
    have e1 : trInv F Ψ' Ψ ∘ trInv F Ψ Ψ' = id := funext (trInv_trInv F Ψ Ψ')
    have e2 : altAinv F Ψ Ψ' ∘ (altA F Ψ Ψ' ∘ altC F Ψ Ψ') = altC F Ψ Ψ' :=
      funext fun x => altAinv_altA F Ψ Ψ' (altC F Ψ Ψ' x)
    have h' : (srcBundle F Ψ Ψ').IsStrongBundleMap (tgtBundle F Ψ Ψ') id (altC F Ψ Ψ') := by
      rw [← e2]; exact (hA.symm.toMap.comp hAC).congr_base e1
    exact ⟨h', (hcomp.of_eq e1).of_eq_map e2 h'⟩

/-- **Coherence in terms of `A ∘ C`** (p. 902): every `A ∘ C : M(Ψ, Ψ') ₛ×ₚ K → M(Ψ', Ψ) ₛ×ₚ' K'`
is a strong bundle isomorphism covering `ι`. -/
def IsCoherentA : Prop :=
  ∀ Ψ Ψ' : Fb.Unif, ∃ h : (srcBundle F Ψ Ψ').IsStrongBundleMap (srcBundle F Ψ' Ψ) (trInv F Ψ Ψ')
      (altA F Ψ Ψ' ∘ altC F Ψ Ψ'),
    (srcBundle F Ψ Ψ').IsStrongBundleIsoOn (srcBundle F Ψ' Ψ) h univ univ

/-- **`(F̄, F)` is coherent iff every `A ∘ C` is a strong bundle isomorphism covering `ι`.** -/
theorem isCoherent_iff_isCoherentA : IsCoherent F ↔ IsCoherentA F :=
  forall₂_congr fun Ψ Ψ' => altC_iso_iff_altA_comp F Ψ Ψ'

end MapA

end StrongBundleUniformizerConstruction

/-! ### The witness -/

open StrongBundleUniformizerConstruction in
/-- **The reflection bundle is coherent** (Definition 19.6.15); `reflBanU` has the uniformizer
`reflΨ`, so the statement is not vacuous. -/
theorem reflBan_isCoherent : IsCoherent reflBanBTD.toTD :=
  isCoherent_of_bundleTransitionData reflBanBTD

open StrongBundleUniformizerConstruction in
/-- For the reflection bundle, every `A ∘ C` is a strong bundle isomorphism covering `ι`. -/
theorem reflBan_isCoherentA : IsCoherentA reflBanBTD.toTD :=
  (isCoherent_iff_isCoherentA reflBanBTD.toTD).1 reflBan_isCoherent

end GroupoidalCategory

end Polyfold
