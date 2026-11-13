import Polyfold.Chapter10.StrongBundleLocalIso
import Polyfold.Chapter10.StrongBundleLocalizationSections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10: **Proposition 10.4.6** (§10.4, p. 501, new in the 2021 edition) and
**Proposition 10.5.6** (§10.5, p. 508, new in the 2021 edition), with Definition 8.4.2 read as
`EpStrongBundle.IsLRLocal` (strong bundle isomorphisms of `W|U(x)`).  Numbers and pages are the
2021 text's.

# The local regularity property of strong bundles under equivalences

## The text, paraphrased

(Proposition 10.4.6) If `Φ` is a strong bundle equivalence `(P : V → X, μ) → (Q : W → Y, ν)`
covering `F : X → Y` and one of the strong bundles has the local regularity property of
Definition 8.4.2, so has the other.  *Proof* (text): for `ψ : F(x) → y` the composite
`V|U(x) → W|U(F(x)) → W|U(y)` of `Φ` and of the transport `H_ψ̂` is a strong bundle isomorphism,
equivariant along `g ↦ ψ ∘ F(g) ∘ ψ⁻¹`; so `V|U(x)` has the property iff `W|U(y)` has it, "a
strong bundle version of Proposition 10.1.9", left to the reader.

(Proposition 10.5.6) The property passes along generalized strong bundle isomorphisms; the proof
follows the ep-groupoid case.

## What is formalized

* `EpStrongBundle.HasLRLocal` (the condition of Definition 8.4.2 on one `U(x)`), with
  `isLRLocal_iff_hasLRLocal`.
* `EpStrongBundle.hasLRLocal_iff_of_equivariant`: the two conjugation arguments of the proof, for
  any local strong bundle isomorphism `H : W|U(x) → W'|U(y)` intertwining the natural lifts
  along a surjection `G_x → G_y` and preserving and reflecting orbit equality.
* `EpStrongBundle.IsStrongBundleEquivalence.exists_transport`: the text's `H_ψ̂ ∘ Φ`,
  `v ↦ ν(ψ_{P(v)}, Φ(v))`, is a local strong bundle isomorphism `V|S → W|Q(S)` covering the chart
  `Q = ψ̂ ∘ F` of `EpFunctor.TransportChart`, near `x`; `transport_natLift` is its equivariance,
  `π_transport_iff` its orbit property.
* **`EpStrongBundle.proposition_10_4_6`** (**Proposition 10.4.6**), and
  **`SBLocalization.proposition_10_5_6`** (**Proposition 10.5.6**), from
  `GenSBMap.iff_of_isGeneralizedIso`.

## The choices made

* Definition 8.4.2 is read as `IsLRLocal` (Findings, Chapter 10, item 72): the text's `B` is a
  strong bundle isomorphism of `W|U(x)` only.  With the formal `EpStrongBundle.IsLR`, which asks
  the conclusion only of strong bundle maps defined on all of `W`, the conjugate `H⁻¹ ∘ B ∘ H` of
  the proof is defined on `V|U(x)` only, and the argument does not apply.
* "`Φ : W → W`" in the statement is read `Φ : V → W` (a reading point, Findings item 57).
* `U(y) = Q(U(x))` "with the natural action" is `EpFunctor.TransportChart.exists_naturalRep_push`
  (and `exists_naturalRep_pull` for the converse), as in Proposition 10.1.9.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### A base-map congruence for `IsLocalIso₂` -/

section Congr

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]

namespace StrongBundle.IsLocalIso₂

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {f : X → X'} {g : X' → X}
  {Φ : Y → Y'} {Ψ : Y' → Y} {U : Set X} {U' : Set X'}

/-- Changing the base maps on `U` and `U'`. -/
theorem congr_base (h : B.IsLocalIso₂ B' f g Φ Ψ U U') {f₂ : X → X'} {g₂ : X' → X}
    (hf : ∀ x ∈ U, f₂ x = f x) (hg : ∀ y ∈ U', g₂ y = g y) :
    B.IsLocalIso₂ B' f₂ g₂ Φ Ψ U U' where
  base := by
    have b := h.base
    exact ⟨b.isScSmoothOn.congr fun x hx => (hf x hx).symm,
      b.isScSmoothOn_inv.congr fun y hy => (hg y hy).symm,
      fun x hx => by show f₂ x ∈ U'; rw [hf x hx]; exact b.mapsTo hx,
      fun y hy => by show g₂ y ∈ U; rw [hg y hy]; exact b.mapsTo_inv hy,
      fun x hx => by rw [hf x hx, hg _ (b.mapsTo hx)]; exact b.left_inv x hx,
      fun y hy => by rw [hg y hy, hf _ (b.mapsTo_inv hy)]; exact b.right_inv y hy⟩
  fiber_linear x hx := let ⟨L, hL⟩ := h.fiber_linear x hx
    ⟨(fiberCast P' (hf x hx).symm).comp L, fun v => by
      simp only [LinearMap.coe_comp, Function.comp_apply, fiberCast_val, hL]⟩
  fiber_linear_inv y hy := let ⟨L, hL⟩ := h.fiber_linear_inv y hy
    ⟨(fiberCast P (hg y hy).symm).comp L, fun v => by
      simp only [LinearMap.coe_comp, Function.comp_apply, fiberCast_val, hL]⟩
  zero := h.zero
  one := h.one

end StrongBundle.IsLocalIso₂

end Congr

/-! ### Definition 8.4.2 on one neighbourhood, and its transport -/

section HasLR

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {Y : EpGroupoid Obj' Mor'}
  {W' : Type u} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle Y.PObj P'}

namespace EpStrongBundle

variable (E : EpStrongBundle X B) (E' : EpStrongBundle Y B')

/-- The condition of Definition 8.4.2 (read as `IsLRLocal`) on one natural representation `U(x)`:
every strong bundle isomorphism `Φ` of `W|U(x)` with `|Φ(w)| = |w|` is `w ↦ g ∗ w`. -/
def HasLRLocal {x : Obj} (R : X.NaturalRep x) : Prop :=
  ∀ (β : Obj → Obj) (Φ : W → W), B.IsLocalIsoOn β Φ R.U →
    (∀ w, P w ∈ R.U → E.toGroupoidStr.π (Φ w) = E.toGroupoidStr.π w) →
    ∃ g : X.Isotropy x, ∀ w (hw : P w ∈ R.U), Φ w = E.natLift R g w hw

theorem isLRLocal_iff_hasLRLocal : E.IsLRLocal ↔ ∀ (x : Obj) (O : Set Obj), IsOpen O → x ∈ O →
    ∃ R : X.NaturalRep x, R.U ⊆ O ∧ E.HasLRLocal R :=
  Iff.rfl

variable {E E'}

/-- **Definition 8.4.2 for conjugate neighbourhoods**: if a local strong bundle isomorphism
`H : W|U(x) → W'|U(y)` intertwines the natural lifts along a surjection `e : G_x → G_y` and
preserves and reflects orbit equality, then `U(x)` has the property of Definition 8.4.2 iff
`U(y)` has it (`H⁻¹ ∘ B ∘ H` and `H ∘ B ∘ H⁻¹`). -/
theorem hasLRLocal_iff_of_equivariant {x : Obj} {y : Obj'} (R : X.NaturalRep x)
    (R' : Y.NaturalRep y) {q : Obj → Obj'} {q' : Obj' → Obj} {H : W → W'} {H' : W' → W}
    (hH : B.IsLocalIso₂ B' q q' H H' R.U R'.U) (e : X.Isotropy x → Y.Isotropy y)
    (he : Surjective e)
    (hequiv : ∀ g w, P w ∈ R.U →
      H (E.lrAct (R.Γ g (P w)) w) = E'.lrAct (R'.Γ (e g) (P' (H w))) (H w))
    (hπ : ∀ a b, P a ∈ R.U → P b ∈ R.U →
      (E.toGroupoidStr.π a = E.toGroupoidStr.π b ↔
        E'.toGroupoidStr.π (H a) = E'.toGroupoidStr.π (H b))) :
    E.HasLRLocal R ↔ E'.HasLRLocal R' := by
  constructor
  · intro h γ Θ hΘ hΘπ
    obtain ⟨γ', Θ', hΘ₂⟩ := hΘ.exists_isLocalIso₂
    have hC := hH.symm.comp (hΘ₂.comp hH)
    obtain ⟨g, hg⟩ := h _ _ hC.isLocalIsoOn fun w hw => by
      have h1 : P' (Θ (H w)) ∈ R'.U := hΘ₂.mapsTo (hH.mapsTo hw)
      refine (hπ _ w (hH.mapsTo_inv h1) hw).2 ?_
      simp only [hH.right_inv h1]
      exact hΘπ _ (hH.mapsTo hw)
    refine ⟨e g, fun w' hw' => ?_⟩
    have hw : P (H' w') ∈ R.U := hH.mapsTo_inv hw'
    have h1 := hg _ hw
    simp only [Function.comp_apply, hH.right_inv hw'] at h1
    rw [natLift_eq_lrAct]
    calc Θ w' = H (H' (Θ w')) := (hH.right_inv (hΘ₂.mapsTo hw')).symm
      _ = H (E.lrAct (R.Γ g (P (H' w'))) (H' w')) := by rw [h1, natLift_eq_lrAct]
      _ = E'.lrAct (R'.Γ (e g) (P' (H (H' w')))) (H (H' w')) := hequiv g _ hw
      _ = E'.lrAct (R'.Γ (e g) (P' w')) w' := by rw [hH.right_inv hw']
  · intro h β Θ hΘ hΘπ
    obtain ⟨β', Θ', hΘ₂⟩ := hΘ.exists_isLocalIso₂
    have hC := hH.comp (hΘ₂.comp hH.symm)
    obtain ⟨k, hk⟩ := h _ _ hC.isLocalIsoOn fun w' hw' => by
      have h0 : P (H' w') ∈ R.U := hH.mapsTo_inv hw'
      have h1 : P (Θ (H' w')) ∈ R.U := hΘ₂.mapsTo h0
      have h2 := (hπ _ _ h1 h0).1 (hΘπ _ h0)
      simp only [Function.comp_apply]
      rwa [hH.right_inv hw'] at h2
    obtain ⟨g, rfl⟩ := he k
    refine ⟨g, fun w hw => ?_⟩
    have hHw : P' (H w) ∈ R'.U := hH.mapsTo hw
    have h1 := hk _ hHw
    simp only [Function.comp_apply, hH.left_inv hw] at h1
    have hΓ : P (E.lrAct (R.Γ g (P w)) w) ∈ R.U := by
      rw [P_lrAct (R.src_Γ g _ hw).symm, R.tgt_Γ g _ hw]; exact R.mapsTo_Φ g hw
    rw [natLift_eq_lrAct]
    calc Θ w = H' (H (Θ w)) := (hH.left_inv (hΘ₂.mapsTo hw)).symm
      _ = H' (E'.lrAct (R'.Γ (e g) (P' (H w))) (H w)) := by rw [h1, natLift_eq_lrAct]
      _ = H' (H (E.lrAct (R.Γ g (P w)) w)) := by rw [hequiv g w hw]
      _ = E.lrAct (R.Γ g (P w)) w := hH.left_inv hΓ

end EpStrongBundle

end HasLR

/-! ### The transport `H_ψ̂ ∘ Φ` along a strong bundle equivalence -/

section Transport

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {Y : EpGroupoid Obj' Mor'}
  {W' : Type u} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle Y.PObj P'}
  [ParacompactSpace (pullbackSpace P' Y.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle Y B'}

namespace EpStrongBundle

/-- `Φ(μ(γ, w)) = μ'(ϕ(γ), Φ(w))` ((10.14)), in the total form `lrAct`. -/
theorem IsStrongBundleFunctor.obj_lrAct {ϕ : EpFunctor X Y}
    {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (h : E.IsStrongBundleFunctor E' ϕ Φ)
    {γ : Mor} {w : W} (hw : P w = X.src γ) :
    Φ.obj (E.lrAct γ w) = E'.lrAct (ϕ.mor γ) (Φ.obj w) := by
  have hw' : P' (Φ.obj w) = Y.src (ϕ.mor γ) := by
    rw [h.isStrongBundleMap_obj.covers, hw, ϕ.src_mor]
  rw [lrAct_eq hw, lrAct_eq hw', h.isMap.map_μ γ w hw]

namespace IsStrongBundleEquivalence

variable {ϕ : EpFunctor X Y} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (h : E.IsStrongBundleEquivalence E' ϕ Φ)
include h

/-- **The text's `H_ψ̂ ∘ Φ` is a local strong bundle isomorphism** (2021 p. 501): for a chart
`Q = ψ̂ ∘ ϕ` along `ψ : ϕ(x) → y` (`EpFunctor.TransportChart`, with `ψ_u : ϕ(u) → Q(u)`), every
neighbourhood of `x` contains an open `S ∋ x` inside the chart such that
`v ↦ μ'(ψ_{P(v)}, Φ(v))` is a strong bundle isomorphism `V|S → W|Q(S)` covering `Q`. -/
theorem exists_transport {x : Obj} {y : Obj'} (T : ϕ.TransportChart x y) :
    ∃ S : Set Obj, IsOpen S ∧ x ∈ S ∧ S ⊆ T.W ∧ ∃ H' : W' → W,
      B.IsLocalIso₂ B' T.Q T.Qinv (fun v => E'.lrAct (T.ψ (P v)) (Φ.obj v)) H' S (T.Q '' S) := by
  have hs := h.isStrongBundleFunctor
  obtain ⟨UF, UF', hxF, hiF⟩ := h.isLocalStrongBundleIso_obj x
  obtain ⟨gF, ΨF, hF⟩ := hiF.exists_isLocalIso₂
  -- the family `m(y') = ψ_{g_F(y')}` over `D = U_F' ∩ g_F⁻¹(U_F ∩ W)`
  have hDo : IsOpen (UF' ∩ gF ⁻¹' (UF ∩ T.W)) :=
    hF.base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hF.base.isOpen_target
      (hF.base.isOpen_source.inter T.isOpen_W)
  have h1 := hF.base.symm.restrict hDo inter_subset_left
  have hsubW : UF ∩ ϕ.obj ⁻¹' (UF' ∩ gF ⁻¹' (UF ∩ T.W)) ⊆ T.W := fun z hz => by
    have h := hz.2.2
    rw [mem_preimage, hF.base.left_inv z hz.1] at h
    exact h.2
  have hγ := (T.isScDiffeoOn_image h1.isOpen_target hsubW).comp h1
  have hm : Y.PObj.IsScSmoothOn Y.PMor (fun y' => T.ψ (gF y')) (UF' ∩ gF ⁻¹' (UF ∩ T.W)) :=
    MPolyfold.IsScSmoothOn.comp T.isScSmoothOn_ψ
      (hF.base.isScSmoothOn_inv.mono hDo inter_subset_left) fun y' hy' => hy'.2.2
  have hL := isLocalIso₂_lrAct (E := E') hm
    (fun y' hy' => by rw [T.src_ψ _ hy'.2.2, hF.base.right_inv y' hy'.1])
    (fun y' hy' => T.tgt_ψ _ hy'.2.2) hγ
  have hC := hL.comp (hF.restrict_target hDo inter_subset_left)
  set S₀ := UF ∩ ϕ.obj ⁻¹' (UF' ∩ gF ⁻¹' (UF ∩ T.W))
  have hxS : x ∈ S₀ := ⟨hxF, hF.base.mapsTo hxF, by
    rw [mem_preimage, hF.base.left_inv x hxF]; exact ⟨hxF, T.mem_W⟩⟩
  refine ⟨S₀, h1.isOpen_target, hxS, hsubW,
    ΨF ∘ fun w => E'.lrAct (Y.inv (T.ψ (gF ((ϕ.obj ∘ T.Qinv) (P' w))))) w, ?_⟩
  refine (hC.congr_base (fun z hz => ?_) (fun y' hy' => ?_)).congr (fun v hv => ?_) (fun _ _ => rfl)
  · simp only [Function.comp_apply, hF.base.left_inv z hz.1]
  · obtain ⟨z, hz, rfl⟩ := hy'
    simp only [Function.comp_apply, T.isScDiffeoOn_Q.left_inv z (hsubW hz),
      hF.base.left_inv z hz.1]
  · simp only [Function.comp_apply, hs.isStrongBundleMap_obj.covers, hF.base.left_inv _ hv.1]

/-- `P'(μ'(ψ_{P(v)}, Φ(v))) = Q(P(v))`. -/
theorem P_transport {x : Obj} {y : Obj'} (T : ϕ.TransportChart x y) {w : W} (hw : P w ∈ T.W) :
    P' (E'.lrAct (T.ψ (P w)) (Φ.obj w)) = T.Q (P w) := by
  rw [P_lrAct (E := E') (m := T.ψ (P w)) (w := Φ.obj w) (by rw [h.covers, T.src_ψ _ hw]),
    T.tgt_ψ _ hw]

/-- **The equivariance of `H_ψ̂ ∘ Φ`** (2021 p. 501): along `g ↦ ψ ∘ ϕ(g) ∘ ψ⁻¹`,
`H(g ∗ w) = (ψ ∘ ϕ(g) ∘ ψ⁻¹) ∗ H(w)` for `H(w) = μ'(ψ_{P(w)}, Φ(w))`, under the hypotheses of
`EpFunctor.TransportChart.Γ_conj` (from which it follows with (10.14)). -/
theorem transport_Γ {x : Obj} {y : Obj'} (T : ϕ.TransportChart x y) (R : X.NaturalRep x)
    (R'' : Y.NaturalRep y) (g : X.Isotropy x) {V : Set Obj} (hVU : V ⊆ R.U) (hVW : V ⊆ T.W)
    (hgW : ∀ u ∈ V, R.Φ g u ∈ T.W) (hV : IsPreconnected V) (hxV : x ∈ V)
    (hQV : ∀ u ∈ V, T.Q u ∈ R''.U) {w : W} (hw : P w ∈ V) :
    E'.lrAct (T.ψ (P (E.lrAct (R.Γ g (P w)) w))) (Φ.obj (E.lrAct (R.Γ g (P w)) w)) =
      E'.lrAct (R''.Γ (T.conj g) (T.Q (P w))) (E'.lrAct (T.ψ (P w)) (Φ.obj w)) := by
  have hγ : P w = X.src (R.Γ g (P w)) := (R.src_Γ g _ (hVU hw)).symm
  have hPγ : P (E.lrAct (R.Γ g (P w)) w) = R.Φ g (P w) := by
    rw [P_lrAct hγ, R.tgt_Γ g _ (hVU hw)]
  have hΦw : P' (Φ.obj w) = Y.src (ϕ.mor (R.Γ g (P w))) := by rw [h.covers, ϕ.src_mor, ← hγ]
  have hΦw' : P' (Φ.obj w) = Y.src (T.ψ (P w)) := by rw [h.covers, T.src_ψ _ (hVW hw)]
  rw [hPγ, h.isStrongBundleFunctor.obj_lrAct hγ,
    ← lrAct_comp hΦw (T.src_ψ_Φ R g hVU hgW hw),
    T.Γ_conj R R'' g hVU hVW hgW hV hxV hQV _ hw,
    lrAct_comp (by rw [P_lrAct hΦw', Y.src_inv]) (T.src_comp_ψ_Φ R g hVU hVW hgW hw),
    lrAct_inv_lrAct hΦw']

/-- `H_ψ̂ ∘ Φ` preserves and reflects orbit equality (`Φ` is full, `μ'` preserves orbits). -/
theorem π_transport_iff {x : Obj} {y : Obj'}
    (T : ϕ.TransportChart x y) {a b : W} (ha : P a ∈ T.W) (hb : P b ∈ T.W) :
    E.toGroupoidStr.π a = E.toGroupoidStr.π b ↔
      E'.toGroupoidStr.π (E'.lrAct (T.ψ (P a)) (Φ.obj a)) =
        E'.toGroupoidStr.π (E'.lrAct (T.ψ (P b)) (Φ.obj b)) := by
  rw [π_lrAct (by rw [h.covers, T.src_ψ _ ha]), π_lrAct (by rw [h.covers, T.src_ψ _ hb])]
  exact ((Φ.injective_orbitMap_of_full h.isEquivalence.full).eq_iff
    (a := E.toEpGroupoid.π a) (b := E.toEpGroupoid.π b)).symm

end IsStrongBundleEquivalence

/-! ### Proposition 10.4.6 -/

/-- **2021 Proposition 10.4.6, p. 501 (new in the 2021 edition)**, with Definition 8.4.2 read as
`IsLRLocal`: if `Φ : (P : V → X, μ) → (P' : W → Y, ν)` is a strong bundle equivalence (covering
`ϕ`), `(P, μ)` has the local regularity property iff `(P', ν)` has it.  The text's proof: the
transport `H_ψ̂ ∘ Φ` (`IsStrongBundleEquivalence.exists_transport`) conjugates the neighbourhoods
(`hasLRLocal_iff_of_equivariant`), with `U(y) = Q(U(x))` (`exists_naturalRep_push`) for one
direction, and `y = ϕ(x)`, `ψ = 1` (`exists_naturalRep_pull`) for the other. -/
theorem proposition_10_4_6 {ϕ : EpFunctor X Y} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (h : E.IsStrongBundleEquivalence E' ϕ Φ) : E.IsLRLocal ↔ E'.IsLRLocal := by
  have hF := h.isEquivalence_base
  constructor
  · intro hE y O hO hyO
    obtain ⟨x, ψ₀, hs, ht⟩ := hF.exists_iso y
    obtain ⟨T, -⟩ := EpFunctor.exists_transportChart hF.isLocalScDiffeo_obj hs ht
    obtain ⟨S, hSo, hxS, hSW, H', hH⟩ := h.exists_transport T
    obtain ⟨R'₀, hR'₀⟩ := Y.theorem_7_1_13 y (hO.inter hH.base.isOpen_target)
      ⟨hyO, x, hxS, T.Q_self⟩
    have hO' : IsOpen (S ∩ T.Q ⁻¹' R'₀.U) :=
      (T.continuousOn_Q.mono hSW).isOpen_inter_preimage hSo R'₀.isOpen_U
    obtain ⟨R, hRO', hRLR⟩ := hE x _ hO'
      ⟨hxS, by rw [mem_preimage, T.Q_self]; exact R'₀.mem_U⟩
    have hRW : R.U ⊆ T.W ∩ T.Q ⁻¹' R'₀.U := fun u hu => ⟨hSW (hRO' hu).1, (hRO' hu).2⟩
    obtain ⟨R', hR'U, -, hR'Γ, -⟩ := T.exists_naturalRep_push hF R R'₀ hRW
    have hHR := hH.restrict_image R.isOpen_U fun u hu => (hRO' hu).1
    rw [← hR'U] at hHR
    refine ⟨R', ?_, (hasLRLocal_iff_of_equivariant R R' hHR T.conj (T.bijective_conj hF).2
      (fun g w hw => ?_) fun a b ha hb => h.π_transport_iff T (hRW ha).1 (hRW hb).1).1 hRLR⟩
    · rw [hR'U]
      rintro _ ⟨u, hu, rfl⟩
      exact (hR'₀ (hRO' hu).2).1
    · rw [hR'Γ, h.P_transport T (hRW hw).1]
      exact h.transport_Γ T R R'₀ g subset_rfl (fun u hu => (hRW hu).1)
        (fun u hu => (hRW (R.mapsTo_Φ g hu)).1) R.isConnected_U.isPreconnected R.mem_U
        (fun u hu => (hRW hu).2) hw
  · intro hE' x O hO hxO
    obtain ⟨T, -⟩ := EpFunctor.exists_transportChart hF.isLocalScDiffeo_obj
      (Y.src_unit (ϕ.obj x)) (Y.tgt_unit (ϕ.obj x))
    obtain ⟨S, hSo, hxS, hSW, H', hH⟩ := h.exists_transport T
    obtain ⟨R'₁, -⟩ := Y.theorem_7_1_13 (ϕ.obj x) isOpen_univ (mem_univ _)
    have hO' : IsOpen ((O ∩ S) ∩ T.Q ⁻¹' R'₁.U) :=
      (T.continuousOn_Q.mono fun u hu => hSW hu.2).isOpen_inter_preimage (hO.inter hSo)
        R'₁.isOpen_U
    obtain ⟨R₀, hR₀⟩ := X.theorem_7_1_13 x hO'
      ⟨⟨hxO, hxS⟩, by rw [mem_preimage, T.Q_self]; exact R'₁.mem_U⟩
    have hR₀W : R₀.U ⊆ T.W := fun u hu => hSW (hR₀ hu).1.2
    have hd₀ := T.isScDiffeoOn_image R₀.isOpen_U hR₀W
    obtain ⟨R', hR'U, hR'LR⟩ := hE' (ϕ.obj x) _ hd₀.isOpen_target ⟨x, R₀.mem_U, T.Q_self⟩
    obtain ⟨R, hRU, hRimg, -, -, -⟩ :=
      T.exists_naturalRep_pull R₀ R'₁ (fun u hu => ⟨hR₀W hu, (hR₀ hu).2⟩) R' hR'U
    have hRS : R.U ⊆ S := by rw [hRU]; exact fun u hu => (hR₀ hu.1).1.2
    have hRW : R.U ⊆ T.W := fun u hu => hSW (hRS hu)
    have hHR := hH.restrict_image R.isOpen_U hRS
    rw [hRimg] at hHR
    refine ⟨R, by rw [hRU]; exact fun u hu => (hR₀ hu.1).1.1,
      (hasLRLocal_iff_of_equivariant R R' hHR T.conj (T.bijective_conj hF).2
        (fun g w hw => ?_) fun a b ha hb => h.π_transport_iff T (hRW ha) (hRW hb)).2 hR'LR⟩
    rw [h.P_transport T (hRW hw)]
    exact h.transport_Γ T R R' g subset_rfl hRW (fun u hu => hRW (R.mapsTo_Φ g hu))
      R.isConnected_U.isPreconnected R.mem_U (fun u hu => hRimg ▸ ⟨u, hu, rfl⟩) hw

end EpStrongBundle

end Transport

/-! ### Proposition 10.5.6 -/

namespace SBLocalization

variable {A A' : SEP.{u}}

/-- **2021 Proposition 10.5.6, p. 508 (new in the 2021 edition)**, with Definition 8.4.2 read as
`IsLRLocal`: for a generalized strong bundle isomorphism `[D] : (P, μ) → (P', μ')`, `(P, μ)` has
the local regularity property iff `(P', μ')` has it.  The text's reduction
(`GenSBMap.iff_of_isGeneralizedIso`) to Proposition 10.4.6 (`proposition_10_4_6`). -/
theorem proposition_10_5_6 {f : GenSBMap A A'} (hf : f.IsGeneralizedIso) :
    A.E.IsLRLocal ↔ A'.E.IsLRLocal :=
  GenSBMap.iff_of_isGeneralizedIso (fun C => C.E.IsLRLocal)
    (fun _ hF => EpStrongBundle.proposition_10_4_6 hF) hf

end SBLocalization

end Polyfold
