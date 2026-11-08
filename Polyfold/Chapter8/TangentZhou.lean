import Polyfold.Chapter7.Zhou
import Polyfold.Chapter8.NonVacuityBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 8, the items of §8.1 "Regularity Properties and Tangents" and §8.4 that use the
Zhou condition or the local regularity property (all new in the 2021 edition): **Proposition
8.1.16** (p. 369), **Proposition 8.1.17** (p. 371) and **Definition 8.4.2** (p. 382).  Numbers
and pages are the 2021 text's.

# The Zhou condition and unique continuation for `TX`; local regularity for strong bundles

## The text, paraphrased

(Proposition 8.1.16, p. 369) If `X` satisfies (ZHOU), so does `TX`.  *Proof*: an isotropy element
of `b ∈ T_xX` is a pair `(g, h)` with `g ∈ G_x`; its natural action `H` lifts `ĝ`
(`τ ∘ H = ĝ ∘ τ` near `b`, (8.16)); if `T(g, h) = TH(b)` is the identity, differentiating (8.16)
and using that `Tτ` is onto gives `Tg = id`, so `g ∈ T_x` by (ZHOU) for `X`; then `s = t` near
`g`, hence `H = id` near `b`.  (Proposition 8.1.17, p. 371) (1) If `X¹` has (LUC) so has `TX`;
(2) if `X` has (SLUC) so has `TX`.  *Proof of (1)*: the natural action of `(Tg, b)` on `TU(x)` is
`Tĝ`; if it is the identity on an open set, `ĝ` is the identity on an open subset of
`V(x) = U(x) ∩ X₁`, hence on `V(x)` by (LUC) for `X¹`, hence on `U(x)` by density, so `Tĝ = id`.
*Proof of (2)*: `(TX)ⁱ = T(Xⁱ)`.  (Definition 8.4.2, p. 382) A strong bundle `(P : W → X, μ)`
over an ep-groupoid has the local regularity property if every `x` has arbitrarily small
natural representations `U(x)` such that every strong bundle isomorphism `B` of `W|U(x)` with
`|B(w)| = |w|` is `w ↦ g ∗ w = μ(Γ(g, P(w)), w)` for some `g ∈ G_x`.  (Proposition 8.4.3, p. 382)
If `X` is effective and has (LR), the strong bundle has the local regularity property.

## What is formalized

* `MPolyfold.levelVal_tangentProj_mem_smoothSet` (smooth tangent vectors lie over smooth points).
* `EpGroupoid.mem_nonEffectivePart_tangent`: if `p(v) ∈ 𝐗^T` then `v ∈ (T𝐗)^T` (the last step of
  the proof of Proposition 8.1.16).
* `TangentZhouReflect` (the step "`T(g, h) = id` ⇒ `Tg = id`") and **`proposition_8_1_16_2021`**.
* `nonEffectivePart_tangent_eq` (`(T𝐗)^T = p⁻¹((𝐗¹)^T)`), **`proposition_8_1_17_2021_one`**
  (Proposition 8.1.17 (1)) and `proposition_8_1_17_2021_two` (Proposition 8.1.17 (2) for `(TX)⁰`).
* `EpStrongBundle.natLift` (`g ∗ w`) and **`EpStrongBundle.IsLR`** (Definition 8.4.2).
* Witnesses: `tangentMor_trivial`, `tangentZhouReflect_trivial`,
  `isOpenMap_tangentProj_of_subsingleton`, `Examples.proposition_8_1_16_2021_point`,
  `Examples.proposition_8_1_17_2021_one_point` (the hypotheses of Propositions 8.1.16 and
  8.1.17 (1) hold for the point ep-groupoid), `EpStrongBundle.isLR_trivial` (every strong bundle
  over a trivial ep-groupoid has the local regularity property).

## What the text leaves implicit, and the choices made

* **Proposition 8.1.16.**  The step "`T(g, h) = id` ⇒ `Tg = id`" differentiates (8.16) and uses
  that `Tτ_X : T_b(TX) → T_xX` is onto; the second tangent bundle `T(TX)`, `Tτ_X` and its
  surjectivity are not formalized, so this step is the hypothesis `TangentZhouReflect`
  (satisfiable: `tangentZhouReflect_trivial`).  The rest is proved: `x = p(b)` is smooth
  (`levelVal_tangentProj_mem_smoothSet`), the base `g` of `(g, h)` lies in `G_x`, (ZHOU) gives
  `g ∈ T_x`, and `s = t` near `g` gives `Ts = Tt` near `(g, h)`.  As in Chapter 7's
  `IsZhou`, `T(g, h)` is the set map `tangentMor` of `TX`; no linear structure is used.
* **Proposition 8.1.17 (1)** is proved through 2021 Proposition 7.2.21 for `TX`: `(T𝐗)^T` is
  `p⁻¹((𝐗¹)^T)`, closed by (LUC) for `X¹`.  It assumes, as Appendix 7.6.4 does,
  `HasConnectedDenseLevelOneReps` (`U(x) ∩ X₁` connected and dense; the text's `V(x)`), and that
  `p : T𝐗 → 𝐗¹` is open (Part I, gap G.8).  (2) is proved for `(TX)⁰ = TX` only: the identification
  `(TX)ⁱ = T(Xⁱ)` is not formalized.
* **Definition 8.4.2** reads "strong bundle isomorphism `B : W|U(x) → W|U(x)`" as the project's
  `StrongBundle.IsStrongBundleIsoOn` (a strong bundle map `W → W` restricting to an isomorphism of
  `W|U(x)`, as for Definition 8.10 in `EpStrongBundle.lean`), and `|B(w)| = |w|` as equality of
  orbits in the groupoid `(W, 𝐖)`.
* **Proposition 8.4.3 is not formalized**: its density argument needs the openness of the bundle
  projection `P : W → X` (not in the project) and the density of the regular points of `U(x)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- A smooth point of `TX` lies over a smooth point of `X` (`p : TX → X¹` is sc-smooth,
`tangentProj_isScSmooth`, and `(X¹)_∞ = X_∞`). -/
theorem levelVal_tangentProj_mem_smoothSet {b : P.TangentSpace}
    (hb : b ∈ P.tangentPolyfold.smoothSet) :
    P.levelVal 1 (P.tangentProj b) ∈ P.smoothSet := by
  refine (mem_shift_smoothSet_iff (P.tangentProj b)).1 (mem_iInter.2 fun m => ?_)
  exact P.tangentProj_isScSmooth.mapsTo_levelSet m (mem_iInter.1 hb m)

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **The last step of the proof of 2021 Proposition 8.1.16**: if `s = t` near the base `p(v)` of
`v ∈ T𝐗`, then `Ts = Tt` near `v`, so `v ∈ (T𝐗)^T`. -/
theorem mem_nonEffectivePart_tangent {v : X.PMor.TangentSpace}
    (h : X.tBase v ∈ X.nonEffectivePart) : v ∈ X.tangentEpGroupoid.nonEffectivePart := by
  rw [X.tangentEpGroupoid.mem_nonEffectivePart_iff]
  obtain ⟨N, hNs, hNo, hvN⟩ := mem_nhds_iff.1 (X.mem_nonEffectivePart_iff.1 h)
  have hs := X.isScSmoothMap_src.mono hNo (subset_univ N)
  have ht := X.isScSmoothMap_tgt.mono hNo (subset_univ N)
  filter_upwards [(MPolyfold.isOpen_tangentPreimage hNo).mem_nhds hvN] with ψ hψ
  change MPolyfold.tangentMap X.isScSmoothMap_src ψ = MPolyfold.tangentMap X.isScSmoothMap_tgt ψ
  rw [← MPolyfold.tangentMapOn_eq_tangentMap X.isScSmoothMap_src hs hψ,
    ← MPolyfold.tangentMapOn_eq_tangentMap X.isScSmoothMap_tgt ht hψ]
  exact MPolyfold.tangentMapOn_congr hs ht hNo subset_rfl subset_rfl (fun φ hφ => hNs hφ) hψ

/-- The step "`T(g, h) = id` ⇒ `Tg = id`" of the proof of 2021 Proposition 8.1.16 (differentiating
(8.16), with `Tτ_X` onto), as a hypothesis: for a smooth `b ∈ TX` and `(g, h) ∈ G_b`, if the
tangent of `(g, h)` in the ep-groupoid `TX` is the identity on `T_b(TX)`, then the tangent of its
base `g` is the identity on `T_{p(b)}X`.  Satisfiable: `tangentZhouReflect_trivial`. -/
def TangentZhouReflect : Prop :=
  ∀ (y : X.tangentEpGroupoid.PObj.SmoothLevel)
    (k : X.tangentEpGroupoid.Isotropy (X.tangentEpGroupoid.PObj.smoothVal y)),
    (∀ q ∈ X.tangentEpGroupoid.PObj.tangentFiber (X.tangentEpGroupoid.PObj.smoothIncl y 1),
      X.tangentEpGroupoid.tangentMor k.val q = q) →
    ∀ v ∈ X.PObj.tangentFiber (X.PObj.tangentProj (X.tangentEpGroupoid.PObj.smoothVal y)),
      X.tangentMor (X.tBase k.val) v = v

/-- **2021 Proposition 8.1.16, p. 369 (new in the 2021 edition)**: if `X` satisfies (ZHOU), so does
the tangent ep-groupoid `TX`, given `TangentZhouReflect`. -/
theorem proposition_8_1_16_2021 (hZ : X.IsZhou) (hr : X.TangentZhouReflect) :
    X.tangentEpGroupoid.IsZhou := by
  intro y k hk
  have hx : X.PObj.levelVal 1 (X.PObj.tangentProj (X.tangentEpGroupoid.PObj.smoothVal y)) ∈
      X.PObj.smoothSet :=
    X.PObj.levelVal_tangentProj_mem_smoothSet (X.tangentEpGroupoid.PObj.smoothVal_mem y)
  have hsrc : X.src (X.tBase k.val) = X.PObj.smoothVal (X.PObj.smoothMk _ hx) := by
    rw [← X.levelVal_tangentProj_tSrc]
    exact congrArg (fun a => X.PObj.levelVal 1 (X.PObj.tangentProj a)) k.src_val
  have htgt : X.tgt (X.tBase k.val) = X.PObj.smoothVal (X.PObj.smoothMk _ hx) := by
    rw [← X.levelVal_tangentProj_tTgt]
    exact congrArg (fun a => X.PObj.levelVal 1 (X.PObj.tangentProj a)) k.tgt_val
  have hy' : X.PObj.smoothIncl (X.PObj.smoothMk _ hx) 1 =
      X.PObj.tangentProj (X.tangentEpGroupoid.PObj.smoothVal y) := MPolyfold.level_ext rfl
  have hg := hZ (X.PObj.smoothMk _ hx) ⟨X.tBase k.val, hsrc, htgt⟩ fun v hv =>
    hr y k hk v (by rw [← hy']; exact hv)
  have h1 : X.tBase k.val ∈ X.nonEffectivePart :=
    (X.val_mem_nonEffectivePart_iff (g := ⟨X.tBase k.val, hsrc, htgt⟩)).2 hg
  exact (X.tangentEpGroupoid.val_mem_nonEffectivePart_iff (g := k)).1
    (X.mem_nonEffectivePart_tangent h1)

/-- `(T𝐗)^T = p⁻¹((𝐗¹)^T)` under (LUC) for `X¹`, with `p : T𝐗 → 𝐗¹` open. -/
theorem nonEffectivePart_tangent_eq (h : X.liftOne.IsLUC) (hR : X.HasConnectedDenseLevelOneReps)
    (hp : IsOpenMap X.PMor.tangentProj) :
    X.tangentEpGroupoid.nonEffectivePart = X.PMor.tangentProj ⁻¹' X.liftOne.nonEffectivePart := by
  have hT1 := X.nonEffectivePart_liftOne_eq (X.liftOne.proposition_7_2_21_2021.1 h) hR
  ext v
  constructor
  · intro hv
    obtain ⟨O, hOs, hOo, hvO⟩ := mem_nhds_iff.1 (X.tangentEpGroupoid.mem_nonEffectivePart_iff.1 hv)
    rw [mem_preimage, X.liftOne.mem_nonEffectivePart_iff]
    filter_upwards [(hp O hOo).mem_nhds ⟨v, hvO, rfl⟩] with φ ⟨w, hwO, hw⟩
    subst hw
    refine MPolyfold.level_ext ?_
    rw [liftOne_src_val, liftOne_tgt_val]
    change X.src (X.tBase w) = X.tgt (X.tBase w)
    rw [← X.levelVal_tangentProj_tSrc, ← X.levelVal_tangentProj_tTgt]
    exact congrArg (fun a => X.PObj.levelVal 1 (X.PObj.tangentProj a)) (hOs hwO)
  · intro hv
    rw [mem_preimage, hT1] at hv
    exact X.mem_nonEffectivePart_tangent hv

/-- **2021 Proposition 8.1.17 (1), p. 371 (new in the 2021 edition)**: if `X¹` has (LUC), so has
`TX`. -/
theorem proposition_8_1_17_2021_one (h : X.liftOne.IsLUC) (hR : X.HasConnectedDenseLevelOneReps)
    (hp : IsOpenMap X.PMor.tangentProj) : X.tangentEpGroupoid.IsLUC := by
  refine X.tangentEpGroupoid.proposition_7_2_21_2021.2 ?_
  rw [X.nonEffectivePart_tangent_eq h hR hp]
  exact (X.liftOne.proposition_7_2_21_2021.1 h).preimage MPolyfold.continuous_tangentProj

/-- **2021 Proposition 8.1.17 (2), p. 371, for `(TX)⁰`**: (SLUC) for `X` gives (LUC) for `TX`. -/
theorem proposition_8_1_17_2021_two (A : EP.{u}) (h : A.IsSLUC)
    (hR : A.X.HasConnectedDenseLevelOneReps) (hp : IsOpenMap A.X.PMor.tangentProj) :
    A.X.tangentEpGroupoid.IsLUC :=
  A.X.proposition_8_1_17_2021_one (h 1) hR hp

/-! ### Witnesses -/

open scoped Classical in
/-- For the trivial ep-groupoid, the tangent of every morphism is the identity. -/
theorem tangentMor_trivial {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (P : MPolyfold Z) (φ : Z) (v : P.TangentSpace) : (trivial P).tangentMor φ v = v := by
  unfold tangentMor
  exact dite_eq_right_iff.2 fun hv => hv.choose_spec.2

/-- **Witness**: `TangentZhouReflect` holds for the trivial ep-groupoid of an M-polyfold. -/
theorem tangentZhouReflect_trivial {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] (P : MPolyfold Z) : (trivial P).TangentZhouReflect :=
  fun _ _ _ v _ => tangentMor_trivial P _ v

/-- **Witness**: `p : TX → X¹` is open when `X` has at most one point. -/
theorem isOpenMap_tangentProj_of_subsingleton {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] [Subsingleton Z] (P : MPolyfold Z) : IsOpenMap P.tangentProj := by
  have : Subsingleton (P.Level 1) := ⟨fun a b => MPolyfold.level_ext (Subsingleton.elim _ _)⟩
  intro s _
  rcases (P.tangentProj '' s).eq_empty_or_nonempty with h | ⟨a, ha⟩
  · rw [h]; exact isOpen_empty
  · have : P.tangentProj '' s = univ := eq_univ_of_forall fun b => Subsingleton.elim a b ▸ ha
    rw [this]; exact isOpen_univ

namespace Examples

/-- The hypotheses of `proposition_8_1_16_2021` are satisfiable. -/
theorem proposition_8_1_16_2021_point : pointEpGroupoid.tangentEpGroupoid.IsZhou :=
  pointEpGroupoid.proposition_8_1_16_2021 (isZhou_trivial _) (tangentZhouReflect_trivial _)

/-- The hypotheses of `proposition_8_1_17_2021_one` are satisfiable. -/
theorem proposition_8_1_17_2021_one_point : pointEpGroupoid.tangentEpGroupoid.IsLUC :=
  pointEpGroupoid.proposition_8_1_17_2021_one isLUC_liftOne_point
    hasConnectedDenseLevelOneReps_point (isOpenMap_tangentProj_of_subsingleton _)

end Examples

end EpGroupoid

/-! ### Definition 8.4.2 -/

section BundleLR

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

/-- The natural lift `g ∗ w = μ(Γ(g, P(w)), w)` of the `G_x`-action to `W|U(x)` (2021 p. 382). -/
def natLift (E : EpStrongBundle X B) {x : Obj} (R : X.NaturalRep x) (g : X.Isotropy x) (w : W)
    (hw : P w ∈ R.U) : W :=
  E.μ ⟨(R.Γ g (P w), w), (R.src_Γ g (P w) hw).symm⟩

/-- **2021 Definition 8.4.2, p. 382 (new in the 2021 edition)**: the local regularity property of a
strong bundle over an ep-groupoid.  Inside every open `O ∋ x` there is a natural
representation `U(x)` such that every strong bundle isomorphism `Φ` of `W|U(x)` (covering some
`β`) with `|Φ(w)| = |w|` is `w ↦ g ∗ w` for some `g ∈ G_x`.  Satisfiable:
`EpStrongBundle.isLR_trivial`. -/
def IsLR (E : EpStrongBundle X B) : Prop :=
  ∀ (x : Obj) (O : Set Obj), IsOpen O → x ∈ O → ∃ R : X.NaturalRep x, R.U ⊆ O ∧
    ∀ (β : Obj → Obj) (Φ : W → W) (hΦ : B.IsStrongBundleMap B β Φ),
      B.IsStrongBundleIsoOn B hΦ R.U R.U →
      (∀ w, P w ∈ R.U → E.toGroupoidStr.π (Φ w) = E.toGroupoidStr.π w) →
      ∃ g : X.Isotropy x, ∀ w (hw : P w ∈ R.U), Φ w = E.natLift R g w hw

end EpStrongBundle

end BundleLR

section BundleLRWitness

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Z}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- **Witness**: every strong bundle over a trivial ep-groupoid has the local regularity
property. -/
theorem EpStrongBundle.isLR_trivial (B : StrongBundle PZ P) :
    (EpStrongBundle.trivial B).IsLR := by
  intro x O hO hxO
  obtain ⟨R, hRO⟩ := (EpGroupoid.trivial PZ).theorem_7_1 x hO hxO
  refine ⟨R, hRO, fun β Φ hΦ _ hπ => ⟨1, fun w hw => ?_⟩⟩
  obtain ⟨q, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 (hπ w hw)
  exact h1.symm.trans h2

end BundleLRWitness

end Polyfold
