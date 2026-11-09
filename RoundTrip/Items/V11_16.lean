import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_16

/-! Round trip for V11_16 (2021 pp. 536–537, after Lemma 11.3.2; 2017 pp. 389–390: push-forward
and pull-back of functors `Θ` along generalized isomorphisms, independence of the representative,
`(g ∘ f)_* = g_* ∘ f_*` "and the like").

The item lists the definitions `Diagram.pushTheta` (`Φ_*F^*`), `Diagram.pullTheta` (`F_*Φ^*`),
`EPLoc.rep`, `EPLoc.pushTheta`, `EPLoc.pullTheta` (vocabulary) and nineteen theorems; `A` is the
conjunction of their types, universes at `0`: `IsRefinement.isEquivalence_Φ_iff`, the refinement
and equivalence steps (`push/pullTheta_eq_of_isRefinement`, `push/pullTheta_eq_of_equiv`), the
representative API (`homMk_rep`, `equiv_rep_homMk`, `isEquivalence_rep_Φ`), independence of the
representative (`pushTheta_homMk`, `pullTheta_homMk`), functoriality (`isFunctorial_push/pullTheta`),
`pushTheta_comp`, `pullTheta_comp` (the latter for **all** generalized maps), `pushTheta_inv`
(`(f⁻¹)_* = f^*`), `pullTheta_pushTheta`, `pushTheta_pullTheta`, and the two base-change lemmas in
the weak fibred product (`WeakFibredProduct.pushforwardTheta_projRight/Left_pullbackTheta`, for
arbitrary ep-groupoids).  `Θ` is only asked to be a functor (any sign).

`B`: for a generalized isomorphism `f` (`IsIso f`), `Φ_*F^*Θ` and `F_*Φ^*Θ'` do not depend on the
representative; `(g ∘ f)_* = g_* ∘ f_*` and `(g ∘ f)^* = f^* ∘ g^*` on any representatives; all for
functors to `ℚ⁺` (nonnegative).  `B`'s `pushRepB`, `pullRepB` are definitionally the project's
`Diagram.pushTheta`, `Diagram.pullTheta`.

* `A_to_B`: `pushTheta_homMk`, `pullTheta_homMk` (twice each) for independence; `pushTheta_comp`,
  `pullTheta_comp` with `pushTheta_homMk`, `pullTheta_homMk`, `isFunctorial_push/pullTheta` for the
  composites; `Φ` an equivalence for a representative of an isomorphism by the non-item
  `theorem_10_3_10`.
* `B_to_A`: from `B` — `pushTheta_homMk`, `pushTheta_eq_of_equiv`, `pushTheta_eq_of_isRefinement`,
  `pushTheta_comp` and (through `pushTheta_homMk`) `pushTheta_inv`.  `B` speaks of nonnegative
  functors only; since `pushforwardTheta` and `pullbackTheta` are additive in `Θ` (the choice in
  `pushforwardTheta` does not depend on `Θ`, `pushRepB_sub`), a functor `Θ = max(Θ,0) − max(−Θ,0)`
  reduces to two nonnegative ones (`eq_of_eq_on_nonneg`).  The rest of `A` is not a consequence of
  `B` and is re-proved outright by local copies of the project's proofs (`*'`): the pull-back
  statements hold for all generalized maps (`B` has isomorphisms only), the base-change lemmas and
  `isEquivalence_Φ_iff` are about arbitrary ep-groupoids and diagrams, the representative API and
  `f^*f_* = id`, `f_*f^* = id` are not stated in `B`. -/

namespace RoundTrip.V11_16
open Polyfold CategoryTheory
open Polyfold.EPLocalization

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.Diagram.IsRefinement.isEquivalence_Φ_iff.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.pushTheta_eq_of_isRefinement.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.pullTheta_eq_of_isRefinement.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.pushTheta_eq_of_equiv.{0}) ∧
  (type_of% @Polyfold.EPLocalization.Diagram.pullTheta_eq_of_equiv.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.homMk_rep.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.equiv_rep_homMk.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.isEquivalence_rep_Φ.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.pushTheta_homMk.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.pullTheta_homMk.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.isFunctorial_pushTheta.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.isFunctorial_pullTheta.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.pushTheta_comp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.pullTheta_comp.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.pushTheta_inv.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.pullTheta_pushTheta.{0}) ∧
  (type_of% @Polyfold.EPLocalization.EPLoc.pushTheta_pullTheta.{0}) ∧
  (type_of% @Polyfold.WeakFibredProduct.pushforwardTheta_projRight_pullbackTheta.{0, 0, 0}) ∧
  (type_of% @Polyfold.WeakFibredProduct.pushforwardTheta_projLeft_pullbackTheta.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.Diagram.IsRefinement.isEquivalence_Φ_iff.{0},
    @Polyfold.EPLocalization.Diagram.pushTheta_eq_of_isRefinement.{0},
    @Polyfold.EPLocalization.Diagram.pullTheta_eq_of_isRefinement.{0},
    @Polyfold.EPLocalization.Diagram.pushTheta_eq_of_equiv.{0},
    @Polyfold.EPLocalization.Diagram.pullTheta_eq_of_equiv.{0},
    @Polyfold.EPLocalization.EPLoc.homMk_rep.{0},
    @Polyfold.EPLocalization.EPLoc.equiv_rep_homMk.{0},
    @Polyfold.EPLocalization.EPLoc.isEquivalence_rep_Φ.{0},
    @Polyfold.EPLocalization.EPLoc.pushTheta_homMk.{0},
    @Polyfold.EPLocalization.EPLoc.pullTheta_homMk.{0},
    @Polyfold.EPLocalization.EPLoc.isFunctorial_pushTheta.{0},
    @Polyfold.EPLocalization.EPLoc.isFunctorial_pullTheta.{0},
    @Polyfold.EPLocalization.EPLoc.pushTheta_comp.{0},
    @Polyfold.EPLocalization.EPLoc.pullTheta_comp.{0},
    @Polyfold.EPLocalization.EPLoc.pushTheta_inv.{0},
    @Polyfold.EPLocalization.EPLoc.pullTheta_pushTheta.{0},
    @Polyfold.EPLocalization.EPLoc.pushTheta_pullTheta.{0},
    @Polyfold.WeakFibredProduct.pushforwardTheta_projRight_pullbackTheta.{0, 0, 0},
    @Polyfold.WeakFibredProduct.pushforwardTheta_projLeft_pullbackTheta.{0, 0, 0}⟩

/-- A representative of an isomorphism has `Φ` an equivalence (Theorem 10.3.10, non-item). -/
theorem isEquivalence_Φ_of_isIso {X Y : EP.{0}} {d : Diagram X Y} (h : IsIso (EPLoc.homMk d)) :
    d.Φ.IsEquivalence :=
  (EPLoc.theorem_10_3_10 d).1.1 ((EPLoc.isGeneralizedIso_iff_isIso _).2 h)

theorem A_to_B : A → B := by
  rintro ⟨-, -, -, -, -, -, -, -, hpush, hpull, hfpush, hfpull, hcomp, hpcomp, -, -, -, -, -⟩
  refine ⟨?_, ?_⟩
  · intro X Y f hf d d' hd hd'
    subst hd
    have hΦ := isEquivalence_Φ_of_isIso hf
    have hΦ' := isEquivalence_Φ_of_isIso (hd' ▸ hf)
    refine ⟨fun Θ hΘ => ?_, fun Θ' hΘ' => ?_⟩
    · change d.pushTheta Θ = d'.pushTheta Θ
      rw [← hpush d hΦ hΘ.2, ← hpush d' hΦ' hΘ.2, hd']
    · change d.pullTheta Θ' = d'.pullTheta Θ'
      rw [← hpull d hΘ'.2, ← hpull d' hΘ'.2, hd']
  · intro X Y Z f g hf hg d e c hd he hc
    subst hd he
    have hf' := (EPLoc.isGeneralizedIso_iff_isIso _).2 hf
    have hg' := (EPLoc.isGeneralizedIso_iff_isIso _).2 hg
    have hc' : IsIso (EPLoc.homMk c) := hc ▸ inferInstance
    have hΦc := isEquivalence_Φ_of_isIso hc'
    have hΦd := isEquivalence_Φ_of_isIso hf
    have hΦe := isEquivalence_Φ_of_isIso hg
    refine ⟨fun Θ hΘ => ?_, fun Θ'' hΘ'' => ?_⟩
    · change c.pushTheta Θ = e.pushTheta (d.pushTheta Θ)
      have hfun : Y.X.IsFunctorial (d.pushTheta Θ) := by
        rw [← hpush d hΦd hΘ.2]; exact hfpush hf' hΘ.2
      rw [← hpush c hΦc hΘ.2, hc, hcomp hf' hg' hΘ.2, hpush d hΦd hΘ.2, hpush e hΦe hfun]
    · change c.pullTheta Θ'' = d.pullTheta (e.pullTheta Θ'')
      have hfun : Y.X.IsFunctorial (e.pullTheta Θ'') := by
        rw [← hpull e hΘ''.2]; exact hfpull _ hΘ''.2
      rw [← hpull c hΘ''.2, hc, hpcomp _ _ hΘ''.2, hpull e hΘ''.2, hpull d hfun]

/-! ### From nonnegative functors to all functors -/

section Sign

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {β : Type} [AddGroup β]

/-- Two additive operators on functions `Obj → ℚ` that agree on functors to `ℚ⁺` agree on all
functors (`Θ = max(Θ, 0) − max(−Θ, 0)`). -/
theorem eq_of_eq_on_nonneg {L₁ L₂ : (Obj → ℚ) → β} (h₁ : ∀ a b, L₁ (a - b) = L₁ a - L₁ b)
    (h₂ : ∀ a b, L₂ (a - b) = L₂ a - L₂ b) (h : ∀ Θ, IsQFunctorB X Θ → L₁ Θ = L₂ Θ)
    {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) : L₁ Θ = L₂ Θ := by
  have hp : IsQFunctorB X (fun x => max (Θ x) 0) :=
    ⟨fun _ => le_max_right _ _, fun φ => by simp only [hΘ φ]⟩
  have hn : IsQFunctorB X (fun x => max (-Θ x) 0) :=
    ⟨fun _ => le_max_right _ _, fun φ => by simp only [hΘ φ]⟩
  have hd : Θ = (fun x => max (Θ x) 0) - (fun x => max (-Θ x) 0) :=
    funext fun x => (max_zero_sub_eq_self (Θ x)).symm
  rw [hd, h₁, h₂, h _ hp, h _ hn]

end Sign

/-- `Φ_*F^*` is additive in `Θ`. -/
theorem pushRepB_sub {X Y : EP.{0}} (d : Diagram X Y) (a b : X.Obj → ℚ) :
    pushRepB d (a - b) = pushRepB d a - pushRepB d b := by
  funext y
  simp only [pushRepB, EpFunctor.pushforwardTheta, EpFunctor.pullbackTheta, Pi.sub_apply]
  split_ifs <;> simp

/-! ### The parts of `A` that come from `B` -/

theorem isIso_homMk {X Y : EP.{0}} {d : Diagram X Y} (hΦ : d.Φ.IsEquivalence) :
    IsIso (EPLoc.homMk d) :=
  (EPLoc.isGeneralizedIso_iff_isIso _).1 ((EPLoc.theorem_10_3_10 d).1.2 hΦ)

theorem homMk_rep' {X Y : EP.{0}} (f : EPLoc.of X ⟶ EPLoc.of Y) :
    EPLoc.homMk (EPLoc.rep f) = f :=
  Quotient.out_eq f

theorem pushTheta_eq_of_equiv_B (hB : B) {X Y : EP.{0}} {d d' : Diagram X Y}
    (h : Diagram.Equiv d d') (hΦ : d.Φ.IsEquivalence) {Θ : X.Obj → ℚ}
    (hΘ : X.X.IsFunctorial Θ) : d.pushTheta Θ = d'.pushTheta Θ := by
  have h' := (hB.1 X Y (EPLoc.homMk d) (isIso_homMk hΦ) d d' rfl
    (EPLoc.homMk_eq_homMk_iff.2 h).symm).1
  exact eq_of_eq_on_nonneg (L₁ := pushRepB d) (L₂ := pushRepB d') (pushRepB_sub _)
    (pushRepB_sub _) h' hΘ

theorem pushTheta_eq_of_isRefinement_B (hB : B) {X Y : EP.{0}} {d d' : Diagram X Y}
    (h : d'.IsRefinement d) (hΦ : d.Φ.IsEquivalence) {Θ : X.Obj → ℚ}
    (hΘ : X.X.IsFunctorial Θ) : d'.pushTheta Θ = d.pushTheta Θ :=
  (pushTheta_eq_of_equiv_B hB ⟨d', h, Diagram.IsRefinement.refl d'⟩ hΦ hΘ).symm

theorem pushTheta_homMk_B (hB : B) {X Y : EP.{0}} (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence)
    {Θ : X.Obj → ℚ} (hΘ : X.X.IsFunctorial Θ) :
    EPLoc.pushTheta (EPLoc.homMk d) Θ = d.pushTheta Θ := by
  have h := (hB.1 X Y (EPLoc.homMk d) (isIso_homMk hΦ) (EPLoc.rep (EPLoc.homMk d)) d
    (homMk_rep' _) rfl).1
  exact eq_of_eq_on_nonneg (L₁ := pushRepB (EPLoc.rep (EPLoc.homMk d))) (L₂ := pushRepB d)
    (pushRepB_sub _) (pushRepB_sub _) h hΘ

theorem pushTheta_comp_B (hB : B) {X Y Z : EP.{0}} {f : EPLoc.of X ⟶ EPLoc.of Y}
    {g : EPLoc.of Y ⟶ EPLoc.of Z} (hf : EPLoc.IsGeneralizedIso f)
    (hg : EPLoc.IsGeneralizedIso g) {Θ : X.Obj → ℚ} (hΘ : X.X.IsFunctorial Θ) :
    EPLoc.pushTheta (f ≫ g) Θ = EPLoc.pushTheta g (EPLoc.pushTheta f Θ) := by
  have h := (hB.2 X Y Z f g ((EPLoc.isGeneralizedIso_iff_isIso f).1 hf)
    ((EPLoc.isGeneralizedIso_iff_isIso g).1 hg) (EPLoc.rep f) (EPLoc.rep g) (EPLoc.rep (f ≫ g))
    (homMk_rep' _) (homMk_rep' _) (homMk_rep' _)).1
  have hsub : ∀ a b : X.Obj → ℚ, pushRepB (EPLoc.rep g) (pushRepB (EPLoc.rep f) (a - b)) =
      pushRepB (EPLoc.rep g) (pushRepB (EPLoc.rep f) a) -
        pushRepB (EPLoc.rep g) (pushRepB (EPLoc.rep f) b) := fun a b => by
    rw [pushRepB_sub, pushRepB_sub]
  exact eq_of_eq_on_nonneg (L₁ := pushRepB (EPLoc.rep (f ≫ g)))
    (L₂ := fun Θ => pushRepB (EPLoc.rep g) (pushRepB (EPLoc.rep f) Θ)) (pushRepB_sub _) hsub h hΘ

/-! ### Local copies of the project's proofs (parts of `A` that `B` cannot give) -/

section BaseChange

open WeakFibredProduct EpFunctor

variable {Obj Mor Obj' Mor' Obj'' Mor'' : Type}
  [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Z : EpGroupoid Obj'' Mor''}
  {F : EpFunctor X Y} {G : EpFunctor Z Y}

theorem pushforwardTheta_projRight_pullbackTheta' (hF : F.IsEquivalence) (h : Admissible F G)
    {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) :
    (projRight F G h).pushforwardTheta ((projLeft F G h).pullbackTheta Θ) =
      G.pullbackTheta (F.pushforwardTheta Θ) := by
  funext z
  obtain ⟨x, φ, hs, ht⟩ := hF.exists_iso (G.obj z)
  have hp : Z.Isomorphic ((projRight F G h).obj (WeakFibredProduct.Obj.mk F G x φ z hs ht)) z :=
    Z.isomorphic_refl z
  rw [pushforwardTheta_eq (isEquivalence_projRight hF h).full
    ((projLeft F G h).isFunctorial_pullbackTheta hΘ) hp, pullbackTheta_apply,
    pullbackTheta_apply, pushforwardTheta_eq hF.full hΘ ⟨φ, hs, ht⟩]
  rfl

theorem pushforwardTheta_projLeft_pullbackTheta' (hG : G.IsEquivalence) (h : Admissible F G)
    {Θ : Obj'' → ℚ} (hΘ : Z.IsFunctorial Θ) :
    (projLeft F G h).pushforwardTheta ((projRight F G h).pullbackTheta Θ) =
      F.pullbackTheta (G.pushforwardTheta Θ) := by
  funext x
  obtain ⟨z, ψ, hs, ht⟩ := hG.exists_iso (F.obj x)
  have h₁ : Y.src (Y.inv ψ) = F.obj x := by rw [Y.src_inv, ht]
  have h₂ : Y.tgt (Y.inv ψ) = G.obj z := by rw [Y.tgt_inv, hs]
  have hp : X.Isomorphic
      ((projLeft F G h).obj (WeakFibredProduct.Obj.mk F G x (Y.inv ψ) z h₁ h₂)) x :=
    X.isomorphic_refl x
  rw [pushforwardTheta_eq (isEquivalence_projLeft hG h).full
    ((projRight F G h).isFunctorial_pullbackTheta hΘ) hp, pullbackTheta_apply,
    pullbackTheta_apply, pushforwardTheta_eq hG.full hΘ ⟨ψ, hs, ht⟩]
  rfl

end BaseChange

section Diagrams

open EpFunctor WeakFibredProduct

variable {X Y Z : EP.{0}}

theorem isEquivalence_Φ_iff' {d d' : Diagram X Y} (h : d'.IsRefinement d) :
    d.Φ.IsEquivalence ↔ d'.Φ.IsEquivalence := by
  obtain ⟨H, hH, -, hΦH⟩ := h
  refine ⟨fun hΦ => (proposition_10_1_5 hΦH).1 (hΦ.comp hH), fun hΦ' => ?_⟩
  exact proposition_10_1_6 hH ((proposition_10_1_5 hΦH).2 hΦ')

theorem pullTheta_eq_of_isRefinement' {d d' : Diagram X Y} (h : d'.IsRefinement d)
    {Θ' : Y.Obj → ℚ} (hΘ' : Y.X.IsFunctorial Θ') : d'.pullTheta Θ' = d.pullTheta Θ' := by
  obtain ⟨H, hH, hF, hΦH⟩ := h
  have hFH : (d.F.comp H).IsEquivalence := d.isEquivalence_F.comp hH
  unfold Diagram.pullTheta
  rw [← pullbackTheta_eq_of_naturallyEquivalent hΦH hΘ',
    ← pushforwardTheta_eq_of_naturallyEquivalent hFH.full d'.isEquivalence_F.full hF
      ((d.Φ.comp H).isFunctorial_pullbackTheta hΘ'),
    pullbackTheta_comp, pushforwardTheta_comp d.isEquivalence_F.full hH.full hFH.full
      (H.isFunctorial_pullbackTheta (d.Φ.isFunctorial_pullbackTheta hΘ')),
    pushforwardTheta_pullbackTheta hH.essSurj (d.Φ.isFunctorial_pullbackTheta hΘ')]

theorem pullTheta_eq_of_equiv' {d d' : Diagram X Y} (h : Diagram.Equiv d d') {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsFunctorial Θ') : d.pullTheta Θ' = d'.pullTheta Θ' := by
  obtain ⟨d'', h1, h2⟩ := h
  rw [← pullTheta_eq_of_isRefinement' h1 hΘ', pullTheta_eq_of_isRefinement' h2 hΘ']

theorem equiv_rep_homMk' (d : Diagram X Y) : Diagram.Equiv (EPLoc.rep (EPLoc.homMk d)) d :=
  Quotient.mk_out (s := Diagram.setoid X Y) d

theorem isEquivalence_rep_Φ' {f : EPLoc.of X ⟶ EPLoc.of Y} (hf : EPLoc.IsGeneralizedIso f) :
    (EPLoc.rep f).Φ.IsEquivalence :=
  (EPLoc.theorem_10_3_10 (EPLoc.rep f)).1.1 (by rw [homMk_rep']; exact hf)

theorem pullTheta_homMk' (d : Diagram X Y) {Θ' : Y.Obj → ℚ} (hΘ' : Y.X.IsFunctorial Θ') :
    EPLoc.pullTheta (EPLoc.homMk d) Θ' = d.pullTheta Θ' :=
  pullTheta_eq_of_equiv' (equiv_rep_homMk' d) hΘ'

theorem isFunctorial_pushTheta' {f : EPLoc.of X ⟶ EPLoc.of Y} (hf : EPLoc.IsGeneralizedIso f)
    {Θ : X.Obj → ℚ} (hΘ : X.X.IsFunctorial Θ) : Y.X.IsFunctorial (EPLoc.pushTheta f Θ) :=
  isFunctorial_pushforwardTheta (isEquivalence_rep_Φ' hf).full
    ((EPLoc.rep f).F.isFunctorial_pullbackTheta hΘ)

theorem isFunctorial_pullTheta' (f : EPLoc.of X ⟶ EPLoc.of Y) {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsFunctorial Θ') : X.X.IsFunctorial (EPLoc.pullTheta f Θ') :=
  isFunctorial_pushforwardTheta (EPLoc.rep f).isEquivalence_F.full
    ((EPLoc.rep f).Φ.isFunctorial_pullbackTheta hΘ')

theorem pullTheta_comp' (f : EPLoc.of X ⟶ EPLoc.of Y) (g : EPLoc.of Y ⟶ EPLoc.of Z)
    {Θ'' : Z.Obj → ℚ} (hΘ'' : Z.X.IsFunctorial Θ'') :
    EPLoc.pullTheta (f ≫ g) Θ'' = EPLoc.pullTheta f (EPLoc.pullTheta g Θ'') := by
  have hG := (EPLoc.rep g).isEquivalence_F
  have hπ := isEquivalence_projLeft hG ((EPLoc.rep f).admissible (EPLoc.rep g))
  have hc := ((EPLoc.rep f).comp (EPLoc.rep g)).isEquivalence_F
  have hfg : f ≫ g = EPLoc.homMk ((EPLoc.rep f).comp (EPLoc.rep g)) := by
    rw [← EPLoc.homMk_comp, homMk_rep', homMk_rep']
  rw [hfg, pullTheta_homMk' _ hΘ'']
  change ((EPLoc.rep f).F.comp (projLeft _ _ _)).pushforwardTheta
    (((EPLoc.rep g).Φ.comp (projRight _ _ _)).pullbackTheta Θ'') = _
  rw [pullbackTheta_comp, pushforwardTheta_comp (EPLoc.rep f).isEquivalence_F.full hπ.full
    hc.full
    ((projRight _ _ _).isFunctorial_pullbackTheta ((EPLoc.rep g).Φ.isFunctorial_pullbackTheta hΘ'')),
    pushforwardTheta_projLeft_pullbackTheta' hG _
      ((EPLoc.rep g).Φ.isFunctorial_pullbackTheta hΘ'')]
  rfl

theorem pushTheta_inv_B (hB : B) {f : EPLoc.of X ⟶ EPLoc.of Y} (hf : EPLoc.IsGeneralizedIso f)
    {g : EPLoc.of Y ⟶ EPLoc.of X} (h₁ : f ≫ g = 𝟙 _) (h₂ : g ≫ f = 𝟙 _) {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsFunctorial Θ') : EPLoc.pushTheta g Θ' = EPLoc.pullTheta f Θ' := by
  have hd := isEquivalence_rep_Φ' hf
  rw [← homMk_rep' f] at h₁ h₂
  rw [(EPLoc.theorem_10_3_10 (EPLoc.rep f)).2 hd g h₁ h₂,
    pushTheta_homMk_B hB _ (EPLoc.rep f).isEquivalence_F hΘ']
  rfl

theorem pullTheta_pushTheta' {f : EPLoc.of X ⟶ EPLoc.of Y} (hf : EPLoc.IsGeneralizedIso f)
    {Θ : X.Obj → ℚ} (hΘ : X.X.IsFunctorial Θ) :
    EPLoc.pullTheta f (EPLoc.pushTheta f Θ) = Θ := by
  have hd := isEquivalence_rep_Φ' hf
  unfold EPLoc.pullTheta EPLoc.pushTheta Diagram.pullTheta Diagram.pushTheta
  rw [pullbackTheta_pushforwardTheta hd.full ((EPLoc.rep f).F.isFunctorial_pullbackTheta hΘ),
    pushforwardTheta_pullbackTheta (EPLoc.rep f).isEquivalence_F.essSurj hΘ]

theorem pushTheta_pullTheta' {f : EPLoc.of X ⟶ EPLoc.of Y} (hf : EPLoc.IsGeneralizedIso f)
    {Θ' : Y.Obj → ℚ} (hΘ' : Y.X.IsFunctorial Θ') :
    EPLoc.pushTheta f (EPLoc.pullTheta f Θ') = Θ' := by
  have hd := isEquivalence_rep_Φ' hf
  unfold EPLoc.pullTheta EPLoc.pushTheta Diagram.pullTheta Diagram.pushTheta
  rw [pullbackTheta_pushforwardTheta (EPLoc.rep f).isEquivalence_F.full
    ((EPLoc.rep f).Φ.isFunctorial_pullbackTheta hΘ'), pushforwardTheta_pullbackTheta hd.essSurj hΘ']

end Diagrams

theorem B_to_A : B → A := fun hB =>
  ⟨isEquivalence_Φ_iff', pushTheta_eq_of_isRefinement_B hB, pullTheta_eq_of_isRefinement',
    pushTheta_eq_of_equiv_B hB, pullTheta_eq_of_equiv', homMk_rep', equiv_rep_homMk',
    isEquivalence_rep_Φ', pushTheta_homMk_B hB, pullTheta_homMk', isFunctorial_pushTheta',
    isFunctorial_pullTheta', pushTheta_comp_B hB, pullTheta_comp', pushTheta_inv_B hB,
    pullTheta_pushTheta', pushTheta_pullTheta', pushforwardTheta_projRight_pullbackTheta',
    pushforwardTheta_projLeft_pullbackTheta'⟩

#rt_check RoundTrip.V11_16.A_to_B [
  Polyfold.EPLocalization.Diagram.IsRefinement.isEquivalence_Φ_iff,
  Polyfold.EPLocalization.Diagram.pushTheta_eq_of_isRefinement,
  Polyfold.EPLocalization.Diagram.pullTheta_eq_of_isRefinement,
  Polyfold.EPLocalization.Diagram.pushTheta_eq_of_equiv,
  Polyfold.EPLocalization.Diagram.pullTheta_eq_of_equiv,
  Polyfold.EPLocalization.EPLoc.homMk_rep, Polyfold.EPLocalization.EPLoc.equiv_rep_homMk,
  Polyfold.EPLocalization.EPLoc.isEquivalence_rep_Φ, Polyfold.EPLocalization.EPLoc.pushTheta_homMk,
  Polyfold.EPLocalization.EPLoc.pullTheta_homMk,
  Polyfold.EPLocalization.EPLoc.isFunctorial_pushTheta,
  Polyfold.EPLocalization.EPLoc.isFunctorial_pullTheta,
  Polyfold.EPLocalization.EPLoc.pushTheta_comp, Polyfold.EPLocalization.EPLoc.pullTheta_comp,
  Polyfold.EPLocalization.EPLoc.pushTheta_inv, Polyfold.EPLocalization.EPLoc.pullTheta_pushTheta,
  Polyfold.EPLocalization.EPLoc.pushTheta_pullTheta,
  Polyfold.WeakFibredProduct.pushforwardTheta_projRight_pullbackTheta,
  Polyfold.WeakFibredProduct.pushforwardTheta_projLeft_pullbackTheta]
#rt_check RoundTrip.V11_16.B_to_A [
  Polyfold.EPLocalization.Diagram.IsRefinement.isEquivalence_Φ_iff,
  Polyfold.EPLocalization.Diagram.pushTheta_eq_of_isRefinement,
  Polyfold.EPLocalization.Diagram.pullTheta_eq_of_isRefinement,
  Polyfold.EPLocalization.Diagram.pushTheta_eq_of_equiv,
  Polyfold.EPLocalization.Diagram.pullTheta_eq_of_equiv,
  Polyfold.EPLocalization.EPLoc.homMk_rep, Polyfold.EPLocalization.EPLoc.equiv_rep_homMk,
  Polyfold.EPLocalization.EPLoc.isEquivalence_rep_Φ, Polyfold.EPLocalization.EPLoc.pushTheta_homMk,
  Polyfold.EPLocalization.EPLoc.pullTheta_homMk,
  Polyfold.EPLocalization.EPLoc.isFunctorial_pushTheta,
  Polyfold.EPLocalization.EPLoc.isFunctorial_pullTheta,
  Polyfold.EPLocalization.EPLoc.pushTheta_comp, Polyfold.EPLocalization.EPLoc.pullTheta_comp,
  Polyfold.EPLocalization.EPLoc.pushTheta_inv, Polyfold.EPLocalization.EPLoc.pullTheta_pushTheta,
  Polyfold.EPLocalization.EPLoc.pushTheta_pullTheta,
  Polyfold.WeakFibredProduct.pushforwardTheta_projRight_pullbackTheta,
  Polyfold.WeakFibredProduct.pushforwardTheta_projLeft_pullbackTheta]
#rt_overlap RoundTrip.V11_16.B_to_A [
  Polyfold.EPLocalization.Diagram.IsRefinement.isEquivalence_Φ_iff,
  Polyfold.EPLocalization.Diagram.pushTheta_eq_of_isRefinement,
  Polyfold.EPLocalization.Diagram.pullTheta_eq_of_isRefinement,
  Polyfold.EPLocalization.Diagram.pushTheta_eq_of_equiv,
  Polyfold.EPLocalization.Diagram.pullTheta_eq_of_equiv,
  Polyfold.EPLocalization.EPLoc.homMk_rep, Polyfold.EPLocalization.EPLoc.equiv_rep_homMk,
  Polyfold.EPLocalization.EPLoc.isEquivalence_rep_Φ, Polyfold.EPLocalization.EPLoc.pushTheta_homMk,
  Polyfold.EPLocalization.EPLoc.pullTheta_homMk,
  Polyfold.EPLocalization.EPLoc.isFunctorial_pushTheta,
  Polyfold.EPLocalization.EPLoc.isFunctorial_pullTheta,
  Polyfold.EPLocalization.EPLoc.pushTheta_comp, Polyfold.EPLocalization.EPLoc.pullTheta_comp,
  Polyfold.EPLocalization.EPLoc.pushTheta_inv, Polyfold.EPLocalization.EPLoc.pullTheta_pushTheta,
  Polyfold.EPLocalization.EPLoc.pushTheta_pullTheta,
  Polyfold.WeakFibredProduct.pushforwardTheta_projRight_pullbackTheta,
  Polyfold.WeakFibredProduct.pushforwardTheta_projLeft_pullbackTheta]

end RoundTrip.V11_16
