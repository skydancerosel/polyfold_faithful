import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_15

/-! Round trip for V11_15 (Lemma 11.3.2 of the 2021 text, p. 536; 2017: Lemma 11.5: the
push-forward along an equivalence is well defined, a functor, inverse to the pull-back, and
invariant under natural equivalence).

`A` is the conjunction of the types of the fifteen listed theorems, universes at `0`:
`pushforwardTheta_eq` (well-definedness: `(F_*Θ)(y) = Θ(x)` for every `F(x) ≅ y`, `F` full),
`pushforwardTheta_obj`, `pushforwardTheta_eq_of_isomorphic`, `isFunctorial_pushforwardTheta`
(`F` full), `isFunctorial_pullbackTheta` (any `F`), `pullbackTheta_pushforwardTheta` (`F` full),
`pushforwardTheta_pullbackTheta` (`F` essentially surjective),
`pushforwardTheta_eq_of_naturallyEquivalent` (`F`, `G` full), `pullbackTheta_eq_of_naturallyEquivalent`
(any `F`, `G`), `pullbackTheta_comp`, `pushforwardTheta_comp` (full functors), `pushforwardTheta_id`,
and the groupoid facts `IsFunctorial.eq_of_isomorphic`, `isomorphic_obj`, `isomorphic_of_full`.
`Θ` is only asked to be a functor (`IsFunctorial`), of any sign.

`B` states the lemma for an equivalence `F` and functors `Θ : X → ℚ⁺` (nonnegative): some
`F(x) ≅ y` exists for every `y`, `Θ(x)` does not depend on the choice, `F_*Θ` is a functor to
`ℚ⁺`, `F^*F_*Θ = Θ`, `F_*F^*Θ' = Θ'`, and naturally equivalent equivalences have equal `F_*`, `F^*`.

* `A_to_B`: each claim of `B` from the corresponding conjunct of `A` (an equivalence is full and
  essentially surjective); the existence of `x` is the non-item `IsEquivalence.exists_iso`, the
  sign of `F_*Θ` the non-item (V11_14) `pushforwardTheta_nonneg`.
* `B_to_A` is vacuous: `A` is strictly more general (fullness or essential surjectivity instead
  of an equivalence, functors of any sign, plus `(G ∘ F)_*`, `(G ∘ F)^*`, `1_*` and three groupoid
  facts that `B` does not state).  It re-proves the fifteen statements outright by local copies
  of the project's proofs (`*'` below), from non-item lemmas (`full_iff`, `essSurj_iff`,
  `Isomorphic.trans`/`symm`/`refl`, the `EpNatTrans` fields).
* `B_to_A_on_domain` shows that `B` does give the text's content of `A` on `B`'s domain: for an
  equivalence and a functor to `ℚ⁺`, `(F_*Θ)(y) = Θ(x)` for every `F(x) ≅ y`
  (`pushforwardTheta_eq`), from `F^*F_*Θ = Θ` and the functoriality of `F_*Θ`. -/

namespace RoundTrip.V11_15
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.pushforwardTheta_eq.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.pushforwardTheta_obj.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.pushforwardTheta_eq_of_isomorphic.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.isFunctorial_pushforwardTheta.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.isFunctorial_pullbackTheta.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.pullbackTheta_pushforwardTheta.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.pushforwardTheta_pullbackTheta.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.pushforwardTheta_eq_of_naturallyEquivalent.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.pullbackTheta_eq_of_naturallyEquivalent.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.pullbackTheta_comp.{0, 0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.pushforwardTheta_comp.{0, 0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.pushforwardTheta_id.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.IsFunctorial.eq_of_isomorphic.{0}) ∧
  (type_of% @Polyfold.EpFunctor.isomorphic_obj.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.isomorphic_of_full.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.pushforwardTheta_eq.{0, 0},
    @Polyfold.EpFunctor.pushforwardTheta_obj.{0, 0},
    @Polyfold.EpFunctor.pushforwardTheta_eq_of_isomorphic.{0, 0},
    @Polyfold.EpFunctor.isFunctorial_pushforwardTheta.{0, 0},
    @Polyfold.EpFunctor.isFunctorial_pullbackTheta.{0, 0},
    @Polyfold.EpFunctor.pullbackTheta_pushforwardTheta.{0, 0},
    @Polyfold.EpFunctor.pushforwardTheta_pullbackTheta.{0, 0},
    @Polyfold.EpFunctor.pushforwardTheta_eq_of_naturallyEquivalent.{0, 0},
    @Polyfold.EpFunctor.pullbackTheta_eq_of_naturallyEquivalent.{0, 0},
    @Polyfold.EpFunctor.pullbackTheta_comp.{0, 0, 0},
    @Polyfold.EpFunctor.pushforwardTheta_comp.{0, 0, 0},
    @Polyfold.EpFunctor.pushforwardTheta_id.{0},
    @Polyfold.EpGroupoid.IsFunctorial.eq_of_isomorphic.{0},
    @Polyfold.EpFunctor.isomorphic_obj.{0, 0},
    @Polyfold.EpFunctor.isomorphic_of_full.{0, 0}⟩

theorem A_to_B : A → B := by
  rintro ⟨heq, -, -, hfun, -, hpp, hpp', hnat, hnat', -, -, -, -, -, -⟩
  intro Obj Mor Obj' Mor' _ _ _ _ _ _ _ _ _ _ _ _ X Y F hF
  refine ⟨fun Θ hΘ => ⟨hF.exists_iso, fun y x x' ψ ψ' hs ht hs' ht' => ?_,
      ⟨EpFunctor.pushforwardTheta_nonneg hΘ.1, hfun hF.full hΘ.2⟩, hpp hF.full hΘ.2⟩,
    fun Θ' hΘ' => hpp' hF.essSurj hΘ'.2,
    fun G hG hFG => ⟨fun Θ hΘ => hnat hF.full hG.full hFG hΘ.2,
      fun Θ' hΘ' => hnat' hFG hΘ'.2⟩⟩
  rw [← heq hF.full hΘ.2 ⟨ψ, hs, ht⟩, heq hF.full hΘ.2 ⟨ψ', hs', ht'⟩]

/-! ### Local copies of the project's proofs (for `B_to_A`, which cannot get `A` from `B`) -/

section Copies

universe u v w

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {Obj'' Mor'' : Type w} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Z : EpGroupoid Obj'' Mor''}

theorem eq_of_isomorphic' {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) {x x' : Obj}
    (h : X.Isomorphic x x') : Θ x = Θ x' := by
  obtain ⟨φ, rfl, rfl⟩ := h
  exact hΘ φ

theorem isomorphic_obj' (F : EpFunctor X Y) {x x' : Obj} (h : X.Isomorphic x x') :
    Y.Isomorphic (F.obj x) (F.obj x') := by
  obtain ⟨φ, rfl, rfl⟩ := h
  exact ⟨F.mor φ, F.src_mor φ, F.tgt_mor φ⟩

theorem isomorphic_of_full' {F : EpFunctor X Y} (hF : F.toFunctor.Full) {x x' : Obj}
    (h : Y.Isomorphic (F.obj x) (F.obj x')) : X.Isomorphic x x' := by
  obtain ⟨ψ, hs, ht⟩ := h
  obtain ⟨φ, h1, h2, -⟩ := (F.full_iff.1 hF) x x' ψ hs ht
  exact ⟨φ, h1, h2⟩

theorem pushforwardTheta_eq' {F : EpFunctor X Y} (hF : F.toFunctor.Full) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) {x : Obj} {y : Obj'} (h : Y.Isomorphic (F.obj x) y) :
    F.pushforwardTheta Θ y = Θ x := by
  have hex : ∃ x, Y.Isomorphic (F.obj x) y := ⟨x, h⟩
  rw [EpFunctor.pushforwardTheta, dif_pos hex]
  exact eq_of_isomorphic' hΘ (isomorphic_of_full' hF (hex.choose_spec.trans h.symm))

theorem pushforwardTheta_obj' {F : EpFunctor X Y} (hF : F.toFunctor.Full) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) (x : Obj) : F.pushforwardTheta Θ (F.obj x) = Θ x :=
  pushforwardTheta_eq' hF hΘ (Y.isomorphic_refl _)

theorem pushforwardTheta_of_not_exists' {F : EpFunctor X Y} {Θ : Obj → ℚ} {y : Obj'}
    (h : ¬ ∃ x, Y.Isomorphic (F.obj x) y) : F.pushforwardTheta Θ y = 0 := by
  rw [EpFunctor.pushforwardTheta, dif_neg h]

theorem pushforwardTheta_eq_of_isomorphic' {F : EpFunctor X Y} (hF : F.toFunctor.Full)
    {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) {y y' : Obj'} (h : Y.Isomorphic y y') :
    F.pushforwardTheta Θ y = F.pushforwardTheta Θ y' := by
  by_cases hex : ∃ x, Y.Isomorphic (F.obj x) y
  · obtain ⟨x, hx⟩ := hex
    rw [pushforwardTheta_eq' hF hΘ hx, pushforwardTheta_eq' hF hΘ (hx.trans h)]
  · rw [pushforwardTheta_of_not_exists' hex, pushforwardTheta_of_not_exists' fun ⟨x, hx⟩ =>
      hex ⟨x, hx.trans h.symm⟩]

theorem isFunctorial_pushforwardTheta' {F : EpFunctor X Y} (hF : F.toFunctor.Full)
    {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) : Y.IsFunctorial (F.pushforwardTheta Θ) := fun φ =>
  pushforwardTheta_eq_of_isomorphic' hF hΘ ⟨φ, rfl, rfl⟩

theorem isFunctorial_pullbackTheta' (F : EpFunctor X Y) {Θ' : Obj' → ℚ}
    (hΘ' : Y.IsFunctorial Θ') : X.IsFunctorial (F.pullbackTheta Θ') := fun φ => by
  change Θ' (F.obj (X.src φ)) = Θ' (F.obj (X.tgt φ))
  rw [← F.src_mor, ← F.tgt_mor]
  exact hΘ' (F.mor φ)

theorem pullbackTheta_pushforwardTheta' {F : EpFunctor X Y} (hF : F.toFunctor.Full)
    {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) : F.pullbackTheta (F.pushforwardTheta Θ) = Θ :=
  funext fun x => pushforwardTheta_obj' hF hΘ x

theorem pushforwardTheta_pullbackTheta' {F : EpFunctor X Y} (hF : F.toFunctor.EssSurj)
    {Θ' : Obj' → ℚ} (hΘ' : Y.IsFunctorial Θ') :
    F.pushforwardTheta (F.pullbackTheta Θ') = Θ' := by
  funext y
  have hex : ∃ x, Y.Isomorphic (F.obj x) y := (F.essSurj_iff.1 hF) y |>.imp
    fun x ⟨ψ, hs, ht⟩ => ⟨ψ, hs, ht⟩
  rw [EpFunctor.pushforwardTheta, dif_pos hex]
  exact eq_of_isomorphic' hΘ' hex.choose_spec

theorem pushforwardTheta_eq_of_naturallyEquivalent' {F G : EpFunctor X Y}
    (hF : F.toFunctor.Full) (hG : G.toFunctor.Full) (hFG : F.NaturallyEquivalent G)
    {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) : F.pushforwardTheta Θ = G.pushforwardTheta Θ := by
  obtain ⟨τ⟩ := hFG
  have hτ : ∀ x, Y.Isomorphic (F.obj x) (G.obj x) := fun x => ⟨τ.app x, τ.src_app x, τ.tgt_app x⟩
  funext y
  by_cases hex : ∃ x, Y.Isomorphic (F.obj x) y
  · obtain ⟨x, hx⟩ := hex
    rw [pushforwardTheta_eq' hF hΘ hx, pushforwardTheta_eq' hG hΘ ((hτ x).symm.trans hx)]
  · rw [pushforwardTheta_of_not_exists' hex, pushforwardTheta_of_not_exists' fun ⟨x, hx⟩ =>
      hex ⟨x, (hτ x).trans hx⟩]

theorem pullbackTheta_eq_of_naturallyEquivalent' {F G : EpFunctor X Y}
    (hFG : F.NaturallyEquivalent G) {Θ' : Obj' → ℚ} (hΘ' : Y.IsFunctorial Θ') :
    F.pullbackTheta Θ' = G.pullbackTheta Θ' := by
  obtain ⟨τ⟩ := hFG
  funext x
  exact eq_of_isomorphic' hΘ' ⟨τ.app x, τ.src_app x, τ.tgt_app x⟩

theorem pushforwardTheta_comp' {F : EpFunctor X Y} {G : EpFunctor Y Z} (hG : G.toFunctor.Full)
    (hF : F.toFunctor.Full) (hGF : (G.comp F).toFunctor.Full) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) :
    (G.comp F).pushforwardTheta Θ = G.pushforwardTheta (F.pushforwardTheta Θ) := by
  funext z
  by_cases hex : ∃ x, Z.Isomorphic (G.obj (F.obj x)) z
  · obtain ⟨x, hx⟩ := hex
    rw [pushforwardTheta_eq' hGF hΘ hx,
      pushforwardTheta_eq' hG (isFunctorial_pushforwardTheta' hF hΘ) hx,
      pushforwardTheta_obj' hF hΘ]
  · rw [pushforwardTheta_of_not_exists' hex]
    by_cases hey : ∃ y, Z.Isomorphic (G.obj y) z
    · obtain ⟨y, hy⟩ := hey
      rw [pushforwardTheta_eq' hG (isFunctorial_pushforwardTheta' hF hΘ) hy,
        pushforwardTheta_of_not_exists' fun ⟨x, hx⟩ =>
          hex ⟨x, (isomorphic_obj' G hx).trans hy⟩]
    · rw [pushforwardTheta_of_not_exists' hey]

theorem pushforwardTheta_id' {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ) :
    (EpFunctor.id X).pushforwardTheta Θ = Θ :=
  funext fun x => pushforwardTheta_obj' (EpFunctor.IsEquivalence.id X).full hΘ x

end Copies

/-- Vacuous: `A` is re-proved outright from the local copies (it is more general than `B`). -/
theorem B_to_A : B → A := fun _ =>
  ⟨@pushforwardTheta_eq'.{0, 0}, @pushforwardTheta_obj'.{0, 0},
    @pushforwardTheta_eq_of_isomorphic'.{0, 0}, @isFunctorial_pushforwardTheta'.{0, 0},
    @isFunctorial_pullbackTheta'.{0, 0}, @pullbackTheta_pushforwardTheta'.{0, 0},
    @pushforwardTheta_pullbackTheta'.{0, 0}, @pushforwardTheta_eq_of_naturallyEquivalent'.{0, 0},
    @pullbackTheta_eq_of_naturallyEquivalent'.{0, 0}, fun _ _ _ => rfl,
    @pushforwardTheta_comp'.{0, 0, 0}, @pushforwardTheta_id'.{0}, @eq_of_isomorphic'.{0},
    @isomorphic_obj'.{0, 0}, @isomorphic_of_full'.{0, 0}⟩

/-- On `B`'s domain (an equivalence, a functor to `ℚ⁺`), `B` gives the well-definedness
`pushforwardTheta_eq` of `A`: `(F_*Θ)(y) = (F_*Θ)(F x) = Θ(x)` for `ψ : F(x) → y`. -/
theorem B_to_A_on_domain (hB : B) {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {F : EpFunctor X Y}
    (hF : F.IsEquivalence) {Θ : Obj → ℚ} (hΘ : IsQFunctorB X Θ) {x : Obj} {y : Obj'}
    (h : Y.Isomorphic (F.obj x) y) : F.pushforwardTheta Θ y = Θ x := by
  obtain ⟨-, -, hfun, hpp⟩ := (hB Obj Mor Obj' Mor' X Y F hF).1 Θ hΘ
  obtain ⟨ψ, hs, ht⟩ := h
  have h1 := hfun.2 ψ
  rw [hs, ht] at h1
  rw [← h1]
  exact congrFun hpp x

#rt_check RoundTrip.V11_15.A_to_B [Polyfold.EpFunctor.pushforwardTheta_eq,
  Polyfold.EpFunctor.pushforwardTheta_obj, Polyfold.EpFunctor.pushforwardTheta_eq_of_isomorphic,
  Polyfold.EpFunctor.isFunctorial_pushforwardTheta, Polyfold.EpFunctor.isFunctorial_pullbackTheta,
  Polyfold.EpFunctor.pullbackTheta_pushforwardTheta,
  Polyfold.EpFunctor.pushforwardTheta_pullbackTheta,
  Polyfold.EpFunctor.pushforwardTheta_eq_of_naturallyEquivalent,
  Polyfold.EpFunctor.pullbackTheta_eq_of_naturallyEquivalent, Polyfold.EpFunctor.pullbackTheta_comp,
  Polyfold.EpFunctor.pushforwardTheta_comp, Polyfold.EpFunctor.pushforwardTheta_id,
  Polyfold.EpGroupoid.IsFunctorial.eq_of_isomorphic, Polyfold.EpFunctor.isomorphic_obj,
  Polyfold.EpFunctor.isomorphic_of_full]
#rt_check RoundTrip.V11_15.B_to_A [Polyfold.EpFunctor.pushforwardTheta_eq,
  Polyfold.EpFunctor.pushforwardTheta_obj, Polyfold.EpFunctor.pushforwardTheta_eq_of_isomorphic,
  Polyfold.EpFunctor.isFunctorial_pushforwardTheta, Polyfold.EpFunctor.isFunctorial_pullbackTheta,
  Polyfold.EpFunctor.pullbackTheta_pushforwardTheta,
  Polyfold.EpFunctor.pushforwardTheta_pullbackTheta,
  Polyfold.EpFunctor.pushforwardTheta_eq_of_naturallyEquivalent,
  Polyfold.EpFunctor.pullbackTheta_eq_of_naturallyEquivalent, Polyfold.EpFunctor.pullbackTheta_comp,
  Polyfold.EpFunctor.pushforwardTheta_comp, Polyfold.EpFunctor.pushforwardTheta_id,
  Polyfold.EpGroupoid.IsFunctorial.eq_of_isomorphic, Polyfold.EpFunctor.isomorphic_obj,
  Polyfold.EpFunctor.isomorphic_of_full]
#rt_check RoundTrip.V11_15.B_to_A_on_domain [Polyfold.EpFunctor.pushforwardTheta_eq,
  Polyfold.EpFunctor.pushforwardTheta_obj, Polyfold.EpFunctor.pushforwardTheta_eq_of_isomorphic,
  Polyfold.EpFunctor.isFunctorial_pushforwardTheta, Polyfold.EpFunctor.isFunctorial_pullbackTheta,
  Polyfold.EpFunctor.pullbackTheta_pushforwardTheta,
  Polyfold.EpFunctor.pushforwardTheta_pullbackTheta,
  Polyfold.EpFunctor.pushforwardTheta_eq_of_naturallyEquivalent,
  Polyfold.EpFunctor.pullbackTheta_eq_of_naturallyEquivalent, Polyfold.EpFunctor.pullbackTheta_comp,
  Polyfold.EpFunctor.pushforwardTheta_comp, Polyfold.EpFunctor.pushforwardTheta_id,
  Polyfold.EpGroupoid.IsFunctorial.eq_of_isomorphic, Polyfold.EpFunctor.isomorphic_obj,
  Polyfold.EpFunctor.isomorphic_of_full]
#rt_overlap RoundTrip.V11_15.B_to_A [Polyfold.EpFunctor.pushforwardTheta_eq,
  Polyfold.EpFunctor.pushforwardTheta_obj, Polyfold.EpFunctor.pushforwardTheta_eq_of_isomorphic,
  Polyfold.EpFunctor.isFunctorial_pushforwardTheta, Polyfold.EpFunctor.isFunctorial_pullbackTheta,
  Polyfold.EpFunctor.pullbackTheta_pushforwardTheta,
  Polyfold.EpFunctor.pushforwardTheta_pullbackTheta,
  Polyfold.EpFunctor.pushforwardTheta_eq_of_naturallyEquivalent,
  Polyfold.EpFunctor.pullbackTheta_eq_of_naturallyEquivalent, Polyfold.EpFunctor.pullbackTheta_comp,
  Polyfold.EpFunctor.pushforwardTheta_comp, Polyfold.EpFunctor.pushforwardTheta_id,
  Polyfold.EpGroupoid.IsFunctorial.eq_of_isomorphic, Polyfold.EpFunctor.isomorphic_obj,
  Polyfold.EpFunctor.isomorphic_of_full]

end RoundTrip.V11_15
