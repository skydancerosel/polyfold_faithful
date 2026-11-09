import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_38

set_option maxSynthPendingDepth 3

/-!
Round trip for V11_38 (Theorem 11.6.6 (1), steps (A)–(C) of its proof; 2021 p. 555, pp. 556–560).

The item lists the definitions `hFunctor`, `hObj`, `hMor` (vocabulary) and twelve theorems.  `A`
is the conjunction of the types of the theorems, universes at `0`: `mor_conj`, `hMor_src`,
`hMor_tgt` (well-definedness of `H`), step (A) `surjective_hObj`, `isLocalScDiffeo_hObj`, step (B)
`isScDiffeo_fibredMap_hFunctor`, step (C) `finite_fiber_hObj`, `isProperMap_hObj`, the general
facts `IsScDiffeoOn.restrictTarget`, `IsLocalScDiffeo.evenlyCovered_of_isProperMap`,
`IsProperCovering.isProperMap`, and the assembled `isProperCovering_hFunctor_of`.

`B` (Theorem 11.6.6 (1)): for proper coverings `F, F', F''`, an equivalence `Γ = (Ψ, Φ) : F → F'`
and a functor `Λ = (ζ, ξ) : F'' → F'`, there is an `EpFunctor H : P → Q` given by (11.18),
(11.19), and it is a proper covering.

* `A ⇒ B` (`A_to_B`, via `A'_to_B`): `H := hFunctor` (its entries are those of (11.18), (11.19)
  by `rfl`), a proper covering by `isProperCovering_hFunctor_of`, whose hypotheses `hΨ`, `hΦ`
  (local sc-diffeomorphisms on objects) and `hs` (`Ψ : Y_x → Y'_{Φ(x)}` onto) come from the
  equivalence `Γ` (fields of `IsEquivalence`).
* `B ⇒ A` fails, for a genuine reason: `A`'s main conjunct `isProperCovering_hFunctor_of` is more
  general than the text's (1) (it needs only `Ψ`, `Φ` local sc-diffeomorphisms on objects and
  `Ψ` onto on fibres, not `Γ` an equivalence), and `A` contains the general lemmas
  `restrictTarget`, `evenlyCovered_of_isProperMap` (a proper local sc-diffeomorphism with finite
  fibre is evenly covered) and `IsProperCovering.isProperMap`, and the steps (A)–(C) as separate
  statements, none of which follows from `B`.  What `B` does give is `A`'s main conjunct in the
  text's case `Γ` an equivalence (`B_to_isProperCovering_hFunctor'`).

**Harness note.**  The statement of `isProperCovering_hFunctor_of` (and of
`isScDiffeo_fibredMap_hFunctor`) contains `hFunctor`, whose fields `src_mor := hMor_src` and
`tgt_mor := hMor_tgt` are the banned theorems themselves, as plain constants (not abstracted into
`hFunctor._proof_N`; `mor_comp := hFunctor._proof_9` also uses them).  So every term mentioning `A`
reaches `hMor_src`, `hMor_tgt`, `mor_conj`, and `#rt_check` and `#rt_check_soft` fail on `A_to_B`
for these three names only (recorded with `#guard_msgs`).  We use the `A'` pattern: `hFunctor'`
is a copy of `hFunctor` (same signature, same object and morphism maps) whose proof fields are
proved here from non-item lemmas (copies `mor_conj'`, `hMor_src'`, `hMor_tgt'`); `A'` is `A` with
the constant `hFunctor` replaced by `hFunctor'` (mechanically, by the elaborator
`replace_hFunctor%`); `A = A'` by `rfl` (`A_eq_A'`, proof irrelevance); `A'_to_B` passes plain
`#rt_check`, and `A_to_B := A'_to_B ∘ (A_eq_A' ▸ ·)`.
-/

namespace RoundTrip.V11_38
open Polyfold

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.ProperCoveringHom.mor_conj.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.hMor_src.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.hMor_tgt.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.surjective_hObj.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.isLocalScDiffeo_hObj.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.isScDiffeo_fibredMap_hFunctor.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.finite_fiber_hObj.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.isProperMap_hObj.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.isProperCovering_hFunctor_of.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.MPolyfold.IsScDiffeoOn.restrictTarget.{0, 0} ∧
  type_of% @Polyfold.MPolyfold.IsLocalScDiffeo.evenlyCovered_of_isProperMap.{0, 0} ∧
  type_of% @Polyfold.EpFunctor.IsProperCovering.isProperMap.{0, 0}

theorem A_holds : A :=
  ⟨@ProperCoveringHom.mor_conj, @ProperCoveringHom.hMor_src, @ProperCoveringHom.hMor_tgt,
    @ProperCoveringHom.surjective_hObj, @ProperCoveringHom.isLocalScDiffeo_hObj,
    @ProperCoveringHom.isScDiffeo_fibredMap_hFunctor, @ProperCoveringHom.finite_fiber_hObj,
    @ProperCoveringHom.isProperMap_hObj, @ProperCoveringHom.isProperCovering_hFunctor_of,
    @MPolyfold.IsScDiffeoOn.restrictTarget, @MPolyfold.IsLocalScDiffeo.evenlyCovered_of_isProperMap,
    @EpFunctor.IsProperCovering.isProperMap⟩

/-! ### `hFunctor'`: a copy of `hFunctor` with proof fields proved from non-item lemmas -/

section HFunctor'

variable {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY' MorY' : Type} [TopologicalSpace ObjY'] [T2Space ObjY'] [ParacompactSpace ObjY']
  [TopologicalSpace MorY'] [T2Space MorY'] [ParacompactSpace MorY']
  {ObjX' MorX' : Type} [TopologicalSpace ObjX'] [T2Space ObjX'] [ParacompactSpace ObjX']
  [TopologicalSpace MorX'] [T2Space MorX'] [ParacompactSpace MorX']
  {ObjY'' MorY'' : Type} [TopologicalSpace ObjY''] [T2Space ObjY''] [ParacompactSpace ObjY'']
  [TopologicalSpace MorY''] [T2Space MorY''] [ParacompactSpace MorY'']
  {ObjX'' MorX'' : Type} [TopologicalSpace ObjX''] [T2Space ObjX''] [ParacompactSpace ObjX'']
  [TopologicalSpace MorX''] [T2Space MorX''] [ParacompactSpace MorX'']
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}
  {Y' : EpGroupoid ObjY' MorY'} {X' : EpGroupoid ObjX' MorX'}
  {Y'' : EpGroupoid ObjY'' MorY''} {X'' : EpGroupoid ObjX'' MorX''}
  {F : EpFunctor Y X} {F' : EpFunctor Y' X'} {F'' : EpFunctor Y'' X''}
  (Γ : ProperCoveringHom F F') (Λ : ProperCoveringHom F'' F')

open WeakFibredProduct ProperCoveringHom

/-- Copy of `mor_conj` (its proof uses only Chapter 7/10 lemmas). -/
theorem mor_conj' {h : MorY} {φ : MorY'} {k : MorY''} (h₁ : Y'.src φ = Γ.Ψ.obj (Y.src h))
    (h₂ : Y'.tgt φ = Λ.Ψ.obj (Y''.src k)) :
    F'.mor (conj Γ.Ψ Λ.Ψ h φ k) = conj Γ.Φ Λ.Φ (F.mor h) (F'.mor φ) (F''.mor k) := by
  have e₁ : Y'.src (Λ.Ψ.mor k) = Y'.tgt φ := by rw [Λ.Ψ.src_mor, h₂]
  have e₂ : Y'.src (Y'.comp (Λ.Ψ.mor k) φ) = Y'.tgt (Y'.inv (Γ.Ψ.mor h)) := by
    rw [Y'.src_comp _ _ e₁, Y'.tgt_inv, Γ.Ψ.src_mor, h₁]
  unfold conj
  rw [F'.mor_comp _ _ e₂, F'.mor_comp _ _ e₁, GroupoidFunctor.mor_inv, ← Γ.comm_mor,
    ← Λ.comm_mor]

theorem hMor_src' (m : Mor Γ.Ψ Λ.Ψ) : src (hMor Γ Λ m) = hObj Γ Λ (src m) :=
  Obj.ext (F.src_mor _) rfl (F''.src_mor _)

theorem hMor_tgt' (m : Mor Γ.Ψ Λ.Ψ) : tgt (hMor Γ Λ m) = hObj Γ Λ (tgt m) :=
  Obj.ext (F.tgt_mor _) (mor_conj' Γ Λ m.src_φ m.tgt_φ).symm (F''.tgt_mor _)

/-- A copy of `ProperCoveringHom.hFunctor` (same signature, same `obj := hObj Γ Λ`,
`mor := hMor Γ Λ`), with the proof fields proved here. -/
def hFunctor' (hP : Admissible Γ.Ψ Λ.Ψ) (hQ : Admissible Γ.Φ Λ.Φ) :
    EpFunctor (epGroupoid Γ.Ψ Λ.Ψ hP) (epGroupoid Γ.Φ Λ.Φ hQ) where
  obj := hObj Γ Λ
  mor := hMor Γ Λ
  src_mor := hMor_src' Γ Λ
  tgt_mor := hMor_tgt' Γ Λ
  mor_comp m m' hc := by
    have hc' : src (hMor Γ Λ m) = tgt (hMor Γ Λ m') := by
      rw [hMor_src', hMor_tgt']; exact congrArg _ hc
    change hMor Γ Λ (WeakFibredProduct.comp m m') =
      WeakFibredProduct.comp (hMor Γ Λ m) (hMor Γ Λ m')
    refine Mor.ext ?_ ?_ ?_
    · rw [h_comp hc', hMor_h, h_comp hc]
      exact F.mor_comp _ _ (src_eq_tgt_iff.1 hc).1
    · rw [φ_comp hc', hMor_φ, φ_comp hc]; rfl
    · rw [k_comp hc', hMor_k, k_comp hc]
      exact F''.mor_comp _ _ (src_eq_tgt_iff.1 hc).2.2
  mor_unit p := Mor.ext (F.mor_unit _) rfl (F''.mor_unit _)
  isScSmoothMap_obj := isScSmoothOn_obj_of hQ (F.isScSmoothMap_obj.comp (isScSmoothMap_x hP))
    (F'.isScSmoothMap_mor.comp (isScSmoothMap_φ hP))
    (F''.isScSmoothMap_obj.comp (isScSmoothMap_z hP))
  isScSmoothMap_mor := isScSmoothOn_mor_of hQ (F.isScSmoothMap_mor.comp (isScSmoothMap_h hP))
    (F'.isScSmoothMap_mor.comp (isScSmoothMap_mφ hP))
    (F''.isScSmoothMap_mor.comp (isScSmoothMap_k hP))

end HFunctor'

/-- Same signature, and the same functor (definitional, by proof irrelevance). -/
example : type_of% @hFunctor' = type_of% @ProperCoveringHom.hFunctor.{0, 0, 0, 0, 0, 0} := rfl
example : @hFunctor' = @ProperCoveringHom.hFunctor.{0, 0, 0, 0, 0, 0} := rfl

open Lean Elab Term Meta in
/-- `replace_hFunctor% t`: the term `t` with every occurrence of the constant
`Polyfold.ProperCoveringHom.hFunctor.{0,…,0}` replaced by `RoundTrip.V11_38.hFunctor'`. -/
elab "replace_hFunctor% " t:term : term => do
  let e ← instantiateMVars (← elabTerm t none)
  let e' := e.replace fun s => match s with
    | .const n us =>
      if n == ``Polyfold.ProperCoveringHom.hFunctor && us.all (·.isZero) then
        some (.const ``RoundTrip.V11_38.hFunctor' [])
      else none
    | _ => none
  if e'.getUsedConstants.contains ``Polyfold.ProperCoveringHom.hFunctor then
    throwError "replace_hFunctor%: an occurrence of hFunctor at nonzero universes is left"
  return e'

/-- `A` with `hFunctor` replaced by its copy `hFunctor'`. -/
def A' : Prop := replace_hFunctor%
  (type_of% @Polyfold.ProperCoveringHom.mor_conj.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.hMor_src.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.hMor_tgt.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.surjective_hObj.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.isLocalScDiffeo_hObj.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.isScDiffeo_fibredMap_hFunctor.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.finite_fiber_hObj.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.isProperMap_hObj.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.ProperCoveringHom.isProperCovering_hFunctor_of.{0, 0, 0, 0, 0, 0} ∧
  type_of% @Polyfold.MPolyfold.IsScDiffeoOn.restrictTarget.{0, 0} ∧
  type_of% @Polyfold.MPolyfold.IsLocalScDiffeo.evenlyCovered_of_isProperMap.{0, 0} ∧
  type_of% @Polyfold.EpFunctor.IsProperCovering.isProperMap.{0, 0})

theorem A_eq_A' : A = A' := rfl

/-- `A' ⇒ B`: `H := hFunctor' Γ Λ` (the entries of (11.18), (11.19) by `rfl`), a proper covering
by `A`'s `isProperCovering_hFunctor_of`, with `hΨ`, `hΦ`, `hs` from the equivalence `Γ`. -/
theorem A'_to_B (hA : A') : B := by
  intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ ObjY' MorY' _ _ _ _ _ _
    ObjX' MorX' _ _ _ _ _ _ ObjY'' MorY'' _ _ _ _ _ _ ObjX'' MorX'' _ _ _ _ _ _
    Y X Y' X' Y'' X'' F F' F'' hF hF' hF'' Γ hΓ Λ
  obtain ⟨-, -, -, -, -, -, -, -, hmain, -⟩ := hA
  refine ⟨hFunctor' Γ Λ (Or.inl hΓ.isEquivalence_Ψ.isLocalScDiffeo_obj)
      (Or.inl hΓ.isEquivalence_Φ.isLocalScDiffeo_obj),
    ⟨fun o => ⟨rfl, rfl, rfl⟩, fun m => ⟨rfl, rfl, rfl⟩⟩, ?_⟩
  exact hmain (Γ := Γ) (Λ := Λ) _ _ hΓ.isEquivalence_Ψ.isLocalScDiffeo_obj
    hΓ.isEquivalence_Φ.isLocalScDiffeo_obj (fun x => (hΓ.isFiberBijective x).surjOn) hF hF' hF''

theorem A_to_B (hA : A) : B := A'_to_B (A_eq_A' ▸ hA)

/-- What `B` gives of `A`: the main conjunct `isProperCovering_hFunctor_of` in the text's case
`Γ` an equivalence (any admissibility proofs; stated with the copy `hFunctor'`, equal to
`hFunctor` by `rfl`).  `B`'s `H` is `hFunctor'` by `EpFunctor.ext`. -/
theorem B_to_isProperCovering_hFunctor' (hB : B)
    {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    {ObjY' MorY' : Type} [TopologicalSpace ObjY'] [T2Space ObjY'] [ParacompactSpace ObjY']
    [TopologicalSpace MorY'] [T2Space MorY'] [ParacompactSpace MorY']
    {ObjX' MorX' : Type} [TopologicalSpace ObjX'] [T2Space ObjX'] [ParacompactSpace ObjX']
    [TopologicalSpace MorX'] [T2Space MorX'] [ParacompactSpace MorX']
    {ObjY'' MorY'' : Type} [TopologicalSpace ObjY''] [T2Space ObjY''] [ParacompactSpace ObjY'']
    [TopologicalSpace MorY''] [T2Space MorY''] [ParacompactSpace MorY'']
    {ObjX'' MorX'' : Type} [TopologicalSpace ObjX''] [T2Space ObjX''] [ParacompactSpace ObjX'']
    [TopologicalSpace MorX''] [T2Space MorX''] [ParacompactSpace MorX'']
    {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}
    {Y' : EpGroupoid ObjY' MorY'} {X' : EpGroupoid ObjX' MorX'}
    {Y'' : EpGroupoid ObjY'' MorY''} {X'' : EpGroupoid ObjX'' MorX''}
    {F : EpFunctor Y X} {F' : EpFunctor Y' X'} {F'' : EpFunctor Y'' X''}
    (Γ : ProperCoveringHom F F') (Λ : ProperCoveringHom F'' F')
    (hP : WeakFibredProduct.Admissible Γ.Ψ Λ.Ψ) (hQ : WeakFibredProduct.Admissible Γ.Φ Λ.Φ)
    (hΓ : Γ.IsEquivalence)
    (hF : F.IsProperCovering) (hF' : F'.IsProperCovering) (hF'' : F''.IsProperCovering) :
    (hFunctor' Γ Λ hP hQ).IsProperCovering := by
  obtain ⟨H, ⟨ho, hm⟩, hH⟩ := hB ObjY MorY ObjX MorX ObjY' MorY' ObjX' MorX' ObjY'' MorY''
    ObjX'' MorX'' Y X Y' X' Y'' X'' F F' F'' hF hF' hF'' Γ hΓ Λ
  have e : H = hFunctor' Γ Λ hP hQ :=
    EpFunctor.ext (funext fun o => WeakFibredProduct.Obj.ext (ho o).1 (ho o).2.1 (ho o).2.2)
      (funext fun m => WeakFibredProduct.Mor.ext (hm m).1 (hm m).2.1 (hm m).2.2)
  subst e
  exact hH

/--
error: rt_check FAIL: RoundTrip.V11_38.A_to_B uses [Polyfold.ProperCoveringHom.mor_conj,
 Polyfold.ProperCoveringHom.hMor_src,
 Polyfold.ProperCoveringHom.hMor_tgt]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V11_38.A_to_B [Polyfold.ProperCoveringHom.mor_conj,
  Polyfold.ProperCoveringHom.hMor_src, Polyfold.ProperCoveringHom.hMor_tgt,
  Polyfold.ProperCoveringHom.surjective_hObj, Polyfold.ProperCoveringHom.isLocalScDiffeo_hObj,
  Polyfold.ProperCoveringHom.isScDiffeo_fibredMap_hFunctor,
  Polyfold.ProperCoveringHom.finite_fiber_hObj, Polyfold.ProperCoveringHom.isProperMap_hObj,
  Polyfold.ProperCoveringHom.isProperCovering_hFunctor_of,
  Polyfold.MPolyfold.IsScDiffeoOn.restrictTarget,
  Polyfold.MPolyfold.IsLocalScDiffeo.evenlyCovered_of_isProperMap,
  Polyfold.EpFunctor.IsProperCovering.isProperMap]

/--
error: rt_check_soft FAIL: RoundTrip.V11_38.A_to_B uses [Polyfold.ProperCoveringHom.mor_conj,
 Polyfold.ProperCoveringHom.hMor_src,
 Polyfold.ProperCoveringHom.hMor_tgt]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V11_38.A_to_B [Polyfold.ProperCoveringHom.mor_conj,
  Polyfold.ProperCoveringHom.hMor_src, Polyfold.ProperCoveringHom.hMor_tgt,
  Polyfold.ProperCoveringHom.surjective_hObj, Polyfold.ProperCoveringHom.isLocalScDiffeo_hObj,
  Polyfold.ProperCoveringHom.isScDiffeo_fibredMap_hFunctor,
  Polyfold.ProperCoveringHom.finite_fiber_hObj, Polyfold.ProperCoveringHom.isProperMap_hObj,
  Polyfold.ProperCoveringHom.isProperCovering_hFunctor_of,
  Polyfold.MPolyfold.IsScDiffeoOn.restrictTarget,
  Polyfold.MPolyfold.IsLocalScDiffeo.evenlyCovered_of_isProperMap,
  Polyfold.EpFunctor.IsProperCovering.isProperMap]

#rt_check RoundTrip.V11_38.A'_to_B [Polyfold.ProperCoveringHom.mor_conj,
  Polyfold.ProperCoveringHom.hMor_src, Polyfold.ProperCoveringHom.hMor_tgt,
  Polyfold.ProperCoveringHom.surjective_hObj, Polyfold.ProperCoveringHom.isLocalScDiffeo_hObj,
  Polyfold.ProperCoveringHom.isScDiffeo_fibredMap_hFunctor,
  Polyfold.ProperCoveringHom.finite_fiber_hObj, Polyfold.ProperCoveringHom.isProperMap_hObj,
  Polyfold.ProperCoveringHom.isProperCovering_hFunctor_of,
  Polyfold.MPolyfold.IsScDiffeoOn.restrictTarget,
  Polyfold.MPolyfold.IsLocalScDiffeo.evenlyCovered_of_isProperMap,
  Polyfold.EpFunctor.IsProperCovering.isProperMap]

#rt_check RoundTrip.V11_38.B_to_isProperCovering_hFunctor' [Polyfold.ProperCoveringHom.mor_conj,
  Polyfold.ProperCoveringHom.hMor_src, Polyfold.ProperCoveringHom.hMor_tgt,
  Polyfold.ProperCoveringHom.surjective_hObj, Polyfold.ProperCoveringHom.isLocalScDiffeo_hObj,
  Polyfold.ProperCoveringHom.isScDiffeo_fibredMap_hFunctor,
  Polyfold.ProperCoveringHom.finite_fiber_hObj, Polyfold.ProperCoveringHom.isProperMap_hObj,
  Polyfold.ProperCoveringHom.isProperCovering_hFunctor_of,
  Polyfold.MPolyfold.IsScDiffeoOn.restrictTarget,
  Polyfold.MPolyfold.IsLocalScDiffeo.evenlyCovered_of_isProperMap,
  Polyfold.EpFunctor.IsProperCovering.isProperMap]

#rt_overlap RoundTrip.V11_38.A'_to_B [Polyfold.ProperCoveringHom.mor_conj,
  Polyfold.ProperCoveringHom.hMor_src, Polyfold.ProperCoveringHom.hMor_tgt,
  Polyfold.ProperCoveringHom.surjective_hObj, Polyfold.ProperCoveringHom.isLocalScDiffeo_hObj,
  Polyfold.ProperCoveringHom.isScDiffeo_fibredMap_hFunctor,
  Polyfold.ProperCoveringHom.finite_fiber_hObj, Polyfold.ProperCoveringHom.isProperMap_hObj,
  Polyfold.ProperCoveringHom.isProperCovering_hFunctor_of,
  Polyfold.MPolyfold.IsScDiffeoOn.restrictTarget,
  Polyfold.MPolyfold.IsLocalScDiffeo.evenlyCovered_of_isProperMap,
  Polyfold.EpFunctor.IsProperCovering.isProperMap]

end RoundTrip.V11_38
