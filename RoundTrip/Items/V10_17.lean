import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_17

/-! Round trip for V10_17 (2021 Definition 10.2.1, p. 477 (2017: Definition 10.3): the weak
fibred product `X ×_Y Z`).

The item is a definition: it lists the definitions `objRight`, `objSet`, `Obj`, `morRight`,
`morSet`, `Mor`, `conj`, `src`, `tgt`, `unit`, `inv`, `comp`, `groupoid` (vocabulary) and three
algebraic lemmas; `A` is the conjunction of the types of the lemmas, universes instantiated at
`0` (`B` lives in `Type`): `WeakFibredProduct.conj_comp_mor` (`(G(k) ∘ ϕ ∘ F(h)⁻¹) ∘ F(h) =
G(k) ∘ ϕ`), `conj_recover` (`G(k)⁻¹ ∘ (G(k) ∘ ϕ ∘ F(h)⁻¹) ∘ F(h) = ϕ`) and `src_eq_tgt_iff`
(the composable pairs).

`B` says that the project's definitions are the text's: objects and morphisms are exactly the
constrained triples, and the five structure maps are the listed ones.  Being a statement about
the project's definitions, `B` holds outright:

* `B_holds`: from the definitions (`Obj.ext`, `Mor.ext`, `Obj.src_φ`, …, `h_comp`, `φ_comp`,
  `k_comp`), plus the identity `G(k) ∘ ϕ ∘ F(h)⁻¹ = G(k) ∘ (ϕ ∘ F(h⁻¹))` (`F.mor_inv` and
  associativity in `Y`; the project brackets `conj` as `(G(k) ∘ ϕ) ∘ F(h)⁻¹`, the blind file as
  `G(k) ∘ (ϕ ∘ F(h⁻¹))`).  So `A_to_B` does not use `A` (flagged in the JSON): the check of the
  definitions is `B_holds` itself.
* `B_to_A`: `B` pins down `conj` (`conj_eq_conjB`: the middle entry of `t(h, ϕ, k)` is
  `G(k) ∘ ϕ ∘ F(h⁻¹)`); `conj_comp_mor` and `conj_recover` follow by groupoid algebra on `conjB`,
  and `src_eq_tgt_iff` from `B`'s entries of `s`, `t` and the extensionality of objects in `B`. -/

namespace RoundTrip.V10_17
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.WeakFibredProduct.conj_comp_mor.{0, 0, 0}) ∧
  (type_of% @Polyfold.WeakFibredProduct.conj_recover.{0, 0, 0}) ∧
  (type_of% @Polyfold.WeakFibredProduct.src_eq_tgt_iff.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.WeakFibredProduct.conj_comp_mor.{0, 0, 0},
    @Polyfold.WeakFibredProduct.conj_recover.{0, 0, 0},
    @Polyfold.WeakFibredProduct.src_eq_tgt_iff.{0, 0, 0}⟩

section
variable {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjZ MorZ : Type} [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
  [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
  {X : EpGroupoid ObjX MorX} {Y : EpGroupoid ObjY MorY} {Z : EpGroupoid ObjZ MorZ}

/-- The two bracketings of `G(k) ∘ ϕ ∘ F(h)⁻¹` agree on admissible triples. -/
theorem conj_eq_conjB_direct (F : EpFunctor X Y) (G : EpFunctor Z Y) {h : MorX} {φ : MorY}
    {k : MorZ} (h₁ : Y.src φ = F.obj (X.src h)) (h₂ : Y.tgt φ = G.obj (Z.src k)) :
    WeakFibredProduct.conj F G h φ k = conjB F G h φ k := by
  unfold WeakFibredProduct.conj conjB
  rw [F.mor_inv]
  refine Y.comp_assoc _ _ _ (by rw [G.src_mor, h₂]) ?_
  rw [Y.tgt_inv, F.src_mor, h₁]

/-- `B` holds for the project's definitions. -/
theorem isTextWFPB (F : EpFunctor X Y) (G : EpFunctor Z Y) : IsTextWFPB F G := by
  refine ⟨fun o => ⟨o.src_φ, o.tgt_φ⟩, fun o o' hx hφ hz => WeakFibredProduct.Obj.ext hx hφ hz,
    fun _ _ _ _ _ => ⟨rfl, rfl, rfl⟩, fun m => ⟨m.src_φ, m.tgt_φ⟩,
    fun m m' hh hφ hk => WeakFibredProduct.Mor.ext hh hφ hk, fun _ _ _ _ _ => ⟨rfl, rfl, rfl⟩,
    fun m => ⟨rfl, rfl, rfl⟩, fun m => ⟨rfl, conj_eq_conjB_direct F G m.src_φ m.tgt_φ, rfl⟩,
    fun o => ⟨rfl, rfl, rfl⟩, fun m => ⟨rfl, conj_eq_conjB_direct F G m.src_φ m.tgt_φ, rfl⟩,
    fun m' m hc => ⟨WeakFibredProduct.h_comp hc, WeakFibredProduct.φ_comp hc,
      WeakFibredProduct.k_comp hc⟩⟩

end

theorem B_holds : B := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F G =>
  isTextWFPB F G

/-- `A → B`: `B` holds outright (it is a statement about the project's definitions). -/
theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := by
  intro hB
  -- `B` pins down `conj`: the middle entry of `t(h, ϕ, k)`
  have hconj : ∀ (ObjX MorX ObjY MorY ObjZ MorZ : Type)
      [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
      [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
      [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
      [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
      [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
      [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
      (X : EpGroupoid ObjX MorX) (Y : EpGroupoid ObjY MorY) (Z : EpGroupoid ObjZ MorZ)
      (F : EpFunctor X Y) (G : EpFunctor Z Y) (h : MorX) (φ : MorY) (k : MorZ)
      (h₁ : Y.src φ = F.obj (X.src h)) (h₂ : Y.tgt φ = G.obj (Z.src k)),
      WeakFibredProduct.conj F G h φ k = conjB F G h φ k := by
    intro ObjX MorX ObjY MorY ObjZ MorZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X Y Z F G h φ k h₁ h₂
    exact (hB ObjX MorX ObjY MorY ObjZ MorZ X Y Z F G).2.2.2.2.2.2.2.1
      (WeakFibredProduct.Mor.mk F G h φ k h₁ h₂) |>.2.1
  -- `conjB ∘ F(h) = G(k) ∘ ϕ`
  have hcomp : ∀ (ObjX MorX ObjY MorY ObjZ MorZ : Type)
      [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
      [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
      [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
      [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
      [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
      [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
      (X : EpGroupoid ObjX MorX) (Y : EpGroupoid ObjY MorY) (Z : EpGroupoid ObjZ MorZ)
      (F : EpFunctor X Y) (G : EpFunctor Z Y) (h : MorX) (φ : MorY) (k : MorZ)
      (h₁ : Y.src φ = F.obj (X.src h)) (h₂ : Y.tgt φ = G.obj (Z.src k)),
      Y.comp (WeakFibredProduct.conj F G h φ k) (F.mor h) = Y.comp (G.mor k) φ := by
    intro ObjX MorX ObjY MorY ObjZ MorZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X Y Z F G h φ k h₁ h₂
    rw [hconj ObjX MorX ObjY MorY ObjZ MorZ X Y Z F G h φ k h₁ h₂, conjB]
    have e₁ : Y.src (G.mor k) = Y.tgt φ := by rw [G.src_mor, h₂]
    have e₂ : Y.src φ = Y.tgt (F.mor (X.inv h)) := by rw [F.tgt_mor, X.tgt_inv, h₁]
    have e₃ : Y.src (F.mor (X.inv h)) = Y.tgt (F.mor h) := by
      rw [F.src_mor, F.tgt_mor, X.src_inv]
    have e₄ : Y.src (Y.comp φ (F.mor (X.inv h))) = Y.tgt (F.mor h) := by
      rw [Y.src_comp _ _ e₂, e₃]
    rw [Y.comp_assoc _ _ _ (by rw [Y.tgt_comp _ _ e₂]; exact e₁) e₄,
      Y.comp_assoc _ _ _ e₂ e₃, ← F.mor_comp _ _ (by rw [X.src_inv]), X.inv_comp, F.mor_unit,
      GroupoidStr.comp_unit_of_eq (G := Y.toGroupoidStr) h₁]
  refine ⟨?_, ?_, ?_⟩
  · intro ObjX MorX _ _ _ _ _ _ ObjY MorY _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ X Y Z F G h φ k h₁ h₂
    exact hcomp ObjX MorX ObjY MorY ObjZ MorZ X Y Z F G h φ k h₁ h₂
  · intro ObjX MorX _ _ _ _ _ _ ObjY MorY _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ X Y Z F G h φ k h₁ h₂
    have e₁ : Y.src (G.mor k) = Y.tgt φ := by rw [G.src_mor, h₂]
    have hs : Y.src (WeakFibredProduct.conj F G h φ k) = Y.tgt (F.mor h) := by
      rw [hconj ObjX MorX ObjY MorY ObjZ MorZ X Y Z F G h φ k h₁ h₂, conjB,
        Y.src_comp _ _ (by rw [Y.tgt_comp _ _ (by rw [F.tgt_mor, X.tgt_inv, h₁])]; exact e₁),
        Y.src_comp _ _ (by rw [F.tgt_mor, X.tgt_inv, h₁]), F.src_mor, X.src_inv, F.tgt_mor]
    have ht : Y.src (Y.inv (G.mor k)) = Y.tgt (WeakFibredProduct.conj F G h φ k) := by
      have := congrArg Y.tgt (hcomp ObjX MorX ObjY MorY ObjZ MorZ X Y Z F G h φ k h₁ h₂)
      rw [Y.tgt_comp _ _ hs, Y.tgt_comp _ _ e₁] at this
      rw [Y.src_inv, this]
    rw [Y.comp_assoc _ _ _ ht hs, hcomp ObjX MorX ObjY MorY ObjZ MorZ X Y Z F G h φ k h₁ h₂,
      GroupoidStr.inv_comp_cancel_left e₁]
  · intro ObjX MorX _ _ _ _ _ _ ObjY MorY _ _ _ _ _ _ ObjZ MorZ _ _ _ _ _ _ X Y Z F G m m'
    obtain ⟨-, hext, -, -, -, -, hsrc, htgt, -, -, -⟩ :=
      hB ObjX MorX ObjY MorY ObjZ MorZ X Y Z F G
    have hc := hconj ObjX MorX ObjY MorY ObjZ MorZ X Y Z F G m'.h m'.φ m'.k m'.src_φ m'.tgt_φ
    obtain ⟨hsx, hsφ, hsz⟩ := hsrc m
    obtain ⟨htx, htφ, htz⟩ := htgt m'
    -- `(groupoid F G).src = src`, `(groupoid F G).tgt = tgt` (the fields of `groupoid`)
    change (WeakFibredProduct.src m).x = _ at hsx
    change (WeakFibredProduct.src m).φ = _ at hsφ
    change (WeakFibredProduct.src m).z = _ at hsz
    change (WeakFibredProduct.tgt m').x = _ at htx
    change (WeakFibredProduct.tgt m').φ = _ at htφ
    change (WeakFibredProduct.tgt m').z = _ at htz
    constructor
    · intro he
      refine ⟨?_, ?_, ?_⟩
      · rw [← hsx, he, htx]
      · rw [← hsφ, he, htφ, hc]
      · rw [← hsz, he, htz]
    · rintro ⟨hx, hφ, hz⟩
      refine hext _ _ ?_ ?_ ?_
      · rw [hsx, htx, hx]
      · rw [hsφ, htφ, hφ, hc]
      · rw [hsz, htz, hz]

/-! ### Harness checks

`B` mentions the item's vocabulary definition `WeakFibredProduct.groupoid`, whose body gives the
groupoid laws by the project theorems `tgt_comp` (through `conj_comp`, which uses the banned
`conj_comp_mor`), `tgt_inv` (through `conj_inv`, which uses the banned `conj_recover`) and
`src_comp`, `comp_assoc` (which use the banned `src_eq_tgt_iff`); these are direct references, not
abstracted `_proof_N` fields.  So every term mentioning `B` reaches the three banned theorems, and
plain `#rt_check` and `#rt_check_soft` fail on both directions (recorded below with
`#guard_msgs`).  Moreover `h_comp`, `φ_comp`, `k_comp` (used in `B_holds`) unfold `compOf`, whose
abstracted proof fields `compOf._proof_1/2` use `src_eq_tgt_iff`.

`#rt_check_except_defs` is the harness traversal `rtCollectSoft` (proof fields `D._proof_N` of
definitions are soft) with the body of the vocabulary definition `WeakFibredProduct.groupoid` not
unfolded: it shows that our proofs reach the banned theorems only through that definition and
through the abstracted proof fields of definitions. -/

open Lean Elab Command in
/-- `#rt_check_except_defs T [nᵢ]`: the proof of `T` reaches the banned `nᵢ` only through the
body of `WeakFibredProduct.groupoid` and through abstracted proof fields of definitions. -/
elab "#rt_check_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let (hard, soft) := rtCollectSoft env (roots.toList.map (·, true))
    (NameSet.empty.insert ``Polyfold.WeakFibredProduct.groupoid) {}
  if hard.contains ``sorryAx || soft.contains ``sorryAx then
    throwError "FAIL: {t.getId} contains sorry"
  let banned := bs.getElems.toList.map (·.getId)
  let badHard := banned.filter hard.contains
  unless badHard.isEmpty do
    throwError "FAIL: {t.getId} uses {badHard} outside `groupoid` and the proof fields"
  let badSoft := banned.filter fun b => soft.contains b
  logInfo m!"OK: {t.getId} reaches the banned theorems only through `groupoid` and the proof fields of definitions (soft: {badSoft})"

/--
error: rt_check FAIL: RoundTrip.V10_17.A_to_B uses [Polyfold.WeakFibredProduct.conj_comp_mor,
 Polyfold.WeakFibredProduct.conj_recover,
 Polyfold.WeakFibredProduct.src_eq_tgt_iff]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_17.A_to_B [Polyfold.WeakFibredProduct.conj_comp_mor,
  Polyfold.WeakFibredProduct.conj_recover, Polyfold.WeakFibredProduct.src_eq_tgt_iff]

/--
error: rt_check FAIL: RoundTrip.V10_17.B_to_A uses [Polyfold.WeakFibredProduct.conj_comp_mor,
 Polyfold.WeakFibredProduct.conj_recover,
 Polyfold.WeakFibredProduct.src_eq_tgt_iff]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_17.B_to_A [Polyfold.WeakFibredProduct.conj_comp_mor,
  Polyfold.WeakFibredProduct.conj_recover, Polyfold.WeakFibredProduct.src_eq_tgt_iff]

#rt_check_except_defs RoundTrip.V10_17.A_to_B [Polyfold.WeakFibredProduct.conj_comp_mor,
  Polyfold.WeakFibredProduct.conj_recover, Polyfold.WeakFibredProduct.src_eq_tgt_iff]
#rt_check_except_defs RoundTrip.V10_17.B_to_A [Polyfold.WeakFibredProduct.conj_comp_mor,
  Polyfold.WeakFibredProduct.conj_recover, Polyfold.WeakFibredProduct.src_eq_tgt_iff]
#rt_overlap RoundTrip.V10_17.B_to_A [Polyfold.WeakFibredProduct.conj_comp_mor,
  Polyfold.WeakFibredProduct.conj_recover, Polyfold.WeakFibredProduct.src_eq_tgt_iff]

end RoundTrip.V10_17
