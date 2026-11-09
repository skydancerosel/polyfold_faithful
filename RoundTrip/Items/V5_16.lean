import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_16

/-!
Round trip for V5_16 (Definitions 5.9 and 5.29, sc-smooth bump functions).  Refreshed 2026-11-02:
the comparison row now also cites the weak-versus-pointwise lemmas of `BumpWeakPointwise.lean` and
`admitsBumpFunctions_of_hilbert`.

A = `AdmitsBumpFunctions.weak` ∧ `admitsBumpFunctionsWeak_of_dense` ∧
`AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth` ∧ `admitsBumpFunctions_of_hilbert` (universes at
`0`); `AdmitsBumpFunctions`, `AdmitsBumpFunctionsWeak`, `HasBumpAt` are vocabulary.

* The definitions agree with B's notions by `Iff.rfl` (`weak_iff_B`, `pointwise_iff_B`); the new
  `HasBumpAt PX x` is B's pointwise reading at the single point `x`.
* `A ⇒ B` (proved, vacuous): B is a definitional identity.
* `B ⇒ A` (not proved any more): B gives `AdmitsBumpFunctions.weak` and
  `admitsBumpFunctionsWeak_of_dense` (`B_gives_weak`, `B_gives_weak_of_dense`; elementary).  It
  says nothing about bump functions on sc-Banach spaces at smooth points (the translation argument
  of `hasBumpAt_of_mem_smooth`, which would have to be re-proved) nor about sc-Hilbert spaces
  (`admitsBumpFunctions_of_hilbert` is Proposition 5.35 in the charts plus Theorem 5.34:
  `of_hilbert_from_5_34`, without B).
-/

namespace RoundTrip.V5_16
open Polyfold

/-- The project's statement, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.MPolyfold.AdmitsBumpFunctions.weak.{0} ∧
  type_of% @Polyfold.MPolyfold.admitsBumpFunctionsWeak_of_dense.{0} ∧
  type_of% @Polyfold.MPolyfold.AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth ∧
  type_of% @Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert.{0}

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.AdmitsBumpFunctions.weak.{0},
    @Polyfold.MPolyfold.admitsBumpFunctionsWeak_of_dense.{0},
    @Polyfold.MPolyfold.AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth,
    @Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert.{0}⟩

/-- The definitions agree: the project's `AdmitsBumpFunctionsWeak` is B's `AdmitsBumpB`
(definitionally: same quantifiers, `f ≠ 0` as functions, `tsupport f ⊆ U`). -/
theorem weak_iff_B {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) : PX.AdmitsBumpFunctionsWeak ↔ AdmitsBumpB PX := Iff.rfl

/-- The project's (pointwise) `AdmitsBumpFunctions` is B's `AdmitsBumpPointB`, definitionally. -/
theorem pointwise_iff_B {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) : PX.AdmitsBumpFunctions ↔ AdmitsBumpPointB PX := Iff.rfl

/-- The new vocabulary `HasBumpAt` is B's pointwise reading at one point. -/
theorem pointwise_iff_forall_hasBumpAt {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] (PX : MPolyfold X) : AdmitsBumpPointB PX ↔ ∀ x, PX.HasBumpAt x := Iff.rfl

/-- The intended comparison `BPointwise` (not the item) holds as well. -/
theorem BPointwise_holds : BPointwise := fun _ _ _ _ PX => pointwise_iff_B PX

/-- `A ⇒ B`: B is a definitional identity; proved outright (the hypothesis is not used). -/
theorem A_to_B : A → B := fun _ _ _ _ _ PX => weak_iff_B PX

/-- B gives A's first conjunct: rewrite the target with B and weaken the pointwise bump `f(x) ≠ 0`
to `f ≠ 0` (elementary; the hypothesis carries no content). -/
theorem B_gives_weak (hB : B) : type_of% @Polyfold.MPolyfold.AdmitsBumpFunctions.weak.{0} := by
  intro X _ _ _ PX h
  rw [hB X PX]
  intro x U hU hx
  obtain ⟨f, hf, hfx, hsupp⟩ := h x U hU hx
  exact ⟨f, hf, fun h0 => hfx (congrFun h0 x), hsupp⟩

/-- B gives A's second conjunct: a bump at a bump point `y ∈ U` is not identically zero
(elementary). -/
theorem B_gives_weak_of_dense (hB : B) :
    type_of% @Polyfold.MPolyfold.admitsBumpFunctionsWeak_of_dense.{0} := by
  intro X _ _ _ PX h
  rw [hB X PX]
  intro x U hU hx
  obtain ⟨y, hy, hyU⟩ := h.exists_mem_open hU ⟨x, hx⟩
  obtain ⟨f, hf, hfy, hsupp⟩ := hy U hU hyU
  exact ⟨f, hf, fun h0 => hfy (congrFun h0 y), hsupp⟩

/-- A's fourth conjunct is Proposition 5.35 in the charts plus Theorem 5.34 (other items'
theorems); proved WITHOUT B, to locate where its content lies. -/
theorem of_hilbert_from_5_34 : type_of% @Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert.{0} := by
  intro X _ _ _ PX h
  refine theorem_5_5_7.2 ⟨{φ | PX.IsChart φ ∧ ∃ b : φ.model.E 0 →L[ℝ] φ.model.E 0 →L[ℝ] ℝ,
    ∀ v, ‖v‖ ^ 2 = b v v}, fun φ hφ => hφ.1, fun x => ?_, fun φ hφ => proposition_5_5_8 _ hφ.2⟩
  obtain ⟨φ, hφ, hx, hb⟩ := h x
  exact ⟨φ, ⟨hφ, hb⟩, hx⟩

#rt_check RoundTrip.V5_16.A_to_B [Polyfold.MPolyfold.AdmitsBumpFunctions.weak,
  Polyfold.MPolyfold.admitsBumpFunctionsWeak_of_dense,
  Polyfold.MPolyfold.AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth,
  Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert]
#rt_check RoundTrip.V5_16.B_gives_weak [Polyfold.MPolyfold.AdmitsBumpFunctions.weak,
  Polyfold.MPolyfold.admitsBumpFunctionsWeak_of_dense,
  Polyfold.MPolyfold.AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth,
  Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert]
#rt_check RoundTrip.V5_16.B_gives_weak_of_dense [Polyfold.MPolyfold.AdmitsBumpFunctions.weak,
  Polyfold.MPolyfold.admitsBumpFunctionsWeak_of_dense,
  Polyfold.MPolyfold.AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth,
  Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert]
#rt_check RoundTrip.V5_16.of_hilbert_from_5_34 [Polyfold.MPolyfold.AdmitsBumpFunctions.weak,
  Polyfold.MPolyfold.admitsBumpFunctionsWeak_of_dense,
  Polyfold.MPolyfold.AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth,
  Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert]
#rt_overlap RoundTrip.V5_16.of_hilbert_from_5_34 [Polyfold.MPolyfold.AdmitsBumpFunctions.weak,
  Polyfold.MPolyfold.admitsBumpFunctionsWeak_of_dense,
  Polyfold.MPolyfold.AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth,
  Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert]

end RoundTrip.V5_16
