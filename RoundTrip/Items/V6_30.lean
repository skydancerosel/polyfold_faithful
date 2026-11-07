import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_30

/-! Round trip for V6_30 (Proposition 6.26, `DET` over a convex set of Fredholm operators).

A = `proposition_6_26` (universes at `0`): for a **nonempty** convex set `C` of Fredholm operators
`E → F`, `DetOn C` is a vector bundle with fibre `ℝ` and has exactly two orientations.
B = for every chart point `p` of a smooth `x` and every sc-Fredholm `f`: `Lin(f, x)` is convex and
contractible, `DET(f, x)` is a vector bundle and has `Nat.card = 2` orientations — with no
hypothesis making `Lin(f, x)` nonempty.

* `A ⇒ B` fails: A's hypothesis `C.Nonempty` is not given by B.  `B_imp_nonemptyLin` shows that
  B itself forces `Lin(f, x) ≠ ∅` everywhere (contractible spaces are nonempty), and
  `A_imp_B_iff_nonemptyLin` that, given A, B is *equivalent* to `NonemptyLin` (every `Lin(f, x)`
  at a smooth point is nonempty).  `NonemptyLin` holds under the project's
  `Bd.HasScPlusSectionsThrough` (`linSet_nonempty`; true with sc-smooth bump functions), so the
  missing hypothesis is satisfiable, and `A_to_Bsec` proves B under it; without sections through
  `−f(x)` (no bump functions) it is open, and B may be false.
* `B ⇒ A` fails: A is about an arbitrary nonempty convex set of Fredholm operators between
  arbitrary Banach spaces; B only about the sets `Lin(f, x) = L₀ + {sc⁺-operators}`.  An arbitrary
  `C` is not such a set, so A would have to be re-proved (contractible base ⇒ two orientations).
-/

namespace RoundTrip.V6_30
open Polyfold

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.proposition_6_26.{0, 0}

theorem A_holds : A := @Polyfold.proposition_6_26.{0, 0}

/-- Every `Lin(f, x)` at a smooth point, read in every chart point, is nonempty. -/
def NonemptyLin : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (_ : Bd.IsScFredholmSection f) (x : X),
    x ∈ PX.smoothSet → ∀ p : ChartPoint Bd x, (p.linSet f).Nonempty

/-- B with the project's hypothesis `Bd.HasScPlusSectionsThrough` added. -/
def Bsec : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P), Bd.HasScPlusSectionsThrough →
    ∀ (f : X → Y) (hf : Bd.IsScFredholmSection f) (x : X),
    x ∈ PX.smoothSet → ∀ p : ChartPoint Bd x,
      Convex ℝ (p.linSet f) ∧ ContractibleSpace ↥(p.linSet f) ∧
      VectorBundle ℝ ℝ (ChartPoint.detLin f p hf) ∧
      Nat.card (LineOrientation (ChartPoint.detLin f p hf)) = 2

/-- `Nat.card = 2` from "two different elements, and every element is one of them". -/
theorem natCard_eq_two {α : Type*} {o₁ o₂ : α} (h : o₁ ≠ o₂) (h' : ∀ o, o = o₁ ∨ o = o₂) :
    Nat.card α = 2 :=
  Nat.card_eq_two_iff.2 ⟨o₁, o₂, h, Set.eq_univ_of_forall fun o => by
    rcases h' o with rfl | rfl
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl⟩

/-- The conclusion of B at one chart point, from A and `Lin(f, x) ≠ ∅`. -/
theorem conclusion_of_A (hA : A) {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {Bd : StrongBundle PX P} {f : X → Y} (hf : Bd.IsScFredholmSection f) {x : X}
    (p : ChartPoint Bd x) (hne : (p.linSet f).Nonempty) :
    Convex ℝ (p.linSet f) ∧ ContractibleSpace ↥(p.linSet f) ∧
      VectorBundle ℝ ℝ (ChartPoint.detLin f p hf) ∧
      Nat.card (LineOrientation (ChartPoint.detLin f p hf)) = 2 := by
  have hconv := p.convex_linSet hf
  obtain ⟨hvb, o₁, o₂, h12, hall⟩ := hA hconv hne (p.isFredholm_of_mem_linSet hf)
  exact ⟨hconv, hconv.contractibleSpace hne, hvb, natCard_eq_two h12 hall⟩

/-- B forces every `Lin(f, x)` to be nonempty (a contractible space is nonempty). -/
theorem B_imp_nonemptyLin : B → NonemptyLin := by
  intro hB X _ _ _ PX Y _ _ _ P _ _ Bd f hf x hx p
  obtain ⟨-, hc, -, -⟩ := hB PX P Bd f hf x hx p
  obtain ⟨L⟩ := (inferInstance : PathConnectedSpace ↥(p.linSet f)).nonempty
  exact ⟨L.1, L.2⟩

/-- **Given A, B is equivalent to the nonemptiness of all `Lin(f, x)`.** -/
theorem A_imp_B_iff_nonemptyLin (hA : A) : B ↔ NonemptyLin := by
  refine ⟨B_imp_nonemptyLin, fun hN => ?_⟩
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f hf x hx p
  exact conclusion_of_A hA hf p (hN PX P Bd f hf x hx p)

/-- `A ⇒ B` under the project's hypothesis that there are sc⁺-sections through all smooth
fibre points (the missing hypothesis is satisfiable). -/
theorem A_to_Bsec : A → Bsec := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd hsec f hf x hx p
  exact conclusion_of_A hA hf p (p.linSet_nonempty hf hx hsec)

/-! `A_to_B` is not proved: B has no hypothesis giving `Lin(f, x) ≠ ∅` (A's `hne`), and by
`A_imp_B_iff_nonemptyLin` it is exactly this nonemptiness that is missing.
`B_to_A` is not proved: B speaks only about the sets `Lin(f, x)`. -/

#rt_check RoundTrip.V6_30.A_to_Bsec [Polyfold.proposition_6_26]
#rt_check RoundTrip.V6_30.B_imp_nonemptyLin [Polyfold.proposition_6_26]

end RoundTrip.V6_30
