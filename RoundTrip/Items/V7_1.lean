import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_1

/-! Round trip for V7_1 (Definition 7.1: groupoids, `mor(x, y)` and the orbit space `|X|`).

The listed declarations are mostly definitions (`GroupoidStr`, `mor`, `morOn`, `Isomorphic`,
`orbitSetoid`, `OrbitSpace`, `π`, `saturation`, `IsSaturated`, `Ob`, `instGroupoid`); the three
listed theorems are `GroupoidStr.π_eq_π_iff`, `GroupoidStr.isSaturated_iff` and
`GroupoidStr.orbitSetoid_eq`, so `A` is the conjunction of their types, universes at `0`.

`B` characterizes the project's definitions: `GroupoidStr` is exactly the text's groupoid with
`m` on the fibred product (a), (b); `mor`, `Isomorphic` are the text's (c), (d); `|X|` is the set
of classes `|x|` with `π x = |x|` (e).
* `A → B`: (a)–(d) are glue (the total `comp` of `GroupoidStr` restricted to composable pairs;
  conversely `m` extended by a junk value).  (e) uses the hypothesis `π x = π y ↔ x ∼ y`
  (conjunct 1 of `A`) for the injectivity of `|X| → {|x|}`.
* `B → A`: `π_eq_π_iff` follows from (d), (e) (`π x = π y ↔ |x| = |y| ↔ x ∼ y`);
  `isSaturated_iff` from that; `orbitSetoid_eq` (the bridge to Mathlib's
  `CategoryTheory.isIsomorphicSetoid`) is not about anything in `B` and is re-proved outright. -/

namespace RoundTrip.V7_1
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GroupoidStr.π_eq_π_iff.{0}) ∧
  (type_of% @Polyfold.GroupoidStr.isSaturated_iff.{0}) ∧
  (type_of% @Polyfold.GroupoidStr.orbitSetoid_eq.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidStr.π_eq_π_iff.{0}, @Polyfold.GroupoidStr.isSaturated_iff.{0},
    @Polyfold.GroupoidStr.orbitSetoid_eq.{0}⟩

/-! ### Glue -/

section Glue
variable {Obj Mor : Type}

theorem isGroupoidB_of (G : GroupoidStr Obj Mor) :
    IsGroupoidB G.src G.tgt (fun p => G.comp p.1.1 p.1.2) G.unit G.inv := by
  refine ⟨fun p => ⟨G.src_comp _ _ p.2, G.tgt_comp _ _ p.2⟩, ?_, fun x => ⟨G.src_unit x,
    G.tgt_unit x⟩, ?_, ?_, fun φ => ⟨G.src_inv φ, G.tgt_inv φ⟩, fun φ _ => G.comp_inv φ,
    fun φ _ => G.inv_comp φ⟩
  · intro φ ψ χ h₁ h₂ _ _
    exact G.comp_assoc φ ψ χ h₁ h₂
  · intro x φ _ hx
    subst hx
    exact G.comp_unit φ
  · intro x ψ _ hx
    subst hx
    exact G.unit_comp ψ

open Classical in
/-- From a text groupoid, a `GroupoidStr` (with `m` extended by a junk value off `𝐗 ₛ×ₜ 𝐗`). -/
noncomputable def ofB (s t : Mor → Obj) (m : ComposableB s t → Mor) (u : Obj → Mor)
    (ι : Mor → Mor) (h : IsGroupoidB s t m u ι) : GroupoidStr Obj Mor where
  src := s
  tgt := t
  comp φ ψ := if hc : s φ = t ψ then m ⟨(φ, ψ), hc⟩ else φ
  unit := u
  inv := ι
  src_comp φ ψ hc := by simp only [dif_pos hc]; exact (h.1 ⟨(φ, ψ), hc⟩).1
  tgt_comp φ ψ hc := by simp only [dif_pos hc]; exact (h.1 ⟨(φ, ψ), hc⟩).2
  comp_assoc φ ψ χ h₁ h₂ := by
    have h₃ : s (m ⟨(φ, ψ), h₁⟩) = t χ := (h.1 ⟨(φ, ψ), h₁⟩).1.trans h₂
    have h₄ : s φ = t (m ⟨(ψ, χ), h₂⟩) := h₁.trans (h.1 ⟨(ψ, χ), h₂⟩).2.symm
    simp only [dif_pos h₁, dif_pos h₂, dif_pos h₃, dif_pos h₄]
    exact h.2.1 φ ψ χ h₁ h₂ h₃ h₄
  src_unit x := (h.2.2.1 x).1
  tgt_unit x := (h.2.2.1 x).2
  comp_unit φ := by
    have hc : s φ = t (u (s φ)) := ((h.2.2.1 (s φ)).2).symm
    simp only [dif_pos hc]
    exact h.2.2.2.1 (s φ) φ hc rfl
  unit_comp φ := by
    have hc : s (u (t φ)) = t φ := (h.2.2.1 (t φ)).1
    simp only [dif_pos hc]
    exact h.2.2.2.2.1 (t φ) φ hc rfl
  src_inv φ := (h.2.2.2.2.2.1 φ).1
  tgt_inv φ := (h.2.2.2.2.2.1 φ).2
  comp_inv φ := by
    have hc : s φ = t (ι φ) := ((h.2.2.2.2.2.1 φ).2).symm
    simp only [dif_pos hc]
    exact h.2.2.2.2.2.2.1 φ hc
  inv_comp φ := by
    have hc : s (ι φ) = t φ := (h.2.2.2.2.2.1 φ).1
    simp only [dif_pos hc]
    exact h.2.2.2.2.2.2.2 φ hc

theorem relB_equivalence (G : GroupoidStr Obj Mor) : Equivalence (relB G) := by
  refine ⟨fun x => ⟨G.unit x, G.src_unit x, G.tgt_unit x⟩, ?_, ?_⟩
  · rintro x y ⟨φ, rfl, rfl⟩
    exact ⟨G.inv φ, G.src_inv φ, G.tgt_inv φ⟩
  · rintro x y z ⟨φ, rfl, rfl⟩ ⟨ψ, hψ, rfl⟩
    exact ⟨G.comp ψ φ, G.src_comp _ _ hψ, G.tgt_comp _ _ hψ⟩

theorem classB_eq_iff (G : GroupoidStr Obj Mor) (x y : Obj) :
    classB G x = classB G y ↔ relB G x y := by
  have he := relB_equivalence G
  constructor
  · intro h
    have hx : x ∈ classB G x := he.refl x
    rw [h] at hx
    exact hx
  · intro h
    ext z
    exact ⟨fun hz => he.trans hz h, fun hz => he.trans hz (he.symm h)⟩

/-- The map `|X| → {|x|}`, `π x ↦ |x|`. -/
def toClass (G : GroupoidStr Obj Mor) : G.OrbitSpace → {S : Set Obj // ∃ x, S = classB G x} :=
  Quotient.lift (fun x => ⟨classB G x, x, rfl⟩) fun x y (hxy : G.Isomorphic x y) =>
    Subtype.ext ((classB_eq_iff G x y).2 hxy)

end Glue

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA
  refine ⟨fun Obj Mor G => isGroupoidB_of G, ?_, fun _ _ _ _ _ => rfl, ?_, ?_⟩
  · intro Obj Mor s t m u ι h
    exact ⟨ofB s t m u ι h, rfl, rfl, rfl, rfl, fun p => dif_pos p.2⟩
  · intro Obj Mor G
    exact ⟨relB_equivalence G, fun _ _ => Iff.rfl⟩
  · intro Obj Mor G
    have hbij : Function.Bijective (toClass G) := by
      constructor
      · intro a b hab
        induction a using Quotient.inductionOn with | h x => ?_
        induction b using Quotient.inductionOn with | h y => ?_
        have h1 : classB G x = classB G y := congrArg Subtype.val hab
        exact (hA.1 G).2 ((classB_eq_iff G x y).1 h1)
      · rintro ⟨S, x, rfl⟩
        exact ⟨G.π x, rfl⟩
    exact ⟨Equiv.ofBijective _ hbij, fun x => rfl⟩

/-! ### `B → A` -/

theorem B_to_A : B → A := by
  intro hB
  -- `π x = π y ↔ x ∼ y`, from (d) and (e)
  have hπ : ∀ (Obj Mor : Type) (G : GroupoidStr Obj Mor) (x y : Obj),
      G.π x = G.π y ↔ G.Isomorphic x y := by
    intro Obj Mor G x y
    obtain ⟨e, he⟩ := hB.2.2.2.2 Obj Mor G
    have hiso := (hB.2.2.2.1 Obj Mor G).2 x y
    rw [hiso, ← classB_eq_iff G x y, ← he x, ← he y]
    constructor
    · intro h; rw [h]
    · intro h; exact e.injective (Subtype.ext h)
  refine ⟨fun {Obj Mor} G x y => hπ Obj Mor G x y, ?_, ?_⟩
  · intro Obj Mor G A
    constructor
    · intro h φ hφ
      rw [← h]
      exact ⟨G.src φ, hφ, (hπ Obj Mor G _ _).2 ⟨φ, rfl, rfl⟩⟩
    · intro h
      refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
      rintro y ⟨a, ha, hay⟩
      obtain ⟨φ, rfl, rfl⟩ := (hπ Obj Mor G _ _).1 hay
      exact h φ ha
  · intro Obj Mor G
    refine Setoid.ext fun x y => ⟨?_, ?_⟩
    · rintro ⟨φ, hx, hy⟩
      exact ⟨(CategoryTheory.Groupoid.isoEquivHom (G.toOb x) (G.toOb y)).symm
        (G.homMk φ hx hy)⟩
    · rintro ⟨i⟩
      exact ⟨i.hom.1, i.hom.2.1, i.hom.2.2⟩

#rt_check RoundTrip.V7_1.A_to_B [Polyfold.GroupoidStr.π_eq_π_iff, Polyfold.GroupoidStr.isSaturated_iff, Polyfold.GroupoidStr.orbitSetoid_eq]
#rt_check RoundTrip.V7_1.B_to_A [Polyfold.GroupoidStr.π_eq_π_iff, Polyfold.GroupoidStr.isSaturated_iff, Polyfold.GroupoidStr.orbitSetoid_eq]
#rt_overlap RoundTrip.V7_1.B_to_A [Polyfold.GroupoidStr.π_eq_π_iff, Polyfold.GroupoidStr.isSaturated_iff, Polyfold.GroupoidStr.orbitSetoid_eq]
#rt_overlap RoundTrip.V7_1.A_to_B [Polyfold.GroupoidStr.π_eq_π_iff, Polyfold.GroupoidStr.isSaturated_iff, Polyfold.GroupoidStr.orbitSetoid_eq]

end RoundTrip.V7_1
