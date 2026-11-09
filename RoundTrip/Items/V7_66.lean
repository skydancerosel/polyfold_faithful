import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_66

/-!
Round trip for V7_66 (Lemma 7.10: invariant sc-smooth majorants).

`A` is the type of `Polyfold.EpGroupoid.lemma_7_6_5` at universe `0`: for a natural representation
`R : X.NaturalRep x` (Theorem 7.1's data on an open **connected** `R.U ∋ x`), an open `U` with
`cl U ⊆ R.U`, invariant under every `R.Φ g` (**`x ∈ U` is not assumed**), and a continuous
`β : X → [0, 1]` with `tsupport β ⊆ U`, invariant on `R.U`, there is an sc-smooth `f ≥ 0`,
invariant on `R.U`, with `β ≤ f`, `tsupport f ⊆ R.U` **and `tsupport f ⊆ cl U`**.

`B` takes the natural action as given data `(Φ, Γ)` on `V(x)` with the clauses of Theorem 7.1
(`IsNatActionB`), **without connectedness of `V(x)`**, assumes `x ∈ U(x)`, and concludes
`tsupport f ⊆ V(x)` only.

* `A → B` is proved only for connected `V(x)` (`A_to_B_of_isConnected`): then B's data is a
  project `NaturalRep` (`Φ(1) = id` and `Φ(g)⁻¹ = Φ(g⁻¹)` follow from `Φ_mul` and the bijectivity
  of `Φ(1)`), and A applies.  For disconnected `V(x)` the project's `NaturalRep` does not exist,
  so A says nothing; B is still true (the averaging proof of the lemma uses only `Φ_mul` and the
  sc-smoothness of the `Φ(g)`), but proving it would mean re-proving Lemma 7.10.
* `B → A` is not proved: A's extra conclusion `tsupport f ⊆ cl U` and its dropped hypothesis
  `x ∈ U` are not provided by B (B applies only to `U ∋ x` and bounds the support by `V(x)` only;
  for `x ∈ cl U ∖ U` B cannot be applied to any `U' ⊇ supp β` with support control inside
  `cl U`).
-/

namespace RoundTrip.V7_66
open Polyfold Set

/-- The project's Lemma 7.10, universes at `0`. -/
def A : Prop := type_of% @Polyfold.EpGroupoid.lemma_7_6_5.{0}

theorem A_holds : A := @Polyfold.EpGroupoid.lemma_7_6_5.{0}

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `Φ(1) = id` on `V` for B's natural action. -/
theorem Φ_one_of {X : EpGroupoid Obj Mor} {x : Obj} {V : Set Obj} {Φ : X.Isotropy x → Obj → Obj}
    {Γ : X.Isotropy x → Obj → Mor} (h : IsNatActionB X x V Φ Γ) {y : Obj} (hy : y ∈ V) :
    Φ 1 y = y := by
  obtain ⟨-, -, hd, hmul, -⟩ := h
  obtain ⟨ψ, hψ⟩ := hd 1
  have hz : ψ y ∈ V := hψ.mapsTo_inv hy
  have h1 : Φ 1 (ψ y) = y := hψ.right_inv y hy
  calc Φ 1 y = Φ 1 (Φ 1 (ψ y)) := by rw [h1]
    _ = Φ (1 * 1) (ψ y) := (hmul 1 1 _ hz).symm
    _ = y := by rw [mul_one, h1]

/-- B's natural action on a **connected** `V` is a project `NaturalRep`. -/
def toNaturalRep {X : EpGroupoid Obj Mor} {x : Obj} {V : Set Obj}
    {Φ : X.Isotropy x → Obj → Obj} {Γ : X.Isotropy x → Obj → Mor} (h : IsNatActionB X x V Φ Γ)
    (hc : IsConnected V) : X.NaturalRep x where
  U := V
  isOpen_U := h.1
  isConnected_U := hc
  mem_U := h.2.1
  Φ := Φ
  Γ := Γ
  isScDiffeoOn_Φ g :=
    { isScSmoothOn := (h.2.2.1 g).choose_spec.isScSmoothOn
      isScSmoothOn_inv := (h.2.2.1 g⁻¹).choose_spec.isScSmoothOn
      mapsTo := (h.2.2.1 g).choose_spec.mapsTo
      mapsTo_inv := (h.2.2.1 g⁻¹).choose_spec.mapsTo
      left_inv := fun y hy => by
        rw [← h.2.2.2.1 g⁻¹ g y hy, inv_mul_cancel, Φ_one_of h hy]
      right_inv := fun y hy => by
        rw [← h.2.2.2.1 g g⁻¹ y hy, mul_inv_cancel, Φ_one_of h hy] }
  Φ_mul := h.2.2.2.1
  isScSmoothOn_Γ := h.2.2.2.2.1
  Γ_self := h.2.2.2.2.2.1
  src_Γ g y hy := (h.2.2.2.2.2.2.1 g y hy).1
  tgt_Γ g y hy := (h.2.2.2.2.2.2.1 g y hy).2
  existsUnique_Γ := h.2.2.2.2.2.2.2

end

/-- `B` with the extra hypothesis that `V(x)` is connected. -/
def B_conn : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ParacompactSpace X.OrbitSpace → X.PObj.AdmitsScPartitionsOfUnity →
    ∀ (x : Obj) (U V : Set Obj), IsOpen U → x ∈ U → IsOpen V → x ∈ V → IsConnected V →
      U ⊆ closure U → closure U ⊆ V →
      ∀ (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor),
        IsNatActionB X x V Φ Γ → (∀ g, Set.MapsTo (Φ g) U U) →
        ∀ β : Obj → ℝ, Continuous β → (∀ y, β y ∈ Set.Icc (0 : ℝ) 1) → tsupport β ⊆ U →
          (∀ g, ∀ y ∈ V, β (Φ g y) = β y) →
          ∃ f : Obj → ℝ, X.PObj.IsScSmoothMap realPolyfold f ∧ (∀ y, 0 ≤ f y) ∧
            tsupport f ⊆ V ∧ (∀ g, ∀ y ∈ V, f (Φ g y) = f y) ∧ ∀ y, β y ≤ f y

/-- **`A → B` for connected `V(x)`** (the only case the project's `NaturalRep` covers). -/
theorem A_to_B_of_isConnected : A → B_conn := by
  intro hA Obj Mor _ _ _ _ _ _ X hpara hpu x U V hUo _ _ _ hVc _ hUV Φ Γ hN hUinv β hβc hβ01
    hβU hβinv
  obtain ⟨f, hf, hf0, -, hfR, hfinv, hβf⟩ :=
    hA hpara hpu (toNaturalRep hN hVc) hUo hUV hUinv hβc hβ01 hβU hβinv
  exact ⟨f, hf, hf0, hfR, hfinv, hβf⟩

#rt_check RoundTrip.V7_66.A_to_B_of_isConnected [Polyfold.EpGroupoid.lemma_7_6_5]
#rt_overlap RoundTrip.V7_66.A_to_B_of_isConnected [Polyfold.EpGroupoid.lemma_7_6_5]

end RoundTrip.V7_66
