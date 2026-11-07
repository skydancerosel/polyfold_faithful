import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_67

/-!
Round trip for V7_67 (the proof of Theorem 7.4).

`A` is the conjunction of the types, universes at `0`, of the listed theorems (`orbitExtension`
is a definition, vocabulary): `exists_invariant_nhds_of_isOpen` (properties (1)–(3): a natural
representation `R` on `W(x) = R.U ⊆ W` and an invariant open `V(x) ∋ x`, `cl V(x) ⊆ W(x)`,
`cl V(x)` proper), `mem_of_π_mem_image_of_invariant` and `saturation_diff_inter_eq_empty`
(property (4) follows from (1)), `isScSmoothMap_orbitExtension` (the extension of an invariant
sc-smooth `f` supported in `W(x)` with proper support is sc-smooth), the invariant sc-smooth
Urysohn lemma `exists_isScSmoothMap_orbit_urysohn`, Part I's `admitsScPartitionsOfUnity_of_approx`
(Theorem 5.12 [5.37] "(ii) ⇒ (i)" for M-polyfolds) and `theorem_7_4`.

`B` is the conjunction of the proof's intermediate claims: existence of the `V(x)` with (1)–(4),
and, **for every choice** of `V(x), W(x)` with B's natural action `IsNatActionB` (Theorem 7.1's
clauses, `W(x)` not required connected), every refinement `(V'_i, V''_i)` and every subordinate
`β`, the invariance of `U''_i`, the support of the cut-offs, and the existence of `f_i`, `h_i`
with `(h_i / Σ h_j)` an sc-smooth partition of unity of `X` subordinate to the `U_λ`.

* `A → B`: only the first two claims are proved (`A_to_B_first_claims`), from
  `exists_invariant_nhds_of_isOpen` and `saturation_diff_inter_eq_empty` (a project
  `NaturalRep` gives B's `IsNatActionB`).  The rest is quantified over B's general natural-action
  data on possibly disconnected `W(x)`, for which A's `NaturalRep`-based lemmas
  (`orbitExtension`, `isScSmoothMap_orbitExtension`) and Lemma 7.10 do not apply, and it asks for
  the text's normalisation `h_i / Σ h_j` with the given refinement and `β`, whereas A's
  `theorem_7_4` goes through a bump covering of `|X|` and the invariant Urysohn lemma.  B is true
  as we read it; proving it means re-doing the construction (Lemma 7.10 for `IsNatActionB`, the
  extension and its sc-smoothness, local finiteness, the quotient).
* `B → A` is not attempted: `admitsScPartitionsOfUnity_of_approx` (a Part I theorem about
  M-polyfolds with the approximation property) and the invariant Urysohn lemma are not among
  B's claims.
-/

namespace RoundTrip.V7_67
open Polyfold Set

/-- The listed theorems of the proof of Theorem 7.4, universes at `0`. -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.exists_invariant_nhds_of_isOpen.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.mem_of_π_mem_image_of_invariant.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.saturation_diff_inter_eq_empty.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScSmoothMap_orbitExtension.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.exists_isScSmoothMap_orbit_urysohn.{0}) ∧
  (type_of% @Polyfold.admitsScPartitionsOfUnity_of_approx.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.theorem_7_4.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.exists_invariant_nhds_of_isOpen.{0},
    @Polyfold.EpGroupoid.mem_of_π_mem_image_of_invariant.{0},
    @Polyfold.EpGroupoid.saturation_diff_inter_eq_empty.{0},
    @Polyfold.EpGroupoid.isScSmoothMap_orbitExtension.{0},
    @Polyfold.EpGroupoid.exists_isScSmoothMap_orbit_urysohn.{0},
    @Polyfold.admitsScPartitionsOfUnity_of_approx.{0},
    @Polyfold.EpGroupoid.theorem_7_4.{0}⟩

/-- The first two claims of B: `(|U_λ|)` is an open cover of `|X|`, and every `x` has a `V(x)`
with (1)–(4). -/
def B_first_claims : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ParacompactSpace X.OrbitSpace → X.PObj.AdmitsScPartitionsOfUnity →
    ∀ (Λ : Type) (U : Λ → Set Obj), (∀ l, IsOpen (U l)) → (∀ l, IsSatB X (U l)) →
      ⋃ l, U l = Set.univ →
      ((∀ l, IsOpen (X.π '' U l)) ∧ (⋃ l, X.π '' U l) = Set.univ) ∧
      (∀ x : Obj, ∃ (V W : Set Obj) (Φ : X.Isotropy x → Obj → Obj)
        (Γ : X.Isotropy x → Obj → Mor), IsGoodNbhdB X U x V W Φ Γ)

/-- **`A → B` for the first two claims of B.** -/
theorem A_to_B_first_claims : A → B_first_claims := by
  rintro ⟨hex, -, hsat, -⟩ Obj Mor _ _ _ _ _ _ X _ _ Λ U hUo _ hcov
  refine ⟨⟨fun l => X.proposition_7_1 _ (hUo l), eq_univ_of_forall fun q => ?_⟩, fun x => ?_⟩
  · obtain ⟨y, rfl⟩ := X.surjective_π q
    obtain ⟨l, hl⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ y : y ∈ ⋃ l, U l)
    exact mem_iUnion.2 ⟨l, mem_image_of_mem _ hl⟩
  · obtain ⟨l, hl⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ x : x ∈ ⋃ l, U l)
    obtain ⟨R, V, hVo, hxV, hVinv, hVcl, hRW, hprop⟩ := hex X x (hUo l) hl
    refine ⟨V, R.U, R.Φ, R.Γ, hVo, hxV,
      ⟨R.isOpen_U, R.mem_U, fun g => ⟨R.Φ g⁻¹, R.isScDiffeoOn_Φ g⟩, R.Φ_mul, R.isScSmoothOn_Γ,
        R.Γ_self, fun g y hy => ⟨R.src_Γ g y hy, R.tgt_Γ g y hy⟩, R.existsUnique_Γ⟩,
      subset_closure, hVcl, hVinv, hprop, ⟨l, subset_closure.trans (hVcl.trans hRW)⟩, ?_⟩
    exact hsat R (subset_closure.trans hVcl) hVinv

#rt_check RoundTrip.V7_67.A_to_B_first_claims [Polyfold.EpGroupoid.exists_invariant_nhds_of_isOpen,
  Polyfold.EpGroupoid.mem_of_π_mem_image_of_invariant,
  Polyfold.EpGroupoid.saturation_diff_inter_eq_empty,
  Polyfold.EpGroupoid.isScSmoothMap_orbitExtension,
  Polyfold.EpGroupoid.exists_isScSmoothMap_orbit_urysohn,
  Polyfold.admitsScPartitionsOfUnity_of_approx,
  Polyfold.EpGroupoid.theorem_7_4]
#rt_overlap RoundTrip.V7_67.A_to_B_first_claims [Polyfold.EpGroupoid.exists_invariant_nhds_of_isOpen,
  Polyfold.EpGroupoid.mem_of_π_mem_image_of_invariant,
  Polyfold.EpGroupoid.saturation_diff_inter_eq_empty,
  Polyfold.EpGroupoid.isScSmoothMap_orbitExtension,
  Polyfold.EpGroupoid.exists_isScSmoothMap_orbit_urysohn,
  Polyfold.admitsScPartitionsOfUnity_of_approx,
  Polyfold.EpGroupoid.theorem_7_4]

end RoundTrip.V7_67
