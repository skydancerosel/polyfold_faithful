import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_55

/-!
Round trip for V7_55 (Theorem 7.3: continuous partitions of unity).

`A` is the conjunction of the types of the three listed theorems (universes at `0`, for the object
universe and for the index universe): `orbitPullback_isSubordinate`,
`exists_isSaturated_nhds_finite_orbitPullback` (two facts about the project's pull-back
`σ ∘ π` of a partition of unity of `|X|`) and `theorem_7_5_4`.

* `A → B`: (1) is `theorem_7_5_4`'s (1).  For (2), `theorem_7_5_4`'s saturated open neighbourhood `W`
  gives B's `V = π(W)`, open since `π` is open (Proposition 7.1), with `π⁻¹(V) = W`; invariance
  `β(s φ) = β(t φ)` is B's `IsoB y z → β y = β z`.
* `B → A`: `theorem_7_5_4` from B (`W = π⁻¹(V)`, open and saturated since `π` is continuous and
  surjective).  The two lemmas on `orbitPullback` are about the project's construction, which B
  does not mention; they are proved outright (two short arguments: `supp(σ ∘ π) ⊆ π⁻¹(supp σ)`
  and local finiteness of `(supp σ_λ)` at `π(x)`).
-/

namespace RoundTrip.V7_55
open Polyfold Set

/-- The listed theorems (universes at `0`). -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.orbitPullback_isSubordinate.{0, 0} ∧
  type_of% @Polyfold.EpGroupoid.exists_isSaturated_nhds_finite_orbitPullback.{0, 0} ∧
  type_of% @Polyfold.EpGroupoid.theorem_7_5_4.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.orbitPullback_isSubordinate.{0, 0},
    @Polyfold.EpGroupoid.exists_isSaturated_nhds_finite_orbitPullback.{0, 0},
    @Polyfold.EpGroupoid.theorem_7_5_4.{0, 0}⟩

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

theorem isSaturated_preimage (X : EpGroupoid Obj Mor) (V : Set X.OrbitSpace) :
    X.IsSaturated (X.π ⁻¹' V) := by
  change X.π ⁻¹' (X.π '' (X.π ⁻¹' V)) = X.π ⁻¹' V
  rw [image_preimage_eq _ X.surjective_π]

end

theorem A_to_B : A → B := by
  rintro ⟨-, -, h3⟩ Obj Mor _ _ _ _ _ _ X hX
  obtain ⟨h1, h2⟩ := h3 X hX
  refine ⟨h1, fun Λ U hUo hUs hcov => ?_⟩
  obtain ⟨β, hsub, hW, hinv⟩ := h2 Λ U hUo hUs hcov
  refine ⟨β, hsub, fun l y z ⟨φ, hy, hz⟩ => hy ▸ hz ▸ hinv l φ, fun x => ?_⟩
  obtain ⟨W, hWo, hWs, hxW, hfin⟩ := hW x
  refine ⟨X.π '' W, X.proposition_7_1_8 _ hWo, mem_image_of_mem _ hxW, ?_⟩
  have e : X.π ⁻¹' (X.π '' W) = W := hWs
  rw [e]
  exact hfin

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  -- `orbitPullback_isSubordinate`: outright
  · intro Obj Mor _ _ _ _ _ _ X ι σ U hσ hU i
    have h1 : tsupport (X.orbitPullback σ i) ⊆ X.π ⁻¹' tsupport (σ i) :=
      tsupport_comp_subset_preimage (σ i) X.continuous_π
    exact (h1.trans (preimage_mono (hσ i))).trans (hU i).subset
  -- `exists_isSaturated_nhds_finite_orbitPullback`: outright
  · intro Obj Mor _ _ _ _ _ _ X ι σ x
    obtain ⟨t, ht, hfin⟩ := σ.locallyFinite_tsupport (X.π x)
    refine ⟨X.π ⁻¹' interior t, isOpen_interior.preimage X.continuous_π,
      isSaturated_preimage X _, mem_interior_iff_mem_nhds.2 ht, hfin.subset fun i hi => ?_⟩
    obtain ⟨y, hyW, hys⟩ := hi
    have h1 : tsupport (X.orbitPullback σ i) ⊆ X.π ⁻¹' tsupport (σ i) :=
      tsupport_comp_subset_preimage (σ i) X.continuous_π
    exact ⟨X.π y, h1 hys, interior_subset hyW⟩
  -- `theorem_7_5_4`: from `B`
  · intro Obj Mor _ _ _ _ _ _ X hX
    obtain ⟨h1, h2⟩ := hB Obj Mor X hX
    refine ⟨h1, fun ι U hUo hUs hcov => ?_⟩
    obtain ⟨β, hsub, hinv, hV⟩ := h2 ι U hUo hUs hcov
    refine ⟨β, hsub, fun x => ?_, fun i φ => hinv i _ _ ⟨φ, rfl, rfl⟩⟩
    obtain ⟨V, hVo, hxV, hfin⟩ := hV x
    exact ⟨X.π ⁻¹' V, hVo.preimage X.continuous_π, isSaturated_preimage X V, hxV, hfin⟩

#rt_check RoundTrip.V7_55.A_to_B [Polyfold.EpGroupoid.orbitPullback_isSubordinate,
  Polyfold.EpGroupoid.exists_isSaturated_nhds_finite_orbitPullback,
  Polyfold.EpGroupoid.theorem_7_5_4]
#rt_check RoundTrip.V7_55.B_to_A [Polyfold.EpGroupoid.orbitPullback_isSubordinate,
  Polyfold.EpGroupoid.exists_isSaturated_nhds_finite_orbitPullback,
  Polyfold.EpGroupoid.theorem_7_5_4]
#rt_overlap RoundTrip.V7_55.B_to_A [Polyfold.EpGroupoid.orbitPullback_isSubordinate,
  Polyfold.EpGroupoid.exists_isSaturated_nhds_finite_orbitPullback,
  Polyfold.EpGroupoid.theorem_7_5_4]

end RoundTrip.V7_55
