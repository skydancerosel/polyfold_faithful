import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_63

/-!
Round trip for V7_63 (Lemma 7.8: morphisms between nearby points lie in the `N_g`).

`A` is the type of `Polyfold.EpGroupoid.lemma_7_6_2` at universe `0`: for ANY open sets
`N_g ∋ g` (`g ∈ G_x`) and any neighbourhood `U₀` of `x` there is an open `U₁ ⊆ U₀` of `x` such
that every morphism with source and target in `U₁` lies in some `N_g`.  `B` states the same
conclusion only for the choices of the proof of Theorem 7.5: open `U₀ ∋ x₀`, open `N^s_g, N^t_g ∋ g`
on which `s`, resp. `t`, is an sc-diffeomorphism onto `U₀`, the `N^s_g ∪ N^t_g` pairwise
disjoint, and `N_g = N^s_g ∩ N^t_g`.

* `A → B`: `A` with `N_g := N^s_g ∩ N^t_g` (open, contains `g`) and the open `U₀`.
* `B → A`: such choices exist inside any given `N_g` and `U₀`: separate the finite `G_x`
  (`finite_isotropy`) by disjoint open `D_g` (Hausdorff), take sheets `A^s_g, A^t_g ⊆ D_g ∩ N_g`
  of `s` and `t` (local sc-diffeomorphisms), `U₀' := int U₀ ∩ ⋂_g s(A^s_g) ∩ t(A^t_g)` and
  `N^s_g := A^s_g ∩ s⁻¹(U₀')`, `N^t_g := A^t_g ∩ t⁻¹(U₀')` (restrictions onto `U₀'`).  Then `B`
  gives `U₁ ⊆ U₀' ⊆ U₀`, and `N^s_g ∩ N^t_g ⊆ N_g`.
-/

namespace RoundTrip.V7_63
open Polyfold Set Topology

/-- The project's Lemma 7.8, universes at `0`. -/
def A : Prop := type_of% @Polyfold.EpGroupoid.lemma_7_6_2.{0}

theorem A_holds : A := @Polyfold.EpGroupoid.lemma_7_6_2.{0}

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X x₀ U₀ Ns Nt hC
  obtain ⟨hU₀o, hxU₀, hN, -, -, -⟩ := hC
  exact hA X (N := fun g => Ns g ∩ Nt g) (fun g => (hN g).1.inter (hN g).2.1)
    (fun g => ⟨(hN g).2.2.1, (hN g).2.2.2⟩) (hU₀o.mem_nhds hxU₀)

theorem B_to_A : B → A := by
  intro hB Obj Mor _ _ _ _ _ _ X x N hNo hgN U₀ hU₀
  have := EpGroupoid.NatRepConstruction.finite_isotropy X x
  -- disjoint open `D_g ∋ g`
  obtain ⟨D, hD, hdisj⟩ := (Set.finite_range fun g : X.Isotropy x => g.val).t2_separation
  have hW : ∀ g : X.Isotropy x, IsOpen (D g.val ∩ N g) ∧ g.val ∈ D g.val ∩ N g := fun g =>
    ⟨(hD g.val).2.inter (hNo g), (hD g.val).1, hgN g⟩
  -- sheets of `s` and `t` inside `D_g ∩ N_g`
  choose As Ss σ hgAs hAsW hσ using fun g =>
    X.isLocalScDiffeo_src.exists_isScDiffeoOn_subset (hW g).1 (hW g).2
  choose At Tt τ hgAt hAtW hτ using fun g =>
    X.isLocalScDiffeo_tgt.exists_isScDiffeoOn_subset (hW g).1 (hW g).2
  -- the common target `U₀'`
  set U₀' := interior U₀ ∩ ⋂ g, Ss g ∩ Tt g with hU₀'
  have hU₀'o : IsOpen U₀' := isOpen_interior.inter
    (isOpen_iInter_of_finite fun g => (hσ g).isOpen_target.inter (hτ g).isOpen_target)
  have hxU₀' : x ∈ U₀' := by
    refine ⟨mem_interior_iff_mem_nhds.2 hU₀, mem_iInter.2 fun g => ⟨?_, ?_⟩⟩
    · have := (hσ g).mapsTo (hgAs g)
      rwa [g.src_val] at this
    · have := (hτ g).mapsTo (hgAt g)
      rwa [g.tgt_val] at this
  have hU₀'S : ∀ g, U₀' ⊆ Ss g := fun g y hy => (mem_iInter.1 hy.2 g).1
  have hU₀'T : ∀ g, U₀' ⊆ Tt g := fun g y hy => (mem_iInter.1 hy.2 g).2
  -- restrictions onto `U₀'`
  have hσ' : ∀ g, X.PMor.IsScDiffeoOn X.PObj X.src (σ g) (As g ∩ X.src ⁻¹' U₀') U₀' := fun g =>
    ((hσ g).symm.restrict hU₀'o (hU₀'S g)).symm
  have hτ' : ∀ g, X.PMor.IsScDiffeoOn X.PObj X.tgt (τ g) (At g ∩ X.tgt ⁻¹' U₀') U₀' := fun g =>
    ((hτ g).symm.restrict hU₀'o (hU₀'T g)).symm
  have hCh : IsChoicesB X x U₀' (fun g => As g ∩ X.src ⁻¹' U₀') (fun g => At g ∩ X.tgt ⁻¹' U₀') := by
    refine ⟨hU₀'o, hxU₀', fun g => ⟨(hσ' g).isOpen_source, (hτ' g).isOpen_source,
      ⟨hgAs g, by rw [mem_preimage, g.src_val]; exact hxU₀'⟩,
      ⟨hgAt g, by rw [mem_preimage, g.tgt_val]; exact hxU₀'⟩⟩, fun g => ⟨σ g, hσ' g⟩,
      fun g => ⟨τ g, hτ' g⟩, fun g g' hne => ?_⟩
    have hsub : ∀ g : X.Isotropy x,
        (As g ∩ X.src ⁻¹' U₀') ∪ (At g ∩ X.tgt ⁻¹' U₀') ⊆ D g.val := fun g φ hφ => by
      rcases hφ with hφ | hφ
      · exact (hAsW g hφ.1).1
      · exact (hAtW g hφ.1).1
    exact Disjoint.mono (hsub g) (hsub g') (hdisj (mem_range_self g) (mem_range_self g')
      fun h => hne (GroupoidStr.Isotropy.ext h))
  obtain ⟨U₁, hU₁o, hxU₁, hU₁U₀', hU₁⟩ := hB Obj Mor X x U₀' _ _ hCh
  refine ⟨U₁, hU₁o, hxU₁, fun y hy => interior_subset (hU₁U₀' hy).1, fun h hs ht => ?_⟩
  obtain ⟨g, hgs, -⟩ := hU₁ h hs ht
  exact ⟨g, (hAsW g hgs.1).2⟩

#rt_check RoundTrip.V7_63.A_to_B [Polyfold.EpGroupoid.lemma_7_6_2]
#rt_check RoundTrip.V7_63.B_to_A [Polyfold.EpGroupoid.lemma_7_6_2]
#rt_overlap RoundTrip.V7_63.B_to_A [Polyfold.EpGroupoid.lemma_7_6_2]
#rt_overlap RoundTrip.V7_63.A_to_B [Polyfold.EpGroupoid.lemma_7_6_2]

end RoundTrip.V7_63
