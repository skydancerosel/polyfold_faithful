import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_64

/-!
Round trip for V7_64 (Lemma 7.9: the invariant neighbourhood `U = ⋃_g t_g s_g⁻¹(U₂)`).

`A` is the conjunction of the types, at universe `0`, of the listed theorems:
`EpGroupoid.lemma_7_9` (for sheets `D : NatRepConstruction.Sheets X x` and an open `U₁ ∋ x` inside
every `s(N_g)` with the property of Lemma 7.8, a connected open `U₂ ∋ x`, `U₂ ⊆ U₁`, with
`D.unionHat U₂ ⊆ U₁` invariant under every `D.hat g = t_g ∘ s_g⁻¹`), and the sheet lemmas
`isConnected_unionHat`, `eqOn_σ_one`, `eqOn_σ_mul`, `hat_one`, `hat_mul` (on a connected
invariant `U`: `U` connected, `s_1⁻¹ = u`, `Φ(1) = id`, `Φ(gh) = Φ(g) Φ(h)`).  `unionHat` is a
definition (vocabulary).

`A → B`: B's choices (`s : N^s_g → U₀`, `t : N^t_g → U₀` sc-diffeomorphisms, `N^s_g ∪ N^t_g`
disjoint) give project sheets on `N_g = N^s_g ∩ N^t_g` (restriction of the two
sc-diffeomorphisms, `S g = U₀ ∩ s_g⁻¹⁻¹(N_g) = s(N_g)`).  B's `U₁ ⊆ U₀` need not lie in the
smaller `s(N_g)`, so Lemma 7.9 is applied to `U₁ ∩ ⋂_g s(N_g)` (open, `G_x` finite); B's images
`t(N_g ∩ s⁻¹(A))` are `D.hat g '' A` for `A ⊆ s(N_g)` (`Sheets.image_σ`).

`B → A` is not attempted: B says nothing about the homomorphism lemmas (`eqOn_σ_one`,
`eqOn_σ_mul`, `hat_one`, `hat_mul`), nor about connectedness (`isConnected_unionHat`, the
connected `U₂` of `lemma_7_9`).
-/

namespace RoundTrip.V7_64
open Polyfold Set

/-- The project's Lemma 7.9 and the listed sheet lemmas, universes at `0`. -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.lemma_7_9.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NatRepConstruction.Sheets.isConnected_unionHat.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NatRepConstruction.Sheets.eqOn_σ_one.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NatRepConstruction.Sheets.eqOn_σ_mul.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NatRepConstruction.Sheets.hat_one.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NatRepConstruction.Sheets.hat_mul.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.lemma_7_9.{0},
    @Polyfold.EpGroupoid.NatRepConstruction.Sheets.isConnected_unionHat.{0},
    @Polyfold.EpGroupoid.NatRepConstruction.Sheets.eqOn_σ_one.{0},
    @Polyfold.EpGroupoid.NatRepConstruction.Sheets.eqOn_σ_mul.{0},
    @Polyfold.EpGroupoid.NatRepConstruction.Sheets.hat_one.{0},
    @Polyfold.EpGroupoid.NatRepConstruction.Sheets.hat_mul.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h79, -⟩ Obj Mor _ _ _ _ _ _ X x₀ U₀ Ns Nt U₁ hC hL
  obtain ⟨-, -, hNo, hσex, hτex, hdisj⟩ := hC
  obtain ⟨hU₁o, hxU₁, hU₁U₀, h78⟩ := hL
  choose σ hσ using hσex
  choose τ hτ using hτex
  -- the project's sheets on `N_g = N^s_g ∩ N^t_g`
  have hNo' : ∀ g, IsOpen (Ns g ∩ Nt g) := fun g => (hNo g).1.inter (hNo g).2.1
  let D : EpGroupoid.NatRepConstruction.Sheets X x₀ :=
    { N := fun g => Ns g ∩ Nt g
      S := fun g => U₀ ∩ σ g ⁻¹' (Ns g ∩ Nt g)
      σ := σ
      mem_N := fun g => ⟨(hNo g).2.2.1, (hNo g).2.2.2⟩
      disjoint_N := fun g g' hne => (hdisj hne).mono
        (inter_subset_left.trans subset_union_left) (inter_subset_left.trans subset_union_left)
      isScDiffeoOn_src := fun g => (hσ g).restrict (hNo' g) inter_subset_left
      isScDiffeoOn_tgt := fun g => ⟨τ g, _, (hτ g).restrict (hNo' g) inter_subset_right⟩ }
  have hSeq : ∀ g, D.S g = X.src '' (Ns g ∩ Nt g) := by
    intro g
    ext y
    constructor
    · rintro ⟨hy, hyN⟩
      exact ⟨σ g y, hyN, (hσ g).right_inv y hy⟩
    · rintro ⟨φ, hφ, rfl⟩
      refine ⟨(hσ g).mapsTo hφ.1, ?_⟩
      change σ g (X.src φ) ∈ Ns g ∩ Nt g
      rw [(hσ g).left_inv φ hφ.1]
      exact hφ
  -- `t_g s_g⁻¹(A) = D.hat g '' A` for `A ⊆ s(N_g)`
  have hhat : ∀ g {A : Set Obj}, A ⊆ D.S g → hatImage X Ns Nt g A = D.hat g '' A := by
    intro g A hA
    have h1 : D.hat g '' A = X.tgt '' (D.σ g '' A) := by
      rw [image_image]
      rfl
    rw [h1, D.image_σ g hA]
    rfl
  -- Lemma 7.9 for `U₁' = U₁ ∩ ⋂_g s(N_g)`
  have := EpGroupoid.NatRepConstruction.finite_isotropy X x₀
  let U₁' := U₁ ∩ ⋂ g, D.S g
  have hU₁'o : IsOpen U₁' := hU₁o.inter (isOpen_iInter_of_finite fun g => D.isOpen_S g)
  have hxU₁' : x₀ ∈ U₁' := ⟨hxU₁, mem_iInter.2 fun g => D.mem_S g⟩
  have hU₁'S : ∀ g, U₁' ⊆ D.S g := fun g y hy => mem_iInter.1 hy.2 g
  obtain ⟨U₂, hU₂o, -, hxU₂, hU₂U₁', hUU₁', hinv⟩ := h79 X D hU₁'o hxU₁' hU₁'S
    fun h hs ht => h78 h hs.1 ht.1
  have hU₂S : ∀ g, U₂ ⊆ D.S g := fun g => hU₂U₁'.trans (hU₁'S g)
  have hUS : ∀ g, D.unionHat U₂ ⊆ D.S g := fun g => hUU₁'.trans (hU₁'S g)
  have hUeq : (⋃ g, hatImage X Ns Nt g U₂) = D.unionHat U₂ := by
    simp only [EpGroupoid.NatRepConstruction.Sheets.unionHat]
    exact iUnion_congr fun g => hhat g (hU₂S g)
  refine ⟨U₂, ?_⟩
  rw [hUeq]
  refine ⟨hU₂o, hxU₂, fun y hy => (hU₂U₁' hy).1, fun g => (hU₂S g).trans (hSeq g).subset,
    D.isOpen_unionHat hU₂o hU₂S, D.mem_unionHat hxU₂, fun y hy => (hUU₁' hy).1,
    fun g => ⟨(hUS g).trans (hSeq g).subset, ?_⟩⟩
  rw [hhat g (hUS g)]
  exact (hinv g).image_subset

#rt_check RoundTrip.V7_64.A_to_B [Polyfold.EpGroupoid.lemma_7_9,
  Polyfold.EpGroupoid.NatRepConstruction.Sheets.isConnected_unionHat,
  Polyfold.EpGroupoid.NatRepConstruction.Sheets.eqOn_σ_one,
  Polyfold.EpGroupoid.NatRepConstruction.Sheets.eqOn_σ_mul,
  Polyfold.EpGroupoid.NatRepConstruction.Sheets.hat_one,
  Polyfold.EpGroupoid.NatRepConstruction.Sheets.hat_mul]
#rt_overlap RoundTrip.V7_64.A_to_B [Polyfold.EpGroupoid.lemma_7_9,
  Polyfold.EpGroupoid.NatRepConstruction.Sheets.isConnected_unionHat,
  Polyfold.EpGroupoid.NatRepConstruction.Sheets.eqOn_σ_one,
  Polyfold.EpGroupoid.NatRepConstruction.Sheets.eqOn_σ_mul,
  Polyfold.EpGroupoid.NatRepConstruction.Sheets.hat_one,
  Polyfold.EpGroupoid.NatRepConstruction.Sheets.hat_mul]

end RoundTrip.V7_64
