import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_62

/-!
Round trip for V7_62 (Theorem 7.5, the natural representation, with the form of its proof).

`A` is the conjunction of the types of the three theorems listed for the item, universes at `0`:
`theorem_7_5` (`∃ R : X.NaturalRep x, R.U ⊆ V`), `NatRepConstruction.exists_sheets` (the choices
of the proof exist) and `NatRepConstruction.exists_naturalRep_sheets` (sheets `D` and a natural
representation `R` with `R.U ⊆ V`, `R.U ⊆ s(N_g)`, `R.Φ = t_g ∘ s_g⁻¹`, `R.Γ = s_g⁻¹`).  The
definitions `Sheets`, `Sheets.mkRep`, `restrict` are vocabulary.  `B` asks for an open `U ⊆ V`
with the natural action (`U` not required connected) and pairwise disjoint sheets `N_g ∋ g` of
`s` and `t` with `Γ(g, y) ∈ N_g`.

* `A → B`: from `exists_naturalRep_sheets`, `U := R.U`, `N := D.N`; `Γ(g, y) = s_g⁻¹(y) ∈ N_g`.
* `B → A`: the sheets of `B` (with the inverses of `s|N_g`) are a `Sheets`; on `U`,
  `s_g⁻¹ = Γ(g, ·)` and `t_g ∘ s_g⁻¹ = Φ(g)` (since `Γ(g, y) ∈ N_g` and `s Γ(g, y) = y`).  The
  connected component `C` of `x₀` in `U` is open (M-polyfolds are locally connected) and
  invariant under every `Φ(g)` (continuous, fixing `x₀`); the `NaturalRep` on `C` with
  `Φ := t_g ∘ s_g⁻¹`, `Γ := s_g⁻¹` is built field by field from `B`'s clauses (homomorphism,
  `Φ(1) = id` from injectivity, smoothness of `Φ(g)`, `Γ(g, ·)` by `congr`), without the
  project's `Sheets.mkRep` (which re-derives the homomorphism property from connectedness).
  `exists_sheets` is the case `V = univ`, `theorem_7_5` forgets the sheets.
-/

namespace RoundTrip.V7_62
open Polyfold Set

/-- The project's Theorem 7.5 and the form of its proof, universes at `0`. -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.theorem_7_5.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NatRepConstruction.exists_sheets.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NatRepConstruction.exists_naturalRep_sheets.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.theorem_7_5.{0},
   @Polyfold.EpGroupoid.NatRepConstruction.exists_sheets.{0},
   @Polyfold.EpGroupoid.NatRepConstruction.exists_naturalRep_sheets.{0}⟩

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X x₀ V hV hx
  obtain ⟨D, R, hRV, hUS, hΦ, hΓ⟩ := hA.2.2 X x₀ hV hx
  refine ⟨R.U, R.Φ, R.Γ, hRV, ⟨R.isOpen_U, R.mem_U, fun g => ⟨R.Φ g⁻¹, R.isScDiffeoOn_Φ g⟩,
    R.Φ_mul, R.isScSmoothOn_Γ, R.Γ_self, fun g y hy => ⟨R.src_Γ g y hy, R.tgt_Γ g y hy⟩,
    R.existsUnique_Γ⟩, D.N, D.disjoint_N, D.mem_N, fun g => ⟨D.σ g, D.S g, D.isScDiffeoOn_src g⟩,
    D.isScDiffeoOn_tgt, fun g y hy => ?_⟩
  rw [hΓ]
  exact D.σ_mem_N g (hUS g hy)

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `exists_naturalRep_sheets` from `B`. -/
theorem exists_naturalRep_sheets_of_B (hB : B) (X : EpGroupoid Obj Mor) (x₀ : Obj)
    {V : Set Obj} (hV : IsOpen V) (hx : x₀ ∈ V) :
    ∃ (D : EpGroupoid.NatRepConstruction.Sheets X x₀) (R : X.NaturalRep x₀), R.U ⊆ V ∧
      (∀ g, R.U ⊆ D.S g) ∧ R.Φ = D.hat ∧ R.Γ = D.σ := by
  obtain ⟨U, Φ, Γ, hUV, ⟨hUo, hxU, hΦd, hΦmul, hΓsm, hΓself, hsΓ, huniq⟩, N, hdisj, hmem, hsrc,
    htgt, hΓN⟩ := hB Obj Mor X x₀ V hV hx
  choose σ S hσ using hsrc
  let D : EpGroupoid.NatRepConstruction.Sheets X x₀ := ⟨N, S, σ, hmem, hdisj, hσ, htgt⟩
  -- on `U`: `s_g⁻¹ = Γ(g, ·)`, `U ⊆ s(N_g)`, `t_g ∘ s_g⁻¹ = Φ(g)`
  have hσΓ : ∀ g, ∀ y ∈ U, D.σ g y = Γ g y := fun g y hy => by
    have := (hσ g).left_inv _ (hΓN g y hy)
    rwa [(hsΓ g y hy).1] at this
  have hUS : ∀ g, U ⊆ D.S g := fun g y hy => by
    have := (hσ g).mapsTo (hΓN g y hy)
    rwa [(hsΓ g y hy).1] at this
  have hhat : ∀ g, ∀ y ∈ U, D.hat g y = Φ g y := fun g y hy => by
    rw [EpGroupoid.NatRepConstruction.Sheets.hat_apply, hσΓ g y hy, (hsΓ g y hy).2]
  have hΦx : ∀ g, Φ g x₀ = x₀ := fun g => by
    rw [← (hsΓ g x₀ hxU).2, hΓself]
    exact g.tgt_val
  -- `Φ(1) = id` on `U` (from the homomorphism property and injectivity)
  have hΦone : ∀ y ∈ U, Φ 1 y = y := fun y hy => by
    obtain ⟨ψ, hψ⟩ := hΦd 1
    have h2 := hΦmul 1 1 y hy
    rw [mul_one] at h2
    exact hψ.injOn (hψ.mapsTo hy) hy h2.symm
  have hΦinv : ∀ g, ∀ y ∈ U, Φ g⁻¹ (Φ g y) = y := fun g y hy => by
    rw [← hΦmul g⁻¹ g y hy, inv_mul_cancel, hΦone y hy]
  have hΦinv' : ∀ g, ∀ y ∈ U, Φ g (Φ g⁻¹ y) = y := fun g y hy => by
    rw [← hΦmul g g⁻¹ y hy, mul_inv_cancel, hΦone y hy]
  -- the connected component `C` of `x₀` in `U`
  set C := connectedComponentIn U x₀ with hCdef
  have hCU : C ⊆ U := connectedComponentIn_subset U x₀
  have hxC : x₀ ∈ C := mem_connectedComponentIn hxU
  have hCo : IsOpen C := X.PObj.isOpen_connectedComponentIn hUo x₀
  have hCc : IsConnected C := isConnected_connectedComponentIn_iff.2 hxU
  have hinv : ∀ g, MapsTo (D.hat g) C C := fun g y hy => by
    obtain ⟨ψ, hψ⟩ := hΦd g
    have hpre : IsPreconnected (Φ g '' C) :=
      isPreconnected_connectedComponentIn.image _ (hψ.isScSmoothOn.continuousOn.mono hCU)
    rw [hhat g y (hCU hy)]
    exact hpre.subset_connectedComponentIn ⟨x₀, hxC, hΦx g⟩
      ((hψ.mapsTo.mono_left hCU).image_subset) ⟨y, hy, rfl⟩
  have hsm : ∀ g, X.PObj.IsScSmoothOn X.PObj (D.hat g) C := fun g => by
    obtain ⟨ψ, hψ⟩ := hΦd g
    exact (hψ.isScSmoothOn.mono hCo hCU).congr fun y hy => (hhat g y (hCU hy)).symm
  -- the natural representation on `C`, with `Φ = t_g ∘ s_g⁻¹` and `Γ = s_g⁻¹`
  let R : X.NaturalRep x₀ :=
    { U := C
      isOpen_U := hCo
      isConnected_U := hCc
      mem_U := hxC
      Φ := D.hat
      Γ := D.σ
      isScDiffeoOn_Φ := fun g =>
        { isScSmoothOn := hsm g
          isScSmoothOn_inv := hsm g⁻¹
          mapsTo := hinv g
          mapsTo_inv := hinv g⁻¹
          left_inv := fun y hy => by
            rw [hhat g y (hCU hy), hhat g⁻¹ _ (hCU (hinv g hy) |> fun h => by
              rwa [hhat g y (hCU hy)] at h), hΦinv g y (hCU hy)]
          right_inv := fun y hy => by
            rw [hhat g⁻¹ y (hCU hy), hhat g _ (hCU (hinv g⁻¹ hy) |> fun h => by
              rwa [hhat g⁻¹ y (hCU hy)] at h), hΦinv' g y (hCU hy)] }
      Φ_mul := fun g h y hy => by
        have hhy : Φ h y ∈ U := by
          have := hCU (hinv h hy)
          rwa [hhat h y (hCU hy)] at this
        rw [hhat _ y (hCU hy), hhat h y (hCU hy), hhat g _ hhy, hΦmul g h y (hCU hy)]
      isScSmoothOn_Γ := fun g =>
        ((hΓsm g).mono hCo hCU).congr fun y hy => (hσΓ g y (hCU hy)).symm
      Γ_self := fun g => by rw [hσΓ g x₀ hxU, hΓself]
      src_Γ := fun g y hy => by rw [hσΓ g y (hCU hy), (hsΓ g y (hCU hy)).1]
      tgt_Γ := fun _ _ _ => rfl
      existsUnique_Γ := fun h hs ht => by
        obtain ⟨g, hg, hu⟩ := huniq h (hCU hs) (hCU ht)
        refine ⟨g, (hσΓ g _ (hCU hs)).trans hg, fun g' hg' => hu g' ?_⟩
        exact (hσΓ g' _ (hCU hs)).symm.trans hg' }
  exact ⟨D, R, hCU.trans hUV, fun g => hCU.trans (hUS g), rfl, rfl⟩

end

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X x V hV hx
    obtain ⟨-, R, hRV, -⟩ := exists_naturalRep_sheets_of_B hB X x hV hx
    exact ⟨R, hRV⟩
  · intro Obj Mor _ _ _ _ _ _ X x
    obtain ⟨D, -⟩ := exists_naturalRep_sheets_of_B hB X x isOpen_univ (mem_univ x)
    exact ⟨D⟩
  · intro Obj Mor _ _ _ _ _ _ X x V hV hx
    exact exists_naturalRep_sheets_of_B hB X x hV hx

#rt_check RoundTrip.V7_62.A_to_B [Polyfold.EpGroupoid.theorem_7_5,
  Polyfold.EpGroupoid.NatRepConstruction.exists_sheets,
  Polyfold.EpGroupoid.NatRepConstruction.exists_naturalRep_sheets]
#rt_check RoundTrip.V7_62.B_to_A [Polyfold.EpGroupoid.theorem_7_5,
  Polyfold.EpGroupoid.NatRepConstruction.exists_sheets,
  Polyfold.EpGroupoid.NatRepConstruction.exists_naturalRep_sheets]
#rt_overlap RoundTrip.V7_62.B_to_A [Polyfold.EpGroupoid.theorem_7_5,
  Polyfold.EpGroupoid.NatRepConstruction.exists_sheets,
  Polyfold.EpGroupoid.NatRepConstruction.exists_naturalRep_sheets]
#rt_overlap RoundTrip.V7_62.A_to_B [Polyfold.EpGroupoid.theorem_7_5,
  Polyfold.EpGroupoid.NatRepConstruction.exists_sheets,
  Polyfold.EpGroupoid.NatRepConstruction.exists_naturalRep_sheets]

end RoundTrip.V7_62
