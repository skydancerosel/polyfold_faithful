import Polyfold.Chapter4.Submanifolds

/-!
# Basic facts on smooth submanifolds

Smooth submanifolds restrict to open sets and subsets, and sc⁺-retractions on a set restrict to
smaller sets. The symmetric results are in `Chapter9/Symmetric.lean`.
-/

set_option maxSynthPendingDepth 3
open Set
noncomputable section
namespace Polyfold
namespace MPolyfold
universe u v
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- An sc⁺-retraction on `V` restricts to an sc⁺-retraction on every open `W ⊆ V` that it maps
into itself. -/
theorem IsScPlusRetractionOn.mono {s : X → X} {V W : Set X} (h : P.IsScPlusRetractionOn s V)
    (hW : IsOpen W) (hWV : W ⊆ V) (hmaps : MapsTo s W W) : P.IsScPlusRetractionOn s W where
  isScSmoothOn := h.isScSmoothOn.mono hW hWV
  mapsTo := hmaps
  idem x hx := h.idem x (hWV hx)
  mem_levelSet x hx := h.mem_levelSet x (hWV hx)
  isScSmoothOn_one x₀ := (h.isScSmoothOn_one x₀).mono hW hWV

/-- The local data of Definition 4.13 for `A`, inside a given open `V`: every `a ∈ A ∩ V` has an
open neighbourhood `W ⊆ V` with an sc⁺-retraction `s : W → W`, `s(W) = A ∩ W`
(`W = V' ∩ V ∩ s⁻¹(V)` for the data `(V', s)` of `A` at `a`). -/
theorem IsSmoothSubmanifold.exists_subset {A V : Set X} (hA : P.IsSmoothSubmanifold A)
    (hV : IsOpen V) {a : X} (ha : a ∈ A) (haV : a ∈ V) :
    ∃ W : Set X, IsOpen W ∧ a ∈ W ∧ W ⊆ V ∧
      ∃ s : X → X, P.IsScPlusRetractionOn s W ∧ s '' W = A ∩ W := by
  obtain ⟨V', hV', haV', s, hs, himg⟩ := hA a ha
  have hsa : s a = a := by
    obtain ⟨b, hb, hba⟩ := (himg.symm ▸ ⟨ha, haV'⟩ : a ∈ s '' V')
    rw [← hba, hs.idem b hb]
  have hWo : IsOpen (V' ∩ V ∩ s ⁻¹' V) :=
    (hs.isScSmoothOn.continuousOn.mono inter_subset_left).isOpen_inter_preimage
      (hV'.inter hV) hV
  have hmaps : MapsTo s (V' ∩ V ∩ s ⁻¹' V) (V' ∩ V ∩ s ⁻¹' V) := fun y hy => by
    refine ⟨⟨hs.mapsTo hy.1.1, hy.2⟩, ?_⟩
    change s (s y) ∈ V
    rw [hs.idem y hy.1.1]
    exact hy.2
  refine ⟨V' ∩ V ∩ s ⁻¹' V, hWo, ⟨⟨haV', haV⟩, by rw [mem_preimage, hsa]; exact haV⟩,
    fun y hy => hy.1.2, s, hs.mono hWo (fun y hy => hy.1.1) hmaps, ?_⟩
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hz : s y ∈ s '' V' := ⟨y, hy.1.1, rfl⟩
    rw [himg] at hz
    exact ⟨hz.1, hmaps hy⟩
  · rintro ⟨hzA, hz⟩
    obtain ⟨b, hb, hbz⟩ := (himg.symm ▸ ⟨hzA, hz.1.1⟩ : z ∈ s '' V')
    refine ⟨z, hz, ?_⟩
    rw [← hbz, hs.idem b hb]

/-- **An open piece of a submanifold is a submanifold**: if `A` is a smooth finite-dimensional
submanifold (Definition 4.13) and `V` is open, then `A ∩ V` is one. -/
theorem IsSmoothSubmanifold.inter_isOpen {A V : Set X} (hA : P.IsSmoothSubmanifold A)
    (hV : IsOpen V) : P.IsSmoothSubmanifold (A ∩ V) := by
  rintro a ⟨ha, haV⟩
  obtain ⟨W, hW, haW, hWV, s, hs, himg⟩ := hA.exists_subset hV ha haV
  refine ⟨W, hW, haW, s, hs, ?_⟩
  rw [himg, inter_assoc, inter_eq_right.2 hWV]

end MPolyfold
end Polyfold
end
