import Polyfold.Chapter7.NaturalRep
import Polyfold.Chapter7.NaturalAction

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, §18.4, an
auxiliary step for the construction of p. 854 and Proposition 18.4.3 (2021 p. 855): **natural
representations carried along an embedding of an ep-groupoid onto an open full piece**.

The construction of p. 854 lives in one strong bundle uniformizer `Ψ̄`; in the model of a covering
family `c ⊔ {Ψ̄}` the uniformizer is one open summand, and the morphisms between its points are
those of `M(Ψ, Ψ)` whatever `c` is.  A natural representation (Theorem 7.1.13) chosen once in the
model of `{Ψ̄}` alone is carried to every model `c ⊔ {Ψ̄}` by the data below, so that the
neighbourhoods of the construction can be chosen before `c`.

## What is formalized (namespace `Polyfold.EpGroupoid`)

* `PieceEmbedding X₀ X`: maps `fo` on objects and `fm` on morphisms compatible with source,
  target and composition, `fm` injective, `fo` an open embedding with an sc-smooth left inverse
  `go` on its open range, every morphism of `X` between points of the range being some `fm a`.
* `PieceEmbedding.isotropyEquiv`: `G_{x₀} ≅ G_{fo x₀}`.
* `PieceEmbedding.naturalRep`: a natural representation `R₀` of `G_{x₀}` on `U₀` gives one of
  `G_{fo x₀}` on `fo(U₀)`, with `Φ(g)(fo y) = fo(Φ₀(g)(y))` and `Γ(g, fo y) = fm(Γ₀(g, y))`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj₀ Mor₀ Obj Mor : Type u}
  [TopologicalSpace Obj₀] [T2Space Obj₀] [ParacompactSpace Obj₀]
  [TopologicalSpace Mor₀] [T2Space Mor₀] [ParacompactSpace Mor₀]
  [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **An embedding of the ep-groupoid `X₀` onto an open full piece of `X`**: `fo` and `fm` are
compatible with the structure maps and the composition, `fm` is injective, `fo` is sc-smooth and
open with an sc-smooth left inverse `go` on its open range, and every morphism of `X` between
points of the range of `fo` is some `fm a`. -/
structure PieceEmbedding (X₀ : EpGroupoid Obj₀ Mor₀) (X : EpGroupoid Obj Mor) where
  fo : Obj₀ → Obj
  fm : Mor₀ → Mor
  go : Obj → Obj₀
  go_fo : ∀ y, go (fo y) = y
  isOpenMap_fo : IsOpenMap fo
  isScSmoothMap_fo : X₀.PObj.IsScSmoothMap X.PObj fo
  isScSmoothOn_go : X.PObj.IsScSmoothOn X₀.PObj go (range fo)
  isScSmoothMap_fm : X₀.PMor.IsScSmoothMap X.PMor fm
  src_fm : ∀ a, X.src (fm a) = fo (X₀.src a)
  tgt_fm : ∀ a, X.tgt (fm a) = fo (X₀.tgt a)
  fm_comp : ∀ a b, X₀.src a = X₀.tgt b → fm (X₀.comp a b) = X.comp (fm a) (fm b)
  injective_fm : Injective fm
  exists_fm : ∀ h : Mor, X.src h ∈ range fo → X.tgt h ∈ range fo → ∃ a, fm a = h

namespace PieceEmbedding

variable {X₀ : EpGroupoid Obj₀ Mor₀} {X : EpGroupoid Obj Mor} (F : PieceEmbedding X₀ X)

theorem injective_fo : Injective F.fo := fun y y' h => by
  rw [← F.go_fo y, h, F.go_fo]

theorem continuous_fo : Continuous F.fo := continuousOn_univ.1 F.isScSmoothMap_fo.continuousOn

theorem isOpen_range : IsOpen (range F.fo) := by
  have := F.isOpenMap_fo univ isOpen_univ
  rwa [image_univ] at this

/-- `fo` is an sc-diffeomorphism from any open `U₀` onto `fo(U₀)`, with inverse `go`. -/
theorem isScDiffeoOn_fo {U₀ : Set Obj₀} (hU₀ : IsOpen U₀) :
    X₀.PObj.IsScDiffeoOn X.PObj F.fo F.go U₀ (F.fo '' U₀) where
  isScSmoothOn := F.isScSmoothMap_fo.mono hU₀ (subset_univ _)
  isScSmoothOn_inv := F.isScSmoothOn_go.mono (F.isOpenMap_fo U₀ hU₀) (image_subset_range _ _)
  mapsTo y hy := ⟨y, hy, rfl⟩
  mapsTo_inv := by
    rintro _ ⟨y, hy, rfl⟩
    rw [F.go_fo]; exact hy
  left_inv y _ := F.go_fo y
  right_inv := by
    rintro _ ⟨y, -, rfl⟩
    rw [F.go_fo]

variable {x₀ : Obj₀}

/-- `g ↦ fm g`, `G_{x₀} → G_{fo x₀}`. -/
def isotropyHom (x₀ : Obj₀) : X₀.Isotropy x₀ →* X.Isotropy (F.fo x₀) :=
  MonoidHom.mk' (fun g => ⟨F.fm g.val, (F.src_fm _).trans (congrArg F.fo g.src_val),
      (F.tgt_fm _).trans (congrArg F.fo g.tgt_val)⟩)
    fun g h => GroupoidStr.Isotropy.ext
      (F.fm_comp _ _ (g.src_val.trans h.tgt_val.symm))

@[simp] theorem isotropyHom_val (g : X₀.Isotropy x₀) : (F.isotropyHom x₀ g).val = F.fm g.val :=
  rfl

theorem bijective_isotropyHom (x₀ : Obj₀) : Bijective (F.isotropyHom x₀) := by
  refine ⟨fun g h e => GroupoidStr.Isotropy.ext (F.injective_fm (congrArg GroupoidStr.Isotropy.val e)),
    fun k => ?_⟩
  obtain ⟨a, ha⟩ := F.exists_fm k.val (by rw [k.src_val]; exact mem_range_self _)
    (by rw [k.tgt_val]; exact mem_range_self _)
  have hs : X₀.src a = x₀ := F.injective_fo (by rw [← F.src_fm, ha, k.src_val])
  have ht : X₀.tgt a = x₀ := F.injective_fo (by rw [← F.tgt_fm, ha, k.tgt_val])
  exact ⟨⟨a, hs, ht⟩, GroupoidStr.Isotropy.ext ha⟩

/-- **`G_{x₀} ≅ G_{fo x₀}`**. -/
def isotropyEquiv (x₀ : Obj₀) : X₀.Isotropy x₀ ≃* X.Isotropy (F.fo x₀) :=
  MulEquiv.ofBijective (F.isotropyHom x₀) (F.bijective_isotropyHom x₀)

@[simp] theorem isotropyEquiv_val (g : X₀.Isotropy x₀) :
    (F.isotropyEquiv x₀ g).val = F.fm g.val := rfl

theorem fm_isotropyEquiv_symm (k : X.Isotropy (F.fo x₀)) :
    F.fm ((F.isotropyEquiv x₀).symm k).val = k.val := by
  have := congrArg GroupoidStr.Isotropy.val ((F.isotropyEquiv x₀).apply_symm_apply k)
  rwa [isotropyEquiv_val] at this

/-- **The natural representation carried along `F`**: on `fo(U₀)`,
`Φ(g)(z) = fo(Φ₀(g')(go z))` and `Γ(g, z) = fm(Γ₀(g', go z))`, `g'` the element of `G_{x₀}`
with `fm g' = g`. -/
def naturalRep (R₀ : X₀.NaturalRep x₀) : X.NaturalRep (F.fo x₀) where
  U := F.fo '' R₀.U
  isOpen_U := F.isOpenMap_fo _ R₀.isOpen_U
  isConnected_U := R₀.isConnected_U.image _ F.continuous_fo.continuousOn
  mem_U := ⟨x₀, R₀.mem_U, rfl⟩
  Φ k z := F.fo (R₀.Φ ((F.isotropyEquiv x₀).symm k) (F.go z))
  Γ k z := F.fm (R₀.Γ ((F.isotropyEquiv x₀).symm k) (F.go z))
  isScDiffeoOn_Φ k := by
    have h1 := F.isScDiffeoOn_fo R₀.isOpen_U
    have h2 := R₀.isScDiffeoOn_Φ ((F.isotropyEquiv x₀).symm k)
    rw [← map_inv] at h2
    exact h1.comp (h2.comp h1.symm)
  Φ_mul g h := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [F.go_fo, map_mul]
    rw [R₀.Φ_mul _ _ y hy]
  isScSmoothOn_Γ k := by
    have h1 := F.isScDiffeoOn_fo R₀.isOpen_U
    refine MPolyfold.IsScSmoothOn.comp F.isScSmoothMap_fm ?_ (mapsTo_univ _ _)
    exact MPolyfold.IsScSmoothOn.comp (R₀.isScSmoothOn_Γ _) h1.isScSmoothOn_inv h1.mapsTo_inv
  Γ_self k := by
    simp only [F.go_fo]
    rw [R₀.Γ_self]
    exact F.fm_isotropyEquiv_symm k
  src_Γ k := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [F.go_fo]
    rw [F.src_fm, R₀.src_Γ _ y hy]
  tgt_Γ k := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [F.go_fo]
    rw [F.tgt_fm, R₀.tgt_Γ _ y hy]
  existsUnique_Γ h hs ht := by
    obtain ⟨y, hy, hys⟩ := hs
    obtain ⟨y', hy', hyt⟩ := ht
    obtain ⟨a, rfl⟩ := F.exists_fm h ⟨y, hys⟩ ⟨y', hyt⟩
    have has : X₀.src a = y := F.injective_fo (by rw [← F.src_fm, hys])
    have hat : X₀.tgt a = y' := F.injective_fo (by rw [← F.tgt_fm, hyt])
    obtain ⟨g, hg, hgu⟩ := R₀.existsUnique_Γ a (has ▸ hy) (hat ▸ hy')
    refine ⟨F.isotropyEquiv x₀ g, ?_, fun k hk => ?_⟩
    · simp only [F.src_fm, F.go_fo, MulEquiv.symm_apply_apply]
      rw [hg]
    · simp only [F.src_fm, F.go_fo] at hk
      have := hgu _ (F.injective_fm hk)
      rw [← this, MulEquiv.apply_symm_apply]

@[simp] theorem naturalRep_U (R₀ : X₀.NaturalRep x₀) : (F.naturalRep R₀).U = F.fo '' R₀.U := rfl

theorem naturalRep_Φ_fo (R₀ : X₀.NaturalRep x₀) (k : X.Isotropy (F.fo x₀)) (y : Obj₀) :
    (F.naturalRep R₀).Φ k (F.fo y) = F.fo (R₀.Φ ((F.isotropyEquiv x₀).symm k) y) := by
  change F.fo (R₀.Φ _ (F.go (F.fo y))) = _
  rw [F.go_fo]

end PieceEmbedding

end EpGroupoid

end Polyfold
