import Polyfold.Chapter10.StrongBundleLocalFamilies

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapters 8 and 10: **Definition 8.4.2** (§8.4, p. 382) and **Proposition 10.4.7**
(§10.4, pp. 501–502), both new in the 2021 edition.  Numbers and pages are the 2021 text's.

# The local regularity property of a strong bundle: the two readings and a germ form

## The text, paraphrased

(Definition 8.4.2, p. 382) A strong bundle `(P : W → X, μ)` over an ep-groupoid has the local
regularity property if every object `x` has arbitrarily small open neighbourhoods `U(x)` with
the natural representation of `G_x` such that every strong bundle isomorphism
`B : W|U(x) → W|U(x)` with `|B(w)| = |w|` is `w ↦ g ∗ w` for some `g ∈ G_x`.

## The two readings

* `EpStrongBundle.IsLRLocal` (`LocalizationLRBundleBase.lean`): `B` is a strong bundle
  isomorphism of `W|U(x)`, with no condition off `W|U(x)`.  This is what the text says: its `B`
  has domain `W|U(x)`, as the `β : U(x) → U(x)` of Definition 7.4.19 (p. 337) has domain `U(x)`,
  and the proofs of Propositions 8.4.3 (p. 382), 10.4.6 and 10.4.7 (pp. 500–502) apply the
  property to maps which are only defined over `U(x)`.
* `EpStrongBundle.IsLR` (`Chapter8/TangentZhou.lean`): the same asked only of those `B` which
  are restrictions of strong bundle maps defined on all of `W`.  It follows from `IsLRLocal`
  (`IsLRLocal.isLR`).

We do not prove `IsLR → IsLRLocal`, and we have no example separating the two.  What `IsLR` gives
is a statement on germs, provided strong bundle isomorphisms of `W|U` can be cut off:

* `StrongBundle.HasLocalIsoExtension`: near every point, a strong bundle isomorphism of `W|U`
  agrees over a smaller neighbourhood `V` (depending on `U` only) with a strong bundle map of
  `W`.  It holds when the base admits sc-smooth bump functions
  (`MPolyfold.AdmitsBumpFunctions.hasLocalIsoExtension`, `Chapter10/StrongBundleCutOff`).
* `EpStrongBundle.IsLRGerm`: inside every open `O ∋ x` there are natural representations
  `U₀(x) ⊆ U(x)` such that every strong bundle isomorphism `B` of `W|U(x)` with `|B(w)| = |w|`
  is `g ∗ ·` **over `U₀(x)`**.
* `IsLRLocal.isLRGerm`, and **`IsLR.isLRGerm`**: `IsLR` and `HasLocalIsoExtension` give
  `IsLRGerm`.  The step from `U₀(x)` to `U(x)` is what is missing for `IsLRLocal`: we do not
  know that a strong bundle isomorphism of `W|U(x)` which is `g ∗ ·` over `U₀(x)` is `g ∗ ·`
  over `U(x)`.
* **`EpStrongBundle.proposition_10_4_7_of_isLRGerm`**: Proposition 10.4.7 needs only the germ
  form (its conclusion is local).  So every consequence of Proposition 10.4.7 holds under
  `IsLR` and `HasLocalIsoExtension` of the target.
* `NaturalRep.tgt_mem_of_subset`: for natural representations `U₀(x) ⊆ U(x)`, a morphism from a
  point of `U₀(x)` to a point of `U(x)` ends in `U₀(x)` (both actions of `G_x` exhaust the
  morphisms, and `G_x` is finite).

Witness: `IsLRGerm` holds for every strong bundle over a trivial ep-groupoid
(`isLRGerm_trivial`), and `proposition_10_4_7_of_isLRGerm_hypotheses`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Natural representations inside one another -/

namespace EpGroupoid.NaturalRep

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor} {x : Obj}

/-- **Natural representations `U₀(x) ⊆ U(x)` have the same orbits**: a morphism from a point of
`U₀(x)` to a point of `U(x)` ends in `U₀(x)`.  The morphisms `Γ₀(g, y)`, `g ∈ G_x`, from
`y ∈ U₀(x)` are pairwise different morphisms between points of `U(x)`, so they are all the
`Γ(g, y)`. -/
theorem tgt_mem_of_subset (R R₀ : X.NaturalRep x) (h : R₀.U ⊆ R.U) {ψ : Mor}
    (hs : X.src ψ ∈ R₀.U) (ht : X.tgt ψ ∈ R.U) : X.tgt ψ ∈ R₀.U := by
  set y := X.src ψ with hy
  have hsrc : ∀ g, X.src (R₀.Γ g y) ∈ R.U := fun g => by rw [R₀.src_Γ g y hs]; exact h hs
  have htgt : ∀ g, X.tgt (R₀.Γ g y) ∈ R.U := fun g => by
    rw [R₀.tgt_Γ g y hs]; exact h (R₀.mapsTo_Φ g hs)
  choose σ hσ _ using fun g => R.existsUnique_Γ (R₀.Γ g y) (hsrc g) (htgt g)
  have hσ' : ∀ g, R.Γ (σ g) y = R₀.Γ g y := fun g => by
    have := hσ g
    rwa [R₀.src_Γ g y hs] at this
  have hinj : Injective σ := fun g₁ g₂ h12 => by
    have h1 : R₀.Γ g₁ y = R₀.Γ g₂ y := by rw [← hσ' g₁, ← hσ' g₂, h12]
    have hs' : X.src (R₀.Γ g₁ y) ∈ R₀.U := by rw [R₀.src_Γ g₁ y hs]; exact hs
    have ht' : X.tgt (R₀.Γ g₁ y) ∈ R₀.U := by
      rw [R₀.tgt_Γ g₁ y hs]; exact R₀.mapsTo_Φ g₁ hs
    obtain ⟨g, -, hu⟩ := R₀.existsUnique_Γ (R₀.Γ g₁ y) hs' ht'
    rw [R₀.src_Γ g₁ y hs] at hu
    exact (hu g₁ rfl).trans (hu g₂ h1.symm).symm
  obtain ⟨g', hg', -⟩ := R.existsUnique_Γ ψ (h hs) ht
  obtain ⟨g, rfl⟩ := (Finite.injective_iff_surjective.1 hinj) g'
  rw [← hy, hσ' g] at hg'
  rw [← hg', R₀.tgt_Γ g y hs]
  exact R₀.mapsTo_Φ g hs

end EpGroupoid.NaturalRep

/-! ### Cutting off strong bundle isomorphisms of `W|U` -/

section Extension

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- **Strong bundle isomorphisms of `Y|U` can be cut off near every point**: every `x` has
arbitrarily small open neighbourhoods `N` such that for every open `U` with `x ∈ U ⊆ N` there is
an open `V`, `x ∈ V ⊆ U`, over which every strong bundle isomorphism `Φ : Y|U → Y|U`
(`StrongBundle.IsLocalIsoOn`) agrees with a strong bundle map of `Y`. -/
def StrongBundle.HasLocalIsoExtension (B : StrongBundle PX P) : Prop :=
  ∀ (x : X) (O : Set X), IsOpen O → x ∈ O → ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ N ⊆ O ∧
    ∀ U : Set X, IsOpen U → x ∈ U → U ⊆ N → ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∀ (β : X → X) (Φ : Y → Y), B.IsLocalIsoOn β Φ U →
        ∃ (β' : X → X) (Φ' : Y → Y), B.IsStrongBundleMap B β' Φ' ∧ ∀ w, P w ∈ V → Φ' w = Φ w

end Extension

/-! ### The germ form of Definition 8.4.2 -/

section Germ

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

/-- **2021 Definition 8.4.2, p. 382, on germs**: inside every open `O ∋ x` there are natural
representations `U₀(x) ⊆ U(x)` such that every strong bundle isomorphism `Φ : W|U(x) → W|U(x)`
(`StrongBundle.IsLocalIsoOn`) with `|Φ(w)| = |w|` is `w ↦ g ∗ w` over `U₀(x)` for some
`g ∈ G_x`.  It follows from `IsLRLocal` (`IsLRLocal.isLRGerm`, with `U₀(x) = U(x)`), and from
`IsLR` when strong bundle isomorphisms of `W|U` can be cut off (`IsLR.isLRGerm`). -/
def IsLRGerm (E : EpStrongBundle X B) : Prop :=
  ∀ (x : Obj) (O : Set Obj), IsOpen O → x ∈ O → ∃ R : X.NaturalRep x, R.U ⊆ O ∧
    ∃ R₀ : X.NaturalRep x, R₀.U ⊆ R.U ∧
      ∀ (β : Obj → Obj) (Φ : W → W), B.IsLocalIsoOn β Φ R.U →
        (∀ w, P w ∈ R.U → E.toGroupoidStr.π (Φ w) = E.toGroupoidStr.π w) →
        ∃ g : X.Isotropy x, ∀ w (hw : P w ∈ R₀.U), Φ w = E.natLift R₀ g w hw

/-- Definition 8.4.2 read with strong bundle isomorphisms of `W|U(x)` implies its germ form. -/
theorem IsLRLocal.isLRGerm {E : EpStrongBundle X B} (h : E.IsLRLocal) : E.IsLRGerm :=
  fun x O hO hxO =>
    let ⟨R, hRO, hR⟩ := h x O hO hxO
    ⟨R, hRO, R, Subset.rfl, hR⟩

variable {E : EpStrongBundle X B}

/-- If `|Φ(w)| = |w|` for a `Φ` with `P(Φ(w)) = β(P(w))`, there is a morphism
`P(w) → β(P(w))`. -/
theorem exists_mor_base_of_π_eq {Φ : W → W} {w : W} {z : Obj} (hz : P (Φ w) = z)
    (h : E.toGroupoidStr.π (Φ w) = E.toGroupoidStr.π w) :
    ∃ ψ : Mor, X.src ψ = P w ∧ X.tgt ψ = z := by
  obtain ⟨q, hqs, hqt⟩ := (GroupoidStr.π_eq_π_iff _).1 h.symm
  obtain ⟨⟨ψ, w'⟩, hq⟩ := q
  have hqs' : w' = w := hqs
  subst hqs'
  exact ⟨ψ, hq.symm, (E.P_μ _).symm.trans ((congrArg P hqt).trans hz)⟩

/-- **A strong bundle isomorphism of `W|U(x)` with `|Φ(w)| = |w|` restricts to one of
`W|U₀(x)`** for natural representations `U₀(x) ⊆ U(x)`: the base map and its inverse preserve
`U₀(x)`. -/
theorem mapsTo_of_π_eq {x : Obj} (R R₀ : X.NaturalRep x) (h : R₀.U ⊆ R.U) {β : Obj → Obj}
    {Φ : W → W} (hΦ : B.IsLocalIsoOn β Φ R.U)
    (hπ : ∀ w, P w ∈ R.U → E.toGroupoidStr.π (Φ w) = E.toGroupoidStr.π w) {β' : Obj → Obj}
    (hβ : X.PObj.IsScDiffeoOn X.PObj β β' R.U R.U) :
    MapsTo β R₀.U R₀.U ∧ MapsTo β' R₀.U R₀.U := by
  have key : ∀ y ∈ R.U, ∃ ψ : Mor, X.src ψ = y ∧ X.tgt ψ = β y := fun y hy => by
    have hw : P (fiberZero P y) ∈ R.U := by rw [isSection_fiberZero (P := P) y]; exact hy
    obtain ⟨ψ, hs, ht⟩ := exists_mor_base_of_π_eq (E := E) (hΦ.covers hw) (hπ _ hw)
    rw [isSection_fiberZero (P := P) y] at hs ht
    exact ⟨ψ, hs, ht⟩
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨ψ, hs, ht⟩ := key y (h hy)
    rw [← ht]
    exact R.tgt_mem_of_subset R₀ h (hs ▸ hy) (ht ▸ hβ.mapsTo (h hy))
  · have hy' : β' y ∈ R.U := hβ.mapsTo_inv (h hy)
    obtain ⟨ψ, hs, ht⟩ := key (β' y) hy'
    rw [hβ.right_inv y (h hy)] at ht
    have h1 := R.tgt_mem_of_subset R₀ h (ψ := X.inv ψ) (by rw [X.src_inv, ht]; exact hy)
      (by rw [X.tgt_inv, hs]; exact hy')
    rwa [X.tgt_inv, hs] at h1

/-- **The formal `IsLR` gives the germ form of Definition 8.4.2** when strong bundle
isomorphisms of `W|U` can be cut off (`StrongBundle.HasLocalIsoExtension`): take `U(x)` in a
neighbourhood where the cut-off is possible, `V ⊆ U(x)` where the cut-off map agrees with the
given one, and `U₀(x) ⊆ V` from `IsLR`.  A strong bundle isomorphism `Φ` of `W|U(x)` with
`|Φ(w)| = |w|` restricts to one of `W|U₀(x)` (`mapsTo_of_π_eq`), which is the restriction of a
strong bundle map of `W`. -/
theorem IsLR.isLRGerm (hE : E.IsLR) (hext : B.HasLocalIsoExtension) : E.IsLRGerm := by
  intro x O hO hxO
  obtain ⟨N, hNo, hxN, hNO, hN⟩ := hext x O hO hxO
  obtain ⟨R, hRN⟩ := X.theorem_7_1_13 x hNo hxN
  obtain ⟨V, hVo, hxV, hVR, hV⟩ := hN R.U R.isOpen_U R.mem_U hRN
  obtain ⟨R₀, hR₀V, hR₀⟩ := hE x V hVo hxV
  refine ⟨R, hRN.trans hNO, R₀, hR₀V.trans hVR, fun β Φ hΦ hπ => ?_⟩
  have hsub : R₀.U ⊆ R.U := hR₀V.trans hVR
  obtain ⟨βe, Φe, hΦe, hagree⟩ := hV β Φ hΦ
  obtain ⟨β', hβ⟩ := hΦ.isScDiffeoOn_base
  obtain ⟨Ψ, hΨ⟩ := hΦ.isScDiffeoOn_zero
  obtain ⟨Φ₁, Ψ₁, hΦ₁, hΨ₁⟩ := hΦ.isScDiffeoOn_one
  obtain ⟨hm, hm'⟩ := mapsTo_of_π_eq (E := E) R R₀ hsub hΦ hπ hβ
  have hβeq : ∀ y ∈ R₀.U, βe y = β y := fun y hy => by
    have hw : P (fiberZero P y) ∈ R.U := by rw [isSection_fiberZero (P := P) y]; exact hsub hy
    have hw' : P (fiberZero P y) ∈ V := by rw [isSection_fiberZero (P := P) y]; exact hR₀V hy
    have h1 := hΦe.covers (fiberZero P y)
    rw [hagree _ hw', hΦ.covers hw, isSection_fiberZero (P := P) y] at h1
    exact h1.symm
  -- the three restrictions to `U₀(x)`
  have hb0 : X.PObj.IsScDiffeoOn X.PObj β β' R₀.U R₀.U :=
    ⟨hβ.isScSmoothOn.mono R₀.isOpen_U hsub, hβ.isScSmoothOn_inv.mono R₀.isOpen_U hsub, hm, hm',
      fun y hy => hβ.left_inv y (hsub hy), fun y hy => hβ.right_inv y (hsub hy)⟩
  have hPo : IsOpen (P ⁻¹' R₀.U) := R₀.isOpen_U.preimage B.continuous
  have hPsub : P ⁻¹' R₀.U ⊆ P ⁻¹' R.U := fun w hw => hsub hw
  have hmΦ : MapsTo Φ (P ⁻¹' R₀.U) (P ⁻¹' R₀.U) := fun w hw => by
    change P (Φ w) ∈ R₀.U
    rw [hΦ.covers (hsub hw)]; exact hm hw
  have hmΨ : MapsTo Ψ (P ⁻¹' R₀.U) (P ⁻¹' R₀.U) := fun w hw => by
    have h1 : P (Ψ w) ∈ R.U := hΨ.mapsTo_inv (hPsub hw)
    have h2 : β (P (Ψ w)) = P w := by rw [← hΦ.covers h1, hΨ.right_inv w (hPsub hw)]
    change P (Ψ w) ∈ R₀.U
    rw [← hβ.left_inv _ h1, h2]
    exact hm' hw
  have hz0 : B.toMPolyfold0.IsScDiffeoOn B.toMPolyfold0 Φ Ψ (P ⁻¹' R₀.U) (P ⁻¹' R₀.U) :=
    ⟨hΨ.isScSmoothOn.mono hPo hPsub, hΨ.isScSmoothOn_inv.mono hPo hPsub, hmΦ, hmΨ,
      fun w hw => hΨ.left_inv w (hPsub hw), fun w hw => hΨ.right_inv w (hPsub hw)⟩
  have hPo1 : IsOpen ((P ∘ B.oneVal) ⁻¹' R₀.U) :=
    R₀.isOpen_U.preimage (B.continuous.comp B.continuous_oneVal)
  have hPsub1 : (P ∘ B.oneVal) ⁻¹' R₀.U ⊆ (P ∘ B.oneVal) ⁻¹' R.U := fun w hw => hsub hw
  have hΨ₁v : ∀ y, P (B.oneVal y) ∈ R.U → B.oneVal (Ψ₁ y) = Ψ (B.oneVal y) := fun y hy => by
    have h1 : P (B.oneVal (Ψ₁ y)) ∈ R.U := hΨ₁.mapsTo_inv hy
    have h2 := congrArg B.oneVal (hΨ₁.right_inv y hy)
    rw [hΦ₁ _ h1] at h2
    rw [← hΨ.left_inv _ h1, h2]
  have ho0 : B.toMPolyfold1.IsScDiffeoOn B.toMPolyfold1 Φ₁ Ψ₁ ((P ∘ B.oneVal) ⁻¹' R₀.U)
      ((P ∘ B.oneVal) ⁻¹' R₀.U) :=
    StrongBundle.isScDiffeoOn_one_of hz0 (fun y hy => hΦ₁ y (hsub hy))
      (fun y hy => hΨ₁v y (hsub hy)) (hΨ₁.isScSmoothOn.mono hPo1 hPsub1)
      (hΨ₁.isScSmoothOn_inv.mono hPo1 hPsub1)
  -- the cut-off map is a strong bundle isomorphism of `W|U₀(x)`
  have hiso : B.IsStrongBundleIsoOn B hΦe R₀.U R₀.U :=
    { isScDiffeoOn_base := ⟨β', hb0.congr_left fun y hy => (hβeq y hy).symm⟩
      isScDiffeoOn_zero := ⟨Ψ, hz0.congr_left fun w hw => (hagree w (hR₀V hw)).symm⟩
      isScDiffeoOn_one := ⟨Ψ₁, ho0.congr_left fun y hy => B.oneVal_injective (by
        rw [StrongBundle.oneVal_oneRestrict, hΦ₁ y (hsub hy)]
        exact (hagree _ (hR₀V hy)).symm)⟩ }
  obtain ⟨g, hg⟩ := hR₀ βe Φe hΦe hiso fun w hw => by
    rw [hagree w (hR₀V hw)]; exact hπ w (hsub hw)
  exact ⟨g, fun w hw => by rw [← hagree w (hR₀V hw)]; exact hg w hw⟩

end EpStrongBundle

end Germ

/-! ### Proposition 10.4.7 from the germ form -/

section Family

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {Y : EpGroupoid Obj' Mor'}
  {W' : Type u} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle Y.PObj P'}
  [ParacompactSpace (pullbackSpace P' Y.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle Y B'}

namespace EpStrongBundle

/-- **2021 Proposition 10.4.7, pp. 501–502, from the germ form of Definition 8.4.2** for the
target: if `Φ, Ψ : (P, μ) → (P', ν)` are strong bundle equivalences covering `ϕ, ψ` with
`|Φ| = |Ψ|`, every `x` has natural representations `U(x)` inside any neighbourhood `O`, with an
sc-smooth `U(x) → 𝐘`, `z ↦ α_z : ϕ(z) → ψ(z)`, such that `ν(α_z, Φ(v)) = Ψ(v)` for
`P(v) = z ∈ U(x)`.  The proof is that of `proposition_10_4_7`; the strong bundle isomorphism
`B = H ∘ Φ⁻¹` of `W'|U(ϕ(x))` is `k ∗ ·` over `U₀(ϕ(x))`, and `U(x) ⊆ ϕ⁻¹(U₀(ϕ(x)))`. -/
theorem proposition_10_4_7_of_isLRGerm {ϕ ψ : EpFunctor X Y}
    {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (hΦ : E.IsStrongBundleEquivalence E' ϕ Φ)
    (hΨ : E.IsStrongBundleEquivalence E' ψ Ψ) (hΦΨ : Φ.orbitMap = Ψ.orbitMap)
    (hE' : E'.IsLRGerm) (x : Obj) {O : Set Obj} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ R : X.NaturalRep x, R.U ⊆ O ∧ ∃ α : Obj → Mor', X.PObj.IsScSmoothOn Y.PMor α R.U ∧
      ∀ z ∈ R.U, Y.src (α z) = ϕ.obj z ∧ Y.tgt (α z) = ψ.obj z ∧
        ∀ v, P v = z → E'.lrAct (α z) (Φ.obj v) = Ψ.obj v := by
  have hπb := π_base_eq_of_orbitMap_eq hΦ.isStrongBundleFunctor hΨ.isStrongBundleFunctor hΦΨ
  -- the chart `Q = ψ̂₀ ∘ ψ` along `ψ₀ : ψ(x) → ϕ(x)`, and the transport `H = H_ψ̂₀ ∘ Ψ`
  obtain ⟨ψ₀, hs₀, ht₀⟩ := Y.π_eq_π_iff.1 (hπb x).symm
  obtain ⟨T, -⟩ := EpFunctor.exists_transportChart hΨ.isEquivalence_base.isLocalScDiffeo_obj
    hs₀ ht₀
  obtain ⟨S, hSo, hxS, hSW, HG', hHG⟩ := hΨ.exists_transport T
  -- `Φ` near `x`
  obtain ⟨UF, UF', hxF, hiF⟩ := hΦ.isLocalStrongBundleIso_obj x
  obtain ⟨gF, ΨF, hF⟩ := hiF.exists_isLocalIso₂
  have hU₀o : IsOpen (UF ∩ S ∩ O) := (hF.base.isOpen_source.inter hSo).inter hO
  have hxU₀ : x ∈ UF ∩ S ∩ O := ⟨⟨hxF, hxS⟩, hxO⟩
  have hF₀ := hF.restrict hU₀o fun u hu => hu.1.1
  have hG₀ := hHG.restrict_image hU₀o fun u hu => hu.1.2
  -- `B = H ∘ Φ⁻¹` on `D = U_F' ∩ g_F⁻¹(U₀)`, covering `γ = Q ∘ g_F`
  have hC := hG₀.comp hF₀.symm
  have hDo : IsOpen (UF' ∩ gF ⁻¹' (UF ∩ S ∩ O)) := hF₀.base.isOpen_target
  have hxD : ϕ.obj x ∈ UF' ∩ gF ⁻¹' (UF ∩ S ∩ O) :=
    ⟨hF.base.mapsTo hxF, by rw [mem_preimage, hF.base.left_inv x hxF]; exact hxU₀⟩
  obtain ⟨R', hR'D, R₀, -, hR'⟩ := hE' _ _ hDo hxD
  have hCR := hC.restrict_image R'.isOpen_U hR'D
  have hγx : (T.Q ∘ gF) (ϕ.obj x) = ϕ.obj x := by
    rw [Function.comp_apply, hF.base.left_inv x hxF, T.Q_self]
  have hγπ : ∀ y ∈ R'.U, Y.π ((T.Q ∘ gF) y) = Y.π y := fun y hy => by
    have hy' := hR'D hy
    rw [Function.comp_apply, T.π_Q (hSW hy'.2.1.2), ← hπb, hF.base.right_inv y hy'.1]
  obtain ⟨himg, -⟩ := Y.lemma_7_4_20 R' hCR.base hγx hγπ
  rw [himg] at hCR
  -- `|B(w)| = |w|`
  have hπB : ∀ w, P' w ∈ R'.U → E'.toGroupoidStr.π ((fun v => E'.lrAct (T.ψ (P v)) (Ψ.obj v))
      (ΨF w)) = E'.toGroupoidStr.π w := fun w hw => by
    have hw' := hR'D hw
    have h1 : P (ΨF w) ∈ UF ∩ S ∩ O := hF₀.symm.mapsTo hw'
    rw [π_lrAct (by rw [hΨ.covers, T.src_ψ _ (hSW h1.1.2)]), ← π_obj_eq_of_orbitMap_eq hΦΨ,
      hF.right_inv hw'.1]
  -- Definition 8.4.2: `B = k ∗ ·`
  obtain ⟨k, hk⟩ := hR' _ _ hCR.isLocalIsoOn hπB
  -- the family `α_z = ψ_z⁻¹ ∘ Γ(k, ϕ(z))` on `V₀ = U₀ ∩ ϕ⁻¹(U(ϕ(x)))`
  have hV₀o : IsOpen ((UF ∩ S ∩ O) ∩ ϕ.obj ⁻¹' R₀.U) :=
    (hF.base.isScSmoothOn.continuousOn.mono fun u hu => hu.1.1).isOpen_inter_preimage hU₀o
      R₀.isOpen_U
  have hkey : ∀ z ∈ (UF ∩ S ∩ O) ∩ ϕ.obj ⁻¹' R₀.U, ∀ v, P v = z →
      E'.lrAct (T.ψ z) (Ψ.obj v) = E'.lrAct (R₀.Γ k (ϕ.obj z)) (Φ.obj v) := by
    intro z hz v hv
    have hvU : P v ∈ UF := hv ▸ hz.1.1.1
    have hΦv : P' (Φ.obj v) ∈ R₀.U := by rw [hΦ.covers, hv]; exact hz.2
    have h1 := hk (Φ.obj v) hΦv
    simp only [Function.comp_apply, hF.left_inv hvU] at h1
    rw [natLift_eq_lrAct, hΦ.covers, hv] at h1
    exact h1
  have hQz : ∀ z ∈ (UF ∩ S ∩ O) ∩ ϕ.obj ⁻¹' R₀.U, R₀.Φ k (ϕ.obj z) = T.Q z := fun z hz => by
    have h1 := congrArg P' (hkey z hz (fiberZero P z) (isSection_fiberZero (P := P) z))
    rw [P_lrAct (E := E') (by
        rw [hΨ.covers, isSection_fiberZero (P := P) z, T.src_ψ _ (hSW hz.1.1.2)]),
      T.tgt_ψ _ (hSW hz.1.1.2),
      P_lrAct (E := E') (by rw [hΦ.covers, isSection_fiberZero (P := P) z, R₀.src_Γ k _ hz.2]),
      R₀.tgt_Γ k _ hz.2] at h1
    exact h1.symm
  have hc : ∀ z ∈ (UF ∩ S ∩ O) ∩ ϕ.obj ⁻¹' R₀.U,
      Y.src (Y.inv (T.ψ z)) = Y.tgt (R₀.Γ k (ϕ.obj z)) := fun z hz => by
    rw [Y.src_inv, T.tgt_ψ z (hSW hz.1.1.2), R₀.tgt_Γ k _ hz.2, hQz z hz]
  have hαs : X.PObj.IsScSmoothOn Y.PMor (fun z => Y.comp (Y.inv (T.ψ z)) (R₀.Γ k (ϕ.obj z)))
      ((UF ∩ S ∩ O) ∩ ϕ.obj ⁻¹' R₀.U) :=
    Y.isScSmoothOn_comp_of
      (MPolyfold.IsScSmoothOn.comp Y.isScSmoothMap_inv
        (T.isScSmoothOn_ψ.mono hV₀o fun z hz => hSW hz.1.1.2) (mapsTo_univ _ _))
      (MPolyfold.IsScSmoothOn.comp (R₀.isScSmoothOn_Γ k)
        (ϕ.isScSmoothMap_obj.mono hV₀o (subset_univ _)) fun z hz => hz.2) hc
  obtain ⟨R, hRV⟩ := X.theorem_7_1_13 x hV₀o ⟨hxU₀, R₀.mem_U⟩
  refine ⟨R, fun u hu => (hRV hu).1.2, _, hαs.mono R.isOpen_U hRV, fun z hz => ?_⟩
  have hz' := hRV hz
  refine ⟨?_, ?_, fun v hv => ?_⟩
  · rw [Y.src_comp _ _ (hc z hz'), R₀.src_Γ k _ hz'.2]
  · rw [Y.tgt_comp _ _ (hc z hz'), Y.tgt_inv, T.src_ψ z (hSW hz'.1.1.2)]
  · have hΦv : P' (Φ.obj v) = Y.src (R₀.Γ k (ϕ.obj z)) := by
      rw [hΦ.covers, hv, R₀.src_Γ k _ hz'.2]
    have hΨv : P' (Ψ.obj v) = Y.src (T.ψ z) := by
      rw [hΨ.covers, hv, T.src_ψ z (hSW hz'.1.1.2)]
    rw [lrAct_comp hΦv (hc z hz'), ← hkey z hz' v hv, lrAct_inv_lrAct hΨv]

end EpStrongBundle

end Family

/-! ### Witnesses -/

section Witness

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Z}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- **Witness** for `EpStrongBundle.IsLRGerm`: every strong bundle over a trivial ep-groupoid
has it. -/
theorem EpStrongBundle.isLRGerm_trivial (B : StrongBundle PZ P) :
    (EpStrongBundle.trivial B).IsLRGerm :=
  (EpStrongBundle.isLRLocal_trivial B).isLRGerm

end Witness

namespace LocalRegularityGermExamples

open StrongBundleEquivalenceExamples StrongBundleLocalizationExamples

/-- **Witness** for `EpStrongBundle.proposition_10_4_7_of_isLRGerm`: on `ℝⁿ × ℝᵏ → ℝⁿ` over the
trivial ep-groupoid of `ℝⁿ` (`epSEP n k`), the bundle has the germ form of the local regularity
property, and `Φ = Ψ = 1` is a strong bundle equivalence with `|Φ| = |Ψ|`. -/
theorem proposition_10_4_7_of_isLRGerm_hypotheses (n k : ℕ) :
    (epSEP n k).E.IsLRGerm ∧
      (epSEP n k).E.IsStrongBundleEquivalence (epSEP n k).E (EpFunctor.id _) (EpFunctor.id _) ∧
      (EpFunctor.id (epSEP n k).E.toEpGroupoid).orbitMap =
        (EpFunctor.id (epSEP n k).E.toEpGroupoid).orbitMap :=
  ⟨EpStrongBundle.isLRGerm_trivial _, EpStrongBundle.isStrongBundleEquivalence_id _, rfl⟩

end LocalRegularityGermExamples

end Polyfold
