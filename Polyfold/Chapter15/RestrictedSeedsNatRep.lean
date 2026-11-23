import Polyfold.Chapter15.RestrictedBundleCompactness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Theorem 7.1.13 (p. 233),
Definition 7.5.8 (p. 271), Proposition 7.1.22 (p. 250) and Corollary 15.3.10 (p. 699).

# Natural representations along an open saturated inclusion

For an ep-groupoid `X`, an open saturated set `W` of objects and an ep-groupoid `X'` whose object
space is carried sc-diffeomorphically onto `W` and whose morphism space is carried
sc-diffeomorphically onto the morphisms between points of `W`, a natural representation of `X`
with domain in `W` is one of `X'`, and the properness property (Definition 7.5.8) is carried along.
This is applied to `[0, 1] × (X|V) → [0, 1] × X` for `V` open and saturated.

## What is formalized

* `EpGroupoid.OpenInclusion X' X W`: the data `ϕ, ϕm` with inverses `ψ, ψm` (defined on all of
  the object and morphism space of `X`, with arbitrary values off `W`).
* `OpenInclusion.iso`, `OpenInclusion.isoEquiv`: the isomorphism of the isotropy groups.
* `OpenInclusion.pullRep`: the natural representation of `X'` on `ϕ⁻¹(U)`, with
  `ϕ ∘ Φ'(g') = Φ(ι g') ∘ ϕ` (`OpenInclusion.ϕ_pullRep_Φ`).
* `OpenInclusion.hasPropernessProperty_preimage`, `OpenInclusion.π_eq_π_iff`,
  `OpenInclusion.isSaturated_preimage`.
* `SBLocalization.cubeRestrInclusion`: the inclusion `[0, 1] × (X|V) → [0, 1] × X`.
* **`SBLocalization.exists_naturalRep_cubeRestr`**, `SBLocalization.cubeRestrInclusion_π_eq_π_iff`,
  `SBLocalization.isSaturated_preimage_cubeRestr`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {O M : Type u} [TopologicalSpace O] [T2Space O] [ParacompactSpace O]
  [TopologicalSpace M] [T2Space M] [ParacompactSpace M]
  {O' M' : Type u} [TopologicalSpace O'] [T2Space O'] [ParacompactSpace O']
  [TopologicalSpace M'] [T2Space M'] [ParacompactSpace M']

/-- An sc-smooth functor `X' → X` which is an sc-diffeomorphism of the object space onto the open
saturated set `W` and of the morphism space onto the morphisms between points of `W`
(the inclusion of the ep-subgroupoid on an open saturated set, Proposition 7.1.22, p. 250, and
its products with a fixed M-polyfold). -/
structure OpenInclusion (X' : EpGroupoid O' M') (X : EpGroupoid O M) (W : Set O) where
  /-- The map on objects. -/
  ϕ : O' → O
  /-- Its inverse on `W`. -/
  ψ : O → O'
  /-- The map on morphisms. -/
  ϕm : M' → M
  /-- Its inverse on the morphisms between points of `W`. -/
  ψm : M → M'
  src_ϕm : ∀ m, X.src (ϕm m) = ϕ (X'.src m)
  tgt_ϕm : ∀ m, X.tgt (ϕm m) = ϕ (X'.tgt m)
  ϕm_comp : ∀ a b, X'.src a = X'.tgt b → ϕm (X'.comp a b) = X.comp (ϕm a) (ϕm b)
  isSaturated : X.IsSaturated W
  obj : X'.PObj.IsScDiffeoOn X.PObj ϕ ψ univ W
  mor : X'.PMor.IsScDiffeoOn X.PMor ϕm ψm univ (X.morOn W)

namespace OpenInclusion

variable {X' : EpGroupoid O' M'} {X : EpGroupoid O M} {W : Set O} (F : OpenInclusion X' X W)

theorem continuous_ϕ : Continuous F.ϕ := continuousOn_univ.1 F.obj.isScSmoothOn.continuousOn

theorem ϕ_mem (y : O') : F.ϕ y ∈ W := F.obj.mapsTo (mem_univ y)

theorem ψ_ϕ (y : O') : F.ψ (F.ϕ y) = y := F.obj.left_inv y (mem_univ y)

theorem ϕ_ψ {x : O} (hx : x ∈ W) : F.ϕ (F.ψ x) = x := F.obj.right_inv x hx

theorem ψm_ϕm (m : M') : F.ψm (F.ϕm m) = m := F.mor.left_inv m (mem_univ m)

theorem ϕm_ψm {h : M} (hh : h ∈ X.morOn W) : F.ϕm (F.ψm h) = h := F.mor.right_inv h hh

theorem ϕ_injective : Injective F.ϕ := fun a b h => by rw [← F.ψ_ϕ a, h, F.ψ_ϕ]

theorem ϕm_injective : Injective F.ϕm := fun a b h => by rw [← F.ψm_ϕm a, h, F.ψm_ϕm]

include F in
theorem isOpen_W : IsOpen W := F.obj.isScSmoothOn_inv.isOpen

theorem src_ψm {h : M} (hh : h ∈ X.morOn W) : X'.src (F.ψm h) = F.ψ (X.src h) := by
  rw [← F.ψ_ϕ (X'.src (F.ψm h)), ← F.src_ϕm, F.ϕm_ψm hh]

theorem tgt_ψm {h : M} (hh : h ∈ X.morOn W) : X'.tgt (F.ψm h) = F.ψ (X.tgt h) := by
  rw [← F.ψ_ϕ (X'.tgt (F.ψm h)), ← F.tgt_ϕm, F.ϕm_ψm hh]

/-! ### The isotropy groups -/

/-- The map `G_{x'} → G_{ϕ(x')}`. -/
def isoFun {x' : O'} (g : X'.Isotropy x') : X.Isotropy (F.ϕ x') :=
  ⟨F.ϕm g.val, by rw [F.src_ϕm, g.src_val], by rw [F.tgt_ϕm, g.tgt_val]⟩

/-- **The homomorphism `ι : G_{x'} → G_{ϕ(x')}` of the isotropy groups.** -/
def iso {x' : O'} : X'.Isotropy x' →* X.Isotropy (F.ϕ x') :=
  MonoidHom.mk' F.isoFun fun g h => GroupoidStr.Isotropy.ext
    (F.ϕm_comp g.val h.val (g.src_val.trans h.tgt_val.symm))

@[simp] theorem iso_val {x' : O'} (g : X'.Isotropy x') : (F.iso g).val = F.ϕm g.val := rfl

theorem val_mem_morOn {x' : O'} (g : X.Isotropy (F.ϕ x')) : g.val ∈ X.morOn W :=
  ⟨by rw [g.src_val]; exact F.ϕ_mem x', by rw [g.tgt_val]; exact F.ϕ_mem x'⟩

/-- The inverse of `ι`. -/
def isoInv {x' : O'} (g : X.Isotropy (F.ϕ x')) : X'.Isotropy x' :=
  ⟨F.ψm g.val, by rw [F.src_ψm (F.val_mem_morOn g), g.src_val, F.ψ_ϕ],
    by rw [F.tgt_ψm (F.val_mem_morOn g), g.tgt_val, F.ψ_ϕ]⟩

theorem isoInv_iso {x' : O'} (g : X'.Isotropy x') : F.isoInv (F.iso g) = g :=
  GroupoidStr.Isotropy.ext (F.ψm_ϕm g.val)

theorem iso_isoInv {x' : O'} (g : X.Isotropy (F.ϕ x')) : F.iso (F.isoInv g) = g :=
  GroupoidStr.Isotropy.ext (F.ϕm_ψm (F.val_mem_morOn g))

/-- **The isotropy groups of `x'` and of `ϕ(x')` are isomorphic.** -/
def isoEquiv (x' : O') : X'.Isotropy x' ≃* X.Isotropy (F.ϕ x') :=
  { F.iso with
    invFun := F.isoInv
    left_inv := F.isoInv_iso
    right_inv := F.iso_isoInv }

@[simp] theorem isoEquiv_apply {x' : O'} (g : X'.Isotropy x') : F.isoEquiv x' g = F.iso g := rfl

/-! ### Orbits and saturated sets -/

/-- Two objects of `X'` are isomorphic iff their images are. -/
theorem π_eq_π_iff (z z' : O') : X'.π z = X'.π z' ↔ X.π (F.ϕ z) = X.π (F.ϕ z') := by
  rw [X'.π_eq_π_iff, X.π_eq_π_iff]
  constructor
  · rintro ⟨m, rfl, rfl⟩
    exact ⟨F.ϕm m, F.src_ϕm m, F.tgt_ϕm m⟩
  · rintro ⟨h, hs, ht⟩
    have hh : h ∈ X.morOn W := ⟨hs ▸ F.ϕ_mem z, ht ▸ F.ϕ_mem z'⟩
    exact ⟨F.ψm h, by rw [F.src_ψm hh, hs, F.ψ_ϕ], by rw [F.tgt_ψm hh, ht, F.ψ_ϕ]⟩

/-- The preimage of a saturated set is saturated. -/
theorem isSaturated_preimage {S : Set O} (hS : X.IsSaturated S) :
    X'.IsSaturated (F.ϕ ⁻¹' S) := by
  refine X'.isSaturated_iff.2 fun m hm => ?_
  have h := X.isSaturated_iff.1 hS (F.ϕm m)
  rw [F.src_ϕm, F.tgt_ϕm] at h
  exact h hm

/-! ### The properness property -/

/-- **Definition 7.5.8 (p. 271) along the inclusion**: if `U` has the properness property in `X`,
then `ϕ⁻¹(U)` has it in `X'`.  A sequence of morphisms of `X'` starting in `cl ϕ⁻¹(U)` with
convergent targets has, in `X`, a convergent subsequence; its limit ends in `W`, hence, `W` being
saturated, is a morphism between points of `W`. -/
theorem hasPropernessProperty_preimage {U : Set O} (hU : X.HasPropernessProperty U) :
    X'.HasPropernessProperty (F.ϕ ⁻¹' U) := by
  refine ⟨hU.1.preimage F.continuous_ϕ, ?_⟩
  rw [X'.isProperSubset_iff_exists_tendsto_subseq isClosed_closure]
  intro φ y hφ hy
  have hφ' : ∀ n, X.src (F.ϕm (φ n)) ∈ closure U := fun n => by
    rw [F.src_ϕm]
    exact F.continuous_ϕ.closure_preimage_subset U (hφ n)
  have hy' : Tendsto (X.tgt ∘ fun n => F.ϕm (φ n)) atTop (𝓝 (F.ϕ y)) := by
    have he : (X.tgt ∘ fun n => F.ϕm (φ n)) = F.ϕ ∘ (X'.tgt ∘ φ) := funext fun n => F.tgt_ϕm _
    rw [he]
    exact (F.continuous_ϕ.tendsto y).comp hy
  obtain ⟨φ₀, -, hφ₀t, ψ, hψ, hlim⟩ :=
    MPolyfold.exists_tendsto_subseq_of_isProperMap_domRestrict X.PMor hU.2 hφ' hy'
  have ht : X.tgt φ₀ ∈ W := by rw [hφ₀t]; exact F.ϕ_mem y
  have hφ₀ : φ₀ ∈ X.morOn W := ⟨src_mem_of_tgt_mem_of_isSaturated F.isSaturated ht, ht⟩
  refine ⟨F.ψm φ₀, ψ, hψ, ?_⟩
  have hc : ContinuousAt F.ψm φ₀ :=
    F.mor.isScSmoothOn_inv.continuousOn.continuousAt (F.mor.isOpen_target.mem_nhds hφ₀)
  refine (hc.tendsto.comp hlim).congr fun n => ?_
  exact F.ψm_ϕm _

/-! ### Natural representations -/

section PullRep

variable {x' : O'} (R : X.NaturalRep (F.ϕ x')) (hRW : R.U ⊆ W)

include hRW in
theorem isScDiffeoOn_ϕ_preimage : X'.PObj.IsScDiffeoOn X.PObj F.ϕ F.ψ (F.ϕ ⁻¹' R.U) R.U := by
  have h := F.obj.restrict (R.isOpen_U.preimage F.continuous_ϕ) (subset_univ _)
  have he : W ∩ F.ψ ⁻¹' (F.ϕ ⁻¹' R.U) = R.U := by
    ext z
    constructor
    · rintro ⟨hz, hz'⟩
      have : F.ϕ (F.ψ z) ∈ R.U := hz'
      rwa [F.ϕ_ψ hz] at this
    · intro hz
      refine ⟨hRW hz, ?_⟩
      change F.ϕ (F.ψ z) ∈ R.U
      rwa [F.ϕ_ψ (hRW hz)]
  rwa [he] at h

/-- **A natural representation of `X` at `ϕ(x')` with domain `U ⊆ W` gives one of `X'` at `x'`
with domain `ϕ⁻¹(U)`** (Theorem 7.1.13, p. 233): `Φ'(g') = ψ ∘ Φ(ι g') ∘ ϕ` and
`Γ'(g', y) = ψm(Γ(ι g', ϕ y))`. -/
def pullRep : X'.NaturalRep x' where
  U := F.ϕ ⁻¹' R.U
  isOpen_U := R.isOpen_U.preimage F.continuous_ϕ
  isConnected_U := by
    have he : F.ϕ ⁻¹' R.U = F.ψ '' R.U := by
      ext z
      constructor
      · intro hz
        exact ⟨F.ϕ z, hz, F.ψ_ϕ z⟩
      · rintro ⟨w, hw, rfl⟩
        change F.ϕ (F.ψ w) ∈ R.U
        rwa [F.ϕ_ψ (hRW hw)]
    rw [he]
    exact R.isConnected_U.image _ (F.obj.isScSmoothOn_inv.continuousOn.mono hRW)
  mem_U := R.mem_U
  Φ g y := F.ψ (R.Φ (F.iso g) (F.ϕ y))
  Γ g y := F.ψm (R.Γ (F.iso g) (F.ϕ y))
  isScDiffeoOn_Φ g := by
    have h1 := F.isScDiffeoOn_ϕ_preimage R hRW
    have h := h1.symm.comp ((R.isScDiffeoOn_Φ (F.iso g)).comp h1)
    rw [← map_inv] at h
    exact h
  Φ_mul g h y hy := by
    have hy' : F.ϕ y ∈ R.U := hy
    change F.ψ (R.Φ (F.iso (g * h)) (F.ϕ y)) =
      F.ψ (R.Φ (F.iso g) (F.ϕ (F.ψ (R.Φ (F.iso h) (F.ϕ y)))))
    rw [map_mul, R.Φ_mul _ _ _ hy', F.ϕ_ψ (hRW (R.mapsTo_Φ _ hy'))]
  isScSmoothOn_Γ g := by
    have h1 := (F.isScDiffeoOn_ϕ_preimage R hRW).isScSmoothOn
    refine F.mor.isScSmoothOn_inv.comp ((R.isScSmoothOn_Γ (F.iso g)).comp h1 fun y hy => hy)
      fun y hy => ?_
    have hm := R.Γ_mem_morOn (F.iso g) (show F.ϕ y ∈ R.U from hy)
    exact ⟨hRW hm.1, hRW hm.2⟩
  Γ_self g := by
    rw [R.Γ_self, F.iso_val, F.ψm_ϕm]
  src_Γ g y hy := by
    have hy' : F.ϕ y ∈ R.U := hy
    have hm := R.Γ_mem_morOn (F.iso g) hy'
    change X'.src (F.ψm (R.Γ (F.iso g) (F.ϕ y))) = y
    rw [F.src_ψm ⟨hRW hm.1, hRW hm.2⟩, R.src_Γ _ _ hy', F.ψ_ϕ]
  tgt_Γ g y hy := by
    have hy' : F.ϕ y ∈ R.U := hy
    have hm := R.Γ_mem_morOn (F.iso g) hy'
    change X'.tgt (F.ψm (R.Γ (F.iso g) (F.ϕ y))) = F.ψ (R.Φ (F.iso g) (F.ϕ y))
    rw [F.tgt_ψm ⟨hRW hm.1, hRW hm.2⟩, R.tgt_Γ _ _ hy']
  existsUnique_Γ h hs ht := by
    have hs' : X.src (F.ϕm h) ∈ R.U := by rw [F.src_ϕm]; exact hs
    have ht' : X.tgt (F.ϕm h) ∈ R.U := by rw [F.tgt_ϕm]; exact ht
    obtain ⟨g, hg, hgu⟩ := R.existsUnique_Γ (F.ϕm h) hs' ht'
    refine ⟨F.isoInv g, ?_, fun g' hg' => ?_⟩
    · change F.ψm (R.Γ (F.iso (F.isoInv g)) (F.ϕ (X'.src h))) = h
      rw [F.iso_isoInv, ← F.src_ϕm, hg, F.ψm_ϕm]
    · have hg'' : F.ψm (R.Γ (F.iso g') (F.ϕ (X'.src h))) = h := hg'
      have hm := R.Γ_mem_morOn (F.iso g') (show F.ϕ (X'.src h) ∈ R.U from hs)
      have h2 : R.Γ (F.iso g') (X.src (F.ϕm h)) = F.ϕm h := by
        rw [F.src_ϕm, ← F.ϕm_ψm (h := R.Γ (F.iso g') (F.ϕ (X'.src h))) ⟨hRW hm.1, hRW hm.2⟩,
          hg'']
      rw [← hgu _ h2, F.isoInv_iso]

@[simp] theorem pullRep_U : (F.pullRep R hRW).U = F.ϕ ⁻¹' R.U := rfl

theorem pullRep_Φ (g : X'.Isotropy x') (y : O') :
    (F.pullRep R hRW).Φ g y = F.ψ (R.Φ (F.iso g) (F.ϕ y)) := rfl

theorem pullRep_Γ (g : X'.Isotropy x') (y : O') :
    (F.pullRep R hRW).Γ g y = F.ψm (R.Γ (F.iso g) (F.ϕ y)) := rfl

/-- `ϕ ∘ Φ'(g') = Φ(ι g') ∘ ϕ` on `ϕ⁻¹(U)`. -/
theorem ϕ_pullRep_Φ (g : X'.Isotropy x') {y : O'} (hy : y ∈ (F.pullRep R hRW).U) :
    F.ϕ ((F.pullRep R hRW).Φ g y) = R.Φ (F.iso g) (F.ϕ y) :=
  F.ϕ_ψ (hRW (R.mapsTo_Φ _ hy))

/-- `ϕm(Γ'(g', y)) = Γ(ι g', ϕ y)` on `ϕ⁻¹(U)`. -/
theorem ϕm_pullRep_Γ (g : X'.Isotropy x') {y : O'} (hy : y ∈ (F.pullRep R hRW).U) :
    F.ϕm ((F.pullRep R hRW).Γ g y) = R.Γ (F.iso g) (F.ϕ y) := by
  have hm := R.Γ_mem_morOn (F.iso g) (show F.ϕ y ∈ R.U from hy)
  exact F.ϕm_ψm ⟨hRW hm.1, hRW hm.2⟩

end PullRep

end OpenInclusion

end EpGroupoid

namespace SBLocalization

open StrongBundle MPolyfold SEP UnitCube

variable {A : SEP.{u}} {V : Set A.Obj} (hV : A.X.IsEpSubgroupoid V)

/-! ### The inclusion `[0, 1] × (X|V) → [0, 1] × X` -/

open scoped Classical in
/-- The inverse of the inclusion of the morphism space of `X|V`, extended by the unit of `a` off
the morphisms between points of `V`. -/
def morRetract (a : (A.restr hV).Obj) (m : A.Mor) : (A.restr hV).Mor :=
  if h : m ∈ A.X.morOn V then (⟨m, h⟩ : A.X.morOn V) else (A.restr hV).X.unit a

theorem isOpen_morOn (hVo : IsOpen V) : IsOpen (A.X.morOn V) :=
  (hVo.preimage A.X.continuous_src).inter (hVo.preimage A.X.continuous_tgt)

/-- **The inclusion of the morphism space of `X|V` is an sc-diffeomorphism onto the open set of
the morphisms between points of `V`.** -/
theorem isScDiffeoOn_morRetract (hVo : IsOpen V) (a : (A.restr hV).Obj) :
    (A.restr hV).X.PMor.IsScDiffeoOn A.X.PMor (A.baseEP.subFunctor hV).mor (morRetract hV a)
      univ (A.X.morOn V) :=
  haveI : ParacompactSpace V := A.X.PObj.paracompactSpace_subtype V
  haveI : ParacompactSpace (A.X.morOn V) := A.X.PMor.paracompactSpace_subtype _
  MPolyfold.isScDiffeoOn_val_subPolyfold_of_isOpen (A.X.isSubMPolyfold_morOn hV)
    (isOpen_morOn hVo) ((A.restr hV).X.unit a)

theorem morOn_cube_snd_preimage :
    (A.cubeSEP 1).X.morOn (Prod.snd ⁻¹' V) =
      (Prod.snd ⁻¹' A.X.morOn V : Set ((Fin 1 → unitInterval) × A.Mor)) := rfl

/-- **The inclusion `[0, 1] × (X|V) → [0, 1] × X`** for `V` open and saturated, with the inverses
extended by the point `a` off `[0, 1] × V`. -/
def cubeRestrInclusion (hVo : IsOpen V) (a : (A.restr hV).Obj) :
    EpGroupoid.OpenInclusion ((A.restr hV).cubeSEP 1).X (A.cubeSEP 1).X
      (Prod.snd ⁻¹' V : Set ((Fin 1 → unitInterval) × A.Obj)) where
  ϕ z := (z.1, restrBase hV z.2)
  ψ := Prod.map id (A.baseEP.subRetract hV a)
  ϕm m := (m.1, (A.baseEP.subFunctor hV).mor m.2)
  ψm := Prod.map id (morRetract hV a)
  src_ϕm _ := rfl
  tgt_ϕm _ := rfl
  ϕm_comp a b h := by
    have : ParacompactSpace V := A.X.PObj.paracompactSpace_subtype V
    exact Prod.ext rfl (EpGroupoid.subEpGroupoid_comp_val hV (congrArg Prod.snd h))
  isSaturated := by
    have h := A.X.isSaturated_prod_cubeProd 1 (univ : Set (Fin 1 → unitInterval))
      hV.isSaturated
    rwa [univ_prod] at h
  obj := by
    have h := MPolyfold.IsScDiffeoOn.prodMap
      (MPolyfold.isScDiffeoOn_id (P := cubePolyfold 1) isOpen_univ)
      (A.baseEP.isScDiffeoOn_subRetract hV hVo a).symm
    rwa [univ_prod_univ, univ_prod] at h
  mor := by
    have h := MPolyfold.IsScDiffeoOn.prodMap
      (MPolyfold.isScDiffeoOn_id (P := cubePolyfold 1) isOpen_univ)
      (isScDiffeoOn_morRetract hV hVo a)
    rwa [univ_prod_univ, univ_prod] at h

@[simp] theorem cubeRestrInclusion_ϕ (hVo : IsOpen V) (a : (A.restr hV).Obj)
    (z : ((A.restr hV).cubeSEP 1).Obj) :
    (cubeRestrInclusion hV hVo a).ϕ z = (z.1, restrBase hV z.2) := rfl

/-- Two points of `[0, 1] × (X|V)` are isomorphic iff their images in `[0, 1] × X` are. -/
theorem cubeRestrInclusion_π_eq_π_iff (hVo : IsOpen V) (z z' : ((A.restr hV).cubeSEP 1).Obj) :
    ((A.restr hV).cubeSEP 1).X.π z = ((A.restr hV).cubeSEP 1).X.π z' ↔
      (A.cubeSEP 1).X.π (z.1, restrBase hV z.2) = (A.cubeSEP 1).X.π (z'.1, restrBase hV z'.2) :=
  (cubeRestrInclusion hV hVo z.2).π_eq_π_iff z z'

/-- The preimage in `[0, 1] × (X|V)` of a saturated subset of `[0, 1] × X` is saturated. -/
theorem isSaturated_preimage_cubeRestr (hVo : IsOpen V) {S : Set (A.cubeSEP 1).Obj}
    (hS : (A.cubeSEP 1).X.IsSaturated S) :
    ((A.restr hV).cubeSEP 1).X.IsSaturated
      ((fun z : ((A.restr hV).cubeSEP 1).Obj => (z.1, restrBase hV z.2)) ⁻¹' S) := by
  rcases isEmpty_or_nonempty (A.restr hV).Obj with he | ⟨⟨a⟩⟩
  · refine (((A.restr hV).cubeSEP 1).X.isSaturated_iff).2 fun m _ => ?_
    exact (he.false (((A.restr hV).cubeSEP 1).X.tgt m).2).elim
  · exact (cubeRestrInclusion hV hVo a).isSaturated_preimage hS

/-- **A natural representation of the cylinder `[0, 1] × X` with domain over `V` is one of the
cylinder `[0, 1] × (X|V)` of the restriction** (Theorem 7.1.13, p. 233; Definition 7.5.8, p. 271;
`V` open and saturated): the domain is the preimage, the properness property is kept, and the
actions correspond under an isomorphism of the isotropy groups. -/
theorem exists_naturalRep_cubeRestr (hVo : IsOpen V) (x' : ((A.restr hV).cubeSEP 1).Obj)
    (R : (A.cubeSEP 1).X.NaturalRep (x'.1, restrBase hV x'.2))
    (hRV : R.U ⊆ Prod.snd ⁻¹' V) (hprop : (A.cubeSEP 1).X.HasPropernessProperty R.U) :
    ∃ R' : ((A.restr hV).cubeSEP 1).X.NaturalRep x',
      R'.U = (fun z : ((A.restr hV).cubeSEP 1).Obj => (z.1, restrBase hV z.2)) ⁻¹' R.U ∧
      ((A.restr hV).cubeSEP 1).X.HasPropernessProperty R'.U ∧
      ∀ g' : ((A.restr hV).cubeSEP 1).X.Isotropy x',
        ∃ g : (A.cubeSEP 1).X.Isotropy (x'.1, restrBase hV x'.2), ∀ y ∈ R'.U,
          ((R'.Φ g' y).1, restrBase hV (R'.Φ g' y).2) = R.Φ g (y.1, restrBase hV y.2) :=
  ⟨(cubeRestrInclusion hV hVo x'.2).pullRep R hRV, rfl,
    (cubeRestrInclusion hV hVo x'.2).hasPropernessProperty_preimage hprop,
    fun g' => ⟨(cubeRestrInclusion hV hVo x'.2).iso g', fun _ hy =>
      (cubeRestrInclusion hV hVo x'.2).ϕ_pullRep_Φ R hRV g' hy⟩⟩

/-- The point `(t, ι a)` of `[0, 1] × X` under the point `(t, a)` of `[0, 1] × (X|V)`. -/
abbrev cubeRestrObj (z : ((A.restr hV).cubeSEP 1).Obj) : (A.cubeSEP 1).Obj :=
  (z.1, restrBase hV z.2)

/-- The same with the isomorphism `ι` of the isotropy groups and the maps `Γ` made explicit. -/
theorem exists_naturalRep_cubeRestr_equiv (hVo : IsOpen V) (x' : ((A.restr hV).cubeSEP 1).Obj)
    (R : (A.cubeSEP 1).X.NaturalRep (x'.1, restrBase hV x'.2))
    (hRV : R.U ⊆ Prod.snd ⁻¹' V) (hprop : (A.cubeSEP 1).X.HasPropernessProperty R.U) :
    ∃ (R' : ((A.restr hV).cubeSEP 1).X.NaturalRep x')
      (ι : ((A.restr hV).cubeSEP 1).X.Isotropy x' ≃*
        (A.cubeSEP 1).X.Isotropy (cubeRestrObj hV x')),
      R'.U = (fun z : ((A.restr hV).cubeSEP 1).Obj => (z.1, restrBase hV z.2)) ⁻¹' R.U ∧
      ((A.restr hV).cubeSEP 1).X.HasPropernessProperty R'.U ∧
      (∀ g', (ι g').val = ((g'.val).1, (A.baseEP.subFunctor hV).mor (g'.val).2)) ∧
      ∀ g', ∀ y ∈ R'.U,
        ((R'.Φ g' y).1, restrBase hV (R'.Φ g' y).2) = R.Φ (ι g') (y.1, restrBase hV y.2) ∧
        ((R'.Γ g' y).1, (A.baseEP.subFunctor hV).mor (R'.Γ g' y).2) =
          R.Γ (ι g') (y.1, restrBase hV y.2) :=
  ⟨(cubeRestrInclusion hV hVo x'.2).pullRep R hRV, (cubeRestrInclusion hV hVo x'.2).isoEquiv x',
    rfl, (cubeRestrInclusion hV hVo x'.2).hasPropernessProperty_preimage hprop, fun _ => rfl,
    fun g' _ hy => ⟨(cubeRestrInclusion hV hVo x'.2).ϕ_pullRep_Φ R hRV g' hy,
      (cubeRestrInclusion hV hVo x'.2).ϕm_pullRep_Γ R hRV g' hy⟩⟩

end SBLocalization

end Polyfold
