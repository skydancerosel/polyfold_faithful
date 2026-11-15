import Polyfold.Chapter15.ProductStrongBundle
import Polyfold.Chapter3.GermFilling
import Polyfold.Chapter3.GermCalculus

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2021), §15.3, the products remark after
**Definition 15.3.3** (p. 692): "`f × f'` is an sc-Fredholm section of `W × W' → X × X'`".
The local part, with the notions of §3.1 (Definitions 3.1.1, 3.1.2, 3.1.4, 3.1.6).

# Products of sc-germs and of fillings

## What is formalized

* `ScNbhdGerm.prod` (the product `G × G'` of two sc-germs of neighbourhoods, in the quadrant
  `C × C'`), `IsQuadrantLike.prod`.
* `IsScSmoothGerm.prodMap`, `IsSc1GermWith.prodMap`: `(u, u') ↦ (f(u), f'(u'))` is an sc-smooth
  germ (an sc¹-germ with the derivative family `Df × Df'`) on `G × G'`.
* `IsScPlusGerm.prodMap`: products of local sc⁺-sections.
* `kerProdCLE`: the kernel of `A × A'` is the product of the kernels.
* **`IsFillingGerm.prod`**: if `g` fills `f̂` for `R` and `g'` fills `f̂'` for `R'`, then
  `g × g'` fills `f̂ × f̂'` for the product retraction `R × R'` (Definition 3.1.4: the conditions
  (1), (2) componentwise; (3) `ker D(r × r')(0) = ker Dr(0) × ker Dr'(0)`,
  `ker (ρ × ρ')(0) = ker ρ(0) × ker ρ'(0)`, and the linearization is the product).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

section GermProducts

variable {E E' F F' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}

/-- `C × C'` is quadrant-like when `C` and `C'` are. -/
lemma IsQuadrantLike.prod (hC : IsQuadrantLike E C) (hC' : IsQuadrantLike E' C') :
    IsQuadrantLike (E.prod E') (C ×ˢ C') where
  zero_mem := ⟨hC.zero_mem, hC'.zero_mem⟩
  convex m := by
    rw [lvlSet_prod]
    exact (hC.convex m).prod (hC'.convex m)
  interior_nonempty m := by
    rw [lvlSet_prod, interior_prod_eq]
    exact (hC.interior_nonempty m).prod (hC'.interior_nonempty m)

/-- **The product germ `G × G'`** in `E ⊕ E'` with the quadrant `C × C'`. -/
def ScNbhdGerm.prod (G : ScNbhdGerm E C) (G' : ScNbhdGerm E' C') :
    ScNbhdGerm (E.prod E') (C ×ˢ C') where
  U m := G.U m ×ˢ G'.U m
  nested m x hx := ⟨G.nested m x.1 hx.1, G'.nested m x.2 hx.2⟩
  zero_mem m := ⟨G.zero_mem m, G'.zero_mem m⟩
  relOpen m := by
    obtain ⟨O, hO, h⟩ := G.relOpen m
    obtain ⟨O', hO', h'⟩ := G'.relOpen m
    exact ⟨O ×ˢ O', hO.prod hO', by rw [lvlSet_prod, h, h', prod_inter_prod]⟩

@[simp] lemma ScNbhdGerm.prod_U (G : ScNbhdGerm E C) (G' : ScNbhdGerm E' C') (m : ℕ) :
    (G.prod G').U m = G.U m ×ˢ G'.U m := rfl

lemma ScNbhdGerm.prod_mapsToGerm_fst (G : ScNbhdGerm E C) (G' : ScNbhdGerm E' C') :
    (G.prod G').MapsToGerm G (E.fstOp E' 0) := by
  intro m x hx
  rw [ScOperator.levelMap_eq]
  exact hx.1

lemma ScNbhdGerm.prod_mapsToGerm_snd (G : ScNbhdGerm E C) (G' : ScNbhdGerm E' C') :
    (G.prod G').MapsToGerm G' (E.sndOp E' 0) := by
  intro m x hx
  rw [ScOperator.levelMap_eq]
  exact hx.2

/-- `(u, u') ↦ (f(u), f'(u'))` is an sc-smooth germ on `G × G'`. -/
theorem IsScSmoothGerm.prodMap (hC : IsQuadrantLike E C) (hC' : IsQuadrantLike E' C')
    {G : ScNbhdGerm E C} {G' : ScNbhdGerm E' C'} {f : E 0 → F 0} {f' : E' 0 → F' 0}
    (hf : IsScSmoothGerm G f) (hf' : IsScSmoothGerm G' f') :
    IsScSmoothGerm (F := F.prod F') (G.prod G') (Prod.map f f') := by
  have hCC := hC.prod hC'
  have h1 : IsScSmoothGerm (G.prod G') (f ∘ E.fstOp E' 0) :=
    IsScSmoothGerm.comp hCC hC hf ((E.fstOp E').isScSmoothGerm _ hCC) (G.prod_mapsToGerm_fst G')
  have h2 : IsScSmoothGerm (G.prod G') (f' ∘ E.sndOp E' 0) :=
    IsScSmoothGerm.comp hCC hC' hf' ((E.sndOp E').isScSmoothGerm _ hCC)
      (G.prod_mapsToGerm_snd G')
  exact IsScSmoothGerm.pair hCC h1 h2

/-- `(u, u') ↦ (f(u), f'(u'))` is an sc¹-germ on `G × G'` with the derivative family
`Df(u) × Df'(u')`. -/
theorem IsSc1GermWith.prodMap (hC : IsQuadrantLike E C) (hC' : IsQuadrantLike E' C')
    {G : ScNbhdGerm E C} {G' : ScNbhdGerm E' C'} {f : E 0 → F 0} {f' : E' 0 → F' 0}
    {Df : E 1 → E 0 →L[ℝ] F 0} {Df' : E' 1 → E' 0 →L[ℝ] F' 0} (hf : IsSc1GermWith G f Df)
    (hf' : IsSc1GermWith G' f' Df') :
    IsSc1GermWith (F := F.prod F') (G.prod G') (Prod.map f f')
      fun x : (E.prod E') 1 => (Df x.1).prodMap (Df' x.2) := by
  have h1 := hf.comp (G.relOpenConvex hC 1) ((E.fstOp E').isSc1GermWith (G.prod G'))
    (G.prod_mapsToGerm_fst G')
  have h2 := hf'.comp (G'.relOpenConvex hC' 1) ((E.sndOp E').isSc1GermWith (G.prod G'))
    (G.prod_mapsToGerm_snd G')
  refine ((h1.pair h2).congr fun _ _ => rfl).congr_deriv fun x _ => ?_
  rw [ScOperator.levelMap_eq, ScOperator.levelMap_eq]
  rfl

/-- Products of local sc⁺-sections (germ reading). -/
theorem IsScPlusGerm.prodMap (hC : IsQuadrantLike E C) (hC' : IsQuadrantLike E' C')
    {U : Set (E 0)} {U' : Set (E' 0)} {s : E 0 → F 1} {s' : E' 0 → F' 1}
    (hs : IsScPlusGerm C U s) (hs' : IsScPlusGerm C' U' s') :
    IsScPlusGerm (E := E.prod E') (F := F.prod F') (C ×ˢ C') (U ×ˢ U') (Prod.map s s') := by
  obtain ⟨G, hG, hsm⟩ := hs
  obtain ⟨G', hG', hsm'⟩ := hs'
  exact ⟨G.prod G', fun x hx => ⟨hG hx.1, hG' hx.2⟩,
    IsScSmoothGerm.prodMap (F := F.shift) (F' := F'.shift) hC hC' hsm hsm'⟩

end GermProducts

/-! ### The kernel of a product -/

section KerProd

variable {V V' V₂ V₂' : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [AddCommGroup V'] [Module ℝ V'] [TopologicalSpace V'] [AddCommGroup V₂] [Module ℝ V₂]
  [TopologicalSpace V₂] [AddCommGroup V₂'] [Module ℝ V₂'] [TopologicalSpace V₂']

omit [TopologicalSpace V] [TopologicalSpace V'] [TopologicalSpace V₂] [TopologicalSpace V₂'] in
lemma fst_mem_ker_of_prod {A : V →ₗ[ℝ] V₂} {A' : V' →ₗ[ℝ] V₂'} {L : V × V' →ₗ[ℝ] V₂ × V₂'}
    (hL : ∀ v, L v = (A v.1, A' v.2)) {v : V × V'} (hv : v ∈ LinearMap.ker L) :
    v.1 ∈ LinearMap.ker A := by
  have h : L v = 0 := LinearMap.mem_ker.1 hv
  rw [hL] at h
  exact LinearMap.mem_ker.2 (congrArg Prod.fst h)

omit [TopologicalSpace V] [TopologicalSpace V'] [TopologicalSpace V₂] [TopologicalSpace V₂'] in
lemma snd_mem_ker_of_prod {A : V →ₗ[ℝ] V₂} {A' : V' →ₗ[ℝ] V₂'} {L : V × V' →ₗ[ℝ] V₂ × V₂'}
    (hL : ∀ v, L v = (A v.1, A' v.2)) {v : V × V'} (hv : v ∈ LinearMap.ker L) :
    v.2 ∈ LinearMap.ker A' := by
  have h : L v = 0 := LinearMap.mem_ker.1 hv
  rw [hL] at h
  exact LinearMap.mem_ker.2 (congrArg Prod.snd h)

omit [TopologicalSpace V] [TopologicalSpace V'] [TopologicalSpace V₂] [TopologicalSpace V₂'] in
lemma mk_mem_ker_of_prod {A : V →ₗ[ℝ] V₂} {A' : V' →ₗ[ℝ] V₂'} {L : V × V' →ₗ[ℝ] V₂ × V₂'}
    (hL : ∀ v, L v = (A v.1, A' v.2)) {a : V} {a' : V'} (ha : a ∈ LinearMap.ker A)
    (ha' : a' ∈ LinearMap.ker A') : (a, a') ∈ LinearMap.ker L := by
  refine LinearMap.mem_ker.2 ?_
  rw [hL]
  exact Prod.ext (LinearMap.mem_ker.1 ha) (LinearMap.mem_ker.1 ha')

/-- If `L(v, v') = (A v, A' v')`, then `ker L ≅ ker A × ker A'`. -/
def kerProdCLE (A : V →L[ℝ] V₂) (A' : V' →L[ℝ] V₂') (L : V × V' →L[ℝ] V₂ × V₂')
    (hL : ∀ v, L v = (A v.1, A' v.2)) :
    LinearMap.ker (L : V × V' →ₗ[ℝ] V₂ × V₂') ≃L[ℝ]
      LinearMap.ker (A : V →ₗ[ℝ] V₂) × LinearMap.ker (A' : V' →ₗ[ℝ] V₂') where
  toFun v := (⟨(v : V × V').1, fst_mem_ker_of_prod (A := (A : V →ₗ[ℝ] V₂))
      (A' := (A' : V' →ₗ[ℝ] V₂')) (L := (L : V × V' →ₗ[ℝ] V₂ × V₂')) hL v.2⟩,
    ⟨(v : V × V').2, snd_mem_ker_of_prod (A := (A : V →ₗ[ℝ] V₂))
      (A' := (A' : V' →ₗ[ℝ] V₂')) (L := (L : V × V' →ₗ[ℝ] V₂ × V₂')) hL v.2⟩)
  invFun u := ⟨((u.1 : V), (u.2 : V')), mk_mem_ker_of_prod (A := (A : V →ₗ[ℝ] V₂))
      (A' := (A' : V' →ₗ[ℝ] V₂')) (L := (L : V × V' →ₗ[ℝ] V₂ × V₂')) hL u.1.2 u.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

@[simp] lemma kerProdCLE_apply_fst (A : V →L[ℝ] V₂) (A' : V' →L[ℝ] V₂')
    (L : V × V' →L[ℝ] V₂ × V₂') (hL : ∀ v, L v = (A v.1, A' v.2))
    (v : LinearMap.ker (L : V × V' →ₗ[ℝ] V₂ × V₂')) :
    ((kerProdCLE A A' L hL v).1 : V) = (v : V × V').1 := rfl

@[simp] lemma kerProdCLE_apply_snd (A : V →L[ℝ] V₂) (A' : V' →L[ℝ] V₂')
    (L : V × V' →L[ℝ] V₂ × V₂') (hL : ∀ v, L v = (A v.1, A' v.2))
    (v : LinearMap.ker (L : V × V' →ₗ[ℝ] V₂ × V₂')) :
    ((kerProdCLE A A' L hL v).2 : V') = (v : V × V').2 := rfl

@[simp] lemma kerProdCLE_symm_apply (A : V →L[ℝ] V₂) (A' : V' →L[ℝ] V₂')
    (L : V × V' →L[ℝ] V₂ × V₂') (hL : ∀ v, L v = (A v.1, A' v.2))
    (u : LinearMap.ker (A : V →ₗ[ℝ] V₂) × LinearMap.ker (A' : V' →ₗ[ℝ] V₂')) :
    (((kerProdCLE A A' L hL).symm u : LinearMap.ker (L : V × V' →ₗ[ℝ] V₂ × V₂')) : V × V') =
      ((u.1 : V), (u.2 : V')) := rfl

end KerProd

/-! ### Products of fillings -/

section FillingProducts

open StrongRetr

variable {E E' F F' : ScBanach} {C U : Set (E 0)} {C' U' : Set (E' 0)}
  {R : E 0 × F 0 → E 0 × F 0} {R' : E' 0 × F' 0 → E' 0 × F' 0}

lemma r_prodBundleMap (y : (E.prod E') 0) :
    StrongRetr.r (E := E.prod E') (F := F.prod F') (prodBundleMap R R') y =
      (StrongRetr.r R y.1, StrongRetr.r R' y.2) := rfl

lemma ρ_prodBundleMap (y : (E.prod E') 0) (h : (F.prod F') 0) :
    StrongRetr.ρ (E := E.prod E') (F := F.prod F') (prodBundleMap R R') y h =
      (StrongRetr.ρ R y.1 h.1, StrongRetr.ρ R' y.2 h.2) := rfl

lemma r_image_prodBundleMap :
    StrongRetr.r (E := E.prod E') (F := F.prod F') (prodBundleMap R R') '' (U ×ˢ U') =
      (StrongRetr.r R '' U) ×ˢ (StrongRetr.r R' '' U') := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.1, hy.1, rfl⟩, ⟨y.2, hy.2, rfl⟩⟩
  · rintro ⟨⟨u, hu, hux⟩, ⟨u', hu', hux'⟩⟩
    exact ⟨(u, u'), ⟨hu, hu'⟩, Prod.ext hux hux'⟩

lemma fillDefect_prodBundleMap (g : E 0 → F 0) (g' : E' 0 → F' 0) :
    fillDefect (E := E.prod E') (F := F.prod F') (prodBundleMap R R') (Prod.map g g') =
      Prod.map (fillDefect R g) (fillDefect R' g') := rfl

/-- **Products of fillings** (Definition 3.1.4, Definition 3.1.6, germ reading): `g × g'` fills
`f̂ × f̂'` for the product strong bundle retraction `R × R'`. -/
theorem IsFillingGerm.prod (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (hR : IsStrongBundleRetraction U R) (hR' : IsStrongBundleRetraction U' R')
    (h0 : (0 : E 0) ∈ U) (h0' : (0 : E' 0) ∈ U') {fb g : E 0 → F 0} {fb' g' : E' 0 → F' 0}
    (hfill : IsFillingGerm hU hR h0 fb g) (hfill' : IsFillingGerm hU' hR' h0' fb' g') :
    IsFillingGerm (E := E.prod E') (F := F.prod F') (hU.prod hU') (hR.prod hU hU' hR')
      (show (0 : (E.prod E') 0) ∈ U ×ˢ U' from ⟨h0, h0'⟩) (Prod.map fb fb') (Prod.map g g') := by
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  have hQ' := hU'.isPartialQuadrant.isQuadrantLike
  have ht1 : Tendsto (fun w : (E.prod E') 0 => w.1) (𝓝 0) (𝓝 0) :=
    continuous_fst.tendsto' _ _ rfl
  have ht2 : Tendsto (fun w : (E.prod E') 0 => w.2) (𝓝 0) (𝓝 0) :=
    continuous_snd.tendsto' _ _ rfl
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [ht1.eventually hfill.eq_on, ht2.eventually hfill'.eq_on] with w hw hw' hwO
    rw [r_image_prodBundleMap] at hwO
    exact Prod.ext (hw hwO.1) (hw' hwO.2)
  · filter_upwards [ht1.eventually hfill.mem_of_fixed, ht2.eventually hfill'.mem_of_fixed]
      with y hy hy' hyU hfix
    rw [r_image_prodBundleMap]
    exact ⟨hy hyU.1 (congrArg Prod.fst hfix), hy' hyU.2 (congrArg Prod.snd hfix)⟩
  · obtain ⟨G, hGU, hg, Dk, hDk, Φ, hΦ⟩ := hfill.germ
    obtain ⟨G', hGU', hg', Dk', hDk', Φ', hΦ'⟩ := hfill'.germ
    refine ⟨G.prod G', fun w hw => ⟨hGU hw.1, hGU' hw.2⟩,
      IsScSmoothGerm.prodMap hQ hQ' hg hg', fun x => (Dk x.1).prodMap (Dk' x.2), ?_, ?_⟩
    · rw [fillDefect_prodBundleMap]
      exact IsSc1GermWith.prodMap hQ hQ' hDk hDk'
    -- `D(r × r')(0) = Dr(0) × Dr'(0)`
    have h0L : (0 : (E.prod E') 1) ∈ (E.prod E').lvlSet (U ×ˢ U') 1 := by
      change (E.prod E').toBase 1 0 ∈ U ×ˢ U'
      rw [map_zero]
      exact ⟨h0, h0'⟩
    have hD := scDeriv_prodMap (F := E) (F' := E') hU hU' (hR.baseRetraction hU).isScSmooth
      (hR'.baseRetraction hU').isScSmooth h0L
    have hDv : ∀ v : E 0 × E' 0,
        (scDeriv (E := E.prod E') (F := E.prod E') (U ×ˢ U')
          (StrongRetr.r (E := E.prod E') (F := F.prod F') (prodBundleMap R R'))
          (0 : (E.prod E') 1)) v =
        (scDeriv U (StrongRetr.r R) (0 : E 1) v.1, scDeriv U' (StrongRetr.r R') (0 : E' 1) v.2) :=
      fun v => congrArg (fun L : (E.prod E') 0 →L[ℝ] (E.prod E') 0 => L v) hD
    have hρv : ∀ h : F 0 × F' 0,
        (StrongRetr.ρCLM (E := E.prod E') (F := F.prod F') (hR.prod hU hU' hR')
          (show (0 : (E.prod E') 0) ∈ U ×ˢ U' from ⟨h0, h0'⟩)) h =
        (StrongRetr.ρCLM hR h0 h.1, StrongRetr.ρCLM hR' h0' h.2) := fun _ => rfl
    refine ⟨((kerProdCLE _ _ _ hDv).trans (Φ.prodCongr Φ')).trans
      (kerProdCLE _ _ _ hρv).symm, fun v => ?_⟩
    exact Prod.ext ((hΦ (kerProdCLE _ _ _ hDv v).1).trans rfl)
      ((hΦ' (kerProdCLE _ _ _ hDv v).2).trans rfl)

end FillingProducts

end Polyfold
