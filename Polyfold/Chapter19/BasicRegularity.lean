import Polyfold.Chapter19.PolyfoldStructureGCT
import Polyfold.Chapter10.EquivalenceZhou
import Polyfold.Chapter8.SmoothRegularAssembly

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.5 (pp. 888–890): **Definitions 19.5.5, 19.5.6, 19.5.8, 19.5.10** ((ZHOU), (LUC), (SLUC),
(LR), (SLR) for a basic construction) and **Propositions 19.5.7, 19.5.11**.  Numbers and pages
are the 2021 text's.

# Regularity conditions of a basic construction

## The text, paraphrased

(Definition 19.5.5) For `Ψ ∈ F(α)`, `Ψ(ō) = α`, and `g ∈ G`, `Tg = Tĝ(ō) : T_ōO → T_ōO`, the
linearization at `ō` of the sc-diffeomorphism `ĝ` of `O`, which fixes `ō`.  (Definition 19.5.6)
`(F, 𝓕)` satisfies (ZHOU) if for every smooth `z ∈ |S|` there are `α_z` with `z = |α_z|` and
`Ψ ∈ F(α_z)` such that `Tg = id` implies `ĝ = id` near `ō`.  (Proposition 19.5.7) If `T` is
metrizable, the polyfold `(S, F, M)` satisfies (ZHOU) if `(F, 𝓕)` does.  (Definition 19.5.8)
(LUC): for every `z` there are `α_z`, `Ψ ∈ F(α_z)` and an open `G`-invariant `U(ō)` such that
`ĝ : U → U` is the identity if it is the identity on a nontrivial open `V ⊂ U`; (SLUC): (LUC)
for the basic constructions `(Fⁱ, 𝓕ⁱ)` of `Sⁱ`.  (Definition 19.5.10) (LR): for every `z` there
are `α_z`, `Ψ ∈ F(α_z)` and arbitrarily small open `G`-invariant `U(ō)` such that every
sc-diffeomorphism `β : U → U` with `|β(q)| = |q|` is `q ↦ g ∗ q` for some `g`; (SLR): (LR) for
every `(Fⁱ, 𝓕ⁱ)`.  (Proposition 19.5.11) (ZHOU) implies (SLUC) and (SLR).

## What is formalized

Pointwise forms for ep-groupoids (namespace `Polyfold.EpGroupoid`): `IsZhouAt` (Chapter 7's
(ZHOU) at one smooth point, `isZhou_iff_forall_isZhouAt`), `IsLRAt` (Chapter 7's (LR) at one
point, `isLR_iff_forall_isLRAt`); `EpFunctor.isZhouAt_of_isZhouAt` (the Zhou condition at `x`
passes to every object isomorphic to `F(x)`, for a full functor that is a local
sc-diffeomorphism on objects; the argument of Proposition 10.1.17) and
`EpFunctor.isZhouAt_of_isZhouAt_obj` (back along `F`).

The translation groupoid `G ⋉ O` (namespace `Polyfold.EpGroupoid.Examples`):
`action_mem_trivialSet_iff` (`g` acts trivially iff `ĝ = id` near the point),
`action_tangentMor_eq` (Chapter 7's tangent map of the morphism `(g, ō)` is `Tĝ(ō)`),
`action_Γ_eq`, `action_Φ_eq` (every natural representation of `G ⋉ O` is the action).

Raised ep-groupoids (namespace `Polyfold.EP`): `liftVal` (the point of `X` under a point of
`Xⁱ`), `exists_liftVal_eq_of_mem` (every point of level `i` lies under a point of `Xⁱ`).

For a uniformizer `Ψ` (namespace `Polyfold.GroupoidalCategory.Uniformizer`): `toEP` (the
ep-groupoid `G ⋉ O`),
`tangentSmul` (`Tg`), `IsZhouAt`, `IsLUCAt`, `IsLRAt` (the printed conditions at `ō`), and
`isZhouAt_iff` / `isLUCAt_iff` / `isLRAt_of_isLRAt` (their ep-groupoid forms).

Models (namespace `Polyfold.GCT.PolyfoldConstruction`): `full_pieceFunctor`,
`isLocalScDiffeo_pieceFunctor_obj` (the functor `G ⋉ O → X_Ψ` of a piece is full and a local
sc-diffeomorphism on objects).

For a basic construction `B` (namespace `Polyfold.GroupoidalCategory.BasicConstruction`):
`IsLevelClass`, `IsSmoothClass`, `mem_levelSet_iff_of_π_eq`, `mem_smoothSet_iff_of_π_eq`
(levels do not depend on the uniformizer: the `f_h` are local sc-diffeomorphisms);
**`definition_19_5_5`**, **`IsZhou`** (Definition 19.5.6), **`IsLUC`**, `IsLUCLevel`, **`IsSLUC`**
(Definition 19.5.8), **`IsLR`**, `IsLRLevel`, **`IsSLR`** (Definition 19.5.10);
**`proposition_19_5_7`**, `isZhou_toEP_of_isZhou` (under (ZHOU) of the polyfold, every `G ⋉ O`
satisfies (ZHOU)), **`proposition_19_5_11`**.

## Readings

* Definitions 19.5.5–19.5.10 speak of `g ∈ G` with `ĝ` fixing `ō` (Definition 19.1.2: `G` is the
  isotropy group of `α`).  We read `G` as the stabilizer `G_ō = {g | g ∗ ō = ō}` (all of `G` when
  `Ψ` is centred at `α`, `IsCentred`), and "G-invariant" as `G_ō`-invariant.
* "`Tg` is the identity": `Tĝ(ō)` (Chapter 2's tangent map of `ĝ`) is the identity on the
  tangent space `T_ōO`; `ō` is smooth because `z` is (`mem_levelSet_iff_of_π_eq`).  "`ĝ` is the
  identity near `ō`": `ĝ(q) = q` for `q` in a neighbourhood of `ō`.
* "Nontrivial open subset": nonempty open subset.  "`|β(q)| = |q|`": the classes of `Ψ(β(q))`
  and `Ψ(q)` in `|S|` agree.  "For a suitable `g ∈ G_x`": `g ∈ G_ō`.
* `(Fⁱ, 𝓕ⁱ)` and `Sⁱ` are not defined in Chapter 19.  We read `|Sⁱ|` as the classes of objects
  `Ψ(q)` with `q ∈ O_i` (`IsLevelClass`; independent of `Ψ` by `mem_levelSet_iff_of_π_eq`) and
  the uniformizers of `Fⁱ` as `Ψⁱ : G ⋉ Oⁱ → Sⁱ`, whose translation groupoid is Chapter 7's
  raised ep-groupoid `(G ⋉ O)ⁱ` (`EP.lift`).  (LUC) and (LR) for `(Fⁱ, 𝓕ⁱ)` are then Chapter 7's
  (LUC) and (LR) of `(G ⋉ O)ⁱ` at the point `ōⁱ` over `ō` (`IsLUCLevel`, `IsLRLevel`); for
  `i = 0` these are the printed conditions (`isLUCAt_iff`, `isLRAt_of_isLRAt`).
* Proposition 19.5.11 is read under the standing assumption of §19.5 (p. 886) that `T` is
  metrizable: its proof ("as a consequence of the considerations in the ep-groupoid case") goes
  through the model `X_Ψ` of the polyfold structure `(F, M)`, Proposition 19.5.7 and Theorems
  7.4.13 and 7.4.24.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter TopologicalSpace

noncomputable section

namespace Polyfold

universe u v

/-! ### The Zhou condition at a point -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **(ZHOU) at a smooth point `y`** (Definition 7.4.5 at `y`): every `g ∈ G_y` with `Tg = id`
on `T_yX` acts trivially near `y`. -/
def IsZhouAt (y : X.PObj.SmoothLevel) : Prop :=
  ∀ g : X.Isotropy (X.PObj.smoothVal y),
    (∀ v ∈ X.PObj.tangentFiber (X.PObj.smoothIncl y 1), X.tangentMor g.val v = v) →
      g ∈ X.trivialSubgroup (X.PObj.smoothVal y)

theorem isZhou_iff_forall_isZhouAt : X.IsZhou ↔ ∀ y, X.IsZhouAt y := Iff.rfl

/-- **(LR) at a point `x`** (Definition 7.4.19 at `x`). -/
def IsLRAt (x : Obj) : Prop :=
  ∀ O : Set Obj, IsOpen O → x ∈ O → ∃ R : X.NaturalRep x, R.U ⊆ O ∧
    ∀ β β' : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj β β' R.U R.U →
      (∀ y ∈ R.U, X.π (β y) = X.π y) → ∃ g : X.Isotropy x, ∀ y ∈ R.U, β y = R.Φ g y

theorem isLR_iff_forall_isLRAt : X.IsLR ↔ ∀ x, X.IsLRAt x := Iff.rfl

end EpGroupoid

namespace EpFunctor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y)

/-- **The Zhou condition passes along a full functor which is a local sc-diffeomorphism on
objects, and along isomorphisms**: (ZHOU) at a smooth `x` gives (ZHOU) at every `y ≅ F(x)` (the
argument of Proposition 10.1.17). -/
theorem isZhouAt_of_isZhouAt (hd : X.PObj.IsLocalScDiffeo Y.PObj F.obj)
    (hfull : F.toFunctor.Full) {x : Obj} (hxS : x ∈ X.PObj.smoothSet)
    (hX : X.IsZhouAt (X.PObj.smoothMk x hxS)) (y : Y.PObj.SmoothLevel) {ψ : Mor'}
    (hs : Y.src ψ = F.obj x) (ht : Y.tgt ψ = Y.PObj.smoothVal y) : Y.IsZhouAt y := by
  intro k hk
  have hyS : Y.PObj.smoothVal y ∈ Y.PObj.smoothSet := Y.PObj.smoothVal_mem y
  have hψS : ψ ∈ Y.PMor.smoothSet := (Y.mem_smoothSet_tgt_iff ψ).1 (ht ▸ hyS)
  have hψ1 : ψ ∈ Y.PMor.levelSet 1 := mem_iInter.1 hψS 1
  have hx1 : x ∈ X.PObj.levelSet 1 := mem_iInter.1 hxS 1
  have hs' : Y.src (Y.inv ψ) = Y.PObj.smoothVal y := by rw [Y.src_inv, ht]
  have ht' : Y.tgt (Y.inv ψ) = F.obj x := by rw [Y.tgt_inv, hs]
  set k' := Y.isotropyConj (Y.inv ψ) hs' ht' k with hk'def
  obtain ⟨φ, hφs, hφt, hφe⟩ := (F.full_iff.1 hfull) x x k'.val k'.src_val k'.tgt_val
  set g : X.Isotropy x := ⟨φ, hφs, hφt⟩
  have hg : F.isotropyHom x g = k' := GroupoidStr.Isotropy.ext hφe
  have hgk : F.mor g.val = Y.comp (Y.comp (Y.inv ψ) k.val) (Y.inv (Y.inv ψ)) :=
    congrArg GroupoidStr.Isotropy.val hg
  rw [EpGroupoid.mem_trivialSubgroup, ← Y.isotropyConj_mem_trivialSet_iff (Y.inv ψ) hs' ht',
    ← hk'def, ← hg, F.isotropyHom_mem_trivialSet_iff hd]
  have hk1 : k.val ∈ Y.PMor.levelSet 1 :=
    (Y.mem_levelSet_src_iff _ 1).1 (by rw [k.src_val]; exact mem_iInter.1 hyS 1)
  have hc : Y.src (Y.inv ψ) = Y.tgt k.val := by rw [Y.src_inv, k.tgt_val, ht]
  have hk' : ∀ b : Y.PObj.TangentSpace, Y.PObj.levelVal 1 (Y.PObj.tangentProj b) = F.obj x →
      Y.tangentMor (F.mor g.val) b = b := by
    intro b hb
    have hbψ : Y.PObj.levelVal 1 (Y.PObj.tangentProj b) = Y.src ψ := hb.trans hs.symm
    have hTψ : Y.PObj.levelVal 1 (Y.PObj.tangentProj (Y.tangentMor ψ b)) =
        Y.PObj.smoothVal y := (Y.levelVal_tangentProj_tangentMor hψ1 hbψ).trans ht
    have hfib : Y.tangentMor ψ b ∈ Y.PObj.tangentFiber (Y.PObj.smoothIncl y 1) :=
      MPolyfold.level_ext hTψ
    rw [hgk, GroupoidStr.inv_inv,
      Y.tangentMor_comp hψ1 (by rw [Y.src_comp _ _ hc, k.src_val, ht]) hbψ,
      Y.tangentMor_comp hk1 hc (by rw [hTψ, k.src_val]), hk _ hfib,
      Y.tangentMor_inv_tangentMor hψ1 hbψ]
  refine hX g fun v hv => ?_
  have hvb : X.PObj.levelVal 1 (X.PObj.tangentProj v) = x := by rw [hv]; rfl
  have hg1 : g.val ∈ X.PMor.levelSet 1 :=
    (X.mem_levelSet_src_iff _ 1).1 (by rw [g.src_val]; exact hx1)
  have hvs : X.PObj.levelVal 1 (X.PObj.tangentProj v) = X.src g.val := hvb.trans g.src_val.symm
  have hTv : X.PObj.levelVal 1 (X.PObj.tangentProj (X.tangentMor g.val v)) = x :=
    (X.levelVal_tangentProj_tangentMor hg1 hvs).trans g.tgt_val
  refine hd.injOn_tangentFiber (X.PObj.tangentProj v) (MPolyfold.level_ext (hTv.trans hvb.symm))
    rfl ?_
  change F.tangent.obj (X.tangentMor g.val v) = F.tangent.obj v
  rw [← F.tangentMor_mor hg1 hvs]
  exact hk' _ ((MPolyfold.levelVal_tangentProj_tangentMap F.isScSmoothMap_obj v).trans
    (by rw [hvb]))

/-- **The Zhou condition passes back along a functor which is a local sc-diffeomorphism on
objects**: (ZHOU) at `F(x)` gives (ZHOU) at `x` (the other half of Proposition 10.1.17). -/
theorem isZhouAt_of_isZhouAt_obj (hd : X.PObj.IsLocalScDiffeo Y.PObj F.obj)
    (x' : X.PObj.SmoothLevel)
    (hY : Y.IsZhouAt (Y.PObj.smoothMk (F.obj (X.PObj.smoothVal x'))
      ((hd.mem_smoothSet_iff _).2 (X.PObj.smoothVal_mem x')))) : X.IsZhouAt x' := by
  intro g hg
  have hxS : X.PObj.smoothVal x' ∈ X.PObj.smoothSet := X.PObj.smoothVal_mem x'
  have hFxS : F.obj (X.PObj.smoothVal x') ∈ Y.PObj.smoothSet := (hd.mem_smoothSet_iff _).2 hxS
  rw [EpGroupoid.mem_trivialSubgroup, ← F.isotropyHom_mem_trivialSet_iff hd]
  refine hY (F.isotropyHom _ g) fun b hb => ?_
  obtain ⟨a, ha, rfl⟩ := hd.tangentFiber_subset_image (X.PObj.smoothIncl x' 1)
    (Y.PObj.smoothIncl (Y.PObj.smoothMk _ hFxS) 1) rfl hb
  have hg1 : g.val ∈ X.PMor.levelSet 1 :=
    (X.mem_levelSet_src_iff _ 1).1 (by rw [g.src_val]; exact mem_iInter.1 hxS 1)
  have hab : X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src g.val := by
    rw [g.src_val, ha]
    rfl
  change Y.tangentMor (F.mor g.val) (F.tangent.obj a) = F.tangent.obj a
  rw [F.tangentMor_mor hg1 hab, hg a ha]

end EpFunctor


/-! ### The translation groupoid `G ⋉ O` -/

namespace EpGroupoid.Examples

variable {K : Type u} [Group K] [Finite K] [TopologicalSpace K] [DiscreteTopology K]
  {U : Type u} [TopologicalSpace U] [T2Space U] [ParacompactSpace U] [MulAction K U]
  {P : MPolyfold U} (hP : ∀ k : K, P.IsScSmoothMap P fun y => k • y)

/-- **In `K ⋉ U`, `g ∈ G_x` acts trivially iff `ĝ = id` near `x`.** -/
theorem action_mem_trivialSet_iff {x : U} (g : (actionEpGroupoid hP).Isotropy x) :
    g ∈ (actionEpGroupoid hP).trivialSet x ↔ ∀ᶠ q in 𝓝 x, g.val.1 • q = q := by
  have hgx : g.val = (g.val.1, x) := Prod.ext rfl g.src_val
  rw [EpGroupoid.mem_trivialSet_iff_eventually]
  constructor
  · intro h
    have hc : Tendsto (fun q : U => (g.val.1, q)) (𝓝 x) (𝓝 g.val) := by
      rw [hgx]
      exact (continuous_const.prodMk continuous_id).tendsto x
    filter_upwards [hc.eventually h] with q hq
    exact hq.symm
  · intro h
    obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.1 h
    have hN : ({g.val.1} ×ˢ W : Set (K × U)) ∈ 𝓝 g.val := by
      rw [hgx]
      exact ((isOpen_discrete _).prod hWo).mem_nhds ⟨rfl, hxW⟩
    filter_upwards [hN] with ψ hψ
    obtain ⟨h1, h2⟩ := hψ
    change ψ.2 = ψ.1 • ψ.2
    rw [show ψ.1 = g.val.1 from h1]
    exact (hW h2).symm

/-- **Chapter 7's tangent map of the morphism `(k, x)` of `K ⋉ U` is `T(k ∗ ·)`** on `T_xU`. -/
theorem action_tangentMor_eq {φ : K × U} (hφ : φ ∈ (actionEpGroupoid hP).PMor.levelSet 1)
    {α : P.TangentSpace} (hα : P.levelVal 1 (P.tangentProj α) = φ.2) :
    (actionEpGroupoid hP).tangentMor φ α = MPolyfold.tangentMap (hP φ.1) α := by
  set X := actionEpGroupoid hP
  rw [X.tangentMor_eq_tangentMapOn_hat hφ hα]
  set S := X.sheetAt φ
  have hd := S.isScDiffeoOn_src
  have hc : ContinuousOn S.srcInv S.srcSet := hd.isScSmoothOn_inv.continuousOn
  have hWo : IsOpen (S.srcSet ∩ S.srcInv ⁻¹' ({φ.1} ×ˢ univ)) :=
    hc.isOpen_inter_preimage hd.isScSmoothOn_inv.isOpen ((isOpen_discrete _).prod isOpen_univ)
  have hxW : φ.2 ∈ S.srcSet ∩ S.srcInv ⁻¹' ({φ.1} ×ˢ univ) := by
    refine ⟨X.src_mem_sheetAt φ, ?_⟩
    have h1 : S.srcInv (X.src φ) = φ := hd.left_inv φ (X.mem_sheetAt φ)
    change S.srcInv (X.src φ) ∈ ({φ.1} ×ˢ univ : Set (K × U))
    rw [h1]
    exact ⟨rfl, mem_univ _⟩
  have heq : EqOn (X.hat φ) (fun y => φ.1 • y) (S.srcSet ∩ S.srcInv ⁻¹' ({φ.1} ×ˢ univ)) := by
    intro y hy
    have h1 : (S.srcInv y).1 = φ.1 := hy.2.1
    have h2 : (S.srcInv y).2 = y := hd.right_inv y hy.1
    change (S.srcInv y).1 • (S.srcInv y).2 = φ.1 • y
    rw [h1, h2]
  have hk := (hP φ.1).mono hWo (subset_univ _)
  have hαW : α ∈ P.tangentPreimage (S.srcSet ∩ S.srcInv ⁻¹' ({φ.1} ×ˢ univ)) := by
    change P.levelVal 1 (P.tangentProj α) ∈ (S.srcSet ∩ S.srcInv ⁻¹' ({φ.1} ×ˢ univ))
    rw [hα]
    exact hxW
  rw [MPolyfold.tangentMapOn_congr (X.isScDiffeoOn_hat φ).isScSmoothOn hk hWo inter_subset_left
    subset_rfl heq hαW]
  exact MPolyfold.tangentMapOn_eq_tangentMap (hP φ.1) hk hαW

/-- **Every natural representation of `K ⋉ U` is the action**: `Γ(g, y) = (g, y)` on `U(x)`. -/
theorem action_Γ_eq {x : U} (R : (actionEpGroupoid hP).NaturalRep x)
    (g : (actionEpGroupoid hP).Isotropy x) {y : U} (hy : y ∈ R.U) : R.Γ g y = (g.val.1, y) := by
  have hgx : g.val = (g.val.1, x) := Prod.ext rfl g.src_val
  refine eqOn_sections_of_isPreconnected
    (actionEpGroupoid hP).isLocalScDiffeo_src.isLocallyInjective R.isConnected_U.isPreconnected
    (R.isScSmoothOn_Γ g).continuousOn
    ((continuous_const.prodMk continuous_id).continuousOn (s := R.U))
    (fun z hz => R.src_Γ g z hz) (fun _ _ => rfl) R.mem_U ?_ hy
  rw [R.Γ_self g]
  exact hgx

/-- **Every natural representation of `K ⋉ U` is the action**: `Φ(g)(y) = g ∗ y` on `U(x)`. -/
theorem action_Φ_eq {x : U} (R : (actionEpGroupoid hP).NaturalRep x)
    (g : (actionEpGroupoid hP).Isotropy x) {y : U} (hy : y ∈ R.U) : R.Φ g y = g.val.1 • y := by
  rw [← R.tgt_Γ g y hy, action_Γ_eq hP R g hy]
  rfl

/-- The element `(g, x)` of the isotropy group of a fixed point `x`. -/
def actionIsotropy {x : U} (g : K) (hg : g • x = x) : (actionEpGroupoid hP).Isotropy x :=
  ⟨(g, x), rfl, hg⟩

@[simp] theorem actionIsotropy_val_fst {x : U} (g : K) (hg : g • x = x) :
    (actionIsotropy hP g hg).val.1 = g := rfl

/-- `(g, x) ↦ g` identifies `G_x` with the stabilizer of `x`. -/
theorem action_isotropy_smul {x : U} (g : (actionEpGroupoid hP).Isotropy x) :
    g.val.1 • x = x := by
  have h := g.tgt_val
  have hs : g.val.2 = x := g.src_val
  change g.val.1 • g.val.2 = x at h
  rwa [hs] at h

theorem action_isotropy_eq {x : U} (g : (actionEpGroupoid hP).Isotropy x) :
    g = actionIsotropy hP g.val.1 (action_isotropy_smul hP g) :=
  GroupoidStr.Isotropy.ext (Prod.ext rfl g.src_val)

end EpGroupoid.Examples


/-! ### The raised ep-groupoids and the points over a point -/

namespace EP

/-- **The point of `X` under a point of `Xⁱ`** (the inclusions `Xⁱ → X`). -/
def liftVal (A : EP.{u}) : (i : ℕ) → (A.lift i).Obj → A.Obj
  | 0, p => p
  | i + 1, p => A.liftVal i ((A.lift i).X.PObj.levelVal 1 p)

/-- **Every point of `X_{i+m}` is under a point of `(Xⁱ)_m`.** -/
theorem exists_liftVal_eq (A : EP.{u}) :
    ∀ (i m : ℕ) (x : A.Obj), x ∈ A.X.PObj.levelSet (i + m) →
      ∃ p : (A.lift i).Obj, A.liftVal i p = x ∧ p ∈ (A.lift i).X.PObj.levelSet m
  | 0, m, x, hx => ⟨x, rfl, by rw [Nat.zero_add] at hx; exact hx⟩
  | i + 1, m, x, hx => by
    obtain ⟨p, hp, hpm⟩ := A.exists_liftVal_eq i (m + 1) x
      (by rwa [show i + (m + 1) = i + 1 + m by omega])
    refine ⟨(A.lift i).X.PObj.levelMk 1 p ((A.lift i).X.PObj.levelSet_antitone (by omega) hpm),
      hp, ?_⟩
    exact (MPolyfold.mem_shift_levelSet_iff _).2 hpm

/-- Every point of `X_i` is under a point of `Xⁱ`. -/
theorem exists_liftVal_eq_of_mem (A : EP.{u}) {i : ℕ} {x : A.Obj}
    (hx : x ∈ A.X.PObj.levelSet i) : ∃ p : (A.lift i).Obj, A.liftVal i p = x := by
  obtain ⟨p, hp, -⟩ := A.exists_liftVal_eq i 0 x hx
  exact ⟨p, hp⟩

end EP

/-! ### The printed conditions at `ō` for a uniformizer -/

namespace GroupoidalCategory.Uniformizer

open EpGroupoid.Examples

variable {C : GroupoidalCategory.{u}} (Ψ : C.Uniformizer)

/-- The translation ep-groupoid `G ⋉ O` of `Ψ` as an object of `EP`. -/
abbrev toEP : EP.{u} := ⟨Ψ.O, Ψ.G × Ψ.O, Ψ.ep⟩

/-- **`Tg = Tĝ`** (Definition 19.5.5): the tangent map of `ĝ = g ∗ ·`. -/
def tangentSmul (g : Ψ.G) : Ψ.P.TangentSpace → Ψ.P.TangentSpace :=
  MPolyfold.tangentMap (Ψ.smooth_smul g)

/-- `Tg` is Chapter 7's tangent map of the morphism `(g, ō)` of `G ⋉ O`. -/
theorem tangentMor_ep_eq {o : Ψ.O} (g : Ψ.G) (ho : o ∈ Ψ.P.levelSet 1)
    {v : Ψ.P.TangentSpace} (hv : Ψ.P.levelVal 1 (Ψ.P.tangentProj v) = o) :
    Ψ.ep.tangentMor (g, o) v = Ψ.tangentSmul g v :=
  action_tangentMor_eq Ψ.smooth_smul ((Ψ.ep.mem_levelSet_src_iff (g, o) 1).1 ho) hv

/-- **(ZHOU) at `ō`, as printed** (Definition 19.5.6): every `g` fixing `ō` with `Tg = id` on
`T_ōO` is the identity near `ō`. -/
def IsZhouAt (y : Ψ.P.SmoothLevel) : Prop :=
  ∀ g : Ψ.G, g • Ψ.P.smoothVal y = Ψ.P.smoothVal y →
    (∀ v ∈ Ψ.P.tangentFiber (Ψ.P.smoothIncl y 1), Ψ.tangentSmul g v = v) →
      ∀ᶠ q in 𝓝 (Ψ.P.smoothVal y), g • q = q

/-- **The printed (ZHOU) at `ō` is Chapter 7's (ZHOU) of `G ⋉ O` at `ō`.** -/
theorem isZhouAt_iff (y : Ψ.P.SmoothLevel) : Ψ.IsZhouAt y ↔ Ψ.ep.IsZhouAt y := by
  have h1 : Ψ.P.smoothVal y ∈ Ψ.P.levelSet 1 := mem_iInter.1 (Ψ.P.smoothVal_mem y) 1
  have hv : ∀ v ∈ Ψ.P.tangentFiber (Ψ.P.smoothIncl y 1),
      Ψ.P.levelVal 1 (Ψ.P.tangentProj v) = Ψ.P.smoothVal y := fun v hv => by
    rw [show Ψ.P.tangentProj v = Ψ.P.smoothIncl y 1 from hv]; rfl
  constructor
  · intro h g hT
    refine (action_mem_trivialSet_iff Ψ.smooth_smul g).2
      (h g.val.1 (action_isotropy_smul _ g) fun v hv' => ?_)
    have hgv : g.val = (g.val.1, Ψ.P.smoothVal y) := Prod.ext rfl g.src_val
    rw [← Ψ.tangentMor_ep_eq g.val.1 h1 (hv v hv'), ← hgv]
    exact hT v hv'
  · intro h g hg hT
    have := h (actionIsotropy Ψ.smooth_smul g hg) fun v hv' => by
      change Ψ.ep.tangentMor (g, Ψ.P.smoothVal y) v = v
      rw [Ψ.tangentMor_ep_eq g h1 (hv v hv')]
      exact hT v hv'
    exact (action_mem_trivialSet_iff Ψ.smooth_smul _).1 this

/-- **(LUC) at `ō`, as printed** (Definition 19.5.8): an open `G_ō`-invariant `U ∋ ō` such that
every `g ∈ G_ō` which is the identity on a nonempty open `V ⊆ U` is the identity on `U`. -/
def IsLUCAt (o : Ψ.O) : Prop :=
  ∃ U : Set Ψ.O, IsOpen U ∧ o ∈ U ∧ (∀ g : Ψ.G, g • o = o → MapsTo (g • ·) U U) ∧
    ∀ g : Ψ.G, g • o = o → ∀ V : Set Ψ.O, IsOpen V → V.Nonempty → V ⊆ U →
      (∀ q ∈ V, g • q = q) → ∀ q ∈ U, g • q = q

/-- **The printed (LUC) at `ō` is Chapter 7's (LUC) of `G ⋉ O` at `ō`** (a natural
representation with the property of Definition 7.2.18). -/
theorem isLUCAt_iff (o : Ψ.O) : Ψ.IsLUCAt o ↔ ∃ R : Ψ.ep.NaturalRep o, R.HasLUC := by
  constructor
  · rintro ⟨U, hU, ho, -, hL⟩
    obtain ⟨R, hRU⟩ := Ψ.ep.theorem_7_1_13 o hU ho
    refine ⟨R, fun g V hVo hVne hVU hV y hy => ?_⟩
    rw [action_Φ_eq _ R g hy]
    refine hL g.val.1 (action_isotropy_smul _ g) V hVo hVne (hVU.trans hRU) (fun q hq => ?_) y
      (hRU hy)
    rw [← action_Φ_eq _ R g (hVU hq)]
    exact hV q hq
  · rintro ⟨R, hR⟩
    refine ⟨R.U, R.isOpen_U, R.mem_U, fun g hg q hq => ?_, fun g hg V hVo hVne hVU hV q hq => ?_⟩
    · have := R.mapsTo_Φ (actionIsotropy _ g hg) hq
      rwa [action_Φ_eq _ R _ hq] at this
    · have := hR (actionIsotropy _ g hg) V hVo hVne hVU (fun y hy => by
        rw [action_Φ_eq _ R _ (hVU hy)]; exact hV y hy) q hq
      rwa [action_Φ_eq _ R _ hq] at this

/-- `|Ψ(q')| = |Ψ(q)|` iff `q'` and `q` have the same class in `G \ O`. -/
theorem π_obj_eq_iff {q q' : Ψ.O} :
    C.π (Ψ.obj q') = C.π (Ψ.obj q) ↔ Ψ.ep.π q' = Ψ.ep.π q := by
  constructor
  · intro h
    obtain ⟨φ, hs, ht⟩ := C.π_eq_π_iff.1 h.symm
    obtain ⟨k, hk, -⟩ := Ψ.exists_smul_eq_mor hs ht
    exact ((GroupoidStr.π_eq_π_iff _).2 ⟨(k, q), rfl, hk⟩).symm
  · intro h
    obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 h
    rw [← hs, ← ht]
    exact (C.π_eq_π_iff).2 ⟨Ψ.mor φ, Ψ.src_mor φ, Ψ.tgt_mor φ⟩

/-- **(LR) at `ō`, as printed** (Definition 19.5.10): arbitrarily small open `G_ō`-invariant
`U ∋ ō` such that every sc-diffeomorphism `β : U → U` with `|β(q)| = |q|` is `q ↦ g ∗ q` for some
`g ∈ G_ō`. -/
def IsLRAt (o : Ψ.O) : Prop :=
  ∀ N : Set Ψ.O, IsOpen N → o ∈ N → ∃ U ⊆ N, IsOpen U ∧ o ∈ U ∧
    (∀ g : Ψ.G, g • o = o → MapsTo (g • ·) U U) ∧
    ∀ β β' : Ψ.O → Ψ.O, Ψ.P.IsScDiffeoOn Ψ.P β β' U U →
      (∀ q ∈ U, C.π (Ψ.obj (β q)) = C.π (Ψ.obj q)) → ∃ g : Ψ.G, g • o = o ∧ ∀ q ∈ U, β q = g • q

/-- **Chapter 7's (LR) of `G ⋉ O` at `ō` gives the printed (LR) at `ō`.** -/
theorem isLRAt_of_isLRAt {o : Ψ.O} (h : Ψ.ep.IsLRAt o) : Ψ.IsLRAt o := by
  intro N hN ho
  obtain ⟨R, hRN, hR⟩ := h N hN ho
  refine ⟨R.U, hRN, R.isOpen_U, R.mem_U, fun g hg q hq => ?_, fun β β' hβ hπ => ?_⟩
  · have := R.mapsTo_Φ (actionIsotropy _ g hg) hq
    rwa [action_Φ_eq _ R _ hq] at this
  · obtain ⟨g, hg⟩ := hR β β' hβ fun y hy => (Ψ.π_obj_eq_iff).1 (hπ y hy)
    exact ⟨g.val.1, action_isotropy_smul _ g, fun q hq => by rw [hg q hq, action_Φ_eq _ R g hq]⟩

end GroupoidalCategory.Uniformizer


/-! ### The piece functors of a model are full -/

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {ι : Type u} (Ψ : ι → S.Unif)

/-- **`G_λ ⋉ O_λ → X_Ψ` is full** (for every family; Lemma 17.1.9). -/
theorem full_pieceFunctor (i : ι) (hc : Continuous (S.hat (Ψ i))) :
    (pieceFunctor Ψ i hc).toFunctor.Full := by
  refine (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => ?_
  obtain ⟨⟨j, k⟩, a⟩ := ψ
  have hs' : (⟨j, a.src⟩ : S.ModelObj Ψ) = ⟨i, x⟩ := hs
  have ht' : (⟨k, a.tgt⟩ : S.ModelObj Ψ) = ⟨i, x'⟩ := ht
  obtain ⟨hj, hsa⟩ := Sigma.mk.inj_iff.1 hs'
  obtain ⟨hk, hta⟩ := Sigma.mk.inj_iff.1 ht'
  subst hj hk
  have hsa : a.src = x := eq_of_heq hsa
  have hta : a.tgt = x' := eq_of_heq hta
  obtain ⟨g, hg, hgm⟩ := (Ψ k).1.toUniformizer.exists_smul_eq_mor
    (a.src_mor.trans (by rw [hsa])) (a.tgt_mor.trans (by rw [hta]))
  refine ⟨(g, x), rfl, hg, ?_⟩
  refine congrArg (Sigma.mk (β := fun p : ι × ι => S.Tr (Ψ p.1) (Ψ p.2)) (k, k)) ?_
  exact GroupoidStr.TransitionSet.ext hsa.symm hgm (hg.trans hta.symm)

/-- `q ↦ q_λ` is a local sc-diffeomorphism `O_λ → ⊔ O_μ`. -/
theorem isLocalScDiffeo_pieceFunctor_obj (i : ι) (hc : Continuous (S.hat (Ψ i))) :
    (Ψ i).1.toUniformizer.ep.PObj.IsLocalScDiffeo (S.modelEP Ψ).X.PObj
      (pieceFunctor Ψ i hc).obj :=
  MPolyfold.isLocalScDiffeo_sigmaMk (fun i => (Ψ i).1.P) i

end GCT.PolyfoldConstruction

/-! ### The conditions for a basic construction -/

namespace GroupoidalCategory.BasicConstruction

open EpGroupoid.Examples GCT.PolyfoldConstruction

variable {C : GroupoidalCategory.{u}} (B : C.BasicConstruction)

/-- **`z ∈ |Sⁱ|`**: `z = |Ψ(q)|` with `q ∈ O_i` for some `Ψ` of `F`. -/
def IsLevelClass (i : ℕ) (z : C.OrbitSpace) : Prop :=
  ∃ (Ψ : B.U.Unif) (q : Ψ.1.O), q ∈ Ψ.1.P.levelSet i ∧ C.π (Ψ.1.obj q) = z

/-- **A smooth class** `z ∈ |S|`: `z = |Ψ(q)|` with `q ∈ O_∞` for some `Ψ` of `F`. -/
def IsSmoothClass (z : C.OrbitSpace) : Prop :=
  ∃ (Ψ : B.U.Unif) (q : Ψ.1.O), q ∈ Ψ.1.P.smoothSet ∧ C.π (Ψ.1.obj q) = z

/-- **Levels do not depend on the uniformizer**: if `|Ψ(q)| = |Ψ'(q')|`, then `q ∈ O_m` iff
`q' ∈ O'_m` (the transition map `f_h` with `h = (q, φ, q')` is an sc-diffeomorphism near `q`). -/
theorem mem_levelSet_iff_of_π_eq {Ψ Ψ' : B.U.Unif} {q : Ψ.1.O} {q' : Ψ'.1.O}
    (h : C.π (Ψ.1.obj q) = C.π (Ψ'.1.obj q')) (m : ℕ) :
    q ∈ Ψ.1.P.levelSet m ↔ q' ∈ Ψ'.1.P.levelSet m := by
  obtain ⟨φ, hs, ht⟩ := C.π_eq_π_iff.1 h
  let a : Ψ.1.Trans Ψ'.1 := ⟨q, φ, q', hs, ht⟩
  obtain ⟨g, hg⟩ := B.rep.diffeo Ψ Ψ' a
  have := hg.mem_levelSet_iff (B.rep.mem_dom Ψ Ψ' a) m
  simp only [B.rep.map_src] at this
  exact this.symm

theorem mem_smoothSet_iff_of_π_eq {Ψ Ψ' : B.U.Unif} {q : Ψ.1.O} {q' : Ψ'.1.O}
    (h : C.π (Ψ.1.obj q) = C.π (Ψ'.1.obj q')) :
    q ∈ Ψ.1.P.smoothSet ↔ q' ∈ Ψ'.1.P.smoothSet := by
  simp only [MPolyfold.smoothSet, mem_iInter, B.mem_levelSet_iff_of_π_eq h]

/-- **2021 Definition 19.5.5, p. 889**: for `g` fixing `ō`, `Tg = Tĝ(ō)` maps `T_ōO` to itself,
with inverse `Tg⁻¹`, and it is Chapter 7's tangent map of the morphism `(g, ō)` of `G ⋉ O`. -/
theorem definition_19_5_5 (Ψ : C.Uniformizer) {o : Ψ.O} {g : Ψ.G} (hg : g • o = o)
    (x₁ : Ψ.P.Level 1) (hx₁ : Ψ.P.levelVal 1 x₁ = o) :
    (∀ v ∈ Ψ.P.tangentFiber x₁, Ψ.tangentSmul g v ∈ Ψ.P.tangentFiber x₁) ∧
      (∀ v ∈ Ψ.P.tangentFiber x₁, Ψ.tangentSmul g⁻¹ (Ψ.tangentSmul g v) = v) ∧
      (∀ v ∈ Ψ.P.tangentFiber x₁, Ψ.ep.tangentMor (g, o) v = Ψ.tangentSmul g v) := by
  have ho : o ∈ Ψ.P.levelSet 1 := hx₁ ▸ MPolyfold.levelVal_mem x₁
  have hv : ∀ v ∈ Ψ.P.tangentFiber x₁, Ψ.P.levelVal 1 (Ψ.P.tangentProj v) = o := fun v hv => by
    rw [show Ψ.P.tangentProj v = x₁ from hv, hx₁]
  have hT : ∀ (k : Ψ.G) (v : Ψ.P.TangentSpace), Ψ.P.levelVal 1 (Ψ.P.tangentProj v) = o →
      k • o = o → Ψ.P.levelVal 1 (Ψ.P.tangentProj (Ψ.tangentSmul k v)) = o := by
    intro k v hvo hk
    rw [Uniformizer.tangentSmul, MPolyfold.levelVal_tangentProj_tangentMap, hvo, hk]
  have hginv : g⁻¹ • o = o := by rw [inv_smul_eq_iff, hg]
  refine ⟨fun v hv' => MPolyfold.level_ext ((hT g v (hv v hv') hg).trans hx₁.symm),
    fun v hv' => ?_, fun v hv' => Ψ.tangentMor_ep_eq g ho (hv v hv')⟩
  have hφ : (g, o) ∈ Ψ.ep.PMor.levelSet 1 := (Ψ.ep.mem_levelSet_src_iff (g, o) 1).1 ho
  have e := Ψ.ep.tangentMor_inv_tangentMor hφ (hv v hv')
  have hinv : Ψ.ep.inv (g, o) = (g⁻¹, o) := Prod.ext rfl hg
  rw [hinv, Ψ.tangentMor_ep_eq g ho (hv v hv'),
    Ψ.tangentMor_ep_eq g⁻¹ ho (hT g v (hv v hv') hg)] at e
  exact e

/-- **2021 Definition 19.5.6, p. 889: (ZHOU) for a basic construction**: for every smooth
`z ∈ |S|` there are `α_z` with `z = |α_z|`, `Ψ ∈ F(α_z)` and `ō` with `Ψ(ō) = α_z` such that
every `g` fixing `ō` with `Tg = id` is the identity near `ō`. -/
def IsZhou : Prop :=
  ∀ z, B.IsSmoothClass z → ∃ (α : C.Obj) (Ψ : C.Uniformizer) (_ : Ψ ∈ B.U.F α)
    (y : Ψ.P.SmoothLevel), C.π α = z ∧ Ψ.obj (Ψ.P.smoothVal y) = α ∧ Ψ.IsZhouAt y

/-- **2021 Definition 19.5.8, p. 889: (LUC) for a basic construction**: for every `z ∈ |S|`
there are `α_z`, `Ψ ∈ F(α_z)` and `ō` with `Ψ(ō) = α_z` with the property `IsLUCAt`. -/
def IsLUC : Prop :=
  ∀ z : C.OrbitSpace, ∃ (α : C.Obj) (Ψ : C.Uniformizer) (_ : Ψ ∈ B.U.F α) (o : Ψ.O),
    C.π α = z ∧ Ψ.obj o = α ∧ Ψ.IsLUCAt o

/-- **(LUC) for `(Fⁱ, 𝓕ⁱ)`** (Definition 19.5.8, as we read it): for every `z ∈ |Sⁱ|` there are
`α_z`, `Ψ ∈ F(α_z)` and the point `ōⁱ` of `(G ⋉ O)ⁱ` over `ō` with Chapter 7's (LUC) at
`ōⁱ`. -/
def IsLUCLevel (i : ℕ) : Prop :=
  ∀ z, B.IsLevelClass i z → ∃ (α : C.Obj) (Ψ : C.Uniformizer) (_ : Ψ ∈ B.U.F α)
    (p : (Ψ.toEP.lift i).Obj), C.π α = z ∧ Ψ.obj (Ψ.toEP.liftVal i p) = α ∧
      ∃ R : (Ψ.toEP.lift i).X.NaturalRep p, R.HasLUC

/-- **2021 Definition 19.5.8, p. 889: (SLUC) for a basic construction**: (LUC) for every
`(Fⁱ, 𝓕ⁱ)`. -/
def IsSLUC : Prop := ∀ i, B.IsLUCLevel i

/-- **2021 Definition 19.5.10, p. 890: (LR) for a basic construction**: for every `z ∈ |S|`
there are `α_z`, `Ψ ∈ F(α_z)` and `ō` with `Ψ(ō) = α_z` with the property `IsLRAt`. -/
def IsLR : Prop :=
  ∀ z : C.OrbitSpace, ∃ (α : C.Obj) (Ψ : C.Uniformizer) (_ : Ψ ∈ B.U.F α) (o : Ψ.O),
    C.π α = z ∧ Ψ.obj o = α ∧ Ψ.IsLRAt o

/-- **(LR) for `(Fⁱ, 𝓕ⁱ)`** (Definition 19.5.10, as we read it): Chapter 7's (LR) of
`(G ⋉ O)ⁱ` at the point over `ō`. -/
def IsLRLevel (i : ℕ) : Prop :=
  ∀ z, B.IsLevelClass i z → ∃ (α : C.Obj) (Ψ : C.Uniformizer) (_ : Ψ ∈ B.U.F α)
    (p : (Ψ.toEP.lift i).Obj), C.π α = z ∧ Ψ.obj (Ψ.toEP.liftVal i p) = α ∧
      (Ψ.toEP.lift i).X.IsLRAt p

/-- **2021 Definition 19.5.10, p. 890: (SLR) for a basic construction**: (LR) for every
`(Fⁱ, 𝓕ⁱ)`. -/
def IsSLR : Prop := ∀ i, B.IsLRLevel i

/-! ### Proposition 19.5.7 -/

variable {B} {hB : B.U.HasClassUniformizers} (hm : @MetrizableSpace C.OrbitSpace (B.natTop hB))

/-- **2021 Proposition 19.5.7, p. 889**: if `T` is metrizable and the basic construction
satisfies (ZHOU), the polyfold `(S, F, M)` satisfies (ZHOU) (Definition 17.1.22): the model of
the covering family of the uniformizers `Ψ_z` of (ZHOU) satisfies Chapter 7's (ZHOU), since every
smooth object of the model is isomorphic to some `ō_z` (Lemma 17.1.15) and the piece functor
`G ⋉ O → X_Ψ` is full and a local sc-diffeomorphism on objects. -/
theorem proposition_19_5_7 (h : B.IsZhou) : (toPolyfoldConstruction hm).IsZhou := by
  set S := toPolyfoldConstruction hm
  have key : ∀ z : C.OrbitSpace, ∃ (α : C.Obj) (Ψ : C.Uniformizer) (_ : Ψ ∈ B.U.F α),
      C.π α = z ∧ (B.IsSmoothClass z →
        ∃ y : Ψ.P.SmoothLevel, Ψ.obj (Ψ.P.smoothVal y) = α ∧ Ψ.IsZhouAt y) := by
    intro z
    by_cases hz : B.IsSmoothClass z
    · obtain ⟨α, Ψ, hΨ, y, hα, hy, hZ⟩ := h z hz
      exact ⟨α, Ψ, hΨ, hα, fun _ => ⟨y, hy, hZ⟩⟩
    · obtain ⟨α, hα, Ψ, hΨ⟩ := hB z
      exact ⟨α, Ψ, hΨ, hα, fun h' => absurd h' hz⟩
  choose α Ψ hΨ hα hy using key
  let Φ : C.OrbitSpace → S.Unif := fun z => ⟨toLocalUniformizer hm (hΨ z), α z, hΨ z⟩
  have hcov : ⋃ z, (Φ z).1.footprint = univ := eq_univ_of_forall fun z => mem_iUnion.2
    ⟨z, by
      obtain ⟨-, hz⟩ := B.theorem_19_2_2_three hB (hΨ z)
      rw [hα z] at hz
      exact hz⟩
  refine ⟨⟨C.OrbitSpace, Φ, hcov⟩, (EpGroupoid.isZhou_iff_forall_isZhouAt _).2 fun y => ?_⟩
  rcases hyv : (S.modelEP Φ).X.PObj.smoothVal y with ⟨j, q⟩
  have hyS : (⟨j, q⟩ : S.ModelObj Φ) ∈ (S.modelEP Φ).X.PObj.smoothSet :=
    hyv ▸ (S.modelEP Φ).X.PObj.smoothVal_mem y
  have hq : q ∈ (Ψ j).P.smoothSet :=
    ((MPolyfold.isLocalScDiffeo_sigmaMk (fun i => (Φ i).1.P) j).mem_smoothSet_iff q).1 hyS
  have hzS : B.IsSmoothClass (C.π ((Ψ j).obj q)) := ⟨⟨Ψ j, α j, hΨ j⟩, q, hq, rfl⟩
  set z := C.π ((Ψ j).obj q) with hzdef
  obtain ⟨y', hy'o, hZ⟩ := hy z hzS
  have hc := continuous_hat hm (Φ z)
  have hX : (Ψ z).ep.IsZhouAt y' := ((Ψ z).isZhouAt_iff y').1 hZ
  obtain ⟨φ, hφs, hφt⟩ := C.π_eq_π_iff.1
    (show C.π ((Ψ z).obj ((Ψ z).P.smoothVal y')) = C.π ((Ψ j).obj q) by rw [hy'o, hα z])
  let ψ : S.ModelMor Φ := ⟨(z, j), ⟨(Ψ z).P.smoothVal y', φ, q, hφs, hφt⟩⟩
  exact (pieceFunctor Φ z hc).isZhouAt_of_isZhouAt (isLocalScDiffeo_pieceFunctor_obj Φ z hc)
    (full_pieceFunctor Φ z hc) ((Ψ z).P.smoothVal_mem y') hX y (ψ := ψ) rfl hyv.symm

/-- **Under (ZHOU) of the polyfold `(S, F, M)`, every translation groupoid `G ⋉ O` of a
uniformizer of `F` satisfies Chapter 7's (ZHOU)** (the model of a covering family containing
`Ψ` satisfies (ZHOU), Proposition 17.1.24, and (ZHOU) passes back along `G ⋉ O → X_Ψ`). -/
theorem isZhou_toEP_of_isZhou (h : (toPolyfoldConstruction hm).IsZhou) (Ψ : B.U.Unif) :
    Ψ.1.ep.IsZhou := by
  set S := toPolyfoldConstruction hm
  obtain ⟨c, hc⟩ := h
  let Φ : Option c.ι → S.Unif := fun o => o.elim (ofUnif hm Ψ) c.Ψ
  have hcov : ⋃ o, (Φ o).1.footprint = univ := eq_univ_of_forall fun z => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (c.cover.symm ▸ mem_univ z)
    exact mem_iUnion.2 ⟨some i, hi⟩
  have hZ : (S.modelEP Φ).X.IsZhou := IsZhou.model ⟨c, hc⟩ ⟨Option c.ι, Φ, hcov⟩
  have hd := isLocalScDiffeo_pieceFunctor_obj Φ none (continuous_hat hm (Φ none))
  exact (EpGroupoid.isZhou_iff_forall_isZhouAt _).2 fun x' =>
    (pieceFunctor Φ none (continuous_hat hm (Φ none))).isZhouAt_of_isZhouAt_obj hd x' (hZ _)

include hm in
/-- **2021 Proposition 19.5.11, p. 890**: (ZHOU) for the basic construction implies (SLUC) and
(SLR) (and, for `i = 0`, the printed (LUC) and (LR)); read under the standing assumption of §19.5
that `T` is metrizable.  Through Proposition 19.5.7, `isZhou_toEP_of_isZhou` and Theorems 7.4.13
and 7.4.24 for the translation groupoids `G ⋉ O`. -/
theorem proposition_19_5_11 (h : B.IsZhou) : B.IsSLUC ∧ B.IsSLR ∧ B.IsLUC ∧ B.IsLR := by
  have hE := isZhou_toEP_of_isZhou hm (proposition_19_5_7 hm h)
  have hpt : ∀ z, ∃ (α : C.Obj) (Ψ : C.Uniformizer) (_ : Ψ ∈ B.U.F α) (o : Ψ.O),
      C.π α = z ∧ Ψ.obj o = α := fun z => by
    obtain ⟨α, hα, Ψ, hΨ⟩ := hB z
    obtain ⟨o, ho⟩ := B.U.isAt α Ψ hΨ
    exact ⟨α, Ψ, hΨ, o, hα, ho⟩
  have hlev : ∀ i z, B.IsLevelClass i z → ∃ (α : C.Obj) (Ψ : C.Uniformizer) (hΨ : Ψ ∈ B.U.F α)
      (p : (Ψ.toEP.lift i).Obj), C.π α = z ∧ Ψ.obj (Ψ.toEP.liftVal i p) = α := by
    intro i z hz
    obtain ⟨Ψ₀, q₀, hq₀, hz₀⟩ := hz
    obtain ⟨α, Ψ, hΨ, o, hα, ho⟩ := hpt z
    have hoi : o ∈ Ψ.P.levelSet i :=
      (B.mem_levelSet_iff_of_π_eq (Ψ := Ψ₀) (Ψ' := ⟨Ψ, α, hΨ⟩)
        (by rw [hz₀]; change z = C.π (Ψ.obj o); rw [ho, hα]) i).1 hq₀
    obtain ⟨p, hp⟩ := Ψ.toEP.exists_liftVal_eq_of_mem hoi
    exact ⟨α, Ψ, hΨ, p, hα, by rw [hp, ho]⟩
  refine ⟨fun i z hz => ?_, fun i z hz => ?_, fun z => ?_, fun z => ?_⟩
  · obtain ⟨α, Ψ, hΨ, p, hα, hp⟩ := hlev i z hz
    exact ⟨α, Ψ, hΨ, p, hα, hp, Ψ.toEP.theorem_7_4_13_all_of_isZhou (hE ⟨Ψ, α, hΨ⟩) i p⟩
  · obtain ⟨α, Ψ, hΨ, p, hα, hp⟩ := hlev i z hz
    exact ⟨α, Ψ, hΨ, p, hα, hp, Ψ.toEP.theorem_7_4_24_all_of_isZhou (hE ⟨Ψ, α, hΨ⟩) i p⟩
  · obtain ⟨α, Ψ, hΨ, o, hα, ho⟩ := hpt z
    exact ⟨α, Ψ, hΨ, o, hα, ho,
      (Ψ.isLUCAt_iff o).2 (Ψ.toEP.theorem_7_4_13_all_of_isZhou (hE ⟨Ψ, α, hΨ⟩) 0 o)⟩
  · obtain ⟨α, Ψ, hΨ, o, hα, ho⟩ := hpt z
    exact ⟨α, Ψ, hΨ, o, hα, ho,
      Ψ.isLRAt_of_isLRAt (Ψ.toEP.theorem_7_4_24_all_of_isZhou (hE ⟨Ψ, α, hΨ⟩) 0 o)⟩

end GroupoidalCategory.BasicConstruction

end Polyfold
