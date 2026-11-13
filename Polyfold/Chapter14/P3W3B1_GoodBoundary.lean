import Polyfold.Chapter13.P3D_SymmetricOn
import Polyfold.Chapter7.TameBoundaryEp
import Polyfold.Chapter7.LocConnected

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.1, pp. 638–642:
**Proposition 14.1.1** (good open neighbourhoods) and **Definition 14.1.2** (good open
neighbourhood in `∂X`).  The 2017 text has the definition (Definition 14.1) and states the
proposition inside the discussion before it; the 2021 edition adds the proof.

# Good open neighbourhoods at the boundary

## The text, paraphrased

(Proposition 14.1.1) In a tame ep-groupoid every `x ∈ ∂X` has arbitrarily small open
neighbourhoods `V(x)` in the object space with (1) `V(x)` and `V(x) ∩ ∂X` connected, (2) the natural
`G_x`-action on `V(x)`, (3) `t : s⁻¹(cl_X V(x)) → X` proper, (4) `d_X(x)` connected components
`θ_i` of `{y ∈ V(x) | d_X(y) = 1}` whose closures `θ̄_i` in `V(x)` contain `x`, with
`d_X(y) = #{i | y ∈ θ̄_i}` on `V(x)` and `V(x) ∩ ∂X = ⋃ θ̄_i`.  The proof works in a tame chart.
(Definition 14.1.2) A good open neighbourhood `U(x)` in `∂X` is `V(x) ∩ ∂X` for such a `V(x)`.

## What is formalized

* `HasBoundaryFaces x V θ`: condition (4) for `θ : Fin (d_X(x)) → Set Obj` (distinct components
  of `V ∩ {d_X = 1}`, closures in `V` through `x`, the counting formula).
  `HasBoundaryFaces.inter_boundary_eq` is (4)(c).
* **Definition 14.1.2**: `IsGoodBoundaryNbhd V` for a neighbourhood `V : X.NatNbhd x` with the
  natural `G_x`-action (agent G's reading of "admits the natural `G_x`-action");
  `NatNbhd.bdry V = V.U ∩ ∂X` is the good open neighbourhood `U(x)` in `∂X`.  The remarks after the
  definition: `IsGoodBoundaryNbhd.mem_boundary` (only points of `∂X` have one),
  `NatNbhd.mapsTo_Φ_bdry` (`U(x)` is `G_x`-invariant), `IsGoodBoundaryNbhd.bdry_eq`
  (`U(x) = ⋃ θ̄_i`).
* **Proposition 14.1.1**: `proposition_14_1_1`, inside any open `W ∋ x`; the relative form
  `exists_isGoodBoundaryNbhd_le` keeps a given natural action (`V ≤ N`), which is what refinements
  of good systems need (Theorem 14.1.6, Lemma 14.2.1).

## Proof (not the text's chart argument)

The proof uses Part I's abstract face calculus (`Chapter2/TameBoundary.lean`, valid for the
degeneracy index of every tame M-polyfold, `MPolyfold.isCornerIndex_degIndex`): start from an
invariant `N' ⊆ W ∩ D` (`D` a neighbourhood all of whose open subsets are face-structured), pass to
the centred part `V₁ = reach N' x` (every face of `V₁` contains `x`), and take the component `V`
of `x` in `V₁`.  `V₁` is `G_x`-invariant because the natural action is by index-preserving
homeomorphisms fixing `x` (faces go to faces, `IsDHomeoOn.facesThrough_image`); `V` is invariant
because `Φ(g)` fixes `x`.  The faces of `V` are the traces of those of `V₁`, so `V` is centred and
face-structured; the `θ̄_i` are its faces, `V ∩ ∂X` is their union, connected since all contain `x`.
The text's chart construction (the set `Q` with `∂C ∩ Q = Θ`) is not needed.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

/-! ### Two facts of the abstract face calculus -/

namespace TameBoundary

variable {X : Type u} [TopologicalSpace X] {d : X → ℕ}

/-- For `p` in the component `V` of `x` in `V₁`, the component of `p` in `V ∩ {d = 1}` is its
component in `V₁ ∩ {d = 1}`. -/
theorem connectedComponentIn_inter_deg_of_mem_cc {V₁ : Set X} {x p : X}
    (hp : p ∈ connectedComponentIn V₁ x) :
    connectedComponentIn (connectedComponentIn V₁ x ∩ {y | d y = 1}) p =
      connectedComponentIn (V₁ ∩ {y | d y = 1}) p := by
  refine Subset.antisymm (connectedComponentIn_mono _
    (inter_subset_inter_left _ (connectedComponentIn_subset _ _))) ?_
  by_cases hp1 : p ∈ V₁ ∩ {y | d y = 1}
  · have hC : connectedComponentIn (V₁ ∩ {y | d y = 1}) p ⊆ connectedComponentIn V₁ x := by
      have h1 := isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hp1) ((connectedComponentIn_subset _ _).trans inter_subset_left)
      rwa [← connectedComponentIn_eq hp] at h1
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hp1)
      (subset_inter hC ((connectedComponentIn_subset _ _).trans inter_subset_right))
  · rw [connectedComponentIn_eq_empty hp1]; exact empty_subset _

/-- The component of `x` in a set centred at `x` is centred at `x`. -/
theorem isCenteredAt_connectedComponentIn {V₁ : Set X} {x : X} (hcen : IsCenteredAt d x V₁)
    (hx : x ∈ V₁) : IsCenteredAt d x (connectedComponentIn V₁ x) := by
  rintro θ ⟨p, hp, hp1, rfl⟩
  have hp' : p ∈ V₁ := connectedComponentIn_subset _ _ hp
  have h := hcen _ (isFaceIn_faceAt hp' hp1)
  refine ⟨mem_connectedComponentIn hx, ?_⟩
  rw [connectedComponentIn_inter_deg_of_mem_cc hp]
  exact h.2

/-- A face is preconnected (the closure in `V` of a connected component). -/
theorem isPreconnected_faceAt (V : Set X) (p : X) : IsPreconnected (faceAt d V p) :=
  isPreconnected_connectedComponentIn.subset_closure (connectedComponentIn_subset_faceAt p)
    inter_subset_right

end TameBoundary

namespace EpGroupoid

open TameBoundary

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### Definition 14.1.2 -/

/-- **Condition (4) of Proposition 14.1.1 / Definition 14.1.2**: `θ₁, …, θ_{d_X(x)}` are distinct
connected components of `{y ∈ V | d_X(y) = 1}` whose closures `θ̄_i = V ∩ cl θ_i` in `V` contain
`x`, and `d_X(y) = #{i | y ∈ θ̄_i}` for `y ∈ V`. -/
structure HasBoundaryFaces (x : Obj) (V : Set Obj) (θ : Fin (X.PObj.degIndex x) → Set Obj) :
    Prop where
  injective : Injective θ
  isComponent : ∀ i, ∃ p ∈ V, X.PObj.degIndex p = 1 ∧
    θ i = connectedComponentIn (V ∩ {y | X.PObj.degIndex y = 1}) p
  mem_closure : ∀ i, x ∈ V ∩ closure (θ i)
  deg_eq : ∀ y ∈ V, {i | y ∈ V ∩ closure (θ i)}.encard = X.PObj.degIndex y

/-- **2021 Definition 14.1.2, p. 641 (2017: Definition 14.1)**: `V(x)`, an open neighbourhood of
`x` with the natural `G_x`-action (`V : X.NatNbhd x`, condition (1)), is a **good open
neighbourhood of `x` in `X`** if (2) `V(x)` and `V(x) ∩ ∂X` are connected, (3)
`t : s⁻¹(cl_X V(x)) → X` is proper, and (4) holds (`HasBoundaryFaces`).  The good open
neighbourhood in `∂X` is `U(x) = V(x) ∩ ∂X` (`NatNbhd.bdry`). -/
structure IsGoodBoundaryNbhd {x : Obj} (V : X.NatNbhd x) : Prop where
  isConnected : IsConnected V.U
  isConnected_bdry : IsConnected (V.U ∩ X.PObj.boundary)
  isProperSubset_closure : X.IsProperSubset (closure V.U)
  hasFaces : ∃ θ, X.HasBoundaryFaces x V.U θ

namespace NatNbhd

variable {X} {x : Obj}

/-- **The good open neighbourhood `U(x) = V(x) ∩ ∂X` in `∂X`** (Definition 14.1.2). -/
def bdry (V : X.NatNbhd x) : Set Obj := V.U ∩ X.PObj.boundary

theorem bdry_subset (V : X.NatNbhd x) : V.bdry ⊆ V.U := inter_subset_left

theorem bdry_subset_boundary (V : X.NatNbhd x) : V.bdry ⊆ X.PObj.boundary := inter_subset_right

/-- The natural action preserves the degeneracy index. -/
theorem degIndex_Φ (V : X.NatNbhd x) (g : X.Isotropy x) {y : Obj} (hy : y ∈ V.U) :
    X.PObj.degIndex (V.rep.Φ g y) = X.PObj.degIndex y :=
  (V.rep.isScDiffeoOn_Φ g).isDHomeoOn.deg_eq y (V.U_subset hy)

/-- **`U(x)` is `G_x`-invariant** (the remark after Definition 14.1.2). -/
theorem mapsTo_Φ_bdry (V : X.NatNbhd x) (g : X.Isotropy x) :
    MapsTo (V.rep.Φ g) V.bdry V.bdry := fun y hy => by
  refine ⟨V.mapsTo_Φ g hy.1, ?_⟩
  change 1 ≤ X.PObj.degIndex _
  rw [V.degIndex_Φ g hy.1]
  exact hy.2

/-- `U(x)` is open in `∂X`: it is the trace of the open set `V(x)`. -/
theorem bdry_eq_inter (V : X.NatNbhd x) : V.bdry = V.U ∩ X.PObj.boundary := rfl

theorem bdry_mono {V V' : X.NatNbhd x} (h : V'.U ⊆ V.U) : V'.bdry ⊆ V.bdry :=
  inter_subset_inter_left _ h

end NatNbhd

variable {X}

/-- **(4)(c)**: `V ∩ ∂X = ⋃ θ̄_i`. -/
theorem HasBoundaryFaces.inter_boundary_eq {x : Obj} {V : Set Obj}
    {θ : Fin (X.PObj.degIndex x) → Set Obj} (h : X.HasBoundaryFaces x V θ) :
    V ∩ X.PObj.boundary = ⋃ i, V ∩ closure (θ i) := by
  ext y
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨hy, hyb⟩
    have h1 : (1 : ℕ∞) ≤ {i | y ∈ V ∩ closure (θ i)}.encard := by
      rw [h.deg_eq y hy]; exact_mod_cast hyb
    obtain ⟨i, hi⟩ := Set.one_le_encard_iff_nonempty.1 h1
    exact ⟨i, hi⟩
  · rintro ⟨i, hy, hyc⟩
    refine ⟨hy, ?_⟩
    have h1 : (1 : ℕ∞) ≤ {i | y ∈ V ∩ closure (θ i)}.encard :=
      Set.one_le_encard_iff_nonempty.2 ⟨i, hy, hyc⟩
    rw [h.deg_eq y hy] at h1
    change 1 ≤ X.PObj.degIndex y
    exact_mod_cast h1

/-- **Definition 14.1.2, the remark after it**: `U(x) = ⋃_{i=1}^{d_X(x)} θ̄_i`. -/
theorem IsGoodBoundaryNbhd.bdry_eq {x : Obj} {V : X.NatNbhd x} (h : X.IsGoodBoundaryNbhd V) :
    ∃ θ, X.HasBoundaryFaces x V.U θ ∧ V.bdry = ⋃ i, V.U ∩ closure (θ i) := by
  obtain ⟨θ, hθ⟩ := h.hasFaces
  exact ⟨θ, hθ, hθ.inter_boundary_eq⟩

/-- Only boundary points have good open neighbourhoods (for `d_X(x) = 0` condition (4) forces
`V ∩ ∂X = ∅`, which is not connected). -/
theorem IsGoodBoundaryNbhd.mem_boundary {x : Obj} {V : X.NatNbhd x}
    (h : X.IsGoodBoundaryNbhd V) : x ∈ X.PObj.boundary := by
  by_contra hx
  have hx0 : X.PObj.degIndex x = 0 := by
    change ¬ 1 ≤ X.PObj.degIndex x at hx; omega
  obtain ⟨θ, hθ⟩ := h.hasFaces
  obtain ⟨y, hy⟩ := h.isConnected_bdry.nonempty
  rw [hθ.inter_boundary_eq] at hy
  obtain ⟨i, -⟩ := mem_iUnion.1 hy
  exact (hx0 ▸ i).elim0

/-! ### Proposition 14.1.1 -/

/-- **Proposition 14.1.1, relative form**: for `x ∈ ∂X` in a tame ep-groupoid, a neighbourhood
`N` of `x` with the natural action and `t : s⁻¹(cl N) → X` proper, and an open `W ∋ x`, there is a
good open neighbourhood `V ⊆ N ∩ W` of `x` (Definition 14.1.2) carrying the action of `N`. -/
theorem exists_isGoodBoundaryNbhd_le (hX : X.IsTame) {x : Obj} (hx : x ∈ X.PObj.boundary)
    (N : X.NatNbhd x) (hN : X.IsProperSubset (closure N.U)) {W : Set Obj} (hW : IsOpen W)
    (hxW : x ∈ W) :
    ∃ V : X.NatNbhd x, V.rep = N.rep ∧ V.U ⊆ N.U ∩ W ∧ X.IsGoodBoundaryNbhd V := by
  set d := X.PObj.degIndex with hd_def
  have hd : IsCornerIndex d := X.PObj.isCornerIndex_degIndex hX
  obtain ⟨D, hD, hxD, hfs⟩ := exists_nbhd_forall_isFaceStructuredOpen hd x
  obtain ⟨N', hrep, hsub⟩ := N.exists_restrict_subset (hW.inter hD) ⟨hxW, hxD⟩
  -- the centred part `V₁ = reach N' x`
  set V₁ := reach d N'.U x with hV₁_def
  have hV₁o : IsOpen V₁ := isOpen_reach hd N'.isOpen_U x
  have hxV₁ : x ∈ V₁ := mem_reach_self N'.mem_U
  have hV₁N' : V₁ ⊆ N'.U := reach_subset _ _
  have hdh : ∀ g, IsDHomeoOn d d (N'.rep.Φ g) N'.rep.U := fun g =>
    (N'.rep.isScDiffeoOn_Φ g).isDHomeoOn
  have himg : ∀ g, N'.rep.Φ g '' N'.U = N'.U := fun g => by
    refine Subset.antisymm (image_subset_iff.2 (N'.mapsTo_Φ g)) fun y hy => ?_
    exact ⟨N'.rep.Φ g⁻¹ y, N'.mapsTo_Φ g⁻¹ hy, N'.Φ_Φ_inv g hy⟩
  have hinv₁ : ∀ g, MapsTo (N'.rep.Φ g) V₁ V₁ := by
    intro g y hy
    refine ⟨N'.mapsTo_Φ g hy.1, fun γ hγ => ?_⟩
    have hft := (hdh g).facesThrough_image N'.U_subset hy.1
    rw [himg g] at hft
    rw [hft] at hγ
    obtain ⟨γ', hγ', rfl⟩ := hγ
    exact ⟨x, hy.2 γ' hγ', N'.rep.Φ_self g⟩
  -- the component `V` of `x` in `V₁`
  set V := connectedComponentIn V₁ x with hV_def
  have hVo : IsOpen V := X.PObj.isOpen_connectedComponentIn hV₁o x
  have hxV : x ∈ V := mem_connectedComponentIn hxV₁
  have hVV₁ : V ⊆ V₁ := connectedComponentIn_subset _ _
  have hVN' : V ⊆ N'.U := hVV₁.trans hV₁N'
  have hVN : V ⊆ N.U := fun y hy => (hsub (hVN' hy)).1
  have hVW : V ⊆ W := fun y hy => (hsub (hVN' hy)).2.1
  have hVD : V ⊆ D := fun y hy => (hsub (hVN' hy)).2.2
  have hinv : ∀ g, MapsTo (N'.rep.Φ g) V V := by
    intro g
    have hc : ContinuousOn (N'.rep.Φ g) V :=
      (N'.rep.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn.mono (hVN'.trans N'.U_subset)
    have h1 : N'.rep.Φ g '' V ⊆ V :=
      (isPreconnected_connectedComponentIn.image _ hc).subset_connectedComponentIn
        ⟨x, hxV, N'.rep.Φ_self g⟩ (image_subset_iff.2 fun y hy => hinv₁ g (hVV₁ hy))
    exact fun y hy => h1 ⟨y, hy, rfl⟩
  -- faces of `V`
  have hcen : IsCenteredAt d x V :=
    isCenteredAt_connectedComponentIn (isCenteredAt_reach hd N'.isOpen_U N'.mem_U) hxV₁
  have hfsV : IsFaceStructuredOpen d V := hfs V hVo hVD
  set F : Set (Set Obj) := {γ | IsFaceIn d V γ} with hF_def
  have hFx : facesThrough d V x = F := by
    ext γ; exact ⟨fun h => h.1, fun h => ⟨h, hcen γ h⟩⟩
  have hFenc : F.encard = d x := by rw [← hFx]; exact hfsV.2 x hxV
  have hFfin : F.Finite := Set.finite_of_encard_eq_coe hFenc
  have : Finite F := hFfin.to_subtype
  have hcard : Nat.card F = d x := by
    rw [Nat.card_coe_set_eq, Set.ncard_def, hFenc, ENat.toNat_natCast]
  let e : Fin (d x) ≃ F := (finCongr hcard.symm).trans (Finite.equivFin F).symm
  choose p hpV hp1 hpe using fun i => (e i).2
  set θ : Fin (d x) → Set Obj := fun i => connectedComponentIn (V ∩ {y | d y = 1}) (p i)
    with hθ_def
  have hθe : ∀ i, V ∩ closure (θ i) = (e i : Set Obj) := fun i => (hpe i).symm
  have hθ : X.HasBoundaryFaces x V θ := by
    refine ⟨fun i j hij => ?_, fun i => ⟨p i, hpV i, hp1 i, rfl⟩, fun i => ?_, fun y hy => ?_⟩
    · have : (e i : Set Obj) = e j := by rw [← hθe, ← hθe, hij]
      exact e.injective (Subtype.ext this)
    · rw [hθe]; exact hcen _ (e i).2
    · have hset : facesThrough d V y =
          (fun i => (e i : Set Obj)) '' {i | y ∈ V ∩ closure (θ i)} := by
        ext γ
        constructor
        · rintro ⟨hγ, hyγ⟩
          obtain ⟨i, hi⟩ := e.surjective ⟨γ, hγ⟩
          refine ⟨i, ?_, congrArg Subtype.val hi⟩
          change y ∈ V ∩ closure (θ i)
          rw [hθe, hi]; exact hyγ
        · rintro ⟨i, hi, rfl⟩
          refine ⟨(e i).2, ?_⟩
          change y ∈ V ∩ closure (θ i) at hi
          rwa [hθe] at hi
      have hinj : InjOn (fun i => (e i : Set Obj)) {i | y ∈ V ∩ closure (θ i)} :=
        fun i _ j _ hij => e.injective (Subtype.ext hij)
      rw [← hinj.encard_image, ← hset]
      exact hfsV.2 y hy
  -- `V ∩ ∂X` is connected
  have hbdry : V ∩ X.PObj.boundary = ⋃₀ (insert {x} F) := by
    ext y
    constructor
    · rintro ⟨hy, hyb⟩
      have h1 : (1 : ℕ∞) ≤ (facesThrough d V y).encard := by
        rw [hfsV.2 y hy]; exact_mod_cast hyb
      obtain ⟨γ, hγ, hyγ⟩ := Set.one_le_encard_iff_nonempty.1 h1
      exact ⟨γ, mem_insert_of_mem _ hγ, hyγ⟩
    · rintro ⟨γ, hγ, hyγ⟩
      rcases hγ with rfl | hγ
      · rw [mem_singleton_iff.1 hyγ]; exact ⟨hxV, hx⟩
      · exact ⟨hγ.subset hyγ, one_le_of_mem_isFaceIn hd hVo hγ hyγ⟩
  have hconn : IsConnected (V ∩ X.PObj.boundary) := by
    refine ⟨⟨x, hxV, hx⟩, ?_⟩
    rw [hbdry]
    refine isPreconnected_sUnion x _ ?_ ?_
    · rintro γ (rfl | hγ)
      · exact mem_singleton x
      · exact hcen γ hγ
    · rintro γ (rfl | ⟨q, -, -, rfl⟩)
      · exact isPreconnected_singleton
      · exact isPreconnected_faceAt V q
  -- assemble
  have hinvN : ∀ g, MapsTo (N.rep.Φ g) V V := fun g => hrep ▸ hinv g
  refine ⟨N.restrict V hVo hxV hVN hinvN, rfl, fun y hy => ⟨hVN hy, hVW hy⟩, ?_⟩
  exact ⟨isConnected_connectedComponentIn_iff.2 hxV₁, hconn,
    isProperMap_domRestrict_of_subset_of_isClosed X.continuous_src hN (closure_mono hVN)
      isClosed_closure, θ, hθ⟩

/-- **2021 Proposition 14.1.1, p. 638 (2017: the discussion before Definition 14.1)**: in a tame
ep-groupoid every `x ∈ ∂X` has, inside any open `W ∋ x`, an open neighbourhood `V(x)` with
(1) `V(x)` and `V(x) ∩ ∂X` connected, (2) the natural `G_x`-action, (3) `t : s⁻¹(cl_X V(x)) → X`
proper, (4) components `θ_1, …, θ_{d_X(x)}` of `{y ∈ V(x) | d_X(y) = 1}` with (a) `x ∈ θ̄_i`,
(b) `d_X(y) = #{i | y ∈ θ̄_i}` on `V(x)`, (c) `V(x) ∩ ∂X = ⋃ θ̄_i`. -/
theorem proposition_14_1_1 (hX : X.IsTame) {x : Obj} (hx : x ∈ X.PObj.boundary) {W : Set Obj}
    (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ V : X.NatNbhd x, V.U ⊆ W ∧ IsConnected V.U ∧ IsConnected (V.U ∩ X.PObj.boundary) ∧
      X.IsProperSubset (closure V.U) ∧
      ∃ θ, X.HasBoundaryFaces x V.U θ ∧ V.U ∩ X.PObj.boundary = ⋃ i, V.U ∩ closure (θ i) := by
  obtain ⟨N, hNW, hN⟩ := X.exists_natNbhd_isProperSubset x hW hxW
  obtain ⟨V, -, hVsub, hV⟩ := exists_isGoodBoundaryNbhd_le hX hx N hN hW hxW
  obtain ⟨θ, hθ⟩ := hV.hasFaces
  exact ⟨V, fun y hy => (hVsub hy).2, hV.isConnected, hV.isConnected_bdry,
    hV.isProperSubset_closure, θ, hθ, hθ.inter_boundary_eq⟩

/-- Good open neighbourhoods exist at every boundary point of a tame ep-groupoid
(Definition 14.1.2 is satisfiable), inside every open neighbourhood. -/
theorem exists_isGoodBoundaryNbhd (hX : X.IsTame) {x : Obj} (hx : x ∈ X.PObj.boundary)
    {W : Set Obj} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ V : X.NatNbhd x, V.U ⊆ W ∧ X.IsGoodBoundaryNbhd V := by
  obtain ⟨N, hNW, hN⟩ := X.exists_natNbhd_isProperSubset x hW hxW
  obtain ⟨V, -, hVsub, hV⟩ := exists_isGoodBoundaryNbhd_le hX hx N hN hW hxW
  exact ⟨V, fun y hy => (hVsub hy).2, hV⟩

end EpGroupoid

end Polyfold
