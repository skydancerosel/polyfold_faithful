import Polyfold.Chapter7.NaturalAction
import Polyfold.Chapter7.NaturalRep
import Polyfold.Chapter7.PartitionsOfUnity

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2021), Part III, §13.1 "Structure Result",
pp. 599–601: **Lemma 13.1.1** (p. 599), **Definition 13.1.2** (good system of open
neighbourhoods, p. 600), **Proposition 13.1.3** (p. 600) and **Definition 13.1.4** (refinement,
subordinate, p. 600).  (2017 text: §13.1, Lemma 13.1, Definition 13.1, Proposition 13.1,
Definition 13.2.)

# Good systems of neighbourhoods: the interface

## The text, paraphrased

(p. 599) Every object `x` of an ep-groupoid has an open neighbourhood `U(x)` with the natural
`G_x`-action such that `t : s⁻¹(cl_X U(x)) → X` is proper.  (Lemma 13.1.1) For a `G_x`-invariant
`V ⊆ U(x)`: `cl_X(V) ⊆ U(x)` if and only if `cl_{|X|}(|V|) ⊆ |U(x)|`.  (Definition 13.1.2) A
family `(U(x))_{x ∈ X}` of open neighbourhoods is a good system if (1) `t : s⁻¹(cl_X U(x)) → X` is
proper, (2) `U(x)` carries the natural `G_x`-action, (3) for all `x, x'` and every connected
component `Σ` of `𝒰(x, x') = {φ | s(φ) ∈ U(x), t(φ) ∈ U(x')}` the maps `s : Σ → U(x)` and
`t : Σ → U(x')` are sc-diffeomorphisms onto open subsets.  (Proposition 13.1.3) Replacing every
`U(x)` by a `G_x`-invariant open neighbourhood `Ũ(x) ⊆ U(x)` gives a good system.  (Definition
13.1.4) Refinements (`W(x) ⊆ U(x)`) and good systems subordinate to an open cover.

## What is formalized (namespace `Polyfold.EpGroupoid`)

* **"An open neighbourhood with the natural `G_x`-action"**: `NatNbhd X x`, an open `U ∋ x`
  inside the domain of a natural representation `rep : X.NaturalRep x` (Theorem 7.1.13) and
  invariant under its action `rep.Φ`.  API: `NatNbhd.ofRep`, `NatNbhd.restrict`,
  `NatNbhd.exists_restrict_subset` (invariant shrinking into any open `V ∋ x`),
  `exists_natNbhd_isProperSubset` (the neighbourhoods of p. 599 exist inside every open set),
  `NatNbhd.π_Φ`, `NatNbhd.exists_Γ_eq`, `NatNbhd.Γ_one`, `NatNbhd.Γ_mul`, `NatNbhd.Γ_inj`.
* **Lemma 13.1.1**: `lemma_13_1_1` (no invariance of `V` needed) and `lemma_13_1_1_book`.
* **`𝒰(A, B)`**: `morBetween A B`, `isOpen_morBetween`.
* **Condition (3) for one set of morphisms**: `IsDiffeoComponent C`; for open `C` it is the
  injectivity of `s` and `t` on `C` (`isDiffeoComponent_iff_injOn`), through
  `MPolyfold.IsLocalScDiffeo.isScDiffeoOn_invFunOn` (an injective local sc-diffeomorphism on an
  open set is an sc-diffeomorphism onto its open image).
* **Definition 13.1.2**: `GoodSystem X` (fields `nbhd`, `isProperSubset_closure`,
  `isDiffeoComponent`); `GoodSystem.U`, `GoodSystem.mor` (`𝒰(x, x')`), `GoodSystem.comp`
  (the component `connectedComponentIn (𝒰(x, x')) φ`), `isOpen_mor`, `isOpen_comp`,
  `isConnected_comp`, `mem_comp`, `comp_subset`, `injOn_src_comp`, `injOn_tgt_comp`,
  `srcInv`, `tgtInv` (the inverses of `s|Σ`, `t|Σ`) and their laws.
* **Partial good systems** (for Theorem 13.1.7): `IsGoodOn N Q` for a family `N` and a set `Q`,
  `GoodSystem.ofIsGoodOn`, `GoodSystem.isGoodOn`.
* **Proposition 13.1.3**: `GoodSystem.restrict` and `proposition_13_1_3`; the remark after it:
  `GoodSystem.exists_refinement_subset`.
* **Definition 13.1.4**: `GoodSystem.IsRefinement`, `GoodSystem.IsSubordinate`,
  `GoodSystem.isRefinement_restrict`.

## Reading

* **"Equipped with the natural `G_x`-action".**  The project's `NaturalRep` (Theorem 7.1.13)
  has a *connected* domain, needed for the homomorphism property.  Proposition 13.1.3 replaces
  `U(x)` by an arbitrary `G_x`-invariant open `Ũ(x) ⊆ U(x)`, which need not be connected.  We
  therefore read "`U(x)` equipped with the natural `G_x`-action" as an open `G_x`-invariant
  `U(x) ∋ x` inside the domain of a natural representation, acted on by its `Φ`, `Γ` (all
  properties of Theorem 7.1.13 hold on `U(x)` by restriction; only connectedness is not asked).
  This is `NatNbhd`.  With this reading Proposition 13.1.3 holds as printed.
* **Lemma 13.1.1** holds for every `V ⊆ U(x)`; the invariance of `V` is not used.
  Direction (1) ⇒ (2) uses only the properness of `cl_X(U(x))` (through Proposition 7.1.10);
  direction (2) ⇒ (1) only the natural action.  The sequences of the text are replaced by the
  filter `𝓝[V] y` and the finiteness of `G_x`.
* **Condition (3)**: "a connected component `Σ ⊆ 𝒰(x, x')`" is `connectedComponentIn
  (𝒰(x, x')) φ` for `φ ∈ 𝒰(x, x')`; "sc-diffeomorphism onto an open subset of `U(x)`" is
  `IsScDiffeoOn s σ Σ (s(Σ))` for some `σ` (open target is part of `IsScDiffeoOn`), and
  `s(Σ) ⊆ U(x)` is automatic.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

/-! ### An injective local sc-diffeomorphism on an open set -/

namespace MPolyfold

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ParacompactSpace M] [Nonempty M]
  {P : MPolyfold M} {N : Type v} [TopologicalSpace N] [T2Space N] [ParacompactSpace N]
  {Q : MPolyfold N}

/-- **An injective local sc-diffeomorphism is an sc-diffeomorphism onto its image**: if `f` is a
local sc-diffeomorphism injective on the open set `S`, then `f : S → f(S)` is an
sc-diffeomorphism onto the open set `f(S)`, with inverse `Function.invFunOn f S`. -/
theorem IsLocalScDiffeo.isScDiffeoOn_invFunOn {f : M → N} (hf : P.IsLocalScDiffeo Q f)
    {S : Set M} (hS : IsOpen S) (hinj : InjOn f S) :
    P.IsScDiffeoOn Q f (Function.invFunOn f S) S (f '' S) := by
  have hfS : IsOpen (f '' S) := hf.isOpenMap S hS
  have hmem : ∀ y ∈ f '' S, Function.invFunOn f S y ∈ S := fun y hy => by
    obtain ⟨a, ha, rfl⟩ := hy
    exact Function.invFunOn_mem ⟨a, ha, rfl⟩
  have hright : ∀ y ∈ f '' S, f (Function.invFunOn f S y) = y := fun y hy => by
    obtain ⟨a, ha, rfl⟩ := hy
    exact Function.invFunOn_eq ⟨a, ha, rfl⟩
  refine
    { isScSmoothOn := hf.isScSmoothMap.mono hS (subset_univ _)
      isScSmoothOn_inv := ?_
      mapsTo := fun a ha => mem_image_of_mem f ha
      mapsTo_inv := hmem
      left_inv := fun a ha => hinj.leftInvOn_invFunOn ha
      right_inv := hright }
  refine IsScSmoothOn.of_locally hfS fun y hy => ?_
  obtain ⟨a, haS, rfl⟩ := hy
  obtain ⟨W, V, σ, haW, hd⟩ := hf a
  have hd' := hd.restrict (hd.isOpen_source.inter hS) inter_subset_left
  refine ⟨V ∩ σ ⁻¹' (W ∩ S), hd'.isOpen_target, ?_, ?_, ?_⟩
  · refine ⟨hd.mapsTo haW, ?_⟩
    rw [mem_preimage, hd.left_inv a haW]
    exact ⟨haW, haS⟩
  · intro z hz
    exact ⟨σ z, hz.2.2, hd.right_inv z hz.1⟩
  · refine hd'.isScSmoothOn_inv.congr fun z hz => ?_
    have hzS : z ∈ f '' S := ⟨σ z, hz.2.2, hd.right_inv z hz.1⟩
    exact hinj hz.2.2 (hmem z hzS) ((hd.right_inv z hz.1).trans (hright z hzS).symm)

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### Continuity of composition -/

variable {X} in
/-- **Composition is continuous** (from Definition 7.1.3 (4)): if `f, g` are continuous on `S`
with `s(f a) = t(g a)`, then `a ↦ f(a) ∘ g(a)` is continuous on `S`. -/
theorem continuousOn_comp_of_continuousOn {α : Type*} [TopologicalSpace α] {S : Set α}
    {f g : α → Mor} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (h : ∀ a ∈ S, X.src (f a) = X.tgt (g a)) :
    ContinuousOn (fun a => X.comp (f a) (g a)) S := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor X.PMor
  let _ := (X.PMor.prod X.PMor).paracompactSpace_subtype (MPolyfold.fibredProduct X.src X.tgt)
  have hm := X.isScSmoothComp
  unfold IsScSmoothComp at hm
  have hc : Continuous fun p : MPolyfold.fibredProduct X.src X.tgt => X.comp p.1.1 p.1.2 :=
    continuousOn_univ.1 hm.continuousOn
  rw [continuousOn_iff_continuous_domRestrict] at hf hg ⊢
  have hpair : Continuous fun a : S =>
      (⟨(f a, g a), h a a.2⟩ : MPolyfold.fibredProduct X.src X.tgt) :=
    (hf.prodMk hg).subtype_mk _
  exact hc.comp hpair

/-! ### Open neighbourhoods with the natural action -/

/-- **An open neighbourhood `U(x)` equipped with the natural `G_x`-action** (§13.1, p. 599): an
open set `U ∋ x` inside the domain of a natural representation `rep` of `G_x` (Theorem 7.1.13),
invariant under the action `rep.Φ`.  (The domain `rep.U` is connected; `U` need not be.) -/
structure NatNbhd (x : Obj) where
  /-- The natural representation whose action `U` carries. -/
  rep : X.NaturalRep x
  /-- The neighbourhood `U(x)`. -/
  U : Set Obj
  isOpen_U : IsOpen U
  mem_U : x ∈ U
  U_subset : U ⊆ rep.U
  mapsTo_Φ : ∀ g, MapsTo (rep.Φ g) U U

namespace NatNbhd

variable {X} {x : Obj} (N : X.NatNbhd x)

/-- The domain of a natural representation, with its action. -/
def ofRep (R : X.NaturalRep x) : X.NatNbhd x :=
  ⟨R, R.U, R.isOpen_U, R.mem_U, subset_rfl, R.mapsTo_Φ⟩

@[simp] theorem ofRep_U (R : X.NaturalRep x) : (ofRep R).U = R.U := rfl

@[simp] theorem ofRep_rep (R : X.NaturalRep x) : (ofRep R).rep = R := rfl

/-- **Restriction** to a smaller invariant open neighbourhood. -/
def restrict (W : Set Obj) (hW : IsOpen W) (hxW : x ∈ W) (hWU : W ⊆ N.U)
    (hinv : ∀ g, MapsTo (N.rep.Φ g) W W) : X.NatNbhd x :=
  ⟨N.rep, W, hW, hxW, hWU.trans N.U_subset, hinv⟩

@[simp] theorem restrict_U (W : Set Obj) (hW : IsOpen W) (hxW : x ∈ W) (hWU : W ⊆ N.U)
    (hinv : ∀ g, MapsTo (N.rep.Φ g) W W) : (N.restrict W hW hxW hWU hinv).U = W := rfl

@[simp] theorem restrict_rep (W : Set Obj) (hW : IsOpen W) (hxW : x ∈ W) (hWU : W ⊆ N.U)
    (hinv : ∀ g, MapsTo (N.rep.Φ g) W W) : (N.restrict W hW hxW hWU hinv).rep = N.rep := rfl

theorem mem_rep_U {y : Obj} (hy : y ∈ N.U) : y ∈ N.rep.U := N.U_subset hy

theorem Φ_mem (g : X.Isotropy x) {y : Obj} (hy : y ∈ N.U) : N.rep.Φ g y ∈ N.U := N.mapsTo_Φ g hy

/-- The largest invariant open subset of `U ∩ V`: `⋂_g (U ∩ Φ(g)⁻¹(V))`. -/
def invariantCore (V : Set Obj) : Set Obj := ⋂ g, N.U ∩ N.rep.Φ g ⁻¹' V

theorem isOpen_invariantCore {V : Set Obj} (hV : IsOpen V) : IsOpen (N.invariantCore V) := by
  have := X.proposition_7_1_12 x
  exact isOpen_iInter_of_finite fun g =>
    ((N.rep.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn.mono N.U_subset).isOpen_inter_preimage
      N.isOpen_U hV

theorem invariantCore_subset (V : Set Obj) : N.invariantCore V ⊆ N.U ∩ V := fun y hy => by
  have h1 := mem_iInter.1 hy 1
  refine ⟨h1.1, ?_⟩
  have h2 := h1.2
  rwa [mem_preimage, N.rep.Φ_one y (N.U_subset h1.1)] at h2

theorem mem_invariantCore {V : Set Obj} (hx : x ∈ V) : x ∈ N.invariantCore V :=
  mem_iInter.2 fun g => ⟨N.mem_U, by rw [mem_preimage, N.rep.Φ_self]; exact hx⟩

theorem mapsTo_Φ_invariantCore (V : Set Obj) (g : X.Isotropy x) :
    MapsTo (N.rep.Φ g) (N.invariantCore V) (N.invariantCore V) := fun y hy =>
  mem_iInter.2 fun h => ⟨N.mapsTo_Φ g (mem_iInter.1 hy 1).1, by
    rw [mem_preimage, ← N.rep.Φ_mul h g y (N.U_subset (mem_iInter.1 hy 1).1)]
    exact (mem_iInter.1 hy (h * g)).2⟩

/-- **Invariant shrinking**: inside every open `V ∋ x` there is a smaller neighbourhood with the
same natural action. -/
theorem exists_restrict_subset {V : Set Obj} (hV : IsOpen V) (hx : x ∈ V) :
    ∃ N' : X.NatNbhd x, N'.rep = N.rep ∧ N'.U ⊆ N.U ∩ V :=
  ⟨N.restrict _ (N.isOpen_invariantCore hV) (N.mem_invariantCore hx)
      (fun _ hy => (N.invariantCore_subset V hy).1) (N.mapsTo_Φ_invariantCore V), rfl,
    N.invariantCore_subset V⟩

/-- `|Φ(g)(y)| = |y|`. -/
theorem π_Φ (g : X.Isotropy x) {y : Obj} (hy : y ∈ N.rep.U) : X.π (N.rep.Φ g y) = X.π y := by
  rw [← N.rep.tgt_Γ g y hy, ← X.π_src_eq_π_tgt, N.rep.src_Γ g y hy]

/-- Every morphism between points of `U(x)` is `Γ(g, s φ)`. -/
theorem exists_Γ_eq {φ : Mor} (hs : X.src φ ∈ N.U) (ht : X.tgt φ ∈ N.U) :
    ∃ g, N.rep.Γ g (X.src φ) = φ :=
  (N.rep.existsUnique_Γ φ (N.U_subset hs) (N.U_subset ht)).exists

theorem Γ_inj {g h : X.Isotropy x} {y : Obj} (hy : y ∈ N.U) :
    N.rep.Γ g y = N.rep.Γ h y ↔ g = h :=
  N.rep.Γ_inj (N.U_subset hy)

theorem Γ_one {y : Obj} (hy : y ∈ N.U) : N.rep.Γ 1 y = X.unit y := N.rep.Γ_one (N.U_subset hy)

theorem Γ_mul (g h : X.Isotropy x) {y : Obj} (hy : y ∈ N.U) :
    X.comp (N.rep.Γ g (N.rep.Φ h y)) (N.rep.Γ h y) = N.rep.Γ (g * h) y :=
  N.rep.Γ_mul g h (N.U_subset hy)

theorem Γ_inv (g : X.Isotropy x) {y : Obj} (hy : y ∈ N.U) :
    N.rep.Γ g⁻¹ (N.rep.Φ g y) = X.inv (N.rep.Γ g y) :=
  N.rep.Γ_inv g (N.U_subset hy)

theorem src_Γ (g : X.Isotropy x) {y : Obj} (hy : y ∈ N.U) : X.src (N.rep.Γ g y) = y :=
  N.rep.src_Γ g y (N.U_subset hy)

theorem tgt_Γ (g : X.Isotropy x) {y : Obj} (hy : y ∈ N.U) :
    X.tgt (N.rep.Γ g y) = N.rep.Φ g y :=
  N.rep.tgt_Γ g y (N.U_subset hy)

theorem Φ_inv_Φ (g : X.Isotropy x) {y : Obj} (hy : y ∈ N.U) : N.rep.Φ g⁻¹ (N.rep.Φ g y) = y :=
  N.rep.Φ_inv_Φ g (N.U_subset hy)

theorem Φ_Φ_inv (g : X.Isotropy x) {y : Obj} (hy : y ∈ N.U) : N.rep.Φ g (N.rep.Φ g⁻¹ y) = y :=
  N.rep.Φ_Φ_inv g (N.U_subset hy)

theorem Φ_mul (g h : X.Isotropy x) {y : Obj} (hy : y ∈ N.U) :
    N.rep.Φ (g * h) y = N.rep.Φ g (N.rep.Φ h y) :=
  N.rep.Φ_mul g h y (N.U_subset hy)

theorem Φ_one {y : Obj} (hy : y ∈ N.U) : N.rep.Φ 1 y = y := N.rep.Φ_one y (N.U_subset hy)

end NatNbhd

/-- **The neighbourhoods of p. 599 exist inside every open set**: for every open `W ∋ x` there is
an open neighbourhood `U(x) ⊆ W` with the natural `G_x`-action such that
`t : s⁻¹(cl_X U(x)) → X` is proper (Theorem 7.1.13 and Definition 7.1.3 (3), through the proof of
Theorem 7.5.7). -/
theorem exists_natNbhd_isProperSubset (x : Obj) {W : Set Obj} (hW : IsOpen W) (hx : x ∈ W) :
    ∃ N : X.NatNbhd x, N.U ⊆ W ∧ X.IsProperSubset (closure N.U) := by
  obtain ⟨R, V, hVo, hxV, hVinv, hVcl, hRW, hprop⟩ := X.exists_invariant_nhds_of_isOpen x hW hx
  exact ⟨⟨R, V, hVo, hxV, subset_closure.trans hVcl, hVinv⟩,
    subset_closure.trans (hVcl.trans hRW), hprop⟩

/-! ### Lemma 13.1.1 -/

/-- **Lemma 13.1.1 (p. 599; 2017: Lemma 13.1)**, for every `V ⊆ U(x)`: if `U(x)` carries the
natural `G_x`-action and `t : s⁻¹(cl_X U(x)) → X` is proper, then `cl_X(V) ⊆ U(x)` if and only
if `cl_{|X|}(|V|) ⊆ |U(x)|`.  (The text asks `V` to be `G_x`-invariant; it is not used.) -/
theorem lemma_13_1_1 {x : Obj} (N : X.NatNbhd x) (hN : X.IsProperSubset (closure N.U))
    {V : Set Obj} (hV : V ⊆ N.U) :
    closure V ⊆ N.U ↔ closure (X.π '' V) ⊆ X.π '' N.U := by
  have hcl : X.π '' closure V = closure (X.π '' V) :=
    X.proposition_7_1_10_of_isProperMap hN (hV.trans subset_closure)
  constructor
  · intro h
    rw [← hcl]
    exact image_mono h
  · intro h y hy
    -- `|y| ∈ |U(x)|`: a morphism `φ : z → y` with `z ∈ U(x)`
    have hπy : X.π y ∈ X.π '' N.U := h (hcl ▸ mem_image_of_mem X.π hy)
    obtain ⟨z, hzU, hzy⟩ := hπy
    obtain ⟨φ, hφs, hφt⟩ := (X.π_eq_π_iff).1 hzy
    -- a sheet of `t` at `φ`
    obtain ⟨W, V', τ, hφW, hd⟩ := X.isLocalScDiffeo_tgt φ
    have hτc : ContinuousOn τ V' := hd.isScSmoothOn_inv.continuousOn
    have hyV' : y ∈ V' := hφt ▸ hd.mapsTo hφW
    have hτy : τ y = φ := by rw [← hφt]; exact hd.left_inv φ hφW
    set O := V' ∩ τ ⁻¹' (X.src ⁻¹' N.U) with hOdef
    have hOo : IsOpen O :=
      (X.continuous_src.comp_continuousOn hτc).isOpen_inter_preimage hd.isOpen_target N.isOpen_U
    have hyO : y ∈ O := ⟨hyV', by rw [mem_preimage, mem_preimage, hτy, hφs]; exact hzU⟩
    -- on `O ∩ V`, `τ(y') ∈ 𝐔(x)` and `y' = Φ(index)(s(τ y'))`
    have hmor : ∀ y' ∈ O ∩ V, τ y' ∈ X.morOn N.rep.U := fun y' hy' =>
      ⟨N.U_subset hy'.1.2, by rw [hd.right_inv y' hy'.1.1]; exact N.U_subset (hV hy'.2)⟩
    have hrepr : ∀ y' ∈ O ∩ V,
        y' = N.rep.Φ (N.rep.index (τ y')) (X.src (τ y')) := fun y' hy' => by
      rw [← N.rep.tgt_eq_Φ_index (hmor y' hy'), hd.right_inv y' hy'.1.1]
    -- `𝓝[V] y` is nontrivial; some index occurs frequently
    have hne : (𝓝[V] y).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hy
    have hOV : ∀ᶠ y' in 𝓝[V] y, y' ∈ O ∩ V :=
      Filter.mem_of_superset (inter_mem_nhdsWithin V (hOo.mem_nhds hyO))
        fun y' hy' => ⟨hy'.2, hy'.1⟩
    have := X.proposition_7_1_12 x
    obtain ⟨g, hg⟩ : ∃ g : X.Isotropy x,
        ∃ᶠ y' in 𝓝[V] y, y' ∈ O ∩ V ∧ N.rep.index (τ y') = g := by
      by_contra hcon
      simp only [not_exists] at hcon
      have hall : ∀ᶠ y' in 𝓝[V] y, ∀ g : X.Isotropy x,
          ¬(y' ∈ O ∩ V ∧ N.rep.index (τ y') = g) :=
        Filter.eventually_all.2 fun g => Filter.not_frequently.1 (hcon g)
      obtain ⟨y', h1, h2⟩ := (hall.and hOV).exists
      exact h1 _ ⟨h2, rfl⟩
    -- the limit: `y = Φ(g)(z) ∈ U(x)`
    have hF : ContinuousAt (fun y' => N.rep.Φ g (X.src (τ y'))) y := by
      have h1 : ContinuousAt (fun y' => X.src (τ y')) y :=
        X.continuous_src.continuousAt.comp (hτc.continuousAt (hd.isOpen_target.mem_nhds hyV'))
      have h2 : ContinuousAt (N.rep.Φ g) (X.src (τ y)) := by
        rw [hτy, hφs]
        exact (N.rep.continuousOn_Φ g).continuousAt (N.rep.isOpen_U.mem_nhds (N.U_subset hzU))
      exact ContinuousAt.comp (g := N.rep.Φ g) (f := fun y' => X.src (τ y')) h2 h1
    have hlim := tendsto_nhds_unique_of_frequently_eq
      (tendsto_nhdsWithin_of_tendsto_nhds (f := id) tendsto_id)
      (tendsto_nhdsWithin_of_tendsto_nhds hF.tendsto)
      (hg.mono fun y' hy' => by
        simp only [id]
        rw [← hy'.2]
        exact hrepr y' hy'.1)
    rw [hlim, hτy, hφs]
    exact N.Φ_mem g hzU

/-- **Lemma 13.1.1, as printed**: for a `G_x`-invariant `V ⊆ U(x)`. -/
theorem lemma_13_1_1_book {x : Obj} (N : X.NatNbhd x) (hN : X.IsProperSubset (closure N.U))
    {V : Set Obj} (hV : V ⊆ N.U) (_hinv : ∀ g, MapsTo (N.rep.Φ g) V V) :
    closure V ⊆ N.U ↔ closure (X.π '' V) ⊆ X.π '' N.U :=
  X.lemma_13_1_1 N hN hV

/-! ### `𝒰(A, B)` and condition (3) -/

/-- **`𝒰(A, B)`**: the morphisms with source in `A` and target in `B` (Definition 13.1.2 (3),
Definition 13.1.5: `𝒰(x, x') = morBetween U(x) U(x')`). -/
def morBetween (A B : Set Obj) : Set Mor := {φ | X.src φ ∈ A ∧ X.tgt φ ∈ B}

variable {X}

theorem isOpen_morBetween {A B : Set Obj} (hA : IsOpen A) (hB : IsOpen B) :
    IsOpen (X.morBetween A B) :=
  (hA.preimage X.continuous_src).inter (hB.preimage X.continuous_tgt)

theorem morBetween_mono {A A' B B' : Set Obj} (hA : A ⊆ A') (hB : B ⊆ B') :
    X.morBetween A B ⊆ X.morBetween A' B' := fun _ hφ => ⟨hA hφ.1, hB hφ.2⟩

variable (X) in
/-- **Condition (3) of Definition 13.1.2 for one set `C` of morphisms**: `s : C → s(C)` and
`t : C → t(C)` are sc-diffeomorphisms onto open subsets. -/
def IsDiffeoComponent (C : Set Mor) : Prop :=
  (∃ σ : Obj → Mor, X.PMor.IsScDiffeoOn X.PObj X.src σ C (X.src '' C)) ∧
    ∃ τ : Obj → Mor, X.PMor.IsScDiffeoOn X.PObj X.tgt τ C (X.tgt '' C)

/-- For an open `C`, condition (3) is the injectivity of `s` and of `t` on `C`. -/
theorem isDiffeoComponent_iff_injOn {C : Set Mor} (hC : IsOpen C) :
    X.IsDiffeoComponent C ↔ InjOn X.src C ∧ InjOn X.tgt C := by
  constructor
  · rintro ⟨⟨σ, hσ⟩, τ, hτ⟩
    exact ⟨hσ.injOn, hτ.injOn⟩
  · rintro ⟨hs, ht⟩
    rcases C.eq_empty_or_nonempty with rfl | ⟨φ, -⟩
    · have hu : X.PObj.IsScSmoothOn X.PMor X.unit ∅ :=
        X.isScSmoothMap_unit.mono isOpen_empty (empty_subset _)
      refine ⟨⟨X.unit, ?_⟩, ⟨X.unit, ?_⟩⟩ <;> rw [image_empty] <;>
        exact ⟨MPolyfold.IsScSmoothOn.mono (by first | exact X.isScSmoothMap_src |
          exact X.isScSmoothMap_tgt) isOpen_empty (empty_subset _), hu,
          mapsTo_empty _ _, mapsTo_empty _ _, fun _ h => h.elim, fun _ h => h.elim⟩
    have : Nonempty Mor := ⟨φ⟩
    exact ⟨⟨_, X.isLocalScDiffeo_src.isScDiffeoOn_invFunOn hC hs⟩,
      ⟨_, X.isLocalScDiffeo_tgt.isScDiffeoOn_invFunOn hC ht⟩⟩

theorem IsDiffeoComponent.injOn_src {C : Set Mor} (h : X.IsDiffeoComponent C) :
    InjOn X.src C := h.1.choose_spec.injOn

theorem IsDiffeoComponent.injOn_tgt {C : Set Mor} (h : X.IsDiffeoComponent C) :
    InjOn X.tgt C := h.2.choose_spec.injOn

/-- A smaller open set inherits condition (3). -/
theorem IsDiffeoComponent.mono {C C' : Set Mor} (h : X.IsDiffeoComponent C) (hC' : IsOpen C')
    (hsub : C' ⊆ C) : X.IsDiffeoComponent C' :=
  (isDiffeoComponent_iff_injOn hC').2 ⟨h.injOn_src.mono hsub, h.injOn_tgt.mono hsub⟩

/-- Connected components of open sets of morphisms are open. -/
theorem isOpen_connectedComponentIn_mor (X : EpGroupoid Obj Mor) {S : Set Mor} (hS : IsOpen S)
    (φ : Mor) :
    IsOpen (connectedComponentIn S φ) :=
  X.PMor.isOpen_connectedComponentIn hS φ

variable (X)

/-! ### Definition 13.1.2 -/

/-- **Definition 13.1.2 (good system of open neighbourhoods, p. 600; 2017: Definition 13.1)**:
a family `(U(x))_{x ∈ X}` of open neighbourhoods such that (2) every `U(x)` carries the natural
`G_x`-action (`nbhd x : NatNbhd X x`), (1) `t : s⁻¹(cl_X U(x)) → X` is proper, and (3) for all
`x, x'` and every connected component `Σ` of `𝒰(x, x')`, `s : Σ → U(x)` and `t : Σ → U(x')` are
sc-diffeomorphisms onto open subsets. -/
structure GoodSystem where
  /-- (2) `U(x)` with the natural `G_x`-action. -/
  nbhd : ∀ x : Obj, X.NatNbhd x
  /-- (1) `t : s⁻¹(cl_X U(x)) → X` is proper. -/
  isProperSubset_closure : ∀ x, X.IsProperSubset (closure (nbhd x).U)
  /-- (3) every connected component of `𝒰(x, x')` satisfies condition (3). -/
  isDiffeoComponent : ∀ x x', ∀ φ ∈ X.morBetween (nbhd x).U (nbhd x').U,
    X.IsDiffeoComponent (connectedComponentIn (X.morBetween (nbhd x).U (nbhd x').U) φ)

/-- **A partial good system on `Q`** (the hypothesis of Theorem 13.1.7): for `q ∈ Q`, `U(q) ⊆ Q`
carries the natural action and the properness property, and condition (3) holds for
`q, q' ∈ Q`.  (The natural action and `𝒰(q, q')` are the same in `X` and in the full
subcategory on the open set `Q`.) -/
structure IsGoodOn (N : ∀ x : Obj, X.NatNbhd x) (Q : Set Obj) : Prop where
  subset : ∀ q ∈ Q, (N q).U ⊆ Q
  isProperSubset_closure : ∀ q ∈ Q, X.IsProperSubset (closure (N q).U)
  isDiffeoComponent : ∀ q ∈ Q, ∀ q' ∈ Q, ∀ φ ∈ X.morBetween (N q).U (N q').U,
    X.IsDiffeoComponent (connectedComponentIn (X.morBetween (N q).U (N q').U) φ)

namespace GoodSystem

variable {X} (𝒰 : X.GoodSystem)

/-- A good system as a partial good system on all of `X`. -/
theorem isGoodOn : X.IsGoodOn 𝒰.nbhd univ :=
  ⟨fun _ _ => subset_univ _, fun q _ => 𝒰.isProperSubset_closure q,
    fun q _ q' _ => 𝒰.isDiffeoComponent q q'⟩

/-- A partial good system on all of `X` is a good system. -/
def ofIsGoodOn (N : ∀ x : Obj, X.NatNbhd x) (h : X.IsGoodOn N univ) : X.GoodSystem :=
  ⟨N, fun q => h.isProperSubset_closure q (mem_univ q),
    fun q q' => h.isDiffeoComponent q (mem_univ q) q' (mem_univ q')⟩

@[simp] theorem ofIsGoodOn_nbhd (N : ∀ x : Obj, X.NatNbhd x) (h : X.IsGoodOn N univ) :
    (ofIsGoodOn N h).nbhd = N := rfl

/-- `U(x)`. -/
def U (x : Obj) : Set Obj := (𝒰.nbhd x).U

/-- **`𝒰(x, x')`** (Definition 13.1.2 (3), Definition 13.1.5). -/
def mor (x x' : Obj) : Set Mor := X.morBetween (𝒰.U x) (𝒰.U x')

/-- The connected component `Σ ∋ φ` of `𝒰(x, x')`. -/
def comp (x x' : Obj) (φ : Mor) : Set Mor := connectedComponentIn (𝒰.mor x x') φ

theorem isOpen_U (x : Obj) : IsOpen (𝒰.U x) := (𝒰.nbhd x).isOpen_U

theorem mem_U (x : Obj) : x ∈ 𝒰.U x := (𝒰.nbhd x).mem_U

theorem isOpen_mor (x x' : Obj) : IsOpen (𝒰.mor x x') :=
  isOpen_morBetween (𝒰.isOpen_U x) (𝒰.isOpen_U x')

theorem isOpen_comp (x x' : Obj) (φ : Mor) : IsOpen (𝒰.comp x x' φ) :=
  isOpen_connectedComponentIn_mor X (𝒰.isOpen_mor x x') φ

theorem mem_comp {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') : φ ∈ 𝒰.comp x x' φ :=
  mem_connectedComponentIn hφ

theorem isConnected_comp {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') :
    IsConnected (𝒰.comp x x' φ) :=
  isConnected_connectedComponentIn_iff.2 hφ

theorem comp_subset (x x' : Obj) (φ : Mor) : 𝒰.comp x x' φ ⊆ 𝒰.mor x x' :=
  connectedComponentIn_subset _ _

theorem comp_eq {x x' : Obj} {φ ψ : Mor} (hψ : ψ ∈ 𝒰.comp x x' φ) :
    𝒰.comp x x' ψ = 𝒰.comp x x' φ :=
  (connectedComponentIn_eq hψ).symm

/-- Condition (3) for the component `Σ ∋ φ`. -/
theorem isDiffeoComponent_comp {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') :
    X.IsDiffeoComponent (𝒰.comp x x' φ) :=
  𝒰.isDiffeoComponent x x' φ hφ

theorem injOn_src_comp {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') :
    InjOn X.src (𝒰.comp x x' φ) :=
  (𝒰.isDiffeoComponent_comp hφ).injOn_src

theorem injOn_tgt_comp {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') :
    InjOn X.tgt (𝒰.comp x x' φ) :=
  (𝒰.isDiffeoComponent_comp hφ).injOn_tgt

/-- `(s|Σ)⁻¹ : s(Σ) → Σ`. -/
def srcInv (x x' : Obj) (φ : Mor) : Obj → Mor :=
  @Function.invFunOn _ _ ⟨φ⟩ X.src (𝒰.comp x x' φ)

/-- `(t|Σ)⁻¹ : t(Σ) → Σ`. -/
def tgtInv (x x' : Obj) (φ : Mor) : Obj → Mor :=
  @Function.invFunOn _ _ ⟨φ⟩ X.tgt (𝒰.comp x x' φ)

/-- **`s : Σ → s(Σ)` is an sc-diffeomorphism onto the open `s(Σ) ⊆ U(x)`**, with inverse
`srcInv`. -/
theorem isScDiffeoOn_src_comp {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') :
    X.PMor.IsScDiffeoOn X.PObj X.src (𝒰.srcInv x x' φ) (𝒰.comp x x' φ)
      (X.src '' 𝒰.comp x x' φ) :=
  haveI : Nonempty Mor := ⟨φ⟩
  X.isLocalScDiffeo_src.isScDiffeoOn_invFunOn (𝒰.isOpen_comp x x' φ) (𝒰.injOn_src_comp hφ)

/-- **`t : Σ → t(Σ)` is an sc-diffeomorphism onto the open `t(Σ) ⊆ U(x')`**, with inverse
`tgtInv`. -/
theorem isScDiffeoOn_tgt_comp {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') :
    X.PMor.IsScDiffeoOn X.PObj X.tgt (𝒰.tgtInv x x' φ) (𝒰.comp x x' φ)
      (X.tgt '' 𝒰.comp x x' φ) :=
  haveI : Nonempty Mor := ⟨φ⟩
  X.isLocalScDiffeo_tgt.isScDiffeoOn_invFunOn (𝒰.isOpen_comp x x' φ) (𝒰.injOn_tgt_comp hφ)

theorem src_comp_subset (x x' : Obj) (φ : Mor) : X.src '' 𝒰.comp x x' φ ⊆ 𝒰.U x := by
  rintro _ ⟨ψ, hψ, rfl⟩
  exact (𝒰.comp_subset x x' φ hψ).1

theorem tgt_comp_subset (x x' : Obj) (φ : Mor) : X.tgt '' 𝒰.comp x x' φ ⊆ 𝒰.U x' := by
  rintro _ ⟨ψ, hψ, rfl⟩
  exact (𝒰.comp_subset x x' φ hψ).2

theorem srcInv_mem {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') {z : Obj}
    (hz : z ∈ X.src '' 𝒰.comp x x' φ) : 𝒰.srcInv x x' φ z ∈ 𝒰.comp x x' φ :=
  (𝒰.isScDiffeoOn_src_comp hφ).mapsTo_inv hz

theorem src_srcInv {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') {z : Obj}
    (hz : z ∈ X.src '' 𝒰.comp x x' φ) : X.src (𝒰.srcInv x x' φ z) = z :=
  (𝒰.isScDiffeoOn_src_comp hφ).right_inv z hz

theorem srcInv_src {x x' : Obj} {φ ψ : Mor} (hφ : φ ∈ 𝒰.mor x x') (hψ : ψ ∈ 𝒰.comp x x' φ) :
    𝒰.srcInv x x' φ (X.src ψ) = ψ :=
  (𝒰.isScDiffeoOn_src_comp hφ).left_inv ψ hψ

theorem tgtInv_mem {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') {z : Obj}
    (hz : z ∈ X.tgt '' 𝒰.comp x x' φ) : 𝒰.tgtInv x x' φ z ∈ 𝒰.comp x x' φ :=
  (𝒰.isScDiffeoOn_tgt_comp hφ).mapsTo_inv hz

theorem tgt_tgtInv {x x' : Obj} {φ : Mor} (hφ : φ ∈ 𝒰.mor x x') {z : Obj}
    (hz : z ∈ X.tgt '' 𝒰.comp x x' φ) : X.tgt (𝒰.tgtInv x x' φ z) = z :=
  (𝒰.isScDiffeoOn_tgt_comp hφ).right_inv z hz

theorem tgtInv_tgt {x x' : Obj} {φ ψ : Mor} (hφ : φ ∈ 𝒰.mor x x') (hψ : ψ ∈ 𝒰.comp x x' φ) :
    𝒰.tgtInv x x' φ (X.tgt ψ) = ψ :=
  (𝒰.isScDiffeoOn_tgt_comp hφ).left_inv ψ hψ

/-! ### Proposition 13.1.3 and Definition 13.1.4 -/

/-- **Condition (3) passes to smaller neighbourhoods**: if `U'(x) ⊆ U(x)` are open, every
connected component of `𝒰'(x, x')` lies in one of `𝒰(x, x')`. -/
theorem isDiffeoComponent_of_subset {x x' : Obj} {A A' : Set Obj} (hA : IsOpen A)
    (hA' : IsOpen A') (hAU : A ⊆ 𝒰.U x) (hA'U : A' ⊆ 𝒰.U x') {φ : Mor}
    (hφ : φ ∈ X.morBetween A A') :
    X.IsDiffeoComponent (connectedComponentIn (X.morBetween A A') φ) := by
  have hsub : X.morBetween A A' ⊆ 𝒰.mor x x' := morBetween_mono hAU hA'U
  exact (𝒰.isDiffeoComponent_comp (hsub hφ)).mono
    (isOpen_connectedComponentIn_mor X (isOpen_morBetween hA hA') φ)
    (connectedComponentIn_mono φ hsub)

/-- **The restriction of a good system** to `G_x`-invariant open neighbourhoods `W(x) ⊆ U(x)`
(Proposition 13.1.3). -/
def restrict (W : Obj → Set Obj) (hW : ∀ x, IsOpen (W x)) (hxW : ∀ x, x ∈ W x)
    (hWU : ∀ x, W x ⊆ 𝒰.U x) (hinv : ∀ x g, MapsTo ((𝒰.nbhd x).rep.Φ g) (W x) (W x)) :
    X.GoodSystem where
  nbhd x := (𝒰.nbhd x).restrict (W x) (hW x) (hxW x) (hWU x) (hinv x)
  isProperSubset_closure x :=
    isProperMap_domRestrict_of_subset_of_isClosed X.continuous_src
      (𝒰.isProperSubset_closure x) (closure_mono (hWU x)) isClosed_closure
  isDiffeoComponent x x' _ hφ :=
    𝒰.isDiffeoComponent_of_subset (hW x) (hW x') (hWU x) (hWU x') hφ

@[simp] theorem restrict_U (W : Obj → Set Obj) (hW : ∀ x, IsOpen (W x)) (hxW : ∀ x, x ∈ W x)
    (hWU : ∀ x, W x ⊆ 𝒰.U x) (hinv : ∀ x g, MapsTo ((𝒰.nbhd x).rep.Φ g) (W x) (W x))
    (x : Obj) : (𝒰.restrict W hW hxW hWU hinv).U x = W x := rfl

/-- **Definition 13.1.4 (p. 600; 2017: Definition 13.2)**: `𝒲` is a **refinement** of `𝒰` if
`W(x) ⊆ U(x)` for all `x`. -/
def IsRefinement (𝒲 𝒰 : X.GoodSystem) : Prop := ∀ x, 𝒲.U x ⊆ 𝒰.U x

/-- **Definition 13.1.4**: `𝒰` is **subordinate** to the open cover `(O_i)` if every `U(x)` lies in
some `O_i`. -/
def IsSubordinate {ι : Type*} (O : ι → Set Obj) : Prop := ∀ x, ∃ i, 𝒰.U x ⊆ O i

theorem isRefinement_restrict (W : Obj → Set Obj) (hW : ∀ x, IsOpen (W x))
    (hxW : ∀ x, x ∈ W x) (hWU : ∀ x, W x ⊆ 𝒰.U x)
    (hinv : ∀ x g, MapsTo ((𝒰.nbhd x).rep.Φ g) (W x) (W x)) :
    (𝒰.restrict W hW hxW hWU hinv).IsRefinement 𝒰 := hWU

/-- **The remark after Proposition 13.1.3**: for open neighbourhoods `V(x)` there is a refinement
`𝒲` of `𝒰` with `W(x) ⊆ U(x) ∩ V(x)`, keeping the natural actions. -/
theorem exists_refinement_subset (V : Obj → Set Obj) (hV : ∀ x, IsOpen (V x))
    (hxV : ∀ x, x ∈ V x) :
    ∃ 𝒲 : X.GoodSystem, 𝒲.IsRefinement 𝒰 ∧ (∀ x, 𝒲.U x ⊆ 𝒰.U x ∩ V x) ∧
      ∀ x, (𝒲.nbhd x).rep = (𝒰.nbhd x).rep := by
  choose N hrep hsub using fun x => (𝒰.nbhd x).exists_restrict_subset (hV x) (hxV x)
  refine ⟨𝒰.restrict (fun x => (N x).U) (fun x => (N x).isOpen_U) (fun x => (N x).mem_U)
    (fun x => fun _ hy => (hsub x hy).1) (fun x g => hrep x ▸ (N x).mapsTo_Φ g),
    fun x _ hy => (hsub x hy).1, fun x => hsub x, fun x => rfl⟩

end GoodSystem

/-- **Proposition 13.1.3 (p. 600; 2017: Proposition 13.1)**: if `(U(x))` is a good system and
`Ũ(x) ⊆ U(x)` are `G_x`-invariant open neighbourhoods of `x`, then `(Ũ(x))` (with the restricted
natural actions) is a good system. -/
theorem proposition_13_1_3 (𝒰 : X.GoodSystem) (W : Obj → Set Obj) (hW : ∀ x, IsOpen (W x))
    (hxW : ∀ x, x ∈ W x) (hWU : ∀ x, W x ⊆ 𝒰.U x)
    (hinv : ∀ x g, MapsTo ((𝒰.nbhd x).rep.Φ g) (W x) (W x)) :
    ∃ 𝒲 : X.GoodSystem, (∀ x, 𝒲.U x = W x) ∧ ∀ x, (𝒲.nbhd x).rep = (𝒰.nbhd x).rep :=
  ⟨𝒰.restrict W hW hxW hWU hinv, fun _ => rfl, fun _ => rfl⟩

end EpGroupoid

end Polyfold
