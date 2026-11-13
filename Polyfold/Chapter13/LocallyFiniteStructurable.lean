import Polyfold.Chapter13.TightOn

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.3, **Proposition 13.3.19** (p. 620; 2017: Proposition 13.5).

# Locally finite sums of structurable sc⁺-multisections are structurable

## The text, paraphrased

For a family `(Λ_l)_{l ∈ L}` of structurable sc⁺-multisection functors with locally finite
domain supports, `⊕_{l ∈ L} Λ_l` is structurable.  *Proof*: with `T_l = T_{Λ_l}` and `J_x` the
(finite) set of `l` with `x ∉ T_l`, take `V(x)` with the natural action and `V(x) ⊆ T_l` for
`l ∉ J_x`, and `U(x) = V(x) ∩ ⋂_{l ∈ J_x} U^l(x)`; pass to tight versions over this common `𝒰`;
take `K_x = ∏_l K^l_x` (`K^l_x = {∗}` for `x ∈ T_l`), `sˣ_k = ∑_l s^{l,x}_{k(l)}`, and
`τ_{x,x'} = ∏_l τ^l_{x,x'}`, which is defined since all but finitely many factors are
`[{∗} ← {∗} → {∗}]`.

## What is formalized (namespace `Polyfold.SBLocalization.LFStructData`)

`LFStructData Λ` bundles the data of the proof: the members `Λ_l` with decorations `D l` and
structures `t l`, the local finiteness (Definition 13.2.12, M's `IsLocallyFiniteFamily`), and one
good system `𝒰₀` (for the natural action at points where no member is non-trivial).

* `O x`, `F x` (the finite set `nontrivIdx Λ (O x)` of Definition 13.2.12), `V x`; the common good
  system `𝒰` with `U(x) ⊆ O(x)`, `U(x) ⊆ T_l` for `l ∈ F x` with `x ∈ T_l`, and `U(x) ≤ U^l(x)`
  for `l ∈ F x`; `isAdapted` (properties (3)–(4) of the proof).
* `Dt l`, `tt l`: the tight versions of the members over `𝒰` (`TightOn`).
* `K x = ∏_{l ∈ L} K^l_x` (finite: `finite_K`), the symmetric structure `Sx x` (M/D's
  `lfSumStructure` relabelled to `K x`), and `Sx_s_apply` (`sˣ_k = ∑_{l ∈ T} s^{l,x}_{k(l)}` for any
  finite `T ⊇ F x`).
* `τ x x' φ = ∏_{l ∈ L} τ^l_{x,x'}(φ)` (`IndexCorr.pi`), and `tau : Dsum.Tau`: Definitions 13.3.4
  and 13.3.6 for it (the step the text leaves to the reader).
* **`proposition_13_3_19`** (for a non-empty family, as printed),
  **`proposition_13_3_19_of_goodSystem`**
  (any family, given that a good system exists), `proposition_13_3_19_of_paracompact`.

## Readings

* The index set `L` lives in the universe of the bundle (`L : Type u`).
* "Locally finite domain supports" is read as M's `IsLocallyFiniteFamily` (Definition 13.2.12):
  every point has an open saturated neighbourhood over which only finitely many members are
  non-trivial.
* For the empty family the sum is the trivial multisection, whose structurability needs a good
  system (Definition 13.3.6); `proposition_13_3_19_of_goodSystem` covers it when one exists, e.g.
  for paracompact `|X|` (Theorem 13.1.8).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}} {L : Type u} {Λ : L → A.W → ℚ≥0}

/-- A member which is trivial over the open `O` (its index is not in `nontrivIdx Λ O`) has
`O ⊆ T_{Λ_l}`. -/
theorem subset_trivialSet_of_not_mem_nontrivIdx (hΛ : ∀ l, IsScPlusMultisection A (Λ l))
    {O : Set A.Obj} (hO : IsOpen O) {l : L} (hl : l ∉ nontrivIdx Λ O) :
    O ⊆ trivialSet (Λ l) := fun y hy =>
  ⟨O, hO, hy, ((hΛ l).isTrivialOn_iff O).2 fun w hw hw0 => by
    by_contra hne
    exact hl ⟨w, hw, hw0, pos_iff_ne_zero.2 hne⟩⟩

/-- On an index `κ : TightIdx p I` with `p`, the tight sections are the zero section. -/
theorem tightIdx_elim_zero {p : Prop} {I : Type u} (hp : p) (f : {_i : I // ¬p} → A.Obj → A.W)
    (κ : TightIdx p I) : Sum.elim (fun _ => fiberZero A.P) f κ = fiberZero A.P := by
  rcases κ with _ | ⟨_, h⟩
  · rfl
  · exact absurd hp h

variable (Λ) in
/-- **The data of the proof of Proposition 13.3.19**: structured representatives
`(Λ_l, 𝒰^l, S^l, τ^l)` of a locally finite family of structurable sc⁺-multisections, and a good
system `𝒰₀` providing the natural actions. -/
structure LFStructData where
  hΛ : ∀ l, IsScPlusMultisection A (Λ l)
  hlf : IsLocallyFiniteFamily Λ
  D : ∀ l, Decoration A (Λ l)
  t : ∀ l, (D l).Tau
  𝒰₀ : A.X.GoodSystem

namespace LFStructData

variable (P : LFStructData Λ)

/-! ### The common good system -/

/-- `O(x)` of Definition 13.2.12. -/
def O (x : A.Obj) : Set A.Obj := (P.hlf x).choose

theorem isOpen_O (x : A.Obj) : IsOpen (P.O x) := (P.hlf x).choose_spec.1

theorem mem_O (x : A.Obj) : x ∈ P.O x := (P.hlf x).choose_spec.2.2.1

theorem finite_O (x : A.Obj) : (nontrivIdx Λ (P.O x)).Finite := (P.hlf x).choose_spec.2.2.2

/-- The finite set of members which are non-trivial over `O(x)` (it contains the text's `J_x`). -/
def F (x : A.Obj) : Finset L := (P.finite_O x).toFinset

theorem mem_F {x : A.Obj} {l : L} : l ∈ P.F x ↔ l ∈ nontrivIdx Λ (P.O x) :=
  (P.finite_O x).mem_toFinset

theorem O_subset_trivialSet {x : A.Obj} {l : L} (hl : l ∉ P.F x) : P.O x ⊆ trivialSet (Λ l) :=
  subset_trivialSet_of_not_mem_nontrivIdx P.hΛ (P.isOpen_O x) fun h => hl (P.mem_F.2 h)

theorem mem_trivialSet_of_not_mem_F {x : A.Obj} {l : L} (hl : l ∉ P.F x) :
    x ∈ trivialSet (Λ l) :=
  P.O_subset_trivialSet hl (P.mem_O x)

/-- `V(x)`: inside `O(x)` and inside `T_l` for the `l ∈ F x` with `x ∈ T_l`. -/
def V (x : A.Obj) : Set A.Obj :=
  P.O x ∩ ⋂ l ∈ P.F x, {y | x ∈ trivialSet (Λ l) → y ∈ trivialSet (Λ l)}

theorem isOpen_V (x : A.Obj) : IsOpen (P.V x) := by
  refine (P.isOpen_O x).inter (isOpen_biInter_finset fun l _ => ?_)
  by_cases hx : x ∈ trivialSet (Λ l)
  · simpa [hx] using isOpen_trivialSet (Λ l)
  · simp [hx]

theorem mem_V (x : A.Obj) : x ∈ P.V x :=
  ⟨P.mem_O x, mem_iInter₂.2 fun _ _ h => h⟩

theorem exists_M (x : A.Obj) :
    ∃ M : A.X.NatNbhd x, M.rep = (P.𝒰₀.nbhd x).rep ∧ M.U ⊆ P.V x ∧ M.Le (P.𝒰₀.nbhd x) ∧
      ∀ l : P.F x, M.Le ((P.D l).𝒰.nbhd x) :=
  NatNbhd.exists_le_of_finite (P.𝒰₀.nbhd x) (fun l : P.F x => (P.D l).𝒰.nbhd x) (P.isOpen_V x)
    (P.mem_V x)

/-- `U(x) = V(x) ∩ ⋂_{l ∈ F x} U^l(x)` (with a natural action agreeing with those of the
`U^l(x)`). -/
def M (x : A.Obj) : A.X.NatNbhd x := (P.exists_M x).choose

theorem M_subset_V (x : A.Obj) : (P.M x).U ⊆ P.V x := (P.exists_M x).choose_spec.2.1

theorem M_le_F {x : A.Obj} {l : L} (hl : l ∈ P.F x) : (P.M x).Le ((P.D l).𝒰.nbhd x) :=
  (P.exists_M x).choose_spec.2.2.2 ⟨l, hl⟩

/-- **The common good system `𝒰`** of the proof. -/
def 𝒰 : A.X.GoodSystem :=
  P.𝒰₀.ofSubset P.M fun x => (P.exists_M x).choose_spec.2.2.1.subset

theorem U_subset_O (x : A.Obj) : P.𝒰.U x ⊆ P.O x := fun _ hy => (P.M_subset_V x hy).1

/-- **Properties (3)–(4) of the proof**: `𝒰` is adapted to every member. -/
theorem isAdapted (l : L) : (P.D l).IsAdapted P.𝒰 where
  triv x hx y hy := by
    by_cases hl : l ∈ P.F x
    · exact mem_iInter₂.1 (P.M_subset_V x hy).2 l hl hx
    · exact P.O_subset_trivialSet hl (P.U_subset_O x hy)
  le x hx := P.M_le_F (by_contra fun hl => hx (P.mem_trivialSet_of_not_mem_F hl))

/-! ### Tight versions over `𝒰` -/

/-- The tight version of the `l`-th member over `𝒰`. -/
def Dt (l : L) : Decoration A (Λ l) := (P.D l).tightOn (P.hΛ l) P.𝒰 (P.isAdapted l)

/-- Its correspondences. -/
def tt (l : L) : (P.Dt l).Tau := (P.t l).tightOn (P.hΛ l) P.𝒰 (P.isAdapted l)

theorem subsingleton_I {x : A.Obj} {l : L} (hl : l ∉ P.F x) : Subsingleton ((P.Dt l).S x).I :=
  TightIdx.subsingleton (I := ((P.D l).S x).I) (P.mem_trivialSet_of_not_mem_F hl)

theorem s_eq_zero {x : A.Obj} {l : L} (hl : l ∉ P.F x) (κ : ((P.Dt l).S x).I) :
    ((P.Dt l).S x).s κ = fiberZero A.P :=
  tightIdx_elim_zero (P.mem_trivialSet_of_not_mem_F hl) _ κ

/-! ### The index sets `K_x = ∏_l K^l_x` and the sections -/

/-- `K_x = ∏_{l ∈ L} K^l_x`. -/
def K (x : A.Obj) : Type u := ∀ l, ((P.Dt l).S x).I

theorem finite_K (x : A.Obj) : Finite (P.K x) :=
  finite_pi_of_subsingleton (P.F x) fun _ hl => P.subsingleton_I hl

instance instFintypeK (x : A.Obj) : Fintype (P.K x) :=
  haveI := P.finite_K x
  Fintype.ofFinite _

instance instMulActionK (x : A.Obj) : MulAction (A.X.Isotropy x) (P.K x) :=
  inferInstanceAs (MulAction (A.X.Isotropy x) (∀ l, ((P.Dt l).S x).I))

/-- The structure of `⊕_l Λ_l` on `U(x)` with the index set `∏_{l ∈ F x} K^l_x` (Lemma 13.2.13,
`lfSumStructure`). -/
def baseS (x : A.Obj) : SymmetricStructureOn A (lfSum Λ) (P.𝒰.nbhd x) :=
  lfSumStructure P.hΛ (P.finite_O x) (P.U_subset_O x) fun j => (P.Dt j).S x

/-- The enumeration of `F x` used by `lfSumStructure`. -/
abbrev en (x : A.Obj) : Fin (Fintype.card (P.finite_O x).toFinset) ≃ (P.finite_O x).toFinset :=
  (Fintype.equivFin (P.finite_O x).toFinset).symm

/-- The restriction `K_x → ∏_{l ∈ F x} K^l_x`. -/
def res (x : A.Obj) (k : P.K x) : (P.baseS x).I := fun m => k (P.en x m)

theorem res_bijective (x : A.Obj) : Bijective (P.res x) := by
  refine ⟨fun k k' e => funext fun l => ?_, fun κ => ?_⟩
  · by_cases hl : l ∈ P.F x
    · obtain ⟨m, hm⟩ := (P.en x).surjective ⟨l, P.mem_F.1 hl |> (P.finite_O x).mem_toFinset.2⟩
      have hl' : ((P.en x m : (P.finite_O x).toFinset) : L) = l := congrArg Subtype.val hm
      subst hl'
      exact congrFun e m
    · exact (P.subsingleton_I hl).elim _ _
  · let κ₁ : ∀ m, ((P.Dt (P.en x m)).S x).I := κ
    let κ' := _root_.Equiv.piCongrLeft (fun j : (P.finite_O x).toFinset => ((P.Dt j).S x).I)
      (P.en x) κ₁
    let k : P.K x := fun l => if hl : l ∈ (P.finite_O x).toFinset then κ' ⟨l, hl⟩
      else Sum.inl ⟨PUnit.unit, P.mem_trivialSet_of_not_mem_F fun h => hl h⟩
    have hk : ∀ j : (P.finite_O x).toFinset, k j = κ' j := by
      rintro ⟨l, hl⟩
      exact dif_pos hl
    exact ⟨k, funext fun m => (hk (P.en x m)).trans
      (_root_.Equiv.piCongrLeft_apply_apply
        (fun j : (P.finite_O x).toFinset => ((P.Dt j).S x).I) (P.en x) κ₁ m)⟩

/-- The relabelling `K_x ≃ ∏_{l ∈ F x} K^l_x`. -/
def resEquiv (x : A.Obj) : P.K x ≃ (P.baseS x).I := Equiv.ofBijective _ (P.res_bijective x)

/-- **The symmetric structure `sˣ = (∑_l s^{l,x}_{k(l)})_{k ∈ K_x}` of `⊕_l Λ_l` on `U(x)`.** -/
def Sx (x : A.Obj) : SymmetricStructureOn A (lfSum Λ) (P.𝒰.nbhd x) :=
  (P.baseS x).reindex (P.K x) (P.resEquiv x) fun _ _ => rfl

/-- **The decoration `(𝒰, S)` of `⊕_l Λ_l`.** -/
def Dsum : Decoration A (lfSum Λ) := ⟨P.𝒰, P.Sx⟩

/-- **`sˣ_k(y) = ∑_{l ∈ T} s^{l,x}_{k(l)}(y)`** for every finite `T ⊇ F x` (the terms with
`l ∉ F x` are zero sections). -/
theorem Sx_s_apply {x y : A.Obj} (hy : y ∈ P.𝒰.U x) (k : P.K x) (T : Finset L)
    (hT : P.F x ⊆ T) :
    (P.Sx x).s k y = ((∑ l ∈ T, (⟨((P.Dt l).S x).s (k l) y, ((P.Dt l).S x).P_s (k l) hy⟩ :
      A.P ⁻¹' {y}) : A.P ⁻¹' {y}) : A.W) := by
  set f : L → A.P ⁻¹' {y} := fun l => ⟨((P.Dt l).S x).s (k l) y, ((P.Dt l).S x).P_s (k l) hy⟩
  have e1 : (P.Sx x).s k y = ((∑ m, f (P.en x m) : A.P ⁻¹' {y}) : A.W) :=
    SymmetricStructureOn.sumSection_apply hy fun m => ((P.Dt _).S x).P_s _ hy
  rw [e1, _root_.Equiv.sum_comp (P.en x) (fun j => f j),
    Finset.sum_coe_sort (P.finite_O x).toFinset f]
  congr 1
  refine Finset.sum_subset hT fun l _ hl => Subtype.ext ?_
  change ((P.Dt l).S x).s (k l) y = fiberZero A.P y
  rw [P.s_eq_zero hl]

/-! ### The correspondences `τ = ∏_l τ^l` -/

theorem finite_out_of_eq {x x' : A.Obj} {τ τ' : ∀ l, IndexCorr ((P.Dt l).S x).I ((P.Dt l).S x').I}
    (h : ∀ l, τ l = τ' l) (hf : Finite (∀ l, (τ' l).out.I)) : Finite (∀ l, (τ l).out.I) := by
  obtain rfl := funext h
  exact hf

theorem τ_TT {x x' : A.Obj} {l : L} (hl : l ∉ P.F x ∪ P.F x') (φ : A.Mor) :
    (P.tt l).τ x x' φ = (IndexCorr.ofEquiv (Equiv.refl PUnit.{u + 1})).map
      (TightIdx.eT (P.mem_trivialSet_of_not_mem_F fun h => hl (Finset.mem_union_left _ h)))
      (TightIdx.eT (P.mem_trivialSet_of_not_mem_F fun h => hl (Finset.mem_union_right _ h))) :=
  Decoration.tightOnτ_TT _ _ φ

theorem τ_const {x x' : A.Obj} {l : L} (hl : l ∉ P.F x ∪ P.F x') (φ ψ : A.Mor) :
    (P.tt l).τ x x' φ = (P.tt l).τ x x' ψ :=
  (P.τ_TT hl φ).trans (P.τ_TT hl ψ).symm

theorem finite_out (x x' : A.Obj) (φ : A.Mor) : Finite (∀ l, ((P.tt l).τ x x' φ).out.I) :=
  finite_pi_of_subsingleton (P.F x ∪ P.F x') fun _ hl =>
    @IndexCorr.subsingleton_out_I _ _ _
      ((IndexDiagram.ofEquiv (Equiv.refl PUnit.{u + 1})).map
        (TightIdx.eT (P.mem_trivialSet_of_not_mem_F fun h => hl (Finset.mem_union_left _ h)))
        (TightIdx.eT (P.mem_trivialSet_of_not_mem_F fun h => hl (Finset.mem_union_right _ h))))
      (P.τ_TT hl φ).symm (inferInstanceAs (Subsingleton PUnit.{u + 1}))

/-- **`τ_{x,x'}(φ) = ∏_{l ∈ L} τ^l_{x,x'}(φ)`.** -/
def τ (x x' : A.Obj) (φ : A.Mor) : IndexCorr (P.K x) (P.K x') :=
  IndexCorr.pi (fun l => (P.tt l).τ x x' φ) (P.finite_out x x' φ)

theorem τ_congr {x x' : A.Obj} {φ ψ : A.Mor}
    (h : ∀ l ∈ P.F x ∪ P.F x', (P.tt l).τ x x' ψ = (P.tt l).τ x x' φ) : P.τ x x' ψ = P.τ x x' φ :=
  IndexCorr.pi_congr (fun l => if hl : l ∈ P.F x ∪ P.F x' then h l hl else P.τ_const hl ψ φ) _ _

/-- **Definition 13.3.4 for `τ`**: the product of the correspondences is a correspondence. -/
theorem isCorrespondence (x x' : A.Obj) : P.Dsum.IsCorrespondence x x' (P.τ x x') where
  locallyConstant φ hφ := by
    have hev : ∀ᶠ ψ in 𝓝 φ, ∀ l ∈ P.F x ∪ P.F x', (P.tt l).τ x x' ψ = (P.tt l).τ x x' φ :=
      (eventually_all_finset _).2 fun l _ =>
        ((P.tt l).isCorrespondence x x').locallyConstant φ hφ
    exact hev.mono fun ψ hψ => P.τ_congr hψ
  finite := by
    rcases (P.𝒰.mor x x').eq_empty_or_nonempty with he | ⟨φ₀, -⟩
    · refine Set.Finite.subset (s := ∅) finite_empty ?_
      rintro _ ⟨φ, hφ, -⟩
      exact (Set.eq_empty_iff_forall_notMem.1 he φ hφ).elim
    have : Nonempty A.Mor := ⟨φ₀⟩
    set T := P.F x ∪ P.F x'
    set R : A.Mor → ∀ l : T, IndexCorr ((P.Dt l).S x).I ((P.Dt l).S x').I :=
      fun φ l => (P.tt l).τ x x' φ
    have hpi : (Set.pi univ fun l : T => (P.tt l).τ x x' '' P.𝒰.mor x x').Finite :=
      Set.Finite.pi fun l => ((P.tt l).isCorrespondence x x').finite
    have hR : (R '' P.𝒰.mor x x').Finite := hpi.subset (by
      rintro _ ⟨φ, hφ, rfl⟩ l -
      exact ⟨φ, hφ, rfl⟩)
    have hRτ : ∀ φ ψ, R φ = R ψ → P.τ x x' φ = P.τ x x' ψ := fun φ ψ e =>
      P.τ_congr fun l hl => congrFun e ⟨l, hl⟩
    refine (hR.image fun r => P.τ x x' (invFunOn R (P.𝒰.mor x x') r)).subset ?_
    rintro _ ⟨φ, hφ, rfl⟩
    refine ⟨R φ, mem_image_of_mem _ hφ, hRτ _ _ ?_⟩
    exact invFunOn_eq (f := R) ⟨φ, hφ, rfl⟩
  biact φ hφ g' g :=
    have e := fun l => ((P.tt l).isCorrespondence x x').biact φ hφ g' g
    (IndexCorr.pi_congr e _ (P.finite_out_of_eq (fun l => (e l).symm)
      (P.finite_out x x' (P.𝒰.biact x x' g' φ g)))).trans
      (IndexCorr.biact_pi g' g _ _ _).symm
  compat φ hφ := IndexCorr.sat_pi _
    (fun l i j => ∀ ψ ∈ P.𝒰.comp x x' φ, (P.Dt l).Compat ψ i j)
    (fun i j H ψ hψ => by
      have hψ' := P.𝒰.comp_subset x x' φ hψ
      change (P.Sx x').s j (A.X.tgt ψ) = fibAct ψ ((P.Sx x).s i (A.X.src ψ))
      rw [P.Sx_s_apply hψ'.2 j (P.F x ∪ P.F x') Finset.subset_union_right,
        P.Sx_s_apply hψ'.1 i (P.F x ∪ P.F x') Finset.subset_union_left, fibAct_sum _ rfl rfl]
      exact congrArg Subtype.val (Finset.sum_congr rfl fun l _ => Subtype.ext (H l ψ hψ)))
    fun l => ((P.tt l).isCorrespondence x x').compat φ hφ

/-- **`(Λ, 𝒰, S, τ)` is structured** (Definition 13.3.6): the conditions on `τ_{x,x}` and on `♯`
hold factorwise. -/
def tau : P.Dsum.Tau where
  τ := P.τ
  isCorrespondence := P.isCorrespondence
  diag x g y hy := by
    let _ : Fintype (∀ l, ((P.Dt l).S x).I) := P.instFintypeK x
    exact IndexCorr.pi_ofPerm g _ (fun l => (P.tt l).diag x g y hy) _
  swap x x' φ hφ := by
    have hfin : Finite (∀ l, (((P.tt l).τ x x' (A.X.inv φ)).swap).out.I) :=
      finite_pi_of_subsingleton (P.F x ∪ P.F x') fun l hl =>
        @IndexCorr.subsingleton_out_I _ _ _
          ((IndexDiagram.ofEquiv (Equiv.refl PUnit.{u + 1})).map
            (TightIdx.eT (P.mem_trivialSet_of_not_mem_F fun h => hl (Finset.mem_union_left _ h)))
            (TightIdx.eT (P.mem_trivialSet_of_not_mem_F fun h =>
              hl (Finset.mem_union_right _ h)))).swap
          (by rw [P.τ_TT hl]; rfl) (inferInstanceAs (Subsingleton PUnit.{u + 1}))
    exact (IndexCorr.pi_congr (fun l => (P.tt l).swap x x' φ hφ) _ hfin).trans
      (IndexCorr.swap_pi _ _ _).symm

end LFStructData

/-- **The proof of Proposition 13.3.19**: `⊕_l Λ_l` is structurable, with the decoration `Dsum`
and the correspondences `tau`. -/
theorem LFStructData.isStructurable (P : LFStructData Λ) : IsStructurable A (lfSum Λ) :=
  ⟨lemma_13_2_13 P.hΛ P.hlf, P.Dsum, ⟨P.tau⟩⟩

/-- **2021 Proposition 13.3.19, p. 620 (2017: Proposition 13.5), for any family**: if a good system
exists, the sum `⊕_{l ∈ L} Λ_l` of a locally finite family of structurable sc⁺-multisections is
structurable. -/
theorem proposition_13_3_19_of_goodSystem (h𝒰 : Nonempty A.X.GoodSystem)
    (h : ∀ l, IsStructurable A (Λ l)) (hlf : IsLocallyFiniteFamily Λ) :
    IsStructurable A (lfSum Λ) := by
  choose hΛ D t using h
  exact (LFStructData.mk hΛ hlf D (fun l => (t l).some) h𝒰.some).isStructurable

/-- **2021 Proposition 13.3.19, p. 620 (2017: Proposition 13.5)**: the sum `⊕_{l ∈ L} Λ_l` of a
(non-empty) locally finite family of structurable sc⁺-multisection functors is structurable. -/
theorem proposition_13_3_19 [Nonempty L] (h : ∀ l, IsStructurable A (Λ l))
    (hlf : IsLocallyFiniteFamily Λ) : IsStructurable A (lfSum Λ) :=
  proposition_13_3_19_of_goodSystem
    ⟨(h (Classical.arbitrary L)).2.choose.𝒰⟩ h hlf

/-- **Proposition 13.3.19 for paracompact `|X|`** (any family, also the empty one). -/
theorem proposition_13_3_19_of_paracompact (hX : A.X.HasParacompactOrbitSpace)
    (h : ∀ l, IsStructurable A (Λ l)) (hlf : IsLocallyFiniteFamily Λ) :
    IsStructurable A (lfSum Λ) :=
  proposition_13_3_19_of_goodSystem
    ⟨(A.X.theorem_13_1_8 hX (fun _ => univ) (fun _ => isOpen_univ) fun _ => mem_univ _).choose⟩
    h hlf

end SBLocalization

end Polyfold
