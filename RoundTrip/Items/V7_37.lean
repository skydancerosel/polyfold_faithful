import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_37

/-! Round trip for V7_37 (p. 241, before Definition 7.12: the subgroup `T_x` of the elements
acting trivially).

`A` is the conjunction of the types of the twelve listed theorems, universes at `0`:
`one_mem_trivialSet`, `NaturalRep.actsTrivially_iff`, `mem_trivialSet_of_section`,
`mem_trivialSet_iff_eventually`, `exists_mem_nhds_trivialSet_iff`,
`exists_naturalRep_trivialSet_iff`, `exists_naturalRep_kerΦ_eq`, `trivialSubgroup_normal`,
`isEffective_iff_trivialSubgroup_eq_bot`, `isotropyConj_mem_trivialSet`,
`map_isotropyConj_trivialSubgroup`, `NaturalRep.mem_trivialSet_of_val_eq_Γ`.
`ActsTrivially`, `trivialSet`, `trivialSubgroup` are vocabulary.

Dictionary: `B`'s `NatRepB` and the project's `NaturalRep` (`toB`, `ofB`; same `U`, `Φ`, `Γ`;
`B` allows any inverse of `Φ(g)`, the project asks `Φ(g⁻¹)`, which follows since `Φ(1) = id` on
`U`); hence `ActsTriviallyB ↔ ActsTrivially` and `TxB = trivialSet` (no hypothesis needed).

* `A → B`: (a) and (d) from `exists_naturalRep_trivialSet_iff`, (b) the dictionary, (c) from
  `one_mem_trivialSet`, (e) `trivialSubgroup` with `trivialSubgroup_normal`.
* `B → A`: from `B`: `one_mem_trivialSet` (c), `exists_naturalRep_trivialSet_iff` (d),
  `exists_naturalRep_kerΦ_eq` (d with `mem_kerΦ`), `trivialSubgroup_normal` (e: the normal `N`
  of `B` has the carrier of `trivialSubgroup`).  The other seven conjuncts are not in `B` (the
  germ characterisation for *every* `R`, the section criterion, the intrinsic form `s = t` near
  `g`, the uniform neighbourhood `N`, effectiveness iff `T_x = 1`, and `φ T_x φ⁻¹ = T_y`); they are
  re-proved outright, by copying the project's proofs (including its private
  `exists_conj_section`) with the listed theorems replaced by the re-proved ones.

`#rt_check_soft` is used: `B`, and every statement mentioning `trivialSubgroup`, reaches the
banned `exists_naturalRep_trivialSet_iff` through the proof field `mul_mem'` of the definition
`EpGroupoid.trivialSubgroup`; no proof here uses it otherwise.
-/

namespace RoundTrip.V7_37
open Polyfold Set Filter Topology Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.one_mem_trivialSet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.actsTrivially_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.mem_trivialSet_of_section.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.mem_trivialSet_iff_eventually.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.exists_mem_nhds_trivialSet_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.exists_naturalRep_trivialSet_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.exists_naturalRep_kerΦ_eq.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.trivialSubgroup_normal.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isEffective_iff_trivialSubgroup_eq_bot.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isotropyConj_mem_trivialSet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.map_isotropyConj_trivialSubgroup.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.mem_trivialSet_of_val_eq_Γ.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.one_mem_trivialSet.{0},
    @Polyfold.EpGroupoid.NaturalRep.actsTrivially_iff.{0},
    @Polyfold.EpGroupoid.mem_trivialSet_of_section.{0},
    @Polyfold.EpGroupoid.mem_trivialSet_iff_eventually.{0},
    @Polyfold.EpGroupoid.exists_mem_nhds_trivialSet_iff.{0},
    @Polyfold.EpGroupoid.exists_naturalRep_trivialSet_iff.{0},
    @Polyfold.EpGroupoid.exists_naturalRep_kerΦ_eq.{0},
    @Polyfold.EpGroupoid.trivialSubgroup_normal.{0},
    @Polyfold.EpGroupoid.isEffective_iff_trivialSubgroup_eq_bot.{0},
    @Polyfold.EpGroupoid.isotropyConj_mem_trivialSet.{0},
    @Polyfold.EpGroupoid.map_isotropyConj_trivialSubgroup.{0},
    @Polyfold.EpGroupoid.NaturalRep.mem_trivialSet_of_val_eq_Γ.{0}⟩

section Dictionary
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor} {x : Obj}

/-- The project's natural representation as `B`'s. -/
def toB (R : X.NaturalRep x) : NatRepB X x where
  U := R.U
  isOpen_U := R.isOpen_U
  isConnected_U := R.isConnected_U
  mem_U := R.mem_U
  Φ := R.Φ
  Γ := R.Γ
  diffeo g := ⟨_, R.isScDiffeoOn_Φ g⟩
  hom := R.Φ_mul
  smooth := R.isScSmoothOn_Γ
  Γ_x := R.Γ_self
  src_Γ := R.src_Γ
  tgt_Γ := R.tgt_Γ
  unique := R.existsUnique_Γ

theorem NatRepB.Φ_one (R : NatRepB X x) : ∀ y ∈ R.U, R.Φ 1 y = y := by
  intro y hy
  obtain ⟨ψ, hψ⟩ := R.diffeo 1
  have h := R.hom 1 1 y hy
  rw [mul_one] at h
  have := congrArg ψ h
  rw [hψ.left_inv _ hy, hψ.left_inv _ (hψ.mapsTo hy)] at this
  exact this.symm

/-- `B`'s natural representation as the project's. -/
def ofB (R : NatRepB X x) : X.NaturalRep x where
  U := R.U
  isOpen_U := R.isOpen_U
  isConnected_U := R.isConnected_U
  mem_U := R.mem_U
  Φ := R.Φ
  Γ := R.Γ
  isScDiffeoOn_Φ g := by
    obtain ⟨ψ, hψ⟩ := R.diffeo g
    obtain ⟨ψ', hψ'⟩ := R.diffeo g⁻¹
    exact ⟨hψ.isScSmoothOn, hψ'.isScSmoothOn, hψ.mapsTo, hψ'.mapsTo,
      fun y hy => by rw [← R.hom _ _ y hy, inv_mul_cancel, R.Φ_one y hy],
      fun y hy => by rw [← R.hom _ _ y hy, mul_inv_cancel, R.Φ_one y hy]⟩
  Φ_mul := R.hom
  isScSmoothOn_Γ := R.smooth
  Γ_self := R.Γ_x
  src_Γ := R.src_Γ
  tgt_Γ := R.tgt_Γ
  existsUnique_Γ := R.unique

theorem actsTriviallyB_iff {g : X.Isotropy x} : ActsTriviallyB X g ↔ X.ActsTrivially g :=
  ⟨fun ⟨R, h⟩ => ⟨ofB R, h⟩, fun ⟨R, h⟩ => ⟨toB R, h⟩⟩

theorem TxB_eq (x : Obj) : TxB X x = X.trivialSet x := by
  ext g
  exact actsTriviallyB_iff

end Dictionary

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  obtain ⟨h1, -, -, -, -, h6, -, h8, -⟩ := hA
  refine ⟨fun x V hV hx => ?_, fun x g => actsTriviallyB_iff.symm,
    fun x => (TxB_eq x).symm, fun x => ?_, fun x V hV hx => ?_,
    fun x => ⟨X.trivialSubgroup x, h8 X x, (TxB_eq x).symm⟩⟩
  · obtain ⟨R, hRV, -⟩ := h6 X x hV hx
    exact ⟨toB R, hRV⟩
  · obtain ⟨R, -, -⟩ := h6 X x isOpen_univ (mem_univ x)
    exact actsTriviallyB_iff.2 (h1 X R)
  · obtain ⟨R, hRV, hR⟩ := h6 X x hV hx
    exact ⟨toB R, hRV, fun g => by rw [TxB_eq]; exact (hR g).symm⟩

/-! ### `B → A` -/

section FromB
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- From `B` (d): small natural representations with `ker Φ = T_x`. -/
theorem exists_naturalRep_trivialSet_iff_of_B (hB : B) (x : Obj) {V : Set Obj} (hV : IsOpen V)
    (hx : x ∈ V) :
    ∃ R : X.NaturalRep x, R.U ⊆ V ∧ ∀ g, g ∈ X.trivialSet x ↔ ∀ y ∈ R.U, R.Φ g y = y := by
  obtain ⟨R, hRV, hR⟩ := (hB Obj Mor X).2.2.2.2.1 x V hV hx
  refine ⟨ofB R, hRV, fun g => ?_⟩
  rw [← TxB_eq]
  exact (hR g).symm

/-- From `B` (e): `T_x` is normal. -/
theorem trivialSubgroup_normal_of_B (hB : B) (x : Obj) : (X.trivialSubgroup x).Normal := by
  obtain ⟨N, hN, hNc⟩ := (hB Obj Mor X).2.2.2.2.2 x
  have : X.trivialSubgroup x = N :=
    SetLike.coe_injective ((X.coe_trivialSubgroup x).trans ((TxB_eq x).symm.trans hNc.symm))
  rw [this]
  exact hN

/-! Outright (not in `B`): copies of the project's proofs. -/

theorem actsTrivially_iff' {x : Obj} (R : X.NaturalRep x) {g : X.Isotropy x} :
    X.ActsTrivially g ↔ ∀ᶠ y in 𝓝 x, R.Φ g y = y := by
  refine ⟨R.eventually_Φ_eq_of_actsTrivially, fun h => ?_⟩
  obtain ⟨N, hN, hNo, hxN⟩ := mem_nhds_iff.1 h
  obtain ⟨R', hR'U, hR'Φ, -⟩ := X.exists_naturalRep_shrink R hNo hxN
  exact ⟨R', fun y hy => by rw [hR'Φ]; exact hN (hR'U hy).1⟩

theorem mem_trivialSet_of_section' {y : Obj} {h : X.Isotropy y} {D : Set Obj} (hD : IsOpen D)
    (hyD : y ∈ D) {k : Obj → Mor} (hk : ContinuousOn k D) (hks : ∀ z ∈ D, X.src (k z) = z)
    (hkt : ∀ z ∈ D, X.tgt (k z) = z) (hky : k y = h.val) : h ∈ X.trivialSet y := by
  obtain ⟨R, -⟩ := X.theorem_7_1 y isOpen_univ (mem_univ y)
  refine (actsTrivially_iff' X R).2 ?_
  have hyC : y ∈ connectedComponentIn (D ∩ R.U) y := mem_connectedComponentIn ⟨hyD, R.mem_U⟩
  have hC := connectedComponentIn_subset (D ∩ R.U) y
  have heq : EqOn k (R.Γ h) (connectedComponentIn (D ∩ R.U) y) :=
    eqOn_sections_of_isPreconnected X.isLocalScDiffeo_src.isLocallyInjective
      isPreconnected_connectedComponentIn (hk.mono fun z hz => (hC hz).1)
      ((R.continuousOn_Γ h).mono fun z hz => (hC hz).2) (fun z hz => hks z (hC hz).1)
      (fun z hz => R.src_Γ h z (hC hz).2) hyC (by rw [hky, R.Γ_self])
  filter_upwards [(X.PObj.isOpen_connectedComponentIn (hD.inter R.isOpen_U) y).mem_nhds hyC]
    with z hz
  rw [← R.tgt_Γ h z (hC hz).2, ← heq hz]
  exact hkt z (hC hz).1

theorem mem_trivialSet_iff_eventually' {x : Obj} {g : X.Isotropy x} :
    g ∈ X.trivialSet x ↔ ∀ᶠ ψ in 𝓝 g.val, X.src ψ = X.tgt ψ := by
  constructor
  · rintro ⟨R, hR⟩
    have hgW : g.val ∈ R.Γ g '' R.U := by
      have h := R.Γ_mem_image g R.mem_U
      rwa [R.Γ_self] at h
    filter_upwards [(R.isOpen_image_Γ g).mem_nhds hgW] with ψ hψ
    obtain ⟨y, hy, rfl⟩ := hψ
    rw [R.src_Γ g y hy, R.tgt_Γ g y hy, hR y hy]
  · intro h
    obtain ⟨W₁, V₁, σ, hgW₁, hd⟩ := X.isLocalScDiffeo_src g.val
    have hσg : σ x = g.val := by
      have h' := hd.left_inv _ hgW₁
      rwa [g.src_val] at h'
    have hxV₁ : x ∈ V₁ := by
      have h' := hd.mapsTo hgW₁
      rwa [g.src_val] at h'
    refine mem_trivialSet_of_section' X
      (hd.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hd.isOpen_target isOpen_interior)
      ⟨hxV₁, by rw [mem_preimage, hσg]; exact mem_interior_iff_mem_nhds.2 h⟩
      (hd.isScSmoothOn_inv.continuousOn.mono inter_subset_left)
      (fun z hz => hd.right_inv z hz.1) (fun z hz => ?_) hσg
    rw [← interior_subset hz.2, hd.right_inv z hz.1]

theorem Φ_eqOn_of_subset' {x : Obj} {R R' : X.NaturalRep x} (h : R.U ⊆ R'.U)
    (g : X.Isotropy x) : EqOn (R.Φ g) (R'.Φ g) R.U := fun _ hy =>
  R.Φ_eqOn R' g (R.isConnected_U.isPreconnected.subset_connectedComponentIn R.mem_U
    (subset_inter subset_rfl h) hy)

theorem exists_mem_nhds_trivialSet_iff' (x : Obj) :
    ∃ N ∈ 𝓝 x, ∀ R : X.NaturalRep x, R.U ⊆ N →
      ∀ g, g ∈ X.trivialSet x ↔ ∀ y ∈ R.U, R.Φ g y = y := by
  obtain ⟨R₀, -⟩ := X.theorem_7_1 x isOpen_univ (mem_univ x)
  have hev : ∀ᶠ y in 𝓝 x, ∀ g, g ∈ X.trivialSet x → R₀.Φ g y = y := by
    have := EpGroupoid.NatRepConstruction.finite_isotropy X x
    refine Filter.eventually_all.2 fun g => ?_
    by_cases hg : g ∈ X.trivialSet x
    · filter_upwards [R₀.eventually_Φ_eq_of_actsTrivially hg] with y hy _ using hy
    · exact Filter.Eventually.of_forall fun _ h => absurd h hg
  refine ⟨{y | ∀ g, g ∈ X.trivialSet x → R₀.Φ g y = y} ∩ R₀.U,
    inter_mem hev (R₀.isOpen_U.mem_nhds R₀.mem_U), fun R hRN g => ⟨fun hg y hy => ?_,
    fun h => ⟨R, h⟩⟩⟩
  rw [Φ_eqOn_of_subset' X (R := R) (R' := R₀) (fun z hz => (hRN hz).2) g hy]
  exact (hRN hy).1 g hg

theorem isEffective_iff_trivialSubgroup_eq_bot' :
    X.IsEffective ↔ ∀ x, X.trivialSubgroup x = ⊥ := by
  refine ⟨fun h x => (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_, fun h =>
    X.isEffective_iff_forall_naturalRep.2 fun x R g hg =>
      (Subgroup.eq_bot_iff_forall _).1 (h x) g ⟨R, hg⟩⟩
  obtain ⟨R, hR⟩ := hg
  exact h.eq_one R hR

theorem mem_trivialSet_of_val_eq_Γ' {x : Obj} (R : X.NaturalRep x) {g : X.Isotropy x}
    (hg : ∀ z ∈ R.U, R.Φ g z = z) {y : Obj} (hy : y ∈ R.U) {h : X.Isotropy y}
    (hh : h.val = R.Γ g y) : h ∈ X.trivialSet y :=
  mem_trivialSet_of_section' X R.isOpen_U hy (R.continuousOn_Γ g) (R.src_Γ g)
    (fun z hz => (R.tgt_Γ g z hz).trans (hg z hz)) hh.symm

/-- Copy of the project's private `exists_conj_section`. -/
theorem exists_conj_section' {x y : Obj} {φ : Mor} (hx : X.src φ = x) (hy : X.tgt φ = y)
    (R : X.NaturalRep x) {g : X.Isotropy x} (hR : ∀ z ∈ R.U, R.Φ g z = z) :
    ∃ D : Set Obj, IsOpen D ∧ y ∈ D ∧ ∃ k : Obj → Mor, ContinuousOn k D ∧
      (∀ z ∈ D, X.src (k z) = z) ∧ (∀ z ∈ D, X.tgt (k z) = z) ∧
      k y = X.comp (X.comp φ g.val) (X.inv φ) := by
  have hθ := (X.sheetAt φ).isScDiffeoOn_tgt
  have hσ := (X.sheetAt φ).isScDiffeoOn_src
  set S := X.sheetAt φ
  set D := S.tgtSet ∩ (fun z => X.src (S.tgtInv z)) ⁻¹' R.U
  have hDo : IsOpen D := (X.continuous_src.comp_continuousOn
    hθ.isScSmoothOn_inv.continuousOn).isOpen_inter_preimage hθ.isOpen_target R.isOpen_U
  have hφy : S.tgtInv y = φ := by rw [← hy]; exact hθ.left_inv φ (X.mem_sheetAt φ)
  have hyD : y ∈ D := ⟨hy ▸ X.tgt_mem_sheetAt φ, by
    rw [mem_preimage, hφy, hx]; exact R.mem_U⟩
  have hc₁ : ∀ z ∈ D, X.src (R.Γ g (X.src (S.tgtInv z))) = X.tgt (X.inv (S.tgtInv z)) :=
    fun z hz => by rw [R.src_Γ g _ hz.2, X.tgt_inv]
  have hit : ∀ z ∈ D, X.tgt (X.comp (R.Γ g (X.src (S.tgtInv z))) (X.inv (S.tgtInv z))) =
      X.src (S.tgtInv z) := fun z hz => by
    rw [X.tgt_comp _ _ (hc₁ z hz), R.tgt_Γ g _ hz.2, hR _ hz.2]
  have his : ∀ z ∈ D, X.src (X.comp (R.Γ g (X.src (S.tgtInv z))) (X.inv (S.tgtInv z))) = z :=
    fun z hz => by rw [X.src_comp _ _ (hc₁ z hz), X.src_inv, hθ.right_inv z hz.1]
  refine ⟨D, hDo, hyD, fun z => X.comp (S.tgtInv z)
    (X.comp (R.Γ g (X.src (S.tgtInv z))) (X.inv (S.tgtInv z))), ?_, fun z hz => ?_,
    fun z hz => ?_, ?_⟩
  · have hF₁ := (R.isScSmoothOn_comp_Γ_tgt g).continuousOn
    have hF₂ := (X.isScSmoothCompSheet S.srcInv S.carrier S.srcSet hσ).continuousOn
    have hψ : ContinuousOn (fun z => X.inv (S.tgtInv z)) D :=
      X.continuous_inv.comp_continuousOn (hθ.isScSmoothOn_inv.continuousOn.mono inter_subset_left)
    have h₁ : MapsTo (fun z => X.inv (S.tgtInv z)) D (X.tgt ⁻¹' R.U) := fun z hz => by
      rw [mem_preimage, X.tgt_inv]; exact hz.2
    have h₂ : MapsTo ((fun ψ => X.comp (R.Γ g (X.tgt ψ)) ψ) ∘ fun z => X.inv (S.tgtInv z)) D
        (X.tgt ⁻¹' S.srcSet) := fun z hz => by
      rw [mem_preimage, Function.comp_apply, X.tgt_inv, hit z hz]
      exact hσ.mapsTo (hθ.mapsTo_inv hz.1)
    refine (hF₂.comp (hF₁.comp hψ h₁) h₂).congr fun z hz => ?_
    simp only [Function.comp_apply, X.tgt_inv, hit z hz, hσ.left_inv _ (hθ.mapsTo_inv hz.1)]
  · rw [X.src_comp _ _ (hit z hz).symm, his z hz]
  · rw [X.tgt_comp _ _ (hit z hz).symm, hθ.right_inv z hz.1]
  · simp only [hφy, hx, R.Γ_self]
    exact (X.comp_assoc _ _ _ (by rw [hx, g.tgt_val]) (by rw [g.src_val, X.tgt_inv, hx])).symm

theorem isotropyConj_mem_trivialSet' {x y : Obj} (φ : Mor) (hx : X.src φ = x)
    (hy : X.tgt φ = y) {g : X.Isotropy x} (hg : g ∈ X.trivialSet x) :
    X.isotropyConj φ hx hy g ∈ X.trivialSet y := by
  obtain ⟨R, hR⟩ := hg
  obtain ⟨D, hDo, hyD, k, hk, hks, hkt, hky⟩ := exists_conj_section' X hx hy R hR
  exact mem_trivialSet_of_section' X hDo hyD hk hks hkt hky

theorem isotropyConj_mem_trivialSet_iff' {x y : Obj} (φ : Mor) (hx : X.src φ = x)
    (hy : X.tgt φ = y) (g : X.Isotropy x) :
    X.isotropyConj φ hx hy g ∈ X.trivialSet y ↔ g ∈ X.trivialSet x := by
  refine ⟨fun h => ?_, isotropyConj_mem_trivialSet' X φ hx hy⟩
  have hx' : X.src (X.inv φ) = y := (X.src_inv φ).trans hy
  have hy' : X.tgt (X.inv φ) = x := (X.tgt_inv φ).trans hx
  have h' := isotropyConj_mem_trivialSet' X (X.inv φ) hx' hy' h
  have hc : X.src g.val = X.tgt (X.inv φ) := by rw [g.src_val, hy']
  have he : X.isotropyConj (X.inv φ) hx' hy' (X.isotropyConj φ hx hy g) = g := by
    refine GroupoidStr.Isotropy.ext ?_
    simp only [GroupoidStr.isotropyConj_val]
    rw [X.comp_assoc _ _ _ (by rw [hx, g.tgt_val]) hc,
      GroupoidStr.inv_comp_cancel_left (by rw [X.tgt_comp _ _ hc, g.tgt_val, hx]),
      GroupoidStr.comp_inv_cancel_right hc]
  rw [he] at h'
  exact h'

theorem map_isotropyConj_trivialSubgroup' {x y : Obj} (φ : Mor) (hx : X.src φ = x)
    (hy : X.tgt φ = y) :
    (X.trivialSubgroup x).map (X.isotropyConj φ hx hy).toMonoidHom = X.trivialSubgroup y := by
  ext h
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact isotropyConj_mem_trivialSet' X φ hx hy hg
  · intro hh
    refine ⟨(X.isotropyConj φ hx hy).symm h,
      (isotropyConj_mem_trivialSet_iff' X φ hx hy _).1 ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [MulEquiv.apply_symm_apply]
    exact hh

end FromB

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {Obj Mor} _ _ _ _ _ _ X x _ => ?_,
    fun R => actsTrivially_iff' _ R,
    fun X => mem_trivialSet_of_section' X,
    fun X => mem_trivialSet_iff_eventually' X,
    fun X => exists_mem_nhds_trivialSet_iff' X,
    fun X => exists_naturalRep_trivialSet_iff_of_B X hB,
    fun X x V hV hx => ?_,
    fun X => trivialSubgroup_normal_of_B X hB,
    fun X => isEffective_iff_trivialSubgroup_eq_bot' X,
    fun X => isotropyConj_mem_trivialSet' X,
    fun X => map_isotropyConj_trivialSubgroup' X,
    fun R g hg y hy h hh => mem_trivialSet_of_val_eq_Γ' _ R hg hy hh⟩
  · exact ((hB Obj Mor X).2.1 x 1).2 ((hB Obj Mor X).2.2.2.1 x)
  · obtain ⟨R, hRV, hR⟩ := exists_naturalRep_trivialSet_iff_of_B X hB x hV hx
    exact ⟨R, hRV, Subgroup.ext fun g => R.mem_kerΦ.trans (hR g).symm⟩

#rt_check_soft RoundTrip.V7_37.A_to_B [Polyfold.EpGroupoid.one_mem_trivialSet,
  Polyfold.EpGroupoid.NaturalRep.actsTrivially_iff, Polyfold.EpGroupoid.mem_trivialSet_of_section,
  Polyfold.EpGroupoid.mem_trivialSet_iff_eventually,
  Polyfold.EpGroupoid.exists_mem_nhds_trivialSet_iff,
  Polyfold.EpGroupoid.exists_naturalRep_trivialSet_iff,
  Polyfold.EpGroupoid.exists_naturalRep_kerΦ_eq, Polyfold.EpGroupoid.trivialSubgroup_normal,
  Polyfold.EpGroupoid.isEffective_iff_trivialSubgroup_eq_bot,
  Polyfold.EpGroupoid.isotropyConj_mem_trivialSet,
  Polyfold.EpGroupoid.map_isotropyConj_trivialSubgroup,
  Polyfold.EpGroupoid.NaturalRep.mem_trivialSet_of_val_eq_Γ]
#rt_check_soft RoundTrip.V7_37.B_to_A [Polyfold.EpGroupoid.one_mem_trivialSet,
  Polyfold.EpGroupoid.NaturalRep.actsTrivially_iff, Polyfold.EpGroupoid.mem_trivialSet_of_section,
  Polyfold.EpGroupoid.mem_trivialSet_iff_eventually,
  Polyfold.EpGroupoid.exists_mem_nhds_trivialSet_iff,
  Polyfold.EpGroupoid.exists_naturalRep_trivialSet_iff,
  Polyfold.EpGroupoid.exists_naturalRep_kerΦ_eq, Polyfold.EpGroupoid.trivialSubgroup_normal,
  Polyfold.EpGroupoid.isEffective_iff_trivialSubgroup_eq_bot,
  Polyfold.EpGroupoid.isotropyConj_mem_trivialSet,
  Polyfold.EpGroupoid.map_isotropyConj_trivialSubgroup,
  Polyfold.EpGroupoid.NaturalRep.mem_trivialSet_of_val_eq_Γ]
#rt_overlap RoundTrip.V7_37.B_to_A [Polyfold.EpGroupoid.one_mem_trivialSet,
  Polyfold.EpGroupoid.NaturalRep.actsTrivially_iff, Polyfold.EpGroupoid.mem_trivialSet_of_section,
  Polyfold.EpGroupoid.mem_trivialSet_iff_eventually,
  Polyfold.EpGroupoid.exists_mem_nhds_trivialSet_iff,
  Polyfold.EpGroupoid.exists_naturalRep_trivialSet_iff,
  Polyfold.EpGroupoid.exists_naturalRep_kerΦ_eq, Polyfold.EpGroupoid.trivialSubgroup_normal,
  Polyfold.EpGroupoid.isEffective_iff_trivialSubgroup_eq_bot,
  Polyfold.EpGroupoid.isotropyConj_mem_trivialSet,
  Polyfold.EpGroupoid.map_isotropyConj_trivialSubgroup,
  Polyfold.EpGroupoid.NaturalRep.mem_trivialSet_of_val_eq_Γ]

end RoundTrip.V7_37
