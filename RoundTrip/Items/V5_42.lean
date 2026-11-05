import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_42

/-! **Refresh 2026-11-02** (HEAD after the germ reading of Definition 3.11 and the notions built
on it).
No declaration of A changed; B's hypothesis IsScFredholmSection now denotes the germ reading
(unused by A ⇒ B), and not_BLiteral now uses the germ-reading witness
TrivialBundle.isScFredholmSection_graphSection. Result unchanged.
-/

namespace RoundTrip.V5_42
open Polyfold

/-- The project's statement: the three theorems of the decls (universes at `0`): `lemma_5_23`
(for `ℓ ≠ 0` and `T = Z ⊕ ker ℓ`, a unique `b : S → Z` with `ℓ ∘ b = τ`, and `ℓ ∘ (b + a) = τ`),
`ne_zero_of_isCompl_ker` (the hidden hypothesis: a nonzero complement of `ker ℓ` forces `ℓ ≠ 0`)
and `exists_isCompl_ker_of_ne_zero` (for `ℓ ≠ 0` and a SPANNING set `D`, a line `ℝ e`, `e ∈ D`,
complementing `ker ℓ`).  All three are pure linear algebra on abstract modules. -/
def A : Prop :=
  (type_of% @Polyfold.lemma_5_23.{0, 0}) ∧
  (type_of% @Polyfold.ne_zero_of_isCompl_ker.{0}) ∧
  (type_of% @Polyfold.exists_isCompl_ker_of_ne_zero.{0})

theorem A_holds : A :=
  ⟨@Polyfold.lemma_5_23.{0, 0}, @Polyfold.ne_zero_of_isCompl_ker.{0},
    @Polyfold.exists_isCompl_ker_of_ne_zero.{0}⟩

set_option linter.unusedSectionVars false

/-! ### Analytic glue: derivatives at smooth points preserve smooth vectors -/

section Smooth

variable {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0} {D : E 1 → E 0 →L[ℝ] F 0}

/-- For an sc¹ map, at a smooth point `z ∈ U₁`, `Df(z)` maps smooth vectors to smooth vectors
(the level operators `Df(z) : E_m → F_m`). -/
theorem deriv_mem_smooth (h : IsSc1With U f D) {z : E 1} (hz : z ∈ E.smoothLvl 1)
    (hzU : z ∈ E.lvlSet U 1) {w : E 0} (hw : w ∈ E.smooth) : D z w ∈ F.smooth := by
  rw [ScScale.mem_smooth_iff]
  intro m
  obtain ⟨x, hx⟩ := E.mem_smoothLvl_iff.1 hz (m + 1)
  have hxz : E.shift.toBase m x = z := by
    apply E.toBase_injective 1
    rw [← E.shift_toBase, hx]
  have hxU : x ∈ E.lvlSet U (m + 1) := by
    rw [ScBanach.mem_lvlSet, hx]; exact hzU
  obtain ⟨v, hv⟩ := (ScScale.mem_smooth_iff (E := E.toScScale)).1 hw m
  refine ⟨levelDeriv D m x v, ?_⟩
  rw [h.toBase_levelDeriv hxU v, hxz, hv]

end Smooth

section Glue
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

open StrongRetr

/-- `KerT ≤ TO`. -/
theorem kerT_le (c : StrongBundleChart PX P) (t : X → ℝ) (z : c.φ.model.E.lvl 1) :
    KerT c t z ≤ TO c z := inf_le_left

/-- **The smooth line** (the part of Lemma 5.23's first sentence that A does not give: "since `x`
is a smooth point, we find a one-dimensional smooth sc-subspace `Z`"): if `dt(x) ≠ 0` on `T_zO`
at a smooth point, some smooth `e ∈ T_zO` has `dt(x)e ≠ 0` (smooth vectors are dense and
`Dr(z)` preserves them), and `Z = ℝ e` splits `T_zO = Z ⊕ ker dt(x)` on every level. -/
theorem exists_splits (c : StrongBundleChart PX P) (t : X → ℝ) (x : X) (hxs : x ∈ PX.smoothSet)
    (hxc : x ∈ c.φ.source) (z : c.φ.model.E.lvl 1)
    (hz : c.φ.model.E.toBase 1 z = c.φ.toPartialEquiv x)
    (hne : ∃ v ∈ TO c z, Dt c t z v ≠ 0) : ∃ Z, SplitsWith c t z Z := by
  classical
  have hxO : c.φ.toPartialEquiv x ∈ r c.R '' c.U := c.r_image ▸ c.φ.mapsTo_model x hxc
  have hzU : z ∈ c.φ.model.E.lvlSet c.U 1 := by
    rw [ScBanach.mem_lvlSet, hz]; exact mem_U_of_mem_O c.isRetraction hxO
  have hzs : z ∈ c.φ.model.E.smoothLvl 1 := by
    change c.φ.model.E.toBase 1 z ∈ c.φ.model.E.smooth
    rw [hz]; exact (PX.mem_smoothSet_iff c.isChart hxc).1 hxs
  have hrs := (r_isScSmooth c.relOpen c.isRetraction).isSc1.isSc1With_scDeriv
  -- a smooth `e = Dr(z)w'` with `Dt e ≠ 0`
  obtain ⟨v, ⟨w, rfl⟩, hvw⟩ := hne
  set φ' : c.φ.model.E.lvl 0 →L[ℝ] ℝ := (Dt c t z).comp (scDeriv c.U (r c.R) z) with hφ'
  have hopen : IsOpen {u : c.φ.model.E.lvl 0 | φ' u ≠ 0} :=
    isOpen_ne_fun φ'.continuous continuous_const
  obtain ⟨w', hw'ne, hw's⟩ :=
    (c.φ.model.E.dense_smooth 0).inter_open_nonempty _ hopen ⟨w, hvw⟩
  set e := scDeriv c.U (r c.R) z w' with he
  have hes : e ∈ c.φ.model.E.smooth := deriv_mem_smooth hrs hzs hzU hw's
  have heTO : e ∈ TO c z := ⟨w', rfl⟩
  have hDe : Dt c t z e ≠ 0 := hw'ne
  have he0 : e ≠ 0 := fun h => hDe (by rw [h, map_zero])
  refine ⟨ℝ ∙ e, finrank_span_singleton he0, ?_, ⟨?_, fun m => ?_⟩, ?_, fun m => ⟨?_, ?_⟩⟩
  · rw [Submodule.span_le]; rintro _ rfl; exact hes
  · exact Submodule.closed_of_finiteDimensional _
  · intro y hy
    refine subset_closure ⟨hy, ?_⟩
    change c.φ.model.E.toBase m y ∈ c.φ.model.E.smooth
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 ((ScBanach.mem_levelSub _).1 hy)
    rw [← ha]; exact c.φ.model.E.smooth.smul_mem a hes
  · rw [Submodule.span_le]; rintro _ rfl; exact heTO
  · -- disjointness on level `m`
    rw [disjoint_iff, eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    rw [Submodule.mem_bot]
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 ((ScBanach.mem_levelSub _).1 hy1)
    have h2 : Dt c t z (c.φ.model.E.toBase m y) = 0 := ((ScBanach.mem_levelSub _).1 hy2).2
    rw [← ha, map_smul, smul_eq_mul] at h2
    have ha0 : a = 0 := (mul_eq_zero.1 h2).resolve_right hDe
    apply c.φ.model.E.toBase_injective m
    rw [← ha, ha0, zero_smul, map_zero]
  · -- the sum is `T_zO` on level `m`
    apply le_antisymm
    · refine sup_le (fun y hy => ?_) (fun y hy => (kerT_le c t z) hy)
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 ((ScBanach.mem_levelSub _).1 hy)
      change c.φ.model.E.toBase m y ∈ TO c z
      rw [← ha]; exact (TO c z).smul_mem a heTO
    · intro y hy
      have hyTO : c.φ.model.E.toBase m y ∈ TO c z := hy
      obtain ⟨em, hem⟩ := (ScScale.mem_smooth_iff (E := c.φ.model.E.toScScale)).1 hes m
      set a := Dt c t z (c.φ.model.E.toBase m y) / Dt c t z e with ha
      have hsplit : y = a • em + (y - a • em) := by abel
      rw [hsplit]
      refine Submodule.add_mem_sup ?_ ?_
      · change c.φ.model.E.toBase m (a • em) ∈ ℝ ∙ e
        rw [map_smul, hem]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
      · change c.φ.model.E.toBase m (y - a • em) ∈ KerT c t z
        rw [map_sub, map_smul, hem]
        refine ⟨Submodule.sub_mem _ hyTO ((TO c z).smul_mem a heTO), ?_⟩
        change Dt c t z (c.φ.model.E.toBase m y - a • e) = 0
        rw [map_sub, map_smul, smul_eq_mul, ha, div_mul_cancel₀ _ hDe, sub_self]

/-- From `SplitsWith`, the line `Z` read inside `T_zO` complements `ker dt(x)` (level `0`). -/
theorem isCompl_of_splits (c : StrongBundleChart PX P) (t : X → ℝ) (z : c.φ.model.E.lvl 1)
    {Z : Submodule ℝ (c.φ.model.E.lvl 0)} (hZ : SplitsWith c t z Z) :
    IsCompl (Z.comap (TO c z).subtype)
      (LinearMap.ker ((Dt c t z).toLinearMap ∘ₗ (TO c z).subtype)) := by
  obtain ⟨-, -, -, hZT, hlev⟩ := hZ
  obtain ⟨hdisj, hsup⟩ := hlev 0
  rw [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at hdisj hsup
  rw [ScBanach.levelSub_zero] at hsup
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    rintro v ⟨hv1, hv2⟩
    have h : (v : c.φ.model.E.lvl 0) ∈ Z ⊓ KerT c t z := ⟨hv1, v.2, hv2⟩
    rw [hdisj.eq_bot, Submodule.mem_bot] at h
    rw [Submodule.mem_bot]; exact Subtype.ext h
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : (v : c.φ.model.E.lvl 0) ∈ Z ⊔ KerT c t z := by rw [hsup]; exact v.2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hv
    have hv' : v = ⟨a, hZT ha⟩ + ⟨b, hb.1⟩ := Subtype.ext (by simp [hab])
    rw [hv']
    exact Submodule.add_mem_sup ha hb.2

/-- `Z ≠ 0` from `finrank Z = 1`, read inside `T_zO`. -/
theorem comap_ne_bot (c : StrongBundleChart PX P) (t : X → ℝ) (z : c.φ.model.E.lvl 1)
    {Z : Submodule ℝ (c.φ.model.E.lvl 0)} (hZ : SplitsWith c t z Z) :
    Z.comap (TO c z).subtype ≠ ⊥ := by
  obtain ⟨h1, -, -, hZT, -⟩ := hZ
  intro hbot
  have hZ0 : Z = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have : (⟨v, hZT hv⟩ : TO c z) ∈ Z.comap (TO c z).subtype := hv
    rw [hbot, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]; exact congrArg Subtype.val this
  rw [hZ0, finrank_bot] at h1
  exact zero_ne_one h1

end Glue

/-- `A ⇒ B`.  (1) ⇒: A's `ne_zero_of_isCompl_ker` in `T_zO`; (1) ⇐: `exists_splits` (the density
argument, not in A: A's `exists_isCompl_ker_of_ne_zero` needs a SPANNING set, which the smooth
vectors of an infinite-dimensional `T_zO` are not, so it cannot produce a smooth `Z`); (2) and
(3): A's `lemma_5_23` in `T = T_zO`, `S = T_xS`, transported from `Z ∩ T_zO` to `Z` (continuity:
`Z` is a line). -/
theorem A_to_B : A → B := by
  rintro ⟨h523, hne, -⟩ X _ _ _ PX Y _ _ _ P _ _ Bd f t x _ _ hxs _ c _ hxc z hz
  set TOm := TO c z
  set ℓ : TOm →ₗ[ℝ] ℝ := (Dt c t z).toLinearMap ∘ₗ TOm.subtype with hℓ
  -- `ℓ ≠ 0` from a splitting
  have hℓne : ∀ Z, SplitsWith c t z Z → ℓ ≠ 0 := fun Z hZ =>
    hne (isCompl_of_splits c t z hZ) (comap_ne_bot c t z hZ)
  -- the linear algebra (2)
  have hb : ∀ Z, SplitsWith c t z Z → ∀ τ : TS c f z →L[ℝ] ℝ,
      ∃! b : TS c f z →L[ℝ] Z, ∀ v, Dt c t z (b v) = τ v := by
    intro Z hZ τ
    have hZT : Z ≤ TOm := hZ.2.2.2.1
    obtain ⟨⟨b₀, hb₀, -⟩, -⟩ := h523 (hℓne Z hZ) (isCompl_of_splits c t z hZ)
      (τ : TS c f z →ₗ[ℝ] ℝ)
    -- `Dt` is injective on `Z`
    have hinj : ∀ u w : Z, Dt c t z u = Dt c t z w → u = w := by
      intro u w huw
      have hu : (u : c.φ.model.E.lvl 0) - w ∈ Z ⊓ KerT c t z :=
        ⟨Z.sub_mem u.2 w.2, TOm.sub_mem (hZT u.2) (hZT w.2), by
          change Dt c t z ((u : c.φ.model.E.lvl 0) - w) = 0
          rw [map_sub, huw, sub_self]⟩
      have hd := (hZ.2.2.2.2 0).1
      rw [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at hd
      rw [hd.eq_bot, Submodule.mem_bot, sub_eq_zero] at hu
      exact Subtype.ext hu
    -- `Z ∩ T_zO → Z`
    set ι : Z.comap TOm.subtype →ₗ[ℝ] Z :=
      ((TOm.subtype ∘ₗ (Z.comap TOm.subtype).subtype).codRestrict Z fun u => u.2) with hι
    set bl : TS c f z →ₗ[ℝ] Z := ι ∘ₗ b₀ with hbl
    have hbl : ∀ v, Dt c t z (bl v) = τ v := fun v => by
      have := LinearMap.congr_fun hb₀ v
      exact this
    -- continuity: `Z` is finite-dimensional (a line)
    have hfin : FiniteDimensional ℝ Z :=
      Module.finite_of_finrank_eq_succ hZ.1
    -- `bl = (Dt|_Z)⁻¹ ∘ τ` is continuous
    set DZ : Z →ₗ[ℝ] ℝ := (Dt c t z).toLinearMap ∘ₗ Z.subtype with hDZ
    have hDZinj : Function.Injective DZ := fun u w h => hinj u w h
    have hDZ0 : DZ ≠ 0 := by
      intro h0
      obtain ⟨u, hu⟩ := (Submodule.exists_mem_ne_zero_of_ne_bot (p := Z) (by
        intro hbot; have h1 := hZ.1; rw [hbot, finrank_bot] at h1; exact zero_ne_one h1))
      exact hu.2 (congrArg Subtype.val (hDZinj (a₁ := ⟨u, hu.1⟩) (a₂ := 0)
        (by rw [h0, map_zero]; rfl)))
    have hcont : Continuous bl := by
      have hDZc : Continuous DZ := LinearMap.continuous_of_finiteDimensional DZ
      -- `bl` is continuous since `DZ ∘ bl = τ` and `DZ` is a homeomorphism onto `ℝ`
      have hsurj : Function.Surjective DZ := by
        have hrange : LinearMap.range DZ ≠ ⊥ := by
          rwa [Ne, LinearMap.range_eq_bot]
        intro r
        obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hrange
        obtain ⟨u, rfl⟩ := hy
        exact ⟨(r / DZ u) • u, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hy0]⟩
      set eZ := LinearEquiv.ofBijective DZ ⟨hDZinj, hsurj⟩ with heZ
      have hsymm : Continuous eZ.symm := LinearMap.continuous_of_finiteDimensional _
      have hbl' : (bl : TS c f z → Z) = eZ.symm ∘ τ := by
        funext v
        apply hDZinj
        change DZ (bl v) = DZ (eZ.symm (τ v))
        rw [show DZ (eZ.symm (τ v)) = eZ (eZ.symm (τ v)) from rfl, LinearEquiv.apply_symm_apply]
        exact hbl v
      rw [hbl']; exact hsymm.comp τ.continuous
    refine ⟨⟨bl, hcont⟩, hbl, fun b' hb' => ?_⟩
    ext v
    exact congrArg Subtype.val (hinj _ _ ((hb' v).trans (hbl v).symm))
  refine ⟨⟨fun ⟨Z, hZ⟩ => ?_, exists_splits c t x hxs hxc z hz⟩, hb, ?_⟩
  · -- (1) ⇒
    have h := hℓne Z hZ
    by_contra hcon
    push Not at hcon
    exact h (LinearMap.ext fun v => hcon v v.2)
  · -- (3), from the second half of `lemma_5_23`
    intro Z hZ τ b hbτ a v
    have hZT : Z ≤ TOm := hZ.2.2.2.1
    obtain ⟨-, h2⟩ := h523 (hℓne Z hZ) (isCompl_of_splits c t z hZ)
      (τ : TS c f z →ₗ[ℝ] ℝ)
    set bT : TS c f z →ₗ[ℝ] TOm :=
      ((Z.subtype ∘ₗ (b : TS c f z →ₗ[ℝ] Z)).codRestrict TOm fun u => hZT (b u).2)
    set aT : TS c f z →ₗ[ℝ] TOm :=
      (((KerT c t z).subtype ∘ₗ (a : TS c f z →ₗ[ℝ] KerT c t z)).codRestrict TOm
        fun u => (a u).2.1)
    have h := h2 bT aT (LinearMap.ext fun u => hbτ u) (fun u => (a u).2.2)
    exact LinearMap.congr_fun h v

/-! ### The literal reading is false

`BLiteral` (the text's first sentence without the hidden hypothesis `dt(x) ≠ 0`) fails already for
the trivial bundle `ℝ¹ × ℝ⁰ → ℝ¹` (`TrivialBundle`, the project's non-vacuity witness), the zero
section, the smooth zero `x = 0` and the constant function `t = 0`: then `dt(x) = 0`, and a
splitting `T_xX = Z ⊕ ker dt(x)` with `dim Z = 1` would give a vector `ζ ∈ Z ⊆ T_xX` with
`dt(x)ζ ≠ 0`. -/

/-- A splitting forces `dt(x) ≠ 0` on `T_zO` (direct, without A). -/
theorem exists_ne_zero_of_splits {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] {P : Y → X}
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (c : StrongBundleChart PX P) (t : X → ℝ) (z : c.φ.model.E.lvl 1)
    {Z : Submodule ℝ (c.φ.model.E.lvl 0)} (hZ : SplitsWith c t z Z) :
    ∃ v ∈ TO c z, Dt c t z v ≠ 0 := by
  obtain ⟨h1, -, -, hZT, hlev⟩ := hZ
  have hne : Z ≠ ⊥ := by
    intro hbot; rw [hbot, finrank_bot] at h1; exact zero_ne_one h1
  obtain ⟨ζ, hζ, hζ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨ζ, hZT hζ, fun h0 => hζ0 ?_⟩
  have hd := (hlev 0).1
  rw [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at hd
  have hmem : ζ ∈ Z ⊓ KerT c t z := ⟨hζ, hZT hζ, h0⟩
  rwa [hd.eq_bot, Submodule.mem_bot] at hmem

open TrivialBundle in
open scoped ContDiff in
theorem not_BLiteral : ¬ BLiteral := by
  intro h
  have hφ : ContDiff ℝ ∞ (fun _ : Fin 1 → ℝ => (0 : Fin 0 → ℝ)) := contDiff_const
  obtain ⟨Z, hZ⟩ := h (rnPolyfold 1) (proj 1 0) (bundle 1 0) (graphSection fun _ => 0)
    (fun _ => 0) 0 (isScFredholmSection_graphSection hφ) (isScSmoothMap_real_const 0)
    (by rw [rnPolyfold_smoothSet]; exact Set.mem_univ _) (isZeroAt_graphSection_iff.2 rfl)
    (chart 0) (isChart_chart 0) (Set.mem_univ _) 0 (by rw [map_zero]; exact (sub_self _).symm)
  obtain ⟨v, -, hv⟩ := exists_ne_zero_of_splits _ _ _ hZ
  apply hv
  have hD := scDeriv_univ_const (V := Fin 1 → ℝ) (V' := ℝ)
    (contDiff_const (c := (0 : ℝ))) (0 : Fin 1 → ℝ)
  change scDeriv (E := ScBanach.const (Fin 1 → ℝ)) (F := ScBanach.const ℝ) Set.univ
    (fun _ => (0 : ℝ)) 0 v = 0
  rw [hD, fderiv_const_apply]
  rfl

/-! `B ⇒ A` is not proved: A is linear algebra on ARBITRARY real modules `T, S` with an arbitrary
linear `ℓ : T → ℝ` and complement `Z` (and an arbitrary spanning set `D`); B is the instance
`T = T_zO`, `S = T_xS = ker f'(x)`, `ℓ = dt(x)` inside a strong bundle chart.  Recovering A would
need to realise every such module and functional as chart data of a strong bundle (not possible
in general: `T` need not even carry a Banach topology), so A is strictly more general.  -/

#rt_check RoundTrip.V5_42.A_to_B [Polyfold.lemma_5_23, Polyfold.ne_zero_of_isCompl_ker,
  Polyfold.exists_isCompl_ker_of_ne_zero]
#rt_check RoundTrip.V5_42.not_BLiteral [Polyfold.lemma_5_23, Polyfold.ne_zero_of_isCompl_ker,
  Polyfold.exists_isCompl_ker_of_ne_zero]

end RoundTrip.V5_42
