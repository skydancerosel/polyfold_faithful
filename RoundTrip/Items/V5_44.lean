import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_44

/-! **Refresh 2026-11-02** (HEAD after the germ reading of Definition 3.11 and the notions built
on it).
No declaration of A changed; B's IsScFredholmSectionTame now denotes the germ reading and still
supplies the sc-smoothness of f in every chart used by A ⇒ BStrong. The obstacle (weak vs
pointwise bump functions) is untouched. Result unchanged.
-/

namespace RoundTrip.V5_44
open Polyfold

/-- The project's statement: the two theorems of the decls (universes at `0`):
`exists_scPlusSection_linAt` (for a strong bundle chart around a smooth point `x`, a smooth `e`
over `x`, a continuous functional `ℓ` and an open `U ∋ x`, an sc⁺-section `s` with `s(x) = 0`,
`supp s ⊆ U` and `Lin_s(z)v = ℓ(v)·Φ(e)₂` on `T_zO`) and `lemma_5_24` (for a finite-dimensional
`K ⊆ T_zO` and `b : K → T_zO` with `Lin_f(z) ∘ b` in the line `ℝ·Φ(e)₂`, an sc⁺-section with
`Lin_f(z)(b v) + Lin_s(z)v = 0` on `K`).  Both assume `AdmitsBumpFunctions` (`f(x) ≠ 0`). -/
def A : Prop :=
  (type_of% @Polyfold.exists_scPlusSection_linAt.{0, 0}) ∧
  (type_of% @Polyfold.lemma_5_24.{0, 0})

theorem A_holds : A := ⟨@Polyfold.exists_scPlusSection_linAt.{0, 0}, @Polyfold.lemma_5_24.{0, 0}⟩

/-- B with the project's (strong) reading of "bump functions": `AdmitsBumpFunctions`
(`f(x) ≠ 0`) in place of `AdmitsBumpFunctionsWeak` (`f ≢ 0`); otherwise literally B. -/
def BStrong : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (t : X → ℝ) (x : X),
    IsTameStrongBundle Bd → PX.AdmitsBumpFunctions →
    Bd.IsScFredholmSectionTame f → PX.IsScSmoothMap realPolyfold t →
    x ∈ PX.smoothSet → IsZeroAt P f x →
    ∀ c : StrongBundleChart PX P, Bd.IsChart c → x ∈ c.φ.source →
    ∀ z : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z = c.φ.toPartialEquiv x →
    ∀ Z : Submodule ℝ (c.φ.model.E.lvl 0), SplitsWith c t z Z →
    ∀ (τ : TS c f z →L[ℝ] ℝ) (b : TS c f z →L[ℝ] Z), (∀ v, Dt c t z (b v) = τ v) →
    ∀ V : Set X, IsOpen V → x ∈ V →
      ∃ s : X → Y, Bd.IsScPlusSection s ∧ suppB P s ⊆ V ∧ IsZeroAt P s x ∧
        ∀ v : TS c f z, Dg c f z (b v) + Dg c s z v = 0

/-- B gives BStrong (strong bump functions give weak ones). -/
theorem BStrong_of_B : B → BStrong := by
  intro hB X _ _ _ PX Y _ _ _ P _ _ Bd f t x hT hbump
  exact hB PX P Bd f t x hT hbump.weak

/-! ### Analytic glue -/

section Smooth

variable {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0} {D : E 1 → E 0 →L[ℝ] F 0}

/-- For an sc¹ map, at a smooth point `z ∈ U₁`, `Df(z)` maps smooth vectors to smooth vectors. -/
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

set_option linter.unusedSectionVars false

open StrongRetr in
/-- **`A ⇒ BStrong`.**  `b` takes values in the line `Z = ℝζ` (`ζ` smooth, `dt(x)ζ ≠ 0`), so
`b v = (τ v / dt(x)ζ)·ζ`; `Dg(ζ)` lies in the fibre `K_{φ(x)}` (`rho_scDeriv_comp_r`, `x` a
zero) and is smooth (level operators at the smooth point), so it is `Φ(e)₂` for a smooth point `e`
of `Y` over `x`; with `ℓ` a Hahn–Banach extension of `−τ/dt(x)ζ` from `T_xS` to `E`, A's
`exists_scPlusSection_linAt` gives `s` with `Lin_s(z)v = ℓ(v)·Dg(ζ)`. -/
theorem A_to_BStrong : A → BStrong := by
  rintro ⟨hex, -⟩ X _ _ _ PX Y _ _ _ P _ _ Bd f t x _ hbump hf _ hxs hx0 c hc hxc z hz Z hZ
    τ b hbτ V hV hxV
  -- `ζ`: a nonzero vector of `Z`, with `dt(x)ζ ≠ 0`
  obtain ⟨h1, hZs, -, hZT, hlev⟩ := hZ
  have hZne : Z ≠ ⊥ := by
    intro hbot; rw [hbot, finrank_bot] at h1; exact zero_ne_one h1
  obtain ⟨ζ, hζ, hζ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZne
  have hDtζ : Dt c t z ζ ≠ 0 := by
    intro h0
    have hd := (hlev 0).1
    rw [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at hd
    have hmem : ζ ∈ Z ⊓ KerT c t z := ⟨hζ, hZT hζ, h0⟩
    rw [hd.eq_bot, Submodule.mem_bot] at hmem
    exact hζ0 hmem
  -- every vector of `Z` is a multiple of `ζ`
  have hline : ∀ w ∈ Z, ∃ a : ℝ, a • ζ = w := by
    intro w hw
    have := (finrank_eq_one_iff_of_nonzero' (⟨ζ, hζ⟩ : Z) (by
      intro h; exact hζ0 (congrArg Subtype.val h))).1 h1 ⟨w, hw⟩
    obtain ⟨a, ha⟩ := this
    exact ⟨a, congrArg Subtype.val ha⟩
  have hbv : ∀ v, (b v : c.φ.model.E.lvl 0) = (τ v / Dt c t z ζ) • ζ := by
    intro v
    obtain ⟨a, ha⟩ := hline _ (b v).2
    have h2 := hbτ v
    rw [← ha, map_smul, smul_eq_mul] at h2
    rw [← ha, ← h2, mul_div_cancel_right₀ _ hDtζ]
  -- the chart data at `x`
  have hfs : IsSection P f := hf.isScSmooth.1
  have hxO : c.φ.toPartialEquiv x ∈ r c.R '' c.U := c.r_image ▸ c.φ.mapsTo_model x hxc
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by rw [hz]; exact hxO
  have hzU : z ∈ c.φ.model.E.lvlSet c.U 1 := mem_U_of_mem_O c.isRetraction hzO
  have hzs : z ∈ c.φ.model.E.smoothLvl 1 := by
    change c.φ.model.E.toBase 1 z ∈ c.φ.model.E.smooth
    rw [hz]; exact (PX.mem_smoothSet_iff c.isChart hxc).1 hxs
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) := hf.isScSmooth.isSc1_principal_comp_r hc
  have hfK : ∀ u ∈ r c.R '' c.U, (u, c.principal f u) ∈ c.R '' (c.U ×ˢ Set.univ) :=
    fun u hu => c.principal_mem_K hfs (c.r_image ▸ hu)
  have hfz : c.principal f (c.φ.model.E.toBase 1 z) = 0 := by
    rw [hz]
    refine c.principal_eq_zero_of_isZeroAt hfs (c.φ.mapsTo_model x hxc) ?_
    rw [c.φ.symm_apply_apply hxc]; exact hx0
  -- `Dg(ζ) ∈ K_{φ(x)} ∩ F_∞`
  set k := Dg c f z ζ with hk
  have hρ := rho_scDeriv_comp_r c.relOpen c.isRetraction hfr hfK hzO hfz ζ
  have hkK : (c.φ.toPartialEquiv x, k) ∈ c.K := by
    have := (mem_rangeS_ρCLM_iff c.isRetraction hzO (mem_U_of_mem_O c.isRetraction hzO)).1
      ⟨k, hρ⟩
    rw [hz] at this; exact this
  have hks : k ∈ c.F.smooth := deriv_mem_smooth hfr.isSc1With_scDeriv hzs hzU (hZs hζ)
  -- the smooth point `e = Φ⁻¹(φ(x), k)` over `x`
  set e := c.toPartialEquiv.symm (c.φ.toPartialEquiv x, k) with he
  have hesm : e ∈ Bd.toMPolyfold0.smoothSet :=
    mem_smoothSet_toMPolyfold0_of_chart hc hkK ((PX.mem_smoothSet_iff c.isChart hxc).1 hxs) hks
  have hPe : P e = x := by
    rw [he, c.proj_symm hkK]; exact c.φ.symm_apply_apply hxc
  have hce : (c e).2 = k := by rw [he, c.apply_symm hkK]
  -- `ℓ`: a continuous extension of `−τ/dt(x)ζ` from `T_xS` to `E`
  obtain ⟨ℓ, hℓ, -⟩ := exists_extension_norm_eq (TS c f z) (-(Dt c t z ζ)⁻¹ • τ)
  obtain ⟨s, hs, hsx, hsupp, hlin⟩ := hex hbump hc hxc hxs hz hesm hPe ℓ hV hxV
  refine ⟨s, hs, hsupp, hsx, fun v => ?_⟩
  have hvTO : (v : c.φ.model.E.lvl 0) ∈ TO c z := v.2.1
  have hs' : Dg c s z v = ℓ v • k := by
    have := hlin ⟨v, hvTO⟩
    rw [hce] at this
    exact this
  rw [hs', hℓ v, hbv v, map_smul]
  change (τ v / Dt c t z ζ) • k + ((-(Dt c t z ζ)⁻¹ • τ) v) • k = 0
  rw [smul_apply, smul_eq_mul, ← add_smul]
  rw [show τ v / Dt c t z ζ + -(Dt c t z ζ)⁻¹ * τ v = 0 by ring, zero_smul]

/-! `A ⇒ B` is not proved: B assumes only `AdmitsBumpFunctionsWeak` (a bump function `f ≢ 0` with
support in `U`), A needs `AdmitsBumpFunctions` (`f(x) ≠ 0`); the project has only strong ⇒ weak
(`AdmitsBumpFunctions.weak`).  The construction of Lemma 5.24 needs a bump `β` equal to `1` near
`x` (Proposition 5.30, from `f(x) ≠ 0`), which a bump vanishing at `x` does not give.  With the
project's reading (`BStrong`) the implication is proved: `A_to_BStrong`; and `B ⇒ BStrong`.

`B ⇒ A` is not proved: A's `exists_scPlusSection_linAt` prescribes `Lin_s(z) = ℓ(·)Φ(e)₂` on all
of `T_zO` for an ARBITRARY functional `ℓ`, smooth `e` and strong bundle (no tameness, no
sc-Fredholm `f`, no `t`, no `Z`); `lemma_5_24` is for an arbitrary section `f`, any
finite-dimensional `K ⊆ T_zO` and any `b` into `T_zO` with `Lin_f ∘ b` in a smooth line.  B only
controls `s'(x)` on `T_xS = ker f'(x)` for `b` with values in a smooth complement `Z` of
`ker dt(x)`, under a tame strong bundle and tame germ data. -/

#rt_check RoundTrip.V5_44.A_to_BStrong [Polyfold.exists_scPlusSection_linAt, Polyfold.lemma_5_24]

end RoundTrip.V5_44
