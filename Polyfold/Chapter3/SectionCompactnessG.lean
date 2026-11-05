import Polyfold.Chapter3.SectionCompactness
import Polyfold.Chapter3.GermFillingChart
import Polyfold.Chapter3.GermCalculus
import Polyfold.Chapter3.BasicGermShrink

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
**Theorem 3.12** (local compactness for sc-Fredholm germs) and **Corollary 3.13** at the base
point, **in the text's germ reading of Definition 3.11** (phase 2): the filling `g` and the
sc⁺-section `t₀` are sc-smooth germs on germs of neighbourhoods `G_g`, `G_s` whose levels may
shrink with the level.

# Local compactness of the solution set of an sc-Fredholm germ, germ reading

## What is formalized

* `Polyfold.theorem_3_12` (the germ version of `theorem_3_12_wholeChart`, hypothesis
  `B.IsScFredholmGerm f x₀`): nested open `O(i) ∋ x₀` such that `closure {x ∈ O(i) | f(x) = 0}`
  is the image of a compact subset of `X_i` under the inclusion `X_i → X`.
* `Polyfold.corollary_3_13` (the germ version of `corollary_3_13_wholeChart`).

## What the text leaves implicit, and the choices made

* **What the old proof used of `g` and `t₀`, and how the germ reading supplies it.**  The proof of
  `theorem_3_12_wholeChart` uses (i) the identities of the filler (conditions (1), (2)) and of the
  conjugation pointwise near `0` — unchanged; (ii) the push-forward `t = Ψ[1]_*(t₀)` only as an
  **sc⁰-germ** on the germ of the basic germ (the input of Theorem 3.40); it was built as a
  section on all of `U'` from `t₀` sc-smooth on `U`.  With `t₀` a germ on `G_s`, `t` is an
  sc⁰-germ on `G″ = ψ'⁻¹(G_s) ⊆ G` (`ScNbhdGerm.preimage`; `IsSc0Germ.comp`, `IsSc0.comp_germ`),
  and the basic germ restricts to `G″` (`IsBasicGerm.mono`), so Theorem 3.40 is applied on `G″`;
  (iii) the continuity of `g` at the `E₀`-limits `ψ'(u')` of zeros, `u' ∈ closure A` — these lie in
  `U ∩ N₁`, and `N₁` is now also chosen inside the open set `O_g` with `(G_g)₀ = O_g ∩ C`, so
  `ψ'(u') ∈ (G_g)₀`, where `g` is continuous (level `0` of the sc⁰-germ `g`).  Nothing of `g`
  away from a level-`0` neighbourhood of `0` is used, and no level `≥ 1` of `G_g` at all.
* As in `theorem_3_12_wholeChart`, only `P ∘ f = id` is used of the section `f`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

section Bundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **Theorem 3.12 (local compactness for sc-Fredholm germs), germ reading** (phase 2; the germ
version of `theorem_3_12_wholeChart`, hypothesis `B.IsScFredholmGerm f x₀` of Definition 3.11 in the text's
germ reading): let `f` be a section of the strong bundle `P : Y → X` and `x₀` a smooth point with
`(f, x₀)` an sc-Fredholm germ and `f(x₀) = 0`.  Then there are nested open neighbourhoods
`O(0) ⊃ O(1) ⊃ …` of `x₀` in `X` such that for every `i` the closure in `X` of
`{x ∈ O(i) | f(x) = 0}` is the image of a compact subset of `X_i` (with the level topology) under
the inclusion `X_i → X`.  The proof is that of `theorem_3_12_wholeChart` with Theorem 3.40 applied on the germ
`G″ = ψ'⁻¹(G_s)` and the continuity of `g` used on `(G_g)₀` only. -/
theorem theorem_3_12 (hf : IsSection P f) {x₀ : X} (hg : B.IsScFredholmGerm f x₀)
    (hx₀ : IsZeroAt P f x₀) :
    ∃ O : ℕ → Set X, (∀ i, IsOpen (O i)) ∧ (∀ i, x₀ ∈ O i) ∧ (∀ i, O (i + 1) ⊆ O i) ∧
      ∀ i, ∃ K : Set (PX.Level i), IsCompact K ∧
        PX.levelVal i '' K = closure {x ∈ O i | IsZeroAt P f x} := by
  obtain ⟨hxs, c, hc, hxV, h0, h0U, g, t₀, hfill, ⟨Gs, -, ht₀⟩, ht₀0, hconj⟩ := hg
  -- the germ `G_g` of the filling and its level-`0` open set `O_g` (`(G_g)₀ = O_g ∩ C`)
  obtain ⟨Gg, -, hgG, -⟩ := hfill.germ
  obtain ⟨Ogg, hOgg, hGgeq⟩ := Gg.relOpen 0
  have h0Ogg : (0 : c.φ.model.E 0) ∈ Ogg := by
    have := Gg.zero_mem 0
    rw [hGgeq] at this
    exact this.1
  -- `g` is continuous on `(G_g)₀` (level `0` of the sc⁰-germ `g`)
  have hgcont : ContinuousOn g (Gg.U 0) :=
    ((hgG 0 : IsSc0Germ Gg g).continuousOn 0).congr fun x _ => (levelMap_zero g x).symm
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh,
    hev⟩ := hconj
  -- notation
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  set ψ' := IsStrongBundleMap.base Ψ' with hψ'def
  have hψψ' : ∀ u ∈ c.U, ψ' (ψ u) = u := fun u hu => hΨ.base_base hu
  have hψ'ψ : ∀ u' ∈ U', ψ (ψ' u') = u' := fun u' hu' => hΨ.base_base' hu'
  set fb := c.principal f with hfbdef
  set sb : c.φ.model.E 0 → c.F 0 := fun u => c.F.toBase 1 (t₀ u) with hsbdef
  have hU := c.relOpen
  have hOU : c.φ.model.O ⊆ c.U := fun z hz => by
    rw [← c.r_image] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact StrongRetr.r_mem c.isRetraction hv
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := h0 ▸ c.φ.mapsTo_model x₀ hxV
  have hC'closed : IsClosed (Ct ×ˢ (univ : Set (W 0))) := hU'.isPartialQuadrant.isClosed
  have hU'C : U' ⊆ Ct ×ˢ univ := by
    obtain ⟨Uo, -, rfl⟩ := hU'.relOpen; exact inter_subset_right
  have h0U' : (0 : (ScBanach.paramProd Pn W) 0) ∈ U' := hψ0 ▸ hΨ.toFun.base_mem h0U
  have hψ'0 : ψ' 0 = 0 := hΨ.base_zero' h0U hψ0
  -- `ψ'` is sc-smooth, hence sc⁰ and continuous on `U'`
  have hψ'sc : IsScSmooth U' ψ' := hΨ.invFun.base_isScSmooth hU'
  have hψ'sc0 : IsSc0 _ _ U' ψ' := hψ'sc.isSc1.isSc0
  have hψ'cont : ContinuousOn ψ' U' := hψ'sc0.continuousOn_base
  have hψcont : ContinuousOn ψ c.U := (hΨ.toFun.base_isScSmooth hU).isSc1.isSc0.continuousOn_base
  -- the neighbourhood `N₁` of `0` where the identities of the filler and the conjugation hold
  have hN₀ : ∀ᶠ u in 𝓝 (0 : c.φ.model.E 0), (u ∈ c.φ.model.O → fb u = g u) ∧
      (u ∈ c.U → g u = StrongRetr.ρ c.R (StrongRetr.r c.R u) (g u) → u ∈ c.φ.model.O) ∧
      (u ∈ c.U → (Ψ (u, g u - sb u)).2 = h (ψ u)) ∧ u ∈ Ogg := by
    have h1 := hfill.eq_on
    have h2 := hfill.mem_of_fixed
    rw [c.r_image] at h1 h2
    refine (h1.and (h2.and (hev.and (hOgg.mem_nhds h0Ogg)))).mono fun u hu =>
      ⟨hu.1, hu.2.1, fun huU => hu.2.2.1 huU, hu.2.2.2⟩
  obtain ⟨N₁, hN₁sub, hN₁open, h0N₁⟩ := mem_nhds_iff.1 hN₀
  have hN₁ : ∀ u ∈ N₁, (u ∈ c.φ.model.O → fb u = g u) ∧
      (u ∈ c.U → g u = StrongRetr.ρ c.R (StrongRetr.r c.R u) (g u) → u ∈ c.φ.model.O) ∧
      (u ∈ c.U → (Ψ (u, g u - sb u)).2 = h (ψ u)) ∧ u ∈ Ogg := fun u hu => hN₁sub hu
  -- points of `U ∩ N₁` lie in `(G_g)₀`, where `g` is continuous
  have hmemGg : ∀ u ∈ c.U, u ∈ N₁ → u ∈ Gg.U 0 := fun u hu huN => by
    rw [hGgeq]; exact ⟨(hN₁ u huN).2.2.2, hU.subset_quadrant hu⟩
  -- zeros of `g` in `U ∩ N₁` lie in `O`
  have hgO : ∀ u ∈ c.U, u ∈ N₁ → g u = 0 → u ∈ c.φ.model.O := fun u hu huN hgu =>
    (hN₁ u huN).2.1 hu (by
      rw [hgu]
      exact ((StrongRetr.ρ_isLinear c.isRetraction
        (StrongRetr.r_mem c.isRetraction hu)).map_zero).symm)
  -- `f̂(0) = g(0) = 0`, `t₀(0) = 0`
  have hfb0 : fb 0 = 0 := by
    have := (c.isZeroAt_iff hf hxV).1 hx₀
    rwa [h0] at this
  have hg0 : g 0 = 0 := by rw [← (hN₁ 0 h0N₁).1 h0O, hfb0]
  have ht00 : t₀ 0 = 0 := by
    apply c.F.toBase_injective 1
    rw [ht₀0, hg0, map_zero]
  -- the germ `G″ = ψ'⁻¹(G_s)` inside the basic germ's `G`, and the basic germ on it
  have hψ'G : IsSc0Germ (F := c.φ.model.E) G ψ' :=
    (hψ'sc0.isSc0Germ hU'.relOpen h0U').mono fun _ _ hz => hG (G.toBase_mem hz)
  have hψ'C : MapsTo ψ' (G.U 0) c.φ.model.C := fun u' hu' =>
    hU.subset_quadrant (hΨ.invFun.base_mem (hG hu'))
  set G'' := G.preimage Gs hψ'G hψ'0 hψ'C with hG''def
  have hG''G : ∀ m, G''.U m ⊆ G.U m := G.preimage_subset Gs hψ'G hψ'0 hψ'C
  have hG''U' : G''.U 0 ⊆ U' := fun _ hz => hG (hG''G 0 hz)
  have hh'' : IsBasicGerm Ct G'' h Bc := hh.mono hCt.isQuadrantLike hG''G
  -- the push-forward sc⁺-germ `t = Ψ[1]_*(t₀)`, an sc⁰-germ into `(ℝᴺ ⊕ W)¹` on `G″`
  set t : (ScBanach.paramProd Pn W) 0 → (ScBanach.paramProd Q W).shift 0 :=
    fun u' => (shiftFiber Ψ (ψ' u', t₀ (ψ' u'))).2 with htdef
  have ht : IsSc0Germ (E := ScBanach.paramProd Pn W) (F := (ScBanach.paramProd Q W).shift) G''
      t := by
    have hψ'G'' : IsSc0Germ (F := c.φ.model.E) G'' ψ' := hψ'G.mono hG''G
    have ht₀ψ' : IsSc0Germ (F := c.F.shift) G'' (t₀ ∘ ψ') :=
      IsSc0Germ.comp (ht₀ 0 : IsSc0Germ (F := c.F.shift) Gs t₀) hψ'G''
        (G.preimage_mapsToGerm Gs hψ'G hψ'0 hψ'C)
    have hpair := hψ'G''.pair ht₀ψ'
    have hfibsc : IsSc0 _ _ (c.U ×ˢ univ)
        fun p : (c.φ.model.E.prod c.F.shift) 0 => (shiftFiber Ψ p).2 :=
      (hΨ.toFun.isScSmooth_one.snd (hU.prod_univ c.F.shift).isScDomain).isSc1.isSc0
    exact (hfibsc.comp_germ hpair fun u' hu' =>
      ⟨hΨ.invFun.base_mem (hG''U' hu'), mem_univ _⟩).congr fun _ _ => rfl
  have ht0 : t 0 = 0 := by
    simp only [htdef, hψ'0, ht00]
    unfold shiftFiber
    simp only [map_zero]
    rw [hΨ.toFun.snd_zero h0U]
    have := Function.leftInverse_invFun ((ScBanach.paramProd Q W).toBase_injective 1) 0
    rw [map_zero] at this
    exact this
  -- the key identity: for `u ∈ U ∩ N₁`, `h(ψ u) + ι t(ψ u) = 0 ⟺ g(u) = 0`
  have hkey : ∀ u ∈ c.U, u ∈ N₁ →
      (h (ψ u) + (ScBanach.paramProd Q W).toBase 1 (t (ψ u)) = 0 ↔ g u = 0) := by
    intro u hu huN
    have e1 : t (ψ u) = (shiftFiber Ψ (u, t₀ u)).2 := by
      simp only [htdef]; rw [hψψ' u hu]
    have e2 : (ScBanach.paramProd Q W).toBase 1 (shiftFiber Ψ (u, t₀ u)).2 = (Ψ (u, sb u)).2 :=
      hΨ.toFun.toBase_shiftFiber_snd (p := (u, t₀ u)) hu
    have e3 : h (ψ u) = (Ψ (u, g u - sb u)).2 := ((hN₁ u huN).2.2.1 hu).symm
    rw [e1, e2, e3, hΨ.toFun.snd_sub hu, sub_add_cancel]
    exact hΨ.snd_eq_zero_iff hu
  -- a ball in `E'₀` whose closed version lies in `U'` and is mapped by `ψ'` into `N₁`
  have hW' : ∀ᶠ u' in 𝓝 (0 : (ScBanach.paramProd Pn W) 0), u' ∈ U' → ψ' u' ∈ N₁ := by
    have h1 : Tendsto ψ' (𝓝[U'] 0) (𝓝 0) := by
      have := hψ'cont 0 h0U'
      rwa [ContinuousWithinAt, hψ'0] at this
    exact eventually_nhdsWithin_iff.1 (h1 (hN₁open.mem_nhds h0N₁))
  obtain ⟨W', hW'sub, hW'open, h0W'⟩ := mem_nhds_iff.1 hW'
  obtain ⟨Uo, hUo, hU'eq⟩ := hU'.relOpen
  obtain ⟨ρ', hρ', hball⟩ := Metric.isOpen_iff.1 (hUo.inter hW'open) 0 ⟨hU'eq ▸ h0U' |>.1, h0W'⟩
  set r₀ := ρ' / 2 with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  have hcball : Metric.closedBall (0 : (ScBanach.paramProd Pn W) 0) r₀ ⊆ Uo ∩ W' :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hcl_mem : ∀ u' ∈ Metric.closedBall (0 : (ScBanach.paramProd Pn W) 0) r₀ ∩ Ct ×ˢ univ,
      u' ∈ U' ∧ u' ∈ W' := fun u' hu' =>
    ⟨hU'eq ▸ ⟨(hcball hu'.1).1, hu'.2⟩, (hcball hu'.1).2⟩
  -- the solution set on the `E'`-side and the local theorem
  set S : Set ((ScBanach.paramProd Pn W) 0) :=
    {u' | u' ∈ G''.U 0 ∧ h u' + (ScBanach.paramProd Q W).toBase 1 (t u') = 0} ∩
      Metric.ball 0 r₀ with hSdef
  obtain ⟨O', hO'open, h0O', hO'nest, hK⟩ := theorem_3_12_local_subset hh'' hCt.isClosed ht ht0
    (S := S) inter_subset_left
  obtain ⟨Og, hOg, hGeq⟩ := G''.relOpen 0
  have hGmem : ∀ u', u' ∈ G''.U 0 ↔ u' ∈ Og ∧ u' ∈ Ct ×ˢ univ := fun u' => by
    rw [hGeq]; rfl
  -- the neighbourhoods `O(i)` in `X`
  set O : ℕ → Set X := fun i =>
    (c.φ.source ∩ c.φ ⁻¹' N₁) ∩
      (c.φ.source ∩ (ψ ∘ c.φ) ⁻¹' (O' i ∩ Og ∩ Metric.ball 0 r₀)) with hOdef
  have hψφ : ContinuousOn (ψ ∘ c.φ) c.φ.source :=
    hψcont.comp c.φ.continuousOn_toFun fun x hx => hOU (c.φ.mapsTo_model x hx)
  refine ⟨O, fun i => ?_, fun i => ?_, fun i x hx => ?_, fun i => ?_⟩
  · exact (c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source hN₁open).inter
      (hψφ.isOpen_inter_preimage c.φ.isOpen_source (((hO'open i).inter hOg).inter
        Metric.isOpen_ball))
  · refine ⟨⟨hxV, by rw [mem_preimage, h0]; exact h0N₁⟩, hxV, ?_⟩
    rw [mem_preimage, Function.comp_apply, h0, hψ0]
    exact ⟨⟨h0O' i, ((hGmem 0).1 (G''.zero_mem 0)).1⟩, Metric.mem_ball_self hr₀pos⟩
  · exact ⟨hx.1, hx.2.1, ⟨⟨hO'nest i hx.2.2.1.1, hx.2.2.1.2⟩, hx.2.2.2⟩⟩
  -- the compactness statement on level `i`
  obtain ⟨K', hK'c, hK'eq⟩ := hK i
  set Z : Set X := {x ∈ O i | IsZeroAt P f x} with hZdef
  set A : Set ((ScBanach.paramProd Pn W) 0) := S ∩ O' i with hAdef
  -- (F1) the closure of `A` lies in `U' ∩ W'`
  have hAsub : A ⊆ Metric.closedBall 0 r₀ ∩ Ct ×ˢ univ := fun u' hu' =>
    ⟨Metric.ball_subset_closedBall hu'.1.2, hU'C (hG''U' hu'.1.1.1)⟩
  have hclA : closure A ⊆ Metric.closedBall 0 r₀ ∩ Ct ×ˢ univ :=
    closure_minimal hAsub (Metric.isClosed_closedBall.inter hC'closed)
  have hclA' : ∀ u' ∈ closure A, u' ∈ U' ∧ ψ' u' ∈ c.U ∧ ψ' u' ∈ N₁ := fun u' hu' => by
    obtain ⟨h1, h2⟩ := hcl_mem u' (hclA hu')
    exact ⟨h1, hΨ.invFun.base_mem h1, hW'sub h2 h1⟩
  -- the zeros of `g` among the images `ψ'(A)`
  have hAzero : ∀ u' ∈ A, g (ψ' u') = 0 := fun u' hu' => by
    have hu'U' : u' ∈ U' := hG''U' hu'.1.1.1
    obtain ⟨-, h2, h3⟩ := hclA' u' (subset_closure hu')
    refine (hkey (ψ' u') h2 h3).1 ?_
    rw [hψ'ψ u' hu'U']
    exact hu'.1.1.2
  -- (Claim 1) `φ(Z) = ψ'(A)`
  have hφZ : c.φ '' Z = ψ' '' A := by
    ext u
    constructor
    · rintro ⟨x, ⟨⟨⟨hxV', hxN⟩, -, hxψ⟩, hxz⟩, rfl⟩
      have huO : c.φ x ∈ c.φ.model.O := c.φ.mapsTo_model x hxV'
      have hfbu : fb (c.φ x) = 0 := (c.isZeroAt_iff hf hxV').1 hxz
      have hgu : g (c.φ x) = 0 := by rw [← (hN₁ _ hxN).1 huO, hfbu]
      have hψU' : ψ (c.φ x) ∈ U' := hΨ.toFun.base_mem (hOU huO)
      refine ⟨ψ (c.φ x), ⟨⟨⟨(hGmem _).2 ⟨hxψ.1.2, hU'C hψU'⟩, ?_⟩, hxψ.2⟩, hxψ.1.1⟩,
        hψψ' _ (hOU huO)⟩
      exact (hkey _ (hOU huO) hxN).2 hgu
    · rintro ⟨u', hu', rfl⟩
      have hu'U' : u' ∈ U' := hG''U' hu'.1.1.1
      obtain ⟨-, h2, h3⟩ := hclA' u' (subset_closure hu')
      have hgu : g (ψ' u') = 0 := hAzero u' hu'
      have huO : ψ' u' ∈ c.φ.model.O := hgO _ h2 h3 hgu
      refine ⟨c.φ.symm (ψ' u'), ⟨⟨⟨c.φ.symm_mapsTo huO, ?_⟩, c.φ.symm_mapsTo huO, ?_⟩, ?_⟩,
        c.φ.apply_symm_apply huO⟩
      · rw [mem_preimage, c.φ.apply_symm_apply huO]; exact h3
      · rw [mem_preimage, Function.comp_apply, c.φ.apply_symm_apply huO, hψ'ψ u' hu'U']
        exact ⟨⟨hu'.2, ((hGmem _).1 hu'.1.1.1).1⟩, hu'.1.2⟩
      · rw [c.isZeroAt_iff hf (c.φ.symm_mapsTo huO), c.φ.apply_symm_apply huO]
        change fb (ψ' u') = 0
        rw [(hN₁ _ h3).1 huO, hgu]
  -- (Claim 2) `closure(φ(Z)) = ψ'(closure A) =: T`, compact and inside `O`
  set T := ψ' '' closure A with hTdef
  have hTc : IsCompact T := by
    have h1 : IsCompact (closure A) := by
      rw [hK'eq]
      exact hK'c.image ((ScBanach.paramProd Pn W).toBase i).continuous
    exact h1.image_of_continuousOn (hψ'cont.mono fun u' hu' => (hclA' u' hu').1)
  have hclφZ : closure (c.φ '' Z) = T := by
    rw [hφZ]
    refine le_antisymm (closure_minimal (image_mono subset_closure) hTc.isClosed) ?_
    exact ContinuousOn.image_closure (hψ'cont.mono fun u' hu' => (hclA' u' hu').1)
  have hTO : ∀ u ∈ T, u ∈ c.φ.model.O ∧ u ∈ c.U ∧ u ∈ N₁ := by
    rintro _ ⟨u', hu', rfl⟩
    obtain ⟨-, h2, h3⟩ := hclA' u' hu'
    have hgu : g (ψ' u') = 0 := by
      refine eq_of_mem_closure_of_continuousOn hgcont (A := ψ' '' A) ?_ ?_ (hmemGg _ h2 h3) ?_
      · rintro _ ⟨v', hv', rfl⟩
        obtain ⟨-, hv2, hv3⟩ := hclA' v' (subset_closure hv')
        exact hmemGg _ hv2 hv3
      · rintro _ ⟨v', hv', rfl⟩; exact hAzero v' hv'
      · exact ContinuousOn.image_closure (hψ'cont.mono fun v' hv' => (hclA' v' hv').1)
          ⟨u', hu', rfl⟩
    exact ⟨hgO _ h2 h3 hgu, h2, h3⟩
  -- (Claim 3) `closure Z = φ⁻¹(T)`
  have hZV : Z ⊆ c.φ.source := fun x hx => hx.1.1.1
  have hclZ : closure Z = c.φ.symm '' T := by
    have hsymmT : ContinuousOn c.φ.symm T := c.φ.continuousOn_invFun.mono fun u hu => (hTO u hu).1
    refine le_antisymm (closure_minimal ?_ (hTc.image_of_continuousOn hsymmT).isClosed) ?_
    · intro x hx
      refine ⟨c.φ x, ?_, c.φ.symm_apply_apply (hZV hx)⟩
      rw [← hclφZ]; exact subset_closure ⟨x, hx, rfl⟩
    · have := ContinuousOn.image_closure (s := c.φ '' Z) (f := c.φ.symm) (by rwa [hclφZ])
      rw [hclφZ, c.φ.toPartialEquiv.symm_image_image_of_subset_source hZV] at this
      exact this
  -- (Claim 4) the compact set in `X_i`
  have hx₀i : x₀ ∈ PX.levelSet i := mem_iInter.1 hxs i
  set x₀' : PX.Level i := PX.levelMk i x₀ hx₀i with hx₀'def
  set Θ : (ScBanach.paramProd Pn W) i → PX.Level i :=
    fun z => PX.levelChartSymm c.isChart i x₀' (levelMap ψ' i z) with hΘdef
  have hK'U' : K' ⊆ (ScBanach.paramProd Pn W).lvlSet U' i := fun z hz =>
    (hclA' _ (hK'eq ▸ ⟨z, hz, rfl⟩)).1
  have hK'T : ∀ z ∈ K', ψ' ((ScBanach.paramProd Pn W).toBase i z) ∈ T := fun z hz =>
    ⟨_, hK'eq ▸ ⟨z, hz, rfl⟩, rfl⟩
  have hlev : ∀ z ∈ K', c.φ.model.E.toBase i (levelMap ψ' i z) =
      ψ' ((ScBanach.paramProd Pn W).toBase i z) := fun z hz =>
    hψ'sc0.toBase_levelMap (hK'U' hz)
  have hlevO : ∀ z ∈ K', levelMap ψ' i z ∈ c.φ.model.E.lvlSet c.φ.model.O i := fun z hz => by
    rw [ScBanach.mem_lvlSet, hlev z hz]
    exact (hTO _ (hK'T z hz)).1
  refine ⟨Θ '' K', hK'c.image_of_continuousOn ?_, ?_⟩
  · exact (PX.continuousOn_levelChartSymm c.isChart i x₀').comp
      ((hψ'sc0.continuousOn i).mono hK'U') hlevO
  · rw [hclZ, image_image, hTdef, hK'eq, image_image, image_image]
    refine image_congr fun z hz => ?_
    simp only [hΘdef]
    rw [PX.levelVal_levelChartSymm c.isChart i x₀' (hlevO z hz), hlev z hz]

/-- **Corollary 3.13** (at the base point of the germ), **germ reading** (phase 2; the germ version
of `corollary_3_13_wholeChart`, hypothesis `B.IsScFredholmGerm f x₀`): let `(f, x₀)` be an sc-Fredholm germ
with `f(x₀) = 0`.  If `f(x_k) = 0` and `x_k → x₀` in `X`, then for every `m` there are lifts
`y_k ∈ X_m` of the `x_k` (for `k` large) converging in `X_m` to the lift of `x₀`. -/
theorem corollary_3_13 (hf : IsSection P f) {x₀ : X} (hg : B.IsScFredholmGerm f x₀)
    (hx₀ : IsZeroAt P f x₀) {x : ℕ → X} (hx : ∀ n, IsZeroAt P f (x n))
    (hlim : Tendsto x atTop (𝓝 x₀)) (m : ℕ) :
    ∃ y₀ : PX.Level m, PX.levelVal m y₀ = x₀ ∧ ∃ y : ℕ → PX.Level m,
      (∀ᶠ n in atTop, PX.levelVal m (y n) = x n) ∧ Tendsto y atTop (𝓝 y₀) := by
  classical
  obtain ⟨O, hO, h0, -, hK⟩ := theorem_3_12 hf hg hx₀
  obtain ⟨K, hKc, hKeq⟩ := hK m
  set y₀ : PX.Level m := PX.levelMk m x₀ (mem_iInter.1 hg.1 m) with hy₀
  have hev : ∀ᶠ n in atTop, x n ∈ O m := hlim.eventually ((hO m).mem_nhds (h0 m))
  have hmem : ∀ n, x n ∈ O m → x n ∈ PX.levelVal m '' K := fun n hn => by
    rw [hKeq]; exact subset_closure ⟨hn, hx n⟩
  refine ⟨y₀, rfl, fun n => if hn : x n ∈ O m then (hmem n hn).choose else y₀, ?_, ?_⟩
  · filter_upwards [hev] with n hn
    rw [dif_pos hn]; exact (hmem n hn).choose_spec.2
  · refine tendsto_of_isCompact_of_tendsto_map hKc (PX.continuous_levelVal m)
      (MPolyfold.levelVal_injective m) ?_ ?_
    · filter_upwards [hev] with n hn
      rw [dif_pos hn]; exact (hmem n hn).choose_spec.1
    · refine hlim.congr' ?_
      filter_upwards [hev] with n hn
      rw [dif_pos hn]; exact ((hmem n hn).choose_spec.2).symm

end Bundle

end Polyfold
