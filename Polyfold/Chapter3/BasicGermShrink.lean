import Polyfold.Chapter3.FredholmGermIndex

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
Definitions 3.1.7 (preprint 3.7) (basic germs) and 3.11 (sc-Fredholm germs), **in the text's germ reading**: the
basic germ to which `g − s` is conjugated may be restricted to a smaller germ of neighbourhoods, in
particular to the germ of the points that the inverse base map `ψ'` sends into the germs on which
the filling `g` and the sc⁺-section `s` are sc-smooth.

# Basic germs on smaller germs, and the conjugation shrunk to the germs of `g` and `s`

## The text, paraphrased

(Definition 3.1.7 (preprint 3.7)) A basic germ is an sc-smooth germ `h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W` with `h(0) = 0`
whose `W`-part is `w − B(a, w)`, `B` an sc⁰-contraction germ (Definition 3.3.1 (preprint 3.28)).  (Definition 3.1.11 (preprint 3.11))
`(f, x₀)` is an sc-Fredholm germ if, in a chart centred at `x₀`, the principal part has a filling
`(g, 0)` (an sc-smooth section germ of `U ◁ F → U`), there is a local sc⁺-section `s` near `0` with
`s(0) = g(0)`, and `g − s` is conjugated by a strong bundle isomorphism `Ψ : U ◁ F → U' ◁ (ℝᴺ ⊕ W)`
to a basic germ.  All of these are **germs**: `g` and `s` are sc-smooth on germs of neighbourhoods
`G_g`, `G_s` of `0` (Definition 3.1.1 (preprint 3.1)) whose levels may shrink with the level.

## What is formalized

* `Polyfold.ScNbhdGerm.exists_ball_paramProd`: every level `U_m` of a germ of neighbourhoods of
  `0 ∈ C̃ ⊕ W` contains `{(a, w) | a ∈ C̃, |a| < r, |w|_m < r}` for some `r > 0`.
* `Polyfold.IsSc0ContractionGerm.mono`, `Polyfold.IsBasicGerm.mono`, `IsBasicGerm.inter`:
  **a basic germ restricts to every smaller germ** (`G'_m ⊆ G_m` for all `m`), with the same `h`
  and `B`.
* `Polyfold.ConjugationData.shrinkGerm` (**the germ `G″`**): for conjugation data `d` of `k` and a
  germ `G'` on the `E`-side, the germ `G″_m = {x ∈ G_m | ψ'_m(x) ∈ G'_m}` of the points of the
  basic germ's `G` that `ψ' = base Ψ'` maps into `G'`, level by level (`ScNbhdGerm.preimage` along
  the sc⁰-germ `ψ'`, `ConjugationData.baseInv_isSc0Germ`); `ConjugationData.shrink`: the
  conjugation data with the **same** `Ψ`, `h`, `B` and the basic germ on `G″`
  (`ConjugationData.basic_shrinkGerm`).
* `Polyfold.ConjugationData.levelMap_mem_of_mem_shrinkGerm` and its forms for `G' = G_g ∩ G_s`
  (`levelMap_mem_inter_of_mem_shrinkGerm`), for every germ inside `G″`
  (`levelMap_mem_of_subset_shrinkGerm`) and along the inclusions
  (`levelMap_inclK_mem_of_subset_shrinkGerm`): `x ∈ G″_m ⇒ ψ'_m(x) ∈ G'_m`; read on the `E`-side,
  `ConjugationData.mem_of_levelMap_base_mem`: `u ∈ U_m` with `ψ_m(u) ∈ G″_m` lies in `G'_m`.  This
  is what makes the nearby points `x₁ ∈ G″₁` produced by the implicit function theorem
  (Corollary 3.5.3 (preprint 3.41)) points where `g` is sc¹: `ψ'₁(x₁) ∈ (G_g)₁` (`BasicGermShrinkIFT.lean`).
* `Polyfold.IsConjugateToBasicGerm.exists_conjugationData_mapsToGerm`: the conjugation of
  Definition 3.1.11 (preprint 3.11) can always be chosen with `ψ'` mapping the basic germ's germ into `G_g ∩ G_s`.
* `Polyfold.ConjugationData.congr`: conjugation data of `k` are conjugation data of every `k'`
  equal to `k` on `U` near `0`, with the same germ `G″` (`shrinkGerm_congr`); this is the
  conjugation part of Theorem 3.1.18 (preprint 3.15) (`IsScFredholmGermWholeChart.sectionAdd`) in the germ reading.  The
  filling and sc⁺-section parts of Theorem 3.1.18 (preprint 3.15) on germs (`g + ŝ ∘ r` a filling germ on `G_g`,
  `ŝ₁ ∘ r + t₀` an sc⁺-germ on `G_s`) need the addition of germs and the germ form of Lemma 3.1.20 (preprint 3.17),
  which are not proved here.

## What the text leaves implicit, and the choices made (the findings)

* **Restricting a basic germ is harmless, but one field needs a reason.**  The sc⁰-contraction
  estimate of Definition 3.3.1 (preprint 3.28) asks that the points `(a, w)`, `a ∈ C̃`, `|a|, |w|_m < r`, lie in
  `U_m`; for a smaller germ this holds after shrinking `r`, because every level of a germ is a
  relatively open neighbourhood of `0` in `C̃ ⊕ W_m` (`exists_ball_paramProd`): no extra
  condition.  The sc-smoothness of `h` on the smaller germ uses the uniqueness of the derivatives
  (`IsScSmoothGerm.mono`), i.e. that `C̃` is quadrant-like; the basic germs of Definition 3.1.11 (preprint 3.11) have
  `C̃` a partial quadrant (`ConjugationData.quadrant`), so this is no restriction there.
* **`G ∩ preimage = preimage`.**  The germ "`G″ = G ∩ ψ'^{-1}(G_g ∩ G_s)`" is the preimage germ
  `G.preimage (G_g ∩ G_s)` itself, which is already contained in `G`
  (`ScNbhdGerm.inter_preimage_U`).
* **The text does not say on which germ the conjugated basic germ lives relative to `G_g`, `G_s`.**
  Its proofs (Corollary 3.5.3 (preprint 3.41), Theorem 3.6.8 (preprint 3.54)) differentiate `g` at `ψ'(x₁)` for the nearby solutions
  `x₁ ∈ G₁` of the basic germ.  With `g` an sc-smooth germ on `G_g` only, `ψ'(x₁)` must lie in
  `(G_g)₁`; for the basic germ on an arbitrary `G` it need not (nothing in Definition 3.1.11 (preprint 3.11) relates
  `G` to `G_g`, whose levels may shrink faster).  Shrinking `G` to `G″` costs
  nothing (`shrink` keeps `Ψ`, `h`, `B` and the conjugation identity) and makes every such point
  admissible.  The restriction `ψ'|_G` is an sc⁰-germ because `ψ'` is sc-smooth on the whole `U'`
  (a strong bundle isomorphism is a map of the whole local bundles), which is what
  `ScNbhdGerm.preimage` needs.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

/-! ### Germs of neighbourhoods of `0 ∈ C̃ ⊕ W` contain balls -/

section Ball

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}

/-- Every level `U_m` of an sc-germ of neighbourhoods of `0 ∈ C̃ ⊕ W` contains the points
`(a, w)` with `a ∈ C̃`, `|a| < r`, `|w|_m < r` for some `r > 0` (`U_m` is relatively open in
`C̃ ⊕ W_m` and contains `0`). -/
lemma ScNbhdGerm.exists_ball_paramProd (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ))
    (m : ℕ) : ∃ r > 0, ∀ a ∈ Ct, ‖a‖ < r → ∀ w : W m, ‖w‖ < r →
      ((a, w) : P × W m) ∈ G.U m := by
  obtain ⟨O, hO, hG⟩ := G.relOpen m
  have h0 : (0 : (ScBanach.paramProd P W) m) ∈ O := by
    have := G.zero_mem m
    rw [hG] at this
    exact this.1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO 0 h0
  refine ⟨r, hr, fun a ha har w hw => ?_⟩
  rw [hG]
  refine ⟨hball ?_, ?_⟩
  · rw [mem_ball_zero_iff]
    change ‖((a, w) : P × W m)‖ < r
    rw [Prod.norm_mk]
    exact max_lt har hw
  · rw [ScBanach.paramProd_lvlSet]
    exact ⟨ha, mem_univ _⟩

end Ball

/-! ### Basic germs on smaller germs -/

section Mono

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P} {G G' : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)}
  {B : P × W 0 → W 0}

/-- **An sc⁰-contraction germ (Definition 3.3.1 (preprint 3.28)) restricts to every smaller germ** `G'`
(`G'_m ⊆ G_m` for all `m`), with the same `B`: the contraction radius is shrunk so that the
`C̃ ⊕ W_m`-ball lies in `G'_m` (`ScNbhdGerm.exists_ball_paramProd`). -/
theorem IsSc0ContractionGerm.mono (h : IsSc0ContractionGerm Ct G B)
    (hsub : ∀ m, G'.U m ⊆ G.U m) : IsSc0ContractionGerm Ct G' B where
  isSc0 := h.isSc0.mono hsub
  B_zero := h.B_zero
  contraction ε hε m := by
    obtain ⟨r, hr, hr'⟩ := h.contraction ε hε m
    obtain ⟨r₁, hr₁, hball⟩ := G'.exists_ball_paramProd m
    refine ⟨min r r₁, lt_min hr hr₁, fun a ha har w w' hw hw' => ⟨?_, ?_⟩⟩
    · exact hball a ha (har.trans_le (min_le_right _ _)) w (hw.trans_le (min_le_right _ _))
    · exact (hr' a ha (har.trans_le (min_le_left _ _)) w w' (hw.trans_le (min_le_left _ _))
        (hw'.trans_le (min_le_left _ _))).2

/-- An sc⁰-contraction germ restricts to the intersection with any germ. -/
theorem IsSc0ContractionGerm.inter (h : IsSc0ContractionGerm Ct G B)
    (G' : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)) :
    IsSc0ContractionGerm Ct (G.inter G') B :=
  h.mono fun _ _ hx => hx.1

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  {f : P × W 0 → Q × W 0}

/-- **A basic germ (Definition 3.1.7 (preprint 3.7)) restricts to every smaller germ** `G'` (`G'_m ⊆ G_m` for all
`m`), with the same `h` and `B`.  The contraction field restricts to every smaller germ
(`IsSc0ContractionGerm.mono`); the sc-smoothness of `f` restricts because `C̃` is quadrant-like
(uniqueness of the derivatives, `IsScSmoothGerm.mono`), which holds for the partial quadrants
`C̃` of Definition 3.1.11 (preprint 3.11). -/
theorem IsBasicGerm.mono (hC : IsQuadrantLike (ScBanach.const P) Ct) (h : IsBasicGerm Ct G f B)
    (hsub : ∀ m, G'.U m ⊆ G.U m) : IsBasicGerm Ct G' f B where
  isScSmooth := IsScSmoothGerm.mono (E := ScBanach.paramProd P W) (F := ScBanach.paramProd Q W)
    (hC.paramProd W) hsub h.isScSmooth
  f_zero := h.f_zero
  snd_eq x hx := h.snd_eq x (hsub 0 hx)
  contraction := h.contraction.mono hsub

/-- A basic germ restricts to the intersection with any germ. -/
theorem IsBasicGerm.inter (hC : IsQuadrantLike (ScBanach.const P) Ct) (h : IsBasicGerm Ct G f B)
    (G' : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)) : IsBasicGerm Ct (G.inter G') f B :=
  h.mono hC fun _ _ hx => hx.1

end Mono

/-! ### `G ∩ preimage = preimage` -/

section InterPreimage

variable {E E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}

/-- The intersection of a germ `G₀` with a preimage germ `G₀.preimage G'` has the levels of the
preimage germ (which is already contained in `G₀`). -/
lemma ScNbhdGerm.inter_preimage_U (G₀ : ScNbhdGerm E C) (G' : ScNbhdGerm E' C')
    {f : E 0 → E' 0} (hf : IsSc0Germ G₀ f) (hf0 : f 0 = 0) (hfC : MapsTo f (G₀.U 0) C') (m : ℕ) :
    (G₀.inter (G₀.preimage G' hf hf0 hfC)).U m = (G₀.preimage G' hf hf0 hfC).U m := by
  ext x
  exact ⟨fun hx => hx.2, fun hx => ⟨hx.1, hx⟩⟩

end InterPreimage

/-! ### The conjugation with the basic germ shrunk to `G″` -/

section Shrink

variable {E F : ScBanach} {C U : Set (E 0)} {k k' : E 0 → F 0}

namespace ConjugationData

variable (d : ConjugationData U k)

/-- `0 ∈ U'` (it lies in the germ `G₀ ⊆ U'`). -/
lemma zero_mem_U' : (0 : (ScBanach.paramProd d.Pn d.W) 0) ∈ d.U' :=
  d.germ_subset (d.G.zero_mem 0)

/-- `ψ'(0) = 0` for the inverse base map `ψ' = base Ψ'`. -/
lemma baseInv_zero (h0 : (0 : E 0) ∈ U) : IsStrongBundleMap.base d.Ψ' 0 = 0 :=
  d.iso.base_zero' h0 d.base_zero

/-- The inverse base map `ψ' = base Ψ'` is sc-smooth on the whole `U'`, hence an sc⁰-germ on the
basic germ's `G` (`G₀ ⊆ U'`). -/
lemma baseInv_isSc0Germ : IsSc0Germ (F := E) d.G (IsStrongBundleMap.base d.Ψ') :=
  ((d.iso.invFun.base_isScSmooth d.relOpen).isSc1.isSc0.isSc0Germ d.relOpen.relOpen
    d.zero_mem_U').mono fun _ _ hz => d.germ_subset (d.G.toBase_mem hz)

/-- `ψ'` maps `G₀ ⊆ U'` into `U ⊆ C`. -/
lemma baseInv_mapsTo (hU : IsRelOpenInQuadrant E C U) :
    MapsTo (IsStrongBundleMap.base d.Ψ') (d.G.U 0) C := fun _ hx => by
  have hUC : U ⊆ C := by
    obtain ⟨O, -, hUO⟩ := hU.relOpen
    rw [hUO]
    exact inter_subset_right
  exact hUC (d.iso.invFun.base_mem (d.germ_subset hx))

/-- **The germ `G″`**: for a germ `G'` of neighbourhoods of `0` in `C` (on the `E`-side, e.g.
`G' = G_g ∩ G_s` for the germs of the filling and of the sc⁺-section), the germ
`G″_m = {x ∈ G_m | ψ'_m(x) ∈ G'_m}` of the points of the basic germ's germ `G` that `ψ' = base Ψ'`
maps into `G'`, level by level. -/
def shrinkGerm (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U) (G' : ScNbhdGerm E C) :
    ScNbhdGerm (ScBanach.paramProd d.Pn d.W) (d.Ct ×ˢ univ) :=
  d.G.preimage G' d.baseInv_isSc0Germ (d.baseInv_zero h0) (d.baseInv_mapsTo hU)

variable (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U) (G' : ScNbhdGerm E C)

/-- Membership in `G″_m`: `x ∈ G_m` and `ψ'_m(x) ∈ G'_m`. -/
lemma mem_shrinkGerm_U {m : ℕ} {x : (ScBanach.paramProd d.Pn d.W) m} :
    x ∈ (d.shrinkGerm hU h0 G').U m ↔
      x ∈ d.G.U m ∧ levelMap (IsStrongBundleMap.base d.Ψ') m x ∈ G'.U m := Iff.rfl

/-- `G″_m ⊆ G_m`. -/
lemma shrinkGerm_subset (m : ℕ) : (d.shrinkGerm hU h0 G').U m ⊆ d.G.U m := fun _ hx => hx.1

/-- `G″₀ ⊆ U'`. -/
lemma shrinkGerm_subset_U' : (d.shrinkGerm hU h0 G').U 0 ⊆ d.U' := fun _ hx =>
  d.germ_subset hx.1

/-- `ψ'` maps `G″` into `G'` level by level. -/
lemma shrinkGerm_mapsToGerm :
    (d.shrinkGerm hU h0 G').MapsToGerm G' (IsStrongBundleMap.base d.Ψ') := fun _ _ hx => hx.2

/-- **`x ∈ G″_m ⇒ ψ'_m(x) ∈ G'_m`.** -/
theorem levelMap_mem_of_mem_shrinkGerm {m : ℕ} {x : (ScBanach.paramProd d.Pn d.W) m}
    (hx : x ∈ (d.shrinkGerm hU h0 G').U m) :
    levelMap (IsStrongBundleMap.base d.Ψ') m x ∈ G'.U m := hx.2

/-- **The G″ property for the filling and the sc⁺-section**: `x ∈ G″_m ⇒
ψ'_m(x) ∈ (G_g)_m ∩ (G_s)_m` for `G″` built from `G' = G_g ∩ G_s`. -/
theorem levelMap_mem_inter_of_mem_shrinkGerm {Gg Gs : ScNbhdGerm E C} {m : ℕ}
    {x : (ScBanach.paramProd d.Pn d.W) m} (hx : x ∈ (d.shrinkGerm hU h0 (Gg.inter Gs)).U m) :
    levelMap (IsStrongBundleMap.base d.Ψ') m x ∈ Gg.U m ∩ Gs.U m := hx.2

/-- The G″ property for every germ `𝒢` inside `G″` (e.g. the germ of the data of Theorem 3.4.2 (preprint 3.38)
built on `G″`). -/
theorem levelMap_mem_of_subset_shrinkGerm
    {𝒢 : ScNbhdGerm (ScBanach.paramProd d.Pn d.W) (d.Ct ×ˢ univ)}
    (h𝒢 : ∀ m, 𝒢.U m ⊆ (d.shrinkGerm hU h0 G').U m) {m : ℕ}
    {x : (ScBanach.paramProd d.Pn d.W) m} (hx : x ∈ 𝒢.U m) :
    levelMap (IsStrongBundleMap.base d.Ψ') m x ∈ G'.U m := (h𝒢 m hx).2

/-- The G″ property along the inclusions: for `x ∈ 𝒢_{m+j}` with `𝒢 ⊆ G″`,
`ψ'_m(ι x) ∈ G'_m` (the form used for curves on level `2` read on level `1`). -/
theorem levelMap_inclK_mem_of_subset_shrinkGerm
    {𝒢 : ScNbhdGerm (ScBanach.paramProd d.Pn d.W) (d.Ct ×ˢ univ)}
    (h𝒢 : ∀ m, 𝒢.U m ⊆ (d.shrinkGerm hU h0 G').U m) {m j : ℕ}
    {x : (ScBanach.paramProd d.Pn d.W) (m + j)} (hx : x ∈ 𝒢.U (m + j)) :
    levelMap (IsStrongBundleMap.base d.Ψ') m ((ScBanach.paramProd d.Pn d.W).inclK m j x) ∈
      G'.U m :=
  (h𝒢 m (𝒢.inclK_mem hx)).2

/-- **The G″ property read on the `E`-side**: a point `u ∈ U_m` whose image `ψ_m(u)` lies in a
germ `𝒢 ⊆ G″` lies in `G'_m` (`u = ψ'_m(ψ_m(u))`).  This is the form of the nearby points
`z₀₁ ∈ U₁` with `ψ₁(z₀₁) = x₁ ∈ 𝒢₁` of Theorem 3.6.8 (preprint 3.54) (1) (`theorem_3_6_8_chart_kernel_wholeChart`). -/
theorem mem_of_levelMap_base_mem
    {𝒢 : ScNbhdGerm (ScBanach.paramProd d.Pn d.W) (d.Ct ×ˢ univ)}
    (h𝒢 : ∀ m, 𝒢.U m ⊆ (d.shrinkGerm hU h0 G').U m) {m : ℕ} {u : E m}
    (hu : u ∈ E.lvlSet U m) (hψu : levelMap (IsStrongBundleMap.base d.Ψ) m u ∈ 𝒢.U m) :
    u ∈ G'.U m := by
  have hψ := (d.iso.toFun.base_isScSmooth hU).isSc1.isSc0
  have h1 : levelMap (IsStrongBundleMap.base d.Ψ') m
      (levelMap (IsStrongBundleMap.base d.Ψ) m u) = u := by
    apply levelMap_eq_of_toBase_eq
    rw [hψ.toBase_levelMap hu, d.iso.base_base hu]
  rw [← h1]
  exact (h𝒢 m hψu).2

/-- `ι(ψ'_m(x)) = ψ'(ι x)` on `G″` (the level-`m` point over `ψ'(ι x)`). -/
lemma toBase_levelMap_of_mem_shrinkGerm {m : ℕ} {x : (ScBanach.paramProd d.Pn d.W) m}
    (hx : x ∈ (d.shrinkGerm hU h0 G').U m) :
    E.toBase m (levelMap (IsStrongBundleMap.base d.Ψ') m x) =
      IsStrongBundleMap.base d.Ψ' ((ScBanach.paramProd d.Pn d.W).toBase m x) :=
  d.baseInv_isSc0Germ.toBase_levelMap hx.1

/-- `G″` is monotone in `G'`. -/
lemma shrinkGerm_mono {G'' : ScNbhdGerm E C} (hG : ∀ m, G'.U m ⊆ G''.U m) (m : ℕ) :
    (d.shrinkGerm hU h0 G').U m ⊆ (d.shrinkGerm hU h0 G'').U m := fun _ hx =>
  ⟨hx.1, hG m hx.2⟩

/-- **The basic germ on `G″`**: `h` is a basic germ (Definition 3.1.7 (preprint 3.7)) on `G″`, with the same
contraction map `B` (`IsBasicGerm.mono`; `C̃` is a partial quadrant). -/
theorem basic_shrinkGerm : IsBasicGerm d.Ct (d.shrinkGerm hU h0 G') d.h d.Bc :=
  d.basic.mono d.quadrant.isQuadrantLike (d.shrinkGerm_subset hU h0 G')

/-- **The conjugation with the basic germ shrunk to `G″`**: the conjugation data `d` with the same
strong bundle isomorphism `Ψ`, the same basic germ `h` and contraction map `B`, and the germ `G″`
of the points of `G` that `ψ'` maps into `G'` (`shrinkGerm`). -/
def shrink : ConjugationData U k :=
  { d with
    G := d.shrinkGerm hU h0 G'
    germ_subset := d.shrinkGerm_subset_U' hU h0 G'
    basic := d.basic_shrinkGerm hU h0 G' }

/-- The germ of the shrunk data is `G″`. -/
@[simp] lemma shrink_G : (d.shrink hU h0 G').G = d.shrinkGerm hU h0 G' := rfl

/-- The shrunk data keep the strong bundle isomorphism `Ψ`. -/
@[simp] lemma shrink_Ψ : (d.shrink hU h0 G').Ψ = d.Ψ := rfl

/-- The shrunk data keep the inverse `Ψ'`. -/
@[simp] lemma shrink_Ψ' : (d.shrink hU h0 G').Ψ' = d.Ψ' := rfl

/-- The shrunk data keep the basic germ `h`. -/
@[simp] lemma shrink_h : (d.shrink hU h0 G').h = d.h := rfl

/-- The shrunk data keep the contraction map `B`. -/
@[simp] lemma shrink_Bc : (d.shrink hU h0 G').Bc = d.Bc := rfl

/-- The shrunk data keep the domain `U'`. -/
@[simp] lemma shrink_U' : (d.shrink hU h0 G').U' = d.U' := rfl

/-- **The G″ property of the shrunk conjugation data**: `x ∈ (d.shrink G').G_m ⇒
ψ'_m(x) ∈ G'_m`, with `ψ'` the inverse base map of the (unchanged) isomorphism. -/
theorem levelMap_mem_of_mem_shrink {m : ℕ} {x : (ScBanach.paramProd d.Pn d.W) m}
    (hx : x ∈ (d.shrink hU h0 G').G.U m) :
    levelMap (IsStrongBundleMap.base (d.shrink hU h0 G').Ψ') m x ∈ G'.U m := hx.2

/-- The G″ property of the shrunk conjugation data for `G' = G_g ∩ G_s`. -/
theorem levelMap_mem_inter_of_mem_shrink {Gg Gs : ScNbhdGerm E C} {m : ℕ}
    {x : (ScBanach.paramProd d.Pn d.W) m} (hx : x ∈ (d.shrink hU h0 (Gg.inter Gs)).G.U m) :
    levelMap (IsStrongBundleMap.base (d.shrink hU h0 (Gg.inter Gs)).Ψ') m x ∈
      Gg.U m ∩ Gs.U m := hx.2

/-- `(d.shrink G').G_m ⊆ d.G_m`. -/
lemma shrink_G_subset (m : ℕ) : (d.shrink hU h0 G').G.U m ⊆ d.G.U m :=
  d.shrinkGerm_subset hU h0 G' m

/-- **Conjugation data transfer to every `k'` equal to `k` on `U` near `0`** (same `Ψ`, `h`, `B`,
`G`).  This is the conjugation part of Theorem 3.1.18 (preprint 3.15) (`IsScFredholmGermWholeChart.sectionAdd`:
`(g + t̃) − (t̃ + t₀) = g − t₀`) in the germ reading. -/
def congr (hkk' : ∀ᶠ u in 𝓝 (0 : E 0), u ∈ U → k u = k' u) : ConjugationData U k' :=
  { d with
    conj := by
      filter_upwards [d.conj, hkk'] with u hu hu' huU
      rw [← hu' huU]; exact hu huU }

/-- The germ `G″` does not change under `congr`. -/
lemma shrinkGerm_congr (hkk' : ∀ᶠ u in 𝓝 (0 : E 0), u ∈ U → k u = k' u) :
    (d.congr hkk').shrinkGerm hU h0 G' = d.shrinkGerm hU h0 G' := rfl

end ConjugationData

/-- **Definition 3.1.11 (preprint 3.11) with the basic germ shrunk to the germs of `g` and `s`**: if `k` is
conjugated to a basic germ, then for any germs `G_g`, `G_s` of neighbourhoods of `0` in `C`
there are conjugation data of `k` whose inverse base map `ψ' = base Ψ'` maps the basic germ's germ
into `G_g` and into `G_s`, level by level. -/
theorem IsConjugateToBasicGerm.exists_conjugationData_mapsToGerm (hU : IsRelOpenInQuadrant E C U)
    (h0 : (0 : E 0) ∈ U) (hk : IsConjugateToBasicGerm U k) (Gg Gs : ScNbhdGerm E C) :
    ∃ d : ConjugationData U k,
      d.G.MapsToGerm Gg (IsStrongBundleMap.base d.Ψ') ∧
        d.G.MapsToGerm Gs (IsStrongBundleMap.base d.Ψ') := by
  obtain ⟨d⟩ := isConjugateToBasicGerm_iff_nonempty.1 hk
  exact ⟨d.shrink hU h0 (Gg.inter Gs),
    fun _ _ hx => (d.levelMap_mem_inter_of_mem_shrink hU h0 hx).1,
    fun _ _ hx => (d.levelMap_mem_inter_of_mem_shrink hU h0 hx).2⟩

end Shrink

end Polyfold
