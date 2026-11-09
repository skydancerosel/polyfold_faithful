import Polyfold.Chapter3.StrongBundleSections
import Polyfold.Chapter3.GermFillingChart
import Polyfold.Chapter3.GermCalculus
import Polyfold.Chapter3.TameGermsG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
**Theorem 3.1.18 (preprint 3.15)** (stability of sc-Fredholm sections under sc⁺-perturbations) **in the text's germ
reading** of Definition 3.1.11 (preprint 3.11) (phase 2 of the germ-versus-chart work; Findings, Chapter 3, items
300–309).

# Theorem 3.1.18 (preprint 3.15) for sc-Fredholm germs in the germ reading

## The text, paraphrased

(Theorem 3.1.18 (preprint 3.15)) `f ∈ Fred(P)`, `s ∈ Γ⁺(P)` imply `f + s ∈ Fred(P)`.  (Proof) In a chart of the germ
data of `(f, x)`, with filling `g`, sc⁺-section `t₀` and `g − t₀` conjugated to a basic germ, the
germ `g + s̃`, `s̃ = ŝ ∘ r`, is a filling of `f̂ + ŝ` (Lemma 3.1.20 (preprint 3.17)), `s̃ + t₀` is an sc⁺-section with
the right value at `0`, and `(g + s̃) − (s̃ + t₀) = g − t₀` is conjugated to the same basic germ.
The filling and the sc⁺-section of Definition 3.1.11 (preprint 3.11) are germs (Definitions 3.1.1–3.1.2 (preprint 3.1–3.2): sc-germs of
neighbourhoods whose levels may shrink with the level).

## What is formalized

* `Polyfold.IsFillingGerm.congr`: a filling germ depends only on `f̂` on `O` and on `g` on `U`.
* `Polyfold.StrongBundle.sectionAdd_chartData_germ`: **the chart step of Theorem 3.1.18 (preprint 3.15) in the germ
  reading** — germ data `(g, t₀)` of `(f, x)` in a chart `c` (`IsFillingGerm`, `IsScPlusGerm`,
  `t₀(0) = g(0)`, conjugation) give the germ data `(g + ŝ ∘ r, ŝ₁ ∘ r + t₀)` of `(f + s, x)` in the
  same chart; the filling lives on the germ of `g`, the sc⁺-germ on the germ of `t₀`.
* `Polyfold.StrongBundle.IsScFredholmGerm.sectionAdd`: `(f + s, x)` is an sc-Fredholm germ in the
  germ reading (`IsScFredholmGerm`) when `(f, x)` is.
* `Polyfold.StrongBundle.regularizing_sectionAdd` and **`Polyfold.theorem_3_1_18_preprint`**:
  Theorem 3.1.18 (preprint 3.15) for sc-Fredholm sections in the germ reading (`IsScFredholmSection`).
* `Polyfold.StrongBundle.IsScFredholmGermWholeChart.sectionAdd_germG`: the old whole-chart hypothesis feeds
  the germ version.

## What the text leaves implicit, and the choices made

* **Which germ result is needed.**  `ŝ ∘ r` is sc-smooth on the whole `U` (the principal part of
  an sc⁺-section of the bundle, in any compatible chart), so the germ form of Lemma 3.1.20 (preprint 3.17) with a
  whole-chart section (`IsFillingGerm.add_section`, applied to `ŝ ∘ r`, with `r ∘ r = r` on `U`)
  suffices; its germ-`ŝ` form (`add_section_germ`) is not needed.  The sum `ŝ₁ ∘ r + t₀` is an
  sc-smooth germ on the germ `G_{t₀}` of `t₀` (a whole-chart map restricts to every germ in `U`).
* **The conjugation is unchanged** (`IsConjugateToBasicGerm.congr`): `(g + s̃) − (s̃ + t₀) = g − t₀`
  on all of `U`.
* Regularity of `f + s` (Definition 3.1.16 (preprint 3.14) (2)) and its sc-smoothness are statements about sections
  and do not involve germ data; `regularizing_sectionAdd` is the proof of
  `regularizing_sectionAdd_wholeChart` with the germ-reading hypothesis.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

/-! ### Fillings in the germ reading depend only on the values near `0` -/

section Congr

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- **A filling germ depends only on `f̂` on `O = r(U)` and on `g` on `U`** (Definition 3.1.6 (preprint 3.6) with
Definition 3.1.4 (preprint 3.4), germ reading, phase 2): conditions (1), (2) are about points of `O` and `U`, and the
sc-smoothness of `g` and the derivative family of `[1 − ρ(r(·))]g` are about the germ `G` with
`G₀ ⊆ U`. -/
theorem IsFillingGerm.congr (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) {fb fb' g g' : E 0 → F 0} (h : IsFillingGerm hU hR h0 fb g)
    (hfb : ∀ x ∈ StrongRetr.r R '' U, fb x = fb' x) (hg : ∀ y ∈ U, g y = g' y) :
    IsFillingGerm hU hR h0 fb' g' := by
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  have hk : ∀ y ∈ U, fillDefect R g y = fillDefect R g' y := fun y hy => by
    simp only [fillDefect, hg y hy]
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [h.eq_on] with x hx hxO
    rw [← hfb x hxO, ← hg x (StrongRetr.mem_U_of_mem_O hR hxO)]
    exact hx hxO
  · filter_upwards [h.mem_of_fixed] with y hy hyU hfix
    rw [← hg y hyU] at hfix
    exact hy hyU hfix
  · obtain ⟨G, hGU, hgs, Dk, hDk, Φ, hΦ⟩ := h.germ
    exact ⟨G, hGU, fun k => IsSckGerm.congr hQ (fun y hy => hg y (hGU hy)) (hgs k), Dk,
      hDk.congr fun y hy => hk y (hGU hy), Φ, hΦ⟩

end Congr

/-! ### Theorem 3.1.18 (preprint 3.15) in the germ reading -/

section FredholmSectionsGerm

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f s : X → Y}

namespace StrongBundle

/-- **Theorem 3.1.18 (preprint 3.15), the chart step, germ reading** (phase 2): let `c` be a chart of `P` with
`0 ∈ U`, `g` a filling germ of `f̂` (`IsFillingGerm`), `t₀` an sc⁺-germ (`IsScPlusGerm`) with
`t₀(0) = g(0)` and `g − t₀` conjugated to a basic germ, and `s` an sc⁺-section.  Then in the same
chart `g + ŝ ∘ r` is a filling germ of the principal part of `f + s` (Lemma 3.1.20 (preprint 3.17) for germs,
`IsFillingGerm.add_section`), `ŝ₁ ∘ r + t₀` is an sc⁺-germ (on the germ of `t₀`) with the value
`g(0) + ŝ(r(0))` at `0`, and `(g + ŝ ∘ r) − (ŝ₁ ∘ r + t₀) = g − t₀` is conjugated to the same basic
germ. -/
theorem sectionAdd_chartData_germ (hfs : IsSection P f) (hs : B.IsScPlusSection s)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (h0U : (0 : c.φ.model.E 0) ∈ c.U)
    {g : c.φ.model.E 0 → c.F 0} {t₀ : c.φ.model.E 0 → c.F 1}
    (hfill : IsFillingGerm c.relOpen c.isRetraction h0U (c.principal f) g)
    (ht₀ : IsScPlusGerm c.φ.model.C c.U t₀) (ht₀0 : c.F.toBase 1 (t₀ 0) = g 0)
    (hconj : IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (t₀ u))) :
    IsFillingGerm c.relOpen c.isRetraction h0U (c.principal (Polyfold.sectionAdd P f s))
        (fun u => g u + c.principal s (StrongRetr.r c.R u)) ∧
      IsScPlusGerm c.φ.model.C c.U (fun u => c.principalLift s (StrongRetr.r c.R u) + t₀ u) ∧
      c.F.toBase 1 (c.principalLift s (StrongRetr.r c.R 0) + t₀ 0) =
        g 0 + c.principal s (StrongRetr.r c.R 0) ∧
      IsConjugateToBasicGerm c.U (fun u => (g u + c.principal s (StrongRetr.r c.R u)) -
        c.F.toBase 1 (c.principalLift s (StrongRetr.r c.R u) + t₀ u)) := by
  have hU := c.relOpen.isScDomain
  have hQ := c.isQuadrantLike
  -- `ŝ₁ ∘ r` is sc-smooth into `F¹` on `U`, and `ŝ ∘ r = ι ∘ ŝ₁ ∘ r`
  have hlift : IsScSmooth (F := c.F.shift) c.U fun u => c.principalLift s (StrongRetr.r c.R u) :=
    (((hs.isScSmoothRetractMap_one hc).comp_isScSmooth (c.isRetraction.baseRetraction c.relOpen)
      c.base_retract).snd hU).congr hU
      fun _ _ => rfl
  have hsr : IsScSmooth c.U fun u => c.principal s (StrongRetr.r c.R u) :=
    (hlift.toBase_shift hU).congr hU fun u hu => hs.toBase_principalLift hc (c.r_mem_O hu)
  obtain ⟨Gt, hGtU, ht⟩ := ht₀
  refine ⟨?_, ⟨Gt, hGtU,
    (hlift.isScSmoothGerm_of_subset hQ c.relOpen.relOpen h0U hGtU).add hQ ht⟩, ?_, ?_⟩
  · -- Lemma 3.1.20 (preprint 3.17) for germs, with the whole-chart section `ŝ ∘ r`
    have h17 := hfill.add_section c.relOpen c.isRetraction h0U hsr fun z hz => by
      have hz' : z ∈ c.φ.model.O := c.r_image ▸ hz
      change (z, c.principal s (StrongRetr.r c.R z)) ∈ c.K
      rw [StrongRetr.r_eq_self c.isRetraction hz]
      exact hs.mem_K hc hz'
    refine h17.congr c.relOpen c.isRetraction h0U (fun z hz => ?_) (fun u hu => ?_)
    · have hz' : z ∈ c.φ.model.O := c.r_image ▸ hz
      change c.principal f z + c.principal s (StrongRetr.r c.R z) = _
      rw [StrongRetr.r_eq_self c.isRetraction hz]
      exact (c.principal_sectionAdd hfs hs.1 hz').symm
    · rw [StrongRetr.r_r c.isRetraction hu]
  · -- the value at `0`
    simp only [map_add, ht₀0]
    rw [hs.toBase_principalLift hc (c.r_mem_O h0U), add_comm]
  · -- `(g + s̃) − (s̃ + t₀) = g − t₀` on `U`
    refine hconj.congr fun u hu => ?_
    simp only [map_add]
    rw [hs.toBase_principalLift hc (c.r_mem_O hu)]
    abel

/-- **Theorem 3.1.18 (preprint 3.15), the germ property, germ reading** (phase 2; the germ form of
`IsScFredholmGermWholeChart.sectionAdd`): if `(f, x)` is an sc-Fredholm germ in the text's germ reading
(`IsScFredholmGerm`) and `s` is an sc⁺-section, then `(f + s, x)` is one, in the same chart, with
the filling germ `g + ŝ ∘ r`, the sc⁺-germ `ŝ₁ ∘ r + t₀` and the conjugation of `g − t₀`
(`sectionAdd_chartData_germ`). -/
theorem IsScFredholmGerm.sectionAdd {x : X} (hfs : IsSection P f)
    (hg : B.IsScFredholmGerm f x) (hs : B.IsScPlusSection s) :
    B.IsScFredholmGerm (Polyfold.sectionAdd P f s) x := by
  obtain ⟨hxs, c, hc, hxV, h0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj⟩ := hg
  obtain ⟨h1, h2, h3, h4⟩ := sectionAdd_chartData_germ hfs hs hc h0U hfill ht₀ ht₀0 hconj
  exact ⟨hxs, c, hc, hxV, h0, h0U, _, _, h1, h2, h3, h4⟩

/-- **Theorem 3.1.18 (preprint 3.15), second clause, germ reading** (phase 2): `f + s` is regularizing when `f` is an
sc-Fredholm section in the germ reading (the proof of `regularizing_sectionAdd_wholeChart`, which uses only
that `f` is an sc-smooth regularizing section). -/
theorem regularizing_sectionAdd (hf : B.IsScFredholmSection f) (hs : B.IsScPlusSection s) :
    ∀ m, ∀ x ∈ PX.levelSet m, sectionAdd P f s x ∈ B.doubleLevel m (m + 1) →
      x ∈ PX.levelSet (m + 1) := by
  intro m x hx hfs
  have hfsec := hf.isScSmooth.1
  refine hf.regularizing m x hx fun c hc hmem => ?_
  have hxV : x ∈ c.φ.source := by rw [c.source_eq, mem_preimage, hfsec x] at hmem; exact hmem
  have h1 := hfs c hc (c.mem_source_of_proj (by rw [(hfsec.sectionAdd hs.1) x]; exact hxV))
  refine ⟨?_, ?_⟩
  · rw [c.fst_apply (by rw [hfsec]; exact hxV), hfsec]
    exact (PX.mem_levelSet_iff c.isChart hxV).1 hx
  · have hsx := hs.snd_mem_range (B.isChart_of_mem hc) hxV hx
    have heq : (c (f x)).2 = (c (sectionAdd P f s x)).2 - (c (s x)).2 := by
      rw [sectionAdd_apply hfsec hs.1, c.snd_add hxV]
      change (c (f x)).2 = (c (f x)).2 + (c (s x)).2 - (c (s x)).2
      abel
    obtain ⟨a, ha⟩ := h1.2
    obtain ⟨b, hb⟩ := hsx
    exact ⟨a - b, by rw [map_sub, ha, hb, heq]⟩

/-- **The old hypothesis feeds the germ version** (phase 2): for an sc-Fredholm germ in the
project's whole-chart sense (`IsScFredholmGermWholeChart`), `(f + s, x)` is an sc-Fredholm germ in the germ
reading (`IsScFredholmGermWholeChart.isScFredholmGerm`, then `IsScFredholmGerm.sectionAdd`). -/
theorem IsScFredholmGermWholeChart.sectionAdd_germG {x : X} (hfs : IsSection P f)
    (hg : B.IsScFredholmGermWholeChart f x) (hs : B.IsScPlusSection s) :
    B.IsScFredholmGerm (Polyfold.sectionAdd P f s) x :=
  hg.isScFredholmGerm.sectionAdd hfs hs

end StrongBundle

open StrongBundle in
/-- **Theorem 3.1.18 (preprint 3.15) (stability under sc⁺-perturbations), germ reading** (phase 2; the germ form of
`theorem_3_1_18_wholeChart`): if `f` is an sc-Fredholm section of the strong bundle `P : Y → X` in the text's
germ reading of Definition 3.1.11 (preprint 3.11) (`IsScFredholmSection`) and `s` is an sc⁺-section, then `f + s`
is an sc-Fredholm section in the germ reading.  (The text assumes the bundle tame; tameness is not
used.) -/
theorem theorem_3_1_18_preprint (hf : B.IsScFredholmSection f) (hs : B.IsScPlusSection s) :
    B.IsScFredholmSection (sectionAdd P f s) where
  isScSmooth := hf.isScSmooth.sectionAdd hs
  regularizing := regularizing_sectionAdd hf hs
  germ x hx := (hf.germ x hx).sectionAdd hf.isScSmooth.1 hs

end FredholmSectionsGerm

end Polyfold
