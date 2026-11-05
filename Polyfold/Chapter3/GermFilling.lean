import Polyfold.Chapter3.Filler

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
Definitions 3.4 and 3.6 (filling, filled version) and the local sc⁺-sections of Definition 3.11,
**in the text's germ reading**.

# Fillings and sc⁺-sections as germs

## The text, paraphrased

(Definition 3.6) `(f, x₀)` has a filling if the section germ `Φ ∘ f ∘ φ⁻¹` has a filling `(g, 0)`,
an sc-smooth section germ of `U ◁ F → U` satisfying conditions (1)–(3) of Definition 3.4 near `0`.
(Definition 3.11) A local sc⁺-section `s` near `0`.  Germs are those of Definitions 3.1–3.2: sc-germs
of neighbourhoods whose levels may shrink with the level.

## What is formalized

* `Polyfold.fillDefect`: the map `k(y) = [1 − ρ(r(y))]g(y)` of Definition 3.4 (3).
* `Polyfold.IsFillingGerm`: a filling in the germ sense (`g` an sc-smooth germ on a germ of
  neighbourhoods `G` with `G₀ ⊆ U`, conditions (1)–(3) near `0`).
* `Polyfold.IsScPlusGerm`: a local sc⁺-section in the germ sense.
* `Polyfold.IsSc1.isSc1GermWith_ofSet`: an sc¹ map on `U` is an sc¹-germ on `ofSet U`.

These were introduced in `Chapter3/GermVsChart.lean` (Findings, Chapter 3, items 260–266) and are
placed here, low in the import chain, so that Definition 3.11 itself can be stated with them.

## What the text leaves implicit, and the choices made

See `Chapter3/GermVsChart.lean`: condition (3) for a germ uses a derivative family `Dk` of the
sc¹-germ `[1 − ρ(r(·))]g`, whose value at `0` is unique (`IsSc1GermWith.eq_of_uniqueDiffWithinAt`).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

/-! ### Intersections of germs of neighbourhoods -/

section Inter

variable {E : ScBanach} {C : Set (E 0)}

/-- The intersection `(U_m ∩ U'_m)_m` of two germs of neighbourhoods. -/
def ScNbhdGerm.inter (G₁ G₂ : ScNbhdGerm E C) : ScNbhdGerm E C where
  U m := G₁.U m ∩ G₂.U m
  nested m x hx := ⟨G₁.nested m x hx.1, G₂.nested m x hx.2⟩
  zero_mem m := ⟨G₁.zero_mem m, G₂.zero_mem m⟩
  relOpen m := by
    obtain ⟨O₁, h₁, e₁⟩ := G₁.relOpen m
    obtain ⟨O₂, h₂, e₂⟩ := G₂.relOpen m
    refine ⟨O₁ ∩ O₂, h₁.inter h₂, ?_⟩
    rw [e₁, e₂]
    ext x
    simp only [mem_inter_iff]
    tauto

@[simp] lemma ScNbhdGerm.inter_U (G₁ G₂ : ScNbhdGerm E C) (m : ℕ) :
    (G₁.inter G₂).U m = G₁.U m ∩ G₂.U m := rfl

end Inter

section Preimage

variable {E E' : ScBanach}

/-! ### Shrinking a germ along an sc⁰-germ -/

namespace ScNbhdGerm

variable {C : Set (E 0)} {C' : Set (E' 0)}

/-- The germ `{x ∈ G₀ | f(x) ∈ G'}`, for an sc⁰-germ `f` on `G₀` with `f(0) = 0` mapping `G₀` into
`C'`: the largest sub-germ of `G₀` on which `f` maps into `G'` level by level. -/
def preimage (G₀ : ScNbhdGerm E C) (G' : ScNbhdGerm E' C') {f : E 0 → E' 0} (hf : IsSc0Germ G₀ f)
    (hf0 : f 0 = 0) (hfC : MapsTo f (G₀.U 0) C') : ScNbhdGerm E C where
  U m := {x ∈ G₀.U m | levelMap f m x ∈ G'.U m}
  nested m x hx := ⟨G₀.nested m x hx.1, by
    rw [← hf.incl_levelMap hx.1]
    exact G'.nested m _ hx.2⟩
  zero_mem m := ⟨G₀.zero_mem m, by
    have : levelMap f m (0 : E m) = 0 :=
      levelMap_eq_of_toBase_eq (by rw [map_zero, map_zero, hf0])
    rw [this]; exact G'.zero_mem m⟩
  relOpen m := by
    obtain ⟨O₀, hO₀, hG₀⟩ := G₀.relOpen m
    obtain ⟨O', hO', hG'⟩ := G'.relOpen m
    -- on `G₀.U m` the condition `levelMap f m x ∈ G'.U m` is `levelMap f m x ∈ O'`
    have hC' : ∀ x ∈ G₀.U m, levelMap f m x ∈ E'.lvlSet C' m := fun x hx => by
      rw [ScBanach.mem_lvlSet, hf.toBase_levelMap hx]
      exact hfC (G₀.toBase_mem hx)
    obtain ⟨V, hV, hVeq⟩ := (continuousOn_iff'.1 (hf.continuousOn m)) O' hO'
    refine ⟨O₀ ∩ V, hO₀.inter hV, ?_⟩
    ext x
    constructor
    · rintro ⟨hx, hfx⟩
      have hx' : x ∈ O₀ ∩ E.lvlSet C m := hG₀ ▸ hx
      have : x ∈ levelMap f m ⁻¹' O' ∩ G₀.U m := ⟨(hG' ▸ hfx : levelMap f m x ∈ O' ∩ _).1, hx⟩
      rw [hVeq] at this
      exact ⟨⟨hx'.1, this.1⟩, hx'.2⟩
    · rintro ⟨⟨hxO, hxV⟩, hxC⟩
      have hx : x ∈ G₀.U m := hG₀ ▸ ⟨hxO, hxC⟩
      refine ⟨hx, ?_⟩
      have : x ∈ V ∩ G₀.U m := ⟨hxV, hx⟩
      rw [← hVeq] at this
      rw [hG']; exact ⟨this.1, hC' x hx⟩

lemma preimage_U (G₀ : ScNbhdGerm E C) (G' : ScNbhdGerm E' C') {f : E 0 → E' 0}
    (hf : IsSc0Germ G₀ f) (hf0 : f 0 = 0) (hfC : MapsTo f (G₀.U 0) C') (m : ℕ) :
    (G₀.preimage G' hf hf0 hfC).U m = {x ∈ G₀.U m | levelMap f m x ∈ G'.U m} := rfl

lemma preimage_subset (G₀ : ScNbhdGerm E C) (G' : ScNbhdGerm E' C') {f : E 0 → E' 0}
    (hf : IsSc0Germ G₀ f) (hf0 : f 0 = 0) (hfC : MapsTo f (G₀.U 0) C') (m : ℕ) :
    (G₀.preimage G' hf hf0 hfC).U m ⊆ G₀.U m := fun _ hx => hx.1

lemma preimage_mapsToGerm (G₀ : ScNbhdGerm E C) (G' : ScNbhdGerm E' C') {f : E 0 → E' 0}
    (hf : IsSc0Germ G₀ f) (hf0 : f 0 = 0) (hfC : MapsTo f (G₀.U 0) C') :
    (G₀.preimage G' hf hf0 hfC).MapsToGerm G' f := fun _ _ hx => hx.2

end ScNbhdGerm

end Preimage

section GermReading

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- The map `k(y) = [1 − ρ(r(y))]g(y)` of Definition 3.4 (3). -/
def fillDefect (R : E 0 × F 0 → E 0 × F 0) (g : E 0 → F 0) : E 0 → F 0 :=
  fun y => g y - StrongRetr.ρ R (StrongRetr.r R y) (g y)

/-- **Definition 3.6 with Definition 3.4, the text's germ reading**: `g` is a **filling** of the
principal part `f̂ : O → F` of a section of `K = R(U ◁ F) → O` if `(g, 0)` is an sc-smooth
section germ of `U ◁ F → U` — `g` is an sc-smooth germ (Definition 3.2) on an sc-germ of
neighbourhoods `G` of `0` in `C` (Definition 3.1, levels `G_m` possibly shrinking with `m`) with
`G₀ ⊆ U` — and (1) `f̂ = g` on `O` near `0`; (2) `y ∈ U` near `0` with `g(y) = ρ(r(y))g(y)` lies in
`O`; (3) the linearization `Dk(0)` of the sc¹-germ `k(y) = [1 − ρ(r(y))]g(y)` on `G` (a derivative
family `Dk`; `Dk(0)` is unique), restricted to `ker Dr(0)`, is a topological linear isomorphism
onto `ker ρ(0)`.  The project's `IsFilledVersion` is the special case of a germ `G = ofSet U`
(`IsFilledVersion.isFillingGerm`, `IsFillingGerm.isFilledVersion`). -/
structure IsFillingGerm (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) (fb g : E 0 → F 0) : Prop where
  eq_on : ∀ᶠ x in 𝓝 (0 : E 0), x ∈ StrongRetr.r R '' U → fb x = g x
  mem_of_fixed : ∀ᶠ y in 𝓝 (0 : E 0), y ∈ U → g y = StrongRetr.ρ R (StrongRetr.r R y) (g y) →
    y ∈ StrongRetr.r R '' U
  germ : ∃ G : ScNbhdGerm E C, G.U 0 ⊆ U ∧ IsScSmoothGerm G g ∧
    ∃ Dk : E 1 → E 0 →L[ℝ] F 0, IsSc1GermWith G (fillDefect R g) Dk ∧
      ∃ Φ : LinearMap.ker ((scDeriv U (StrongRetr.r R) (0 : E 1) : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0)
          ≃L[ℝ] LinearMap.ker ((StrongRetr.ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0),
        ∀ v : LinearMap.ker ((scDeriv U (StrongRetr.r R) (0 : E 1) : E 0 →L[ℝ] E 0) :
          E 0 →ₗ[ℝ] E 0),
          ((Φ v : LinearMap.ker ((StrongRetr.ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0)) : F 0) =
            Dk 0 (v : E 0)

/-- **A local sc⁺-section of `U ◁ F → U`, the text's germ reading**: a map `s : E₀ → F₁` which is
an sc-smooth germ into `F¹` on an sc-germ of neighbourhoods `G` of `0` in `C` with `G₀ ⊆ U`. -/
def IsScPlusGerm (C U : Set (E 0)) (s : E 0 → F 1) : Prop :=
  ∃ G : ScNbhdGerm E C, G.U 0 ⊆ U ∧ IsScSmoothGerm (F := F.shift) G s

/-- An sc¹ map on a relatively open `U ∋ 0` is an sc¹-germ on `ofSet U` with the derivative family
`scDeriv U k`. -/
theorem IsSc1.isSc1GermWith_ofSet (hU : ∃ O : Set (E 0), IsOpen O ∧ U = O ∩ C)
    (h0 : (0 : E 0) ∈ U) {k : E 0 → F 0} (hk : IsSc1 U k) :
    IsSc1GermWith (ScNbhdGerm.ofSet hU h0) k (scDeriv U k) :=
  ⟨hk.isSc0.isSc0Germ hU h0, hk.isSc1With_scDeriv.hasFDerivWithinAt, by
    have := hk.tangentMap_isSc0
    rw [ScNbhdGerm.ofSet_tangent]
    exact this.isSc0Germ _ _⟩

end GermReading

end Polyfold
