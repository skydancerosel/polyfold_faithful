import Polyfold.Chapter5.GeneralPosition
import Polyfold.Chapter3.IndexAlongPaths

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5, p. 222:
**Lemma 6.6.4 (preprint 6.29)** (finitely many sc⁺-sections put the family `F` along a path in general position)
and the paragraph after it *(book 2017: Lemma 6.12; see `BookConcordance.md`)*.

# General position of the family `F` along a path

## The text, paraphrased

Let `P : Y → X` be a strong bundle over a tame M-polyfold, `f` an sc-Fredholm section,
`φ : [0, 1] → X` an sc-smooth path and `s` an sc⁺-section of the pull-back of `P` to
`X × [0, 1]` with `s(φ(t), t) = f(φ(t))` (Proposition 6.6.3 (preprint 6.28) (3)).  For sc⁺-sections
`s₁, …, s_k` of the same bundle, `F(t, y, λ) = f(y) − s(y, t) + Σ λᵢ sᵢ(y, t)` satisfies
`F(t, φ(t), 0) = 0`; put `F_t(y, λ) = F(t, y, λ)`.  (Lemma 6.6.4 (preprint 6.29)) There are finitely many
`s₁, …, s_k` with property (P): for every `t ∈ [0, 1]`, `F_t` is in general position to the
boundary of `X × ℝᵏ` at `(φ(t), 0)`.  (After the lemma) (P) implies that `F` is in general position
to the boundary of `[0, 1] × X × ℝᵏ` at all points `(t, φ(t), 0)`.  The text's proof is the
sentence before the lemma: "using the results from the transversality theory".

## What is formalized

* `isZeroAt_paramSection_zero`: if `g(y) = 0`, then `(0, y)` is a zero of
  `F(λ, y) = g(y) + Σ λᵢ sᵢ(y)` (the text's `F(t, φ(t), 0) = 0`).
* `exists_sections_isGeneralPositionGerm_of_isCompact`: the construction in the proof of Theorem
  5.18 over a compact set `K` of zeros of `g`: over a tame `X` with sc-smooth bump functions there
  are finitely many sc⁺-sections `s₁, …, s_k` and an open `W ⊇ K` such that `F` is in general
  position (Definition 5.3.9 (preprint 5.17)) at `(0, y)` for every zero `y ∈ W` of `g`.
* `lemma_6_6_4`: Lemma 6.6.4 (preprint 6.29) in the form that the text derives from (P) and uses afterwards: for an
  sc-smooth family `Φ : ℝⁿ → X` and an sc⁺-section `S` of `ℝⁿ × X → Y` with
  `(f̃ + S)(q, Φ(q)) = 0` for `q` near `[0, 1]ⁿ`, there are finitely many sc⁺-sections
  `s₁, …, s_k` of `ℝⁿ × X → Y` such that `F(λ, (q, y)) = f(y) + S(q, y) + Σ λᵢ sᵢ(q, y)` is in
  general position at `(0, (q, Φ(q)))` for all `q` near `[0, 1]ⁿ`.

## Reading

* Paths and families are on `ℝⁿ` and only `[0, 1]ⁿ` matters (decision D2, as in
  `OrientableNbhd.lean`): `n = 1` is the text's path, `n = 2` serves the homotopies of Theorem
  6.35.  The hypothesis on `S` is the conclusion of Proposition 6.6.3 (preprint 6.28) (3)
  (`exists_isScPlusSection_pullback_of_family`), with `S = −s` (the sign of `sectionAdd`).  The
  factors are ordered `ℝᵏ × (ℝⁿ × X)` (Theorem 3.1.21 (preprint 3.18)'s `paramSection`), so the text's point
  `(t, φ(t), 0)` is `(0, (q, Φ(q)))`.
* The hypotheses are the text's standing ones: `X` tame (§6.5 works over a tame M-polyfold;
  Definition 5.3.9 (preprint 5.17) is read in tame charts, and the openness of general position along the solution
  set, Theorem 4.2.11 (preprint 4.22) (3), uses it), sc-smooth bump functions (assumed from §6.2 on), and `f` with
  tame germ data (Definition 3.6.4 (preprint 3.51), as in Chapters 3 and 5).
* The text gives no proof; the one here is that of Theorem 5.3.10 (preprint 5.18) (`exists_sections_isParamGP`,
  openness of general position, compactness of `[0, 1]ⁿ`).
* Property (P) for the slices `F_t` on `X × ℝᵏ` is not stated here.  The conclusion is the general
  position of `F` at the points `(t, φ(t), 0)`, which is what the implicit function theorem of
  Lemma 6.6.5 (preprint 6.30) needs.  As we read it, the slice form follows from it: the tangent vectors
  `(0, (τ, Φ'(q)τ))` of the family of zeros lie in `ker F'`, so `F'` and `F_t'` have the same
  image, and `Φ'(q)τ` lies in the reduced tangent space (`ℝⁿ` has no boundary, so a corner
  coordinate of `Φ` vanishing at `q` has a minimum there); this chart computation is not carried
  out here.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

/-! ### General position along a compact set of zeros -/

section Compact

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- **The points `(0, y)` are zeros of `F`** (the text: "for `λ = 0` the points `(t, φ(t), 0)`
are solutions of `F(t, φ(t), 0) = 0`"): if `g(y) = 0`, then
`F(0, y) = g(y) + Σ 0 · sᵢ(y) = 0` for `F(λ, y) = g(y) + Σ λᵢ sᵢ(y)`. -/
theorem isZeroAt_paramSection_zero {g : X → Y} (hg : IsSection P g) {k : ℕ}
    {s : Fin k → X → Y} (hs : ∀ i, IsSection P (s i)) {y : X} (hy : IsZeroAt P g y) :
    IsZeroAt (pullbackProj P Prod.snd) (paramSection g hg s hs) (0, y) := by
  rw [isZeroAt_paramSection_iff]
  change IsZeroAt P (paramSlice g hg s hs 0) y
  rw [paramSlice_zero]; exact hy

/-- **Sections putting `F` in general position along a compact set of zeros** (the construction
in the proof of Theorem 5.3.10 (preprint 5.18), `theorem_5_3_10_param`, over a compact set `K` of zeros in place of the
solution set): let `X` be tame with sc-smooth bump functions, `g` an sc-Fredholm section with tame
germ data and `K` a compact set of zeros of `g`.  Then there are finitely many sc⁺-sections
`s₁, …, s_k` and an open `W ⊇ K` such that `F(λ, y) = g(y) + Σ λᵢ sᵢ(y)` is in general position
(Definition 5.3.9 (preprint 5.17)) at `(0, y)` for every zero `y ∈ W` of `g`.  The paracompactness of `ℝᵏ × X` and
of the pull-back bundle (Props; they hold by `MPolyfold.paracompactSpace_prod` and
`paracompactSpace_pullbackSpace`) are instance binders of the conclusion, `k` being existential.
*Proof*: at `x ∈ K`, sections with (i)–(ii) in a tame chart centred at `x`
(`exists_sections_isParamGP`) make `F` general at `(0, x)`
(`isGeneralPositionGerm_paramSection_of_isParamGP`), hence at `(0, y)` for the zeros `y` near `x`
(`exists_isOpen_isGeneralPositionGerm`, over the tame `ℝᵏ × X`); finitely many such
neighbourhoods cover `K`, and the united family keeps (i)–(ii) at each such `(0, y)`
(`isParamGP_of_isGeneralPositionGerm`, `IsParamGP.comp`). -/
theorem exists_sections_isGeneralPositionGerm_of_isCompact (hX : PX.IsTame)
    (hbump : PX.AdmitsBumpFunctions) {g : X → Y} (hg : B.IsScFredholmSectionTame g)
    {K : Set X} (hK : IsCompact K) (hK0 : ∀ x ∈ K, IsZeroAt P g x) :
    ∃ (k : ℕ) (s : Fin k → X → Y) (hs : ∀ i, B.IsScPlusSection (s i)) (W : Set X),
      IsOpen W ∧ K ⊆ W ∧
      ∀ [ParacompactSpace ((Fin k → ℝ) × X)]
        [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))],
        ∀ y ∈ W, IsZeroAt P g y →
          (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
            (paramSection g hg.isScSmooth.1 s fun i => (hs i).1) (0, y) := by
  classical
  obtain ⟨N, hN⟩ := proposition_5_1_3_exists (B := B)
  have hgF : B.IsScFredholmSection g := hg.toIsScFredholmSection
  -- a tame chart centred at every zero of `g`, with a presentation
  have hch : ∀ y : solutionSet P g, ∃ c : StrongBundleChart PX P,
      B.IsTameChart c ∧ (y : X) ∈ c.φ.source ∧ c.φ y = 0 := fun y => by
    obtain ⟨-, c, hc, hyc, hφ0, -⟩ := hg.germTame y (hgF.mem_smoothSet_of_isZeroAt y.2)
    exact ⟨c, hc, hyc, hφ0⟩
  choose c hc hyc hφ0 using hch
  have hpres : ∀ y : solutionSet P g, ∃ (n : ℕ) (Wq : ScBanach)
      (T : ScIso (c y).φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
      (c y).φ.model.C = T 0 ⁻¹' quadrant n Wq 0 := fun y => (c y).φ.model.isPartialQuadrant
  choose n Wq T hT using hpres
  -- at every point of `K`: sections with (i)–(ii), and a neighbourhood where `F_x` is general
  have hfam : ∀ x : K, ∃ (k : ℕ) (s : Fin k → X → Y) (hsp : ∀ i, B.IsScPlusSection (s i)),
      ∃ Ux : Set X, IsOpen Ux ∧ (x : X) ∈ Ux ∧ ∀ y ∈ Ux, IsZeroAt P g y →
        haveI := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
        haveI := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
          ((rnPolyfold k).prod PX) B
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
          (paramSection g hg.isScSmooth.1 s fun i => (hsp i).1) (0, y) := by
    intro x
    have hx0 : IsZeroAt P g x := hK0 x x.2
    obtain ⟨k, s, hsp, -, -, hgpx⟩ := exists_sections_isParamGP hbump hN hg hx0
      (hc ⟨x, hx0⟩) (hyc ⟨x, hx0⟩) (hφ0 ⟨x, hx0⟩) (T ⟨x, hx0⟩) (hT ⟨x, hx0⟩) isOpen_univ
      (mem_univ _)
    have := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
    have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
      ((rnPolyfold k).prod PX) B
    have hFt := theorem_3_1_21_tame hg hsp
    have hz0 : ∀ y, IsZeroAt P g y → IsZeroAt (pullbackProj P Prod.snd)
        (paramSection g hg.isScSmooth.1 s fun i => (hsp i).1) (0, y) := fun y hy =>
      isZeroAt_paramSection_zero hg.isScSmooth.1 (fun i => (hsp i).1) hy
    have h0 := isGeneralPositionGerm_paramSection_of_isParamGP hg hsp hx0 (hc ⟨x, hx0⟩)
      (hyc ⟨x, hx0⟩) (hφ0 ⟨x, hx0⟩) (T ⟨x, hx0⟩) (hT ⟨x, hx0⟩) hgpx
    obtain ⟨W, hWo, h0W, -, hW⟩ :=
      exists_isOpen_isGeneralPositionGerm (prod_rn_isTame hX) hFt (hz0 x hx0) h0
    exact ⟨k, s, hsp, Prod.mk 0 ⁻¹' W, hWo.preimage (continuous_const.prodMk continuous_id),
      h0W, fun y hy hy0 => (hW (0, y) hy (hz0 y hy0)).2.1⟩
  choose k s hsp Ux hUxo hxUx hUx using hfam
  -- a finite subcover of `K`, and the united family `t`
  obtain ⟨T₀, hT₀⟩ := hK.elim_finite_subcover Ux hUxo
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxUx ⟨x, hx⟩⟩)
  let e := Fintype.equivFin (Σ x : T₀, Fin (k x.1))
  set m := Fintype.card (Σ x : T₀, Fin (k x.1)) with hm
  set t : Fin m → X → Y := fun j => s (e.symm j).1.1 (e.symm j).2 with htdef
  have ht : ∀ j, B.IsScPlusSection (t j) := fun j => hsp _ _
  refine ⟨m, t, ht, ⋃ x ∈ T₀, Ux x, isOpen_biUnion fun x _ => hUxo x, hT₀, ?_⟩
  -- `F` is in general position at every `(0, y)`, `y ∈ W` a zero
  intro _ _ y hyW hy
  obtain ⟨x, hxT, hyUx⟩ := mem_iUnion₂.1 hyW
  have := MPolyfold.paracompactSpace_prod (rnPolyfold (k x)) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin (k x) → ℝ) × X → X))
    ((rnPolyfold (k x)).prod PX) B
  have hgx := hUx x y hyUx hy
  have hpx := isParamGP_of_isGeneralPositionGerm hg (hsp x) hy (hc ⟨y, hy⟩) (hyc ⟨y, hy⟩)
    (hφ0 ⟨y, hy⟩) (T ⟨y, hy⟩) (hT ⟨y, hy⟩) hgx
  have hpt := hpx.comp (fun i => e ⟨⟨x, hxT⟩, i⟩) (t := t) (fun i => by
    have := congrArg (fun σ : (Σ x : T₀, Fin (k x.1)) => s σ.1.1 σ.2)
      (e.symm_apply_apply ⟨⟨x, hxT⟩, i⟩)
    exact this.symm)
  exact isGeneralPositionGerm_paramSection_of_isParamGP hg ht hy (hc ⟨y, hy⟩)
    (hyc ⟨y, hy⟩) (hφ0 ⟨y, hy⟩) (T ⟨y, hy⟩) (hT ⟨y, hy⟩) hpt

end Compact

/-! ### Lemma 6.6.4 (preprint 6.29) -/

section Lemma629

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {n : ℕ} [ParacompactSpace ((Fin n → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

/-- **Lemma 6.6.4 (preprint 6.29)**, in the form that the text derives from property (P) and uses afterwards
("`F` is in general position to the boundary at all points `(t, φ(t), 0)`"): let `X` be tame with
sc-smooth bump functions, `f` an sc-Fredholm section with tame germ data, `Φ : ℝⁿ → X`
sc-smooth and `S` an sc⁺-section of the pull-back `π*Y → ℝⁿ × X` with `(f̃ + S)(q, Φ(q)) = 0`
for `q` near `[0, 1]ⁿ` (Proposition 6.6.3 (preprint 6.28) (3), `S = −s`).  Then there are finitely many
sc⁺-sections `s₁, …, s_k` of `π*Y` such that `F(λ, (q, y)) = f(y) + S(q, y) + Σ λᵢ sᵢ(q, y)`
(the text's `F(t, y, λ) = f(y) − s(y, t) + Σ λᵢ sᵢ(y, t)`) is in general position (Definition
5.17) at `(0, (q, Φ(q)))` for all `q` near `[0, 1]ⁿ`.  The paracompactness of
`ℝᵏ × (ℝⁿ × X)` and of the pull-back bundle are instance binders of the conclusion, `k` being
existential.  *Proof*: `f̃ + S` is an sc-Fredholm section with tame germ data
(`IsScFredholmSectionTame.param`, `theorem_3_1_18_tame`) of `π*Y` over the tame `ℝⁿ × X`
(`prod_rn_isTame`), which admits sc-smooth bump functions (`admitsBumpFunctions_prod_rn`);
`exists_sections_isGeneralPositionGerm_of_isCompact` applies to the compact set of zeros
`{(q, Φ(q)) | q ∈ [0, 1]ⁿ}`, and its open `W` pulls back along `q ↦ (q, Φ(q))` to a
neighbourhood of `[0, 1]ⁿ`. -/
theorem lemma_6_6_4 (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {Φ : (Fin n → ℝ) → X}
    (hΦ : (rnPolyfold n).IsScSmoothMap PX Φ)
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    (hz : ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1), IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) (q, Φ q)) :
    ∃ (k : ℕ) (s : Fin k → (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
      (hs : ∀ i, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection
        (s i)),
      ∀ [ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
        [ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
          (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))],
        ∀ᶠ q in 𝓝ˢ (Icc (0 : Fin n → ℝ) 1),
          ((B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).pullback
            (MPolyfold.isScSmoothMap_snd (rnPolyfold k)
              ((rnPolyfold n).prod PX))).IsGeneralPositionGerm
            (paramSection (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S)
              ((isSection_pullbackLift _).sectionAdd hS.1) s fun i => (hs i).1) (0, (q, Φ q)) := by
  have hΦc : Continuous Φ := continuousOn_univ.1 hΦ.continuousOn
  have hγ : Continuous fun q : Fin n → ℝ => (q, Φ q) := continuous_id.prodMk hΦc
  have hg := theorem_3_1_18_tame hf.param hS
  have hK : IsCompact ((fun q : Fin n → ℝ => (q, Φ q)) '' Icc 0 1) :=
    isCompact_Icc.image hγ
  have hK0 : ∀ x ∈ (fun q : Fin n → ℝ => (q, Φ q)) '' Icc 0 1, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (paramLift f hf.isScSmooth.1) S) x := by
    rintro _ ⟨q, hq, rfl⟩
    exact hz.self_of_nhdsSet q hq
  obtain ⟨k, s, hs, W, hWo, hKW, hW⟩ := exists_sections_isGeneralPositionGerm_of_isCompact
    (prod_rn_isTame hX) (MPolyfold.admitsBumpFunctions_prod_rn hbump) hg hK hK0
  refine ⟨k, s, hs, ?_⟩
  intro _ _
  have hWq : (fun q : Fin n → ℝ => (q, Φ q)) ⁻¹' W ∈ 𝓝ˢ (Icc (0 : Fin n → ℝ) 1) :=
    (hWo.preimage hγ).mem_nhdsSet.2 fun q hq => hKW ⟨q, hq, rfl⟩
  filter_upwards [hz, hWq] with q hq hqW
  exact hW _ hqW hq

end Lemma629

end Polyfold
