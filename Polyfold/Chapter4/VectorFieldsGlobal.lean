import Polyfold.Chapter2.TangentLift

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 4, §4.4
"Sc-Differential Forms" (pp. 195–199) and Appendix 4.5 (pp. 199–208): **Lemma 4.4.4** (p. 196),
**Proposition 4.4.5** (p. 196; 2017: Proposition 4.5; preprint: Proposition 4.26) and
**Lemma 4.5.1** (p. 201) on an M-polyfold, with the computation of §4.5.2 (pp. 201–202).  All of
these except Proposition 4.4.5 are new in the 2021 edition.  The local forms are in
`VectorFields.lean`.

# Vector fields and their Lie bracket on an M-polyfold

## The text, paraphrased

(Lemma 4.4.4, p. 196) By the natural identification `(TX)^i ≡ T(X^i)` over `(X¹)^i ≡ X^{i+1}`
(Proposition 2.3.17), the index of an sc-smooth section `A` of `TX → X¹` can be raised by `i`:
`A^(i)` is an sc-smooth vector field of `X^i`, a section of `T(X^i) → X^{i+1}`.

(Proposition 4.4.5, p. 196) For sc-smooth vector fields `A`, `B` on `X` the usual formula defines
the Lie bracket `[A, B]`, an sc-smooth section of `TX|X² → X²`, the pull-back of `TX → X¹` by the
inclusion `X² → X¹`.

(Lemma 4.5.1, p. 201, proof left to the reader) If a local sc-diffeomorphism `φ` relates `A` to
itself and `B` to itself, it relates `[A, B]` to itself; so the bracket does not depend on the
local coordinates.  (§4.5.2) In local models `O = r(U)`, `O' = r'(U')` and for an sc-smooth
`φ : O → O'` with `Dφ A = A ∘ φ`, `Dφ B = B ∘ φ`: differentiating at points of level `2`, using the
symmetry of `D²φ` and the chain rule, `Dφ [A, B] = [A, B] ∘ φ`.

## What is formalized

Local models (`retractLieBracket` of `VectorFields.lean`):
* `IsRetractVectorField.diff_related`: the relation `Df A = A' ∘ f` differentiated at `x ∈ O₂`;
  `IsRetractVectorField.related_shift`: the relation on level `1`.
* `retractLieBracket_natural` (**Lemma 4.5.1**, local form, the computation of §4.5.2):
  `Df(x) [A, B](x) = [A', B'](f(x))` on `O₂` for an sc-smooth `f : O → O'` between retracts
  (not only diffeomorphisms) relating `A` to `A'` and `B` to `B'` on `O₁`.
* `IsRetractVectorField.restrict`, `retractLieBracket_restrict` (the bracket only depends on the
  retraction near the point), `levelMap_levelMap_comp_eq`, and
  `retractLieBracket_natural_inter` (Lemma 4.5.1 for `f` defined on an open part `O ∩ W`, in the
  form `Tf(x, [A, B](x)) = (f(x), [A', B'](f(x)))`).

M-polyfolds:
* `MPolyfold.tangentChartMap_change` (`Tψ = T(ψ ∘ φ⁻¹) ∘ Tφ`), `MPolyfold.chartRetraction`;
  `MPolyfold.principalPart` (the principal part `A_φ` of `A` in a chart),
  `IsScVectorField.isRetractVectorField_principalPart` (it is a vector field on the model),
  `IsScVectorField.principalPart_related` (principal parts are related by transition maps).
* `MPolyfold.chartLieBracket`, `IsScVectorField.chartLieBracket_change` (**Lemma 4.5.1** for
  transition maps: the independence of the chart).
* `MPolyfold.lieBracket` (`[A, B] : X² → TX`, defined in a chosen chart),
  `MPolyfold.tangentChartMap_lieBracket` (in every chart `ψ`,
  `Tψ([A, B](x)) = (ψ(x), [A_ψ, B_ψ](ψ(x)))`), `MPolyfold.continuous_lieBracket`, and
  `proposition_4_4_5` (**Proposition 4.4.5**): `[A, B]` is sc-smooth from `X²` to `TX` and
  `p ∘ [A, B]` is the inclusion `X² → X¹`.
* `MPolyfold.liftLevelOneMap`, `MPolyfold.levelTwoMap` (`f₁ : X¹ → Y¹`, `f₂ : X² → Y²`) and
  `lemma_4_5_1` (**Lemma 4.5.1**): for an sc-smooth `f : X → Y` with `Tf ∘ A = A' ∘ f₁` and
  `Tf ∘ B = B' ∘ f₁` on `X¹`, `Tf ∘ [A, B] = [A', B'] ∘ f₂` on `X²`.
* `MPolyfold.vectorFieldLevelOne`, `MPolyfold.raiseIndex`, `lemma_4_4_4`
  (**Lemma 4.4.4**, `i = 1`): `A^(1) = Φ⁻¹ ∘ A₁` is an sc-smooth vector field on `X¹`, with
  `Φ(A^(1)(x)) = A(x)`.

The hypotheses `IsScVectorField` are satisfiable: `MPolyfold.isScVectorField_zero`
(`VectorFields.lean`).

## What the text leaves implicit, and the choices made

* "Section of `TX|X² → X²`" is read as an sc-smooth map `X² → TX` covering the inclusion
  `X² → X¹`; `X²` is the iterate `(X¹)¹` (`P.shift.shift`).  The pull-back bundle itself is not
  built.
* The bracket at `x ∈ X²` is defined in a chosen chart with a chosen retraction of its model;
  `tangentChartMap_lieBracket` shows that every chart and every retraction gives the same vector
  (Lemma 4.5.1 applied to the transition maps, together with `retractLieBracket_restrict`).
* Lemma 4.5.1 is proved for sc-smooth maps (an sc-diffeomorphism is not needed), between two
  M-polyfolds `X → Y` (the text: a local sc-diffeomorphism `X → X`; its domain and image would
  have to be given their induced M-polyfold structures, which is not done here), with vector
  fields `A, B` on `X` and `A', B'` on `Y`.  The relations `Tf ∘ A = A' ∘ f₁`, `Tf ∘ B = B' ∘ f₁`
  are assumed on `X¹`: the computation of §4.5.2 differentiates them, which needs them on an open
  set of `X¹`, not only at the points of `X₂` as the statement reads.  The local form is also
  applied to the transition maps of charts, which gives the independence of the chart.
* Lemma 4.4.4 is proved for `i = 1`; every fixed `i` follows by applying it to `X¹`, `X²`, …,
  since `A^(1)` is again an sc-smooth vector field; the statement for all `i` at once is
  `lemma_4_4_4_all` in `Chapter2/TangentLiftAll.lean`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

section Naturality

variable {E F : ScBanach} {C : Set (E 0)} {C' : Set (F 0)}

/-- The relation `Dg(r(y)) Ã(y) = Ã'(g(y))` (`g = f ∘ r`) differentiated at `x ∈ O₂` in a direction
`b ∈ T_x(O¹)`: `D²g(x)(A(x), b) + Dg(x) DÃ(x) b = DÃ'(g(x)) Dg(x) b` (§4.5.2, p. 201). -/
theorem IsRetractVectorField.diff_related {R : ScRetraction E C} {R' : ScRetraction F C'}
    {f : E 0 → F 0} (hf : IsScSmoothRetractMap E C R.retract F C' R'.retract f)
    {A : E 1 → E 0} {A' : F 1 → F 0}
    (hA : IsRetractVectorField E C R.retract A) (hA' : IsRetractVectorField F C' R'.retract A')
    (hAA' : ∀ x ∈ E.lvlSet R.retract 1, scDeriv R.U (f ∘ R) x (A x) = A' (levelMap f 1 x))
    {x : E.shift 1} (hx : x ∈ E.shift.lvlSet (E.lvlSet R.retract 1) 1) {b : E 1}
    (hb : scDeriv (E := E.shift) (F := E.shift) R.shift.U R.shift x b = b) :
    scSecondDeriv R.U (f ∘ R) x (levelMap (E := E.shift) (F := E) A 1 x) b +
        scDeriv R.U (f ∘ R) (E.incl 1 x)
          (scDeriv (E := E.shift) (F := E) R.shift.U (A ∘ R.shift) x b) =
      scDeriv (E := F.shift) (F := F) R'.shift.U (A' ∘ R'.shift)
        (levelMap (E := E.shift) (F := F.shift) (levelMap (f ∘ R) 1) 1 x)
        (scDeriv (E := E.shift) (F := F.shift) R.shift.U (levelMap (f ∘ R) 1) x b) := by
  set ρ := R.shift with hρ
  set g := f ∘ R with hg
  have hgs : IsScSmooth R.U g := hf.comp_isScSmooth R rfl
  have hf0 := hf.isSc0 R.isScRetract
  have hAs : IsScSmooth (E := E.shift) (F := E) ρ.U (A ∘ ρ) := hA.isScSmooth_comp R rfl
  have hA's : IsScSmooth (E := F.shift) (F := F) R'.shift.U (A' ∘ R'.shift) :=
    hA'.isScSmooth_comp R' rfl
  have hρs : IsScSmooth ρ.U ρ := ρ.isScSmooth
  have hβ : IsScSmooth ρ.U (scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ)) :=
    hρs.scPair ρ.isScDomain hAs
  have hg1 : IsScSmooth (E := E.shift) (F := F.shift) ρ.U (levelMap g 1) :=
    hgs.shift R.isScDomain
  have hgU : MapsTo g R.U R'.U := fun y hy =>
    R'.retract_subset (hf.mapsTo (R.apply_mem_retract hy))
  have hmaps1 : MapsTo (levelMap g 1) ρ.U R'.shift.U :=
    fun y hy => hgs.isSc1.isSc0.levelMap_mapsTo hgU 1 hy
  have hA'g : IsScSmooth (E := E.shift) (F := F) ρ.U ((A' ∘ R'.shift) ∘ levelMap g 1) :=
    IsScSmooth.comp ρ.isScDomain R'.shift.isScDomain hA's hg1 hmaps1
  have hΓ : IsScSmooth ρ.U (scPair (E := E.shift) (F := F.shift) (G := F) (levelMap g 1)
      ((A' ∘ R'.shift) ∘ levelMap g 1)) := hg1.scPair ρ.isScDomain hA'g
  have hTg : IsSc1 (E.tangentSet R.U) (tangentMap R.U g) := (hgs 2).2.1
  have hβmaps : MapsTo (scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ)) ρ.U
      (E.tangentSet R.U) := fun y hy => ρ.mapsTo hy
  -- `g₁ ∘ r¹ = g₁` and `g₁ = f₁ ∘ r¹` on `U¹`
  have hgρ : ∀ y ∈ ρ.U, levelMap g 1 y = levelMap f 1 (ρ y) := fun y hy =>
    hf0.levelMap_comp R.isSc1.isSc0 R.mapsTo_retract hy
  have hgρρ : ∀ y ∈ ρ.U, levelMap g 1 (ρ y) = levelMap g 1 y := fun y hy => by
    rw [hgρ y hy, hgρ (ρ y) (ρ.mapsTo hy), ρ.idem y hy]
  have hfix : EqOn (tangentMap R.U g ∘ scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ))
      (scPair (E := E.shift) (F := F.shift) (G := F) (levelMap g 1)
        ((A' ∘ R'.shift) ∘ levelMap g 1)) ρ.U := fun y hy => by
    have hyO : ρ y ∈ E.lvlSet R.retract 1 := by
      rw [← R.shift_retract]; exact ρ.mapsTo_retract hy
    have hfO : levelMap f 1 (ρ y) ∈ F.lvlSet R'.retract 1 :=
      hf.mapsTo_levelMap R.isScRetract 1 hyO
    have hfix' : R'.shift (levelMap f 1 (ρ y)) = levelMap f 1 (ρ y) :=
      R'.shift.apply_eq_self_of_mem_retract (by rw [R'.shift_retract]; exact hfO)
    change ((levelMap g 1 (ρ y), scDeriv R.U g (ρ y) (A (ρ y))) : F.tangent 0) =
      (levelMap g 1 y, A' (R'.shift (levelMap g 1 y)))
    rw [hgρρ y hy, hAA' _ hyO, hgρ y hy, hfix']
  have hx1 : x ∈ E.shift.lvlSet ρ.U 1 := E.lvlSet_mono R.retract_subset 2 hx
  obtain ⟨hTβ, hchain⟩ := theorem_1_3_1' ρ.isScDomain R.isScDomain.tangentSet (hβ 1).1 hTg hβmaps
  have hcongr := hTβ.tangentMap_congr ρ.isScDomain hfix
  have hq : ((x, b) : E.shift.tangent 0) ∈ E.shift.tangentSet ρ.U := hx1
  have key := congrArg Prod.snd ((hchain hq).symm.trans (hcongr hq))
  change scDeriv (E.tangentSet R.U) (tangentMap R.U g)
      (levelMap (scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ)) 1 x)
      (scDeriv ρ.U (scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ)) x b) =
    scDeriv ρ.U (scPair (E := E.shift) (F := F.shift) (G := F) (levelMap g 1)
      ((A' ∘ R'.shift) ∘ levelMap g 1)) x b at key
  have hDβ : scDeriv ρ.U (scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ)) x =
      (scDeriv ρ.U ρ x).prod (scDeriv ρ.U (A ∘ ρ) x) :=
    IsSc1.scDeriv_eqOn ((hρs 1).1.isSc1With_scDeriv.scPair (hAs 1).1.isSc1With_scDeriv)
      (ρ.isScDomain.uniqueDiffWithinAt 1) hx1
  have hDΓ : scDeriv ρ.U (scPair (E := E.shift) (F := F.shift) (G := F) (levelMap g 1)
      ((A' ∘ R'.shift) ∘ levelMap g 1)) x =
      (scDeriv ρ.U (levelMap g 1) x).prod (scDeriv ρ.U ((A' ∘ R'.shift) ∘ levelMap g 1) x) :=
    IsSc1.scDeriv_eqOn ((hg1 1).1.isSc1With_scDeriv.scPair (hA'g 1).1.isSc1With_scDeriv)
      (ρ.isScDomain.uniqueDiffWithinAt 1) hx1
  have hlev : levelMap (scPair (E := E.shift) (F := E.shift) (G := E) ρ (A ∘ ρ)) 1 x =
      ((x, levelMap (E := E.shift) (F := E) A 1 x) : E.tangent 1) := by
    rw [IsSc0.levelMap_scPair (hρs 0) (hAs 0) hx1, levelMap_comp_shift_eq R hAs hx,
      ρ.levelMap_one_eq_self (by rw [R.shift_retract]; exact hx)]
  rw [hlev, hDβ, hDΓ, ContinuousLinearMap.prod_apply, ContinuousLinearMap.prod_apply, hb] at key
  have hsplit : ((b, scDeriv ρ.U (A ∘ ρ) x b) : E.tangent 0) =
      ((b, 0) : E.tangent 0) + ((0, scDeriv ρ.U (A ∘ ρ) x b) : E.tangent 0) := by simp
  have hp : ((x, levelMap (E := E.shift) (F := E) A 1 x) : E.tangent 1) ∈
      E.tangent.lvlSet (E.tangentSet R.U) 1 :=
    E.mem_lvlSet_tangentSet.2 (E.lvlSet_mono R.retract_subset 2 hx)
  rw [hsplit, map_add, scDeriv_tangentMap_inr (hgs 2) hp] at key
  have key2 := congrArg Prod.snd key
  simp only [Prod.snd_add] at key2
  -- the chain rule for `Ã' ∘ g₁`
  obtain ⟨-, hchain2⟩ := theorem_1_3_1' ρ.isScDomain R'.shift.isScDomain (hg1 1).1 (hA's 1).1 hmaps1
  have key3 := congrArg Prod.snd (hchain2 hq)
  change scDeriv ρ.U ((A' ∘ R'.shift) ∘ levelMap g 1) x b =
    scDeriv R'.shift.U (A' ∘ R'.shift) (levelMap (levelMap g 1) 1 x)
      (scDeriv ρ.U (levelMap g 1) x b) at key3
  rw [← key3, ← key2]
  rfl


/-- `Dg¹(x) B₁(x) = B'₁(g₂(x))` for `x ∈ O₂`: the relation `Dg(x) B(x) = B'(g(x))` on level `1`. -/
theorem IsRetractVectorField.related_shift {R : ScRetraction E C} {R' : ScRetraction F C'}
    {f : E 0 → F 0} (hf : IsScSmoothRetractMap E C R.retract F C' R'.retract f)
    {B : E 1 → E 0} {B' : F 1 → F 0} (hB : IsRetractVectorField E C R.retract B)
    (hBB' : ∀ x ∈ E.lvlSet R.retract 1, scDeriv R.U (f ∘ R) x (B x) = B' (levelMap f 1 x))
    {x : E.shift 1} (hx : x ∈ E.shift.lvlSet (E.lvlSet R.retract 1) 1) :
    scDeriv (E := E.shift) (F := F.shift) R.shift.U (levelMap (f ∘ R) 1) x
        (levelMap (E := E.shift) (F := E) B 1 x) =
      levelMap (E := F.shift) (F := F) B' 1
        (levelMap (E := E.shift) (F := F.shift) (levelMap (f ∘ R) 1) 1 x) := by
  set ρ := R.shift with hρ
  set g := f ∘ R with hg
  have hgs : IsScSmooth R.U g := hf.comp_isScSmooth R rfl
  have hf0 := hf.isSc0 R.isScRetract
  have hg1 : IsScSmooth (E := E.shift) (F := F.shift) ρ.U (levelMap g 1) :=
    hgs.shift R.isScDomain
  have hx1 : x ∈ E.shift.lvlSet ρ.U 1 := E.lvlSet_mono R.retract_subset 2 hx
  have hxO : E.shift.toBase 1 x ∈ E.lvlSet R.retract 1 := hx
  have hρx : ρ (E.shift.toBase 1 x) = E.shift.toBase 1 x :=
    ρ.apply_eq_self_of_mem_retract (by rw [R.shift_retract]; exact hxO)
  have hD := hgs.isSc1.isSc1With_scDeriv
  have hder : scDeriv (E := E.shift) (F := F.shift) ρ.U (levelMap g 1) x =
      levelDeriv (scDeriv R.U g) 1 x :=
    IsSc1.scDeriv_eqOn (hD.shift R.isScDomain) (ρ.isScDomain.uniqueDiffWithinAt 1) hx1
  have hBs := hB.isScSmooth_comp R rfl
  have hBr : B (E.shift.toBase 1 x) ∈ range (E.toBase 1) := by
    have := (hBs 0 : IsSc0 E.shift E ρ.U (B ∘ ρ)).mem_range 1 x hx1
    rwa [Function.comp_apply, hρx] at this
  symm
  apply levelMap_eq_of_toBase_eq
  rw [hder, hD.toBase_levelDeriv hx1, toBase_levelMap hBr, hBB' _ hxO,
    (hg1 0 : IsSc0 E.shift F.shift ρ.U (levelMap g 1)).toBase_levelMap hx1,
    show levelMap g 1 (E.shift.toBase 1 x) = levelMap f 1 (ρ (E.shift.toBase 1 x)) from
      hf0.levelMap_comp R.isSc1.isSc0 R.mapsTo_retract (E.lvlSet_mono R.retract_subset 1 hxO),
    hρx]

/-- **2021 Lemma 4.5.1, p. 201 (new in the 2021 edition; proof left to the reader), local form**,
by the computation of §4.5.2 (pp. 201–202): for an sc-smooth map `f : (O, C, E) → (O', C', F)`
between retracts and vector fields `A`, `B` on `O`, `A'`, `B'` on `O'` with
`Df(x) A(x) = A'(f(x))`, `Df(x) B(x) = B'(f(x))` on `O₁`, also
`Df(x) [A, B](x) = [A', B'](f(x))` on `O₂` (`Df = D(f ∘ r)`). -/
theorem retractLieBracket_natural {R : ScRetraction E C} {R' : ScRetraction F C'}
    {f : E 0 → F 0} (hf : IsScSmoothRetractMap E C R.retract F C' R'.retract f)
    {A B : E 1 → E 0} {A' B' : F 1 → F 0}
    (hA : IsRetractVectorField E C R.retract A) (hB : IsRetractVectorField E C R.retract B)
    (hA' : IsRetractVectorField F C' R'.retract A') (hB' : IsRetractVectorField F C' R'.retract B')
    (hAA' : ∀ x ∈ E.lvlSet R.retract 1, scDeriv R.U (f ∘ R) x (A x) = A' (levelMap f 1 x))
    (hBB' : ∀ x ∈ E.lvlSet R.retract 1, scDeriv R.U (f ∘ R) x (B x) = B' (levelMap f 1 x))
    {x : E.shift 1} (hx : x ∈ E.shift.lvlSet (E.lvlSet R.retract 1) 1) :
    scDeriv R.U (f ∘ R) (E.incl 1 x) (retractLieBracket R A B x) =
      retractLieBracket R' A' B'
        (levelMap (E := E.shift) (F := F.shift) (levelMap (f ∘ R) 1) 1 x) := by
  have hbB := (hB.shift R.isScRetract).scDeriv_apply R.shift R.shift_retract hx
  have hbA := (hA.shift R.isScRetract).scDeriv_apply R.shift R.shift_retract hx
  have h1 := hA.diff_related hf hA' hAA' hx hbB
  have h2 := hB.diff_related hf hB' hBB' hx hbA
  rw [hB.related_shift hf hBB' hx] at h1
  rw [hA.related_shift hf hAA' hx] at h2
  have hsym := scSecondDeriv_symm R.relOpen (hf.comp_isScSmooth R rfl 2) (z := x)
    (R.retract_subset hx) (levelMap (E := E.shift) (F := E) A 1 x)
    (levelMap (E := E.shift) (F := E) B 1 x)
  unfold retractLieBracket
  rw [map_sub, eq_sub_of_add_eq' h1, eq_sub_of_add_eq' h2, hsym]
  abel

/-- `(f ∘ r)₂ = f₂` on `O₂`. -/
theorem levelMap_levelMap_comp_eq {R : ScRetraction E C} {O' : Set (F 0)} {f : E 0 → F 0}
    (hf : IsScSmoothRetractMap E C R.retract F C' O' f) {x : E.shift 1}
    (hx : x ∈ E.shift.lvlSet (E.lvlSet R.retract 1) 1) :
    levelMap (E := E.shift) (F := F.shift) (levelMap (f ∘ R) 1) 1 x =
      levelMap (E := E.shift) (F := F.shift) (levelMap f 1) 1 x := by
  have hgs : IsScSmooth R.U (f ∘ R) := hf.comp_isScSmooth R rfl
  have hf0 := hf.isSc0 R.isScRetract
  have hg1 : IsScSmooth (E := E.shift) (F := F.shift) R.shift.U (levelMap (f ∘ R) 1) :=
    hgs.shift R.isScDomain
  have hf1 := (hf.shift R.isScRetract).isSc0 R.isScRetract.shift
  have hx1 : x ∈ E.shift.lvlSet R.shift.U 1 := E.lvlSet_mono R.retract_subset 2 hx
  have hxO : E.shift.toBase 1 x ∈ E.lvlSet R.retract 1 := hx
  apply F.shift.toBase_injective 1
  rw [(hg1 0 : IsSc0 E.shift F.shift R.shift.U (levelMap (f ∘ R) 1)).toBase_levelMap hx1,
    hf1.toBase_levelMap hx, hf0.levelMap_comp R.isSc1.isSc0 R.mapsTo_retract
      (E.lvlSet_mono R.retract_subset 1 hxO),
    R.levelMap_one_eq_self hxO]

/-- A vector field on `O = r(U)` restricts to the open subset `O ∩ W = r'(U')`, `r'` the
restriction of `r` (Proposition 2.1.10 (1) of the preprint numbering, `ScRetraction.restrict`). -/
theorem IsRetractVectorField.restrict {R : ScRetraction E C} {A : E 1 → E 0}
    (hA : IsRetractVectorField E C R.retract A) {W : Set (E 0)} (hW : IsOpen W) :
    IsRetractVectorField E C (R.restrict hW).retract A := by
  set R₀ := R.restrict hW with hR₀
  rw [IsRetractVectorField, isScSmoothRetractMap_iff_exists R₀.isScRetract.shift]
  refine ⟨fun x hx => ?_, R₀.shift, R₀.shift_retract, ?_⟩
  · have hx' : x ∈ E.lvlSet R.retract 1 := by
      have : E.toBase 1 x ∈ R₀.retract := hx
      rw [hR₀, R.restrict_retract hW] at this
      exact this.1
    have hxU : x ∈ E.lvlSet R₀.U 1 := E.lvlSet_mono R₀.retract_subset 1 hx
    change ((x, A x) : E.tangent 0) ∈ retractTangent E C R₀.retract
    rw [retractTangent_eq, R₀.mem_tangent_iff_of_mem hx, R.scDeriv_restrict hW hxU]
    exact hA.scDeriv_apply R rfl hx'
  · have h := hA.comp_isScSmooth R.shift R.shift_retract
    exact h.of_subset R₀.shift.isScDomain fun y hy => E.lvlSet_mono inter_subset_left 1 hy

/-- The bracket only depends on the retraction near the point: `[A, B]_{r'} = [A, B]_r` on
`(O ∩ W)₂` for the restriction `r'` of `r`. -/
theorem retractLieBracket_restrict {R : ScRetraction E C} {A B : E 1 → E 0}
    (hA : IsRetractVectorField E C R.retract A) (hB : IsRetractVectorField E C R.retract B)
    {W : Set (E 0)} (hW : IsOpen W) {x : E.shift 1}
    (hx : x ∈ E.shift.lvlSet (R.restrict hW).shift.U 1) :
    retractLieBracket (R.restrict hW) A B x = retractLieBracket R A B x := by
  have hsub : (R.restrict hW).shift.U ⊆ R.shift.U := fun y hy =>
    E.lvlSet_mono inter_subset_left 1 hy
  have hD : ∀ G : E 1 → E 0, IsScSmooth (E := E.shift) (F := E) R.shift.U (G ∘ R.shift) →
      scDeriv (E := E.shift) (F := E) (R.restrict hW).shift.U (G ∘ R.shift) x =
        scDeriv (E := E.shift) (F := E) R.shift.U (G ∘ R.shift) x := by
    intro G hG
    ext v
    have h := (hG 1).1.tangentMap_eqOn_of_subset (R.restrict hW).shift.isScDomain hsub
      (show ((x, v) : E.shift.tangent 0) ∈ E.shift.tangentSet (R.restrict hW).shift.U from hx)
    exact congrArg Prod.snd h
  change scDeriv (E := E.shift) (F := E) (R.restrict hW).shift.U (A ∘ R.shift) x
      (levelMap (E := E.shift) (F := E) B 1 x) -
    scDeriv (E := E.shift) (F := E) (R.restrict hW).shift.U (B ∘ R.shift) x
      (levelMap (E := E.shift) (F := E) A 1 x) = _
  rw [hD A (hA.isScSmooth_comp R rfl), hD B (hB.isScSmooth_comp R rfl)]
  rfl

/-- **Lemma 4.5.1, local form, on an open part `O ∩ W` of a retract** (the shape of a transition
map): for `f : O ∩ W → O'` sc-smooth with `Tf(x, A(x)) = (f(x), A'(f(x)))`,
`Tf(x, B(x)) = (f(x), B'(f(x)))` on `(O ∩ W)₁`, also
`Tf(x, [A, B](x)) = (f(x), [A', B'](f(x)))` on `(O ∩ W)₂`. -/
theorem retractLieBracket_natural_inter {R : ScRetraction E C} {R' : ScRetraction F C'}
    {W : Set (E 0)} (hW : IsOpen W) {f : E 0 → F 0}
    (hf : IsScSmoothRetractMap E C (R.retract ∩ W) F C' R'.retract f)
    {A B : E 1 → E 0} {A' B' : F 1 → F 0}
    (hA : IsRetractVectorField E C R.retract A) (hB : IsRetractVectorField E C R.retract B)
    (hA' : IsRetractVectorField F C' R'.retract A') (hB' : IsRetractVectorField F C' R'.retract B')
    (hAA' : ∀ z ∈ E.lvlSet (R.retract ∩ W) 1, retractTangentMap E C (R.retract ∩ W) f
      ((z, A z) : E.tangent 0) = ((levelMap f 1 z, A' (levelMap f 1 z)) : F.tangent 0))
    (hBB' : ∀ z ∈ E.lvlSet (R.retract ∩ W) 1, retractTangentMap E C (R.retract ∩ W) f
      ((z, B z) : E.tangent 0) = ((levelMap f 1 z, B' (levelMap f 1 z)) : F.tangent 0))
    {x : E.shift 1} (hx : x ∈ E.shift.lvlSet (E.lvlSet (R.retract ∩ W) 1) 1) :
    retractTangentMap E C (R.retract ∩ W) f
        ((E.incl 1 x, retractLieBracket R A B x) : E.tangent 0) =
      ((levelMap f 1 (E.incl 1 x), retractLieBracket R' A' B'
        (levelMap (E := E.shift) (F := F.shift) (levelMap f 1) 1 x)) : F.tangent 0) := by
  set R₀ := R.restrict hW with hR₀def
  have hR₀ : R₀.retract = R.retract ∩ W := R.restrict_retract hW
  have hf₀ : IsScSmoothRetractMap E C R₀.retract F C' R'.retract f := by rw [hR₀]; exact hf
  have hA₀ := hA.restrict hW
  have hB₀ := hB.restrict hW
  have hx₀ : x ∈ E.shift.lvlSet (E.lvlSet R₀.retract 1) 1 := by rw [hR₀]; exact hx
  have hrel : ∀ (G : E 1 → E 0) (G' : F 1 → F 0) (hG : IsRetractVectorField E C R₀.retract G),
      (∀ z ∈ E.lvlSet (R.retract ∩ W) 1, retractTangentMap E C (R.retract ∩ W) f
        ((z, G z) : E.tangent 0) = ((levelMap f 1 z, G' (levelMap f 1 z)) : F.tangent 0)) →
      ∀ z ∈ E.lvlSet R₀.retract 1, scDeriv R₀.U (f ∘ R₀) z (G z) = G' (levelMap f 1 z) := by
    intro G G' hG hGG' z hz
    have h := hGG' z (by rw [← hR₀]; exact hz)
    rw [← hR₀, retractTangentMap_apply hf₀ R₀ rfl (hG.mem_retractTangent hz)] at h
    exact congrArg Prod.snd h
  have hnat := retractLieBracket_natural hf₀ hA₀ hB₀ hA' hB' (hrel A A' hA₀ hAA')
    (hrel B B' hB₀ hBB') hx₀
  have hx₀U : x ∈ E.shift.lvlSet R₀.shift.U 1 := E.lvlSet_mono R₀.retract_subset 2 hx₀
  have hloc := retractLieBracket_restrict hA hB hW hx₀U
  have hbr := (proposition_4_4_5_local hA₀ hB₀).1 x hx₀
  rw [← hR₀, ← hloc, retractTangentMap_apply hf₀ R₀ rfl hbr, hnat,
    levelMap_levelMap_comp_eq hf₀ hx₀]
  refine Prod.ext ?_ rfl
  have hxO : E.incl 1 x ∈ E.lvlSet R₀.retract 1 := hx₀
  change levelMap (f ∘ R₀) 1 (E.incl 1 x) = levelMap f 1 (E.incl 1 x)
  rw [(hf₀.isSc0 R₀.isScRetract).levelMap_comp R₀.isSc1.isSc0 R₀.mapsTo_retract
    (E.lvlSet_mono R₀.retract_subset 1 hxO)]
  exact congrArg (levelMap f 1) (R₀.levelMap_one_eq_self hxO)

end Naturality

/-! ### Principal parts and the Lie bracket on an M-polyfold -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- The change of tangent charts: `Tψ = T(ψ ∘ φ⁻¹) ∘ Tφ` over `V_φ ∩ V_ψ` (formula (2.9)). -/
theorem tangentChartMap_change {φ ψ : MChart X} (hφ : P.IsChart φ) (hψ : P.IsChart ψ)
    {α : P.TangentSpace} (hαφ : α ∈ tangentChartSet φ) (hαψ : α ∈ tangentChartSet ψ) :
    tangentChartMap hψ α = retractTangentMap φ.model.E φ.model.C (φ.overlap ψ)
      (φ.transition ψ) (tangentChartMap hφ α) := by
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  rw [tangentChartMap_mk hψ hαψ, tangentChartMap_mk hφ hαφ,
    p.transport_transport hφ hψ hαφ hαψ]

/-- A chosen sc-smooth retraction onto the model `O` of a chart. -/
def chartRetraction (φ : MChart X) : ScRetraction φ.model.E φ.model.C :=
  φ.model.isScRetract.choose

omit [T2Space X] [ParacompactSpace X] in
lemma chartRetraction_retract (φ : MChart X) : (chartRetraction φ).retract = φ.model.O :=
  φ.model.isScRetract.choose_spec

section PrincipalPart

variable {φ : MChart X} (hφ : P.IsChart φ) (x₀ : P.Level 1)

/-- The principal part `A_φ : O₁ → E` of a vector field `A : X¹ → TX` in the chart `φ`:
`Tφ(A(φ⁻¹(z))) = (z, A_φ(z))` (`x₀` is a junk value off `O₁`). -/
def principalPart (A : P.Level 1 → P.TangentSpace) (z : φ.model.E 1) : φ.model.E 0 :=
  (tangentChartMap hφ (A ((levelChart hφ x₀).symm z))).2

/-- `Tφ(A(y)) = (φ(y), A_φ(φ(y)))` for a section `A` and `y ∈ V₁`. -/
theorem tangentChartMap_eq_principalPart {A : P.Level 1 → P.TangentSpace}
    (hA : ∀ x, P.tangentProj (A x) = x) {y : P.Level 1} (hy : P.levelVal 1 y ∈ φ.source) :
    tangentChartMap hφ (A y) =
      ((levelChart hφ x₀ y, principalPart hφ x₀ A (levelChart hφ x₀ y)) :
        φ.model.E.tangent 0) := by
  have hsy : (levelChart hφ x₀).symm (levelChart hφ x₀ y) = y :=
    (levelChart hφ x₀).symm_apply_apply hy
  have hα : A y ∈ tangentChartSet φ := by
    change P.levelVal 1 (P.tangentProj (A y)) ∈ φ.source
    rw [hA]; exact hy
  refine Prod.ext ?_ ?_
  · rw [tangentChartMap_fst hφ hα, hA, levelChart_apply]
  · change _ = (tangentChartMap hφ (A ((levelChart hφ x₀).symm (levelChart hφ x₀ y)))).2
    rw [hsy]

variable {hφ x₀}

/-- The principal part of an sc-smooth vector field is a vector field on the local model
(Definition 4.4.3 in the chart `φ`). -/
theorem IsScVectorField.isRetractVectorField_principalPart {A : P.Level 1 → P.TangentSpace}
    (hA : P.IsScVectorField A) :
    IsRetractVectorField φ.model.E φ.model.C φ.model.O (principalPart hφ x₀ A) := by
  have hmaps : MapsTo A (levelChart hφ x₀).source (tangentChart hφ (A x₀)).source :=
    fun y hy => by
      change P.levelVal 1 (P.tangentProj (A y)) ∈ φ.source
      rw [hA.2]; exact hy
  have h := hA.1.smooth (levelChart hφ x₀) (tangentChart hφ (A x₀)) (P.shift_isChart hφ x₀)
    (P.tangentPolyfold_isChart hφ _) _ (levelChart hφ x₀).isOpen_source
    (fun y hy => ⟨mem_univ _, hy⟩) hmaps
  have himg : levelChart hφ x₀ '' (levelChart hφ x₀).source =
      φ.model.E.lvlSet φ.model.O 1 := (levelChart hφ x₀).image_source
  rw [himg] at h
  refine h.congr fun z hz => ?_
  have hz' : φ.model.E.toBase 1 z ∈ φ.model.O := hz
  have hsrc : P.levelVal 1 ((levelChart hφ x₀).symm z) ∈ φ.source := by
    rw [levelChart_symm_apply hφ x₀ hz']; exact φ.symm_mapsTo hz'
  change tangentChartMap hφ (A ((levelChart hφ x₀).symm z)) =
    ((z, principalPart hφ x₀ A z) : φ.model.E.tangent 0)
  rw [tangentChartMap_eq_principalPart hφ x₀ hA.2 hsrc, (levelChart hφ x₀).apply_symm_apply hz]

/-- The principal parts in two charts are related by the transition map:
`T(ψ ∘ φ⁻¹)(z, A_φ(z)) = (ψφ⁻¹(z), A_ψ(ψφ⁻¹(z)))` on the overlap. -/
theorem IsScVectorField.principalPart_related {A : P.Level 1 → P.TangentSpace}
    (hA : P.IsScVectorField A) {ψ : MChart X} (hψ : P.IsChart ψ) (y₀ : P.Level 1)
    {z : φ.model.E 1} (hz : z ∈ φ.model.E.lvlSet (φ.overlap ψ) 1) :
    retractTangentMap φ.model.E φ.model.C (φ.overlap ψ) (φ.transition ψ)
        ((z, principalPart hφ x₀ A z) : φ.model.E.tangent 0) =
      ((levelMap (φ.transition ψ) 1 z, principalPart hψ y₀ A (levelMap (φ.transition ψ) 1 z)) :
        ψ.model.E.tangent 0) := by
  have hzO : φ.model.E.toBase 1 z ∈ φ.model.O := φ.overlap_subset ψ hz
  have hyv : P.levelVal 1 ((levelChart hφ x₀).symm z) = φ.symm (φ.model.E.toBase 1 z) :=
    levelChart_symm_apply hφ x₀ hzO
  obtain ⟨w, hw, hwz⟩ := hz
  have hyw : P.levelVal 1 ((levelChart hφ x₀).symm z) = w := by
    rw [hyv, ← hwz, φ.symm_apply_apply hw.1]
  have hyφ : P.levelVal 1 ((levelChart hφ x₀).symm z) ∈ φ.source := hyw ▸ hw.1
  have hyψ : P.levelVal 1 ((levelChart hφ x₀).symm z) ∈ ψ.source := hyw ▸ hw.2
  have hαφ : A ((levelChart hφ x₀).symm z) ∈ tangentChartSet φ := by
    change P.levelVal 1 (P.tangentProj _) ∈ φ.source
    rw [hA.2]; exact hyφ
  have hαψ : A ((levelChart hφ x₀).symm z) ∈ tangentChartSet ψ := by
    change P.levelVal 1 (P.tangentProj _) ∈ ψ.source
    rw [hA.2]; exact hyψ
  have h1 := tangentChartMap_change hφ hψ hαφ hαψ
  have hzO' : z ∈ φ.model.E.lvlSet φ.model.O 1 := hzO
  rw [tangentChartMap_eq_principalPart hφ x₀ hA.2 hyφ, (levelChart hφ x₀).apply_symm_apply hzO',
    tangentChartMap_eq_principalPart hψ y₀ hA.2 hyψ] at h1
  have htr : levelChart hψ y₀ ((levelChart hφ x₀).symm z) = levelMap (φ.transition ψ) 1 z :=
    levelChart_transition hφ x₀ hψ y₀ hzO
  rw [htr] at h1
  exact h1.symm

variable (hφ x₀) in
/-- The Lie bracket of the principal parts in the chart `φ`, with the chosen retraction. -/
def chartLieBracket (A B : P.Level 1 → P.TangentSpace) (z : φ.model.E.shift 1) : φ.model.E 0 :=
  retractLieBracket (chartRetraction φ) (principalPart hφ x₀ A) (principalPart hφ x₀ B) z

/-- Proposition 4.4.5 in the chart `φ` (`proposition_4_4_5_local`). -/
theorem IsScVectorField.chartLieBracket_spec {A B : P.Level 1 → P.TangentSpace}
    (hA : P.IsScVectorField A) (hB : P.IsScVectorField B) :
    (∀ z ∈ φ.model.E.shift.lvlSet (φ.model.E.lvlSet φ.model.O 1) 1,
      ((φ.model.E.incl 1 z, chartLieBracket hφ x₀ A B z) : φ.model.E.tangent 0) ∈
        retractTangent φ.model.E φ.model.C φ.model.O) ∧
    IsScSmoothRetractMap φ.model.E.shift.shift
      (φ.model.E.shift.lvlSet (φ.model.E.lvlSet φ.model.C 1) 1)
      (φ.model.E.shift.lvlSet (φ.model.E.lvlSet φ.model.O 1) 1) φ.model.E.tangent
      (φ.model.E.tangentSet φ.model.C) (retractTangent φ.model.E φ.model.C φ.model.O)
      (fun z => ((φ.model.E.incl 1 z, chartLieBracket hφ x₀ A B z) : φ.model.E.tangent 0)) := by
  have hA' := hA.isRetractVectorField_principalPart (hφ := hφ) (x₀ := x₀)
  have hB' := hB.isRetractVectorField_principalPart (hφ := hφ) (x₀ := x₀)
  rw [← chartRetraction_retract φ] at hA' hB'
  have h := proposition_4_4_5_local hA' hB'
  rw [chartRetraction_retract φ] at h
  exact h

/-- **Independence of the chart** (2021 Lemma 4.5.1, p. 201, applied to transition maps): the
brackets in two charts are related by the tangent map of the transition map. -/
theorem IsScVectorField.chartLieBracket_change {A B : P.Level 1 → P.TangentSpace}
    (hA : P.IsScVectorField A) (hB : P.IsScVectorField B) {ψ : MChart X} (hψ : P.IsChart ψ)
    (y₀ : P.Level 1) {z : φ.model.E.shift 1}
    (hz : z ∈ φ.model.E.shift.lvlSet (φ.model.E.lvlSet (φ.overlap ψ) 1) 1) :
    retractTangentMap φ.model.E φ.model.C (φ.overlap ψ) (φ.transition ψ)
        ((φ.model.E.incl 1 z, chartLieBracket hφ x₀ A B z) : φ.model.E.tangent 0) =
      ((levelMap (φ.transition ψ) 1 (φ.model.E.incl 1 z), chartLieBracket hψ y₀ A B
        (levelMap (E := φ.model.E.shift) (F := ψ.model.E.shift)
          (levelMap (φ.transition ψ) 1) 1 z)) : ψ.model.E.tangent 0) := by
  obtain ⟨W, hW, hWeq⟩ := φ.exists_isOpen_image_eq (s := φ.source ∩ ψ.source) inter_subset_left
    (φ.isOpen_source.inter ψ.isOpen_source)
  have hov : φ.overlap ψ = (chartRetraction φ).retract ∩ W := by
    rw [chartRetraction_retract]; exact hWeq
  have hf : IsScSmoothRetractMap φ.model.E φ.model.C ((chartRetraction φ).retract ∩ W)
      ψ.model.E ψ.model.C (chartRetraction ψ).retract (φ.transition ψ) := by
    rw [← hov, chartRetraction_retract]
    exact (hφ.compatible hψ (P := P)).1.mono_target fun _ hz =>
      ψ.overlap_subset φ (φ.transition_mapsTo ψ hz)
  have hAφ := hA.isRetractVectorField_principalPart (hφ := hφ) (x₀ := x₀)
  have hBφ := hB.isRetractVectorField_principalPart (hφ := hφ) (x₀ := x₀)
  have hAψ := hA.isRetractVectorField_principalPart (hφ := hψ) (x₀ := y₀)
  have hBψ := hB.isRetractVectorField_principalPart (hφ := hψ) (x₀ := y₀)
  rw [← chartRetraction_retract φ] at hAφ hBφ
  rw [← chartRetraction_retract ψ] at hAψ hBψ
  have hAA' : ∀ w ∈ φ.model.E.lvlSet ((chartRetraction φ).retract ∩ W) 1,
      retractTangentMap φ.model.E φ.model.C ((chartRetraction φ).retract ∩ W) (φ.transition ψ)
        ((w, principalPart hφ x₀ A w) : φ.model.E.tangent 0) =
      ((levelMap (φ.transition ψ) 1 w, principalPart hψ y₀ A (levelMap (φ.transition ψ) 1 w)) :
        ψ.model.E.tangent 0) := fun w hw => by
    rw [← hov] at hw ⊢; exact hA.principalPart_related hψ y₀ hw
  have hBB' : ∀ w ∈ φ.model.E.lvlSet ((chartRetraction φ).retract ∩ W) 1,
      retractTangentMap φ.model.E φ.model.C ((chartRetraction φ).retract ∩ W) (φ.transition ψ)
        ((w, principalPart hφ x₀ B w) : φ.model.E.tangent 0) =
      ((levelMap (φ.transition ψ) 1 w, principalPart hψ y₀ B (levelMap (φ.transition ψ) 1 w)) :
        ψ.model.E.tangent 0) := fun w hw => by
    rw [← hov] at hw ⊢; exact hB.principalPart_related hψ y₀ hw
  rw [hov] at hz ⊢
  exact retractLieBracket_natural_inter hW hf hAφ hBφ hAψ hBψ hAA' hBB' hz

end PrincipalPart

/-! ### The Lie bracket `[A, B] : X² → TX` (Proposition 4.4.5) -/

section Bracket

variable {A B : P.Level 1 → P.TangentSpace}

/-- For `x ∈ X²` in the domain of `ψ`: `ι(ψ¹)¹(x) = ψ(x)` on level `1`, and `(ψ¹)¹(x) ∈ O₂`. -/
lemma levelLift_levelChart_spec {ψ : MChart X} (hψ : P.IsChart ψ) (y₀ : P.Level 1)
    (x : P.shift.Level 1) (hx : P.levelVal 1 (P.shift.levelVal 1 x) ∈ ψ.source) :
    ψ.model.E.incl 1 (levelLift (levelChart hψ y₀) 1 (P.shift.levelVal 1 x)) =
        levelLift ψ 1 (P.levelVal 1 (P.shift.levelVal 1 x)) ∧
      levelLift (levelChart hψ y₀) 1 (P.shift.levelVal 1 x) ∈
        ψ.model.E.shift.lvlSet (ψ.model.E.lvlSet ψ.model.O 1) 1 := by
  have h := P.shift.toBase_levelLift (P.shift_isChart hψ y₀) (x := P.shift.levelVal 1 x) hx
    (P.shift.levelVal_mem x)
  refine ⟨h, ?_⟩
  change (levelChart hψ y₀).model.E.toBase 1 _ ∈ ψ.model.E.lvlSet ψ.model.O 1
  rw [h]
  exact (levelChart hψ y₀).mapsTo_model _ hx

/-- The tuple `(x, φ, [A_φ, B_φ](φ(x)))` at `x ∈ X²`, in a chosen chart `φ` around `x`. -/
def lieBracketPre (hA : P.IsScVectorField A) (hB : P.IsScVectorField B) (x : P.shift.Level 1) :
    P.TangentPre where
  x := P.levelVal 1 (P.shift.levelVal 1 x)
  φ := P.someChart (P.levelVal 1 (P.shift.levelVal 1 x))
  h := chartLieBracket (P.someChart_isChart _) (P.shift.levelVal 1 x) A B
    (levelLift (levelChart (P.someChart_isChart _) (P.shift.levelVal 1 x)) 1
      (P.shift.levelVal 1 x))
  isChart := P.someChart_isChart _
  mem_source := P.mem_someChart_source _
  mem_level := P.levelVal_mem _
  mem_tangent := by
    have hs := levelLift_levelChart_spec (P.someChart_isChart _) (P.shift.levelVal 1 x) x
      (P.mem_someChart_source _)
    rw [← hs.1]
    exact (IsScVectorField.chartLieBracket_spec (hφ := P.someChart_isChart _)
      (x₀ := P.shift.levelVal 1 x) hA hB).1 _ hs.2

/-- **The Lie bracket** `[A, B] : X² → TX` of two sc-smooth vector fields (Proposition 4.4.5,
§4.5.1): the class of `[A_φ, B_φ](φ(x))` in a chart `φ` around `x`; by
`tangentChartMap_lieBracket` it is the same in every chart. -/
def lieBracket (hA : P.IsScVectorField A) (hB : P.IsScVectorField B) (x : P.shift.Level 1) :
    P.TangentSpace :=
  TangentSpace.mk (lieBracketPre hA hB x)

/-- `[A, B](x) ∈ T_xX`: `[A, B]` is a section of `TX|X² → X²`. -/
theorem tangentProj_lieBracket (hA : P.IsScVectorField A) (hB : P.IsScVectorField B)
    (x : P.shift.Level 1) : P.tangentProj (lieBracket hA hB x) = P.shift.levelVal 1 x :=
  P.level_ext rfl

/-- **Independence of the chart** (2021 Lemma 4.5.1, p. 201): in every chart `ψ` around `x ∈ X²`,
`Tψ([A, B](x)) = (ψ(x), [A_ψ, B_ψ](ψ(x)))`. -/
theorem tangentChartMap_lieBracket (hA : P.IsScVectorField A) (hB : P.IsScVectorField B)
    (x : P.shift.Level 1) {ψ : MChart X} (hψ : P.IsChart ψ)
    (hx : P.levelVal 1 (P.shift.levelVal 1 x) ∈ ψ.source) (y₀ : P.Level 1) :
    tangentChartMap hψ (lieBracket hA hB x) =
      ((levelLift ψ 1 (P.levelVal 1 (P.shift.levelVal 1 x)), chartLieBracket hψ y₀ A B
        (levelLift (levelChart hψ y₀) 1 (P.shift.levelVal 1 x))) : ψ.model.E.tangent 0) := by
  set q := lieBracketPre hA hB x with hq
  set x₁ := P.shift.levelVal 1 x with hx₁
  set φ := P.someChart (P.levelVal 1 x₁) with hφdef
  have hφ : P.IsChart φ := P.someChart_isChart _
  have hxφ : P.levelVal 1 x₁ ∈ φ.source := P.mem_someChart_source _
  rw [lieBracket, tangentChartMap_mk hψ hx]
  refine Prod.ext (q.transport_fst hψ hx) ?_
  have hsφ := levelLift_levelChart_spec hφ x₁ x hxφ
  set z := levelLift (levelChart hφ x₁) 1 x₁ with hz_def
  have hz : z ∈ φ.model.E.shift.lvlSet (φ.model.E.lvlSet (φ.overlap ψ) 1) 1 := by
    change φ.model.E.toBase 1 (φ.model.E.incl 1 z) ∈ φ.overlap ψ
    rw [hsφ.1, P.toBase_levelLift hφ hxφ (P.levelVal_mem x₁)]
    exact ⟨_, ⟨hxφ, hx⟩, rfl⟩
  have hvec : q.vec = ((φ.model.E.incl 1 z, chartLieBracket hφ x₁ A B z) :
      φ.model.E.tangent 0) := by
    change ((levelLift φ 1 (P.levelVal 1 x₁), chartLieBracket hφ x₁ A B z) :
      φ.model.E.tangent 0) = _
    rw [hsφ.1]
  have hch := IsScVectorField.chartLieBracket_change (hφ := hφ) (x₀ := x₁) hA hB hψ y₀ hz
  change (retractTangentMap φ.model.E φ.model.C (φ.overlap ψ) (φ.transition ψ) q.vec).2 = _
  rw [hvec, hch]
  change chartLieBracket hψ y₀ A B _ = chartLieBracket hψ y₀ A B _
  congr 1
  apply ψ.model.E.shift.toBase_injective 1
  have hT1 := ((hφ.compatible hψ (P := P)).1.shift (φ.isScRetract_overlap ψ)).isSc0
    (φ.isScRetract_overlap ψ).shift
  rw [hT1.toBase_levelMap hz]
  have hsψ := levelLift_levelChart_spec hψ y₀ x hx
  have hzO : φ.model.E.toBase 1 (levelChart hφ x₁ x₁) ∈ φ.model.O := by
    rw [levelChart_apply, P.toBase_levelLift hφ hxφ (P.levelVal_mem x₁)]
    exact φ.mapsTo_model _ hxφ
  have htr := levelChart_transition hφ x₁ hψ y₀ hzO
  rw [(levelChart hφ x₁).transition_apply (levelChart hψ y₀) hxφ] at htr
  change levelMap (φ.transition ψ) 1 (φ.model.E.incl 1 z) =
    ψ.model.E.incl 1 (levelLift (levelChart hψ y₀) 1 x₁)
  rw [hsφ.1, hsψ.1]
  exact htr.symm

/-- `Tψ ∘ [A, B] = ([A_ψ, B_ψ]-section) ∘ (ψ¹)¹` on the domain of the chart `(ψ¹)¹` of `X²`. -/
theorem tangentChartMap_lieBracket_eq (hA : P.IsScVectorField A) (hB : P.IsScVectorField B)
    {ψ : MChart X} (hψ : P.IsChart ψ) (y₀ : P.Level 1) (x₀ : P.shift.Level 1)
    {y : P.shift.Level 1} (hy : y ∈ (levelChart (P.shift_isChart hψ y₀) x₀).source) :
    tangentChartMap hψ (lieBracket hA hB y) =
      ((ψ.model.E.incl 1 (levelChart (P.shift_isChart hψ y₀) x₀ y),
        chartLieBracket hψ y₀ A B (levelChart (P.shift_isChart hψ y₀) x₀ y)) :
        ψ.model.E.tangent 0) := by
  rw [tangentChartMap_lieBracket hA hB y hψ hy y₀, levelChart_apply,
    (levelLift_levelChart_spec hψ y₀ y hy).1]

/-- `[A, B] : X² → TX` is continuous. -/
theorem continuous_lieBracket (hA : P.IsScVectorField A) (hB : P.IsScVectorField B) :
    Continuous (lieBracket hA hB) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨ψ, hψ, W, hW, rfl⟩
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  set x₁ := P.shift.levelVal 1 x
  set χ := levelChart (P.shift_isChart hψ x₁) x
  have hG := (IsScVectorField.chartLieBracket_spec (hφ := hψ) (x₀ := x₁) hA hB).2
  have hGc := (hG.isSc0 ψ.model.isScRetract.shift.shift).continuousOn_base
  have hc : ContinuousOn ((fun z => ((ψ.model.E.incl 1 z, chartLieBracket hψ x₁ A B z) :
      ψ.model.E.tangent 0)) ∘ χ) χ.source :=
    hGc.comp χ.continuousOn_toFun fun y hy => χ.mapsTo_model y hy
  refine ⟨χ.source ∩ ((fun z => ((ψ.model.E.incl 1 z, chartLieBracket hψ x₁ A B z) :
      ψ.model.E.tangent 0)) ∘ χ) ⁻¹' W, ?_, hc.isOpen_inter_preimage χ.isOpen_source hW,
      ⟨hx.1, ?_⟩⟩
  · rintro y ⟨hy, hyW⟩
    refine ⟨hy, ?_⟩
    rw [tangentChartMap_lieBracket_eq hA hB hψ x₁ x hy]
    exact hyW
  · have h2 := hx.2
    change tangentChartMap hψ (lieBracket hA hB x) ∈ W at h2
    rw [tangentChartMap_lieBracket_eq hA hB hψ x₁ x hx.1] at h2
    exact h2

/-- **2021 Proposition 4.4.5, p. 196** (2017: Proposition 4.5; preprint: Proposition 4.26; proof in
§4.5.1–§4.5.2): for sc-smooth vector fields `A`, `B` on the M-polyfold `X`, the Lie bracket
`[A, B]`, defined in charts by the usual formula, is an sc-smooth section of `TX|X² → X²`: an
sc-smooth map `X² → TX` with `p([A, B](x)) = x`.  It does not depend on the chart
(`tangentChartMap_lieBracket`). -/
theorem _root_.Polyfold.proposition_4_4_5 (hA : P.IsScVectorField A)
    (hB : P.IsScVectorField B) :
    P.shift.shift.IsScSmoothMap P.tangentPolyfold (lieBracket hA hB) ∧
      ∀ x, P.tangentProj (lieBracket hA hB x) = P.shift.levelVal 1 x := by
  refine ⟨?_, tangentProj_lieBracket hA hB⟩
  refine IsScSmoothOn.of_exists_charts isOpen_univ (continuous_lieBracket hA hB).continuousOn
    fun x _ => ?_
  set x₁ := P.shift.levelVal 1 x
  obtain ⟨ψ, hψ, hxψ⟩ := P.exists_isChart_mem_source (P.levelVal 1 x₁)
  set χ := levelChart (P.shift_isChart hψ x₁) x
  refine ⟨χ, tangentChart hψ (lieBracket hA hB x), χ.source,
    P.shift.shift_isChart (P.shift_isChart hψ x₁) x, P.tangentPolyfold_isChart hψ _,
    χ.isOpen_source, hxψ, fun y hy => ⟨mem_univ _, hy⟩, fun y hy => hy, ?_⟩
  have himg : χ '' χ.source = ψ.model.E.shift.lvlSet (ψ.model.E.lvlSet ψ.model.O 1) 1 :=
    χ.image_source
  rw [himg]
  refine (IsScVectorField.chartLieBracket_spec (hφ := hψ) (x₀ := x₁) hA hB).2.congr
    fun z hz => ?_
  have hsrc : χ.symm z ∈ χ.source := χ.symm_mapsTo hz
  change ((ψ.model.E.incl 1 z, chartLieBracket hψ x₁ A B z) : ψ.model.E.tangent 0) =
    tangentChartMap hψ (lieBracket hA hB (χ.symm z))
  rw [tangentChartMap_lieBracket_eq hA hB hψ x₁ x hsrc, χ.apply_symm_apply hz]

end Bracket

/-! ### Lemma 4.5.1 on M-polyfolds: naturality of the bracket -/

section Naturality

universe v

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {f : X → Y} (hf : P.IsScSmoothMap Q f)

/-- The level-`1` map `f₁ : X¹ → Y¹` of an sc-smooth map. -/
def liftLevelOneMap (x : P.Level 1) : Q.Level 1 :=
  Q.levelMk 1 (f (P.levelVal 1 x)) (hf.mapsTo_levelSet 1 (P.levelVal_mem x))

/-- The level-`2` map `f₂ : X² → Y²` of an sc-smooth map. -/
def levelTwoMap (x : P.shift.Level 1) : Q.shift.Level 1 :=
  Q.shift.levelMk 1 (liftLevelOneMap hf (P.shift.levelVal 1 x))
    ((mem_shift_levelSet_iff _).2 (hf.mapsTo_levelSet 2
      ((mem_shift_levelSet_iff _).1 (P.shift.levelVal_mem x))))

/-- `(ψ ∘ f ∘ φ⁻¹)₁ (φ(x)) = ψ(f(x))` on level `1`. -/
lemma levelMap_coord_levelLift {φ : MChart X} {ψ : MChart Y} {x : X} (hxφ : x ∈ φ.source)
    (hφ : P.IsChart φ) (hψ : Q.IsChart ψ) (hfx : f x ∈ ψ.source) (hx1 : x ∈ P.levelSet 1)
    (hfx1 : f x ∈ Q.levelSet 1) :
    levelMap (ψ ∘ f ∘ φ.symm) 1 (levelLift φ 1 x) = levelLift ψ 1 (f x) := by
  apply levelMap_eq_of_toBase_eq
  rw [Q.toBase_levelLift hψ hfx hfx1, P.toBase_levelLift hφ hxφ hx1]
  simp only [Function.comp_apply, φ.symm_apply_apply hxφ]

variable {A B : P.Level 1 → P.TangentSpace} {A' B' : Q.Level 1 → Q.TangentSpace}

/-- **2021 Lemma 4.5.1, p. 201 (new in the 2021 edition; proof left to the reader)**, for an
sc-smooth map `f : X → Y` of M-polyfolds (a local sc-diffeomorphism `X → X` in the text): if
`Tf ∘ A = A' ∘ f₁` and `Tf ∘ B = B' ∘ f₁` on `X¹`, then `Tf ∘ [A, B] = [A', B'] ∘ f₂` on `X²`. -/
theorem _root_.Polyfold.lemma_4_5_1 (hA : P.IsScVectorField A) (hB : P.IsScVectorField B)
    (hA' : Q.IsScVectorField A') (hB' : Q.IsScVectorField B')
    (hAA' : ∀ x, tangentMap hf (A x) = A' (liftLevelOneMap hf x))
    (hBB' : ∀ x, tangentMap hf (B x) = B' (liftLevelOneMap hf x)) (x : P.shift.Level 1) :
    tangentMap hf (lieBracket hA hB x) = lieBracket hA' hB' (levelTwoMap hf x) := by
  set x₁ := P.shift.levelVal 1 x with hx₁
  set b := P.levelVal 1 x₁ with hb
  obtain ⟨φ, hφ, hbφ⟩ := P.exists_isChart_mem_source b
  obtain ⟨ψ, hψ, hfbψ⟩ := Q.exists_isChart_mem_source (f b)
  set y₀ := liftLevelOneMap hf x₁ with hy₀
  have hb1 : b ∈ P.levelSet 1 := P.levelVal_mem x₁
  have hfb1 : f b ∈ Q.levelSet 1 := hf.mapsTo_levelSet 1 hb1
  -- both sides lie over `f(x)` in the chart `ψ`
  have hL : tangentMap hf (lieBracket hA hB x) ∈ tangentChartSet ψ := by
    change Q.levelVal 1 (Q.tangentProj (tangentMap hf _)) ∈ ψ.source
    rw [levelVal_tangentProj_tangentMap]; exact hfbψ
  have hR : lieBracket hA' hB' (levelTwoMap hf x) ∈ tangentChartSet ψ := hfbψ
  refine tangentChartMap_injOn hψ hL hR ?_
  -- the right side in `ψ`
  rw [tangentChartMap_lieBracket hA' hB' (levelTwoMap hf x) hψ hfbψ y₀]
  -- the left side, through `φ`
  have hαφ : lieBracket hA hB x ∈ tangentChartSet φ := hbφ
  rw [tangentChartMap_tangentMap hf hφ hψ hαφ hfbψ, tangentChartMap_lieBracket hA hB x hφ hbφ x₁]
  have hsφ := levelLift_levelChart_spec hφ x₁ x hbφ
  set z := levelLift (levelChart hφ x₁) 1 x₁ with hz_def
  rw [← hsφ.1]
  set s := TangentPre.fdom φ f ψ with hs
  have hso : IsOpen s := TangentPre.isOpen_fdom hf φ ψ
  obtain ⟨W, hW, hWeq⟩ := φ.exists_isOpen_image_eq (s := s) inter_subset_left hso
  have hov : φ '' s = (chartRetraction φ).retract ∩ W := by
    rw [chartRetraction_retract]; exact hWeq
  have hF : IsScSmoothRetractMap φ.model.E φ.model.C ((chartRetraction φ).retract ∩ W)
      ψ.model.E ψ.model.C (chartRetraction ψ).retract (ψ ∘ f ∘ φ.symm) := by
    rw [← hov, chartRetraction_retract]
    exact TangentPre.isScSmoothRetractMap_coord hf hφ hψ subset_rfl hso
  have hAφ := hA.isRetractVectorField_principalPart (hφ := hφ) (x₀ := x₁)
  have hBφ := hB.isRetractVectorField_principalPart (hφ := hφ) (x₀ := x₁)
  have hAψ := hA'.isRetractVectorField_principalPart (hφ := hψ) (x₀ := y₀)
  have hBψ := hB'.isRetractVectorField_principalPart (hφ := hψ) (x₀ := y₀)
  rw [← chartRetraction_retract φ] at hAφ hBφ
  rw [← chartRetraction_retract ψ] at hAψ hBψ
  -- the principal parts are related by `ψ ∘ f ∘ φ⁻¹`
  have hrel : ∀ (G : P.Level 1 → P.TangentSpace) (G' : Q.Level 1 → Q.TangentSpace),
      P.IsScVectorField G → Q.IsScVectorField G' →
      (∀ x, tangentMap hf (G x) = G' (liftLevelOneMap hf x)) →
      ∀ w ∈ φ.model.E.lvlSet ((chartRetraction φ).retract ∩ W) 1,
        retractTangentMap φ.model.E φ.model.C ((chartRetraction φ).retract ∩ W)
          (ψ ∘ f ∘ φ.symm) ((w, principalPart hφ x₁ G w) : φ.model.E.tangent 0) =
        ((levelMap (ψ ∘ f ∘ φ.symm) 1 w, principalPart hψ y₀ G'
          (levelMap (ψ ∘ f ∘ φ.symm) 1 w)) : ψ.model.E.tangent 0) := by
    intro G G' hG hG' hGG' w hw
    rw [← hov] at hw ⊢
    have hwO : φ.model.E.toBase 1 w ∈ φ.model.O := φ.image_subset_model inter_subset_left hw
    obtain ⟨u, hu, huw⟩ := hw
    set y := (levelChart hφ x₁).symm w with hy
    have hyv : P.levelVal 1 y = u := by
      rw [hy, levelChart_symm_apply hφ x₁ hwO, ← huw, φ.symm_apply_apply hu.1]
    have hyφ : P.levelVal 1 y ∈ φ.source := hyv ▸ hu.1
    have hfyψ : f (P.levelVal 1 y) ∈ ψ.source := hyv ▸ hu.2
    have hαφ' : G y ∈ tangentChartSet φ := by
      change P.levelVal 1 (P.tangentProj (G y)) ∈ φ.source
      rw [hG.2]; exact hyφ
    have hfα : f (P.levelVal 1 (P.tangentProj (G y))) ∈ ψ.source := by rw [hG.2]; exact hfyψ
    have h1 := tangentChartMap_tangentMap hf hφ hψ hαφ' hfα
    have hwy : levelChart hφ x₁ y = w := (levelChart hφ x₁).apply_symm_apply hwO
    rw [tangentChartMap_eq_principalPart hφ x₁ hG.2 hyφ, hwy, hGG' y,
      tangentChartMap_eq_principalPart hψ y₀ hG'.2
        (show Q.levelVal 1 (liftLevelOneMap hf y) ∈ ψ.source from hfyψ)] at h1
    have hlev : levelChart hψ y₀ (liftLevelOneMap hf y) = levelMap (ψ ∘ f ∘ φ.symm) 1 w := by
      rw [levelChart_apply, ← hwy, levelChart_apply]
      exact (levelMap_coord_levelLift hyφ hφ hψ hfyψ (P.levelVal_mem y)
        (hf.mapsTo_levelSet 1 (P.levelVal_mem y))).symm
    rw [hlev] at h1
    rw [hs]
    exact h1.symm
  have hz : z ∈ φ.model.E.shift.lvlSet
      (φ.model.E.lvlSet ((chartRetraction φ).retract ∩ W) 1) 1 := by
    rw [← hov]
    change φ.model.E.toBase 1 (φ.model.E.incl 1 z) ∈ φ '' s
    rw [hsφ.1, P.toBase_levelLift hφ hbφ hb1]
    exact ⟨b, ⟨hbφ, hfbψ⟩, rfl⟩
  have hnat := retractLieBracket_natural_inter hW hF hAφ hBφ hAψ hBψ
    (hrel A A' hA hA' hAA') (hrel B B' hB hB' hBB') hz
  rw [← hov] at hnat
  rw [show chartLieBracket hφ x₁ A B z = retractLieBracket (chartRetraction φ)
    (principalPart hφ x₁ A) (principalPart hφ x₁ B) z from rfl, hnat]
  -- the base points
  have h1 : levelMap (ψ ∘ f ∘ φ.symm) 1 (φ.model.E.incl 1 z) = levelLift ψ 1 (f b) := by
    rw [hsφ.1]; exact levelMap_coord_levelLift hbφ hφ hψ hfbψ hb1 hfb1
  refine Prod.ext h1 ?_
  change chartLieBracket hψ y₀ A' B' _ = chartLieBracket hψ y₀ A' B' _
  congr 1
  apply levelMap_eq_of_toBase_eq
  have hsψ : ψ.model.E.incl 1 (levelLift (levelChart hψ y₀) 1 y₀) = levelLift ψ 1 (f b) :=
    (levelLift_levelChart_spec hψ y₀ (levelTwoMap hf x) hfbψ).1
  change ψ.model.E.incl 1 (levelLift (levelChart hψ y₀) 1 y₀) = _
  rw [hsψ]
  exact h1.symm

end Naturality

/-! ### Raising the index of a vector field (Lemma 4.4.4) -/

section RaiseIndex

variable {A : P.Level 1 → P.TangentSpace}

/-- The level-`1` map `A₁ : (X¹)¹ → (TX)¹` of a vector field. -/
def vectorFieldLevelOne (hA : P.IsScVectorField A) (x : P.shift.Level 1) :
    P.tangentPolyfold.Level 1 :=
  P.tangentPolyfold.levelMk 1 (A (P.shift.levelVal 1 x))
    (hA.1.mapsTo_levelSet 1 (P.shift.levelVal_mem x))

/-- `A^(1) = Φ⁻¹ ∘ A₁ : X² → T(X¹)`, the vector field `A` with the index raised by one, through
the identification `Φ : T(X¹) ≡ (TX)¹` of Proposition 2.3.17. -/
def raiseIndex (hA : P.IsScVectorField A) (x : P.shift.Level 1) : P.shift.TangentSpace :=
  tangentShiftEquiv.symm (vectorFieldLevelOne hA x)

/-- **2021 Lemma 4.4.4, p. 196 (new in the 2021 edition)**, `i = 1` (larger `i` by iterating:
`A^(1)` is again an sc-smooth vector field, of `X¹`): `A^(1)` is an sc-smooth vector field on
`X¹`, i.e. an sc-smooth section of `T(X¹) → X²`, and it is `A` on `X²`: `Φ(A^(1)(x)) = A(x)`
(as an element of `(TX)¹`). -/
theorem _root_.Polyfold.lemma_4_4_4 (hA : P.IsScVectorField A) :
    P.shift.IsScVectorField (raiseIndex hA) ∧
      ∀ x, P.tangentPolyfold.levelVal 1 (tangentShiftEquiv (raiseIndex hA x)) =
        A (P.shift.levelVal 1 x) := by
  have h1 : P.shift.shift.IsScSmoothMap P.tangentPolyfold.shift (vectorFieldLevelOne hA) :=
    IsScSmoothMap.levelOne hA.1 fun _ => rfl
  refine ⟨⟨IsScSmoothMap.comp tangentShiftEquiv_symm_isScSmooth h1, fun x => ?_⟩, fun x => ?_⟩
  · have h := tangentProjShift_tangentShiftMap (tangentShiftEquiv.symm (vectorFieldLevelOne hA x))
    rw [tangentShiftMap_symm] at h
    rw [raiseIndex, ← h]
    apply level_ext
    exact hA.2 (P.shift.levelVal 1 x)
  · rw [raiseIndex, Equiv.apply_symm_apply]
    rfl

end RaiseIndex

end MPolyfold

end Polyfold
