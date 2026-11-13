import Polyfold.Chapter4.BoundaryForms2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.4, pp. 198–199
(2017 p. 150; preprint p. 168): forms on `∂X`, "which coincide on the intersection of local faces".

# Agreement of `τ` over a map gives agreement of `dτ`: the general argument

`BoundaryForms2021` reads a form on `∂X` as an sc-form `τ` on the tame boundary `bX` that agrees
over `B : bX → X`, and puts the agreement of `dτ` into the definition.  This file proves the
general statement from which the second condition follows from the first; the companion file
`A3BoundaryForms2021b` supplies its two hypotheses for `B`.

## The argument

Let `f : X → Y` be sc-smooth and `τ` an sc-form on `X` agreeing over `f`.

* (`formPullback_eq_of_isAgreeingOver`, `formPullback_extD_eq_of_isAgreeingOver`)  If
  `g, g' : Z → X` are sc-smooth with `f ∘ g = f ∘ g'`, then `g^*τ = g'^*τ` (this is the
  agreement), hence `(g¹)^*dτ = d(g^*τ) = d(g'^*τ) = (g'¹)^*dτ` by the naturality of `d`
  (`extD_formPullback`).  So `dτ` takes the same value on `(Tg v₀, …, Tg v_k)` and on
  `(Tg' v₀, …, Tg' v_k)`.
* So `dτ` agrees over `f¹` as soon as every pair of tuples of tangent vectors with the same image
  under `Tf` has this form.  Two hypotheses on `f` give that, on every level:
  `IsTangentInjective f` (`Tf` is injective on every tangent space; for base points `p = p'`), and
  `HasCornerCover f` (for `p ≠ p'` with `f(p) = f(p')` there are `Z`, `g`, `g'` with
  `f ∘ g = f ∘ g'` and a point `z` with `g(z) = p`, `g'(z) = p'`, such that all pairs
  `(a, a') ∈ T_pX × T_{p'}X` with `Tf a = Tf a'` are `(Tg v, Tg' v)`, level by level).
* (`isAgreeingOver_extD`)  Both hypotheses are stated on `X` itself; the statement on `Xⁱ` is
  obtained through the inclusions `Xⁱ → X`, `T(Xⁱ) → TX` (`incl`, `tangentIncl`), which are
  injective, natural, and onto the points of level `i` (`exists_incl_eq`,
  `exists_tangentIncl_eq`).

For `B : bX → X` (file `A3BoundaryForms2021b`), `Z` is a relatively open neighbourhood of the
point in the partial quadrant of a tame chart, and `g`, `g'` are the lifts to the two local faces
of `r ∘ P_i ∘ P_j`, the retraction `r` after the projection onto `{λ_i = λ_j = 0}`; its image is
the intersection of the two faces near the point.
-/

open Set Function

noncomputable section

namespace Polyfold

namespace MPolyfold

section Square

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}
  {f : X → Y} {g g' : Z → X} {k : ℕ}

/-- `Tf ∘ Tg = Tf ∘ Tg'` when `f ∘ g = f ∘ g'`. -/
theorem tangentMap_tangentMap_eq_of_comp_eq (hf : P.IsScSmoothMap Q f) (hg : S.IsScSmoothMap P g)
    (hg' : S.IsScSmoothMap P g') (hfg : ∀ z, f (g z) = f (g' z)) (v : S.TangentSpace) :
    tangentMap hf (tangentMap hg v) = tangentMap hf (tangentMap hg' v) := by
  have h1 := congrFun (tangentMap_comp hf hg) v
  have h2 := congrFun (tangentMap_comp hf hg') v
  have h3 : ∀ (h h' : Z → Y) (e : h = h') (a : S.IsScSmoothMap Q h) (b : S.IsScSmoothMap Q h'),
      tangentMap a v = tangentMap b v := by
    rintro h _ rfl a b; rfl
  exact h1.symm.trans ((h3 _ _ (funext hfg) _ _).trans h2)

/-- **If `τ` agrees over `f` and `f ∘ g = f ∘ g'`, then `g^*τ = g'^*τ`.** -/
theorem formPullback_eq_of_isAgreeingOver (hf : P.IsScSmoothMap Q f) (hg : S.IsScSmoothMap P g)
    (hg' : S.IsScSmoothMap P g') (hfg : ∀ z, f (g z) = f (g' z))
    {τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} (hτ : IsAgreeingOver hf τ) :
    formPullback hg τ = formPullback hg' τ := by
  funext z
  ext v
  rw [formPullback_apply, formPullback_apply]
  refine hτ (show f (P.levelVal 1 (liftLevelOneMap hg z)) =
    f (P.levelVal 1 (liftLevelOneMap hg' z)) from hfg _) _ _ fun j => ?_
  rw [coe_tangentFiberMap_apply, coe_tangentFiberMap_apply]
  exact tangentMap_tangentMap_eq_of_comp_eq hf hg hg' hfg _

/-- **If the sc-form `τ` agrees over `f` and `f ∘ g = f ∘ g'`, then `(g¹)^*dτ = (g'¹)^*dτ`**: by
the naturality of `d`, both are `d` of `g^*τ = g'^*τ`. -/
theorem formPullback_extD_eq_of_isAgreeingOver (hf : P.IsScSmoothMap Q f)
    (hg : S.IsScSmoothMap P g) (hg' : S.IsScSmoothMap P g') (hfg : ∀ z, f (g z) = f (g' z))
    {τ : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin k]→ₗ[ℝ] ℝ} (hτs : τ ∈ P.scForms k)
    (hτ : IsAgreeingOver hf τ) :
    formPullback (isScSmoothMap_liftLevelOneMap hg) (extD τ) =
      formPullback (isScSmoothMap_liftLevelOneMap hg') (extD τ) := by
  rw [← extD_formPullback hg hτs, ← extD_formPullback hg' hτs,
    formPullback_eq_of_isAgreeingOver hf hg hg' hfg hτ]

end Square

end MPolyfold

namespace BundledMPolyfold

open MPolyfold

universe u v w

variable (A : BundledMPolyfold.{u})

/-! ### The inclusions `Xⁱ → X` and `T(Xⁱ) → TX` and the levels -/

/-- The points of `Xⁱ` on level `m` are the points of `X` on level `i + m`. -/
theorem incl_mem_levelSet_iff : ∀ (i m : ℕ) (y : (A.lift i).carrier),
    A.incl i y ∈ A.P.levelSet (i + m) ↔ y ∈ (A.lift i).P.levelSet m
  | 0, m, y => by rw [Nat.zero_add]; rfl
  | i + 1, m, y => by
    have h := incl_mem_levelSet_iff i (m + 1) ((A.lift i).P.levelVal 1 y)
    have e : i + 1 + m = i + (m + 1) := by omega
    rw [e]
    exact h.trans (mem_shift_levelSet_iff (PX := (A.lift i).P) y).symm

/-- The image of `Xⁱ → X` lies in `X_i`. -/
theorem incl_mem_levelSet (i : ℕ) (y : (A.lift i).carrier) : A.incl i y ∈ A.P.levelSet i := by
  have := (A.incl_mem_levelSet_iff i 0 y).2 (by rw [levelSet_zero]; exact mem_univ _)
  simpa using this

/-- Every point of `X_i` is the image of a point of `Xⁱ`. -/
theorem exists_incl_eq : ∀ (i : ℕ) {x : A.carrier}, x ∈ A.P.levelSet i →
    ∃ y : (A.lift i).carrier, A.incl i y = x
  | 0, x, _ => ⟨x, rfl⟩
  | i + 1, x, hx => by
    obtain ⟨y, rfl⟩ := exists_incl_eq i (A.P.levelSet_succ_subset i hx)
    exact ⟨(A.lift i).P.levelMk 1 y ((A.incl_mem_levelSet_iff i 1 y).1 hx), rfl⟩

/-- `T(Xⁱ) → TX` is injective. -/
theorem tangentIncl_injective (i : ℕ) : Injective (A.tangentIncl i) := fun α β h => by
  apply (A.tangentLiftEquiv i).toEquiv.injective
  apply A.tangent.incl_injective i
  exact (A.incl_tangentLiftEquiv i α).trans (h.trans (A.incl_tangentLiftEquiv i β).symm)

/-- The image of `T(Xⁱ) → TX` lies in `(TX)_i`. -/
theorem tangentIncl_mem_levelSet (i : ℕ) (α : (A.lift i).tangent.carrier) :
    A.tangentIncl i α ∈ A.P.tangentPolyfold.levelSet i := by
  rw [← A.incl_tangentLiftEquiv i α]
  exact A.tangent.incl_mem_levelSet i _

/-- Every vector of `(TX)_i` is the image of a vector of `T(Xⁱ)`. -/
theorem exists_tangentIncl_eq (i : ℕ) {a : A.P.TangentSpace}
    (ha : a ∈ A.P.tangentPolyfold.levelSet i) :
    ∃ α : (A.lift i).tangent.carrier, A.tangentIncl i α = a := by
  obtain ⟨y, rfl⟩ := A.tangent.exists_incl_eq i ha
  refine ⟨(A.tangentLiftEquiv i).toEquiv.symm y, ?_⟩
  rw [← A.incl_tangentLiftEquiv i]
  exact congrArg (A.tangent.incl i) ((A.tangentLiftEquiv i).toEquiv.apply_symm_apply y)

/-- The base point of the image of `α ∈ T(Xⁱ)` in `TX` is the image of the base point. -/
theorem levelVal_tangentProj_tangentIncl : ∀ (i : ℕ) (α : (A.lift i).tangent.carrier),
    A.P.levelVal 1 (A.P.tangentProj (A.tangentIncl i α)) =
      A.incl (i + 1) ((A.lift i).P.tangentProj α)
  | 0, _ => rfl
  | i + 1, α => by
    have h := levelVal_tangentProj_tangentIncl i (tangentLower (P := (A.lift i).P) α)
    have h2 := tangentProj_tangentLower (P := (A.lift i).P) α
    exact h.trans (congrArg (A.incl (i + 1)) h2)

variable {A} {B : BundledMPolyfold.{v}}

/-- Two bundled sc-smooth maps with the same underlying map are equal. -/
theorem scMap_ext {P : MPolyfold A.carrier} {Q : MPolyfold B.carrier} {f g : ScMap P Q}
    (h : ∀ x, f x = g x) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  obtain rfl : f = g := funext h
  rfl

/-! ### The two hypotheses -/

/-- **`Tf` is injective on every tangent space** `T_xX`, `x ∈ X_1`. -/
def IsTangentInjective (f : ScMap A.P B.P) : Prop :=
  ∀ a a' : A.P.TangentSpace, A.P.tangentProj a = A.P.tangentProj a' →
    MPolyfold.tangentMap f.isScSmoothMap a = MPolyfold.tangentMap f.isScSmoothMap a' → a = a'

/-- **Pairs of points with the same image are covered by squares**: for `p ≠ p'` with
`f(p) = f(p')` there are an M-polyfold `Z`, sc-smooth `g, g' : Z → X` with `f ∘ g = f ∘ g'` and
`z ∈ Z` with `g(z) = p`, `g'(z) = p'`, on the level of `p`, such that every pair
`(a, a') ∈ T_pX × T_{p'}X` with `Tf a = Tf a'` is `(Tg v, Tg' v)` for a `v ∈ T_zZ` on the level of
`a`. -/
def HasCornerCover (f : ScMap A.P B.P) : Prop :=
  ∀ p p' : A.carrier, p ≠ p' → f p = f p' →
    ∃ (Z : BundledMPolyfold.{w}) (g g' : ScMap Z.P A.P) (z : Z.carrier),
      (∀ y, f (g y) = f (g' y)) ∧ g z = p ∧ g' z = p' ∧
      (∀ m, p ∈ A.P.levelSet m → z ∈ Z.P.levelSet m) ∧
      ∀ (m : ℕ) (a a' : A.P.TangentSpace), a ∈ A.P.tangentPolyfold.levelSet m →
        A.P.levelVal 1 (A.P.tangentProj a) = p → A.P.levelVal 1 (A.P.tangentProj a') = p' →
        MPolyfold.tangentMap f.isScSmoothMap a = MPolyfold.tangentMap f.isScSmoothMap a' →
        ∃ v : Z.P.TangentSpace, v ∈ Z.P.tangentPolyfold.levelSet m ∧
          Z.P.levelVal 1 (Z.P.tangentProj v) = z ∧
          MPolyfold.tangentMap g.isScSmoothMap v = a ∧ MPolyfold.tangentMap g'.isScSmoothMap v = a'

variable {f : ScMap A.P B.P} {k : ℕ}

/-- On every `Xⁱ`, `T(fⁱ)` is injective on the tangent spaces. -/
theorem IsTangentInjective.lift (hf : IsTangentInjective f) (i : ℕ)
    {α α' : (A.lift i).P.TangentSpace}
    (hp : (A.lift i).P.tangentProj α = (A.lift i).P.tangentProj α')
    (h : MPolyfold.tangentMap (A.liftMap f i).isScSmoothMap α =
      MPolyfold.tangentMap (A.liftMap f i).isScSmoothMap α') : α = α' := by
  apply A.tangentIncl_injective i
  refine hf _ _ (level_ext ?_) ?_
  · exact (A.levelVal_tangentProj_tangentIncl i α).trans
      ((congrArg (A.incl (i + 1)) hp).trans (A.levelVal_tangentProj_tangentIncl i α').symm)
  · exact (tangentIncl_tangentMap f i α).symm.trans
      ((congrArg (B.tangentIncl i) h).trans (tangentIncl_tangentMap f i α'))

/-- The lifted square: `fⁱ ∘ gⁱ = fⁱ ∘ g'ⁱ`. -/
theorem liftMap_liftMap_eq_of_comp_eq {Z : BundledMPolyfold.{w}} {g g' : ScMap Z.P A.P}
    (hfg : ∀ y, f (g y) = f (g' y)) (i : ℕ) (y : (Z.lift i).carrier) :
    A.liftMap f i (Z.liftMap g i y) = A.liftMap f i (Z.liftMap g' i y) := by
  rw [← liftMap_comp_apply f g i y, ← liftMap_comp_apply f g' i y]
  have e : f.comp g = f.comp g' := scMap_ext hfg
  rw [e]

/-- The value of `dτ` on the images of a tuple of vectors of `T(Zⁱ⁺¹)` under `T(gⁱ⁺¹)` and
`T(g'ⁱ⁺¹)` is the same. -/
theorem extD_apply_eq_of_square {Z : BundledMPolyfold.{w}} {g g' : ScMap Z.P A.P}
    (hfg : ∀ y, f (g y) = f (g' y)) (i : ℕ) (τ : A.forms k i)
    (hτ : IsAgreeingOver (A.liftMap f i).isScSmoothMap τ.1)
    {z : (Z.lift (i + 1)).P.Level 1} {x x' : (A.lift (i + 1)).P.Level 1}
    (hx : Z.liftMap g (i + 1) ((Z.lift (i + 1)).P.levelVal 1 z) = (A.lift (i + 1)).P.levelVal 1 x)
    (hx' : Z.liftMap g' (i + 1) ((Z.lift (i + 1)).P.levelVal 1 z) =
      (A.lift (i + 1)).P.levelVal 1 x')
    (ν : Fin (k + 1) → (Z.lift (i + 1)).P.tangentFiber z)
    (α : Fin (k + 1) → (A.lift (i + 1)).P.tangentFiber x)
    (α' : Fin (k + 1) → (A.lift (i + 1)).P.tangentFiber x')
    (hα : ∀ j, MPolyfold.tangentMap (Z.liftMap g (i + 1)).isScSmoothMap (ν j).1 = (α j).1)
    (hα' : ∀ j, MPolyfold.tangentMap (Z.liftMap g' (i + 1)).isScSmoothMap (ν j).1 = (α' j).1) :
    extD τ.1 x α = extD τ.1 x' α' := by
  have key := formPullback_extD_eq_of_isAgreeingOver (A.liftMap f i).isScSmoothMap
    (Z.liftMap g i).isScSmoothMap (Z.liftMap g' i).isScSmoothMap
    (liftMap_liftMap_eq_of_comp_eq hfg i) τ.2 hτ
  have h1 := formPullback_eq (isScSmoothMap_liftLevelOneMap (Z.liftMap g i).isScSmoothMap)
    (extD τ.1) ν hx α hα
  have h2 := formPullback_eq (isScSmoothMap_liftLevelOneMap (Z.liftMap g' i).isScSmoothMap)
    (extD τ.1) ν hx' α' hα'
  rw [← h1, ← h2, key]

/-- **Agreement of `τ` gives agreement of `dτ`**: let `f : X → Y` be sc-smooth with `Tf` injective
on the tangent spaces and with the pairs of points over a common image covered by squares
(`HasCornerCover`).  If the sc-form `τ` on `Xⁱ` agrees over `fⁱ`, then `dτ` agrees over
`fⁱ⁺¹`. -/
theorem isAgreeingOver_extD (hinj : IsTangentInjective f) (hcov : HasCornerCover.{u, v, w} f)
    (i : ℕ) (τ : A.forms k i) (hτ : IsAgreeingOver (A.liftMap f i).isScSmoothMap τ.1) :
    IsAgreeingOver (A.liftMap f (i + 1)).isScSmoothMap (extD τ.1) := by
  intro x x' hxx α α' hα
  -- the base points in `X`
  set p := A.incl (i + 1) ((A.lift (i + 1)).P.levelVal 1 x) with hp
  set p' := A.incl (i + 1) ((A.lift (i + 1)).P.levelVal 1 x') with hp'
  have hfp : f p = f p' := by
    rw [hp, hp', ← A.incl_liftMap f (i + 1), ← A.incl_liftMap f (i + 1), hxx]
  by_cases hpp : p = p'
  · -- the same base point: the vectors coincide
    obtain rfl : x = x' := level_ext (A.incl_injective (i + 1) hpp)
    have : α = α' := funext fun j => Subtype.ext
      (hinj.lift (i + 1) ((α j).2.trans (α' j).2.symm) (hα j))
    rw [this]
  · obtain ⟨Z, g, g', z, hfg, hgz, hgz', hlev, hvec⟩ := hcov p p' hpp hfp
    -- the point of `Zⁱ⁺¹` on level one over `z`
    have hpl : p ∈ A.P.levelSet (i + 1 + 1) :=
      (A.incl_mem_levelSet_iff (i + 1) 1 _).2 (levelVal_mem x)
    obtain ⟨y, hy⟩ := Z.exists_incl_eq (i + 1) (Z.P.levelSet_antitone (Nat.le_succ _) (hlev _ hpl))
    have hy1 : y ∈ (Z.lift (i + 1)).P.levelSet 1 :=
      (Z.incl_mem_levelSet_iff (i + 1) 1 y).1 (hy ▸ hlev _ hpl)
    set z₁ : (Z.lift (i + 1)).P.Level 1 := (Z.lift (i + 1)).P.levelMk 1 y hy1 with hz₁
    have hgy : Z.liftMap g (i + 1) y = (A.lift (i + 1)).P.levelVal 1 x := by
      apply A.incl_injective (i + 1)
      rw [Z.incl_liftMap g (i + 1) y, hy, hgz]
    have hgy' : Z.liftMap g' (i + 1) y = (A.lift (i + 1)).P.levelVal 1 x' := by
      apply A.incl_injective (i + 1)
      rw [Z.incl_liftMap g' (i + 1) y, hy, hgz']
    -- the vectors
    have hex : ∀ j, ∃ ν : (Z.lift (i + 1)).P.tangentFiber z₁,
        MPolyfold.tangentMap (Z.liftMap g (i + 1)).isScSmoothMap ν.1 = (α j).1 ∧
          MPolyfold.tangentMap (Z.liftMap g' (i + 1)).isScSmoothMap ν.1 = (α' j).1 := by
      intro j
      have hb : A.P.levelVal 1 (A.P.tangentProj (A.tangentIncl (i + 1) (α j).1)) = p :=
        (A.levelVal_tangentProj_tangentIncl (i + 1) (α j).1).trans
          (congrArg (A.incl (i + 1 + 1)) (α j).2)
      have hb' : A.P.levelVal 1 (A.P.tangentProj (A.tangentIncl (i + 1) (α' j).1)) = p' :=
        (A.levelVal_tangentProj_tangentIncl (i + 1) (α' j).1).trans
          (congrArg (A.incl (i + 1 + 1)) (α' j).2)
      have hT : MPolyfold.tangentMap f.isScSmoothMap (A.tangentIncl (i + 1) (α j).1) =
          MPolyfold.tangentMap f.isScSmoothMap (A.tangentIncl (i + 1) (α' j).1) :=
        (tangentIncl_tangentMap f (i + 1) (α j).1).symm.trans
          ((congrArg (B.tangentIncl (i + 1)) (hα j)).trans
            (tangentIncl_tangentMap f (i + 1) (α' j).1))
      obtain ⟨v, hvl, hvz, hv, hv'⟩ := hvec (i + 1) _ _
        (A.tangentIncl_mem_levelSet (i + 1) (α j).1) hb hb' hT
      obtain ⟨ν, rfl⟩ := Z.exists_tangentIncl_eq (i + 1) hvl
      have hν : (Z.lift (i + 1)).P.tangentProj ν = z₁ := by
        apply level_ext
        apply Z.incl_injective (i + 1)
        have := Z.levelVal_tangentProj_tangentIncl (i + 1) ν
        exact this.symm.trans (hvz.trans hy.symm)
      refine ⟨⟨ν, hν⟩, ?_, ?_⟩
      · exact A.tangentIncl_injective (i + 1) ((tangentIncl_tangentMap g (i + 1) ν).trans hv)
      · exact A.tangentIncl_injective (i + 1) ((tangentIncl_tangentMap g' (i + 1) ν).trans hv')
    choose ν hν hν' using hex
    exact extD_apply_eq_of_square hfg i τ hτ (z := z₁) hgy hgy' ν α α' hν hν'

/-- **The two definitions coincide**: under the hypotheses of `isAgreeingOver_extD`, the forms `τ`
on `Xⁱ` such that `τ` and `dτ` agree over `f` are all the forms agreeing over `f`. -/
theorem agreeDForms_eq_agreeForms (hinj : IsTangentInjective f)
    (hcov : HasCornerCover.{u, v, w} f) (k i : ℕ) : agreeDForms f k i = agreeForms f k i :=
  le_antisymm inf_le_left fun τ hτ => ⟨hτ, isAgreeingOver_extD hinj hcov i τ hτ⟩

end BundledMPolyfold

end Polyfold
