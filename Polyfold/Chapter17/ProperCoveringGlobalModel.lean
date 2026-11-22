import Polyfold.Chapter17.ProperCoveringPolyfold
import Polyfold.Chapter17.ModelEquivalence

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8:
the **sc-smooth model `τ̂ : E → X` of a proper polyfold covering functor and the equivalences
`Γ̂`, `Γ` of (17.104)** (p. 838), for a family of proper covering uniformizers (Definitions
17.8.10, 17.8.12, 17.8.13, pp. 834–836) whose base uniformizers cover `|B|`.  Numbers and pages
are the 2021 text's.

# The global model (17.104)

## The text, paraphrased

(p. 838) For a proper polyfold covering functor `P : A → B` and a covering family of
uniformizers `(Ψ̂_λ, Ψ_λ)_{λ ∈ Λ}` (the `Ψ_λ` cover `B`), with the coverings
`τ̂_λ : E_λ → G_λ ⋉ O_λ`, put `E = ⊔ E_λ`, `X = ⊔ O_λ`, `τ̂(e_λ) = τ̂_λ(e_λ)` (a surjective local
sc-diffeomorphism), `𝐄 = ⊔_{(λ, λ')} M(Ψ̂_λ, Ψ̂_λ')` and `𝐗 = ⊔_{(λ, λ')} M(Ψ_λ, Ψ_λ')`.  "As
previously seen" `E ≡ (E, 𝐄)` and `X ≡ (X, 𝐗)` are ep-groupoids, and `τ̂` extends to a proper
covering functor `E → X`.  It comes with a natural pair of equivalences `Γ̂ : E → A`,
`Γ : X → B` with `P ∘ Γ̂ = Γ ∘ τ̂` (17.104).  The details are left to the reader.

## What is formalized (namespace `Polyfold.ProperPolyfoldCoveringStructure`)

For a proper polyfold covering structure `S` (Definition 17.8.13) of `P` and any family
`Uf : ι → S.toC.Unif`:

* `HatTr U U'` (the transition M-polyfold `M(Ψ̂, Ψ̂')` of `S`), with its structure maps
  (`isLocalScDiffeo_hatSrc`, `isLocalScDiffeo_hatTgt`, `isScSmoothMap_hatUnit`,
  `isScSmoothMap_hatInv`, `isScSmoothMap_hatMul`).
* The groupoid `hatGroupoid Uf` on `HatObj Uf = Σ λ, E_λ` with morphisms
  `HatMor Uf = Σ (λ, λ'), M(Ψ̂_λ, Ψ̂_λ')` (the pullback of `A` along `e_λ ↦ Ψ̂_λ(e_λ)`), the
  M-polyfolds `hatObjPolyfold`, `hatMorPolyfold`, and the structure maps
  (`isLocalScDiffeo_hatModelSrc`, `isLocalScDiffeo_hatModelTgt`, `isScSmoothMap_hatModelUnit`,
  `isScSmoothMap_hatModelInv`, `isScSmoothComp_hatModel`).
* The properness: `exists_isProperMap_hatTr` (the analogue of Proposition 17.1.11 for the `Ψ̂`,
  from Proposition 17.1.11 for `M(Ψ, Ψ')`, a sheet of `τ̂` and Proposition 17.8.15) and
  `exists_isProperMap_hatModel`.
* **`hatEpGroupoid Uf hPc`, `hatEP`: `E ≡ (E, 𝐄)` is an ep-groupoid.**
* `baseEP Uf` (`X`, the model of Theorem 17.1.14 for `λ ↦ Ψ_λ`), **`hatModelFunctor`
  (`τ̂ : E → X`, an sc-smooth functor)**, **`hatFunctor` (`Γ̂ : E → A`)**, `baseFunctor`
  (`Γ = Γ_Ψ` of (17.10)); **the square (17.104)**: `square_obj`, `square_mor`.
* **`Γ̂` is an equivalence**: `hatFunctor_full`, `hatFunctor_faithful` (every family),
  `hatFunctor_essSurj`, `hatFunctor_isEquivalence` (when the `Ψ_λ` cover `|B|`); **`|Γ̂|` is a
  homeomorphism**: `continuous_hatOrbitMap`, `isOpenMap_hatOrbitMap`,
  `isHomeomorph_hatOrbitMap`.  For `Γ` these are Lemma 17.1.15
  (`lemma_17_1_15_of_isCovering`).
* Witness: `z3HatModel_nondegenerate`, for the two sheets of `ℤ/3 ⋉ ℝ` over `ℤ/3 ⋉ ℝ`
  (`z3PolyfoldCoveringFunctor`) and the one-element family at `0`: both equivalences and
  homeomorphisms, an object of `E` with a non-unit automorphism, and a fibre of `τ̂` with two
  points.

## Readings

* "Natural pair of equivalences" is read as for `Γ_Ψ` in Lemma 17.1.15: functors that are
  equivalences of categories (Mathlib's `Functor.IsEquivalence` of the underlying functors) with
  `|Γ̂|`, `|Γ|` homeomorphisms.  `A` and `B` carry no M-polyfold structure, so `Γ̂` and `Γ` are
  functors of groupoids; `τ̂` is an sc-smooth functor of ep-groupoids.
* "As previously seen `E` is an ep-groupoid": Definition 17.8.13 gives the M-polyfold structures
  and the structure maps of the `M(Ψ̂, Ψ̂')`; the properness of `E` is proved from that of the
  `M(Ψ, Ψ')` (Proposition 17.1.11) through Proposition 17.8.15, which uses that `P` is a proper
  covering functor (`hPc`).
* The covering condition is used only for the essential surjectivity of `Γ̂` and the
  homeomorphisms; the ep-groupoid and the functors are built for any family.
-/

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace ProperPolyfoldCoveringStructure

open ProperCoveringUniformizer ProperCoveringUniformizerConstruction GCT GCT.PolyfoldConstruction

variable {A B : GCT.{u}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
  (S : ProperPolyfoldCoveringStructure P)

/-- The transition set `M(Ψ̂, Ψ̂')` with the M-polyfold structure of `S`. -/
def HatTr (U U' : S.toC.Unif) : Type u := HatTrans U.unif U'.unif

instance (U U' : S.toC.Unif) : TopologicalSpace (S.HatTr U U') := S.topH U U'
instance (U U' : S.toC.Unif) : T2Space (S.HatTr U U') := S.t2H U U'
instance (U U' : S.toC.Unif) : ParacompactSpace (S.HatTr U U') := S.paraH U U'

/-- The M-polyfold `M(Ψ̂, Ψ̂')`. -/
def hatTransPolyfold (U U' : S.toC.Unif) : MPolyfold (S.HatTr U U') := S.MH U U'

/-- An element of `M(Ψ̂, Ψ̂')` as an element of the transition M-polyfold. -/
abbrev toHatTr {U U' : S.toC.Unif} (a : HatTrans U.unif U'.unif) : S.HatTr U U' := a

/-- Definition 17.8.13 (a): `s : M(Ψ̂, Ψ̂') → E` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_hatSrc (U U' : S.toC.Unif) :
    (S.hatTransPolyfold U U').IsLocalScDiffeo U.unif.E.PObj fun a : S.HatTr U U' => a.src :=
  S.isLocalScDiffeo_src U U'

/-- Definition 17.8.13 (a): `t : M(Ψ̂, Ψ̂') → E'` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_hatTgt (U U' : S.toC.Unif) :
    (S.hatTransPolyfold U U').IsLocalScDiffeo U'.unif.E.PObj fun a : S.HatTr U U' => a.tgt :=
  S.isLocalScDiffeo_tgt U U'

theorem continuous_hatSrc (U U' : S.toC.Unif) : Continuous fun a : S.HatTr U U' => a.src :=
  (S.isLocalScDiffeo_hatSrc U U').continuous

theorem continuous_hatTgt (U U' : S.toC.Unif) : Continuous fun a : S.HatTr U U' => a.tgt :=
  (S.isLocalScDiffeo_hatTgt U U').continuous

/-- Definition 17.8.13 (b): the unit map `E → M(Ψ̂, Ψ̂)` is sc-smooth. -/
theorem isScSmoothMap_hatUnit (U : S.toC.Unif) :
    U.unif.E.PObj.IsScSmoothMap (S.hatTransPolyfold U U)
      fun e => S.toHatTr (GroupoidStr.TransitionSet.unit e) :=
  S.isScSmoothMap_unit U

/-- Definition 17.8.13 (b): the inversion is sc-smooth. -/
theorem isScSmoothMap_hatInv (U U' : S.toC.Unif) :
    (S.hatTransPolyfold U U').IsScSmoothMap (S.hatTransPolyfold U' U)
      fun a : S.HatTr U U' => S.toHatTr (GroupoidStr.TransitionSet.inv a) :=
  S.isScSmoothMap_inv U U'

/-- Definition 17.8.13 (c): the multiplication is sc-smooth. -/
theorem isScSmoothMap_hatMul (U U' U'' : S.toC.Unif) :
    MPolyfold.IsScSmoothOnFibredProduct (S.hatTransPolyfold U' U'') (S.hatTransPolyfold U U')
      (S.hatTransPolyfold U U'') (S.isLocalScDiffeo_hatSrc U' U'')
      (S.isLocalScDiffeo_hatTgt U U').isScSmoothMap
      fun p => S.toHatTr (GroupoidStr.TransitionSet.mul p) :=
  S.isScSmoothMap_mul U U' U''

/-! ### The ep-groupoid `𝐄 = ⊔ M(Ψ̂_λ, Ψ̂_λ')` -/

variable {ι : Type u} (Uf : ι → S.toC.Unif)

/-- The object M-polyfold `E = ⊔_λ E_λ` of (17.104). -/
abbrev HatObj : Type u := Σ i, (Uf i).unif.ObjE

/-- The morphism M-polyfold `𝐄 = ⊔_{(λ, λ')} M(Ψ̂_λ, Ψ̂_λ')` of (17.104). -/
abbrev HatMor : Type u := Σ p : ι × ι, S.HatTr (Uf p.1) (Uf p.2)

/-- `e_λ ↦ Ψ̂_λ(e_λ)`. -/
def hatObjMap (x : S.HatObj Uf) : A.Obj := (Uf x.1).unif.hat.obj x.2

/-- `𝐄` is the transition set of `E → A ← E`. -/
def hatMorEquiv :
    S.HatMor Uf ≃ A.toGroupoidStr.TransitionSet (S.hatObjMap Uf) (S.hatObjMap Uf) where
  toFun φ := ⟨⟨φ.1.1, φ.2.src⟩, φ.2.mor, ⟨φ.1.2, φ.2.tgt⟩, φ.2.src_mor, φ.2.tgt_mor⟩
  invFun b := ⟨(b.src.1, b.tgt.1), ⟨b.src.2, b.mor, b.tgt.2, b.src_mor, b.tgt_mor⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The groupoid `(E, 𝐄)`** of (17.104): `s(e, φ, e') = e`, `t(e, φ, e') = e'`, and the
composition of `A`. -/
def hatGroupoid : GroupoidStr (S.HatObj Uf) (S.HatMor Uf) :=
  (A.toGroupoidStr.pullback (S.hatObjMap Uf)).ofEquiv (S.hatMorEquiv Uf)

variable {S Uf}

@[simp] theorem hatGroupoid_src (φ : S.HatMor Uf) :
    (S.hatGroupoid Uf).src φ = ⟨φ.1.1, φ.2.src⟩ := rfl

@[simp] theorem hatGroupoid_tgt (φ : S.HatMor Uf) :
    (S.hatGroupoid Uf).tgt φ = ⟨φ.1.2, φ.2.tgt⟩ := rfl

@[simp] theorem hatGroupoid_unit (x : S.HatObj Uf) :
    (S.hatGroupoid Uf).unit x = ⟨(x.1, x.1), GroupoidStr.TransitionSet.unit x.2⟩ := rfl

@[simp] theorem hatGroupoid_inv (φ : S.HatMor Uf) :
    (S.hatGroupoid Uf).inv φ = ⟨(φ.1.2, φ.1.1), GroupoidStr.TransitionSet.inv φ.2⟩ := rfl

/-- The composition of `(E, 𝐄)` on morphisms with composable morphisms of `A`. -/
theorem hatGroupoid_comp_of {i j j' k : ι} (a : S.HatTr (Uf j') (Uf k))
    (b : S.HatTr (Uf i) (Uf j)) (h : A.toGroupoidStr.src a.mor = A.toGroupoidStr.tgt b.mor) :
    (S.hatGroupoid Uf).comp ⟨(j', k), a⟩ ⟨(i, j), b⟩ =
      ⟨(i, k), GroupoidStr.TransitionSet.comp a b h⟩ := by
  change (S.hatMorEquiv Uf).symm ((A.toGroupoidStr.pullback _).comp _ _) = _
  rw [GroupoidStr.pullback_comp_of _ _ h]
  rfl

/-- The morphism of `A` underlying a composite. -/
theorem hatGroupoid_comp_mor {φ ψ : S.HatMor Uf}
    (h : (S.hatGroupoid Uf).src φ = (S.hatGroupoid Uf).tgt ψ) :
    ((S.hatGroupoid Uf).comp φ ψ).2.mor = A.toGroupoidStr.comp φ.2.mor ψ.2.mor := by
  obtain ⟨⟨j', k⟩, a⟩ := φ
  obtain ⟨⟨i, j⟩, b⟩ := ψ
  have hc : A.toGroupoidStr.src a.mor = A.toGroupoidStr.tgt b.mor := by
    rw [a.src_mor, b.tgt_mor]
    exact congrArg (S.hatObjMap Uf) h
  rw [hatGroupoid_comp_of a b hc]
  rfl

variable (S Uf)

/-- The M-polyfold structure of `E = ⊔_λ E_λ`. -/
def hatObjPolyfold : MPolyfold (S.HatObj Uf) := MPolyfold.sigma fun i => (Uf i).unif.E.PObj

/-- The M-polyfold structure of `𝐄 = ⊔ M(Ψ̂_λ, Ψ̂_λ')`. -/
def hatMorPolyfold : MPolyfold (S.HatMor Uf) :=
  MPolyfold.sigma fun p : ι × ι => S.hatTransPolyfold (Uf p.1) (Uf p.2)

/-- `s : 𝐄 → E` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_hatModelSrc :
    (S.hatMorPolyfold Uf).IsLocalScDiffeo (S.hatObjPolyfold Uf) (S.hatGroupoid Uf).src :=
  (MPolyfold.isLocalScDiffeo_sigma_iff _).2 fun p =>
    (MPolyfold.isLocalScDiffeo_sigmaMk (fun i => (Uf i).unif.E.PObj) p.1).comp
      (S.isLocalScDiffeo_hatSrc (Uf p.1) (Uf p.2))

/-- `t : 𝐄 → E` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_hatModelTgt :
    (S.hatMorPolyfold Uf).IsLocalScDiffeo (S.hatObjPolyfold Uf) (S.hatGroupoid Uf).tgt :=
  (MPolyfold.isLocalScDiffeo_sigma_iff _).2 fun p =>
    (MPolyfold.isLocalScDiffeo_sigmaMk (fun i => (Uf i).unif.E.PObj) p.2).comp
      (S.isLocalScDiffeo_hatTgt (Uf p.1) (Uf p.2))

/-- The unit map `E → 𝐄` is sc-smooth. -/
theorem isScSmoothMap_hatModelUnit :
    (S.hatObjPolyfold Uf).IsScSmoothMap (S.hatMorPolyfold Uf) (S.hatGroupoid Uf).unit :=
  (MPolyfold.isScSmoothMap_sigma_iff _).2 fun i =>
    (MPolyfold.isScSmoothMap_sigmaMk_comp_iff
      (fun p : ι × ι => S.hatTransPolyfold (Uf p.1) (Uf p.2)) (i := (i, i))).2
      (S.isScSmoothMap_hatUnit (Uf i))

/-- The inversion `𝐄 → 𝐄` is sc-smooth. -/
theorem isScSmoothMap_hatModelInv :
    (S.hatMorPolyfold Uf).IsScSmoothMap (S.hatMorPolyfold Uf) (S.hatGroupoid Uf).inv := by
  have := MPolyfold.isScSmoothMap_sigmaMap
    (fun p : ι × ι => S.hatTransPolyfold (Uf p.1) (Uf p.2))
    (R := fun p : ι × ι => S.hatTransPolyfold (Uf p.1) (Uf p.2)) (σ := Prod.swap)
    (g := fun p (a : S.HatTr (Uf p.1) (Uf p.2)) => S.toHatTr (GroupoidStr.TransitionSet.inv a))
    fun p => S.isScSmoothMap_hatInv (Uf p.1) (Uf p.2)
  exact this

/-- The inclusion of `M(Ψ̂_λ, Ψ̂_λ')` into `𝐄`. -/
abbrev hatMorMk (p : ι × ι) : S.HatTr (Uf p.1) (Uf p.2) → S.HatMor Uf :=
  Sigma.mk (β := fun p : ι × ι => S.HatTr (Uf p.1) (Uf p.2)) p

/-- The multiplication of `𝐄` in the sheet form (Definition 17.8.13 (c) for the pieces). -/
theorem isScSmoothCompSheet_hatModel :
    IsScSmoothCompSheet (S.hatObjPolyfold Uf) (S.hatMorPolyfold Uf)
      (S.hatGroupoid Uf).src (S.hatGroupoid Uf).tgt (S.hatGroupoid Uf).comp := by
  intro σ W V hd
  have hVo : IsOpen V := hd.isScSmoothOn_inv.isOpen
  have htc : Continuous (S.hatGroupoid Uf).tgt := (S.isLocalScDiffeo_hatModelTgt Uf).continuous
  refine (MPolyfold.isScSmoothOn_sigma_iff _ (hVo.preimage htc)).2 fun p => ?_
  obtain ⟨i, j⟩ := p
  refine MPolyfold.IsScSmoothOn.of_locally ((hVo.preimage htc).preimage continuous_sigmaMk)
    fun b₀ hb₀ => ?_
  have hy₀ : (⟨j, b₀.tgt⟩ : S.HatObj Uf) ∈ V := hb₀
  rcases hσ₀ : σ ⟨j, b₀.tgt⟩ with ⟨⟨j', k⟩, a₀⟩
  have hsrc₀ : (S.hatGroupoid Uf).src (σ ⟨j, b₀.tgt⟩) = ⟨j, b₀.tgt⟩ := hd.right_inv _ hy₀
  rw [hσ₀] at hsrc₀
  have hj : j = j' := ((Sigma.mk.inj_iff.1 hsrc₀).1).symm
  subst hj
  have hsrc₀'' : a₀.src = b₀.tgt := eq_of_heq (Sigma.mk.inj_iff.1 hsrc₀).2
  obtain ⟨W', V', σ', ha₀W', hd'⟩ := S.isLocalScDiffeo_hatSrc (Uf j) (Uf k) a₀
  have hσc : ContinuousOn σ V := hd.isScSmoothOn_inv.continuousOn
  have hW'o : IsOpen (S.hatMorMk Uf (j, k) '' W') :=
    isOpenMap_sigmaMk _ hd'.isOpen_source
  set N : Set (S.HatTr (Uf i) (Uf j)) :=
    (fun b : S.HatTr (Uf i) (Uf j) => (⟨j, b.tgt⟩ : S.HatObj Uf)) ⁻¹'
      (V ∩ σ ⁻¹' (S.hatMorMk Uf (j, k) '' W')) ∩
        (fun b : S.HatTr (Uf i) (Uf j) => b.tgt) ⁻¹' V'
  have hbc : Continuous fun b : S.HatTr (Uf i) (Uf j) => (⟨j, b.tgt⟩ : S.HatObj Uf) :=
    continuous_sigmaMk.comp (S.continuous_hatTgt _ _)
  have hNo : IsOpen N :=
    ((hσc.isOpen_inter_preimage hVo hW'o).preimage hbc).inter
      (hd'.isOpen_target.preimage (S.continuous_hatTgt _ _))
  have hb₀N : b₀ ∈ N := by
    refine ⟨⟨hy₀, ?_⟩, ?_⟩
    · change σ ⟨j, b₀.tgt⟩ ∈ S.hatMorMk Uf (j, k) '' W'
      rw [hσ₀]
      exact ⟨a₀, ha₀W', rfl⟩
    · change b₀.tgt ∈ V'
      rw [← hsrc₀'']
      exact hd'.mapsTo ha₀W'
  have hσN : ∀ b ∈ N, σ ⟨j, b.tgt⟩ = ⟨(j, k), σ' b.tgt⟩ := by
    intro b hb
    obtain ⟨⟨hbV, a, haW', ha⟩⟩ := hb
    have hs : (S.hatGroupoid Uf).src (σ ⟨j, b.tgt⟩) = ⟨j, b.tgt⟩ := hd.right_inv _ hbV
    rw [← ha] at hs ⊢
    obtain ⟨-, hs'⟩ := Sigma.mk.inj_iff.1 hs
    have hs'' : a.src = b.tgt := eq_of_heq hs'
    congr 1
    rw [← hs'', hd'.left_inv a haW']
  have hcomp : ∀ b (hb : b ∈ N), (S.hatGroupoid Uf).comp
      (σ ((S.hatGroupoid Uf).tgt ⟨(i, j), b⟩)) ⟨(i, j), b⟩ =
        ⟨(i, k), GroupoidStr.TransitionSet.comp (σ' b.tgt) b
          (by rw [(σ' b.tgt).src_mor, b.tgt_mor, hd'.right_inv _ hb.2])⟩ := by
    intro b hb
    change (S.hatGroupoid Uf).comp (σ ⟨j, b.tgt⟩) ⟨(i, j), b⟩ = _
    rw [hσN b hb, hatGroupoid_comp_of]
  let _ := MPolyfold.paracompactSpace_prod (S.hatTransPolyfold (Uf j) (Uf k))
    (S.hatTransPolyfold (Uf i) (Uf j))
  set d := MPolyfold.fibredSubDataL hd' (S.isLocalScDiffeo_hatTgt (Uf i) (Uf j)).isScSmoothMap
  let a₀' : MPolyfold.fibredProduct (fun a : S.HatTr (Uf j) (Uf k) => a.src)
      (fun b : S.HatTr (Uf i) (Uf j) => b.tgt) := ⟨(σ' b₀.tgt, b₀), by
    change (σ' b₀.tgt).src = b₀.tgt
    exact hd'.right_inv _ hb₀N.2⟩
  have hm := (S.isScSmoothMap_hatMul (Uf i) (Uf j) (Uf k)).isScSmoothOn_sheet hd' a₀'
  refine ⟨N, hNo, hb₀N, fun b hb => hb.1.1, ?_⟩
  have hm' := (MPolyfold.isScSmoothOn_sigmaMk_comp_iff
    (fun p : ι × ι => S.hatTransPolyfold (Uf p.1) (Uf p.2)) (i := (i, k))).2
    (hm.mono hNo fun b hb => hb.2)
  refine hm'.congr fun b hb => ?_
  simp only [Function.comp_apply]
  rw [hcomp b hb]
  have hv := d.retractInto_val a₀' (x := (σ' b.tgt, b)) ⟨hd'.mapsTo_inv hb.2, hb.2⟩
  refine Sigma.ext rfl (heq_of_eq (GroupoidStr.TransitionSet.ext ?_ ?_ ?_))
  · exact congrArg (fun p : S.HatTr (Uf j) (Uf k) × S.HatTr (Uf i) (Uf j) => p.2.src) hv
  · exact congrArg (fun p : S.HatTr (Uf j) (Uf k) × S.HatTr (Uf i) (Uf j) =>
      A.toGroupoidStr.comp p.1.mor p.2.mor) hv
  · exact congrArg (fun p : S.HatTr (Uf j) (Uf k) × S.HatTr (Uf i) (Uf j) => p.1.tgt) hv

/-- The multiplication `𝐄 ₛ×ₜ 𝐄 → 𝐄` is sc-smooth (Definition 7.1.3 (4)). -/
theorem isScSmoothComp_hatModel :
    IsScSmoothComp (S.hatObjPolyfold Uf) (S.hatMorPolyfold Uf)
      (S.hatGroupoid Uf).src (S.hatGroupoid Uf).tgt (S.hatGroupoid Uf).comp
      (S.isLocalScDiffeo_hatModelSrc Uf) (S.isLocalScDiffeo_hatModelTgt Uf).isScSmoothMap :=
  (isScSmoothComp_iff_sheet _ _).2 (S.isScSmoothCompSheet_hatModel Uf)

/-! ### Properness -/

variable {S} in
/-- **The properness property for the `Ψ̂`** (the analogue of Proposition 17.1.11): for `e ∈ E`
there is an open neighbourhood `W` with `t : s⁻¹(cl W) → E'` proper in every `M(Ψ̂, Ψ̂')`.  From
Proposition 17.1.11 for `M(Ψ, Ψ')`, a sheet of `τ̂` at `e`, and the sc-diffeomorphism
`M(Ψ̂, Ψ̂') ≅ M(Ψ, Ψ') ₛ×_τ̂ E` of Proposition 17.8.15. -/
theorem exists_isProperMap_hatTr (hPc : P.IsProperCoveringGCT) (U : S.toC.Unif) (e : U.unif.ObjE) :
    ∃ W : Set U.unif.ObjE, IsOpen W ∧ e ∈ W ∧ ∀ U' : S.toC.Unif,
      IsProperMap (((fun a : S.HatTr U U' => a.src) ⁻¹' closure W).domRestrict
        fun a : S.HatTr U U' => a.tgt) := by
  set Ub := S.toC.baseUnif S.SB S.SB_F U
  obtain ⟨V, hV, heV, hprop⟩ := S.SB.proposition_17_1_11 Ub (U.unif.τ.obj e)
  obtain ⟨W₀, V₀, σ, heW₀, hd⟩ := U.unif.model.isLocalScDiffeo e
  have := U.unif.Ψ.P.metrizableSpace
  have := U.unif.E.PObj.metrizableSpace
  have hτc : Continuous U.unif.τ.obj := U.unif.model.isLocalScDiffeo.continuous
  obtain ⟨T, hT, hTc, hTsub⟩ := exists_mem_nhds_isClosed_subset
    ((hd.isOpen_target.inter hV).mem_nhds ⟨hd.mapsTo heW₀, heV⟩)
  set W := W₀ ∩ U.unif.τ.obj ⁻¹' interior T
  have hWo : IsOpen W := hd.isOpen_source.inter (isOpen_interior.preimage hτc)
  have heW : e ∈ W := ⟨heW₀, mem_interior_iff_mem_nhds.2 hT⟩
  have hτW : ∀ z ∈ closure W, U.unif.τ.obj z ∈ T := fun z hz =>
    closure_minimal (fun w (hw : w ∈ W) => interior_subset (s := T) hw.2) (hTc.preimage hτc) hz
  have hclW : ∀ z ∈ closure W, σ (U.unif.τ.obj z) = z := by
    intro z hz
    obtain ⟨w, hwW, hwz⟩ := mem_closure_iff_seq_limit.1 hz
    have hτz : U.unif.τ.obj z ∈ V₀ := (hTsub (hτW z hz)).1
    have h1 : Tendsto (fun n => σ (U.unif.τ.obj (w n))) atTop (𝓝 (σ (U.unif.τ.obj z))) :=
      ((hd.isScSmoothOn_inv.continuousOn.continuousAt
        (hd.isOpen_target.mem_nhds hτz)).tendsto).comp ((hτc.tendsto z).comp hwz)
    have h2 : (fun n => σ (U.unif.τ.obj (w n))) = w := funext fun n => hd.left_inv _ (hwW n).1
    rw [h2] at h1
    exact (tendsto_nhds_unique hwz h1).symm
  refine ⟨W, hWo, heW, fun U' => ?_⟩
  set Ub' := S.toC.baseUnif S.SB S.SB_F U'
  have := U'.unif.E.PObj.metrizableSpace
  have := (S.hatTransPolyfold U U').metrizableSpace
  have := (S.SB.transPolyfold Ub Ub').metrizableSpace
  set D := (fun a : S.HatTr U U' => a.src) ⁻¹' closure W
  refine isProperMap_iff_isCompact_preimage.2 ⟨(S.continuous_hatTgt U U').comp
    continuous_subtype_val, fun K hK => ?_⟩
  refine (Topology.IsInducing.subtypeVal.isCompact_iff).2 ?_
  have himg : Subtype.val '' (D.domRestrict (fun a : S.HatTr U U' => a.tgt) ⁻¹' K) =
      {a : S.HatTr U U' | a.src ∈ closure W ∧ a.tgt ∈ K} := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, hb⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨a, h1⟩, h2, rfl⟩
  rw [himg]
  have hτ'c : Continuous U'.unif.τ.obj := U'.unif.model.isLocalScDiffeo.continuous
  have hK' : IsCompact (U'.unif.τ.obj '' K) := hK.image hτ'c
  have hB : IsCompact {b : S.BaseTr U U' | b.src ∈ closure V ∧ b.tgt ∈ U'.unif.τ.obj '' K} := by
    have h := ((hprop Ub').isCompact_preimage hK').image continuous_subtype_val
    convert h using 1
    ext b
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨b, h1⟩, h2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.2, hc⟩
  refine IsSeqCompact.isCompact fun x hx => ?_
  set px : ℕ → S.BaseTr U U' := fun k => transMap U.unif U'.unif (x k)
  have hpx : ∀ k, px k ∈
      {b : S.BaseTr U U' | b.src ∈ closure V ∧ b.tgt ∈ U'.unif.τ.obj '' K} := fun k =>
    ⟨subset_closure (hTsub (hτW _ (hx k).1)).2, ⟨(x k).tgt, (hx k).2, rfl⟩⟩
  obtain ⟨b, -, φ, hφ, hbl⟩ := hB.isSeqCompact hpx
  have hbs : b.src ∈ T := hTc.mem_of_tendsto
    (((S.SB.continuous_trSrc Ub Ub').tendsto b).comp hbl)
    (Eventually.of_forall fun k => hτW _ (hx (φ k)).1)
  have hbV₀ : b.src ∈ V₀ := (hTsub hbs).1
  have hsrc : Tendsto (fun k => (x (φ k)).src) atTop (𝓝 (σ b.src)) := by
    have h1 := ((hd.isScSmoothOn_inv.continuousOn.continuousAt
      (hd.isOpen_target.mem_nhds hbV₀)).tendsto).comp
      (((S.SB.continuous_trSrc Ub Ub').tendsto b).comp hbl)
    refine h1.congr fun k => ?_
    exact hclW _ (hx (φ k)).1
  let := MPolyfold.paracompactSpace_prod (S.SB.transPolyfold Ub Ub') U.unif.E.PObj
  let := ((S.SB.transPolyfold Ub Ub').prod U.unif.E.PObj).paracompactSpace_subtype
    (MPolyfold.fibredProduct (fun a : S.BaseTr U U' => a.src) U.unif.τ.obj)
  obtain ⟨g, hg⟩ := S.proposition_17_8_15 hPc U U'
  have hgc : Continuous g := continuousOn_univ.1 hg.isScSmoothOn_inv.continuousOn
  have hmem : (b, σ b.src) ∈
      MPolyfold.fibredProduct (fun a : S.BaseTr U U' => a.src) U.unif.τ.obj :=
    (hd.right_inv _ hbV₀).symm
  set q : MPolyfold.fibredProduct (fun a : S.BaseTr U U' => a.src) U.unif.τ.obj :=
    ⟨(b, σ b.src), hmem⟩
  have hq : Tendsto (fun k => (⟨(px (φ k), (x (φ k)).src), rfl⟩ :
      MPolyfold.fibredProduct (fun a : S.BaseTr U U' => a.src) U.unif.τ.obj)) atTop (𝓝 q) :=
    tendsto_subtype_rng.2 (hbl.prodMk_nhds hsrc)
  have hx' : Tendsto (fun k => x (φ k)) atTop (𝓝 (g q)) := by
    refine ((hgc.tendsto q).comp hq).congr fun k => ?_
    exact hg.left_inv _ (mem_univ _)
  refine ⟨g q, ⟨?_, ?_⟩, φ, hφ, hx'⟩
  · exact isClosed_closure.mem_of_tendsto (((S.continuous_hatSrc U U').tendsto _).comp hx')
      (Eventually.of_forall fun k => (hx (φ k)).1)
  · exact hK.isClosed.mem_of_tendsto (((S.continuous_hatTgt U U').tendsto _).comp hx')
      (Eventually.of_forall fun k => (hx (φ k)).2)

/-- The inclusion of `E_λ` into `E`. -/
abbrev hatObjMk (i : ι) : (Uf i).unif.ObjE → S.HatObj Uf :=
  Sigma.mk (β := fun i => (Uf i).unif.ObjE) i

/-- The properness of `(E, 𝐄)`: `U = W(e) ⊂ E_λ ⊂ E` with `W(e)` of `exists_isProperMap_hatTr`. -/
theorem exists_isProperMap_hatModel (hPc : P.IsProperCoveringGCT) (x : S.HatObj Uf) :
    ∃ V : Set (S.HatObj Uf), IsOpen V ∧ x ∈ V ∧
      IsProperMap (((S.hatGroupoid Uf).src ⁻¹' closure V).domRestrict
        (S.hatGroupoid Uf).tgt) := by
  obtain ⟨i, q⟩ := x
  obtain ⟨U, hU, hqU, hprop⟩ := exists_isProperMap_hatTr hPc (Uf i) q
  refine ⟨S.hatObjMk Uf i '' U, isOpenMap_sigmaMk (σ := fun i => (Uf i).unif.ObjE) _ hU,
    ⟨q, hqU, rfl⟩, ?_⟩
  have hcl : closure (S.hatObjMk Uf i '' U) = S.hatObjMk Uf i '' closure U :=
    (IsClosedEmbedding.sigmaMk (σ := fun i => (Uf i).unif.ObjE) (i := i)).closure_image_eq U
  rw [hcl]
  set D := (S.hatGroupoid Uf).src ⁻¹' (S.hatObjMk Uf i '' closure U)
  have hD : ∀ p : ι × ι, (S.hatMorMk Uf p ⁻¹' D).Nonempty → p.1 = i := by
    rintro p ⟨a, q', -, hq'⟩
    exact ((Sigma.mk.inj_iff.1 hq').1).symm
  have hτ : ∀ p p' : ι × ι, (S.hatMorMk Uf p ⁻¹' D).Nonempty →
      (S.hatMorMk Uf p' ⁻¹' D).Nonempty → p.2 = p'.2 → p = p' :=
    fun p p' hp hp' h => Prod.ext ((hD p hp).trans (hD p' hp').symm) h
  have hpiece : ∀ p : ι × ι, IsProperMap ((S.hatMorMk Uf p ⁻¹' D).domRestrict
      fun a : S.HatTr (Uf p.1) (Uf p.2) => a.tgt) := by
    rintro ⟨i', j⟩
    by_cases hi : i' = i
    · subst hi
      have hDp : S.hatMorMk Uf (i', j) ⁻¹' D =
          (fun a : S.HatTr (Uf i') (Uf j) => a.src) ⁻¹' closure U := by
        ext a
        constructor
        · rintro ⟨q', hq', he⟩
          have : q' = a.src := eq_of_heq (Sigma.mk.inj_iff.1 he).2
          change a.src ∈ closure U
          rw [← this]
          exact hq'
        · intro ha
          exact ⟨a.src, ha, rfl⟩
      rw [hDp]
      exact hprop (Uf j)
    · have : IsEmpty (S.hatMorMk Uf (i', j) ⁻¹' D) :=
        ⟨fun a => hi (hD (i', j) ⟨a.1, a.2⟩)⟩
      exact isProperMap_of_isEmpty _
  exact isProperMap_domRestrict_sigmaMap (A := fun p : ι × ι => S.HatTr (Uf p.1) (Uf p.2))
    (B := fun i => (Uf i).unif.ObjE) Prod.snd (fun p a => a.tgt)
    (fun p => S.continuous_hatTgt (Uf p.1) (Uf p.2)) D hτ hpiece

/-- **The ep-groupoid `E ≡ (E, 𝐄)`** of (17.104), p. 838: objects `⊔_λ E_λ`, morphisms
`⊔_{(λ, λ')} M(Ψ̂_λ, Ψ̂_λ')`. -/
def hatEpGroupoid (hPc : P.IsProperCoveringGCT) : EpGroupoid (S.HatObj Uf) (S.HatMor Uf) where
  toGroupoidStr := S.hatGroupoid Uf
  PObj := S.hatObjPolyfold Uf
  PMor := S.hatMorPolyfold Uf
  isLocalScDiffeo_src := S.isLocalScDiffeo_hatModelSrc Uf
  isLocalScDiffeo_tgt := S.isLocalScDiffeo_hatModelTgt Uf
  isScSmoothMap_unit := S.isScSmoothMap_hatModelUnit Uf
  isScSmoothMap_inv := S.isScSmoothMap_hatModelInv Uf
  exists_isProperMap := S.exists_isProperMap_hatModel Uf hPc
  isScSmoothComp := S.isScSmoothComp_hatModel Uf

/-- `E` as an object of `EP`. -/
def hatEP (hPc : P.IsProperCoveringGCT) : EP.{u} :=
  ⟨S.HatObj Uf, S.HatMor Uf, S.hatEpGroupoid Uf hPc⟩

/-! ### The functors `τ̂ : E → X`, `Γ̂ : E → A`, `Γ : X → B` -/

/-- The base family `λ ↦ Ψ_λ`, as uniformizers of the polyfold structure of `B`. -/
abbrev baseFam : ι → S.SB.Unif := fun i => S.toC.baseUnif S.SB S.SB_F (Uf i)

/-- `X = ⊔_λ O_λ` with `𝐗 = ⊔ M(Ψ_λ, Ψ_λ')`, the model ep-groupoid of Theorem 17.1.14. -/
abbrev baseEP : EP.{u} := S.SB.modelEP (S.baseFam Uf)

/-- A morphism of `X` is determined by its source, target and morphism of `B`. -/
theorem baseModelMor_ext {φ ψ : S.SB.ModelMor (S.baseFam Uf)}
    (hs : (S.SB.modelGroupoid (S.baseFam Uf)).src φ = (S.SB.modelGroupoid (S.baseFam Uf)).src ψ)
    (hm : φ.2.mor = ψ.2.mor)
    (ht : (S.SB.modelGroupoid (S.baseFam Uf)).tgt φ = (S.SB.modelGroupoid (S.baseFam Uf)).tgt ψ) :
    φ = ψ :=
  (S.SB.modelMorEquiv (S.baseFam Uf)).injective (GroupoidStr.TransitionSet.ext hs hm ht)

/-- `e_λ ↦ τ̂_λ(e_λ)`. -/
def hatModelObj (x : S.HatObj Uf) : S.SB.ModelObj (S.baseFam Uf) :=
  ⟨x.1, (Uf x.1).unif.τ.obj x.2⟩

/-- `(e, φ, e') ↦ p(e, φ, e')` of (17.102). -/
def hatModelMor (φ : S.HatMor Uf) : S.SB.ModelMor (S.baseFam Uf) :=
  ⟨φ.1, transMap (Uf φ.1.1).unif (Uf φ.1.2).unif φ.2⟩

/-- **The functor `τ̂ : E → X`** of (17.104): `e_λ ↦ τ̂_λ(e_λ)`, `(e, φ, e') ↦ p(e, φ, e')`. -/
def hatModelFunctor (hPc : P.IsProperCoveringGCT) :
    EpFunctor (S.hatEpGroupoid Uf hPc) (S.baseEP Uf).X where
  obj := S.hatModelObj Uf
  mor := S.hatModelMor Uf
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp φ ψ h := by
    have hc : A.toGroupoidStr.src φ.2.mor = A.toGroupoidStr.tgt ψ.2.mor := by
      rw [φ.2.src_mor, ψ.2.tgt_mor]
      exact congrArg (S.hatObjMap Uf) h
    have h' : (S.SB.modelGroupoid (S.baseFam Uf)).src (S.hatModelMor Uf φ) =
        (S.SB.modelGroupoid (S.baseFam Uf)).tgt (S.hatModelMor Uf ψ) :=
      congrArg (S.hatModelObj Uf) h
    refine S.baseModelMor_ext Uf ?_ ?_ ?_
    · exact (congrArg (S.hatModelObj Uf) ((S.hatGroupoid Uf).src_comp φ ψ h)).trans
        ((S.SB.modelGroupoid (S.baseFam Uf)).src_comp _ _ h').symm
    · refine Eq.trans ?_ (GCT.PolyfoldConstruction.modelGroupoid_comp_mor h').symm
      change P.mor ((S.hatGroupoid Uf).comp φ ψ).2.mor = B.toGroupoidStr.comp (P.mor φ.2.mor)
        (P.mor ψ.2.mor)
      rw [hatGroupoid_comp_mor h, P.mor_comp _ _ hc]
    · exact (congrArg (S.hatModelObj Uf) ((S.hatGroupoid Uf).tgt_comp φ ψ h)).trans
        ((S.SB.modelGroupoid (S.baseFam Uf)).tgt_comp _ _ h').symm
  mor_unit x := by
    refine S.baseModelMor_ext Uf rfl ?_ rfl
    change P.mor (A.toGroupoidStr.unit ((Uf x.1).unif.hat.obj x.2)) =
      B.toGroupoidStr.unit ((Uf x.1).unif.Ψ.obj ((Uf x.1).unif.τ.obj x.2))
    rw [P.mor_unit, (Uf x.1).unif.obj_comm]
  isScSmoothMap_obj := by
    have := MPolyfold.isScSmoothMap_sigmaMap (fun i => (Uf i).unif.E.PObj)
      (R := fun i => (S.baseFam Uf i).1.P) (σ := id)
      (g := fun i e => (Uf i).unif.τ.obj e) fun i => (Uf i).unif.τ.isScSmoothMap_obj
    exact this
  isScSmoothMap_mor := by
    have := MPolyfold.isScSmoothMap_sigmaMap
      (fun p : ι × ι => S.hatTransPolyfold (Uf p.1) (Uf p.2))
      (R := fun p : ι × ι => S.SB.transPolyfold (S.baseFam Uf p.1) (S.baseFam Uf p.2))
      (σ := id) (g := fun p a => transMap (Uf p.1).unif (Uf p.2).unif a)
      fun p => (S.isLocalScDiffeo_p (Uf p.1) (Uf p.2)).isScSmoothMap
    exact this

/-- **The functor `Γ̂ : E → A`** of (17.104): `e_λ ↦ Ψ̂_λ(e_λ)`, `(e, φ, e') ↦ φ`. -/
def hatFunctor (hPc : P.IsProperCoveringGCT) :
    GroupoidFunctor (S.hatEpGroupoid Uf hPc).toGroupoidStr A.toGroupoidStr where
  obj := S.hatObjMap Uf
  mor φ := φ.2.mor
  src_mor φ := φ.2.src_mor
  tgt_mor φ := φ.2.tgt_mor
  mor_comp _ _ h := hatGroupoid_comp_mor h
  mor_unit _ := rfl

/-- **The functor `Γ : X → B`** of (17.104), the functor `Γ_Ψ` of (17.10) for `λ ↦ Ψ_λ`. -/
abbrev baseFunctor : GroupoidFunctor (S.baseEP Uf).X.toGroupoidStr B.toGroupoidStr :=
  S.SB.modelFunctor (S.baseFam Uf)

/-- **The square (17.104) commutes on objects**: `P ∘ Γ̂ = Γ ∘ τ̂`. -/
theorem square_obj (hPc : P.IsProperCoveringGCT) (x : S.HatObj Uf) :
    P.obj ((S.hatFunctor Uf hPc).obj x) =
      (S.baseFunctor Uf).obj ((S.hatModelFunctor Uf hPc).obj x) :=
  (Uf x.1).unif.obj_comm x.2

/-- **The square (17.104) commutes on morphisms**: `P ∘ Γ̂ = Γ ∘ τ̂`. -/
theorem square_mor (hPc : P.IsProperCoveringGCT) (φ : S.HatMor Uf) :
    P.mor ((S.hatFunctor Uf hPc).mor φ) =
      (S.baseFunctor Uf).mor ((S.hatModelFunctor Uf hPc).mor φ) := rfl

/-- `Γ̂` is full: every `φ : Ψ̂_λ(e) → Ψ̂_λ'(e')` is `Γ̂(e, φ, e')`. -/
theorem hatFunctor_full (hPc : P.IsProperCoveringGCT) : (S.hatFunctor Uf hPc).toFunctor.Full :=
  (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht =>
    ⟨⟨(x.1, x'.1), ⟨x.2, ψ, x'.2, hs, ht⟩⟩, rfl, rfl, rfl⟩

/-- `Γ̂` is faithful. -/
theorem hatFunctor_faithful (hPc : P.IsProperCoveringGCT) :
    (S.hatFunctor Uf hPc).toFunctor.Faithful :=
  (GroupoidFunctor.faithful_iff _).2 fun _ _ hs ht he =>
    (S.hatMorEquiv Uf).injective (GroupoidStr.TransitionSet.ext hs he ht)

variable {S Uf} in
/-- `Γ̂` is essentially surjective when the `Ψ_λ` cover `|B|`: an object `α` of `A` has
`P(α) ≅ Ψ_λ(q)`; the lift of this isomorphism from `α` ends in `P⁻¹(Ψ_λ(O_λ)) = Ψ̂_λ(E_λ)`. -/
theorem hatFunctor_essSurj (hPc : P.IsProperCoveringGCT)
    (h : S.SB.IsCoveringFamily (S.baseFam Uf)) : (S.hatFunctor Uf hPc).toFunctor.EssSurj := by
  refine (GroupoidFunctor.essSurj_iff _).2 fun α => ?_
  obtain ⟨x, ψ, hs, ht⟩ :=
    (GroupoidFunctor.essSurj_iff _).1 (GCT.PolyfoldConstruction.modelFunctor_essSurj h) (P.obj α)
  obtain ⟨φ, hφm, hφs⟩ := ProperCoveringUniformizer.exists_lift hPc
    ⟨(B.toGroupoidStr.inv ψ, α), by rw [B.toGroupoidStr.src_inv, ht]⟩
  have hφm' : P.mor φ = B.toGroupoidStr.inv ψ := hφm
  have hφs' : A.toGroupoidStr.src φ = α := hφs
  have htφ : P.obj (A.toGroupoidStr.tgt φ) = (Uf x.1).unif.Ψ.obj x.2 := by
    rw [← P.tgt_mor, hφm', B.toGroupoidStr.tgt_inv]
    exact hs
  obtain ⟨e, he⟩ : A.toGroupoidStr.tgt φ ∈ range (Uf x.1).unif.hat.obj :=
    (Uf x.1).unif.preimage_range ▸ (⟨x.2, htφ.symm⟩ : A.toGroupoidStr.tgt φ ∈
      P.obj ⁻¹' range (Uf x.1).unif.Ψ.obj)
  exact ⟨⟨x.1, e⟩, A.toGroupoidStr.inv φ, by rw [A.toGroupoidStr.src_inv, ← he]; rfl,
    by rw [A.toGroupoidStr.tgt_inv, hφs']⟩

variable {S Uf} in
/-- **`Γ̂ : E → A` is an equivalence of categories** when the `Ψ_λ` cover `|B|`. -/
theorem hatFunctor_isEquivalence (hPc : P.IsProperCoveringGCT)
    (h : S.SB.IsCoveringFamily (S.baseFam Uf)) : (S.hatFunctor Uf hPc).toFunctor.IsEquivalence :=
  { faithful := S.hatFunctor_faithful Uf hPc, full := S.hatFunctor_full Uf hPc,
    essSurj := hatFunctor_essSurj hPc h }

/-- `|Ψ̂_λ| : |E_λ| → |A|` is an open embedding (Definition 17.8.10 (4)). -/
theorem isOpenEmbedding_hatOrbitMap (hPc : P.IsProperCoveringGCT) (U : S.toC.Unif) :
    IsOpenEmbedding U.unif.hat.orbitMap := by
  obtain ⟨V, hV, -, -, -, he, hr⟩ := U.unif.orbit_homeomorph
  exact ⟨he, hr ▸ hV.preimage hPc.continuous_orbitMap⟩

/-- `|Γ̂|` is continuous. -/
theorem continuous_hatOrbitMap (hPc : P.IsProperCoveringGCT) :
    Continuous (S.hatFunctor Uf hPc).orbitMap :=
  (S.hatEP Uf hPc).X.proposition_7_1_8_isOpenQuotientMap.isQuotientMap.continuous_iff.2
    (continuous_sigma fun i =>
      (S.isOpenEmbedding_hatOrbitMap hPc (Uf i)).continuous.comp (Uf i).unif.E.continuous_π)

/-- `|Γ̂|` is open: on `|E_λ|` it is `|Ψ̂_λ|`, an open embedding. -/
theorem isOpenMap_hatOrbitMap (hPc : P.IsProperCoveringGCT) :
    IsOpenMap (S.hatFunctor Uf hPc).orbitMap := by
  intro W hW
  have he : (S.hatFunctor Uf hPc).orbitMap '' W = ⋃ i, ((Uf i).unif.hat.orbitMap ∘
      (Uf i).unif.E.π) '' ((fun q => (S.hatEP Uf hPc).X.π ⟨i, q⟩) ⁻¹' W) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨⟨i, q⟩, rfl⟩ := (S.hatEP Uf hPc).X.surjective_π w
      exact mem_iUnion.2 ⟨i, q, hw, rfl⟩
    · intro hz
      obtain ⟨i, q, hq, rfl⟩ := mem_iUnion.1 hz
      exact ⟨_, hq, rfl⟩
  rw [he]
  exact isOpen_iUnion fun i => ((S.isOpenEmbedding_hatOrbitMap hPc (Uf i)).isOpenMap.comp
    (Uf i).unif.E.proposition_7_1_8) _
    (hW.preimage ((S.hatEP Uf hPc).X.continuous_π.comp continuous_sigmaMk))

variable {S Uf} in
/-- **`|Γ̂| : |E| → |A|` is a homeomorphism** when the `Ψ_λ` cover `|B|`. -/
theorem isHomeomorph_hatOrbitMap (hPc : P.IsProperCoveringGCT)
    (h : S.SB.IsCoveringFamily (S.baseFam Uf)) : IsHomeomorph (S.hatFunctor Uf hPc).orbitMap :=
  ⟨S.continuous_hatOrbitMap Uf hPc, S.isOpenMap_hatOrbitMap Uf hPc,
    GroupoidFunctor.bijective_orbitMap_of_isEquivalence _ (hatFunctor_isEquivalence hPc h)⟩

end ProperPolyfoldCoveringStructure

/-! ### Witness: two sheets of `ℤ/3 ⋉ ℝ` -/

section Z3

open GCT GCT.PolyfoldConstruction ProperCoveringUniformizerConstruction
  ProperPolyfoldCoveringStructure EpGroupoid.Examples

attribute [local instance] instMulActionZ3Bool

/-- The sheet uniformizer of `z3PolyfoldCoveringFunctor` at `0`. -/
def z3HatUnif : z3PolyfoldCoveringFunctor.S.toC.Unif :=
  ⟨⟨0, sheetUniformizer isScSmoothMap_z3_smul Bool 0 fun _ => rfl⟩,
    sheetUniformizer_mem isScSmoothMap_z3_smul Bool 0 fun _ => rfl⟩

/-- The one-element family `{(Ψ̂, Ψ)}` at `0`. -/
abbrev z3HatFam : PUnit.{1} → z3PolyfoldCoveringFunctor.S.toC.Unif := fun _ => z3HatUnif

/-- Its base uniformizer is the tautological uniformizer of `ℤ/3 ⋉ ℝ`, whose footprint is
`|B|`. -/
theorem z3HatFam_isCoveringFamily :
    z3PolyfoldCoveringFunctor.S.SB.IsCoveringFamily
      (z3PolyfoldCoveringFunctor.S.baseFam z3HatFam) := by
  refine eq_univ_of_forall fun z => mem_iUnion.2 ⟨PUnit.unit, ?_⟩
  change z ∈ (GCT.LocalUniformizer.tautological _ _).footprint
  rw [GCT.LocalUniformizer.tautological_footprint]
  exact mem_univ z

/-- The object `(true, 0)` of `E`. -/
abbrev z3HatPt : z3PolyfoldCoveringFunctor.S.HatObj z3HatFam := ⟨PUnit.unit, (true, 0)⟩

/-- The automorphism of `(true, 0)` over the generator of `ℤ/3`. -/
def z3HatMor : z3PolyfoldCoveringFunctor.S.HatMor z3HatFam :=
  ⟨(PUnit.unit, PUnit.unit), ⟨(true, 0), (Multiplicative.ofAdd (1 : ZMod 3), (true, 0)), (true, 0),
    rfl, rfl⟩⟩

/-- **The global model (17.104) is non-degenerate**: for the two sheets of `ℤ/3 ⋉ ℝ` over
`ℤ/3 ⋉ ℝ`, the family `{(Ψ̂, Ψ)}` covers `|B|`, `Γ̂` and `Γ` are equivalences with
`|Γ̂|`, `|Γ|` homeomorphisms, `E` has an object with a non-unit automorphism, and the fibre of
`τ̂` over `0` has two points, one on each sheet. -/
theorem z3HatModel_nondegenerate :
    let F := z3PolyfoldCoveringFunctor
    let hPc := F.isProperCovering
    (F.S.hatFunctor z3HatFam hPc).toFunctor.IsEquivalence ∧
      IsHomeomorph (F.S.hatFunctor z3HatFam hPc).orbitMap ∧
      (F.S.baseFunctor z3HatFam).toFunctor.IsEquivalence ∧
      IsHomeomorph (F.S.baseFunctor z3HatFam).orbitMap ∧
      (F.S.hatEpGroupoid z3HatFam hPc).src z3HatMor = z3HatPt ∧
      (F.S.hatEpGroupoid z3HatFam hPc).tgt z3HatMor = z3HatPt ∧
      z3HatMor ≠ (F.S.hatEpGroupoid z3HatFam hPc).unit z3HatPt ∧
      ((F.S.hatModelFunctor z3HatFam hPc).obj ⁻¹' {⟨PUnit.unit, (0 : Fin 1 → ℝ)⟩}).ncard = 2 := by
  intro F hPc
  refine ⟨hatFunctor_isEquivalence hPc z3HatFam_isCoveringFamily,
    isHomeomorph_hatOrbitMap hPc z3HatFam_isCoveringFamily,
    (lemma_17_1_15_of_isCovering z3HatFam_isCoveringFamily).1,
    (lemma_17_1_15_of_isCovering z3HatFam_isCoveringFamily).2, rfl, rfl, fun h => ?_, ?_⟩
  · have h1 := congrArg (fun φ : F.S.HatMor z3HatFam => φ.2.mor.1) h
    change Multiplicative.ofAdd (1 : ZMod 3) = 1 at h1
    exact absurd h1 (by decide)
  · have h : (F.S.hatModelFunctor z3HatFam hPc).obj ⁻¹' {⟨PUnit.unit, (0 : Fin 1 → ℝ)⟩} =
        {(⟨PUnit.unit, (true, 0)⟩ : F.S.HatObj z3HatFam), ⟨PUnit.unit, (false, 0)⟩} := by
      ext ⟨u, b, x⟩
      change (⟨u, x⟩ : F.S.SB.ModelObj (F.S.baseFam z3HatFam)) = ⟨PUnit.unit, (0 : Fin 1 → ℝ)⟩ ↔ _
      cases u
      constructor
      · intro h1
        have hx : x = 0 := eq_of_heq (Sigma.mk.inj_iff.1 h1).2
        subst hx
        cases b
        · exact Or.inr rfl
        · exact Or.inl rfl
      · rintro (h1 | h1) <;>
        · have hx : x = 0 :=
            congrArg (fun z : F.S.HatObj z3HatFam => (z.2 : Bool × (Fin 1 → ℝ)).2) h1
          rw [hx]
    rw [h]
    exact Set.ncard_pair fun h => Bool.noConfusion
      (congrArg (fun z : F.S.HatObj z3HatFam => (z.2 : Bool × (Fin 1 → ℝ)).1) h)

end Z3

end Polyfold
