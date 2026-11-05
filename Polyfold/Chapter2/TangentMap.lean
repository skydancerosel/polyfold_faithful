import Polyfold.Chapter2.TangentBundle
import Polyfold.Chapter2.TameRetracts
import Polyfold.Chapter2.StrongBundle
import Polyfold.Chapter2.Metrizable
import Polyfold.Chapter2.StrongBundlePullback
import Polyfold.Chapter2.TameFaces
import Polyfold.Chapter2.FibredProduct
import Polyfold.Chapter2.PartialCone
import Polyfold.Chapter2.CornerGerms
import Polyfold.Chapter2.StrongBundleOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.2: the tangent
map `Tf : TX → TY` of an sc-smooth map between M-polyfolds and the chain rule (the text's
"tangent functor", the paragraph after Theorem 2.8, transported to M-polyfolds; the text itself
only writes `Tf` for sc-smooth maps between retracts and uses `Tf` for M-polyfolds from §2.3 on,
e.g. in Proposition 2.21 (4) and Definition 2.38).

# The tangent map of an sc-smooth map between M-polyfolds

## What is formalized

* `Polyfold.MChart.retractTangentMap_comp_image`: the chain rule for maps on chart images with the
  locality of `Tf` built in (the bookkeeping that every well-definedness proof below needs).
* `MPolyfold.IsScSmoothOn.mapsTo_levelSet`: an sc-smooth map maps `X₁` into `Y₁` (more generally
  `X_m` into `Y_m`; the text's "sc-smooth maps preserve the filtration").
* `MPolyfold.TangentPre.ftransport p f ψ = T(ψ ∘ f ∘ φ⁻¹)(φ(x), h)`: the image vector of
  `(x, φ, h)` seen in a chart `ψ` of `Y` around `f(x)`; `ftransport_fst`, `ftransport_mem`,
  `ftransport_transport` (changing the chart of `Y`), `TangentPre.Rel.ftransport` (independence
  of the representative).
* `MPolyfold.tangentMap hf : TX → TY` (**`Tf`**), with `tangentMap_mk` (its value on any chart
  of `Y` around `f(x)`), `tangentProj_tangentMap` (`p ∘ Tf = f ∘ p`), and
  `tangentChartMap_tangentMap` (`Tψ ∘ Tf = T(ψ ∘ f ∘ φ⁻¹) ∘ Tφ`, formula (5) for `f`).
* `MPolyfold.tangentMap_id` (`T(id) = id`) and `MPolyfold.tangentMap_comp` (**the chain rule**
  `T(g ∘ f) = Tg ∘ Tf`), and `MPolyfold.tangentMap_isScSmooth`: `Tf : TX → TY` is sc-smooth
  (under the paracompactness hypotheses on `TX`, `TY`).

## What the text leaves implicit, and the choices made

* `Tf[(x, φ, h)]` is defined through a chosen chart `ψ` of `Y` around `f(x)`
  (`Classical.choose`); the class does not depend on this choice nor on the representative, by the
  chain rule on small overlaps.  The text never spells this out.
* Only `f : X → Y` sc-smooth on all of `X` is treated (`IsScSmoothMap`); the germ version is the
  same with `U` in place of `X`.
* This file imports `Polyfold.Chapter2.TameRetracts`, `Polyfold.Chapter2.TameFaces`,
  `Polyfold.Chapter2.FibredProduct`, `Polyfold.Chapter2.PartialCone`,
  `Polyfold.Chapter2.CornerGerms` (§2.4),
  `Polyfold.Chapter2.StrongBundle`,
  `Polyfold.Chapter2.StrongBundlePullback`, `Polyfold.Chapter2.StrongBundleOne` (§2.5) and `Polyfold.Chapter2.Metrizable` (Theorem
  2.16, Propositions 2.19 (3), 2.21 (3)–(4)) only so that they are part of the build; nothing from
  them is used here.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E E' E'' : ScBanach}

/-! ### The chain rule on chart images, with locality -/

namespace MChart

variable {X : Type*} [TopologicalSpace X]

/-- **Chain rule with locality.** Let `φ` be a chart, `t ⊆ s₁ ∩ s₂` with `s₁, s₂, t ⊆ V` open, `F`
sc-smooth on `φ(s₁)` into a retract `O₁` and mapping `φ(t)` into a retract `O₁'`, `G` sc-smooth on
`O₁'`, and `H` sc-smooth on `φ(s₂)` with `H = G ∘ F` on `φ(t)`.  Then `TH = TG ∘ TF` on `T(φ(t))`,
the tangent maps being computed on `φ(s₂)`, `O₁'` and `φ(s₁)`. -/
theorem retractTangentMap_comp_image (φ : MChart X) {s₁ s₂ t : Set X} (hs₁ : s₁ ⊆ φ.source)
    (hs₁o : IsOpen s₁) (hs₂ : s₂ ⊆ φ.source) (hs₂o : IsOpen s₂) (hts₁ : t ⊆ s₁) (hts₂ : t ⊆ s₂)
    (hto : IsOpen t) {C₁ O₁ O₁' : Set (E' 0)} {C₂ O₂ : Set (E'' 0)} (hO₁' : IsScRetract E' C₁ O₁')
    {F : φ.model.E 0 → E' 0} (hF : IsScSmoothRetractMap φ.model.E φ.model.C (φ '' s₁) E' C₁ O₁ F)
    (hFt : MapsTo F (φ '' t) O₁') {G : E' 0 → E'' 0} (hG : IsScSmoothRetractMap E' C₁ O₁' E'' C₂ O₂ G)
    {H : φ.model.E 0 → E'' 0} (hH : IsScSmoothRetractMap φ.model.E φ.model.C (φ '' s₂) E'' C₂ O₂ H)
    (hHGF : EqOn H (G ∘ F) (φ '' t)) {a : φ.model.E.tangent 0}
    (ha : a ∈ retractTangent φ.model.E φ.model.C (φ '' t)) :
    retractTangentMap φ.model.E φ.model.C (φ '' s₂) H a =
      retractTangentMap E' C₁ O₁' G (retractTangentMap φ.model.E φ.model.C (φ '' s₁) F a) := by
  have hts : t ⊆ φ.source := hts₁.trans hs₁
  have hφs₁ : IsScRetract φ.model.E φ.model.C (φ '' s₁) := φ.isScRetract_image hs₁ hs₁o
  have hφs₂ : IsScRetract φ.model.E φ.model.C (φ '' s₂) := φ.isScRetract_image hs₂ hs₂o
  have hφt : IsScRetract φ.model.E φ.model.C (φ '' t) := φ.isScRetract_image hts hto
  obtain ⟨W, hW, hWeq⟩ := φ.exists_isOpen_image_eq hts hto
  have hWeq₁ : φ '' t = φ '' s₁ ∩ W := by
    rw [hWeq]
    exact (inter_eq_inter_of_subset (φ.image_subset_model hs₁) (hWeq ▸ image_mono hts₁)).symm
  have hWeq₂ : φ '' t = φ '' s₂ ∩ W := by
    rw [hWeq]
    exact (inter_eq_inter_of_subset (φ.image_subset_model hs₂) (hWeq ▸ image_mono hts₂)).symm
  -- `F` and `H` restricted to `φ(t)`
  have hFt' : IsScSmoothRetractMap φ.model.E φ.model.C (φ '' t) E' C₁ O₁' F := by
    rw [hWeq₁]; exact (hF.restrict hφs₁).mono_target (hWeq₁ ▸ hFt)
  have hHt : IsScSmoothRetractMap φ.model.E φ.model.C (φ '' t) E'' C₂ O₂ H := by
    rw [hWeq₂]; exact hH.restrict hφs₂
  -- locality for `H` and `F`, the chain rule on `φ(t)`
  have hlocH := retractTangentMap_inter_isOpen hH hφs₂ hW (hWeq₂ ▸ ha)
  have hlocF := retractTangentMap_inter_isOpen hF hφs₁ hW (hWeq₁ ▸ ha)
  rw [← hWeq₂] at hlocH
  rw [← hWeq₁] at hlocF
  rw [← hlocH, ← hlocF, retractTangentMap_congr hHt hφt hHGF ha,
    retractTangentMap_comp hG hFt' hφt hO₁' ha]
  rfl

end MChart

namespace MPolyfold

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

/-! ### Sc-smooth maps preserve the levels -/

/-- An sc-smooth map maps `X_m ∩ U` into `Y_m`. -/
theorem IsScSmoothOn.mapsTo_levelSet {f : X → Y} {U : Set X} (hf : P.IsScSmoothOn Q f U) (m : ℕ) :
    MapsTo f (U ∩ P.levelSet m) (Q.levelSet m) := by
  rintro x ⟨hxU, hxm⟩
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  obtain ⟨ψ, hψ, hfxψ⟩ := Q.exists_isChart_mem_source (f x)
  set V := U ∩ φ.source ∩ f ⁻¹' ψ.source with hV
  have hVo : IsOpen V :=
    (hf.continuousOn.mono inter_subset_left).isOpen_inter_preimage (hf.isOpen.inter φ.isOpen_source)
      ψ.isOpen_source
  have hxV : x ∈ V := ⟨⟨hxU, hxφ⟩, hfxψ⟩
  have hsm := hf.smooth φ ψ hφ hψ V hVo (fun y hy => hy.1) fun y hy => hy.2
  rw [Q.mem_levelSet_iff hψ hfxψ]
  have h1 := hsm.mem_range_toBase (φ.isScRetract_image (fun y hy => hy.1.2) hVo) ⟨x, hxV, rfl⟩
    (m := m) ((P.mem_levelSet_iff hφ hxφ).1 hxm)
  simpa only [Function.comp_apply, φ.symm_apply_apply hxφ] using h1

theorem IsScSmoothMap.mapsTo_levelSet {f : X → Y} (hf : P.IsScSmoothMap Q f) (m : ℕ) :
    MapsTo f (P.levelSet m) (Q.levelSet m) := by
  have := IsScSmoothOn.mapsTo_levelSet hf m
  rwa [univ_inter] at this

/-! ### The image vector `T(ψ ∘ f ∘ φ⁻¹)(φ(x), h)` -/

namespace TangentPre

variable {f : X → Y}

/-- The domain `V ∩ f⁻¹(V')` of the coordinate representation `ψ ∘ f ∘ φ⁻¹`. -/
def fdom (φ : MChart X) (f : X → Y) (ψ : MChart Y) : Set X := φ.source ∩ f ⁻¹' ψ.source

lemma isOpen_fdom (hf : P.IsScSmoothMap Q f) (φ : MChart X) (ψ : MChart Y) :
    IsOpen (fdom φ f ψ) :=
  (hf.continuousOn.mono (subset_univ _)).isOpen_inter_preimage φ.isOpen_source ψ.isOpen_source

/-- `ψ ∘ f ∘ φ⁻¹` is sc-smooth on `φ(s)` for every open `s ⊆ V ∩ f⁻¹(V')`. -/
lemma isScSmoothRetractMap_coord (hf : P.IsScSmoothMap Q f) {φ : MChart X} {ψ : MChart Y}
    (hφ : P.IsChart φ) (hψ : Q.IsChart ψ) {s : Set X} (hs : s ⊆ fdom φ f ψ) (hso : IsOpen s) :
    IsScSmoothRetractMap φ.model.E φ.model.C (φ '' s) ψ.model.E ψ.model.C ψ.model.O
      (ψ ∘ f ∘ φ.symm) :=
  hf.smooth φ ψ hφ hψ s hso (fun _ hy => ⟨mem_univ _, (hs hy).1⟩) fun _ hy => (hs hy).2

/-- The image of the vector `(x, φ, h)` under `f`, seen in the chart `ψ` of `Y`:
`T(ψ ∘ f ∘ φ⁻¹)(φ(x), h)`, the tangent map computed on `φ(V ∩ f⁻¹(V'))`. -/
def ftransport (p : P.TangentPre) (f : X → Y) (ψ : MChart Y) : ψ.model.E.tangent 0 :=
  retractTangentMap p.φ.model.E p.φ.model.C (p.φ '' fdom p.φ f ψ) (ψ ∘ f ∘ p.φ.symm) p.vec

variable (hf : P.IsScSmoothMap Q f) (p : P.TangentPre) {ψ : MChart Y} (hψ : Q.IsChart ψ)
  (hx : f p.x ∈ ψ.source)
include hf hψ hx

omit hψ in
lemma vec_mem_fdom : p.vec ∈ retractTangent p.φ.model.E p.φ.model.C (p.φ '' fdom p.φ f ψ) :=
  p.vec_mem_image inter_subset_left (isOpen_fdom hf p.φ ψ) ⟨p.mem_source, hx⟩

lemma ftransport_mem : p.ftransport f ψ ∈ retractTangent ψ.model.E ψ.model.C ψ.model.O :=
  (isScSmoothRetractMap_coord hf p.isChart hψ subset_rfl (isOpen_fdom hf p.φ ψ)).tangentMap_mapsTo
    (p.φ.isScRetract_image inter_subset_left (isOpen_fdom hf p.φ ψ)) ψ.model.isScRetract
    (vec_mem_fdom hf p hx)

/-- The base point of the image vector is `ψ(f(x))`. -/
lemma ftransport_fst : (p.ftransport f ψ).1 = levelLift ψ 1 (f p.x) := by
  have hsm := isScSmoothRetractMap_coord hf p.isChart hψ subset_rfl (isOpen_fdom hf p.φ ψ)
  obtain ⟨R, hR⟩ := p.φ.isScRetract_image (s := fdom p.φ f ψ) inter_subset_left (isOpen_fdom hf p.φ ψ)
  have hmem := vec_mem_fdom hf p hx
  rw [ftransport, retractTangentMap_apply hsm R hR hmem]
  apply ψ.model.E.toBase_injective 1
  have hsc : IsSc0 p.φ.model.E ψ.model.E R.U ((ψ ∘ f ∘ p.φ.symm) ∘ R) :=
    (hsm.comp_isScSmooth R hR).isSc1.isSc0
  have h1 : p.vec.1 ∈ p.φ.model.E.lvlSet R.U 1 := by
    apply R.lvlSet_retract_subset 1
    rw [hR]
    exact retractTangent_fst_mem (p.φ.isScRetract_image inter_subset_left (isOpen_fdom hf p.φ ψ)) hmem
  have h2 : p.φ p.x ∈ R.retract := by rw [hR]; exact ⟨p.x, ⟨p.mem_source, hx⟩, rfl⟩
  have hfx1 : f p.x ∈ Q.levelSet 1 := hf.mapsTo_levelSet 1 p.mem_level
  rw [hsc.toBase_levelMap h1, Function.comp_apply, p.toBase_vec_fst,
    R.apply_eq_self_of_mem_retract h2, Function.comp_apply, Function.comp_apply,
    p.φ.symm_apply_apply p.mem_source, Q.toBase_levelLift hψ hx hfx1]

omit hψ hx in
/-- Changing the chart of `Y`: `T(ψ₂ ∘ ψ₁⁻¹)` carries the image vector in `ψ₁` to the image vector in
`ψ₂`. -/
theorem ftransport_transport {ψ₁ ψ₂ : MChart Y} (hψ₁ : Q.IsChart ψ₁) (hψ₂ : Q.IsChart ψ₂)
    (hx₁ : f p.x ∈ ψ₁.source) (hx₂ : f p.x ∈ ψ₂.source) :
    retractTangentMap ψ₁.model.E ψ₁.model.C (ψ₁.overlap ψ₂) (ψ₁.transition ψ₂) (p.ftransport f ψ₁) =
      p.ftransport f ψ₂ := by
  set t := fdom p.φ f ψ₁ ∩ fdom p.φ f ψ₂ with ht
  have hs₁o : IsOpen (fdom p.φ f ψ₁) := isOpen_fdom hf p.φ ψ₁
  have hs₂o : IsOpen (fdom p.φ f ψ₂) := isOpen_fdom hf p.φ ψ₂
  have hto : IsOpen t := hs₁o.inter hs₂o
  have hxt : p.x ∈ t := ⟨⟨p.mem_source, hx₁⟩, ⟨p.mem_source, hx₂⟩⟩
  have hG : IsScSmoothRetractMap ψ₁.model.E ψ₁.model.C (ψ₁.overlap ψ₂) ψ₂.model.E ψ₂.model.C
      ψ₂.model.O (ψ₁.transition ψ₂) :=
    (hψ₁.compatible hψ₂ (P := Q)).1.mono_target fun _ hz =>
      ψ₂.overlap_subset ψ₁ (ψ₁.transition_mapsTo ψ₂ hz)
  have hFt : MapsTo (ψ₁ ∘ f ∘ p.φ.symm) (p.φ '' t) (ψ₁.overlap ψ₂) := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.1]
    exact ⟨f y, ⟨hy.1.2, hy.2.2⟩, rfl⟩
  exact (p.φ.retractTangentMap_comp_image inter_subset_left hs₁o inter_subset_left hs₂o
    inter_subset_left inter_subset_right hto (ψ₁.isScRetract_overlap ψ₂)
    (isScSmoothRetractMap_coord hf p.isChart hψ₁ subset_rfl hs₁o) hFt hG
    (isScSmoothRetractMap_coord hf p.isChart hψ₂ subset_rfl hs₂o)
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.1, MChart.transition,
        ψ₁.symm_apply_apply hy.1.2])
    (p.vec_mem_image (fun y hy => hy.1.1) hto hxt)).symm

omit hψ hx in
/-- The image vector computed from the vector seen in any chart `φ'` of `X` around `x`:
`T(ψ ∘ f ∘ φ⁻¹)(φ(x), h) = T(ψ ∘ f ∘ φ'⁻¹)(T(φ' ∘ φ⁻¹)(φ(x), h))`. -/
theorem ftransport_eq_of_transport {φ' : MChart X} (hφ' : P.IsChart φ') (hxφ' : p.x ∈ φ'.source)
    (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source) :
    p.ftransport f ψ = retractTangentMap φ'.model.E φ'.model.C (φ' '' fdom φ' f ψ) (ψ ∘ f ∘ φ'.symm)
      (p.transport φ') := by
  set t := (p.φ.source ∩ φ'.source) ∩ fdom p.φ f ψ with ht
  have hs₁o : IsOpen (p.φ.source ∩ φ'.source) := p.φ.isOpen_source.inter φ'.isOpen_source
  have hs₂o : IsOpen (fdom p.φ f ψ) := isOpen_fdom hf p.φ ψ
  have hto : IsOpen t := hs₁o.inter hs₂o
  have hxt : p.x ∈ t := ⟨⟨p.mem_source, hxφ'⟩, ⟨p.mem_source, hx⟩⟩
  have hO₁' : IsScRetract φ'.model.E φ'.model.C (φ' '' fdom φ' f ψ) :=
    φ'.isScRetract_image inter_subset_left (isOpen_fdom hf φ' ψ)
  have hF : IsScSmoothRetractMap p.φ.model.E p.φ.model.C (p.φ '' (p.φ.source ∩ φ'.source)) φ'.model.E
      φ'.model.C (φ'.overlap p.φ) (p.φ.transition φ') := (p.isChart.compatible hφ' (P := P)).1
  have hFt : MapsTo (p.φ.transition φ') (p.φ '' t) (φ' '' fdom φ' f ψ) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [p.φ.transition_apply φ' hy.1.1]
    exact ⟨y, ⟨hy.1.2, hy.2.2⟩, rfl⟩
  exact p.φ.retractTangentMap_comp_image inter_subset_left hs₁o inter_subset_left hs₂o
    inter_subset_left inter_subset_right hto hO₁' hF hFt
    (isScSmoothRetractMap_coord hf hφ' hψ subset_rfl (isOpen_fdom hf φ' ψ))
    (isScSmoothRetractMap_coord hf p.isChart hψ subset_rfl hs₂o)
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.1, p.φ.transition_apply φ' hy.1.1,
        φ'.symm_apply_apply hy.1.2])
    (p.vec_mem_image (fun y hy => hy.1.1) hto hxt)

omit hf p hψ hx in
/-- Equivalent tuples have the same image vector. -/
theorem Rel.ftransport (hf : P.IsScSmoothMap Q f) {p q : P.TangentPre} (h : Rel p q) {ψ : MChart Y}
    (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source) : p.ftransport f ψ = q.ftransport f ψ := by
  rw [ftransport_eq_of_transport hf p q.isChart (h.1 ▸ q.mem_source) hψ hx, h.2,
    ftransport_eq_of_transport hf q q.isChart q.mem_source hψ (h.1 ▸ hx), q.transport_self]

/-- The tuple `(f(x), ψ, Df(x)h)` of `Y`: the image of `(x, φ, h)` under `f`, in the chart `ψ`. -/
def fimageWith : Q.TangentPre where
  x := f p.x
  φ := ψ
  h := (p.ftransport f ψ).2
  isChart := hψ
  mem_source := hx
  mem_level := hf.mapsTo_levelSet 1 p.mem_level
  mem_tangent := by
    have h1 : ((levelLift ψ 1 (f p.x), (p.ftransport f ψ).2) : ψ.model.E.tangent 0) =
        p.ftransport f ψ := Prod.ext (ftransport_fst hf p hψ hx).symm rfl
    rw [h1]
    exact ftransport_mem hf p hψ hx

lemma fimageWith_x : (fimageWith hf p hψ hx).x = f p.x := rfl

lemma fimageWith_vec : (fimageWith hf p hψ hx).vec = p.ftransport f ψ :=
  Prod.ext (ftransport_fst hf p hψ hx).symm rfl

lemma fimageWith_transport (χ : MChart Y) :
    (fimageWith hf p hψ hx).transport χ =
      retractTangentMap ψ.model.E ψ.model.C (ψ.overlap χ) (ψ.transition χ) (p.ftransport f ψ) :=
  congrArg (retractTangentMap ψ.model.E ψ.model.C (ψ.overlap χ) (ψ.transition χ))
    (fimageWith_vec hf p hψ hx)

lemma fimageWith_transport_self : (fimageWith hf p hψ hx).transport ψ = p.ftransport f ψ :=
  ((fimageWith hf p hψ hx).transport_self).trans (fimageWith_vec hf p hψ hx)

omit hψ hx in
/-- The class of the image tuple does not depend on the chart of `Y`. -/
theorem mk_fimageWith_eq {ψ₁ ψ₂ : MChart Y} (hψ₁ : Q.IsChart ψ₁) (hψ₂ : Q.IsChart ψ₂)
    (hx₁ : f p.x ∈ ψ₁.source) (hx₂ : f p.x ∈ ψ₂.source) :
    TangentSpace.mk (fimageWith hf p hψ₁ hx₁) = TangentSpace.mk (fimageWith hf p hψ₂ hx₂) := by
  refine TangentSpace.sound ⟨rfl, ?_⟩
  show (fimageWith hf p hψ₁ hx₁).transport ψ₂ = (fimageWith hf p hψ₂ hx₂).vec
  rw [fimageWith_transport, fimageWith_vec, ftransport_transport hf p hψ₁ hψ₂ hx₁ hx₂]

omit p hψ hx in
/-- The class of the image tuple does not depend on the representative. -/
theorem mk_fimageWith_eq_of_rel {p q : P.TangentPre} (h : Rel p q) (hψ : Q.IsChart ψ)
    (hx : f p.x ∈ ψ.source) :
    TangentSpace.mk (fimageWith hf p hψ hx) = TangentSpace.mk (fimageWith hf q hψ (h.1 ▸ hx)) := by
  refine TangentSpace.sound ⟨?_, ?_⟩
  · show f p.x = f q.x
    rw [h.1]
  · show (fimageWith hf p hψ hx).transport ψ = (fimageWith hf q hψ (h.1 ▸ hx)).vec
    rw [fimageWith_transport_self, fimageWith_vec, h.ftransport hf hψ hx]

/-- The image tuple in the chosen chart of `Y` around `f(x)`. -/
def fimage : Q.TangentPre :=
  fimageWith hf p (Q.exists_isChart_mem_source (f p.x)).choose_spec.1
    (Q.exists_isChart_mem_source (f p.x)).choose_spec.2

end TangentPre

/-! ### The tangent map `Tf : TX → TY` -/

section TangentMap

variable {f : X → Y} (hf : P.IsScSmoothMap Q f)

/-- **The tangent map** `Tf : TX → TY` of an sc-smooth map `f : X → Y`,
`[(x, φ, h)] ↦ [(f(x), ψ, (T(ψ ∘ f ∘ φ⁻¹)(φ(x), h))₂)]`. -/
def tangentMap : P.TangentSpace → Q.TangentSpace :=
  TangentSpace.lift (fun p => TangentSpace.mk (p.fimage hf)) fun p q h => by
    rw [TangentPre.fimage, TangentPre.fimage, TangentPre.mk_fimageWith_eq_of_rel hf h,
      TangentPre.mk_fimageWith_eq hf q]

/-- `Tf[(x, φ, h)]` computed in any chart `ψ` of `Y` around `f(x)`. -/
theorem tangentMap_mk (p : P.TangentPre) {ψ : MChart Y} (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source) :
    tangentMap hf (TangentSpace.mk p) = TangentSpace.mk (p.fimageWith hf hψ hx) := by
  change TangentSpace.mk (p.fimage hf) = _
  rw [TangentPre.fimage, TangentPre.mk_fimageWith_eq hf p _ hψ _ hx]

/-- `p ∘ Tf = f ∘ p`: `Tf` covers `f`. -/
theorem levelVal_tangentProj_tangentMap (α : P.TangentSpace) :
    Q.levelVal 1 (Q.tangentProj (tangentMap hf α)) = f (P.levelVal 1 (P.tangentProj α)) := by
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  obtain ⟨ψ, hψ, hx⟩ := Q.exists_isChart_mem_source (f p.x)
  rw [tangentMap_mk hf p hψ hx]
  rfl

/-- `Tψ ∘ Tf = T(ψ ∘ f ∘ φ⁻¹) ∘ Tφ` on `TV ∩ p⁻¹(f⁻¹(V'))` (formula (5) for `f`). -/
theorem tangentChartMap_tangentMap {φ : MChart X} (hφ : P.IsChart φ) {ψ : MChart Y} (hψ : Q.IsChart ψ)
    {α : P.TangentSpace} (hα : α ∈ tangentChartSet φ)
    (hfα : f (P.levelVal 1 (P.tangentProj α)) ∈ ψ.source) :
    tangentChartMap hψ (tangentMap hf α) =
      retractTangentMap φ.model.E φ.model.C (φ '' TangentPre.fdom φ f ψ) (ψ ∘ f ∘ φ.symm)
        (tangentChartMap hφ α) := by
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  have hfα' : f p.x ∈ ψ.source := hfα
  rw [tangentMap_mk hf p hψ hfα', tangentChartMap_mk hψ hfα',
    TangentPre.fimageWith_transport_self, tangentChartMap_mk hφ hα,
    TangentPre.ftransport_eq_of_transport hf p hφ hα hψ hfα']

/-- `Tf` maps `T_xX` into `T_{f(x)}Y`. -/
theorem tangentMap_mapsTo_fiber (x : P.Level 1) (y : Q.Level 1)
    (hxy : f (P.levelVal 1 x) = Q.levelVal 1 y) :
    MapsTo (tangentMap hf) (P.tangentFiber x) (Q.tangentFiber y) := fun α hα => by
  change Q.tangentProj (tangentMap hf α) = y
  apply level_ext
  rw [levelVal_tangentProj_tangentMap]
  have : P.tangentProj α = x := hα
  rw [this, hxy]

end TangentMap

/-! ### `T(id) = id` and the chain rule -/

/-- **`T(id) = id`**. -/
theorem tangentMap_id : tangentMap (P := P) isScSmoothMap_id = id := by
  funext α
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  rw [tangentMap_mk (isScSmoothMap_id (P := P)) p p.isChart p.mem_source]
  refine TangentSpace.sound ⟨rfl, ?_⟩
  show (p.fimageWith (isScSmoothMap_id (P := P)) p.isChart p.mem_source).transport p.φ = p.vec
  rw [TangentPre.fimageWith_transport_self]
  change retractTangentMap p.φ.model.E p.φ.model.C (p.φ '' TangentPre.fdom p.φ id p.φ)
    (p.φ ∘ id ∘ p.φ.symm) p.vec = p.vec
  have hsub : TangentPre.fdom p.φ id p.φ ⊆ p.φ.source := inter_subset_left
  have hso : IsOpen (TangentPre.fdom p.φ id p.φ) :=
    TangentPre.isOpen_fdom (isScSmoothMap_id (P := P)) p.φ p.φ
  refine retractTangentMap_id (p.φ.isScRetract_image hsub hso) ?_
    (p.vec_mem_image hsub hso ⟨p.mem_source, p.mem_source⟩)
  rintro _ ⟨y, hy, rfl⟩
  simp only [Function.comp_apply, id, p.φ.symm_apply_apply hy.1]

/-- **The chain rule for M-polyfolds**: `T(g ∘ f) = Tg ∘ Tf`. -/
theorem tangentMap_comp {f : X → Y} {g : Y → Z} (hg : Q.IsScSmoothMap S g) (hf : P.IsScSmoothMap Q f) :
    tangentMap (hg.comp hf) = tangentMap hg ∘ tangentMap hf := by
  funext α
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  obtain ⟨ψ, hψ, hx⟩ := Q.exists_isChart_mem_source (f p.x)
  obtain ⟨χ, hχ, hgx⟩ := S.exists_isChart_mem_source (g (f p.x))
  set r := p.fimageWith hf hψ hx with hr
  have hgr : g r.x ∈ χ.source := hgx
  rw [Function.comp_apply, tangentMap_mk hf p hψ hx, tangentMap_mk hg r hχ hgr,
    tangentMap_mk (hg.comp hf) p hχ hgx]
  refine TangentSpace.sound ⟨rfl, ?_⟩
  show (p.fimageWith (hg.comp hf) hχ hgx).transport χ = (r.fimageWith hg hχ hgr).vec
  rw [TangentPre.fimageWith_transport_self, TangentPre.fimageWith_vec hg r hχ hgr]
  -- `T(χ ∘ g ∘ f ∘ φ⁻¹) = T(χ ∘ g ∘ ψ⁻¹) ∘ T(ψ ∘ f ∘ φ⁻¹)`
  change _ = retractTangentMap ψ.model.E ψ.model.C (ψ '' TangentPre.fdom ψ g χ) (χ ∘ g ∘ ψ.symm) r.vec
  refine Eq.trans ?_ (congrArg (retractTangentMap ψ.model.E ψ.model.C (ψ '' TangentPre.fdom ψ g χ)
    (χ ∘ g ∘ ψ.symm)) (TangentPre.fimageWith_vec hf p hψ hx)).symm
  set t := TangentPre.fdom p.φ f ψ ∩ f ⁻¹' TangentPre.fdom ψ g χ with ht
  have hs₁o : IsOpen (TangentPre.fdom p.φ f ψ) := TangentPre.isOpen_fdom hf p.φ ψ
  have hs₂o : IsOpen (TangentPre.fdom p.φ (g ∘ f) χ) := TangentPre.isOpen_fdom (hg.comp hf) p.φ χ
  have hto : IsOpen t :=
    (hf.continuousOn.mono (subset_univ _)).isOpen_inter_preimage hs₁o
      (TangentPre.isOpen_fdom hg ψ χ)
  have hts₂ : t ⊆ TangentPre.fdom p.φ (g ∘ f) χ := fun y hy => ⟨hy.1.1, hy.2.2⟩
  have hxt : p.x ∈ t := ⟨⟨p.mem_source, hx⟩, ⟨hx, hgx⟩⟩
  have hO₁' : IsScRetract ψ.model.E ψ.model.C (ψ '' TangentPre.fdom ψ g χ) :=
    ψ.isScRetract_image inter_subset_left (TangentPre.isOpen_fdom hg ψ χ)
  have hFt : MapsTo (ψ ∘ f ∘ p.φ.symm) (p.φ '' t) (ψ '' TangentPre.fdom ψ g χ) := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.1]
    exact ⟨f y, hy.2, rfl⟩
  exact p.φ.retractTangentMap_comp_image inter_subset_left hs₁o inter_subset_left hs₂o
    inter_subset_left hts₂ hto hO₁'
    (TangentPre.isScSmoothRetractMap_coord hf p.isChart hψ subset_rfl hs₁o) hFt
    (TangentPre.isScSmoothRetractMap_coord hg hψ hχ subset_rfl (TangentPre.isOpen_fdom hg ψ χ))
    (TangentPre.isScSmoothRetractMap_coord (hg.comp hf) p.isChart hχ subset_rfl hs₂o)
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.1, ψ.symm_apply_apply hy.2.1])
    (p.vec_mem_image (fun y hy => hy.1.1) hto hxt)

/-! ### `Tf` is sc-smooth -/

section Smooth

variable {f : X → Y} (hf : P.IsScSmoothMap Q f)

/-- `Tf : TX → TY` is continuous. -/
theorem continuous_tangentMap : Continuous (tangentMap hf) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨ψ, hψ, W, hW, rfl⟩
  rw [isOpen_iff_forall_mem_open]
  intro α hα
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  set φ := p.φ with hφdef
  have hφ : P.IsChart φ := p.isChart
  have hαV : TangentSpace.mk p ∈ tangentChartSet φ := p.mem_source
  have hfα : f (P.levelVal 1 (P.tangentProj (TangentSpace.mk p))) ∈ ψ.source := by
    rw [← levelVal_tangentProj_tangentMap hf]; exact hα.1
  -- the set `φ(V ∩ f⁻¹(V')) = O ∩ W₀` and the continuity of `T(ψ ∘ f ∘ φ⁻¹)` on its tangent
  have hso : IsOpen (TangentPre.fdom φ f ψ) := TangentPre.isOpen_fdom hf φ ψ
  obtain ⟨W₀, hW₀, hW₀eq⟩ := φ.exists_isOpen_image_eq (s := TangentPre.fdom φ f ψ) inter_subset_left hso
  have hTs : retractTangent φ.model.E φ.model.C (φ '' TangentPre.fdom φ f ψ) =
      retractTangent φ.model.E φ.model.C φ.model.O ∩ (φ.model.E.lvlSet W₀ 1 ×ˢ univ) := by
    rw [hW₀eq, retractTangent_inter_isOpen φ.model.isScRetract hW₀]
  have hcont := ((TangentPre.isScSmoothRetractMap_coord hf hφ hψ subset_rfl hso).tangent
    (φ.isScRetract_image inter_subset_left hso) ψ.model.isScRetract).continuousOn
    (φ.isScRetract_image inter_subset_left hso).tangentSet
  obtain ⟨u, hu, hueq⟩ := (continuousOn_iff'.1 hcont) W hW
  refine ⟨{γ | γ ∈ tangentChartSet φ ∧ tangentChartMap hφ γ ∈ (φ.model.E.lvlSet W₀ 1 ×ˢ univ) ∩ u},
    ?_, isOpen_tangent_basic hφ (((φ.model.E.isOpen_lvlSet hW₀ 1).prod isOpen_univ).inter hu), ?_⟩
  · rintro γ ⟨hγ, hγW₀, hγu⟩
    have hγT : tangentChartMap hφ γ ∈ retractTangent φ.model.E φ.model.C (φ '' TangentPre.fdom φ f ψ) := by
      rw [hTs]; exact ⟨tangentChartMap_mem hφ hγ, hγW₀⟩
    have hfγ : f (P.levelVal 1 (P.tangentProj γ)) ∈ ψ.source := by
      have h1 := retractTangent_fst_mem (φ.isScRetract_image inter_subset_left hso) hγT
      rw [ScBanach.mem_lvlSet, tangentChartMap_fst hφ hγ,
        P.toBase_levelLift hφ hγ (levelVal_mem _)] at h1
      obtain ⟨y, hy, hyeq⟩ := h1
      rw [← φ.toPartialEquiv.injOn hy.1 hγ hyeq]
      exact hy.2
    refine ⟨?_, ?_⟩
    · show Q.levelVal 1 (Q.tangentProj (tangentMap hf γ)) ∈ ψ.source
      rw [levelVal_tangentProj_tangentMap]; exact hfγ
    rw [tangentChartMap_tangentMap hf hφ hψ hγ hfγ]
    have : tangentChartMap hφ γ ∈ u ∩ retractTangent φ.model.E φ.model.C (φ '' TangentPre.fdom φ f ψ) :=
      ⟨hγu, hγT⟩
    rw [← hueq] at this
    exact this.1
  · refine ⟨hαV, ?_, ?_⟩
    · have h1 : tangentChartMap hφ (TangentSpace.mk p) ∈
          retractTangent φ.model.E φ.model.C (φ '' TangentPre.fdom φ f ψ) := by
        rw [tangentChartMap_mk_self]
        exact p.vec_mem_image inter_subset_left hso ⟨p.mem_source, hfα⟩
      rw [hTs] at h1; exact h1.2
    · have h1 : tangentChartMap hφ (TangentSpace.mk p) ∈
          retractTangent φ.model.E φ.model.C (φ '' TangentPre.fdom φ f ψ) := by
        rw [tangentChartMap_mk_self]
        exact p.vec_mem_image inter_subset_left hso ⟨p.mem_source, hfα⟩
      have h2 : tangentChartMap hφ (TangentSpace.mk p) ∈
          retractTangentMap φ.model.E φ.model.C (φ '' TangentPre.fdom φ f ψ) (ψ ∘ f ∘ φ.symm) ⁻¹' W ∩
            retractTangent φ.model.E φ.model.C (φ '' TangentPre.fdom φ f ψ) := by
        refine ⟨?_, h1⟩
        rw [mem_preimage, ← tangentChartMap_tangentMap hf hφ hψ hαV hfα]
        exact hα.2
      rw [hueq] at h2
      exact h2.1

/-- **`Tf : TX → TY` is sc-smooth** (the tangent functor on M-polyfolds): in the charts `Tφ`, `Tψ`
it is `T(ψ ∘ f ∘ φ⁻¹)`. -/
theorem tangentMap_isScSmooth [ParacompactSpace P.TangentSpace] [ParacompactSpace Q.TangentSpace] :
    P.tangentPolyfold.IsScSmoothMap Q.tangentPolyfold (tangentMap hf) := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ (continuous_tangentMap hf).continuousOn
    fun α _ => ?_
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  set φ := p.φ with hφdef
  have hφ : P.IsChart φ := p.isChart
  obtain ⟨ψ, hψ, hx⟩ := Q.exists_isChart_mem_source (f p.x)
  have hso : IsOpen (TangentPre.fdom φ f ψ) := TangentPre.isOpen_fdom hf φ ψ
  -- the open set `V = TV ∩ p⁻¹(f⁻¹(V'))`
  set V : Set P.TangentSpace := {γ | γ ∈ tangentChartSet φ ∧
    f (P.levelVal 1 (P.tangentProj γ)) ∈ ψ.source} with hV
  have hVo : IsOpen V :=
    (isOpen_tangentChartSet hφ).inter (ψ.isOpen_source.preimage
      ((hf.continuousOn.mono (subset_univ _)).comp_continuous continuous_levelVal_tangentProj
        fun _ => mem_univ _))
  have hTs : retractTangent φ.model.E φ.model.C (φ '' TangentPre.fdom φ f ψ) =
      tangentChart hφ (TangentSpace.mk p) '' V := by
    ext a
    constructor
    · intro ha
      have haO : a ∈ retractTangent φ.model.E φ.model.C φ.model.O :=
        (TangentPre.mem_retractTangent_image_iff inter_subset_left hso
          (retractTangent_fst_mem (φ.isScRetract_image inter_subset_left hso) ha)).1 ha
      refine ⟨TangentSpace.mk (TangentPre.ofVec hφ haO), ⟨(TangentPre.ofVec hφ haO).mem_source, ?_⟩,
        tangentChartMap_mk_ofVec hφ haO⟩
      change f (TangentPre.ofVec hφ haO).x ∈ ψ.source
      rw [TangentPre.ofVec_x]
      obtain ⟨y, hy, hyeq⟩ := retractTangent_fst_mem (φ.isScRetract_image inter_subset_left hso) ha
      rw [← hyeq, φ.symm_apply_apply hy.1]
      exact hy.2
    · rintro ⟨γ, ⟨hγ, hfγ⟩, rfl⟩
      refine (TangentPre.mem_retractTangent_image_iff inter_subset_left hso ?_).2
        (tangentChartMap_mem hφ hγ)
      change φ.model.E.toBase 1 (tangentChartMap hφ γ).1 ∈ _
      rw [tangentChartMap_fst hφ hγ, P.toBase_levelLift hφ hγ (levelVal_mem _)]
      exact ⟨_, ⟨hγ, hfγ⟩, rfl⟩
  refine ⟨tangentChart hφ (TangentSpace.mk p), tangentChart hψ (tangentMap hf (TangentSpace.mk p)), V,
    P.tangentPolyfold_isChart hφ _, Q.tangentPolyfold_isChart hψ _, hVo, ⟨p.mem_source, hx⟩,
    fun γ hγ => ⟨mem_univ _, hγ.1⟩, ?_, ?_⟩
  · intro γ hγ
    show Q.levelVal 1 (Q.tangentProj (tangentMap hf γ)) ∈ ψ.source
    rw [levelVal_tangentProj_tangentMap]
    exact hγ.2
  · rw [← hTs]
    refine ((TangentPre.isScSmoothRetractMap_coord hf hφ hψ subset_rfl hso).tangent
      (φ.isScRetract_image inter_subset_left hso) ψ.model.isScRetract).congr fun a ha => ?_
    have haO : a ∈ retractTangent φ.model.E φ.model.C φ.model.O :=
      (TangentPre.mem_retractTangent_image_iff inter_subset_left hso
        (retractTangent_fst_mem (φ.isScRetract_image inter_subset_left hso) ha)).1 ha
    change _ = tangentChartMap hψ (tangentMap hf (tangentChartInv hφ _ a))
    rw [tangentChartInv_of_mem hφ _ haO]
    have hγ : TangentSpace.mk (TangentPre.ofVec hφ haO) ∈ tangentChartSet φ :=
      (TangentPre.ofVec hφ haO).mem_source
    have hfγ : f (P.levelVal 1 (P.tangentProj (TangentSpace.mk (TangentPre.ofVec hφ haO)))) ∈
        ψ.source := by
      change f (TangentPre.ofVec hφ haO).x ∈ ψ.source
      rw [TangentPre.ofVec_x]
      obtain ⟨y, hy, hyeq⟩ := retractTangent_fst_mem (φ.isScRetract_image inter_subset_left hso) ha
      rw [← hyeq, φ.symm_apply_apply hy.1]
      exact hy.2
    rw [tangentChartMap_tangentMap hf hφ hψ hγ hfγ, tangentChartMap_mk_ofVec hφ haO]

end Smooth

end MPolyfold

end Polyfold
