import Polyfold.Chapter2.TangentMap

/-!
# Local tangent maps

The tangent map `tangentMapOn` of a map defined on an open subset, the tangent preimage, and the
domain, image and transport lemmas for tangent pre-vectors. The tangent constructions of Chapter 8
are in `Chapter8/TangentLocal.lean`.
-/

open Set Filter Topology Function
noncomputable section
namespace Polyfold
namespace MPolyfold
universe u v w
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}
section Preimage

variable (P) in
/-- The part `p⁻¹(U) = {v ∈ TX | p(v) ∈ U}` of `TX` over a subset `U ⊆ X` (the text's `TU`). -/
def tangentPreimage (U : Set X) : Set P.TangentSpace :=
  {α | P.levelVal 1 (P.tangentProj α) ∈ U}

lemma mem_tangentPreimage {U : Set X} {α : P.TangentSpace} :
    α ∈ P.tangentPreimage U ↔ P.levelVal 1 (P.tangentProj α) ∈ U := Iff.rfl

lemma tangentFiber_subset_tangentPreimage {U : Set X} {x : P.Level 1}
    (hx : P.levelVal 1 x ∈ U) : P.tangentFiber x ⊆ P.tangentPreimage U := fun α hα => by
  change P.levelVal 1 (P.tangentProj α) ∈ U
  rw [show P.tangentProj α = x from hα]
  exact hx

end Preimage

variable (P) in
/-- An M-polyfold with a point has a point on level `1` (the points of `O ∩ E₁` are dense in a
retract `O`, by the density of `E₁` in `E₀`). -/
theorem exists_mem_levelSet_one (x : X) : (P.levelSet 1).Nonempty := by
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source x
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  have hxU : φ x ∈ R.U := R.retract_subset (hR ▸ φ.mapsTo_model x hx)
  obtain ⟨W, hW, hWU⟩ := R.relOpen.relOpen
  have hC := R.relOpen.isPartialQuadrant
  rw [hWU] at hxU
  have hint : (interior φ.model.C).Nonempty := hC.interior_lvlSet_nonempty 0
  have hcl : φ x ∈ closure (interior φ.model.C) := by
    rw [hC.convex.closure_interior_eq_closure_of_nonempty_interior hint]
    exact subset_closure hxU.2
  obtain ⟨z, hzW, hzC⟩ := mem_closure_iff.1 hcl W hW hxU.1
  obtain ⟨z₁, hz₁⟩ := (φ.model.E.denseRange_incl 0).exists_mem_open
    (hW.inter _root_.isOpen_interior) ⟨z, hzW, hzC⟩
  have hz₁U : z₁ ∈ φ.model.E.lvlSet R.U 1 := by
    change φ.model.E.toBase 1 z₁ ∈ R.U
    rw [hWU]
    exact ⟨hz₁.1, interior_subset hz₁.2⟩
  have hRz : R (φ.model.E.toBase 1 z₁) ∈ φ.model.O := hR ▸ R.apply_mem_retract hz₁U
  refine ⟨φ.symm (R (φ.model.E.toBase 1 z₁)), (P.mem_levelSet_iff hφ (φ.symm_mapsTo hRz)).2 ?_⟩
  rw [φ.apply_symm_apply hRz]
  exact ⟨levelMap R 1 z₁, R.isSc1.isSc0.toBase_levelMap hz₁U⟩

variable (P) in
/-- `TX` is nonempty as soon as `X` is: the zero vector at a point of `X₁`. -/
theorem nonempty_tangentSpace (x : X) : Nonempty P.TangentSpace := by
  obtain ⟨y, hy⟩ := P.exists_mem_levelSet_one x
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  refine ⟨TangentSpace.mk ⟨y, φ, 0, hφ, hyφ, hy, mk_zero_mem_retractTangent φ.model.isScRetract ?_⟩⟩
  change φ.model.E.toBase 1 (levelLift φ 1 y) ∈ φ.model.O
  rw [P.toBase_levelLift hφ hyφ hy]
  exact φ.mapsTo_model y hyφ

namespace TangentPre
variable {f : X → Y} {U : Set X}

/-- The domain `U ∩ V ∩ f⁻¹(V')` of the coordinate representation `ψ ∘ f ∘ φ⁻¹` of a map
considered on the open set `U`. -/
def fdomOn (U : Set X) (φ : MChart X) (f : X → Y) (ψ : MChart Y) : Set X :=
  U ∩ φ.source ∩ f ⁻¹' ψ.source

omit [T2Space X] [ParacompactSpace X] [T2Space Y] [ParacompactSpace Y] in
lemma fdomOn_univ (φ : MChart X) (f : X → Y) (ψ : MChart Y) : fdomOn univ φ f ψ = fdom φ f ψ := by
  simp only [fdomOn, fdom, univ_inter]

omit [T2Space X] [ParacompactSpace X] [T2Space Y] [ParacompactSpace Y] in
lemma fdomOn_subset (U : Set X) (φ : MChart X) (f : X → Y) (ψ : MChart Y) :
    fdomOn U φ f ψ ⊆ φ.source := fun _ hy => hy.1.2

lemma isOpen_fdomOn (hf : P.IsScSmoothOn Q f U) (φ : MChart X) (ψ : MChart Y) :
    IsOpen (fdomOn U φ f ψ) :=
  (hf.continuousOn.mono inter_subset_left).isOpen_inter_preimage (hf.isOpen.inter φ.isOpen_source)
    ψ.isOpen_source

/-- `ψ ∘ f ∘ φ⁻¹` is sc-smooth on `φ(s)` for every open `s ⊆ U ∩ V ∩ f⁻¹(V')`. -/
lemma isScSmoothRetractMap_coordOn (hf : P.IsScSmoothOn Q f U) {φ : MChart X} {ψ : MChart Y}
    (hφ : P.IsChart φ) (hψ : Q.IsChart ψ) {s : Set X} (hs : s ⊆ fdomOn U φ f ψ) (hso : IsOpen s) :
    IsScSmoothRetractMap φ.model.E φ.model.C (φ '' s) ψ.model.E ψ.model.C ψ.model.O
      (ψ ∘ f ∘ φ.symm) :=
  hf.smooth φ ψ hφ hψ s hso (fun _ hy => (hs hy).1) fun _ hy => (hs hy).2

/-- The image of `(x, φ, h)` under `f` (sc-smooth on `U ∋ x`) in the chart `ψ` of `Y`:
`T(ψ ∘ f ∘ φ⁻¹)(φ(x), h)`, the tangent map computed on `φ(U ∩ V ∩ f⁻¹(V'))`. -/
def ftransportOn (p : P.TangentPre) (U : Set X) (f : X → Y) (ψ : MChart Y) :
    ψ.model.E.tangent 0 :=
  retractTangentMap p.φ.model.E p.φ.model.C (p.φ '' fdomOn U p.φ f ψ) (ψ ∘ f ∘ p.φ.symm) p.vec

lemma vec_mem_fdomOn (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U)
    {ψ : MChart Y} (hx : f p.x ∈ ψ.source) :
    p.vec ∈ retractTangent p.φ.model.E p.φ.model.C (p.φ '' fdomOn U p.φ f ψ) :=
  p.vec_mem_image (fdomOn_subset _ _ _ _) (isOpen_fdomOn hf p.φ ψ) ⟨⟨hxU, p.mem_source⟩, hx⟩

lemma ftransportOn_mem (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U)
    {ψ : MChart Y} (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source) :
    p.ftransportOn U f ψ ∈ retractTangent ψ.model.E ψ.model.C ψ.model.O :=
  (isScSmoothRetractMap_coordOn hf p.isChart hψ subset_rfl
    (isOpen_fdomOn hf p.φ ψ)).tangentMap_mapsTo
    (p.φ.isScRetract_image (fdomOn_subset _ _ _ _) (isOpen_fdomOn hf p.φ ψ)) ψ.model.isScRetract
    (vec_mem_fdomOn hf p hxU hx)

/-- The base point of the image vector is `ψ(f(x))`. -/
lemma ftransportOn_fst (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U)
    {ψ : MChart Y} (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source) :
    (p.ftransportOn U f ψ).1 = levelLift ψ 1 (f p.x) := by
  have hso := isOpen_fdomOn hf p.φ ψ
  have hsm := isScSmoothRetractMap_coordOn hf p.isChart hψ subset_rfl hso
  obtain ⟨R, hR⟩ := p.φ.isScRetract_image (fdomOn_subset U p.φ f ψ) hso
  have hmem := vec_mem_fdomOn hf p hxU hx
  rw [ftransportOn, retractTangentMap_apply hsm R hR hmem]
  apply ψ.model.E.toBase_injective 1
  have hsc : IsSc0 p.φ.model.E ψ.model.E R.U ((ψ ∘ f ∘ p.φ.symm) ∘ R) :=
    (hsm.comp_isScSmooth R hR).isSc1.isSc0
  have h1 : p.vec.1 ∈ p.φ.model.E.lvlSet R.U 1 := by
    apply R.lvlSet_retract_subset 1
    rw [hR]
    exact retractTangent_fst_mem (p.φ.isScRetract_image (fdomOn_subset U p.φ f ψ) hso) hmem
  have h2 : p.φ p.x ∈ R.retract := by rw [hR]; exact ⟨p.x, ⟨⟨hxU, p.mem_source⟩, hx⟩, rfl⟩
  have hfx1 : f p.x ∈ Q.levelSet 1 := hf.mapsTo_levelSet 1 ⟨hxU, p.mem_level⟩
  rw [hsc.toBase_levelMap h1, Function.comp_apply, p.toBase_vec_fst,
    R.apply_eq_self_of_mem_retract h2, Function.comp_apply, Function.comp_apply,
    p.φ.symm_apply_apply p.mem_source, Q.toBase_levelLift hψ hx hfx1]

/-- Changing the chart of `Y`: `T(ψ₂ ∘ ψ₁⁻¹)` carries the image vector in `ψ₁` to the image vector
in `ψ₂`. -/
theorem ftransportOn_transport (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U)
    {ψ₁ ψ₂ : MChart Y} (hψ₁ : Q.IsChart ψ₁) (hψ₂ : Q.IsChart ψ₂) (hx₁ : f p.x ∈ ψ₁.source)
    (hx₂ : f p.x ∈ ψ₂.source) :
    retractTangentMap ψ₁.model.E ψ₁.model.C (ψ₁.overlap ψ₂) (ψ₁.transition ψ₂)
      (p.ftransportOn U f ψ₁) = p.ftransportOn U f ψ₂ := by
  set t := fdomOn U p.φ f ψ₁ ∩ fdomOn U p.φ f ψ₂ with ht
  have hs₁o : IsOpen (fdomOn U p.φ f ψ₁) := isOpen_fdomOn hf p.φ ψ₁
  have hs₂o : IsOpen (fdomOn U p.φ f ψ₂) := isOpen_fdomOn hf p.φ ψ₂
  have hto : IsOpen t := hs₁o.inter hs₂o
  have hxt : p.x ∈ t := ⟨⟨⟨hxU, p.mem_source⟩, hx₁⟩, ⟨⟨hxU, p.mem_source⟩, hx₂⟩⟩
  have hG : IsScSmoothRetractMap ψ₁.model.E ψ₁.model.C (ψ₁.overlap ψ₂) ψ₂.model.E ψ₂.model.C
      ψ₂.model.O (ψ₁.transition ψ₂) :=
    (hψ₁.compatible hψ₂ (P := Q)).1.mono_target fun _ hz =>
      ψ₂.overlap_subset ψ₁ (ψ₁.transition_mapsTo ψ₂ hz)
  have hFt : MapsTo (ψ₁ ∘ f ∘ p.φ.symm) (p.φ '' t) (ψ₁.overlap ψ₂) := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.1.2]
    exact ⟨f y, ⟨hy.1.2, hy.2.2⟩, rfl⟩
  exact (p.φ.retractTangentMap_comp_image (fdomOn_subset _ _ _ _) hs₁o (fdomOn_subset _ _ _ _) hs₂o
    inter_subset_left inter_subset_right hto (ψ₁.isScRetract_overlap ψ₂)
    (isScSmoothRetractMap_coordOn hf p.isChart hψ₁ subset_rfl hs₁o) hFt hG
    (isScSmoothRetractMap_coordOn hf p.isChart hψ₂ subset_rfl hs₂o)
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.1.2, MChart.transition,
        ψ₁.symm_apply_apply hy.1.2])
    (p.vec_mem_image (fun y hy => hy.1.1.2) hto hxt)).symm

/-- The image vector computed from the vector seen in any chart `φ'` of `X` around `x`. -/
theorem ftransportOn_eq_of_transport (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre)
    (hxU : p.x ∈ U) {φ' : MChart X} (hφ' : P.IsChart φ') (hxφ' : p.x ∈ φ'.source) {ψ : MChart Y}
    (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source) :
    p.ftransportOn U f ψ = retractTangentMap φ'.model.E φ'.model.C (φ' '' fdomOn U φ' f ψ)
      (ψ ∘ f ∘ φ'.symm) (p.transport φ') := by
  set t := (p.φ.source ∩ φ'.source) ∩ fdomOn U p.φ f ψ with ht
  have hs₁o : IsOpen (p.φ.source ∩ φ'.source) := p.φ.isOpen_source.inter φ'.isOpen_source
  have hs₂o : IsOpen (fdomOn U p.φ f ψ) := isOpen_fdomOn hf p.φ ψ
  have hto : IsOpen t := hs₁o.inter hs₂o
  have hxt : p.x ∈ t := ⟨⟨p.mem_source, hxφ'⟩, ⟨⟨hxU, p.mem_source⟩, hx⟩⟩
  have hO₁' : IsScRetract φ'.model.E φ'.model.C (φ' '' fdomOn U φ' f ψ) :=
    φ'.isScRetract_image (fdomOn_subset _ _ _ _) (isOpen_fdomOn hf φ' ψ)
  have hF : IsScSmoothRetractMap p.φ.model.E p.φ.model.C (p.φ '' (p.φ.source ∩ φ'.source))
      φ'.model.E φ'.model.C (φ'.overlap p.φ) (p.φ.transition φ') :=
    (p.isChart.compatible hφ' (P := P)).1
  have hFt : MapsTo (p.φ.transition φ') (p.φ '' t) (φ' '' fdomOn U φ' f ψ) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [p.φ.transition_apply φ' hy.1.1]
    exact ⟨y, ⟨⟨hy.2.1.1, hy.1.2⟩, hy.2.2⟩, rfl⟩
  exact p.φ.retractTangentMap_comp_image inter_subset_left hs₁o (fdomOn_subset _ _ _ _) hs₂o
    inter_subset_left inter_subset_right hto hO₁' hF hFt
    (isScSmoothRetractMap_coordOn hf hφ' hψ subset_rfl (isOpen_fdomOn hf φ' ψ))
    (isScSmoothRetractMap_coordOn hf p.isChart hψ subset_rfl hs₂o)
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.1, p.φ.transition_apply φ' hy.1.1,
        φ'.symm_apply_apply hy.1.2])
    (p.vec_mem_image (fun y hy => hy.1.1) hto hxt)

/-- Equivalent tuples have the same image vector. -/
theorem Rel.ftransportOn (hf : P.IsScSmoothOn Q f U) {p q : P.TangentPre} (h : Rel p q)
    (hxU : p.x ∈ U) {ψ : MChart Y} (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source) :
    p.ftransportOn U f ψ = q.ftransportOn U f ψ := by
  have hqU : q.x ∈ U := h.1 ▸ hxU
  have hqx : f q.x ∈ ψ.source := h.1 ▸ hx
  rw [ftransportOn_eq_of_transport hf p hxU q.isChart (h.1 ▸ q.mem_source) hψ hx, h.2,
    ftransportOn_eq_of_transport hf q hqU q.isChart q.mem_source hψ hqx, q.transport_self]

/-- **Locality**: if `f = g` on an open `W ⊆ U ∩ U'`, the image vectors of a tuple over `W` agree
(the chain rule with `G = id`, computed on `φ(W ∩ V ∩ f⁻¹(V'))`). -/
theorem ftransportOn_congr {g : X → Y} {U' W : Set X} (hf : P.IsScSmoothOn Q f U)
    (hg : P.IsScSmoothOn Q g U') (hW : IsOpen W) (hWU : W ⊆ U) (hWU' : W ⊆ U') (hfg : EqOn f g W)
    (p : P.TangentPre) (hxW : p.x ∈ W) {ψ : MChart Y} (hψ : Q.IsChart ψ)
    (hx : f p.x ∈ ψ.source) : p.ftransportOn U f ψ = p.ftransportOn U' g ψ := by
  set t := fdomOn W p.φ f ψ with ht
  have hs₁o := isOpen_fdomOn hf p.φ ψ
  have hs₂o := isOpen_fdomOn hg p.φ ψ
  have hto : IsOpen t := isOpen_fdomOn (hf.mono hW hWU) p.φ ψ
  have hts₁ : t ⊆ fdomOn U p.φ f ψ := fun y hy => ⟨⟨hWU hy.1.1, hy.1.2⟩, hy.2⟩
  have hts₂ : t ⊆ fdomOn U' p.φ g ψ := fun y hy =>
    ⟨⟨hWU' hy.1.1, hy.1.2⟩, by rw [mem_preimage, ← hfg hy.1.1]; exact hy.2⟩
  have hxt : p.x ∈ t := ⟨⟨hxW, p.mem_source⟩, hx⟩
  have hFt : MapsTo (ψ ∘ f ∘ p.φ.symm) (p.φ '' t) ψ.model.O := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.2]
    exact ψ.mapsTo_model _ hy.2
  have key := p.φ.retractTangentMap_comp_image (fdomOn_subset _ _ _ _) hs₁o
    (fdomOn_subset _ _ _ _) hs₂o hts₁ hts₂ hto ψ.model.isScRetract
    (isScSmoothRetractMap_coordOn hf p.isChart hψ subset_rfl hs₁o) hFt
    (isScSmoothRetractMap_id ψ.model.O)
    (isScSmoothRetractMap_coordOn hg p.isChart hψ subset_rfl hs₂o)
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp_apply, id, p.φ.symm_apply_apply hy.1.2, hfg hy.1.1])
    (p.vec_mem_image (fun y hy => hy.1.2) hto hxt)
  rw [ftransportOn, ftransportOn, key]
  exact (retractTangentMap_id ψ.model.isScRetract (fun _ _ => rfl)
    (ftransportOn_mem hf p (hWU hxW) hψ hx)).symm

/-- The tuple `(f(x), ψ, Df(x)h)` of `Y`: the image of `(x, φ, h)` under `f`, in the chart `ψ`. -/
def fimageOnWith (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U) {ψ : MChart Y}
    (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source) : Q.TangentPre where
  x := f p.x
  φ := ψ
  h := (p.ftransportOn U f ψ).2
  isChart := hψ
  mem_source := hx
  mem_level := hf.mapsTo_levelSet 1 ⟨hxU, p.mem_level⟩
  mem_tangent := by
    have h1 : ((levelLift ψ 1 (f p.x), (p.ftransportOn U f ψ).2) : ψ.model.E.tangent 0) =
        p.ftransportOn U f ψ := Prod.ext (ftransportOn_fst hf p hxU hψ hx).symm rfl
    rw [h1]
    exact ftransportOn_mem hf p hxU hψ hx

section FImage
variable (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U) {ψ : MChart Y}
  (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source)

lemma fimageOnWith_vec : (fimageOnWith hf p hxU hψ hx).vec = p.ftransportOn U f ψ :=
  Prod.ext (ftransportOn_fst hf p hxU hψ hx).symm rfl

lemma fimageOnWith_transport (χ : MChart Y) :
    (fimageOnWith hf p hxU hψ hx).transport χ =
      retractTangentMap ψ.model.E ψ.model.C (ψ.overlap χ) (ψ.transition χ)
        (p.ftransportOn U f ψ) :=
  congrArg (retractTangentMap ψ.model.E ψ.model.C (ψ.overlap χ) (ψ.transition χ))
    (fimageOnWith_vec hf p hxU hψ hx)

lemma fimageOnWith_transport_self :
    (fimageOnWith hf p hxU hψ hx).transport ψ = p.ftransportOn U f ψ :=
  ((fimageOnWith hf p hxU hψ hx).transport_self).trans (fimageOnWith_vec hf p hxU hψ hx)

end FImage

/-- The class of the image tuple does not depend on the chart of `Y`. -/
theorem mk_fimageOnWith_eq (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U)
    {ψ₁ ψ₂ : MChart Y} (hψ₁ : Q.IsChart ψ₁) (hψ₂ : Q.IsChart ψ₂) (hx₁ : f p.x ∈ ψ₁.source)
    (hx₂ : f p.x ∈ ψ₂.source) :
    TangentSpace.mk (fimageOnWith hf p hxU hψ₁ hx₁) =
      TangentSpace.mk (fimageOnWith hf p hxU hψ₂ hx₂) := by
  refine TangentSpace.sound ⟨rfl, ?_⟩
  change (fimageOnWith hf p hxU hψ₁ hx₁).transport ψ₂ = (fimageOnWith hf p hxU hψ₂ hx₂).vec
  rw [fimageOnWith_transport, fimageOnWith_vec, ftransportOn_transport hf p hxU hψ₁ hψ₂ hx₁ hx₂]

/-- The class of the image tuple does not depend on the representative. -/
theorem mk_fimageOnWith_eq_of_rel (hf : P.IsScSmoothOn Q f U) {p q : P.TangentPre} (h : Rel p q)
    (hxU : p.x ∈ U) (hqU : q.x ∈ U) {ψ : MChart Y} (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source)
    (hqx : f q.x ∈ ψ.source) :
    TangentSpace.mk (fimageOnWith hf p hxU hψ hx) =
      TangentSpace.mk (fimageOnWith hf q hqU hψ hqx) := by
  refine TangentSpace.sound ⟨?_, ?_⟩
  · change f p.x = f q.x
    rw [h.1]
  · change (fimageOnWith hf p hxU hψ hx).transport ψ = (fimageOnWith hf q hqU hψ hqx).vec
    rw [fimageOnWith_transport_self, fimageOnWith_vec, h.ftransportOn hf hxU hψ hx]

/-- The image tuple in the chosen chart of `Y` around `f(x)`. -/
def fimageOn (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U) : Q.TangentPre :=
  fimageOnWith hf p hxU (Q.exists_isChart_mem_source (f p.x)).choose_spec.1
    (Q.exists_isChart_mem_source (f p.x)).choose_spec.2

end TangentPre

section TangentMapOn
variable {f : X → Y} {U : Set X}

open scoped Classical in
/-- **The tangent map `Tf : p⁻¹(U) → TY`** of a map `f` sc-smooth on the open set `U`,
`[(x, φ, h)] ↦ [(f(x), ψ, (T(ψ ∘ f ∘ φ⁻¹)(φ(x), h))₂)]` for `x ∈ U`; off `p⁻¹(U)` a junk value
(a point of `TY`, which is nonempty as soon as `Y` is: `nonempty_tangentSpace`). -/
def tangentMapOn (hf : P.IsScSmoothOn Q f U) : P.TangentSpace → Q.TangentSpace :=
  TangentSpace.lift (fun p => if hx : p.x ∈ U then TangentSpace.mk (p.fimageOn hf hx)
      else Classical.choice (Q.nonempty_tangentSpace (f p.x))) fun p q h => by
    by_cases hx : p.x ∈ U
    · have hqU : q.x ∈ U := h.1 ▸ hx
      have hψ := (Q.exists_isChart_mem_source (f p.x)).choose_spec
      have hqx : f q.x ∈ (Q.exists_isChart_mem_source (f p.x)).choose.source := h.1 ▸ hψ.2
      rw [dif_pos hx, dif_pos hqU, TangentPre.fimageOn, TangentPre.fimageOn]
      exact (TangentPre.mk_fimageOnWith_eq_of_rel hf h hx hqU hψ.1 hψ.2 hqx).trans
        (TangentPre.mk_fimageOnWith_eq hf q hqU _ _ _ _)
    · have hqU : q.x ∉ U := h.1 ▸ hx
      rw [dif_neg hx, dif_neg hqU]

/-- `Tf[(x, φ, h)]` computed in any chart `ψ` of `Y` around `f(x)`, for `x ∈ U`. -/
theorem tangentMapOn_mk (hf : P.IsScSmoothOn Q f U) (p : P.TangentPre) (hxU : p.x ∈ U)
    {ψ : MChart Y} (hψ : Q.IsChart ψ) (hx : f p.x ∈ ψ.source) :
    tangentMapOn hf (TangentSpace.mk p) = TangentSpace.mk (p.fimageOnWith hf hxU hψ hx) := by
  rw [tangentMapOn, TangentSpace.lift_mk, dif_pos hxU, TangentPre.fimageOn,
    TangentPre.mk_fimageOnWith_eq hf p hxU _ hψ _ hx]

/-- `p ∘ Tf = f ∘ p` on `p⁻¹(U)`. -/
theorem levelVal_tangentProj_tangentMapOn (hf : P.IsScSmoothOn Q f U) {α : P.TangentSpace}
    (hα : α ∈ P.tangentPreimage U) :
    Q.levelVal 1 (Q.tangentProj (tangentMapOn hf α)) = f (P.levelVal 1 (P.tangentProj α)) := by
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  obtain ⟨ψ, hψ, hx⟩ := Q.exists_isChart_mem_source (f p.x)
  rw [tangentMapOn_mk hf p hα hψ hx]
  rfl

/-- `Tf` maps `p⁻¹(U)` into `p⁻¹(V)` when `f` maps `U` into `V`. -/
theorem tangentMapOn_mapsTo (hf : P.IsScSmoothOn Q f U) {V : Set Y} (hfUV : MapsTo f U V) :
    MapsTo (tangentMapOn hf) (P.tangentPreimage U) (Q.tangentPreimage V) := fun α hα => by
  change Q.levelVal 1 (Q.tangentProj (tangentMapOn hf α)) ∈ V
  rw [levelVal_tangentProj_tangentMapOn hf hα]
  exact hfUV hα

/-- `Tf` maps `T_xX` into `T_{f(x)}Y` for `x ∈ U`. -/
theorem tangentMapOn_mapsTo_fiber (hf : P.IsScSmoothOn Q f U) (x : P.Level 1)
    (hx : P.levelVal 1 x ∈ U) (y : Q.Level 1) (hxy : f (P.levelVal 1 x) = Q.levelVal 1 y) :
    MapsTo (tangentMapOn hf) (P.tangentFiber x) (Q.tangentFiber y) := fun α hα => by
  have hαx : P.tangentProj α = x := hα
  change Q.tangentProj (tangentMapOn hf α) = y
  apply level_ext
  rw [levelVal_tangentProj_tangentMapOn hf (tangentFiber_subset_tangentPreimage hx hα), hαx, hxy]

/-- `Tψ ∘ Tf = T(ψ ∘ f ∘ φ⁻¹) ∘ Tφ` on `p⁻¹(U ∩ V ∩ f⁻¹(V'))` (formula (5) for `f`). -/
theorem tangentChartMap_tangentMapOn (hf : P.IsScSmoothOn Q f U) {φ : MChart X}
    (hφ : P.IsChart φ) {ψ : MChart Y} (hψ : Q.IsChart ψ) {α : P.TangentSpace}
    (hα : α ∈ P.tangentPreimage (TangentPre.fdomOn U φ f ψ)) :
    tangentChartMap hψ (tangentMapOn hf α) =
      retractTangentMap φ.model.E φ.model.C (φ '' TangentPre.fdomOn U φ f ψ) (ψ ∘ f ∘ φ.symm)
        (tangentChartMap hφ α) := by
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  have hxU : p.x ∈ U := hα.1.1
  have hxφ : p.x ∈ φ.source := hα.1.2
  have hfα : f p.x ∈ ψ.source := hα.2
  rw [tangentMapOn_mk hf p hxU hψ hfα, tangentChartMap_mk hψ hfα,
    TangentPre.fimageOnWith_transport_self, tangentChartMap_mk hφ hxφ,
    TangentPre.ftransportOn_eq_of_transport hf p hxU hφ hxφ hψ hfα]

/-- **Locality of `Tf`**: if `f = g` on an open `W ⊆ U ∩ U'`, then `Tf = Tg` on `p⁻¹(W)`. -/
theorem tangentMapOn_congr {g : X → Y} {U' W : Set X} (hf : P.IsScSmoothOn Q f U)
    (hg : P.IsScSmoothOn Q g U') (hW : IsOpen W) (hWU : W ⊆ U) (hWU' : W ⊆ U')
    (hfg : EqOn f g W) : EqOn (tangentMapOn hf) (tangentMapOn hg) (P.tangentPreimage W) := by
  intro α hα
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  have hxW : p.x ∈ W := hα
  obtain ⟨ψ, hψ, hx⟩ := Q.exists_isChart_mem_source (f p.x)
  have hx' : g p.x ∈ ψ.source := hfg hxW ▸ hx
  rw [tangentMapOn_mk hf p (hWU hxW) hψ hx, tangentMapOn_mk hg p (hWU' hxW) hψ hx']
  refine TangentSpace.sound ⟨hfg hxW, ?_⟩
  change (p.fimageOnWith hf (hWU hxW) hψ hx).transport ψ = (p.fimageOnWith hg (hWU' hxW) hψ hx').vec
  rw [TangentPre.fimageOnWith_transport_self, TangentPre.fimageOnWith_vec]
  exact TangentPre.ftransportOn_congr hf hg hW hWU hWU' hfg p hxW hψ hx

/-- For a globally sc-smooth `f`, the tangent map on `U` is Part I's `Tf` on `p⁻¹(U)`. -/
theorem tangentMapOn_eq_tangentMap (hf : P.IsScSmoothMap Q f) (hf' : P.IsScSmoothOn Q f U) :
    EqOn (tangentMapOn hf') (tangentMap hf) (P.tangentPreimage U) := by
  intro α hα
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  have hxU : p.x ∈ U := hα
  obtain ⟨ψ, hψ, hx⟩ := Q.exists_isChart_mem_source (f p.x)
  rw [tangentMapOn_mk hf' p hxU hψ hx, tangentMap_mk hf p hψ hx]
  refine TangentSpace.sound ⟨rfl, ?_⟩
  change (p.fimageOnWith hf' hxU hψ hx).transport ψ = (p.fimageWith hf hψ hx).vec
  rw [TangentPre.fimageOnWith_transport_self, TangentPre.fimageWith_vec]
  have h1 : p.ftransport f ψ = p.ftransportOn univ f ψ := by
    rw [TangentPre.ftransport, TangentPre.ftransportOn, TangentPre.fdomOn_univ]
  rw [h1]
  exact TangentPre.ftransportOn_congr hf' hf hf'.isOpen subset_rfl (subset_univ _)
    (eqOn_refl _ _) p hxU hψ hx

/-- The tangent map on `univ` is Part I's `Tf`. -/
theorem tangentMapOn_univ (hf : P.IsScSmoothMap Q f) : tangentMapOn hf = tangentMap hf :=
  funext fun _ => tangentMapOn_eq_tangentMap hf hf (mem_univ _)

/-- **`T(id) = id`** on `p⁻¹(U)`. -/
theorem tangentMapOn_id (h : P.IsScSmoothOn P id U) :
    EqOn (tangentMapOn h) id (P.tangentPreimage U) := fun α hα => by
  rw [tangentMapOn_eq_tangentMap isScSmoothMap_id h hα, tangentMap_id]

/-- `Tf = id` on `p⁻¹(U)` for a map `f` sc-smooth on `U` with `f = id` on `U`. -/
theorem tangentMapOn_eqOn_id {f : X → X} (hf : P.IsScSmoothOn P f U) (hfid : EqOn f id U) :
    EqOn (tangentMapOn hf) id (P.tangentPreimage U) := fun α hα => by
  rw [tangentMapOn_congr hf (isScSmoothMap_id.mono hf.isOpen (subset_univ _)) hf.isOpen subset_rfl
    subset_rfl hfid hα]
  exact tangentMapOn_id _ hα

/-- **The chain rule on open sets**: `T(g ∘ f) = Tg ∘ Tf` on `p⁻¹(U)`, for `f` sc-smooth on `U`,
`g` sc-smooth on `V` and `f(U) ⊆ V`. -/
theorem tangentMapOn_comp {g : Y → Z} {V : Set Y} (hg : Q.IsScSmoothOn S g V)
    (hf : P.IsScSmoothOn Q f U) (hfUV : MapsTo f U V) :
    EqOn (tangentMapOn (hg.comp hf hfUV)) (tangentMapOn hg ∘ tangentMapOn hf)
      (P.tangentPreimage U) := by
  intro α hα
  obtain ⟨p, rfl⟩ := TangentSpace.exists_rep α
  have hxU : p.x ∈ U := hα
  obtain ⟨ψ, hψ, hx⟩ := Q.exists_isChart_mem_source (f p.x)
  obtain ⟨χ, hχ, hgx⟩ := S.exists_isChart_mem_source (g (f p.x))
  set r := p.fimageOnWith hf hxU hψ hx with hr
  have hrV : r.x ∈ V := hfUV hxU
  have hgr : g r.x ∈ χ.source := hgx
  rw [Function.comp_apply, tangentMapOn_mk hf p hxU hψ hx, tangentMapOn_mk hg r hrV hχ hgr,
    tangentMapOn_mk (hg.comp hf hfUV) p hxU hχ hgx]
  refine TangentSpace.sound ⟨rfl, ?_⟩
  change (p.fimageOnWith (hg.comp hf hfUV) hxU hχ hgx).transport χ =
    (r.fimageOnWith hg hrV hχ hgr).vec
  rw [TangentPre.fimageOnWith_transport_self, TangentPre.fimageOnWith_vec hg r hrV hχ hgr]
  change _ = retractTangentMap ψ.model.E ψ.model.C (ψ '' TangentPre.fdomOn V ψ g χ)
    (χ ∘ g ∘ ψ.symm) r.vec
  refine Eq.trans ?_ (congrArg (retractTangentMap ψ.model.E ψ.model.C
    (ψ '' TangentPre.fdomOn V ψ g χ) (χ ∘ g ∘ ψ.symm))
    (TangentPre.fimageOnWith_vec hf p hxU hψ hx)).symm
  set t := TangentPre.fdomOn U p.φ f ψ ∩ f ⁻¹' TangentPre.fdomOn V ψ g χ with ht
  have hs₁o : IsOpen (TangentPre.fdomOn U p.φ f ψ) := TangentPre.isOpen_fdomOn hf p.φ ψ
  have hs₂o : IsOpen (TangentPre.fdomOn U p.φ (g ∘ f) χ) :=
    TangentPre.isOpen_fdomOn (hg.comp hf hfUV) p.φ χ
  have hto : IsOpen t :=
    (hf.continuousOn.mono fun y hy => hy.1.1).isOpen_inter_preimage hs₁o
      (TangentPre.isOpen_fdomOn hg ψ χ)
  have hts₂ : t ⊆ TangentPre.fdomOn U p.φ (g ∘ f) χ := fun y hy => ⟨hy.1.1, hy.2.2⟩
  have hxt : p.x ∈ t := ⟨⟨⟨hxU, p.mem_source⟩, hx⟩, ⟨⟨hrV, hx⟩, hgx⟩⟩
  have hO₁' : IsScRetract ψ.model.E ψ.model.C (ψ '' TangentPre.fdomOn V ψ g χ) :=
    ψ.isScRetract_image (TangentPre.fdomOn_subset _ _ _ _) (TangentPre.isOpen_fdomOn hg ψ χ)
  have hFt : MapsTo (ψ ∘ f ∘ p.φ.symm) (p.φ '' t) (ψ '' TangentPre.fdomOn V ψ g χ) := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.1.2]
    exact ⟨f y, hy.2, rfl⟩
  exact p.φ.retractTangentMap_comp_image (TangentPre.fdomOn_subset _ _ _ _) hs₁o
    (TangentPre.fdomOn_subset _ _ _ _) hs₂o inter_subset_left hts₂ hto hO₁'
    (TangentPre.isScSmoothRetractMap_coordOn hf p.isChart hψ subset_rfl hs₁o) hFt
    (TangentPre.isScSmoothRetractMap_coordOn hg hψ hχ subset_rfl
      (TangentPre.isOpen_fdomOn hg ψ χ))
    (TangentPre.isScSmoothRetractMap_coordOn (hg.comp hf hfUV) p.isChart hχ subset_rfl hs₂o)
    (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp_apply, p.φ.symm_apply_apply hy.1.1.2,
        ψ.symm_apply_apply hy.2.1.2])
    (p.vec_mem_image (fun y hy => hy.1.1.2) hto hxt)

end TangentMapOn
end MPolyfold
end Polyfold
end
