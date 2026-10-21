import FCAppendix.Existence.NarrowPayOnceCompactIntegralC1

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology MeasureTheory
open PayOnce PayOnce.OwnImpact CommonList
open scoped ContDiff

def jointProfileScore {R : ℕ} (n c : ℕ) (t : ℝ×(Fin (R+1)→ℝ)) : ℝ :=
  profileScore n c t.1 t.2

theorem contDiffAt_jointProfileScore {R n c : ℕ} (hn : 2≤n) (hc : c≤R+1)
    (t : ℝ×(Fin (R+1)→ℝ)) (hb : ∀i,0<t.2 i)
    (hp : ∀i,kernelMarginal n c t.2 i∈Ioo (0:ℝ) 1) :
    ContDiffAt ℝ 1 (jointProfileScore n c) t := by
  let K := kernelMarginal (ι:=Fin (R+1)) n c
  have hK := contDiffAt_kernelMarginal_interior hn (by simpa using hc) t.2 hb hp
  have hp0 : ContDiffAt ℝ 1 (fun b=>K b 0) t.2 :=
    (contDiffAt_apply ℝ ℝ 0 (K t.2)).comp t.2 (hK.of_le (WithTop.coe_le_coe.mpr le_top))
  have hU : ContDiffAt ℝ 1 (fun b=>fderiv ℝ K b (focalDirection R)) t.2 :=
    (hK.fderiv_right (m:=1) (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiffAt_const
  have hu0 : ContDiffAt ℝ 1 (fun b=>fderiv ℝ K b (focalDirection R) 0) t.2 :=
    (contDiffAt_apply ℝ ℝ 0 _).comp t.2 hU
  have hpb : ContDiffAt ℝ 1 (fun x : ℝ×(Fin (R+1)→ℝ)=>K x.2 0) t :=
    hp0.comp t contDiffAt_snd
  have hub : ContDiffAt ℝ 1 (fun x : ℝ×(Fin (R+1)→ℝ)=>fderiv ℝ K x.2 (focalDirection R) 0) t :=
    hu0.comp t contDiffAt_snd
  have hbid : ContDiffAt ℝ 1 (fun x : ℝ×(Fin (R+1)→ℝ)=>x.2 0) t :=
    (contDiffAt_apply ℝ ℝ 0 t.2).comp t contDiffAt_snd
  have hs : ContDiffAt ℝ 1 (fun x : ℝ×(Fin (R+1)→ℝ)=>PayOnce.success n (K x.2 0)) t := by
    dsimp [PayOnce.success]
    exact contDiffAt_const.sub ((contDiffAt_const.sub hpb).pow n)
  exact (((((contDiffAt_fst.sub hbid).mul contDiffAt_const).mul
    ((contDiffAt_const.sub hpb).pow (n-1))).mul hub)).sub hs

def rowParameterLinear (R : ℕ) : (ℝ×ℝ)→L[ℝ] (ℝ×(Fin (R+1)→ℝ)) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (focalDirection R))

def rowParameter {R : ℕ} {V : Type*} (beta : V→ℝ) (omega : Fin R→V) (t : ℝ×ℝ) :
    ℝ×(Fin (R+1)→ℝ) := (t.1,rowBids beta t.2 omega)

theorem hasFDerivAt_rowParameter {R : ℕ} {V : Type*} (beta : V→ℝ)
    (omega : Fin R→V) (t : ℝ×ℝ) :
    HasFDerivAt (rowParameter beta omega) (rowParameterLinear R) t := by
  have he : (fun x : ℝ×ℝ=>rowBids beta x.2 omega)=
      (fun x : ℝ×ℝ=>rowBids beta 0 omega+x.2 • focalDirection R) := by
    funext x i
    refine Fin.cases ?_ (fun j=>?_) i <;> simp [rowBids,focalDirection]
  have hrow : HasFDerivAt (fun x : ℝ×ℝ=>rowBids beta x.2 omega)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (focalDirection R)) t := by
    rw [he]
    simpa only [zero_add] using ((hasFDerivAt_snd (𝕜:=ℝ) (p:=t)).smul_const (focalDirection R)).const_add (rowBids beta 0 omega)
  exact hasFDerivAt_fst.prodMk hrow

namespace FiniteScoreControl
variable {n R c : ℕ} {w0 kappa eps delta : ℝ}
  (U : FiniteScoreControl n R c w0 kappa eps delta)
  (nu : Measure U.valueBand) [IsProbabilityMeasure nu]

def expectedJointScore (beta : U.valueBand→ℝ) (t : ℝ×ℝ) : ℝ :=
  finiteExpectedScore (R:=R) n c nu beta t.1 t.2

def rowJointScoreDerivative (beta : U.valueBand→ℝ) (t : ℝ×ℝ) (omega : Fin R→U.valueBand) :
    (ℝ×ℝ)→L[ℝ] ℝ :=
  (fderiv ℝ (jointProfileScore n c) (rowParameter beta omega t)).comp (rowParameterLinear R)

theorem contDiffAt_expectedJointScore (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
    (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps)) (t : ℝ×ℝ)
    (ht : t.2∈Ioo (U.B-eps) (U.B+eps)) :
    ContDiffAt ℝ 1 (U.expectedJointScore nu beta) t := by
  let s : Set (ℝ×ℝ) := univ×ˢIoo (U.B-eps) (U.B+eps)
  let f : (ℝ×ℝ)→(Fin R→U.valueBand)→ℝ := fun t omega=>jointProfileScore n c (rowParameter beta omega t)
  let g := U.rowJointScoreDerivative beta
  have hs : IsOpen s := isOpen_univ.prod isOpen_Ioo
  have hpos (v : U.valueBand) : 0<beta v := U.lower_pos.trans_le (hb v).1
  have hpair : Continuous (fun x : (ℝ×ℝ)×(Fin R→U.valueBand)=>rowParameter beta x.2 x.1) := by
    apply Continuous.prodMk (continuous_fst.fst) ?_
    exact (continuous_rowBids_joint beta hbeta).comp (continuous_fst.snd.prodMk continuous_snd)
  have hreg (x : ℝ×ℝ) (hx : x∈s) (omega : Fin R→U.valueBand) :
      ContDiffAt ℝ 1 (jointProfileScore n c) (rowParameter beta omega x) := by
    apply contDiffAt_jointProfileScore U.n_ge (by have:=U.c_le; omega)
    · intro i
      exact Fin.cases (U.lower_pos.trans_le hx.2.1.le) (fun j=>hpos (omega j)) i
    · exact U.interior _ (U.row_box beta hb x.2 ⟨hx.2.1.le,hx.2.2.le⟩ omega)
  have hg : ContinuousOn (fun x : (ℝ×ℝ)×(Fin R→U.valueBand)=>g x.1 x.2) (s×ˢuniv) := by
    intro x hx
    have hfd := (hreg x.1 hx.1 x.2).continuousAt_fderiv (by norm_num)
    have hh := hfd.comp (f:=fun x : (ℝ×ℝ)×(Fin R→U.valueBand)=>rowParameter beta x.2 x.1) (x:=x) hpair.continuousAt
    exact (hh.clm_comp continuousAt_const).continuousWithinAt
  have hd (x : ℝ×ℝ) (hx : x∈s) (omega : Fin R→U.valueBand) :
      HasFDerivAt (fun y=>f y omega) (g x omega) x :=
    (hreg x hx omega).differentiableAt (by norm_num) |>.hasFDerivAt |>.comp x (hasFDerivAt_rowParameter beta omega x)
  have hf (x : ℝ×ℝ) (hx : x∈s) : Continuous (f x) := by
    rw [continuous_iff_continuousAt]
    intro omega
    have hc : Continuous (fun omega : Fin R→U.valueBand=>rowParameter beta omega x) :=
      hpair.comp (continuous_const.prodMk continuous_id)
    exact (hreg x hx omega).continuousAt.comp (f:=fun omega : Fin R→U.valueBand=>rowParameter beta omega x) (x:=omega) hc.continuousAt
  have hh := contDiffAt_integral_of_compact_rows (Measure.pi (fun _ : Fin R=>nu)) f g s hs hf hg hd t ⟨mem_univ _,ht⟩
  apply hh.congr_of_eventuallyEq
  filter_upwards [hs.mem_nhds ⟨mem_univ _,ht⟩] with x hx
  apply integral_congr_ae
  apply ae_of_all
  intro omega
  exact (finiteRowScore_eq_profileScore U.n_ge (by have:=U.c_le; omega) beta x.1 x.2 omega
    (U.lower_pos.trans_le hx.2.1.le) hpos (U.interior _ (U.row_box beta hb x.2 ⟨hx.2.1.le,hx.2.2.le⟩ omega)))

end FiniteScoreControl
end FCAppendix.Existence.NarrowPayOnce
