import FCAppendix.Existence.NarrowPayOnceSecondProfile
import FCAppendix.Existence.NarrowPayOnceReferenceCurvature
import FCAppendix.PayOnce.ResponseFactor

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology
open PayOnce PayOnce.OwnImpact CommonList
open PayOnce.ResponseFactor
open scoped BigOperators ContDiff

def focalDirection (R : ℕ) : Fin (R+1)→ℝ := Fin.cons 1 (fun _=>0)

def profileScore {R : ℕ} (n c : ℕ) (w : ℝ) (b : Fin (R+1)→ℝ) : ℝ :=
  let K := kernelMarginal (ι:=Fin (R+1)) n c
  let p := K b 0
  (w-b 0)*(n:ℝ)*(1-p)^(n-1)*fderiv ℝ K b (focalDirection R) 0-PayOnce.success n p

def profileScoreDerivative {R : ℕ} (n c : ℕ) (w : ℝ) (b h : Fin (R+1)→ℝ) : ℝ :=
  let K := kernelMarginal (ι:=Fin (R+1)) n c
  let p := K b 0
  let u := fderiv ℝ K b (focalDirection R) 0
  let uh := fderiv ℝ K b h 0
  let u2 := fderiv ℝ (fun a=>fderiv ℝ K a (focalDirection R)) b h 0;
  -(h 0) * (n:ℝ) * (1-p)^(n-1) * u -
    (w-b 0) * (n:ℝ) * ((n-1:ℕ):ℝ) * (1-p)^(n-2) * uh * u +
    (w-b 0) * (n:ℝ) * (1-p)^(n-1) * u2 - (n:ℝ) * (1-p)^(n-1) * uh

theorem differentiableAt_profileScore {R n c : ℕ} (hn : 2≤n) (hc : c≤R+1)
    (w : ℝ) (b : Fin (R+1)→ℝ) (hb : ∀i,0<b i)
    (hp : ∀i,kernelMarginal n c b i∈Ioo (0:ℝ) 1) :
    DifferentiableAt ℝ (profileScore n c w) b := by
  have hK := contDiffAt_kernelMarginal_interior hn (by simpa using hc) b hb hp
  have hdK := hK.differentiableAt (by simp)
  have hU : ContDiffAt ℝ 1 (fun a=>fderiv ℝ (kernelMarginal n c) a (focalDirection R)) b :=
    (hK.fderiv_right (m:=1) (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiffAt_const
  have hdU := hU.differentiableAt (by norm_num)
  have hp0 : DifferentiableAt ℝ (fun a=>kernelMarginal n c a (0:Fin (R+1))) b :=
    (differentiableAt_apply (𝕜:=ℝ) (0:Fin (R+1)) (kernelMarginal n c b)).comp b hdK
  have hu0 : DifferentiableAt ℝ
      (fun a=>fderiv ℝ (kernelMarginal n c) a (focalDirection R) (0:Fin (R+1))) b := by
    have hApply : DifferentiableAt ℝ (fun z : Fin (R+1)→ℝ=>z 0)
        (fderiv ℝ (kernelMarginal n c) b (focalDirection R)) := differentiableAt_apply _ _
    exact DifferentiableAt.comp b hApply hdU
  have hS : DifferentiableAt ℝ (fun a=>PayOnce.success n (kernelMarginal n c a (0:Fin (R+1)))) b := by
    dsimp [PayOnce.success]
    fun_prop
  exact (((((differentiableAt_const w).sub (differentiableAt_apply 0 b)).mul_const (n:ℝ)).mul
    (((differentiableAt_const (1:ℝ)).sub hp0).pow (n-1))).mul hu0).sub hS

theorem fderiv_profileScore {R n c : ℕ} (hn : 2≤n) (hc : c≤R+1)
    (w : ℝ) (b : Fin (R+1)→ℝ) (hb : ∀i,0<b i)
    (hp : ∀i,kernelMarginal n c b i∈Ioo (0:ℝ) 1) (h : Fin (R+1)→ℝ) :
    fderiv ℝ (profileScore n c w) b h=profileScoreDerivative n c w b h := by
  let K := kernelMarginal (ι:=Fin (R+1)) n c
  let u := fun a=>fderiv ℝ K a (focalDirection R)
  have hK := contDiffAt_kernelMarginal_interior hn (by simpa using hc) b hb hp
  have hdK : DifferentiableAt ℝ K b := hK.differentiableAt (by simp)
  have hU : ContDiffAt ℝ 1 u b :=
    (hK.fderiv_right (m:=1) (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiffAt_const
  have hdU : DifferentiableAt ℝ u b := hU.differentiableAt (by norm_num)
  let curve := fun t : ℝ=>b+t • h
  have hcurve : HasDerivAt curve h 0 := by
    simpa [curve] using (((hasDerivAt_id (0:ℝ)).smul_const h).const_add b)
  have hcb : curve 0=b := by simp [curve]
  have hpc : HasDerivAt (fun t=>K (curve t)) (fderiv ℝ K b h) 0 := by
    have hh := HasFDerivAt.comp_hasDerivAt_of_eq (𝕜:=ℝ) (x:=(0:ℝ)) hdK.hasFDerivAt hcurve hcb.symm
    simpa only [Function.comp_def] using hh
  have huc : HasDerivAt (fun t=>u (curve t)) (fderiv ℝ u b h) 0 := by
    have hh := HasFDerivAt.comp_hasDerivAt_of_eq (𝕜:=ℝ) (x:=(0:ℝ)) hdU.hasFDerivAt hcurve hcb.symm
    simpa only [Function.comp_def] using hh
  have hp0 := hasDerivAt_pi.mp hpc 0
  have hu0 := hasDerivAt_pi.mp huc 0
  have hb0 := hasDerivAt_pi.mp hcurve 0
  have hz := ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub hp0).pow (n-1)
  have hS := (hasDerivAt_const (0:ℝ) (1:ℝ)).sub
    (((hasDerivAt_const (0:ℝ) (1:ℝ)).sub hp0).pow n)
  have hh := (((((hasDerivAt_const (0:ℝ) w).sub hb0).mul_const (n:ℝ)).mul hz).mul hu0).sub hS
  have hscore : HasDerivAt (fun t=>profileScore n c w (curve t))
      (profileScoreDerivative n c w b h) 0 := by
    convert hh using 1 <;> first | rfl |
      (simp only [hcb,Nat.sub_sub]; dsimp [profileScoreDerivative,K,u]; rw [hcb]; ring)
  have hd := HasFDerivAt.comp_hasDerivAt_of_eq (𝕜:=ℝ) (x:=(0:ℝ))
    (differentiableAt_profileScore hn hc w b hb hp).hasFDerivAt hcurve hcb.symm
  exact hd.unique hscore

theorem constant_second_focal_derivative {R n c : ℕ} (hn : 2≤n) (hc : c≤R+1)
    {B rho : ℝ} (hB : 0<B) (hrho : rho∈Ioo (0:ℝ) 1)
    (hcap : ((R:ℝ)+1)*rho=c) (h : Fin (R+1)→ℝ) :
    let K := kernelMarginal (ι:=Fin (R+1)) n c
    let M : ℝ := (R:ℝ)+1
    let a := H n rho/(B*Hslope n rho)
    let mu := (∑j,h j)/M
    fderiv ℝ (fun b=>fderiv ℝ K b (focalDirection R)) (fun _=>B) h 0 =
      sensitivity n B rho*(-Hslope n rho*a*((2-3/M)*h 0-(1-2/M)*mu)+
        B*Hcurvature n rho*a^2*(1-2/M)*(h 0-mu)) := by
  let K := kernelMarginal (ι:=Fin (R+1)) n c
  let M : ℝ := (R:ℝ)+1
  let a := H n rho/(B*Hslope n rho)
  let mu := (∑j,h j)/M
  let e := focalDirection R
  let v := secondReceiptForcing n (fun _=>B) (fun _=>rho) e h
    (fderiv ℝ K (fun _=>B) e) (fderiv ℝ K (fun _=>B) h)
  have hM : 0<M := by dsimp [M]; positivity
  have hD := Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩
  have hs : 0<sensitivity n B rho := sensitivity_pos hn hB ⟨hrho.1.le,hrho.2.le⟩
  have he : (∑j,e j)=1 := by simp [e,focalDirection,Fin.sum_univ_succ]
  have heh : (∑j,e j*h j)=h 0 := by simp [e,focalDirection,Fin.sum_univ_succ]
  have hbase : K (fun _=>B)=fun _=>rho :=
    kernelMarginal_constant hn (by simpa using hc) hB hrho (by simpa using hcap)
  have hp : ∀j,K (fun _=>B) j∈Ioo (0:ℝ) 1 := by simp only [hbase]; exact fun _=>hrho
  have hd (z : Fin (R+1)→ℝ) (j : Fin (R+1)) :
      fderiv ℝ K (fun _=>B) z j=a*(z j-(∑i,z i)/M) := by
    rw [fderiv_kernelMarginal_constant hn (by simpa using hc) hB hrho (by simpa using hcap)]
    simp only [smul_apply,sub_apply,ContinuousLinearMap.id_apply,Pi.smul_apply,
      Pi.sub_apply,smul_eq_mul,meanProjection_apply,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
    rfl
  have hv (j : Fin (R+1)) : v j=
      (-2*Hslope n rho*a+B*Hcurvature n rho*a^2)*(e j*h j)+
      (Hslope n rho*a-B*Hcurvature n rho*a^2)*mu*e j+
      (Hslope n rho*a-B*Hcurvature n rho*a^2)/M*h j+
      B*Hcurvature n rho*a^2/M*mu := by
    dsimp [v,secondReceiptForcing]
    rw [hd e j,hd h j,he]
    change -Hslope n rho*(e j*(a*(h j-mu))+h j*(a*(e j-1/M)))+
        B*Hcurvature n rho*(a*(e j-1/M))*(a*(h j-mu))=_
    ring
  have hvsum : (∑j,v j)=(-2*Hslope n rho*a+B*Hcurvature n rho*a^2)*(h 0-mu) := by
    simp_rw [hv]
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,he,heh,Nat.cast_add,Nat.cast_one]
    dsimp [mu,M]
    field_simp
    ring
  have havg : (∑j,sensitivity n B rho*v j)/(∑_j : Fin (R+1),sensitivity n B rho)=
      (∑j,v j)/M := by
    rw [← Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    dsimp [M]
    field_simp
  have hsecond := fderiv_fderiv_kernelMarginal_interior hn (by simpa using hc)
    (fun _ : Fin (R+1)=>B) (fun _=>hB) hp e h 0
  change _=sensitivity n B rho*(-Hslope n rho*a*((2-3/M)*h 0-(1-2/M)*mu)+
    B*Hcurvature n rho*a^2*(1-2/M)*(h 0-mu))
  change kernelMarginal n c (fun _ : Fin (R+1)=>B)=(fun _=>rho) at hbase
  rw [hsecond,hbase]
  change sensitivity n B rho*(v 0-(∑j,sensitivity n B rho*v j)/
    (∑_j : Fin (R+1),sensitivity n B rho))=_
  rw [havg,hvsum,hv]
  simp only [e,focalDirection,Fin.cons_zero]
  ring

theorem second_H_identity {n : ℕ} (hn : 2≤n) (p : ℝ) :
    2*Hslope n p-p*Hcurvature n p=((n:ℝ)-1)*(1-p)^(n-2) := by
  have he : (fun x : ℝ=>H n x-x*Hslope n x)=(fun x=>(1-x)^(n-1)) :=
    funext (H_sub_mul_Hslope (by omega))
  have hl := (hasDerivAt_H n p).sub ((hasDerivAt_id p).mul (hasDerivAt_Hslope n p))
  have hr := ((hasDerivAt_id p).const_sub 1).pow (n-1)
  change HasDerivAt (fun x : ℝ=>H n x-x*Hslope n x) _ p at hl
  rw [he] at hl
  have hh := hl.unique hr
  simp only [id_eq,Nat.sub_sub,Nat.cast_sub (show 1≤n by omega),Nat.cast_one] at hh
  linarith

theorem profileScore_reference_linearization {R n c : ℕ} (hn : 2≤n)
    (hc : c≤R+1) (hR : 0<R) {B rho w : ℝ} (hB : 0<B)
    (hrho : rho∈Ioo (0:ℝ) 1) (hcap : ((R:ℝ)+1)*rho=c)
    (hFOC : w*(1-rho)^(n-1)=B*(H n rho+rho/(R:ℝ)*Hslope n rho))
    (h : Fin (R+1)→ℝ) :
    fderiv ℝ (profileScore n c w) (fun _=>B) h =
      -referenceCurvature n R rho w B*h 0+
      (referenceCurvature n R rho w B-referenceCommonSensitivity n R rho w B)/(R:ℝ)*
        (∑j : Fin R,h j.succ) := by
  let K := kernelMarginal (ι:=Fin (R+1)) n c
  have hRreal : (0:ℝ)<R := by exact_mod_cast hR
  have hM : (0:ℝ)<(R:ℝ)+1 := by positivity
  have hD := Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩
  have hn1 : 0<(n:ℝ)-1 := by
    have hh : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    linarith
  have hz : 0<1-rho := sub_pos.mpr hrho.2
  have hF : 0<H n rho-rho*Hslope n rho := by
    rw [H_sub_mul_Hslope (by omega)]
    exact pow_pos hz _
  have hbase : K (fun _=>B)=fun _=>rho :=
    kernelMarginal_constant hn (by simpa using hc) hB hrho (by simpa using hcap)
  have hp : ∀j,K (fun _=>B) j∈Ioo (0:ℝ) 1 := by simp only [hbase]; exact fun _=>hrho
  have hd (z : Fin (R+1)→ℝ) : fderiv ℝ K (fun _=>B) z 0=
      H n rho/(B*Hslope n rho)*(z 0-(∑i,z i)/((R:ℝ)+1)) := by
    rw [fderiv_kernelMarginal_constant hn (by simpa using hc) hB hrho (by simpa using hcap)]
    simp only [smul_apply,sub_apply,ContinuousLinearMap.id_apply,Pi.smul_apply,
      Pi.sub_apply,smul_eq_mul,meanProjection_apply,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  have he : (∑j : Fin (R+1),focalDirection R j)=1 := by
    simp [focalDirection,Fin.sum_univ_succ]
  rw [fderiv_profileScore hn hc w (fun _=>B) (fun _=>hB) hp h]
  dsimp [profileScoreDerivative]
  change kernelMarginal n c (fun _ : Fin (R+1)=>B)=(fun _=>rho) at hbase
  rw [hbase,constant_second_focal_derivative hn hc hB hrho hcap h]
  dsimp only [K] at hd
  rw [hd h,hd (focalDirection R),he]
  simp only [focalDirection,Fin.cons_zero,Nat.cast_sub (show 1≤n by omega),Nat.cast_one]
  have hp1 : (1-rho)^(n-1)=H n rho-rho*Hslope n rho := (H_sub_mul_Hslope (by omega) rho).symm
  have hp2 : (1-rho)^(n-2)=(2*Hslope n rho-rho*Hcurvature n rho)/((n:ℝ)-1) :=
    (eq_div_iff hn1.ne').mpr (by nlinarith [second_H_identity hn rho])
  have hw : w=B*(H n rho+rho/(R:ℝ)*Hslope n rho)/(H n rho-rho*Hslope n rho) := by
    apply (eq_div_iff hF.ne').mpr
    simpa only [hp1] using hFOC
  unfold referenceCurvature referenceCommonSensitivity referenceOwnScale
  rw [hp1,hp2,hw,Fin.sum_univ_succ]
  dsimp [sensitivity]
  field_simp
  ring

theorem profileScore_constant_eq_zero {R n c : ℕ} (hn : 2≤n)
    (hc : c≤R+1) (hR : 0<R) {B rho w : ℝ} (hB : 0<B)
    (hrho : rho∈Ioo (0:ℝ) 1) (hcap : ((R:ℝ)+1)*rho=c)
    (hFOC : w*(1-rho)^(n-1)=B*(H n rho+rho/(R:ℝ)*Hslope n rho)) :
    profileScore (R:=R) n c w (fun _=>B)=0 := by
  have hRreal : (0:ℝ)<R := by exact_mod_cast hR
  have hM : (0:ℝ)<(R:ℝ)+1 := by positivity
  have hD := Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩
  have hz : 0<1-rho := sub_pos.mpr hrho.2
  have hF : 0<H n rho-rho*Hslope n rho := by
    rw [H_sub_mul_Hslope (by omega)]
    exact pow_pos hz _
  have hbase := kernelMarginal_constant (ι:=Fin (R+1)) hn (by simpa using hc) hB hrho
    (by simpa using hcap)
  have he : (∑j : Fin (R+1),focalDirection R j)=1 := by
    simp [focalDirection,Fin.sum_univ_succ]
  have hd : fderiv ℝ (kernelMarginal n c) (fun _ : Fin (R+1)=>B) (focalDirection R) 0=
      H n rho/(B*Hslope n rho)*(1-1/((R:ℝ)+1)) := by
    rw [fderiv_kernelMarginal_constant hn (by simpa using hc) hB hrho (by simpa using hcap)]
    simp only [smul_apply,sub_apply,ContinuousLinearMap.id_apply,Pi.smul_apply,
      Pi.sub_apply,smul_eq_mul,meanProjection_apply,Fintype.card_fin,Nat.cast_add,Nat.cast_one,he]
    rfl
  have hp1 : (1-rho)^(n-1)=H n rho-rho*Hslope n rho := (H_sub_mul_Hslope (by omega) rho).symm
  have hw : w=B*(H n rho+rho/(R:ℝ)*Hslope n rho)/(H n rho-rho*Hslope n rho) := by
    apply (eq_div_iff hF.ne').mpr
    simpa only [hp1] using hFOC
  dsimp only [profileScore]
  rw [hbase,hd,← H_mul n (by omega),hp1,hw]
  field_simp
  ring

theorem source_reference_linearization {R n c : ℕ} (hn : 2≤n)
    (hc : 1≤c) (hcR : c≤R) {w : ℝ} (hw : 0<w) (h : Fin (R+1)→ℝ) :
    let rho := density R c
    let B := referenceBid n R c w
    profileScore (R:=R) n c w (fun _=>B)=0 ∧
    fderiv ℝ (profileScore n c w) (fun _=>B) h =
      -referenceCurvature n R rho w B*h 0+
      (referenceCurvature n R rho w B-referenceCommonSensitivity n R rho w B)/(R:ℝ)*
        (∑j : Fin R,h j.succ) := by
  have hR : 0<R := by omega
  have hRreal : (0:ℝ)<R := by exact_mod_cast hR
  have hcreal : (1:ℝ)≤c := by exact_mod_cast hc
  have hcRreal : (c:ℝ)≤R := by exact_mod_cast hcR
  have hrho := density_bounds hRreal hcreal hcRreal
  have hB := (referenceBid_pos_lt hn hRreal hcreal hcRreal hw).1
  have hD := Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩
  have hH := H_pos n (by omega) (density R c) hrho.1.le hrho.2.le
  have hden : 0<H n (density R c)+density R c/(R:ℝ)*Hslope n (density R c) := by
    have hr : 0<density R c := hrho.1
    positivity
  have hcap : ((R:ℝ)+1)*density R c=c := by unfold density; field_simp
  have hFOC : w*(1-density R c)^(n-1)=referenceBid n R c w*
      (H n (density R c)+density R c/(R:ℝ)*Hslope n (density R c)) := by
    unfold referenceBid
    exact (div_mul_cancel₀ _ hden.ne').symm
  exact ⟨profileScore_constant_eq_zero hn (by omega) hR hB hrho hcap hFOC,
    profileScore_reference_linearization hn (by omega) hR hB hrho hcap hFOC h⟩

end FCAppendix.Existence.NarrowPayOnce
