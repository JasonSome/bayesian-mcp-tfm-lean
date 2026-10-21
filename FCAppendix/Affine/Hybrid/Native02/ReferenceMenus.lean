import FCAppendix.Affine.Hybrid.Native02.PrimitiveInput
import FCAppendix.Affine.Hybrid.Native02.ReferenceCountLimits
import FCAppendix.Affine.Hybrid.MenuLipschitz

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open Set MeasureTheory ProbabilityTheory Game Bayes Filter Topology

def broadcastReference (eta xi z v lam b : ℝ) : ℝ :=
  z*(v-b)+(1-z)*independentTwo eta v b (exposure xi lam b)
def singletonReference (xi z v lam b : ℝ) : ℝ :=
  (z/2+(1-z)*exposure xi lam b)*(v-b)

theorem broadcastReference_eq_two {eta xi z v lam b : ℝ}
    (heta : eta=1-2*xi) (hxi : 0< xi) (hxi1 : xi<1) (hb : 0< b)
    (hq : exposure xi lam b∈ Icc (0:ℝ) 1) :
    broadcastReference eta xi z v lam b=two xi z v lam (exposure xi lam b) := by
  have hden : 0<1-xi*exposure xi lam b := by nlinarith [hq.2]
  have hprice : lam/(1-xi*exposure xi lam b)=b := by
    apply (div_eq_iff hden.ne').2
    exact (mixed_receipt xi lam b hxi.ne' hb.ne').symm
  unfold broadcastReference two
  rw [independentTwo_eq_menu heta hxi.ne' hb.ne']
  simp only [two,zero_mul,sub_zero,one_mul,zero_add,hprice]

theorem singletonReference_eq_one {xi z v lam b : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (hb : 0< b)
    (hq : exposure xi lam b∈ Icc (0:ℝ) 1) :
    singletonReference xi z v lam b=one xi z v lam (exposure xi lam b) := by
  have hden : 0<1-xi*exposure xi lam b := by nlinarith [hq.2]
  have hprice : lam/(1-xi*exposure xi lam b)=b := by
    apply (div_eq_iff hden.ne').2
    exact (mixed_receipt xi lam b hxi.ne' hb.ne').symm
  simp only [singletonReference,one,hprice]

theorem broadcastReference_le_U2 {eta xi z v lam b : ℝ}
    (heta : eta=1-2*xi) (hxi : 0< xi) (hxi1 : xi<1) (hb : 0< b)
    (hq : exposure xi lam b∈ Icc (0:ℝ) 1) :
    broadcastReference eta xi z v lam b≤ Menus.U2 hxi hxi1 z lam v := by
  rw [broadcastReference_eq_two heta hxi hxi1 hb hq]
  exact le_unitMaximum _ _ _ hq

theorem singletonReference_le_U1 {xi z v lam b : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (hb : 0< b)
    (hq : exposure xi lam b∈ Icc (0:ℝ) 1) :
    singletonReference xi z v lam b≤ Menus.U1 hxi hxi1 z lam v := by
  rw [singletonReference_eq_one hxi hxi1 hb hq]
  exact le_unitMaximum _ _ _ hq

theorem broadcastReference_price_bound {eta xi z v lam lam' b L U W : ℝ}
    (hxi : 0< xi) (hL : 0< L) (hz0 : 0≤ z) (hz1 : z≤1)
    (hb : b∈ Icc L U) (hv : |v|≤ W)
    (hq : exposure xi lam b∈ Icc (0:ℝ) 1)
    (hq' : exposure xi lam' b∈ Icc (0:ℝ) 1) :
    |broadcastReference eta xi z v lam b-broadcastReference eta xi z v lam' b|≤
      (broadcastExposureModulus eta W U/(xi*L))*|lam-lam'| := by
  have hW : 0≤ W := (abs_nonneg v).trans hv
  have hU : 0< U := hL.trans_le (hb.1.trans hb.2)
  have hab : |b|≤ U := by rw [abs_of_pos (hL.trans_le hb.1)];exact hb.2
  have hpoly := independentTwo_lipschitz (eta := eta) hv hab hq hq'
  have heq : broadcastReference eta xi z v lam b-broadcastReference eta xi z v lam' b=
      (1-z)*(independentTwo eta v b (exposure xi lam b)-
        independentTwo eta v b (exposure xi lam' b)) := by unfold broadcastReference;ring
  rw [heq,abs_mul,abs_of_nonneg (sub_nonneg.mpr hz1)]
  calc
    _≤|independentTwo eta v b (exposure xi lam b)-
        independentTwo eta v b (exposure xi lam' b)| :=
      mul_le_of_le_one_left (abs_nonneg _) (by linarith)
    _≤ broadcastExposureModulus eta W U*|exposure xi lam b-exposure xi lam' b| := hpoly
    _≤ broadcastExposureModulus eta W U*(|lam-lam'|/(xi*L)) :=
      mul_le_mul_of_nonneg_left (exposure_abs_sub_price xi L b lam lam' hxi hL hb.1)
        (broadcastExposureModulus_nonneg hW hU.le)
    _=_ := by ring

theorem singletonReference_price_bound {xi z v lam lam' b L U W : ℝ}
    (hxi : 0< xi) (hL : 0< L) (hz0 : 0≤ z) (hz1 : z≤1)
    (hb : b∈ Icc L U) (hv : |v|≤ W) :
    |singletonReference xi z v lam b-singletonReference xi z v lam' b|≤
      ((W+U)/(xi*L))*|lam-lam'| := by
  have hab : |b|≤ U := by rw [abs_of_pos (hL.trans_le hb.1)];exact hb.2
  have heq : singletonReference xi z v lam b-singletonReference xi z v lam' b=
      (1-z)*((v-b)*exposure xi lam b-(v-b)*exposure xi lam' b) := by
    unfold singletonReference;ring
  rw [heq,abs_mul,abs_of_nonneg (sub_nonneg.mpr hz1)]
  calc
    _≤|(v-b)*exposure xi lam b-(v-b)*exposure xi lam' b| :=
      mul_le_of_le_one_left (abs_nonneg _) (by linarith)
    _≤(W+U)*|exposure xi lam b-exposure xi lam' b| := singleton_exposure_lipschitz hv hab
    _≤(W+U)*(|lam-lam'|/(xi*L)) :=
      mul_le_mul_of_nonneg_left (exposure_abs_sub_price xi L b lam lam' hxi hL hb.1)
        (add_nonneg ((abs_nonneg v).trans hv) ((abs_nonneg b).trans hab))
    _=_ := by ring

theorem M1_price_bound {xi lam lam' v : ℝ} (hxi : 0< xi) (hxi1 : xi<1) :
    |Menus.M1 hxi hxi1 lam v-Menus.M1 hxi hxi1 lam' v|≤|lam-lam'|/(1-xi) := by
  have hdir (l l' : ℝ) : Menus.M1 hxi hxi1 l v-Menus.M1 hxi hxi1 l' v≤|l-l'|/(1-xi) := by
    let q:=unitArgmax (outsideOneAt xi v l) (continuousOn_M1_unit hxi hxi1 v l)
    have hq:= (unitArgmax_spec (outsideOneAt xi v l) (continuousOn_M1_unit hxi hxi1 v l)).1
    have hm:=le_unitMaximum (outsideOneAt xi v l') (continuousOn_M1_unit hxi hxi1 v l') q hq
    have hd:=outsideOneAt_multiplier_lipschitz (xi:=xi) (v:=v) (lam:=l) (lam':=l') hxi hxi1 hq
    change outsideOneAt xi v l' q ≤ Menus.M1 hxi hxi1 l' v at hm
    change |outsideOneAt xi v l q-outsideOneAt xi v l' q| ≤ _ at hd
    change outsideOneAt xi v l q-Menus.M1 hxi hxi1 l' v≤ _
    linarith [le_abs_self (outsideOneAt xi v l q-outsideOneAt xi v l' q)]
  rw [abs_le]
  exact ⟨by have hh:=hdir lam' lam;rw [abs_sub_comm lam' lam] at hh;linarith,hdir lam lam'⟩

theorem M2_price_bound {v lam lam' : ℝ} (hv : 0< v)
    (hl : lam∈ Icc (0:ℝ) v) (hl' : lam'∈ Icc (0:ℝ) v) :
    |outsideTwo v lam-outsideTwo v lam'|≤2*|lam-lam'| := by
  have heq : outsideTwo v lam-outsideTwo v lam'=(lam-lam')*(lam+lam'-2*v)/v := by
    unfold outsideTwo;ring
  have hfactor : |lam+lam'-2*v|≤2*v := by
    rw [abs_le];constructor <;> linarith [hl.1,hl.2,hl'.1,hl'.2]
  rw [heq,abs_div,abs_mul,abs_of_pos hv]
  apply (div_le_iff₀ hv).2
  have hh:=mul_le_mul_of_nonneg_left hfactor (abs_nonneg (lam-lam'))
  nlinarith

namespace PrimitiveInput
variable (p : PrimitiveInput)

theorem exposure_beta (v : p.Value) : exposure p.xi p.lam (p.beta v)=p.q v := by
  have hprod : p.xi*p.q v≤ p.xi := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (p.q_mem v).2 p.xi_pos.le
  have hd : 0<1-p.xi*p.q v := sub_pos.mpr (hprod.trans_lt p.xi_lt_one)
  unfold exposure beta
  field_simp [p.lam_pos.ne',p.xi_pos.ne',hd.ne']
  ring

theorem broadcastReference_beta (v : p.Value) :
    broadcastReference p.eta p.xi p.z v.1 p.lam (p.beta v)=
      Menus.U2 p.xi_pos p.xi_lt_one p.z p.lam v.1 := by
  have hprod : p.xi*p.q v≤ p.xi := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (p.q_mem v).2 p.xi_pos.le
  have hd : 0<1-p.xi*p.q v := sub_pos.mpr (hprod.trans_lt p.xi_lt_one)
  have hb : 0< p.beta v := div_pos p.lam_pos hd
  rw [broadcastReference_eq_two (by dsimp [xi];ring) p.xi_pos p.xi_lt_one hb
    (by rw [p.exposure_beta];exact p.q_mem v),p.exposure_beta]
  exact p.target_value v

end PrimitiveInput
end FCAppendix.Affine.Hybrid.Native02
