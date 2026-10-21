import FCAppendix.Affine.Hybrid.Native02.GlobalDeviations

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open Set Filter Topology

def unitArgmax (f : ℝ→ℝ) (hf : ContinuousOn f (Icc (0:ℝ) 1)) : ℝ :=
  Classical.choose (isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one) hf)

theorem unitArgmax_spec (f : ℝ→ℝ) (hf : ContinuousOn f (Icc (0:ℝ) 1)) :
    unitArgmax f hf∈ Icc (0:ℝ) 1 ∧
      ∀ q∈ Icc (0:ℝ) 1,f q≤ f (unitArgmax f hf) := by
  have h := Classical.choose_spec
    (isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one) hf)
  exact ⟨h.1,fun q hq=> h.2 hq⟩

def unitMaximum (f : ℝ→ℝ) (hf : ContinuousOn f (Icc (0:ℝ) 1)) : ℝ := f (unitArgmax f hf)

theorem le_unitMaximum (f : ℝ→ℝ) (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (q : ℝ) (hq : q∈ Icc (0:ℝ) 1) : f q≤ unitMaximum f hf :=
  (unitArgmax_spec f hf).2 q hq

theorem unitMaximum_eq_of_maximizer (f : ℝ→ℝ) (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (q : ℝ) (hq : q∈ Icc (0:ℝ) 1) (hmax : ∀ r∈ Icc (0:ℝ) 1,f r≤ f q) :
    unitMaximum f hf=f q :=
  le_antisymm (hmax _ (unitArgmax_spec f hf).1) (le_unitMaximum f hf q hq)

theorem unitEnvelope_lipschitz (f : ℝ→ℝ→ℝ)
    (hf : ∀ v,ContinuousOn (f v) (Icc (0:ℝ) 1))
    (slope : ℝ→ℝ) (hs : ∀ q∈ Icc (0:ℝ) 1,slope q∈ Icc (0:ℝ) 1)
    (hlinear : ∀ v w q,q∈ Icc (0:ℝ) 1→ f v q-f w q=slope q*(v-w)) :
    LipschitzWith 1 (fun v=> unitMaximum (f v) (hf v)) := by
  have hle (v w : ℝ) : unitMaximum (f v) (hf v)-unitMaximum (f w) (hf w)≤|v-w| := by
    let q := unitArgmax (f v) (hf v)
    have hq := (unitArgmax_spec (f v) (hf v)).1
    have hw := le_unitMaximum (f w) (hf w) q hq
    have he := hlinear v w q hq
    have hb : slope q*(v-w)≤|v-w| := by
      exact (mul_le_mul_of_nonneg_left (le_abs_self (v-w)) (hs q hq).1).trans
        (mul_le_of_le_one_left (abs_nonneg _) (hs q hq).2)
    change f v q-unitMaximum (f w) (hf w)≤ _
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.dist_eq,Real.dist_eq,NNReal.coe_one,one_mul,abs_le]
  exact ⟨by have hh:=hle w v;rw [abs_sub_comm w v] at hh;linarith,hle v w⟩

theorem continuousOn_unit_cost {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1) (lam : ℝ) :
    ContinuousOn (fun q : ℝ=> lam/(1-xi*q)) (Icc (0:ℝ) 1) := by
  apply continuousOn_const.div
    (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
  intro q hq
  have : 0<1-xi*q := by nlinarith [hq.2]
  exact this.ne'

theorem continuousOn_two_unit {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1) (z v lam : ℝ) :
    ContinuousOn (two xi z v lam) (Icc (0:ℝ) 1) := by
  unfold two
  exact (continuousOn_const.mul
    (continuousOn_const.sub (continuousOn_unit_cost hxi hxi1 lam))).add
    (continuousOn_const.mul
      ((continuousOn_const.mul
        ((continuousOn_const.mul continuousOn_id).sub (continuousOn_id.pow 2))).sub
        (continuousOn_const.mul continuousOn_id)))

theorem continuousOn_one_unit {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1) (z v lam : ℝ) :
    ContinuousOn (one xi z v lam) (Icc (0:ℝ) 1) := by
  unfold one
  exact (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).mul
    (continuousOn_const.sub (continuousOn_unit_cost hxi hxi1 lam))

theorem continuousOn_M1_unit {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1) (v lam : ℝ) :
    ContinuousOn (outsideOneAt xi v lam) (Icc (0:ℝ) 1) :=
  continuousOn_id.mul (continuousOn_const.sub (continuousOn_unit_cost hxi hxi1 lam))

namespace Menus
variable {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1) (z lam : ℝ)

def U2 (v : ℝ) : ℝ := unitMaximum (two xi z v lam) (continuousOn_two_unit hxi hxi1 z v lam)
def U1 (v : ℝ) : ℝ := unitMaximum (one xi z v lam) (continuousOn_one_unit hxi hxi1 z v lam)
def M1 (v : ℝ) : ℝ := unitMaximum (outsideOneAt xi v lam) (continuousOn_M1_unit hxi hxi1 v lam)

theorem M1_nonneg (v : ℝ) : 0≤ M1 hxi hxi1 lam v := by
  have h := le_unitMaximum (outsideOneAt xi v lam) (continuousOn_M1_unit hxi hxi1 v lam)
    0 ⟨le_rfl,zero_le_one⟩
  simpa only [outsideOneAt,zero_mul,M1] using h

theorem U2_continuous (hz0 : 0≤ z) (hz1 : z≤1) : Continuous (U2 hxi hxi1 z lam) := by
  apply (unitEnvelope_lipschitz (fun v q=> two xi z v lam q)
    (fun v=> continuousOn_two_unit hxi hxi1 z v lam)
    (fun q=> z+(1-z)*(2*q-q^2)) ?_ ?_).continuous
  · intro q hq
    have hqq0 : 0≤2*q-q^2 := by nlinarith [mul_nonneg hq.1 (sub_nonneg.mpr hq.2)]
    have hqq1 : 2*q-q^2≤1 := by nlinarith [sq_nonneg (1-q)]
    constructor
    · exact add_nonneg hz0 (mul_nonneg (sub_nonneg.mpr hz1) hqq0)
    · nlinarith [mul_nonneg (sub_nonneg.mpr hz1) (sub_nonneg.mpr hqq1)]
  · intro v w q hq
    unfold two
    ring

theorem U1_continuous (hz0 : 0≤ z) (hz1 : z≤1) : Continuous (U1 hxi hxi1 z lam) := by
  apply (unitEnvelope_lipschitz (fun v q=> one xi z v lam q)
    (fun v=> continuousOn_one_unit hxi hxi1 z v lam)
    (fun q=> z/2+(1-z)*q) ?_ ?_).continuous
  · intro q hq
    constructor
    · exact add_nonneg (div_nonneg hz0 (by norm_num))
        (mul_nonneg (sub_nonneg.mpr hz1) hq.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr hz1) (sub_nonneg.mpr hq.2)]
  · intro v w q hq
    unfold one
    ring

theorem M1_continuous : Continuous (M1 hxi hxi1 lam) := by
  exact (unitEnvelope_lipschitz (fun v q=> outsideOneAt xi v lam q)
    (fun v=> continuousOn_M1_unit hxi hxi1 v lam) id (fun _ h=> h)
    (by intros;unfold outsideOneAt;simp only [id_eq];ring)).continuous

theorem U2_zero_eq (hlam : 0< lam) (v : ℝ) (hlv : lam< v) :
    U2 hxi hxi1 0 lam v=outsideTwo v lam := by
  have hv := hlam.trans hlv
  obtain ⟨hq,heq,hmax⟩ := two_zero_max (xi:=xi) hv hlam hlv
  rw [U2,unitMaximum_eq_of_maximizer _ _ _ ⟨hq.1.le,hq.2.le⟩]
  · exact heq
  · intro q hq'
    rw [heq]
    exact hmax q

theorem active_compact_margin (hz0 : 0≤ z) (hz1 : z≤1)
    (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty) (R : ℝ)
    (h1 : ∀ v∈ K,U1 hxi hxi1 z lam v< U2 hxi hxi1 z lam v)
    (hM : ∀ v∈ K,M1 hxi hxi1 lam v< U2 hxi hxi1 z lam v)
    (hR : ∀ v∈ K,v-R< U2 hxi hxi1 z lam v) :
    ∃delta>0,∀ v∈ K,
      max (U1 hxi hxi1 z lam v) (max (M1 hxi hxi1 lam v) (v-R))+delta≤
        U2 hxi hxi1 z lam v := by
  apply compact_strict_margin hK hne (U2_continuous hxi hxi1 z lam hz0 hz1).continuousOn
    (((U1_continuous hxi hxi1 z lam hz0 hz1).max
      ((M1_continuous hxi hxi1 lam).max (continuous_id.sub continuous_const))).continuousOn)
  intro v hv
  exact max_lt (h1 v hv) (max_lt (hM v hv) (hR v hv))

theorem active_M2_compact_margin (hz0 : 0≤ z) (hz1 : z≤1)
    (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty)
    (hpositive : ∀ v∈ K,0< v)
    (hstrict : ∀ v∈ K,outsideTwo v lam< U2 hxi hxi1 z lam v) :
    ∃delta>0,∀ v∈ K,outsideTwo v lam+delta≤ U2 hxi hxi1 z lam v := by
  have he : ContinuousOn (fun v=> outsideTwo v lam) K := by
    unfold outsideTwo
    exact ((continuousOn_id.sub continuousOn_const).pow 2).div continuousOn_id
      (fun v hv=>(hpositive v hv).ne')
  exact compact_strict_margin hK hne
    (U2_continuous hxi hxi1 z lam hz0 hz1).continuousOn he hstrict

theorem upper_compact_margin (hz0 : 0≤ z) (hz1 : z≤1)
    (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty)
    (hpositive : ∀ v∈ K,0< v) (R : ℝ)
    (h2 : ∀ v∈ K,U2 hxi hxi1 z lam v< v-R)
    (h1 : ∀ v∈ K,U1 hxi hxi1 z lam v< v-R)
    (hM : ∀ v∈ K,M1 hxi hxi1 lam v< v-R)
    (hE : ∀ v∈ K,outsideTwo v lam< v-R) :
    ∃delta>0,∀ v∈ K,
      max (U2 hxi hxi1 z lam v)
        (max (U1 hxi hxi1 z lam v) (max (M1 hxi hxi1 lam v) (outsideTwo v lam)))+delta≤ v-R := by
  have he : ContinuousOn (fun v=> outsideTwo v lam) K := by
    unfold outsideTwo
    exact ((continuousOn_id.sub continuousOn_const).pow 2).div continuousOn_id
      (fun v hv=>(hpositive v hv).ne')
  apply compact_strict_margin hK hne (continuous_id.sub continuous_const).continuousOn
    (ContinuousOn.sup (U2_continuous hxi hxi1 z lam hz0 hz1).continuousOn
      (ContinuousOn.sup (U1_continuous hxi hxi1 z lam hz0 hz1).continuousOn
        (ContinuousOn.sup (M1_continuous hxi hxi1 lam).continuousOn he)))
  intro v hv
  exact max_lt (h2 v hv) (max_lt (h1 v hv) (max_lt (hM v hv) (hE v hv)))

theorem upper_start_from_source_guard (K : Set ℝ) (hK : IsCompact K)
    (hne : K.Nonempty) (R : ℝ)
    (hM : ∀ v∈ K,M1 hxi hxi1 lam v< v-R) :
    ∃t∈ K,R< t ∧ ∀ v∈ K,t≤ v := by
  obtain ⟨t,ht,hmin⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
  refine ⟨t,ht,?_,?_⟩
  · have hh := (M1_nonneg hxi hxi1 lam t).trans_lt (hM t ht)
    linarith
  · intro v hv
    exact hmin hv

end Menus
end FCAppendix.Affine.Hybrid.Native02
