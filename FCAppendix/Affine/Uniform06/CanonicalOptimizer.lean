import FCAppendix.Affine.Uniform06.SourceCanonicalRegularity
import FCAppendix.Affine.Uniform06.EntrySourceGap

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.CanonicalOptimizer

open Set Filter Topology

def one (C : ℝ → ℝ) (v b : ℝ) : ℝ := (v-b)*C b
def two (η : ℝ) (C R : ℝ → ℝ) (v b : ℝ) : ℝ :=
  (v-b)*(2*C b-R b)-η*b*R b

def Optimal (C : ℝ → ℝ) (v b : ℝ) : Prop :=
  b ∈ Icc (0:ℝ) v ∧ ∀ a ∈ Icc (0:ℝ) v,one C v a ≤ one C v b

theorem exists_interior {C : ℝ → ℝ} {lo d v H : ℝ}
    (hlo : 0 < lo) (hld : lo < d) (hdv : d < v) (hvH : v ≤ H)
    (hnon : ∀ b,0 ≤ C b) (hmono : MonotoneOn C (Icc (0:ℝ) H))
    (hcont : ContinuousOn C (Icc lo H)) (hd : 0 < C d)
    (hbeat : v*C lo < (v-d)*C d) :
    ∃ b,Optimal C v b ∧ lo < b ∧ b < v ∧ 0 < one C v b := by
  have hC : ContinuousOn (one C v) (Icc lo v) :=
    (continuous_const.sub continuous_id).continuousOn.mul
      (hcont.mono (fun _ hx => ⟨hx.1,hx.2.trans hvH⟩))
  obtain ⟨b,hb,hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨d,⟨hld.le,hdv.le⟩⟩ hC
  have hpos : 0 < one C v b :=
    (mul_pos (sub_pos.mpr hdv) hd).trans_le (hmax ⟨hld.le,hdv.le⟩)
  have hsmall (a : ℝ) (ha : a ∈ Icc (0:ℝ) lo) :
      one C v a < one C v b := by
    have hCa := hmono ⟨ha.1,ha.2.trans (hld.le.trans (hdv.le.trans hvH))⟩
      ⟨hlo.le,hld.le.trans (hdv.le.trans hvH)⟩ ha.2
    have hv0 : 0 ≤ v := hlo.le.trans (hld.le.trans hdv.le)
    have hu : one C v a ≤ v*C lo := by
      unfold one
      calc
        _ ≤ v*C a := mul_le_mul_of_nonneg_right (by linarith only [ha.1]) (hnon a)
        _ ≤ v*C lo := mul_le_mul_of_nonneg_left hCa hv0
    exact (hu.trans_lt hbeat).trans_le (hmax ⟨hld.le,hdv.le⟩)
  have hleft : lo < b := by
    by_contra hn
    exact (lt_irrefl (one C v b)) (hsmall b ⟨hlo.le.trans hb.1,le_of_not_gt hn⟩)
  have hright : b < v := by
    apply lt_of_le_of_ne hb.2
    intro he
    rw [he,one,sub_self,zero_mul] at hpos
    exact lt_irrefl _ hpos
  refine ⟨b,⟨⟨hlo.le.trans hb.1,hb.2⟩,?_⟩,hleft,hright,hpos⟩
  intro a ha
  rcases le_total a lo with hal | hla
  · exact (hsmall a ⟨ha.1,hal⟩).le
  · exact hmax ⟨hla,ha.2⟩

theorem rent_lt_of_amplification {C : ℝ → ℝ} {v b e G : ℝ}
    (hopt : Optimal C v b) (hC : 0 < C b) (he : 0 < e)
    (hG : v < e*G) (hamp : b+e ≤ v → G*C b ≤ C (b+e)) :
    v-b < 2*e := by
  by_contra hn
  have hr : 2*e ≤ v-b := le_of_not_gt hn
  have hraise : b+e ≤ v := by linarith
  have hgain := hamp hraise
  have hG0 : 0 < G := by
    have hv : 0 ≤ v := hopt.1.1.trans hopt.1.2
    nlinarith
  have hraiseC : 0 < C (b+e) := (mul_pos hG0 hC).trans_le hgain
  have hnew : one C v b < one C v (b+e) := by
    unfold one
    calc
      (v-b)*C b ≤ v*C b :=
        mul_le_mul_of_nonneg_right (by linarith [hopt.1.1]) hC.le
      _ < (e*G)*C b := mul_lt_mul_of_pos_right hG hC
      _ = e*(G*C b) := by ring
      _ ≤ e*C (b+e) := mul_le_mul_of_nonneg_left hgain he.le
      _ ≤ (v-(b+e))*C (b+e) :=
        mul_le_mul_of_nonneg_right (by linarith) hraiseC.le
  exact (not_lt_of_ge (hopt.2 (b+e) ⟨by linarith [hopt.1.1],hraise⟩)) hnew

theorem finite_FOC {C : ℝ → ℝ} {v b d : ℝ}
    (hopt : Optimal C v b) (hb : 0 < b) (hbv : b < v)
    (hd : HasDerivAt C d b) : C b = (v-b)*d := by
  have hmax : IsLocalMax (one C v) b := by
    filter_upwards [Ioo_mem_nhds hb hbv] with a ha
    exact hopt.2 a ⟨ha.1.le,ha.2.le⟩
  exact EntryOptimizer.singleton_FOC_of_localMax C v b d hd hmax

theorem relative_advantage_identity {η v b d : ℝ} {C R : ℝ → ℝ}
    (hbv : b < v) (hC : 0 < C b) (hFOC : C b = (v-b)*d) :
    (two η C R v b-one C v b)/one C v b =
      1-R b/C b-η*(b*(d/C b)*(R b/C b)) := by
  have hvb : v-b ≠ 0 := (sub_pos.mpr hbv).ne'
  have hc : C b ≠ 0 := hC.ne'
  have hd : d = C b/(v-b) := (eq_div_iff hvb).mpr (by linarith [hFOC])
  rw [hd]
  unfold one two
  field_simp [hvb,hc]
  ring

theorem relative_advantage_tendsto (η ξ : ℝ) (_hξ : 0 < ξ)
    (C R : ℕ → ℝ → ℝ) (v b d : ℕ → ℝ)
    (hfinite : ∀ᶠ n in atTop,b n < v n ∧ 0 < C n (b n) ∧
      C n (b n)=(v n-b n)*d n)
    (hr : Tendsto (fun n => R n (b n)/C n (b n)) atTop (𝓝 0))
    (hbr : Tendsto (fun n => b n*(d n/C n (b n))*(R n (b n)/C n (b n)))
      atTop (𝓝 (2/ξ))) :
    Tendsto (fun n => (two η (C n) (R n) (v n) (b n)-
      one (C n) (v n) (b n))/one (C n) (v n) (b n))
      atTop (𝓝 (1-2*η/ξ)) := by
  have ht := ((tendsto_const_nhds (x := (1:ℝ))).sub hr).sub (hbr.const_mul η)
  have he : (1:ℝ)-0-η*(2/ξ)=1-2*η/ξ := by ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [hfinite] with n hn
  exact (relative_advantage_identity hn.1 hn.2.1 hn.2.2).symm

theorem source_factor_pos (i : Uniform07.Row) :
    0 < 1-2*Uniform07.eta i/Uniform07.xi i := by
  cases i <;> norm_num [Uniform07.eta,Uniform07.etaQ,Uniform07.xi,Uniform07.xiQ]

theorem full_menu_transfer (C R single broadcast : ℝ → ℝ)
    {η v b E F : ℝ} (hopt : Optimal C v b)
    (hsingle : ∀ a ∈ Icc (0:ℝ) v,single a ≤ one C v a+E)
    (hbroadcast : two η C R v b-F ≤ broadcast b)
    (hpay : E+F < two η C R v b-one C v b) :
    ∀ a ∈ Icc (0:ℝ) v,single a < broadcast b := by
  intro a ha
  have hm := hopt.2 a ha
  have hs := hsingle a ha
  linarith

end FCAppendix.Affine.Uniform06.CanonicalOptimizer
