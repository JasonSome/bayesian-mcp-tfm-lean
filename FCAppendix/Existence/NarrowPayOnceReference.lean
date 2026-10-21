import FCAppendix.PayOnce.AnalyticalKernel
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology Finset
open PayOnce PayOnce.OwnImpact CommonList
open scoped BigOperators

def residual (R c p : ℝ) : ℝ := (c-p)/R
def density (R c : ℝ) : ℝ := c/(R+1)
def referenceBid (n : ℕ) (R c w : ℝ) : ℝ :=
  w*(1-density R c)^(n-1)/(H n (density R c)+density R c/R*Hslope n (density R c))
def referenceUtility (n : ℕ) (R c w B p : ℝ) : ℝ :=
  w*success n p-(n:ℝ)*B*p*H n (residual R c p)
def referenceScore (n : ℕ) (R c w B p : ℝ) : ℝ :=
  (n:ℝ)*(w*(1-p)^(n-1)-B*(H n (residual R c p)+p/R*Hslope n (residual R c p)))

theorem residual_bounds {R c p : ℝ} (hR : 0<R) (hc : 1 ≤ c) (hcR : c ≤ R)
    (hp : p ∈ Icc (0:ℝ) 1) : residual R c p ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact div_nonneg (by linarith [hp.2]) hR.le
  · exact (div_le_one hR).mpr (by linarith [hp.1])

theorem density_bounds {R c : ℝ} (hR : 0<R) (hc : 1 ≤ c) (hcR : c ≤ R) :
    density R c ∈ Ioo (0:ℝ) 1 := by
  constructor
  · exact div_pos (by linarith) (by linarith)
  · exact (div_lt_one (by linarith)).mpr (by linarith)

theorem residual_density {R c : ℝ} (hR : 0<R) : residual R c (density R c)=density R c := by
  unfold residual density
  field_simp
  ring

theorem Hslope_antitone (n : ℕ) {x y : ℝ} (hxy : x ≤ y) (hy1 : y ≤ 1) :
    Hslope n y ≤ Hslope n x := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (power_mono (sub_nonneg.mpr hy1) (by linarith) (j-1))
    (Nat.cast_nonneg j)

theorem H_ge_last (n : ℕ) (hn : 0<n) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    (1-p)^(n-1) ≤ H n p := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  apply (le_div_iff₀ hnR).mpr
  calc
    _ = ∑ _j ∈ range n, (1-p)^(n-1) := by simp [mul_comm]
    _ ≤ _ := sum_le_sum fun j hj => pow_le_pow_of_le_one
      (sub_nonneg.mpr hp.2) (by linarith [hp.1]) (by have := mem_range.mp hj; omega)

theorem referenceBid_pos_lt {n : ℕ} (hn : 2 ≤ n) {R c w : ℝ}
    (hR : 0<R) (hc : 1 ≤ c) (hcR : c ≤ R) (hw : 0<w) :
    0<referenceBid n R c w ∧ referenceBid n R c w<w := by
  have hp := density_bounds hR hc hcR
  have hH := H_pos n (by omega) _ hp.1.le hp.2.le
  have hD := Hslope_pos hn ⟨hp.1.le,hp.2.le⟩
  have hcor : 0<density R c/R*Hslope n (density R c) := mul_pos (div_pos hp.1 hR) hD
  have hden : 0<H n (density R c)+density R c/R*Hslope n (density R c) := by positivity
  constructor
  · exact div_pos (mul_pos hw (pow_pos (sub_pos.mpr hp.2) _)) hden
  · apply (div_lt_iff₀ hden).mpr
    have hlast := H_ge_last n (by omega) ⟨hp.1.le,hp.2.le⟩
    nlinarith

theorem hasDerivAt_referenceUtility (n : ℕ) (R c w B p : ℝ) :
    HasDerivAt (referenceUtility n R c w B) (referenceScore n R c w B p) p := by
  have hq : HasDerivAt (residual R c) (-1/R) p := by
    exact ((hasDerivAt_id p).const_sub c).div_const R
  have hS : HasDerivAt (success n) ((n:ℝ)*(1-p)^(n-1)) p := by
    convert (((hasDerivAt_id p).const_sub 1).pow n).const_sub 1 using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have h := (hS.const_mul w).sub
    (((hasDerivAt_id p).const_mul ((n:ℝ)*B)).mul ((hasDerivAt_H n _).comp p hq))
  convert h using 1 <;> first | rfl | (dsimp [referenceScore]; ring)

theorem referenceScore_strictAntiOn {n : ℕ} (hn : 2 ≤ n) {R c w B : ℝ}
    (hR : 0<R) (hc : 1 ≤ c) (hcR : c ≤ R) (hw : 0 ≤ w) (hB : 0<B) :
    StrictAntiOn (referenceScore n R c w B) (Icc 0 1) := by
  intro x hx y hy hxy
  have hqx := residual_bounds hR hc hcR hx
  have hqy := residual_bounds hR hc hcR hy
  have hq : residual R c y<residual R c x := (div_lt_div_iff_of_pos_right hR).mpr (by linarith)
  have hH := H_strict n hn _ _ hq hqx.2
  have hD := Hslope_antitone n hq.le hqx.2
  have hD0 := (Hslope_pos hn hqx).le
  have hcost : H n (residual R c x)+x/R*Hslope n (residual R c x)<
      H n (residual R c y)+y/R*Hslope n (residual R c y) := by
    have hmult := mul_le_mul (div_le_div_of_nonneg_right hxy.le hR.le) hD
      hD0 (div_nonneg hy.1 hR.le)
    linarith
  have hpow : (1-y)^(n-1) ≤ (1-x)^(n-1) :=
    power_mono (sub_nonneg.mpr hy.2) (by linarith) (n-1)
  have hgain := mul_le_mul_of_nonneg_left hpow hw
  have hcostB := mul_lt_mul_of_pos_left hcost hB
  unfold referenceScore
  exact mul_lt_mul_of_pos_left (by linarith) (by exact_mod_cast (show 0<n by omega))

theorem referenceScore_at_density {n : ℕ} (hn : 2 ≤ n) {R c w : ℝ}
    (hR : 0<R) (hc : 1 ≤ c) (hcR : c ≤ R) :
    referenceScore n R c w (referenceBid n R c w) (density R c)=0 := by
  have hp := density_bounds hR hc hcR
  have hden : H n (density R c)+density R c/R*Hslope n (density R c)≠0 := by
    exact (add_pos (H_pos n (by omega) _ hp.1.le hp.2.le)
      (mul_pos (div_pos hp.1 hR) (Hslope_pos hn ⟨hp.1.le,hp.2.le⟩))).ne'
  unfold referenceScore
  rw [residual_density hR,referenceBid,div_mul_cancel₀ _ hden,sub_self,mul_zero]

theorem referenceUtility_strict_global {n : ℕ} (hn : 2 ≤ n) {R c w : ℝ}
    (hR : 0<R) (hc : 1 ≤ c) (hcR : c ≤ R) (hw : 0<w)
    {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) (hne : p≠density R c) :
    referenceUtility n R c w (referenceBid n R c w) p<
      referenceUtility n R c w (referenceBid n R c w) (density R c) := by
  let B := referenceBid n R c w
  let U := referenceUtility n R c w B
  have hrho := density_bounds hR hc hcR
  have hB := (referenceBid_pos_lt hn hR hc hcR hw).1
  have hanti := referenceScore_strictAntiOn hn hR hc hcR hw.le hB
  have hz := referenceScore_at_density hn (w:=w) hR hc hcR
  have hcont : Continuous U := continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_referenceUtility n R c w B x).continuousAt
  have hleft : StrictMonoOn U (Icc 0 (density R c)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_referenceUtility n R c w B x).deriv]
    have hh := hanti ⟨hx.1.le,hx.2.le.trans hrho.2.le⟩ ⟨hrho.1.le,hrho.2.le⟩ hx.2
    change referenceScore n R c w B (density R c)=0 at hz
    linarith
  have hright : StrictAntiOn U (Icc (density R c) 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_referenceUtility n R c w B x).deriv]
    have hh := hanti ⟨hrho.1.le,hrho.2.le⟩ ⟨hrho.1.le.trans hx.1.le,hx.2.le⟩ hx.1
    change referenceScore n R c w B (density R c)=0 at hz
    linarith
  rcases lt_or_gt_of_ne hne with hl | hr
  · exact hleft ⟨hp.1,hl.le⟩ ⟨hrho.1.le,le_rfl⟩ hl
  · exact hright ⟨le_rfl,hrho.2.le⟩ ⟨hr.le,hp.2⟩ hr

theorem referenceUtility_at_density {n : ℕ} (hn : 2 ≤ n) {R c w : ℝ} (hR : 0<R) :
    referenceUtility n R c w (referenceBid n R c w) (density R c)=
      (w-referenceBid n R c w)*success n (density R c) := by
  rw [referenceUtility,residual_density hR]
  have hh := H_mul n (by omega) (density R c)
  linear_combination -referenceBid n R c w*hh

theorem referenceUtility_nonneg {n : ℕ} (hn : 2 ≤ n) {R c w : ℝ}
    (hR : 0<R) (hc : 1 ≤ c) (hcR : c ≤ R) (hw : 0<w) :
    0<referenceUtility n R c w (referenceBid n R c w) (density R c) := by
  have hh := referenceUtility_strict_global hn hR hc hcR hw (p:=0) ⟨le_rfl,zero_le_one⟩
    (density_bounds hR hc hcR).1.ne
  simpa only [referenceUtility,success,sub_zero,one_pow,sub_self,mul_zero,zero_mul] using hh

theorem reference_allocation_at_bid {n r c : ℕ} (hn : 2 ≤ n) (hc : 1 ≤ c)
    (hcr : c ≤ r+1) {w : ℝ} (hw : 0<w) :
    AnalyticalKernel.allocation n c hn (show c ≤ Fintype.card (Fin (r+1))+1 by simpa using hcr.trans (Nat.le_succ _))
      (fun _ : Fin (r+1) => referenceBid n (r+1) c w) (referenceBid n (r+1) c w)=
      density (r+1) c := by
  have hR : (0:ℝ)<(r:ℝ)+1 := by positivity
  have hcR : (c:ℝ) ≤ (r:ℝ)+1 := by exact_mod_cast hcr
  have hc1 : (1:ℝ) ≤ c := by exact_mod_cast hc
  have hp := density_bounds hR hc1 hcR
  have hB := (referenceBid_pos_lt hn hR hc1 hcR hw).1
  let B := referenceBid n (r+1) c w
  let p := density (r+1) c
  have hL : 0<B*H n p := mul_pos hB (H_pos n (by omega) p hp.1.le hp.2.le)
  apply AnalyticalKernel.allocation_eq_kernel hn _ _ (fun _ => hB) hB hL ?_ |>.trans ?_
  · rw [KernelTailEvent.kernel_at_score hn hB hp.1.le hp.2.le]
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    change p+((r:ℝ)+1)*p=c
    dsimp [p,density]
    field_simp
    ring
  · exact KernelTailEvent.kernel_at_score hn hB hp.1.le hp.2.le

theorem reference_all_raw_bids {n r c : ℕ} (hn : 2 ≤ n) (hc : 1 ≤ c)
    (hcr : c ≤ r+1) {w : ℝ} (hw : 0<w) (b : ℝ) (hb : 0 ≤ b) :
    (w-b)*success n (AnalyticalKernel.allocation n c hn
      (show c ≤ Fintype.card (Fin (r+1))+1 by simpa using hcr.trans (Nat.le_succ _))
      (fun _ : Fin (r+1) => referenceBid n (r+1) c w) b) ≤
      (w-referenceBid n (r+1) c w)*success n (density (r+1) c) := by
  have hR : (0:ℝ)<(r:ℝ)+1 := by positivity
  have hcR : (c:ℝ) ≤ (r:ℝ)+1 := by exact_mod_cast hcr
  have hc1 : (1:ℝ) ≤ c := by exact_mod_cast hc
  let B := referenceBid n (r+1) c w
  let p := AnalyticalKernel.allocation n c hn
    (show c ≤ Fintype.card (Fin (r+1))+1 by simpa using hcr.trans (Nat.le_succ _)) (fun _ : Fin (r+1) => B) b
  have hB := (referenceBid_pos_lt hn hR hc1 hcR hw).1
  have hp := AnalyticalKernel.allocation_bounds hn
    (show c ≤ Fintype.card (Fin (r+1))+1 by simpa using hcr.trans (Nat.le_succ _)) (fun _ : Fin (r+1) => B) b
  rw [← referenceUtility_at_density hn hR]
  change (w-b)*success n p ≤ referenceUtility n (r+1) c w B (density (r+1) c)
  by_cases hb0 : b=0
  · have hp0 : p=0 := by simp only [p,AnalyticalKernel.allocation,hb0,lt_self_iff_false,false_and,dif_neg,not_false_eq_true]
    simpa only [hp0,success,sub_zero,one_pow,sub_self,mul_zero] using
      (referenceUtility_nonneg hn hR hc1 hcR hw).le
  have hbp : 0<b := lt_of_le_of_ne hb (Ne.symm hb0)
  obtain ⟨L,hL,hpL,hcap⟩ := AnalyticalKernel.allocation_root hn
    (show c ≤ Fintype.card (Fin (r+1))+1 by simpa using hcr.trans (Nat.le_succ _))
    (fun _ : Fin (r+1) => B) (fun _ => hB) hbp
  change p=kernel n b L at hpL
  rw [← hpL] at hcap
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at hcap
  have hqeq : kernel n B L=residual (r+1) c p := by
    apply (eq_div_iff hR.ne').mpr
    linarith
  have hpU : referenceUtility n (r+1) c w B p ≤
      referenceUtility n (r+1) c w B (density (r+1) c) := by
    by_cases he : p=density (r+1) c
    · rw [he]
    · exact (referenceUtility_strict_global hn hR hc1 hcR hw hp he).le
  apply le_trans _ hpU
  by_cases hp0 : p=0
  · simp only [hp0,success,sub_zero,one_pow,sub_self,mul_zero,referenceUtility,zero_mul,sub_zero]
    exact le_rfl
  have hpp : 0<p := lt_of_le_of_ne hp.1 (Ne.symm hp0)
  have hq1 : kernel n B L<1 := by
    rw [hqeq]
    apply (div_lt_one hR).mpr
    linarith
  have hscore := scalar_receipt_le_of_lt_one n B L _ (scalarThreshold_kernel n hn hB hL) hq1
  have hown := scalar_price_le_of_pos n b L _ (scalarThreshold_kernel n hn hbp hL) (by rwa [← hpL])
  rw [← hpL] at hown
  rw [hqeq] at hscore
  have hpay := mul_le_mul_of_nonneg_left (hscore.trans hown) (mul_nonneg (Nat.cast_nonneg n) hp.1)
  have hS := H_mul n (by omega) p
  have hS' := congrArg (fun x => b*x) hS
  dsimp [referenceUtility]
  nlinarith [hS']

theorem reference_all_joint_deviations {n r c : ℕ} (hn : 2 ≤ n) (hc : 1 ≤ c)
    (hcr : c ≤ r+1) {w : ℝ} (hw : 0<w) (b : ℝ) (hb : 0 ≤ b) (k : ℕ) (hk : k ≤ n) :
    (w-b)*success k (AnalyticalKernel.allocation n c hn
      (show c ≤ Fintype.card (Fin (r+1))+1 by simpa using hcr.trans (Nat.le_succ _))
      (fun _ : Fin (r+1) => referenceBid n (r+1) c w) b) ≤
      (w-referenceBid n (r+1) c w)*success n (density (r+1) c) := by
  let p := AnalyticalKernel.allocation n c hn
    (show c ≤ Fintype.card (Fin (r+1))+1 by simpa using hcr.trans (Nat.le_succ _))
    (fun _ : Fin (r+1) => referenceBid n (r+1) c w) b
  have hp := AnalyticalKernel.allocation_bounds hn
    (show c ≤ Fintype.card (Fin (r+1))+1 by simpa using hcr.trans (Nat.le_succ _))
    (fun _ : Fin (r+1) => referenceBid n (r+1) c w) b
  by_cases hwb : 0 ≤ w-b
  · apply le_trans _ (reference_all_raw_bids hn hc hcr hw b hb)
    apply mul_le_mul_of_nonneg_left _ hwb
    exact sub_le_sub_left (pow_le_pow_of_le_one (sub_nonneg.mpr hp.2) (by linarith [hp.1]) hk) 1
  · have hnonneg : 0 ≤ success k p := by
      exact sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hp.2) (by linarith [hp.1]))
    have hu := referenceUtility_nonneg hn (by positivity : (0:ℝ)<(r:ℝ)+1)
      (show (1:ℝ)≤c by exact_mod_cast hc) (show (c:ℝ)≤(r:ℝ)+1 by exact_mod_cast hcr) hw
    rw [referenceUtility_at_density hn (by positivity)] at hu
    exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hwb) hnonneg).trans hu.le

end FCAppendix.Existence.NarrowPayOnce
