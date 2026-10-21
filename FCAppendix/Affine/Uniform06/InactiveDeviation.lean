import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace FCAppendix.Affine.Uniform06.InactiveDeviation

open Set Filter

def utility (η v b SP DP C R : ℝ) : ℝ :=
  (v-b)*(SP+2*C-R)-η*b*(DP+R)

theorem utility_components (η v b SP DP C R : ℝ) :
    utility η v b SP DP C R =
      (v-b)*SP-η*b*DP+2*(v-b)*C-((v-b)+η*b)*R := by
  unfold utility
  ring

theorem duplicate_charge_le_value {η v b : ℝ}
    (hη : η ≤ 1) (hb : 0 ≤ b) : (v-b)+η*b ≤ v := by
  have h := mul_le_mul_of_nonneg_right hη hb
  nlinarith

theorem positive_rent_forces_canonical
    {η v b SP DP C R ε V a Q : ℝ}
    (_hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hb : 0 ≤ b)
    (hε : 0 < ε) (hrent : ε ≤ v-b) (hv : v ≤ V)
    (hQ : 0 ≤ Q) (ha : 0 ≤ a)
    (hDP : 0 ≤ DP) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hpure : a*Q ≤ SP)
    (hDPsmall : V*DP ≤ ε*a*Q/4)
    (hRsmall : V*R ≤ ε*C)
    (henvelope : utility η v b SP DP C R ≤ ε*a*Q/4+2*V*C) :
    ε*a*Q ≤ 4*V*C ∧ utility η v b SP DP C R ≤ 3*V*C := by
  have hr0 : 0 ≤ v-b := hε.le.trans hrent
  have hηb : η*b ≤ V := by
    have h := mul_le_mul_of_nonneg_right hη1 hb
    nlinarith
  have hcharge := duplicate_charge_le_value (v := v) hη1 hb
  have hP : ε*(a*Q) ≤ (v-b)*SP := by
    calc
      _ ≤ (v-b)*(a*Q) := mul_le_mul_of_nonneg_right hrent (mul_nonneg ha hQ)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpure hr0
  have hD : η*b*DP ≤ ε*a*Q/4 :=
    (mul_le_mul_of_nonneg_right hηb hDP).trans hDPsmall
  have hRR : ((v-b)+η*b)*R ≤ ε*C :=
    (mul_le_mul_of_nonneg_right (hcharge.trans hv) hR).trans hRsmall
  have hCC := mul_le_mul_of_nonneg_right hrent hC
  have hid := utility_components η v b SP DP C R
  have hlower : 3*ε*a*Q/4+ε*C ≤ utility η v b SP DP C R := by
    nlinarith
  have hmain : ε*a*Q ≤ 4*V*C := by nlinarith [mul_nonneg hε.le hC]
  exact ⟨hmain, by linarith⟩

theorem feasible_quarter_raise {v b ε entry cap : ℝ}
    (hb : 0 ≤ b) (hε : 0 < ε) (hrent : ε ≤ v-b)
    (hvEntry : v < entry) (hvCap : v ≤ cap) :
    b+ε/4 ∈ Icc 0 cap ∧ b+ε/4 < v ∧ b+ε/4 < entry ∧
      3*ε/4 ≤ v-(b+ε/4) := by
  constructor
  · constructor <;> linarith
  constructor
  · linarith
  constructor <;> linarith

theorem raised_bid_gain
    {η v b ε V C SP' DP' C' R' U : ℝ}
    (hη1 : η ≤ 1) (hb : 0 ≤ b) (hε : 0 < ε)
    (hrent : ε ≤ v-b) (hv : v ≤ V)
    (hSP : 0 ≤ SP') (hDP : 0 ≤ DP') (hR : 0 ≤ R') (hC : 0 ≤ C')
    (hpureLoss : V*DP' ≤ V*C)
    (hduplicate : V*R' ≤ ε*C'/2)
    (hamplify : 4*V*C < ε*C')
    (hU : U ≤ 3*V*C) :
    U < utility η v (b+ε/4) SP' DP' C' R' := by
  have hb' : 0 ≤ b+ε/4 := by linarith
  have hr' : 3*ε/4 ≤ v-(b+ε/4) := by linarith
  have hr0 : 0 ≤ v-(b+ε/4) := by linarith
  have hηb : η*(b+ε/4) ≤ V := by
    have h := mul_le_mul_of_nonneg_right hη1 hb'
    nlinarith
  have hD : η*(b+ε/4)*DP' ≤ V*C :=
    (mul_le_mul_of_nonneg_right hηb hDP).trans hpureLoss
  have hR' : ((v-(b+ε/4))+η*(b+ε/4))*R' ≤ ε*C'/2 :=
    (mul_le_mul_of_nonneg_right
      ((duplicate_charge_le_value hη1 hb').trans hv) hR).trans hduplicate
  have hP := mul_nonneg hr0 hSP
  have hCC := mul_le_mul_of_nonneg_right hr' hC
  have hid := utility_components η v (b+ε/4) SP' DP' C' R'
  nlinarith

theorem no_positive_rent_at_IC
    (SP DP C R : ℝ → ℝ) {η v b ε V a Q entry cap : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hb : 0 ≤ b)
    (hε : 0 < ε) (hrent : ε ≤ v-b) (hv : v ≤ V)
    (hvEntry : v < entry) (hvCap : v ≤ cap)
    (hQ : 0 ≤ Q) (ha : 0 ≤ a)
    (hDP : 0 ≤ DP b) (hC : 0 ≤ C b) (hR : 0 ≤ R b)
    (hpure : a*Q ≤ SP b)
    (hDPsmall : V*DP b ≤ ε*a*Q/4)
    (hRsmall : V*R b ≤ ε*C b)
    (henvelope : utility η v b (SP b) (DP b) (C b) (R b) ≤
      ε*a*Q/4+2*V*C b)
    (hSP' : 0 ≤ SP (b+ε/4)) (hDP' : 0 ≤ DP (b+ε/4))
    (hC' : 0 ≤ C (b+ε/4)) (hR' : 0 ≤ R (b+ε/4))
    (hpureLoss : V*DP (b+ε/4) ≤ V*C b)
    (hduplicate : V*R (b+ε/4) ≤ ε*C (b+ε/4)/2)
    (hamplify : 4*V*C b < ε*C (b+ε/4))
    (hIC : ∀ b' ∈ Icc (0:ℝ) cap,
      utility η v b' (SP b') (DP b') (C b') (R b') ≤
        utility η v b (SP b) (DP b) (C b) (R b)) : False := by
  have hforced := positive_rent_forces_canonical hη0 hη1 hb hε hrent hv
    hQ ha hDP hC hR hpure hDPsmall hRsmall henvelope
  have hfeasible := feasible_quarter_raise hb hε hrent hvEntry hvCap
  have hgain := raised_bid_gain hη1 hb hε hrent hv hSP' hDP' hR' hC'
    hpureLoss hduplicate hamplify hforced.2
  exact (not_lt_of_ge (hIC _ hfeasible.1)) hgain

theorem uniform_identity_of_uniform_no_rent
    (B : ℕ → ℝ → ℝ) (K : Set ℝ)
    (hbelow : ∀ᶠ m in atTop, ∀ v ∈ K, B m v ≤ v)
    (hnoRent : ∀ ε > (0:ℝ), ∀ᶠ m in atTop,
      ∀ v ∈ K, ¬ ε ≤ v-B m v) :
    TendstoUniformlyOn B (fun v => v) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hbelow, hnoRent ε hε] with m hm hn v hv
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hm v hv))]
  have h := lt_of_not_ge (hn v hv)
  linarith

end FCAppendix.Affine.Uniform06.InactiveDeviation
