import FCAppendix.Exclusive.NarrowExistenceSensitivity

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open Set Filter Topology
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem inverseLogBid_bounds (r delta z : ℝ) (hr : 0 ≤ r)
    (hz : z ∈ Icc (-delta) delta) :
    Real.exp (-r*delta) ≤ Real.exp (-r*z) ∧
      Real.exp (-r*z) ≤ Real.exp (r*delta) := by
  constructor <;> apply Real.exp_le_exp.mpr <;> nlinarith [hz.1, hz.2]

theorem inverseLogBidSum_bounds (r delta : ℝ) (hr : 0 ≤ r)
    (z : ι → ℝ) (hz : ∀ i, z i ∈ Icc (-delta) delta) :
    (Fintype.card ι:ℝ)*Real.exp (-r*delta) ≤ Exclusive.Existence.inverseLogBidSum r z ∧
      Exclusive.Existence.inverseLogBidSum r z ≤ (Fintype.card ι:ℝ)*Real.exp (r*delta) := by
  constructor
  · simpa only [Exclusive.Existence.inverseLogBidSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (fun i _ => (inverseLogBid_bounds r delta (z i) hr (hz i)).1))
  · simpa only [Exclusive.Existence.inverseLogBidSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (fun i _ => (inverseLogBid_bounds r delta (z i) hr (hz i)).2))

def profileShare (r : ℝ) (z : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (-r*z i)/Exclusive.Existence.inverseLogBidSum r z

theorem profileShare_bounds [Nonempty ι] (r delta : ℝ) (hr : 0 ≤ r)
    (z : ι → ℝ) (hz : ∀ i, z i ∈ Icc (-delta) delta) (i : ι) :
    Real.exp (-2*r*delta)/(Fintype.card ι:ℝ) ≤ profileShare r z i ∧
      profileShare r z i ≤ Real.exp (2*r*delta)/(Fintype.card ι:ℝ) := by
  have hN : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsum := inverseLogBidSum_bounds r delta hr z hz
  have hi := inverseLogBid_bounds r delta (z i) hr (hz i)
  have hpos := Exclusive.Existence.inverseLogBidSum_pos r z
  have hlo : 0 < (Fintype.card ι:ℝ)*Real.exp (-r*delta) := mul_pos hN (Real.exp_pos _)
  have hhi : 0 < (Fintype.card ι:ℝ)*Real.exp (r*delta) := mul_pos hN (Real.exp_pos _)
  have helo : Real.exp (-r*delta)/((Fintype.card ι:ℝ)*Real.exp (r*delta)) =
      Real.exp (-2*r*delta)/(Fintype.card ι:ℝ) := by
    rw [mul_comm (Fintype.card ι:ℝ), div_mul_eq_div_div, ← Real.exp_sub]
    congr 2
    ring
  have hehi : Real.exp (r*delta)/((Fintype.card ι:ℝ)*Real.exp (-r*delta)) =
      Real.exp (2*r*delta)/(Fintype.card ι:ℝ) := by
    rw [mul_comm (Fintype.card ι:ℝ), div_mul_eq_div_div, ← Real.exp_sub]
    congr 2
    ring
  constructor
  · rw [← helo]
    exact (div_le_div_of_nonneg_left (Real.exp_pos _).le hpos hsum.2).trans
      (div_le_div_of_nonneg_right hi.1 hpos.le)
  · rw [← hehi]
    exact (div_le_div_of_nonneg_right hi.2 hpos.le).trans
      (div_le_div_of_nonneg_left (Real.exp_pos _).le hlo hsum.1)

theorem profileShare_pos [Nonempty ι] (r : ℝ) (z : ι → ℝ) (i : ι) :
    0 < profileShare r z i :=
  div_pos (Real.exp_pos _) (Exclusive.Existence.inverseLogBidSum_pos r z)

theorem profileShare_le_one [Nonempty ι] (r : ℝ) (z : ι → ℝ) (i : ι) :
    profileShare r z i ≤ 1 := by
  apply (div_le_one (Exclusive.Existence.inverseLogBidSum_pos r z)).2
  exact Finset.single_le_sum (fun j _ => (Real.exp_pos (-r*z j)).le) (Finset.mem_univ i)

theorem profileFailure_bounds [Nonempty ι] (r delta : ℝ) (hr : 0 ≤ r)
    (z : ι → ℝ) (hz : ∀ i, z i ∈ Icc (-delta) delta) (i : ι)
    (c : ℕ) (hc : c ≤ Fintype.card ι) :
    (1-(c:ℝ)/(Fintype.card ι:ℝ))*Real.exp (-2*r*delta) ≤
        ((Fintype.card ι-c:ℕ):ℝ)*profileShare r z i ∧
      ((Fintype.card ι-c:ℕ):ℝ)*profileShare r z i ≤
        (1-(c:ℝ)/(Fintype.card ι:ℝ))*Real.exp (2*r*delta) := by
  have hN : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hs := profileShare_bounds r delta hr z hz i
  have hg : (0:ℝ) ≤ ((Fintype.card ι-c:ℕ):ℝ) := Nat.cast_nonneg _
  have he (x : ℝ) : ((Fintype.card ι-c:ℕ):ℝ)*(x/(Fintype.card ι:ℝ)) =
      (1-(c:ℝ)/(Fintype.card ι:ℝ))*x := by
    rw [Nat.cast_sub hc]
    field_simp [hN.ne']
  constructor
  · simpa only [he] using mul_le_mul_of_nonneg_left hs.1 hg
  · simpa only [he] using mul_le_mul_of_nonneg_left hs.2 hg

theorem profileFailure_error [Nonempty ι] (r delta : ℝ) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (z : ι → ℝ) (hz : ∀ i, z i ∈ Icc (-delta) delta) (i : ι)
    (c : ℕ) (hc : c ≤ Fintype.card ι) :
    |((Fintype.card ι-c:ℕ):ℝ)*profileShare r z i-
        (1-(c:ℝ)/(Fintype.card ι:ℝ))| ≤
      Real.exp (2*r*delta)-Real.exp (-2*r*delta) := by
  have hb := profileFailure_bounds r delta hr z hz i c hc
  have hN : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have ha0 : 0 ≤ 1-(c:ℝ)/(Fintype.card ι:ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one hN).2 (by exact_mod_cast hc)
  have ha1 : 1-(c:ℝ)/(Fintype.card ι:ℝ) ≤ 1 := by
    linarith [div_nonneg (Nat.cast_nonneg c) hN.le]
  have hlo : Real.exp (-2*r*delta) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by nlinarith : -2*r*delta ≤ 0)
  have hhi : 1 ≤ Real.exp (2*r*delta) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by positivity : (0:ℝ) ≤ 2*r*delta)
  have hspan := mul_le_mul_of_nonneg_right ha1 (sub_nonneg.mpr (hlo.trans hhi))
  have hmlo := mul_le_mul_of_nonneg_left hlo ha0
  have hmhi := mul_le_mul_of_nonneg_left hhi ha0
  apply abs_le.mpr
  constructor <;> nlinarith

theorem active_count_ratio_neighborhood (h rho eps : ℝ)
    (hh : 0 < h) (hrho : 0 < rho) (hrh : rho < h) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s t : ℝ,
      |s-h| < delta → |t-rho| < delta →
        h/2 < s ∧ 0 < t ∧ t < s ∧ |t/s-rho/h| < eps := by
  let x0 : ℝ×ℝ := (h,rho)
  have hratio : ContinuousAt (fun x : ℝ×ℝ => x.2/x.1) x0 :=
    continuousAt_snd.div continuousAt_fst hh.ne'
  have h1 := (continuousAt_fst : ContinuousAt (fun x : ℝ×ℝ => x.1) x0).eventually
    (eventually_gt_nhds (show h/2 < h by linarith))
  have h2 := (continuousAt_snd : ContinuousAt (fun x : ℝ×ℝ => x.2) x0).eventually
    (eventually_gt_nhds hrho)
  have h3 := ((continuousAt_fst : ContinuousAt (fun x : ℝ×ℝ => x.1) x0).sub
    continuousAt_snd).eventually (eventually_gt_nhds (show (0:ℝ) < h-rho by linarith))
  have h4 := hratio.eventually (Metric.ball_mem_nhds (rho/h) heps)
  have hall : ∀ᶠ x : ℝ×ℝ in 𝓝 x0,
      h/2 < x.1 ∧ 0 < x.2 ∧ x.2 < x.1 ∧ |x.2/x.1-rho/h| < eps := by
    filter_upwards [h1,h2,h3,h4] with x hx1 hx2 hx3 hx4
    change 0 < x.1-x.2 at hx3
    exact ⟨hx1,hx2,by linarith,by simpa only [Metric.mem_ball,Real.dist_eq] using hx4⟩
  obtain ⟨delta, hd, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨delta, hd, ?_⟩
  intro s t hs ht
  apply hball (a := (s,t))
  simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq] using max_lt hs ht

omit [Fintype ι] in

theorem finite_profile_state_neighborhood (r h rho eps : ℝ)
    (hr : 0 ≤ r) (hh : 0 < h) (hrho : 0 < rho) (hrh : rho < h) (heps : 0 < eps) :
    ∃ delta eta : ℝ, ∃ M0 : ℕ, 0 < delta ∧ 0 < eta ∧ 0 < M0 ∧
      ∀ (ι : Type*) [Fintype ι] (M c : ℕ), M0 ≤ M →
      ∀ (z : ι → ℝ), (∀ i, z i ∈ Icc (-delta) delta) →
      |(Fintype.card ι:ℝ)/(M:ℝ)-h| < eta → |(c:ℝ)/(M:ℝ)-rho| < eta →
      ∀ i : ι, c < Fintype.card ι ∧
        |((Fintype.card ι-c:ℕ):ℝ)*profileShare r z i-(1-rho/h)| < eps ∧
        profileShare r z i < eps := by
  have hcont : Continuous (fun e : ℝ => Real.exp (2*r*e)-Real.exp (-2*r*e)) := by fun_prop
  have hcont2 : Continuous (fun e : ℝ => Real.exp (2*r*e)) := by fun_prop
  have h1 := hcont.continuousAt.eventually (eventually_lt_nhds
    (show Real.exp (2*r*0)-Real.exp (-2*r*0) < eps/2 by norm_num; positivity))
  have h2 := hcont2.continuousAt.eventually (eventually_lt_nhds
    (show Real.exp (2*r*0) < (2:ℝ) by norm_num))
  obtain ⟨b, hb, hball⟩ := Metric.mem_nhds_iff.mp (h1.and h2)
  let delta := b/2
  have hdel : 0 < delta := by dsimp [delta]; positivity
  have hdelmem : delta ∈ Metric.ball (0:ℝ) b := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hdel]
    dsimp [delta]
    linarith
  have hdBounds := hball hdelmem
  obtain ⟨eta, heta, hratio⟩ := active_count_ratio_neighborhood h rho (eps/2)
    hh hrho hrh (by positivity)
  obtain ⟨M0, hM0⟩ := exists_nat_gt (4/(h*eps))
  have hM0pos : 0 < M0 := by
    have hp : (0:ℝ) < (M0:ℝ) := (div_pos (by norm_num) (mul_pos hh heps)).trans hM0
    exact_mod_cast hp
  refine ⟨delta, eta, M0, hdel, heta, hM0pos, ?_⟩
  intro ι _ M c hM z hz hN hC i
  letI : Nonempty ι := ⟨i⟩
  have hMpos : (0:ℝ) < M := by exact_mod_cast (lt_of_lt_of_le hM0pos hM)
  have hrat := hratio ((Fintype.card ι:ℝ)/(M:ℝ)) ((c:ℝ)/(M:ℝ)) hN hC
  have hcN : c < Fintype.card ι := by
    exact_mod_cast ((div_lt_div_iff_of_pos_right hMpos).mp hrat.2.2.1)
  have heq : ((c:ℝ)/(M:ℝ))/((Fintype.card ι:ℝ)/(M:ℝ)) =
      (c:ℝ)/(Fintype.card ι:ℝ) := by field_simp
  have hraterr : |(c:ℝ)/(Fintype.card ι:ℝ)-rho/h| < eps/2 := by
    simpa only [heq] using hrat.2.2.2
  have herr := profileFailure_error r delta hr hdel.le z hz i c hcN.le
  have hsmall : |((Fintype.card ι-c:ℕ):ℝ)*profileShare r z i-(1-rho/h)| < eps := by
    have htriangle : |((Fintype.card ι-c:ℕ):ℝ)*profileShare r z i-(1-rho/h)| ≤
        |((Fintype.card ι-c:ℕ):ℝ)*profileShare r z i-
          (1-(c:ℝ)/(Fintype.card ι:ℝ))|+|(c:ℝ)/(Fintype.card ι:ℝ)-rho/h| := by
      calc
        _ = |(((Fintype.card ι-c:ℕ):ℝ)*profileShare r z i-
            (1-(c:ℝ)/(Fintype.card ι:ℝ)))-((c:ℝ)/(Fintype.card ι:ℝ)-rho/h)| := by
          congr 1
          ring
        _ ≤ _ := by
          simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le
            (((Fintype.card ι-c:ℕ):ℝ)*profileShare r z i-(1-(c:ℝ)/(Fintype.card ι:ℝ)))
            0 ((c:ℝ)/(Fintype.card ι:ℝ)-rho/h)
    linarith [hdBounds.1]
  have hshare := (profileShare_bounds r delta hr z hz i).2
  have hNpos : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hNlarge : 2/eps < (Fintype.card ι:ℝ) := by
    have hMlarge : 4/(h*eps) < (M:ℝ) := hM0.trans_le (by exact_mod_cast hM)
    have hNM : h/2*(M:ℝ) < (Fintype.card ι:ℝ) := (lt_div_iff₀ hMpos).mp hrat.1
    have hx : 4 < (M:ℝ)*(h*eps) := (div_lt_iff₀ (mul_pos hh heps)).mp hMlarge
    apply (div_lt_iff₀ heps).2
    nlinarith
  have hshareSmall : profileShare r z i < eps := by
    have hbound : Real.exp (2*r*delta)/(Fintype.card ι:ℝ) < 2/(Fintype.card ι:ℝ) :=
      (div_lt_div_iff_of_pos_right hNpos).2 hdBounds.2
    have h2N : 2/(Fintype.card ι:ℝ) < eps :=
      (div_lt_iff₀ hNpos).2 (by simpa only [mul_comm] using (div_lt_iff₀ heps).mp hNlarge)
    exact hshare.trans_lt (hbound.trans h2N)
  exact ⟨hcN, hsmall, hshareSmall⟩

end FCAppendix.Exclusive.Narrow.Existence
