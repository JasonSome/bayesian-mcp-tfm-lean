import FCAppendix.Affine.Tail04.Underfill
import FCAppendix.Affine.Hybrid.Menu
import FCAppendix.Finite.PPIRankTypes
import FCAppendix.Finite.SingletonDeviation
import FCAppendix.Probability.FinitePushforward

noncomputable section
namespace FCAppendix.Affine.Tail04.GlobalLower
open MeasureTheory ProbabilityTheory Set Game Bayes Classical
open scoped BigOperators

theorem payoff_le_bid_positive_part {n : ℕ} (P : Interim.Problem n)
    (v : ℝ) (a : JointAction n) :
    P.payoff v a ≤ max (v-P.g-a.bid) 0 := by
  have hu := (P.outcome a).utility_le_bid_net_success v a.bid P.g P.A P.G
    a.bid_nonneg P.g_nonneg
  change P.payoff v a ≤ _ at hu
  by_cases hv : 0 ≤ v-P.g-a.bid
  · rw [max_eq_left hv]
    have hh := mul_le_mul_of_nonneg_left ((P.outcome a).success_le_one) hv
    exact hu.trans (by simpa using hh)
  · rw [max_eq_right (le_of_not_ge hv)]
    exact hu.trans (mul_nonpos_of_nonpos_of_nonneg
      (le_of_not_ge hv) (P.outcome a).success_nonneg)

theorem payoff_le_value_sub_one {n : ℕ} (P : Interim.Problem n)
    (v : ℝ) (hv : 1 ≤ v) (a : JointAction n) (ha : 1 ≤ a.bid) :
    P.payoff v a ≤ v-1 := by
  exact (payoff_le_bid_positive_part P v a).trans
    (max_le (by linarith [P.g_nonneg]) (by linarith))

theorem low_bestResponse_of_restricted {n : ℕ} (P : Interim.Problem n)
    (d0 v : ℝ) (hd0 : 0 ≤ d0) (hv : v ≤ d0) (a : JointAction n)
    (hbox : ∀ a' : JointAction n, a'.bid ≤ d0 → P.payoff v a' ≤ P.payoff v a) :
    P.BestResponse v a := by
  intro a'
  by_cases hb : a'.bid ≤ d0
  · exact hbox a' hb
  · have hnonneg : 0 ≤ P.payoff v a := by
      simpa using hbox (Interim.abstain n) hd0
    have hnet : v-P.g-a'.bid ≤ 0 := by linarith [P.g_nonneg]
    exact (payoff_le_bid_positive_part P v a').trans
      (by simpa only [max_eq_right hnet] using hnonneg)

theorem payoff_value_lipschitz {n : ℕ} (P : Interim.Problem n)
    (a : JointAction n) (v w : ℝ) :
    |P.payoff v a-P.payoff w a| ≤ |v-w| := by
  have he : P.payoff v a-P.payoff w a = (v-w)*(P.outcome a).success := by
    rw [P.payoff_affine w v a]
    ring
  rw [he,abs_mul,abs_of_nonneg (P.outcome a).success_nonneg]
  simpa using mul_le_mul_of_nonneg_left (P.outcome a).success_le_one (abs_nonneg (v-w))

theorem action_gap_transport {n : ℕ} (P : Interim.Problem n)
    (a a' : JointAction n) (v v0 d w : ℝ)
    (hgap : d ≤ P.payoff v0 a-P.payoff v0 a') (hwidth : |v-v0| ≤ w) :
    d-2*w ≤ P.payoff v a-P.payoff v a' := by
  have h1 := (abs_le.mp ((payoff_value_lipschitz P a v v0).trans hwidth)).1
  have h2 := (abs_le.mp ((payoff_value_lipschitz P a' v v0).trans hwidth)).2
  linarith

section NativeLow
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem affine_receipt_lower_two (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (r : ℕ) (hr : 0 < r) (hr2 : r ≤ 2) :
    ((1+η)/2)*(r:ℝ) ≤ (Schedule.affine 2 η hη0 hη1).charge r := by
  interval_cases r <;> norm_num [Schedule.affine,successIndicator]
  all_goals linarith

theorem native_low_acceptance_exp (Γ : FiniteGame m 2 c Seed)
    (hm : 11 ≤ m) (hc : (c:ℝ) ≤ (m:ℝ)/2)
    (j : Fin 2) (hj : ProposerRationalAtFeasibleLists Γ j) (i : Fin m)
    (a t b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hbt : b/a ≤ t)
    (hA : ∀ r : ℕ, 0< r → r≤2 → a*(r:ℝ) ≤ Γ.A.charge r)
    (hmass : (3/5:ℝ) ≤ alphaGt Γ j t) :
    acceptProb Γ i b j ≤ Real.exp (-((m-1:ℕ):ℝ)/200) := by
  let p := alphaGt Γ j (b/a)
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have hp : (3/5:ℝ) ≤ p := hmass.trans (alphaGt_antitone Γ j hbt)
  have hcm : c ≤ m := by
    have : (c:ℝ) ≤ (m:ℝ) := by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    exact_mod_cast this
  have hN : (m-1:ℕ)+1=m := by omega
  have hcast : ((m-1:ℕ):ℝ) = (m:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  have hmR : (11:ℝ) ≤ m := by exact_mod_cast hm
  have hmargin : (c:ℝ) ≤ (m-1:ℕ)*(p-(1/20:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (m-1))
    rw [hcast] at hh ⊢
    nlinarith
  have hbin : binomBelow (m-1) p c ≤ Real.exp (-((m-1:ℕ):ℝ)/200) := by
    rw [binomBelow_eq_prob (m-1) c (by omega) p hp0 hp1]
    convert! Underfill.binomial_underload_exp (m-1) c p (1/20)
      hp0 hp1 (by norm_num) hmargin using 1
    ring
  exact (acceptProb_le_rank_nonneg Γ j hj i a ha hA b hb).trans hbin

theorem native_low_all_routes_success_exp (Γ : FiniteGame m 2 c Seed)
    (hm : 11 ≤ m) (hc : (c:ℝ) ≤ (m:ℝ)/2)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j) (i : Fin m)
    (a t : ℝ) (ha : 0< a)
    (hA : ∀ r : ℕ, 0< r → r≤2 → a*(r:ℝ) ≤ Γ.A.charge r)
    (hmass : ∀ j, (3/5:ℝ) ≤ alphaGt Γ j t)
    (act : JointAction 2) (hbid : act.bid/a ≤ t) :
    ((problem Γ i).outcome act).success ≤ 2*Real.exp (-((m-1:ℕ):ℝ)/200) := by
  have hbound (j : Fin 2) := native_low_acceptance_exp Γ hm hc j (hj j) i
    a t act.bid ha act.bid_nonneg hbid hA (hmass j)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hbound j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have hmean : meanAcceptProb Γ i act.bid ≤ Real.exp (-((m-1:ℕ):ℝ)/200) := by
    unfold meanAcceptProb
    norm_num only [Nat.cast_ofNat]
    nlinarith
  exact (success_le_n_meanAcceptProb Γ (by omega) i act).trans
    (by simpa using mul_le_mul_of_nonneg_left hmean (by norm_num : (0:ℝ) ≤ 2))

theorem native_low_all_routes_payoff_exp (Γ : FiniteGame m 2 c Seed)
    (hm : 11 ≤ m) (hc : (c:ℝ) ≤ (m:ℝ)/2)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j) (i : Fin m)
    (a t v : ℝ) (ha : 0< a) (hv : 0≤ v)
    (hA : ∀ r : ℕ, 0< r → r≤2 → a*(r:ℝ) ≤ Γ.A.charge r)
    (hmass : ∀ j, (3/5:ℝ) ≤ alphaGt Γ j t)
    (act : JointAction 2) (hbid : act.bid/a ≤ t) :
    (problem Γ i).payoff v act ≤ 2*v*Real.exp (-((m-1:ℕ):ℝ)/200) := by
  have hs := native_low_all_routes_success_exp Γ hm hc hj i a t ha hA hmass act hbid
  have hu := ((problem Γ i).outcome act).utility_le_bid_net_success
    v act.bid Γ.g Γ.A Γ.G act.bid_nonneg Γ.g_nonneg
  change (problem Γ i).payoff v act ≤ _ at hu
  have hcost : 0 ≤ (Γ.g+act.bid)*((problem Γ i).outcome act).success :=
    mul_nonneg (add_nonneg Γ.g_nonneg act.bid_nonneg)
      ((problem Γ i).outcome act).success_nonneg
  have hvs := mul_le_mul_of_nonneg_left hs hv
  nlinarith

end NativeLow

theorem canonical_one_at_two (ξ lam q : ℝ) (hξ0 : 0≤ ξ) (hξ1 : ξ≤1/2)
    (hq0 : 0≤ q) (hq1 : q≤1) (hlam : 1-ξ ≤ lam) :
    Hybrid.one ξ 0 2 lam q ≤ 1 := by
  have hξq : ξ*q≤ ξ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hq1 hξ0
  have hd : 0 < 1-ξ*q := by nlinarith
  have hfac : 0 ≤ (1-q)*(1-2*ξ*q) := by
    apply mul_nonneg (sub_nonneg.mpr hq1)
    nlinarith
  have hlamq := mul_le_mul_of_nonneg_right hlam hq0
  have he : Hybrid.one ξ 0 2 lam q =
      (2*q*(1-ξ*q)-q*lam)/(1-ξ*q) := by
    unfold Hybrid.one
    field_simp [hd.ne',show 1-q*ξ ≠ 0 by nlinarith]
    ring
  rw [he]
  apply (div_le_iff₀ hd).2
  nlinarith

theorem canonical_one_large_value (ξ lam q v : ℝ)
    (hξ0 : 0≤ ξ) (hξ1 : ξ<1) (hlam : 0≤ lam)
    (_hq0 : 0≤ q) (hq1 : q≤1) (hv : lam/(1-ξ)^2 ≤ v) :
    Hybrid.one ξ 0 v lam q ≤ v-lam/(1-ξ) := by
  have hk : 0 < 1-ξ := by linarith
  have hξq : ξ*q≤ ξ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hq1 hξ0
  have hd : 0 < 1-ξ*q := by nlinarith
  have hkd : (1-ξ)^2 ≤ (1-ξ)*(1-ξ*q) := by
    have hh := mul_nonneg hk.le (sub_nonneg.mpr hξq)
    nlinarith
  have hfrac : lam/((1-ξ)*(1-ξ*q)) ≤ v :=
    (div_le_div_of_nonneg_left hlam (sq_pos_of_pos hk) hkd).trans hv
  have he : (v-lam/(1-ξ))-Hybrid.one ξ 0 v lam q =
      (1-q)*(v-lam/((1-ξ)*(1-ξ*q))) := by
    unfold Hybrid.one
    field_simp
    ring
  have hh := mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr hfrac)
  rw [←he] at hh
  linarith

theorem canonical_two_bound (ξ lam q v : ℝ) (hv : 0< v) :
    Hybrid.two ξ 0 v lam q ≤ v-(2*lam-lam^2/v) := by
  rw [Hybrid.two_zero_square _ _ _ _ hv.ne']
  have he : Hybrid.outsideTwo v lam = v-(2*lam-lam^2/v) := by
    unfold Hybrid.outsideTwo
    field_simp [hv.ne']
    ring
  rw [he]
  exact sub_le_self _ (mul_nonneg hv.le (sq_nonneg _))

theorem canonical_two_lower_multiplier_bound (ξ lam lamlo q v : ℝ)
    (hv : 0< v) (hq : 0≤ q) (hlam : lamlo≤ lam) :
    Hybrid.two ξ 0 v lam q ≤ v-(2*lamlo-lamlo^2/v) := by
  have hm : Hybrid.two ξ 0 v lam q ≤ Hybrid.two ξ 0 v lamlo q := by
    unfold Hybrid.two
    have hh := mul_nonneg (sub_nonneg.mpr hlam) hq
    nlinarith
  exact hm.trans (canonical_two_bound ξ lamlo q v hv)

theorem canonical_two_uniform_large_value (ξ lam lamlo q v vmin : ℝ)
    (hvmin : 0< vmin) (hv : vmin≤ v) (hq : 0≤ q) (hlam : lamlo≤ lam) :
    Hybrid.two ξ 0 v lam q ≤ v-(2*lamlo-lamlo^2/vmin) := by
  have hfrac := div_le_div_of_nonneg_left (sq_nonneg lamlo) hvmin hv
  exact (canonical_two_lower_multiplier_bound ξ lam lamlo q v
    (hvmin.trans_le hv) hq hlam).trans (by linarith)

theorem weighted_two_regime_bound (θ uA uR C : ℝ)
    (hθ0 : 0≤ θ) (hθ1 : θ≤1) (hA : uA≤ C) (hR : uR≤ C) :
    (1-θ)*uA+θ*uR ≤ C := by
  have ha := mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr hθ1)
  have hr := mul_le_mul_of_nonneg_left hR hθ0
  nlinarith

theorem source_canonical_margins (ξ : ℝ) (hξ0 : 0≤ ξ) (hξ1 : ξ≤1/2) :
    (1-19*ξ/20)-(1-ξ)*(1+ξ/50) = ξ*(3/100+ξ/50) ∧
    1/25 ≤ 2*(1-19*ξ/20)-(1+ξ/50) ∧
    1199/3200 ≤ 2*(1-19*ξ/20)-(1-19*ξ/20)^2/2-(1-37*ξ/40) := by
  refine ⟨by ring,by linarith,?_⟩
  have hx2 : ξ^2≤1/4 := by nlinarith
  nlinarith

theorem source_active_partial_margin (ξ θ : ℝ) (hθ : θ≠0) :
    θ*(11*ξ/(10*θ))+(1-θ)*(1-37*ξ/40)-(1+ξ/50) =
      31*ξ/200-θ*(1-37*ξ/40) := by
  field_simp
  ring

theorem bid_mixed_flag_le_baseline (B b e : ℝ) (hB : 1< B)
    (hb0 : 1≤ b) (hb1 : b≤ B) (he : 0≤ e) :
    e*((B-b)/(B-1))^2 ≤ e := by
  have hd : 0< B-1 := by linarith
  have hq0 : 0≤(B-b)/(B-1) := div_nonneg (by linarith) hd.le
  have hq1 : (B-b)/(B-1)≤1 := (div_le_one hd).2 (by linarith)
  have hq2 : ((B-b)/(B-1))^2≤1 := by
    have hh := mul_nonneg hq0 (sub_nonneg.mpr hq1)
    nlinarith
  simpa using mul_le_mul_of_nonneg_left hq2 he

theorem active_one_marginal (e q : ℝ) (he : 0≤ e) (hq : q≤1) :
    (1-e)/2+e*q ≤ (1+e)/2 := by
  have hh := mul_le_mul_of_nonneg_left hq he
  nlinarith

theorem active_two_regime_one_marginal (θ eA eR qA qR : ℝ)
    (hθ0 : 0≤ θ) (hθ1 : θ≤1) (heA : 0≤ eA) (heR : 0≤ eR)
    (hqA : qA≤1) (hqR : qR≤1) :
    (1-θ)*((1-eA)/2+eA*qA)+θ*((1-eR)/2+eR*qR) ≤
      (1+((1-θ)*eA+θ*eR))/2 := by
  have hA := mul_le_mul_of_nonneg_left (active_one_marginal eA qA heA hqA)
    (sub_nonneg.mpr hθ1)
  have hR := mul_le_mul_of_nonneg_left (active_one_marginal eR qR heR hqR) hθ0
  nlinarith

section NativeSingleton
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem native_active_singleton_excluded (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (v vmin B ε qbar : ℝ) (hvmin : 0≤ vmin) (hv : vmin≤ v)
    (_hq0 : 0≤ qbar) (hq1 : qbar≤1) (a a' : JointAction 2)
    (hk : a'.routeCount=1) (hq : meanAcceptProb Γ i a'.bid≤ qbar)
    (hintended : v-B-ε ≤ (problem Γ i).payoff v a)
    (hgap : B+ε < (1-qbar)*vmin) :
    (problem Γ i).payoff v a' < (problem Γ i).payoff v a := by
  have hmean0 : 0≤ meanAcceptProb Γ i a'.bid := by
    unfold meanAcceptProb acceptProb
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => measureReal_nonneg)
  have hpay : (problem Γ i).payoff v a' ≤ v*qbar := by
    rw [singleton_payoff Γ (by omega) i a' hk v]
    have hcost := mul_nonneg (add_nonneg Γ.g_nonneg a'.bid_nonneg) hmean0
    have hmul := mul_le_mul_of_nonneg_left hq (hvmin.trans hv)
    nlinarith
  have hg := mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr hq1)
  linarith

end NativeSingleton

section OriginalRegime
variable {Ω : Type*} [MeasurableSpace Ω]

theorem original_count_success (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω → Fin 3) (hK : Measurable K) :
    (CountLaw.ofMeasure μ K hK).success = μ.real {ω | K ω≠0} := by
  have hS : MeasurableSet {ω | K ω≠0} := (hK (measurableSet_singleton 0)).compl
  rw [CountLaw.success,CountLaw.expect_ofMeasure]
  have he : (fun ω => successIndicator (K ω).val) =
      {ω | K ω≠0}.indicator (fun _ : Ω => (1:ℝ)) := by
    funext ω
    have hh : (K ω).val=0 ↔ K ω=0 := by
      constructor
      · intro h;exact Fin.ext h
      · intro h; rw [h]; rfl
    simp [Set.indicator,successIndicator,hh]
  rw [he]
  exact integral_indicator_one hS

theorem original_count_duplicates (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω → Fin 3) (hK : Measurable K) :
    (CountLaw.ofMeasure μ K hK).duplicates = μ.real {ω | K ω=2} := by
  rw [CountLaw.duplicates_eq_expect,CountLaw.expect_ofMeasure]
  have he : (fun ω => ((K ω).val:ℝ)-successIndicator (K ω).val) =
      {ω | K ω=2}.indicator (fun _ : Ω => (1:ℝ)) := by
    funext ω
    simp only [Set.indicator,Set.mem_setOf_eq]
    generalize K ω = r
    fin_cases r <;> norm_num [successIndicator,Fin.ext_iff]
  rw [he]
  exact integral_indicator_one (hK (measurableSet_singleton 2))

theorem original_common_regime_bounds (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (K1 K2 : Ω → Fin 3) (hK1 : Measurable K1) (hK2 : Measurable K2)
    (ε : ℝ)
    (hone : μ.real {ω | ω∈E ∧ K1 ω=0} ≤ ε)
    (htwoOutside : μ.real {ω | ω∉E ∧ K2 ω≠0} ≤ ε)
    (htwoMiss : μ.real {ω | ω∈E ∧ K2 ω≠2} ≤ ε) :
    μ.real E-ε ≤ (CountLaw.ofMeasure μ K1 hK1).success ∧
    (CountLaw.ofMeasure μ K2 hK2).success ≤ μ.real E+ε ∧
    μ.real E-ε ≤ (CountLaw.ofMeasure μ K2 hK2).duplicates := by
  rw [original_count_success,original_count_success,original_count_duplicates]
  have h1 : E ⊆ {ω | K1 ω≠0} ∪ {ω | ω∈E ∧ K1 ω=0} := by
    intro ω hω
    by_cases hk : K1 ω=0
    · exact Or.inr ⟨hω,hk⟩
    · exact Or.inl hk
  have h2 : {ω | K2 ω≠0} ⊆ E ∪ {ω | ω∉E ∧ K2 ω≠0} := by
    intro ω hω
    by_cases hωE : ω∈E
    · exact Or.inl hωE
    · exact Or.inr ⟨hωE,hω⟩
  have h3 : E ⊆ {ω | K2 ω=2} ∪ {ω | ω∈E ∧ K2 ω≠2} := by
    intro ω hω
    by_cases hk : K2 ω=2
    · exact Or.inl hk
    · exact Or.inr ⟨hω,hk⟩
  have h1' := (measureReal_mono (μ := μ) h1).trans (measureReal_union_le _ _)
  have h2' := (measureReal_mono (μ := μ) h2).trans (measureReal_union_le _ _)
  have h3' := (measureReal_mono (μ := μ) h3).trans (measureReal_union_le _ _)
  exact ⟨by linarith,by linarith,by linarith⟩

theorem original_common_good_event (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E G : Set Ω) (K1 K2 : Ω → Fin 3) (hK1 : Measurable K1) (hK2 : Measurable K2)
    (ε : ℝ) (hbad : μ.real Gᶜ ≤ ε)
    (hgood : ∀ ω∈G, (ω∈E → K1 ω≠0 ∧ K2 ω=2) ∧ (ω∉E → K2 ω=0)) :
    μ.real E-ε ≤ (CountLaw.ofMeasure μ K1 hK1).success ∧
    (CountLaw.ofMeasure μ K2 hK2).success ≤ μ.real E+ε ∧
    μ.real E-ε ≤ (CountLaw.ofMeasure μ K2 hK2).duplicates := by
  apply original_common_regime_bounds μ E K1 K2 hK1 hK2 ε
  · exact (measureReal_mono (μ := μ) (by
      intro ω hω hG
      exact ((hgood ω hG).1 hω.1).1 hω.2)).trans hbad
  · exact (measureReal_mono (μ := μ) (by
      intro ω hω hG
      exact hω.2 ((hgood ω hG).2 hω.1))).trans hbad
  · exact (measureReal_mono (μ := μ) (by
      intro ω hω hG
      exact hω.2 ((hgood ω hG).1 hω.1).2)).trans hbad

end OriginalRegime

theorem partial_broadcast_charge_gap (μ1 μ2 : CountLaw 2) (G : Schedule 2)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (v V R u p ε b1 b2 : ℝ)
    (hv : v≤ V) (hR : 0≤ R) (hu : 0≤ u) (hp0 : 0≤ p) (hp1 : p≤1) (hε : 0≤ ε)
    (hb1R : R≤ b1) (hb1U : b1≤ R+u) (hb1v : b1≤ v)
    (hb2R : R≤ b2) (hb2v : b2≤ v)
    (hD1 : μ1.duplicates=0) (hS1 : p-ε≤ μ1.success)
    (hS2 : μ2.success≤ p+ε) (hD2 : p-ε≤ μ2.duplicates) :
    η*R*p-u-2*V*ε ≤
      μ1.utility v b1 0 (Schedule.affine 2 η hη0 hη1) G-
      μ2.utility v b2 0 (Schedule.affine 2 η hη0 hη1) G := by
  have hb10 : 0≤ b1 := hR.trans hb1R
  have hb20 : 0≤ b2 := hR.trans hb2R
  have hone := mul_le_mul_of_nonneg_left hS1 (sub_nonneg.mpr hb1v)
  have htwo := mul_le_mul_of_nonneg_left hS2 (sub_nonneg.mpr hb2v)
  have hdup := mul_le_mul_of_nonneg_left hD2 (mul_nonneg hη0 hb20)
  have hprice1 := mul_le_mul_of_nonneg_left hb1U hp0
  have hup := mul_le_mul_of_nonneg_right hp1 hu
  have herror1 := mul_le_mul_of_nonneg_right
    (show v-b1≤ V by linarith) hε
  have hprice2 := mul_le_mul_of_nonneg_left hb2R
    (mul_nonneg hp0 (by linarith : 0≤1+η))
  have herror2 := mul_le_mul_of_nonneg_right
    (show v-(1-η)*b2≤ V by
      have hh := mul_nonneg (sub_nonneg.mpr hη1) hb20
      linarith) hε
  rw [CountLaw.utility_eq,CountLaw.utility_eq,
    CountLaw.charge_affine,CountLaw.charge_affine,hD1]
  nlinarith

section NativePartial
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem native_singleton_duplicates_zero (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) (a : JointAction 2) (hk : a.routeCount=1) :
    ((problem Γ i).outcome a).duplicates=0 := by
  have hload := load_le_routeCount_mul_success Γ i a
  simp only [hk,Nat.cast_one,one_mul] at hload
  exact sub_eq_zero.mpr (le_antisymm hload ((problem Γ i).outcome a).success_le_load)

theorem native_partial_broadcast_excluded (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1) (hg : Γ.g=0)
    (E G : Set (Sample m 2 Seed)) (v V R u ε : ℝ)
    (hv : v≤ V) (hR : 0≤ R) (hu : 0≤ u) (hε : 0≤ ε)
    (a1 a2 : JointAction 2) (hk1 : a1.routeCount=1) (_hk2 : a2.routeCount=2)
    (hb1R : R≤ a1.bid) (hb1U : a1.bid≤ R+u) (hb1v : a1.bid≤ v)
    (hb2R : R≤ a2.bid) (hb2v : a2.bid≤ v)
    (hbad : (sampleLaw Γ).real Gᶜ≤ ε)
    (hgood : ∀ ω∈G,
      (ω∈E → focalCount Γ i a1 ω≠0 ∧ focalCount Γ i a2 ω=2) ∧
      (ω∉E → focalCount Γ i a2 ω=0))
    (hgap : u+2*V*ε < η*R*(sampleLaw Γ).real E) :
    (problem Γ i).payoff v a2 < (problem Γ i).payoff v a1 := by
  have hbounds := original_common_good_event (sampleLaw Γ) E G
    (focalCount Γ i a1) (focalCount Γ i a2)
    (measurable_focalCount Γ i a1) (measurable_focalCount Γ i a2) ε hbad hgood
  rw [←problem_outcome,←problem_outcome] at hbounds
  have h := partial_broadcast_charge_gap
    ((problem Γ i).outcome a1) ((problem Γ i).outcome a2) Γ.G η hη0 hη1
    v V R u ((sampleLaw Γ).real E) ε a1.bid a2.bid
    hv hR hu measureReal_nonneg measureReal_le_one hε
    hb1R hb1U hb1v hb2R hb2v (native_singleton_duplicates_zero Γ i a1 hk1)
    hbounds.1 hbounds.2.1 hbounds.2.2
  have hpay : η*R*(sampleLaw Γ).real E-u-2*V*ε ≤
      (problem Γ i).payoff v a1-(problem Γ i).payoff v a2 := by
    change _ ≤ ((problem Γ i).outcome a1).utility v a1.bid Γ.g Γ.A Γ.G-
      ((problem Γ i).outcome a2).utility v a2.bid Γ.g Γ.A Γ.G
    simpa only [hg,hA] using h
  linarith

end NativePartial
end FCAppendix.Affine.Tail04.GlobalLower
