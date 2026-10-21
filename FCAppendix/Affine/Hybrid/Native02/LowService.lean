import FCAppendix.Affine.Hybrid.Native02.CapacityLimit
import FCAppendix.Finite.ReceiptBoundsAE
import FCAppendix.Finite.NonrareRanks
import FCAppendix.Finite.VisibleQuantiles
import FCAppendix.Existence.SingletonLimits

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open scoped BigOperators

theorem few_rivals_of_accepts_nonnegative {m n c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (G : FiniteGame m n c Seed) (j : Fin n) (i : Fin m)
    (a : ℝ) (ha : 0< a)
    (hA : ∀ r : ℕ,0< r→ r≤ n→ a*(r:ℝ)≤ G.A.charge r)
    (b : ℝ) (hb : 0≤ b) (w : Background m n Seed)
    (belief : Fin m→ FiniteLaw (Fin n))
    (hopt : Finite.Optimal c (beliefReceipts G.A belief (presentList w i b j))
      (G.policy j (presentList w i b j) (w.2 j)).val)
    (hacc : Accepts G i b j w) : rivals i (aboveAt j (b/a)) w< c := by
  classical
  let X := presentList w i b j
  let r := beliefReceipts G.A belief X
  have hri := beliefReceipts_bounds G.A belief X a hA i b hb (presentList_self w i b j)
  by_contra hmany
  have hm : c≤ rivals i (aboveAt j (b/a)) w := le_of_not_gt hmany
  apply Finite.excluded_of_many_better c r _ hopt i ?_ hacc
  rw [rivals_eq_card] at hm
  apply hm.trans (Finset.card_le_card ?_)
  intro l hl
  simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,and_true,
    aboveAt,mem_setOf_eq] at hl
  obtain ⟨hli,hreach,hbid⟩ := hl
  have hsome : X l=some (w.1 l).1.2.bid := by
    rw [show X=presentList w i b j from rfl,presentList_other w i l hli,if_pos hreach]
  have hrl := beliefReceipts_bounds G.A belief X a hA l _
    (w.1 l).1.2.bid_nonneg hsome
  have hab : b< a*(w.1 l).1.2.bid := by
    have hh := mul_lt_mul_of_pos_left hbid ha
    simpa only [mul_div_cancel₀ b ha.ne'] using hh
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  dsimp only [r]
  linarith [hri.2,hrl.1]

theorem acceptProb_upper_nonnegative {m n c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (G : FiniteGame m n c Seed) (j : Fin n)
    (hj : ProposerRationalAtFeasibleLists G j) (i : Fin m) (a : ℝ) (ha : 0< a)
    (hA : ∀ r : ℕ,0< r→ r≤ n→ a*(r:ℝ)≤ G.A.charge r) (b : ℝ) (hb : 0≤ b) :
    acceptProb G i b j≤ binomBelow (m-1) (alphaGt G j (b/a)) c := by
  have hset : MeasurableSet {w : Background m n Seed |
      Accepts G i b j w→ rivals i (aboveAt j (b/a)) w< c} := by
    simpa only [imp_iff_not_or,compl_setOf,setOf_or] using
      (measurableSet_accepts G i b j).compl.union
        (measurableSet_rivals_lt (Seed:=Seed) i (aboveAt j (b/a))
          (measurableSet_aboveAt j (b/a)) c)
  have hae : ∀ᵐw ∂backgroundLaw G,
      Accepts G i b j w→ rivals i (aboveAt j (b/a)) w< c := by
    apply (Measure.ae_prod_iff_ae_ae hset).mpr
    obtain ⟨belief,hopt⟩ := hj
    apply ae_of_all
    intro d
    let X := presentDrawList d i b j
    have hs := hopt X (presentDrawList_feasible d i b hb j)
    have hseed := (measurePreserving_eval (fun _ : Fin n=> G.seedLaw) j).quasiMeasurePreserving.ae hs
    filter_upwards [hseed] with s hs
    exact few_rivals_of_accepts_nonnegative G j i a ha hA b hb (d,s) (belief X) hs
  rw [alphaGt,←prob_rivals_lt G i _ (measurableSet_aboveAt j (b/a)) c,acceptProb]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)

theorem low_raw_success_bound {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : FiniteGame m 2 c Seed) (hprop : ∀ j,ProposerRationalAtFeasibleLists G j)
    (kappa d p delta : ℝ) (hk : 0< kappa)
    (hA : ∀ r : ℕ,0< r→ r≤2→ kappa*(r:ℝ)≤ G.A.charge r)
    (htail : ∀ j,p≤ alphaGt G j (d/kappa))
    (hc : c≤(m-1)+1) (hdelta : 0< delta)
    (hgap : delta≤(m-1:ℕ)*p-(c:ℝ))
    (i : Fin m) (a : JointAction 2) (hab : a.bid≤ d) :
    ((problem G i).outcome a).success≤2*((m-1:ℕ)/(4*delta^2)) := by
  have hj (j : Fin 2) : acceptProb G i a.bid j≤(m-1:ℕ)/(4*delta^2) := by
    apply (acceptProb_upper_nonnegative G j (hprop j) i kappa hk hA a.bid a.bid_nonneg).trans
    have htail' : p≤ alphaGt G j (a.bid/kappa) :=
      (htail j).trans (alphaGt_antitone G j (div_le_div_of_nonneg_right hab hk.le))
    have hslot : delta≤(m-1:ℕ)*alphaGt G j (a.bid/kappa)-(c:ℝ) := by
      have hh := mul_le_mul_of_nonneg_left htail' (Nat.cast_nonneg (m-1) : (0:ℝ)≤(m-1:ℕ))
      linarith
    exact binomBelow_upper_of_gap (m-1) c hc _ delta measureReal_nonneg measureReal_le_one hdelta hslot
  have hm : meanAcceptProb G i a.bid≤(m-1:ℕ)/(4*delta^2) := by
    unfold meanAcceptProb
    rw [Fin.sum_univ_two]
    norm_num only [Nat.cast_ofNat]
    linarith [hj 0,hj 1]
  exact (success_le_n_meanAcceptProb G (by norm_num) i a).trans
    (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤2))

theorem original_low_service_tail {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : FiniteGame m 2 c Seed) (s a h d kappa : ℝ)
    (ha : 0≤ a) (hh : 0≤ h) (hd : 0≤ d) (hk : 0< kappa) (hk1 : kappa≤1)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hjoint : G.F⊗ₘG.σ=populationJoint s a h PL PA PH)
    (hL : ∀ᵐx ∂(PL : Measure (ℝ×JointAction 2)),x.2.bid≤ d)
    (hA : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),d< kappa*x.2.bid ∧ x.2.routeCount=2)
    (hH : ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),d< kappa*x.2.bid ∧ x.2.routeCount=1) :
    ∀ j,alphaGt G j (d/kappa)=a+h/2 := by
  have hdd : d≤ d/kappa := (le_div_iff₀ hk).2 (mul_le_of_le_one_right hd hk1)
  intro j
  apply original_population_active_visible_mass G s a h (d/kappa) ha hh PL PA PH hjoint
  · exact hL.mono (fun _ hx=> hx.trans hdd)
  · exact hA.mono (fun _ hx=>⟨(div_lt_iff₀ hk).2 (by simpa only [mul_comm] using hx.1),hx.2⟩)
  · exact hH.mono (fun _ hx=>⟨(div_lt_iff₀ hk).2 (by simpa only [mul_comm] using hx.1),hx.2⟩)

theorem eventually_uniform_low_service {N C : ℕ→ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : ∀ k,FiniteGame (N k+1) 2 (C k) Seed)
    (hN : Tendsto N atTop atTop) (hc : ∀ k,C k≤ N k+1)
    (kappa d p rho : ℝ) (hk : 0< kappa) (hgap : rho< p)
    (hcap : Tendsto (fun k=>(C k:ℝ)/((N k:ℝ)+1)) atTop (𝓝 rho))
    (hprop : ∀ k j,ProposerRationalAtFeasibleLists (G k) j)
    (hA : ∀ k (r : ℕ),0< r→ r≤2→ kappa*(r:ℝ)≤(G k).A.charge r)
    (htail : ∀ k j,p≤ alphaGt (G k) j (d/kappa)) :
    ∃e : ℕ→ℝ,(∀ k,0≤ e k) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ᶠk in atTop,∀ i : Fin (N k+1),∀ a : JointAction 2,a.bid≤ d→
        ((problem (G k) i).outcome a).success≤ e k := by
  let tau := (p-rho)/2
  have htau : 0< tau := by dsimp only [tau];linarith
  let e : ℕ→ℝ := fun k=>2/(4*(N k:ℝ)*tau^2)
  have he0 : ∀ k,0≤ e k := by intro k;dsimp only [e];positivity
  have he : Tendsto e atTop (𝓝 0) := by
    convert! (rank_error_tendsto_zero N hN tau).const_mul 2 using 1
    · funext k
      dsimp [e]
      ring
    · ring
  have hc' := Existence.RankEnvelope.capacity_rival_density N C hN hcap
  have hr : ∀ᶠk in atTop,tau≤ p-(C k:ℝ)/(N k:ℝ) := by
    have hl := (tendsto_const_nhds (x:=p)).sub hc'
    filter_upwards [hl.eventually (Ioi_mem_nhds (show tau< p-rho by dsimp [tau];linarith))]
      with k hk
    exact hk.le
  refine ⟨e,he0,he,?_⟩
  filter_upwards [hr,hN.eventually_gt_atTop 0] with k hkratio hNk
  intro i a hab
  have hNpos : (0:ℝ)< N k := Nat.cast_pos.mpr hNk
  have hslot : (N k:ℝ)*tau≤(N k:ℝ)*p-C k := by
    have hh := mul_le_mul_of_nonneg_left hkratio hNpos.le
    field_simp [hNpos.ne'] at hh
    nlinarith
  have hb := low_raw_success_bound (G k) (hprop k) kappa d p (N k*tau) hk (hA k)
    (htail k) (by simpa only [Nat.add_sub_cancel] using hc k) (mul_pos hNpos htau)
    (by simpa only [Nat.add_sub_cancel] using hslot) i a hab
  simp only [Nat.add_sub_cancel] at hb
  convert! hb using 1
  dsimp only [e]
  field_simp [hNpos.ne',htau.ne']

theorem low_raw_payoff_bound {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : FiniteGame m 2 c Seed) (hg : G.g=0) (i : Fin m) (v B e : ℝ)
    (hv : 0≤ v) (hB : v≤ B) (he : 0≤ e) (a : JointAction 2)
    (hservice : ((problem G i).outcome a).success≤ e) :
    (problem G i).payoff v a≤ B*e := by
  have hh := ((problem G i).outcome a).utility_le_net_success v a.bid G.g G.A G.G
    a.bid_nonneg G.g_nonneg
  change (problem G i).payoff v a≤ _ at hh
  rw [hg,sub_zero] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hservice hv).trans
    (mul_le_mul_of_nonneg_right hB he))

end FCAppendix.Affine.Hybrid.Native02
