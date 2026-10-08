import FCAppendix.Exclusive.CompletionNarrowFamily

noncomputable section
namespace FCAppendix.Completion.Exclusive
open MeasureTheory ProbabilityTheory Filter Topology Set
open FCAppendix Game Bayes Exclusive Exclusive.Narrow Exclusive.Narrow.Finite
open Bayes.ExclusiveNarrow

def sourceCorridor (d m c : ℕ) (hd : 1 ≤ d) (hm : 0 < m) (hc : 0 < c)
    (X eta : ℝ) (hX : 0 < X) (heta : eta ∈ Ioo (0:ℝ) 1)
    (hspread : spreadRatio d eta ((c:ℝ)/m) < 1) : Corridor (d+1) m c where
  lower := X*(1-eta)
  upper := X*(1+eta)
  lower_pos := mul_pos hX (sub_pos.mpr heta.2)
  width := by nlinarith [mul_pos hX heta.1]
  proposers := by omega
  population := hm
  capacity := hc
  spread := by
    have hsm : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
    have hs : 0 < 1-eta := sub_pos.mpr heta.2
    have ht : 0 < 1+eta := by linarith [heta.1]
    have hw : 0 < inverseBid (d+1) (X*(1+eta)) :=
      inverseBid_pos _ (mul_pos hX ht)
    unfold spreadRatio at hspread
    rw [← inverseBid_ratio_scale d hX hs ht] at hspread
    have hp := mul_lt_mul_of_pos_right hspread (mul_pos hsm hw)
    convert hp using 1
    · rfl
    · field_simp [hsm.ne',hw.ne']
    · ring

theorem corridorPlay_of_class
    {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (P : Corridor n m c)
    (E : Set ℝ) (hE : MeasurableSet E) (hclass : ExclusiveBroadcastOn Γ E)
    (hband : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v,
      v ∈ E → a.bid ∈ Ioo P.lower P.upper) : CorridorPlay Γ P := by
  letI : IsMarkovKernel Γ.σ := Γ.hσ
  have hb : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.1 ∈ E → x.2.bid ∈ Ioo P.lower P.upper :=
    Measure.ae_compProd_of_ae_ae (by
      have hm := (hE.preimage (measurable_fst : Measurable (Prod.fst : ℝ × JointAction n → ℝ))).compl.union
        (measurableSet_Ioo (a := P.lower) (b := P.upper) |>.preimage ((measurable_bid n).comp measurable_snd))
      simpa only [Set.preimage, Set.compl_setOf, Set.setOf_or, imp_iff_not_or, Function.comp_def] using hm) hband
  filter_upwards [hclass,hb] with x hx hxb
  by_cases he : x.1 ∈ E
  · exact Or.inr ⟨(hx.1 he).2,(hxb he).1.le,(hxb he).2.le⟩
  · exact Or.inl (hx.2 he)

theorem scalarCorridor_of_source (d : ℕ) (hd : 1 ≤ d)
    {h rho cap H lam0 eta l u L U : ℝ}
    (hh : 0 < h) (hrho : rho < h) (hcap0 : 0 ≤ cap) (hcap : cap < h)
    (hH : 0 < H) (hL : 0 < L) (heta : eta ∈ Ioo (0:ℝ) 1)
    (hlam : lam0 ∈ Icc (2*L) (U/2))
    (hqL : 1-u ≤ qLower d h eta cap) (hqU : qUpper d h eta cap ≤ 1-l)
    (hpL : (1/2:ℝ) ≤ priceLower d h rho eta cap)
    (hpU : priceUpper d h rho eta cap ≤ 2) :
    ScalarCorridor d
      ((H*lam0/(sourceQ h rho)^d)*(1-eta))
      ((H*lam0/(sourceQ h rho)^d)*(1+eta)) h cap l u (H*L) (H*U) := by
  let X := H*lam0/(sourceQ h rho)^d
  let lo := X*(1-eta)
  let hi := X*(1+eta)
  have hlam0 : 0 < lam0 := (by positivity : 0 < 2*L).trans_le hlam.1
  have hq0 : 0 < sourceQ h rho := by
    dsimp [sourceQ]
    exact sub_pos.mpr ((div_lt_one hh).mpr hrho)
  have hX : 0 < X := by dsimp [X]; positivity
  have hlo : 0 < lo := mul_pos hX (sub_pos.mpr heta.2)
  have hhi : 0 < hi := mul_pos hX (by linarith [heta.1])
  have hband : lo ≤ hi := by dsimp [lo,hi]; nlinarith [mul_pos hX heta.1]
  have hweight : h*inverseBid (d+1) hi ≤ h*inverseBid (d+1) lo :=
    mul_le_mul_of_nonneg_left (inverseBid_antitone (d+1) (by omega) hlo hband) hh.le
  have hloW : h*inverseBid (d+1) lo ∈
      Icc (h*inverseBid (d+1) hi) (h*inverseBid (d+1) lo) := ⟨hweight,le_rfl⟩
  have hhiW : h*inverseBid (d+1) hi ∈
      Icc (h*inverseBid (d+1) hi) (h*inverseBid (d+1) lo) := ⟨le_rfl,hweight⟩
  have hlowExposure := relative_exposure_corridor d hd hh hcap hX heta
    (show hi ∈ Icc lo hi from ⟨hband,le_rfl⟩) hloW
  have huppExposure := relative_exposure_corridor d hd hh hcap hX heta
    (show lo ∈ Icc lo hi from ⟨le_rfl,hband⟩) hhiW
  have hlowPrice := relative_price_corridor d hd hh hrho hcap hH hlam0 heta hloW
  have huppPrice := relative_price_corridor d hd hh hrho hcap hH hlam0 heta hhiW
  have hden : 0 < H*lam0 := mul_pos hH hlam0
  have hnormL : (1/2:ℝ) ≤ ((h-cap)/(h*inverseBid (d+1) lo))^d/(H*lam0) :=
    hpL.trans hlowPrice.1
  have hnormU : ((h-cap)/(h*inverseBid (d+1) hi))^d/(H*lam0) ≤ 2 :=
    huppPrice.2.trans hpU
  refine ⟨hcap0,hcap,hqL.trans hlowExposure.1,huppExposure.2.trans hqU,?_,?_⟩
  · have hs := (le_div_iff₀ hden).mp hnormL
    have ht := mul_le_mul_of_nonneg_left hlam.1 hH.le
    nlinarith
  · have hs := (div_le_iff₀ hden).mp hnormU
    have ht := mul_le_mul_of_nonneg_left hlam.2 hH.le
    nlinarith

theorem source_slope_bounds (d : ℕ) (hd : 1 ≤ d) (G : Schedule (d+1))
    {l u L U : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u < 1)
    (hL : 0 < L) (hLU : L ≤ U) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ H g : ℝ, 0 < H → 0 ≤ g → g/H < eps →
      ∃ k K : ℝ, 0 < k ∧ 0 ≤ K ∧
        ∀ a : UserTariff, a.Allowed → ∀ lam ∈ Icc (H*L) (H*U),
          ∀ p ∈ Icc l u,
            lam*dfTariff d a p+g*deriv (baseMarginalCost d G) p ∈ Icc k K := by
  obtain ⟨eps,Fmin,Fmax,Dmin,Dmax,Kbase,heps,_hFm,_hFM,hDm,hDM,_hKb,hbounds,hguard⟩ :=
    exists_uniform_small_base_guard d hd G hl hlu hu hL hLU
  obtain ⟨Kbase',hKb',hbase⟩ := base_derivative_bound d G hlu hu
  refine ⟨eps,heps,?_⟩
  intro H g hH hg hsmall
  let k := H*L*Dmin/2
  let K := H*U*Dmax+g*Kbase'
  have hU : 0 < U := hL.trans_le hLU
  have hDmax : 0 < Dmax := hDm.trans_le hDM
  refine ⟨k,K,by dsimp [k]; positivity,by dsimp [K]; positivity,?_⟩
  intro a ha lam hlam p hp
  refine ⟨(hguard H g lam hH hg hsmall hlam a ha).1 p hp,?_⟩
  have hlam0 : 0 ≤ lam := (mul_pos hH hL).le.trans hlam.1
  have hdf := (hbounds a ha p hp).2
  have hfirst : lam*dfTariff d a p ≤ H*U*Dmax :=
    mul_le_mul hlam.2 hdf.2 (hDm.le.trans hdf.1) (mul_pos hH hU).le
  have hsecond : g*deriv (baseMarginalCost d G) p ≤ g*Kbase' :=
    mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (hbase p hp)) hg
  exact add_le_add hfirst hsecond

theorem source_family_scalar_inputs (d : ℕ) (hd : 1 ≤ d) (G : Schedule (d+1))
    {h rho : ℝ} (hh : 0 < h) (hrho : 0 < rho) (hrhoh : rho < h) (hh1 : h ≤ 1) :
    ∃ eta delta l u L U eps : ℝ,
      eta ∈ Ioo (0:ℝ) 1 ∧ 0 < delta ∧ 0 < l ∧ l < u ∧ u < 1 ∧
      0 < L ∧ L ≤ U ∧ 0 < eps ∧
      ∀ H g : ℝ, 0 < H → 0 ≤ g → g/H < eps →
        ∃ k K : ℝ, 0 < k ∧ 0 ≤ K ∧
          ∀ a : UserTariff, a.Allowed →
            (∀ cap : ℝ, |cap-rho| < delta →
              ScalarCorridor d (H*sourceBid d a h rho*(1-eta))
                (H*sourceBid d a h rho*(1+eta)) h cap l u (H*L) (H*U) ∧
              spreadRatio d eta cap < 1) ∧
            (∀ lam ∈ Icc (H*L) (H*U), ∀ p ∈ Icc l u,
              lam*dfTariff d a p+g*deriv (baseMarginalCost d G) p ∈ Icc k K) := by
  obtain ⟨eta0,delta,l,u,L,U,eps0,heta0,hdelta,hl,hlu,hu,hL,hLU,_heps0,hprice,hscalar,_hmono⟩ :=
    select_source_rectangle d hd G hh hrho hrhoh hh1
  obtain ⟨eps,heps,hslope⟩ := source_slope_bounds d hd G hl.le hlu.le hu hL hLU
  let eta := eta0/2
  have heta : eta ∈ Ioo (0:ℝ) 1 := by dsimp [eta]; constructor <;> linarith [heta0.1,heta0.2]
  have habs : |eta| < eta0 := by rw [abs_of_pos heta.1]; dsimp [eta]; linarith [heta0.1]
  refine ⟨eta,delta,l,u,L,U,eps,heta,hdelta,hl,hlu,hu,hL,hLU,heps,?_⟩
  intro H g hH hg hsmall
  obtain ⟨k,K,hk,hK,hderiv⟩ := hslope H g hH hg hsmall
  refine ⟨k,K,hk,hK,?_⟩
  intro a ha
  refine ⟨?_,hderiv a ha⟩
  intro cap hcap
  obtain ⟨hc0,hch,hqL,hqU,hpL,hpU,hspread⟩ := hscalar eta cap habs hcap
  have hc := scalarCorridor_of_source d hd hh hrhoh hc0.le hch hH hL heta
    (hprice a ha) hqL.le hqU.le hpL.le hpU.le
  have hcenter : H*sourcePrice d a h rho/(sourceQ h rho)^d = H*sourceBid d a h rho := by
    unfold sourceBid
    ring
  rw [hcenter] at hc
  exact ⟨hc,hspread⟩

theorem source_scalar_corridor_eventually
    {d : ℕ} {M C : ℕ → ℕ} {lo hi h rho l u L U delta : ℝ}
    (hdelta : 0 < delta)
    (hlocal : ∀ cap : ℝ, |cap-rho| < delta → ScalarCorridor d lo hi h cap l u L U)
    (hcap : Tendsto (fun t => (C t:ℝ)/M t) atTop (𝓝 rho)) :
    ∀ᶠ t in atTop, ScalarCorridor d lo hi h ((C t:ℝ)/M t) l u L U := by
  filter_upwards [hcap.eventually (Metric.ball_mem_nhds rho hdelta)] with t ht
  exact hlocal _ (by simpa [Metric.mem_ball,Real.dist_eq] using ht)

def extendPureTail (T0 : ℕ) (b0 : ℝ) (beta : ℕ → ℝ → ℝ) (t : ℕ) : ℝ → ℝ :=
  if T0 ≤ t then beta (t-T0) else fun _ => b0

theorem extendPureTail_shift (T0 : ℕ) (b0 : ℝ) (beta : ℕ → ℝ → ℝ) (t : ℕ) :
    extendPureTail T0 b0 beta (t+T0) = beta t := by
  simp [extendPureTail]

theorem restore_narrow_tail
    {d : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    (Γ : (t : ℕ) → FiniteGame (M t) (d+1) (C t) Seed)
    (mu : Measure ℝ) (T0 : ℕ) (b0 : ℝ) (betaTail : ℕ → ℝ → ℝ)
    (bidInf pInf : ℝ → ℝ)
    (hmono : ∀ t, Monotone (betaTail t)) (hmeas : ∀ t, Measurable (betaTail t))
    (hpure : ∀ t, ∀ᵐ v ∂mu, ∀ᵐ a ∂(Γ (t+T0)).σ v, a.bid = betaTail t v)
    (hbid : ∀ᵐ v ∂mu, Tendsto (fun t => betaTail t v) atTop (𝓝 (bidInf v)))
    (hcount : ∀ᵐ v ∂mu, ∀ I : (t : ℕ) → Fin (M (t+T0)), ∀ j : Fin (d+1+1),
      Tendsto (fun t => (typeOutcome (Γ (t+T0)) (I t) v).mass j) atTop
        (𝓝 (PayOnce.ManyProposers.binomialMass (d+1) (pInf v) j.val))) :
    ∃ beta : ℕ → ℝ → ℝ,
      (∀ t, Monotone (beta t) ∧ Measurable (beta t)) ∧
      (∀ᶠ t in atTop, ∀ᵐ v ∂mu, ∀ᵐ a ∂(Γ t).σ v, a.bid = beta t v) ∧
      (∀ᵐ v ∂mu, Tendsto (fun t => beta t v) atTop (𝓝 (bidInf v))) ∧
      (∀ᵐ v ∂mu, ∀ I : (t : ℕ) → Fin (M t), ∀ j : Fin (d+1+1),
        Tendsto (fun t => (typeOutcome (Γ t) (I t) v).mass j) atTop
          (𝓝 (PayOnce.ManyProposers.binomialMass (d+1) (pInf v) j.val))) := by
  let beta := extendPureTail T0 b0 betaTail
  refine ⟨beta,?_,?_,?_,?_⟩
  · intro t
    by_cases ht : T0 ≤ t
    · simpa [beta,extendPureTail,ht] using And.intro (hmono (t-T0)) (hmeas (t-T0))
    · simp only [beta,extendPureTail,ht,if_false]
      exact ⟨monotone_const,measurable_const⟩
  · filter_upwards [eventually_ge_atTop T0] with t ht
    have hp := hpure (t-T0)
    have hidx : t-T0+T0 = t := by omega
    rw [hidx] at hp
    simpa only [beta,extendPureTail,if_pos ht] using hp
  · apply ae_full_sequence_from_tail beta bidInf T0
    simpa [beta,extendPureTail_shift] using hbid
  · filter_upwards [hcount] with v hv
    intro I j
    exact full_sequence_from_tail (fun t => (typeOutcome (Γ t) (I t) v).mass j)
      (PayOnce.ManyProposers.binomialMass (d+1) (pInf v) j.val) T0
      (hv (fun t => I (t+T0)) j)

end FCAppendix.Completion.Exclusive
