import FCAppendix.Exclusive.NarrowExistenceGameAffine
import FCAppendix.Exclusive.NarrowExistenceGameCount

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

def stateBoxLower : RowState := ![0, 0, Real.exp (-1), 0, 0]
def stateBoxUpper : RowState := ![1, 1, Real.exp 1, 2, 1]
def stateBox : Set RowState := Icc stateBoxLower stateBoxUpper

theorem isCompact_stateBox : IsCompact stateBox := isCompact_Icc

theorem sourceReferenceState_mem_box {p0 : ℝ} (hp0 : 0 < p0) (hp1 : p0 < 1) :
    sourceReferenceState p0 ∈ stateBox := by
  constructor <;> intro i <;> fin_cases i <;>
    simp [stateBoxLower, stateBoxUpper, sourceReferenceState]
  all_goals linarith

theorem profileFailure_lt_one_of_full_ratio
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (r delta : ℝ) (hr : 0 ≤ r) (z : ι → ℝ)
    (hz : ∀ i, z i ∈ Icc (-delta) delta) (M c : ℕ)
    (hM : 0 < M) (hNM : Fintype.card ι ≤ M)
    (hsafe : (1-(c : ℝ)/(M : ℝ))*Real.exp (2*r*delta) < 1) (i : ι) :
    ((Fintype.card ι-c : ℕ) : ℝ)*profileShare r z i < 1 := by
  by_cases hcN : Fintype.card ι ≤ c
  · simp [Nat.sub_eq_zero_of_le hcN]
  have hNc : c ≤ Fintype.card ι := by omega
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hfrac : (c : ℝ)/(M : ℝ) ≤ (c : ℝ)/(Fintype.card ι : ℝ) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg c) hN (by exact_mod_cast hNM)
  have hf := (profileFailure_bounds r delta hr z hz i c hNc).2
  have hmul := mul_le_mul_of_nonneg_right (show
      1-(c : ℝ)/(Fintype.card ι : ℝ) ≤ 1-(c : ℝ)/(M : ℝ) by linarith)
    (Real.exp_pos (2*r*delta)).le
  exact hf.trans_lt (hmul.trans_lt hsafe)

theorem finiteRowState_mem_box {m : ℕ} {V : Type*}
    (d c : ℕ) (delta baseRatio : ℝ) (hdelta : delta ≤ 1)
    (hbase : baseRatio ∈ Icc (0 : ℝ) 1) (beta : V → ℝ)
    (hbeta : ∀ v, beta v ∈ Icc (-delta) delta)
    (v z : ℝ) (hv : v ∈ Icc (0 : ℝ) 2) (hz : z ∈ Icc (-delta) delta)
    (omega : RivalProfile m V)
    (hsafe : (1-(c : ℝ)/((m : ℝ)+1))*Real.exp (2*(1/(d : ℝ))*delta) < 1) :
    finiteRowState d c baseRatio beta v z omega ∈ stateBox := by
  let r : ℝ := 1/(d : ℝ)
  let Z := activeLogProfile beta z omega
  have hband := activeLogProfile_band beta delta z hz hbeta omega
  have hshare := logShare_eq_activeProfileShare r beta z omega
  have hpos : 0 < logShare r (rivalInverseSum r beta omega) z :=
    hshare ▸ profileShare_pos r Z none
  have hle : logShare r (rivalInverseSum r beta omega) z ≤ 1 :=
    hshare ▸ profileShare_le_one r Z none
  have hN : Fintype.card (ActiveIndex omega) ≤ m+1 := by
    rw [activeIndex_card]
    have := activeCount_le omega
    omega
  have hq := profileFailure_lt_one_of_full_ratio r delta (by dsimp [r]; positivity)
    Z hband (m+1) c (by omega) hN (by simpa only [Nat.cast_add, Nat.cast_one] using hsafe) none
  rw [activeIndex_card, ← hshare] at hq
  have hq0 : 0 ≤ ((1+activeCount omega-c : ℕ) : ℝ)*
      logShare r (rivalInverseSum r beta omega) z :=
    mul_nonneg (Nat.cast_nonneg _) hpos.le
  have hexlo : Real.exp (-1) ≤ Real.exp z := Real.exp_le_exp.mpr (by linarith [hz.1])
  have hexhi : Real.exp z ≤ Real.exp 1 := Real.exp_le_exp.mpr (hz.2.trans hdelta)
  constructor
  · intro i
    fin_cases i
    · exact hq0
    · exact hpos.le
    · exact hexlo
    · exact hv.1
    · exact hbase.1
  · intro i
    fin_cases i
    · exact hq.le
    · exact hle
    · exact hexhi
    · exact hv.2
    · exact hbase.2

theorem finiteRowState_dist_lt {m : ℕ} {V : Type*}
    (d c : ℕ) (baseRatio : ℝ) (beta : V → ℝ) (v z p0 radius : ℝ)
    (omega : RivalProfile m V) (hradius : 0 < radius)
    (hq : |((1+activeCount omega-c : ℕ) : ℝ)*
      logShare (1/(d : ℝ)) (rivalInverseSum (1/(d : ℝ)) beta omega) z-(1-p0)| < radius)
    (hs : logShare (1/(d : ℝ)) (rivalInverseSum (1/(d : ℝ)) beta omega) z < radius)
    (he : |Real.exp z-1| < radius) (hv : |v-1| < radius) (hb : |baseRatio| < radius) :
    dist (finiteRowState d c baseRatio beta v z omega) (sourceReferenceState p0) < radius := by
  apply (dist_pi_lt_iff hradius).mpr
  intro i
  have hsp : 0 ≤ logShare (1/(d : ℝ)) (rivalInverseSum (1/(d : ℝ)) beta omega) z := by
    rw [logShare_eq_activeProfileShare]
    exact (profileShare_pos _ _ none).le
  fin_cases i
  · exact hq
  · change |logShare (1/(d : ℝ)) (rivalInverseSum (1/(d : ℝ)) beta omega) z-0| < radius
    simpa only [sub_zero, abs_of_nonneg hsp] using hs
  · exact he
  · exact hv
  · change |baseRatio-0| < radius
    simpa only [sub_zero] using hb

theorem sampled_state_neighborhood (d : ℕ) (h rho radius : ℝ)
    (hh : 0 < h) (hrho : 0 < rho) (hrh : rho < h) (hradius : 0 < radius) :
    ∃ delta eps eta : ℝ, ∃ M0 : ℕ,
      0 < delta ∧ delta ≤ 1 ∧ 0 < eps ∧ eps < 1 ∧ 0 < eta ∧ 0 < M0 ∧
      ∀ {m : ℕ} {V : Type*} (c : ℕ), M0 ≤ m+1 →
      |(c : ℝ)/((m : ℝ)+1)-rho| < eta →
      ∀ (beta : V → ℝ), (∀ v, beta v ∈ Icc (-delta) delta) →
      ∀ (v z baseRatio : ℝ), v ∈ Icc (1-eps) (1+eps) →
      z ∈ Icc (-delta) delta → baseRatio ∈ Icc (0 : ℝ) eps →
      ∀ omega : RivalProfile m V,
      |(1+(activeCount omega : ℝ))/((m : ℝ)+1)-h| < eta →
      dist (finiteRowState d c baseRatio beta v z omega)
        (sourceReferenceState (rho/h)) < radius := by
  obtain ⟨dt, eta, M0, hdt, heta, hM0, ht⟩ :=
    finite_profile_state_neighborhood (1/(d : ℝ)) h rho (radius/2)
      (by positivity) hh hrho hrh (by positivity)
  have he := Real.continuous_exp.continuousAt.eventually
    (Metric.ball_mem_nhds (Real.exp 0) hradius)
  obtain ⟨de, hde, hball⟩ := Metric.mem_nhds_iff.mp he
  let delta := min dt (min 1 de)/2
  let eps := min 1 radius/4
  have hdpos : 0 < delta := by dsimp [delta]; positivity
  have hddt : delta ≤ dt := by have := min_le_left dt (min 1 de); dsimp [delta]; linarith
  have hd1 : delta ≤ 1 := by
    have := (min_le_right dt (min 1 de)).trans (min_le_left 1 de)
    dsimp [delta]
    linarith
  have hdde : delta < de := by
    have := (min_le_right dt (min 1 de)).trans (min_le_right 1 de)
    dsimp [delta]
    linarith
  have heps : 0 < eps := by dsimp [eps]; positivity
  have heps1 : eps < 1 := by have := min_le_left (1 : ℝ) radius; dsimp [eps]; linarith
  have hepsr : eps < radius := by have := min_le_right (1 : ℝ) radius; dsimp [eps]; linarith
  refine ⟨delta, eps, eta, M0, hdpos, hd1, heps, heps1, heta, hM0, ?_⟩
  intro m V c hM hC beta hb v z baseRatio hv hz hbase omega hN
  have hb' : ∀ v, beta v ∈ Icc (-dt) dt := fun v =>
    ⟨by linarith [(hb v).1], (hb v).2.trans hddt⟩
  have hz' : z ∈ Icc (-dt) dt := ⟨by linarith [hz.1], hz.2.trans hddt⟩
  have hs := ht (ActiveIndex omega) (m+1) c hM (activeLogProfile beta z omega)
    (activeLogProfile_band beta dt z hz' hb' omega)
    (by simpa only [activeIndex_card, Nat.cast_add, Nat.cast_one] using hN)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hC) none
  have hshare := logShare_eq_activeProfileShare (1/(d : ℝ)) beta z omega
  have hq : |((1+activeCount omega-c : ℕ) : ℝ)*
      logShare (1/(d : ℝ)) (rivalInverseSum (1/(d : ℝ)) beta omega) z-(1-rho/h)| < radius := by
    have hh' := hs.2.1
    rw [activeIndex_card, ← hshare] at hh'
    linarith
  have hsmall : logShare (1/(d : ℝ)) (rivalInverseSum (1/(d : ℝ)) beta omega) z < radius := by
    rw [hshare]
    linarith [hs.2.2]
  have hex : |Real.exp z-1| < radius := by
    have hzde : z ∈ Metric.ball (0 : ℝ) de := by
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
      exact (abs_le.mpr ⟨by linarith [hz.1], hz.2⟩).trans_lt hdde
    simpa only [Metric.mem_ball, Real.dist_eq, Real.exp_zero, mem_setOf_eq] using hball hzde
  apply finiteRowState_dist_lt d c baseRatio beta v z (rho/h) radius omega hradius hq hsmall hex
  · exact (abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩).trans_lt hepsr
  · simpa only [abs_of_nonneg hbase.1] using hbase.2.trans_lt hepsr

theorem exists_all_active_log_band (r rho : ℝ) (hrho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      (1-rho/2)*Real.exp (2*r*delta) < 1 := by
  have hc : Continuous (fun z : ℝ => (1-rho/2)*Real.exp (2*r*z)) := by fun_prop
  have he := hc.continuousAt.eventually (eventually_lt_nhds
    (show (1-rho/2)*Real.exp (2*r*0) < 1 by simp; linarith))
  obtain ⟨de, hde, hball⟩ := Metric.mem_nhds_iff.mp he
  let delta := min 1 de/2
  have hdpos : 0 < delta := by dsimp [delta]; positivity
  have hd1 : delta ≤ 1 := by have := min_le_left (1 : ℝ) de; dsimp [delta]; linarith
  refine ⟨delta, hdpos, hd1, ?_⟩
  apply hball
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hdpos]
  have := min_le_right (1 : ℝ) de
  dsimp [delta]
  linarith

theorem exists_reference_curvature_floor (d : ℕ) (hd : 1 ≤ d)
    (p0 : ℝ) (hp0 : 0 < p0) (hp1 : p0 < 1) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ a : UserTariff, a.Allowed →
      kappa ≤ literalReferenceCurvature d a p0 := by
  let ku := literalReferenceCurvature d .unique p0
  let k0 := literalReferenceCurvature d (.affine 0) p0
  let k1 := literalReferenceCurvature d (.affine 1) p0
  have hku : 0 < ku := (literal_reference_bounds d hd .unique trivial p0 hp0 hp1).1
  have hk0 : 0 < k0 := (literal_reference_bounds d hd (.affine 0)
    (by constructor <;> norm_num) p0 hp0 hp1).1
  have hk1 : 0 < k1 := (literal_reference_bounds d hd (.affine 1)
    (by constructor <;> norm_num) p0 hp0 hp1).1
  let kappa := min ku (min k0 k1)
  have h0 : kappa ≤ k0 := (min_le_right ku (min k0 k1)).trans (min_le_left k0 k1)
  have h1 : kappa ≤ k1 := (min_le_right ku (min k0 k1)).trans (min_le_right k0 k1)
  refine ⟨kappa, by dsimp [kappa]; positivity, ?_⟩
  intro a ha
  cases a with
  | unique => exact min_le_left _ _
  | affine eta =>
    rw [literalReferenceCurvature_affine d hd eta p0 hp0 hp1]
    have hl := mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr ha.2)
    have hr := mul_le_mul_of_nonneg_left h1 ha.1
    change kappa ≤ (1-eta)*k0+eta*k1
    nlinarith

structure UniformFiniteConstants (d : ℕ) (G : Schedule (d+1)) (h rho : ℝ) where
  delta : ℝ
  eps : ℝ
  eta : ℝ
  kappa : ℝ
  B : ℝ
  M0 : ℕ
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  eps_pos : 0 < eps
  eps_lt_one : eps < 1
  eta_pos : 0 < eta
  kappa_pos : 0 < kappa
  B_pos : 0 < B
  M0_pos : 0 < M0
  reference : ∀ a : UserTariff, a.Allowed →
    kappa ≤ literalReferenceCurvature d a (rho/h) ∧ literalReferenceCurvature d a (rho/h) ≤ B
  capacity_pos : ∀ {m : ℕ} (c : ℕ), M0 ≤ m+1 →
    |(c : ℝ)/((m : ℝ)+1)-rho| < eta → 0 < c
  typical_overload : ∀ {m : ℕ} (c : ℕ), M0 ≤ m+1 →
    |(c : ℝ)/((m : ℝ)+1)-rho| < eta → ∀ omega : RivalProfile m (ValueBand eps),
    |(1+(activeCount omega : ℝ))/((m : ℝ)+1)-h| < eta → c < 1+activeCount omega
  safe : ∀ {m : ℕ} (c : ℕ), M0 ≤ m+1 → |(c : ℝ)/((m : ℝ)+1)-rho| < eta →
    (1-(c : ℝ)/((m : ℝ)+1))*Real.exp (2*(1/(d : ℝ))*delta) < 1
  all_rows : ∀ {m : ℕ} {V : Type} (c : ℕ), M0 ≤ m+1 → |(c : ℝ)/((m : ℝ)+1)-rho| < eta →
    ∀ a : UserTariff, a.Allowed → ∀ (beta : V → ℝ),
    (∀ v, beta v ∈ Icc (-delta) delta) →
    ∀ (v z baseRatio : ℝ), v ∈ Icc (1-eps) (1+eps) → z ∈ Icc (-delta) delta →
    baseRatio ∈ Icc (0 : ℝ) eps → ∀ omega : RivalProfile m V,
      |finiteRowScore d c a G (rho/h) baseRatio beta v z omega| ≤ B ∧
      |sourceStateCurvature d a G (rho/h) (finiteRowState d c baseRatio beta v z omega)| ≤ B ∧
      |sourceStateInfluence d a G (rho/h) (finiteRowState d c baseRatio beta v z omega)| ≤ B
  good_rows : ∀ {m : ℕ} {V : Type} (c : ℕ), M0 ≤ m+1 → |(c : ℝ)/((m : ℝ)+1)-rho| < eta →
    ∀ a : UserTariff, a.Allowed → ∀ (beta : V → ℝ),
    (∀ v, beta v ∈ Icc (-delta) delta) →
    ∀ (v z baseRatio : ℝ), v ∈ Icc (1-eps) (1+eps) → z ∈ Icc (-delta) delta →
    baseRatio ∈ Icc (0 : ℝ) eps → ∀ omega : RivalProfile m V,
    |(1+(activeCount omega : ℝ))/((m : ℝ)+1)-h| < eta →
      (11/12 : ℝ)*literalReferenceCurvature d a (rho/h) ≤
        sourceStateCurvature d a G (rho/h) (finiteRowState d c baseRatio beta v z omega) ∧
      |sourceStateInfluence d a G (rho/h) (finiteRowState d c baseRatio beta v z omega)| ≤
        (17/24 : ℝ)*literalReferenceCurvature d a (rho/h)
  central_rows : ∀ {m : ℕ} {V : Type} (c : ℕ), M0 ≤ m+1 → |(c : ℝ)/((m : ℝ)+1)-rho| < eta →
    ∀ a : UserTariff, a.Allowed → ∀ (v baseRatio : ℝ), v ∈ Icc (1-eps) (1+eps) →
    baseRatio ∈ Icc (0 : ℝ) eps → ∀ omega : RivalProfile m V,
    |(1+(activeCount omega : ℝ))/((m : ℝ)+1)-h| < eta →
      |finiteRowScore d c a G (rho/h) baseRatio (fun _ => 0) v 0 omega| ≤ kappa*delta/48
  rare : ∀ (hh : h ∈ Icc (0 : ℝ) 1) {m : ℕ}, M0 ≤ m+1 →
    ∀ (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu],
      (iidRivalLaw m ⟨h, hh⟩ nu).real
        {omega | eta ≤ |(1+(activeCount omega : ℝ))/((m : ℝ)+1)-h|} ≤
        min (kappa/(48*B)) (kappa*delta/(48*B))

theorem exists_uniform_finite_constants_bounded (d : ℕ) (hd : 1 ≤ d)
    (G : Schedule (d+1)) (h rho : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hrho : 0 < rho) (hrh : rho < h)
    (deltaCap epsCap etaCap : ℝ) (hdeltaCap : 0 < deltaCap)
    (hepsCap : 0 < epsCap) (hetaCap : 0 < etaCap) :
    ∃ C : UniformFiniteConstants d G h rho,
      C.delta ≤ deltaCap ∧ C.eps ≤ epsCap ∧ C.eta ≤ etaCap := by
  have hp0 : 0 < rho/h := div_pos hrho hh
  have hp1 : rho/h < 1 := (div_lt_one hh).mpr hrh
  obtain ⟨kappa, hkappa, hkref⟩ := exists_reference_curvature_floor d hd (rho/h) hp0 hp1
  obtain ⟨B, hB, hb⟩ := source_uniform_bounds d G (rho/h) stateBox isCompact_stateBox
  obtain ⟨radiusK, hradiusK, hK⟩ :=
    source_uniform_neighborhood d hd G (rho/h) 1 hp0 hp1 (by norm_num)
  obtain ⟨dk, ek, etak, Mk, hdk, hdk1, hek, hek1, hetak, hMk, hstateK⟩ :=
    sampled_state_neighborhood d h rho radiusK hh hrho hrh hradiusK
  obtain ⟨da, hda, _hda1, hactive⟩ := exists_all_active_log_band (1/(d : ℝ)) rho hrho
  let delta := min (min dk da) deltaCap
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdeltaK : delta ≤ dk := (min_le_left _ _).trans (min_le_left _ _)
  have hdeltaA : delta ≤ da := (min_le_left _ _).trans (min_le_right _ _)
  have hdelta1 : delta ≤ 1 := hdeltaK.trans hdk1
  obtain ⟨radiusS, hradiusS, hS⟩ := source_uniform_neighborhood d hd G (rho/h)
    (kappa*delta/48) hp0 hp1 (by positivity)
  obtain ⟨ds, es, etas, Ms, hds, _hds1, hes, _hes1, hetas, hMs, hstateS⟩ :=
    sampled_state_neighborhood d h rho radiusS hh hrho hrh hradiusS
  let eps := min (min ek es) epsCap
  let eta := min (min etak (min etas (min (rho/2) ((h-rho)/4)))) etaCap
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hepsK : eps ≤ ek := (min_le_left _ _).trans (min_le_left _ _)
  have hepsS : eps ≤ es := (min_le_left _ _).trans (min_le_right _ _)
  have heps1 : eps < 1 := hepsK.trans_lt hek1
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetaK : eta ≤ etak := (min_le_left _ _).trans (min_le_left _ _)
  have hetaS : eta ≤ etas :=
    ((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hetaR : eta ≤ rho/2 :=
    (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hetaGap : eta ≤ (h-rho)/4 :=
    (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hrarepos : 0 < min (kappa/(48*B)) (kappa*delta/(48*B)) := by positivity
  obtain ⟨Mr, hMr⟩ := exists_count_bad_probability_bound (V := ValueBand eps)
    (⟨h, hh.le, hh1⟩ : unitInterval) heta hrarepos
  let M0 := max Mk (max Ms (Mr+1))
  have hM0k : Mk ≤ M0 := le_max_left _ _
  have hM0s : Ms ≤ M0 := (le_max_left _ _).trans (le_max_right _ _)
  have hM0r : Mr+1 ≤ M0 := (le_max_right _ _).trans (le_max_right _ _)
  have hsafe : ∀ {m : ℕ} (c : ℕ), M0 ≤ m+1 →
      |(c : ℝ)/((m : ℝ)+1)-rho| < eta →
      (1-(c : ℝ)/((m : ℝ)+1))*Real.exp (2*(1/(d : ℝ))*delta) < 1 := by
    intro m c _ hC
    have hratio : rho/2 < (c : ℝ)/((m : ℝ)+1) := by
      have := (abs_lt.mp hC).1
      linarith
    have ha : 0 ≤ 1-rho/2 := by linarith
    have he : Real.exp (2*(1/(d : ℝ))*delta) ≤ Real.exp (2*(1/(d : ℝ))*da) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdeltaA (by positivity))
    exact ((mul_le_mul_of_nonneg_right (show 1-(c : ℝ)/((m : ℝ)+1) ≤ 1-rho/2 by linarith)
      (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_left he ha)).trans_lt hactive
  refine ⟨{
    delta := delta
    eps := eps
    eta := eta
    kappa := kappa
    B := B
    M0 := M0
    delta_pos := hdelta
    delta_le_one := hdelta1
    eps_pos := heps
    eps_lt_one := heps1
    eta_pos := heta
    kappa_pos := hkappa
    B_pos := hB
    M0_pos := hMk.trans_le hM0k
    reference := ?_
    capacity_pos := ?_
    typical_overload := ?_
    safe := hsafe
    all_rows := ?_
    good_rows := ?_
    central_rows := ?_
    rare := ?_ }, ?_, ?_, ?_⟩
  · intro a ha
    have hbref := (hb a ha _ (sourceReferenceState_mem_box hp0 hp1)).2.1
    rw [(sourceStateCurvature_reference d hd a G (rho/h) hp0 hp1).1] at hbref
    exact ⟨hkref a ha, (le_abs_self _).trans hbref⟩
  · intro m c _ hC
    have hratio : 0 < (c : ℝ)/((m : ℝ)+1) := by
      have := (abs_lt.mp hC).1
      linarith
    exact Nat.cast_pos.mp ((div_pos_iff_of_pos_right (by positivity)).mp hratio)
  · intro m c _ hC omega hN
    have hratio : (c : ℝ)/((m : ℝ)+1) <
        (1+(activeCount omega : ℝ))/((m : ℝ)+1) := by
      have hc := (abs_lt.mp hC).2
      have hn := (abs_lt.mp hN).1
      linarith
    have hnum := (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < (m : ℝ)+1)).mp hratio
    exact_mod_cast hnum
  · intro m V c hM hC a ha beta hbeta v z baseRatio hv hz hbase omega
    have hv' : v ∈ Icc (0 : ℝ) 2 := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hbase' : baseRatio ∈ Icc (0 : ℝ) 1 := ⟨hbase.1, hbase.2.trans heps1.le⟩
    have hbox := finiteRowState_mem_box d c delta baseRatio hdelta1 hbase' beta hbeta
      v z hv' hz omega (hsafe c hM hC)
    simpa only [finiteRowScore_eq_sourceStateScore] using hb a ha _ hbox
  · intro m V c hM hC a ha beta hbeta v z baseRatio hv hz hbase omega hN
    have hbetaK : ∀ v, beta v ∈ Icc (-dk) dk := fun v =>
      ⟨by linarith [(hbeta v).1], (hbeta v).2.trans hdeltaK⟩
    have hvK : v ∈ Icc (1-ek) (1+ek) := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hzK : z ∈ Icc (-dk) dk := ⟨by linarith [hz.1], hz.2.trans hdeltaK⟩
    have hnear := hstateK c (hM0k.trans hM) (hC.trans_le hetaK) beta hbetaK
      v z baseRatio hvK hzK ⟨hbase.1, hbase.2.trans hepsK⟩ omega (hN.trans_le hetaK)
    have hg := hK a ha _ hnear
    have hlow := (abs_lt.mp hg.1).1
    have ht := abs_sub_le
      (sourceStateInfluence d a G (rho/h) (finiteRowState d c baseRatio beta v z omega))
      (literalReferenceCross d a (rho/h)) 0
    rw [sub_zero, sub_zero] at ht
    have hc := (literal_reference_bounds d hd a ha (rho/h) hp0 hp1).2
    constructor <;> linarith [hg.2.1]
  · intro m V c hM hC a ha v baseRatio hv hbase omega hN
    have hvS : v ∈ Icc (1-es) (1+es) := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hzero : (0 : ℝ) ∈ Icc (-ds) ds := ⟨by linarith, hds.le⟩
    have hnear := hstateS c (hM0s.trans hM) (hC.trans_le hetaS) (fun _ : V => 0)
      (fun _ => hzero) v 0 baseRatio hvS hzero ⟨hbase.1, hbase.2.trans hepsS⟩
      omega (hN.trans_le hetaS)
    have hg := (hS a ha _ hnear).2.2
    simpa only [finiteRowScore_eq_sourceStateScore] using hg.le
  · intro hh' m hM nu _
    have hm : Mr ≤ m := by omega
    exact (hMr m hm nu).le
  · exact min_le_right _ _
  · exact min_le_right _ _
  · exact min_le_right _ _

theorem exists_uniform_finite_constants (d : ℕ) (hd : 1 ≤ d)
    (G : Schedule (d+1)) (h rho : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hrho : 0 < rho) (hrh : rho < h) :
    Nonempty (UniformFiniteConstants d G h rho) := by
  obtain ⟨C, _⟩ := exists_uniform_finite_constants_bounded d hd G h rho hh hh1 hrho hrh
    1 1 1 (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C⟩

end FCAppendix.Exclusive.Narrow.Existence
