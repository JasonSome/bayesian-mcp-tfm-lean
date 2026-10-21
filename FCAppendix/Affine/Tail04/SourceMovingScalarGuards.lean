import FCAppendix.Affine.Tail04.SourcePartialNoisyError
import FCAppendix.Affine.Tail04.SourceNoisyData
import FCAppendix.Affine.Tail04.OriginalMovingLow
import FCAppendix.Affine.Tail04.MarketLimits

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceMovingScalarGuards
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open OriginalValues OriginalPopulation MenuError SourceMenuPopulation SourceMomentRectangle
open SourcePartialNoisyError

def cap (ξ k : ℝ) (N : ℕ) : ℝ := movingCap (Central.B ξ) k (N+1)
def cutoff (N : ℕ) : ℝ := movingThreshold (N+1)
def noise (ξ Up k : ℝ) (N : ℕ) : ℝ :=
  SourceNoisyData.budget ξ (Central.R ξ) Up (cap ξ k N) (Central.B ξ)
def commonPhysical (ξ Up k : ℝ) (N : ℕ) : ℝ :=
  cap ξ k N*(1+noise ξ Up k N)
def partialPhysical (ξ Up k : ℝ) (N : ℕ) : ℝ := Up*(1+noise ξ Up k N)
def bulkWidth (ξ Up u k : ℝ) (N : ℕ) : ℝ := (1+u)*(1+noise ξ Up k N)-1

theorem cutoff_tendsto : Tendsto cutoff atTop atTop :=
  movingThreshold_tendsto.comp (tendsto_add_atTop_nat 1)

theorem cap_tendsto (ξ k : ℝ) : Tendsto (cap ξ k) atTop (𝓝 (Central.B ξ)) := by
  have h : Tendsto (fun N => k/cutoff N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop cutoff_tendsto
  simpa only [cap,cutoff,movingCap,sub_zero] using! tendsto_const_nhds.sub h

theorem physical_flag_gap (ξ Up k : ℝ) (N : ℕ) (hU : 0< cap ξ k N) :
    k/(2*cutoff N)≤ Central.B ξ-commonPhysical ξ Up k N := by
  have hbudget : noise ξ Up k N≤(Central.B ξ-cap ξ k N)/(2*cap ξ k N) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb := (le_div_iff₀ (by positivity : 0<2*cap ξ k N)).mp hbudget
  have hgap : Central.B ξ-cap ξ k N=k/cutoff N := by
    unfold cap cutoff movingCap
    ring
  have hh : k/(2*cutoff N)=(Central.B ξ-cap ξ k N)/2 := by
    rw [hgap]
    ring
  rw [hh]
  unfold commonPhysical
  nlinarith

lemma nominal_receipt_gap {ξ : ℝ} (hξ : 0< ξ) :
    (1-ξ)*Central.B ξ< Central.R ξ := by
  unfold Central.B Central.R
  nlinarith [sq_nonneg ξ]

theorem noise_tendsto {ξ Up : ℝ} (hξ : 0< ξ) (hξh : ξ<1/2)
    (hUp0 : 0< Up) (hUp1 : Up<1) (k : ℝ) :
    Tendsto (noise ξ Up k) atTop (𝓝 0) := by
  have hB : 0< Central.B ξ := by unfold Central.B;linarith
  have hκ : 0<1-ξ := by linarith
  have hgap := nominal_receipt_gap hξ
  have hU := cap_tendsto ξ k
  have hden : 2*((1-ξ)*Central.B ξ)≠0 := by positivity
  have hden' : 2*Central.B ξ≠0 := by positivity
  have hg := ((tendsto_const_nhds (x:=Central.R ξ)).sub (hU.const_mul (1-ξ))).div
    ((hU.const_mul (1-ξ)).const_mul 2) hden
  have hb := ((tendsto_const_nhds (x:=Central.B ξ)).sub hU).div (hU.const_mul 2) hden'
  have hp : 0≤(1-Up)/(2*Up) := div_nonneg (by linarith) (by positivity)
  have hgp : 0≤(Central.R ξ-(1-ξ)*Central.B ξ)/(2*((1-ξ)*Central.B ξ)) :=
    div_nonneg (sub_nonneg.mpr hgap.le) (by positivity)
  have hh := (tendsto_const_nhds (x:=(1/2:ℝ))).min
    ((tendsto_const_nhds (x:=(1-Up)/(2*Up))).min (hg.min hb))
  simpa only [noise,SourceNoisyData.budget,sub_self,zero_div,
    min_eq_right hgp,min_eq_right hp,min_eq_right (by norm_num : (0:ℝ)≤1/2)] using! hh

theorem physical_tendsto {ξ Up : ℝ} (hξ : 0< ξ) (hξh : ξ<1/2)
    (hUp0 : 0< Up) (hUp1 : Up<1) (u k : ℝ) :
    Tendsto (commonPhysical ξ Up k) atTop (𝓝 (Central.B ξ)) ∧
    Tendsto (partialPhysical ξ Up k) atTop (𝓝 Up) ∧
    Tendsto (bulkWidth ξ Up u k) atTop (𝓝 u) := by
  have hn := noise_tendsto hξ hξh hUp0 hUp1 k
  have h1 := (tendsto_const_nhds (x:=(1:ℝ))).add hn
  refine ⟨?_,?_,?_⟩
  · simpa only [commonPhysical,add_zero,mul_one] using! (cap_tendsto ξ k).mul h1
  · simpa only [partialPhysical,add_zero,mul_one] using! h1.const_mul Up
  · simpa only [bulkWidth,add_zero,mul_one,add_sub_cancel_left] using! (h1.const_mul (1+u)).sub_const 1

theorem original_upper_mass_tendsto (P : ValueParameters) :
    Tendsto (fun N => upperMass P (cutoff N)) atTop (𝓝 0) := by
  apply ((OriginalMovingLow.raw_mass_tendsto P).comp (tendsto_add_atTop_nat 1)).congr'
  filter_upwards [cutoff_tendsto.eventually_gt_atTop P.M] with N hM
  dsimp only [Function.comp_apply,upperMass,cutoff,movingPrivateMass]
  rw [powerTail_ten P.M (movingThreshold (N+1)) P.M_pos (P.M_pos.trans hM)]

theorem original_scaled_private_tendsto (P : ValueParameters) :
    Tendsto (fun N : ℕ => (N+1:ℝ)*
      (upperMass P (cutoff N)/(partialMass+upperMass P (cutoff N)))) atTop (𝓝 0) := by
  have hh := (private_share_scaled_tendsto partialMass (activeMass P.theta) P.zeta P.M
    (by norm_num [partialMass]) P.active_mass_pos.le P.zeta_pos.le).comp (tendsto_add_atTop_nat 1)
  apply hh.congr'
  filter_upwards [cutoff_tendsto.eventually_gt_atTop P.M] with N hM
  simp only [Function.comp_apply,movingPrivateShare,movingPrivateMass,upperMass,cutoff,
    powerTail_ten P.M (movingThreshold (N+1)) P.M_pos (P.M_pos.trans hM),Nat.cast_add,Nat.cast_one]

theorem eventually_two_fixed_room (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) :
    ∀ᶠ N : ℕ in atTop,∀ reg,32/((N-1:ℕ):ℝ)≤ radius ξ (centerMoment P reg) := by
  have hn : Tendsto (fun N : ℕ=>((N-1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
  have he : Tendsto (fun N : ℕ=>(32:ℝ)/((N-1:ℕ):ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have h0 := he.eventually (gt_mem_nhds (SourcePartialPublicGuard.guard_radius_positive P hξ false))
  have h1 := he.eventually (gt_mem_nhds (SourcePartialPublicGuard.guard_radius_positive P hξ true))
  filter_upwards [h0,h1] with N hN0 hN1
  intro reg
  cases reg
  · exact hN0.le
  · exact hN1.le

structure Range (P : ValueParameters) (ξ Up u k : ℝ) (N : ℕ) : Prop where
  rivals_positive : 0< N
  two_fixed_positive : 0< N-1
  capacity_positive : 0< iidCapacity (99/200) N
  capacity_less_population : iidCapacity (99/200) N< N+1
  cutoff_gt_M : P.M< cutoff N
  base_contains_bulk : 1+u≤ cap ξ k N
  base_below_nominal : cap ξ k N< Central.B ξ
  flag_endpoint_gap : k/(2*cutoff N)≤ Central.B ξ-commonPhysical ξ Up k N
  budget_positive : 0< noise ξ Up k N
  budget_le_one : noise ξ Up k N≤1
  partial_below_value : partialPhysical ξ Up k N<2-P.w
  bulk_below_nominal : 1+bulkWidth ξ Up u k N< Central.B ξ
  partial_guard : partialPhysical ξ Up k N≤ Central.R ξ+ξ/1000
  moment_guard : relativeError P.zeta (bulkWidth ξ Up u k N) (Central.B ξ)≤ ξ/1000
  upper_mass_guard : upperMass P (cutoff N)≤ Central.mixedR (P.theta^2)/1000
  room : ∀ reg,8/(N:ℝ)≤ radius ξ (centerMoment P reg)
  two_fixed_room : ∀ reg,32/((N-1:ℕ):ℝ)≤ radius ξ (centerMoment P reg)
  owner_receipt_guard : (1-ξ)*commonPhysical ξ Up k N+ξ*commonPhysical ξ Up k N*
    ((N+1:ℝ)*(upperMass P (cutoff N)/(partialMass+upperMass P (cutoff N))))≤ Central.R ξ
  partial_downward_margin :
    2*(valueBound P+1)*SourcePartialPublicGuard.badBound P ξ N<
      ((Up-Central.R ξ)/2)*(1-P.theta)

theorem eventually_range (P : ValueParameters) {ξ Up u k : ℝ}
    (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u) (hk : 0< k)
    (hRUp : Central.R ξ< Up) (hUp : Up<1) (hvalue : Up<2-P.w)
    (huB : 1+u< Central.B ξ) (hUpMargin : Up< Central.R ξ+ξ/1000)
    (hsmall : relativeError P.zeta u (Central.B ξ)< ξ/1000) :
    ∀ᶠ N in atTop,Range P ξ Up u k N := by
  have hR : 0< Central.R ξ := by unfold Central.R;nlinarith
  have hUp0 : 0< Up := hR.trans hRUp
  have hp := physical_tendsto hξ hξh hUp0 hUp u k
  have herr : Tendsto (fun N => relativeError P.zeta (bulkWidth ξ Up u k N) (Central.B ξ))
      atTop (𝓝 (relativeError P.zeta u (Central.B ξ))) :=
    tendsto_const_nhds.add (hp.2.2.mul_const (1+2/(Central.B ξ-1)))
  have hUpperPos : 0< Central.mixedR (P.theta^2)/1000 := by
    unfold Central.mixedR Central.h
    positivity
  have hown := ((hp.1.const_mul (1-ξ)).add
    ((hp.1.const_mul ξ).mul (original_scaled_private_tendsto P)))
  have hown' : Tendsto (fun N => (1-ξ)*commonPhysical ξ Up k N+
      ξ*commonPhysical ξ Up k N*((N+1:ℝ)*
        (upperMass P (cutoff N)/(partialMass+upperMass P (cutoff N)))))
      atTop (𝓝 ((1-ξ)*Central.B ξ)) := by simpa only [mul_zero,add_zero] using hown
  have hcapPos : ∀ᶠ N in atTop,0< iidCapacity (99/200) N := by
    have h := (tendsto_add_atTop_nat 1).eventually Markets.eventually_capacity_positive
    simpa only [iidCapacity,Markets.capacity,Nat.cast_add,Nat.cast_one] using h
  have hmargin := SourcePartialNoisyError.eventually_downward_margin P ξ hξ
    ((Up-Central.R ξ)/2) (by linarith)
  filter_upwards [eventually_gt_atTop (1:ℕ),hcapPos,
    cutoff_tendsto.eventually_gt_atTop P.M,
    (cap_tendsto ξ k).eventually (lt_mem_nhds huB),
    hp.2.1.eventually (gt_mem_nhds hvalue),
    (hp.2.2.const_add 1).eventually (gt_mem_nhds huB),
    hp.2.1.eventually (gt_mem_nhds hUpMargin),
    herr.eventually (gt_mem_nhds hsmall),
    (original_upper_mass_tendsto P).eventually (gt_mem_nhds hUpperPos),
    SourcePartialPublicGuard.eventually_room P hξ,
    eventually_two_fixed_room P hξ,
    hown'.eventually (gt_mem_nhds (nominal_receipt_gap hξ)),hmargin]
      with N hN hc hM hU hval hbulk hpart herr hmass hroom hroom2 howner hmar
  have hUB : cap ξ k N< Central.B ξ := by
    have ht := movingThreshold_pos (N+1) (by omega)
    change Central.B ξ-k/movingThreshold (N+1)< Central.B ξ
    exact sub_lt_self _ (div_pos hk ht)
  have hb := SourceNoisyData.budget_bounds (by linarith : ξ<1) hUp0 hUp
    (show 0< cap ξ k N by linarith)
    (SourceNoisyData.source_receipt_gap hξ hξh hUB) hUB
  have hcm : iidCapacity (99/200) N< N+1 := by
    have hn : (0:ℝ)< N+1 := by positivity
    have hf : (iidCapacity (99/200) N:ℝ)≤(99/200:ℝ)*((N:ℝ)+1) :=
      Nat.floor_le (by positivity)
    have hh : (iidCapacity (99/200) N:ℝ)<(N+1:ℕ) := by
      push_cast
      nlinarith
    exact_mod_cast hh
  exact ⟨by omega,by omega,hc,hcm,hM,hU.le,hUB,
    physical_flag_gap ξ Up k N (by linarith),hb.1,hb.2.1,hval,hbulk,hpart.le,herr.le,
    hmass.le,hroom,hroom2,howner.le,hmar⟩

end FCAppendix.Affine.Tail04.SourceMovingScalarGuards
