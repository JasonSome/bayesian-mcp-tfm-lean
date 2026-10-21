import FCAppendix.Affine.Tail04.ActiveGainUniformModulus
import FCAppendix.Affine.Tail04.SourceNoisyData
import FCAppendix.Affine.Tail04.MovingBoundary

noncomputable section
namespace FCAppendix.Affine.Tail04.MovingActiveAtomRates
open Set Filter Topology Real
open ActiveGainUniformModulus ActualGuardMarginals

lemma budget_half_gap {ξ R Up U F : ℝ} (hU : 0< U) :
    U*(1+SourceNoisyData.budget ξ R Up U F)≤(F+U)/2 := by
  have he : SourceNoisyData.budget ξ R Up U F≤(F-U)/(2*U) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hh := (le_div_iff₀ (show 0<2*U from by positivity)).mp he
  nlinarith

theorem moving_physical_cap_room {ξ R Up F k : ℝ} {m : ℕ}
    (hU : 0< movingCap F k m) :
    movingCap F k m*(1+SourceNoisyData.budget ξ R Up (movingCap F k m) F)≤
      F-(k/2)/movingThreshold m := by
  have h := budget_half_gap (ξ:=ξ) (R:=R) (Up:=Up) (F:=F) hU
  unfold movingCap at h ⊢
  calc
    _ ≤ (F+(F-k/movingThreshold m))/2 := h
    _ = _ := by ring

def coefficientConstant (ξ width e0 F k : ℝ) : ℝ :=
  (1-2*ξ)*(sourceQmin ξ width)^2*e0^2*(k/(2*(F-1)))^4/2

lemma coefficientConstant_pos {ξ width e0 F k : ℝ}
    (hξ : 0< ξ) (hξh : ξ<1/2) (hw : 0< width) (he : 0< e0)
    (hF : 1< F) (hk : 0< k) : 0< coefficientConstant ξ width e0 F k := by
  have hq := sourceQmin_pos hξ hw
  have hη : 0<1-2*ξ := by linarith
  unfold coefficientConstant
  positivity

theorem populationCoefficient_moving_lower {ξ width e0 F k C : ℝ} {m : ℕ}
    (hm : 1≤ m) (_hξ : 0< ξ) (hξh : ξ≤1/2) (_hw : 0< width)
    (he : 0< e0) (hF : 1< F) (hk : 0< k)
    (hC : C≤ F-(k/2)/movingThreshold m) :
    coefficientConstant ξ width e0 F k/((m:ℝ)^2*movingThreshold m^4)≤
      populationCoefficient m ξ width e0 F C := by
  have hm0 : (0:ℝ)< m := by exact_mod_cast (show 0< m by omega)
  have hm1 : (1:ℝ)≤ m := by exact_mod_cast hm
  have ht := movingThreshold_pos m (by omega)
  have hη : 0≤1-2*ξ := by linarith
  have hf := mixed_flag_lower_at_cap e0 (F-1) F (k/2) (movingThreshold m) C
    he (by linarith) (by positivity) ht hC
  let a := e0*(k/(2*(F-1)))^2/movingThreshold m^2
  have ha0 : 0≤ a := by dsimp [a];positivity
  have ha : a≤ flagFloor e0 F C := by
    convert! hf using 1
    dsimp [a,flagFloor]
    field_simp [ht.ne',ne_of_gt (show 0< F-1 from by linarith)]
  have hsq : a^2≤(flagFloor e0 F C)^2 := by nlinarith
  have hg0 : 0≤(1-2*ξ)*(sourceQmin ξ width)^2 := by positivity
  have hnum := mul_le_mul_of_nonneg_left hsq hg0
  have hd : (m:ℝ)*((m:ℝ)+1)≤2*(m:ℝ)^2 := by nlinarith
  calc
    _ = ((1-2*ξ)*(sourceQmin ξ width)^2*a^2)/(2*(m:ℝ)^2) := by
      dsimp [coefficientConstant,a]
      field_simp
    _ ≤ ((1-2*ξ)*(sourceQmin ξ width)^2*(flagFloor e0 F C)^2)/(2*(m:ℝ)^2) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ ((1-2*ξ)*(sourceQmin ξ width)^2*(flagFloor e0 F C)^2)/
        ((m:ℝ)*((m:ℝ)+1)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ = _ := rfl

def twoFixedError (guardRate lowRate : ℝ) (m : ℕ) : ℝ :=
  10*Real.exp (-guardRate*(m-2:ℕ))+Real.exp (-lowRate*(m-2:ℕ))

lemma twoFixedError_nonneg (guardRate lowRate : ℝ) (m : ℕ) :
    0≤ twoFixedError guardRate lowRate m := by unfold twoFixedError;positivity

def exponentialConstant (guardRate lowRate : ℝ) : ℝ :=
  10*Real.exp (2*guardRate)+Real.exp (2*lowRate)

lemma exponentialConstant_pos (guardRate lowRate : ℝ) :
    0< exponentialConstant guardRate lowRate := by unfold exponentialConstant;positivity

theorem twoFixedError_le_one_exponential {guardRate lowRate : ℝ}
    (m : ℕ) (hm : 2≤ m) :
    twoFixedError guardRate lowRate m≤
      exponentialConstant guardRate lowRate*
        Real.exp (-(min guardRate lowRate)*(m:ℝ)) := by
  have hm0 : (0:ℝ)≤ m := Nat.cast_nonneg m
  have hg : Real.exp (-guardRate*(m:ℝ))≤ Real.exp (-(min guardRate lowRate)*(m:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left guardRate lowRate])
  have hl : Real.exp (-lowRate*(m:ℝ))≤ Real.exp (-(min guardRate lowRate)*(m:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right guardRate lowRate])
  have he (q : ℝ) : Real.exp (-q*(m-2:ℕ))=Real.exp (2*q)*Real.exp (-q*(m:ℝ)) := by
    rw [Nat.cast_sub hm]
    norm_num only [Nat.cast_ofNat]
    rw [show -q*((m:ℝ)-2)=2*q+(-q*(m:ℝ)) by ring,Real.exp_add]
  rw [twoFixedError,he,he]
  have h1 := mul_le_mul_of_nonneg_left hg (show 0≤10*Real.exp (2*guardRate) from by positivity)
  have h2 := mul_le_mul_of_nonneg_left hl (show 0≤ Real.exp (2*lowRate) from by positivity)
  unfold exponentialConstant
  nlinarith only [h1,h2]

theorem exceptional_loss_lt_quarter_coefficient {ξ width e0 F k guardRate lowRate : ℝ}
    (hξ : 0< ξ) (hξh : ξ<1/2) (hw : 0< width)
    (he : 0< e0) (hF : 1< F) (hk : 0< k)
    (hg : 0< guardRate) (hl : 0< lowRate) :
    ∀ᶠ m : ℕ in atTop,∀ C : ℝ,C≤ F-(k/2)/movingThreshold m →
      2*(movingThreshold m+2*C+1)*twoFixedError guardRate lowRate m<
        populationCoefficient m ξ width e0 F C/4 := by
  have hG := coefficientConstant_pos hξ hξh hw he hF hk
  have hExp := exponentialConstant_pos guardRate lowRate
  have hrate : 0< min guardRate lowRate := lt_min hg hl
  have hr := rare_jump_eventually_smaller
    (2*exponentialConstant guardRate lowRate) (F+1) (min guardRate lowRate)
    (coefficientConstant ξ width e0 F k/4)
    (by positivity) (by linarith) hrate (by positivity)
  filter_upwards [eventually_ge_atTop (2:ℕ),hr] with m hm hrare
  intro C hC
  have hm1 : (1:ℝ)≤ m := by exact_mod_cast (show 1≤ m by omega)
  have ht := movingThreshold_pos m (by omega)
  have hCF : C≤ F := by
    have : 0≤(k/2)/movingThreshold m := by positivity
    linarith
  have herr := twoFixedError_le_one_exponential (guardRate:=guardRate) (lowRate:=lowRate) m hm
  have hc := populationCoefficient_moving_lower (by omega : 1≤ m) hξ hξh.le hw he hF hk hC
  have hcomparison :
      2*(movingThreshold m+2*C+1)*twoFixedError guardRate lowRate m≤
        (2*exponentialConstant guardRate lowRate)*(movingThreshold m+2*(F+1))*(m:ℝ)*
          Real.exp (-(min guardRate lowRate)*(m:ℝ)) := by
    by_cases hneg : movingThreshold m+2*C+1<0
    · have hnonpos := mul_nonpos_of_nonpos_of_nonneg
        (by linarith : 2*(movingThreshold m+2*C+1)≤0)
        (twoFixedError_nonneg guardRate lowRate m)
      exact hnonpos.trans (by positivity)
    · have hnonneg : 0≤ movingThreshold m+2*C+1 := le_of_not_gt hneg
      calc
        _ ≤ 2*(movingThreshold m+2*C+1)*
            (exponentialConstant guardRate lowRate*Real.exp (-(min guardRate lowRate)*(m:ℝ))) :=
          mul_le_mul_of_nonneg_left herr (by positivity)
        _ ≤ 2*(movingThreshold m+2*(F+1))*
            (exponentialConstant guardRate lowRate*Real.exp (-(min guardRate lowRate)*(m:ℝ))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
        _ ≤ (2*exponentialConstant guardRate lowRate)*(movingThreshold m+2*(F+1))*(m:ℝ)*
            Real.exp (-(min guardRate lowRate)*(m:ℝ)) := by
          have hh := mul_le_mul_of_nonneg_left hm1
            (show 0≤2*(movingThreshold m+2*(F+1))*
              (exponentialConstant guardRate lowRate*Real.exp (-(min guardRate lowRate)*(m:ℝ))) from by positivity)
          nlinarith only [hh]
  apply (hcomparison.trans_lt hrare).trans_le
  have hh := div_le_div_of_nonneg_right hc (by norm_num : (0:ℝ)≤4)
  convert! hh using 1; ring

theorem equal_private_eventually_small :
    ∀ᶠ m : ℕ in atTop,(75/4:ℝ)/Real.sqrt (m-2:ℕ)≤1/8 := by
  filter_upwards [eventually_ge_atTop (22502:ℕ)] with m hm
  have hn : 22500≤ m-2 := by omega
  have hnr : (22500:ℝ)≤(m-2:ℕ) := by exact_mod_cast hn
  have hs : (150:ℝ)≤ Real.sqrt (m-2:ℕ) :=
    (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr (by nlinarith only [hnr])
  apply (div_le_iff₀ (show 0< Real.sqrt (m-2:ℕ) from by linarith)).mpr
  nlinarith

end FCAppendix.Affine.Tail04.MovingActiveAtomRates
