import FCAppendix.Affine.Tail04.MovingActiveAtomRates
import FCAppendix.Affine.Tail04.SourceMovingScalarGuards

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceActiveErrorRates
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open OriginalValues SourceMomentRectangle SourceMenuPopulation SourceMovingScalarGuards
open MovingActiveAtomRates ActiveGainUniformModulus

def guardRate (P : ValueParameters) (ξ : ℝ) : ℝ :=
  min ((radius ξ (centerMoment P false))^2/200)
    ((radius ξ (centerMoment P true))^2/200)

def lowRate (P : ValueParameters) : ℝ := (lowMass P.theta)^2/2

def sourceError (P : ValueParameters) (ξ : ℝ) (N : ℕ) : ℝ :=
  10*Real.exp (-guardRate P ξ*(N:ℝ))+Real.exp (-lowRate P*(N:ℝ))

lemma guardRate_pos (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) : 0< guardRate P ξ := by
  unfold guardRate
  exact lt_min
    (div_pos (sq_pos_of_pos (SourcePartialPublicGuard.guard_radius_positive P hξ false)) (by norm_num))
    (div_pos (sq_pos_of_pos (SourcePartialPublicGuard.guard_radius_positive P hξ true)) (by norm_num))

lemma lowRate_pos (P : ValueParameters) : 0< lowRate P := by
  unfold lowRate
  exact div_pos (sq_pos_of_pos P.low_mass_pos) (by norm_num)

lemma sourceError_nonneg (P : ValueParameters) (ξ : ℝ) (N : ℕ) : 0≤ sourceError P ξ N := by
  unfold sourceError
  positivity

lemma regime_error_le (P : ValueParameters) (ξ : ℝ) (N : ℕ) (reg : Bool) :
    10*Real.exp (-(N:ℝ)*(radius ξ (centerMoment P reg))^2/200)+
      Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2)≤ sourceError P ξ N := by
  have hrate : guardRate P ξ≤(radius ξ (centerMoment P reg))^2/200 := by
    cases reg
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hx := Real.exp_le_exp.mpr
    (show -(N:ℝ)*(radius ξ (centerMoment P reg))^2/200≤-guardRate P ξ*(N:ℝ) by
      nlinarith [mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg N)])
  unfold sourceError lowRate
  calc
    _ ≤ 10*Real.exp (-guardRate P ξ*(N:ℝ))+
        Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2) :=
      add_le_add (mul_le_mul_of_nonneg_left hx (by norm_num : (0:ℝ)≤10)) le_rfl
    _ = _ := by
      congr 1
      congr 1
      ring

lemma sourceError_eq_twoFixed (P : ValueParameters) (ξ : ℝ) (N : ℕ) :
    sourceError P ξ N=twoFixedError (guardRate P ξ) (lowRate P) (N+2) := by
  simp only [sourceError,twoFixedError,Nat.add_sub_cancel]

def sourceMinFlag (P : ValueParameters) : ℝ := min (SourceNoisyData.eA P) (SourceNoisyData.eR P)

lemma sourceMinFlag_pos (P : ValueParameters) : 0< sourceMinFlag P :=
  lt_min (SourceNoisyData.eA_bounds P).1 (SourceNoisyData.eR_bounds P).1

theorem eventually_strict (P : ValueParameters) {ξ width k : ℝ}
    (hξ : 0< ξ) (hξh : ξ<1/2) (hw : 0< width) (hk : 0< k) :
    ∀ᶠ N : ℕ in atTop,∀ C : ℝ,
      C≤ Central.B ξ-(k/2)/cutoff N →
      2*(cutoff N+2*C+1)*sourceError P ξ (N-1)<
        populationCoefficient (N+1) ξ width (sourceMinFlag P) (Central.B ξ) C*
          (1/2-(75/4:ℝ)/Real.sqrt (N-1:ℕ)) := by
  have hF : 1< Central.B ξ := by unfold Central.B;linarith
  have hr := (tendsto_add_atTop_nat 1).eventually
    (exceptional_loss_lt_quarter_coefficient hξ hξh hw (sourceMinFlag_pos P)
      hF hk (guardRate_pos P hξ) (lowRate_pos P))
  have he := (tendsto_add_atTop_nat 1).eventually equal_private_eventually_small
  filter_upwards [eventually_ge_atTop (1:ℕ),hr,he] with N hN hrare heq
  intro C hC
  have hpop := populationCoefficient_moving_lower (m:=N+1) (by omega)
    hξ hξh.le hw (sourceMinFlag_pos P) hF hk hC
  have hconst := coefficientConstant_pos hξ hξh hw (sourceMinFlag_pos P) hF hk
  have ht : 0< movingThreshold (N+1) := movingThreshold_pos (N+1) (by omega)
  have hp : 0< populationCoefficient (N+1) ξ width (sourceMinFlag P) (Central.B ξ) C :=
    (div_pos hconst (by positivity)).trans_le hpop
  have hn : N+1-2=N-1 := by omega
  have herr := hrare C hC
  rw [hn] at heq
  rw [twoFixedError,hn] at herr
  change 2*(cutoff N+2*C+1)*sourceError P ξ (N-1)<
    populationCoefficient (N+1) ξ width (sourceMinFlag P) (Central.B ξ) C/4 at herr
  have hfactor : 1/4≤1/2-(75/4:ℝ)/Real.sqrt (N-1:ℕ) := by linarith
  exact herr.trans_le (by
    have hh := mul_le_mul_of_nonneg_left hfactor hp.le
    simpa only [div_eq_mul_inv,one_mul] using hh)

end FCAppendix.Affine.Tail04.SourceActiveErrorRates
