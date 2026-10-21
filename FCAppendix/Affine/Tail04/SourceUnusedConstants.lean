import FCAppendix.Affine.Tail04.UnusedPublicPrices
import FCAppendix.Affine.Tail04.SourceMovingMenuRates
import FCAppendix.Affine.Tail04.SourceMenuPopulation

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceUnusedConstants
open Set Filter Topology
open OriginalValues SourceMenuPopulation WeightedFlagBound

def least (P : ValueParameters) : ℝ:=min (baseFlag P false) (baseFlag P true)
def greatest (P : ValueParameters) : ℝ:=max (baseFlag P false) (baseFlag P true)
def epsilon (P : ValueParameters) (B u : ℝ) : ℝ:=
  min (least P*((B-1-u)/(B-1))^2) (1-greatest P)/4

theorem least_pos (P : ValueParameters) : 0< least P :=
  lt_min (baseFlag_bounds P false).1 (baseFlag_bounds P true).1

theorem greatest_lt_one (P : ValueParameters) : greatest P<1 :=
  max_lt (baseFlag_bounds P false).2 (baseFlag_bounds P true).2

theorem epsilon_bounds (P : ValueParameters) {B u : ℝ} (hB : 1< B) (hu : 1+u< B) :
    0< epsilon P B u ∧ epsilon P B u<1/2 := by
  have hd : 0< B-1 := by linarith
  have hn : 0< B-1-u := by linarith
  have hq : 0<(B-1-u)/(B-1) := div_pos hn hd
  have hm : 0< min (least P*((B-1-u)/(B-1))^2) (1-greatest P) :=
    lt_min (mul_pos (least_pos P) (sq_pos_of_pos hq)) (by linarith [greatest_lt_one P])
  have hg0 : 0< greatest P := (baseFlag_bounds P false).1.trans_le (le_max_left _ _)
  have he := min_le_right (least P*((B-1-u)/(B-1))^2) (1-greatest P)
  unfold epsilon
  constructor <;> linarith

theorem flag_bounds (P : ValueParameters) {B u : ℝ} (hB : 1< B) (hu : 1+u< B)
    {ι : Type*} (b : ι→ℝ) (reg : Bool) (j : ι) (hb : b j∈Icc (1:ℝ) (1+u)) :
    epsilon P B u≤ sourceFlagProb (baseFlag P reg) B b j ∧
      sourceFlagProb (baseFlag P reg) B b j≤1-epsilon P B u := by
  have hl : least P≤ baseFlag P reg := by
    cases reg
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hg : baseFlag P reg≤ greatest P := by
    cases reg
    · exact le_max_left _ _
    · exact le_max_right _ _
  have he := epsilon_bounds P hB hu
  have hmin0 : 0≤ min (least P*((B-1-u)/(B-1))^2) (1-greatest P) := by
    have hp := he.1
    unfold epsilon at hp
    linarith
  have heL : epsilon P B u≤ baseFlag P reg*((B-1-u)/(B-1))^2 := by
    have hh:=mul_le_mul_of_nonneg_right hl (sq_nonneg ((B-1-u)/(B-1)))
    have hmin:=min_le_left (least P*((B-1-u)/(B-1))^2) (1-greatest P)
    unfold epsilon
    linarith
  have heU : baseFlag P reg≤1-epsilon P B u := by
    have hmin:=min_le_right (least P*((B-1-u)/(B-1))^2) (1-greatest P)
    unfold epsilon
    linarith
  rw [sourceFlagProb_eq (baseFlag_bounds P reg).1.le (baseFlag_bounds P reg).2.le hB b j
    ⟨hb.1,hb.2.trans hu.le⟩]
  exact bulk_flag_bounds (baseFlag_bounds P reg).1.le hB (by linarith) hb heL heU

def cover (ξ : ℝ) : ℕ:=5+Nat.ceil (8/ξ)

theorem cover_bounds {ξ : ℝ} (hξ : 0< ξ) :
    ξ<(5:ℝ)*(ξ/4) ∧ (5:ℝ)*(ξ/4)+2≤(cover ξ:ℝ)*(ξ/4) := by
  have hh : 8/ξ≤(Nat.ceil (8/ξ):ℝ) := Nat.le_ceil _
  have hh' := mul_le_mul_of_nonneg_right hh (div_nonneg hξ.le (by norm_num : (0:ℝ)≤4))
  have he : (8/ξ)*(ξ/4)=2 := by field_simp;ring
  rw [he] at hh'
  simp only [cover,Nat.cast_add,Nat.cast_ofNat]
  constructor <;> nlinarith

def crossingCoefficient (P : ValueParameters) (B u ξ : ℝ) : ℝ:=
  (2/epsilon P B u+(cover ξ:ℝ)*Real.sqrt (2/epsilon P B u))/
    Real.sqrt (P.bulkWeight/2)

theorem crossingCoefficient_nonneg (P : ValueParameters) {B u ξ : ℝ}
    (hB : 1< B) (hu : 1+u< B) : 0≤ crossingCoefficient P B u ξ := by
  have he:=(epsilon_bounds P hB hu).1
  unfold crossingCoefficient
  positivity

theorem crossing_rate (P : ValueParameters) {B u ξ : ℝ}
    (hB : 1< B) (hu : 1+u< B) (N : ℕ) (hbulk : 1≤ P.bulkWeight*(N:ℝ)/2) :
    2/(epsilon P B u*(P.bulkWeight*N/2))+
      (cover ξ:ℝ)*Real.sqrt (2/(epsilon P B u*(P.bulkWeight*N/2)+1))≤
        crossingCoefficient P B u ξ/Real.sqrt N := by
  have he:=weighted_error_sqrt_rate (epsilon_bounds P hB hu).1 hbulk (cover ξ)
  have hs : Real.sqrt (P.bulkWeight*(N:ℝ)/2)=
      Real.sqrt (P.bulkWeight/2)*Real.sqrt N := by
    rw [show P.bulkWeight*(N:ℝ)/2=(P.bulkWeight/2)*(N:ℝ) by ring,
      Real.sqrt_mul (half_pos P.bulkWeight_pos).le]
  rw [hs] at he
  simpa only [crossingCoefficient,div_div] using he

def regimeCoefficient (P : ValueParameters) (ξ : ℝ) (reg : Bool) : ℝ:=
  160/(ξ*centerMoment P reg)+6/SourceMomentRectangle.radius ξ (centerMoment P reg)

def coefficient (P : ValueParameters) (ξ : ℝ) : ℝ:=
  regimeCoefficient P ξ false+regimeCoefficient P ξ true

def integerCoefficient (P : ValueParameters) : ℝ:=
  32/centerMoment P false+32/centerMoment P true

theorem regimeCoefficient_nonneg (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) (reg : Bool) :
    0≤ regimeCoefficient P ξ reg := by
  have hc:=centerMoment_pos P reg
  unfold regimeCoefficient SourceMomentRectangle.radius SourceMomentRectangle.γ
  positivity

def rate (P : ValueParameters) (ξ u : ℝ) (N : ℕ) : ℝ:=
  (5*coefficient P ξ+2*crossingCoefficient P (Central.B ξ) u ξ)/Real.sqrt N+
    (5*coefficient P ξ+integerCoefficient P)/(N:ℝ)+
    6*Real.exp (-(N:ℝ)*P.bulkWeight^2/2)+
    2*Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2)

theorem rate_nonneg (P : ValueParameters) {ξ u : ℝ} (hξ : 0< ξ)
    (huB : 1+u< Central.B ξ) (N : ℕ) : 0≤ rate P ξ u N := by
  have hB : 1< Central.B ξ := by unfold Central.B;linarith
  have hK0:=regimeCoefficient_nonneg P hξ false
  have hK1:=regimeCoefficient_nonneg P hξ true
  have hC:=crossingCoefficient_nonneg (ξ:=ξ) P hB huB
  have hc0:=centerMoment_pos P false
  have hc1:=centerMoment_pos P true
  unfold rate coefficient integerCoefficient
  positivity

theorem scaled_rate_tendsto (P : ValueParameters) (ξ u : ℝ) :
    Tendsto (fun N=> SourceMovingScalarGuards.cutoff N^2*rate P ξ u N) atTop (𝓝 0) := by
  have h1:=SourceMovingMenuRates.cutoff_square_over_sqrt
  have h2:=SourceMovingMenuRates.cutoff_square_over_rivals
  have h3:=SourceMovingMenuRates.cutoff_square_exponential
    (show 0< P.bulkWeight^2/2 by have hb:=P.bulkWeight_pos;positivity)
  have h4:=SourceMovingMenuRates.cutoff_square_exponential
    (show 0<(lowMass P.theta)^2/2 by have hh:=P.low_mass_pos;positivity)
  have hh:=(((h1.const_mul (5*coefficient P ξ+2*crossingCoefficient P (Central.B ξ) u ξ)).add
    (h2.const_mul (5*coefficient P ξ+integerCoefficient P))).add (h3.const_mul 6)).add (h4.const_mul 2)
  convert! hh using 1
  · funext N
    unfold rate
    rw [show -(N:ℝ)*P.bulkWeight^2/2=-(P.bulkWeight^2/2)*(N:ℝ) by ring,
      show -(N:ℝ)*(lowMass P.theta)^2/2=-((lowMass P.theta)^2/2)*(N:ℝ) by ring]
    ring
  · simp

theorem eventually_budgets (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) :
    ∀ᶠN : ℕ in atTop,
      (∀reg,4*ξ/((N:ℝ)*centerMoment P reg)≤ SourceMomentRectangle.γ ξ) ∧
      1≤ P.bulkWeight*(N:ℝ)/2 := by
  have hg : 0< SourceMomentRectangle.γ ξ := by unfold SourceMomentRectangle.γ;positivity
  have he (reg : Bool) : ∀ᶠN : ℕ in atTop,
      4*ξ/((N:ℝ)*centerMoment P reg)≤ SourceMomentRectangle.γ ξ := by
    have hh : Tendsto (fun N : ℕ=>(4*ξ/centerMoment P reg)/(N:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hh':=hh.eventually (gt_mem_nhds hg)
    filter_upwards [hh'] with N hN
    have heq : 4*ξ/((N:ℝ)*centerMoment P reg)=(4*ξ/centerMoment P reg)/(N:ℝ) := by ring
    rw [heq]
    exact hN.le
  have hb : ∀ᶠN : ℕ in atTop,1≤ P.bulkWeight*(N:ℝ)/2 := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (2/P.bulkWeight))] with N hN
    have hN' : (Nat.ceil (2/P.bulkWeight):ℝ)≤ N := by exact_mod_cast hN
    have hmin : 2/P.bulkWeight≤(N:ℝ) := (Nat.le_ceil _).trans hN'
    have hh:=mul_le_mul_of_nonneg_left hmin P.bulkWeight_pos.le
    have heq : P.bulkWeight*(2/P.bulkWeight)=2 := by field_simp [P.bulkWeight_pos.ne']
    rw [heq] at hh
    linarith
  filter_upwards [he false,he true,hb] with N h0 h1 hb
  exact ⟨fun reg=> by cases reg <;> assumption,hb⟩

end FCAppendix.Affine.Tail04.SourceUnusedConstants
