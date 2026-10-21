import FCAppendix.Affine.Tail04.ZeroSourceCommonMenuError
import FCAppendix.Affine.Tail04.SourceMultiplierRectangle

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroSourceMultiplierRectangle
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open FiniteTailNoisyGame SourceTailNoisyFixedPoint NativeZeroNoiseSource
open OriginalActiveCompression ZeroCommonMenuCount
open MenuError SourceMenuPopulation SourceMenuError SourceMomentRectangle ZeroSourceCommonMoments
open SourceMultiplierRectangle

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (hfloor : ∀ v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
  (hF : D.F=Central.B D.ξ) (hflags : ∀ reg,D.e0 reg=baseFlag P reg)
  (huB : 1+D.u< Central.B D.ξ)

local notation "Ds" => installOriginal D P t ht
local notation "E" => regions D P hdR H hUH
local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "μ" => userLaw Γ
local notation "tag" => Observable.Regions.coarseTag E
local notation "decode" => ZeroNativeFiberProduct.commonProjection D P hdR H hUH
local notation "M" => mixedMean Ds tag decode μ
local notation "W" => reciprocalMean Ds tag decode μ
local notation "lam" => ZeroSourceCommonMenuError.lambda D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare

include t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags huB in
theorem actual_moment_error (reg : Bool) :
    |M reg-centerMoment P reg|≤ centerMoment P reg*
        relativeError P.zeta (D.u) (Central.B D.ξ) ∧
    |W reg-centerMoment P reg|≤ centerMoment P reg*
        relativeError P.zeta (D.u) (Central.B D.ξ) := by
  have he := baseFlag_bounds P reg
  have hm := SourceNativeMoments.native_two_moment_error Γ P E rfl t ht
    (D.u) (baseFlag P reg) (Central.B D.ξ)
    D.hu D.huU huB
    (by change D.U≤Central.B D.ξ; simpa only [←hF] using (base_active_le_physical D).trans D.hUF) he.1 he.2.le πL
    («partial» D P t ht π) (π 0)
    (π 1) upperBid hupperBid hfloor
    (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)
  rw [centerMoment_eq] at hm
  rw [mixed_mean D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags,
    reciprocal_mean D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags]
  simpa only [mixedMoment,reciprocalMoment,nativeFlag,nativeBid,
    SourceNativeMoments.mixedWeight_eq_marked,originalReciprocalWeight_eq_marked] using! hm

include t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags huB in
theorem actual_mem {ρ : ℝ} {Λ : Set (ℝ×ℝ)}
    (hrect : MomentInvariant P D.ξ ρ Λ)
    (hρ : relativeError P.zeta (D.u) (Central.B D.ξ)≤ ρ) :
    (lam false,lam true)∈Λ := by
  apply hrect M W
  · intro reg
    exact (actual_moment_error D P t ht πL π upperBid hupperBid hdR H hUH
      hfloor N hrare hF hflags huB reg).1.trans
        (mul_le_mul_of_nonneg_left hρ (centerMoment_pos P reg).le)
  · intro reg
    exact (actual_moment_error D P t ht πL π upperBid hupperBid hdR H hUH
      hfloor N hrare hF hflags huB reg).2.trans
        (mul_le_mul_of_nonneg_left hρ (centerMoment_pos P reg).le)

include ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags huB in
theorem actual_nominal_bounds (hξh : D.ξ<1/2) (hR : D.R=Central.R D.ξ)
    (hRp : D.Up≤ Central.R D.ξ+D.ξ/1000)
    (hsmall : relativeError P.zeta (D.u) (Central.B D.ξ)≤ D.ξ/1000)
    (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000) (reg : Bool) :
    (1-D.ξ)*Central.B D.ξ≤ lam reg ∧ lam reg≤1 := by
  have hj := game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare
  have G := native_nominal_guard_interior Γ P E rfl t ht (D.u)
    D.hu D.huU πL («partial» D P t ht π)
    (π 0) (π 1) upperBid hupperBid hfloor hj
    D.ξ D.hξ hξh huB (by change D.U≤Central.B D.ξ; simpa only [←hF] using (base_active_le_physical D).trans D.hUF) hR hRp hsmall hmSmall reg
  have hg := G.mean_margins D.hξ.le
    (integral_nonneg fun x => (indicator_bounds (categoryFlag E 2) x).1)
  have ha := SourceNativeMoments.native_active_mean Γ P E rfl t ht (D.u)
    D.huU πL («partial» D P t ht π) (π 0)
    (π 1) upperBid hupperBid hfloor hj
  have hp := (native_private_means Γ P E rfl t ht (D.u)
    D.huU πL («partial» D P t ht π) (π 0)
    (π 1) upperBid hupperBid hfloor hj).1
  have hn := population_mean_eq P D.ξ t
    (mixedMoment Γ P E D.ξ reg) ht.le reg
  dsimp only [ZeroSourceCommonMenuError.lambda]
  rw [mixed_mean D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags,
    reciprocal_mean D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags]
  change _≤ meanNumerator P D.ξ (mixedMoment Γ P E D.ξ reg) reg/
    reciprocalMoment Γ P E D.ξ reg ∧ _≤1
  have ha' : (∫ x, MenuError.indicator (categoryFlag E 1) x ∂userLaw Γ)=
      activeMass P.theta-upperMass P t := ha
  have hg' : 0< reciprocalMoment Γ P E D.ξ reg ∧
      (1-D.ξ)*Central.B D.ξ+2*γ D.ξ≤
        populationNumerator D.ξ (99/200) (activeMass P.theta-upperMass P t)
          (mixedMoment Γ P E D.ξ reg) ((partialMass+upperMass P t)/2) (keptShare P t reg)/
          reciprocalMoment Γ P E D.ξ reg ∧
      populationNumerator D.ξ (99/200) (activeMass P.theta-upperMass P t)
          (mixedMoment Γ P E D.ξ reg) ((partialMass+upperMass P t)/2) (keptShare P t reg)/
          reciprocalMoment Γ P E D.ξ reg+2*γ D.ξ≤1 := by
    simpa only [ha',hp] using! hg
  rw [hn] at hg'
  have hγ : 0≤ γ D.ξ := by unfold γ; linarith [D.hξ]
  exact ⟨by linarith [hg'.2.1],by linarith [hg'.2.2]⟩

include ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags huB in
theorem actual_nominal_margins (hξh : D.ξ<1/2) (hR : D.R=Central.R D.ξ)
    (hRp : D.Up≤ Central.R D.ξ+D.ξ/1000)
    (hsmall : relativeError P.zeta (D.u) (Central.B D.ξ)≤ D.ξ/1000)
    (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000) (reg : Bool) :
    (1-D.ξ)*Central.B D.ξ+2*γ D.ξ≤ lam reg ∧ lam reg+2*γ D.ξ≤1 := by
  have hj := game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare
  have G := native_nominal_guard_interior Γ P E rfl t ht (D.u)
    D.hu D.huU πL («partial» D P t ht π)
    (π 0) (π 1) upperBid hupperBid hfloor hj
    D.ξ D.hξ hξh huB (by change D.U≤Central.B D.ξ; simpa only [←hF] using (base_active_le_physical D).trans D.hUF) hR hRp hsmall hmSmall reg
  have hg := G.mean_margins D.hξ.le
    (integral_nonneg fun x => (indicator_bounds (categoryFlag E 2) x).1)
  have ha := SourceNativeMoments.native_active_mean Γ P E rfl t ht (D.u)
    D.huU πL («partial» D P t ht π) (π 0)
    (π 1) upperBid hupperBid hfloor hj
  have hp := (native_private_means Γ P E rfl t ht (D.u)
    D.huU πL («partial» D P t ht π) (π 0)
    (π 1) upperBid hupperBid hfloor hj).1
  have hn := population_mean_eq P D.ξ t
    (mixedMoment Γ P E D.ξ reg) ht.le reg
  dsimp only [ZeroSourceCommonMenuError.lambda]
  rw [mixed_mean D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags,
    reciprocal_mean D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags]
  change _≤ meanNumerator P D.ξ (mixedMoment Γ P E D.ξ reg) reg/
    reciprocalMoment Γ P E D.ξ reg ∧ _≤1
  have ha' : (∫ x, MenuError.indicator (categoryFlag E 1) x ∂userLaw Γ)=
      activeMass P.theta-upperMass P t := ha
  have hg' : 0< reciprocalMoment Γ P E D.ξ reg ∧
      (1-D.ξ)*Central.B D.ξ+2*γ D.ξ≤
        populationNumerator D.ξ (99/200) (activeMass P.theta-upperMass P t)
          (mixedMoment Γ P E D.ξ reg) ((partialMass+upperMass P t)/2) (keptShare P t reg)/
          reciprocalMoment Γ P E D.ξ reg ∧
      populationNumerator D.ξ (99/200) (activeMass P.theta-upperMass P t)
          (mixedMoment Γ P E D.ξ reg) ((partialMass+upperMass P t)/2) (keptShare P t reg)/
          reciprocalMoment Γ P E D.ξ reg+2*γ D.ξ≤1 := by
    simpa only [ha',hp] using! hg
  rw [hn] at hg'
  have hγ : 0≤ γ D.ξ := by unfold γ; linarith [D.hξ]
  exact ⟨by linarith [hg'.2.1],by linarith [hg'.2.2]⟩

end FCAppendix.Affine.Tail04.ZeroSourceMultiplierRectangle
