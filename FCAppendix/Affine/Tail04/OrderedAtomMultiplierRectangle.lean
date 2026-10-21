import FCAppendix.Affine.Tail04.OrderedAtomCommonPayoff
import FCAppendix.Affine.Tail04.SourceMultiplierRectangle

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomMultiplierRectangle
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open FiniteTailNoisyGame SourceTailNoisyFixedPoint NativeNoisySource LatentNoisyPopulation
open OrderedAtomActiveLaw OrderedAtomActiveCompression OrderedOriginalCommonMenuCount
open MenuError SourceMenuPopulation SourceMenuError SourceMomentRectangle SourceCommonMoments

def MomentInvariant (P : ValueParameters) (ξ ρ : ℝ) (Λ : Set (ℝ×ℝ)) : Prop :=
  ∀ M W : Bool→ℝ,
    (∀ reg,|M reg-centerMoment P reg|≤ centerMoment P reg*ρ) →
    (∀ reg,|W reg-centerMoment P reg|≤ centerMoment P reg*ρ) →
    (meanNumerator P ξ (M false) false/W false,
      meanNumerator P ξ (M true) true/W true)∈Λ

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (hfloor : ∀ v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
  (hF : D.F=Central.B D.ξ) (hflags : ∀ reg,D.e0 reg=baseFlag P reg)
  (huB : 1+bulkPhysicalWidth D< Central.B D.ξ)

local notation "Ds" => installOriginal D P t ht
local notation "E" => regions D P hdR H hBH
local notation "Γ" => game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "μ" => drawLaw D P t ht πL π upperBid hupperBid
local notation "tag" => latentTag D P hdR H hBH
local notation "decode" => latentBid D P hdR H hBH
local notation "M" => mixedMean Ds tag decode μ
local notation "W" => reciprocalMean Ds tag decode μ
local notation "lam" => OrderedSourceCommonMenuError.lambda D P t ht πL π upperBid hupperBid hdR H hBH

include hfloor N hrare hF hflags huB in
theorem actual_moment_error (reg : Bool) :
    |M reg-centerMoment P reg|≤ centerMoment P reg*
        relativeError P.zeta (bulkPhysicalWidth D) (Central.B D.ξ) ∧
    |W reg-centerMoment P reg|≤ centerMoment P reg*
        relativeError P.zeta (bulkPhysicalWidth D) (Central.B D.ξ) := by
  exact SourceMultiplierRectangle.actual_moment_error D P t ht πL π upperBid hupperBid
    hdR H hBH hfloor N hrare hF hflags huB reg

include hfloor N hrare hF hflags huB in
theorem actual_mem {ρ : ℝ} {Λ : Set (ℝ×ℝ)}
    (hrect : MomentInvariant P D.ξ ρ Λ)
    (hρ : relativeError P.zeta (bulkPhysicalWidth D) (Central.B D.ξ)≤ ρ) :
    (lam false,lam true)∈Λ := by
  apply hrect M W
  · intro reg
    exact (actual_moment_error D P t ht πL π upperBid hupperBid hdR H hBH
      hfloor N hrare hF hflags huB reg).1.trans
        (mul_le_mul_of_nonneg_left hρ (centerMoment_pos P reg).le)
  · intro reg
    exact (actual_moment_error D P t ht πL π upperBid hupperBid hdR H hBH
      hfloor N hrare hF hflags huB reg).2.trans
        (mul_le_mul_of_nonneg_left hρ (centerMoment_pos P reg).le)

include hfloor N hrare hF hflags huB in
theorem actual_nominal_bounds (hξh : D.ξ<1/2) (hR : D.R=Central.R D.ξ)
    (hRp : D.V≤ Central.R D.ξ+D.ξ/1000)
    (hsmall : relativeError P.zeta (bulkPhysicalWidth D) (Central.B D.ξ)≤ D.ξ/1000)
    (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000) (reg : Bool) :
    (1-D.ξ)*Central.B D.ξ≤ lam reg ∧ lam reg≤1 := by
  exact SourceMultiplierRectangle.actual_nominal_bounds D P t ht πL π upperBid hupperBid
    hdR H hBH hfloor N hrare hF hflags huB hξh hR hRp hsmall hmSmall reg

theorem eventually_physical_tolerance {ξ Up u k ρ : ℝ}
    (hξ : 0< ξ) (hξh : ξ<1/2) (hUp0 : 0< Up) (hUp : Up<1)
    (hρ : relativeError P.zeta u (Central.B ξ)< ρ) :
    ∀ᶠ N in atTop,relativeError P.zeta
      (SourceMovingScalarGuards.bulkWidth ξ Up u k N) (Central.B ξ)< ρ := by
  have hw := (SourceMovingScalarGuards.physical_tendsto hξ hξh hUp0 hUp u k).2.2
  have he := (hw.mul_const (1+2/(Central.B ξ-1))).const_add P.zeta
  exact he.eventually (gt_mem_nhds hρ)

end FCAppendix.Affine.Tail04.OrderedAtomMultiplierRectangle
