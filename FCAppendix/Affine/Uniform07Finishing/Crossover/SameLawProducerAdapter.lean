import FCAppendix.Affine.Uniform07Finishing.Crossover.NativeBroadcastLaw
import FCAppendix.Affine.Uniform07Finishing.Native.SourceProducerAdapter

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology
open Crossover Crossover.Physical

def UniformAuxiliaryData05.crossoverBroadcastLaw (D : UniformAuxiliaryData05)
    (row : Uniform07.Row) (k : ℕ) :
    BroadcastLaw05 (D.market row k).native (Uniform07.cutoff row) (Early.bidCap row) :=
  (D.market row k).broadcastLaw (D.positive_bid_continuity row k) (D.lower_broadcast row k)

structure SameLawCrossoverKernels06 (D : UniformAuxiliaryData05) (row : Uniform07.Row) where
  canonicalEvent : ∀ k, Fin (D.start+k) → CanonicalEvent (D.market row k).native
  A : ℝ→ℝ
  Amin : ℝ
  Amax : ℝ
  Rmax : ℝ
  Dmax : ℝ
  AminPositive : 0< Amin
  RmaxNonnegative : 0≤ Rmax
  DmaxNonnegative : 0≤ Dmax
  e19 : ℕ→ℝ
  eS : ℕ→ℝ
  eD : ℕ→ℝ
  ell : ℕ→ℝ
  nonnegative : ∀ᶠ k in atTop, 0≤ e19 k ∧ 0≤ eS k ∧ 0≤ eD k ∧ 0< ell k
  core : ∀ᶠ k in atTop, ∀ i : Fin (D.start+k),
    Nonempty (RemoteCore06 row (D.market row k).native i (canonicalEvent k i)
      (sourceCrossoverStart row) (sourceCrossoverEnd row) (Early.bidCap row)
      (D.crossoverBroadcastLaw row k) A Amin Amax Rmax Dmax (e19 k) (ell k))
  split : ∀ᶠ k in atTop, ∀ i : Fin (D.start+k),
    Nonempty (PureDerivativeBounds06 (D.market row k).native i (canonicalEvent k i)
      (Uniform07.cutoff row) (sourceCrossoverStart row) (sourceCrossoverEnd row)
      (eS k) (eD k))
  e19Small : Tendsto e19 atTop (𝓝 0)
  successCoefficient : ℝ
  successRate : ℝ
  successRatePositive : 0< successRate
  successChernoff : ∀ᶠ k in atTop,
    eS k≤ successCoefficient*Real.exp (-successRate*((D.start+k:ℕ):ℝ))
  duplicateSmall : Tendsto eD atTop (𝓝 0)
  duplicateRentSmall : Tendsto
    (fun k => eD k/(((D.start+k:ℕ):ℝ)*sourceCrossoverStart row*ell k/2))
      atTop (𝓝 0)

def SameLawCrossoverKernels06.toCrossoverFamily
    {D : UniformAuxiliaryData05} {row : Uniform07.Row}
    (K : SameLawCrossoverKernels06 D row) :
    CrossoverFamily06 (fun k=>(D.market row k).native) row where
  populationTendsto:=tail_population_tendsto D.start
  broadcast:=D.crossoverBroadcastLaw row
  canonicalEvent:=K.canonicalEvent
  A:=K.A
  Amin:=K.Amin
  Amax:=K.Amax
  Rmax:=K.Rmax
  Dmax:=K.Dmax
  AminPositive:=K.AminPositive
  RmaxNonnegative:=K.RmaxNonnegative
  DmaxNonnegative:=K.DmaxNonnegative
  e19:=K.e19
  eS:=K.eS
  eD:=K.eD
  ell:=K.ell
  nonnegative:=K.nonnegative
  core:=K.core
  split:=K.split
  e19Small:=K.e19Small
  successCoefficient:=K.successCoefficient
  successRate:=K.successRate
  successRatePositive:=K.successRatePositive
  successChernoff:=K.successChernoff
  duplicateSmall:=K.duplicateSmall
  duplicateRentSmall:=K.duplicateRentSmall

structure SameLawPhysicalKernels05_06 (P : UniformPhysicalLowerData05) where
  crossover : ∀ row, SameLawCrossoverKernels06 P.toAuxiliary row
  low : ∀ row, LowFamily06 (fun k=>(P.market row k).native) row
  product : ∀ row, ProductFamily05 (fun k=>(P.market row k).native) row
    (fun k=>(P.market row k).R)
  entry : ∀ row, EntryFullMenu06 (fun k=>(P.market row k).native) row
  canonical : ∀ row, CanonicalOptimizer06 (fun k=>(P.market row k).native) row

def SameLawPhysicalKernels05_06.toAuxiliaryKernels
    {P : UniformPhysicalLowerData05} (K : SameLawPhysicalKernels05_06 P) :
    UniformAuxiliaryKernels05_06 P.toAuxiliary where
  physical:=fun row=>{
    crossover:=(K.crossover row).toCrossoverFamily
    low:=K.low row
    product:=K.product row
    entry:=K.entry row
    canonical:=K.canonical row }

def uniform_native_pair_from_same_law_physical_producers
    (P : UniformPhysicalLowerData05) (K : SameLawPhysicalKernels05_06 P) :
    UniformNativePair :=
  uniform_native_pair_from_physical_lower_producers P K.toAuxiliaryKernels

theorem aff_uniform_result_from_same_law_physical_producers
    (P : UniformPhysicalLowerData05) (K : SameLawPhysicalKernels05_06 P) :
    AffUniformResult :=
  aff_uniform_result_from_physical_lower_producers P K.toAuxiliaryKernels

end FCAppendix.Affine.Uniform07Finishing
