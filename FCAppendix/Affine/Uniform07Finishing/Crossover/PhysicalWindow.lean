import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalRent
import FCAppendix.Affine.Uniform07Finishing.Crossover.OverlapStart

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology

namespace Physical
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def canonicalSlope (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (b : ℝ) : ℝ :=
  deriv (canonicalMarginal Γ i B) b/canonicalMarginal Γ i B b

def finiteBarrier (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (eta t b : ℝ) : ℝ :=
  barrier eta b (canonicalSlope Γ i B b) (comparisonMarginal Γ i B t b)
    (canonicalDuplicate Γ i B b) (deriv (canonicalDuplicate Γ i B) b)

def canonicalShare (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (t b : ℝ) : ℝ :=
  canonicalMarginal Γ i B b/comparisonMarginal Γ i B t b

def physicalFlow (Γ : FiniteGame m 2 c Seed) (t b : ℝ) : ℝ :=
  deriv (pureRank m c t) (rank Γ t b)*deriv (rank Γ t) b

structure BroadcastLaw05 (Γ : FiniteGame m 2 c Seed) (t U : ℝ) where
  lower : ProbabilityMeasure (ℝ × Icc (0:ℝ) U)
  literal : (Γ.F ⊗ₘ Γ.σ).restrict {z : ℝ × JointAction 2 | z.1≤ t} =
    ENNReal.ofReal t • (lower : Measure (ℝ × Icc (0:ℝ) U)).map
      (fun z => (z.1,sourceLowerBroadcastAction U z.2))
  atomless : NullSingletonClass (lowerBidMeasure Γ t)
  payoffContinuous : ∀ i : Fin m, ∀ z : ℝ × Icc (0:ℝ) U, 0< z.2.1 →
    ContinuousAt (fun w : ℝ × Icc (0:ℝ) U =>
      (problem Γ i).payoff w.1 (sourceLowerBroadcastAction U w.2)) z
  broadcastIC : ∀ᵐ z ∂(lower : Measure (ℝ × Icc (0:ℝ) U)),
    ∀ i : Fin m, ∀ b' : Icc (0:ℝ) U,
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U b')≤
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)

theorem BroadcastLaw05.rankContinuous {Γ : FiniteGame m 2 c Seed} {t U : ℝ}
    (P : BroadcastLaw05 Γ t U) : Continuous (rank Γ t) := by
  letI : NullSingletonClass (lowerBidMeasure Γ t) := P.atomless
  letI : IsFiniteMeasure (lowerBidMeasure Γ t) := by
    unfold lowerBidMeasure
    infer_instance
  have h := continuous_finite_bid_cdf (lowerBidMeasure Γ t) (fun b => measure_singleton b)
  exact h.congr (fun b => (rank_eq_lowerBidMeasure Γ t b).symm)

theorem BroadcastLaw05.literal_bid_mass {Γ : FiniteGame m 2 c Seed} {t U : ℝ}
    (P : BroadcastLaw05 Γ t U) :
    lowerBidMeasure Γ t = ENNReal.ofReal t •
      (((P.lower : Measure (ℝ × Icc (0:ℝ) U)).map Prod.snd).map
        (fun b : Icc (0:ℝ) U => (b:ℝ))) := by
  unfold lowerBidMeasure
  rw [P.literal,Measure.map_smul]
  have hmap := Measure.map_map (μ := (P.lower : Measure (ℝ × Icc (0:ℝ) U)))
    ((measurable_bid 2).comp measurable_snd)
    (measurable_fst.prodMk ((sourceLowerBroadcastAction_measurable U).comp measurable_snd))
  simp only [Function.comp_def] at hmap
  rw [hmap,Measure.map_map measurable_subtype_coe measurable_snd]
  rfl

theorem BroadcastLaw05.support_adapter {Γ : FiniteGame m 2 c Seed} {t U : ℝ}
    (P : BroadcastLaw05 Γ t U) {b : Icc (0:ℝ) U}
    (hb : (b:ℝ)∈(lowerBidMeasure Γ t).support) :
    b∈((P.lower : Measure (ℝ × Icc (0:ℝ) U)).map Prod.snd).support :=
  bid_support_of_scaled_subtype_map U (P.lower : Measure (ℝ × Icc (0:ℝ) U))
    (lowerBidMeasure Γ t) (ENNReal.ofReal t) P.literal_bid_mass hb

structure CanonicalAt06 (row : Uniform07.Row) (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) (B : CanonicalEvent Γ) (A : ℝ→ℝ) (Dmax e19 b : ℝ) : Prop where
  canonicalDerivative : HasDerivAt (canonicalMarginal Γ i B)
    (deriv (canonicalMarginal Γ i B) b) b
  duplicateDerivative : HasDerivAt (canonicalDuplicate Γ i B)
    (deriv (canonicalDuplicate Γ i B) b) b
  finiteSlope : |canonicalSlope Γ i B b/(m:ℝ)-A b|≤ e19
  canonicalPaymentRatio : canonicalDuplicate Γ i B b≤
    2*canonicalMarginal Γ i B b*(1+e19)/(Uniform07.xi row*b*canonicalSlope Γ i B b)
  canonicalDerivativeRatio : deriv (canonicalDuplicate Γ i B) b∈
    Icc (0:ℝ) (Dmax*canonicalMarginal Γ i B b)
  canonicalDerivativeAsymptotic :
    |deriv (canonicalDuplicate Γ i B) b/canonicalMarginal Γ i B b-
      2/(Uniform07.xi row*b)|≤ e19

def referenceSlope (m : ℕ) (A : ℝ→ℝ) (b : ℝ) : ℝ := (m:ℝ)*A b

def leadingBarrier (row : Uniform07.Row) (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) (B : CanonicalEvent Γ) (A : ℝ→ℝ) (b : ℝ) : ℝ :=
  (1+(Uniform07.eta row/Uniform07.xi row)*
    canonicalShare Γ i B (Uniform07.cutoff row) b)/referenceSlope m A b

structure RemoteCore06 (row : Uniform07.Row) (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) (B : CanonicalEvent Γ) (L R U : ℝ)
    (P : BroadcastLaw05 Γ (Uniform07.cutoff row) U)
    (A : ℝ→ℝ) (Amin Amax Rmax Dmax e19 ell : ℝ) where
  interval : L≤ R
  bid0 : 0< L
  bid1 : R≤ 1
  feasible : R≤ U
  halfFeasible : Uniform07.cutoff row/2≤ U
  sourceInterval : Icc L R ⊆ Icc (Uniform07.cutoff row/2)
    (Uniform07.sourceZhi row*Uniform07.cutoff row)
  remote : Set (Icc (0:ℝ) U)
  remoteOpen : IsOpen remote
  remoteContains : ∀ b (hb : b∈Icc L R),
    (⟨b,⟨bid0.le.trans hb.1, hb.2.trans feasible⟩⟩ : Icc (0:ℝ) U)∈remote
  sorted : ∀ᵐ z ∂(P.lower : Measure (ℝ × Icc (0:ℝ) U)),
    z.2∈remote → z.1=rank Γ (Uniform07.cutoff row) z.2.1
  rankRange : ∀ b∈Icc L R, rank Γ (Uniform07.cutoff row) b∈Icc (0:ℝ) (Uniform07.cutoff row)
  rankAC : AbsolutelyContinuousOnInterval (rank Γ (Uniform07.cutoff row)) L R
  successAC : AbsolutelyContinuousOnInterval (success Γ i) L R
  duplicateAC : AbsolutelyContinuousOnInterval (duplicate Γ i) L R
  canonicalAC : AbsolutelyContinuousOnInterval (canonicalMarginal Γ i B) L R
  canonicalDuplicateAC : AbsolutelyContinuousOnInterval (canonicalDuplicate Γ i B) L R
  canonicalAE : ∀ᵐ b ∂(volume : Measure ℝ), b∈Icc L R →
    CanonicalAt06 row Γ i B A Dmax e19 b
  canonicalPositive : ∀ b∈Icc L R, 0< canonicalMarginal Γ i B b
  purePositive : ∀ b∈Icc L R, 0< pureRank m c (Uniform07.cutoff row) (rank Γ (Uniform07.cutoff row) b)
  canonicalDuplicateProbability : ∀ b∈Icc L R,
    canonicalDuplicate Γ i B b∈Icc (0:ℝ) (canonicalMarginal Γ i B b)
  pureDerivative : ∀ b∈Icc L R,
    HasDerivAt (pureRank m c (Uniform07.cutoff row))
      (deriv (pureRank m c (Uniform07.cutoff row)) (rank Γ (Uniform07.cutoff row) b))
      (rank Γ (Uniform07.cutoff row) b)
  pureDerivativePositive : ∀ b∈Icc L R,
    0< deriv (pureRank m c (Uniform07.cutoff row)) (rank Γ (Uniform07.cutoff row) b)
  pureDerivativeUpper : ∀ b∈Icc L R,
    deriv (pureRank m c (Uniform07.cutoff row)) (rank Γ (Uniform07.cutoff row) b)≤
      (21/10000:ℝ)*(m:ℝ)*pureRank m c (Uniform07.cutoff row) (rank Γ (Uniform07.cutoff row) b)
  sourceDerivative : ∀ b∈Icc L R, HasDerivWithinAt (negativePhysicalSourceRate row) (A b)
    (Icc (Uniform07.cutoff row/2)
      (Uniform07.sourceZhi row*Uniform07.cutoff row)) b
  rateContinuous : ContinuousOn A (Icc L R)
  rateBounds : ∀ b∈Icc L R, A b∈Icc Amin Amax
  canonicalRatio : ∀ b∈Icc L R,
    canonicalDuplicate Γ i B b≤ Rmax*canonicalMarginal Γ i B b/(m:ℝ)

  halfValueAcceptance : ∀ w∈Ioc (0:ℝ) (Uniform07.cutoff row), ell≤ q Γ i (w/2)
  halfValueDuplicate : ∀ w∈Ioc (0:ℝ) (Uniform07.cutoff row), duplicate Γ i (w/2)≤ ell/2
  commonDensity : ∀ᵐ b ∂(volume : Measure ℝ), b∈Icc L R →
    HasDerivAt (rank Γ (Uniform07.cutoff row)) (deriv (rank Γ (Uniform07.cutoff row)) b) b ∧
    HasDerivAt (success Γ i) (deriv (success Γ i) b) b ∧
    HasDerivAt (duplicate Γ i) (deriv (duplicate Γ i) b) b ∧
    (b∈(lowerBidMeasure Γ (Uniform07.cutoff row)).support →
      (rank Γ (Uniform07.cutoff row) b-b)*deriv (success Γ i) b=
        success Γ i b+Uniform07.eta row*duplicate Γ i b+
          Uniform07.eta row*b*deriv (duplicate Γ i) b)

structure RemoteKernels06 (row : Uniform07.Row) (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) (B : CanonicalEvent Γ) (L R U : ℝ)
    (P : BroadcastLaw05 Γ (Uniform07.cutoff row) U)
    (A : ℝ→ℝ) (Amin Amax Rmax Dmax e19 e ell : ℝ)
    extends RemoteCore06 row Γ i B L R U P A Amin Amax Rmax Dmax e19 ell where
  successValueError : ∀ b∈Icc L R,
    |successError Γ i B (Uniform07.cutoff row) b|≤
      e*comparisonMarginal Γ i B (Uniform07.cutoff row) b/(m:ℝ)
  duplicateValueError : ∀ b∈Icc L R,
    |duplicateError Γ i B b|≤ e*comparisonMarginal Γ i B (Uniform07.cutoff row) b/(m:ℝ)
  derivativeErrors : ∀ᵐ b ∂(volume : Measure ℝ), b∈Icc L R →
    |deriv (successError Γ i B (Uniform07.cutoff row)) b|≤
      e*(physicalFlow Γ (Uniform07.cutoff row) b/(m:ℝ)+comparisonMarginal Γ i B (Uniform07.cutoff row) b) ∧
    |deriv (duplicateError Γ i B) b|≤
      e*(physicalFlow Γ (Uniform07.cutoff row) b/(m:ℝ)+comparisonMarginal Γ i B (Uniform07.cutoff row) b)

theorem RemoteKernels06.density
    {row : Uniform07.Row} {Γ : FiniteGame m 2 c Seed} {i : Fin m}
    {B : CanonicalEvent Γ} {L R U : ℝ}
    {P : BroadcastLaw05 Γ (Uniform07.cutoff row) U} {A : ℝ→ℝ}
    {Amin Amax Rmax Dmax e19 e ell : ℝ}
    (E : RemoteKernels06 row Γ i B L R U P A Amin Amax Rmax Dmax e19 e ell) :
    ∀ᵐ b ∂(volume : Measure ℝ), b∈Icc L R →
      HasDerivAt (rank Γ (Uniform07.cutoff row)) (deriv (rank Γ (Uniform07.cutoff row)) b) b ∧
      HasDerivAt (success Γ i) (deriv (success Γ i) b) b ∧
      HasDerivAt (duplicate Γ i) (deriv (duplicate Γ i) b) b ∧
      (b∈(lowerBidMeasure Γ (Uniform07.cutoff row)).support →
        (rank Γ (Uniform07.cutoff row) b-b)*deriv (success Γ i) b=
          success Γ i b+Uniform07.eta row*duplicate Γ i b+
            Uniform07.eta row*b*deriv (duplicate Γ i) b) ∧
      |deriv (successError Γ i B (Uniform07.cutoff row)) b|≤
        e*(physicalFlow Γ (Uniform07.cutoff row) b/(m:ℝ)+comparisonMarginal Γ i B (Uniform07.cutoff row) b) ∧
      |deriv (duplicateError Γ i B) b|≤
        e*(physicalFlow Γ (Uniform07.cutoff row) b/(m:ℝ)+comparisonMarginal Γ i B (Uniform07.cutoff row) b) := by
  filter_upwards [E.commonDensity,E.derivativeErrors] with b hb he hbI
  exact ⟨(hb hbI).1,(hb hbI).2.1,(hb hbI).2.2.1,(hb hbI).2.2.2,(he hbI).1,(he hbI).2⟩

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
