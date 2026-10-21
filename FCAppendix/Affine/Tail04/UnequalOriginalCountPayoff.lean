import FCAppendix.Affine.Tail04.NoisyPrivateLaws
import FCAppendix.Affine.Tail04.EqualNoisyUtilities

noncomputable section
namespace FCAppendix.Affine.Tail04.UnequalOriginalCountPayoff
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy SortedAllNoise
open AllNoiseFiniteSelector
open scoped BigOperators

variable {N : ℕ} [Nonempty (Fin N)]

def parameter {H : ℕ} {R Rp B : ℝ} (reg : Bool)
    (b : Fin N → Icc (1:ℝ) B) (σ : WeakProbability.Law (Signal H R Rp)) :
    Parameters N H R Rp B :=
  (((reg,(∅,(Finset.univ,∅))),sortedBox b),(σ,1))

omit [Nonempty (Fin N)] in
lemma parameter_publicBids {H : ℕ} {R Rp B : ℝ} (reg : Bool)
    (b : Fin N → Icc (1:ℝ) B) (σ : WeakProbability.Law (Signal H R Rp)) :
    publicBids (parameter reg b σ)=sorted (fun i => (b i:ℝ)) := rfl

omit [Nonempty (Fin N)] in
lemma parameter_regime {H : ℕ} {R Rp B : ℝ} (reg : Bool)
    (b : Fin N → Icc (1:ℝ) B) (σ : WeakProbability.Law (Signal H R Rp)) :
    regime (parameter reg b σ).1.1=reg := rfl

def originalCount (H0 H1 c : ℕ) (ξ B R Rp Rm width e0 F : ℝ)
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → Icc (1:ℝ) B) (σ : WeakProbability.Law (Signal H0 R Rp))
    (θ0 : Measure (Row H0 R Rp Rm)) (θ1 : Measure (Row H1 R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1] (i : Fin N) : CountLaw 2 :=
  let p := parameter reg b σ
  let k := focalRank (fun j => (b j:ℝ)) i
  if lowPresent then
    OriginalOwnerCount.countLaw N H0 H1 c ξ B R Rp Rm width ν0 ν1 p
      (sourceFlagProb e0 F (publicBids p))
      (sourceFlagProb_nonneg e0 F (publicBids p))
      (sourceFlagProb_le_one e0 F (publicBids p)) θ0 θ1 k
  else NativeTypicalCount.fallbackCount N H0 H1 c ξ B R Rp Rm p θ0 θ1 k

omit [Nonempty (Fin N)] in
lemma parameter_not_typical (H0 H1 c : ℕ) (ξ B R Rp width : ℝ)
    (reg : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → Icc (1:ℝ) B) (σ : WeakProbability.Law (Signal H0 R Rp)) :
    ¬UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 (parameter reg b σ) := by
  have hw := (TypicalGuard.weight_bounds N H0 H1 c ξ B R Rp width reg
    ∅ Finset.univ ∅ (sorted (fun i => (b i:ℝ))) ν0 ν1).2
  change ¬(1:ℝ)<_
  exact not_lt.mpr hw

omit [Nonempty (Fin N)] in

theorem noLow_pairCount (H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (reg : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → Icc (1:ℝ) B) (σ : WeakProbability.Law (Signal H0 R Rp))
    (i : Fin N)
    (z : (Row H0 R Rp Rm×unitInterval)×(Row H1 R Rp Rm×unitInterval)) :
    originalPairCount (unequal0 N H0 H1 c ξ B R Rp Rm width ν0 ν1)
      (unequal1 N H0 H1 c ξ B R Rp Rm width ν0 ν1)
      (parameter reg b σ) (Sum.inl i) (Sum.inl i) z=
    originalPairCount (NativeTypicalCount.fallback0 N H0 H1 c ξ B R Rp Rm)
      (NativeTypicalCount.fallback1 N H0 H1 c ξ B R Rp Rm)
      (parameter reg b σ) (Sum.inl i) (Sum.inl i) z := by
  have hn := parameter_not_typical H0 H1 c ξ B R Rp width reg ν0 ν1 b σ
  simp only [originalPairCount,localAccept,unequal0,unequal1,if_neg hn,
    NativeTypicalCount.fallback0,NativeTypicalCount.fallback1]
  rfl

theorem originalCount_eq_raw (H0 H1 c : ℕ) {ξ B R Rp Rm width e0 F : ℝ}
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → Icc (1:ℝ) B) (σ : WeakProbability.Law (Signal H0 R Rp))
    (θ0 : Measure (Row H0 R Rp Rm)) (θ1 : Measure (Row H1 R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hν0 : θ0.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν0)
    (hν1 : θ1.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν1)
    (hξ : ξ∈Ioo (0:ℝ) 1) (hw : 0< width) (hR : 0< R) (hRRm : R≤ Rm)
    (hRp : Rp<1) (hgap : (1-ξ)*B< R) (hfloor : B< Rm)
    (hno : ∀ j k,j≠k → (b j:ℝ)≠(b k:ℝ)) (i : Fin N) :
    originalCount H0 H1 c ξ B R Rp Rm width e0 F reg lowPresent ν0 ν1 b σ θ0 θ1 i=
      UnequalNoisyCountPayoff.rawCount H0 H1 c ξ B R Rp width e0 F reg lowPresent
        ν0 ν1 (fun j => (b j:ℝ)) i := by
  let p := parameter reg b σ
  let k := focalRank (fun j => (b j:ℝ)) i
  have hdistinct : ∀ j,j≠k → publicBids p j≠publicBids p k := by
    intro j hj
    apply hno
    exact (PrivateRowSorting.permutation (fun t => (b t:ℝ))).injective.ne hj
  have hf := AtypicalActiveNoisy.original_countLaw N H0 H1 c p θ0 θ1 ν0 ν1
    hν0 hν1 ⟨hξ.1.le,hξ.2⟩ hR hRRm hRp hgap hfloor k hdistinct
  have hf' : NativeTypicalCount.fallbackCount N H0 H1 c ξ B R Rp Rm p θ0 θ1 k=
      sortedFallback N H0 H1 c ξ ν0 ν1 (fun j => (b j:ℝ)) i := hf
  cases lowPresent
  · exact hf'
  · change OriginalOwnerCount.countLaw N H0 H1 c ξ B R Rp Rm width ν0 ν1 p
      (sourceFlagProb e0 F (publicBids p)) (sourceFlagProb_nonneg e0 F (publicBids p))
      (sourceFlagProb_le_one e0 F (publicBids p)) θ0 θ1 k=_
    rw [OriginalOwnerCount.countLaw_eq N H0 H1 c R Rp Rm width ν0 ν1
      hξ.1 hξ.2.le hw p _ _ _ θ0 θ1 hν0 hν1 k,hf']
    exact UnequalNoisyCountPayoff.typicalRankCount_sorted
      (NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1)
      (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1)
      e0 F (fun j => (b j:ℝ)) i _

omit [Nonempty (Fin N)] in

lemma original_flag_formula {B F e0 : ℝ} (he0 : 0≤ e0) (he1 : e0≤1)
    (hF : 1< F) (hBF : B≤ F) (b : Fin N → Icc (1:ℝ) B) (i : Fin N) :
    sourceFlagProb e0 F (fun j => (b j:ℝ)) i=mixedFlagProbability e0 F (b i) :=
  sourceFlagProb_eq he0 he1 hF _ i ⟨(b i).2.1,(b i).2.2.trans hBF⟩

theorem ae_originalCount_eq_raw (H0 H1 c : ℕ) {ξ U R Rp Rm width e0 F eps : ℝ}
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → Icc (1:ℝ) U) (σ : WeakProbability.Law (Signal H0 R Rp))
    (θ0 : Measure (Row H0 R Rp Rm)) (θ1 : Measure (Row H1 R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hν0 : θ0.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν0)
    (hν1 : θ1.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν1)
    (heps : 0< eps) (hξ : ξ∈Ioo (0:ℝ) 1) (hw : 0< width) (hR : 0< R) (hRRm : R≤ Rm)
    (hRp : Rp<1) (hgap : (1-ξ)*(U*(1+eps))< R) (hfloor : U*(1+eps)< Rm) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)),∀ i,
      originalCount H0 H1 c ξ (U*(1+eps)) R Rp Rm width e0 F reg lowPresent ν0 ν1
        (EqualNoisyUtilities.physical heps.le b z) σ θ0 θ1 i=
      UnequalNoisyCountPayoff.rawCount H0 H1 c ξ (U*(1+eps)) R Rp width e0 F reg lowPresent
        ν0 ν1 (noisyBids eps (fun j => (b j:ℝ)) z) i := by
  have hb (j : Fin N) : (b j:ℝ)≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (b j).2.1)
  filter_upwards [AtypicalActiveNoisy.ae_noisyBids_distinct heps.ne' _ hb] with z hz
  intro i
  exact originalCount_eq_raw H0 H1 c reg lowPresent ν0 ν1
    (EqualNoisyUtilities.physical heps.le b z) σ θ0 θ1 hν0 hν1 hξ hw hR hRRm hRp hgap hfloor hz i

theorem utility_eq_original_integral (H0 H1 c : ℕ) {ξ U R Rp Rm width e0 F eps eta : ℝ}
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → Icc (1:ℝ) U) (σ : WeakProbability.Law (Signal H0 R Rp))
    (θ0 : Measure (Row H0 R Rp Rm)) (θ1 : Measure (Row H1 R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hν0 : θ0.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν0)
    (hν1 : θ1.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν1)
    (heps : 0< eps) (hξ : ξ∈Ioo (0:ℝ) 1) (hw : 0< width) (hR : 0< R) (hRRm : R≤ Rm)
    (hRp : Rp<1) (hgap : (1-ξ)*(U*(1+eps))< R) (hfloor : U*(1+eps)< Rm)
    (heta0 : 0≤ eta) (heta1 : eta≤1) (v : ℝ) (i : Fin N) :
    UnequalNoisyCountPayoff.utility H0 H1 c ξ (U*(1+eps)) R Rp width e0 F eps eta
      reg lowPresent heta0 heta1 ν0 ν1 i (v,fun j => (b j:ℝ))=
      ∫ z : Fin N → unitInterval,
        affineCountUtility (originalCount H0 H1 c ξ (U*(1+eps)) R Rp Rm width e0 F
          reg lowPresent ν0 ν1 (EqualNoisyUtilities.physical heps.le b z) σ θ0 θ1 i)
          v (noisyBids eps (fun j => (b j:ℝ)) z i) eta heta0 heta1
          ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)) := by
  rw [UnequalNoisyCountPayoff.utility_eq_integral H0 H1 c ξ (U*(1+eps)) R Rp width
    e0 F eta reg lowPresent heps heta0 heta1 ν0 ν1 i v]
  apply integral_congr_ae
  filter_upwards [ae_originalCount_eq_raw H0 H1 c reg lowPresent ν0 ν1 b σ θ0 θ1
    hν0 hν1 heps hξ hw hR hRRm hRp hgap hfloor] with z hz
  rw [hz i]

end FCAppendix.Affine.Tail04.UnequalOriginalCountPayoff
