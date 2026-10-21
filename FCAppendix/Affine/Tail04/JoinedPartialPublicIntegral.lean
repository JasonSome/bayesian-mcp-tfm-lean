import FCAppendix.Affine.Tail04.UnequalPartialOriginalIntegral
import FCAppendix.Affine.Tail04.PublicScenario
import FCAppendix.Affine.Tail04.PrivatePartialSorting

noncomputable section
namespace FCAppendix.Affine.Tail04.JoinedPartialPublicIntegral
open MeasureTheory ProbabilityTheory Set Classical
open LocalHighCommon EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy AllCountAtypical
open JoinedPartialNoisy PartialPublicWeights OriginalOwnerCount AtypicalPartialNoisy
open scoped BigOperators

def parameters {N H : ℕ} {B R V : ℝ} (b : Fin N → Icc (1:ℝ) B)
    (σ : WeakProbability.Law (Signal H R V)) (q : Scenario N×unitInterval) :
    Parameters N H R V B := ((q.1,b),(σ,q.2))

lemma measurable_parameters {N H : ℕ} {B R V : ℝ} (b : Fin N → Icc (1:ℝ) B)
    (σ : WeakProbability.Law (Signal H R V)) : Measurable (parameters b σ) :=
  (measurable_fst.prodMk measurable_const).prodMk (measurable_const.prodMk measurable_snd)

def choice (Q : PublicScenario.Data) {N : ℕ} (H0 H1 : ℕ)
    (b : Fin N → ℝ) (lowPresent : Bool) (u : unitInterval) : Scenario N×unitInterval :=
  if lowPresent then PublicScenario.draw Q N (b,(H0,H1)) u
  else (PublicScenario.fallback N,1)

lemma fallback_weight (Q : PublicScenario.Data) {N : ℕ} (H0 H1 : ℕ)
    {B R V : ℝ} (width : ℝ) (b : Fin N → Icc (1:ℝ) B)
    (σ : WeakProbability.Law (Signal H0 R V)) (u : unitInterval) :
    publicWeight N H0 H1 Q.c Q.ξ B R V width (Q.marksLaw H0) (Q.marksLaw H1)
      (parameters b σ (PublicScenario.fallback N,u))=0 := by
  simp [publicWeight,parameters,PublicScenario.fallback,TypicalGuard.weight,
    TypicalHighPolicy.Structural,mixed,owner0,owner1]

def publicRule (Q : PublicScenario.Data) {N : ℕ} (H0 H1 : ℕ)
    {B R V : ℝ} (width : ℝ) (b : Fin N → Icc (1:ℝ) B)
    (σ : WeakProbability.Law (Signal H0 R V)) (I : ℝ)
    (q : Scenario N×unitInterval) : ℝ :=
  if UseTypical N H0 H1 Q.c Q.ξ B R V width (Q.marksLaw H0) (Q.marksLaw H1)
      (parameters b σ q) then (if q.1.1 then 0 else 1) else I

lemma measurable_publicRule (Q : PublicScenario.Data) {N : ℕ} (H0 H1 : ℕ)
    {B R V : ℝ} (width : ℝ) (b : Fin N → Icc (1:ℝ) B)
    (σ : WeakProbability.Law (Signal H0 R V)) (I : ℝ) :
    Measurable (publicRule Q H0 H1 width b σ I) :=
  Measurable.ite ((measurableSet_useTypical N H0 H1 Q.c Q.ξ B R V width
    (Q.marksLaw H0) (Q.marksLaw H1)).preimage (measurable_parameters b σ))
      ((measurable_of_countable (fun r : Bool => if r then (0:ℝ) else 1)).comp
        measurable_fst.fst) measurable_const

lemma publicRule_bound (Q : PublicScenario.Data) {N : ℕ} (H0 H1 : ℕ)
    {B R V : ℝ} (width : ℝ) (b : Fin N → Icc (1:ℝ) B)
    (σ : WeakProbability.Law (Signal H0 R V)) (I : ℝ) (q : Scenario N×unitInterval) :
    ‖publicRule Q H0 H1 width b σ I q‖≤1+|I| := by
  unfold publicRule
  split_ifs <;> simp only [Real.norm_eq_abs,abs_zero,abs_one] <;> linarith [abs_nonneg I]

lemma publicRule_branch (Q : PublicScenario.Data) {N : ℕ} (H0 H1 : ℕ)
    {B R V : ℝ} (width : ℝ) (b : Fin N → Icc (1:ℝ) B)
    (σ : WeakProbability.Law (Signal H0 R V)) (I : ℝ) (sc : Scenario N) :
    (∫ u : unitInterval,publicRule Q H0 H1 width b σ I (sc,u))=
      publicWeight N H0 H1 Q.c Q.ξ B R V width (Q.marksLaw H0) (Q.marksLaw H1)
        (parameters b σ (sc,1))*(if sc.1 then 0 else 1)+
      (1-publicWeight N H0 H1 Q.c Q.ξ B R V width (Q.marksLaw H0) (Q.marksLaw H1)
        (parameters b σ (sc,1)))*I := by
  convert! integral_strict_branch
    (JoinedPartialNoisy.weight N H0 H1 Q.c Q.ξ B R V width
      (Q.marksLaw H0) (Q.marksLaw H1) (parameters b σ (sc,1))) (if sc.1 then 0 else 1) I using 1

lemma conditionalScenario_rule (Q : PublicScenario.Data) {N : ℕ} (hN : 0< N)
    (H0 H1 : ℕ) {B R V : ℝ} (width : ℝ) (b : Fin N → Icc (1:ℝ) B)
    (σ : WeakProbability.Law (Signal H0 R V)) (I : ℝ) (reg : Bool) :
    (PublicScenario.conditionalScenarioLaw Q N (H0,H1) (fun j => (b j:ℝ)) reg).expect
      (fun sc => ∫ u : unitInterval,publicRule Q H0 H1 width b σ I (sc,u))=
      UnequalPartialCountPayoff.rawWeight N H0 H1 Q.c Q.ξ B R V width (PublicScenario.e0 Q reg) Q.B0
        reg true (Q.marksLaw H0) (Q.marksLaw H1) (fun j => (b j:ℝ))*(if reg then 0 else 1)+
      (1-UnequalPartialCountPayoff.rawWeight N H0 H1 Q.c Q.ξ B R V width (PublicScenario.e0 Q reg) Q.B0
        reg true (Q.marksLaw H0) (Q.marksLaw H1) (fun j => (b j:ℝ)))*I := by
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  let p : Parameters N H0 R V B := (((reg,(∅,(∅,∅))),b),(σ,1))
  have hw := owner_weight_expect H0 H1 Q.c Q.ξ B R V width (PublicScenario.e0 Q reg) Q.B0
    (Q.marksLaw H0) (Q.marksLaw H1) p
  rw [PublicScenario.conditionalScenarioLaw,dif_pos hN,FiniteLaw.expect_map]
  simp_rw [publicRule_branch]
  change (integerOwnerPlanLaw (fun j => (b j:ℝ)) _ _ _ _).expect
    (fun out => publicWeight N H0 H1 Q.c Q.ξ B R V width (Q.marksLaw H0) (Q.marksLaw H1)
      (planParameter p out.1.1 out.1.2 out.2)*(if reg then 0 else 1)+
      (1-publicWeight N H0 H1 Q.c Q.ξ B R V width (Q.marksLaw H0) (Q.marksLaw H1)
        (planParameter p out.1.1 out.1.2 out.2))*I)=_
  rw [FiniteLaw.expect_add,FiniteLaw.expect_mul_const,FiniteLaw.expect_mul_const,
    FiniteLaw.expect_sub,FiniteLaw.expect_const]
  convert! congrArg (fun w : ℝ => w*(if reg then 0 else 1)+(1-w)*I) hw using 1

theorem public_rule_integral (Q : PublicScenario.Data) {N : ℕ} (H0 H1 : ℕ)
    {B R V : ℝ} (width : ℝ) (b : Fin N → Icc (1:ℝ) B)
    (σ : WeakProbability.Law (Signal H0 R V)) (I : ℝ) (lowPresent : Bool) :
    (∫ u : unitInterval,publicRule Q H0 H1 width b σ I
      (choice Q H0 H1 (fun j => (b j:ℝ)) lowPresent u))=
      (IndependentCounts.bernoulli Q.θ Q.θ_nonneg Q.θ_le_one).expect (fun reg =>
        UnequalPartialCountPayoff.rawWeight N H0 H1 Q.c Q.ξ B R V width (PublicScenario.e0 Q reg) Q.B0
          reg lowPresent (Q.marksLaw H0) (Q.marksLaw H1) (fun j => (b j:ℝ))*(if reg then 0 else 1)+
        (1-UnequalPartialCountPayoff.rawWeight N H0 H1 Q.c Q.ξ B R V width (PublicScenario.e0 Q reg) Q.B0
          reg lowPresent (Q.marksLaw H0) (Q.marksLaw H1) (fun j => (b j:ℝ)))*I) := by
  have hf := measurable_publicRule Q H0 H1 width b σ I
  cases lowPresent
  · have hz (reg : Bool) : UnequalPartialCountPayoff.rawWeight N H0 H1 Q.c Q.ξ B R V width
        (PublicScenario.e0 Q reg) Q.B0 reg false (Q.marksLaw H0) (Q.marksLaw H1) (fun j => (b j:ℝ))=0 := by
      simp [UnequalPartialCountPayoff.rawWeight]
    simp only [hz,zero_mul,sub_zero,one_mul,FiniteLaw.expect_const]
    have hno : ¬UseTypical N H0 H1 Q.c Q.ξ B R V width (Q.marksLaw H0) (Q.marksLaw H1)
        (parameters b σ (PublicScenario.fallback N,1)) := by
      rw [UseTypical,fallback_weight]
      norm_num [parameters]
    simp [choice,publicRule,hno]
  · let C := PublicScenario.scenarioLaw Q N (H0,H1) (fun j => (b j:ℝ))
    have hi : Integrable (publicRule Q H0 H1 width b σ I)
        ((FiniteLaw.probabilityMeasure C).prod (volume : Measure unitInterval)) :=
      Integrable.of_bound hf.aestronglyMeasurable (1+|I|)
        (ae_of_all _ fun q => publicRule_bound Q H0 H1 width b σ I q)
    have hm : Measurable (fun u : unitInterval =>
        PublicScenario.draw Q N ((fun j => (b j:ℝ)),(H0,H1)) u) :=
      (PublicScenario.measurable_draw Q N).comp (measurable_const.prodMk measurable_id)
    have hmap := integral_map (μ := (volume : Measure unitInterval))
      (φ := fun u : unitInterval => PublicScenario.draw Q N ((fun j => (b j:ℝ)),(H0,H1)) u)
      hm.aemeasurable hf.aestronglyMeasurable
    rw [PublicScenario.draw_law] at hmap
    change (∫ u : unitInterval,publicRule Q H0 H1 width b σ I
      (PublicScenario.draw Q N ((fun j => (b j:ℝ)),(H0,H1)) u))=_
    rw [←hmap,integral_prod _ hi,LowBody.integral_probabilityMeasure]
    dsimp only [C]
    by_cases hN : 0< N
    · rw [PublicScenario.scenarioLaw_conditional Q N hN,FiniteLaw.expect_finiteMix]
      exact FiniteLaw.expect_congr _ (fun reg => conditionalScenario_rule Q hN H0 H1 width b σ I reg)
    · have hn : N=0 := by omega
      subst N
      have hz (reg : Bool) : UnequalPartialCountPayoff.rawWeight 0 H0 H1 Q.c Q.ξ B R V width
          (PublicScenario.e0 Q reg) Q.B0 reg true (Q.marksLaw H0) (Q.marksLaw H1) (fun j => (b j:ℝ))=0 := by
        simp [UnequalPartialCountPayoff.rawWeight]
      simp only [PublicScenario.scenarioLaw,Nat.not_lt_zero,dite_false,FiniteLaw.expect_dirac]
      rw [publicRule_branch,fallback_weight]
      simp only [hz,zero_mul,sub_zero,one_mul,FiniteLaw.expect_const]

theorem ae_every_public_joined_rank (N H0 H1 c : ℕ) {ξ B R U eps Rm width : ℝ}
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (side : Bool)
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hw : 0< width)
    (row : Row (ownCount H0 H1 side) R (U*(1+eps)) Rm)
    (hR : 0< R) (heps : 0< eps) (hRRm : R≤ Rm) (hV : U*(1+eps)<1)
    (hgap : (1-ξ)*B< R) (hfloor : U*(1+eps)< Rm)
    (j : Fin (ownCount H0 H1 side)) (price : Icc R U) :
    ∀ᵐ z : unitInterval ∂volume,
      ∀ p : Parameters N H0 R (U*(1+eps)) B,
      ∀ σ : Equiv.Perm (Fin (ownCount H0 H1 side)),∀ u : unitInterval,
      (if Sum.inr (σ.symm j)∈unequalSide N H0 H1 c ξ B R (U*(1+eps)) Rm width ν0 ν1 side
        (p,PrivatePartialSorting.reindexRow σ (noisyRow hR heps.le j price row z)) u
        then (1:ℝ) else 0)=
      if UseTypical N H0 H1 c ξ B R (U*(1+eps)) width ν0 ν1 p then
        (if regime p.1.1 then 0 else 1)
      else rankInclusion N H0 H1 c side j (inputAt (price,signal row) z) := by
  have hn (k : Fin (ownCount H0 H1 side)) : ∀ᵐ z : unitInterval ∂volume,
      k≠j → numericalEntry (noisyRow hR heps.le j price row z k)≠
        Hybrid.activeNoisyRealBid eps price z := by
    filter_upwards [Hybrid.ae_activeNoisyRealBid_ne eps price (numericalEntry (row k))
      heps.ne' (hR.trans_le price.2.1).ne'] with z hz hkj
    simpa [noisyRow,Function.update_of_ne hkj] using hz.symm
  filter_upwards [ae_all_iff.mpr hn] with z hz
  intro p σ u
  let price' : Icc R (U*(1+eps)) :=
    ⟨Hybrid.activeNoisyRealBid eps price z,Hybrid.activeNoisyRealBid_mem hR heps.le price z⟩
  have h := PrivatePartialSorting.joined_reindexed_rank N H0 H1 c ν0 ν1 side hξ hξ1 hw p
    (noisyRow hR heps.le j price row z) σ hR hRRm hV hgap hfloor j price'
    (by simp [noisyRow,price']) hz u
  have hr : rivalsAbove j (Hybrid.activeNoisyRealBid eps price z)
      (signal (noisyRow hR heps.le j price row z))=
      rivalsAbove j (Hybrid.activeNoisyRealBid eps price z) (signal row) := by
    ext k
    by_cases hk : k=j
    · subst k;simp [rivalsAbove]
    · simp [rivalsAbove,noisyRow,signal,Function.update_of_ne hk]
  simp only [rankInclusion,inputAt,price',hr] at h ⊢
  convert! h using 1

def samplerValue (Q : PublicScenario.Data) {N : ℕ} (H0 H1 : ℕ)
    {B R U eps Rm : ℝ} (width : ℝ) (side lowPresent : Bool)
    (b : Fin N → Icc (1:ℝ) B) (σ : WeakProbability.Law (Signal H0 R (U*(1+eps))))
    (hR : 0< R) (heps : 0≤ eps) (j : Fin (ownCount H0 H1 side)) (price : Icc R U)
    (row : Row (ownCount H0 H1 side) R (U*(1+eps)) Rm)
    (perm : unitInterval → Equiv.Perm (Fin (ownCount H0 H1 side))) (v : ℝ)
    (z publicSeed privateSeed : unitInterval) : ℝ :=
  (v-Hybrid.activeNoisyRealBid eps price z)*
    (if Sum.inr ((perm z).symm j)∈unequalSide N H0 H1 Q.c Q.ξ B R (U*(1+eps)) Rm width
      (Q.marksLaw H0) (Q.marksLaw H1) side
      (parameters b σ (choice Q H0 H1 (fun k => (b k:ℝ)) lowPresent publicSeed),
        PrivatePartialSorting.reindexRow (perm z) (noisyRow hR heps j price row z)) privateSeed
      then 1 else 0)

theorem sampler_ownNoise_integral (Q : PublicScenario.Data) {N : ℕ} (H0 H1 : ℕ)
    {B R U eps Rm : ℝ} (width : ℝ) (side lowPresent : Bool)
    (b : Fin N → Icc (1:ℝ) B) (σ : WeakProbability.Law (Signal H0 R (U*(1+eps))))
    (hξ : 0< Q.ξ) (hξ1 : Q.ξ≤1) (hw : 0< width)
    (hR : 0< R) (heps : 0< eps) (hRRm : R≤ Rm) (hV : U*(1+eps)<1)
    (hgap : (1-Q.ξ)*B< R) (hfloor : U*(1+eps)< Rm)
    (j : Fin (ownCount H0 H1 side)) (price : Icc R U)
    (row : Row (ownCount H0 H1 side) R (U*(1+eps)) Rm)
    (perm : unitInterval → Equiv.Perm (Fin (ownCount H0 H1 side))) (v : ℝ) :
    (∫ z : unitInterval,∫ publicSeed : unitInterval,∫ privateSeed : unitInterval,
      samplerValue Q H0 H1 width side lowPresent b σ hR heps.le j price row perm v
        z publicSeed privateSeed)=
    ∫ z : unitInterval,
      (IndependentCounts.bernoulli Q.θ Q.θ_nonneg Q.θ_le_one).expect (fun reg =>
        UnequalPartialOriginalIntegral.branchValue N H0 H1 Q.c (ξ:=Q.ξ) side reg
          (fun k => (b k:ℝ)) hR heps.le j price v
          (UnequalPartialCountPayoff.rawWeight N H0 H1 Q.c Q.ξ B R (U*(1+eps)) width
            (PublicScenario.e0 Q reg) Q.B0 reg lowPresent (Q.marksLaw H0) (Q.marksLaw H1)
              (fun k => (b k:ℝ))) row z) := by
  apply integral_congr_ae
  filter_upwards [ae_every_public_joined_rank N H0 H1 Q.c (Q.marksLaw H0) (Q.marksLaw H1)
    side hξ hξ1 hw row hR heps hRRm hV hgap hfloor j price,
    ae_actual_inclusion_eq_rank N H0 H1 Q.c side (fun k => (b k:ℝ)) row
      ⟨hξ.le,hξ1⟩ (fun k => (b k).2) hR heps hRRm hV hgap hfloor j price] with z hz hr
  have he (a u : unitInterval) : samplerValue Q H0 H1 width side lowPresent b σ hR heps.le
      j price row perm v z a u=(v-Hybrid.activeNoisyRealBid eps price z)*
        publicRule Q H0 H1 width b σ (rankInclusion N H0 H1 Q.c side j
          (inputAt (price,signal row) z)) (choice Q H0 H1 (fun k => (b k:ℝ)) lowPresent a) := by
    unfold samplerValue
    rw [hz]
    rfl
  simp_rw [he]
  simp only [integral_const,probReal_univ,one_smul]
  rw [integral_const_mul,public_rule_integral,←FiniteLaw.expect_const_mul]
  apply FiniteLaw.expect_congr
  intro reg
  unfold UnequalPartialOriginalIntegral.branchValue
  rw [hr]

end FCAppendix.Affine.Tail04.JoinedPartialPublicIntegral
