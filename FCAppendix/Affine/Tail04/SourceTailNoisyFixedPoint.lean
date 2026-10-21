import FCAppendix.Affine.Tail04.FiniteTailNoisyGame
import FCAppendix.Affine.Tail04.JointNoisyCompactness
import FCAppendix.Affine.Tail04.OriginalActiveComponents

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceTailNoisyFixedPoint
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional OriginalValues FiniteTailNoisyGame CompactSourceBidLaws Hybrid
open scoped BigOperators

def tailMass (P : ValueParameters) (t : ℝ) : ℝ :=
  activeMass P.theta*P.zeta*powerTail P.M 10 t

lemma tailMass_nonneg (P : ValueParameters) (t : ℝ) (ht : P.M≤ t) : 0≤ tailMass P t :=
  OriginalValues.tailMass_nonneg P t ht

def originalCategories (P : ValueParameters) (t : ℝ) (ht : P.M< t) : FiniteLaw (Fin 4) where
  mass := ![lowMass P.theta,P.bulkWeight+P.truncatedTailWeight t,
    (partialMass+tailMass P t)/2,(partialMass+tailMass P t)/2]
  nonneg := by
    intro k
    fin_cases k
    · exact P.low_mass_pos.le
    · exact (add_pos P.bulkWeight_pos (P.truncatedTailWeight_pos t ht)).le
    · exact div_nonneg (add_nonneg (by norm_num [partialMass]) (tailMass_nonneg P t ht.le)) (by norm_num)
    · exact div_nonneg (add_nonneg (by norm_num [partialMass]) (tailMass_nonneg P t ht.le)) (by norm_num)
  total := by
    simp only [Fin.sum_univ_succ,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.sum_univ_zero,add_zero]
    rw [P.component_weight_sum]
    unfold tailMass
    linarith [mass_sum P.theta]

def originalBulkShare (P : ValueParameters) (t : ℝ) (ht : P.M< t) : unitInterval :=
  ⟨P.bulkWeight/(P.bulkWeight+P.truncatedTailWeight t),by
    have hb := P.bulkWeight_pos
    have ht' := P.truncatedTailWeight_pos t ht
    exact ⟨div_nonneg hb.le (add_pos hb ht').le,
      (div_le_one (add_pos hb ht')).mpr (le_add_of_nonneg_right ht'.le)⟩⟩

def originalUpperShare (P : ValueParameters) (t : ℝ) (ht : P.M< t) : unitInterval :=
  ⟨tailMass P t/(partialMass+tailMass P t),by
    have hh : 0< partialMass := by norm_num [partialMass]
    have hu := tailMass_nonneg P t ht.le
    exact ⟨div_nonneg hu (add_pos_of_pos_of_nonneg hh hu).le,
      (div_le_one (add_pos_of_pos_of_nonneg hh hu)).mpr (le_add_of_nonneg_left hh.le)⟩⟩

def installOriginal (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) : Data :=
  { D with bulkShare:=originalBulkShare P t ht
           upperShare:=originalUpperShare P t ht
           categories:=originalCategories P t ht }

def valueLo (P : ValueParameters) : Fin 3 → ℝ := ![P.vA-P.w,P.M,2-P.w]
def valueHi (P : ValueParameters) (t : ℝ) : Fin 3 → ℝ := ![P.vA+P.w,t,2+P.w]
def bidLo (D : Data) : Fin 3 → ℝ := ![1,1,D.R]
def bidHi (D : Data) : Fin 3 → ℝ := ![1+D.u,D.U,D.Up]

def originalValueLaw (P : ValueParameters) (t : ℝ) (ht : P.M< t) :
    ∀ i : Fin 3,Measure (ActiveValue (valueLo P i) (valueHi P t i)) := by
  intro i
  refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>Fin.cases ?_ (fun n=>Fin.elim0 n) k) j) i
  · exact P.originalBulkLaw
  · exact P.originalTruncatedTailLaw t ht
  · exact P.originalPartialLaw

instance originalValueLaw_probability (P : ValueParameters) (t : ℝ) (ht : P.M< t) (i : Fin 3) :
    IsProbabilityMeasure (originalValueLaw P t ht i) := by
  have hi : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases hi with hi | hi | hi <;> subst i
  · exact ValueParameters.originalBulkLaw_probability P
  · exact ValueParameters.originalTruncatedTailLaw_probability P t ht
  · exact ValueParameters.originalPartialLaw_probability P

lemma bidLo_pos (D : Data) (i : Fin 3) : 0< bidLo D i := by
  fin_cases i
  · norm_num [bidLo]
  · norm_num [bidLo]
  · exact D.hR

lemma bidLo_le_hi (D : Data) (i : Fin 3) : bidLo D i≤ bidHi D i := by
  fin_cases i
  · dsimp [bidLo,bidHi]
    linarith [D.hu]
  · exact D.hU
  · exact D.hRUp

instance baseBid_nonempty (D : Data) (i : Fin 3) :
    Nonempty (ActiveBaseBid (bidLo D i) (bidHi D i)) :=
  ⟨⟨bidLo D i,le_rfl,bidLo_le_hi D i⟩⟩

abbrev JointProfile (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) :=
  Profile (fun i => ActiveValue (valueLo P i) (valueHi P t i))
    (fun i => ActiveBaseBid (bidLo D i) (bidHi D i)) (originalValueLaw P t ht)

def bidLaws (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
    (π : JointProfile D P t ht) : D.BidLaws :=
  (bidMarginal (π 0).1,bidMarginal (π 1).1,bidMarginal (π 2).1)

lemma continuous_bidLaws (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) :
    Continuous (bidLaws D P t ht) :=
  (continuous_bidMarginal.comp (continuous_subtype_val.comp (continuous_apply 0))).prodMk
    ((continuous_bidMarginal.comp (continuous_subtype_val.comp (continuous_apply 1))).prodMk
      (continuous_bidMarginal.comp (continuous_subtype_val.comp (continuous_apply 2))))

def payoff (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ) :
    ∀ i : Fin 3,JointProfile D P t ht×
      (ActiveValue (valueLo P i) (valueHi P t i)×ActiveBaseBid (bidLo D i) (bidHi D i)) → ℝ := by
  intro i
  refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>Fin.cases ?_ (fun n=>Fin.elim0 n) k) j) i
  · exact fun p => (installOriginal D P t ht).activeExpected N
      (bidLaws D P t ht p.1,((p.2.1:ℝ),extendBid D.huU p.2.2))
  · exact fun p => (installOriginal D P t ht).activeExpected N
      (bidLaws D P t ht p.1,((p.2.1:ℝ),p.2.2))
  · exact fun p => (installOriginal D P t ht).partialExpected N
      (bidLaws D P t ht p.1,((p.2.1:ℝ),p.2.2))

theorem continuous_payoff (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ) (i : Fin 3) :
    Continuous (payoff D P t ht N i) := by
  have hi : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases hi with hi | hi | hi <;> subst i
  · exact ((installOriginal D P t ht).continuous_activeExpected N).comp
      (((continuous_bidLaws D P t ht).comp continuous_fst).prodMk
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
          ((continuous_extendBid D.huU).comp (continuous_snd.comp continuous_snd))))
  · exact ((installOriginal D P t ht).continuous_activeExpected N).comp
      (((continuous_bidLaws D P t ht).comp continuous_fst).prodMk
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
          (continuous_snd.comp continuous_snd)))
  · exact ((installOriginal D P t ht).continuous_partialExpected N).comp
      (((continuous_bidLaws D P t ht).comp continuous_fst).prodMk
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
          (continuous_snd.comp continuous_snd)))

theorem exists_original_joint_noisy_law (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ) :
    ∃ (π : JointProfile D P t ht)
      (σ : ∀ i : Fin 3,Kernel (ActiveValue (valueLo P i) (valueHi P t i))
        (ActiveBaseBid (bidLo D i) (bidHi D i))),
      (∀ i,IsMarkovKernel (σ i)) ∧
      (∀ i,originalValueLaw P t ht i ⊗ₘ σ i=((π i).1 : Measure _)) ∧
      (∀ i,AllActionOptimal (π i) (fun x => payoff D P t ht N i (π,x))) ∧
      (∀ i,∀ᵐ v ∂originalValueLaw P t ht i,∀ᵐ b ∂σ i v,
        ∀ b' : ActiveBaseBid (bidLo D i) (bidHi D i),
          payoff D P t ht N i (π,(v,b'))≤ payoff D P t ht N i (π,(v,b))) :=
  exists_population_laws (fun i => ActiveValue (valueLo P i) (valueHi P t i))
    (fun i => ActiveBaseBid (bidLo D i) (bidHi D i)) (originalValueLaw P t ht)
      (payoff D P t ht N) (continuous_payoff D P t ht N)

def atNoise (D : Data) (eps : ℝ) (heps : 0< eps) (hsmall : eps< D.eps) : Data :=
  { D with eps:=eps
           heps:=heps
           hRp:=by
             have hUp : 0≤ D.Up := D.hR.le.trans D.hRUp
             have hh := mul_le_mul_of_nonneg_left (show 1+eps≤1+D.eps by linarith) hUp
             exact hh.trans_lt D.hRp
           hgap:=by
             have hκ : 0≤1-D.ξ := sub_nonneg.mpr D.hξ1.le
             have hU : 0≤ D.U := (by norm_num : (0:ℝ)≤1).trans D.hU
             have hh := mul_le_mul_of_nonneg_left
               (mul_le_mul_of_nonneg_left (show 1+eps≤1+D.eps by linarith) hU) hκ
             exact hh.trans_lt D.hgap
           hUF:=by
             have hU : 0≤ D.U := (by norm_num : (0:ℝ)≤1).trans D.hU
             exact (mul_le_mul_of_nonneg_left (show 1+eps≤1+D.eps by linarith) hU).trans D.hUF }

def sequencePayoff (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ)
    (eps : unitInterval) : ∀ i : Fin 3,JointProfile D P t ht×
      (ActiveValue (valueLo P i) (valueHi P t i)×ActiveBaseBid (bidLo D i) (bidHi D i)) → ℝ :=
  if h : 0<(eps:ℝ) ∧ (eps:ℝ)< D.eps then payoff (atNoise D eps h.1 h.2) P t ht N else fun _ _ => 0

lemma sequencePayoff_eq (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ)
    (eps : unitInterval) (heps : 0<(eps:ℝ)) (hsmall : (eps:ℝ)< D.eps) :
    sequencePayoff D P t ht N eps=payoff (atNoise D eps heps hsmall) P t ht N := by
  unfold sequencePayoff
  rw [dif_pos (show 0<(eps:ℝ) ∧ (eps:ℝ)<D.eps from ⟨heps,hsmall⟩)]

lemma continuous_sequencePayoff (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ)
    (eps : unitInterval) (i : Fin 3) : Continuous (sequencePayoff D P t ht N eps i) := by
  unfold sequencePayoff
  split_ifs with h
  · exact continuous_payoff (atNoise D eps h.1 h.2) P t ht N i
  · exact continuous_const

theorem exists_original_joint_noisy_sequence (D : Data) (hbudget : D.eps≤1)
    (P : ValueParameters) (t : ℝ) (ht : P.M< t) (N : ℕ) :
    ∃ (eps : ℕ → unitInterval) (π : ℕ → JointProfile D P t ht) (π₀ : JointProfile D P t ht),
      (∀ j,0<(eps j:ℝ) ∧ (eps j:ℝ)< D.eps) ∧
      Tendsto eps atTop (𝓝 0) ∧
      (∀ j,∃ σ : ∀ i : Fin 3,Kernel (ActiveValue (valueLo P i) (valueHi P t i))
          (ActiveBaseBid (bidLo D i) (bidHi D i)),
        (∀ i,IsMarkovKernel (σ i)) ∧
        (∀ i,originalValueLaw P t ht i ⊗ₘ σ i=((π j i).1 : Measure _)) ∧
        (∀ i,AllActionOptimal (π j i) (fun x => sequencePayoff D P t ht N (eps j) i (π j,x))) ∧
        (∀ i,∀ᵐ v ∂originalValueLaw P t ht i,∀ᵐ b ∂σ i v,
          ∀ b' : ActiveBaseBid (bidLo D i) (bidHi D i),
            sequencePayoff D P t ht N (eps j) i (π j,(v,b'))≤
              sequencePayoff D P t ht N (eps j) i (π j,(v,b)))) ∧
      Tendsto π atTop (𝓝 π₀) ∧
      (∀ i,Tendsto (fun j => activeUniversalNoisyLaw (bidLo_pos D i) (bidLo_le_hi D i)
          (originalValueLaw P t ht i) (eps j,π j i)) atTop
        (𝓝 (activeUniversalNoisyLaw (bidLo_pos D i) (bidLo_le_hi D i)
          (originalValueLaw P t ht i) (0,π₀ i)))) :=
  exists_joint_noisy_compact_sequence (valueLo P) (valueHi P t) (bidLo D) (bidHi D)
    (bidLo_pos D) (bidLo_le_hi D) (originalValueLaw P t ht)
    (sequencePayoff D P t ht N)
    (fun eps _ i => continuous_sequencePayoff D P t ht N eps i) D.eps D.heps hbudget

end FCAppendix.Affine.Tail04.SourceTailNoisyFixedPoint
