import FCAppendix.Affine.UniformFinite.FiniteExperiment
import FCAppendix.Affine.UniformFinite.SourcePayoffContinuity
import FCAppendix.Affine.UniformFinite.ActualBoundaryProbability
import FCAppendix.Affine.UniformFinite.AtomCrossingAlgebra
import FCAppendix.Affine.UniformFinite.NoisyFixedPoint

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

namespace ActualSurplus
open Uniform05

def localUnderflow (N : ℕ) (kind : Fin N→ Fin 3) : Prop :=
  LowBody.hitCount (fun k : Fin 3=> k≠2) kind < Uniform07.capacity (N+1)

lemma lower_plus_upperZero {N : ℕ} (kind : Fin N→ Fin 3) :
    ActualBoundary.lowerKindCount kind+ActualBoundary.upperZeroCount kind =
      LowBody.hitCount (fun k : Fin 3=> k≠2) kind := by
  unfold ActualBoundary.lowerKindCount ActualBoundary.upperZeroCount LowBody.hitCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  generalize h : kind j=k
  fin_cases k <;> norm_num [h] <;> decide

lemma focalRow_lowerCard {N : ℕ} (kind : Fin N→ Fin 3) :
    (focalRow kind).lower.card=ActualBoundary.lowerKindCount kind+1 := by
  rw [focalRow, ActualBoundary.countRow_lowerCard]
  change LowBody.hitCount (fun k : Fin 3=>k=0) (Fin.cons 0 kind)=
    LowBody.hitCount (fun k : Fin 3=>k=0) kind+1
  rw [LowBody.hitCount_cons]
  simp only [if_true]
  omega

lemma focalRow_upperZero {N : ℕ} (kind : Fin N→ Fin 3) :
    (focalRow kind).upper0=ActualBoundary.upperZeroCount kind := by
  rw [focalRow, ActualBoundary.countRow_upperZero]
  change LowBody.hitCount (fun k : Fin 3=>k=1) (Fin.cons 0 kind)=
    LowBody.hitCount (fun k : Fin 3=>k=1) kind
  rw [LowBody.hitCount_cons]
  simp only [show (0:Fin 3)≠1 by decide, if_false, zero_add]

lemma focalRow_focal_mem {N : ℕ} (kind : Fin N→ Fin 3) :
    (0:Fin (N+1))∈(focalRow kind).lower := by
  simp [focalRow, Source.countRowOfKind]

theorem L_residuals {N : ℕ} (kind : Fin N→ Fin 3)
    (hM : 2*Uniform07.capacity (N+1)< N+1) (hL : localUnderflow N kind) :
    Source.residual (focalRow kind) 0=(focalRow kind).lower.card ∧
    Source.residual (focalRow kind) 1=0 := by
  have hlow := focalRow_lowerCard kind
  have hupp := focalRow_upperZero kind
  have hsum := lower_plus_upperZero kind
  have hpart := (focalRow kind).partition
  change LowBody.hitCount (fun k : Fin 3=> k≠2) kind< Uniform07.capacity (N+1) at hL
  have hl : (focalRow kind).lower.card≤ Uniform07.capacity (N+1)-(focalRow kind).upper0 := by
    omega
  have hr : Uniform07.capacity (N+1)≤(focalRow kind).upper1 := by omega
  constructor
  · simpa only [Source.residual, Source.upperCount, if_true] using min_eq_left hl
  · simp [Source.residual, Source.upperCount, Nat.sub_eq_zero_of_le hr]

theorem L_probability (i : Row) (N : ℕ) (hc : 0< Uniform07.capacity (N+1)) :
    (categoryRowLaw i N).prob (localUnderflow N) =
      AtomEvents.lowerEvent (t i) (t_pos i).le (t_lt_one i).le (N+1) := by
  have hp : (categoryLaw i).prob (fun k : Fin 3=> k≠2)=(1+t i)/2 := by
    rw [FiniteLaw.prob_eq_expect]
    unfold FiniteLaw.expect categoryLaw
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    norm_num [Fin.ext_iff]
    ring
  have he (kind : Fin N→ Fin 3) : localUnderflow N kind ↔
      LowBody.hitCount (fun k : Fin 3=> k≠2) kind≤ Uniform07.capacity (N+1)-1 := by
    unfold localUnderflow
    omega
  rw [FiniteLaw.prob_eq_expect]
  simp only [he]
  change (CommonList.iid (categoryLaw i) N).expect _=_
  have hh := LowBody.expect_hitCount_binomial (categoryLaw i) (fun k : Fin 3=>k≠2) N
    (fun n=>if n≤Uniform07.capacity (N+1)-1 then (1:ℝ) else 0)
  rw [hh]
  unfold AtomEvents.lowerEvent
  conv_rhs => rw [FiniteLaw.prob_eq_expect]
  change ActualBoundary.binomialMean N ((categoryLaw i).prob (fun k : Fin 3=>k≠2)) _ _
    (fun n=>if n≤Uniform07.capacity (N+1)-1 then (1:ℝ) else 0) =
    ActualBoundary.binomialMean (N+1-1) ((1+t i)/2) _ _
      (fun n=>if n≤Uniform07.capacity (N+1)-1 then (1:ℝ) else 0)
  rw [Nat.add_sub_cancel]
  congr 1

theorem rowPayoff_on_L (i : Row) {N : ℕ} (G : RestrictedLaw i)
    (kind : Fin N→ Fin 3) (v own : ℝ) (rivals : Fin N→ Bid i)
    (hM : 2*Uniform07.capacity (N+1)< N+1)
    (hL : localUnderflow N kind) (hb : 0< own) :
    rowPayoff i G (focalRow kind) v (focalBids i kind own rivals) 0 = v-own := by
  obtain ⟨hl,hr⟩ := L_residuals kind hM hL
  have hf := focalRow_focal_mem kind
  have hcard : 0<(focalRow kind).lower.card := Finset.card_pos.mpr ⟨0,hf⟩
  rw [ActualAtoms.rowPayoff_eq_pure_of_right_zero i G (focalRow kind) v _ 0 hf
    (by omega) hr]
  have hinc := (Source.lowerTemplate (focalRow kind)).selection_contains_left
    (kappa_range i).1 (Source.lowerBids (focalRow kind) (focalBids i kind own rivals)) 0 hf
    (by simpa only [Source.lowerBids_of_mem _ _ hf, focalBids_zero] using hb)
    (by simpa only [Source.lowerTemplate] using hl.ge)
  have hemp := (Source.lowerTemplate (focalRow kind)).selection_empty_right
    (kappa i) (Source.lowerBids (focalRow kind) (focalBids i kind own rivals)) hr
  simp [LowBody.purePayoff, LowBody.focalCopy, hinc, hemp,
    Source.lowerBids_of_mem _ _ hf, focalBids_zero, Fin.ext_iff]

lemma pairPayoff_le_surplus {M : ℕ} (i : Row) (v own : ℝ)
    (hb0 : 0≤ own) (hbv : own≤ v) (a : Fin M) (P : Allocation M) :
    pairPayoff (eta i) v own a P≤ v-own := by
  have he := (eta_range i).1
  by_cases h0 : a∈P.1 <;> by_cases h1 : a∈P.2 <;>
    simp [pairPayoff, Literal.firstCopy, Literal.duplicateCopy,
      WeightedSampling.indicator, h0, h1] <;> nlinarith

lemma pairPayoff_nonneg {M : ℕ} (i : Row) (v own : ℝ)
    (hb0 : 0≤ own) (hcost : (1+eta i)*own≤ v) (a : Fin M) (P : Allocation M) :
    0≤ pairPayoff (eta i) v own a P := by
  have he := (eta_range i).1
  by_cases h0 : a∈P.1 <;> by_cases h1 : a∈P.2 <;>
    simp [pairPayoff, Literal.firstCopy, Literal.duplicateCopy,
      WeightedSampling.indicator, h0, h1] <;> nlinarith

lemma rowPayoff_le_surplus {M : ℕ} [NeZero M] (i : Row) (G : RestrictedLaw i)
    (row : Source.CountRow M) (v : ℝ) (b : Fin M→ℝ) (a : Fin M)
    (hb0 : 0≤ b a) (hbv : b a≤ v) : rowPayoff i G row v b a≤ v-b a :=
  FiniteLaw.expect_le_const _ (fun P=> pairPayoff_le_surplus i v (b a) hb0 hbv a P)

lemma rowPayoff_nonneg {M : ℕ} [NeZero M] (i : Row) (G : RestrictedLaw i)
    (row : Source.CountRow M) (v : ℝ) (b : Fin M→ℝ) (a : Fin M)
    (hb0 : 0≤ b a) (hcost : (1+eta i)*b a≤ v) : 0≤ rowPayoff i G row v b a :=
  FiniteLaw.expect_nonneg _ (fun P=> pairPayoff_nonneg i v (b a) hb0 hcost a P)

def cappedFocalBids {N : ℕ} (i : Row) (kind : Fin N→ Fin 3)
    (own : Bid i) (rivals : Fin N→ Bid i) : Fin (N+1)→ Bid i :=
  Fin.cons own (fun j => if kind j=0 then rivals j else ⟨0, le_rfl, (cap_pos i).le⟩)

lemma cappedFocalBids_val {N : ℕ} (i : Row) (kind : Fin N→ Fin 3)
    (own : Bid i) (rivals : Fin N→ Bid i) :
    (fun a => (cappedFocalBids i kind own rivals a:ℝ))=focalBids i kind own rivals := by
  funext a
  refine Fin.cases ?_ (fun j=>?_) a
  · rfl
  · by_cases hk : kind j=0 <;> simp [cappedFocalBids, focalBids, hk]

lemma continuous_cappedFocalBids {N : ℕ} (i : Row) (kind : Fin N→ Fin 3) :
    Continuous (fun p : Bid i×(Fin N→ Bid i) => cappedFocalBids i kind p.1 p.2) := by
  apply continuous_pi
  intro a
  refine Fin.cases ?_ (fun j=>?_) a
  · exact continuous_fst
  · by_cases hk : kind j=0
    · simpa [cappedFocalBids, hk, Function.comp_def] using (continuous_apply j).comp continuous_snd
    · simp only [cappedFocalBids, Fin.cons_succ, if_neg hk]
      exact continuous_const

lemma measurable_noisy_row {N : ℕ} (i : Row) (eps : unitInterval) (pi : Joint i)
    (v : Value i) (q : unitInterval) (kind : Fin N→ Fin 3) :
    Measurable (fun p : (Fin N→ Bid i)×unitInterval =>
      rowPayoff i (restrictedLaw i (eps,pi)) (focalRow kind) v
        (focalBids i kind (noisyBid i (eps,((v,q),p.2)):ℝ) p.1) 0) := by
  have hmap : @Measurable ((Fin N→Bid i)×unitInterval) (Noisy.Sample i N) _ _
      (fun p => (((pi,(v,q)) : Noisy.Parameter i),p)) :=
    measurable_const.prodMk measurable_id
  convert! (Noisy.measurable_rowFunction i eps kind).comp hmap using 1

lemma integrable_noisy_joint {N : ℕ} (i : Row) (eps : unitInterval) (pi : Joint i)
    (v : Value i) (q : unitInterval) (kind : Fin N→ Fin 3) :
    Integrable (fun p : (Fin N→ Bid i)×unitInterval =>
      rowPayoff i (restrictedLaw i (eps,pi)) (focalRow kind) v
        (focalBids i kind (noisyBid i (eps,((v,q),p.2)):ℝ) p.1) 0)
      ((rowLaw N (restrictedLaw i (eps,pi)).bidLaw : Measure (Fin N→ Bid i)).prod volume) :=
  Integrable.of_bound (measurable_noisy_row i eps pi v q kind).aestronglyMeasurable
    (3*(v:ℝ)) (ae_of_all _ (fun p => by
      simpa only [Real.norm_eq_abs] using noisyRowPayoff_bound i eps pi v q p.2 kind p.1))

lemma integrable_noisy_own {N : ℕ} (i : Row) (eps : unitInterval) (pi : Joint i)
    (v : Value i) (q : unitInterval) (kind : Fin N→ Fin 3) (rivals : Fin N→ Bid i) :
    Integrable (fun z : unitInterval => rowPayoff i (restrictedLaw i (eps,pi))
      (focalRow kind) v (focalBids i kind (noisyBid i (eps,((v,q),z)):ℝ) rivals) 0) := by
  have hm := (measurable_noisy_row i eps pi v q kind).comp
    ((measurable_const (a := rivals)).prodMk measurable_id)
  exact Integrable.of_bound hm.aestronglyMeasurable (3*(v:ℝ))
    (ae_of_all _ (fun z=> by
      simpa only [Real.norm_eq_abs] using noisyRowPayoff_bound i eps pi v q z kind rivals))

def comparisonBid (i : Row) (v : Value i) : ℝ := max ((v:ℝ)/2) (floorBid i v)

lemma comparisonBid_feasible (i : Row) (v : Value i) :
    comparisonBid i v∈Icc (floorBid i v) (hiBid i v) ∧ comparisonBid i v≤ chi*(v:ℝ) := by
  have hf := floor_le_chi_mul i v.property.1 (t_pos i).le
  have hhalf : (v:ℝ)/2≤ chi*(v:ℝ) := by
    have hχ : (1:ℝ)/2≤ chi := by norm_num [chi]
    nlinarith [v.property.1]
  have hχv : chi*(v:ℝ)≤(v:ℝ) := by norm_num [chi]; linarith [v.property.1]
  have hχcap : chi*(v:ℝ)≤ cap i :=
    (mul_le_mul_of_nonneg_left v.property.2 (by norm_num [chi])).trans (chi_t_lt_cap i).le
  refine ⟨⟨le_max_right _ _, ?_⟩,max_le hhalf hf⟩
  exact (max_le hhalf hf).trans (le_min hχv hχcap)

lemma comparisonBid_pos (i : Row) (v : Value i) (hv : 0<(v:ℝ)) :
    0< comparisonBid i v := (half_pos hv).trans_le (le_max_left _ _)

def comparisonChoice (i : Row) (v : Value i) : unitInterval :=
  choiceForBid i v (comparisonBid i v)

lemma noisy_comparison_bounds (i : Row) (eps : unitInterval)
    (heps : (eps:ℝ)<1) (v : Value i) (hv : 0<(v:ℝ)) (z : unitInterval) :
    0<(noisyBid i (eps,((v,comparisonChoice i v),z)):ℝ) ∧
      (noisyBid i (eps,((v,comparisonChoice i v),z)):ℝ)≤(chi+(eps:ℝ))*(v:ℝ) := by
  have hbase : (baseBid i (v,comparisonChoice i v):ℝ)=comparisonBid i v :=
    choiceForBid_exact i v hv _ (comparisonBid_feasible i v).1
  have hnoise0 : 0≤ floorBid i v+width i v*(z:ℝ) := by
    exact add_nonneg (floor_nonneg i v) (mul_nonneg (width_nonneg i v) z.property.1)
  constructor
  · rw [noisy_bid_from_base, hbase]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr heps) (comparisonBid_pos i v hv))
      (mul_nonneg eps.property.1 hnoise0)
  · have hb := (abs_le.mp (physical_base_error i eps (v,comparisonChoice i v) z)).2
    rw [hbase] at hb
    nlinarith [(comparisonBid_feasible i v).2]

theorem expectedUtility_comparison_lower (i : Row) (N : ℕ)
    (hM : 2*Uniform07.capacity (N+1)< N+1) (hc : 0< Uniform07.capacity (N+1))
    (eps : unitInterval) (heps : (eps:ℝ)<1)
    (hcost : (1+eta i)*(chi+(eps:ℝ))≤1)
    (pi : Joint i) (v : Value i) (hv : 0<(v:ℝ)) :
    (1-chi-(eps:ℝ))*(v:ℝ)*
      AtomEvents.lowerEvent (t i) (t_pos i).le (t_lt_one i).le (N+1) ≤
        expectedUtility i N eps pi v (comparisonChoice i v) := by
  let G := restrictedLaw i (eps,pi)
  let C := (1-chi-(eps:ℝ))*(v:ℝ)
  have hpoint (kind : Fin N→ Fin 3) (rivals : Fin N→ Bid i) (z : unitInterval) :
      (if localUnderflow N kind then C else 0) ≤
        rowPayoff i G (focalRow kind) v
          (focalBids i kind (noisyBid i (eps,((v,comparisonChoice i v),z)):ℝ) rivals) 0 := by
    have hb := noisy_comparison_bounds i eps heps v hv z
    by_cases hL : localUnderflow N kind
    · rw [if_pos hL, rowPayoff_on_L i G kind v _ rivals hM hL hb.1]
      dsimp only [C]
      nlinarith
    · rw [if_neg hL]
      apply rowPayoff_nonneg i G (focalRow kind) v _ 0
      · simpa only [focalBids_zero] using hb.1.le
      · simp only [focalBids_zero]
        have hη : 0≤1+eta i := by linarith [(eta_range i).1]
        have hc1 := mul_le_mul_of_nonneg_left hb.2 hη
        have hc2 := mul_le_mul_of_nonneg_right hcost v.property.1
        nlinarith
  have hrow (kind : Fin N→ Fin 3) :
      (if localUnderflow N kind then C else 0) ≤
        ∫rivals : Fin N→ Bid i, (∫z : unitInterval,
          rowPayoff i G (focalRow kind) v
            (focalBids i kind (noisyBid i (eps,((v,comparisonChoice i v),z)):ℝ) rivals) 0)
        ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)) := by
    have hj := integrable_noisy_joint i eps pi v (comparisonChoice i v) kind
    have hh := integral_mono (integrable_const (if localUnderflow N kind then C else 0))
      hj.integral_prod_left (fun rivals=> by
        have hown := integral_mono
          (integrable_const (if localUnderflow N kind then C else 0))
          (integrable_noisy_own i eps pi v (comparisonChoice i v) kind rivals)
          (hpoint kind rivals)
        simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hown)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh
  have hcat := (categoryRowLaw i N).expect_mono hrow
  have he : (categoryRowLaw i N).expect (fun kind=> if localUnderflow N kind then C else 0) =
      C*(categoryRowLaw i N).prob (localUnderflow N) := by
    calc
      _ = (categoryRowLaw i N).expect
          (fun kind=> C*(if localUnderflow N kind then (1:ℝ) else 0)) := by
        apply FiniteLaw.expect_congr
        intro kind
        split_ifs <;> simp
      _ = _ := by rw [FiniteLaw.expect_const_mul, ← FiniteLaw.prob_eq_expect]
  rw [he, L_probability i N hc] at hcat
  exact hcat

theorem expectedUtility_le_min_surplus (i : Row) (N : ℕ) (eps : unitInterval)
    (pi : Joint i) (v : Value i) (q : unitInterval) :
    expectedUtility i N eps pi v q ≤
      (v:ℝ)-(noisyBid i (eps,((v,q),0)):ℝ) := by
  let G := restrictedLaw i (eps,pi)
  apply (categoryRowLaw i N).expect_le_const
  intro kind
  have hbound (rivals : Fin N→ Bid i) (z : unitInterval) :
      rowPayoff i G (focalRow kind) v
        (focalBids i kind (noisyBid i (eps,((v,q),z)):ℝ) rivals) 0 ≤
          (v:ℝ)-(noisyBid i (eps,((v,q),0)):ℝ) := by
    have hb := noisyRealBid_bounds i eps v q z
    have hmin : (noisyBid i (eps,((v,q),0)):ℝ)≤(noisyBid i (eps,((v,q),z)):ℝ) := by
      change noisyRealBid i eps v q 0≤ noisyRealBid i eps v q z
      unfold noisyRealBid
      have hw := width_nonneg i v
      have hn := mul_nonneg (mul_nonneg hw eps.property.1) z.property.1
      norm_num only [show ((0:unitInterval):ℝ)=0 by rfl, mul_zero, add_zero]
      nlinarith
    have hh := rowPayoff_le_surplus i G (focalRow kind) v
      (focalBids i kind (noisyBid i (eps,((v,q),z))) rivals) 0
      (by simpa only [focalBids_zero] using (noisyBid i (eps,((v,q),z))).property.1)
      (by convert! hb.2.trans (min_le_left _ _) using 1)
    simpa only [focalBids_zero] using hh.trans (sub_le_sub_left hmin _)
  have hj := integrable_noisy_joint i eps pi v q kind
  have hh := integral_mono hj.integral_prod_left (integrable_const
      ((v:ℝ)-(noisyBid i (eps,((v,q),0)):ℝ))) (fun rivals=> by
    have hown := integral_mono (integrable_noisy_own i eps pi v q kind rivals)
      (integrable_const ((v:ℝ)-(noisyBid i (eps,((v,q),0)):ℝ))) (hbound rivals)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hown)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh

theorem supported_physical_surplus (i : Row) (N : ℕ)
    (hM : 2*Uniform07.capacity (N+1)< N+1) (hc : 0< Uniform07.capacity (N+1))
    (eps : unitInterval)
    (heps : (eps:ℝ)≤(1-chi)*
      AtomEvents.lowerEvent (t i) (t_pos i).le (t_lt_one i).le (N+1)/4)
    (hcost : (1+eta i)*(chi+(eps:ℝ))≤1)
    (pi : Joint i) (v : Value i) (hv : 0<(v:ℝ)) (q : unitInterval)
    (hopt : expectedUtility i N eps pi v (comparisonChoice i v)≤ expectedUtility i N eps pi v q)
    (z : unitInterval) :
    (1-chi)*(noisyBid i (eps,((v,q),z)):ℝ)*
      AtomEvents.lowerEvent (t i) (t_pos i).le (t_lt_one i).le (N+1)/2 ≤
        (v:ℝ)-(noisyBid i (eps,((v,q),z)):ℝ) := by
  let L := AtomEvents.lowerEvent (t i) (t_pos i).le (t_lt_one i).le (N+1)
  have hL0 : 0≤ L := FiniteLaw.prob_nonneg _ _
  have hL1 : L≤1 := FiniteLaw.prob_le_one _ _
  have heps1 : (eps:ℝ)<1 := by
    have hχ : chi=69/100 := rfl
    change (eps:ℝ)≤(1-chi)*L/4 at heps
    nlinarith
  have hlo := expectedUtility_comparison_lower i N hM hc eps heps1 hcost pi v hv
  have hhi := expectedUtility_le_min_surplus i N eps pi v q
  have hrange : (noisyBid i (eps,((v,q),z)):ℝ)≤
      (noisyBid i (eps,((v,q),0)):ℝ)+(eps:ℝ)*(v:ℝ) := by
    have hdiff : (noisyBid i (eps,((v,q),z)):ℝ)-(noisyBid i (eps,((v,q),0)):ℝ) =
        (eps:ℝ)*width i v*(z:ℝ) := by
      change noisyRealBid i eps v q z-noisyRealBid i eps v q 0=_
      unfold noisyRealBid
      ring
    have h1 := mul_le_mul_of_nonneg_left z.property.2
      (mul_nonneg eps.property.1 (width_nonneg i v))
    have h2 := mul_le_mul_of_nonneg_left (width_le_value i v) eps.property.1
    nlinarith
  exact CopyAlgebra.noisy_physical_surplus chi L (eps:ℝ) v
    (noisyBid i (eps,((v,q),z)):ℝ) (noisyBid i (eps,((v,q),0)):ℝ)
    (expectedUtility i N eps pi v q) (by norm_num [chi]) hL0 hL1 eps.property.1 heps
    v.property.1 ((noisyRealBid_bounds i eps v q z).2.trans (min_le_left _ _)) hrange
    (hlo.trans hopt) hhi

theorem noisyIC_common_conull_surplus (i : Row) (N : ℕ)
    (hM : 2*Uniform07.capacity (N+1)< N+1) (hc : 0< Uniform07.capacity (N+1))
    (eps : unitInterval)
    (heps : (eps:ℝ)≤(1-chi)*
      AtomEvents.lowerEvent (t i) (t_pos i).le (t_lt_one i).le (N+1)/4)
    (hcost : (1+eta i)*(chi+(eps:ℝ))≤1)
    (pi : Joint i) (hIC : NoisyIC i N eps pi) :
    ∀ᵐp∂(pi.1 : Measure (Value i×unitInterval)), ∀z : unitInterval,
      (1-chi)*(noisyBid i (eps,(p,z)):ℝ)*
        AtomEvents.lowerEvent (t i) (t_pos i).le (t_lt_one i).le (N+1)/2 ≤
          (p.1:ℝ)-(noisyBid i (eps,(p,z)):ℝ) := by
  filter_upwards [hIC] with p hp
  intro z
  by_cases hv : 0<(p.1:ℝ)
  · exact supported_physical_surplus i N hM hc eps heps hcost pi p.1 hv p.2
      (hp (comparisonChoice i p.1)) z
  · have hv0 : (p.1:ℝ)=0 := le_antisymm (le_of_not_gt hv) p.1.property.1
    have hb := noisyRealBid_bounds i eps p.1 p.2 z
    have hb0 := (noisyBid i (eps,(p,z))).property.1
    have he : (noisyBid i (eps,(p,z)):ℝ)=0 := by
      have hhi : (noisyBid i (eps,(p,z)):ℝ)≤(p.1:ℝ) := hb.2.trans (min_le_left _ _)
      linarith
    simp only [hv0, he, mul_zero, zero_mul, zero_div, sub_zero, le_refl]

end ActualSurplus
end FCAppendix.Affine.UniformFinite
