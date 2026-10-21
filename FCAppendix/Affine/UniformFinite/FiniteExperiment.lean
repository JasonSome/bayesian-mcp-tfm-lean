import FCAppendix.Affine.UniformFinite.ActualContinuation
import FCAppendix.Affine.UniformFinite.NoisyChoices
import FCAppendix.Existence.R01PayOnceRowIntegration

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

def categoryLaw (i : Row) : FiniteLaw (Fin 3) where
  mass k := if k=0 then Uniform05.t i else (1-Uniform05.t i)/2
  nonneg k := by
    split_ifs
    · exact (Uniform05.t_pos i).le
    · linarith [Uniform05.t_lt_one i]
  total := by
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp

@[simp] lemma categoryLaw_lower (i : Row) : (categoryLaw i).mass 0=Uniform05.t i := by
  simp [categoryLaw]

@[simp] lemma categoryLaw_upper0 (i : Row) :
    (categoryLaw i).mass 1=(1-Uniform05.t i)/2 := by simp [categoryLaw]

@[simp] lemma categoryLaw_upper1 (i : Row) :
    (categoryLaw i).mass 2=(1-Uniform05.t i)/2 := by simp [categoryLaw]

def categoryRowLaw (i : Row) (N : ℕ) : FiniteLaw (Fin N→ Fin 3) :=
  CommonList.iid (categoryLaw i) N

def focalRow {N : ℕ} (kind : Fin N→ Fin 3) : Source.CountRow (N+1) :=
  Source.countRowOfKind (Fin.cons 0 kind)

def focalBids {N : ℕ} (i : Row) (kind : Fin N→ Fin 3)
    (own : ℝ) (b : Fin N→ Bid i) : Fin (N+1)→ℝ :=
  Fin.cons own (fun j=> if kind j=0 then (b j:ℝ) else 0)

@[simp] lemma focalBids_zero {N : ℕ} (i : Row) (kind : Fin N→ Fin 3)
    (own : ℝ) (b : Fin N→ Bid i) : focalBids i kind own b 0=own := by
  simp [focalBids]

@[simp] lemma focalBids_succ {N : ℕ} (i : Row) (kind : Fin N→ Fin 3)
    (own : ℝ) (b : Fin N→ Bid i) (j : Fin N) :
    focalBids i kind own b j.succ=(if kind j=0 then (b j:ℝ) else 0) := by
  simp [focalBids]

lemma continuous_focalBids {N : ℕ} (i : Row) (kind : Fin N→ Fin 3) :
    Continuous (fun p : ℝ×(Fin N→ Bid i)=> focalBids i kind p.1 p.2) := by
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun j=>?_) j
  · simpa using (continuous_fst : Continuous (fun p : ℝ×(Fin N→ Bid i)=> p.1))
  · by_cases hk : kind j=0
    · change Continuous (fun p : ℝ×(Fin N→ Bid i) => if kind j=0 then (p.2 j : ℝ) else 0)
      simp only [hk, if_true]
      exact continuous_subtype_val.comp ((continuous_apply j).comp continuous_snd)
    · simpa [hk] using (continuous_const : Continuous (fun _ : ℝ×(Fin N→ Bid i)=>(0:ℝ)))

def rawUtility (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i) (v own : ℝ) : ℝ :=
  (categoryRowLaw i N).expect (fun kind=>
    ∫b : Fin N→ Bid i,
      rowPayoff i G (focalRow kind) v (focalBids i kind own b) 0
      ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)))

def expectedUtility (i : Row) (N : ℕ) (eps : unitInterval)
    (pi : Joint i) (v : Value i) (q : unitInterval) : ℝ :=
  let G := restrictedLaw i (eps,pi)
  (categoryRowLaw i N).expect (fun kind=>
    ∫b : Fin N→ Bid i,
      (∫z : unitInterval,
        rowPayoff i G (focalRow kind) v
          (focalBids i kind (noisyBid i (eps,((v,q),z)):ℝ) b) 0)
      ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)))

def NoisyIC (i : Row) (N : ℕ) (eps : unitInterval) (pi : Joint i) : Prop :=
  ∀ᵐp ∂(pi.1 : Measure (Value i×unitInterval)),∀q' : unitInterval,
    expectedUtility i N eps pi p.1 q'≤ expectedUtility i N eps pi p.1 p.2

def DisintegratedNoisyIC (i : Row) (N : ℕ) (eps : unitInterval)
    (pi : Joint i) (sigma : Kernel (Value i) unitInterval) : Prop :=
  IsMarkovKernel sigma ∧
    lowerMeasure i⊗ₘsigma=(pi.1 : Measure (Value i×unitInterval)) ∧
    (∀ᵐv ∂lowerMeasure i,∀ᵐq ∂sigma v,∀q' : unitInterval,
      expectedUtility i N eps pi v q'≤ expectedUtility i N eps pi v q)

lemma rawUtility_bound (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i) (v own : ℝ) :
    |rawUtility i N G v own|≤|v|+(1+|Uniform05.eta i|)*|own| := by
  have hrow (kind : Fin N→ Fin 3) :
      |(∫b : Fin N→ Bid i,
        rowPayoff i G (focalRow kind) v (focalBids i kind own b) 0
        ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)))|≤
        |v|+(1+|Uniform05.eta i|)*|own| := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const
        (f := fun b : Fin N→ Bid i => rowPayoff i G (focalRow kind) v (focalBids i kind own b) 0)
        (C := |v|+(1+|Uniform05.eta i|)*|own|)
        (ae_of_all (rowLaw N G.bidLaw : Measure (Fin N→ Bid i)) (fun b=> by
          simpa only [Real.norm_eq_abs,focalBids_zero] using
            rowPayoff_bound i G (focalRow kind) v (focalBids i kind own b) 0))
  apply abs_le.mpr
  constructor
  · exact (categoryRowLaw i N).const_le_expect (fun kind=>(abs_le.mp (hrow kind)).1)
  · exact (categoryRowLaw i N).expect_le_const (fun kind=>(abs_le.mp (hrow kind)).2)

lemma noisyRowPayoff_bound (i : Row) {N : ℕ} (eps : unitInterval) (pi : Joint i)
    (v : Value i) (q z : unitInterval) (kind : Fin N→ Fin 3) (b : Fin N→ Bid i) :
    |rowPayoff i (restrictedLaw i (eps,pi)) (focalRow kind) v
      (focalBids i kind (noisyBid i (eps,((v,q),z)):ℝ) b) 0|≤3*(v:ℝ) := by
  have hb := noisyRealBid_bounds i eps v q z
  have hb0 : 0≤(noisyBid i (eps,((v,q),z)):ℝ) := (noisyBid i (eps,((v,q),z))).property.1
  have hbv : (noisyBid i (eps,((v,q),z)):ℝ)≤(v:ℝ) := hb.2.trans (min_le_left _ _)
  have hη := Uniform05.eta_range i
  have h := rowPayoff_bound i (restrictedLaw i (eps,pi)) (focalRow kind) v
    (focalBids i kind (noisyBid i (eps,((v,q),z)):ℝ) b) 0
  simp only [focalBids_zero,abs_of_nonneg v.property.1,abs_of_nonneg hb0,
    abs_of_nonneg hη.1.le] at h
  nlinarith

lemma expectedUtility_bound (i : Row) (N : ℕ) (eps : unitInterval)
    (pi : Joint i) (v : Value i) (q : unitInterval) :
    |expectedUtility i N eps pi v q|≤3*(v:ℝ) := by
  let G := restrictedLaw i (eps,pi)
  have hinner (kind : Fin N→ Fin 3) (b : Fin N→ Bid i) :
      |(∫z : unitInterval,rowPayoff i G (focalRow kind) v
        (focalBids i kind (noisyBid i (eps,((v,q),z)):ℝ) b) 0)|≤3*(v:ℝ) := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const
        (f := fun z : unitInterval => rowPayoff i G (focalRow kind) v
          (focalBids i kind (noisyBid i (eps,((v,q),z)):ℝ) b) 0)
        (C := 3*(v : ℝ))
        (ae_of_all (volume : Measure unitInterval) (fun z=> by
          simpa only [Real.norm_eq_abs] using noisyRowPayoff_bound i eps pi v q z kind b))
  have houter (kind : Fin N→ Fin 3) :
      |(∫b : Fin N→ Bid i,(∫z : unitInterval,rowPayoff i G (focalRow kind) v
        (focalBids i kind (noisyBid i (eps,((v,q),z)):ℝ) b) 0)
        ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)))|≤3*(v:ℝ) := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const
        (f := fun b : Fin N→ Bid i => ∫z : unitInterval, rowPayoff i G (focalRow kind) v
          (focalBids i kind (noisyBid i (eps,((v,q),z)):ℝ) b) 0)
        (C := 3*(v : ℝ))
        (ae_of_all (rowLaw N G.bidLaw : Measure (Fin N→ Bid i)) (fun b=> by
          simpa only [Real.norm_eq_abs] using hinner kind b))
  apply abs_le.mpr
  constructor
  · exact (categoryRowLaw i N).const_le_expect (fun kind=>(abs_le.mp (houter kind)).1)
  · exact (categoryRowLaw i N).expect_le_const (fun kind=>(abs_le.mp (houter kind)).2)

theorem rival_bid_row_exact (i : Row) (N : ℕ) (eps : unitInterval) (pi : Joint i) :
    (rowLaw N (restrictedLaw i (eps,pi)).bidLaw : Measure (Fin N→ Bid i))=
      Measure.pi (fun _ : Fin N=>(bidLaw i (eps,pi) : Measure (Bid i))) := by
  rw [restrictedLaw_bidLaw]
  exact rowLaw_eq_pi N _

theorem rival_bid_coordinate_exact (i : Row) (N : ℕ) (eps : unitInterval)
    (pi : Joint i) (j : Fin N) :
    (rowLaw N (restrictedLaw i (eps,pi)).bidLaw : Measure (Fin N→ Bid i)).map
      (fun b=> b j)=(bidLaw i (eps,pi) : Measure (Bid i)) := by
  rw [rowLaw_coordinate,restrictedLaw_bidLaw]

end FCAppendix.Affine.UniformFinite
