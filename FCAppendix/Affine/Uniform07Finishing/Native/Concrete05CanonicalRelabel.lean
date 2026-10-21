import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Canonical
import FCAppendix.Affine.UniformFinite.SourceRelabel

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open FCAppendix.Affine UniformFinite WeightedSampling
open Crossover.Received06
open scoped BigOperators
variable {row : Uniform07.Row} {m N : ℕ}

theorem countTest_affine (q : Fin 3→ℝ) (i : Fin m) (P : UniformFinite.Allocation m) :
    q (UniformFinite.pairCount i P)=q 0+(q 1-q 0)*Literal.firstCopy i P+
      (q 2-q 1)*Literal.duplicateCopy i P := by
  by_cases h0 : i∈P.1 <;> by_cases h1 : i∈P.2 <;>
    simp [UniformFinite.pairCount,Literal.firstCopy,Literal.duplicateCopy,
      WeightedSampling.indicator,h0,h1]

theorem countTest_expect_affine (L : FiniteLaw (UniformFinite.Allocation m))
    (q : Fin 3→ℝ) (i : Fin m) :
    L.expect (fun P=>q (UniformFinite.pairCount i P))=
      q 0+(q 1-q 0)*L.expect (Literal.firstCopy i)+
        (q 2-q 1)*L.expect (Literal.duplicateCopy i) := by
  simp_rw [countTest_affine]
  rw [FiniteLaw.expect_add,FiniteLaw.expect_add,FiniteLaw.expect_const,
    FiniteLaw.expect_const_mul,FiniteLaw.expect_const_mul]

theorem count_expect_eq_of_two_payoffs
    (A B : FiniteLaw (UniformFinite.Allocation m)) (i j : Fin m)
    {η own : ℝ} (hηb : η*own≠0)
    (h0 : A.expect (UniformFinite.pairPayoff η 0 own i)=
      B.expect (UniformFinite.pairPayoff η 0 own j))
    (h1 : A.expect (UniformFinite.pairPayoff η 1 own i)=
      B.expect (UniformFinite.pairPayoff η 1 own j)) (q : Fin 3→ℝ) :
    A.expect (fun P=>q (UniformFinite.pairCount i P))=
      B.expect (fun P=>q (UniformFinite.pairCount j P)) := by
  change A.expect (fun P=>(0-own)*Literal.firstCopy i P-η*own*Literal.duplicateCopy i P)=
    B.expect (fun P=>(0-own)*Literal.firstCopy j P-η*own*Literal.duplicateCopy j P) at h0
  change A.expect (fun P=>(1-own)*Literal.firstCopy i P-η*own*Literal.duplicateCopy i P)=
    B.expect (fun P=>(1-own)*Literal.firstCopy j P-η*own*Literal.duplicateCopy j P) at h1
  simp only [FiniteLaw.expect_sub,
    FiniteLaw.expect_const_mul] at h0 h1
  have hS : A.expect (Literal.firstCopy i)=B.expect (Literal.firstCopy j) := by
    linarith
  have hD : A.expect (Literal.duplicateCopy i)=B.expect (Literal.duplicateCopy j) := by
    apply (mul_left_cancel₀ hηb)
    rw [hS] at h0
    linarith
  rw [countTest_expect_affine,countTest_expect_affine,hS,hD]

theorem rowCanonicalMoment05_relabel [NeZero m]
    (e : Equiv.Perm (Fin m)) (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) (D : UniformFinite.Source.CountRow m)
    (b : Fin m→ Uniform05.Bid row) (i : Fin m) (hi : i∈D.lower)
    (hb : 0<(b i:ℝ)) (q : Fin 3→ℝ) :
    rowCanonicalMoment05 row G (UniformFinite.SourceRelabel.row e D)
      (fun j=>(b (e.symm j):ℝ)) (e i) q=
      rowCanonicalMoment05 row G D (fun j=>(b j:ℝ)) i q := by
  have hηb : Uniform05.eta row*(b i:ℝ)≠0 :=
    mul_ne_zero (Uniform05.eta_range row).1.ne' hb.ne'
  by_cases he : UniformFinite.Source.residual D 0=UniformFinite.Source.residual D 1
  · simp only [rowCanonicalMoment05,UniformFinite.SourceRelabel.residual,if_pos he]
    exact count_expect_eq_of_two_payoffs _ _ _ _ hηb
      (UniformFinite.SourceRelabel.equalPayoff e row G D b 0 i)
      (UniformFinite.SourceRelabel.equalPayoff e row G D b 1 i) q
  · simp only [rowCanonicalMoment05,UniformFinite.SourceRelabel.residual,if_neg he]
    change UniformFinite.Source.guardAlpha row G (UniformFinite.SourceRelabel.row e D)
        ((fun j=>(b j:ℝ))∘e.symm)*_= _
    rw [UniformFinite.SourceRelabel.alpha]
    by_cases hz : UniformFinite.Source.guardAlpha row G D (fun j=>(b j:ℝ))=0
    · simp only [hz,zero_mul]
    · have ha : 0< UniformFinite.Source.guardAlpha row G D (fun j=>(b j:ℝ)) :=
        lt_of_le_of_ne (UniformFinite.Source.guardAlpha_bounds row G D _).1 (Ne.symm hz)
      have haraw : 0< UniformFinite.Source.rawAlpha row G D
          (UniformFinite.SourceContinuity.bids row (G,b)) := by
        unfold UniformFinite.Source.guardAlpha at ha
        split_ifs at ha
        · exact False.elim ((lt_irrefl 0) ha)
        · exact ha
      congr 1
      exact count_expect_eq_of_two_payoffs _ _ _ _ hηb
        (UniformFinite.SourceRelabel.canonicalPayoff e row G D b 0 i hi haraw)
        (UniformFinite.SourceRelabel.canonicalPayoff e row G D b 1 i hi haraw) q

theorem numeric_row_relabel (row : Uniform07.Row) (e : Equiv.Perm (Fin m))
    (i : Fin m) (z : Fin m→ UniformFinite.NumericObservation row) :
    UniformFinite.Late.ExceptionalProfile.numericRow row (e i) (z∘e.symm)=
      UniformFinite.SourceRelabel.row e
        (UniformFinite.Late.ExceptionalProfile.numericRow row i z) := by
  unfold UniformFinite.Late.ExceptionalProfile.numericRow UniformFinite.NativeProfile.numericRow
  rw [←UniformFinite.SourceRelabel.countRowOfKind]
  congr 1
  funext j
  by_cases hj : j=e i
  · subst j
    simp [UniformFinite.NativeProfile.insert]
  · have hj' : e.symm j≠i := by
      intro h
      exact hj ((e.apply_symm_apply j).symm.trans (congrArg e h))
    simp [UniformFinite.NativeProfile.insert,Function.update_of_ne hj,
      Function.update_of_ne hj',Function.comp_apply]

theorem numeric_bids_relabel (row : Uniform07.Row) (e : Equiv.Perm (Fin m))
    (i : Fin m) (own : ℝ) (z : Fin m→ UniformFinite.NumericObservation row) :
    UniformFinite.Late.ExceptionalProfile.numericBids row (e i) own (z∘e.symm)=
      UniformFinite.Late.ExceptionalProfile.numericBids row i own z∘e.symm := by
  funext j
  by_cases hj : j=e i
  · subst j
    simp [UniformFinite.Late.ExceptionalProfile.numericBids]
  · have hj' : e.symm j≠i := by
      intro h
      exact hj ((e.apply_symm_apply j).symm.trans (congrArg e h))
    simp [UniformFinite.Late.ExceptionalProfile.numericBids,Function.update_of_ne hj,
      Function.update_of_ne hj',Function.comp_apply]

theorem numeric_bids_capped_vector (row : Uniform07.Row) (i : Fin m)
    (own : Uniform05.Bid row) (z : Fin m→ UniformFinite.NumericObservation row) :
    UniformFinite.Late.ExceptionalProfile.numericBids row i own z=
      fun j=>(UniformFinite.NativeProfile.numericBids row
        (UniformFinite.NativeProfile.insert i own z) j:ℝ) := by
  funext j
  by_cases hj : j=i
  · subst j
    simp [UniformFinite.Late.ExceptionalProfile.numericBids,UniformFinite.NativeProfile.numericBids,
      UniformFinite.NativeProfile.insert,UniformFinite.NativeProfile.numericCapped]
  · rcases hz : z j with b|k <;>
      simp [UniformFinite.Late.ExceptionalProfile.numericBids,UniformFinite.NativeProfile.numericBids,
        UniformFinite.NativeProfile.insert,UniformFinite.NativeProfile.numericCapped,
        UniformFinite.numericBid,hj,hz,UniformFinite.Noisy.zeroBid]

theorem numeric_canonical_relabel [NeZero m]
    (row : Uniform07.Row) (G : Uniform05.RestrictedLaw row)
    (e : Equiv.Perm (Fin m)) (i : Fin m) (own : Uniform05.Bid row)
    (hown : 0<(own:ℝ)) (z : Fin m→ UniformFinite.NumericObservation row)
    (q : Fin 3→ℝ) :
    rowCanonicalMoment05 row G
      (UniformFinite.Late.ExceptionalProfile.numericRow row (e i) (z∘e.symm))
      (UniformFinite.Late.ExceptionalProfile.numericBids row (e i) own (z∘e.symm)) (e i) q=
    rowCanonicalMoment05 row G
      (UniformFinite.Late.ExceptionalProfile.numericRow row i z)
      (UniformFinite.Late.ExceptionalProfile.numericBids row i own z) i q := by
  rw [numeric_row_relabel,numeric_bids_relabel,numeric_bids_capped_vector]
  exact rowCanonicalMoment05_relabel e row G _ _ i
    (UniformFinite.Late.ExceptionalProfile.focal_mem row i z)
    (by simpa [UniformFinite.NativeProfile.numericBids,UniformFinite.NativeProfile.insert,
      UniformFinite.NativeProfile.numericCapped] using hown) q

theorem numeric_profile_relabel_preserving (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) (e : Equiv.Perm (Fin m)) :
    MeasurePreserving (fun z : Fin m→ UniformFinite.NumericObservation row=>z∘e.symm)
      (Measure.pi (fun _ : Fin m=>UniformFinite.numericObservationLaw row G))
      (Measure.pi (fun _ : Fin m=>UniformFinite.numericObservationLaw row G)) := by
  convert measurePreserving_piCongrLeft
    (fun _ : Fin m=>UniformFinite.numericObservationLaw row G) e using 1
  funext z j
  simp [MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft']

theorem measurable_indexed_canonical_moment [NeZero m]
    (row : Uniform07.Row) (G : Uniform05.RestrictedLaw row) (i : Fin m)
    (own : Uniform05.Bid row) (q : Fin 3→ℝ) (hq : q 0=0) :
    Measurable (fun z : Fin m→ UniformFinite.NumericObservation row=>
      rowCanonicalMoment05 row G
        (UniformFinite.Late.ExceptionalProfile.numericRow row i z)
        (UniformFinite.Late.ExceptionalProfile.numericBids row i own z) i q) := by
  have hm : 0< m := Nat.pos_of_ne_zero (NeZero.ne m)
  have heq : nativeCanonicalNumericMoment row G i own q=
      (fun z : Fin m→UniformFinite.NumericObservation row=>
        rowCanonicalMoment05 row G
          (UniformFinite.Late.ExceptionalProfile.numericRow row i z)
          (UniformFinite.Late.ExceptionalProfile.numericBids row i own z) i q) :=
    funext (fun z=>numeric_canonical_moment_eq05 row G hm i own z q hq)
  rw [←heq]
  exact measurable_nativeCanonicalNumericMoment row G i own q

theorem indexed_canonical_integral_relabel [NeZero m]
    (row : Uniform07.Row) (G : Uniform05.RestrictedLaw row)
    (e : Equiv.Perm (Fin m)) (i : Fin m) (own : Uniform05.Bid row)
    (hown : 0<(own:ℝ)) (q : Fin 3→ℝ) (hq : q 0=0) :
    (∫z,rowCanonicalMoment05 row G
      (UniformFinite.Late.ExceptionalProfile.numericRow row (e i) z)
      (UniformFinite.Late.ExceptionalProfile.numericBids row (e i) own z) (e i) q
      ∂Measure.pi (fun _ : Fin m=>UniformFinite.numericObservationLaw row G))=
    ∫z,rowCanonicalMoment05 row G
      (UniformFinite.Late.ExceptionalProfile.numericRow row i z)
      (UniformFinite.Late.ExceptionalProfile.numericBids row i own z) i q
      ∂Measure.pi (fun _ : Fin m=>UniformFinite.numericObservationLaw row G) := by
  let f := fun z : Fin m→ UniformFinite.NumericObservation row=>
    rowCanonicalMoment05 row G
      (UniformFinite.Late.ExceptionalProfile.numericRow row (e i) z)
      (UniformFinite.Late.ExceptionalProfile.numericBids row (e i) own z) (e i) q
  have hf : Measurable f:=measurable_indexed_canonical_moment row G (e i) own q hq
  conv_lhs => rw [←(numeric_profile_relabel_preserving row G e).map_eq]
  rw [integral_map (numeric_profile_relabel_preserving row G e).measurable.aemeasurable
      hf.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ (fun z=>numeric_canonical_relabel row G e i own hown z q))

theorem indexed_zero_canonical_row (row : Uniform07.Row) (G : Uniform05.RestrictedLaw row)
    (own : Uniform05.Bid row) (q : Fin 3→ℝ)
    (z : Fin (N+1)→ UniformFinite.NumericObservation row) :
    rowCanonicalMoment05 row G
      (UniformFinite.Late.ExceptionalProfile.numericRow row 0 z)
      (UniformFinite.Late.ExceptionalProfile.numericBids row 0 own z) 0 q=
      numericalCanonicalMoment05 row N G own q (fun j=>z j.succ) := by
  have hD : UniformFinite.Late.ExceptionalProfile.numericRow row 0 z=
      UniformFinite.Source.countRowOfKind
        (Fin.cons 0 (fun j : Fin N=>UniformFinite.numericKind row (z j.succ))) := by
    unfold UniformFinite.Late.ExceptionalProfile.numericRow UniformFinite.NativeProfile.numericRow
    congr 1
    funext j
    refine Fin.cases ?_ (fun k=>?_) j <;>
      simp [UniformFinite.NativeProfile.insert,UniformFinite.numericKind]
  have hb : UniformFinite.Late.ExceptionalProfile.numericBids row 0 own z=
      Fin.cons (own:ℝ) (fun j : Fin N=>UniformFinite.numericBid row (z j.succ)) := by
    funext j
    refine Fin.cases ?_ (fun k=>?_) j <;>
      simp [UniformFinite.Late.ExceptionalProfile.numericBids]
  rw [hD,hb]
  rfl

theorem measurable_numericalCanonicalMoment05
    (row : Uniform07.Row) (G : Uniform05.RestrictedLaw row)
    (own : Uniform05.Bid row) (q : Fin 3→ℝ) (hq : q 0=0) :
    Measurable (numericalCanonicalMoment05 row N G own q) := by
  let add : (Fin N→ UniformFinite.NumericObservation row)→
      Fin (N+1)→ UniformFinite.NumericObservation row :=
    fun z=>Fin.cons (Sum.inl (UniformFinite.Noisy.zeroBid row)) z
  have hadd : Measurable add:=UniformFinite.NativeProfile.measurable_numericFocal row _
  have h:= (measurable_indexed_canonical_moment row G (0 : Fin (N+1)) own q hq).comp hadd
  have heq : ((fun z : Fin (N+1)→UniformFinite.NumericObservation row=>
      rowCanonicalMoment05 row G
        (UniformFinite.Late.ExceptionalProfile.numericRow row 0 z)
        (UniformFinite.Late.ExceptionalProfile.numericBids row 0 own z) 0 q)∘add)=
      numericalCanonicalMoment05 row N G own q := by
    funext z
    dsimp only [Function.comp_def]
    rw [indexed_zero_canonical_row]
    rfl
  rw [←heq]
  exact h

theorem indexed_zero_canonical_integral (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) (own : Uniform05.Bid row)
    (q : Fin 3→ℝ) (hq : q 0=0) :
    (∫z,rowCanonicalMoment05 row G
      (UniformFinite.Late.ExceptionalProfile.numericRow row (0 : Fin (N+1)) z)
      (UniformFinite.Late.ExceptionalProfile.numericBids row 0 own z) 0 q
      ∂Measure.pi (fun _ : Fin (N+1)=>UniformFinite.numericObservationLaw row G))=
      ∫z,numericalCanonicalMoment05 row N G own q z
        ∂Measure.pi (fun _ : Fin N=>UniformFinite.numericObservationLaw row G) := by
  let μ:=UniformFinite.numericObservationLaw row G
  let tail : (Fin (N+1)→ UniformFinite.NumericObservation row)→
      Fin N→ UniformFinite.NumericObservation row :=fun z j=>z j.succ
  have htail : MeasurePreserving tail (Measure.pi (fun _ : Fin (N+1)=>μ))
      (Measure.pi (fun _ : Fin N=>μ)) :=
    (measurePreserving_snd (μ:=μ) (ν:=Measure.pi (fun _ : Fin N=>μ))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1)=>μ) 0)
  simp_rw [indexed_zero_canonical_row]
  change (∫z,numericalCanonicalMoment05 row N G own q (tail z)
      ∂Measure.pi (fun _ : Fin (N+1)=>μ))=_
  rw [←htail.map_eq]
  exact (integral_map htail.measurable.aemeasurable
    (measurable_numericalCanonicalMoment05 row G own q hq).aestronglyMeasurable).symm

theorem native_canonical_count_eq_numerical {row : Uniform07.Row}
    (E : UniformFinite.ExactRestrictedLaw row (N+1))
    (hc : 1≤ Uniform07.capacity (N+1)) {R : ℝ} (hR : 0< R)
    (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (hguard : Uniform07.kappa row*R< E.law.multiplier-Early.nativeRadius row)
    (i : Fin (N+1)) (own : Uniform05.Bid row) (hown : 0<(own:ℝ))
    (q : Fin 3→ℝ) (hq : q 0=0) :
    nativeCanonicalMoment E hc R i (Hybrid.lowBroadcast own) q=
      ∫z,numericalCanonicalMoment05 row N E.law own q z
        ∂Measure.pi (fun _ : Fin N=>UniformFinite.numericObservationLaw row E.law) := by
  rw [native_canonical_count_eq05 E hc hR hUR hRt hguard i own hown q hq]
  have hrel:=indexed_canonical_integral_relabel row E.law
    (Equiv.swap (0 : Fin (N+1)) i) 0 own hown q hq
  simp only [Equiv.swap_apply_left] at hrel
  rw [hrel]
  exact indexed_zero_canonical_integral row E.law own q hq

end FCAppendix.Affine.Uniform07Finishing.Concrete05
