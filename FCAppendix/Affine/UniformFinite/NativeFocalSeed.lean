import FCAppendix.Affine.UniformFinite.NativeSeedIntegration
import FCAppendix.Affine.UniformFinite.RawCounts

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.NativeRow
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game
open Uniform05 SourceContinuity WeightedSampling
open scoped BigOperators
variable {M : ℕ} [NeZero M]

lemma map_mass_pos {A B : Type*} [Fintype A] [Fintype B]
    (P : FiniteLaw A) (f : A→ B) (a : A) (ha : 0< P.mass a) :
    0<(P.map f).mass (f a) := by
  apply ha.trans_le
  change P.mass a≤∑b,if f b=f a then P.mass b else 0
  have h:=Finset.single_le_sum (s:=Finset.univ)
    (f:=fun b=> if f b=f a then P.mass b else 0)
    (fun b _=> by split_ifs; exact P.nonneg b; exact le_rfl) (Finset.mem_univ a)
  simpa only [if_true] using h

theorem draw_mass_pos (i : Row) (row : Source.CountRow M) (x : State i M) (s : Seeds) :
    0<(continuationLaw i x.1 row (bids i x)).mass (draw i row x s) := by
  rw [← experimentLaw_eq_continuation i row x]
  apply map_mass_pos _ Prod.snd (commonSample i row x s.1,draw i row x s)
  change 0<(commonLaw i row x).mass (commonSample i row x s.1)*
    ((privateLaw i row 0 x (commonSample i row x s.1)).mass
      (privateSample i row 0 (x,commonSample i row x s.1) s.2.1)*
    (privateLaw i row 1 x (commonSample i row x s.1)).mass
      (privateSample i row 1 (x,commonSample i row x s.1) s.2.2))
  convert! mul_pos (commonSample_support i row x s.1)
    (mul_pos (privateSample_support i row 0 (x,commonSample i row x s.1) s.2.1)
      (privateSample_support i row 1 (x,commonSample i row x s.1) s.2.2)) using 1

lemma nonnegative_support_zero {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (f : Ω→ℝ) (hf : ∀a,0≤ f a) (hmean : P.expect f=0)
    (a : Ω) (ha : 0< P.mass a) : f a=0 := by
  have h:=Finset.single_le_sum (s:=Finset.univ) (f:=fun b=> P.mass b*f b)
    (fun b _=> mul_nonneg (P.nonneg b) (hf b)) (Finset.mem_univ a)
  change P.mass a*f a≤ P.expect f at h
  rw [hmean] at h
  have he : P.mass a*f a=0:=le_antisymm h (mul_nonneg ha.le (hf a))
  exact (mul_eq_zero.mp he).resolve_left ha.ne'

def focalTrace (a : Fin M) (P : Allocation M) : Bool×Bool :=
  (decide (a∈P.1),decide (a∈P.2))

omit [NeZero M] in
lemma trace_zero_of_first_zero (a : Fin M) (P : Allocation M)
    (h : Literal.firstCopy a P=0) : focalTrace a P=(false,false) := by
  by_cases h0 : a∈P.1 <;> by_cases h1 : a∈P.2 <;>
    simp [Literal.firstCopy,WeightedSampling.indicator,h0,h1] at h ⊢ ;
    simp [focalTrace,h0,h1]

theorem guarded_seed_trace_support (i : Row) (row : Source.CountRow M)
    (hne : Source.residual row 0≠Source.residual row 1)
    (x : State i M) (a : Fin M) (ha : a∈row.lower)
    (hbid : bids i x a≤ t i/2) (hraw : 0< rawWeight i row x)
    (P : Allocation M) (hP : 0<(continuationLaw i x.1 row (bids i x)).mass P) :
    focalTrace a P=(false,false) := by
  have hz (v : ℝ) : rowPayoff i x.1 row v (bids i x) a=0 := by
    rw [SeedRejection.rowPayoff_eq_pure_near_seed i row a ha hne (v,x)
      (hbid.trans (SeedRejection.cutoffNeighborhood_gt_seed i).le)]
    exact SeedRejection.purePayoff_zero_near_seed i row a ha (v,x) hraw
      (hbid.trans (SeedRejection.cutoffNeighborhood_gt_seed i).le)
  have hmean : successProbability i x.1 row (bids i x) a=0 := by
    have h:=row_value_difference i x.1 row (bids i x) a 1 0
    simpa only [hz,sub_self,sub_zero,one_mul] using h.symm
  exact trace_zero_of_first_zero a P (nonnegative_support_zero _ (Literal.firstCopy a)
    (fun P=>(firstCopy_bounds a P).1) hmean P hP)

theorem guarded_seed_trace (i : Row) (row : Source.CountRow M)
    (hne : Source.residual row 0≠Source.residual row 1)
    (x : State i M) (a : Fin M) (ha : a∈row.lower)
    (hbid : bids i x a≤ t i/2) (hraw : 0< rawWeight i row x) (s : Seeds) :
    focalTrace a (draw i row x s)=(false,false) :=
  guarded_seed_trace_support i row hne x a ha hbid hraw _ (draw_mass_pos i row x s)

lemma private_integral_common_irrelevant (i : Row) (row : Source.CountRow M)
    (x : State i M) (h : Source.residual row 0=Source.residual row 1 ∨
      Source.guardAlpha i x.1 row (bids i x)=0) (u : unitInterval)
    (f : Allocation M→ℝ) :
    (∫s,f (draw i row x (u,s)) ∂((volume : Measure unitInterval).prod volume))=
      (continuationLaw i x.1 row (bids i x)).expect f := by
  rw [← draw_integral i row x f]
  have hi : Integrable (fun s : Seeds=> f (draw i row x s)) seedsLaw :=
    Integrable.of_bound ((measurable_of_countable f).comp (draw_measurable i row x)).aestronglyMeasurable
      (∑P,|f P|) (Eventually.of_forall (fun s=> finite_bound f _))
  rw [seedsLaw,integral_prod _ hi]
  have he : (fun q : unitInterval=>∫s,f (draw i row x (q,s))
      ∂((volume : Measure unitInterval).prod volume)) =
      fun _ : unitInterval=>∫s,f (draw i row x (u,s))
        ∂((volume : Measure unitInterval).prod volume) := by
    funext q
    simp only [draw_common_irrelevant i row x h q u]
  rw [he]
  simp

theorem fixed_seed_trace_integral (i : Row) (row : Source.CountRow M)
    (x : State i M) (a : Fin M) (ha : a∈row.lower) (hbid : bids i x a≤ t i/2)
    (u : unitInterval) (g : Bool×Bool→ℝ) :
    (∫s,g (focalTrace a (draw i row x (u,s)))
      ∂((volume : Measure unitInterval).prod volume))=
      (continuationLaw i x.1 row (bids i x)).expect (fun P=> g (focalTrace a P)) := by
  by_cases he : Source.residual row 0=Source.residual row 1
  · exact private_integral_common_irrelevant i row x (Or.inl he) u (fun P=>g (focalTrace a P))
  by_cases hz : Source.guardAlpha i x.1 row (bids i x)=0
  · exact private_integral_common_irrelevant i row x (Or.inr hz) u (fun P=>g (focalTrace a P))
  have hα : 0< Source.guardAlpha i x.1 row (bids i x) :=
    lt_of_le_of_ne (Source.guardAlpha_bounds i x.1 row (bids i x)).1 (Ne.symm hz)
  have hr:=alpha_pos_raw i row x hα
  have hleft : (∫s,g (focalTrace a (draw i row x (u,s)))
      ∂((volume : Measure unitInterval).prod volume))=g (false,false) := by
    simp only [guarded_seed_trace i row he x a ha hbid hr]
    simp
  rw [hleft]
  symm
  calc
    _=(continuationLaw i x.1 row (bids i x)).expect (fun _=> g (false,false)) := by
      unfold FiniteLaw.expect
      apply Finset.sum_congr rfl
      intro P _
      by_cases hP : (continuationLaw i x.1 row (bids i x)).mass P=0
      · simp only [hP,zero_mul]
      · exact congrArg (fun tr : Bool×Bool=>
          (continuationLaw i x.1 row (bids i x)).mass P*g tr)
          (guarded_seed_trace_support i row he x a ha hbid hr P
            (lt_of_le_of_ne (FiniteLaw.nonneg _ P) (Ne.symm hP)))
    _=g (false,false) := FiniteLaw.expect_const _ _

theorem fixed_seed_trace_law (i : Row) (row : Source.CountRow M)
    (x : State i M) (a : Fin M) (ha : a∈row.lower) (hbid : bids i x a≤ t i/2)
    (u : unitInterval) :
    FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod volume)
      (fun s=> focalTrace a (draw i row x (u,s)))
      ((measurable_of_countable (focalTrace a)).comp
        ((draw_measurable i row x).comp ((measurable_const (a := u)).prodMk measurable_id))) =
      (continuationLaw i x.1 row (bids i x)).map (focalTrace a) := by
  apply FiniteLaw.ext_expect
  intro g
  rw [FiniteLaw.expect_ofMeasure,FiniteLaw.expect_map,fixed_seed_trace_integral i row x a ha hbid u g]

end FCAppendix.Affine.UniformFinite.NativeRow
