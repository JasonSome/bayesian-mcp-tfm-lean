import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05AboveCapGuard
import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Counts

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine LowBody StrictNative
open scoped BigOperators
variable {M : ℕ} [Nonempty (Fin M)] [NeZero M]

omit [Nonempty (Fin M)] [NeZero M] in
theorem rowContext_exceptional_card_le_one (i : Uniform07.Row)
    (row : UniformFinite.Source.CountRow M) (b : Fin M→ℝ) (a : Fin M)
    (hcap : ∀j,b j≤ Early.bidCap i) (own : ℝ) :
    (Weighted.exceptionalSet (Early.bidCap i)
      (rowContext row (Function.update b a own)).1).card≤ 1 := by
  have hs : Weighted.exceptionalSet (Early.bidCap i)
      (rowContext row (Function.update b a own)).1⊆{a} := by
    intro j hj
    apply Finset.mem_singleton.mpr
    by_contra hja
    have hpos:=(Finset.mem_filter.mp hj).2.2
    by_cases hl : j∈row.lower
    · have hb : entryBid ((rowContext row (Function.update b a own)).1 j)=b j := by
        simp only [rowContext,if_pos hl,entryBid,Function.update_of_ne hja]
      rw [hb] at hpos
      exact not_lt.mpr (hcap j) hpos
    · have hb : entryBid ((rowContext row (Function.update b a own)).1 j)=0 := by
        simp only [rowContext,if_neg hl,entryBid]
      rw [hb] at hpos
      exact not_lt.mpr (native_cap_positive i).le hpos
  simpa only [Finset.card_singleton] using Finset.card_le_card hs

omit [Nonempty (Fin M)] in

theorem native_alpha_one_weight_gate (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (X : ClassifiedContext M)
    (hα : (literalSourceAlpha i G.multiplier G.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin i) (UniformFinite.Source.commonGuardMargin i)
      X:ℝ)=1) :
    ((max (Weighted.budget (Uniform07.capacity M) 0 X)
      (Weighted.budget (Uniform07.capacity M) 1 X)-
        Weighted.commonBudget (Uniform07.capacity M) X:ℕ):ℝ)<
      WeightedSampling.totalWeight (Weighted.sourceWeights (Uniform07.xi i) G.multiplier
        (Early.demandRatio i) (Early.bidCap i) X.1) := by
  have hM : 0< M := Nat.pos_of_ne_zero (NeZero.ne M)
  have he:=UniformFinite.Source.common_guard_margin i
  have hpos : 0<(literalSourceAlpha i G.multiplier G.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin i) (UniformFinite.Source.commonGuardMargin i)
      X:ℝ) := by rw [hα]; norm_num
  have ho:=Weighted.sourceGuardAlpha_outer (Uniform07.capacity M) hM he X hpos 2
  change UniformFinite.Source.commonGuardMargin i*M<
    WeightedSampling.totalWeight (Weighted.sourceWeights (Uniform07.xi i) G.multiplier
      (Early.demandRatio i) (Early.bidCap i) X.1)-
      ((max (Weighted.budget (Uniform07.capacity M) 0 X)
        (Weighted.budget (Uniform07.capacity M) 1 X)-
          Weighted.commonBudget (Uniform07.capacity M) X:ℕ):ℝ) at ho
  have hem : 0< UniformFinite.Source.commonGuardMargin i*(M:ℝ) :=
    mul_pos he (by exact_mod_cast hM)
  linarith

theorem above_cap_context_count_eq (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (row : UniformFinite.Source.CountRow M)
    (b : Fin M→ℝ) (a : Fin M) (ha : a∈row.lower)
    (hmask : UniformFinite.Source.lowerBids row b=b) (hzero : b a=0)
    (hb : ∀j,b j∈Icc (0:ℝ) (Early.bidCap i))
    {own R : ℝ} (hown : Early.bidCap i< own) (hownR : own≤ R)
    (hR : 0< R) (hguard : Uniform07.kappa i*R< G.multiplier-Early.nativeRadius i)
    (hα : (literalSourceAlpha i G.multiplier G.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin i) (UniformFinite.Source.commonGuardMargin i)
      (rowContext row (Function.update b a own)):ℝ)=1)
    (hβ : UniformFinite.Late.Exceptional.alpha i G row (Function.update b a own) a=1)
    (seed : Prop) [Decidable seed] (hseed : seed) (q : Fin 3→ℝ) :
    nativeContextCountMoment i G (rowContext row (Function.update b a own)) seed a q=
      (UniformFinite.Late.Exceptional.continuationLaw i G row
        (Function.update b a own) a).expect (fun P=>q (UniformFinite.pairCount a P)) := by
  let X:=rowContext row (Function.update b a own)
  have hX:=rowContext_valid row (Function.update b a own)
  have heq:=rowContext_update_entry row b a ha hmask own
  have hM : 0< M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hΛ : (54/100:ℝ)*Uniform07.cutoff i< G.multiplier := by
    simpa only [Uniform05.t_eq_canonical] using G.multiplier_guards.1
  have h0 : NonnegativeList X.1 := by
    intro j
    change 0≤ entryBid ((rowContext row (Function.update b a own)).1 j)
    rw [congrFun heq j]
    by_cases hj : j=a
    · subst j
      simpa only [Function.update_self] using ((native_cap_positive i).trans hown).le
    · simpa only [Function.update_of_ne hj] using (hb j).1
  have hbound : ∀j,entryBid (X.1 j)≤ R := by
    intro j
    change entryBid ((rowContext row (Function.update b a own)).1 j)≤ R
    rw [congrFun heq j]
    by_cases hj : j=a
    · subst j
      simpa only [Function.update_self] using hownR
    · simpa only [Function.update_of_ne hj] using (hb j).2.trans (hown.le.trans hownR)
  by_cases he : Weighted.budget (Uniform07.capacity M) 0 X=
      Weighted.budget (Uniform07.capacity M) 1 X
  · have he' : UniformFinite.Source.residual row 0=UniformFinite.Source.residual row 1 := by
      simpa only [←decoded_residual X hX,rowContext_decode,X] using he
    rw [UniformFinite.Late.Exceptional.continuationLaw,if_pos he']
    have hC:=decoded_equal_count_moment i X hX he a q
    rw [show UniformFinite.NativeContext.decode X=row from rowContext_decode _ _,
      show (fun j=>entryBid (X.1 j))=Function.update b a own from heq] at hC
    rw [hC]
    unfold nativeContextCountMoment
    rw [Weighted.finitePathCountCorrection_equal_budget _ _ _ _ _ _ _ _ X he a q]
    simp only [ite_self,add_zero]
    rfl
  · have he' : UniformFinite.Source.residual row 0≠UniformFinite.Source.residual row 1 := by
      simpa only [←decoded_residual X hX,rowContext_decode,X] using he
    rw [UniformFinite.Late.Exceptional.continuationLaw,if_neg he',FiniteLaw.expect_mixture,hβ]
    simp only [one_mul,sub_self,zero_mul,add_zero]
    have hw:=rowContext_exceptional_weight i G row b a ha hmask hzero (fun j=>(hb j).2) hown
    have hC:=decoded_exceptional_canonical_count_moment i G X hX a hw a q
    rw [show UniformFinite.NativeContext.decode X=row from rowContext_decode _ _,
      show (fun j=>entryBid (X.1 j))=Function.update b a own from heq] at hC
    rw [hC]
    unfold nativeContextCountMoment
    rw [if_pos hseed,Weighted.literal_finitePathCountCorrection_eq_balanced i hΛ hR hguard hM
      (UniformFinite.Source.common_guard_margin i) (Uniform07.capacity M) X h0 hbound a q]
    have hcard:=rowContext_exceptional_card_le_one i row b a (fun j=>(hb j).2) own
    have hweight:=native_alpha_one_weight_gate i G X hα
    rw [if_pos ⟨hcard,hweight⟩]
    change _+(literalSourceAlpha i G.multiplier G.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin i) (UniformFinite.Source.commonGuardMargin i)
      X:ℝ)*(_-_)=_
    rw [hα]
    ring

omit [NeZero M] in
theorem abs_nativeContextCountMoment_le (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (X : ClassifiedContext M)
    (seed : Prop) [Decidable seed] (a : Fin M) (q : Fin 3→ℝ) :
    |nativeContextCountMoment i G X seed a q|≤ 3*∑k : Fin 3,|q k| := by
  have hbase:=Weighted.abs_privateCountMoment_le (Uniform07.xi i) (Uniform07.xi_pos i)
    (source_xi_lt_one i) (Uniform07.capacity M) X none a q
  have hcorr:=abs_finitePathCountCorrection_le (Uniform07.xi i) (Uniform07.xi_pos i)
    (source_xi_lt_one i) G.multiplier (Early.demandRatio i) (Early.bidCap i)
    (Uniform07.capacity M) (literalSourceAlpha i G.multiplier G.rejectionRoot
      (10*UniformFinite.Source.commonGuardMargin i) (UniformFinite.Source.commonGuardMargin i)) X a q
  dsimp only [literalSourceAlpha] at hcorr
  unfold nativeContextCountMoment
  split_ifs
  · exact (abs_add_le _ _).trans (by linarith)
  · simp only [add_zero]
    have hsum : 0≤∑k : Fin 3,|q k| := Finset.sum_nonneg (fun _ _=>abs_nonneg _)
    linarith

theorem abs_native_exceptional_context_difference_le (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (X : ClassifiedContext M)
    (seed : Prop) [Decidable seed] (a : Fin M) (q : Fin 3→ℝ) :
    |nativeContextCountMoment i G X seed a q-
      (UniformFinite.Late.Exceptional.continuationLaw i G (UniformFinite.NativeContext.decode X)
        (fun j=>entryBid (X.1 j)) a).expect (fun P=>q (UniformFinite.pairCount a P))|≤
      4*∑k : Fin 3,|q k| := by
  have hbase:=abs_nativeContextCountMoment_le i G X seed a q
  have hrec : |(UniformFinite.Late.Exceptional.continuationLaw i G
      (UniformFinite.NativeContext.decode X) (fun j=>entryBid (X.1 j)) a).expect
        (fun P=>q (UniformFinite.pairCount a P))|≤∑k : Fin 3,|q k| := by
    apply (WeightedSampling.abs_expect_le _ _).trans
    apply WeightedSampling.expect_le_const
    intro P _
    exact Finset.single_le_sum (fun j _=>abs_nonneg (q j)) (Finset.mem_univ _)
  exact (abs_sub _ _).trans (by linarith)

end FCAppendix.Affine.Uniform07Finishing.Concrete05
