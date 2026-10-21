import FCAppendix.Affine.UniformFinite.OwnBidModulus
import FCAppendix.Affine.UniformFinite.EqualRaise
import FCAppendix.Affine.UniformFinite.ActualDuplicateEvent

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Classical
open scoped BigOperators
namespace ActualAtoms

variable {M : ℕ}

def pureDuplicateGain (i : Row) (row : Source.CountRow M) (b : Fin M→ℝ)
    (a : Fin M) (target : ℝ) : Prop :=
  LowBody.focalCopy ((Source.lowerTemplate row).selection (Uniform05.kappa i)
    (Source.lowerBids row b)) a≠2 ∧
  LowBody.focalCopy ((Source.lowerTemplate row).selection (Uniform05.kappa i)
    (Source.lowerBids row (Function.update b a target))) a=2

theorem exists_all_equal_raise_modulus [NeZero M] (i : Row) (a err : ℝ)
    (ha : 0< a) (herr : 0< err) :
    ∃ radius : ℝ, 0< radius ∧ ∀ (row : Source.CountRow M) (f : Fin M),
      f∈row.lower → Source.residual row 0=Source.residual row 1 →
      ∀ x : OwnBid.Box i M,∀target : Bid i,
        a≤ SourceContinuity.bids i x.2 f →
        SourceContinuity.bids i x.2 f≤(target:ℝ) →
        (target:ℝ)-SourceContinuity.bids i x.2 f< radius →
        -err≤ rowPayoff i x.2.1 row x.1
          (SourceContinuity.bids i (OwnBid.change i x f target).2) f-
          rowPayoff i x.2.1 row x.1 (SourceContinuity.bids i x.2) f := by
  classical
  have hlocal (j : Source.CountRow M×Fin M) :
      ∃r : ℝ,0< r ∧ ∀hf:j.2∈j.1.lower,
        ∀heq:Source.residual j.1 0=Source.residual j.1 1,
        ∀x : OwnBid.Box i M,∀target : Bid i,
          a≤ SourceContinuity.bids i x.2 j.2 →
          SourceContinuity.bids i x.2 j.2≤(target:ℝ) →
          (target:ℝ)-SourceContinuity.bids i x.2 j.2< r →
          -err≤ rowPayoff i x.2.1 j.1 x.1
            (SourceContinuity.bids i (OwnBid.change i x j.2 target).2) j.2-
            rowPayoff i x.2.1 j.1 x.1 (SourceContinuity.bids i x.2) j.2 := by
    by_cases hf : j.2∈j.1.lower
    · by_cases heq : Source.residual j.1 0=Source.residual j.1 1
      · obtain ⟨r,hr,h⟩:=OwnBid.exists_equal_raise_modulus i j.1 j.2 hf heq (L:=a) ha herr
        exact ⟨r,hr,fun _ _=> h⟩
      · exact ⟨1,by norm_num,fun _ h=> False.elim (heq h)⟩
    · exact ⟨1,by norm_num,fun h=> False.elim (hf h)⟩
  choose r hr hlocal using hlocal
  let radius := Finset.univ.inf' Finset.univ_nonempty r
  have hradius : 0< radius := (Finset.lt_inf'_iff _).mpr (fun j _=> hr j)
  refine ⟨radius,hradius,?_⟩
  intro row f hf heq x target hb hraise hnear
  exact hlocal (row,f) hf heq x target hb hraise
    (hnear.trans_le (Finset.inf'_le r (Finset.mem_univ (row,f))))

lemma pure_bound_from_modulus [NeZero M] (i : Row) (row : Source.CountRow M)
    (f : Fin M) (hf : f∈row.lower) (x : OwnBid.Box i M) (target : Bid i)
    (hv : SourceContinuity.bids i x.2 f≤(x.1:ℝ))
    (hraise : SourceContinuity.bids i x.2 f<(target:ℝ)) :
    -(if pureDuplicateGain i row (SourceContinuity.bids i x.2) f target
      then Uniform05.eta i*SourceContinuity.bids i x.2 f else 0)-
      (1+Uniform05.eta i)*((target:ℝ)-SourceContinuity.bids i x.2 f) ≤
      SourceContinuity.purePayoff i row f (OwnBid.realBox i (OwnBid.change i x f target))-
        SourceContinuity.purePayoff i row f (OwnBid.realBox i x) := by
  have hp:=PureAtoms.pure_raising_gain_lower (Source.lowerTemplate row) (kappa_ge_half i)
    (Source.lowerBids row (SourceContinuity.bids i x.2)) f (x.1:ℝ) (target:ℝ)
    (by simpa only [Source.lowerBids_of_mem row _ hf] using hv)
    (by simpa only [Source.lowerBids_of_mem row _ hf] using hraise)
  simp only [twice_kappa,add_sub_cancel_left,Source.lowerBids_of_mem row _ hf] at hp
  simp only [SourceContinuity.purePayoff,OwnBid.realBox,OwnBid.bids_change,
    pairPayoff_eq_purePayoff,pureDuplicateGain,lowerBids_update row _ f hf]
  convert! hp using 1;
    simp only [LowBody.purePayoff,Function.update_self,Source.lowerBids_of_mem row _ hf,
      OwnBid.change]

theorem exists_actual_raise_modulus [NeZero M] (i : Row) (a err : ℝ)
    (ha : 0< a) (herr : 0< err) :
    ∃radius : ℝ,0< radius ∧ ∀ (row : Source.CountRow M) (f : Fin M),
      f∈row.lower → ∀ x : OwnBid.Box i M,∀target : Bid i,
        a≤ SourceContinuity.bids i x.2 f →
        SourceContinuity.bids i x.2 f≤(x.1:ℝ) →
        SourceContinuity.bids i x.2 f<(target:ℝ) →
        (target:ℝ)-SourceContinuity.bids i x.2 f< radius →
        -(if pureDuplicateGain i row (SourceContinuity.bids i x.2) f target
          then Uniform05.eta i*SourceContinuity.bids i x.2 f else 0)-
          (1+Uniform05.eta i)*((target:ℝ)-SourceContinuity.bids i x.2 f)-err ≤
        rowPayoff i x.2.1 row x.1
          (SourceContinuity.bids i (OwnBid.change i x f target).2) f-
          rowPayoff i x.2.1 row x.1 (SourceContinuity.bids i x.2) f := by
  obtain ⟨ru,hru,hu⟩:=OwnBid.exists_all_unequal_raise_modulus (M:=M) i herr
  obtain ⟨re,hre,he⟩:=exists_all_equal_raise_modulus (M:=M) i a err ha herr
  refine ⟨min ru re,lt_min hru hre,?_⟩
  intro row f hf x target hb hv hraise hnear
  let loss:=if pureDuplicateGain i row (SourceContinuity.bids i x.2) f target
    then Uniform05.eta i*SourceContinuity.bids i x.2 f else 0
  let price:=(1+Uniform05.eta i)*((target:ℝ)-SourceContinuity.bids i x.2 f)
  have hloss : 0≤ loss := by
    dsimp only [loss]
    split_ifs
    · exact mul_nonneg (Uniform05.eta_range i).1.le (ha.le.trans hb)
    · rfl
  have hprice : 0≤ price:=mul_nonneg (by linarith [(Uniform05.eta_range i).1])
    (sub_nonneg.mpr hraise.le)
  by_cases heq : Source.residual row 0=Source.residual row 1
  · have h:=he row f hf heq x target hb hraise.le (hnear.trans_le (min_le_right _ _))
    change -loss-price-err≤ _
    linarith
  · have h:=hu row f hf heq x target hraise.le (hnear.trans_le (min_le_left _ _))
    have hp:=pure_bound_from_modulus i row f hf x target hv hraise
    have hα:=Source.guardAlpha_bounds i x.2.1 row (SourceContinuity.bids i x.2)
    have hm:=mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hα.2)
    change -loss-price-err≤ _
    nlinarith

theorem exists_actual_zero_raise_modulus [NeZero M] (i : Row) {err : ℝ}
    (herr : 0< err) :
    ∃radius : ℝ,0< radius ∧ ∀ (row : Source.CountRow M) (f : Fin M),
      f∈row.lower → ∀x : OwnBid.Box i M,∀target : Bid i,
        SourceContinuity.bids i x.2 f≤(x.1:ℝ) →
        SourceContinuity.bids i x.2 f<(target:ℝ) →
        (target:ℝ)-SourceContinuity.bids i x.2 f< radius →
        -Uniform05.eta i*SourceContinuity.bids i x.2 f-
          (1+Uniform05.eta i)*((target:ℝ)-SourceContinuity.bids i x.2 f)-err ≤
        rowPayoff i x.2.1 row x.1
          (SourceContinuity.bids i (OwnBid.change i x f target).2) f-
          rowPayoff i x.2.1 row x.1 (SourceContinuity.bids i x.2) f := by
  obtain ⟨r,hr,h⟩:=OwnBid.exists_all_unequal_raise_modulus (M:=M) i herr
  refine ⟨r,hr,?_⟩
  intro row f hf x target hv hraise hnear
  have hbid:=SourceContinuity.bids_bounds i x.2 f
  have he:=Uniform05.eta_range i
  by_cases heq : Source.residual row 0=Source.residual row 1
  · have hh:=OwnBid.equal_raise_lower i row f hf heq x target hraise.le hv
    exact (sub_le_self _ herr.le).trans hh
  · have hm:=h row f hf heq x target hraise.le hnear
    have hp:=pure_bound_from_modulus i row f hf x target hv hraise
    have hloss : (if pureDuplicateGain i row (SourceContinuity.bids i x.2) f target
        then Uniform05.eta i*SourceContinuity.bids i x.2 f else 0)≤
        Uniform05.eta i*SourceContinuity.bids i x.2 f := by
      split_ifs <;> nlinarith [mul_nonneg he.1.le hbid.1]
    have hα:=Source.guardAlpha_bounds i x.2.1 row (SourceContinuity.bids i x.2)
    have hl : -Uniform05.eta i*SourceContinuity.bids i x.2 f-
        (1+Uniform05.eta i)*((target:ℝ)-SourceContinuity.bids i x.2 f)≤0 := by
      nlinarith [mul_nonneg he.1.le hbid.1,
        mul_nonneg (by linarith : 0≤1+Uniform05.eta i) (sub_nonneg.mpr hraise.le)]
    have hp' : -Uniform05.eta i*SourceContinuity.bids i x.2 f-
        (1+Uniform05.eta i)*((target:ℝ)-SourceContinuity.bids i x.2 f)≤
      SourceContinuity.purePayoff i row f (OwnBid.realBox i (OwnBid.change i x f target))-
        SourceContinuity.purePayoff i row f (OwnBid.realBox i x) := by linarith
    have hmul:=mul_le_mul_of_nonneg_left hp' (sub_nonneg.mpr hα.2)
    nlinarith

end ActualAtoms
end FCAppendix.Affine.UniformFinite
